// Copyright 2018 PingCAP, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// See the License for the specific language governing permissions and
// limitations under the License.

package core

import (
	"github.com/pingcap/errors"
	"github.com/pingcap/tidb/expression"
	"github.com/pingcap/tidb/parser/ast"
	"math/bits"
)

type joinReorderDPSolver struct {
	*baseSingleGroupJoinOrderSolver
	newJoin func(lChild, rChild LogicalPlan, eqConds []*expression.ScalarFunction, otherConds []expression.Expression) LogicalPlan
}

type joinGroupEqEdge struct {
	nodeIDs []int
	edge    *expression.ScalarFunction
}

type joinGroupNonEqEdge struct {
	nodeIDs    []int
	nodeIDMask uint
	expr       expression.Expression
}

func (s *joinReorderDPSolver) solve(joinGroup []LogicalPlan, eqConds []expression.Expression) (LogicalPlan, error) {
	// TODO: You need to implement the join reorder algo based on DP.

	// The pseudo code can be found in README.
	// And there's some common struct and method like `baseNodeCumCost`, `calcJoinCumCost` you can use in `rule_join_reorder.go`.
	// Also, you can take a look at `rule_join_reorder_greedy.go`, this file implement the join reorder algo based on greedy algorithm.
	// You'll see some common usages in the greedy version.

	// Note that the join tree may be disconnected. i.e. You need to consider the case `select * from t, t1, t2`.

	// fmt.Printf("solve: %v\n", eqConds)
	for _, node := range joinGroup {
		_, err := node.recursiveDeriveStats()
		if err != nil {
			return nil, err
		}
		s.curJoinGroup = append(s.curJoinGroup, &jrNode{
			p:       node,
			cumCost: s.baseNodeCumCost(node),
		})
	}

	adjMatrix := make([][]int, len(s.curJoinGroup))
	eqEdges := make([]joinGroupEqEdge, 0, len(eqConds))
	for _, cond := range eqConds {
		sf, ok := cond.(*expression.ScalarFunction)
		if !ok {
			return nil, errors.Errorf("illegal eqCond")
		}
		lCol := sf.GetArgs()[0].(*expression.Column)
		rCol := sf.GetArgs()[1].(*expression.Column)

		lIndex, err := findNodeIndexInGroup(joinGroup, lCol)
		if err != nil {
			return nil, err
		}
		rIndex, err := findNodeIndexInGroup(joinGroup, rCol)
		if err != nil {
			return nil, err
		}
		eqEdges = append(eqEdges, joinGroupEqEdge{
			nodeIDs: []int{lIndex, rIndex},
			edge:    sf,
		})
		adjMatrix[lIndex] = append(adjMatrix[lIndex], rIndex)
		adjMatrix[rIndex] = append(adjMatrix[rIndex], lIndex)
	}

	nonEqEdges := make([]joinGroupNonEqEdge, 0, len(s.otherConds))
	for _, cond := range s.otherConds {
		cols := expression.ExtractColumns(cond)
		mask := uint(0)
		ids := make([]int, 0, len(cols))
		for _, col := range cols {
			idx, err := findNodeIndexInGroup(joinGroup, col)
			if err != nil {
				return nil, err
			}
			ids = append(ids, idx)
			mask |= (1 << uint(idx))
		}

		nonEqEdges = append(nonEqEdges, joinGroupNonEqEdge{
			nodeIDs:    ids,
			nodeIDMask: mask,
			expr:       cond,
		})
	}

	// bfs join graph
	// index by nodeID
	visited := make([]bool, len(joinGroup))
	visitIDs := make([]int, len(joinGroup))

	var joins []LogicalPlan
	for i := 0; i < len(joinGroup); i++ {
		if visited[i] {
			continue
		}
		visitQueue := s.bfsOnePhase(i, visited, adjMatrix, visitIDs)

		visitMask := uint(0)
		for _, id := range visitQueue {
			visitMask |= (1 << id)
		}
		var subNonEqEdges []joinGroupNonEqEdge
		for j := 0; j < len(nonEqEdges); j++ {
			if nonEqEdges[j].nodeIDMask&visitMask != nonEqEdges[j].nodeIDMask {
				continue
			}

			//newMask := uint(0)
			//for _, nodeID := range nonEqEdges[i].nodeIDs {
			//	newMask |= 1 << uint(visitIDs[nodeID])
			//}
			//nonEqEdges[i].nodeIDMask = newMask
			subNonEqEdges = append(subNonEqEdges, nonEqEdges[i])
			// remove non eq edge i
			nonEqEdges = append(nonEqEdges[:i], nonEqEdges[i+1:]...)
		}
		// do dp
		join, err := s.doDP(visitQueue, visitIDs, joinGroup, eqEdges, subNonEqEdges)
		if err != nil {
			return nil, err
		}
		joins = append(joins, join)
	}
	// remain edges
	remainedOtherCond := make([]expression.Expression, 0, len(nonEqEdges))
	for _, edge := range nonEqEdges {
		remainedOtherCond = append(remainedOtherCond, edge.expr)
	}
	return s.makeBushyJoin(joins, remainedOtherCond), nil

	// return nil, errors.Errorf("unimplemented")
}

func (s *joinReorderDPSolver) bfsOnePhase(start int, visited []bool, adjMatrix [][]int, visitIDs []int) []int {
	q := []int{start}
	visited[start] = true
	var visitQueue []int
	var round = 0
	for len(q) > 0 {
		cur := q[0]
		q = q[1:]
		visitIDs[cur] = round
		visitQueue = append(visitQueue, cur)

		for _, next := range adjMatrix[cur] {
			if !visited[next] {
				q = append(q, next)
				visited[next] = true
			}
		}
		round++
	}
	return visitQueue
}

func (s *joinReorderDPSolver) doDP(
	visitQueue,
	visitIDs []int,
	joinGroup []LogicalPlan,
	eqEdges []joinGroupEqEdge,
	nonEqEdges []joinGroupNonEqEdge,
) (LogicalPlan, error) {
	totalCnt := len(visitQueue)
	costs := make([]*jrNode, 1<<totalCnt)
	for i := 0; i < totalCnt; i++ {
		costs[1<<i] = s.curJoinGroup[visitQueue[i]]
	}
	for subGroup := uint(1); subGroup < (1 << totalCnt); subGroup++ {
		if bits.OnesCount(subGroup) <= 1 {
			continue
		}

		// generate all subgroup && calculate the smallest cost
		for sub := (subGroup - 1) & subGroup; sub > 0; sub = (sub - 1) & subGroup {
			remain := subGroup ^ sub
			if sub > remain {
				continue
			}
			// not connected
			if costs[sub] == nil || costs[remain] == nil {
				continue
			}

			conEqEdges, conNonEqEdges := s.getConnectedNodes(sub, remain, visitIDs, eqEdges, nonEqEdges)
			if len(conEqEdges) == 0 {
				continue
			}
			// fmt.Printf("newJoinWithEdge: %v %v %v\n", subGroup, sub, remain)
			join, err := s.newJoinWithEdge(costs[sub].p, costs[remain].p, conEqEdges, conNonEqEdges)
			if err != nil {
				return nil, err
			}
			// fmt.Printf("calcJoinCumCost: %v, %v\n", conEqEdges, conEqEdges[0].edge)
			cost := s.calcJoinCumCost(join, costs[sub], costs[remain])
			if costs[subGroup] == nil {
				costs[subGroup] = &jrNode{
					p:       join,
					cumCost: cost,
				}
			} else if costs[subGroup].cumCost > cost {
				costs[subGroup].p = join
				costs[subGroup].cumCost = cost
			}
		}
	}
	return costs[(1<<totalCnt)-1].p, nil
}

// calculate all edges which connect the two subgroup
func (s *joinReorderDPSolver) getConnectedNodes(
	leftMask, rightMask uint,
	visitIDs []int,
	eqEdges []joinGroupEqEdge,
	nonEqEdges []joinGroupNonEqEdge,
) ([]joinGroupEqEdge, []expression.Expression) {
	var conEqEdges []joinGroupEqEdge
	var conNonEqEdges []expression.Expression
	for _, edge := range eqEdges {
		lIndMask := uint(1 << uint(visitIDs[edge.nodeIDs[0]]))
		rIndMask := uint(1 << uint(visitIDs[edge.nodeIDs[1]]))
		if ((leftMask&lIndMask) > 0 && (rightMask&rIndMask) > 0) ||
			((leftMask&rIndMask) > 0 && (rightMask&lIndMask) > 0) {
			conEqEdges = append(conEqEdges, edge)
		}
	}

	for _, edge := range nonEqEdges {
		var visitIDMask = uint(0)
		for _, id := range edge.nodeIDs {
			visitIDMask |= 1 << uint(visitIDs[id])
		}

		if visitIDMask&(leftMask|rightMask) != visitIDMask {
			continue
		}
		if (visitIDMask&leftMask == 0) || (visitIDMask&rightMask == 0) {
			continue
		}
		conNonEqEdges = append(conNonEqEdges, edge.expr)
	}
	return conEqEdges, conNonEqEdges
}

func (s *joinReorderDPSolver) newJoinWithEdge(leftPlan, rightPlan LogicalPlan, edges []joinGroupEqEdge, otherConds []expression.Expression) (LogicalPlan, error) {
	var eqConds []*expression.ScalarFunction
	for _, edge := range edges {
		lCol := edge.edge.GetArgs()[0].(*expression.Column)
		rCol := edge.edge.GetArgs()[1].(*expression.Column)
		if leftPlan.Schema().Contains(lCol) {
			eqConds = append(eqConds, edge.edge)
		} else {
			newSf := expression.NewFunctionInternal(s.ctx, ast.EQ, edge.edge.GetType(), rCol, lCol).(*expression.ScalarFunction)
			eqConds = append(eqConds, newSf)
		}
	}
	join := s.newJoin(leftPlan, rightPlan, eqConds, otherConds)
	_, err := join.recursiveDeriveStats()
	return join, err
}

// Make cartesian join as bushy tree.
func (s *joinReorderDPSolver) makeBushyJoin(cartesianJoinGroup []LogicalPlan, otherConds []expression.Expression) LogicalPlan {
	for len(cartesianJoinGroup) > 1 {
		resultJoinGroup := make([]LogicalPlan, 0, len(cartesianJoinGroup))
		for i := 0; i < len(cartesianJoinGroup); i += 2 {
			if i+1 == len(cartesianJoinGroup) {
				resultJoinGroup = append(resultJoinGroup, cartesianJoinGroup[i])
				break
			}
			// TODO:Since the other condition may involve more than two tables, e.g. t1.a = t2.b+t3.c.
			//  So We'll need a extra stage to deal with it.
			// Currently, we just add it when building cartesianJoinGroup.
			mergedSchema := expression.MergeSchema(cartesianJoinGroup[i].Schema(), cartesianJoinGroup[i+1].Schema())
			var usedOtherConds []expression.Expression
			otherConds, usedOtherConds = expression.FilterOutInPlace(otherConds, func(expr expression.Expression) bool {
				return expression.ExprFromSchema(expr, mergedSchema)
			})
			resultJoinGroup = append(resultJoinGroup, s.newJoin(cartesianJoinGroup[i], cartesianJoinGroup[i+1], nil, usedOtherConds))
		}
		cartesianJoinGroup = resultJoinGroup
	}
	return cartesianJoinGroup[0]
}

func findNodeIndexInGroup(group []LogicalPlan, col *expression.Column) (int, error) {
	for i, plan := range group {
		if plan.Schema().Contains(col) {
			return i, nil
		}
	}
	return -1, ErrUnknownColumn.GenWithStackByArgs(col, "JOIN REORDER RULE")
}
