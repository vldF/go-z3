// Copyright 2017 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package z3

import "runtime"

/*
#cgo LDFLAGS: -lz3
#include <z3.h>
#include <stdlib.h>
*/
import "C"

// A Solver is a collection of predicates that can be checked for
// satisfiability.
//
// These predicates form a stack that can be manipulated with
// Push/Pop.
type Solver struct {
	*solverImpl
	noEq
}

type solverImpl struct {
	ctx *Context
	c   C.Z3_solver
}

// NewSolver returns a new, empty solver.
func NewSolver(ctx *Context) *Solver {
	var impl *solverImpl
	ctx.do(func() {
		impl = &solverImpl{
			ctx,
			C.Z3_mk_solver(ctx.c),
		}
	})
	ctx.do(func() {
		C.Z3_solver_inc_ref(ctx.c, impl.c)
	})
	runtime.SetFinalizer(impl, func(impl *solverImpl) {
		impl.ctx.do(func() {
			C.Z3_solver_dec_ref(impl.ctx.c, impl.c)
		})
	})
	return &Solver{impl, noEq{}}
}

// Assert adds val to the set of predicates that must be satisfied.
func (s *Solver) Assert(val Bool) {
	s.ctx.do(func() {
		C.Z3_solver_assert(s.ctx.c, s.c, val.c)
	})
	runtime.KeepAlive(s)
	runtime.KeepAlive(val)
}

func (s *Solver) AssertAndTrack(val Bool, p Bool) {
	s.ctx.do(func() {
		C.Z3_solver_assert_and_track(s.ctx.c, s.c, val.c, p.c)
	})
	runtime.KeepAlive(s)
	runtime.KeepAlive(val)
}

func (s *Solver) GetUnsatCore() []Bool {
	var unsatCoreVector C.Z3_ast_vector
	var n C.uint
	s.ctx.do(func() {
		unsatCoreVector = C.Z3_solver_get_unsat_core(s.ctx.c, s.c)
		C.Z3_ast_vector_inc_ref(s.ctx.c, unsatCoreVector)
		n = C.Z3_ast_vector_size(s.ctx.c, unsatCoreVector)
	})
	s.ctx.do(func() { C.Z3_ast_vector_dec_ref(s.ctx.c, unsatCoreVector) })
	unsatCore := make([]Bool, n)
	for i := C.uint(0); i < n; i++ {
		unsatCore[i] = Bool(wrapValue(s.ctx, func() C.Z3_ast {
			return C.Z3_ast_vector_get(s.ctx.c, unsatCoreVector, i)
		}))
	}
	runtime.KeepAlive(s)
	return unsatCore
}

// Push saves the current state of the Solver so it can be restored
// with Pop.
func (s *Solver) Push() {
	s.ctx.do(func() {
		C.Z3_solver_push(s.ctx.c, s.c)
	})
	runtime.KeepAlive(s)
}

// Pop removes assertions that were added since the matching Push.
func (s *Solver) Pop() {
	s.ctx.do(func() {
		C.Z3_solver_pop(s.ctx.c, s.c, 1)
	})
	runtime.KeepAlive(s)
}

// Reset removes all assertions from the Solver and resets its stack.
func (s *Solver) Reset() {
	s.ctx.do(func() {
		C.Z3_solver_reset(s.ctx.c, s.c)
	})
	runtime.KeepAlive(s)
}

// ErrSatUnknown is produced when Z3 cannot determine satisfiability.
type ErrSatUnknown struct {
	// Reason gives a brief description of why Z3 could not
	// determine satisfiability.
	Reason string
}

// Error returns the reason Z3 could not determine satisfiability.
func (e *ErrSatUnknown) Error() string {
	return e.Reason
}

// Check determines whether the predicates in Solver s are satisfiable
// or unsatisfiable. If Z3 is unable to determine satisfiability, it
// returns an *ErrSatUnknown error.
func (s *Solver) Check() (sat bool, err error) {
	var res C.Z3_lbool
	s.ctx.do(func() {
		res = C.Z3_solver_check(s.ctx.c, s.c)
	})
	if res == C.Z3_L_UNDEF {
		// Get the reason.
		s.ctx.do(func() {
			cerr := C.Z3_solver_get_reason_unknown(s.ctx.c, s.c)
			err = &ErrSatUnknown{C.GoString(cerr)}
		})
	}
	runtime.KeepAlive(s)
	return res == C.Z3_L_TRUE, err
}

// Model returns the model for the last Check. Model panics if Check
// has not been called or the last Check did not return true.
func (s *Solver) Model() *Model {
	var model *Model
	s.ctx.do(func() {
		model = wrapModel(s.ctx, C.Z3_solver_get_model(s.ctx.c, s.c))
	})
	runtime.KeepAlive(s)
	return model
}

// String returns a string representation of s.
func (s *Solver) String() string {
	var res string
	s.ctx.do(func() {
		res = C.GoString(C.Z3_solver_to_string(s.ctx.c, s.c))
	})
	runtime.KeepAlive(s)
	return res
}
