import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.SimpleModule.Basic (IsSimpleModule)

--Define a ring R and a simple R-module S.

variable (R : Type u_2) [Ring R] (S : Type u_4) [AddCommGroup S] [Module R S] [IsSimpleModule R S]


#check R
#check S
