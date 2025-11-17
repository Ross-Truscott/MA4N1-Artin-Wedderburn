import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.SimpleModule.Basic
-- Remove SimpleModule.Basic later when I work out how to bring just the defintions

/-
This section is on the Proof of Lemma 2 from the outline, which states

Let S be a simple R-module and D = End_R(S). Define M = S^n. Then End_R(M) = M_n(D)
-/

namespace Lemma2

--Define a ring R, a simple R-module S .
variable (R : Type u_2) [Ring R] (S : Type u_4) [AddCommGroup S] [Module R S] [IsSimpleModule R S]

-- Define the Endomorphism ring of S and M = S^n
variable (D : Module.End R S)
variable {ι} (M : DirectSum ι fun (i : ι) => S i)



end Lemma2
