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
-- variable (D : Module.End R S)
variable (M : DirectSum (Fin n) fun _ => S)

/-
Standard proof : End(M) is determined by the action on each summand S. So, look at the inclusion
ιᵢ: S → M & projection πᵢ: M → S and consider f_ij = πᵢfιⱼ ∈ End(S) (= D by Schurs lemma).
Elements of M are (s_1,…,s_n) so we can consider
f(s_1,…,s_n) = (∑f_1j(s_j),…,∑f_nj(s_j)), but this is just the matrix representation.
This is a homomorphism clearly, and simple to show its bijective.
This gives us that End(M)≅Mₙ(End(S))≅Mₙ(D) by Schurs lemma.
-/


end Lemma2

namespace kernel_result

-- Define two rings and a ring homomorphism between them.
variable {R : Type*} [Ring R]
variable {S : Type*} [Ring S]
variable (f : R →+* S)

def ideal (S : Set R) : Prop :=
  (0 ∈ S) ∧
  (∀ x y, x ∈ S → y ∈ S → x+y ∈ S) ∧
  (∀ x, x ∈ S → -x ∈ S) ∧
  (∀ x r, x ∈ S → r * x ∈ S)

-- Statement of the theorem that the kernel of a ring homomorphism is an ideal.
theorem ker_hom_is_ideal : ideal {r : R | f r = 0} := by
  constructor
  · simp

  constructor
  · intro x y hx hy
    simp at *
    rw [hx, hy, zero_add]

  constructor
  · simp

  intro x r hx
  simp at *
  rw [hx, mul_zero]

end kernel_result
