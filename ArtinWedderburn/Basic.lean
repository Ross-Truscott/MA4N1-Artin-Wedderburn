import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.SimpleModule.Basic
-- Remove SimpleModule.Basic later when I work out how to bring just the defintions

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

namespace Lemma2
/-
This section is on the Proof of Lemma 2 from the outline, which states:

Thm: Let S be a simple R-module and D = End_R(S). Define M = S^n. Then End_R(M) = M_n(D)
Proof : End(M) is determined by the action on each summand S. So, look at the inclusion
ιᵢ: S → M & projection πᵢ: M → S and consider f_ij = πᵢfιⱼ ∈ End(S) (= D by Schurs lemma).
Elements of M are (s_1,…,s_n) so we can consider
f(s_1,…,s_n) = (∑f_1j(s_j),…,∑f_nj(s_j)), but this is just the matrix representation.
This is a homomorphism clearly, and simple to show its bijective.
This gives us that End(M)≅Mₙ(End(S))≅Mₙ(D) by Schurs lemma.

This is still true without the simplicity assumption, so this is what we prove.
-/

def NEndEquivMatrixEnd
    (n : ℕ) (R : Type) [Ring R] (S : Type) [AddCommGroup S] [Module R S] :
    Module.End R (Fin n → S) ≃ Matrix (Fin n) (Fin n) (Module.End R S) where
    --Def of forwards map
  toFun F i j :=
    {
      toFun s := F (Pi.single j s) i
      --Proof its linear
      map_add' s t := by
        rw[Pi.single_add,map_add, Pi.add_apply]
      map_smul' r s := by
        rw[Pi.single_smul]
        simp
      }
    --Def of reverse map
  invFun M :=
  {
    toFun v i :=
      ∑ j, M i j (v j)
      --Proof its linear
    map_add' v w := by
        funext i
        simp [Finset.sum_add_distrib, map_add]
    map_smul' r v := by
        funext i
        simp
        rw [Finset.smul_sum]
  }
  --Proof theyre inverse
  left_inv := by
    intro M
    simp
    sorry
  right_inv := by
    sorry



end Lemma2
