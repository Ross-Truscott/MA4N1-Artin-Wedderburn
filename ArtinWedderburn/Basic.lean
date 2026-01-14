import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.SimpleModule.Basic
-- Remove SimpleModule.Basic later when I work out how to bring just the defintions
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.Ring.Opposite

namespace schur

-- Define two rings and a ring homomorphism between them.
variable {R : Type*} [Ring R]
variable {S : Type*} [Ring S]
variable (f : R →+* S)

def ideal (S : Set R) : Prop :=
  (0 ∈ S) ∧
  (∀ x y, x ∈ S → y ∈ S → x+y ∈ S) ∧
  (∀ x, x ∈ S → -x ∈ S) ∧
  (∀ x r, x ∈ S → r * x ∈ S)

-- Statement and proof of the theorem that the kernel of a ring homomorphism is an ideal.
theorem ker_hom_is_ideal :
  ideal {r : R | f r = 0} :=
  by
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

def congruence : RingCon R where
  r x y := f x = f y
  add' := by
    sorry
  mul' := by
    sorry
  iseqv := by
    sorry

-- def map : Quotient (congruence f) →+* S :=
  -- RingCon.lift (congruence f) f (fun x y h => h)

-- Statement of the first isomorphism theorem for rings.
theorem first_iso_thm :
  Nonempty (f.range ≃+* R ⧸ RingHom.ker f) :=
  by
    sorry

-- Defines a simple R-module M
variable {M : Type*} [AddCommGroup M] [Module R M]

-- Statement of Schur's lemma.
theorem schur [IsSimpleModule R M] :
  Nonempty (DivisionRing (Module.End R M)) :=
  by
    sorry

end schur

namespace Lemma2
/-
This is the Proof of Lemma 2 from the outline, which states:

Thm: Let S be a simple R-module and D = End_R(S). Define M = S^n. Then End_R(M) = M_n(D)
Proof : End(M) is determined by the action on each summand S. So, look at the inclusion
ιᵢ: S → M & projection πᵢ: M → S and consider f_ij = πᵢfιⱼ ∈ End(S).
Elements of M are (s_1,…,s_n) so we can consider
f(s_1,…,s_n) = (∑f_1j(s_j),…,∑f_nj(s_j)), but this is just the matrix representation.
This is a homomorphism, clearly, and its simple to show its bijective.
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
  --Proof they are inverse
  left_inv := by
    intro F
    ext a b
    simp [Pi.single_apply]
    rw [Finset.sum_eq_single a]
    · simp
    · simp
      intro c cna
      rw [if_neg cna, Pi.single_zero, map_zero, Pi.zero_apply]
    · simp


  right_inv := by
   intro M
   ext a b c
   simp [Pi.single_apply]
   rw [Finset.sum_eq_single b]
   · simp only [↓reduceIte]
   · simp
     intro d dnb
     rw [if_neg dnb]
     exact LinearMap.map_zero (M a d)
   · simp

-- Use Equiv.toLinearEquiv? Not sure if needed, but it exists
-- Probably more sensible to just use this in situ with Schurs in final proof

/-
This is a proof of lemma 4 from the outline, which states:
For any (unital) ring R, End_R(R) ≅ R.
That is, a ring is isomorphic to the endomorphism ring of itself viewed as a right module.
The proof is simply to consider the map φ_r:R→End_R(R) by φ_r(s)=rs
and go through the easy verification that it's bijective and a homomorphism.

Technically we prove that End_R(R) ≅ Rᵒᵖ as lean works with left modules.
These statements are dual to each other however, right R modules are left R^op modules.
This means we actually aim to prove R≅M_n(D)ᵒᵖ in the end.
-/

noncomputable def RopToEndRMap
    (R : Type) [Ring R] :
    Rᵐᵒᵖ →+* Module.End R R :=
{ toFun := fun s =>
  { toFun := fun r => r * s.unop
    map_add' := by
      intros x y
      apply right_distrib
    map_smul' := by
      intros a r
      rw [RingHom.id_apply,smul_mul_assoc]
  }
  map_one' := by
    ext
    simp
  map_mul' := by
    intros x y
    ext
    simp
  map_zero' := by
    ext
    simp
  map_add' := by
    intros x y
    ext
    simp
}

--`Proof' that homomorphism + bijective = isomorphism
noncomputable def ringEquivEnd
    (R : Type) [Ring R] :
    Rᵐᵒᵖ ≃+* Module.End R R :=
    RingEquiv.ofBijective (RopToEndRMap R)
    ⟨-- injective
      by
      intros x y h
      have h1 := LinearMap.congr_fun h 1
      dsimp [RopToEndRMap] at h1
      repeat rw [one_mul] at h1
      exact MulOpposite.unop_injective h1
      -- surjective
      ,
      by
        intro f
        use MulOpposite.op (f 1)
        apply LinearMap.ext
        intro r
        dsimp [RopToEndRMap]
        rw [← smul_eq_mul, ← LinearMap.map_smul, smul_eq_mul, mul_one]
    ⟩
