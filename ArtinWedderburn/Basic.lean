import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.Ring.Opposite
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.Module.Submodule.Lattice

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
    intro w x y z h1 h2
    simp [map_add]
    rw [h1, h2]

  mul' := by
    intro w x y z h1 h2
    simp [map_mul]
    rw [h1, h2]

  iseqv := by
    constructor
    · intro x
      rfl

    · intro x y h
      simp [h.symm]

    · intro x y z h1 h2
      rw [h1, h2]


def hom : (congruence f).Quotient →+* f.range where
  toFun := Quotient.lift
    (f.codRestrict f.range Set.mem_range_self)
    (fun x y h => Subtype.eq h)

  map_zero' := by
    apply Subtype.ext
    change f 0 = 0
    simp

  map_one' := by
    apply Subtype.ext
    change f 1 = 1
    simp

  map_add' := by
    intro x y
    refine Quotient.inductionOn x (fun x ↦ ?_)
    refine Quotient.inductionOn y (fun y ↦ ?_)
    apply Subtype.ext
    change f (x + y) = f x + f y
    exact RingHom.map_add f x y

  map_mul':= by
    intro x y
    refine Quotient.inductionOn x (fun x ↦ ?_)
    refine Quotient.inductionOn y (fun y ↦ ?_)
    apply Subtype.ext
    change f (x * y) = f x * f y
    exact RingHom.map_mul f x y


-- Statement of the first isomorphism theorem for rings.
theorem first_iso_thm :
  Nonempty ((congruence f).Quotient ≃+* f.range) :=
  by

    have bijection : Function.Bijective (hom f) :=
    by
      constructor
      · intro x y
        refine Quotient.inductionOn x (fun x ↦ ?_)
        refine Quotient.inductionOn y (fun y ↦ ?_)
        intro h
        apply Quotient.sound
        exact congr_arg Subtype.val h

      · intro y
        rcases y with ⟨_, ⟨r, rfl⟩⟩
        exists Quotient.mk (congruence f).toSetoid r

    exact Nonempty.intro (RingEquiv.ofBijective (hom f) bijection)


variable {R : Type*} [Ring R]
variable {ι : Type*}
variable {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]


-- Statement and sharp proof of Schur's lemma.
theorem schurs {i j} [IsSimpleModule R (M i)] [IsSimpleModule R (M j)]
(phi : M i →ₗ[R] M j) (h0 : phi ≠ 0) : Function.Bijective phi :=
  by
    constructor
    · exact LinearMap.injective_of_ne_zero h0

    · exact LinearMap.surjective_of_ne_zero h0


/-
Proof that for disctinct simple modules S_i, End(⊕S_i) ≅ ⊕End(S_i).
Note that in general we have End(⊕S_i) = ∏_{i,j}Hom(S_i,S_j), hence
we need to prove this, and that for simple modules Hom(M,N) = 0.
-/
theorem Simple_Hom_Eq_Zero_If_Not_Iso
    {i j : ι} [IsSimpleModule R (M i)] [IsSimpleModule R (M j)]
    (h_not_iso : ¬ Nonempty (M i ≃ₗ[R] M j)) (f : M i →ₗ[R] M j) : f = 0 := by
    classical
    by_contra hf
    apply h_not_iso
    have h' : Function.Bijective f :=
    schurs (i := i) (j := j) f hf
    refine ⟨LinearEquiv.ofBijective f h'⟩


end schur

namespace temporary

variable {R : Type*} [Ring R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

open scoped BigOperators

def inj (i : ι) : M i →ₗ[R] ((j : ι) → M j) :=
  { toFun := fun m ↦ Pi.single i m
    map_add' := fun x y ↦ by simp [Pi.single_add]
    map_smul' := fun r x ↦ by simp [Pi.single_smul] }

def End_DirectSum_Equiv_DirectSum_End
    [∀ i, IsSimpleModule R (M i)]
    (h_pairwise : Pairwise (fun i j ↦ ¬ Nonempty (M i ≃ₗ[R] M j))) :
    Module.End R ((i : ι) → M i) ≃+* Π i, Module.End R (M i) := by
      sorry


end temporary

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
end Lemma2


open scoped BigOperators

namespace Lemma3

variable {R : Type*} [Ring R]
variable {ι : Type*} [DecidableEq ι]

/--
Textbook argument, see Anthony Knapp, Advanced Algebra, pp. 81:
We are about to prove a semi simple ring is an internal direct sum of finitely many of its minimal left ideals.
Assume `R = ⨁ i, I i` as an internal direct sum of left ideals (`Submodule R R`).
Decompose `1` in the direct sum; this has finite support `s`.
Then `1 ∈ ⨆ i ∈ s, I i`, hence this finite supremum is a left ideal containing `1`,
so it must be `⊤` (the whole module).
-/

theorem exists_finset_iSup_eq_top_of_isInternal
    (I : ι → Submodule R R) (hI : DirectSum.IsInternal I) :
    ∃ s : Finset ι, (⨆ i ∈ s, I i) = (⊤ : Submodule R R) := by
  classical
  -- Turn the `IsInternal` proof into a decomposition, so we can talk about components.
  letI : DirectSum.Decomposition I := DirectSum.IsInternal.chooseDecomposition I hI

  -- Let `s` be the (finite) support of the decomposition of `1`.
  let s : Finset ι := DFinsupp.support ((DirectSum.decompose I) (1 : R))
  refine ⟨s, ?_⟩

  -- The finite supremum over `s` is a left ideal containing `1`, hence it is `⊤`.
  refine top_unique ?_
  intro r _

  have one_mem : (1 : R) ∈ (⨆ i ∈ s, I i) := by
    -- Each summand lies in the corresponding `I i`,
    -- so the finite sum lies in the finite supremum.
    have hsum_mem :
        (∑ i ∈ s, (((DirectSum.decompose I) (1 : R)) i : R)) ∈ (⨆ i ∈ s, I i) := by
      refine
        Submodule.sum_mem_biSup (s := s)
          (f := fun i => (((DirectSum.decompose I) (1 : R)) i : R)) (p := I) ?_
      intro i hi
      exact (((DirectSum.decompose I) (1 : R)) i).property

    -- And this sum is exactly `1` (the decomposition recomposes).
    have hsum_eq :
        (∑ i ∈ s, (((DirectSum.decompose I) (1 : R)) i : R)) = (1 : R) := by
      simpa [s] using (DirectSum.sum_support_decompose I (1 : R))

    -- Therefore `1` belongs to the finite supremum.
    simpa [hsum_eq] using hsum_mem

  -- Now use the standard trick: if a left ideal contains `1`, it contains every `r = r • 1`.
  simpa using ((⨆ i ∈ s, I i).smul_mem r one_mem)

end Lemma3


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
  --Homomorphism
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
noncomputable def RingEquivEnd
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

/-
This is a proof of lemma 5 from the outline, which states:
For a semi-simple Artinian right R module (left R^op module) M,
 End_R(M) ≅ ⊕ M_{a_i}(D_i)
for a division rings D_i and non-negative integers a_i.
The proof of this is essentially just colating all of the prior work.
-/


namespace main_result

variable {R : Type*} [Ring R] [IsSemisimpleRing R] [IsArtinianRing R]

/-
The below statement MUST be checked and probably corrected in due course.
Merely pushing as a first attempt and placeholder.
-/

theorem artin_wedderburn :
  ∃ (ι : ℕ) (n : Fin ι → ℕ) (D : Fin ι → Type*) (_ : ∀ i, DivisionRing (D i)),
  Nonempty (R ≃+* Π (i : Fin ι), Matrix (Fin (n i)) (Fin (n i)) (D i)) :=
  by
    sorry

end main_result
