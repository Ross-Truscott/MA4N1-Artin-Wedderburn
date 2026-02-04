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
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Order.Atoms

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

-- Statement of the first isomorphism theorem for modules.
noncomputable def first_iso_thm_modules {i j} (f : M i →ₗ[R] M j) :
  (M i ⧸ LinearMap.ker f) ≃ₗ[R] LinearMap.range f :=
  by
    let f_restricted : M i →ₗ[R] LinearMap.range f := f.rangeRestrict

    let f_lifted : (M i ⧸ LinearMap.ker f) →ₗ[R] LinearMap.range f :=
    Submodule.liftQ (LinearMap.ker f) f_restricted (by rw [LinearMap.ker_rangeRestrict])

    apply LinearEquiv.ofBijective f_lifted

    constructor
    · rw [← LinearMap.ker_eq_bot]
      rw [Submodule.ker_liftQ]
      rw [LinearMap.ker_rangeRestrict]
      exact Submodule.mkQ_map_self (LinearMap.ker f)

    · rw [← LinearMap.range_eq_top]
      rw [Submodule.range_liftQ]
      exact LinearMap.range_rangeRestrict f


-- Statement and proof of Schur's lemma.
theorem schurs {i j} [IsSimpleModule R (M i)] [IsSimpleModule R (M j)]
  (phi : M i →ₗ[R] M j) (h0 : phi ≠ 0) : Function.Bijective phi :=
  by
    have ker_eq_bot : LinearMap.ker phi = ⊥ := by

      rcases eq_bot_or_eq_top (LinearMap.ker phi) with h_bot | h_top
      · exact h_bot

      · have : phi = 0 := LinearMap.ker_eq_top.mp h_top
        contradiction

    have range_eq_top : LinearMap.range phi = ⊤ := by

      let induced_phi := first_iso_thm_modules phi

      let type_fix := Submodule.quotEquivOfEqBot (LinearMap.ker phi) ker_eq_bot

      let cleaner_iso : M i ≃ₗ[R] LinearMap.range phi := type_fix.symm.trans induced_phi

      -- Proof by contradiction.
      have range_neq_bot : LinearMap.range phi ≠ ⊥ := by
        intro range_eq_bot

        have : Subsingleton (M i) :=
          @Function.Injective.subsingleton _ _ _
          cleaner_iso.injective (Submodule.subsingleton_iff_eq_bot.mpr range_eq_bot)

        exact @not_subsingleton _ (IsSimpleModule.nontrivial R (M i)) this

      rcases eq_bot_or_eq_top (LinearMap.range phi) with eq_bot | eq_top
      · exact False.elim (range_neq_bot eq_bot)

      · exact eq_top

    exact ⟨LinearMap.ker_eq_bot.mp ker_eq_bot, LinearMap.range_eq_top.mp range_eq_top⟩

end schur

namespace temporary


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
   · simp
   · simp
     intro d dnb
     rw [if_neg dnb]
     exact LinearMap.map_zero (M a d)
   · simp

-- Use Equiv.toLinearEquiv? Not sure if needed, but it exists
-- Probably more sensible to just use this in situ with Schurs in final proof
end Lemma2


open scoped BigOperators


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

def RopToEndRMap
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
  --Homomorphism proof, these are trivial but messy hence the simps.
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

-- Homomorphism + bijective = isomorphism
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
Proof that for disctinct modules S_i such that Hom(S_i,S_j) = 0 for i≠j, End(⊕S_i) ≅ ⊕End(S_i).

We note that lemma 2, and this result, are special cases of the more general forumla
End(⊕M_i) = ⊕_i⊕_jHom(M_i,M_j) for some modules M_i. Note that this is a big matrix.
Thus, to prove this we need to show that for isotypic
(i.e. built out of copies of a single simple module) modules M,N, Hom(M,N) = 0,
that is, the big matrix is diagonal. Since lemma 2 is a special case, the proof goes similarly.
-/

variable {R : Type*} [Ring R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

--For the actual proof we need to first group our simple decompositon into isotypic modules,
--that is, we define S_i ≅ I^{n_i}_i so that each S_i is pairwise non-isomorphic
--Hence we need to show that if Hom(M,N) = 0, so does Hom(M^m,N^n).

theorem Isotypic_Hom_Eq_Zero
  (n m : ℕ) (R : Type) [Ring R] (S T : Type)
  [AddCommGroup S] [Module R S] [AddCommGroup T] [Module R T]
  (h_not_iso: ∀ f : S →ₗ[R] T, f = 0) (f : (Fin n → S) →ₗ[R] (Fin m → T)) : f = 0 := by
    apply LinearMap.ext
    intro v
    ext k
    rw [← Finset.univ_sum_single v, map_sum]
    simp
    apply Finset.sum_eq_zero --Want to show each term is 0
    intro j a
    let component_map : S →ₗ[R] T := {
      toFun := fun s => (f (Pi.single j s)) k -- this is the inclsion, map, projection
      map_add' := by
        intros x y
        rw [Pi.single_add, map_add, Pi.add_apply]
      map_smul' := by
         intros r s
         rw [Pi.single_smul, map_smul, Pi.smul_apply, RingHom.id_apply]
    }
    have h_zero := h_not_iso component_map
    change component_map (v j) = 0
    rw [h_zero, LinearMap.zero_apply]


open scoped BigOperators

--Same basic idea as lemma 2, but now much generalised using the above theorem
--we just consider the projections and inclusions in much the same way

def End_DirectSum_Equiv_DirectSum_End
    (h_pairwise : Pairwise (fun i j ↦ ∀ f : M i →ₗ[R] M j, f = 0)) :
    Module.End R ((i : ι) → M i) ≃+* Π i, Module.End R (M i) where
      --Defines Functions
      toFun F i := {
        toFun := fun m ↦ (F (Pi.single i m)) i
        map_add' := by
          intros x y
          rw [Pi.single_add, map_add, Pi.add_apply]
        map_smul' := by
          intros m x
          simp
          rw [Pi.single_smul, LinearMap.map_smul_of_tower, Pi.smul_apply]
    }
      invFun f := {
        toFun := fun v i ↦ f i (v i)
        map_add' := by
          intros x y
          ext i
          rw [Pi.add_apply,Pi.add_apply, LinearMap.map_add]
        map_smul' := by
          intros m x
          ext i
          rw [Pi.smul_apply, map_smul, RingHom.id_apply, Pi.smul_apply]
      }

    --Proof it's linear
      map_add' := by
        intros x y
        ext i j
        simp

-- I think this looks dense but its basically just showing the product of diagonal matrices is diag.
      map_mul' := by
        intros F G
        ext i m
        simp
        let v := G (Pi.single i m)
        have h_off_diag : ∀ j, i ≠ j → v j = 0 := by
          intros j hij
          let f : M i →ₗ[R] M j := { -- This reads out the j-th component of the image under G
            toFun := fun x ↦ (G (Pi.single i x)) j
            map_add' := by
              intros x y
              rw [Pi.single_add, map_add, Pi.add_apply]
            map_smul' := by
              intros m x
              rw [RingHom.id_apply, Pi.single_smul, LinearMap.map_smul_of_tower, Pi.smul_apply]
          }
          --This shows the j-th component from the above is 0, which is by schurs
          have : f = 0 :=  (h_pairwise hij) f
          exact LinearMap.congr_fun this m

        have hv_eq : v = Pi.single i (v i) := by
          ext j
          by_cases h : i = j
          · rw [h, Pi.single_eq_same]
          · rw [h_off_diag j h, Pi.single_eq_of_ne (Ne.symm h)]
        rw [← hv_eq]

      --Proof they're inverse
      right_inv := by
        intro f
        ext i m
        simp

--As with map_mul, this looks quite dense but is fine, we just need to define a map
--so that we can apply schurs lemma to say the off diagonals are 0
      left_inv := by
        intro F
        apply LinearMap.ext
        intro v
        ext k
        simp
        have h_sum_v : v = ∑ j, Pi.single j (v j) := by
          ext i
          rw [Finset.sum_apply]
          simp
        conv_rhs => rw [h_sum_v, map_sum, Finset.sum_apply]
        rw [Finset.sum_eq_single k]
        · intros j _ hjk -- We are showing that if j≠k, that term of the sum is 0
          let f_jk : M j →ₗ[R] M k := {
            toFun := fun m ↦ (F (Pi.single j m)) k
            map_add' := by
              intros x y
              rw [Pi.single_add, LinearMap.map_add, Pi.add_apply]
            map_smul' := by
              intros m x
              rw [RingHom.id_apply, Pi.single_smul, LinearMap.map_smul_of_tower, Pi.smul_apply]
          }
          have h_zero := (h_pairwise hjk) f_jk
          exact LinearMap.congr_fun h_zero (v j)
        · intro hk
          exact (hk (Finset.mem_univ _)).elim


namespace main_result


variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]


/-
NEW HELPER FUNCTION 4
Intended to provide isotypic decomposition of semisimple modules.

Also intended for usage in the proof of Lemma 5.
-/


theorem existence_of_isotypic_decomposition
  [IsArtinian R M] [IsSemisimpleModule R M] :
  ∃ (m : ℕ)
    (S : Fin m → Type*)
    (_ : ∀ i, AddCommGroup (S i)) (_ : ∀ i, Module R (S i))
    (_ : ∀ i, IsSimpleModule R (S i))
    (h_distinct : Pairwise (fun i j => ¬ Nonempty (S i ≃ₗ[R] S j)))
    (n : Fin m → ℕ),
  Nonempty (M ≃ₗ[R] Π i, Fin (n i) → S i) :=
  by
    sorry


namespace main_result

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]


/-
NEW HELPER FUNCTION 5
Hopefully says that isomorphic modules have isomorphic rings of endomorphisms.

Also intended for usage in the proof of Lemma 5.
-/


def ringConj {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (e : M ≃ₗ[R] N) : Module.End R M ≃+* Module.End R N :=
  {
    toFun := fun f => e.comp (f.comp e.symm.toLinearMap)
    invFun := fun f => e.symm.comp (f.comp e.toLinearMap)

    left_inv := fun f => by
      ext
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearEquiv.symm_apply_apply]

    right_inv := fun f => by
      ext
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearEquiv.apply_symm_apply]

    map_add' := fun f g => by
      ext
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearMap.add_apply, map_add]

    map_mul' := fun f g => by
      ext
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        Module.End.mul_apply, LinearEquiv.symm_apply_apply]
  }


/-
An attempted statement of Lemma 5, in slightly different form of that to the outline.

Proof difficult.
-/


theorem Lemma5
  [IsArtinian R M] [IsSemisimpleModule R M] :
  ∃ (m : ℕ)
    (D : Fin m → Type*) (_ : ∀ i, DivisionRing (D i))
    (n : Fin m → ℕ),
  Nonempty (Module.End R M ≃+* Π i, Matrix (Fin (n i)) (Fin (n i)) (D i)) :=
  by
    sorry


/-
This is a proof of lemma 5 from the outline, which states:
For a semi-simple Artinian right R module (left R^op module) M,
 End_R(M) ≅ ⊕ M_{a_i}(D_i)
for a division rings D_i and non-negative integers a_i.
The proof of this is essentially just colating all of the prior work.
-/

def End_SemisimpleM_Iso_Sum_Of_Matrices
  (R : Type*) [Ring R]
  (M : Type*) [AddCommGroup M] [Module Rᵐᵒᵖ M] [IsArtinian Rᵐᵒᵖ M] [IsSemisimpleModule Rᵐᵒᵖ M]
  (ι : Type*) (S : ι → Type*) [∀ i, AddCommGroup (S i)] [∀ i, Module Rᵐᵒᵖ (S i)] (n : ι → ℕ) :
  Module.End Rᵐᵒᵖ M ≃+* (∀ i : ι, Matrix (Fin (n i)) (Fin (n i)) (Module.End Rᵐᵒᵖ (S i))) := by
    sorry


/-
Artin-Wedderburn Theorem
-/


theorem artin_wedderburn {R : Type u} [Ring R] [IsArtinianRing R] [IsSemisimpleRing R] :
  ∃ (ι : ℕ) (n : Fin ι → ℕ) (D : Fin ι → Type u) (_ : ∀ i, DivisionRing (D i)),
  (∀ i, n i > 0) ∧ Nonempty (R ≃+* Π (i : Fin ι), Matrix (Fin (n i)) (Fin (n i)) (D i)) :=
  by
    obtain ⟨m_raw, (D_raw : Fin m_raw → Type u), h_div_raw, n_raw, ⟨iso_end⟩⟩ :=
      Lemma5 (R := R) (M := R)

    let valid_indices := { i : Fin m_raw // n_raw i > 0 }
    let ι := Fintype.card valid_indices
    let index_equiv : Fin ι ≃ valid_indices := (Fintype.equivFin valid_indices).symm
    let n : Fin ι → ℕ := fun i => n_raw (index_equiv i)
    let D : Fin ι → Type u := fun i => (D_raw (index_equiv i))ᵐᵒᵖ

    let h_is_divring : ∀ i, DivisionRing (D i) := fun i => inferInstance

    have h_ni_pos : ∀ i, n i > 0 := fun i => (index_equiv i).2

    let iso_R_EndOp : R ≃+* (Module.End R R)ᵐᵒᵖ :=
    {
      toFun := fun r => MulOpposite.op {
        toFun := fun x => x * r,
        map_add' := fun x y => add_mul x y r,
        map_smul' := fun s x => by simp [smul_eq_mul, mul_assoc]
      },

      invFun := fun f => (MulOpposite.unop f) 1,
      left_inv := fun r => one_mul r,

      right_inv := fun f => by
        let g := MulOpposite.unop f
        rw [← MulOpposite.op_unop f]
        apply congr_arg MulOpposite.op
        apply LinearMap.ext
        intro x
        change x * g 1 = g x
        calc
          x * g 1 = x • g 1 := by rw [smul_eq_mul]
          _ = g (x • 1) := by erw [LinearMap.map_smul]
          _ = g (x * 1) := by rw [smul_eq_mul]
          _ = g x := by rw [mul_one]

      map_mul' := fun r s => by sorry
      map_add' := fun r s => by sorry
    }

    let iso_matrix_op (i : Fin ι) :
        (Matrix (Fin (n i)) (Fin (n i)) (D_raw (index_equiv i)))ᵐᵒᵖ
          ≃+* Matrix (Fin (n i)) (Fin (n i)) (D i) :=
      {
        toFun := fun M_op =>
          let M := MulOpposite.unop M_op
          Matrix.of (fun j k => MulOpposite.op (M k j)),

        invFun := fun M =>
          MulOpposite.op (Matrix.of (fun j k => MulOpposite.unop (M k j))),

        left_inv := by exact congrFun rfl
        right_inv := by exact congrFun rfl
        map_add' := by
          intros
          simp only [MulOpposite.unop_add, Matrix.add_apply, MulOpposite.op_add,
            Matrix.of_add_of, EmbeddingLike.apply_eq_iff_eq]
          rfl,

        map_mul' := by sorry
      }

    let iso_pi_op :
      (Π (i : Fin m_raw), Matrix (Fin (n_raw i)) (Fin (n_raw i)) (D_raw i))ᵐᵒᵖ
        ≃+* Π (i : Fin m_raw), (Matrix (Fin (n_raw i)) (Fin (n_raw i)) (D_raw i))ᵐᵒᵖ :=
    {
      toFun := fun f i => MulOpposite.op ((MulOpposite.unop f) i),
      invFun := fun g => MulOpposite.op (fun i => MulOpposite.unop (g i)),
      left_inv := fun x => MulOpposite.op_unop x,
      right_inv := fun g => by ext; simp [MulOpposite.op_unop, MulOpposite.unop_op],
      map_add' := fun x y => by
        ext; simp [MulOpposite.unop_add, Pi.add_apply, MulOpposite.op_add]

      map_mul' := fun x y => by
        ext; simp [MulOpposite.unop_mul, Pi.mul_apply, MulOpposite.op_mul]
    }

    let drop_zeros :
      (Π (i : Fin m_raw), (Matrix (Fin (n_raw i)) (Fin (n_raw i)) (D_raw i))ᵐᵒᵖ)
        ≃+* (Π (i : valid_indices), (Matrix (Fin (n_raw i)) (Fin (n_raw i)) (D_raw i))ᵐᵒᵖ) :=
    {
      toFun := fun f i => f i,
      invFun := fun g i =>
        if h : n_raw i > 0 then g ⟨i, h⟩
        else MulOpposite.op 0,

      left_inv := fun f => by sorry
      right_inv := fun g => by ext ⟨i, h⟩; dsimp; rw [dif_pos h],
      map_add' := fun x y => by ext; rfl,
      map_mul' := fun x y => by ext; rfl
    }

    let reindex :
      (Π (i : valid_indices), (Matrix (Fin (n_raw i)) (Fin (n_raw i)) (D_raw i))ᵐᵒᵖ)
      ≃+* (Π (i : Fin ι), Matrix (Fin (n i)) (Fin (n i)) (D i)) :=
    {
      toFun := fun f j => iso_matrix_op j (f (index_equiv j)),
      invFun := fun g i => sorry,
      left_inv := fun f => by sorry,
      right_inv := fun g => by sorry,
      map_add' := fun x y => by ext; simp [Pi.add_apply, map_add],
      map_mul' := fun x y => by ext; simp [Pi.mul_apply, map_mul]
    }

    let final_composition : R ≃+* Π i, Matrix (Fin (n i)) (Fin (n i)) (D i) :=
      iso_R_EndOp.trans ((RingEquiv.op iso_end).trans (iso_pi_op.trans (drop_zeros.trans reindex)))

    refine ⟨ι, n, D, h_is_divring, ⟨h_ni_pos, ⟨?_⟩⟩⟩
    convert final_composition


end main_result

namespace Grave_Yard
/-
There were a number of theorems that we proved and didnt end up needing, or accidently did twice
by working independently. For completeness, we list them here.
-/

/-
NEW HELPER FUNCTION 1
Establishes that given our M_i are orthogonal, we have a ring isomorphism
between the endomorphism ring of the direct sum of M_i, and the product
of individual endomorphism rings of each M_i.

Intended for usage in the proof of Lemma 5.
-/

def End_DirectSum_Orthogonal
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (h_ortho : ∀ i j, i ≠ j → ∀ (f : M i →ₗ[R] M j), f = 0) :
  Module.End R ((i : ι) → M i) ≃+* Π i, Module.End R (M i)
  where
    toFun F i := {
      toFun := fun m ↦ (F (Pi.single i m)) i
      map_add' := by simp [Pi.single_add]
      map_smul' := by simp [Pi.single_smul]
    }

    invFun f := {
      toFun := fun v i ↦ f i (v i)
      map_add' := by
        intros
        ext
        simp [map_add]
      map_smul' := by
        intros
        ext
        simp [map_smul]
    }

    map_add' := by
      intros
      ext
      simp only [LinearMap.add_apply, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk]

    map_mul' := by
      intros F G
      ext i m
      simp only [Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, Pi.mul_apply]
      let v := G (Pi.single i m)

      have h_off_diag_is_zero : ∀ j, i ≠ j → v j = 0 := by
        intros j hij

        let f_ij : M i →ₗ[R] M j := {
          toFun := fun x ↦ (G (Pi.single i x)) j
          map_add' := by
            intros
            simp only [Pi.single_add, map_add, Pi.add_apply]
          map_smul' := by
            intros
            simp only [Pi.single_smul, map_smul, Pi.smul_apply, RingHom.id_apply]
        }

        exact LinearMap.congr_fun (h_ortho i j hij f_ij) m

      have hv_eq : v = Pi.single i (v i) := by
        ext j; by_cases h : i = j
        · rw [h, Pi.single_eq_same]
        · rw [h_off_diag_is_zero j h, Pi.single_eq_of_ne (Ne.symm h)]

      rw [← hv_eq]

    left_inv := by sorry

    right_inv := by
      intro f
      ext
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.single_eq_same]

/-
NEW HELPER FUNCTION 2
Should give a ring isomorphism between the endomorphism ring of a finite direct sum of
the module S and the ring of matrices over the endomorphism ring of S.

Also intended for usage in the proof of Lemma 5.
This is actually just lemma2 again
-/


def End_PowerOfS_Equiv_Matrix
  (S : Type*) [AddCommGroup S] [Module R S] (n : ℕ) :
  Module.End R (Fin n → S) ≃+* Matrix (Fin n) (Fin n) (Module.End R S)
  where
    toFun f i j := {
      toFun := fun s ↦ (f (Pi.single j s)) i

      map_add' := by
        intros
        simp only [Pi.single_add, map_add, Pi.add_apply]

      map_smul' := by
        intros
        simp only [Pi.single_smul, map_smul, Pi.smul_apply, RingHom.id_apply]
    }

    invFun M := {
      toFun := fun v i ↦ ∑ j, (M i j) (v j)

      map_add' := by
        intros
        funext
        simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]

      map_smul' := by
        intros
        funext
        simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]
    }

    map_add' := by
      intros
      ext
      simp only [LinearMap.add_apply, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk,
        Matrix.add_apply]

    map_mul' := by
      intros f g
      ext i j s
      dsimp only [Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk]

      have h_vector_decomp : (g (Pi.single j s)) = ∑ k, Pi.single k ((g (Pi.single j s)) k) := by
        ext k
        simp only [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ,
          ↓reduceIte]

      rw [h_vector_decomp]
      rw [map_sum]
      simp [Finset.sum_apply]

      rw [Matrix.mul_apply]
      simp only [LinearMap.coeFn_sum, Finset.sum_apply, Module.End.mul_apply, LinearMap.coe_mk,
        AddHom.coe_mk]

    left_inv := by
      intro f
      apply LinearMap.ext
      intro vec
      ext k
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk]

      have h_vector_decomp : vec = ∑ idx, Pi.single idx (vec idx) := by
        ext idx
        simp only [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ,
          ↓reduceIte]

      conv_rhs =>
        rw [h_vector_decomp]
        rw [map_sum]
        rw [Finset.sum_apply]

    right_inv := by
      intro M
      ext i j s
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [Finset.sum_eq_single j]
      · simp only [Pi.single_eq_same]
      · intros k _ h_neq
        simp only [Pi.single_apply, if_neg h_neq, map_zero]
      · intro h; exact (h (Finset.mem_univ j)).elim

/-
NEW HELPER FUNCTION 3
Hopefully proves that if S and T are simple modules that are not isomorphic, then
their direct sums are orthogonal.

Also intended for usage in the proof of Lemma 5.
-/


theorem isotypic_orthogonality
  {S T : Type*} [AddCommGroup S] [Module R S] [AddCommGroup T] [Module R T]
  [IsSimpleModule R S] [IsSimpleModule R T]
  (n m : ℕ)
  (h_distinct : ¬ Nonempty (S ≃ₗ[R] T))
  (f : (Fin n → S) →ₗ[R] (Fin m → T)) : f = 0 :=
  by
    apply LinearMap.ext
    intro vec
    ext k

    have h_decomp : vec = ∑ idx, Pi.single idx (vec idx) := by
      ext idx
      simp only [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

    rw [h_decomp, map_sum, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intros j _

    let f_component : S →ₗ[R] T := {
      toFun := fun s ↦ (f (Pi.single j s)) k

      map_add' := by simp only [Pi.single_add, map_add, Pi.add_apply, implies_true]

      map_smul' := by simp only [Pi.single_smul, map_smul, Pi.smul_apply, RingHom.id_apply,
        implies_true]
    }

    have h_map_is_zero : f_component = 0 := by
      by_contra h_nonzero

      have h_ker : LinearMap.ker f_component = ⊥ :=
        (eq_bot_or_eq_top (LinearMap.ker f_component)).resolve_right
        (fun h_top => h_nonzero (LinearMap.ker_eq_top.mp h_top))

      have h_range : LinearMap.range f_component = ⊤ :=
        (eq_bot_or_eq_top (LinearMap.range f_component)).resolve_left
        (fun h_bot => h_nonzero (LinearMap.range_eq_bot.mp h_bot))

      exact h_distinct ⟨LinearEquiv.ofBijective f_component
        ⟨LinearMap.ker_eq_bot.mp h_ker, LinearMap.range_eq_top.mp h_range⟩⟩

    change f_component (vec j) = 0
    rw [h_map_is_zero]
    simp


/- Lemma3-/

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


variable {R : Type*} [Ring R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

--Basically just schurs lemma, if a map between simple modules isnt an iso, its 0.
theorem Simple_Hom_Eq_Zero_If_Not_Iso
    {i j : ι} [IsSimpleModule R (M i)] [IsSimpleModule R (M j)]
    (h_not_iso : ¬ Nonempty (M i ≃ₗ[R] M j)) (f : M i →ₗ[R] M j) : f = 0 := by
    classical
    by_contra hf
    apply h_not_iso
    have h' : Function.Bijective f :=
    schur.schurs (i := i) (j := j) f hf
    refine ⟨LinearEquiv.ofBijective f h'⟩
