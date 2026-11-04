module

public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.GradedRealizationPullbackIso
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.NonnegTruncationFunctorial

/-!
# The degreewise pullback commutes with the nonnegative truncation

Let `g : X ⟶ Y` be a morphism of schemes and `𝒞` a sheaf of `ℤ`-graded `𝒪_Y`-algebras. There are
two ways to reach a nonnegatively graded `𝒪_X`-algebra from it: truncate and then pull back
degreewise, or pull back and then truncate. **This file identifies them**, as sheaves of graded
algebras and then as algebra sheaves.

In a nonnegative degree the two agree on the nose — the truncation leaves nonnegative degrees
alone (`Stacks.AlgebraicGeometry.NonnegTruncation.piece_ofNat`), and so does the degreewise
pullback — and so do their multiplications and their units. In a negative degree one is the
pullback of a zero object and the other is a zero object; the pullback of sheaves of modules is
additive (`RingedSpaceModuleAdjunction.modulePullback_additive`), so the first is a zero object
too, and the unique morphism between them is an isomorphism.

## Main definitions

* `Stacks.GradedRealizationPullback.nonnegTruncationComm`: **the comparison
  `g^*(𝒞_{≥0}) ⟶ (g^*𝒞)_{≥0}`** as a unital homomorphism of sheaves of graded algebras — the
  identity in a nonnegative degree and the zero morphism between two zero objects in a negative
  one.
* `Stacks.GradedRealizationPullback.nonnegTruncationAlgebraSheafComparisonIso`: **the algebra
  pullback of the ungraded realisation of `𝒞_{≥0}` is the ungraded realisation of
  `(g^*𝒞)_{≥0}`**.

## Main results

* `Stacks.GradedRealizationPullback.isIso_nonnegTruncationComm_app`: the comparison is an
  isomorphism in every degree.

## References

* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec Stacks.RingedSpace
open Stacks.AlgebraicGeometry.NonnegTruncation

universe u

namespace Stacks.GradedRealizationPullback

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (𝒞 : SheafOfModules.GradedAlgebra.{u, u} Y.ringCatSheaf)

/-! ### The negative degrees are zero on both sides -/

/-- The pullback of sheaves of modules along a morphism of schemes is additive. -/
instance additive_pullback : (Scheme.Modules.pullback g).Additive :=
  RingedSpaceModuleAdjunction.modulePullback_additive g.toLRSHom.toShHom

/-- **The degreewise pullback of the truncation is a zero object in a negative degree**: it is
the pullback of a zero object, and the pullback is additive. -/
theorem isZero_pbGraded_nonnegTruncation_piece_negSucc (n : ℕ) :
    IsZero ((pbGraded g (nonnegTruncation 𝒞)).piece (.negSucc n)) :=
  IsZero.of_iso (isZero_zero _) ((Scheme.Modules.pullback g).mapZeroObject)

/-- A local section of the degreewise pullback of the truncation in a negative degree is zero. -/
theorem eq_zero_pbGraded_nonnegTruncation_negSucc (n : ℕ) (U : (Opens ↥X)ᵒᵖ)
    (x : ((pbGraded g (nonnegTruncation 𝒞)).piece (.negSucc n)).val.obj U) : x = 0 :=
  eq_zero_of_isZero (isZero_pbGraded_nonnegTruncation_piece_negSucc g 𝒞 n) U x

/-! ### The comparison -/

/-- The degreewise components of the comparison `g^*(𝒞_{≥0}) ⟶ (g^*𝒞)_{≥0}`: the identity in a
nonnegative degree, where both sides are `g^*𝒞ₙ`, and the zero morphism between the two zero
objects in a negative degree. -/
def nonnegTruncationCommApp : ∀ n : ℤ,
    (pbGraded g (nonnegTruncation 𝒞)).piece n ⟶ (nonnegTruncation (pbGraded g 𝒞)).piece n
  | .ofNat _ => 𝟙 _
  | .negSucc _ => 0

/-- In a nonnegative degree the comparison component is the identity. -/
@[simp] theorem nonnegTruncationCommApp_ofNat (n : ℕ) :
    nonnegTruncationCommApp g 𝒞 (.ofNat n) = 𝟙 _ := rfl

/-- In a negative degree the comparison component is the zero morphism. -/
@[simp] theorem nonnegTruncationCommApp_negSucc (n : ℕ) :
    nonnegTruncationCommApp g 𝒞 (.negSucc n) = 0 := rfl

/-- **The comparison `g^*(𝒞_{≥0}) ⟶ (g^*𝒞)_{≥0}`**, as a unital homomorphism of sheaves of graded
algebras, with components `nonnegTruncationCommApp`. -/
def nonnegTruncationComm :
    SheafOfModules.GradedAlgebra.UnitalHom (pbGraded g (nonnegTruncation 𝒞))
      (nonnegTruncation (pbGraded g 𝒞)) where
  app := nonnegTruncationCommApp g 𝒞
  map_mul i j U x y := by
    rcases i with a | a
    · rcases j with b | b
      · rfl
      · have hL : ((pbGraded g (nonnegTruncation 𝒞)).mul (a : ℤ) (Int.negSucc b)).app U x y
            = 0 := by
          rw [eq_zero_pbGraded_nonnegTruncation_negSucc g 𝒞 b U y, map_zero]
        refine Eq.trans (congrArg
          (fun z => (nonnegTruncationCommApp g 𝒞 ((a : ℤ) + Int.negSucc b)).val.app U z) hL) ?_
        exact (map_zero _).trans
          (mul_app_apply_eq_zero_of_neg_right (pbGraded g 𝒞) (a : ℤ) b U _ _).symm
    · have hL : ((pbGraded g (nonnegTruncation 𝒞)).mul (Int.negSucc a) j).app U x y = 0 := by
        rw [eq_zero_pbGraded_nonnegTruncation_negSucc g 𝒞 a U x, map_zero,
          AddMonoidHom.zero_apply]
      refine Eq.trans (congrArg
        (fun z => (nonnegTruncationCommApp g 𝒞 (Int.negSucc a + j)).val.app U z) hL) ?_
      exact (map_zero _).trans
        (mul_app_apply_eq_zero_of_neg_left (pbGraded g 𝒞) a j U _ _).symm
  map_one _ := rfl

/-- The degree-`n` component of `nonnegTruncationComm` is `nonnegTruncationCommApp`. -/
@[simp] theorem nonnegTruncationComm_app (n : ℤ) :
    (nonnegTruncationComm g 𝒞).app n = nonnegTruncationCommApp g 𝒞 n := rfl

/-- **The comparison is an isomorphism in every degree.** In a nonnegative degree it is the
identity; in a negative degree it is the zero morphism between two zero objects. -/
theorem isIso_nonnegTruncationComm_app (n : ℤ) :
    IsIso ((nonnegTruncationComm g 𝒞).app n) := by
  rcases n with a | a
  · rw [nonnegTruncationComm_app, nonnegTruncationCommApp_ofNat]
    exact ⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩
  · rw [nonnegTruncationComm_app, nonnegTruncationCommApp_negSucc]
    exact ⟨0, (isZero_pbGraded_nonnegTruncation_piece_negSucc g 𝒞 a).eq_of_src _ _,
      (isZero_piece_negSucc (pbGraded g 𝒞) a).eq_of_src _ _⟩

/-! ### The algebra sheaves -/

section Algebra

variable (hc : ∀ (i j : ℤ) (W : (Opens ↥Y)ᵒᵖ) (a : (𝒞.piece i).val.obj W)
  (b : (𝒞.piece j).val.obj W), HEq ((𝒞.mul i j).app W a b) ((𝒞.mul j i).app W b a))

/-- **The ungraded realisation of `g^*(𝒞_{≥0})` is that of `(g^*𝒞)_{≥0}`**, as sheaves of
commutative `𝒪_X`-algebras: `Stacks.RelativeSpec.gradedAlgebraSheafIso` applied to
`nonnegTruncationComm`, which is an isomorphism in every degree. -/
def nonnegTruncationCommAlgebraSheafIso :
    gradedAlgebraSheaf X (pbGraded g (nonnegTruncation 𝒞))
        (pbGraded_mul_comm g (nonnegTruncation 𝒞) (isCommutative_nonnegTruncation 𝒞 hc)) ≅
      gradedAlgebraSheaf X (nonnegTruncation (pbGraded g 𝒞))
        (isCommutative_nonnegTruncation (pbGraded g 𝒞) (pbGraded_mul_comm g 𝒞 hc)) :=
  haveI : ∀ n : ℤ, IsIso ((nonnegTruncationComm g 𝒞).app n) :=
    isIso_nonnegTruncationComm_app g 𝒞
  gradedAlgebraSheafIso X
    (pbGraded_mul_comm g (nonnegTruncation 𝒞) (isCommutative_nonnegTruncation 𝒞 hc))
    (isCommutative_nonnegTruncation (pbGraded g 𝒞) (pbGraded_mul_comm g 𝒞 hc))
    (nonnegTruncationComm g 𝒞)

/-- **The algebra pullback of the ungraded realisation of `𝒞_{≥0}` is the ungraded realisation of
`(g^*𝒞)_{≥0}`**: the composite of `Stacks.GradedRealizationPullback.comparisonIso` for the
truncated algebra with `nonnegTruncationCommAlgebraSheafIso`. -/
def nonnegTruncationAlgebraSheafComparisonIso :
    (algebraPullback g).obj
        (gradedAlgebraSheaf Y (nonnegTruncation 𝒞)
          (isCommutative_nonnegTruncation 𝒞 hc)) ≅
      gradedAlgebraSheaf X (nonnegTruncation (pbGraded g 𝒞))
        (isCommutative_nonnegTruncation (pbGraded g 𝒞) (pbGraded_mul_comm g 𝒞 hc)) :=
  comparisonIso g (nonnegTruncation 𝒞) (isCommutative_nonnegTruncation 𝒞 hc) ≪≫
    nonnegTruncationCommAlgebraSheafIso g 𝒞 hc

end Algebra

end Stacks.GradedRealizationPullback

end
