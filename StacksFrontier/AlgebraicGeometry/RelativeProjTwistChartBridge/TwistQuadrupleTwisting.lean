module

public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistChartBridge.ThetaUniversalComparison
public import StacksFrontier.AlgebraicGeometry.TwistTensor.GradedLaurentUnit
public import StacksFrontier.AlgebraicGeometry.TwistTensor.PsiLegUnit
public import StacksFrontier.AlgebraicGeometry.TwistTensor.PsiLegVeroneseMultiplicative
public import StacksFrontier.AlgebraicGeometry.TwistTensor.DegreeOpenTwistInvertible
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineTwisting

/-!
# The twisting of the glued twists along a morphism into the degree-`d` locus

Let `r : T ⟶ Proj_S(𝒜)` be a morphism over `f : T ⟶ S` landing in the relative degree-`d` locus
`U_d`. The glued twists of [Stacks, Tag 01NR] then give a map of graded algebras

`f^*𝒜^{(d)} ⟶ r^*(⨁_n 𝒪(nd)) ≅ ⨁_n (r^*𝒪(d))^{⊗ n}` ,

the second leg `...RelativeProjTwists.TwistData.psiLegVeronese` followed by the recognition
comparison `...RelativeVeroneseTwists.laurentComparisonOfDegreeOpen` at the identity of
`r^*𝒪(d)`. This file packages it as a `...RelativeProjQcohSheaf.Twisting`.

## Main definitions

* `...RelativeProjTwistChartBridge.twistLine`: `r^*𝒪(d)`.
* `...RelativeProjTwistChartBridge.twistRecognition`: the recognition comparison
  `r^*(⨁_n 𝒪(nd)) ≅ ⨁_n (r^*𝒪(d))^{⊗ n}`.
* `...RelativeProjTwistChartBridge.twistTwisting`: the twisting.

## References

* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.RingedSpace
open Stacks.PullbackTensorCoherence
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.RelativeVeroneseTwists

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge

variable {S T : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} (D : TwistData A) (d : ℕ)
  (r : T ⟶ (relativeProj A).scheme)

/-- `r^*𝒪(d)`, the degree-one piece of `r^*(⨁_n 𝒪(nd))`. -/
abbrev twistLine : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace) :=
  (pullbackTwistVeronese D (d : ℤ) r).piece 1

variable (hg : ∀ t : T, r.base t ∈ (relativeProj A).degreeOpen d)
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T)
    (twistLine D d r)]

/-- The recognition comparison `r^*(⨁_n 𝒪(nd)) ≅ ⨁_n (r^*𝒪(d))^{⊗ n}` at the identity of
`r^*𝒪(d)`. -/
def twistRecognition : pullbackTwistVeronese D (d : ℤ) r ≅ laurent (twistLine D d r) :=
  laurentComparisonOfDegreeOpen D d r hg (Iso.refl _)

/-- The recognition comparison is multiplicative, in the morphism-level form. -/
theorem twistRecognition_mulSheaf (i j : ℤ) :
    SheafOfModules.GradedAlgebra.mulSheaf (pullbackTwistVeronese D (d : ℤ) r) i j ≫
        (twistRecognition D d r hg).hom.app (i + j) =
      ((twistRecognition D d r hg).hom.app i ⊗ₘ (twistRecognition D d r hg).hom.app j) ≫
        SheafOfModules.GradedAlgebra.mulSheaf (laurent (twistLine D d r)) i j :=
  GradedLaurentRecognition.pieceIso_mulSheaf _ _ _ _ _ i j

variable {f : T ⟶ S} (hr : r ≫ (relativeProj A).toBase = f)

/-- The degreewise components of the twisting. -/
def twistApp (n : ℤ) :
    (pullbackFunctor (ringedSpaceHom f)).obj ((situationAlgebra A).piece (n * d)) ⟶
      (laurent (twistLine D d r)).piece n :=
  D.psiLegVeronese r hr (d : ℤ) n ≫ (twistRecognition D d r hg).hom.app n

/-- The degreewise components of the twisting are multiplicative: the product of the
components in degrees `i` and `j` is the multiplication of `f^*𝒜^{(d)}` followed by the
component in degree `i + j`. -/
theorem twistApp_mul (i j : ℤ) :
    MonoidalCategoryStruct.tensorHom (twistApp D d r hg hr i) (twistApp D d r hg hr j) ≫
        (laurent (twistLine D d r)).mulSheaf i j =
      inv (pullbackTensorComparison (ringedSpaceHom f) ((situationAlgebra A).piece (i * d))
          ((situationAlgebra A).piece (j * d))) ≫
        (pullbackFunctor (ringedSpaceHom f)).map
          ((situationAlgebra A).mulSheaf (i * d) (j * d) ≫
            eqToHom (congrArg (situationAlgebra A).piece
              (by ring : i * (d : ℤ) + j * d = (i + j) * d))) ≫
        twistApp D d r hg hr (i + j) := by
  have hL : (Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra (ringedSpaceHom f)
        (GradedVeronese.veronese (situationAlgebra A) (d : ℤ)) (isSheafStruct S)).mulSheaf i j =
      inv (pullbackTensorComparison (ringedSpaceHom f) ((situationAlgebra A).piece (i * d))
          ((situationAlgebra A).piece (j * d))) ≫
        (pullbackFunctor (ringedSpaceHom f)).map
          ((situationAlgebra A).mulSheaf (i * d) (j * d) ≫
            eqToHom (congrArg (situationAlgebra A).piece
              (by ring : i * (d : ℤ) + j * d = (i + j) * d))) :=
    (ProjRepresentsF1.mulSheaf_pullbackGradedAlgebra (f := f)
        (GradedVeronese.veronese (situationAlgebra A) (d : ℤ)) i j).trans
      (congrArg (fun z =>
          inv (pullbackTensorComparison (ringedSpaceHom f) ((situationAlgebra A).piece (i * d))
              ((situationAlgebra A).piece (j * d))) ≫
            (pullbackFunctor (ringedSpaceHom f)).map z)
        (GradedVeronese.veronese_mulSheaf (situationAlgebra A) (d : ℤ) i j))
  have hleg := D.psiLegVeronese_mulSheaf r hr (d : ℤ) i j
  rw [hL] at hleg
  have h1 : MonoidalCategoryStruct.tensorHom (twistApp D d r hg hr i) (twistApp D d r hg hr j) =
      (D.psiLegVeronese r hr (d : ℤ) i ⊗ₘ D.psiLegVeronese r hr (d : ℤ) j) ≫
        ((twistRecognition D d r hg).hom.app i ⊗ₘ (twistRecognition D d r hg).hom.app j) :=
    (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _).symm
  refine (congrArg (fun z => z ≫ (laurent (twistLine D d r)).mulSheaf i j) h1).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => (D.psiLegVeronese r hr (d : ℤ) i ⊗ₘ
      D.psiLegVeronese r hr (d : ℤ) j) ≫ z) (twistRecognition_mulSheaf D d r hg i j).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ (twistRecognition D d r hg).hom.app (i + j)) hleg.symm).trans ?_
  exact (Category.assoc _ _ _).trans (Category.assoc _ _ _)

omit [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T)
  (twistLine D d r)] in
/-- The transpose of the homogeneous-section map carries the degree-shifted unit to the
degree-shifted unit, with the degree free. -/
theorem psiTranspose_unit_shift (m : ℤ) (h : (0 : ℤ) = m) :
    (D.psiTranspose m).val.app (op ((relativeProj A).toBase ⁻¹ᵁ ⊤))
        (pullbackUnit (ringedSpaceHom (relativeProj A).toBase) (A.piece m) (op ⊤)
          ((eqToHom (congrArg A.piece h) : A.piece 0 ⟶ A.piece m).val.app (op ⊤)
            (A.one ⊤))) =
      (eqToHom (congrArg D.algebra.piece h) : D.algebra.piece 0 ⟶ D.algebra.piece m).val.app
        (op ⊤) (D.algebra.one.eval (op ⊤)) := by
  subst h
  exact D.psiTranspose_zero_unit ⊤

omit [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T)
  (twistLine D d r)] in
/-- **The second leg carries the unit to the unit**: the unit of `f^*𝒜^{(d)}` followed by the
leg in degree zero is the unit of `r^*(⨁_n 𝒪(nd))`. -/
theorem psiLegVeronese_one :
    Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) (situationAlgebra A) ≫
        (pullbackFunctor (ringedSpaceHom f)).map
          (eqToHom (congrArg (situationAlgebra A).piece (by ring : (0 : ℤ) = 0 * d))) ≫
        D.psiLegVeronese r hr (d : ℤ) 0 =
      SheafOfModules.GradedAlgebra.oneHom (pullbackTwistVeronese D (d : ℤ) r) := by
  subst hr
  have h0 : (0 : ℤ) = 0 * (d : ℤ) := by ring
  have hL : (Stacks.PullbackGradedAlgebra.pullbackOne
        (ringedSpaceHom (r ≫ (relativeProj A).toBase)) (situationAlgebra A) ≫
        (pullbackFunctor (ringedSpaceHom (r ≫ (relativeProj A).toBase))).map
          (eqToHom (congrArg (situationAlgebra A).piece h0)) ≫
        D.psiLegVeronese r rfl (d : ℤ) 0).val.app (op ⊤) (oneSec T.toRingedSpace (op ⊤)) =
      pullbackUnit (ringedSpaceHom r) (D.algebra.piece (0 * d)) (op ⊤)
        ((eqToHom (congrArg D.algebra.piece h0) :
          D.algebra.piece 0 ⟶ D.algebra.piece (0 * d)).val.app (op ⊤)
          (D.algebra.one.eval (op ⊤))) := by
    refine (congrArg (fun z => (D.psiLegVeronese r rfl (d : ℤ) 0).val.app (op ⊤)
      (((pullbackFunctor (ringedSpaceHom (r ≫ (relativeProj A).toBase))).map
          (eqToHom (congrArg (situationAlgebra A).piece h0))).val.app (op ⊤) z))
      (AffineTwisting.pullbackOne_val_app_oneSec (r ≫ (relativeProj A).toBase)
        (situationAlgebra A))).trans ?_
    refine (congrArg (fun z => (D.psiLegVeronese r rfl (d : ℤ) 0).val.app (op ⊤) z)
      (pullbackUnit_naturality (ringedSpaceHom (r ≫ (relativeProj A).toBase))
        (eqToHom (congrArg (situationAlgebra A).piece h0)) (op ⊤) _)).trans ?_
    refine (congrArg (fun φ => φ.val.app (op ⊤)
      (pullbackUnit (ringedSpaceHom (r ≫ (relativeProj A).toBase)) (A.piece (0 * d)) (op ⊤)
        ((eqToHom (congrArg (situationAlgebra A).piece h0)).val.app (op ⊤)
          ((situationAlgebra A).one.eval (op ⊤))))) (D.psiLeg_rfl_eq r (0 * (d : ℤ)))).trans ?_
    refine (congrArg (fun z =>
        ((pullbackFunctor (ringedSpaceHom r)).map (D.psiTranspose (0 * (d : ℤ)))).val.app
          (op ⊤) z)
      (Stacks.PullbackCompMonoidal.comparison_pullbackUnit
        (ringedSpaceHom (relativeProj A).toBase) (ringedSpaceHom r) _ (op ⊤) _)).trans ?_
    refine (pullbackUnit_naturality (ringedSpaceHom r) (D.psiTranspose (0 * (d : ℤ)))
      (op ⊤) _).trans ?_
    exact congrArg (pullbackUnit (ringedSpaceHom r) (D.algebra.piece (0 * d)) (op ⊤))
      (psiTranspose_unit_shift D (0 * (d : ℤ)) h0)
  have hR : (SheafOfModules.GradedAlgebra.oneHom (pullbackTwistVeronese D (d : ℤ) r)).val.app
        (op ⊤) (oneSec T.toRingedSpace (op ⊤)) =
      pullbackUnit (ringedSpaceHom r) (D.algebra.piece (0 * d)) (op ⊤)
        ((eqToHom (congrArg D.algebra.piece h0) :
          D.algebra.piece 0 ⟶ D.algebra.piece (0 * d)).val.app (op ⊤)
          (D.algebra.one.eval (op ⊤))) :=
    (oneMorphism_val_app_oneSec (pullbackTwistVeronese D (d : ℤ) r) (op ⊤)).trans
      (pullbackSectionsUnit_eval (ringedSpaceHom r) _ _ ⊤)
  exact (SheafOfModules.unitHomEquiv _).injective
    (AffineTwisting.sections_eq_of_eval_top _ _ _ (hL.trans hR.symm))

/-- The degreewise components carry the unit to the unit. -/
theorem twistApp_one :
    Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f) (situationAlgebra A) ≫
        (pullbackFunctor (ringedSpaceHom f)).map
          (eqToHom (congrArg (situationAlgebra A).piece (by ring : (0 : ℤ) = 0 * d))) ≫
        twistApp D d r hg hr 0 =
      SheafOfModules.GradedAlgebra.oneHom (laurent (twistLine D d r)) := by
  refine (congrArg (fun z => Stacks.PullbackGradedAlgebra.pullbackOne (ringedSpaceHom f)
      (situationAlgebra A) ≫ z) (Category.assoc _ _ _).symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ (twistRecognition D d r hg).hom.app 0)
    (psiLegVeronese_one D d r hr)).trans ?_
  exact GradedLaurentRecognition.oneHom_comp_gradedIso_app_zero _ _ _ _ _

/-- **The twisting of the glued twists along `r`**: the second leg of [Stacks, Tag 01O1]'s
triangle followed by the recognition comparison, a twisting `f^*𝒜^{(d)} ⟶ ⨁_n (r^*𝒪(d))^{⊗ n}`
over `f`. -/
def twistTwisting : Twisting f (situationAlgebra A) (d : ℤ) (twistLine D d r) where
  app n := twistApp D d r hg hr n
  app_mul i j := twistApp_mul D d r hg hr i j
  app_one := twistApp_one D d r hg hr

/-- The degree-`n` component of `twistTwisting` is the second leg in degree `n` followed by
the recognition comparison in degree `n`. -/
@[simp] theorem twistTwisting_app (n : ℤ) :
    (twistTwisting D d r hg hr).app n =
      D.psiLegVeronese r hr (d : ℤ) n ≫ (twistRecognition D d r hg).hom.app n := rfl

end Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge

end
