module

public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerSolutionRealization
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.FlatProperOfIdealSheafMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionRealizationConormal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionRealizationOfCharts

/-!
# The square of first order thickenings of a realized solution of the tower problem

In the situation of `AlgebraicGeometry.ProperFlatFibre.towerProblem`, let `X₀ ⊂ X'` be a
realization over `Y = Spec(lim Rₙ)` of a solution `𝒪'` of the tower problem
(`AlgebraicGeometry.ProperFlatFibre.nonempty_towerSolutionRealization`). The closed subspace
`X₀ ⊂ X'` maps to the closed subspace `Y₀ ⊂ Y` through `X₀ ⟶ Y₀`, giving the morphism of first
order thickenings `(X₀ ⊂ X') ⟶ (Y₀ ⊂ Y)` of the body of the proof of
[Stacks Project, Tag 0D3X]. We show that this square commutes and that its top arrow is flat,
proper and of finite presentation. The invertibility of its conormal map
`f^*𝒞_{Y₀/Y} ⟶ 𝒞_{X₀/X'}` (Stacks 04CP) is the next step: by
`AlgebraicGeometry.Space.isIso_conormalMapOfImmersions_of_isIso_map_idealSheafMap` and
`AlgebraicGeometry.Space.isIso_of_isIso_modulePullback_map` it is that of the map
`g^*𝓘_{Y₀} ⟶ 𝓘_{X₀}` of defining ideals, pulled back to `X₀ ⊂ X'` and read on `X₀`.

## Main definitions

All names below are in the namespace `AlgebraicGeometry.ProperFlatFibre`.

* `towerRealizationClosedMap`: `(X₀ ⊂ X') ⟶ (Y₀ ⊂ Y)`.

## Main results

* `towerRealization_sq`: the square commutes.
* `isFlat_isProper_isFinitePresentation_towerRealizationClosedMap`: `(X₀ ⊂ X') ⟶ (Y₀ ⊂ Y)` is
  flat, proper and of finite presentation.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

/-- In a category, if `m = ρ ≫ ι`, `m ≫ h = f ≫ s` and `r ≫ j = s` for an isomorphism `ρ`, then
`ι ≫ h = (ρ⁻¹ ≫ f ≫ r) ≫ j`. -/
theorem CategoryTheory.comp_eq_iso_inv_comp_comp_comp {C : Type*} [Category C] {A Z X Y Y₀ W : C}
    (ρ : A ≅ Z) (ι : Z ⟶ X) (m : A ⟶ X) (h : X ⟶ Y) (f : A ⟶ Y₀) (r : Y₀ ⟶ W) (j : W ⟶ Y)
    {s : Y₀ ⟶ Y} (hm : m = ρ.hom ≫ ι) (hh : m ≫ h = f ≫ s) (hr : r ≫ j = s) :
    ι ≫ h = (ρ.inv ≫ f ≫ r) ≫ j := by
  subst hm hr
  rw [Category.assoc, Category.assoc, ← hh]
  simp

namespace AlgebraicGeometry.ProperFlatFibre

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (ξ : ℕ ⥤ CartesianProperFlatSpaces B S hS)
  {Λ : Type u} [CommRing Λ] {R : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ}
  (hsurj : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), Function.Surjective (R.map f).hom)
  (hsq : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), RingHom.ker (R.map f).hom.toRingHom ^ 2 = ⊥)
  (e : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).obj (towerBase ξ n) ≅
    Spec (.of (R.obj (.op n))))
  (cR : Cone R) (hcR : IsLimit cR) (c : Cocone (ξ ⋙ cartesianProperFlatProjection B S hS))
  (eLimit : (BigFppfOver.toScheme B S hS).obj c.pt ≅ Spec (.of cR.pt))
  (hc : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).map (c.ι.app n) ≫ eLimit.hom =
    (e n).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (cR.π.app (.op n)).hom.toRingHom).op)
  {P' : (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).CompatibleFirstOrderThickening}
  (X' : Space.EtaleSquareZeroExtension.Realization
    (towerSolutionSquareZeroExtension ξ hsurj hsq e cR hcR c eLimit hc P'))

/-- **The morphism `(X₀ ⊂ X') ⟶ (Y₀ ⊂ Y)` of closed subspaces**: `(X₀ ⊂ X') ≅ X₀ ⟶ Y₀ ≅
(Y₀ ⊂ Y)`. -/
abbrev towerRealizationClosedMap :
    (⟨(Space.EtaleSquareZeroExtension.Realization.closedSubspace X').1.toFunctor, (Space.EtaleSquareZeroExtension.Realization.closedSubspace X').2.1⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨(limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc).1.toFunctor,
        (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc).2.1⟩ :=
  (Space.EtaleSquareZeroExtension.Realization.closedSpaceIso X').inv ≫ towerStructureMap ξ 0 ≫
    (limitBaseRangeIso ξ hsurj hsq e cR hcR c eLimit hc).hom

/-- **The square `(X₀ ⊂ X') ⟶ (Y₀ ⊂ Y)` commutes**: `X₀ ⟶ X' ⟶ Y` is `X₀ ⟶ Y₀ ⟶ Y`. -/
theorem towerRealization_sq :
    Space.subspaceInclusion B S hS X'.ambient (Space.EtaleSquareZeroExtension.Realization.closedSubspace X') ≫ X'.toBase =
      towerRealizationClosedMap ξ hsurj hsq e cR hcR c eLimit hc X' ≫
        Space.subspaceInclusion B S hS (schemeSpace c.pt)
          (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc) :=
  CategoryTheory.comp_eq_iso_inv_comp_comp_comp (Space.EtaleSquareZeroExtension.Realization.closedSpaceIso X') _ _ _ _ _ _
    (Space.EtaleSquareZeroExtension.Realization.immersion_eq_closedSpaceIso_hom_comp X') X'.over_base
    (Space.rangeSpaceIso_hom_comp_subspaceInclusion B S hS (c.ι.app 0)
      (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1)

/-- **`(X₀ ⊂ X') ⟶ (Y₀ ⊂ Y)` is flat, proper and of finite presentation**. -/
theorem isFlat_isProper_isFinitePresentation_towerRealizationClosedMap :
    Space.IsFlat B S hS (towerRealizationClosedMap ξ hsurj hsq e cR hcR c eLimit hc X').hom ∧
      Space.IsProper B S hS (towerRealizationClosedMap ξ hsurj hsq e cR hcR c eLimit hc X').hom ∧
      Space.IsFinitePresentation B S hS
        (towerRealizationClosedMap ξ hsurj hsq e cR hcR c eLimit hc X').hom :=
  Space.isFlat_isProper_isFinitePresentation_iso_comp_comp_iso B S hS (Space.EtaleSquareZeroExtension.Realization.closedSpaceIso X').symm
    (towerStructureMap ξ 0) (limitBaseRangeIso ξ hsurj hsq e cR hcR c eLimit hc)
    ⟨(ξ.obj 0).obj.property.2.1, (ξ.obj 0).obj.property.2.2, (ξ.obj 0).obj.property.1⟩

end AlgebraicGeometry.ProperFlatFibre

end
