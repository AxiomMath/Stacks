module

public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerSolutionConormal
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalMapOfSubspaceInclusions
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.RestrictedBaseTransport

/-!
# The conormal map of a realized solution of the tower problem is invertible

In the body of the proof of [Stacks Project, Tag 0D3X], a solution
`0 → f^*𝒞_{Y₀/Y} → 𝒪' → 𝒪_{X₀} → 0` of the tower problem
(`AlgebraicGeometry.ProperFlatFibre.towerProblem`) is realized by Stacks 05ZT as a first order
thickening `X₀ ⊂ X'` over `Y = Spec(lim Rₙ)`, and the source concludes, by the flatness clause of
Stacks 06BH, that `X'` is flat over `Y` with `X₀ = Y₀ ×_Y X'`. What that clause needs is that the
conormal map `f^*𝒞_{Y₀/Y} ⟶ 𝒞_{X₀/X'}` of `(X₀ ⊂ X') ⟶ (Y₀ ⊂ Y)` is an isomorphism: the ideal
of `X₀ ⊂ X'` is the ideal `f^*𝒞_{Y₀/Y}` of the solution, and the map is the one the solution
induces on the base ideal, which is universal.

The tower problem is posed over the small étale ringed topos of `Y₀ = Spec(R₀)`, while its base
thickening is the range `Y₀ ⊂ Y`. Its solutions are carried to solutions of the extension problem
`AlgebraicGeometry.Space.FlatThickeningDeformation.problem` of `X₀ ⟶ Y₀ ⊂ Y` by
`AlgebraicGeometry.Space.FlatThickeningDeformation.solutionOfRestricted`, with the same thickened
structure sheaf; a realization of the one is a realization of the other
(`AlgebraicGeometry.Space.FlatThickeningDeformation.realizationOfEq`), and for the latter the
invertibility of the conormal map is
`AlgebraicGeometry.Space.FlatThickeningDeformation.isIso_conormalMap_realized`.

## Main results

* `AlgebraicGeometry.ProperFlatFibre.isIso_towerRealizationConormalMap`: the conormal map of
  `(X₀ ⊂ X') ⟶ (Y₀ ⊂ Y)` is invertible, for every solution of the tower problem and every
  realization of it.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 06BH](https://stacks.math.columbia.edu/tag/06BH)
* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

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

/-- `Y₀ ⊂ Y = Spec(lim Rₙ)` is a first order thickening. -/
abbrev limitBaseThickening : Space.IsFirstOrderThickening B S hS (schemeSpace c.pt)
    (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc).1 :=
  Space.isFirstOrderThickening_range_yoneda_map B S hS (c.ι.app 0)
    (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc)

/-- `Y₀ ≅ (Y₀ ⊂ Y) ⊆ Y` is `Y₀ ⟶ Y`. -/
theorem limitBaseRangeIso_hom_comp_subspaceInclusion :
    (limitBaseRangeIso ξ hsurj hsq e cR hcR c eLimit hc).hom ≫
        Space.subspaceInclusion B S hS (schemeSpace c.pt)
          (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc) =
      schemeSpaceMap (c.ι.app 0) :=
  Space.rangeSpaceIso_hom_comp_subspaceInclusion B S hS (c.ι.app 0)
    (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1

/-- The tower problem is the restricted problem of `X₀ ⟶ Y₀` over `Y₀ ≅ (Y₀ ⊂ Y)`. -/
theorem towerProblem_eq_restrictedProblem :
    towerProblem ξ hsurj hsq e cR hcR c eLimit hc =
      Space.FlatThickeningDeformation.restrictedProblem
        (limitBaseThickening ξ hsurj hsq e cR hcR c eLimit hc)
        (limitBaseRangeIso ξ hsurj hsq e cR hcR c eLimit hc) (towerStructureMap ξ 0) :=
  rfl

variable {ξ hsurj hsq e cR hcR c eLimit hc}
  (P' : (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).CompatibleFirstOrderThickening)

/-- **A solution of the tower problem, as a solution of the problem of `X₀ ⟶ (Y₀ ⊂ Y)`.** -/
abbrev towerBaseSolution :=
  Space.FlatThickeningDeformation.solutionOfRestricted
    (limitBaseThickening ξ hsurj hsq e cR hcR c eLimit hc)
    (limitBaseRangeIso ξ hsurj hsq e cR hcR c eLimit hc) (towerStructureMap ξ 0) P'

/-- `X₀ ⟶ Y` is the composite `X₀ ⟶ Y₀ ≅ (Y₀ ⊂ Y) ⊆ Y`. -/
theorem towerLimitStructureMap_eq :
    towerLimitStructureMap ξ c 0 =
      (towerStructureMap ξ 0 ≫ (limitBaseRangeIso ξ hsurj hsq e cR hcR c eLimit hc).hom) ≫
        Space.subspaceInclusion B S hS (schemeSpace c.pt)
          (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc) :=
  (congrArg (towerStructureMap ξ 0 ≫ ·)
    (limitBaseRangeIso_hom_comp_subspaceInclusion ξ hsurj hsq e cR hcR c eLimit hc)).symm.trans
    (Category.assoc _ _ _).symm

/-- The base map of the square-zero extension of a solution of the tower problem is, up to the
identification of `X₀ ⟶ Y` in `towerLimitStructureMap_eq`, the base map of the square-zero
extension of the corresponding solution `towerBaseSolution` of the problem of `X₀ ⟶ (Y₀ ⊂ Y)`.
-/
theorem towerSolution_toBase_eq :
    (towerSolutionSquareZeroExtension ξ hsurj hsq e cR hcR c eLimit hc P').toBase =
      eqToHom (congrArg (Space.inverseImageStructureCommRingSheaf B S hS)
          (towerLimitStructureMap_eq (hsurj := hsurj) (hsq := hsq) (e := e) (hcR := hcR)
            (eLimit := eLimit) (hc := hc))) ≫
        (Space.FlatThickeningDeformation.solutionSquareZeroExtension
          (towerBaseSolution P')).toBase := by
  have hco := Space.FlatThickeningDeformation.restrictedBase_coherence
    (limitBaseThickening ξ hsurj hsq e cR hcR c eLimit hc)
    (limitBaseRangeIso ξ hsurj hsq e cR hcR c eLimit hc) (towerStructureMap ξ 0)
    (schemeSpaceMap (c.ι.app 0))
    (limitBaseRangeIso_hom_comp_subspaceInclusion ξ hsurj hsq e cR hcR c eLimit hc)
  refine (congrArg (· ≫ _) hco).trans ?_
  rfl

/-- **A realization of a solution of the tower problem, as a realization of the corresponding
solution of the problem of `X₀ ⟶ (Y₀ ⊂ Y)`.** -/
abbrev towerBaseRealization
    (X' : Space.EtaleSquareZeroExtension.Realization
      (towerSolutionSquareZeroExtension ξ hsurj hsq e cR hcR c eLimit hc P')) :
    Space.SquareZeroExtension.Realization B S hS
      (Space.FlatThickeningDeformation.solutionSquareZeroExtension (towerBaseSolution P')) :=
  Space.FlatThickeningDeformation.realizationOfEq towerLimitStructureMap_eq
    (E₁ := towerSolutionSquareZeroExtension ξ hsurj hsq e cR hcR c eLimit hc P') rfl
    (Category.id_comp _).symm ((Category.comp_id _).trans (towerSolution_toBase_eq P')) X'

/-- **The conormal map of a realized solution of the tower problem is invertible**: the map
`f^*𝒞_{Y₀/Y} ⟶ 𝒞_{X₀/X'}` of Stacks 04CP for `(X₀ ⊂ X') ⟶ (Y₀ ⊂ Y)`. -/
theorem isIso_towerRealizationConormalMap
    (X' : Space.EtaleSquareZeroExtension.Realization
      (towerSolutionSquareZeroExtension ξ hsurj hsq e cR hcR c eLimit hc P')) :
    IsIso (Space.conormalMapOfImmersions B S hS
      (Space.subspaceInclusion B S hS X'.ambient X'.closedSubspace)
      (Space.subspaceInclusion B S hS (schemeSpace c.pt)
        (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc))
      (towerRealizationClosedMap ξ hsurj hsq e cR hcR c eLimit hc X') X'.toBase
      (Space.isImmersion_subspaceInclusion B S hS _ _)
      (Space.isImmersion_subspaceInclusion B S hS _ _)
      (towerRealization_sq ξ hsurj hsq e cR hcR c eLimit hc X')) := by
  have h := Space.FlatThickeningDeformation.isIso_conormalMap_realized
    (towerBaseRealization P' X')
  have h' : IsIso (Space.conormalMap B S hS X'.closedSubspace
      (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc) X'.toBase
      (towerRealizationClosedMap ξ hsurj hsq e cR hcR c eLimit hc X')
      (towerRealization_sq ξ hsurj hsq e cR hcR c eLimit hc X')) := h
  exact Space.isIso_conormalMapOfImmersions_of_isIso_map_idealSheafMap _ _ _ _ _
    (Space.isIso_modulePullback_map_idealSheafMap_of_isIso_conormalMap B S hS _ _ _ _ _ h')

end AlgebraicGeometry.ProperFlatFibre

end
