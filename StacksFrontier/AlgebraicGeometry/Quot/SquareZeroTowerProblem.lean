module

public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.DefiningIdealBaseRingTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RestrictedFirstOrderExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningUnramified
public import StacksFrontier.Deformation.ToposThickening.AlgebraExtensionBaseProblem

/-!
# The extension problem of a square-zero tower over the limit of the bases

In the situation of `AlgebraicGeometry.ProperFlatFibre.towerSpace` — a system `Xₙ ⟶ Yₙ` of
finitely presented, flat and proper algebraic spaces over the spectra of a tower `(Rₙ)` of rings
with surjective transition maps of square-zero kernel — let `Y₀ ⟶ Y = Spec(lim Rₙ)` be the
canonical morphism to the limit of the bases. The body of the proof of
[Stacks Project, Tag 0D3X] poses a square-zero extension problem over `X₀ ⟶ Y₀ ⊂ Y`. This file
sets it up:

* `Y₀ ⟶ Y` is a closed immersion with square-zero ideal (its ring map `lim Rₙ → R₀` is
  surjective with kernel `lim Iₙ` of square zero);
* the base thickening is `0 → 𝒞_{Y₀/Y} → i⁻¹𝒪_Y → 𝒪_{Y₀} → 0` on `Y₀`, `i : Y₀ ⟶ Y`;
* the problem `towerProblem` over `f : X₀ ⟶ Y₀` has thickened base `i⁻¹𝒪_Y` with reduction
  `i^♯`, inverse image of the base ideal `f⁻¹𝒞_{Y₀/Y}`, prescribed module `f^*𝒞_{Y₀/Y}`, and the
  canonical map `f⁻¹𝒞_{Y₀/Y} ⟶ f^*𝒞_{Y₀/Y}`.

## Main definitions

* `AlgebraicGeometry.ProperFlatFibre.limitBaseExtension`: the base thickening on `Y₀`.
* `AlgebraicGeometry.ProperFlatFibre.towerProblem`: the extension problem.
* `AlgebraicGeometry.ProperFlatFibre.towerProblemBaseIso`: its thickened base is `i⁻¹𝒪_Y`, with
  reduction `i^♯` (`towerProblemBaseIso_hom_comp_fSharpInverseImage`), the form in which
  [Stacks Project, Tag 0D3Q] takes it.

## Main results

* `AlgebraicGeometry.ProperFlatFibre.isSquareZeroClosedImmersion_limitBase`: `Y₀ ⟶ Y` is a closed
  immersion with square-zero ideal.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 0D3Q](https://stacks.math.columbia.edu/tag/0D3Q)
* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Deformation.ToposThickening

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

include hsurj hsq hcR hc in
/-- **`Y₀ ⟶ Spec(lim Rₙ)` is a closed immersion with square-zero ideal**: it is identified with
`Spec(lim Rₙ → R₀)`, a surjection with kernel `lim Iₙ` of square zero. -/
theorem isSquareZeroClosedImmersion_limitBase :
    Space.IsSquareZeroClosedImmersion B S hS (c.ι.app 0) :=
  isFirstOrderThickening_of_specIso (CommRingCat.ofHom (CommAlgCat.towerLimitProjection cR))
    (CommAlgCat.surjective_towerLimit_π_zero hsurj cR hcR)
    (CommAlgCat.ker_towerLimit_π_zero_sq_eq_bot hsq cR hcR) _ (e 0) eLimit (hc 0)

/-- The closed subspace `Y₀ ⊆ Spec(lim Rₙ)`. -/
abbrev limitBaseSubspace : Space.ClosedSubspaces B S hS (schemeSpace c.pt).1 :=
  Space.rangeSubspace B S hS (c.ι.app 0)
    (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1

/-- `Y₀ ≅ (Y₀ ⊆ Spec(lim Rₙ))`. -/
abbrev limitBaseRangeIso :
    schemeSpace (towerBase ξ 0) ≅
      (⟨(limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc).1.toFunctor,
        (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc).2.1⟩ : AlgebraicSpaces B S hS) :=
  Space.rangeSpaceIso B S hS (c.ι.app 0)
    (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1

/-- The conormal module `𝒞_{Y₀/Y}` of `Y₀ ⊆ Y = Spec(lim Rₙ)`, on `Y₀`. -/
abbrev limitBaseConormal :=
  Space.restrictedConormalModule B S hS (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc)
    (limitBaseRangeIso ξ hsurj hsq e cR hcR c eLimit hc)

/-- **The base thickening `0 → 𝒞_{Y₀/Y} → i⁻¹𝒪_Y → 𝒪_{Y₀} → 0`** on `Y₀`, `i : Y₀ ⟶ Y`. -/
abbrev limitBaseExtension :=
  Space.restrictedFirstOrderExtension B S hS (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc)
    (Space.isFirstOrderThickening_range_yoneda_map B S hS (c.ι.app 0)
      (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc))
    (limitBaseRangeIso ξ hsurj hsq e cR hcR c eLimit hc) (𝟙 _)

/-- **The extension problem of the body of [Stacks Project, Tag 0D3X]** over
`f : X₀ ⟶ Y₀ ⊂ Spec(lim Rₙ)`: the lower row is the inverse image of the base thickening, the
prescribed module is `f^*𝒞_{Y₀/Y}`, and the map on ideals is the canonical
`f⁻¹𝒞_{Y₀/Y} ⟶ f^*𝒞_{Y₀/Y}`. -/
def towerProblem :
    RingedToposExtensionProblem (Space.smallEtaleRingedTopos B S hS (towerSpace ξ 0))
      (Space.smallEtaleRingedTopos B S hS (schemeSpace (towerBase ξ 0))) :=
  RingedToposExtensionProblem.ofBaseAlgebraExtension
    (X := Space.smallEtaleRingedTopos B S hS (towerSpace ξ 0))
    (D := Space.smallEtaleRingedTopos B S hS (schemeSpace (towerBase ξ 0)))
    (Space.smallEtaleRingedToposHom B S hS (towerStructureMap ξ 0))
    (limitBaseExtension ξ hsurj hsq e cR hcR c eLimit hc)
    ((Space.modulePullback B S hS (towerStructureMap ξ 0)).obj
      (limitBaseConormal ξ hsurj hsq e cR hcR c eLimit hc))
    ((Space.extendScalarsFSharpAdjunction B S hS (towerStructureMap ξ 0)).unit.app _)

/-- The morphism of ringed topoi of `towerProblem` is the one induced by `X₀ ⟶ Y₀`. -/
theorem towerProblem_f :
    (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).f =
      Space.smallEtaleRingedToposHom B S hS (towerStructureMap ξ 0) :=
  rfl

/-- **The thickened base of the problem is `i⁻¹𝒪_Y`**, `i : Y₀ ⟶ Y = Spec(lim Rₙ)`. -/
def towerProblemBaseIso :
    (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).baseExtension ≅
      (Space.smallEtaleInverseImageRing B S hS (schemeSpaceMap (c.ι.app 0))).obj
        (Space.smallEtaleRingedTopos B S hS (schemeSpace c.pt)).O :=
  (Space.restrictedFirstOrderExtensionIso B S hS
      (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc) _
      (limitBaseRangeIso ξ hsurj hsq e cR hcR c eLimit hc) (𝟙 _)).symm ≪≫
    eqToIso (congrArg (Space.inverseImageStructureSheaf B S hS)
      (Space.rangeSpaceIso_hom_comp_subspaceInclusion B S hS (c.ι.app 0)
        (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1))

/-- The forward map of `towerProblemBaseIso` is the inverse of
`Space.restrictedFirstOrderExtensionIso` followed by the transport along
`Space.rangeSpaceIso_hom_comp_subspaceInclusion`. -/
theorem towerProblemBaseIso_hom :
    (towerProblemBaseIso ξ hsurj hsq e cR hcR c eLimit hc).hom =
      (Space.restrictedFirstOrderExtensionIso B S hS
        (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc)
        (Space.isFirstOrderThickening_range_yoneda_map B S hS (c.ι.app 0)
          (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc))
        (limitBaseRangeIso ξ hsurj hsq e cR hcR c eLimit hc) (𝟙 _)).inv ≫
      eqToHom (congrArg (Space.inverseImageStructureSheaf B S hS)
        (Space.rangeSpaceIso_hom_comp_subspaceInclusion B S hS (c.ι.app 0)
          (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1)) :=
  rfl

/-- The identification of the thickened base with `i⁻¹𝒪_Y` carries its reduction to `i^♯`. -/
theorem towerProblemBaseIso_hom_comp_fSharpInverseImage :
    (towerProblemBaseIso ξ hsurj hsq e cR hcR c eLimit hc).hom ≫
        (Space.smallEtaleRingedToposHom B S hS (schemeSpaceMap (c.ι.app 0))).fSharpInverseImage =
      (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).baseReduction := by
  have h := Space.restrictedFirstOrderExtensionIso_hom_comp_reduction B S hS
      (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc)
      (Space.isFirstOrderThickening_range_yoneda_map B S hS (c.ι.app 0)
        (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc))
      (limitBaseRangeIso ξ hsurj hsq e cR hcR c eLimit hc) (𝟙 _)
  refine (congrArg (· ≫ _) (towerProblemBaseIso_hom ξ hsurj hsq e cR hcR c eLimit hc)).trans ?_
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (Space.structureSharpInverseImage_eqToHom B S hS
      (Space.rangeSpaceIso_hom_comp_subspaceInclusion B S hS (c.ι.app 0)
        (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1))).trans ?_)
  exact (Iso.inv_comp_eq _).2 h.symm

end AlgebraicGeometry.ProperFlatFibre

end
