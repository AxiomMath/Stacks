module

public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerEffectiveAssembly
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitKernelMapFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictedPerfectDescentOverIntegers
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointPerfectOfProper
public import StacksFrontier.Deformation.Artin.Versality.OpennessTower

/-!
# Square-zero effectiveness of `Spaces'_{fp, flat, proper}` on the conormal input alone

The per-tower assembly of the body of the proof of Stacks 0D3X,
`AlgebraicGeometry.ProperFlatFibre.isEffectiveSystem_of_limitComparison_sections`, has three
inputs: the perfectness of `RΓ(X₀, -)` on perfect objects (Stacks 0CTM), the limit comparison of
Stacks 0D3F on the sections `1 ⊗ m`, and the invertibility of the conormal map of a realized
solution of the tower problem. The first two are discharged here, by
`AlgebraicGeometry.Space.isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_isProper`
(with the descent of perfect objects `AlgebraicGeometry.Space.perfectObjectsDescend_overIntegers`)
and by
`ProperFlatFibre.baseRingTensorSection_comp_towerProblemKernelIso_inv_comp_towerLimitKernelMap_π`.
The proofs are those of the corresponding declarations of
`StacksDraft.AlgebraicGeometry.Quot.ProperFlatSquareZeroEffectiveOfConormal`, stated here for
the base's hypothesis (4) of Stacks 0CXU,
`Deformation.Artin.IsSquareZeroEffective`.

## Main results

* `AlgebraicGeometry.ProperFlatFibre.isEffectiveSystem_of_towerConormal`: one square-zero tower
  is effective once the conormal map of every realized solution of its tower problem is
  invertible.
* `AlgebraicGeometry.isSquareZeroEffective_cartesianProperFlat_of_towerConormal`: the square-zero
  effectiveness of the stack, from that conormal input for every tower.

None of these is registered: the conormal input is a step of the proof of Stacks 0D3X.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin

universe w u

namespace AlgebraicGeometry.ProperFlatFibre

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (ξ : ℕ ⥤ CartesianProperFlatSpaces B S hS)
  {Λ : Type u} [CommRing Λ] {R : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ}
  (hsurj : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), Function.Surjective (R.map f).hom)
  (hsq : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), RingHom.ker (R.map f).hom.toRingHom ^ 2 = ⊥)
  (e : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).obj (towerBase ξ n) ≅
    Spec (.of (R.obj (.op n))))
  (he : ∀ {i j : ℕ} (f : i ⟶ j),
    (BigFppfOver.toScheme B S hS).map ((ξ ⋙ cartesianProperFlatProjection B S hS).map f) ≫
      (e j).hom = (e i).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (R.map f.op).hom.toRingHom).op)
  (cR : Cone R) (hcR : IsLimit cR) (c : Cocone (ξ ⋙ cartesianProperFlatProjection B S hS))
  (eLimit : (BigFppfOver.toScheme B S hS).obj c.pt ≅ Spec (.of cR.pt))
  (hc : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).map (c.ι.app n) ≫ eLimit.hom =
    (e n).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (cR.π.app (.op n)).hom.toRingHom).op)

include he in
/-- **The square-zero tower is effective, on the conormal input alone.** This is
`AlgebraicGeometry.ProperFlatFibre.isEffectiveSystem_of_limitComparison_sections` with its
perfectness input supplied by
`AlgebraicGeometry.Space.isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_isProper`
(the descent of perfect objects being `AlgebraicGeometry.Space.perfectObjectsDescend_overIntegers`)
and its limit comparison on the sections `1 ⊗ m` by
`ProperFlatFibre.baseRingTensorSection_comp_towerProblemKernelIso_inv_comp_towerLimitKernelMap_π`.
The remaining input `hconormal` is the invertibility of the conormal map of every realized
solution of the tower problem. -/
theorem isEffectiveSystem_of_towerConormal
    (hZ : B.Contains (⊤_ Scheme.{u}))
    [HasProduct fun n : ℕ => (Space.baseRingTensorModule B S hS (towerSpace ξ 0)
      (Space.baseRingHomOfMap (towerStructureMap ξ 0))).obj
        ((towerBaseKernelSystem ξ hsurj hsq e).obj ⟨n⟩)]
    [HasLimit (towerBaseKernelSystem ξ hsurj hsq e ⋙ Space.baseRingTensorModule B S hS
      (towerSpace ξ 0) (Space.baseRingHomOfMap (towerStructureMap ξ 0)))]
    (hconormal : ∀
      (P' : (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).CompatibleFirstOrderThickening)
      (Rz : Space.EtaleSquareZeroExtension.Realization
        (towerSolutionSquareZeroExtension ξ hsurj hsq e cR hcR c eLimit hc P')),
      IsIso (Space.conormalMapOfImmersions B S hS
        (Space.subspaceInclusion B S hS Rz.ambient
          (Space.EtaleSquareZeroExtension.Realization.closedSubspace Rz))
        (Space.subspaceInclusion B S hS (schemeSpace c.pt)
          (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc))
        (towerRealizationClosedMap ξ hsurj hsq e cR hcR c eLimit hc Rz) Rz.toBase
        (Space.isImmersion_subspaceInclusion B S hS _ _)
        (Space.isImmersion_subspaceInclusion B S hS _ _)
        (towerRealization_sq ξ hsurj hsq e cR hcR c eLimit hc Rz))) :
    Deformation.Artin.IsEffectiveSystem (cartesianProperFlatProjection B S hS) ξ c :=
  isEffectiveSystem_of_limitComparison_sections ξ @hsurj @hsq e @he cR hcR c eLimit hc hZ
    (fun K hK => Space.isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_isProper hZ
      (Space.perfectObjectsDescend_overIntegers hZ)
      (isAffine_towerBase ξ e 0) (towerStructureMap ξ 0) (ξ.obj 0).obj.property.2.2
      (ξ.obj 0).obj.property.1 (isFlat_towerStructureMap ξ 0) K hK)
    (baseRingTensorSection_comp_towerProblemKernelIso_inv_comp_towerLimitKernelMap_π ξ @hsurj @hsq e
      @he
      cR hcR c eLimit hc) hconormal

end AlgebraicGeometry.ProperFlatFibre

namespace AlgebraicGeometry

open ProperFlatFibre

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **`Spaces'_{fp, flat, proper}` satisfies hypothesis (4) of Stacks 0CXU, on the conormal
input alone**: `AlgebraicGeometry.ProperFlatFibre.isEffectiveSystem_of_towerConormal` applied to
every system `ξ` over `Spec(Rₙ)`, `Rₙ → Rₘ` surjective with square-zero kernel. -/
theorem isSquareZeroEffective_cartesianProperFlat_of_towerConormal
    (hconormal : ∀ (Λ : Type u) [CommRing Λ] (R : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ)
      (hsurj : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), Function.Surjective (R.map f).hom)
      (hsq : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), RingHom.ker (R.map f).hom.toRingHom ^ 2 = ⊥)
      (ξ : ℕ ⥤ CartesianProperFlatSpaces B S hS)
      (e : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).obj (towerBase ξ n) ≅
        Spec (.of (R.obj (.op n))))
      (cR : Cone R) (hcR : IsLimit cR) (c : Cocone (ξ ⋙ cartesianProperFlatProjection B S hS))
      (eLimit : (BigFppfOver.toScheme B S hS).obj c.pt ≅ Spec (.of cR.pt))
      (hc : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).map (c.ι.app n) ≫ eLimit.hom =
        (e n).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (cR.π.app (.op n)).hom.toRingHom).op)
      (P' : (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).CompatibleFirstOrderThickening)
      (Rz : Space.EtaleSquareZeroExtension.Realization
        (towerSolutionSquareZeroExtension ξ hsurj hsq e cR hcR c eLimit hc P')),
      IsIso (Space.conormalMapOfImmersions B S hS
        (Space.subspaceInclusion B S hS Rz.ambient
          (Space.EtaleSquareZeroExtension.Realization.closedSubspace Rz))
        (Space.subspaceInclusion B S hS (schemeSpace c.pt)
          (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc))
        (towerRealizationClosedMap ξ hsurj hsq e cR hcR c eLimit hc Rz) Rz.toBase
        (Space.isImmersion_subspaceInclusion B S hS _ _)
        (Space.isImmersion_subspaceInclusion B S hS _ _)
        (towerRealization_sq ξ hsurj hsq e cR hcR c eLimit hc Rz))) :
    IsSquareZeroEffective B S hS (cartesianProperFlatProjection B S hS)
      (cartesianProperFlatProjection_isFiberedInGroupoids B S hS) := by
  intro Λ _ _ _ R cR hcR hsurj hsq ξ c e eLimit he hc _
  exact isEffectiveSystem_of_towerConormal ξ @hsurj @hsq e @he
    cR hcR c eLimit hc B.contains_terminal (hconormal Λ R @hsurj @hsq ξ e cR hcR c eLimit hc)

end AlgebraicGeometry

end
