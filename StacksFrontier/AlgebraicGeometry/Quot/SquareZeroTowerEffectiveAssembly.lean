module

public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerKernelChange
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitComparisonData
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerRealizationCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionRealizationOfCharts

/-!
# Effectivity of a square-zero tower of proper flat families, assembled

In the body of the proof of [Stacks Project, Tag 0D3X], a system `ξ` of finitely presented, flat
and proper algebraic spaces over a tower `Spec(Rₙ)` with surjective square-zero transitions is
shown effective in four steps: the limit comparison of the tower problem (Stacks 0D3F), a solution
`𝒪'` of the tower problem with a morphism to the limit of the `i⁻¹𝒪_{Xₙ}`
(`AlgebraicGeometry.ProperFlatFibre.exists_towerProblem_kernelChangeHom_of_limitComparison`), its
realization `X₀ ⊂ X'` over `Y = Spec(lim Rₙ)` (Stacks 05ZT,
`AlgebraicGeometry.ProperFlatFibre.nonempty_towerSolutionRealization`), and the invertibility of
the conormal map of `(X₀ ⊂ X') ⟶ (Y₀ ⊂ Y)`, after which
`AlgebraicGeometry.ProperFlatFibre.isEffectiveSystem_of_isIso_towerRealizationConormalMap`
concludes. This file chains the four steps for one system.

## Main results

* `AlgebraicGeometry.ProperFlatFibre.isEffectiveSystem_of_limitComparison_sections`: the system is
  effective, given the perfectness of `RΓ(X₀, -)` on perfect objects (Stacks 0CTM), the value of
  the limit comparison on the sections `1 ⊗ m`, and the invertibility of the conormal map of
  every realized solution. None of these three is registered here: this is the assembly of the
  body of the proof, whose three inputs are proved separately.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

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

section

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasColimitsOfShape_discrete_derivedCategory
attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction in
/-- **The square-zero tower is effective, from the three inputs of the body of the proof of
Stacks 0D3X**: the perfectness of `RΓ(X₀, -)` on perfect objects (`hpush`, Stacks 0CTM), the value
of `φ = towerLimitKernelMap` on the sections `1 ⊗ m` of `𝒪_{X₀} ⊗ lim Iₙ` (`H`, the limit
comparison of Stacks 0D3F for `Iₙ = towerBaseKernelSystem`), and the invertibility of the conormal
map of `(X₀ ⊂ X') ⟶ (Y₀ ⊂ Y)` for every realization `X'` of a solution of the tower problem
(`hconormal`). The solution with a morphism to `lim i⁻¹𝒪_{Xₙ}` comes from the limit comparison, it
is realized over `Y = Spec(lim Rₙ)` by Stacks 05ZT, and the invertible conormal map makes the
realization effective. -/
theorem isEffectiveSystem_of_limitComparison_sections (hZ : B.Contains (⊤_ Scheme.{u}))
    [HasProduct fun n : ℕ => (Space.baseRingTensorModule B S hS (towerSpace ξ 0)
      (Space.baseRingHomOfMap (towerStructureMap ξ 0))).obj
        ((towerBaseKernelSystem ξ hsurj hsq e).obj ⟨n⟩)]
    [HasLimit (towerBaseKernelSystem ξ hsurj hsq e ⋙ Space.baseRingTensorModule B S hS
      (towerSpace ξ 0) (Space.baseRingHomOfMap (towerStructureMap ξ 0)))]
    (hpush : ∀ K,
      (Space.spacesEtaleModelRingedTopos B S hS (towerSpace ξ 0)).toRingedSite.IsPerfect K →
      (pointRingedTopos
          (CommRingCat.of (Space.baseRing B S hS (towerBase ξ 0)))).toRingedSite.IsPerfect
        ((derivedPushforward (Space.spacesEtaleModelToBaseRing B S hS (towerSpace ξ 0)
          (Space.baseRingHomOfMap (towerStructureMap ξ 0)))).obj K))
    (H : ∀ (n : ℕ) (m : ↑(limit (towerBaseKernelSystem ξ hsurj hsq e))),
      Space.baseRingTensorSection B S hS (towerSpace ξ 0)
          (Space.baseRingHomOfMap (towerStructureMap ξ 0)) _ m ≫
        (towerProblemKernelIso ξ hsurj hsq e cR hcR c eLimit hc).inv ≫
        towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc ≫
        limit.π (towerIdealSystem ξ hsurj hsq e he) (op n) =
      Space.baseRingTensorSection B S hS (towerSpace ξ 0)
          (Space.baseRingHomOfMap (towerStructureMap ξ 0)) _
          (limit.π (towerBaseKernelSystem ξ hsurj hsq e) (op n) m) ≫
        (towerIdealSystemObjIso ξ hsurj hsq e he n).hom)
    (hconormal : ∀
      (P' : (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).CompatibleFirstOrderThickening)
      (Rz : Space.EtaleSquareZeroExtension.Realization
        (towerSolutionSquareZeroExtension ξ hsurj hsq e cR hcR c eLimit hc P')),
      IsIso (Space.conormalMapOfImmersions B S hS
        (Space.subspaceInclusion B S hS Rz.ambient Rz.closedSubspace)
        (Space.subspaceInclusion B S hS (schemeSpace c.pt)
          (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc))
        (towerRealizationClosedMap ξ hsurj hsq e cR hcR c eLimit hc Rz) Rz.toBase
        (Space.isImmersion_subspaceInclusion B S hS _ _)
        (Space.isImmersion_subspaceInclusion B S hS _ _)
        (towerRealization_sq ξ hsurj hsq e cR hcR c eLimit hc Rz))) :
    Deformation.Artin.IsEffectiveSystem (cartesianProperFlatProjection B S hS) ξ c := by
  obtain ⟨α, β, hφ⟩ := towerProblem_limitComparison_data ξ @hsurj @hsq e @he cR hcR c eLimit hc H
  obtain ⟨P', ⟨κ⟩⟩ := exists_towerProblem_kernelChangeHom_of_limitComparison ξ @hsurj @hsq e @he
    cR hcR c eLimit hc hZ (towerBaseKernelSystem ξ hsurj hsq e)
    (surjective_towerBaseKernelSystem_map ξ @hsurj @hsq e) hpush α β hφ
  obtain ⟨Rz⟩ := nonempty_towerSolutionRealization ξ @hsurj @hsq e cR hcR c eLimit hc P'
  exact isEffectiveSystem_of_isIso_towerRealizationConormalMap ξ @hsurj @hsq e @he cR hcR c eLimit
    hc Rz κ (hconormal P' Rz)

end

end AlgebraicGeometry.ProperFlatFibre
