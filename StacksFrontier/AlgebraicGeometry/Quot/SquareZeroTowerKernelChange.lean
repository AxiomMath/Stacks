module

public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitIdealMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickenedBasePushoutSolution
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleLimitComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CoheratorLimitComparison

/-!
# A solution of the tower problem mapping to `𝒜 = lim 𝒪_{Xₙ}`

In the situation of `AlgebraicGeometry.ProperFlatFibre.towerProblem`, the body of the proof of
[Stacks Project, Tag 0D3X] obtains the structure sheaf `𝒪'` of the formal object's limit from the
extension `𝒜 = lim 𝒪_{Xₙ}` by [Stacks Project, Tag 0D3Q]: once `DQ_{X₀}` inverts
`φ : f^*𝒞_{Y₀/Y} ⟶ lim 𝒪_{X₀} ⊗ Iₙ`, the solution `𝒜` of the problem changed along `φ` receives
a solution `𝒪'` of the problem itself.

## Main results

* `AlgebraicGeometry.ProperFlatFibre.isClosedImmersion_limitBase`: `Y₀ ⟶ Spec(lim Rₙ)` is a closed
  immersion of algebraic spaces.
* `AlgebraicGeometry.ProperFlatFibre.exists_towerProblem_kernelChangeHom`.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 0D3Q](https://stacks.math.columbia.edu/tag/0D3Q)
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
  (he : ∀ {i j : ℕ} (f : i ⟶ j),
    (BigFppfOver.toScheme B S hS).map ((ξ ⋙ cartesianProperFlatProjection B S hS).map f) ≫
      (e j).hom = (e i).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (R.map f.op).hom.toRingHom).op)
  (cR : Cone R) (hcR : IsLimit cR) (c : Cocone (ξ ⋙ cartesianProperFlatProjection B S hS))
  (eLimit : (BigFppfOver.toScheme B S hS).obj c.pt ≅ Spec (.of cR.pt))
  (hc : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).map (c.ι.app n) ≫ eLimit.hom =
    (e n).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (cR.π.app (.op n)).hom.toRingHom).op)

include hsurj hsq hcR hc in
/-- **`Y₀ ⟶ Spec(lim Rₙ)` is a closed immersion of algebraic spaces.** -/
theorem isClosedImmersion_limitBase :
    Space.IsClosedImmersion B S hS (schemeSpaceMap (c.ι.app 0)).hom :=
  (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
    (@AlgebraicGeometry.IsClosedImmersion.{u}) _).2
    (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1

include e in
/-- `X₀` is quasi-compact and quasi-separated: it is of finite presentation over the affine
`Y₀`. -/
theorem qcqs_towerSpace_zero (hZ : B.Contains (⊤_ Scheme.{u})) :
    Space.IsQuasiCompactSpace B S hS (towerSpace ξ 0).1 ∧
      Space.IsAbsolutelyQuasiSeparated B S hS hZ (towerSpace ξ 0).1 :=
  Space.qcqs_of_isFinitePresentation_schemeSpace hZ (towerStructureMap ξ 0)
    (isAffine_towerBase ξ e 0) (ξ.obj 0).obj.property.1

section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

/-- **A solution of the tower problem mapping to `𝒜 = lim 𝒪_{Xₙ}`** (the step of the body of
[Stacks Project, Tag 0D3X] that invokes Stacks 0D3Q). If `DQ_{X₀}` inverts
`φ : f^*𝒞_{Y₀/Y} ⟶ lim 𝒪_{X₀} ⊗ Iₙ` (`towerLimitKernelMap`), the problem `towerProblem` has a
solution `𝒪'` with a morphism to `𝒜` over `φ`. -/
theorem exists_towerProblem_kernelChangeHom (hZ : B.Contains (⊤_ Scheme.{u}))
    (hDQ :
      letI := Space.quasicoherentDerivedInclusion_isLeftAdjoint_of_qcqs B S hS hZ
        (towerSpace ξ 0).1 (towerSpace ξ 0).2
        (qcqs_towerSpace_zero ξ e hZ).1
        (qcqs_towerSpace_zero ξ e hZ).2
      IsIso ((Space.qcohDerivedProp B S hS (towerSpace ξ 0)).ι.rightAdjoint.map
        ((DerivedCategory.singleFunctor (Space.Modules.{u, u} B S hS (towerSpace ξ 0).1
          (towerSpace ξ 0).2) 0).map (towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc)))) :
    ∃ P' : (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).CompatibleFirstOrderThickening,
      Nonempty (RingedToposExtensionProblem.KernelChangeHom.{u, u + 1, u, u, u + 1, u}
        (S := towerProblem ξ hsurj hsq e cR hcR c eLimit hc)
        (towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc) P'
        (towerLimitSolutionOfKernelMap ξ hsurj hsq e he cR hcR c eLimit hc)) :=
  Space.exists_kernelChangeHom_of_isIso_coherator_map_of_qcqs B S hS hZ
    (qcqs_towerSpace_zero ξ e hZ).1
    (qcqs_towerSpace_zero ξ e hZ).2
    (towerStructureMap ξ 0) (schemeSpaceMap (c.ι.app 0))
    (isClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc)
    (towerProblem ξ hsurj hsq e cR hcR c eLimit hc)
    (towerProblem_f ξ hsurj hsq e cR hcR c eLimit hc)
    (towerProblemBaseIso ξ hsurj hsq e cR hcR c eLimit hc)
    (towerProblemBaseIso_hom_comp_fSharpInverseImage ξ hsurj hsq e cR hcR c eLimit hc)
    (towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc) hDQ
    (towerLimitSolutionOfKernelMap ξ hsurj hsq e he cR hcR c eLimit hc)

end

section

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasColimitsOfShape_discrete_derivedCategory
attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction in
/-- **The solution of the tower problem, from an identification of `φ` with the canonical map of
Stacks 0D3F.** Let `(M_n)` be an inverse system of `Γ(Y₀)`-modules with surjective transitions,
and suppose `RΓ(X₀, -)` carries perfect objects to perfect objects (Stacks 0CTM). If
`φ : f^*𝒞_{Y₀/Y} ⟶ lim 𝒪_{X₀} ⊗ Iₙ` is, up to isomorphisms, the canonical map
`𝒪_{X₀} ⊗ lim M_n ⟶ lim 𝒪_{X₀} ⊗ M_n`, then the tower problem has a solution `𝒪'` with a
morphism to `𝒜` over `φ`. -/
theorem exists_towerProblem_kernelChangeHom_of_limitComparison (hZ : B.Contains (⊤_ Scheme.{u}))
    (Msys : ℕᵒᵖ ⥤ ModuleCat.{u} (Space.baseRing B S hS (towerBase ξ 0)))
    (hMsurj : ∀ n : ℕ, Function.Surjective (Msys.map (homOfLE (Nat.le_succ n)).op))
    [HasProduct fun n : ℕ => (Space.baseRingTensorModule B S hS (towerSpace ξ 0)
      (Space.baseRingHomOfMap (towerStructureMap ξ 0))).obj (Msys.obj ⟨n⟩)]
    [HasLimit (Msys ⋙ Space.baseRingTensorModule B S hS (towerSpace ξ 0)
      (Space.baseRingHomOfMap (towerStructureMap ξ 0)))]
    (hpush : ∀ K,
      (Space.spacesEtaleModelRingedTopos B S hS (towerSpace ξ 0)).toRingedSite.IsPerfect K →
        (pointRingedTopos
          (CommRingCat.of (Space.baseRing B S hS (towerBase ξ 0)))).toRingedSite.IsPerfect
          ((derivedPushforward (Space.spacesEtaleModelToBaseRing B S hS (towerSpace ξ 0)
            (Space.baseRingHomOfMap (towerStructureMap ξ 0)))).obj K))
    (α : (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).G ≅
      (Space.baseRingTensorModule B S hS (towerSpace ξ 0)
        (Space.baseRingHomOfMap (towerStructureMap ξ 0))).obj (limit Msys))
    (β : limit (Msys ⋙ Space.baseRingTensorModule B S hS (towerSpace ξ 0)
        (Space.baseRingHomOfMap (towerStructureMap ξ 0))) ≅
        ((towerProblem ξ hsurj hsq e cR hcR c eLimit hc).changeKernel
          (towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc)).G)
    (hφ : towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc = α.hom ≫
      limit.post Msys (Space.baseRingTensorModule B S hS (towerSpace ξ 0)
        (Space.baseRingHomOfMap (towerStructureMap ξ 0))) ≫ β.hom) :
    ∃ P' : (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).CompatibleFirstOrderThickening,
      Nonempty (RingedToposExtensionProblem.KernelChangeHom.{u, u + 1, u, u, u + 1, u}
        (S := towerProblem ξ hsurj hsq e cR hcR c eLimit hc)
        (towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc) P'
        (towerLimitSolutionOfKernelMap ξ hsurj hsq e he cR hcR c eLimit hc)) :=
  exists_towerProblem_kernelChangeHom ξ hsurj hsq e he cR hcR c eLimit hc hZ
    (Space.isIso_coherator_map_single_of_eq_limitComparison hZ
      (qcqs_towerSpace_zero ξ e hZ).1
      (qcqs_towerSpace_zero ξ e hZ).2
      (towerStructureMap ξ 0) (isFlat_towerStructureMap ξ 0) (ξ.obj 0).obj.property.1
      (isAffine_towerBase ξ e 0) Msys hMsurj hpush _ α β hφ)

end

end AlgebraicGeometry.ProperFlatFibre

end
