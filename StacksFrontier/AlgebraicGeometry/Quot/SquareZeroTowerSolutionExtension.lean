module

public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerKernelChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleRestrictionModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AlgebraExtensionAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleSquareZeroExtension
public import StacksFrontier.Deformation.ToposThickening.KernelPushoutAlgebraExtension

/-!
# A solution of the tower problem as 05ZT data over `Spec(lim Rₙ)`

In the situation of `AlgebraicGeometry.ProperFlatFibre.towerProblem`, a solution `𝒪'` of the
problem is an extension `0 → f^*𝒞_{Y₀/Y} → 𝒪' → 𝒪_{X₀} → 0` of `f⁻¹(i⁻¹𝒪_Y)`-algebras, where
`f : X₀ ⟶ Y₀` is the structure morphism and `i : Y₀ ⟶ Y = Spec(lim Rₙ)`. Through the composition
law `(f ≫ i)⁻¹𝒪_Y ≅ f⁻¹i⁻¹𝒪_Y` of Stacks 03G8 it is an extension of `(f ≫ i)⁻¹𝒪_Y`-algebras, with
quasi-coherent kernel: exactly the data of Stacks 05ZT for the morphism `f ≫ i : X₀ ⟶ Y`. In the
proof of [Stacks Project, Tag 0D3X] this is the step "the sheaf `𝒪'` determines a first order
thickening `X₁ ⊂ X` over `Spec(R₁) ⊂ Spec(lim Rₙ)` by Lemma 05ZT".

## Main definitions

* `AlgebraicGeometry.ProperFlatFibre.towerSolutionBaseIso`: `(f ≫ i)⁻¹𝒪_Y ≅ f⁻¹` of the thickened
  base of the problem.
* `AlgebraicGeometry.ProperFlatFibre.towerSolutionAlgebraExtension`: a solution as an extension of
  `(f ≫ i)⁻¹𝒪_Y`-algebras.
* `AlgebraicGeometry.ProperFlatFibre.towerSolutionSquareZeroExtension`: a solution as 05ZT data
  for `f ≫ i`.

## Main results

* `AlgebraicGeometry.ProperFlatFibre.towerSolutionBaseIso_hom_comp`: the identification is
  compatible with the structure maps.
* `AlgebraicGeometry.ProperFlatFibre.isQuasicoherentOnSite_towerProblem_G`: the ideal
  `f^*𝒞_{Y₀/Y}` of the problem is quasi-coherent.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
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

/-- **`(f ≫ i)⁻¹𝒪_Y ≅ f⁻¹(i⁻¹𝒪_Y)`**, the second factor being the thickened base of the tower
problem: the composition law of Stacks 03G8 followed by `f⁻¹` of
`AlgebraicGeometry.ProperFlatFibre.towerProblemBaseIso`. -/
def towerSolutionBaseIso :
    (Space.smallEtaleInverseImageRing B S hS (towerLimitStructureMap ξ c 0)).obj
        (Space.smallEtaleRingedTopos B S hS (schemeSpace c.pt)).O ≅
      (Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
        (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).f.toToposHom).obj
        (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).baseExtension :=
  ((Space.smallEtaleRingedToposHom_compInverseImageRingIso B S hS (towerStructureMap ξ 0)
      (schemeSpaceMap (c.ι.app 0))).app
      (Space.smallEtaleRingedTopos B S hS (schemeSpace c.pt)).O).symm ≪≫
    (Space.smallEtaleInverseImageRing B S hS (towerStructureMap ξ 0)).mapIso
      (towerProblemBaseIso ξ hsurj hsq e cR hcR c eLimit hc).symm

/-- **The identification of the bases is compatible with the structure maps**: followed by the
reduction of the thickened base and the structure map of `f`, it is the structure map of
`f ≫ i`. -/
theorem towerSolutionBaseIso_hom_comp :
    (towerSolutionBaseIso ξ hsurj hsq e cR hcR c eLimit hc).hom ≫
        (Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
          (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).f.toToposHom).map
          (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).baseReduction ≫
        (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).f.fSharpInverseImage =
      Space.structureSharpInverseImage B S hS (towerLimitStructureMap ξ c 0) := by
  have hred : (towerProblemBaseIso ξ hsurj hsq e cR hcR c eLimit hc).inv ≫
      (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).baseReduction =
        (Space.smallEtaleRingedToposHom B S hS (schemeSpaceMap (c.ι.app 0))).fSharpInverseImage :=
    (Iso.inv_comp_eq _).2
      (towerProblemBaseIso_hom_comp_fSharpInverseImage ξ hsurj hsq e cR hcR c eLimit hc).symm
  have h03G8 := Space.smallEtaleRingedToposHom_compInverseImageRingIso_fSharpInverseImage B S hS
    (towerStructureMap ξ 0) (schemeSpaceMap (c.ι.app 0))
  change ((Space.smallEtaleRingedToposHom_compInverseImageRingIso B S hS (towerStructureMap ξ 0)
      (schemeSpaceMap (c.ι.app 0))).inv.app _ ≫
      (Space.smallEtaleInverseImageRing B S hS (towerStructureMap ξ 0)).map
        (towerProblemBaseIso ξ hsurj hsq e cR hcR c eLimit hc).inv) ≫
      (Space.smallEtaleInverseImageRing B S hS (towerStructureMap ξ 0)).map
        (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).baseReduction ≫
      (Space.smallEtaleRingedToposHom B S hS (towerStructureMap ξ 0)).fSharpInverseImage = _
  rw [Category.assoc, ← Functor.map_comp_assoc, hred, ← h03G8]
  exact Iso.inv_hom_id_app_assoc _ _ _

/-- **The ideal `f^*𝒞_{Y₀/Y}` of the tower problem is quasi-coherent**: the conormal module of a
closed subspace is quasi-coherent, and so is its pullback. -/
theorem isQuasicoherentOnSite_towerProblem_G :
    (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).G.IsQuasicoherentOnSite :=
  Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (towerStructureMap ξ 0) _
    (SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((Space.modulePullbackIsoEtaleRestrictionModule B S hS _
        (Space.isEtale_hom_of_iso B S hS _)).app _)
      (Space.isQuasicoherentOnSite_modulePullback_of_isEtale B S hS _
        (Space.isEtale_hom_of_iso B S hS _) _
        (Space.isQuasicoherentOnSite_conormalModule B S hS _ _)))

/-- **A solution of the tower problem as an extension of `(f ≫ i)⁻¹𝒪_Y`-algebras** of `𝒪_{X₀}`
by `f^*𝒞_{Y₀/Y}`. -/
abbrev towerSolutionAlgebraExtension
    (P' : (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).CompatibleFirstOrderThickening) :
    Deformation.AlgebraExtension (J := Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
      (Space.structureSharpInverseImage B S hS (towerLimitStructureMap ξ c 0))
      (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).G :=
  RingedToposExtensionProblem.toAlgebraExtension.{u, u + 1, u, u, u + 1, u}
    (towerProblem ξ hsurj hsq e cR hcR c eLimit hc)
    (towerSolutionBaseIso ξ hsurj hsq e cR hcR c eLimit hc)
    (towerSolutionBaseIso_hom_comp ξ hsurj hsq e cR hcR c eLimit hc) P'

/-- **A solution of the tower problem as the data of Stacks 05ZT** for `f ≫ i : X₀ ⟶ Y`. -/
def towerSolutionSquareZeroExtension
    (P' : (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).CompatibleFirstOrderThickening) :
    Space.EtaleSquareZeroExtension (towerLimitStructureMap ξ c 0) :=
  Space.SquareZeroExtension.ofAlgebraExtension _
    (towerSolutionAlgebraExtension ξ hsurj hsq e cR hcR c eLimit hc P')
    (isQuasicoherentOnSite_towerProblem_G ξ hsurj hsq e cR hcR c eLimit hc)

end AlgebraicGeometry.ProperFlatFibre

end
