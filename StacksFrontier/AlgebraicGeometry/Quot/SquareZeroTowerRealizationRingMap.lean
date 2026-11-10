module

public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitIdealMap
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerSolutionRealization
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionRealizationOfCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningHomChartComponents
public import StacksFrontier.Deformation.ToposThickening.KernelPushoutFaithful

/-!
# The maps `i⁻¹𝒪_{X'} ⟶ aₙ⁻¹𝒪_{Xₙ}` of a realized solution of the tower problem

In the proof of [Stacks Project, Tag 0D3X], a solution `𝒪'` of the tower problem maps to
`𝒜 = lim Aₙ`, `Aₙ = aₙ⁻¹𝒪_{Xₙ}` (Stacks 0D3Q), and is realized as `i⁻¹𝒪_{X'}` for a first order
thickening `i : X₀ ⟶ X'` over `Y = Spec(lim Rₙ)` (Stacks 05ZT). The composite
`φₙ : i⁻¹𝒪_{X'} ≅ 𝒪' ⟶ 𝒜 ⟶ Aₙ` is the map from which the morphism `Xₙ ⟶ X'` of the step
"`Xₙ ≅ X' ×_Y Yₙ`" is built. This file defines it and proves the two compatibilities that
construction needs: `φₙ` lies over the reductions to `𝒪_{X₀}`, and it is compatible with the maps
from `(X₀ ⟶ Y)⁻¹𝒪_Y`.

## Main definitions

* `AlgebraicGeometry.ProperFlatFibre.towerRealizationRingMap`: `φₙ`.

## Main results

* `AlgebraicGeometry.ProperFlatFibre.towerRealizationRingMap_comp_fSharpInverseImage`:
  `φₙ ≫ aₙ♯ = i♯`.
* `AlgebraicGeometry.ProperFlatFibre.inverseImageStructureSheafMap_comp_towerRealizationRingMap`:
  the compatibility of `φₙ` with the maps from `(X₀ ⟶ Y)⁻¹𝒪_Y`.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
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
  {P' : (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).CompatibleFirstOrderThickening}
  (κ : RingedToposExtensionProblem.KernelChangeHom.{u, u + 1, u, u, u + 1, u}
    (S := towerProblem ξ hsurj hsq e cR hcR c eLimit hc)
    (towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc) P'
    (towerLimitSolutionOfKernelMap ξ hsurj hsq e he cR hcR c eLimit hc))
  (Rz : Space.EtaleSquareZeroExtension.Realization
    (towerSolutionSquareZeroExtension ξ hsurj hsq e cR hcR c eLimit hc P'))

/-- **`φₙ : i⁻¹𝒪_{X'} ≅ 𝒪' ⟶ 𝒜 ⟶ Aₙ`**, for a realization `X₀ ⊂ X'` of a solution `𝒪'` of the
tower problem with its map `κ` to `𝒜 = lim Aₙ`. -/
def towerRealizationRingMap (n : ℕ) :
    (Space.smallEtaleInverseImageRing B S hS Rz.immersion).obj
        (Space.smallEtaleRingedTopos B S hS Rz.ambient).O ⟶
      (Space.smallEtaleInverseImageRing B S hS (towerInclusion ξ n)).obj
        (Space.smallEtaleRingedTopos B S hS (towerSpace ξ n)).O :=
  Rz.sheafIso.hom ≫ κ.hom ≫ limit.π (towerRingSystem ξ) (op n)

/-- The projection `𝒜 ⟶ Aₙ` followed by `aₙ♯` is the reduction of `𝒜`. -/
theorem limit_π_towerRingSystem_comp_structureSharpInverseImage (n : ℕ) :
    limit.π (towerRingSystem ξ) (op n) ≫
        Space.structureSharpInverseImage B S hS (towerInclusion ξ n) =
      towerRingLimitReduction ξ := by
  have hw := limit.w (towerRingSystem ξ) (homOfLE (Nat.zero_le n)).op
  have hn : (towerRingSystem ξ).map (homOfLE (Nat.zero_le n)).op ≫
      (towerRingReduction ξ).app (op 0) = (towerRingReduction ξ).app (op n) :=
    ((towerRingReduction ξ).naturality (homOfLE (Nat.zero_le n)).op).trans (Category.comp_id _)
  rw [← towerRingReduction_app, ← hn, ← Category.assoc, hw]

/-- **`φₙ` lies over the reductions**: `φₙ ≫ aₙ♯ = i♯`. -/
theorem towerRealizationRingMap_comp_fSharpInverseImage (n : ℕ) :
    towerRealizationRingMap ξ hsurj hsq e he cR hcR c eLimit hc κ Rz n ≫
        (Space.smallEtaleRingedToposHom B S hS (towerInclusion ξ n)).fSharpInverseImage =
      (Space.smallEtaleRingedToposHom B S hS Rz.immersion).fSharpInverseImage := by
  have h1 := limit_π_towerRingSystem_comp_structureSharpInverseImage ξ n
  have h2 : κ.hom ≫ towerRingLimitReduction ξ = P'.reduction := κ.reduction_comm
  refine (Category.assoc _ _ _).trans ?_
  refine ((congrArg (Rz.sheafIso.hom ≫ ·) ((Category.assoc _ _ _).trans
    ((congrArg (κ.hom ≫ ·) h1).trans h2)))).trans ?_
  exact Rz.quotient_compatibility

/-- `X₀ ⟶ X' ⟶ Y` is `X₀ ⟶ Xₙ ⟶ Y`. -/
theorem towerRealization_immersion_comp_toBase (n : ℕ) :
    Rz.immersion ≫ Rz.toBase = towerInclusion ξ n ≫ towerLimitStructureMap ξ c n :=
  Rz.over_base.trans (towerInclusion_comp_towerLimitStructureMap ξ c n).symm

/-- The algebra structure of the realized solution, followed by `κ` and the projection to
`Aₙ`, is the map `(X₀ ⟶ Y)⁻¹𝒪_Y ⟶ Aₙ` of the tower. -/
theorem towerSolutionSquareZeroExtension_toBase_comp_limit_π (n : ℕ) :
    (towerSolutionSquareZeroExtension ξ hsurj hsq e cR hcR c eLimit hc P').toBase ≫ κ.hom ≫
        limit.π (towerRingSystem ξ) (op n) = towerLimitBaseMapApp ξ c n := by
  have hbm : P'.baseMap ≫ κ.hom = towerProblemLimitBaseMap ξ c hsurj hsq e cR hcR eLimit hc :=
    κ.baseMap_comm
  have hθ : (towerSolutionBaseIso ξ hsurj hsq e cR hcR c eLimit hc).hom ≫
      (Space.thickenedBaseIso B S hS (towerStructureMap ξ 0) (schemeSpaceMap (c.ι.app 0))
        (towerProblemBaseIso ξ hsurj hsq e cR hcR c eLimit hc)).inv = 𝟙 _ :=
    (Space.thickenedBaseIso B S hS (towerStructureMap ξ 0) (schemeSpaceMap (c.ι.app 0))
        (towerProblemBaseIso ξ hsurj hsq e cR hcR c eLimit hc)).hom_inv_id
  have hL : towerProblemLimitBaseMap ξ c hsurj hsq e cR hcR eLimit hc ≫
      limit.π (towerRingSystem ξ) (op n) =
      (Space.thickenedBaseIso B S hS (towerStructureMap ξ 0) (schemeSpaceMap (c.ι.app 0))
        (towerProblemBaseIso ξ hsurj hsq e cR hcR c eLimit hc)).inv ≫ towerLimitBaseMapApp ξ c n :=
    (Category.assoc _ _ _).trans (congrArg _ (limit.lift_π _ _))
  change ((towerSolutionBaseIso ξ hsurj hsq e cR hcR c eLimit hc).hom ≫ P'.baseMap) ≫ κ.hom ≫
    limit.π (towerRingSystem ξ) (op n) = _
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) hbm).trans hL))).trans ?_
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hθ).trans (Category.id_comp _))

/-- Cancelling `eqToHom`s, abstractly: if `t = eqToHom h₁ ≫ a ≫ b ≫ s` and
`t ≫ k = eqToHom h₂ ≫ m'`, then `(a ≫ b) ≫ s ≫ k = eqToHom h ≫ m'`. Stated in an abstract
category so that it is matched up to definitional unfolding at concrete sheaves. -/
theorem comp_eq_eqToHom_comp_of_eq_eqToHom_comp {C : Type*} [Category C]
    {Y Y₁ Y₂ M M' A P : C} (t : Y ⟶ A) (k : A ⟶ P) (h₁ : Y = Y₁) (h₂ : Y = Y₂) (h : Y₁ = Y₂)
    (a : Y₁ ⟶ M) (b : M ⟶ M') (s : M' ⟶ A) (m' : Y₂ ⟶ P)
    (hA : t = eqToHom h₁ ≫ a ≫ b ≫ s) (key : t ≫ k = eqToHom h₂ ≫ m') :
    (a ≫ b) ≫ s ≫ k = eqToHom h ≫ m' := by
  subst h₁ h₂ hA
  simpa using key

/-- **`φₙ` is compatible with the maps from `(X₀ ⟶ Y)⁻¹𝒪_Y`**: `(X₀ ⟶ X' ⟶ Y)⁻¹𝒪_Y ⟶ i⁻¹𝒪_{X'}`
followed by `φₙ` is `(X₀ ⟶ Xₙ ⟶ Y)⁻¹𝒪_Y ⟶ aₙ⁻¹𝒪_{Xₙ}`. This is the `05ZT` algebra
compatibility of the realization, the compatibility of `κ` with the maps from the thickened base,
and the definition of `𝒜 ⟶ Aₙ` on the base. -/
theorem inverseImageStructureSheafMap_comp_towerRealizationRingMap (n : ℕ) :
    Space.inverseImageStructureSheafMap B S hS Rz.immersion Rz.toBase ≫
        towerRealizationRingMap ξ hsurj hsq e he cR hcR c eLimit hc κ Rz n =
      eqToHom (congrArg (Space.inverseImageStructureSheaf B S hS)
          (towerRealization_immersion_comp_toBase ξ hsurj hsq e cR hcR c eLimit hc Rz n)) ≫
        Space.inverseImageStructureSheafMap B S hS (towerInclusion ξ n)
          (towerLimitStructureMap ξ c n) := by
  have key := towerSolutionSquareZeroExtension_toBase_comp_limit_π ξ hsurj hsq e he cR hcR c
    eLimit hc κ n
  exact comp_eq_eqToHom_comp_of_eq_eqToHom_comp _ _ _ _ _ _ _ _ _
    Rz.algebra_compatibility key

end AlgebraicGeometry.ProperFlatFibre

end
