module

public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitBaseMap
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitSurjective
public import StacksFrontier.Deformation.AlgebraExtension.InverseLimit

/-!
# `𝒜 = lim 𝒪_{Xₙ}` as a solution of the tower problem over a change of ideal

In the situation of `AlgebraicGeometry.ProperFlatFibre.towerProblem`, the body of the proof of
[Stacks Project, Tag 0D3X] considers the extension
`0 → lim 𝒪_{X₁} ⊗ Iₙ → lim 𝒪_{Xₙ} → 𝒪_{X₁} → 0` over `0 → lim Iₙ → lim Rₙ → R₁ → 0`.
This file assembles it on the small étale site of `X₀`: the middle term is `𝒜 = lim Aₙ`
(`towerRingLimit`), its reduction is locally surjective with square-zero kernel, the ideal is the
limit of the ideals `𝒪_{X₀} ⊗ Iₙ` of the extensions `towerExtension`, and the inverse image of the
thickened base maps to `𝒜` over the reductions (`towerProblemLimitBaseMap`). Given a map
`φ : f^*𝒞_{Y₀/Y} ⟶ lim 𝒪_{X₀} ⊗ Iₙ` through which the base ideal is carried to the kernel, this is
a solution of the problem obtained from `towerProblem` by changing its ideal along `φ`.

## Main definitions

* `AlgebraicGeometry.ProperFlatFibre.towerIdealSystem`: the tower `n ↦ 𝒪_{X₀} ⊗ Iₙ` of ideals.
* `AlgebraicGeometry.ProperFlatFibre.towerLimitSolution`: the solution `𝒜` of the changed problem.

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

/-- **The tower `n ↦ 𝒪_{X₀} ⊗ Iₙ` of ideals** of the extensions `towerExtension`, with the
transitions induced by `A_{n+1} ⟶ Aₙ`. -/
abbrev towerIdealSystem :=
  Deformation.AlgebraExtension.InverseLimit.idealSystem.{u, u + 1, u}
    (J := Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (towerRingSystem ξ)
    (towerRingReduction ξ)
    (fun n => towerExtension ξ hsurj hsq e he n (𝟙 _))
    (fun n => towerRingSystemExtensionIso ξ hsurj hsq e he n (𝟙 _))
    (fun n => towerRingSystemExtensionIso_hom_comp_reduction ξ hsurj hsq e he n (𝟙 _))

/-- **The extension `0 → lim 𝒪_{X₀} ⊗ Iₙ → 𝒜 → 𝒪_{X₀} → 0` as a solution of the tower problem
over a change of ideal.** For `φ : f^*𝒞_{Y₀/Y} ⟶ lim 𝒪_{X₀} ⊗ Iₙ` carrying the base ideal to the
kernel of `𝒜 ⟶ 𝒪_{X₀}` (`hφ`), `𝒜` with its reduction, the map from the inverse image of the
thickened base and the inclusion of `lim 𝒪_{X₀} ⊗ Iₙ` solves the problem obtained from
`towerProblem` by changing its ideal along `φ`. -/
def towerLimitSolution
    (φ : (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).G ⟶
      limit (towerIdealSystem ξ hsurj hsq e he))
    (hφ : ∀ (U : (Space.SmallEtale B S hS (towerSpace ξ 0).1)ᵒᵖ)
      (a : (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).I.val.obj U),
      (towerProblemLimitBaseMap ξ c hsurj hsq e cR hcR eLimit hc).hom.app U
          ((towerProblem ξ hsurj hsq e cR hcR c eLimit hc).idealInclusion.val.app U a) =
        (Deformation.AlgebraExtension.InverseLimit.kernelInclusion.{u, u + 1, u}
          (J := Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (towerRingSystem ξ)
          (towerRingReduction ξ) (fun n => towerExtension ξ hsurj hsq e he n (𝟙 _))
          (fun n => towerRingSystemExtensionIso ξ hsurj hsq e he n (𝟙 _))
          (fun n =>
            towerRingSystemExtensionIso_hom_comp_reduction ξ hsurj hsq e he n (𝟙 _))).val.app U
          (φ.val.app U ((towerProblem ξ hsurj hsq e cR hcR c eLimit hc).c.val.app U a))) :
    ((towerProblem ξ hsurj hsq e cR hcR c eLimit hc).changeKernel φ).CompatibleFirstOrderThickening
    where
  extension := towerRingLimit ξ
  reduction := towerRingLimitReduction ξ
  locallySurjective := isLocallySurjective_towerRingLimitReduction ξ hsurj hsq e he
  squareZero := towerRingLimitReduction_squareZero ξ hsurj hsq e he
  baseMap := towerProblemLimitBaseMap ξ c hsurj hsq e cR hcR eLimit hc
  baseMap_reduction := towerProblemLimitBaseMap_reduction ξ c hsurj hsq e cR hcR eLimit hc
  kernelInclusion := Deformation.AlgebraExtension.InverseLimit.kernelInclusion.{u, u + 1, u}
          (J := Space.SmallEtale.topology B S hS (towerSpace ξ 0).1) (towerRingSystem ξ)
    (towerRingReduction ξ) (fun n => towerExtension ξ hsurj hsq e he n (𝟙 _))
    (fun n => towerRingSystemExtensionIso ξ hsurj hsq e he n (𝟙 _))
    (fun n => towerRingSystemExtensionIso_hom_comp_reduction ξ hsurj hsq e he n (𝟙 _))
  kernelZero := Deformation.AlgebraExtension.InverseLimit.kernelZero.{u, u + 1, u} _ _ _ _ _
  kernelUniversal :=
    Deformation.AlgebraExtension.InverseLimit.kernelUniversal.{u, u + 1, u} _ _ _ _ _
  baseMap_ideal := hφ

end AlgebraicGeometry.ProperFlatFibre

end
