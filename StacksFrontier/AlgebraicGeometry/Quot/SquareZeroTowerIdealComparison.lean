module

public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerKernelChange
public import StacksFrontier.Deformation.RingThickening.SquareZeroTowerKernels

/-!
# The kernels `Iₙ` as modules over `Γ(Y₀)`

In the situation of `AlgebraicGeometry.ProperFlatFibre.towerProblem`, the body of the proof of
[Stacks Project, Tag 0D3X] applies [Stacks Project, Tag 0D3F] to `X₀ ⟶ Y₀` and the inverse system
of the kernels `Iₙ = Ker(Rₙ → R₀)`. This file reads that system over `Γ(Y₀) ≅ R₀`, the base ring
of `𝒪_{X₀} ⊗ -`, with its surjective transition maps.

## Main definitions

* `AlgebraicGeometry.ProperFlatFibre.towerBaseKernelSystem`: `n ↦ Iₙ` as `Γ(Y₀)`-modules.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public noncomputable section

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

/-- **The kernels `Iₙ = Ker(Rₙ → R₀)` as modules over `Γ(Y₀)`**, through `Γ(Y₀) ≅ R₀`. -/
abbrev towerBaseKernelSystem : ℕᵒᵖ ⥤ ModuleCat.{u} (Space.baseRing B S hS (towerBase ξ 0)) :=
  CommAlgCat.towerKernelSystem R hsurj hsq ⋙
    ModuleCat.restrictScalars.{u} (towerBaseΓIso ξ e 0).hom.hom

/-- The transition maps of `towerBaseKernelSystem` are surjective. -/
theorem surjective_towerBaseKernelSystem_map (n : ℕ) :
    Function.Surjective ((towerBaseKernelSystem ξ hsurj hsq e).map (homOfLE (Nat.le_succ n)).op) :=
  CommAlgCat.surjective_towerKernelSystem_map R hsurj hsq n

end AlgebraicGeometry.ProperFlatFibre

end
