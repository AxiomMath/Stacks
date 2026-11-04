module

public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningAffineOverAffineBase.FiniteOrderStep
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningAffineOverAffineBase.FinitelyGeneratedStep

/-!
# Affineness over a thickening of an affine base

Let `U` be an algebraic space over an affine object `T` of the big fppf site of `S`, and let
`T₀ ⟶ T` be a thickening.  If the base change `U ×_T T₀` is affine, then `U` is affine.

The proof has two steps.

* The submersive presentation of a chart of `U ×_T T₀` and its roots lift to a chart of `U`
  modulo a finitely generated ideal `K` of the kernel of `Γ(T) ⟶ Γ(T₀)`; then the base change of
  `U` to the finite-order thickening `Spec(Γ(T)/K)` of `T` is affine
  (`AlgebraicGeometry.Space.exists_isFiniteOrderThickening_isAffineSpace_pullback`).
* Along a finite-order thickening affineness lifts by induction on the order, from the
  first-order case (`AlgebraicGeometry.Space.isAffineSpace_of_isFiniteOrderThickening_pullback`).

## Main results

* `AlgebraicGeometry.Space.isAffineSpace_of_isAffineSpace_pullback_of_isThickening`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **An algebraic space over an affine base whose base change to a thickening of the base is
affine is affine.** -/
theorem isAffineSpace_of_isAffineSpace_pullback_of_isThickening
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    {T₀ T : BigFppfOver B S hS} (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (k : T₀ ⟶ T) (hk : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k))
    (π : U ⟶ yoneda.obj T)
    (hU₀ : IsAffineSpace B S hS (pullback π (yoneda.map k))) :
    IsAffineSpace B S hS U := by
  have := hT
  obtain ⟨_, ι, hι, hUι⟩ :=
    exists_isFiniteOrderThickening_isAffineSpace_pullback B S hS hU k hk π hU₀
  exact isAffineSpace_of_isFiniteOrderThickening_pullback B S hS hU ι hι π hUι

end AlgebraicGeometry.Space

end
