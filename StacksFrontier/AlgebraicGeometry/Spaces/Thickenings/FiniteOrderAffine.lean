module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineOfFiniteOrderThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FirstOrderAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FirstOrderFiltration

/-!
# A finite order thickening of an affine algebraic space is affine

Let `G ⊂ X` be an `n`th order thickening of algebraic spaces over a scheme `S` whose closed member
`G` is affine.  Then `X` is affine.  This is the direct argument for finite order thickenings in
the proof of Stacks 05ZR: filter `G = X₀ ⊂ X₁ ⊂ ⋯ ⊂ Xₙ = X` by the closed subspaces cut out by the
powers of the ideal of `G`; each `Xₖ ⊂ Xₖ₊₁` is a first-order thickening, so each `Xₖ` is affine
by induction on `k` (`AlgebraicGeometry.Space.isAffineSpace_of_isFirstOrderThickening`).

## Main results

* `AlgebraicGeometry.Space.isAffineSpace_of_isNthOrderThickening`
* `AlgebraicGeometry.Space.isAffineSpace_of_isFiniteOrderThickening`

## References

* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An `n`th order thickening of an affine algebraic space is affine.**  Let `G ⊂ X` be an
`n`th order thickening of algebraic spaces over `S` whose closed member `G` is affine.  Then `X`
is affine. -/
theorem isAffineSpace_of_isNthOrderThickening {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}
    {n : ℕ} (hG : IsNthOrderThickening B S hS n X G) (hGa : IsAffineSpace B S hS G.toFunctor) :
    IsAffineSpace B S hS X.1 := by
  obtain ⟨Xs, -, -, -, h0, hn, hle, hfo⟩ := exists_firstOrderThickening_filtration B S hS X hG
  have key : ∀ k, IsAffineSpace B S hS (Xs k).1.toFunctor := by
    intro k
    induction k with
    | zero => rw [h0]; exact hGa
    | succ k ih =>
      refine isAffineSpace_of_isFirstOrderThickening B S hS
        (X := ⟨(Xs (k + 1)).1.toFunctor, (Xs (k + 1)).2.1⟩) (hfo k) (ih.of_iso ?_)
      exact NatIso.ofComponents (fun T ↦ Equiv.toIso
        { toFun := fun x ↦ ⟨⟨x.1, hle k T x.2⟩, x.2⟩
          invFun := fun y ↦ ⟨y.1.1, y.2⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }) (fun _ ↦ rfl)
  have hX := key n
  rw [hn] at hX
  exact hX.of_iso (asIso (Subfunctor.ι _))

end AlgebraicGeometry.Space

end
