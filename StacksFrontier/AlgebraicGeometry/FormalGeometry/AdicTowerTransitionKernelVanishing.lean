module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicTowerTransitionKernel
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections

/-!
# The uniform twisted vanishing the proof of [Stacks, Tag 089A] asks of the transition kernels

The second paragraph of the proof of [Stacks, Tag 089A] ends by producing an integer `d₀` with

  `H¹(X₀, 𝓕ₙ ⊗ L ^⊗ d) = 0` for every `n` and every `d ≥ d₀`,

`𝓕ₙ = Ker(𝒪_{X_{n+1}} ⟶ 𝒪_{Xₙ})` being `Stacks.AdicTower.transitionKernel`. The point is the
uniformity in `n`: a bound depending on `n` would not let the sections of `L ^⊗ d` be lifted
inductively up the tower, which is what the rest of the proof does with it.

This file names that conclusion, as `Stacks.AdicTower.UniformTwistVanishing`, in the spelling
[Stacks, Tag 0897] part (2) produces —
`Stacks.AlgebraicGeometry.GradedProperCohomology.cohomologyOf` of
`Stacks.RelativeVeryAmple.tensorModules` with `Stacks.Ample.tensorPowModule`, which is
exactly `Stacks.AlgebraicGeometry.GradedProperCohomology.pieceTwist` read at a homogeneous
piece. It also supplies the one step between the two:
`Stacks.AdicTower.uniformTwistVanishing_of_isZero_pieceTwistCohomology` turns the conclusion of
[Stacks, Tag 0897] part (2) for *any* graded module whose degree-`n+1` piece is `𝓕ₙ` into
`UniformTwistVanishing`, so that once the graded module of the source's paragraph and
[Stacks, Tag 0897] part (2) are both available the vanishing is a one-line substitution.

**No instance of [Stacks, Tag 0897] is used here.** Its only sites in this repository,
`Stacks.AlgebraicGeometry.GradedProperCohomology.exists_isZero_pieceTwistCohomology` and its
primed variant, still carry the base change `X' = Spec B ×_{Spec A} X₀` of the source's proof as
hypotheses; discharging those is not this file's business.

## Main definitions

* `Stacks.AdicTower.UniformTwistVanishing`: **the vanishing, as a proposition.**

## Main results

* `Stacks.AdicTower.uniformTwistVanishing_of_isZero_pieceTwistCohomology`: the conclusion of
  [Stacks, Tag 0897] part (2) for a graded module realizing the transition kernels gives it.

## References

* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.RelativeVeryAmple
open Stacks.AlgebraicGeometry.GradedProperCohomology
open scoped AlgebraicGeometry

universe u

namespace Stacks.AdicTower

variable {A : Type u} [CommRing A] {I : Ideal A} {Xn : ℕ → Scheme.{u}}
  {t : ∀ n, Xn n ⟶ Xn (n + 1)}

/-- **The uniform twisted vanishing of [Stacks, Tag 089A].** There is a degree `d₀`, the same
for every `n`, above which the first cohomology of the `d`-th twist of the transition kernel
`𝓕ₙ = Ker(𝒪_{X_{n+1}} ⟶ 𝒪_{Xₙ})` by an invertible `𝒪_{X₀}`-module `L` vanishes.

The source obtains this from [Stacks, Tag 0897] part (2) applied to the graded algebra
`𝓑 = (X₀ ⟶ S₀)^* B̃` for `B = ⨁ Iⁿ/Iⁿ⁺¹` and to `𝓕 = ⨁_{n ≥ 0} 𝓕ₙ` as a finite type
quasi-coherent graded `𝓑`-module. -/
def UniformTwistVanishing (t : ∀ n, Xn n ⟶ Xn (n + 1)) (L : (Xn 0).Modules)
    [IsInvertibleModule (Xn 0) L] : Prop :=
  ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ n : ℕ,
    IsZero (cohomologyOf (Xn 0) 1
      (tensorModules (Xn 0) (transitionKernel t n) (tensorPowModule (Xn 0) L (d : ℤ))))

/-- **[Stacks, Tag 0897] part (2) gives the uniform vanishing.** Let `F` be a graded module over
a sheaf of graded `𝒪_{X₀}`-algebras whose degree-`n + 1` piece is the `n`-th transition kernel
— which is what the second paragraph of the proof of [Stacks, Tag 089A] constructs. Then the
conclusion of [Stacks, Tag 0897] part (2) for `F`, namely a `d₀` above which every
`Hᵖ(X₀, Fₘ ⊗ L ^⊗ d)` with `p > 0` vanishes, is the uniform vanishing for the transition
kernels.

Only the degree-one, nonnegative-degree part of the hypothesis is used; the statement keeps the
shape [Stacks, Tag 0897] part (2) has so that composing with it is a substitution. -/
theorem uniformTwistVanishing_of_isZero_pieceTwistCohomology
    {𝓑 : _root_.SheafOfModules.GradedAlgebra.{u, u} (Xn 0).ringCatSheaf}
    (F : _root_.SheafOfModules.GradedModule 𝓑)
    (e : ∀ n : ℕ, F.piece ((n + 1 : ℕ) : ℤ) ≅ transitionKernel t n)
    (L : (Xn 0).Modules) [IsInvertibleModule (Xn 0) L]
    (h : ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ p : ℕ, 0 < p → ∀ m : ℤ,
      IsZero (cohomologyOf (Xn 0) p (pieceTwist F L m (d : ℤ)))) :
    UniformTwistVanishing t L := by
  obtain ⟨d₀, hd₀⟩ := h
  refine ⟨d₀, fun d hd n => (hd₀ d hd 1 Nat.one_pos ((n + 1 : ℕ) : ℤ)).of_iso ?_⟩
  exact ((AlgebraicGeometry.moduleGlobalSections (Xn 0)).rightDerived 1).mapIso
    (tensorModulesMapIso (Xn 0) (e n).symm (Iso.refl _))

end Stacks.AdicTower

end
