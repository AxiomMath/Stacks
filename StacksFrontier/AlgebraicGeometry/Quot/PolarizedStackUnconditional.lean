module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedLimitPreserving
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.BaseChange

/-!
# The stack of polarized families, with Stacks Tag 0893 discharged

`AlgebraicGeometry.polarizedProjection_isFiberedInGroupoids` and
`AlgebraicGeometry.polarizedStack` are stated on the hypothesis
`AlgebraicGeometry.Scheme.Modules.RelativelyAmpleBaseChange`, which is Stacks Tag 0893. That
hypothesis is now the theorem `Stacks.AmpleBridge.relativelyAmpleBaseChange`, so this file
records the same statements with no hypothesis.

## Main results

* `AlgebraicGeometry.polarizedProjection_existsLift_unconditional` and
  `AlgebraicGeometry.polarizedProjection_isFiberedInGroupoids_unconditional`: **Stacks 003S** for
  polarized families, with no hypothesis. The second is also the assertion of **Stacks 0D3Z**
  over the big fppf site of schemes.
* `AlgebraicGeometry.polarizedStackUnconditional`: **Stacks 0D1M and 003S**, `𝒫olarized` as an
  object of the 2-category of categories fibred in groupoids over the big fppf site of a
  terminal base scheme, with no hypothesis.
* `AlgebraicGeometry.IsLimitPreservingPolarizedUnconditional`: the assertion of Stacks 07XL for
  `𝒫olarized`, stated with no hypothesis. It is proved, at index categories in the scheme
  universe, by `AlgebraicGeometry.isLimitPreservingPolarizedUnconditional` in
  `StacksFrontier/AlgebraicGeometry/Quot/PolarizedLimitPreservingProof.lean`.

## References

* [Stacks Project, Tag 003S](https://stacks.math.columbia.edu/tag/003S)
* [Stacks Project, Tag 0D1M](https://stacks.math.columbia.edu/tag/0D1M)
* [Stacks Project, Tag 0893](https://stacks.math.columbia.edu/tag/0893)
* [Stacks Project, Tag 0D43](https://stacks.math.columbia.edu/tag/0D43)
-/

@[expose] public noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- **Stacks 003S (a) for polarized families, with no hypothesis.** Every morphism of base
schemes lifts to a morphism of polarized families into any polarized family over its target. -/
theorem polarizedProjection_existsLift_unconditional {B : BigFppfSite.{u}} {V U : B.Schemes}
    (f : V ⟶ U) (x : PolarizedFamily B) (hx : (polarizedProjection B).obj x = U) :
    ∃ (y : PolarizedFamily B) (φ : y ⟶ x), (polarizedProjection B).IsHomLift f φ :=
  polarizedProjection_existsLift Stacks.AmpleBridge.relativelyAmpleBaseChange f x hx

/-- **Stacks 003S for polarized families, with no hypothesis.** Polarized families of Stacks
0D1M form a category fibred in groupoids over the big fppf site.

This is also **Stacks 0D3Z** over the big fppf site of schemes: condition (a) of Stacks 003S is
`AlgebraicGeometry.polarizedProjection_existsLift`, by base change, and condition (b) is
`AlgebraicGeometry.polarizedProjection_uniqueLift`. -/
@[stacks 0D3Z "fibred in groupoids over the fppf site of schemes"]
theorem polarizedProjection_isFiberedInGroupoids_unconditional {B : BigFppfSite.{u}} :
    (polarizedProjection B).IsFiberedInGroupoids :=
  polarizedProjection_isFiberedInGroupoids Stacks.AmpleBridge.relativelyAmpleBaseChange

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)

/-- **Stacks 0D1M and 003S, with no hypothesis.** `𝒫olarized` as an object of the 2-category of
categories fibred in groupoids over the big fppf site of a terminal base scheme. -/
def polarizedStackUnconditional (hT : IsTerminal (B.obj hS)) :
    CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
  polarizedStack B hS Stacks.AmpleBridge.relativelyAmpleBaseChange hT

/-- The assertion of Stacks 07XL for `𝒫olarized`, with no hypothesis: for every cofiltered
inverse system of affine schemes over the terminal base with limit `T`, the canonical comparison
`colim 𝒫olarized_{Tᵢ} ⥤ 𝒫olarized_T` is an equivalence of categories. -/
abbrev IsLimitPreservingPolarizedUnconditional (hT : IsTerminal (B.obj hS)) : Prop :=
  Deformation.Artin.IsLimitPreserving.{u, v, w, u + 1, u} B S hS
    (polarizedStackUnconditional B hS hT)

end AlgebraicGeometry

end
