module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.WholeTag
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.ContainedSubscheme

/-!
# Over a closed subscheme of `D`, the two branches cover the whole total space

In the situation of [Stacks, Tag 0F97] let `W ⊆ Y` be a closed subscheme contained in the divisor
`D`, that is `zeroIdeal Y L₁ L₂ s ≤ W` in the order on ideal sheaves. The case `W ⊆ D` of
[Stacks, Tag 0F98] base-changes the diagram along `W ↪ Y` and reads off
`p^{-1}(W) = W₁ ∪ W₂` with each `Wᵢ` a line bundle over `W`. This file supplies that union.

The mechanism is that the base change turns `D` into the whole of `W`: the section `s` restricts
to zero on `W` because `W` sits inside its zero scheme
(`Stacks.Divisors.pullbackGlobalSections_subschemeι_eq_zero_of_le`, [Stacks, Tag 02OR]), and the
comparison of [Stacks, Tag 01CD] that reads the restricted section as a section of the tensor
product of the restricted modules is additive, so the restricted section of `L₁ ⊗ L₂` is zero
too, and the zero scheme of a zero section is everything
(`Stacks.Divisors.zeroScheme_zero_eq_bot`). Condition (5) of
`Stacks.Chow.TensorZeroScheme.Decomposition` over `W` therefore reads
`⊥ = D₁ ⊓ D₂` — the two branches, intersected as ideal sheaves, meet in the trivial ideal, which
is to say they cover the total space as closed subschemes. Nothing here is specific to which
decomposition over `W` is used, so the statement is about an arbitrary one; the one produced by
base change is supplied by
`Stacks.Chow.TensorZeroScheme.Decomposition.isStableUnderBaseChange`.

Note the index convention of `Stacks.Chow.TensorZeroScheme.Decomposition`: `⊓` of ideal sheaves
is the scheme-theoretic *union* of the subschemes and `⊔` their intersection, the ideal order
being opposite to inclusion.

## Main results

* `Stacks.Chow.TensorZeroScheme.pullbackTensorSection_subschemeι_eq_zero_of_le`: **the section
  cutting out `D` restricts to zero on any closed subscheme of `D`**, at the spelling of the
  restricted section that the base change of the diagram of [Stacks, Tag 0F97] uses.
* `Stacks.Chow.TensorZeroScheme.zeroIdeal_pullbackTensorSection_subschemeι_eq_bot`: **the divisor
  of the base-changed diagram over a closed subscheme of `D` is the whole subscheme.**
* `Stacks.Chow.TensorZeroScheme.Decomposition.inf_eq_bot_of_zeroIdeal_le`: **the two branches of
  a decomposition over a closed subscheme of `D` cover its total space**, which is the identity
  `p^{-1}(W) = W₁ ∪ W₂` of the proof of [Stacks, Tag 0F98].

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.PullbackTensorIso (pullbackTensorSection)

universe u

namespace Stacks.Chow.TensorZeroScheme

variable {Y : Scheme.{u}} (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)) (W : Y.IdealSheafData)

include h₁ h₂ in
/-- **The section cutting out `D` restricts to zero on any closed subscheme of `D`**, read as a
section of the tensor product of the restricted modules. The restriction of `s` as a section of
`L₁ ⊗ L₂` vanishes because the subscheme lies in the zero scheme, and the comparison of
[Stacks, Tag 01CD] which rewrites it as a section of `L₁|_W ⊗ L₂|_W` is additive. -/
theorem pullbackTensorSection_subschemeι_eq_zero_of_le (hW : zeroIdeal Y L₁ L₂ s ≤ W) :
    pullbackTensorSection W.subschemeι L₁ L₂ s = 0 := by
  have h0 : pullbackGlobalSections W.subschemeι (Stacks.Divisors.tensorModules L₁ L₂) s = 0 :=
    Stacks.Divisors.pullbackGlobalSections_subschemeι_eq_zero_of_le
      (Stacks.Divisors.tensorModules L₁ L₂) s W hW
  have hrfl : pullbackTensorSection W.subschemeι L₁ L₂ s =
      Scheme.Modules.Hom.app
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso W.subschemeι L₁ L₂).hom ⊤
        (pullbackGlobalSections W.subschemeι (Stacks.Divisors.tensorModules L₁ L₂) s) := rfl
  rw [hrfl, h0, map_zero]

include h₁ h₂ in
/-- **The divisor of the base-changed diagram over a closed subscheme of `D` is the whole
subscheme.** Its cutting section is zero, and the zero scheme of a zero section is everything. -/
theorem zeroIdeal_pullbackTensorSection_subschemeι_eq_bot (hW : zeroIdeal Y L₁ L₂ s ≤ W) :
    zeroIdeal W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s) = ⊥ := by
  rw [zeroIdeal, pullbackTensorSection_subschemeι_eq_zero_of_le L₁ L₂ s W hW,
    Stacks.Divisors.zeroScheme_zero_eq_bot]

include h₁ h₂ in
/-- **The two branches of a decomposition over a closed subscheme of `D` cover its total
space.** This is the identity `p^{-1}(W) = W₁ ∪ W₂` of the case `W ⊆ D` of [Stacks, Tag 0F98]:
condition (5) of the diagram computes the inverse image of the divisor as the union of the two
branches, and over `W` the divisor is all of `W`, so its inverse image is all of the total
space. -/
theorem Decomposition.inf_eq_bot_of_zeroIdeal_le (hW : zeroIdeal Y L₁ L₂ s ≤ W)
    (R : Decomposition W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)) :
    R.D₁ ⊓ R.D₂ = ⊥ := by
  rw [← R.preimage_eq_union, zeroIdeal_pullbackTensorSection_subschemeι_eq_bot L₁ L₂ s W hW,
    Scheme.IdealSheafData.comap_bot]

end Stacks.Chow.TensorZeroScheme

end
