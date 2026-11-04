module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.DecompositionNormalize
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.DecompositionTransport
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeRegularSection
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeTensorFactor

/-!
# The diagram of Tag 0F97 restricted to a closed subscheme of the base, and the two branch
divisors there

Let `Y` be a scheme, let `L₁`, `L₂` be invertible `𝒪_Y`-modules, let `s ∈ Γ(Y, L₁ ⊗ L₂)` and let
`D = Z(s)`, `p : L ⟶ Y`, `D₁`, `D₂` be the diagram of [Stacks, Tag 0F97]. For a closed subscheme
`W ⊆ Y` this file base-changes that whole diagram along the closed immersion `W ↪ Y`, and reads
off the consequence [Stacks, Tag 0F98] needs in its case `W ⊄ D`: both branch divisors restrict to
**effective Cartier divisors** on `p^{-1}(W)`.

The cartesian square to base change along is
`AlgebraicGeometry.Scheme.IdealSheafData.isPullback_subschemeMap_of_comap` at `p` and `W`, whose
corner is the scheme-theoretic inverse image `p^{-1}(W)` presented as an ideal sheaf; feeding it to
`Stacks.Chow.TensorZeroScheme.Decomposition.baseChange` produces a diagram as in the tag over `W`
whose two closed subschemes are, by
`Stacks.Chow.TensorZeroScheme.Decomposition.comap_D₁_baseChange`, exactly `D₁ ∩ p^{-1}(W)` and
`D₂ ∩ p^{-1}(W)`.

## Main definitions

* `Stacks.Chow.TensorZeroScheme.decompositionComap` — **the diagram of Tag 0F97 over a closed
  subscheme `W` of the base**, as a `Stacks.Chow.TensorZeroScheme.Decomposition`.

## Main results

* `Stacks.Chow.TensorZeroScheme.comap_branch₁_decompositionComap` and `…_branch₂_…` — its two
  closed subschemes are the restrictions of `D₁` and of `D₂`.
* `Stacks.Chow.TensorZeroScheme.isEffectiveCartierDivisor_comap_branch₁_of_not_le` and
  `…_branch₂_…` — **for `W` integral and not contained in `D`, the restriction of each branch to
  `p^{-1}(W)` is an effective Cartier divisor.**

## Implementation notes

### Why the branches become Cartier only after restricting to `p^{-1}(W)`

`D₁` is *not* an effective Cartier divisor on `L`: over an affine `Spec(B) ⊆ Y` with both modules
trivialized, `L` is `Spec(B[z₁, z₂]/(z₁z₂ - f))` with `f` cutting out `D`, `D₁` is cut out by `z₁`,
and `z₁ · z₂ = f` makes `z₁` a zerodivisor wherever `f` vanishes. Nor is `D₁ ⟶ Y` flat — it
factors through the closed immersion `D ↪ Y` by
`Stacks.Chow.TensorZeroScheme.branch₁_subschemeι_comp_proj` — so the relative-divisor base change
`Stacks.Chow.isEffectiveCartierDivisor_comap_comap_subschemeι` does not apply either. The
hypothesis `W ⊄ D` is therefore essential and is used twice.

### The route

Over `W` the section `s` restricts to a *regular* section, because `W` is integral and `W ⊄ D`
says the restriction is nonzero: that is
`Stacks.Divisors.isEffectiveCartierDivisor_comap_zeroScheme_of_isIntegral`, giving that `D ∩ W` is
an effective Cartier divisor on `W`. The projection `p^{-1}(W) ⟶ W` is flat, being a base change of
`p` — it is the field `p_flat` of the base-changed diagram — so
`Stacks.Divisors.isPullbackDefined_of_flat` carries that divisor to an effective Cartier divisor
on `p^{-1}(W)`. Condition (1) of the tag identifies it there with the zero scheme of a *pure
tensor* `s₁ ⊗ s₂` of the two transported sections
(`Stacks.Chow.TensorZeroScheme.comap_zeroIdeal_of_tensorSection_eq`), and
`Stacks.Divisors.isEffectiveCartierDivisor_zeroScheme_of_tensorSection_left` splits a Cartier zero
scheme of a pure tensor into its two factors. Those factors are the two branches by condition (3),
which the base-changed diagram carries as `zeroScheme₁` and `zeroScheme₂`.

No local-model computation enters: the nonzerodivisor statement about `z₁` is obtained from the
one about `f` by the factorization, not by a chart.

### No `@[stacks 0F98]` attribute here

[Stacks, Tag 0F98] is a single identity of maps on Chow groups and nothing here asserts it; this
file discharges one hypothesis of one of the two cases of its proof. Putting a qualified `0F98` on
a prerequisite would misrepresent a proof step as a fragment of the statement — see the convention
notes in `StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChowMaps` and
`…ChowPrimeCycleTransverse`. The identity itself is
`Stacks.Chow.TensorZeroScheme.gysinChowBranch₁_flatPullbackChowProj` of
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionBranchChowIdentity`.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
* [Stacks Project, Tag 02OO](https://stacks.math.columbia.edu/tag/02OO)
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
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)) (R : Decomposition Y L₁ L₂ s)
  (W : Y.IdealSheafData)

/-! ### The cartesian square of a closed subscheme of the base -/

include h₁ h₂ in
/-- **The inverse image of a closed subscheme of the base is a fibre product.** This is
`AlgebraicGeometry.Scheme.IdealSheafData.isPullback_subschemeMap_of_comap` at the projection `p`
of the diagram of Tag 0F97, and it is the square the diagram is base changed along. -/
theorem isPullback_comap_proj :
    IsPullback (W.comap R.normalize.p).subschemeι
      (Scheme.IdealSheafData.subschemeMap (W.comap R.normalize.p) W R.normalize.p
        (Scheme.IdealSheafData.le_map_iff_comap_le.2 le_rfl))
      R.normalize.p W.subschemeι :=
  Scheme.IdealSheafData.isPullback_subschemeMap_of_comap R.normalize.p rfl

/-! ### The diagram of Tag 0F97 over a closed subscheme of the base -/

include h₁ h₂ in
/-- **The diagram of [Stacks, Tag 0F97] over a closed subscheme `W` of the base.** Its total space
is the scheme-theoretic inverse image `p^{-1}(W)`, its projection is the restriction of `p`, and
all seven conditions of the tag hold for it — this is
`Stacks.Chow.TensorZeroScheme.Decomposition.baseChange`, the base-change clause of the tag, at the
closed immersion `W ↪ Y`. -/
def decompositionComap :
    Decomposition W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s) :=
  R.normalize.baseChange W.subschemeι (isPullback_comap_proj L₁ L₂ s R W)

include h₁ h₂ in
/-- The first closed subscheme of the diagram over `W` is the restriction of `D₁` to
`p^{-1}(W)`. -/
theorem comap_branch₁_decompositionComap :
    (decompositionComap L₁ L₂ s R W).D₁ =
      R.normalize.D₁.comap (W.comap R.normalize.p).subschemeι :=
  (R.normalize.comap_D₁_baseChange W.subschemeι
    (isPullback_comap_proj L₁ L₂ s R W)).symm

include h₁ h₂ in
/-- The second closed subscheme of the diagram over `W` is the restriction of `D₂` to
`p^{-1}(W)`. -/
theorem comap_branch₂_decompositionComap :
    (decompositionComap L₁ L₂ s R W).D₂ =
      R.normalize.D₂.comap (W.comap R.normalize.p).subschemeι :=
  (R.normalize.comap_D₂_baseChange W.subschemeι
    (isPullback_comap_proj L₁ L₂ s R W)).symm

/-! ### The two branch divisors on `p^{-1}(W)` -/

include h₁ h₂ in
/-- **The inverse image of `D` in `p^{-1}(W)` is the zero scheme of a pure tensor, and is an
effective Cartier divisor there**, for `W` integral and not contained in `D`.

`D ∩ W` is an effective Cartier divisor on `W` because `W` is integral and the restriction of `s`
to it is nonzero (`Stacks.Divisors.isEffectiveCartierDivisor_comap_zeroScheme_of_isIntegral`), and
`p^{-1}(W) ⟶ W` is flat, so `Stacks.Divisors.isPullbackDefined_of_flat` carries it over; condition
(1) of Tag 0F97 for the base-changed diagram presents the result as the zero scheme of
`s₁ ⊗ s₂`. -/
theorem isEffectiveCartierDivisor_zeroScheme_tensorSection_decompositionComap
    (hWint : IsIntegral W.subscheme) (hle : ¬ zeroIdeal Y L₁ L₂ s ≤ W) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (Stacks.Divisors.zeroScheme (decompositionComap L₁ L₂ s R W).total
        (Stacks.Divisors.tensorModules
          ((Scheme.Modules.pullback (decompositionComap L₁ L₂ s R W).p).obj
            ((Scheme.Modules.pullback W.subschemeι).obj L₁))
          ((Scheme.Modules.pullback (decompositionComap L₁ L₂ s R W).p).obj
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)))
        (Stacks.Divisors.tensorSection _ _ ⊤ (decompositionComap L₁ L₂ s R W).s₁
          (decompositionComap L₁ L₂ s R W).s₂)) := by
  set R' := decompositionComap L₁ L₂ s R W with hR
  have : AlgebraicGeometry.Flat R'.p := R'.p_flat
  have hD : Stacks.Divisors.IsEffectiveCartierDivisor
      (zeroIdeal W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s)) := by
    rw [← comap_zeroIdeal s W.subschemeι]
    exact Stacks.Divisors.isEffectiveCartierDivisor_comap_zeroScheme_of_isIntegral
      (Stacks.Divisors.tensorModules L₁ L₂) s W hWint hle
  have hcomap : Stacks.Divisors.IsEffectiveCartierDivisor
      ((zeroIdeal W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s)).comap R'.p) :=
    Stacks.Divisors.isPullbackDefined_of_flat R'.p _ hD
  rw [comap_zeroIdeal_of_tensorSection_eq (pullbackTensorSection W.subschemeι L₁ L₂ s) R'.p
    R'.s₁ R'.s₂ R'.pullback_section_eq] at hcomap
  exact hcomap

include h₁ h₂ in
/-- **The restriction of the first branch `D₁` to `p^{-1}(W)` is an effective Cartier divisor**,
for `W` an integral closed subscheme of `Y` not contained in `D` — the case `W ⊄ D` of
[Stacks, Tag 0F98]. This is the hypothesis `hD₁` of
`Stacks.Chow.TensorZeroScheme.leftRule_cycle_eq_rightRule_cycle_of_cartier`.

The inverse image of `D` in `p^{-1}(W)` is the zero scheme of the pure tensor `s₁ ⊗ s₂` and is
Cartier there, and
`Stacks.Divisors.isEffectiveCartierDivisor_zeroScheme_of_tensorSection_left` splits off the first
factor, whose zero scheme is `D₁ ∩ p^{-1}(W)` by condition (3) of Tag 0F97. -/
theorem isEffectiveCartierDivisor_comap_branch₁_of_not_le
    (hWint : IsIntegral W.subscheme) (hle : ¬ zeroIdeal Y L₁ L₂ s ≤ W) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (R.normalize.D₁.comap (W.comap R.normalize.p).subschemeι) := by
  set R' := decompositionComap L₁ L₂ s R W with hR
  rw [← comap_branch₁_decompositionComap L₁ L₂ s R W, R'.zeroScheme₁]
  exact Stacks.Divisors.isEffectiveCartierDivisor_zeroScheme_of_tensorSection_left _ _ R'.s₁ R'.s₂
    (isEffectiveCartierDivisor_zeroScheme_tensorSection_decompositionComap L₁ L₂ s R W hWint hle)

include h₁ h₂ in
/-- **The restriction of the second branch `D₂` to `p^{-1}(W)` is an effective Cartier divisor**,
for `W` an integral closed subscheme of `Y` not contained in `D`: the argument of
`Stacks.Chow.TensorZeroScheme.isEffectiveCartierDivisor_comap_branch₁_of_not_le` in the second
factor. -/
theorem isEffectiveCartierDivisor_comap_branch₂_of_not_le
    (hWint : IsIntegral W.subscheme) (hle : ¬ zeroIdeal Y L₁ L₂ s ≤ W) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (R.normalize.D₂.comap (W.comap R.normalize.p).subschemeι) := by
  set R' := decompositionComap L₁ L₂ s R W with hR
  rw [← comap_branch₂_decompositionComap L₁ L₂ s R W, R'.zeroScheme₂]
  exact Stacks.Divisors.isEffectiveCartierDivisor_zeroScheme_of_tensorSection_right _ _ R'.s₁ R'.s₂
    (isEffectiveCartierDivisor_zeroScheme_tensorSection_decompositionComap L₁ L₂ s R W hWint hle)

end Stacks.Chow.TensorZeroScheme

end
