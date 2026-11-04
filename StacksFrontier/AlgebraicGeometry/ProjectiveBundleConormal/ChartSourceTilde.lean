module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartKernelTilde
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.RestrictTensor
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.Trivialize

/-!
# The source of the conormal map of Tag 0B3V clause 3, over a chart

The conormal map of [Stacks, Tag 0B3V] clause 3 goes out of
`ker(q) ⊗ 𝓛^{⊗ -1}`. Over an affine open `U` trivialising `𝓛` the twist drops
(`Stacks.ProjectiveBundleConormal.restrictSourceIso`) and what is left is `ker(q)|_U`, which
`Stacks.ProjectiveBundleConormal.restrictKernelIsoTilde` identifies with the quasi-coherent sheaf
attached to the kernel of the chart's linear form. **This file composes the two**, so that the
source of the clause's map is read on the chart as `(ker p)^~` in one step.

It also records the cover carrying all of the chart data at once, with the trivialisation of `𝓛`
**induced by the frame** rather than taken independently of it; the trivialisation is exactly what
`restrictSourceIso` consumes, so the combined form is stated here rather than reassembled by every
consumer.

## Main definitions

* `Stacks.ProjectiveBundleConormal.chartTrivialisation`: **the trivialisation of `𝓛|_U` induced by
  the chart data** — the one the image of the chart's section generates.
* `Stacks.ProjectiveBundleConormal.restrictConormalSourceIsoTilde`: **the source of clause 3's
  conormal map, restricted to a chart, is `(ker p)^~`.**

## Main results

* `Stacks.ProjectiveBundleConormal.exists_affine_open_chartData`: **the cover.** Around every
  point of `X` there is an affine open carrying a frame, a section at which the chart's linear
  form takes the value `1`, and a trivialisation of `𝓛` **which is the one that data induces.**

## Implementation notes

**The trivialisation is induced by the frame, and that is the whole point of the statement.** Taken
from `Stacks.ProjectiveBundleConormal.exists_affine_open_splitting`, which hands back a frame and
a trivialisation *with no relation between them*, it would leave a chart computation treating
`pairing(q s, θ⁻¹ 1)` as an unknown unit rather than as `1`, which is the obstruction `hpair` of
the "What is not done" of `StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartMeeting`. `Stacks.ProjectiveBundleConormal.restrictIsoUnitOfSpanEqTop` turns the
spanning section `q s` — spanning by
`Stacks.ProjectiveBundleConormal.span_singleton_app_eq_top_of_chartLinearForm_eq_one`, which is
the frame condition and nothing more — into a trivialisation, so the two are related by
construction and the cover statement can *pin* the trivialisation it returns. The frame of
`exists_affine_open_splitting` is therefore the only thing that statement is used for here,
through `exists_affine_open_chartLinearForm`.

The target of `restrictIsoUnitOfSpanEqTop` is `SheafOfModules.unit U.toScheme.ringCatSheaf`, and
that is the monoidal unit of
`Stacks.ProjectiveBundleConormal.monoidalSheafTensor` definitionally, so it is used at the `𝟙_ _`
spelling `restrictSourceIso` asks for with no unit comparison. This is the same ascription
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.Trivialize` makes, and for the same
reason.

Invertibility of `Q.L` is needed as an *instance* at the
`AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2` spelling, which is
the one `Stacks.ProjectiveBundleConormal.restrictSourceIso` and
`Stacks.ProjectiveBundleConormal.restrictIsoUnitOfSpanEqTop` are stated in;
`Stacks.Divisors.InvertibleQuotient.invertible` is already that statement, but it is a field and
not an instance, so it is registered below.

Both composites are a single `≪≫` of two named isomorphisms; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartKernelTilde` for why nothing here is
nested further.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

universe u

namespace Stacks.ProjectiveBundleConormal

attribute [local instance] monoidalSheafTensor

variable {X : Scheme.{u}} {E : X.Modules} (Q : Stacks.Divisors.InvertibleQuotient X E)

/-- **An invertible quotient is invertible**, as an instance at the spelling the conormal
material uses. `Stacks.Divisors.InvertibleQuotient.invertible` is already this statement, but it
is a structure field, so instance search does not see it. -/
instance isInvertible_quotient_algebraicGeometry :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 Q.L :=
  Q.invertible

/-! ### The trivialisation induced by the chart data -/

/-- **The trivialisation of `𝓛|_U` induced by the chart data.** On an affine open `U` carrying a
frame `e` for `𝓛` and a section `s` of `ℰ` whose linear form is `1`, the image `q s` spans
`Γ(𝓛, U)` (`Stacks.ProjectiveBundleConormal.span_singleton_app_eq_top_of_chartLinearForm_eq_one`)
and therefore trivialises `𝓛` there
(`Stacks.ProjectiveBundleConormal.restrictIsoUnitOfSpanEqTop`).

**This is the trivialisation a chart computation must be fed, and not an arbitrary one.** The
trivialisation enters clause 3 of [Stacks, Tag 0B3V] through
`Stacks.ProjectiveBundleConormal.restrictSourceIso`, which untwists the source of the conormal map
by the section `θ⁻¹(1)` of `𝓛^{⊗ -1}` it names; the source half of the chart computation then has
to pair that section against `q s`, and that pairing can only be `1` if the frame is the one the
trivialisation induces. Produced independently of the frame — as
`Stacks.ProjectiveBundleConormal.exists_affine_open_splitting` produces it — the pairing is only a
unit, and nothing can make it `1`. See the implementation notes of this file, and, for the two
section formulas that are *also* needed before the value `1` can be read off, item 2 of the "What
is not done" of `StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartMeeting`. -/
def chartTrivialisation {U : X.Opens} (hU : IsAffineOpen U)
    (e : Γ(Q.L, U) ≃ₗ[Γ(X, U)] Γ(X, U)) (s : Γ(E, U)) (hs : chartLinearForm Q U e s = 1) :
    (Scheme.Modules.restrictFunctor U.ι).obj Q.L ≅ 𝟙_ (↑U : Scheme.{u}).Modules :=
  restrictIsoUnitOfSpanEqTop Q.L U hU (Q.q.app U s)
    (span_singleton_app_eq_top_of_chartLinearForm_eq_one Q U e hs)

/-! ### The cover carrying the chart data -/

/-- **The cover carrying all of the chart data, with the trivialisation pinned.** Around every
point of `X` there is an affine open `U`, a frame `e` for `𝓛` on `U`, a section `s` of `ℰ` on `U`
at which the chart's linear form takes the value `1`, and a trivialisation of `𝓛|_U` **which is
the one that data induces**, `Stacks.ProjectiveBundleConormal.chartTrivialisation`.

The frame and the section are `Stacks.ProjectiveBundleConormal.exists_affine_open_chartLinearForm`
— ultimately `Stacks.ProjectiveBundleConormal.exists_affine_open_splitting` — read in the
vocabulary of `Stacks.ProjectiveBundleConormal.restrictConormalSourceIsoTilde`, through
`Stacks.ProjectiveBundleConormal.chartLinearForm`; the trivialisation is *not* the one that
statement produces, which is independent of the frame.

**The pin is the content.** It is what lets a consumer quantified over chart data assume the
relation between the frame and the trivialisation that the chart computation of clause 3 needs:
without it `pairing(q s, θ⁻¹ 1)` is an unknown unit for want of any relation at all, and no later
computation can recover the value `1`. The two reductions of clause 3
to a chart equation,
`Stacks.ProjectiveBundleConormal.isIso_conormalCanonicalMap_of_restrict_eq` and
`Stacks.ProjectiveBundleConormal.isIso_conormalCanonicalMap_of_restrict_eq_taut`, carry the
relation into their hypotheses for exactly that reason. -/
theorem exists_affine_open_chartData (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ (hU : IsAffineOpen U) (e : Γ(Q.L, U) ≃ₗ[Γ(X, U)] Γ(X, U))
      (s : Γ(E, U)) (hs : chartLinearForm Q U e s = 1)
      (τ : (Scheme.Modules.restrictFunctor U.ι).obj Q.L ≅ 𝟙_ (↑U : Scheme.{u}).Modules),
      τ = chartTrivialisation Q hU e s hs := by
  obtain ⟨U, hxU, hU, e, s, hs⟩ := exists_affine_open_chartLinearForm Q x
  exact ⟨U, hxU, hU, e, s, hs, chartTrivialisation Q hU e s hs, rfl⟩

/-! ### The source of the conormal map on a chart -/

variable [E.IsQuasicoherent] (U : X.Opens) (e : Γ(Q.L, U) ≃ₗ[Γ(X, U)] Γ(X, U))
  (hU : IsAffineOpen U)

/-- **The source of the conormal map of [Stacks, Tag 0B3V] clause 3, restricted to a chart, is
`(ker p)^~`.** The twist is trivial on `U` so it drops
(`Stacks.ProjectiveBundleConormal.restrictSourceIso`), and the kernel that is left is the sheaf
attached to the kernel of the chart's linear form
(`Stacks.ProjectiveBundleConormal.restrictKernelIsoTilde`).

This is the source half of the comparison that clause 3 asserts is an isomorphism; the target
half is the conormal sheaf of the zero section of `𝐀(ker p)`, computed by
`Stacks.ProjectiveBundleConormal.conormalZeroSectionIso`. -/
def restrictConormalSourceIsoTilde
    (τ : (Scheme.Modules.restrictFunctor U.ι).obj Q.L ≅ 𝟙_ (↑U : Scheme.{u}).Modules) :
    (Scheme.Modules.restrictFunctor U.ι).obj
        (kernel Q.q ⊗
          Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1)) ≅
      (Scheme.Modules.pullback hU.isoSpec.hom).obj (tilde (chartKerModule Q U e)) :=
  restrictSourceIso Q.L U (kernel Q.q) τ ≪≫ restrictKernelIsoTilde Q U e hU

end Stacks.ProjectiveBundleConormal

end
