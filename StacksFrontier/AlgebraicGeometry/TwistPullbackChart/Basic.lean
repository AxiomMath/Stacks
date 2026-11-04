module

public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Basic
public import StacksFrontier.AlgebraicGeometry.TwistPullbackChart.Chart

/-!
# The twist half of Stacks Tag 01NE is an absolute statement

`Stacks.AmpleImmersionReduction.TwistPullback f` — the first of the four named inputs of
[Stacks, Tag 01VS] — is stated about a morphism `p : X ⟶ ℙⁿ_S` lying over `S`. This file removes
the base: it reduces that condition to the same assertion about a morphism
`g : X ⟶ ℙⁿ_ℤ` to the integral model, with no base scheme and no clause over `S`.

## What the reduction consumes

The clause `p ≫ pr₁ = f` — "`p` lies over `S`" — is used exactly once, through
`Stacks.AmpleProjectiveImmersion.liftOver_eq`: a morphism to `ℙⁿ_S` lying over `S` *is* the lift
of the pair `(f, p ≫ pr₂)`, so `p` is determined by the morphism `g := p ≫ pr₂` to the integral
model. The hyperplane sheaf of `ℙⁿ_S` is by definition the pullback of the integral model's, so
`Stacks.AmpleProjectiveImmersion.liftOverTwistIso` identifies `p ^* 𝒪(1)` on `ℙⁿ_S` with
`g ^* 𝒪(1)` on `ℙⁿ_ℤ` by pseudofunctoriality. The pinning clause transfers verbatim, because it
is already written about `p ≫ projectiveSpaceOver.toIntegralAtUniverse n S`.

Nothing else is consumed: no ampleness, no finite type hypothesis, no immersion and no degree.

## Why this is worth separating

The absolute form is the one the remaining mathematics is stated at. `g ^* 𝒪(1)` is trivialized
on each chart `X_{sᵢ}` by `Stacks.TwistPullbackChart.pullbackTwistRestrictIsoUnitChart`, whose
statement names only the integral model, and the transition-cocycle comparison that
`TwistPullback` still owes (see the companion file's "What is not done") is likewise a statement
about `ℙⁿ_ℤ`. Carrying `S` through it would add the `liftOver` bookkeeping to every step.

## Main definitions

* `Stacks.TwistPullbackChart.TwistPullbackAtUniverse`: the twist half of [Stacks, Tag 01NE] for a
  morphism to the integral model of projective space.

## Main results

* `Stacks.TwistPullbackChart.twistPullback_of_atUniverse`:
  **`Stacks.AmpleImmersionReduction.TwistPullback f` for every `f : X ⟶ S`, from the absolute
  form.** Unconditional in the base.

## What is not done

`Stacks.TwistPullbackChart.TwistPullbackAtUniverse` is **not** proved; see the companion file
`StacksFrontier/AlgebraicGeometry/TwistPullbackChart/Chart.lean` for the `𝒪(1)` half of it that
is, and for the exact proposition that remains.

**No Stacks tag attribute is attached.** Tag 01NE is a representability statement and nothing
here is one of its assertions; Tag 01VS is not proved, three of its four named inputs being
untouched by this file.

## References

* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Ample Stacks.ProjectiveFromSections Stacks.AmpleProjectiveImmersion
open Stacks.SectionsToProjectiveSpace

universe u

namespace Stacks.TwistPullbackChart

/-- **The twist half of [Stacks, Tag 01NE], at the integral model.** A morphism
`g : X ⟶ ℙⁿ_ℤ` restricting on each chart `X_{sᵢ}` to the morphism of the ratio family `sₖ/sᵢ`
attached to a generating family `s` of global sections of an invertible `M` pulls the hyperplane
sheaf back to `M`.

This is `Stacks.AmpleImmersionReduction.TwistPullback` with the base scheme removed. It mentions
no base, no structure morphism and no clause over `S`. -/
def TwistPullbackAtUniverse : Prop :=
  ∀ {X : Scheme.{u}} (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M] (n : ℕ)
    (s : Fin (n + 1) → Γ(M, ⊤)), GeneratesStalks s →
      ∀ g : X ⟶ projectiveSpaceAtUniverse.{u} n,
        (∀ i, (nvCover s i).ι ≫ g =
          toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i)) →
          Nonempty (M ≅ (Scheme.Modules.pullback g).obj (twistingSheafAtUniverse n))

/-- **`Stacks.AmpleImmersionReduction.TwistPullback f` for every `f : X ⟶ S`, from the absolute
form.**

The morphism to the integral model is `g := p ≫ projectiveSpaceOver.toIntegralAtUniverse n S`;
`Stacks.AmpleProjectiveImmersion.liftOver_eq` recovers `p` from it using the clause that `p` lies
over `S`, and `Stacks.AmpleProjectiveImmersion.liftOverTwistIso` identifies the two pullbacks of
the hyperplane sheaf. The pinning clause is transferred unchanged. -/
theorem twistPullback_of_atUniverse (h : TwistPullbackAtUniverse.{u}) {X S : Scheme.{u}}
    (f : X ⟶ S) : Stacks.AmpleImmersionReduction.TwistPullback f := by
  intro M _ n s hgen p hpf hchart
  obtain ⟨e⟩ := h M n s hgen (p ≫ projectiveSpaceOver.toIntegralAtUniverse n S) hchart
  have hp : liftOver f (p ≫ projectiveSpaceOver.toIntegralAtUniverse n S) = p :=
    liftOver_eq f p hpf
  exact ⟨e ≪≫ (liftOverTwistIso f (p ≫ projectiveSpaceOver.toIntegralAtUniverse n S)).symm ≪≫
    eqToIso (by rw [hp])⟩

end Stacks.TwistPullbackChart

end
