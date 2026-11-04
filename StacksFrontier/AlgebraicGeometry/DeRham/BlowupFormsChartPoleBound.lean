module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsChartFactor
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackVanishing

/-!
# The pole bound of Stacks 0G5G on a standard chart, read on sections

In the situation of `StacksFrontier.AlgebraicGeometry.DeRham.BlowupDifferentialFormsComparison` —
a ring `R`, `S = Spec(R)`, the coordinate closed immersion `Z = 𝐀^m_S ⟶ 𝐀^{m+n}_S = X`, the
blowup `b : L ⟶ X` of `X` along `Z` — the first canonical map of [Stacks, Tag 0G5G] is
`φ : b^*Ω^a_{X/S} ⟶ Ω^a_{L/S}` (`Stacks.DeRham.blowupFormsPullbackMap`), and
`Stacks.DeRham.exists_comp_pullback_blowupFormsPullbackMap` is the pole bound on the `i`-th
standard chart, as a factorisation of multiplication by `y_i^{n-1}` through the inverse image of
`φ` along that chart.

**This file reads that factorisation on sections.** Its deliverable is that over every open `W`
of `L` contained in the image of the `i`-th standard chart, the cokernel of `φ` kills
`y_i^{n-1} · s` for every section `s` of `Ω^a_{L/S}` over `W`, with `y_i^{n-1}` read as the
restriction to `W` of the global section `Stacks.DeRham.coordinateBlowupPoleSection` of `𝒪_L`
obtained by pulling `y_i^{n-1}` back along `b`.

## Main definitions

* `Stacks.DeRham.coordinateBlowupPoleSection`: the pullback along `b` of `y_i^{n-1}`, a global
  section of `𝒪_L`.

## Main results

* `Stacks.DeRham.cokernelπ_app_smul_poleSection_eq_zero`: **the pole bound on sections.**

## Implementation notes

All the sheaf theory is in
`Stacks.AlgebraicGeometry.Modules.cokernelπ_app_smul_eq_zero`, stated for a variable open
immersion and variable modules; this file only supplies the chart and its scalar. The reason it is
worth stating there is that the step is about *restriction* along the chart —
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` — rather than about inverse image: the sections
of a restriction over an open `V` of the chart are literally the sections of the module over the
image of `V`, whereas the sections of an inverse image are a sheafified tensor product. Against
the concrete modules here — inverse images of exterior powers of sheaves of relative
differentials — naming the comparison of those two functors and its inverse inside this file
costs the generalisation of the chart-level factorisation's own type; against variables it is
immediate.

The chart used in the factorisation is `j = g ≫ j_i` for an isomorphism `g` from affine space,
which has the same image as `j_i`
(`AlgebraicGeometry.Scheme.Hom.opensRange_comp_of_isIso`), so the hypothesis below mentions only
`j_i`.

No `@[stacks]` attribute is attached: this is one step inside the proof of the pole bound, not an
assertion of the tag.

## Which blowup this is

`Stacks.DeRham.coordinateBlowup` is `AlgebraicGeometry.blowUp`, and
`Stacks.DeRham.coordinateExceptional` is the **reducible**
`AlgebraicGeometry.exceptionalIdeal`. The library has a second constant
`Stacks.Blowup.exceptionalIdeal` with the same body, and two further blowup models
`Stacks.Blowup.blowUp` and `Stacks.Blowup.blowUpSpec` with no isomorphism to
`AlgebraicGeometry.blowUp`; nothing stated for those applies here.

## References

* [Stacks Project, Tag 0G5G](https://stacks.math.columbia.edu/tag/0G5G)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.Modules (cokernelπ_app_smul_eq_zero)

universe u

namespace Stacks.DeRham

variable (R : Type u) [CommRing R] (m n : ℕ) (i : Fin n)

/-- **The equation of `(n-1)E` on the standard charts, as a global section of `𝒪_L`:** the
pullback along the blowing-up morphism of the `(n-1)`-st power of the `i`-th of the last `n`
coordinates. -/
noncomputable abbrev coordinateBlowupPoleSection : Γ(coordinateBlowup R m n, ⊤) :=
  (coordinateBlowupToAmbient R m n).appTop (coordinateChartPoleSection R m n i)

/-- **The pole bound of [Stacks, Tag 0G5G] on the sections over the opens of a standard chart.**
Over an open `W` of `L` contained in the image of the `i`-th standard chart, the cokernel of the
first canonical map `φ : b^*Ω^a_{X/S} ⟶ Ω^a_{L/S}` kills `y_i^{n-1} · s` for every section `s` of
`Ω^a_{L/S}` over `W`, the scalar being the restriction to `W` of the pullback along `b` of
`y_i^{n-1}`.

This is `Stacks.DeRham.exists_comp_pullback_blowupFormsPullbackMap` fed to
`Stacks.AlgebraicGeometry.Modules.cokernelπ_app_smul_eq_zero`: the second clause of the former
says that the scalar of the chart-level factorisation is the pullback along the chart of the
global section of `𝒪_L` above, which is exactly the hypothesis of the latter. -/
theorem cokernelπ_app_smul_poleSection_eq_zero (a : ℕ) {W : (coordinateBlowup R m n).Opens}
    (hW : W ≤ (coordinateBlowupChartι R m n i).opensRange)
    (s : Γ(Scheme.Hom.relativeDifferentialForms (coordinateBlowupToBase R m n) (a : ℤ), W)) :
    (cokernel.π (blowupFormsPullbackMap R m n a)).app W
        ((coordinateBlowup R m n).presheaf.map W.leTop.op
          (coordinateBlowupPoleSection R m n i) • s) = 0 := by
  obtain ⟨g, hgiso, hpole, Θ, hΘ⟩ := exists_comp_pullback_blowupFormsPullbackMap R m n i a
  have := hgiso
  refine cokernelπ_app_smul_eq_zero (g ≫ coordinateBlowupChartι R m n i)
    (coordinateBlowupPoleSection R m n i) (blowupFormsPullbackMap R m n a) Θ ?_ ?_ s
  · rw [hpole]
    exact hΘ
  · rw [Scheme.Hom.opensRange_comp_of_isIso]
    exact hW

end Stacks.DeRham

end
