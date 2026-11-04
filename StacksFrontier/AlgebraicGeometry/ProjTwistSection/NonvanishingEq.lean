module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.SectionGenerator
public import StacksFrontier.AlgebraicGeometry.ProjTwistSection.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The nonvanishing locus of `f / 1` *is* `D₊(f)`, when `Proj 𝒮` is covered by degree-one opens

`StacksFrontier/AlgebraicGeometry/ProjTwistSection/Basic.lean` proves one containment: the
canonical section `f / 1` of `𝒪_{Proj 𝒮}(1)` attached to `f ∈ 𝒮 1` is nonvanishing on the standard
open `D₊(f)`. This file proves the reverse containment, hence the **equality**
`(Proj 𝒮)_{f/1} = D₊(f)`, under the hypothesis that every point of `Proj 𝒮` lies in `D₊(g)` for
some `g ∈ 𝒮 1`.

The argument at a point `x` with a degree-one `g ∉ x` is the source's: on the open
`V = (Proj 𝒮)_{f/1} ⊓ D₊(g)` the section `f / 1` *generates* `𝒪(1)` — that is what nonvanishing
means, by `Stacks.SheafOfModules.bijective_smul_of_subset_nonvanishingLocus` — so some
`r ∈ Γ(V, 𝒪)` carries it to the [Stacks, Tag 01MS] trivializing section `g / 1`. Reading that
equation in the fibre at `x`, which for these sheaves is literally the localization of `S` at the
homogeneous prime `x`, gives `r(x) · (f / 1) = g / 1` there; the right-hand side is a unit because
`g ∉ x`, so `f / 1` is a unit of that localization, so `f ∉ x`.

## Main results

* `Stacks.ProjTwistSection.mem_basicOpen_of_mem_nonvanishingOpen_homogeneousSection`: the
  pointwise statement, with the degree-one element `g` at `x` given.
* `Stacks.ProjTwistSection.nonvanishingOpen_homogeneousSection_le_basicOpen`: the containment
  missing from `Basic.lean`.
* `Stacks.ProjTwistSection.nonvanishingOpen_homogeneousSection_eq_basicOpen`: **the equality.**

## Implementation notes

The degree-one covering hypothesis is **not** removable, and the counterexample is small, so it
is recorded here rather than guessed at by the next reader. It is *not* formalized; it is a
reason not to try to drop the hypothesis. Take `S = k[u, v]` with `deg u = 1`, `deg v = 2`, and
`f = u`. Then `𝒪(1)` is invertible: on `D₊(u)` the degree-one part of `S_u` is `u · S₍u₎`, and on
`D₊(v)` it is `u · S₍v₎` with `S₍v₎ = k[u²/v]`, so `𝒪(1)` is free of rank one on `u` over both
charts of a cover. But the prime `(u)` is a point of `Proj S` — it is homogeneous, prime, and does
not contain `v`, hence not the irrelevant ideal — and it lies in `D₊(v)`, where `u / 1` is that
very frame. So `u / 1` is nonvanishing at `(u) ∉ D₊(u)`, and the containment proved here fails
there. What the hypothesis rules out is exactly this: `(u)` is covered by no `D₊(g)` with
`g ∈ S_1`, since `S_1 = k · u`. The hypothesis is the source's own, and appears verbatim in
[Stacks, Tag 01MT] ("Assume `X` is covered by the standard opens `D₊(f)` with `f ∈ S_1`") and as
the `d = 1` case of the open `U_d` of [Stacks, Tag 01N5].

No `@[stacks ...]` attribute is attached. The equality is used inside the proofs of the source's
Tag 01N8 and Tag 01NE but is not the statement of any tag, and these statements carry a
hypothesis — the degree-one covering — that no tag of this neighbourhood carries alone.

The invertibility of `𝒪(1)` is an instance hypothesis rather than a derived fact, for the same
reason as in `basicOpen_le_nonvanishingOpen_homogeneousSection`: the available route
(`Stacks.AlgebraicGeometry.ProjDegreeOne.isInvertible_twistingSheaf`) needs `𝒮` generated in
degree one over `𝒮 0`, which is a hypothesis on `𝒮` and not on `f`.

Two spellings are load-bearing. The fibre of the twisting sheaf at
`x` is `LocalizedModule x.primeCompl S`, which is the *same type* as the local ring
`Localization x.primeCompl` in which the structure sheaf's sections take their values, with the
module action being ring multiplication; both coincidences are `rfl` at this pin and are recorded
in the implementation notes of `StacksFrontier/AlgebraicGeometry/ProjTrivialization/Basic.lean`.
That is what lets the equation of sections be read at `x` as an equation of the shape
`ρ * Localization.mk f 1 = …` with no transport. The degree is spelled `1 * ((1 : ℕ) : ℤ)` on the
trivialization's side and `((1 : ℕ) : ℤ)` on the section's side; those are the same numeral after
evaluation, so no cast appears.

## References

* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 01MT](https://stacks.math.columbia.edu/tag/01MT)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTrivialization

universe u

namespace Stacks.ProjTwistSection

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
    (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The ideal underlying a point of `ProjectiveSpectrum 𝒮` is prime. -/
local instance (x : ProjectiveSpectrum.top 𝒮) : x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

variable [Stacks.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj 𝒮).presheaf
    (structureSheafRing (AlgebraicGeometry.Proj
      𝒮).toRingedSpace).property
    (twistingModule 𝒮 1)]

/-- **If `f / 1` is nonvanishing at a point of a degree-one standard open, then that point lies
in `D₊(f)`.** On the intersection of the nonvanishing locus with `D₊(g)` the section `f / 1`
generates `𝒪(1)`, so it carries some function to the trivializing section `g / 1`; in the
localization at `x` that exhibits `f / 1` as a divisor of a unit. -/
@[ega "II 3.3.3" "(f)"]
theorem mem_basicOpen_of_mem_nonvanishingOpen_homogeneousSection
    (f : S) (hf : f ∈ 𝒮 1) {g : S} (hg : g ∈ 𝒮 1)
    (x : ProjectiveSpectrum.top 𝒮) (hxg : x ∈ ProjectiveSpectrum.basicOpen 𝒮 g)
    (hx : x ∈ Stacks.SheafOfModules.nonvanishingOpen
      (X := (AlgebraicGeometry.Proj 𝒮).toRingedSpace) (twistingModule 𝒮 1)
      (homogeneousSection 𝒮 f hf)) :
    x ∈ ProjectiveSpectrum.basicOpen 𝒮 f := by
  set L := twistingModule 𝒮 1 with hL
  set s := homogeneousSection 𝒮 f hf with hs
  set V := Stacks.SheafOfModules.nonvanishingOpen
      (X := (AlgebraicGeometry.Proj 𝒮).toRingedSpace) L s ⊓ ProjectiveSpectrum.basicOpen 𝒮 g
    with hV
  have hxV : x ∈ V := ⟨hx, hxg⟩
  have hVg : V ≤ ProjectiveSpectrum.basicOpen 𝒮 g := inf_le_right
  obtain ⟨r, hr⟩ := (Stacks.SheafOfModules.bijective_smul_of_subset_nonvanishingLocus
    L s V (fun y hy => hy.1)).2 (trivializingSection 𝒮 hg 1 hVg)
  have key := congrArg Subtype.val hr
  have key2 : HomogeneousLocalization.val (r.1 ⟨x, hxV⟩) *
      Localization.mk f (1 : x.asHomogeneousIdeal.toIdeal.primeCompl)
      = trivializingFun 𝒮 1 hVg ⟨x, hxV⟩ := congrFun key ⟨x, hxV⟩
  have hunit : IsUnit (trivializingFun 𝒮 1 hVg ⟨x, hxV⟩) := isUnit_trivializingFun 𝒮 1 hVg _
  rw [← key2] at hunit
  have hf1 : IsUnit (Localization.mk f (1 : x.asHomogeneousIdeal.toIdeal.primeCompl)) :=
    isUnit_of_mul_isUnit_right hunit
  rw [Localization.mk_eq_mk'] at hf1
  exact (IsLocalization.AtPrime.isUnit_mk'_iff _ x.asHomogeneousIdeal.toIdeal f 1).mp hf1

/-- **The nonvanishing locus of `f / 1` is contained in `D₊(f)`**, for `f ∈ 𝒮 1`, as soon as
`Proj 𝒮` is covered by the standard opens of degree-one elements. -/
@[ega "II 3.3.3" "(f)"]
theorem nonvanishingOpen_homogeneousSection_le_basicOpen (f : S) (hf : f ∈ 𝒮 1)
    (hcov : ∀ x : ProjectiveSpectrum.top 𝒮,
      ∃ g : S, g ∈ 𝒮 1 ∧ x ∈ ProjectiveSpectrum.basicOpen 𝒮 g) :
    Stacks.SheafOfModules.nonvanishingOpen (X := (AlgebraicGeometry.Proj 𝒮).toRingedSpace)
        (twistingModule 𝒮 1) (homogeneousSection 𝒮 f hf)
      ≤ ProjectiveSpectrum.basicOpen 𝒮 f := by
  intro x hx
  obtain ⟨g, hg, hxg⟩ := hcov x
  exact mem_basicOpen_of_mem_nonvanishingOpen_homogeneousSection 𝒮 f hf hg x hxg hx

/-- **The nonvanishing locus of the canonical section of `𝒪(1)` attached to a degree-one element
`f` is exactly the standard open `D₊(f)`**, as soon as `Proj 𝒮` is covered by the standard opens
of degree-one elements. One containment is
`basicOpen_le_nonvanishingOpen_homogeneousSection` and needs no hypothesis on `𝒮`; the other is
`nonvanishingOpen_homogeneousSection_le_basicOpen`. -/
@[ega "II 2.6.3" "Degree d = 1", ega "II 3.3.3" "special case"]
theorem nonvanishingOpen_homogeneousSection_eq_basicOpen (f : S) (hf : f ∈ 𝒮 1)
    (hcov : ∀ x : ProjectiveSpectrum.top 𝒮,
      ∃ g : S, g ∈ 𝒮 1 ∧ x ∈ ProjectiveSpectrum.basicOpen 𝒮 g) :
    Stacks.SheafOfModules.nonvanishingOpen (X := (AlgebraicGeometry.Proj 𝒮).toRingedSpace)
        (twistingModule 𝒮 1) (homogeneousSection 𝒮 f hf)
      = ProjectiveSpectrum.basicOpen 𝒮 f :=
  le_antisymm (nonvanishingOpen_homogeneousSection_le_basicOpen 𝒮 f hf hcov)
    (basicOpen_le_nonvanishingOpen_homogeneousSection 𝒮 f hf)

end Stacks.ProjTwistSection

end
