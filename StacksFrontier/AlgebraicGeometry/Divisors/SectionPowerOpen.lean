module

public import StacksFrontier.AlgebraicGeometry.Divisors.NonvanishingLocusRestrict
public import StacksFrontier.AlgebraicGeometry.TensorSectionPower.Basic

/-!
# Powers of a section over an open, and the affineness of its nonvanishing locus

Let `X` be a scheme, `N` an invertible `𝒪_X`-module and `U` an open of `X`. This file supplies
two facts about a section `s` of `N` over `U`:

1. **nonvanishing is unchanged by passing to a power**, `U_{s ^ m} = U_s` for `m ≥ 1`, where the
   power is `Stacks.TensorSectionPower.secPow` and the nonvanishing locus over `U` is
   `Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn`. This is the second of the two facts
   `StacksFrontier/AlgebraicGeometry/PullbackExtension/Basic.lean` lists as needed for part (1) of
   [Stacks, Tag 0892], where it is what lets an argument available
   only for the exponents dividing some fixed `m₀` be run at every exponent: the power may now be
   taken on the open the section lives on rather than only globally.
2. **the nonvanishing locus over `U` is an open of `X`, and its affineness is the affineness of
   the nonvanishing locus upstairs**, on the open subscheme `U.toScheme` where ampleness produces
   it.

The first item is stated for its own sake and for Tag 0892: the general case of
[Stacks, Tag 0AYM](https://stacks.math.columbia.edu/tag/0AYM), in
`StacksFrontier/AlgebraicGeometry/Divisors/InvertibleSheafGeneral.lean`, turns out not to need it —
`Stacks.ModuleSectionExtension.exists_tensorPow_tensorSection_of_isAmple` returns the denominator
as a *global* section of a tensor power together with the equality of nonvanishing opens on the
nose, so the power that the source takes over `X_s` is already global there and no divisibility
condition survives. See that file's implementation notes.

## The powers themselves are already there

`Stacks.TensorSectionPower.secPow` is the `(k+1)`-st power of a section over an **arbitrary**
open, formed with `Stacks.SectionTensorFormula.tensorSection`, and
`Stacks.TensorSectionPower.map_secPow` is its compatibility with restriction. What was missing is
only its nonvanishing locus: `Stacks.TensorSectionPower.nonvanishingLocus_secPow` is stated for
`U = ⊤`, because `Stacks.Ample.nonvanishingLocus` takes a global section.
`Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn` removes that restriction, and the engine
of the global statement — `Stacks.TensorSectionProduct.germ_tensorSection_notMem_maximalSmul_iff`,
the Tag 01CY remark `U_{m ⊗ n} = U_m ∩ U_n` at the germ — is already stated over an arbitrary
open. So the induction of `nonvanishingLocus_secPow` goes through verbatim over `U`, and nothing
about powers has to be redone.

Indexing follows `secPow`: `secPow M u k` is the `(k+1)`-st power, so the hypothesis `m ≠ 0` of
the informal statement is carried by the indexing rather than by a side condition.

## Transport of affineness along the open immersion is Mathlib's

The general case of Tag 0AYM knows an open of `U.toScheme` to be affine — it is produced there,
by ampleness — and needs the corresponding open of `X` to be affine.
`AlgebraicGeometry.Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion` is exactly that, for an
arbitrary open immersion and in both directions, with
`AlgebraicGeometry.IsAffineOpen.image_of_isOpenImmersion` and
`AlgebraicGeometry.IsAffineOpen.preimage_of_isOpenImmersion` as its two halves. Nothing about
affineness is reproved here; what is proved is the *identification* that lets it be applied,
namely that the open of `X` underlying `nonvanishingLocusOn N U s` is the image along `U.ι` of
the nonvanishing open of the corresponding global section on `U.toScheme`
(`Stacks.SectionPowerOpen.nonvanishingOpenOn_eq_image`).

## Main definitions

* `Stacks.SectionPowerOpen.nonvanishingOpenOn`: the nonvanishing locus of a section over an open,
  bundled as an open subset of `X`.

## Main results

* `Stacks.SectionPowerOpen.nonvanishingLocusOn_secPow`: **`U_{s ^ (k+1)} = U_s`**, the
  nonvanishing locus over an open of a power of a section of an invertible module.
* `Stacks.SectionPowerOpen.mem_nonvanishingLocusOn_secPow_iff`: the same pointwise, at a point
  already known to lie in `U`.
* `Stacks.SectionPowerOpen.isOpen_nonvanishingLocusOn`: **the nonvanishing locus of a section
  over an open is open**, the analogue over `U` of
  `Stacks.NonvanishingOpen.isOpen_nonvanishingLocus` ([Stacks, Tag 01CY], openness). It is the
  image under the open embedding `U.ι` of the nonvanishing locus upstairs.
* `Stacks.SectionPowerOpen.nonvanishingOpenOn_eq_image`: `U_s` is the image along `U.ι` of the
  nonvanishing open of `Stacks.NonvanishingLocusRestrict.restrictSection U N s`.
* `Stacks.SectionPowerOpen.isAffineOpen_nonvanishingOpenOn_iff`: **`U_s` is affine exactly when
  the nonvanishing open upstairs is**, which is the direction in which ampleness on `U.toScheme`
  is consumed.
* `Stacks.SectionPowerOpen.nonvanishingOpenOn_secPow`: the power law in the bundled shape, an
  equality of opens of `X`.

## Implementation notes

**Invertibility is the `Stacks.Ample.IsInvertibleModule` spelling.** That is the one the power
and tensor-product machinery takes as an instance binder; the other class realising
[Stacks, Tag 01CS] is bridged to it by
`Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible`. Invertibility
of the pullback `U.ι^* N`, needed to bundle the nonvanishing locus upstairs as an open, is
[Stacks, Tag 0B8L] (`Stacks.InvertiblePullback.isInvertibleModule_restrict`), an instance.

**The monoidal structure on `X.Modules` is reintroduced with local instances.** It is transported
along the sheafification localization and its pieces are declared as local instances in their
origin files, so a fresh file does not find them by instance search; the attribute block below is
the same one `StacksFrontier/AlgebraicGeometry/TensorSectionPower/Basic.lean` carries.

## No Stacks attribute is attached

Nothing here is an assertion of a numbered source item. The power law over an open is the
bookkeeping that [Stacks, Tag 01CY]'s remark `X_{st} = X_s ∩ X_t` already supplies at the germ,
and the affineness transport is Mathlib's.

## References

* [Stacks Project, Tag 0AYM](https://stacks.math.columbia.edu/tag/0AYM)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.Ample
open Stacks.NonvanishingLocusRestrict (nonvanishingLocusOn mem_nonvanishingLocusOn_iff
  nonvanishingLocusOn_subset restrictSection nonvanishingLocus_restrictSection)
open Stacks.TensorSectionPower (powObj secPow)

universe u

namespace Stacks.SectionPowerOpen

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj

variable {X : Scheme.{u}}

/-! ### The nonvanishing locus of a power of a section over an open -/

section Power

variable (M : X.Modules) [IsInvertibleModule X M] {U : X.Opens}

/-- **A power of a section does not vanish where the section does not**, pointwise and over an
arbitrary open. At a point `y` of `U`, the germ of the `(k+1)`-st power of `u` generates the
stalk of `M ^⊗ (k+1)` exactly when the germ of `u` generates the stalk of `M`: the remark
`U_{m ⊗ n} = U_m ∩ U_n` of [Stacks, Tag 01CY]
(`Stacks.TensorSectionProduct.germ_tensorSection_notMem_maximalSmul_iff`) with both factors
powers of the same section, so that the intersection collapses. -/
theorem mem_nonvanishingLocusOn_secPow_iff (u : Γ(M, U)) (k : ℕ) {y : X} (hy : y ∈ U) :
    y ∈ nonvanishingLocusOn (powObj M k) U (secPow M u k) ↔ y ∈ nonvanishingLocusOn M U u := by
  induction k with
  | zero => exact Iff.rfl
  | succ k ih =>
      refine Iff.trans (mem_nonvanishingLocusOn_iff (powObj M (k + 1)) U hy) ?_
      refine Iff.trans
        (Stacks.TensorSectionProduct.germ_tensorSection_notMem_maximalSmul_iff
          (secPow M u k) u hy) ?_
      exact Iff.trans
        (and_congr (Iff.trans (mem_nonvanishingLocusOn_iff (powObj M k) U hy).symm ih)
          (mem_nonvanishingLocusOn_iff M U hy).symm)
        and_self_iff

/-- **`U_{s ^ (k+1)} = U_s`**: the nonvanishing locus over an open `U` of the `(k+1)`-st power of
a section of an invertible module is the nonvanishing locus of the section itself. This is
`Stacks.TensorSectionPower.nonvanishingLocus_secPow` with the global open `⊤` replaced by an
arbitrary `U`. -/
theorem nonvanishingLocusOn_secPow (u : Γ(M, U)) (k : ℕ) :
    nonvanishingLocusOn (powObj M k) U (secPow M u k) = nonvanishingLocusOn M U u :=
  Set.ext fun _ =>
    ⟨fun h => (mem_nonvanishingLocusOn_secPow_iff M u k h.1).mp h,
      fun h => (mem_nonvanishingLocusOn_secPow_iff M u k h.1).mpr h⟩

end Power

/-! ### The nonvanishing locus over an open is open -/

section Open

variable (N : X.Modules) [IsInvertibleModule X N] (U : X.Opens)

omit [IsInvertibleModule X N] in
/-- The nonvanishing locus over `U` of a section `s` of `N` is the image along `U.ι` of the
nonvanishing locus on `U.toScheme` of the global section of `U.ι^* N` corresponding to `s`.
`Stacks.NonvanishingLocusRestrict.nonvanishingLocus_restrictSection` identifies the latter with
the preimage, and taking the image back recovers the set because it is contained in `U`, which is
the range of `U.ι`. -/
theorem image_nonvanishingLocus_restrictSection (s : Γ(N, U)) :
    U.ι.base '' Stacks.Ample.nonvanishingLocus
        (Stacks.AmpleLocallyClosed.pullbackModule U.ι N) (restrictSection U N s) =
      nonvanishingLocusOn N U s := by
  rw [nonvanishingLocus_restrictSection, Set.image_preimage_eq_inter_range,
    Scheme.Opens.range_ι]
  exact Set.inter_eq_self_of_subset_left (nonvanishingLocusOn_subset N U s)

/-- **The nonvanishing locus of a section over an open is an open subset of `X`**: the analogue
over `U` of the openness clause of [Stacks, Tag 01CY]
(`Stacks.NonvanishingOpen.isOpen_nonvanishingLocus`). It is the image of an open subset of
`U.toScheme` under the open embedding `U.ι`. -/
theorem isOpen_nonvanishingLocusOn (s : Γ(N, U)) : IsOpen (nonvanishingLocusOn N U s) := by
  rw [← image_nonvanishingLocus_restrictSection N U s]
  exact U.ι.isOpenEmbedding.isOpenMap _
    (Stacks.NonvanishingOpen.isOpen_nonvanishingLocus U.toScheme
      (Stacks.AmpleLocallyClosed.pullbackModule U.ι N) (restrictSection U N s))

/-- **The nonvanishing locus of a section over an open, bundled as an open of `X`.** At `U = ⊤`
this is `Stacks.NonvanishingOpen.nonvanishingOpen`. -/
def nonvanishingOpenOn (s : Γ(N, U)) : X.Opens :=
  ⟨nonvanishingLocusOn N U s, isOpen_nonvanishingLocusOn N U s⟩

/-- The underlying set of `nonvanishingOpenOn N U s` is `nonvanishingLocusOn N U s`. -/
@[simp]
theorem coe_nonvanishingOpenOn (s : Γ(N, U)) :
    (nonvanishingOpenOn N U s : Set X) = nonvanishingLocusOn N U s := rfl

/-- The nonvanishing open of a section over `U` is contained in `U`. -/
theorem nonvanishingOpenOn_le (s : Γ(N, U)) : nonvanishingOpenOn N U s ≤ U :=
  nonvanishingLocusOn_subset N U s

/-- **`U_s` is the image along `U.ι` of the nonvanishing open upstairs.** This is the
identification that makes the affineness transport of
`AlgebraicGeometry.Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion` applicable to `U_s`. -/
theorem nonvanishingOpenOn_eq_image (s : Γ(N, U)) :
    nonvanishingOpenOn N U s =
      U.ι ''ᵁ Stacks.NonvanishingOpen.nonvanishingOpen U.toScheme
        (Stacks.AmpleLocallyClosed.pullbackModule U.ι N) (restrictSection U N s) :=
  Opens.ext (by
    rw [coe_nonvanishingOpenOn, Scheme.Hom.coe_image, ← image_nonvanishingLocus_restrictSection,
      Stacks.NonvanishingOpen.coe_nonvanishingOpen])

/-- **Transport of affineness across the open immersion `U.ι`, at the nonvanishing opens.** The
nonvanishing locus over `U` of a section `s` of `N` is an affine open of `X` exactly when the
nonvanishing open on `U.toScheme` of the corresponding global section of `U.ι^* N` is an affine
open of `U.toScheme`.

The affineness transport itself is Mathlib's
`AlgebraicGeometry.Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion`; what is supplied here is the
identification of the two opens. The direction used by the general case of [Stacks, Tag 0AYM] is
`mpr`: ampleness of `U.ι^* L` produces the affine open upstairs, and the divisor is cut out
downstairs. -/
theorem isAffineOpen_nonvanishingOpenOn_iff (s : Γ(N, U)) :
    IsAffineOpen (nonvanishingOpenOn N U s) ↔
      IsAffineOpen (Stacks.NonvanishingOpen.nonvanishingOpen U.toScheme
        (Stacks.AmpleLocallyClosed.pullbackModule U.ι N) (restrictSection U N s)) := by
  rw [nonvanishingOpenOn_eq_image]
  exact U.ι.isAffineOpen_iff_of_isOpenImmersion

end Open

/-! ### The power law in the bundled shape -/

/-- **`U_{s ^ (k+1)} = U_s` as an equality of opens of `X`.** -/
theorem nonvanishingOpenOn_secPow (M : X.Modules) [IsInvertibleModule X M] {U : X.Opens}
    (u : Γ(M, U)) (k : ℕ) :
    nonvanishingOpenOn (powObj M k) U (secPow M u k) = nonvanishingOpenOn M U u :=
  Opens.ext (nonvanishingLocusOn_secPow M u k)

end Stacks.SectionPowerOpen

end
