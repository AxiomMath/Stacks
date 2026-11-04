module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability
public import StacksFrontier.RingTheory.RegularRing.Defs

/-!
# Regular schemes, and the regular and singular loci

A scheme is regular, or nonsingular, when every point has an affine open neighbourhood whose
ring of sections is a regular Noetherian ring. Every regular scheme is normal. The regular locus
of a scheme consists of the points whose local rings are regular local rings, and the singular
locus is its complement.

## Main definitions

* `AlgebraicGeometry.IsRegular` is the predicate that a scheme is regular.
* `AlgebraicGeometry.regularLocus` is the set of points with regular local ring.
* `AlgebraicGeometry.singularLocus` is the complementary set of singular points.

## Main results

* `AlgebraicGeometry.isNormal_of_isRegular` states that a regular scheme is normal.

## Implementation notes

The affine neighbourhood is bundled as an element of `Scheme.affineOpens`. The source asks of
`𝒪_X(U)` that it be *Noetherian and regular*, and that conjunction is Mathlib's class
`IsRegularRing`: it extends `IsNoetherianRing`, and its further field is that the localization at
every prime is a regular local ring. Both halves of the source's requirement are therefore
written into `IsRegular`; `IsRegularRing.toIsNoetherian` reads the Noetherian one back off, so no
separate conjunct is needed here and no consumer needs a Noetherian hypothesis on a scheme it
already knows to be regular. The neighbourhoods of the definition cover, so a regular scheme is
locally Noetherian — `AlgebraicGeometry.isLocallyNoetherian_of_isRegular` — and the equivalence
with "locally Noetherian with regular local rings at every point" is Tag 02IT as
`AlgebraicGeometry.isRegular_tfae`. `IsRegular` is an abbreviation so clients can use its
pointwise characterization directly.

Both loci are abbreviations, so membership reduces directly to regularity, respectively
nonregularity, of the stalk. Although the source works with a locally Noetherian scheme, the
definitions make sense for every scheme; local Noetherian hypotheses belong on results which use
the loci.

## References

* [Stacks Project, Tag 02IS](https://stacks.math.columbia.edu/tag/02IS)
* [Stacks Project, Tag 0569](https://stacks.math.columbia.edu/tag/0569)
* [Stacks Project, Tag 07R1](https://stacks.math.columbia.edu/tag/07R1)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A scheme is regular, or nonsingular, if every point has an affine open neighbourhood whose
ring of sections is Noetherian and regular. -/
@[stacks 02IS "the source's requirement on `𝒪_X(U)`, Noetherian *and* regular, is Mathlib's
  class `IsRegularRing`: it extends `IsNoetherianRing`, and its further field is that the
  localization at every prime is a regular local ring. Both halves of the requirement are
  therefore written into this definition, the Noetherian one recoverable as
  `IsRegularRing.toIsNoetherian`; see the module docstring"]
public abbrev IsRegular (X : Scheme.{u}) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ U.val ∧ IsRegularRing Γ(X, U)

/-- **Stacks Project, Tag 0569.** Every regular scheme is normal. -/
@[stacks 0569 "a regular scheme is normal; the sole hypothesis is `IsRegular` of Tag 02IS, whose
  `IsRegularRing` already carries Noetherianness, so nothing beyond the source is assumed"]
public theorem isNormal_of_isRegular (X : Scheme.{u}) (hX : IsRegular X) :
    IsNormal X := by
  rw [isNormal_iff_stalk_normal]
  intro x
  obtain ⟨U, hxU, hreg⟩ := hX x
  let : IsRegularRing Γ(X, U) := hreg
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let p := (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal
  let : p.IsPrime := (U.2.primeIdealOf ⟨x, hxU⟩).isPrime
  let : IsLocalization.AtPrime (X.presheaf.stalk x) p := U.2.isLocalization_stalk ⟨x, hxU⟩
  let e : Localization.AtPrime p ≃+* X.presheaf.stalk x :=
    IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) (X.presheaf.stalk x)
  obtain ⟨hd, hc⟩ := main_theorem0567 Γ(X, U) p
  let : IsDomain (Localization.AtPrime p) := hd
  have : IsDomain (X.presheaf.stalk x) := Function.Injective.isDomain e.symm e.symm.injective
  exact ⟨inferInstance, @IsIntegrallyClosed.of_equiv _ _ _ _ e hc⟩

/-- The regular locus of a scheme: the points at which its local ring is regular. -/
@[stacks 07R1 "regular locus",
  ega "IV 6.12.1" "Reg(X)", ega "IV 7.3.12" "special case"]
public abbrev regularLocus (X : Scheme.{u}) : Set X :=
  {x | IsRegularLocalRing (X.presheaf.stalk x)}

/-- The singular locus of a scheme, the complement of its regular locus. -/
@[stacks 07R1 "singular locus",
  ega "IV 6.12.1" "Sing(X)"]
public abbrev singularLocus (X : Scheme.{u}) : Set X :=
  (regularLocus X)ᶜ

end AlgebraicGeometry

end
