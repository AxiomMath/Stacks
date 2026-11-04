module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FrobeniusCohomologyIsogeny

/-!
# [Stacks, Tag 07N5] reduced to the first two arrows of its own proof

The proof of [Stacks, Tag 07N5] factors the canonical map

`F_E ∘ (F_X)^*_cris : RΓ(Cris(X/S), E) ⊗^L_{A, σ} A ⟶ RΓ(Cris(X/S), E)`

into three arrows, (07QC), (07N6) and the one induced by the Frobenius structure map `F_E`, and
shows each of the three becomes an isomorphism after inverting `p`.  The third of them is proved
in `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FrobeniusCohomologyIsogeny.lean` as
`becomesIsoAfterInvertingPrime_frobeniusCohomologyMap` of
`Crystalline.GlobalCrystallineSituation.SmallSite`.

This file measures what is left.  It names the composite of the *first two* arrows as a
proposition and proves that, together with the delimiter under which the third arrow is available
in this library, it is **equivalent** to
`Crystalline.GlobalCrystallineSituation.SmallSite.Statement07N5`
(`statement07N5_iff_baseChangeArrows07N5Isogeny`).  So the two remaining arrows are not merely
sufficient for the tag: they are exactly what is missing, and nothing has been traded away in
isolating them.

## The two propositions, and why they are two

`FrobeniusFactorsThroughCohomologyMap07N5` says that the carried map of `Statement07N5` factors
through `RΓ(Cris(X/S), (F_X)^*_cris E)` by the third arrow.  This is a statement about the
*construction* of the carried map, not about its being an isogeny; the source's own proof asserts
it, since `F_E ∘ (F_X)^*_cris` is by definition a composite whose last factor is the arrow induced
by `F_E`.  It is stated here rather than proved because `Statement07N5` quantifies over an
arbitrary choice of the map — no term of type
`Crystalline.GlobalCrystallineSituation.SmallSite.FrobeniusMap07N5` is constructed anywhere, for
the reason recorded in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FrobeniusInvertPrime.lean` — and for an
arbitrary choice there is nothing to factor.

`BaseChangeArrows07N5Isogeny` says that the first factor so exhibited becomes an isomorphism after
inverting `p`.  That is the content of the source's (07QC) and (07N6), and it is where the real
work is: (07QC) needs [Stacks, Tag 07MU] and [Stacks, Tag 07MY], and both arrows move the *site*
rather than the coefficients, which needs the action of a morphism of crystalline topoi on
module-valued cohomology.

Keeping the two apart is what makes the equivalence meaningful: the factorization is the shape of
the source's argument, and the isogeny is its substance.

## The delimiter

`BoundedCommonLocalRanks07N5` asks that every `F`-crystal of the situation have a bounded common
local rank, `Crystalline.FCrystal.HasBoundedCommonLocalRank`.  This is **not** a hypothesis of
[Stacks, Tag 07N5] and it is not introduced here; it is inherited from the third arrow.
`becomesIsoAfterInvertingPrime_frobeniusCohomologyMap` carries it because it is the exact
condition under which the two-sided identity of [Stacks, Tag 07N4] is available in this library —
see the "Where the two-sidedness comes from" section of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FrobeniusCohomologyIsogeny.lean` and
`Crystalline.FCrystal.hasBoundedCommonLocalRank_of_rankLE`, which records the one step from a mere
bound on the rank of `E` to a common local rank for `E` and its Frobenius pullback that the
library cannot take.  It is discharged for crystals of constant rank by
`Crystalline.FCrystal.hasBoundedCommonLocalRank_of_rank`.

It is a delimiter and not a weakening because it is not removable by anything in this file: the
third arrow's isogeny is used in both directions of the equivalence below, and that is the only
form of it the library has.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `BoundedCommonLocalRanks07N5` — every `F`-crystal of the situation has a bounded common local
  rank; the delimiter inherited from [Stacks, Tag 07N4].
* `FrobeniusFactorsThroughCohomologyMap07N5` — the carried map of `Statement07N5` factors through
  `RΓ(Cris(X/S), (F_X)^*_cris E)` by the third arrow of the source's proof.
* `BaseChangeArrows07N5Isogeny` — **the composite of the first two arrows of the proof of
  [Stacks, Tag 07N5] becomes an isomorphism after inverting `p`**; the source's (07QC) and (07N6)
  together.

## Main results

* `becomesIsoAfterInvertingPrime_iff_of_factors` — for a nondegenerate `F`-crystal with a bounded
  common local rank, the tag's map becomes an isomorphism after inverting `p` **if and only if**
  the first factor of any factorization of it through the third arrow does.  This is the
  measurement: the third arrow's isogeny cancels on the right.
* `statement07N5_of_baseChangeArrows07N5Isogeny` — **[Stacks, Tag 07N5] follows from the first two
  arrows of its proof and nothing else**, given the factorization and the delimiter.
* `statement07N5_iff_baseChangeArrows07N5Isogeny` — and conversely, so the reduction is lossless.

## What is and is not proved

**No `@[stacks 07N5]` attribute is placed in this file**; the tag is
`Crystalline.GlobalCrystallineSituation.SmallSite.statement07N5` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Frobenius07N5Theorem.lean`, which supplies
the two arrows isolated here over `X^{(1)}` and reads each against the source's own citation for
it.  Here `FrobeniusFactorsThroughCohomologyMap07N5` and `BaseChangeArrows07N5Isogeny` are
propositions taken as hypotheses, for an arbitrary map, and `Statement07N5` is itself a
proposition about a given map.  What is proved is the equivalence between the tag's conclusion and
the isogeny of the first two arrows.

Nothing here supplies the canonical map of the tag (that is
`...SmallSite.frobeniusMap07N5Canonical` of `SmallSite/FrobeniusDerivedGlobalSections.lean`, built
from the σ-semilinear Frobenius action `...SmallSite.frobeniusSigmaSemilinearAction`), nor
[Stacks, Tag 07MU], [Stacks, Tag 07MY] or [Stacks, Tag 07QC], which enter the proof of the tag
through `...SmallSite.isIso_baseChangeArrow07QC`.

## References

* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
* [Stacks Project, Tag 07N4](https://stacks.math.columbia.edu/tag/07N4)
* [Stacks Project, Tag 07QC](https://stacks.math.columbia.edu/tag/07QC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u wS wA wP

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

section IsogenyReduction

variable (T : Crystalline.FCrystalSituation.{u})

/-- **The delimiter inherited from [Stacks, Tag 07N4]**: every `F`-crystal of the situation has a
bounded common local rank.

This is the hypothesis of `becomesIsoAfterInvertingPrime_frobeniusCohomologyMap`, the third arrow
of the proof of [Stacks, Tag 07N5], read for every `F`-crystal at once.  It is not a hypothesis of
the tag; see the module docstring for why it cannot be removed here, and
`Crystalline.FCrystal.hasBoundedCommonLocalRank_of_rank` for the crystals that satisfy it
outright. -/
def BoundedCommonLocalRanks07N5 : Prop :=
  ∀ E : Crystalline.FCrystal T, ∃ rmax : ℕ, E.HasBoundedCommonLocalRank rmax

variable [HasDerivedCategory.{wS} (ModuleSheaf T.global)]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤))]
  [HasDerivedCategory.{wP} (ModuleCat.{u + 1} (invertPrimeRing T.global))]

/-- **The object `RΓ(Cris(X/S), (F_X)^*_cris E)` of `D(Mod_A)`** that the first two arrows of the
proof of [Stacks, Tag 07N5] land in and the third arrow starts from.

It is the source of `frobeniusCohomologyMap`, named so that the factorizations below can be read
without unfolding it. -/
abbrev frobeniusPullbackDerivedGlobalSections (E : Crystalline.FCrystal T) :
    DerivedCategory (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤)) :=
  (crisRestrictDerivedGlobalSections T.global).obj (T.frobeniusModulePullback.obj E.crystal)

/-- **The type of the composite of the first two arrows of the proof of [Stacks, Tag 07N5]**,
`RΓ(Cris(X/S), E) ⊗^L_{A, σ} A ⟶ RΓ(Cris(X/S), (F_X)^*_cris E)`: the source's (07QC) followed by
its (07N6).

No term of this type is constructed; the two arrows move the site rather than the coefficients. -/
abbrev BaseChangeArrows07N5 (E : Crystalline.FCrystal T) :=
  frobeniusDerivedBaseChangeTensorGlobalSections T (toSmallFCrystal E) ⟶
    frobeniusPullbackDerivedGlobalSections T E

/-- **The third arrow's isogeny cancels on the right.**

For a nondegenerate `F`-crystal with a bounded common local rank, and for any factorization
`ψ = φ ≫ F_E` of a map through the third arrow of the proof of [Stacks, Tag 07N5], the map `ψ`
becomes an isomorphism after inverting `p` exactly when `φ` does.

Forwards this is `BecomesIsoAfterInvertingPrime.of_comp_left`, backwards
`BecomesIsoAfterInvertingPrime.comp`; both use
`becomesIsoAfterInvertingPrime_frobeniusCohomologyMap`, which is why
`Crystalline.FCrystal.HasBoundedCommonLocalRank` appears on both sides and is a delimiter rather
than a weakening. -/
theorem becomesIsoAfterInvertingPrime_iff_of_factors (E : Crystalline.FCrystal T) {rmax : ℕ}
    (hrank : E.HasBoundedCommonLocalRank rmax) (hE : E.Nondegenerate)
    {ψ : FrobeniusMap07N5 T (toSmallFCrystal E)} {φ : BaseChangeArrows07N5 T E}
    (hfac : ψ = φ ≫ frobeniusCohomologyMap T E) :
    BecomesIsoAfterInvertingPrime T.global ψ ↔ BecomesIsoAfterInvertingPrime T.global φ := by
  have harrow : BecomesIsoAfterInvertingPrime T.global (frobeniusCohomologyMap T E) :=
    becomesIsoAfterInvertingPrime_frobeniusCohomologyMap T E hrank hE
  subst hfac
  exact ⟨fun h => h.of_comp_left T.global harrow, fun h => h.comp T.global harrow⟩

variable (frobeniusMap : ∀ E : Crystalline.FCrystal T, FrobeniusMap07N5 T (toSmallFCrystal E))

/-- **The carried map of [Stacks, Tag 07N5] factors through the third arrow of the source's
proof.**  For every nondegenerate `F`-crystal there is a map
`RΓ(Cris(X/S), E) ⊗^L_{A, σ} A ⟶ RΓ(Cris(X/S), (F_X)^*_cris E)` whose composite with
`frobeniusCohomologyMap` is the carried map.

This is the shape of the source's argument, and it is a proposition here only because
`Crystalline.GlobalCrystallineSituation.SmallSite.Statement07N5` quantifies over an arbitrary
choice of its map: for the canonical `F_E ∘ (F_X)^*_cris` the factorization holds by
construction, and for an arbitrary choice there is nothing to factor.  No assertion about
isogenies is made; that is `BaseChangeArrows07N5Isogeny`. -/
def FrobeniusFactorsThroughCohomologyMap07N5 : Prop :=
  ∀ E : Crystalline.FCrystal T, E.Nondegenerate →
    ∃ φ : BaseChangeArrows07N5 T E, frobeniusMap E = φ ≫ frobeniusCohomologyMap T E

/-- **The composite of the first two arrows of the proof of [Stacks, Tag 07N5] becomes an
isomorphism after inverting `p`**: the source's (07QC) and (07N6) together, read at any
factorization of the carried map through the third arrow.

The four hypotheses are the tag's own — `A` Noetherian and `p`-adically complete, `X ⟶ S₀` proper
and smooth — and they are present because the source's proof of these two arrows uses them:
(07QC) is where [Stacks, Tag 07MU] and [Stacks, Tag 07MY] enter, and those are the statements that
need properness and smoothness.  Carrying them here makes this proposition weaker and the
reduction below correspondingly stronger. -/
def BaseChangeArrows07N5Isogeny : Prop :=
  IsNoetherianRing ↥Γ(T.global.S.scheme, ⊤) →
    IsAdicComplete (Ideal.span {(T.global.p : Γ(T.global.S.scheme, ⊤))})
        ↥Γ(T.global.S.scheme, ⊤) →
      IsProper T.global.toClosedFiber → Smooth T.global.toClosedFiber →
        ∀ E : Crystalline.FCrystal T, E.Nondegenerate →
          ∀ φ : BaseChangeArrows07N5 T E, frobeniusMap E = φ ≫ frobeniusCohomologyMap T E →
            BecomesIsoAfterInvertingPrime T.global φ

/-- **[Stacks, Tag 07N5] follows from the first two arrows of its own proof, and from nothing
else.**

Given the delimiter `BoundedCommonLocalRanks07N5`, the factorization
`FrobeniusFactorsThroughCohomologyMap07N5` of the carried map through the third arrow, and
`BaseChangeArrows07N5Isogeny` — that the first factor becomes an isomorphism after inverting `p` —
the carried map becomes an isomorphism after inverting `p`, which is
`Crystalline.GlobalCrystallineSituation.SmallSite.Statement07N5`.

This is not a proof of the tag: all three inputs are propositions, and the module docstring says
what each of them stands for. -/
theorem statement07N5_of_baseChangeArrows07N5Isogeny
    (hrank : BoundedCommonLocalRanks07N5 T)
    (hfac : FrobeniusFactorsThroughCohomologyMap07N5 T frobeniusMap)
    (hiso : BaseChangeArrows07N5Isogeny T frobeniusMap) :
    Statement07N5 T frobeniusMap := by
  intro hnoeth hcomplete hproper hsmooth E hE
  obtain ⟨rmax, hr⟩ := hrank E
  obtain ⟨φ, hφ⟩ := hfac E hE
  exact (becomesIsoAfterInvertingPrime_iff_of_factors T E hr hE hφ).2
    (hiso hnoeth hcomplete hproper hsmooth E hE φ hφ)

/-- **The reduction of [Stacks, Tag 07N5] to the first two arrows of its proof is lossless.**

Given the delimiter and the factorization of the carried map through the third arrow, the tag's
conclusion and `BaseChangeArrows07N5Isogeny` are *equivalent*.  So the first two arrows are not
merely sufficient for [Stacks, Tag 07N5]: they are exactly what the library is missing, and
isolating them has traded nothing away.

The converse direction is `BecomesIsoAfterInvertingPrime.of_comp_left` applied through
`becomesIsoAfterInvertingPrime_iff_of_factors`; it is available precisely because the third arrow
is an isogeny and so cancels. -/
theorem statement07N5_iff_baseChangeArrows07N5Isogeny
    (hrank : BoundedCommonLocalRanks07N5 T)
    (hfac : FrobeniusFactorsThroughCohomologyMap07N5 T frobeniusMap) :
    Statement07N5 T frobeniusMap ↔ BaseChangeArrows07N5Isogeny T frobeniusMap := by
  refine ⟨fun h hnoeth hcomplete hproper hsmooth E hE φ hφ => ?_,
    statement07N5_of_baseChangeArrows07N5Isogeny T frobeniusMap hrank hfac⟩
  obtain ⟨rmax, hr⟩ := hrank E
  exact (becomesIsoAfterInvertingPrime_iff_of_factors T E hr hE hφ).1
    (h hnoeth hcomplete hproper hsmooth E hE)

end IsogenyReduction

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
