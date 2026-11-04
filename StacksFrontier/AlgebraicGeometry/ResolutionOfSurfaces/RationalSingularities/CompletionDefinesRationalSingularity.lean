module

public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformModule
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Independence
public import StacksFrontier.AlgebraicGeometry.Normalization.NormalizedBlowUpDescent
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.CompletionRationalSingularity
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LocalBirationalExtensions
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedModification
public import StacksFrontier.RingTheory.LocalCohomology.Deps.PuncturedSpectrumNonempty
public import StacksCore.Tactic.StacksAttribute

/-!
# Clause (1) of Tag 0BG7: the completion defines a rational singularity

Let `(A, 𝔪, κ)` be a local normal Nagata domain of dimension two defining a rational singularity
whose completion `A^` along `𝔪` is a normal domain. Then `A^` defines a rational singularity.

## Main definitions

* `AlgebraicGeometry.CompletionVanishingDescends` is the carried hypothesis standing for the two
  steps of the source's proof which this development lacks: flat base change for `H¹` along
  `A ⟶ A^` ([Stacks, Tag 02KH]) followed by the first conclusion of [Stacks, Tag 0AXF].

## Main results

* `AlgebraicGeometry.definesRationalSingularity_adicCompletion_maximalIdeal`: clause (1) of
  [Stacks, Tag 0BG7], under the hypothesis `AlgebraicGeometry.CompletionVanishingDescends` and
  [Stacks, Tag 081S] for modifications of `Spec(A^)`.  Both clauses of [Stacks, Tag 0BG7] at the
  source's hypotheses, with nothing carried, are
  `AlgebraicGeometry.definesRationalSingularity_adicCompletion_and_isNormalDomain_stalk_blowUp`
  in `StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowupStillGood`.

## Implementation notes

The source's proof of clause (1) takes a normal modification `q : Y ⟶ Spec(A^)` and produces
`H¹(Y, 𝒪_Y) = 0` in four steps: a `U`-admissible blowup `f : X ⟶ Spec(A)` whose base change
along `Spec(A^) ⟶ Spec(A)` dominates `Y`; the replacement of `X` by its normalization, after
which `X^ν ⟶ Spec(A)` is a *normal* modification and the rational singularity of `A` kills
`H¹(X^ν, 𝒪)`; flat base change along `A ⟶ A^`, which carries that vanishing to
`X^ν ×_{Spec(A)} Spec(A^)`; and [Stacks, Tag 0AXF], whose Leray sequence injects `H¹(Y, 𝒪_Y)`
into it.

The first step is
`AlgebraicGeometry.exists_isAdmissibleBlowup_isPullback_dominating_adicCompletion`, under
[Stacks, Tag 081S], and the second is `AlgebraicGeometry.isModification_normalization_comp`. The
last two are bundled into the single hypothesis `AlgebraicGeometry.CompletionVanishingDescends`,
in the shape of `AlgebraicGeometry.SpreadOutVanishingDescends` for the analogous pair of steps
over a local ring. They are bundled rather than taken separately for the following reasons.

* Flat base change for `H¹` is [Stacks, Tag 02KH], available as
  `Stacks.AlgebraicGeometry.FlatBaseChangeDerived.cohomologyBaseChangeIso`. That is stated for
  the right derived functors of module-valued global sections, whereas
  `AlgebraicGeometry.DefinesRationalSingularity` is stated for Mathlib's
  `CategoryTheory.Sheaf.H`. The two models are compared by
  `AlgebraicGeometry.isZeroFirstStructureSheafCohomology_iff_isZero_rightDerived` and
  `AlgebraicGeometry.subsingleton_firstCohomologyAsBaseModule_iff`, which relate
  `AlgebraicGeometry.IsZeroFirstStructureSheafCohomology` to the module-valued model and to
  `AlgebraicGeometry.firstCohomologyAsBaseModule` in both directions, and by
  `AlgebraicGeometry.isZeroFirstStructureSheafCohomology_iff_isZero_firstCohomologyStructureSheaf`
  against the `ℤ`-indexed derived functor in which `cohomologyBaseChangeIso` is stated.
  Instantiating that base-change isomorphism at `Spec(A^) ⟶ Spec(A)` needs its flatness and
  quasi-compactness hypotheses discharged for the completion map and for the normalized
  modification.
* The first conclusion of [Stacks, Tag 0AXF] rests, for its right-hand exactness, on
  [Stacks, Tag 02V7] in fibre dimension one and hence on [Stacks, Tags 02OD and 02O5]. The form
  `AlgebraicGeometry.LerayFirstCohomologyExact` asks for both schemes to be normal, where the tag
  asks only for the lower one, and clause (1) applies it to `X^ν ×_{Spec(A)} Spec(A^)`, whose
  normality does not follow, `A` being Nagata rather than excellent, so that `A ⟶ A^` need not be
  regular.
* [Stacks, Tag 0AXF] requires the upper morphism to be a modification, so the bundle also
  absorbs the fact that `X^ν ×_{Spec(A)} Spec(A^) ⟶ Spec(A^)` is one. There is no base-change
  stability lemma for `AlgebraicGeometry.IsModification`, nor for
  `AlgebraicGeometry.IsBirational`, and `isIntegral_pullback_of_flat_of_isIso_morphismRestrict`
  takes reducedness of the pullback as a hypothesis, which
  `AlgebraicGeometry.isRegular_pullback_completion_iff` supplies only for a *regular* source,
  whereas `X^ν` is normal and need not be regular.

## References

* [Stacks Project, Tag 0BG7](https://stacks.math.columbia.edu/tag/0BG7)
* [Stacks Project, Tag 0AXF](https://stacks.math.columbia.edu/tag/0AXF)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 081S](https://stacks.math.columbia.edu/tag/081S)
* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-! ### The carried hypothesis: flat base change followed by the Leray injection -/

/-- **A carried hypothesis: [Stacks, Tag 02KH] for `H¹` along `A ⟶ A^`, followed by the first
conclusion of [Stacks, Tag 0AXF].** Let `f : X ⟶ Spec(A)` be a modification with `X` normal and
let `q : Y ⟶ Spec(A^)` be a modification with `Y` normal. If the base change `Z` of `f` along
`Spec(A^) ⟶ Spec(A)` dominates `Y` over `Spec(A^)`, then vanishing of the first cohomology of
`𝒪_X` forces vanishing of the first cohomology of `𝒪_Y`.

Flat base change carries the vanishing from `X` to `Z`, and the Leray sequence of
[Stacks, Tag 0AXF] injects `H¹(Y, 𝒪_Y)` into `H¹(Z, 𝒪_Z)`. See the module documentation for why
the two steps are carried together and why
`AlgebraicGeometry.LerayFirstCohomologyExact` does not serve in their place. -/
public def CompletionVanishingDescends (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsDomain (AdicCompletion (maximalIdeal A) A)] : Prop :=
  ∀ ⦃X Y Z : Scheme.{u}⦄ (f : X ⟶ Spec (.of A))
      (q : Y ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A)))
      (c : Z ⟶ X) (b : Z ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A))) (g : Z ⟶ Y),
    IsNormal X → IsModification f → IsNormal Y → IsModification q →
      IsPullback c b f (specMapAdicCompletion A) → g ≫ q = b →
        IsZeroFirstStructureSheafCohomology X → IsZeroFirstStructureSheafCohomology Y

/-! ### Admissible blowups of the spectrum of a local domain of positive dimension -/

/-- The punctured spectrum of a local ring of positive Krull dimension is nonempty, as a set of
points of the spectrum. -/
public theorem nonempty_coe_puncturedSpectrum (A : Type u) [CommRing A] [IsLocalRing A]
    (hdim : 1 ≤ ringKrullDim A) :
    (Stacks.puncturedSpectrum A : Set (Spec (.of A))).Nonempty :=
  Set.nonempty_coe_sort.mp
    ((Stacks.Divisors.nonempty_puncturedSpectrum_iff_one_le_ringKrullDim A).mpr hdim)

/-- **An admissible blowup of the spectrum of a local domain of positive dimension is a
modification.** It is proper, and over a nonempty open its centre misses it is birational with
integral source. -/
public theorem isModification_of_isAdmissibleBlowup_puncturedSpectrum (A : Type u) [CommRing A]
    [IsLocalRing A] [IsDomain A] (hdim : 1 ≤ ringKrullDim A) {X : Scheme.{u}}
    {f : X ⟶ Spec (.of A)}
    (hadm : Stacks.Blowup.IsAdmissibleBlowup (Stacks.puncturedSpectrum A) f) :
    IsModification f :=
  have hU := nonempty_coe_puncturedSpectrum A hdim
  ⟨hadm.isBirational hU, hadm.isProper, hadm.isIntegral hU⟩

/-! ### Clause (1) of Tag 0BG7 -/

/-- **[Stacks, Tag 0BG7], clause (1).** Let `(A, 𝔪, κ)` be a local normal Nagata domain of
dimension two which defines a rational singularity and whose completion `A^` along `𝔪` is a
normal domain. Then `A^` defines a rational singularity.

Given a normal modification `q : Y ⟶ Spec(A^)`,
`AlgebraicGeometry.exists_isAdmissibleBlowup_isPullback_dominating_adicCompletion` produces an
admissible blowup `f : X ⟶ Spec(A)` whose base change along `Spec(A^) ⟶ Spec(A)` dominates `Y`;
`AlgebraicGeometry.isModification_normalization_comp` replaces `X` by its normalization, a
normal modification of `Spec(A)`, so that the rational singularity of `A` kills the first
cohomology of its structure sheaf; and the carried
`AlgebraicGeometry.CompletionVanishingDescends` transports that vanishing across the base change
and down the domination to `Y`.

The hypothesis `h081S` is [Stacks, Tag 081S], which the dominating-blowup step already carries;
`hdescend` is flat base change for `H¹` together with the first conclusion of
[Stacks, Tag 0AXF]. See the module documentation. -/
public theorem definesRationalSingularity_adicCompletion_maximalIdeal (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNormalDomain A] [IsNormalDomain (AdicCompletion (maximalIdeal A) A)]
    (hNagata : IsNagataRing A) (hdim : ringKrullDim A = 2)
    (hrat : DefinesRationalSingularity A)
    (h081S : ∀ ⦃Y : Scheme.{u}⦄ (q : Y ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A))),
      IsModification q →
        StrictTransformOpenImmersion q
          (Stacks.puncturedSpectrum (AdicCompletion (maximalIdeal A) A)))
    (hdescend : CompletionVanishingDescends.{u} A) :
    DefinesRationalSingularity (AdicCompletion (maximalIdeal A) A) := by
  have hNoeth : IsNoetherianRing A := hNagata.1
  rw [definesRationalSingularity_iff]
  intro Y hY q hq
  obtain ⟨X, Y', f, c, b, g, hadm, hsq, hg⟩ :=
    exists_isAdmissibleBlowup_isPullback_dominating_adicCompletion A hdim q hq (h081S q hq)
  have hfmod : IsModification f :=
    isModification_of_isAdmissibleBlowup_puncturedSpectrum A (by rw [hdim]; exact one_le_two) hadm
  have hXint : IsIntegral X := hfmod.source_isIntegral
  have hfproper : IsProper f := hfmod.isProper
  have hfin := Stacks.AlgebraicGeometry.Normalization.finite_irreducibleComponents_of_isNagataScheme
    X (isNagataScheme_of_locallyOfFiniteType f (isNagataScheme_spec_of_isNagataRing A hNagata))
  have hXnu : IsNormal (X.normalizationScheme hfin) := Scheme.isNormal_normalizationScheme X hfin
  have hnumod : IsModification (X.normalization hfin ≫ f) :=
    isModification_normalization_comp A hNagata f hfmod hfin
  let d : (pullback (X.normalization hfin ≫ f) (specMapAdicCompletion A) : Scheme.{u}) ⟶ Y' :=
    hsq.lift (pullback.fst _ _ ≫ X.normalization hfin) (pullback.snd _ _)
      (by rw [Category.assoc, pullback.condition])
  have hcomm : (d ≫ g) ≫ q =
      pullback.snd (X.normalization hfin ≫ f) (specMapAdicCompletion A) := by
    rw [Category.assoc, hg, hsq.lift_snd]
  exact hdescend (X.normalization hfin ≫ f) q _ _ (d ≫ g)
    hXnu hnumod hY hq (IsPullback.of_hasPullback _ _) hcomm (hrat _ _ hnumod)

end AlgebraicGeometry

end
