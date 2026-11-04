module

public import StacksFrontier.AlgebraicGeometry.Flatness.Applications.FiniteLocallyFreeStrictTransform
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformFinitePresentationFromFlat
public import StacksFrontier.AlgebraicGeometry.Morphisms.PullbackRestrictTransport

/-!
# Making the strict transform of a proper scheme finite locally free, Stacks tag 0B49

Let `S` be a quasi-compact and quasi-separated scheme, let `f : X ⟶ S` be proper and let
`U ⊆ S` be a quasi-compact open over which `X` is finite locally free. Then there is a
`U`-admissible blowup of `S` along which the strict transform of `X` becomes finite locally free.

The flattening input of [Stacks, Tag 081R] is supplied by
`exists_isAdmissibleBlowup_flat_finitePresentation_strictTransform_of_affineCase`, whose two
hypotheses hold here: (1) `f` is of finite type, quasi-compact and quasi-separated because it is
proper, and (2) `f ∣_ U` is flat and locally of finite presentation because `X_U ⟶ U` is finite
locally free; the two readings of "`f` over `U`" agree by
`AlgebraicGeometry.prop_morphismRestrict_iff_pullback_snd`. The rest of the argument is
`AlgebraicGeometry.exists_isAdmissibleBlowup_isFiniteLocallyFree_strictTransform`.

## Main results

* `AlgebraicGeometry.exists_isAdmissibleBlowup_isFiniteLocallyFree_strictTransform_of_isProper`:
  **[Stacks, Tag 0B49]**, under exactly the source's hypotheses.

## References

* [Stacks Project, Tag 0B49](https://stacks.math.columbia.edu/tag/0B49)
* [Stacks Project, Tag 081R](https://stacks.math.columbia.edu/tag/081R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0B49.** Let `S` be a quasi-compact and quasi-separated scheme, let
`f : X ⟶ S` be proper and let `U ⊆ S` be a quasi-compact open over which `X` is finite locally
free. Then there is a `U`-admissible blowup of `S` along which the strict transform of `X` is
finite locally free. -/
@[stacks 0B49 "the conclusion in full, under exactly the source's hypotheses (1) and (2)"]
theorem exists_isAdmissibleBlowup_isFiniteLocallyFree_strictTransform_of_isProper
    {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] (f : X ⟶ S) [IsProper f]
    (U : S.Opens) (hU : IsCompact (U : Set S))
    [Stacks.Morphisms.IsFiniteLocallyFree (pullback.snd f U.ι)] :
    ∃ I : S.IdealSheafData,
      Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase I) ∧
        Stacks.Morphisms.IsFiniteLocallyFree (strictTransformToBlowUp f I) := by
  have hrFlat : MorphismProperty.RespectsIso @Flat :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hrLofp : MorphismProperty.RespectsIso @LocallyOfFinitePresentation :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hflfU :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      (pullback.snd f U.ι)).mp inferInstance
  -- the base change over `U` is the restriction of `f` to `U`, so `f ∣_ U` is flat and locally
  -- of finite presentation: hypothesis (2) of [Stacks, Tag 081R]
  -- the base change over `U` is the restriction of `f` to `U`, so `f ∣_ U` is flat and locally
  -- of finite presentation: hypothesis (2) of [Stacks, Tag 081R]
  have hflatU := (prop_morphismRestrict_iff_pullback_snd @Flat f U).mpr hflfU.2.1
  have hlofpU :=
    (prop_morphismRestrict_iff_pullback_snd @LocallyOfFinitePresentation f U).mpr hflfU.2.2
  obtain ⟨I, hIfp, hIdisj, -, hflat, hfp⟩ :=
    exists_isAdmissibleBlowup_flat_finitePresentation_strictTransform_of_affineCase f U hU
      hflatU hlofpU
  exact exists_isAdmissibleBlowup_isFiniteLocallyFree_strictTransform f U hU
    ⟨I, hIfp, hIdisj, hflat, hfp.locallyOfFinitePresentation⟩

end AlgebraicGeometry

end
