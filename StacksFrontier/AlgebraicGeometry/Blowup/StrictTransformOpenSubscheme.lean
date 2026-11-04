module

public import StacksFrontier.AlgebraicGeometry.Blowup.DominatedByBlowup
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformIsoOverOpen
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.NagataInputs
public import StacksFrontier.AlgebraicGeometry.Flatness.ExtendingFromOpen.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformFinitePresentationFromFlat

/-!
# The strict transform becomes an open subscheme of the blowup

Let `f : X ⟶ S` be separated and of finite type, let `S` be quasi-compact and quasi-separated and
let `U ⊆ S` be a quasi-compact open over which `f` is an isomorphism. Then there is a
`U`-admissible blowup of `S` along which the strict transform of `X` is an open subscheme of the
blowup. This is [Stacks, Tag 081S], whose conclusion is
`AlgebraicGeometry.StrictTransformOpenImmersion`.

## Main results

* `AlgebraicGeometry.strictTransformOpenImmersion_of_flatteningCentre`: the statement with the
  *flatness* clause of [Stacks, Tag 081R] carried as a hypothesis.
* `AlgebraicGeometry.strictTransformOpenImmersion_of_affineCharts`: the conclusion of the tag, with
  `AlgebraicGeometry.AffineChartFlatteningCentre` — the affine case of the flatness half of
  [Stacks, Tag 0815] with that tag's hypotheses (2)-(5) deleted — as an extra input. No tag: that
  predicate is false in general.

[Stacks, Tag 081S] itself, under exactly the source's hypotheses, is derived from these results in
`StacksFrontier.AlgebraicGeometry.Flatness.Compactification.StrictTransformOpenSubscheme`.

## Implementation notes

The source's proof is: a first `U`-admissible blowup makes `S ∖ U` the support of an effective
Cartier divisor, so that `U` is scheme-theoretically dense; a second one ([Stacks, Tag 081R]) makes
the strict transform flat and of finite presentation; and then [Stacks, Tag 081M] — a flat,
separated morphism locally of finite type which is an isomorphism over a retrocompact
scheme-theoretically dense open is an open immersion — finishes.

Both blowups are inside the following theorem, in namespace `AlgebraicGeometry`:
`exists_isAdmissibleBlowup_flat_finitePresentation_support_eq_compl_of_flatteningCentre`, which
produces a single centre `ℐ` supported on *exactly* the complement of `U`. That support identity is
what replaces the source's first blowup: the exceptional ideal of a blowup is the inverse-image
ideal of the centre, so the inverse image `U'` of `U` in `Bl_ℐ(S)` is the complement of the
exceptional divisor (`AlgebraicGeometry.preimage_eq_compl_support_exceptionalIdeal`), hence
scheme-theoretically dense and retrocompact by [Stacks, Tag 07ZU].

That the strict transform is an isomorphism over `U'` is
`AlgebraicGeometry.isIso_strictTransformToBlowUp_morphismRestrict`: over `U'` the closed immersion
cutting out the strict transform inside the base change is an isomorphism, because the centre is
supported away from `U`, and the base change is an isomorphism over `U'` because `f` is one over
`U`.

## References

* [Stacks Project, Tag 081S](https://stacks.math.columbia.edu/tag/081S)
* [Stacks Project, Tag 081R](https://stacks.math.columbia.edu/tag/081R)
* [Stacks Project, Tag 081M](https://stacks.math.columbia.edu/tag/081M)
* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 07ZU](https://stacks.math.columbia.edu/tag/07ZU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A centre supported on exactly the complement of `U` has the inverse image of `U` as the
complement of its exceptional divisor.** The exceptional ideal is the inverse-image ideal sheaf of
the centre, so the support of the one is the inverse image of the support of the other. -/
theorem preimage_eq_compl_support_exceptionalIdeal {S : Scheme.{u}} (ℐ : S.IdealSheafData)
    (U : S.Opens) (h : (ℐ.support : Set S) = (U : Set S)ᶜ) :
    (blowUpToBase ℐ ⁻¹ᵁ U : (blowUp ℐ).Opens) = (exceptionalIdeal ℐ).support.compl := by
  have hs : ∀ y : blowUp ℐ, y ∈ ((exceptionalIdeal ℐ).support : Set (blowUp ℐ)) ↔
      (blowUpToBase ℐ) y ∈ (ℐ.support : Set S) := fun y ↦ by
    show y ∈ ((ℐ.comap (blowUpToBase ℐ)).support : Set (blowUp ℐ)) ↔ _
    simp
  refine Opens.ext (Set.ext fun x ↦ ?_)
  show (blowUpToBase ℐ) x ∈ U ↔ x ∉ ((exceptionalIdeal ℐ).support : Set (blowUp ℐ))
  rw [hs x, h]
  simp

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Stacks Project, Tag 081S**, with the flatness clause of [Stacks, Tag 081R] carried as a
hypothesis. Let `S` be a quasi-compact and quasi-separated scheme, let `f : X ⟶ S` be separated and
of finite type and let `U ⊆ S` be a quasi-compact open over which `f` is an isomorphism. Granted a
`U`-admissible centre whose strict transform is flat, there is a `U`-admissible centre along whose
blowup the strict transform of `X` is an open subscheme. -/
theorem strictTransformOpenImmersion_of_flatteningCentre [CompactSpace S] [QuasiSeparatedSpace S]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (U : S.Opens)
    (hU : IsCompact (U : Set S)) [IsIso (f ∣_ U)]
    (hflat : ∃ I : S.IdealSheafData, FinitePresentation I.subschemeι ∧
      Disjoint (U : Set S) (I.support : Set S) ∧ Flat (strictTransformToBlowUp f I)) :
    StrictTransformOpenImmersion f U := by
  obtain ⟨ℐ, hfp, hsupp, -, hflat', hfpst⟩ :=
    exists_isAdmissibleBlowup_flat_finitePresentation_support_eq_compl_of_flatteningCentre f U hU
      hflat
  have hdisj : Disjoint (U : Set S) (ℐ.support : Set S) := by
    rw [hsupp]
    exact disjoint_compl_right
  have hEV : (blowUpToBase ℐ ⁻¹ᵁ U : (blowUp ℐ).Opens) = (exceptionalIdeal ℐ).support.compl :=
    preimage_eq_compl_support_exceptionalIdeal ℐ U hsupp
  have hdense : Scheme.Opens.IsSchemeTheoreticallyDense (blowUpToBase ℐ ⁻¹ᵁ U) := by
    rw [hEV]
    exact Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor
      (exceptionalIdeal ℐ) inferInstance
  have hretro : IsRetrocompact ((blowUpToBase ℐ ⁻¹ᵁ U : (blowUp ℐ).Opens) : Set (blowUp ℐ)) := by
    have hqc : QuasiCompact (blowUpToBase ℐ ⁻¹ᵁ U).ι := by
      rw [hEV]
      infer_instance
    rw [IsRetrocompact_iff_isSpectralMap_subtypeVal]
    exact quasiCompact_iff_isSpectralMap.mp hqc
  have _ : Flat (strictTransformToBlowUp f ℐ) := hflat'
  have _ : IsSeparated (pullback.snd f (blowUpToBase ℐ)) := inferInstance
  have _ : IsSeparated (strictTransformToBlowUp f ℐ) := inferInstance
  have _ : IsIso (strictTransformToBlowUp f ℐ ∣_ (blowUpToBase ℐ ⁻¹ᵁ U)) :=
    isIso_strictTransformToBlowUp_morphismRestrict f ℐ U hdisj
  exact ⟨ℐ, hfp, hdisj,
    isOpenImmersion_of_isIso_morphismRestrict (strictTransformToBlowUp f ℐ)
      (blowUpToBase ℐ ⁻¹ᵁ U) hretro hdense⟩

/-- **Stacks Project, Tag 081S.** Let `f : X ⟶ S` be separated and of finite type with `S`
quasi-compact and quasi-separated, and let `U ⊆ S` be a quasi-compact open such that `f` is an
isomorphism over `U`. Then there is a `U`-admissible blowup of `S` along which the strict transform
of `X` is an open subscheme of the blowup.

The one hypothesis carried is `AlgebraicGeometry.AffineChartFlatteningCentre`, the affine case of
the flatness half of [Stacks, Tag 0815]; the flatness clause of [Stacks, Tag 081R] comes from it
through `AlgebraicGeometry.exists_isAdmissibleBlowup_flat_strictTransform`. No tag is attached
because that hypothesis, which omits the hypotheses (2)-(5) of [Stacks, Tag 0815], is false in
general. -/
theorem strictTransformOpenImmersion_of_affineCharts [CompactSpace S] [QuasiSeparatedSpace S]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (U : S.Opens)
    (hU : IsCompact (U : Set S)) [IsIso (f ∣_ U)]
    (H : AffineChartFlatteningCentre f X.unitModule U) :
    StrictTransformOpenImmersion f U :=
  strictTransformOpenImmersion_of_flatteningCentre f U hU
    (let ⟨I, hIfp, hIdisj, _, hIflat⟩ := exists_isAdmissibleBlowup_flat_strictTransform f U hU H
    ⟨I, hIfp, hIdisj, hIflat⟩)

end AlgebraicGeometry

end
