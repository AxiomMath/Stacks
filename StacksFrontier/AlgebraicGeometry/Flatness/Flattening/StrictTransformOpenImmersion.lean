module

public import StacksFrontier.AlgebraicGeometry.Blowup.DominatedByBlowup
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.StrictTransformOpenSubscheme
public import StacksFrontier.AlgebraicGeometry.Flatness.ExtendingFromOpen.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.AffineChartFlatteningFromInduction
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.ModuleFlatteningBlowup
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformSchemeFlattening
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.DominatingBlowup

/-!
# Modifications dominated by admissible blowups

Let `S` be a quasi-compact and quasi-separated scheme, let `f : X ⟶ S` be proper and locally of
finite presentation, and let `U ⊆ S` be a quasi-compact open over which `f` is an isomorphism.
Then there is a `U`-admissible blowup `S' ⟶ S` which dominates `X`. In particular, in an
`AlgebraicGeometry.VanishingSituation` the modification is dominated by an admissible blowup of
the punctured spectrum.

## Main results

* `AlgebraicGeometry.isIso_ker_subschemeι_morphismRestrict`: the scheme-theoretic closure of an
  open `W` is `W` again over `W`.
* `AlgebraicGeometry.isIso_strictTransformToBlowUp_morphismRestrict_of_exceptionalComplement_eq`:
  over the complement of the exceptional divisor the strict transform is an isomorphism.
* `AlgebraicGeometry.exists_isAdmissibleBlowup_dominating_of_locallyOfFinitePresentation`: a
  proper morphism, locally of finite presentation, which is an isomorphism over a quasi-compact
  open `U`, is dominated by a `U`-admissible blowup.
* `AlgebraicGeometry.VanishingSituation.exists_isAdmissibleBlowup_dominating_of_noetherian`:
  [Stacks, Tag 0B4M], the modification of Situation [Stacks, Tag 0AX8] is dominated by an
  admissible blowup of the punctured spectrum.

## References

* [Stacks Project, Tag 081S](https://stacks.math.columbia.edu/tag/081S)
* [Stacks Project, Tag 081T](https://stacks.math.columbia.edu/tag/081T)
* [Stacks Project, Tag 0B4M](https://stacks.math.columbia.edu/tag/0B4M)
* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
* [Stacks Project, Tag 080Y](https://stacks.math.columbia.edu/tag/080Y)
* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 081M](https://stacks.math.columbia.edu/tag/081M)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The scheme-theoretic closure of an open, over that open -/

/-- **The closed subscheme cut out by the kernel of the inclusion of an open `W` is `W` again
over `W`.** -/
theorem isIso_ker_subschemeι_morphismRestrict {T : Scheme.{u}} (W : T.Opens) :
    IsIso (W.ι.ker.subschemeι ∣_ W) := by
  set ι := W.ι.ker.subschemeι with hι
  have hrange : Set.range W.ι.toImage ⊆ Set.range (ι ⁻¹ᵁ W).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change ι (W.ι.toImage x) ∈ W
    rw [← Scheme.Hom.comp_apply, hι, Scheme.Hom.toImage_imageι]
    exact x.2
  let t : W.toScheme ⟶ (ι ⁻¹ᵁ W).toScheme := IsOpenImmersion.lift (ι ⁻¹ᵁ W).ι W.ι.toImage hrange
  have ht : t ≫ (ι ⁻¹ᵁ W).ι = W.ι.toImage := IsOpenImmersion.lift_fac _ _ _
  have h₁ : t ≫ (ι ∣_ W) = 𝟙 _ := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, ht, hι,
      Scheme.Hom.toImage_imageι, Category.id_comp]
  have h₂ : (ι ∣_ W) ≫ t = 𝟙 _ := by
    rw [← cancel_mono ((ι ⁻¹ᵁ W).ι ≫ ι), Category.assoc, ← Category.assoc t, ht, hι,
      Scheme.Hom.toImage_imageι, Category.id_comp, ← hι, morphismRestrict_ι]
  exact ⟨t, h₂, h₁⟩

variable {X S : Scheme.{u}}

/-- **Over the complement of the exceptional divisor the strict transform is an isomorphism.**
If `f` is an isomorphism over `U` and the inverse image of `U` in the blowup of `S` in `K` is the
complement of the exceptional divisor, then the strict transform of `X` is an isomorphism over that
complement. -/
theorem isIso_strictTransformToBlowUp_morphismRestrict_of_exceptionalComplement_eq (f : X ⟶ S)
    (K : S.IdealSheafData)
    (U : S.Opens) [IsIso (f ∣_ U)]
    (hUK : (exceptionalIdeal K).support.compl = blowUpToBase K ⁻¹ᵁ U) :
    IsIso (strictTransformToBlowUp f K ∣_ (exceptionalIdeal K).support.compl) := by
  have h₁ : IsIso ((Stacks.StrictTransform.ideal f (blowUpToBase K) (exceptionalIdeal K)).subschemeι
      ∣_ Stacks.StrictTransform.exceptionalComplement f (blowUpToBase K) (exceptionalIdeal K)) := by
    rw [Stacks.StrictTransform.ideal_eq_ker_ι]
    exact isIso_ker_subschemeι_morphismRestrict _
  have h₂ : IsIso (pullback.snd f (blowUpToBase K) ∣_ (exceptionalIdeal K).support.compl) := by
    rw [hUK]
    have h := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f (blowUpToBase K))
      (US := U) (UT := blowUpToBase K ⁻¹ᵁ U) (UX := f ⁻¹ᵁ U) le_rfl le_rfl
      (UY := pullback.snd f (blowUpToBase K) ⁻¹ᵁ (blowUpToBase K ⁻¹ᵁ U)) (by
        rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition,
          inf_idem])
    have hU' : IsIso (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
      rw [Scheme.Hom.resLE_eq_morphismRestrict]
      infer_instance
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
      (MorphismProperty.isomorphisms Scheme).of_isPullback h hU'
  rw [strictTransformToBlowUp, morphismRestrict_comp]
  exact IsIso.comp_isIso' h₁ h₂

/-! ### Dominating admissible blowups -/

/-- A proper morphism `f : X ⟶ S`, locally of finite presentation, to a quasi-compact and
quasi-separated scheme, which is an isomorphism over a quasi-compact open `U`, is dominated by a
`U`-admissible blowup. -/
theorem exists_isAdmissibleBlowup_dominating_of_locallyOfFinitePresentation [CompactSpace S]
    [QuasiSeparatedSpace S] (f : X ⟶ S) [IsProper f] [LocallyOfFinitePresentation f]
    (U : S.Opens) (hU : IsCompact (U : Set S)) [IsIso (f ∣_ U)] :
    ∃ (S' : Scheme.{u}) (b : S' ⟶ S),
      Stacks.Blowup.IsAdmissibleBlowup U b ∧ ∃ g : S' ⟶ X, g ≫ f = b :=
  exists_isAdmissibleBlowup_dominating_of_isCompact f U hU
    (strictTransformOpenImmersion_of_isIso_morphismRestrict f U hU)

/-! ### The vanishing situation -/

namespace VanishingSituation

/-- In Situation [Stacks, Tag 0AX8] the conclusion of [Stacks, Tag 081S] holds for the
modification `f` and the punctured spectrum `U = S ∖ {s}`: there is a `U`-admissible blowup of
`S` in which the strict transform of `X` is an open subscheme. The modification is proper and an
isomorphism over `U` (`isIso_morphismRestrict_puncturedSpectrumOpen`), and `U` is quasi-compact
because `S = Spec(A)` is Noetherian. -/
theorem strictTransformOpenImmersion (V : VanishingSituation.{u}) :
    StrictTransformOpenImmersion V.f V.puncturedSpectrumOpen := by
  have : IsIso (V.f ∣_ V.puncturedSpectrumOpen) := V.isIso_morphismRestrict_puncturedSpectrumOpen
  have : IsProper V.f := V.modification.isProper
  have hnoeth : NoetherianSpace V.base := inferInstanceAs (NoetherianSpace (PrimeSpectrum V.A))
  exact strictTransformOpenImmersion_of_isIso_morphismRestrict V.f V.puncturedSpectrumOpen
    (NoetherianSpace.isCompact _)

/-- **Stacks Project, Tag 0B4M.** In Situation [Stacks, Tag 0AX8] — `A` a Noetherian normal
local domain of dimension two, `S = Spec(A)`, `U = S ∖ {s}` its punctured spectrum and
`f : X ⟶ S` a modification — there is a `U`-admissible blowup `b : S' ⟶ S` which dominates `X`:
it factors as `S' ⟶ X ⟶ S`.

As in the source this is the case of [Stacks, Tag 081T] at `f`. Both results 081T cites are
proved here for this situation: [Stacks, Tag 080Y] by `AlgebraicGeometry.cartierBoundaryReduction`
and [Stacks, Tag 081S] by `strictTransformOpenImmersion`. The hypothesis of the source's
discussion that the special fibre has positive dimension is not needed. -/
@[stacks 0B4M "the full statement in Situation 0AX8: the inputs 080Y and 081S of 081T are \
proved, by `cartierBoundaryReduction` and `VanishingSituation.strictTransformOpenImmersion`"]
theorem exists_isAdmissibleBlowup_dominating_of_noetherian (V : VanishingSituation.{u}) :
    ∃ (S' : Scheme.{u}) (b : S' ⟶ V.base),
      Stacks.Blowup.IsAdmissibleBlowup V.puncturedSpectrumOpen b ∧
        ∃ g : S' ⟶ V.X, g ≫ V.f = b := by
  have hnoeth : NoetherianSpace V.base := inferInstanceAs (NoetherianSpace (PrimeSpectrum V.A))
  exact V.exists_isAdmissibleBlowup_dominating
    (cartierBoundaryReduction V.puncturedSpectrumOpen (NoetherianSpace.isCompact _))
    V.strictTransformOpenImmersion

end VanishingSituation

end AlgebraicGeometry

end
