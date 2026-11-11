module

public import StacksFrontier.AlgebraicGeometry.Blowup.CompositeCentre
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformSchemeFlattening
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Bijective
import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierComplement
import StacksFrontier.AlgebraicGeometry.Divisors.LocallyPrincipalComplementAffine
import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.FiniteTypeIdealSheaf
import StacksFrontier.AlgebraicGeometry.Flatness.ExtendingFromOpen.Finite
import StacksFrontier.AlgebraicGeometry.Properties.FiniteTypeIdealSheafOfOpen
import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.DenseOpen
import StacksFrontier.AlgebraicGeometry.StrictTransform.CompositionScheme

/-!
# Making the strict transform of a proper scheme finite locally free

Let `S` be a quasi-compact and quasi-separated scheme, let `f : X ⟶ S` be proper and let
`U ⊆ S` be a quasi-compact open over which `X` is finite locally free. Then there is a
`U`-admissible blowup of `S` along which the strict transform of `X` becomes finite locally free.

The construction follows the source. Flattening ([Stacks, Tag 081R]) produces a centre `I`,
finitely presented and supported away from `U`, whose strict transform `X₁ ⟶ S₁ = Bl_I(S)` is
flat and locally of finite presentation. The complement of `U` is the support of a centre `J` of
finite type, and the composite centre `I · J` is the one asserted: by [Stacks, Tag 080B] the
blowup of `S` in `I · J` is the blowup of `S₁` in `Z = J·𝒪_{S₁}` followed by `S₁ ⟶ S`, and by
[Stacks, Tag 080I] part (2) the strict transform of `X` along `Bl_{I·J}(S) ⟶ S` is the strict
transform of `X₁` along `Bl_Z(S₁) ⟶ S₁`. The latter is the whole base change, `X₁` being flat
([Stacks, Tag 080F] part (1)), hence proper and flat over `Bl_Z(S₁)`; it is finite over the
inverse image of `U`, which is the complement of the exceptional divisor of the second blowup and
so topologically dense ([Stacks, Tag 07ZU]); hence it is finite ([Stacks, Tag 0B48]) and
therefore finite locally free ([Stacks, Tag 02KB]).

## Main results

* `AlgebraicGeometry.isFinite_morphismRestrict_pullback_snd_preimage`: a base change which is
  finite over an open of the base stays finite over the inverse image of that open.
* `AlgebraicGeometry.isFinite_pullback_snd_of_isFinite_morphismRestrict`: finiteness of the
  restriction of a morphism to an open of the target is finiteness of the corresponding base
  change.
* `AlgebraicGeometry.exists_isAdmissibleBlowup_isFiniteLocallyFree_strictTransform`: the
  argument of [Stacks, Tag 0B49] from a flattening centre for `f` and `U` onwards. Tag 0B49
  itself, with the flattening centre supplied by [Stacks, Tag 081R], is
  `AlgebraicGeometry.exists_isAdmissibleBlowup_isFiniteLocallyFree_strictTransform_of_isProper`
  in `StacksFrontier.AlgebraicGeometry.Flatness.Applications.FiniteLocallyFreeStrictTransformOfProper`.

## Implementation notes

The blowup used is `AlgebraicGeometry.blowUp`, with structure morphism
`AlgebraicGeometry.blowUpToBase`, because tags 080B and 080I are stated for it;
`Stacks.Blowup.isAdmissibleBlowup_iff` reads admissibility, which is phrased with the second
construction `Stacks.Blowup.blowUp`, in those terms. The strict transform of `X` as a scheme over
the blowup is `AlgebraicGeometry.strictTransformToBlowUp`, the closed immersion of the strict
transform into the base change followed by the projection to the blowup.

**The flattening input.** The hypothesis `hcentre` is the conclusion of [Stacks, Tag 081R]: a
centre `I`, finitely presented and supported away from `U`, whose strict transform is flat and
locally of finite presentation over the blowup. The library proves it for proper `f` with `X_U`
finite locally free over `U`:
`AlgebraicGeometry.exists_isAdmissibleBlowup_flat_finitePresentation_strictTransform_of_affineCase`
gives all four clauses under the source's hypotheses of Tag 081R, and
`AlgebraicGeometry.exists_isAdmissibleBlowup_isFiniteLocallyFree_strictTransform_of_isProper`
feeds it to the theorem below. The input is kept as an argument here because other callers
supply a flattening centre of their own.

Quasi-compactness and quasi-separatedness of the strict transform are not part of the hypothesis,
because they follow from properness of `f`; so `hcentre` asks only for the local condition.

## References

* [Stacks Project, Tag 0B49](https://stacks.math.columbia.edu/tag/0B49)
* [Stacks Project, Tag 081R](https://stacks.math.columbia.edu/tag/081R)
* [Stacks Project, Tag 080B](https://stacks.math.columbia.edu/tag/080B)
* [Stacks Project, Tag 080F](https://stacks.math.columbia.edu/tag/080F)
* [Stacks Project, Tag 080I](https://stacks.math.columbia.edu/tag/080I)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 07ZU](https://stacks.math.columbia.edu/tag/07ZU)
* [Stacks Project, Tag 0B48](https://stacks.math.columbia.edu/tag/0B48)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A base change which is finite over an open of the base is finite over the inverse image of
that open.** The restriction of `X ×_S T ⟶ T` to `g⁻¹(U)` is the base change of `X_U ⟶ U` along
`g⁻¹(U) ⟶ U`. -/
theorem isFinite_morphismRestrict_pullback_snd_preimage {X S T : Scheme.{u}} (f : X ⟶ S)
    (g : T ⟶ S) (U : S.Opens) [IsFinite (pullback.snd f U.ι)] :
    IsFinite (pullback.snd f g ∣_ (g ⁻¹ᵁ U)) := by
  have hresp : MorphismProperty.RespectsIso @IsFinite :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hbig₁ : IsPullback
      (pullback.fst (pullback.snd f U.ι) (g ∣_ U) ≫ pullback.fst f U.ι)
      (pullback.snd (pullback.snd f U.ι) (g ∣_ U)) f ((g ⁻¹ᵁ U).ι ≫ g) := by
    simpa only [morphismRestrict_ι] using
      (IsPullback.of_hasPullback (pullback.snd f U.ι) (g ∣_ U)).paste_horiz
        (IsPullback.of_hasPullback f U.ι)
  have hbig₂ := (isPullback_morphismRestrict (pullback.snd f g) (g ⁻¹ᵁ U)).paste_vert
    (IsPullback.of_hasPullback f g).flip
  have h₁ : IsFinite (pullback.snd f ((g ⁻¹ᵁ U).ι ≫ g)) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) hbig₁.isoPullback.hom _,
      hbig₁.isoPullback_hom_snd]
    infer_instance
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite)
      hbig₂.flip.isoPullback.inv _, hbig₂.flip.isoPullback_inv_snd]
  exact h₁

/-- **Finiteness of the restriction of a morphism to an open of the target is finiteness of the
corresponding base change.** The base change `X ×_S U ⟶ U` is the restriction `X_U ⟶ U`. -/
theorem isFinite_pullback_snd_of_isFinite_morphismRestrict {X S : Scheme.{u}} (f : X ⟶ S)
    (U : S.Opens) (h : IsFinite (f ∣_ U)) : IsFinite (pullback.snd f U.ι) := by
  have hresp : MorphismProperty.RespectsIso @IsFinite :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict f U,
    MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite)]
  exact h

/-- **Finiteness over an open persists to the strict transform over the inverse image of that
open in the blowup.** -/
private theorem isFinite_pullback_snd_strictTransformToBlowUp_preimage {X S : Scheme.{u}}
    (f : X ⟶ S) (I : S.IdealSheafData) (U : S.Opens) [IsFinite (pullback.snd f U.ι)] :
    IsFinite (pullback.snd (strictTransformToBlowUp f I) (blowUpToBase I ⁻¹ᵁ U).ι) := by
  have hp : IsFinite (pullback.snd f (blowUpToBase I) ∣_ (blowUpToBase I ⁻¹ᵁ U)) :=
    isFinite_morphismRestrict_pullback_snd_preimage f (blowUpToBase I) U
  have hc : IsFinite ((Stacks.StrictTransform.ideal f (blowUpToBase I)
      (exceptionalIdeal I)).subschemeι ∣_
        (pullback.snd f (blowUpToBase I) ⁻¹ᵁ (blowUpToBase I ⁻¹ᵁ U))) := inferInstance
  refine isFinite_pullback_snd_of_isFinite_morphismRestrict _ _ ?_
  rw [show strictTransformToBlowUp f I =
    (Stacks.StrictTransform.ideal f (blowUpToBase I) (exceptionalIdeal I)).subschemeι ≫
      pullback.snd f (blowUpToBase I) from rfl, morphismRestrict_comp]
  exact MorphismProperty.comp_mem (W := @IsFinite) _ _ hc hp

/-- **The argument of Stacks Project, Tag 0B49, from a flattening centre onwards.** Let `S` be
a quasi-compact and quasi-separated scheme, let `f : X ⟶ S` be proper and let `U ⊆ S` be a
quasi-compact open over which `X` is finite locally free. Given a centre `I`, finitely presented
and supported away from `U`, whose strict transform is flat and locally of finite presentation
(the conclusion of [Stacks, Tag 081R]), there is a `U`-admissible blowup of `S` along which the
strict transform of `X` is finite locally free. Tag 0B49 itself is
`AlgebraicGeometry.exists_isAdmissibleBlowup_isFiniteLocallyFree_strictTransform_of_isProper`,
which supplies the centre. -/
theorem exists_isAdmissibleBlowup_isFiniteLocallyFree_strictTransform {X S : Scheme.{u}}
    [CompactSpace S] [QuasiSeparatedSpace S] (f : X ⟶ S) [IsProper f] (U : S.Opens)
    (hU : IsCompact (U : Set S))
    [Stacks.Morphisms.IsFiniteLocallyFree (pullback.snd f U.ι)]
    (hcentre : ∃ I : S.IdealSheafData,
      FinitePresentation I.subschemeι ∧ Disjoint (U : Set S) (I.support : Set S) ∧
        Flat (strictTransformToBlowUp f I) ∧
          LocallyOfFinitePresentation (strictTransformToBlowUp f I)) :
    ∃ I : S.IdealSheafData,
      Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase I) ∧
        Stacks.Morphisms.IsFiniteLocallyFree (strictTransformToBlowUp f I) := by
  have hflfU :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      (pullback.snd f U.ι)).mp inferInstance
  have _ : IsFinite (pullback.snd f U.ι) := hflfU.1
  obtain ⟨I, hIfp, hIdisj, hflat, hfp⟩ := hcentre
  have _ : Flat (strictTransformToBlowUp f I) := hflat
  have _ : LocallyOfFinitePresentation (strictTransformToBlowUp f I) := hfp
  -- the complement of `U` is the support of a centre of finite type
  obtain ⟨J, hJft, hJsupp⟩ := exists_isFiniteType_support_eq_compl S U hU
  have hZsupp : ∀ y : blowUp I,
      y ∈ ((J.comap (blowUpToBase I)).support : Set (blowUp I)) ↔
        (blowUpToBase I) y ∈ (J.support : Set S) := fun y ↦ by simp
  -- the second centre, on the blowup in `I`, and the composite centre `I * J`
  have hcomap : J.comap (blowUpToBase I) =
      exceptionalIdeal I ^ 0 * J.comap (blowUpToBase I) := by rw [pow_zero, one_mul]
  obtain ⟨e⟩ := nonempty_blowUpCompositionIso I (J.comap (blowUpToBase I)) 0 J hcomap
  -- the support of `J` is covered by the first centre and the image of the second
  have hKsupport : (I * J).supportSet = I.supportSet ∪
      (blowUpToBase I).base '' (J.comap (blowUpToBase I)).supportSet :=
    supportSet_mul_eq_union_image_comap I J
  -- the composite centre is finitely presented and supported exactly off `U`
  have hKfp : FinitePresentation (I * J).subschemeι :=
    finitePresentation_mul_subschemeι I J hIfp hJft
  have hIsubJ : I.supportSet ⊆ J.supportSet := fun x hx ↦ by
    change x ∈ (J.support : Set S)
    rw [hJsupp]
    exact Set.disjoint_right.mp hIdisj hx
  have hKsuppJ : (I * J).supportSet = J.supportSet := by
    have hmul : (I * J).supportSet = I.supportSet ∪ J.supportSet :=
      congrArg (fun C : Closeds S ↦ (C : Set S))
        (Scheme.IdealSheafData.support_mul (I := I) (J := J)) |>.trans
        (Closeds.coe_sup _ _)
    rw [hmul, Set.union_eq_right.mpr hIsubJ]
  have hKdisj : Disjoint (U : Set S) ((I * J).support : Set S) := by
    change Disjoint (U : Set S) ((I * J).supportSet)
    rw [hKsuppJ]
    change Disjoint (U : Set S) ((J.support : Set S))
    rw [hJsupp]
    exact disjoint_compl_right
  -- the second blowup, and the inverse image of `U` on it
  set Z : (blowUp I).IdealSheafData := J.comap (blowUpToBase I) with hZ
  set f₁ := strictTransformToBlowUp f I with hf₁
  set U₂ : (blowUp Z).Opens := blowUpToBase Z ⁻¹ᵁ (blowUpToBase I ⁻¹ᵁ U) with hU₂
  have hEV : U₂ = (exceptionalIdeal Z).support.compl := by
    refine Opens.ext (Set.ext fun x ↦ ?_)
    have h₁ : x ∈ ((exceptionalIdeal Z).support : Set (blowUp Z)) ↔
        (blowUpToBase I) ((blowUpToBase Z) x) ∈ (J.support : Set S) := by
      change x ∈ ((Z.comap (blowUpToBase Z)).support : Set (blowUp Z)) ↔ _
      rw [Scheme.IdealSheafData.support_comap]
      exact hZsupp ((blowUpToBase Z) x)
    change (blowUpToBase I) ((blowUpToBase Z) x) ∈ U ↔
      x ∉ ((exceptionalIdeal Z).support : Set (blowUp Z))
    rw [h₁, hJsupp]
    simp
  -- that inverse image is the complement of an effective Cartier divisor, hence dense
  have hU₂dense : Dense (U₂ : Set (blowUp Z)) := by
    have hdense : Scheme.Opens.IsSchemeTheoreticallyDense U₂ := by
      rw [hEV]
      exact Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor
        (exceptionalIdeal Z) inferInstance
    have _ : IsAffineHom U₂.ι := by
      rw [hEV]
      exact Stacks.Divisors.isAffineHom_compl_of_isEffectiveCartierDivisor
        (exceptionalIdeal Z) inferInstance
    have _ : IsSchemeTheoreticallyDominant U₂.ι :=
      Stacks.SchemeTheoreticImage.isSchemeTheoreticallyDominant_of_dense U₂ hdense
    have hrange : Set.range U₂.ι.base = (U₂ : Set (blowUp Z)) := by
      refine Set.Subset.antisymm ?_ fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩
      rintro _ ⟨y, rfl⟩
      exact y.2
    rw [← hrange]
    exact U₂.ι.denseRange
  -- the strict transform of a flat scheme is the whole base change
  have hbot : Stacks.StrictTransform.ideal f₁ (blowUpToBase Z) (exceptionalIdeal Z) = ⊥ :=
    strictTransformIdeal_eq_bot_of_flat_at_exceptional f₁ Z fun x _ ↦ Flat.stalkMap f₁ x
  have _ : IsIso (Stacks.StrictTransform.ideal f₁ (blowUpToBase Z)
      (exceptionalIdeal Z)).subschemeι := by
    rw [hbot]
    infer_instance
  set f₂ := strictTransformToBlowUp f₁ Z with hf₂
  have _ : Flat f₂ := inferInstance
  have _ : LocallyOfFinitePresentation f₂ := inferInstance
  have _ : IsProper f₂ := inferInstance
  -- the twice-transformed scheme is finite over the inverse image of `U`
  have _ : IsFinite (pullback.snd f₁ (blowUpToBase I ⁻¹ᵁ U).ι) :=
    isFinite_pullback_snd_strictTransformToBlowUp_preimage f I U
  have hfinU₂ : IsFinite (pullback.snd f₂ U₂.ι) :=
    isFinite_pullback_snd_strictTransformToBlowUp_preimage f₁ Z _
  have _ : IsFinite (pullback.snd f₂ U₂.ι) := hfinU₂
  have hfin₂ : IsFinite f₂ :=
    isFinite_of_isFinite_over_dense_open f₂ U₂ hU₂dense (Or.inl inferInstance)
  -- transport along the identification of the composite blowup with the blowup in `I * J`
  obtain ⟨g, -, hg⟩ :=
    Stacks.StrictTransform.strictTransform_comp_blowUp f I (I * J) Z hKsupport e
  have _ : IsIso e.hom.left :=
    ⟨e.inv.left, Over.hom_left_inv_left e, Over.inv_left_hom_left e⟩
  have hg' : g.hom ≫ strictTransformToBlowUp f (I * J) = f₂ ≫ e.hom.left :=
    hg.trans (Category.assoc _ _ _).symm
  have key : ∀ P : MorphismProperty Scheme.{u}, P.RespectsIso → P f₂ →
      P (strictTransformToBlowUp f (I * J)) := by
    intro P hresp hP
    rw [← P.cancel_left_of_respectsIso g.hom, hg', P.cancel_right_of_respectsIso]
    exact hP
  have hrFinite : MorphismProperty.RespectsIso @IsFinite :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hrFlat : MorphismProperty.RespectsIso @Flat :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hrLofp : MorphismProperty.RespectsIso @LocallyOfFinitePresentation :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine ⟨I * J, (Stacks.Blowup.isAdmissibleBlowup_iff U _).mpr
    ⟨I * J, hKfp, hKdisj, Iso.refl _, Category.id_comp _⟩, ?_⟩
  exact (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    (strictTransformToBlowUp f (I * J))).2
    ⟨key @IsFinite hrFinite hfin₂, key @Flat hrFlat inferInstance,
      key @LocallyOfFinitePresentation hrLofp inferInstance⟩

end AlgebraicGeometry

end
