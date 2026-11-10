module

public import StacksFrontier.AlgebraicGeometry.Blowup.CompositeCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Bijective
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierComplement
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.AffineChartDescentFiniteType
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformSchemeFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.FiniteLocallyFreeRank
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AlmostBlowUp.IsomorphismAwayFromCenter
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FinitePresentationFromDenseOpen
public import StacksFrontier.AlgebraicGeometry.Properties.FiniteTypeIdealSheafOfOpen
public import StacksFrontier.AlgebraicGeometry.StrictTransform.CompositionScheme
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.Shrinking

/-!
# The finite-presentation clause of tag 081R follows from its flatness clause

Let `S` be a quasi-compact and quasi-separated scheme, let `f : X ⟶ S` be of finite type and
quasi-separated and let `U ⊆ S` be a quasi-compact open over which `f` is locally of finite
presentation. **Granted only the flatness clause of [Stacks, Tag 081R]** — some `U`-admissible
centre whose strict transform is flat — there is a `U`-admissible centre whose strict transform
is flat *and of finite presentation*.

So the finite-presentation clause of tag 081R is not an independent gap: the whole tag reduces
to the flatness half of [Stacks, Tag 0815], and nothing of that tag's own
finite-presentation half is used.

## Main results

* `exists_isAdmissibleBlowup_flat_finitePresentation_support_eq_compl_of_flatteningCentre`:
  the reduction just described, with the extra information that the centre produced is supported
  on *exactly* the complement of `U` — so that the inverse image of `U` in the blowup is the
  complement of the exceptional divisor, hence scheme-theoretically dense. That is what
  [Stacks, Tag 081S] needs on top of tag 081R.
* `AlgebraicGeometry.exists_isAdmissibleBlowup_flat_finitePresentation_of_flatteningCentre`:
  the same statement with that clause weakened to disjointness from `U`. No tag.
* `exists_isAdmissibleBlowup_flat_finitePresentation_strictTransform_of_affineCharts`:
  the conclusion of tag 081R in full, carrying nothing but
  `AlgebraicGeometry.AffineChartFlatteningCentre` — the affine case of the flatness half of
  tag 0815 with that tag's hypotheses (2)-(5) deleted — obtained by composing the reduction with
  `AlgebraicGeometry.exists_isAdmissibleBlowup_flat_strictTransform`. No tag: the statement omits
  the flatness half of hypothesis (2) of the source.
* `exists_isAdmissibleBlowup_flat_finitePresentation_strictTransform_of_affineCase`:
  **[Stacks, Tag 081R]** in full, under exactly the source's hypotheses, carrying nothing. This
  is where the tag is registered.

## Implementation notes

This is the source's "we may assume `U` is scheme-theoretically dense", the third paragraph of
Remark 38.30.1 ([Stacks, Tag 080Y]), carried out on the composite centre.

Let `I` be the centre the flatness clause supplies, so that `f₁ : X₁ ⟶ S₁ = Bl_I(S)` is flat,
and let `J` be a centre of finite type cutting out `S ∖ U`
(`AlgebraicGeometry.exists_isFiniteType_support_eq_compl`). The centre asserted is the product
`I · J`:

* by [Stacks, Tag 080B] (`AlgebraicGeometry.nonempty_blowUpCompositionIso`) the blowup of `S` in
  `I · J` is the blowup of `S₁` in `Z = J·𝒪_{S₁}` followed by `S₁ ⟶ S`, and by
  [Stacks, Tag 080I] part (2) (`Stacks.StrictTransform.strictTransform_comp_blowUp`) the strict
  transform of `X` along `Bl_{I·J}(S) ⟶ S` is the strict transform `f₂` of `X₁` along
  `Bl_Z(S₁) ⟶ S₁`;
* `f₁` being flat, that second strict transform is the whole base change
  ([Stacks, Tag 080F] part (1),
  `AlgebraicGeometry.strictTransformIdeal_eq_bot_of_flat_at_exceptional`), so `f₂` is flat;
* the inverse image `U₂` of `U` in `Bl_Z(S₁)` is exactly the complement of the exceptional
  divisor of the second blowup, hence the complement of an effective Cartier divisor
  ([Stacks, Tag 02OS]); so it is scheme-theoretically dense and its inclusion is affine, both
  halves of [Stacks, Tag 07ZU]
  (`Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor` and
  `Stacks.Divisors.isAffineHom_compl_of_isEffectiveCartierDivisor`), whence `U₂` is also
  retrocompact;
* `f₂` is locally of finite type and locally of finite presentation over `U₂`, so
  [Stacks, Tag 081P], in the form
  `FinitePresentationFromDenseOpen.locallyOfFinitePresentation_of_flat_of_retrocompact_dense_open`,
  makes it locally of finite presentation; and
  `AlgebraicGeometry.finitePresentation_strictTransformToBlowUp_iff` upgrades that to finite
  presentation.

**Local finite presentation over the inverse image of `U`.** This is where the centres being
supported away from `U` is used. A strict transform is a closed subscheme of a base change cut
out by `Stacks.StrictTransform.ideal`, which by
`Stacks.StrictTransform.ideal_eq_ker_ι` is the kernel ideal of the inclusion of the complement
of the exceptional divisor's inverse image. Over the inverse image of `U` that complement is
everything, and a kernel ideal restricts to zero on any open inside the open it is the kernel of
(`AlgebraicGeometry.comap_ker_ι_eq_bot_of_le` below), so by
`AlgebraicGeometry.restrict_isIso_iff_comap_bot` the closed immersion restricts to an
isomorphism there: over the inverse image of `U` the strict transform *is* the base change, and
local finite presentation comes from that of `f ∣_ U` by base change
(`AlgebraicGeometry.morphismRestrict_pullback_snd_preimage_of_isStableUnderBaseChange`).

## References

* [Stacks Project, Tag 081R](https://stacks.math.columbia.edu/tag/081R)
* [Stacks Project, Tag 080Y](https://stacks.math.columbia.edu/tag/080Y)
* [Stacks Project, Tag 080B](https://stacks.math.columbia.edu/tag/080B)
* [Stacks Project, Tag 080F](https://stacks.math.columbia.edu/tag/080F)
* [Stacks Project, Tag 080I](https://stacks.math.columbia.edu/tag/080I)
* [Stacks Project, Tag 081P](https://stacks.math.columbia.edu/tag/081P)
* [Stacks Project, Tag 07ZU](https://stacks.math.columbia.edu/tag/07ZU)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A kernel ideal restricts to zero on any open inside the open it is the kernel of.** A
section of `𝒪_T` vanishing on `V` vanishes on the smaller `W`, so the closed subscheme cut out
by `V.ι.ker` meets `W` in all of `W`. -/
theorem comap_ker_ι_eq_bot_of_le {T : Scheme.{u}} {V W : T.Opens} (h : W ≤ V) :
    (V.ι.ker).comap W.ι = ⊥ := by
  rw [← T.homOfLE_ι h, Scheme.IdealSheafData.comap_comp, ker_comap_self,
    Scheme.IdealSheafData.comap_bot]

/-- **A property stable under base change passes from `f` over `U` to a base change of `f` over
the inverse image of `U`.** Both morphisms are base changes of `f` along `U' ⟶ U ⟶ S`, so
`AlgebraicGeometry.prop_iff_of_isPullback` identifies them. -/
theorem morphismRestrict_pullback_snd_preimage_of_isStableUnderBaseChange
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] {X S T : Scheme.{u}}
    (f : X ⟶ S) (b : T ⟶ S) (U : S.Opens) (h : P (f ∣_ U)) :
    P (pullback.snd f b ∣_ (b ⁻¹ᵁ U)) := by
  have _ : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine (prop_iff_of_isPullback P
    (isPullback_pullback_snd_morphismRestrict f U (b ∣_ U) ((b ⁻¹ᵁ U).ι ≫ b)
      (morphismRestrict_ι b U))
    (isPullback_morphismRestrict_pullback_snd f b (b ⁻¹ᵁ U))).mp ?_
  exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback (f ∣_ U) (b ∣_ U)) h

/-- The support of the inverse image of an ideal sheaf is the preimage of its support. -/
private theorem coe_support_comap {X Y : Scheme.{u}} (g : X ⟶ Y) (I : Y.IdealSheafData) :
    ((I.comap g).support : Set X) = g.base ⁻¹' (I.support : Set Y) := by
  rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage]

/-- **Over an open of the blowup lying over `U`, the strict transform of `X` is the whole base
change.** The defining ideal of the strict transform is the kernel ideal of the inclusion of the
complement of the exceptional divisor's inverse image, and that complement contains the inverse
image of `U` because the centre is supported away from `U`. -/
theorem isIso_strictTransformι_morphismRestrict_of_disjoint {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) (U : S.Opens) (hdisj : Disjoint (U : Set S) (I.support : Set S)) :
    IsIso ((Stacks.StrictTransform.ideal f (blowUpToBase I) (exceptionalIdeal I)).subschemeι ∣_
      (pullback.snd f (blowUpToBase I) ⁻¹ᵁ (blowUpToBase I ⁻¹ᵁ U))) := by
  have hs : ((exceptionalIdeal I).support : Set (blowUp I)) =
      (blowUpToBase I).base ⁻¹' (I.support : Set S) := by
    exact coe_support_comap (blowUpToBase I) I
  have hle : (blowUpToBase I ⁻¹ᵁ U : (blowUp I).Opens) ≤ (exceptionalIdeal I).support.compl := by
    intro y hy
    change y ∉ ((exceptionalIdeal I).support : Set (blowUp I))
    rw [hs]
    exact fun hmem ↦ Set.disjoint_left.mp hdisj hy hmem
  rw [restrict_isIso_iff_comap_bot, Stacks.StrictTransform.ideal_eq_ker_ι]
  exact comap_ker_ι_eq_bot_of_le (fun x hx ↦ hle hx)

/-- **Local finite presentation of the strict transform over the inverse image of `U`.** Over
that open the strict transform is the base change, by
`AlgebraicGeometry.isIso_strictTransformι_morphismRestrict_of_disjoint`, and the base change of
`f ∣_ U` is locally of finite presentation. -/
theorem locallyOfFinitePresentation_strictTransformToBlowUp_morphismRestrict {X S : Scheme.{u}}
    (f : X ⟶ S) (I : S.IdealSheafData) (U : S.Opens)
    (hdisj : Disjoint (U : Set S) (I.support : Set S))
    (h : LocallyOfFinitePresentation (f ∣_ U)) :
    LocallyOfFinitePresentation (strictTransformToBlowUp f I ∣_ (blowUpToBase I ⁻¹ᵁ U)) := by
  have _ := isIso_strictTransformι_morphismRestrict_of_disjoint f I U hdisj
  have _ : MorphismProperty.RespectsIso (@LocallyOfFinitePresentation) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.ContainsIdentities (@LocallyOfFinitePresentation) :=
    ⟨fun T ↦ inferInstanceAs (LocallyOfFinitePresentation (𝟙 T))⟩
  have hA : LocallyOfFinitePresentation
      ((Stacks.StrictTransform.ideal f (blowUpToBase I) (exceptionalIdeal I)).subschemeι ∣_
        (pullback.snd f (blowUpToBase I) ⁻¹ᵁ (blowUpToBase I ⁻¹ᵁ U))) :=
    MorphismProperty.of_isIso _ _
  have hB : LocallyOfFinitePresentation
      (pullback.snd f (blowUpToBase I) ∣_ (blowUpToBase I ⁻¹ᵁ U)) :=
    morphismRestrict_pullback_snd_preimage_of_isStableUnderBaseChange
      (@LocallyOfFinitePresentation) f (blowUpToBase I) U h
  rw [show strictTransformToBlowUp f I =
    (Stacks.StrictTransform.ideal f (blowUpToBase I)
        (exceptionalIdeal I)).subschemeι ≫ pullback.snd f (blowUpToBase I) from rfl,
    morphismRestrict_comp]
  exact MorphismProperty.comp_mem (W := @LocallyOfFinitePresentation) _ _ hA hB

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Stacks Project, Tag 081R, with the support of the centre pinned down.** Let `S` be a
quasi-compact and quasi-separated scheme, let `f : X ⟶ S` be of finite type and quasi-separated
and let `U ⊆ S` be a quasi-compact open over which `f` is locally of finite presentation.
Granted the *flatness* clause of the conclusion for some `U`-admissible centre, there is a
centre supported on exactly the complement of `U` — in particular `U`-admissible — whose strict
transform is flat and of finite presentation over the blowup.

Only the flatness clause is carried: the finite-presentation clause of the conclusion is
derived.

The centre asserted is the composite `I · J` of the carried centre `I` with a centre `J` of
finite type cutting out `S ∖ U`, and the support of a composite centre is the union of the two
supports; `I` being supported away from `U`, that union is the complement of `U` on the nose.
This is the clause [Stacks, Tag 081S] needs beyond tag 081R: it makes the inverse image of `U`
in the blowup the complement of the exceptional divisor. -/
theorem exists_isAdmissibleBlowup_flat_finitePresentation_support_eq_compl_of_flatteningCentre
    [CompactSpace S] [QuasiSeparatedSpace S] [LocallyOfFiniteType f] [QuasiCompact f]
    [QuasiSeparated f] (U : S.Opens) (hU : IsCompact (U : Set S))
    [LocallyOfFinitePresentation (f ∣_ U)]
    (hflat : ∃ I : S.IdealSheafData, FinitePresentation I.subschemeι ∧
      Disjoint (U : Set S) (I.support : Set S) ∧ Flat (strictTransformToBlowUp f I)) :
    ∃ ℐ : S.IdealSheafData,
      FinitePresentation ℐ.subschemeι ∧
        (ℐ.support : Set S) = (U : Set S)ᶜ ∧
          Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase ℐ) ∧
            Flat (strictTransformToBlowUp f ℐ) ∧
              FinitePresentation (strictTransformToBlowUp f ℐ) := by
  obtain ⟨I, hIfp, hIdisj, hIflat⟩ := hflat
  have _ := hIflat
  obtain ⟨J, hJft, hJsupp⟩ := exists_isFiniteType_support_eq_compl S U hU
  have hcomap : J.comap (blowUpToBase I) =
      exceptionalIdeal I ^ 0 * J.comap (blowUpToBase I) := by rw [pow_zero, one_mul]
  obtain ⟨e⟩ := nonempty_blowUpCompositionIso I (J.comap (blowUpToBase I)) 0 J hcomap
  have hKsupport : (I * J).supportSet = I.supportSet ∪
      (blowUpToBase I).base '' (J.comap (blowUpToBase I)).supportSet :=
    supportSet_mul_eq_union_image I (J.comap (blowUpToBase I)) 0 J hcomap
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
  have hKsupp : (((I * J).support : Set S)) = (U : Set S)ᶜ := hKsuppJ.trans hJsupp
  -- the second blowup, and the inverse image of `U` on it
  set Z : (blowUp I).IdealSheafData := J.comap (blowUpToBase I) with hZ
  set f₁ := strictTransformToBlowUp f I with hf₁
  set U₁ : (blowUp I).Opens := blowUpToBase I ⁻¹ᵁ U with hU₁
  set U₂ : (blowUp Z).Opens := blowUpToBase Z ⁻¹ᵁ U₁ with hU₂
  have hEV : U₂ = (exceptionalIdeal Z).support.compl := by
    refine Opens.ext (Set.ext fun x ↦ ?_)
    have h₁ : x ∈ ((exceptionalIdeal Z).support : Set (blowUp Z)) ↔
        (blowUpToBase I) ((blowUpToBase Z) x) ∈ (J.support : Set S) := by
      exact (Set.ext_iff.mp (coe_support_comap (blowUpToBase Z) Z) x).trans
        (Set.ext_iff.mp (coe_support_comap (blowUpToBase I) J) _)
    change (blowUpToBase I) ((blowUpToBase Z) x) ∈ U ↔
      x ∉ ((exceptionalIdeal Z).support : Set (blowUp Z))
    rw [h₁, hJsupp]
    simp
  -- that inverse image is the complement of an effective Cartier divisor
  have hdense : Scheme.Opens.IsSchemeTheoreticallyDense U₂ := by
    rw [hEV]
    exact Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor
      (exceptionalIdeal Z) inferInstance
  have hretro : IsRetrocompact (U₂ : Set (blowUp Z)) := by
    have hqc : QuasiCompact U₂.ι := by
      rw [hEV]
      infer_instance
    rw [IsRetrocompact_iff_isSpectralMap_subtypeVal]
    exact quasiCompact_iff_isSpectralMap.mp hqc
  -- the strict transform of a flat scheme is the whole base change
  have hbot : Stacks.StrictTransform.ideal f₁ (blowUpToBase Z) (exceptionalIdeal Z) = ⊥ :=
    strictTransformIdeal_eq_bot_of_flat_at_exceptional f₁ Z fun x _ ↦ Flat.stalkMap f₁ x
  have _ : IsIso (Stacks.StrictTransform.ideal f₁ (blowUpToBase Z)
      (exceptionalIdeal Z)).subschemeι := by
    rw [hbot]
    infer_instance
  set f₂ := strictTransformToBlowUp f₁ Z with hf₂
  have _ : Flat f₂ := inferInstance
  have _ : LocallyOfFiniteType f₂ := inferInstance
  -- local finite presentation over the inverse image of `U`, in two steps
  have hlfp₁ : LocallyOfFinitePresentation (f₁ ∣_ U₁) :=
    locallyOfFinitePresentation_strictTransformToBlowUp_morphismRestrict f I U hIdisj
      inferInstance
  have hZdisj : Disjoint (U₁ : Set (blowUp I)) (Z.support : Set (blowUp I)) := by
    have hZs : (Z.support : Set (blowUp I)) = ((U₁ : Set (blowUp I)))ᶜ := by
      rw [hZ, coe_support_comap, hJsupp, Set.preimage_compl]
      rfl
    exact disjoint_compl_right.mono_right hZs.le
  have hlfp₂ : LocallyOfFinitePresentation (f₂ ∣_ U₂) :=
    locallyOfFinitePresentation_strictTransformToBlowUp_morphismRestrict f₁ Z U₁ hZdisj hlfp₁
  have _ := hlfp₂
  have hlfp : LocallyOfFinitePresentation f₂ :=
    FinitePresentationFromDenseOpen.locallyOfFinitePresentation_of_flat_of_retrocompact_dense_open
      f₂ U₂ hretro hdense
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
  refine ⟨I * J, hKfp, hKsupp,
    (Stacks.Blowup.isAdmissibleBlowup_iff U (blowUpToBase (I * J))).mpr
      ⟨I * J, hKfp, disjoint_compl_right.mono_right hKsupp.le, Iso.refl _, Category.id_comp _⟩,
    key @Flat MorphismProperty.IsStableUnderBaseChange.respectsIso inferInstance, ?_⟩
  exact (finitePresentation_strictTransformToBlowUp_iff f (I * J)).mpr
    (key @LocallyOfFinitePresentation MorphismProperty.IsStableUnderBaseChange.respectsIso
      hlfp)

/-- **Stacks Project, Tag 081R.** Let `S` be a quasi-compact and quasi-separated scheme, let
`f : X ⟶ S` be of finite type and quasi-separated and let `U ⊆ S` be a quasi-compact open over
which `f` is locally of finite presentation. Granted the *flatness* clause of the conclusion for
some `U`-admissible centre, there is a `U`-admissible centre whose strict transform is flat and
of finite presentation over the blowup.

Only the flatness clause is carried: the finite-presentation clause of the conclusion is
derived.

This tag is NOT registered on this declaration. The statement omits the flatness half of
hypothesis (2) of the source -- `X_U ⟶ U` flat -- on the ground that it enters only through the
carried affine case; it does, but `AlgebraicGeometry.AffineChartFlatteningCentre` is that case
with tag 0815's hypotheses (2)-(5) deleted and is false in general, by
`AlgebraicGeometry.affineChartFlatteningCentre_top_iff`, so without the flatness hypothesis the
carried hypothesis is unsatisfiable. The tag sits on
`AlgebraicGeometry.exists_isAdmissibleBlowup_flat_finitePresentation_strictTransform_of_affineCase`
below, which has hypothesis (2) in full and carries nothing: the affine case it consumes is
`AffineChartFlatteningCentreUnderSourceHypotheses.of_compactSpace`, which is that case for an
arbitrary quasi-coherent module with nothing granted, and the reduction of a morphism locally of
finite TYPE to one of finite PRESENTATION is what applies it (tag 04II immerses the chart into
affine space over the base and tag 080G transports the conclusion back).
-/
theorem exists_isAdmissibleBlowup_flat_finitePresentation_of_flatteningCentre [CompactSpace S]
    [QuasiSeparatedSpace S] [LocallyOfFiniteType f] [QuasiCompact f] [QuasiSeparated f]
    (U : S.Opens) (hU : IsCompact (U : Set S)) [LocallyOfFinitePresentation (f ∣_ U)]
    (hflat : ∃ I : S.IdealSheafData, FinitePresentation I.subschemeι ∧
      Disjoint (U : Set S) (I.support : Set S) ∧ Flat (strictTransformToBlowUp f I)) :
    ∃ ℐ : S.IdealSheafData,
      FinitePresentation ℐ.subschemeι ∧
        Disjoint (U : Set S) (ℐ.support : Set S) ∧
          Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase ℐ) ∧
            Flat (strictTransformToBlowUp f ℐ) ∧
              FinitePresentation (strictTransformToBlowUp f ℐ) := by
  obtain ⟨ℐ, hfp, hsupp, hadm, hflat', hfpst⟩ :=
    exists_isAdmissibleBlowup_flat_finitePresentation_support_eq_compl_of_flatteningCentre f U hU
      hflat
  refine ⟨ℐ, hfp, ?_, hadm, hflat', hfpst⟩
  exact disjoint_compl_right.mono_right hsupp.le

/-- **Stacks Project, Tag 081R**, carrying nothing but the affine case of the *flatness* half of
[Stacks, Tag 0815].

`AlgebraicGeometry.exists_isAdmissibleBlowup_flat_strictTransform` proves the flatness clause
from `AlgebraicGeometry.AffineChartFlatteningCentre`, and
`AlgebraicGeometry.exists_isAdmissibleBlowup_flat_finitePresentation_of_flatteningCentre` turns
that into both clauses. So the only thing the whole of tag 081R still waits on is that one
predicate — the affine case of the flatness assertion of tag 0815.

This tag is NOT registered on this declaration. The statement omits the flatness half of
hypothesis (2) of the source -- `X_U ⟶ U` flat -- on the ground that it enters only through the
carried affine case; it does, but `AlgebraicGeometry.AffineChartFlatteningCentre` is that case
with tag 0815's hypotheses (2)-(5) deleted and is false in general, by
`AlgebraicGeometry.affineChartFlatteningCentre_top_iff`, so without the flatness hypothesis the
carried hypothesis is unsatisfiable. The tag sits on
`AlgebraicGeometry.exists_isAdmissibleBlowup_flat_finitePresentation_strictTransform_of_affineCase`
below, which has hypothesis (2) in full and carries nothing: the affine case it consumes is
`AffineChartFlatteningCentreUnderSourceHypotheses.of_compactSpace`, which is that case for an
arbitrary quasi-coherent module with nothing granted, and the reduction of a morphism locally of
finite TYPE to one of finite PRESENTATION is what applies it (tag 04II immerses the chart into
affine space over the base and tag 080G transports the conclusion back).
-/
theorem exists_isAdmissibleBlowup_flat_finitePresentation_strictTransform_of_affineCharts
    [CompactSpace S] [QuasiSeparatedSpace S] [LocallyOfFiniteType f] [QuasiCompact f]
    [QuasiSeparated f] (U : S.Opens) (hU : IsCompact (U : Set S))
    [LocallyOfFinitePresentation (f ∣_ U)]
    (H : AffineChartFlatteningCentre f X.unitModule U) :
    ∃ ℐ : S.IdealSheafData,
      FinitePresentation ℐ.subschemeι ∧
        Disjoint (U : Set S) (ℐ.support : Set S) ∧
          Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase ℐ) ∧
            Flat (strictTransformToBlowUp f ℐ) ∧
              FinitePresentation (strictTransformToBlowUp f ℐ) :=
  exists_isAdmissibleBlowup_flat_finitePresentation_of_flatteningCentre f U hU
    (let ⟨I, hIfp, hIdisj, _, hIflat⟩ :=
      exists_isAdmissibleBlowup_flat_strictTransform f U hU H
    ⟨I, hIfp, hIdisj, hIflat⟩)

/-- **Stacks Project, Tag 081R.** Let `S` be a quasi-compact and quasi-separated scheme, let
`f : X ⟶ S` be of finite type and quasi-separated and let `U ⊆ S` be a quasi-compact open such
that `X_U ⟶ U` is flat and locally of finite presentation. Then there is a `U`-admissible blowup
of `S` along which the strict transform of `X` is flat and of finite presentation.

Both hypotheses of the source are present: (1) `f` of finite type and quasi-separated, and (2)
`X_U ⟶ U` flat and locally of finite presentation. Hypothesis (2) is what
`exists_isAdmissibleBlowup_flat_finitePresentation_strictTransform_of_affineCharts`
and `AlgebraicGeometry.exists_isAdmissibleBlowup_flat_strictTransform` omit the flatness half of,
on the ground that it enters only through the affine case they take as an input. It does enter
only through it, but the hypothesis-free `AlgebraicGeometry.AffineChartFlatteningCentre` that
those forms take is false in general, so no proof of the affine case can supply it. With
hypothesis (2) present the chain closes:
`AlgebraicGeometry.AffineChartFlatteningCentre.of_affineCase`
produces the chart predicate precisely from hypothesis (2), by the source's own route through the
immersion into affine space of [Stacks, Tag 04II], and the affine case it calls on is
`AffineChartFlatteningCentreUnderSourceHypotheses.of_compactSpace`, itself proved from
[Stacks, Tag 0811]. -/
@[stacks 081R "the conclusion in full -- the strict transform flat AND of finite presentation -- \
under exactly the source's hypotheses (1) and (2): the affine case of the \
flatness assertion of [Stacks, Tag 0815] that the proof consumes is \
`AlgebraicGeometry.AffineChartFlatteningCentreUnderSourceHypotheses.of_compactSpace`, \
itself proved from \
[Stacks, Tag 0811]"]
theorem exists_isAdmissibleBlowup_flat_finitePresentation_strictTransform_of_affineCase
    [CompactSpace S] [QuasiSeparatedSpace S] [LocallyOfFiniteType f] [QuasiCompact f]
    [QuasiSeparated f] (U : S.Opens) (hU : IsCompact (U : Set S)) (hflat : Flat (f ∣_ U))
    (hfp : LocallyOfFinitePresentation (f ∣_ U)) :
    ∃ ℐ : S.IdealSheafData,
      FinitePresentation ℐ.subschemeι ∧
        Disjoint (U : Set S) (ℐ.support : Set S) ∧
          Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase ℐ) ∧
            Flat (strictTransformToBlowUp f ℐ) ∧
              FinitePresentation (strictTransformToBlowUp f ℐ) := by
  have _ : LocallyOfFinitePresentation (f ∣_ U) := hfp
  exact exists_isAdmissibleBlowup_flat_finitePresentation_strictTransform_of_affineCharts f U hU
    (AffineChartFlatteningCentre.of_affineCase f U hU hflat hfp)

end AlgebraicGeometry

end
