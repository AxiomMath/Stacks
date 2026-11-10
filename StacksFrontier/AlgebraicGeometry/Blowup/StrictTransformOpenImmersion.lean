module

public import StacksFrontier.AlgebraicGeometry.Blowup.DominatedByBlowup
public import StacksFrontier.AlgebraicGeometry.Blowup.IsoOffCentre
public import StacksFrontier.AlgebraicGeometry.Flatness.ExtendingFromOpen.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformFlatnessTransport
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformSchemeFlattening
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.DenseOpen
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Iterated
import StacksFrontier.AlgebraicGeometry.Blowup.CompositeCentre
import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Bijective
import StacksFrontier.AlgebraicGeometry.Properties.FiniteTypeIdealSheafOfOpen
import StacksFrontier.AlgebraicGeometry.StrictTransform.CompositionScheme

/-!
# The strict transform as an open subscheme of the blowup of the boundary

Let `f : X ⟶ S` be separated and locally of finite type and let `U ⊆ S` be an open over which
`f` is an isomorphism. Blow `S` up in a centre `I` supported exactly on `S ∖ U`. Then the part
of the blowup lying over `U` is the complement of the exceptional divisor, so it is
scheme-theoretically dense and retrocompact, and the strict transform of `X` is an isomorphism
over it. Granted that the strict transform is flat over the blowup, [Stacks, Tag 081M] therefore
makes it an open subscheme of the blowup — which is the conclusion
`AlgebraicGeometry.StrictTransformOpenImmersion` of [Stacks, Tag 081S].

## Main results

* `AlgebraicGeometry.preimage_compl_support_eq_compl_support_exceptionalIdeal`: for a centre
  supported exactly on the complement of `U`, the inverse image of `U` in the blowup is the
  complement of the exceptional divisor.
* `AlgebraicGeometry.isIso_morphismRestrict_strictTransformToBlowUp`: away from the centre the
  strict transform of `X` is an isomorphism onto the blowup, as soon as `f` is an isomorphism
  over the complement of the centre.
* `AlgebraicGeometry.flat_strictTransformToBlowUp_of_flat`: the strict transform of a flat
  morphism is flat over the blowup, for an arbitrary centre.
* `AlgebraicGeometry.strictTransformOpenImmersion_of_flat_strictTransform`: **the conclusion of
  [Stacks, Tag 081S] granted flatness of the strict transform over a boundary centre.**
* `AlgebraicGeometry.strictTransformOpenImmersion_of_flat`: the conclusion of
  [Stacks, Tag 081S] for a *flat* separated morphism locally of finite type, with nothing
  carried.
* `AlgebraicGeometry.exists_flat_strictTransformToBlowUp_support_eq_compl`: a centre supported on
  the *whole* of `S ∖ U` with flat strict transform, from one merely supported away from `U`.
* `AlgebraicGeometry.strictTransformOpenImmersion_of_flat_strictTransform_of_disjoint`: the
  conclusion of [Stacks, Tag 081S] from the conclusion of the cited [Stacks, Tag 081R].
* `AlgebraicGeometry.strictTransformOpenImmersion_of_affineChartFlatteningCentre`: **the
  conclusion of [Stacks, Tag 081S] granted only `AffineChartFlatteningCentre`**, the affine case
  of the cited flattening theorem [Stacks, Tag 0815], which is the single input the library's
  [Stacks, Tag 081R] carries.

## What is proved and what is not: no `@[stacks 081S]` attribute

No result in this file carries `@[stacks 081S]`, and none may.

Tag 081S asserts, for `φ : X ⟶ S` separated of finite type over a quasi-compact quasi-separated
`S` and a quasi-compact open `U ⊆ S` with `φ^{-1}U ⟶ U` an isomorphism, that *some*
`U`-admissible blowup puts the strict transform of `X` inside the blowup as an open subscheme.
Its proof has three steps: reduce to `S ∖ U` being an effective Cartier divisor
([Stacks, Tag 080Y], here `AlgebraicGeometry.cartierBoundaryReduction`); blow up again so that
the strict transform becomes flat ([Stacks, Tag 081R], here
`AlgebraicGeometry.exists_isAdmissibleBlowup_flat_strictTransform`); conclude by
[Stacks, Tag 081M], here `AlgebraicGeometry.isOpenImmersion_of_isIso_morphismRestrict`.

Everything here is proved except the flattening step, which is reduced to exactly one cited
external input. `AlgebraicGeometry.exists_isAdmissibleBlowup_flat_strictTransform` carries the
hypothesis `AlgebraicGeometry.AffineChartFlatteningCentre`, the affine case of the flatness half
of the Raynaud–Gruson flattening theorem [Stacks, Tag 0815]. Nothing in the tree produces one
except `AlgebraicGeometry.AffineChartFlatteningCentre.of_isFlatOver`, which needs the morphism to
be flat already — which is exactly the case `strictTransformOpenImmersion_of_flat` settles, and
no more. So `strictTransformOpenImmersion_of_affineChartFlatteningCentre` is 081S with that one
hypothesis carried, and it is not tagged because that hypothesis is not one the source makes:
tag 081S asserts its conclusion outright.

**The composite-centre step needs no further cited input.** The single centre for a composite of
two blowups,
`AlgebraicGeometry.nonempty_blowUpCompositionIso` ([Stacks, Tag 080B] part (2)), depends on the
factorization `J·𝒪_{S'} = E^d · Z'` of the cited Stacks Lemma 31.32.5, [Stacks, Tag 0803], which
is not in the library. That dependence is real in general and the factorization is indeed absent,
but it is vacuous in the case used here: the second centre is taken to be `J·𝒪_{S'}` itself for
`J` the boundary centre on `S`, and then `d = 0` makes the factorization `rfl` up to
`pow_zero` and `one_mul`. `AlgebraicGeometry.exists_flat_strictTransformToBlowUp_support_eq_compl`
is therefore unconditional, and the same observation is already used by
`AlgebraicGeometry.exists_isAdmissibleBlowup_isFiniteLocallyFree_strictTransform`
(`StacksFrontier/AlgebraicGeometry/Flatness/Applications/FiniteLocallyFreeStrictTransform.lean`),
whose composite-centre construction this one follows.

Consequently `AlgebraicGeometry.exists_isAdmissibleBlowup_dominating` ([Stacks, Tag 081T]) still
carries `StrictTransformOpenImmersion` as its hypothesis `h081S` for a morphism that is neither
flat nor supplied with `AffineChartFlatteningCentre`, and in particular for the modification of
Situation [Stacks, Tag 0AX8] consumed by [Stacks, Tag 0B4M].

## Implementation notes

The proof that the strict transform is an isomorphism over the inverse image of `U` splits the
composite `X' ⟶ X ×_S S' ⟶ S'` defining `AlgebraicGeometry.strictTransformToBlowUp`. Over the
exceptional complement the first factor is an isomorphism because
`Stacks.StrictTransform.ideal_eq_ker_ι` presents the strict transform as the scheme-theoretic
image of that open, and a scheme-theoretic image is an isomorphism over the open it is the image
of (`Stacks.SchemeTheoreticImage.isIso_imageι_restrict`); the second is an isomorphism because it
is a base change of `f` along a morphism landing in `U`.

That last step repeats, as a `have`, the ten lines of
`Stacks.ResolutionOfSurfaces.isIso_pullback_snd_over_open`
(`StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/DominateByNormalizedBlowUps/Basic.lean`),
which is the statement wanted verbatim and which is now `public` there, so this `have` can be
deleted in favour of it.

Retrocompactness of the exceptional complement is affineness of its inclusion
([Stacks, Tag 07ZU], `Stacks.Divisors.isAffineHom_compl_of_isEffectiveCartierDivisor`) read
through `Stacks.StrictTransform.isRetrocompact_of_quasiCompact_ι`; scheme-theoretic density is
the other half of the same tag.

## References

* [Stacks Project, Tag 081S](https://stacks.math.columbia.edu/tag/081S)
* [Stacks Project, Tag 081R](https://stacks.math.columbia.edu/tag/081R)
* [Stacks Project, Tag 081M](https://stacks.math.columbia.edu/tag/081M)
* [Stacks Project, Tag 080Y](https://stacks.math.columbia.edu/tag/080Y)
* [Stacks Project, Tag 080F](https://stacks.math.columbia.edu/tag/080F)
* [Stacks Project, Tag 07ZU](https://stacks.math.columbia.edu/tag/07ZU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-! ### The blowup of the boundary -/

/-- For a centre supported exactly on the complement of `U`, the inverse image of `U` in the
blowup is the open complement of the exceptional divisor: the exceptional ideal is the inverse
image of the centre, so its support is the inverse image of the support of the centre. -/
public theorem preimage_compl_support_eq_compl_support_exceptionalIdeal (I : S.IdealSheafData) :
    (blowUpToBase I ⁻¹ᵁ (I.support.compl : S.Opens) : (blowUp I).Opens) =
      (exceptionalIdeal I).support.compl := by
  refine TopologicalSpace.Opens.ext ?_
  have h : ((exceptionalIdeal I).support : Set (blowUp I)) =
      (blowUpToBase I).base ⁻¹' (I.support : Set S) := by
    change ((I.comap (blowUpToBase I)).support : Set (blowUp I)) = _
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage]
  rw [show (((exceptionalIdeal I).support.compl : (blowUp I).Opens) : Set (blowUp I)) =
      ((exceptionalIdeal I).support : Set (blowUp I))ᶜ from rfl, h, Scheme.Hom.coe_preimage,
    show ((I.support.compl : S.Opens) : Set S) = (I.support : Set S)ᶜ from rfl,
    Set.preimage_compl]

/-- The exceptional complement of a blowup is retrocompact: its inclusion is affine, because the
exceptional divisor is an effective Cartier divisor ([Stacks, Tag 07ZU]), hence quasi-compact. -/
public theorem isRetrocompact_compl_support_exceptionalIdeal (I : S.IdealSheafData) :
    IsRetrocompact ((((exceptionalIdeal I).support.compl : (blowUp I).Opens)) :
      Set (blowUp I)) := by
  have : IsAffineHom (Scheme.Opens.ι (exceptionalIdeal I).support.compl) :=
    Stacks.Divisors.isAffineHom_compl_of_isEffectiveCartierDivisor _
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I)
  exact Stacks.StrictTransform.isRetrocompact_of_quasiCompact_ι _

/-! ### The strict transform away from the centre -/

/-- **Away from the centre the strict transform of `X` is an isomorphism onto the blowup.**
The morphism `AlgebraicGeometry.strictTransformToBlowUp` is the closed immersion of the strict
transform into `X ×_S S'` followed by the projection to the blowup. Over the exceptional
complement the first factor is an isomorphism, because the strict transform is the
scheme-theoretic image of that open; and the projection is an isomorphism there because it is a
base change of `f` along a morphism landing in the complement of the centre. -/
public theorem isIso_morphismRestrict_strictTransformToBlowUp (f : X ⟶ S)
    (I : S.IdealSheafData) (hf : IsIso (f ∣_ (I.support.compl : S.Opens))) :
    IsIso (strictTransformToBlowUp f I ∣_
      (blowUpToBase I ⁻¹ᵁ (I.support.compl : S.Opens) : (blowUp I).Opens)) := by
  let := hf
  -- The projection of the base change is an isomorphism over the inverse image of the
  -- complement of the centre.
  have hsnd : IsIso (pullback.snd f (blowUpToBase I) ∣_
      (blowUpToBase I ⁻¹ᵁ (I.support.compl : S.Opens) : (blowUp I).Opens)) := by
    have h := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f (blowUpToBase I))
      (US := (I.support.compl : S.Opens))
      (UT := (blowUpToBase I ⁻¹ᵁ (I.support.compl : S.Opens) : (blowUp I).Opens))
      (UX := f ⁻¹ᵁ (I.support.compl : S.Opens)) le_rfl le_rfl
      (UY := pullback.snd f (blowUpToBase I) ⁻¹ᵁ
        (blowUpToBase I ⁻¹ᵁ (I.support.compl : S.Opens) : (blowUp I).Opens))
      (by
        rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
        exact (inf_idem _).symm)
    have : IsIso (f.resLE (I.support.compl : S.Opens) (f ⁻¹ᵁ (I.support.compl : S.Opens))
        le_rfl) := by
      rw [Scheme.Hom.resLE_eq_morphismRestrict]
      infer_instance
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using h.isIso_snd_of_isIso
  -- The closed immersion of the strict transform is an isomorphism over the exceptional
  -- complement.
  have hfst : IsIso ((Stacks.StrictTransform.ideal f (blowUpToBase I)
      (exceptionalIdeal I)).subschemeι ∣_
        (pullback.snd f (blowUpToBase I) ⁻¹ᵁ
          (blowUpToBase I ⁻¹ᵁ (I.support.compl : S.Opens) : (blowUp I).Opens))) := by
    rw [← Stacks.StrictTransform.exceptionalComplement_blowUp f I,
      Stacks.StrictTransform.ideal_eq_ker_ι]
    exact Stacks.SchemeTheoreticImage.isIso_imageι_restrict _
  rw [show strictTransformToBlowUp f I =
      (Stacks.StrictTransform.ideal f (blowUpToBase I) (exceptionalIdeal I)).subschemeι ≫
        pullback.snd f (blowUpToBase I) from rfl, morphismRestrict_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hfst hsnd

/-! ### The strict transform of a flat morphism -/

/-- **The strict transform of a flat morphism is flat over the blowup, for an arbitrary centre.**
The strict transform of the structure sheaf is flat over the blowup
(`AlgebraicGeometry.isFlatOver_strictTransformSheaf_of_isFlatOver`, which is
[Stacks, Tag 080F] part (2) together with stability of flatness under base change), and
`AlgebraicGeometry.flat_strictTransformToBlowUp_iff` reads that as flatness of the strict
transform of `X`. -/
public theorem flat_strictTransformToBlowUp_of_flat (f : X ⟶ S) [Flat f]
    (I : S.IdealSheafData) : Flat (strictTransformToBlowUp f I) :=
  (flat_strictTransformToBlowUp_iff f I).mpr
    (isFlatOver_strictTransformSheaf_of_isFlatOver f I X.unitModule fun x ↦
      (isFlatOverAt_unit_iff_isFlatAt f x).mpr ((Flat.iff_flat_stalkMap f).mp inferInstance x))

/-! ### Tag 081S granted the flatness of the strict transform -/

/-- An open is the complement of the support of a centre if that support is its complement. -/
private theorem eq_compl_support_of_support_eq_compl (I : S.IdealSheafData) (U : S.Opens)
    (h : (I.support : Set S) = (U : Set S)ᶜ) : U = I.support.compl :=
  TopologicalSpace.Opens.ext (by rw [← compl_compl (U : Set S), ← h]; rfl)

/-- **The conclusion of [Stacks, Tag 081S], granted the flatness of the strict transform over a
boundary centre.** Let `f : X ⟶ S` be separated and locally of finite type and let `U ⊆ S` be an
open over which `f` is an isomorphism. Let `I` be a finitely presented centre whose support is
exactly the complement of `U`, and suppose the strict transform of `X` along the blowup of `S`
in `I` is flat over that blowup. Then that blowup witnesses
`AlgebraicGeometry.StrictTransformOpenImmersion`.

The inverse image of `U` in the blowup is the complement of the exceptional divisor, hence
scheme-theoretically dense and retrocompact ([Stacks, Tag 07ZU]), and the strict transform is an
isomorphism over it; so [Stacks, Tag 081M] applies.

No `@[stacks 081S]` attribute: the flatness hypothesis is the conclusion of the cited
[Stacks, Tag 081R], which this development does not prove. See the module documentation. -/
public theorem strictTransformOpenImmersion_of_flat_strictTransform (f : X ⟶ S) [IsSeparated f]
    [LocallyOfFiniteType f] (U : S.Opens) (I : S.IdealSheafData)
    (hIfp : FinitePresentation I.subschemeι) (hIU : U = I.support.compl)
    (hf : IsIso (f ∣_ U)) (hflat : Flat (strictTransformToBlowUp f I)) :
    StrictTransformOpenImmersion f U := by
  subst hIU
  let := hf
  let := hflat
  refine ⟨I, hIfp, disjoint_compl_left, ?_⟩
  have hdense : Scheme.Opens.IsSchemeTheoreticallyDense
      (blowUpToBase I ⁻¹ᵁ (I.support.compl : S.Opens) : (blowUp I).Opens) := by
    rw [preimage_compl_support_eq_compl_support_exceptionalIdeal I]
    exact Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor _
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I)
  have hretro : IsRetrocompact
      ((blowUpToBase I ⁻¹ᵁ (I.support.compl : S.Opens) : (blowUp I).Opens) :
        Set (blowUp I)) := by
    rw [preimage_compl_support_eq_compl_support_exceptionalIdeal I]
    exact isRetrocompact_compl_support_exceptionalIdeal I
  let := isIso_morphismRestrict_strictTransformToBlowUp f I hf
  exact isOpenImmersion_of_isIso_morphismRestrict (strictTransformToBlowUp f I)
    (blowUpToBase I ⁻¹ᵁ (I.support.compl : S.Opens)) hretro hdense

/-- **The conclusion of [Stacks, Tag 081S] for a flat morphism, with nothing carried.** On a
quasi-compact quasi-separated scheme `S`, a flat separated morphism `f : X ⟶ S` locally of finite
type which is an isomorphism over a quasi-compact open `U` admits a `U`-admissible blowup along
which the strict transform of `X` is an open subscheme.

A finite type centre supported exactly on `S ∖ U` exists by [Stacks, Tag 01PH]
(`AlgebraicGeometry.exists_isFiniteType_idealSheafData_support_eq_compl`) and is finitely
presented as a closed subscheme (`Stacks.Flatness.finitePresentation_subschemeι_iff`); the strict
transform of a flat morphism is flat over any blowup
(`AlgebraicGeometry.flat_strictTransformToBlowUp_of_flat`).

No `@[stacks 081S]` attribute: flatness of `f` is an extra hypothesis the source does not make,
and is exactly the case in which the flattening step of the source's proof is vacuous. -/
public theorem strictTransformOpenImmersion_of_flat (f : X ⟶ S) [CompactSpace S]
    [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f] [Flat f] (U : S.Opens)
    (hU : IsCompact (U : Set S)) (hf : IsIso (f ∣_ U)) :
    StrictTransformOpenImmersion f U := by
  obtain ⟨I, hIft, hIsupp⟩ := exists_isFiniteType_idealSheafData_support_eq_compl U hU
  refine strictTransformOpenImmersion_of_flat_strictTransform f U I
    ((Stacks.Flatness.finitePresentation_subschemeι_iff I).mpr hIft) ?_ hf
    (flat_strictTransformToBlowUp_of_flat f I)
  exact eq_compl_support_of_support_eq_compl I U hIsupp

/-! ### The composite centre supported on the whole boundary -/

/-- **A finitely presented centre supported exactly on `S ∖ U` whose strict transform is flat,
from one that is merely supported away from `U`.** The hypotheses on `I` are the conclusion of
[Stacks, Tag 081R]; the centre produced is the composite `I · J` with the centre `J` of finite
type cutting out `S ∖ U` ([Stacks, Tag 01PH]).

By [Stacks, Tag 080B] part (2) the blowup of `S` in `I · J` is the blowup of `Bl_I(S)` in
`J·𝒪_{Bl_I(S)}` over `S`, and the support of `I · J` is that of `J`, which is `S ∖ U`, because
`I` is supported away from `U`. By [Stacks, Tag 080I] part (2) the strict transform of `X` along
the blowup in `I · J` is the strict transform along the second blowup of the strict transform
along the first, which is flat over `Bl_I(S)` by hypothesis; so the twice-transformed scheme is
flat by `AlgebraicGeometry.flat_strictTransformToBlowUp_of_flat`, and flatness transports along
the identification. -/
public theorem exists_flat_strictTransformToBlowUp_support_eq_compl (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] (U : S.Opens) (hU : IsCompact (U : Set S))
    (I : S.IdealSheafData) (hIfp : FinitePresentation I.subschemeι)
    (hIdisj : Disjoint (U : Set S) (I.support : Set S))
    (hflat : Flat (strictTransformToBlowUp f I)) :
    ∃ K : S.IdealSheafData, FinitePresentation K.subschemeι ∧
      ((K.support : Set S) = (U : Set S)ᶜ) ∧ Flat (strictTransformToBlowUp f K) := by
  let := hflat
  obtain ⟨J, hJft, hJsupp⟩ := exists_isFiniteType_support_eq_compl S U hU
  have hcomap : J.comap (blowUpToBase I) =
      exceptionalIdeal I ^ 0 * J.comap (blowUpToBase I) := by rw [pow_zero, one_mul]
  obtain ⟨e⟩ := nonempty_blowUpCompositionIso I (J.comap (blowUpToBase I)) 0 J hcomap
  have hKsupport : (I * J).supportSet = I.supportSet ∪
      (blowUpToBase I).base '' (J.comap (blowUpToBase I)).supportSet :=
    supportSet_mul_eq_union_image I (J.comap (blowUpToBase I)) 0 J hcomap
  have hKfp : FinitePresentation (I * J).subschemeι :=
    finitePresentation_mul_subschemeι I J hIfp hJft
  -- the support of the composite centre is the whole complement of `U`
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
  -- the twice-transformed scheme is flat, and flatness transports to the composite centre
  have hflat₂ : Flat (strictTransformToBlowUp (strictTransformToBlowUp f I)
      (J.comap (blowUpToBase I))) := flat_strictTransformToBlowUp_of_flat _ _
  obtain ⟨g, -, hg⟩ :=
    Stacks.StrictTransform.strictTransform_comp_blowUp f I (I * J)
      (J.comap (blowUpToBase I)) hKsupport e
  have _ : IsIso e.hom.left :=
    ⟨e.inv.left, Over.hom_left_inv_left e, Over.inv_left_hom_left e⟩
  have hg' : g.hom ≫ strictTransformToBlowUp f (I * J) =
      strictTransformToBlowUp (strictTransformToBlowUp f I) (J.comap (blowUpToBase I)) ≫
        e.hom.left :=
    hg.trans (Category.assoc _ _ _).symm
  have hrFlat : MorphismProperty.RespectsIso @Flat :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine ⟨I * J, hKfp, ?_, ?_⟩
  · change (I * J).supportSet = (U : Set S)ᶜ
    rw [hKsuppJ]
    exact hJsupp
  · rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Flat) g.hom
      (strictTransformToBlowUp f (I * J)), hg',
      MorphismProperty.cancel_right_of_respectsIso (P := @Flat)]
    exact hflat₂

/-! ### Tag 081S granted the cited flattening -/

/-- **The conclusion of [Stacks, Tag 081S] from the conclusion of the cited [Stacks, Tag 081R].**
Let `S` be quasi-compact and quasi-separated, let `f : X ⟶ S` be separated and locally of finite
type and let `U ⊆ S` be a quasi-compact open over which `f` is an isomorphism. Given a finitely
presented centre `I` supported away from `U` along whose blowup the strict transform of `X` is
flat, `AlgebraicGeometry.StrictTransformOpenImmersion` holds.

The centre is first replaced by one supported on the whole of `S ∖ U`
(`AlgebraicGeometry.exists_flat_strictTransformToBlowUp_support_eq_compl`), and then
`AlgebraicGeometry.strictTransformOpenImmersion_of_flat_strictTransform` applies. -/
public theorem strictTransformOpenImmersion_of_flat_strictTransform_of_disjoint (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]
    (U : S.Opens) (hU : IsCompact (U : Set S)) (hf : IsIso (f ∣_ U)) (I : S.IdealSheafData)
    (hIfp : FinitePresentation I.subschemeι) (hIdisj : Disjoint (U : Set S) (I.support : Set S))
    (hflat : Flat (strictTransformToBlowUp f I)) :
    StrictTransformOpenImmersion f U := by
  obtain ⟨K, hKfp, hKsupp, hKflat⟩ :=
    exists_flat_strictTransformToBlowUp_support_eq_compl f U hU I hIfp hIdisj hflat
  refine strictTransformOpenImmersion_of_flat_strictTransform f U K hKfp ?_ hf hKflat
  exact eq_compl_support_of_support_eq_compl K U hKsupp

/-- **The conclusion of [Stacks, Tag 081S], granted only the affine case of the cited flattening
theorem [Stacks, Tag 0815].** Let `S` be quasi-compact and quasi-separated, let `f : X ⟶ S` be
separated, quasi-compact, quasi-separated and locally of finite type, and let `U ⊆ S` be a
quasi-compact open over which `f` is an isomorphism. Granted
`AlgebraicGeometry.AffineChartFlatteningCentre` for the structure sheaf of `X` — which is what
the library's [Stacks, Tag 081R] carries, and all it carries — the strict transform of `X` is an
open subscheme of a `U`-admissible blowup.

This is the source's proof: flatten by [Stacks, Tag 081R], enlarge the centre to the whole
boundary, and apply [Stacks, Tag 081M].

No `@[stacks 081S]` attribute: `AffineChartFlatteningCentre` is a hypothesis the source does not
make, and tag 081S asserts its conclusion outright. See the module documentation. -/
public theorem strictTransformOpenImmersion_of_affineChartFlatteningCentre (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [QuasiSeparated f] (U : S.Opens) (hU : IsCompact (U : Set S))
    (hf : IsIso (f ∣_ U)) (H : AffineChartFlatteningCentre f X.unitModule U) :
    StrictTransformOpenImmersion f U := by
  obtain ⟨I, hIfp, hIdisj, -, hflat⟩ := exists_isAdmissibleBlowup_flat_strictTransform f U hU H
  exact strictTransformOpenImmersion_of_flat_strictTransform_of_disjoint f U hU hf I hIfp
    hIdisj hflat

end AlgebraicGeometry

end
