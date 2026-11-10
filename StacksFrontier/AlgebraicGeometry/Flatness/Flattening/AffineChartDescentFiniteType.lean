module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderEquivalence
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.AffinePushforward
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FiniteTypePushforward
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FinitePushforward
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.StructureSheafProjectiveSections
public import StacksFrontier.AlgebraicGeometry.FiniteTypeClosedInFinitePresentation.QuasiAffine
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.AffineChartDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibreFreeBlowup0811
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformSchemeFlattening
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.AffinePushforward
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.PointwiseOpenLocus
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The affine case of tag 0815 for a morphism locally of finite type

Hypothesis (2) of [Stacks, Tag 0815] asks for a morphism locally of finite **presentation**,
while the flattening statements that consume the affine case of its flatness assertion —
[Stacks, Tags 081R, 081S, 081T, 0B49, 0CP1, 0F3W, 0F3Z] and, through them, [Stacks, Tag 0EVC] —
have a morphism only locally of finite **type**, flat and locally of finite presentation over the
open `U`. This file makes the affine case applicable to such a morphism, by the route the source
itself takes: [Stacks, Tag 04II] immerses the chart over the base into a relative affine space,
[Stacks, Tag 01ZG] turns that immersion into a closed immersion `i` into a scheme `Z` of finite
presentation over the base, the affine case is applied to `Z` and the direct image `i_* M`, and
[Stacks, Tag 080G] carries the flatness it produces back to the strict transform of `M`.

The affine case itself is not assumed here. It is
`AlgebraicGeometry.AffineChartFlatteningCentreUnderSourceHypotheses.of_compactSpace`, which is
that case for an arbitrary quasi-coherent module over a quasi-compact, quasi-separated base, with
nothing granted; `Z` and `T` are quasi-compact and `T` is quasi-separated at the one place the
affine case is used, so nothing here carries it as a hypothesis.

## Main results

* `AlgebraicGeometry.exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_isQuasiAffine`:
  the flatness assertion of [Stacks, Tag 0815] for a morphism `g : Y ⟶ T` with `Y` quasi-affine
  which is only locally of finite **type**, provided it is locally of finite presentation over
  the open `A`. This is the form a morphism locally of finite type can consume.
* `AlgebraicGeometry.AffineChartFlatteningCentre.of_affineCase`: consequently, the
  hypothesis-free affine-chart predicate holds for the structure sheaf of a scheme locally of
  finite type over a quasi-separated base, flat and locally of finite presentation over `U`,
  unconditionally. This is what the eight tags above need: each has been restated with its own
  source hypothesis (2) present, and this is what produces
  `AlgebraicGeometry.AffineChartFlatteningCentre f 𝒪_X U` for them without assuming `f`
  locally of finite presentation.
* `AlgebraicGeometry.exists_isAdmissibleBlowup_flat_strictTransform_of_affineCase`: the flatness
  assertion of [Stacks, Tag 081R] under exactly the source's hypotheses, carrying nothing.
  No tag: the whole of [Stacks, Tag 081R] — both clauses of its conclusion — is
`AlgebraicGeometry.exists_isAdmissibleBlowup_flat_finitePresentation_strictTransform_of_affineCase`
  of
`StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformFinitePresentationFromFlat`,
  which is where that tag is registered.
* `AlgebraicGeometry.morphismRestrict_resLE_of_morphismRestrict`: a morphism property local at
  the source and right-cancellable along monomorphisms passes from the restriction of `f` over
  `U` to the restriction, over `U ∩ V`, of the restriction of `f` to a pair of opens
  `W ⊆ f⁻¹(V)`. This is how hypothesis (2) of [Stacks, Tag 081R] reaches the charts.

## Implementation notes

The source's route is taken only once, on the chart, and it is taken for an arbitrary
quasi-coherent module of finite type rather than for the structure sheaf: quasi-affineness of the
source is used only for [Stacks, Tag 04II], and the hypotheses the affine case needs of `i_* M`
over the open `A` are exactly the hypotheses `M` has there.

Finiteness of `i_* M` over `A` is where hypothesis (2) of [Stacks, Tag 081R] — `g` locally of
finite presentation over `A`, rather than everywhere — is used, and it is the only place: the
closed immersion `i` restricted over `A` is locally of finite presentation by [Stacks, Tag 02FV]
(`AlgebraicGeometry.locallyOfFinitePresentation_of_comp`), because its composite with the
restriction of `Z ⟶ T` is the restriction of `g`, which is locally of finite presentation, and
`Z ⟶ T` is locally of finite type; being also finite it is of finite presentation, so
[Stacks, Tag 05B4] (`AlgebraicGeometry.isFinitePresentation_iff_pushforward_isFinitePresentation`)
carries finite presentation of `M` over `A` to `i_* M`. Flatness over `A` travels by
[Stacks, Tag 0FLM] (`AlgebraicGeometry.isFlatOver_pushforward_iff`), and both use
`Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`, that restriction to an open
of the target commutes with the direct image.

The conclusion comes back along [Stacks, Tag 080G]
(`AlgebraicGeometry.strictTransformSheafPushforwardIso`) and [Stacks, Tag 0FLM] again, applied to
the base change of `i`, which is affine.

`AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource` is not found by instance
resolution, the ring-homomorphism property not being determined by the morphism property, so the
two instances of it used here are named.

No tag is registered here. [Stacks, Tag 0815] is registered, in full and on its own hypotheses
alone, on
`AlgebraicGeometry.exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_affineCharts`
of `StacksFrontier/AlgebraicGeometry/Flatness/Flattening/ModuleFlatteningBlowup.lean`; what is
proved here is that tag's flatness assertion for the weaker hypothesis (2) of
[Stacks, Tag 081R], for a quasi-affine source.
[Stacks, Tag 081R] in full is
`AlgebraicGeometry.exists_isAdmissibleBlowup_flat_finitePresentation_strictTransform_of_affineCase`
of
`StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformFinitePresentationFromFlat`.
[Stacks, Tag 081R] itself needs, beyond this, the step that dominates finitely many
blowups by one — the first paragraph of its proof — which is not treated here; what is treated is
exactly what the affine-chart predicate asks for, the source of a chart being affine.

## References

* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 081R](https://stacks.math.columbia.edu/tag/081R)
* [Stacks Project, Tag 04II](https://stacks.math.columbia.edu/tag/04II)
* [Stacks Project, Tag 01ZG](https://stacks.math.columbia.edu/tag/01ZG)
* [Stacks Project, Tag 02FV](https://stacks.math.columbia.edu/tag/02FV)
* [Stacks Project, Tag 05B4](https://stacks.math.columbia.edu/tag/05B4)
* [Stacks Project, Tag 080G](https://stacks.math.columbia.edu/tag/080G)
* [Stacks Project, Tag 0FLM](https://stacks.math.columbia.edu/tag/0FLM)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Flatness is local at the source. The instance
`AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource` does not fire on its own, the
ring-homomorphism property not being an output of the morphism property. -/
@[sga "4 IV 8.5.5" "special case"]
private theorem isZariskiLocalAtSource_flat : IsZariskiLocalAtSource @Flat.{u} :=
  HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Flat.{u, u})

/-- Being locally of finite presentation is local at the source. -/
@[sga "4 IV 8.5.5" "special case"]
private theorem isZariskiLocalAtSource_locallyOfFinitePresentation :
    IsZariskiLocalAtSource @LocallyOfFinitePresentation.{u} :=
  HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.FinitePresentation.{u, u})

/-- A morphism property stable under base change is right-cancellable along monomorphisms: the
first factor is the base change of the composite along the second. -/
@[ega "I 5.5.12" "(v), special case"]
private theorem hasOfPostcompProperty_monomorphisms (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] :
    P.HasOfPostcompProperty (MorphismProperty.monomorphisms Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.hasOfPostcompProperty_monomorphisms

/-- **A morphism property local at the source reaches the charts of a restriction.** Let `P` be
local at the source and right-cancellable along monomorphisms, and suppose `P` holds for the
restriction `f ∣_ U` of `f : X ⟶ S` over an open `U` of `S`. Then `P` holds for the restriction
over `U ∩ V` of the restriction of `f` to any pair of opens `W ⊆ f⁻¹(V)`.

Both `AlgebraicGeometry.Flat` and `AlgebraicGeometry.LocallyOfFinitePresentation` qualify: they
are local at the source and stable under base change.

The composite of the morphism in question with the open immersion `U ∩ V ⟶ U` is the composite of
the open immersion `W ∩ f⁻¹(U) ⟶ f⁻¹(U)` with `f ∣_ U`, which has `P` because `P` is local at the
source; cancelling the first open immersion, a monomorphism, gives the claim. -/
theorem morphismRestrict_resLE_of_morphismRestrict {P : MorphismProperty Scheme.{u}}
    (hsrc : IsZariskiLocalAtSource P)
    (hcancel : P.HasOfPostcompProperty (MorphismProperty.monomorphisms Scheme.{u}))
    {X S : Scheme.{u}} (f : X ⟶ S) {U V : S.Opens} {W : X.Opens} (e : W ≤ f ⁻¹ᵁ V)
    (hf : P (f ∣_ U)) :
    P (f.resLE V W e ∣_ V.ι ⁻¹ᵁ U) := by
  have _ := hsrc
  have _ := hcancel
  have hB : f.resLE V W e ⁻¹ᵁ (V.ι ⁻¹ᵁ U) ≤ W.ι ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    rw [Scheme.Hom.resLE_preimage]
    exact W.ι.preimage_mono (f.preimage_mono (V.ι.image_preimage_le U))
  have hoi : IsOpenImmersion (V.ι.resLE U (V.ι ⁻¹ᵁ U) le_rfl) := by
    delta Scheme.Hom.resLE
    infer_instance
  refine MorphismProperty.of_postcomp (W' := MorphismProperty.monomorphisms Scheme.{u}) P _
    (V.ι.resLE U (V.ι ⁻¹ᵁ U) le_rfl) (inferInstanceAs (Mono _)) ?_
  have key : (f.resLE V W e ∣_ V.ι ⁻¹ᵁ U) ≫ V.ι.resLE U (V.ι ⁻¹ᵁ U) le_rfl =
      W.toScheme.homOfLE hB ≫ (W.ι ∣_ f ⁻¹ᵁ U) ≫ f ∣_ U := by
    rw [← cancel_mono U.ι]
    simp
  rw [key]
  exact IsZariskiLocalAtSource.comp (IsZariskiLocalAtSource.comp hf _) _

/-- **Stacks Project, Tag 0815, flatness assertion, for a morphism locally of finite type with
quasi-affine source.** Let `T` be quasi-compact and quasi-separated, let `g : Y ⟶ T` be locally
of finite type with `Y` quasi-affine, let `M` be a quasi-coherent `𝒪_Y`-module of finite type and
let `A ⊆ T` be a quasi-compact open over which `g` is locally of finite presentation and `M` is
of finite presentation and flat. Then there is a centre `I` on `T`, finitely presented and
supported away from `A`, exhibiting the blowup of `T` in `I` as an `A`-admissible blowup, along
which the strict transform of `M` is flat.

The affine case this consumes is
`AlgebraicGeometry.AffineChartFlatteningCentreUnderSourceHypotheses.of_compactSpace`, which is
unconditional. It is applied not to `g` but to the scheme `Z` of finite presentation
over `T` that [Stacks, Tag 01ZG] produces, and not to `M` but to its direct image along the
closed immersion `Y ⟶ Z`; the base `T` and the source `Z` are quasi-compact and `T` is
quasi-separated, so that theorem's hypotheses are the ones assumed here.

This is hypothesis (2) of the source — `g` locally of finite presentation — replaced by
hypothesis (2) of [Stacks, Tag 081R]: `g` locally of finite type, and locally of finite
presentation over `A`. The replacement is what makes the statement usable by the flattening
statements for morphisms of finite type, and it adds no hypothesis anywhere: a morphism locally
of finite presentation is locally of finite type, and its restriction over `A` is locally of
finite presentation.

`Y` quasi-affine is what [Stacks, Tag 04II] needs, and is all the affine-chart predicate
`AlgebraicGeometry.AffineChartFlatteningCentre` ever asks for, its charts being affine. -/
theorem exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_isQuasiAffine
    {T Y : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T] (g : Y ⟶ T) [Y.IsQuasiAffine]
    [LocallyOfFiniteType g] (M : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (A : T.Opens)
    (hA : IsCompact (A : Set T)) (hgA : LocallyOfFinitePresentation (g ∣_ A))
    (hMfp : (M.restrict (g ⁻¹ᵁ A).ι).IsFinitePresentation)
    (hMflat : IsFlatOver (g.resLE A (g ⁻¹ᵁ A) le_rfl).toLRSHom.toShHom (M.restrict (g ⁻¹ᵁ A).ι)) :
    ∃ I : T.IdealSheafData,
      FinitePresentation I.subschemeι ∧
      Disjoint (A : Set T) (I.support : Set T) ∧
      Stacks.Blowup.IsAdmissibleBlowup A (blowUpToBase I) ∧
      IsFlatOver (pullback.snd g (blowUpToBase I)).toLRSHom.toShHom
        (Stacks.StrictTransform.sheaf g (blowUpToBase I) (exceptionalIdeal I) M) := by
  obtain ⟨Z, p, i, hp, hi, hip⟩ := exists_finitePresentation_isClosedImmersion_of_isQuasiAffine g
  have _ : IsClosedImmersion i := hi
  have _ : LocallyOfFinitePresentation p := hp.1
  have _ : QuasiCompact p := hp.2.1
  have _ : QuasiSeparated p := hp.2.2
  have _ : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace p
  subst hip
  have hMflat' : IsFlatOver ((i ≫ p) ∣_ A).toLRSHom.toShHom (M.restrict ((i ≫ p) ⁻¹ᵁ A).ι) := by
    rwa [← Scheme.Hom.resLE_eq_morphismRestrict]
  have _ : ((Scheme.Modules.pushforward i).obj M).IsFiniteType :=
    isFiniteType_pushforward_of_isFinite' i M
  have hjfp : FinitePresentation (i ∣_ p ⁻¹ᵁ A) := by
    have hcomp : LocallyOfFinitePresentation ((i ∣_ p ⁻¹ᵁ A) ≫ p ∣_ A) := by
      rwa [← morphismRestrict_comp]
    exact ⟨locallyOfFinitePresentation_of_comp (i ∣_ p ⁻¹ᵁ A) (p ∣_ A), inferInstance,
      inferInstance⟩
  have hGfp : (((Scheme.Modules.pushforward i).obj M).restrict (p ⁻¹ᵁ A).ι).IsFinitePresentation :=
    Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso.{u, u, u}
      ((Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso i (p ⁻¹ᵁ A)).app M).symm
      ((isFinitePresentation_iff_pushforward_isFinitePresentation (i ∣_ p ⁻¹ᵁ A) hjfp _).mp hMfp)
  have hGflat : IsFlatOver (p.resLE A (p ⁻¹ᵁ A) le_rfl).toLRSHom.toShHom
      (((Scheme.Modules.pushforward i).obj M).restrict (p ⁻¹ᵁ A).ι) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    refine (isFlatOver_iff_of_moduleIso _
      ((Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso i
        (p ⁻¹ᵁ A)).app M)).mpr ?_
    refine (isFlatOver_pushforward_iff (i ∣_ p ⁻¹ᵁ A) (p ∣_ A) _).mp ?_
    rwa [← morphismRestrict_comp]
  obtain ⟨I, hIfp, hIdisj, hIadm, hIflat⟩ :=
    exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_affineCase p
      ((Scheme.Modules.pushforward i).obj M) A hA hGfp hGflat
      (AffineChartFlatteningCentreUnderSourceHypotheses.of_compactSpace p
        ((Scheme.Modules.pushforward i).obj M) A hA)
  refine ⟨I, hIfp, hIdisj, hIadm, ?_⟩
  have _ : (Stacks.StrictTransform.sheaf (i ≫ p) (blowUpToBase I)
      (exceptionalIdeal I) M).IsQuasicoherent := inferInstance
  have h1 := (isFlatOver_iff_of_moduleIso (pullback.snd p (blowUpToBase I)).toLRSHom.toShHom
    (strictTransformSheafPushforwardIso i p I M)).mpr hIflat
  have h2 := (isFlatOver_pushforward_iff (baseChangeInducedMap i p (blowUpToBase I))
    (pullback.snd p (blowUpToBase I))
    (Stacks.StrictTransform.sheaf (i ≫ p) (blowUpToBase I) (exceptionalIdeal I) M)).mpr h1
  rwa [baseChangeInducedMap_snd] at h2

/-- **The affine-chart case of the flatness assertion of [Stacks, Tag 0815] for the structure
sheaf of a scheme locally of finite type.** Let `S` be quasi-separated, let `f : X ⟶ S` be
locally of finite type and let `U ⊆ S` be a quasi-compact open over which `f` is flat and locally
of finite presentation. Then every pair of affine charts `W ⊆ f⁻¹(V)` carries a flattening
centre for `𝒪_X`, that is, `AlgebraicGeometry.AffineChartFlatteningCentre f 𝒪_X U` holds.

That predicate is what the restored forms of
[Stacks, Tags 081R, 081S, 081T, 0B49, 0CP1, 0F3W, 0F3Z] and [Stacks, Tag 0EVC] are proved from:
their morphisms are of finite *type*, so hypothesis (2) of [Stacks, Tag 0815] is unavailable to
them and `AlgebraicGeometry.AffineChartFlatteningCentreUnderSourceHypotheses` cannot be applied
to their `f`. A chart is affine, hence quasi-affine, so
`AlgebraicGeometry.exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_isQuasiAffine`
applies to it; its hypotheses on the module are satisfied by the structure sheaf, which is of
finite presentation (`AlgebraicGeometry.Scheme.unitModule_isFinitePresentation`), and whose
flatness over the chart of `U` is flatness of the morphism there
(`AlgebraicGeometry.isFlatOverAt_unit_iff_isFlatAt`), which
`AlgebraicGeometry.morphismRestrict_resLE_of_morphismRestrict` carries from `f ∣_ U` to the
chart. -/
theorem AffineChartFlatteningCentre.of_affineCase {S X : Scheme.{u}} [QuasiSeparatedSpace S]
    (f : X ⟶ S) [LocallyOfFiniteType f] (U : S.Opens) (hU : IsCompact (U : Set S))
    (hflat : Flat (f ∣_ U)) (hfp : LocallyOfFinitePresentation (f ∣_ U)) :
    AffineChartFlatteningCentre f X.unitModule U := by
  intro V W hVW
  have _ : IsAffine V.1.toScheme := V.2
  have _ : IsAffine W.1.toScheme := W.2
  have _ : QuasiCompact V.1.ι := quasiCompact_ι_of_isCompact V.1 V.2.isCompact
  have hAc : IsCompact ((V.1.ι ⁻¹ᵁ U : V.1.toScheme.Opens) : Set V.1.toScheme) :=
    V.1.ι.isCompact_preimage hU
  have hgflat : Flat (f.resLE V.1 W.1 hVW ∣_ V.1.ι ⁻¹ᵁ U) :=
    morphismRestrict_resLE_of_morphismRestrict isZariskiLocalAtSource_flat
      (hasOfPostcompProperty_monomorphisms @Flat.{u}) f hVW hflat
  have hgfp : LocallyOfFinitePresentation (f.resLE V.1 W.1 hVW ∣_ V.1.ι ⁻¹ᵁ U) :=
    morphismRestrict_resLE_of_morphismRestrict
      isZariskiLocalAtSource_locallyOfFinitePresentation
      (hasOfPostcompProperty_monomorphisms @LocallyOfFinitePresentation.{u}) f hVW hfp
  have _ : (W.1.toScheme.unitModule).IsFiniteType :=
    inferInstanceAs (SheafOfModules.unit W.1.toScheme.ringCatSheaf).IsFiniteType
  have hiso : (Scheme.Modules.pullback W.1.ι).obj X.unitModule ≅ W.1.toScheme.unitModule :=
    ((Scheme.Modules.restrictFunctorIsoPullback W.1.ι).app X.unitModule).symm ≪≫
      Scheme.Modules.restrictUnitIso W.1.ι
  have _ : ((Scheme.Modules.pullback W.1.ι).obj X.unitModule).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback W.1.ι X.unitModule inferInstance
  have _ : ((Scheme.Modules.pullback W.1.ι).obj X.unitModule).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} hiso.symm
  have hisoD : ((Scheme.Modules.pullback W.1.ι).obj X.unitModule).restrict
        (f.resLE V.1 W.1 hVW ⁻¹ᵁ V.1.ι ⁻¹ᵁ U).ι ≅
      (f.resLE V.1 W.1 hVW ⁻¹ᵁ V.1.ι ⁻¹ᵁ U).toScheme.unitModule :=
    (Scheme.Modules.restrictFunctor _).mapIso hiso ≪≫ Scheme.Modules.restrictUnitIso _
  have hMfp : (((Scheme.Modules.pullback W.1.ι).obj X.unitModule).restrict
      (f.resLE V.1 W.1 hVW ⁻¹ᵁ V.1.ι ⁻¹ᵁ U).ι).IsFinitePresentation :=
    Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso.{u, u, u} hisoD.symm
      (Scheme.unitModule_isFinitePresentation _)
  have hMflat : IsFlatOver ((f.resLE V.1 W.1 hVW).resLE (V.1.ι ⁻¹ᵁ U)
        (f.resLE V.1 W.1 hVW ⁻¹ᵁ V.1.ι ⁻¹ᵁ U) le_rfl).toLRSHom.toShHom
      (((Scheme.Modules.pullback W.1.ι).obj X.unitModule).restrict
        (f.resLE V.1 W.1 hVW ⁻¹ᵁ V.1.ι ⁻¹ᵁ U).ι) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact (isFlatOver_iff_of_moduleIso _ hisoD).mpr fun z ↦
      (isFlatOverAt_unit_iff_isFlatAt _ z).mpr ((Flat.iff_flat_stalkMap _).mp hgflat z)
  obtain ⟨I, hIfp, hIdisj, -, hIflat⟩ :=
    exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_isQuasiAffine
      (f.resLE V.1 W.1 hVW) ((Scheme.Modules.pullback W.1.ι).obj X.unitModule)
      (V.1.ι ⁻¹ᵁ U) hAc hgfp hMfp hMflat
  exact ⟨I, hIfp, hIdisj, hIflat⟩

/-- **The flatness assertion of [Stacks, Tag 081R] under exactly the source's hypotheses.** Let
`S` be quasi-compact and quasi-separated, let `f : X ⟶ S` be of finite type and quasi-separated
and let `U ⊆ S` be a quasi-compact open over which `f` is flat and locally of finite
presentation. Then some `U`-admissible blowup of `S` flattens the strict transform of `X`.

No tag is registered here: this is the flatness clause alone, and [Stacks, Tag 081R] asserts
finite presentation of the strict transform as well. The tag in full is
`AlgebraicGeometry.exists_isAdmissibleBlowup_flat_finitePresentation_strictTransform_of_affineCase`
of
`StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformFinitePresentationFromFlat`,
which states both clauses under these same hypotheses.

The chart predicate comes from
`AlgebraicGeometry.AffineChartFlatteningCentre.of_affineCase`, which needs precisely hypothesis
(2) of the source — `X_U ⟶ U` flat and locally of finite presentation — and that hypothesis is
present here. [Stacks, Tags 081S, 081T, 0B49, 0CP1, 0F3W, 0F3Z] and [Stacks, Tag 0EVC] reach the
affine case through this one, each under its own source hypotheses. -/
theorem exists_isAdmissibleBlowup_flat_strictTransform_of_affineCase {S X : Scheme.{u}}
    [CompactSpace S] [QuasiSeparatedSpace S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    [QuasiSeparated f] (U : S.Opens) (hU : IsCompact (U : Set S)) (hflat : Flat (f ∣_ U))
    (hfp : LocallyOfFinitePresentation (f ∣_ U)) :
    ∃ I : S.IdealSheafData,
      FinitePresentation I.subschemeι ∧
      Disjoint (U : Set S) (I.support : Set S) ∧
      Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase I) ∧
      Flat (strictTransformToBlowUp f I) :=
  exists_isAdmissibleBlowup_flat_strictTransform f U hU
    (AffineChartFlatteningCentre.of_affineCase f U hU hflat hfp)

end AlgebraicGeometry

end
