module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactnessSheafify
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.AffinePushforward
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.ClosedImmersionIntoFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.PushforwardFinite
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FinitePushforward
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformSchemeFlattening
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.ClosedImmersion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flattening the strict transform of a scheme, with finite presentation

Let `S` be a quasi-compact and quasi-separated scheme, let `f : X ⟶ S` be of finite type and
quasi-separated and let `U ⊆ S` be a quasi-compact open over which `f` is flat and locally of
finite presentation. Then there is a `U`-admissible blowup `S' ⟶ S` along which the strict
transform of `X` is flat **and of finite presentation** over `S'`.

Both clauses of the conclusion of [Stacks, Tag 081R] are proved here, from the statement of
[Stacks, Tag 0815] carried as a hypothesis. This is the whole of the source's own argument for
tag 081R: embed `X` as a closed subscheme of a scheme `V` of finite presentation over `S`
([Stacks, Tag 01ZG]), apply tag 0815 to the direct image `i_*𝒪_X` on `V`, and carry the two
properties it produces back along the direct image, which commutes with strict transform
([Stacks, Tag 080G]).

## Main definitions

* `AlgebraicGeometry.FinitePresentationHasStrictTransformSheafFlatteningBlowup` is the statement
  of [Stacks, Tag 0815] in the spelling of [Stacks, Tag 080D]: the strict transform of the
  module is read on the base change `X ×_S S'`, which is where that tag puts it.

## Main results

* `AlgebraicGeometry.finitePresentation_strictTransformToBlowUp_iff`: the unconditional half of
  the finite-presentation clause of tag 081R — the strict transform is quasi-compact and
  quasi-separated over the blowup for free, so the clause *is* local finite presentation. This
  needs no flatness, no hypothesis on the centre and nothing of tag 0815.
* `AlgebraicGeometry.exists_isAdmissibleBlowup_flat_finitePresentation_strictTransform`:
  **[Stacks, Tag 081R]** in full — flatness *and* finite presentation of the strict transform —
  with the statement of tag 0815 carried as a hypothesis.
* `AlgebraicGeometry.exists_isAdmissibleBlowup_flat_locallyOfFinitePresentation_strictTransform`:
  the same conclusion in the shape the downstream tags consume it, with local finite presentation
  of the strict transform in place of finite presentation.

## Implementation notes

`X ⟶ S` is of finite type and quasi-separated with `S` quasi-compact and quasi-separated, so
[Stacks, Tag 01ZG] (`AlgebraicGeometry.exists_finitePresentation_closedImmersion`) factors it as
a closed immersion `i : X ⟶ V` followed by a morphism `p : V ⟶ S` of finite presentation; this
replaces the source's chart-by-chart immersion into a relative affine space, and is why no
reduction to affines appears below. The module `𝓕 = i_*𝒪_X` on `V` is quasi-coherent and of
finite type, and over `U` it is of finite presentation and flat because `i ∣_ p⁻¹(U)` is of
finite presentation (the composite `(i ≫ p) ∣_ U` is, and `p ∣_ U` is) and `(i ≫ p) ∣_ U` is
flat. Those are the five hypotheses of tag 0815 for `𝓕/V/S` and `U`.

Tag 0815 returns a centre `ℐ`, finitely presented and supported away from `U`, such that the
strict transform of `𝓕` on `V ×_S S'` is flat over `S'` and of finite presentation. Write
`g' : X ×_S S' ⟶ V ×_S S'` for the base change of `i` and `ι : X' ⟶ X ×_S S'` for the closed
immersion of the strict transform of `X`. Then:

* the strict transform of `𝒪_X` is `ι_*𝒪_{X'}` ([Stacks, Tag 080E], as
  `AlgebraicGeometry.strictTransformSheafBlowUpIso` composed with
  `AlgebraicGeometry.strictTransformSheafComapUnitIso`), so the strict transform of `𝓕` is
  `(ι ≫ g')_*𝒪_{X'}` ([Stacks, Tag 080G],
  `AlgebraicGeometry.strictTransformSheafPushforwardIso`);
* finite presentation of `(ι ≫ g')_*𝒪_{X'}` makes the ideal sheaf of the closed immersion
  `ι ≫ g'` of finite type ([Stacks, Tag 01BP]) and hence that closed immersion of finite
  presentation ([Stacks, Tag 01TV]); composing with the projection `V ×_S S' ⟶ S'`, which is a
  base change of `p`, gives finite presentation of `X' ⟶ S'`;
* flatness over `S'` passes from `(ι ≫ g')_*𝒪_{X'}` to `ι_*𝒪_{X'}` along the affine morphism
  `g'` ([Stacks, Tag 0FLM]) and then to `X' ⟶ S'` by
  `AlgebraicGeometry.flat_strictTransformToBlowUp_iff`.

The strict transform of `X` appears through
`AlgebraicGeometry.strictTransformBlowUpι`, which presents it as the base change
`X ×_X X'` of `X` along the blowup of `X` in `ℐ·𝒪_X`; the comparison with the presentation
`AlgebraicGeometry.strictTransformToBlowUp` used in the conclusion is the isomorphism
`AlgebraicGeometry.strictTransformBlowUpComapIso`, cancelled by
`AlgebraicGeometry.strictTransformBlowUpι_comp_snd`.

The hypothesis is the statement of tag 0815 itself. It differs from
`AlgebraicGeometry.FinitePresentationHasModuleFlatteningBlowup`, which asks for finite
presentation of the strict transform *pulled back to the strict transform of `X`* rather than on
the base change `X ×_S S'`. Tag 080D puts the strict transform of a module on the
base change and tag 0815 concludes that it is "an `𝒪_{X ×_S S'}`-module of finite presentation",
which is the form needed here and the form stated below; the pullback along the closed immersion
of the strict transform is a consequence of it, not an equivalent of it.

## References

* [Stacks Project, Tag 081R](https://stacks.math.columbia.edu/tag/081R)
* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 01ZG](https://stacks.math.columbia.edu/tag/01ZG)
* [Stacks Project, Tag 01BP](https://stacks.math.columbia.edu/tag/01BP)
* [Stacks Project, Tag 01TV](https://stacks.math.columbia.edu/tag/01TV)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 080E](https://stacks.math.columbia.edu/tag/080E)
* [Stacks Project, Tag 080G](https://stacks.math.columbia.edu/tag/080G)
* [Stacks Project, Tag 0FLM](https://stacks.math.columbia.edu/tag/0FLM)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- **The statement of [Stacks, Tag 0815]**, with the strict transform of the module read on the
base change `X ×_S S'` as [Stacks, Tag 080D] defines it.

For `X` quasi-compact and locally of finite presentation over a quasi-compact and
quasi-separated `S`, a quasi-coherent `𝒪_X`-module of finite type which over a quasi-compact
open `U ⊆ S` is of finite presentation and flat can be flattened by a `U`-admissible blowup: a
centre `ℐ` on `S`, finitely presented and supported away from `U`, whose strict transform is an
`𝒪_{X ×_S S'}`-module of finite presentation and flat over the blowup. -/
def FinitePresentationHasStrictTransformSheafFlatteningBlowup : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (F : X.Modules) [CompactSpace X]
    [CompactSpace S] [QuasiSeparatedSpace S] [LocallyOfFinitePresentation f]
    [F.IsQuasicoherent] [F.IsFiniteType], IsCompact (U : Set S) →
    ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj F).IsFinitePresentation →
    IsFlatOver (f ∣_ U).toLRSHom.toShHom ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj F) →
    ∃ ℐ : S.IdealSheafData,
      FinitePresentation ℐ.subschemeι ∧
        Disjoint (U : Set S) (ℐ.support : Set S) ∧
          IsFlatOver (pullback.snd f (blowUpToBase ℐ)).toLRSHom.toShHom
              (Stacks.StrictTransform.sheaf f (blowUpToBase ℐ) (exceptionalIdeal ℐ) F) ∧
            (Stacks.StrictTransform.sheaf f (blowUpToBase ℐ) (exceptionalIdeal ℐ)
              F).IsFinitePresentation

/-- A closed immersion whose direct image of the structure sheaf is of finite presentation is of
finite presentation: that direct image is the quotient of the structure sheaf of the target by
the ideal sheaf, so [Stacks, Tag 01BP] makes the ideal sheaf of finite type and
[Stacks, Tag 01TV] applies. -/
@[ega "IV 8.6.1" "direction"]
theorem finitePresentation_of_isFinitePresentation_pushforward_unitModule {Z W : Scheme.{u}}
    (j : Z ⟶ W) [IsClosedImmersion j]
    (h : ((Scheme.Modules.pushforward j).obj Z.unitModule).IsFinitePresentation) :
    FinitePresentation j := by
  have hI : (Stacks.ClosedImmersion.idealSheaf j.toLRSHom.toShHom).IsFiniteType := by
    have hfp : ((SheafOfModules.pushforward (structureSheafHom j.toLRSHom.toShHom)).obj
        (SheafOfModules.unit (structureSheafRing Z.toRingedSpace))).IsFinitePresentation := h
    have _ :=
      Stacks.AlgebraicGeometry.ClosedImmersionTFAE.epi_unitToPushforwardObjUnit_of_isClosedImmersion
        j
    exact Stacks.SheafOfModules.LocalKernel.kernel_isFiniteType_of_epi_from_finiteType
      (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom j.toLRSHom.toShHom))
  exact (finitePresentation_iff_isFiniteType_idealSheaf j).2 hI

/-- Finite presentation is unchanged by precomposing with an isomorphism. -/
theorem finitePresentation_of_isIso_comp {A B C : Scheme.{u}} (e : A ≅ B) (m : B ⟶ C)
    (h : FinitePresentation (e.hom ≫ m)) : FinitePresentation m := by
  obtain ⟨_, _, _⟩ := h
  have _ : IsOpenImmersion e.inv := IsOpenImmersion.of_isIso _
  rw [← e.inv_hom_id_assoc m]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The strict transform of `X` is quasi-compact over the blowup as soon as `f` is: it is a
closed subscheme of the base change `X ×_S S'`, whose projection to the blowup is a base change
of `f`. -/
instance quasiCompact_strictTransformToBlowUp [QuasiCompact f] (ℐ : S.IdealSheafData) :
    QuasiCompact (strictTransformToBlowUp f ℐ) :=
  have _ : QuasiCompact (pullback.snd f (blowUpToBase ℐ)) :=
    quasiCompact_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f (blowUpToBase ℐ)) ‹QuasiCompact f›
  inferInstance

/-- The strict transform of `X` is quasi-separated over the blowup as soon as `f` is. -/
instance quasiSeparated_strictTransformToBlowUp [QuasiSeparated f] (ℐ : S.IdealSheafData) :
    QuasiSeparated (strictTransformToBlowUp f ℐ) :=
  have _ : QuasiSeparated (pullback.snd f (blowUpToBase ℐ)) :=
    quasiSeparated_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f (blowUpToBase ℐ)) ‹QuasiSeparated f›
  inferInstance

/-- The strict transform of `X` is locally of finite type over the blowup as soon as `f` is. -/
instance locallyOfFiniteType_strictTransformToBlowUp [LocallyOfFiniteType f]
    (ℐ : S.IdealSheafData) : LocallyOfFiniteType (strictTransformToBlowUp f ℐ) :=
  have _ : LocallyOfFiniteType (pullback.snd f (blowUpToBase ℐ)) :=
    locallyOfFiniteType_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f (blowUpToBase ℐ)) ‹LocallyOfFiniteType f›
  inferInstance

/-- **The reduction of the finite-presentation clause of [Stacks, Tag 081R] to its local half**,
which is the source's own first sentence: `f` being of finite type and quasi-separated, the
strict transform of `X` is quasi-compact and quasi-separated over the blowup for any centre at
all, so finite presentation over the blowup is *local* finite presentation and nothing more.

This holds with no reference to the centre and no flatness, so it is independent of
[Stacks, Tag 0815]: what that tag is needed for in the conclusion of tag 081R is local finite
presentation. The source obtains it from [Stacks, Tag 081N], which is
`FinitePresentationFromDenseOpen.locallyOfFinitePresentation_of_flat_of_retrocompact_dense_open`
(tag 081P), applied to the strict transform — which by the instances above is locally of finite
type, and which is flat by
`AlgebraicGeometry.exists_isAdmissibleBlowup_flat_strictTransform` — once some retrocompact
scheme-theoretically dense open of the blowup avoids the exceptional divisor. The complement of
the exceptional divisor is such an open, by
`Stacks.Blowup.isRetrocompact_compl_support_exceptionalIdeal` and
`Stacks.Blowup.isSchemeTheoreticallyDense_compl_support_exceptionalIdeal`, so the deduction is
`Stacks.Blowup.locallyOfFinitePresentation_strictTransformMap_of_flat`. -/
theorem finitePresentation_strictTransformToBlowUp_iff [LocallyOfFiniteType f] [QuasiCompact f]
    [QuasiSeparated f] (ℐ : S.IdealSheafData) :
    FinitePresentation (strictTransformToBlowUp f ℐ) ↔
      LocallyOfFinitePresentation (strictTransformToBlowUp f ℐ) :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h, inferInstance, inferInstance⟩⟩

/-- Over an open `W` of the target, the direct image of the structure sheaf along a closed
immersion `i` is of finite presentation as soon as `i ∣_ W` is of finite presentation. -/
theorem isFinitePresentation_pullback_pushforward_unitModule {X V : Scheme.{u}} (i : X ⟶ V)
    [IsClosedImmersion i] (W : V.Opens) (h : FinitePresentation (i ∣_ W)) :
    ((Scheme.Modules.pullback W.ι).obj
      ((Scheme.Modules.pushforward i).obj X.unitModule)).IsFinitePresentation := by
  have hOX : ((Scheme.Modules.restrictFunctor (i ⁻¹ᵁ W).ι).obj
      X.unitModule).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (i ⁻¹ᵁ W).toScheme.ringCatSheaf).prop_of_iso
      (Scheme.Modules.restrictUnitIso (i ⁻¹ᵁ W).ι).symm inferInstance
  have hpush : ((Scheme.Modules.pushforward (i ∣_ W)).obj
      ((Scheme.Modules.restrictFunctor (i ⁻¹ᵁ W).ι).obj X.unitModule)).IsFinitePresentation :=
    (isFinitePresentation_iff_pushforward_isFinitePresentation (i ∣_ W) h _).1 hOX
  have hrestr : ((Scheme.Modules.restrictFunctor W.ι).obj
      ((Scheme.Modules.pushforward i).obj X.unitModule)).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation W.toScheme.ringCatSheaf).prop_of_iso
      ((Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso i W).app
        X.unitModule).symm hpush
  exact (SheafOfModules.isFinitePresentation W.toScheme.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app _) hrestr

/-- Over an open `U` of `S` over which `i ≫ p` is flat, the direct image of the structure sheaf
along the closed immersion `i` is flat over `p`. -/
theorem isFlatOver_pullback_pushforward_unitModule {X V S : Scheme.{u}} (i : X ⟶ V)
    [IsClosedImmersion i] (p : V ⟶ S) (U : S.Opens) [Flat ((i ≫ p) ∣_ U)] :
    IsFlatOver (p ∣_ U).toLRSHom.toShHom ((Scheme.Modules.pullback (p ⁻¹ᵁ U).ι).obj
      ((Scheme.Modules.pushforward i).obj X.unitModule)) := by
  have _ : Flat ((i ∣_ (p ⁻¹ᵁ U)) ≫ (p ∣_ U)) := by
    have hloc : Flat ((i ≫ p) ∣_ U) := inferInstance
    rwa [morphismRestrict_comp] at hloc
  have hunit : IsFlatOver ((i ∣_ (p ⁻¹ᵁ U)) ≫ (p ∣_ U)).toLRSHom.toShHom
      (i ⁻¹ᵁ (p ⁻¹ᵁ U)).toScheme.unitModule := fun x ↦
    (isFlatOverAt_unit_iff_isFlatAt _ x).2 (Flat.stalkMap _ x)
  have hOXU : IsFlatOver ((i ∣_ (p ⁻¹ᵁ U)) ≫ (p ∣_ U)).toLRSHom.toShHom
      ((Scheme.Modules.restrictFunctor (i ⁻¹ᵁ (p ⁻¹ᵁ U)).ι).obj X.unitModule) :=
    (isFlatOver_iff_of_moduleIso _
      (Scheme.Modules.restrictUnitIso (i ⁻¹ᵁ (p ⁻¹ᵁ U)).ι).symm).mp hunit
  have hpush := (isFlatOver_pushforward_iff (i ∣_ (p ⁻¹ᵁ U)) (p ∣_ U)
    ((Scheme.Modules.restrictFunctor (i ⁻¹ᵁ (p ⁻¹ᵁ U)).ι).obj X.unitModule)).mp hOXU
  have hrestr : IsFlatOver (p ∣_ U).toLRSHom.toShHom
      ((Scheme.Modules.restrictFunctor (p ⁻¹ᵁ U).ι).obj
        ((Scheme.Modules.pushforward i).obj X.unitModule)) :=
    (isFlatOver_iff_of_moduleIso _
      ((Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso i
        (p ⁻¹ᵁ U)).app X.unitModule)).mpr hpush
  exact (isFlatOver_iff_of_moduleIso _
    ((Scheme.Modules.restrictFunctorIsoPullback (p ⁻¹ᵁ U).ι).app _)).mp hrestr

/-- The base change of a closed immersion `i : X ⟶ V` along the blowup is a closed immersion. -/
private theorem isClosedImmersion_baseChangeInducedMap {X V S T : Scheme.{u}} (i : X ⟶ V)
    [IsClosedImmersion i] (p : V ⟶ S) (g : T ⟶ S) :
    IsClosedImmersion (baseChangeInducedMap i p g) :=
  IsClosedImmersion.isStableUnderBaseChange.of_isPullback
    (isPullback_baseChangeInducedMap i p g) inferInstance

/-- If the strict transform of `i_*𝒪_X` is flat over the blowup, for a closed immersion
`i : X ⟶ V`, then the strict transform of `X` is flat over the blowup ([Stacks, Tag 080G]). -/
theorem flat_strictTransformToBlowUp_of_isFlatOver_strictTransformSheaf {X V S : Scheme.{u}}
    (i : X ⟶ V) [IsClosedImmersion i] (p : V ⟶ S) (ℐ : S.IdealSheafData)
    (h : IsFlatOver (pullback.snd p (blowUpToBase ℐ)).toLRSHom.toShHom
      (Stacks.StrictTransform.sheaf p (blowUpToBase ℐ) (exceptionalIdeal ℐ)
        ((Scheme.Modules.pushforward i).obj X.unitModule))) :
    Flat (strictTransformToBlowUp (i ≫ p) ℐ) := by
  have _ := isClosedImmersion_baseChangeInducedMap i p (blowUpToBase ℐ)
  have _ : (Stacks.StrictTransform.sheaf (i ≫ p) (blowUpToBase ℐ) (exceptionalIdeal ℐ)
      X.unitModule).IsQuasicoherent :=
    Stacks.StrictTransform.isQuasicoherent_sheaf_blowUp (i ≫ p) ℐ X.unitModule
  refine (flat_strictTransformToBlowUp_iff (i ≫ p) ℐ).mpr ?_
  have h' := (isFlatOver_pushforward_iff (baseChangeInducedMap i p (blowUpToBase ℐ))
    (pullback.snd p (blowUpToBase ℐ)) (Stacks.StrictTransform.sheaf (i ≫ p) (blowUpToBase ℐ)
      (exceptionalIdeal ℐ) X.unitModule)).mpr
    ((isFlatOver_iff_of_moduleIso _
      (sheafPushforwardIso i p (blowUpToBase ℐ) (exceptionalIdeal ℐ) X.unitModule)).mpr h)
  rwa [baseChangeInducedMap_snd] at h'

/-- If the strict transform of `i_*𝒪_X` is of finite presentation, for a closed immersion
`i : X ⟶ V` into a scheme of finite presentation over `S`, then the strict transform of `X` is of
finite presentation over the blowup ([Stacks, Tag 080E], [Stacks, Tag 080G]). -/
theorem finitePresentation_strictTransformToBlowUp_of_isFinitePresentation_strictTransformSheaf
    {X V S : Scheme.{u}} (i : X ⟶ V) [IsClosedImmersion i] (p : V ⟶ S)
    (hp : FinitePresentation p) (ℐ : S.IdealSheafData)
    (h : (Stacks.StrictTransform.sheaf p (blowUpToBase ℐ) (exceptionalIdeal ℐ)
      ((Scheme.Modules.pushforward i).obj X.unitModule)).IsFinitePresentation) :
    FinitePresentation (strictTransformToBlowUp (i ≫ p) ℐ) := by
  have _ := isClosedImmersion_baseChangeInducedMap i p (blowUpToBase ℐ)
  have e080E : Stacks.StrictTransform.sheaf (i ≫ p) (blowUpToBase ℐ) (exceptionalIdeal ℐ)
        X.unitModule ≅
      (Scheme.Modules.pushforward (strictTransformBlowUpι (i ≫ p) ℐ)).obj
        (Stacks.StrictTransform.baseChange (𝟙 X)
          (blowUpToBase (ℐ.comap (i ≫ p)))).unitModule :=
    strictTransformSheafBlowUpIso (i ≫ p) ℐ X.unitModule ≪≫
      (Scheme.Modules.pushforward (strictTransformBlowUpι (i ≫ p) ℐ)).mapIso
        (strictTransformSheafComapUnitIso (i ≫ p) ℐ)
  have ePush : (Scheme.Modules.pushforward (strictTransformBlowUpι (i ≫ p) ℐ ≫
          baseChangeInducedMap i p (blowUpToBase ℐ))).obj
        (Stacks.StrictTransform.baseChange (𝟙 X)
          (blowUpToBase (ℐ.comap (i ≫ p)))).unitModule ≅
      Stacks.StrictTransform.sheaf p (blowUpToBase ℐ) (exceptionalIdeal ℐ)
        ((Scheme.Modules.pushforward i).obj X.unitModule) :=
    ((Scheme.Modules.pushforwardComp (strictTransformBlowUpι (i ≫ p) ℐ)
        (baseChangeInducedMap i p (blowUpToBase ℐ))).app _).symm ≪≫
      (Scheme.Modules.pushforward (baseChangeInducedMap i p
        (blowUpToBase ℐ))).mapIso e080E.symm ≪≫
      sheafPushforwardIso i p (blowUpToBase ℐ) (exceptionalIdeal ℐ) X.unitModule
  obtain ⟨_, _, _⟩ : FinitePresentation (strictTransformBlowUpι (i ≫ p) ℐ ≫
      baseChangeInducedMap i p (blowUpToBase ℐ)) :=
    finitePresentation_of_isFinitePresentation_pushforward_unitModule _
      ((SheafOfModules.isFinitePresentation (Stacks.StrictTransform.baseChange p
        (blowUpToBase ℐ)).ringCatSheaf).prop_of_iso ePush.symm h)
  obtain ⟨_, _, _⟩ := id hp
  have hcomp : FinitePresentation ((strictTransformBlowUpι (i ≫ p) ℐ ≫
      baseChangeInducedMap i p (blowUpToBase ℐ)) ≫ pullback.snd p (blowUpToBase ℐ)) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  rw [Category.assoc, baseChangeInducedMap_snd, strictTransformBlowUpι_comp_snd] at hcomp
  exact finitePresentation_of_isIso_comp (strictTransformBlowUpComapIso (i ≫ p) ℐ) _ hcomp

/-- **Stacks Project, Tag 081R.** Let `S` be a quasi-compact and quasi-separated scheme, let
`f : X ⟶ S` be of finite type and quasi-separated and let `U ⊆ S` be a quasi-compact open such
that `X_U ⟶ U` is flat and locally of finite presentation. Granted the statement of
[Stacks, Tag 0815], there is a centre `ℐ` on `S`, finitely presented and supported away from
`U`, exhibiting the blowup of `S` in `ℐ` as a `U`-admissible blowup, such that the strict
transform of `X` along that blowup is flat **and of finite presentation** over it. -/
theorem exists_isAdmissibleBlowup_flat_finitePresentation_strictTransform [CompactSpace S]
    [QuasiSeparatedSpace S] [LocallyOfFiniteType f] [QuasiCompact f] [QuasiSeparated f]
    (U : S.Opens) (hU : IsCompact (U : Set S)) [Flat (f ∣_ U)]
    [LocallyOfFinitePresentation (f ∣_ U)]
    (H : FinitePresentationHasStrictTransformSheafFlatteningBlowup.{u}) :
    ∃ ℐ : S.IdealSheafData,
      FinitePresentation ℐ.subschemeι ∧
        Disjoint (U : Set S) (ℐ.support : Set S) ∧
          Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase ℐ) ∧
            Flat (strictTransformToBlowUp f ℐ) ∧
              FinitePresentation (strictTransformToBlowUp f ℐ) := by
  have _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have _ : QuasiSeparatedSpace X := (quasiSeparated_iff_quasiSeparatedSpace f).mp inferInstance
  obtain ⟨V, p, i, hp, _, rfl⟩ := exists_finitePresentation_closedImmersion f
  obtain ⟨_, _, _⟩ := id hp
  have _ : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace p
  have _ : (X.unitModule).IsFiniteType :=
    inferInstanceAs (SheafOfModules.unit X.ringCatSheaf).IsFiniteType
  have _ : ((Scheme.Modules.pushforward i).obj X.unitModule).IsFiniteType :=
    (isFiniteType_iff_pushforward_isFiniteType i X.unitModule).1 inferInstance
  have _ : LocallyOfFinitePresentation ((i ∣_ (p ⁻¹ᵁ U)) ≫ (p ∣_ U)) := by
    have hloc : LocallyOfFinitePresentation ((i ≫ p) ∣_ U) := inferInstance
    rwa [morphismRestrict_comp] at hloc
  obtain ⟨ℐ, hIfp, hIdisj, hflatST, hfpST⟩ :=
    H p U ((Scheme.Modules.pushforward i).obj X.unitModule) hU
      (isFinitePresentation_pullback_pushforward_unitModule i (p ⁻¹ᵁ U)
        ⟨locallyOfFinitePresentation_of_comp _ (p ∣_ U), inferInstance, inferInstance⟩)
      (isFlatOver_pullback_pushforward_unitModule i p U)
  exact ⟨ℐ, hIfp, hIdisj, (Stacks.Blowup.isAdmissibleBlowup_iff U (blowUpToBase ℐ)).mpr
    ⟨ℐ, hIfp, hIdisj, Iso.refl _, Category.id_comp _⟩,
    flat_strictTransformToBlowUp_of_isFlatOver_strictTransformSheaf i p ℐ hflatST,
    finitePresentation_strictTransformToBlowUp_of_isFinitePresentation_strictTransformSheaf
      i p hp ℐ hfpST⟩

/-- The conclusion of [Stacks, Tag 081R] in the shape the downstream tags consume it: a centre,
finitely presented and supported away from `U`, whose strict transform is flat and *locally* of
finite presentation over the blowup.

This is the local reading of the flatness-and-finite-presentation conclusion:
`AlgebraicGeometry.finitePresentation_strictTransformToBlowUp_iff` makes the two agree, the strict
transform being quasi-compact and quasi-separated over the blowup for free. -/
theorem exists_isAdmissibleBlowup_flat_locallyOfFinitePresentation_strictTransform
    [CompactSpace S] [QuasiSeparatedSpace S] [LocallyOfFiniteType f] [QuasiCompact f]
    [QuasiSeparated f] (U : S.Opens) (hU : IsCompact (U : Set S)) [Flat (f ∣_ U)]
    [LocallyOfFinitePresentation (f ∣_ U)]
    (H : FinitePresentationHasStrictTransformSheafFlatteningBlowup.{u}) :
    ∃ ℐ : S.IdealSheafData,
      FinitePresentation ℐ.subschemeι ∧ Disjoint (U : Set S) (ℐ.support : Set S) ∧
        Flat (strictTransformToBlowUp f ℐ) ∧
          LocallyOfFinitePresentation (strictTransformToBlowUp f ℐ) :=
  let ⟨ℐ, hIfp, hIdisj, _, hflat, hfp⟩ :=
    exists_isAdmissibleBlowup_flat_finitePresentation_strictTransform f U hU H
  ⟨ℐ, hIfp, hIdisj, hflat, hfp.1⟩

end AlgebraicGeometry

end
