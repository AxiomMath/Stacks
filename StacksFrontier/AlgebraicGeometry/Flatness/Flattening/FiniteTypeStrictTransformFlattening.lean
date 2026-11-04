module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.AffinePushforward
public import StacksFrontier.AlgebraicGeometry.Flatness.ExtendingFromOpen.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.ModuleFlatteningBlowup
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformSchemeFlattening

/-!
# Flattening the strict transform of a finite type scheme, with nothing granted

Let `S` be a quasi-compact and quasi-separated scheme, let `f : X ⟶ S` be of finite type and
quasi-separated, and let `U ⊆ S` be a quasi-compact open over which `f` is flat and locally of
finite presentation. Then there is a `U`-admissible blowup of `S` along which the strict
transform of `X` becomes flat over the blowup.

This is the flatness assertion of [Stacks, Tag 081R] with no hypothesis beyond those of the
source. The library's form of that tag,
`AlgebraicGeometry.exists_isAdmissibleBlowup_flat_strictTransform`, carries the affine case
`AlgebraicGeometry.AffineChartFlatteningCentre` as a hypothesis; what is proved here instead is
the source's own argument, which needs no such hypothesis because
[Stacks, Tag 0815] is available in full.

## Main results

* `AlgebraicGeometry.exists_isAdmissibleBlowup_flat_strictTransform_of_locallyOfFiniteType`: the
  flatness assertion of **[Stacks, Tag 081R]**, with nothing granted.

## Implementation notes

The source reduces to an affine source, immerses it into a relative affine space and applies
[Stacks, Tag 0815] there. The reduction to an affine source is unnecessary once [Stacks, Tag 01ZG]
is available globally: `AlgebraicGeometry.exists_finitePresentation_closedImmersion` factors `f`
as a closed immersion `i : X ⟶ X'` followed by a morphism `p : X' ⟶ S` of finite presentation, and
`i_* 𝒪_X` is a quasi-coherent `𝒪_{X'}`-module of finite type which over `U` is of finite
presentation and flat, so [Stacks, Tag 0815] applies to the data `i_* 𝒪_X / X' / S`.

Finite presentation and flatness of `i_* 𝒪_X` over `U` are read off the corresponding properties
of `f` over `U` through the restriction of the factorization to `U`
(`AlgebraicGeometry.morphismRestrict_comp`): the closed immersion `i ∣_ p⁻¹(U)` is locally of
finite presentation by cancellation, and direct image along an affine morphism neither creates
nor destroys finite presentation ([Stacks, Tag 01BP] in the form
`AlgebraicGeometry.isFinitePresentation_iff_pushforward_isFinitePresentation`) or flatness over a
base ([Stacks, Tag 0FLM]).

What comes back from [Stacks, Tag 0815] is flatness of the strict transform of `i_* 𝒪_X`.
[Stacks, Tag 080G] identifies that with the direct image, along the base change of `i`, of the
strict transform of `𝒪_X`, so [Stacks, Tag 0FLM] again turns it into flatness of the strict
transform of `𝒪_X` over the blowup, which is flatness of the strict transform of `X` by
`AlgebraicGeometry.flat_strictTransformToBlowUp_iff`.

**What is not proved.** The source also concludes that the strict transform is of finite
presentation over the blowup; that assertion is not treated here, exactly as in the library's
form of the tag.

## References

* [Stacks Project, Tag 081R](https://stacks.math.columbia.edu/tag/081R)
* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 01ZG](https://stacks.math.columbia.edu/tag/01ZG)
* [Stacks Project, Tag 080G](https://stacks.math.columbia.edu/tag/080G)
* [Stacks Project, Tag 0FLM](https://stacks.math.columbia.edu/tag/0FLM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The direct image of a restriction along `i ∣_ V` is the restriction of the direct image
along `i`. -/
private def pushforwardRestrictIso {X X' : Scheme.{u}} (i : X ⟶ X') (V : X'.Opens)
    (M : X.Modules) :
    (Scheme.Modules.pushforward (i ∣_ V)).obj
        ((Scheme.Modules.restrictFunctor (i ⁻¹ᵁ V).ι).obj M) ≅
      (Scheme.Modules.pullback V.ι).obj ((Scheme.Modules.pushforward i).obj M) :=
  ((Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso i V).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback V.ι).app _

/-- For a closed immersion `i : X ⟶ X'` and `p : X' ⟶ S` locally of finite presentation, if
`i ≫ p` is locally of finite presentation over an open `U ⊆ S`, then `i_* 𝒪_X` is of finite
presentation over `p⁻¹(U)`. -/
theorem isFinitePresentation_pullback_pushforward_unit_of_isClosedImmersion
    {X X' S : Scheme.{u}} (i : X ⟶ X') (p : X' ⟶ S) [IsClosedImmersion i]
    [LocallyOfFinitePresentation p] (U : S.Opens) [LocallyOfFinitePresentation ((i ≫ p) ∣_ U)] :
    ((Scheme.Modules.pullback (p ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit X.ringCatSheaf))).IsFinitePresentation := by
  set OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  set V : X'.Opens := p ⁻¹ᵁ U
  have hcompU : LocallyOfFinitePresentation ((i ∣_ V) ≫ (p ∣_ U)) := by
    have hloc : LocallyOfFinitePresentation ((i ≫ p) ∣_ U) := inferInstance
    rwa [morphismRestrict_comp] at hloc
  have hiVFP : FinitePresentation (i ∣_ V) :=
    ⟨locallyOfFinitePresentation_of_comp (i ∣_ V) (p ∣_ U), inferInstance, inferInstance⟩
  set OXV := (Scheme.Modules.restrictFunctor (i ⁻¹ᵁ V).ι).obj OX
  have hOXVfp : OXV.IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (i ⁻¹ᵁ V).toScheme.ringCatSheaf).prop_of_iso
      (Scheme.Modules.restrictUnitIso (i ⁻¹ᵁ V).ι).symm inferInstance
  exact (SheafOfModules.isFinitePresentation V.toScheme.ringCatSheaf).prop_of_iso
    (pushforwardRestrictIso i V OX)
    ((isFinitePresentation_iff_pushforward_isFinitePresentation (i ∣_ V) hiVFP OXV).1 hOXVfp)

/-- For a closed immersion `i : X ⟶ X'` and `p : X' ⟶ S`, if `i ≫ p` is flat over an open
`U ⊆ S`, then `i_* 𝒪_X` is flat over `U` on `p⁻¹(U)`. -/
theorem isFlatOver_pullback_pushforward_unit_of_isClosedImmersion
    {X X' S : Scheme.{u}} (i : X ⟶ X') (p : X' ⟶ S) [IsClosedImmersion i] (U : S.Opens)
    [Flat ((i ≫ p) ∣_ U)] :
    IsFlatOver (p ∣_ U).toLRSHom.toShHom ((Scheme.Modules.pullback (p ⁻¹ᵁ U).ι).obj
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit X.ringCatSheaf))) := by
  set OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  set V : X'.Opens := p ⁻¹ᵁ U
  set OXV := (Scheme.Modules.restrictFunctor (i ⁻¹ᵁ V).ι).obj OX
  have hres : IsFlatOver ((i ≫ p) ∣_ U).toLRSHom.toShHom
      (SheafOfModules.unit ((i ≫ p) ⁻¹ᵁ U).toScheme.ringCatSheaf) := fun z ↦
    (isFlatOverAt_unit_iff_isFlatAt ((i ≫ p) ∣_ U) z).2 (Flat.stalkMap ((i ≫ p) ∣_ U) z)
  rw [morphismRestrict_comp] at hres
  have hbase : IsFlatOver ((i ∣_ V) ≫ (p ∣_ U)).toLRSHom.toShHom OXV :=
    (isFlatOver_iff_of_moduleIso ((i ∣_ V) ≫ (p ∣_ U)).toLRSHom.toShHom
      (Scheme.Modules.restrictUnitIso (i ⁻¹ᵁ V).ι)).2 hres
  exact (isFlatOver_iff_of_moduleIso (p ∣_ U).toLRSHom.toShHom (pushforwardRestrictIso i V OX)).1
    ((isFlatOver_pushforward_iff (i ∣_ V) (p ∣_ U) OXV).1 hbase)

/-- **The flatness assertion of [Stacks, Tag 081R], with nothing granted.** Let `S` be a
quasi-compact and quasi-separated scheme, let `f : X ⟶ S` be of finite type and quasi-separated,
and let `U ⊆ S` be a quasi-compact open over which `f` is flat and locally of finite
presentation. Then there is a centre `I` on `S`, finitely presented and supported away from `U`
— so the blowup of `S` in `I` is a `U`-admissible blowup — along which the strict transform of
`X` is flat over the blowup. -/
theorem exists_isAdmissibleBlowup_flat_strictTransform_of_locallyOfFiniteType
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]
    [LocallyOfFiniteType f] [QuasiCompact f] [QuasiSeparated f]
    (U : S.Opens) (hU : IsCompact (U : Set S))
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)] :
    ∃ I : S.IdealSheafData, FinitePresentation I.subschemeι ∧
      Disjoint (U : Set S) (I.support : Set S) ∧
        Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase I) ∧
          Flat (strictTransformToBlowUp f I) := by
  have _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have _ : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨X', p, i, ⟨_, _, _⟩, _, rfl⟩ := exists_finitePresentation_closedImmersion f
  have _ : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace p
  set OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  set F : X'.Modules := (Scheme.Modules.pushforward i).obj OX
  have _ : F.IsFiniteType := (isFiniteType_iff_pushforward_isFiniteType i OX).1 inferInstance
  obtain ⟨K, hKfp, hKdisj, hKadm, -, hKflat⟩ :=
    exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_affineCharts p F U hU
      (isFinitePresentation_pullback_pushforward_unit_of_isClosedImmersion i p U)
      (isFlatOver_pullback_pushforward_unit_of_isClosedImmersion i p U)
  refine ⟨K, hKfp, hKdisj, hKadm, ?_⟩
  rw [flat_strictTransformToBlowUp_iff]
  have hdown : IsFlatOver (baseChangeInducedMap i p (blowUpToBase K) ≫
      pullback.snd p (blowUpToBase K)).toLRSHom.toShHom
      (Stacks.StrictTransform.sheaf (i ≫ p) (blowUpToBase K) (exceptionalIdeal K) OX) :=
    (isFlatOver_pushforward_iff (baseChangeInducedMap i p (blowUpToBase K))
      (pullback.snd p (blowUpToBase K))
      (Stacks.StrictTransform.sheaf (i ≫ p) (blowUpToBase K) (exceptionalIdeal K) OX)).2
      ((isFlatOver_iff_of_moduleIso (pullback.snd p (blowUpToBase K)).toLRSHom.toShHom
        (sheafPushforwardIso i p (blowUpToBase K) (exceptionalIdeal K) OX)).2 hKflat)
  rwa [baseChangeInducedMap_snd i p (blowUpToBase K)] at hdown

end AlgebraicGeometry

end
