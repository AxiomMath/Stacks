module

public import StacksFrontier.AlgebraicGeometry.Flatness.Applications.FiniteLocallyFreeStrictTransform
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.ModuleFlatteningBlowup
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic

/-!
# Making the strict transform finite locally free over a locally Noetherian base

Over a quasi-compact, quasi-separated and locally Noetherian base `S`, a proper morphism
`f : X ⟶ S` which is flat over a quasi-compact open `U ⊆ S` has a `U`-admissible centre whose
strict transform is flat and locally of finite presentation over the blowup. This is the
conclusion of [Stacks, Tag 081R] in that setting, so [Stacks, Tag 0B49] holds outright there.

The centre comes from [Stacks, Tag 0815] applied to the structure sheaf `𝒪_X`: a morphism of
finite type over a locally Noetherian base is locally of finite presentation, and `𝒪_X`
restricted to `f⁻¹(U)` is of finite presentation and flat over `U`.
`AlgebraicGeometry.flat_strictTransformToBlowUp_iff` reads the flatness of the strict transform
of `𝒪_X` as flatness of the strict transform of `X`. The strict transform is of finite type over
the blowup, which is locally Noetherian, so it is locally of finite presentation.

## Main results

* `exists_flat_strictTransform_of_isLocallyNoetherian`: the conclusion of [Stacks, Tag 081R] over
  a locally Noetherian base.
* `exists_isAdmissibleBlowup_isFiniteLocallyFree_strictTransform_of_isLocallyNoetherian`:
  [Stacks, Tag 0B49] over a locally Noetherian base.

## References

* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 081R](https://stacks.math.columbia.edu/tag/081R)
* [Stacks Project, Tag 0B49](https://stacks.math.columbia.edu/tag/0B49)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **[Stacks, Tag 081R] over a locally Noetherian base.** Let `S` be quasi-compact,
quasi-separated and locally Noetherian, let `f : X ⟶ S` be proper and let `U ⊆ S` be a
quasi-compact open over which `f` is flat. There is a centre `I` on `S`, finitely presented and
supported away from `U`, such that the strict transform of `X` along the blowup of `S` in `I` is
flat and locally of finite presentation over that blowup. -/
theorem exists_flat_strictTransform_of_isLocallyNoetherian {X S : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] [IsLocallyNoetherian S] (f : X ⟶ S) [IsProper f] (U : S.Opens)
    (hU : IsCompact (U : Set S)) [Flat (f ∣_ U)] :
    ∃ I : S.IdealSheafData,
      FinitePresentation I.subschemeι ∧ Disjoint (U : Set S) (I.support : Set S) ∧
        Flat (strictTransformToBlowUp f I) ∧
          LocallyOfFinitePresentation (strictTransformToBlowUp f I) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : X.unitModule.IsFiniteType :=
    inferInstanceAs (SheafOfModules.unit X.ringCatSheaf).IsFiniteType
  have hFfp : ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj X.unitModule).IsFinitePresentation :=
    Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback (f ⁻¹ᵁ U).ι
      X.unitModule
  have hFflat : IsFlatOver (f ∣_ U).toLRSHom.toShHom
      ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj X.unitModule) :=
    (isFlatOver_iff_of_moduleIso _ (Scheme.Modules.pullbackUnitIso (f ⁻¹ᵁ U).ι)).mpr
      fun x ↦ (isFlatOverAt_unit_iff_isFlatAt (f ∣_ U) x).mpr
        ((Flat.iff_flat_stalkMap (f ∣_ U)).mp inferInstance x)
  obtain ⟨I, hIfp, hIdisj, -, -, hflat⟩ :=
    exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_affineCharts f X.unitModule U hU
      hFfp hFflat
  have : IsLocallyNoetherian (blowUp I) := LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase I)
  exact ⟨I, hIfp, hIdisj, (flat_strictTransformToBlowUp_iff f I).mpr hflat, inferInstance⟩

/-- **[Stacks, Tag 0B49] over a locally Noetherian base.** Let `S` be quasi-compact,
quasi-separated and locally Noetherian, let `f : X ⟶ S` be proper and let `U ⊆ S` be a
quasi-compact open over which `X` is finite locally free. Then there is a `U`-admissible blowup of
`S` along which the strict transform of `X` is finite locally free. -/
theorem exists_isAdmissibleBlowup_isFiniteLocallyFree_strictTransform_of_isLocallyNoetherian
    {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f] (U : S.Opens) (hU : IsCompact (U : Set S))
    [Stacks.Morphisms.IsFiniteLocallyFree (pullback.snd f U.ι)] :
    ∃ I : S.IdealSheafData,
      Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase I) ∧
        Stacks.Morphisms.IsFiniteLocallyFree (strictTransformToBlowUp f I) := by
  have hflat : Flat (pullback.snd f U.ι) :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      (pullback.snd f U.ι)).mp inferInstance).2.1
  have : MorphismProperty.RespectsIso @Flat :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : Flat (f ∣_ U) := by
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict f U] at hflat
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @Flat) _ _).mp hflat
  exact exists_isAdmissibleBlowup_isFiniteLocallyFree_strictTransform f U hU
    (exists_flat_strictTransform_of_isLocallyNoetherian f U hU)

end AlgebraicGeometry

end
