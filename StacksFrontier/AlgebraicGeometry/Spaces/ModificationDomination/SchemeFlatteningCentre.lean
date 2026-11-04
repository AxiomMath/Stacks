module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.ModuleFlatteningBlowup
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformSchemeFlattening
public import StacksFrontier.AlgebraicGeometry.Flatness.Applications.FiniteLocallyFreeStrictTransformNoetherian

/-!
# A flattening centre with support exactly the complement of the open, over a Noetherian base

Let `S` be a quasi-compact, quasi-separated, locally Noetherian scheme, let `f : X ⟶ S` be locally
of finite type with `X` quasi-compact, and let `U ⊆ S` be a quasi-compact open over which `f` is
flat. Then there is a finitely presented centre `K` on `S` whose support is exactly `S ∖ U` such
that the strict transform of `X` along the blowup of `S` in `K` is flat over that blowup.

This is [Stacks, Tag 0815] for the structure sheaf of `X`, in the form
`AlgebraicGeometry.exists_flatteningCentre_supportSet_eq_compl`, read as a statement about the
strict transform of `X` through `AlgebraicGeometry.flat_strictTransformToBlowUp_iff`.

## Main results

* `AlgebraicGeometry.exists_supportSet_eq_compl_flat_strictTransformToBlowUp`: there is a
  finitely presented centre with support `S ∖ U` along whose blowup the strict transform of `X`
  is flat.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A flattening centre cutting out exactly `S ∖ U`, over a Noetherian base.** Let `S` be
quasi-compact, quasi-separated and locally Noetherian, let `f : X ⟶ S` be locally of finite type
with `X` quasi-compact and let `U ⊆ S` be a quasi-compact open over which `f` is flat. There is a
finitely presented centre `K` on `S` with support `S ∖ U` such that the strict transform of `X`
along the blowup of `S` in `K` is flat over that blowup. -/
theorem exists_supportSet_eq_compl_flat_strictTransformToBlowUp {X S : Scheme.{u}}
    [CompactSpace S] [QuasiSeparatedSpace S] [IsLocallyNoetherian S] [CompactSpace X]
    (f : X ⟶ S) [LocallyOfFiniteType f] (U : S.Opens) (hU : IsCompact (U : Set S))
    [Flat (f ∣_ U)] :
    ∃ K : S.IdealSheafData, FinitePresentation K.subschemeι ∧
      K.supportSet = (U : Set S)ᶜ ∧ Flat (strictTransformToBlowUp f K) := by
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
  obtain ⟨K, hKfp, hKsupp, hflat⟩ :=
    exists_flatteningCentre_supportSet_eq_compl f X.unitModule U hU hFfp hFflat
  exact ⟨K, hKfp, hKsupp, (flat_strictTransformToBlowUp_iff f K).mpr hflat⟩

end AlgebraicGeometry

end
