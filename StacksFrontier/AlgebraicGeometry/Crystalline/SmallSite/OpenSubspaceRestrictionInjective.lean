module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekSliceEquivalenceExact
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisModuleDirectImage
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ChangeBaseConnectedLimits
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LowerShriekAbelianExact
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenSubspaceCoreflection
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ZariskiModuleDirectImage

/-!
# Restricting sheaves of modules to an open of `X` preserves injective objects

For an open `V` of `X`, restriction of sheaves of `𝒪_{X/S}`-modules from `Cris(X/S)` to
`Cris(V/S)`, `...SmallSite.openSubspaceModuleRestriction`, carries injective modules to injective
modules.  This is what lets the right derived functor of a functor precomposed with restriction be
computed by restricting an injective resolution, the identification the remark of
[Stacks, Tag 07ML] takes for granted when it writes `Rf'_{cris, *}F'` for the value of the
restricted direct image.

The proof is `Stacks.SheafOfModules.preservesInjectiveObjects_pullback_of_sliceEquivalence`, the
module form of [Stacks, Tag 03F3] (1) for a functor of sites whose slice functors are equivalences:
the inclusion `u : Cris(V/S) ⥤ Cris(X/S)` is fully faithful and its essential image is closed
under passing to objects mapping into it, so each `Over.post u` is an equivalence.  That lemma
asks the rings to live at the universe of the sections, so it is applied to the universe lift of
the structure sheaf, and transported back along the ring-universe isomorphisms of categories.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `CrystallineThickening.range_toX_subset_of_hom` — an object of `Cris(X/S)` mapping to one lying
  over `V` lies over `V`.
* `isEquivalence_overPost_openSubspaceInclusion` — the slice functors of `u` are equivalences.
* `openSubspaceModuleRestriction_preservesInjectiveObjects` — restriction of modules to
  `Cris(V/S)` preserves injective objects.

## References

* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 07ML](https://stacks.math.columbia.edu/tag/07ML)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} (V : S.X.Opens)

namespace CrystallineThickening

/-- An object of `Cris(X/S)` with a morphism to an object lying over `V` lies over `V`: its map
to `X` factors through the map to `X` of the target. -/
theorem range_toX_subset_of_hom {A B : CrystallineThickening S} (g : A ⟶ B)
    (hB : Set.range ⇑B.obj.toX.base ⊆ Set.range ⇑V.ι.base) :
    Set.range ⇑A.obj.toX.base ⊆ Set.range ⇑V.ι.base := by
  rintro _ ⟨x, rfl⟩
  have : A.obj.toX.base x = B.obj.toX.base (g.hom.sourceHom.base x) := by
    rw [← Scheme.Hom.comp_apply, g.hom.toX_naturality]
  rw [this]
  exact hB ⟨_, rfl⟩

end CrystallineThickening

open _root_.Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening

/-- **The slice functors of the inclusion `Cris(V/S) ⥤ Cris(X/S)` are essentially surjective**:
an object of `Cris(X/S)` over `u(B)` lies over `V`, hence comes from `Cris(V/S)`, and the
inclusion being full its structure morphism comes from one over `B`. -/
instance essSurj_overPost_openSubspaceInclusion (B : CrystallineThickening (openSubspace S V)) :
    (Over.post (X := B) (openSubspaceInclusion S V)).EssSurj where
  mem_essImage Y := by
    have hY : Set.range ⇑Y.left.obj.toX.base ⊆ Set.range ⇑V.ι.base :=
      range_toX_subset_of_hom V Y.hom (range_toX_openSubspaceInclusion_obj_subset V B)
    obtain ⟨A, ⟨e⟩⟩ := smallChangeBase_essImage_of_range_toX_subset
      (h := openSubspace_changeBase_condition S V)
      (DividedPowerScheme.isInducedOpen_of_isIso (𝟙 S.S)) Y.left hY
    refine ⟨Over.mk ((openSubspaceInclusion S V).preimage (e.hom ≫ Y.hom)), ⟨?_⟩⟩
    exact Over.isoMk e (by exact ((openSubspaceInclusion S V).map_preimage _).symm)

/-- **The slice functors of the inclusion `Cris(V/S) ⥤ Cris(X/S)` are equivalences**, the
inclusion being fully faithful with essential image closed under passing to objects mapping into
it. -/
instance isEquivalence_overPost_openSubspaceInclusion
    (B : CrystallineThickening (openSubspace S V)) :
    (Over.post (X := B) (openSubspaceInclusion S V)).IsEquivalence where

/-- The ring sheaf obtained by restricting the universe-lifted structure sheaf of `Cris(X/S)` to
`Cris(V/S)` is the universe-lifted structure sheaf of `Cris(V/S)`. -/
theorem inverseImageRing_structureSheafULift :
    Stacks.SheafOfModules.inverseImageRing (smallTopology (openSubspace S V)) (smallTopology S)
        (openSubspaceInclusion S V) (structureSheafULift S) =
      structureSheafULift (openSubspace S V) :=
  rfl

/-- **Restriction of modules over the universe-lifted structure sheaves** from `Cris(X/S)` to
`Cris(V/S)`. -/
abbrev openSubspaceModuleRestrictionULift :
    SheafOfModules.{u + 1} (structureSheafULift S) ⥤
      SheafOfModules.{u + 1} (structureSheafULift (openSubspace S V)) :=
  SheafOfModules.pushforward.{u + 1}
    (Stacks.SheafOfModules.structureMap (smallTopology (openSubspace S V)) (smallTopology S)
      (openSubspaceInclusion S V) (structureSheafULift S))

/-- **Restriction of modules over the universe-lifted structure sheaf to `Cris(V/S)` preserves
injective objects**, by the module form of [Stacks, Tag 03F3] (1) for a functor of sites whose
slice functors are equivalences. -/
theorem preservesInjectiveObjects_openSubspaceModuleRestrictionULift :
    (openSubspaceModuleRestrictionULift V).PreservesInjectiveObjects := by
  have := CrystallineThickening.hasPullbacks_crystallineThickening (openSubspace S V)
  have := CrystallineThickening.hasEqualizers_crystallineThickening (openSubspace S V)
  have : EssentiallySmall.{u + 1} (CrystallineThickening (openSubspace S V)) :=
    essentiallySmall_of_small_of_locallySmall _
  exact Stacks.SheafOfModules.preservesInjectiveObjects_pullback_of_sliceEquivalence.{u + 1}
    (smallTopology (openSubspace S V)) (smallTopology S) (openSubspaceInclusion S V)
    (structureSheafULift S)

/-- Restriction of modules to `Cris(V/S)` is, up to the two ring-universe isomorphisms of
categories, restriction of modules over the universe-lifted structure sheaves. -/
theorem openSubspaceModuleRestriction_eq_ulift :
    openSubspaceModuleRestriction S V =
      moduleRingULiftUp S ⋙ openSubspaceModuleRestrictionULift V ⋙
        moduleRingULiftDown (openSubspace S V) :=
  rfl

/-- **Restriction of sheaves of `𝒪_{X/S}`-modules to `Cris(V/S)` preserves injective objects.** -/
instance openSubspaceModuleRestriction_preservesInjectiveObjects :
    (openSubspaceModuleRestriction S V).PreservesInjectiveObjects := by
  have := preservesInjectiveObjects_openSubspaceModuleRestrictionULift V
  have : (moduleRingULiftDown (openSubspace S V)).IsEquivalence :=
    (moduleRingULiftEquivalence (openSubspace S V)).isEquivalence_inverse
  rw [openSubspaceModuleRestriction_eq_ulift]
  infer_instance

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
