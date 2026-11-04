module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.ContinuousActions
public import StacksCore.CategoryTheory.CofilteredSystem
public import StacksCore.Tactic.StacksAttribute

/-!
# Exact functors on finite continuous group actions

An exact set-valued functor on the category of finite continuous actions of a topological
group, whose values are finite, is naturally isomorphic to the underlying-set functor.

## Main results

* `CategoryTheory.nonempty_iso_forget_of_preservesFiniteLimits_and_colimits` identifies such a
  functor with the underlying-set functor.

## Implementation notes

The category of finite continuous `G`-sets is represented by `ContAction FintypeCat G`.
Exactness is represented by preservation of finite limits and finite colimits. The pointwise
finiteness assumption remains explicit. The argument first upgrades an exact functor on an
arbitrary Galois category to one reflecting isomorphisms, and then produces an isomorphism of
fibre functors from a section of the pro-representing cofiltered system.

## References

* [Stacks Project, Tag 0BMV](https://stacks.math.columbia.edu/tag/0BMV)
* [Stacks Project, Tag 0034](https://stacks.math.columbia.edu/tag/0034)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open scoped FintypeCatDiscrete

universe u v

namespace CategoryTheory

section ExactFunctor
variable {C : Type*} [Category C] [PreGaloisCategory C]
    (H : C ⥤ FintypeCat.{u}) [PreGaloisCategory.FiberFunctor H]
    (F : C ⥤ Type*) [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- An exact functor takes a nonempty value wherever the fibre functor does.

The hypothesis `[Nonempty (H.obj X)]` constrains the *fibre functor* `H`, while the conclusion
is about the *other* functor `F`, so it neither gives away the conclusion nor makes the statement
vacuous. It is deliberate and cannot be dropped: `Nonempty (H.obj (⊤_ C))` always holds, so the
hypothesis is satisfiable, whereas `F.obj (⊥_ C)` is empty for every `F` preserving finite
colimits, so the hypothesis-free form `∀ X, Nonempty (F.obj X)` is false. The one call site below
discharges it from `¬ IsEmpty (H.obj Z)`. -/
private lemma nonempty_obj_of_nonempty_fiber (X : C) [Nonempty (H.obj X)] :
    Nonempty (F.obj X) := by
  let H' := H ⋙ FintypeCat.incl
  let : Unique (H'.obj (⊤_ C)) := Types.isTerminalEquivUnique _
    (terminalIsTerminal.isTerminalObj H' (⊤_ C))
  have : Epi (H'.map (terminal.from X)) := ConcreteCategory.epi_of_surjective _
    (fun y ↦ ⟨Classical.arbitrary (H.obj X), Subsingleton.elim _ _⟩)
  have : Epi (terminal.from X) := Functor.epi_of_epi_map H' inferInstance
  have : Unique (F.obj (⊤_ C)) := Types.isTerminalEquivUnique _
    (terminalIsTerminal.isTerminalObj F (⊤_ C))
  obtain ⟨x, _⟩ := (surjective_of_epi (F.map (terminal.from X))) default
  exact ⟨x⟩

include H in
private lemma isIso_of_mono_of_map_isIso {X Y : C} (i : X ⟶ Y) [Mono i]
    [IsIso (F.map i)] : IsIso i := by
  obtain ⟨Z, j, ⟨hc⟩⟩ := PreGaloisCategory.monoInducesIsoOnDirectSummand i
  have hc' : IsColimit (BinaryCofan.mk (F.map i) (F.map j)) :=
    (isColimitMapCoconeBinaryCofanEquiv F i j) (isColimitOfPreserves F hc)
  have hd := ((Types.binaryCofan_isColimit_iff _).mp ⟨hc'⟩).2.2.disjoint
  have he : IsEmpty (F.obj Z) := ⟨fun z ↦ by
    obtain ⟨x, hx⟩ := surjective_of_epi (F.map i) (F.map j z)
    exact Set.disjoint_left.mp hd ⟨x, hx⟩ ⟨z, rfl⟩⟩
  have he' : IsEmpty (H.obj Z) := by
    by_contra hn
    have : Nonempty (H.obj Z) := not_isEmpty_iff.mp hn
    obtain ⟨z⟩ := nonempty_obj_of_nonempty_fiber H F Z
    exact he.false z
  obtain ⟨hz⟩ := (PreGaloisCategory.initial_iff_fiber_empty H Z).mpr he'
  exact (BinaryCofan.isColimit_iff_isIso_inl hz (BinaryCofan.mk i j)).mp ⟨hc⟩

include H in
private lemma faithful_of_preservesFiniteLimits_and_colimits : F.Faithful where
  map_injective {X Y} f g h := by
    have : IsIso (equalizer.ι (F.map f) (F.map g)) := equalizer.ι_of_eq h
    have : IsIso (F.map (equalizer.ι f g)) := by
      rw [← equalizerComparison_comp_π f g F]
      infer_instance
    have : IsIso (equalizer.ι f g) := isIso_of_mono_of_map_isIso H F _
    exact eq_of_epi_equalizer

include H in
private lemma reflectsIsomorphisms_of_preservesFiniteLimits_and_colimits :
    F.ReflectsIsomorphisms := by
  have : F.Faithful := faithful_of_preservesFiniteLimits_and_colimits H F
  refine ⟨fun {X Y} f hf ↦ ?_⟩
  have : Mono f := Functor.mono_of_mono_map F inferInstance
  exact isIso_of_mono_of_map_isIso H F f
end ExactFunctor

private noncomputable def natTransEquivSections
    {C : Type u} [Category.{v} C] [GaloisCategory C]
    (F : C ⥤ FintypeCat.{v}) [PreGaloisCategory.FiberFunctor F]
    (H : C ⥤ FintypeCat.{v}) :
    (F ⟶ H) ≃
      (PreGaloisCategory.PointedGaloisObject.incl F ⋙ H ⋙ FintypeCat.incl).sections :=
  let F' := F ⋙ FintypeCat.incl
  let H' := H ⋙ FintypeCat.incl
  let e₁ : (F ⟶ H) ≃ (F' ⟶ H') :=
    (FullyFaithful.whiskeringRight (FullyFaithful.ofFullyFaithful FintypeCat.incl) C).homEquiv
  let e₂ : (F' ⟶ H') ≅
      (colimit ((PreGaloisCategory.PointedGaloisObject.incl F).op ⋙ coyoneda) ⟶ H') :=
    (yoneda.obj H').mapIso (colimit.isoColimitCocone
      ⟨PreGaloisCategory.PointedGaloisObject.cocone F,
        PreGaloisCategory.PointedGaloisObject.isColimit F⟩).op
  let e₃ : (colimit ((PreGaloisCategory.PointedGaloisObject.incl F).op ⋙ coyoneda) ⟶ H') ≅
      limit ((PreGaloisCategory.PointedGaloisObject.incl F ⋙ H') ⋙ uliftFunctor.{u}) :=
    colimitCoyonedaHomIsoLimit' (PreGaloisCategory.PointedGaloisObject.incl F) H'
  let e₄ := Types.limitEquivSections
    ((PreGaloisCategory.PointedGaloisObject.incl F ⋙ H') ⋙ uliftFunctor.{u})
  let e₅ := (Types.sectionsEquiv
    (PreGaloisCategory.PointedGaloisObject.incl F ⋙ H')).symm
  e₁.trans <| e₂.toEquiv.trans <| e₃.toEquiv.trans <| e₄.trans e₅

private theorem nonempty_natTrans
    {C : Type u} [Category.{v} C] [GaloisCategory C]
    (F H : C ⥤ FintypeCat.{v}) [PreGaloisCategory.FiberFunctor F]
    [PreGaloisCategory.FiberFunctor H] : Nonempty (F ⟶ H) := by
  apply (natTransEquivSections F H).nonempty_congr.mpr
  let K := PreGaloisCategory.PointedGaloisObject.incl F ⋙ H ⋙ FintypeCat.incl
  have : ∀ j, Finite (K.obj j) := fun j ↦ (H.obj j.obj).property
  have : ∀ j, Nonempty (K.obj j) := fun j ↦
    ⟨Classical.choice (PreGaloisCategory.nonempty_fiber_of_isConnected H j.obj)⟩
  exact (nonempty_sections_of_finite_cofiltered_system K).to_subtype

@[sga "1 V 5.7"]
private theorem nonempty_fiberFunctor_iso
    {C : Type u} [Category.{v} C] [GaloisCategory C]
    (F H : C ⥤ FintypeCat.{v}) [PreGaloisCategory.FiberFunctor F]
    [PreGaloisCategory.FiberFunctor H] : Nonempty (F ≅ H) := by
  obtain ⟨f⟩ := nonempty_natTrans F H
  obtain ⟨g⟩ := nonempty_natTrans H F
  have : IsIso (f ≫ g) := PreGaloisCategory.FibreFunctor.end_isIso F (f ≫ g)
  have : IsIso (g ≫ f) := PreGaloisCategory.FibreFunctor.end_isIso H (g ≫ f)
  have : Mono f := mono_of_mono f g
  have : IsSplitEpi f := IsSplitEpi.mk' ⟨inv (g ≫ f) ≫ g, by simp⟩
  have : IsIso f := isIso_of_mono_of_isSplitEpi f
  exact ⟨asIso f⟩

/-- **Stacks Project, Tag 0BMV.** An exact set-valued functor on finite continuous actions of a
topological group, with finite values, is naturally isomorphic to the underlying-set functor. -/
@[stacks 0BMV, sga "1 V 5.7" "Finite-G-Sets case"]
public theorem nonempty_iso_forget_of_preservesFiniteLimits_and_colimits
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (F : ContAction FintypeCat.{u} G ⥤ Type u)
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [∀ X, Finite (F.obj X)] :
    Nonempty (F ≅ forget (ContAction FintypeCat.{u} G)) := by
  let H := forget₂ (ContAction FintypeCat.{u} G) FintypeCat
  let F' : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u} :=
    ObjectProperty.lift _ F (fun X ↦ inferInstance)
  have hF' : F' ⋙ FintypeCat.incl = F := rfl
  have : PreservesFiniteLimits (F' ⋙ FintypeCat.incl) := hF'.symm ▸ inferInstance
  have : PreservesFiniteColimits (F' ⋙ FintypeCat.incl) := hF'.symm ▸ inferInstance
  have : PreservesFiniteLimits F' :=
    preservesFiniteLimits_of_reflects_of_preserves F' FintypeCat.incl
  have : PreservesFiniteColimits F' :=
    preservesFiniteColimits_of_reflects_of_preserves F' FintypeCat.incl
  have : F.ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_preservesFiniteLimits_and_colimits H F
  have : F'.ReflectsIsomorphisms := ⟨fun f hf ↦ by
    have : IsIso (F.map f) := FintypeCat.incl.map_isIso (F'.map f)
    exact isIso_of_reflects_iso f F⟩
  have : PreGaloisCategory.FiberFunctor F' := {
    preservesQuotientsByFiniteGroups := fun K _ _ ↦ by
      obtain ⟨K', hK', hfin, ⟨e⟩⟩ :=
        Finite.exists_type_univ_nonempty_mulEquiv.{u, 0} K
      let : Fintype K' := Fintype.ofFinite K'
      exact preservesColimitsOfShape_of_equiv e.toSingleObjEquiv.symm F' }
  obtain ⟨e⟩ := nonempty_fiberFunctor_iso F' H
  exact ⟨isoWhiskerRight e FintypeCat.incl⟩

end CategoryTheory
