module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Elementary properties of the fibre functor of a Galois category

The fibre functor of a Galois category detects the basic categorical notions: an object is
initial exactly when its fibre is empty and terminal exactly when its fibre is a singleton, a
morphism is mono exactly when its map on fibres is injective and epi exactly when that map is
surjective. Consequently the fibre functor is faithful, a morphism out of a connected object is
determined by the image of a single point, every morphism between connected objects is an
epimorphism, and a map out of a coproduct of connected objects into a finite coproduct factors
componentwise.

## Main results

* `CategoryTheory.isInitial_iff_isEmpty_fiber` and
  `CategoryTheory.isTerminal_iff_unique_fiber` characterise initial and terminal objects by
  their fibres.
* `CategoryTheory.IsGaloisCategory.mono_iff_injective` and
  `CategoryTheory.epi_iff_surjective_on_fiber`
  characterise monomorphisms and epimorphisms by their maps on fibres.
* `CategoryTheory.fiberFunctor_faithful` says the fibre functor is faithful.
* `CategoryTheory.hom_ext_of_isConnected` says two morphisms out of a connected object agree
  as soon as their maps on fibres agree at one point.
* `CategoryTheory.epi_of_connected` says every morphism between connected objects is an
  epimorphism.
* `CategoryTheory.exists_component_maps` factors a morphism from a coproduct of connected
  objects to a finite coproduct through a map of indexing types.

## Implementation notes

Each characterisation is obtained from exactness of the fibre functor together with the fact
that it reflects isomorphisms: reflection upgrades the preserved limit or colimit cone to one in
the source category, and the corresponding statement in `Type` is then elementary.

## References

* [Stacks Project, Tag 0BN0](https://stacks.math.columbia.edu/tag/0BN0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w x y

namespace CategoryTheory

/-- An object of a Galois category is initial if and only if its fibre is empty. -/
@[stacks 0BN0 "initial_iff_empty"]
public theorem isInitial_iff_isEmpty_fiber {C : Type u} [Category.{v, u} C]
    (F : C ⥤ Type w) [IsGaloisCategory F] (A : C) :
    Nonempty (IsInitial A) ↔ IsEmpty (F.obj A) := by
  let : ReflectsColimit (Functor.empty.{0} C) F := reflectsColimit_of_reflectsIsomorphisms _ _
  simpa only [Types.initial_iff_empty] using (IsInitial.isInitialIffObj F A).nonempty_congr

/-- An object of a Galois category is terminal if and only if its fibre is a singleton. -/
@[stacks 0BN0 "terminal_iff_singleton"]
public theorem isTerminal_iff_unique_fiber {C : Type u} [Category.{v, u} C]
    (F : C ⥤ Type w) [IsGaloisCategory F] (Z : C) :
    Nonempty (IsTerminal Z) ↔ Nonempty (Unique (F.obj Z)) := by
  let : ReflectsLimit (Functor.empty.{0} C) F := reflectsLimit_of_reflectsIsomorphisms _ _
  exact ((IsTerminal.isTerminalIffObj F Z).trans (Types.isTerminalEquivUnique _)).nonempty_congr

namespace IsGaloisCategory

/-- A morphism in a Galois category is mono if and only if its map on fibres is injective. -/
@[stacks 0BN0 "mono_iff_injective"]
public lemma mono_iff_injective {C : Type u} [Category.{v, u} C] (F : C ⥤ Type w)
    [IsGaloisCategory F] {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ Function.Injective (F.map f) :=
  (F.mono_map_iff_mono f).symm.trans (_root_.CategoryTheory.mono_iff_injective _)

end IsGaloisCategory

/-- A morphism in a Galois category is an epimorphism if and only if its map on fibres is
surjective. -/
@[stacks 0BN0 "epi_iff_surjective"]
public lemma epi_iff_surjective_on_fiber {C : Type u} [Category.{v, u} C]
    (F : C ⥤ Type w) [IsGaloisCategory F] {X Y : C} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective (F.map f) := by
  rw [← CategoryTheory.epi_iff_surjective]
  exact ⟨fun _ ↦ inferInstance, fun _ ↦
    (⟨fun g h ↦ (isIso_iff_of_reflects_iso g F).mp (h ())⟩ :
      JointlyReflectIsomorphisms (fun _ : Unit ↦ F)).epi f⟩

/-- The fibre functor of a Galois category is faithful. -/
@[stacks 0BN0 "faithful"]
public instance fiberFunctor_faithful {C : Type u} [Category.{v, u} C]
    (F : C ⥤ Type w) [IsGaloisCategory F] : F.Faithful := by
  refine ⟨fun {X Y f g} h => ?_⟩
  have : IsIso (F.map (equalizer.ι f g)) :=
    isIso_limit_cone_parallelPair_of_eq h (isLimitOfHasEqualizerOfPreservesLimit F f g)
  have : IsIso (equalizer.ι f g) := Functor.ReflectsIsomorphisms.reflects F _
  exact eq_of_epi_equalizer

/-- The fibre of a connected object of a Galois category is nonempty. -/
private theorem nonempty_fiber_of_isConnected {C : Type u} [Category.{v, u} C]
    (F : C ⥤ Type w) [IsGaloisCategory F] (X : C) [PreGaloisCategory.IsConnected X] :
    Nonempty (F.obj X) := by
  by_contra hn
  exact PreGaloisCategory.IsConnected.notInitial
    (Classical.choice ((isInitial_iff_isEmpty_fiber F X).2 (not_nonempty_iff.mp hn)))

/-- A monomorphism into a connected object is an isomorphism if its source has a fibre point. -/
private theorem isIso_of_isConnected_of_fiber {C : Type u} [Category.{v, u} C]
    (F : C ⥤ Type w) [IsGaloisCategory F] {X Z : C} [PreGaloisCategory.IsConnected X]
    (i : Z ⟶ X) [Mono i] (z : F.obj Z) : IsIso i :=
  PreGaloisCategory.IsConnected.noTrivialComponent Z i fun hi ↦
    ((isInitial_iff_isEmpty_fiber F Z).1 ⟨hi⟩).false z

/-- Two morphisms from a connected object agree if their maps on fibres agree at one point. -/
@[stacks 0BN0 "one_element"]
public lemma hom_ext_of_isConnected {C : Type u} [Category.{v, u} C]
    (F : C ⥤ Type w) [IsGaloisCategory F] {X Y : C}
    [PreGaloisCategory.IsConnected X] (a b : X ⟶ Y) (x : F.obj X)
    (h : F.map a x = F.map b x) : a = b := by
  have : IsIso (equalizer.ι a b) :=
    isIso_of_isConnected_of_fiber F _ <|
      (PreservesEqualizer.iso F a b ≪≫ Types.equalizerIso (F.map a) (F.map b)).toEquiv.symm ⟨x, h⟩
  exact eq_of_epi_equalizer

/-- Every morphism between connected objects in a Galois category is an epimorphism. -/
@[stacks 0BN0 "connected_epi"]
public theorem epi_of_connected {C : Type u} [Category.{v, u} C]
    (F : C ⥤ Type w) [IsGaloisCategory F] {X Y : C}
    [PreGaloisCategory.IsConnected X] [PreGaloisCategory.IsConnected Y]
    (f : X ⟶ Y) : Epi f := by
  refine Epi.mk ?_
  intro Z g h hfg
  have ⟨x⟩ := nonempty_fiber_of_isConnected F X
  have : IsIso (equalizer.ι g h) :=
    isIso_of_isConnected_of_fiber F _ (F.map (equalizer.lift f hfg) x)
  exact (cancel_epi (equalizer.ι g h)).mp (equalizer.condition g h)

/-- A map from a coproduct of connected objects to a finite coproduct factors componentwise
through a map of indexing types. -/
@[stacks 0BN0 "component_maps"]
public theorem exists_component_maps {C : Type u} [Category.{v, u} C]
    (F : C ⥤ Type w) [IsGaloisCategory F]
    {I : Type x} {J : Type y} [Finite J]
    (A : I → C) (B : J → C) (X Y : C)
    (a : (i : I) → A i ⟶ X) (b : (j : J) → B j ⟶ Y)
    (_ha : IsColimit (Cofan.mk X a)) (hb : IsColimit (Cofan.mk Y b))
    (hA : ∀ i, PreGaloisCategory.IsConnected (A i)) (f : X ⟶ Y) :
    ∃ (α : I → J) (g : (i : I) → A i ⟶ B (α i)),
      ∀ i, g i ≫ b (α i) = a i ≫ f := by
  classical
  have hbF : IsColimit (Cofan.mk (F.obj Y) (fun j => F.map (b j))) :=
    isColimitCofanMkObjOfIsColimit F B _ hb
  have hfactor : ∀ i, ∃ j, ∃ g : A i ⟶ B j, g ≫ b j = a i ≫ f := by
    intro i
    have := hA i
    obtain ⟨s⟩ := nonempty_fiber_of_isConnected F (A i)
    obtain ⟨j, t, ht⟩ :=
      Cofan.inj_jointly_surjective_of_isColimit hbF (F.map (a i ≫ f) s)
    have : Mono (b j) :=
      (IsGaloisCategory.mono_iff_injective F (b j)).2 (Cofan.inj_injective_of_isColimit hbF j)
    have : IsIso (pullback.fst (a i ≫ f) (b j)) :=
      isIso_of_isConnected_of_fiber F _
        ((isLimitOfHasPullbackOfPreservesLimit F (a i ≫ f) (b j)).lift
          (PullbackCone.mk (W := PUnit.{w + 1})
            (TypeCat.ofHom (fun _ : PUnit.{w + 1} => s))
            (TypeCat.ofHom (fun _ : PUnit.{w + 1} => t))
            (by ext x; exact ht.symm)) PUnit.unit)
    refine ⟨j, inv (pullback.fst (a i ≫ f) (b j)) ≫
      pullback.snd (a i ≫ f) (b j), ?_⟩
    rw [Category.assoc, ← pullback.condition]
    simp
  choose α g hg using hfactor
  exact ⟨α, g, hg⟩

end CategoryTheory
