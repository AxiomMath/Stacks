module

public import StacksCore.CategoryTheory.Filtration.Basic
public import StacksCore.CategoryTheory.Limits.Shapes.IsTerminal
public import StacksCore.CategoryTheory.Subobject.Lattice
import StacksCore.Tactic.StacksAttribute

/-!
# Finite filtrations

A filtration `F` on `X` is finite (Stacks 0121 (7)) if `F^nX = X` and `F^mX = 0` for some `n, m`.
We state the two halves separately, at the level of the inclusions `F^iX ⟶ X`, with no hypotheses
on the category. For a decreasing `ℤ`-filtration a top step at `n` gives top steps at all `m ≤ n`,
and a zero step at `m` gives zero steps at all `n ≥ m`. Both halves are inherited by induced and
quotient filtrations and transport along isomorphisms of filtered objects.

## Main definitions

* `Filtration.HasTopStep`: some inclusion `F.ι.app i` is an isomorphism.
* `Filtration.HasBotStep`: some step `F^jX` is an initial object.
* `Filtration.IsFinite`: a filtration with both a top step and an initial step.

## Main results

* `Filtration.isFinite_iff_subobject`: `F` is finite iff `F^nX = ⊤` and `F^mX = ⊥` in
  `Subobject X` for some `n, m`.
* `Filtration.isExhaustive_of_hasTopStep`: a filtration with a top step is exhaustive.
* `Filtration.isSeparated_of_hasBotStep`: a filtration with an initial step is separated.
* `Filtration.isIso_ι_app_of_le`, `Filtration.isZero_obj_of_le`: top steps propagate downwards
  and zero steps propagate upwards in a decreasing `ℤ`-filtration.
* `FilteredObject.isFinite_of_iso`: finiteness transports along isomorphisms of filtered objects.
* `FilteredObject.epi_hom_of_forall_epi_natTrans_app`: a morphism of filtered objects which is an
  epimorphism on every step is an epimorphism on the underlying objects when the target
  filtration has a top step.
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite

variable {C : Type*} [Category* C] {I : Type*} [Category* I]

namespace Filtration

variable {X : C}

/-- Some step of the filtration is all of `X`: the inclusion `F^iX ⟶ X` is an isomorphism for
some `i`. -/
class HasTopStep (F : Filtration X I) : Prop where
  exists_isIso : ∃ i, IsIso (F.ι.app i)

/-- Some step `F^jX` of the filtration is an initial object. -/
class HasBotStep (F : Filtration X I) : Prop where
  exists_isInitial : ∃ j, Nonempty (IsInitial (F.obj j))

/-- **Stacks 0121** (7).
A filtration is finite if some step is all of `X` and some step is an initial object. -/
@[mk_iff, stacks 0121 "(7) for an arbitrary index category and any category `C`"]
class IsFinite (F : Filtration X I) : Prop extends HasTopStep F, HasBotStep F

section Bridges

variable (F : Filtration X I)

/-- `F^iX = X` as a subobject iff the inclusion `F^iX ⟶ X` is an isomorphism. -/
lemma subobject_eq_top_iff (i : I) : F.subobject i = ⊤ ↔ IsIso (F.ι.app i) :=
  (Subobject.isIso_iff_mk_eq_top _).symm

/-- `F^jX = ⊥` as a subobject iff the step `F^jX` is initial. -/
lemma subobject_eq_bot_iff [HasInitial C] [InitialMonoClass C] (j : I) :
    F.subobject j = ⊥ ↔ Nonempty (IsInitial (F.obj j)) :=
  Subobject.mk_eq_bot_iff_nonempty_isInitial _

/-- The lattice form of `HasTopStep`. -/
lemma hasTopStep_iff : HasTopStep F ↔ ∃ i, F.subobject i = ⊤ :=
  ⟨fun ⟨⟨i, h⟩⟩ => ⟨i, (F.subobject_eq_top_iff i).2 h⟩,
    fun ⟨i, h⟩ => ⟨i, (F.subobject_eq_top_iff i).1 h⟩⟩

/-- The lattice form of `HasBotStep`. -/
lemma hasBotStep_iff [HasInitial C] [InitialMonoClass C] :
    HasBotStep F ↔ ∃ j, F.subobject j = ⊥ :=
  ⟨fun ⟨⟨j, h⟩⟩ => ⟨j, (F.subobject_eq_bot_iff j).2 h⟩,
    fun ⟨j, h⟩ => ⟨j, (F.subobject_eq_bot_iff j).1 h⟩⟩

/-- Stacks 0121 (7) in the lattice `Subobject X`: `F^nX = ⊤` and `F^mX = ⊥` for some `n, m`. -/
lemma isFinite_iff_subobject [HasInitial C] [InitialMonoClass C] :
    IsFinite F ↔ (∃ i, F.subobject i = ⊤) ∧ ∃ j, F.subobject j = ⊥ := by
  rw [isFinite_iff, hasTopStep_iff, hasBotStep_iff]

/-- With zero morphisms, a filtration with a zero step has a step which is a zero object. -/
lemma HasBotStep.exists_isZero [HasZeroMorphisms C] [HasBotStep F] : ∃ j, IsZero (F.obj j) :=
  let ⟨j, ⟨h⟩⟩ := HasBotStep.exists_isInitial (F := F); ⟨j, h.isZero⟩

/-- With zero morphisms, `HasBotStep` says that some step is a zero object. -/
lemma hasBotStep_iff_exists_isZero [HasZeroMorphisms C] :
    HasBotStep F ↔ ∃ j, IsZero (F.obj j) :=
  ⟨fun _ => HasBotStep.exists_isZero F, fun ⟨j, h⟩ => ⟨⟨j, ⟨h.isInitial⟩⟩⟩⟩

/-- A filtration with a top step is exhaustive, Stacks 0121 (9). -/
lemma isExhaustive_of_hasTopStep [HasTopStep F] : IsExhaustive F := by
  obtain ⟨i, hi⟩ := HasTopStep.exists_isIso (F := F)
  refine ⟨fun _ _ => le_top, fun S hS => ?_⟩
  rw [← subobject_eq_top_iff] at hi
  exact hi ▸ hS ⟨i, rfl⟩

/-- A filtration with a zero step is separated, Stacks 0121 (9). -/
lemma isSeparated_of_hasBotStep [HasInitial C] [InitialMonoClass C] [HasBotStep F] :
    IsSeparated F := by
  obtain ⟨j, hj⟩ := HasBotStep.exists_isInitial (F := F)
  refine ⟨fun _ _ => bot_le, fun S hS => ?_⟩
  rw [← subobject_eq_bot_iff] at hj
  exact hj ▸ hS ⟨j, rfl⟩

end Bridges

section Range

/-- Top steps propagate along index arrows: `F^iX = X` and `i ⟶ j` give `F^jX = X`. -/
lemma isIso_ι_app_of_hom (F : Filtration X I) {i j : I} (f : i ⟶ j) [IsIso (F.ι.app i)] :
    IsIso (F.ι.app j) := by
  have : IsSplitEpi (F.ι.app j) :=
    ⟨⟨⟨inv (F.ι.app i) ≫ F.step f, by
      rw [Category.assoc, F.step_comp_ι_app, IsIso.inv_hom_id]⟩⟩⟩
  exact isIso_of_mono_of_isSplitEpi _

/-- A top step at the source of an index arrow makes the step an isomorphism. -/
lemma isIso_step_of_isIso_ι_app (F : Filtration X I) {i j : I} (f : i ⟶ j)
    [IsIso (F.ι.app i)] : IsIso (F.step f) :=
  have := F.isIso_ι_app_of_hom f
  IsIso.of_isIso_fac_right (F.step_comp_ι_app f)

/-- Initial steps propagate backwards along index arrows: `F^jX` initial and `i ⟶ j` give `F^iX`
initial. -/
noncomputable def isInitialObjOfHom (F : Filtration X I) {i j : I} (f : i ⟶ j)
    (hj : IsInitial (F.obj j)) : IsInitial (F.obj i) :=
  have := hj.isIso_of_mono (F.step f)
  hj.ofIso (asIso (F.step f)).symm

/-- For a decreasing `ℤ`-filtration, `F^nX = X` implies `F^mX = X` for `m ≤ n`. -/
lemma isIso_ι_app_of_le (F : Filtration X ℤᵒᵖ) {m n : ℤ} (h : m ≤ n)
    (hn : IsIso (F.ι.app (op n))) : IsIso (F.ι.app (op m)) :=
  F.isIso_ι_app_of_hom (opHomOfLE h)

/-- For a decreasing `ℤ`-filtration, `F^mX` initial implies `F^nX` initial for `m ≤ n`. -/
noncomputable def isInitialObjOfLE (F : Filtration X ℤᵒᵖ) {m n : ℤ} (h : m ≤ n)
    (hm : IsInitial (F.obj (op m))) : IsInitial (F.obj (op n)) :=
  F.isInitialObjOfHom (opHomOfLE h) hm

/-- For a decreasing `ℤ`-filtration, `F^mX = 0` implies `F^nX = 0` for `m ≤ n`. -/
lemma isZero_obj_of_le [HasZeroMorphisms C] (F : Filtration X ℤᵒᵖ) {m n : ℤ} (h : m ≤ n)
    (hm : IsZero (F.obj (op m))) : IsZero (F.obj (op n)) :=
  (F.isInitialObjOfLE h hm.isInitial).isZero

end Range

section Pullback

variable [HasPullbacks C]

/-- The filtration induced along any morphism `f : Y ⟶ X` by a filtration with a top step has
a top step. -/
instance (F : Filtration X I) {Y : C} (f : Y ⟶ X) [HasTopStep F] : HasTopStep (F.pullback f) :=
  let ⟨i, _⟩ := HasTopStep.exists_isIso (F := F)
  ⟨⟨i, (IsPullback.of_hasPullback (F.ι.app i) f).isIso_snd_of_isIso⟩⟩

/-- The filtration induced along a monomorphism `f : Y ⟶ X` by a filtration with an initial step
has an initial step. -/
instance (F : Filtration X I) {Y : C} (f : Y ⟶ X) [Mono f] [HasBotStep F] :
    HasBotStep (F.pullback f) := by
  obtain ⟨j, ⟨hj⟩⟩ := HasBotStep.exists_isInitial (F := F)
  have h : IsInitial (Limits.pullback (F.ι.app j) f) := hj.ofMono (pullback.fst (F.ι.app j) f)
  exact ⟨⟨j, ⟨h⟩⟩⟩

/-- The filtration induced along a monomorphism by a finite filtration is finite. -/
instance (F : Filtration X I) {Y : C} (f : Y ⟶ X) [Mono f] [IsFinite F] :
    IsFinite (F.pullback f) := {}

end Pullback

section Pushforward

variable [HasImages C]

/-- In a balanced category, the image filtration of a filtration with a top step along an
epimorphism `e : X ⟶ Z` has a top step. -/
instance [Balanced C] (F : Filtration X I) {Z : C} (e : X ⟶ Z) [Epi e] [HasTopStep F] :
    HasTopStep (F.pushforward e) := by
  obtain ⟨i, _⟩ := HasTopStep.exists_isIso (F := F)
  refine ⟨⟨i, ?_⟩⟩
  have : Epi (F.ι.app i ≫ e) := epi_comp _ _
  have : Epi (image.ι (F.ι.app i ≫ e)) := epi_of_epi_fac (image.fac _)
  exact isIso_of_mono_of_epi (image.ι (F.ι.app i ≫ e))

/-- When morphisms out of initial objects are monomorphisms, the image filtration of a filtration
with an initial step along any morphism `e : X ⟶ Z` has an initial step. -/
instance [InitialMonoClass C] (F : Filtration X I) {Z : C} (e : X ⟶ Z) [HasBotStep F] :
    HasBotStep (F.pushforward e) :=
  let ⟨j, ⟨hj⟩⟩ := HasBotStep.exists_isInitial (F := F)
  have : Mono (F.ι.app j ≫ e) := hj.mono_from _
  ⟨⟨j, ⟨hj.ofIso (imageMonoIsoSource (F.ι.app j ≫ e)).symm⟩⟩⟩

/-- In a balanced category in which morphisms out of initial objects are monomorphisms, the
image filtration of a finite filtration along an epimorphism is finite. -/
instance [Balanced C] [InitialMonoClass C] (F : Filtration X I) {Z : C} (e : X ⟶ Z) [Epi e]
    [IsFinite F] : IsFinite (F.pushforward e) := {}

end Pushforward

end Filtration

namespace FilteredObject

open Filtration

/-- An isomorphism of filtered objects is an isomorphism on every step. -/
instance isIso_natTrans_app_of_isIso {A B : FilteredObject C I} (f : A ⟶ B) [IsIso f] (i : I) :
    IsIso (f.natTrans.app i) := by
  obtain ⟨-, h⟩ := (isIso_iff f).mp ‹_›
  exact h i

/-- Top steps transport along isomorphisms of filtered objects. -/
lemma hasTopStep_of_iso {A B : FilteredObject C I} (e : A ≅ B) [HasTopStep A.filtration] :
    HasTopStep B.filtration := by
  obtain ⟨i, _⟩ := HasTopStep.exists_isIso (F := A.filtration)
  have := isIso_hom_of_isIso e.hom
  have : IsIso (e.hom.natTrans.app i ≫ B.filtration.ι.app i) := by rw [e.hom.comm]; infer_instance
  exact ⟨⟨i, IsIso.of_isIso_comp_left (e.hom.natTrans.app i) _⟩⟩

/-- Initial steps transport along isomorphisms of filtered objects. -/
lemma hasBotStep_of_iso {A B : FilteredObject C I} (e : A ≅ B) [HasBotStep A.filtration] :
    HasBotStep B.filtration := by
  obtain ⟨j, ⟨hj⟩⟩ := HasBotStep.exists_isInitial (F := A.filtration)
  exact ⟨⟨j, ⟨hj.ofIso (asIso (e.hom.natTrans.app j))⟩⟩⟩

/-- Finiteness transports along isomorphisms of filtered objects. -/
lemma isFinite_of_iso {A B : FilteredObject C I} (e : A ≅ B) [IsFinite A.filtration] :
    IsFinite B.filtration :=
  have := hasTopStep_of_iso e
  have := hasBotStep_of_iso e
  ⟨⟩

/-- A morphism of filtered objects which is an epimorphism on every step is an epimorphism on
the underlying objects, once the target filtration has a top step. -/
theorem epi_hom_of_forall_epi_natTrans_app {X Y : FilteredObject C I} [HasTopStep Y.filtration]
    (u : X ⟶ Y) (h : ∀ i, Epi (u.natTrans.app i)) : Epi u.hom := by
  obtain ⟨i, hi⟩ := HasTopStep.exists_isIso (F := Y.filtration)
  have := h i
  have : Epi (X.filtration.ι.app i ≫ u.hom) := by rw [← u.comm]; infer_instance
  exact epi_of_epi (X.filtration.ι.app i) u.hom

end FilteredObject

end CategoryTheory
