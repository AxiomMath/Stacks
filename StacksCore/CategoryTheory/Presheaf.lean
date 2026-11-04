module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
import StacksCore.Tactic.StacksAttribute

/-! # Presheaves
This file adds stacks tags to various mathlib declarations around presheaves.
-/

universe w v u

public section

namespace CategoryTheory

add_to_stacks 00V2 "Since presheaves are just functors, no extra definition is introduced - the
  category of presheaves on `C` is just the functor category `Cᵒᵖ ⥤ Type w`."
  CategoryTheory.Functor

add_to_stacks 00V3 "Since presheaves are just functors, no extra definition is introduced - the
  category of `A`-valued presheaves on `C` is just the functor category `Cᵒᵖ ⥤ A`."
  CategoryTheory.Functor

add_to_stacks 00V6 "Mathlib defines a more generally property of being locally injective with
  respect to a Grothendieck topology; letting that be the trivial topology recovers the property
  of being injective." Presheaf.IsLocallyInjective
add_to_stacks 00V6 "Mathlib defines a more generally property of being locally surjective with
  respect to a Grothendieck topology; letting that be the trivial topology recovers the property
  of being surjective." Presheaf.IsLocallySurjective

/-- A morphism of presheaves is locally injective with respect to the trivial topology if and only
if it is injective. -/
@[stacks 00V6]
lemma Presheaf.isLocallyInjective_bot {C : Type*} [Category* C] {A : Type*} [Category* A]
    {FA : A → A → Type*} {CA : A → Type*} [(X Y : A) → FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory A FA] {F G : Cᵒᵖ ⥤ A} {f : F ⟶ G} :
    IsLocallyInjective ⊥ f ↔ ∀ X, Function.Injective (f.app X) := by
  refine ⟨fun h X x x' hx ↦ ?_, isLocallyInjective_of_injective _ _⟩
  simpa using h.equalizerSieve_mem x x' hx

/-- A morphism of presheaves is locally surjective with respect to the trivial topology if and only
if it is surjective. -/
@[stacks 00V6]
lemma Presheaf.isLocallySurjective_bot {C : Type*} [Category* C] {A : Type*} [Category* A]
    {FA : A → A → Type*} {CA : A → Type*} [(X Y : A) → FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory A FA] {F G : Cᵒᵖ ⥤ A} {f : F ⟶ G} :
    IsLocallySurjective ⊥ f ↔ ∀ X, Function.Surjective (f.app X) := by
  refine ⟨fun h X x ↦ ?_, isLocallySurjective_of_surjective _ _⟩
  simpa [← Sieve.id_mem_iff_eq_top, imageSieve] using h.imageSieve_mem x

lemma Presheaf.IsLocallyInjective.mono {C : Type*} [Category* C] {A : Type*} [Category* A]
    {FA : A → A → Type*} {CA : A → Type*} [(X Y : A) → FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory A FA] {F G : Cᵒᵖ ⥤ A} {f : F ⟶ G}
    {J J' : GrothendieckTopology C} (h : J ≤ J')
    (hf : IsLocallyInjective J f) : IsLocallyInjective J' f where
  equalizerSieve_mem _ _ h' := h _ <| hf.equalizerSieve_mem _ _ h'

/-- Every injective morphism of presheaves is a monomorphism. -/
lemma Presheaf.mono_of_isLocallyInjective_bot {C : Type*} [Category* C] {A : Type*} [Category* A]
    {FA : A → A → Type*} {CA : A → Type*} [(X Y : A) → FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory A FA] [Limits.HasPullbacks A] {F G : Cᵒᵖ ⥤ A} {f : F ⟶ G}
    (hf : IsLocallyInjective ⊥ f) : Mono f := by
  rw [isLocallyInjective_bot] at hf
  rw [NatTrans.mono_iff_mono_app]
  exact fun _ ↦ ConcreteCategory.mono_of_injective _ <| hf _

/-- A morphism of presheaves of types is injective if and only if it is a monomorphism. -/
@[stacks 00V7]
lemma Presheaf.isLocallyInjective_bot_iff_mono {C : Type*} [Category* C] {F G : Cᵒᵖ ⥤ Type w}
    {f : F ⟶ G} : IsLocallyInjective ⊥ f ↔ Mono f := by
  simp only [isLocallyInjective_bot, NatTrans.mono_iff_mono_app, mono_iff_injective]

lemma Presheaf.IsLocallySurjective.mono {C : Type*} [Category* C] {A : Type*} [Category* A]
    {FA : A → A → Type*} {CA : A → Type*} [(X Y : A) → FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory A FA] {F G : Cᵒᵖ ⥤ A} {f : F ⟶ G}
    {J J' : GrothendieckTopology C} (h : J ≤ J')
    (hf : IsLocallySurjective J f) : IsLocallySurjective J' f where
  imageSieve_mem _ := h _ <| hf.imageSieve_mem _

/-- Every surjective morphism of presheaves is an epimorphism. -/
lemma Presheaf.epi_of_isLocallySurjective_bot {C : Type*} [Category* C] {A : Type*} [Category* A]
    {FA : A → A → Type*} {CA : A → Type*} [(X Y : A) → FunLike (FA X Y) (CA X) (CA Y)]
    [ConcreteCategory A FA] [Limits.HasPushouts A] {F G : Cᵒᵖ ⥤ A} {f : F ⟶ G}
    (hf : IsLocallySurjective ⊥ f) : Epi f := by
  rw [isLocallySurjective_bot] at hf
  rw [NatTrans.epi_iff_epi_app]
  exact fun _ ↦ ConcreteCategory.epi_of_surjective _ <| hf _

/-- A morphism of presheaves of types is surjective if and only if it is an epimorphism. -/
@[stacks 00V7]
lemma Presheaf.isLocallySurjective_bot_iff_epi {C : Type*} [Category* C] {F G : Cᵒᵖ ⥤ Type w}
    {f : F ⟶ G} : IsLocallySurjective ⊥ f ↔ Epi f := by
  simp only [isLocallySurjective_bot, NatTrans.epi_iff_epi_app, epi_iff_surjective]

/-- A morphism of presheaves of types is an isomorphism if and only if it is both injective and
surjective. -/
@[stacks 00V7, sga "4 I 3.3" "mono + epi => iso"]
lemma Presheaf.isIso_iff_isLocallyBijective {C : Type*} [Category* C] {F G : Cᵒᵖ ⥤ Type w}
    {f : F ⟶ G} : IsIso f ↔ IsLocallyInjective ⊥ f ∧ IsLocallySurjective ⊥ f := by
  rw [isIso_iff_mono_and_epi, isLocallySurjective_bot_iff_epi, isLocallyInjective_bot_iff_mono]

add_to_stacks 00V8 Subfunctor

-- Stacks 00V9 asserts that the subpresheaf is UNIQUE as well as that it exists.
-- `Subfunctor.toRange_ι` is the range factorisation alone, so it does not cover the tag; the tag is
-- stated whole by `CategoryTheory.Presheaf.existsUnique_subfunctor_surjective_factorization`.

add_to_stacks 00VA Subfunctor.range

end CategoryTheory
