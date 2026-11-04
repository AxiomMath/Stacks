module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import StacksCore.Tactic.StacksAttribute

/-! # Cohomological δ-functors: Stacks 010Q, 010R, 010S

Stacks 010Q: a *cohomological δ-functor* from an abelian category `𝒜` to an abelian category
`ℬ` is a family of additive functors `Fⁿ : 𝒜 ⥤ ℬ`, `n ≥ 0`, together with, for every short
exact sequence `0 → A → B → C → 0` of `𝒜`, connecting morphisms `δ : Fⁿ(C) ⟶ Fⁿ⁺¹(A)`, such
that the long sequence `0 → F⁰(A) → F⁰(B) → F⁰(C) → F¹(A) → F¹(B) → …` is exact and `δ` is
natural in the short exact sequence. Stacks 010R: a morphism of δ-functors is a family of
natural transformations `tⁿ : Fⁿ ⟶ Gⁿ` commuting with the connecting morphisms. Stacks 010S: a
δ-functor `F` is *universal* if every `t : F⁰ ⟶ G⁰` extends uniquely to a morphism of
δ-functors `F ⟶ G`.

## Design

* A short exact sequence is a Mathlib `ShortComplex 𝒜` together with a proof of
  `ShortComplex.ShortExact`; a morphism of short exact sequences is a morphism of short
  complexes. Nothing new is defined for them.
* The connecting morphism `δ` is indexed by the exactness proof, `DeltaFunctor.δ hS n`, and its
  naturality in the short exact sequence is the field `δ_naturality`. This is the same data as
  a natural transformation on the full subcategory of short exact sequences (the choice made in
  the Liquid Tensor Experiment, which had no `ShortComplex` API), without the functor-composition
  layer in every statement, and it matches Mathlib's `Functor.homologySequenceδ` and
  `ShortComplex.ShortExact.singleδ`. Indexing `δ` by the exactness proof (rather than defining it
  on all short complexes) is what makes 010U, uniqueness up to unique isomorphism, true as stated.
* The exactness of the long sequence is recorded three terms at a time: `exact_map` for
  `Fⁿ(A) → Fⁿ(B) → Fⁿ(C)` (Mathlib's `S.map (Fⁿ)`), `exact_δ₁` for `Fⁿ(B) → Fⁿ(C) → Fⁿ⁺¹(A)`,
  `exact_δ₂` for `Fⁿ(C) → Fⁿ⁺¹(A) → Fⁿ⁺¹(B)`, and `mono_map_f` for `0 → F⁰(A) → F⁰(B)`; the two
  composition-to-zero facts needed to write the short complexes are the fields `map_g_δ` and
  `δ_map_f`.

The theorems of the section (010T: effaceable δ-functors are universal; 010U: uniqueness) live
in `StacksCore.CategoryTheory.Abelian.DeltaFunctor.Effaceable`.
-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory

open Limits

variable (A : Type u) [Category.{v} A] (B : Type u') [Category.{v'} B]

/-- Stacks 010Q: a cohomological δ-functor from `A` to `B`: additive functors `Fⁿ : A ⥤ B`
(`n ≥ 0`) and, for every short exact sequence `0 → X₁ → X₂ → X₃ → 0` of `A`, connecting
morphisms `δ : Fⁿ(X₃) ⟶ Fⁿ⁺¹(X₁)`, natural in the short exact sequence, such that
`0 → F⁰(X₁) → F⁰(X₂) → F⁰(X₃) → F¹(X₁) → F¹(X₂) → …` is exact. -/
@[stacks 010Q "cohomological δ-functor: additive `Fⁿ`, long exact sequence, natural `δ`"]
structure DeltaFunctor [Preadditive A] [Preadditive B] where
  /-- The functors `Fⁿ`, `n ≥ 0`. -/
  functor : ℕ → A ⥤ B
  /-- Each `Fⁿ` is additive. -/
  [additive : ∀ n, (functor n).Additive]
  /-- The connecting morphism `δ : Fⁿ(X₃) ⟶ Fⁿ⁺¹(X₁)` of a short exact sequence
  `0 → X₁ → X₂ → X₃ → 0`. -/
  δ : ∀ {S : ShortComplex A}, S.ShortExact → ∀ n : ℕ,
    (functor n).obj S.X₃ ⟶ (functor (n + 1)).obj S.X₁
  /-- `Fⁿ(X₂) → Fⁿ(X₃) → Fⁿ⁺¹(X₁)` composes to zero. -/
  map_g_δ : ∀ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ), (functor n).map S.g ≫ δ hS n = 0
  /-- `Fⁿ(X₃) → Fⁿ⁺¹(X₁) → Fⁿ⁺¹(X₂)` composes to zero. -/
  δ_map_f : ∀ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ),
    δ hS n ≫ (functor (n + 1)).map S.f = 0
  /-- `0 → F⁰(X₁) → F⁰(X₂)` is exact: `F⁰` preserves the monomorphism of a short exact
  sequence. -/
  mono_map_f : ∀ {S : ShortComplex A}, S.ShortExact → Mono ((functor 0).map S.f)
  /-- `Fⁿ(X₁) → Fⁿ(X₂) → Fⁿ(X₃)` is exact. -/
  exact_map : ∀ {S : ShortComplex A}, S.ShortExact → ∀ n : ℕ, (S.map (functor n)).Exact
  /-- `Fⁿ(X₂) → Fⁿ(X₃) → Fⁿ⁺¹(X₁)` is exact. -/
  exact_δ₁ : ∀ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ),
    (ShortComplex.mk ((functor n).map S.g) (δ hS n) (map_g_δ hS n)).Exact
  /-- `Fⁿ(X₃) → Fⁿ⁺¹(X₁) → Fⁿ⁺¹(X₂)` is exact. -/
  exact_δ₂ : ∀ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ),
    (ShortComplex.mk (δ hS n) ((functor (n + 1)).map S.f) (δ_map_f hS n)).Exact
  /-- `δ` is natural in the short exact sequence: for a morphism `φ` of short exact sequences,
  `Fⁿ(φ₃) ≫ δ = δ ≫ Fⁿ⁺¹(φ₁)`. -/
  δ_naturality : ∀ {S T : ShortComplex A} (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T)
    (n : ℕ), (functor n).map φ.τ₃ ≫ δ hT n = δ hS n ≫ (functor (n + 1)).map φ.τ₁

namespace DeltaFunctor

variable {A B}

attribute [instance] additive

attribute [reassoc] map_g_δ δ_map_f

attribute [reassoc] δ_naturality

variable [Preadditive A] [Preadditive B] (F : DeltaFunctor A B)

/-- `Fⁿ(X₁) → Fⁿ(X₂) → Fⁿ(X₃)` composes to zero (this needs no exactness: `Fⁿ` is additive). -/
@[reassoc (attr := simp)]
lemma map_f_comp_map_g {S : ShortComplex A} (n : ℕ) :
    (F.functor n).map S.f ≫ (F.functor n).map S.g = 0 := by
  rw [← Functor.map_comp, S.zero, Functor.map_zero]

/-- The short complex `Fⁿ(X₂) → Fⁿ(X₃) → Fⁿ⁺¹(X₁)`. -/
abbrev scδ₁ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) : ShortComplex B :=
  ShortComplex.mk ((F.functor n).map S.g) (F.δ hS n) (F.map_g_δ hS n)

/-- The short complex `Fⁿ(X₃) → Fⁿ⁺¹(X₁) → Fⁿ⁺¹(X₂)`. -/
abbrev scδ₂ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) : ShortComplex B :=
  ShortComplex.mk (F.δ hS n) ((F.functor (n + 1)).map S.f) (F.δ_map_f hS n)

lemma scδ₁_exact {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) : (F.scδ₁ hS n).Exact :=
  F.exact_δ₁ hS n

lemma scδ₂_exact {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) : (F.scδ₂ hS n).Exact :=
  F.exact_δ₂ hS n

/-- If `Fⁿ⁺¹(X₁) → Fⁿ⁺¹(X₂)` is zero then the connecting morphism `δ : Fⁿ(X₃) ⟶ Fⁿ⁺¹(X₁)` is
an epimorphism (exactness of `Fⁿ(X₃) → Fⁿ⁺¹(X₁) → Fⁿ⁺¹(X₂)`). -/
lemma epi_δ_of_map_f_eq_zero {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ)
    (h : (F.functor (n + 1)).map S.f = 0) : Epi (F.δ hS n) :=
  (F.exact_δ₂ hS n).epi_f h

/-- If `Fⁿ(X₂) → Fⁿ(X₃)` is zero then the connecting morphism `δ : Fⁿ(X₃) ⟶ Fⁿ⁺¹(X₁)` is a
monomorphism (exactness of `Fⁿ(X₂) → Fⁿ(X₃) → Fⁿ⁺¹(X₁)`). -/
lemma mono_δ_of_map_g_eq_zero {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ)
    (h : (F.functor n).map S.g = 0) : Mono (F.δ hS n) :=
  (F.exact_δ₁ hS n).mono_g h

/-- When `Fⁿ⁺¹(X₁) → Fⁿ⁺¹(X₂)` is zero, `δ : Fⁿ(X₃) ⟶ Fⁿ⁺¹(X₁)` is a cokernel of
`Fⁿ(X₂) → Fⁿ(X₃)`. This is the description `Fⁿ⁺¹(X₁) = Coker(Fⁿ(X₂) → Fⁿ(X₃))` used in the
proof of Stacks 010T. -/
noncomputable def δIsCokernel [Balanced B] {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) (h : (F.functor (n + 1)).map S.f = 0) :
    IsColimit (CokernelCofork.ofπ (F.δ hS n) (F.map_g_δ hS n)) :=
  haveI := F.epi_δ_of_map_f_eq_zero hS n h
  (F.exact_δ₁ hS n).gIsCokernel

section Hom

variable {F} {G : DeltaFunctor A B}

/-- Stacks 010R: a morphism of δ-functors `F ⟶ G` is a family of natural transformations
`tⁿ : Fⁿ ⟶ Gⁿ` commuting with the connecting morphisms of every short exact sequence. -/
@[stacks 010R "morphism of δ-functors: `tⁿ : Fⁿ ⟶ Gⁿ` commuting with the `δ`", ext]
structure Hom (F G : DeltaFunctor A B) where
  /-- The components `tⁿ : Fⁿ ⟶ Gⁿ`. -/
  app : ∀ n : ℕ, F.functor n ⟶ G.functor n
  /-- Compatibility with the connecting morphisms: `tⁿ(X₃) ≫ δ_G = δ_F ≫ tⁿ⁺¹(X₁)`. -/
  comm : ∀ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ),
    (app n).app S.X₃ ≫ G.δ hS n = F.δ hS n ≫ (app (n + 1)).app S.X₁ := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm

/-- δ-functors from `A` to `B` form a category. -/
@[simps id_app comp_app]
instance : Category (DeltaFunctor A B) where
  Hom := Hom
  id F := { app := fun _ ↦ 𝟙 _ }
  comp η γ := { app := fun n ↦ η.app n ≫ γ.app n }

/-- Two morphisms of δ-functors agree if all their components do. -/
@[ext]
lemma hom_ext {η γ : F ⟶ G} (h : ∀ n, η.app n = γ.app n) : η = γ :=
  Hom.ext (funext h)

/-- Componentwise, a morphism of δ-functors is a natural transformation. -/
@[reassoc]
lemma Hom.naturality (η : F ⟶ G) (n : ℕ) {X Y : A} (f : X ⟶ Y) :
    (F.functor n).map f ≫ (η.app n).app Y = (η.app n).app X ≫ (G.functor n).map f :=
  (η.app n).naturality f

end Hom

/-- Stacks 010S: a δ-functor `F` is universal if every natural transformation `t : F⁰ ⟶ G⁰`
extends uniquely to a morphism of δ-functors `F ⟶ G`. -/
@[stacks 010S "universal δ-functor: every `t : F⁰ ⟶ G⁰` extends uniquely to `F ⟶ G`"]
class IsUniversal (F : DeltaFunctor A B) : Prop where
  /-- Existence and uniqueness of the extension of `t : F⁰ ⟶ G⁰`. -/
  existsUnique (G : DeltaFunctor A B) (t : F.functor 0 ⟶ G.functor 0) : ∃! η : F ⟶ G, η.app 0 = t

namespace IsUniversal

variable [F.IsUniversal] {G : DeltaFunctor A B}

/-- The extension of `t : F⁰ ⟶ G⁰` to a morphism of δ-functors out of a universal `F`. -/
noncomputable def lift (t : F.functor 0 ⟶ G.functor 0) : F ⟶ G :=
  (IsUniversal.existsUnique G t).choose

@[simp]
lemma lift_app_zero (t : F.functor 0 ⟶ G.functor 0) : (lift F t).app 0 = t :=
  (IsUniversal.existsUnique G t).choose_spec.1

/-- Morphisms out of a universal δ-functor are determined by their degree-zero component. -/
lemma hom_ext_zero {η γ : F ⟶ G} (h : η.app 0 = γ.app 0) : η = γ := by
  obtain ⟨_, _, hu⟩ := IsUniversal.existsUnique G (η.app 0)
  exact (hu η rfl).trans (hu γ h.symm).symm

lemma eq_lift (η : F ⟶ G) : η = lift F (η.app 0) :=
  hom_ext_zero F (by simp)

end IsUniversal

end DeltaFunctor

end CategoryTheory
