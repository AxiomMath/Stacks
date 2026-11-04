module

public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.HomologicalConstructions

/-! # The homological δ-functor `Tᵢ = E²⁻ⁱ` of a cohomological δ-functor vanishing in degree three

Let `E` be a cohomological δ-functor `A ⥤ B` (Stacks 010Q) with `E³ = 0`. Reading its long exact
sequences backwards gives a homological δ-functor `T` with

* `T₀ = E²`, `T₁ = E¹`, `T₂ = E⁰` and `Tᵢ = 0` for `i ≥ 3`;
* connecting maps `T₁(X₃) ⟶ T₀(X₁)` and `T₂(X₃) ⟶ T₁(X₁)` the connecting maps `δ¹` and `δ⁰`
  of `E`.

The vanishing of `E³` is what makes `T₀ = E²` right exact, the last condition of a homological
δ-functor; the left exactness of `E⁰` gives exactness at `T₂(X₁)`.

This is how the compactly supported cohomology `H_c^{2-i}` of a curve, which lives in degrees
`0, 1, 2`, becomes a homological δ-functor in the representation (Stacks 03VM).

## Main definitions

* `Stacks.CategoryHomology.HomologicalDeltaFunctor.ofDeltaFunctorTwoSub`: the homological
  δ-functor `Tᵢ = E²⁻ⁱ`.

## Main results

* `Stacks.CategoryHomology.HomologicalDeltaFunctor.coeffaceable_ofDeltaFunctorTwoSub`: `T` is
  coeffaceable as soon as every object is the target of an epimorphism killed by `E¹`, and of
  one killed by `E⁰`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category ZeroObject

universe v v' u u'

namespace Stacks.CategoryHomology.HomologicalDeltaFunctor

section Reindex

variable {A : Type u} [Category.{v} A] [Abelian A] {B : Type u'} [Category.{v'} B] [Abelian B]
  (E : DeltaFunctor A B)

/-- The functors `Tᵢ = E²⁻ⁱ` for `i ≤ 2`, and `0` above. -/
def twoSubFunctor : ℕ → A ⥤ B
  | 0 => E.functor 2
  | 1 => E.functor 1
  | 2 => E.functor 0
  | _ + 3 => 0

/-- Each functor `Tᵢ = E²⁻ⁱ` is additive. -/
instance twoSubFunctor_additive : ∀ n, (twoSubFunctor E n).Additive
  | 0 => inferInstanceAs (E.functor 2).Additive
  | 1 => inferInstanceAs (E.functor 1).Additive
  | 2 => inferInstanceAs (E.functor 0).Additive
  | _ + 3 => inferInstanceAs (0 : A ⥤ B).Additive

/-- The functors `Tᵢ`, `i ≥ 3`, vanish on every object. -/
theorem isZero_twoSubFunctor_obj (n : ℕ) (X : A) :
    IsZero ((twoSubFunctor E (n + 3)).obj X) :=
  Functor.zero_obj X

/-- The connecting maps of `Tᵢ = E²⁻ⁱ`: `δ¹` and `δ⁰` of `E`, and `0` above. -/
def twoSubδ {S : ShortComplex A} (hS : S.ShortExact) :
    ∀ n : ℕ, (twoSubFunctor E (n + 1)).obj S.X₃ ⟶ (twoSubFunctor E n).obj S.X₁
  | 0 => E.δ hS 1
  | 1 => E.δ hS 0
  | _ + 2 => 0

variable (h3 : ∀ X : A, IsZero ((E.functor 3).obj X))

include h3 in
/-- `E²` sends the epimorphism of a short exact sequence to an epimorphism when `E³ = 0`. -/
theorem epi_map_g_two {S : ShortComplex A} (hS : S.ShortExact) :
    Epi ((E.functor 2).map S.g) :=
  (E.exact_δ₁ hS 2).epi_f ((h3 S.X₁).eq_of_tgt _ _)

/-- **The homological δ-functor `Tᵢ = E²⁻ⁱ`** of a cohomological δ-functor `E` with `E³ = 0`:
`T₀ = E²`, `T₁ = E¹`, `T₂ = E⁰`, `Tᵢ = 0` for `i ≥ 3`, with the connecting maps of `E`. -/
def ofDeltaFunctorTwoSub : HomologicalDeltaFunctor A B where
  functor := twoSubFunctor E
  δ hS n := twoSubδ E hS n
  map_g_δ hS n := by
    rcases n with _ | _ | n
    · exact E.map_g_δ hS 1
    · exact E.map_g_δ hS 0
    · exact comp_zero
  δ_map_f hS n := by
    rcases n with _ | _ | n
    · exact E.δ_map_f hS 1
    · exact E.δ_map_f hS 0
    · exact zero_comp
  epi_map_g hS := epi_map_g_two E h3 hS
  exact_map {S} hS n := by
    rcases n with _ | _ | _ | n
    · exact E.exact_map hS 2
    · exact E.exact_map hS 1
    · exact E.exact_map hS 0
    · exact ShortComplex.exact_of_isZero_X₂ _ (isZero_twoSubFunctor_obj E n S.X₂)
  exact_δ₁ {S} hS n := by
    rcases n with _ | _ | n
    · exact E.exact_δ₁ hS 1
    · exact E.exact_δ₁ hS 0
    · exact ShortComplex.exact_of_isZero_X₂ _ (isZero_twoSubFunctor_obj E n S.X₃)
  exact_δ₂ {S} hS n := by
    rcases n with _ | _ | _ | n
    · exact E.exact_δ₂ hS 1
    · exact E.exact_δ₂ hS 0
    · have := E.mono_map_f hS
      exact (ShortComplex.exact_iff_mono _ rfl).2 (inferInstanceAs (Mono ((E.functor 0).map S.f)))
    · exact ShortComplex.exact_of_isZero_X₂ _ (isZero_twoSubFunctor_obj E n S.X₁)
  δ_naturality {S T} hS hT φ n := by
    rcases n with _ | _ | _ | n
    · exact E.δ_naturality hS hT φ 1
    · exact E.δ_naturality hS hT φ 0
    · exact (comp_zero).trans zero_comp.symm
    · exact (isZero_twoSubFunctor_obj E n T.X₁).eq_of_tgt _ _

/-- The functor `T₀` is `E²`. -/
@[simp]
lemma ofDeltaFunctorTwoSub_functor_zero : (ofDeltaFunctorTwoSub E h3).functor 0 = E.functor 2 :=
  rfl

/-- The functor `T₁` is `E¹`. -/
@[simp]
lemma ofDeltaFunctorTwoSub_functor_one : (ofDeltaFunctorTwoSub E h3).functor 1 = E.functor 1 :=
  rfl

/-- The functor `T₂` is `E⁰`. -/
@[simp]
lemma ofDeltaFunctorTwoSub_functor_two : (ofDeltaFunctorTwoSub E h3).functor 2 = E.functor 0 :=
  rfl

/-- The connecting map `T₁(X₃) ⟶ T₀(X₁)` is `δ¹` of `E`. -/
lemma ofDeltaFunctorTwoSub_δ_zero {S : ShortComplex A} (hS : S.ShortExact) :
    (ofDeltaFunctorTwoSub E h3).δ hS 0 = E.δ hS 1 :=
  rfl

/-- The connecting map `T₂(X₃) ⟶ T₁(X₁)` is `δ⁰` of `E`. -/
lemma ofDeltaFunctorTwoSub_δ_one {S : ShortComplex A} (hS : S.ShortExact) :
    (ofDeltaFunctorTwoSub E h3).δ hS 1 = E.δ hS 0 :=
  rfl

/-- **Coeffaceability of `Tᵢ = E²⁻ⁱ`.** It suffices that every object be the target of an
epimorphism killed by `E¹` and of one killed by `E⁰`; the functors `Tᵢ`, `i ≥ 3`, vanish. -/
theorem coeffaceable_ofDeltaFunctorTwoSub
    (h1 : ∀ X : A, ∃ (P : A) (π : P ⟶ X), Epi π ∧ (E.functor 1).map π = 0)
    (h0 : ∀ X : A, ∃ (P : A) (π : P ⟶ X), Epi π ∧ (E.functor 0).map π = 0) :
    (ofDeltaFunctorTwoSub E h3).Coeffaceable where
  nonempty X n := by
    rcases n with _ | _ | n
    · obtain ⟨P, π, hπ, h⟩ := h1 X
      exact ⟨{ P := P, π := π, epi := hπ, map_π := h }⟩
    · obtain ⟨P, π, hπ, h⟩ := h0 X
      exact ⟨{ P := P, π := π, epi := hπ, map_π := h }⟩
    · exact ⟨{ P := X, π := 𝟙 X, map_π := (isZero_twoSubFunctor_obj E n X).eq_of_src _ _ }⟩

variable {E} in
/-- The components of a morphism of cohomological δ-functors, reindexed: `ηᵢ = η²⁻ⁱ`. -/
def twoSubFunctorMap {E' : DeltaFunctor A B} (η : E ⟶ E') :
    ∀ n : ℕ, twoSubFunctor E n ⟶ twoSubFunctor E' n
  | 0 => η.app 2
  | 1 => η.app 1
  | 2 => η.app 0
  | _ + 3 => 0

variable {E} in
/-- **A morphism of cohomological δ-functors induces one of the reindexed homological
δ-functors** `Tᵢ = E²⁻ⁱ`. -/
def ofDeltaFunctorTwoSubMap {E' : DeltaFunctor A B} (η : E ⟶ E')
    (h3' : ∀ X : A, IsZero ((E'.functor 3).obj X)) :
    ofDeltaFunctorTwoSub E h3 ⟶ ofDeltaFunctorTwoSub E' h3' where
  app := twoSubFunctorMap η
  comm {S} hS n := by
    rcases n with _ | _ | n
    · exact (η.comm hS 1).symm
    · exact (η.comm hS 0).symm
    · exact zero_comp.trans comp_zero.symm

/-- The component in degree `0` of the induced morphism is `η²`. -/
@[simp]
lemma ofDeltaFunctorTwoSubMap_app_zero {E' : DeltaFunctor A B} (η : E ⟶ E')
    (h3' : ∀ X : A, IsZero ((E'.functor 3).obj X)) :
    (ofDeltaFunctorTwoSubMap h3 η h3').app 0 = η.app 2 :=
  rfl

/-- The component in degree `1` of the induced morphism is `η¹`. -/
@[simp]
lemma ofDeltaFunctorTwoSubMap_app_one {E' : DeltaFunctor A B} (η : E ⟶ E')
    (h3' : ∀ X : A, IsZero ((E'.functor 3).obj X)) :
    (ofDeltaFunctorTwoSubMap h3 η h3').app 1 = η.app 1 :=
  rfl

/-- The component in degree `2` of the induced morphism is `η⁰`. -/
@[simp]
lemma ofDeltaFunctorTwoSubMap_app_two {E' : DeltaFunctor A B} (η : E ⟶ E')
    (h3' : ∀ X : A, IsZero ((E'.functor 3).obj X)) :
    (ofDeltaFunctorTwoSubMap h3 η h3').app 2 = η.app 0 :=
  rfl

end Reindex

end Stacks.CategoryHomology.HomologicalDeltaFunctor
