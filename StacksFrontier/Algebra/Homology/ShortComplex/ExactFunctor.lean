module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Tactic.CrossRefAttribute
public import StacksCore.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Exactness of a functor through short exact sequences, without additivity

Let `F : C ⥤ D` be a functor between abelian categories, *not* assumed additive. Stacks,
Lemma 010N, parts (2)–(4): `F` is left exact, right exact, resp. exact, if and only if it sends
every short exact sequence `0 → A → B → C → 0` to an exact sequence `0 → F(A) → F(B) → F(C)`,
`F(A) → F(B) → F(C) → 0`, resp. `0 → F(A) → F(B) → F(C) → 0`.

Mathlib states these equivalences for an additive functor
(`CategoryTheory.Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono` and its
companions); the `add_to_stacks 010N` registrations of parts (2)–(4) in
`StacksCore/Algebra/Homology/ShortComplex/ExactFunctor.lean` point to those Mathlib lemmas and so
assume `[F.Additive]`. The theorems here state parts (2)–(4) without the additivity hypothesis:
additivity is proved instead of assumed. As `F` need not preserve zero
morphisms, `S.map F` is not available, and "the image of `S` is exact" is spelled with the short
complex `ShortComplex.mk (F.map S.f) (F.map S.g) w`, where `w : F.map S.f ≫ F.map S.g = 0` is
part of the conclusion.

## Main results

* `CategoryTheory.Functor.additive_of_forall_shortExact_exists_exact`: a functor sending every
  short exact sequence to a sequence exact in the middle is additive.
* `CategoryTheory.Functor.preservesFiniteLimits_iff_forall_shortExact_exists_exact_and_mono`:
  Stacks 010N (2).
* `CategoryTheory.Functor.preservesFiniteColimits_iff_forall_shortExact_exists_exact_and_epi`:
  Stacks 010N (3).
* `CategoryTheory.Functor.exact_iff_forall_shortExact_exists_shortExact`: Stacks 010N (4).

## Implementation notes

Zero morphisms are preserved because the image of the short exact sequence
`X --𝟙--> X --> 0` is a complex, which forces `F.map (0 : X ⟶ 0) = 0`, and with `X = 0` that
`F.obj 0` is a zero object. Additivity then follows from Stacks 0DLP: the image of the split
sequence `X → X ⊞ Y → Y` is exact in the middle, which makes the comparison
`F.obj (X ⊞ Y) ⟶ F.obj X ⊞ F.obj Y` a monomorphism.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Limits ZeroObject

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

/-- A functor between abelian categories which sends every short exact sequence to a complex
preserves zero morphisms. -/
lemma preservesZeroMorphisms_of_forall_shortExact_map_comp_map_eq_zero (F : C ⥤ D)
    (h : ∀ S : ShortComplex C, S.ShortExact → F.map S.f ≫ F.map S.g = 0) :
    F.PreservesZeroMorphisms := by
  have key (X : C) : F.map (0 : X ⟶ 0) = 0 := by
    have hS : (ShortComplex.mk (𝟙 X) (0 : X ⟶ 0) comp_zero).ShortExact :=
      { exact := (ShortComplex.exact_iff_epi _ rfl).2 (inferInstanceAs (Epi (𝟙 X)))
        mono_f := inferInstanceAs (Mono (𝟙 X))
        epi_g := epi_of_target_iso_zero _ (Iso.refl _) }
    simpa using h _ hS
  refine preservesZeroMorphisms_of_map_zero_object (IsZero.isoZero ?_)
  rw [IsZero.iff_id_eq_zero, ← F.map_id, id_zero]
  exact key 0

/-- A functor between abelian categories which sends every short exact sequence
`0 → A → B → C → 0` to a sequence `F(A) → F(B) → F(C)` which is exact (in particular a complex)
is additive. -/
lemma additive_of_forall_shortExact_exists_exact (F : C ⥤ D)
    (h : ∀ S : ShortComplex C, S.ShortExact →
      ∃ w : F.map S.f ≫ F.map S.g = 0, (ShortComplex.mk _ _ w).Exact) :
    F.Additive := by
  have : F.PreservesZeroMorphisms :=
    preservesZeroMorphisms_of_forall_shortExact_map_comp_map_eq_zero F fun S hS ↦
      (h S hS).fst
  refine _root_.Functor.additive_of_mono_biprodComparison F fun X Y ↦ ?_
  obtain ⟨w, hw⟩ := h _ (ShortComplex.Splitting.ofHasBinaryBiproduct X Y).shortExact
  rw [Preadditive.mono_iff_cancel_zero]
  intro T u hu
  have h₁ : u ≫ F.map biprod.fst = 0 := by simpa using hu =≫ biprod.fst
  have h₂ : u ≫ F.map biprod.snd = 0 := by simpa using hu =≫ biprod.snd
  have : Mono (F.map (biprod.inl : X ⟶ X ⊞ Y)) := inferInstance
  have hl : hw.lift u h₂ ≫ F.map biprod.inl = u := hw.lift_f u h₂
  have hl' := hl =≫ F.map biprod.fst
  rw [Category.assoc, ← F.map_comp, biprod.inl_fst, F.map_id, Category.comp_id, h₁] at hl'
  rw [← hl, hl', zero_comp]

/-- **Stacks 010N (2)**, for an arbitrary functor: a functor `F` between abelian categories is
left exact if and only if for every short exact sequence `0 → A → B → C → 0` the sequence
`0 → F(A) → F(B) → F(C)` is exact. `F` is not assumed additive. -/
@[stacks 010N "part 2, for an arbitrary (not necessarily additive) functor"]
theorem preservesFiniteLimits_iff_forall_shortExact_exists_exact_and_mono (F : C ⥤ D) :
    PreservesFiniteLimits F ↔ ∀ S : ShortComplex C, S.ShortExact →
      ∃ w : F.map S.f ≫ F.map S.g = 0, (ShortComplex.mk _ _ w).Exact ∧ Mono (F.map S.f) := by
  constructor
  · intro hF S hS
    have : F.Additive := leftExactFunctor_le_additiveFunctor C D F hF
    exact ⟨(S.map F).zero, (preservesFiniteLimits_iff_forall_exact_map_and_mono F).1 hF S hS⟩
  · intro h
    have : F.Additive := additive_of_forall_shortExact_exists_exact F fun S hS ↦
      ⟨(h S hS).fst, (h S hS).snd.1⟩
    exact (preservesFiniteLimits_iff_forall_exact_map_and_mono F).2 fun S hS ↦ (h S hS).snd

/-- **Stacks 010N (3)**, for an arbitrary functor: a functor `F` between abelian categories is
right exact if and only if for every short exact sequence `0 → A → B → C → 0` the sequence
`F(A) → F(B) → F(C) → 0` is exact. `F` is not assumed additive. -/
@[stacks 010N "part 3, for an arbitrary (not necessarily additive) functor"]
theorem preservesFiniteColimits_iff_forall_shortExact_exists_exact_and_epi (F : C ⥤ D) :
    PreservesFiniteColimits F ↔ ∀ S : ShortComplex C, S.ShortExact →
      ∃ w : F.map S.f ≫ F.map S.g = 0, (ShortComplex.mk _ _ w).Exact ∧ Epi (F.map S.g) := by
  constructor
  · intro hF S hS
    have : F.Additive := rightExactFunctor_le_additiveFunctor C D F hF
    exact ⟨(S.map F).zero, (preservesFiniteColimits_iff_forall_exact_map_and_epi F).1 hF S hS⟩
  · intro h
    have : F.Additive := additive_of_forall_shortExact_exists_exact F fun S hS ↦
      ⟨(h S hS).fst, (h S hS).snd.1⟩
    exact (preservesFiniteColimits_iff_forall_exact_map_and_epi F).2 fun S hS ↦ (h S hS).snd

/-- **Stacks 010N (4)**, for an arbitrary functor: a functor `F` between abelian categories is
exact (preserves finite limits and finite colimits) if and only if for every short exact sequence
`0 → A → B → C → 0` the sequence `0 → F(A) → F(B) → F(C) → 0` is exact. `F` is not assumed
additive. -/
@[stacks 010N "part 4, for an arbitrary (not necessarily additive) functor"]
theorem exact_iff_forall_shortExact_exists_shortExact (F : C ⥤ D) :
    PreservesFiniteLimits F ∧ PreservesFiniteColimits F ↔ ∀ S : ShortComplex C, S.ShortExact →
      ∃ w : F.map S.f ≫ F.map S.g = 0, (ShortComplex.mk _ _ w).ShortExact := by
  constructor
  · rintro ⟨hl, hr⟩ S hS
    have : F.Additive := leftExactFunctor_le_additiveFunctor C D F hl
    have e : PreservesFiniteLimits F ∧ PreservesFiniteColimits F ↔
        ∀ S : ShortComplex C, S.ShortExact → (S.map F).ShortExact := (exact_tfae F).out 4 1
    exact ⟨(S.map F).zero, e.1 ⟨hl, hr⟩ S hS⟩
  · intro h
    have : F.Additive := additive_of_forall_shortExact_exists_exact F fun S hS ↦
      ⟨(h S hS).fst, (h S hS).snd.exact⟩
    have e : PreservesFiniteLimits F ∧ PreservesFiniteColimits F ↔
        ∀ S : ShortComplex C, S.ShortExact → (S.map F).ShortExact := (exact_tfae F).out 4 1
    exact e.2 fun S hS ↦ (h S hS).snd

end CategoryTheory.Functor
