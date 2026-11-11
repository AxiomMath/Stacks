module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import StacksCore.CategoryTheory.Filtration.Strict
import StacksCore.Tactic.StacksAttribute

/-!
# Composition of strict morphisms of filtered objects (Stacks 05SJ)

Stacks 05SJ: let `𝒜` be an abelian category and `f : A ⟶ B`, `g : B ⟶ C` strict morphisms of
filtered objects. Then
1. in general `g ∘ f` is not strict;
2. if `g` is injective, then `g ∘ f` is strict;
3. if `f` is surjective, then `g ∘ f` is strict.

Parts (2) and (3) are `FilteredObject.IsStrict.comp_of_mono` and
`FilteredObject.IsStrict.comp_of_epi` in `StacksCore.CategoryTheory.Filtration.Strict` (with the
equivalences `isStrict_comp_iff_of_mono` and `isStrict_comp_iff_of_epi`); their `stacks 05SJ`
notes there name the part each covers, and that module's docstring records part (1) as not
formalized there.
This module formalizes part (1) and states the whole lemma.

## Main results

* `FilteredObject.exists_isStrict_not_isStrict_comp`: part (1) in any abelian category with a
  nonzero object `X`. This is the Stacks counterexample with `k` replaced by `X`:
  `B = X ⊕ X` filtered by `F^nB = B` for `n < 0`, `F⁰B = X ⊕ 0` (the kernel of the second
  projection) and `F^nB = 0` for `n > 0`; `A = X` embedded diagonally with the induced filtration
  and `C = X`, the quotient of `B` by the second summand, with the quotient filtration. Both maps
  are strict by Stacks 0124, `F⁰A = 0` and `F⁰C = C`, and the composite is the identity of `X`,
  which is not strict.
* `FilteredObject.exists_isStrict_not_isStrict_comp_moduleCat`: part (1) for vector spaces over
  a field `k`, the setting of the Stacks counterexample.
* `FilteredObject.isStrict_comp_stacks_05SJ`: all three parts together.
-/

@[expose] public section

universe u

namespace CategoryTheory

open Limits Opposite

namespace FilteredObject

variable {C : Type*} [Category* C] [Abelian C]

/-- The filtration on `X ⊞ X` of the Stacks 05SJ counterexample: `F^n = X ⊞ X` for `n < 0`,
`F⁰ = X ⊞ 0`, the kernel of the second projection, and `F^n = 0` for `n > 0`. -/
noncomputable def strictCompCounterexampleFiltration (X : C) : Filtration (X ⊞ X) ℤᵒᵖ :=
  Filtration.ofAntitone
    (fun n => if n < 0 then ⊤ else if n = 0 then kernelSubobject (biprod.snd : X ⊞ X ⟶ X) else ⊥)
    (fun a b hab => by
      dsimp only
      split_ifs <;> first | exact le_rfl | exact le_top | exact bot_le | omega)

/-- Stacks 05SJ (1) in any abelian category with a nonzero object: there are strict morphisms
`f : A ⟶ B` and `g : B ⟶ D` of `ℤ`-filtered objects whose composite is not strict. -/
theorem exists_isStrict_not_isStrict_comp {X : C} (hX : ¬ IsZero X) :
    ∃ (A B D : FilteredObject C ℤᵒᵖ) (f : A ⟶ B) (g : B ⟶ D),
      IsStrict f ∧ IsStrict g ∧ ¬ IsStrict (f ≫ g) := by
  have : Nontrivial (Subobject X) := Subobject.nontrivial_of_not_isZero hX
  let B : FilteredObject C ℤᵒᵖ := ⟨X ⊞ X, strictCompCounterexampleFiltration X⟩
  have : Mono (biprod.lift (𝟙 X) (𝟙 X)) := mono_of_mono_fac (biprod.lift_fst (𝟙 X) (𝟙 X))
  refine ⟨_, B, _, pullbackHom B (biprod.lift (𝟙 X) (𝟙 X)), pushforwardHom B biprod.fst,
    inferInstance, inferInstance, fun h => ?_⟩
  have hB : B.subobject (op 0) = kernelSubobject (biprod.snd : X ⊞ X ⟶ X) := by
    exact (Filtration.subobject_ofAntitone _ _ 0).trans (by simp)
  -- `F⁰A = Δ⁻¹(X ⊞ 0) = 0`
  have hA : (Subobject.pullback (biprod.lift (𝟙 X) (𝟙 X))).obj
      (kernelSubobject (biprod.snd : X ⊞ X ⟶ X)) = ⊥ := by
    set P := (Subobject.pullback (biprod.lift (𝟙 X) (𝟙 X))).obj
      (kernelSubobject (biprod.snd : X ⊞ X ⟶ X))
    have hP : P.Factors P.arrow := Subobject.factors_self P
    rw [Limits.pullback_factors_iff, kernelSubobject_factors_iff] at hP
    simp only [Category.assoc, biprod.lift_snd, Category.comp_id] at hP
    rw [← Subobject.mk_arrow P, Subobject.mk_eq_bot_iff_zero]
    exact hP
  -- `F⁰D = fst(X ⊞ 0) = X`
  have hD : (Subobject.exists (biprod.fst : X ⊞ X ⟶ X)).obj
      (kernelSubobject (biprod.snd : X ⊞ X ⟶ X)) = ⊤ := by
    refine top_le_iff.1 (le_trans ?_ ((Subobject.exists biprod.fst).monotone
      (le_kernelSubobject _ (Subobject.mk (biprod.inl : X ⟶ X ⊞ X))
        (by rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc, biprod.inl_snd,
          comp_zero]))))
    rw [Subobject.exists_mk_eq_imageSubobject, biprod.inl_fst, imageSubobject_mono,
      Subobject.mk_eq_top_of_isIso]
  have h0 := (isStrict_iff_exists_eq _).1 h (op 0)
  rw [pullbackObj_subobject, pushforwardObj_subobject, hB, hA, hD, inf_top_eq, comp_hom,
    pullbackHom_hom, pushforwardHom_hom, biprod.lift_fst, imageSubobject_mono,
    Subobject.mk_eq_top_of_isIso, Subobject.bot_eq_zero, Subobject.exists_mk_eq_imageSubobject,
    zero_comp, imageSubobject_zero] at h0
  exact bot_ne_top h0

/-- Stacks 05SJ (1) for vector spaces over a field `k`: there are strict morphisms of
`ℤ`-filtered `k`-vector spaces whose composite is not strict. -/
theorem exists_isStrict_not_isStrict_comp_moduleCat (k : Type u) [Field k] :
    ∃ (A B D : FilteredObject (ModuleCat.{u} k) ℤᵒᵖ) (f : A ⟶ B) (g : B ⟶ D),
      IsStrict f ∧ IsStrict g ∧ ¬ IsStrict (f ≫ g) :=
  exists_isStrict_not_isStrict_comp (X := ModuleCat.of k k)
    (fun h => not_subsingleton k (ModuleCat.isZero_of_iff_subsingleton.1 h))

/-- Stacks 05SJ. Let `𝒜` be an abelian category and let `f : A ⟶ B`, `g : B ⟶ D` be strict
morphisms of filtered objects. Then (1) in general `f ≫ g` is not strict: there are strict
morphisms of `ℤ`-filtered vector spaces over any field `k` whose composite is not strict;
(2) if `g` is a monomorphism, then `f ≫ g` is strict; (3) if `f` is an epimorphism, then
`f ≫ g` is strict. -/
@[stacks 05SJ "(1) a counterexample in `k`-vector spaces for any field `k`, and in any abelian \
category with a nonzero object (`exists_isStrict_not_isStrict_comp`); (2) `g ∘ f` is strict for \
`g` a monomorphism; (3) `g ∘ f` is strict for `f` an epimorphism"]
theorem isStrict_comp_stacks_05SJ (k : Type u) [Field k] (I : Type*) [Category* I] :
    (∃ (A B D : FilteredObject (ModuleCat.{u} k) ℤᵒᵖ) (f : A ⟶ B) (g : B ⟶ D),
      IsStrict f ∧ IsStrict g ∧ ¬ IsStrict (f ≫ g)) ∧
    (∀ {A B D : FilteredObject C I} (f : A ⟶ B) (g : B ⟶ D), IsStrict f → IsStrict g →
      Mono g.hom → IsStrict (f ≫ g)) ∧
    (∀ {A B D : FilteredObject C I} (f : A ⟶ B) (g : B ⟶ D), IsStrict f → IsStrict g →
      Epi f.hom → IsStrict (f ≫ g)) :=
  ⟨exists_isStrict_not_isStrict_comp_moduleCat k,
    fun f g _ _ _ => IsStrict.comp_of_mono f g, fun f g _ _ _ => IsStrict.comp_of_epi f g⟩

end FilteredObject

end CategoryTheory
