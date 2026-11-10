module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Module.Injective
public import Mathlib.Basic.Finite.Sum
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Finite modules against filtered colimits of modules over a finite ring

Let `R` be a ring, `F : J ⥤ Mod_R` a filtered diagram and `c` a colimit cocone of `F` which the
forgetful functor preserves. For a module `N` which is finite as a set, over a ring `R` which is
finite:

* every linear map `N ⟶ c.pt` factors through some `F(j)`;
* two linear maps `N ⟶ F(j)` which agree in the colimit agree at a later stage;
* if every `F(j)` is an injective module, so is `c.pt` (the case of a finite ring of the theorem
  of Bass and Papp).

## Main results

* `ModuleCat.FiniteFilteredColimit.exists_eq_at_stage`: finitely many pairs of elements with
  equal images in the colimit become equal at one stage.
* `ModuleCat.FiniteFilteredColimit.exists_stage`: finitely many elements of the colimit are
  images of elements of one stage.
* `ModuleCat.FiniteFilteredColimit.exists_lift`: the factorization of a linear map from a finite
  module.
* `ModuleCat.FiniteFilteredColimit.exists_map_comp_eq`: two such factorizations agree at a later
  stage.
* `ModuleCat.FiniteFilteredColimit.injective_pt`: a filtered colimit of injective modules over a
  finite ring is injective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v' v u

namespace ModuleCat.FiniteFilteredColimit

variable {R : Type u} [Ring R] {J : Type v} [Category.{v'} J] [IsFiltered J]
  (F : J ⥤ ModuleCat.{w} R) [PreservesColimit F (forget (ModuleCat.{w} R))]
  {c : Cocone F} (hc : IsColimit c)

omit [IsFiltered J] [PreservesColimit F (forget (ModuleCat.{w} R))] in
/-- For a cocone `c` over `F` and a morphism `t : k ⟶ k'`, the image of `F.map t z` under
`c.ι.app k'` is the image of `z` under `c.ι.app k`. -/
lemma cocone_map_apply (c : Cocone F) {k k' : J} (t : k ⟶ k') (z : F.obj k) :
    c.ι.app k' (F.map t z) = c.ι.app k z := by
  rw [← ConcreteCategory.comp_apply, c.w]

omit [IsFiltered J] [PreservesColimit F (forget (ModuleCat.{w} R))] in
/-- `F.map (t ≫ t')` applied to an element `z` is `F.map t'` applied to `F.map t z`. -/
lemma map_comp_apply {k k' k'' : J} (t : k ⟶ k') (t' : k' ⟶ k'') (z : F.obj k) :
    F.map (t ≫ t') z = F.map t' (F.map t z) := by
  rw [F.map_comp, ConcreteCategory.comp_apply]

include hc in
/-- **Finitely many relations hold at one stage.** If finitely many pairs `(x s, y s)` of
elements of `F(k)` have equal images in the colimit, then they become equal along a single
morphism `k ⟶ k'`. -/
theorem exists_eq_at_stage {ι : Type*} [Finite ι] {k : J} (x y : ι → F.obj k)
    (h : ∀ s, c.ι.app k (x s) = c.ι.app k (y s)) :
    ∃ (k' : J) (t : k ⟶ k'), ∀ s, F.map t (x s) = F.map t (y s) := by
  classical
  have hι := Fintype.ofFinite ι
  suffices H : ∀ S : Finset ι, ∃ (k' : J) (t : k ⟶ k'), ∀ s ∈ S, F.map t (x s) = F.map t (y s) by
    obtain ⟨k', t, ht⟩ := H Finset.univ
    exact ⟨k', t, fun s => ht s (Finset.mem_univ s)⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨k, 𝟙 k, by simp⟩
  | insert a S ha ih =>
    obtain ⟨k₁, t₁, ht₁⟩ := ih
    have e : c.ι.app k₁ (F.map t₁ (x a)) = c.ι.app k₁ (F.map t₁ (y a)) := by
      rw [cocone_map_apply F c t₁, cocone_map_apply F c t₁]
      exact h a
    obtain ⟨k₂, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq F hc _ _ e
    refine ⟨IsFiltered.coeq f g, t₁ ≫ f ≫ IsFiltered.coeqHom f g, fun s hs => ?_⟩
    obtain rfl | hs := Finset.mem_insert.mp hs
    · rw [map_comp_apply F t₁ (f ≫ IsFiltered.coeqHom f g),
        map_comp_apply F t₁ (f ≫ IsFiltered.coeqHom f g), map_comp_apply F f,
        hfg, ← map_comp_apply F g, ← IsFiltered.coeq_condition f g]
    · rw [map_comp_apply F t₁, map_comp_apply F t₁, ht₁ s hs]

include hc in
/-- **Finitely many elements of the colimit come from one stage.** -/
theorem exists_stage {ι : Type*} [Finite ι] (z : ι → c.pt) :
    ∃ (k : J) (y : ι → F.obj k), ∀ s, c.ι.app k (y s) = z s := by
  classical
  have hι := Fintype.ofFinite ι
  suffices H : ∀ S : Finset ι, ∃ (k : J) (y : ι → F.obj k), ∀ s ∈ S, c.ι.app k (y s) = z s by
    obtain ⟨k, y, hy⟩ := H Finset.univ
    exact ⟨k, y, fun s => hy s (Finset.mem_univ s)⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨IsFiltered.nonempty.some, fun _ => 0, by simp⟩
  | insert a S ha ih =>
    obtain ⟨k₁, y₁, hy₁⟩ := ih
    obtain ⟨k₀, y₀, hy₀⟩ := Concrete.isColimit_exists_rep F hc (z a)
    refine ⟨IsFiltered.max k₁ k₀, fun s => if s = a then F.map (IsFiltered.rightToMax k₁ k₀) y₀
      else F.map (IsFiltered.leftToMax k₁ k₀) (y₁ s), fun s hs => ?_⟩
    by_cases hsa : s = a
    · subst hsa
      simp only [ite_true]
      rwa [cocone_map_apply F c]
    · simp only [hsa, ite_false]
      rw [cocone_map_apply F c, hy₁ s ((Finset.mem_insert.mp hs).resolve_left hsa)]

include hc in
/-- **Linear maps from a finite module factor through a stage.** Over a finite ring `R`, every
linear map `φ : N →ₗ[R] c.pt` from a finite module `N` is the composite of some
`ψ : N →ₗ[R] F(j)` with `c.ι.app j`. -/
theorem exists_lift [Finite R] (N : Type*) [AddCommGroup N] [Module R N] [Finite N]
    (φ : N →ₗ[R] c.pt) :
    ∃ (j : J) (ψ : N →ₗ[R] F.obj j), (c.ι.app j).hom.comp ψ = φ := by
  obtain ⟨k, z, hz⟩ := exists_stage F hc (fun n : N => φ n)
  let x : (N × N) ⊕ (R × N) → F.obj k := fun t => match t with
    | .inl (a, b) => z (a + b)
    | .inr (r, a) => z (r • a)
  let y : (N × N) ⊕ (R × N) → F.obj k := fun t => match t with
    | .inl (a, b) => z a + z b
    | .inr (r, a) => r • z a
  have hxy : ∀ t : (N × N) ⊕ (R × N), c.ι.app k (x t) = c.ι.app k (y t) := by
    rintro (⟨a, b⟩ | ⟨r, a⟩) <;> simp only [x, y, map_add, map_smul, hz]
  obtain ⟨k', t, ht⟩ := exists_eq_at_stage F hc x y hxy
  refine ⟨k', { toFun := fun n => F.map t (z n)
                map_add' := fun a b => ?_
                map_smul' := fun r a => ?_ }, ?_⟩
  · simpa only [x, y, map_add] using ht (.inl (a, b))
  · simpa only [x, y, map_smul, RingHom.id_apply] using ht (.inr (r, a))
  · ext n
    exact (cocone_map_apply F c t (z n)).trans (hz n)

include hc in
/-- **Two linear maps from a finite module which agree in the colimit agree at a later
stage.** -/
theorem exists_map_comp_eq (N : Type*) [AddCommGroup N] [Module R N] [Finite N] {j : J}
    (ψ₁ ψ₂ : N →ₗ[R] F.obj j)
    (h : (c.ι.app j).hom.comp ψ₁ = (c.ι.app j).hom.comp ψ₂) :
    ∃ (j' : J) (t : j ⟶ j'), (F.map t).hom.comp ψ₁ = (F.map t).hom.comp ψ₂ := by
  obtain ⟨j', t, ht⟩ := exists_eq_at_stage F hc (fun n : N => ψ₁ n) (fun n => ψ₂ n)
    (fun n => LinearMap.congr_fun h n)
  exact ⟨j', t, LinearMap.ext ht⟩

include hc in
/-- **A filtered colimit of injective modules over a finite ring is injective** (the theorem of
Bass and Papp, for a finite ring). -/
theorem injective_pt [Finite R] [Small.{w} R] (hF : ∀ j, Module.Injective R (F.obj j)) :
    Module.Injective R c.pt := by
  refine Module.Baer.injective fun I g => ?_
  obtain ⟨j, ψ, hψ⟩ := exists_lift F hc I g
  obtain ⟨ψ', hψ'⟩ := Module.Baer.of_injective (hF j) I ψ
  refine ⟨(c.ι.app j).hom.comp ψ', fun x hx => ?_⟩
  rw [LinearMap.comp_apply, hψ' x hx, ← hψ, LinearMap.comp_apply]

end ModuleCat.FiniteFilteredColimit

end
