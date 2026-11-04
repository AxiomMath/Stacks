module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence

/-!
# Degreewise dévissage for surjectivity of the restriction map

Let `i : Y ⟶ X` be a morphism of schemes and `0 → F₁ → F₂ → F₃ → 0` a short exact sequence of
abelian sheaves on the small étale site of `X`. The restriction maps
`r_q(F) : H^q(X, F) → H^q(Y, i^{-1} F)` form a morphism between the two long exact cohomology
sequences, and the four lemma gives surjectivity of one of them from surjectivity and
injectivity of its neighbours. This file records the two instances used in the dévissage of
Stacks Project Tag 03SC part (7) when the restriction map is known a priori to be injective for
*every* sheaf:

* surjectivity of `r_q(F₂)` follows from surjectivity of `r_q(F₁)` and of `r_q(F₃)` and
  injectivity of `r_{q+1}(F₁)` — closure under extensions in a single degree;
* surjectivity of `r_q(F₁)` follows from surjectivity of `r_q(F₂)`, injectivity of `r_q(F₃)`
  and, when `q = m + 1`, surjectivity of `r_m(F₃)` — passage to a subsheaf, at the cost of the
  quotient in the *previous* degree. This is what allows an ascending induction on the degree.

## Main results

* `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_X₂_of_shortExact_of_injective`
* `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_X₁_of_shortExact_of_X₃`

Both hold for an arbitrary morphism of schemes. No tag is attached.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}} (i : Y ⟶ X)
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- If two classes agree after composing with `φ`, their difference is killed by `φ`. -/
private theorem sub_comp_mk₀_eq_zero {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]
    {Z A B : C} (φ : A ⟶ B) {q : ℕ} (a b : Ext Z A q)
    (h : a.comp (Ext.mk₀ φ) (add_zero q) = b.comp (Ext.mk₀ φ) (add_zero q)) :
    (b - a).comp (Ext.mk₀ φ) (add_zero q) = 0 := by
  rw [sub_eq_add_neg, Ext.add_comp, Ext.neg_comp, h, add_neg_cancel]

/-- **Closure under extensions in one degree.** For a short exact sequence
`0 → F₁ → F₂ → F₃ → 0`, if restriction along `i` is surjective in degree `q` for `F₁` and `F₃`
and injective in degree `q + 1` for `F₁`, then it is surjective in degree `q` for `F₂`. -/
theorem surjective_etaleCohomologyRestrictionMap_X₂_of_shortExact_of_injective
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (hS : S.ShortExact) (q : ℕ)
    (h₁ : Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₁ q))
    (h₃ : Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₃ q))
    (h₁' : Function.Injective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₁ (q + 1))) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₂ q) := by
  have hS' := hS.map_of_exact (etaleAbelianInverseImage.{u, v} i)
  intro y
  obtain ⟨x₃, hx₃⟩ := h₃ (y.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} i).map S.g))
    (add_zero q))
  have hδ : x₃.comp hS.extClass rfl = 0 := by
    apply h₁'
    have h0 := hS'.comp_extClass
    simp only [ShortComplex.map_g] at h0
    rw [etaleCohomologyRestrictionMap_comp_extClass.{u, v, w} i hS q (q + 1) rfl, hx₃,
      map_zero, Ext.comp_assoc_of_second_deg_zero, h0, Ext.comp_zero]
  obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ _ hS x₃ rfl hδ
  have hmiddle : (etaleCohomologyRestrictionMap.{u, v, w} i S.X₂ q x₂).comp
      (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} i).map S.g)) (add_zero q) =
      y.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} i).map S.g)) (add_zero q) := by
    rw [← etaleCohomologyRestrictionMap_comp_mk₀.{u, v, w} i S.g q x₂, hx₂, hx₃]
  obtain ⟨y₁, hy₁⟩ := Ext.covariant_sequence_exact₂ _ hS' _
    (sub_comp_mk₀_eq_zero _ _ _ hmiddle)
  have hy₁' : y₁.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} i).map S.f)) (add_zero q) =
      y - etaleCohomologyRestrictionMap.{u, v, w} i S.X₂ q x₂ := hy₁
  obtain ⟨x₁, hx₁⟩ := h₁ y₁
  refine ⟨x₂ + x₁.comp (Ext.mk₀ S.f) (add_zero q), ?_⟩
  rw [map_add, etaleCohomologyRestrictionMap_comp_mk₀.{u, v, w} i S.f q x₁, hx₁, hy₁']
  abel

/-- **Passage to a subsheaf, at the cost of the previous degree.** For a short exact sequence
`0 → F₁ → F₂ → F₃ → 0`, if restriction along `i` is surjective in degree `q` for `F₂`, injective
in degree `q` for `F₃`, and — when `q = m + 1` — surjective in degree `m` for `F₃`, then it is
surjective in degree `q` for `F₁`. -/
theorem surjective_etaleCohomologyRestrictionMap_X₁_of_shortExact_of_X₃
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (hS : S.ShortExact) (q : ℕ)
    (h₂ : Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₂ q))
    (h₃ : Function.Injective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₃ q))
    (h₃' : ∀ m, q = m + 1 →
      Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₃ m)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i S.X₁ q) := by
  have hS' := hS.map_of_exact (etaleAbelianInverseImage.{u, v} i)
  have : Mono ((etaleAbelianInverseImage.{u, v} i).map S.f) := hS'.mono_f
  intro y
  obtain ⟨x₂, hx₂⟩ := h₂ (y.comp (Ext.mk₀ ((etaleAbelianInverseImage.{u, v} i).map S.f))
    (add_zero q))
  have hg : x₂.comp (Ext.mk₀ S.g) (add_zero q) = 0 := by
    apply h₃
    rw [etaleCohomologyRestrictionMap_comp_mk₀.{u, v, w} i S.g q x₂, hx₂, map_zero,
      Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, ← Functor.map_comp, S.zero,
      Functor.map_zero, Ext.mk₀_zero, Ext.comp_zero]
  obtain ⟨x₁, hx₁⟩ := Ext.covariant_sequence_exact₂ _ hS x₂ hg
  have hdiff := sub_comp_mk₀_eq_zero ((etaleAbelianInverseImage.{u, v} i).map S.f)
    (etaleCohomologyRestrictionMap.{u, v, w} i S.X₁ q x₁) y (by
      rw [← etaleCohomologyRestrictionMap_comp_mk₀.{u, v, w} i S.f q x₁, hx₁, hx₂])
  obtain _ | m := q
  · refine ⟨x₁, (sub_eq_zero.mp ?_).symm⟩
    exact Ext.postcomp_mk₀_injective_of_mono _ _ (hdiff.trans (map_zero _).symm)
  · obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ _ hS' _ hdiff rfl
    obtain ⟨x₃, hx₃⟩ := h₃' m rfl z
    refine ⟨x₁ + x₃.comp hS.extClass rfl, ?_⟩
    rw [map_add, etaleCohomologyRestrictionMap_comp_extClass.{u, v, w} i hS m (m + 1) rfl, hx₃,
      hz]
    abel

/-- **Passage to a subsheaf along a monomorphism.** For a monomorphism `m : G ⟶ P` of abelian
sheaves, restriction along `i` is surjective in degree `q` on `G` as soon as it is surjective in
degree `q` on `P`, injective in degree `q` on the cokernel of `m`, and — when `q = n + 1` —
surjective in degree `n` on that cokernel. -/
theorem surjective_etaleCohomologyRestrictionMap_of_mono
    {G P : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (m : G ⟶ P) [Mono m]
    (q : ℕ)
    (hP : Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i P q))
    (hQ : Function.Injective (etaleCohomologyRestrictionMap.{u, v, w} i (cokernel m) q))
    (hQ' : ∀ n, q = n + 1 →
      Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i (cokernel m) n)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, v, w} i G q) :=
  surjective_etaleCohomologyRestrictionMap_X₁_of_shortExact_of_X₃.{u, v, w} i
    (S := ShortComplex.mk m (cokernel.π m) (cokernel.condition m))
    { exact := ShortComplex.exact_cokernel m } q hP hQ hQ'

omit [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] in
/-- The cokernel of a morphism into a sheaf killed by `n` is killed by `n`. -/
theorem nsmul_id_cokernel_eq_zero_of_nsmul_id
    {G P : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (m : G ⟶ P) {n : ℕ}
    (hP : n • 𝟙 P = 0) : n • 𝟙 (cokernel m) = 0 := by
  apply (cancel_epi (cokernel.π m)).1
  rw [Preadditive.comp_nsmul, Category.comp_id, comp_zero, ← Category.id_comp (cokernel.π m),
    ← Preadditive.nsmul_comp, hP, zero_comp]

end Stacks.EtaleCohomology

end
