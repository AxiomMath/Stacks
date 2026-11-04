module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject

/-!
# Internal-hom evaluation morphisms: uniqueness, and transport along an invertible object

Let `C` be a monoidal category and let `K`, `M`, `H` be objects.  Say that a morphism
`c : H ⊗ K ⟶ M` **exhibits `H` as an internal hom from `K` to `M`** when for every object `Z` the
map

`(Z ⟶ H) → (Z ⊗ K ⟶ M)`, `a ↦ a ▷ K ≫ c`

is a bijection.  This is the hypothesis shape of
`CategoryTheory.MonoidalCategory.isIso_of_isInvertible_of_tensorHomBijective`, chosen so that a
consumer holding the tensor–internal-hom bijection of a particular development only has to
rewrite that bijection into it.

This file collects what such a family of bijections determines.

*Uniqueness.* Two internal homs for the same pair are canonically isomorphic, compatibly with the
two evaluation morphisms, so one evaluation morphism is invertible exactly when the other is.
This is what lets a statement about *the* evaluation morphism of a development be checked on any
other morphism with the same universal property.

*Transport along an invertible object.* If `c : H ⊗ K ⟶ M` exhibits `H` as an internal hom from
`K` to `M` and `L` is an invertible object ([Stacks, Tag 0FFN]), then

`(H ⊗ L) ⊗ K ⟶ M ⊗ L`,  `σ_H ≫ c ▷ L`

exhibits `H ⊗ L` as an internal hom from `K` to `M ⊗ L`, for any natural isomorphism
`σ : (- ⊗ L) ⊗ K ≅ (- ⊗ K) ⊗ L`.  **A braiding is what produces such a `σ`**: the required
isomorphism is `(X ⊗ L) ⊗ K ≅ (X ⊗ K) ⊗ L`, which commutes `L` past `K`, and in a bare monoidal
category there is nothing to commute them with.  (This is the one place a braiding enters;
`CategoryTheory.MonoidalCategory.isIso_of_isInvertible_of_tensorHomBijective` uses none, and its
docstring correctly says so.)  `CategoryTheory.MonoidalCategory.tensorRightComm` is that `σ` in a
braided category.

Putting the two together: for internal homs `H` from `K` to `M` and `H'` from `K` to `M'`, with
`M' ≅ M ⊗ L` and `L` invertible, the evaluation morphism at `(K, M')` is invertible exactly when
the one at `(K, M)` is.

## Main definitions

* `CategoryTheory.MonoidalCategory.tensorRightComm`: the natural isomorphism
  `(- ⊗ L) ⊗ K ≅ (- ⊗ K) ⊗ L` of a braided monoidal category.

## Main results

* `CategoryTheory.MonoidalCategory.exists_iso_whiskerRight_comp_of_tensorHomBijective`: two
  internal homs for one pair are canonically isomorphic, compatibly with the evaluations.
* `CategoryTheory.MonoidalCategory.isIso_iff_of_tensorHomBijective`: hence one evaluation
  morphism is invertible exactly when the other is.
* `CategoryTheory.MonoidalCategory.tensorHomBijective_comp_iso`: an internal hom is unchanged by
  an isomorphism of the target.
* `CategoryTheory.MonoidalCategory.tensorHomBijective_whiskerRight_of_hasInverse` and
  `…_of_isInvertible`: **the transport along an invertible object.**
* `CategoryTheory.MonoidalCategory.isIso_iff_of_tensorHomBijective_of_isInvertible`: **the
  comparison of the two evaluation morphisms at `(K, M)` and at `(K, M ⊗ L)`.**

## Implementation notes

The transport is proved without any braided coherence computation, and that is why `σ` is a
parameter rather than built from the braiding inside the proof.  Write `D` for an inverse of `L`
and `u_W : W ≅ (W ⊗ D) ⊗ L` for the unit isomorphism of the equivalence `- ⊗ L`
(`Stacks.HasInverse.tensorRightEquivalence`).  Since `- ⊗ L` is fully faithful there is a *unique*
morphism `τ : (Z ⊗ K) ⊗ D ⟶ (Z ⊗ D) ⊗ K` with

`τ ▷ L = u_{Z ⊗ K}⁻¹ ≫ (u_Z ▷ K) ≫ σ_{Z ⊗ D}`,

and it is invertible because the right-hand side is.  Defining `τ` *by* that equation — rather
than writing down a candidate built from associators and the braiding and then proving the
equation — removes the whole coherence obligation: what is left is the naturality of `σ` at a
morphism `Z ⊗ D ⟶ H`, which is free.  The resulting identity

`(u_Z ≫ f ▷ L) ▷ K ≫ σ_H ≫ c ▷ L = u_{Z ⊗ K} ≫ (τ ≫ (f ▷ K ≫ c)) ▷ L`

exhibits the map of the conclusion, precomposed with the bijection `f ↦ u_Z ≫ f ▷ L`, as a
composite of three bijections.  No naturality of `u` is used, so `u` is taken as a bare family of
isomorphisms; this also keeps the objects spelled `(W ⊗ D) ⊗ L` rather than as values of the
composite functor, which is what the `rw`s in the proof need.

## References

* [Stacks Project, Tag 0FFM](https://stacks.math.columbia.edu/tag/0FFM)
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **Two internal homs for one pair are canonically isomorphic**, compatibly with their
evaluation morphisms: the isomorphism is the morphism matched with `c₁` by the bijections of
`c₂`, and its inverse is the morphism matched with `c₂` by those of `c₁`. -/
theorem exists_iso_whiskerRight_comp_of_tensorHomBijective {K M H₁ H₂ : C}
    (c₁ : H₁ ⊗ K ⟶ M) (c₂ : H₂ ⊗ K ⟶ M)
    (h₁ : ∀ Z : C, Function.Bijective fun a : Z ⟶ H₁ => a ▷ K ≫ c₁)
    (h₂ : ∀ Z : C, Function.Bijective fun a : Z ⟶ H₂ => a ▷ K ≫ c₂) :
    ∃ e : H₁ ≅ H₂, e.hom ▷ K ≫ c₂ = c₁ := by
  obtain ⟨f, hf⟩ := (h₂ H₁).surjective c₁
  obtain ⟨g, hg⟩ := (h₁ H₂).surjective c₂
  have hf' : f ▷ K ≫ c₂ = c₁ := hf
  have hg' : g ▷ K ≫ c₁ = c₂ := hg
  refine ⟨⟨f, g, (h₁ H₁).injective ?_, (h₂ H₂).injective ?_⟩, hf'⟩
  · show (f ≫ g) ▷ K ≫ c₁ = (𝟙 H₁) ▷ K ≫ c₁
    rw [comp_whiskerRight, Category.assoc, hg', hf', id_whiskerRight, Category.id_comp]
  · show (g ≫ f) ▷ K ≫ c₂ = (𝟙 H₂) ▷ K ≫ c₂
    rw [comp_whiskerRight, Category.assoc, hf', hg', id_whiskerRight, Category.id_comp]

/-- **Invertibility of an internal-hom evaluation morphism depends only on the pair**: two
evaluation morphisms for one pair differ by whiskering an isomorphism of the internal homs. -/
theorem isIso_iff_of_tensorHomBijective {K M H₁ H₂ : C}
    (c₁ : H₁ ⊗ K ⟶ M) (c₂ : H₂ ⊗ K ⟶ M)
    (h₁ : ∀ Z : C, Function.Bijective fun a : Z ⟶ H₁ => a ▷ K ≫ c₁)
    (h₂ : ∀ Z : C, Function.Bijective fun a : Z ⟶ H₂ => a ▷ K ≫ c₂) :
    IsIso c₁ ↔ IsIso c₂ := by
  obtain ⟨e, he⟩ := exists_iso_whiskerRight_comp_of_tensorHomBijective c₁ c₂ h₁ h₂
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · rw [← he] at *
    exact IsIso.of_isIso_comp_left (e.hom ▷ K) c₂
  · rw [← he]
    infer_instance

/-- **Invertibility of a homothety depends only on the object**, not on the internal hom it is
read at.  A *homothety* of `K` at an internal hom `c : H ⊗ K ⟶ K` from `K` to itself is a
morphism `a : 𝟙_ C ⟶ H` with `a ▷ K ≫ c = (λ_ K).hom`; the bijections determine it, and two
such, read at two internal homs for the pair `(K, K)`, differ by composition with the canonical
isomorphism of the internal homs.

This is what frees a statement about *the* homothety of a development from the particular
internal hom that development constructs: it may be checked at any other object carrying an
internal-hom structure for `(K, K)`, for instance one transported along a functor. -/
theorem isIso_iff_of_whiskerRight_comp_eq_leftUnitor {K H₁ H₂ : C}
    (c₁ : H₁ ⊗ K ⟶ K) (c₂ : H₂ ⊗ K ⟶ K)
    (h₁ : ∀ Z : C, Function.Bijective fun a : Z ⟶ H₁ => a ▷ K ≫ c₁)
    (h₂ : ∀ Z : C, Function.Bijective fun a : Z ⟶ H₂ => a ▷ K ≫ c₂)
    {a₁ : 𝟙_ C ⟶ H₁} {a₂ : 𝟙_ C ⟶ H₂}
    (ha₁ : a₁ ▷ K ≫ c₁ = (λ_ K).hom) (ha₂ : a₂ ▷ K ≫ c₂ = (λ_ K).hom) :
    IsIso a₁ ↔ IsIso a₂ := by
  obtain ⟨e, he⟩ := exists_iso_whiskerRight_comp_of_tensorHomBijective c₁ c₂ h₁ h₂
  have hcomp : a₁ ≫ e.hom = a₂ := by
    refine (h₂ (𝟙_ C)).injective ?_
    show (a₁ ≫ e.hom) ▷ K ≫ c₂ = a₂ ▷ K ≫ c₂
    rw [comp_whiskerRight, Category.assoc, he, ha₁, ha₂]
  refine ⟨fun _ => ?_, fun h => ?_⟩
  · rw [← hcomp]; infer_instance
  · rw [← hcomp] at h
    exact IsIso.of_isIso_comp_right a₁ e.hom

/-- **A homothety of `K` is invertible exactly when the unit is an internal hom from `K` to `K`
through the left unitor.**  Indeed `𝟙_ C` always carries the candidate homothety `𝟙 (𝟙_ C)`, so
`CategoryTheory.MonoidalCategory.isIso_iff_of_whiskerRight_comp_eq_leftUnitor` compares the given
homothety with an identity.

This is the criterion at which a statement "the homothety of `K` is invertible" becomes a
statement about morphism groups: it asks that `(Z ⟶ 𝟙_ C) → (Z ⊗ K ⟶ K)`, `b ↦ b ▷ K ≫ λ_`, be
bijective for every `Z`. -/
theorem isIso_iff_tensorHomBijective_tensorUnit {K H : C} (c : H ⊗ K ⟶ K)
    (hc : ∀ Z : C, Function.Bijective fun a : Z ⟶ H => a ▷ K ≫ c)
    {a : 𝟙_ C ⟶ H} (ha : a ▷ K ≫ c = (λ_ K).hom) :
    IsIso a ↔ ∀ Z : C, Function.Bijective fun b : Z ⟶ 𝟙_ C => b ▷ K ≫ (λ_ K).hom := by
  have hunit : (𝟙 (𝟙_ C)) ▷ K ≫ (λ_ K).hom = (λ_ K).hom := by
    rw [id_whiskerRight, Category.id_comp]
  refine ⟨fun h Z => ?_, fun h => ?_⟩
  · have hfac : (fun b : Z ⟶ 𝟙_ C => b ▷ K ≫ (λ_ K).hom) =
        (fun x : Z ⟶ H => x ▷ K ≫ c) ∘ (fun b : Z ⟶ 𝟙_ C => b ≫ a) := by
      funext b
      simp only [Function.comp_apply, comp_whiskerRight, Category.assoc, ha]
    rw [hfac]
    refine (hc Z).comp ⟨fun b₁ b₂ hb => ?_, fun x => ⟨x ≫ inv a, by simp⟩⟩
    simpa using congrArg (fun g : Z ⟶ H => g ≫ inv a) hb
  · rw [isIso_iff_of_whiskerRight_comp_eq_leftUnitor c (λ_ K).hom hc h ha hunit]
    infer_instance

/-- An internal hom is unchanged by an isomorphism of the target. -/
theorem tensorHomBijective_comp_iso {K M M' H : C} (c : H ⊗ K ⟶ M) (u : M ≅ M')
    (hc : ∀ Z : C, Function.Bijective fun a : Z ⟶ H => a ▷ K ≫ c) (Z : C) :
    Function.Bijective fun a : Z ⟶ H => a ▷ K ≫ (c ≫ u.hom) := by
  have he : (fun a : Z ⟶ H => a ▷ K ≫ (c ≫ u.hom)) =
      (fun g : Z ⊗ K ⟶ M => g ≫ u.hom) ∘ (fun a : Z ⟶ H => a ▷ K ≫ c) := by
    funext a; simp
  rw [he]
  exact Function.Bijective.comp ⟨fun g₁ g₂ hg => by
    simpa using congrArg (fun g : Z ⊗ K ⟶ M' => g ≫ u.inv) hg,
    fun g => ⟨g ≫ u.inv, by simp⟩⟩ (hc Z)

/-- **Transport of an internal hom along an invertible object.**  If `c : H ⊗ K ⟶ M` exhibits `H`
as an internal hom from `K` to `M` and `L` has a tensor inverse, then `σ_H ≫ c ▷ L` exhibits
`H ⊗ L` as an internal hom from `K` to `M ⊗ L`, for any natural isomorphism
`σ : (- ⊗ L) ⊗ K ≅ (- ⊗ K) ⊗ L`.

See the implementation notes of this file: the comparison `τ` is *defined* by the equation it has
to satisfy, using that `- ⊗ L` is fully faithful, so no coherence identity is proved here. -/
theorem tensorHomBijective_whiskerRight_of_hasInverse {K M H : C} (c : H ⊗ K ⟶ M)
    (hc : ∀ Z : C, Function.Bijective fun a : Z ⟶ H => a ▷ K ≫ c)
    {L : C} (h : HasInverse L)
    (σ : tensorRight L ⋙ tensorRight K ≅ tensorRight K ⋙ tensorRight L) (Z : C) :
    Function.Bijective fun a : Z ⟶ H ⊗ L => a ▷ K ≫ σ.hom.app H ≫ c ▷ L := by
  have : (tensorRight L).IsEquivalence := h.tensorRightEquivalence.isEquivalence_functor
  have U : ∀ W : C, W ≅ (W ⊗ h.inv) ⊗ L := fun W =>
    h.tensorRightEquivalence.symm.unitIso.app W
  have hbij : ∀ (W Y : C),
      Function.Bijective (fun f : W ⊗ h.inv ⟶ Y => (U W).hom ≫ f ▷ L) := by
    intro W Y
    have he : (fun f : W ⊗ h.inv ⟶ Y => (U W).hom ≫ f ▷ L) =
        (fun g : (W ⊗ h.inv) ⊗ L ⟶ Y ⊗ L => (U W).hom ≫ g) ∘
          (fun f : W ⊗ h.inv ⟶ Y => (tensorRight L).map f) := rfl
    rw [he]
    refine Function.Bijective.comp ?_ ⟨(tensorRight L).map_injective,
      (tensorRight L).map_surjective⟩
    exact ⟨fun g₁ g₂ hg => by
        simpa using congrArg (fun g : W ⟶ Y ⊗ L => (U W).inv ≫ g) hg,
      fun g => ⟨(U W).inv ≫ g, by simp⟩⟩
  set τ : (Z ⊗ K) ⊗ h.inv ⟶ (Z ⊗ h.inv) ⊗ K :=
    (tensorRight L).preimage ((U (Z ⊗ K)).inv ≫ ((U Z).hom ▷ K) ≫
      σ.hom.app (Z ⊗ h.inv)) with hτ
  have hτmap : τ ▷ L =
      (U (Z ⊗ K)).inv ≫ ((U Z).hom ▷ K) ≫ σ.hom.app (Z ⊗ h.inv) :=
    (tensorRight L).map_preimage _
  have : IsIso ((tensorRight L).map τ) := by
    have hm : (tensorRight L).map τ =
        (U (Z ⊗ K)).inv ≫ ((U Z).hom ▷ K) ≫ σ.hom.app (Z ⊗ h.inv) :=
      (tensorRight L).map_preimage _
    rw [hm]; infer_instance
  have : IsIso τ := isIso_of_reflects_iso τ (tensorRight L)
  have key : (fun a : Z ⟶ H ⊗ L => a ▷ K ≫ σ.hom.app H ≫ c ▷ L) ∘
        (fun f : Z ⊗ h.inv ⟶ H => (U Z).hom ≫ f ▷ L) =
      (fun g : (Z ⊗ K) ⊗ h.inv ⟶ M => (U (Z ⊗ K)).hom ≫ g ▷ L) ∘
        (fun g : (Z ⊗ h.inv) ⊗ K ⟶ M => τ ≫ g) ∘
          (fun f : Z ⊗ h.inv ⟶ H => f ▷ K ≫ c) := by
    funext f
    have hnat : (f ▷ L) ▷ K ≫ σ.hom.app H = σ.hom.app (Z ⊗ h.inv) ≫ (f ▷ K) ▷ L :=
      σ.hom.naturality f
    simp only [Function.comp_apply, comp_whiskerRight, Category.assoc, hτmap,
      Iso.hom_inv_id_assoc]
    rw [reassoc_of% hnat]
  have hcomp : Function.Bijective
      ((fun a : Z ⟶ H ⊗ L => a ▷ K ≫ σ.hom.app H ≫ c ▷ L) ∘
        (fun f : Z ⊗ h.inv ⟶ H => (U Z).hom ≫ f ▷ L)) := by
    rw [key]
    refine (hbij (Z ⊗ K) M).comp (Function.Bijective.comp ?_ (hc (Z ⊗ h.inv)))
    exact ⟨fun g₁ g₂ hg => by simpa using congrArg (fun g => inv τ ≫ g) hg,
      fun g => ⟨inv τ ≫ g, by simp⟩⟩
  exact (Function.Bijective.of_comp_iff _ (hbij Z H)).mp hcomp

section Braided

variable [BraidedCategory C]

/-- The natural isomorphism `(- ⊗ L) ⊗ K ≅ (- ⊗ K) ⊗ L` of a braided monoidal category: commute
`L` past `K` inside. -/
def tensorRightComm (L K : C) :
    tensorRight L ⋙ tensorRight K ≅ tensorRight K ⋙ tensorRight L :=
  (tensorRightTensor L K).symm ≪≫ (tensoringRight C).mapIso (β_ L K) ≪≫ tensorRightTensor K L

/-- The component of `tensorRightComm L K` at `X` is
`(X ⊗ L) ⊗ K ≅ X ⊗ (L ⊗ K) ≅ X ⊗ (K ⊗ L) ≅ (X ⊗ K) ⊗ L`. -/
@[simp]
lemma tensorRightComm_hom_app (L K X : C) :
    (tensorRightComm L K).hom.app X =
      (α_ X L K).hom ≫ (X ◁ (β_ L K).hom) ≫ (α_ X K L).inv := by
  simp [tensorRightComm]

/-- The inverse component of `tensorRightComm L K` at `X` is
`(X ⊗ K) ⊗ L ≅ X ⊗ (K ⊗ L) ≅ X ⊗ (L ⊗ K) ≅ (X ⊗ L) ⊗ K`, using the inverse braiding. -/
@[simp]
lemma tensorRightComm_inv_app (L K X : C) :
    (tensorRightComm L K).inv.app X =
      (α_ X K L).hom ≫ (X ◁ (β_ L K).inv) ≫ (α_ X L K).inv := by
  simp [tensorRightComm]

/-- **Transport of an internal hom along an invertible object**, in a braided monoidal category:
the natural isomorphism needed by
`CategoryTheory.MonoidalCategory.tensorHomBijective_whiskerRight_of_hasInverse` is the one the
braiding provides. -/
theorem tensorHomBijective_whiskerRight_of_isInvertible {K M H : C} (c : H ⊗ K ⟶ M)
    (hc : ∀ Z : C, Function.Bijective fun a : Z ⟶ H => a ▷ K ≫ c)
    {L : C} (hL : IsInvertible L) (Z : C) :
    Function.Bijective fun a : Z ⟶ H ⊗ L =>
      a ▷ K ≫ (tensorRightComm L K).hom.app H ≫ c ▷ L := by
  obtain ⟨h⟩ := hL
  exact tensorHomBijective_whiskerRight_of_hasInverse c hc h (tensorRightComm L K) Z

/-- **The evaluation morphisms at `(K, M)` and at `(K, M ⊗ L)` are invertible together**, for `L`
an invertible object of a braided monoidal category.

This is the formal monoidal step in the uniqueness of dualizing complexes: with
`M' ≅ M ⊗ L` for an invertible `L`, the internal hom from `K` to `M'` is `H ⊗ L` and its
evaluation morphism is the evaluation morphism at `(K, M)` whiskered by `L`, so one is invertible
exactly when the other is. -/
theorem isIso_iff_of_tensorHomBijective_of_isInvertible {K M M' H H' L : C}
    (c : H ⊗ K ⟶ M) (c' : H' ⊗ K ⟶ M')
    (hc : ∀ Z : C, Function.Bijective fun a : Z ⟶ H => a ▷ K ≫ c)
    (hc' : ∀ Z : C, Function.Bijective fun a : Z ⟶ H' => a ▷ K ≫ c')
    (hL : IsInvertible L) (u : M ⊗ L ≅ M') :
    IsIso c' ↔ IsIso c := by
  have : (tensorRight L).IsEquivalence := by
    obtain ⟨h⟩ := hL
    exact h.tensorRightEquivalence.isEquivalence_functor
  rw [isIso_iff_of_tensorHomBijective c'
    (((tensorRightComm L K).hom.app H ≫ c ▷ L) ≫ u.hom) hc'
    (tensorHomBijective_comp_iso _ u
      (tensorHomBijective_whiskerRight_of_isInvertible c hc hL))]
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · have : IsIso ((tensorRightComm L K).hom.app H ≫ c ▷ L) :=
      IsIso.of_isIso_comp_right _ u.hom
    have : IsIso ((tensorRight L).map c) :=
      IsIso.of_isIso_comp_left ((tensorRightComm L K).hom.app H) (c ▷ L)
    exact isIso_of_reflects_iso c (tensorRight L)
  · infer_instance

end Braided

end CategoryTheory.MonoidalCategory

end
