module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.ClosedCoverExactSequence
import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport

/-!
# The exact sequence of Chow groups of a cover by two closed immersions

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `j₁ : X₁ ⟶ X`,
`j₂ : X₂ ⟶ X` be closed immersions of schemes locally of finite type over `S` whose images cover
`X`. Stacks 0F94 says that for every `k` the sequence

  `A_k(X₁ ×_X X₂) → A_k(X₁) ⊕ A_k(X₂) → A_k(X) → 0`

is exact. `Stacks.Chow.exact_intersectionToSummandsChow_summandsToUnionChow` and
`Stacks.Chow.surjective_summandsToUnionChow`
state this for the closed subschemes cut out by two ideal sheaves; this file deduces the form for
two arbitrary closed immersions.

## Main results

* `Stacks.Chow.surjective_chowPushforwardOfIsClosedImmersion_coprod`,
  `Stacks.Chow.exact_chowPushforwardOfIsClosedImmersion_prod_coprod` — Stacks 0F94 for two
  arbitrary closed immersions `X₁ ⟶ X` and `X₂ ⟶ X` whose images cover `X`, the intersection
  being the fibre product `X₁ ×_X X₂`.

## Implementation notes

The form of Stacks 0F94 for two arbitrary closed immersions `j₁ : X₁ ⟶ X` and `j₂ : X₂ ⟶ X`
is deduced from the form for ideal sheaves, applied to their kernels `I` and `J`. Each `j_i`
factors as an isomorphism onto the closed subscheme cut out by its kernel followed by the
inclusion of that subscheme, so the summands correspond. The intersection `X₁ ×_X X₂` receives a
closed immersion from the subscheme cut out by `I ⊔ J`, through which the exactness statement
for ideal sheaves is pushed; this closed immersion is in fact an isomorphism, but that is not
needed.

## References

* [Stacks Project, Tag 0F94](https://stacks.math.columbia.edu/tag/0F94)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

open Scheme.IdealSheafData (inclusion inclusion_subschemeι inclusion_subschemeι_assoc)

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u})

variable {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

variable (I J : X.IdealSheafData) (k : ℤ)

/-! ### Covers by two arbitrary closed immersions -/

section ClosedImmersions

open CategoryTheory.Limits

variable {A B D : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
  [LocallyOfFiniteType sB] (sD : D ⟶ C.S) [LocallyOfFiniteType sD]

/-- **Stacks 02R5, 0GU8.** Pushforward along closed immersions is functorial, read on an element
and for a composite presented by an equality. -/
theorem chowPushforwardOfIsClosedImmersion_comp_apply (f : A ⟶ B) [IsClosedImmersion f]
    (g : B ⟶ D) [IsClosedImmersion g] (h : A ⟶ D) [IsClosedImmersion h] (hfg : f ≫ g = h)
    (hf : f ≫ sB = sA) (hg : g ≫ sD = sB) (hh : h ≫ sD = sA) (k : ℤ) (α : chowGroup C sA k) :
    chowPushforwardOfIsClosedImmersion C sB sD g hg k
        (chowPushforwardOfIsClosedImmersion C sA sB f hf k α) =
      chowPushforwardOfIsClosedImmersion C sA sD h hh k α := by
  subst hfg
  exact DFunLike.congr_fun (chowPushforwardOfIsClosedImmersion_comp C sA sB sD f g hf hg k) α

/-- Pushforward along a closed immersion which is an identity is the identity. -/
theorem chowPushforwardOfIsClosedImmersion_eq_self (f : A ⟶ A) [IsClosedImmersion f]
    (hf : f = 𝟙 A) (hf' : f ≫ sA = sA) (k : ℤ) (α : chowGroup C sA k) :
    chowPushforwardOfIsClosedImmersion C sA sA f hf' k α = α := by
  subst hf
  exact DFunLike.congr_fun (properChowPushforward_id C sA k _) α

variable {X₁ X₂ : Scheme.{u}} (j₁ : X₁ ⟶ X) (j₂ : X₂ ⟶ X) [IsClosedImmersion j₁]
  [IsClosedImmersion j₂]

/-- Two closed immersions whose images cover `X` have kernels whose supports cover `X`. -/
theorem support_ker_sup_eq_top_of_range_union_eq_univ
    (hcover : Set.range j₁ ∪ Set.range j₂ = Set.univ) :
    j₁.ker.support ⊔ j₂.ker.support = ⊤ := by
  refine SetLike.coe_injective ?_
  rw [Closeds.coe_sup, Scheme.Hom.support_ker, Scheme.Hom.support_ker,
    j₁.isClosedEmbedding.isClosed_range.closure_eq,
    j₂.isClosedEmbedding.isClosed_range.closure_eq, hcover, Closeds.coe_top]

/-- The inverse of the isomorphism of a closed immersion onto the closed subscheme cut out by its
kernel, followed by the closed immersion, is the inclusion of that subscheme. -/
theorem inv_toImage_comp (j : X₁ ⟶ X) [IsClosedImmersion j] :
    inv j.toImage ≫ j = j.ker.subschemeι := by
  rw [IsIso.inv_comp_eq, Scheme.Hom.toImage_imageι]

variable (sX₁ : X₁ ⟶ C.S) [LocallyOfFiniteType sX₁] (sX₂ : X₂ ⟶ C.S) [LocallyOfFiniteType sX₂]
  (hj₁ : j₁ ≫ sX = sX₁) (hj₂ : j₂ ≫ sX = sX₂) (k : ℤ)

omit [LocallyOfFiniteType sX] [IsClosedImmersion j₁] [LocallyOfFiniteType sX₁] in
include hj₁ in
/-- The isomorphism of a closed immersion onto the closed subscheme cut out by its kernel is a
morphism over the base. -/
theorem toImage_comp_subschemeι_comp_structureMorphism :
    j₁.toImage ≫ j₁.ker.subschemeι ≫ sX = sX₁ := by
  rw [Scheme.Hom.toImage_imageι_assoc, hj₁]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sX₁] in
include hj₁ in
/-- The inverse of the isomorphism of a closed immersion onto the closed subscheme cut out by its
kernel is a morphism over the base. -/
theorem inv_toImage_comp_structureMorphism_eq_subschemeι :
    inv j₁.toImage ≫ sX₁ = j₁.ker.subschemeι ≫ sX := by
  rw [← hj₁, ← Category.assoc, inv_toImage_comp]

omit [LocallyOfFiniteType sX] [IsClosedImmersion j₁] [IsClosedImmersion j₂]
  [LocallyOfFiniteType sX₁] [LocallyOfFiniteType sX₂] in
include hj₁ hj₂ in
/-- The two structure morphisms of the fibre product `X₁ ×_X X₂` over the base agree. -/
theorem pullbackSnd_comp_structureMorphism_eq_fst :
    pullback.snd j₁ j₂ ≫ sX₂ = pullback.fst j₁ j₂ ≫ sX₁ := by
  rw [← hj₁, ← hj₂, pullback.condition_assoc]

/-- **Stacks 0F94, surjectivity, for two closed immersions.** If the images of two closed
immersions `j₁ : X₁ ⟶ X` and `j₂ : X₂ ⟶ X` cover `X`, every class of `k`-cycles on `X` is the sum
of the pushforwards of a class on `X₁` and a class on `X₂`. -/
@[stacks 0F94 "surjectivity, for two arbitrary closed immersions"]
theorem surjective_chowPushforwardOfIsClosedImmersion_coprod
    (hcover : Set.range j₁ ∪ Set.range j₂ = Set.univ) :
    Function.Surjective ((chowPushforwardOfIsClosedImmersion C sX₁ sX j₁ hj₁ k).coprod
      (chowPushforwardOfIsClosedImmersion C sX₂ sX j₂ hj₂ k)) := by
  intro α
  obtain ⟨⟨q₁, q₂⟩, hq⟩ := surjective_summandsToUnionChow C sX j₁.ker j₂.ker k
    (support_ker_sup_eq_top_of_range_union_eq_univ j₁ j₂ hcover) α
  refine ⟨(chowPushforwardOfIsClosedImmersion C _ sX₁ (inv j₁.toImage)
      (inv_toImage_comp_structureMorphism_eq_subschemeι C sX j₁ sX₁ hj₁) k q₁,
    chowPushforwardOfIsClosedImmersion C _ sX₂ (inv j₂.toImage)
      (inv_toImage_comp_structureMorphism_eq_subschemeι C sX j₂ sX₂ hj₂) k q₂), ?_⟩
  rwa [AddMonoidHom.coprod_apply,
    chowPushforwardOfIsClosedImmersion_comp_apply C _ sX₁ sX (inv j₁.toImage) j₁
      j₁.ker.subschemeι (inv_toImage_comp j₁) _ hj₁ rfl k,
    chowPushforwardOfIsClosedImmersion_comp_apply C _ sX₂ sX (inv j₂.toImage) j₂
      j₂.ker.subschemeι (inv_toImage_comp j₂) _ hj₂ rfl k]

/-- Pushing a class `c` on a subscheme `K ⊇ j.ker` forward along a closed immersion `φ` and then
`g`, where `φ ≫ g` is the inclusion followed by `inv j.toImage`, recovers a class `α` on `X₁`
as soon as the pushforward of `c` to `j.ker` is the pushforward of `α` along `j.toImage`. -/
private theorem pushforward_pushforward_eq_of_comp_inclusion_inv_toImage
    {P : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (g : P ⟶ X₁) [IsClosedImmersion g]
    (K : X.IdealSheafData) (hK : j₁.ker ≤ K) (φ : K.subscheme ⟶ P) [IsClosedImmersion φ]
    (hφg : φ ≫ g = inclusion hK ≫ inv j₁.toImage) (hφs : φ ≫ sP = K.subschemeι ≫ sX)
    (hg : g ≫ sX₁ = sP) (c : chowGroup C (K.subschemeι ≫ sX) k) (α : chowGroup C sX₁ k)
    (hc : chowPushforwardOfIsClosedImmersion C _ (j₁.ker.subschemeι ≫ sX) (inclusion hK)
        (inclusion_subschemeι_assoc hK sX) k c =
      chowPushforwardOfIsClosedImmersion C sX₁ _ j₁.toImage
        (toImage_comp_subschemeι_comp_structureMorphism C sX j₁ sX₁ hj₁) k α) :
    chowPushforwardOfIsClosedImmersion C sP sX₁ g hg k
      (chowPushforwardOfIsClosedImmersion C _ sP φ hφs k c) = α := by
  have hinv := inv_toImage_comp_structureMorphism_eq_subschemeι C sX j₁ sX₁ hj₁
  rw [chowPushforwardOfIsClosedImmersion_comp_apply C _ sP sX₁ φ g (inclusion hK ≫ inv j₁.toImage)
      hφg hφs hg (by rw [Category.assoc, hinv, inclusion_subschemeι_assoc]) k,
    ← chowPushforwardOfIsClosedImmersion_comp_apply C _ (j₁.ker.subschemeι ≫ sX) sX₁
      (inclusion hK) (inv j₁.toImage) _ rfl (inclusion_subschemeι_assoc hK sX) hinv, hc,
    chowPushforwardOfIsClosedImmersion_comp_apply C sX₁ _ sX₁ j₁.toImage (inv j₁.toImage)
      (𝟙 X₁) (IsIso.hom_inv_id _) _ _ (Category.id_comp sX₁) k]
  exact chowPushforwardOfIsClosedImmersion_eq_self C sX₁ (𝟙 X₁) rfl _ k α

/-- **Stacks 0F94, exactness in the middle, for two closed immersions.** If the images of two
closed immersions `j₁ : X₁ ⟶ X` and `j₂ : X₂ ⟶ X` cover `X`, a pair of classes of `k`-cycles on
`X₁` and `X₂` has vanishing sum of pushforwards exactly when it is the pair of pushforwards of a
class on the fibre product `X₁ ×_X X₂`, the second one negated. -/
@[stacks 0F94 "exactness in the middle, for two arbitrary closed immersions"]
theorem exact_chowPushforwardOfIsClosedImmersion_prod_coprod
    (hcover : Set.range j₁ ∪ Set.range j₂ = Set.univ) :
    Function.Exact
      ((chowPushforwardOfIsClosedImmersion C (pullback.fst j₁ j₂ ≫ sX₁) sX₁
          (pullback.fst j₁ j₂) rfl k).prod
        (-chowPushforwardOfIsClosedImmersion C (pullback.fst j₁ j₂ ≫ sX₁) sX₂
          (pullback.snd j₁ j₂)
          (pullbackSnd_comp_structureMorphism_eq_fst C sX j₁ j₂ sX₁ sX₂ hj₁ hj₂)
          k))
      ((chowPushforwardOfIsClosedImmersion C sX₁ sX j₁ hj₁ k).coprod
        (chowPushforwardOfIsClosedImmersion C sX₂ sX j₂ hj₂ k)) := by
  have hsnd := pullbackSnd_comp_structureMorphism_eq_fst C sX j₁ j₂ sX₁ sX₂ hj₁ hj₂
  intro x
  constructor
  · intro hzero
    obtain ⟨α₁, α₂⟩ := x
    set I := j₁.ker
    set J := j₂.ker
    let q₁ := chowPushforwardOfIsClosedImmersion C sX₁ (I.subschemeι ≫ sX) j₁.toImage
      (toImage_comp_subschemeι_comp_structureMorphism C sX j₁ sX₁ hj₁) k α₁
    let q₂ := chowPushforwardOfIsClosedImmersion C sX₂ (J.subschemeι ≫ sX) j₂.toImage
      (toImage_comp_subschemeι_comp_structureMorphism C sX j₂ sX₂ hj₂) k α₂
    have hq : summandsToUnionChow C sX I J k (q₁, q₂) = 0 := by
      change chowPushforwardOfIsClosedImmersion C _ sX I.subschemeι rfl k q₁ +
        chowPushforwardOfIsClosedImmersion C _ sX J.subschemeι rfl k q₂ = 0
      rwa [chowPushforwardOfIsClosedImmersion_comp_apply C sX₁ _ sX j₁.toImage I.subschemeι j₁
          (Scheme.Hom.toImage_imageι j₁) _ rfl hj₁ k,
        chowPushforwardOfIsClosedImmersion_comp_apply C sX₂ _ sX j₂.toImage J.subschemeι j₂
          (Scheme.Hom.toImage_imageι j₂) _ rfl hj₂ k]
    obtain ⟨c, hc⟩ := (exact_intersectionToSummandsChow_summandsToUnionChow C sX I J k
      (support_ker_sup_eq_top_of_range_union_eq_univ j₁ j₂ hcover) (q₁, q₂)).mp hq
    have hc₁ := congrArg Prod.fst hc
    have hc₂ := congrArg Prod.snd hc
    change chowPushforwardOfIsClosedImmersion C _ _ (inclusion (le_sup_left : I ≤ I ⊔ J)) _ k c =
      q₁ at hc₁
    change -chowPushforwardOfIsClosedImmersion C _ _ (inclusion (le_sup_right : J ≤ I ⊔ J)) _ k c =
      q₂ at hc₂
    have hφ : (inclusion (le_sup_left : I ≤ I ⊔ J) ≫ inv j₁.toImage) ≫ j₁ =
        (inclusion (le_sup_right : J ≤ I ⊔ J) ≫ inv j₂.toImage) ≫ j₂ := by
      rw [Category.assoc, Category.assoc, inv_toImage_comp, inv_toImage_comp,
        inclusion_subschemeι, inclusion_subschemeι]
    let φ := pullback.lift _ _ hφ
    have hφfst : φ ≫ pullback.fst j₁ j₂ = inclusion (le_sup_left : I ≤ I ⊔ J) ≫ inv j₁.toImage :=
      pullback.lift_fst _ _ _
    have hφsnd : φ ≫ pullback.snd j₁ j₂ =
        inclusion (le_sup_right : J ≤ I ⊔ J) ≫ inv j₂.toImage :=
      pullback.lift_snd _ _ _
    have : IsClosedImmersion (φ ≫ pullback.fst j₁ j₂ ≫ j₁) := by
      rw [← Category.assoc, hφfst, Category.assoc, inv_toImage_comp, inclusion_subschemeι]
      infer_instance
    have : IsClosedImmersion φ :=
      IsClosedImmersion.of_comp_isClosedImmersion φ (pullback.fst j₁ j₂ ≫ j₁)
    have hφs : φ ≫ pullback.fst j₁ j₂ ≫ sX₁ = (I ⊔ J).subschemeι ≫ sX := by
      rw [← Category.assoc, hφfst, Category.assoc,
        inv_toImage_comp_structureMorphism_eq_subschemeι C sX j₁ sX₁ hj₁,
        inclusion_subschemeι_assoc]
    refine ⟨chowPushforwardOfIsClosedImmersion C _ _ φ hφs k c, Prod.ext ?_ ?_⟩
    · exact pushforward_pushforward_eq_of_comp_inclusion_inv_toImage C sX j₁ sX₁ hj₁ k _
        (pullback.fst j₁ j₂) _ le_sup_left φ hφfst hφs rfl c α₁ hc₁
    · change -chowPushforwardOfIsClosedImmersion C _ sX₂ (pullback.snd j₁ j₂) hsnd k
        (chowPushforwardOfIsClosedImmersion C _ _ φ hφs k c) = α₂
      rw [← map_neg, ← map_neg]
      exact pushforward_pushforward_eq_of_comp_inclusion_inv_toImage C sX j₂ sX₂ hj₂ k _
        (pullback.snd j₁ j₂) _ le_sup_right φ hφsnd hφs hsnd (-c) α₂ (by rw [map_neg, hc₂])
  · rintro ⟨γ, rfl⟩
    change chowPushforwardOfIsClosedImmersion C sX₁ sX j₁ hj₁ k
        (chowPushforwardOfIsClosedImmersion C _ sX₁ (pullback.fst j₁ j₂) rfl k γ) +
      chowPushforwardOfIsClosedImmersion C sX₂ sX j₂ hj₂ k
        (-chowPushforwardOfIsClosedImmersion C _ sX₂ (pullback.snd j₁ j₂) hsnd k γ) = 0
    rw [map_neg, chowPushforwardOfIsClosedImmersion_comp_apply C _ sX₁ sX (pullback.fst j₁ j₂) j₁
        _ rfl rfl hj₁ (by rw [Category.assoc, hj₁]) k,
      chowPushforwardOfIsClosedImmersion_comp_apply C _ sX₂ sX (pullback.snd j₁ j₂) j₂
        (pullback.fst j₁ j₂ ≫ j₁) pullback.condition.symm hsnd hj₂
        (by rw [Category.assoc, hj₁]) k, add_neg_cancel]

end ClosedImmersions

end Stacks.Chow

end
