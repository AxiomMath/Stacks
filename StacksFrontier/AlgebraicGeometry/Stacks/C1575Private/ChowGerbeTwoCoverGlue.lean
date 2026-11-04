module

public import StacksFrontier.AlgebraicGeometry.Stacks.C1575Private.ChowGerbeCompactificationGlue
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaReductions
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Equivalence

/-!
# Gluing two 1-morphisms out of an algebraic space covered by two subspaces

Let `Z` be an algebraic space covered (fppf locally) by two subspaces `U₀` and `U₁`, and let
`y₀ : U₀ ⟶ 𝒳`, `y₁ : U₁ ⟶ 𝒳` be 1-morphisms into an algebraic stack together with a 2-morphism
`y₀|_{U₀ ∩ U₁} ⟶ y₁|_{U₀ ∩ U₁}`. Then there is a 1-morphism `y : Z ⟶ 𝒳` restricting to `y₀`
and to `y₁`. Two members need no cocycle condition: the transition morphisms are `e`, its
inverse (`𝒳` is fibred in groupoids) and identities.

This is how the descent step of the proof of [Stacks, Tag 0CQ7] is carried out here: instead of
gluing all the `x_i` at once along `φ_{ij}`, which requires the cocycle condition on the triple
intersections `W_i ∩ W_j ∩ W_k` and hence the scheme-theoretic density of `V`, the opens
`W_1, W_2` are merged first, then the result with `W_3`, and so on.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeMerge.exists_hom_of_twoCover`.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.PresheafOfCategories

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeMerge

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section TwoCover

variable {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U₀ U₁ : Subfunctor Z)
  (h₀ : IsAlgebraicSpace B S hS U₀.toFunctor) (h₁ : IsAlgebraicSpace B S hS U₁.toFunctor)
  (h₀₁ : IsAlgebraicSpace B S hS (U₀ ⊓ U₁).toFunctor) {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (y₀ : algebraicSpaceStack.{u, w} B S hS U₀.toFunctor h₀ ⟶ 𝒳)
  (y₁ : algebraicSpaceStack.{u, w} B S hS U₁.toFunctor h₁ ⟶ 𝒳)
  (e : algebraicSpaceStackMap.{u, w} B S hS h₀₁ h₀ (Subfunctor.homOfLe inf_le_left) ≫ y₀ ⟶
    algebraicSpaceStackMap.{u, w} B S hS h₀₁ h₁ (Subfunctor.homOfLe inf_le_right) ≫ y₁)

/-- The two-member family `U₀, U₁`, indexed by `Bool`. -/
abbrev twoCoverFamily : Bool → Subfunctor Z := fun b => bif b then U₁ else U₀

include h₀ h₁ in
/-- Each member of `twoCoverFamily U₀ U₁` is an algebraic space. -/
lemma isAlgebraicSpace_twoCoverFamily (b : Bool) :
    IsAlgebraicSpace B S hS (twoCoverFamily U₀ U₁ b).toFunctor := by
  cases b
  · exact h₀
  · exact h₁

/-- The two-member family `y₀, y₁` of 1-morphisms. -/
abbrev twoCoverHom (b : Bool) :
    algebraicSpaceStack.{u, w} B S hS (twoCoverFamily U₀ U₁ b).toFunctor
      (isAlgebraicSpace_twoCoverFamily U₀ U₁ h₀ h₁ b) ⟶ 𝒳 :=
  match b with
  | false => y₀
  | true => y₁

/-- The component of `e` at a point of `Z` lying in `U₀ ∩ U₁`. -/
abbrev twoCoverComponent (a : (fibredCategory B S hS Z).val.obj)
    (hi : a.fiber.as ∈ U₀.obj (op a.base)) (hj : a.fiber.as ∈ U₁.obj (op a.base)) :
    y₀.hom.hom.obj (fibredCategorySubfunctorObj U₀ a hi) ⟶
      y₁.hom.hom.obj (fibredCategorySubfunctorObj U₁ a hj) :=
  e.hom.hom.toNatTrans.app (fibredCategorySubfunctorObj (U₀ ⊓ U₁) a ⟨hi, hj⟩)

/-- The component `twoCoverComponent` lies over the identity of the base. -/
lemma isHomLift_twoCoverComponent (a : (fibredCategory B S hS Z).val.obj)
    (hi : a.fiber.as ∈ U₀.obj (op a.base)) (hj : a.fiber.as ∈ U₁.obj (op a.base)) :
    𝒳.val.val.p.IsHomLift (𝟙 a.base) (twoCoverComponent U₀ U₁ h₀ h₁ h₀₁ y₀ y₁ e a hi hj) :=
  e.hom.hom.isHomLift' (fibredCategorySubfunctorObj (U₀ ⊓ U₁) a ⟨hi, hj⟩)

/-- The component `twoCoverComponent` is an isomorphism, since `𝒳` is fibred in groupoids. -/
instance isIso_twoCoverComponent (a : (fibredCategory B S hS Z).val.obj)
    (hi : a.fiber.as ∈ U₀.obj (op a.base)) (hj : a.fiber.as ∈ U₁.obj (op a.base)) :
    IsIso (twoCoverComponent U₀ U₁ h₀ h₁ h₀₁ y₀ y₁ e a hi hj) :=
  Functor.IsFiberedInGroupoids.isIso_of_isHomLift_id 𝒳.val.isFiberedInGroupoids _
    (isHomLift_twoCoverComponent U₀ U₁ h₀ h₁ h₀₁ y₀ y₁ e a hi hj)

/-- The transition morphisms of the two-member family: identities, `e` and its inverse. -/
noncomputable def twoCoverTransition : ∀ (i j : Bool) (a : (fibredCategory B S hS Z).val.obj)
    (hi : a.fiber.as ∈ (twoCoverFamily U₀ U₁ i).obj (op a.base))
    (hj : a.fiber.as ∈ (twoCoverFamily U₀ U₁ j).obj (op a.base)),
    (twoCoverHom U₀ U₁ h₀ h₁ y₀ y₁ i).hom.hom.obj
        (fibredCategorySubfunctorObj (twoCoverFamily U₀ U₁ i) a hi) ⟶
      (twoCoverHom U₀ U₁ h₀ h₁ y₀ y₁ j).hom.hom.obj
        (fibredCategorySubfunctorObj (twoCoverFamily U₀ U₁ j) a hj)
  | false, false, _, _, _ => 𝟙 _
  | true, true, _, _, _ => 𝟙 _
  | false, true, a, hi, hj => twoCoverComponent U₀ U₁ h₀ h₁ h₀₁ y₀ y₁ e a hi hj
  | true, false, a, hi, hj => inv (twoCoverComponent U₀ U₁ h₀ h₁ h₀₁ y₀ y₁ e a hj hi)

end TwoCover

/-- **Gluing two 1-morphisms along a 2-morphism over the intersection.** Let `Z` be an algebraic
space and `U₀, U₁ ⊆ Z` algebraic subspaces such that every element of `Z` lies fppf locally in
`U₀` or in `U₁`. Given 1-morphisms `y₀ : U₀ ⟶ 𝒳`, `y₁ : U₁ ⟶ 𝒳` into an algebraic stack and a
2-morphism `e : y₀|_{U₀ ∩ U₁} ⟶ y₁|_{U₀ ∩ U₁}`, there is a 1-morphism `y : Z ⟶ 𝒳` whose
restrictions to `U₀` and `U₁` are 2-isomorphic to `y₀` and `y₁`. -/
theorem exists_hom_of_twoCover {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) (U₀ U₁ : Subfunctor Z)
    (h₀ : IsAlgebraicSpace B S hS U₀.toFunctor) (h₁ : IsAlgebraicSpace B S hS U₁.toFunctor)
    (h₀₁ : IsAlgebraicSpace B S hS (U₀ ⊓ U₁).toFunctor) {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (y₀ : algebraicSpaceStack.{u, w} B S hS U₀.toFunctor h₀ ⟶ 𝒳)
    (y₁ : algebraicSpaceStack.{u, w} B S hS U₁.toFunctor h₁ ⟶ 𝒳)
    (e : algebraicSpaceStackMap.{u, w} B S hS h₀₁ h₀ (Subfunctor.homOfLe inf_le_left) ≫ y₀ ⟶
      algebraicSpaceStackMap.{u, w} B S hS h₀₁ h₁ (Subfunctor.homOfLe inf_le_right) ≫ y₁)
    (hcov : ∀ (T : BigFppfOver B S hS) (z : Z.obj (op T)), ∃ R ∈ BigFppfOver.topology B S hS T,
      ∀ ⦃V : BigFppfOver B S hS⦄ ⦃f : V ⟶ T⦄, R.arrows f →
        Z.map f.op z ∈ U₀.obj (op V) ∨ Z.map f.op z ∈ U₁.obj (op V)) :
    ∃ y : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳,
      Nonempty (algebraicSpaceStackMap.{u, w} B S hS h₀ hZ U₀.ι ≫ y ≅ y₀) ∧
        Nonempty (algebraicSpaceStackMap.{u, w} B S hS h₁ hZ U₁.ι ≫ y ≅ y₁) := by
  obtain ⟨y, hy⟩ := exists_algebraicSpaceStack_hom_of_cocycle hZ (twoCoverFamily U₀ U₁)
    (isAlgebraicSpace_twoCoverFamily U₀ U₁ h₀ h₁) (twoCoverHom U₀ U₁ h₀ h₁ y₀ y₁)
    (twoCoverTransition U₀ U₁ h₀ h₁ h₀₁ y₀ y₁ e)
    (fun i j a hi hj => by
      cases i <;> cases j
      · exact IsHomLift.id (BasedFunctor.w_obj y₀.hom.hom _)
      · exact isHomLift_twoCoverComponent U₀ U₁ h₀ h₁ h₀₁ y₀ y₁ e a hi hj
      · have := isHomLift_twoCoverComponent U₀ U₁ h₀ h₁ h₀₁ y₀ y₁ e a hj hi
        exact IsHomLift.lift_id_inv_isIso (p := 𝒳.val.val.p) a.base _
      · exact IsHomLift.id (BasedFunctor.w_obj y₁.hom.hom _))
    (fun i j a b m hai haj hbi hbj => by
      cases i <;> cases j <;>
        simp only [twoCoverTransition, Category.comp_id, Category.id_comp]
      · exact (e.hom.hom.toNatTrans.naturality
          (fibredCategorySubfunctorHom (U₀ ⊓ U₁) m ⟨hai, haj⟩ ⟨hbi, hbj⟩))
      · rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
        exact (e.hom.hom.toNatTrans.naturality
          (fibredCategorySubfunctorHom (U₀ ⊓ U₁) m ⟨haj, hai⟩ ⟨hbj, hbi⟩)).symm)
    (fun i j k a hi hj hk => by
      cases i <;> cases j <;> cases k <;>
        simp [twoCoverTransition])
    (fun T z => by
      obtain ⟨R, hR, hRU⟩ := hcov T z
      refine ⟨R, hR, fun V f hf => ?_⟩
      rcases hRU hf with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩)
  exact ⟨y, hy false, hy true⟩

end AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeMerge

end
