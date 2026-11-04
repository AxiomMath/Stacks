module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaRepresentableProducts
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor

/-!
# The criteria for a representable diagonal: conditions (6) and (7) (Stacks 045G)

Let `S` be a scheme contained in a big fppf site `B` and let `𝒳` be a category fibred in
groupoids over the big fppf site of `S`. Condition (6) of Stacks 045G says that the 2-fibre
product over `𝒳` of any two 1-morphisms out of *representable* categories fibred in groupoids is
representable by an algebraic space, and condition (7) says that every 1-morphism to `𝒳` out of a
category fibred in groupoids representable by an *algebraic space* is representable by algebraic
spaces.

This is the one equivalence of Stacks 045G the source does not call formal. In the direction (6)
to (7) it is Stacks 0300: condition (6) is carried along the equivalences already proved to
condition (3), which says that a scheme-valued point `y` of `𝒳` is representable by algebraic
spaces, and then `𝒰 ×_𝒳 (Sch/V)_{fppf}` is representable by an algebraic space because `𝒰` is. In
the direction (7) to (6) it is Stacks 0300 again, now with the roles of the two factors exchanged:
condition (7) applies to the first factor of the 2-fibre product and the second one is
representable by an algebraic space, being representable by a scheme.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_twoFibreProduct_swap_iff`: the 2-fibre
  product over `𝒳` is representable by an algebraic space exactly when the one with the two
  factors exchanged is.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_of_isRepresentableCFG`: a representable
  category fibred in groupoids is representable by an algebraic space.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_forall_twoFibreProduct`: a
  1-morphism to `𝒳` is representable by algebraic spaces as soon as its 2-fibre product with every
  scheme-valued point of `𝒳` is representable by an algebraic space over `S`.
* `AlgebraicGeometry.Stack.isRepresentableFromAlgebraicSpaces_of_isRepresentableFromSchemes`: the
  implication from condition (3) to condition (7).
* `hasAlgebraicSpaceRepresentableProducts_iff_isRepresentableFromAlgebraicSpaces`, in the namespace
  `AlgebraicGeometry.Stack`: **Stacks 045G**, the equivalence of conditions (6) and (7).

## Implementation notes

Both directions need the 2-fibre product in an order the hypothesis does not supply it in, because
Stacks 0300 makes the *first* factor the one that is representable by an algebraic space while the
*second* leg is the one that has to be representable by algebraic spaces. The exchange is
`CategoryTheory.TwoFibreProductOver.swap`, which commutes with the structure functor on the nose,
so `StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence` turns it into an equivalence
in the 2-category of categories over the site and
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_iff_of_equivalenceOver` into the asserted
equivalence of the two conditions.

Condition (7) is about representability over the big fppf site of a *scheme-valued point*, while
Stacks 0300 produces representability over the site of `S`; the two are matched by Stacks 04SG,
`AlgebraicGeometry.Stack.exists_isAlgebraicSpace_equivalenceOver_of_comp_overMap`, and the first
factors — the big fppf site of `V` and the slice of the site of `S` over `V` — by the
iterated-slice equivalence fed to `CategoryTheory.TwoFibreProductOver.precomposeFst`. That is
exactly the argument of the direction (4) to (3), and it is isolated here as
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_forall_twoFibreProduct`, whose second
factor is an arbitrary category fibred in groupoids.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w v₁ w₁ v₂ w₂ a₁ b₁ a₂ b₂

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))

/-- **The 2-fibre product over `𝒳` is symmetric in its two factors.** The 2-fibre product of `x`
and `y` over `𝒳` is representable by an algebraic space exactly when the 2-fibre product of `y`
and `x` is.

`CategoryTheory.TwoFibreProductOver.swap` exchanges the two factors and inverts the comparison
isomorphism of an object; it is strictly over the site, so it is an equivalence in the 2-category
of categories over the site. -/
theorem isRepresentableByAlgebraicSpace_twoFibreProduct_swap_iff
    (𝒯₁ : CatFiberedInGroupoids.{u, a₁, u + 1, b₁} (BigFppfOver B S hS))
    (𝒯₂ : CatFiberedInGroupoids.{u, a₂, u + 1, b₂} (BigFppfOver B S hS))
    (x : 𝒯₁.val ⥤ᵇ 𝒳.val) (y : 𝒯₂.val ⥤ᵇ 𝒳.val) :
    IsRepresentableByAlgebraicSpace B S hS (twoFibreProduct B S hS 𝒳 𝒯₁ 𝒯₂ x y) ↔
      IsRepresentableByAlgebraicSpace B S hS (twoFibreProduct B S hS 𝒳 𝒯₂ 𝒯₁ y x) := by
  obtain ⟨k⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (TwoFibreProductOver.isFiberedInGroupoids 𝒯₁.val.p 𝒯₂.val.p 𝒳.val.p x.toFunctor y.toFunctor
      𝒯₁.isFiberedInGroupoids 𝒯₂.isFiberedInGroupoids 𝒳.isFiberedInGroupoids x.w y.w)
    (TwoFibreProductOver.isFiberedInGroupoids 𝒯₂.val.p 𝒯₁.val.p 𝒳.val.p y.toFunctor x.toFunctor
      𝒯₂.isFiberedInGroupoids 𝒯₁.isFiberedInGroupoids 𝒳.isFiberedInGroupoids y.w x.w)
    (TwoFibreProductOver.swap 𝒯₁.val.p 𝒯₂.val.p 𝒳.val.p x.toFunctor y.toFunctor)
    (TwoFibreProductOver.swap_comp_structureFunctor _ _ _ _ _) inferInstance
  exact (isRepresentableByAlgebraicSpace_iff_of_equivalenceOver k).symm

/-- Stacks 0300 with the factors exchanged: the 2-fibre product of `f` and `g` over `𝒳` is
representable by an algebraic space when `f` is representable by algebraic spaces and the source
of `g` is representable by an algebraic space. -/
private theorem isRepresentableByAlgebraicSpace_twoFibreProduct_of_right
    (𝒯₁ : CatFiberedInGroupoids.{u, a₁, u + 1, b₁} (BigFppfOver B S hS))
    (𝒯₂ : CatFiberedInGroupoids.{u, a₂, u + 1, b₂} (BigFppfOver B S hS))
    (g : 𝒯₁.val ⥤ᵇ 𝒳.val) (f : 𝒯₂.val ⥤ᵇ 𝒳.val)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f)
    (h𝒯₁ : IsRepresentableByAlgebraicSpace B S hS 𝒯₁) :
    IsRepresentableByAlgebraicSpace B S hS (twoFibreProduct B S hS 𝒳 𝒯₂ 𝒯₁ f g) :=
  (isRepresentableByAlgebraicSpace_twoFibreProduct_swap_iff B S hS 𝒳 𝒯₁ 𝒯₂ g f).1
    (isRepresentableByAlgebraicSpace_twoFibreProduct B S hS 𝒳 𝒯₁ 𝒯₂ g f hf h𝒯₁)

/-- **Stacks 04SV for a representable category fibred in groupoids.** A category fibred in
groupoids over the big fppf site of `S` which is representable in the sense of Stacks 02Y8 — that
is, equivalent over the site to a slice — is representable by an algebraic space over `S`, namely
by the algebraic space of points of the representing scheme. -/
theorem isRepresentableByAlgebraicSpace_of_isRepresentableCFG
    (𝒯 : CatFiberedInGroupoids.{u, a₁, u + 1, b₁} (BigFppfOver B S hS))
    (h : Stacks.RepresentableMorphism.IsRepresentableCFG 𝒯.val.p) :
    IsRepresentableByAlgebraicSpace B S hS 𝒯 := by
  obtain ⟨X, E, hE⟩ := h
  obtain ⟨G, hG, ⟨η, -⟩, ⟨ε, -⟩⟩ := hE.exists_inverse
  obtain ⟨k⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    𝒯.isFiberedInGroupoids (schemeFibredCategory B S hS X).isFiberedInGroupoids E
    hE.isCartesianFunctor.comm (CategoryTheory.Equivalence.mk E G ε.symm η).isEquivalence_functor
  exact isRepresentableByAlgebraicSpace_of_equivalenceOver k
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS X)

/-- **A pointwise criterion for representability by algebraic spaces.** A 1-morphism `x` to `𝒳`
from a category fibred in groupoids `𝒯` is representable by algebraic spaces as soon as, for every
scheme `V` over `S` and every 1-morphism `y` to `𝒳` from the category represented by `V`, the
2-fibre product of `y` and `x` over `𝒳` is representable by an algebraic space over `S`.

This is the argument of the direction (4) to (3) of Stacks 045G with the second factor an arbitrary
category fibred in groupoids: the scheme-valued point of `𝒳` over `V` that condition (7) is stated
with becomes a 1-morphism out of the category represented by `V` along the iterated-slice
equivalence, which `CategoryTheory.TwoFibreProductOver.precomposeFst` turns into an equivalence of
the two 2-fibre products, and the change of base from `S` to `V` is Stacks 04SG. -/
theorem isRepresentableByAlgebraicSpaces_of_forall_twoFibreProduct
    (𝒯 : CatFiberedInGroupoids.{u, a₁, u + 1, b₁} (BigFppfOver B S hS))
    (x : 𝒯.val ⥤ᵇ 𝒳.val)
    (h : ∀ (V : BigFppfOver B S hS) (y : (schemeFibredCategory B S hS V).val ⥤ᵇ 𝒳.val),
      IsRepresentableByAlgebraicSpace B S hS
        (twoFibreProduct B S hS 𝒳 (schemeFibredCategory B S hS V) 𝒯 y x)) :
    IsRepresentableByAlgebraicSpaces B S hS x := by
  dsimp only [IsRepresentableByAlgebraicSpaces]
  intro V z hz
  have hy : (Over.iteratedSliceForward V ⋙ z) ⋙ 𝒳.val.p =
      (schemeFibredCategory B S hS V).val.p :=
    (congrArg (fun F => Over.iteratedSliceForward V ⋙ F) hz).trans
      (Over.iteratedSliceForward_comp_map V)
  obtain ⟨G, hG, ⟨e⟩⟩ := h V ⟨Over.iteratedSliceForward V ⋙ z, hy⟩
  have hstruct := TwoFibreProductOver.isFiberedInGroupoids (Over.map V.hom)
    𝒯.val.p 𝒳.val.p z x.toFunctor (Functor.IsFiberedInGroupoids.over_map V.hom)
    𝒯.isFiberedInGroupoids 𝒳.isFiberedInGroupoids hz x.w
  have hfstc : TwoFibreProductOver.fst (Over.map V.hom) 𝒯.val.p 𝒳.val.p z x.toFunctor ⋙
        Over.map V.hom =
      TwoFibreProductOver.structureFunctor (Over.map V.hom) 𝒯.val.p 𝒳.val.p z x.toFunctor :=
    TwoFibreProductOver.fst_comp_eq
  have hqf : (TwoFibreProductOver.fst (Over.map V.hom) 𝒯.val.p 𝒳.val.p z
      x.toFunctor).IsFiberedInGroupoids :=
    (Functor.isFiberedInGroupoids_comp_overMap_iff V.hom _).1 (by rwa [hfstc])
  obtain ⟨k⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (TwoFibreProductOver.isFiberedInGroupoids (schemeFibredCategory B S hS V).val.p
      𝒯.val.p 𝒳.val.p (Over.iteratedSliceForward V ⋙ z) x.toFunctor
      (schemeFibredCategory B S hS V).isFiberedInGroupoids 𝒯.isFiberedInGroupoids
      𝒳.isFiberedInGroupoids hy x.w)
    hstruct
    (TwoFibreProductOver.precomposeFst (schemeFibredCategory B S hS V).val.p
      (Over.map V.hom) 𝒯.val.p 𝒳.val.p z x.toFunctor
      (Over.iteratedSliceForward V) (Over.iteratedSliceForward_comp_map V))
    (TwoFibreProductOver.precomposeFst_comp_structureFunctor _ _ _ _ _ _ _ _)
    (TwoFibreProductOver.isEquivalence_precomposeFst
      (schemeFibredCategory B S hS V).val.p (Over.map V.hom) 𝒯.val.p 𝒳.val.p z x.toFunctor
      (Over.iteratedSliceForward V) (Over.iteratedSliceForward_comp_map V)
      𝒯.isFiberedInGroupoids (schemeFibredCategory B S hS V).isFiberedInGroupoids
      (Functor.IsFiberedInGroupoids.over_map V.hom)
      (Over.iteratedSliceEquiv V).isEquivalence_functor hz)
  exact exists_isAlgebraicSpace_equivalenceOver_of_comp_overMap B S hS V _ hqf hG
    (StacksRepresentableCFG.EquivalenceOver.ofEq TwoFibreProductOver.fst_comp_eq.symm
      (k.symm.trans e))

/-- **Stacks 045G, the implication from condition (3) to condition (7).** If every 1-morphism to
`𝒳` from the category represented by a scheme over `S` is representable by algebraic spaces, then
so is every 1-morphism to `𝒳` from a category fibred in groupoids representable by an algebraic
space over `S`.

This is the source's own argument: a scheme-valued point `y` of `𝒳` is representable by algebraic
spaces by condition (3), so Stacks 0300 makes `𝒰 ×_{x, 𝒳, y} (Sch/V)_{fppf}` representable by an
algebraic space, and exchanging the two factors gives the 2-fibre product in the order the
pointwise criterion wants it. -/
theorem isRepresentableFromAlgebraicSpaces_of_isRepresentableFromSchemes
    (h₃ : IsRepresentableFromSchemes B S hS 𝒳) :
    IsRepresentableFromAlgebraicSpaces.{u, v, w, v₁, w₁} B S hS 𝒳 :=
  fun 𝒯 h𝒯 x => isRepresentableByAlgebraicSpaces_of_forall_twoFibreProduct B S hS 𝒳 𝒯 x
    fun V y => isRepresentableByAlgebraicSpace_twoFibreProduct_of_right B S hS 𝒳 𝒯
      (schemeFibredCategory B S hS V) x y (h₃ V y) h𝒯

/-- **Stacks 045G, the equivalence of conditions (6) and (7).** The 2-fibre product over `𝒳` of
any two 1-morphisms out of representable categories fibred in groupoids is representable by an
algebraic space if and only if every 1-morphism to `𝒳` out of a category fibred in groupoids
representable by an algebraic space is representable by algebraic spaces. -/
@[stacks 045G "parts (6) and (7)"]
theorem hasAlgebraicSpaceRepresentableProducts_iff_isRepresentableFromAlgebraicSpaces :
    HasAlgebraicSpaceRepresentableProducts.{u, v, w, v₁, w₁, v₂, w₂} B S hS 𝒳 ↔
      IsRepresentableFromAlgebraicSpaces.{u, v, w, v₁, w₁} B S hS 𝒳 := by
  refine ⟨fun h₆ => ?_, fun h₇ 𝒯₁ 𝒯₂ hT₁ hT₂ x y => ?_⟩
  · exact isRepresentableFromAlgebraicSpaces_of_isRepresentableFromSchemes B S hS 𝒳
      ((isRepresentableFromSchemes_iff_hasAlgebraicSpaceSchemePointProducts B S hS 𝒳).2
        ((hasAlgebraicSpaceSchemePointProducts_iff_hasAlgebraicSpaceRepresentableProducts
          B S hS 𝒳).2 h₆))
  · exact isRepresentableByAlgebraicSpace_twoFibreProduct_of_right B S hS 𝒳 𝒯₂ 𝒯₁ y x
      (h₇ 𝒯₁ (isRepresentableByAlgebraicSpace_of_isRepresentableCFG B S hS 𝒯₁ hT₁) x)
      (isRepresentableByAlgebraicSpace_of_isRepresentableCFG B S hS 𝒯₂ hT₂)

end AlgebraicGeometry.Stack

end
