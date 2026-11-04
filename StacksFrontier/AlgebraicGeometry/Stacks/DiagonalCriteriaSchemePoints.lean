module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilitySmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor

/-!
# The criteria for a representable diagonal: conditions (3) and (4)

Let `S` be a scheme contained in a big fppf site `B` and let `𝒳` be a category fibred in
groupoids over the big fppf site of `S`. Every 1-morphism to `𝒳` from the category represented by
a scheme over `S` is representable by algebraic spaces if and only if the 2-fibre product over `𝒳`
of any two such 1-morphisms is representable by an algebraic space.

Spelled out, condition (3) says that for every scheme `V` over `S` and every scheme-valued point
`z` of `𝒳` over `V`, the first projection of `(Sch/V)_{fppf} ×_{z, 𝒳, x} (Sch/U)_{fppf}` is
equivalent, *over the big fppf site of `V`*, to an algebraic space over `V`; condition (4) says
that the same 2-fibre product is equivalent, *over the big fppf site of `S`*, to an algebraic space
over `S`. The two are matched by
`AlgebraicGeometry.Stack.exists_isAlgebraicSpace_equivalenceOver_comp_overMap_iff` and by the
identification of the big fppf site of `V` with the slice of the site of `S` over `V`.

## Main results

* `CategoryTheory.Over.iteratedSliceForward_comp_map`: composing
  `CategoryTheory.Over.iteratedSliceForward` with `Over.map U.hom` gives `Over.forget U`.
* `AlgebraicGeometry.Stack.isRepresentableFromSchemes_iff_hasAlgebraicSpaceSchemePointProducts`:
  the equivalence of conditions (3) and (4).

## Implementation notes

`Over.iteratedSliceBackward V ⋙ Over.forget V` is `Over.map V.hom` on the nose, while
`Over.iteratedSliceForward V ⋙ Over.map V.hom` is `Over.forget V` only up to
`CategoryTheory.Over.w`, so `CategoryTheory.Over.iteratedSliceForward_comp_map` is proved with
`CategoryTheory.Functor.ext`.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.PresheafOfCategories

namespace CategoryTheory.Over

universe v₁ u₁

/-- The iterated-slice equivalence identifies the slice of `𝒞` at `U` with the slice of `𝒞/U.left`
at the structure morphism of `U`: composing `CategoryTheory.Over.iteratedSliceForward` with the
relocalization functor of `U.hom` gives the forgetful functor of `𝒞/U`. -/
@[sga "4 IV 5.5" "partial"]
lemma iteratedSliceForward_comp_map {T : Type u₁} [Category.{v₁} T] {X : T} (U : Over X) :
    Over.iteratedSliceForward U ⋙ Over.map U.hom = Over.forget U := by
  refine CategoryTheory.Functor.ext
    (fun m => PresheafOfCategories.over_mk_eq m.left (Over.w m.hom)) (fun m m' f => ?_)
  refine PresheafOfCategories.over_hom_eq_conj
    (PresheafOfCategories.over_mk_eq m.left (Over.w m.hom))
    (PresheafOfCategories.over_mk_eq m'.left (Over.w m'.hom)) rfl rfl _ _ ?_
  simp
  rfl

end CategoryTheory.Over

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))

/-- Every 1-morphism to `𝒳` from the category represented by a scheme over `S` is representable
by algebraic spaces if and only if the 2-fibre product over `𝒳` of any two such 1-morphisms is
representable by an algebraic space. -/
@[stacks 045G "parts (3) and (4)"]
theorem isRepresentableFromSchemes_iff_hasAlgebraicSpaceSchemePointProducts :
    IsRepresentableFromSchemes B S hS 𝒳 ↔ HasAlgebraicSpaceSchemePointProducts B S hS 𝒳 := by
  constructor
  · intro h₃ U V x y
    have hz : (Over.iteratedSliceBackward U ⋙ x.toFunctor) ⋙ 𝒳.val.p = Over.map U.hom :=
      congrArg (fun F => Over.iteratedSliceBackward U ⋙ F) x.w
    obtain ⟨F, hF, ⟨e⟩⟩ := h₃ V y U (Over.iteratedSliceBackward U ⋙ x.toFunctor) hz
    obtain ⟨G, hG, ⟨e'⟩⟩ := exists_isAlgebraicSpace_equivalenceOver_comp_overMap B S hS U
      (TwoFibreProductOver.fst (Over.map U.hom) (schemeFibredCategory B S hS V).val.p 𝒳.val.p
        (Over.iteratedSliceBackward U ⋙ x.toFunctor) y.toFunctor) hF e
    refine ⟨G, hG, ?_⟩
    obtain ⟨k⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
      (TwoFibreProductOver.isFiberedInGroupoids (Over.map U.hom)
        (schemeFibredCategory B S hS V).val.p 𝒳.val.p
        (Over.iteratedSliceBackward U ⋙ x.toFunctor) y.toFunctor
        (Functor.IsFiberedInGroupoids.over_map U.hom)
        (schemeFibredCategory B S hS V).isFiberedInGroupoids 𝒳.isFiberedInGroupoids hz y.w)
      (TwoFibreProductOver.isFiberedInGroupoids (schemeFibredCategory B S hS U).val.p
        (schemeFibredCategory B S hS V).val.p 𝒳.val.p x.toFunctor y.toFunctor
        (schemeFibredCategory B S hS U).isFiberedInGroupoids
        (schemeFibredCategory B S hS V).isFiberedInGroupoids 𝒳.isFiberedInGroupoids x.w y.w)
      (TwoFibreProductOver.precomposeFst (Over.map U.hom)
        (schemeFibredCategory B S hS U).val.p (schemeFibredCategory B S hS V).val.p 𝒳.val.p
        x.toFunctor y.toFunctor (Over.iteratedSliceBackward U) rfl)
      (TwoFibreProductOver.precomposeFst_comp_structureFunctor _ _ _ _ _ _ _ _)
      (TwoFibreProductOver.isEquivalence_precomposeFst (Over.map U.hom)
        (schemeFibredCategory B S hS U).val.p (schemeFibredCategory B S hS V).val.p 𝒳.val.p
        x.toFunctor y.toFunctor (Over.iteratedSliceBackward U) rfl
        (schemeFibredCategory B S hS V).isFiberedInGroupoids
        (Functor.IsFiberedInGroupoids.over_map U.hom)
        (schemeFibredCategory B S hS U).isFiberedInGroupoids
        (Over.iteratedSliceEquiv U).symm.isEquivalence_functor x.w)
    exact ⟨k.symm.trans (StacksRepresentableCFG.EquivalenceOver.ofEq
      (TwoFibreProductOver.fst_comp_eq) e')⟩
  · intro h₄ U x
    dsimp only [IsRepresentableByAlgebraicSpaces]
    intro V z hz
    have hy : (Over.iteratedSliceForward V ⋙ z) ⋙ 𝒳.val.p =
        (schemeFibredCategory B S hS V).val.p :=
      (congrArg (fun F => Over.iteratedSliceForward V ⋙ F) hz).trans
        (Over.iteratedSliceForward_comp_map V)
    obtain ⟨G, hG, ⟨e⟩⟩ := h₄ V U ⟨Over.iteratedSliceForward V ⋙ z, hy⟩ x
    have hstruct := TwoFibreProductOver.isFiberedInGroupoids (Over.map V.hom)
      (schemeFibredCategory B S hS U).val.p 𝒳.val.p z x.toFunctor
      (Functor.IsFiberedInGroupoids.over_map V.hom)
      (schemeFibredCategory B S hS U).isFiberedInGroupoids 𝒳.isFiberedInGroupoids hz x.w
    have hfstc : TwoFibreProductOver.fst (Over.map V.hom)
          (schemeFibredCategory B S hS U).val.p 𝒳.val.p z x.toFunctor ⋙ Over.map V.hom =
        TwoFibreProductOver.structureFunctor (Over.map V.hom)
          (schemeFibredCategory B S hS U).val.p 𝒳.val.p z x.toFunctor :=
      TwoFibreProductOver.fst_comp_eq
    have hqf : (TwoFibreProductOver.fst (Over.map V.hom)
        (schemeFibredCategory B S hS U).val.p 𝒳.val.p z x.toFunctor).IsFiberedInGroupoids :=
      (Functor.isFiberedInGroupoids_comp_overMap_iff V.hom _).1 (hfstc ▸ hstruct)
    obtain ⟨k⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
      (TwoFibreProductOver.isFiberedInGroupoids (schemeFibredCategory B S hS V).val.p
        (schemeFibredCategory B S hS U).val.p 𝒳.val.p (Over.iteratedSliceForward V ⋙ z)
        x.toFunctor (schemeFibredCategory B S hS V).isFiberedInGroupoids
        (schemeFibredCategory B S hS U).isFiberedInGroupoids 𝒳.isFiberedInGroupoids hy x.w)
      hstruct
      (TwoFibreProductOver.precomposeFst (schemeFibredCategory B S hS V).val.p
        (Over.map V.hom) (schemeFibredCategory B S hS U).val.p 𝒳.val.p z x.toFunctor
        (Over.iteratedSliceForward V) (Over.iteratedSliceForward_comp_map V))
      (TwoFibreProductOver.precomposeFst_comp_structureFunctor _ _ _ _ _ _ _ _)
      (TwoFibreProductOver.isEquivalence_precomposeFst
        (schemeFibredCategory B S hS V).val.p (Over.map V.hom)
        (schemeFibredCategory B S hS U).val.p 𝒳.val.p z x.toFunctor
        (Over.iteratedSliceForward V) (Over.iteratedSliceForward_comp_map V)
        (schemeFibredCategory B S hS U).isFiberedInGroupoids
        (schemeFibredCategory B S hS V).isFiberedInGroupoids
        (Functor.IsFiberedInGroupoids.over_map V.hom)
        (Over.iteratedSliceEquiv V).isEquivalence_functor hz)
    exact exists_isAlgebraicSpace_equivalenceOver_of_comp_overMap B S hS V _ hqf hG
      (StacksRepresentableCFG.EquivalenceOver.ofEq TwoFibreProductOver.fst_comp_eq.symm
        (k.symm.trans e))

end AlgebraicGeometry.Stack

end
