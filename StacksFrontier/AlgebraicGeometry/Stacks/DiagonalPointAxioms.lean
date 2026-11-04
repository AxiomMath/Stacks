module

public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalPointFibreOverBase
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverBased
public import StacksFrontier.CategoryTheory.Sites.Localization.StacksOverSlice
public import StacksFrontier.CategoryTheory.Sites.Stack.OverIsStack
public import StacksFrontier.CategoryTheory.Sites.Stack.PresheafElementsStack
public import StacksFrontier.CategoryTheory.Sites.Stack.SetoidToSets
public import StacksFrontier.CategoryTheory.Sites.Stack.SetoidTwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.ReverseEffective

/-!
# Axiom [0] for the functor `Y` of the proof of Stacks 07Y5

Let `𝒳` be a category fibred in groupoids over the big fppf site of `S` which is a stack in
groupoids for a subcanonical topology `J` (axiom [0] for `𝒳` is the case of the étale topology).
For a scheme `V` over `S` and a point `y` of `𝒳 × 𝒳` over `V`, the 2-fibre product
`𝒴 = (Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳` is then a stack in setoids, and its functor of
isomorphism classes `Y` is a sheaf: this is the sentence "Observe that `Y` is a sheaf for the
étale topology by Stacks, Lemmas 0432 and 05UI" of the proof of Stacks 07Y5.

The 2-fibre product is a stack by Stacks 02ZL (its three factors are: `𝒳` by hypothesis,
`(Sch/V)_{fppf}` because `J` is subcanonical, Stacks 04WU and 04WV, and `𝒳 × 𝒳` by 02ZL
again); its fibres are setoids by
`AlgebraicGeometry.Stack.diagonalPointFibreOverBase_isFiberedInSetoids`, which is the content of
Stacks 05UI here. Stacks 0432 turns the stack in setoids into a sheaf of sets.

## Main results

* `AlgebraicGeometry.Stack.isStackInSetoids_diagonalPointFibreOverBase`.
* `AlgebraicGeometry.Stack.isSheaf_diagonalPointFunctorOverBase`: axiom [0] for `Y`.

## References

* [Stacks Project, Tag 07Y5](https://stacks.math.columbia.edu/tag/07Y5)
* [Stacks Project, Tag 0432](https://stacks.math.columbia.edu/tag/0432)
* [Stacks Project, Tag 05UI](https://stacks.math.columbia.edu/tag/05UI)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {V : BigFppfOver B S hS}
  {y : BigFppfOver B V.left.1 V.left.2 ⥤ (CatFiberedInGroupoids.product 𝒳 𝒳).val.obj}
  (hy : y ⋙ (CatFiberedInGroupoids.product 𝒳 𝒳).val.p = Over.map V.hom)
  (J : GrothendieckTopology B.Schemes) [J.Subcanonical]

include hy in
/-- **`𝒴` is a stack in setoids** for the topology `J` restricted to `(Sch/S)_{fppf}`, as soon as
`𝒳` is a stack in groupoids for it and `J` is subcanonical. -/
theorem isStackInSetoids_diagonalPointFibreOverBase
    (hstack : 𝒳.val.p.IsStackInGroupoids.{u + 1} (J.over (B.obj hS))) :
    (diagonalPointFibreOverBase B S hS 𝒳 V y).IsStackInSetoids (J.over (B.obj hS)) := by
  have hrep (X : B.Schemes) : Presheaf.IsSheaf J (yoneda.obj X) :=
    (isSheaf_iff_isSheaf_of_type J _).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)
  have hT : (Over.map V.hom).IsStack (J.over (B.obj hS)) :=
    Over.isStack_of_comp_forget (Over.map V.hom) (hrep _) (by
      rw [Over.mapForget_eq]
      exact (Over.isStack_forget_iff_isSheaf (U := V.left) J).mpr (hrep _))
  have hid : (𝟭 (BigFppfOver B S hS)).IsStack (J.over (B.obj hS)) :=
    Over.isStack_of_comp_forget (𝟭 (BigFppfOver B S hS)) (hrep _)
      ((Over.isStack_forget_iff_isSheaf (U := B.obj hS) J).mpr (hrep _))
  let := 𝒳.isFiberedInGroupoids.isFibered
  have h𝒳 : 𝒳.val.p.IsStack (J.over (B.obj hS)) := Functor.isStack_of_isStackInGroupoids hstack
  have hprod : (CatFiberedInGroupoids.product 𝒳 𝒳).val.p.IsStack (J.over (B.obj hS)) :=
    (TwoFibreProductOver.isStack_isFiberedInGroupoids_structureFunctor h𝒳 h𝒳 hid
      𝒳.isFiberedInGroupoids 𝒳.isFiberedInGroupoids Functor.isFiberedInGroupoids_id
      (Functor.comp_id _) (Functor.comp_id _)).1
  have h𝒴 : (diagonalPointFibreOverBase B S hS 𝒳 V y).IsStack (J.over (B.obj hS)) :=
    (TwoFibreProductOver.isStack_isFiberedInGroupoids_structureFunctor hT h𝒳 hprod
      (Functor.IsFiberedInGroupoids.over_map V.hom) 𝒳.isFiberedInGroupoids
      (CatFiberedInGroupoids.product 𝒳 𝒳).isFiberedInGroupoids hy
      (diagonalBasedFunctor B S hS 𝒳).w).1
  have hset := diagonalPointFibreOverBase_isFiberedInSetoids hy
  exact ⟨h𝒴, fun U => hset.isFiberedInGroupoids.fiber_isGroupoid U, hset.fiber_isThin⟩

include hy in
/-- **Axiom [0] for `Y`** (the proof of Stacks 07Y5, citing Stacks 0432 and 05UI): the functor
of isomorphism classes of `𝒴` is a sheaf for `J`, as soon as `𝒳` is a stack in groupoids for `J`
and `J` is subcanonical. -/
theorem isSheaf_diagonalPointFunctorOverBase
    (hstack : 𝒳.val.p.IsStackInGroupoids.{u + 1} (J.over (B.obj hS))) :
    Presheaf.IsSheaf (J.over (B.obj hS)) (diagonalPointFunctorOverBase hy) := by
  let : (BasedCategory.ofFunctor (diagonalPointFibreOverBase B S hS 𝒳 V y)).p.IsFiberedInSetoids :=
    diagonalPointFibreOverBase_isFiberedInSetoids hy
  let : (BasedCategory.ofFunctor
      (presheafOfCategories (diagonalPointFunctorOverBase hy ⋙ typeToCat)).p).p.IsFiberedInSets :=
    PresheafOfCategories.isFiberedInSets_discreteProjection _
  let e := (diagonalPointFibreOverBaseEquivalenceOver hy).toBasedEquivalence
    (𝒳 := BasedCategory.ofFunctor (diagonalPointFibreOverBase B S hS 𝒳 V y))
    (𝒴 := BasedCategory.ofFunctor
      (presheafOfCategories (diagonalPointFunctorOverBase hy ⋙ typeToCat)).p)
  have h := (BasedCategory.isStackInSetoids_iff_isSheaf_objPresheaf_of_equivalence e
    (J.over (B.obj hS))).1 (isStackInSetoids_diagonalPointFibreOverBase hy J hstack)
  have h' := (Presheaf.isSheaf_of_iso_iff
    (PresheafOfCategories.objPresheafIso (diagonalPointFunctorOverBase hy))).1 h
  rw [isSheaf_iff_isSheaf_of_type] at h' ⊢
  exact (Presieve.isSheaf_comp_uliftFunctor_iff _).1 h'

end AlgebraicGeometry.Stack

end
