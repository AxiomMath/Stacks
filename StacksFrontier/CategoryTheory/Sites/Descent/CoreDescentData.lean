module

public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import StacksFrontier.CategoryTheory.Functor.IsCoreInclusion
public import StacksFrontier.CategoryTheory.Sites.Descent.LocallyRepresentableSheaves
public import StacksFrontier.CategoryTheory.Sites.Descent.StrongTransDescentData

/-!
# Descent for the maximal subgroupoid of a pseudofunctor

Let `F` and `G` be pseudofunctors from `LocallyDiscrete Cᵒᵖ` to `Cat` and let
`τ : F.StrongTrans G` be a strong transformation which exhibits each category `F.obj a` as the
maximal subgroupoid of `G.obj a` — that is, each component `τ.app a` is a
`CategoryTheory.Functor.IsCoreInclusion`.  This file shows that **`F` inherits the descent
properties of `G`**: if descent along a family of morphisms is effective for `G` then it is
effective for `F`, so if `G` is a stack then so is `F`.

`StacksFrontier.CategoryTheory.Sites.Descent.StrongTransDescentData` proves the analogous
invariance along a strong transformation whose components are *equivalences*.  That result does
not apply here, and no weakening of it does: a category is not equivalent to its maximal
subgroupoid.  What is true instead is that the comparison functor on descent data is again a
core inclusion, so the transfer is the square form
`CategoryTheory.Functor.isEquivalence_of_isCoreInclusion` of "an equivalence restricts to an
equivalence of cores", applied to

```
F.obj (op S) --F.toDescentData--> F.DescentData f
    | τ.app                             | τ.descentDataFunctor
    v                                   v
G.obj (op S) --G.toDescentData--> G.DescentData f
```

whose commutativity is
`CategoryTheory.Pseudofunctor.StrongTrans.toDescentDataCompDescentDataFunctorIso`.

The mathematical content is that the gluing morphisms of a descent datum are automatically
isomorphisms (Mathlib's `CategoryTheory.Pseudofunctor.DescentData.iso`), so passing to the
maximal subgroupoid in each fibre loses no descent datum, and that an isomorphism of descent
data is componentwise an isomorphism
(`CategoryTheory.Pseudofunctor.DescentData.objIso`), so it loses no isomorphism either.

## Main results

* `CategoryTheory.Pseudofunctor.StrongTrans.isIsoWide_descentDataFunctor`: the functor induced
  on descent data by a fibrewise iso-wide strong transformation is iso-wide.
* `CategoryTheory.Pseudofunctor.StrongTrans.isEquivalence_toDescentData_of_isCoreInclusion`:
  **effective descent along a family passes to the fibrewise maximal subgroupoid.**
* `CategoryTheory.Pseudofunctor.StrongTrans.isStackFor_of_isCoreInclusion` and
  `CategoryTheory.Pseudofunctor.StrongTrans.isStack_of_isCoreInclusion`: **the fibrewise maximal
  subgroupoid of a stack is a stack.**

## References

* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
-/

@[expose] public section

namespace CategoryTheory

open Opposite Bicategory

universe t v' v u' u

namespace Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C] {F G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
  (τ : F.StrongTrans G) {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- **The functor induced on descent data by a fibrewise iso-wide strong transformation is
iso-wide.**

Faithfulness is
`CategoryTheory.Pseudofunctor.StrongTrans.faithful_descentDataFunctor`.  That a morphism of
descent data for `F` becomes an isomorphism is Mathlib's
`CategoryTheory.Pseudofunctor.DescentData.isoMk` applied to its components.  That every
isomorphism of transported descent data comes from a morphism of descent data for `F` uses that
such an isomorphism is componentwise an isomorphism, and that its compatibility descends because
`CategoryTheory.Pseudofunctor.StrongTrans.mapPullHom` is injective on a faithful component. -/
lemma isIsoWide_descentDataFunctor
    (hτ : ∀ a : LocallyDiscrete Cᵒᵖ, (τ.app a).toFunctor.IsIsoWide) :
    (τ.descentDataFunctor f).IsIsoWide := by
  have (a : LocallyDiscrete Cᵒᵖ) : (τ.app a).toFunctor.Faithful := (hτ a).faithful
  refine ⟨τ.faithful_descentDataFunctor f, ?_, ?_⟩
  · intro D₁ D₂ φ
    have he : (DescentData.isoMk
          (fun i ↦ @asIso _ _ _ _ _ ((hτ (.mk (op (X i)))).isIso_map (φ.hom i)))
          (fun _ q _ _ f₁ f₂ hf₁ hf₂ ↦
            (τ.descentDataMap f φ).comm q f₁ f₂ hf₁ hf₂)).hom =
        (τ.descentDataFunctor f).map φ := by
      ext i
      rfl
    rw [← he]
    infer_instance
  · intro D₁ D₂ e
    choose g hg using fun i ↦
      (hτ (.mk (op (X i)))).exists_map_eq (DescentData.objIso e i)
    refine ⟨{ hom := g, comm := ?_ }, ?_⟩
    · intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
      refine τ.mapPullHom_injective ?_
      have h := e.hom.comm q f₁ f₂ hf₁ hf₂
      rw [← τ.mapPullHom_comp, ← τ.mapPullHom_comp, τ.mapPullHom_map, τ.mapPullHom_map,
        hg i₁, hg i₂]
      exact h
    · ext i
      exact hg i

/-- **Effective descent along a family passes to the fibrewise maximal subgroupoid.**

If each component of `τ` exhibits `F.obj a` as the maximal subgroupoid of `G.obj a`, and descent
along the family `f` is effective for `G`, then it is effective for `F`. -/
theorem isEquivalence_toDescentData_of_isCoreInclusion
    (hτ : ∀ a : LocallyDiscrete Cᵒᵖ, (τ.app a).toFunctor.IsCoreInclusion)
    (hG : (G.toDescentData f).IsEquivalence) :
    (F.toDescentData f).IsEquivalence :=
  have := hG
  Functor.isEquivalence_of_isCoreInclusion (hτ (.mk (op S)))
    (τ.isIsoWide_descentDataFunctor f fun a ↦ (hτ a).toIsIsoWide)
    (τ.toDescentDataCompDescentDataFunctorIso f)

/-- **The fibrewise maximal subgroupoid of a pseudofunctor which is a stack for a presieve is a
stack for that presieve.** -/
theorem isStackFor_of_isCoreInclusion
    (hτ : ∀ a : LocallyDiscrete Cᵒᵖ, (τ.app a).toFunctor.IsCoreInclusion)
    {S : C} (R : Presieve S) (hG : G.IsStackFor R) : F.IsStackFor R := by
  rw [Pseudofunctor.isStackFor_iff] at hG ⊢
  exact τ.isEquivalence_toDescentData_of_isCoreInclusion _ hτ hG

/-- **The premise of the transfer is satisfiable.**  The identity strong transformation of a
pseudofunctor whose fibres are groupoids exhibits each fibre as its own maximal subgroupoid, so
the three statements above are implications about an inhabited premise and not vacuously true.
The non-degenerate inhabitant is the fibrewise inclusion of maximal subgroupoids; see
`AlgebraicGeometry.frobeniusColimitModuleCoreInclusion`. -/
lemma isCoreInclusion_id_app
    [∀ a : LocallyDiscrete Cᵒᵖ, IsGroupoid (F.obj a : Type u')]
    (a : LocallyDiscrete Cᵒᵖ) :
    ((StrongTrans.id F).app a).toFunctor.IsCoreInclusion :=
  Functor.isCoreInclusion_id _

/-- **The fibrewise maximal subgroupoid of a stack is a stack.** -/
theorem isStack_of_isCoreInclusion
    (hτ : ∀ a : LocallyDiscrete Cᵒᵖ, (τ.app a).toFunctor.IsCoreInclusion)
    (J : GrothendieckTopology C) [G.IsStack J] : F.IsStack J :=
  Pseudofunctor.IsStack.of_isStackFor fun _ R hR ↦
    τ.isStackFor_of_isCoreInclusion hτ _ (G.isStackFor' R hR)

end Pseudofunctor.StrongTrans

end CategoryTheory

end
