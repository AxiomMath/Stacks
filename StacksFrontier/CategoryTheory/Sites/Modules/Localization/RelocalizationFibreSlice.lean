module

public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RelocalizationBaseChange

/-! # The fibre form and the slice form of Stacks 04J4's comparison agree

Stacks 04J4 identifies the inverse image of a relocalization with base change, and this
repository carries that identification twice.  `relocalizationFibreIso` states it on the
*inverses* of Stacks 04IE's equivalences,
```
  E_K⁻¹ ∘ j_{H/K}⁻¹ ≅ (base change along a) ∘ E_H⁻¹ ,
```
which is the form the fibre computation produces, and `relocalizationInverseImageSliceIso`
states it on the *functors*,
```
  j_{H/K}⁻¹ ∘ E_H ≅ E_K ∘ (base change along a) ,
```
which is the form every consumer uses.  The second is built from the first by inserting the unit
of `E_K` and the counit of `E_H`, so a consumer holding the fibre form at an object `S` of
`Sh(C)/K` cannot reach the slice form directly: the slice form speaks about objects of the
localized topos, and `S` is only isomorphic to the image of one.

This file supplies the missing bridge.  The transport is the counit of `E_K` itself: the fibre
comparison at `S`, pushed through `E_H` and followed by the counit of `E_H`, is the slice
comparison at `E_K⁻¹S` followed by base change applied to the counit of `E_K` at `S`.  No
essential surjectivity is invoked — `E_K` really does come with that isomorphism — and the proof
is the naturality of the two comparisons together with `Equivalence.unit_inverse_comp`.

## Main results

* `AlgebraicGeometry.RingedTopos.functor_map_relocalizationFibreIso_hom_app_comp_counit`: the
  fibre form of Stacks 04J4's comparison, transported across Stacks 04IE's equivalences, is its
  slice form.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedTopos

attribute [local instance] AlgebraicGeometry.RingedTopos.isContinuous_elementPostcomp
  AlgebraicGeometry.RingedTopos.isCocontinuous_elementPostcomp

variable (X : RingedTopos.{u, u, u}) {H K : X.Topos}

/-- **Stacks 04J4: the fibre form of the comparison is its slice form.** For `a : H ⟶ K` and an
object `S` of `Sh(C)/K`, the component of `relocalizationFibreIso` at `S`, pushed through the
equivalence of Stacks 04IE at `H` and followed by that equivalence's counit, is the component of
`relocalizationInverseImageSliceIso` at `E_K⁻¹S`, followed by base change along `a` applied to
the counit of the equivalence at `K`.

The right-hand side is the only place the two forms can meet: `relocalizationFibreIso` is
indexed by objects of `Sh(C)/K` and `relocalizationInverseImageSliceIso` by objects of the
localized topos, and the counit of `E_K` is what carries the one indexing to the other.

Unfolding `relocalizationInverseImageSliceIso` holds by `rfl` (its unitors contribute
identities), after which the identity is the naturality of the fibre comparison at the counit,
the naturality of the counit of the equivalence at `H`, and the triangle identity
`CategoryTheory.Equivalence.unit_inverse_comp`, which collapses the inserted unit. -/
theorem functor_map_relocalizationFibreIso_hom_app_comp_counit (a : H ⟶ K) (S : Over K) :
    (localizationEquivalence X H).functor.map ((X.relocalizationFibreIso a).hom.app S) ≫
        (localizationEquivalence X H).counitIso.hom.app ((Over.pullback a).obj S) =
      (X.relocalizationInverseImageSliceIso a).hom.app
          ((localizationEquivalence X K).inverse.obj S) ≫
        (Over.pullback a).map ((localizationEquivalence X K).counitIso.hom.app S) := by
  have hslice : (X.relocalizationInverseImageSliceIso a).hom.app
        ((localizationEquivalence X K).inverse.obj S) =
      (localizationEquivalence X H).functor.map
          ((X.relocalizationMorphismOfTopoi a).inverseImage.map
            ((localizationEquivalence X K).unitIso.hom.app
              ((localizationEquivalence X K).inverse.obj S))) ≫
        (localizationEquivalence X H).functor.map
          ((X.relocalizationFibreIso a).hom.app
            ((localizationEquivalence X K).functor.obj
              ((localizationEquivalence X K).inverse.obj S))) ≫
        (localizationEquivalence X H).counitIso.hom.app
          ((Over.pullback a).obj
            ((localizationEquivalence X K).functor.obj
              ((localizationEquivalence X K).inverse.obj S))) :=
    rfl
  have hfibre := (X.relocalizationFibreIso a).hom.naturality
    ((localizationEquivalence X K).counitIso.hom.app S)
  have hcounit := (localizationEquivalence X H).counitIso.hom.naturality
    ((Over.pullback a).map ((localizationEquivalence X K).counitIso.hom.app S))
  have htriangle : (localizationEquivalence X K).unitIso.hom.app
        ((localizationEquivalence X K).inverse.obj S) ≫
      (localizationEquivalence X K).inverse.map
        ((localizationEquivalence X K).counitIso.hom.app S) = 𝟙 _ :=
    (localizationEquivalence X K).unit_inverse_comp S
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hcounit
  have hinner :
      (X.relocalizationMorphismOfTopoi a).inverseImage.map
          ((localizationEquivalence X K).unitIso.hom.app
            ((localizationEquivalence X K).inverse.obj S)) ≫
        (X.relocalizationFibreIso a).hom.app
            ((localizationEquivalence X K).functor.obj
              ((localizationEquivalence X K).inverse.obj S)) ≫
          (localizationEquivalence X H).inverse.map
            ((Over.pullback a).map
              ((localizationEquivalence X K).counitIso.hom.app S)) =
      (X.relocalizationFibreIso a).hom.app S := by
    refine Eq.trans (congrArg (fun z =>
      (X.relocalizationMorphismOfTopoi a).inverseImage.map
        ((localizationEquivalence X K).unitIso.hom.app
          ((localizationEquivalence X K).inverse.obj S)) ≫ z) hfibre.symm) ?_
    simp only [Functor.comp_map, Functor.id_obj, Functor.comp_obj]
    rw [← Functor.map_comp_assoc, htriangle]
    simp
  refine Eq.symm (Eq.trans (congrArg (fun z => z ≫ (Over.pullback a).map
      ((localizationEquivalence X K).counitIso.hom.app S)) hslice) ?_)
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z => (localizationEquivalence X H).functor.map
      ((X.relocalizationMorphismOfTopoi a).inverseImage.map
        ((localizationEquivalence X K).unitIso.hom.app
          ((localizationEquivalence X K).inverse.obj S))) ≫ z) (Category.assoc _ _ _)) ?_
  refine Eq.trans (congrArg (fun z => (localizationEquivalence X H).functor.map
      ((X.relocalizationMorphismOfTopoi a).inverseImage.map
        ((localizationEquivalence X K).unitIso.hom.app
          ((localizationEquivalence X K).inverse.obj S))) ≫
      (localizationEquivalence X H).functor.map
        ((X.relocalizationFibreIso a).hom.app
          ((localizationEquivalence X K).functor.obj
            ((localizationEquivalence X K).inverse.obj S))) ≫ z) hcounit.symm) ?_
  refine Eq.trans (congrArg (fun z => (localizationEquivalence X H).functor.map
      ((X.relocalizationMorphismOfTopoi a).inverseImage.map
        ((localizationEquivalence X K).unitIso.hom.app
          ((localizationEquivalence X K).inverse.obj S))) ≫ z)
    ((localizationEquivalence X H).functor.map_comp_assoc _ _ _).symm) ?_
  refine Eq.trans ((localizationEquivalence X H).functor.map_comp_assoc _ _ _).symm ?_
  exact congrArg (fun z => (localizationEquivalence X H).functor.map z ≫
    (localizationEquivalence X H).counitIso.hom.app ((Over.pullback a).obj S)) hinner

end AlgebraicGeometry.RingedTopos
