module

public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.HomologicalPrecompose
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.LeftDerived
public import StacksFrontier.CategoryTheory.Abelian.Projective.LeftDerivedComp

/-! # The comparison `Lₙ G ∘ W ⟶ Lₙ (W ⋙ G)` is a morphism of δ-functors

`StacksFrontier/CategoryTheory/Abelian/Projective/LeftDerivedComp.lean` constructs, for an exact
additive `W : C ⥤ D` and an additive `G : D ⥤ T`, the comparison
`Lₙ G (W X) ⟶ Lₙ (W ⋙ G) (X)` and proves that it is natural in `X` and compatible with the
connecting morphisms. This file packages those two facts as a single morphism of homological
δ-functors

`(Lₙ G).precomp W ⟶ Lₙ (W ⋙ G)`,

which is the form in which the universality of a δ-functor consumes it: a morphism into a
universal homological δ-functor is determined by its degree-zero component, and that is only
applicable to a morphism of δ-functors, not to a mere family of natural transformations.

## Main definitions

* `CategoryTheory.Functor.leftDerivedCompDeltaHom`.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 08PH](https://stacks.math.columbia.edu/tag/08PH)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe v u v₂ u₂ vT uT

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [EnoughProjectives D]
  {T : Type uT} [Category.{vT} T] [Abelian T]
  (W : C ⥤ D) [W.Additive] [PreservesFiniteLimits W] [PreservesFiniteColimits W]
  (G : D ⥤ T) [G.Additive]

/-- **The comparison `Lₙ G ∘ W ⟶ Lₙ (W ⋙ G)` as a morphism of homological δ-functors.** The
components are `CategoryTheory.Functor.leftDerivedComp` and the compatibility with the connecting
morphisms is `CategoryTheory.Functor.leftDerivedCompApp_δ`. -/
def leftDerivedCompDeltaHom :
    G.leftDerivedHomologicalDeltaFunctor.precomp W ⟶
      (W ⋙ G).leftDerivedHomologicalDeltaFunctor where
  app n := leftDerivedComp W G n
  comm hS n := leftDerivedCompApp_δ W G hS n

/-- The components of `CategoryTheory.Functor.leftDerivedCompDeltaHom`. -/
@[simp]
lemma leftDerivedCompDeltaHom_app (n : ℕ) :
    (leftDerivedCompDeltaHom W G).app n = leftDerivedComp W G n :=
  rfl

end CategoryTheory.Functor

end
