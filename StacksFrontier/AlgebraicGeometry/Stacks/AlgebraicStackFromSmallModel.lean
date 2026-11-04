module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackSmallModel

/-!
# 1-morphisms out of the small model of an algebraic stack

`AlgebraicGeometry.Stack.AlgebraicStacks.smallModelHom` reads a based functor between two
algebraic stacks whose hom types are not small as a 1-morphism between their small models. When
the *target* is already an object of the 2-category of algebraic stacks of **Stacks 03YP** — the
stack of a scheme of the site, say, or any algebraic stack whose hom types lie in the universe of
the schemes — no shrinking is wanted there, and the 1-morphism out of the small model of the
source is the comparison out of it followed by the based functor.

This file is that construction, together with the one fact a consumer needs about it: it is an
equivalence of the underlying categories exactly when the based functor is, the comparison out of
the small model being one (`CategoryTheory.ShrinkHoms.inverse` is an equivalence). That is what
makes a notion invariant only under equivalence — smoothness of a 1-morphism to a fixed target in
the sense of **Stacks 075U**, through
`AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_of_isEquivalence_comp` — transportable along an
identification of an algebraic stack with large hom types.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.fromSmallModel`: a based functor from an algebraic
  stack to an object of the 2-category of Stacks 03YP, read as a 1-morphism out of the small
  model of the source.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.fromSmallModel_toFunctor`: its underlying functor is
  the comparison out of the small model followed by the based functor.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isEquivalence_fromSmallModel`: it is an equivalence as
  soon as the based functor is.

## References

* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : BasedCategory.{v, u + 1} (BigFppfOver B S hS)}

/-- The based functor underlying
`AlgebraicGeometry.Stack.AlgebraicStacks.fromSmallModel`: the comparison out of the small model of
the source followed by the given based functor. -/
noncomputable def AlgebraicStacks.fromSmallModelBasedFunctor
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳) (𝒵 : AlgebraicStacks.{u, w} B S hS)
    (f : 𝒳 ⥤ᵇ 𝒵.val.val) :
    (AlgebraicStacks.smallModel B S hS 𝒳 h𝒳).val.val ⥤ᵇ 𝒵.val.val where
  toFunctor := (AlgebraicStacks.smallModelEquivalenceOver B S hS 𝒳 h𝒳).inv.functor ⋙ f.toFunctor
  w := by
    rw [Functor.assoc, f.w]
    exact (AlgebraicStacks.smallModelEquivalenceOver B S hS 𝒳 h𝒳).inv.w

/-- **A based functor out of an algebraic stack into an object of the 2-category of algebraic
stacks of Stacks 03YP, read as a 1-morphism out of the small model of the source**: undo the
shrinking of the hom types of the source and apply the functor.

Compared with `AlgebraicGeometry.Stack.AlgebraicStacks.smallModelHom` the target is not shrunk,
because it already has its hom types in the universe of the schemes. -/
noncomputable def AlgebraicStacks.fromSmallModel (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳)
    (𝒵 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⥤ᵇ 𝒵.val.val) :
    AlgebraicStacks.smallModel B S hS 𝒳 h𝒳 ⟶ 𝒵 :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    (AlgebraicStacks.fromSmallModelBasedFunctor B S hS h𝒳 𝒵 f))

/-- The functor underlying `AlgebraicGeometry.Stack.AlgebraicStacks.fromSmallModel` is the
comparison out of the small model followed by the given based functor. -/
theorem AlgebraicStacks.fromSmallModel_toFunctor (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳)
    (𝒵 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⥤ᵇ 𝒵.val.val) :
    CatFiberedInGroupoids.homFunctor (AlgebraicStacks.fromSmallModel B S hS h𝒳 𝒵 f).hom =
      (AlgebraicStacks.smallModelEquivalenceOver B S hS 𝒳 h𝒳).inv.functor ⋙ f.toFunctor :=
  rfl

/-- **The 1-morphism out of the small model is an equivalence as soon as the based functor is.**
The comparison out of the small model is an equivalence — it is
`CategoryTheory.ShrinkHoms.inverse` — so the composite is one whenever the second factor is. -/
theorem AlgebraicStacks.isEquivalence_fromSmallModel (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳)
    (𝒵 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⥤ᵇ 𝒵.val.val) (hf : f.toFunctor.IsEquivalence) :
    Functor.IsEquivalence
      (CatFiberedInGroupoids.homFunctor (AlgebraicStacks.fromSmallModel B S hS h𝒳 𝒵 f).hom) := by
  rw [AlgebraicStacks.fromSmallModel_toFunctor]
  have := locallySmall_of_isAlgebraicStack B S hS h𝒳
  have : (AlgebraicStacks.smallModelEquivalenceOver B S hS 𝒳 h𝒳).inv.functor.IsEquivalence :=
    inferInstanceAs (ShrinkHoms.inverse.{u} 𝒳.obj).IsEquivalence
  infer_instance

end AlgebraicGeometry.Stack

end
