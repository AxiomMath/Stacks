module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseRingLinear
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyOverBaseFunctor

/-!
# Global sections over a base ring is a linear functor

Let `A` be a commutative ring, let `f : X ⟶ Spec A` be a morphism of schemes and let
`Stacks.LocalCohomology.sectionsOverBase A f` be global sections on `X` with scalars restricted
to `A`. Both its source and its target are `A`-linear categories — the source by
`AlgebraicGeometry.Scheme.linearOfRingHom` applied to `Stacks.LocalCohomology.baseScalars`, the
target because `A` is commutative — and the functor is `A`-linear: multiplication by `a ∈ A` on a
sheaf of modules becomes multiplication by `a` on its global sections.

## Main results

* `Stacks.LocalCohomology.sectionsOverBase_linear` — global sections over the base is an
  `A`-linear functor.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace Stacks.LocalCohomology

variable (A : Type u) [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **Global sections with scalars restricted to the base is an `A`-linear functor.** -/
theorem sectionsOverBase_linear :
    letI := Scheme.linearOfRingHom.{u, max u v} X A (baseScalars A f)
    Functor.Linear A (sectionsOverBase.{u, v} A f) := by
  let _ := Scheme.linearOfRingHom.{u, max u v} X A (baseScalars A f)
  refine ⟨fun {M N} g a => ?_⟩
  ext x
  exact Scheme.smul_val_app_top X A (baseScalars A f) a g x

end Stacks.LocalCohomology

end
