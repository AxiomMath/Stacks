module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AffineSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.LimitSections

namespace Stacks.Algebraization.C1573
end Stacks.Algebraization.C1573

/-!
# The projections onto the terms of a completion, on the sections over an affine open

The kernel and the image of the projection `F ⟶ F / Iⁿ⁺¹F` onto the `n`-th term of the completion
of a coherent module, read through `Stacks.Algebraization.affineSectionFunctor`, the evaluation
at an affine open valued in modules over the functions on that open.  These are
`Stacks.Algebraization.completionProjection_app_ker` and
`Stacks.Algebraization.completionProjection_app_surjective` in that spelling.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Algebraization

open _root_.Stacks.Algebraization.C1573
/-- The projection onto the `n`-th term of the completion is surjective on the sections over an
affine open. -/
theorem C1573.surjective_affineSectionFunctor_map_completionProjection (X : Scheme.{u})
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ)
    (U : X.affineOpens) :
    Function.Surjective ((affineSectionFunctor U).map (completionProjection X I F n)) :=
  completionProjection_app_surjective X I F n U

/-- The kernel of the projection onto the `n`-th term of the completion on the sections over an
affine open `U` is `I(U)ⁿ⁺¹` times the sections. -/
theorem C1573.ker_affineSectionFunctor_map_completionProjection (X : Scheme.{u})
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ)
    (U : X.affineOpens) :
    LinearMap.ker ((affineSectionFunctor U).map (completionProjection X I F n)).hom =
      I.ideal U ^ (n + 1) • (⊤ : Submodule Γ(X, U.1) ((affineSectionFunctor U).obj F.obj)) := by
  ext x
  exact SetLike.ext_iff.mp (completionProjection_app_ker X I F n U) x

end Stacks.Algebraization

end
