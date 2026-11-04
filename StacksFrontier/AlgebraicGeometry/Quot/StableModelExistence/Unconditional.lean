module

public import StacksFrontier.AlgebraicGeometry.Quot.StableModelExistence.FromNodeBlowups
public import StacksFrontier.AlgebraicGeometry.Quot.StableModelExistence.NodalBlowupInput2

/-!
# The existence half of Stacks 0E97 for scheme models

Let `R` be a discrete valuation ring with fraction field `K` and `C` a smooth curve over `K`. Two
models of `C` over `R` which are stable families of curves of genus `g` are isomorphic as models
(`AlgebraicGeometry.existsIsoOfStableModels`). This is `AlgebraicGeometry.ExistsIsoOfStableModels`,
the existence half of Stacks 0E97, proved with no further input: it is
`AlgebraicGeometry.existsIsoOfStableModels_of_input2` with `Input2` supplied by
`Stacks.Models.StableModelExistence.input2`.
-/

@[expose] public noncomputable section

universe u

/-- **The existence half of Stacks 0E97, for schemes.** Let `R` be a discrete valuation ring with
fraction field `K` and `C` a smooth curve over `K`. If `X` and `X'` are models of `C` which are
stable families of curves of genus `g` over `R`, there is an isomorphism of models `X ≅ X'`. -/
theorem AlgebraicGeometry.existsIsoOfStableModels (B : BigFppfSite.{u})
    (hZ : B.Contains integerBase) (g : ℕ) : ExistsIsoOfStableModels B hZ g :=
  existsIsoOfStableModels_of_input2 B hZ g Stacks.Models.StableModelExistence.input2

end
