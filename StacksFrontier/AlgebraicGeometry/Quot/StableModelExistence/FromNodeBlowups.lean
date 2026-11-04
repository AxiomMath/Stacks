module

public import StacksFrontier.AlgebraicGeometry.Quot.StableModelExistence.Assembly
public import StacksFrontier.AlgebraicGeometry.Quot.StableModelExistence.StableContractionMorphism

/-!
# The existence half of Stacks 0E97, from the special fibres of the node blowups

`AlgebraicGeometry.existsIsoOfStableModels_of_input2_input5` proves the existence half of Stacks
0E97 for scheme models from two inputs. The second, `Input5`, the contraction of the minimal model
onto a stable model with its morphism exposed, holds by
`Stacks.Models.exists_stableContraction_of_isMinimalModel`. So the existence half follows from
`Input2` alone: the property of the special fibres of the resolution of an at-worst-nodal model by
blowing up its nodes.

## Main results

* `Stacks.Models.StableModelExistence.input5`: `Input5` holds.
* `AlgebraicGeometry.existsIsoOfStableModels_of_input2`: the existence half of Stacks 0E97 follows
  from `Input2`.
-/


@[expose] public noncomputable section

universe u

namespace Stacks.Models.StableModelExistence

/-- `Input5` holds: `Stacks.Models.exists_stableContraction_of_isMinimalModel`. -/
theorem input5 : Input5.{u} := by
  intro R K _ _ _ _ _ _ C Y c _ _ hc _ hg p e hmin hnod
  obtain ⟨Z, pZ, eZ, cZ, hcZ, h₁, h₂, h₃, h₄, -⟩ :=
    Stacks.Models.exists_stableContraction_of_isMinimalModel R K c hc hg p e hmin hnod
  exact ⟨Z, pZ, eZ, cZ, hcZ, h₁, h₂, h₃, h₄⟩

end Stacks.Models.StableModelExistence

open Stacks.Models.StableModelExistence in
/-- **The existence half of Stacks 0E97, from the special fibres of the node blowups.**
`ExistsIsoOfStableModels` follows from `Input2`: the property (*) of the special fibre of the
resolution of an at-worst-nodal model by blowing up nodes. -/
theorem AlgebraicGeometry.existsIsoOfStableModels_of_input2 (B : BigFppfSite.{u})
    (hZ : B.Contains integerBase) (g : ℕ) (h2 : Input2.{u}) : ExistsIsoOfStableModels B hZ g :=
  existsIsoOfStableModels_of_input2_input5 B hZ g h2 input5

end
