module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.Basic

/-!
# The canonical map from the degree-zero part of a graded module

Let `S` be a scheme, `𝒜` a graded `𝒪_S`-algebra and `ℳ` a graded `𝒜`-module (Situation 01NN),
and let `(d, f : T → S, L, ψ)` be a quadruple over a test scheme `T` as in Section 01NS. Tag
01O6 attaches to these data the `𝒪_T`-module

`ℳ̃_T = (f^*ℳ^{(d)} ⊗_{f^*𝒜^{(d)}} (⨁_{n ∈ ℤ} L^{⊗ n}))₀`.

This file constructs the canonical map `f^*ℳ_0 ⟶ ℳ̃_T`, which carries a local section `x` of
`f^*ℳ_0` to the pure tensor `x ⊗ 1` of degree zero. It is property (3) of Tag 01O7 read on the
chart of a quadruple: the map `π^*ℳ_0 ⟶ ℳ̃` of that property pulls back along the morphism
`h : T → Proj_S(𝒜)` classified by the quadruple to a map `f^*ℳ_0 ⟶ ℳ̃_T`, because `π ∘ h = f`
and `h^*ℳ̃ = ℳ̃_T`.
The map `π^*ℳ_0 ⟶ ℳ̃` on `Proj_S(𝒜)` itself is
`Stacks.RelativeProj.Situation.degreeZeroSheafMap`, in
`StacksFrontier/Topology/Sheaves/Modules/ModuleGlueing/RelativeProjModuleSheafDegreeZeroMap.lean`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.oneTensor`: the global unit `1` of
  `L^{⊗ 0} = 𝒪_T`, as a morphism from the tensor unit to the degree-`(-0)` piece of the Laurent
  algebra.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.unitSummand`: the identification
  `f^*ℳ_0 ⊗ 𝒪_T ⟶ f^*ℳ_{0 · d} ⊗ L^{⊗ (-0)}` of `f^*ℳ_0` with the degree-zero summand of the
  pure tensors.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.degreeZeroMap`: **the canonical map
  `f^*ℳ_0 ⟶ ℳ̃_T`**, `x ↦ x ⊗ 1`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting.degreeZeroMap_comp`: the canonical
  map is determined by the degree-zero pure tensors: composing it with the morphism out of
  `ℳ̃_T` that a balanced family of degreewise maps induces gives the degree-zero member of that
  family.

## Implementation notes

The degree-zero summand of the pure tensors is `f^*ℳ_{0 · d} ⊗ L^{⊗ (-0)}`. Neither factor is
syntactically the one wanted: the exponent `0 · d` of the module is only propositionally `0`,
and the exponent `-0` of the tensor power is only propositionally `0`, where the tensor power is
the structure sheaf, hence the unit of the tensor product of Tag 01CA. So `unitSummand` is the
tensor product of a reindexing of the module with the unit `1` of the Laurent algebra, and the
canonical map is the inverse of the unit constraint followed by it and by the degree-zero pure
tensors.

`unitSummand` is given the type `… ⟶ summand f M d L 0` rather than the unfolded type of its
body, so that the composite defining `degreeZeroMap` has `summand f M d L 0` as its middle
object on the nose; rewriting inside the composite is otherwise blocked by the need to unfold
`summand`, which `rw` does not do.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01O6](https://stacks.math.columbia.edu/tag/01O6)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting

variable {T S : Scheme.{u}} {f : T ⟶ S}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)}
  (M : SheafOfModules.GradedModule.{u, u, u} A) {d : ℤ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  (ψ : Twisting f A d L)

/-- The global unit `1` of the Laurent algebra of `L`, read in degree `-0`: a morphism from the
unit of the tensor product of Tag 01CA to `L^{⊗ (-0)}`. -/
def oneTensor : 𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) ⟶
    (laurent L).piece (-0) :=
  SheafOfModules.GradedAlgebra.oneHom (laurent L) ≫
    eqToHom (congrArg (laurent L).piece (neg_zero (G := ℤ)).symm)

/-- The identification of `f^*ℳ_0` with the degree-zero summand `f^*ℳ_{0 · d} ⊗ L^{⊗ (-0)}` of
the pure tensors: reindex the module from degree `0` to degree `0 · d`, and tensor with the
unit `1` of the Laurent algebra. -/
def unitSummand :
    (pullbackFunctor (ringedSpaceHom f)).obj (M.piece 0) ⊗
        𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) ⟶ summand f M d L 0 :=
  MonoidalCategoryStruct.tensorHom
    ((pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg M.piece (zero_mul d).symm)))
    (oneTensor (L := L))

/-- **Stacks Project, Tag 01O7, property (3), on the chart of a quadruple.** The canonical map
`f^*ℳ_0 ⟶ ℳ̃_T`, which carries a local section `x` of `f^*ℳ_0` to the pure tensor `x ⊗ 1` of
degree zero.

Property (3) of Tag 01O7 provides a map `π^*ℳ_0 ⟶ ℳ̃` on `Proj_S(𝒜)`; its pullback along the
morphism `h : T → Proj_S(𝒜)` classified by the quadruple is this map, since `π ∘ h = f` and
`h^*ℳ̃ = ℳ̃_T`. The map on `Proj_S(𝒜)` itself is
`Stacks.RelativeProj.Situation.degreeZeroSheafMap`. -/
def degreeZeroMap :
    (pullbackFunctor (ringedSpaceHom f)).obj (M.piece 0) ⟶ associatedSheaf M ψ :=
  (ρ_ ((pullbackFunctor (ringedSpaceHom f)).obj (M.piece 0))).inv ≫
    unitSummand M (L := L) ≫ pureTensor M ψ 0

/-- **The canonical map `f^*ℳ_0 ⟶ ℳ̃_T` is determined by the degree-zero pure tensors.**
Composing it with the morphism out of `ℳ̃_T` induced by a balanced family `b` of degreewise
maps gives the degree-zero member `b 0` of the family, read through the identification of
`f^*ℳ_0` with the degree-zero summand. -/
theorem degreeZeroMap_comp {N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    (b : ∀ n : ℤ, summand f M d L n ⟶ N) (h : associatedSheaf M ψ ⟶ N)
    (hh : ∀ n : ℤ, pureTensor M ψ n ≫ h = b n) :
    degreeZeroMap M ψ ≫ h =
      (ρ_ ((pullbackFunctor (ringedSpaceHom f)).obj (M.piece 0))).inv ≫
        unitSummand M (L := L) ≫ b 0 := by
  change ((ρ_ _).inv ≫ unitSummand M (L := L) ≫ pureTensor M ψ 0) ≫ h = _
  rw [Category.assoc, Category.assoc, hh 0]

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting

end
