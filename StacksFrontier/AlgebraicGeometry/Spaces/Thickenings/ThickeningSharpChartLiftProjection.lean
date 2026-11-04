module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartLiftIdentify
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapComp

/-!
# The composite chart reading of a solution and of the comorphism it solves for

Let `Z ⊆ X` be a thickening of algebraic spaces over a scheme `S` with inclusion `i : Z ⟶ X`, let
`c, c' : X ⟶ W` be two morphisms agreeing on `Z`, and let
`a : 𝒪_W ⟶ (i ≫ c)_*(i^{-1}𝒪_X)` be a solution of the lifting problem whose reduction is the
comorphism of `i ≫ c`. Over an affine étale chart `Q` of `W` and an index `j` of `X` above
`X ×_W Q` the solution has a morphism of charts `ψ : P ⟶ Q`, `P = j.right.unop`, and suppose that
`ψ` is a chart morphism of `c'`.

Then `a` and the comorphism of `c'` read through the thickening at the composite index `i ≫ c`
agree at every index of the form

`StructuredArrow.mk ((chartBaseChangeComp i c Q j).op ≫ k.hom)`

for an index `k` of `Z` above `Z ×_X P`.

## Main results

* `AlgebraicGeometry.Space.directImageChartProjection_comp_eq_of_thickeningLiftChartSiteHom`:
  the composite chart readings of `a` and of the comorphism of `c'` agree.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), part (3), iterated
  direct images.
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3), diagrams of charts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-- The composite chart readings of a solution of the lifting problem and of the comorphism of a
morphism agreeing with `c` on the thickening agree, at every index of `Z` above `Z ×_X P` composed
with an index `j` of `X` above `X ×_W Q`, as soon as the morphism of charts the solution attaches
over `Q` and `j` is a chart morphism of `c'`. -/
theorem directImageChartProjection_comp_eq_of_thickeningLiftChartSiteHom
    (hZ : IsThickening B S hS X Z.1) (c c' : X ⟶ W)
    (hcc : subspaceInclusion B S hS X Z ≫ c' = subspaceInclusion B S hS X Z ≫ c)
    (a : structureRingSheaf B S hS W ⟶ thickeningLiftRingSheaf B S hS Z c)
    (hred : a ≫ thickeningLiftReduction B S hS Z c =
      structureSharp B S hS (subspaceInclusion B S hS X Z ≫ c))
    (Q : SmallEtale B S hS W.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj Q))]
    (j : StructuredArrow (op (chartBaseChange B S hS c Q)) (comparisonFunctor B S hS X).op)
    (ψ : (SmallEtale.toOver B S hS X.1).obj j.right.unop ⟶
      (SmallEtale.toOver B S hS W.1).obj Q)
    (hψ : (BigFppfOver.toScheme B S hS).map ψ = thickeningLiftChartHom B S hS Z hZ c a Q j)
    (hψ' : j.right.unop.1.hom ≫ c'.hom = yoneda.map ψ ≫ Q.1.hom)
    (k : StructuredArrow
      (op (chartBaseChange B S hS (subspaceInclusion B S hS X Z) j.right.unop))
      (comparisonFunctor B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).op)
    (b : ToType ((structureRingSheaf B S hS W).obj.obj (op Q))) :
    (directImageChartProjection B S hS (subspaceInclusion B S hS X Z ≫ c) Q
          (StructuredArrow.mk ((chartBaseChangeComp B S hS
            (subspaceInclusion B S hS X Z) c Q j).op ≫ k.hom))).app
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).obj
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
        ((structureSharpThroughThickeningAt B S hS Z c'
          (subspaceInclusion B S hS X Z ≫ c) hcc).hom.app (op Q) b) =
      (directImageChartProjection B S hS (subspaceInclusion B S hS X Z ≫ c) Q
          (StructuredArrow.mk ((chartBaseChangeComp B S hS
            (subspaceInclusion B S hS X Z) c Q j).op ≫ k.hom))).app
        ((sheafCompose (SmallEtale.topology B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
          (CategoryTheory.forget RingCat.{u})).obj
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
        (a.hom.app (op Q) b) := by
  have hab : (Z.1.preimage j.right.unop.1.hom).ι ≫
        yoneda.map (chartBaseChangeMap B S hS c Q j) =
      (Z.1.preimage j.right.unop.1.hom).ι ≫ yoneda.map ψ :=
    (comp_preimage_ι_eq_chartBaseChangeMap B S hS Z hZ c a hred Q j ψ hψ).symm
  have hθ : chartBaseChangeMap B S hS (subspaceInclusion B S hS X Z ≫ c) Q
        (StructuredArrow.mk ((chartBaseChangeComp B S hS
          (subspaceInclusion B S hS X Z) c Q j).op ≫ k.hom)) =
      chartBaseChangeMap B S hS (subspaceInclusion B S hS X Z) j.right.unop k ≫ ψ :=
    (chartBaseChangeMap_comp_chart B S hS (subspaceInclusion B S hS X Z) c Q j k).trans
      (comp_chartBaseChangeMap_eq_of_thickeningRestriction_eq B S hS Z j.right.unop Q
        (chartBaseChangeMap B S hS c Q j) ψ hab k)
  have happ : thickeningLiftChartAppTop B S hS Z hZ c a Q j =
      chartPullbackRingHom B S hS c' Q
        (indexOfChartDiagram B S hS c' (⟨j.right.unop, Q, ψ, hψ'⟩ :
          ChartDiagram B S hS X.1 W.1 c'.hom)) :=
    congrArg (·.hom) ((thickeningLiftChartHom_appTop B S hS Z hZ c a Q j).symm.trans
      (congrArg (·.appTop) (hψ.symm.trans (congrArg (BigFppfOver.toScheme B S hS).map
        (chartBaseChangeMap_indexOfChartDiagram B S hS c' (⟨j.right.unop, Q, ψ, hψ'⟩ :
          ChartDiagram B S hS X.1 W.1 c'.hom)).symm))))
  refine Eq.trans (directImageChartProjection_structureSharpThroughThickeningAt_common
    B S hS Z c' (subspaceInclusion B S hS X Z ≫ c) hcc Q j.right.unop ψ hψ' k
    ((chartBaseChangeComp B S hS (subspaceInclusion B S hS X Z) c Q j).op ≫ k.hom) hθ b) ?_
  refine Eq.trans ?_ (directImageChartProjection_pushforwardRingSheafCompInv B S hS
    (subspaceInclusion B S hS X Z) c Q j k
    (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))
    (a.hom.app (op Q) b))
  refine congrArg
    ((directImageChartProjection B S hS (subspaceInclusion B S hS X Z) j.right.unop k).app
      ((sheafCompose (SmallEtale.topology B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS).1)
        (CategoryTheory.forget RingCat.{u})).obj
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))) ?_
  refine Eq.trans ?_ (thickeningRingUnit_thickeningLiftChartAppTop B S hS Z hZ c a Q j b)
  exact congrArg ((thickeningRingUnit B S hS Z).hom.app j.right)
    (DFunLike.congr_fun happ b).symm

end AlgebraicGeometry.Space

end
