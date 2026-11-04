module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.IsomorphismApproximationComplete
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedDeformationFiniteDimensional
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedDiagonal
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesForget
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackRepresentable
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesOverSpaceStack
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFibreCountable
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFormalEffective
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedLimitPreservingProof
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOpenVersality
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedRSStar
public import StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterionFiniteDimensionalDeformation
public import StacksFrontier.RingTheory.GRing.EssFiniteType
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesArtinInputs
import StacksCore.Tactic.StacksAttribute

/-!
# The stack of polarized proper schemes is algebraic (Stacks 0D4X)

Let `𝒫olarized` be the stack over `(Sch/Spec ℤ)_{fppf}` of Situation 0D1M, whose objects are
proper, flat, finitely presented morphisms `X ⟶ S` together with an invertible `𝒪_X`-module
`ℒ` ample on `X/S`. Then `𝒫olarized` is an algebraic stack, and so, for every algebraic space `A`
over `Spec ℤ`, is the stack `A-Polarized` of Remark 0D1N, of triples `(X ⟶ S, ℒ, h : S ⟶ A)`.

The proof is the source's. The absolute clause is Artin's criterion, Stacks 07Y4
(`AlgebraicGeometry.Stack.isAlgebraicStack_of_artinAxioms`), over the locally Noetherian base
`Spec ℤ`, whose local rings are G-rings (Stacks 07PX); its hypotheses are

* the diagonal is representable by algebraic spaces: Stacks 0D42,
  `AlgebraicGeometry.hasRepresentableDiagonal_polarizedStackUnconditional`;
* axiom [-1], the set-theoretic condition:
  `AlgebraicGeometry.isSizeBounded_polarizedStackUnconditional`;
* axiom [0], the stack condition: Stacks 0D40, here the fppf stack condition
  `AlgebraicGeometry.polarizedStackUnconditional_isStack`, which implies the étale
  one;
* axiom [1], limit preservation: Stacks 0D43,
  `AlgebraicGeometry.isLimitPreservingPolarizedUnconditional`;
* axiom [2], condition (RS): condition (RS*) of Stacks 0D44,
  `AlgebraicGeometry.satisfiesRSStar_polarizedSliceProjection`, through the remark after
  Stacks 07Y8;
* axiom [3], finite dimensionality of the tangent spaces: Stacks 0D4S (1), in the namespace
  `AlgebraicGeometry.PolarizedDeformation`,
  `isFiniteDimensionalDeformationCategory_predeformationCategory`;
* effectivity of formal objects: Stacks 0D4U,
  `AlgebraicGeometry.polarizedFormalObject_isEffective`;
* openness of versality: Stacks 0D4V,
  `AlgebraicGeometry.isOpenVersality_polarizedStack_specULiftZ`.

The relative clause follows from the absolute one by the description of `A-Polarized` as a
2-fibre product in Remark 0D1N and the fact that algebraic stacks have 2-fibre products
(Stacks 04T2): that is
`AlgebraicGeometry.PolarizedFamilyOver.isAlgebraicStack_siteProjection_of_isAlgebraicStack`.

## Main results

* `AlgebraicGeometry.isAlgebraicStack_polarizedStack`: **Stacks 0D4X**, both clauses.

## Implementation notes

The base `Spec ℤ` is `AlgebraicGeometry.integerBase`, the spectrum of the integers raised to the
universe of the site; it lies in every big fppf site
(`AlgebraicGeometry.BigFppfSite.contains_integerBase`) and is terminal there
(`AlgebraicGeometry.isTerminal_obj_specULiftZ`), so the big fppf site over it is the source's
`Sch_{fppf}`. The universe of the stack condition in the conclusion is free.

## References

* [Stacks Project, Tag 0D4X](https://stacks.math.columbia.edu/tag/0D4X)
* [Stacks Project, Tag 07Y4](https://stacks.math.columbia.edu/tag/07Y4)
* [Stacks Project, Tag 0D1N](https://stacks.math.columbia.edu/tag/0D1N)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

private instance : IsLocallyNoetherian integerBase.{u} :=
  isLocallyNoetherian_Spec.mpr (isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm)

variable (B : BigFppfSite.{u})

/-- **Stacks 0D4X.** The stack `𝒫olarized` of polarized proper schemes (Situation 0D1M) over the
big fppf site of `Spec ℤ` is an algebraic stack. In fact, for every algebraic space `A` over
`Spec ℤ`, the stack `A-Polarized` of Remark 0D1N, of polarized proper schemes `(X ⟶ S, ℒ)`
together with a morphism `S ⟶ A`, is an algebraic stack. -/
@[stacks 0D4X]
theorem isAlgebraicStack_polarizedStack :
    Stack.IsAlgebraicStack.{u, w} B integerBase B.contains_integerBase
        (polarizedStackUnconditional B B.contains_integerBase
          (isTerminal_obj_specULiftZ B B.contains_integerBase)).val ∧
      ∀ (A : (BigFppfOver B integerBase B.contains_integerBase)ᵒᵖ ⥤ Type u),
        IsAlgebraicSpace B integerBase B.contains_integerBase A →
        Stack.IsAlgebraicStack.{u, w} B integerBase B.contains_integerBase
          (BasedCategory.ofFunctor
            (AlgebraicGeometry.PolarizedFamilyOver.projection B integerBase
              B.contains_integerBase A)) := by
  have habs : Stack.IsAlgebraicStack.{u, w} B integerBase B.contains_integerBase
      (polarizedStackUnconditional B B.contains_integerBase
        (isTerminal_obj_specULiftZ B B.contains_integerBase)).val :=
    Stack.isAlgebraicStack_of_artinAxioms.{u, u, u + 1, w} B integerBase B.contains_integerBase
      (polarizedStackUnconditional B B.contains_integerBase
        (isTerminal_obj_specULiftZ B B.contains_integerBase))
      (hasRepresentableDiagonal_polarizedStackUnconditional B B.contains_integerBase
        (isTerminal_obj_specULiftZ B B.contains_integerBase))
      (AlgebraicGeometry.isSizeBounded_polarizedStackUnconditional B B.contains_integerBase)
      (((polarizedStackUnconditional_isStack B
          B.contains_integerBase).isStackInGroupoids
          (polarizedStackUnconditional B B.contains_integerBase
            (isTerminal_obj_specULiftZ B B.contains_integerBase)).property).of_le
        (fun _ _ hS => Stack.etaleTopology_le_topology B _ hS))
      (isLimitPreservingPolarizedUnconditional B B.contains_integerBase
        (isTerminal_obj_specULiftZ B B.contains_integerBase))
      (Deformation.Artin.satisfiesRS_of_satisfiesRSStar B integerBase B.contains_integerBase _ _
        (satisfiesRSStar_polarizedSliceProjection B B.contains_integerBase
          (isTerminal_obj_specULiftZ B B.contains_integerBase)))
      (Stack.hasFiniteDimensionalTangentSpaces_of_isFiniteDimensionalDeformationCategory B
        integerBase B.contains_integerBase _ fun _ _ _ _ _ iΛ x₀ hx₀ hlft hqc =>
          PolarizedDeformation.isFiniteDimensionalDeformationCategory_predeformationCategory B
            B.contains_integerBase (isTerminal_obj_specULiftZ B B.contains_integerBase) iΛ x₀ hx₀
            ⟨hlft, hqc⟩)
      (polarizedFormalObject_isEffective B B.contains_integerBase)
      (isOpenVersality_polarizedStack_specULiftZ B B.contains_integerBase)
      (fun s _ => C1590Private.isGRing_stalk_integerBase s)
  exact ⟨habs, fun A hA =>
    PolarizedFamilyOver.isAlgebraicStack_siteProjection_of_isAlgebraicStack
      (isTerminal_obj_specULiftZ B B.contains_integerBase) hA habs⟩

end AlgebraicGeometry

end
