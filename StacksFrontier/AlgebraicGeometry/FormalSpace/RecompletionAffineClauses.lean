module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Types
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionFormalSpace
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation

/-!
# Recompletion of an affine formal algebraic space: the affine and McQuillan clauses

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an *affine* formal algebraic
space over `S`, let `i : X_red ⟶ X` be a reduction of `X` and let `T ⊆ |X_red|` be closed.
**Stacks 0GVV** records five properties of the completion `X_{/T}` of `X` along `T`:

1. `X_{/T}` is an affine formal algebraic space;
2. if `X` is McQuillan, so is `X_{/T}`;
3. if `|X_red| \ T` is quasi-compact and `X` is countably indexed, so is `X_{/T}`;
4. if `|X_red| \ T` is quasi-compact and `X` is adic\*, so is `X_{/T}`;
5. if `X` is Noetherian, so is `X_{/T}`.

This file carries clause (1). Clause (2) is
`AlgebraicGeometry.FormalSpace.hasSomeSurjectivePresentation_completionAlong'`, in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionAffineClausesVariants`. Clauses (3), (4)
and (5) are in `StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionAffineClausesTypes`, which
needs the ring-theoretic machinery of Stacks 0GXX.

## Main results

* `AlgebraicGeometry.FormalSpace.completionOfAffineIsAffine_of_cited`: clause (1) under the
  hypotheses below, a corollary of `AlgebraicGeometry.FormalSpace.completionOfAffineIsAffine`
  (**clause (1)**), in the ambient spelling
  `AlgebraicGeometry.FormalSpace.CompletionOfAffineIsAffine` — *every* completion of *every*
  affine formal algebraic space over `S` along *every* closed set of its points is affine
  formal. This is the form Stacks 0GVR
  (`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_completionAlong`) carries as its
  hypothesis `haff`, and
  `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_completionAlong_of_cited` is that
  theorem with `haff` discharged by this one.

## What is assumed

Clause (1) of Stacks 0GVV is Stacks 0GVQ, which is already proved in this library as
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_completionAlong'`, in the spelling
`X_{/T}` for a subset `T` of the points of a reduction. What is added here is the *ambient*
spelling, quantified over the space and over the closed subset of its own points, which is
what consumers of clause (1) in this library ask for and which needs no reduction. It is
assembled out of
`AlgebraicGeometry.FormalSpace.exists_affinePresentation_completionSheafULift`, the geometric
half of Stacks 0GVQ, and therefore carries exactly that theorem's two general cited inputs:

* `haiy`: **Stacks 0AIY** at the affine stages. The library proves 0AIY as
  `AlgebraicGeometry.FormalSpace.hasSomeSurjectivePresentation_completionSheaf`, for the
  completion `AlgebraicGeometry.Space.completionSheaf` formed inside presheaves of `Type u`;
  the missing step is its identification with
  `AlgebraicGeometry.Space.completionSheafULift` of the represented fppf sheaf, in
  `Type (u + 1)`.
* `hcolim`: completion commutes with directed colimits of fppf sheaves. This is the step the
  source writes as `X_{/T} = colim (X_λ)_{/T}`.

Both are quantified over their own data and neither mentions any particular space or subset.
Alongside them, `hset` is the set-theoretic condition of Stacks 0AIS on the completions,
carried in exactly the place and for exactly the reason that
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_colimit` (Stacks 0GVM) carries it.

For clause (2) this file keeps the general cited input `hspf`, namely
`AlgebraicGeometry.FormalSpace.CompletionOfMcQuillanIsSpf`: the completion of a McQuillan
affine formal algebraic space along a closed subset of its reduction is the formal spectrum of
a weakly admissible topological ring. This is the source's own step, which writes `X = Spf(A)`
and observes that `X_{/T} ⟶ X ⟶ Spec(A)` satisfies condition (2) of Stacks 0AIC. From it the
conclusion is not immediate: being presented by a weakly admissible ring is condition (1) of
Stacks 0AIC and McQuillan is condition (4), and the implication between them is
`AlgebraicGeometry.FormalSpace.hasAllSurjectivePresentations_of_weakIdealColimitPresentation`
(Stacks 0AIC, (1) ⇒ (5)) followed by
`AlgebraicGeometry.FormalSpace.HasAllSurjectivePresentations.hasSomeSurjectivePresentation`
(Stacks 0AIC, (5) ⇒ (4)).

The reduction is supplied as data satisfying `AlgebraicGeometry.FormalSpace.IsReduction`
rather than constructed, since Stacks 0AIN — the existence of a reduction — is not available
in this library; this is how Stacks 0GVQ, Stacks 0GVR and Stacks 0GVT are stated here as well.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AIY](https://stacks.math.columbia.edu/tag/0AIY)
* [Stacks Project, Tag 0GVQ](https://stacks.math.columbia.edu/tag/0GVQ)
* [Stacks Project, Tag 0GVR](https://stacks.math.columbia.edu/tag/0GVR)
* [Stacks Project, Tag 0GVV](https://stacks.math.columbia.edu/tag/0GVV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Clause (1): the completion of an affine formal algebraic space is affine formal -/

/-- **Clause (1) of Stacks 0GVV**, in the ambient spelling
`AlgebraicGeometry.FormalSpace.CompletionOfAffineIsAffine`: the completion of an affine formal
algebraic space over `S` along a closed set of its points is again an affine formal algebraic
space, for every such space and every such set at once. Through the bijection
`|Y_red| = |Y|` given by the inclusion of a reduction this is the source's statement about a
closed subset of `|Y_red|`, and no reduction enters the statement.

The two general cited inputs `haiy` (Stacks 0AIY at the affine stages) and `hcolim`
(completion commutes with directed colimits) and the Stacks 0AIS condition `hset` are
hypotheses; see the section "What is assumed" of this file. None of them is used: this is
`AlgebraicGeometry.FormalSpace.completionOfAffineIsAffine` (clause (1) of Stacks 0GVV), which
assumes nothing. -/
theorem completionOfAffineIsAffine_of_cited
    (haiy : ∀ (V : BigAffineFppf B S hS)
      (V' : Set (Space.pointsULift.{u + 1} B S hS (affineStageSheaf B S hS V).obj)),
      @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS
        (affineStageSheaf B S hS V).obj) V' →
      IsAffineFormalAlgebraicSpace B S hS
        (Space.completionSheafULift B S hS (affineStageSheaf B S hS V) V'))
    (hcolim : ∀ (K : Type (u + 1)) (pre : Preorder K), letI := pre
      Nonempty K → IsDirected K (· ≤ ·) →
      ∀ (F : K ⥤ FppfSheaf B S hS) (Z : FppfSheaf B S hS) (eZ : Z ≅ colimit F)
        (V : Set (Space.pointsULift.{u + 1} B S hS Z.obj)),
        Nonempty (Space.completionSheafULift B S hS Z V ≅
          colimit (completionColimitDiagram B S hS F Z eZ V)))
    (hset : ∀ (Y : FppfSheaf B S hS)
      (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj)),
      SatisfiesSetTheoreticCondition B S hS (Space.completionSheafULift B S hS Y W)) :
    CompletionOfAffineIsAffine B S hS :=
  completionOfAffineIsAffine B S hS

/-- **Stacks 0GVR** with its hypothesis `haff` discharged: the completion of a formal
algebraic space `X` over `S` along a closed subset `T` of the points of a reduction is a formal
algebraic space, granted only the general cited inputs of clause (1) of Stacks 0GVV.

This is `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_completionAlong` (Stacks 0GVR)
with its affine-case hypothesis supplied by
`AlgebraicGeometry.FormalSpace.completionOfAffineIsAffine_of_cited`. The tag registration for
Stacks 0GVR stays on that theorem. -/
theorem isFormalAlgebraicSpace_completionAlong_of_cited {X Xred : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) {i : Xred ⟶ X}
    (hi : IsReduction B S hS X Xred i)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS X.obj)
      (Space.pointsMapULift.{u + 1} B S hS Xred.obj i.hom '' T))
    (haiy : ∀ (V : BigAffineFppf B S hS)
      (V' : Set (Space.pointsULift.{u + 1} B S hS (affineStageSheaf B S hS V).obj)),
      @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS
        (affineStageSheaf B S hS V).obj) V' →
      IsAffineFormalAlgebraicSpace B S hS
        (Space.completionSheafULift B S hS (affineStageSheaf B S hS V) V'))
    (hcolim : ∀ (K : Type (u + 1)) (pre : Preorder K), letI := pre
      Nonempty K → IsDirected K (· ≤ ·) →
      ∀ (F : K ⥤ FppfSheaf B S hS) (Z : FppfSheaf B S hS) (eZ : Z ≅ colimit F)
        (V : Set (Space.pointsULift.{u + 1} B S hS Z.obj)),
        Nonempty (Space.completionSheafULift B S hS Z V ≅
          colimit (completionColimitDiagram B S hS F Z eZ V)))
    (hsetAll : ∀ (Y : FppfSheaf B S hS)
      (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj)),
      SatisfiesSetTheoreticCondition B S hS (Space.completionSheafULift B S hS Y W))
    (hset : SatisfiesSetTheoreticCondition B S hS (completionAlong i T)) :
    IsFormalAlgebraicSpace B S hS (completionAlong i T) :=
  isFormalAlgebraicSpace_completionAlong B S hS hX hi T hT
    (completionOfAffineIsAffine_of_cited B S hS haiy hcolim hsetAll) hset

/-! ### Clause (2): the completion of a McQuillan space is McQuillan -/

/-- The step of the source's proof of clause (2) of Stacks 0GVV: the completion of a McQuillan
affine formal algebraic space over `S` along a closed subset of the points of a reduction is
the formal spectrum of a weakly admissible topological ring, that is satisfies condition (1)
of Stacks 0AIC. The source obtains it by writing `Y = Spf(A)` and checking that
`Y_{/V} ⟶ Y ⟶ Spec(A)` satisfies condition (2) of Stacks 0AIC. It is quantified over its own
space, reduction and subset. -/
abbrev CompletionOfMcQuillanIsSpf : Prop :=
  ∀ (Y Yred : FppfSheaf B S hS) (j : Yred ⟶ Y), IsReduction B S hS Y Yred j →
    HasSomeSurjectivePresentation B S hS Y →
    ∀ V : Set (Space.pointsULift.{u + 1} B S hS Yred.obj),
      @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Yred.obj) V →
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
        (_ : IsLinearTopology A A), IsPresentingRing B S hS A (completionAlong j V)

end AlgebraicGeometry.FormalSpace

end
