module

public import StacksFrontier.AlgebraicGeometry.Stacks.DescendingStacksAlongLimitAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.SmoothQuotientStackModel
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceUniverses
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.IsomorphismSheafAlgebraic
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.PullbackFiberComp
public import StacksFrontier.CategoryTheory.FiberedCategory.ShrinkHomsBasedCategory

/-!
# A small-hom model of the quotient stack at a stage

The quotient stack `[U/R]` of a groupoid in algebraic spaces is a stackification, and its hom sets
sit one universe above those of an object of `AlgebraicGeometry.Stack.AlgebraicStacks`. This file
shows that this is only a matter of size: the hom sets of `[U/R]` are `u`-small, so `[U/R]` is
equivalent over the big fppf site to the category with the same objects and shrunk hom sets, and
when `[U/R]` is algebraic that category is an object of the 2-category of algebraic stacks. This
discharges `AlgebraicGeometry.Stack.StackDescentSystem.StageStackModel`, the universe step of the
proof of Stacks 0CN4.

## Main results

* `AlgebraicGeometry.Stack.nonempty_quotientStackModel`: an algebraic quotient stack over an
  algebraic space `Y` has a model over `Y` in `AlgebraicGeometry.Stack.AlgebraicStacks`.
* `AlgebraicGeometry.Stack.StackDescentSystem.stageStackModel`: every algebraic quotient stack
  of a groupoid over a stage has a model in `AlgebraicGeometry.Stack.AlgebraicStacks`.

## Implementation notes

The shrunk model is `CategoryTheory.BasedCategory.shrinkHoms`. Smallness of the hom sets of
`[U/R]` is `AlgebraicGeometry.Stack.locallySmall_quotientStack`, read off the `Type u` model of the
isomorphism sheaf that `AlgebraicGeometry.Stack.exists_shrunk_isomPresheaf` produces
unconditionally.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The small-hom model of an algebraic quotient stack.** For a groupoid in algebraic spaces over
an algebraic space `Y` whose quotient stack is algebraic, the shrunk model of `[U/R]` is an
algebraic stack by Stacks 03YQ in independent universes, its structure 1-morphism to `Y` is the
canonical map of Stacks 044R read through the shrinking, and the shrinking itself identifies it
with `[U/R]` over `Y`. -/
theorem nonempty_quotientStackModel {Y : AlgebraicSpaces B S hS}
    (G : GroupoidInAlgebraicSpaces B S hS Y)
    (hG : IsAlgebraicStack.{u, w} B S hS (quotientStack G)) :
    Nonempty (QuotientStackModel.{u, w} Y G) := by
  have := locallySmall_quotientStack G
  let 𝒬 := quotientStack G
  let e := BasedCategory.shrinkHomsEquivalenceOver.{u} 𝒬
  have halg : IsAlgebraicStack.{u, w} B S hS (BasedCategory.shrinkHoms.{u} 𝒬) :=
    isAlgebraicStack_of_equivalenceOver B S hS e hG
  let 𝒳ᵢ : AlgebraicStacks.{u, w} B S hS :=
    ⟨CatFiberedInGroupoids.mk (BasedCategory.shrinkHoms.{u} 𝒬) halg.1, halg⟩
  let toBase : BasedCategory.shrinkHoms.{u} 𝒬 ⥤ᵇ
      (algebraicSpaceStack.{u, w} B S hS Y.obj Y.property).val.val :=
    { toFunctor := ShrinkHoms.inverse 𝒬.obj ⋙ (quotientStackToBase G).toFunctor
      w := (Functor.assoc _ _ _).trans
        (congrArg (ShrinkHoms.inverse 𝒬.obj ⋙ ·) (quotientStackToBase G).w) }
  let E : BasedCategory.Equivalence 𝒬 (BasedCategory.shrinkHoms.{u} 𝒬) := e.toBasedEquivalence
  refine ⟨{
    stack := 𝒳ᵢ
    structureMorphism := Bicategory.InducedBicategory.mkHom
      (Bicategory.InducedBicategory.mkHom toBase)
    equivOver := { equiv := E, compIso := ?_ } }⟩
  refine BasedNatIso.mkNatIso (NatIso.ofComponents (fun x => Iso.refl _) ?_) ?_
  · intro x y f
    show (quotientStackToBase G).toFunctor.map
        ((equivShrink (x ⟶ y)).symm (equivShrink (x ⟶ y) f)) ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp
  · intro a
    exact IsHomLift.id (Functor.congr_obj (BasedFunctor.w (E.functor.comp toBase)) a)

namespace StackDescentSystem

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    [Nonempty I]
    (C : StackDescentSystem B S hS hZ I)

/-- **The small-hom model of an algebraic quotient stack at a stage**: the model of
`AlgebraicGeometry.Stack.nonempty_quotientStackModel` over the stage `X_i`. -/
theorem stageStackModel : C.StageStackModel.{u, w} := fun _ Gᵢ hGᵢ =>
  (nonempty_quotientStackModel Gᵢ hGᵢ).map (QuotientStackModel.ofModel C)

end StackDescentSystem

end AlgebraicGeometry.Stack

end
