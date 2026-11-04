module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackOfAction
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackTorsorComparison
public import StacksFrontier.CategoryTheory.Sites.Stackification.ComparisonEquivalence
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyGroupoid

/-!
# The quotient stack is the stack of torsors with an equivariant map (Stacks 04WM)

Let `G` be a group algebraic space over an algebraic space `B` over a scheme `S` of a big fppf
site, acting on an algebraic space `X` over `B`.  The quotient stack `[X/G]` of Stacks 044Q is
the stackification of the pointwise groupoid fibration of the action groupoid of Stacks 0444, and
`[[X/G]]` of Situation 04WL is the category of fppf `G`-torsors with a `G`-equivariant map to
`X`.  **Stacks 04WM** says that the two are canonically equivalent over the big fppf site of `S`.

## Main results

* `AlgebraicGeometry.Space.quotientStackTorsorEquivalence`: **Stacks 04WM**, the equivalence
  `[X/G] ≌ [[X/G]]` over the big fppf site, together with a vertical natural isomorphism
  identifying its forward 1-morphism, restricted along the canonical map from the pointwise
  presentation, with the explicit pointwise comparison `F_p` of
  `AlgebraicGeometry.Space.actionPointwiseComparison`.

## Implementation notes

The source of the equivalence is the quotient stack of the action groupoid of Stacks 0444,
`AlgebraicGeometry.Stack.quotientStackOfAction ⟨B, hB⟩ G.obj.X X G.property hX`, which is by
definition `AlgebraicGeometry.Stack.quotientStack` of
`(AlgebraicGeometry.Space.groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX).groupoid` — the
action groupoid `(X, G ×_B X, pr₁, a, m)` of the given action.  The target is
`AlgebraicGeometry.Space.TorsorWithMap.projection`, whose stack property is Stacks 0370,
`projection_isStackInGroupoids_of_isAlgebraicSpace`, together with Stacks 04US,
`AlgebraicGeometry.Space.FppfTorsors.projection_isStack`.

The explicit comparison out of the pointwise action groupoid is
`AlgebraicGeometry.Space.actionPointwiseComparison`, and the three properties of Stacks 02ZN it
has are `AlgebraicGeometry.Space.actionPointwiseComparison_comp_projection`,
`AlgebraicGeometry.Space.actionPointwiseComparison_locallyBijective` and
`AlgebraicGeometry.Space.actionPointwiseComparison_locallyEssImage`.  Both of the latter are
stated there for the comparison composed with a functor raising the universe of the morphisms,
because the morphism presheaves of Stacks 042V are formed for two categories over the site with a
common hom universe while the pointwise action groupoid has morphisms one universe below those of
`[[X/G]]`; the universe-raising functor is
`(AlgebraicGeometry.Stack.quotientPrestackEquivalence _).inverse`, which is exactly how `F_p`
enters, since the stackification of Stacks 02ZN is formed on the universe-lifted presentation
`AlgebraicGeometry.Stack.quotientPrestack`.

The forward 1-morphism of the equivalence is the extension of `F_p` over the stackification,
`CategoryTheory.Functor.Stackification.extendGroupoid` (Stacks 0436), and the vertical natural
isomorphism is its unit; the equivalence itself is
`CategoryTheory.Functor.Stackification.equivalenceOverOfStackifications`, which produces an
equivalence over the site *with that prescribed forward 1-morphism*, so that the result is not
the bare existence of an equivalence.

## References

* [Stacks Project, Tag 04WM](https://stacks.math.columbia.edu/tag/04WM)
* [Stacks Project, Situation 04WL](https://stacks.math.columbia.edu/tag/04WL)
* [Stacks Project, Tag 0370](https://stacks.math.columbia.edu/tag/0370)
* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 0436](https://stacks.math.columbia.edu/tag/0436)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (hB : IsAlgebraicSpace 𝒞 S hS B)
  (G : GroupAlgebraicSpace 𝒞 S hS B hB) (X : Over B) [ModObj G.obj.X X]
  (hX : IsAlgebraicSpace 𝒞 S hS X.left)

/-- The projection of `[[X/G]]` is a stack over the big fppf site in the sieve-indexed sense of
Stacks 026F. -/
theorem TorsorWithMap.projection_isStack_of_isAlgebraicSpace
    (hX' : IsAlgebraicSpace 𝒞 S hS X.left) :
    (TorsorWithMap.projection hB G X).IsStack (BigFppfOver.topology 𝒞 S hS) :=
  let : HasPullbacks (BigFppfOver 𝒞 S hS) := inferInstance
  let : (TorsorWithMap.projection hB G X).IsFibered :=
    (TorsorWithMap.projection_isFiberedInGroupoids (hB := hB) (G := G) X
      (torsorProjection_isFiberedInGroupoids hB G)).isFibered
  Functor.isStack_of_isStackInGroupoids
    (TorsorWithMap.projection_isStackInGroupoids_of_isAlgebraicSpace.{u, u + 1} hB G X hX')

/-- The comparison `F_p`, read on the universe-lifted pointwise presentation, lies strictly over
the big fppf site. -/
theorem actionPointwiseComparison_lift_comp :
    ((Stack.quotientPrestackEquivalence
          (groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX).groupoid).inverse ⋙
        actionPointwiseComparison hB G X hX) ⋙ TorsorWithMap.projection hB G X =
      (Stack.quotientPrestack
        (groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX).groupoid).p := by
  rw [CategoryTheory.Functor.assoc, actionPointwiseComparison_comp_projection]
  rfl

/-- The extension of `F_p` over the stackification: the 1-morphism `[X/G] ⟶ [[X/G]]` of
Stacks 0436 attached to `F_p`. -/
def actionPointwiseComparisonExtension :
    (Stack.quotientStackOfAction ⟨B, hB⟩ G.obj.X X G.property hX).obj ⥤
      TorsorWithMap hB G X :=
  Functor.Stackification.extendGroupoid
    (Stack.isFiberedInGroupoids_quotientPrestack _)
    (Stack.isFiberedInGroupoids_quotientStack _) (Stack.isStack_quotientStack _)
    (TorsorWithMap.projection_isFiberedInGroupoids (hB := hB) (G := G) X
      (torsorProjection_isFiberedInGroupoids hB G))
    (TorsorWithMap.projection_isStack_of_isAlgebraicSpace hB G X hX)
    (Stack.isFibredOneMorphism_toQuotientStack _).comp_eq
    (actionPointwiseComparison_lift_comp hB G X hX)
    (Stack.isLocallyBijective_toQuotientStack _)
    (Stack.essImage_toQuotientStack _)

/-- The extension lies strictly over the big fppf site. -/
theorem actionPointwiseComparisonExtension_comp_projection :
    actionPointwiseComparisonExtension hB G X hX ⋙ TorsorWithMap.projection hB G X =
      (Stack.quotientStackOfAction ⟨B, hB⟩ G.obj.X X G.property hX).p :=
  Functor.Stackification.extendGroupoid_comp_eq ..

/-- The unit of Stacks 0436 for `F_p`: the extension restricted along the canonical map to the
stackification is `F_p` on the universe-lifted pointwise presentation. -/
def actionPointwiseComparisonExtensionUnit :
    Stack.toQuotientStack (groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX).groupoid ⋙
        actionPointwiseComparisonExtension hB G X hX ≅
      (Stack.quotientPrestackEquivalence
          (groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX).groupoid).inverse ⋙
        actionPointwiseComparison hB G X hX :=
  Functor.Stackification.unitGroupoid
    (Stack.isFiberedInGroupoids_quotientPrestack _)
    (Stack.isFiberedInGroupoids_quotientStack _) (Stack.isStack_quotientStack _)
    (TorsorWithMap.projection_isFiberedInGroupoids (hB := hB) (G := G) X
      (torsorProjection_isFiberedInGroupoids hB G))
    (TorsorWithMap.projection_isStack_of_isAlgebraicSpace hB G X hX)
    (Stack.isFibredOneMorphism_toQuotientStack _).comp_eq
    (actionPointwiseComparison_lift_comp hB G X hX)
    (Stack.isLocallyBijective_toQuotientStack _)
    (Stack.essImage_toQuotientStack _)

/-- Every component of the unit lies over an identity of the big fppf site. -/
theorem actionPointwiseComparisonExtensionUnit_isHomLift
    (A : (Stack.quotientPrestack
      (groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX).groupoid).obj) :
    (TorsorWithMap.projection hB G X).IsHomLift
      (𝟙 ((Stack.quotientPrestack
        (groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX).groupoid).p.obj A))
      ((actionPointwiseComparisonExtensionUnit hB G X hX).hom.app A) :=
  Functor.Stackification.isHomLift_unitGroupoid_app (A := A) ..

/-- The extension restricted along the canonical map from the *unlifted* pointwise presentation
is `F_p`: the unit, whiskered with the universe lift. -/
def actionPointwiseComparisonExtensionIso :
    Stack.pointwiseToQuotientStack
        (groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX).groupoid ⋙
      actionPointwiseComparisonExtension hB G X hX ≅ actionPointwiseComparison hB G X hX :=
  Functor.isoWhiskerLeft
    (Stack.quotientPrestackEquivalence
      (groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX).groupoid).functor
    (actionPointwiseComparisonExtensionUnit hB G X hX)

/-- Every component of that isomorphism lies over an identity of the big fppf site. -/
theorem actionPointwiseComparisonExtensionIso_isHomLift
    (A : (actionPointwiseCategory hB G X hX).obj) :
    (TorsorWithMap.projection hB G X).IsHomLift (𝟙 A.base)
      ((actionPointwiseComparisonExtensionIso hB G X hX).hom.app A) :=
  actionPointwiseComparisonExtensionUnit_isHomLift hB G X hX
    ((Stack.quotientPrestackEquivalence
      (groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX).groupoid).functor.obj A)

/-- The quotient stack `[X/G]` of the action of a group algebraic space `G` over
an algebraic space `B` on an algebraic space `X` over `B` is canonically equivalent, over the big
fppf site of `S`, to the stack `[[X/G]]` of fppf `G`-torsors with a `G`-equivariant map to `X`;
and the forward 1-morphism of the equivalence extends the explicit pointwise comparison `F_p` of
`AlgebraicGeometry.Space.actionPointwiseComparison`, the identification being a natural
isomorphism all of whose components lie over identities of the site.

The source is the quotient stack of the action groupoid `(X, G ×_B X, pr₁, a, m)` of Stacks 0444,
that is `AlgebraicGeometry.Stack.quotientStackOfAction` of Stacks 044Q part (2). -/
@[stacks 04WM "the canonical equivalence [X/G] ≌ [[X/G]] over the big fppf site, whose forward \
functor extends the explicit pointwise comparison F_p"]
def quotientStackTorsorEquivalence :
    {e : StacksRepresentableCFG.EquivalenceOver
        (Stack.quotientStackOfAction ⟨B, hB⟩ G.obj.X X G.property hX).p
        (TorsorWithMap.projection hB G X) //
      ∃ α : Stack.pointwiseToQuotientStack
            (groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX).groupoid ⋙ e.hom.functor ≅
          actionPointwiseComparison hB G X hX,
        ∀ A : (actionPointwiseCategory hB G X hX).obj,
          (TorsorWithMap.projection hB G X).IsHomLift (𝟙 A.base) (α.hom.app A)} := by
  have hsq := TorsorWithMap.projection_isStack_of_isAlgebraicSpace hB G X hX
  have hq := TorsorWithMap.projection_isFiberedInGroupoids (hB := hB) (G := G) X
    (torsorProjection_isFiberedInGroupoids hB G)
  haveI : (TorsorWithMap.projection hB G X).IsFibered := hsq.isFibered
  have hF := hq.isFibredOneMorphism (actionPointwiseComparison_lift_comp hB G X hX)
  refine ⟨Functor.Stackification.equivalenceOverOfStackifications
    (Stack.isFiberedInGroupoids_quotientStack _) hq (Stack.isStack_quotientStack _) hsq
    (Stack.isFibredOneMorphism_toQuotientStack _) hF
    (Stack.isLocallyBijective_toQuotientStack _)
    (fun U x y => actionPointwiseComparison_locallyBijective hB G X hX
      (Stack.quotientPrestackEquivalence
        (groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX).groupoid).inverse hF U x y)
    (Stack.essImage_toQuotientStack _)
    (fun U y => actionPointwiseComparison_locallyEssImage hB G X hX
      (Stack.isFiberedInGroupoids_quotientPrestack _)
      (Stack.quotientPrestackEquivalence
        (groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX).groupoid).inverse
      (fun A => ⟨ULiftHom.objUp.{u + 1, u + 1} A, rfl⟩)
      (actionPointwiseComparison_lift_comp hB G X hX) U y)
    (actionPointwiseComparisonExtension hB G X hX)
    (hq.isFibredOneMorphism (actionPointwiseComparisonExtension_comp_projection hB G X hX))
    (actionPointwiseComparisonExtensionUnit hB G X hX)
    (actionPointwiseComparisonExtensionUnit_isHomLift hB G X hX),
    actionPointwiseComparisonExtensionIso hB G X hX,
    actionPointwiseComparisonExtensionIso_isHomLift hB G X hX⟩

end AlgebraicGeometry.Space

end
