module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified

/-!
# The pre-relation of a groupoid over the base, read in the binary product

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site.  Its pre-relation is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.sourceTarget`, the morphism `(t, s)` into the
square `AlgebraicGeometry.GroupoidInAlgebraicSpaces.objectPairs` of the object space, which is
the fibre product `U ×_B U`.  When `B` is the final algebraic space — the case of a groupoid over
the base scheme of the site — that fibre product is the *binary product* `U ⨯ U` of presheaves,
and the pre-relation is the lift `prod.lift t s` of the two structure morphisms.

That lift is the shape in which the transfers of
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSpacesDerealizationProperties` and the
division of
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.DerealizationIdentityArrowDivision` take the
hypotheses on the pre-relation, while `…sourceTarget` is the shape in which the fibre-product
square of the object space produces them.  This file compares the two and transfers the three
properties the division consumes across the comparison.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.objectPairsProdIso`: **the square of the object
  space over a final base is the binary product of the object space with itself.**

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.sourceTarget_comp_objectPairsProdIso`: **the
  pre-relation `(t, s)`, read through that comparison, is `prod.lift t s`.**
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isUnramified_prodLift_of_sourceTarget`,
  `…isSeparated_prodLift_of_sourceTarget` and
  `…isLocallyQuasiFinite_prodLift_of_sourceTarget`: the three properties of the pre-relation that
  the division of **Stacks 04S4** by the piece through the identity consumes, carried from the
  fibre-product shape to the binary-product shape.

## References

* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 04S4](https://stacks.math.columbia.edu/tag/04S4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
  (hB : IsTerminal B.obj)

/-- A fibre product over a final presheaf is a binary product, so the square `U ×_B U` of the
object space of a groupoid over a final base is a limit of the pair `(U, U)`. -/
def isLimit_objectPairsBinaryFan :
    IsLimit (BinaryFan.mk (pullback.fst G.objectsToBase.hom G.objectsToBase.hom)
      (pullback.snd G.objectsToBase.hom G.objectsToBase.hom)) :=
  isProductOfIsTerminalIsPullback G.objectsToBase.hom G.objectsToBase.hom
    (pullback.fst G.objectsToBase.hom G.objectsToBase.hom)
    (pullback.snd G.objectsToBase.hom G.objectsToBase.hom) hB (pullbackIsPullback _ _)

/-- **The square of the object space over a final base is the binary product of the object space
with itself.** -/
def objectPairsProdIso :
    (objectPairs G).obj ≅
      (G.objects.obj ⨯ G.objects.obj : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :=
  (limit.isoLimitCone ⟨_, isLimit_objectPairsBinaryFan G hB⟩).symm

/-- The comparison of `AlgebraicGeometry.GroupoidInAlgebraicSpaces.objectPairsProdIso` is
compatible with the target component. -/
theorem objectPairsProdIso_hom_fst :
    (objectPairsProdIso G hB).hom ≫ prod.fst = (objectPairsTarget G).hom :=
  limit.isoLimitCone_inv_π ⟨_, isLimit_objectPairsBinaryFan G hB⟩ ⟨WalkingPair.left⟩

/-- The comparison of `AlgebraicGeometry.GroupoidInAlgebraicSpaces.objectPairsProdIso` is
compatible with the source component. -/
theorem objectPairsProdIso_hom_snd :
    (objectPairsProdIso G hB).hom ≫ prod.snd = (objectPairsSource G).hom :=
  limit.isoLimitCone_inv_π ⟨_, isLimit_objectPairsBinaryFan G hB⟩ ⟨WalkingPair.right⟩

/-- **The pre-relation `(t, s) : R ⟶ U ×_B U` of a groupoid over a final base, read through the
comparison with the binary product, is the lift `prod.lift t s` of the target and the source.**

This is the identification that carries a property of the pre-relation stated at the fibre
product of the object space with itself over the base — the shape in which the fibre-product
square produces it — to the same property stated at the binary product of presheaves, which is
the shape the de-realization transfers consume. -/
theorem sourceTarget_comp_objectPairsProdIso :
    (sourceTarget G).hom ≫ (objectPairsProdIso G hB).hom =
      prod.lift G.target.hom G.source.hom := by
  refine prod.hom_ext ?_ ?_
  · rw [Category.assoc, objectPairsProdIso_hom_fst, prod.lift_fst]
    exact sourceTarget_target_projection G
  · rw [Category.assoc, objectPairsProdIso_hom_snd, prod.lift_snd]
    exact sourceTarget_source_projection G

/-- A property of presheaf morphisms respecting isomorphisms passes from the pre-relation at the
fibre product of the object space to the pre-relation at the binary product. -/
private theorem prodLift_of_sourceTarget_of_respectsIso
    (hB : IsTerminal B.obj) (P : MorphismProperty ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u))
    [P.RespectsIso] (h : P (sourceTarget G).hom) : P (prod.lift G.target.hom G.source.hom) := by
  rw [← sourceTarget_comp_objectPairsProdIso G hB]
  exact MorphismProperty.RespectsIso.postcomp _ _ _ h

include hB in
/-- **A property étale local on the source and the target transfers from the pre-relation at the
fibre product of the object space to the pre-relation at the binary product.** -/
theorem holdsOnEveryEtaleChart_prodLift_of_sourceTarget {P : MorphismProperty Scheme.{u}}
    (h : Space.HoldsOnEveryEtaleChart C S hS P (sourceTarget G).hom) :
    Space.HoldsOnEveryEtaleChart C S hS P (prod.lift G.target.hom G.source.hom) := by
  let : MorphismProperty.RespectsIso
      (fun ⦃F F' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u⦄ (f : F ⟶ F') =>
        Space.HoldsOnEveryEtaleChart C S hS P f) :=
    Space.holdsOnEveryEtaleChart_respectsIso_presheaf C S hS P
  exact prodLift_of_sourceTarget_of_respectsIso G hB _ h

include hB in
/-- **The pre-relation at the binary product is unramified as soon as the pre-relation at the
fibre product of the object space is.** -/
theorem isUnramified_prodLift_of_sourceTarget
    (h : Space.IsUnramified C S hS (sourceTarget G).hom) :
    Space.IsUnramified C S hS (prod.lift G.target.hom G.source.hom) :=
  holdsOnEveryEtaleChart_prodLift_of_sourceTarget G hB h

include hB in
/-- **The pre-relation at the binary product is locally of finite type as soon as the
pre-relation at the fibre product of the object space is.** -/
theorem isLocallyOfFiniteType_prodLift_of_sourceTarget
    (h : Space.IsLocallyOfFiniteType C S hS (sourceTarget G).hom) :
    Space.IsLocallyOfFiniteType C S hS (prod.lift G.target.hom G.source.hom) :=
  holdsOnEveryEtaleChart_prodLift_of_sourceTarget G hB h

include hB in
/-- **The pre-relation at the binary product is locally quasi-finite as soon as the pre-relation
at the fibre product of the object space is.** -/
theorem isLocallyQuasiFinite_prodLift_of_sourceTarget
    (h : Space.IsLocallyQuasiFinite C S hS (sourceTarget G).hom) :
    Space.IsLocallyQuasiFinite C S hS (prod.lift G.target.hom G.source.hom) :=
  holdsOnEveryEtaleChart_prodLift_of_sourceTarget G hB h

include hB in
/-- **The pre-relation at the binary product is separated as soon as the pre-relation at the
fibre product of the object space is.**

Separatedness is a condition on the relative diagonal rather than a chart condition, so this
does not go through
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.holdsOnEveryEtaleChart_prodLift_of_sourceTarget`;
the comparison absorbed is the same one. -/
theorem isSeparated_prodLift_of_sourceTarget
    (h : Space.IsSeparated C S hS (sourceTarget G).hom) :
    Space.IsSeparated C S hS (prod.lift G.target.hom G.source.hom) := by
  let : MorphismProperty.RespectsIso (@Space.IsSeparated C S hS) :=
    Space.isSeparated_respectsIso C S hS
  exact prodLift_of_sourceTarget_of_respectsIso G hB _ h

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
