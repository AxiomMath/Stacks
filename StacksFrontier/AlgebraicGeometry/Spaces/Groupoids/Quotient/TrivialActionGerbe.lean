module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.GerbeCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.ActionGroupoid

/-!
# The quotient stack of a group algebraic space acting on the base (Stacks 06PF)

Let `G` be a group algebraic space over an algebraic space `B` over a scheme `S` of a big fppf
site, and endow `B` with the trivial action of `G`. This file proves that the structure arrow
`[B/G] ⟶ B` of Stacks 044R turns `[B/G]` into a gerbe over `B`.

## Main definitions

* `AlgebraicGeometry.Space.modObjTensorUnit`: the unique, hence trivial, action of a monoid
  object of a cartesian monoidal category on the terminal object.

## Main results

* `AlgebraicGeometry.Stack.isGerbeOver_quotientStackToBase_trivialAction`: **Stacks 06PF**.

## Implementation notes

`B` over `B` is the terminal object of the slice over `B`, so it carries exactly one action of
`G`: the action morphism `G ×_B B ⟶ B` is the unique morphism to a terminal object, and the unit
and associativity laws hold for the same reason. That action is the trivial one, so the quotient
stack of the action groupoid of Stacks 0444 attached to it is `[B/G]` for the trivial action.

The object space of that action groupoid is `B` itself and its structure morphism to the base is
the identity, which is what the heterogeneous equations carried by Stacks 0444 say here. So the
statement follows from `AlgebraicGeometry.Stack.isGerbeOver_quotientStackToBase_of_isIso`: the
object space surjects onto the base because the structure morphism is an isomorphism, and two
points of the object space with the same image in `B` are then equal and are joined by the
identity arrow of the groupoid. These two facts are the surjectivity of `B ⟶ B` and of
`B ×_B G ⟶ B` that the source invokes, the latter having the unit of `G` as a section.

`AlgebraicGeometry.Space.groupoidOfAction` provides the action groupoid the statement quantifies
over.

## References

* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
* [Stacks Project, Tag 06PE](https://stacks.math.columbia.edu/tag/06PE)
* [Stacks Project, Tag 06PF](https://stacks.math.columbia.edu/tag/06PF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u uD vD

namespace AlgebraicGeometry.Space

/-- A monoid object of a cartesian monoidal category acts on the terminal object in exactly one
way, namely trivially: any two morphisms to a terminal object agree. -/
noncomputable instance modObjTensorUnit {D : Type uD} [Category.{vD} D]
    [CartesianMonoidalCategory D] (M : D) [MonObj M] : ModObj M (𝟙_ D) where
  smul := toUnit _
  one_smul := by apply toUnit_unique
  mul_smul := by apply toUnit_unique

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- **Stacks 06PF.** Let `G` be a group algebraic space over `B` and endow `B` with the trivial
action of `G`. The structure arrow `[B/G] ⟶ B` turns `[B/G]` into a gerbe over `B`. -/
@[stacks 06PF]
theorem isGerbeOver_quotientStackToBase_trivialAction
    (B : AlgebraicSpaces C S hS) (G : Over B.obj) [GrpObj G]
    (hG : IsAlgebraicSpace C S hS G.left)
    (A : Space.ActionGroupoidConstruction B G (𝟙_ (Over B.obj)) hG B.property) :
    CategoryTheory.IsGerbeOver (BigFppfOver.topology C S hS)
      (fibredCategory C S hS B.obj).val.p (quotientStackToBase A.groupoid).toFunctor := by
  have htypes : A.groupoid.objects.obj = B.obj := congrArg (fun z => z.obj) A.objects_eq
  have h : A.groupoid.objectsToBase.hom = eqToHom htypes := by
    have h2 := (conj_eqToHom_iff_heq A.groupoid.objectsToBase.hom (𝟙 B.obj) htypes rfl).2
      A.objectsToBase_eq
    simpa using h2
  exact isGerbeOver_quotientStackToBase_of_isIso A.groupoid (by rw [h]; infer_instance)

end AlgebraicGeometry.Stack

end
