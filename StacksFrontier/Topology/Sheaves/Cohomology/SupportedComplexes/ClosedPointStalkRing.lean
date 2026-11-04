module

public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedPointDerivedSections
public import
  StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackLeftExact

/-!
# Sections on a space with at most one point are the stalk

Let `X` be a topological space with at most one point and let `x ∈ X`. For every presheaf `F` on
`X` with values in a category with colimits the germ map

`Γ(⊤, F) ⟶ F_x`

is an isomorphism.

For a point `x` of a ringed space `X` there is an isomorphism of commutative rings

`Γ({x}, 𝒪_X|_{\{x\}}) ≅ 𝒪_{X,x}`.

## Main definitions

* `Stacks.Topology.sectionsIsoStalk`: the germ map `Γ(⊤, F) ⟶ F_x` as an isomorphism, on a space
  with at most one point.
* `Stacks.Cohomology.SupportedComplexes.singletonPoint`: the point of the ringed space on a
  singleton.
* `Stacks.Cohomology.SupportedComplexes.sectionsAtPointStructureSheafIso`: the displayed
  identification `Γ({x}, 𝒪_X|_{\{x\}}) ≅ 𝒪_{X,x}` of commutative rings.

## Main results

* `Stacks.Topology.eq_top_of_mem_of_subsingleton`: on a space with at most one point an open
  containing the point is the whole space.
* `Stacks.Topology.isTerminal_op_top_openNhds`: `⊤` is initial among the open neighbourhoods of
  the point.
* `Stacks.Topology.isIso_Γgerm_of_subsingleton`: the germ map at `⊤` is an isomorphism.

## References

* [Stacks Project, Tag 0G02](https://stacks.math.columbia.edu/tag/0G02)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe v u

namespace Stacks.Topology

variable {C : Type u} [Category.{v} C] [HasColimits.{v} C] {X : TopCat.{v}}
  [Subsingleton X] (x : X)

/-- On a space with at most one point an open containing the point is the whole space. -/
public theorem eq_top_of_mem_of_subsingleton (U : Opens X) (hx : x ∈ U) : U = ⊤ :=
  eq_top_iff.2 fun y _ ↦ Subsingleton.elim x y ▸ hx

/-- The whole space is the initial open neighbourhood of a point of a space with at most one
point, stated as terminality of `op ⊤` in the opposite category. -/
public def isTerminal_op_top_openNhds : IsTerminal (op (⟨⊤, trivial⟩ : OpenNhds x)) :=
  IsTerminal.ofUniqueHom
    (fun U ↦ Quiver.Hom.op (homOfLE (Subtype.coe_le_coe.mp
      (le_of_eq (eq_top_of_mem_of_subsingleton x U.unop.1 U.unop.2).symm))))
    (fun _ _ ↦ Subsingleton.elim _ _)

/-- The germ map on global sections is an isomorphism on a space with at most one point. -/
public theorem isIso_Γgerm_of_subsingleton (F : TopCat.Presheaf C X) : IsIso (F.Γgerm x) :=
  isIso_ι_of_isTerminal (isTerminal_op_top_openNhds x) ((OpenNhds.inclusion x).op ⋙ F)

/-- Sections on the whole space are the stalk, on a space with at most one point. -/
public def sectionsIsoStalk (F : TopCat.Presheaf C X) : F.obj (op ⊤) ≅ F.stalk x :=
  letI := isIso_Γgerm_of_subsingleton x F
  asIso (F.Γgerm x)

end Stacks.Topology

namespace Stacks.Cohomology.SupportedComplexes

variable (X : RingedSpace.{u, u}) (x : X.carrier)

/-- The point of the ringed space on the singleton `{x}`. -/
public abbrev singletonPoint : (closedSubsetRingedSpace X ({x} : Set X.carrier)).carrier :=
  ⟨x, rfl⟩

/-- The ring of sections of the restricted structure sheaf on a point is the local ring there:
`Γ({x}, 𝒪_X|_{\{x\}}) ≅ 𝒪_{X,x}`. -/
public def sectionsAtPointStructureSheafIso :
    (closedSubsetRingedSpace X ({x} : Set X.carrier)).presheaf.obj (op ⊤) ≅
      X.presheaf.stalk x :=
  Stacks.Topology.sectionsIsoStalk (singletonPoint X x)
      (closedSubsetRingedSpace X ({x} : Set X.carrier)).presheaf ≪≫
    AlgebraicGeometry.RingedSpace.inverseImageStalkIso X
      (ClosedImmersionSheaves.closedSubsetInclusion ({x} : Set X.carrier)) (singletonPoint X x)

end Stacks.Cohomology.SupportedComplexes

end
