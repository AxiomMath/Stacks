module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms

/-!
# The schematic locus of an algebraic space

The schematic locus of a presheaf `F` on the big fppf site over `S` is the supremum, in the
complete lattice of subfunctors of `F`, of the open subspaces of `F` which are represented by a
scheme over `S`; every such open subspace is contained in it (Stacks 03JH).

## Main definitions

* `AlgebraicGeometry.Space.schematicLocus` is the supremum, in the complete lattice of
  subfunctors, of the open subspaces which are represented by a scheme over `S`.

## Main results

* `AlgebraicGeometry.Space.le_schematicLocus`: every representable open subspace is contained
  in the schematic locus.

## References

* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The schematic locus of `F`: the union of all open subspaces of `F` which are represented
by a scheme over `S`. -/
@[stacks 03JH "schematic locus"]
def schematicLocus (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Subfunctor F :=
  sSup {G : Subfunctor F | IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable}

/-- Every open subspace which is represented by a scheme over `S` is contained in the
schematic locus. -/
@[stacks 03JH "maximality"]
theorem le_schematicLocus (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (G : Subfunctor F)
    (hG : IsOpenSubspace B S hS G) (hGrep : G.toFunctor.IsRepresentable) :
    G ≤ schematicLocus B S hS F :=
  le_sSup ⟨hG, hGrep⟩

end AlgebraicGeometry.Space

end
