module

public import StacksFrontier.Homology.KFlat.Flat

/-!
# Acyclicity of a colimit of complexes, for an arbitrary colimit cocone

A colimit of acyclic complexes along a shape whose colimits are exact is acyclic. This file
records that statement for an arbitrary colimit cocone rather than for the cocone of the colimit
API, which is what a consumer whose colimit comes from an explicit construction has.

## Main results

* `HomologicalComplex.acyclic_of_isColimit`: **the point of a colimit cocone over a diagram of
  acyclic complexes is acyclic**, along a shape whose colimits in the base are exact.

## Implementation notes

The statement is deduced from `CochainComplex.KFlat.acyclic_colimit`, the same assertion for the
chosen colimit, by transporting exactness in each degree along the canonical isomorphism between
the two colimits.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w x v u

namespace HomologicalComplex

/-- **The point of a colimit cocone over a diagram of acyclic complexes is acyclic**, along a
shape whose colimits in the base category are exact. -/
lemma acyclic_of_isColimit {A : Type u} [Category.{v} A] [Abelian A] {I : Type*}
    {cs : ComplexShape I} {J : Type w} [Category.{x} J] [HasColimitsOfShape J A]
    [HasExactColimitsOfShape J A] {K : J ⥤ HomologicalComplex A cs} {c : Cocone K}
    (hc : IsColimit c) (hK : ∀ j, (K.obj j).Acyclic) : c.pt.Acyclic := fun i ↦
  (CochainComplex.KFlat.acyclic_colimit K hK i).of_iso
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit K) hc)

end HomologicalComplex
