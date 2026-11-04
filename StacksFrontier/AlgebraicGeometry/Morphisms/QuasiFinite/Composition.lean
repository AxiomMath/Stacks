module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs

/-!
# Composition of quasi-finite morphisms

Local quasi-finiteness is stable under composition, and so is quasi-finiteness: each of the
three conditions cutting out a quasi-finite morphism — local finite type, quasi-compactness and
the fibre condition — is itself stable under composition.

## Main results

* `AlgebraicGeometry.locallyQuasiFinite_conditions_comp`: a composition of locally quasi-finite
  morphisms is locally quasi-finite.
* `AlgebraicGeometry.quasiFinite_conditions_comp`: a composition of quasi-finite morphisms is
  quasi-finite.

## Implementation notes

As in `AlgebraicGeometry.QuasiFinite.Defs`, local quasi-finiteness is the conjunction of the
typeclasses `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.LocallyQuasiFinite`,
and quasi-finiteness adds `AlgebraicGeometry.QuasiCompact`. Each conjunct is stable under
composition in Mathlib, so the hypotheses are taken as instances and the conclusions are the
corresponding conjunctions.

The fibre condition composes because quasi-finiteness of ring maps does, which is
[Stacks Project, Tag 00PO](https://stacks.math.columbia.edu/tag/00PO).

## References

* [Stacks Project, Tag 01TL](https://stacks.math.columbia.edu/tag/01TL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 01TL.** The composition of two locally quasi-finite morphisms is
locally quasi-finite. -/
@[stacks 01TL "locally quasi-finite morphisms"]
theorem locallyQuasiFinite_conditions_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [LocallyOfFiniteType g] [LocallyQuasiFinite g] :
    LocallyOfFiniteType (f ≫ g) ∧ LocallyQuasiFinite (f ≫ g) :=
  ⟨inferInstance, inferInstance⟩

/-- **Stacks Project, Tag 01TL.** The composition of two quasi-finite morphisms is
quasi-finite. -/
@[stacks 01TL "quasi-finite morphisms"]
theorem quasiFinite_conditions_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f]
    [LocallyOfFiniteType g] [QuasiCompact g] [LocallyQuasiFinite g] :
    (LocallyOfFiniteType (f ≫ g) ∧ QuasiCompact (f ≫ g)) ∧ LocallyQuasiFinite (f ≫ g) :=
  ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

end AlgebraicGeometry

end
