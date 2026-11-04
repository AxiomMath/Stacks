module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleTensor

/-!
# The braided and closed structure on abelian groups, transported from modules

`AddCommGrpCat.monoidalCategory` is the monoidal structure on abelian groups given by the tensor
product over `ℤ`, obtained by transport along the equivalence `AddCommGrpCat.uliftIntEquivalence`
with modules over a universe-lifted copy of `ℤ`. This file names the rest of the transported
structure in an arbitrary universe: the monoidality of the two functors of that equivalence, the
braiding `AddCommGrpCat.braidedCategory`, and the internal hom `AddCommGrpCat.monoidalClosed`.

## Implementation notes

The structures are named, rather than being anonymous local instances, because
`StacksFrontier.AlgebraicGeometry.Spaces.AbelianSheafMonoidal` needs them to put a tensor product on
the abelian sheaves of a topological space. They are `@[instance_reducible]` definitions rather
than instances, since a global monoidal instance on a category with finite products conflicts with
the cartesian one; a consumer enables them with `attribute [local instance]`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

universe v

namespace AddCommGrpCat

section TransportedStructure

attribute [local instance] monoidalCategory

/-- The equivalence with the modules over a universe-lifted copy of the integers is a monoidal
equivalence: its inverse is a monoidal functor. -/
@[instance_reducible] def uliftIntEquivalenceInverseMonoidal :
    (uliftIntEquivalence.{v}).inverse.Monoidal := by
  change (Monoidal.equivalenceTransported (uliftIntEquivalence.{v})).inverse.Monoidal
  infer_instance

attribute [local instance] uliftIntEquivalenceInverseMonoidal

/-- The equivalence with the modules over a universe-lifted copy of the integers is a monoidal
equivalence: its functor is a monoidal functor. -/
@[instance_reducible] def uliftIntEquivalenceFunctorMonoidal :
    (uliftIntEquivalence.{v}).functor.Monoidal := by
  change (Monoidal.equivalenceTransported (uliftIntEquivalence.{v})).functor.Monoidal
  infer_instance

attribute [local instance] uliftIntEquivalenceFunctorMonoidal

/-- The tensor product of abelian groups is braided, the braiding being transported from the
modules over a universe-lifted copy of the integers. -/
@[instance_reducible] def braidedCategory : BraidedCategory AddCommGrpCat.{v} := by
  change BraidedCategory (Monoidal.Transported (uliftIntEquivalence.{v}))
  infer_instance

/-- The tensor product of abelian groups is closed, the internal hom being transported from the
modules over a universe-lifted copy of the integers. -/
@[instance_reducible] def monoidalClosed : MonoidalClosed AddCommGrpCat.{v} :=
  MonoidalClosed.ofEquiv (uliftIntEquivalence.{v}).inverse
    (uliftIntEquivalence.{v}).symm.toAdjunction

end TransportedStructure

end AddCommGrpCat

end
