module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Dimension.Catenary

/-!
# Universally catenary schemes

A locally Noetherian scheme is universally catenary if the source of every morphism to it
which is locally of finite type is a catenary space. The property is inherited by every scheme
locally of finite type over such a base.

## Main definitions

* `AlgebraicGeometry.Scheme.IsUniversallyCatenary` is the universally catenary condition for a
  locally Noetherian scheme.

## Main results

* `AlgebraicGeometry.Scheme.isUniversallyCatenary_iff` characterizes universal catenarity by
  its defining condition.
* `AlgebraicGeometry.Scheme.IsUniversallyCatenary.isCatenarySpace` applies universal catenarity
  to a locally finite type morphism.
* `AlgebraicGeometry.Scheme.isUniversallyCatenary_of_locallyOfFiniteType` shows that universal
  catenarity is inherited by schemes locally of finite type over the base.

## Implementation notes

Local Noetherianity is carried by a typeclass assumption. A morphism locally of finite type is
expressed by `AlgebraicGeometry.LocallyOfFiniteType`, and catenarity of its source by
`IrreducibleClosedsCodim.IsCatenarySpace` on the underlying topological space.
`IsUniversallyCatenary` is kept as an exposed definition so that its characterization is
available by reduction; the named elimination lemma lets downstream results use the condition
without unfolding it. Local Noetherianity of the source in the inheritance statement is
inferred from the locally finite type morphism and the local Noetherianity of the target.

## References

* [Stacks Project, Tag 02J8](https://stacks.math.columbia.edu/tag/02J8)
* [Stacks Project, Tag 02J9](https://stacks.math.columbia.edu/tag/02J9)
-/

@[expose] public section

namespace AlgebraicGeometry.Scheme

open CategoryTheory

universe u

/-- A locally Noetherian scheme `S` is **universally catenary** if every scheme locally of
finite type over `S` is catenary. -/
@[stacks 02J8]
def IsUniversallyCatenary (S : Scheme.{u}) [IsLocallyNoetherian S] : Prop :=
  ∀ (X : Scheme.{u}) (f : X ⟶ S) [LocallyOfFiniteType f],
    IrreducibleClosedsCodim.IsCatenarySpace X

/-- A locally Noetherian scheme is universally catenary exactly when the source of every
locally finite type morphism to it is catenary. -/
theorem isUniversallyCatenary_iff (S : Scheme.{u}) [IsLocallyNoetherian S] :
    IsUniversallyCatenary S ↔ (∀ (X : Scheme.{u}) (f : X ⟶ S) [LocallyOfFiniteType f],
      IrreducibleClosedsCodim.IsCatenarySpace X) := Iff.rfl

/-- The source of a locally finite type morphism to a universally catenary scheme is
catenary. -/
theorem IsUniversallyCatenary.isCatenarySpace {S X : Scheme.{u}} [IsLocallyNoetherian S]
    (hS : IsUniversallyCatenary S) (f : X ⟶ S) [LocallyOfFiniteType f] :
    IrreducibleClosedsCodim.IsCatenarySpace X := hS X f

/-- A scheme locally of finite type over a locally Noetherian universally catenary scheme is
universally catenary. -/
@[stacks 02J9 "inheritance", ega "IV 10.6.1" "(i), condition 2° for X"]
theorem isUniversallyCatenary_of_locallyOfFiniteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian S]
    (hS : IsUniversallyCatenary S) :
    @IsUniversallyCatenary X
      (AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian f) := fun _ g _ => hS _ (g ≫ f)

end AlgebraicGeometry.Scheme
