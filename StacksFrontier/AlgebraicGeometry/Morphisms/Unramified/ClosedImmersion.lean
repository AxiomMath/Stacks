module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Closed immersions are unramified

A closed immersion of schemes is unramified, and it is G-unramified exactly when its ideal
sheaf is of finite type as a module over the structure sheaf of the target.

## Main results

* `AlgebraicGeometry.unramified_of_isClosedImmersion` says that a closed immersion is
  unramified.
* `AlgebraicGeometry.gUnramified_iff_isFiniteType_idealSheaf` characterizes G-unramified closed
  immersions by finite type of their ideal sheaves.

## Implementation notes

The ideal sheaf is the categorical kernel of the map from the structure sheaf of the target to
the pushforward of the structure sheaf of the source. The two independent assertions of the
source are stated separately; unramifiedness is a class, so the first is an instance.

A closed immersion is a monomorphism, hence formally unramified, and it is of finite type, so
the first assertion is immediate from the conjunctive description of unramifiedness. For the
second, local finite presentation of a closed immersion is equivalent to finite presentation,
which is equivalent to finite type of the ideal sheaf.

## References

* [Stacks Project, Tag 02GC](https://stacks.math.columbia.edu/tag/02GC)
* [Stacks Project, Tag 01TV](https://stacks.math.columbia.edu/tag/01TV)
* [Stacks Project, Tag 02HE](https://stacks.math.columbia.edu/tag/02HE)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A closed immersion of schemes is unramified. -/
@[stacks 02GC "unramified", ega "IV 17.3.3" "(i), special case"]
instance unramified_of_isClosedImmersion {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] : Unramified i :=
  (unramified_iff_locallyOfFiniteType_and_formallyUnramified i).2 ⟨inferInstance, inferInstance⟩

/-- A closed immersion of schemes is G-unramified exactly when its ideal sheaf is of finite
type. -/
@[stacks 02GC "G-unramified iff finite-type ideal sheaf"]
theorem gUnramified_iff_isFiniteType_idealSheaf {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    GUnramified i ↔ (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).IsFiniteType := by
  rw [gUnramified_iff_locallyOfFinitePresentation_and_formallyUnramified,
    ← finitePresentation_iff_isFiniteType_idealSheaf i]
  exact ⟨fun h => ⟨h.1, inferInstance, inferInstance⟩, fun h => ⟨h.1, inferInstance⟩⟩

end AlgebraicGeometry
