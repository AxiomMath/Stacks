module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The diagonal of an unramified morphism

The diagonal of an unramified morphism of schemes is an open immersion. Conversely, a morphism
with open diagonal is unramified as soon as it is locally of finite type, and G-unramified as
soon as it is locally of finite presentation.

## Main results

* `AlgebraicGeometry.Unramified.isOpenImmersion_diagonal`: the diagonal of an unramified
  morphism is an open immersion.
* `AlgebraicGeometry.Unramified.of_isOpenImmersion_diagonal`: the converse under local finite
  type.
* `AlgebraicGeometry.GUnramified.of_isOpenImmersion_diagonal`: the converse under local finite
  presentation.

## References

* [Stacks Project, Tag 02GE](https://stacks.math.columbia.edu/tag/02GE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Unramified

/-- The diagonal of an unramified morphism is an open immersion. -/
@[stacks 02GE "part (1)",
  ega "IV 17.4.2" "a) ⇒ b)",
  sga "3 XI 1.3" "(a) => (b)",
  ega "IV 17.4.1" "a) => b)", sga "1 I 3.4" "diagonal case (g = id)", sga "1 I 3.1" "(ii) => (iii)"]
public instance isOpenImmersion_diagonal {X S : Scheme.{u}} (f : X ⟶ S) [Unramified f] :
    IsOpenImmersion (pullback.diagonal f) := by
  let h := (unramified_iff_locallyOfFiniteType_and_formallyUnramified f).mp inferInstance
  have := h.1; have := h.2; infer_instance

/-- A morphism locally of finite type whose diagonal is an open immersion is unramified. -/
@[stacks 02GE "part (2)",
  ega "IV 17.4.2" "b) ⇒ a)",
  sga "3 XI 1.3" "(b) => (a)",
  ega "IV 17.4.1.2" "diagonal => unramified",
  ega "IV 17.4.1" "b) => a)",
  sga "1 I 3.1" "(iii) => (ii)"]
public instance of_isOpenImmersion_diagonal {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsOpenImmersion (pullback.diagonal f)] :
    Unramified f :=
  (unramified_iff_locallyOfFiniteType_and_formallyUnramified f).mpr
    ⟨inferInstance, inferInstance⟩

end Unramified

namespace GUnramified

/-- A morphism locally of finite presentation whose diagonal is an open immersion is
G-unramified. -/
@[stacks 02GE "part (3)",
  ega "IV 17.4.2" "b) ⇒ a)",
  ega "IV 17.4.1" "b) => a)",
  sga "3 XI 1.3" "(b) => (a)", sga "1 I 3.1" "(iii)=>(ii), fin pres"]
public instance of_isOpenImmersion_diagonal {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [IsOpenImmersion (pullback.diagonal f)] :
    GUnramified f :=
  (gUnramified_iff_locallyOfFinitePresentation_and_formallyUnramified f).mpr
    ⟨inferInstance, inferInstance⟩

end GUnramified

end AlgebraicGeometry

end
