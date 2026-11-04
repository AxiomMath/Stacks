module

public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
import all StacksFrontier.CategoryTheory.Sites.Glueing.GlueingSheaves

/-!
# Morphisms of sheaves on slice sites glue

The pseudofunctor `J.pseudofunctorOver A` of sheaves on the slice sites of a site is a prestack:
its presheaves of morphisms are sheaves, being the internal hom sheaves of the slice sites. This
is Stacks 04TQ, and it needs no assumption on the coefficient category `A`.

The proof is the one of the descent equivalence for glued sheaves
(`Stacks.SheafGluing.DescentEquivalence`): restriction along the iterated slice equivalence
`C/T.left ≌ (C/S)/T` identifies the presheaf of morphisms of the pseudofunctor with the internal
hom presheaf.

## Main results

* `CategoryTheory.GrothendieckTopology.isPrestack_pseudofunctorOver` — the prestack property.

## References

* [Stacks Project, Tag 04TQ](https://stacks.math.columbia.edu/tag/04TQ)
-/

@[expose] public noncomputable section

universe u v u' v'

namespace CategoryTheory.GrothendieckTopology

/-- **Maps of sheaves glue (Stacks 04TQ).** The pseudofunctor of sheaves on the slice sites is a
prestack, for any coefficient category. -/
public theorem isPrestack_pseudofunctorOver {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (A : Type u') [Category.{v'} A] :
    (J.pseudofunctorOver A).IsPrestack J :=
  Stacks.SheafGluing.DescentEquivalence.isPrestack J A

end CategoryTheory.GrothendieckTopology

end
