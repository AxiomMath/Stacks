module

public import StacksFrontier.Algebra.DGA.DerivedCategory
public import StacksFrontier.CategoryTheory.Localization.Saturated.Closure

/-!
# Right fractions and MS4 for the quasi-isomorphisms

Let `A` be a differential graded algebra. The quasi-isomorphisms of the homotopy category of
right differential graded `A`-modules admit a *right* calculus of fractions, and they are
multiplicative and satisfy the saturation axiom MS4.

`StacksDraft.Ch22.Sec22.Tag09KX` already supplies the *left* calculus of fractions and the
compatibility with the triangulation; this file adds the two remaining pieces of the localization
data that the general derived-functor principle of Tag 06XN takes as hypotheses, namely
`CategoryTheory.MorphismProperty.HasRightCalculusOfFractions` — the hypothesis of the left
derived half, `Stacks.DerivedFunctor.Computing.leftDerived_everywhereDefined_and_computes` — and
`CategoryTheory.MorphismProperty.IsSaturatedMultiplicative`, which both halves take.

## Main results

* `DifferentialGradedModule.quasiIsomorphisms_hasRightCalculusOfFractions`
* `DifferentialGradedModule.quasiIsomorphisms_isSaturatedMultiplicative`

## Implementation notes

Both are read off the identification of the quasi-isomorphisms with the multiplicative system
attached to the acyclic modules, `DifferentialGradedModule.acyclic_trW_eq_quasiIsomorphisms` of
Tag 09KW, exactly as Tag 09KX obtains the left calculus of fractions: rewriting backwards along
it turns the goal into a statement about `(acyclic A).trW`, where Mathlib's instance for the
multiplicative system of a triangulated subcategory of a triangulated category applies. The
triangulated structure on the homotopy category it needs is the one of Tag 09KI.

`IsSaturatedMultiplicative` is strictly weaker than the `IsSaturated` of Tag 09KW — it asks for
MS1 and MS4 but not for the Ore and cancellation conditions MS2 and MS3 — so it is obtained from
the already-proved `DifferentialGradedModule.quasiIsomorphisms_isSaturated` by
`CategoryTheory.MorphismProperty.IsSaturated.isSaturatedMultiplicative` rather than proved again.
No Stacks tag is attached here: the clause "saturated multiplicative system" of Tag 09KW is
already carried by `DifferentialGradedModule.quasiIsomorphisms_isSaturated`, and these two
results restate parts of that same content in the forms the Tag 06XN interface demands.

## References

* [Stacks Project, Tag 09KW](https://stacks.math.columbia.edu/tag/09KW)
* [Stacks Project, Tag 06XN](https://stacks.math.columbia.edu/tag/06XN)
-/

@[expose] public section

open CategoryTheory

namespace DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra.{u, v} R)

/-- The quasi-isomorphisms admit a right calculus of fractions: they are the class of morphisms
whose cone is acyclic, and the acyclic objects form a full triangulated subcategory of the
homotopy category, which is itself triangulated. This is the dual of
`DifferentialGradedModule.quasiIsomorphisms_hasLeftCalculusOfFractions`, and it is the
localization hypothesis of the left derived half of Tag 06XN. -/
instance quasiIsomorphisms_hasRightCalculusOfFractions :
    (quasiIsomorphisms.{u, v, w} A).HasRightCalculusOfFractions := by
  rw [← acyclic_trW_eq_quasiIsomorphisms A]
  infer_instance

/-- The quasi-isomorphisms are multiplicative and satisfy the saturation axiom MS4: if `f ≫ g`
and `g ≫ h` are quasi-isomorphisms, so is `g`. This is the weakening of
`DifferentialGradedModule.quasiIsomorphisms_isSaturated` that both halves of Tag 06XN take as a
hypothesis. -/
theorem quasiIsomorphisms_isSaturatedMultiplicative :
    (quasiIsomorphisms.{u, v, w} A).IsSaturatedMultiplicative :=
  (quasiIsomorphisms_isSaturated.{u, v, w} A).isSaturatedMultiplicative

end DifferentialGradedModule

end
