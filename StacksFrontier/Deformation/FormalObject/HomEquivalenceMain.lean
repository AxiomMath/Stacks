module

public import StacksFrontier.Deformation.FormalObject.HomEquivalenceCounit
public import StacksFrontier.Deformation.FormalObject.HomEquivalenceUnit

/-!
# Completion and restriction are 2-adjoint on hom categories (Stacks 06HA)

Completion of a category cofibered in groupoids over Artinian local algebras is, on hom
categories, left adjoint to restriction from complete local algebras to Artinian local
algebras.  The two comparison isomorphisms are built in
`StacksFrontier.Deformation.FormalObject.HomEquivalenceUnit` and
`StacksFrontier.Deformation.FormalObject.HomEquivalenceCounit`; here they are assembled into
the equivalence of hom categories together with the canonical formulas for both
directions.

## Main results

* `completionHomEquivalence`: **Stacks 06HA**.

## References

* [Stacks Project, Tag 06HA](https://stacks.math.columbia.edu/tag/06HA)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v w uF vF uG vG

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
  (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
variable {G : Type uG} [Category.{vG} G]
  (q : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k)

/-- **Stacks Project, Tag 06HA (hom equivalence).** Completion and restriction
induce quasi-inverse equivalences on hom categories, with the forward and
backward formulas specified above. -/
@[stacks 06HA "hom_equivalence"]
public noncomputable def completionHomEquivalence
    (hp : IsCofiberedInGroupoids p)
    (hq : IsCofiberedInGroupoids q) :
    CompletionHomEquivalence p q hp hq :=
  completionHomEquivalenceOfIsos p q hp hq
    (completionHomUnitIso p q hp hq) (completionHomCounitIso p q hp hq)

end

end Deformation

end
