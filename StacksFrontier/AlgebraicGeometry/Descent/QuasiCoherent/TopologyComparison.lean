module

public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.FinerTopologies
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.Coverings
public import StacksCore.Tactic.StacksAttribute

/-!
# Syntomic coverings are fpqc, and the sheaf condition passes to a coarser topology

Tag 03DT asserts the sheaf condition for the presheaf of Tag 03DS with respect to Zariski,
étale, smooth, syntomic, fppf and fpqc coverings.  The Stacks proof treats only the fpqc case and
obtains the other five from the comparison of coverings, since each of the five other covering
notions is fpqc.  This file supplies the two ingredients of that reduction which were missing:
the syntomic comparison, and the transfer of the sheaf condition along an inclusion of
Grothendieck topologies localized at an object.

## Main results

* `AlgebraicGeometry.isSyntomicCovering_iff_mem_precoverage` identifies the predicate of Tag 0225
  with membership of the presieve in the precoverage of syntomic morphisms, and
  `AlgebraicGeometry.isSyntomicCovering_mem_fppfPrecoverage` together with
  `AlgebraicGeometry.isSyntomicCovering_mem_fpqcPrecoverage` restate the two comparisons for a
  family satisfying that predicate.
* `Stacks.Sites.isSheaf_over_of_le`: a presheaf on `CategoryTheory.Over X` which is a sheaf for
  the localization at `X` of a topology `K` is a sheaf for the localization at `X` of every
  topology below `K`.

## Implementation notes

The syntomic comparison is stated both as an inclusion of precoverages and, for a family
satisfying `AlgebraicGeometry.IsSyntomicCovering`, as membership of the generated presieve.  The
two are not interchangeable without `AlgebraicGeometry.Scheme.ofArrows_mem_precoverage_iff`: the
predicate of Tag 0225 records joint surjectivity as an equality of the union of the ranges with
the whole space, while a precoverage records it as a pointwise existential.

`Stacks.Sites.isSheaf_over_of_le` is `CategoryTheory.Presheaf.IsSheaf.of_le` together with the
observation that `CategoryTheory.GrothendieckTopology.over` is monotone: a sieve of
`CategoryTheory.Over X` is covering for `J.over X` exactly when its image sieve of the base is
covering for `J`, so an inclusion `J ≤ K` of topologies on the base gives `J.over X ≤ K.over X`
with no condition on `X`.

## References

* [Stacks Project, Tag 021N](https://stacks.math.columbia.edu/tag/021N)
* [Stacks Project, Tag 0225](https://stacks.math.columbia.edu/tag/0225)
* [Stacks Project, Tag 022C](https://stacks.math.columbia.edu/tag/022C)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe v₂ v₁ u₂ u₁ u v

namespace AlgebraicGeometry.Scheme


end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- A family of morphisms is a syntomic covering family in the sense of Tag 0225 exactly when its
presieve belongs to the precoverage of syntomic morphisms. -/
public theorem isSyntomicCovering_iff_mem_precoverage {T : Scheme.{u}} {I : Type v}
    {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ T} :
    IsSyntomicCovering X f ↔
      Presieve.ofArrows X f ∈ Scheme.precoverage (@Syntomic : MorphismProperty Scheme.{u}) T := by
  refine Iff.trans ?_
    (Scheme.ofArrows_mem_precoverage_iff (P := (@Syntomic : MorphismProperty Scheme.{u}))).symm
  constructor
  · exact fun hf ↦ ⟨fun x ↦ by simpa using Set.eq_univ_iff_forall.mp hf.2 x, hf.1⟩
  · exact fun hf ↦ ⟨hf.2, Set.eq_univ_iff_forall.mpr fun x ↦ by simpa using hf.1 x⟩

/-- Every syntomic covering family in the sense of Tag 0225 is an fppf covering family.  This is
`AlgebraicGeometry.Scheme.syntomicPrecoverage_le_fppfPrecoverage` read through
`AlgebraicGeometry.isSyntomicCovering_iff_mem_precoverage`. -/
public theorem isSyntomicCovering_mem_fppfPrecoverage {T : Scheme.{u}} {I : Type v}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T) (hf : IsSyntomicCovering X f) :
    Presieve.ofArrows X f ∈ Scheme.fppfPrecoverage T :=
  Scheme.syntomicPrecoverage_le_fppfPrecoverage _ (isSyntomicCovering_iff_mem_precoverage.mp hf)

/-- Every syntomic covering family in the sense of Tag 0225 is an fpqc covering family.  This is
the form in which the syntomic case of Tag 03DT consumes
`AlgebraicGeometry.Scheme.syntomicPrecoverage_le_fpqcPrecoverage`. -/
public theorem isSyntomicCovering_mem_fpqcPrecoverage {T : Scheme.{u}} {I : Type v}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T) (hf : IsSyntomicCovering X f) :
    Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage T :=
  Scheme.fppfPrecoverage_le_fpqcPrecoverage _ (isSyntomicCovering_mem_fppfPrecoverage X f hf)

end AlgebraicGeometry

namespace Stacks.Sites

/-- **The sheaf condition on a localized site passes to a coarser topology.**  If a presheaf on
the objects over `X` is a sheaf for the localization at `X` of a Grothendieck topology `K`, it is
a sheaf for the localization at `X` of every topology below `K`.

This is the step by which the Zariski, étale, smooth, syntomic and fppf cases of Tag 03DT follow
from its fpqc case. -/
public theorem isSheaf_over_of_le {C : Type u₁} [Category.{v₁} C] {A : Type u₂}
    [Category.{v₂} A] {J K : GrothendieckTopology C} (h : J ≤ K) (X : C)
    (F : (Over X)ᵒᵖ ⥤ A) (hF : Presheaf.IsSheaf (K.over X) F) :
    Presheaf.IsSheaf (J.over X) F :=
  Presheaf.IsSheaf.of_le (fun Y _ hR ↦ h Y.left hR) hF

end Stacks.Sites

end
