module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.Coverings

/-!
# Smooth, étale, and Zariski coverings are syntomic coverings

Every smooth covering of a scheme is a syntomic covering. Consequently, the same is true of
every étale covering and every Zariski covering.

## Main results

* `AlgebraicGeometry.isSyntomicCovering_of_mem_smoothPrecoverage` says that a smooth covering
  is syntomic.
* `AlgebraicGeometry.isSyntomicCovering_of_mem_etalePrecoverage` says that an étale covering
  is syntomic.
* `AlgebraicGeometry.isSyntomicCovering_of_mem_zariskiPrecoverage` says that a Zariski
  covering is syntomic.

## Implementation notes

Smooth, étale, and Zariski covering families are expressed as membership of their families of
arrows in Mathlib's corresponding precoverages. The conclusion uses the syntomic-covering
predicate `AlgebraicGeometry.IsSyntomicCovering`. The last two statements follow from the
first by monotonicity of the precoverage in the morphism property.

## References

* [Stacks Project, Tag 0226](https://stacks.math.columbia.edu/tag/0226)
-/

@[expose] public section

open CategoryTheory MorphismProperty

universe u v

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0226.** Every smooth covering is a syntomic covering. -/
@[stacks 0226 "smooth coverings"]
public theorem isSyntomicCovering_of_mem_smoothPrecoverage
    {T : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ T}
    (hf : Presieve.ofArrows X f ∈ Scheme.precoverage (@Smooth.{u}) T) :
    IsSyntomicCovering X f := by
  obtain ⟨hc, hs⟩ := (Scheme.ofArrows_mem_precoverage_iff (P := @Smooth.{u})).mp hf
  exact ⟨fun i => @syntomic_of_smooth _ _ (f i) (hs i),
    by simpa only [Set.eq_univ_iff_forall, Set.mem_iUnion] using hc⟩

/-- **Stacks Project, Tag 0226.** Every étale covering is a syntomic covering. -/
@[stacks 0226 "étale coverings"]
public theorem isSyntomicCovering_of_mem_etalePrecoverage
    {T : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ T}
    (hf : Presieve.ofArrows X f ∈ Scheme.etalePrecoverage T) :
    IsSyntomicCovering X f :=
  isSyntomicCovering_of_mem_smoothPrecoverage
    (Scheme.precoverage_mono (P := @Etale.{u}) (Q := @Smooth.{u})
      (fun _ _ _ hg => let := hg; inferInstance) T hf)

/-- **Stacks Project, Tag 0226.** Every Zariski covering is a syntomic covering. -/
@[stacks 0226 "Zariski coverings"]
public theorem isSyntomicCovering_of_mem_zariskiPrecoverage
    {T : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ T}
    (hf : Presieve.ofArrows X f ∈ Scheme.zariskiPrecoverage T) :
    IsSyntomicCovering X f :=
  isSyntomicCovering_of_mem_smoothPrecoverage
    (Scheme.precoverage_mono (P := @IsOpenImmersion.{u}) (Q := @Smooth.{u})
      (fun _ _ _ hg => let := hg; inferInstance) T hf)

end AlgebraicGeometry
