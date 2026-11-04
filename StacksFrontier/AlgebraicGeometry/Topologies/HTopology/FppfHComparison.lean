module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.FinerTopologies
public import StacksFrontier.AlgebraicGeometry.Topologies.H.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.V.FppfAffineDomination

/-!
# Fppf coverings are h coverings

An h covering is a family of morphisms of schemes that is locally of finite presentation
member by member and is a ph covering.  Both conditions hold for an fppf covering: local
finite presentation is part of the definition of an fppf covering family, and an fppf covering
is a ph covering by Stacks 0DBT.  Since syntomic, smooth, étale and Zariski covering families
are fppf covering families (Stacks 021N), they are h coverings too.

## Main results

* `AlgebraicGeometry.IsHCovering.of_fppf_syntomic_smooth_etale_zariski`: Stacks 0ETV, an fppf
  covering is an h covering, and hence so are syntomic, smooth, étale and Zariski coverings.
* `AlgebraicGeometry.IsHCovering.of_mem_fppfPrecoverage`: an fppf covering is an h covering.
* `AlgebraicGeometry.IsHCovering.of_mem_syntomicPrecoverage`,
  `AlgebraicGeometry.IsHCovering.of_mem_smoothPrecoverage` and
  `AlgebraicGeometry.IsHCovering.of_mem_zariskiPrecoverage`: the syntomic, smooth and Zariski
  consequences, one at a time.

## Implementation notes

A covering family is presented by the membership of its presieve `Presieve.ofArrows X f` in
the relevant precoverage, which is the form the comparisons of Stacks 021N are stated in, so
each of the four consequences is one application of the fppf case.

The étale consequence also has a proof that avoids the fppf case:
`AlgebraicGeometry.isHCovering_of_etale` in
`StacksFrontier.AlgebraicGeometry.Topologies.HTopology.EtaleHComparison`, where the étale case of
Stacks 0DBT comes from the finite locally free domination of Stacks 02LH.

## References

* [Stacks Project, Tag 021N](https://stacks.math.columbia.edu/tag/021N)
* [Stacks Project, Tag 0DBT](https://stacks.math.columbia.edu/tag/0DBT)
* [Stacks Project, Tag 0ETS](https://stacks.math.columbia.edu/tag/0ETS)
* [Stacks Project, Tag 0ETV](https://stacks.math.columbia.edu/tag/0ETV)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-- An fppf covering of schemes is an h covering.

The members of an fppf covering are flat and locally of finite presentation, which supplies
the local finite presentation half of the definition of an h covering, and the family is a ph
covering by `AlgebraicGeometry.IsPHCovering.of_mem_fppfPrecoverage`, Stacks 0DBT. -/
public theorem IsHCovering.of_mem_fppfPrecoverage {T : Scheme.{u}} {I : Type v}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hf : Presieve.ofArrows X f ∈ Scheme.fppfPrecoverage T) :
    IsHCovering X f :=
  ⟨fun i ↦ (((Scheme.ofArrows_mem_precoverage_iff
      (P := @Flat ⊓ @LocallyOfFinitePresentation)).mp hf).2 i).2,
    IsPHCovering.of_mem_fppfPrecoverage X f hf⟩

/-- A syntomic covering of schemes is an h covering: it is an fppf covering by Stacks 021N. -/
public theorem IsHCovering.of_mem_syntomicPrecoverage {T : Scheme.{u}} {I : Type v}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hf : Presieve.ofArrows X f ∈
      Scheme.precoverage (@Syntomic : MorphismProperty Scheme.{u}) T) :
    IsHCovering X f :=
  .of_mem_fppfPrecoverage X f (Scheme.syntomicPrecoverage_le_fppfPrecoverage _ hf)

/-- A smooth covering of schemes is an h covering: it is an fppf covering by Stacks 021N. -/
public theorem IsHCovering.of_mem_smoothPrecoverage {T : Scheme.{u}} {I : Type v}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hf : Presieve.ofArrows X f ∈
      Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}) T) :
    IsHCovering X f :=
  .of_mem_fppfPrecoverage X f (Scheme.smoothPrecoverage_le_fppfPrecoverage _ hf)

/-- A Zariski covering of schemes is an h covering: it is an fppf covering by Stacks 021N. -/
public theorem IsHCovering.of_mem_zariskiPrecoverage {T : Scheme.{u}} {I : Type v}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hf : Presieve.ofArrows X f ∈ Scheme.zariskiPrecoverage T) :
    IsHCovering X f :=
  .of_mem_fppfPrecoverage X f (Scheme.zariskiPrecoverage_le_fppfPrecoverage _ hf)

/-- **[Stacks, Tag 0ETV].** An fppf covering is an h covering. Hence syntomic, smooth, étale
and Zariski coverings are h coverings as well.

Here a family `{f i : X i ⟶ T}` is an fppf (resp. syntomic, smooth, étale, Zariski) covering
when its members are flat and locally of finite presentation (resp. syntomic, smooth, étale,
open immersions) and jointly surjective, that is, when `Presieve.ofArrows X f` belongs to the
corresponding precoverage; it is an h covering, `AlgebraicGeometry.IsHCovering` (Stacks 0ETS),
when its members are locally of finite presentation and it is a ph covering (Stacks 0DBG).

The fppf case holds because the members of an fppf covering are locally of finite
presentation and an fppf covering is a ph covering, Stacks 0DBT; the other four follow from it
and Stacks 021N. -/
@[stacks 0ETV]
public theorem IsHCovering.of_fppf_syntomic_smooth_etale_zariski {T : Scheme.{u}} {I : Type v}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T) :
    (Presieve.ofArrows X f ∈ Scheme.fppfPrecoverage T → IsHCovering X f) ∧
    (Presieve.ofArrows X f ∈
      Scheme.precoverage (@Syntomic : MorphismProperty Scheme.{u}) T → IsHCovering X f) ∧
    (Presieve.ofArrows X f ∈
      Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}) T → IsHCovering X f) ∧
    (Presieve.ofArrows X f ∈ Scheme.etalePrecoverage T → IsHCovering X f) ∧
    (Presieve.ofArrows X f ∈ Scheme.zariskiPrecoverage T → IsHCovering X f) :=
  ⟨.of_mem_fppfPrecoverage X f, .of_mem_syntomicPrecoverage X f,
    .of_mem_smoothPrecoverage X f,
    fun hf ↦ .of_mem_fppfPrecoverage X f (Scheme.etalePrecoverage_le_fppfPrecoverage _ hf),
    .of_mem_zariskiPrecoverage X f⟩

end AlgebraicGeometry

end
