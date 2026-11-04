module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.TopologyComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.StandardRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.V.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Vtopology.StandardFpqcCoverings
public import StacksCore.Tactic.StacksAttribute

/-!
# Fpqc coverings are V coverings

Every fpqc covering is a V covering, and hence so is every fppf, syntomic, smooth, étale or
Zariski covering, each of those being fpqc.

## Main results

* `AlgebraicGeometry.isVCovering_of_mem_fpqcPrecoverage`: every fpqc covering is a V covering.
* `AlgebraicGeometry.isVCovering_of_mem_fppfPrecoverage`,
  `AlgebraicGeometry.isVCovering_of_mem_syntomicPrecoverage`,
  `AlgebraicGeometry.isVCovering_of_mem_smoothPrecoverage`,
  `AlgebraicGeometry.isVCovering_of_mem_etalePrecoverage` and
  `AlgebraicGeometry.isVCovering_of_mem_zariskiPrecoverage`: the five a fortiori statements.

## Implementation notes

Both notions are affine-local on the target, so the proof is the comparison of the two
refinement conditions above a fixed affine open `U` of the target.  On the fpqc side,
`AlgebraicGeometry.presieve₀_mem_fpqcPrecoverage_iff_affine_refinements`, the characterization
packaging Stacks 022E, produces above `U` a finite standard fpqc covering refining the base
change of the family along `U.ι`; on the V side,
`AlgebraicGeometry.isStandardVCovering_of_flat_affineCover`, Stacks 0ETC, says that this
standard fpqc covering is a standard V covering.  The two refinement data have the same shape,
a `CategoryTheory.PreZeroHypercover.Hom` into the base change `pullback₂` of the given family,
so the only step left is a change of the index universe: Stacks 022E hands back an index in
`Type 0` whereas `AlgebraicGeometry.IsVCovering` asks for a
`CategoryTheory.PreZeroHypercover.{u}`.  The index is transported by
`AlgebraicGeometry.Scheme.AffineCover.reindex` along an equivalence supplied by
`Small.equiv_small`, which applies because the index is finite.

The five a fortiori statements are each one application of the corresponding comparison of
precoverages, Stacks 022C.

## References

* [Stacks Project, Tag 022C](https://stacks.math.columbia.edu/tag/022C)
* [Stacks Project, Tag 022E](https://stacks.math.columbia.edu/tag/022E)
* [Stacks Project, Tag 0ETC](https://stacks.math.columbia.edu/tag/0ETC)
* [Stacks Project, Tag 0ETK](https://stacks.math.columbia.edu/tag/0ETK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-- **Stacks 0ETK.** Every fpqc covering is a V covering.

Above an affine open of the target, Stacks 022E refines the base change of the family by a
standard fpqc covering, and Stacks 0ETC says that a standard fpqc covering is a standard V
covering. -/
@[stacks 0ETK "fpqc_v"]
public theorem isVCovering_of_mem_fpqcPrecoverage {T : Scheme.{u}} {I : Type v}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage T) :
    IsVCovering X f := by
  intro U hU
  have : IsAffine U.toScheme := hU
  obtain ⟨-, hrefine⟩ := (presieve₀_mem_fpqcPrecoverage_iff_affine_refinements
    ({ I₀ := I, X := X, f := f } : PreZeroHypercover.{v} T)).mp hf
  obtain ⟨V, hfin, ⟨φ⟩⟩ := hrefine U.ι
  obtain ⟨J, ⟨e⟩⟩ := Small.equiv_small.{u} (α := V.I₀)
  have : Finite V.I₀ := hfin
  let W : U.toScheme.AffineCover.{u} (@Flat.{u}) := V.reindex e.symm
  have hWfin : Finite W.I₀ := Finite.of_equiv V.I₀ e
  refine ⟨W.cover.toPreZeroHypercover, hWfin, fun j ↦ inferInstanceAs (IsAffine (Spec (W.X j))),
    isStandardVCovering_of_flat_affineCover W, ⟨?_⟩⟩
  exact
    { s₀ j := φ.s₀ (e.symm j)
      h₀ j := φ.h₀ (e.symm j)
      w₀ j := φ.w₀ (e.symm j) }

/-- **Stacks 0ETK.** Every fppf covering is a V covering, being an fpqc covering by
Stacks 022C. -/
@[stacks 0ETK "fppf_v"]
public theorem isVCovering_of_mem_fppfPrecoverage {T : Scheme.{u}} {I : Type v}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hf : Presieve.ofArrows X f ∈ Scheme.fppfPrecoverage T) :
    IsVCovering X f :=
  isVCovering_of_mem_fpqcPrecoverage X f (Scheme.fppfPrecoverage_le_fpqcPrecoverage T hf)

/-- **Stacks 0ETK.** Every syntomic covering is a V covering, being an fpqc covering by
Stacks 022C. -/
@[stacks 0ETK "syntomic_v"]
public theorem isVCovering_of_mem_syntomicPrecoverage {T : Scheme.{u}} {I : Type v}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hf : Presieve.ofArrows X f ∈
      Scheme.precoverage (@Syntomic : MorphismProperty Scheme.{u}) T) :
    IsVCovering X f :=
  isVCovering_of_mem_fpqcPrecoverage X f (Scheme.syntomicPrecoverage_le_fpqcPrecoverage T hf)

/-- **Stacks 0ETK.** Every smooth covering is a V covering, being an fpqc covering by
Stacks 022C. -/
@[stacks 0ETK "smooth_v"]
public theorem isVCovering_of_mem_smoothPrecoverage {T : Scheme.{u}} {I : Type v}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hf : Presieve.ofArrows X f ∈
      Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}) T) :
    IsVCovering X f :=
  isVCovering_of_mem_fpqcPrecoverage X f (Scheme.smoothPrecoverage_le_fpqcPrecoverage T hf)

/-- **Stacks 0ETK.** Every étale covering is a V covering, being an fpqc covering by
Stacks 022C. -/
@[stacks 0ETK "etale_v"]
public theorem isVCovering_of_mem_etalePrecoverage {T : Scheme.{u}} {I : Type v}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hf : Presieve.ofArrows X f ∈ Scheme.etalePrecoverage T) :
    IsVCovering X f :=
  isVCovering_of_mem_fpqcPrecoverage X f (Scheme.etalePrecoverage_le_fpqcPrecoverage T hf)

/-- **Stacks 0ETK.** Every Zariski covering is a V covering, being an fpqc covering by
Stacks 022C. -/
@[stacks 0ETK "zariski_v"]
public theorem isVCovering_of_mem_zariskiPrecoverage {T : Scheme.{u}} {I : Type v}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hf : Presieve.ofArrows X f ∈ Scheme.zariskiPrecoverage T) :
    IsVCovering X f :=
  isVCovering_of_mem_fpqcPrecoverage X f (Scheme.zariskiPrecoverage_le_fpqcPrecoverage T hf)

end AlgebraicGeometry

end
