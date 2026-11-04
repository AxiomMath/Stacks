module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDescent
public import StacksFrontier.CategoryTheory.Sites.Stack.EffectiveDescentRefinement
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge

/-!
# `Coh_{X/Y}` is a stack in groupoids

**Stacks 08KC.**  In Situation 08KB the category `Coh_{X/Y}` of triples `(T, g, F)`, with its
projection `(T, g, F) ↦ T` to the big fppf site of `S`, is a stack in groupoids.

The projection is fibred in groupoids by Stacks 08W5.  Its morphism presheaves are sheaves by
`AlgebraicGeometry.Space.CoherentSituation.isMorSheaf` (the statement on `Isom` of the source),
and a descent datum relative to an arbitrary covering sieve is effective because it is effective
relative to a covering family contained in the sieve whose members form an fpqc covering
(`AlgebraicGeometry.Space.CoherentSituation.isEffective_of_isFpqcCovering`, the statement on
descent data of the source), the morphism presheaves being sheaves
(`CategoryTheory.Functor.hasEffectiveDescent_of_familyRefinements`).  This is a stack in the
sense of Stacks 026F, hence, being fibred in groupoids, a stack in groupoids in the sense of
Stacks 02ZI (`CategoryTheory.Functor.IsStack.isStackInGroupoids`).

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.isStack`: the form of Stacks 026F.
* `AlgebraicGeometry.Space.CoherentSituation.isStackInGroupoids`: **Stacks 08KC.**

## References

* [Stacks Project, Tag 08KC](https://stacks.math.columbia.edu/tag/08KC)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace CoherentSituation

variable (D : CoherentSituation B S hS)

/-- **`Coh_{X/Y}` is a stack in the sense of Stacks 026F** over the big fppf site of `S`. -/
theorem isStack :
    (coherentBasedCategory D.categoryData).p.IsStack (BigFppfOver.topology B S hS) := by
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  have : (coherentBasedCategory D.categoryData).p.IsFibered :=
    D.isFiberedInGroupoids_siteProjection.isFibered
  refine ⟨inferInstance, D.isMorSheaf,
    Functor.hasEffectiveDescent_of_familyRefinements D.isMorSheaf fun U R hR => ?_⟩
  obtain ⟨L, V, f, hfR, hcov, hfpqc⟩ := exists_fpqc_family R hR
  exact ⟨L, V, f, hfR, hcov, fun E => isEffective_of_isFpqcCovering f hcov hfpqc E⟩

/-- **Stacks 08KC.**  In Situation 08KB the projection `Coh_{X/Y} ⟶ (Sch/S)_fppf`,
`(T, g, F) ↦ T`, makes the category `Coh_{X/Y}` of Stacks 08KB a stack in groupoids over the big
fppf site of `S`. -/
@[stacks 08KC]
theorem isStackInGroupoids :
    (coherentBasedCategory D.categoryData).p.IsStackInGroupoids.{w}
      (BigFppfOver.topology B S hS) := by
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  exact Functor.IsStack.isStackInGroupoids D.isStack D.isFiberedInGroupoids_siteProjection

end CoherentSituation

end AlgebraicGeometry.Space

end
