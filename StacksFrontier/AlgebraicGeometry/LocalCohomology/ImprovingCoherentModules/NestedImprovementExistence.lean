module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtensionConstruction
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.NestedImprovementComposition
public import StacksCore.Tactic.StacksAttribute

/-!
# Existence of the improvement, at the hypotheses of the source

Let `X` be a Noetherian scheme which locally has a dualizing complex and let `T' ⊆ T ⊆ X` be
subsets stable under specialization such that every immediate specialization `x ⤳ x'` with
`x' ∈ T'` has `x ∈ T`.  A coherent `𝒪_X`-module `F` then admits an improvement along `T' ⊆ T`,
which is `AlgebraicGeometry.IsNestedImprovement`.

That is the existence half of [Stacks, Tag 0EI4], and the source proves it by composing two
constructions: the depth-one quotient of `F` along `T` ([Stacks, Tag 0DX3]) and a depth-two
extension of that quotient along `T'` ([Stacks, Tag 0EI3]).  Both are available in this library —
the first as `AlgebraicGeometry.depthOneQuotient`, the second as
`AlgebraicGeometry.exists_isDepthTwoExtension_of_hasDualizingComplex` — and the composition is
`AlgebraicGeometry.isNestedImprovement_depthOneQuotient_comp`, which needs no hypothesis beyond
`T' ⊆ T`.  This module carries out that composition.

## Main results

* `AlgebraicGeometry.exists_isNestedImprovement_of_hasDualizingComplex`:
  **[Stacks, Tag 0EI4], existence**, at the hypotheses of the source and no others.
* `AlgebraicGeometry.existsUnique_isNestedImprovement_of_hasDualizingComplex`:
  **[Stacks, Tag 0EI4], the source's unique map**, existence and uniqueness together at those
  same hypotheses.

## Implementation notes

The depth hypothesis of [Stacks, Tag 0EI3] is checked for the depth-one quotient `F'` of `F`
along `T`, not for `F`: an immediate specialization `x ⤳ x'` with `x' ∈ T'` has `x ∈ T` by the
hypothesis of [Stacks, Tag 0EI4], and `F'` has depth at least one at every point of `T` by
[Stacks, Tag 0DX3].  This is the only use of that hypothesis of [Stacks, Tag 0EI4], and it is why
`T'` is allowed to be smaller than `T`.

This statement once carried a hypothesis `AlgebraicGeometry.HasClosedLowDepthLocus T' F'`, the
one input [Stacks, Tag 0EI3] used to assume beyond the source's.  It is now discharged inside
[Stacks, Tag 0EI3] itself by
`AlgebraicGeometry.hasClosedLowDepthLocus_of_hasDualizingComplex`, so nothing of it survives
here and this statement is at the hypotheses of the source alone.

The dualizing hypothesis is the source's, in the form [Stacks, Tag 0EI3] consumes:
`AlgebraicGeometry.HasDualizingComplexOnAffineCover`, every point having an affine neighbourhood
whose sections admit a dualizing complex.  This statement once asked for the strictly stronger
`AlgebraicGeometry.LocallyHasDualizingComplex` — every affine open, not merely a cover — and
converted it with
`AlgebraicGeometry.hasDualizingComplexOnAffineCover_of_locallyHasDualizingComplex`.  Since
[Stacks, Tag 0EI3] only ever needed the cover form, the conversion was a strengthening of this
theorem's hypothesis that bought nothing, and it is gone.  The converse passage is not available
in this library, so the distinction is not idle: proving this from the stronger form would not
have proved it at the source's hypotheses.

## References

* [Stacks Project, Tag 0EI4](https://stacks.math.columbia.edu/tag/0EI4)
* [Stacks Project, Tag 0EI3](https://stacks.math.columbia.edu/tag/0EI3)
* [Stacks Project, Tag 0DX3](https://stacks.math.columbia.edu/tag/0DX3)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0EI4, existence, at the hypotheses of the source.** Let `X` be a
Noetherian scheme which locally has a dualizing complex and let `T' ⊆ T ⊆ X` be stable under
specialization and such that every immediate specialization into `T'` starts in `T`.  Then a
coherent `𝒪_X`-module `F` admits a map to a coherent module which is an isomorphism on the
stalks away from `T`, is surjective on the stalks with target of depth at least one at the
points of `T` outside `T'`, and has target of depth at least two at the points of `T'`.

The map is the depth-one quotient of `F` along `T` followed by a depth-two extension of that
quotient along `T'`, which is the source's construction: the first step is [Stacks, Tag 0DX3],
the second is the existence half of [Stacks, Tag 0EI3] in the form
`AlgebraicGeometry.exists_isDepthTwoExtension_of_hasDualizingComplex`, and the composition is
`AlgebraicGeometry.isNestedImprovement_depthOneQuotient_comp`.

The dualizing hypothesis is `AlgebraicGeometry.HasDualizingComplexOnAffineCover`, which says
every point has an affine open neighbourhood whose ring of sections admits a dualizing complex.
That is the source's phrase "locally has a dualizing complex", and it is **weaker** than
`AlgebraicGeometry.LocallyHasDualizingComplex`, which asks this of *every* affine open. -/
public theorem exists_isNestedImprovement_of_hasDualizingComplex
    (X : Scheme.{u}) [IsNoetherian X] (hdual : HasDualizingComplexOnAffineCover X)
    (T T' : Set X) (hTT' : T' ⊆ T)
    (hT : StableUnderSpecialization T) (hT' : StableUnderSpecialization T')
    (himm : ∀ x x' : X, IsImmediateSpecialization x x' → x' ∈ T' → x ∈ T)
    (F : X.Modules) [F.IsCoherent] :
    ∃ (G : X.Modules) (φ : F ⟶ G), IsNestedImprovement T T' φ := by
  have hq := depthOneQuotient_spec X T hT F
  let : (depthOneQuotient X T hT F).IsCoherent := hq.1
  obtain ⟨H, ψ, hψ⟩ := exists_isDepthTwoExtension_of_hasDualizingComplex X hdual
    T' hT' (depthOneQuotient X T hT F)
    (fun x x' himmx hx' _ => hq.2.2.2 x (himm x x' himmx hx'))
  exact ⟨H, _, isNestedImprovement_depthOneQuotient_comp X T T' hTT' hT F ψ hψ⟩

/-- **Stacks Project, Tag 0EI4, the source's unique map.** Under the hypotheses of
`AlgebraicGeometry.exists_isNestedImprovement_of_hasDualizingComplex` there is a map `F ⟶ F''`
of coherent modules which is an isomorphism on the stalks away from `T`, is surjective on the
stalks with target of depth at least one at the points of `T` outside `T'`, and has target of
depth at least two at the points of `T'`; and it is unique: any other such map is carried to it
by a unique isomorphism under `F`.

This is the source's sentence "there exists a unique map" in one statement.  Existence is
`AlgebraicGeometry.exists_isNestedImprovement_of_hasDualizingComplex` and uniqueness is
`AlgebraicGeometry.nestedImprovement_unique`, which needs neither the dualizing complex, nor the
condition on immediate specializations, nor `T' ⊆ T`. -/
public theorem existsUnique_isNestedImprovement_of_hasDualizingComplex
    (X : Scheme.{u}) [IsNoetherian X] (hdual : HasDualizingComplexOnAffineCover X)
    (T T' : Set X) (hTT' : T' ⊆ T)
    (hT : StableUnderSpecialization T) (hT' : StableUnderSpecialization T')
    (himm : ∀ x x' : X, IsImmediateSpecialization x x' → x' ∈ T' → x ∈ T)
    (F : X.Modules) [F.IsCoherent] :
    ∃ (G : X.Modules) (φ : F ⟶ G), IsNestedImprovement T T' φ ∧
      ∀ (H : X.Modules) (ψ : F ⟶ H), IsNestedImprovement T T' ψ →
        ∃! e : G ≅ H, φ ≫ e.hom = ψ := by
  obtain ⟨G, φ, hφ⟩ :=
    exists_isNestedImprovement_of_hasDualizingComplex X hdual T T' hTT' hT hT' himm F
  exact ⟨G, φ, hφ, fun H ψ hψ => nestedImprovement_unique X T T' hT F G H φ ψ hφ hψ⟩

end AlgebraicGeometry

end
