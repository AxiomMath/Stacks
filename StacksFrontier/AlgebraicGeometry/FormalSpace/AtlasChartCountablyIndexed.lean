module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasChartRefinementCountableCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ChartMapCompletedEtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransferRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyRefined

/-!
# Countable indexing of the charts of a locally countably indexed formal algebraic space

Let `S` be a scheme contained in a big fppf site `B`. For a formal algebraic space `X` over
`S`, every affine formal algebraic space representable étale over `X` is countably indexed
exactly when `X` admits an atlas as in Definition **Stacks 0AIM** all of whose members are
countably indexed. This is **Stacks 0AKX** at the property of being countably indexed.

## Main results

* `hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty_isCountablyIndexed`:
  **Stacks 0AKX** at countable indexing.
* `isCountablyIndexed_of_isRepresentableEtale_of_isLocallyCountablyIndexed`: the implication
  (2) ⟹ (1), in the shape its consumers take.
* `hasEtaleRefinementOfSourceCover_isCountablyWeaklyAdmissible`:
  `AlgebraicGeometry.FormalSpace.HasEtaleRefinementOfSourceCover'` at `C = WAdmᶜᵒᵘⁿᵗ`, with
  nothing assumed.

## What is assumed

Nothing. Every input is a theorem of this library:

* the refinement half of the implication (2) ⟹ (1) —
  `…exists_countablyIndexed_surjective_flat_over_chart`, which rests on **Stacks 0AJ3** in its
  chart form, clause (1) of **Stacks 0AKQ**, the implication (1) ⟹ (2) of **Stacks 0AJ9** and
  the coproduct stability of countable indexing;
* the transfer of countable indexing along the surjective flat morphism that refinement
  produces — `…isCountablyIndexed_iff_of_surjective_flat`, **Stacks 0AKS**, whose forward
  implication is the source's cofinality argument
  `…isCountablyIndexed_target_of_surjective_flat`;
* the presented refinement of a covering of the source —
  `…exists_finite_affineEtaleRefinement_completedEtaleCover_of_sourceCover`, whose two
  remaining hypotheses `hUcount` and `hVcount` are exactly the implication (2) ⟹ (1) proved
  here.

## Implementation notes

Stacks 0AKX is registered here **at the concrete property `IsCountablyIndexed`** and not at an
arbitrary `P`. The general statement
`…hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty` carries two hypotheses, and
the refinement one of them asks for is *false* at arbitrary `P`, so the tag as quantified over
all `P` does not hold. At `P = IsCountablyIndexed` both hypotheses are
theorems, so the instantiation is unconditional; it is the instantiation, never the
generalisation, that may be registered.

The standing hypothesis `hX` that `X` is a formal algebraic space is the source's own: Stacks
0AKX is stated for a formal algebraic space over `S`. It is not implied by the atlas data
alone, which additionally carries the set-theoretic condition of Stacks 0AIS.

`hasEtaleRefinementOfSourceCover_isCountablyWeaklyAdmissible` carries no tag: the predicate it
proves is a step inside the proof of Stacks 0ANG, assembled from Stacks 0AJ2, quasi-compactness
of an affine formal algebraic space and Stacks 0AN8, rather than a numbered statement of the
source.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AJ2](https://stacks.math.columbia.edu/tag/0AJ2)
* [Stacks Project, Tag 0AKS](https://stacks.math.columbia.edu/tag/0AKS)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AKX at countable indexing.** Let `X` be a formal algebraic space over `S`. Then
every affine formal algebraic space representable étale over `X` is countably indexed if and
only if `X` admits an atlas as in Definition **Stacks 0AIM** all of whose members are countably
indexed.

The implication (1) ⟹ (2) is the atlas of `X`. For (2) ⟹ (1), a chart `g : Z ⟶ X` receives a
surjective flat morphism, representable by algebraic spaces, from a countably indexed affine
formal algebraic space — the coproduct of a finite jointly surjective subfamily of the atlas
refined against `Z` — and **Stacks 0AKS** transfers countable indexing along it. -/
@[stacks 0AKX "the equivalence of conditions (1) and (2) at the property of being countably \
indexed, with nothing assumed. The refinement of the atlas against a chart is the library's \
`exists_countablyIndexed_surjective_flat_over_chart` (Stacks 0AJ3 in its chart form, clause \
(1) of Stacks 0AKQ, the implication (1) ⟹ (2) of Stacks 0AJ9 and the coproduct stability of \
countable indexing), and the transfer of countable indexing along the surjective flat morphism \
it produces is Stacks 0AKS. The equivalence is registered at this property rather than at an \
arbitrary one because the refinement is false at an arbitrary property"]
theorem hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty_isCountablyIndexed
    (X : FppfSheaf B S hS) (hX : IsFormalAlgebraicSpace B S hS X) :
    HasAffineEtaleChartProperty B S hS X (IsCountablyIndexed B S hS) ↔
      HasAffineEtaleAtlasWithProperty B S hS X (IsCountablyIndexed B S hS) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  refine ⟨fun h ↦ ?_, fun hatlas Z g hZ hg ↦ ?_⟩
  · obtain ⟨-, I, Xi, fi, hXiaff, hXiet, hXisurj⟩ := hX
    exact ⟨I, Xi, fi, hXiaff, hXiet, hXisurj, fun i ↦ h (Xi i) (fi i) (hXiaff i) (hXiet i)⟩
  · obtain ⟨W, w, hWaff, hWcount, hwrep, hwsurj, hwflat, -⟩ :=
      exists_countablyIndexed_surjective_flat_over_chart B S hS hX hatlas g hZ hg
    exact (isCountablyIndexed_iff_of_surjective_flat' B S hS w hWaff hZ hwrep hwsurj hwflat).1
      hWcount

/-- **The implication (2) ⟹ (1) of Stacks 0AKX at countable indexing**, in the shape its
consumers take: an affine formal algebraic space representable étale over a locally countably
indexed formal algebraic space is countably indexed. -/
theorem isCountablyIndexed_of_isRepresentableEtale_of_isLocallyCountablyIndexed
    (Z : FppfSheaf B S hS) (hZ : IsLocallyCountablyIndexed B S hS Z)
    (U : FppfSheaf B S hS) (a : U ⟶ Z) (hU : IsAffineFormalAlgebraicSpace B S hS U)
    (ha : IsRepresentableEtale B S hS a) : IsCountablyIndexed B S hS U :=
  (hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty_isCountablyIndexed
    B S hS Z hZ.1).2 hZ.2 U a hU ha

/-- **The presented refinement of a covering of the source holds at `C = WAdmᶜᵒᵘⁿᵗ`.** This is
`AlgebraicGeometry.FormalSpace.HasEtaleRefinementOfSourceCover'` for the class of countably
weakly admissible topological rings, with nothing assumed.

It is `exists_finite_affineEtaleRefinement_completedEtaleCover_of_sourceCover` with its two
remaining hypotheses discharged: the members of the covering being refined are affine formal
algebraic spaces representable étale over the two ends of `f`, which are locally countably
indexed, so they are countably indexed by the implication (2) ⟹ (1) of **Stacks 0AKX**. -/
theorem hasEtaleRefinementOfSourceCover_isCountablyWeaklyAdmissible
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) :
    HasEtaleRefinementOfSourceCover' B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible f := by
  intro hX hY I U V u v t hUcover hVaffine hVetale hVsquare U₀ V₀ a b τ hU₀ hV₀ ha hb hsquare
  exact exists_finite_affineEtaleRefinement_completedEtaleCover_of_sourceCover B S hS f U V u v t
    hUcover hVaffine hVetale hVsquare
    (fun i ↦ isCountablyIndexed_of_isRepresentableEtale_of_isLocallyCountablyIndexed B S hS X hX
      (U i) (u i) (hUcover.1 i) (hUcover.2.1 i))
    (fun i ↦ isCountablyIndexed_of_isRepresentableEtale_of_isLocallyCountablyIndexed B S hS Y hY
      (V i) (v i) (hVaffine i) (hVetale i))
    a b τ hU₀ hV₀ ha hb hsquare

end AlgebraicGeometry.FormalSpace

end
