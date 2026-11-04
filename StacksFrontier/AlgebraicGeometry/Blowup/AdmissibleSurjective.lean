module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Bijective
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformModule

/-!
# An admissible blowup with dense centre complement is surjective

A `U`-admissible blowup `b : X' ⟶ X` is an isomorphism over `U`, because its centre is supported
away from `U` and the blowup morphism is an isomorphism off its centre ([Stacks, Tag 02OS]); and
it is proper, because its centre is of finite presentation as a closed subscheme. So its range is
a closed set containing `U`. If `U` is topologically dense in `X` the range is therefore all of
`X`.

This is not stated in the Stacks Project as a numbered result; it is the standing fact the
proofs that pass to an admissible blowup of the base use in order to know that nothing of the
base is lost. Without a density hypothesis it is false: the blowup in the zero ideal sheaf is
empty, and the zero ideal sheaf is `⊥`-admissible.

## Main results

* `Stacks.Blowup.IsAdmissibleBlowup.surjective`: a `U`-admissible blowup with `U` topologically
  dense is surjective.
* `Stacks.Blowup.surjective_blowUpToBase`: the same for the blowup morphism itself, whose centre
  is then only required to be of finite presentation and supported away from a dense open.

## Implementation notes

`Stacks.Blowup.IsAdmissibleBlowup` is stated with `Stacks.Blowup.blowUp` while
`AlgebraicGeometry.exists_blowUpToBase_eq_of_notMem_support`, which supplies the points over the
complement of the centre, is stated with `AlgebraicGeometry.blowUp`. The two constructions are
identified by `AlgebraicGeometry.isAdmissibleBlowup_iff`, which is how the isomorphism to a
blowup is taken here.

## References

* [Stacks Project, Tag 080K](https://stacks.math.columbia.edu/tag/080K)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Blowup

/-- **A `U`-admissible blowup with `U` topologically dense is surjective.**

The blowup morphism is an isomorphism over the complement of its centre
([Stacks, Tag 02OS]), and `U` is disjoint from that centre, so the range of the modification
contains `U`. The modification is proper, hence closed, so its range is closed; a closed set
containing a dense set is everything.

Density is essential: the blowup in the zero ideal sheaf is empty, and `⊥` is an admissible
centre for the empty open. -/
theorem IsAdmissibleBlowup.surjective {X X' : Scheme.{u}} {U : X.Opens} {b : X' ⟶ X}
    (h : IsAdmissibleBlowup U b) (hU : Dense (U : Set X)) : Surjective b := by
  obtain ⟨I, -, hIdisj, e, he⟩ := (isAdmissibleBlowup_iff U b).mp h
  have _ : IsProper b := h.isProper
  -- The range of a proper morphism is closed.
  have hclosed : IsClosed (Set.range b.base) := by
    rw [← Set.image_univ]
    exact Scheme.Hom.isClosedMap b _ isClosed_univ
  -- It contains `U`, over which the blowup morphism hits every point.
  have hmem : (U : Set X) ⊆ Set.range b.base := by
    intro x hx
    obtain ⟨y, hy⟩ :=
      exists_blowUpToBase_eq_of_notMem_support I (Set.disjoint_left.mp hIdisj hx)
    refine ⟨e.inv.base y, ?_⟩
    rw [← hy, ← he, ← Scheme.Hom.comp_apply, e.inv_hom_id_assoc]
  exact (surjective_iff b).mpr
    (Set.range_eq_univ.mp
      (Set.eq_univ_of_univ_subset (hU.closure_eq ▸ closure_minimal hmem hclosed)))

/-- **The blowup morphism in a centre of finite presentation supported away from a dense open is
surjective.** This is `Stacks.Blowup.IsAdmissibleBlowup.surjective` for the blowup itself. -/
theorem surjective_blowUpToBase {X : Scheme.{u}} {U : X.Opens} (hU : Dense (U : Set X))
    {I : X.IdealSheafData} (hIfp : AlgebraicGeometry.FinitePresentation I.subschemeι)
    (hIdisj : Disjoint (U : Set X) (I.support : Set X)) : Surjective (blowUpToBase I) :=
  (isAdmissibleBlowup_blowUpToBase hIfp hIdisj).surjective hU

end Stacks.Blowup

end
