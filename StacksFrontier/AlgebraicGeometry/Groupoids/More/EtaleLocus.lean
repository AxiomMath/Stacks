module

public import StacksFrontier.AlgebraicGeometry.Groupoids.More.GroupoidSituation
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.PointwiseMaximalLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.LocalStructure.OpenCopies
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.LocusBaseChange
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.PointwiseEtale
public import StacksCore.Tactic.StacksAttribute

/-!
# The étale locus in a groupoid slice

In the flat, locally finitely presented groupoid situation the largest open of
`U' ×_{g, U, t} R` on which the induced map `h` to `U` is étale is pulled back from an open of
`U'`.  The étale locus of a morphism is open and is the largest étale open, and for a morphism
locally of finite presentation it commutes with base change along a flat morphism, so
`AlgebraicGeometry.exists_open_with_preimage_maximal_locus` applies.

## Main definitions

This file introduces no definitions.

## Main results

* `AlgebraicGeometry.exists_open_with_preimage_maximal_etaleLocus` identifies the largest étale
  open with the inverse image of an open of `U'`.

## Implementation notes

The pointwise condition fed to
`AlgebraicGeometry.exists_open_with_preimage_maximal_locus_of_pointwise` is
`AlgebraicGeometry.EtaleAt`, étaleness on some affine chart; openness of its locus is formal,
since the chart witnessing one point witnesses every point of itself.  The base-change input is
the disjunctive form `AlgebraicGeometry.etaleAt_iff_of_isPullback`, used through its second
alternative, flatness of the morphism being based changed along.

## References

* [Stacks Project, Tag 047W](https://stacks.math.columbia.edu/tag/047W)
* [Stacks Project, Tag 0476](https://stacks.math.columbia.edu/tag/0476)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 047W, case (8).**  In the flat, locally finitely presented groupoid
situation the largest open of `U' ×_{g, U, t} R` on which `h` is étale is the inverse image
along the projection of an open of `U'`. -/
@[stacks 047W "etale"]
public theorem exists_open_with_preimage_maximal_etaleLocus
    (D : FlatLocallyFinitelyPresentedGroupoidSituation.{u}) :
    ∃ W : D.U'.Opens,
      IsGreatest {V : D.fiberProduct.Opens | Etale (V.ι ≫ D.h)}
        ((pullback.fst D.g D.groupoid.target.left) ⁻¹ᵁ W) := by
  have hzar : IsZariskiLocalAtSource (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Etale)
  let R : MorphismProperty Scheme.{u} := fun _ _ f => Flat f ∧ LocallyOfFinitePresentation f
  exact exists_open_with_preimage_maximal_locus_of_pointwise
    (@Etale.{u}) (@LocallyOfFinitePresentation.{u}) R (fun _ _ _ hf => hf.2)
    (fun _ _ f x => EtaleAt f x)
    (fun _ _ f _ => isOpen_setOf_etaleAt f)
    (fun _ _ f _ x =>
      ⟨fun ⟨U, hxU, hU⟩ =>
          Stacks.FundamentalGroup.ExtendedEtaleFold.etaleAt_of_etaleAt_isOpenImmersion_comp
            U.ι f ⟨x, hxU⟩ ((etale_iff_forall_etaleAt (U.ι ≫ f)).mp hU ⟨x, hxU⟩),
        fun hx => exists_open_etale_of_etaleAt f hx⟩)
    (fun {_ _ _ _ f _ p q} hf hq hp x' => by
      have : LocallyOfFinitePresentation f := hf
      exact (etaleAt_iff_of_isPullback hp (Or.inr hq.1) x').symm)
    D.groupoid D.g
    (show R D.groupoid.source.left from ⟨inferInstance, inferInstance⟩)
    (show R D.groupoid.target.left from ⟨inferInstance, inferInstance⟩)
    inferInstance

end AlgebraicGeometry
