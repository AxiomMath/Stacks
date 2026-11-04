module

public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.GroupoidSituation
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.PointwiseMaximalLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Locus
public import StacksCore.Tactic.StacksAttribute

/-!
# The locally quasi-finite locus in a groupoid slice

In the groupoid situation with structure maps locally of finite type, the largest open of
`U' ×_{g, U, t} R` on which the induced map `h` to `U` is locally quasi-finite is pulled back
from an open of `U'`.  This is the case `d = 0` of the relative-dimension locus: a morphism
locally of finite type is quasi-finite at a point exactly when the fibre through that point has
local dimension zero there, so the quasi-finite locus is the dimension-zero locus, which is open
and commutes with arbitrary base change.  No flatness hypothesis on the source and target maps
is needed.

## Main definitions

This file introduces no definitions.

## Main results

* `AlgebraicGeometry.exists_open_with_preimage_maximal_quasiFiniteLocus` identifies the largest
  locally quasi-finite open with the inverse image of an open of `U'`.

## Implementation notes

As elsewhere in this development, the source's notion of a locally quasi-finite morphism is the
conjunction of Mathlib's `AlgebraicGeometry.LocallyOfFiniteType` and
`AlgebraicGeometry.LocallyQuasiFinite`, the latter carrying only the isolation of points in
fibres.  The first conjunct holds for every restriction of `h` to an open, `h` being locally of
finite type in the situation at hand, so the transfer principle is applied to
`AlgebraicGeometry.LocallyQuasiFinite` alone and the conjunction is reinstated afterwards.

The pointwise condition is `AlgebraicGeometry.quasiFiniteAt`, which already carries both
conjuncts pointwise; its locus is `AlgebraicGeometry.quasiFiniteLocus`, open by Tag 01TI, and
its invariance under base change is read off the invariance of the local dimension of a fibre.

## References

* [Stacks Project, Tag 047W](https://stacks.math.columbia.edu/tag/047W)
* [Stacks Project, Tag 0397](https://stacks.math.columbia.edu/tag/0397)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- Local quasi-finiteness in Mathlib's fibre-isolation sense is local on the source for the
Zariski topology. -/
private instance locallyQuasiFinite_isZariskiLocalAtSource :
    IsZariskiLocalAtSource (@LocallyQuasiFinite.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.QuasiFinite)

/-- A morphism locally of finite type is quasi-finite at a point exactly when it is locally
quasi-finite on some open neighbourhood of that point. -/
private theorem exists_mem_locallyQuasiFinite_comp_ι_iff {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) :
    (∃ U : X.Opens, x ∈ U ∧ LocallyQuasiFinite (U.ι ≫ f)) ↔ quasiFiniteAt f x := by
  refine ⟨fun ⟨U, hxU, hU⟩ => ⟨finiteTypeAt_of_locallyOfFiniteType f x, ?_⟩,
    fun hx => ⟨quasiFiniteLocus f, (mem_quasiFiniteLocus_iff f x).mpr hx, inferInstance⟩⟩
  have _ : LocallyQuasiFinite (U.ι ≫ f) := hU
  exact (Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion (f := U.ι) (g := f)
    (x := (⟨x, hxU⟩ : U.toScheme))).mp (Scheme.Hom.quasiFiniteAt (U.ι ≫ f) ⟨x, hxU⟩)

/-- **Stacks Project, Tag 047W, case (2).**  In the groupoid situation with structure maps
locally of finite type, the largest open of `U' ×_{g, U, t} R` on which `h` is locally
quasi-finite is the inverse image along the projection of an open of `U'`. -/
@[stacks 047W "locally quasi-finite"]
public theorem exists_open_with_preimage_maximal_quasiFiniteLocus
    (D : LocallyOfFiniteTypeGroupoidSituation.{u}) :
    ∃ W : D.U'.Opens,
      IsGreatest
        {V : D.fiberProduct.Opens |
          LocallyOfFiniteType (V.ι ≫ D.h) ∧ LocallyQuasiFinite (V.ι ≫ D.h)}
        ((pullback.fst D.g D.groupoid.target.left) ⁻¹ᵁ W) := by
  obtain ⟨W, hW⟩ := exists_open_with_preimage_maximal_locus_of_pointwise
    (@LocallyQuasiFinite.{u}) (@LocallyOfFiniteType.{u}) (@LocallyOfFiniteType.{u})
    (fun {_ _} _ h => h)
    (fun _ _ f x => quasiFiniteAt f x)
    (fun _ _ f _ => by
      have h : {x | quasiFiniteAt f x} = (quasiFiniteLocus f : Set _) :=
        (Set.ext fun x => mem_quasiFiniteLocus_iff f x).symm
      rw [h]
      exact (quasiFiniteLocus f).2)
    (fun _ _ f hf x => by
      have : LocallyOfFiniteType f := hf
      exact exists_mem_locallyQuasiFinite_comp_ι_iff f x)
    (fun {_ _ _ _ f f' p _} hf _ hp x' => by
      have : LocallyOfFiniteType f := hf
      have : LocallyOfFiniteType f' :=
        MorphismProperty.IsStableUnderBaseChange.of_isPullback hp hf
      rw [quasiFiniteAt_iff_fiberDimensionAt_eq_zero f' x',
        quasiFiniteAt_iff_fiberDimensionAt_eq_zero f (p x'),
        topologicalKrullDimAt_fiber_eq_of_isPullback hp x'])
    D.groupoid D.g inferInstance inferInstance inferInstance
  refine ⟨W, ?_⟩
  have hft : LocallyOfFiniteType D.h := by
    show LocallyOfFiniteType
      (pullback.snd D.g D.groupoid.target.left ≫ D.groupoid.source.left)
    infer_instance
  have hset : {V : D.fiberProduct.Opens |
        LocallyOfFiniteType (V.ι ≫ D.h) ∧ LocallyQuasiFinite (V.ι ≫ D.h)} =
      {V : D.fiberProduct.Opens | LocallyQuasiFinite (V.ι ≫ D.h)} :=
    Set.ext fun V => ⟨fun h => h.2, fun h => ⟨inferInstance, h⟩⟩
  rw [hset]
  exact hW

end AlgebraicGeometry
