module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.GroupoidSituation
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.PointwiseMaximalLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.LocusBaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# The smooth locus in a groupoid slice

In the flat, locally finitely presented groupoid situation the largest open of
`U' ×_{g, U, t} R` on which the induced map `h` to `U` is smooth is pulled back from an open of
`U'`.  The smooth locus of a morphism locally of finite presentation is open and is the largest
smooth open, and it commutes with base change along a flat morphism locally of finite
presentation, so `AlgebraicGeometry.exists_open_with_preimage_maximal_locus` applies.

## Main definitions

This file introduces no definitions.

## Main results

* `AlgebraicGeometry.exists_open_with_preimage_maximal_smoothLocus` identifies the largest
  smooth open with the inverse image of an open of `U'`.

## Implementation notes

The pointwise condition fed to
`AlgebraicGeometry.exists_open_with_preimage_maximal_locus_of_pointwise` is formal smoothness of
the stalk map, which is the underlying set of `AlgebraicGeometry.Scheme.Hom.smoothLocus` and
needs no finiteness hypothesis to be stated; its openness is where local finite presentation
enters.  The base-change input is the disjunctive form
`AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_preimage_of_isPullback`, used through its second
alternative, flatness of the morphism being based changed along.

## References

* [Stacks Project, Tag 047W](https://stacks.math.columbia.edu/tag/047W)
* [Stacks Project, Tag 02V4](https://stacks.math.columbia.edu/tag/02V4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- A morphism locally of finite presentation is smooth on an open subscheme exactly when its
stalk map is formally smooth at every point of that open. -/
private theorem smooth_comp_ι_iff_forall_formallySmooth_stalkMap {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (U : X.Opens) :
    Smooth (U.ι ≫ f) ↔ ∀ x ∈ U, (f.stalkMap x).hom.FormallySmooth := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq, eq_top_iff]
  exact ⟨fun h x hx => h (Set.mem_univ (⟨x, hx⟩ : U.toScheme)),
    fun h y _ => h y.1 y.2⟩

/-- **Stacks Project, Tag 047W, case (7).**  In the flat, locally finitely presented groupoid
situation the largest open of `U' ×_{g, U, t} R` on which `h` is smooth is the inverse image
along the projection of an open of `U'`. -/
@[stacks 047W "smooth"]
public theorem exists_open_with_preimage_maximal_smoothLocus
    (D : FlatLocallyFinitelyPresentedGroupoidSituation.{u}) :
    ∃ W : D.U'.Opens,
      IsGreatest {V : D.fiberProduct.Opens | Smooth (V.ι ≫ D.h)}
        ((pullback.fst D.g D.groupoid.target.left) ⁻¹ᵁ W) := by
  have hzar : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Smooth)
  let R : MorphismProperty Scheme.{u} := fun _ _ f => Flat f ∧ LocallyOfFinitePresentation f
  exact exists_open_with_preimage_maximal_locus_of_pointwise
    (@Smooth.{u}) (@LocallyOfFinitePresentation.{u}) R (fun _ _ _ hf => hf.2)
    (fun X _ f x => (f.stalkMap x).hom.FormallySmooth)
    (fun X _ f hf => by
      have : LocallyOfFinitePresentation f := hf
      exact f.isOpen_smoothLocus)
    (fun X _ f hf x => by
      have : LocallyOfFinitePresentation f := hf
      exact ⟨fun ⟨U, hxU, hU⟩ =>
        (smooth_comp_ι_iff_forall_formallySmooth_stalkMap f U).mp hU x hxU, fun hx =>
        ⟨f.smoothLocus, hx,
          (smooth_comp_ι_iff_forall_formallySmooth_stalkMap f f.smoothLocus).mpr fun _ hy => hy⟩⟩)
    (fun {X _ X' _ f f' p q} hf hq hp x' => by
      have : LocallyOfFinitePresentation f := hf
      have : LocallyOfFinitePresentation f' :=
        MorphismProperty.IsStableUnderBaseChange.of_isPullback hp hf
      exact SetLike.ext_iff.mp
        (Scheme.Hom.smoothLocus_eq_preimage_of_isPullback hp (Or.inr hq.1)) x')
    D.groupoid D.g
    (show R D.groupoid.source.left from ⟨inferInstance, inferInstance⟩)
    (show R D.groupoid.target.left from ⟨inferInstance, inferInstance⟩)
    (show LocallyOfFinitePresentation D.g from inferInstance)

end AlgebraicGeometry
