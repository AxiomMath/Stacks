module

public import StacksFrontier.AlgebraicGeometry.Groupoids.More.GroupoidSituation
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.PointwiseMaximalLocus
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.EtaleUnramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.BaseChangeLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Local
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.OpenLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksCore.Tactic.StacksAttribute

/-!
# The unramified locus in a groupoid slice

In the groupoid situation with structure maps locally of finite type, the largest open of
`U' ×_{g, U, t} R` on which the induced map `h` to `U` is unramified is pulled back from an open
of `U'`.  The unramified locus of a morphism is open and is the largest unramified open, and
for a morphism locally of finite type it commutes with arbitrary base change, so
`AlgebraicGeometry.exists_open_with_preimage_maximal_locus` applies.  No flatness hypothesis on
the source and target maps is needed.

## Main definitions

This file introduces no definitions.

## Main results

* `AlgebraicGeometry.exists_open_with_preimage_maximal_unramifiedLocus` identifies the largest
  unramified open with the inverse image of an open of `U'`.

## Implementation notes

The pointwise condition fed to
`AlgebraicGeometry.exists_open_with_preimage_maximal_locus_of_pointwise` is
`AlgebraicGeometry.UnramifiedAt`, unramifiedness of the map of sections over some affine chart;
openness of its locus is formal, since the chart witnessing one point witnesses every point of
itself.  Matching that chart condition with the restriction of the morphism to an open
neighbourhood is the chart bridge of `AlgebraicGeometry.comp_ι_of_appLE` and
`AlgebraicGeometry.exists_appLE_of_comp_ι`, read for the pair of ring-map properties defining
unramifiedness.  The base-change input needs no flatness at all, which is why the weaker
groupoid situation suffices.

## References

* [Stacks Project, Tag 047W](https://stacks.math.columbia.edu/tag/047W)
* [Stacks Project, Tag 0475](https://stacks.math.columbia.edu/tag/0475)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- Unramifiedness of morphisms of schemes is the affine-local property attached to the
conjunction of formal unramifiedness and finite type of ring maps, in the form that applies to
the class `AlgebraicGeometry.Unramified` itself. -/
private instance hasRingHomProperty_unramified_pair :
    HasRingHomProperty (@Unramified.{u})
      (fun {R T : Type u} [CommRing R] [CommRing T] (g : R →+* T) =>
        g.FormallyUnramified ∧ g.FiniteType) :=
  hasRingHomProperty_unramified

/-- Unramifiedness is local on the source for the Zariski topology. -/
private instance unramified_isZariskiLocalAtSource :
    IsZariskiLocalAtSource (@Unramified.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtSource

/-- Unramifiedness is stable under postcomposition with an open immersion, an open immersion
being étale and hence unramified. -/
private instance unramified_respectsRight_isOpenImmersion :
    MorphismProperty.RespectsRight (@Unramified.{u}) @IsOpenImmersion where
  postcomp i hi f hf := have := hi; MorphismProperty.comp_mem _ f i hf (unramified_of_etale i)

/-- A morphism of schemes is unramified at a point exactly when it is unramified on some open
neighbourhood of that point. -/
private theorem exists_mem_unramified_comp_ι_iff {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    (∃ U : X.Opens, x ∈ U ∧ Unramified (U.ι ≫ f)) ↔ UnramifiedAt f x := by
  constructor
  · rintro ⟨C, hx, hC⟩
    obtain ⟨U, hxU, V, e, hQ⟩ := exists_appLE_of_comp_ι (@Unramified.{u}) f hC hx
    let _ : Algebra Γ(S, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 e).hom.toAlgebra
    exact ⟨U.1, U.2, hxU, V.1, V.2, e, ⟨RingHom.formallyUnramified_algebraMap.mp hQ.1,
      RingHom.finiteType_algebraMap.mp hQ.2⟩⟩
  · rintro ⟨U, hU, hxU, V, hV, e, halg⟩
    let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    have halg' : Algebra.Unramified Γ(S, V) Γ(X, U) := halg
    exact ⟨U, hxU, comp_ι_of_appLE (@Unramified.{u}) f hU hV e
      ⟨RingHom.formallyUnramified_algebraMap.mpr halg'.formallyUnramified,
        RingHom.finiteType_algebraMap.mpr halg'.finiteType⟩⟩

/-- **Stacks Project, Tag 047W, case (3).**  In the groupoid situation with structure maps
locally of finite type, the largest open of `U' ×_{g, U, t} R` on which `h` is unramified is the
inverse image along the projection of an open of `U'`. -/
@[stacks 047W "unramified"]
public theorem exists_open_with_preimage_maximal_unramifiedLocus
    (D : LocallyOfFiniteTypeGroupoidSituation.{u}) :
    ∃ W : D.U'.Opens,
      IsGreatest {V : D.fiberProduct.Opens | Unramified (V.ι ≫ D.h)}
        ((pullback.fst D.g D.groupoid.target.left) ⁻¹ᵁ W) :=
  exists_open_with_preimage_maximal_locus_of_pointwise
    (@Unramified.{u}) (@LocallyOfFiniteType.{u}) (@LocallyOfFiniteType.{u})
    (fun {_ _} _ h => h)
    (fun _ _ f x => UnramifiedAt f x)
    (fun _ _ f _ => isOpen_setOf_unramifiedAt f)
    (fun _ _ f _ x => exists_mem_unramified_comp_ι_iff f x)
    (fun {_ _ _ _ f _ p q} hf _ hp x' => by
      have : LocallyOfFiniteType f := hf
      exact (unramifiedAt_iff_of_isPullback hp x').symm)
    D.groupoid D.g inferInstance inferInstance inferInstance

end AlgebraicGeometry
