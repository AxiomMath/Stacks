module

public import StacksFrontier.AlgebraicGeometry.Groupoids.More.GroupoidSituation
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.PointwiseMaximalLocus
public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.UniversalSyntomicOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PointwiseBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Comp
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Local
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.SyntomicBaseChange.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The syntomic locus in a groupoid slice

In the flat, locally finitely presented groupoid situation the largest open of
`U' ×_{g, U, t} R` on which the induced map `h` to `U` is syntomic is pulled back from an open
of `U'`.  The syntomic locus of a morphism is open and is the largest syntomic open, and for a
morphism locally of finite presentation it commutes with base change along a flat morphism, so
`AlgebraicGeometry.exists_open_with_preimage_maximal_locus` applies.

## Main definitions

This file introduces no definitions.

## Main results

* `AlgebraicGeometry.exists_open_with_preimage_maximal_syntomicLocus` identifies the largest
  syntomic open with the inverse image of an open of `U'`.

## Implementation notes

The pointwise condition fed to
`AlgebraicGeometry.exists_open_with_preimage_maximal_locus_of_pointwise` is
`AlgebraicGeometry.SyntomicAt`, syntomicity of the map of sections over some affine chart; openness
of its locus is `AlgebraicGeometry.isOpen_setOf_syntomicAt`, and matching it with the restriction
of the morphism to an open neighbourhood uses `AlgebraicGeometry.comp_ι_of_appLE` and
`AlgebraicGeometry.exists_appLE_of_comp_ι`.

For the base change the chart description is useless and the stalk description of
`AlgebraicGeometry.syntomicAt_tfae` is used instead: over a morphism locally of finite
presentation, syntomicity at a point is flatness of the stalk map together with the closed
fibre being a complete intersection, the finite-presentation clause being automatic.  The first
is `AlgebraicGeometry.isFlatAt_iff_of_isPullback`, which is where flatness of the base morphism
is used, and the second is
`AlgebraicGeometry.isCompleteIntersectionFibreAt_baseChange_iff`, which needs no flatness at
all.  The source's own route is the same: the locus of fibrewise complete intersections
commutes with any base change, and is the syntomic locus where the morphism is flat.

## References

* [Stacks Project, Tag 047W](https://stacks.math.columbia.edu/tag/047W)
* [Stacks Project, Tag 02V3](https://stacks.math.columbia.edu/tag/02V3)
* [Stacks Project, Tag 01UE](https://stacks.math.columbia.edu/tag/01UE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- Syntomicity is local on the source for the Zariski topology. -/
private instance syntomic_isZariskiLocalAtSource :
    IsZariskiLocalAtSource (@Syntomic.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Syntomic.{u})

/-- Syntomicity is stable under postcomposition with an open immersion, an open immersion being
syntomic. -/
private instance syntomic_respectsRight_isOpenImmersion :
    MorphismProperty.RespectsRight (@Syntomic.{u}) @IsOpenImmersion where
  postcomp i hi f hf :=
    have := hi; MorphismProperty.comp_mem _ f i hf (syntomic_of_isOpenImmersion i)

/-- A morphism of schemes is syntomic at a point exactly when it is syntomic on some open
neighbourhood of that point. -/
private theorem exists_mem_syntomic_comp_ι_iff {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    (∃ U : X.Opens, x ∈ U ∧ Syntomic (U.ι ≫ f)) ↔ SyntomicAt f x := by
  constructor
  · rintro ⟨C, hx, hC⟩
    exact exists_appLE_of_comp_ι (@Syntomic.{u}) f hC hx
  · rintro ⟨U, hxU, V, e, halg⟩
    exact ⟨U.1, hxU, comp_ι_of_appLE (@Syntomic.{u}) f U.2 V.2 e halg⟩

/-- For a morphism locally of finite presentation, syntomicity at a point is flatness of the
stalk map there together with the closed fibre being a complete intersection over the residue
field of the image point. -/
@[ega "IV 19.3.6" "more general"]
private theorem syntomicAt_iff_isFlatAt_and_isCompleteIntersectionFibreAt
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (x : X) :
    SyntomicAt f x ↔
      (IsFlatAt f.toLRSHom.toShHom x ∧ IsCompleteIntersectionFibreAt f x) := by
  obtain ⟨-, ⟨V, hV, rfl⟩, hfxV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hfxV (V.2.preimage f.continuous)
  have hfp : FinitePresentationAt f x :=
    ⟨⟨V, hV⟩, ⟨U, hU⟩, hxU, hUV, f.finitePresentation_appLE hV hU hUV⟩
  have htfae := (syntomicAt_tfae f x ⟨V, hV⟩ hfxV).out 1 3
  exact htfae.trans ⟨fun hx => ⟨hx.2.1, hx.2.2⟩, fun hx => ⟨hfp, hx.1, hx.2⟩⟩

/-- **Stacks Project, Tag 047W, case (6).**  In the flat, locally finitely presented groupoid
situation the largest open of `U' ×_{g, U, t} R` on which `h` is syntomic is the inverse image
along the projection of an open of `U'`. -/
@[stacks 047W "syntomic"]
public theorem exists_open_with_preimage_maximal_syntomicLocus
    (D : FlatLocallyFinitelyPresentedGroupoidSituation.{u}) :
    ∃ W : D.U'.Opens,
      IsGreatest {V : D.fiberProduct.Opens | Syntomic (V.ι ≫ D.h)}
        ((pullback.fst D.g D.groupoid.target.left) ⁻¹ᵁ W) := by
  let R : MorphismProperty Scheme.{u} := fun _ _ f => Flat f ∧ LocallyOfFinitePresentation f
  exact exists_open_with_preimage_maximal_locus_of_pointwise
    (@Syntomic.{u}) (@LocallyOfFinitePresentation.{u}) R (fun _ _ _ hf => hf.2)
    (fun _ _ f x => SyntomicAt f x)
    (fun _ _ f _ => isOpen_setOf_syntomicAt f)
    (fun _ _ f _ x => exists_mem_syntomic_comp_ι_iff f x)
    (fun {_ _ _ _ f f' p q} hf hq hp x' => by
      have : LocallyOfFinitePresentation f := hf
      have : Flat q := hq.1
      have : LocallyOfFinitePresentation f' :=
        MorphismProperty.IsStableUnderBaseChange.of_isPullback hp hf
      rw [syntomicAt_iff_isFlatAt_and_isCompleteIntersectionFibreAt f' x',
        syntomicAt_iff_isFlatAt_and_isCompleteIntersectionFibreAt f (p x')]
      exact and_congr (isFlatAt_iff_of_isPullback hp x')
        (isCompleteIntersectionFibreAt_baseChange_iff p f' f q hp x'))
    D.groupoid D.g
    (show R D.groupoid.source.left from ⟨inferInstance, inferInstance⟩)
    (show R D.groupoid.target.left from ⟨inferInstance, inferInstance⟩)
    (show LocallyOfFinitePresentation D.g from inferInstance)

end AlgebraicGeometry
