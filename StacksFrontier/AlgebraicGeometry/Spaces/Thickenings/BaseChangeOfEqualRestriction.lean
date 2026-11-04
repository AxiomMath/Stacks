module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleFullyFaithful

/-!
# Two morphisms which agree on a first order thickening have the same direct image

Let `i : X ⟶ Y` be the inclusion of a first order thickening of algebraic spaces over a scheme
`S`, and let `a, b : Y ⟶ Z` be two morphisms which agree on the thickening, `i ≫ a = i ≫ b`.
Then base change along `a` and base change along `b` are *canonically isomorphic* functors on
the spaces-étale sites, and therefore the two direct images `a_*` and `b_*` of sheaves on the
small étale sites are canonically isomorphic as well — for sheaves of sets and for the direct
image of the structure sheaf as a sheaf of rings.

This is the half of [Stacks Project, Tag 05ZM] which the difference of two lifts needs.  For
`V` étale over `Z` the two base changes `V ×_{Z, a} Y` and `V ×_{Z, b} Y` are different objects
of the spaces-étale site of `Y`; they have *the same* base change to `X`, because `a` and `b`
become equal there, and base change along the inclusion of a first order thickening is fully
faithful by [Stacks Project, Tag 05ZH].  So the identity of the common base change is the image
of a unique isomorphism `V ×_{Z, a} Y ≅ V ×_{Z, b} Y`, and uniqueness makes the family natural.

The point of the construction is that the two comorphisms `a^♯ : 𝒪_Z ⟶ a_*𝒪_Y` and
`b^♯ : 𝒪_Z ⟶ b_*𝒪_Y` of [Stacks Project, Tag 03G8] have *different* targets, so that their
difference — the derivation of [Stacks Project, Tag 0618] — cannot even be formed.  Composing
`b^♯` with the isomorphism below carries it into the target of `a^♯`, and the two are then two
morphisms of sheaves of rings between one and the same pair of objects.

## Main definitions

* `AlgebraicGeometry.Space.spacesBaseChangeIsoOfCompEq`: the natural isomorphism
  `(-) ×_{Z, a} Y ≅ (-) ×_{Z, b} Y` of base-change functors on the spaces-étale sites.
* `AlgebraicGeometry.Space.smallEtaleDirectImageIsoOfCompEq`: the induced isomorphism
  `a_* ≅ b_*` of direct images of sheaves of sets on the small étale sites.
* `AlgebraicGeometry.Space.structureRingSheafDirectImageIsoOfCompEq`: the induced isomorphism
  `a_*𝒪_Y ≅ b_*𝒪_Y` of sheaves of rings on the small étale site of `Z`.
* `AlgebraicGeometry.Space.structureSharpTransport`: the comorphism `b^♯` carried into the
  target of `a^♯`, so that the two lifts are a pair of morphisms of sheaves of rings
  `𝒪_Z ⟶ a_*𝒪_Y`.

## Main results

* `AlgebraicGeometry.Space.map_spacesBaseChangeIsoOfCompEq_hom_app`: the characterising
  property of the isomorphism of base-change functors.  Its image under base change along the
  inclusion of the thickening is the comparison of the two iterated base changes, so the
  isomorphism is pinned down: two isomorphisms with that property agree, by faithfulness.
* `AlgebraicGeometry.Space.structureRingSheafDirectImageIsoOfCompEq_forget`: on underlying
  sheaves of sets the isomorphism of sheaves of rings is the isomorphism of direct images, so
  the ring structure is carried along and nothing else is chosen.

## Implementation notes

**Why the isomorphism is produced by full faithfulness and not by a universal property.**  The
two base changes `V ×_{Z, a} Y` and `V ×_{Z, b} Y` are *not* isomorphic over `V`: the two maps
to `V` are `a` and `b` read on the fibre product, and those differ.  The isomorphism is over
`Y` only, and the datum which pins it down is its base change to `X`.  So it is obtained as the
preimage of an isomorphism under a fully faithful functor — `CategoryTheory.Functor.preimageIso`
at the functor category, through
`CategoryTheory.Functor.FullyFaithful.whiskeringRight` — and not from the universal property of
a fibre product.

**Why the hypothesis is `Subfunctor.range i.hom` and not a closed subspace.**  That is the
shape in which [Stacks Project, Tag 05ZH] is proved in this development, as
`AlgebraicGeometry.Space.full_spacesBaseChange_of_isFirstOrderThickening` and
`AlgebraicGeometry.Space.faithful_spacesBaseChange_of_isFirstOrderThickening`; for the
inclusion of a closed subspace `Z` the range is `Z` itself by
`AlgebraicGeometry.Space.Subfunctor.range_ι`, and
`AlgebraicGeometry.Space.isFirstOrderThickening_range_subspaceInclusion` below converts.

**The direct image is transported through the two factors it is built from.**
`AlgebraicGeometry.Space.smallEtaleDirectImage` is restriction along spaces-étale base change
conjugated by the comparison equivalences of [Stacks Project, Tag 03G1], and only the middle
factor depends on the morphism.  So the isomorphism of direct images is the isomorphism of the
middle factor, `CategoryTheory.Functor.sheafPushforwardContinuousIso`, whiskered on both sides;
the two comparison factors are untouched.  The sheaf-of-rings form transports the ring
operations along that isomorphism by
`Stacks.Sheaves.ToposPullback.pullbackRingSheafMapOfNatTrans`, whose functoriality in the
transformation makes the two directions mutually inverse.

## References

* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

/-! ### The hypothesis at a closed subspace -/

/-- **The hypothesis of `AlgebraicGeometry.Space.spacesBaseChangeIsoOfCompEq` at a closed
subspace.**  The range of the inclusion of a closed subspace is the subspace itself, so a
closed subspace which is a first order thickening has an inclusion whose range is one. -/
theorem isFirstOrderThickening_range_subspaceInclusion (G : ClosedSubspaces B S hS X.1)
    (hG : IsFirstOrderThickening B S hS X G.1) :
    IsFirstOrderThickening B S hS X
      (Subfunctor.range (subspaceInclusion B S hS X G).hom) := by
  have h : Subfunctor.range (subspaceInclusion B S hS X G).hom = G.1 :=
    Subfunctor.range_ι G.1
  rw [h]
  exact hG

/-! ### The comparison of the two base-change functors -/

/-- The two iterated base changes of a single object of the spaces-étale site of `Z`, along two
morphisms which agree on the thickening, are the same object: both are the base change along
the composite, and the two composites are equal. -/
noncomputable def spacesBaseChangeCompIsoOfCompEq (i : X ⟶ Y) {a b : Y ⟶ Z}
    (hab : i ≫ a = i ≫ b) :
    (spacesBaseChange B S hS a).functor ⋙ (spacesBaseChange B S hS i).functor ≅
      (spacesBaseChange B S hS b).functor ⋙ (spacesBaseChange B S hS i).functor :=
  spacesBaseChange_comp B S hS i a ≪≫
    eqToIso (congrArg (fun m : X ⟶ Z ↦ (spacesBaseChange B S hS m).functor) hab) ≪≫
    (spacesBaseChange_comp B S hS i b).symm

/-- **Two morphisms which agree on a first order thickening have canonically isomorphic
base-change functors.**  For the inclusion `i : X ⟶ Y` of a first order thickening and
`a, b : Y ⟶ Z` with `i ≫ a = i ≫ b`, the functors `V ↦ V ×_{Z, a} Y` and `V ↦ V ×_{Z, b} Y` on
the spaces-étale sites are isomorphic.

This is the comparison of [Stacks Project, Tag 05ZM] in the form the difference of two lifts
needs: the two base changes become equal over the thickening, and base change along the
inclusion of a first order thickening is fully faithful by [Stacks Project, Tag 05ZH], so the
identity of the common base change is the image of a unique isomorphism. -/
noncomputable def spacesBaseChangeIsoOfCompEq (i : X ⟶ Y) [Mono i.hom]
    (hT : IsFirstOrderThickening B S hS Y (Subfunctor.range i.hom)) {a b : Y ⟶ Z}
    (hab : i ≫ a = i ≫ b) :
    (spacesBaseChange B S hS a).functor ≅ (spacesBaseChange B S hS b).functor :=
  ((fullyFaithfulSpacesBaseChangeOfIsFirstOrderThickening B S hS i hT).whiskeringRight
      (SpacesEtale B S hS Z)).preimageIso (spacesBaseChangeCompIsoOfCompEq B S hS i hab)

/-- **The characterising property of `spacesBaseChangeIsoOfCompEq`.**  Base changing the
isomorphism along the inclusion of the thickening gives back the comparison of the two iterated
base changes.  Since base change along the inclusion is faithful, this determines the
isomorphism. -/
theorem map_spacesBaseChangeIsoOfCompEq_hom_app (i : X ⟶ Y) [Mono i.hom]
    (hT : IsFirstOrderThickening B S hS Y (Subfunctor.range i.hom)) {a b : Y ⟶ Z}
    (hab : i ≫ a = i ≫ b) (V : SpacesEtale B S hS Z) :
    (spacesBaseChange B S hS i).functor.map
        ((spacesBaseChangeIsoOfCompEq B S hS i hT hab).hom.app V) =
      (spacesBaseChangeCompIsoOfCompEq B S hS i hab).hom.app V :=
  (fullyFaithfulSpacesBaseChangeOfIsFirstOrderThickening B S hS i hT).map_preimage _

/-! ### The comparison of the two direct images -/

/-- **Two morphisms which agree on a first order thickening have canonically isomorphic direct
images of sheaves of sets** on the small étale sites.  The direct image is restriction along
spaces-étale base change conjugated by the comparison equivalences of
[Stacks Project, Tag 03G1], and only the middle factor depends on the morphism, so the
isomorphism is `AlgebraicGeometry.Space.spacesBaseChangeIsoOfCompEq` read on sheaves. -/
noncomputable def smallEtaleDirectImageIsoOfCompEq (i : X ⟶ Y) [Mono i.hom]
    (hT : IsFirstOrderThickening B S hS Y (Subfunctor.range i.hom)) {a b : Y ⟶ Z}
    (hab : i ≫ a = i ≫ b) :
    smallEtaleDirectImage B S hS a ≅ smallEtaleDirectImage B S hS b :=
  Functor.isoWhiskerLeft (smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse
    (Functor.isoWhiskerRight
      (Functor.sheafPushforwardContinuousIso (spacesBaseChangeIsoOfCompEq B S hS i hT hab)
        (Type u) (SpacesEtale.topology B S hS Z) (SpacesEtale.topology B S hS Y))
      (smallEtaleComparisonRestriction B S hS Z))

/-- The morphism of inverse-image sheaves of rings induced by a natural transformation is
functorial in that transformation: the transported ring structures are compared by the
transformation itself, so a composite induces the composite.  This is what makes the two
directions of `AlgebraicGeometry.Space.structureRingSheafDirectImageIsoOfCompEq` mutually
inverse. -/
theorem pullbackRingSheafMapOfNatTrans_comp' {C : Type*} [Category C] {D : Type*}
    [Category D] (J : GrothendieckTopology C) {K : GrothendieckTopology D}
    [J.HasSheafCompose (CategoryTheory.forget RingCat.{u})]
    [K.HasSheafCompose (CategoryTheory.forget RingCat.{u})]
    {Φ Φ' Φ'' : Sheaf K (Type u) ⥤ Sheaf J (Type u)} [PreservesFiniteProducts Φ]
    [PreservesFiniteProducts Φ'] [PreservesFiniteProducts Φ'']
    (O : Sheaf K RingCat.{u}) (θ : Φ ⟶ Φ') (θ' : Φ' ⟶ Φ'') :
    pullbackRingSheafMapOfNatTrans J O θ ≫ pullbackRingSheafMapOfNatTrans J O θ' =
      pullbackRingSheafMapOfNatTrans J O (θ ≫ θ') := rfl

/-- **Two morphisms which agree on a first order thickening have canonically isomorphic direct
images of the structure sheaf**, as sheaves of rings on the small étale site of the target.
The ring operations are carried along
`AlgebraicGeometry.Space.smallEtaleDirectImageIsoOfCompEq` and nothing else is chosen; see
`AlgebraicGeometry.Space.structureRingSheafDirectImageIsoOfCompEq_forget`.

This is what lets the two comorphisms `a^♯` and `b^♯` of [Stacks Project, Tag 03G8] be compared:
their targets are the two direct images, and the difference of [Stacks Project, Tag 0618] is
formed in the common one. -/
noncomputable def structureRingSheafDirectImageIsoOfCompEq (i : X ⟶ Y) [Mono i.hom]
    (hT : IsFirstOrderThickening B S hS Y (Subfunctor.range i.hom)) {a b : Y ⟶ Z}
    (hab : i ≫ a = i ≫ b) :
    structureRingSheafDirectImage B S hS a ≅ structureRingSheafDirectImage B S hS b where
  hom := pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Z.1)
    (structureRingSheaf B S hS Y) (smallEtaleDirectImageIsoOfCompEq B S hS i hT hab).hom
  inv := pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Z.1)
    (structureRingSheaf B S hS Y) (smallEtaleDirectImageIsoOfCompEq B S hS i hT hab).inv
  hom_inv_id :=
    (pullbackRingSheafMapOfNatTrans_comp' (SmallEtale.topology B S hS Z.1)
      (structureRingSheaf B S hS Y) _ _).trans
      (congrArg (pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Z.1)
        (structureRingSheaf B S hS Y))
        (smallEtaleDirectImageIsoOfCompEq B S hS i hT hab).hom_inv_id)
  inv_hom_id :=
    (pullbackRingSheafMapOfNatTrans_comp' (SmallEtale.topology B S hS Z.1)
      (structureRingSheaf B S hS Y) _ _).trans
      (congrArg (pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Z.1)
        (structureRingSheaf B S hS Y))
        (smallEtaleDirectImageIsoOfCompEq B S hS i hT hab).inv_hom_id)

/-- On underlying sheaves of sets the isomorphism of direct images of the structure sheaf is
the isomorphism of direct images of sheaves of sets: the ring operations are transported and
nothing else. -/
theorem structureRingSheafDirectImageIsoOfCompEq_forget (i : X ⟶ Y) [Mono i.hom]
    (hT : IsFirstOrderThickening B S hS Y (Subfunctor.range i.hom)) {a b : Y ⟶ Z}
    (hab : i ≫ a = i ≫ b) :
    (sheafCompose (SmallEtale.topology B S hS Z.1)
          (CategoryTheory.forget RingCat.{u})).map
        (structureRingSheafDirectImageIsoOfCompEq B S hS i hT hab).hom =
      (smallEtaleDirectImageIsoOfCompEq B S hS i hT hab).hom.app
        (Sheaf.ringSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y)) :=
  ringSheafMap_pullbackRingSheafMapOfNatTrans.{u, u, u, u + 1, u, u + 1} _ _ _

/-! ### The two comorphisms in one place -/

/-- **The comorphism of `b` carried into the target of the comorphism of `a`.**  For two
morphisms which agree on a first order thickening, this is `b^♯ : 𝒪_Z ⟶ b_*𝒪_Y` composed with
the isomorphism `b_*𝒪_Y ≅ a_*𝒪_Y`, so that it and `a^♯` are two morphisms of sheaves of rings
between one and the same pair of objects.

Forming the two lifts of [Stacks Project, Tag 0618] as a pair of maps with one target is what
this is for; their difference is the derivation of that tag. -/
noncomputable def structureSharpTransport (i : X ⟶ Y) [Mono i.hom]
    (hT : IsFirstOrderThickening B S hS Y (Subfunctor.range i.hom)) {a b : Y ⟶ Z}
    (hab : i ≫ a = i ≫ b) :
    structureRingSheaf B S hS Z ⟶ structureRingSheafDirectImage B S hS a :=
  structureSharp B S hS b ≫ (structureRingSheafDirectImageIsoOfCompEq B S hS i hT hab).inv

end AlgebraicGeometry.Space

end
