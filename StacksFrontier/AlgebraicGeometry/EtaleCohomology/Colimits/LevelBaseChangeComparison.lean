module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineLimitEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.TransitionBaseChangeCoherence
public import StacksFrontier.CategoryTheory.Adjunction.Mates

/-! # Base change through the two site equivalences of Stacks 03Q6's system of sheaves

`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.BaseChangeAlgebraSystemInverseImages`
records that three equivalences of abelian sheaf categories separate a level of the site system
of Stacks 0EYL from the small étale site of the scheme the level sits over, and that transporting
the system `𝒢_i = (Y_i ⟶ X)^{-1} ℱ` onto the levels needs each of them to be compatible with
base change. For the third — the comparison of the bounded small étale site with Mathlib's — that
compatibility is `AlgebraicGeometry.SmallEtale.sheafEquivPullbackBaseChangeIso`. This file supplies
it for the other two:

* the inclusion of the small *affine* étale site into the small étale site, restriction along
  which is `Stacks.EtaleCohomology.BaseChangeAlgebraSystem.restrictToAffineEtale`, the sheaf form
  of Stacks 04HR;
* the level equivalence of Stacks 0EYL, restriction along which is
  `Stacks.EtaleCohomology.AffineLimitCohomology.restrictToLevel`.

Each is treated in the shape of `AlgebraicGeometry.SmallEtale.sheafEquivPullbackBaseChangeIso`:
first the square of *direct* images, obtained from a comparison of the underlying *site* functors
by `CategoryTheory.Functor.sheafPushforwardContinuousComp'`; then the square of *inverse* images,
obtained from it by `CategoryTheory.Adjunction.leftAdjointUniq` for arbitrary chosen left adjoints
of the four direct images; then the pinning statement that the conjugate of the square of inverse
images, under the two composite adjunctions, is the inverse of the square of direct images, which
determines it completely because conjugation is a bijection; and finally the specialisation in
which the left adjoints of the two restrictions are the quasi-inverses of the equivalences they
are.

## Main definitions

Restriction to the small affine étale site, in the namespace `AlgebraicGeometry.SmallAffineEtale`,
for a morphism `f : T ⟶ S` of a big étale site between **affine** schemes:

* `inclusionPushforwardBaseChangeIso` — the square of direct images.
* `inclusionPullbackBaseChangeIso` — the square of inverse images, at arbitrary left adjoints.
* `inclusionEquivPullbackBaseChangeIso` — the square of inverse images with the two left adjoints
  of the restrictions taken to be the quasi-inverses of the equivalences of Stacks 04HR.

Restriction to a level of the system of Stacks 0EYL, for an arrow `a : i ⟶ j` of the index
category of the system. In the namespace `Stacks.EtaleCohomology.TransitionBaseChange`, where the
comparison of the transition functors with base change lives:

* `transitionAffineIso` — **the transition functor of the system is base change of small affine
  étale sites**, the small affine étale companion of
  `Stacks.EtaleCohomology.TransitionBaseChange.transitionIso`.

In the namespace `Stacks.EtaleCohomology.AffineLimitCohomology`, where `restrictToLevel` lives:

* `levelPushforwardBaseChangeIso` — the square of direct images.
* `levelPullbackBaseChangeIso` — the square of inverse images, at arbitrary left adjoints.
* `levelEquivPullbackBaseChangeIso` — the square of inverse images with the two left adjoints of
  the restrictions taken to be the quasi-inverses of the level equivalences.

## Main results

* `conjugateEquiv_inclusionPullbackBaseChangeIso_hom` and
  `conjugateEquiv_levelPullbackBaseChangeIso_hom` pin the two squares of inverse images down:
  each has the inverse of the corresponding square of direct images as its conjugate. Since
  conjugation is a bijection this determines them completely, and in particular makes them
  independent of which left adjoints of the four direct images were chosen.
* `transitionAffineIso_hom_app_inclusion` identifies the components of `transitionAffineIso` with
  those of `transitionIso`, so the coherence laws
  `Stacks.EtaleCohomology.TransitionBaseChange.transitionIso_id_hom_app` and
  `.transitionIso_comp_hom_app` are statements about it as well.
* `transitionAffineIso_id_hom_app` and `transitionAffineIso_comp_hom_app` — **the identity and
  composition laws of the small affine étale comparison**, obtained that way. Their two
  ingredients are the small affine étale transports of base change along a morphism only provably
  an identity or a composite, `AlgebraicGeometry.smallAffineEtaleBaseChange_factoredIdIso` and
  `..._factoredCompIso`, with `stageAffineIdIso` and `stageAffineCompIso` the instances of them at
  the transition morphisms of the system.

## Implementation notes

**The site square for the affine inclusion is an equality.**
`AlgebraicGeometry.smallAffineEtaleBaseChange_comp_inclusion` says that base change between small
affine étale categories followed by the inclusion into the small étale category *is* the inclusion
followed by base change between small étale categories, on the nose. All that is left on the
sheaf side is to break the two composites apart, which is what
`CategoryTheory.Functor.sheafPushforwardContinuousComp'` does.

**The site square for the levels is the existing one, with the inclusion cancelled.**
`Stacks.EtaleCohomology.TransitionBaseChange.transitionIso` compares the transition functor with
base change *in the small étale site*, because base change of small affine étale sites is
assembled only between affine schemes. Composing with the equality above turns it into a
comparison of two functors into the small affine étale site followed by the inclusion, and the
inclusion is fully faithful, so `CategoryTheory.Functor.fullyFaithfulCancelRight` removes it.
`transitionAffineIso` is therefore not a second construction of the comparison: it is
`transitionIso` itself, read in the smaller site, which is what
`transitionAffineIso_hom_app_inclusion` says and what makes the two coherence laws of
`transitionIso` apply to it unchanged.

**Affineness.** The first half needs `S` and `T` affine, because that is the only case in which
`AlgebraicGeometry.smallAffineEtaleBaseChange` is assembled — step 1 of the three steps named in
`BaseChangeAlgebraSystemInverseImages.lean`. The second half needs the schemes of two levels
affine for the same reason, which in the colimit theorems is supplied by
`[∀ i : Iᵒᵖ, IsAffine (D.obj i)]`. Neither half needs the limit cone, and neither uses any
affineness beyond that.

**Why the left adjoints are arguments rather than functors.** As in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/BoundedSiteBaseChangeComparison.lean`: a left
adjoint of a direct image is determined only up to isomorphism and different developments pick
different representatives, so taking the adjunctions as arguments lets each consumer use its own,
and the two `conjugateEquiv` statements are then the only available sense in which the comparison
is independent of that choice.

**Coefficients.** The two squares of direct images and the two squares of inverse images at
arbitrary left adjoints are stated at an arbitrary coefficient category, as the model is. No
separate restatement at `AddCommGrpCat` is given for them, and none is needed:
`Stacks.EtaleCohomology.BaseChangeAlgebraSystem.restrictToAffineEtale` and
`Stacks.EtaleCohomology.AffineLimitCohomology.restrictToLevel` are `abbrev`s for exactly the two
`sheafPushforwardContinuous` functors appearing below, so at
`A := AddCommGrpCat.{u + 1}` and `A := AddCommGrpCat.{max u v + 1}` the statements below *are*
the statements about those two restrictions. Only the two specialisations at the equivalences'
quasi-inverses — `inclusionEquivPullbackBaseChangeIso` and `levelEquivPullbackBaseChangeIso` —
say something the general form does not, since a choice of left adjoint is being made, and those
are stated at the coefficients the colimit development uses.

**The two spelling restatements of continuity.** `InverseSystemOfFiniteSites.continuous` is a
theorem rather than an instance, and
`AlgebraicGeometry.smallAffineEtaleBaseChange_isContinuous` is stated for a morphism of
`B.Scheme`, so its conclusion names the topologies of `(B.obj (D.obj _) _).obj` while the
statements here carry `levelScheme`; the two are definitionally equal but instance search does not
pass between them. `isContinuous_sysTransition` and
`isContinuous_smallAffineEtaleBaseChange_stageMap` are those two restatements, in the style of
`AlgebraicGeometry.SmallEtale.isContinuous_inclusionSmallEtaleBaseChange`.

## What this file does not contain

The system of sheaves itself, and the coherence of the comparisons below. This file closes the
third and last of the three geometric steps listed in
`BaseChangeAlgebraSystemInverseImages.lean`, but two things stand between those three steps and
an `InverseSystemOfFiniteSites.AbelianSheafSystem`:

* the **assembly**: a cocone of direct images `R_i` from the levels to the abelian sheaves of the
  small étale site of `X`, built out of the three comparisons and direct image along the
  projection `Y_i ⟶ X`, together with the `hid` and `hcomp` of
  `InverseSystemOfFiniteSites.inverseImageSystem` read on those `R_i`. That is
  `Stacks.EtaleCohomology.TransitionBaseChange.projSquare` with
  `projSquare_id_inv_app` and `projSquare_comp_inv_app`, in
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.StageProjectionBaseChangeCoherence`.

The **coherence of the small affine étale comparison** is no longer among them: it is
`transitionAffineIso_id_hom_app` and `transitionAffineIso_comp_hom_app` above. Nor is its
sheaf-level consequence for the two squares of direct images: the *pasting* of the level square
and the affine square is a single restriction along `transitionIso`, and its identity and
composition laws are
`Stacks.EtaleCohomology.TransitionBaseChange.levelEtaleSquare_id_inv_app` and
`.levelEtaleSquare_comp_inv_app` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/LevelEtaleSquareCoherence.lean`. The
assembly itself is carried out in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/StageProjectionBaseChangeCoherence.lean`,
on the remaining input named in that file: the pseudofunctor coherence of
`AlgebraicGeometry.smallEtaleBaseChange` along the projections `Y_i ⟶ X`, which is not a statement
about any of the six comparisons below.

Nothing below is a clause of Stacks 03Q6: these are inputs to the construction of that tag's
system of sheaves, not components of its statement, so no tag is claimed, following
`TransitionIsBaseChange.lean` and `TransitionBaseChangeCoherence.lean`.

Nothing here bears on the *non-affine* case of Stacks 03Q6 — gap (a), a `qcqs` but non-affine
`X` — which is a separate development, nor on the index-naturality of the transition maps of the
cohomology diagram recorded in `BaseChangeAlgebraSystemEtaleCohomology.lean`, which needs the
system of sheaves to be *constructed* and not merely its inputs to exist.

## References

* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.SmallAffineEtale

universe v' u' u

attribute [local instance]
  Stacks.EtaleCohomology.BaseChangeAlgebraSystem.isDenseSubsite_smallAffineEtaleInclusion

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)
  [IsAffine S.obj] [IsAffine T.obj] (A : Type u') [Category.{v'} A]

/-- **Restriction to the small affine étale site has the same direct image along base change.**
Direct image along base change for the small étale sites, followed by restriction to the small
affine étale site of `S`, is restriction to the small affine étale site of `T` followed by direct
image along base change for the small affine étale sites.

Both direct images are restriction along a base change functor of sites, so this is
`AlgebraicGeometry.smallAffineEtaleBaseChange_comp_inclusion` — the equality of the two composites
of site functors — read on sheaves, restriction along a composite being the composite of the
restrictions up to the canonical comparison. -/
def inclusionPushforwardBaseChangeIso :
    (smallEtaleBaseChange B f).sheafPushforwardContinuous A
          (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property) ⋙
        (inclusion B S.obj S.property).sheafPushforwardContinuous A
          (topology B S.obj S.property) (SmallEtale.topology B S.obj S.property) ≅
      (inclusion B T.obj T.property).sheafPushforwardContinuous A
          (topology B T.obj T.property) (SmallEtale.topology B T.obj T.property) ⋙
        (smallAffineEtaleBaseChange B f).sheafPushforwardContinuous A
          (topology B S.obj S.property) (topology B T.obj T.property) := by
  have hc : (inclusion B S.obj S.property ⋙ smallEtaleBaseChange B f).IsContinuous
      (topology B S.obj S.property) (SmallEtale.topology B T.obj T.property) :=
    Functor.isContinuous_comp _ _ _ (SmallEtale.topology B S.obj S.property) _
  exact Functor.sheafPushforwardContinuousComp' (F := inclusion B S.obj S.property)
      (G := smallEtaleBaseChange B f) (Iso.refl _) _ _ _ _ ≪≫
    (Functor.sheafPushforwardContinuousComp' (F := smallAffineEtaleBaseChange B f)
      (G := inclusion B T.obj T.property)
      (eqToIso (smallAffineEtaleBaseChange_comp_inclusion B f)) _ _ _ _).symm

section Pullback

variable
  {LE : Sheaf (SmallEtale.topology B S.obj S.property) A ⥤
    Sheaf (SmallEtale.topology B T.obj T.property) A}
  {LA : Sheaf (topology B S.obj S.property) A ⥤ Sheaf (topology B T.obj T.property) A}
  {ES : Sheaf (topology B S.obj S.property) A ⥤ Sheaf (SmallEtale.topology B S.obj S.property) A}
  {ET : Sheaf (topology B T.obj T.property) A ⥤ Sheaf (SmallEtale.topology B T.obj T.property) A}
  (adjE : LE ⊣ (smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property))
  (adjA : LA ⊣ (smallAffineEtaleBaseChange B f).sheafPushforwardContinuous A
      (topology B S.obj S.property) (topology B T.obj T.property))
  (adjS : ES ⊣ (inclusion B S.obj S.property).sheafPushforwardContinuous A
      (topology B S.obj S.property) (SmallEtale.topology B S.obj S.property))
  (adjT : ET ⊣ (inclusion B T.obj T.property).sheafPushforwardContinuous A
      (topology B T.obj T.property) (SmallEtale.topology B T.obj T.property))

/-- **Restriction to the small affine étale site has the same inverse image along base change.**
The left adjoint of restriction to the small affine étale site of `S`, followed by inverse image
along base change for the small étale sites, is inverse image along base change for the small
affine étale sites followed by the left adjoint of restriction to the small affine étale site of
`T`.

This is `AlgebraicGeometry.SmallAffineEtale.inclusionPushforwardBaseChangeIso` read on left
adjoints: the two composites of direct images are isomorphic, hence the two composites of their
left adjoints are, canonically. -/
def inclusionPullbackBaseChangeIso : ES ⋙ LE ≅ LA ⋙ ET :=
  Adjunction.leftAdjointUniq
    ((adjS.comp adjE).ofNatIsoRight (inclusionPushforwardBaseChangeIso B f A))
    (adjA.comp adjT)

/-- **The comparison of inverse images is the one whose conjugate is the comparison of direct
images.** Conjugation under the two composite adjunctions is a bijection, so this equation
determines `AlgebraicGeometry.SmallAffineEtale.inclusionPullbackBaseChangeIso` completely, and in
particular makes it independent of which left adjoints of the four direct images were chosen. -/
theorem conjugateEquiv_inclusionPullbackBaseChangeIso_hom :
    conjugateEquiv (adjA.comp adjT) (adjS.comp adjE)
        (inclusionPullbackBaseChangeIso B f A adjE adjA adjS adjT).hom =
      (inclusionPushforwardBaseChangeIso B f A).inv :=
  Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
    (adjS.comp adjE) (inclusionPushforwardBaseChangeIso B f A) (adjA.comp adjT)

end Pullback

section Equivalence

open Stacks.EtaleCohomology.BaseChangeAlgebraSystem

attribute [local instance]
  Stacks.EtaleCohomology.BaseChangeAlgebraSystem.isCocontinuous_smallAffineEtaleInclusion
  Stacks.EtaleCohomology.BaseChangeAlgebraSystem.hasSheafify_smallAffineEtale
  Stacks.EtaleCohomology.BaseChangeAlgebraSystem.hasSheafify_smallEtale
  Stacks.EtaleCohomology.BaseChangeAlgebraSystem.restrictToAffineEtale_isEquivalence

/-- **The equivalence of Stacks 04HR commutes with inverse image along base change.** The version
of `AlgebraicGeometry.SmallAffineEtale.inclusionPullbackBaseChangeIso` in which the two left
adjoints of the restrictions are the quasi-inverses of the equivalences
`Stacks.EtaleCohomology.BaseChangeAlgebraSystem.restrictToAffineEtale` are, by Stacks 04HR on
sheaves. -/
def inclusionEquivPullbackBaseChangeIso
    {LE : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B T.obj T.property) AddCommGrpCat.{u + 1}}
    {LA : Sheaf (topology B S.obj S.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (topology B T.obj T.property) AddCommGrpCat.{u + 1}}
    (adjE : LE ⊣ (smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property))
    (adjA : LA ⊣ (smallAffineEtaleBaseChange B f).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (topology B S.obj S.property) (topology B T.obj T.property)) :
    (restrictToAffineEtale B S.obj S.property).asEquivalence.inverse ⋙ LE ≅
      LA ⋙ (restrictToAffineEtale B T.obj T.property).asEquivalence.inverse :=
  inclusionPullbackBaseChangeIso B f AddCommGrpCat.{u + 1} adjE adjA
    (restrictToAffineEtale B S.obj S.property).asEquivalence.symm.toAdjunction
    (restrictToAffineEtale B T.obj T.property).asEquivalence.symm.toAdjunction

end Equivalence

end AlgebraicGeometry.SmallAffineEtale

namespace Stacks.EtaleCohomology.TransitionBaseChange

universe v u

open AlgebraicGeometry

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : Iᵒᵖ ⥤ Scheme.{max u v}} {c : Limits.Cone D}
  {B : AlgebraicGeometry.BigEtaleSite.{max u v}}
  {hD : ∀ i, B.Contains (D.obj i)} {hX : B.Contains c.pt}
  (E : AffineEtaleSiteColimit D c B hD hX)

variable {i j : E.system.I} (a : i ⟶ j)
  [IsAffine (D.obj (stage E i))] [IsAffine (D.obj (stage E j))]

/-- **The transition functor of the site system of Stacks 0EYL is base change of small affine
étale sites.** The small affine étale companion of
`Stacks.EtaleCohomology.TransitionBaseChange.transitionIso`, which states the same thing after
composing with the inclusion into the small étale site.

It is not a second construction of the comparison. Base change between small affine étale
categories followed by that inclusion *is* the inclusion followed by base change between small
étale categories (`AlgebraicGeometry.smallAffineEtaleBaseChange_comp_inclusion`), so
`transitionIso` is already an isomorphism of the two composites below followed by the inclusion;
the inclusion is fully faithful, and this is `transitionIso` with it cancelled. In particular the
two coherence laws `transitionIso_id_hom_app` and `transitionIso_comp_hom_app` are statements
about this comparison too, by `transitionAffineIso_hom_app_inclusion`. -/
def transitionAffineIso :
    E.system.u a ⋙ (E.levelEquiv i).functor ≅
      (E.levelEquiv j).functor ⋙
        AlgebraicGeometry.smallAffineEtaleBaseChange B (stageMap E a) :=
  Functor.fullyFaithfulCancelRight
    (AlgebraicGeometry.SmallAffineEtale.inclusion B (D.obj (stage E i)) (hD (stage E i)))
    (transitionIso E a)

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- **The components of `transitionAffineIso` are those of `transitionIso`.** Read in the small
étale site of `X_i`, the small affine étale comparison is the comparison of the two fibre-product
squares that `componentIso_hom_fst` and `componentIso_hom_snd` pin down, so everything proved
about `transitionIso` — in particular its identity and composition laws — holds of it. -/
@[simp]
theorem transitionAffineIso_hom_app_inclusion (Y : E.system.C j) :
    (AlgebraicGeometry.SmallAffineEtale.inclusion B (D.obj (stage E i)) (hD (stage E i))).map
        ((transitionAffineIso E a).hom.app Y) =
      (transitionIso E a).hom.app Y :=
  Functor.map_preimage _ _

/-! ### The coherence of the small affine étale comparison

The two laws below are `Stacks.EtaleCohomology.TransitionBaseChange.transitionIso_id_hom_app` and
`.transitionIso_comp_hom_app` read in the small affine étale site. Nothing is reproved: the
inclusion of the small affine étale category into the small étale one is faithful, it carries
`transitionAffineIso` to `transitionIso` (`transitionAffineIso_hom_app_inclusion`) and the small
affine étale transports of base change to the small étale ones
(`AlgebraicGeometry.smallAffineEtaleBaseChange_factoredIdIso_hom_app_inclusion` and
`..._factoredCompIso_hom_app_inclusion`), so each law *is* the corresponding small étale law
after applying the inclusion.
-/

section AffineCoherence

/-- **Base change along the transition morphism of an identity arrow is the identity functor**, on
small affine étale categories. The small affine étale companion of
`Stacks.EtaleCohomology.TransitionBaseChange.stageIdIso`. -/
def stageAffineIdIso (i : E.system.I) [IsAffine (D.obj (stage E i))] :
    AlgebraicGeometry.smallAffineEtaleBaseChange B (stageMap E (𝟙 i)) ≅
      𝟭 (AlgebraicGeometry.SmallAffineEtale B (D.obj (stage E i)) (hD (stage E i))) :=
  AlgebraicGeometry.smallAffineEtaleBaseChange_factoredIdIso B (stageMap E (𝟙 i))
    (stageMap_id E i)

/-- **Base change along the transition morphisms of `a` and `b` composes to base change along the
transition morphism of `a ≫ b`**, on small affine étale categories. The small affine étale
companion of `Stacks.EtaleCohomology.TransitionBaseChange.stageCompIso`. -/
def stageAffineCompIso {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k)
    [IsAffine (D.obj (stage E i))] [IsAffine (D.obj (stage E j))]
    [IsAffine (D.obj (stage E k))] :
    AlgebraicGeometry.smallAffineEtaleBaseChange B (stageMap E b) ⋙
        AlgebraicGeometry.smallAffineEtaleBaseChange B (stageMap E a) ≅
      AlgebraicGeometry.smallAffineEtaleBaseChange B (stageMap E (a ≫ b)) :=
  AlgebraicGeometry.smallAffineEtaleBaseChange_factoredCompIso B (stageMap E a) (stageMap E b)
    (stageMap E (a ≫ b)) (stageMap_comp E a b).symm

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- **The identity law of the small affine étale comparison.** At an identity arrow of the index
category `transitionAffineIso` is, read across `stageAffineIdIso`, the canonical identification of
`(system.u (𝟙 i)).obj Y` with `Y` coming from `InverseSystemOfFiniteSites.id_map`.

This is `Stacks.EtaleCohomology.TransitionBaseChange.transitionIso_id_hom_app` read in the small
affine étale site, through the faithfulness of the inclusion. -/
theorem transitionAffineIso_id_hom_app (i : E.system.I) [IsAffine (D.obj (stage E i))]
    (Y : E.system.C i) :
    (transitionAffineIso E (𝟙 i)).hom.app Y ≫
        (stageAffineIdIso E i).hom.app ((E.levelEquiv i).functor.obj Y) =
      (E.levelEquiv i).functor.map (eqToHom (Functor.congr_obj (E.system.id_map i) Y)) := by
  refine (AlgebraicGeometry.SmallAffineEtale.inclusion B (D.obj (stage E i))
    (hD (stage E i))).map_injective ?_
  have h2 : (AlgebraicGeometry.SmallAffineEtale.inclusion B (D.obj (stage E i))
        (hD (stage E i))).map
      ((stageAffineIdIso E i).hom.app ((E.levelEquiv i).functor.obj Y)) =
      (stageIdIso E i).hom.app ((levelEtale E i).obj Y) :=
    AlgebraicGeometry.smallAffineEtaleBaseChange_factoredIdIso_hom_app_inclusion B
      (stageMap E (𝟙 i)) (stageMap_id E i) ((E.levelEquiv i).functor.obj Y)
  rw [Functor.map_comp, transitionAffineIso_hom_app_inclusion E (𝟙 i) Y, h2]
  exact transitionIso_id_hom_app E i Y

omit [Nonempty I] [IsDirected I (· ≤ ·)] in
/-- **The composition law of the small affine étale comparison.** At a composite `a ≫ b` the
comparison is the comparison at `a`, followed by the base change along `stageMap a` of the
comparison at `b`, read across `stageAffineCompIso` and the canonical identification coming from
`InverseSystemOfFiniteSites.comp`.

This is `Stacks.EtaleCohomology.TransitionBaseChange.transitionIso_comp_hom_app` read in the small
affine étale site, through the faithfulness of the inclusion. -/
theorem transitionAffineIso_comp_hom_app {i j k : E.system.I} (a : i ⟶ j) (b : j ⟶ k)
    [IsAffine (D.obj (stage E i))] [IsAffine (D.obj (stage E j))]
    [IsAffine (D.obj (stage E k))] (Y : E.system.C k) :
    (transitionAffineIso E (a ≫ b)).hom.app Y =
      (E.levelEquiv i).functor.map (eqToHom (Functor.congr_obj (E.system.comp a b) Y)) ≫
        (transitionAffineIso E a).hom.app ((E.system.u b).obj Y) ≫
          (AlgebraicGeometry.smallAffineEtaleBaseChange B (stageMap E a)).map
              ((transitionAffineIso E b).hom.app Y) ≫
            (stageAffineCompIso E a b).hom.app ((E.levelEquiv k).functor.obj Y) := by
  refine (AlgebraicGeometry.SmallAffineEtale.inclusion B (D.obj (stage E i))
    (hD (stage E i))).map_injective ?_
  have hbc : (AlgebraicGeometry.SmallAffineEtale.inclusion B (D.obj (stage E i))
        (hD (stage E i))).map
      ((AlgebraicGeometry.smallAffineEtaleBaseChange B (stageMap E a)).map
        ((transitionAffineIso E b).hom.app Y)) =
      (AlgebraicGeometry.smallEtaleBaseChange B (stageMap E a)).map
        ((transitionIso E b).hom.app Y) :=
    (AlgebraicGeometry.inclusion_map_smallAffineEtaleBaseChange_map B (stageMap E a)
      ((transitionAffineIso E b).hom.app Y)).trans
      (congrArg (AlgebraicGeometry.smallEtaleBaseChange B (stageMap E a)).map
        (transitionAffineIso_hom_app_inclusion E b Y))
  have hcc : (AlgebraicGeometry.SmallAffineEtale.inclusion B (D.obj (stage E i))
        (hD (stage E i))).map
      ((stageAffineCompIso E a b).hom.app ((E.levelEquiv k).functor.obj Y)) =
      (stageCompIso E a b).hom.app ((levelEtale E k).obj Y) :=
    AlgebraicGeometry.smallAffineEtaleBaseChange_factoredCompIso_hom_app_inclusion B
      (stageMap E a) (stageMap E b) (stageMap E (a ≫ b)) (stageMap_comp E a b).symm
      ((E.levelEquiv k).functor.obj Y)
  rw [transitionAffineIso_hom_app_inclusion E (a ≫ b) Y, Functor.map_comp, Functor.map_comp,
    Functor.map_comp, transitionAffineIso_hom_app_inclusion E a ((E.system.u b).obj Y), hbc, hcc]
  exact transitionIso_comp_hom_app E a b Y

end AffineCoherence

end Stacks.EtaleCohomology.TransitionBaseChange

namespace Stacks.EtaleCohomology.AffineLimitCohomology

universe v' u' v u

open AlgebraicGeometry CategoryTheory.Sites.InverseSystem
open Stacks.EtaleCohomology.BaseChangeAlgebraSystem

attribute [local instance] isDenseSubsite_levelFunctor

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Limits.Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)
  (hc : Limits.IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
  [∀ i : Iᵒᵖ, IsAffine (D.obj i)]
  {i j : (sys D c B hD hX hc).I} (a : i ⟶ j)
  (A : Type u') [Category.{v'} A]


omit [∀ i : Iᵒᵖ, IsAffine (D.obj i)] in
/-- **The transition functor of the site system of Stacks 0EYL is continuous**, in the spelling
in which the statement below needs it. `InverseSystemOfFiniteSites.continuous` is a theorem rather
than an instance — continuity is half of the system's `isMorphismOfSites` field — so instance
search does not find it on its own. -/
theorem isContinuous_sysTransition :
    ((sys D c B hD hX hc).u a).IsContinuous ((sys D c B hD hX hc).J j)
      ((sys D c B hD hX hc).J i) :=
  (sys D c B hD hX hc).continuous a

/-- **Base change between the small affine étale sites of two levels is continuous**, in the
spelling in which the statement below needs it.
`AlgebraicGeometry.smallAffineEtaleBaseChange_isContinuous` is stated for a morphism of
`B.Scheme`, so its conclusion names the topologies of `(B.obj (D.obj _) _).obj`, which is
definitionally but not syntactically the `levelScheme` carried here, and instance search cannot
pass between the two spellings. This is the restatement it does find, in the style of
`AlgebraicGeometry.SmallEtale.isContinuous_inclusionSmallEtaleBaseChange`. -/
theorem isContinuous_smallAffineEtaleBaseChange_stageMap :
    (AlgebraicGeometry.smallAffineEtaleBaseChange B
        (TransitionBaseChange.stageMap (affineEtaleSiteColimit D c B hD hX hc) a)).IsContinuous
      (AlgebraicGeometry.SmallAffineEtale.topology B (levelScheme D c B hD hX hc j)
        (hD (levelIndex D c B hD hX hc j)))
      (AlgebraicGeometry.SmallAffineEtale.topology B (levelScheme D c B hD hX hc i)
        (hD (levelIndex D c B hD hX hc i))) :=
  AlgebraicGeometry.smallAffineEtaleBaseChange_isContinuous B _

attribute [local instance] isContinuous_sysTransition
  isContinuous_smallAffineEtaleBaseChange_stageMap

/-- **Restriction to a level of the system of Stacks 0EYL has the same direct image along base
change.** Restriction to the level `i`, followed by direct image along the transition functor of
an arrow `a : i ⟶ j`, is direct image along base change of small affine étale sites followed by
restriction to the level `j`.

Both direct images are restriction along a site functor, so this is the comparison
`Stacks.EtaleCohomology.TransitionBaseChange.transitionAffineIso` of the transition functor with
base change, read on sheaves. -/
def levelPushforwardBaseChangeIso :
    (levelAffineEtaleFunctor D c B hD hX hc i).sheafPushforwardContinuous A
          ((sys D c B hD hX hc).J i)
          (AlgebraicGeometry.SmallAffineEtale.topology B (levelScheme D c B hD hX hc i)
            (hD (levelIndex D c B hD hX hc i))) ⋙
        ((sys D c B hD hX hc).u a).sheafPushforwardContinuous A ((sys D c B hD hX hc).J j)
          ((sys D c B hD hX hc).J i) ≅
      (AlgebraicGeometry.smallAffineEtaleBaseChange B
            (TransitionBaseChange.stageMap
              (affineEtaleSiteColimit D c B hD hX hc) a)).sheafPushforwardContinuous A
          (AlgebraicGeometry.SmallAffineEtale.topology B (levelScheme D c B hD hX hc j)
            (hD (levelIndex D c B hD hX hc j)))
          (AlgebraicGeometry.SmallAffineEtale.topology B (levelScheme D c B hD hX hc i)
            (hD (levelIndex D c B hD hX hc i))) ⋙
        (levelAffineEtaleFunctor D c B hD hX hc j).sheafPushforwardContinuous A
          ((sys D c B hD hX hc).J j)
          (AlgebraicGeometry.SmallAffineEtale.topology B (levelScheme D c B hD hX hc j)
            (hD (levelIndex D c B hD hX hc j))) := by
  have hc1 : ((sys D c B hD hX hc).u a ⋙ levelAffineEtaleFunctor D c B hD hX hc i).IsContinuous
      ((sys D c B hD hX hc).J j)
      (AlgebraicGeometry.SmallAffineEtale.topology B (levelScheme D c B hD hX hc i)
        (hD (levelIndex D c B hD hX hc i))) :=
    Functor.isContinuous_comp _ _ _ ((sys D c B hD hX hc).J i) _
  exact Functor.sheafPushforwardContinuousComp' (F := (sys D c B hD hX hc).u a)
      (G := levelAffineEtaleFunctor D c B hD hX hc i) (Iso.refl _) _ _ _ _ ≪≫
    (Functor.sheafPushforwardContinuousComp' (F := levelAffineEtaleFunctor D c B hD hX hc j)
      (G := AlgebraicGeometry.smallAffineEtaleBaseChange B
        (TransitionBaseChange.stageMap (affineEtaleSiteColimit D c B hD hX hc) a))
      (TransitionBaseChange.transitionAffineIso
        (affineEtaleSiteColimit D c B hD hX hc) a).symm _ _ _ _).symm

section Pullback

variable
  {LU : Sheaf ((sys D c B hD hX hc).J j) A ⥤ Sheaf ((sys D c B hD hX hc).J i) A}
  {LBC : Sheaf (AlgebraicGeometry.SmallAffineEtale.topology B (levelScheme D c B hD hX hc j)
            (hD (levelIndex D c B hD hX hc j))) A ⥤
          Sheaf (AlgebraicGeometry.SmallAffineEtale.topology B (levelScheme D c B hD hX hc i)
            (hD (levelIndex D c B hD hX hc i))) A}
  {EI : Sheaf ((sys D c B hD hX hc).J i) A ⥤
          Sheaf (AlgebraicGeometry.SmallAffineEtale.topology B (levelScheme D c B hD hX hc i)
            (hD (levelIndex D c B hD hX hc i))) A}
  {EJ : Sheaf ((sys D c B hD hX hc).J j) A ⥤
          Sheaf (AlgebraicGeometry.SmallAffineEtale.topology B (levelScheme D c B hD hX hc j)
            (hD (levelIndex D c B hD hX hc j))) A}
  (adjU : LU ⊣ ((sys D c B hD hX hc).u a).sheafPushforwardContinuous A
      ((sys D c B hD hX hc).J j) ((sys D c B hD hX hc).J i))
  (adjBC : LBC ⊣ (AlgebraicGeometry.smallAffineEtaleBaseChange B
        (TransitionBaseChange.stageMap
          (affineEtaleSiteColimit D c B hD hX hc) a)).sheafPushforwardContinuous A
        (AlgebraicGeometry.SmallAffineEtale.topology B (levelScheme D c B hD hX hc j)
          (hD (levelIndex D c B hD hX hc j)))
        (AlgebraicGeometry.SmallAffineEtale.topology B (levelScheme D c B hD hX hc i)
          (hD (levelIndex D c B hD hX hc i))))
  (adjI : EI ⊣ (levelAffineEtaleFunctor D c B hD hX hc i).sheafPushforwardContinuous A
      ((sys D c B hD hX hc).J i)
      (AlgebraicGeometry.SmallAffineEtale.topology B (levelScheme D c B hD hX hc i)
        (hD (levelIndex D c B hD hX hc i))))
  (adjJ : EJ ⊣ (levelAffineEtaleFunctor D c B hD hX hc j).sheafPushforwardContinuous A
      ((sys D c B hD hX hc).J j)
      (AlgebraicGeometry.SmallAffineEtale.topology B (levelScheme D c B hD hX hc j)
        (hD (levelIndex D c B hD hX hc j))))

/-- **Restriction to a level of the system of Stacks 0EYL has the same inverse image along base
change.** Inverse image along the transition functor of `a : i ⟶ j`, followed by the left adjoint
of restriction to the level `i`, is the left adjoint of restriction to the level `j` followed by
inverse image along base change of small affine étale sites.

This is `levelPushforwardBaseChangeIso` read on left adjoints. -/
def levelPullbackBaseChangeIso : LU ⋙ EI ≅ EJ ⋙ LBC :=
  Adjunction.leftAdjointUniq
    ((adjU.comp adjI).ofNatIsoRight (levelPushforwardBaseChangeIso D c B hD hX hc a A))
    (adjJ.comp adjBC)

/-- **The comparison of inverse images is the one whose conjugate is the comparison of direct
images.** Conjugation under the two composite adjunctions is a bijection, so this equation
determines `levelPullbackBaseChangeIso` completely, and in particular makes it independent of
which left adjoints of the four direct images were chosen. -/
theorem conjugateEquiv_levelPullbackBaseChangeIso_hom :
    conjugateEquiv (adjJ.comp adjBC) (adjU.comp adjI)
        (levelPullbackBaseChangeIso D c B hD hX hc a A adjU adjBC adjI adjJ).hom =
      (levelPushforwardBaseChangeIso D c B hD hX hc a A).inv :=
  Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom
    (adjU.comp adjI) (levelPushforwardBaseChangeIso D c B hD hX hc a A) (adjJ.comp adjBC)

end Pullback

section Equivalence

attribute [local instance] hasSheafify_level restrictToLevel_isEquivalence

/-- **The level equivalence of Stacks 0EYL commutes with inverse image along base change.** The
version of `levelPullbackBaseChangeIso` in which the two left adjoints of the restrictions are the
quasi-inverses of the equivalences `restrictToLevel` are. -/
def levelEquivPullbackBaseChangeIso
    {LU : Sheaf ((sys D c B hD hX hc).J j) AddCommGrpCat.{max u v + 1} ⥤
      Sheaf ((sys D c B hD hX hc).J i) AddCommGrpCat.{max u v + 1}}
    {LBC : Sheaf (AlgebraicGeometry.SmallAffineEtale.topology B (levelScheme D c B hD hX hc j)
          (hD (levelIndex D c B hD hX hc j))) AddCommGrpCat.{max u v + 1} ⥤
        Sheaf (AlgebraicGeometry.SmallAffineEtale.topology B (levelScheme D c B hD hX hc i)
          (hD (levelIndex D c B hD hX hc i))) AddCommGrpCat.{max u v + 1}}
    (adjU : LU ⊣ ((sys D c B hD hX hc).u a).sheafPushforwardContinuous
      AddCommGrpCat.{max u v + 1} ((sys D c B hD hX hc).J j) ((sys D c B hD hX hc).J i))
    (adjBC : LBC ⊣ (AlgebraicGeometry.smallAffineEtaleBaseChange B
        (TransitionBaseChange.stageMap
          (affineEtaleSiteColimit D c B hD hX hc) a)).sheafPushforwardContinuous
      AddCommGrpCat.{max u v + 1}
      (AlgebraicGeometry.SmallAffineEtale.topology B (levelScheme D c B hD hX hc j)
        (hD (levelIndex D c B hD hX hc j)))
      (AlgebraicGeometry.SmallAffineEtale.topology B (levelScheme D c B hD hX hc i)
        (hD (levelIndex D c B hD hX hc i)))) :
    LU ⋙ (restrictToLevel D c B hD hX hc i).asEquivalence.inverse ≅
      (restrictToLevel D c B hD hX hc j).asEquivalence.inverse ⋙ LBC :=
  levelPullbackBaseChangeIso D c B hD hX hc a AddCommGrpCat.{max u v + 1} adjU adjBC
    (restrictToLevel D c B hD hX hc i).asEquivalence.symm.toAdjunction
    (restrictToLevel D c B hD hX hc j).asEquivalence.symm.toAdjunction

end Equivalence

end Stacks.EtaleCohomology.AffineLimitCohomology
