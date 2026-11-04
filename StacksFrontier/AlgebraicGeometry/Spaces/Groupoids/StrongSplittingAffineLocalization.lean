module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantOpenSubgroupoid
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.RestrictionProperties
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.GroupoidInverse
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.InvariantAffineOpen
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.IteratedRestrictionSplitting
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SchemeSplittings
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingDerealizationResiduePoint

/-!
# Shrinking a splitting to an affine étale neighbourhood

Let `(U, R, s, t, c)` be a groupoid scheme with `U` affine and with `s` and `t` flat and locally
of finite presentation, and let `u` be a point of `U`.  Suppose given the output of
**Stacks 04RX**: a scheme `U'`, a separated étale morphism `U' ⟶ U`, a point `u'` of `U'` over
`u` with `κ(u) = κ(u')`, and a strong splitting `P` of `R' = R|_{U'}` over `u'`.  Then `U'` can
be shrunk to an *affine* étale neighbourhood: there is an affine open `U'' ⊆ U'` containing `u'`
such that the restriction of `R'` to `U''` is strongly split over `u'`.  This is
**Stacks 04RZ**.

The shrinking is the source's.  Because `s` and `t` are flat and locally of finite presentation,
so are `s'` and `t'` (Stacks 04MV), hence so are their restrictions to the open subscheme `P` of
the arrow scheme of `R'`; those restrictions are finite by the definition of a splitting, so
they are finite locally free (Stacks 02KB).  The orbit `t|_P(s|_P^{-1}(u'))` of `u'` under `P` is
therefore a finite set of points of `U'`, and since `U` is affine and `U' ⟶ U` is separated and
quasi-finite, Stacks 07S0 puts that finite set inside a single affine open of `U'`.  Stacks 03JE
then produces a `P`-invariant affine open `U'' ⊆ U'` containing `u'`, and the restriction of `P`
to `U''` — which is a subgroupoid precisely because `U''` is `P`-invariant — is a strong
splitting of `R'|_{U''}` over `u'`.

**Stacks 04S0** is the same statement with "strong splitting" replaced by "quasi-splitting" and
Stacks 04RX replaced by Stacks 04RY, and the source proves it by rerunning that argument; it is
proved here the same way.  The first three paragraphs are literally shared, as
`Stacks.Groupoids.GroupoidScheme.exists_isAffineOpen_isInvariantOpen_of_openFiniteSubgroupoid`,
since they use nothing about the splitting beyond conditions (a) and (b) of Stacks 04RK.  The
last paragraph is cheaper in the quasi-splitting case: condition (c) of part (3) of Stacks 04RK
holds for every open finite subgroupoid at every point, by the footnote to that part of the tag,
so no argument about the stabilizer of `u''` is needed.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.EtaleStrongSplitting`: the output of **Stacks 04RX** in the
  form its consumer uses — a separated étale morphism `U' ⟶ U`, a point of `U'` over the given
  point with the same residue field, the restriction `R|_{U'}` and a strong splitting of it over
  that point.
* `Stacks.Groupoids.GroupoidScheme.EtaleQuasiSplitting`: the same for the output of
  **Stacks 04RY**, with a quasi-splitting in place of the strong splitting.
* `Stacks.Groupoids.GroupoidScheme.invariantOpenToObjects` and
  `Stacks.Groupoids.GroupoidScheme.invariantOpenToArrows`: the two open immersions, into the
  object scheme and into the arrow scheme of the ambient groupoid, carried by an invariant open
  of the object scheme of an open finite subgroupoid.

## Main results

* `Stacks.Groupoids.GroupoidScheme.isStronglySplitAt_restrictInvariantOpen`: the last paragraph
  of the proof of Stacks 04RZ, isolated.  If `P` is a strong splitting of `R` over `u` and `V` is
  a `P`-invariant open of the object scheme, then the restriction of `P` to `V` is a strong
  splitting of `R|_V` over every point of `V` lying over `u`.
* `Stacks.Groupoids.GroupoidScheme.exists_isAffine_isStronglySplitAt`: **Stacks 04RZ**,
  conditional on Stacks 04RX as described above.
* `Stacks.Groupoids.GroupoidScheme.exists_isAffine_isQuasiSplitAt`: the shrinking step of
  **Stacks 04S0**, taking the output of Stacks 04RY in the same way, and with `R|_{U''}` read as
  the restriction of `R` along the composite `U'' ⟶ U' ⟶ U`.  Stacks 04S0 itself is
  `Stacks.Groupoids.GroupoidScheme.exists_isAffine_isQuasiSplitAt_of_quasiSplittingSituation`.

## Implementation notes

Both the hypothesis and the conclusion are about restrictions of groupoid schemes, which this
library realizes by `AlgebraicGeometry.GroupoidScheme.Restriction`: a groupoid scheme whose
object scheme is *equal* to the scheme being restricted to and whose arrow scheme is *equal* to
the chosen iterated fibre product `AlgebraicGeometry.restrictionArrows`.  Two consequences shape
what is proved here.

First, the conclusion is stated for an arbitrary groupoid scheme realizing the restriction, not
for the realization `AlgebraicGeometry.GroupoidScheme.restrict` built by `Classical.choice`,
whose identity and composition morphisms are opaque.  Nothing is lost, and the statement is in
fact stronger: the fields of `AlgebraicGeometry.GroupoidScheme.Restriction` pin down the object
scheme, the arrow scheme, the source, the target and the morphism to the ambient groupoid, and
`AlgebraicGeometry.GroupoidScheme.restriction_hom_ext` says that a generalized point of the
arrow scheme is determined by its source, its target and its underlying ambient arrow; so the
two morphism axioms `map_identity` and `map_comp` of the inclusion of the restricted splitting
are *derived* from that uniqueness principle rather than computed, and the construction applies
verbatim to `AlgebraicGeometry.GroupoidScheme.restrict`.

Second, the ambient groupoid of the conclusion is the restriction of `R' = R|_{U'}` to `U''`
rather than the restriction of `R` to `U''`; this is recorded in the attribute string on
`Stacks.Groupoids.GroupoidScheme.exists_isAffine_isStronglySplitAt`.  The two are canonically
isomorphic — that is Stacks 04MW, available in this library as the comparison diagram
`AlgebraicGeometry.doubleRestrictionDiagram` — but they are not *equal*, and
`AlgebraicGeometry.GroupoidScheme.Restriction` demands equality with the chosen iterated fibre
product, so a realization of one is not a realization of the other.  Restricting in two steps is
also what makes the inclusion of the restricted splitting an open immersion cheaply: the
restricting morphism `U'' ⟶ U'` is then an open immersion, so
`AlgebraicGeometry.restrictionArrowsToArrows` is an open immersion as well and the inclusion is
an open immersion by cancellation.  Restricting `R` along the composite `U'' ⟶ U' ⟶ U` in one
step replaces that open immersion by an étale morphism, for which the cancellation fails.  For
Stacks 04S0 the restriction of `R` along the composite is reached afterwards, by transporting
the quasi-splitting along that comparison with
`AlgebraicGeometry.GroupoidScheme.isQuasiSplitAt_of_iteratedRestriction'`, so there both
readings are asserted.

The `P`-invariant open is turned into a groupoid scheme by
`Stacks.Groupoids.restrictInvariantOpen`, whose arrow scheme is literally the open subscheme
`(s|_P)^{-1}(V)` of the arrow scheme of `P`; this is the equality
`P|_V = (s|_P)^{-1}(V) = (t|_P)^{-1}(V)` that the source records.  Everything below is phrased
through the morphism of groupoid schemes `Stacks.Groupoids.restrictInvariantOpenHom` rather than
through the restricted structure morphisms themselves, so that no step depends on unfolding
`Stacks.Groupoids.restrictInvariantOpen`.  Finiteness of its source morphism is finiteness of
the restriction of `s|_P` to an open of the target, which holds because being finite is Zariski
local on the target; finiteness of its target morphism is then obtained from the inverse
morphism, which is an isomorphism on underlying schemes, exactly as in
`AlgebraicGeometry.restriction_target_mem`.

## References

* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 03JE](https://stacks.math.columbia.edu/tag/03JE)
* [Stacks Project, Tag 04MV](https://stacks.math.columbia.edu/tag/04MV)
* [Stacks Project, Tag 04MW](https://stacks.math.columbia.edu/tag/04MW)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 04RL](https://stacks.math.columbia.edu/tag/04RL)
* [Stacks Project, Tag 04RV](https://stacks.math.columbia.edu/tag/04RV)
* [Stacks Project, Tag 04RX](https://stacks.math.columbia.edu/tag/04RX)
* [Stacks Project, Tag 04RY](https://stacks.math.columbia.edu/tag/04RY)
* [Stacks Project, Tag 04RZ](https://stacks.math.columbia.edu/tag/04RZ)
* [Stacks Project, Tag 04S0](https://stacks.math.columbia.edu/tag/04S0)
* [Stacks Project, Tag 07S0](https://stacks.math.columbia.edu/tag/07S0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids Stacks.Morphisms

noncomputable section

universe u

namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}} {H : GroupoidScheme S}

/-! ### Generalized points of the arrow scheme of a restriction

The universal property of `AlgebraicGeometry.restrictionArrows` as an iterated fibre product, in
the two halves used below: a generalized point is *built* from a source, a target and an ambient
arrow, and it is *determined* by them. -/

/-- The generalized point of the arrow scheme of a restriction with prescribed source, target and
underlying arrow of the ambient groupoid. -/
def restrictionLift {U' T : Over S} (g : U' ⟶ H.objects) (s t : T ⟶ U')
    (a : T ⟶ H.arrows) (hs : s ≫ g = a ≫ H.source) (ht : t ≫ g = a ≫ H.target) :
    T ⟶ restrictionArrows H g :=
  pullback.lift (pullback.lift t a ht) (pullback.lift a s hs.symm)
    ((pullback.lift_snd _ _ _).trans (pullback.lift_fst _ _ _).symm)

/-- The source of `Stacks.Groupoids.GroupoidScheme.restrictionLift` is the prescribed one. -/
private theorem restrictionLift_source {U' T : Over S} (g : U' ⟶ H.objects) (s t : T ⟶ U')
    (a : T ⟶ H.arrows) (hs : s ≫ g = a ≫ H.source) (ht : t ≫ g = a ≫ H.target) :
    restrictionLift g s t a hs ht ≫ restrictionSource H g = s :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ pullback.snd H.source g) (pullback.lift_snd _ _ _)).trans
      (pullback.lift_snd _ _ _))

/-- The target of `Stacks.Groupoids.GroupoidScheme.restrictionLift` is the prescribed one. -/
private theorem restrictionLift_target {U' T : Over S} (g : U' ⟶ H.objects) (s t : T ⟶ U')
    (a : T ⟶ H.arrows) (hs : s ≫ g = a ≫ H.source) (ht : t ≫ g = a ≫ H.target) :
    restrictionLift g s t a hs ht ≫ restrictionTarget H g = t :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ pullback.fst g H.target) (pullback.lift_fst _ _ _)).trans
      (pullback.lift_fst _ _ _))

/-- The underlying ambient arrow of `Stacks.Groupoids.GroupoidScheme.restrictionLift` is the
prescribed one. -/
private theorem restrictionLift_arrow {U' T : Over S} (g : U' ⟶ H.objects) (s t : T ⟶ U')
    (a : T ⟶ H.arrows) (hs : s ≫ g = a ≫ H.source) (ht : t ≫ g = a ≫ H.target) :
    restrictionLift g s t a hs ht ≫ restrictionArrowsToArrows H g = a :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ pullback.snd g H.target) (pullback.lift_fst _ _ _)).trans
      (pullback.lift_snd _ _ _))

/-- `AlgebraicGeometry.GroupoidScheme.restriction_hom_ext` transported to an arbitrary groupoid
scheme realizing the restriction: a generalized point of its arrow scheme is determined by its
source, its target and its underlying arrow of the ambient groupoid. -/
private theorem restriction_hom_ext' {U' : Over S} (g : U' ⟶ H.objects)
    (R : AlgebraicGeometry.GroupoidScheme.Restriction H g) {T : Over S}
    (f h : T ⟶ R.groupoid.arrows)
    (hs : f ≫ R.groupoid.source = h ≫ R.groupoid.source)
    (ht : f ≫ R.groupoid.target = h ≫ R.groupoid.target)
    (ha : f ≫ R.hom.mapArrows = h ≫ R.hom.mapArrows) : f = h := by
  have key : f ≫ eqToHom R.arrows_eq = h ≫ eqToHom R.arrows_eq := by
    refine AlgebraicGeometry.GroupoidScheme.restriction_hom_ext H g _ _ ?_ ?_ ?_
    · rw [R.source_eq] at hs
      simp only [← Category.assoc] at hs
      exact (cancel_mono (eqToHom R.objects_eq.symm)).1 hs
    · rw [R.target_eq] at ht
      simp only [← Category.assoc] at ht
      exact (cancel_mono (eqToHom R.objects_eq.symm)).1 ht
    · rw [R.mapArrows_eq] at ha
      simpa only [← Category.assoc] using ha
  exact (cancel_mono (eqToHom R.arrows_eq)).1 key

/-- For a restriction along an open immersion the canonical morphism to the ambient arrow scheme
is an open immersion: it is the composite of two base changes of the restricting morphism. -/
private theorem restrictionArrowsToArrows_isOpenImmersion {U' : Over S} (g : U' ⟶ H.objects)
    [IsOpenImmersion g.left] : IsOpenImmersion (restrictionArrowsToArrows H g).left := by
  have hg : IsOpenImmersion ((Over.forget S).map g) := by
    show IsOpenImmersion g.left
    infer_instance
  have htarget : IsOpenImmersion (pullback.snd g H.target).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      ((IsPullback.of_hasPullback g H.target).map (Over.forget S)) hg
  have hsource : IsOpenImmersion (pullback.fst H.source g).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      ((IsPullback.of_hasPullback H.source g).flip.map (Over.forget S)) hg
  have hfst : IsOpenImmersion
      (pullback.fst (pullback.snd g H.target) (pullback.fst H.source g)).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      ((IsPullback.of_hasPullback (pullback.snd g H.target)
        (pullback.fst H.source g)).flip.map (Over.forget S)) hsource
  show IsOpenImmersion
    ((pullback.fst (pullback.snd g H.target) (pullback.fst H.source g)).left ≫
      (pullback.snd g H.target).left)
  have := hfst
  have := htarget
  infer_instance

/-- A transport along an equality of objects of `Over S` is an isomorphism on underlying schemes. -/
private instance isIso_eqToHom_left {X Y : Over S} (h : X = Y) : IsIso (eqToHom h).left :=
  inferInstanceAs (IsIso ((Over.forget S).map (eqToHom h)))

/-- The map on objects of a realization of a restriction is the restricting morphism up to the
transport along the equality of object schemes. -/
private theorem restriction_mapObjects_left {U' : Over S} (g : U' ⟶ H.objects)
    (R : AlgebraicGeometry.GroupoidScheme.Restriction H g) :
    R.hom.mapObjects.left = (eqToHom R.objects_eq).left ≫ g.left := by
  rw [R.mapObjects_eq]
  rfl

/-- The morphism to the ambient arrow scheme of an arbitrary groupoid scheme realizing a
restriction along an open immersion is an open immersion. -/
theorem isOpenImmersion_restriction_mapArrows {U' : Over S} (g : U' ⟶ H.objects)
    (R : AlgebraicGeometry.GroupoidScheme.Restriction H g) [IsOpenImmersion g.left] :
    IsOpenImmersion R.hom.mapArrows.left := by
  have h := restrictionArrowsToArrows_isOpenImmersion g
  rw [R.mapArrows_eq, Over.comp_left]
  infer_instance

/-! ### Two computations in an arbitrary groupoid scheme -/

/-- The source of a composite of two composable generalized arrows is the source of the second
one. -/
private theorem compose_comp_source (K : GroupoidScheme S) {T : Over S} (f g : T ⟶ K.arrows)
    (w : f ≫ K.source = g ≫ K.target) :
    K.compose f g w ≫ K.source = g ≫ K.source := by
  rw [GroupoidScheme.compose, Category.assoc, K.source_comp, ← Category.assoc,
    pullback.lift_snd]

/-- The target of a composite of two composable generalized arrows is the target of the first
one. -/
private theorem compose_comp_target (K : GroupoidScheme S) {T : Over S} (f g : T ⟶ K.arrows)
    (w : f ≫ K.source = g ≫ K.target) :
    K.compose f g w ≫ K.target = f ≫ K.target := by
  rw [GroupoidScheme.compose, Category.assoc, K.target_comp, ← Category.assoc,
    pullback.lift_fst]

/-- Composition of generalized arrows depends only on the two arrows, not on the proof that they
are composable. -/
private theorem compose_congr (K : GroupoidScheme S) {T : Over S} {f g f' g' : T ⟶ K.arrows}
    (hf : f = f') (hg : g = g') (w : f ≫ K.source = g ≫ K.target)
    (w' : f' ≫ K.source = g' ≫ K.target) : K.compose f g w = K.compose f' g' w' := by
  subst hf
  subst hg
  rfl

/-! ### The structure morphisms of an open finite subgroupoid -/

variable (P : OpenFiniteSubgroupoid H)

/-- The source morphism of an open finite subgroupoid is the restriction of the ambient source
morphism along the open immersion of arrow schemes. -/
private theorem openFiniteSubgroupoid_source_eq :
    P.subgroupoid.source = P.inclusion.mapArrows ≫ H.source ≫ eqToHom P.objects_eq.symm := by
  rw [← Category.assoc, P.inclusion.map_source, P.mapObjects_eq, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id]

/-- The target morphism of an open finite subgroupoid is the restriction of the ambient target
morphism along the open immersion of arrow schemes. -/
private theorem openFiniteSubgroupoid_target_eq :
    P.subgroupoid.target = P.inclusion.mapArrows ≫ H.target ≫ eqToHom P.objects_eq.symm := by
  rw [← Category.assoc, P.inclusion.map_target, P.mapObjects_eq, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id]

/-- The map on objects of the inclusion of an open finite subgroupoid is an isomorphism on
underlying schemes: it is a transport along the equality of object schemes. -/
private instance isIso_openFiniteSubgroupoid_mapObjects :
    IsIso P.inclusion.mapObjects.left := by
  rw [P.mapObjects_eq]
  infer_instance

/-- **Stacks 02KB** for a structure morphism of an open finite subgroupoid: it is finite by
definition, and flatness and local finite presentation are inherited from the ambient morphism
through the open immersion of arrow schemes, so it is finite locally free. -/
private theorem isFiniteLocallyFree_openFiniteSubgroupoid {a : P.subgroupoid.arrows ⟶ _}
    {b : H.arrows ⟶ H.objects} (hab : a = P.inclusion.mapArrows ≫ b ≫ eqToHom P.objects_eq.symm)
    (hfin : IsFinite a.left) [Flat b.left] [LocallyOfFinitePresentation b.left] :
    IsFiniteLocallyFree a.left := by
  have hopen := P.arrows_open
  have heq : a.left = P.inclusion.mapArrows.left ≫ b.left ≫ (eqToHom P.objects_eq.symm).left := by
    rw [hab]
    rfl
  refine (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mpr
    ⟨hfin, ?_, ?_⟩ <;> rw [heq] <;> infer_instance

/-- **Stacks 02KB** for the source morphism of an open finite subgroupoid. -/
private theorem isFiniteLocallyFree_openFiniteSubgroupoid_source
    [Flat H.source.left] [LocallyOfFinitePresentation H.source.left] :
    IsFiniteLocallyFree P.subgroupoid.source.left :=
  isFiniteLocallyFree_openFiniteSubgroupoid P (openFiniteSubgroupoid_source_eq P) P.source_finite

/-- **Stacks 02KB** for the target morphism of an open finite subgroupoid. -/
private theorem isFiniteLocallyFree_openFiniteSubgroupoid_target
    [Flat H.target.left] [LocallyOfFinitePresentation H.target.left] :
    IsFiniteLocallyFree P.subgroupoid.target.left :=
  isFiniteLocallyFree_openFiniteSubgroupoid P (openFiniteSubgroupoid_target_eq P) P.target_finite

/-! ### Restricting an open finite subgroupoid to an invariant open -/

variable (V : P.subgroupoid.objects.left.Opens) (hV : IsInvariantOpen P.subgroupoid V)

/-- The morphism from an invariant open of the object scheme of an open finite subgroupoid to the
ambient object scheme. -/
def invariantOpenToObjects : (restrictInvariantOpen P.subgroupoid V hV).objects ⟶ H.objects :=
  (restrictInvariantOpenHom P.subgroupoid V hV).mapObjects ≫ P.inclusion.mapObjects

/-- The morphism from the arrow scheme of the restriction of an open finite subgroupoid to an
invariant open to the ambient arrow scheme. -/
def invariantOpenToArrows : (restrictInvariantOpen P.subgroupoid V hV).arrows ⟶ H.arrows :=
  (restrictInvariantOpenHom P.subgroupoid V hV).mapArrows ≫ P.inclusion.mapArrows

/-- The morphism `invariantOpenToObjects` is an open immersion. -/
instance isOpenImmersion_invariantOpenToObjects :
    IsOpenImmersion (invariantOpenToObjects P V hV).left := by
  rw [invariantOpenToObjects, Over.comp_left]
  infer_instance

/-- The morphism `invariantOpenToArrows` is an open immersion. -/
instance isOpenImmersion_invariantOpenToArrows :
    IsOpenImmersion (invariantOpenToArrows P V hV).left := by
  have := P.arrows_open
  rw [invariantOpenToArrows, Over.comp_left]
  infer_instance

/-- The source morphism of the restricted subgroupoid lies over the ambient source morphism. -/
theorem invariantOpen_source_comp :
    (restrictInvariantOpen P.subgroupoid V hV).source ≫ invariantOpenToObjects P V hV =
      invariantOpenToArrows P V hV ≫ H.source := by
  rw [invariantOpenToObjects, invariantOpenToArrows, ← Category.assoc,
    ← (restrictInvariantOpenHom P.subgroupoid V hV).map_source, Category.assoc,
    ← P.inclusion.map_source, ← Category.assoc]

/-- The target morphism of the restricted subgroupoid lies over the ambient target morphism. -/
theorem invariantOpen_target_comp :
    (restrictInvariantOpen P.subgroupoid V hV).target ≫ invariantOpenToObjects P V hV =
      invariantOpenToArrows P V hV ≫ H.target := by
  rw [invariantOpenToObjects, invariantOpenToArrows, ← Category.assoc,
    ← (restrictInvariantOpenHom P.subgroupoid V hV).map_target, Category.assoc,
    ← P.inclusion.map_target, ← Category.assoc]

/-- The identity morphism of the restricted subgroupoid lies over the ambient identity
morphism. -/
private theorem invariantOpen_identity_comp :
    (restrictInvariantOpen P.subgroupoid V hV).identity ≫ invariantOpenToArrows P V hV =
      invariantOpenToObjects P V hV ≫ H.identity := by
  rw [invariantOpenToObjects, invariantOpenToArrows, ← Category.assoc,
    ← (restrictInvariantOpenHom P.subgroupoid V hV).map_identity, Category.assoc,
    ← P.inclusion.map_identity, ← Category.assoc]

/-- The morphism to the ambient arrow scheme takes composites of composable generalized arrows of
the restricted subgroupoid to composites. -/
private theorem invariantOpen_compose_comp {T : Over S}
    (f g : T ⟶ (restrictInvariantOpen P.subgroupoid V hV).arrows)
    (w : f ≫ (restrictInvariantOpen P.subgroupoid V hV).source =
      g ≫ (restrictInvariantOpen P.subgroupoid V hV).target)
    (w' : (f ≫ invariantOpenToArrows P V hV) ≫ H.source =
      (g ≫ invariantOpenToArrows P V hV) ≫ H.target) :
    (restrictInvariantOpen P.subgroupoid V hV).compose f g w ≫ invariantOpenToArrows P V hV =
      H.compose (f ≫ invariantOpenToArrows P V hV) (g ≫ invariantOpenToArrows P V hV) w' := by
  have hk : ∀ k : T ⟶ (restrictInvariantOpen P.subgroupoid V hV).arrows,
      k ≫ invariantOpenToArrows P V hV =
        (k ≫ (restrictInvariantOpenHom P.subgroupoid V hV).mapArrows) ≫ P.inclusion.mapArrows :=
    fun k => (Category.assoc _ _ _).symm
  have hfa := hk f
  have hga := hk g
  have hw₁ : (f ≫ (restrictInvariantOpenHom P.subgroupoid V hV).mapArrows) ≫
      P.subgroupoid.source =
        (g ≫ (restrictInvariantOpenHom P.subgroupoid V hV).mapArrows) ≫
          P.subgroupoid.target := by
    rw [Category.assoc, Category.assoc,
      (restrictInvariantOpenHom P.subgroupoid V hV).map_source,
      (restrictInvariantOpenHom P.subgroupoid V hV).map_target, ← Category.assoc,
      ← Category.assoc, w]
  have hw₂ : ((f ≫ (restrictInvariantOpenHom P.subgroupoid V hV).mapArrows) ≫
      P.inclusion.mapArrows) ≫ H.source =
        ((g ≫ (restrictInvariantOpenHom P.subgroupoid V hV).mapArrows) ≫
          P.inclusion.mapArrows) ≫ H.target := by
    rw [← hfa, ← hga]
    exact w'
  calc (restrictInvariantOpen P.subgroupoid V hV).compose f g w ≫ invariantOpenToArrows P V hV
      = ((restrictInvariantOpen P.subgroupoid V hV).compose f g w ≫
          (restrictInvariantOpenHom P.subgroupoid V hV).mapArrows) ≫ P.inclusion.mapArrows :=
        hk _
    _ = P.subgroupoid.compose (f ≫ (restrictInvariantOpenHom P.subgroupoid V hV).mapArrows)
          (g ≫ (restrictInvariantOpenHom P.subgroupoid V hV).mapArrows) hw₁ ≫
          P.inclusion.mapArrows := by
        rw [(restrictInvariantOpenHom P.subgroupoid V hV).map_comp T f g w hw₁]
    _ = H.compose ((f ≫ (restrictInvariantOpenHom P.subgroupoid V hV).mapArrows) ≫
          P.inclusion.mapArrows)
          ((g ≫ (restrictInvariantOpenHom P.subgroupoid V hV).mapArrows) ≫
            P.inclusion.mapArrows) hw₂ :=
        P.inclusion.map_comp T _ _ hw₁ hw₂
    _ = H.compose (f ≫ invariantOpenToArrows P V hV) (g ≫ invariantOpenToArrows P V hV) w' :=
        compose_congr H hfa.symm hga.symm hw₂ w'

/-- The source morphism of the restriction of an open finite subgroupoid to an invariant open is
finite: it is the restriction of a finite morphism to an open of its target, and being finite is
Zariski local on the target. -/
theorem isFinite_invariantOpen_source :
    IsFinite (restrictInvariantOpen P.subgroupoid V hV).source.left := by
  have := isFinite_isZariskiLocalAtTarget.{u}
  have hfin : IsFinite P.subgroupoid.source.left := P.source_finite
  have hrestrict : (invariantSource P.subgroupoid V).left =
      P.subgroupoid.source.left ∣_ V := by
    rw [← cancel_mono V.ι, morphismRestrict_ι]
    exact congrArg Over.Hom.left (invariantSource_ι P.subgroupoid V)
  show IsFinite (invariantSource P.subgroupoid V).left
  rw [hrestrict]
  exact IsZariskiLocalAtTarget.restrict (P := @IsFinite) hfin V

/-- The target morphism of the restriction of an open finite subgroupoid to an invariant open is
finite: the inverse morphism of that restriction is an isomorphism on underlying schemes and
carries its source morphism to its target morphism. -/
theorem isFinite_invariantOpen_target :
    IsFinite (restrictInvariantOpen P.subgroupoid V hV).target.left := by
  have hsrc := isFinite_invariantOpen_source P V hV
  have hiso : IsIso (restrictInvariantOpen P.subgroupoid V hV).inverse.left :=
    groupoidInverse_left_isIso _
  rw [← (restrictInvariantOpen P.subgroupoid V hV).source_inverse]
  show IsFinite ((restrictInvariantOpen P.subgroupoid V hV).inverse.left ≫
    (restrictInvariantOpen P.subgroupoid V hV).source.left)
  infer_instance

/-! ### The inclusion of the restricted subgroupoid into the restricted groupoid -/

variable (R : AlgebraicGeometry.GroupoidScheme.Restriction H (invariantOpenToObjects P V hV))

/-- The map on arrow schemes of the inclusion of the restricted subgroupoid into the restriction
of the ambient groupoid along the invariant open: the generalized point of the arrow scheme of
the restriction with the prescribed source, target and ambient arrow. -/
def invariantOpenMapArrows :
    (restrictInvariantOpen P.subgroupoid V hV).arrows ⟶ R.groupoid.arrows :=
  restrictionLift (invariantOpenToObjects P V hV)
      (restrictInvariantOpen P.subgroupoid V hV).source
      (restrictInvariantOpen P.subgroupoid V hV).target (invariantOpenToArrows P V hV)
      (invariantOpen_source_comp P V hV) (invariantOpen_target_comp P V hV) ≫
    eqToHom R.arrows_eq.symm

/-- The source of `Stacks.Groupoids.GroupoidScheme.invariantOpenMapArrows`. -/
theorem invariantOpenMapArrows_source :
    invariantOpenMapArrows P V hV R ≫ R.groupoid.source =
      (restrictInvariantOpen P.subgroupoid V hV).source ≫ eqToHom R.objects_eq.symm := by
  rw [invariantOpenMapArrows, R.source_eq]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc, restrictionLift_source]

/-- The target of `Stacks.Groupoids.GroupoidScheme.invariantOpenMapArrows`. -/
theorem invariantOpenMapArrows_target :
    invariantOpenMapArrows P V hV R ≫ R.groupoid.target =
      (restrictInvariantOpen P.subgroupoid V hV).target ≫ eqToHom R.objects_eq.symm := by
  rw [invariantOpenMapArrows, R.target_eq]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc, restrictionLift_target]

/-- The underlying ambient arrow of `Stacks.Groupoids.GroupoidScheme.invariantOpenMapArrows`. -/
theorem invariantOpenMapArrows_arrow :
    invariantOpenMapArrows P V hV R ≫ R.hom.mapArrows = invariantOpenToArrows P V hV := by
  rw [invariantOpenMapArrows, R.mapArrows_eq]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact restrictionLift_arrow _ _ _ _ _ _

/-- `Stacks.Groupoids.GroupoidScheme.invariantOpenMapArrows` is an open immersion: composed with
the morphism to the ambient arrow scheme it is the open immersion
`Stacks.Groupoids.GroupoidScheme.invariantOpenToArrows`, and that morphism is itself an open
immersion because the invariant open is one. -/
theorem isOpenImmersion_invariantOpenMapArrows :
    IsOpenImmersion (invariantOpenMapArrows P V hV R).left := by
  have hmap := isOpenImmersion_restriction_mapArrows (invariantOpenToObjects P V hV) R
  have hcomp : IsOpenImmersion
      ((invariantOpenMapArrows P V hV R).left ≫ R.hom.mapArrows.left) := by
    rw [← Over.comp_left, invariantOpenMapArrows_arrow]
    infer_instance
  exact IsOpenImmersion.of_comp _ R.hom.mapArrows.left

/-- The identity axiom for the inclusion of the restricted subgroupoid. -/
theorem invariantOpen_map_identity :
    eqToHom R.objects_eq.symm ≫ R.groupoid.identity =
      (restrictInvariantOpen P.subgroupoid V hV).identity ≫ invariantOpenMapArrows P V hV R := by
  refine restriction_hom_ext' (invariantOpenToObjects P V hV) R _ _ ?_ ?_ ?_
  · rw [Category.assoc, R.groupoid.source_identity, Category.comp_id, Category.assoc,
      invariantOpenMapArrows_source, ← Category.assoc,
      (restrictInvariantOpen P.subgroupoid V hV).source_identity, Category.id_comp]
  · rw [Category.assoc, R.groupoid.target_identity, Category.comp_id, Category.assoc,
      invariantOpenMapArrows_target, ← Category.assoc,
      (restrictInvariantOpen P.subgroupoid V hV).target_identity, Category.id_comp]
  · have hL : (eqToHom R.objects_eq.symm ≫ R.groupoid.identity) ≫ R.hom.mapArrows =
        invariantOpenToObjects P V hV ≫ H.identity := by
      rw [Category.assoc, ← R.hom.map_identity, R.mapObjects_eq]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    have hR : ((restrictInvariantOpen P.subgroupoid V hV).identity ≫
        invariantOpenMapArrows P V hV R) ≫ R.hom.mapArrows =
        invariantOpenToObjects P V hV ≫ H.identity := by
      rw [Category.assoc, invariantOpenMapArrows_arrow, invariantOpen_identity_comp]
    rw [hL, hR]

/-- The composition axiom for the inclusion of the restricted subgroupoid. -/
theorem invariantOpen_map_comp (T : Over S)
    (f g : T ⟶ (restrictInvariantOpen P.subgroupoid V hV).arrows)
    (w : f ≫ (restrictInvariantOpen P.subgroupoid V hV).source =
      g ≫ (restrictInvariantOpen P.subgroupoid V hV).target)
    (w' : (f ≫ invariantOpenMapArrows P V hV R) ≫ R.groupoid.source =
      (g ≫ invariantOpenMapArrows P V hV R) ≫ R.groupoid.target) :
    (restrictInvariantOpen P.subgroupoid V hV).compose f g w ≫
        invariantOpenMapArrows P V hV R =
      R.groupoid.compose (f ≫ invariantOpenMapArrows P V hV R)
        (g ≫ invariantOpenMapArrows P V hV R) w' := by
  have e : ∀ k : T ⟶ (restrictInvariantOpen P.subgroupoid V hV).arrows,
      k ≫ invariantOpenToArrows P V hV = (k ≫ invariantOpenMapArrows P V hV R) ≫ R.hom.mapArrows :=
    fun k => ((Category.assoc _ _ _).trans
      (congrArg (k ≫ ·) (invariantOpenMapArrows_arrow P V hV R))).symm
  have e1 := e f
  have e2 := e g
  have hw₃ : ((f ≫ invariantOpenMapArrows P V hV R) ≫ R.hom.mapArrows) ≫ H.source =
      ((g ≫ invariantOpenMapArrows P V hV R) ≫ R.hom.mapArrows) ≫ H.target := by
    simp only [Category.assoc]
    rw [R.hom.map_source, R.hom.map_target]
    simp only [← Category.assoc]
    rw [w']
  have hw₂ : (f ≫ invariantOpenToArrows P V hV) ≫ H.source =
      (g ≫ invariantOpenToArrows P V hV) ≫ H.target := by
    rw [e1, e2]
    exact hw₃
  refine restriction_hom_ext' (invariantOpenToObjects P V hV) R _ _ ?_ ?_ ?_
  · have hL : ((restrictInvariantOpen P.subgroupoid V hV).compose f g w ≫
        invariantOpenMapArrows P V hV R) ≫ R.groupoid.source =
        g ≫ (restrictInvariantOpen P.subgroupoid V hV).source ≫
          eqToHom R.objects_eq.symm := by
      rw [Category.assoc, invariantOpenMapArrows_source, ← Category.assoc,
        compose_comp_source, Category.assoc]
    have hR : (R.groupoid.compose (f ≫ invariantOpenMapArrows P V hV R)
        (g ≫ invariantOpenMapArrows P V hV R) w') ≫ R.groupoid.source =
        g ≫ (restrictInvariantOpen P.subgroupoid V hV).source ≫
          eqToHom R.objects_eq.symm := by
      rw [compose_comp_source R.groupoid, Category.assoc, invariantOpenMapArrows_source]
    rw [hL, hR]
  · have hL : ((restrictInvariantOpen P.subgroupoid V hV).compose f g w ≫
        invariantOpenMapArrows P V hV R) ≫ R.groupoid.target =
        f ≫ (restrictInvariantOpen P.subgroupoid V hV).target ≫
          eqToHom R.objects_eq.symm := by
      rw [Category.assoc, invariantOpenMapArrows_target, ← Category.assoc,
        compose_comp_target, Category.assoc]
    have hR : (R.groupoid.compose (f ≫ invariantOpenMapArrows P V hV R)
        (g ≫ invariantOpenMapArrows P V hV R) w') ≫ R.groupoid.target =
        f ≫ (restrictInvariantOpen P.subgroupoid V hV).target ≫
          eqToHom R.objects_eq.symm := by
      rw [compose_comp_target R.groupoid, Category.assoc, invariantOpenMapArrows_target]
    rw [hL, hR]
  · have hL : ((restrictInvariantOpen P.subgroupoid V hV).compose f g w ≫
        invariantOpenMapArrows P V hV R) ≫ R.hom.mapArrows =
        H.compose (f ≫ invariantOpenToArrows P V hV) (g ≫ invariantOpenToArrows P V hV)
          hw₂ := by
      rw [Category.assoc, invariantOpenMapArrows_arrow,
        invariantOpen_compose_comp P V hV f g w hw₂]
    have hR : (R.groupoid.compose (f ≫ invariantOpenMapArrows P V hV R)
        (g ≫ invariantOpenMapArrows P V hV R) w') ≫ R.hom.mapArrows =
        H.compose (f ≫ invariantOpenToArrows P V hV) (g ≫ invariantOpenToArrows P V hV)
          hw₂ := by
      rw [R.hom.map_comp T (f ≫ invariantOpenMapArrows P V hV R)
        (g ≫ invariantOpenMapArrows P V hV R) w' hw₃]
      exact compose_congr H e1.symm e2.symm hw₃ hw₂
    rw [hL, hR]

/-- The inclusion of the restricted subgroupoid into the restriction of the ambient groupoid
along the invariant open. -/
def invariantOpenInclusion :
    Hom (restrictInvariantOpen P.subgroupoid V hV) R.groupoid where
  mapObjects := eqToHom R.objects_eq.symm
  mapArrows := invariantOpenMapArrows P V hV R
  map_source := invariantOpenMapArrows_source P V hV R
  map_target := invariantOpenMapArrows_target P V hV R
  map_identity := invariantOpen_map_identity P V hV R
  map_comp := invariantOpen_map_comp P V hV R

/-- **Conditions (a) and (b) of Stacks 04RK for the restricted subgroupoid.**  The restriction of
an open finite subgroupoid to an invariant open of the object scheme is an open finite
subgroupoid of the restriction of the ambient groupoid along that open. -/
def invariantOpenSubgroupoidRestriction : OpenFiniteSubgroupoid R.groupoid where
  subgroupoid := restrictInvariantOpen P.subgroupoid V hV
  objects_eq := R.objects_eq.symm
  inclusion := invariantOpenInclusion P V hV R
  mapObjects_eq := rfl
  arrows_open := isOpenImmersion_invariantOpenMapArrows P V hV R
  source_finite := isFinite_invariantOpen_source P V hV
  target_finite := isFinite_invariantOpen_target P V hV

/-! ### Condition (c): the stabilizer of a point of the invariant open -/

/-- **The last paragraph of the proof of Stacks 04RZ.**  Let `P` be a strong splitting of a
groupoid scheme `R` over a point `u` of its object scheme, let `V` be a `P`-invariant open of the
object scheme and let `R|_V` be the restriction of `R` along `V`.  Then the restriction of `P` to
`V` is a strong splitting of `R|_V` over every point of `V` lying over `u`.

Conditions (a) and (b) of **Stacks 04RK** are
`Stacks.Groupoids.GroupoidScheme.invariantOpenSubgroupoidRestriction`.  For condition (c), an
arrow of `R|_V` whose source and target are the given point has an underlying arrow of `R` whose
source and target are `u`, hence lies in `P`; its source lies in `V` because it agrees with the
image of the given point, so the arrow already lies in the restriction of `P` to `V`. -/
theorem isStronglySplitAt_restrictInvariantOpen {u : H.objects.left} (P : StrongSplitting H u)
    (V : P.subgroupoid.objects.left.Opens) (hV : IsInvariantOpen P.subgroupoid V)
    (R : AlgebraicGeometry.GroupoidScheme.Restriction H
      (invariantOpenToObjects P.toOpenFiniteSubgroupoid V hV))
    (w : R.groupoid.objects.left) (hw : R.hom.mapObjects.left.base w = u) :
    IsStronglySplitAt R.groupoid w := by
  have hmapArrows := isOpenImmersion_restriction_mapArrows
    (invariantOpenToObjects P.toOpenFiniteSubgroupoid V hV) R
  have hisoObjects : IsIso P.inclusion.mapObjects.left :=
    isIso_openFiniteSubgroupoid_mapObjects P.toOpenFiniteSubgroupoid
  refine ⟨{ invariantOpenSubgroupoidRestriction P.toOpenFiniteSubgroupoid V hV R with
    contains_stabilizer := ?_ }⟩
  intro r hrs hrt
  have hsrc : H.source.left.base (R.hom.mapArrows.left.base r) = u := by
    have h := congrArg (fun k : R.groupoid.arrows.left ⟶ H.objects.left => k.base r)
      R.hom.map_source_left
    simp only [Scheme.Hom.comp_apply] at h
    rw [h, hrs, hw]
  have htgt : H.target.left.base (R.hom.mapArrows.left.base r) = u := by
    have h := congrArg (fun k : R.groupoid.arrows.left ⟶ H.objects.left => k.base r)
      R.hom.map_target_left
    simp only [Scheme.Hom.comp_apply] at h
    rw [h, hrt, hw]
  obtain ⟨p, hp⟩ := P.contains_stabilizer (R.hom.mapArrows.left.base r) hsrc htgt
  -- the image of `w` in the object scheme of the subgroupoid
  have hwV : (restrictInvariantOpenHom P.subgroupoid V hV).mapObjects.left.base
      ((eqToHom R.objects_eq).left.base w) ∈ V := by
    have hmem : (restrictInvariantOpenHom P.subgroupoid V hV).mapObjects.left.base
        ((eqToHom R.objects_eq).left.base w) ∈
          (restrictInvariantOpenHom P.subgroupoid V hV).mapObjects.left.opensRange :=
      Scheme.Hom.mem_opensRange.mpr ⟨_, rfl⟩
    rwa [opensRange_restrictInvariantOpenHom_mapObjects P.subgroupoid V hV] at hmem
  have hobj : P.inclusion.mapObjects.left.base
      ((restrictInvariantOpenHom P.subgroupoid V hV).mapObjects.left.base
        ((eqToHom R.objects_eq).left.base w)) = u := by
    have hmo : R.hom.mapObjects = eqToHom R.objects_eq ≫
        ((restrictInvariantOpenHom P.subgroupoid V hV).mapObjects ≫
          P.inclusion.mapObjects) := R.mapObjects_eq
    have h := congrArg (fun k : R.groupoid.objects ⟶ H.objects => k.left.base w) hmo
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at h
    exact h.symm.trans hw
  have hpsrc : P.subgroupoid.source.left.base p =
      (restrictInvariantOpenHom P.subgroupoid V hV).mapObjects.left.base
        ((eqToHom R.objects_eq).left.base w) := by
    have h := congrArg (fun k : P.subgroupoid.arrows.left ⟶ H.objects.left => k.base p)
      P.inclusion.map_source_left
    simp only [Scheme.Hom.comp_apply] at h
    refine P.inclusion.mapObjects.left.isOpenEmbedding.injective ?_
    rw [← h, hp, hsrc, hobj]
  have hpmem : p ∈ invariantArrows P.subgroupoid V := by
    rw [mem_invariantArrows_iff, hpsrc]
    exact hwV
  obtain ⟨q, hq⟩ : ∃ q, (restrictInvariantOpenHom P.subgroupoid V hV).mapArrows.left.base q = p :=
    Scheme.Hom.mem_opensRange.mp (by
      rw [opensRange_restrictInvariantOpenHom_mapArrows P.subgroupoid V hV]
      exact hpmem)
  refine ⟨q, R.hom.mapArrows.left.isOpenEmbedding.injective ?_⟩
  have hcomp := congrArg
    (fun k : (restrictInvariantOpen P.subgroupoid V hV).arrows ⟶ H.arrows => k.left.base q)
    (invariantOpenMapArrows_arrow P.toOpenFiniteSubgroupoid V hV R)
  simp only [Over.comp_left, Scheme.Hom.comp_apply] at hcomp
  show R.hom.mapArrows.left.base
    ((invariantOpenInclusion P.toOpenFiniteSubgroupoid V hV R).mapArrows.left.base q) = _
  show R.hom.mapArrows.left.base
    ((invariantOpenMapArrows P.toOpenFiniteSubgroupoid V hV R).left.base q) = _
  rw [hcomp, invariantOpenToArrows]
  simp only [Over.comp_left, Scheme.Hom.comp_apply]
  rw [hq, hp]

/-! ### Shrinking an open finite subgroupoid to an invariant affine open

The construction shared by the proofs of Stacks 04RZ and Stacks 04S0: the first three paragraphs
of the proof of Stacks 04RZ, which use nothing about the splitting beyond conditions (a) and (b)
of Stacks 04RK and so apply to a strong splitting and to a quasi-splitting alike. -/

/-- The restriction to an invariant open of the object scheme of an open finite subgroupoid of a
restriction along an étale morphism stays étale over the base, and keeps the point and its residue
field. -/
private theorem etale_residueFieldMap_invariantOpenToObjects {G : GroupoidScheme S}
    {U' : Over S} {g : U' ⟶ G.objects} [Etale g.left]
    (R' : AlgebraicGeometry.GroupoidScheme.Restriction G g)
    (P : OpenFiniteSubgroupoid R'.groupoid) (V : P.subgroupoid.objects.left.Opens)
    (hV : IsInvariantOpen P.subgroupoid V)
    (w : (restrictInvariantOpen P.subgroupoid V hV).objects.left) {u : G.objects.left}
    (x : R'.groupoid.objects.left) (hw : (invariantOpenToObjects P V hV).left.base w = x)
    (hx : R'.hom.mapObjects.left.base x = u)
    (hiso : IsIso (R'.hom.mapObjects.left.residueFieldMap x)) :
    Etale (invariantOpenToObjects P V hV ≫ R'.hom.mapObjects).left ∧
      (invariantOpenToObjects P V hV ≫ R'.hom.mapObjects).left.base w = u ∧
      IsIso ((invariantOpenToObjects P V hV ≫ R'.hom.mapObjects).left.residueFieldMap w) := by
  have hmoEt : Etale R'.hom.mapObjects.left := by
    rw [restriction_mapObjects_left]
    infer_instance
  refine ⟨?_, ?_, ?_⟩
  · rw [Over.comp_left]
    infer_instance
  · rw [Over.comp_left, Scheme.Hom.comp_apply, hw]
    exact hx
  · rw [Over.comp_left, Scheme.residueFieldMap_comp]
    have hw' : (invariantOpenToObjects P V hV).left w = x := hw
    have h1 : IsIso (R'.hom.mapObjects.left.residueFieldMap
        ((invariantOpenToObjects P V hV).left w)) := by
      rw [hw']
      exact hiso
    exact IsIso.comp_isIso' h1 inferInstance

/-- **The construction common to the proofs of Stacks 04RZ and Stacks 04S0.**  Let `R` be a
groupoid scheme with affine object scheme whose source and target are flat and locally of finite
presentation, let `g : U' ⟶ U` be a separated étale morphism to its object scheme, let `R'`
realize the restriction `R|_{U'}`, and let `P` be an open finite subgroupoid of `R'`.  Then every
point of `U'` is the image of a point of a `P`-invariant affine open of the object scheme of `P`.

By Stacks 04MV the source and target of `R'` are again flat and locally of finite presentation,
hence so are their restrictions to the arrow scheme of `P`; those are finite by the definition of
an open finite subgroupoid, so they are finite locally free by Stacks 02KB.  The orbit of the
point under `P` is therefore a finite set of points, and since `U` is affine and the morphism
from the object scheme of `P` to `U` is separated and locally quasi-finite, Stacks 07S0 puts that
finite set inside a single affine open.  Stacks 03JE then produces the invariant affine open. -/
theorem exists_isAffineOpen_isInvariantOpen_of_openFiniteSubgroupoid
    {G : GroupoidScheme S} [IsAffine G.objects.left]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left]
    [Flat G.target.left] [LocallyOfFinitePresentation G.target.left]
    {U' : Over S} {g : U' ⟶ G.objects} [IsSeparated g.left] [Etale g.left]
    (R' : AlgebraicGeometry.GroupoidScheme.Restriction G g)
    (P : OpenFiniteSubgroupoid R'.groupoid) (x : R'.groupoid.objects.left) :
    ∃ (V : P.subgroupoid.objects.left.Opens) (hV : IsInvariantOpen P.subgroupoid V)
      (w : (restrictInvariantOpen P.subgroupoid V hV).objects.left),
      IsAffineOpen V ∧ (invariantOpenToObjects P V hV).left.base w = x := by
  -- the source and target of `R'` are flat and locally of finite presentation, by Stacks 04MV
  have hprojFlat : Flat ((Over.forget S).map g) := by
    show Flat g.left
    infer_instance
  have hprojLfp : LocallyOfFinitePresentation ((Over.forget S).map g) := by
    show LocallyOfFinitePresentation g.left
    infer_instance
  have hsq := (IsPullback.of_hasPullback g G.target).map (Over.forget S)
  have hsndFlat : Flat (pullback.snd g G.target).left :=
    MorphismProperty.of_isPullback hsq hprojFlat
  have hsndLfp : LocallyOfFinitePresentation (pullback.snd g G.target).left :=
    MorphismProperty.of_isPullback hsq hprojLfp
  have hcompFlat : Flat (pullback.snd g G.target ≫ G.source).left := by
    rw [Over.comp_left]
    infer_instance
  have hcompLfp :
      LocallyOfFinitePresentation (pullback.snd g G.target ≫ G.source).left := by
    rw [Over.comp_left]
    infer_instance
  have hFlatSource : Flat R'.groupoid.source.left :=
    AlgebraicGeometry.restriction_source_mem G g R' @Flat hcompFlat
  have hLfpSource : LocallyOfFinitePresentation R'.groupoid.source.left :=
    AlgebraicGeometry.restriction_source_mem G g R' @LocallyOfFinitePresentation hcompLfp
  have hFlatTarget : Flat R'.groupoid.target.left :=
    AlgebraicGeometry.restriction_target_mem G g R' @Flat hcompFlat
  have hLfpTarget : LocallyOfFinitePresentation R'.groupoid.target.left :=
    AlgebraicGeometry.restriction_target_mem G g R' @LocallyOfFinitePresentation hcompLfp
  -- hence the source and target of the subgroupoid are finite locally free, by Stacks 02KB
  have hQsource := isFiniteLocallyFree_openFiniteSubgroupoid_source P
  have hQtarget := isFiniteLocallyFree_openFiniteSubgroupoid_target P
  -- the morphism from the object scheme of the subgroupoid to `U` is separated étale
  have hmoSep : IsSeparated R'.hom.mapObjects.left := by
    rw [restriction_mapObjects_left]
    infer_instance
  have hmoEt : Etale R'.hom.mapObjects.left := by
    rw [restriction_mapObjects_left]
    infer_instance
  have hisoIncl : IsIso P.inclusion.mapObjects.left :=
    isIso_openFiniteSubgroupoid_mapObjects P
  have hqSep : IsSeparated (P.inclusion.mapObjects ≫ R'.hom.mapObjects).left := by
    rw [Over.comp_left]
    infer_instance
  have hqEt : Etale (P.inclusion.mapObjects ≫ R'.hom.mapObjects).left := by
    rw [Over.comp_left]
    infer_instance
  obtain ⟨hqLft, hqLqf⟩ := locallyQuasiFinite_of_etale
    (P.inclusion.mapObjects ≫ R'.hom.mapObjects).left
  -- the given point read on the object scheme of the subgroupoid
  have hpointMap : P.inclusion.mapObjects.left.base
      ((eqToHom P.objects_eq.symm).left.base x) = x := by
    rw [P.mapObjects_eq]
    exact over_eqToHom_apply_symm P.objects_eq x
  -- its orbit under the subgroupoid is finite, and lies in an affine open by Stacks 07S0
  have hQfin : IsFinite P.subgroupoid.source.left := P.source_finite
  have horbit : (P.subgroupoid.target.left.base ''
      (P.subgroupoid.source.left.base ⁻¹'
        {(eqToHom P.objects_eq.symm).left.base x})).Finite :=
    (P.subgroupoid.source.left.finite_preimage_singleton _).image _
  obtain ⟨W, hWaff, hWsub⟩ := exists_isAffineOpen_containing_finite_of_locallyQuasiFinite
    (P.inclusion.mapObjects ≫ R'.hom.mapObjects).left horbit
  -- Stacks 03JE produces the invariant affine open
  obtain ⟨V, hVinv, hVaff, hVu⟩ :=
    AlgebraicGeometry.GroupoidScheme.exists_isInvariantOpen_isAffineOpen_mem
      P.subgroupoid ((eqToHom P.objects_eq.symm).left.base x) ⟨W, hWaff, hWsub⟩
  obtain ⟨w, hw⟩ : ∃ w,
      (restrictInvariantOpenHom P.subgroupoid V hVinv).mapObjects.left.base w =
        (eqToHom P.objects_eq.symm).left.base x :=
    Scheme.Hom.mem_opensRange.mp (by
      rw [opensRange_restrictInvariantOpenHom_mapObjects P.subgroupoid V hVinv]
      exact hVu)
  refine ⟨V, hVinv, w, hVaff, ?_⟩
  have h := congrArg
    (fun k : (restrictInvariantOpen P.subgroupoid V hVinv).objects ⟶ R'.groupoid.objects =>
      k.left.base w)
    (show invariantOpenToObjects P V hVinv =
      (restrictInvariantOpenHom P.subgroupoid V hVinv).mapObjects ≫
        P.inclusion.mapObjects from rfl)
  simp only [Over.comp_left, Scheme.Hom.comp_apply] at h
  rw [h, hw, hpointMap]

/-! ### Stacks 04RZ -/

/-- **The output of Stacks 04RX**, in the form in which Stacks 04RZ consumes it: a scheme `U'`
with a separated étale morphism `g : U' ⟶ U` to the object scheme of a groupoid scheme `R`, the
restriction `R' = R|_{U'}`, a point `u'` of `U'` above the given point `u` of `U` with
`κ(u) = κ(u')`, and a strong splitting of `R'` over `u'`.

The point and the splitting are recorded on the object scheme of the restriction, which the field
`AlgebraicGeometry.GroupoidScheme.Restriction.objects_eq` says is `U'` itself; the morphism
`R'.objects ⟶ U` through which the point lies over `u` is then
`AlgebraicGeometry.GroupoidScheme.Restriction.hom`, so no transport along that equality appears
in the statement. -/
structure EtaleStrongSplitting (G : GroupoidScheme S) (u : G.objects.left) where
  /-- The scheme `U'`. -/
  objects : Over S
  /-- The morphism `g : U' ⟶ U`. -/
  projection : objects ⟶ G.objects
  /-- `g` is separated. -/
  [projection_isSeparated : IsSeparated projection.left]
  /-- `g` is étale. -/
  [projection_etale : Etale projection.left]
  /-- The restriction `R' = R|_{U'}`. -/
  restriction : AlgebraicGeometry.GroupoidScheme.Restriction G projection
  /-- The point `u'` of `U'`, read on the object scheme of `R'`. -/
  point : restriction.groupoid.objects.left
  /-- The point `u'` lies over `u`. -/
  point_over : restriction.hom.mapObjects.left.base point = u
  /-- The residue field extension `κ(u) ⊆ κ(u')` is trivial. -/
  residueFieldMap_isIso : IsIso (restriction.hom.mapObjects.left.residueFieldMap point)
  /-- A strong splitting of `R'` over `u'`. -/
  splitting : StrongSplitting restriction.groupoid point

attribute [instance] EtaleStrongSplitting.projection_isSeparated
  EtaleStrongSplitting.projection_etale

/-- **The shrinking step in the proof of Stacks 04RZ.**  Let `R` be a groupoid scheme with affine
object scheme whose source and target are flat and locally of finite presentation, and let the
output of Stacks 04RX at `u` be given — a separated étale `g : U' ⟶ U`, the restriction
`R' = R|_{U'}`, a point `u'` of `U'` over `u` with `κ(u) = κ(u')` and a strong splitting of `R'`
over `u'`.  Then there is an affine open `U'' ⊆ U'` containing `u'` such that the restriction of
`R'` to `U''` is strongly split over `u'`.

Nothing about the splitting beyond conditions (a) and (b) of Stacks 04RK enters the production
of `U''`, which is therefore the shared
`Stacks.Groupoids.GroupoidScheme.exists_isAffineOpen_isInvariantOpen_of_openFiniteSubgroupoid`;
condition (c) at `u'` for the restricted splitting is
`Stacks.Groupoids.GroupoidScheme.isStronglySplitAt_restrictInvariantOpen`.  Because `U''` is an
open of `U'`, the morphism `U'' ⟶ U'` is an open immersion, and the splitting is obtained for
every groupoid scheme realizing the restriction of `R'` to `U''`. -/
theorem exists_isAffine_isStronglySplitAt_of_etaleStrongSplitting
    {G : GroupoidScheme S} [IsAffine G.objects.left]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left]
    [Flat G.target.left] [LocallyOfFinitePresentation G.target.left]
    {u : G.objects.left} (E : EtaleStrongSplitting G u) :
    ∃ (U'' : Over S) (j : U'' ⟶ E.restriction.groupoid.objects) (u'' : U''.left),
      IsAffine U''.left ∧ IsOpenImmersion j.left ∧
      Etale (j ≫ E.restriction.hom.mapObjects).left ∧
      (j ≫ E.restriction.hom.mapObjects).left.base u'' = u ∧
      IsIso ((j ≫ E.restriction.hom.mapObjects).left.residueFieldMap u'') ∧
      ∀ R'' : AlgebraicGeometry.GroupoidScheme.Restriction E.restriction.groupoid j,
        IsStronglySplitAt R''.groupoid ((eqToHom R''.objects_eq.symm).left.base u'') := by
  -- the shrinking of `U'`, which uses only conditions (a) and (b) of the splitting
  obtain ⟨V, hVinv, w, hVaff, hjw⟩ :=
    exists_isAffineOpen_isInvariantOpen_of_openFiniteSubgroupoid E.restriction
      E.splitting.toOpenFiniteSubgroupoid E.point
  obtain ⟨hEt, hover, hiso⟩ := etale_residueFieldMap_invariantOpenToObjects E.restriction
    E.splitting.toOpenFiniteSubgroupoid V hVinv w E.point hjw E.point_over E.residueFieldMap_isIso
  refine ⟨(restrictInvariantOpen E.splitting.subgroupoid V hVinv).objects,
    invariantOpenToObjects E.splitting.toOpenFiniteSubgroupoid V hVinv, w, hVaff,
    isOpenImmersion_invariantOpenToObjects E.splitting.toOpenFiniteSubgroupoid V hVinv, hEt,
    hover, hiso, ?_⟩
  · intro R''
    refine isStronglySplitAt_restrictInvariantOpen E.splitting V hVinv R'' _ ?_
    have hmo : R''.hom.mapObjects = eqToHom R''.objects_eq ≫
      invariantOpenToObjects E.splitting.toOpenFiniteSubgroupoid V hVinv := R''.mapObjects_eq
    have h := congrArg
      (fun k : R''.groupoid.objects ⟶ E.restriction.groupoid.objects =>
        k.left.base ((eqToHom R''.objects_eq.symm).left.base w)) hmo
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at h
    rw [h, over_eqToHom_apply_symm R''.objects_eq w, hjw]

/-- **The output of Stacks 04RX as `EtaleStrongSplitting`.**  In the strong splitting situation
of Stacks 04RL, with the source flat and locally of finite presentation, there are a scheme `U'`
over `S`, a separated étale `g : U' ⟶ U`, the restriction `R' = R|_{U'}`, a point `u'` of `U'`
over `u` with `κ(u) = κ(u')`, and a strong splitting of `R'` over `u'`.

The scheme, the morphism, the point and the splitting are the de-realization, provided by
`Stacks.Groupoids.GroupoidScheme.exists_etale_separated_scheme_isStronglySplitAt`, of the
algebraic space and the splitting of the restricted realization which Stacks 04RX produces; `R'`
is `AlgebraicGeometry.GroupoidScheme.restrict`, for which the splitting is available because it
is available for every groupoid scheme realizing the restriction. -/
theorem nonempty_etaleStrongSplitting_scheme
    (D : AlgebraicGeometry.Space.StrongSplittingSituation.{u})
    (C : AlgebraicGeometry.BigFppfSite.{u}) (hS : C.Contains D.S)
    (hU : C.Contains D.groupoid.objects.left) (hR : C.Contains D.groupoid.arrows.left)
    (hP : C.Contains (pullback D.groupoid.source D.groupoid.target).left)
    (hK : C.Contains (Spec (D.groupoid.objects.left.residueField D.u)))
    (hflat : AlgebraicGeometry.Flat D.groupoid.source.left)
    (hfp : AlgebraicGeometry.LocallyOfFinitePresentation D.groupoid.source.left) :
    Nonempty (EtaleStrongSplitting D.groupoid D.u) := by
  obtain ⟨Y, q, y, hsep, het, hyu, hyiso, hsplit⟩ :=
    exists_etale_separated_scheme_isStronglySplitAt D C hS hU hR hP hK hflat hfp
  obtain ⟨hpoint, hpiso⟩ := isIso_residueFieldMap_restriction_mapObjects D.groupoid q D.u
    (AlgebraicGeometry.GroupoidScheme.restrict D.groupoid q) y hyu hyiso
  obtain ⟨Q⟩ := hsplit (AlgebraicGeometry.GroupoidScheme.restrict D.groupoid q)
  exact ⟨{ objects := Y
           projection := q
           projection_isSeparated := hsep
           projection_etale := het
           restriction := AlgebraicGeometry.GroupoidScheme.restrict D.groupoid q
           point := (eqToHom (AlgebraicGeometry.GroupoidScheme.restrict
             D.groupoid q).objects_eq.symm).left.base y
           point_over := hpoint
           residueFieldMap_isIso := hpiso
           splitting := Q }⟩

/-- **Stacks Project, Tag 04RZ.**

In the strong splitting situation of Stacks 04RL, with `s` and `t` in addition flat and locally
of finite presentation and with `U` affine, there are an affine scheme `U''`, an étale morphism
`U'' ⟶ U` and a point `u''` of `U''` over `u` with `κ(u) = κ(u'')`, such that the restriction of
`R` to `U''` is strongly split over `u''`.

The étale neighbourhood `U'` of Stacks 04RX is shrunk to an affine one: `U''` is an invariant
affine open of the object scheme of the strong splitting of `R' = R|_{U'}`, so `U'' ⟶ U'` is an
open immersion and the restriction of that splitting to `U''` is a strong splitting of
`R'|_{U''}` over `u''`.  The restriction is taken in two steps, as the restriction of `R'` to
`U''`; its identification with the restriction of `R` along the composite `U'' ⟶ U' ⟶ U` is
Stacks 04MW. -/
@[stacks 04RZ "in Situation 04RL with s, t flat and locally of finite presentation and U affine:
an affine scheme U'', an étale U'' ⟶ U and a point u'' over u with κ(u) = κ(u''), such that
R|_{U''} is strongly split over u''. R|_{U''} is covered in its two-step reading, as the
restriction to U'' of R' = R|_{U'} for the étale neighbourhood U' of Stacks 04RX, rather than as
the restriction of R along the composite U'' ⟶ U' ⟶ U; the identification of the two is
Stacks 04MW, which this library has as the comparison diagram `doubleRestrictionDiagram` and not
as an identification of realizations. The conclusion is stronger than the tag in two respects:
U'' ⟶ U' is an open immersion, not merely étale, and the strong splitting is produced for EVERY
groupoid scheme realizing that restriction. Beyond Situation 04RL the hypotheses are that the big
fppf site contains the base, object, arrow and composable-pair schemes and Spec κ(u), this
library's standing ambient requirement"]
theorem exists_isAffine_isStronglySplitAt
    (D : AlgebraicGeometry.Space.StrongSplittingSituation.{u})
    (C : AlgebraicGeometry.BigFppfSite.{u}) (hS : C.Contains D.S)
    (hU : C.Contains D.groupoid.objects.left) (hR : C.Contains D.groupoid.arrows.left)
    (hP : C.Contains (pullback D.groupoid.source D.groupoid.target).left)
    (hK : C.Contains (Spec (D.groupoid.objects.left.residueField D.u)))
    [IsAffine D.groupoid.objects.left]
    [Flat D.groupoid.source.left] [LocallyOfFinitePresentation D.groupoid.source.left]
    [Flat D.groupoid.target.left] [LocallyOfFinitePresentation D.groupoid.target.left] :
    ∃ (U' : Over D.S) (g : U' ⟶ D.groupoid.objects)
      (R' : AlgebraicGeometry.GroupoidScheme.Restriction D.groupoid g)
      (U'' : Over D.S) (j : U'' ⟶ R'.groupoid.objects) (u'' : U''.left),
      IsAffine U''.left ∧ IsOpenImmersion j.left ∧
      Etale (j ≫ R'.hom.mapObjects).left ∧
      (j ≫ R'.hom.mapObjects).left.base u'' = D.u ∧
      IsIso ((j ≫ R'.hom.mapObjects).left.residueFieldMap u'') ∧
      ∀ R'' : AlgebraicGeometry.GroupoidScheme.Restriction R'.groupoid j,
        IsStronglySplitAt R''.groupoid ((eqToHom R''.objects_eq.symm).left.base u'') := by
  obtain ⟨E⟩ := nonempty_etaleStrongSplitting_scheme D C hS hU hR hP hK inferInstance inferInstance
  obtain ⟨U'', j, u'', hU''⟩ := exists_isAffine_isStronglySplitAt_of_etaleStrongSplitting E
  exact ⟨E.objects, E.projection, E.restriction, U'', j, u'', hU''⟩

/-! ### Stacks 04S0 -/

/-- **The output of Stacks 04RY**, in the form in which Stacks 04S0 consumes it: a scheme `U'`
with a separated étale morphism `g : U' ⟶ U` to the object scheme of a groupoid scheme `R`, the
restriction `R' = R|_{U'}`, a point `u'` of `U'` above the given point `u` of `U` with
`κ(u) = κ(u')`, and a *quasi*-splitting of `R'` over `u'`.

This is `Stacks.Groupoids.GroupoidScheme.EtaleStrongSplitting` with part (1) of Stacks 04RK
replaced by part (3): the subgroupoid is required to contain only the identity arrow at `u'`,
not the whole stabilizer of `u'`.  As there, the point and the splitting are recorded on the
object scheme of the restriction, which the field
`AlgebraicGeometry.GroupoidScheme.Restriction.objects_eq` says is `U'` itself. -/
structure EtaleQuasiSplitting (G : GroupoidScheme S) (u : G.objects.left) where
  /-- The scheme `U'`. -/
  objects : Over S
  /-- The morphism `g : U' ⟶ U`. -/
  projection : objects ⟶ G.objects
  /-- `g` is separated. -/
  [projection_isSeparated : IsSeparated projection.left]
  /-- `g` is étale. -/
  [projection_etale : Etale projection.left]
  /-- The restriction `R' = R|_{U'}`. -/
  restriction : AlgebraicGeometry.GroupoidScheme.Restriction G projection
  /-- The point `u'` of `U'`, read on the object scheme of `R'`. -/
  point : restriction.groupoid.objects.left
  /-- The point `u'` lies over `u`. -/
  point_over : restriction.hom.mapObjects.left.base point = u
  /-- The residue field extension `κ(u) ⊆ κ(u')` is trivial. -/
  residueFieldMap_isIso : IsIso (restriction.hom.mapObjects.left.residueFieldMap point)
  /-- A quasi-splitting of `R'` over `u'`. -/
  splitting : QuasiSplitting restriction.groupoid point

attribute [instance] EtaleQuasiSplitting.projection_isSeparated
  EtaleQuasiSplitting.projection_etale

/-- **The shrinking step of Stacks 04S0**: the last paragraph of the source's proof, run on the
output of Stacks 04RY packaged as
`Stacks.Groupoids.GroupoidScheme.EtaleQuasiSplitting`.

Given a groupoid scheme with `U` affine and with `s` and `t` flat and locally of finite
presentation, and given a separated étale `g : U' ⟶ U`, the restriction `R' = R|_{U'}`, a point
`u'` of `U'` over `u` with `κ(u) = κ(u')` and a quasi-splitting of `R'` over `u'`, there are an
affine open `U'' ⊆ U'` containing `u'` and a point `u''` of `U''` over `u` with
`κ(u) = κ(u'')` such that `U'' ⟶ U` is étale and `R|_{U''}` is quasi-split over `u''`.

The source proves Stacks 04S0 by rerunning the proof of Stacks 04RZ with "strong splitting"
replaced by "quasi-splitting" and the appeal to Stacks 04RX replaced by an appeal to
Stacks 04RY, and that is what happens here.  The first three paragraphs of that proof use
nothing about the splitting beyond conditions (a) and (b) of Stacks 04RK, so they are shared
verbatim as
`Stacks.Groupoids.GroupoidScheme.exists_isAffineOpen_isInvariantOpen_of_openFiniteSubgroupoid`.
Its last paragraph is *cheaper* here than for Stacks 04RZ: condition (c) of part (3) of
Stacks 04RK holds for every open finite subgroupoid at every point, by the footnote to that part
of the tag, so the restriction of the quasi-splitting to the invariant affine open needs no
argument about the stabilizer of `u''` at all.

`R|_{U''}` is read as the tag reads it, as the restriction of `R` along the composite
`U'' ⟶ U' ⟶ U`: the quasi-splitting obtained for a realization of `(R|_{U'})|_{U''}` is
transported along the comparison isomorphism of
`AlgebraicGeometry.GroupoidScheme.isQuasiSplitAt_of_iteratedRestriction'`, and both readings are
asserted.

The standing hypotheses of Situation 04RV — that `s` and `t` are separated and locally of finite
type and that `s` is quasi-finite at `e(u)` — play no part here, because their only role in the
proof of the tag is to supply Stacks 04RY, which this statement takes as given.  Stacks 04S0
itself, with the étale quasi-splitting produced from Stacks 04RY rather than given, is
`Stacks.Groupoids.GroupoidScheme.exists_isAffine_isQuasiSplitAt_of_quasiSplittingSituation`.

In two further respects the conclusion is stronger than the tag: the morphism `U'' ⟶ U'` is an
open immersion, not merely étale, and the quasi-splitting is produced for *every* groupoid
scheme realizing the restriction, not just for one. -/
theorem exists_isAffine_isQuasiSplitAt {G : GroupoidScheme S} [IsAffine G.objects.left]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left]
    [Flat G.target.left] [LocallyOfFinitePresentation G.target.left]
    {u : G.objects.left} (E : EtaleQuasiSplitting G u) :
    ∃ (U'' : Over S) (j : U'' ⟶ E.restriction.groupoid.objects) (u'' : U''.left),
      IsAffine U''.left ∧ IsOpenImmersion j.left ∧
      Etale (j ≫ E.restriction.hom.mapObjects).left ∧
      (j ≫ E.restriction.hom.mapObjects).left.base u'' = u ∧
      IsIso ((j ≫ E.restriction.hom.mapObjects).left.residueFieldMap u'') ∧
      (∀ R'' : AlgebraicGeometry.GroupoidScheme.Restriction E.restriction.groupoid j,
        IsQuasiSplitAt R''.groupoid ((eqToHom R''.objects_eq.symm).left.base u'')) ∧
      ∀ R''' : AlgebraicGeometry.GroupoidScheme.Restriction G
          (j ≫ E.restriction.hom.mapObjects),
        IsQuasiSplitAt R'''.groupoid ((eqToHom R'''.objects_eq.symm).left.base u'') := by
  -- the shrinking of `U'`, which uses only conditions (a) and (b) of the splitting
  obtain ⟨V, hVinv, w, hVaff, hjw⟩ :=
    exists_isAffineOpen_isInvariantOpen_of_openFiniteSubgroupoid E.restriction
      E.splitting.toOpenFiniteSubgroupoid E.point
  -- the footnote to part (3) of Stacks 04RK: condition (c) is free
  have hquasi : ∀ R'' : AlgebraicGeometry.GroupoidScheme.Restriction
      E.restriction.groupoid (invariantOpenToObjects E.splitting.toOpenFiniteSubgroupoid V hVinv),
      IsQuasiSplitAt R''.groupoid ((eqToHom R''.objects_eq.symm).left.base w) := fun R'' =>
    ⟨(invariantOpenSubgroupoidRestriction E.splitting.toOpenFiniteSubgroupoid V hVinv
      R'').toQuasiSplitting _⟩
  obtain ⟨hEt, hover, hiso⟩ := etale_residueFieldMap_invariantOpenToObjects E.restriction
    E.splitting.toOpenFiniteSubgroupoid V hVinv w E.point hjw E.point_over E.residueFieldMap_isIso
  refine ⟨(restrictInvariantOpen E.splitting.subgroupoid V hVinv).objects,
    invariantOpenToObjects E.splitting.toOpenFiniteSubgroupoid V hVinv, w, hVaff,
    isOpenImmersion_invariantOpenToObjects E.splitting.toOpenFiniteSubgroupoid V hVinv, hEt,
    hover, hiso, hquasi, ?_⟩
  · -- the restriction of `R` along the composite, identified with the iterated restriction
    intro R'''
    exact AlgebraicGeometry.GroupoidScheme.isQuasiSplitAt_of_iteratedRestriction'
      E.restriction (AlgebraicGeometry.GroupoidScheme.restrict E.restriction.groupoid
        (invariantOpenToObjects E.splitting.toOpenFiniteSubgroupoid V hVinv)) R''' w
      (hquasi _)

end Stacks.Groupoids.GroupoidScheme

end

end
