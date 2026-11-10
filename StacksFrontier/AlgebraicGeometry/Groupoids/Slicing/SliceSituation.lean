module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Restriction
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid

/-!
# Fibres in a restriction of a groupoid scheme

Fix a groupoid scheme, a morphism `g : U' ⟶ U` to its object scheme, and compatible points of
the two object schemes. This file records the restricted groupoid, the stabilizer and source
fibres at the chosen points, and the canonical base-change description of the source fibre of
the restriction.

## Main definitions

* `AlgebraicGeometry.SliceSituation` is the standing data of the slice situation.
* `AlgebraicGeometry.SliceFiberComparison` records the canonical comparison of source fibres,
  together with its two projection formulas.
* `AlgebraicGeometry.SliceIdentityPoints` records the identity points in the arrow, stabilizer
  and source fibres and their canonical images.

## Main results

* `AlgebraicGeometry.stabilizerArrow_isImmersion` says that the stabilizer is a locally closed
  subscheme of the arrow scheme.
* `AlgebraicGeometry.SliceSituation.sliceFiberComparison` constructs the canonical base-change
  description of the source fibre of the restricted groupoid.
* `AlgebraicGeometry.SliceSituation.sliceIdentityPoints` constructs the compatible identity
  points.

## Implementation notes

The restriction is represented by the chosen iterated fibre product of
`AlgebraicGeometry.GroupoidScheme.Restriction`, so its source fibre is taken using
`AlgebraicGeometry.restrictionSource`. The equality of source fibres asserted by the source is
recorded as a canonical isomorphism whose maps to the original arrow scheme and to the spectrum
of the residue field are specified; this avoids identifying two separately chosen fibre
products definitionally.

## References

* [Stacks Project, Tag 04MY](https://stacks.math.columbia.edu/tag/04MY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids
open CartesianMonoidalCategory MonoidalCategory MonObj

universe u

namespace AlgebraicGeometry

/-- The standing data for the slice situation: a groupoid scheme, a morphism
to its object scheme, and points lying over one another. -/
@[stacks 04MY "the slice situation"]
public structure SliceSituation where
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The groupoid scheme `(U, R, s, t, c)` over `S`. -/
  groupoid : GroupoidScheme S
  /-- The scheme `U'`, regarded over `S`. -/
  U' : Over S
  /-- The restricting morphism `g : U' ⟶ U`. -/
  g : U' ⟶ groupoid.objects
  /-- The point `u ∈ U`. -/
  u : groupoid.objects.left
  /-- The point `u' ∈ U'`. -/
  u' : U'.left
  /-- The compatibility `g(u') = u`. -/
  mapsTo : g.left u' = u

namespace SliceSituation

/-- The restriction of the groupoid along `g`. -/
noncomputable def restriction (D : SliceSituation) :
    GroupoidScheme.Restriction D.groupoid D.g :=
  GroupoidScheme.restrict D.groupoid D.g

/-- The restricted groupoid scheme `(U', R', s', t', c')`. -/
noncomputable def restrictedGroupoid (D : SliceSituation) : GroupoidScheme D.S :=
  D.restriction.groupoid

/-- The point of the object scheme of the chosen restricted groupoid
corresponding to `u'`. -/
noncomputable def restrictedObjectPoint (D : SliceSituation) :
    D.restrictedGroupoid.objects.left :=
  (eqToHom D.restriction.objects_eq.symm).left D.u'

/-- The scheme `U' ×_{g,U,t} R`. -/
noncomputable def arrowSource (D : SliceSituation) : Over D.S :=
  pullback D.g D.groupoid.target

/-- The morphism `h = s ∘ pr₂ : U' ×_{g,U,t} R ⟶ U` (the projection
to `R` is the second projection in the chosen pullback). -/
noncomputable def sourceMap (D : SliceSituation) :
    D.arrowSource ⟶ D.groupoid.objects :=
  pullback.snd D.g D.groupoid.target ≫ D.groupoid.source

/-- The source morphism of the chosen presentation of the restricted arrow
scheme. -/
noncomputable def restrictedSource (D : SliceSituation) :
    (restrictionArrows D.groupoid D.g).left ⟶ D.U'.left :=
  (restrictionSource D.groupoid D.g).left

/-- The scheme-theoretic source fibre `F_u`. -/
noncomputable def sourceFiber (D : SliceSituation) : Scheme :=
  D.groupoid.source.left.fiber D.u

/-- The scheme-theoretic stabilizer fibre `G_u`. -/
noncomputable def stabilizerFiber (D : SliceSituation) : Scheme :=
  (stabilizer D.groupoid).hom.fiber D.u

/-- The stabilizer fibre of the restricted groupoid at `u'`. -/
noncomputable def restrictedStabilizerFiber (D : SliceSituation) : Scheme :=
  (stabilizer D.restrictedGroupoid).hom.fiber D.restrictedObjectPoint

/-- The scheme-theoretic source fibre `F'_{u'}` of the restriction. -/
noncomputable def restrictedSourceFiber (D : SliceSituation) : Scheme :=
  D.restrictedSource.fiber D.u'

/-- The residue-field morphism `Spec(κ(u')) ⟶ Spec(κ(u))` induced by `g`
and the equality `g(u') = u`. -/
noncomputable def residueSpectrumMap (D : SliceSituation) :
    Spec (D.U'.left.residueField D.u') ⟶
      Spec (D.groupoid.objects.left.residueField D.u) :=
  Spec.map ((D.groupoid.objects.left.residueFieldCongr D.mapsTo).inv ≫
    D.g.left.residueFieldMap D.u')

/-- The base change of `h⁻¹(u)` from `κ(u)` to `κ(u')`. -/
noncomputable def baseChangedSourceFiber (D : SliceSituation) : Scheme :=
  pullback (D.sourceMap.left.fiberToSpecResidueField D.u) D.residueSpectrumMap

/-- The canonical comparison expressing
`F'_{u'} = h⁻¹(u) ×_{Spec(κ(u))} Spec(κ(u'))`.

The two equations specify the comparison by its projection to the original
arrow scheme and its residue-field projection. -/
structure SliceFiberComparison (D : SliceSituation) where
  /-- The canonical base-change isomorphism. -/
  iso : D.restrictedSourceFiber ≅ D.baseChangedSourceFiber
  /-- After projection to `R`, the comparison is the canonical map from the
  restricted arrow scheme to the original arrow scheme. -/
  iso_hom_arrow :
    iso.hom ≫
        pullback.fst (D.sourceMap.left.fiberToSpecResidueField D.u)
          D.residueSpectrumMap ≫
        D.sourceMap.left.fiberι D.u ≫
        (pullback.snd D.g D.groupoid.target).left =
      D.restrictedSource.fiberι D.u' ≫
        (restrictionArrowsToArrows D.groupoid D.g).left
  /-- The second projection is the canonical map of the restricted fibre to
  `Spec(κ(u'))`. -/
  iso_hom_residue :
    iso.hom ≫
        pullback.snd (D.sourceMap.left.fiberToSpecResidueField D.u)
          D.residueSpectrumMap =
      D.restrictedSource.fiberToSpecResidueField D.u'

/-- The map of scheme-theoretic fibres induced by a commuting square, at a point of the target of
the right-hand vertical map. -/
private noncomputable def mapFibers {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y)
    (f' : X' ⟶ Y') (m : X' ⟶ X) (g : Y' ⟶ Y)
    (comm : f' ≫ g = m ≫ f) (x' : Y') (y : Y) (hy : g x' = y) :
    f'.fiber x' ⟶ f.fiber y :=
  pullback.map _ _ _ _ m
    (Spec.map ((Y.residueFieldCongr hy).inv ≫ g.residueFieldMap x')) g comm (by
      calc
        _ = Spec.map (g.residueFieldMap x') ≫ Y.fromSpecResidueField (g x') :=
          (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField (f := g) x').symm
        _ = Spec.map (g.residueFieldMap x') ≫
              Spec.map ((Y.residueFieldCongr hy).inv) ≫ Y.fromSpecResidueField y := by
          rw [← Category.assoc, ← Scheme.residueFieldCongr_fromSpecResidueField hy.symm]
          rw [Scheme.residueFieldCongr_inv hy]
          exact (Category.assoc _ _ _).symm
        _ = Spec.map ((Y.residueFieldCongr hy).inv ≫ g.residueFieldMap x') ≫
              Y.fromSpecResidueField y := by
          rw [Spec.map_comp]
          symm
          exact Category.assoc _ _ _)

/-- The source of the restricted arrow scheme, the canonical map to the original arrow scheme and
the restricting morphism form a pullback square on underlying schemes. -/
private lemma restrictionSourceSquare {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) :
    IsPullback
      (pullback.fst (pullback.snd g G.target) (pullback.fst G.source g)).left
      (pullback.snd (pullback.snd g G.target) (pullback.fst G.source g) ≫
        pullback.snd G.source g).left
      (pullback.snd g G.target ≫ G.source).left
      g.left := by
  let P := pullback g G.target
  let Q := pullback G.source g
  have h₁ : IsPullback
      (pullback.fst (pullback.snd g G.target) (pullback.fst G.source g))
      (pullback.snd (pullback.snd g G.target) (pullback.fst G.source g))
      (pullback.snd g G.target) (pullback.fst G.source g) :=
    IsPullback.of_hasPullback _ _
  have h₂ : IsPullback (pullback.fst G.source g) (pullback.snd G.source g)
      G.source g := IsPullback.of_hasPullback _ _
  have hp := (h₁.paste_vert h₂).map (Over.forget S)
  simpa [P, Q] using hp

/-- The canonical base-change comparison of source fibres, extracted from the pullback square of
the restriction. -/
private noncomputable def sliceFiberComparisonData (D : SliceSituation) :
    SliceFiberComparison D := by
  cases D with
  | mk S G U' g u u' mapsTo =>
    cases mapsTo
    let D : SliceSituation := ⟨S, G, U', g, g.left u', u', rfl⟩
    change SliceFiberComparison D
    have hp := isPullback_fiberToSpecResidueField_of_isPullback
      (restrictionSourceSquare G g) u'
    have hres : D.residueSpectrumMap = Spec.map (g.left.residueFieldMap u') := by
      simp [D, residueSpectrumMap]
    -- Naming the fibre types here is what keeps `hp'` and the comparison isomorphism below
    -- stated at the scheme-theoretic fibres rather than at the fibre products defining them.
    let m : D.restrictedSource.fiber D.u' ⟶ D.sourceMap.left.fiber D.u :=
      pullback.map D.restrictedSource (U'.left.fromSpecResidueField u')
      D.sourceMap.left (G.objects.left.fromSpecResidueField (g.left u'))
      (pullback.fst (pullback.snd g G.target) (pullback.fst G.source g)).left
      (Spec.map (g.left.residueFieldMap u')) g.left
      (restrictionSourceSquare G g).w.symm
      (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField (f := g.left) u').symm
    have hp' : IsPullback m (D.restrictedSource.fiberToSpecResidueField D.u')
        (D.sourceMap.left.fiberToSpecResidueField D.u) D.residueSpectrumMap := by
      rw [hres]
      exact hp
    -- The projection formula for `m` is proved on its own, so that the only step taken on the
    -- goal itself is the one `isoPullback_hom_fst` provides.
    have hm : m ≫ D.sourceMap.left.fiberι D.u ≫
          (pullback.snd D.g D.groupoid.target).left =
        D.restrictedSource.fiberι D.u' ≫
          (restrictionArrowsToArrows D.groupoid D.g).left := by
      simp only [m, D, Scheme.Hom.fiberι, pullback.map, restrictionArrowsToArrows]
      refine (Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ (pullback.snd g G.target).left)
          (pullback.lift_fst _ _ _)).trans ?_)
      exact Category.assoc _ _ _
    refine ⟨hp'.isoPullback, ?_, hp'.isoPullback_hom_snd⟩
    refine Eq.trans ?_ hm
    -- Restating the goal at the fibre product the projection is taken from, rather than at the
    -- name `baseChangedSourceFiber` for it, is what makes the reassociation below explicit.
    change hp'.isoPullback.hom ≫ pullback.fst
          (D.sourceMap.left.fiberToSpecResidueField D.u) D.residueSpectrumMap ≫
          D.sourceMap.left.fiberι D.u ≫ (pullback.snd D.g D.groupoid.target).left =
        m ≫ D.sourceMap.left.fiberι D.u ≫ (pullback.snd D.g D.groupoid.target).left
    rw [← Category.assoc, hp'.isoPullback_hom_fst]

/-- **Stacks Project, Tag 04MY.** The source fibre in the restricted groupoid
is canonically the base change of `h⁻¹(u)` along
`Spec(κ(u')) ⟶ Spec(κ(u))`. -/
@[stacks 04MY "the fibre comparison"]
noncomputable def sliceFiberComparison (D : SliceSituation) :
    SliceFiberComparison D :=
  Classical.choice (by exact ⟨sliceFiberComparisonData D⟩)

/-- The identity points in the source and stabilizer fibres of a groupoid and
of its restriction, together with the canonical maps carrying the restricted
identity points to the original ones.  The projection equations characterize
all the points occurring here as the relevant identity arrows. -/
structure SliceIdentityPoints (D : SliceSituation) where
  /-- The identity arrow viewed as a point of the original source fibre. -/
  sourceIdentity : D.sourceFiber
  sourceIdentity_fiberι :
    D.groupoid.source.left.fiberι D.u sourceIdentity =
      D.groupoid.identity.left D.u
  /-- The identity arrow viewed as a point of the original stabilizer. -/
  stabilizerIdentity : (stabilizer D.groupoid).left
  stabilizerIdentity_arrow :
    stabilizerArrow D.groupoid stabilizerIdentity =
      D.groupoid.identity.left D.u
  stabilizerIdentity_base :
    (stabilizer D.groupoid).hom stabilizerIdentity = D.u
  /-- The same point viewed in the fibre `G_u`. -/
  stabilizerFiberIdentity : D.stabilizerFiber
  stabilizerFiberIdentity_fiberι :
    (stabilizer D.groupoid).hom.fiberι D.u stabilizerFiberIdentity =
      stabilizerIdentity
  /-- The identity arrow of the restriction, in the chosen iterated-pullback
  presentation of `R'`. -/
  restrictedIdentity : (restrictionArrows D.groupoid D.g).left
  restrictedIdentity_source :
    D.restrictedSource restrictedIdentity = D.u'
  restrictedIdentity_target :
    (restrictionTarget D.groupoid D.g).left restrictedIdentity = D.u'
  restrictedIdentity_arrow :
    (restrictionArrowsToArrows D.groupoid D.g).left restrictedIdentity =
      D.groupoid.identity.left D.u
  /-- The restricted identity viewed as a point of `F'_{u'}`. -/
  restrictedSourceIdentity : D.restrictedSourceFiber
  restrictedSourceIdentity_fiberι :
    D.restrictedSource.fiberι D.u' restrictedSourceIdentity = restrictedIdentity
  /-- The identity arrow viewed as a point of the restricted stabilizer. -/
  restrictedStabilizerIdentity : (stabilizer D.restrictedGroupoid).left
  restrictedStabilizerIdentity_arrow :
    stabilizerArrow D.restrictedGroupoid restrictedStabilizerIdentity =
      D.restrictedGroupoid.identity.left D.restrictedObjectPoint
  restrictedStabilizerIdentity_base :
    (stabilizer D.restrictedGroupoid).hom restrictedStabilizerIdentity =
      D.restrictedObjectPoint
  /-- The same point viewed in the restricted stabilizer fibre. -/
  restrictedStabilizerFiberIdentity : D.restrictedStabilizerFiber
  restrictedStabilizerFiberIdentity_fiberι :
    (stabilizer D.restrictedGroupoid).hom.fiberι D.restrictedObjectPoint
        restrictedStabilizerFiberIdentity = restrictedStabilizerIdentity
  /-- The canonical map `F'_{u'} ⟶ F_u`. -/
  sourceFiberMap : D.restrictedSourceFiber ⟶ D.sourceFiber
  sourceFiberMap_identity : sourceFiberMap restrictedSourceIdentity = sourceIdentity
  sourceFiberMap_arrow :
    sourceFiberMap ≫ D.groupoid.source.left.fiberι D.u =
      D.restrictedSource.fiberι D.u' ≫
        (restrictionArrowsToArrows D.groupoid D.g).left
  /-- The canonical map `G'_{u'} ⟶ G_u`. -/
  stabilizerFiberMap : D.restrictedStabilizerFiber ⟶ D.stabilizerFiber
  stabilizerFiberMap_identity :
    stabilizerFiberMap restrictedStabilizerFiberIdentity = stabilizerFiberIdentity
  stabilizerFiberMap_arrow :
    stabilizerFiberMap ≫ (stabilizer D.groupoid).hom.fiberι D.u ≫
        stabilizerArrow D.groupoid =
      (stabilizer D.restrictedGroupoid).hom.fiberι D.restrictedObjectPoint ≫
        stabilizerArrow D.restrictedGroupoid ≫
        D.restriction.hom.mapArrows.left

/-- The generalized point `Spec κ(u) ⟶ U` at the point `u`, regarded over the base. -/
private noncomputable def residueFieldPoint {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.objects.left) :
    Over.mk (G.objects.left.fromSpecResidueField u ≫ G.objects.hom) ⟶ G.objects :=
  Over.homMk (G.objects.left.fromSpecResidueField u) rfl

/-- The generalized point of the stabilizer given by the identity arrow at `u`. -/
private noncomputable def stabilizerIdentityLift {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.objects.left) :
    Over.mk (G.objects.left.fromSpecResidueField u ≫ G.objects.hom) ⟶ stabilizerOverBase G :=
  pullback.lift (residueFieldPoint G u ≫ G.identity) (residueFieldPoint G u) (by
    apply hom_ext
    · simp only [Category.assoc, sourceTarget, diagonal, lift_fst, G.target_identity]
    · simp only [Category.assoc, sourceTarget, diagonal, lift_snd, G.source_identity])

/-- The identity arrow at a point, as a point of the stabilizer. -/
private noncomputable def stabilizerIdentityPoint {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.objects.left) : (stabilizer G).left :=
  (stabilizerIdentityLift G u).left (IsLocalRing.closedPoint _)

/-- The identity point of the stabilizer, projected to the arrows. -/
private lemma stabilizerIdentityLift_fst {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.objects.left) :
    stabilizerIdentityLift G u ≫ pullback.fst (sourceTarget G) (diagonal G) =
      residueFieldPoint G u ≫ G.identity :=
  pullback.lift_fst _ _ _

/-- The identity point of the stabilizer, projected to the objects. -/
private lemma stabilizerIdentityLift_snd {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.objects.left) :
    stabilizerIdentityLift G u ≫ pullback.snd (sourceTarget G) (diagonal G) =
      residueFieldPoint G u :=
  pullback.lift_snd _ _ _

/-- The identity point of the stabilizer has the identity arrow as its underlying arrow. -/
private lemma stabilizerIdentityPoint_arrow {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.objects.left) :
    stabilizerArrow G (stabilizerIdentityPoint G u) = G.identity.left u := by
  have h := congrArg (fun f : _ ⟶ G.arrows => f.left (IsLocalRing.closedPoint _))
    (stabilizerIdentityLift_fst G u)
  exact h.trans (congrArg G.identity.left (Scheme.fromSpecResidueField_apply u _))

/-- The identity point of the stabilizer lies over the chosen point of the object scheme. -/
private lemma stabilizerIdentityPoint_base {S : Scheme.{u}} (G : GroupoidScheme S)
    (u : G.objects.left) :
    (stabilizer G).hom (stabilizerIdentityPoint G u) = u := by
  have h := congrArg (fun f : _ ⟶ G.objects => f.left (IsLocalRing.closedPoint _))
    (stabilizerIdentityLift_snd G u)
  exact h.trans (Scheme.fromSpecResidueField_apply u _)

/-- The identity arrow of the restricted groupoid, carried into the chosen iterated fibre product
presenting the restricted arrow scheme. -/
private noncomputable def restrictedIdentityPoint (D : SliceSituation) :
    (restrictionArrows D.groupoid D.g).left :=
  (eqToHom D.restriction.arrows_eq).left
    (D.restrictedGroupoid.identity.left D.restrictedObjectPoint)

/-- The comparison of the object scheme of the restriction with `U'` is inverse to its inverse. -/
private lemma objects_eqToHom_apply_symm (D : SliceSituation) (x : D.U'.left) :
    (eqToHom D.restriction.objects_eq).left
      ((eqToHom D.restriction.objects_eq.symm).left x) = x := by
  rw [← Scheme.Hom.comp_apply]
  simp

/-- A morphism out of the restricted arrow scheme which, after identifying with the arrows of the
chosen restriction, is an end of the groupoid sends the restricted identity point to `u'`. -/
private lemma restrictedIdentityPoint_apply (D : SliceSituation)
    (r : (restrictionArrows D.groupoid D.g).left ⟶ D.U'.left)
    (a : D.restriction.groupoid.arrows.left ⟶ D.restriction.groupoid.objects.left)
    (ha : a = (eqToHom D.restriction.arrows_eq).left ≫ r ≫
      (eqToHom D.restriction.objects_eq.symm).left)
    (hid : D.restriction.groupoid.identity.left ≫ a = 𝟙 _) :
    r (restrictedIdentityPoint D) = D.u' := by
  have h : a (D.restriction.groupoid.identity.left
      ((eqToHom D.restriction.objects_eq.symm).left D.u')) =
      (eqToHom D.restriction.objects_eq.symm).left D.u' := by
    rw [← Scheme.Hom.comp_apply, hid]
    rfl
  subst ha
  simp only [Scheme.Hom.comp_apply] at h
  have h' := congrArg (eqToHom D.restriction.objects_eq).left h
  simp only [objects_eqToHom_apply_symm] at h'
  exact h'

/-- The restricted identity point has source the chosen point of `U'`. -/
private lemma restrictedIdentityPoint_source (D : SliceSituation) :
    D.restrictedSource (restrictedIdentityPoint D) = D.u' :=
  restrictedIdentityPoint_apply D _ _ (congrArg Over.Hom.left D.restriction.source_eq)
    (congrArg Over.Hom.left D.restriction.groupoid.source_identity)

/-- The restricted identity point has target the chosen point of `U'`. -/
private lemma restrictedIdentityPoint_target (D : SliceSituation) :
    (restrictionTarget D.groupoid D.g).left (restrictedIdentityPoint D) = D.u' :=
  restrictedIdentityPoint_apply D _ _ (congrArg Over.Hom.left D.restriction.target_eq)
    (congrArg Over.Hom.left D.restriction.groupoid.target_identity)

/-- The map of object schemes of the restriction sends the point corresponding to `u'` to `u`. -/
private lemma restriction_mapObjects_apply (D : SliceSituation) :
    D.restriction.hom.mapObjects.left ((eqToHom D.restriction.objects_eq.symm).left D.u') =
      D.u := by
  rw [congrArg Over.Hom.left D.restriction.mapObjects_eq, Over.comp_left, Scheme.Hom.comp_apply,
    objects_eqToHom_apply_symm, D.mapsTo]

/-- The map of arrow schemes of the restriction sends the identity arrow at the point corresponding
to `u'` to the identity arrow at `u`. -/
private lemma restriction_mapArrows_identity_apply (D : SliceSituation) :
    D.restriction.hom.mapArrows.left (D.restriction.groupoid.identity.left
      ((eqToHom D.restriction.objects_eq.symm).left D.u')) = D.groupoid.identity.left D.u := by
  have hmi : D.restriction.hom.mapObjects.left ≫ D.groupoid.identity.left =
      D.restriction.groupoid.identity.left ≫ D.restriction.hom.mapArrows.left :=
    congrArg Over.Hom.left D.restriction.hom.map_identity
  rw [← restriction_mapObjects_apply D, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← hmi]
  rfl

/-- The restricted identity point maps to the identity arrow of the original groupoid. -/
private lemma restrictedIdentityPoint_arrow (D : SliceSituation) :
    (restrictionArrowsToArrows D.groupoid D.g).left (restrictedIdentityPoint D) =
      D.groupoid.identity.left D.u := by
  rw [← restriction_mapArrows_identity_apply D, congrArg Over.Hom.left D.restriction.mapArrows_eq,
    Over.comp_left, Scheme.Hom.comp_apply]
  rfl

/-- A point of the source of a morphism lying over a given point of the target, as a point of the
scheme-theoretic fibre there. -/
private noncomputable def pointInFiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) (x : X) (h : f x = y) : f.fiber y :=
  (f.fiberHomeo y).symm ⟨x, by simpa using h⟩

/-- `pointInFiber` is a lift of the given point along the inclusion of the fibre. -/
private lemma pointInFiber_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) (x : X) (h : f x = y) : f.fiberι y (pointInFiber f y x h) = x :=
  f.fiberι_fiberHomeo_symm y ⟨x, by simpa using h⟩

/-- `mapFibers` is compatible with the inclusions of the two fibres. -/
private lemma mapFibers_fiberι {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y)
    (f' : X' ⟶ Y') (m : X' ⟶ X) (g : Y' ⟶ Y)
    (comm : f' ≫ g = m ≫ f) (x' : Y') (y : Y) (hy : g x' = y) :
    mapFibers f f' m g comm x' y hy ≫ f.fiberι y = f'.fiberι x' ≫ m := by
  unfold mapFibers
  exact pullback.lift_fst _ _ _

/-- `mapFibers` carries the point of a fibre determined by a point of the source to the
corresponding point of the target fibre. -/
private lemma mapFibers_pointInFiber {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y)
    (f' : X' ⟶ Y') (m : X' ⟶ X) (g : Y' ⟶ Y)
    (comm : f' ≫ g = m ≫ f) (x' : Y') (y : Y) (hy : g x' = y)
    (z : X') (hz : f' z = x') :
    mapFibers f f' m g comm x' y hy (pointInFiber f' x' z hz) =
      pointInFiber f y (m z) (by
        have hc := congrArg (fun q : X' ⟶ Y => q z) comm
        have hc' : g (f' z) = f (m z) := by
          simpa only [Scheme.Hom.comp_apply] using hc
        exact hc'.symm.trans ((congrArg g hz).trans hy)) := by
  apply (f.fiberHomeo y).injective
  apply Subtype.ext
  change f.fiberι y (mapFibers f f' m g comm x' y hy
      (pointInFiber f' x' z hz)) =
    f.fiberι y (pointInFiber f y (m z) _)
  calc
    _ = (mapFibers f f' m g comm x' y hy ≫ f.fiberι y)
        (pointInFiber f' x' z hz) := by rw [Scheme.Hom.comp_apply]
    _ = (f'.fiberι x' ≫ m) (pointInFiber f' x' z hz) := by
      rw [mapFibers_fiberι]
    _ = m z := by simp [pointInFiber_fiberι]
    _ = f.fiberι y (pointInFiber f y (m z) _) := by
      rw [pointInFiber_fiberι]

/-- The source of the restricted arrow scheme and the restricting morphism commute with the
canonical map to the original arrow scheme and the original source. -/
private lemma restrictedSource_arrow_square (D : SliceSituation) :
    D.restrictedSource ≫ D.g.left =
      (restrictionArrowsToArrows D.groupoid D.g).left ≫ D.groupoid.source.left :=
  congrArg Over.Hom.left (GroupoidScheme.restriction_condition D.groupoid D.g)

/-- The compatible identity points of the stabilizer and source fibres before and after
restriction, together with the canonical maps of fibres. -/
private noncomputable def sliceIdentityPointsData (D : SliceSituation) :
    SliceIdentityPoints D := by
  let sourceIdentity : D.sourceFiber :=
    pointInFiber D.groupoid.source.left D.u
      (D.groupoid.identity.left D.u) (by
        have hs : D.groupoid.identity.left ≫ D.groupoid.source.left = 𝟙 _ :=
          congrArg Over.Hom.left D.groupoid.source_identity
        change D.groupoid.source.left (D.groupoid.identity.left D.u) = D.u
        rw [← Scheme.Hom.comp_apply, hs]
        rfl)
  let restrictedIdentity : (restrictionArrows D.groupoid D.g).left :=
    restrictedIdentityPoint D
  let restrictedSourceIdentity : D.restrictedSourceFiber :=
    pointInFiber D.restrictedSource D.u' restrictedIdentity
      (restrictedIdentityPoint_source D)
  let op : D.restriction.groupoid.objects.left :=
    (eqToHom D.restriction.objects_eq.symm).left D.u'
  let restrictedStabilizerIdentity : (stabilizer D.restriction.groupoid).left :=
    stabilizerIdentityPoint D.restriction.groupoid op
  have hobj : D.restriction.hom.mapObjects.left.base op = D.u :=
    restriction_mapObjects_apply D
  let stabilizerIdentity : (stabilizer D.groupoid).left :=
    (stabilizerMap D.restriction.hom).left restrictedStabilizerIdentity
  have hstabBase : (stabilizer D.groupoid).hom stabilizerIdentity = D.u := by
    calc
      _ = D.restriction.hom.mapObjects.left
          ((stabilizer D.restriction.groupoid).hom restrictedStabilizerIdentity) := by
        rw [← Scheme.Hom.comp_apply, stabilizerMap_left_comp_hom]
        rfl
      _ = D.restriction.hom.mapObjects.left op := by
        rw [stabilizerIdentityPoint_base]
      _ = D.u := hobj
  have hmapIdentity : D.restriction.hom.mapArrows.left.base
      ((D.restriction.groupoid.identity.left).base op) =
        (D.groupoid.identity.left).base D.u := restriction_mapArrows_identity_apply D
  have hstabArrow : (stabilizerArrow D.groupoid).base stabilizerIdentity =
      (D.groupoid.identity.left).base D.u := by
    dsimp [SliceSituation.restrictedGroupoid]
    have hst := stabilizerMap_left_comp_stabilizerArrow D.restriction.hom
    have hstPoint := congrArg
      (fun f : Scheme.Hom _ _ => f.base restrictedStabilizerIdentity) hst
    rw [Scheme.Hom.comp_base, ConcreteCategory.comp_apply] at hstPoint
    have hrid : (stabilizerArrow D.restriction.groupoid).base restrictedStabilizerIdentity =
        (D.restriction.groupoid.identity.left).base op := by
      simpa using stabilizerIdentityPoint_arrow D.restriction.groupoid op
    calc
      _ = D.restriction.hom.mapArrows.left.base
          ((stabilizerArrow D.restriction.groupoid).base restrictedStabilizerIdentity) := hstPoint
      _ = D.restriction.hom.mapArrows.left.base
          ((D.restriction.groupoid.identity.left).base op) := by rw [hrid]
      _ = (D.groupoid.identity.left).base D.u := hmapIdentity
  let stabilizerFiberIdentity : D.stabilizerFiber :=
    pointInFiber (stabilizer D.groupoid).hom D.u stabilizerIdentity hstabBase
  let restrictedStabilizerFiberIdentity : D.restrictedStabilizerFiber :=
    pointInFiber (stabilizer D.restriction.groupoid).hom op
      restrictedStabilizerIdentity
      (stabilizerIdentityPoint_base D.restriction.groupoid op)
  let sourceFiberMap : D.restrictedSourceFiber ⟶ D.sourceFiber :=
    mapFibers D.groupoid.source.left D.restrictedSource
      (restrictionArrowsToArrows D.groupoid D.g).left D.g.left
      (restrictedSource_arrow_square D) D.u' D.u D.mapsTo
  let stabilizerFiberMap : D.restrictedStabilizerFiber ⟶ D.stabilizerFiber :=
    mapFibers (stabilizer D.groupoid).hom
      (stabilizer D.restriction.groupoid).hom
      (stabilizerMap D.restriction.hom).left
      D.restriction.hom.mapObjects.left
      (stabilizerMap_left_comp_hom D.restriction.hom).symm
      op D.u hobj
  refine
    { sourceIdentity := sourceIdentity
      sourceIdentity_fiberι := pointInFiber_fiberι _ _ _ _
      stabilizerIdentity := stabilizerIdentity
      stabilizerIdentity_arrow := by simpa using hstabArrow
      stabilizerIdentity_base := hstabBase
      stabilizerFiberIdentity := stabilizerFiberIdentity
      stabilizerFiberIdentity_fiberι := pointInFiber_fiberι _ _ _ _
      restrictedIdentity := restrictedIdentity
      restrictedIdentity_source := restrictedIdentityPoint_source D
      restrictedIdentity_target := restrictedIdentityPoint_target D
      restrictedIdentity_arrow := restrictedIdentityPoint_arrow D
      restrictedSourceIdentity := restrictedSourceIdentity
      restrictedSourceIdentity_fiberι := pointInFiber_fiberι _ _ _ _
      restrictedStabilizerIdentity := restrictedStabilizerIdentity
      restrictedStabilizerIdentity_arrow := stabilizerIdentityPoint_arrow _ _
      restrictedStabilizerIdentity_base := stabilizerIdentityPoint_base _ _
      restrictedStabilizerFiberIdentity := restrictedStabilizerFiberIdentity
      restrictedStabilizerFiberIdentity_fiberι := pointInFiber_fiberι _ _ _ _
      sourceFiberMap := sourceFiberMap
      sourceFiberMap_identity := by
        dsimp [sourceFiberMap]
        -- `Eq.trans` rather than `calc`, so that the two fibre types are matched up by the
        -- elaborator instead of by a `Trans` instance search.
        refine (mapFibers_pointInFiber _ _ _ _ _ _ _ _ _ _).trans ?_
        dsimp [sourceIdentity, pointInFiber]
        apply (D.groupoid.source.left.fiberHomeo D.u).injective
        simp
        simpa [restrictedIdentity] using restrictedIdentityPoint_arrow D
      sourceFiberMap_arrow := by
        dsimp [sourceFiberMap]
        exact mapFibers_fiberι _ _ _ _ _ _ _ _
      stabilizerFiberMap := stabilizerFiberMap
      stabilizerFiberMap_identity := by
        dsimp [stabilizerFiberMap]
        exact mapFibers_pointInFiber _ _ _ _ _ _ _ _ _ _
      stabilizerFiberMap_arrow := by
        dsimp [stabilizerFiberMap]
        change mapFibers (stabilizer D.groupoid).hom
          (stabilizer D.restriction.groupoid).hom
          (stabilizerMap D.restriction.hom).left
          D.restriction.hom.mapObjects.left
          (stabilizerMap_left_comp_hom D.restriction.hom).symm op D.u hobj ≫
            (stabilizer D.groupoid).hom.fiberι D.u ≫ stabilizerArrow D.groupoid =
          (stabilizer D.restriction.groupoid).hom.fiberι op ≫
            stabilizerArrow D.restriction.groupoid ≫ D.restriction.hom.mapArrows.left
        rw [← Category.assoc, mapFibers_fiberι, Category.assoc,
          stabilizerMap_left_comp_stabilizerArrow] }

/-- **Stacks Project, Tag 04MY.** The identity arrows determine compatible
points of the stabilizer and source fibres before and after restriction; the
canonical maps of fibres carry each restricted identity point to the original
one. -/
@[stacks 04MY "the compatible identity points"]
noncomputable def sliceIdentityPoints (D : SliceSituation) :
    SliceIdentityPoints D :=
  Classical.choice (by exact ⟨sliceIdentityPointsData D⟩)

end SliceSituation

/-- **Stacks Project, Tag 04MY.** The stabilizer of a groupoid scheme is a
locally closed subscheme of its arrow scheme. -/
@[stacks 04MY "the stabilizer is locally closed"]
public theorem stabilizerArrow_isImmersion {S : Scheme.{u}} (G : GroupoidScheme S) :
    IsImmersion (stabilizerArrow G) := by
  change IsImmersion ((pullback.fst (sourceTarget G) (diagonal G)).left)
  have hd : IsImmersion (diagonal G).left := by
    change IsImmersion (pullback.diagonal G.objects.hom)
    infer_instance
  have hp : IsPullback (pullback.fst (sourceTarget G) (diagonal G))
      (pullback.snd (sourceTarget G) (diagonal G)) (sourceTarget G) (diagonal G) :=
    IsPullback.of_hasPullback _ _
  have hp' : IsPullback ((pullback.fst (sourceTarget G) (diagonal G)).left)
      ((pullback.snd (sourceTarget G) (diagonal G)).left)
      (sourceTarget G).left (diagonal G).left :=
    (hp.preservesLimit_cospan_iff (F := Over.forget S)).mp inferInstance
  exact IsImmersion.isStableUnderBaseChange.of_isPullback hp'.flip hd

end AlgebraicGeometry
