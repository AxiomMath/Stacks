module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.EtaleQuotientMorphism
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantBaseChangeMorphism

/-!
# The stabilizer square of the morphism of base changes induced by a morphism of groupoids

Let `F : G' ⟶ G` be a morphism of groupoid schemes over `S` whose target square and whose
stabilizer square are cartesian, let `C ⟶ C₁` and `C' ⟶ C'₁` be extensions of the two invariant
rings compatible along `ψ : C₁ →+* C'₁`, and let
`F₁ : AlgebraicGeometry.GroupoidScheme.baseChangeHom F ψ hψ bc bc'` be the induced morphism
from the pushforward of the base change of `G'` to the base change of `G`. This file proves that
the stabilizer square of `F₁` is again cartesian.

This is *not* a formal consequence of the two cartesian squares already available for `F₁`. Over
a point of the fibre product of the stabilizer of the base change of `G` with the object scheme
of the base change of `G'`, the cartesian target square produces a unique arrow upstairs with
the prescribed target, and the one thing left to check — that its source agrees with its target
— is exactly where the cartesian stabilizer square of `F` is used, as in
`AlgebraicGeometry.GroupoidScheme.universallyInjective_invariantPullbackComparison`.

The argument is run twice over, so it is isolated here as two statements about an arbitrary
morphism of groupoid schemes: `AlgebraicGeometry.isPullback_stabilizerMap` reduces the cartesian
stabilizer square to the cartesian target square together with the hypothesis that an arrow
whose image has equal source and target has equal source and target, and
`AlgebraicGeometry.source_eq_target_of_mapArrows_source_eq_target` supplies that hypothesis from
a cartesian stabilizer square.

## Main definitions

* `AlgebraicGeometry.stabilizerSquareArrow`: the arrow upstairs attached to a point of the fibre
  product of the stabilizer downstairs with the object scheme upstairs.
* `AlgebraicGeometry.stabilizerSquareLift`: the same point read as a point of the stabilizer
  upstairs.

## Main results

* `AlgebraicGeometry.stabilizerMap_hom_ext`: a point of the stabilizer upstairs is determined by
  its image in the stabilizer downstairs and its base point.
* `AlgebraicGeometry.isPullback_stabilizerMap`: the stabilizer square of a morphism of groupoid
  schemes is cartesian as soon as its target square is and arrows whose image has equal source
  and target have equal source and target.
* `AlgebraicGeometry.source_eq_target_of_mapArrows_source_eq_target`: a cartesian stabilizer
  square makes the latter hypothesis automatic.
* `AlgebraicGeometry.GroupoidScheme.baseChangeMapArrows_source_eq_target` and
  `AlgebraicGeometry.GroupoidScheme.isPullback_stabilizerMap_baseChangeHom`: the hypothesis and
  the conclusion for the induced morphism of base changes.

## Implementation notes

The stabilizer of the pushforward of the base change of `G'` is *not* the stabilizer of that
base change: the monoidal product of `Over (Spec C₁)` is a fibre product over `Spec C₁`, so both
the source-target morphism and the diagonal change when the base is changed. No comparison
between the two stabilizers is needed, because `AlgebraicGeometry.stabilizerLift` and the two
statements above are stated for an arbitrary groupoid scheme and so apply to the pushforward
directly; the structure maps of the pushforward are those of the base change on underlying
schemes, which is what reduces the hypothesis for `F₁` to a statement about the base change
of `G'`.

## References

* [Stacks Project, Tag 03BK](https://stacks.math.columbia.edu/tag/03BK)
* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids
open CartesianMonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-! ### The stabilizer square of a morphism of groupoid schemes -/

section Stabilizer

variable {S : Scheme.{u}} {G G' : GroupoidScheme S} (F : GroupoidScheme.Hom G' G)
  (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left)

include htarget in
/-- A point of the stabilizer of `G'` is determined by its image in the stabilizer of `G`
together with its base point, as soon as the target square of `F` is cartesian. -/
theorem stabilizerMap_hom_ext {T : Scheme.{u}} {k l : T ⟶ (stabilizer G').left}
    (h₁ : k ≫ (stabilizerMap F).left = l ≫ (stabilizerMap F).left)
    (h₂ : k ≫ (stabilizer G').hom = l ≫ (stabilizer G').hom) : k = l := by
  refine (cancel_mono (stabilizerArrow G')).mp (htarget.hom_ext ?_ ?_)
  · rw [Category.assoc, Category.assoc, ← stabilizerMap_left_comp_stabilizerArrow,
      ← Category.assoc, ← Category.assoc, h₁]
  · rw [Category.assoc, Category.assoc, stabilizerArrow_comp_target, h₂]

/-- **The arrow of `G'` attached to a point of the fibre product of the stabilizer of `G` with
the object scheme of `G'`**: the lift, against the cartesian target square of `F`, of the arrow
of `G` underlying the given point of the stabilizer. -/
def stabilizerSquareArrow {T : Scheme.{u}} (a : T ⟶ (stabilizer G).left)
    (b : T ⟶ G'.objects.left) (hab : a ≫ (stabilizer G).hom = b ≫ F.mapObjects.left) :
    T ⟶ G'.arrows.left :=
  htarget.lift (a ≫ stabilizerArrow G) b (by
    rw [Category.assoc, stabilizerArrow_comp_target, hab])

/-- The image in `G` of `AlgebraicGeometry.stabilizerSquareArrow` is the arrow underlying the
given point of the stabilizer of `G`. -/
@[reassoc]
theorem stabilizerSquareArrow_comp_mapArrows {T : Scheme.{u}} (a : T ⟶ (stabilizer G).left)
    (b : T ⟶ G'.objects.left) (hab : a ≫ (stabilizer G).hom = b ≫ F.mapObjects.left) :
    stabilizerSquareArrow F htarget a b hab ≫ F.mapArrows.left = a ≫ stabilizerArrow G :=
  htarget.lift_fst _ _ _

/-- The target of `AlgebraicGeometry.stabilizerSquareArrow` is the given point of the object
scheme of `G'`. -/
@[reassoc]
theorem stabilizerSquareArrow_comp_target {T : Scheme.{u}} (a : T ⟶ (stabilizer G).left)
    (b : T ⟶ G'.objects.left) (hab : a ≫ (stabilizer G).hom = b ≫ F.mapObjects.left) :
    stabilizerSquareArrow F htarget a b hab ≫ G'.target.left = b :=
  htarget.lift_snd _ _ _

/-- The image in `G` of `AlgebraicGeometry.stabilizerSquareArrow` has equal source and
target. -/
theorem stabilizerSquareArrow_map_source_eq_target {T : Scheme.{u}}
    (a : T ⟶ (stabilizer G).left) (b : T ⟶ G'.objects.left)
    (hab : a ≫ (stabilizer G).hom = b ≫ F.mapObjects.left) :
    (stabilizerSquareArrow F htarget a b hab ≫ F.mapArrows.left) ≫ G.source.left =
      (stabilizerSquareArrow F htarget a b hab ≫ F.mapArrows.left) ≫ G.target.left := by
  rw [stabilizerSquareArrow_comp_mapArrows, Category.assoc, Category.assoc,
    stabilizerArrow_comp_source, stabilizerArrow_comp_target]

variable (hsrc : ∀ {T : Scheme.{u}} (r : T ⟶ G'.arrows.left),
  (r ≫ F.mapArrows.left) ≫ G.source.left = (r ≫ F.mapArrows.left) ≫ G.target.left →
    r ≫ G'.source.left = r ≫ G'.target.left)

/-- **The point of the stabilizer of `G'` attached to a point of the fibre product of the
stabilizer of `G` with the object scheme of `G'`.** -/
def stabilizerSquareLift {T : Scheme.{u}} (a : T ⟶ (stabilizer G).left)
    (b : T ⟶ G'.objects.left) (hab : a ≫ (stabilizer G).hom = b ≫ F.mapObjects.left) :
    T ⟶ (stabilizer G').left :=
  stabilizerLift G' (stabilizerSquareArrow F htarget a b hab)
    (hsrc _ (stabilizerSquareArrow_map_source_eq_target F htarget a b hab))

/-- The arrow underlying `AlgebraicGeometry.stabilizerSquareLift`. -/
@[reassoc]
theorem stabilizerSquareLift_comp_stabilizerArrow {T : Scheme.{u}} (a : T ⟶ (stabilizer G).left)
    (b : T ⟶ G'.objects.left) (hab : a ≫ (stabilizer G).hom = b ≫ F.mapObjects.left) :
    stabilizerSquareLift F htarget hsrc a b hab ≫ stabilizerArrow G' =
      stabilizerSquareArrow F htarget a b hab :=
  stabilizerLift_comp_stabilizerArrow G' _ _

/-- The base point of `AlgebraicGeometry.stabilizerSquareLift` is the given point of the object
scheme of `G'`. -/
@[reassoc]
theorem stabilizerSquareLift_comp_hom {T : Scheme.{u}} (a : T ⟶ (stabilizer G).left)
    (b : T ⟶ G'.objects.left) (hab : a ≫ (stabilizer G).hom = b ≫ F.mapObjects.left) :
    stabilizerSquareLift F htarget hsrc a b hab ≫ (stabilizer G').hom = b := by
  have h : stabilizerSquareLift F htarget hsrc a b hab ≫ (stabilizer G').hom =
      stabilizerSquareArrow F htarget a b hab ≫ G'.source.left :=
    stabilizerLift_comp_hom G' _ _
  rw [h, hsrc _ (stabilizerSquareArrow_map_source_eq_target F htarget a b hab),
    stabilizerSquareArrow_comp_target]

/-- The image of `AlgebraicGeometry.stabilizerSquareLift` in the stabilizer of `G` is the given
point of the stabilizer of `G`. -/
@[reassoc]
theorem stabilizerSquareLift_comp_stabilizerMap {T : Scheme.{u}} (a : T ⟶ (stabilizer G).left)
    (b : T ⟶ G'.objects.left) (hab : a ≫ (stabilizer G).hom = b ≫ F.mapObjects.left) :
    stabilizerSquareLift F htarget hsrc a b hab ≫ (stabilizerMap F).left = a := by
  refine (cancel_mono (stabilizerArrow G)).mp ?_
  rw [Category.assoc, stabilizerMap_left_comp_stabilizerArrow, ← Category.assoc,
    stabilizerSquareLift_comp_stabilizerArrow, stabilizerSquareArrow_comp_mapArrows]

include htarget hsrc in
/-- **The stabilizer square of a morphism of groupoid schemes is cartesian** as soon as its
target square is and an arrow of `G'` whose image in `G` has equal source and target has itself
equal source and target. -/
theorem isPullback_stabilizerMap :
    IsPullback (stabilizerMap F).left (stabilizer G').hom (stabilizer G).hom
      F.mapObjects.left :=
  IsPullback.of_isLimit' ⟨stabilizerMap_left_comp_hom F⟩ (PullbackCone.IsLimit.mk _
    (fun s => stabilizerSquareLift F htarget hsrc s.fst s.snd s.condition)
    (fun s => stabilizerSquareLift_comp_stabilizerMap F htarget hsrc s.fst s.snd s.condition)
    (fun s => stabilizerSquareLift_comp_hom F htarget hsrc s.fst s.snd s.condition)
    (fun _ _ h₁ h₂ => stabilizerMap_hom_ext F htarget
      (h₁.trans (stabilizerSquareLift_comp_stabilizerMap F htarget hsrc _ _ _).symm)
      (h₂.trans (stabilizerSquareLift_comp_hom F htarget hsrc _ _ _).symm)))

include htarget in
/-- **An arrow of `G'` whose image in `G` has equal source and target has equal source and
target**, as soon as the target and stabilizer squares of `F` are cartesian.

The image is a point of the stabilizer of `G`, the cartesian stabilizer square lifts it to a
point of the stabilizer of `G'`, and the cartesian target square identifies the arrow underlying
that point with the given arrow. -/
theorem source_eq_target_of_mapArrows_source_eq_target
    (hstab : IsPullback (stabilizerMap F).left (stabilizer G').hom (stabilizer G).hom
      F.mapObjects.left)
    {T : Scheme.{u}} (r : T ⟶ G'.arrows.left)
    (hr : (r ≫ F.mapArrows.left) ≫ G.source.left = (r ≫ F.mapArrows.left) ≫ G.target.left) :
    r ≫ G'.source.left = r ≫ G'.target.left := by
  have hw : stabilizerLift G (r ≫ F.mapArrows.left) hr ≫ (stabilizer G).hom =
      (r ≫ G'.target.left) ≫ F.mapObjects.left := by
    rw [stabilizerLift_comp_hom, hr, Category.assoc, F.map_target_left, ← Category.assoc]
  have key : hstab.lift (stabilizerLift G (r ≫ F.mapArrows.left) hr) (r ≫ G'.target.left) hw ≫
      stabilizerArrow G' = r := by
    refine htarget.hom_ext ?_ ?_
    · rw [Category.assoc, ← stabilizerMap_left_comp_stabilizerArrow, ← Category.assoc,
        hstab.lift_fst, stabilizerLift_comp_stabilizerArrow]
    · rw [Category.assoc, stabilizerArrow_comp_target, hstab.lift_snd]
  rw [← key, Category.assoc, Category.assoc, stabilizerArrow_comp_source,
    stabilizerArrow_comp_target]

end Stabilizer

namespace GroupoidScheme

/-! ### The stabilizer square of the induced morphism of base changes -/

section Induced

variable {S : Scheme.{u}} {G G' : GroupoidScheme S} {C₁ C'₁ : Type u} [CommRing C₁]
  [CommRing C'₁] [Algebra (invariantRing G) C₁] [Algebra (invariantRing G') C'₁]
  (F : GroupoidScheme.Hom G' G) (ψ : C₁ →+* C'₁)
  (hψ : ψ.comp (algebraMap (invariantRing G) C₁) =
    (algebraMap (invariantRing G') C'₁).comp (invariantRingMap F))
  (bc : AffineInvariantBaseChange G C₁) (bc' : AffineInvariantBaseChange G' C'₁)

/-- **An arrow of the base change of `G'` whose image in the base change of `G` has equal source
and target has equal source and target.**

Both halves of the cartesian object square of the base change of `G'` are checked: over
`Spec C'₁` because source and target of an arrow lie over the point the arrow lies over, and
over the object scheme of `G'` by
`AlgebraicGeometry.source_eq_target_of_mapArrows_source_eq_target`, whose hypothesis is the
assumption read through the two projections to the arrow scheme of `G`. -/
theorem baseChangeMapArrows_source_eq_target
    (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left)
    (hstab : IsPullback (stabilizerMap F).left (stabilizer G').hom (stabilizer G).hom
      F.mapObjects.left)
    {T : Scheme.{u}} (r : T ⟶ bc'.groupoid.arrows.left)
    (hr : (r ≫ baseChangeMapArrows F ψ hψ bc bc') ≫ bc.groupoid.source.left =
      (r ≫ baseChangeMapArrows F ψ hψ bc bc') ≫ bc.groupoid.target.left) :
    r ≫ bc'.groupoid.source.left = r ≫ bc'.groupoid.target.left := by
  have hG : ((r ≫ bc'.arrowsProjection) ≫ F.mapArrows.left) ≫ G.source.left =
      ((r ≫ bc'.arrowsProjection) ≫ F.mapArrows.left) ≫ G.target.left := by
    have h := congrArg (fun z => z ≫ bc.objectsProjection) hr
    simp only [Category.assoc,
      ← baseChangeMapArrows_comp_arrowsProjection_assoc F ψ hψ bc bc',
      bc.projection_source, bc.projection_target]
    simpa only [Category.assoc] using h
  have hkey := source_eq_target_of_mapArrows_source_eq_target F htarget hstab
    (r ≫ bc'.arrowsProjection) hG
  refine bc'.objects_isPullback.hom_ext ?_ ?_
  · simpa only [Category.assoc, ← bc'.projection_source, ← bc'.projection_target] using hkey
  · rw [Category.assoc, Category.assoc, Over.w bc'.groupoid.source, Over.w bc'.groupoid.target]

/-- **The stabilizer square of the morphism of base changes induced by a morphism of affine
groupoid schemes is cartesian** as soon as the target and stabilizer squares of the original
morphism are. This is the input the second conclusion of [Stacks Project, Tag 0DT9] needs at the
induced morphism. -/
theorem isPullback_stabilizerMap_baseChangeHom [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsAffine G'.objects.left] [IsAffine G'.arrows.left]
    (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left)
    (hstab : IsPullback (stabilizerMap F).left (stabilizer G').hom (stabilizer G).hom
      F.mapObjects.left) :
    IsPullback (stabilizerMap (baseChangeHom F ψ hψ bc bc')).left
      (stabilizer (bc'.groupoid.pushforward (Spec.map (CommRingCat.ofHom ψ)))).hom
      (stabilizer bc.groupoid).hom (baseChangeHom F ψ hψ bc bc').mapObjects.left :=
  isPullback_stabilizerMap (baseChangeHom F ψ hψ bc bc')
    (target_isPullback_mapArrows_baseChangeHom F ψ hψ bc bc' htarget)
    fun r hr => baseChangeMapArrows_source_eq_target F ψ hψ bc bc' htarget hstab r hr

end Induced

end GroupoidScheme

end AlgebraicGeometry

end

end
