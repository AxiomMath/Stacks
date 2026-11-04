module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Compose
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid

/-!
# Restricting twice, and restricting along the composite

Let `G` be a groupoid scheme, let `g : U' ⟶ U` be a morphism to its scheme of objects, let `R'`
be a groupoid scheme realizing the restriction `G|_{U'}` and let `g' : U'' ⟶ U'`.  Restricting
`R'` along `g'` and restricting `G` along the composite `g' ≫ g` produce isomorphic groupoid
schemes, by an isomorphism which is the identity on objects and compatible with the two
morphisms to `G`.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.Restriction.lift` builds a generalized point of the arrow
  scheme of a realization of a restriction from a source, a target and an ambient arrow.
* `AlgebraicGeometry.GroupoidScheme.iteratedRestrictionHom` is the comparison morphism from a
  realization of `(G|_{U'})|_{U''}` to a realization of `G|_{U''}`.

## Main results

* `AlgebraicGeometry.GroupoidScheme.Restriction.hom_ext`: a generalized point of the arrow
  scheme of a realization of a restriction is determined by its source, its target and its
  underlying ambient arrow.
* `AlgebraicGeometry.GroupoidScheme.isIso_iteratedRestrictionHom_mapObjects` and
  `AlgebraicGeometry.GroupoidScheme.isIso_iteratedRestrictionHom_mapArrows`: the comparison
  morphism is an isomorphism on objects and on arrows.

## Implementation notes

A realization of a restriction is an `AlgebraicGeometry.GroupoidScheme.Restriction`, whose arrow
scheme is required to be *equal* to the chosen iterated fibre product
`AlgebraicGeometry.restrictionArrows`.  Two realizations of restrictions taken along different
morphisms therefore have different arrow schemes, and the comparison between them is an
isomorphism and not an equality.  Everything below is phrased through the universal property of
the arrow scheme of a realization — a generalized point of it is built from, and is determined
by, a source, a target and an arrow of the ambient groupoid — so no step unfolds the fibre
product beyond `AlgebraicGeometry.GroupoidScheme.restrictionArrowsLift` itself.

## References

* [Stacks Project, Tag 02VB](https://stacks.math.columbia.edu/tag/02VB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} {H : Stacks.Groupoids.GroupoidScheme S}

/-! ### The universal property of the arrow scheme of a restriction -/

/-- The generalized point of `AlgebraicGeometry.restrictionArrows` with prescribed source,
target and underlying arrow of the ambient groupoid. -/
noncomputable def restrictionArrowsLift {U' T : Over S} (g : U' ⟶ H.objects) (s t : T ⟶ U')
    (a : T ⟶ H.arrows) (hs : s ≫ g = a ≫ H.source) (ht : t ≫ g = a ≫ H.target) :
    T ⟶ restrictionArrows H g :=
  pullback.lift (pullback.lift t a ht) (pullback.lift a s hs.symm)
    ((pullback.lift_snd _ _ _).trans (pullback.lift_fst _ _ _).symm)

/-- The source of `AlgebraicGeometry.GroupoidScheme.restrictionArrowsLift` is the prescribed
one. -/
@[simp]
theorem restrictionArrowsLift_source {U' T : Over S} (g : U' ⟶ H.objects) (s t : T ⟶ U')
    (a : T ⟶ H.arrows) (hs : s ≫ g = a ≫ H.source) (ht : t ≫ g = a ≫ H.target) :
    restrictionArrowsLift g s t a hs ht ≫ restrictionSource H g = s :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ pullback.snd H.source g) (pullback.lift_snd _ _ _)).trans
      (pullback.lift_snd _ _ _))

/-- The target of `AlgebraicGeometry.GroupoidScheme.restrictionArrowsLift` is the prescribed
one. -/
@[simp]
theorem restrictionArrowsLift_target {U' T : Over S} (g : U' ⟶ H.objects) (s t : T ⟶ U')
    (a : T ⟶ H.arrows) (hs : s ≫ g = a ≫ H.source) (ht : t ≫ g = a ≫ H.target) :
    restrictionArrowsLift g s t a hs ht ≫ restrictionTarget H g = t :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ pullback.fst g H.target) (pullback.lift_fst _ _ _)).trans
      (pullback.lift_fst _ _ _))

/-- The underlying ambient arrow of `AlgebraicGeometry.GroupoidScheme.restrictionArrowsLift` is
the prescribed one. -/
@[simp]
theorem restrictionArrowsLift_arrow {U' T : Over S} (g : U' ⟶ H.objects) (s t : T ⟶ U')
    (a : T ⟶ H.arrows) (hs : s ≫ g = a ≫ H.source) (ht : t ≫ g = a ≫ H.target) :
    restrictionArrowsLift g s t a hs ht ≫ restrictionArrowsToArrows H g = a :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ pullback.snd g H.target) (pullback.lift_fst _ _ _)).trans
      (pullback.lift_snd _ _ _))

namespace Restriction

variable {U' : Over S} {g : U' ⟶ H.objects}

/-- The generalized point of the arrow scheme of a groupoid scheme realizing a restriction,
with prescribed source, target and underlying arrow of the ambient groupoid. -/
noncomputable def lift (R : Restriction H g) {T : Over S} (s t : T ⟶ R.groupoid.objects)
    (a : T ⟶ H.arrows) (hs : s ≫ R.hom.mapObjects = a ≫ H.source)
    (ht : t ≫ R.hom.mapObjects = a ≫ H.target) : T ⟶ R.groupoid.arrows :=
  restrictionArrowsLift g (s ≫ eqToHom R.objects_eq) (t ≫ eqToHom R.objects_eq) a
      (by rw [Category.assoc, ← R.mapObjects_eq]; exact hs)
      (by rw [Category.assoc, ← R.mapObjects_eq]; exact ht) ≫
    eqToHom R.arrows_eq.symm

/-- The source of `AlgebraicGeometry.GroupoidScheme.Restriction.lift` is the prescribed one. -/
@[simp]
theorem lift_source (R : Restriction H g) {T : Over S} (s t : T ⟶ R.groupoid.objects)
    (a : T ⟶ H.arrows) (hs : s ≫ R.hom.mapObjects = a ≫ H.source)
    (ht : t ≫ R.hom.mapObjects = a ≫ H.target) :
    R.lift s t a hs ht ≫ R.groupoid.source = s := by
  simp [lift, R.source_eq, reassoc_of% restrictionArrowsLift_source]

/-- The target of `AlgebraicGeometry.GroupoidScheme.Restriction.lift` is the prescribed one. -/
@[simp]
theorem lift_target (R : Restriction H g) {T : Over S} (s t : T ⟶ R.groupoid.objects)
    (a : T ⟶ H.arrows) (hs : s ≫ R.hom.mapObjects = a ≫ H.source)
    (ht : t ≫ R.hom.mapObjects = a ≫ H.target) :
    R.lift s t a hs ht ≫ R.groupoid.target = t := by
  simp [lift, R.target_eq, reassoc_of% restrictionArrowsLift_target]

/-- The underlying ambient arrow of `AlgebraicGeometry.GroupoidScheme.Restriction.lift` is the
prescribed one. -/
@[simp]
theorem lift_arrow (R : Restriction H g) {T : Over S} (s t : T ⟶ R.groupoid.objects)
    (a : T ⟶ H.arrows) (hs : s ≫ R.hom.mapObjects = a ≫ H.source)
    (ht : t ≫ R.hom.mapObjects = a ≫ H.target) :
    R.lift s t a hs ht ≫ R.hom.mapArrows = a := by
  rw [lift, R.mapArrows_eq, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, restrictionArrowsLift_arrow]

/-- A generalized point of the arrow scheme of a groupoid scheme realizing a restriction is
determined by its source, its target and its underlying arrow of the ambient groupoid. -/
theorem hom_ext (R : Restriction H g) {T : Over S} {f h : T ⟶ R.groupoid.arrows}
    (hs : f ≫ R.groupoid.source = h ≫ R.groupoid.source)
    (ht : f ≫ R.groupoid.target = h ≫ R.groupoid.target)
    (ha : f ≫ R.hom.mapArrows = h ≫ R.hom.mapArrows) : f = h := by
  have key : f ≫ eqToHom R.arrows_eq = h ≫ eqToHom R.arrows_eq := by
    refine AlgebraicGeometry.GroupoidScheme.restriction_hom_ext H g _ _ ?_ ?_ ?_
    · have h1 := hs
      rw [R.source_eq] at h1
      simp only [← Category.assoc] at h1
      exact (cancel_mono (eqToHom R.objects_eq.symm)).1 h1
    · have h1 := ht
      rw [R.target_eq] at h1
      simp only [← Category.assoc] at h1
      exact (cancel_mono (eqToHom R.objects_eq.symm)).1 h1
    · have h1 := ha
      rw [R.mapArrows_eq] at h1
      simp only [← Category.assoc] at h1
      exact h1
  exact (cancel_mono (eqToHom R.arrows_eq)).1 key

end Restriction

/-! ### Comparing an iterated restriction with the restriction along the composite -/

variable {U' U'' : Over S} {g : U' ⟶ H.objects} (R' : Restriction H g)
  {j : U'' ⟶ R'.groupoid.objects} (R'' : Restriction R'.groupoid j)
  (R''' : Restriction H (j ≫ R'.hom.mapObjects))

/-- A realization of `(G|_{U'})|_{U''}` and a realization of `G|_{U''}` have the same scheme of
objects, both being `U''`. -/
theorem iteratedRestriction_objects_eq : R''.groupoid.objects = R'''.groupoid.objects :=
  R''.objects_eq.trans R'''.objects_eq.symm

@[simp]
theorem eqToHom_iteratedRestriction_objects :
    eqToHom (iteratedRestriction_objects_eq R' R'' R''') ≫ eqToHom R'''.objects_eq =
      eqToHom R''.objects_eq := by
  rw [eqToHom_trans]

@[simp]
theorem eqToHom_iteratedRestriction_objects_symm :
    eqToHom (iteratedRestriction_objects_eq R' R'' R''').symm ≫ eqToHom R''.objects_eq =
      eqToHom R'''.objects_eq := by
  rw [eqToHom_trans]

/-- The two realizations have the same map to the scheme of objects of the ambient groupoid. -/
theorem iteratedRestriction_mapObjects :
    eqToHom (iteratedRestriction_objects_eq R' R'' R''') ≫ R'''.hom.mapObjects =
      R''.hom.mapObjects ≫ R'.hom.mapObjects := by
  rw [R'''.mapObjects_eq, R''.mapObjects_eq]
  simp only [Category.assoc]
  rw [eqToHom_trans_assoc]

/-- The source of an arrow of a realization of `(G|_{U'})|_{U''}`, read in the ambient
groupoid. -/
theorem iteratedRestriction_source_condition :
    (R''.groupoid.source ≫ eqToHom (iteratedRestriction_objects_eq R' R'' R''')) ≫
        R'''.hom.mapObjects =
      (R''.hom.mapArrows ≫ R'.hom.mapArrows) ≫ H.source := by
  simp only [Category.assoc, iteratedRestriction_mapObjects]
  rw [← Category.assoc, ← R''.hom.map_source, Category.assoc, ← R'.hom.map_source]

/-- The target of an arrow of a realization of `(G|_{U'})|_{U''}`, read in the ambient
groupoid. -/
theorem iteratedRestriction_target_condition :
    (R''.groupoid.target ≫ eqToHom (iteratedRestriction_objects_eq R' R'' R''')) ≫
        R'''.hom.mapObjects =
      (R''.hom.mapArrows ≫ R'.hom.mapArrows) ≫ H.target := by
  simp only [Category.assoc, iteratedRestriction_mapObjects]
  rw [← Category.assoc, ← R''.hom.map_target, Category.assoc, ← R'.hom.map_target]

/-- The comparison morphism on arrow schemes, from a realization of `(G|_{U'})|_{U''}` to a
realization of `G|_{U''}`. -/
noncomputable def iteratedRestrictionArrows : R''.groupoid.arrows ⟶ R'''.groupoid.arrows :=
  R'''.lift (R''.groupoid.source ≫ eqToHom (iteratedRestriction_objects_eq R' R'' R'''))
    (R''.groupoid.target ≫ eqToHom (iteratedRestriction_objects_eq R' R'' R'''))
    (R''.hom.mapArrows ≫ R'.hom.mapArrows)
    (iteratedRestriction_source_condition R' R'' R''')
    (iteratedRestriction_target_condition R' R'' R''')

@[simp]
theorem iteratedRestrictionArrows_source :
    iteratedRestrictionArrows R' R'' R''' ≫ R'''.groupoid.source =
      R''.groupoid.source ≫ eqToHom (iteratedRestriction_objects_eq R' R'' R''') :=
  R'''.lift_source _ _ _ _ _

@[simp]
theorem iteratedRestrictionArrows_target :
    iteratedRestrictionArrows R' R'' R''' ≫ R'''.groupoid.target =
      R''.groupoid.target ≫ eqToHom (iteratedRestriction_objects_eq R' R'' R''') :=
  R'''.lift_target _ _ _ _ _

@[simp]
theorem iteratedRestrictionArrows_arrow :
    iteratedRestrictionArrows R' R'' R''' ≫ R'''.hom.mapArrows =
      R''.hom.mapArrows ≫ R'.hom.mapArrows :=
  R'''.lift_arrow _ _ _ _ _

/-- The arrow of the first restriction underlying an arrow of a realization of `G|_{U''}`. -/
noncomputable def iteratedRestrictionAmbientArrow :
    R'''.groupoid.arrows ⟶ R'.groupoid.arrows :=
  R'.lift (R'''.groupoid.source ≫ eqToHom R'''.objects_eq ≫ j)
    (R'''.groupoid.target ≫ eqToHom R'''.objects_eq ≫ j) R'''.hom.mapArrows
    (by simp only [Category.assoc]; rw [← R'''.mapObjects_eq, ← R'''.hom.map_source])
    (by simp only [Category.assoc]; rw [← R'''.mapObjects_eq, ← R'''.hom.map_target])

@[simp]
theorem iteratedRestrictionAmbientArrow_source :
    iteratedRestrictionAmbientArrow R' R''' ≫ R'.groupoid.source =
      R'''.groupoid.source ≫ eqToHom R'''.objects_eq ≫ j :=
  R'.lift_source _ _ _ _ _

@[simp]
theorem iteratedRestrictionAmbientArrow_target :
    iteratedRestrictionAmbientArrow R' R''' ≫ R'.groupoid.target =
      R'''.groupoid.target ≫ eqToHom R'''.objects_eq ≫ j :=
  R'.lift_target _ _ _ _ _

@[simp]
theorem iteratedRestrictionAmbientArrow_arrow :
    iteratedRestrictionAmbientArrow R' R''' ≫ R'.hom.mapArrows = R'''.hom.mapArrows :=
  R'.lift_arrow _ _ _ _ _

/-- The comparison morphism on arrow schemes, from a realization of `G|_{U''}` to a realization
of `(G|_{U'})|_{U''}`. -/
noncomputable def iteratedRestrictionArrowsInv :
    R'''.groupoid.arrows ⟶ R''.groupoid.arrows :=
  R''.lift
    (R'''.groupoid.source ≫ eqToHom (iteratedRestriction_objects_eq R' R'' R''').symm)
    (R'''.groupoid.target ≫ eqToHom (iteratedRestriction_objects_eq R' R'' R''').symm)
    (iteratedRestrictionAmbientArrow R' R''')
    (by
      rw [R''.mapObjects_eq, iteratedRestrictionAmbientArrow_source]
      simp only [Category.assoc]
      rw [eqToHom_trans_assoc])
    (by
      rw [R''.mapObjects_eq, iteratedRestrictionAmbientArrow_target]
      simp only [Category.assoc]
      rw [eqToHom_trans_assoc])

@[simp]
theorem iteratedRestrictionArrowsInv_source :
    iteratedRestrictionArrowsInv R' R'' R''' ≫ R''.groupoid.source =
      R'''.groupoid.source ≫ eqToHom (iteratedRestriction_objects_eq R' R'' R''').symm :=
  R''.lift_source _ _ _ _ _

@[simp]
theorem iteratedRestrictionArrowsInv_target :
    iteratedRestrictionArrowsInv R' R'' R''' ≫ R''.groupoid.target =
      R'''.groupoid.target ≫ eqToHom (iteratedRestriction_objects_eq R' R'' R''').symm :=
  R''.lift_target _ _ _ _ _

@[simp]
theorem iteratedRestrictionArrowsInv_arrow :
    iteratedRestrictionArrowsInv R' R'' R''' ≫ R''.hom.mapArrows =
      iteratedRestrictionAmbientArrow R' R''' :=
  R''.lift_arrow _ _ _ _ _

/-- The comparison morphism carries the arrow of the first restriction underlying an arrow of a
realization of `(G|_{U'})|_{U''}` to the one underlying its image. -/
theorem iteratedRestrictionArrows_comp_ambientArrow :
    iteratedRestrictionArrows R' R'' R''' ≫ iteratedRestrictionAmbientArrow R' R''' =
      R''.hom.mapArrows := by
  refine R'.hom_ext ?_ ?_ ?_
  · simp [reassoc_of% iteratedRestrictionArrows_source, R''.hom.map_source,
      R''.mapObjects_eq]
  · simp [reassoc_of% iteratedRestrictionArrows_target, R''.hom.map_target,
      R''.mapObjects_eq]
  · rw [Category.assoc, iteratedRestrictionAmbientArrow_arrow,
      iteratedRestrictionArrows_arrow]

theorem iteratedRestrictionArrows_comp_inv :
    iteratedRestrictionArrows R' R'' R''' ≫ iteratedRestrictionArrowsInv R' R'' R''' =
      𝟙 R''.groupoid.arrows := by
  refine R''.hom_ext ?_ ?_ ?_
  · simp [reassoc_of% iteratedRestrictionArrows_source]
  · simp [reassoc_of% iteratedRestrictionArrows_target]
  · rw [Category.assoc, iteratedRestrictionArrowsInv_arrow,
      iteratedRestrictionArrows_comp_ambientArrow, Category.id_comp]

theorem iteratedRestrictionArrowsInv_comp :
    iteratedRestrictionArrowsInv R' R'' R''' ≫ iteratedRestrictionArrows R' R'' R''' =
      𝟙 R'''.groupoid.arrows := by
  refine R'''.hom_ext ?_ ?_ ?_
  · simp [reassoc_of% iteratedRestrictionArrowsInv_source]
  · simp [reassoc_of% iteratedRestrictionArrowsInv_target]
  · rw [Category.assoc, iteratedRestrictionArrows_arrow, ← Category.assoc,
      iteratedRestrictionArrowsInv_arrow, iteratedRestrictionAmbientArrow_arrow,
      Category.id_comp]

/-- The comparison morphism carries the identity arrow to the identity arrow, read through the
two morphisms to the ambient groupoid. -/
theorem iteratedRestriction_identity :
    eqToHom (iteratedRestriction_objects_eq R' R'' R''') ≫ R'''.groupoid.identity ≫
        R'''.hom.mapArrows =
      R''.groupoid.identity ≫ R''.hom.mapArrows ≫ R'.hom.mapArrows := by
  conv_lhs =>
    rw [← R'''.hom.map_identity, ← Category.assoc, iteratedRestriction_mapObjects,
      Category.assoc, R'.hom.map_identity, ← Category.assoc, R''.hom.map_identity,
      Category.assoc]

instance isIso_iteratedRestrictionArrows : IsIso (iteratedRestrictionArrows R' R'' R''') :=
  ⟨iteratedRestrictionArrowsInv R' R'' R''',
    iteratedRestrictionArrows_comp_inv R' R'' R''',
    iteratedRestrictionArrowsInv_comp R' R'' R'''⟩

/-- The comparison morphism of groupoid schemes from a realization of `(G|_{U'})|_{U''}` to a
realization of `G|_{U''}`.  It is the identity on objects, and on arrows it preserves the
underlying arrow of the ambient groupoid. -/
noncomputable def iteratedRestrictionHom :
    Stacks.Groupoids.GroupoidScheme.Hom R''.groupoid R'''.groupoid where
  mapObjects := eqToHom (iteratedRestriction_objects_eq R' R'' R''')
  mapArrows := iteratedRestrictionArrows R' R'' R'''
  map_source := iteratedRestrictionArrows_source R' R'' R'''
  map_target := iteratedRestrictionArrows_target R' R'' R'''
  map_identity := by
    refine R'''.hom_ext ?_ ?_ ?_
    · rw [Category.assoc, R'''.groupoid.source_identity, Category.comp_id, Category.assoc,
        iteratedRestrictionArrows_source, ← Category.assoc, R''.groupoid.source_identity,
        Category.id_comp]
    · rw [Category.assoc, R'''.groupoid.target_identity, Category.comp_id, Category.assoc,
        iteratedRestrictionArrows_target, ← Category.assoc, R''.groupoid.target_identity,
        Category.id_comp]
    · rw [Category.assoc, Category.assoc, iteratedRestrictionArrows_arrow]
      exact iteratedRestriction_identity R' R'' R'''
  map_comp := by
    intro T f h w w'
    have hw₂ : (f ≫ R''.hom.mapArrows) ≫ R'.groupoid.source =
        (h ≫ R''.hom.mapArrows) ≫ R'.groupoid.target := by
      simp only [Category.assoc, R''.hom.map_source, R''.hom.map_target]
      simp only [← Category.assoc]
      rw [w]
    have hw₃ : ((f ≫ R''.hom.mapArrows) ≫ R'.hom.mapArrows) ≫ H.source =
        ((h ≫ R''.hom.mapArrows) ≫ R'.hom.mapArrows) ≫ H.target := by
      simp only [Category.assoc, R'.hom.map_source, R'.hom.map_target]
      simp only [← Category.assoc]
      rw [hw₂]
    have harrow : ∀ k : T ⟶ R''.groupoid.arrows,
        (k ≫ iteratedRestrictionArrows R' R'' R''') ≫ R'''.hom.mapArrows =
          (k ≫ R''.hom.mapArrows) ≫ R'.hom.mapArrows := fun k => by
      rw [Category.assoc, iteratedRestrictionArrows_arrow, Category.assoc]
    have hw₄ : ((f ≫ iteratedRestrictionArrows R' R'' R''') ≫ R'''.hom.mapArrows) ≫ H.source =
        ((h ≫ iteratedRestrictionArrows R' R'' R''') ≫ R'''.hom.mapArrows) ≫ H.target := by
      rw [harrow f, harrow h]
      exact hw₃
    refine R'''.hom_ext ?_ ?_ ?_
    · rw [groupoidCompose_source]
      simp only [Category.assoc, iteratedRestrictionArrows_source]
      simp only [← Category.assoc]
      rw [groupoidCompose_source]
    · rw [groupoidCompose_target]
      simp only [Category.assoc, iteratedRestrictionArrows_target]
      simp only [← Category.assoc]
      rw [groupoidCompose_target]
    · rw [Category.assoc, iteratedRestrictionArrows_arrow, ← Category.assoc,
        R''.hom.map_comp T f h w hw₂, R'.hom.map_comp T _ _ hw₂ hw₃,
        R'''.hom.map_comp T _ _ w' hw₄]
      exact groupoidCompose_arrow_eq _ _ _ _ hw₃ hw₄ (harrow f).symm (harrow h).symm

@[simp]
theorem iteratedRestrictionHom_mapObjects :
    (iteratedRestrictionHom R' R'' R''').mapObjects =
      eqToHom (iteratedRestriction_objects_eq R' R'' R''') :=
  rfl

@[simp]
theorem iteratedRestrictionHom_mapArrows :
    (iteratedRestrictionHom R' R'' R''').mapArrows = iteratedRestrictionArrows R' R'' R''' :=
  rfl

instance isIso_iteratedRestrictionHom_mapObjects :
    IsIso (iteratedRestrictionHom R' R'' R''').mapObjects :=
  inferInstanceAs (IsIso (eqToHom (iteratedRestriction_objects_eq R' R'' R''')))

instance isIso_iteratedRestrictionHom_mapArrows :
    IsIso (iteratedRestrictionHom R' R'' R''').mapArrows :=
  inferInstanceAs (IsIso (iteratedRestrictionArrows R' R'' R'''))

end AlgebraicGeometry.GroupoidScheme

end
