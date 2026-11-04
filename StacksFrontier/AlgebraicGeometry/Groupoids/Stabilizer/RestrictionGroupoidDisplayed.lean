module

public import Mathlib.CategoryTheory.InducedCategory
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.GroupoidInverse
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeDerealization
public import StacksCore.Tactic.StacksAttribute

/-!
# The restriction of a groupoid scheme, built from the displayed data

Let `(U, R, s, t, c)` be a groupoid scheme over `S` and `g : U' ⟶ U` a morphism.  Stacks
Lemma 02VB forms the iterated fibre product
`R' = (U' ×_{g, U, t} R) ×_R (R ×_{s, U, g} U')`, with `s'` and `t'` the two projections to
`U'`, equips it with a canonical composition law `c'`, and asserts that `(U', R', s', t', c')`
is a groupoid scheme, that `g` and the projection `R' ⟶ R` form a morphism of groupoid schemes,
and that on `T`-valued points this morphism is the restriction of the groupoid
`(U(T), R(T), s, t, c)` along `U'(T) ⟶ U(T)`.

This file builds that groupoid scheme out of exactly the displayed data:

* its objects are `U'`, its arrows are `AlgebraicGeometry.restrictionArrows G g`, which is the
  iterated fibre product above, and its source and target are
  `AlgebraicGeometry.restrictionSource` and `AlgebraicGeometry.restrictionTarget`, the two
  displayed projections;
* its composition, identity and inverse are the scheme-level morphisms
  `Stacks.Groupoids.GroupoidScheme.restrictionComposition`,
  `Stacks.Groupoids.GroupoidScheme.restrictionIdentity` and
  `Stacks.Groupoids.GroupoidScheme.restrictionInverse`, each of which is the unique morphism
  with its source, its target and its underlying arrow of `G`.

The restriction of a usual groupoid `C` along a map of sets `Ob' ⟶ Ob` (the groupoid whose
arrows `x' ⟶ y'` are the arrows `g x' ⟶ g y'` of `C`) is Mathlib's `InducedCategory`, with
the canonical functor `inducedFunctor`.  The pointwise assertion of 02VB is stated as an
isomorphism of categories between the groupoid of `T`-points of the restriction and the induced
category, which is the identity on objects and carries the canonical functor to the evaluation
of the morphism of groupoid schemes.

Finally, the realization `AlgebraicGeometry.GroupoidScheme.restrict` of the structure
`AlgebraicGeometry.GroupoidScheme.Restriction` is identified with this construction: the type of
restrictions is a subsingleton.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.restrictGroupoid`: the groupoid scheme `(U', R', s', t', c')`.
* `AlgebraicGeometry.GroupoidScheme.restrictGroupoidHom`: its morphism to `(U, R, s, t, c)`.
* `AlgebraicGeometry.GroupoidScheme.restrictGroupoidEvaluationFunctor` and
  `AlgebraicGeometry.GroupoidScheme.restrictGroupoidEvaluationInverse`: the mutually inverse
  identifications of the `T`-points of the restriction with the induced groupoid.

## Main results

* `AlgebraicGeometry.GroupoidScheme.restrictGroupoid_isRestriction`: Stacks Lemma 02VB.
* `AlgebraicGeometry.GroupoidScheme.restrict_groupoid`: the realization `restrict` has the
  groupoid scheme `restrictGroupoid` as its groupoid.

## References

* [Stacks Project, Tag 02VB](https://stacks.math.columbia.edu/tag/02VB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}}

/-- The condition making two generalized arrows of a restriction composable in `G`: the
source of the first underlying arrow is the target of the second. -/
theorem restriction_compose_condition (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) {T : Over S} (f h : T ⟶ AlgebraicGeometry.restrictionArrows G p)
    (w : f ≫ AlgebraicGeometry.restrictionSource G p =
      h ≫ AlgebraicGeometry.restrictionTarget G p) :
    (f ≫ AlgebraicGeometry.restrictionArrowsToArrows G p) ≫ G.source =
      (h ≫ AlgebraicGeometry.restrictionArrowsToArrows G p) ≫ G.target := by
  rw [Category.assoc, Category.assoc,
    ← AlgebraicGeometry.GroupoidScheme.restriction_condition,
    AlgebraicGeometry.GroupoidScheme.restriction_condition', ← Category.assoc, w,
    Category.assoc]

/-- **The arrow of `G` underlying the composite of two composable generalized arrows of a
restriction is their composite in `G`.** -/
theorem restrictionComposition_lift_comp_arrowsToArrows (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) {T : Over S} (f h : T ⟶ AlgebraicGeometry.restrictionArrows G p)
    (w : f ≫ AlgebraicGeometry.restrictionSource G p =
      h ≫ AlgebraicGeometry.restrictionTarget G p) :
    (pullback.lift f h w ≫ restrictionComposition G p) ≫
        AlgebraicGeometry.restrictionArrowsToArrows G p =
      G.compose (f ≫ AlgebraicGeometry.restrictionArrowsToArrows G p)
        (h ≫ AlgebraicGeometry.restrictionArrowsToArrows G p)
        (restriction_compose_condition G p f h w) := by
  rw [Category.assoc, restrictionComposition_comp_arrowsToArrows, restrictionAmbientComp,
    compose, ← Category.assoc]
  congr 1
  apply pullback.hom_ext <;>
    simp [restrictionAmbientLift_comp_fst, restrictionAmbientLift_comp_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc, pullback.lift_fst, pullback.lift_snd]

/-- The ambient lift of the composable pairs of a restriction is the map induced by the
projection to the arrows of `G` on the schemes of composable pairs. -/
theorem restrictionAmbientLift_eq_map (G : GroupoidScheme S) {X : Over S}
    (p : X ⟶ G.objects) (h₁ : AlgebraicGeometry.restrictionArrowsToArrows G p ≫ G.source =
      AlgebraicGeometry.restrictionSource G p ≫ p)
    (h₂ : AlgebraicGeometry.restrictionArrowsToArrows G p ≫ G.target =
      AlgebraicGeometry.restrictionTarget G p ≫ p) :
    pullback.map _ _ _ _ (AlgebraicGeometry.restrictionArrowsToArrows G p)
        (AlgebraicGeometry.restrictionArrowsToArrows G p) p (by rw [h₁]) (by rw [h₂]) =
      restrictionAmbientLift G p :=
  pullback.hom_ext ((pullback.lift_fst _ _ _).trans (restrictionAmbientLift_comp_fst G p).symm)
    ((pullback.lift_snd _ _ _).trans (restrictionAmbientLift_comp_snd G p).symm)

end Stacks.Groupoids.GroupoidScheme

namespace AlgebraicGeometry.GroupoidScheme

attribute [local simp] pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc

section Restrict

variable {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) {U' : Over S}
  (g : U' ⟶ G.objects)

/-- The identity at the target of a generalized arrow of the restriction lies over the identity
at the target of its underlying arrow of `G`. -/
theorem restrictionTarget_restrictionIdentity_arrowsToArrows {T : Over S}
    (f : T ⟶ restrictionArrows G g) :
    (f ≫ restrictionTarget G g ≫ G.restrictionIdentity g) ≫ restrictionArrowsToArrows G g =
      (f ≫ restrictionArrowsToArrows G g) ≫ G.target ≫ G.identity := by
  simpa only [Category.assoc, G.restrictionIdentity_comp_arrowsToArrows g] using
    congrArg (fun z => f ≫ z ≫ G.identity) (restriction_condition' G g).symm

/-- The identity at the source of a generalized arrow of the restriction lies over the identity
at the source of its underlying arrow of `G`. -/
theorem restrictionSource_restrictionIdentity_arrowsToArrows {T : Over S}
    (f : T ⟶ restrictionArrows G g) :
    (f ≫ restrictionSource G g ≫ G.restrictionIdentity g) ≫ restrictionArrowsToArrows G g =
      (f ≫ restrictionArrowsToArrows G g) ≫ G.source ≫ G.identity := by
  simpa only [Category.assoc, G.restrictionIdentity_comp_arrowsToArrows g] using
    congrArg (fun z => f ≫ z ≫ G.identity) (restriction_condition G g)

/-- **The restriction `(U', R', s', t', c')` of a groupoid scheme `G` along `g : U' ⟶ U`.**
Its arrows are the iterated fibre product `R' = (U' ×_{g, U, t} R) ×_R (R ×_{s, U, g} U')`,
its source and target are the two displayed projections to `U'`, and its composition, identity
and inverse are `Stacks.Groupoids.GroupoidScheme.restrictionComposition`,
`Stacks.Groupoids.GroupoidScheme.restrictionIdentity` and
`Stacks.Groupoids.GroupoidScheme.restrictionInverse`.  This is the groupoid scheme of Stacks
Lemma 02VB. -/
noncomputable def restrictGroupoid : Stacks.Groupoids.GroupoidScheme S where
  objects := U'
  arrows := restrictionArrows G g
  source := restrictionSource G g
  target := restrictionTarget G g
  comp := G.restrictionComposition g
  identity := G.restrictionIdentity g
  inverse := G.restrictionInverse g
  source_identity := G.restrictionIdentity_comp_source g
  target_identity := G.restrictionIdentity_comp_target g
  source_inverse := G.restrictionInverse_comp_source g
  target_inverse := G.restrictionInverse_comp_target g
  source_comp := G.restrictionComposition_comp_source g
  target_comp := G.restrictionComposition_comp_target g
  left_identity := by
    intro T f w
    apply restriction_hom_ext G g
    · simp [G.restrictionComposition_comp_source g]
    · simp [G.restrictionComposition_comp_target g, G.restrictionIdentity_comp_target g]
    · have wG : ((f ≫ restrictionArrowsToArrows G g) ≫ G.target ≫ G.identity) ≫ G.source =
          f ≫ restrictionArrowsToArrows G g ≫ G.target := by
        simp [G.source_identity]
      calc
        (pullback.lift (f ≫ restrictionTarget G g ≫ G.restrictionIdentity g) f w ≫
              G.restrictionComposition g) ≫ restrictionArrowsToArrows G g =
            G.compose ((f ≫ restrictionTarget G g ≫ G.restrictionIdentity g) ≫
              restrictionArrowsToArrows G g) (f ≫ restrictionArrowsToArrows G g) _ :=
          G.restrictionComposition_lift_comp_arrowsToArrows g
            (f ≫ restrictionTarget G g ≫ G.restrictionIdentity g) f w
        _ = f ≫ restrictionArrowsToArrows G g := by
          simpa only [Stacks.Groupoids.GroupoidScheme.compose,
            restrictionTarget_restrictionIdentity_arrowsToArrows G g f] using
            G.left_identity T (f ≫ restrictionArrowsToArrows G g) wG
  right_identity := by
    intro T f w
    apply restriction_hom_ext G g
    · simp [G.restrictionComposition_comp_source g, G.restrictionIdentity_comp_source g]
    · simp [G.restrictionComposition_comp_target g]
    · have wG : f ≫ restrictionArrowsToArrows G g ≫ G.source =
          (f ≫ restrictionArrowsToArrows G g ≫ G.source ≫ G.identity) ≫ G.target := by
        simp [G.target_identity]
      calc
        (pullback.lift f (f ≫ restrictionSource G g ≫ G.restrictionIdentity g) w ≫
              G.restrictionComposition g) ≫ restrictionArrowsToArrows G g =
            G.compose (f ≫ restrictionArrowsToArrows G g)
              ((f ≫ restrictionSource G g ≫ G.restrictionIdentity g) ≫
                restrictionArrowsToArrows G g) _ :=
          G.restrictionComposition_lift_comp_arrowsToArrows g f
            (f ≫ restrictionSource G g ≫ G.restrictionIdentity g) w
        _ = f ≫ restrictionArrowsToArrows G g := by
          simpa only [Stacks.Groupoids.GroupoidScheme.compose,
            restrictionSource_restrictionIdentity_arrowsToArrows G g f] using
            G.right_identity T (f ≫ restrictionArrowsToArrows G g) wG
  left_inverse := by
    intro T f w
    apply restriction_hom_ext G g
    · simp [G.restrictionComposition_comp_source g, G.restrictionIdentity_comp_source g]
    · simp [G.restrictionComposition_comp_target g, G.restrictionInverse_comp_target g,
        G.restrictionIdentity_comp_target g]
    · have wG : ((f ≫ restrictionArrowsToArrows G g) ≫ G.inverse) ≫ G.source =
          (f ≫ restrictionArrowsToArrows G g) ≫ G.target := by
        rw [Category.assoc, G.source_inverse]
      calc
        (pullback.lift (f ≫ G.restrictionInverse g) f w ≫ G.restrictionComposition g) ≫
              restrictionArrowsToArrows G g =
            G.compose ((f ≫ G.restrictionInverse g) ≫ restrictionArrowsToArrows G g)
              (f ≫ restrictionArrowsToArrows G g) _ :=
          G.restrictionComposition_lift_comp_arrowsToArrows g (f ≫ G.restrictionInverse g) f w
        _ = G.compose ((f ≫ restrictionArrowsToArrows G g) ≫ G.inverse)
            (f ≫ restrictionArrowsToArrows G g) wG := by
          congr 1
          simp [G.restrictionInverse_comp_arrowsToArrows g]
        _ = f ≫ restrictionArrowsToArrows G g ≫ G.source ≫ G.identity := by
          simpa [Stacks.Groupoids.GroupoidScheme.compose] using
            G.left_inverse T (f ≫ restrictionArrowsToArrows G g) wG
        _ = (f ≫ restrictionSource G g ≫ G.restrictionIdentity g) ≫
            restrictionArrowsToArrows G g :=
          (restrictionSource_restrictionIdentity_arrowsToArrows G g f).symm
  right_inverse := by
    intro T f w
    apply restriction_hom_ext G g
    · simp [G.restrictionComposition_comp_source g, G.restrictionInverse_comp_source g,
        G.restrictionIdentity_comp_source g]
    · simp [G.restrictionComposition_comp_target g, G.restrictionIdentity_comp_target g]
    · have wG : (f ≫ restrictionArrowsToArrows G g) ≫ G.source =
          ((f ≫ restrictionArrowsToArrows G g) ≫ G.inverse) ≫ G.target := by
        rw [Category.assoc (f ≫ _), G.target_inverse]
      calc
        (pullback.lift f (f ≫ G.restrictionInverse g) w ≫ G.restrictionComposition g) ≫
              restrictionArrowsToArrows G g =
            G.compose (f ≫ restrictionArrowsToArrows G g)
              ((f ≫ G.restrictionInverse g) ≫ restrictionArrowsToArrows G g) _ :=
          G.restrictionComposition_lift_comp_arrowsToArrows g f (f ≫ G.restrictionInverse g) w
        _ = G.compose (f ≫ restrictionArrowsToArrows G g)
            ((f ≫ restrictionArrowsToArrows G g) ≫ G.inverse) wG := by
          congr 1
          simp [G.restrictionInverse_comp_arrowsToArrows g]
        _ = f ≫ restrictionArrowsToArrows G g ≫ G.target ≫ G.identity := by
          simpa [Stacks.Groupoids.GroupoidScheme.compose] using
            G.right_inverse T (f ≫ restrictionArrowsToArrows G g) wG
        _ = (f ≫ restrictionTarget G g ≫ G.restrictionIdentity g) ≫
            restrictionArrowsToArrows G g :=
          (restrictionTarget_restrictionIdentity_arrowsToArrows G g f).symm
  assoc := by
    intro T f h k w₁ w₂ w₃ w₄
    apply restriction_hom_ext G g
    · simp [G.restrictionComposition_comp_source g]
    · simp [G.restrictionComposition_comp_target g]
    · have wfg := G.restriction_compose_condition g f h w₁
      have wgh := G.restriction_compose_condition g h k w₂
      have w₁G : (G.compose (f ≫ restrictionArrowsToArrows G g)
            (h ≫ restrictionArrowsToArrows G g) wfg) ≫ G.source =
          (k ≫ restrictionArrowsToArrows G g) ≫ G.target := by
        simpa [Stacks.Groupoids.GroupoidScheme.compose, G.source_comp] using wgh
      have w₂G : (f ≫ restrictionArrowsToArrows G g) ≫ G.source =
          (G.compose (h ≫ restrictionArrowsToArrows G g)
            (k ≫ restrictionArrowsToArrows G g) wgh) ≫ G.target := by
        simpa [Stacks.Groupoids.GroupoidScheme.compose, G.target_comp] using wfg
      simpa only [Stacks.Groupoids.GroupoidScheme.restrictionComposition_lift_comp_arrowsToArrows,
        Stacks.Groupoids.GroupoidScheme.compose] using
        G.assoc T (f ≫ restrictionArrowsToArrows G g) (h ≫ restrictionArrowsToArrows G g)
          (k ≫ restrictionArrowsToArrows G g) wfg wgh w₁G w₂G

/-- **The canonical morphism of groupoid schemes from the restriction of `G` along `g` to
`G`**: it is `g` on objects and the displayed projection `R' ⟶ R` on arrows. -/
noncomputable def restrictGroupoidHom :
    Stacks.Groupoids.GroupoidScheme.Hom (restrictGroupoid G g) G where
  mapObjects := g
  mapArrows := restrictionArrowsToArrows G g
  map_source := (restriction_condition G g).symm
  map_target := restriction_condition' G g
  map_identity := (G.restrictionIdentity_comp_arrowsToArrows g).symm
  map_comp := fun _ f h w _ => G.restrictionComposition_lift_comp_arrowsToArrows g f h w

/-- The generalized arrow of the restriction lifting a generalized arrow of `G` between the
images of two generalized objects of `U'`: the triple `(y, f, x)`. -/
noncomputable def restrictGroupoidLift {T : Over S} (x y : T ⟶ U')
    (f : G.EvaluationHom (x ≫ g : G.Evaluation T) (y ≫ g : G.Evaluation T)) :
    (restrictGroupoid G g).EvaluationHom x y where
  arrow := pullback.lift (pullback.lift y f.arrow f.target_eq.symm)
    (pullback.lift f.arrow x f.source_eq)
    ((pullback.lift_snd _ _ _).trans (pullback.lift_fst _ _ _).symm)
  source_eq := by
    change _ ≫ pullback.snd _ _ ≫ pullback.snd G.source g = x
    rw [← Category.assoc, pullback.lift_snd, pullback.lift_snd]
  target_eq := by
    change _ ≫ pullback.fst _ _ ≫ pullback.fst g G.target = y
    rw [← Category.assoc, pullback.lift_fst, pullback.lift_fst]

/-- The lifted arrow lies over the given arrow of `G`. -/
theorem restrictGroupoidLift_arrow_comp {T : Over S} (x y : T ⟶ U')
    (f : G.EvaluationHom (x ≫ g : G.Evaluation T) (y ≫ g : G.Evaluation T)) :
    (restrictGroupoidLift G g x y f).arrow ≫ restrictionArrowsToArrows G g = f.arrow :=
  (Category.assoc _ _ _).symm.trans
    ((pullback.lift_fst _ _ _ =≫ pullback.snd g G.target).trans
      (pullback.lift_snd _ _ _))

/-- **On every test scheme the canonical functor is fully faithful**: an arrow of `G(T)`
between the images of two generalized objects of `U'` is the image of exactly one arrow of the
restriction. -/
noncomputable def restrictGroupoidHomEvaluationFullyFaithful (T : Over S) :
    ((restrictGroupoidHom G g).evaluation T).FullyFaithful where
  preimage {x y} f := restrictGroupoidLift G g x y f
  map_preimage {x y} f :=
    Stacks.Groupoids.GroupoidScheme.EvaluationHom.ext (restrictGroupoidLift_arrow_comp G g x y f)
  preimage_map {x y} f :=
    Stacks.Groupoids.GroupoidScheme.EvaluationHom.ext <| restriction_hom_ext G g _ _
      ((restrictGroupoidLift G g x y _).source_eq.trans f.source_eq.symm)
      ((restrictGroupoidLift G g x y _).target_eq.trans f.target_eq.symm)
      (restrictGroupoidLift_arrow_comp G g x y _)

/-- The map `U'(T) ⟶ U(T)` on generalized objects induced by `g`, as the object map of the
canonical functor. -/
noncomputable abbrev restrictGroupoidEvaluationObj (T : Over S) :
    (restrictGroupoid G g).Evaluation T → G.Evaluation T :=
  ((restrictGroupoidHom G g).evaluation T).obj

/-- The object map of the canonical functor is `u ↦ g ∘ u`. -/
theorem restrictGroupoidEvaluationObj_apply (T : Over S) (x : T ⟶ U') :
    restrictGroupoidEvaluationObj G g T x = x ≫ g :=
  rfl

/-- The groupoid of `T`-points of the restriction, to the restriction of the groupoid of
`T`-points of `G` along `U'(T) ⟶ U(T)`: the identity on objects, and the canonical functor on
arrows. -/
noncomputable def restrictGroupoidEvaluationFunctor (T : Over S) :
    (restrictGroupoid G g).Evaluation T ⥤
      InducedCategory (G.Evaluation T) (restrictGroupoidEvaluationObj G g T) where
  obj x := x
  map f := InducedCategory.homMk (((restrictGroupoidHom G g).evaluation T).map f)
  map_id x := InducedCategory.hom_ext (((restrictGroupoidHom G g).evaluation T).map_id x)
  map_comp f h :=
    InducedCategory.hom_ext (((restrictGroupoidHom G g).evaluation T).map_comp f h)

/-- The restriction of the groupoid of `T`-points of `G` along `U'(T) ⟶ U(T)`, to the groupoid
of `T`-points of the restriction: the identity on objects, and the unique lift on arrows. -/
noncomputable def restrictGroupoidEvaluationInverse (T : Over S) :
    InducedCategory (G.Evaluation T) (restrictGroupoidEvaluationObj G g T) ⥤
      (restrictGroupoid G g).Evaluation T where
  obj x := x
  map f := (restrictGroupoidHomEvaluationFullyFaithful G g T).preimage f.hom
  map_id _ := (restrictGroupoidHomEvaluationFullyFaithful G g T).preimage_id
  map_comp f h := (restrictGroupoidHomEvaluationFullyFaithful G g T).preimage_comp f.hom h.hom

/-- The identification of the `T`-points of the restriction with the induced groupoid followed
by its canonical functor is the evaluation of the canonical morphism of groupoid schemes. -/
theorem restrictGroupoidEvaluationFunctor_comp_inducedFunctor (T : Over S) :
    restrictGroupoidEvaluationFunctor G g T ⋙
        inducedFunctor (restrictGroupoidEvaluationObj G g T) =
      (restrictGroupoidHom G g).evaluation T :=
  rfl

/-- The identification of the `T`-points of the restriction with the induced groupoid has the
lift as a left inverse. -/
theorem restrictGroupoidEvaluationFunctor_comp_inverse (T : Over S) :
    restrictGroupoidEvaluationFunctor G g T ⋙ restrictGroupoidEvaluationInverse G g T =
      𝟭 _ :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ f =>
    ((restrictGroupoidHomEvaluationFullyFaithful G g T).preimage_map f).trans
      ((Category.id_comp _).symm.trans (𝟙 _ ≫= (Category.comp_id f).symm)))

/-- The identification of the `T`-points of the restriction with the induced groupoid has the
lift as a right inverse. -/
theorem restrictGroupoidEvaluationInverse_comp_functor (T : Over S) :
    restrictGroupoidEvaluationInverse G g T ⋙ restrictGroupoidEvaluationFunctor G g T =
      𝟭 _ :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ f =>
    (InducedCategory.hom_ext
      ((restrictGroupoidHomEvaluationFullyFaithful G g T).map_preimage f.hom) :
        InducedCategory.homMk _ = f).trans
      ((Category.id_comp _).symm.trans (𝟙 _ ≫= (Category.comp_id f).symm)))

/-- **Stacks Lemma 02VB.**  Let `(U, R, s, t, c)` be a groupoid scheme over `S` and
`g : U' ⟶ U` a morphism.  With `R' = (U' ×_{g, U, t} R) ×_R (R ×_{s, U, g} U')` the iterated
fibre product of the displayed diagram, `s' : R' ⟶ R ×_{s, U, g} U' ⟶ U'` and
`t' : R' ⟶ U' ×_{g, U, t} R ⟶ U'`, the groupoid scheme `restrictGroupoid G g` is
`(U', R', s', t', c')` for the canonical composition law
`c' = Stacks.Groupoids.GroupoidScheme.restrictionComposition`, which is characterized as the
morphism on composable pairs whose source, target and underlying arrow of `R` are those of the
second factor, of the first factor, and the composite in `R`.  The morphism of groupoid schemes
`restrictGroupoidHom G g` is `g` on objects and the projection `R' ⟶ R` on arrows.  Finally, on
every scheme `T` over `S`, the functor of groupoids
`(U'(T), R'(T), s', t', c') ⟶ (U(T), R(T), s, t, c)` is the restriction of
`(U(T), R(T), s, t, c)` via `U'(T) ⟶ U(T)`: there is an isomorphism of categories to the
induced groupoid `InducedCategory (U(T), R(T), s, t, c) (· ≫ g)`, the identity on objects,
carrying the functor to the canonical functor `inducedFunctor` of the restriction. -/
@[stacks 02VB]
theorem restrictGroupoid_isRestriction :
    (restrictGroupoid G g).objects = U' ∧
    (restrictGroupoid G g).arrows =
      pullback (pullback.snd g G.target) (pullback.fst G.source g) ∧
    (restrictGroupoid G g).source =
      pullback.snd (pullback.snd g G.target) (pullback.fst G.source g) ≫
        pullback.snd G.source g ∧
    (restrictGroupoid G g).target =
      pullback.fst (pullback.snd g G.target) (pullback.fst G.source g) ≫
        pullback.fst g G.target ∧
    (restrictGroupoid G g).comp = G.restrictionComposition g ∧
    (∀ {T : Over S} (a b : T ⟶ (restrictGroupoid G g).arrows)
        (w : a ≫ (restrictGroupoid G g).source = b ≫ (restrictGroupoid G g).target),
      (pullback.lift a b w ≫ (restrictGroupoid G g).comp) ≫ (restrictGroupoid G g).source =
          b ≫ (restrictGroupoid G g).source ∧
        (pullback.lift a b w ≫ (restrictGroupoid G g).comp) ≫ (restrictGroupoid G g).target =
          a ≫ (restrictGroupoid G g).target ∧
        (pullback.lift a b w ≫ (restrictGroupoid G g).comp) ≫
            (restrictGroupoidHom G g).mapArrows =
          G.compose (a ≫ (restrictGroupoidHom G g).mapArrows)
            (b ≫ (restrictGroupoidHom G g).mapArrows)
            (G.restriction_compose_condition g a b w)) ∧
    (restrictGroupoidHom G g).mapObjects = g ∧
    (restrictGroupoidHom G g).mapArrows =
      pullback.fst (pullback.snd g G.target) (pullback.fst G.source g) ≫
        pullback.snd g G.target ∧
    ∀ T : Over S,
      (∀ x, (restrictGroupoidEvaluationFunctor G g T).obj x = x) ∧
      restrictGroupoidEvaluationFunctor G g T ⋙ restrictGroupoidEvaluationInverse G g T =
        𝟭 _ ∧
      restrictGroupoidEvaluationInverse G g T ⋙ restrictGroupoidEvaluationFunctor G g T =
        𝟭 _ ∧
      restrictGroupoidEvaluationFunctor G g T ⋙
          inducedFunctor (restrictGroupoidEvaluationObj G g T) =
        (restrictGroupoidHom G g).evaluation T :=
  ⟨rfl, rfl, rfl, rfl, rfl,
    fun a b w => ⟨(Category.assoc _ _ _).trans
        ((pullback.lift a b w ≫= G.restrictionComposition_comp_source g).trans
          (pullback.lift_snd_assoc a b w _)),
      (Category.assoc _ _ _).trans
        ((pullback.lift a b w ≫= G.restrictionComposition_comp_target g).trans
          (pullback.lift_fst_assoc a b w _)),
      G.restrictionComposition_lift_comp_arrowsToArrows g a b w⟩,
    rfl, rfl, fun T => ⟨fun _ => rfl, restrictGroupoidEvaluationFunctor_comp_inverse G g T,
      restrictGroupoidEvaluationInverse_comp_functor G g T,
      restrictGroupoidEvaluationFunctor_comp_inducedFunctor G g T⟩⟩

/-- The restriction of `G` along `g`, built from the displayed data, as a realization of the
structure `AlgebraicGeometry.GroupoidScheme.Restriction`: every specification field holds by
`rfl`. -/
noncomputable def displayedRestriction : Restriction G g where
  groupoid := restrictGroupoid G g
  objects_eq := rfl
  arrows_eq := rfl
  source_eq := rfl
  target_eq := rfl
  hom := restrictGroupoidHom G g
  mapObjects_eq := rfl
  mapArrows_eq := rfl
  evaluation_fullyFaithful T := ⟨restrictGroupoidHomEvaluationFullyFaithful G g T⟩

/-- **Every realization of the restriction is the displayed one.**  The specification fields of
`AlgebraicGeometry.GroupoidScheme.Restriction` fix the objects, arrows, source, target and the
canonical morphism, and these force the composition, identity and inverse. -/
theorem Restriction.eq_displayedRestriction (R : Restriction G g) :
    R = displayedRestriction G g := by
  obtain ⟨H, hO, hA, hS, hT, F, hmo, hma, hff⟩ := R
  obtain ⟨objs, arrs, src, tgt, comp, ident, inv, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀,
    h₁₁⟩ := H
  have hO' : objs = U' := hO
  have hA' : arrs = restrictionArrows G g := hA
  subst objs arrs
  obtain rfl : src = restrictionSource G g := by
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hS
  obtain rfl : tgt = restrictionTarget G g := by
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hT
  have hc := F.comp_mapArrows
  have hid := F.map_identity
  have hinv := groupoidHom_map_inverse F
  obtain ⟨mo, ma, m₁, m₂, m₃, m₄⟩ := F
  have hmo' : mo = g := by simpa only [eqToHom_refl, Category.id_comp] using hmo
  have hma' : ma = restrictionArrowsToArrows G g := by
    simpa only [eqToHom_refl, Category.id_comp] using hma
  dsimp only at hc hid hinv
  subst mo ma
  obtain rfl : comp = G.restrictionComposition g := by
    refine G.eq_restrictionComposition_of_spec g comp h₅ h₆ ?_
    rw [hc, Stacks.Groupoids.GroupoidScheme.Hom.mapComposable]
    exact congrArg (· ≫ G.comp) (G.restrictionAmbientLift_eq_map g m₁ m₂)
  obtain rfl := G.eq_restrictionIdentity_of_spec g ident h₁ h₂ hid.symm
  obtain rfl := G.eq_restrictionInverse_of_spec g inv h₃ h₄ hinv.symm
  rfl

/-- A restriction of a groupoid scheme is unique: the type of realizations is a subsingleton. -/
instance : Subsingleton (Restriction G g) :=
  ⟨fun R₁ R₂ => (R₁.eq_displayedRestriction G g).trans
    (R₂.eq_displayedRestriction G g).symm⟩

/-- The realization `AlgebraicGeometry.GroupoidScheme.restrict` is the displayed one. -/
theorem restrict_eq_displayedRestriction : restrict G g = displayedRestriction G g :=
  (restrict G g).eq_displayedRestriction G g

/-- The groupoid scheme of the realization `AlgebraicGeometry.GroupoidScheme.restrict` is
`(U', R', s', t', c')` built from the displayed data. -/
theorem restrict_groupoid : (restrict G g).groupoid = restrictGroupoid G g :=
  congrArg Restriction.groupoid (restrict_eq_displayedRestriction G g)

end Restrict

end AlgebraicGeometry.GroupoidScheme

end
