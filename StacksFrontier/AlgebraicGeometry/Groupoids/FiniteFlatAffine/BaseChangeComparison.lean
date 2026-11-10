module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidBaseChange
public import StacksFrontier.AlgebraicGeometry.Groupoids.FieldExtensionEvaluation
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.OverPullback

/-!
# Comparison maps attached to a morphism of groupoid schemes over a morphism of bases

A morphism `P` of groupoid schemes lying over a morphism `f` of bases carries the structure
maps of the source groupoid to those of the target groupoid. This file records the
consequences that are used when the two object squares and arrow squares are cartesian: the
source and target squares are then cartesian as well, so every property of morphisms stable
under base change passes from `G` to `G'`.

The remaining results compare `P` with composition and with the inverse. Compatibility with
the inverse is not a field of `AlgebraicGeometry.GroupoidScheme.HomOver`; it is a consequence
of compatibility with composition and the identity, obtained by reading `P` as a functor
between the groupoids of generalized points and using that a functor preserves inverses.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.HomOver.evaluationFunctor`: the functor on generalized
  points induced by `P`.
* `AlgebraicGeometry.GroupoidScheme.HomOver.composablesMap`: the induced map on the schemes of
  composable arrows.

## Main results

* `AlgebraicGeometry.GroupoidScheme.HomOver.source_isPullback` and
  `AlgebraicGeometry.GroupoidScheme.HomOver.target_isPullback`: the source and target squares
  are cartesian.
* `AlgebraicGeometry.GroupoidScheme.HomOver.comp_left`: compatibility with composition, on
  underlying schemes.
* `AlgebraicGeometry.GroupoidScheme.HomOver.map_inverse`: compatibility with the inverse.

## References

* [Stacks Project, Tag 0DT8](https://stacks.math.columbia.edu/tag/0DT8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The underlying morphism of schemes of a lift into a fibre product of `Over S` is the lift
into the underlying cartesian square. -/
theorem overFibreProduct_lift_left {S : Scheme.{u}} {X Y Z : Over S} (a b : Y ⟶ Z)
    (f g : X ⟶ Y) (w : f ≫ a = g ≫ b) :
    (pullback.lift f g w).left =
      (overFibreProduct_isPullback a b).lift f.left g.left (congrArg Over.Hom.left w) := by
  refine (overFibreProduct_isPullback a b).hom_ext ?_ ?_
  · calc
      (pullback.lift f g w).left ≫ (pullback.fst a b).left = f.left := by
        simpa only [Over.comp_left] using congrArg Over.Hom.left (pullback.lift_fst f g w)
      _ = _ := ((overFibreProduct_isPullback a b).lift_fst _ _ _).symm
  · calc
      (pullback.lift f g w).left ≫ (pullback.snd a b).left = g.left := by
        simpa only [Over.comp_left] using congrArg Over.Hom.left (pullback.lift_snd f g w)
      _ = _ := ((overFibreProduct_isPullback a b).lift_snd _ _ _).symm

namespace GroupoidScheme

namespace HomOver

variable {S S' : Scheme.{u}} {f : S' ⟶ S} {G' : GroupoidScheme S'} {G : GroupoidScheme S}

/-- A morphism of groupoid schemes over a morphism of bases, read as a functor between the
groupoids of generalized points on a test scheme. -/
noncomputable def evaluationFunctor (P : HomOver f G' G) (T : Over S') :
    G'.Evaluation T ⥤ G.Evaluation ((Over.map f).obj T) where
  obj x := (Over.map f).map x ≫ P.mapObjects
  map {x y} (h : G'.EvaluationHom x y) :=
    { arrow := (Over.map f).map h.arrow ≫ P.mapArrows
      source_eq := by
        calc
          ((Over.map f).map h.arrow ≫ P.mapArrows) ≫ G.source =
              (Over.map f).map h.arrow ≫ (Over.map f).map G'.source ≫ P.mapObjects := by
            rw [Category.assoc, P.map_source]
          _ = (Over.map f).map (h.arrow ≫ G'.source) ≫ P.mapObjects :=
            congrArg (fun k => k ≫ P.mapObjects)
              ((Over.map f).map_comp h.arrow G'.source).symm
          _ = (Over.map f).map x ≫ P.mapObjects := by rw [h.source_eq]
      target_eq := by
        calc
          ((Over.map f).map h.arrow ≫ P.mapArrows) ≫ G.target =
              (Over.map f).map h.arrow ≫ (Over.map f).map G'.target ≫ P.mapObjects := by
            rw [Category.assoc, P.map_target]
          _ = (Over.map f).map (h.arrow ≫ G'.target) ≫ P.mapObjects :=
            congrArg (fun k => k ≫ P.mapObjects)
              ((Over.map f).map_comp h.arrow G'.target).symm
          _ = (Over.map f).map y ≫ P.mapObjects := by rw [h.target_eq] }
  map_id x := by
    apply GroupoidScheme.EvaluationHom.ext
    change (Over.map f).map (x ≫ G'.identity) ≫ P.mapArrows =
      ((Over.map f).map x ≫ P.mapObjects) ≫ G.identity
    rw [Functor.map_comp]
    calc
      ((Over.map f).map x ≫ (Over.map f).map G'.identity) ≫ P.mapArrows =
          (Over.map f).map x ≫ ((Over.map f).map G'.identity ≫ P.mapArrows) := by
        rw [Category.assoc]
      _ = (Over.map f).map x ≫ (P.mapObjects ≫ G.identity) := by rw [← P.map_identity]
      _ = ((Over.map f).map x ≫ P.mapObjects) ≫ G.identity := by rw [Category.assoc]
  map_comp (h₁ : G'.EvaluationHom _ _) (h₂ : G'.EvaluationHom _ _) := by
    apply GroupoidScheme.EvaluationHom.ext
    have w := h₂.source_eq.trans h₁.target_eq.symm
    have w' : ((Over.map f).map h₂.arrow ≫ P.mapArrows) ≫ G.source =
        ((Over.map f).map h₁.arrow ≫ P.mapArrows) ≫ G.target := by
      calc
        ((Over.map f).map h₂.arrow ≫ P.mapArrows) ≫ G.source =
            (Over.map f).map h₂.arrow ≫ ((Over.map f).map G'.source ≫ P.mapObjects) := by
          rw [Category.assoc, P.map_source]
        _ = ((Over.map f).map h₂.arrow ≫ (Over.map f).map G'.source) ≫ P.mapObjects := by
          rw [Category.assoc]
        _ = (Over.map f).map (h₂.arrow ≫ G'.source) ≫ P.mapObjects :=
          congrArg (fun k => k ≫ P.mapObjects)
            ((Over.map f).map_comp h₂.arrow G'.source).symm
        _ = (Over.map f).map (h₁.arrow ≫ G'.target) ≫ P.mapObjects := by rw [w]
        _ = ((Over.map f).map h₁.arrow ≫ (Over.map f).map G'.target) ≫ P.mapObjects :=
          congrArg (fun k => k ≫ P.mapObjects)
            ((Over.map f).map_comp h₁.arrow G'.target)
        _ = (Over.map f).map h₁.arrow ≫ ((Over.map f).map G'.target ≫ P.mapObjects) := by
          rw [Category.assoc]
        _ = ((Over.map f).map h₁.arrow ≫ P.mapArrows) ≫ G.target := by
          rw [← P.map_target, ← Category.assoc]
    have hm := P.map_comp T h₂.arrow h₁.arrow w w'
    change (Over.map f).map (pullback.lift h₂.arrow h₁.arrow w ≫ G'.comp) ≫ P.mapArrows =
      pullback.lift ((Over.map f).map h₂.arrow ≫ P.mapArrows)
        ((Over.map f).map h₁.arrow ≫ P.mapArrows) w' ≫ G.comp
    simpa [GroupoidScheme.compose, Functor.map_comp, Category.assoc] using hm

/-- The two legs of the scheme of composable arrows of `G'`, pushed along `P`, are composable
in `G`. -/
theorem composables_condition (P : HomOver f G' G) :
    (pullback.fst G'.source G'.target).left ≫ P.mapArrows.left ≫ G.source.left =
      (pullback.snd G'.source G'.target).left ≫ P.mapArrows.left ≫ G.target.left := by
  have hs : P.mapArrows.left ≫ G.source.left = G'.source.left ≫ P.mapObjects.left := by
    simpa only [Over.comp_left, Over.map_map_left] using congrArg Over.Hom.left P.map_source
  have ht : P.mapArrows.left ≫ G.target.left = G'.target.left ≫ P.mapObjects.left := by
    simpa only [Over.comp_left, Over.map_map_left] using congrArg Over.Hom.left P.map_target
  have hp : (pullback.fst G'.source G'.target).left ≫ G'.source.left =
      (pullback.snd G'.source G'.target).left ≫ G'.target.left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (pullback.condition :
      pullback.fst G'.source G'.target ≫ G'.source =
        pullback.snd G'.source G'.target ≫ G'.target)
  simp only [hs, ht, ← Category.assoc, hp]

/-- The map induced by `P` on the schemes of composable arrows. -/
noncomputable def composablesMap (P : HomOver f G' G) :
    (pullback G'.source G'.target).left ⟶ (pullback G.source G.target).left :=
  (overFibreProduct_isPullback G.source G.target).lift
    ((pullback.fst G'.source G'.target).left ≫ P.mapArrows.left)
    ((pullback.snd G'.source G'.target).left ≫ P.mapArrows.left) (composables_condition P)

/-- `composablesMap P` followed by the first projection is the first projection followed by
the map of `P` on arrows. -/
@[reassoc]
theorem composablesMap_fst (P : HomOver f G' G) :
    composablesMap P ≫ (pullback.fst G.source G.target).left =
      (pullback.fst G'.source G'.target).left ≫ P.mapArrows.left :=
  (overFibreProduct_isPullback G.source G.target).lift_fst _ _ (composables_condition P)

/-- `composablesMap P` followed by the second projection is the second projection followed by
the map of `P` on arrows. -/
@[reassoc]
theorem composablesMap_snd (P : HomOver f G' G) :
    composablesMap P ≫ (pullback.snd G.source G.target).left =
      (pullback.snd G'.source G'.target).left ≫ P.mapArrows.left :=
  (overFibreProduct_isPullback G.source G.target).lift_snd _ _ (composables_condition P)

/-- Compatibility of `P` with composition, on underlying schemes. -/
theorem comp_left (P : HomOver f G' G) :
    G'.comp.left ≫ P.mapArrows.left = composablesMap P ≫ G.comp.left := by
  set T := pullback G'.source G'.target with hT
  set a := pullback.fst G'.source G'.target with ha
  set b := pullback.snd G'.source G'.target with hb
  have w : a ≫ G'.source = b ≫ G'.target := pullback.condition
  have w' : ((Over.map f).map a ≫ P.mapArrows) ≫ G.source =
      ((Over.map f).map b ≫ P.mapArrows) ≫ G.target := by
    apply Over.OverMorphism.ext
    change ((Over.map f).map a).left ≫ P.mapArrows.left ≫ G.source.left = _
    simpa only [ha, hb, Over.map_map_left, Over.comp_left, Category.assoc] using
      composables_condition P
  have hm := P.map_comp T a b w w'
  have hLiftId : pullback.lift a b w = 𝟙 T := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.id_comp]
    · rw [pullback.lift_snd, Category.id_comp]
  have hLift : (pullback.lift ((Over.map f).map a ≫ P.mapArrows)
      ((Over.map f).map b ≫ P.mapArrows) w').left = composablesMap P :=
    overFibreProduct_lift_left G.source G.target _ _ w'
  have hm' := congrArg Over.Hom.left hm
  simp only [GroupoidScheme.compose, Over.comp_left] at hm'
  rw [hLiftId] at hm'
  simpa [hLift] using hm'

/-- Compatibility of `P` with the inverse. This is not part of the data of a morphism of
groupoid schemes; it follows because a functor between groupoids preserves inverses. -/
theorem map_inverse (P : HomOver f G' G) :
    (Over.map f).map G'.inverse ≫ P.mapArrows = P.mapArrows ≫ G.inverse := by
  let F := evaluationFunctor P G'.arrows
  let h : G'.EvaluationHom G'.source G'.target := ⟨𝟙 G'.arrows, by simp, by simp⟩
  let x : G'.Evaluation G'.arrows := G'.source
  let y : G'.Evaluation G'.arrows := G'.target
  let hHom : x ⟶ y := h
  have : IsIso hHom := inferInstance
  have hInv := congrArg (fun z : F.obj y ⟶ F.obj x => z.arrow) (Functor.map_inv F hHom)
  rw [← Groupoid.inv_eq_inv hHom, ← Groupoid.inv_eq_inv (F.map hHom)] at hInv
  change (Over.map f).map (h.arrow ≫ G'.inverse) ≫ P.mapArrows =
    ((Over.map f).map h.arrow ≫ P.mapArrows) ≫ G.inverse at hInv
  simpa [h, Functor.map_comp, Category.assoc] using hInv

/-- If a square of structure maps commutes under `P` and the arrow and object squares are
cartesian, then the square of structure maps is cartesian. -/
private theorem isPullback_of_arrows_objects (P : HomOver f G' G)
    (hA : IsPullback P.mapArrows.left G'.arrows.hom G.arrows.hom f)
    (hO : IsPullback P.mapObjects.left G'.objects.hom G.objects.hom f)
    {s : G'.arrows ⟶ G'.objects} {t : G.arrows ⟶ G.objects}
    (h : P.mapArrows ≫ t = (Over.map f).map s ≫ P.mapObjects) :
    IsPullback P.mapArrows.left s.left t.left P.mapObjects.left := by
  refine IsPullback.of_bot (v₂₁ := G'.objects.hom) (v₂₂ := G.objects.hom) ?_ ?_ hO
  · simpa only [Over.w] using hA
  · exact congrArg Over.Hom.left h

/-- When the arrow and object squares of `P` are cartesian, so is the source square. -/
theorem source_isPullback (P : HomOver f G' G)
    (hA : IsPullback P.mapArrows.left G'.arrows.hom G.arrows.hom f)
    (hO : IsPullback P.mapObjects.left G'.objects.hom G.objects.hom f) :
    IsPullback P.mapArrows.left G'.source.left G.source.left P.mapObjects.left :=
  isPullback_of_arrows_objects P hA hO P.map_source

/-- When the arrow and object squares of `P` are cartesian, so is the target square. -/
theorem target_isPullback (P : HomOver f G' G)
    (hA : IsPullback P.mapArrows.left G'.arrows.hom G.arrows.hom f)
    (hO : IsPullback P.mapObjects.left G'.objects.hom G.objects.hom f) :
    IsPullback P.mapArrows.left G'.target.left G.target.left P.mapObjects.left :=
  isPullback_of_arrows_objects P hA hO P.map_target

end HomOver

variable {S S' : Scheme.{u}} {f : S' ⟶ S} {G : GroupoidScheme S}

/-- The source map of a base-changed groupoid scheme is the base change of the source map. -/
theorem BaseChange.source_isPullback (bc : BaseChange f G) :
    IsPullback bc.projection.mapArrows.left bc.groupoid.source.left G.source.left
      bc.projection.mapObjects.left :=
  bc.projection.source_isPullback bc.isPullback_arrows bc.isPullback_objects

/-- The target map of a base-changed groupoid scheme is the base change of the target map. -/
theorem BaseChange.target_isPullback (bc : BaseChange f G) :
    IsPullback bc.projection.mapArrows.left bc.groupoid.target.left G.target.left
      bc.projection.mapObjects.left :=
  bc.projection.target_isPullback bc.isPullback_arrows bc.isPullback_objects

end GroupoidScheme

end AlgebraicGeometry

end
