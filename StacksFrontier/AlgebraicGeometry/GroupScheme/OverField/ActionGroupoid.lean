module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic
public import StacksFrontier.CategoryTheory.Monoidal.ActionGroupoid

/-!
# The groupoid scheme associated to a group scheme action

An action of a group scheme `G` over `Y` on a scheme `X` over `Y` gives a groupoid scheme, with
objects `X` and arrows `G ⊗ X`.

## Main definitions

* `AlgebraicGeometry.actionInverse` is the inverse map of the action groupoid, as a morphism of
  schemes over `Y`. Its composition and identity maps are the readings in `Over Y.left` of
  `Stacks.Groupoids.ActionGroupoid.composition` and
  `Stacks.Groupoids.ActionGroupoid.identity`.
* `AlgebraicGeometry.ActionGroupoidConstruction` records the resulting groupoid scheme together
  with the specified formulas for all its structure morphisms.

## Main results

* `AlgebraicGeometry.actionComposition_eval` evaluates composition on a composable pair of
  generalized points.
* `AlgebraicGeometry.groupoidSchemeOfAction` constructs the action groupoid scheme over any
  base of `Y`.

## Implementation notes

Tensor products in `Over Y` are fibre products over `Y`.  The auxiliary morphism
`Stacks.Groupoids.ActionGroupoid.composition` is the map
`((g, x), (g', x')) ↦ (g g', x')`; it, the identity and the inverse, and the groupoid axioms
they satisfy, are those of the action groupoid of a group
object in a cartesian monoidal category, read in the slice over `Y.left`.  The functor
`Over.map Y.hom` regards a scheme over `Y` as a scheme over `S`.  Heterogeneous equalities in
`ActionGroupoidConstruction` state that the bundled structure maps are exactly these maps; they
avoid replacing the specified objects by merely isomorphic ones.

## References

* [Stacks Project, Tag 0234](https://stacks.math.columbia.edu/tag/0234)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (Y : Over S) (G X : Over Y.left) [GrpObj G] [ModObj G X]

/-- Regarding schemes over `Y` as schemes over a base of `Y` preserves fibre products. -/
theorem overMap_preserves_pullback (A B C : Over Y.left) (f : A ⟶ C) (g : B ⟶ C) :
    IsPullback
      ((Over.map Y.hom).map (pullback.fst f g))
      ((Over.map Y.hom).map (pullback.snd f g))
      ((Over.map Y.hom).map f) ((Over.map Y.hom).map g) := by
  let F := Over.map Y.hom
  let P := pullback f g
  refine IsPullback.mk' (by
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg F.map pullback.condition) ?_ ?_
  · intro T k l hk hl
    let TY : Over Y.left := Over.mk (k.left ≫ P.hom)
    let kY : TY ⟶ P := Over.homMk k.left rfl
    have hkLeft : k.left ≫ (pullback.fst f g).left = l.left ≫ (pullback.fst f g).left := by
      simpa [F] using congrArg Over.Hom.left hk
    have hlLeft : k.left ≫ (pullback.snd f g).left = l.left ≫ (pullback.snd f g).left := by
      simpa [F] using congrArg Over.Hom.left hl
    have hbase : k.left ≫ P.hom = l.left ≫ P.hom := by
      simp only [P, ← Over.w (pullback.fst f g), reassoc_of% hkLeft]
    let lY : TY ⟶ P := Over.homMk l.left hbase.symm
    have hkY : kY ≫ pullback.fst f g = lY ≫ pullback.fst f g := by
      apply Over.OverMorphism.ext
      simpa [kY, lY] using hkLeft
    have hlY : kY ≫ pullback.snd f g = lY ≫ pullback.snd f g := by
      apply Over.OverMorphism.ext
      simpa [kY, lY] using hlLeft
    have hY : kY = lY := pullback.hom_ext hkY hlY
    apply Over.OverMorphism.ext
    simpa [kY, lY] using congrArg Over.Hom.left hY
  · intro T a b hab
    let TY : Over Y.left := Over.mk (a.left ≫ A.hom)
    have habLeft : a.left ≫ f.left = b.left ≫ g.left := congrArg Over.Hom.left hab
    have hbase : b.left ≫ B.hom = TY.hom := by
      dsimp [TY]
      rw [← Over.w g, ← Over.w f, reassoc_of% habLeft]
    let aY : TY ⟶ A := Over.homMk a.left rfl
    let bY : TY ⟶ B := Over.homMk b.left hbase
    have habY : aY ≫ f = bY ≫ g := Over.OverMorphism.ext habLeft
    let lY : TY ⟶ P := pullback.lift aY bY habY
    let l : T ⟶ F.obj P := Over.homMk lY.left (by
      dsimp [F]
      change lY.left ≫ (P.hom ≫ Y.hom) = T.hom
      rw [← Category.assoc, Over.w lY]
      simpa [TY, F, Category.assoc] using (Over.w a))
    refine ⟨l, ?_, ?_⟩
    · apply Over.OverMorphism.ext
      change lY.left ≫ (pullback.fst f g).left = a.left
      exact congrArg Over.Hom.left (pullback.lift_fst aY bY habY)
    · apply Over.OverMorphism.ext
      change lY.left ≫ (pullback.snd f g).left = b.left
      exact congrArg Over.Hom.left (pullback.lift_snd aY bY habY)

/-- The source of a composite arrow in the action groupoid is the source of its second
factor. -/
theorem actionComposition_source :
    Stacks.Groupoids.ActionGroupoid.composition G X ≫ snd G X =
      pullback.snd (snd G X) γ[G, X] ≫ snd G X :=
  Stacks.Groupoids.ActionGroupoid.composition_source G X

/-- The target of a composite arrow in the action groupoid is the target of its first
factor. -/
theorem actionComposition_target :
    Stacks.Groupoids.ActionGroupoid.composition G X ≫ γ[G, X] =
      pullback.fst (snd G X) γ[G, X] ≫ γ[G, X] :=
  Stacks.Groupoids.ActionGroupoid.composition_target G X

/-- Composition in the action groupoid, evaluated on a composable pair of generalized
points. -/
theorem actionComposition_eval {T : Over Y.left} (Z : Over Y.left) [ModObj G Z]
    (x y : T ⟶ G ⊗ Z) (w : x ≫ snd G Z = y ≫ γ[G,Z]) :
    pullback.lift x y w ≫ Stacks.Groupoids.ActionGroupoid.composition G Z =
      lift ((x ≫ fst G Z) * (y ≫ fst G Z)) (y ≫ snd G Z) :=
  Stacks.Groupoids.ActionGroupoid.composition_eval G Z x y w

/-- The inverse map of the action groupoid over `Y`: it sends `(g,x)` to
`(g⁻¹,g • x)`. -/
noncomputable def actionInverse : G ⊗ X ⟶ G ⊗ X :=
  Stacks.Groupoids.ActionGroupoid.inverse G X

/-- A generalized point over the base `S` of `Y`, viewed over `Y` itself. -/
private def actionTestObject {T : Over S} {A : Over Y.left}
    (f : T ⟶ (Over.map Y.hom).obj A) : Over Y.left :=
  Over.mk (f.left ≫ A.hom)

/-- The morphism over `Y` underlying a generalized point over the base `S` of `Y`. -/
private def actionTestMap {T : Over S} {A : Over Y.left}
    (f : T ⟶ (Over.map Y.hom).obj A) : actionTestObject Y f ⟶ A :=
  Over.homMk f.left rfl

/-- The comparison from a generalized point over `S` to the same point viewed over `Y`. -/
private def actionTestBase {T : Over S} {A : Over Y.left}
    (f : T ⟶ (Over.map Y.hom).obj A) : T ⟶ (Over.map Y.hom).obj (actionTestObject Y f) :=
  Over.homMk (𝟙 T.left) (by
    dsimp [actionTestObject]
    simpa [Category.assoc] using (Over.w f))

/-- A generalized point over `S` factors through its own image over `Y`. -/
private theorem actionTest_factor {T : Over S} {A : Over Y.left}
    (f : T ⟶ (Over.map Y.hom).obj A) :
    actionTestBase Y f ≫ (Over.map Y.hom).map (actionTestMap Y f) = f :=
  Over.OverMorphism.ext (Category.id_comp f.left)

/-- A groupoid scheme equipped with the precise identifications of its objects, arrows, and
structure morphisms with those arising from an action. -/
structure ActionGroupoidConstruction where
  /-- The resulting groupoid scheme over `S`. -/
  groupoid : Stacks.Groupoids.GroupoidScheme S
  /-- The scheme of objects is `X`, viewed over `S`. -/
  objects_eq : groupoid.objects = (Over.map Y.hom).obj X
  /-- The scheme of arrows is `G ×_Y X`, viewed over `S`. -/
  arrows_eq : groupoid.arrows = (Over.map Y.hom).obj (G ⊗ X)
  /-- The source map is the projection `(g, x) ↦ x`. -/
  source_eq : HEq groupoid.source ((Over.map Y.hom).map (snd G X))
  /-- The target map is the action `(g, x) ↦ g • x`. -/
  target_eq : HEq groupoid.target ((Over.map Y.hom).map γ[G, X])
  /-- The canonical identification of the two presentations of the scheme of composable
  arrows. -/
  compositionDomainIso :
    pullback
        ((Over.map Y.hom).map (snd G X))
        ((Over.map Y.hom).map γ[G, X]) ≅
      (Over.map Y.hom).obj (pullback (snd G X) γ[G, X])
  /-- The identification `compositionDomainIso` is compatible with the first projections. -/
  compositionDomainIso_fst :
    compositionDomainIso.hom ≫
        (Over.map Y.hom).map (pullback.fst (snd G X) γ[G, X]) =
      pullback.fst
        ((Over.map Y.hom).map (snd G X))
        ((Over.map Y.hom).map γ[G, X])
  /-- The identification `compositionDomainIso` is compatible with the second projections. -/
  compositionDomainIso_snd :
    compositionDomainIso.hom ≫
        (Over.map Y.hom).map (pullback.snd (snd G X) γ[G, X]) =
      pullback.snd
        ((Over.map Y.hom).map (snd G X))
        ((Over.map Y.hom).map γ[G, X])
  /-- Composition is the composition of the action groupoid over `Y`, transported along
  `compositionDomainIso`. -/
  comp_eq : HEq groupoid.comp
    (compositionDomainIso.hom ≫
      (Over.map Y.hom).map (Stacks.Groupoids.ActionGroupoid.composition G X))
  /-- The identity map is `x ↦ (1, x)`. -/
  identity_eq : HEq groupoid.identity
    ((Over.map Y.hom).map (Stacks.Groupoids.ActionGroupoid.identity G X))
  /-- The inverse map is `(g, x) ↦ (g⁻¹, g • x)`. -/
  inverse_eq : HEq groupoid.inverse ((Over.map Y.hom).map (actionInverse Y G X))

/-- The action groupoid scheme of a group scheme action, with objects `X`, arrows `G ×_Y X`,
and the source, target, composition, identity, and inverse maps given by the standard
formulas. -/
@[stacks 0234, sga "3 V 10.2"]
noncomputable def groupoidSchemeOfAction : ActionGroupoidConstruction Y G X := by
  let F := Over.map Y.hom
  let p : F.obj (G ⊗ X) ⟶ F.obj X := F.map (snd G X)
  let q : F.obj (G ⊗ X) ⟶ F.obj X := F.map γ[G, X]
  let d := pullback p q
  have hpres := overMap_preserves_pullback Y (G ⊗ X) (G ⊗ X) X (snd G X) γ[G, X]
  let iso : d ≅ F.obj (pullback (snd G X) γ[G, X]) :=
    (IsPullback.of_hasPullback p q).isoIsPullback _ _ hpres
  have hp : iso.hom ≫ F.map (pullback.fst (snd G X) γ[G, X]) = pullback.fst p q := by
    exact (IsPullback.of_hasPullback p q).isoIsPullback_hom_fst _ _ hpres
  have hq : iso.hom ≫ F.map (pullback.snd (snd G X) γ[G, X]) = pullback.snd p q := by
    exact (IsPullback.of_hasPullback p q).isoIsPullback_hom_snd _ _ hpres
  let H_Y : Stacks.Groupoids.GroupoidObjectData X (G ⊗ X) :=
    { source := snd G X
      target := γ[G, X]
      comp := Stacks.Groupoids.ActionGroupoid.composition G X
      identity := Stacks.Groupoids.ActionGroupoid.identity G X
      inverse := actionInverse Y G X
      source_identity := Stacks.Groupoids.ActionGroupoid.identity_source G X
      target_identity := Stacks.Groupoids.ActionGroupoid.identity_target G X
      source_inverse := Stacks.Groupoids.ActionGroupoid.inverse_source G X
      target_inverse := Stacks.Groupoids.ActionGroupoid.inverse_target G X
      source_comp := actionComposition_source Y G X
      target_comp := actionComposition_target Y G X
      left_identity := Stacks.Groupoids.ActionGroupoid.composition_left_identity G X
      right_identity := Stacks.Groupoids.ActionGroupoid.composition_right_identity G X
      left_inverse := Stacks.Groupoids.ActionGroupoid.composition_left_inverse G X
      right_inverse := Stacks.Groupoids.ActionGroupoid.composition_right_inverse G X
      assoc := Stacks.Groupoids.ActionGroupoid.composition_assoc G X }
  let comp : d ⟶ F.obj (G ⊗ X) := iso.hom ≫ F.map (Stacks.Groupoids.ActionGroupoid.composition G X)
  have lift_pair_factor {T : Over S} {TY : Over Y.left}
      (b : T ⟶ F.obj TY) (uY vY : TY ⟶ G ⊗ X)
      (wY : uY ≫ snd G X = vY ≫ γ[G, X])
      (u v : T ⟶ F.obj (G ⊗ X))
      (hu : b ≫ F.map uY = u) (hv : b ≫ F.map vY = v)
      (w : u ≫ p = v ≫ q) :
      pullback.lift u v w ≫ iso.hom =
        b ≫ F.map (pullback.lift uY vY wY) := by
    apply hpres.hom_ext
    · calc
        pullback.lift u v w ≫ iso.hom ≫ F.map (pullback.fst (snd G X) γ[G, X]) =
            pullback.lift u v w ≫ pullback.fst p q := by rw [hp]
        _ = u := by rw [pullback.lift_fst]
        _ = b ≫ F.map uY := hu.symm
        _ = b ≫ F.map (pullback.lift uY vY wY ≫ pullback.fst (snd G X) γ[G, X]) := by
              rw [pullback.lift_fst]
    · calc
        pullback.lift u v w ≫ iso.hom ≫ F.map (pullback.snd (snd G X) γ[G, X]) =
            pullback.lift u v w ≫ pullback.snd p q := by rw [hq]
        _ = v := by rw [pullback.lift_snd]
        _ = b ≫ F.map vY := hv.symm
        _ = b ≫ F.map (pullback.lift uY vY wY ≫ pullback.snd (snd G X) γ[G, X]) := by
              rw [pullback.lift_snd]
  have comp_pair_factor {T : Over S} {TY : Over Y.left}
      (b : T ⟶ F.obj TY) (uY vY : TY ⟶ G ⊗ X)
      (wY : uY ≫ snd G X = vY ≫ γ[G, X])
      (u v : T ⟶ F.obj (G ⊗ X))
      (hu : b ≫ F.map uY = u) (hv : b ≫ F.map vY = v)
      (w : u ≫ p = v ≫ q) :
      pullback.lift u v w ≫ comp =
        b ≫ F.map (pullback.lift uY vY wY ≫ Stacks.Groupoids.ActionGroupoid.composition G X) := by
    calc
      pullback.lift u v w ≫ comp =
          (pullback.lift u v w ≫ iso.hom) ≫
              F.map (Stacks.Groupoids.ActionGroupoid.composition G X) := by
            simp [comp, Category.assoc]
      _ = (b ≫ F.map (pullback.lift uY vY wY)) ≫
            F.map (Stacks.Groupoids.ActionGroupoid.composition G X) := by
            rw [lift_pair_factor b uY vY wY u v hu hv w]
      _ = b ≫ F.map (pullback.lift uY vY wY ≫ Stacks.Groupoids.ActionGroupoid.composition G X) := by
            simp [F.map_comp, Category.assoc]
  let H : Stacks.Groupoids.GroupoidScheme S :=
      { objects := F.obj X
        arrows := F.obj (G ⊗ X)
        source := p
        target := q
        comp := comp
        identity := F.map (Stacks.Groupoids.ActionGroupoid.identity G X)
        inverse := F.map (actionInverse Y G X)
        source_identity := by
          change F.map (Stacks.Groupoids.ActionGroupoid.identity G X ≫ snd G X) = 𝟙 (F.obj X)
          rw [← F.map_id]
          exact congrArg F.map (Stacks.Groupoids.ActionGroupoid.identity_source G X)
        target_identity := by
          change F.map (Stacks.Groupoids.ActionGroupoid.identity G X ≫ γ[G, X]) = 𝟙 (F.obj X)
          rw [← F.map_id]
          exact congrArg F.map (Stacks.Groupoids.ActionGroupoid.identity_target G X)
        source_inverse := by
          change F.map (actionInverse Y G X ≫ snd G X) = F.map γ[G, X]
          exact congrArg F.map (Stacks.Groupoids.ActionGroupoid.inverse_source G X)
        target_inverse := by
          change F.map (actionInverse Y G X ≫ γ[G, X]) = F.map (snd G X)
          exact congrArg F.map (Stacks.Groupoids.ActionGroupoid.inverse_target G X)
        source_comp := by
          change comp ≫ p = pullback.snd p q ≫ p
          dsimp only [comp, p]
          rw [Category.assoc, ← F.map_comp, actionComposition_source, F.map_comp,
            ← Category.assoc, hq]
        target_comp := by
          change comp ≫ q = pullback.fst p q ≫ q
          dsimp only [comp, q]
          rw [Category.assoc, ← F.map_comp, actionComposition_target, F.map_comp,
            ← Category.assoc, hp]
        left_identity := by
          intros T f w
          let TY := actionTestObject Y f
          let fY := actionTestMap Y f
          let tbase := actionTestBase Y f
          have hf : tbase ≫ F.map fY = f := actionTest_factor Y f
          have wY :
              (fY ≫ γ[G, X] ≫ Stacks.Groupoids.ActionGroupoid.identity G X) ≫ snd G X =
                fY ≫ γ[G, X] := by
            simp [Stacks.Groupoids.ActionGroupoid.identity]
          have hu : tbase ≫ F.map (fY ≫ γ[G, X] ≫ Stacks.Groupoids.ActionGroupoid.identity G X) =
              f ≫ q ≫ F.map (Stacks.Groupoids.ActionGroupoid.identity G X) := by
            rw [F.map_comp, F.map_comp, ← Category.assoc, ← Category.assoc, hf]
            rfl
          calc
            pullback.lift (f ≫ q ≫ F.map (Stacks.Groupoids.ActionGroupoid.identity G X)) f w ≫
                  comp =
                tbase ≫ F.map (pullback.lift
                  (fY ≫ γ[G, X] ≫ Stacks.Groupoids.ActionGroupoid.identity G X) fY wY ≫
                  Stacks.Groupoids.ActionGroupoid.composition G X) :=
              comp_pair_factor tbase _ _ wY _ _ hu hf w
            _ = tbase ≫ F.map fY := by rw [H_Y.left_identity TY fY wY]
            _ = f := hf
        right_identity := by
          intros T f w
          let TY := actionTestObject Y f
          let fY := actionTestMap Y f
          let tbase := actionTestBase Y f
          have hf : tbase ≫ F.map fY = f := actionTest_factor Y f
          let vY := fY ≫ snd G X ≫ Stacks.Groupoids.ActionGroupoid.identity G X
          have wY : fY ≫ snd G X = vY ≫ γ[G, X] := by
            calc
              fY ≫ snd G X = fY ≫ snd G X ≫ 𝟙 X := by simp
              _ = fY ≫ snd G X ≫ (Stacks.Groupoids.ActionGroupoid.identity G X ≫ γ[G, X]) := by
                    rw [← H_Y.target_identity]
              _ = vY ≫ γ[G, X] := by simp [vY, Category.assoc]
          have wY' : fY ≫ H_Y.source = (fY ≫ H_Y.source ≫ H_Y.identity) ≫ H_Y.target := by
            simpa [H_Y, vY] using wY
          let v := f ≫ p ≫ F.map (Stacks.Groupoids.ActionGroupoid.identity G X)
          have hv : tbase ≫ F.map vY = v := by
            calc
              tbase ≫ F.map vY =
                  (tbase ≫ F.map fY) ≫ p ≫
                      F.map (Stacks.Groupoids.ActionGroupoid.identity G X) := by
                    simp [vY, p, F.map_comp, Category.assoc]
              _ = v := congrArg (fun k : T ⟶ F.obj (G ⊗ X) =>
                    k ≫ p ≫ F.map (Stacks.Groupoids.ActionGroupoid.identity G X)) hf
          calc
            pullback.lift f v w ≫ comp =
                tbase ≫
                    F.map (pullback.lift fY vY wY ≫
                      Stacks.Groupoids.ActionGroupoid.composition G X) :=
                  comp_pair_factor tbase fY vY wY f v hf hv w
            _ = tbase ≫ F.map fY := by
                  rw [H_Y.right_identity TY fY wY']
            _ = f := hf
        left_inverse := by
          intros T f w
          let TY := actionTestObject Y f
          let fY := actionTestMap Y f
          let tbase := actionTestBase Y f
          have hf : tbase ≫ F.map fY = f := actionTest_factor Y f
          let uY := fY ≫ actionInverse Y G X
          have wY : uY ≫ snd G X = fY ≫ γ[G, X] := by
            simp [uY, actionInverse, Stacks.Groupoids.ActionGroupoid.inverse]
          have wY' : (fY ≫ H_Y.inverse) ≫ H_Y.source = fY ≫ H_Y.target := by
            simp [H_Y, actionInverse, Stacks.Groupoids.ActionGroupoid.inverse]
          let u := f ≫ F.map (actionInverse Y G X)
          have hu : tbase ≫ F.map uY = u := by
            calc
              tbase ≫ F.map uY = (tbase ≫ F.map fY) ≫ F.map (actionInverse Y G X) := by
                simp [uY, F.map_comp, Category.assoc]
              _ = u := congrArg (fun k : T ⟶ F.obj (G ⊗ X) =>
                    k ≫ F.map (actionInverse Y G X)) hf
          calc
            pullback.lift u f w ≫ comp =
                tbase ≫
                    F.map (pullback.lift uY fY wY ≫
                      Stacks.Groupoids.ActionGroupoid.composition G X) :=
                  comp_pair_factor tbase uY fY wY u f hu hf w
            _ = tbase ≫ F.map (fY ≫ snd G X ≫ Stacks.Groupoids.ActionGroupoid.identity G X) := by
                  rw [H_Y.left_inverse TY fY wY']
            _ = f ≫ p ≫ F.map (Stacks.Groupoids.ActionGroupoid.identity G X) := by
                  calc
                    tbase ≫ F.map (fY ≫ snd G X ≫ Stacks.Groupoids.ActionGroupoid.identity G X) =
                        (tbase ≫ F.map fY) ≫ p ≫
                            F.map (Stacks.Groupoids.ActionGroupoid.identity G X) := by
                          simp [p, F.map_comp, Category.assoc]
                    _ = f ≫ p ≫ F.map (Stacks.Groupoids.ActionGroupoid.identity G X) :=
                          congrArg (fun k : T ⟶ F.obj (G ⊗ X) =>
                            k ≫ p ≫ F.map (Stacks.Groupoids.ActionGroupoid.identity G X)) hf
        right_inverse := by
          intros T f w
          let TY := actionTestObject Y f
          let fY := actionTestMap Y f
          let tbase := actionTestBase Y f
          have hf : tbase ≫ F.map fY = f := actionTest_factor Y f
          let vY := fY ≫ actionInverse Y G X
          have wY : fY ≫ snd G X = vY ≫ γ[G, X] := by
            simpa [vY, H_Y, Category.assoc] using
              (congrArg (fun k => fY ≫ k) H_Y.target_inverse).symm
          have wY' : fY ≫ H_Y.source = (fY ≫ H_Y.inverse) ≫ H_Y.target := by
            simpa [H_Y, actionInverse, Stacks.Groupoids.ActionGroupoid.inverse, vY] using wY
          let v := f ≫ F.map (actionInverse Y G X)
          have hv : tbase ≫ F.map vY = v := by
            calc
              tbase ≫ F.map vY = (tbase ≫ F.map fY) ≫ F.map (actionInverse Y G X) := by
                simp [vY, F.map_comp, Category.assoc]
              _ = v := congrArg (fun k : T ⟶ F.obj (G ⊗ X) =>
                    k ≫ F.map (actionInverse Y G X)) hf
          calc
            pullback.lift f v w ≫ comp =
                tbase ≫
                    F.map (pullback.lift fY vY wY ≫
                      Stacks.Groupoids.ActionGroupoid.composition G X) :=
                  comp_pair_factor tbase fY vY wY f v hf hv w
            _ = tbase ≫ F.map (fY ≫ γ[G, X] ≫ Stacks.Groupoids.ActionGroupoid.identity G X) := by
                  rw [H_Y.right_inverse TY fY wY']
            _ = f ≫ q ≫ F.map (Stacks.Groupoids.ActionGroupoid.identity G X) := by
                  calc
                    tbase ≫ F.map (fY ≫ γ[G, X] ≫ Stacks.Groupoids.ActionGroupoid.identity G X) =
                      (tbase ≫ F.map fY) ≫ q ≫
                          F.map (Stacks.Groupoids.ActionGroupoid.identity G X) := by
                          simp [q, F.map_comp, Category.assoc]
                    _ = f ≫ q ≫ F.map (Stacks.Groupoids.ActionGroupoid.identity G X) :=
                          congrArg (fun k : T ⟶ F.obj (G ⊗ X) =>
                            k ≫ q ≫ F.map (Stacks.Groupoids.ActionGroupoid.identity G X)) hf
        assoc := by
          intros T f g h wfg wgh w₁ w₂
          let TY := actionTestObject Y f
          let fY := actionTestMap Y f
          let tbase := actionTestBase Y f
          have hf : tbase ≫ F.map fY = f := actionTest_factor Y f
          have base_eq (u v : T ⟶ F.obj (G ⊗ X)) (w : u ≫ p = v ≫ q) :
              v.left ≫ (G ⊗ X).hom = u.left ≫ (G ⊗ X).hom := by
            have e : u.left ≫ (snd G X).left = v.left ≫ (γ[G, X]).left := by
              simpa [p, q, F] using congrArg Over.Hom.left w
            calc
              v.left ≫ (G ⊗ X).hom = (v.left ≫ (γ[G, X]).left) ≫ X.hom := by
                simp [Category.assoc]
              _ = (u.left ≫ (snd G X).left) ≫ X.hom := by rw [e]
              _ = u.left ≫ (G ⊗ X).hom := by
                simpa [Category.assoc] using
                  congrArg (fun k => u.left ≫ k) (Over.w (snd G X))
          have gBase := base_eq f g wfg
          have hBase := (base_eq g h wgh).trans gBase
          have wfgLeft : f.left ≫ (snd G X).left = g.left ≫ (γ[G, X]).left := by
            simpa [p, q, F] using congrArg Over.Hom.left wfg
          have wghLeft : g.left ≫ (snd G X).left = h.left ≫ (γ[G, X]).left := by
            simpa [p, q, F] using congrArg Over.Hom.left wgh
          let gY : TY ⟶ G ⊗ X := Over.homMk g.left (by
            change g.left ≫ (G ⊗ X).hom = f.left ≫ (G ⊗ X).hom
            exact gBase)
          let hY : TY ⟶ G ⊗ X := Over.homMk h.left (by
            change h.left ≫ (G ⊗ X).hom = f.left ≫ (G ⊗ X).hom
            exact hBase)
          have hg : tbase ≫ F.map gY = g := by
            apply Over.OverMorphism.ext
            change 𝟙 T.left ≫ g.left = g.left
            simp
          have hh : tbase ≫ F.map hY = h := by
            apply Over.OverMorphism.ext
            change 𝟙 T.left ≫ h.left = h.left
            simp
          have wfgY : fY ≫ snd G X = gY ≫ γ[G, X] := by
            apply Over.OverMorphism.ext
            exact wfgLeft
          have wghY : gY ≫ snd G X = hY ≫ γ[G, X] := by
            apply Over.OverMorphism.ext
            exact wghLeft
          let pairFGY := pullback.lift fY gY wfgY
          let pairGHY := pullback.lift gY hY wghY
          have w1Y :
              (pairFGY ≫ Stacks.Groupoids.ActionGroupoid.composition G X) ≫ snd G X =
                hY ≫ γ[G, X] := by
            calc
              (pairFGY ≫ Stacks.Groupoids.ActionGroupoid.composition G X) ≫ snd G X =
                  pairFGY ≫ (Stacks.Groupoids.ActionGroupoid.composition G X ≫ snd G X) := by
                    rw [Category.assoc]
              _ = pairFGY ≫ (pullback.snd (snd G X) γ[G, X] ≫ snd G X) := by
                    rw [actionComposition_source]
              _ = gY ≫ snd G X := by
                    rw [← Category.assoc, pullback.lift_snd]
              _ = hY ≫ γ[G, X] := wghY
          have w2Y : fY ≫ snd G X =
              (pairGHY ≫ Stacks.Groupoids.ActionGroupoid.composition G X) ≫ γ[G, X] := by
            calc
              fY ≫ snd G X = gY ≫ γ[G, X] := wfgY
              _ = pairGHY ≫ (Stacks.Groupoids.ActionGroupoid.composition G X ≫ γ[G, X]) := by
                    rw [actionComposition_target, ← Category.assoc, pullback.lift_fst]
          let fgY := pairFGY ≫ Stacks.Groupoids.ActionGroupoid.composition G X
          let ghY := pairGHY ≫ Stacks.Groupoids.ActionGroupoid.composition G X
          let fg := pullback.lift f g wfg ≫ comp
          let gh := pullback.lift g h wgh ≫ comp
          have hfg : tbase ≫ F.map fgY = fg := by
            dsimp [fg, fgY]
            exact (comp_pair_factor tbase fY gY wfgY f g hf hg wfg).symm
          have hgh : tbase ≫ F.map ghY = gh := by
            dsimp [gh, ghY]
            exact (comp_pair_factor tbase gY hY wghY g h hg hh wgh).symm
          calc
            pullback.lift fg h w₁ ≫ comp =
                tbase ≫
                    F.map (pullback.lift fgY hY w1Y ≫
                      Stacks.Groupoids.ActionGroupoid.composition G X) :=
                  comp_pair_factor tbase fgY hY w1Y fg h hfg hh w₁
            _ = tbase ≫
                    F.map (pullback.lift fY ghY w2Y ≫
                      Stacks.Groupoids.ActionGroupoid.composition G X) := by
                  exact congrArg (fun k => tbase ≫ F.map k)
                    (H_Y.assoc TY fY gY hY wfgY wghY w1Y w2Y)
            _ = pullback.lift f gh w₂ ≫ comp := by
                  symm
                  exact comp_pair_factor tbase fY ghY w2Y f gh hf hgh w₂ }
  refine
    { groupoid := H
      objects_eq := rfl
      arrows_eq := rfl
      source_eq := HEq.rfl
      target_eq := HEq.rfl
      compositionDomainIso := iso
      compositionDomainIso_fst := hp
      compositionDomainIso_snd := hq
      comp_eq := by rfl
      identity_eq := by rfl
      inverse_eq := by rfl }

end AlgebraicGeometry

end
