module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The stabilizer action on the arrows of a groupoid scheme

For a groupoid scheme, its stabilizer group scheme acts from the left on the arrow scheme
viewed over the object scheme by the target morphism.  On generalized points, this action is
composition in the groupoid.

## Main definitions

* `AlgebraicGeometry.arrowsOverTarget` is the arrow scheme viewed over the object scheme by the
  target morphism.
* `AlgebraicGeometry.stabilizerAction` equips it with the canonical action of the stabilizer.

## Main results

* `AlgebraicGeometry.stabilizer_smul_arrow` identifies the action on generalized points with
  groupoid composition.

## References

* [Stacks Project, Tag 0237](https://stacks.math.columbia.edu/tag/0237)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory MonObj
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The arrow scheme of a groupoid scheme, regarded as a scheme over its object scheme via the
target morphism. -/
noncomputable abbrev arrowsOverTarget {S : Scheme.{u}} (G : GroupoidScheme S) :
    Over G.objects.left :=
  Over.mk G.target.left

/-- A generalized point of the arrow scheme over the target, regarded as a generalized arrow
of the groupoid over the original base. -/
noncomputable def arrowOverTargetHom {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over G.objects.left} (r : T ⟶ arrowsOverTarget G) :
    (Over.map G.objects.hom).obj T ⟶ G.arrows :=
  Over.homMk r.left (by
    calc
      r.left ≫ G.arrows.hom = r.left ≫ G.target.left ≫ G.objects.hom := by
        rw [← G.target.w]
      _ = T.hom ≫ G.objects.hom := by
        have hr : r.left ≫ G.target.left = T.hom := by
          simpa [arrowsOverTarget] using r.w
        exact congrArg (fun k ↦ k ≫ G.objects.hom) hr)

/-- A generalized arrow over its target has target equal to its object over the object
scheme. -/
lemma arrowOverTargetHom_target {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over G.objects.left} (r : T ⟶ arrowsOverTarget G) :
    arrowOverTargetHom G r ≫ G.target = Over.homMk T.hom := by
  ext
  exact r.w

/-- A stabilizer arrow and an arrow lying over the same target are composable in the
groupoid. -/
lemma stabilizerArrowHom_arrowOverTarget_composable {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over G.objects.left} (g : T ⟶ stabilizer G) (r : T ⟶ arrowsOverTarget G) :
    stabilizerArrowHom G g ≫ G.source = arrowOverTargetHom G r ≫ G.target :=
  (stabilizerArrowHom_source G g).trans (arrowOverTargetHom_target G r).symm

/-- A `ModObj` structure is the stabilizer action induced by groupoid composition when its
action on every pair of generalized points is their groupoid composite. -/
def IsStabilizerAction {S : Scheme.{u}} (G : GroupoidScheme S)
    (h : ModObj (stabilizer G) (arrowsOverTarget G)) : Prop :=
  letI := h
  ∀ (T : Over G.objects.left) (g : T ⟶ stabilizer G) (r : T ⟶ arrowsOverTarget G),
    arrowOverTargetHom G (lift g r ≫ γ[stabilizer G, arrowsOverTarget G]) =
      G.compose (stabilizerArrowHom G g) (arrowOverTargetHom G r)
        (stabilizerArrowHom_arrowOverTarget_composable G g r)

/-- The action morphism of the stabilizer on the arrows over the target: on generalized points
it is composition in the groupoid. -/
noncomputable def stabilizerActionMap {S : Scheme.{u}}
    (G : GroupoidScheme S) :
    stabilizer G ⊗ arrowsOverTarget G ⟶ arrowsOverTarget G := by
  let T : Over G.objects.left := stabilizer G ⊗ arrowsOverTarget G
  let g : (Over.map G.objects.hom).obj T ⟶ G.arrows :=
    stabilizerArrowHom G (fst (stabilizer G) (arrowsOverTarget G))
  let r : (Over.map G.objects.hom).obj T ⟶ G.arrows :=
    arrowOverTargetHom G (snd (stabilizer G) (arrowsOverTarget G))
  let c : (Over.map G.objects.hom).obj T ⟶ G.arrows :=
    G.compose g r (stabilizerArrowHom_arrowOverTarget_composable G
      (fst (stabilizer G) (arrowsOverTarget G))
      (snd (stabilizer G) (arrowsOverTarget G)))
  exact Over.homMk c.left (by
    change c.left ≫ G.target.left = T.hom
    calc
      c.left ≫ G.target.left = g.left ≫ G.target.left := by
        have htarget : G.comp.left ≫ G.target.left =
            (pullback.fst G.source G.target).left ≫ G.target.left :=
          congrArg Over.Hom.left G.target_comp
        have hlift : (pullback.lift g r
            (stabilizerArrowHom_arrowOverTarget_composable G
              (fst (stabilizer G) (arrowsOverTarget G))
              (snd (stabilizer G) (arrowsOverTarget G)))).left ≫
              (pullback.fst G.source G.target).left = g.left :=
          congrArg Over.Hom.left (pullback.lift_fst g r _)
        change (pullback.lift g r _).left ≫ G.comp.left ≫ G.target.left = _
        calc
          _ = (pullback.lift g r _).left ≫
              (pullback.fst G.source G.target).left ≫ G.target.left := by
            rw [htarget]
          _ = g.left ≫ G.target.left := by rw [← Category.assoc, hlift]
      _ = T.hom := congrArg Over.Hom.left
        (stabilizerArrowHom_target G (fst (stabilizer G) (arrowsOverTarget G))))

/-- The generalized arrow attached to a generalized point of the arrows over the target is
natural in the test object. -/
lemma arrowOverTargetHom_comp {S : Scheme.{u}} (G : GroupoidScheme S)
    {T U : Over G.objects.left} (k : T ⟶ U)
    (r : U ⟶ arrowsOverTarget G) :
    arrowOverTargetHom G (k ≫ r) =
      (Over.map G.objects.hom).map k ≫ arrowOverTargetHom G r := by
  apply Over.OverMorphism.ext
  rfl

/-- A generalized point of the arrows over the target is determined by the generalized arrow it
induces. -/
lemma arrowOverTargetHom_injective {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over G.objects.left} {f g : T ⟶ arrowsOverTarget G}
    (h : arrowOverTargetHom G f = arrowOverTargetHom G g) : f = g :=
  Over.OverMorphism.ext (congrArg (fun k => k.left) h)

/-- The action morphism evaluated on a pair of generalized points is their groupoid
composite. -/
lemma stabilizerActionMap_apply {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over G.objects.left} (g : T ⟶ stabilizer G)
    (r : T ⟶ arrowsOverTarget G) :
    arrowOverTargetHom G (lift g r ≫ stabilizerActionMap G) =
      G.compose (stabilizerArrowHom G g) (arrowOverTargetHom G r)
        (stabilizerArrowHom_arrowOverTarget_composable G g r) := by
  let P : Over G.objects.left := stabilizer G ⊗ arrowsOverTarget G
  let a : (Over.map G.objects.hom).obj P ⟶ G.arrows :=
    stabilizerArrowHom G (fst (stabilizer G) (arrowsOverTarget G))
  let b : (Over.map G.objects.hom).obj P ⟶ G.arrows :=
    arrowOverTargetHom G (snd (stabilizer G) (arrowsOverTarget G))
  let w := stabilizerArrowHom_arrowOverTarget_composable G
    (fst (stabilizer G) (arrowsOverTarget G))
    (snd (stabilizer G) (arrowsOverTarget G))
  let k : (Over.map G.objects.hom).obj T ⟶ (Over.map G.objects.hom).obj P :=
    (Over.map G.objects.hom).map (lift g r)
  have ha : k ≫ a = stabilizerArrowHom G g := by
    apply Over.OverMorphism.ext
    change (lift g r).left ≫ (fst (stabilizer G) (arrowsOverTarget G)).left ≫
      stabilizerArrow G = g.left ≫ stabilizerArrow G
    have hf := congrArg Over.Hom.left (lift_fst g r)
    exact congrArg (fun z => z ≫ stabilizerArrow G) hf
  have hb : k ≫ b = arrowOverTargetHom G r := by
    apply Over.OverMorphism.ext
    change (lift g r).left ≫ (snd (stabilizer G) (arrowsOverTarget G)).left = r.left
    exact congrArg Over.Hom.left (lift_snd g r)
  have hbase : arrowOverTargetHom G (stabilizerActionMap G) = G.compose a b w := by
    apply Over.OverMorphism.ext
    rfl
  rw [arrowOverTargetHom_comp, hbase, groupoidCompose_pre G k a b w]
  simp only [ha, hb]

/-- The unit of the stabilizer group structure is the identity arrow. -/
lemma stabilizerOne_eq_unit {S : Scheme.{u}} (G : GroupoidScheme S) :
    stabilizerOne G = (η[stabilizer G] : 𝟙_ (Over G.objects.left) ⟶ stabilizer G) := by
  let T : Over S := (Over.map G.objects.hom).obj (𝟙_ (Over G.objects.left))
  let b : T ⟶ G.objects := Over.homMk (𝟙 G.objects.left)
  have hm : lift (η[stabilizer G])
      (𝟙 (𝟙_ (Over G.objects.left)) ≫ stabilizerOne G) ≫ μ[stabilizer G] =
      𝟙 (𝟙_ (Over G.objects.left)) ≫ stabilizerOne G := by
    let _ : ModObj (stabilizer G) (stabilizer G) := ModObj.regular (stabilizer G)
    change (1 : (𝟙_ (Over G.objects.left) ⟶ stabilizer G)) •
      (𝟙 (𝟙_ (Over G.objects.left)) ≫ stabilizerOne G) = _
    exact one_smul (𝟙_ (Over G.objects.left) ⟶ stabilizer G)
      (𝟙 (𝟙_ (Over G.objects.left)) ≫ stabilizerOne G)
  have hc' : stabilizerArrowHom G
      (𝟙 (𝟙_ (Over G.objects.left)) ≫ stabilizerOne G) =
      G.compose (stabilizerArrowHom G (η[stabilizer G]))
        (stabilizerArrowHom G (𝟙 (𝟙_ (Over G.objects.left)) ≫ stabilizerOne G))
        (stabilizerArrowHom_composable G (η[stabilizer G])
          (𝟙 (𝟙_ (Over G.objects.left)) ≫ stabilizerOne G)) := by
    simpa only [hm] using stabilizer_mul_comp_arrow G (𝟙_ (Over G.objects.left))
      (η[stabilizer G]) (𝟙 (𝟙_ (Over G.objects.left)) ≫ stabilizerOne G)
  have hid : stabilizerArrowHom G
      (𝟙 (𝟙_ (Over G.objects.left)) ≫ stabilizerOne G) =
      b ≫ G.identity := by
    simpa [b, T, Over.tensorUnit_hom] using
      stabilizerArrowHom_stabilizerOne G (𝟙 (𝟙_ (Over G.objects.left)))
  have hsec : stabilizerArrowHom G
      (𝟙 (𝟙_ (Over G.objects.left)) ≫ stabilizerOne G) =
      (stabilizerArrowHom G (η[stabilizer G]) ≫ G.source) ≫ G.identity := by
    have hs := stabilizerArrowHom_source G (η[stabilizer G])
    change stabilizerArrowHom G (η[stabilizer G]) ≫ G.source = b at hs
    rw [hid, hs]
  have hright : G.compose (stabilizerArrowHom G (η[stabilizer G]))
      ((stabilizerArrowHom G (η[stabilizer G]) ≫ G.source) ≫ G.identity)
      (by simp [Category.assoc, G.target_identity]) =
      stabilizerArrowHom G (η[stabilizer G]) := by
    simpa [GroupoidScheme.compose] using
      G.right_identity ((Over.map G.objects.hom).obj (𝟙_ (Over G.objects.left)))
        (stabilizerArrowHom G (η[stabilizer G])) (by
          simp [Category.assoc, G.target_identity])
  have hr : G.compose (stabilizerArrowHom G (η[stabilizer G]))
      (stabilizerArrowHom G (𝟙 (𝟙_ (Over G.objects.left)) ≫ stabilizerOne G))
      (stabilizerArrowHom_composable G (η[stabilizer G])
        (𝟙 (𝟙_ (Over G.objects.left)) ≫ stabilizerOne G)) =
      stabilizerArrowHom G (η[stabilizer G]) := by
    simpa only [hsec, ← Category.assoc] using hright
  simpa only [Category.id_comp] using stabilizerArrowHom_injective G (hc'.trans hr)

/-- The stabilizer group scheme acts canonically on the arrow scheme over the object scheme via
the target map; the action is induced by composition in the groupoid. -/
@[stacks 0237]
noncomputable def stabilizerAction {S : Scheme.{u}} (G : GroupoidScheme S) :
    { h : ModObj (stabilizer G) (arrowsOverTarget G) // IsStabilizerAction G h } := by
  let h : ModObj (stabilizer G) (arrowsOverTarget G) :=
    { smul := stabilizerActionMap G
      one_smul := by
        change η ▷ arrowsOverTarget G ≫ stabilizerActionMap G =
          (λ_ (arrowsOverTarget G)).hom
        rw [← lift_comp_fst_snd (η[stabilizer G] ▷ arrowsOverTarget G)]
        simp only [whiskerRight_fst, whiskerRight_snd]
        apply Over.OverMorphism.ext
        let T : Over G.objects.left := 𝟙_ (Over G.objects.left) ⊗ arrowsOverTarget G
        let k : T ⟶ 𝟙_ (Over G.objects.left) := fst _ _
        let g : T ⟶ stabilizer G := k ≫ η[stabilizer G]
        let r : T ⟶ arrowsOverTarget G := snd _ _
        change (lift g r).left ≫ (stabilizerActionMap G).left =
          (λ_ (arrowsOverTarget G)).hom.left
        let q := arrowOverTargetHom G r
        have hg : stabilizerArrowHom G g = q ≫ G.target ≫ G.identity := by
          change stabilizerArrowHom G (k ≫ η[stabilizer G]) = _
          rw [← stabilizerOne_eq_unit G]
          calc
            stabilizerArrowHom G (k ≫ stabilizerOne G) =
                Over.homMk T.hom ≫ G.identity :=
                  stabilizerArrowHom_stabilizerOne G k
            _ = (q ≫ G.target) ≫ G.identity :=
                  congrArg (fun z => z ≫ G.identity)
                    (arrowOverTargetHom_target G r).symm
            _ = q ≫ G.target ≫ G.identity := Category.assoc _ _ _
        have w : (q ≫ G.target ≫ G.identity) ≫ G.source = q ≫ G.target := by
          simp [Category.assoc, G.source_identity]
        have hcomp : G.compose (stabilizerArrowHom G g) q
            (stabilizerArrowHom_arrowOverTarget_composable G g r) = q := by
          calc
            G.compose (stabilizerArrowHom G g) q
                (stabilizerArrowHom_arrowOverTarget_composable G g r) =
                G.compose (q ≫ G.target ≫ G.identity) q w := by
              simp only [hg]
            _ = q := by
              simpa [GroupoidScheme.compose] using
                G.left_identity ((Over.map G.objects.hom).obj T) q w
        have hact := congrArg Over.Hom.left (stabilizerActionMap_apply G g r)
        have hact' : (lift g r).left ≫ (stabilizerActionMap G).left =
            (G.compose (stabilizerArrowHom G g) q
              (stabilizerArrowHom_arrowOverTarget_composable G g r)).left := by
          simpa [q, arrowOverTargetHom] using hact
        rw [hact', congrArg Over.Hom.left hcomp]
        simp [q, r, arrowOverTargetHom, Over.leftUnitor_hom_left]
      mul_smul := by
        change μ[stabilizer G] ▷ arrowsOverTarget G ≫ stabilizerActionMap G =
          (α_ (stabilizer G) (stabilizer G) (arrowsOverTarget G)).hom ≫
            stabilizer G ◁ stabilizerActionMap G ≫ stabilizerActionMap G
        let T : Over G.objects.left :=
          (stabilizer G ⊗ stabilizer G) ⊗ arrowsOverTarget G
        let p12 : T ⟶ stabilizer G ⊗ stabilizer G := fst _ _
        let p3 : T ⟶ arrowsOverTarget G := snd _ _
        let p1 : T ⟶ stabilizer G := p12 ≫ fst _ _
        let p2 : T ⟶ stabilizer G := p12 ≫ snd _ _
        let m : T ⟶ stabilizer G := p12 ≫ μ[stabilizer G]
        let inner : T ⟶ arrowsOverTarget G := lift p2 p3 ≫ stabilizerActionMap G
        let leftPair : T ⟶ stabilizer G ⊗ arrowsOverTarget G := lift m p3
        let rightPair : T ⟶ stabilizer G ⊗ arrowsOverTarget G := lift p1 inner
        have hleftPair : leftPair = μ[stabilizer G] ▷ arrowsOverTarget G := by
          apply hom_ext
          · simp [leftPair, m, p12, p3]
          · simp [leftPair, p3]
        have hαsnd :
            (α_ (stabilizer G) (stabilizer G) (arrowsOverTarget G)).hom ≫
                snd (stabilizer G) (stabilizer G ⊗ arrowsOverTarget G) = lift p2 p3 := by
          apply hom_ext
          · simp [p2, p12]
          · simp [p3]
        have hrightPair : rightPair =
            (α_ (stabilizer G) (stabilizer G) (arrowsOverTarget G)).hom ≫
              stabilizer G ◁ stabilizerActionMap G := by
          apply hom_ext
          · simp [rightPair, inner, p1, p12, p3]
          · calc
              lift p1 inner ≫ snd _ _ = inner := lift_snd _ _
              _ = lift p2 p3 ≫ stabilizerActionMap G := rfl
              _ = ((α_ (stabilizer G) (stabilizer G) (arrowsOverTarget G)).hom ≫
                    snd (stabilizer G) (stabilizer G ⊗ arrowsOverTarget G)) ≫
                    stabilizerActionMap G := by rw [hαsnd]
              _ = ((α_ (stabilizer G) (stabilizer G) (arrowsOverTarget G)).hom ≫
                    stabilizer G ◁ stabilizerActionMap G) ≫ snd _ _ := by
                      calc
                        _ = (α_ (stabilizer G) (stabilizer G)
                              (arrowsOverTarget G)).hom ≫
                              (snd (stabilizer G)
                                (stabilizer G ⊗ arrowsOverTarget G) ≫
                                  stabilizerActionMap G) := Category.assoc _ _ _
                        _ = (α_ (stabilizer G) (stabilizer G)
                              (arrowsOverTarget G)).hom ≫
                              (stabilizer G ◁ stabilizerActionMap G ≫
                                snd (stabilizer G) (arrowsOverTarget G)) := by
                                rw [whiskerLeft_snd]
                        _ = _ := (Category.assoc _ _ _).symm
        have hp12 : p12 = lift p1 p2 := by
          apply hom_ext <;> simp [p12, p1, p2]
        have hm : m = lift p1 p2 ≫ μ[stabilizer G] := by
          simp [m, hp12]
        have hwfg : stabilizerArrowHom G p1 ≫ G.source =
            stabilizerArrowHom G p2 ≫ G.target :=
          stabilizerArrowHom_composable G p1 p2
        have wgh : stabilizerArrowHom G p2 ≫ G.source =
            arrowOverTargetHom G p3 ≫ G.target :=
          stabilizerArrowHom_arrowOverTarget_composable G p2 p3
        have wleft :
            (G.compose (stabilizerArrowHom G p1) (stabilizerArrowHom G p2) hwfg) ≫
                G.source = arrowOverTargetHom G p3 ≫ G.target := by
          calc
            _ = pullback.lift (stabilizerArrowHom G p1) (stabilizerArrowHom G p2)
                  hwfg ≫ (G.comp ≫ G.source) := by
                    simp [GroupoidScheme.compose, Category.assoc]
            _ = pullback.lift (stabilizerArrowHom G p1) (stabilizerArrowHom G p2)
                  hwfg ≫ (pullback.snd G.source G.target ≫ G.source) := by
                    rw [G.source_comp]
            _ = stabilizerArrowHom G p2 ≫ G.source := by
                    rw [← Category.assoc, pullback.lift_snd]
            _ = arrowOverTargetHom G p3 ≫ G.target := wgh
        have wright : stabilizerArrowHom G p1 ≫ G.source =
            (G.compose (stabilizerArrowHom G p2) (arrowOverTargetHom G p3) wgh) ≫
              G.target := by
          calc
            _ = stabilizerArrowHom G p1 ≫ G.source := by simp
            _ = stabilizerArrowHom G p2 ≫ G.target := hwfg
            _ = pullback.lift (stabilizerArrowHom G p2) (arrowOverTargetHom G p3)
                  wgh ≫ (pullback.fst G.source G.target ≫ G.target) := by
                    rw [← Category.assoc, pullback.lift_fst]
            _ = pullback.lift (stabilizerArrowHom G p2) (arrowOverTargetHom G p3)
                  wgh ≫ (G.comp ≫ G.target) := by
                    rw [← G.target_comp]
            _ = _ := by
              simp only [GroupoidScheme.compose, Category.assoc]
        have hassoc := G.assoc ((Over.map G.objects.hom).obj T)
          (stabilizerArrowHom G p1) (stabilizerArrowHom G p2)
          (arrowOverTargetHom G p3) hwfg wgh wleft wright
        have hmul := stabilizer_mul_comp_arrow G T p1 p2
        have hprod : stabilizerArrowHom G m =
            G.compose (stabilizerArrowHom G p1) (stabilizerArrowHom G p2) hwfg := by
          rw [hm]
          exact hmul
        have hleftEval : arrowOverTargetHom G (leftPair ≫ stabilizerActionMap G) =
            G.compose (G.compose (stabilizerArrowHom G p1)
              (stabilizerArrowHom G p2) hwfg) (arrowOverTargetHom G p3) wleft := by
          have hpoint := stabilizerActionMap_apply G m p3
          simpa only [leftPair, hprod] using hpoint
        have hinnerEval : arrowOverTargetHom G inner =
            G.compose (stabilizerArrowHom G p2) (arrowOverTargetHom G p3) wgh :=
          stabilizerActionMap_apply G p2 p3
        have hrightEval : arrowOverTargetHom G (rightPair ≫ stabilizerActionMap G) =
            G.compose (stabilizerArrowHom G p1)
              (G.compose (stabilizerArrowHom G p2) (arrowOverTargetHom G p3) wgh)
              wright := by
          have hpoint := stabilizerActionMap_apply G p1 inner
          simpa only [rightPair, hinnerEval] using hpoint
        apply arrowOverTargetHom_injective G
        calc
          arrowOverTargetHom G
              ((μ[stabilizer G] ▷ arrowsOverTarget G) ≫ stabilizerActionMap G) =
              arrowOverTargetHom G (leftPair ≫ stabilizerActionMap G) := by
                rw [← hleftPair]
          _ = G.compose
                (G.compose (stabilizerArrowHom G p1) (stabilizerArrowHom G p2) hwfg)
                (arrowOverTargetHom G p3) wleft := hleftEval
          _ = G.compose (stabilizerArrowHom G p1)
                (G.compose (stabilizerArrowHom G p2) (arrowOverTargetHom G p3) wgh)
                wright := hassoc
          _ = arrowOverTargetHom G
                ((α_ (stabilizer G) (stabilizer G) (arrowsOverTarget G)).hom ≫
                  stabilizer G ◁ stabilizerActionMap G ≫ stabilizerActionMap G) := by
                rw [← Category.assoc, ← hrightPair]
                exact hrightEval.symm }
  refine ⟨h, ?_⟩
  intro T g r
  let _ := h
  exact stabilizerActionMap_apply G g r

/-- The canonical action of the stabilizer on the arrow scheme over the target. -/
noncomputable instance {S : Scheme.{u}} (G : GroupoidScheme S) :
    ModObj (stabilizer G) (arrowsOverTarget G) :=
  (stabilizerAction G).1

/-- The stabilizer action on generalized arrows is composition in the groupoid. -/
lemma stabilizer_smul_arrow {S : Scheme.{u}} (G : GroupoidScheme S)
    (T : Over G.objects.left) (g : T ⟶ stabilizer G) (r : T ⟶ arrowsOverTarget G) :
    arrowOverTargetHom G (lift g r ≫ γ[stabilizer G, arrowsOverTarget G]) =
      G.compose (stabilizerArrowHom G g) (arrowOverTargetHom G r)
        (stabilizerArrowHom_arrowOverTarget_composable G g r) :=
  (stabilizerAction G).2 T g r

end AlgebraicGeometry

end
