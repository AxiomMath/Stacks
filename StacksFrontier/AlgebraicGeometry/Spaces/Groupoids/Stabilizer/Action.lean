module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.GroupStructure

/-!
# The stabilizer acts on the arrows of a groupoid in algebraic spaces

Let `G` be a groupoid in algebraic spaces over `B`, with object space `U` and arrow space `R`.
Reading `R` as an algebraic space over `U` through the target morphism, the stabilizer group
space of `G` acts on it from the left: an arrow whose two endpoints are a point `u` of `U`
composes with any arrow whose target is `u`.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.arrowsOverTarget`: the arrow space, read over
  the object space through the target morphism.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.IsStabilizerAction`: the property of an action
  of the stabilizer on it that it is groupoid composition on generalized points.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerActionMap`: the action morphism.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerAction`: the action exists and is groupoid
  composition.

## Implementation notes

The action is a `CategoryTheory.ModObj` in the slice of presheaves over the object space, whose
cartesian monoidal structure is `AlgebraicGeometry.Space.overCartesianMonoidalCategory`.

## References

* [Stacks Project, Tag 043H](https://stacks.math.columbia.edu/tag/043H)
* [Stacks Project, Tag 043Q](https://stacks.math.columbia.edu/tag/043Q)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 0447](https://stacks.math.columbia.edu/tag/0447)
* [Stacks Project, Tag 0449](https://stacks.math.columbia.edu/tag/0449)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory MonObj

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The arrow space of a groupoid in algebraic spaces, read over the object space through the
target morphism. -/
noncomputable abbrev arrowsOverTarget (G : GroupoidInAlgebraicSpaces C S hS B) :
    Over G.objects.obj :=
  Over.mk G.target.hom

/-- An action of the stabilizer on the arrow space over the object space is *induced by
composition* when on every pair of generalized points it is groupoid composition. -/
def IsStabilizerAction (G : GroupoidInAlgebraicSpaces C S hS B)
    (h : ModObj (stabilizer G) (arrowsOverTarget G)) : Prop :=
  letI := h
  ∀ (T : Over G.objects.obj) (g : T ⟶ stabilizer G) (r : T ⟶ arrowsOverTarget G),
    ∃ (w : (g.left ≫ stabilizerArrow G) ≫ G.source.hom = r.left ≫ G.target.hom),
      (lift g r ≫ γ[stabilizer G, arrowsOverTarget G]).left =
        pullback.lift (g.left ≫ stabilizerArrow G) r.left w ≫ G.comp.hom

/-- A generalized point of the stabilizer is composable before any generalized point of the
arrow space over the object space. -/
theorem stabilizerArrowHom_arrowOverTarget_composable
    (G : GroupoidInAlgebraicSpaces C S hS B) {T : Over G.objects.obj}
    (g : T ⟶ stabilizer G) (r : T ⟶ arrowsOverTarget G) :
    stabilizerArrowHom G g ≫ G.source.hom = r.left ≫ G.target.hom :=
  (stabilizerArrowHom_source G g).trans r.w.symm

/-- The underlying arrow of the unit of the stabilizer is the identity arrow. -/
theorem stabilizerArrowHom_unit (G : GroupoidInAlgebraicSpaces C S hS B) :
    stabilizerArrowHom G (η[stabilizer G]) = (identityArrow G).hom := by
  let T : Over G.objects.obj := 𝟙_ (Over G.objects.obj)
  let f : T ⟶ stabilizer G := η[stabilizer G]
  let g : T ⟶ stabilizer G := stabilizerOne G
  have hmul : lift f g ≫ μ[stabilizer G] = g := MonObj.lift_comp_one_left (𝟙 T) g
  have hcomp : groupoidCompose G (stabilizerArrowHom G f) (stabilizerArrowHom G g)
      (stabilizerArrowHom_composable G f g) = stabilizerArrowHom G g :=
    (stabilizerArrowHom_mul G f g).symm.trans (congrArg (stabilizerArrowHom G) hmul)
  have hid : identityAfterSource G (stabilizerArrowHom G f) = stabilizerArrowHom G g := by
    change stabilizerArrowHom G f ≫ G.source.hom ≫ (identityArrow G).hom = _
    calc
      _ = T.hom ≫ (identityArrow G).hom :=
        congrArg (fun q => q ≫ (identityArrow G).hom) (stabilizerArrowHom_source G f)
      _ = stabilizerArrowHom G g := by
        change T.hom ≫ (identityArrow G).hom = stabilizerArrowHom G (𝟙 T ≫ stabilizerOne G)
        exact (stabilizerArrowHom_one G (𝟙 T)).symm
  have hright : groupoidCompose G (stabilizerArrowHom G f)
      (stabilizerArrowHom G g) (stabilizerArrowHom_composable G f g) =
        stabilizerArrowHom G f := by
    calc
      _ = groupoidCompose G (stabilizerArrowHom G f)
          (identityAfterSource G (stabilizerArrowHom G f))
          (identityAfterSource_composable G _) :=
        groupoidCompose_congr G _ _ rfl hid.symm
      _ = stabilizerArrowHom G f := groupoidCompose_rightIdentity G _
  have heq : stabilizerArrowHom G f = stabilizerArrowHom G g := hright.symm.trans hcomp
  have hunitarrow : stabilizerArrowHom G g = (identityArrow G).hom := by
    have h' : stabilizerArrowHom G g = 𝟙 G.objects.obj ≫ (identityArrow G).hom := by
      simpa [g, T, Over.tensorUnit_hom] using stabilizerArrowHom_one G (𝟙 T)
    exact h'.trans (Category.id_comp _)
  exact heq.trans hunitarrow

/-- The action morphism of the stabilizer on the arrow space over the object space: groupoid
composition. -/
noncomputable def stabilizerActionMap (G : GroupoidInAlgebraicSpaces C S hS B) :
    stabilizer G ⊗ arrowsOverTarget G ⟶ arrowsOverTarget G := by
  let T : Over G.objects.obj := stabilizer G ⊗ arrowsOverTarget G
  let f : T.left ⟶ G.arrows.obj :=
    (fst (stabilizer G) (arrowsOverTarget G)).left ≫ stabilizerArrow G
  let g : T.left ⟶ G.arrows.obj := (snd (stabilizer G) (arrowsOverTarget G)).left
  have w : f ≫ G.source.hom = g ≫ G.target.hom := by
    have hs := stabilizerArrowHom_source G (fst (stabilizer G) (arrowsOverTarget G))
    have ht : g ≫ G.target.hom = T.hom :=
      (snd (stabilizer G) (arrowsOverTarget G)).w.trans
        (fst (stabilizer G) (arrowsOverTarget G)).w
    exact hs.trans ht.symm
  let c := groupoidCompose G f g w
  exact Over.homMk c (by
    change c ≫ G.target.hom = T.hom
    calc
      c ≫ G.target.hom = f ≫ G.target.hom := groupoidCompose_target G f g w
      _ = T.hom := stabilizerArrowHom_target G (fst _ _))

/-- On generalized points the action of the stabilizer is groupoid composition. -/
theorem stabilizerActionMap_apply (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : Over G.objects.obj} (g : T ⟶ stabilizer G) (r : T ⟶ arrowsOverTarget G) :
    (lift g r ≫ stabilizerActionMap G).left =
      groupoidCompose G (stabilizerArrowHom G g) r.left
        (stabilizerArrowHom_arrowOverTarget_composable G g r) := by
  let P : Over G.objects.obj := stabilizer G ⊗ arrowsOverTarget G
  let a : P.left ⟶ G.arrows.obj :=
    (fst (stabilizer G) (arrowsOverTarget G)).left ≫ stabilizerArrow G
  let b : P.left ⟶ G.arrows.obj := (snd (stabilizer G) (arrowsOverTarget G)).left
  let w : a ≫ G.source.hom = b ≫ G.target.hom := stabilizerArrowHom_arrowOverTarget_composable G
    (fst (stabilizer G) (arrowsOverTarget G)) (snd (stabilizer G) (arrowsOverTarget G))
  let k : T.left ⟶ P.left := (lift g r).left
  have ha : k ≫ a = stabilizerArrowHom G g := by
    change (lift g r).left ≫
      (fst (stabilizer G) (arrowsOverTarget G)).left ≫ stabilizerArrow G = _
    exact congrArg (fun z => z ≫ stabilizerArrow G)
      (congrArg Over.Hom.left (lift_fst g r))
  have hb : k ≫ b = r.left := by
    change (lift g r).left ≫ (snd (stabilizer G) (arrowsOverTarget G)).left = _
    exact congrArg Over.Hom.left (lift_snd g r)
  have hw := stabilizerArrowHom_arrowOverTarget_composable G g r
  change (lift g r).left ≫ (stabilizerActionMap G).left = _
  rw [show (stabilizerActionMap G).left = groupoidCompose G a b w from rfl]
  change k ≫ groupoidCompose G a b w = _
  calc
    _ = groupoidCompose G (k ≫ a) (k ≫ b)
        (by
          calc
            (k ≫ a) ≫ G.source.hom = k ≫ (a ≫ G.source.hom) := Category.assoc _ _ _
            _ = k ≫ (b ≫ G.target.hom) := congrArg (fun q => k ≫ q) w
            _ = (k ≫ b) ≫ G.target.hom := (Category.assoc _ _ _).symm) :=
      groupoidCompose_pre G k a b w
    _ = groupoidCompose G (stabilizerArrowHom G g) r.left hw :=
      groupoidCompose_congr G _ _ ha hb

/-- The stabilizer of a groupoid in algebraic spaces acts on its arrow space over the object space,
and the action is groupoid composition on generalized points. -/
@[stacks 0449]
noncomputable def stabilizerAction (G : GroupoidInAlgebraicSpaces C S hS B) :
    { h : ModObj (stabilizer G) (arrowsOverTarget G) // IsStabilizerAction G h } := by
  let h : ModObj (stabilizer G) (arrowsOverTarget G) := {
    smul := stabilizerActionMap G
    one_smul := by
      change η[stabilizer G] ▷ arrowsOverTarget G ≫ stabilizerActionMap G =
        (λ_ (arrowsOverTarget G)).hom
      rw [← lift_comp_fst_snd (η[stabilizer G] ▷ arrowsOverTarget G)]
      simp only [whiskerRight_fst, whiskerRight_snd]
      apply Over.OverMorphism.ext
      let T : Over G.objects.obj := 𝟙_ (Over G.objects.obj) ⊗ arrowsOverTarget G
      let k : T ⟶ 𝟙_ (Over G.objects.obj) := fst _ _
      let g : T ⟶ stabilizer G := k ≫ η[stabilizer G]
      let r : T ⟶ arrowsOverTarget G := snd _ _
      change (lift g r).left ≫ (stabilizerActionMap G).left =
        (λ_ (arrowsOverTarget G)).hom.left
      have hbase : k.left = r.left ≫ G.target.hom := by
        calc
          k.left = T.hom := by simpa [T, Over.tensorUnit_hom] using k.w
          _ = r.left ≫ G.target.hom := r.w.symm
      have hunit := stabilizerArrowHom_unit G
      have hg : stabilizerArrowHom G g = identityAfterTarget G r.left := by
        change k.left ≫ η[stabilizer G].left ≫ stabilizerArrow G = _
        have hη' : k.left ≫ (η[stabilizer G].left ≫ stabilizerArrow G) =
            k.left ≫ (identityArrow G).hom := by
          change k.left ≫ stabilizerArrowHom G (η[stabilizer G]) = _
          exact congrArg (fun q => k.left ≫ q) hunit
        exact hη'.trans ((congrArg (fun q => q ≫ (identityArrow G).hom) hbase).trans
          (Category.assoc _ _ _))
      calc
        (lift g r).left ≫ (stabilizerActionMap G).left =
            groupoidCompose G (stabilizerArrowHom G g) r.left
              (stabilizerArrowHom_arrowOverTarget_composable G g r) :=
          stabilizerActionMap_apply G g r
        _ = groupoidCompose G (identityAfterTarget G r.left) r.left
              (identityAfterTarget_composable G r.left) :=
          groupoidCompose_congr G _ _ hg rfl
        _ = r.left := groupoidCompose_leftIdentity G r.left
        _ = (λ_ (arrowsOverTarget G)).hom.left := by
          simp [r, Over.leftUnitor_hom_left]
    mul_smul := by
      change μ[stabilizer G] ▷ arrowsOverTarget G ≫ stabilizerActionMap G =
        (α_ (stabilizer G) (stabilizer G) (arrowsOverTarget G)).hom ≫
          stabilizer G ◁ stabilizerActionMap G ≫ stabilizerActionMap G
      let T : Over G.objects.obj :=
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
        apply CartesianMonoidalCategory.hom_ext
        · simp [leftPair, m, p12, p3]
        · simp [leftPair, p3]
      have hαsnd : (α_ (stabilizer G) (stabilizer G) (arrowsOverTarget G)).hom ≫
          snd (stabilizer G) (stabilizer G ⊗ arrowsOverTarget G) = lift p2 p3 := by
        apply CartesianMonoidalCategory.hom_ext
        · simp [p2, p12]
        · simp [p3]
      have hrightPair : rightPair =
          (α_ (stabilizer G) (stabilizer G) (arrowsOverTarget G)).hom ≫
            stabilizer G ◁ stabilizerActionMap G := by
        apply CartesianMonoidalCategory.hom_ext
        · simp [rightPair, inner, p1, p12, p3]
        · calc
            lift p1 inner ≫ snd _ _ = inner := lift_snd _ _
            _ = lift p2 p3 ≫ stabilizerActionMap G := rfl
            _ = ((α_ (stabilizer G) (stabilizer G) (arrowsOverTarget G)).hom ≫
                snd (stabilizer G) (stabilizer G ⊗ arrowsOverTarget G)) ≫
                  stabilizerActionMap G :=
              congrArg (fun q => q ≫ stabilizerActionMap G) hαsnd.symm
            _ = ((α_ (stabilizer G) (stabilizer G) (arrowsOverTarget G)).hom ≫
                stabilizer G ◁ stabilizerActionMap G) ≫
                  snd (stabilizer G) (arrowsOverTarget G) := by
              calc
                _ = (α_ (stabilizer G) (stabilizer G) (arrowsOverTarget G)).hom ≫
                    (snd (stabilizer G) (stabilizer G ⊗ arrowsOverTarget G) ≫
                      stabilizerActionMap G) := Category.assoc _ _ _
                _ = (α_ (stabilizer G) (stabilizer G) (arrowsOverTarget G)).hom ≫
                    (stabilizer G ◁ stabilizerActionMap G ≫
                      snd (stabilizer G) (arrowsOverTarget G)) := by
                  rw [whiskerLeft_snd]
                _ = _ := (Category.assoc _ _ _).symm
      have hp12 : p12 = lift p1 p2 := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [p12, p1, p2]
      have hm : m = lift p1 p2 ≫ μ[stabilizer G] := by
        simp [m, hp12]
      have hwfg := stabilizerArrowHom_composable G p1 p2
      have wgh := stabilizerArrowHom_arrowOverTarget_composable G p2 p3
      have wleft : groupoidCompose G (stabilizerArrowHom G p1)
          (stabilizerArrowHom G p2) hwfg ≫ G.source.hom = p3.left ≫ G.target.hom := by
        rwa [groupoidCompose_source]
      have wright : stabilizerArrowHom G p1 ≫ G.source.hom =
          groupoidCompose G (stabilizerArrowHom G p2) p3.left wgh ≫ G.target.hom := by
        rwa [groupoidCompose_target]
      have hassoc := groupoidCompose_assoc G (stabilizerArrowHom G p1)
        (stabilizerArrowHom G p2) p3.left hwfg wgh wleft wright
      obtain ⟨wm, hmul⟩ := stabilizer_mul_comp_arrow G T p1 p2
      have hprod : stabilizerArrowHom G m =
          groupoidCompose G (stabilizerArrowHom G p1) (stabilizerArrowHom G p2) hwfg := by
        have hchar : stabilizerArrowHom G (lift p1 p2 ≫ μ[stabilizer G]) =
            groupoidCompose G (stabilizerArrowHom G p1)
              (stabilizerArrowHom G p2) hwfg := by
          change (lift p1 p2 ≫ μ[stabilizer G]).left ≫ stabilizerArrow G = _ at hmul
          exact hmul.trans (groupoidCompose_eq_comp G _ _ hwfg).symm
        rwa [hm]
      have hleftEval : (leftPair ≫ stabilizerActionMap G).left =
          groupoidCompose G (groupoidCompose G (stabilizerArrowHom G p1)
            (stabilizerArrowHom G p2) hwfg) p3.left wleft := by
        simpa only [leftPair, hprod] using stabilizerActionMap_apply G m p3
      have hinnerEval : inner.left =
          groupoidCompose G (stabilizerArrowHom G p2) p3.left wgh :=
        stabilizerActionMap_apply G p2 p3
      have hrightEval : (rightPair ≫ stabilizerActionMap G).left =
          groupoidCompose G (stabilizerArrowHom G p1)
            (groupoidCompose G (stabilizerArrowHom G p2) p3.left wgh) wright := by
        simpa only [rightPair, hinnerEval] using stabilizerActionMap_apply G p1 inner
      apply Over.OverMorphism.ext
      calc
        (μ[stabilizer G] ▷ arrowsOverTarget G ≫ stabilizerActionMap G).left =
            (leftPair ≫ stabilizerActionMap G).left := by rw [← hleftPair]
        _ = groupoidCompose G (groupoidCompose G (stabilizerArrowHom G p1)
              (stabilizerArrowHom G p2) hwfg) p3.left wleft := hleftEval
        _ = groupoidCompose G (stabilizerArrowHom G p1)
              (groupoidCompose G (stabilizerArrowHom G p2) p3.left wgh) wright := hassoc
        _ = ((α_ (stabilizer G) (stabilizer G) (arrowsOverTarget G)).hom ≫
              stabilizer G ◁ stabilizerActionMap G ≫ stabilizerActionMap G).left := by
          rw [← Category.assoc, ← hrightPair]
          exact hrightEval.symm }
  refine ⟨h, ?_⟩
  intro T g r
  let _ := h
  refine ⟨stabilizerArrowHom_arrowOverTarget_composable G g r, ?_⟩
  change (lift g r ≫ stabilizerActionMap G).left = _
  calc
    (lift g r ≫ stabilizerActionMap G).left =
        groupoidCompose G (stabilizerArrowHom G g) r.left
          (stabilizerArrowHom_arrowOverTarget_composable G g r) :=
      stabilizerActionMap_apply G g r
    _ = pullback.lift (stabilizerArrowHom G g) r.left
          (stabilizerArrowHom_arrowOverTarget_composable G g r) ≫ G.comp.hom :=
      groupoidCompose_eq_comp G _ _ _

/-- The canonical action of the stabilizer on the arrow space over the object space. -/
noncomputable instance (G : GroupoidInAlgebraicSpaces C S hS B) :
    ModObj (stabilizer G) (arrowsOverTarget G) :=
  (stabilizerAction G).1

end AlgebraicGeometry.GroupoidInAlgebraicSpaces
