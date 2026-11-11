module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic

/-!
# Generalized points of a groupoid scheme, and the squares of its composition diagram

Evaluating a groupoid scheme on a test scheme over the base yields an honest groupoid, whose
objects are the generalized objects and whose arrows are the generalized arrows with prescribed
source and target. The two lower squares and the top triangle (read as a square) of the
composition diagram of a groupoid scheme are cartesian.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.Evaluation` is the type of generalized objects over a test
  scheme.
* `Stacks.Groupoids.GroupoidScheme.EvaluationHom` is the type of generalized arrows with a
  prescribed source and target.
* `Stacks.Groupoids.GroupoidScheme.evaluationGroupoid` is the resulting groupoid structure.

## Main results

* `Stacks.Groupoids.GroupoidScheme.fst_snd_isPullback` records the defining square of the
  scheme of composable arrows as the lower-left square of the composition diagram.
* `Stacks.Groupoids.GroupoidScheme.comp_source_isPullback` says that composition together with
  the second projection exhibits the scheme of composable arrows as the fibre product of the
  source map with itself.
* `Stacks.Groupoids.GroupoidScheme.target_comp_isPullback` says that the first projection
  together with composition exhibits it as the fibre product of the target map with itself.

## Implementation notes

In a groupoid, a pair of arrows `(α, β)` with the same target corresponds to the composable
pair `(α, α⁻¹ ∘ β)`, and a composable pair `(α, β)` with `α ∘ β` prescribed determines `β`
from `α`. Both statements are bijections of generalized points, so both squares are cartesian
by Yoneda; the argument is carried out in
`Stacks.Groupoids.GroupoidScheme.evaluationGroupoid`.

## References

* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
* [Stacks Project, Tag 02YE](https://stacks.math.columbia.edu/tag/02YE)
* [Stacks Project, Tag 04LF](https://stacks.math.columbia.edu/tag/04LF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids.GroupoidScheme

/-- Objects of the groupoid obtained by evaluating a groupoid scheme on a test scheme. -/
@[implicit_reducible]
def Evaluation {S : Scheme.{u}} (G : GroupoidScheme S) (T : Over S) :=
  T ⟶ G.objects

/-- An arrow between two generalized objects is a generalized arrow with the prescribed source
and target. -/
@[ext]
structure EvaluationHom {S : Scheme.{u}} (G : GroupoidScheme S) {T : Over S}
    (x y : G.Evaluation T) where
  /-- The corresponding generalized arrow of the arrow scheme. -/
  arrow : T ⟶ G.arrows
  /-- The arrow has source `x`. -/
  source_eq : arrow ≫ G.source = x
  /-- The arrow has target `y`. -/
  target_eq : arrow ≫ G.target = y

/-- Evaluation on a test scheme is a groupoid. -/
@[implicit_reducible]
noncomputable def evaluationGroupoid {S : Scheme.{u}} (G : GroupoidScheme S) (T : Over S) :
    Groupoid (G.Evaluation T) where
  Hom := G.EvaluationHom
  id x :=
    { arrow := x ≫ G.identity
      source_eq := by simp only [Category.assoc, G.source_identity, Category.comp_id]
      target_eq := by simp only [Category.assoc, G.target_identity, Category.comp_id] }
  comp f g :=
    { arrow := pullback.lift g.arrow f.arrow (g.source_eq.trans f.target_eq.symm) ≫ G.comp
      source_eq := by
        simp only [Category.assoc, G.source_comp, pullback.lift_snd_assoc, f.source_eq]
      target_eq := by
        simp only [Category.assoc, G.target_comp, pullback.lift_fst_assoc, g.target_eq] }
  id_comp f := by
    apply EvaluationHom.ext
    convert G.right_identity T f.arrow
      (by
        calc
          f.arrow ≫ G.source = (f.arrow ≫ G.source) ≫ 𝟙 G.objects :=
            (Category.comp_id _).symm
          _ = (f.arrow ≫ G.source) ≫ (G.identity ≫ G.target) :=
            congrArg ((f.arrow ≫ G.source) ≫ ·) G.target_identity.symm
          _ = ((f.arrow ≫ G.source) ≫ G.identity) ≫ G.target :=
            (Category.assoc _ _ _).symm) using 1
    simp only [← Category.assoc, f.source_eq]
  comp_id f := by
    apply EvaluationHom.ext
    convert G.left_identity T f.arrow
      (by
        calc
          ((f.arrow ≫ G.target) ≫ G.identity) ≫ G.source =
              (f.arrow ≫ G.target) ≫ (G.identity ≫ G.source) :=
            Category.assoc _ _ _
          _ = (f.arrow ≫ G.target) ≫ 𝟙 G.objects :=
            congrArg ((f.arrow ≫ G.target) ≫ ·) G.source_identity
          _ = f.arrow ≫ G.target := Category.comp_id _) using 1
    simp only [← Category.assoc, f.target_eq]
  assoc f g h := by
    apply EvaluationHom.ext
    exact (G.assoc T h.arrow g.arrow f.arrow
      (h.source_eq.trans g.target_eq.symm) (g.source_eq.trans f.target_eq.symm)
      (by simp only [Category.assoc, G.source_comp, pullback.lift_snd_assoc,
        g.source_eq, f.target_eq])
      (by simp only [Category.assoc, G.target_comp, pullback.lift_fst_assoc,
        g.target_eq, h.source_eq])).symm
  inv f :=
    { arrow := f.arrow ≫ G.inverse
      source_eq := by simp only [Category.assoc, G.source_inverse, f.target_eq]
      target_eq := by simp only [Category.assoc, G.target_inverse, f.source_eq] }
  inv_comp f := by
    apply EvaluationHom.ext
    convert G.right_inverse T f.arrow
      (by simp only [Category.assoc, G.target_inverse, f.source_eq]) using 1
    simp only [← Category.assoc, f.target_eq]
  comp_inv f := by
    apply EvaluationHom.ext
    convert G.left_inverse T f.arrow
      (by simp only [Category.assoc, G.source_inverse, f.target_eq]) using 1
    simp only [← Category.assoc, f.source_eq]

/-- The groupoid of generalized points of a groupoid scheme over a test scheme. -/
noncomputable instance {S : Scheme.{u}} (G : GroupoidScheme S) (T : Over S) :
    Groupoid (G.Evaluation T) :=
  G.evaluationGroupoid T

/-- A lift into a pullback equals `x` when its components are those of `x`. -/
private theorem pullback_lift_eq {C : Type*} [Category C] {X Y Z T : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    [HasPullback f g] (a : T ⟶ X) (b : T ⟶ Y) (h : a ≫ f = b ≫ g) (x : T ⟶ pullback f g)
    (ha : a = x ≫ pullback.fst f g) (hb : b = x ≫ pullback.snd f g) : pullback.lift a b h = x := by
  subst ha hb
  exact pullback.hom_ext (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

/-- The lower-left square of the composition diagram, formed by the two projections out of the
scheme of composable arrows, the source map and the target map, is a pullback square: it is the
defining square of the fibre product `R ×_{s, U, t} R`. -/
@[stacks 04LF "diagram (04LF): the lower-left square (projections `pr₀`, `pr₁`, source and \
target) is cartesian"]
theorem fst_snd_isPullback {S : Scheme.{u}} (G : GroupoidScheme S) :
    IsPullback (pullback.fst G.source G.target) (pullback.snd G.source G.target) G.source
      G.target :=
  IsPullback.of_hasPullback G.source G.target

/-- The square formed by composition, the second projection, and two copies of the source map
is a pullback square: a composable pair of arrows is determined by its first member together
with its composite. -/
@[stacks 02YE "the lower-right square",
  stacks 04LF "diagram (04LF): the lower-right square is cartesian",
  stacks 03C6 "the lower composition square of the diagram: top map the composition, \
verticals the second projection and the source, bottom map the source"]
theorem comp_source_isPullback {S : Scheme.{u}} (G : GroupoidScheme S) :
    IsPullback G.comp (pullback.snd G.source G.target) G.source G.source := by
  refine IsPullback.mk' G.source_comp ?_ ?_
  · intro T x y hcomp hsnd
    let gr : Groupoid.{u} (T ⟶ G.objects) := G.evaluationGroupoid T
    apply pullback.hom_ext
    · let b : (x ≫ pullback.snd G.source G.target ≫ G.source : T ⟶ G.objects) ⟶
          (x ≫ pullback.snd G.source G.target ≫ G.target) :=
        { arrow := x ≫ pullback.snd G.source G.target, source_eq := rfl, target_eq := rfl }
      have hsource : y ≫ pullback.fst G.source G.target ≫ G.source =
          x ≫ pullback.snd G.source G.target ≫ G.target := by
        calc
          _ = y ≫ pullback.snd G.source G.target ≫ G.target := by
            simp only [pullback.condition]
          _ = _ := by simpa only [Category.assoc] using congrArg (· ≫ G.target) hsnd.symm
      have htarget : y ≫ pullback.fst G.source G.target ≫ G.target =
          x ≫ pullback.fst G.source G.target ≫ G.target := by
        simpa only [Category.assoc, G.target_comp, pullback.lift_fst_assoc] using
          congrArg (· ≫ G.target) hcomp.symm
      let a : (x ≫ pullback.snd G.source G.target ≫ G.target : T ⟶ G.objects) ⟶
          (x ≫ pullback.fst G.source G.target ≫ G.target) :=
        { arrow := x ≫ pullback.fst G.source G.target
          source_eq := by simp only [Category.assoc, pullback.condition], target_eq := rfl }
      let a' : (x ≫ pullback.snd G.source G.target ≫ G.target : T ⟶ G.objects) ⟶
          (x ≫ pullback.fst G.source G.target ≫ G.target) :=
        { arrow := y ≫ pullback.fst G.source G.target
          source_eq := hsource, target_eq := htarget }
      have hba : b ≫ a = b ≫ a' := by
        apply EvaluationHom.ext
        change pullback.lift _ _ _ ≫ G.comp = pullback.lift _ _ _ ≫ G.comp
        rw [pullback_lift_eq _ _ _ x rfl rfl, pullback_lift_eq _ _ _ y rfl hsnd]
        exact hcomp
      exact congrArg (fun q ↦ q.arrow) ((cancel_epi b).1 hba)
    · exact hsnd
  · intro T a b hab
    let gr : Groupoid.{u} (T ⟶ G.objects) := G.evaluationGroupoid T
    let β : (a ≫ G.source : T ⟶ G.objects) ⟶ (b ≫ G.target) :=
      { arrow := b, source_eq := hab.symm, target_eq := rfl }
    let α : (a ≫ G.source : T ⟶ G.objects) ⟶ (a ≫ G.target) :=
      { arrow := a, source_eq := rfl, target_eq := rfl }
    refine ⟨pullback.lift (gr.inv β ≫ α).arrow b (gr.inv β ≫ α).source_eq, ?_, ?_⟩
    · change (β ≫ (gr.inv β ≫ α)).arrow = a
      rw [← gr.assoc, gr.comp_inv, gr.id_comp]
    · exact pullback.lift_snd _ _ _

/-- The upper triangle in the composition diagram, viewed as a square with two copies of its
apex, is a pullback square: a pair of arrows with the same target is the same thing as a
composable pair together with its composite. -/
@[stacks 02YE "the upper square",
  stacks 04LF "diagram (04LF): the top triangle, read as a square with two copies of its apex \
`U` (maps `pr₀`, `c`, and the target map twice), is cartesian"]
theorem target_comp_isPullback {S : Scheme.{u}} (G : GroupoidScheme S) :
    IsPullback (pullback.fst G.source G.target) G.comp G.target G.target := by
  refine IsPullback.mk' G.target_comp.symm ?_ ?_
  · intro T x y hfst hcomp
    let gr : Groupoid.{u} (T ⟶ G.objects) := G.evaluationGroupoid T
    apply pullback.hom_ext
    · exact hfst
    · let a : (x ≫ pullback.fst G.source G.target ≫ G.source : T ⟶ G.objects) ⟶
          (x ≫ pullback.fst G.source G.target ≫ G.target) :=
        { arrow := x ≫ pullback.fst G.source G.target, source_eq := rfl, target_eq := rfl }
      have htarget : y ≫ pullback.snd G.source G.target ≫ G.target =
          x ≫ pullback.fst G.source G.target ≫ G.source := by
        calc
          _ = y ≫ pullback.fst G.source G.target ≫ G.source := by
            simp only [pullback.condition]
          _ = _ := by simpa only [Category.assoc] using congrArg (· ≫ G.source) hfst.symm
      have hsource : y ≫ pullback.snd G.source G.target ≫ G.source =
          x ≫ pullback.snd G.source G.target ≫ G.source := by
        simpa only [Category.assoc, G.source_comp, pullback.lift_snd_assoc] using
          congrArg (· ≫ G.source) hcomp.symm
      let b : (x ≫ pullback.snd G.source G.target ≫ G.source : T ⟶ G.objects) ⟶
          (x ≫ pullback.fst G.source G.target ≫ G.source) :=
        { arrow := x ≫ pullback.snd G.source G.target
          source_eq := rfl, target_eq := by simp only [Category.assoc, pullback.condition] }
      let b' : (x ≫ pullback.snd G.source G.target ≫ G.source : T ⟶ G.objects) ⟶
          (x ≫ pullback.fst G.source G.target ≫ G.source) :=
        { arrow := y ≫ pullback.snd G.source G.target
          source_eq := hsource, target_eq := htarget }
      have hba : b ≫ a = b' ≫ a := by
        apply EvaluationHom.ext
        change pullback.lift _ _ _ ≫ G.comp = pullback.lift _ _ _ ≫ G.comp
        rw [pullback_lift_eq _ _ _ x rfl rfl, pullback_lift_eq _ _ _ y hfst rfl]
        exact hcomp
      exact congrArg (fun q ↦ q.arrow) ((cancel_mono a).1 hba)
  · intro T a b hab
    let gr : Groupoid.{u} (T ⟶ G.objects) := G.evaluationGroupoid T
    let α : (a ≫ G.source : T ⟶ G.objects) ⟶ (a ≫ G.target) :=
      { arrow := a, source_eq := rfl, target_eq := rfl }
    let β : (b ≫ G.source : T ⟶ G.objects) ⟶ (a ≫ G.target) :=
      { arrow := b, source_eq := rfl, target_eq := hab.symm }
    refine ⟨pullback.lift a (β ≫ gr.inv α).arrow (β ≫ gr.inv α).target_eq.symm, ?_, ?_⟩
    · exact pullback.lift_fst _ _ _
    · change ((β ≫ gr.inv α) ≫ α).arrow = b
      rw [gr.assoc, gr.inv_comp, gr.comp_id]

end Stacks.Groupoids.GroupoidScheme

end
