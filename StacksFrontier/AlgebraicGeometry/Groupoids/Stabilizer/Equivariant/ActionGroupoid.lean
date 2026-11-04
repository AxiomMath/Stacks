module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Equivariant.ActionArrows

/-!
# The groupoid scheme attached to an equivariant scheme

For an equivariant scheme `V` for a groupoid scheme `G`, this file assembles the action arrows of
`V` into a groupoid scheme `AlgebraicGeometry.equivariantActionGroupoid V`, whose objects are the
objects of `V` and whose arrows are the pairs of an object and an arrow of `G` acting on it.

## References

* [Stacks Project, Tag 0APE](https://stacks.math.columbia.edu/tag/0APE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The groupoid scheme attached to an equivariant scheme: its objects are the objects upstairs
and its arrows are the pairs of an object and an arrow of `G` acting on it. -/
@[implicit_reducible]
noncomputable def equivariantActionGroupoid {S : Scheme.{u}}
    {G : GroupoidScheme S} (V : EquivariantScheme G) : GroupoidScheme S := by
  refine
    { objects := equivariantObjectOver V
      arrows := equivariantActionArrows V
      source := equivariantActionArrowSource V
      target := equivariantActionArrowTarget V
      comp := equivariantActionArrowComposition V
      identity := equivariantActionArrowIdentity V
      inverse := equivariantActionArrowInverse V
      source_identity := equivariantActionArrowIdentity_source V
      target_identity := equivariantActionArrowIdentity_target V
      source_inverse := equivariantActionArrowInverse_source V
      target_inverse := equivariantActionArrowInverse_target V
      source_comp := equivariantActionArrowComposition_source_eq_snd V
      target_comp := ?_
      left_identity := ?_
      right_identity := ?_
      left_inverse := ?_
      right_inverse := ?_
      assoc := ?_ }
  · exact equivariantActionArrowComposition_target V
  · intro T f w
    apply equivariantActionArrow_ext V
    · change (pullback.lift (f ≫ equivariantActionArrowTarget V ≫
          equivariantActionArrowIdentity V) f w ≫
            equivariantActionArrowComposition V) ≫ equivariantActionArrowTarget V =
          f ≫ equivariantActionArrowTarget V
      let a := pullback.fst (equivariantActionArrowSource V)
        (equivariantActionArrowTarget V)
      let p := pullback.lift (f ≫ equivariantActionArrowTarget V ≫
        equivariantActionArrowIdentity V) f w
      calc
        (p ≫ equivariantActionArrowComposition V) ≫ equivariantActionArrowTarget V =
            p ≫ a ≫ equivariantActionArrowTarget V := by
              rw [Category.assoc, equivariantActionArrowComposition_target]
        _ = f ≫ equivariantActionArrowTarget V := by
              have hp : p ≫ a = f ≫ equivariantActionArrowTarget V ≫
                  equivariantActionArrowIdentity V :=
                pullback.lift_fst _ _ _
              rw [← Category.assoc, hp]
              simp only [Category.assoc, equivariantActionArrowIdentity_target,
                Category.comp_id]
    · change (pullback.lift (f ≫ equivariantActionArrowTarget V ≫
          equivariantActionArrowIdentity V) f w ≫
            equivariantActionArrowComposition V) ≫ equivariantActionArrowBase V =
          f ≫ equivariantActionArrowBase V
      let a := pullback.fst (equivariantActionArrowSource V)
        (equivariantActionArrowTarget V)
      let b := pullback.snd (equivariantActionArrowSource V)
        (equivariantActionArrowTarget V)
      let p := pullback.lift (f ≫ equivariantActionArrowTarget V ≫
        equivariantActionArrowIdentity V) f w
      have hp : p ≫ a = f ≫ equivariantActionArrowTarget V ≫
          equivariantActionArrowIdentity V :=
        pullback.lift_fst _ _ _
      have hpcond : p ≫ a ≫ equivariantActionArrowSource V =
          p ≫ b ≫ equivariantActionArrowTarget V := by
        have hpb : p ≫ b = f :=
          pullback.lift_snd _ _ _
        simpa only [Category.assoc, reassoc_of% hp, reassoc_of% hpb] using w
      have hw := equivariantCompositionCondition V (p ≫ a) (p ≫ b) hpcond
      have hw' : (p ≫ a ≫ equivariantActionArrowBase V) ≫ G.source =
          (p ≫ b ≫ equivariantActionArrowBase V) ≫ G.target := by
        simpa only [Category.assoc] using hw
      have hbase :
          (p ≫ equivariantActionArrowComposition V) ≫ equivariantActionArrowBase V =
            G.compose (p ≫ a ≫ equivariantActionArrowBase V)
              (p ≫ b ≫ equivariantActionArrowBase V) hw' := by
        calc
          _ = p ≫ (equivariantActionArrowComposition V ≫ equivariantActionArrowBase V) :=
                Category.assoc _ _ _
          _ = p ≫ G.compose
                (a ≫ equivariantActionArrowBase V) (b ≫ equivariantActionArrowBase V)
                (equivariantCompositionCondition V a b pullback.condition) := by
                  rw [equivariantActionArrowComposition_base]
          _ = G.compose (p ≫ a ≫ equivariantActionArrowBase V)
                (p ≫ b ≫ equivariantActionArrowBase V) hw :=
                  (groupoidCompose_precomp _ p _ _
                    (equivariantCompositionCondition V a b pullback.condition) hw').symm
      calc
        (p ≫ equivariantActionArrowComposition V) ≫ equivariantActionArrowBase V =
            G.compose (p ≫ a ≫ equivariantActionArrowBase V)
              (p ≫ b ≫ equivariantActionArrowBase V) hw' := hbase
        _ = f ≫ equivariantActionArrowBase V := by
          have hfirst : p ≫ a ≫ equivariantActionArrowBase V =
              (f ≫ equivariantActionArrowBase V) ≫ G.target ≫ G.identity := by
            simpa only [Category.assoc, reassoc_of% hp, equivariantActionArrowIdentity_base] using
              congrArg (· ≫ G.identity) (equivariantActionArrowCondition V f)
          have hsecond : p ≫ b ≫ equivariantActionArrowBase V =
              f ≫ equivariantActionArrowBase V := by
            have hpb : p ≫ b = f :=
              pullback.lift_snd _ _ _
            rw [← Category.assoc, hpb]
          let wId :
              ((f ≫ equivariantActionArrowBase V) ≫ G.target ≫ G.identity) ≫ G.source =
                (f ≫ equivariantActionArrowBase V) ≫ G.target := by
            simp [G.source_identity]
          have hcomp := groupoidCompose_arrow_eq
            (p ≫ a ≫ equivariantActionArrowBase V)
            ((f ≫ equivariantActionArrowBase V) ≫ G.target ≫ G.identity)
            (p ≫ b ≫ equivariantActionArrowBase V)
            (f ≫ equivariantActionArrowBase V) hw' wId hfirst hsecond
          rw [hcomp]
          exact G.left_identity T (f ≫ equivariantActionArrowBase V) wId
  · intro T f w
    apply equivariantActionArrow_ext V
    · let a := pullback.fst (equivariantActionArrowSource V)
        (equivariantActionArrowTarget V)
      let p := pullback.lift f
        (f ≫ equivariantActionArrowSource V ≫ equivariantActionArrowIdentity V) w
      have hp : p ≫ a = f :=
        pullback.lift_fst _ _ _
      calc
        (p ≫ equivariantActionArrowComposition V) ≫ equivariantActionArrowTarget V =
            p ≫ a ≫ equivariantActionArrowTarget V := by
              rw [Category.assoc, equivariantActionArrowComposition_target]
        _ = f ≫ equivariantActionArrowTarget V := by rw [← Category.assoc, hp]
    · let a := pullback.fst (equivariantActionArrowSource V)
        (equivariantActionArrowTarget V)
      let b := pullback.snd (equivariantActionArrowSource V)
        (equivariantActionArrowTarget V)
      let p := pullback.lift f
        (f ≫ equivariantActionArrowSource V ≫ equivariantActionArrowIdentity V) w
      have hpa : p ≫ a = f :=
        pullback.lift_fst _ _ _
      have hpb : p ≫ b = f ≫ equivariantActionArrowSource V ≫
          equivariantActionArrowIdentity V :=
        pullback.lift_snd _ _ _
      have hpcond : p ≫ a ≫ equivariantActionArrowSource V =
          p ≫ b ≫ equivariantActionArrowTarget V := by
        simpa only [Category.assoc, reassoc_of% hpa, reassoc_of% hpb] using w
      have hw := equivariantCompositionCondition V (p ≫ a) (p ≫ b) hpcond
      have hw' : (p ≫ a ≫ equivariantActionArrowBase V) ≫ G.source =
          (p ≫ b ≫ equivariantActionArrowBase V) ≫ G.target := by
        simpa only [Category.assoc] using hw
      have hbase :
          (p ≫ equivariantActionArrowComposition V) ≫ equivariantActionArrowBase V =
            G.compose (p ≫ a ≫ equivariantActionArrowBase V)
              (p ≫ b ≫ equivariantActionArrowBase V) hw' := by
        calc
          _ = p ≫ (equivariantActionArrowComposition V ≫ equivariantActionArrowBase V) :=
                Category.assoc _ _ _
          _ = p ≫ G.compose
                (a ≫ equivariantActionArrowBase V) (b ≫ equivariantActionArrowBase V)
                (equivariantCompositionCondition V a b pullback.condition) := by
                  rw [equivariantActionArrowComposition_base]
          _ = G.compose (p ≫ a ≫ equivariantActionArrowBase V)
                (p ≫ b ≫ equivariantActionArrowBase V) hw' :=
                  (groupoidCompose_precomp _ p _ _
                    (equivariantCompositionCondition V a b pullback.condition) hw').symm
      calc
        (p ≫ equivariantActionArrowComposition V) ≫ equivariantActionArrowBase V =
            G.compose (p ≫ a ≫ equivariantActionArrowBase V)
              (p ≫ b ≫ equivariantActionArrowBase V) hw' := hbase
        _ = f ≫ equivariantActionArrowBase V := by
          have hfirst : p ≫ a ≫ equivariantActionArrowBase V =
              f ≫ equivariantActionArrowBase V := by
            rw [← Category.assoc, hpa]
          have hsecond : p ≫ b ≫ equivariantActionArrowBase V =
              (f ≫ equivariantActionArrowBase V) ≫ G.source ≫ G.identity := by
            simpa only [Category.assoc, reassoc_of% hpb, equivariantActionArrowIdentity_base] using
              congrArg (· ≫ G.identity) (equivariantActionArrowSource_obj V f)
          let wId :
              (f ≫ equivariantActionArrowBase V) ≫ G.source =
                ((f ≫ equivariantActionArrowBase V) ≫ G.source ≫ G.identity) ≫ G.target := by
            simp [G.target_identity]
          have hcomp := groupoidCompose_arrow_eq
            (p ≫ a ≫ equivariantActionArrowBase V)
            (f ≫ equivariantActionArrowBase V)
            (p ≫ b ≫ equivariantActionArrowBase V)
            ((f ≫ equivariantActionArrowBase V) ≫ G.source ≫ G.identity)
            hw' wId hfirst hsecond
          rw [hcomp]
          exact G.right_identity T (f ≫ equivariantActionArrowBase V) wId
  · intro T f w
    apply equivariantActionArrow_ext V
      (pullback.lift (f ≫ equivariantActionArrowInverse V) f w ≫
        equivariantActionArrowComposition V)
      (f ≫ equivariantActionArrowSource V ≫ equivariantActionArrowIdentity V)
    · let a := pullback.fst (equivariantActionArrowSource V)
        (equivariantActionArrowTarget V)
      let p := pullback.lift (f ≫ equivariantActionArrowInverse V) f w
      have hpa : p ≫ a = f ≫ equivariantActionArrowInverse V :=
        pullback.lift_fst _ _ _
      calc
        (p ≫ equivariantActionArrowComposition V) ≫ equivariantActionArrowTarget V =
            p ≫ a ≫ equivariantActionArrowTarget V := by
              rw [Category.assoc, equivariantActionArrowComposition_target]
        _ = (f ≫ equivariantActionArrowSource V ≫
              equivariantActionArrowIdentity V) ≫ equivariantActionArrowTarget V := by
              simp only [Category.assoc, reassoc_of% hpa, equivariantActionArrowInverse_target,
                equivariantActionArrowIdentity_target, Category.comp_id]
    · let a := pullback.fst (equivariantActionArrowSource V)
        (equivariantActionArrowTarget V)
      let b := pullback.snd (equivariantActionArrowSource V)
        (equivariantActionArrowTarget V)
      let p := pullback.lift (f ≫ equivariantActionArrowInverse V) f w
      have hpa : p ≫ a = f ≫ equivariantActionArrowInverse V :=
        pullback.lift_fst _ _ _
      have hpb : p ≫ b = f :=
        pullback.lift_snd _ _ _
      have hpcond : p ≫ a ≫ equivariantActionArrowSource V =
          p ≫ b ≫ equivariantActionArrowTarget V := by
        simpa only [Category.assoc, reassoc_of% hpa, reassoc_of% hpb] using
          congrArg (f ≫ ·) (equivariantActionArrowInverse_source V)
      have hw := equivariantCompositionCondition V (p ≫ a) (p ≫ b) hpcond
      have hw' : (p ≫ a ≫ equivariantActionArrowBase V) ≫ G.source =
          (p ≫ b ≫ equivariantActionArrowBase V) ≫ G.target := by
        simpa only [Category.assoc] using hw
      have hbase :
          (p ≫ equivariantActionArrowComposition V) ≫ equivariantActionArrowBase V =
            G.compose (p ≫ a ≫ equivariantActionArrowBase V)
              (p ≫ b ≫ equivariantActionArrowBase V) hw' := by
        calc
          _ = p ≫ (equivariantActionArrowComposition V ≫ equivariantActionArrowBase V) :=
                Category.assoc _ _ _
          _ = p ≫ G.compose
                (a ≫ equivariantActionArrowBase V) (b ≫ equivariantActionArrowBase V)
                (equivariantCompositionCondition V a b pullback.condition) := by
                  rw [equivariantActionArrowComposition_base]
          _ = G.compose (p ≫ a ≫ equivariantActionArrowBase V)
                (p ≫ b ≫ equivariantActionArrowBase V) hw' :=
                  (groupoidCompose_precomp _ p _ _
                    (equivariantCompositionCondition V a b pullback.condition) hw').symm
      have hfirst : p ≫ a ≫ equivariantActionArrowBase V =
          (f ≫ equivariantActionArrowBase V) ≫ G.inverse := by
        calc
          p ≫ a ≫ equivariantActionArrowBase V =
              (f ≫ equivariantActionArrowInverse V) ≫ equivariantActionArrowBase V := by
                rw [← Category.assoc, hpa]
          _ = (f ≫ equivariantActionArrowBase V) ≫ G.inverse := by
                simpa only [Category.assoc] using congrArg
                  (fun z => f ≫ z) (equivariantActionArrowInverse_base V)
      have hsecond : p ≫ b ≫ equivariantActionArrowBase V =
          f ≫ equivariantActionArrowBase V := by
        rw [← Category.assoc, hpb]
      have wInv :
          ((f ≫ equivariantActionArrowBase V) ≫ G.inverse) ≫ G.source =
            (f ≫ equivariantActionArrowBase V) ≫ G.target := by
        simpa only [Category.assoc] using congrArg
          (fun z => f ≫ equivariantActionArrowBase V ≫ z) G.source_inverse
      have hcomp := groupoidCompose_arrow_eq
        (p ≫ a ≫ equivariantActionArrowBase V)
        ((f ≫ equivariantActionArrowBase V) ≫ G.inverse)
        (p ≫ b ≫ equivariantActionArrowBase V)
        (f ≫ equivariantActionArrowBase V) hw' wInv hfirst hsecond
      have hidentity : (f ≫ equivariantActionArrowSource V ≫
          equivariantActionArrowIdentity V) ≫ equivariantActionArrowBase V =
            ((f ≫ equivariantActionArrowBase V) ≫ G.source) ≫ G.identity := by
        simpa only [Category.assoc, equivariantActionArrowIdentity_base] using
          congrArg (· ≫ G.identity) (equivariantActionArrowSource_obj V f)
      rw [hbase, hcomp, hidentity]
      exact G.left_inverse T (f ≫ equivariantActionArrowBase V) wInv
  · intro T f w
    apply equivariantActionArrow_ext V
    · let a := pullback.fst (equivariantActionArrowSource V)
        (equivariantActionArrowTarget V)
      let p := pullback.lift f (f ≫ equivariantActionArrowInverse V) w
      have hpa : p ≫ a = f :=
        pullback.lift_fst _ _ _
      calc
        (p ≫ equivariantActionArrowComposition V) ≫ equivariantActionArrowTarget V =
            p ≫ a ≫ equivariantActionArrowTarget V := by
              rw [Category.assoc, equivariantActionArrowComposition_target]
        _ = f ≫ equivariantActionArrowTarget V := by
              rw [← Category.assoc, hpa]
        _ = (f ≫ equivariantActionArrowTarget V ≫
              equivariantActionArrowIdentity V) ≫ equivariantActionArrowTarget V := by
                simpa only [Category.assoc, Category.id_comp, Category.comp_id] using
                  congrArg (fun z => (f ≫ equivariantActionArrowTarget V) ≫ z)
                    (equivariantActionArrowIdentity_target V).symm
    · let a := pullback.fst (equivariantActionArrowSource V)
        (equivariantActionArrowTarget V)
      let b := pullback.snd (equivariantActionArrowSource V)
        (equivariantActionArrowTarget V)
      let p := pullback.lift f (f ≫ equivariantActionArrowInverse V) w
      have hpa : p ≫ a = f :=
        pullback.lift_fst _ _ _
      have hpb : p ≫ b = f ≫ equivariantActionArrowInverse V :=
        pullback.lift_snd _ _ _
      have hpcond : p ≫ a ≫ equivariantActionArrowSource V =
          p ≫ b ≫ equivariantActionArrowTarget V := by
        simpa only [Category.assoc, reassoc_of% hpa, reassoc_of% hpb] using w
      have hw := equivariantCompositionCondition V (p ≫ a) (p ≫ b) hpcond
      have hw' : (p ≫ a ≫ equivariantActionArrowBase V) ≫ G.source =
          (p ≫ b ≫ equivariantActionArrowBase V) ≫ G.target := by
        simpa only [Category.assoc] using hw
      have hbase :
          (p ≫ equivariantActionArrowComposition V) ≫ equivariantActionArrowBase V =
            G.compose (p ≫ a ≫ equivariantActionArrowBase V)
              (p ≫ b ≫ equivariantActionArrowBase V) hw' := by
        calc
          _ = p ≫ (equivariantActionArrowComposition V ≫ equivariantActionArrowBase V) :=
                Category.assoc _ _ _
          _ = p ≫ G.compose
                (a ≫ equivariantActionArrowBase V) (b ≫ equivariantActionArrowBase V)
                (equivariantCompositionCondition V a b pullback.condition) := by
                  rw [equivariantActionArrowComposition_base]
          _ = G.compose (p ≫ a ≫ equivariantActionArrowBase V)
                (p ≫ b ≫ equivariantActionArrowBase V) hw' :=
                  (groupoidCompose_precomp _ p _ _
                    (equivariantCompositionCondition V a b pullback.condition) hw').symm
      have hfirst : p ≫ a ≫ equivariantActionArrowBase V =
          f ≫ equivariantActionArrowBase V :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ equivariantActionArrowBase V) hpa)
      have hsecond : p ≫ b ≫ equivariantActionArrowBase V =
          (f ≫ equivariantActionArrowBase V) ≫ G.inverse := by
        calc
          p ≫ b ≫ equivariantActionArrowBase V =
              (p ≫ b) ≫ equivariantActionArrowBase V := (Category.assoc _ _ _).symm
          _ = (f ≫ equivariantActionArrowInverse V) ≫
                equivariantActionArrowBase V := congrArg
                  (fun z => z ≫ equivariantActionArrowBase V) hpb
          _ = (f ≫ equivariantActionArrowBase V) ≫ G.inverse := by
                simpa only [Category.assoc] using congrArg
                  (fun z => f ≫ z) (equivariantActionArrowInverse_base V)
      have wInv : (f ≫ equivariantActionArrowBase V) ≫ G.source =
          ((f ≫ equivariantActionArrowBase V) ≫ G.inverse) ≫ G.target := by
        simpa only [Category.assoc] using congrArg
          (fun z => f ≫ equivariantActionArrowBase V ≫ z) G.target_inverse.symm
      have hcomp := groupoidCompose_arrow_eq
        (p ≫ a ≫ equivariantActionArrowBase V)
        (f ≫ equivariantActionArrowBase V)
        (p ≫ b ≫ equivariantActionArrowBase V)
        ((f ≫ equivariantActionArrowBase V) ≫ G.inverse) hw' wInv hfirst hsecond
      have hidentity : (f ≫ equivariantActionArrowTarget V ≫
          equivariantActionArrowIdentity V) ≫ equivariantActionArrowBase V =
            (f ≫ equivariantActionArrowBase V) ≫ G.target ≫ G.identity := by
        simpa only [Category.assoc, equivariantActionArrowIdentity_base] using
          congrArg (· ≫ G.identity) (equivariantActionArrowCondition V f)
      rw [hbase, hcomp, hidentity]
      exact G.right_inverse T (f ≫ equivariantActionArrowBase V) wInv
  · intro T f g h wfg wgh w₁ w₂
    let pfg := pullback.lift f g wfg
    let pgh := pullback.lift g h wgh
    let ql := pullback.lift (pfg ≫ equivariantActionArrowComposition V) h w₁
    let qr := pullback.lift f (pgh ≫ equivariantActionArrowComposition V) w₂
    let bf := f ≫ equivariantActionArrowBase V
    let bg := g ≫ equivariantActionArrowBase V
    let bh := h ≫ equivariantActionArrowBase V
    let wfgB := equivariantCompositionCondition V f g wfg
    let wghB := equivariantCompositionCondition V g h wgh
    let pfg₀ := pullback.fst (equivariantActionArrowSource V)
      (equivariantActionArrowTarget V)
    let pfg₁ := pullback.snd (equivariantActionArrowSource V)
      (equivariantActionArrowTarget V)
    have hpfg₀ : pfg ≫ pfg₀ = f :=
      pullback.lift_fst _ _ _
    have hpfg₁ : pfg ≫ pfg₁ = g :=
      pullback.lift_snd _ _ _
    have hpgh₀ : pgh ≫ pfg₀ = g :=
      pullback.lift_fst _ _ _
    have hpgh₁ : pgh ≫ pfg₁ = h :=
      pullback.lift_snd _ _ _
    have wfg₀ : (pfg ≫ pfg₀) ≫ equivariantActionArrowSource V =
        (pfg ≫ pfg₁) ≫ equivariantActionArrowTarget V := by
      rw [hpfg₀, hpfg₁]
      exact wfg
    have wgh₀ : (pgh ≫ pfg₀) ≫ equivariantActionArrowSource V =
        (pgh ≫ pfg₁) ≫ equivariantActionArrowTarget V := by
      rw [hpgh₀, hpgh₁]
      exact wgh
    let wfgP := equivariantCompositionCondition V (pfg ≫ pfg₀) (pfg ≫ pfg₁) wfg₀
    let wghP := equivariantCompositionCondition V (pgh ≫ pfg₀) (pgh ≫ pfg₁) wgh₀
    have hpfgBase₀ : pfg ≫ pfg₀ ≫ equivariantActionArrowBase V = bf :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ equivariantActionArrowBase V) hpfg₀)
    have hpfgBase₁ : pfg ≫ pfg₁ ≫ equivariantActionArrowBase V = bg :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ equivariantActionArrowBase V) hpfg₁)
    have hpghBase₀ : pgh ≫ pfg₀ ≫ equivariantActionArrowBase V = bg :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ equivariantActionArrowBase V) hpgh₀)
    have hpghBase₁ : pgh ≫ pfg₁ ≫ equivariantActionArrowBase V = bh :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ equivariantActionArrowBase V) hpgh₁)
    have hfgB : (pfg ≫ equivariantActionArrowComposition V) ≫
        equivariantActionArrowBase V = G.compose bf bg wfgB := by
      calc
        _ = G.compose (pfg ≫ pfg₀ ≫ equivariantActionArrowBase V)
              (pfg ≫ pfg₁ ≫ equivariantActionArrowBase V) wfgP :=
                equivariantActionArrowComposition_base_comp V pfg
        _ = G.compose bf bg wfgB := groupoidCompose_arrow_eq
              (pfg ≫ pfg₀ ≫ equivariantActionArrowBase V) bf
              (pfg ≫ pfg₁ ≫ equivariantActionArrowBase V) bg
              wfgP wfgB hpfgBase₀ hpfgBase₁
    have hghB : (pgh ≫ equivariantActionArrowComposition V) ≫
        equivariantActionArrowBase V = G.compose bg bh wghB := by
      calc
        _ = G.compose (pgh ≫ pfg₀ ≫ equivariantActionArrowBase V)
              (pgh ≫ pfg₁ ≫ equivariantActionArrowBase V) wghP :=
                equivariantActionArrowComposition_base_comp V pgh
        _ = G.compose bg bh wghB := groupoidCompose_arrow_eq
              (pgh ≫ pfg₀ ≫ equivariantActionArrowBase V) bg
              (pgh ≫ pfg₁ ≫ equivariantActionArrowBase V) bh
              wghP wghB hpghBase₀ hpghBase₁
    have w₁B : G.compose bf bg wfgB ≫ G.source = bh ≫ G.target :=
      (groupoidCompose_source _ _ _ _).trans wghB
    have w₂B : bf ≫ G.source = G.compose bg bh wghB ≫ G.target :=
      wfgB.trans (groupoidCompose_target _ _ _ _).symm
    have hql₀ : ql ≫ pfg₀ = pfg ≫ equivariantActionArrowComposition V :=
      pullback.lift_fst _ _ _
    have hql₁ : ql ≫ pfg₁ = h :=
      pullback.lift_snd _ _ _
    have hqr₀ : qr ≫ pfg₀ = f :=
      pullback.lift_fst _ _ _
    have hqr₁ : qr ≫ pfg₁ = pgh ≫ equivariantActionArrowComposition V :=
      pullback.lift_snd _ _ _
    have wql : (ql ≫ pfg₀) ≫ equivariantActionArrowSource V =
        (ql ≫ pfg₁) ≫ equivariantActionArrowTarget V := by
      rw [hql₀, hql₁]
      exact w₁
    have wqr : (qr ≫ pfg₀) ≫ equivariantActionArrowSource V =
        (qr ≫ pfg₁) ≫ equivariantActionArrowTarget V := by
      rw [hqr₀, hqr₁]
      exact w₂
    let wqlB := equivariantCompositionCondition V (ql ≫ pfg₀) (ql ≫ pfg₁) wql
    let wqrB := equivariantCompositionCondition V (qr ≫ pfg₀) (qr ≫ pfg₁) wqr
    have hqlBase₀ : ql ≫ pfg₀ ≫ equivariantActionArrowBase V =
        (pfg ≫ equivariantActionArrowComposition V) ≫ equivariantActionArrowBase V :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ equivariantActionArrowBase V) hql₀)
    have hqlBase₁ : ql ≫ pfg₁ ≫ equivariantActionArrowBase V = bh :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ equivariantActionArrowBase V) hql₁)
    have hqrBase₀ : qr ≫ pfg₀ ≫ equivariantActionArrowBase V = bf :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ equivariantActionArrowBase V) hqr₀)
    have hqrBase₁ : qr ≫ pfg₁ ≫ equivariantActionArrowBase V =
        (pgh ≫ equivariantActionArrowComposition V) ≫ equivariantActionArrowBase V :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ equivariantActionArrowBase V) hqr₁)
    have w₁P := equivariantCompositionCondition V
      (pfg ≫ equivariantActionArrowComposition V) h w₁
    have w₂P := equivariantCompositionCondition V f
      (pgh ≫ equivariantActionArrowComposition V) w₂
    have hleftB : (ql ≫ equivariantActionArrowComposition V) ≫
        equivariantActionArrowBase V = G.compose (G.compose bf bg wfgB) bh w₁B := by
      calc
        (ql ≫ equivariantActionArrowComposition V) ≫ equivariantActionArrowBase V =
            G.compose (ql ≫ pfg₀ ≫ equivariantActionArrowBase V)
              (ql ≫ pfg₁ ≫ equivariantActionArrowBase V) wqlB :=
                equivariantActionArrowComposition_base_comp V ql
        _ = G.compose ((pfg ≫ equivariantActionArrowComposition V) ≫
              equivariantActionArrowBase V) bh w₁P := groupoidCompose_arrow_eq
                (ql ≫ pfg₀ ≫ equivariantActionArrowBase V)
                ((pfg ≫ equivariantActionArrowComposition V) ≫
                  equivariantActionArrowBase V)
                (ql ≫ pfg₁ ≫ equivariantActionArrowBase V) bh
                wqlB w₁P hqlBase₀ hqlBase₁
        _ = G.compose (G.compose bf bg wfgB) bh w₁B :=
              groupoidCompose_arrow_eq
                ((pfg ≫ equivariantActionArrowComposition V) ≫
                  equivariantActionArrowBase V) (G.compose bf bg wfgB) bh bh
                w₁P w₁B hfgB rfl
    have hrightB : (qr ≫ equivariantActionArrowComposition V) ≫
        equivariantActionArrowBase V = G.compose bf (G.compose bg bh wghB) w₂B := by
      calc
        (qr ≫ equivariantActionArrowComposition V) ≫ equivariantActionArrowBase V =
            G.compose (qr ≫ pfg₀ ≫ equivariantActionArrowBase V)
              (qr ≫ pfg₁ ≫ equivariantActionArrowBase V) wqrB :=
                equivariantActionArrowComposition_base_comp V qr
        _ = G.compose bf ((pgh ≫ equivariantActionArrowComposition V) ≫
              equivariantActionArrowBase V) w₂P := groupoidCompose_arrow_eq
                (qr ≫ pfg₀ ≫ equivariantActionArrowBase V) bf
                (qr ≫ pfg₁ ≫ equivariantActionArrowBase V)
                ((pgh ≫ equivariantActionArrowComposition V) ≫
                  equivariantActionArrowBase V)
                wqrB w₂P hqrBase₀ hqrBase₁
        _ = G.compose bf (G.compose bg bh wghB) w₂B :=
              groupoidCompose_arrow_eq
                bf bf ((pgh ≫ equivariantActionArrowComposition V) ≫
                  equivariantActionArrowBase V) (G.compose bg bh wghB)
                w₂P w₂B rfl hghB
    have hassoc := G.assoc T bf bg bh wfgB wghB w₁B w₂B
    apply equivariantActionArrow_ext V
      (ql ≫ equivariantActionArrowComposition V)
      (qr ≫ equivariantActionArrowComposition V)
    · calc
        (ql ≫ equivariantActionArrowComposition V) ≫ equivariantActionArrowTarget V =
            (ql ≫ pfg₀) ≫ equivariantActionArrowTarget V :=
              equivariantActionArrowComposition_target_comp V ql
        _ = (pfg ≫ equivariantActionArrowComposition V) ≫
              equivariantActionArrowTarget V := congrArg
                (fun z => z ≫ equivariantActionArrowTarget V) hql₀
        _ = (pfg ≫ pfg₀) ≫ equivariantActionArrowTarget V :=
              equivariantActionArrowComposition_target_comp V pfg
        _ = f ≫ equivariantActionArrowTarget V := congrArg
              (fun z => z ≫ equivariantActionArrowTarget V) hpfg₀
        _ = (qr ≫ pfg₀) ≫ equivariantActionArrowTarget V := congrArg
              (fun z => z ≫ equivariantActionArrowTarget V) hqr₀.symm
        _ = (qr ≫ equivariantActionArrowComposition V) ≫
              equivariantActionArrowTarget V :=
                (equivariantActionArrowComposition_target_comp V qr).symm
    · rw [hleftB, hrightB]
      simpa [GroupoidScheme.compose] using hassoc

end AlgebraicGeometry

end
