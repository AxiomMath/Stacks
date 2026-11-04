module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Equivariant.EquivariantScheme

/-!
# The arrow scheme of the groupoid attached to an equivariant scheme

For an equivariant scheme `V` for a groupoid scheme `G`, the arrows of the attached groupoid are
the pairs of an object of `V` and an arrow of `G` whose target lies under it.  This file defines
this arrow scheme together with its source, target, identity, inverse and composition maps, and
proves the identities between them that the groupoid axioms need.

## References

* [Stacks Project, Tag 0APE](https://stacks.math.columbia.edu/tag/0APE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The scheme over the base underlying an equivariant scheme. -/
abbrev equivariantObjectOver {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) : Over S := V.obj.left

/-- The structure map of an equivariant scheme to the object scheme of `G`. -/
abbrev equivariantObjectMap {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) : equivariantObjectOver V ⟶ G.objects :=
  V.obj.hom

/-- The arrow scheme of the groupoid attached to an equivariant scheme: pairs of an object
upstairs and an arrow of `G` whose target lies under it. -/
noncomputable abbrev equivariantActionArrows {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) : Over S := pullback (equivariantObjectMap V) G.target

/-- The source map of the groupoid attached to an equivariant scheme: the action of the arrow on
the object. -/
noncomputable abbrev equivariantActionArrowSource {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) : equivariantActionArrows V ⟶ equivariantObjectOver V :=
  V.action (pullback.fst (equivariantObjectMap V) G.target)
    (pullback.snd (equivariantObjectMap V) G.target) pullback.condition

/-- The target map of the groupoid attached to an equivariant scheme: the object the arrow acts
on. -/
noncomputable abbrev equivariantActionArrowTarget {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) : equivariantActionArrows V ⟶ equivariantObjectOver V :=
  pullback.fst (equivariantObjectMap V) G.target

/-- The map to the arrow scheme of `G` from the arrow scheme of the groupoid attached to an
equivariant scheme. -/
noncomputable abbrev equivariantActionArrowBase {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) : equivariantActionArrows V ⟶ G.arrows :=
  pullback.snd (equivariantObjectMap V) G.target

/-- The identity section of the groupoid attached to an equivariant scheme. -/
noncomputable def equivariantActionArrowIdentity {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) : equivariantObjectOver V ⟶ equivariantActionArrows V :=
  pullback.lift (𝟙 (equivariantObjectOver V)) (V.obj.hom ≫ G.identity) (by
    change V.obj.hom = (V.obj.hom ≫ G.identity) ≫ G.target
    rw [Category.assoc, G.target_identity]
    simp)

/-- Inversion of the groupoid attached to an equivariant scheme. -/
noncomputable def equivariantActionArrowInverse {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) : equivariantActionArrows V ⟶ equivariantActionArrows V :=
  pullback.lift (equivariantActionArrowSource V)
    (equivariantActionArrowBase V ≫ G.inverse) (by
      rw [Category.assoc, G.target_inverse]
      simpa [equivariantActionArrowSource, equivariantActionArrowBase] using
        V.action_comp_hom
          (pullback.fst (equivariantObjectMap V) G.target)
          (pullback.snd (equivariantObjectMap V) G.target) pullback.condition)

/-- The source of a generalized arrow of the attached groupoid is the action of its arrow of `G`
on its target. -/
theorem equivariantActionArrowSource_comp {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) {T : Over S} (f : T ⟶ equivariantActionArrows V) :
    f ≫ equivariantActionArrowSource V =
      V.action (f ≫ equivariantActionArrowTarget V) (f ≫ equivariantActionArrowBase V) (by
        calc
          (f ≫ equivariantActionArrowTarget V) ≫ V.obj.hom =
              f ≫ (equivariantActionArrowTarget V ≫ V.obj.hom) := Category.assoc _ _ _
          _ = f ≫ (equivariantActionArrowBase V ≫ G.target) :=
              congrArg (fun k => f ≫ k) pullback.condition
          _ = (f ≫ equivariantActionArrowBase V) ≫ G.target :=
              (Category.assoc _ _ _).symm) := by
  unfold equivariantActionArrowSource equivariantActionArrowTarget equivariantActionArrowBase
    EquivariantScheme.action
  have w : (f ≫ pullback.fst (equivariantObjectMap V) G.target) ≫ V.obj.hom =
      (f ≫ pullback.snd (equivariantObjectMap V) G.target) ≫ G.target := by
    rw [Category.assoc, Category.assoc]
    exact congrArg (f ≫ ·) pullback.condition
  have hlift :
      pullback.lift (f ≫ pullback.fst (equivariantObjectMap V) G.target)
          (f ≫ pullback.snd (equivariantObjectMap V) G.target) w =
        f ≫ pullback.lift (pullback.fst (equivariantObjectMap V) G.target)
          (pullback.snd (equivariantObjectMap V) G.target) pullback.condition := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
    · simp only [Category.assoc, pullback.lift_snd]
  rw [hlift]
  simp only [Category.assoc]

/-- The target of a generalized arrow of the attached groupoid lies under the target of its arrow
of `G`. -/
theorem equivariantActionArrowCondition {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) {T : Over S} (f : T ⟶ equivariantActionArrows V) :
    (f ≫ equivariantActionArrowTarget V) ≫ equivariantObjectMap V =
      (f ≫ equivariantActionArrowBase V) ≫ G.target := by
  rw [Category.assoc, Category.assoc]
  exact congrArg (f ≫ ·) pullback.condition

/-- The source of a generalized arrow of the attached groupoid lies under the source of its arrow
of `G`. -/
theorem equivariantActionArrowSource_obj {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) {T : Over S} (f : T ⟶ equivariantActionArrows V) :
    (f ≫ equivariantActionArrowSource V) ≫ equivariantObjectMap V =
      (f ≫ equivariantActionArrowBase V) ≫ G.source := by
  rw [equivariantActionArrowSource_comp]
  exact V.action_comp_hom _ _ _

/-- Two composable generalized arrows of the attached groupoid have composable arrows of `G`. -/
theorem equivariantCompositionCondition {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) {T : Over S} (f g : T ⟶ equivariantActionArrows V)
    (w : f ≫ equivariantActionArrowSource V = g ≫ equivariantActionArrowTarget V) :
    (f ≫ equivariantActionArrowBase V) ≫ G.source =
      (g ≫ equivariantActionArrowBase V) ≫ G.target := by
  rw [← V.action_comp_hom (f ≫ equivariantActionArrowTarget V)
    (f ≫ equivariantActionArrowBase V) (equivariantActionArrowCondition V f),
    ← equivariantActionArrowSource_comp, w]
  exact equivariantActionArrowCondition V g

/-- Composition in the groupoid attached to an equivariant scheme: compose the arrows of `G` and
keep the target of the first. -/
noncomputable def equivariantActionArrowComposition {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) :
    pullback (equivariantActionArrowSource V) (equivariantActionArrowTarget V) ⟶
      equivariantActionArrows V := by
  let f := pullback.fst (equivariantActionArrowSource V) (equivariantActionArrowTarget V)
  let g := pullback.snd (equivariantActionArrowSource V) (equivariantActionArrowTarget V)
  let w := equivariantCompositionCondition V f g pullback.condition
  exact pullback.lift (f ≫ equivariantActionArrowTarget V)
    (G.compose (f ≫ equivariantActionArrowBase V) (g ≫ equivariantActionArrowBase V) w)
    ((equivariantActionArrowCondition V f).trans (groupoidCompose_target _ _ _ _).symm)

/-- A generalized arrow of the attached groupoid is determined by its target and its arrow of
`G`. -/
theorem equivariantActionArrow_ext {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) {T : Over S}
    (f g : T ⟶ equivariantActionArrows V)
    (ht : f ≫ equivariantActionArrowTarget V = g ≫ equivariantActionArrowTarget V)
    (hr : f ≫ equivariantActionArrowBase V = g ≫ equivariantActionArrowBase V) : f = g :=
  pullback.hom_ext ht hr

/-- Composition in the attached groupoid preserves the target of the first factor. -/
theorem equivariantActionArrowComposition_target {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) :
    equivariantActionArrowComposition V ≫ equivariantActionArrowTarget V =
      pullback.fst (equivariantActionArrowSource V) (equivariantActionArrowTarget V) ≫
        equivariantActionArrowTarget V := by
  dsimp [equivariantActionArrowComposition]
  rw [pullback.lift_fst]

/-- The target of a composite, after precomposition with a generalized point. -/
theorem equivariantActionArrowComposition_target_comp {S : Scheme.{u}}
    {G : GroupoidScheme S} (V : EquivariantScheme G) {T : Over S}
    (p : T ⟶ pullback (equivariantActionArrowSource V)
      (equivariantActionArrowTarget V)) :
    (p ≫ equivariantActionArrowComposition V) ≫ equivariantActionArrowTarget V =
      (p ≫ pullback.fst (equivariantActionArrowSource V)
        (equivariantActionArrowTarget V)) ≫ equivariantActionArrowTarget V := by
  simp only [Category.assoc, equivariantActionArrowComposition_target]

/-- The arrow of `G` underlying a composite is the composite of the two underlying arrows. -/
theorem equivariantActionArrowComposition_base {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) :
    equivariantActionArrowComposition V ≫ equivariantActionArrowBase V =
      G.compose
        (pullback.fst (equivariantActionArrowSource V) (equivariantActionArrowTarget V) ≫
          equivariantActionArrowBase V)
        (pullback.snd (equivariantActionArrowSource V) (equivariantActionArrowTarget V) ≫
          equivariantActionArrowBase V)
        (equivariantCompositionCondition V _ _ pullback.condition) := by
  dsimp [equivariantActionArrowComposition]
  rw [pullback.lift_snd]

/-- The arrow of `G` underlying a composite, after precomposition with a generalized point. -/
theorem equivariantActionArrowComposition_base_comp {S : Scheme.{u}}
    {G : GroupoidScheme S} (V : EquivariantScheme G) {T : Over S}
    (p : T ⟶ pullback (equivariantActionArrowSource V)
      (equivariantActionArrowTarget V)) :
    (p ≫ equivariantActionArrowComposition V) ≫ equivariantActionArrowBase V =
      G.compose
        (p ≫ pullback.fst (equivariantActionArrowSource V)
          (equivariantActionArrowTarget V) ≫ equivariantActionArrowBase V)
        (p ≫ pullback.snd (equivariantActionArrowSource V)
          (equivariantActionArrowTarget V) ≫ equivariantActionArrowBase V)
        (equivariantCompositionCondition V
          (p ≫ pullback.fst (equivariantActionArrowSource V)
            (equivariantActionArrowTarget V))
          (p ≫ pullback.snd (equivariantActionArrowSource V)
            (equivariantActionArrowTarget V)) (by
              calc
                (p ≫ pullback.fst (equivariantActionArrowSource V)
                    (equivariantActionArrowTarget V)) ≫ equivariantActionArrowSource V =
                    p ≫ (pullback.fst (equivariantActionArrowSource V)
                      (equivariantActionArrowTarget V) ≫ equivariantActionArrowSource V) :=
                        Category.assoc _ _ _
                _ = p ≫ (pullback.snd (equivariantActionArrowSource V)
                      (equivariantActionArrowTarget V) ≫ equivariantActionArrowTarget V) :=
                        congrArg (fun z => p ≫ z) pullback.condition
                _ = (p ≫ pullback.snd (equivariantActionArrowSource V)
                      (equivariantActionArrowTarget V)) ≫ equivariantActionArrowTarget V :=
                        (Category.assoc _ _ _).symm)) := by
  let a := pullback.fst (equivariantActionArrowSource V)
    (equivariantActionArrowTarget V)
  let b := pullback.snd (equivariantActionArrowSource V)
    (equivariantActionArrowTarget V)
  have w := equivariantCompositionCondition V (p ≫ a) (p ≫ b) (by
    rw [Category.assoc, Category.assoc]
    exact congrArg (p ≫ ·) pullback.condition)
  rw [Category.assoc, equivariantActionArrowComposition_base]
  exact (groupoidCompose_precomp _ p _ _
    (equivariantCompositionCondition V a b pullback.condition)
    (by simpa only [Category.assoc] using w)).symm

/-- The source of a composite is the action of the composite arrow of `G` on the common target. -/
private theorem equivariantActionArrowComposition_source {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) :
    equivariantActionArrowComposition V ≫ equivariantActionArrowSource V =
      V.action
        (pullback.fst (equivariantActionArrowSource V) (equivariantActionArrowTarget V) ≫
          equivariantActionArrowTarget V)
        (G.compose
          (pullback.fst (equivariantActionArrowSource V) (equivariantActionArrowTarget V) ≫
            equivariantActionArrowBase V)
          (pullback.snd (equivariantActionArrowSource V) (equivariantActionArrowTarget V) ≫
            equivariantActionArrowBase V)
          (equivariantCompositionCondition V _ _ pullback.condition)) (by
          calc
            _ = (pullback.fst (equivariantActionArrowSource V)
                  (equivariantActionArrowTarget V) ≫ equivariantActionArrowBase V) ≫
                  G.target := equivariantActionArrowCondition V _
            _ = G.compose
                  (pullback.fst (equivariantActionArrowSource V)
                    (equivariantActionArrowTarget V) ≫ equivariantActionArrowBase V)
                  (pullback.snd (equivariantActionArrowSource V)
                    (equivariantActionArrowTarget V) ≫ equivariantActionArrowBase V)
                  (equivariantCompositionCondition V _ _ pullback.condition) ≫ G.target :=
                (groupoidCompose_target _ _ _ _).symm) := by
  simpa only [equivariantActionArrowComposition_target,
    equivariantActionArrowComposition_base] using
    equivariantActionArrowSource_comp V (equivariantActionArrowComposition V)

/-- The source of a composite is the source of its second factor. -/
theorem equivariantActionArrowComposition_source_eq_snd {S : Scheme.{u}}
    {G : GroupoidScheme S} (V : EquivariantScheme G) :
    equivariantActionArrowComposition V ≫ equivariantActionArrowSource V =
      pullback.snd (equivariantActionArrowSource V) (equivariantActionArrowTarget V) ≫
        equivariantActionArrowSource V := by
  rw [equivariantActionArrowComposition_source]
  let f := pullback.fst (equivariantActionArrowSource V) (equivariantActionArrowTarget V)
  let g := pullback.snd (equivariantActionArrowSource V) (equivariantActionArrowTarget V)
  have hw : f ≫ equivariantActionArrowSource V = g ≫ equivariantActionArrowTarget V :=
    pullback.condition
  have hbase := equivariantCompositionCondition V f g hw
  have hsource := equivariantActionArrowSource_comp V f
  have htarget : g ≫ equivariantActionArrowTarget V =
      V.action (f ≫ equivariantActionArrowTarget V)
        (f ≫ equivariantActionArrowBase V) (equivariantActionArrowCondition V f) :=
    hw.symm.trans hsource
  have wfg : V.action (f ≫ equivariantActionArrowTarget V)
        (f ≫ equivariantActionArrowBase V) (equivariantActionArrowCondition V f) ≫ V.obj.hom =
      (g ≫ equivariantActionArrowBase V) ≫ G.target :=
    (V.action_comp_hom _ _ _).trans hbase
  show V.action (f ≫ equivariantActionArrowTarget V)
      (G.compose (f ≫ equivariantActionArrowBase V) (g ≫ equivariantActionArrowBase V) hbase) _ =
    g ≫ equivariantActionArrowSource V
  calc
    _ = V.action
          (V.action (f ≫ equivariantActionArrowTarget V) (f ≫ equivariantActionArrowBase V)
            (equivariantActionArrowCondition V f)) (g ≫ equivariantActionArrowBase V) _ :=
          (equivariant_action_cocycle V (f ≫ equivariantActionArrowTarget V)
            (f ≫ equivariantActionArrowBase V) (g ≫ equivariantActionArrowBase V)
            (equivariantActionArrowCondition V f) hbase).symm
    _ = V.action (g ≫ equivariantActionArrowTarget V) (g ≫ equivariantActionArrowBase V) _ :=
          V.action_point_eq (g ≫ equivariantActionArrowBase V) wfg
            (equivariantActionArrowCondition V g) htarget.symm
    _ = g ≫ equivariantActionArrowSource V := (equivariantActionArrowSource_comp V g).symm

/-- The identity section is a section of the target map. -/
theorem equivariantActionArrowIdentity_target {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) :
    equivariantActionArrowIdentity V ≫ equivariantActionArrowTarget V =
      𝟙 (equivariantObjectOver V) := by
  dsimp [equivariantActionArrowIdentity, equivariantActionArrowTarget,
    equivariantActionArrows]
  rw [pullback.lift_fst]

/-- The identity section has underlying arrow the identity arrow of `G`. -/
theorem equivariantActionArrowIdentity_base {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) :
    equivariantActionArrowIdentity V ≫ equivariantActionArrowBase V =
      V.obj.hom ≫ G.identity := by
  dsimp [equivariantActionArrowIdentity, equivariantActionArrowBase,
    equivariantActionArrows]
  rw [pullback.lift_snd]

/-- The identity section is a section of the source map. -/
theorem equivariantActionArrowIdentity_source {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) :
    equivariantActionArrowIdentity V ≫ equivariantActionArrowSource V =
      𝟙 (equivariantObjectOver V) := by
  rw [equivariantActionArrowSource_comp]
  simpa only [equivariantActionArrowIdentity_target, equivariantActionArrowIdentity_base,
    Category.id_comp, Category.comp_id] using
    equivariant_action_identity V (𝟙 (equivariantObjectOver V))

/-- Inversion exchanges target and source. -/
theorem equivariantActionArrowInverse_target {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) :
    equivariantActionArrowInverse V ≫ equivariantActionArrowTarget V =
      equivariantActionArrowSource V := by
  dsimp [equivariantActionArrowInverse, equivariantActionArrowTarget,
    equivariantActionArrows]
  rw [pullback.lift_fst]

/-- Inversion has underlying arrow the inverse arrow of `G`. -/
theorem equivariantActionArrowInverse_base {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) :
    equivariantActionArrowInverse V ≫ equivariantActionArrowBase V =
      equivariantActionArrowBase V ≫ G.inverse := by
  dsimp [equivariantActionArrowInverse, equivariantActionArrowBase,
    equivariantActionArrows]
  rw [pullback.lift_snd]

/-- Inversion exchanges source and target. -/
theorem equivariantActionArrowInverse_source {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) :
    equivariantActionArrowInverse V ≫ equivariantActionArrowSource V =
      equivariantActionArrowTarget V := by
  rw [equivariantActionArrowSource_comp]
  simpa only [equivariantActionArrowInverse_target, equivariantActionArrowInverse_base] using
    equivariant_action_inverse V (equivariantActionArrowTarget V) (equivariantActionArrowBase V)
      (equivariantActionArrowCondition V (𝟙 (equivariantActionArrows V)))

end AlgebraicGeometry

end
