module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Equivariant.ActionGroupoid

/-!
# Cartesian groupoid schemes as equivariant schemes

Equivariant schemes for a groupoid scheme `G` are the same thing as groupoid schemes cartesian
over `G`.  This file regards the groupoid scheme attached to an equivariant scheme as cartesian
over `G`, builds the two functors between the categories, their unit and counit, and the
equivalence.

## Main definitions

* `AlgebraicGeometry.CartesianOverEquivariantEquivalenceData` specifies the forward
  construction on objects, descent isomorphisms, and morphisms.

## Main results

* `AlgebraicGeometry.cartesianOverEquivalenceEquivariantScheme` identifies groupoid schemes
  cartesian over `G` with equivariant schemes for `G`.
* Its `obj_eq`, `descentIso_hom`, and `map_hom` lemmas characterize the forward functor by the
  construction used to build it.

## References

* [Stacks Project, Tag 0APE](https://stacks.math.columbia.edu/tag/0APE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The arrows of the attached groupoid are the action arrows. -/
theorem equivariantActionGroupoid_arrows {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) :
    (equivariantActionGroupoid V).arrows = equivariantActionArrows V := rfl

/-- The source of the attached groupoid is the action. -/
theorem equivariantActionGroupoid_source {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) :
    (equivariantActionGroupoid V).source = equivariantActionArrowSource V := rfl

/-- The target of the attached groupoid is the first projection. -/
theorem equivariantActionGroupoid_target {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) :
    (equivariantActionGroupoid V).target = equivariantActionArrowTarget V := rfl

/-- The identity of the attached groupoid is the identity section. -/
theorem equivariantActionGroupoid_identity {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) :
    (equivariantActionGroupoid V).identity = equivariantActionArrowIdentity V := rfl

/-- Composition in the attached groupoid is composition of action arrows. -/
private theorem equivariantActionGroupoid_comp {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) :
    (equivariantActionGroupoid V).comp = equivariantActionArrowComposition V := rfl

/-- Composition in the attached groupoid preserves the target of the first factor, in the form
stated for `Stacks.Groupoids.GroupoidScheme.compose`. -/
private theorem equivariantActionGroupoid_compose_target {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) {T : Over S}
    (a b : T ⟶ equivariantActionArrows V)
    (w : a ≫ equivariantActionArrowSource V = b ≫ equivariantActionArrowTarget V) :
    GroupoidScheme.compose (equivariantActionGroupoid V) a b w ≫
        equivariantActionArrowTarget V = a ≫ equivariantActionArrowTarget V := by
  unfold GroupoidScheme.compose
  rw [← equivariantActionGroupoid_target, Category.assoc,
    (equivariantActionGroupoid V).target_comp, pullback.lift_fst_assoc]

/-- A generalized arrow of the attached groupoid is determined by its target and its arrow of `G`,
in the form stated for the groupoid scheme itself. -/
private theorem equivariantActionGroupoid_arrow_ext {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) {T : Over S}
    (f g : T ⟶ (equivariantActionGroupoid V).arrows)
    (ht : f ≫ (equivariantActionGroupoid V).target =
      g ≫ (equivariantActionGroupoid V).target)
    (hb : f ≫ equivariantActionArrowBase V = g ≫ equivariantActionArrowBase V) : f = g := by
  change f ≫ equivariantActionArrowTarget V = g ≫ equivariantActionArrowTarget V at ht
  exact equivariantActionArrow_ext V f g ht hb

/-- The canonical morphism from the groupoid attached to an equivariant scheme to `G`. -/
@[implicit_reducible] noncomputable def equivariantActionGroupoidHom {S : Scheme.{u}}
    {G : GroupoidScheme S} (V : EquivariantScheme G) :
    GroupoidScheme.Hom (equivariantActionGroupoid V) G where
  mapObjects := V.obj.hom
  mapArrows := equivariantActionArrowBase V
  map_source := (V.action_comp_hom
    (pullback.fst (equivariantObjectMap V) G.target)
    (pullback.snd (equivariantObjectMap V) G.target) pullback.condition).symm
  map_target := by
    change pullback.snd (equivariantObjectMap V) G.target ≫ G.target =
      pullback.fst (equivariantObjectMap V) G.target ≫ V.obj.hom
    exact pullback.condition.symm
  map_identity := (equivariantActionArrowIdentity_base V).symm
  map_comp := by
    intro T f g w w'
    let p := pullback.lift f g w
    have hp₀ : p ≫ pullback.fst (equivariantActionArrowSource V)
        (equivariantActionArrowTarget V) = f :=
      pullback.lift_fst _ _ _
    have hp₁ : p ≫ pullback.snd (equivariantActionArrowSource V)
        (equivariantActionArrowTarget V) = g :=
      pullback.lift_snd _ _ _
    have hbase := equivariantActionArrowComposition_base_comp V p
    have hfirst : p ≫ pullback.fst (equivariantActionArrowSource V)
        (equivariantActionArrowTarget V) ≫ equivariantActionArrowBase V =
          f ≫ equivariantActionArrowBase V :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ equivariantActionArrowBase V) hp₀)
    have hsecond : p ≫ pullback.snd (equivariantActionArrowSource V)
        (equivariantActionArrowTarget V) ≫ equivariantActionArrowBase V =
          g ≫ equivariantActionArrowBase V :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ equivariantActionArrowBase V) hp₁)
    exact hbase.trans (groupoidCompose_arrow_eq _ (f ≫ equivariantActionArrowBase V) _
      (g ≫ equivariantActionArrowBase V) _ w' hfirst hsecond)

/-- The canonical morphism to `G` is cartesian. -/
theorem equivariantActionGroupoidHom_cartesian {S : Scheme.{u}}
    {G : GroupoidScheme S} (V : EquivariantScheme G) :
    IsCartesian (equivariantActionGroupoidHom V) := by
  change IsPullback (equivariantActionArrowBase V).left
    (equivariantActionArrowSource V).left G.source.left V.obj.hom.left
  have hQ : IsPullback (pullback.fst G.source V.obj.hom).left
      (pullback.snd G.source V.obj.hom).left G.source.left V.obj.hom.left :=
    IsPullback.of_isLimit_cone
      (isLimitOfPreserves (Over.forget S)
        (limit.isLimit (cospan G.source V.obj.hom)))
  let e₀ := (Over.forget S).mapIso V.descentIso
  let e : (equivariantActionArrows V).left ≅ (pullback G.source V.obj.hom).left := by
    simpa only [Over.forget_obj, equivariantActionArrows, equivariantObjectMap] using e₀
  have hefst : e.hom ≫ (pullback.fst G.source V.obj.hom).left =
      (equivariantActionArrowBase V).left := by
    calc
      e.hom ≫ (pullback.fst G.source V.obj.hom).left =
          e₀.hom ≫ (pullback.fst G.source V.obj.hom).left := by simp [e]
      _ = (equivariantActionArrowBase V).left := by
          simpa [e₀, Functor.mapIso_hom, Over.forget_map, equivariantActionArrowBase,
            equivariantActionArrows, equivariantObjectMap] using
            congrArg Over.Hom.left V.descentIso_over
  have hesnd : e.hom ≫ (pullback.snd G.source V.obj.hom).left =
      (equivariantActionArrowSource V).left := by
    simp [e, e₀, Functor.mapIso_hom, Over.forget_map,
      equivariantActionArrowSource,
      equivariantActionArrows, equivariantObjectMap, EquivariantScheme.action]
  refine hQ.of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · rw [← hefst]
    simp
  · rw [← hesnd]
    simp

/-- An equivariant scheme, regarded as a groupoid scheme cartesian over `G`. -/
@[implicit_reducible] private noncomputable def equivariantAsCartesianOver {S : Scheme.{u}}
    {G : GroupoidScheme S} (V : EquivariantScheme G) : CartesianOver G where
  left := equivariantActionGroupoid V
  hom := equivariantActionGroupoidHom V
  isCartesian := equivariantActionGroupoidHom_cartesian V

/-- The map on action arrows induced by an equivariant morphism. -/
private noncomputable def equivariantActionArrowMap {S : Scheme.{u}}
    {G : GroupoidScheme S} {V W : EquivariantScheme G}
    (f : EquivariantScheme.Hom V W) : equivariantActionArrows V ⟶ equivariantActionArrows W :=
  pullback.lift (equivariantActionArrowTarget V ≫ f.hom.left)
    (equivariantActionArrowBase V) (by
      rw [Category.assoc, f.hom.w]
      exact pullback.condition)

/-- The induced map on action arrows commutes with the target maps. -/
private theorem equivariantActionArrowMap_target {S : Scheme.{u}} {G : GroupoidScheme S}
    {V W : EquivariantScheme G} (f : EquivariantScheme.Hom V W) :
    equivariantActionArrowMap f ≫ equivariantActionArrowTarget W =
      equivariantActionArrowTarget V ≫ f.hom.left := by
  dsimp [equivariantActionArrowMap, equivariantActionArrows,
    equivariantActionArrowTarget]
  rw [pullback.lift_fst]

/-- The induced map on action arrows preserves the underlying arrow of `G`. -/
private theorem equivariantActionArrowMap_base {S : Scheme.{u}} {G : GroupoidScheme S}
    {V W : EquivariantScheme G} (f : EquivariantScheme.Hom V W) :
    equivariantActionArrowMap f ≫ equivariantActionArrowBase W =
      equivariantActionArrowBase V := by
  dsimp [equivariantActionArrowMap, equivariantActionArrows,
    equivariantActionArrowBase]
  rw [pullback.lift_snd]

/-- The induced map on action arrows commutes with the source maps. -/
private theorem equivariantActionArrowMap_source {S : Scheme.{u}} {G : GroupoidScheme S}
    {V W : EquivariantScheme G} (f : EquivariantScheme.Hom V W) :
    equivariantActionArrowMap f ≫ equivariantActionArrowSource W =
      equivariantActionArrowSource V ≫ f.hom.left := by
  rw [equivariantActionArrowSource_comp]
  simp only [equivariantActionArrowMap_target, equivariantActionArrowMap_base]
  simpa only [equivariantActionArrowCondition] using
    (f.comm (equivariantActionArrows V) (equivariantActionArrowTarget V)
      (equivariantActionArrowBase V)
      (equivariantActionArrowCondition V (𝟙 (equivariantActionArrows V)))).symm

/-- The morphism of attached groupoid schemes induced by an equivariant morphism. -/
private noncomputable def equivariantActionGroupoidHomMap {S : Scheme.{u}}
    {G : GroupoidScheme S} {V W : EquivariantScheme G}
    (f : EquivariantScheme.Hom V W) :
    GroupoidScheme.Hom (equivariantActionGroupoid V) (equivariantActionGroupoid W) where
  mapObjects := f.hom.left
  mapArrows := equivariantActionArrowMap f
  map_source := equivariantActionArrowMap_source f
  map_target := equivariantActionArrowMap_target f
  map_identity := by
    apply equivariantActionArrow_ext W
    · calc
        (f.hom.left ≫ equivariantActionArrowIdentity W) ≫
            equivariantActionArrowTarget W = f.hom.left := by
              simp only [Category.assoc, equivariantActionArrowIdentity_target,
                Category.comp_id]
        _ = (equivariantActionArrowIdentity V ≫ equivariantActionArrowMap f) ≫
              equivariantActionArrowTarget W := by
                have h₁ := congrArg (fun k => k ≫ f.hom.left)
                  (equivariantActionArrowIdentity_target V)
                have h₂ := congrArg (fun k => equivariantActionArrowIdentity V ≫ k)
                  (equivariantActionArrowMap_target f)
                calc
                  f.hom.left = (𝟙 (equivariantObjectOver V)) ≫ f.hom.left :=
                    (Category.id_comp _).symm
                  _ = (equivariantActionArrowIdentity V ≫
                        equivariantActionArrowTarget V) ≫ f.hom.left := by
                          simpa only [Category.assoc, Category.id_comp] using h₁.symm
                  _ = (equivariantActionArrowIdentity V ≫
                        (equivariantActionArrowMap f ≫ equivariantActionArrowTarget W)) := by
                          exact congrArg (fun k => equivariantActionArrowIdentity V ≫ k)
                            (equivariantActionArrowMap_target f).symm
                  _ = (equivariantActionArrowIdentity V ≫ equivariantActionArrowMap f) ≫
                        equivariantActionArrowTarget W := (Category.assoc _ _ _).symm
    · calc
        (f.hom.left ≫ equivariantActionArrowIdentity W) ≫
            equivariantActionArrowBase W = V.obj.hom ≫ G.identity := by
              rw [Category.assoc, equivariantActionArrowIdentity_base,
                ← Category.assoc, f.hom.w]
        _ = (equivariantActionArrowIdentity V ≫ equivariantActionArrowMap f) ≫
              equivariantActionArrowBase W := by
                rw [Category.assoc, equivariantActionArrowMap_base,
                  equivariantActionArrowIdentity_base]
  map_comp := by
    intro T a b w w'
    let wV := equivariantCompositionCondition V a b w
    have wW : (a ≫ equivariantActionArrowMap f ≫ equivariantActionArrowBase W) ≫ G.source =
        (b ≫ equivariantActionArrowMap f ≫ equivariantActionArrowBase W) ≫ G.target := by
      have h₁ : equivariantActionArrowBase W ≫ G.source =
          equivariantActionArrowSource W ≫ W.obj.hom := (equivariantActionGroupoidHom W).map_source
      have h₂ : equivariantActionArrowBase W ≫ G.target =
          equivariantActionArrowTarget W ≫ W.obj.hom := (equivariantActionGroupoidHom W).map_target
      have := congrArg (· ≫ W.obj.hom) w'
      simp only [Category.assoc] at this
      simp only [Category.assoc, h₁, h₂]
      exact this
    let cV := GroupoidScheme.compose (equivariantActionGroupoid V) a b w
    let cW := GroupoidScheme.compose (equivariantActionGroupoid W)
      (a ≫ equivariantActionArrowMap f) (b ≫ equivariantActionArrowMap f) w'
    have hbaseV := (equivariantActionGroupoidHom V).map_comp T a b w wV
    have hbaseW := (equivariantActionGroupoidHom W).map_comp T
      (a ≫ equivariantActionArrowMap f) (b ≫ equivariantActionArrowMap f) w' wW
    change cV ≫ equivariantActionArrowMap f = cW
    apply equivariantActionGroupoid_arrow_ext W (cV ≫ equivariantActionArrowMap f) cW
    · calc
        (cV ≫ equivariantActionArrowMap f) ≫ equivariantActionArrowTarget W =
            cV ≫ (equivariantActionArrowMap f ≫ equivariantActionArrowTarget W) :=
              Category.assoc _ _ _
        _ = cV ≫ (equivariantActionArrowTarget V ≫ f.hom.left) :=
              congrArg (fun k => cV ≫ k) (equivariantActionArrowMap_target f)
        _ = (a ≫ equivariantActionArrowTarget V) ≫ f.hom.left := by
              have ht := congrArg (fun k => k ≫ f.hom.left)
                (equivariantActionGroupoid_compose_target V a b w)
              simpa only [Category.assoc] using ht
        _ = (a ≫ equivariantActionArrowMap f) ≫ equivariantActionArrowTarget W := by
              calc
                _ = a ≫ (equivariantActionArrowTarget V ≫ f.hom.left) :=
                  Category.assoc _ _ _
                _ = a ≫ (equivariantActionArrowMap f ≫
                    equivariantActionArrowTarget W) :=
                      congrArg (fun k => a ≫ k)
                        (equivariantActionArrowMap_target f).symm
                _ = (a ≫ equivariantActionArrowMap f) ≫
                    equivariantActionArrowTarget W := (Category.assoc _ _ _).symm
        _ = cW ≫ equivariantActionArrowTarget W := by
              symm
              exact equivariantActionGroupoid_compose_target W
                (a ≫ equivariantActionArrowMap f) (b ≫ equivariantActionArrowMap f) w'
    · calc
        (cV ≫ equivariantActionArrowMap f) ≫ equivariantActionArrowBase W =
            cV ≫ equivariantActionArrowBase V := by
              rw [Category.assoc, equivariantActionArrowMap_base]
        _ = G.compose (a ≫ equivariantActionArrowBase V)
              (b ≫ equivariantActionArrowBase V) wV := hbaseV
        _ = G.compose
              (a ≫ equivariantActionArrowMap f ≫ equivariantActionArrowBase W)
              (b ≫ equivariantActionArrowMap f ≫ equivariantActionArrowBase W) wW := by
                apply groupoidCompose_arrow_eq
                · exact congrArg (fun k => a ≫ k)
                    (equivariantActionArrowMap_base f).symm
                · exact congrArg (fun k => b ≫ k)
                    (equivariantActionArrowMap_base f).symm
        _ = cW ≫ equivariantActionArrowBase W := hbaseW.symm

/-- The equivariant morphism induced by a morphism of groupoid schemes cartesian over `G`. -/
private noncomputable def cartesianOverToEquivariantHom {S : Scheme.{u}}
    {G : GroupoidScheme S} {X Y : CartesianOver G} (f : X ⟶ Y) :
    EquivariantScheme.Hom (cartesianOverToEquivariant X)
      (cartesianOverToEquivariant Y) where
  hom := Over.homMk f.hom.mapObjects f.mapObjects_comp
  comm := by
    intro T v a w
    let α := cartesianOverLiftArrow X v a w
    have w' : (v ≫ f.hom.mapObjects) ≫ Y.hom.mapObjects = a ≫ G.target := by
      rw [Category.assoc, f.mapObjects_comp]
      exact w
    let β := cartesianOverLiftArrow Y (v ≫ f.hom.mapObjects) a w'
    have hβ : α ≫ f.hom.mapArrows = β := by
      apply cartesianOverLiftArrow_ext Y (α ≫ f.hom.mapArrows) β
      · rw [Category.assoc, f.hom.map_target, ← Category.assoc, cartesianOverLiftArrow_target,
          cartesianOverLiftArrow_target]
      · rw [Category.assoc, f.mapArrows_comp, cartesianOverLiftArrow_mapArrows,
          cartesianOverLiftArrow_mapArrows]
    calc
      (pullback.lift v a w ≫ (cartesianOverDescentIso X).hom ≫
          pullback.snd G.source X.hom.mapObjects) ≫ f.hom.mapObjects =
          (α ≫ X.left.source) ≫ f.hom.mapObjects := by
            exact congrArg (fun k => k ≫ f.hom.mapObjects)
              (cartesianOverDescentIso_action X v a w)
      _ = α ≫ (X.left.source ≫ f.hom.mapObjects) := Category.assoc _ _ _
      _ = α ≫ (f.hom.mapArrows ≫ Y.left.source) :=
            congrArg (fun k => α ≫ k) f.hom.map_source.symm
      _ = (α ≫ f.hom.mapArrows) ≫ Y.left.source := (Category.assoc _ _ _).symm
      _ = β ≫ Y.left.source := congrArg (fun k => k ≫ Y.left.source) hβ
      _ = pullback.lift (v ≫ f.hom.mapObjects) a w' ≫
            (cartesianOverDescentIso Y).hom ≫
              pullback.snd G.source Y.hom.mapObjects :=
                (cartesianOverDescentIso_action Y (v ≫ f.hom.mapObjects) a w').symm

/-- The functor from groupoid schemes cartesian over `G` to equivariant schemes. -/
@[implicit_reducible] private noncomputable def cartesianOverToEquivariantFunctor {S : Scheme.{u}}
    (G : GroupoidScheme S) : CartesianOver G ⥤ EquivariantScheme G where
  obj := cartesianOverToEquivariant
  map := cartesianOverToEquivariantHom
  map_id := by
    intro X
    change cartesianOverToEquivariantHom (𝟙 X) =
      EquivariantScheme.Hom.id (cartesianOverToEquivariant X)
    apply EquivariantScheme.hom_ext
    apply Over.OverMorphism.ext
    change (GroupoidScheme.Hom.id X.left).mapObjects = 𝟙 X.left.objects
    rfl
  map_comp := by
    intro X Y Z f g
    change cartesianOverToEquivariantHom (f ≫ g) =
      EquivariantScheme.Hom.comp (cartesianOverToEquivariantHom f)
        (cartesianOverToEquivariantHom g)
    apply EquivariantScheme.hom_ext
    apply Over.OverMorphism.ext
    change (GroupoidScheme.Hom.comp f.hom g.hom).mapObjects =
      f.hom.mapObjects ≫ g.hom.mapObjects
    rfl

/-- The functor from equivariant schemes to groupoid schemes cartesian over `G`. -/
@[implicit_reducible] private noncomputable def equivariantToCartesianFunctor {S : Scheme.{u}}
    (G : GroupoidScheme S) : EquivariantScheme G ⥤ CartesianOver G where
  obj := equivariantAsCartesianOver
  map f :=
    { hom := equivariantActionGroupoidHomMap f
      mapObjects_comp := f.hom.w
      mapArrows_comp := equivariantActionArrowMap_base f }
  map_id := by
    intro V
    apply CartesianOver.hom_ext
    apply CartesianOver.groupoidHom_ext
    · change (EquivariantScheme.Hom.id V).hom.left = 𝟙 V.obj.left
      rfl
    · change equivariantActionArrowMap (EquivariantScheme.Hom.id V) =
        𝟙 (equivariantActionArrows V)
      apply equivariantActionArrow_ext V
      · rw [equivariantActionArrowMap_target]
        simp [EquivariantScheme.Hom.id]
      · rw [equivariantActionArrowMap_base]
        simp
  map_comp := by
    intro V W Z f g
    apply CartesianOver.hom_ext
    apply CartesianOver.groupoidHom_ext
    · change (EquivariantScheme.Hom.comp f g).hom.left = f.hom.left ≫ g.hom.left
      rfl
    · change equivariantActionArrowMap (EquivariantScheme.Hom.comp f g) =
        equivariantActionArrowMap f ≫ equivariantActionArrowMap g
      apply equivariantActionArrow_ext Z
      · simp only [Category.assoc, equivariantActionArrowMap_target,
          reassoc_of% equivariantActionArrowMap_target]
        rfl
      · simp only [Category.assoc, equivariantActionArrowMap_base]

/-- For the cartesian groupoid scheme attached to an equivariant scheme, lifting an arrow is the
evident map into the fibre product. -/
private theorem cartesianOverLiftArrow_reconstructed_eq {S : Scheme.{u}}
    {G : GroupoidScheme S} (V : EquivariantScheme G) {T : Over S}
    (v : T ⟶ V.obj.left) (f : T ⟶ G.arrows)
    (w : v ≫ V.obj.hom = f ≫ G.target) :
    cartesianOverLiftArrow (equivariantAsCartesianOver V) v f w =
      pullback.lift v f w := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    simpa [equivariantAsCartesianOver, equivariantActionGroupoid,
      equivariantActionGroupoid_target] using
      cartesianOverLiftArrow_target (equivariantAsCartesianOver V) v f w
  · rw [pullback.lift_snd]
    simpa [equivariantAsCartesianOver, equivariantActionGroupoid,
      equivariantActionGroupoidHom] using
      cartesianOverLiftArrow_mapArrows (equivariantAsCartesianOver V) v f w

/-- Lifting the image of an arrow along its own target gives that arrow back. -/
private theorem cartesianOverLiftArrow_id {S : Scheme.{u}}
    {G : GroupoidScheme S} (X : CartesianOver G) :
    cartesianOverLiftArrow X X.left.target X.hom.mapArrows X.hom.map_target.symm =
      𝟙 X.left.arrows := by
  apply cartesianOverLiftArrow_ext X
  · rw [cartesianOverLiftArrow_target, Category.id_comp]
  · rw [cartesianOverLiftArrow_mapArrows, Category.id_comp]

/-- Lifting the target and the arrow of `G` into the fibre product is the target comparison. -/
private theorem lift_target_mapArrows_eq_cartesianOverTargetComparison {S : Scheme.{u}}
    {G : GroupoidScheme S} (X : CartesianOver G) :
    pullback.lift X.left.target X.hom.mapArrows X.hom.map_target.symm =
      (cartesianOverTargetComparison X).hom := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst, cartesianOverTargetComparison_hom_fst]
  · rw [pullback.lift_snd, cartesianOverTargetComparison_hom_snd]

/-- The target comparison identifies the source map of the attached groupoid with the source map
upstairs. -/
private theorem cartesianOverTargetComparison_source {S : Scheme.{u}}
    {G : GroupoidScheme S} (X : CartesianOver G) :
    (cartesianOverTargetComparison X).hom ≫
        (equivariantActionGroupoid (cartesianOverToEquivariant X)).source =
      X.left.source := by
  change (cartesianOverTargetComparison X).hom ≫
      (pullback.lift (pullback.fst X.hom.mapObjects G.target)
        (pullback.snd X.hom.mapObjects G.target) pullback.condition ≫
          (cartesianOverDescentIso X).hom ≫
            pullback.snd G.source X.hom.mapObjects) = _
  have hlift_id : pullback.lift (pullback.fst X.hom.mapObjects G.target)
      (pullback.snd X.hom.mapObjects G.target) pullback.condition =
        𝟙 (pullback X.hom.mapObjects G.target) := by
    apply pullback.hom_ext <;> simp
  rw [hlift_id, Category.id_comp, ← lift_target_mapArrows_eq_cartesianOverTargetComparison,
    cartesianOverDescentIso_action X X.left.target X.hom.mapArrows,
    cartesianOverLiftArrow_id]
  simp

/-- The comparison morphism from a cartesian groupoid scheme to the groupoid attached to its
equivariant scheme. -/
@[implicit_reducible] private noncomputable def cartesianOverUnitHom {S : Scheme.{u}}
    {G : GroupoidScheme S} (X : CartesianOver G) :
    X ⟶ equivariantAsCartesianOver (cartesianOverToEquivariant X) where
  hom := {
    mapObjects := 𝟙 X.left.objects
    mapArrows := (cartesianOverTargetComparison X).hom
    map_source := by
      change (cartesianOverTargetComparison X).hom ≫
          (equivariantActionGroupoid (cartesianOverToEquivariant X)).source =
        X.left.source ≫ 𝟙 X.left.objects
      rw [Category.comp_id]
      exact cartesianOverTargetComparison_source X
    map_target := by
      change (cartesianOverTargetComparison X).hom ≫
          pullback.fst X.hom.mapObjects G.target = X.left.target ≫ 𝟙 X.left.objects
      rw [Category.comp_id]
      exact cartesianOverTargetComparison_hom_fst X
    map_identity := by
      change 𝟙 X.left.objects ≫ equivariantActionArrowIdentity (cartesianOverToEquivariant X) =
        X.left.identity ≫ (cartesianOverTargetComparison X).hom
      rw [Category.id_comp]
      apply equivariantActionArrow_ext (cartesianOverToEquivariant X)
      · rw [equivariantActionArrowIdentity_target]
        change 𝟙 X.left.objects = (X.left.identity ≫ (cartesianOverTargetComparison X).hom) ≫
          pullback.fst X.hom.mapObjects G.target
        rw [Category.assoc, cartesianOverTargetComparison_hom_fst, X.left.target_identity]
      · rw [equivariantActionArrowIdentity_base]
        change X.hom.mapObjects ≫ G.identity =
          (X.left.identity ≫ (cartesianOverTargetComparison X).hom) ≫
            pullback.snd X.hom.mapObjects G.target
        rw [Category.assoc, cartesianOverTargetComparison_hom_snd]
        exact X.hom.map_identity
    map_comp := by
      intro T a b w w'
      apply equivariantActionGroupoid_arrow_ext (cartesianOverToEquivariant X)
      · change (X.left.compose a b w ≫ (cartesianOverTargetComparison X).hom) ≫
            (equivariantActionGroupoid (cartesianOverToEquivariant X)).target =
          (equivariantActionGroupoid (cartesianOverToEquivariant X)).compose
            (a ≫ (cartesianOverTargetComparison X).hom)
            (b ≫ (cartesianOverTargetComparison X).hom) w' ≫
              (equivariantActionGroupoid (cartesianOverToEquivariant X)).target
        rw [groupoidCompose_target]
        change (X.left.compose a b w ≫ (cartesianOverTargetComparison X).hom) ≫
            pullback.fst X.hom.mapObjects G.target =
          (a ≫ (cartesianOverTargetComparison X).hom) ≫
            pullback.fst X.hom.mapObjects G.target
        simp only [Category.assoc, cartesianOverTargetComparison_hom_fst]
        exact groupoidCompose_target _ a b w
      · let F := equivariantActionGroupoidHom (cartesianOverToEquivariant X)
        have h : (cartesianOverTargetComparison X).hom ≫ F.mapArrows =
            X.hom.mapArrows := cartesianOverTargetComparison_hom_snd X
        have wG : (a ≫ X.hom.mapArrows) ≫ G.source =
            (b ≫ X.hom.mapArrows) ≫ G.target := by
          simpa only [Category.assoc, X.hom.map_source, X.hom.map_target] using
            congrArg (fun q => q ≫ X.hom.mapObjects) w
        have wG' : ((a ≫ (cartesianOverTargetComparison X).hom) ≫ F.mapArrows) ≫
            G.source = ((b ≫ (cartesianOverTargetComparison X).hom) ≫ F.mapArrows) ≫
              G.target := by simpa only [Category.assoc, h] using wG
        change (X.left.compose a b w ≫ (cartesianOverTargetComparison X).hom) ≫
            F.mapArrows =
          (equivariantActionGroupoid (cartesianOverToEquivariant X)).compose
            (a ≫ (cartesianOverTargetComparison X).hom)
            (b ≫ (cartesianOverTargetComparison X).hom) w' ≫ F.mapArrows
        rw [Category.assoc, h, X.hom.map_comp T a b w wG,
          F.map_comp T _ _ w' wG']
        apply groupoidCompose_arrow_eq <;> simp only [Category.assoc, h]
  }
  mapObjects_comp := Category.id_comp _
  mapArrows_comp := cartesianOverTargetComparison_hom_snd X

/-- The inverse of a morphism of groupoid schemes whose two components are isomorphisms. -/
private noncomputable def groupoidHomInv {S : Scheme.{u}}
    {G H : GroupoidScheme S} (F : GroupoidScheme.Hom G H)
    [IsIso F.mapObjects] [IsIso F.mapArrows] : GroupoidScheme.Hom H G where
  mapObjects := inv F.mapObjects
  mapArrows := inv F.mapArrows
  map_source := by
    apply (cancel_mono F.mapObjects).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [← F.map_source, IsIso.inv_hom_id_assoc]
  map_target := by
    apply (cancel_mono F.mapObjects).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [← F.map_target, IsIso.inv_hom_id_assoc]
  map_identity := by
    apply (cancel_mono F.mapArrows).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [← F.map_identity, IsIso.inv_hom_id_assoc]
  map_comp := by
    intro T a b w w'
    apply (cancel_mono F.mapArrows).1
    have w'' : ((a ≫ inv F.mapArrows) ≫ F.mapArrows) ≫ H.source =
        ((b ≫ inv F.mapArrows) ≫ F.mapArrows) ≫ H.target := by simpa using w
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      F.map_comp T _ _ w' w'']
    apply groupoidCompose_arrow_eq <;> simp

/-- A morphism of cartesian groupoid schemes whose two components are isomorphisms is an
isomorphism. -/
@[implicit_reducible] private noncomputable def cartesianOverIsoOfComponents {S : Scheme.{u}}
    {G : GroupoidScheme S} {X Y : CartesianOver G} (f : X ⟶ Y)
    [IsIso f.hom.mapObjects] [IsIso f.hom.mapArrows] : X ≅ Y where
  hom := f
  inv := {
    hom := groupoidHomInv f.hom
    mapObjects_comp := by
      change inv f.hom.mapObjects ≫ X.hom.mapObjects = Y.hom.mapObjects
      rw [← f.mapObjects_comp, IsIso.inv_hom_id_assoc]
    mapArrows_comp := by
      change inv f.hom.mapArrows ≫ X.hom.mapArrows = Y.hom.mapArrows
      rw [← f.mapArrows_comp, IsIso.inv_hom_id_assoc]
  }
  hom_inv_id := by
    apply CartesianOver.hom_ext
    apply CartesianOver.groupoidHom_ext
    · exact IsIso.hom_inv_id _
    · exact IsIso.hom_inv_id _
  inv_hom_id := by
    apply CartesianOver.hom_ext
    apply CartesianOver.groupoidHom_ext
    · exact IsIso.inv_hom_id _
    · exact IsIso.inv_hom_id _

/-- A cartesian groupoid scheme is isomorphic to the groupoid attached to its equivariant
scheme. -/
@[implicit_reducible] private noncomputable def cartesianOverUnitIso {S : Scheme.{u}}
    {G : GroupoidScheme S} (X : CartesianOver G) :
    X ≅ equivariantAsCartesianOver (cartesianOverToEquivariant X) := by
  letI : IsIso (cartesianOverUnitHom X).hom.mapObjects :=
    inferInstanceAs (IsIso (𝟙 X.left.objects))
  letI : IsIso (cartesianOverUnitHom X).hom.mapArrows :=
    inferInstanceAs (IsIso (cartesianOverTargetComparison X).hom)
  exact cartesianOverIsoOfComponents (cartesianOverUnitHom X)

/-- The unit isomorphism of the equivalence. -/
private noncomputable def cartesianOverUnitNatIso {S : Scheme.{u}}
    (G : GroupoidScheme S) :
    𝟭 (CartesianOver G) ≅
      cartesianOverToEquivariantFunctor G ⋙ equivariantToCartesianFunctor G :=
  NatIso.ofComponents cartesianOverUnitIso (by
    intro X Y f
    apply CartesianOver.hom_ext
    apply CartesianOver.groupoidHom_ext
    · change f.hom.mapObjects ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.mapObjects
      simp
    · change f.hom.mapArrows ≫ (cartesianOverTargetComparison Y).hom =
        (cartesianOverTargetComparison X).hom ≫
          equivariantActionArrowMap (cartesianOverToEquivariantHom f)
      apply pullback.hom_ext
      · have ht : equivariantActionArrowMap (cartesianOverToEquivariantHom f) ≫
            pullback.fst Y.hom.mapObjects G.target =
          pullback.fst X.hom.mapObjects G.target ≫ f.hom.mapObjects :=
          equivariantActionArrowMap_target (cartesianOverToEquivariantHom f)
        simp only [Category.assoc, ht, cartesianOverTargetComparison_hom_fst]
        rw [← Category.assoc, cartesianOverTargetComparison_hom_fst]
        exact f.hom.map_target
      · have hb : equivariantActionArrowMap (cartesianOverToEquivariantHom f) ≫
            pullback.snd Y.hom.mapObjects G.target =
          pullback.snd X.hom.mapObjects G.target :=
          equivariantActionArrowMap_base (cartesianOverToEquivariantHom f)
        simp only [Category.assoc, hb, cartesianOverTargetComparison_hom_snd]
        exact f.mapArrows_comp)

/-- The equivariant scheme of the cartesian groupoid scheme attached to an equivariant scheme has
the same action. -/
private theorem cartesianOverToEquivariant_action_reconstructed {S : Scheme.{u}}
    {G : GroupoidScheme S} (V : EquivariantScheme G) {T : Over S}
    (v : T ⟶ V.obj.left) (f : T ⟶ G.arrows)
    (w : v ≫ V.obj.hom = f ≫ G.target) :
    (cartesianOverToEquivariant (equivariantAsCartesianOver V)).action v f w =
      V.action v f w := by
  calc
    _ = cartesianOverLiftArrow (equivariantAsCartesianOver V) v f w ≫
        (equivariantAsCartesianOver V).left.source :=
      cartesianOverDescentIso_action (equivariantAsCartesianOver V) v f w
    _ = pullback.lift v f w ≫ equivariantActionArrowSource V :=
      congrArg (fun k => k ≫ equivariantActionArrowSource V)
        (cartesianOverLiftArrow_reconstructed_eq V v f w)
    _ = V.action v f w := by
      rw [equivariantActionArrowSource_comp]
      simp only [pullback.lift_fst, pullback.lift_snd]

/-- An equivariant scheme is isomorphic to the equivariant scheme of its cartesian groupoid
scheme. -/
private noncomputable def cartesianOverCounitIso {S : Scheme.{u}}
    {G : GroupoidScheme S} (V : EquivariantScheme G) :
    cartesianOverToEquivariant (equivariantAsCartesianOver V) ≅ V where
  hom := {
    hom := Over.homMk (𝟙 V.obj.left)
    comm := by
      intro T v f w
      change (cartesianOverToEquivariant (equivariantAsCartesianOver V)).action v f w ≫
        𝟙 _ = V.action (v ≫ 𝟙 _) f _
      simpa only [Category.comp_id] using
        cartesianOverToEquivariant_action_reconstructed V v f w
  }
  inv := {
    hom := Over.homMk (𝟙 V.obj.left)
    comm := by
      intro T v f w
      change V.action v f w ≫ 𝟙 _ =
        (cartesianOverToEquivariant (equivariantAsCartesianOver V)).action (v ≫ 𝟙 _) f _
      simpa only [Category.comp_id] using
        (cartesianOverToEquivariant_action_reconstructed V v f w).symm
  }
  hom_inv_id := by
    apply EquivariantScheme.hom_ext
    apply Over.OverMorphism.ext
    exact Category.id_comp _
  inv_hom_id := by
    apply EquivariantScheme.hom_ext
    apply Over.OverMorphism.ext
    exact Category.id_comp _

/-- The counit isomorphism of the equivalence. -/
private noncomputable def cartesianOverCounitNatIso {S : Scheme.{u}}
    (G : GroupoidScheme S) :
    equivariantToCartesianFunctor G ⋙ cartesianOverToEquivariantFunctor G ≅
      𝟭 (EquivariantScheme G) :=
  NatIso.ofComponents cartesianOverCounitIso (by
    intro V W f
    apply EquivariantScheme.hom_ext
    apply Over.OverMorphism.ext
    change f.hom.left ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.left
    simp)

/-- An equivalence between groupoid schemes cartesian over `G` and equivariant schemes for `G`,
together with equations describing its forward functor.

The descent equation is `(t', f) ≫ φ = (f, s')`, after identifying the
underlying object with `U'`. Since the cartesian groupoid morphism makes both
comparison maps isomorphisms, this characterizes `φ = (f, s') ∘ (t', f)⁻¹`.
The morphism equation says that the forward functor uses the object map. -/
structure CartesianOverEquivariantEquivalenceData
    {S : Scheme.{u}} (G : GroupoidScheme S) where
  /-- The equivalence of categories. -/
  equivalence : CartesianOver G ≌ EquivariantScheme G
  /-- The forward construction keeps the object scheme and its map to `G`. -/
  obj_eq (X : CartesianOver G) :
    (equivalence.functor.obj X).obj = Over.mk X.hom.mapObjects
  /-- The descent isomorphism is induced by the target and source squares. -/
  descentIso_hom (X : CartesianOver G) :
    pullback.lift
        (X.left.target ≫ (eqToHom (obj_eq X).symm).left) X.hom.mapArrows
        (by simpa only [Category.assoc, Over.w, Over.mk_hom] using X.hom.map_target.symm) ≫
      (equivalence.functor.obj X).descentIso.hom =
    pullback.lift X.hom.mapArrows
      (X.left.source ≫ (eqToHom (obj_eq X).symm).left)
      (by simpa only [Category.assoc, Over.w, Over.mk_hom] using X.hom.map_source)
  /-- On morphisms the forward construction is induced by `hom.mapObjects`. -/
  map_hom {X Y : CartesianOver G} (f : X ⟶ Y) :
    (equivalence.functor.map f).hom ≫ eqToHom (obj_eq Y) =
      eqToHom (obj_eq X) ≫
        Over.homMk (U := Over.mk X.hom.mapObjects) (V := Over.mk Y.hom.mapObjects)
          f.hom.mapObjects f.mapObjects_comp

/-- There is an equivalence between groupoid schemes cartesian over `G` and equivariant schemes
for `G` satisfying the equations of `CartesianOverEquivariantEquivalenceData` on objects, descent
isomorphisms, and morphisms. -/
@[stacks 0APE "the equivalence with the forward construction in the proof"]
theorem nonempty_cartesianOverEquivariantEquivalenceData
    {S : Scheme.{u}} (G : GroupoidScheme S) :
    Nonempty (CartesianOverEquivariantEquivalenceData G) := by
  refine ⟨{
    equivalence := CategoryTheory.Equivalence.mk (cartesianOverToEquivariantFunctor G)
      (equivariantToCartesianFunctor G) (cartesianOverUnitNatIso G)
      (cartesianOverCounitNatIso G)
    obj_eq := fun X => rfl
    descentIso_hom := ?_
    map_hom := ?_
  }⟩
  · intro X
    change pullback.lift (X.left.target ≫ 𝟙 _) X.hom.mapArrows _ ≫
        (cartesianOverDescentIso X).hom =
      pullback.lift X.hom.mapArrows (X.left.source ≫ 𝟙 _) _
    simp only [Category.comp_id]
    rw [lift_target_mapArrows_eq_cartesianOverTargetComparison]
    change (cartesianOverTargetComparison X).hom ≫
      ((cartesianOverTargetComparison X).inv ≫ (cartesianOverSourceComparison X).hom) = _
    rw [Iso.hom_inv_id_assoc]
    apply pullback.hom_ext
    · rw [cartesianOverSourceComparison_hom_fst, pullback.lift_fst]
    · rw [cartesianOverSourceComparison_hom_snd, pullback.lift_snd]
  · intro X Y f
    apply Over.OverMorphism.ext
    change f.hom.mapObjects ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.mapObjects
    simp

/-- A chosen equivalence between groupoid schemes cartesian over `G` and equivariant schemes for
`G`, with its characterizing equations. -/
noncomputable def cartesianOverEquivariantEquivalenceData
    {S : Scheme.{u}} (G : GroupoidScheme S) :
    CartesianOverEquivariantEquivalenceData G :=
  Classical.choice (nonempty_cartesianOverEquivariantEquivalenceData G)

/-- Cartesian groupoid schemes over `G` are equivalent to schemes over the
object scheme of `G` endowed with a normalized cocyclic pullback isomorphism. -/
@[stacks 0APE]
noncomputable def cartesianOverEquivalenceEquivariantScheme
    {S : Scheme.{u}} (G : GroupoidScheme S) :
    CartesianOver G ≌ EquivariantScheme G :=
  (cartesianOverEquivariantEquivalenceData G).equivalence

/-- The forward equivalence keeps the object scheme and its structure map. -/
theorem cartesianOverEquivalenceEquivariantScheme_obj_eq
    {S : Scheme.{u}} (G : GroupoidScheme S) (X : CartesianOver G) :
    ((cartesianOverEquivalenceEquivariantScheme G).functor.obj X).obj =
      Over.mk X.hom.mapObjects :=
  (cartesianOverEquivariantEquivalenceData G).obj_eq X

/-- The forward equivalence uses the descent isomorphism induced by the
cartesian groupoid morphism: `(t', f) ≫ φ = (f, s')`. -/
theorem cartesianOverEquivalenceEquivariantScheme_descentIso_hom
    {S : Scheme.{u}} (G : GroupoidScheme S) (X : CartesianOver G) :
    pullback.lift
        (X.left.target ≫ (eqToHom
          (cartesianOverEquivalenceEquivariantScheme_obj_eq G X).symm).left)
        X.hom.mapArrows
        (by simpa only [Category.assoc, Over.w, Over.mk_hom] using X.hom.map_target.symm) ≫
      ((cartesianOverEquivalenceEquivariantScheme G).functor.obj X).descentIso.hom =
    pullback.lift X.hom.mapArrows
      (X.left.source ≫ (eqToHom
        (cartesianOverEquivalenceEquivariantScheme_obj_eq G X).symm).left)
      (by simpa only [Category.assoc, Over.w, Over.mk_hom] using X.hom.map_source) :=
  (cartesianOverEquivariantEquivalenceData G).descentIso_hom X

/-- The forward equivalence sends a morphism to its object map, under the
specified identifications of the underlying objects. -/
theorem cartesianOverEquivalenceEquivariantScheme_map_hom
    {S : Scheme.{u}} (G : GroupoidScheme S) {X Y : CartesianOver G} (f : X ⟶ Y) :
    ((cartesianOverEquivalenceEquivariantScheme G).functor.map f).hom ≫
        eqToHom (cartesianOverEquivalenceEquivariantScheme_obj_eq G Y) =
      eqToHom (cartesianOverEquivalenceEquivariantScheme_obj_eq G X) ≫
        Over.homMk (U := Over.mk X.hom.mapObjects) (V := Over.mk Y.hom.mapObjects)
          f.hom.mapObjects f.mapObjects_comp :=
  (cartesianOverEquivariantEquivalenceData G).map_hom f


end AlgebraicGeometry

end
