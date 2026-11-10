module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Cartesian
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Compose
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.OverPullbackLeft
public import StacksFrontier.AlgebraicGeometry.Groupoids.FieldExtensionEvaluation
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.GroupoidInverse
public import StacksCore.Tactic.StacksAttribute

/-!
# Equivariant schemes for a groupoid scheme

For a groupoid scheme `G`, a scheme over its object scheme together with an isomorphism
between its two pullbacks to the arrow scheme is called an equivariant scheme.  The
isomorphism is required to be the identity on identity arrows and to satisfy the cocycle
condition on composable arrows.  This file sets up the two categories that the equivalence of
Tag 0APE compares, the calculus of the action of an equivariant scheme, and the equivariant
scheme attached to a groupoid scheme cartesian over `G`.

## Main definitions

* `AlgebraicGeometry.EquivariantScheme` packages a scheme over the object scheme and its
  normalized, cocyclic pullback isomorphism.
* `AlgebraicGeometry.EquivariantScheme.Hom` is an equivariant morphism.
* `AlgebraicGeometry.cartesianOverToEquivariant` is the equivariant scheme attached to a
  groupoid scheme cartesian over `G`.

## Main results

* `AlgebraicGeometry.EquivariantScheme.action_comp_hom`,
  `AlgebraicGeometry.EquivariantScheme.comp_action`,
  `AlgebraicGeometry.EquivariantScheme.action_arrow_eq` and
  `AlgebraicGeometry.EquivariantScheme.action_point_eq` are the calculus of the action of an
  equivariant scheme on generalized points: the action of an arrow lies over the source of
  that arrow, it commutes with change of test object, and it is unchanged when the acting
  arrow, respectively the point acted on, is replaced by an equal one.

## Implementation notes

The normalization and cocycle conditions are expressed on arbitrary generalized points.  This
is the internal categorical form of the two base-change equations of Tag 0APE and avoids
choosing comparison isomorphisms between iterated pullbacks.  The auxiliary category structures
on groupoid morphisms and cartesian objects make the two categories occurring in the statement
explicit.

## References

* [Stacks Project, Tag 0APE](https://stacks.math.columbia.edu/tag/0APE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- A morphism of groupoid schemes cartesian for the source maps is also cartesian for the target
maps, because the two are exchanged by inversion. -/
theorem cartesianOver_target_pullback {S : Scheme.{u}} {G : GroupoidScheme S}
    (X : CartesianOver G) :
    IsPullback X.hom.mapArrows.left X.left.target.left G.target.left
      X.hom.mapObjects.left := by
  have hsource : IsPullback X.hom.mapArrows.left X.left.source.left G.source.left
      X.hom.mapObjects.left := X.isCartesian
  let e₁ : X.left.arrows.left ≅ X.left.arrows.left :=
    { hom := X.left.inverse.left
      inv := X.left.inverse.left
      hom_inv_id := by simpa using congrArg Over.Hom.left (groupoidInverse_involutive X.left)
      inv_hom_id := by simpa using congrArg Over.Hom.left (groupoidInverse_involutive X.left) }
  let e₂ : G.arrows.left ≅ G.arrows.left :=
    { hom := G.inverse.left
      inv := G.inverse.left
      hom_inv_id := by simpa using congrArg Over.Hom.left (groupoidInverse_involutive G)
      inv_hom_id := by simpa using congrArg Over.Hom.left (groupoidInverse_involutive G) }
  have hmapinv := congrArg Over.Hom.left (groupoidHom_map_inverse X.hom)
  refine hsource.of_iso e₁ e₂ (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change X.hom.mapArrows.left ≫ G.inverse.left =
      X.left.inverse.left ≫ X.hom.mapArrows.left
    simpa only [Over.comp_left] using hmapinv
  · change X.left.source.left = X.left.inverse.left ≫ X.left.target.left
    simpa only [Over.comp_left] using
      (congrArg Over.Hom.left X.left.target_inverse).symm
  · change G.source.left = G.inverse.left ≫ G.target.left
    simpa only [Over.comp_left] using
      (congrArg Over.Hom.left G.target_inverse).symm
  · simp

/-- For a groupoid scheme cartesian over `G`, the arrow scheme is the fibre product of the map on
objects with the target map of `G`. -/
noncomputable def cartesianOverTargetComparison {S : Scheme.{u}}
    {G : GroupoidScheme S} (X : CartesianOver G) :
    X.left.arrows ≅ pullback X.hom.mapObjects G.target := by
  let h := cartesianOver_target_pullback X
  exact Over.isoMk (h.flip.isoPullback ≪≫
    (overPullbackLeftIso X.hom.mapObjects G.target).symm) (by
      simp only [Iso.trans_hom, Iso.symm_hom]
      rw [← Over.w (pullback.fst X.hom.mapObjects G.target :
        pullback X.hom.mapObjects G.target ⟶ X.left.objects), Category.assoc,
        reassoc_of% overPullbackLeftIso_inv_fst, reassoc_of% h.flip.isoPullback_hom_fst]
      exact X.left.target.w)

/-- For a groupoid scheme cartesian over `G`, the arrow scheme is the fibre product of the source
map of `G` with the map on objects. -/
noncomputable def cartesianOverSourceComparison {S : Scheme.{u}}
    {G : GroupoidScheme S} (X : CartesianOver G) :
    X.left.arrows ≅ pullback G.source X.hom.mapObjects :=
  Over.isoMk (X.isCartesian.isoPullback ≪≫
    (overPullbackLeftIso G.source X.hom.mapObjects).symm) (by
      simp only [Iso.trans_hom, Iso.symm_hom]
      rw [← Over.w (pullback.snd G.source X.hom.mapObjects :
        pullback G.source X.hom.mapObjects ⟶ X.left.objects), Category.assoc,
        reassoc_of% overPullbackLeftIso_inv_snd, reassoc_of% X.isCartesian.isoPullback_hom_snd]
      exact X.left.source.w)

/-- The target comparison sends an arrow to its target. -/
theorem cartesianOverTargetComparison_hom_fst {S : Scheme.{u}}
    {G : GroupoidScheme S} (X : CartesianOver G) :
    (cartesianOverTargetComparison X).hom ≫ pullback.fst X.hom.mapObjects G.target =
      X.left.target := by
  apply Over.OverMorphism.ext
  let h := cartesianOver_target_pullback X
  change (h.flip.isoPullback.hom ≫
    (overPullbackLeftIso X.hom.mapObjects G.target).inv ≫
      (pullback.fst X.hom.mapObjects G.target).left) = X.left.target.left
  rw [overPullbackLeftIso_inv_fst, h.flip.isoPullback_hom_fst]

/-- The target comparison sends an arrow to its image in `G`. -/
theorem cartesianOverTargetComparison_hom_snd {S : Scheme.{u}}
    {G : GroupoidScheme S} (X : CartesianOver G) :
    (cartesianOverTargetComparison X).hom ≫ pullback.snd X.hom.mapObjects G.target =
      X.hom.mapArrows := by
  apply Over.OverMorphism.ext
  let h := cartesianOver_target_pullback X
  change (h.flip.isoPullback.hom ≫
    (overPullbackLeftIso X.hom.mapObjects G.target).inv ≫
      (pullback.snd X.hom.mapObjects G.target).left) = X.hom.mapArrows.left
  rw [overPullbackLeftIso_inv_snd, h.flip.isoPullback_hom_snd]

/-- The source comparison sends an arrow to its image in `G`. -/
theorem cartesianOverSourceComparison_hom_fst {S : Scheme.{u}}
    {G : GroupoidScheme S} (X : CartesianOver G) :
    (cartesianOverSourceComparison X).hom ≫ pullback.fst G.source X.hom.mapObjects =
      X.hom.mapArrows := by
  apply Over.OverMorphism.ext
  change (X.isCartesian.isoPullback.hom ≫
    (overPullbackLeftIso G.source X.hom.mapObjects).inv ≫
      (pullback.fst G.source X.hom.mapObjects).left) = X.hom.mapArrows.left
  rw [overPullbackLeftIso_inv_fst, X.isCartesian.isoPullback_hom_fst]

/-- The source comparison sends an arrow to its source. -/
theorem cartesianOverSourceComparison_hom_snd {S : Scheme.{u}}
    {G : GroupoidScheme S} (X : CartesianOver G) :
    (cartesianOverSourceComparison X).hom ≫ pullback.snd G.source X.hom.mapObjects =
      X.left.source := by
  apply Over.OverMorphism.ext
  change (X.isCartesian.isoPullback.hom ≫
    (overPullbackLeftIso G.source X.hom.mapObjects).inv ≫
      (pullback.snd G.source X.hom.mapObjects).left) = X.left.source.left
  rw [overPullbackLeftIso_inv_snd, X.isCartesian.isoPullback_hom_snd]

/-- The arrow of a cartesian groupoid scheme determined by an object upstairs and an arrow of `G`
with matching target. -/
noncomputable def cartesianOverLiftArrow {S : Scheme.{u}}
    {G : GroupoidScheme S} (X : CartesianOver G) {T : Over S}
    (v : T ⟶ X.left.objects) (f : T ⟶ G.arrows)
    (w : v ≫ X.hom.mapObjects = f ≫ G.target) : T ⟶ X.left.arrows :=
  pullback.lift v f w ≫ (cartesianOverTargetComparison X).inv

/-- The lifted arrow has the prescribed target. -/
theorem cartesianOverLiftArrow_target {S : Scheme.{u}}
    {G : GroupoidScheme S} (X : CartesianOver G) {T : Over S}
    (v : T ⟶ X.left.objects) (f : T ⟶ G.arrows)
    (w : v ≫ X.hom.mapObjects = f ≫ G.target) :
    cartesianOverLiftArrow X v f w ≫ X.left.target = v := by
  change (pullback.lift v f w ≫ (cartesianOverTargetComparison X).inv) ≫
      X.left.target = v
  rw [← cartesianOverTargetComparison_hom_fst]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact pullback.lift_fst v f w

/-- The lifted arrow has the prescribed image in `G`. -/
theorem cartesianOverLiftArrow_mapArrows {S : Scheme.{u}}
    {G : GroupoidScheme S} (X : CartesianOver G) {T : Over S}
    (v : T ⟶ X.left.objects) (f : T ⟶ G.arrows)
    (w : v ≫ X.hom.mapObjects = f ≫ G.target) :
    cartesianOverLiftArrow X v f w ≫ X.hom.mapArrows = f := by
  change (pullback.lift v f w ≫ (cartesianOverTargetComparison X).inv) ≫
      X.hom.mapArrows = f
  rw [← cartesianOverTargetComparison_hom_snd]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact pullback.lift_snd v f w

/-- An arrow of a cartesian groupoid scheme is determined by its target and its image in `G`. -/
theorem cartesianOverLiftArrow_ext {S : Scheme.{u}}
    {G : GroupoidScheme S} (X : CartesianOver G) {T : Over S}
    (f g : T ⟶ X.left.arrows)
    (ht : f ≫ X.left.target = g ≫ X.left.target)
    (hb : f ≫ X.hom.mapArrows = g ≫ X.hom.mapArrows) : f = g := by
  apply (cancel_mono (cartesianOverTargetComparison X).hom).1
  apply pullback.hom_ext
  · simpa only [Category.assoc, cartesianOverTargetComparison_hom_fst] using ht
  · simpa only [Category.assoc, cartesianOverTargetComparison_hom_snd] using hb

/-- The source of the lifted arrow lies over the source of the arrow of `G` it was lifted from. -/
private theorem cartesianOverLiftArrow_source_obj {S : Scheme.{u}}
    {G : GroupoidScheme S} (X : CartesianOver G) {T : Over S}
    (v : T ⟶ X.left.objects) (f : T ⟶ G.arrows)
    (w : v ≫ X.hom.mapObjects = f ≫ G.target) :
    cartesianOverLiftArrow X v f w ≫ X.left.source ≫ X.hom.mapObjects =
      f ≫ G.source := by
  rw [← X.hom.map_source, ← Category.assoc, cartesianOverLiftArrow_mapArrows]

/-- The descent isomorphism of a cartesian groupoid scheme: it sends `(v, f)` with `f` of target
the image of `v` to `(f, f · v)`. -/
noncomputable def cartesianOverDescentIso {S : Scheme.{u}}
    {G : GroupoidScheme S} (X : CartesianOver G) :
    pullback X.hom.mapObjects G.target ≅ pullback G.source X.hom.mapObjects :=
  (cartesianOverTargetComparison X).symm ≪≫ cartesianOverSourceComparison X

/-- The descent isomorphism computes the source of the lifted arrow, which is the action of the
arrow of `G` on the object upstairs. -/
theorem cartesianOverDescentIso_action {S : Scheme.{u}}
    {G : GroupoidScheme S} (X : CartesianOver G) {T : Over S}
    (v : T ⟶ X.left.objects) (f : T ⟶ G.arrows)
    (w : v ≫ X.hom.mapObjects = f ≫ G.target) :
    pullback.lift v f w ≫ (cartesianOverDescentIso X).hom ≫
        pullback.snd G.source X.hom.mapObjects =
      cartesianOverLiftArrow X v f w ≫ X.left.source := by
  simp only [cartesianOverDescentIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, cartesianOverSourceComparison_hom_snd]
  rfl

namespace GroupoidScheme.Hom

/-- The identity morphism of a groupoid scheme. -/
def id {S : Scheme.{u}} (G : GroupoidScheme S) : GroupoidScheme.Hom G G where
  mapObjects := 𝟙 G.objects
  mapArrows := 𝟙 G.arrows
  map_source := by simp
  map_target := by simp
  map_identity := by simp
  map_comp := by simp [GroupoidScheme.compose]

/-- Composition of morphisms of groupoid schemes. -/
def comp {S : Scheme.{u}} {G H K : GroupoidScheme S}
    (F : GroupoidScheme.Hom G H) (E : GroupoidScheme.Hom H K) :
    GroupoidScheme.Hom G K where
  mapObjects := F.mapObjects ≫ E.mapObjects
  mapArrows := F.mapArrows ≫ E.mapArrows
  map_source := by
    rw [Category.assoc, E.map_source, ← Category.assoc, F.map_source,
      Category.assoc]
  map_target := by
    rw [Category.assoc, E.map_target, ← Category.assoc, F.map_target,
      Category.assoc]
  map_identity := by
    rw [Category.assoc, E.map_identity, ← Category.assoc, F.map_identity,
      Category.assoc]
  map_comp := by
    intro T f g w w'
    have wh : (f ≫ F.mapArrows) ≫ H.source =
        (g ≫ F.mapArrows) ≫ H.target := by
      simp only [Category.assoc, F.map_source, F.map_target, reassoc_of% w]
    rw [← Category.assoc, F.map_comp T f g w wh]
    simpa only [Category.assoc] using
      E.map_comp T (f ≫ F.mapArrows) (g ≫ F.mapArrows) wh w'

end GroupoidScheme.Hom

namespace CartesianOver

/-- Two morphisms of groupoid schemes are equal when their object and arrow
maps are equal. -/
@[ext]
theorem groupoidHom_ext {S : Scheme.{u}} {G H : GroupoidScheme S}
    (F E : GroupoidScheme.Hom G H) (h₀ : F.mapObjects = E.mapObjects)
    (h₁ : F.mapArrows = E.mapArrows) : F = E := by
  cases F
  cases E
  cases h₀
  cases h₁
  rfl

/-- Two morphisms of cartesian groupoid schemes are equal when their
underlying groupoid morphisms are equal. -/
@[ext]
theorem hom_ext {S : Scheme.{u}} {G : GroupoidScheme S}
    {X Y : CartesianOver G} (f g : CartesianOver.Hom X Y)
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Cartesian groupoid schemes over `G` form a category. -/
instance {S : Scheme.{u}} {G : GroupoidScheme S} : Category (CartesianOver G) where
  Hom := CartesianOver.Hom
  id X :=
    { hom := GroupoidScheme.Hom.id X.left
      mapObjects_comp := by simp [GroupoidScheme.Hom.id]
      mapArrows_comp := by simp [GroupoidScheme.Hom.id] }
  comp f g :=
    { hom := GroupoidScheme.Hom.comp f.hom g.hom
      mapObjects_comp := by
        simp only [GroupoidScheme.Hom.comp]
        rw [Category.assoc, g.mapObjects_comp, f.mapObjects_comp]
      mapArrows_comp := by
        simp only [GroupoidScheme.Hom.comp]
        rw [Category.assoc, g.mapArrows_comp, f.mapArrows_comp] }
  id_comp f := by
    apply hom_ext
    apply groupoidHom_ext <;> simp [GroupoidScheme.Hom.id,
      GroupoidScheme.Hom.comp]
  comp_id f := by
    apply hom_ext
    apply groupoidHom_ext <;> simp [GroupoidScheme.Hom.id,
      GroupoidScheme.Hom.comp]
  assoc f g h := by
    apply hom_ext
    apply groupoidHom_ext <;> simp [GroupoidScheme.Hom.comp]

end CartesianOver

/-- A scheme over the object scheme of `G`, equipped with a normalized
cocyclic isomorphism between its pullbacks along target and source. -/
structure EquivariantScheme {S : Scheme.{u}} (G : GroupoidScheme S) where
  /-- The scheme over the object scheme. -/
  obj : Over G.objects
  /-- The isomorphism `V ×_{U,t} R ≅ R ×_{s,U} V`. -/
  descentIso : pullback obj.hom G.target ≅ pullback G.source obj.hom
  /-- The isomorphism is over the arrow scheme. -/
  descentIso_over : descentIso.hom ≫ pullback.fst G.source obj.hom =
    pullback.snd obj.hom G.target
  /-- Pullback along the identity is the identity of `V`. -/
  identity : ∀ (T : Over S) (v : T ⟶ obj.left),
    pullback.lift v (v ≫ obj.hom ≫ G.identity) (by
      simpa only [Category.assoc, Category.comp_id] using
        congrArg (fun k ↦ v ≫ obj.hom ≫ k) G.target_identity.symm) ≫
        descentIso.hom ≫ pullback.snd G.source obj.hom = v
  /-- Pullback along composition is the composite of the two pullbacks. -/
  cocycle : ∀ (T : Over S) (v : T ⟶ obj.left) (f g : T ⟶ G.arrows)
      (wvf : v ≫ obj.hom = f ≫ G.target) (wfg : f ≫ G.source = g ≫ G.target),
    pullback.lift
          (pullback.lift v f wvf ≫ descentIso.hom ≫ pullback.snd G.source obj.hom)
          g (by
            calc
              (pullback.lift v f wvf ≫ descentIso.hom ≫
                    pullback.snd G.source obj.hom) ≫ obj.hom =
                  pullback.lift v f wvf ≫ descentIso.hom ≫
                    pullback.fst G.source obj.hom ≫ G.source := by
                      simpa only [Category.assoc] using congrArg
                        (fun k ↦ pullback.lift v f wvf ≫ descentIso.hom ≫ k)
                        (pullback.condition (f := G.source) (g := obj.hom)).symm
              _ = pullback.lift v f wvf ≫ pullback.snd obj.hom G.target ≫
                    G.source := by
                      simpa only [Category.assoc] using congrArg
                        (fun k ↦ pullback.lift v f wvf ≫ k ≫ G.source)
                        descentIso_over
              _ = f ≫ G.source := by
                rw [← Category.assoc, pullback.lift_snd]
              _ = g ≫ G.target := wfg) ≫
        descentIso.hom ≫ pullback.snd G.source obj.hom =
      pullback.lift v (G.compose f g wfg) (by
        simp only [GroupoidScheme.compose, Category.assoc, G.target_comp]
        rw [← Category.assoc, pullback.lift_fst, wvf]) ≫
        descentIso.hom ≫ pullback.snd G.source obj.hom

namespace EquivariantScheme

/-- The action of an equivariant scheme on a generalized arrow. -/
noncomputable def action {S : Scheme.{u}} {G : GroupoidScheme S} (V : EquivariantScheme G)
    {T : Over S} (v : T ⟶ V.obj.left) (f : T ⟶ G.arrows)
    (w : v ≫ V.obj.hom = f ≫ G.target) : T ⟶ V.obj.left :=
  pullback.lift v f w ≫ V.descentIso.hom ≫ pullback.snd G.source V.obj.hom

/-- An equivariant morphism is a map over the object scheme commuting with the
action of every generalized arrow. -/
@[ext]
structure Hom {S : Scheme.{u}} {G : GroupoidScheme S}
    (V W : EquivariantScheme G) where
  /-- The underlying map over the object scheme. -/
  hom : Over.Hom V.obj W.obj
  /-- Compatibility with the pullback isomorphisms. -/
  comm : ∀ (T : Over S) (v : T ⟶ V.obj.left) (f : T ⟶ G.arrows)
      (w : v ≫ V.obj.hom = f ≫ G.target),
    V.action v f w ≫ hom.left = W.action (v ≫ hom.left) f (by simpa using w)

/-- Two equivariant morphisms are equal when their underlying maps are equal. -/
theorem hom_ext {S : Scheme.{u}} {G : GroupoidScheme S}
    {V W : EquivariantScheme G} (f g : Hom V W) (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The identity equivariant morphism. -/
def Hom.id {S : Scheme.{u}} {G : GroupoidScheme S} (V : EquivariantScheme G) : Hom V V where
  hom := Over.homMk (𝟙 V.obj.left)
  comm := by simp

/-- Composition of equivariant morphisms. -/
def Hom.comp {S : Scheme.{u}} {G : GroupoidScheme S} {V W Z : EquivariantScheme G}
    (f : Hom V W) (g : Hom W Z) : Hom V Z where
  hom := Over.homMk (f.hom.left ≫ g.hom.left) (by
    rw [Category.assoc, g.hom.w, f.hom.w])
  comm := by
    intro T v a w
    change V.action v a w ≫ (f.hom.left ≫ g.hom.left) =
      Z.action (v ≫ (f.hom.left ≫ g.hom.left)) a _
    rw [← Category.assoc, f.comm]
    simpa only [Category.assoc] using g.comm T (v ≫ f.hom.left) a (by
      rw [Category.assoc, f.hom.w, w])

/-- The identity and composition of equivariant morphisms, as a `CategoryStruct`. -/
noncomputable instance {S : Scheme.{u}} {G : GroupoidScheme S} :
    CategoryStruct (EquivariantScheme G) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

/-- Equivariant schemes for `G` form a category. -/
noncomputable instance {S : Scheme.{u}} {G : GroupoidScheme S} :
    Category (EquivariantScheme G) where
  id_comp f := by
    apply hom_ext
    change (Hom.comp (Hom.id _) f).hom = f.hom
    apply Comma.hom_ext
    · exact Category.id_comp _
    · rfl
  comp_id f := by
    apply hom_ext
    change (Hom.comp f (Hom.id _)).hom = f.hom
    apply Comma.hom_ext
    · exact Category.comp_id _
    · rfl
  assoc f g h := by
    apply hom_ext
    change (Hom.comp (Hom.comp f g) h).hom = (Hom.comp f (Hom.comp g h)).hom
    apply Comma.hom_ext
    · exact Category.assoc _ _ _
    · rfl

/-- The action commutes with change of test object: acting after restricting along `k` is
restricting the action along `k`.  The composability witness appears in the type of an action,
so it is supplied again for the restricted pair. -/
theorem comp_action {S : Scheme.{u}} {G : GroupoidScheme S} (V : EquivariantScheme G)
    {T U : Over S} (k : U ⟶ T) (v : T ⟶ V.obj.left) (a : T ⟶ G.arrows)
    (w : v ≫ V.obj.hom = a ≫ G.target)
    (w' : (k ≫ v) ≫ V.obj.hom = (k ≫ a) ≫ G.target) :
    k ≫ V.action v a w = V.action (k ≫ v) (k ≫ a) w' := by
  have h : k ≫ pullback.lift v a w = pullback.lift (k ≫ v) (k ≫ a) w' := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
  simp only [EquivariantScheme.action]
  conv_lhs => rw [← Category.assoc, h]

end EquivariantScheme

/-- The action of an arrow on an object upstairs lies over the source of that arrow. -/
theorem EquivariantScheme.action_comp_hom {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) {T : Over S} (v : T ⟶ V.obj.left)
    (f : T ⟶ G.arrows) (w : v ≫ V.obj.hom = f ≫ G.target) :
    V.action v f w ≫ V.obj.hom = f ≫ G.source := by
  unfold EquivariantScheme.action
  rw [Category.assoc, Category.assoc, ← pullback.condition, reassoc_of% V.descentIso_over,
    pullback.lift_snd_assoc]

/-- An identity arrow acts trivially. -/
theorem equivariant_action_identity {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) {T : Over S} (v : T ⟶ V.obj.left) :
    V.action v (v ≫ V.obj.hom ≫ G.identity) (by
      simpa only [Category.assoc, Category.comp_id] using
        congrArg (fun k ↦ v ≫ V.obj.hom ≫ k) G.target_identity.symm) = v :=
  V.identity T v

/-- Acting by two composable arrows in succession is acting by their composite. -/
theorem equivariant_action_cocycle {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) {T : Over S} (v : T ⟶ V.obj.left)
    (f g : T ⟶ G.arrows) (wvf : v ≫ V.obj.hom = f ≫ G.target)
    (wfg : f ≫ G.source = g ≫ G.target) :
    V.action (V.action v f wvf) g (by
      calc
        V.action v f wvf ≫ V.obj.hom = f ≫ G.source :=
          V.action_comp_hom v f wvf
        _ = g ≫ G.target := wfg) =
      V.action v (G.compose f g wfg) (by
        simp only [GroupoidScheme.compose, Category.assoc, G.target_comp]
        rw [← Category.assoc, pullback.lift_fst, wvf]) :=
  V.cocycle T v f g wvf wfg

/-- The action is unchanged when the acting arrow is replaced by an equal one.  The
composability witness appears in the type of an action, so this congruence rule is what
replaces a rewrite. -/
theorem EquivariantScheme.action_arrow_eq {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) {T : Over S} (v : T ⟶ V.obj.left)
    (f g : T ⟶ G.arrows) (wf : v ≫ V.obj.hom = f ≫ G.target)
    (wg : v ≫ V.obj.hom = g ≫ G.target) (h : f = g) :
    V.action v f wf = V.action v g wg := by
  subst g
  congr 2

/-- The action is unchanged when the object acted on is replaced by an equal one.  The
composability witness appears in the type of an action, so this congruence rule is what
replaces a rewrite. -/
theorem EquivariantScheme.action_point_eq {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) {T : Over S} {v w : T ⟶ V.obj.left}
    (f : T ⟶ G.arrows) (hv : v ≫ V.obj.hom = f ≫ G.target)
    (hw : w ≫ V.obj.hom = f ≫ G.target) (h : v = w) :
    V.action v f hv = V.action w f hw := by
  subst w
  congr 2

/-- Acting by an arrow and then by its inverse is trivial. -/
theorem equivariant_action_inverse {S : Scheme.{u}} {G : GroupoidScheme S}
    (V : EquivariantScheme G) {T : Over S} (v : T ⟶ V.obj.left)
    (f : T ⟶ G.arrows) (wf : v ≫ V.obj.hom = f ≫ G.target) :
    V.action (V.action v f wf) (f ≫ G.inverse) (by
      rw [V.action_comp_hom v f wf, Category.assoc, G.target_inverse]) = v := by
  let wfg : f ≫ G.source = (f ≫ G.inverse) ≫ G.target := by
    rw [Category.assoc, G.target_inverse]
  have hcomp : G.compose f (f ≫ G.inverse) wfg = f ≫ G.target ≫ G.identity := by
    simpa [GroupoidScheme.compose] using G.right_inverse T f wfg
  have wid : v ≫ V.obj.hom = f ≫ G.target ≫ G.identity ≫ G.target := by
    simpa [Category.assoc, G.target_identity] using wf
  have wcomp : v ≫ V.obj.hom =
      G.compose f (f ≫ G.inverse) wfg ≫ G.target :=
    wf.trans (groupoidCompose_target G f _ wfg).symm
  have wvId : v ≫ V.obj.hom =
      (v ≫ V.obj.hom ≫ G.identity) ≫ G.target := by
    simp [G.target_identity]
  calc
    V.action (V.action v f wf) (f ≫ G.inverse) _ =
        V.action v (G.compose f (f ≫ G.inverse) wfg) _ :=
          equivariant_action_cocycle V v f (f ≫ G.inverse) wf wfg
    _ = V.action v (f ≫ G.target ≫ G.identity) _ :=
          V.action_arrow_eq v _ _ wcomp wid hcomp
    _ = V.action v (v ≫ V.obj.hom ≫ G.identity) _ :=
          V.action_arrow_eq v _ _ wid wvId (by simp only [← Category.assoc, wf])
    _ = v := equivariant_action_identity V v

/-- The equivariant scheme attached to a groupoid scheme cartesian over `G`: its object scheme is
the object scheme upstairs and its descent isomorphism is the comparison of the two cartesian
squares. -/
@[implicit_reducible] noncomputable def cartesianOverToEquivariant {S : Scheme.{u}}
    {G : GroupoidScheme S} (X : CartesianOver G) : EquivariantScheme G where
  obj := Over.mk X.hom.mapObjects
  descentIso := cartesianOverDescentIso X
  descentIso_over := by
    apply Over.OverMorphism.ext
    have hs : (cartesianOverSourceComparison X).hom.left ≫
        (pullback.fst G.source X.hom.mapObjects).left = X.hom.mapArrows.left := by
      simpa only [Over.comp_left] using
        congrArg Over.Hom.left (cartesianOverSourceComparison_hom_fst X)
    have ht : (cartesianOverTargetComparison X).hom.left ≫
        (pullback.snd X.hom.mapObjects G.target).left = X.hom.mapArrows.left := by
      simpa only [Over.comp_left] using
        congrArg Over.Hom.left (cartesianOverTargetComparison_hom_snd X)
    have hi : (cartesianOverTargetComparison X).inv.left ≫
        (cartesianOverTargetComparison X).hom.left = 𝟙 _ := by
      simpa only [Over.comp_left, Over.id_left] using
        congrArg Over.Hom.left (cartesianOverTargetComparison X).inv_hom_id
    change (cartesianOverTargetComparison X).inv.left ≫
        ((cartesianOverSourceComparison X).hom.left ≫
          (pullback.fst G.source X.hom.mapObjects).left) =
      (pullback.snd X.hom.mapObjects G.target).left
    rw [hs, ← ht, ← Category.assoc, hi, Category.id_comp]
  identity := by
    intro T v
    let f := v ≫ X.hom.mapObjects ≫ G.identity
    have wf : v ≫ X.hom.mapObjects = f ≫ G.target := by
      simp [f, G.target_identity]
    let a := cartesianOverLiftArrow X v f wf
    have ha : a = v ≫ X.left.identity := by
      apply cartesianOverLiftArrow_ext X a (v ≫ X.left.identity)
      · exact (cartesianOverLiftArrow_target X v f wf).trans (by simp [X.left.target_identity])
      · exact (cartesianOverLiftArrow_mapArrows X v f wf).trans (by simp [f, X.hom.map_identity])
    change pullback.lift v f wf ≫ (cartesianOverDescentIso X).hom ≫
      pullback.snd G.source X.hom.mapObjects = v
    calc
      _ = a ≫ X.left.source := cartesianOverDescentIso_action X v f wf
      _ = (v ≫ X.left.identity) ≫ X.left.source := congrArg
            (fun k => k ≫ X.left.source) ha
      _ = v := by simp [Category.assoc, X.left.source_identity]
  cocycle := by
    intro T v f g wvf wfg
    let a := cartesianOverLiftArrow X v f wvf
    let x := a ≫ X.left.source
    have wxg : x ≫ X.hom.mapObjects = g ≫ G.target :=
      (cartesianOverLiftArrow_source_obj X v f wvf).trans wfg
    let b := cartesianOverLiftArrow X x g wxg
    let wX : a ≫ X.left.source = b ≫ X.left.target :=
      (cartesianOverLiftArrow_target X x g wxg).symm
    let c := GroupoidScheme.compose X.left a b wX
    have wG : (a ≫ X.hom.mapArrows) ≫ G.source =
        (b ≫ X.hom.mapArrows) ≫ G.target := by
      simp only [Category.assoc, X.hom.map_source, X.hom.map_target, reassoc_of% wX]
    have hcbase : c ≫ X.hom.mapArrows =
        G.compose (a ≫ X.hom.mapArrows) (b ≫ X.hom.mapArrows) wG :=
      X.hom.map_comp T a b wX wG
    have hcTarget : c ≫ X.left.target = v := by
      dsimp [c, GroupoidScheme.compose]
      rw [Category.assoc, X.left.target_comp, ← Category.assoc, pullback.lift_fst]
      exact cartesianOverLiftArrow_target X v f wvf
    have hcSource : c ≫ X.left.source = b ≫ X.left.source := by
      dsimp [c, GroupoidScheme.compose]
      rw [Category.assoc, X.left.source_comp, ← Category.assoc, pullback.lift_snd]
    have hcomposeTarget : G.compose f g wfg ≫ G.target = f ≫ G.target := by
      dsimp [GroupoidScheme.compose]
      rw [Category.assoc, G.target_comp, ← Category.assoc, pullback.lift_fst]
    have hcompTarget : v ≫ X.hom.mapObjects = G.compose f g wfg ≫ G.target :=
      wvf.trans hcomposeTarget.symm
    have hcbase' : c ≫ X.hom.mapArrows = G.compose f g wfg :=
      hcbase.trans (groupoidCompose_arrow_eq
        (a ≫ X.hom.mapArrows) f (b ≫ X.hom.mapArrows) g wG wfg
        (cartesianOverLiftArrow_mapArrows X v f wvf)
        (cartesianOverLiftArrow_mapArrows X x g wxg))
    have heq : c = cartesianOverLiftArrow X v (G.compose f g wfg) hcompTarget := by
      apply cartesianOverLiftArrow_ext X c
      · rw [hcTarget, cartesianOverLiftArrow_target]
      · rw [hcbase', cartesianOverLiftArrow_mapArrows]
    let u := pullback.lift v f wvf ≫ (cartesianOverDescentIso X).hom ≫
      pullback.snd G.source X.hom.mapObjects
    have hu : u = x := by
      simpa [u] using cartesianOverDescentIso_action X v f wvf
    have wouter : u ≫ X.hom.mapObjects = g ≫ G.target := by
      rw [hu]
      exact wxg
    have houter : pullback.lift u g wouter = pullback.lift x g wxg := by
      apply pullback.hom_ext
      · simpa only [pullback.lift_fst] using hu
      · simp only [pullback.lift_snd]
    change pullback.lift u g wouter ≫ (cartesianOverDescentIso X).hom ≫
        pullback.snd G.source X.hom.mapObjects =
      pullback.lift v (G.compose f g wfg) hcompTarget ≫
        (cartesianOverDescentIso X).hom ≫
          pullback.snd G.source X.hom.mapObjects
    rw [houter, cartesianOverDescentIso_action, cartesianOverDescentIso_action, ← heq]
    exact hcSource.symm


end AlgebraicGeometry

end
