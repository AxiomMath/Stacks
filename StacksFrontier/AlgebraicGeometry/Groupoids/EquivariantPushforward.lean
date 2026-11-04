module

public import StacksFrontier.AlgebraicGeometry.Groupoids.GroupoidPushforward
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Equivariant

/-!
# Equivariant schemes for a pushed-forward groupoid

Let `g : Y ⟶ S` be a morphism of schemes and let `G` be a groupoid scheme over `Y`.  An
equivariant scheme for `G` is the same thing as an equivariant scheme for the groupoid scheme
`G.pushforward g` over `S`: the data on either side is a scheme over the object scheme of `G`
together with a normalized cocyclic isomorphism of its two pullbacks along source and target,
and neither the data nor the conditions refer to the base scheme.  This file proves that.

## Main definitions

* `AlgebraicGeometry.EquivariantScheme.homMk` and `AlgebraicGeometry.EquivariantScheme.isoMk`
  build an equivariant morphism, respectively an isomorphism, out of a morphism of the
  underlying objects which is compatible with the two actions.
* `AlgebraicGeometry.EquivariantScheme.pushforwardEquivariantFunctor` is the comparison
  functor, built from `AlgebraicGeometry.EquivariantScheme.pushforwardDescentIso` and the
  action `AlgebraicGeometry.EquivariantScheme.pushforwardAct`.
* `AlgebraicGeometry.EquivariantScheme.descendEquivariant` is the equivariant scheme for `G`
  attached to one for `G.pushforward g`, whose image under the comparison functor is isomorphic
  to the one it came from.

## Main results

* `AlgebraicGeometry.EquivariantScheme.pushforwardEquivariantEquivalence`: **equivariant
  schemes for `G` are the same thing as equivariant schemes for `G.pushforward g`.**
* `AlgebraicGeometry.cartesianOverPushforwardEquivalence`: **groupoid schemes cartesian over
  `G` are the same thing as groupoid schemes cartesian over `G.pushforward g`.**

## Implementation notes

Only one of the two functors is constructed: the comparison is shown to be full, faithful and
essentially surjective, so the inverse is not needed on morphisms.  Essential surjectivity is
where the work is, because an equivariant scheme `W` for `G.pushforward g` has an object scheme
`W.obj.left` in `Over S` which is only *isomorphic*, not equal, to the image of the object
scheme in `Over Y` that it determines, namely `Over.mk (W.obj.hom.left ≫ G.objects.hom)`.  The
descent isomorphism of `W` is therefore transported along that comparison, by
`Stacks.Groupoids.pullbackLeftLegIso` and `Stacks.Groupoids.pullbackRightLegIso`, before it is
descended.

Every statement about a generalized point of `Over S` is phrased through
`Stacks.Groupoids.overAscend`, never through `CategoryTheory.Over.map`, because the test object
is in general not the image of one from `Over Y` but only a scheme over `S` whose structure
morphism factors through `g`.  The two agree on the images, by
`Stacks.Groupoids.overAscend_self`.

## References

* [Stacks Project, Tag 0APD](https://stacks.math.columbia.edu/tag/0APD)
* [Stacks Project, Tag 0APE](https://stacks.math.columbia.edu/tag/0APE)
* [Stacks Project, Tag 0APF](https://stacks.math.columbia.edu/tag/0APF)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

namespace EquivariantScheme

section IsoMk

variable {S : Scheme.{u}} {H : GroupoidScheme S} {V W : EquivariantScheme H}

/-- An equivariant morphism out of a morphism of the underlying objects which is compatible
with the two actions. -/
def homMk (k : V.obj ⟶ W.obj)
    (h : ∀ {T : Over S} (v : T ⟶ V.obj.left) (a : T ⟶ H.arrows)
      (w : v ≫ V.obj.hom = a ≫ H.target)
      (w' : (v ≫ k.left) ≫ W.obj.hom = a ≫ H.target),
      V.action v a w ≫ k.left = W.action (v ≫ k.left) a w') : V ⟶ W where
  hom := k
  comm := fun _ v a w => h v a w _

/-- The underlying morphism of `AlgebraicGeometry.EquivariantScheme.homMk k h` is `k`. -/
@[simp]
lemma homMk_hom (k : V.obj ⟶ W.obj)
    (h : ∀ {T : Over S} (v : T ⟶ V.obj.left) (a : T ⟶ H.arrows)
      (w : v ≫ V.obj.hom = a ≫ H.target)
      (w' : (v ≫ k.left) ≫ W.obj.hom = a ≫ H.target),
      V.action v a w ≫ k.left = W.action (v ≫ k.left) a w') :
    (homMk k h).hom = k := rfl

/-- An isomorphism of equivariant schemes out of an isomorphism of the underlying objects which
is compatible with the two actions. -/
def isoMk (i : V.obj ≅ W.obj)
    (h : ∀ {T : Over S} (v : T ⟶ V.obj.left) (a : T ⟶ H.arrows)
      (w : v ≫ V.obj.hom = a ≫ H.target)
      (w' : (v ≫ i.hom.left) ≫ W.obj.hom = a ≫ H.target),
      V.action v a w ≫ i.hom.left = W.action (v ≫ i.hom.left) a w') : V ≅ W where
  hom := homMk i.hom h
  inv := homMk i.inv (by
    intro T u a w w'
    have hhi : i.hom.left ≫ i.inv.left = 𝟙 V.obj.left := by
      rw [← Over.comp_left, i.hom_inv_id, Over.id_left]
    have hih : i.inv.left ≫ i.hom.left = 𝟙 W.obj.left := by
      rw [← Over.comp_left, i.inv_hom_id, Over.id_left]
    have hu : (u ≫ i.inv.left) ≫ i.hom.left = u := by
      rw [Category.assoc, hih, Category.comp_id]
    have key := h (u ≫ i.inv.left) a w' (by rwa [hu])
    rw [W.action_point_eq a _ w hu] at key
    rw [← key, Category.assoc, hhi, Category.comp_id])
  hom_inv_id := by
    refine EquivariantScheme.hom_ext _ _ ?_
    exact Over.OverMorphism.ext (congrArg Over.Hom.left i.hom_inv_id)
  inv_hom_id := by
    refine EquivariantScheme.hom_ext _ _ ?_
    exact Over.OverMorphism.ext (congrArg Over.Hom.left i.inv_hom_id)

/-- The underlying morphism of the forward map of `AlgebraicGeometry.EquivariantScheme.isoMk i h`
is `i.hom`. -/
@[simp]
lemma isoMk_hom_hom (i : V.obj ≅ W.obj)
    (h : ∀ {T : Over S} (v : T ⟶ V.obj.left) (a : T ⟶ H.arrows)
      (w : v ≫ V.obj.hom = a ≫ H.target)
      (w' : (v ≫ i.hom.left) ≫ W.obj.hom = a ≫ H.target),
      V.action v a w ≫ i.hom.left = W.action (v ≫ i.hom.left) a w') :
    (isoMk i h).hom.hom = i.hom := rfl

end IsoMk

section Pushforward

variable {Y S : Scheme.{u}} (g : Y ⟶ S) {G : GroupoidScheme Y}

/-- The descent isomorphism of the pushforward of an equivariant scheme: the descent
isomorphism of `V`, transported across the two comparison isomorphisms for a pullback. -/
def pushforwardDescentIso (V : EquivariantScheme G) :
    pullback ((Over.map g).map V.obj.hom) ((Over.map g).map G.target) ≅
      pullback ((Over.map g).map G.source) ((Over.map g).map V.obj.hom) :=
  (PreservesPullback.iso (Over.map g) V.obj.hom G.target).symm ≪≫
    (Over.map g).mapIso V.descentIso ≪≫
      PreservesPullback.iso (Over.map g) G.source V.obj.hom

/-- The action of the pushforward of an equivariant scheme on generalized points. -/
def pushforwardAct (V : EquivariantScheme G) {A : Over S}
    (v : A ⟶ (Over.map g).obj V.obj.left) (a : A ⟶ (Over.map g).obj G.arrows)
    (w : v ≫ (Over.map g).map V.obj.hom = a ≫ (Over.map g).map G.target) :
    A ⟶ (Over.map g).obj V.obj.left :=
  pullback.lift v a w ≫ (pushforwardDescentIso g V).hom ≫
    pullback.snd ((Over.map g).map G.source) ((Over.map g).map V.obj.hom)

/-- The action of the pushforward, by its definition. -/
lemma pushforwardAct_def (V : EquivariantScheme G) {A : Over S}
    (v : A ⟶ (Over.map g).obj V.obj.left) (a : A ⟶ (Over.map g).obj G.arrows)
    (w : v ≫ (Over.map g).map V.obj.hom = a ≫ (Over.map g).map G.target) :
    pushforwardAct g V v a w = pullback.lift v a w ≫ (pushforwardDescentIso g V).hom ≫
      pullback.snd ((Over.map g).map G.source) ((Over.map g).map V.obj.hom) := rfl

/-- The second projection of the pushed-forward descent isomorphism. -/
lemma pushforwardDescentIso_hom_comp_snd (V : EquivariantScheme G) :
    (pushforwardDescentIso g V).hom ≫
        pullback.snd ((Over.map g).map G.source) ((Over.map g).map V.obj.hom) =
      (PreservesPullback.iso (Over.map g) V.obj.hom G.target).inv ≫
        (Over.map g).map (V.descentIso.hom ≫ pullback.snd G.source V.obj.hom) := by
  simp only [pushforwardDescentIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc, PreservesPullback.iso_hom_snd]

/-- The pushed-forward descent isomorphism lies over the arrow scheme. -/
lemma pushforwardDescentIso_over (V : EquivariantScheme G) :
    (pushforwardDescentIso g V).hom ≫
        pullback.fst ((Over.map g).map G.source) ((Over.map g).map V.obj.hom) =
      pullback.snd ((Over.map g).map V.obj.hom) ((Over.map g).map G.target) := by
  rw [pushforwardDescentIso, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Category.assoc, PreservesPullback.iso_hom_fst, ← Functor.map_comp,
    V.descentIso_over, PreservesPullback.iso_inv_snd]

/-- **The action of the pushforward is the action of `V`.**  A generalized point of the
pushforward whose test object is re-based over `Y` acts as it does in `V`. -/
lemma pushforwardAct_eq (V : EquivariantScheme G) {A : Over S} {base : A.left ⟶ Y}
    (hb : base ≫ g = A.hom)
    (v : A ⟶ (Over.map g).obj V.obj.left) (a : A ⟶ (Over.map g).obj G.arrows)
    (v' : (Over.mk base : Over Y) ⟶ V.obj.left) (a' : (Over.mk base : Over Y) ⟶ G.arrows)
    (hv : v'.left = v.left) (ha : a'.left = a.left)
    (w' : v' ≫ V.obj.hom = a' ≫ G.target)
    (w : v ≫ (Over.map g).map V.obj.hom = a ≫ (Over.map g).map G.target) :
    pushforwardAct g V v a w = overAscend g hb (V.action v' a' w') := by
  rw [pushforwardAct_def, pushforwardDescentIso_hom_comp_snd, ← Category.assoc,
    lift_comp_preservesPullbackIso_inv g V.obj.hom G.target hb v a v' a' hv ha w' w,
    ← overAscend_comp]
  rfl

/-- The point of `Y` under a generalized point of the object scheme of the pushforward. -/
lemma object_base (V : EquivariantScheme G) {A : Over S}
    (v : A ⟶ (Over.map g).obj V.obj.left) : (v.left ≫ V.obj.left.hom) ≫ g = A.hom :=
  (Category.assoc _ _ _).trans (Over.w v)

/-- An arrow acting on a generalized point of the object scheme lies over the same point of
`Y` as that point. -/
lemma arrows_base_of_target (V : EquivariantScheme G) {A : Over S}
    (v : A ⟶ (Over.map g).obj V.obj.left) (a : A ⟶ (Over.map g).obj G.arrows)
    (w : v ≫ (Over.map g).map V.obj.hom = a ≫ (Over.map g).map G.target) :
    a.left ≫ G.arrows.hom = v.left ≫ V.obj.left.hom := by
  have hwva : v.left ≫ V.obj.hom.left = a.left ≫ G.target.left := congrArg Over.Hom.left w
  rw [← Over.w G.target, ← Category.assoc, ← hwva, Category.assoc, Over.w V.obj.hom]

/-- The compatibility of a generalized point of the pushforward with its arrow, after
descending both along their common base point in `Y`. -/
private theorem overDescend_comp_hom_eq (V : EquivariantScheme G) {A : Over S}
    (v : A ⟶ (Over.map g).obj V.obj.left) (a : A ⟶ (Over.map g).obj G.arrows)
    (w : v ≫ (Over.map g).map V.obj.hom = a ≫ (Over.map g).map G.target) :
    overDescend g v rfl ≫ V.obj.hom =
      overDescend g a (arrows_base_of_target g V v a w) ≫ G.target := by
  have hw : v.left ≫ V.obj.hom.left = a.left ≫ G.target.left := congrArg Over.Hom.left w
  exact Over.OverMorphism.ext hw

/-- The normalization of the pushed-forward action along the identity section. -/
lemma pushforwardAct_identity (V : EquivariantScheme G) {A : Over S}
    (v : A ⟶ (Over.map g).obj V.obj.left)
    (w : v ≫ (Over.map g).map V.obj.hom =
      (v ≫ (Over.map g).map V.obj.hom ≫ (Over.map g).map G.identity) ≫
        (Over.map g).map G.target) :
    pushforwardAct g V v
      (v ≫ (Over.map g).map V.obj.hom ≫ (Over.map g).map G.identity) w = v := by
  have hb : (v.left ≫ V.obj.left.hom) ≫ g = A.hom := object_base g V v
  have w' : overDescend g v rfl ≫ V.obj.hom =
      (overDescend g v rfl ≫ V.obj.hom ≫ G.identity) ≫ G.target := by
    rw [Category.assoc, Category.assoc, G.target_identity, Category.comp_id]
  have hid : V.action (overDescend g v rfl)
      (overDescend g v rfl ≫ V.obj.hom ≫ G.identity) w' = overDescend g v rfl :=
    V.identity _ (overDescend g v rfl)
  rw [pushforwardAct_eq g V hb v _ (overDescend g v rfl)
    (overDescend g v rfl ≫ V.obj.hom ≫ G.identity) rfl rfl w', hid,
    overAscend_overDescend]

/-- The cocycle law of the pushed-forward action. -/
lemma pushforwardAct_cocycle (V : EquivariantScheme G) {A : Over S}
    (v : A ⟶ (Over.map g).obj V.obj.left) (a b : A ⟶ (Over.map g).obj G.arrows)
    (wva : v ≫ (Over.map g).map V.obj.hom = a ≫ (Over.map g).map G.target)
    (wab : a ≫ (Over.map g).map G.source = b ≫ (Over.map g).map G.target)
    (w₁ : pushforwardAct g V v a wva ≫ (Over.map g).map V.obj.hom =
      b ≫ (Over.map g).map G.target)
    (w₂ : v ≫ (Over.map g).map V.obj.hom =
      (pullback.lift a b wab ≫ GroupoidScheme.pushforwardComp g G) ≫
        (Over.map g).map G.target) :
    pushforwardAct g V (pushforwardAct g V v a wva) b w₁ =
      pushforwardAct g V v (pullback.lift a b wab ≫ GroupoidScheme.pushforwardComp g G) w₂ := by
  have hb : (v.left ≫ V.obj.left.hom) ≫ g = A.hom := object_base g V v
  have hwab : a.left ≫ G.source.left = b.left ≫ G.target.left :=
    congrArg Over.Hom.left wab
  have ha : a.left ≫ G.arrows.hom = v.left ≫ V.obj.left.hom :=
    arrows_base_of_target g V v a wva
  have hbb : b.left ≫ G.arrows.hom = v.left ≫ V.obj.left.hom :=
    (GroupoidScheme.arrows_base_of_source g G a b wab).trans ha
  have wva' := overDescend_comp_hom_eq g V v a wva
  have wab' : overDescend g a ha ≫ G.source = overDescend g b hbb ≫ G.target :=
    Over.OverMorphism.ext hwab
  have hA := pushforwardAct_eq g V hb v a (overDescend g v rfl) (overDescend g a ha)
    rfl rfl wva' wva
  have hC := GroupoidScheme.lift_comp_pushforwardComp' g G hb a b
    (overDescend g a ha) (overDescend g b hbb) rfl rfl wab' wab
  have w₁' : V.action (overDescend g v rfl) (overDescend g a ha) wva' ≫ V.obj.hom =
      overDescend g b hbb ≫ G.target :=
    (V.action_comp_hom _ _ wva').trans wab'
  have w₂' : overDescend g v rfl ≫ V.obj.hom =
      (pullback.lift (overDescend g a ha) (overDescend g b hbb) wab' ≫ G.comp) ≫ G.target := by
    rwa [Category.assoc, G.target_comp, ← Category.assoc, pullback.lift_fst]
  rw [pushforwardAct_eq g V hb _ b (V.action (overDescend g v rfl) (overDescend g a ha) wva')
      (overDescend g b hbb) (congrArg Over.Hom.left hA).symm rfl w₁' w₁,
    pushforwardAct_eq g V hb v _ (overDescend g v rfl)
      (pullback.lift (overDescend g a ha) (overDescend g b hbb) wab' ≫ G.comp)
      rfl (congrArg Over.Hom.left hC).symm w₂' w₂]
  exact congrArg (overAscend g hb)
    (V.cocycle _ (overDescend g v rfl) (overDescend g a ha) (overDescend g b hbb) wva' wab')

/-- **The pushforward of an equivariant scheme.**  For `g : Y ⟶ S` and an equivariant scheme
for a groupoid scheme `G` over `Y`, this is the equivariant scheme for `G.pushforward g` with
the same object scheme and the same descent isomorphism. -/
def pushforwardEquivariantObj (V : EquivariantScheme G) :
    EquivariantScheme (G.pushforward g) where
  obj := Over.mk ((Over.map g).map V.obj.hom)
  descentIso := pushforwardDescentIso g V
  descentIso_over := pushforwardDescentIso_over g V
  identity := fun _ v => pushforwardAct_identity g V v _
  cocycle := fun _ v a b wva wab => pushforwardAct_cocycle g V v a b wva wab _ _

/-- The object scheme of the pushforward of `V` is the image of the object scheme of `V`, over
the image of the object scheme of `G`. -/
@[simp]
lemma pushforwardEquivariantObj_obj (V : EquivariantScheme G) :
    (pushforwardEquivariantObj g V).obj = Over.mk ((Over.map g).map V.obj.hom) := rfl

/-- The action of the pushforward of an equivariant scheme is
`AlgebraicGeometry.EquivariantScheme.pushforwardAct`. -/
lemma pushforwardEquivariantObj_action (V : EquivariantScheme G) {A : Over S}
    (v : A ⟶ (Over.map g).obj V.obj.left) (a : A ⟶ (Over.map g).obj G.arrows)
    (w : v ≫ (Over.map g).map V.obj.hom = a ≫ (Over.map g).map G.target) :
    (pushforwardEquivariantObj g V).action v a w = pushforwardAct g V v a w := rfl

/-- The morphism of object schemes underlying the pushforward of an equivariant morphism. -/
def pushforwardObjMap {V W : EquivariantScheme G} (φ : V ⟶ W) :
    (Over.mk ((Over.map g).map V.obj.hom) : Over ((Over.map g).obj G.objects)) ⟶
      Over.mk ((Over.map g).map W.obj.hom) :=
  Over.homMk ((Over.map g).map φ.hom.left) (by
    have h : (Over.map g).map φ.hom.left ≫ (Over.map g).map W.obj.hom =
        (Over.map g).map V.obj.hom := by
      rw [← Functor.map_comp, Over.w φ.hom]
    exact h)

/-- The underlying morphism of `AlgebraicGeometry.EquivariantScheme.pushforwardObjMap g φ` is
the image of the underlying morphism of `φ`. -/
@[simp]
lemma pushforwardObjMap_left {V W : EquivariantScheme G} (φ : V ⟶ W) :
    (pushforwardObjMap g φ).left = (Over.map g).map φ.hom.left := rfl

/-- **An equivariant morphism commutes with the pushed-forward actions.** -/
lemma pushforwardAct_comp_map {V W : EquivariantScheme G} (φ : V ⟶ W) {A : Over S}
    (v : A ⟶ (Over.map g).obj V.obj.left) (a : A ⟶ (Over.map g).obj G.arrows)
    (w : v ≫ (Over.map g).map V.obj.hom = a ≫ (Over.map g).map G.target)
    (w' : (v ≫ (Over.map g).map φ.hom.left) ≫ (Over.map g).map W.obj.hom =
      a ≫ (Over.map g).map G.target) :
    pushforwardAct g V v a w ≫ (Over.map g).map φ.hom.left =
      pushforwardAct g W (v ≫ (Over.map g).map φ.hom.left) a w' := by
  have hb : (v.left ≫ V.obj.left.hom) ≫ g = A.hom := object_base g V v
  have ha : a.left ≫ G.arrows.hom = v.left ≫ V.obj.left.hom :=
    arrows_base_of_target g V v a w
  have wva' := overDescend_comp_hom_eq g V v a w
  have wW : (overDescend g v rfl ≫ φ.hom.left) ≫ W.obj.hom =
      overDescend g a ha ≫ G.target := by
    rwa [Category.assoc, Over.w φ.hom]
  rw [pushforwardAct_eq g V hb v a (overDescend g v rfl) (overDescend g a ha) rfl rfl wva' w,
    pushforwardAct_eq g W hb _ a (overDescend g v rfl ≫ φ.hom.left) (overDescend g a ha)
      rfl rfl wW w', ← overAscend_comp]
  exact congrArg (overAscend g hb) (φ.comm _ (overDescend g v rfl) (overDescend g a ha) wva')

/-- The pushforward of an equivariant morphism. -/
def pushforwardEquivariantMap {V W : EquivariantScheme G} (φ : V ⟶ W) :
    pushforwardEquivariantObj g V ⟶ pushforwardEquivariantObj g W :=
  homMk (pushforwardObjMap g φ)
    (fun v a w w' => pushforwardAct_comp_map g φ v a w w')

/-- The underlying morphism of the pushforward of an equivariant morphism `φ` is the image of
the underlying morphism of `φ`. -/
@[simp]
lemma pushforwardEquivariantMap_hom_left {V W : EquivariantScheme G} (φ : V ⟶ W) :
    (pushforwardEquivariantMap g φ).hom.left = (Over.map g).map φ.hom.left := rfl

/-- The underlying morphism of an identity equivariant morphism. -/
@[simp]
lemma id_hom_left {S : Scheme.{u}} {H : GroupoidScheme S} (V : EquivariantScheme H) :
    (𝟙 V : V ⟶ V).hom.left = 𝟙 V.obj.left := rfl

/-- The underlying morphism of a composite of equivariant morphisms. -/
@[simp]
lemma comp_hom_left {S : Scheme.{u}} {H : GroupoidScheme S} {V W Z : EquivariantScheme H}
    (φ : V ⟶ W) (ψ : W ⟶ Z) : (φ ≫ ψ).hom.left = φ.hom.left ≫ ψ.hom.left := rfl

/-- **The comparison functor**: the pushforward of an equivariant scheme for a groupoid scheme
over `Y` to one for its pushforward to `S`. -/
def pushforwardEquivariantFunctor (H : GroupoidScheme Y) :
    EquivariantScheme H ⥤ EquivariantScheme (H.pushforward g) where
  obj V := pushforwardEquivariantObj g V
  map φ := pushforwardEquivariantMap g φ
  map_id V := by
    refine EquivariantScheme.hom_ext _ _ ?_
    apply Over.OverMorphism.ext
    rw [pushforwardEquivariantMap_hom_left, id_hom_left, id_hom_left,
      CategoryTheory.Functor.map_id]
    rfl
  map_comp φ ψ := by
    refine EquivariantScheme.hom_ext _ _ ?_
    apply Over.OverMorphism.ext
    rw [pushforwardEquivariantMap_hom_left, comp_hom_left, comp_hom_left,
      pushforwardEquivariantMap_hom_left, pushforwardEquivariantMap_hom_left,
      CategoryTheory.Functor.map_comp]
    rfl

/-- The comparison functor sends an equivariant morphism `φ` to one whose underlying morphism
is the image of the underlying morphism of `φ`. -/
@[simp]
lemma pushforwardEquivariantFunctor_map_hom_left {V W : EquivariantScheme G} (φ : V ⟶ W) :
    ((pushforwardEquivariantFunctor g G).map φ).hom.left = (Over.map g).map φ.hom.left := rfl

/-- The action of an equivariant scheme, by its definition. -/
lemma action_def {S : Scheme.{u}} {H : GroupoidScheme S} (V : EquivariantScheme H)
    {T : Over S} (v : T ⟶ V.obj.left) (a : T ⟶ H.arrows)
    (w : v ≫ V.obj.hom = a ≫ H.target) :
    V.action v a w =
      pullback.lift v a w ≫ V.descentIso.hom ≫ pullback.snd H.source V.obj.hom := rfl

/-- **The pushed-forward action at images of generalized points of `Over Y`.** -/
lemma pushforwardAct_map (V : EquivariantScheme G) {T : Over Y}
    (v₀ : (Over.map g).obj T ⟶ (Over.map g).obj V.obj.left)
    (a₀ : (Over.map g).obj T ⟶ (Over.map g).obj G.arrows)
    (v : T ⟶ V.obj.left) (a : T ⟶ G.arrows)
    (hv : v.left = v₀.left) (ha : a.left = a₀.left)
    (w : v ≫ V.obj.hom = a ≫ G.target)
    (w₀ : v₀ ≫ (Over.map g).map V.obj.hom = a₀ ≫ (Over.map g).map G.target) :
    pushforwardAct g V v₀ a₀ w₀ = (Over.map g).map (V.action v a w) := by
  rw [pushforwardAct_eq g V (rfl : T.hom ≫ g = ((Over.map g).obj T).hom) v₀ a₀ v a hv ha w w₀,
    overAscend_self]

/-- The morphism of object schemes underlying an equivariant morphism between pushforwards,
spelled in the image of `Over Y`. -/
def pushforwardHomLeft {V W : EquivariantScheme G}
    (ψ : pushforwardEquivariantObj g V ⟶ pushforwardEquivariantObj g W) :
    (Over.map g).obj V.obj.left ⟶ (Over.map g).obj W.obj.left := ψ.hom.left

/-- The underlying morphism of schemes of
`AlgebraicGeometry.EquivariantScheme.pushforwardHomLeft g ψ` is that of `ψ`. -/
@[simp]
lemma pushforwardHomLeft_left {V W : EquivariantScheme G}
    (ψ : pushforwardEquivariantObj g V ⟶ pushforwardEquivariantObj g W) :
    (pushforwardHomLeft g ψ).left = ψ.hom.left.left := rfl

/-- An equivariant morphism between pushforwards commutes with the pushed-forward actions. -/
lemma pushforwardAct_comm_of_hom {V W : EquivariantScheme G}
    (ψ : pushforwardEquivariantObj g V ⟶ pushforwardEquivariantObj g W)
    {A : Over S} (v : A ⟶ (Over.map g).obj V.obj.left) (a : A ⟶ (Over.map g).obj G.arrows)
    (w : v ≫ (Over.map g).map V.obj.hom = a ≫ (Over.map g).map G.target)
    (w' : (v ≫ pushforwardHomLeft g ψ) ≫ (Over.map g).map W.obj.hom =
      a ≫ (Over.map g).map G.target) :
    pushforwardAct g V v a w ≫ pushforwardHomLeft g ψ =
      pushforwardAct g W (v ≫ pushforwardHomLeft g ψ) a w' :=
  ψ.comm A v a w

/-- The comparison functor is faithful: an equivariant morphism is determined by its
underlying morphism of schemes, and so is its image. -/
instance : (pushforwardEquivariantFunctor g G).Faithful where
  map_injective {V W} {φ ψ} h := by
    have h1 := congrArg EquivariantScheme.Hom.hom h
    have h2 := congrArg Over.Hom.left h1
    have h3 := congrArg Over.Hom.left h2
    exact EquivariantScheme.hom_ext _ _ (Over.OverMorphism.ext (Over.OverMorphism.ext h3))

/-- The comparison functor is full: an equivariant morphism between pushforwards comes from
one downstairs, because a morphism of the image object schemes which respects the structure
morphisms to the image of `G.objects` respects the structure morphisms to `Y` as well. -/
instance : (pushforwardEquivariantFunctor g G).Full where
  map_surjective {V W} ψ := by
    have hk : pushforwardHomLeft g ψ ≫ (Over.map g).map W.obj.hom =
        (Over.map g).map V.obj.hom := Over.w ψ.hom
    have hkl : (pushforwardHomLeft g ψ).left ≫ W.obj.hom.left = V.obj.hom.left :=
      congrArg Over.Hom.left hk
    have h1 : (pushforwardHomLeft g ψ).left ≫ W.obj.left.hom = V.obj.left.hom := by
      rw [← Over.w W.obj.hom, ← Category.assoc, hkl, Over.w V.obj.hom]
    have hmk : (Over.map g).map
        (Over.homMk (pushforwardHomLeft g ψ).left h1 : V.obj.left ⟶ W.obj.left) =
          pushforwardHomLeft g ψ := by
      apply Over.OverMorphism.ext
      rfl
    refine ⟨homMk (Over.homMk (Over.homMk (pushforwardHomLeft g ψ).left h1)
      (Over.OverMorphism.ext hkl)) ?_, ?_⟩
    · intro T v a w w'
      have w₂ : (Over.map g).map v ≫ (Over.map g).map V.obj.hom =
          (Over.map g).map a ≫ (Over.map g).map G.target := by
        rw [← Functor.map_comp, ← Functor.map_comp, w]
      have w₃ : ((Over.map g).map v ≫ pushforwardHomLeft g ψ) ≫ (Over.map g).map W.obj.hom =
          (Over.map g).map a ≫ (Over.map g).map G.target := by
        rwa [Category.assoc, hk]
      have hL := pushforwardAct_map g V ((Over.map g).map v) ((Over.map g).map a) v a rfl rfl
        w w₂
      have hR := pushforwardAct_map g W ((Over.map g).map v ≫ pushforwardHomLeft g ψ)
        ((Over.map g).map a)
        (v ≫ Over.homMk (pushforwardHomLeft g ψ).left h1) a rfl rfl w' w₃
      have hc := pushforwardAct_comm_of_hom g ψ ((Over.map g).map v) ((Over.map g).map a) w₂ w₃
      rw [hL, hR] at hc
      have key : (Over.map g).map (V.action v a w ≫
          (Over.homMk (pushforwardHomLeft g ψ).left h1 : V.obj.left ⟶ W.obj.left)) =
            (Over.map g).map
              (W.action (v ≫ Over.homMk (pushforwardHomLeft g ψ).left h1) a w') := by
        rw [Functor.map_comp, hmk]
        exact hc
      have key2 := congrArg Over.Hom.left key
      exact Over.OverMorphism.ext key2
    · exact EquivariantScheme.hom_ext _ _ (Over.OverMorphism.ext hmk)

section Descend

variable (W : EquivariantScheme (G.pushforward g))

/-- The structure morphism of `W`, with the object scheme of the pushforward spelled through
`CategoryTheory.Over.map`. -/
def descendObjHom : W.obj.left ⟶ (Over.map g).obj G.objects := W.obj.hom

/-- The underlying morphism of `AlgebraicGeometry.EquivariantScheme.descendObjHom g W` is that
of the structure morphism of `W`. -/
@[simp]
lemma descendObjHom_left : (descendObjHom g W).left = W.obj.hom.left := rfl

/-- The descent isomorphism of `W`, with the structure morphisms of the pushforward spelled
through `CategoryTheory.Over.map`. -/
def descendDescentIso' : pullback (descendObjHom g W) ((Over.map g).map G.target) ≅
    pullback ((Over.map g).map G.source) (descendObjHom g W) := W.descentIso

/-- The descent isomorphism of `W` lies over the arrow scheme. -/
lemma descendDescentIso'_over :
    (descendDescentIso' g W).hom ≫
        pullback.fst ((Over.map g).map G.source) (descendObjHom g W) =
      pullback.snd (descendObjHom g W) ((Over.map g).map G.target) := W.descentIso_over

/-- The action of `W`, with the structure morphisms spelled through `CategoryTheory.Over.map`. -/
lemma descendAction_def {A : Over S} (v : A ⟶ W.obj.left) (a : A ⟶ (Over.map g).obj G.arrows)
    (w : v ≫ descendObjHom g W = a ≫ (Over.map g).map G.target) :
    W.action v a w = pullback.lift v a w ≫ (descendDescentIso' g W).hom ≫
      pullback.snd ((Over.map g).map G.source) (descendObjHom g W) := rfl

/-- The scheme over `Y` under the object scheme of an equivariant scheme for the pushforward:
its underlying scheme, taken over `Y` through the structure morphism to the object scheme. -/
abbrev descendOver : Over Y := Over.mk ((descendObjHom g W).left ≫ G.objects.hom)

/-- Its structure morphism to the object scheme of `G`. -/
def descendHom : descendOver g W ⟶ G.objects := Over.homMk (descendObjHom g W).left rfl

/-- The underlying morphism of `AlgebraicGeometry.EquivariantScheme.descendHom g W` is that of
the structure morphism of `W`. -/
@[simp]
lemma descendHom_left : (descendHom g W).left = (descendObjHom g W).left := rfl

/-- The comparison between the image of the descended object scheme and the object scheme of
`W`: the identity on underlying schemes. -/
def descendComparison : (Over.map g).obj (descendOver g W) ≅ W.obj.left :=
  Over.isoMk (Iso.refl _) (by
    have h : (descendObjHom g W).left ≫ (G.objects.hom ≫ g) = W.obj.left.hom :=
      Over.w (descendObjHom g W)
    rw [Iso.refl_hom, Category.id_comp]
    exact h.symm.trans (Category.assoc _ _ _).symm)

/-- The forward map of the comparison is the identity on underlying schemes. -/
@[simp]
lemma descendComparison_hom_left : (descendComparison g W).hom.left = 𝟙 W.obj.left.left := rfl

/-- The inverse map of the comparison is the identity on underlying schemes. -/
@[simp]
lemma descendComparison_inv_left : (descendComparison g W).inv.left = 𝟙 W.obj.left.left := rfl

/-- The image of the descended structure morphism is the structure morphism of `W`,
transported along the comparison. -/
lemma map_descendHom :
    (Over.map g).map (descendHom g W) = (descendComparison g W).hom ≫ descendObjHom g W :=
  Over.OverMorphism.ext (Category.id_comp _).symm

/-- A generalized point of the descended object scheme acted on by an arrow, read through the
comparison with the object scheme of `W`. -/
private lemma map_comp_descendComparison_hom_comp {A : Over Y} (v : A ⟶ descendOver g W)
    (a : A ⟶ G.arrows) (w : v ≫ descendHom g W = a ≫ G.target) :
    ((Over.map g).map v ≫ (descendComparison g W).hom) ≫ descendObjHom g W =
      (Over.map g).map a ≫ (Over.map g).map G.target := by
  rw [Category.assoc, ← map_descendHom, ← Functor.map_comp, ← Functor.map_comp, w]

/-- The descent isomorphism of `W`, read on the pullbacks of the descended structure
morphism. -/
def descendDescentIsoAux :
    (Over.map g).obj (pullback (descendHom g W) G.target) ≅
      (Over.map g).obj (pullback G.source (descendHom g W)) :=
  PreservesPullback.iso (Over.map g) (descendHom g W) G.target ≪≫
    pullbackLeftLegIso (descendComparison g W) ((Over.map g).map G.target)
      (map_descendHom g W) ≪≫
    descendDescentIso' g W ≪≫
    (pullbackRightLegIso (descendComparison g W) ((Over.map g).map G.source)
      (map_descendHom g W)).symm ≪≫
    (PreservesPullback.iso (Over.map g) G.source (descendHom g W)).symm

/-- The forward map of `AlgebraicGeometry.EquivariantScheme.descendDescentIsoAux g W` as a
composite of the forward maps of its five factors. -/
lemma descendDescentIsoAux_hom :
    (descendDescentIsoAux g W).hom =
      (PreservesPullback.iso (Over.map g) (descendHom g W) G.target).hom ≫
        (pullbackLeftLegIso (descendComparison g W) ((Over.map g).map G.target)
          (map_descendHom g W)).hom ≫ (descendDescentIso' g W).hom ≫
        (pullbackRightLegIso (descendComparison g W) ((Over.map g).map G.source)
          (map_descendHom g W)).inv ≫
        (PreservesPullback.iso (Over.map g) G.source (descendHom g W)).inv := rfl

/-- The transported descent isomorphism lies over the arrow scheme. -/
lemma descendDescentIsoAux_over :
    (descendDescentIsoAux g W).hom ≫
        (Over.map g).map (pullback.fst G.source (descendHom g W)) =
      (Over.map g).map (pullback.snd (descendHom g W) G.target) := by
  rw [descendDescentIsoAux_hom]
  simp only [Category.assoc]
  rw [PreservesPullback.iso_inv_fst, pullbackRightLegIso_inv_comp_fst,
    descendDescentIso'_over, pullbackLeftLegIso_hom_comp_snd, PreservesPullback.iso_hom_snd]

/-- The transported descent isomorphism, on underlying schemes. -/
lemma descendDescentIsoAux_over_left :
    (descendDescentIsoAux g W).hom.left ≫ (pullback.fst G.source (descendHom g W)).left =
      (pullback.snd (descendHom g W) G.target).left := by
  have h := congrArg Over.Hom.left (descendDescentIsoAux_over g W)
  rw [Over.comp_left, Over.map_map_left, Over.map_map_left] at h
  exact h

/-- The transported descent isomorphism respects the structure morphisms to `Y`, so it
descends. -/
lemma descendDescentIsoAux_hom_left_comp :
    (descendDescentIsoAux g W).hom.left ≫ (pullback G.source (descendHom g W)).hom =
      (pullback (descendHom g W) G.target).hom := by
  rw [← Over.w (pullback.snd (descendHom g W) G.target), ← descendDescentIsoAux_over_left,
    Category.assoc, Over.w (pullback.fst G.source (descendHom g W))]

/-- The descent isomorphism of the descended equivariant scheme. -/
def descendDescentIso :
    pullback (descendHom g W) G.target ≅ pullback G.source (descendHom g W) :=
  overDescendIso g (descendDescentIsoAux g W) (descendDescentIsoAux_hom_left_comp g W)

/-- The image of the descended descent isomorphism is the transported descent isomorphism. -/
lemma map_descendDescentIso_hom :
    (Over.map g).map (descendDescentIso g W).hom = (descendDescentIsoAux g W).hom :=
  map_overDescendIso_hom g _ _

/-- The descended descent isomorphism lies over the arrow scheme. -/
lemma descendDescentIso_over :
    (descendDescentIso g W).hom ≫ pullback.fst G.source (descendHom g W) =
      pullback.snd (descendHom g W) G.target :=
  Over.OverMorphism.ext (descendDescentIsoAux_over_left g W)

/-- The action of the descended equivariant scheme on generalized points. -/
def descendAct {A : Over Y} (v : A ⟶ descendOver g W) (a : A ⟶ G.arrows)
    (w : v ≫ descendHom g W = a ≫ G.target) : A ⟶ descendOver g W :=
  pullback.lift v a w ≫ (descendDescentIso g W).hom ≫
    pullback.snd G.source (descendHom g W)

/-- The action of the descended equivariant scheme, by its definition. -/
lemma descendAct_def {A : Over Y} (v : A ⟶ descendOver g W) (a : A ⟶ G.arrows)
    (w : v ≫ descendHom g W = a ≫ G.target) :
    descendAct g W v a w = pullback.lift v a w ≫ (descendDescentIso g W).hom ≫
      pullback.snd G.source (descendHom g W) := rfl

/-- The image of the second projection of the descended descent isomorphism is the second
projection of the transported descent isomorphism. -/
lemma map_descendDescentIso_hom_comp_snd :
    (Over.map g).map ((descendDescentIso g W).hom ≫ pullback.snd G.source (descendHom g W)) =
      (descendDescentIsoAux g W).hom ≫
        (Over.map g).map (pullback.snd G.source (descendHom g W)) := by
  rw [Functor.map_comp, map_descendDescentIso_hom]

/-- The second projection of the transported descent isomorphism. -/
lemma descendDescentIsoAux_hom_comp_snd :
    (descendDescentIsoAux g W).hom ≫
        (Over.map g).map (pullback.snd G.source (descendHom g W)) =
      (PreservesPullback.iso (Over.map g) (descendHom g W) G.target).hom ≫
        (pullbackLeftLegIso (descendComparison g W) ((Over.map g).map G.target)
          (map_descendHom g W)).hom ≫ (descendDescentIso' g W).hom ≫
        pullback.snd ((Over.map g).map G.source) (descendObjHom g W) ≫
          (descendComparison g W).inv := by
  rw [descendDescentIsoAux_hom]
  simp only [Category.assoc]
  rw [PreservesPullback.iso_inv_snd, pullbackRightLegIso_inv_comp_snd]

/-- **The action of the descended equivariant scheme is the action of `W`.** -/
lemma overAscend_descendAct {A : Over S} {base : A.left ⟶ Y} (hb : base ≫ g = A.hom)
    (v : (Over.mk base : Over Y) ⟶ descendOver g W) (a : (Over.mk base : Over Y) ⟶ G.arrows)
    (w : v ≫ descendHom g W = a ≫ G.target)
    (v₀ : A ⟶ (Over.map g).obj (descendOver g W)) (a₀ : A ⟶ (Over.map g).obj G.arrows)
    (hv : v.left = v₀.left) (ha : a.left = a₀.left)
    (w₀ : (v₀ ≫ (descendComparison g W).hom) ≫ descendObjHom g W =
      a₀ ≫ (Over.map g).map G.target) :
    overAscend g hb (descendAct g W v a w) =
      W.action (v₀ ≫ (descendComparison g W).hom) a₀ w₀ ≫ (descendComparison g W).inv := by
  have w₁ : v₀ ≫ (Over.map g).map (descendHom g W) = a₀ ≫ (Over.map g).map G.target := by
    rwa [map_descendHom, ← Category.assoc]
  have hl := lift_comp_preservesPullbackIso_inv g (descendHom g W) G.target hb v₀ a₀ v a
    hv ha w w₁
  have hpbL : pullback.lift v₀ a₀ w₁ ≫
      (pullbackLeftLegIso (descendComparison g W) ((Over.map g).map G.target)
        (map_descendHom g W)).hom =
      pullback.lift (v₀ ≫ (descendComparison g W).hom) a₀ w₀ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullbackLeftLegIso_hom_comp_fst, ← Category.assoc,
        pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullbackLeftLegIso_hom_comp_snd, pullback.lift_snd,
        pullback.lift_snd]
  rw [descendAct_def, overAscend_comp, ← hl, map_descendDescentIso_hom_comp_snd,
    descendDescentIsoAux_hom_comp_snd, descendAction_def]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc, ← Category.assoc (pullback.lift v₀ a₀ w₁), hpbL]

/-- `AlgebraicGeometry.EquivariantScheme.overAscend_descendAct` at images of generalized points
of `Over Y`. -/
lemma map_descendAct {A : Over Y} (v : A ⟶ descendOver g W) (a : A ⟶ G.arrows)
    (w : v ≫ descendHom g W = a ≫ G.target)
    (w₀ : ((Over.map g).map v ≫ (descendComparison g W).hom) ≫ descendObjHom g W =
      (Over.map g).map a ≫ (Over.map g).map G.target) :
    (Over.map g).map (descendAct g W v a w) =
      W.action ((Over.map g).map v ≫ (descendComparison g W).hom) ((Over.map g).map a) w₀ ≫
        (descendComparison g W).inv := by
  rw [← overAscend_self g (descendAct g W v a w)]
  exact overAscend_descendAct g W (A := (Over.map g).obj A) (base := A.hom) rfl v a w
    ((Over.map g).map v) ((Over.map g).map a) rfl rfl w₀

/-- The normalization of the descended action along the identity section. -/
lemma descendAct_identity {A : Over Y} (v : A ⟶ descendOver g W)
    (w : v ≫ descendHom g W = (v ≫ descendHom g W ≫ G.identity) ≫ G.target) :
    descendAct g W v (v ≫ descendHom g W ≫ G.identity) w = v := by
  have w₀ := map_comp_descendComparison_hom_comp g W v _ w
  have w₂ : ((Over.map g).map v ≫ (descendComparison g W).hom) ≫ descendObjHom g W =
      ((((Over.map g).map v ≫ (descendComparison g W).hom) ≫ descendObjHom g W ≫
        (Over.map g).map G.identity)) ≫ (Over.map g).map G.target := by
    simp only [Category.assoc, ← Functor.map_comp, G.target_identity,
      CategoryTheory.Functor.map_id, Category.comp_id]
  have harr : (Over.map g).map (v ≫ descendHom g W ≫ G.identity) =
      ((Over.map g).map v ≫ (descendComparison g W).hom) ≫ descendObjHom g W ≫
        (Over.map g).map G.identity := by
    rw [Category.assoc, ← Category.assoc (descendComparison g W).hom, ← map_descendHom,
      ← Functor.map_comp, ← Functor.map_comp]
  have hid : W.action ((Over.map g).map v ≫ (descendComparison g W).hom)
      ((((Over.map g).map v ≫ (descendComparison g W).hom) ≫ descendObjHom g W ≫
        (Over.map g).map G.identity)) w₂ =
      (Over.map g).map v ≫ (descendComparison g W).hom := W.identity _ _
  have hlast : ((Over.map g).map v ≫ (descendComparison g W).hom) ≫
      (descendComparison g W).inv = (Over.map g).map v := by
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have key : (Over.map g).map (descendAct g W v (v ≫ descendHom g W ≫ G.identity) w) =
      (Over.map g).map v :=
    ((map_descendAct g W v _ w w₀).trans
      (congrArg (fun z ↦ z ≫ (descendComparison g W).inv)
        ((W.action_arrow_eq _ _ _ w₀ w₂ harr).trans hid))).trans hlast
  have key2 := congrArg Over.Hom.left key
  exact Over.OverMorphism.ext key2

/-- The cocycle law of the descended action. -/
lemma descendAct_cocycle {A : Over Y} (v : A ⟶ descendOver g W) (a b : A ⟶ G.arrows)
    (wva : v ≫ descendHom g W = a ≫ G.target) (wab : a ≫ G.source = b ≫ G.target)
    (w₁ : descendAct g W v a wva ≫ descendHom g W = b ≫ G.target)
    (w₂ : v ≫ descendHom g W = G.compose a b wab ≫ G.target) :
    descendAct g W (descendAct g W v a wva) b w₁ =
      descendAct g W v (G.compose a b wab) w₂ := by
  have w₀a := map_comp_descendComparison_hom_comp g W v a wva
  have hA := map_descendAct g W v a wva w₀a
  have hAh : (Over.map g).map (descendAct g W v a wva) ≫ (descendComparison g W).hom =
      W.action ((Over.map g).map v ≫ (descendComparison g W).hom) ((Over.map g).map a) w₀a := by
    rw [hA, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have w₀b := map_comp_descendComparison_hom_comp g W _ b w₁
  have w₀c := map_comp_descendComparison_hom_comp g W v _ w₂
  have wab' : (Over.map g).map a ≫ (Over.map g).map G.source =
      (Over.map g).map b ≫ (Over.map g).map G.target := by
    rw [← Functor.map_comp, ← Functor.map_comp, wab]
  have hcomp : (Over.map g).map (G.compose a b wab) =
      (G.pushforward g).compose ((Over.map g).map a) ((Over.map g).map b) wab' :=
    ((GroupoidScheme.pushforward_compose g G (A := (Over.map g).obj A) (base := A.hom) rfl
      ((Over.map g).map a) ((Over.map g).map b) a b rfl rfl wab wab').trans
        (overAscend_self g (G.compose a b wab))).symm
  have w₀d : ((Over.map g).map v ≫ (descendComparison g W).hom) ≫ descendObjHom g W =
      (G.pushforward g).compose ((Over.map g).map a) ((Over.map g).map b) wab' ≫
        (Over.map g).map G.target := by
    rw [w₀c, hcomp]
    rfl
  have w₀e : W.action ((Over.map g).map v ≫ (descendComparison g W).hom)
      ((Over.map g).map a) w₀a ≫ descendObjHom g W =
      (Over.map g).map b ≫ (Over.map g).map G.target := by rwa [← hAh]
  have hcoc : W.action (W.action ((Over.map g).map v ≫ (descendComparison g W).hom)
        ((Over.map g).map a) w₀a) ((Over.map g).map b) w₀e =
      W.action ((Over.map g).map v ≫ (descendComparison g W).hom)
        ((G.pushforward g).compose ((Over.map g).map a) ((Over.map g).map b) wab') w₀d :=
    W.cocycle _ _ _ _ w₀a wab'
  have hstep : W.action ((Over.map g).map (descendAct g W v a wva) ≫
        (descendComparison g W).hom) ((Over.map g).map b) w₀b =
      W.action ((Over.map g).map v ≫ (descendComparison g W).hom)
        ((Over.map g).map (G.compose a b wab)) w₀c :=
    ((W.action_point_eq _ w₀b w₀e hAh).trans hcoc).trans
      (W.action_arrow_eq _ _ _ w₀d w₀c hcomp.symm)
  have key : (Over.map g).map (descendAct g W (descendAct g W v a wva) b w₁) =
      (Over.map g).map (descendAct g W v (G.compose a b wab) w₂) :=
    ((map_descendAct g W _ b w₁ w₀b).trans
      (congrArg (fun z ↦ z ≫ (descendComparison g W).inv) hstep)).trans
      (map_descendAct g W v _ w₂ w₀c).symm
  have key2 := congrArg Over.Hom.left key
  exact Over.OverMorphism.ext key2

/-- **The descended equivariant scheme.**  An equivariant scheme for `G.pushforward g`
determines one for `G`: its object scheme is taken over `Y` through the structure morphism to
the object scheme, and its descent isomorphism is the transported one. -/
def descendEquivariant : EquivariantScheme G where
  obj := Over.mk (descendHom g W)
  descentIso := descendDescentIso g W
  descentIso_over := descendDescentIso_over g W
  identity := fun _ v => descendAct_identity g W v _
  cocycle := fun _ v a b wva wab => descendAct_cocycle g W v a b wva wab _ _

/-- The object of the descended equivariant scheme is the descended structure morphism. -/
@[simp]
lemma descendEquivariant_obj : (descendEquivariant g W).obj = Over.mk (descendHom g W) := rfl

/-- The pushforward of the descended equivariant scheme acts as `W` does. -/
lemma pushforwardAct_descendEquivariant {A : Over S}
    (v : A ⟶ (Over.map g).obj (descendOver g W)) (a : A ⟶ (Over.map g).obj G.arrows)
    (w : v ≫ (Over.map g).map (descendHom g W) = a ≫ (Over.map g).map G.target)
    (w₀ : (v ≫ (descendComparison g W).hom) ≫ descendObjHom g W =
      a ≫ (Over.map g).map G.target) :
    pushforwardAct g (descendEquivariant g W) v a w =
      W.action (v ≫ (descendComparison g W).hom) a w₀ ≫ (descendComparison g W).inv := by
  have hb : (v.left ≫ (descendOver g W).hom) ≫ g = A.hom :=
    object_base g (descendEquivariant g W) v
  have ha : a.left ≫ G.arrows.hom = v.left ≫ (descendOver g W).hom :=
    arrows_base_of_target g (descendEquivariant g W) v a w
  have w'' : overDescend g v rfl ≫ descendHom g W = overDescend g a ha ≫ G.target :=
    overDescend_comp_hom_eq g (descendEquivariant g W) v a w
  rw [pushforwardAct_eq g (descendEquivariant g W) hb v a (overDescend g v rfl)
    (overDescend g a ha) rfl rfl w'' w]
  exact overAscend_descendAct g W hb (overDescend g v rfl) (overDescend g a ha) w'' v a
    rfl rfl w₀

/-- `AlgebraicGeometry.EquivariantScheme.pushforwardAct_descendEquivariant`, transported
along the comparison. -/
lemma pushforwardAct_descendEquivariant_comp {A : Over S}
    (v : A ⟶ (Over.map g).obj (descendOver g W)) (a : A ⟶ (Over.map g).obj G.arrows)
    (w : v ≫ (Over.map g).map (descendHom g W) = a ≫ (Over.map g).map G.target)
    (w₀ : (v ≫ (descendComparison g W).hom) ≫ descendObjHom g W =
      a ≫ (Over.map g).map G.target) :
    pushforwardAct g (descendEquivariant g W) v a w ≫ (descendComparison g W).hom =
      W.action (v ≫ (descendComparison g W).hom) a w₀ := by
  rw [pushforwardAct_descendEquivariant g W v a w w₀]
  exact comp_inv_comp_hom _ (descendComparison g W)

/-- The comparison of object schemes between the pushforward of the descended equivariant
scheme and `W`. -/
def descendEquivariantObjIso :
    (Over.mk ((Over.map g).map (descendHom g W)) :
        Over ((Over.map g).obj G.objects)) ≅ W.obj :=
  Over.isoMk (descendComparison g W) (map_descendHom g W).symm

/-- The underlying morphism of the forward map of
`AlgebraicGeometry.EquivariantScheme.descendEquivariantObjIso g W` is the comparison. -/
@[simp]
lemma descendEquivariantObjIso_hom_left :
    (descendEquivariantObjIso g W).hom.left = (descendComparison g W).hom := rfl

/-- **The pushforward of the descended equivariant scheme is `W`.** -/
def descendEquivariantIso : pushforwardEquivariantObj g (descendEquivariant g W) ≅ W :=
  isoMk (descendEquivariantObjIso g W)
    (fun v a w w' => pushforwardAct_descendEquivariant_comp g W v a w w')

/-- The comparison functor is essentially surjective. -/
instance : (pushforwardEquivariantFunctor g G).EssSurj where
  mem_essImage W := ⟨descendEquivariant g W, ⟨descendEquivariantIso g W⟩⟩

/-- The comparison functor is an equivalence. -/
instance : (pushforwardEquivariantFunctor g G).IsEquivalence where

/-- **Equivariant schemes for a groupoid scheme over `Y` are the same thing as equivariant
schemes for its pushforward to `S`.** -/
def pushforwardEquivariantEquivalence (H : GroupoidScheme Y) :
    EquivariantScheme H ≌ EquivariantScheme (H.pushforward g) :=
  (pushforwardEquivariantFunctor g H).asEquivalence

end Descend

end Pushforward

end EquivariantScheme

/-- **Groupoid schemes cartesian over a groupoid scheme `G` over `Y` are the same thing as
groupoid schemes cartesian over its pushforward to `S`.** -/
def cartesianOverPushforwardEquivalence {Y S : Scheme.{u}} (g : Y ⟶ S)
    (G : GroupoidScheme Y) : CartesianOver G ≌ CartesianOver (G.pushforward g) :=
  (cartesianOverEquivalenceEquivariantScheme G).trans
    ((EquivariantScheme.pushforwardEquivariantEquivalence g G).trans
      (cartesianOverEquivalenceEquivariantScheme (G.pushforward g)).symm)

end AlgebraicGeometry

end

end
