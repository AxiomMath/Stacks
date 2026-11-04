module

public import StacksFrontier.AlgebraicGeometry.Descent.IntegralEtaleBaseCoordinate
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.Flat
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.FpqcReflect
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale effectivity of a descent datum is fpqc local in the base

Let `f : X ⟶ S` be a surjective integral morphism, `D` a descent datum relative to `X / S` whose
underlying scheme is quasi-compact, separated and étale, and `w : W ⟶ S` a flat surjective
quasi-compact morphism of the base. This file proves that étale effectivity of `D` may be checked
after base change of the base along `w`: if `D.changeDatum w` is étale effective then so is `D`.
This is a step of [Stacks, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP).

## Main definitions

* `AlgebraicGeometry.DescentDatum.Descended.changeBaseDescended`: **the scheme over `S`
  descending the datum relative to the composite `X ×_S W ⟶ S`**, assembled from a scheme over
  `W` descending the base change of `D` and a scheme over `S` descending the datum relative to
  `w` that it carries.

## Main results

* `AlgebraicGeometry.DescentData.PullbackFunctor.act_comp_objIso_fst`: **the gluing action of the
  pullback of a datum along a commutative square, read in the datum coordinate**, is the gluing
  action of the datum itself.
* `AlgebraicGeometry.DescentDatum.changeDatum_act_changePt`: the gluing action of a base-changed
  datum at a point named by its two coordinates: the datum coordinate moves, the base coordinate
  does not.
* `AlgebraicGeometry.DescentDatum.changePt_act_comp_proj`: the projection of a scheme descending
  a base-changed datum does not see the gluing action on the datum coordinate.
* `AlgebraicGeometry.DescentDatum.Descended.changePt_comp_proj_comp`: the composite projection to
  the scheme over `S` does not see the base coordinate.
* `AlgebraicGeometry.DescentDatum.Descended.changeBase_act_comp_proj_comp`: **the invariance of
  that composite for the gluing isomorphism of the datum relative to the composite
  `X ×_S W ⟶ S`**.
* `AlgebraicGeometry.DescentDatum.isEtaleEffective_of_isEtaleEffective_changeDatum`: **étale
  effectivity of a quasi-compact separated étale datum along a surjective integral morphism is
  fpqc local in the base.**

## Implementation notes

The datum relative to the composite `X ×_S W ⟶ S` and the base change `D.changeDatum w` have the
*same* underlying scheme over `X ×_S W`, both being the pullback of `D.over` along
`X ×_S W ⟶ X`: the two pullback functors differ only in the square's base map, which does not
enter the underlying object. That coincidence is definitional, so the two spellings are
interchanged by term-mode type ascription; rewriting across them is not type-correct under the
`implicit` transparency level and is avoided throughout, which is why the computations are
phrased as `calc` chains of `Category.assoc` and `congrArg` rather than `rw` and `simp`.

The gluing isomorphisms of the two data are *not* the same: one lives over `(X ×_S W) ×_W
(X ×_S W)`, the other over `(X ×_S W) ×_S (X ×_S W)`, which fibres over `W ×_S W`. The acting
point of the second therefore carries a `W`-coordinate that the first does not move. Both actions
are read off `AlgebraicGeometry.DescentData.PullbackFunctor.actOn_objIso_fst`, which describes the
action of any pullback of a datum along any commutative square in terms of the original action.

The hypotheses on `D` are those of Tag 0BTP: quasi-compactness and separatedness of the
underlying scheme are what make the datum relative to `w` carried by `Q.base` quasi-compact and
separated, hence effective along `w`.

## References

* [Stacks Project, Tag 023Y](https://stacks.math.columbia.edu/tag/023Y)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

namespace DescentData.PullbackFunctor

variable {S S' X X' : Scheme.{u}} {a : X ⟶ S} {a' : X' ⟶ S'} {hS : S' ⟶ S} {p : X' ⟶ X}
  {comm : p ≫ a = a' ≫ hS} (P : DescentData.PullbackFunctor a a' hS p comm)
  (D : DescentData (fun _ : Unit ↦ a))

/-- **The gluing action of the pullback of a datum along a commutative square, read in the datum
coordinate**: it is the gluing action of the datum itself, on the datum coordinate of the point
acted on and along the image under the square's top map of the acting point. -/
lemma act_comp_objIso_fst {Z : Scheme.{u}} (κ : Z ⟶ ((P.functor.obj D).obj ()).left)
    (y : Z ⟶ X') (hκ : κ ≫ ((P.functor.obj D).obj ()).hom ≫ a' = y ≫ a')
    (ν : Z ⟶ (D.obj ()).left) (x : Z ⟶ X)
    (hν : κ ≫ (P.objIso D).hom.left ≫ pullback.fst (D.obj ()).hom p = ν)
    (hx : y ≫ p = x) (hc : ν ≫ (D.obj ()).hom ≫ a = x ≫ a) :
    DescentData.act (P.functor.obj D) κ y hκ ≫
        (P.objIso D).hom.left ≫ pullback.fst (D.obj ()).hom p =
      DescentData.act D ν x hc := by
  rw [show DescentData.act (P.functor.obj D) κ y hκ =
      pullback.lift κ y hκ ≫ (P.functor.obj D).actOn from rfl, Category.assoc,
    P.actOn_objIso_fst D, ← Category.assoc, DescentData.comp_actOn]
  refine DescentData.act_congr D ?_ ?_
  · rw [Category.assoc, P.sourceMap_fst D, pullback.lift_fst_assoc]
    exact hν
  · rw [Category.assoc, P.sourceMap_snd D, pullback.lift_snd_assoc]
    exact hx

end DescentData.PullbackFunctor

namespace DescentDatum

section ChangeAct

variable {S X T : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f) (g : T ⟶ S)

/-- The comparison of the underlying scheme of the base change with the chosen base change is
the identity. -/
lemma changeOverIso_hom_left_eq_id : (D.changeOverIso g).hom.left = 𝟙 _ := rfl

/-- The datum coordinate of a point of the base change is the first projection. -/
lemma changeNu_eq_pullbackFst :
    D.changeNu g = pullback.fst D.over.hom (pullback.fst f g) :=
  Category.id_comp (pullback.fst D.over.hom (pullback.fst f g))

/-- The gluing action of the base change, read in the datum coordinate, is the gluing action of
the datum itself. -/
lemma changeDatum_actOn_comp_changeNu :
    (D.changeDatum g).actOn ≫ D.changeNu g =
      (changePullbackFunctor f g).sourceMap D ≫ D.actOn :=
  (changePullbackFunctor f g).actOn_objIso_fst D

variable {D g}

/-- The lift along the source map of the pullback functor of a point named by its coordinates. -/
lemma changePt_lift_comp_sourceMap {Z : Scheme.{u}} (ν : Z ⟶ D.over.left) (t : Z ⟶ T)
    (x : Z ⟶ X) (y : Z ⟶ pullback f g) (hyf : y ≫ pullback.fst f g = x)
    (h : ν ≫ D.over.hom ≫ f = t ≫ g) (hx : ν ≫ D.over.hom ≫ f = x ≫ f)
    (h' : D.changePt g ν t h ≫ (D.changeDatum g).over.hom ≫ pullback.snd f g =
      y ≫ pullback.snd f g) :
    pullback.lift (D.changePt g ν t h) y h' ≫ (changePullbackFunctor f g).sourceMap D =
      pullback.lift ν x hx := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, (changePullbackFunctor f g).sourceMap_fst D, pullback.lift_fst,
      pullback.lift_fst_assoc]
    exact D.changePt_comp_changeNu g ν t h
  · rw [Category.assoc, (changePullbackFunctor f g).sourceMap_snd D, pullback.lift_snd,
      pullback.lift_snd_assoc, hyf]

/-- A point of the base change whose coordinates are known is the point named by them. -/
private lemma eq_changePt_of_comp_over_hom {Z : Scheme.{u}}
    (κ : Z ⟶ (D.changeDatum g).over.left) {ν : Z ⟶ D.over.left} {y : Z ⟶ pullback f g}
    {t : Z ⟶ T} (hν : κ ≫ D.changeNu g = ν) (hy : κ ≫ (D.changeDatum g).over.hom = y)
    (ht : y ≫ pullback.snd f g = t) (h : ν ≫ D.over.hom ≫ f = t ≫ g) :
    κ = D.changePt g ν t h :=
  (D.changePt_changeNu_changeBase g κ).symm.trans
    (changePt_congr D g hν (by rw [changeBase, ← Category.assoc, hy, ht]))

/-- **The gluing action of a base-changed datum at a point named by its coordinates.** The
datum coordinate is acted on by the gluing action of the datum itself, along the first
coordinate of the acting point of `X ×_S T`, and the base coordinate is unchanged. -/
lemma changeDatum_act_changePt {Z : Scheme.{u}} (ν : Z ⟶ D.over.left) (t : Z ⟶ T)
    (x : Z ⟶ X) (y : Z ⟶ pullback f g) (hyf : y ≫ pullback.fst f g = x)
    (hys : y ≫ pullback.snd f g = t)
    (h : ν ≫ D.over.hom ≫ f = t ≫ g) (hx : ν ≫ D.over.hom ≫ f = x ≫ f)
    (h' : D.changePt g ν t h ≫ (D.changeDatum g).over.hom ≫ pullback.snd f g =
      y ≫ pullback.snd f g)
    (h₂ : DescentData.act D ν x hx ≫ D.over.hom ≫ f = t ≫ g) :
    DescentData.act (D.changeDatum g) (D.changePt g ν t h) y h' =
      D.changePt g (DescentData.act D ν x hx) t h₂ := by
  have hnu : DescentData.act (D.changeDatum g) (D.changePt g ν t h) y h' ≫ D.changeNu g =
      DescentData.act D ν x hx := by
    rw [show DescentData.act (D.changeDatum g) (D.changePt g ν t h) y h' =
        pullback.lift (D.changePt g ν t h) y h' ≫ (D.changeDatum g).actOn from rfl,
      Category.assoc, changeDatum_actOn_comp_changeNu D g, ← Category.assoc,
      changePt_lift_comp_sourceMap ν t x y hyf h hx h']
    rfl
  exact eq_changePt_of_comp_over_hom _ hnu
    (DescentData.act_hom (D.changeDatum g) (D.changePt g ν t h) y h') hys h₂

/-- **The projection of a scheme descending a base-changed datum is invariant under the gluing
action**, read at a point named by a point of the underlying scheme and a point of `X ×_S T`. -/
lemma act_comp_proj (Q : (D.changeDatum g).Descended) {Z : Scheme.{u}}
    (κ : Z ⟶ (D.changeDatum g).over.left) (y : Z ⟶ pullback f g)
    (h : κ ≫ (D.changeDatum g).over.hom ≫ pullback.snd f g = y ≫ pullback.snd f g) :
    DescentData.act (D.changeDatum g) κ y h ≫ Q.proj = κ ≫ Q.proj := by
  rw [show DescentData.act (D.changeDatum g) κ y h =
      pullback.lift κ y h ≫ (D.changeDatum g).actOn from rfl,
    show (D.changeDatum g).actOn = (D.changeDatum g).transitionPullbackIso.hom ≫
      pullback.snd (pullback.snd f g)
        ((D.changeDatum g).over.hom ≫ pullback.snd f g) from rfl]
  simp only [Category.assoc]
  rw [Q.proj_invariant, pullback.lift_fst_assoc]

/-- **The projection of a scheme descending a base-changed datum does not see the gluing action
on the datum coordinate.** -/
lemma changePt_act_comp_proj (Q : (D.changeDatum g).Descended) {Z : Scheme.{u}}
    (ν : Z ⟶ D.over.left) (t : Z ⟶ T) (x : Z ⟶ X)
    (hx : ν ≫ D.over.hom ≫ f = x ≫ f) (h : ν ≫ D.over.hom ≫ f = t ≫ g)
    (h₂ : DescentData.act D ν x hx ≫ D.over.hom ≫ f = t ≫ g) :
    D.changePt g (DescentData.act D ν x hx) t h₂ ≫ Q.proj =
      D.changePt g ν t h ≫ Q.proj := by
  have hy : (pullback.lift x t (hx.symm.trans h) : Z ⟶ pullback f g) ≫
      pullback.fst f g = x := pullback.lift_fst _ _ _
  have hy' : (pullback.lift x t (hx.symm.trans h) : Z ⟶ pullback f g) ≫
      pullback.snd f g = t := pullback.lift_snd _ _ _
  have h' : D.changePt g ν t h ≫ (D.changeDatum g).over.hom ≫ pullback.snd f g =
      pullback.lift x t (hx.symm.trans h) ≫ pullback.snd f g := by
    rw [hy']
    exact D.changePt_comp_changeBase g ν t h
  rw [← changeDatum_act_changePt ν t x _ hy hy' h hx h' h₂]
  exact act_comp_proj Q _ _ h'

end ChangeAct

/-! ### The datum relative to the composite `X ×_S T ⟶ T ⟶ S` -/

section ChangeBaseAct

variable {S X T : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f) (g : T ⟶ S)

/-- The base coordinate of a point of the base change lies over the point of `S` the point
itself lies over. -/
lemma changeBase_comp_eq :
    D.changeBase g ≫ g = (D.changeDatum g).over.hom ≫ (pullback.fst f g ≫ f) :=
  (Category.assoc _ _ _).trans
    (congrArg (fun k ↦ (D.changeDatum g).over.hom ≫ k) pullback.condition.symm)

/-- **The gluing action of the datum relative to the composite, in the datum coordinate**, is
the gluing action of the datum itself along the `X`-coordinate of the acting point. -/
lemma changeBase_act_comp_changeNu {Z : Scheme.{u}}
    (κ : Z ⟶ (D.changeDatum g).over.left) (y : Z ⟶ pullback f g)
    (hκ : κ ≫ (D.changeDatum g).over.hom ≫ (pullback.fst f g ≫ f) =
      y ≫ (pullback.fst f g ≫ f))
    (hc : (κ ≫ D.changeNu g) ≫ D.over.hom ≫ f = (y ≫ pullback.fst f g) ≫ f) :
    DescentData.act (pullbackSquareDatum (changeBasePullbackFunctor f g) D) κ y hκ ≫
        D.changeNu g =
      DescentData.act D (κ ≫ D.changeNu g) (y ≫ pullback.fst f g) hc :=
  DescentData.PullbackFunctor.act_comp_objIso_fst (changeBasePullbackFunctor f g) D κ y hκ
    (κ ≫ D.changeNu g) (y ≫ pullback.fst f g) rfl rfl hc

/-- The gluing action of the datum relative to the composite lands over the acting point. -/
lemma changeBase_act_comp_over_hom {Z : Scheme.{u}}
    (κ : Z ⟶ (D.changeDatum g).over.left) (y : Z ⟶ pullback f g)
    (hκ : κ ≫ (D.changeDatum g).over.hom ≫ (pullback.fst f g ≫ f) =
      y ≫ (pullback.fst f g ≫ f)) :
    DescentData.act (pullbackSquareDatum (changeBasePullbackFunctor f g) D) κ y hκ ≫
      (D.changeDatum g).over.hom = y :=
  DescentData.act_hom (pullbackSquareDatum (changeBasePullbackFunctor f g) D) κ y hκ

/-- The gluing action of the datum relative to the composite, at the universal point of its
source. -/
lemma changeBase_actOn_eq_act :
    (pullbackSquareDatum (changeBasePullbackFunctor f g) D).actOn =
      DescentData.act (pullbackSquareDatum (changeBasePullbackFunctor f g) D)
        (pullback.fst ((D.changeDatum g).over.hom ≫ (pullback.fst f g ≫ f))
          (pullback.fst f g ≫ f))
        (pullback.snd ((D.changeDatum g).over.hom ≫ (pullback.fst f g ≫ f))
          (pullback.fst f g ≫ f)) pullback.condition := by
  refine Eq.symm (Eq.trans (show DescentData.act
      (pullbackSquareDatum (changeBasePullbackFunctor f g) D) _ _ pullback.condition =
      pullback.lift
        (pullback.fst ((D.changeDatum g).over.hom ≫ (pullback.fst f g ≫ f))
          (pullback.fst f g ≫ f))
        (pullback.snd ((D.changeDatum g).over.hom ≫ (pullback.fst f g ≫ f))
          (pullback.fst f g ≫ f)) pullback.condition ≫
        (pullbackSquareDatum (changeBasePullbackFunctor f g) D).actOn from rfl) ?_)
  rw [pullback.lift_fst_snd]
  exact Category.id_comp _

end ChangeBaseAct

namespace Descended

section BaseFpqc

variable {S X W : Scheme.{u}} {f : X ⟶ S} [Surjective f] [IsIntegralHom f]
  {D : DescentDatum f} {w : W ⟶ S} (Q : (D.changeDatum w).Descended) [Etale Q.base.hom]
  (hff : (etaleDescentFunctor (pullback.snd f (pullback.fst w w ≫ w))).FullyFaithful)

omit [Surjective f] [IsIntegralHom f] in
/-- **A morphism out of the descended scheme which is invariant for the gluing isomorphism over
the base kills its action.** The invariance is the hypothesis `hρ`, in the shape of the
`proj_invariant` field of a scheme descending the datum relative to `w`. -/
lemma actPullback_comp_of_proj_invariant {B : Scheme.{u}} (ρ : Q.base.left ⟶ B)
    (hρ : (baseGluingPullbackIso Q hff).hom ≫ pullback.snd w (Q.base.hom ≫ w) ≫ ρ =
      pullback.fst (Q.base.hom ≫ w) w ≫ ρ)
    {Z : Scheme.{u}} (v : Z ⟶ Q.base.left) (x : Z ⟶ W)
    (h : v ≫ Q.base.hom ≫ w = x ≫ w) :
    actPullback Q.base (baseGluingPullbackIso Q hff).hom v x h ≫ ρ = v ≫ ρ := by
  rw [show actPullback Q.base (baseGluingPullbackIso Q hff).hom v x h =
      pullback.lift v x h ≫ (baseGluingPullbackIso Q hff).hom ≫
        pullback.snd w (Q.base.hom ≫ w) from rfl]
  simp only [Category.assoc]
  rw [hρ, pullback.lift_fst_assoc]

/-- **The composite projection to the scheme over `S` does not see the base coordinate.** -/
lemma changePt_comp_proj_comp {B : Scheme.{u}} (ρ : Q.base.left ⟶ B)
    (hρ : (baseGluingPullbackIso Q hff).hom ≫ pullback.snd w (Q.base.hom ≫ w) ≫ ρ =
      pullback.fst (Q.base.hom ≫ w) w ≫ ρ)
    {Z : Scheme.{u}} (ν : Z ⟶ D.over.left) (u₁ u₂ : Z ⟶ W)
    (h₁ : ν ≫ D.over.hom ≫ f = u₁ ≫ w) (h₂ : ν ≫ D.over.hom ≫ f = u₂ ≫ w) :
    D.changePt w ν u₁ h₁ ≫ Q.proj ≫ ρ = D.changePt w ν u₂ h₂ ≫ Q.proj ≫ ρ := by
  have hc : (D.changePt w ν u₁ h₁ ≫ Q.proj) ≫ Q.base.hom ≫ w = u₂ ≫ w := by
    rw [Category.assoc, D.proj_comp_base_hom_eq_changeBase_assoc w Q, ← Category.assoc,
      changePt_comp_changeBase]
    exact h₁.symm.trans h₂
  have hmv := baseGluingMovesBase Q hff ν u₁ u₂ h₁ h₂ hc
  calc D.changePt w ν u₁ h₁ ≫ Q.proj ≫ ρ
      = (D.changePt w ν u₁ h₁ ≫ Q.proj) ≫ ρ := (Category.assoc _ _ _).symm
    _ = actPullback Q.base (baseGluingPullbackIso Q hff).hom
          (D.changePt w ν u₁ h₁ ≫ Q.proj) u₂ hc ≫ ρ :=
        (actPullback_comp_of_proj_invariant Q hff ρ hρ _ u₂ hc).symm
    _ = (D.changePt w ν u₂ h₂ ≫ Q.proj) ≫ ρ := by rw [hmv]
    _ = D.changePt w ν u₂ h₂ ≫ Q.proj ≫ ρ := Category.assoc _ _ _

/-- The gluing isomorphism over the base read off the datum relative to `w`. -/
lemma baseDescentDatum_transitionPullbackIso_hom [IsSeparated Q.base.hom] :
    (baseDescentDatum Q hff).transitionPullbackIso.hom =
      (baseGluingPullbackIso Q hff).hom :=
  DescentDatum.ofPullbackIso_gluingPullbackIso_hom Q.base (baseGluingPullbackIso Q hff)
    (baseGluingPullbackIso_hom_fst Q hff) (baseGluingPullbackIso_hom_snd Q hff)
    (actPullbackLaw_baseGluingPullbackIso Q hff (baseGluingMovesBase Q hff))

/-- The invariance of the projection of a scheme descending the datum relative to `w`, read on
the gluing isomorphism over the base. -/
lemma baseDescended_proj_invariant [IsSeparated Q.base.hom]
    (R : (baseDescentDatum Q hff).Descended) :
    (baseGluingPullbackIso Q hff).hom ≫
        pullback.snd w (Q.base.hom ≫ w) ≫ (R.proj : Q.base.left ⟶ R.base.left) =
      pullback.fst (Q.base.hom ≫ w) w ≫ (R.proj : Q.base.left ⟶ R.base.left) := by
  rw [← baseDescentDatum_transitionPullbackIso_hom Q hff]
  exact R.proj_invariant

/-- **The projection of the datum relative to the composite `X ×_S W ⟶ S` is invariant under
that datum's gluing action**, at a point named by its coordinates, for any `ρ` invariant for the
gluing isomorphism over the base. -/
lemma changeBase_act_comp_proj_comp {B : Scheme.{u}} (ρ : Q.base.left ⟶ B)
    (hρ : (baseGluingPullbackIso Q hff).hom ≫ pullback.snd w (Q.base.hom ≫ w) ≫ ρ =
      pullback.fst (Q.base.hom ≫ w) w ≫ ρ)
    {Z : Scheme.{u}} (κ : Z ⟶ (D.changeDatum w).over.left) (y : Z ⟶ pullback f w)
    (hκ : κ ≫ (D.changeDatum w).over.hom ≫ (pullback.fst f w ≫ f) =
      y ≫ (pullback.fst f w ≫ f)) :
    DescentData.act (pullbackSquareDatum (changeBasePullbackFunctor f w) D) κ y hκ ≫
        Q.proj ≫ ρ = κ ≫ Q.proj ≫ ρ := by
  have hu : (κ ≫ D.changeBase w) ≫ w = y ≫ (pullback.fst f w ≫ f) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k ↦ κ ≫ k) (changeBase_comp_eq D w)).trans hκ)
  have h : (κ ≫ D.changeNu w) ≫ D.over.hom ≫ f = (κ ≫ D.changeBase w) ≫ w :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k ↦ κ ≫ k) (D.changeNu_comp w)).trans (Category.assoc _ _ _).symm)
  have hc : (κ ≫ D.changeNu w) ≫ D.over.hom ≫ f = (y ≫ pullback.fst f w) ≫ f :=
    h.trans (hu.trans (Category.assoc _ _ _).symm)
  have hu₁ : (y ≫ pullback.snd f w) ≫ w = y ≫ (pullback.fst f w ≫ f) :=
    (Category.assoc _ _ _).trans (congrArg (fun k ↦ y ≫ k) pullback.condition.symm)
  have h₁ : DescentData.act D (κ ≫ D.changeNu w) (y ≫ pullback.fst f w) hc ≫
      D.over.hom ≫ f = (y ≫ pullback.snd f w) ≫ w :=
    (Category.assoc _ _ _).symm.trans
      (((congrArg (fun k ↦ k ≫ f)
            (DescentData.act_hom D (κ ≫ D.changeNu w) (y ≫ pullback.fst f w) hc)).trans
          (Category.assoc _ _ _)).trans hu₁.symm)
  have h₂ : DescentData.act D (κ ≫ D.changeNu w) (y ≫ pullback.fst f w) hc ≫
      D.over.hom ≫ f = (κ ≫ D.changeBase w) ≫ w := h₁.trans (hu₁.trans hu.symm)
  rw [eq_changePt_of_comp_over_hom _ (changeBase_act_comp_changeNu D w κ y hκ hc)
    (changeBase_act_comp_over_hom D w κ y hκ) rfl h₁]
  conv_rhs => rw [← D.changePt_changeNu_changeBase w κ]
  calc D.changePt w (DescentData.act D (κ ≫ D.changeNu w) (y ≫ pullback.fst f w) hc)
          (y ≫ pullback.snd f w) h₁ ≫ Q.proj ≫ ρ
      = D.changePt w (DescentData.act D (κ ≫ D.changeNu w) (y ≫ pullback.fst f w) hc)
          (κ ≫ D.changeBase w) h₂ ≫ Q.proj ≫ ρ :=
        changePt_comp_proj_comp Q hff ρ hρ _ _ _ h₁ h₂
    _ = (D.changePt w (DescentData.act D (κ ≫ D.changeNu w) (y ≫ pullback.fst f w) hc)
          (κ ≫ D.changeBase w) h₂ ≫ Q.proj) ≫ ρ := (Category.assoc _ _ _).symm
    _ = (D.changePt w (κ ≫ D.changeNu w) (κ ≫ D.changeBase w) h ≫ Q.proj) ≫ ρ := by
        rw [changePt_act_comp_proj Q (κ ≫ D.changeNu w) (κ ≫ D.changeBase w)
          (y ≫ pullback.fst f w) hc h h₂]
    _ = D.changePt w (κ ≫ D.changeNu w) (κ ≫ D.changeBase w) h ≫ Q.proj ≫ ρ :=
        Category.assoc _ _ _

/-- **The scheme over `S` descending the datum relative to the composite `X ×_S W ⟶ S`.** Its
base is the scheme over `S` descending the datum relative to `w` carried by `Q.base`, and its
projection is the composite of the two projections. -/
def changeBaseDescended [IsSeparated Q.base.hom] (R : (baseDescentDatum Q hff).Descended) :
    (pullbackSquareDatum (changeBasePullbackFunctor f w) D).Descended where
  base := R.base
  proj := Q.proj ≫ (R.proj : Q.base.left ⟶ R.base.left)
  isPullback := by
    have h0 := Q.isPullback.paste_vert
      (R.isPullback : IsPullback Q.base.hom (R.proj : Q.base.left ⟶ R.base.left) w R.base.hom)
    rw [← pullback.condition] at h0
    exact h0
  proj_invariant :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k ↦ k ≫ Q.proj ≫ (R.proj : Q.base.left ⟶ R.base.left))
          (changeBase_actOn_eq_act D w)).trans
        (changeBase_act_comp_proj_comp Q hff (R.proj : Q.base.left ⟶ R.base.left)
          (baseDescended_proj_invariant Q hff R) _ _ pullback.condition))

/-- The base of `changeBaseDescended Q hff R` is the base of `R`. -/
@[simp]
lemma changeBaseDescended_base [IsSeparated Q.base.hom]
    (R : (baseDescentDatum Q hff).Descended) :
    (changeBaseDescended Q hff R).base = R.base := rfl

end BaseFpqc

end Descended

/-! ### fpqc-locality of étale effectivity in the base -/

/-- **Étale effectivity of a quasi-compact separated étale descent datum along a surjective
integral morphism is fpqc-local in the base.** If the base change of the datum along a flat
surjective quasi-compact `w : W ⟶ S` is étale effective, so is the datum itself. -/
@[sga "1 IX 4.2" "special case"]
theorem isEtaleEffective_of_isEtaleEffective_changeDatum {S X W : Scheme.{u}} (f : X ⟶ S)
    [Surjective f] [IsIntegralHom f] (w : W ⟶ S) [Flat w] [Surjective w] [QuasiCompact w]
    (D : DescentDatum f) [Etale D.over.hom] (hqc : QuasiCompact D.over.hom)
    (hsep : IsSeparated D.over.hom) (h : (D.changeDatum w).IsEtaleEffective) :
    D.IsEtaleEffective := by
  obtain ⟨Q, hQ⟩ := exists_descended_etale_of_isEtaleEffective (D.changeDatum w) h
  obtain ⟨hff⟩ :=
    Descended.nonempty_fullyFaithful_etaleDescentFunctor_baseSelfProduct f w
  have hqc' : QuasiCompact (D.changeDatum w).over.hom :=
    quasiCompact_changeDatum_over_hom D w hqc
  have hsep' : IsSeparated (D.changeDatum w).over.hom :=
    isSeparated_changeDatum_over_hom D w hsep
  have hQqc : QuasiCompact Q.base.hom := Q.quasiCompact_base_hom hqc'
  have hQsep : IsSeparated Q.base.hom := Q.isSeparated_base_hom hsep'
  obtain ⟨R, hR⟩ :=
    qcSepEtaleEffective_of_flat w (Descended.baseDescentDatum Q hff) hQ hQqc hQsep
  have hD' : Etale (pullbackSquareDatum (changeBasePullbackFunctor f w) D).over.hom :=
    property_pullbackSquare_over_hom (changeBasePullbackFunctor f w) @Etale D ‹Etale D.over.hom›
  have hbase : Etale (Descended.changeBaseDescended Q hff R).base.hom := hR
  exact isEtaleEffective_of_isEtaleEffective_changeBase f w D
    (Descended.changeBaseDescended Q hff R).isEtaleEffective

end DescentDatum

end AlgebraicGeometry

end
