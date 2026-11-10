module

public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.BaseGluing

/-!
# The cocycle condition of the gluing isomorphism over the base

Let `f : X ⟶ S` be a surjective integral morphism, `D` a descent datum relative to `X / S` with
étale underlying scheme, `w : W ⟶ S` a morphism of the base and `Q` a scheme over `W` descending
`D.changeDatum w`. `AlgebraicGeometry.DescentDatum.Descended.baseGluingPullbackIso` is the
candidate gluing isomorphism of a descent datum relative to `w` with underlying scheme `Q.base`,
compatible with the two projections by
`AlgebraicGeometry.DescentDatum.Descended.baseGluingPullbackIso_hom_fst` and
`AlgebraicGeometry.DescentDatum.Descended.baseGluingPullbackIso_hom_snd`. This file proves its
cocycle condition from one hypothesis on the gluing isomorphism: that it acts on generalized
points by *moving the base coordinate*, leaving the point of `D.over` alone.

Two things make that hypothesis the whole of the cocycle condition. The first is that a point of
`D.changeDatum g` is exactly a pair of a point of `D.over` and a point of the new base lying over
one point of `S` (`AlgebraicGeometry.DescentDatum.changePt`), so the projection of a descended
scheme becomes a function `(ν, t) ↦ ρ ν t` of two such coordinates. The second is that the
projection of a descended scheme is surjective, hence has dense range, and that `Q.base` is
unramified and separated over `W`: by
`AlgebraicGeometry.DescentDatum.actPullback_eq_of_denseRange` the action law then has to be
checked only on the pullback of the universal triple along the projection, where all three
points of `W` act on points of the form `ρ ν t`.

## Main definitions

* `AlgebraicGeometry.DescentDatum.changePt`: **the point of the base change of a descent datum
  named by a point of the datum's scheme and a point of the new base** lying over one point of
  `S`, together with `AlgebraicGeometry.DescentDatum.changeNu` and
  `AlgebraicGeometry.DescentDatum.changeBase` reading the two coordinates back off a point.
* `AlgebraicGeometry.DescentDatum.Descended.BaseGluingMovesBase`: the hypothesis that the gluing
  isomorphism acts by moving the base coordinate.
* `AlgebraicGeometry.DescentDatum.Descended.baseDatumOfMovesBase`: **the descent datum relative
  to `w` with underlying scheme `Q.base`**, built from that hypothesis.

## Main results

* `AlgebraicGeometry.DescentDatum.Descended.actPullback_baseGluingPullbackIso`: **the action of
  the candidate gluing isomorphism is the comparison of the two pullbacks of the descended
  scheme**, evaluated at the point named by the acting pair.
* `AlgebraicGeometry.DescentDatum.Descended.actPullback_fstPullbackProj`: **the gluing
  isomorphism carries the first projection of the descended scheme over `W ×_S W` to the
  second.** This is the defining property of the comparison morphism, read in the action
  formalism.
* `AlgebraicGeometry.DescentDatum.Descended.actPullbackLaw_baseGluingPullbackIso`: **the cocycle
  condition for the candidate gluing isomorphism**, from the hypothesis that it moves the base
  coordinate.

## Implementation notes

`AlgebraicGeometry.DescentDatum.Descended.actPullback_fstPullbackProj` is the defining property
of `AlgebraicGeometry.DescentDatum.Descended.baseGluingIso` transported into the action formalism,
and follows directly from
`AlgebraicGeometry.DescentDatum.Descended.proj_comp_compareOfFullyFaithful`. What it does *not*
give is the identification of its first projection with `ρ ν t` for the coordinates of
`AlgebraicGeometry.DescentDatum.changePt`: that is a computation with
`AlgebraicGeometry.DescentDatum.Descended.changeComp`, whose projection is written through
`AlgebraicGeometry.DescentDatum.changeCompDatumIso`, and it is exactly the content of
`AlgebraicGeometry.DescentDatum.Descended.BaseGluingMovesBase`.

## References

* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

namespace DescentDatum

/-! ### Generalized points of a base-changed descent datum -/

section ChangePt

variable {S X T : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f) (g : T ⟶ S)

/-- The underlying scheme of the base change of `D` along `g : T ⟶ S`, identified with the base
change of `D.over` along `X ×_S T ⟶ X`. -/
abbrev changeOverIso :
    (D.changeDatum g).over ≅ (Over.pullback (pullback.fst f g)).obj D.over :=
  (changePullbackFunctor f g).objIso D

/-- The morphism of underlying schemes of `D.changeOverIso g` is an isomorphism. -/
instance isIso_changeOverIso_hom_left : IsIso (D.changeOverIso g).hom.left := by
  change IsIso ((Over.forget (pullback f g)).map (D.changeOverIso g).hom)
  infer_instance

/-- `D.changeOverIso g` is a morphism over `X ×_S T`. -/
@[reassoc]
lemma changeOverIso_hom_left_comp_snd :
    (D.changeOverIso g).hom.left ≫ pullback.snd D.over.hom (pullback.fst f g) =
      (D.changeDatum g).over.hom :=
  Over.w (D.changeOverIso g).hom

/-- **The coordinate in the datum's own scheme of a point of the base change.** -/
def changeNu : (D.changeDatum g).over.left ⟶ D.over.left :=
  (D.changeOverIso g).hom.left ≫ pullback.fst D.over.hom (pullback.fst f g)

/-- **The coordinate in the new base of a point of the base change.** -/
def changeBase : (D.changeDatum g).over.left ⟶ T :=
  (D.changeDatum g).over.hom ≫ pullback.snd f g

/-- The coordinate `D.changeNu g` in the datum's scheme lies over the projection of a point of
the base change to `X`. -/
@[reassoc]
lemma changeNu_comp_over_hom :
    D.changeNu g ≫ D.over.hom = (D.changeDatum g).over.hom ≫ pullback.fst f g := by
  rw [changeNu, Category.assoc, pullback.condition, ← Category.assoc,
    changeOverIso_hom_left_comp_snd]

/-- **The two coordinates of a point of the base change lie over one point of `S`.** -/
@[reassoc]
lemma changeNu_comp : D.changeNu g ≫ D.over.hom ≫ f = D.changeBase g ≫ g := by
  rw [← Category.assoc, changeNu_comp_over_hom, changeBase, Category.assoc, Category.assoc,
    pullback.condition]

/-- **The point of the base change of `D` along `g` named by a point of the datum's scheme and a
point of the new base** lying over one point of `S`. -/
def changePt {Z : Scheme.{u}} (ν : Z ⟶ D.over.left) (t : Z ⟶ T)
    (h : ν ≫ D.over.hom ≫ f = t ≫ g) : Z ⟶ (D.changeDatum g).over.left :=
  pullback.lift ν (pullback.lift (ν ≫ D.over.hom) t ((Category.assoc _ _ _).trans h))
      (pullback.lift_fst _ _ _).symm ≫
    inv (D.changeOverIso g).hom.left

variable {Z : Scheme.{u}}

/-- The image of `D.changePt g ν t h` under `D.changeOverIso g` is the point of the fibre product
with coordinates `ν` and `(ν ≫ D.over.hom, t)`. -/
lemma changePt_comp_changeOverIso (ν : Z ⟶ D.over.left) (t : Z ⟶ T)
    (h : ν ≫ D.over.hom ≫ f = t ≫ g) :
    D.changePt g ν t h ≫ (D.changeOverIso g).hom.left =
      pullback.lift ν (pullback.lift (ν ≫ D.over.hom) t ((Category.assoc _ _ _).trans h))
        (pullback.lift_fst _ _ _).symm := by
  rw [changePt, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- The point `D.changePt g ν t h` lies over the point `(ν ≫ D.over.hom, t)` of `X ×_S T`. -/
@[reassoc]
lemma changePt_comp_over_hom (ν : Z ⟶ D.over.left) (t : Z ⟶ T)
    (h : ν ≫ D.over.hom ≫ f = t ≫ g) :
    D.changePt g ν t h ≫ (D.changeDatum g).over.hom =
      pullback.lift (ν ≫ D.over.hom) t ((Category.assoc _ _ _).trans h) := by
  rw [← changeOverIso_hom_left_comp_snd, ← Category.assoc, changePt_comp_changeOverIso,
    pullback.lift_snd]

/-- The coordinate in the datum's scheme of `D.changePt g ν t h` is `ν`. -/
@[reassoc (attr := simp)]
lemma changePt_comp_changeNu (ν : Z ⟶ D.over.left) (t : Z ⟶ T)
    (h : ν ≫ D.over.hom ≫ f = t ≫ g) : D.changePt g ν t h ≫ D.changeNu g = ν := by
  rw [changeNu, ← Category.assoc, changePt_comp_changeOverIso, pullback.lift_fst]

/-- The coordinate in the new base of `D.changePt g ν t h` is `t`. -/
@[reassoc (attr := simp)]
lemma changePt_comp_changeBase (ν : Z ⟶ D.over.left) (t : Z ⟶ T)
    (h : ν ≫ D.over.hom ≫ f = t ≫ g) : D.changePt g ν t h ≫ D.changeBase g = t := by
  rw [changeBase, ← Category.assoc, changePt_comp_over_hom, pullback.lift_snd]

/-- The projection of a scheme descending the base change lands over the base coordinate. -/
@[reassoc]
lemma proj_comp_base_hom_eq_changeBase (Q : (D.changeDatum g).Descended) :
    Q.proj ≫ Q.base.hom = D.changeBase g :=
  Q.proj_comp_base_hom

/-- **Every point of the base change is named by its two coordinates.** -/
lemma changePt_changeNu_changeBase (κ : Z ⟶ (D.changeDatum g).over.left) :
    D.changePt g (κ ≫ D.changeNu g) (κ ≫ D.changeBase g)
        (by rw [Category.assoc, Category.assoc, changeNu_comp]) = κ := by
  rw [← cancel_mono (D.changeOverIso g).hom.left, changePt_comp_changeOverIso]
  refine pullback.hom_ext ?_ ?_
  · rw [pullback.lift_fst, changeNu, Category.assoc]
  · rw [pullback.lift_snd]
    conv_rhs => rw [Category.assoc, changeOverIso_hom_left_comp_snd]
    refine pullback.hom_ext ?_ ?_
    · simp only [pullback.lift_fst, Category.assoc, changeNu_comp_over_hom]
    · simp only [pullback.lift_snd, changeBase, Category.assoc]

end ChangePt

namespace Descended

/-! ### The action of the candidate gluing isomorphism -/

section BaseCocycle

variable {S X W : Scheme.{u}} {f : X ⟶ S} [Surjective f] [IsIntegralHom f]
  {D : DescentDatum f} {w : W ⟶ S} (Q : (D.changeDatum w).Descended) [Etale Q.base.hom]
  (hff : (etaleDescentFunctor (pullback.snd f (pullback.fst w w ≫ w))).FullyFaithful)

variable {Z : Scheme.{u}}

/-- The point of the base change of `Q.base` along the first projection of `W ×_S W` named by a
point of `Q.base` and a second point of `W` over the same point of `S`. -/
def actLift (v : Z ⟶ Q.base.left) (x : Z ⟶ W) (h : v ≫ Q.base.hom ≫ w = x ≫ w) :
    Z ⟶ pullback Q.base.hom (pullback.fst w w) :=
  pullback.lift v (pullback.lift (v ≫ Q.base.hom) x ((Category.assoc _ _ _).trans h))
    (pullback.lift_fst _ _ _).symm

omit [Surjective f] [IsIntegralHom f] [Etale Q.base.hom] in
/-- The coordinate in `Q.base` of `actLift Q v x h` is `v`. -/
@[reassoc (attr := simp)]
lemma actLift_comp_fst (v : Z ⟶ Q.base.left) (x : Z ⟶ W)
    (h : v ≫ Q.base.hom ≫ w = x ≫ w) :
    actLift Q v x h ≫ pullback.fst Q.base.hom (pullback.fst w w) = v :=
  pullback.lift_fst _ _ _

omit [Surjective f] [IsIntegralHom f] [Etale Q.base.hom] in
/-- The coordinate in `W ×_S W` of `actLift Q v x h` is the pair `(v ≫ Q.base.hom, x)`. -/
@[reassoc]
lemma actLift_comp_snd (v : Z ⟶ Q.base.left) (x : Z ⟶ W)
    (h : v ≫ Q.base.hom ≫ w = x ≫ w) :
    actLift Q v x h ≫ pullback.snd Q.base.hom (pullback.fst w w) =
      pullback.lift (v ≫ Q.base.hom) x ((Category.assoc _ _ _).trans h) :=
  pullback.lift_snd _ _ _

omit [Surjective f] [IsIntegralHom f] in
/-- **The action of the candidate gluing isomorphism is the comparison of the two pullbacks of
the descended scheme**, evaluated at the point named by the acting pair. -/
lemma actPullback_baseGluingPullbackIso (v : Z ⟶ Q.base.left) (x : Z ⟶ W)
    (h : v ≫ Q.base.hom ≫ w = x ≫ w) :
    actPullback Q.base (baseGluingPullbackIso Q hff).hom v x h =
      actLift Q v x h ≫ (baseGluingIso Q hff).hom.left ≫
        pullback.fst Q.base.hom (pullback.snd w w) := by
  have hL : pullback.lift v x h ≫ (pullbackRightPullbackFstIso w w Q.base.hom).inv =
      actLift Q v x h := by
    refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_)
    · simp only [Category.assoc, pullbackRightPullbackFstIso_inv_fst, pullback.lift_fst,
        actLift_comp_fst]
    · simp only [Category.assoc, pullbackRightPullbackFstIso_inv_snd_fst, actLift_comp_snd,
        pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd, actLift_comp_snd,
        pullback.lift_snd]
  rw [actPullback, baseGluingPullbackIso, DescentDatum.pullbackIsoOfBaseChangeIso_hom]
  simp only [Category.assoc]
  rw [← Category.assoc (pullback.lift v x h) (pullbackRightPullbackFstIso w w Q.base.hom).inv,
    hL, DescentDatum.sndProjPastingIso_hom_snd]

/-- The projection of the first pullback of the descended scheme to `W ×_S W`, with its target
written as a literal fibre product. -/
def fstPullbackProj : (D.changeDatum (pullback.fst w w ≫ w)).over.left ⟶
    pullback Q.base.hom (pullback.fst w w) :=
  (fstPullbackDescended Q).proj

/-- The projection of the second pullback of the descended scheme to `W ×_S W`, with its target
written as a literal fibre product. -/
def sndPullbackProj : (D.changeDatum (pullback.fst w w ≫ w)).over.left ⟶
    pullback Q.base.hom (pullback.snd w w) :=
  (sndPullbackDescended Q).proj

omit [Surjective f] [IsIntegralHom f] [Etale Q.base.hom] in
/-- The coordinate in `W ×_S W` of `fstPullbackProj Q` is the base coordinate of the base
change of `D`. -/
@[reassoc]
lemma fstPullbackProj_comp_snd :
    fstPullbackProj Q ≫ pullback.snd Q.base.hom (pullback.fst w w) =
      D.changeBase (pullback.fst w w ≫ w) :=
  (fstPullbackDescended Q).proj_comp_base_hom

omit [Surjective f] [IsIntegralHom f] [Etale Q.base.hom] in
/-- The coordinate in `W ×_S W` of `sndPullbackProj Q` is the base coordinate of the base
change of `D`. -/
@[reassoc]
lemma sndPullbackProj_comp_snd :
    sndPullbackProj Q ≫ pullback.snd Q.base.hom (pullback.snd w w) =
      D.changeBase (pullback.fst w w ≫ w) :=
  (sndPullbackDescended Q).proj_comp_base_hom

omit [Surjective f] [IsIntegralHom f] in
/-- **The gluing isomorphism carries the projection of the first pullback of the descended
scheme to that of the second.** -/
lemma fstPullbackProj_comp_baseGluingIso :
    fstPullbackProj Q ≫ (baseGluingIso Q hff).hom.left = sndPullbackProj Q :=
  proj_comp_compareOfFullyFaithful hff (fstPullbackDescended Q) (sndPullbackDescended Q)

omit [Surjective f] [IsIntegralHom f] in
/-- **The gluing isomorphism acts on the projection of the first pullback of the descended
scheme and produces that of the second.** This is
`AlgebraicGeometry.DescentDatum.Descended.fstPullbackProj_comp_baseGluingIso` read in the action
formalism: the second universal point of `W` moves the first projection to the second. -/
lemma actPullback_fstPullbackProj
    (Λ : Z ⟶ (D.changeDatum (pullback.fst w w ≫ w)).over.left)
    (h : (Λ ≫ fstPullbackProj Q ≫ pullback.fst Q.base.hom (pullback.fst w w)) ≫
        Q.base.hom ≫ w =
      (Λ ≫ D.changeBase (pullback.fst w w ≫ w) ≫ pullback.snd w w) ≫ w) :
    actPullback Q.base (baseGluingPullbackIso Q hff).hom
        (Λ ≫ fstPullbackProj Q ≫ pullback.fst Q.base.hom (pullback.fst w w))
        (Λ ≫ D.changeBase (pullback.fst w w ≫ w) ≫ pullback.snd w w) h =
      Λ ≫ sndPullbackProj Q ≫ pullback.fst Q.base.hom (pullback.snd w w) := by
  have hlift : actLift Q (Λ ≫ fstPullbackProj Q ≫ pullback.fst Q.base.hom (pullback.fst w w))
      (Λ ≫ D.changeBase (pullback.fst w w ≫ w) ≫ pullback.snd w w) h =
      Λ ≫ fstPullbackProj Q := by
    refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_)
    · simp only [actLift_comp_fst, Category.assoc]
    · simp only [actLift_comp_snd, pullback.lift_fst, Category.assoc,
        pullback.condition (f := Q.base.hom) (g := pullback.fst w w),
        fstPullbackProj_comp_snd_assoc]
    · simp only [actLift_comp_snd, pullback.lift_snd, Category.assoc,
        fstPullbackProj_comp_snd_assoc]
  rw [actPullback_baseGluingPullbackIso Q hff, hlift, Category.assoc,
    ← Category.assoc (fstPullbackProj Q), fstPullbackProj_comp_baseGluingIso Q hff]

/-! ### The cocycle condition -/

/-- **The gluing isomorphism acts by moving the base coordinate.** A point of the base change of
`D` along `w` is a pair of a point `ν` of the datum's scheme and a point `u` of `W` over one
point of `S` (`AlgebraicGeometry.DescentDatum.changePt`); this says that the second point of `W`
acts on the projection of such a pair by replacing `u`, leaving `ν` alone. -/
def BaseGluingMovesBase : Prop :=
  ∀ {Z : Scheme.{u}} (ν : Z ⟶ D.over.left) (u₁ u₂ : Z ⟶ W)
    (h₁ : ν ≫ D.over.hom ≫ f = u₁ ≫ w) (h₂ : ν ≫ D.over.hom ≫ f = u₂ ≫ w)
    (hc : (D.changePt w ν u₁ h₁ ≫ Q.proj) ≫ Q.base.hom ≫ w = u₂ ≫ w),
      actPullback Q.base (baseGluingPullbackIso Q hff).hom
          (D.changePt w ν u₁ h₁ ≫ Q.proj) u₂ hc =
        D.changePt w ν u₂ h₂ ≫ Q.proj

omit [Surjective f] [IsIntegralHom f] in
/-- **The action law for a triple whose point of the descended scheme is the projection of a
point of the base change.** -/
lemma actPullback_act_act_of_movesBase (H : BaseGluingMovesBase Q hff)
    (ν : Z ⟶ D.over.left) (v : Z ⟶ Q.base.left) (u₁ x y : Z ⟶ W)
    (h₁ : ν ≫ D.over.hom ≫ f = u₁ ≫ w)
    (hv₀ : D.changePt w ν u₁ h₁ ≫ Q.proj = v)
    (hx : ν ≫ D.over.hom ≫ f = x ≫ w) (hy : ν ≫ D.over.hom ≫ f = y ≫ w)
    (hv : v ≫ Q.base.hom ≫ w = x ≫ w)
    (hvx : actPullback Q.base (baseGluingPullbackIso Q hff).hom v x hv ≫ Q.base.hom ≫ w =
      y ≫ w)
    (hvy : v ≫ Q.base.hom ≫ w = y ≫ w) :
    actPullback Q.base (baseGluingPullbackIso Q hff).hom
        (actPullback Q.base (baseGluingPullbackIso Q hff).hom v x hv) y hvx =
      actPullback Q.base (baseGluingPullbackIso Q hff).hom v y hvy := by
  have hbh : ∀ {Z' : Scheme.{u}} (ν' : Z' ⟶ D.over.left) (t : Z' ⟶ W)
      (ht : ν' ≫ D.over.hom ≫ f = t ≫ w),
      (D.changePt w ν' t ht ≫ Q.proj) ≫ Q.base.hom ≫ w = t ≫ w := by
    intro Z' ν' t ht
    rw [Category.assoc, D.proj_comp_base_hom_eq_changeBase_assoc w Q, ← Category.assoc,
      changePt_comp_changeBase]
  have hbh' : (D.changePt w ν x hx ≫ Q.proj) ≫ Q.base.hom ≫ w = y ≫ w :=
    (hbh ν x hx).trans (hx.symm.trans hy)
  subst hv₀
  refine (actPullback_congr Q.base _ (H ν u₁ x h₁ hx hv) rfl hvx hbh').trans ?_
  exact (H ν x y hx hy hbh').trans (H ν u₁ y h₁ hy hvy).symm

omit [IsIntegralHom f] in
/-- **The cocycle condition for the candidate gluing isomorphism**, from the hypothesis that it
moves the base coordinate. -/
theorem actPullbackLaw_baseGluingPullbackIso [IsSeparated Q.base.hom]
    (H : BaseGluingMovesBase Q hff) :
    ActPullbackLaw Q.base (baseGluingPullbackIso Q hff).hom := by
  have hι := baseGluingPullbackIso_hom_snd Q hff
  apply actPullbackLaw_of_universal Q.base _ hι
  have hdense := (Surjective.surj
    (f := pullback.snd Q.proj (tripleV Q.base (f := w)))).denseRange
  have hcoord : pullback.fst Q.proj (tripleV Q.base (f := w)) ≫ D.changeBase w =
      pullback.snd Q.proj (tripleV Q.base (f := w)) ≫ tripleV Q.base (f := w) ≫
        Q.base.hom := by
    rw [← D.proj_comp_base_hom_eq_changeBase w Q, ← Category.assoc,
      pullback.condition (f := Q.proj) (g := tripleV Q.base (f := w)), Category.assoc]
  have hν : pullback.fst Q.proj (tripleV Q.base (f := w)) ≫ D.changeNu w ≫
      D.over.hom ≫ f = pullback.snd Q.proj (tripleV Q.base (f := w)) ≫
        tripleV Q.base (f := w) ≫ Q.base.hom ≫ w := by
    rw [D.changeNu_comp w, ← Category.assoc, hcoord, Category.assoc, Category.assoc]
  have hv : (pullback.snd Q.proj (tripleV Q.base (f := w)) ≫ tripleV Q.base (f := w)) ≫
      Q.base.hom ≫ w =
      (pullback.snd Q.proj (tripleV Q.base (f := w)) ≫ tripleX Q.base (f := w)) ≫ w := by
    rw [Category.assoc, Category.assoc, tripleV_comp]
  have hw' : (pullback.snd Q.proj (tripleV Q.base (f := w)) ≫ tripleX Q.base (f := w)) ≫ w =
      (pullback.snd Q.proj (tripleV Q.base (f := w)) ≫ tripleY Q.base (f := w)) ≫ w := by
    rw [Category.assoc, Category.assoc, tripleX_comp]
  have hvy : (pullback.snd Q.proj (tripleV Q.base (f := w)) ≫ tripleV Q.base (f := w)) ≫
      Q.base.hom ≫ w =
      (pullback.snd Q.proj (tripleV Q.base (f := w)) ≫ tripleY Q.base (f := w)) ≫ w :=
    hv.trans hw'
  have hvx := actPullback_comp_hom_comp Q.base (baseGluingPullbackIso Q hff).hom hι
    (pullback.snd Q.proj (tripleV Q.base (f := w)) ≫ tripleV Q.base (f := w))
    (pullback.snd Q.proj (tripleV Q.base (f := w)) ≫ tripleX Q.base (f := w))
    (pullback.snd Q.proj (tripleV Q.base (f := w)) ≫ tripleY Q.base (f := w)) hv hw'
  refine actPullback_eq_of_denseRange Q.base _ hι (tripleV Q.base (f := w))
    (tripleX Q.base (f := w)) (tripleY Q.base (f := w)) (tripleV_comp Q.base)
    (tripleX_comp Q.base) _ (pullback.snd Q.proj (tripleV Q.base (f := w))) hdense ?_
  refine comp_actPullback_act_act Q.base _ (pullback.snd Q.proj (tripleV Q.base (f := w)))
    (tripleV Q.base (f := w)) (tripleX Q.base (f := w)) (tripleY Q.base (f := w))
    (tripleV_comp Q.base) (tripleX_comp Q.base) _ hv hw' hvx ?_
  refine actPullback_act_act_of_movesBase Q hff H
    (pullback.fst Q.proj (tripleV Q.base (f := w)) ≫ D.changeNu w) _
    (pullback.fst Q.proj (tripleV Q.base (f := w)) ≫ D.changeBase w) _ _
    (by rw [Category.assoc, D.changeNu_comp w, Category.assoc]) ?_ ?_ ?_ hv hvx hvy
  · rw [D.changePt_changeNu_changeBase w (pullback.fst Q.proj (tripleV Q.base (f := w)))]
    exact pullback.condition
  · rw [Category.assoc, hν, Category.assoc, tripleV_comp]
  · rw [Category.assoc, hν, Category.assoc, tripleV_comp, tripleX_comp]

/-- **The descent datum relative to `w` with underlying scheme the descended scheme**, built
from the hypothesis that the gluing isomorphism moves the base coordinate. -/
def baseDatumOfMovesBase [IsSeparated Q.base.hom] (H : BaseGluingMovesBase Q hff) :
    DescentDatum w :=
  DescentDatum.ofPullbackIso Q.base (baseGluingPullbackIso Q hff)
    (baseGluingPullbackIso_hom_fst Q hff) (baseGluingPullbackIso_hom_snd Q hff)
    (actPullbackLaw_baseGluingPullbackIso Q hff H)

end BaseCocycle

end Descended

end DescentDatum

end AlgebraicGeometry

end
