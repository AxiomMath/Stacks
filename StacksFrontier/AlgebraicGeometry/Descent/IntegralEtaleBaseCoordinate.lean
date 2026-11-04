module

public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.BaseCocycle

/-!
# The gluing isomorphism over the base moves the base coordinate

Let `f : X ⟶ S` be a surjective integral morphism, `D` a descent datum relative to `X / S` with
étale underlying scheme, `w : W ⟶ S` a morphism of the base and `Q` a scheme over `W` descending
the base change `D.changeDatum w`. `AlgebraicGeometry.DescentDatum.Descended.baseDatumOfMovesBase`
turns `Q.base` into a descent datum relative to `w`, but only after
`AlgebraicGeometry.DescentDatum.Descended.BaseGluingMovesBase`: the hypothesis that the candidate
gluing isomorphism `AlgebraicGeometry.DescentDatum.Descended.baseGluingPullbackIso` acts on
generalized points by moving the coordinate in `W` and leaving the coordinate in `D.over` alone.
This file proves that hypothesis, so the descent datum relative to `w` is unconditional
(`AlgebraicGeometry.DescentDatum.Descended.baseDescentDatum`).

The content is a computation with the comparison of the two base changes of `D` to `W ×_S W`:
the iterated one, obtained by restricting `D.changeDatum w` along a projection, and the direct
one along the composite `W ×_S W ⟶ W ⟶ S`. That comparison
(`AlgebraicGeometry.DescentDatum.changeCompDatumIso`) is a composite of two factorisation
isomorphisms with the comparison of two morphisms completing one square, and the middle factor is
the gluing action of `D` along the two ways of projecting `(X ×_S W) ×_W (W ×_S W)` to `X`. Those
two projections are *equal*, so the action is trivial and the whole comparison is the identity on
the coordinate in `D.over` — which is exactly what makes the gluing isomorphism move only the
base coordinate.

## Main definitions

* `AlgebraicGeometry.DescentDatum.changeCompNu`: **the coordinate in `D.over` of the comparison
  of the iterated and the direct base change.**
* `AlgebraicGeometry.DescentDatum.Descended.baseDescentDatum`: **the descent datum relative to
  `w` with underlying scheme `Q.base`**, with no hypothesis beyond separatedness of `Q.base` over
  `W`.

## Main results

* `AlgebraicGeometry.DescentDatum.changeCompNu_comp_changeNu` and
  `...changeCompNu_comp_changeBase`: the comparison leaves the coordinate in `D.over` alone and
  pushes the coordinate in the base down along the projection.
* `AlgebraicGeometry.DescentDatum.changePt_comp_changeCompNu`: the same, read at a point named by
  its two coordinates.
* `AlgebraicGeometry.DescentDatum.Descended.changeComp_proj_comp_fst`: the first component of the
  projection of a base-changed descended scheme is the comparison followed by the original
  projection.
* `AlgebraicGeometry.DescentDatum.Descended.baseGluingMovesBase`: **the gluing isomorphism over
  the base moves the base coordinate.**

## Implementation notes

`AlgebraicGeometry.DescentDatum.baseChangeAct_eq_fst_of_eq` is the one place where the gluing
isomorphism of `D` is used, and it is used only to say that acting along a map by itself does
nothing; it is stated for two morphisms and an equality between them rather than for one
morphism, because the two morphisms occur inside the types of the two pullback functors being
compared and so cannot be identified by rewriting.

The three factors of the comparison are each read off on the coordinate in `D.over` separately,
and the first and the third are the two instances of
`AlgebraicGeometry.DescentData.factorizationObjIso_hom_left_fst`; the comparison
`AlgebraicGeometry.DescentDatum.changeCompDatumIso` is literally that composite, which
`AlgebraicGeometry.DescentDatum.changeCompDatumIso_hom_hom` records.

## References

* [Stacks Project, Tag 023Y](https://stacks.math.columbia.edu/tag/023Y)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

namespace DescentDatum

variable {S X T T' : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f) (g : T ⟶ S) (g' : T' ⟶ T)

/-- The comparison of the iterated and the direct base change, on underlying schemes. -/
lemma changeCompDatumIso_hom_hom :
    ((changeCompDatumIso g g' D).hom.hom ()) =
      (DescentData.factorizationObjIso (changeCompDirectFunctor f g g')
          (changePullbackFunctor f (g' ≫ g)) (changeCompFunctor f g g') D).hom ≫
        (DescentData.baseChangeObjIso (changeCompDirectFunctor f g g')
            (changeCompIterFunctor f g g') D).hom ≫
          (DescentData.factorizationObjIso (changeCompIterFunctor f g g')
            (changePullbackFunctor f g) (changePullbackFunctor (pullback.snd f g) g') D).inv :=
  rfl

/-- **The datum coordinate of the comparison of the iterated and the direct base change.** -/
def changeCompNu : (D.changeDatum (g' ≫ g)).over.left ⟶ (D.changeDatum g).over.left :=
  inv (Descended.squareOver (changeCompFunctor f g g') (D.changeDatum (g' ≫ g))) ≫
    ((changeCompDatumIso g g' D).hom.hom ()).left ≫ (D.changeDatum g).changeNu g'

/-- The two factorisations of the horizontal arrow agree. -/
lemma changeComp_arrow_eq :
    (changeCompIso f g g').hom ≫ pullback.fst f (g' ≫ g) =
      pullback.fst (pullback.snd f g) g' ≫ pullback.fst f g :=
  pullbackLeftPullbackSndIso_hom_fst f g g'

/-- **The gluing action along two equal maps is trivial.** -/
lemma baseChangeAct_eq_fst_of_eq {X' : Scheme.{u}} (f₀ f₁ : X' ⟶ X) (he : f₀ = f₁)
    (hf : f₀ ≫ f = f₁ ≫ f) :
    D.baseChangeAct f₀ f₁ hf = pullback.fst D.over.hom f₀ := by
  subst he
  rw [DescentData.baseChangeAct]
  exact (DescentData.act_congr D rfl pullback.condition.symm).trans
    (DescentData.act_self D _)

/-- The third factor of the comparison, read on the datum coordinate. -/
lemma factorizationObjIso_inv_left_changeNu :
    (DescentData.factorizationObjIso (changeCompIterFunctor f g g')
          (changePullbackFunctor f g) (changePullbackFunctor (pullback.snd f g) g') D).inv.left ≫
        (D.changeDatum g).changeNu g' ≫ D.changeNu g =
      ((changeCompIterFunctor f g g').objIso D).hom.left ≫
        pullback.fst D.over.hom
          (pullback.fst (pullback.snd f g) g' ≫ pullback.fst f g) := by
  rw [show (D.changeDatum g).changeNu g' ≫ D.changeNu g =
      ((changePullbackFunctor (pullback.snd f g) g').objIso (D.changeDatum g)).hom.left ≫
        pullback.fst (D.changeDatum g).over.hom (pullback.fst (pullback.snd f g) g') ≫
          ((changePullbackFunctor f g).objIso D).hom.left ≫
            pullback.fst D.over.hom (pullback.fst f g) by
    simp only [changeNu, changeOverIso, Category.assoc],
    ← DescentData.factorizationObjIso_hom_left_fst (changeCompIterFunctor f g g')
      (changePullbackFunctor f g) (changePullbackFunctor (pullback.snd f g) g') D, ← Category.assoc,
    ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.id_comp]

/-- The middle factor of the comparison, read on the datum coordinate. -/
lemma baseChangeObjIso_hom_left_changeComp :
    (DescentData.baseChangeObjIso (changeCompDirectFunctor f g g')
          (changeCompIterFunctor f g g') D).hom.left ≫
        ((changeCompIterFunctor f g g').objIso D).hom.left ≫
          pullback.fst D.over.hom
            (pullback.fst (pullback.snd f g) g' ≫ pullback.fst f g) =
      ((changeCompDirectFunctor f g g').objIso D).hom.left ≫
        pullback.fst D.over.hom
          ((changeCompIso f g g').hom ≫ pullback.fst f (g' ≫ g)) := by
  rw [DescentData.baseChangeObjIso_hom_left_objIso_assoc, DescentData.baseChangeMap_left_fst]
  congr 1
  exact D.baseChangeAct_eq_fst_of_eq _ _ (changeComp_arrow_eq (f := f) g g') _

/-- The first factor of the comparison, read on the datum coordinate. -/
lemma factorizationObjIso_hom_left_changeComp :
    (DescentData.factorizationObjIso (changeCompDirectFunctor f g g')
          (changePullbackFunctor f (g' ≫ g)) (changeCompFunctor f g g') D).hom.left ≫
        ((changeCompDirectFunctor f g g').objIso D).hom.left ≫
          pullback.fst D.over.hom
            ((changeCompIso f g g').hom ≫ pullback.fst f (g' ≫ g)) =
      Descended.squareOver (changeCompFunctor f g g') (D.changeDatum (g' ≫ g)) ≫
        D.changeNu (g' ≫ g) := by
  rw [DescentData.factorizationObjIso_hom_left_fst (changeCompDirectFunctor f g g')
    (changePullbackFunctor f (g' ≫ g)) (changeCompFunctor f g g') D]
  simp only [Descended.squareOver, changeNu, changeOverIso, Category.assoc]

/-- **The datum coordinate of the comparison is the datum coordinate.** -/
lemma changeCompNu_comp_changeNu :
    D.changeCompNu g g' ≫ D.changeNu g = D.changeNu (g' ≫ g) := by
  rw [changeCompNu, changeCompDatumIso_hom_hom]
  simp only [Over.comp_left, Category.assoc]
  rw [factorizationObjIso_inv_left_changeNu D g g',
    baseChangeObjIso_hom_left_changeComp D g g',
    factorizationObjIso_hom_left_changeComp D g g', ← Category.assoc,
    IsIso.inv_hom_id, Category.id_comp]

/-- **The base coordinate of the comparison is the base coordinate, pushed down along `g'`.** -/
lemma changeCompNu_comp_changeBase :
    D.changeCompNu g g' ≫ D.changeBase g = D.changeBase (g' ≫ g) ≫ g' := by
  rw [changeCompNu, changeBase]
  simp only [Category.assoc]
  rw [changeNu_comp_over_hom_assoc, Over.w_assoc, ← Category.assoc,
    Descended.inv_squareOver_comp_over_hom (comm := changeCompIso_hom_comp_snd f g g'),
    IsIso.Iso.inv_hom, pullback.condition (f := pullback.snd f g) (g := g')]
  simp only [Category.assoc]
  rw [← Category.assoc (changeCompIso f g g').inv, changeCompIso_inv_comp_snd]
  simp [changeBase]

/-- Transport of a point of a base-changed datum along equalities of its two coordinates. -/
lemma changePt_congr {Z : Scheme.{u}} {ν ν' : Z ⟶ D.over.left} {t t' : Z ⟶ T}
    (hν : ν = ν') (ht : t = t')
    {h : ν ≫ D.over.hom ≫ f = t ≫ g} {h' : ν' ≫ D.over.hom ≫ f = t' ≫ g} :
    D.changePt g ν t h = D.changePt g ν' t' h' := by
  subst hν ht
  rfl

/-- **The comparison of the iterated and the direct base change pushes the base coordinate down
along `g'` and leaves the datum coordinate alone.** -/
lemma changePt_comp_changeCompNu {Z : Scheme.{u}} (ν : Z ⟶ D.over.left) (t : Z ⟶ T')
    (h : ν ≫ D.over.hom ≫ f = t ≫ (g' ≫ g)) :
    D.changePt (g' ≫ g) ν t h ≫ D.changeCompNu g g' =
      D.changePt g ν (t ≫ g') (by rw [h, Category.assoc]) :=
  (D.changePt_changeNu_changeBase g
      (D.changePt (g' ≫ g) ν t h ≫ D.changeCompNu g g')).symm.trans
    (changePt_congr D g
      (by rw [Category.assoc, changeCompNu_comp_changeNu, changePt_comp_changeNu])
      (by rw [Category.assoc, changeCompNu_comp_changeBase, ← Category.assoc,
        changePt_comp_changeBase]))

namespace Descended

variable {D} {g}

/-- **The first component of the projection of a base-changed descended scheme** is the
comparison of the two base changes followed by the original projection. -/
lemma changeComp_proj_comp_fst (Q : (D.changeDatum g).Descended) (g' : T' ⟶ T) :
    (Q.changeComp g').proj ≫ pullback.fst Q.base.hom g' = D.changeCompNu g g' ≫ Q.proj := by
  have h1 : pullbackSquareProj (changePullbackFunctor (pullback.snd f g) g') Q ≫
      pullback.fst Q.base.hom g' = (D.changeDatum g).changeNu g' ≫ Q.proj := by
    rw [pullbackSquareProj_comp_fst]
    simp only [changeNu, changeOverIso, Category.assoc]
  calc (Q.changeComp g').proj ≫ pullback.fst Q.base.hom g'
      = (inv (squareOver (changeCompFunctor f g g') (D.changeDatum (g' ≫ g))) ≫
          ((changeCompDatumIso g g' D).hom.hom ()).left ≫
            pullbackSquareProj (changePullbackFunctor (pullback.snd f g) g') Q) ≫
          pullback.fst Q.base.hom g' := rfl
    _ = D.changeCompNu g g' ≫ Q.proj := by
        rw [changeCompNu]
        simp only [Category.assoc, h1]

/-- **The projection of a descended scheme transported along an equality of base morphisms**,
read at a point named by its two coordinates. -/
lemma changePt_comp_changeCongr_proj {g₁ g₂ : T ⟶ S} (hg : g₁ = g₂)
    (Q : (D.changeDatum g₁).Descended) {B : Scheme.{u}} (k : Q.base.left ⟶ B)
    {Z : Scheme.{u}} (ν : Z ⟶ D.over.left) (t : Z ⟶ T)
    (h₂ : ν ≫ D.over.hom ≫ f = t ≫ g₂) (h₁ : ν ≫ D.over.hom ≫ f = t ≫ g₁) :
    D.changePt g₂ ν t h₂ ≫ (changeCongr hg Q).proj ≫ k =
      D.changePt g₁ ν t h₁ ≫ Q.proj ≫ k := by
  subst hg
  rfl

section BaseGluing

variable {W : Scheme.{u}} [Surjective f] [IsIntegralHom f] {w : W ⟶ S}
  (Q : (D.changeDatum w).Descended) [Etale Q.base.hom]
  (hff : (etaleDescentFunctor (pullback.snd f (pullback.fst w w ≫ w))).FullyFaithful)

omit [Surjective f] [IsIntegralHom f] [Etale Q.base.hom] in
/-- The first projection of the descended scheme over `W ×_S W`, at a point named by its
coordinates. -/
lemma fstPullbackProj_comp_fst_changePt {Z : Scheme.{u}} (ν : Z ⟶ D.over.left)
    (m : Z ⟶ pullback w w) (h : ν ≫ D.over.hom ≫ f = m ≫ (pullback.fst w w ≫ w)) :
    D.changePt (pullback.fst w w ≫ w) ν m h ≫
        fstPullbackProj Q ≫ pullback.fst Q.base.hom (pullback.fst w w) =
      D.changePt w ν (m ≫ pullback.fst w w) (by rw [h, Category.assoc]) ≫ Q.proj := by
  rw [show fstPullbackProj Q ≫ pullback.fst Q.base.hom (pullback.fst w w) =
      D.changeCompNu w (pullback.fst w w) ≫ Q.proj from
      changeComp_proj_comp_fst Q (pullback.fst w w),
    ← Category.assoc, changePt_comp_changeCompNu]

omit [Surjective f] [IsIntegralHom f] [Etale Q.base.hom] in
/-- The second projection of the descended scheme over `W ×_S W`, at a point named by its
coordinates. -/
lemma sndPullbackProj_comp_fst_changePt {Z : Scheme.{u}} (ν : Z ⟶ D.over.left)
    (m : Z ⟶ pullback w w) (h : ν ≫ D.over.hom ≫ f = m ≫ (pullback.fst w w ≫ w))
    (h' : ν ≫ D.over.hom ≫ f = m ≫ (pullback.snd w w ≫ w)) :
    D.changePt (pullback.fst w w ≫ w) ν m h ≫
        sndPullbackProj Q ≫ pullback.fst Q.base.hom (pullback.snd w w) =
      D.changePt w ν (m ≫ pullback.snd w w) (by rw [h', Category.assoc]) ≫ Q.proj := by
  have e1 : D.changePt (pullback.fst w w ≫ w) ν m h ≫
      sndPullbackProj Q ≫ pullback.fst Q.base.hom (pullback.snd w w) =
      D.changePt (pullback.snd w w ≫ w) ν m h' ≫
        (Q.changeComp (pullback.snd w w)).proj ≫
          pullback.fst Q.base.hom (pullback.snd w w) :=
    changePt_comp_changeCongr_proj pullback.condition.symm (Q.changeComp (pullback.snd w w))
      (pullback.fst Q.base.hom (pullback.snd w w)) ν m h h'
  rw [e1, changeComp_proj_comp_fst, ← Category.assoc, changePt_comp_changeCompNu]

/-- **The gluing isomorphism over the base moves the base coordinate.** This is the hypothesis
of `AlgebraicGeometry.DescentDatum.Descended.baseDatumOfMovesBase`, discharged. -/
theorem baseGluingMovesBase : BaseGluingMovesBase Q hff := by
  intro Z ν u₁ u₂ h₁ h₂ hc
  set m : Z ⟶ pullback w w := pullback.lift u₁ u₂ (h₁.symm.trans h₂)
  have hm1 : m ≫ pullback.fst w w = u₁ := pullback.lift_fst _ _ _
  have hm2 : m ≫ pullback.snd w w = u₂ := pullback.lift_snd _ _ _
  have hmc : ν ≫ D.over.hom ≫ f = m ≫ (pullback.fst w w ≫ w) := by
    rwa [← Category.assoc m, hm1]
  have hmc' : ν ≫ D.over.hom ≫ f = m ≫ (pullback.snd w w ≫ w) := by
    rwa [← Category.assoc m, hm2]
  have hfst : D.changePt (pullback.fst w w ≫ w) ν m hmc ≫
      fstPullbackProj Q ≫ pullback.fst Q.base.hom (pullback.fst w w) =
      D.changePt w ν u₁ h₁ ≫ Q.proj := by
    rw [fstPullbackProj_comp_fst_changePt Q ν m hmc]
    exact congrArg (· ≫ Q.proj) (changePt_congr D w rfl hm1)
  have hsnd : D.changePt (pullback.fst w w ≫ w) ν m hmc ≫
      sndPullbackProj Q ≫ pullback.fst Q.base.hom (pullback.snd w w) =
      D.changePt w ν u₂ h₂ ≫ Q.proj := by
    rw [sndPullbackProj_comp_fst_changePt Q ν m hmc hmc']
    exact congrArg (· ≫ Q.proj) (changePt_congr D w rfl hm2)
  have hbase : D.changePt (pullback.fst w w ≫ w) ν m hmc ≫
      D.changeBase (pullback.fst w w ≫ w) ≫ pullback.snd w w = u₂ := by
    rw [← Category.assoc, changePt_comp_changeBase, hm2]
  have hh : (D.changePt (pullback.fst w w ≫ w) ν m hmc ≫
        fstPullbackProj Q ≫ pullback.fst Q.base.hom (pullback.fst w w)) ≫ Q.base.hom ≫ w =
      (D.changePt (pullback.fst w w ≫ w) ν m hmc ≫
        D.changeBase (pullback.fst w w ≫ w) ≫ pullback.snd w w) ≫ w := by
    rwa [hfst, hbase]
  exact (actPullback_congr Q.base (baseGluingPullbackIso Q hff).hom hfst.symm hbase.symm hc
    hh).trans ((actPullback_fstPullbackProj Q hff
      (D.changePt (pullback.fst w w ≫ w) ν m hmc) hh).trans hsnd)

/-- **The descent datum relative to `w` with underlying scheme `Q.base`.** This is
`AlgebraicGeometry.DescentDatum.Descended.baseDatumOfMovesBase` with its hypothesis
discharged. -/
def baseDescentDatum [IsSeparated Q.base.hom] : DescentDatum w :=
  baseDatumOfMovesBase Q hff (baseGluingMovesBase Q hff)

/-- The underlying scheme over `W` of `baseDescentDatum Q hff` is `Q.base`. -/
@[simp]
lemma baseDescentDatum_over [IsSeparated Q.base.hom] :
    (baseDescentDatum Q hff).over = Q.base :=
  rfl

end BaseGluing

end Descended

end DescentDatum

end AlgebraicGeometry

end
