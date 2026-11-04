module

public import StacksFrontier.AlgebraicGeometry.BoundedFibreDescent.GluingPoints
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.SingleMorphismAction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.PuncturedSpectrumDescent
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.LimitSetup

/-!
# The gluing isomorphism of a descent datum, read over the double fibre product

A descent datum relative to `f : X ⟶ S` carries its gluing isomorphism in two interchangeable
shapes. `AlgebraicGeometry.DescentDatum.transitionPullbackIso` is the shape
`V ×_S X ≅ X ×_S V`, between two literal fibre products. The other is an isomorphism in
`CategoryTheory.Over (X ×_S X)` between the base changes of `V` along the two projections.

This file translates between the two, in both directions, using the identifications
`V ×_X (X ×_S X) ≅ V ×_S X` along the first projection and `V ×_X (X ×_S X) ≅ X ×_S V` along the
second. The cocycle condition is likewise read as one equation between two morphisms over the
triple fibre product `X ×_S X ×_S X`.

## Main definitions

* `AlgebraicGeometry.DescentDatum.sndProjPastingIso`: `V ×_X (X ×_S X) ≅ X ×_S V`, the second
  projection's counterpart of `CategoryTheory.Limits.pullbackRightPullbackFstIso`.
* `AlgebraicGeometry.DescentDatum.transitionBaseChangeIso`: **the gluing isomorphism of a
  descent datum read in `Over (X ×_S X)`.**
* `AlgebraicGeometry.DescentDatum.pullbackIsoOfBaseChangeIso`: **the converse translation**, of
  an isomorphism over `X ×_S X` into the shape
  `AlgebraicGeometry.DescentDatum.ofPullbackIso` asks for, with its two component identities.
* `AlgebraicGeometry.DescentDatum.tripleObjIso`: the base change of `V` along the first
  projection of `X ×_S X ×_S X` is `V ×_S X ×_S X`.
* `AlgebraicGeometry.DescentDatum.triActTwice`, `AlgebraicGeometry.DescentDatum.triActOnce`:
  the two sides of the cocycle condition over the triple fibre product.

## Main results

* `AlgebraicGeometry.DescentDatum.actPullbackLaw_transitionPullbackIso`: the cocycle condition
  of a descent datum in the form `AlgebraicGeometry.DescentDatum.ofPullbackIso` asks for.
* `AlgebraicGeometry.DescentDatum.actPullbackLaw_of_triAct_eq`: the cocycle condition of a
  candidate gluing isomorphism is one equation over the triple fibre product.

## References

* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace DescentDatum

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The base change of `W` along the second projection of `X ×_S X` is `X ×_S W`.** This is
the second projection's counterpart of `CategoryTheory.Limits.pullbackRightPullbackFstIso`. -/
def sndProjPastingIso (W : Over X) :
    pullback W.hom (pullback.snd f f) ≅ pullback f (W.hom ≫ f) :=
  pullbackSymmetry _ _ ≪≫ pullbackLeftPullbackSndIso f f W.hom

/-- The first component of `AlgebraicGeometry.DescentDatum.sndProjPastingIso` is the first
projection of `X ×_S X`. -/
@[reassoc (attr := simp)]
lemma sndProjPastingIso_hom_fst (W : Over X) :
    (sndProjPastingIso f W).hom ≫ pullback.fst f (W.hom ≫ f) =
      pullback.snd W.hom (pullback.snd f f) ≫ pullback.fst f f := by
  simp [sndProjPastingIso]

/-- The second component of `AlgebraicGeometry.DescentDatum.sndProjPastingIso` is the
projection to `W`. -/
@[reassoc (attr := simp)]
lemma sndProjPastingIso_hom_snd (W : Over X) :
    (sndProjPastingIso f W).hom ≫ pullback.snd f (W.hom ≫ f) =
      pullback.fst W.hom (pullback.snd f f) := by
  simp [sndProjPastingIso]

/-- The inverse of `AlgebraicGeometry.DescentDatum.sndProjPastingIso` followed by the projection
to `W` is the projection of `X ×_S W` to `W`. -/
@[reassoc (attr := simp)]
lemma sndProjPastingIso_inv_fst (W : Over X) :
    (sndProjPastingIso f W).inv ≫ pullback.fst W.hom (pullback.snd f f) =
      pullback.snd f (W.hom ≫ f) := by
  rw [Iso.inv_comp_eq, sndProjPastingIso_hom_snd]

/-- The inverse of `AlgebraicGeometry.DescentDatum.sndProjPastingIso` followed by the first
projection to `X` is the projection of `X ×_S W` to `X`. -/
@[reassoc]
lemma sndProjPastingIso_inv_snd_fst (W : Over X) :
    (sndProjPastingIso f W).inv ≫ pullback.snd W.hom (pullback.snd f f) ≫ pullback.fst f f =
      pullback.fst f (W.hom ≫ f) := by
  rw [Iso.inv_comp_eq]
  exact (sndProjPastingIso_hom_fst f W).symm

/-- The inverse of `AlgebraicGeometry.DescentDatum.sndProjPastingIso` followed by the second
projection to `X` is the projection of `X ×_S W` to `W` followed by the structure morphism of
`W`. -/
@[reassoc]
lemma sndProjPastingIso_inv_snd_snd (W : Over X) :
    (sndProjPastingIso f W).inv ≫ pullback.snd W.hom (pullback.snd f f) ≫ pullback.snd f f =
      pullback.snd f (W.hom ≫ f) ≫ W.hom := by
  rw [Iso.inv_comp_eq, ← pullback.condition, sndProjPastingIso_hom_snd_assoc]

/-- **The gluing isomorphism of a descent datum, read in `Over (X ×_S X)`** as an isomorphism
between the two base changes of the underlying scheme along the two projections. -/
def transitionBaseChangeIso (D : DescentDatum f) :
    (Over.pullback (pullback.fst f f)).obj D.over ≅
      (Over.pullback (pullback.snd f f)).obj D.over :=
  Over.isoMk (pullbackRightPullbackFstIso f f D.over.hom ≪≫ D.transitionPullbackIso ≪≫
      (sndProjPastingIso f D.over).symm) (by
    have h1 : D.transitionPullbackIso.hom ≫ pullback.fst f (D.over.hom ≫ f) =
        pullback.fst (D.over.hom ≫ f) f ≫ D.over.hom := D.gluingPullbackIso_hom_fst' () ()
    have h2 : D.transitionPullbackIso.hom ≫ pullback.snd f (D.over.hom ≫ f) ≫ D.over.hom =
        pullback.snd (D.over.hom ≫ f) f := D.gluingPullbackIso_hom_snd () ()
    have hcomp : (pullbackRightPullbackFstIso f f D.over.hom ≪≫ D.transitionPullbackIso ≪≫
        (sndProjPastingIso f D.over).symm).hom =
        (pullbackRightPullbackFstIso f f D.over.hom).hom ≫ D.transitionPullbackIso.hom ≫
          (sndProjPastingIso f D.over).inv := rfl
    rw [hcomp]
    refine pullback.hom_ext (f := f) (g := f) ?_ ?_
    · simp only [Over.pullback_obj_hom, Category.assoc, sndProjPastingIso_inv_snd_fst,
        h1, pullbackRightPullbackFstIso_hom_fst_assoc]
      exact pullback.condition (f := D.over.hom) (g := pullback.fst f f)
    · simp only [Over.pullback_obj_hom, Category.assoc, sndProjPastingIso_inv_snd_snd,
        h2, pullbackRightPullbackFstIso_hom_snd])

/-- The underlying morphism of `AlgebraicGeometry.DescentDatum.transitionBaseChangeIso` is
`AlgebraicGeometry.DescentDatum.transitionPullbackIso` conjugated by the two pasting
isomorphisms. -/
@[simp]
lemma transitionBaseChangeIso_hom_left (D : DescentDatum f) :
    (transitionBaseChangeIso f D).hom.left =
      (pullbackRightPullbackFstIso f f D.over.hom).hom ≫ D.transitionPullbackIso.hom ≫
        (sndProjPastingIso f D.over).inv :=
  rfl

/-- **The converse translation**: an isomorphism over `X ×_S X` between the two base changes of
`W` gives the gluing isomorphism in the shape
`AlgebraicGeometry.DescentDatum.ofPullbackIso` asks for. -/
def pullbackIsoOfBaseChangeIso (W : Over X)
    (ψ : (Over.pullback (pullback.fst f f)).obj W ≅ (Over.pullback (pullback.snd f f)).obj W) :
    pullback (W.hom ≫ f) f ≅ pullback f (W.hom ≫ f) :=
  (pullbackRightPullbackFstIso f f W.hom).symm ≪≫ (Over.forget _).mapIso ψ ≪≫
    sndProjPastingIso f W

/-- `AlgebraicGeometry.DescentDatum.pullbackIsoOfBaseChangeIso` is the underlying morphism of
`ψ` conjugated by the two pasting isomorphisms. -/
@[simp]
lemma pullbackIsoOfBaseChangeIso_hom (W : Over X)
    (ψ : (Over.pullback (pullback.fst f f)).obj W ≅ (Over.pullback (pullback.snd f f)).obj W) :
    (pullbackIsoOfBaseChangeIso f W ψ).hom =
      (pullbackRightPullbackFstIso f f W.hom).inv ≫ ψ.hom.left ≫
        (sndProjPastingIso f W).hom :=
  rfl

/-- The first component identity of `AlgebraicGeometry.DescentDatum.pullbackIsoOfBaseChangeIso`:
followed by the projection to `X`, it is the projection to `W` followed by `W.hom`. -/
lemma pullbackIsoOfBaseChangeIso_hom_fst (W : Over X)
    (ψ : (Over.pullback (pullback.fst f f)).obj W ≅ (Over.pullback (pullback.snd f f)).obj W) :
    (pullbackIsoOfBaseChangeIso f W ψ).hom ≫ pullback.fst f (W.hom ≫ f) =
      pullback.fst (W.hom ≫ f) f ≫ W.hom := by
  have hw : ψ.hom.left ≫ pullback.snd W.hom (pullback.snd f f) =
      pullback.snd W.hom (pullback.fst f f) := ψ.hom.w
  simp only [pullbackIsoOfBaseChangeIso_hom, Category.assoc, sndProjPastingIso_hom_fst,
    reassoc_of% hw, ← pullback.condition, pullbackRightPullbackFstIso_inv_fst_assoc]

/-- The second component identity of `AlgebraicGeometry.DescentDatum.pullbackIsoOfBaseChangeIso`:
followed by the projection to `W` and `W.hom`, it is the projection to `X`. -/
lemma pullbackIsoOfBaseChangeIso_hom_snd (W : Over X)
    (ψ : (Over.pullback (pullback.fst f f)).obj W ≅ (Over.pullback (pullback.snd f f)).obj W) :
    (pullbackIsoOfBaseChangeIso f W ψ).hom ≫ pullback.snd f (W.hom ≫ f) ≫ W.hom =
      pullback.snd (W.hom ≫ f) f := by
  have hw : ψ.hom.left ≫ pullback.snd W.hom (pullback.snd f f) =
      pullback.snd W.hom (pullback.fst f f) := ψ.hom.w
  simp only [pullbackIsoOfBaseChangeIso_hom, Category.assoc, sndProjPastingIso_hom_snd_assoc,
    pullback.condition, reassoc_of% hw, pullbackRightPullbackFstIso_inv_snd_snd]

/-- **The two translations of the gluing isomorphism are inverse to each other.** Reading the
gluing isomorphism of a descent datum in `Over (X ×_S X)` and then back on the literal fibre
products gives it again. -/
@[simp]
lemma pullbackIsoOfBaseChangeIso_transitionBaseChangeIso_hom (D : DescentDatum f) :
    (pullbackIsoOfBaseChangeIso f D.over (transitionBaseChangeIso f D)).hom =
      D.transitionPullbackIso.hom := by
  rw [pullbackIsoOfBaseChangeIso_hom, transitionBaseChangeIso_hom_left, Category.assoc,
    Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-! ### The triple fibre product -/

attribute [local implicit_reducible] tripleObj

/-- The first of the three projections of `X ×_S X ×_S X` to `X`, in the bracketing
`(X ×_S X) ×_S X`. -/
def tripleBaseFst : pullback (pullback.fst f f ≫ f) f ⟶ X :=
  pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.fst f f

/-- The second of the three projections of `X ×_S X ×_S X` to `X`. -/
def tripleBaseSnd : pullback (pullback.fst f f ≫ f) f ⟶ X :=
  pullback.fst (pullback.fst f f ≫ f) f ≫ pullback.snd f f

/-- The third of the three projections of `X ×_S X ×_S X` to `X`. -/
def tripleBaseThd : pullback (pullback.fst f f ≫ f) f ⟶ X :=
  pullback.snd (pullback.fst f f ≫ f) f

/-- The first and third projections of `X ×_S X ×_S X` agree over `S`. -/
@[reassoc]
lemma tripleBaseFst_comp : tripleBaseFst f ≫ f = tripleBaseThd f ≫ f := by
  rw [tripleBaseFst, tripleBaseThd, Category.assoc]
  exact pullback.condition

/-- The second and third projections of `X ×_S X ×_S X` agree over `S`. -/
@[reassoc]
lemma tripleBaseSnd_comp : tripleBaseSnd f ≫ f = tripleBaseThd f ≫ f := by
  rw [tripleBaseSnd, Category.assoc, ← pullback.condition, ← tripleBaseFst_comp, tripleBaseFst,
    Category.assoc]

/-- Two generalized points of the triple fibre product agree as soon as their three
components do. -/
lemma tripleBase_hom_ext {Z : Scheme.{u}} {m n : Z ⟶ pullback (pullback.fst f f ≫ f) f}
    (h₁ : m ≫ tripleBaseFst f = n ≫ tripleBaseFst f)
    (h₂ : m ≫ tripleBaseSnd f = n ≫ tripleBaseSnd f)
    (h₃ : m ≫ tripleBaseThd f = n ≫ tripleBaseThd f) : m = n := by
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) h₃
  · exact (Category.assoc m _ _).trans (h₁.trans (Category.assoc n _ _).symm)
  · exact (Category.assoc m _ _).trans (h₂.trans (Category.assoc n _ _).symm)

/-- The generalized point of the triple fibre product named by three points of `X` lying over
one point of `S`. -/
def tripleBaseLift {Z : Scheme.{u}} (x y z : Z ⟶ X) (hxz : x ≫ f = z ≫ f)
    (hyz : y ≫ f = z ≫ f) : Z ⟶ pullback (pullback.fst f f ≫ f) f :=
  pullback.lift (pullback.lift x y (hxz.trans hyz.symm)) z
    (by rw [← Category.assoc, pullback.lift_fst]; exact hxz)

/-- The first component of `AlgebraicGeometry.DescentDatum.tripleBaseLift f x y z` is `x`. -/
@[reassoc (attr := simp)]
lemma tripleBaseLift_fst {Z : Scheme.{u}} (x y z : Z ⟶ X) (hxz : x ≫ f = z ≫ f)
    (hyz : y ≫ f = z ≫ f) : tripleBaseLift f x y z hxz hyz ≫ tripleBaseFst f = x := by
  rw [tripleBaseFst, tripleBaseLift, ← Category.assoc, pullback.lift_fst, pullback.lift_fst]

/-- The second component of `AlgebraicGeometry.DescentDatum.tripleBaseLift f x y z` is `y`. -/
@[reassoc (attr := simp)]
lemma tripleBaseLift_snd {Z : Scheme.{u}} (x y z : Z ⟶ X) (hxz : x ≫ f = z ≫ f)
    (hyz : y ≫ f = z ≫ f) : tripleBaseLift f x y z hxz hyz ≫ tripleBaseSnd f = y := by
  rw [tripleBaseSnd, tripleBaseLift, ← Category.assoc, pullback.lift_fst, pullback.lift_snd]

/-- The third component of `AlgebraicGeometry.DescentDatum.tripleBaseLift f x y z` is `z`. -/
@[reassoc (attr := simp)]
lemma tripleBaseLift_thd {Z : Scheme.{u}} (x y z : Z ⟶ X) (hxz : x ≫ f = z ≫ f)
    (hyz : y ≫ f = z ≫ f) : tripleBaseLift f x y z hxz hyz ≫ tripleBaseThd f = z :=
  pullback.lift_snd _ _ _

/-- Two generalized points of `AlgebraicGeometry.DescentDatum.tripleObj` agree as soon as their
three components do. -/
lemma tripleObj_hom_ext {V : Over X} {Z : Scheme.{u}} {m n : Z ⟶ tripleObj V (f := f)}
    (h₁ : m ≫ tripleV V (f := f) = n ≫ tripleV V (f := f))
    (h₂ : m ≫ tripleX V (f := f) = n ≫ tripleX V (f := f))
    (h₃ : m ≫ tripleY V (f := f) = n ≫ tripleY V (f := f)) : m = n := by
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) h₃
  · exact (Category.assoc m _ _).trans (h₁.trans (Category.assoc n _ _).symm)
  · exact (Category.assoc m _ _).trans (h₂.trans (Category.assoc n _ _).symm)

/-- The first component of a generalized point of the base change of `V` along the first
projection of the triple fibre product lies over the second component. -/
lemma tripleObjIso_cond₁ (V : Over X) :
    pullback.fst V.hom (tripleBaseFst f) ≫ V.hom ≫ f =
      (pullback.snd V.hom (tripleBaseFst f) ≫ tripleBaseSnd f) ≫ f := by
  simp only [pullback.condition_assoc, Category.assoc, tripleBaseFst_comp, tripleBaseSnd_comp]

/-- The second and third components of a generalized point of the triple fibre product lie over
one point of the base. -/
lemma tripleObjIso_cond₂ (V : Over X) :
    (pullback.snd V.hom (tripleBaseFst f) ≫ tripleBaseSnd f) ≫ f =
      (pullback.snd V.hom (tripleBaseFst f) ≫ tripleBaseThd f) ≫ f := by
  simp only [Category.assoc, tripleBaseSnd_comp]

/-- **The base change of `V` along the first projection of `X ×_S X ×_S X` is the triple
product `V ×_S X ×_S X`** on which the cocycle condition of a descent datum lives. -/
def tripleObjIso (V : Over X) :
    pullback V.hom (tripleBaseFst f) ≅ tripleObj V (f := f) where
  hom := tripleLift V (pullback.fst V.hom (tripleBaseFst f))
    (pullback.snd V.hom (tripleBaseFst f) ≫ tripleBaseSnd f)
    (pullback.snd V.hom (tripleBaseFst f) ≫ tripleBaseThd f)
    (tripleObjIso_cond₁ f V) (tripleObjIso_cond₂ f V)
  inv := pullback.lift (tripleV V (f := f))
    (tripleBaseLift f (tripleV V (f := f) ≫ V.hom) (tripleX V (f := f)) (tripleY V (f := f))
      (by rw [Category.assoc]; exact (tripleV_comp V).trans (tripleX_comp V))
      (tripleX_comp V))
    (tripleBaseLift_fst f _ _ _ _ _).symm
  hom_inv_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp,
        tripleLift_comp_tripleV]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
      refine tripleBase_hom_ext f ?_ ?_ ?_
      · rw [Category.assoc, tripleBaseLift_fst, ← Category.assoc, tripleLift_comp_tripleV]
        exact pullback.condition
      · rw [Category.assoc, tripleBaseLift_snd, tripleLift_comp_tripleX]
      · rw [Category.assoc, tripleBaseLift_thd, tripleLift_comp_tripleY]
  inv_hom_id := by
    refine tripleObj_hom_ext f ?_ ?_ ?_
    · rw [Category.assoc, tripleLift_comp_tripleV, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, tripleLift_comp_tripleX, pullback.lift_snd_assoc,
        tripleBaseLift_snd, Category.id_comp]
    · rw [Category.assoc, tripleLift_comp_tripleY, pullback.lift_snd_assoc,
        tripleBaseLift_thd, Category.id_comp]

/-- The `V`-component of `AlgebraicGeometry.DescentDatum.tripleObjIso` is the projection to
`V`. -/
@[reassoc (attr := simp)]
lemma tripleObjIso_hom_tripleV (V : Over X) :
    (tripleObjIso f V).hom ≫ tripleV V (f := f) = pullback.fst V.hom (tripleBaseFst f) :=
  tripleLift_comp_tripleV V _ _ _ (tripleObjIso_cond₁ f V) (tripleObjIso_cond₂ f V)

/-- The first `X`-component of `AlgebraicGeometry.DescentDatum.tripleObjIso` is the second
projection of the triple fibre product. -/
@[reassoc (attr := simp)]
lemma tripleObjIso_hom_tripleX (V : Over X) :
    (tripleObjIso f V).hom ≫ tripleX V (f := f) =
      pullback.snd V.hom (tripleBaseFst f) ≫ tripleBaseSnd f :=
  tripleLift_comp_tripleX V _ _ _ (tripleObjIso_cond₁ f V) (tripleObjIso_cond₂ f V)

/-- The second `X`-component of `AlgebraicGeometry.DescentDatum.tripleObjIso` is the third
projection of the triple fibre product. -/
@[reassoc (attr := simp)]
lemma tripleObjIso_hom_tripleY (V : Over X) :
    (tripleObjIso f V).hom ≫ tripleY V (f := f) =
      pullback.snd V.hom (tripleBaseFst f) ≫ tripleBaseThd f :=
  tripleLift_comp_tripleY V _ _ _ (tripleObjIso_cond₁ f V) (tripleObjIso_cond₂ f V)

/-! ### The cocycle condition in the form `ofPullbackIso` asks for -/

/-- **The gluing isomorphism of a descent datum is the candidate gluing map built from its own
pullback-form gluing isomorphism.** -/
lemma gluingHomOfPullbackHom_transitionPullbackIso (D : DescentDatum f) :
    gluingHomOfPullbackHom D.over D.transitionPullbackIso.hom
        (D.gluingPullbackIso_hom_fst' () ()) = D.transition.hom.left := by
  apply Over.OverMorphism.ext
  simp [gluingHomOfPullbackHom_left]

/-- The action of a descent datum on generalized points is the action of its pullback-form
gluing isomorphism. -/
lemma act_left (D : DescentDatum f) {W : Over S} (a : W ⟶ (Over.map f).obj D.over)
    (b : W ⟶ Over.mk f) :
    (D.act a b).left = actPullback D.over D.transitionPullbackIso.hom a.left b.left
      ((Over.w a).trans (Over.w b).symm) := by
  refine Eq.trans ?_ (left_gluingAction_gluingHomOfPullbackHom D.over
    D.transitionPullbackIso.hom (D.gluingPullbackIso_hom_fst' () ()) a b)
  exact congrArg (fun ψ ↦ (gluingAction D.over ψ a b).left)
    (gluingHomOfPullbackHom_transitionPullbackIso f D).symm

/-- **The cocycle condition of a descent datum, in the form
`AlgebraicGeometry.DescentDatum.ofPullbackIso` asks for.** Acting twice is acting once, read on
the literal fibre products rather than on the products of `CategoryTheory.Over`. -/
theorem actPullbackLaw_transitionPullbackIso (D : DescentDatum f) :
    ActPullbackLaw D.over D.transitionPullbackIso.hom := by
  intro Z v x y hv hw hvx
  have hvw : v ≫ ((Over.map f).obj D.over).hom = (Over.mk (y ≫ f) : Over S).hom :=
    hv.trans hw
  have h := congrArg Over.Hom.left (D.act_act (T := Over.mk (y ≫ f)) (Over.homMk v hvw)
    (Over.homMk x hw) (Over.homMk y rfl))
  simp only [act_left] at h
  exact h

/-! ### The cocycle condition as one equation over the triple fibre product -/

/-- **The result of acting twice** — in turn with the second and with the third of the three
universal points of `X` — on the universal point of `V`, read over the base change of `V` along
the first projection of `X ×_S X ×_S X`. -/
def triActTwice (V : Over X) (ι : pullback (V.hom ≫ f) f ⟶ pullback f (V.hom ≫ f))
    (hι : ι ≫ pullback.snd f (V.hom ≫ f) ≫ V.hom = pullback.snd (V.hom ≫ f) f) :
    pullback V.hom (tripleBaseFst f) ⟶ V.left :=
  actPullback V ι
    (actPullback V ι (pullback.fst V.hom (tripleBaseFst f))
      (pullback.snd V.hom (tripleBaseFst f) ≫ tripleBaseSnd f) (tripleObjIso_cond₁ f V))
    (pullback.snd V.hom (tripleBaseFst f) ≫ tripleBaseThd f)
    (actPullback_comp_hom_comp V ι hι _ _ _ (tripleObjIso_cond₁ f V) (tripleObjIso_cond₂ f V))

/-- **The result of acting once**, with the third universal point of `X`, on the universal point
of `V`. -/
def triActOnce (V : Over X) (ι : pullback (V.hom ≫ f) f ⟶ pullback f (V.hom ≫ f)) :
    pullback V.hom (tripleBaseFst f) ⟶ V.left :=
  actPullback V ι (pullback.fst V.hom (tripleBaseFst f))
    (pullback.snd V.hom (tripleBaseFst f) ≫ tripleBaseThd f)
    ((tripleObjIso_cond₁ f V).trans (tripleObjIso_cond₂ f V))

/-- `AlgebraicGeometry.DescentDatum.triActTwice` lies over the third projection of the triple
fibre product. -/
@[reassoc]
lemma triActTwice_comp_hom (V : Over X) (ι : pullback (V.hom ≫ f) f ⟶ pullback f (V.hom ≫ f))
    (hι : ι ≫ pullback.snd f (V.hom ≫ f) ≫ V.hom = pullback.snd (V.hom ≫ f) f) :
    triActTwice f V ι hι ≫ V.hom =
      pullback.snd V.hom (tripleBaseFst f) ≫ tripleBaseThd f :=
  actPullback_comp_hom V ι hι _ _ _

/-- `AlgebraicGeometry.DescentDatum.triActOnce` lies over the third projection of the triple
fibre product. -/
@[reassoc]
lemma triActOnce_comp_hom (V : Over X) (ι : pullback (V.hom ≫ f) f ⟶ pullback f (V.hom ≫ f))
    (hι : ι ≫ pullback.snd f (V.hom ≫ f) ≫ V.hom = pullback.snd (V.hom ≫ f) f) :
    triActOnce f V ι ≫ V.hom = pullback.snd V.hom (tripleBaseFst f) ≫ tripleBaseThd f :=
  actPullback_comp_hom V ι hι _ _ _

/-- Acting commutes with change of test scheme, with the two points given up to equality. -/
private lemma comp_actPullback_eq (V : Over X) (ι : pullback (V.hom ≫ f) f ⟶ pullback f (V.hom ≫ f))
    {Z Z' : Scheme.{u}} (k : Z' ⟶ Z) (v : Z ⟶ V.left) (x : Z ⟶ X) (h : v ≫ V.hom ≫ f = x ≫ f)
    {v' : Z' ⟶ V.left} {x' : Z' ⟶ X} (hv : k ≫ v = v') (hx : k ≫ x = x')
    (h' : v' ≫ V.hom ≫ f = x' ≫ f) :
    k ≫ actPullback V ι v x h = actPullback V ι v' x' h' := by
  subst hv hx
  exact comp_actPullback V ι k v x h h'

/-- **Acting twice commutes with change of test scheme.** -/
lemma comp_triActTwice (V : Over X) (ι : pullback (V.hom ≫ f) f ⟶ pullback f (V.hom ≫ f))
    (hι : ι ≫ pullback.snd f (V.hom ≫ f) ≫ V.hom = pullback.snd (V.hom ≫ f) f)
    {Z : Scheme.{u}} (H : Z ⟶ pullback V.hom (tripleBaseFst f)) (v : Z ⟶ V.left) (x y : Z ⟶ X)
    (hHv : H ≫ pullback.fst V.hom (tripleBaseFst f) = v)
    (hHx : H ≫ pullback.snd V.hom (tripleBaseFst f) ≫ tripleBaseSnd f = x)
    (hHy : H ≫ pullback.snd V.hom (tripleBaseFst f) ≫ tripleBaseThd f = y)
    (hv : v ≫ V.hom ≫ f = x ≫ f) (hw : x ≫ f = y ≫ f) :
    H ≫ triActTwice f V ι hι =
      actPullback V ι (actPullback V ι v x hv) y
        (actPullback_comp_hom_comp V ι hι v x y hv hw) := by
  have hinner : H ≫ actPullback V ι (pullback.fst V.hom (tripleBaseFst f))
        (pullback.snd V.hom (tripleBaseFst f) ≫ tripleBaseSnd f) (tripleObjIso_cond₁ f V) =
      actPullback V ι v x hv := by
    exact comp_actPullback_eq f V ι H _ _ (tripleObjIso_cond₁ f V) hHv hHx hv
  exact comp_actPullback_eq f V ι H _ _ _ hinner hHy _

/-- **Acting once commutes with change of test scheme.** -/
lemma comp_triActOnce (V : Over X) (ι : pullback (V.hom ≫ f) f ⟶ pullback f (V.hom ≫ f))
    {Z : Scheme.{u}} (H : Z ⟶ pullback V.hom (tripleBaseFst f)) (v : Z ⟶ V.left) (y : Z ⟶ X)
    (hHv : H ≫ pullback.fst V.hom (tripleBaseFst f) = v)
    (hHy : H ≫ pullback.snd V.hom (tripleBaseFst f) ≫ tripleBaseThd f = y)
    (hvy : v ≫ V.hom ≫ f = y ≫ f) :
    H ≫ triActOnce f V ι = actPullback V ι v y hvy := by
  exact comp_actPullback_eq f V ι H _ _ _ hHv hHy hvy

/-- **The cocycle condition, read over the triple fibre product**: for a gluing isomorphism
satisfying the action law the two sides agree. -/
lemma triActTwice_eq_triActOnce (V : Over X)
    (ι : pullback (V.hom ≫ f) f ⟶ pullback f (V.hom ≫ f))
    (hι : ι ≫ pullback.snd f (V.hom ≫ f) ≫ V.hom = pullback.snd (V.hom ≫ f) f)
    (hlaw : ActPullbackLaw V ι) : triActTwice f V ι hι = triActOnce f V ι :=
  hlaw _ _ _ (tripleObjIso_cond₁ f V) (tripleObjIso_cond₂ f V) _

/-- **An action-like morphism over the triple fibre product, read as a morphism of base
changes** from the base change of `V` along the first projection to the base change along the
third. -/
def triOverHom (V : Over X) (w : pullback V.hom (tripleBaseFst f) ⟶ V.left)
    (hw : w ≫ V.hom = pullback.snd V.hom (tripleBaseFst f) ≫ tripleBaseThd f) :
    (Over.pullback (tripleBaseFst f)).obj V ⟶ (Over.pullback (tripleBaseThd f)).obj V :=
  Over.homMk (pullback.lift w (pullback.snd V.hom (tripleBaseFst f)) hw)
    (pullback.lift_snd _ _ _)

/-- The `V`-component of `AlgebraicGeometry.DescentDatum.triOverHom f V w hw` is `w`. -/
@[reassoc (attr := simp)]
lemma triOverHom_left_fst (V : Over X) (w : pullback V.hom (tripleBaseFst f) ⟶ V.left)
    (hw : w ≫ V.hom = pullback.snd V.hom (tripleBaseFst f) ≫ tripleBaseThd f) :
    (triOverHom f V w hw).left ≫ pullback.fst V.hom (tripleBaseThd f) = w :=
  pullback.lift_fst _ _ _

/-- **The cocycle condition of a candidate gluing isomorphism is one equation between two
morphisms over the triple fibre product.** The two sides are
`AlgebraicGeometry.DescentDatum.triActTwice` and
`AlgebraicGeometry.DescentDatum.triActOnce`. -/
theorem actPullbackLaw_of_triAct_eq (V : Over X)
    (ι : pullback (V.hom ≫ f) f ⟶ pullback f (V.hom ≫ f))
    (hι : ι ≫ pullback.snd f (V.hom ≫ f) ≫ V.hom = pullback.snd (V.hom ≫ f) f)
    (h : triActTwice f V ι hι = triActOnce f V ι) : ActPullbackLaw V ι := by
  refine actPullbackLaw_of_universal V ι hι ?_
  have hV : (tripleObjIso f V).hom ≫ tripleV V (f := f) = pullback.fst V.hom (tripleBaseFst f) :=
    tripleObjIso_hom_tripleV f V
  have hX : (tripleObjIso f V).hom ≫ tripleX V (f := f) =
      pullback.snd V.hom (tripleBaseFst f) ≫ tripleBaseSnd f := tripleObjIso_hom_tripleX f V
  have hY : (tripleObjIso f V).hom ≫ tripleY V (f := f) =
      pullback.snd V.hom (tripleBaseFst f) ≫ tripleBaseThd f := tripleObjIso_hom_tripleY f V
  have hinner : (tripleObjIso f V).hom ≫
      actPullback V ι (tripleV V (f := f)) (tripleX V (f := f)) (tripleV_comp V) =
      actPullback V ι (pullback.fst V.hom (tripleBaseFst f))
        (pullback.snd V.hom (tripleBaseFst f) ≫ tripleBaseSnd f) (tripleObjIso_cond₁ f V) := by
    exact comp_actPullback_eq f V ι _ _ _ (tripleV_comp V) hV hX _
  have hVY := (tripleObjIso_cond₁ f V).trans (tripleObjIso_cond₂ f V)
  rwa [← cancel_epi (tripleObjIso f V).hom,
    comp_actPullback_eq f V ι _ _ _ _ hinner hY (actPullback_comp_hom_comp V ι hι _ _ _
      (tripleObjIso_cond₁ f V) (tripleObjIso_cond₂ f V)),
    comp_actPullback_eq f V ι _ _ _ _ hV hY hVY]

end DescentDatum

end AlgebraicGeometry

end
