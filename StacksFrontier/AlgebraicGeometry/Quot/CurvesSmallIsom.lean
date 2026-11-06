module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallAutomorphisms
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyIsomSeparated
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallAutomorphisms

/-!
# The isomorphism space of two families of curves

Let `y₁` and `y₂` be objects of the small model `AlgebraicGeometry.curvesSmall` of the stack of
curves over the same scheme `U` of the big fppf site of `Spec(ℤ)`, i.e. two families of curves
`Y ⟶ U` and `X ⟶ U` (Stacks 0D4Z). Two presheaves are attached to the pair:

* the isomorphism space `Isom_𝒳(y₁, y₂)` of Stacks 04YP
  (`AlgebraicGeometry.Stack.isomSpace`), a presheaf on the big fppf site of `U` whose sections
  over `V ⟶ U` are the isomorphisms from the pullback of `y₁` to the pullback of `y₂` in the fibre
  over `V`; and
* the functor `Isom_U(Y, X)` of Stacks 0DPP (`AlgebraicGeometry.CurveFamily.isomFunctor`), a
  subpresheaf of the relative morphism functor of Stacks 05Y2 on the big fppf site of `Spec(ℤ)`,
  whose sections over `T` are the pairs `(a, b)` with `a : T ⟶ U` and `b : Y_T ⟶ X_T` an
  isomorphism over `T`.

This file identifies the two, generalising the case `y₁ = y₂` of
`AlgebraicGeometry.curvesSmall.nonempty_arrowIso_autFunctorProjection`: the structure morphism of
`Isom_𝒳(y₁, y₂)`, viewed over `Spec(ℤ)` along `U ⟶ Spec(ℤ)` (Stacks 04SG), is isomorphic as an
arrow to the projection `Isom_U(Y, X) ⟶ U`. With
`AlgebraicGeometry.CurveFamily.isSeparated_isomFunctorProjection` this gives the separation step
in the proof of Stacks 0DSQ: `Isom_𝒳(y₁, y₂)` is separated over `U`.

## Main results

* `AlgebraicGeometry.curvesSmall.nonempty_arrowIso_isomFunctorProjection`: the arrow isomorphism.
* `AlgebraicGeometry.curvesSmall.isSeparated_relocalizeToYoneda_isomSpace`: `Isom_𝒳(y₁, y₂)` is
  separated over `U`, read over `Spec(ℤ)`.
* `AlgebraicGeometry.curvesSmall.isQuasiSeparated_relocalizeToYoneda_isomSpace`: hence
  quasi-separated.
* `AlgebraicGeometry.curvesSmall.isQuasiCompact_relocalizeToYoneda_isomSpace_of`: it is
  quasi-compact over `U` as soon as `Isom_U(Y, X)` is.

## Implementation notes

The two families have bases `p(y₁)` and `p(y₂)`, both equal to `U` but not definitionally; the
family `X` is read over the base of `Y` through the identification `eqToHom` of the two. The
argument is that of `StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallAutomorphisms`, whose
`y`-independent private steps are reused through `import all`: the chosen pullback of `y₂` along
`V ⟶ U` is the base change of `X` through the chosen cartesian arrow, so a morphism of the fibre
from the pullback of `y₁` to that of `y₂` is a morphism `Y_V ⟶ X_V` over `V`.

## References

* [Stacks Project, Tag 04YP](https://stacks.math.columbia.edu/tag/04YP)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 05Y2](https://stacks.math.columbia.edu/tag/05Y2)
* [Stacks Project, Tag 0DPP](https://stacks.math.columbia.edu/tag/0DPP)
* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace curvesSmall

attribute [local instance] isFibered locallySmall_curveFamily

attribute [local implicit_reducible] schemeSpace ShrinkHoms.fromShrinkHoms ShrinkHoms.inverse
  curvesSmall curvesSmallBased

variable {U : BigFppfOver B integerBase hZ} (y₁ y₂ : (curvesSmall B hZ).val.p.Fiber U)

/-- The identification of the bases of the families of `y₂` and `y₁`, both `U`. -/
private noncomputable abbrev φ₂₁ : (fam y₂).base ⟶ (fam y₁).base :=
  eqToHom (y₂.2.trans y₁.2.symm)

private instance isIso_yoneda_map_φ₂₁ : IsIso (yoneda.map (φ₂₁ y₁ y₂)) :=
  (yoneda.mapIso (eqToIso (y₂.2.trans y₁.2.symm))).isIso_hom

/-- The structure morphism of the family of `y₂`, read over the base of the family of `y₁`. -/
private noncomputable abbrev tgt : (fam y₂).total.obj ⟶ (schemeSpace (fam y₁).base).obj :=
  (fam y₂).toBase.hom ≫ yoneda.map (φ₂₁ y₁ y₂)

/-- The identification of the bases of the chosen pullbacks of `y₁` and `y₂` along `g`. -/
private noncomputable abbrev pbBaseIso (g : Over U) : (pb y₁ g).base ≅ (pb y₂ g).base :=
  eqToIso ((Functor.pullbackFiber (curvesSmall B hZ).val.p y₁ g.hom).2.trans
    (Functor.pullbackFiber (curvesSmall B hZ).val.p y₂ g.hom).2.symm)

/-- A morphism of the fibre over `g.left` from the pullback of `y₁` to that of `y₂`, as a
morphism of families. -/
private noncomputable abbrev unshrink₂ {g : Over U}
    (m : Functor.pullbackFiber (curvesSmall B hZ).val.p y₁ g.hom ⟶
      Functor.pullbackFiber (curvesSmall B hZ).val.p y₂ g.hom) : pb y₁ g ⟶ pb y₂ g :=
  uns m.1

private theorem unshrink₂_baseMap {g : Over U}
    (m : Functor.pullbackFiber (curvesSmall B hZ).val.p y₁ g.hom ⟶
      Functor.pullbackFiber (curvesSmall B hZ).val.p y₂ g.hom) :
    (unshrink₂ y₁ y₂ m).baseMap = (pbBaseIso y₁ y₂ g).hom := by
  have := m.2
  have h := IsHomLift.fac' (curvesSmall B hZ).val.p (𝟙 g.left) m.1
  change (unshrink₂ y₁ y₂ m).baseMap = _ at h
  rw [h, Category.id_comp, eqToHom_trans]
  rfl

/-- Two morphisms which agree with a common one up to `eqToHom` on both sides agree up to the
induced `eqToHom`s. -/
private theorem eqToHom_comp_comp_eqToHom_of_eq {C : Type*} [Category C] {P₁ P₂ L V Q₁ Q₂ : C}
    (a₁ : P₁ = L) (a₂ : P₂ = L) (b₁ : Q₁ = V) (b₂ : Q₂ = V) (p₁ : P₁ ⟶ Q₁) (p₂ : P₂ ⟶ Q₂)
    (f : L ⟶ V) (h₁ : eqToHom a₁.symm ≫ p₁ = f ≫ eqToHom b₁.symm)
    (h₂ : eqToHom a₂.symm ≫ p₂ = f ≫ eqToHom b₂.symm) :
    eqToHom (a₁.trans a₂.symm) ≫ p₂ ≫ eqToHom (b₂.trans b₁.symm) = p₁ := by
  subst a₁ a₂ b₁ b₂
  simp_all

private theorem pbBaseIso_pbMap_baseMap (g : Over U) :
    (pbBaseIso y₁ y₂ g).hom ≫ (pbMap y₂ g).baseMap ≫ φ₂₁ y₁ y₂ = (pbMap y₁ g).baseMap :=
  eqToHom_comp_comp_eqToHom_of_eq (Functor.pullbackFiber (curvesSmall B hZ).val.p y₁ g.hom).2
    (Functor.pullbackFiber (curvesSmall B hZ).val.p y₂ g.hom).2 y₁.2 y₂.2 _ _ g.hom
    (pbMap_baseMap y₁ g) (pbMap_baseMap y₂ g)

/-- `pbBaseIso_pbMap_baseMap`, after applying `yoneda`. -/
private theorem yoneda_map_pbBaseIso_comp (g : Over U) :
    yoneda.map (pbBaseIso y₁ y₂ g).hom ≫ yoneda.map (pbMap y₂ g).baseMap ≫
      yoneda.map (φ₂₁ y₁ y₂) = yoneda.map (pbMap y₁ g).baseMap := by
  rw [← Functor.map_comp, ← Functor.map_comp, pbBaseIso_pbMap_baseMap]

private theorem pairBase_comp_φ₂₁ (g : Over U) {W : BigFppfOver B integerBase hZ}
    (e : W ≅ (pb y₁ g).base) :
    pairBase y₂ g (e ≪≫ pbBaseIso y₁ y₂ g) ≫ yoneda.map (φ₂₁ y₁ y₂) = pairBase y₁ g e :=
  (Functor.map_comp _ _ _).symm.trans (congrArg yoneda.map
    (((Category.assoc _ _ _).trans (Category.assoc _ _ _)).trans
      (congrArg (e.hom ≫ ·) (pbBaseIso_pbMap_baseMap y₁ y₂ g))))

/-- The cartesian square of `pbMap y₂ g` in presheaves, read over the base of the family of
`y₁`. -/
private theorem isPullback_pb₂ (g : Over U) {W : BigFppfOver B integerBase hZ}
    (e : W ≅ (pb y₁ g).base) :
    IsPullback ((pb y₂ g).toBase.hom ≫ yoneda.map (e ≪≫ pbBaseIso y₁ y₂ g).inv)
      (pbMap y₂ g).totalMap.hom (pairBase y₁ g e) (tgt y₁ y₂) :=
  (isPullback_pb y₂ g (e ≪≫ pbBaseIso y₁ y₂ g)).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (asIso (yoneda.map (φ₂₁ y₁ y₂))) ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((pairBase_comp_φ₂₁ y₁ y₂ g e).trans (Category.id_comp _).symm) (Category.id_comp _).symm

/-- The identification of the base change of `fam y₂` along `W ⟶ fam y₁` with `pb y₂ g`. -/
private noncomputable abbrev κ₂ (g : Over U) {W : BigFppfOver B integerBase hZ}
    (e : W ≅ (pb y₁ g).base) :
    pullback (pairBase y₁ g e) (tgt y₁ y₂) ⟶ (pb y₂ g).total.obj :=
  (isPullback_pb₂ y₁ y₂ g e).isoPullback.inv

private theorem κ₂_fst (g : Over U) {W : BigFppfOver B integerBase hZ}
    (e : W ≅ (pb y₁ g).base) :
    κ₂ y₁ y₂ g e ≫ (pb y₂ g).toBase.hom ≫ yoneda.map (e ≪≫ pbBaseIso y₁ y₂ g).inv =
      pullback.fst _ _ :=
  IsPullback.isoPullback_inv_fst _

private theorem κ₂_snd (g : Over U) {W : BigFppfOver B integerBase hZ}
    (e : W ≅ (pb y₁ g).base) :
    κ₂ y₁ y₂ g e ≫ (pbMap y₂ g).totalMap.hom = pullback.snd _ _ :=
  IsPullback.isoPullback_inv_snd _

private theorem κ₂_toBase (g : Over U) {W : BigFppfOver B integerBase hZ}
    (e : W ≅ (pb y₁ g).base) :
    κ₂ y₁ y₂ g e ≫ (pb y₂ g).toBase.hom =
      pullback.fst _ _ ≫ yoneda.map (e ≪≫ pbBaseIso y₁ y₂ g).hom := by
  calc κ₂ y₁ y₂ g e ≫ (pb y₂ g).toBase.hom
      = κ₂ y₁ y₂ g e ≫ (pb y₂ g).toBase.hom ≫
          yoneda.map ((e ≪≫ pbBaseIso y₁ y₂ g).inv ≫ (e ≪≫ pbBaseIso y₁ y₂ g).hom) := by
        rw [Iso.inv_hom_id, CategoryTheory.Functor.map_id]; rfl
    _ = pullback.fst _ _ ≫ yoneda.map (e ≪≫ pbBaseIso y₁ y₂ g).hom := by
        rw [Functor.map_comp, ← κ₂_fst y₁ y₂ g e]; simp only [Category.assoc]

private theorem unshrink₂_totalMap_comp_toBase {g : Over U}
    (m : Functor.pullbackFiber (curvesSmall B hZ).val.p y₁ g.hom ⟶
      Functor.pullbackFiber (curvesSmall B hZ).val.p y₂ g.hom) :
    (unshrink₂ y₁ y₂ m).totalMap.hom ≫ (pb y₂ g).toBase.hom =
      (pb y₁ g).toBase.hom ≫ yoneda.map (pbBaseIso y₁ y₂ g).hom := by
  rw [totalMap_comp_toBase, unshrink₂_baseMap]

private theorem unshrink₂_totalMap_comp_tgt {g : Over U}
    (m : Functor.pullbackFiber (curvesSmall B hZ).val.p y₁ g.hom ⟶
      Functor.pullbackFiber (curvesSmall B hZ).val.p y₂ g.hom) :
    (unshrink₂ y₁ y₂ m).totalMap.hom ≫ (pbMap y₂ g).totalMap.hom ≫ tgt y₁ y₂ =
      (pbMap y₁ g).totalMap.hom ≫ (fam y₁).toBase.hom := by
  change _ ≫ _ ≫ (fam y₂).toBase.hom ≫ yoneda.map (φ₂₁ y₁ y₂) = _
  rw [reassoc_of% (totalMap_comp_toBase (pbMap y₂ g)),
    reassoc_of% (unshrink₂_totalMap_comp_toBase y₁ y₂ m), yoneda_map_pbBaseIso_comp,
    totalMap_comp_toBase]

/-- The pair of Stacks 05Y1 attached to a morphism `m` from the chosen pullback of `y₁` along `g`
to that of `y₂`: its base is the morphism `W ⟶ U` and its second component is `m` followed by the
cartesian arrow to `y₂`, read on the base change of `fam y₁`. -/
private noncomputable def isoPair (g : Over U) {W : BigFppfOver B integerBase hZ}
    (e : W ≅ (pb y₁ g).base)
    (m : Functor.pullbackFiber (curvesSmall B hZ).val.p y₁ g.hom ⟶
      Functor.pullbackFiber (curvesSmall B hZ).val.p y₂ g.hom) :
    Space.RelativeMorphism B integerBase hZ (fam y₁).total.obj (fam y₂).total.obj
      (schemeSpace (fam y₁).base).obj (fam y₁).toBase.hom (tgt y₁ y₂) (yoneda.obj W) where
  base := pairBase y₁ g e
  morphism := κ y₁ g e ≫ (unshrink₂ y₁ y₂ m).totalMap.hom ≫ (pbMap y₂ g).totalMap.hom
  commutes := by
    rw [Category.assoc, Category.assoc, unshrink₂_totalMap_comp_tgt, reassoc_of% (κ_snd y₁ g e)]

attribute [local implicit_reducible] isoPair

private theorem isoPair_morphism (g : Over U) {W : BigFppfOver B integerBase hZ}
    (e : W ≅ (pb y₁ g).base)
    (m : Functor.pullbackFiber (curvesSmall B hZ).val.p y₁ g.hom ⟶
      Functor.pullbackFiber (curvesSmall B hZ).val.p y₂ g.hom) :
    (isoPair y₁ y₂ g e m).morphism =
      κ y₁ g e ≫ (unshrink₂ y₁ y₂ m).totalMap.hom ≫ (pbMap y₂ g).totalMap.hom :=
  rfl

private theorem isoPair_baseChangeMap_comp_κ₂ (g : Over U) {W : BigFppfOver B integerBase hZ}
    (e : W ≅ (pb y₁ g).base)
    (m : Functor.pullbackFiber (curvesSmall B hZ).val.p y₁ g.hom ⟶
      Functor.pullbackFiber (curvesSmall B hZ).val.p y₂ g.hom) :
    (isoPair y₁ y₂ g e m).baseChangeMap ≫ κ₂ y₁ y₂ g e =
      κ y₁ g e ≫ (unshrink₂ y₁ y₂ m).totalMap.hom := by
  apply (isPullback_pb₂ y₁ y₂ g e).hom_ext
  · calc ((isoPair y₁ y₂ g e m).baseChangeMap ≫ κ₂ y₁ y₂ g e) ≫ (pb y₂ g).toBase.hom ≫
          yoneda.map (e ≪≫ pbBaseIso y₁ y₂ g).inv
        = (isoPair y₁ y₂ g e m).baseChangeMap ≫ pullback.fst _ _ := by
          rw [Category.assoc, κ₂_fst]; rfl
      _ = pullback.fst _ _ := Space.RelativeMorphism.baseChangeMap_comp_fst _
      _ = κ y₁ g e ≫ (pb y₁ g).toBase.hom ≫ yoneda.map e.inv := (κ_fst y₁ g e).symm
      _ = (κ y₁ g e ≫ (unshrink₂ y₁ y₂ m).totalMap.hom) ≫ (pb y₂ g).toBase.hom ≫
          yoneda.map (e ≪≫ pbBaseIso y₁ y₂ g).inv := by
          rw [Category.assoc, reassoc_of% (unshrink₂_totalMap_comp_toBase y₁ y₂ m),
            ← Functor.map_comp, Iso.trans_inv, Iso.hom_inv_id_assoc]
  · calc ((isoPair y₁ y₂ g e m).baseChangeMap ≫ κ₂ y₁ y₂ g e) ≫ (pbMap y₂ g).totalMap.hom
        = (isoPair y₁ y₂ g e m).baseChangeMap ≫ pullback.snd _ _ := by
          rw [Category.assoc, κ₂_snd]; rfl
      _ = (isoPair y₁ y₂ g e m).morphism := Space.RelativeMorphism.baseChangeMap_comp_snd _
      _ = _ := (isoPair_morphism y₁ y₂ g e m).trans (Category.assoc _ _ _).symm

private theorem isoPair_isRelativeIso (g : Over U) {W : BigFppfOver B integerBase hZ}
    (e : W ≅ (pb y₁ g).base)
    (m : Functor.pullbackFiber (curvesSmall B hZ).val.p y₁ g.hom ⟶
      Functor.pullbackFiber (curvesSmall B hZ).val.p y₂ g.hom) [IsIso m] :
    (isoPair y₁ y₂ g e m).IsRelativeIso := by
  have : IsIso m.1 := inferInstanceAs (IsIso (Functor.Fiber.fiberInclusion.map m))
  have : IsIso (unshrink₂ y₁ y₂ m) := isIso_uns m.1
  have := isIso_totalMap (unshrink₂ y₁ y₂ m)
  have h : (isoPair y₁ y₂ g e m).baseChangeMap =
      κ y₁ g e ≫ (unshrink₂ y₁ y₂ m).totalMap.hom ≫ inv (κ₂ y₁ y₂ g e) := by
    rw [← reassoc_of% (isoPair_baseChangeMap_comp_κ₂ y₁ y₂ g e m), IsIso.hom_inv_id,
      Category.comp_id]
  show IsIso (isoPair y₁ y₂ g e m).baseChangeMap
  rw [h]
  infer_instance

private theorem unshrink₂_morRestrict {g₁ g₂ : Over U} (H : g₁ ⟶ g₂)
    (m : Functor.pullbackFiber (curvesSmall B hZ).val.p y₁ g₂.hom ⟶
      Functor.pullbackFiber (curvesSmall B hZ).val.p y₂ g₂.hom) :
    unshrink₂ y₁ y₂ (Functor.morRestrict _ y₁ y₂ H m) ≫ pbMap y₂ g₁ =
      pbRestrict y₁ H ≫ unshrink₂ y₁ y₂ m ≫ pbMap y₂ g₂ := by
  have h := congrArg uns (Functor.morRestrict_fac _ y₁ y₂ H m)
  exact (uns_comp _ _).symm.trans (h.trans ((uns_comp _ _).trans
    (congrArg (uns (Functor.pullbackFiberMap _ y₁ H) ≫ ·) (uns_comp _ _))))

/-- **Naturality of the pairs.** Restricting the pair of `m` along `f : W₁ ⟶ W₂` is the pair of
the restriction of `m`. -/
private theorem isoPair_morRestrict {g₁ g₂ : Over U} (H : g₁ ⟶ g₂)
    {W₁ W₂ : BigFppfOver B integerBase hZ}
    (f : W₁ ⟶ W₂) (e₁ : W₁ ≅ (pb y₁ g₁).base) (e₂ : W₂ ≅ (pb y₁ g₂).base)
    (hcomp : e₁.hom ≫ (pbRestrict y₁ H).baseMap = f ≫ e₂.hom)
    (m : Functor.pullbackFiber (curvesSmall B hZ).val.p y₁ g₂.hom ⟶
      Functor.pullbackFiber (curvesSmall B hZ).val.p y₂ g₂.hom) :
    isoPair y₁ y₂ g₁ e₁ (Functor.morRestrict _ y₁ y₂ H m) =
      Space.RelativeMorphism.restrict (yoneda.map f) (isoPair y₁ y₂ g₂ e₂ m) := by
  have hb : pairBase y₁ g₁ e₁ = yoneda.map f ≫ pairBase y₁ g₂ e₂ := by
    show yoneda.map (e₁.hom ≫ (pbMap y₁ g₁).baseMap) =
      yoneda.map f ≫ yoneda.map (e₂.hom ≫ (pbMap y₁ g₂).baseMap)
    rw [← pbRestrict_comp_pbMap y₁ H]
    show yoneda.map (e₁.hom ≫ (pbRestrict y₁ H).baseMap ≫ (pbMap y₁ g₂).baseMap) =
      yoneda.map f ≫ yoneda.map (e₂.hom ≫ (pbMap y₁ g₂).baseMap)
    rw [← Functor.map_comp, reassoc_of% hcomp]
  refine Space.RelativeMorphism.ext_of_base_eq hb ?_
  have hK : κ y₁ g₁ e₁ ≫ (pbRestrict y₁ H).totalMap.hom =
      (pullback.congrHom hb rfl).hom ≫
        pullback.map (yoneda.map f ≫ pairBase y₁ g₂ e₂) (fam y₁).toBase.hom (pairBase y₁ g₂ e₂)
          (fam y₁).toBase.hom (yoneda.map f) (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ κ y₁ g₂ e₂ := by
    apply (isPullback_pb y₁ g₂ e₂).hom_ext
    · simp only [Category.assoc, κ_fst]
      rw [reassoc_of% (totalMap_comp_toBase (pbRestrict y₁ H)), reassoc_of% (κ_toBase y₁ g₁ e₁),
        ← Functor.map_comp, ← Functor.map_comp, reassoc_of% hcomp, e₂.hom_inv_id,
        Category.comp_id]
      simp
    · simp only [Category.assoc, κ_snd]
      rw [← comp_totalMap_hom, pbRestrict_comp_pbMap, κ_snd]
      simp
  show κ y₁ g₁ e₁ ≫ (unshrink₂ y₁ y₂ (Functor.morRestrict _ y₁ y₂ H m)).totalMap.hom ≫
      (pbMap y₂ g₁).totalMap.hom = _ ≫ _ ≫ κ y₁ g₂ e₂ ≫ (unshrink₂ y₁ y₂ m).totalMap.hom ≫
      (pbMap y₂ g₂).totalMap.hom
  have h : (unshrink₂ y₁ y₂ (Functor.morRestrict _ y₁ y₂ H m)).totalMap.hom ≫
      (pbMap y₂ g₁).totalMap.hom = (pbRestrict y₁ H).totalMap.hom ≫
        (unshrink₂ y₁ y₂ m).totalMap.hom ≫ (pbMap y₂ g₂).totalMap.hom :=
    congrArg (fun k : pb y₁ g₁ ⟶ fam y₂ => k.totalMap.hom) (unshrink₂_morRestrict y₁ y₂ H m)
  rw [h, reassoc_of% hK]
  rfl

/-- **Distinct morphisms give distinct pairs.** -/
private theorem isoPair_injective (g : Over U) {W : BigFppfOver B integerBase hZ}
    (e : W ≅ (pb y₁ g).base) : Function.Injective (isoPair y₁ y₂ g e) := by
  intro m₁ m₂ h
  have h₁ : κ y₁ g e ≫ (unshrink₂ y₁ y₂ m₁).totalMap.hom ≫ (pbMap y₂ g).totalMap.hom =
      κ y₁ g e ≫ (unshrink₂ y₁ y₂ m₂).totalMap.hom ≫ (pbMap y₂ g).totalMap.hom := by
    rw [← isoPair_morphism, ← isoPair_morphism]
    exact eq_of_heq (congr_arg_heq Space.RelativeMorphism.morphism h)
  replace h₁ := (Iso.cancel_iso_inv_left _ _ _).1 h₁
  have ht : (unshrink₂ y₁ y₂ m₁).totalMap.hom = (unshrink₂ y₁ y₂ m₂).totalMap.hom :=
    (isPullback_totalMap_hom (pbMap y₂ g)).hom_ext h₁
      ((unshrink₂_totalMap_comp_toBase y₁ y₂ m₁).trans
        (unshrink₂_totalMap_comp_toBase y₁ y₂ m₂).symm)
  have hu : unshrink₂ y₁ y₂ m₁ = unshrink₂ y₁ y₂ m₂ :=
    CurveFamily.Hom.ext ((unshrink₂_baseMap y₁ y₂ m₁).trans (unshrink₂_baseMap y₁ y₂ m₂).symm)
      (ObjectProperty.hom_ext _ ht)
  exact Functor.Fiber.hom_ext (uns_injective hu)

/-- **Every relative isomorphism over `W` is the pair of a morphism of the fibre.** -/
private theorem exists_isoPair_eq (g : Over U) {W : BigFppfOver B integerBase hZ}
    (e : W ≅ (pb y₁ g).base)
    (r : Space.RelativeMorphism B integerBase hZ (fam y₁).total.obj (fam y₂).total.obj
      (schemeSpace (fam y₁).base).obj (fam y₁).toBase.hom (tgt y₁ y₂) (yoneda.obj W))
    (hr : r.IsRelativeIso) (hb : pairBase y₁ g e = r.base) :
    ∃ m, isoPair y₁ y₂ g e m = r := by
  let c := (pullback.congrHom hb (rfl : (fam y₁).toBase.hom = _)).hom
  let c' := (pullback.congrHom hb (rfl : tgt y₁ y₂ = _)).hom
  let σ := inv (κ y₁ g e) ≫ c ≫ r.morphism
  have hκsnd : inv (κ y₁ g e) ≫ pullback.snd _ _ = (pbMap y₁ g).totalMap.hom := by
    rw [IsIso.inv_comp_eq, κ_snd]
  have hc_snd : c ≫ pullback.snd _ _ = pullback.snd _ _ := by simp [c]
  have hc_fst : c ≫ pullback.fst _ _ = pullback.fst _ _ := by simp [c]
  have hc'_snd : c' ≫ pullback.snd _ _ = pullback.snd _ _ := by simp [c']
  have hc'_fst : c' ≫ pullback.fst _ _ = pullback.fst _ _ := by simp [c']
  have hσ' : σ ≫ tgt y₁ y₂ = (pb y₁ g).toBase.hom ≫ yoneda.map (pbMap y₁ g).baseMap := by
    show inv (κ y₁ g e) ≫ c ≫ r.morphism ≫ tgt y₁ y₂ = _
    rw [r.commutes, reassoc_of% hc_snd, reassoc_of% hκsnd]
    exact totalMap_comp_toBase (pbMap y₁ g)
  have hσ : σ ≫ (fam y₂).toBase.hom =
      ((pb y₁ g).toBase.hom ≫ yoneda.map (pbBaseIso y₁ y₂ g).hom) ≫
        yoneda.map (pbMap y₂ g).baseMap := by
    refine (cancel_mono (yoneda.map (φ₂₁ y₁ y₂))).1 ((Category.assoc _ _ _).trans (hσ'.trans ?_))
    simp only [Category.assoc, yoneda_map_pbBaseIso_comp]
  let t := (isPullback_totalMap_hom (pbMap y₂ g)).lift σ
    ((pb y₁ g).toBase.hom ≫ yoneda.map (pbBaseIso y₁ y₂ g).hom) hσ
  have ht₁ : t ≫ (pbMap y₂ g).totalMap.hom = σ := IsPullback.lift_fst _ _ _ _
  have ht₂ : t ≫ (pb y₂ g).toBase.hom =
      (pb y₁ g).toBase.hom ≫ yoneda.map (pbBaseIso y₁ y₂ g).hom :=
    IsPullback.lift_snd _ _ _ _
  have hc'inv_snd : inv c' ≫ pullback.snd _ _ = pullback.snd _ _ := by
    rw [IsIso.inv_comp_eq, hc'_snd]
  have hc'inv_fst : inv c' ≫ pullback.fst _ _ = pullback.fst _ _ := by
    rw [IsIso.inv_comp_eq, hc'_fst]
  have ht : t = inv (κ y₁ g e) ≫ c ≫ r.baseChangeMap ≫ inv c' ≫ κ₂ y₁ y₂ g e := by
    apply (isPullback_totalMap_hom (pbMap y₂ g)).hom_ext
    · rw [ht₁]
      simp only [Category.assoc]
      rw [κ₂_snd, hc'inv_snd, Space.RelativeMorphism.baseChangeMap_comp_snd]
    · rw [ht₂]
      simp only [Category.assoc]
      rw [κ₂_toBase, reassoc_of% hc'inv_fst, Space.RelativeMorphism.baseChangeMap_comp_fst_assoc,
        reassoc_of% hc_fst, Iso.trans_hom, Functor.map_comp, ← reassoc_of% (κ_toBase y₁ g e),
        IsIso.inv_hom_id_assoc]
  have : IsIso r.baseChangeMap := hr
  have : IsIso t := by
    rw [ht]
    infer_instance
  have hsq : IsPullback t (pb y₁ g).toBase.hom (pb y₂ g).toBase.hom
      (yoneda.map (pbBaseIso y₁ y₂ g).hom) :=
    IsPullback.of_horiz_isIso ⟨ht₂⟩
  let u : pb y₁ g ⟶ pb y₂ g :=
    { baseMap := (pbBaseIso y₁ y₂ g).hom
      totalMap := ObjectProperty.homMk t
      cartesian := hsq.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ hsq.w) }
  let m₀ : (Functor.pullbackFiber (curvesSmall B hZ).val.p y₁ g.hom).1 ⟶
      (Functor.pullbackFiber (curvesSmall B hZ).val.p y₂ g.hom).1 := equivShrink _ u
  have hm₀ : uns m₀ = u := (equivShrink _).symm_apply_apply u
  have hlift : (curvesSmall B hZ).val.p.IsHomLift (𝟙 g.left) m₀ := by
    refine IsHomLift.of_fac' _ (𝟙 g.left) m₀
      (Functor.pullbackFiber (curvesSmall B hZ).val.p y₁ g.hom).2
      (Functor.pullbackFiber (curvesSmall B hZ).val.p y₂ g.hom).2 ?_
    show (uns m₀).baseMap = _
    rw [hm₀, Category.id_comp, eqToHom_trans]
    rfl
  refine ⟨⟨m₀, hlift⟩, Space.RelativeMorphism.ext_of_base_eq hb ?_⟩
  show κ y₁ g e ≫ (uns m₀).totalMap.hom ≫ (pbMap y₂ g).totalMap.hom = c ≫ r.morphism
  rw [hm₀]
  show κ y₁ g e ≫ t ≫ (pbMap y₂ g).totalMap.hom = c ≫ r.morphism
  rw [ht₁, IsIso.hom_inv_id_assoc]

/-- The presheaf `Isom_𝒳(y₁, y₂)` on the site of `U`, viewed on the site of `Spec(ℤ)` over `U`
(Stacks 04SG). -/
private noncomputable abbrev isomRel₂ : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u :=
  (OverShriek.relocalizePresheafFunctor U.hom).obj
    (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂)

/-- The object of `𝒮/U` a section of `isomRel₂ y₁ y₂` over `W` lives over. -/
private noncomputable abbrev secObj₂ {W : BigFppfOver B integerBase hZ}
    (x : (isomRel₂ y₁ y₂).obj (op W)) : Over U :=
  (Over.iteratedSliceBackward U).obj (Over.mk x.1.1)

/-- The identification of `W` with the base of the chosen pullback of `y₁` a section lives on. -/
private noncomputable abbrev secIso₂ {W : BigFppfOver B integerBase hZ}
    (x : (isomRel₂ y₁ y₂).obj (op W)) : W ≅ (pb y₁ (secObj₂ y₁ y₂ x)).base :=
  secIso' y₁ x.1.1 (OverShriek.relocalizeFactors U.hom _ x)

/-- The component at `W` of the transport: a section `(ψ, m)` of `isomRel₂ y₁ y₂` goes to the
relative isomorphism of families over `W` that `m` is. -/
private noncomputable def toIsomApp (W : BigFppfOver B integerBase hZ)
    (x : (isomRel₂ y₁ y₂).obj (op W)) :
    (CurveFamily.isomFunctor (fam y₁) (fam y₂) (tgt y₁ y₂)).toFunctor.obj (op W) :=
  ⟨equivShrink _ (isoPair y₁ y₂ (secObj₂ y₁ y₂ x) (secIso₂ y₁ y₂ x) x.1.2.1), by
    refine (CurveFamily.mem_isomFunctor_iff _ _ _ _ _).2 ?_
    change Space.RelativeMorphism.IsRelativeIso ((equivShrink _).symm (equivShrink _ _))
    rw [Equiv.symm_apply_apply]
    have : IsIso x.1.2.1 := x.1.2.2
    exact isoPair_isRelativeIso y₁ y₂ _ _ _⟩

/-- The transport is natural. -/
private theorem toIsomApp_naturality {W W' : BigFppfOver B integerBase hZ} (f : W' ⟶ W)
    (x : (isomRel₂ y₁ y₂).obj (op W)) :
    toIsomApp y₁ y₂ W' ((isomRel₂ y₁ y₂).map f.op x) =
      (CurveFamily.isomFunctor (fam y₁) (fam y₂) (tgt y₁ y₂)).toFunctor.map f.op
        (toIsomApp y₁ y₂ W x) := by
  apply Subtype.ext
  show equivShrink _ (isoPair y₁ y₂ _ (secIso₂ y₁ y₂ ((isomRel₂ y₁ y₂).map f.op x)) _) =
    equivShrink _ (Space.RelativeMorphism.restrict (yoneda.map f)
      ((equivShrink _).symm (equivShrink _
        (isoPair y₁ y₂ (secObj₂ y₁ y₂ x) (secIso₂ y₁ y₂ x) x.1.2.1))))
  rw [Equiv.symm_apply_apply]
  congr 1
  exact isoPair_morRestrict y₁ y₂ _ f _ _ (secIso'_hom_pbRestrict y₁ f _ _ _ _
    (Over.homMk f.left rfl : Over.mk (f.left ≫ x.1.1) ⟶ Over.mk x.1.1) rfl) x.1.2.1

private theorem toIsomApp_injective (W : BigFppfOver B integerBase hZ) :
    Function.Injective (toIsomApp y₁ y₂ W) := by
  rintro ⟨⟨ψ₁, s₁⟩, h₁⟩ ⟨⟨ψ₂, s₂⟩, h₂⟩ hx
  have hp := (equivShrink _).injective (congrArg Subtype.val hx)
  have hb := congrArg Space.RelativeMorphism.base hp
  change pairBase y₁ _ (secIso' y₁ ψ₁ h₁) = pairBase y₁ _ (secIso' y₁ ψ₂ h₂) at hb
  replace hb := (pairBase_secIso' y₁ ψ₁ h₁).symm.trans (hb.trans (pairBase_secIso' y₁ ψ₂ h₂))
  obtain rfl : ψ₁ = ψ₂ := congrArg Over.Hom.left ((cancel_mono _).1 (yoneda.map_injective hb))
  obtain rfl : s₁ = s₂ := Subtype.ext (isoPair_injective y₁ y₂ _ _ hp)
  rfl

private theorem toIsomApp_surjective (W : BigFppfOver B integerBase hZ) :
    Function.Surjective (toIsomApp y₁ y₂ W) := by
  rintro ⟨s, hs⟩
  let r := (equivShrink _).symm s
  have hr : r.IsRelativeIso := (CurveFamily.mem_isomFunctor_iff _ _ _ _ _).1 hs
  let k₀ : W ⟶ (curvesSmall B hZ).val.p.obj y₁.1 := Yoneda.fullyFaithful.preimage r.base
  let k : W ⟶ U := k₀ ≫ eqToHom y₁.2
  have hb : pairBase y₁ _ (secIso' y₁ k.left (Over.w k)) = r.base := by
    rw [pairBase_secIso']
    rw [show (Over.homMk k.left (Over.w k) : W ⟶ U) = k from rfl]
    refine (congrArg yoneda.map (show (k₀ ≫ eqToHom y₁.2) ≫ eqToHom y₁.2.symm = k₀ by
        rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])).trans ?_
    exact Yoneda.fullyFaithful.map_preimage _
  obtain ⟨m, hm⟩ := exists_isoPair_eq y₁ y₂ _ (secIso' y₁ k.left (Over.w k)) r hr hb
  have := (curvesSmall B hZ).isFiberedInGroupoids.fiber_isGroupoid
    ((Over.iteratedSliceBackward U).obj (Over.mk k.left)).left
  refine ⟨OverShriek.relocalizeMk U.hom _ k.left ⟨m, (inferInstance : IsIso m)⟩ (Over.w k), ?_⟩
  apply Subtype.ext
  show equivShrink _ (isoPair y₁ y₂ _ (secIso' y₁ k.left (Over.w k)) m) = s
  rw [hm]
  exact (equivShrink _).apply_symm_apply s

/-- **The transport of Isom presheaves.** `Isom_𝒳(y₁, y₂)` on the site of `U`, viewed on the site
of `Spec(ℤ)` over `U` (Stacks 04SG), is the presheaf `Isom_U(Y, X)` of isomorphisms between the
families that `y₁` and `y₂` are. -/
private noncomputable def isomRelIsoIsomFunctor :
    isomRel₂ y₁ y₂ ≅ (CurveFamily.isomFunctor (fam y₁) (fam y₂) (tgt y₁ y₂)).toFunctor :=
  NatIso.ofComponents
    (fun W => (Equiv.ofBijective (toIsomApp y₁ y₂ W.unop)
      ⟨toIsomApp_injective y₁ y₂ W.unop, toIsomApp_surjective y₁ y₂ W.unop⟩).toIso)
    (fun {W W'} f => by
      ext x
      exact toIsomApp_naturality y₁ y₂ f.unop x)

private theorem isomRelIsoIsomFunctor_hom_comp_projection :
    (isomRelIsoIsomFunctor y₁ y₂).hom ≫
        CurveFamily.isomFunctorProjection (fam y₁) (fam y₂) (tgt y₁ y₂) =
      OverShriek.relocalizeToYoneda U.hom
          (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂) ≫
        yoneda.map (eqToHom y₁.2.symm) := by
  ext W x
  show yonedaEquiv (Space.RelativeMorphism.base ((equivShrink _).symm
      (equivShrink _ (isoPair y₁ y₂ _ (secIso₂ y₁ y₂ x) x.1.2.1)))) =
    (Over.homMk x.1.1 (OverShriek.relocalizeFactors U.hom _ x) : W.unop ⟶ U) ≫ eqToHom y₁.2.symm
  rw [Equiv.symm_apply_apply]
  show yonedaEquiv (pairBase y₁ _ (secIso' y₁ x.1.1 _)) = _
  rw [pairBase_secIso']
  exact yonedaEquiv_yoneda_map _

private theorem isomRelIsoIsomFunctor_inv_comp_projection :
    (isomRelIsoIsomFunctor y₁ y₂).inv ≫
        (OverShriek.relocalizeToYoneda U.hom
          (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂) ≫
        yoneda.map (eqToHom y₁.2.symm)) =
      CurveFamily.isomFunctorProjection (fam y₁) (fam y₂) (tgt y₁ y₂) ≫ 𝟙 _ :=
  (congrArg ((isomRelIsoIsomFunctor y₁ y₂).inv ≫ ·)
    (isomRelIsoIsomFunctor_hom_comp_projection y₁ y₂).symm).trans
      ((Iso.inv_hom_id_assoc _ _).trans (Category.comp_id _).symm)

/-- **The isomorphism space of two families of curves is `Isom_U(Y, X)`.** For objects `y₁` and
`y₂` of the small model of the stack of curves over `U`, i.e. families of curves `Y ⟶ U` and
`X ⟶ U`, the structure morphism of `Isom_𝒳(y₁, y₂)` over `U`, viewed on the big fppf site of
`Spec(ℤ)` (Stacks 04SG), is isomorphic as an arrow to the projection `Isom_U(Y, X) ⟶ U` of
Stacks 0DPP, the family `X` being read over the base of `Y` through the identification of both
with `U`. -/
theorem nonempty_arrowIso_isomFunctorProjection :
    Nonempty (Arrow.mk (OverShriek.relocalizeToYoneda U.hom
          (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂) ≫
        yoneda.map (eqToHom y₁.2.symm)) ≅
      Arrow.mk (CurveFamily.isomFunctorProjection
        (ShrinkHoms.fromShrinkHoms y₁.1 : CurveFamily B hZ)
        (ShrinkHoms.fromShrinkHoms y₂.1 : CurveFamily B hZ)
        ((ShrinkHoms.fromShrinkHoms y₂.1 : CurveFamily B hZ).toBase.hom ≫
          yoneda.map (eqToHom (y₂.2.trans y₁.2.symm))))) :=
  ⟨Arrow.isoMk (isomRelIsoIsomFunctor y₁ y₂) (Iso.refl _)
    ((isomRelIsoIsomFunctor_hom_comp_projection y₁ y₂).trans (Category.comp_id _).symm)⟩

/-- **`Isom_𝒳(y₁, y₂)` is separated over `U`.** For objects `y₁` and `y₂` of the small model of
the stack of curves over `U`, the structure morphism of the isomorphism space of Stacks 04YP,
viewed over `Spec(ℤ)` (Stacks 04SG), is separated: it is the projection `Isom_U(Y, X) ⟶ U`
(`AlgebraicGeometry.curvesSmall.nonempty_arrowIso_isomFunctorProjection`), which is separated by
Stacks 0DPN and 0DPP (`AlgebraicGeometry.CurveFamily.isSeparated_isomFunctorProjection`). This is
the separation step of the proof of Stacks 0DSQ. -/
theorem isSeparated_relocalizeToYoneda_isomSpace :
    Space.IsSeparated B integerBase hZ (OverShriek.relocalizeToYoneda U.hom
      (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂)) := by
  have hxp : Space.IsProper B integerBase hZ (tgt y₁ y₂) :=
    (Space.isProper_comp_isIso_iff B integerBase hZ _ (yoneda.map (φ₂₁ y₁ y₂))).2 (fam y₂).proper
  have hxfp : Space.IsFinitePresentation B integerBase hZ (tgt y₁ y₂) :=
    ⟨(Space.holdsOnEveryEtaleChart_comp_iso_iff B integerBase hZ _ _
        (yoneda.map (φ₂₁ y₁ y₂))).2
        (fam y₂).finitePresentation.1,
      (Space.isQuasiCompact_comp_isIso_iff B integerBase hZ _ (yoneda.map (φ₂₁ y₁ y₂))).2
        (fam y₂).finitePresentation.2.1,
      (Space.isQuasiSeparated_comp_isIso_iff B integerBase hZ _ (yoneda.map (φ₂₁ y₁ y₂))).2
        (fam y₂).finitePresentation.2.2⟩
  have hs := CurveFamily.isSeparated_isomFunctorProjection (fam y₁) (fam y₂) (tgt y₁ y₂) hxp hxfp
  have h' : Space.IsSeparated B integerBase hZ (OverShriek.relocalizeToYoneda U.hom
      (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂) ≫
        yoneda.map (eqToHom y₁.2.symm)) :=
    Space.isSeparated_of_arrowIso B integerBase hZ _ _ (isomRelIsoIsomFunctor y₁ y₂).inv (𝟙 _)
      (isomRelIsoIsomFunctor_inv_comp_projection y₁ y₂) hs
  have := Space.isSeparated_respectsIso B integerBase hZ
  exact (MorphismProperty.cancel_right_of_respectsIso
    (@Space.IsSeparated B integerBase hZ) _ _).1 h'

/-- **`Isom_𝒳(y₁, y₂)` is quasi-separated over `U`**, being separated (Stacks 03KK). -/
theorem isQuasiSeparated_relocalizeToYoneda_isomSpace :
    Space.IsQuasiSeparated B integerBase hZ (OverShriek.relocalizeToYoneda U.hom
      (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂)) :=
  Space.isQuasiSeparated_of_isSeparated B integerBase hZ
    (isSeparated_relocalizeToYoneda_isomSpace y₁ y₂)

/-- **Quasi-compactness of `Isom_𝒳(y₁, y₂)` is that of `Isom_U(Y, X)`.** For objects `y₁` and `y₂`
of the small model of the stack of curves over `U`, the structure morphism of the isomorphism
space of Stacks 04YP, viewed over `Spec(ℤ)` (Stacks 04SG), is quasi-compact as soon as the
projection `Isom_U(Y, X) ⟶ U` of Stacks 0DPP is
(`AlgebraicGeometry.curvesSmall.nonempty_arrowIso_isomFunctorProjection`). -/
theorem isQuasiCompact_relocalizeToYoneda_isomSpace_of
    (hqc : Space.IsQuasiCompact B integerBase hZ (CurveFamily.isomFunctorProjection
      (ShrinkHoms.fromShrinkHoms y₁.1 : CurveFamily B hZ)
      (ShrinkHoms.fromShrinkHoms y₂.1 : CurveFamily B hZ)
      ((ShrinkHoms.fromShrinkHoms y₂.1 : CurveFamily B hZ).toBase.hom ≫
        yoneda.map (eqToHom (y₂.2.trans y₁.2.symm))))) :
    Space.IsQuasiCompact B integerBase hZ (OverShriek.relocalizeToYoneda U.hom
      (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂)) := by
  have h' : Space.IsQuasiCompact B integerBase hZ (OverShriek.relocalizeToYoneda U.hom
      (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂) ≫
        yoneda.map (eqToHom y₁.2.symm)) :=
    Space.isQuasiCompact_of_arrowIso B integerBase hZ _ _ (isomRelIsoIsomFunctor y₁ y₂).inv (𝟙 _)
      (isomRelIsoIsomFunctor_inv_comp_projection y₁ y₂) hqc
  exact (Space.isQuasiCompact_comp_isIso_iff B integerBase hZ _
    (yoneda.map (eqToHom y₁.2.symm))).1 h'

end curvesSmall

end AlgebraicGeometry

end
