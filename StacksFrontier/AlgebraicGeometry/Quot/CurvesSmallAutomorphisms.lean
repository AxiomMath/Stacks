module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallModel
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyAutomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupGroundFieldExtension
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomGroupSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RestrictionOfScalarsCartesian

/-!
# The automorphism group space of a family of curves

Let `y` be an object of the small model `AlgebraicGeometry.curvesSmall` of the stack of curves
over a scheme `U` of the big fppf site of `Spec(ℤ)`, i.e. a family of curves `X ⟶ U` (Stacks
0D4Z). Two group-valued presheaves are attached to it:

* the automorphism group algebraic space `Isom_𝒳(y, y)` of Stacks 04YP
  (`AlgebraicGeometry.Stack.automorphismGroupSpace`), a presheaf on the big fppf site of `U`
  whose sections over `V ⟶ U` are the automorphisms of the pullback of `y` to `V` in the fibre
  of the stack; and
* the automorphism functor `Aut_U(X)` of the family (Stacks 0DPP, as used in Section 0DSR,
  `AlgebraicGeometry.CurveFamily.autFunctor`), a subpresheaf of the relative morphism functor of
  Stacks 05Y2 on the big fppf site of `Spec(ℤ)`, whose sections over `T` are the pairs `(a, b)`
  with `a : T ⟶ U` and `b` an automorphism of the base change `X_T` over `T`.

This file identifies the two: the structure morphism of `Isom_𝒳(y, y)`, viewed over `Spec(ℤ)`
along `U ⟶ Spec(ℤ)` (Stacks 04SG, `CategoryTheory.OverShriek.relocalizePresheafFunctor`), is
isomorphic as an arrow to the projection `Aut_U(X) ⟶ U`. Consequently every étale-local
property of the one is a property of the other.

## Main results

* `AlgebraicGeometry.curvesSmall.nonempty_arrowIso_autFunctorProjection`: the arrow isomorphism.
* `AlgebraicGeometry.curvesSmall.holdsOnEveryEtaleChart_automorphismGroupSpace_iff`: a property of
  morphisms of schemes holds on every étale chart of the automorphism group algebraic space of
  `y` over `U` exactly when it does for `Aut_U(X) ⟶ U` over `Spec(ℤ)`.
* `AlgebraicGeometry.curvesSmall.isUnramified_autFunctorProjection_of_hom`: unramifiedness of
  `Aut_U(X) ⟶ U` passes along morphisms of families.

## References

* [Stacks Project, Tag 04YP](https://stacks.math.columbia.edu/tag/04YP)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 05Y2](https://stacks.math.columbia.edu/tag/05Y2)
* [Stacks Project, Tag 0DPP](https://stacks.math.columbia.edu/tag/0DPP)
* [Stacks Project, Tag 0DSR](https://stacks.math.columbia.edu/tag/0DSR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace curvesSmall

/-- The cartesian square of a morphism of families of curves, read in presheaves
(`AlgebraicGeometry.AlgebraicSpaces.isPullback_hom`) with its base side written through Yoneda. -/
private theorem isPullback_totalMap_hom {G F : CurveFamily B hZ} (χ : G ⟶ F) :
    IsPullback χ.totalMap.hom G.toBase.hom F.toBase.hom (yoneda.map χ.baseMap) :=
  AlgebraicSpaces.isPullback_hom B integerBase hZ χ.cartesian

private theorem isFibered : (curvesSmall B hZ).val.p.IsFibered :=
  (curvesSmall B hZ).isFiberedInGroupoids.isFibered

attribute [local instance] isFibered locallySmall_curveFamily

attribute [local implicit_reducible] schemeSpace ShrinkHoms.fromShrinkHoms ShrinkHoms.inverse
  curvesSmall curvesSmallBased

variable {U : BigFppfOver B integerBase hZ} (y : (curvesSmall B hZ).val.p.Fiber U)

/-- A morphism of the small model, as a morphism of families of curves. -/
private noncomputable def uns {X Y : (curvesSmall B hZ).val.obj} (f : X ⟶ Y) :
    (ShrinkHoms.fromShrinkHoms X : CurveFamily B hZ) ⟶ ShrinkHoms.fromShrinkHoms Y :=
  (ShrinkHoms.inverse (CurveFamily B hZ)).map f

private theorem uns_comp {X Y Z : (curvesSmall B hZ).val.obj} (f : X ⟶ Y) (g : Y ⟶ Z) :
    uns (f ≫ g) = uns f ≫ uns g :=
  (ShrinkHoms.inverse (CurveFamily B hZ)).map_comp f g

private theorem uns_injective {X Y : (curvesSmall B hZ).val.obj} :
    Function.Injective (uns (X := X) (Y := Y)) :=
  (equivShrink _).symm.injective

private theorem isIso_uns {X Y : (curvesSmall B hZ).val.obj} (f : X ⟶ Y) [IsIso f] :
    IsIso (uns f) :=
  Functor.map_isIso (ShrinkHoms.inverse (CurveFamily B hZ)) f

/-- The chosen pullback of `y` along `g`, as a family of curves. -/
private noncomputable abbrev pb (g : Over U) : CurveFamily B hZ :=
  ShrinkHoms.fromShrinkHoms (Functor.pullbackFiber (curvesSmall B hZ).val.p y g.hom).1

/-- The chosen cartesian arrow from the pullback of `y` along `g`, as a morphism of families. -/
private noncomputable abbrev pbMap (g : Over U) :
    pb y g ⟶ (ShrinkHoms.fromShrinkHoms y.1 : CurveFamily B hZ) :=
  uns (Functor.IsPreFibered.pullbackMap y.2 g.hom)

/-- A morphism of the fibre over `g.left`, as an endomorphism of the family `pb y g`. -/
private noncomputable abbrev unshrink {g : Over U}
    (m : Functor.pullbackFiber (curvesSmall B hZ).val.p y g.hom ⟶
      Functor.pullbackFiber (curvesSmall B hZ).val.p y g.hom) : pb y g ⟶ pb y g :=
  uns m.1

/-- The base map of a morphism of the small model lying over `f`, read in the fibre. -/
private theorem eqToHom_uns_baseMap {X Y : (curvesSmall B hZ).val.obj} (φ : X ⟶ Y)
    {a b : BigFppfOver B integerBase hZ} (f : a ⟶ b) [(curvesSmall B hZ).val.p.IsHomLift f φ] :
    eqToHom (IsHomLift.domain_eq (curvesSmall B hZ).val.p f φ).symm ≫ (uns φ).baseMap =
      f ≫ eqToHom (IsHomLift.codomain_eq (curvesSmall B hZ).val.p f φ).symm := by
  have h := IsHomLift.fac' (curvesSmall B hZ).val.p f φ
  change (uns φ).baseMap = _ at h
  rw [h]
  exact (eqToHom_trans_assoc _ _ _).trans (by rw [eqToHom_refl]; exact Category.id_comp _)

private theorem pbMap_baseMap (g : Over U) :
    eqToHom (Functor.pullbackFiber (curvesSmall B hZ).val.p y g.hom).2.symm ≫
      (pbMap y g).baseMap = g.hom ≫ eqToHom y.2.symm :=
  eqToHom_uns_baseMap _ g.hom

private theorem unshrink_baseMap {g : Over U}
    (m : Functor.pullbackFiber (curvesSmall B hZ).val.p y g.hom ⟶
      Functor.pullbackFiber (curvesSmall B hZ).val.p y g.hom) :
    (unshrink y m).baseMap = 𝟙 _ := by
  have := m.2
  have h := (eqToHom_uns_baseMap m.1 (𝟙 g.left)).trans (Category.id_comp _)
  exact ((eqToHom_comp_iff _ _ _).1 h).trans ((eqToHom_trans _ _).trans (eqToHom_refl _ _))

/-- The family of curves underlying an object of the small model. -/
private noncomputable abbrev fam : CurveFamily B hZ := ShrinkHoms.fromShrinkHoms y.1

/-- The base of the pair attached to `e : W ≅ (pb y g).base`: the morphism `W ⟶ U`. -/
private noncomputable abbrev pairBase (g : Over U) {W : BigFppfOver B integerBase hZ}
    (e : W ≅ (pb y g).base) : yoneda.obj W ⟶ (schemeSpace (fam y).base).obj :=
  yoneda.map (e.hom ≫ (pbMap y g).baseMap)

/-- The cartesian square of `pbMap y g` in presheaves, with its base corner moved along an
isomorphism `e : W ≅ (pb y g).base`. -/
private theorem isPullback_pb (g : Over U) {W : BigFppfOver B integerBase hZ}
    (e : W ≅ (pb y g).base) :
    IsPullback ((pb y g).toBase.hom ≫ yoneda.map e.inv) (pbMap y g).totalMap.hom
      (pairBase y g e) (fam y).toBase.hom :=
  (isPullback_totalMap_hom (pbMap y g)).flip.of_iso (Iso.refl _)
    (yoneda.mapIso e.symm) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
    (by simp [Functor.map_comp]) (by simp)

/-- The identification of the base change of `fam y` along `W ⟶ fam y` with `pb y g`. -/
private noncomputable abbrev κ (g : Over U) {W : BigFppfOver B integerBase hZ}
    (e : W ≅ (pb y g).base) :
    pullback (pairBase y g e) (fam y).toBase.hom ⟶
      (pb y g).total.obj :=
  (isPullback_pb y g e).isoPullback.inv

private theorem κ_fst (g : Over U) {W : BigFppfOver B integerBase hZ} (e : W ≅ (pb y g).base) :
    κ y g e ≫ (pb y g).toBase.hom ≫ yoneda.map e.inv = pullback.fst _ _ :=
  IsPullback.isoPullback_inv_fst _

private theorem κ_snd (g : Over U) {W : BigFppfOver B integerBase hZ} (e : W ≅ (pb y g).base) :
    κ y g e ≫ (pbMap y g).totalMap.hom = pullback.snd _ _ :=
  IsPullback.isoPullback_inv_snd _

private theorem unshrink_totalMap_comp_toBase {g : Over U}
    (m : Functor.pullbackFiber (curvesSmall B hZ).val.p y g.hom ⟶
      Functor.pullbackFiber (curvesSmall B hZ).val.p y g.hom) :
    (unshrink y m).totalMap.hom ≫ (pb y g).toBase.hom = (pb y g).toBase.hom := by
  have h := (isPullback_totalMap_hom (unshrink y m)).w
  rw [unshrink_baseMap, CategoryTheory.Functor.map_id] at h
  exact h.trans (Category.comp_id _)

/-- The pair of Stacks 05Y1 attached to an automorphism `m` of the chosen pullback of `y` along
`g`: its base is the morphism `W ⟶ U` and its second component is `m` followed by the cartesian
arrow to `y`, read on the base change of `fam y`. -/
private noncomputable def pair (g : Over U) {W : BigFppfOver B integerBase hZ}
    (e : W ≅ (pb y g).base)
    (m : Functor.pullbackFiber (curvesSmall B hZ).val.p y g.hom ⟶
      Functor.pullbackFiber (curvesSmall B hZ).val.p y g.hom) :
    Space.RelativeMorphism B integerBase hZ (fam y).total.obj (fam y).total.obj
      (schemeSpace (fam y).base).obj (fam y).toBase.hom (fam y).toBase.hom (yoneda.obj W) where
  base := pairBase y g e
  morphism := κ y g e ≫ (unshrink y m).totalMap.hom ≫ (pbMap y g).totalMap.hom
  commutes := by
    have h1 := (isPullback_totalMap_hom (pbMap y g)).w
    simp only [Category.assoc, h1, reassoc_of% (unshrink_totalMap_comp_toBase y m)]
    rw [← h1, reassoc_of% (κ_snd y g e)]

attribute [local implicit_reducible] pair

private theorem pair_baseChangeMap_comp_κ (g : Over U) {W : BigFppfOver B integerBase hZ}
    (e : W ≅ (pb y g).base)
    (m : Functor.pullbackFiber (curvesSmall B hZ).val.p y g.hom ⟶
      Functor.pullbackFiber (curvesSmall B hZ).val.p y g.hom) :
    (pair y g e m).baseChangeMap ≫ κ y g e = κ y g e ≫ (unshrink y m).totalMap.hom := by
  apply (isPullback_pb y g e).hom_ext
  · simp only [Category.assoc, κ_fst, reassoc_of% (unshrink_totalMap_comp_toBase y m)]
    exact Space.RelativeMorphism.baseChangeMap_comp_fst _
  · simp only [Category.assoc, κ_snd]
    exact Space.RelativeMorphism.baseChangeMap_comp_snd _

private theorem isIso_totalMap {X Y : CurveFamily B hZ} (f : X ⟶ Y) [IsIso f] :
    IsIso f.totalMap.hom :=
  ⟨(inv f).totalMap.hom,
    congrArg (fun k : X ⟶ X => k.totalMap.hom) (IsIso.hom_inv_id f),
    congrArg (fun k : Y ⟶ Y => k.totalMap.hom) (IsIso.inv_hom_id f)⟩

private theorem pair_isRelativeIso (g : Over U) {W : BigFppfOver B integerBase hZ}
    (e : W ≅ (pb y g).base)
    (m : Functor.pullbackFiber (curvesSmall B hZ).val.p y g.hom ⟶
      Functor.pullbackFiber (curvesSmall B hZ).val.p y g.hom) [IsIso m] :
    (pair y g e m).IsRelativeIso := by
  have : IsIso m.1 := inferInstanceAs (IsIso (Functor.Fiber.fiberInclusion.map m))
  have : IsIso (unshrink y m) := isIso_uns m.1
  have := isIso_totalMap (unshrink y m)
  have h : (pair y g e m).baseChangeMap =
      κ y g e ≫ (unshrink y m).totalMap.hom ≫ inv (κ y g e) := by
    rw [← reassoc_of% (pair_baseChangeMap_comp_κ y g e m), IsIso.hom_inv_id, Category.comp_id]
  change IsIso (pair y g e m).baseChangeMap
  rw [h]
  infer_instance

/-- The restriction map of the chosen pullbacks of `y`, as a morphism of families. -/
private noncomputable abbrev pbRestrict {g₁ g₂ : Over U} (H : g₁ ⟶ g₂) : pb y g₁ ⟶ pb y g₂ :=
  uns (Functor.pullbackFiberMap _ y H)

private theorem pbRestrict_comp_pbMap {g₁ g₂ : Over U} (H : g₁ ⟶ g₂) :
    pbRestrict y H ≫ pbMap y g₂ = pbMap y g₁ :=
  (uns_comp _ _).symm.trans (congrArg uns (Functor.pullbackFiberMap_fac _ y H))

private theorem pbRestrict_baseMap {g₁ g₂ : Over U} (H : g₁ ⟶ g₂) :
    eqToHom (Functor.pullbackFiber (curvesSmall B hZ).val.p y g₁.hom).2.symm ≫
      (pbRestrict y H).baseMap =
      H.left ≫ eqToHom (Functor.pullbackFiber (curvesSmall B hZ).val.p y g₂.hom).2.symm :=
  eqToHom_uns_baseMap _ H.left

private theorem unshrink_morRestrict {g₁ g₂ : Over U} (H : g₁ ⟶ g₂)
    (m : Functor.pullbackFiber (curvesSmall B hZ).val.p y g₂.hom ⟶
      Functor.pullbackFiber (curvesSmall B hZ).val.p y g₂.hom) :
    unshrink y (Functor.morRestrict _ y y H m) ≫ pbMap y g₁ =
      pbRestrict y H ≫ unshrink y m ≫ pbMap y g₂ := by
  have h := congrArg uns (Functor.morRestrict_fac _ y y H m)
  exact (uns_comp _ _).symm.trans (h.trans ((uns_comp _ _).trans
    (congrArg (uns (Functor.pullbackFiberMap _ y H) ≫ ·) (uns_comp _ _))))

private theorem κ_toBase (g : Over U) {W : BigFppfOver B integerBase hZ}
    (e : W ≅ (pb y g).base) :
    κ y g e ≫ (pb y g).toBase.hom = pullback.fst _ _ ≫ yoneda.map e.hom := by
  calc κ y g e ≫ (pb y g).toBase.hom
      = κ y g e ≫ (pb y g).toBase.hom ≫ yoneda.map (e.inv ≫ e.hom) := by
        rw [e.inv_hom_id, CategoryTheory.Functor.map_id]
        rfl
    _ = pullback.fst _ _ ≫ yoneda.map e.hom := by
        rw [Functor.map_comp, ← κ_fst y g e]
        simp only [Category.assoc]

private theorem comp_totalMap_hom {X Y Z : CurveFamily B hZ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).totalMap.hom = f.totalMap.hom ≫ g.totalMap.hom :=
  rfl

private theorem totalMap_comp_toBase {X Y : CurveFamily B hZ} (f : X ⟶ Y) :
    f.totalMap.hom ≫ Y.toBase.hom = X.toBase.hom ≫ yoneda.map f.baseMap :=
  (isPullback_totalMap_hom f).w

/-- **Naturality of the pairs.** Restricting the pair of `m` along `f : W₁ ⟶ W₂` is the pair of
the restriction of `m`. -/
private theorem pair_morRestrict {g₁ g₂ : Over U} (H : g₁ ⟶ g₂)
    {W₁ W₂ : BigFppfOver B integerBase hZ}
    (f : W₁ ⟶ W₂) (e₁ : W₁ ≅ (pb y g₁).base) (e₂ : W₂ ≅ (pb y g₂).base)
    (hcomp : e₁.hom ≫ (pbRestrict y H).baseMap = f ≫ e₂.hom)
    (m : Functor.pullbackFiber (curvesSmall B hZ).val.p y g₂.hom ⟶
      Functor.pullbackFiber (curvesSmall B hZ).val.p y g₂.hom) :
    pair y g₁ e₁ (Functor.morRestrict _ y y H m) =
      Space.RelativeMorphism.restrict (yoneda.map f) (pair y g₂ e₂ m) := by
  have hb : pairBase y g₁ e₁ = yoneda.map f ≫ pairBase y g₂ e₂ := by
    change yoneda.map (e₁.hom ≫ (pbMap y g₁).baseMap) =
      yoneda.map f ≫ yoneda.map (e₂.hom ≫ (pbMap y g₂).baseMap)
    rw [← pbRestrict_comp_pbMap y H]
    change yoneda.map (e₁.hom ≫ (pbRestrict y H).baseMap ≫ (pbMap y g₂).baseMap) =
      yoneda.map f ≫ yoneda.map (e₂.hom ≫ (pbMap y g₂).baseMap)
    rw [← Functor.map_comp, reassoc_of% hcomp]
  refine Space.RelativeMorphism.ext_of_base_eq hb ?_
  have hK : κ y g₁ e₁ ≫ (pbRestrict y H).totalMap.hom =
      (pullback.congrHom hb rfl).hom ≫
        pullback.map (yoneda.map f ≫ pairBase y g₂ e₂) (fam y).toBase.hom (pairBase y g₂ e₂)
          (fam y).toBase.hom (yoneda.map f) (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ κ y g₂ e₂ := by
    apply (isPullback_pb y g₂ e₂).hom_ext
    · simp only [Category.assoc, κ_fst]
      rw [reassoc_of% (totalMap_comp_toBase (pbRestrict y H)), reassoc_of% (κ_toBase y g₁ e₁),
        ← Functor.map_comp, ← Functor.map_comp, reassoc_of% hcomp, e₂.hom_inv_id,
        Category.comp_id]
      simp
    · simp only [Category.assoc, κ_snd]
      rw [← comp_totalMap_hom, pbRestrict_comp_pbMap, κ_snd]
      simp
  change κ y g₁ e₁ ≫ (unshrink y (Functor.morRestrict _ y y H m)).totalMap.hom ≫
      (pbMap y g₁).totalMap.hom = _ ≫ _ ≫ κ y g₂ e₂ ≫ (unshrink y m).totalMap.hom ≫
      (pbMap y g₂).totalMap.hom
  have h : (unshrink y (Functor.morRestrict _ y y H m)).totalMap.hom ≫ (pbMap y g₁).totalMap.hom =
      (pbRestrict y H).totalMap.hom ≫ (unshrink y m).totalMap.hom ≫ (pbMap y g₂).totalMap.hom :=
    congrArg (fun k : pb y g₁ ⟶ fam y => k.totalMap.hom) (unshrink_morRestrict y H m)
  rw [h, reassoc_of% hK]
  rfl

private theorem pair_morphism (g : Over U) {W : BigFppfOver B integerBase hZ}
    (e : W ≅ (pb y g).base)
    (m : Functor.pullbackFiber (curvesSmall B hZ).val.p y g.hom ⟶
      Functor.pullbackFiber (curvesSmall B hZ).val.p y g.hom) :
    (pair y g e m).morphism = κ y g e ≫ (unshrink y m).totalMap.hom ≫ (pbMap y g).totalMap.hom :=
  rfl

/-- **Distinct automorphisms give distinct pairs.** -/
private theorem pair_injective (g : Over U) {W : BigFppfOver B integerBase hZ}
    (e : W ≅ (pb y g).base) : Function.Injective (pair y g e) := by
  intro m₁ m₂ h
  have h₁ : κ y g e ≫ (unshrink y m₁).totalMap.hom ≫ (pbMap y g).totalMap.hom =
      κ y g e ≫ (unshrink y m₂).totalMap.hom ≫ (pbMap y g).totalMap.hom := by
    rw [← pair_morphism, ← pair_morphism]
    exact eq_of_heq (congr_arg_heq Space.RelativeMorphism.morphism h)
  simp only [Iso.cancel_iso_inv_left] at h₁
  have ht : (unshrink y m₁).totalMap.hom = (unshrink y m₂).totalMap.hom :=
    (isPullback_totalMap_hom (pbMap y g)).hom_ext h₁
      ((unshrink_totalMap_comp_toBase y m₁).trans (unshrink_totalMap_comp_toBase y m₂).symm)
  have hu : unshrink y m₁ = unshrink y m₂ :=
    CurveFamily.Hom.ext ((unshrink_baseMap y m₁).trans (unshrink_baseMap y m₂).symm)
      (ObjectProperty.hom_ext _ ht)
  exact Functor.Fiber.hom_ext (uns_injective hu)

/-- **Every relative automorphism over `W` is the pair of an automorphism.** -/
private theorem exists_pair_eq (g : Over U) {W : BigFppfOver B integerBase hZ}
    (e : W ≅ (pb y g).base)
    (r : Space.RelativeMorphism B integerBase hZ (fam y).total.obj (fam y).total.obj
      (schemeSpace (fam y).base).obj (fam y).toBase.hom (fam y).toBase.hom (yoneda.obj W))
    (hr : r.IsRelativeIso) (hb : pairBase y g e = r.base) :
    ∃ m, pair y g e m = r := by
  let c := (pullback.congrHom hb (rfl : (fam y).toBase.hom = _)).hom
  let σ := inv (κ y g e) ≫ c ≫ r.morphism
  have hκsnd : inv (κ y g e) ≫ pullback.snd _ _ = (pbMap y g).totalMap.hom := by
    rw [IsIso.inv_comp_eq, κ_snd]
  have hc_snd : c ≫ pullback.snd _ _ = pullback.snd _ _ := by simp [c]
  have hc_fst : c ≫ pullback.fst _ _ = pullback.fst _ _ := by simp [c]
  have hσ : σ ≫ (fam y).toBase.hom = (pb y g).toBase.hom ≫ yoneda.map (pbMap y g).baseMap := by
    change inv (κ y g e) ≫ c ≫ r.morphism ≫ (fam y).toBase.hom = _
    rw [r.commutes, reassoc_of% hc_snd, reassoc_of% hκsnd]
    exact totalMap_comp_toBase (pbMap y g)
  let t := (isPullback_totalMap_hom (pbMap y g)).lift σ (pb y g).toBase.hom hσ
  have ht₁ : t ≫ (pbMap y g).totalMap.hom = σ := IsPullback.lift_fst _ _ _ _
  have ht₂ : t ≫ (pb y g).toBase.hom = (pb y g).toBase.hom := IsPullback.lift_snd _ _ _ _
  have hcinv_snd : inv c ≫ pullback.snd _ _ = pullback.snd _ _ := by
    rw [IsIso.inv_comp_eq, hc_snd]
  have hcinv_fst : inv c ≫ pullback.fst _ _ = pullback.fst _ _ := by
    rw [IsIso.inv_comp_eq, hc_fst]
  have ht : t = inv (κ y g e) ≫ c ≫ r.baseChangeMap ≫ inv c ≫ κ y g e := by
    apply (isPullback_totalMap_hom (pbMap y g)).hom_ext
    · rw [ht₁]
      simp only [Category.assoc]
      rw [κ_snd, hcinv_snd, Space.RelativeMorphism.baseChangeMap_comp_snd]
    · rw [ht₂]
      simp only [Category.assoc]
      rw [κ_toBase, reassoc_of% hcinv_fst, Space.RelativeMorphism.baseChangeMap_comp_fst_assoc,
        reassoc_of% hc_fst, ← κ_toBase, IsIso.inv_hom_id_assoc]
  have : IsIso r.baseChangeMap := hr
  have : IsIso t := by
    rw [ht]
    infer_instance
  have hsq : IsPullback t (pb y g).toBase.hom (pb y g).toBase.hom (yoneda.map (𝟙 (pb y g).base)) :=
    IsPullback.of_horiz_isIso ⟨by rw [ht₂, CategoryTheory.Functor.map_id]; rfl⟩
  let u : pb y g ⟶ pb y g :=
    { baseMap := 𝟙 _
      totalMap := ObjectProperty.homMk t
      cartesian := hsq.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ hsq.w) }
  let m₀ : (Functor.pullbackFiber (curvesSmall B hZ).val.p y g.hom).1 ⟶
      (Functor.pullbackFiber (curvesSmall B hZ).val.p y g.hom).1 := equivShrink _ u
  have hm₀ : uns m₀ = u := (equivShrink _).symm_apply_apply u
  have hlift : (curvesSmall B hZ).val.p.IsHomLift (𝟙 g.left) m₀ := by
    refine IsHomLift.of_fac' _ (𝟙 g.left) m₀
      (Functor.pullbackFiber (curvesSmall B hZ).val.p y g.hom).2
      (Functor.pullbackFiber (curvesSmall B hZ).val.p y g.hom).2 ?_
    change (uns m₀).baseMap = _
    rw [hm₀, Category.id_comp, eqToHom_trans, eqToHom_refl]
    rfl
  refine ⟨⟨m₀, hlift⟩, Space.RelativeMorphism.ext_of_base_eq hb ?_⟩
  change κ y g e ≫ (uns m₀).totalMap.hom ≫ (pbMap y g).totalMap.hom = c ≫ r.morphism
  rw [hm₀]
  change κ y g e ≫ t ≫ (pbMap y g).totalMap.hom = c ≫ r.morphism
  rw [ht₁, IsIso.hom_inv_id_assoc]

/-- The presheaf `Isom_𝒳(y, y)` on the site of `U`, viewed on the site of `Spec(ℤ)` over `U`
(Stacks 04SG). -/
private noncomputable abbrev isomRel : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u :=
  (OverShriek.relocalizePresheafFunctor U.hom).obj
    (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y y)

/-- The object of `𝒮/U` a section of `isomRel y` over `W` lives over. -/
private noncomputable abbrev secObj {W : BigFppfOver B integerBase hZ}
    (x : (isomRel y).obj (op W)) : Over U :=
  (Over.iteratedSliceBackward U).obj (Over.mk x.1.1)

/-- The identification of `W` with the base of the chosen pullback along `ψ : W ⟶ U`. -/
private noncomputable def secIso' {W : BigFppfOver B integerBase hZ} (ψ : W.left ⟶ U.left)
    (h : ψ ≫ U.hom = W.hom) :
    W ≅ (pb y ((Over.iteratedSliceBackward U).obj (Over.mk ψ))).base :=
  Over.isoMk (f := W) (g := ((Over.iteratedSliceBackward U).obj (Over.mk ψ)).left)
    (Iso.refl W.left) (by
    change 𝟙 _ ≫ ψ ≫ U.hom = W.hom
    exact (Category.id_comp _).trans h) ≪≫
  eqToIso (Functor.pullbackFiber (curvesSmall B hZ).val.p y
    ((Over.iteratedSliceBackward U).obj (Over.mk ψ)).hom).2.symm

private theorem secIso'_hom_pbRestrict {W W' : BigFppfOver B integerBase hZ} (f : W' ⟶ W)
    (ψ₁ : W'.left ⟶ U.left) (h₁ : ψ₁ ≫ U.hom = W'.hom) (ψ₂ : W.left ⟶ U.left)
    (h₂ : ψ₂ ≫ U.hom = W.hom) (k : Over.mk ψ₁ ⟶ Over.mk ψ₂) (hk : k.left = f.left) :
    (secIso' y ψ₁ h₁).hom ≫ (pbRestrict y ((Over.iteratedSliceBackward U).map k)).baseMap =
      f ≫ (secIso' y ψ₂ h₂).hom := by
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (pbRestrict_baseMap y ((Over.iteratedSliceBackward U).map k))).trans ?_)
  have hleft : (Over.isoMk (f := W') (g := ((Over.iteratedSliceBackward U).obj (Over.mk ψ₁)).left)
      (Iso.refl W'.left) (by
        change 𝟙 _ ≫ ψ₁ ≫ U.hom = W'.hom
        exact (Category.id_comp _).trans h₁)).hom ≫
        ((Over.iteratedSliceBackward U).map k).left =
      f ≫ (Over.isoMk (f := W) (g := ((Over.iteratedSliceBackward U).obj (Over.mk ψ₂)).left)
        (Iso.refl W.left) (by
          change 𝟙 _ ≫ ψ₂ ≫ U.hom = W.hom
          exact (Category.id_comp _).trans h₂)).hom := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left]
    exact hk
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ eqToHom _) hleft).trans
    (Category.assoc _ _ _))

/-- The identification of `W` with the base of the chosen pullback a section lives on. -/
private noncomputable abbrev secIso {W : BigFppfOver B integerBase hZ}
    (x : (isomRel y).obj (op W)) : W ≅ (pb y (secObj y x)).base :=
  secIso' y x.1.1 (OverShriek.relocalizeFactors U.hom _ x)

/-- The component at `W` of the transport: a section `(ψ, m)` of `isomRel y` goes to the relative
automorphism of `fam y` over `W` that `m` is. -/
private noncomputable def toAutApp (W : BigFppfOver B integerBase hZ)
    (x : (isomRel y).obj (op W)) : (CurveFamily.autFunctor (fam y)).toFunctor.obj (op W) :=
  ⟨equivShrink _ (pair y (secObj y x) (secIso y x) x.1.2.1), by
    refine (CurveFamily.mem_isomFunctor_iff _ _ _ _ _).2 ?_
    change Space.RelativeMorphism.IsRelativeIso ((equivShrink _).symm (equivShrink _ _))
    rw [Equiv.symm_apply_apply]
    have : IsIso x.1.2.1 := x.1.2.2
    exact pair_isRelativeIso y _ _ _⟩

/-- The transport is natural. -/
private theorem toAutApp_naturality {W W' : BigFppfOver B integerBase hZ} (f : W' ⟶ W)
    (x : (isomRel y).obj (op W)) :
    toAutApp y W' ((isomRel y).map f.op x) =
      (CurveFamily.autFunctor (fam y)).toFunctor.map f.op (toAutApp y W x) := by
  apply Subtype.ext
  change equivShrink _ (pair y _ (secIso y ((isomRel y).map f.op x)) _) =
    equivShrink _ (Space.RelativeMorphism.restrict (yoneda.map f)
      ((equivShrink _).symm (equivShrink _ (pair y (secObj y x) (secIso y x) x.1.2.1))))
  rw [Equiv.symm_apply_apply]
  congr 1
  exact pair_morRestrict y _ f _ _ (secIso'_hom_pbRestrict y f _ _ _ _
    (Over.homMk f.left rfl : Over.mk (f.left ≫ x.1.1) ⟶ Over.mk x.1.1) rfl) x.1.2.1

private theorem secIso'_hom_pbMap {W : BigFppfOver B integerBase hZ} (ψ : W.left ⟶ U.left)
    (h : ψ ≫ U.hom = W.hom) :
    (secIso' y ψ h).hom ≫ (pbMap y ((Over.iteratedSliceBackward U).obj (Over.mk ψ))).baseMap =
      (Over.homMk ψ h : W ⟶ U) ≫ eqToHom y.2.symm := by
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (pbMap_baseMap y ((Over.iteratedSliceBackward U).obj (Over.mk ψ)))).trans ?_)
  refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ eqToHom _) ?_)
  apply Over.OverMorphism.ext
  simp only [Over.comp_left]
  rfl

private theorem pairBase_secIso' {W : BigFppfOver B integerBase hZ} (ψ : W.left ⟶ U.left)
    (h : ψ ≫ U.hom = W.hom) :
    pairBase y _ (secIso' y ψ h) = yoneda.map ((Over.homMk ψ h : W ⟶ U) ≫ eqToHom y.2.symm) :=
  congrArg yoneda.map (secIso'_hom_pbMap y ψ h)

private theorem toAutApp_injective (W : BigFppfOver B integerBase hZ) :
    Function.Injective (toAutApp y W) := by
  rintro ⟨⟨ψ₁, s₁⟩, h₁⟩ ⟨⟨ψ₂, s₂⟩, h₂⟩ hx
  have hp := (equivShrink _).injective (congrArg Subtype.val hx)
  have hb := congrArg Space.RelativeMorphism.base hp
  change pairBase y _ (secIso' y ψ₁ h₁) = pairBase y _ (secIso' y ψ₂ h₂) at hb
  replace hb := (pairBase_secIso' y ψ₁ h₁).symm.trans (hb.trans (pairBase_secIso' y ψ₂ h₂))
  obtain rfl : ψ₁ = ψ₂ :=
    congrArg Over.Hom.left ((cancel_mono _).1 (yoneda.map_injective hb))
  obtain rfl : s₁ = s₂ := Subtype.ext (pair_injective y _ _ hp)
  rfl

private theorem toAutApp_surjective (W : BigFppfOver B integerBase hZ) :
    Function.Surjective (toAutApp y W) := by
  rintro ⟨s, hs⟩
  let r := (equivShrink _).symm s
  have hr : r.IsRelativeIso := (CurveFamily.mem_isomFunctor_iff _ _ _ _ _).1 hs
  let k₀ : W ⟶ (curvesSmall B hZ).val.p.obj y.1 := Yoneda.fullyFaithful.preimage r.base
  let k : W ⟶ U := k₀ ≫ eqToHom y.2
  have hb : pairBase y _ (secIso' y k.left (Over.w k)) = r.base := by
    rw [pairBase_secIso', show (Over.homMk k.left (Over.w k) : W ⟶ U) = k from rfl]
    refine (congrArg yoneda.map (show (k₀ ≫ eqToHom y.2) ≫ eqToHom y.2.symm = k₀ by
        rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])).trans ?_
    exact Yoneda.fullyFaithful.map_preimage _
  obtain ⟨m, hm⟩ := exists_pair_eq y _ (secIso' y k.left (Over.w k)) r hr hb
  have := (curvesSmall B hZ).isFiberedInGroupoids.fiber_isGroupoid
    ((Over.iteratedSliceBackward U).obj (Over.mk k.left)).left
  refine ⟨OverShriek.relocalizeMk U.hom _ k.left ⟨m, (inferInstance : IsIso m)⟩ (Over.w k), ?_⟩
  apply Subtype.ext
  change equivShrink _ (pair y _ (secIso' y k.left (Over.w k)) m) = s
  rw [hm]
  exact (equivShrink _).apply_symm_apply s

/-- **The transport of Isom presheaves.** `Isom_𝒳(y, y)` on the site of `U`, viewed on the site of
`Spec(ℤ)` over `U` (Stacks 04SG), is the presheaf `Aut_U(X)` of automorphisms of the family `X`
that `y` is. -/
private noncomputable def isomRelIsoAutFunctor :
    isomRel y ≅ (CurveFamily.autFunctor (fam y)).toFunctor :=
  NatIso.ofComponents
    (fun W => (Equiv.ofBijective (toAutApp y W.unop)
      ⟨toAutApp_injective y W.unop, toAutApp_surjective y W.unop⟩).toIso)
    (fun {W W'} f => by
      ext x
      exact toAutApp_naturality y f.unop x)

private theorem isomRelIsoAutFunctor_hom_comp_projection :
    (isomRelIsoAutFunctor y).hom ≫ CurveFamily.autFunctorProjection (fam y) =
      OverShriek.relocalizeToYoneda U.hom
          (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y y) ≫
        yoneda.map (eqToHom y.2.symm) := by
  ext W x
  change yonedaEquiv (Space.RelativeMorphism.base ((equivShrink _).symm
      (equivShrink _ (pair y _ (secIso y x) x.1.2.1)))) =
    (Over.homMk x.1.1 (OverShriek.relocalizeFactors U.hom _ x) : W.unop ⟶ U) ≫ eqToHom y.2.symm
  rw [Equiv.symm_apply_apply]
  change yonedaEquiv (pairBase y _ (secIso' y x.1.1 _)) = _
  rw [pairBase_secIso']
  exact yonedaEquiv_yoneda_map _

/-- **The automorphism group space of a family of curves is `Aut_U(X)`.** For an object `y` of
the small model of the stack of curves over `U`, i.e. a family of curves `X ⟶ U`, the structure
morphism of `Isom_𝒳(y, y)` over `U`, viewed on the big fppf site of `Spec(ℤ)` (Stacks 04SG), is
isomorphic as an arrow to the projection `Aut_U(X) ⟶ U` of the automorphism functor of the
family (Stacks 0DPP): an automorphism of the pullback of `y` to `V ⟶ U` in the small model is an
automorphism of the base change `X_V` over `V`. -/
theorem nonempty_arrowIso_autFunctorProjection :
    Nonempty (Arrow.mk (OverShriek.relocalizeToYoneda U.hom
          (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y y) ≫
        yoneda.map (eqToHom y.2.symm)) ≅
      Arrow.mk (CurveFamily.autFunctorProjection
        (ShrinkHoms.fromShrinkHoms y.1 : CurveFamily B hZ))) :=
  ⟨Arrow.isoMk (isomRelIsoAutFunctor y) (Iso.refl _)
    ((isomRelIsoAutFunctor_hom_comp_projection y).trans (Category.comp_id _).symm)⟩

private theorem pair_id (g : Over U) {W : BigFppfOver B integerBase hZ}
    (e : W ≅ (pb y g).base) :
    pair y g e (𝟙 _) = Space.RelativeMorphism.identity _ (pairBase y g e) := by
  refine Space.RelativeMorphism.mk_eq_mk ?_
  have h1 : (unshrink y (𝟙 (Functor.pullbackFiber (curvesSmall B hZ).val.p y g.hom))) = 𝟙 _ :=
    (ShrinkHoms.inverse (CurveFamily B hZ)).map_id _
  change κ y g e ≫ (unshrink y (𝟙 _)).totalMap.hom ≫ (pbMap y g).totalMap.hom = pullback.snd _ _
  rw [h1]
  exact (congrArg (κ y g e ≫ ·) (Category.id_comp _)).trans (κ_snd y g e)

/-- **The transport of `Isom_𝒳(y, y)` to `Aut_U(X)`, with its two properties.** `Isom_𝒳(y, y)`
on the site of `U`, viewed on the site of `Spec(ℤ)` over `U` (Stacks 04SG), is isomorphic to the
presheaf `Aut_U(X)` of automorphisms of the family `X` that `y` is, by an isomorphism lying over
`U` which sends a section `(ψ, m)` whose automorphism `m` is the identity to the identity
automorphism of the base change of `X` along `ψ`. -/
theorem exists_isomSpaceRelocalizeIso_autFunctor :
    ∃ e : (OverShriek.relocalizePresheafFunctor U.hom).obj
        (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y y) ≅
      (CurveFamily.autFunctor (ShrinkHoms.fromShrinkHoms y.1 : CurveFamily B hZ)).toFunctor,
      e.hom ≫ CurveFamily.autFunctorProjection (ShrinkHoms.fromShrinkHoms y.1 : CurveFamily B hZ) =
          OverShriek.relocalizeToYoneda U.hom
              (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y y) ≫
            yoneda.map (eqToHom y.2.symm) ∧
        ∀ {W : BigFppfOver B integerBase hZ}
          (x : ((OverShriek.relocalizePresheafFunctor U.hom).obj
            (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y y)).obj (op W)),
          x.1.2.1 = 𝟙 _ →
            Space.relativeHomSections B integerBase hZ _ _ _ _ _ _ _ _ W (e.hom.app (op W) x).1 =
              Space.RelativeMorphism.identity _
                (yoneda.map ((Over.homMk x.1.1 (OverShriek.relocalizeFactors U.hom _ x) :
                  W ⟶ U) ≫ eqToHom y.2.symm)) := by
  refine ⟨isomRelIsoAutFunctor y, isomRelIsoAutFunctor_hom_comp_projection y, fun x hx => ?_⟩
  change (equivShrink _).symm (equivShrink _ (pair y (secObj y x) (secIso y x) x.1.2.1)) = _
  rw [Equiv.symm_apply_apply, hx]
  exact (pair_id y (secObj y x) (secIso y x)).trans
    (congrArg (Space.RelativeMorphism.identity _) (pairBase_secIso' y x.1.1 _))

/-- Étale-chart conditions on morphisms of presheaves are invariant under isomorphism of arrows. -/
private theorem holdsOnEveryEtaleChart_iff_of_arrowIso (P : MorphismProperty Scheme.{u})
    {F G F' G' : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} {f : F ⟶ G} {f' : F' ⟶ G'}
    (e : Arrow.mk f ≅ Arrow.mk f') :
    Space.HoldsOnEveryEtaleChart B integerBase hZ P f ↔
      Space.HoldsOnEveryEtaleChart B integerBase hZ P f' :=
  have := Space.holdsOnEveryEtaleChart_respectsIso_presheaf B integerBase hZ P
  MorphismProperty.arrow_mk_iso_iff
    (fun ⦃F G : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u⦄ (f : F ⟶ G) =>
      Space.HoldsOnEveryEtaleChart B integerBase hZ P f) e

/-- **Properties of `Aut_U(X)` are properties of the automorphism group space.** For a property
`P` of morphisms of schemes, the structure morphism of the automorphism group algebraic space
(Stacks 04YP) of an object `y` of the stack of curves over `U` satisfies `P` on every étale chart
exactly when the projection `Aut_U(X) ⟶ U` of the family `X` that `y` is does. -/
theorem holdsOnEveryEtaleChart_automorphismGroupSpace_iff.{w} (P : MorphismProperty Scheme.{u})
    (h𝒳 : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesSmall B hZ).val) :
    Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P
        (Stack.automorphismGroupSpace B integerBase hZ (curvesSmall B hZ) h𝒳 U y).obj.X.hom ↔
      Space.HoldsOnEveryEtaleChart B integerBase hZ P
        (CurveFamily.autFunctorProjection (ShrinkHoms.fromShrinkHoms y.1 : CurveFamily B hZ)) := by
  let F := Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y y
  have e₁ : Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P
        (Stack.automorphismGroupSpace B integerBase hZ (curvesSmall B hZ) h𝒳 U y).obj.X.hom ↔
      Space.HoldsOnEveryEtaleChart B U.left.1 U.left.2 P (Space.toYonedaId B U.left.1 U.left.2 F) :=
    ⟨Space.holdsOnEveryEtaleChart_of_isTerminal B U.left.1 U.left.2
        (Stack.isTerminal_siteTerminalSpace B integerBase hZ U)
        (Space.isTerminal_yoneda_obj_base B U.left.1 U.left.2) _ _,
      Space.holdsOnEveryEtaleChart_of_isTerminal B U.left.1 U.left.2
        (Space.isTerminal_yoneda_obj_base B U.left.1 U.left.2)
        (Stack.isTerminal_siteTerminalSpace B integerBase hZ U) _ _⟩
  rw [e₁, ← Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B U.left.1 integerBase U.left.2 hZ
    U.hom P F, ← Space.holdsOnEveryEtaleChart_comp_iso_iff B integerBase hZ P _
      (yoneda.map (eqToHom y.2.symm))]
  obtain ⟨e⟩ := nonempty_arrowIso_autFunctorProjection y
  exact holdsOnEveryEtaleChart_iff_of_arrowIso P e

/-- A family of curves as an object of the small model, over its own base. -/
private abbrev fiberOf (F : CurveFamily B hZ) : (curvesSmall B hZ).val.p.Fiber F.base :=
  ⟨ShrinkHoms.toShrinkHoms F, rfl⟩

private theorem isUnramified_autFunctorProjection_iff (F : CurveFamily B hZ) :
    Space.IsUnramified B integerBase hZ (CurveFamily.autFunctorProjection F) ↔
      Space.IsUnramified B integerBase hZ (OverShriek.relocalizeToYoneda F.base.hom
        (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) F.base (fiberOf F) (fiberOf F))) := by
  obtain ⟨e⟩ := nonempty_arrowIso_autFunctorProjection (fiberOf F)
  refine (holdsOnEveryEtaleChart_iff_of_arrowIso
    (@AlgebraicGeometry.Unramified : MorphismProperty Scheme.{u}) e).symm.trans ?_
  exact Space.holdsOnEveryEtaleChart_comp_iso_iff B integerBase hZ _ _ _

/-- **Unramified automorphism groups are inherited along morphisms of families.** If
`φ : F ⟶ G` is a morphism of families of curves (a cartesian square) and `Aut(G) ⟶ G.base` is
unramified, so is `Aut(F) ⟶ F.base`. -/
theorem isUnramified_autFunctorProjection_of_hom.{w}
    (h𝒳 : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesSmall B hZ).val)
    {F G : CurveFamily B hZ} (φ : F ⟶ G)
    (hG : Space.IsUnramified B integerBase hZ (CurveFamily.autFunctorProjection G)) :
    Space.IsUnramified B integerBase hZ (CurveFamily.autFunctorProjection F) := by
  let 𝒳 := curvesSmall B hZ
  let m : (fiberOf F).1 ⟶ (fiberOf G).1 := equivShrink _ φ
  let e : F.base ⟶ G.base := 𝒳.val.p.map m
  have : 𝒳.val.p.IsHomLift e m := IsHomLift.map _ _
  have hm : 𝒳.val.p.IsStronglyCartesian e m :=
    𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift e m
  let IF := Stack.isomSpace B integerBase hZ 𝒳 F.base (fiberOf F) (fiberOf F)
  let IG := Stack.isomSpace B integerBase hZ 𝒳 G.base (fiberOf G) (fiberOf G)
  let c : IF ≅ (Over.map e.left).op ⋙ IG :=
    Stack.isomSpaceBaseChange B integerBase hZ 𝒳 e (x := fiberOf G) (x' := fiberOf F) m hm
  have hIF := Stack.isAlgebraicSpace_isomSpace B integerBase hZ 𝒳 h𝒳 F.base (fiberOf F) (fiberOf F)
  have hIG := Stack.isAlgebraicSpace_isomSpace B integerBase hZ 𝒳 h𝒳 G.base (fiberOf G) (fiberOf G)
  have hRF : IsAlgebraicSpace B F.base.left.1 F.base.left.2 ((Over.map e.left).op ⋙ IG) :=
    isAlgebraicSpace_of_iso B F.base.left.1 F.base.left.2 c.symm hIF
  rw [isUnramified_autFunctorProjection_iff] at hG ⊢
  rw [← Over.w e]
  have sq := OverShriek.isPullback_relocalizeRestrictMap G.base.hom e.left IG
  let A : AlgebraicSpaces B integerBase hZ :=
    ⟨_, isAlgebraicSpace_viewOver B _ integerBase _ hZ (e.left ≫ G.base.hom) _ hRF⟩
  let A' : AlgebraicSpaces B integerBase hZ :=
    ⟨_, isAlgebraicSpace_viewOver B _ integerBase _ hZ G.base.hom _ hIG⟩
  let Y : AlgebraicSpaces B integerBase hZ := ⟨_, isAlgebraicSpace_yoneda B integerBase hZ
    (Over.mk (e.left ≫ G.base.hom))⟩
  let Y' : AlgebraicSpaces B integerBase hZ := ⟨_, isAlgebraicSpace_yoneda B integerBase hZ
    (Over.mk G.base.hom)⟩
  have sq' : IsPullback
      (ObjectProperty.homMk (OverShriek.relocalizeRestrictMap G.base.hom e.left IG) : A ⟶ A')
      (ObjectProperty.homMk (OverShriek.relocalizeToYoneda (e.left ≫ G.base.hom)
          ((OverShriek.relocalizeRestrict e.left).obj IG)) : A ⟶ Y)
      (ObjectProperty.homMk (OverShriek.relocalizeToYoneda G.base.hom IG) : A' ⟶ Y')
      (ObjectProperty.homMk (yoneda.map (Over.homMk e.left rfl :
          Over.mk (e.left ≫ G.base.hom) ⟶ Over.mk G.base.hom)) : Y ⟶ Y') :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ sq.w) sq
  have hR : Space.IsUnramified B integerBase hZ (OverShriek.relocalizeToYoneda (e.left ≫ G.base.hom)
      ((OverShriek.relocalizeRestrict e.left).obj IG)) :=
    (Space.isUnramified_isStableUnderBaseChange B integerBase hZ).of_isPullback sq' hG
  have hc : (OverShriek.relocalizePresheafFunctor (e.left ≫ G.base.hom)).map c.hom ≫
      OverShriek.relocalizeToYoneda (e.left ≫ G.base.hom)
        ((OverShriek.relocalizeRestrict e.left).obj IG) =
      OverShriek.relocalizeToYoneda (e.left ≫ G.base.hom) IF := by
    ext V x
    exact Over.OverMorphism.ext rfl
  exact (holdsOnEveryEtaleChart_iff_of_arrowIso
    (@AlgebraicGeometry.Unramified : MorphismProperty Scheme.{u})
    (Arrow.isoMk ((OverShriek.relocalizePresheafFunctor (e.left ≫ G.base.hom)).mapIso c)
      (Iso.refl _) (hc.trans (Category.comp_id _).symm))).2 hR

end curvesSmall

end AlgebraicGeometry
