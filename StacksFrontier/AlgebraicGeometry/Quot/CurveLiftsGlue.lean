module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveLiftsProducts
public import StacksFrontier.Deformation.Examples.Geometric.SchemesRimSchlessinger
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme

/-!
# Gluing lifts of a family of curves over `k[M] ×_k k[N]`

Let `x` be a family of curves over a field `k`, and let `M` and `N` be modules. Lifts of `x`
over the square-zero extensions `k[M]` and `k[N]` glue along `x` to a lift over `k[M × N]`: the
glued total space is the pushout of the two total spaces along the total space of `x`.

## Main definitions

* `CurveLift.gluedScheme`: The pushout of the total spaces of two lifts along the total space
  of `x`.
* `CurveLift.gluedFamily`: The family of curves over `k[M × N]` with total space the glued
  scheme.
* `CurveLift.gluedLift`: The lift of `x` over `k[M × N]` glued from lifts over `k[M]` and `k[N]`.

## Main results

* `CurveLift.isPullback_glued`: The glued scheme restricts to the two given lifts.
* `CurveLift.liftClasses_product_bijective`: Isomorphism classes of lifts over `k[M × N]` are in
  bijection with pairs of isomorphism classes of lifts over `k[M]` and `k[N]`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- A morphism into a family of curves whose total space is the algebraic space of an object of
the site, from a cartesian square of schemes. -/
def homToSchemeSpace {y y' : CurveFamily B hZ} (hy : y.total.obj.IsRepresentable)
    {W : BigFppfOver B integerBase hZ} (hW : y'.total = schemeSpace W) (t : W ⟶ y'.base)
    (ht : y'.toBase = eqToHom hW ≫ schemeSpaceMap t) (bm : y.base ⟶ y'.base)
    (g : (BigFppfOver.toScheme B integerBase hZ).obj (totalSite hy) ⟶
      (BigFppfOver.toScheme B integerBase hZ).obj W)
    (hg : IsPullback g ((BigFppfOver.toScheme B integerBase hZ).map (totalSiteToBase hy))
      ((BigFppfOver.toScheme B integerBase hZ).map t)
      ((BigFppfOver.toScheme B integerBase hZ).map bm)) : y ⟶ y' where
  baseMap := bm
  totalMap := (totalSpaceIso hy).inv ≫ schemeSpaceMap (integerSiteHom g) ≫ eqToHom hW.symm
  cartesian := by
    have hsite : IsPullback (integerSiteHom (U := totalSite hy) (V := W) g)
        (totalSiteToBase hy) t bm := FiniteFreeAlgebra.isPullback_of_isPullback_toScheme hg
    refine IsPullback.of_iso (isPullback_schemeSpaceMap hsite) (totalSpaceIso hy)
      (eqToIso hW.symm) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · exact (Iso.hom_inv_id_assoc (totalSpaceIso hy) _).symm
    · apply ObjectProperty.hom_ext
      change yoneda.map (totalSiteToBase hy) ≫ 𝟙 _ = _
      rw [Category.comp_id, yoneda_map_totalSiteToBase]
      rfl
    · rw [ht]
      simp
    · exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The base morphism of `homToSchemeSpace` is the given morphism of bases. -/
theorem homToSchemeSpace_baseMap {y y' : CurveFamily B hZ} (hy : y.total.obj.IsRepresentable)
    {W : BigFppfOver B integerBase hZ} (hW : y'.total = schemeSpace W) (t : W ⟶ y'.base)
    (ht : y'.toBase = eqToHom hW ≫ schemeSpaceMap t) (bm : y.base ⟶ y'.base)
    (g : (BigFppfOver.toScheme B integerBase hZ).obj (totalSite hy) ⟶
      (BigFppfOver.toScheme B integerBase hZ).obj W)
    (hg : IsPullback g ((BigFppfOver.toScheme B integerBase hZ).map (totalSiteToBase hy))
      ((BigFppfOver.toScheme B integerBase hZ).map t)
      ((BigFppfOver.toScheme B integerBase hZ).map bm)) :
    (homToSchemeSpace hy hW t ht bm g hg).baseMap = bm := rfl

/-- Precomposing a morphism built by `homToSchemeSpace` builds the morphism of the composite
square. -/
theorem comp_homToSchemeSpace {y₀ y y' : CurveFamily B hZ} (hy₀ : y₀.total.obj.IsRepresentable)
    (hy : y.total.obj.IsRepresentable) (f : y₀ ⟶ y)
    {W : BigFppfOver B integerBase hZ} (hW : y'.total = schemeSpace W) (t : W ⟶ y'.base)
    (ht : y'.toBase = eqToHom hW ≫ schemeSpaceMap t) (bm : y.base ⟶ y'.base)
    (g : (BigFppfOver.toScheme B integerBase hZ).obj (totalSite hy) ⟶
      (BigFppfOver.toScheme B integerBase hZ).obj W)
    (hg : IsPullback g ((BigFppfOver.toScheme B integerBase hZ).map (totalSiteToBase hy))
      ((BigFppfOver.toScheme B integerBase hZ).map t)
      ((BigFppfOver.toScheme B integerBase hZ).map bm))
    (bm₀ : y₀.base ⟶ y'.base) (hbm : f.baseMap ≫ bm = bm₀)
    (g₀ : (BigFppfOver.toScheme B integerBase hZ).obj (totalSite hy₀) ⟶
      (BigFppfOver.toScheme B integerBase hZ).obj W)
    (hg₀ : IsPullback g₀ ((BigFppfOver.toScheme B integerBase hZ).map (totalSiteToBase hy₀))
      ((BigFppfOver.toScheme B integerBase hZ).map t)
      ((BigFppfOver.toScheme B integerBase hZ).map bm₀))
    (hgg : (BigFppfOver.toScheme B integerBase hZ).map (totalSiteMap hy hy₀ f) ≫ g = g₀) :
    f ≫ homToSchemeSpace hy hW t ht bm g hg = homToSchemeSpace hy₀ hW t ht bm₀ g₀ hg₀ := by
  subst hbm hgg
  refine Hom.ext rfl ?_
  show f.totalMap ≫ (totalSpaceIso hy).inv ≫ schemeSpaceMap (integerSiteHom g) ≫
      eqToHom hW.symm = (totalSpaceIso hy₀).inv ≫ schemeSpaceMap (integerSiteHom
        ((BigFppfOver.toScheme B integerBase hZ).map (totalSiteMap hy hy₀ f) ≫ g)) ≫
      eqToHom hW.symm
  simp only [← Category.assoc]
  congr 1
  apply ObjectProperty.hom_ext
  have h' : f.totalMap.hom = (totalSiteIso hy₀).inv ≫ yoneda.map (totalSiteMap hy hy₀ f) ≫
      (totalSiteIso hy).hom := by
    rw [yoneda_map_totalSiteMap hy hy₀ f]
    simp
  show f.totalMap.hom ≫ (totalSiteIso hy).inv ≫ yoneda.map (integerSiteHom g) =
    (totalSiteIso hy₀).inv ≫ yoneda.map (integerSiteHom
        ((BigFppfOver.toScheme B integerBase hZ).map (totalSiteMap hy hy₀ f) ≫ g))
  rw [h']
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  congr 1

end CurveFamily

namespace CurveLift

open Deformation.Artin

variable {k : Type u} [Field k] {toS : Spec (.of k) ⟶ integerBase}
  {hk : B.Contains (Spec (.of k))} (x : CurveFamily B hZ)
  (hx : (curvesProjectionOver B hZ).obj x = algebraOver k B integerBase hZ toS hk)

omit [Field k] in
/-- Conjugating a morphism of the site by `eqToHom`s preserves being a finite-order thickening
after passing to schemes. -/
theorem isFiniteOrderThickening_map_eqToHom_comp_comp {U V W Y : BigFppfOver B integerBase hZ}
    (h₁ : U = V) (g : V ⟶ W) (h₂ : W = Y)
    (hg : Stacks.Thickenings.IsFiniteOrderThickening
      ((BigFppfOver.toScheme B integerBase hZ).map g)) :
    Stacks.Thickenings.IsFiniteOrderThickening
      ((BigFppfOver.toScheme B integerBase hZ).map (eqToHom h₁ ≫ g ≫ eqToHom h₂)) := by
  subst h₁ h₂
  simpa using hg

omit hx in
/-- The square-zero immersion `Spec k ⟶ Spec k[M]` is a first-order thickening. -/
theorem isFiniteOrderThickening_toScheme_squareZeroArrow (M : SiteModule k B) :
    Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B integerBase hZ).map
      (squareZeroArrow k B integerBase hZ toS hk M)) := by
  have h := Stacks.Smooth.isFirstOrderThickening_specMap (squareZeroProjection k M.obj)
    (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩) (squareZeroProjection_ker_sq k M.obj)
  exact ⟨h.1, ⟨1, h.2⟩⟩

include hx in
/-- The scheme representing the total space of a family of curves over a field has topological
Krull dimension at most `1`. -/
theorem topologicalKrullDim_total_le :
    topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj
      (CurveFamily.totalSite (isRepresentable_total x hx))) ≤ 1 := by
  have hxr := isRepresentable_total x hx
  have h1 := Space.dimension_yoneda_eq_topologicalKrullDim B integerBase hZ
    (CurveFamily.totalSite hxr)
  have h2 := Space.dimension_eq_of_iso B integerBase hZ (isAlgebraicSpace_yoneda _ _ _ _)
    x.total.property (CurveFamily.totalSiteIso hxr)
  have h3 := Space.dimension_eq_iSup_localRingDimension B integerBase hZ x.total.obj
    x.total.property
  rw [← h1, h2, h3]
  refine iSup_le fun y => ?_
  exact_mod_cast x.localRingDimension_le_one_of_base_eq
    (congrArg (BigFppfOver.toScheme B integerBase hZ).obj hx) y

section Glue

variable {M N : SiteModule k B} (b₁ : Lift x hx M) (b₂ : Lift x hx N)

/-- The scheme representing the total space of `x`. -/
abbrev totalScheme : Scheme.{u} :=
  (BigFppfOver.toScheme B integerBase hZ).obj
    (CurveFamily.totalSite (isRepresentable_total x hx))

/-- The scheme representing the total space of a lift. -/
abbrev liftTotalScheme {L : SiteModule k B} (b : Lift x hx L) : Scheme.{u} :=
  (BigFppfOver.toScheme B integerBase hZ).obj
    (CurveFamily.totalSite (isRepresentable_total_lift x hx b))

/-- The closed immersion of the total space of `x` into the total space of a lift. -/
abbrev liftRestriction {L : SiteModule k B} (b : Lift x hx L) :
    totalScheme x hx ⟶ liftTotalScheme x hx b :=
  (BigFppfOver.toScheme B integerBase hZ).map (CurveFamily.totalSiteMap
    (isRepresentable_total_lift x hx b) (isRepresentable_total x hx) b.1.hom)

/-- The total space of `x` is the pullback of the total space of a lift along the closed
immersion of bases. -/
theorem isPullback_liftRestriction {L : SiteModule k B} (b : Lift x hx L) :
    IsPullback (liftRestriction x hx b)
      ((BigFppfOver.toScheme B integerBase hZ).map
        (CurveFamily.totalSiteToBase (isRepresentable_total x hx)))
      ((BigFppfOver.toScheme B integerBase hZ).map
        (CurveFamily.totalSiteToBase (isRepresentable_total_lift x hx b)))
      ((BigFppfOver.toScheme B integerBase hZ).map b.1.hom.baseMap) :=
  (CurveFamily.isPullback_totalSite _ _ b.1.hom).map (BigFppfOver.toScheme B integerBase hZ)

/-- The closed immersion of the total space of `x` into the total space of a lift is a
thickening. -/
theorem isThickening_liftRestriction {L : SiteModule k B} (b : Lift x hx L) :
    Stacks.Thickenings.IsThickening (liftRestriction x hx b) :=
  Stacks.Thickenings.isThickening_of_isPullback (isPullback_liftRestriction x hx b)
    (isThickening_lift_hom x hx b)

/-- The morphism `liftRestriction` is a closed immersion. -/
instance {L : SiteModule k B} (b : Lift x hx L) : IsClosedImmersion (liftRestriction x hx b) :=
  (isThickening_liftRestriction x hx b).1

/-- The total spaces of two lifts admit a pushout along the total space of `x`. -/
instance : HasPushout (liftRestriction x hx b₂) (liftRestriction x hx b₁) :=
  Stacks.Pushout.hasPushout_of_isThickening _ _ (isThickening_liftRestriction x hx b₂)

/-- The scheme glued from the total spaces of two lifts along the total space of `x`. -/
abbrev gluedScheme : Scheme.{u} := pushout (liftRestriction x hx b₂) (liftRestriction x hx b₁)

/-- The morphism of bases underlying a lift is a finite-order thickening. -/
theorem isFiniteOrderThickening_lift_hom {L : SiteModule k B} (b : Lift x hx L) :
    Stacks.Thickenings.IsFiniteOrderThickening
      ((BigFppfOver.toScheme B integerBase hZ).map b.1.hom.baseMap) := by
  rw [baseMap_lift_hom x hx b]
  exact isFiniteOrderThickening_map_eqToHom_comp_comp _ _ _
    (isFiniteOrderThickening_toScheme_squareZeroArrow (hk := hk) (toS := toS) L)

/-- The morphism of bases underlying a lift is a closed immersion of schemes. -/
instance {L : SiteModule k B} (b : Lift x hx L) :
    IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map b.1.hom.baseMap) :=
  (isThickening_lift_hom x hx b).1

omit [Field k] in
/-- Cancellation of `eqToHom e.symm ≫ eqToHom e` inside a composite. -/
theorem comp_comp_eqToHom_comp_eqToHom {C : Type*} [Category C] {X Y U V W : C} (a : X ⟶ Y)
    (b : Y ⟶ V) (e : U = V) (f : V ⟶ W) :
    (a ≫ b ≫ eqToHom e.symm) ≫ eqToHom e ≫ f = a ≫ b ≫ f := by
  subst e
  simp

omit [Field k] in
/-- A trailing `eqToHom` of an equality `Z = Z` may be dropped. -/
theorem eqToHom_comp_comp_eqToHom_self {C : Type*} [Category C] {X Y Z : C} (e : X = Y)
    (f : Y ⟶ Z) (h : Z = Z) : eqToHom e ≫ f ≫ eqToHom h = eqToHom e ≫ f := by
  simp

/-- The inclusion of the base of a lift over `k[M]` into `Spec k[M × N]`. -/
abbrev glueBaseFst (N : SiteModule k B) :
    (curvesProjectionOver B hZ).obj b₁.1.right ⟶
      squareZeroOver k B integerBase hZ toS (siteModuleProd k B hk M N) :=
  eqToHom (liftAlong_base_obj (curvesProjectionOver B hZ) x (arrow x hx M) b₁) ≫
    squareZeroOverMap k B integerBase hZ toS (siteModuleFst k B hk M N)

/-- The inclusion of the base of a lift over `k[N]` into `Spec k[M × N]`. -/
abbrev glueBaseSnd (M : SiteModule k B) :
    (curvesProjectionOver B hZ).obj b₂.1.right ⟶
      squareZeroOver k B integerBase hZ toS (siteModuleProd k B hk M N) :=
  eqToHom (liftAlong_base_obj (curvesProjectionOver B hZ) x (arrow x hx N) b₂) ≫
    squareZeroOverMap k B integerBase hZ toS (siteModuleSnd k B hk M N)

/-- The composite `Spec k ⟶ Spec k[M] ⟶ Spec k[M × N]` is the square-zero immersion of
`Spec k` into `Spec k[M × N]`. -/
theorem baseMap_comp_glueBaseFst :
    b₁.1.hom.baseMap ≫ glueBaseFst x hx b₁ N = arrow x hx (siteModuleProd k B hk M N) := by
  rw [baseMap_lift_hom x hx b₁]
  refine (comp_comp_eqToHom_comp_eqToHom _ _ _ _).trans ?_
  rw [squareZeroArrow_naturality]
  rfl

/-- The composite `Spec k ⟶ Spec k[N] ⟶ Spec k[M × N]` is the square-zero immersion of
`Spec k` into `Spec k[M × N]`. -/
theorem baseMap_comp_glueBaseSnd :
    b₂.1.hom.baseMap ≫ glueBaseSnd x hx b₂ M = arrow x hx (siteModuleProd k B hk M N) := by
  rw [baseMap_lift_hom x hx b₂]
  refine (comp_comp_eqToHom_comp_eqToHom _ _ _ _).trans ?_
  rw [squareZeroArrow_naturality]
  rfl

/-- The base of the gluing: `Spec k[M × N]` is the pushout of the bases of the two lifts. -/
theorem isPushout_glueBase :
    IsPushout ((BigFppfOver.toScheme B integerBase hZ).map b₂.1.hom.baseMap)
      ((BigFppfOver.toScheme B integerBase hZ).map b₁.1.hom.baseMap)
      ((BigFppfOver.toScheme B integerBase hZ).map (glueBaseSnd x hx b₂ M))
      ((BigFppfOver.toScheme B integerBase hZ).map (glueBaseFst x hx b₁ N)) :=
  isPushout_map_of_eqToHom_conj hx
    (liftAlong_base_obj (curvesProjectionOver B hZ) x (arrow x hx M) b₁)
    (liftAlong_base_obj (curvesProjectionOver B hZ) x (arrow x hx N) b₂) rfl
    (isPushout_toScheme_squareZero M N) (baseMap_lift_hom x hx b₂) (baseMap_lift_hom x hx b₁)
    (by simp only [eqToHom_refl, Category.comp_id])
    (by simp only [eqToHom_refl, Category.comp_id])

/-- Two maps out of the bases of the lifts that agree on the base of `x` give agreeing composites
from the total space of `x`. -/
private theorem liftRestriction_comp_comp_eq {T : Scheme.{u}}
    (e₂ : (BigFppfOver.toScheme B integerBase hZ).obj b₂.1.right.base ⟶ T)
    (e₁ : (BigFppfOver.toScheme B integerBase hZ).obj b₁.1.right.base ⟶ T)
    (h : (BigFppfOver.toScheme B integerBase hZ).map b₂.1.hom.baseMap ≫ e₂ =
      (BigFppfOver.toScheme B integerBase hZ).map b₁.1.hom.baseMap ≫ e₁) :
    liftRestriction x hx b₂ ≫ (BigFppfOver.toScheme B integerBase hZ).map
        (CurveFamily.totalSiteToBase (isRepresentable_total_lift x hx b₂)) ≫ e₂ =
      liftRestriction x hx b₁ ≫ (BigFppfOver.toScheme B integerBase hZ).map
        (CurveFamily.totalSiteToBase (isRepresentable_total_lift x hx b₁)) ≫ e₁ := by
  rw [← Category.assoc, (isPullback_liftRestriction x hx b₂).w, ← Category.assoc,
    (isPullback_liftRestriction x hx b₁).w, Category.assoc, Category.assoc, h]

/-- The two composites from the total space of `x` to `Spec k[M × N]` through the total
spaces of the two lifts agree. -/
theorem glue_w : liftRestriction x hx b₂ ≫ (BigFppfOver.toScheme B integerBase hZ).map
      (CurveFamily.totalSiteToBase (isRepresentable_total_lift x hx b₂)) ≫
      (BigFppfOver.toScheme B integerBase hZ).map (glueBaseSnd x hx b₂ M) =
    liftRestriction x hx b₁ ≫ (BigFppfOver.toScheme B integerBase hZ).map
      (CurveFamily.totalSiteToBase (isRepresentable_total_lift x hx b₁)) ≫
      (BigFppfOver.toScheme B integerBase hZ).map (glueBaseFst x hx b₁ N) :=
  liftRestriction_comp_comp_eq x hx b₁ b₂ _ _ (isPushout_glueBase x hx b₁ b₂).w

/-- The structure morphism of the glued scheme. -/
abbrev gluedToBase : gluedScheme x hx b₁ b₂ ⟶ (BigFppfOver.toScheme B integerBase hZ).obj
    (squareZeroOver k B integerBase hZ toS (siteModuleProd k B hk M N)) :=
  pushout.desc ((BigFppfOver.toScheme B integerBase hZ).map
      (CurveFamily.totalSiteToBase (isRepresentable_total_lift x hx b₂)) ≫
      (BigFppfOver.toScheme B integerBase hZ).map (glueBaseSnd x hx b₂ M))
    ((BigFppfOver.toScheme B integerBase hZ).map
      (CurveFamily.totalSiteToBase (isRepresentable_total_lift x hx b₁)) ≫
      (BigFppfOver.toScheme B integerBase hZ).map (glueBaseFst x hx b₁ N)) (glue_w x hx b₁ b₂)

/-- The glued scheme is flat over `Spec k[M × N]`. -/
theorem flat_gluedToBase : Flat (gluedToBase x hx b₁ b₂) := by
  have hpo := isPushout_glueBase x hx b₁ b₂
  have := hpo.hasPushout
  have hw := liftRestriction_comp_comp_eq x hx b₁ b₂ (pushout.inl _ _) (pushout.inr _ _)
    pushout.condition
  have hfl := Deformation.Examples.flat_pushoutDesc_of_isFiniteOrderThickening
    (isFiniteOrderThickening_lift_hom x hx b₂) (isPullback_liftRestriction x hx b₁)
    (isPullback_liftRestriction x hx b₂)
    (CurveFamily.flat_toScheme_map_totalSiteToBase (isRepresentable_total_lift x hx b₁))
    (CurveFamily.flat_toScheme_map_totalSiteToBase (isRepresentable_total_lift x hx b₂)) hw
  have heq : gluedToBase x hx b₁ b₂ = (IsPushout.of_hasPushout _ _).desc _ _ hw ≫
      hpo.isoPushout.inv := by
    apply pushout.hom_ext
    · rw [pushout.inl_desc, ← Category.assoc, IsPushout.inl_desc, Category.assoc,
        IsPushout.inl_isoPushout_inv]
    · rw [pushout.inr_desc, ← Category.assoc, IsPushout.inr_desc, Category.assoc,
        IsPushout.inr_isoPushout_inv]
  rw [heq]
  infer_instance

/-- **The glued scheme restricts to the two lifts.** The squares from the total spaces of the
two lifts into the glued scheme are cartesian over `Spec k[M] ⟶ Spec k[M × N]` and
`Spec k[N] ⟶ Spec k[M × N]`. -/
theorem isPullback_glued :
    IsPullback (pushout.inr (liftRestriction x hx b₂) (liftRestriction x hx b₁))
        ((BigFppfOver.toScheme B integerBase hZ).map
          (CurveFamily.totalSiteToBase (isRepresentable_total_lift x hx b₁)))
        (gluedToBase x hx b₁ b₂)
        ((BigFppfOver.toScheme B integerBase hZ).map (glueBaseFst x hx b₁ N)) ∧
      IsPullback (pushout.inl (liftRestriction x hx b₂) (liftRestriction x hx b₁))
        ((BigFppfOver.toScheme B integerBase hZ).map
          (CurveFamily.totalSiteToBase (isRepresentable_total_lift x hx b₂)))
        (gluedToBase x hx b₁ b₂)
        ((BigFppfOver.toScheme B integerBase hZ).map (glueBaseSnd x hx b₂ M)) :=
  Stacks.Pushout.isPullback_of_isPushout_glued (isThickening_lift_hom x hx b₂)
    (isPushout_glueBase x hx b₁ b₂) (isPullback_liftRestriction x hx b₁)
    (isPullback_liftRestriction x hx b₂) (IsPushout.of_hasPushout _ _)
    (pushout.inr_desc _ _ _) (pushout.inl_desc _ _ _)

/-- The closed immersion of the total space of `x` into the glued scheme. -/
abbrev gluedSpecial : totalScheme x hx ⟶ gluedScheme x hx b₁ b₂ :=
  liftRestriction x hx b₁ ≫ pushout.inr (liftRestriction x hx b₂) (liftRestriction x hx b₁)

/-- The total space of `x` is the special fibre of the glued scheme. -/
theorem isPullback_gluedSpecial :
    IsPullback (gluedSpecial x hx b₁ b₂)
      ((BigFppfOver.toScheme B integerBase hZ).map
        (CurveFamily.totalSiteToBase (isRepresentable_total x hx)))
      (gluedToBase x hx b₁ b₂)
      ((BigFppfOver.toScheme B integerBase hZ).map (arrow x hx (siteModuleProd k B hk M N))) := by
  have h := (isPullback_liftRestriction x hx b₁).paste_horiz (isPullback_glued x hx b₁ b₂).1
  have he : (BigFppfOver.toScheme B integerBase hZ).map b₁.1.hom.baseMap ≫
      (BigFppfOver.toScheme B integerBase hZ).map (glueBaseFst x hx b₁ N) =
      (BigFppfOver.toScheme B integerBase hZ).map (arrow x hx (siteModuleProd k B hk M N)) :=
    ((BigFppfOver.toScheme B integerBase hZ).map_comp _ _).symm.trans
      (congrArg (BigFppfOver.toScheme B integerBase hZ).map
        (baseMap_comp_glueBaseFst x hx b₁ (N := N)))
  exact he ▸ h

/-- The immersion of the base of `x` into `Spec k[L]` is a finite-order thickening. -/
theorem isFiniteOrderThickening_arrow (L : SiteModule k B) :
    Stacks.Thickenings.IsFiniteOrderThickening
      ((BigFppfOver.toScheme B integerBase hZ).map (arrow x hx L)) := by
  simpa using isFiniteOrderThickening_map_eqToHom_comp_comp hx
    (squareZeroArrow k B integerBase hZ toS hk L) rfl
    (isFiniteOrderThickening_toScheme_squareZeroArrow L)

/-- The cartesian finite-order deformation diagram of the glued scheme over the thickening
`Spec k ⊆ Spec k[M × N]`. -/
def gluedDiagram : Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.{u} where
  S := (BigFppfOver.toScheme B integerBase hZ).obj x.base
  S' := (BigFppfOver.toScheme B integerBase hZ).obj
    (squareZeroOver k B integerBase hZ toS (siteModuleProd k B hk M N))
  iS := (BigFppfOver.toScheme B integerBase hZ).map (arrow x hx (siteModuleProd k B hk M N))
  iS_finiteOrder := isFiniteOrderThickening_arrow x hx _
  X := totalScheme x hx
  X' := gluedScheme x hx b₁ b₂
  iX := gluedSpecial x hx b₁ b₂
  iX_thickening := Stacks.Thickenings.isThickening_of_isPullback
    (isPullback_gluedSpecial x hx b₁ b₂) (isFiniteOrderThickening_arrow x hx _).isThickening
  Y := (BigFppfOver.toScheme B integerBase hZ).obj x.base
  Y' := (BigFppfOver.toScheme B integerBase hZ).obj
    (squareZeroOver k B integerBase hZ toS (siteModuleProd k B hk M N))
  iY := (BigFppfOver.toScheme B integerBase hZ).map (arrow x hx (siteModuleProd k B hk M N))
  iY_thickening := (isFiniteOrderThickening_arrow x hx _).isThickening
  pX := (BigFppfOver.toScheme B integerBase hZ).map
    (CurveFamily.totalSiteToBase (isRepresentable_total x hx))
  pX' := gluedToBase x hx b₁ b₂
  pY := 𝟙 _
  pY' := 𝟙 _
  f := (BigFppfOver.toScheme B integerBase hZ).map
    (CurveFamily.totalSiteToBase (isRepresentable_total x hx))
  f' := gluedToBase x hx b₁ b₂
  f_over_S := Category.comp_id _
  f'_over_S' := Category.comp_id _
  f_thickening_comm := (isPullback_gluedSpecial x hx b₁ b₂).w.symm
  X_cartesian := isPullback_gluedSpecial x hx b₁ b₂
  Y_cartesian := IsPullback.of_vert_isIso ⟨by simp⟩
  X'_flat := flat_gluedToBase x hx b₁ b₂

/-- The glued scheme is proper over `Spec k[M × N]`. -/
theorem isProper_gluedToBase : IsProper (gluedToBase x hx b₁ b₂) :=
  (gluedDiagram x hx b₁ b₂).isProper_iff.mp
    (CurveFamily.isProper_toScheme_map_totalSiteToBase (isRepresentable_total x hx))

/-- The glued scheme is locally of finite presentation over `Spec k[M × N]`. -/
theorem locallyOfFinitePresentation_gluedToBase :
    LocallyOfFinitePresentation (gluedToBase x hx b₁ b₂) :=
  (gluedDiagram x hx b₁ b₂).locallyOfFinitePresentation_iff.mp
    (CurveFamily.locallyOfFinitePresentation_toScheme_map_totalSiteToBase
      (isRepresentable_total x hx))

/-- The glued scheme lies in the big fppf site `B`. -/
theorem contains_gluedScheme : B.Contains (gluedScheme x hx b₁ b₂) := by
  have := isProper_gluedToBase x hx b₁ b₂
  exact lt_of_le_of_lt (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact
    (gluedToBase x hx b₁ b₂))
    (squareZeroOver k B integerBase hZ toS (siteModuleProd k B hk M N)).left.property

/-- The glued scheme has topological Krull dimension at most `1`. -/
theorem topologicalKrullDim_gluedScheme_le : topologicalKrullDim (gluedScheme x hx b₁ b₂) ≤ 1 :=
  (IsHomeomorph.topologicalKrullDim_eq _
    ((gluedDiagram x hx b₁ b₂).iX_thickening.homeomorph).isHomeomorph).symm.trans_le
    (topologicalKrullDim_total_le x hx)

/-- The glued scheme, as an object of the site. -/
abbrev gluedSite : BigFppfOver B integerBase hZ :=
  (schemeOverIntegers B).obj (B.obj (contains_gluedScheme x hx b₁ b₂))

/-- The structure morphism of the glued scheme, as a morphism of the site. -/
abbrev gluedSiteToBase :
    gluedSite x hx b₁ b₂ ⟶ squareZeroOver k B integerBase hZ toS (siteModuleProd k B hk M N) :=
  integerSiteHom (gluedToBase x hx b₁ b₂)

/-- The family of curves of `curveFamilyOfSchemeMorphism` at the glued scheme. -/
def gluedFamilyAux : CurveFamily B hZ :=
  haveI hp : IsProper ((BigFppfOver.toScheme B integerBase hZ).map
      (gluedSiteToBase x hx b₁ b₂)) :=
    isProper_gluedToBase x hx b₁ b₂
  curveFamilyOfSchemeMorphism B hZ (gluedSiteToBase x hx b₁ b₂) (flat_gluedToBase x hx b₁ b₂) hp
    (locallyOfFinitePresentation_gluedToBase x hx b₁ b₂)
    (Space.isQuasiCompact_yoneda_map B integerBase hZ _ inferInstance)
    ((Space.isSeparated_yoneda_map_iff B integerBase hZ _).mpr inferInstance)
    ((Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ _).mpr inferInstance)
    (topologicalKrullDim_gluedScheme_le x hx b₁ b₂)

/-- **The family of curves over `k[M × N]` glued from lifts over `k[M]` and `k[N]`.** -/
abbrev gluedFamily : CurveFamily B hZ where
  base := squareZeroOver k B integerBase hZ toS (siteModuleProd k B hk M N)
  total := schemeSpace (gluedSite x hx b₁ b₂)
  toBase := schemeSpaceMap (gluedSiteToBase x hx b₁ b₂)
  flat := (gluedFamilyAux x hx b₁ b₂).flat
  proper := (gluedFamilyAux x hx b₁ b₂).proper
  finitePresentation := (gluedFamilyAux x hx b₁ b₂).finitePresentation
  relativeDimensionLE := (gluedFamilyAux x hx b₁ b₂).relativeDimensionLE

/-- The morphism from `x` to the glued family. -/
def gluedArrow : x ⟶ gluedFamily x hx b₁ b₂ :=
  CurveFamily.homToSchemeSpace (isRepresentable_total x hx) rfl (gluedSiteToBase x hx b₁ b₂)
    (Category.id_comp _).symm (arrow x hx (siteModuleProd k B hk M N)) (gluedSpecial x hx b₁ b₂)
    (isPullback_gluedSpecial x hx b₁ b₂)

/-- The morphism from the lift over `k[M]` to the glued family. -/
def gluedFst : b₁.1.right ⟶ gluedFamily x hx b₁ b₂ :=
  CurveFamily.homToSchemeSpace (isRepresentable_total_lift x hx b₁) rfl
    (gluedSiteToBase x hx b₁ b₂) (Category.id_comp _).symm (glueBaseFst x hx b₁ N)
    (pushout.inr _ _) (isPullback_glued x hx b₁ b₂).1

/-- The morphism from the lift over `k[N]` to the glued family. -/
def gluedSnd : b₂.1.right ⟶ gluedFamily x hx b₁ b₂ :=
  CurveFamily.homToSchemeSpace (isRepresentable_total_lift x hx b₂) rfl
    (gluedSiteToBase x hx b₁ b₂) (Category.id_comp _).symm (glueBaseSnd x hx b₂ M)
    (pushout.inl _ _) (isPullback_glued x hx b₁ b₂).2

/-- The morphism from `x` to the lift over `k[M]`, followed by `gluedFst`, is `gluedArrow`. -/
theorem hom_comp_gluedFst : b₁.1.hom ≫ gluedFst x hx b₁ b₂ = gluedArrow x hx b₁ b₂ :=
  CurveFamily.comp_homToSchemeSpace _ _ _ _ _ _ _ _ _ _ (baseMap_comp_glueBaseFst x hx b₁) _ _
    rfl

/-- The morphism from `x` to the lift over `k[N]`, followed by `gluedSnd`, is `gluedArrow`. -/
theorem hom_comp_gluedSnd : b₂.1.hom ≫ gluedSnd x hx b₁ b₂ = gluedArrow x hx b₁ b₂ :=
  CurveFamily.comp_homToSchemeSpace _ _ _ _ _ _ _ _ _ _ (baseMap_comp_glueBaseSnd x hx b₂) _ _
    pushout.condition

/-- **The lift of `x` over `k[M × N]` glued from lifts over `k[M]` and `k[N]`.** -/
def gluedLift : Lift x hx (siteModuleProd k B hk M N) :=
  liftAlongMk (curvesProjectionOver B hZ) x (arrow x hx _) rfl (gluedArrow x hx b₁ b₂) (by
    change (curvesProjectionOver B hZ).IsHomLift
      ((curvesProjectionOver B hZ).map (gluedArrow x hx b₁ b₂)) _
    infer_instance)

/-- The morphism of lifts from the lift over `k[M]` to the glued lift. -/
def gluedFstHom : b₁.1 ⟶ (gluedLift x hx b₁ b₂).1 :=
  Under.homMk (gluedFst x hx b₁ b₂) (hom_comp_gluedFst x hx b₁ b₂)

/-- The morphism of lifts from the lift over `k[N]` to the glued lift. -/
def gluedSndHom : b₂.1 ⟶ (gluedLift x hx b₁ b₂).1 :=
  Under.homMk (gluedSnd x hx b₁ b₂) (hom_comp_gluedSnd x hx b₁ b₂)

/-- The morphism `gluedFstHom` lies over `baseFst x hx M N`. -/
theorem gluedFstHom_isHomLift :
    (Under.post (curvesProjectionOver B hZ)).IsHomLift (baseFst x hx M N)
      (gluedFstHom x hx b₁ b₂) :=
  underPost_isHomLift_of_isHomLift_right x (s := b₁) (t := gluedLift x hx b₁ b₂) _ _
    (IsHomLift.of_fac' _ _ _
      (liftAlong_base_obj (curvesProjectionOver B hZ) x (arrow x hx M) b₁) rfl
      (eqToHom_comp_comp_eqToHom_self _ _ _).symm)

/-- The morphism `gluedSndHom` lies over `baseSnd x hx M N`. -/
theorem gluedSndHom_isHomLift :
    (Under.post (curvesProjectionOver B hZ)).IsHomLift (baseSnd x hx M N)
      (gluedSndHom x hx b₁ b₂) :=
  underPost_isHomLift_of_isHomLift_right x (s := b₂) (t := gluedLift x hx b₁ b₂) _ _
    (IsHomLift.of_fac' _ _ _
      (liftAlong_base_obj (curvesProjectionOver B hZ) x (arrow x hx N) b₂) rfl
      (eqToHom_comp_comp_eqToHom_self _ _ _).symm)

end Glue

/-- **Lifts of a family of curves over a field turn products of modules into products of
sets.** Restriction along `k[M × N] ⟶ k[M]` and `k[M × N] ⟶ k[N]` is a bijection from the
isomorphism classes of lifts of `x` over `k[M × N]` to pairs of isomorphism classes of lifts
over `k[M]` and `k[N]`: the restrictions of a lift determine it up to isomorphism
(`existsUnique_fiberHom`), and lifts over `k[M]` and `k[N]` glue along `x` to a lift over
`k[M × N]` (Stacks 07RV and 07RX). This is the instance of (RS*) used by Stacks 07Y9 for the
tangent functor. -/
theorem liftClasses_product_bijective (hp : (curvesProjectionOver B hZ).IsFiberedInGroupoids)
    (M N : SiteModule k B) :
    letI := underPost_isFibered (curvesProjectionOver B hZ) hp x
    Function.Bijective (fun a : squareZeroLiftClasses k B integerBase hZ toS hk
        (curvesProjectionOver B hZ) x hx (siteModuleProd k B hk M N) =>
      ((Under.post (curvesProjectionOver B hZ)).isoClassPresheaf.map
          (Under.homMk (U := Under.mk (eqToHom hx ≫ squareZeroArrow k B integerBase hZ toS hk M))
            (V := Under.mk (eqToHom hx ≫
              squareZeroArrow k B integerBase hZ toS hk (siteModuleProd k B hk M N)))
            (squareZeroOverMap k B integerBase hZ toS (siteModuleFst k B hk M N))
            (by simp [squareZeroArrow_naturality])).op a,
        (Under.post (curvesProjectionOver B hZ)).isoClassPresheaf.map
          (Under.homMk (U := Under.mk (eqToHom hx ≫ squareZeroArrow k B integerBase hZ toS hk N))
            (V := Under.mk (eqToHom hx ≫
              squareZeroArrow k B integerBase hZ toS hk (siteModuleProd k B hk M N)))
            (squareZeroOverMap k B integerBase hZ toS (siteModuleSnd k B hk M N))
            (by simp [squareZeroArrow_naturality])).op a)) := by
  let := underPost_isFibered (curvesProjectionOver B hZ) hp x
  have hq := underPost_isFiberedInGroupoids (curvesProjectionOver B hZ) hp x
  refine ⟨fun a a' h => ?_, fun ⟨a₁, a₂⟩ => ?_⟩
  · induction a using Quotient.ind with
    | _ c =>
    induction a' using Quotient.ind with
    | _ c' =>
    obtain ⟨θ₁⟩ := (Functor.isoClassMk_eq_iff _ _).1 (congrArg Prod.fst h)
    obtain ⟨θ₂⟩ := (Functor.isoClassMk_eq_iff _ _).1 (congrArg Prod.snd h)
    have hφ : ∀ (d : (Under.post (curvesProjectionOver B hZ)).Fiber
        (Under.mk (arrow x hx (siteModuleProd k B hk M N)))) {U} (g : U ⟶ _),
        (Under.post (curvesProjectionOver B hZ)).IsHomLift g
          (Functor.IsPreFibered.pullbackMap d.2 g) := fun _ _ _ => inferInstance
    obtain ⟨θ, -, -⟩ := existsUnique_fiberHom x hx (hφ c (baseFst x hx M N))
      (hφ c (baseSnd x hx M N)) (hφ c' (baseFst x hx M N)) (hφ c' (baseSnd x hx M N))
      θ₁.hom θ₂.hom
    have := Functor.IsFiberedInGroupoids.fiber_isGroupoid hq
      (Under.mk (arrow x hx (siteModuleProd k B hk M N)))
    exact Quotient.sound ⟨asIso θ⟩
  · induction a₁ using Quotient.ind with
    | _ b₁ =>
    induction a₂ using Quotient.ind with
    | _ b₂ =>
    refine ⟨Quotient.mk _ (gluedLift x hx b₁ b₂), Prod.ext ?_ ?_⟩
    · have hΦ := gluedFstHom_isHomLift x hx b₁ b₂
      have := Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift hq (baseFst x hx M N)
        (gluedFstHom x hx b₁ b₂)
      exact (Functor.isoClassMk_eq_pullbackFiber_of_isCartesian (baseFst x hx M N) _ b₁ _ hΦ
        inferInstance).symm
    · have hΦ := gluedSndHom_isHomLift x hx b₁ b₂
      have := Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift hq (baseSnd x hx M N)
        (gluedSndHom x hx b₁ b₂)
      exact (Functor.isoClassMk_eq_pullbackFiber_of_isCartesian (baseSnd x hx M N) _ b₂ _ hΦ
        inferInstance).symm

end CurveLift

end AlgebraicGeometry
