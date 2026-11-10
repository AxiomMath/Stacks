module

public import Mathlib.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.Modules.StructureSheafLocalization

/-!
# Functoriality of the sheafified localization along a continuous functor

Let `A` and `C` be ringed sites and let `F : A.C ⥤ C.C` be a continuous functor, so that
restriction along `F` carries sheaves on `C` to sheaves on `A`; write `F_*` for that direct
image.  Let `T` and `U` be multiplicative subpresheaves of the two structure sheaves, in the
sense of `AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf`.  A morphism
`φ : A.O ⟶ F_* C.O` of structure sheaves carrying `T` into `U` extends canonically to the
sheafified localizations of Stacks 0EMC:

`T⁻¹A.O ⟶ F_* (U⁻¹C.O)`.

Over an object `V` the extension is the fraction rule `a/t ↦ φ(a)/φ(t)`, and it is the unique
morphism of sheaves of rings lying over `φ`.

## Main definitions

* `AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.localizationMapApp` is the fraction
  rule `a/t ↦ φ(a)/φ(t)` on the sectionwise localizations over a single object, and
  `AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.localizationPresheafMap` assembles
  the rules into a morphism of presheaves of rings.
* `AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.localizationSheafMap` is the induced
  morphism `T⁻¹A.O ⟶ F_* (U⁻¹C.O)` of sheaves of rings.

## Main results

* `AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.localizationMapApp_algebraMap` is
  the fraction rule on a section with denominator `1`, and
  `AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.localizationMapApp_mk'` is the rule
  on a general fraction, in closed form.
* `AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.localizationSheafMap_comp`: the
  square relating the two localization maps `𝒪 ⟶ 𝒪⁻¹` to `φ` and to the extension commutes, and
  `localizationSheafMap_app_toLocalizationSheaf` is the same statement on sections.
* `AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.localizationSheafMap_unique`: that
  square determines the extension uniquely.

## References

* [Stacks Project, Tag 0EMC](https://stacks.math.columbia.edu/tag/0EMC)
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v₃ v₄ w

namespace AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf

variable {A : RingedSite.{v₁, v₂, w}} {C : RingedSite.{v₃, v₄, w}}
  (T : MultiplicativeSubpresheaf A) (F : A.C ⥤ C.C) [F.IsContinuous A.J C.J]
  (U : MultiplicativeSubpresheaf C)
  (φ : A.O ⟶ (F.sheafPushforwardContinuous CommRingCat.{w} A.J C.J).obj C.O)
  (hφ : ∀ V, T.obj V ≤ (U.obj (F.op.obj V)).comap (φ.hom.app V).hom)

/-- The structure map of `φ` over an object `V`, as a ring homomorphism into the ring of sections
over `F V`. -/
abbrev sectionMap (V : A.Cᵒᵖ) : A.O.obj.obj V →+* C.O.obj.obj (F.op.obj V) :=
  (φ.hom.app V).hom

/-- The fraction rule `a/t ↦ φ(a)/φ(t)` over one object `V`: the extension of the structure map
of `φ` over `V` to the sectionwise localizations. -/
noncomputable def localizationMapApp (V : A.Cᵒᵖ) :
    Localization (T.obj V) →+* Localization (U.obj (F.op.obj V)) :=
  IsLocalization.map (M := T.obj V) (Localization (U.obj (F.op.obj V)))
    (sectionMap F φ V) (hφ V)

/-- The fraction rule extends the structure map of `φ`: a section, viewed as a fraction with
denominator `1`, goes to its image under `φ` viewed the same way. -/
theorem localizationMapApp_algebraMap (V : A.Cᵒᵖ) (r : A.O.obj.obj V) :
    T.localizationMapApp F U φ hφ V
        (algebraMap (A.O.obj.obj V) (Localization (T.obj V)) r) =
      algebraMap (C.O.obj.obj (F.op.obj V)) (Localization (U.obj (F.op.obj V)))
        (sectionMap F φ V r) :=
  IsLocalization.map_eq (M := T.obj V) (g := sectionMap F φ V) (hφ V) r

/-- The fraction rule in closed form: the fraction `a/t` with prescribed denominator `t` over
`V` goes to the fraction `φ(a)/φ(t)` over `F V`. -/
theorem localizationMapApp_mk' (V : A.Cᵒᵖ) (a : A.O.obj.obj V) (t : T.obj V) :
    T.localizationMapApp F U φ hφ V
        (IsLocalization.mk' (Localization (T.obj V)) a t) =
      IsLocalization.mk' (Localization (U.obj (F.op.obj V))) (sectionMap F φ V a)
        (⟨sectionMap F φ V t, hφ V t.2⟩ : U.obj (F.op.obj V)) :=
  IsLocalization.map_mk' (M := T.obj V) (g := sectionMap F φ V) (hφ V) a t

/-- The fraction rules over the objects of `A.C`, as a morphism of presheaves of rings. -/
noncomputable def localizationPresheafMap :
    T.localizationPresheaf ⟶ F.op ⋙ U.localizationPresheaf where
  app V := CommRingCat.ofHom (T.localizationMapApp F U φ hφ V)
  naturality {V W} k := by
    apply CommRingCat.hom_ext
    refine IsLocalization.ringHom_ext (T.obj V) (RingHom.ext fun r => ?_)
    have hφnat : sectionMap F φ W ((A.O.obj.map k).hom r) =
        (C.O.obj.map (F.op.map k)).hom (sectionMap F φ V r) :=
      ConcreteCategory.congr_hom (φ.hom.naturality k) r
    have hTk : (T.localizationPresheaf.map k).hom
          (algebraMap (A.O.obj.obj V) (Localization (T.obj V)) r) =
        algebraMap (A.O.obj.obj W) (Localization (T.obj W)) ((A.O.obj.map k).hom r) :=
      (ConcreteCategory.congr_hom (T.toLocalizationPresheaf.naturality k) r).symm
    have hUk : (U.localizationPresheaf.map (F.op.map k)).hom
          (algebraMap (C.O.obj.obj (F.op.obj V)) (Localization (U.obj (F.op.obj V)))
            (sectionMap F φ V r)) =
        algebraMap (C.O.obj.obj (F.op.obj W)) (Localization (U.obj (F.op.obj W)))
          ((C.O.obj.map (F.op.map k)).hom (sectionMap F φ V r)) :=
      (ConcreteCategory.congr_hom (U.toLocalizationPresheaf.naturality (F.op.map k))
        (sectionMap F φ V r)).symm
    change T.localizationMapApp F U φ hφ W
        ((T.localizationPresheaf.map k).hom
          (algebraMap (A.O.obj.obj V) (Localization (T.obj V)) r)) =
      (U.localizationPresheaf.map (F.op.map k)).hom
        (T.localizationMapApp F U φ hφ V
          (algebraMap (A.O.obj.obj V) (Localization (T.obj V)) r))
    rw [hTk, localizationMapApp_algebraMap, localizationMapApp_algebraMap, hUk, hφnat]

/-- The fraction rules are the components of the morphism of presheaves. -/
theorem localizationPresheafMap_app (V : A.Cᵒᵖ) :
    ((T.localizationPresheafMap F U φ hφ).app V).hom = T.localizationMapApp F U φ hφ V :=
  rfl

section Sheafified

variable [HasWeakSheafify A.J CommRingCat.{w}] [HasWeakSheafify C.J CommRingCat.{w}]

/-- The morphism `T⁻¹A.O ⟶ F_* (U⁻¹C.O)` of sheaves of rings induced by a morphism
`φ : A.O ⟶ F_* C.O` of structure sheaves carrying `T` into `U`: the sheafification of the
fraction rule `AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.localizationPresheafMap`. -/
noncomputable def localizationSheafMap :
    (presheafToSheaf A.J CommRingCat.{w}).obj T.localizationPresheaf ⟶
      (F.sheafPushforwardContinuous CommRingCat.{w} A.J C.J).obj
        ((presheafToSheaf C.J CommRingCat.{w}).obj U.localizationPresheaf) :=
  ⟨sheafifyLift A.J
    (T.localizationPresheafMap F U φ hφ ≫
      Functor.whiskerLeft F.op (toSheafify C.J U.localizationPresheaf))
    ((F.sheafPushforwardContinuous CommRingCat.{w} A.J C.J).obj
      ((presheafToSheaf C.J CommRingCat.{w}).obj U.localizationPresheaf)).property⟩

/-- The induced morphism of sheaves restricts along sheafification to the fraction rule on the
presheaves of sectionwise localizations. -/
theorem localizationSheafMap_toSheafify :
    toSheafify A.J T.localizationPresheaf ≫ (T.localizationSheafMap F U φ hφ).hom =
      T.localizationPresheafMap F U φ hφ ≫
        Functor.whiskerLeft F.op (toSheafify C.J U.localizationPresheaf) :=
  toSheafify_sheafifyLift _ _ _

/-- The canonical map from the structure sheaf to the sheafified localization, written as the
sectionwise localization map followed by sheafification. -/
theorem toLocalizationSheaf_hom :
    T.toLocalizationSheaf.hom =
      T.toLocalizationPresheaf ≫ toSheafify A.J T.localizationPresheaf := by
  change (sheafificationIso A.O).hom.hom ≫ sheafifyMap A.J T.toLocalizationPresheaf = _
  rw [show (sheafificationIso A.O).hom.hom = toSheafify A.J A.O.obj by simp]
  exact (toSheafify_naturality A.J T.toLocalizationPresheaf).symm

/-- Over `V`, the map to the sheafified localization is the sectionwise localization map followed
by sheafification. -/
private theorem toLocalizationSheaf_app_apply (V : A.Cᵒᵖ) (r : A.O.obj.obj V) :
    (T.toLocalizationSheaf.hom.app V).hom r =
      ((toSheafify A.J T.localizationPresheaf).app V).hom
        ((T.toLocalizationPresheaf.app V).hom r) := by
  rw [NatTrans.congr_app T.toLocalizationSheaf_hom V]; rfl

/-- Localizing a section of `A.O` over `V` and then applying the induced morphism is applying `φ`
and then localizing over `F V`. -/
theorem localizationSheafMap_app_toLocalizationSheaf (V : A.Cᵒᵖ) (r : A.O.obj.obj V) :
    ((T.localizationSheafMap F U φ hφ).hom.app V).hom
        ((T.toLocalizationSheaf.hom.app V).hom r) =
      (U.toLocalizationSheaf.hom.app (F.op.obj V)).hom (sectionMap F φ V r) := by
  have hS : ((T.localizationSheafMap F U φ hφ).hom.app V).hom
        (((toSheafify A.J T.localizationPresheaf).app V).hom
          ((T.toLocalizationPresheaf.app V).hom r)) =
      ((toSheafify C.J U.localizationPresheaf).app (F.op.obj V)).hom
        (T.localizationMapApp F U φ hφ V ((T.toLocalizationPresheaf.app V).hom r)) := by
    rw [← localizationPresheafMap_app T F U φ hφ V]
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (T.localizationSheafMap_toSheafify F U φ hφ) V)
      ((T.toLocalizationPresheaf.app V).hom r)
  rw [toLocalizationSheaf_app_apply, hS, toLocalizationSheaf_app_apply]
  exact congrArg _ (T.localizationMapApp_algebraMap F U φ hφ V r)

/-- The square relating the two localization maps `𝒪 ⟶ 𝒪⁻¹` to `φ` and to
`AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.localizationSheafMap` commutes. -/
theorem localizationSheafMap_comp :
    T.toLocalizationSheaf ≫ T.localizationSheafMap F U φ hφ =
      φ ≫ (F.sheafPushforwardContinuous CommRingCat.{w} A.J C.J).map U.toLocalizationSheaf := by
  apply Sheaf.hom_ext
  ext V r
  exact T.localizationSheafMap_app_toLocalizationSheaf F U φ hφ V r

/-- Any morphism of sheaves of rings `T⁻¹A.O ⟶ F_* (U⁻¹C.O)` making the square of
`AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.localizationSheafMap_comp` commute is
`AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf.localizationSheafMap`. -/
theorem localizationSheafMap_unique
    (g : (presheafToSheaf A.J CommRingCat.{w}).obj T.localizationPresheaf ⟶
      (F.sheafPushforwardContinuous CommRingCat.{w} A.J C.J).obj
        ((presheafToSheaf C.J CommRingCat.{w}).obj U.localizationPresheaf))
    (hg : T.toLocalizationSheaf ≫ g =
      φ ≫ (F.sheafPushforwardContinuous CommRingCat.{w} A.J C.J).map U.toLocalizationSheaf) :
    g = T.localizationSheafMap F U φ hφ := by
  have hψ (V : A.Cᵒᵖ) (r : T.obj V) :
      IsUnit (((φ ≫ (F.sheafPushforwardContinuous CommRingCat.{w} A.J C.J).map
        U.toLocalizationSheaf).hom.app V).hom (r : A.O.obj.obj V)) :=
    U.isUnit_toLocalizationSheaf (F.op.obj V) ⟨sectionMap F φ V r, hφ V r.2⟩
  obtain ⟨g₀, _, huniq⟩ := T.existsUnique_lift_toLocalizationSheaf _ _ hψ
  exact (huniq g hg).trans (huniq _ (T.localizationSheafMap_comp F U φ hφ)).symm

end Sheafified

end AlgebraicGeometry.RingedSite.MultiplicativeSubpresheaf

end
