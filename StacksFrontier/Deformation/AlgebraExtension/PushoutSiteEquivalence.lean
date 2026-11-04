module

public import StacksFrontier.Deformation.AlgebraExtension.PushoutFunctor
public import StacksFrontier.Deformation.AlgebraExtension.SiteEquivalence

/-!
# Pushout of extensions on a site equivalent to a small site

Let `e : 𝒞 ≌ 𝒟` be an equivalence of sites whose inverse is a dense subsite, with `𝒟` small. The
pushout functor `Deformation.AlgebraExtension.pushoutFunctor` is built on the small site `𝒟`, by
the square-zero pushout of sheaves of rings there. Transporting it along the equivalence of
extension categories `Deformation.AlgebraExtension.isEquivalence_siteRestriction` gives a pushout
functor on `𝒞`, with the universal property `Deformation.AlgebraExtension.IsPushoutFunctor`.

This is how the functor `F` "given by pushout" of the situation preceding
[Stacks Project, Tag 0D3P] exists on the small étale site of an algebraic space, whose objects
lie in `Type (u + 1)`: that site is equivalent to a small model.

## Main definitions

* `Deformation.AlgebraExtension.sitePushoutFunctor`: the transported pushout functor.
* `Deformation.AlgebraExtension.isPushoutFunctor_sitePushoutFunctor`: its universal property.

## References

* [Stacks Project, Tag 0D3P](https://stacks.math.columbia.edu/tag/0D3P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v₁ w₁

namespace Deformation.AlgebraExtension

variable {C : Type v₁} [Category.{w₁} C] {D : Type u} [SmallCategory D]
  {J : GrothendieckTopology C} (K : GrothendieckTopology D) (e : C ≌ D)
  [e.inverse.IsDenseSubsite K J]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify K CommRingCat.{u}] [K.WEqualsLocallyBijective CommRingCat.{u}]
  {A O : Sheaf J CommRingCat.{u}} (a : A ⟶ O)
  {M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O)}
  (φ : M ⟶ N)

attribute [local instance] isEquivalence_siteRestriction

/-- The restriction of `φ` to `𝒟`. -/
abbrev siteModuleMap := (moduleRes K e.inverse O).map φ

/-- **The pushout functor along `φ` on `𝒞`**: restrict to `𝒟`, push out there, and come back
along the inverse of the equivalence of extension categories. -/
def sitePushoutFunctor : AlgebraExtension a M ⥤ AlgebraExtension a N :=
  siteRestriction K e a M ⋙ pushoutFunctor _ (siteModuleMap K e φ) ⋙
    (siteRestriction K e a N).asEquivalence.inverse

/-- The counit of the equivalence of categories of extensions of `N`, at the pushout of the
restriction of `P`. -/
abbrev siteCounit (P : AlgebraExtension a M) :=
  (siteRestriction K e a N).asEquivalence.counitIso.app
    ((pushoutFunctor _ (siteModuleMap K e φ)).obj ((siteRestriction K e a M).obj P))

omit [HasWeakSheafify K CommRingCat] [K.WEqualsLocallyBijective CommRingCat] in
/-- The restriction of `φ` to `𝒟` agrees with `φ` under the identifications of the restricted
modules. -/
theorem siteModuleMap_comm (V : Dᵒᵖ)
    (m : ((moduleRes K e.inverse O).obj M).val.obj V) :
    (idModuleComparison K e a N).μ V ((siteModuleMap K e φ).val.app V m) =
      φ.val.app (e.inverse.op.obj V) ((idModuleComparison K e a M).μ V m) :=
  rfl

/-- The restriction to `𝒟` of the comparison `P ⟶ F(P)`. -/
def sitePushoutιRestricted (P : AlgebraExtension a M) :
    MapAlong (siteModuleMap K e φ) ((siteRestriction K e a M).obj P)
      ((siteRestriction K e a N).obj ((sitePushoutFunctor K e a φ).obj P)) :=
  MapAlong.comp ((isPushoutFunctor_pushoutFunctor _ (siteModuleMap K e φ)).ι _)
    (siteCounit K e a φ P).inv (Category.comp_id _)

/-- There is a map `P ⟶ F(P)` along `φ` whose restriction to `𝒟` is `sitePushoutιRestricted`. -/
theorem exists_sitePushoutι (P : AlgebraExtension a M) :
    ∃ f : MapAlong φ P ((sitePushoutFunctor K e a φ).obj P),
      (ringRes K e.inverse).map f.hom = (sitePushoutιRestricted K e a φ P).hom :=
  MapAlong.exists_restrictVia_eq (idModuleComparison K e a M) (idModuleComparison K e a N)
    (siteModuleMap_comm K e a φ) _

/-- The comparison `P ⟶ F(P)` along `φ`. -/
def sitePushoutι (P : AlgebraExtension a M) : MapAlong φ P ((sitePushoutFunctor K e a φ).obj P) :=
  (exists_sitePushoutι K e a φ P).choose

/-- The restriction to `𝒟` of `sitePushoutι` is the comparison map of the pushout on `𝒟`
followed by the inverse of the counit. -/
theorem ringRes_map_sitePushoutι (P : AlgebraExtension a M) :
    (ringRes K e.inverse).map (sitePushoutι K e a φ P).hom =
      ((isPushoutFunctor_pushoutFunctor _ (siteModuleMap K e φ)).ι _).hom ≫
        (siteCounit K e a φ P).inv.hom :=
  (exists_sitePushoutι K e a φ P).choose_spec

/-- The underlying ring maps of the inverse of `siteCounit` and of `siteCounit` compose to the
identity. -/
theorem siteCounit_inv_hom_hom (P : AlgebraExtension a M) :
    (siteCounit K e a φ P).inv.hom ≫ (siteCounit K e a φ P).hom.hom = 𝟙 _ :=
  congrArg MapAlong.hom (siteCounit K e a φ P).inv_hom_id

/-- Naturality of the inverse of `siteCounit` in the extension `P`, on underlying ring maps. -/
theorem siteCounit_naturality {P P' : AlgebraExtension a M} (k : P ⟶ P') :
    ((pushoutFunctor _ (siteModuleMap K e φ)).map ((siteRestriction K e a M).map k)).hom ≫
        (siteCounit K e a φ P').inv.hom =
      (siteCounit K e a φ P).inv.hom ≫
        (ringRes K e.inverse).map ((sitePushoutFunctor K e a φ).map k).hom :=
  congrArg MapAlong.hom ((siteRestriction K e a N).asEquivalence.counitIso.inv.naturality _)

/-- **The transported pushout functor has the universal property of pushout along `φ`.** -/
def isPushoutFunctor_sitePushoutFunctor : IsPushoutFunctor φ (sitePushoutFunctor K e a φ) where
  ι := sitePushoutι K e a φ
  naturality {P P'} k := (ringRes K e.inverse).map_injective <| by
    refine ((ringRes K e.inverse).map_comp _ _).trans (Eq.trans ?_
      ((ringRes K e.inverse).map_comp _ _).symm)
    refine (congrArg (· ≫ (ringRes K e.inverse).map ((sitePushoutFunctor K e a φ).map k).hom)
      (ringRes_map_sitePushoutι K e a φ P)).trans (Eq.trans ?_
        (congrArg ((ringRes K e.inverse).map k.hom ≫ ·)
          (ringRes_map_sitePushoutι K e a φ P')).symm)
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (siteCounit_naturality K e a φ k).symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (siteCounit K e a φ P').inv.hom)
          ((isPushoutFunctor_pushoutFunctor _ (siteModuleMap K e φ)).naturality
            ((siteRestriction K e a M).map k))).trans (Category.assoc _ _ _))))
  desc_unique P Q h := by
    let h' := MapAlong.restrictVia (idRingComparison K e a) (idModuleComparison K e a M)
      (idModuleComparison K e a N) (siteModuleMap_comm K e a φ) h
    obtain ⟨k', hk', hku⟩ := (isPushoutFunctor_pushoutFunctor ((ringRes K e.inverse).map a)
      (siteModuleMap K e φ)).desc_unique _ _ h'
    let RN := siteRestriction K e a N
    obtain ⟨k, hk⟩ := RN.map_surjective ((siteCounit K e a φ P).hom ≫ k')
    refine ⟨k, (ringRes K e.inverse).map_injective ?_, fun k₂ hk₂ => RN.map_injective ?_⟩
    · refine ((ringRes K e.inverse).map_comp _ _).trans ?_
      refine (congrArg₂ (· ≫ ·) (ringRes_map_sitePushoutι K e a φ P)
        (congrArg MapAlong.hom hk)).trans ?_
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ k'.hom)
          (siteCounit_inv_hom_hom K e a φ P)).trans (Category.id_comp _)))).trans hk')
    · have h2 : (siteCounit K e a φ P).inv ≫ RN.map k₂ = k' := by
        refine hku _ ((Category.assoc _ _ _).symm.trans ?_)
        refine (congrArg (· ≫ (ringRes K e.inverse).map k₂.hom)
          (ringRes_map_sitePushoutι K e a φ P).symm).trans ?_
        exact ((ringRes K e.inverse).map_comp _ _).symm.trans
          (congrArg (ringRes K e.inverse).map hk₂)
      exact ((Iso.hom_inv_id_assoc (siteCounit K e a φ P) (RN.map k₂)).symm.trans
        (congrArg ((siteCounit K e a φ P).hom ≫ ·) h2)).trans hk.symm

end Deformation.AlgebraExtension

end
