module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.ArtinianLocalRing
public import StacksFrontier.AlgebraicGeometry.Pushout.SchemePushout
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.RimSchlessinger
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.ResidueField.Basic

/-!
# Change of field for a point of a category fibred in groupoids over the big fppf site

Let `𝒳` be a category fibred in groupoids over the big fppf site `(Sch/S)_{fppf}`, let `x₀` be an
object of `𝒳` lying over `Spec k` for a field `k` of finite type over `S`, let `l/k` be a finite
extension, and let `x_{l,0}` be a restriction of `x₀` to `Spec l`. An object of the category
`(𝓕_{𝒳,k,x₀})_{l/k}` obtained from the predeformation category of `x₀` by change of residue field
is a deformation of `x₀` over `A ×_l k`, for `A` an Artinian local `Λ`-algebra with residue field
`l`; restricting it along `Spec A ⟶ Spec (A ×_l k)` gives a deformation of `x_{l,0}` over `A`.
This file builds the resulting canonical functor `(𝓕_{𝒳,k,x₀})_{l/k} ⥤ 𝓕_{𝒳,l,x_{l,0}}` over
`𝒞_{Λ,l}`, and proves it is an equivalence when `𝒳` satisfies (RS).

This is the first of the four parts of
`StacksFrontier.Deformation.Artin.ChangeOfField.SiteRestriction`:
it contains the site-level helpers, the projections `comparisonProjection` and
`deformationProjection`, and the objects of the big fppf site over the changed base
`Spec (A ×_l k)`. The functor is built in `SiteRestriction.Functor`; that it is an equivalence is
proved in `SiteRestriction.EssSurj` and `SiteRestriction.Equivalence`.

## Main definitions

* `Deformation.Artin.Site.comparisonProjection` — the first projection `A ×_l k ⟶ A` of a
  comparison algebra of Tag 07W8.
* `Deformation.Artin.Site.deformationProjection` — that projection read on the base of a
  deformation through the identification carried by an object of `(𝓕_{𝒳,k,x₀})_{l/k}`.
* `Deformation.Artin.Site.ChangeOfFieldFunctor` specifies the restriction functor: a functor over
  `𝒞_{Λ,l}` together with, for each object, a cartesian restricting arrow of `𝒳` lying over
  `Spec A ⟶ Spec (A ×_l k)`, compatible with the distinguished arrows out of `x_{l,0}` and
  natural in morphisms of deformations.

## Main results

* `Deformation.Artin.Site.changeOfFieldFunctor` constructs the canonical functor.
* `Deformation.Artin.Site.changeOfFieldFunctor_isEquivalence` proves that it is an equivalence
  when `𝒳` satisfies (RS).

## References

* [Stacks Project, Tag 07WX](https://stacks.math.columbia.edu/tag/07WX)
* [Stacks Project, Tag 07WP](https://stacks.math.columbia.edu/tag/07WP)
* [Stacks Project, Tag 07W8](https://stacks.math.columbia.edu/tag/07W8)
* [Stacks Project, Tag 0ET0](https://stacks.math.columbia.edu/tag/0ET0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace Deformation.Artin.Site

attribute [local implicit_reducible] CategoryTheory.Over.post
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.mk
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
  CategoryTheory.Limits.CategoricalPullback.π₁
  CategoryTheory.Limits.CategoricalPullback.π₂

@[implicit_reducible] private noncomputable def siteObjectOver
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {Z : Scheme.{u}}
    (hZ : B.Contains Z) (f : Z ⟶ S) : AlgebraicGeometry.BigFppfOver B S hS :=
  Over.mk (Classical.choose
    (B.inclusion.map_surjective (X := B.obj hZ) (Y := B.obj hS) f))

private theorem siteObjectOver_post
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z : Scheme.{u}} (hZ : B.Contains Z) (f : Z ⟶ S) :
    (Over.post (X := B.obj hS) B.inclusion).obj
      (siteObjectOver B S hS hZ f) = Over.mk f := by
  show Over.mk (B.inclusion.map (Classical.choose
    (B.inclusion.map_surjective (X := B.obj hZ) (Y := B.obj hS) f))) = Over.mk f
  congr 1
  exact Classical.choose_spec
    (B.inclusion.map_surjective (X := B.obj hZ) (Y := B.obj hS) f)

@[implicit_reducible] private noncomputable def siteObjectOverFiniteType
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z : Scheme.{u}} (f : Z ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] :
    AlgebraicGeometry.BigFppfOver B S hS :=
  siteObjectOver B S hS (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact f hS) f

private theorem siteObjectOverFiniteType_post
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z : Scheme.{u}} (f : Z ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] :
    (Over.post (X := B.obj hS) B.inclusion).obj
      (siteObjectOverFiniteType B S hS f) = Over.mk f :=
  siteObjectOver_post B S hS
    (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact f hS) f

private theorem contains_domain_of_post_eq
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS) {Z : Scheme.{u}} (f : Z ⟶ S)
    (hU : (Over.post (X := B.obj hS) B.inclusion).obj U = Over.mk f) :
    B.Contains Z := by
  have hz := congrArg Over.left hU
  change B.inclusion.obj U.left = Z at hz
  exact hz ▸ U.left.property

private theorem finiteType_of_residuePoint
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) {S : Scheme.{u}}
    (f : Spec (.of A) ⟶ S)
    (hf : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫ f) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫ f)) :
    LocallyOfFiniteType f ∧ QuasiCompact f := by
  let e : Spec (.of k) ≅ Spec (.of (IsLocalRing.ResidueField A)) :=
    Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso A.residueEquiv.toRingEquiv).op
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) =
      Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) := by
    simp [e, Deformation.Artin.residueMap]
  have hg : Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ f =
      e.inv ≫ Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫ f := by
    rw [← he]
    simp
  have := hf.1
  have := hf.2
  exact (AlgebraicGeometry.finiteType_iff_residueField_comp_finiteType S A f).2
    (by rw [hg]; exact ⟨inferInstance, inferInstance⟩)

private theorem spec_algebraMap_kl_finiteType
    (T : Deformation.ChangeOfFieldsSituation.{u, u, u}) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap T.k T.l))) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.k T.l))) := by
  have : Module.Finite T.k T.l := T.finiteKL
  have : CompactSpace (Spec (.of T.l)) := Scheme.compactSpace_of_isAffine _
  exact ⟨HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance),
    inferInstance⟩

/-- The composite of `Spec.map` of two ring maps is `Spec.map` of their composite. -/
private theorem spec_map_comp_ofHom {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R'']
    (f : R →+* R') (g : R' →+* R'') :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom (g.comp f)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

private theorem changeFieldPoint_finiteType
    (T : Deformation.ChangeOfFieldsSituation.{u, u, u}) {S : Scheme.{u}}
    (iΛ : Spec (.of T.Λ) ⟶ S)
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ)) :
    LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ) := by
  obtain ⟨hloc, hqc⟩ := spec_algebraMap_kl_finiteType T
  obtain ⟨h₁, h₂⟩ := hfinite
  have hpoint : Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) =
    Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) := by
    rw [spec_map_comp_ofHom, ← IsScalarTower.algebraMap_eq]
  rw [← hpoint, Category.assoc]
  exact ⟨inferInstance, inferInstance⟩

private theorem residueMap_comp_algebraMap
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :
    (Deformation.Artin.residueMap A).comp (algebraMap Λ A) = algebraMap Λ k := by
  ext x
  show A.residueEquiv
    (IsLocalRing.residue A (algebraMap Λ A x)) = algebraMap Λ k x
  rw [← IsLocalRing.ResidueField.algebraMap_eq (R := A)]
  exact A.residueEquiv.commutes x

private theorem residuePoint_base
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S) :
    Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ =
    Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ := by
  rw [← Category.assoc, spec_map_comp_ofHom, residueMap_comp_algebraMap]

private theorem finiteType_of_baseArtinian
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :
    LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) := by
  refine finiteType_of_residuePoint A _ ?_
  rw [residuePoint_base A iΛ]
  exact hfinite

@[implicit_reducible] private noncomputable def siteObjectOverHom
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z W : Scheme.{u}} (hZ : B.Contains Z) (hW : B.Contains W)
    (fZ : Z ⟶ S) (fW : W ⟶ S) (g : Z ⟶ W) (hg : g ≫ fW = fZ) :
    siteObjectOver B S hS hZ fZ ⟶ siteObjectOver B S hS hW fW := by
  let m := Classical.choose
    (B.inclusion.map_surjective (X := B.obj hZ) (Y := B.obj hW) g)
  have hm : B.inclusion.map m = g := Classical.choose_spec
    (B.inclusion.map_surjective (X := B.obj hZ) (Y := B.obj hW) g)
  refine Over.homMk m ?_
  apply B.inclusion.map_injective
  change B.inclusion.map (m ≫ Classical.choose
      (B.inclusion.map_surjective (X := B.obj hW) (Y := B.obj hS) fW)) =
    B.inclusion.map (Classical.choose
      (B.inclusion.map_surjective (X := B.obj hZ) (Y := B.obj hS) fZ))
  rw [Functor.map_comp, hm,
    Classical.choose_spec (B.inclusion.map_surjective (X := B.obj hW) (Y := B.obj hS) fW),
    Classical.choose_spec (B.inclusion.map_surjective (X := B.obj hZ) (Y := B.obj hS) fZ)]
  exact hg

@[local simp] private theorem siteObjectOverHom_underlying
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z W : Scheme.{u}} (hZ : B.Contains Z) (hW : B.Contains W)
    (fZ : Z ⟶ S) (fW : W ⟶ S) (g : Z ⟶ W) (hg : g ≫ fW = fZ) :
    B.inclusion.map (siteObjectOverHom B S hS hZ hW fZ fW g hg).left = g :=
  Classical.choose_spec
    (B.inclusion.map_surjective (X := B.obj hZ) (Y := B.obj hW) g)

@[implicit_reducible] private noncomputable def liftFullMap
    {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) [F.Full] {X Y : C} (f : F.obj X ⟶ F.obj Y) : X ⟶ Y :=
  Classical.choose (F.map_surjective f)

private theorem map_liftFullMap
    {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) [F.Full] {X Y : C} (f : F.obj X ⟶ F.obj Y) :
    F.map (liftFullMap F f) = f :=
  Classical.choose_spec (F.map_surjective f)

@[implicit_reducible] private noncomputable def liftIsoFullFaithful
    {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) [F.Full] [F.Faithful] {X Y : C}
    (e : F.obj X ≅ F.obj Y) : X ≅ Y where
  hom := liftFullMap F e.hom
  inv := liftFullMap F e.inv
  hom_inv_id := F.map_injective (by
    rw [F.map_comp, map_liftFullMap, map_liftFullMap, F.map_id]
    exact e.hom_inv_id)
  inv_hom_id := F.map_injective (by
    rw [F.map_comp, map_liftFullMap, map_liftFullMap, F.map_id]
    exact e.inv_hom_id)

@[implicit_reducible] private noncomputable def siteObjectOverIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z : Scheme.{u}} (hZ : B.Contains Z) (f : Z ⟶ S)
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (hU : (Over.post (X := B.obj hS) B.inclusion).obj U = Over.mk f) :
    siteObjectOver B S hS hZ f ≅ U :=
  liftIsoFullFaithful (Over.post (X := B.obj hS) B.inclusion)
    (eqToIso ((siteObjectOver_post B S hS hZ f).trans hU.symm))

private theorem siteObjectOverIso_post_hom
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z : Scheme.{u}} (hZ : B.Contains Z) (f : Z ⟶ S)
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (hU : (Over.post (X := B.obj hS) B.inclusion).obj U = Over.mk f) :
    (Over.post (X := B.obj hS) B.inclusion).map
        (siteObjectOverIso B S hS hZ f U hU).hom =
      (eqToIso ((siteObjectOver_post B S hS hZ f).trans hU.symm)).hom :=
  map_liftFullMap (Over.post (X := B.obj hS) B.inclusion)
    ((eqToIso ((siteObjectOver_post B S hS hZ f).trans hU.symm)).hom)

/-- Factor a morphism through a Cartesian arrow when its base map factors through
the arrow's base map. -/
private theorem cartesian_factor_of_fibered
    {C : Type*} [Category C] {X : Type*} [Category X]
    (p : X ⥤ C) [p.IsFibered]
    {a b a' : X} (φ : a ⟶ b) [p.IsCartesian (p.map φ) φ]
    (g : p.obj a' ⟶ p.obj a) (ψ : a' ⟶ b)
    (h : p.map ψ = g ≫ p.map φ) :
    ∃! χ : a' ⟶ a, p.IsHomLift g χ ∧ χ ≫ φ = ψ := by
  have : p.IsStronglyCartesian (p.map φ) φ := inferInstance
  have : p.IsHomLift (g ≫ p.map φ) ψ :=
    h.symm ▸ (show p.IsHomLift (p.map ψ) ψ from inferInstance)
  exact CategoryTheory.Functor.IsStronglyCartesian.universal_property
    p (p.map φ) φ g (g ≫ p.map φ) rfl ψ

private theorem cartesian_factor_of_strongly_cartesian
    {C : Type*} [Category C] {X : Type*} [Category X]
    (p : X ⥤ C) {R S : C} (f : R ⟶ S)
    {a b a' : X} (φ : a ⟶ b) [p.IsStronglyCartesian f φ]
    (g : p.obj a' ⟶ R) (ψ : a' ⟶ b)
    (hb : p.obj b = S)
    (h : p.map ψ = g ≫ f ≫ eqToHom hb.symm) :
    ∃! χ : a' ⟶ a, p.IsHomLift g χ ∧ χ ≫ φ = ψ := by
  cases hb
  have h' : p.map ψ = g ≫ f := by simpa using h
  have : p.IsHomLift (g ≫ f) ψ := h'.symm ▸ inferInstance
  exact CategoryTheory.Functor.IsStronglyCartesian.universal_property
    p f φ g (g ≫ f) rfl ψ

private structure ChosenCartesianLift
    {A : Type*} [Category A] {C : Type*} [Category C]
    (p : A ⥤ C) {V U : C} (f : V ⟶ U) (x : A) (hx : p.obj x = U) where
  obj : A
  arrow : obj ⟶ x
  isHomLift : p.IsHomLift f arrow

@[implicit_reducible] private noncomputable def chosenCartesianLift
    {A : Type*} [Category A] {C : Type*} [Category C]
    (p : A ⥤ C) (hp : p.IsFiberedInGroupoids)
    {V U : C} (f : V ⟶ U) (x : A) (hx : p.obj x = U) :
    ChosenCartesianLift p f x hx := by
  let y := Classical.choose (hp.exists_lift f x hx)
  let φ := Classical.choose (Classical.choose_spec (hp.exists_lift f x hx))
  let hφ := Classical.choose_spec
    (Classical.choose_spec (hp.exists_lift f x hx))
  exact ⟨y, φ, hφ⟩

@[implicit_reducible] private def schemeMap {C : Type*} [Category C] {S : Scheme.{u}}
    (q : C ⥤ Over S) {x y : C} {U V : Scheme.{u}}
    {fU : U ⟶ S} {fV : V ⟶ S}
    (hx : q.obj x = Over.mk fU) (hy : q.obj y = Over.mk fV) (f : x ⟶ y) : U ⟶ V :=
  eqToHom (congrArg Over.left hx).symm ≫ (q.map f).left ≫
    eqToHom (congrArg Over.left hy)

private theorem schemeMap_comp {C : Type*} [Category C] {S : Scheme.{u}}
    (q : C ⥤ Over S) {x y z : C} {U V W : Scheme.{u}}
    {fU : U ⟶ S} {fV : V ⟶ S} {fW : W ⟶ S}
    (hx : q.obj x = Over.mk fU) (hy : q.obj y = Over.mk fV)
    (hz : q.obj z = Over.mk fW) (f : x ⟶ y) (g : y ⟶ z) :
    schemeMap q hx hz (f ≫ g) = schemeMap q hx hy f ≫ schemeMap q hy hz g := by
  simp [schemeMap, Category.assoc]

private theorem schemeMap_eq_iff {C : Type*} [Category C] {S : Scheme.{u}}
    (q : C ⥤ Over S) {x y : C} {U V : Scheme.{u}}
    {fU : U ⟶ S} {fV : V ⟶ S}
    (hx : q.obj x = Over.mk fU) (hy : q.obj y = Over.mk fV) (f g : x ⟶ y) :
    schemeMap q hx hy f = schemeMap q hx hy g ↔ q.map f = q.map g := by
  simp only [schemeMap, cancel_epi, cancel_mono]
  exact ⟨Over.OverMorphism.ext, congrArg Over.Hom.left⟩

private theorem cartesian_cancel
    {C : Type*} [Category C] {D : Type*} [Category D]
    (p : C ⥤ D) (hp : p.IsFiberedInGroupoids)
    {x y z : C} (r : y ⟶ z) {f g : x ⟶ y}
    (hb : p.map f = p.map g) (h : f ≫ r = g ≫ r) : f = g := by
  have : p.IsStronglyCartesian (p.map r) r := hp.isStronglyCartesian_homLift _ _
  have : p.IsHomLift (p.map f) g := hb.symm ▸ (IsHomLift.map p g)
  exact Functor.IsStronglyCartesian.ext p (p.map r) r (p.map f) h

@[implicit_reducible] private noncomputable def siteMapOfSchemes
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {x y : AlgebraicGeometry.BigFppfOver B S hS} {U V : Scheme.{u}}
    {fU : U ⟶ S} {fV : V ⟶ S}
    (hx : (Over.post B.inclusion).obj x = Over.mk fU)
    (hy : (Over.post B.inclusion).obj y = Over.mk fV)
    (f : U ⟶ V) (hf : f ≫ fV = fU) : x ⟶ y :=
  (Over.post B.inclusion).preimage
    (eqToHom hx ≫ Over.homMk (V := Over.mk fV) f hf ≫ eqToHom hy.symm)

private theorem siteMapOfSchemes_base
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {x y : AlgebraicGeometry.BigFppfOver B S hS} {U V : Scheme.{u}}
    {fU : U ⟶ S} {fV : V ⟶ S}
    (hx : (Over.post B.inclusion).obj x = Over.mk fU)
    (hy : (Over.post B.inclusion).obj y = Over.mk fV)
    (f : U ⟶ V) (hf : f ≫ fV = fU) :
    schemeMap (Over.post B.inclusion) hx hy
      (siteMapOfSchemes B S hS hx hy f hf) = f := by
  unfold schemeMap siteMapOfSchemes
  rw [Functor.map_preimage]
  simp [Category.assoc]

section Construction

variable (T : Deformation.ChangeOfFieldsSituation.{u, u, u})
variable {S : Scheme.{u}}
variable (iΛ : Spec (.of T.Λ) ⟶ S)
variable (B : AlgebraicGeometry.BigFppfSite.{u}) (hS : B.Contains S)
variable {X : Type v} [Category.{w} X]
variable (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
variable (x₀ xₗ : X)
variable (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ =
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
variable (hxₗ : (p ⋙ Over.post B.inclusion).obj xₗ =
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ))
variable (η : xₗ ⟶ x₀)

/-- The category structure on the predeformation category of `x₀`. -/
local instance : Category.{max u w}
    (Deformation.Artin.predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀).carrier :=
  (Deformation.Artin.predeformationCategory iΛ
    (p ⋙ Over.post B.inclusion) x₀ hx₀).category

/-- The category structure on the predeformation category of `x_{l,0}`. -/
local instance : Category.{max u w}
    (Deformation.Artin.predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) xₗ hxₗ).carrier :=
  (Deformation.Artin.predeformationCategory iΛ
    (p ⋙ Over.post B.inclusion) xₗ hxₗ).category

/-- The first projection `B ×_l k → B`, transported to the comparison algebra. -/
public def comparisonProjection
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} T.Λ T.l) :
    (Deformation.comparisonFunctor T).functor.obj A →+* A :=
  (RingHom.pullbackFst (Deformation.residueMap T A) (algebraMap T.k T.l)).comp
    ((Deformation.comparisonFunctor T).pullbackEquiv A).toRingHom

/-- The ring map from the algebra of a changed deformation to its new base. -/
public def deformationProjection
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    ((Deformation.Artin.predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst).algebra →+* a.snd :=
  (comparisonProjection T a.snd).comp
    (eqToHom ((Deformation.Artin.predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀).object_projection a.fst).symm ≫
      a.iso.hom).hom.toRingHom

private theorem comparisonProjection_algebraMap
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} T.Λ T.l) (r : T.Λ) :
    comparisonProjection T A (algebraMap T.Λ
      ((Deformation.comparisonFunctor T).functor.obj A) r) = algebraMap T.Λ A r := by
  simp [comparisonProjection, RingHom.comp_apply,
    (Deformation.comparisonFunctor T).algebraMap_fst]

private theorem comparisonProjection_residueMap
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} T.Λ T.l) :
    (Deformation.residueMap T A).comp (comparisonProjection T A) =
      (algebraMap T.k T.l).comp
        (Deformation.Artin.residueMap ((Deformation.comparisonFunctor T).functor.obj A)) := by
  ext x
  show (Deformation.residueMap T A)
      (((Deformation.comparisonFunctor T).pullbackEquiv A x).val.1) =
    (algebraMap T.k T.l)
      (((Deformation.comparisonFunctor T).functor.obj A).residueEquiv
        (IsLocalRing.residue _ x))
  rw [(Deformation.comparisonFunctor T).residue_snd A x]
  exact ((Deformation.comparisonFunctor T).pullbackEquiv A x).property

private theorem comparisonProjection_natural
    {A A' : Deformation.ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (f : A ⟶ A') :
    (comparisonProjection T A').comp
        ((Deformation.comparisonFunctor T).functor.map f).hom.toRingHom =
      f.hom.toRingHom.comp (comparisonProjection T A) := by
  ext x
  show ((Deformation.comparisonFunctor T).pullbackEquiv A'
      (((Deformation.comparisonFunctor T).functor.map f).hom x)).val.1 =
    f.hom.toRingHom
      (((Deformation.comparisonFunctor T).pullbackEquiv A x).val.1)
  exact (Deformation.comparisonFunctor T).map_fst f x

private theorem artinianResidueMap_natural
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (A A' : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) (f : A ⟶ A') :
    (Deformation.Artin.residueMap A').comp f.hom.toRingHom = Deformation.Artin.residueMap A := by
  ext x
  exact f.residue_comm x

private theorem deformationProjection_algebraMap
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) (r : T.Λ) :
    deformationProjection T iΛ B hS p x₀ hx₀ a
      (algebraMap T.Λ ((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst).algebra r) =
      algebraMap T.Λ a.snd r := by
  simp [deformationProjection, comparisonProjection_algebraMap]

private theorem deformationProjection_comp_algebraMap
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    (deformationProjection T iΛ B hS p x₀ hx₀ a).comp
      (algebraMap T.Λ ((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst).algebra) =
      algebraMap T.Λ a.snd := by
  ext r
  exact deformationProjection_algebraMap T iΛ B hS p x₀ hx₀ a r

private theorem deformationProjection_residueMap
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    (Deformation.residueMap T a.snd).comp
      (deformationProjection T iΛ B hS p x₀ hx₀ a) =
      (algebraMap T.k T.l).comp (Deformation.Artin.residueMap
        ((Deformation.Artin.predeformationCategory iΛ
          (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst).algebra) := by
  unfold deformationProjection
  rw [← RingHom.comp_assoc, comparisonProjection_residueMap,
    RingHom.comp_assoc]
  exact congrArg ((algebraMap T.k T.l).comp)
    (artinianResidueMap_natural _ _
      ((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).object_projection a.fst ▸ a.iso.hom))

private theorem deformationProjection_natural
    (a b : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection)
    (f : a ⟶ b) :
    (deformationProjection T iΛ B hS p x₀ hx₀ b).comp
        ((Deformation.Artin.predeformationCategory iΛ
          (p ⋙ Over.post B.inclusion) x₀ hx₀).morphisms a.fst b.fst f.fst).ringHom.hom.toRingHom =
      f.snd.hom.toRingHom.comp
        (deformationProjection T iΛ B hS p x₀ hx₀ a) := by
  have hmor : ((Deformation.Artin.predeformationCategory iΛ
          (p ⋙ Over.post B.inclusion) x₀ hx₀).morphisms a.fst b.fst f.fst).ringHom ≫
        eqToHom ((Deformation.Artin.predeformationCategory iΛ
          (p ⋙ Over.post B.inclusion) x₀ hx₀).object_projection b.fst).symm ≫ b.iso.hom =
      (eqToHom ((Deformation.Artin.predeformationCategory iΛ
          (p ⋙ Over.post B.inclusion) x₀ hx₀).object_projection a.fst).symm ≫ a.iso.hom) ≫
        (Deformation.comparisonFunctor T).functor.map f.snd := by
    rw [← (Deformation.Artin.predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀).morphism_projection f.fst]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [f.w]
  let C₀ := Deformation.Artin.predeformationCategory iΛ
    (p ⋙ Over.post B.inclusion) x₀ hx₀
  calc
    (deformationProjection T iΛ B hS p x₀ hx₀ b).comp
        (C₀.morphisms a.fst b.fst f.fst).ringHom.hom.toRingHom =
      RingHom.comp (comparisonProjection T b.snd)
        (((eqToHom (C₀.object_projection a.fst).symm ≫ a.iso.hom) ≫
          (Deformation.comparisonFunctor T).functor.map f.snd).hom.toRingHom) := by
      rw [← hmor, deformationProjection]
      rfl
    _ = RingHom.comp (comparisonProjection T b.snd)
        (RingHom.comp ((Deformation.comparisonFunctor T).functor.map f.snd).hom.toRingHom
          (eqToHom (C₀.object_projection a.fst).symm ≫ a.iso.hom).hom.toRingHom) := rfl
    _ = RingHom.comp f.snd.hom.toRingHom
        (RingHom.comp (comparisonProjection T a.snd)
          (eqToHom (C₀.object_projection a.fst).symm ≫ a.iso.hom).hom.toRingHom) := by
      rw [← RingHom.comp_assoc, comparisonProjection_natural, RingHom.comp_assoc]
    _ = f.snd.hom.toRingHom.comp
        (deformationProjection T iΛ B hS p x₀ hx₀ a) := by
      rw [deformationProjection]

private theorem deformationProjection_residuePoint
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    Spec.map (CommRingCat.ofHom (Deformation.residueMap T a.snd)) ≫
      Spec.map (CommRingCat.ofHom (deformationProjection T iΛ B hS p x₀ hx₀ a)) =
    Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)) ≫
      Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap
        ((Deformation.Artin.predeformationCategory iΛ
          (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst).algebra)) := by
  rw [spec_map_comp_ofHom, spec_map_comp_ofHom, deformationProjection_residueMap]

private theorem deformationProjection_base
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    Spec.map (CommRingCat.ofHom (deformationProjection T iΛ B hS p x₀ hx₀ a)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap T.Λ
        ((Deformation.Artin.predeformationCategory iΛ
          (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst).algebra)) =
    Spec.map (CommRingCat.ofHom (algebraMap T.Λ a.snd)) := by
  rw [spec_map_comp_ofHom, deformationProjection_comp_algebraMap]

private theorem deformationProjection_locallyOfFiniteType_quasiCompact
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (deformationProjection T iΛ B hS p x₀ hx₀ a))) ∧
      QuasiCompact
        (Spec.map (CommRingCat.ofHom (deformationProjection T iΛ B hS p x₀ hx₀ a))) := by
  let A₀ := (Deformation.Artin.predeformationCategory iΛ
    (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst |>.algebra
  let f := Spec.map (CommRingCat.ofHom (deformationProjection T iΛ B hS p x₀ hx₀ a))
  have hsurj : Function.Surjective (Deformation.Artin.residueMap A₀) := by
    intro y
    obtain ⟨z, hz⟩ := A₀.residueEquiv.surjective y
    obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective z
    exact ⟨x, by simp [Deformation.Artin.residueMap, hx, hz]⟩
  have : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A₀))) :=
    IsClosedImmersion.spec_of_surjective _ hsurj
  obtain ⟨hfieldFT, hfieldQC⟩ := spec_algebraMap_kl_finiteType T
  have hres : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap a.snd)) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)) ≫
        Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A₀)) := by
    dsimp [f, A₀]
    exact deformationProjection_residuePoint T iΛ B hS p x₀ hx₀ a
  refine finiteType_of_residuePoint a.snd f ?_
  rw [hres]
  exact ⟨inferInstance, inferInstance⟩

private theorem contains_changedBase
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    B.Contains (Spec (.of a.snd)) := by
  let C₀ := Deformation.Artin.predeformationCategory iΛ
    (p ⋙ Over.post B.inclusion) x₀ hx₀
  let d := C₀.objects a.fst
  let f₀ := Spec.map (CommRingCat.ofHom (algebraMap T.Λ d.algebra)) ≫ iΛ
  have hZ₀ : B.Contains (Spec (.of d.algebra)) :=
    contains_domain_of_post_eq B S hS (p.obj d.point) f₀ d.base
  have hfinite := deformationProjection_locallyOfFiniteType_quasiCompact
    T iΛ B hS p x₀ hx₀ a
  have : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (deformationProjection T iΛ B hS p x₀ hx₀ a))) := hfinite.1
  have : QuasiCompact
      (Spec.map (CommRingCat.ofHom (deformationProjection T iΛ B hS p x₀ hx₀ a))) := hfinite.2
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
    (Spec.map (CommRingCat.ofHom (deformationProjection T iΛ B hS p x₀ hx₀ a))) hZ₀

@[implicit_reducible] private noncomputable def siteObjectOverChangedBase
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    AlgebraicGeometry.BigFppfOver B S hS :=
  siteObjectOver B S hS (contains_changedBase T iΛ B hS p x₀ hx₀ a)
    (Spec.map (CommRingCat.ofHom (algebraMap T.Λ a.snd)) ≫ iΛ)

private theorem siteObjectOverChangedBase_post
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    (Over.post (X := B.obj hS) B.inclusion).obj
      (siteObjectOverChangedBase T iΛ B hS p x₀ hx₀ a) =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ a.snd)) ≫ iΛ) :=
  siteObjectOver_post B S hS (contains_changedBase T iΛ B hS p x₀ hx₀ a)
    (Spec.map (CommRingCat.ofHom (algebraMap T.Λ a.snd)) ≫ iΛ)

@[implicit_reducible] private noncomputable def siteObjectOverChangedBaseToDeformation
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    siteObjectOverChangedBase T iΛ B hS p x₀ hx₀ a ⟶
      p.obj ((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst).point := by
  let C₀ := Deformation.Artin.predeformationCategory iΛ
    (p ⋙ Over.post B.inclusion) x₀ hx₀
  let d := C₀.objects a.fst
  let f₀ := Spec.map (CommRingCat.ofHom (algebraMap T.Λ d.algebra)) ≫ iΛ
  have hZ₀ : B.Contains (Spec (.of d.algebra)) :=
    contains_domain_of_post_eq B S hS (p.obj d.point) f₀ d.base
  let W₀ := siteObjectOver B S hS hZ₀ f₀
  letI : B.Contains (Spec (.of a.snd)) :=
    contains_changedBase T iΛ B hS p x₀ hx₀ a
  let fₗ := Spec.map (CommRingCat.ofHom (algebraMap T.Λ a.snd)) ≫ iΛ
  let g := Spec.map (CommRingCat.ofHom (deformationProjection T iΛ B hS p x₀ hx₀ a))
  have hg : g ≫ f₀ = fₗ := by
    dsimp [g, f₀, fₗ]
    exact congrArg (fun q => q ≫ iΛ)
      (deformationProjection_base T iΛ B hS p x₀ hx₀ a)
  have e : W₀ ≅ p.obj d.point :=
    siteObjectOverIso B S hS hZ₀ f₀ (p.obj d.point) d.base
  exact siteObjectOverHom B S hS
      (contains_changedBase T iΛ B hS p x₀ hx₀ a) hZ₀ fₗ f₀ g hg ≫ e.hom

@[implicit_reducible] private noncomputable def changedBaseLift
    (hp : p.IsFiberedInGroupoids)
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    ChosenCartesianLift p
      (siteObjectOverChangedBaseToDeformation T iΛ B hS p x₀ hx₀ a)
      ((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst).point rfl :=
  chosenCartesianLift p hp
    (siteObjectOverChangedBaseToDeformation T iΛ B hS p x₀ hx₀ a)
    ((Deformation.Artin.predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst).point rfl

private theorem changedBaseLift_base
    (hp : p.IsFiberedInGroupoids)
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    p.obj
      (changedBaseLift T iΛ B hS p x₀ hx₀ hp a).obj =
      siteObjectOverChangedBase T iΛ B hS p x₀ hx₀ a := by
  let f := siteObjectOverChangedBaseToDeformation T iΛ B hS p x₀ hx₀ a
  let L := changedBaseLift T iΛ B hS p x₀ hx₀ hp a
  have : p.IsHomLift f L.arrow := L.isHomLift
  exact IsHomLift.domain_eq p f L.arrow

private theorem contains_extendedPoint
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (iΛ : Spec (.of T.Λ) ⟶ S)
    {X : Type v} [Category.{w} X] (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (xₗ : X)
    (hxₗ : (p ⋙ Over.post B.inclusion).obj xₗ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ)) :
    B.Contains (Spec (.of T.l)) :=
  contains_domain_of_post_eq B S hS (p.obj xₗ)
    (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ) hxₗ

@[implicit_reducible] private noncomputable def siteObjectOverExtendedPoint
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (iΛ : Spec (.of T.Λ) ⟶ S)
    {X : Type v} [Category.{w} X] (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (xₗ : X)
    (hxₗ : (p ⋙ Over.post B.inclusion).obj xₗ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ)) :
    AlgebraicGeometry.BigFppfOver B S hS :=
  siteObjectOver B S hS (contains_extendedPoint T B S hS iΛ p xₗ hxₗ)
    (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ)

@[implicit_reducible] private noncomputable def siteObjectOverExtendedPointIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (iΛ : Spec (.of T.Λ) ⟶ S)
    {X : Type v} [Category.{w} X] (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (xₗ : X)
    (hxₗ : (p ⋙ Over.post B.inclusion).obj xₗ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ)) :
    siteObjectOverExtendedPoint T B S hS iΛ p xₗ hxₗ ≅ p.obj xₗ :=
  siteObjectOverIso B S hS (contains_extendedPoint T B S hS iΛ p xₗ hxₗ)
    (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ)
    (p.obj xₗ) hxₗ

@[implicit_reducible] private noncomputable def siteObjectOverExtendedPointToChangedBase
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    siteObjectOverExtendedPoint T B S hS iΛ p xₗ hxₗ ⟶
      siteObjectOverChangedBase T iΛ B hS p x₀ hx₀ a := by
  let fₗ := Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ
  let fA := Spec.map (CommRingCat.ofHom (algebraMap T.Λ a.snd)) ≫ iΛ
  let g := Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap a.snd))
  exact siteObjectOverHom B S hS (contains_extendedPoint T B S hS iΛ p xₗ hxₗ)
    (contains_changedBase T iΛ B hS p x₀ hx₀ a) fₗ fA g (residuePoint_base a.snd iΛ)

private theorem extendedPointToChangedBase_base
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    eqToHom (congrArg Over.left hxₗ).symm ≫
      ((Over.post (X := B.obj hS) B.inclusion).map
        ((siteObjectOverExtendedPointIso T B S hS iΛ p xₗ hxₗ).inv ≫
          siteObjectOverExtendedPointToChangedBase T iΛ B hS p x₀ xₗ hx₀ hxₗ a)).left ≫
      eqToHom (congrArg Over.left
        (siteObjectOverChangedBase_post T iΛ B hS p x₀ hx₀ a)) =
      Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap a.snd)) := by
  let P := Over.post (X := B.obj hS) B.inclusion
  let eL := siteObjectOverExtendedPointIso T B S hS iΛ p xₗ hxₗ
  let g₀ := siteObjectOverExtendedPointToChangedBase T iΛ B hS p x₀ xₗ hx₀ hxₗ a
  have hPostL : P.obj (siteObjectOverExtendedPoint T B S hS iΛ p xₗ hxₗ) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ) :=
    siteObjectOver_post B S hS
      (contains_extendedPoint T B S hS iΛ p xₗ hxₗ)
      (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ)
  have hPostA := siteObjectOverChangedBase_post T iΛ B hS p x₀ hx₀ a
  have hEhom : P.map eL.hom = (eqToIso (hPostL.trans hxₗ.symm)).hom := by
    show (Over.post (X := B.obj hS) B.inclusion).map
        (siteObjectOverIso B S hS
          (contains_extendedPoint T B S hS iΛ p xₗ hxₗ)
          (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ)
          (p.obj xₗ) hxₗ).hom = _
    exact siteObjectOverIso_post_hom B S hS
      (contains_extendedPoint T B S hS iΛ p xₗ hxₗ)
      (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ)
      (p.obj xₗ) hxₗ
  have hEiso : P.mapIso eL = eqToIso (hPostL.trans hxₗ.symm) := Iso.ext hEhom
  have hEinv : (P.map eL.inv).left =
      eqToHom (congrArg Over.left hxₗ) ≫
        eqToHom (congrArg Over.left hPostL).symm := by
    rw [← Functor.mapIso_inv, hEiso]
    simp [P]
  have hg₀ : (P.map g₀).left =
      eqToHom (congrArg Over.left hPostL) ≫
        Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap a.snd)) ≫
        eqToHom (congrArg Over.left hPostA).symm := by
    show B.inclusion.map (Over.Hom.left g₀) = _
    dsimp only [g₀, siteObjectOverExtendedPointToChangedBase]
    have hraw := siteObjectOverHom_underlying B S hS
      (contains_extendedPoint T B S hS iΛ p xₗ hxₗ)
      (contains_changedBase T iΛ B hS p x₀ hx₀ a) _ _ _ (residuePoint_base a.snd iΛ)
    convert hraw using 1 <;> cat_disch
  show eqToHom (congrArg Over.left hxₗ).symm ≫
    (P.map eL.inv).left ≫ (P.map g₀).left ≫
    eqToHom (congrArg Over.left hPostA) = _
  rw [hEinv, hg₀]
  simp

end Construction

end Deformation.Artin.Site
