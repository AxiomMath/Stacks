module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.ArtinianLocalRing
public import StacksFrontier.AlgebraicGeometry.Pushout.SchemePushout
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.Deformation.Artin.ChangeOfField.SiteRestriction.EssSurj
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.RimSchlessinger
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.ResidueField.Basic

import all StacksFrontier.Deformation.Artin.ChangeOfField.SiteRestriction.EssSurj
import all StacksFrontier.Deformation.Artin.ChangeOfField.SiteRestriction.Functor
import all StacksFrontier.Deformation.Artin.ChangeOfField.SiteRestriction.Projection

/-!
# The change-of-field functor is an equivalence

This is the fourth of the four parts of
`StacksFrontier.Deformation.Artin.ChangeOfField.SiteRestriction`.
It proves that the canonical functor `(𝓕_{𝒳,k,x₀})_{l/k} ⥤ 𝓕_{𝒳,l,x_{l,0}}` is faithful and full
when `𝒳` satisfies (RS), and concludes `Deformation.Artin.Site.changeOfFieldFunctor_isEquivalence`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace Deformation.Artin.Site

attribute [local implicit_reducible]
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.mk
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
  CategoryTheory.Limits.CategoricalPullback.π₁
  CategoryTheory.Limits.CategoricalPullback.π₂

section Equivalence

variable (T : Deformation.ChangeOfFieldsSituation.{u, u, u})
variable {S : Scheme.{u}} [IsLocallyNoetherian S]
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

attribute [local instance]
  instCategoryCarrierΛKPredeformationCategoryCompBigFppfOverOverSchemePostSchemesInclusion_1
  instCategoryCarrierΛLPredeformationCategoryCompBigFppfOverOverSchemePostSchemesInclusion_1

omit [IsLocallyNoetherian S] in
private theorem satisfiesRS_of_ringPullback
    (hp : p.IsFiberedInGroupoids)
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (hRS : Deformation.Artin.SatisfiesRS B S hS p hp)
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} T.Λ T.l)
    (R : Deformation.ArtinianLocalAlgCat.{u, u, u} T.Λ T.k)
    (r : R →+* A)
    (hR : IsPullback (CommRingCat.ofHom r)
      (CommRingCat.ofHom (Deformation.Artin.residueMap R))
      (CommRingCat.ofHom (Deformation.residueMap T A))
      (CommRingCat.ofHom (algebraMap T.k T.l)))
    {U V W Z : AlgebraicGeometry.BigFppfOver B S hS}
    (hU : (Over.post B.inclusion).obj U =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ))
    (hV : (Over.post B.inclusion).obj V =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (hW : (Over.post B.inclusion).obj W =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ A)) ≫ iΛ))
    (hZ : (Over.post B.inclusion).obj Z =
      Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap T.Λ R)) ≫ iΛ))
    (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z)
    (w : f ≫ i = g ≫ j)
    (hf : schemeMap (Over.post B.inclusion) hU hV f =
      Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))
    (hg : schemeMap (Over.post B.inclusion) hU hW g =
      Spec.map (CommRingCat.ofHom (Deformation.residueMap T A)))
    (hi : schemeMap (Over.post B.inclusion) hV hZ i =
      Spec.map (CommRingCat.ofHom
        (Deformation.Artin.residueMap R)))
    (hj : schemeMap (Over.post B.inclusion) hW hZ j =
      Spec.map (CommRingCat.ofHom r)) :
    letI : p.IsFibered := hp.isFibered
    (Deformation.Artin.fiberSquareComparison p p.chosenPullbacks f g i j w).IsEquivalence := by
  have : p.IsFibered := hp.isFibered
  have hfiniteL := changeFieldPoint_finiteType T iΛ hfinite
  apply hRS g f j i w.symm
  · exact siteObject_isArtinianLocal_of_post_eq B S hS U T.l hU
  · exact siteObject_isArtinianLocal_of_post_eq B S hS W A hW
  · exact siteObject_isArtinianLocal_of_post_eq B S hS V T.k hV
  · exact siteObject_isArtinianLocal_of_post_eq B S hS Z
      R hZ
  · exact siteObject_isFiniteTypeOver_of_post_eq B S hS U hU hfiniteL
  · exact siteObject_isFiniteTypeOver_of_post_eq B S hS W hW
      (finiteType_of_baseArtinian iΛ hfiniteL A)
  · exact siteObject_isFiniteTypeOver_of_post_eq B S hS V hV hfinite
  · exact siteObject_isFiniteTypeOver_of_post_eq B S hS Z hZ
      (finiteType_of_baseArtinian iΛ hfinite R)
  · apply schemeMap_isClosedImmersion B S hS hU hW g
    rw [hg]
    exact IsClosedImmersion.spec_of_surjective _
      (A.residueEquiv.surjective.comp (IsLocalRing.residue_surjective (R := A)))
  · apply schemeMap_isPushout B S hS hU hW hV hZ g f j i
    rw [hf, hg, hi, hj]
    have : Subsingleton ↥(Spec (.of A)) := Ring.KrullDimLE.subsingleton_primeSpectrum A
    exact isPushout_spec_of_isPullback _ _ _ _
      (A.residueEquiv.surjective.comp (IsLocalRing.residue_surjective (R := A))) hR

@[implicit_reducible] private def artinianRingIso
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {A B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k} (e : A ≅ B) :
    CommRingCat.of A ≅ CommRingCat.of B where
  hom := CommRingCat.ofHom e.hom.hom.toRingHom
  inv := CommRingCat.ofHom e.inv.hom.toRingHom
  hom_inv_id := by
    change CommRingCat.ofHom (e.hom ≫ e.inv).hom.toRingHom = _
    rw [e.hom_inv_id]
    rfl
  inv_hom_id := by
    change CommRingCat.ofHom (e.inv ≫ e.hom).hom.toRingHom = _
    rw [e.inv_hom_id]
    rfl

private theorem comparisonRing_isPullback_of_iso
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} T.Λ T.l)
    (R : Deformation.ArtinianLocalAlgCat.{u, u, u} T.Λ T.k)
    (e : R ≅ (Deformation.comparisonFunctor T).functor.obj A) :
    IsPullback (CommRingCat.ofHom ((comparisonProjection T A).comp e.hom.hom.toRingHom))
      (CommRingCat.ofHom (Deformation.Artin.residueMap R))
      (CommRingCat.ofHom (Deformation.residueMap T A))
      (CommRingCat.ofHom (algebraMap T.k T.l)) := by
  apply (comparisonRing_isPullback T A).of_iso (artinianRingIso e).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · show CommRingCat.ofHom (comparisonProjection T A) ≫ 𝟙 _ =
      (artinianRingIso e).inv ≫ (artinianRingIso e).hom ≫
        CommRingCat.ofHom (comparisonProjection T A)
    simp
  · show CommRingCat.ofHom (Deformation.Artin.residueMap _) ≫ 𝟙 _ =
      CommRingCat.ofHom e.inv.hom.toRingHom ≫ CommRingCat.ofHom (Deformation.Artin.residueMap R)
    rw [Category.comp_id, ← CommRingCat.ofHom_comp, artinianResidueMap_natural]
  · simp
  · simp

omit [IsLocallyNoetherian S] in
private theorem deformationRing_isPullback
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    IsPullback (CommRingCat.ofHom (deformationProjection T iΛ B hS p x₀ hx₀ a))
      (CommRingCat.ofHom (Deformation.Artin.residueMap
        (((Deformation.Artin.predeformationCategory iΛ
          (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst).algebra)))
      (CommRingCat.ofHom (Deformation.residueMap T a.snd))
      (CommRingCat.ofHom (algebraMap T.k T.l)) := by
  let C₀ := Deformation.Artin.predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
  let e := (eqToIso (C₀.object_projection a.fst)).symm ≪≫ a.iso
  have h := comparisonRing_isPullback_of_iso T a.snd (C₀.objects a.fst).algebra e
  simpa only [deformationProjection, e, Iso.trans_hom,
    Iso.symm_hom, eqToIso.inv] using h

private theorem isPullback_cast_residueMap
    (A A' : Deformation.ArtinianLocalAlgCat.{u, u, u} T.Λ T.l) (hA : A' = A)
    (R : Deformation.ArtinianLocalAlgCat.{u, u, u} T.Λ T.k) (r : R →+* A)
    (h : IsPullback (CommRingCat.ofHom r) (CommRingCat.ofHom (Deformation.Artin.residueMap R))
      (CommRingCat.ofHom (Deformation.residueMap T A))
      (CommRingCat.ofHom (algebraMap T.k T.l))) :
    IsPullback (CommRingCat.ofHom (hA.symm ▸ r))
      (CommRingCat.ofHom (Deformation.Artin.residueMap R))
      (CommRingCat.ofHom (Deformation.residueMap T A'))
      (CommRingCat.ofHom (algebraMap T.k T.l)) := by
  subst A'
  exact h

omit [IsLocallyNoetherian S] in
private theorem satisfiesRS_restriction_square
    (hp : p.IsFiberedInGroupoids)
    (hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
      ((p ⋙ Over.post B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) =
        Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (hRS : Deformation.Artin.SatisfiesRS B S hS p hp)
    (F : ChangeOfFieldFunctor T iΛ B hS p x₀ xₗ hx₀ hxₗ η)
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    let d := (Deformation.Artin.predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst
    let d' := (Deformation.Artin.predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) xₗ hxₗ).objects
      (F.toFunctor.obj a)
    letI : p.IsFibered := hp.isFibered
    ∀ (w : p.map η ≫ p.map d.arrow = p.map d'.arrow ≫ p.map (F.restriction a)),
      (Deformation.Artin.fiberSquareComparison p p.chosenPullbacks (p.map η) (p.map d'.arrow)
        (p.map d.arrow) (p.map (F.restriction a)) w).IsEquivalence := by
  intro d d'
  have : p.IsFibered := hp.isFibered
  intro w
  apply satisfiesRS_of_ringPullback T iΛ B hS p hp hfinite hRS d'.algebra d.algebra
    ((F.algebra_eq a).symm ▸ deformationProjection T iΛ B hS p x₀ hx₀ a)
    (isPullback_cast_residueMap T a.snd d'.algebra (F.algebra_eq a) d.algebra _
      (deformationRing_isPullback T iΛ B hS p x₀ hx₀ a))
    hxₗ hx₀ d'.base d.base (p.map η) (p.map d'.arrow)
    (p.map d.arrow) (p.map (F.restriction a)) w
    hηbase d'.arrow_base d.arrow_base (F.restriction_base a)

/-- Morphisms of deformations with the same ring map have the same image of the arrow in `𝒞`. -/
private theorem map_arrow_eq_of_ringHom_eq {S : Scheme.{u}}
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hS : B.Contains S)
    {X : Type v} [Category.{w} X] (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {i : Spec (.of Λ) ⟶ S} {x : X}
    {hx : (p ⋙ Over.post B.inclusion).obj x = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ i)}
    {da db : Deformation.Artin.DeformationObject i (p ⋙ Over.post B.inclusion) x hx}
    (m n : Deformation.Artin.DeformationMorphism i (p ⋙ Over.post B.inclusion) x hx da db)
    (h : m.ringHom = n.ringHom) : p.map m.arrow = p.map n.arrow := by
  apply (Over.post B.inclusion).map_injective
  apply (schemeMap_eq_iff _ db.base da.base _ _).mp
  rw [show schemeMap (p ⋙ Over.post B.inclusion) db.base da.base m.arrow = _ from m.arrow_base,
    show schemeMap (p ⋙ Over.post B.inclusion) db.base da.base n.arrow = _ from n.arrow_base, h]

omit [IsLocallyNoetherian S] in
private theorem changeOfFieldFunctor_faithful
    (hp : p.IsFiberedInGroupoids)
    (hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
      ((p ⋙ Over.post B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) =
        Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (hRS : Deformation.Artin.SatisfiesRS B S hS p hp)
    (F : ChangeOfFieldFunctor T iΛ B hS p x₀ xₗ hx₀ hxₗ η) : F.toFunctor.Faithful := by
  let P := Over.post (X := B.obj hS) B.inclusion
  let q := p ⋙ P
  let C₀ := Deformation.Artin.predeformationCategory iΛ q x₀ hx₀
  let Cₗ := Deformation.Artin.predeformationCategory iΛ q xₗ hxₗ
  constructor
  intro a b f g hfg
  have hs : f.snd = g.snd := by
    show (Deformation.changeOfFieldsProjection T C₀.projection).map f =
      (Deformation.changeOfFieldsProjection T C₀.projection).map g
    rw [Functor.map_eq_of_comp_eq _ _ F.toFunctor F.projection_comm f,
      Functor.map_eq_of_comp_eq _ _ F.toFunctor F.projection_comm g, hfg]
  have hf : C₀.projection.map f.fst = C₀.projection.map g.fst := by
    apply (cancel_mono b.iso.hom).mp
    rw [f.w, g.w, hs]
  have hr : (C₀.morphisms a.fst b.fst f.fst).ringHom =
      (C₀.morphisms a.fst b.fst g.fst).ringHom := by
    rw [← C₀.morphism_projection f.fst, ← C₀.morphism_projection g.fst, hf]
  let α := (C₀.morphisms a.fst b.fst f.fst).arrow
  let β := (C₀.morphisms a.fst b.fst g.fst).arrow
  have hbase : p.map α = p.map β := map_arrow_eq_of_ringHom_eq B hS p _ _ hr
  let db := C₀.objects b.fst
  let db' := Cₗ.objects (F.toFunctor.obj b)
  have hw : p.map η ≫ p.map db.arrow = p.map db'.arrow ≫ p.map (F.restriction b) := by
    rw [← p.map_comp, ← p.map_comp, F.arrow_comm]
  have : p.IsFibered := hp.isFibered
  have := satisfiesRS_restriction_square T iΛ B hS p x₀ xₗ hx₀ hxₗ η
    hp hηbase hfinite hRS F b hw
  have : p.IsHomLift (p.map α) β := hbase.symm ▸ IsHomLift.map p β
  have hαβ : α = β := by
    apply fiberSquareComparison_arrow_ext p p.chosenPullbacks
      (p.map η) (p.map db'.arrow) (p.map db.arrow) (p.map (F.restriction b)) hw hp
      (a := Functor.Fiber.mk (p := p) (a := db.point) rfl) (p.map α)
      (Functor.Fiber.mk (p := p) (a := x₀) rfl)
      (Functor.Fiber.mk (p := p) (a := db'.point) rfl) db.arrow (F.restriction b)
    · exact (C₀.morphisms a.fst b.fst f.fst).triangle.trans
        (C₀.morphisms a.fst b.fst g.fst).triangle.symm
    · show F.restriction b ≫ (C₀.morphisms a.fst b.fst f.fst).arrow =
        F.restriction b ≫ (C₀.morphisms a.fst b.fst g.fst).arrow
      rw [← F.restriction_natural f, ← F.restriction_natural g, hfg]
  exact CategoricalPullback.hom_ext
    ((C₀.morphisms a.fst b.fst).injective (deformationMorphism_ext hr hαβ)) hs

omit [IsLocallyNoetherian S] in
private theorem deformationProjection_natural_of_comm
    (a b : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection)
    (u : a.snd ⟶ b.snd)
    (v : ((Deformation.Artin.predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst).algebra ⟶
      ((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).objects b.fst).algebra)
    (h : v ≫ eqToHom ((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).object_projection b.fst).symm ≫ b.iso.hom =
      eqToHom ((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).object_projection a.fst).symm ≫
        a.iso.hom ≫ (Deformation.comparisonFunctor T).functor.map u) :
    (deformationProjection T iΛ B hS p x₀ hx₀ b).comp v.hom.toRingHom =
      u.hom.toRingHom.comp (deformationProjection T iΛ B hS p x₀ hx₀ a) := by
  let C₀ := Deformation.Artin.predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
  calc
    _ = (comparisonProjection T b.snd).comp
        (v ≫ eqToHom (C₀.object_projection b.fst).symm ≫ b.iso.hom).hom.toRingHom := by
      rw [deformationProjection]
      rfl
    _ = (comparisonProjection T b.snd).comp
        (eqToHom (C₀.object_projection a.fst).symm ≫ a.iso.hom ≫
          (Deformation.comparisonFunctor T).functor.map u).hom.toRingHom := by rw [h]
    _ = ((comparisonProjection T b.snd).comp
        ((Deformation.comparisonFunctor T).functor.map u).hom.toRingHom).comp
        (eqToHom (C₀.object_projection a.fst).symm ≫ a.iso.hom).hom.toRingHom := rfl
    _ = _ := by
      rw [comparisonProjection_natural, deformationProjection]
      rfl

omit [IsLocallyNoetherian S] in
private theorem exists_lifted_algebra_hom
    (a b : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection)
    (u : a.snd ⟶ b.snd) :
    ∃ v : ((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst).algebra ⟶
      ((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).objects b.fst).algebra,
      (deformationProjection T iΛ B hS p x₀ hx₀ b).comp v.hom.toRingHom =
        u.hom.toRingHom.comp (deformationProjection T iΛ B hS p x₀ hx₀ a) ∧
      eqToHom ((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).object_projection a.fst) ≫ v ≫
        eqToHom ((Deformation.Artin.predeformationCategory iΛ
          (p ⋙ Over.post B.inclusion) x₀ hx₀).object_projection b.fst).symm ≫ b.iso.hom =
            a.iso.hom ≫ (Deformation.comparisonFunctor T).functor.map u := by
  let C₀ := Deformation.Artin.predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
  let v := eqToHom (C₀.object_projection a.fst).symm ≫ a.iso.hom ≫
    (Deformation.comparisonFunctor T).functor.map u ≫ b.iso.inv ≫
      eqToHom (C₀.object_projection b.fst)
  refine ⟨v, deformationProjection_natural_of_comm T iΛ B hS p x₀ hx₀ a b u v ?_, ?_⟩
  · simp [v, Category.assoc]
  · simp [v, Category.assoc]

private theorem ringHom_natural_cast
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {A A' B B' : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    (hA : A' = A) (hB : B' = B) (u : A' ⟶ B')
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* A) (g : S →+* B) (v : R →+* S)
    (h : g.comp v =
      (eqToHom hA.symm ≫ u ≫ eqToHom hB).hom.toRingHom.comp f) :
    (hB.symm ▸ g).comp v = u.hom.toRingHom.comp (hA.symm ▸ f) := by
  subst A' B'
  simpa using h

omit [IsLocallyNoetherian S] in
private theorem changeOfFieldFunctor_hom_ext
    (hp : p.IsFiberedInGroupoids)
    (F : ChangeOfFieldFunctor T iΛ B hS p x₀ xₗ hx₀ hxₗ η)
    {a b : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection}
    {f g : F.toFunctor.obj a ⟶ F.toFunctor.obj b}
    (hb : (Deformation.Artin.predeformationCategory iΛ
          (p ⋙ Over.post B.inclusion) xₗ hxₗ).projection.map f =
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) xₗ hxₗ).projection.map g)
    (hr : ((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) xₗ hxₗ).morphisms _ _ f).arrow ≫ F.restriction a =
      ((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) xₗ hxₗ).morphisms _ _ g).arrow ≫ F.restriction a) : f = g := by
  let P := Over.post (X := B.obj hS) B.inclusion
  let q := p ⋙ P
  let Cₗ := Deformation.Artin.predeformationCategory iΛ q xₗ hxₗ
  apply (Cₗ.morphisms _ _).injective
  have hring : (Cₗ.morphisms _ _ f).ringHom = (Cₗ.morphisms _ _ g).ringHom := by
    rw [← Cₗ.morphism_projection f, ← Cₗ.morphism_projection g, hb]
  apply deformationMorphism_ext hring
  apply cartesian_cancel p hp (F.restriction a) _ hr
  exact map_arrow_eq_of_ringHom_eq B hS p _ _ hring

omit [IsLocallyNoetherian S] in
private theorem exists_schemeMap_eq_spec_map
    {da db : Deformation.Artin.DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀}
    (v : da.algebra ⟶ db.algebra) :
    ∃ h : p.obj db.point ⟶ p.obj da.point,
      schemeMap (Over.post B.inclusion) db.base da.base h =
        Spec.map (CommRingCat.ofHom v.hom.toRingHom) := by
  have hvbase : Spec.map (CommRingCat.ofHom v.hom.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap T.Λ da.algebra)) ≫ iΛ) =
      Spec.map (CommRingCat.ofHom (algebraMap T.Λ db.algebra)) ≫ iΛ := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext t
    exact v.hom.commutes t
  exact ⟨siteMapOfSchemes B S hS db.base da.base _ hvbase,
    siteMapOfSchemes_base B S hS db.base da.base _ _⟩

omit [IsLocallyNoetherian S] in
private theorem map_arrow_eq_comp_of_schemeMap
    {da db : Deformation.Artin.DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀}
    {v : da.algebra ⟶ db.algebra} {h : p.obj db.point ⟶ p.obj da.point}
    (hh : schemeMap (Over.post B.inclusion) db.base da.base h =
      Spec.map (CommRingCat.ofHom v.hom.toRingHom)) :
    p.map da.arrow = p.map db.arrow ≫ h := by
  let P := Over.post (X := B.obj hS) B.inclusion
  let q := p ⋙ P
  apply P.map_injective
  apply (schemeMap_eq_iff P hx₀ da.base _ _).mp
  rw [schemeMap_comp P hx₀ db.base, hh]
  show schemeMap q hx₀ da.base da.arrow =
    schemeMap q hx₀ db.base db.arrow ≫ _
  rw [show schemeMap q hx₀ da.base da.arrow = _ from da.arrow_base,
    show schemeMap q hx₀ db.base db.arrow = _ from db.arrow_base,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, artinianResidueMap_natural]

omit [IsLocallyNoetherian S] in
private theorem map_restriction_comp_eq_of_schemeMap
    (F : ChangeOfFieldFunctor T iΛ B hS p x₀ xₗ hx₀ hxₗ η)
    {a b : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection}
    (t : F.toFunctor.obj a ⟶ F.toFunctor.obj b)
    {v : ((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst).algebra ⟶
      ((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).objects b.fst).algebra}
    (hv : (deformationProjection T iΛ B hS p x₀ hx₀ b).comp v.hom.toRingHom =
      (eqToHom (F.algebra_eq a).symm ≫ ((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) xₗ hxₗ).morphisms _ _ t).ringHom ≫
          eqToHom (F.algebra_eq b)).hom.toRingHom.comp
        (deformationProjection T iΛ B hS p x₀ hx₀ a))
    {h : p.obj ((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).objects b.fst).point ⟶
      p.obj ((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst).point}
    (hh : schemeMap (Over.post B.inclusion)
      ((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).objects b.fst).base
      ((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst).base h =
      Spec.map (CommRingCat.ofHom v.hom.toRingHom)) :
    p.map (((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) xₗ hxₗ).morphisms _ _ t).arrow ≫ F.restriction a) =
      p.map (F.restriction b) ≫ h := by
  let P := Over.post (X := B.obj hS) B.inclusion
  let q := p ⋙ P
  let C₀ := Deformation.Artin.predeformationCategory iΛ q x₀ hx₀
  let Cₗ := Deformation.Artin.predeformationCategory iΛ q xₗ hxₗ
  let da := C₀.objects a.fst
  let db := C₀.objects b.fst
  let da' := Cₗ.objects (F.toFunctor.obj a)
  let db' := Cₗ.objects (F.toFunctor.obj b)
  let m := Cₗ.morphisms _ _ t
  apply P.map_injective
  apply (schemeMap_eq_iff P db'.base da.base _ _).mp
  rw [schemeMap_comp P db'.base db.base, hh]
  show schemeMap q db'.base da.base (m.arrow ≫ F.restriction a) =
    schemeMap q db'.base db.base (F.restriction b) ≫ _
  rw [schemeMap_comp q db'.base da'.base,
    show schemeMap q db'.base da'.base m.arrow = _ from m.arrow_base,
    show schemeMap q da'.base da.base (F.restriction a) = _ from F.restriction_base a,
    show schemeMap q db'.base db.base (F.restriction b) = _ from F.restriction_base b,
    ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  exact (ringHom_natural_cast (F.algebra_eq a) (F.algebra_eq b) m.ringHom
    _ _ v.hom.toRingHom hv).symm

omit [IsLocallyNoetherian S] in
private theorem projection_map_changeOfFieldFunctor_of_snd
    (F : ChangeOfFieldFunctor T iΛ B hS p x₀ xₗ hx₀ hxₗ η)
    {a b : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀).projection}
    (t : F.toFunctor.obj a ⟶ F.toFunctor.obj b) (φ : a ⟶ b)
    (hφ : φ.snd = eqToHom (F.algebra_eq a).symm ≫ ((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) xₗ hxₗ).morphisms _ _ t).ringHom ≫
          eqToHom (F.algebra_eq b)) :
    (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) xₗ hxₗ).projection.map (F.toFunctor.map φ) =
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) xₗ hxₗ).projection.map t := by
  let Cₗ := Deformation.Artin.predeformationCategory iΛ (p ⋙ Over.post B.inclusion) xₗ hxₗ
  let hA := (Cₗ.object_projection (F.toFunctor.obj a)).trans (F.algebra_eq a)
  let hB := (Cₗ.object_projection (F.toFunctor.obj b)).trans (F.algebra_eq b)
  have he : φ.snd = eqToHom hA.symm ≫ Cₗ.projection.map (F.toFunctor.map φ) ≫
      eqToHom hB := Functor.map_eq_of_comp_eq _ _ F.toFunctor F.projection_comm φ
  calc
    Cₗ.projection.map (F.toFunctor.map φ) =
        eqToHom hA ≫ φ.snd ≫ eqToHom hB.symm := by
      simpa [Category.assoc] using congrArg
        (fun s => eqToHom hA ≫ s ≫ eqToHom hB.symm) he.symm
    _ = Cₗ.projection.map t := by
      rw [hφ, ← Cₗ.morphism_projection t]
      simp [eqToHom_trans, Category.assoc]

omit [IsLocallyNoetherian S] in
private theorem changeOfFieldFunctor_full
    (hp : p.IsFiberedInGroupoids)
    (hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
      ((p ⋙ Over.post B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) =
        Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (hRS : Deformation.Artin.SatisfiesRS B S hS p hp)
    (F : ChangeOfFieldFunctor T iΛ B hS p x₀ xₗ hx₀ hxₗ η) : F.toFunctor.Full := by
  let P := Over.post (X := B.obj hS) B.inclusion
  let q := p ⋙ P
  let C₀ := Deformation.Artin.predeformationCategory iΛ q x₀ hx₀
  let Cₗ := Deformation.Artin.predeformationCategory iΛ q xₗ hxₗ
  refine ⟨fun {a b} t => ?_⟩
  let da := C₀.objects a.fst
  let db := C₀.objects b.fst
  let db' := Cₗ.objects (F.toFunctor.obj b)
  let m := Cₗ.morphisms _ _ t
  let u := eqToHom (F.algebra_eq a).symm ≫ m.ringHom ≫ eqToHom (F.algebra_eq b)
  obtain ⟨v, hv, hvcomm⟩ := exists_lifted_algebra_hom T iΛ B hS p x₀ hx₀ a b u
  obtain ⟨h, hh⟩ := exists_schemeMap_eq_spec_map T iΛ B hS p x₀ hx₀ v
  have hw : p.map η ≫ p.map db.arrow = p.map db'.arrow ≫ p.map (F.restriction b) := by
    rw [← p.map_comp, ← p.map_comp, F.arrow_comm]
  have : p.IsFibered := hp.isFibered
  have := satisfiesRS_restriction_square T iΛ B hS p x₀ xₗ hx₀ hxₗ η
    hp hηbase hfinite hRS F b hw
  have : p.IsHomLift (p.map db.arrow ≫ h) da.arrow :=
    map_arrow_eq_comp_of_schemeMap T iΛ B hS p x₀ hx₀ hh ▸ IsHomLift.map p da.arrow
  have : p.IsHomLift (p.map (F.restriction b) ≫ h) (m.arrow ≫ F.restriction a) :=
    map_restriction_comp_eq_of_schemeMap T iΛ B hS p x₀ xₗ hx₀ hxₗ η F t hv hh ▸
      IsHomLift.map p (m.arrow ≫ F.restriction a)
  obtain ⟨γ, hγ, hγr, hγs⟩ := fiberSquareComparison_pointed_arrow_exists p p.chosenPullbacks
    (p.map η) (p.map db'.arrow) (p.map db.arrow) (p.map (F.restriction b)) hw hp
    (a := Functor.Fiber.mk (p := p) (a := db.point) rfl) h
    (Functor.Fiber.mk (p := p) (a := xₗ) rfl)
    (Functor.Fiber.mk (p := p) (a := x₀) rfl)
    (Functor.Fiber.mk (p := p) (a := db'.point) rfl)
    η db'.arrow db.arrow (F.restriction b) da.arrow (m.arrow ≫ F.restriction a)
    (F.arrow_comm b).symm (by rw [← Category.assoc, m.triangle, F.arrow_comm])
  have hγmap : p.map γ = h := by simpa using IsHomLift.fac' p h γ
  have hγbase : schemeMap q db.base da.base γ =
      Spec.map (CommRingCat.ofHom v.hom.toRingHom) := by
    show schemeMap P db.base da.base (p.map γ) = _
    rw [hγmap]
    exact hh
  let n : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ da db := ⟨v, γ, hγr, hγbase⟩
  let f := (C₀.morphisms a.fst b.fst).symm n
  have hf : C₀.morphisms a.fst b.fst f = n := Equiv.apply_symm_apply _ n
  have hfmap : C₀.projection.map f = eqToHom (C₀.object_projection a.fst) ≫
      v ≫ eqToHom (C₀.object_projection b.fst).symm := by
    have he := C₀.morphism_projection f
    rw [hf] at he
    simpa [Category.assoc] using congrArg
      (fun s => eqToHom (C₀.object_projection a.fst) ≫ s ≫
        eqToHom (C₀.object_projection b.fst).symm) he
  let φ : a ⟶ b := ⟨f, u, by rwa [hfmap]⟩
  refine ⟨φ, changeOfFieldFunctor_hom_ext T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp F ?_ ?_⟩
  · exact projection_map_changeOfFieldFunctor_of_snd T iΛ B hS p x₀ xₗ hx₀ hxₗ η F t φ rfl
  · rw [F.restriction_natural]
    show F.restriction b ≫ (C₀.morphisms a.fst b.fst f).arrow =
      m.arrow ≫ F.restriction a
    rw [hf]
    exact hγs

omit [IsLocallyNoetherian S] in
/-- Under (RS), restriction of deformations is an equivalence over the Artinian local algebras
with residue field `l`. -/
@[stacks 07WX "the canonical functor is an equivalence under (RS), for a category \
  fibred in groupoids over the big fppf site"]
public theorem changeOfFieldFunctor_isEquivalence
    (hp : p.IsFiberedInGroupoids)
    (hη : p.IsCartesian (p.map η) η)
    (hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
      ((p ⋙ Over.post B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) =
        Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ) ∧
      QuasiCompact
        (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ))
    (hRS : Deformation.Artin.SatisfiesRS B S hS p hp) :
    (changeOfFieldFunctor T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hη hηbase).toFunctor.IsEquivalence := by
  let F := changeOfFieldFunctor T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hη hηbase
  exact ⟨changeOfFieldFunctor_faithful T iΛ B hS p x₀ xₗ hx₀ hxₗ η
      hp hηbase hfinite hRS F,
    changeOfFieldFunctor_full T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase hfinite hRS F,
    changeOfFieldFunctor_essSurj T iΛ B hS p x₀ xₗ hx₀ hxₗ η
      hp hηbase hfinite hRS F⟩

end Equivalence

end Deformation.Artin.Site
