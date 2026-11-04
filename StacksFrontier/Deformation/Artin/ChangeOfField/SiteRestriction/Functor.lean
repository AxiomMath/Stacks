module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.ArtinianLocalRing
public import StacksFrontier.AlgebraicGeometry.Pushout.SchemePushout
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.Deformation.Artin.ChangeOfField.SiteRestriction.Projection
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.RimSchlessinger
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.ResidueField.Basic

import all StacksFrontier.Deformation.Artin.ChangeOfField.SiteRestriction.Projection

/-!
# The change-of-field restriction functor

This is the second of the four parts of
`StacksFrontier.Deformation.Artin.ChangeOfField.SiteRestriction`.
For an object of `(𝓕_{𝒳,k,x₀})_{l/k}` over `A`, it builds the deformation of `x_{l,0}` over `A`
obtained by restricting along `Spec A ⟶ Spec (A ×_l k)`, assembles these restrictions into a functor
over `𝒞_{Λ,l}`, and defines `Deformation.Artin.Site.ChangeOfFieldFunctor` and
`Deformation.Artin.Site.changeOfFieldFunctor`.
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

attribute [local instance]
  instCategoryCarrierΛKPredeformationCategoryCompBigFppfOverOverSchemePostSchemesInclusion
  instCategoryCarrierΛLPredeformationCategoryCompBigFppfOverOverSchemePostSchemesInclusion

private theorem changedBaseToDeformation_base
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    eqToHom (congrArg Over.left
        (siteObjectOverChangedBase_post T iΛ B hS p x₀ hx₀ a)).symm ≫
      ((Over.post (X := B.obj hS) B.inclusion).map
        (siteObjectOverChangedBaseToDeformation T iΛ B hS p x₀ hx₀ a)).left ≫
      eqToHom (congrArg Over.left
        ((Deformation.Artin.predeformationCategory iΛ
          (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst).base) =
      Spec.map (CommRingCat.ofHom (deformationProjection T iΛ B hS p x₀ hx₀ a)) := by
  let P := Over.post (X := B.obj hS) B.inclusion
  let d := (Deformation.Artin.predeformationCategory iΛ
    (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst
  let fA := siteObjectOverChangedBaseToDeformation T iΛ B hS p x₀ hx₀ a
  have hPostA := siteObjectOverChangedBase_post T iΛ B hS p x₀ hx₀ a
  have hPostA_left : congrArg Over.left hPostA = rfl := Subsingleton.elim _ _
  let hZ₀ := contains_domain_of_post_eq B S hS (p.obj d.point)
    (Spec.map (CommRingCat.ofHom (algebraMap T.Λ d.algebra)) ≫ iΛ) d.base
  let W₀ := siteObjectOver B S hS hZ₀
    (Spec.map (CommRingCat.ofHom (algebraMap T.Λ d.algebra)) ≫ iΛ)
  have hPost₀ : P.obj W₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ d.algebra)) ≫ iΛ) :=
    siteObjectOver_post B S hS hZ₀ _
  have hPost₀_left : congrArg Over.left hPost₀ = rfl := Subsingleton.elim _ _
  let fₗ := Spec.map (CommRingCat.ofHom (algebraMap T.Λ a.snd)) ≫ iΛ
  let f₀ := Spec.map (CommRingCat.ofHom (algebraMap T.Λ d.algebra)) ≫ iΛ
  let g := Spec.map (CommRingCat.ofHom (deformationProjection T iΛ B hS p x₀ hx₀ a))
  have hg : g ≫ f₀ = fₗ := by
    dsimp [g, f₀, fₗ]
    exact congrArg (fun q => q ≫ iΛ)
      (deformationProjection_base T iΛ B hS p x₀ hx₀ a)
  let e := siteObjectOverIso B S hS hZ₀ f₀ (p.obj d.point) d.base
  let q := siteObjectOverHom B S hS
    (contains_changedBase T iΛ B hS p x₀ hx₀ a) hZ₀ fₗ f₀ g hg
  have hq : B.inclusion.map (Over.Hom.left q) = g :=
    siteObjectOverHom_underlying B S hS
      (contains_changedBase T iΛ B hS p x₀ hx₀ a) hZ₀ fₗ f₀ g hg
  have he' : (P.map e.hom).left =
      eqToHom (congrArg Over.left hPost₀) ≫
        eqToHom (congrArg Over.left d.base).symm := by
    have heleft := congrArg Over.Hom.left
      (siteObjectOverIso_post_hom B S hS hZ₀ f₀ (p.obj d.point) d.base)
    convert heleft using 1
    cat_disch
  have hfA : (P.map fA).left =
      eqToHom (congrArg Over.left hPostA) ≫
        Spec.map (CommRingCat.ofHom (deformationProjection T iΛ B hS p x₀ hx₀ a)) ≫
        eqToHom (congrArg Over.left d.base).symm := by
    show (P.map (q ≫ e.hom)).left = _
    rw [Functor.map_comp, Over.comp_left]
    have hqP : (P.map q).left = g := hq
    rw [hqP, he', hPostA_left, hPost₀_left]
    cat_disch
  show eqToHom (congrArg Over.left hPostA).symm ≫ (P.map fA).left ≫
    eqToHom (congrArg Over.left d.base) = _
  rw [hfA]
  simp

private theorem changedBaseRestriction_baseFactor
    (_hp : p.IsFiberedInGroupoids)
    (hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
      ((p ⋙ Over.post B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) =
        Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    p.map (η ≫ ((Deformation.Artin.predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst).arrow) =
    (siteObjectOverExtendedPointIso T B S hS iΛ p xₗ hxₗ).inv ≫
      siteObjectOverExtendedPointToChangedBase T iΛ B hS p x₀ xₗ hx₀ hxₗ a ≫
      siteObjectOverChangedBaseToDeformation T iΛ B hS p x₀ hx₀ a := by
  let C₀ := Deformation.Artin.predeformationCategory iΛ
    (p ⋙ Over.post B.inclusion) x₀ hx₀
  let d := C₀.objects a.fst
  rw [Functor.map_comp]
  apply Functor.map_injective (Over.post B.inclusion)
  rw [Functor.map_comp]
  apply CostructuredArrow.hom_ext
  show ((p ⋙ Over.post B.inclusion).map η).left ≫
      ((p ⋙ Over.post B.inclusion).map d.arrow).left =
    ((Over.post B.inclusion).map
      ((siteObjectOverExtendedPointIso T B S hS iΛ p xₗ hxₗ).inv ≫
        siteObjectOverExtendedPointToChangedBase T iΛ B hS p x₀ xₗ hx₀ hxₗ a ≫
        siteObjectOverChangedBaseToDeformation T iΛ B hS p x₀ hx₀ a)).left
  rw [Functor.map_comp, Functor.map_comp]
  let α := eqToHom (congrArg Over.left hxₗ).symm
  let β := eqToHom (congrArg Over.left d.base)
  have hleft : α ≫
        ((p ⋙ Over.post B.inclusion).map η).left ≫
        ((p ⋙ Over.post B.inclusion).map d.arrow).left ≫ β =
      Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)) ≫
        Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap d.algebra)) := by
    calc
      _ = (α ≫ ((p ⋙ Over.post B.inclusion).map η).left ≫
          eqToHom (congrArg Over.left hx₀)) ≫
          (eqToHom (congrArg Over.left hx₀).symm ≫
            ((p ⋙ Over.post B.inclusion).map d.arrow).left ≫ β) := by simp
      _ = _ := by rw [hηbase, d.arrow_base]
  have hright : α ≫
        ((Over.post B.inclusion).map
          ((siteObjectOverExtendedPointIso T B S hS iΛ p xₗ hxₗ).inv ≫
            siteObjectOverExtendedPointToChangedBase T iΛ B hS p x₀ xₗ hx₀ hxₗ a ≫
            siteObjectOverChangedBaseToDeformation T iΛ B hS p x₀ hx₀ a)).left ≫ β =
      Spec.map (CommRingCat.ofHom (Deformation.residueMap T a.snd)) ≫
        Spec.map (CommRingCat.ofHom (deformationProjection T iΛ B hS p x₀ hx₀ a)) := by
    calc
      _ = (α ≫ ((Over.post (X := B.obj hS) B.inclusion).map
            ((siteObjectOverExtendedPointIso T B S hS iΛ p xₗ hxₗ).inv ≫
              siteObjectOverExtendedPointToChangedBase T iΛ B hS p x₀ xₗ hx₀ hxₗ a)).left ≫
            eqToHom (congrArg Over.left
              (siteObjectOverChangedBase_post T iΛ B hS p x₀ hx₀ a))) ≫
          (eqToHom (congrArg Over.left
              (siteObjectOverChangedBase_post T iΛ B hS p x₀ hx₀ a)).symm ≫
            ((Over.post (X := B.obj hS) B.inclusion).map
              (siteObjectOverChangedBaseToDeformation T iΛ B hS p x₀ hx₀ a)).left ≫ β) := by
        simp
      _ = _ := congrArg₂ (· ≫ ·)
        (extendedPointToChangedBase_base T iΛ B hS p x₀ xₗ hx₀ hxₗ a)
        (changedBaseToDeformation_base T iΛ B hS p x₀ hx₀ a)
  have hright' := hright.trans (deformationProjection_residuePoint T iΛ B hS p x₀ hx₀ a)
  have hboth := hleft.trans hright'.symm
  exact (cancel_mono β).1 ((cancel_epi α).1 hboth)

private structure ChangedBaseFactorData
    (hp : p.IsFiberedInGroupoids)
    (hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
      ((p ⋙ Over.post B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) =
        Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) where
  arrow : xₗ ⟶ (changedBaseLift T iΛ B hS p x₀ hx₀ hp a).obj
  isHomLift : p.IsHomLift
    ((siteObjectOverExtendedPointIso T B S hS iΛ p xₗ hxₗ).inv ≫
      siteObjectOverExtendedPointToChangedBase T iΛ B hS p x₀ xₗ hx₀ hxₗ a) arrow
  arrow_comp : arrow ≫ (changedBaseLift T iΛ B hS p x₀ hx₀ hp a).arrow =
    η ≫ ((Deformation.Artin.predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst).arrow

@[implicit_reducible] private noncomputable def changedBaseFactorData
    (hp : p.IsFiberedInGroupoids)
    (hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
      ((p ⋙ Over.post B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) =
        Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    ChangedBaseFactorData T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase a := by
  classical
  let C₀ := Deformation.Artin.predeformationCategory iΛ
    (p ⋙ Over.post B.inclusion) x₀ hx₀
  let d := C₀.objects a.fst
  let L := changedBaseLift T iΛ B hS p x₀ hx₀ hp a
  let fA := siteObjectOverChangedBaseToDeformation T iΛ B hS p x₀ hx₀ a
  let eL := siteObjectOverExtendedPointIso T B S hS iΛ p xₗ hxₗ
  let g₀ := siteObjectOverExtendedPointToChangedBase T iΛ B hS p x₀ xₗ hx₀ hxₗ a
  let g := eL.inv ≫ g₀
  let ψ := η ≫ d.arrow
  have hfactor : p.map ψ = g ≫ fA :=
    changedBaseRestriction_baseFactor T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase a
  letI : p.IsHomLift fA L.arrow := L.isHomLift
  letI : p.IsStronglyCartesian fA L.arrow := hp.isStronglyCartesian_homLift fA L.arrow
  have hfactor' : p.map ψ = g ≫ fA ≫ eqToHom (rfl : p.obj d.point = p.obj d.point).symm := by
    simpa using hfactor
  let factors := cartesian_factor_of_strongly_cartesian
    p fA L.arrow g ψ rfl hfactor'
  let χ := Classical.choose factors.exists
  have hχ := Classical.choose_spec factors.exists
  exact ⟨χ, hχ.1, hχ.2⟩

@[implicit_reducible] private noncomputable def changedBaseDeformationObject
    (hp : p.IsFiberedInGroupoids)
    (hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
      ((p ⋙ Over.post B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) =
        Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    Deformation.Artin.DeformationObject iΛ
      (p ⋙ Over.post B.inclusion) xₗ hxₗ := by
  let C₀ := Deformation.Artin.predeformationCategory iΛ
    (p ⋙ Over.post B.inclusion) x₀ hx₀
  let d := C₀.objects a.fst
  let L := changedBaseLift T iΛ B hS p x₀ hx₀ hp a
  let fd := changedBaseFactorData T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase a
  let hDom := changedBaseLift_base T iΛ B hS p x₀ hx₀ hp a
  let A := siteObjectOverChangedBase T iΛ B hS p x₀ hx₀ a
  let fA := Spec.map (CommRingCat.ofHom (algebraMap T.Λ a.snd)) ≫ iΛ
  let hPostA := siteObjectOverChangedBase_post T iΛ B hS p x₀ hx₀ a
  let postLift := congrArg (Over.post (X := B.obj hS) B.inclusion).obj hDom
  let hBase := postLift.trans hPostA
  refine {
    algebra := a.snd
    point := L.obj
    arrow := fd.arrow
    base := hBase
    arrow_base := ?_ }
  let P := Over.post (X := B.obj hS) B.inclusion
  let eL := siteObjectOverExtendedPointIso T B S hS iΛ p xₗ hxₗ
  let g₀ := siteObjectOverExtendedPointToChangedBase T iΛ B hS p x₀ xₗ hx₀ hxₗ a
  let g := eL.inv ≫ g₀
  have hMap : p.map fd.arrow = g ≫ eqToHom hDom.symm := by
    have : p.IsHomLift g fd.arrow := fd.isHomLift
    have h := IsHomLift.fac' p g fd.arrow
    simpa [fd, g, eL, g₀, hDom] using h
  have hMapQ : ((p ⋙ P).map fd.arrow).left =
      (P.map g).left ≫
        eqToHom (congrArg Over.left (congrArg P.obj hDom).symm) := by
    rw [Functor.comp_map, hMap, Functor.map_comp, Over.comp_left]
    rw [eqToHom_map P hDom.symm]
    simp
  have hTransport :
      eqToHom (congrArg Over.left (congrArg P.obj hDom).symm) ≫
      eqToHom (congrArg Over.left hBase) =
      eqToHom (congrArg Over.left hPostA) := by
    simp [eqToHom_trans, P]
  change eqToHom (congrArg Over.left hxₗ).symm ≫
    ((p ⋙ Over.post B.inclusion).map fd.arrow).left ≫
      eqToHom (congrArg Over.left hBase) =
    Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap a.snd))
  calc
    _ = eqToHom (congrArg Over.left hxₗ).symm ≫ (P.map g).left ≫
        eqToHom (congrArg Over.left hPostA) := by
      rw [hMapQ, Category.assoc, hTransport, ← Category.assoc]
    _ = Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap a.snd)) :=
      extendedPointToChangedBase_base T iΛ B hS p x₀ xₗ hx₀ hxₗ a

@[implicit_reducible] private noncomputable def changedBaseOutputObject
    (hp : p.IsFiberedInGroupoids)
    (hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
      ((p ⋙ Over.post B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) =
        Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    (Deformation.Artin.predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) xₗ hxₗ).carrier :=
  (Deformation.Artin.predeformationCategory iΛ
    (p ⋙ Over.post B.inclusion) xₗ hxₗ).objects.symm
      (changedBaseDeformationObject T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase a)

private theorem changedBaseOutputObject_spec
    (hp : p.IsFiberedInGroupoids)
    (hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
      ((p ⋙ Over.post B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) =
        Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    (Deformation.Artin.predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) xₗ hxₗ).objects
        (changedBaseOutputObject T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase a) =
      changedBaseDeformationObject T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase a := by
  simp [changedBaseOutputObject]

private theorem changedBaseOutputObject_algebra
    (hp : p.IsFiberedInGroupoids)
    (hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
      ((p ⋙ Over.post B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) =
        Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    ((Deformation.Artin.predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) xₗ hxₗ).objects
        (changedBaseOutputObject T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase a)).algebra = a.snd := by
  rw [changedBaseOutputObject_spec]
  rfl

private theorem changedBaseOutputObject_point
    (hp : p.IsFiberedInGroupoids)
    (hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
      ((p ⋙ Over.post B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) =
        Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    ((Deformation.Artin.predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) xₗ hxₗ).objects
        (changedBaseOutputObject T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase a)).point =
      (changedBaseLift T iΛ B hS p x₀ hx₀ hp a).obj :=
  congrArg Deformation.Artin.DeformationObject.point
    (changedBaseOutputObject_spec T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase a)

@[implicit_reducible] private noncomputable def changedBaseOutputRestriction
    (hp : p.IsFiberedInGroupoids)
    (hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
      ((p ⋙ Over.post B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) =
        Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    ((Deformation.Artin.predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) xₗ hxₗ).objects
        (changedBaseOutputObject T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase a)).point ⟶
      ((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst).point :=
  eqToHom (changedBaseOutputObject_point T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase a) ≫
    (changedBaseLift T iΛ B hS p x₀ hx₀ hp a).arrow

private theorem changedBaseRestriction_base
    (hp : p.IsFiberedInGroupoids)
    (hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
      ((p ⋙ Over.post B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) =
        Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))
    (a : Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection) :
    schemeMap (p ⋙ Over.post B.inclusion)
      (changedBaseDeformationObject T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase a).base
      ((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst).base
      (changedBaseLift T iΛ B hS p x₀ hx₀ hp a).arrow =
    Spec.map (CommRingCat.ofHom (deformationProjection T iΛ B hS p x₀ hx₀ a)) := by
  let L := changedBaseLift T iΛ B hS p x₀ hx₀ hp a
  let := L.isHomLift
  have h := IsHomLift.fac' p
    (siteObjectOverChangedBaseToDeformation T iΛ B hS p x₀ hx₀ a) L.arrow
  show eqToHom _ ≫ ((Over.post B.inclusion).map (p.map L.arrow)).left ≫ eqToHom _ = _
  rw [h]
  simp only [Functor.map_comp, Over.comp_left, eqToHom_map, Over.eqToHom_left]
  dsimp only [siteObjectOverChangedBaseToDeformation]
  simp only [Functor.map_comp, Over.comp_left]
  rw [siteObjectOverIso_post_hom]
  simp only [eqToIso.hom, Over.eqToHom_left]
  rw [show ((Over.post B.inclusion).map
    (siteObjectOverHom B S hS _ _ _ _ _ _)).left = _ from
      siteObjectOverHom_underlying B S hS _ _ _ _ _ _]
  simp [Category.assoc, eqToHom_trans]

private theorem deformationMorphism_ext
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {X : Type v} [Category.{w} X] {q : X ⥤ Over S} {x₀ : X}
    {hx₀ : q.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {a b : Deformation.Artin.DeformationObject iΛ q x₀ hx₀}
    {f g : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ a b}
    (h₁ : f.ringHom = g.ringHom) (h₂ : f.arrow = g.arrow) : f = g := by
  cases f
  cases g
  cases h₁
  cases h₂
  rfl

private theorem deformationMorphism_transport_exists
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {X : Type v} [Category.{w} X] {q : X ⥤ Over S} {x₀ : X}
    {hx₀ : q.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (C : Deformation.Artin.PredeformationConstruction iΛ q x₀ hx₀)
    {d e : Deformation.Artin.DeformationObject iΛ q x₀ hx₀}
    {a b : C.carrier} (ha : C.objects a = d) (hb : C.objects b = e)
    (m : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ d e)
    {z : X} (r : d.point ⟶ z) (s : e.point ⟶ z) (hm : m.arrow ≫ r = s) :
    letI := C.category
    ∃ f : a ⟶ b,
      eqToHom ((C.object_projection a).trans (congrArg (fun d => d.algebra) ha)).symm ≫
        C.projection.map f ≫
        eqToHom ((C.object_projection b).trans (congrArg (fun d => d.algebra) hb)) = m.ringHom ∧
      (C.morphisms a b f).arrow ≫ eqToHom (congrArg (fun d => d.point) ha) ≫ r =
        eqToHom (congrArg (fun d => d.point) hb) ≫ s := by
  let := C.category
  subst d e
  refine ⟨(C.morphisms a b).symm m, ?_, ?_⟩
  · simpa using C.morphism_projection ((C.morphisms a b).symm m)
  · simpa using hm

private theorem deformation_arrow_transport
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {X : Type v} [Category.{w} X] {q : X ⥤ Over S} {x₀ : X}
    {hx₀ : q.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {d e : Deformation.Artin.DeformationObject iΛ q x₀ hx₀} (h : d = e) :
    d.arrow ≫ eqToHom (congrArg Deformation.Artin.DeformationObject.point h) = e.arrow := by
  subst e
  simp

private theorem deformation_restriction_transport
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {X : Type v} [Category.{w} X] {q : X ⥤ Over S} {x₀ : X}
    {hx₀ : q.obj x₀ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {d e : Deformation.Artin.DeformationObject iΛ q x₀ hx₀} (h : d = e)
    {z : X} {A : Type u} [CommRing A] {fA : Spec (.of A) ⟶ S}
    (hz : q.obj z = Over.mk fA) (r : e.point ⟶ z) (f : A →+* e.algebra)
    (hr : schemeMap q e.base hz r = Spec.map (CommRingCat.ofHom f)) :
    schemeMap q d.base hz (eqToHom (congrArg Deformation.Artin.DeformationObject.point h) ≫ r) =
      Spec.map (CommRingCat.ofHom
        ((congrArg Deformation.Artin.DeformationObject.algebra h).symm ▸ f)) := by
  subst e
  simpa [schemeMap] using hr

section RestrictionFunctor

variable (hp : p.IsFiberedInGroupoids)
variable (hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
  ((p ⋙ Over.post B.inclusion).map η).left ≫
  eqToHom (congrArg Over.left hx₀) =
    Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))

local notation "P" => Over.post (X := B.obj hS) B.inclusion
local notation "q" => p ⋙ P
local notation "C₀" => Deformation.Artin.predeformationCategory iΛ q x₀ hx₀
local notation "Cₗ" => Deformation.Artin.predeformationCategory iΛ q xₗ hxₗ
local notation "D" => changedBaseDeformationObject T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase
local notation "R" a:max =>
  ChosenCartesianLift.arrow (changedBaseLift T iΛ B hS p x₀ hx₀ hp a)
local notation "A" => Deformation.ChangeOfFieldsCategory T
  (Deformation.Artin.PredeformationConstruction.projection C₀)

private theorem changedBase_morphism_exists {a b : A} (f : a ⟶ b) :
    ∃ m : Deformation.Artin.DeformationMorphism iΛ q xₗ hxₗ (D a) (D b),
      m.ringHom = f.snd ∧ m.arrow ≫ R a = R b ≫ ((C₀).morphisms a.fst b.fst f.fst).arrow := by
  let da := D a
  let db := D b
  let m := (C₀).morphisms a.fst b.fst f.fst
  have hf : Spec.map (CommRingCat.ofHom f.snd.hom.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap T.Λ a.snd)) ≫ iΛ) =
      Spec.map (CommRingCat.ofHom (algebraMap T.Λ b.snd)) ≫ iΛ := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext t
    exact f.snd.hom.commutes t
  let g := siteMapOfSchemes B S hS db.base da.base
    (Spec.map (CommRingCat.ofHom f.snd.hom.toRingHom)) hf
  have hg : schemeMap P db.base da.base g =
      Spec.map (CommRingCat.ofHom f.snd.hom.toRingHom) :=
    siteMapOfSchemes_base B S hS db.base da.base _ hf
  have hfactor : p.map (R b ≫ m.arrow) = g ≫ p.map (R a) := by
    apply (P).map_injective
    apply (schemeMap_eq_iff P db.base ((C₀).objects a.fst).base _ _).mp
    show schemeMap q db.base ((C₀).objects a.fst).base (R b ≫ m.arrow) = _
    rw [schemeMap_comp q db.base ((C₀).objects b.fst).base,
      schemeMap_comp P db.base da.base]
    show schemeMap q db.base ((C₀).objects b.fst).base (R b) ≫
      schemeMap q ((C₀).objects b.fst).base ((C₀).objects a.fst).base m.arrow =
      schemeMap P db.base da.base g ≫ schemeMap q da.base ((C₀).objects a.fst).base (R a)
    rw [changedBaseRestriction_base, changedBaseRestriction_base, hg]
    rw [show schemeMap q ((C₀).objects b.fst).base ((C₀).objects a.fst).base m.arrow =
      Spec.map (CommRingCat.ofHom m.ringHom.hom.toRingHom) from m.arrow_base]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, deformationProjection_natural]
  have : p.IsFibered := hp.isFibered
  have : p.IsCartesian (p.map (R a)) (R a) :=
    (hp.isStronglyCartesian_homLift _ _).isCartesian_of_isStronglyCartesian
  obtain ⟨χ, ⟨hχ, hχr⟩, _⟩ := cartesian_factor_of_fibered p (R a) g (R b ≫ m.arrow) hfactor
  let := hχ
  have hχmap : p.map χ = g := by simpa using IsHomLift.fac' p g χ
  have hχbase : schemeMap q db.base da.base χ =
      Spec.map (CommRingCat.ofHom f.snd.hom.toRingHom) := by
    show schemeMap P db.base da.base (p.map χ) = _
    rw [hχmap]
    exact hg
  have htri : db.arrow ≫ χ = da.arrow := by
    apply cartesian_cancel p hp (R a)
    · apply (P).map_injective
      apply (schemeMap_eq_iff q hxₗ da.base _ _).mp
      rw [schemeMap_comp q hxₗ db.base]
      rw [show schemeMap q hxₗ db.base db.arrow = _ from db.arrow_base,
        show schemeMap q hxₗ da.base da.arrow = _ from da.arrow_base, hχbase]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, artinianResidueMap_natural]
    · calc
        (db.arrow ≫ χ) ≫ R a = db.arrow ≫ (R b ≫ m.arrow) := by rw [Category.assoc, hχr]
        _ = (η ≫ ((C₀).objects b.fst).arrow) ≫ m.arrow := by
          rw [← Category.assoc]
          exact congrArg (fun t => t ≫ m.arrow)
            (changedBaseFactorData T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase b).arrow_comp
        _ = η ≫ ((C₀).objects a.fst).arrow := by rw [Category.assoc, m.triangle]
        _ = da.arrow ≫ R a :=
          (changedBaseFactorData T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase a).arrow_comp.symm
  exact ⟨⟨f.snd, χ, htri, hχbase⟩, rfl, hχr⟩

local notation "O" => changedBaseOutputObject T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase
local notation "r" => changedBaseOutputRestriction T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase

private theorem outputRestriction_eq (a : A) :
    r a = eqToHom (congrArg Deformation.Artin.DeformationObject.point
      (changedBaseOutputObject_spec T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase a)) ≫ R a := by
  rfl

private theorem outputProjection_eq (a : A) : (Cₗ).projection.obj (O a) = a.snd :=
  ((Cₗ).object_projection (O a)).trans
    (changedBaseOutputObject_algebra T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase a)

private theorem outputMorphism_exists {a b : A} (f : a ⟶ b) :
    ∃ g : O a ⟶ O b,
      eqToHom (outputProjection_eq T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase a).symm ≫
        (Cₗ).projection.map g ≫
        eqToHom (outputProjection_eq T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase b) = f.snd ∧
      ((Cₗ).morphisms (O a) (O b) g).arrow ≫ r a =
        r b ≫ ((C₀).morphisms a.fst b.fst f.fst).arrow := by
  obtain ⟨m, hm, hn⟩ := changedBase_morphism_exists T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase f
  obtain ⟨g, hg, hr⟩ := deformationMorphism_transport_exists (Cₗ)
    (changedBaseOutputObject_spec T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase a)
    (changedBaseOutputObject_spec T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase b)
    m (R a) (R b ≫ ((C₀).morphisms a.fst b.fst f.fst).arrow) hn
  refine ⟨g, hg.trans hm, ?_⟩
  simpa only [outputRestriction_eq, Category.assoc] using hr

@[implicit_reducible] private noncomputable def outputMap {a b : A} (f : a ⟶ b) : O a ⟶ O b :=
  (outputMorphism_exists T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase f).choose

private theorem outputMap_projection {a b : A} (f : a ⟶ b) :
    eqToHom (outputProjection_eq T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase a).symm ≫
      (Cₗ).projection.map (outputMap T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase f) ≫
      eqToHom (outputProjection_eq T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase b) = f.snd :=
  (outputMorphism_exists T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase f).choose_spec.1

/-- The image of `outputMap f` under the projection, with the `eqToHom` casts made explicit. -/
private theorem outputMap_projection_map {a b : A} (f : a ⟶ b) :
    (Cₗ).projection.map (outputMap T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase f) =
      eqToHom (outputProjection_eq T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase a) ≫ f.snd ≫
        eqToHom (outputProjection_eq T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase b).symm := by
  rw [← outputMap_projection T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase f]
  simp

private theorem outputMap_natural {a b : A} (f : a ⟶ b) :
    ((Cₗ).morphisms (O a) (O b)
      (outputMap T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase f)).arrow ≫ r a =
      r b ≫ ((C₀).morphisms a.fst b.fst f.fst).arrow :=
  (outputMorphism_exists T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase f).choose_spec.2

private theorem outputHom_ext {a b : A} {f g : O a ⟶ O b}
    (hb : (Cₗ).projection.map f = (Cₗ).projection.map g)
    (hr : ((Cₗ).morphisms (O a) (O b) f).arrow ≫ r a =
      ((Cₗ).morphisms (O a) (O b) g).arrow ≫ r a) : f = g := by
  apply ((Cₗ).morphisms (O a) (O b)).injective
  have hring : ((Cₗ).morphisms (O a) (O b) f).ringHom =
      ((Cₗ).morphisms (O a) (O b) g).ringHom := by
    rw [← (Cₗ).morphism_projection f, ← (Cₗ).morphism_projection g, hb]
  apply deformationMorphism_ext hring
  apply cartesian_cancel p hp (r a) _ hr
  apply (P).map_injective
  apply (schemeMap_eq_iff q ((Cₗ).objects (O b)).base ((Cₗ).objects (O a)).base _ _).mp
  show eqToHom _ ≫ _ ≫ eqToHom _ = eqToHom _ ≫ _ ≫ eqToHom _
  rw [((Cₗ).morphisms (O a) (O b) f).arrow_base,
    ((Cₗ).morphisms (O a) (O b) g).arrow_base, hring]

@[implicit_reducible] private noncomputable def restrictionFunctor : A ⥤ (Cₗ).carrier where
  obj := O
  map f := outputMap T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase f
  map_id a := by
    apply outputHom_ext T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase
    · rw [outputMap_projection_map]
      simp
    · rw [outputMap_natural, (Cₗ).reversed_identity]
      change r a ≫ ((C₀).morphisms a.fst a.fst (𝟙 a.fst)).arrow = 𝟙 _ ≫ r a
      rw [(C₀).reversed_identity]
      simp
  map_comp {a b c} f g := by
    apply outputHom_ext T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase
    · rw [outputMap_projection_map, Functor.map_comp, outputMap_projection_map,
        outputMap_projection_map]
      simp
    · rw [outputMap_natural, (Cₗ).reversed_composition]
      rw [Category.assoc, outputMap_natural, ← Category.assoc, outputMap_natural]
      rw [Category.assoc]
      exact congrArg (fun t => r c ≫ t) ((C₀).reversed_composition f.fst g.fst)

end RestrictionFunctor

/-- The canonical restriction functor, specified on deformations by cartesian
arrows and on morphisms by the resulting naturality equation. -/
public structure ChangeOfFieldFunctor where
  /-- The functor from the change-of-fields category over the deformations of `x₀` to the
  deformations of `xₗ`. -/
  toFunctor :
    Deformation.ChangeOfFieldsCategory T
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).projection ⥤
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) xₗ hxₗ).carrier
  projection_comm : toFunctor ⋙
      (Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) xₗ hxₗ).projection =
      Deformation.changeOfFieldsProjection T
        (Deformation.Artin.predeformationCategory iΛ
          (p ⋙ Over.post B.inclusion) x₀ hx₀).projection
  algebra_eq (a) :
    ((Deformation.Artin.predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) xₗ hxₗ).objects (toFunctor.obj a)).algebra = a.snd
  /-- The arrow from the point of the image deformation of `a` to the point of the deformation
  `a.fst`. -/
  restriction (a) :
    ((Deformation.Artin.predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) xₗ hxₗ).objects (toFunctor.obj a)).point ⟶
    ((Deformation.Artin.predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst).point
  restriction_base (a) :
    eqToHom (congrArg Over.left
      ((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) xₗ hxₗ).objects (toFunctor.obj a)).base).symm ≫
      ((p ⋙ Over.post B.inclusion).map (restriction a)).left ≫
      eqToHom (congrArg Over.left
        ((Deformation.Artin.predeformationCategory iΛ
          (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst).base) =
      Spec.map (CommRingCat.ofHom
        ((algebra_eq a).symm ▸ deformationProjection T iΛ B hS p x₀ hx₀ a))
  restriction_cartesian (a) : p.IsCartesian (p.map (restriction a)) (restriction a)
  arrow_comm (a) :
    ((Deformation.Artin.predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) xₗ hxₗ).objects (toFunctor.obj a)).arrow ≫
      restriction a = η ≫
      ((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).objects a.fst).arrow
  restriction_natural {a b} (f : a ⟶ b) :
    ((Deformation.Artin.predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) xₗ hxₗ).morphisms
        (toFunctor.obj a) (toFunctor.obj b) (toFunctor.map f)).arrow ≫
      restriction a = restriction b ≫
      ((Deformation.Artin.predeformationCategory iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀).morphisms a.fst b.fst f.fst).arrow

/-- The canonical functor `(𝓕_{𝒳,k,x₀})_{l/k} ⥤ 𝓕_{𝒳,l,x_{l,0}}` over `𝒞_{Λ,l}`, restricting
deformations along `Spec A ⟶ Spec (A ×_l k)`. -/
@[stacks 07WX "the canonical functor, for a category fibred in groupoids over the \
  big fppf site"]
public noncomputable def changeOfFieldFunctor
    (hp : p.IsFiberedInGroupoids)
    (_hη : p.IsCartesian (p.map η) η)
    (hηbase : eqToHom (congrArg Over.left hxₗ).symm ≫
      ((p ⋙ Over.post B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) =
        Spec.map (CommRingCat.ofHom (algebraMap T.k T.l))) :
    ChangeOfFieldFunctor T iΛ B hS p x₀ xₗ hx₀ hxₗ η := private_decl% (by
  refine {
    toFunctor := restrictionFunctor T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase
    projection_comm := ?_
    algebra_eq := changedBaseOutputObject_algebra T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase
    restriction := changedBaseOutputRestriction T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase
    restriction_base := ?_
    restriction_cartesian := ?_
    arrow_comm := ?_
    restriction_natural := outputMap_natural T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase }
  · refine CategoryTheory.Functor.ext (outputProjection_eq T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase) ?_
    intro a b f
    have h := outputMap_projection T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase f
    simpa [restrictionFunctor, Deformation.changeOfFieldsProjection, Category.assoc] using
      congrArg (fun m => eqToHom (outputProjection_eq T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase a) ≫
        m ≫ eqToHom (outputProjection_eq T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase b).symm) h
  · intro a
    rw [outputRestriction_eq]
    exact deformation_restriction_transport
      (changedBaseOutputObject_spec T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase a)
      _ _ _ (changedBaseRestriction_base T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase a)
  · intro a
    let := hp.isStronglyCartesian_homLift
      (p.map (changedBaseOutputRestriction T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase a))
      (changedBaseOutputRestriction T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase a)
    infer_instance
  · intro a
    dsimp only [restrictionFunctor]
    rw [outputRestriction_eq, ← Category.assoc, deformation_arrow_transport
      (changedBaseOutputObject_spec T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase a)]
    exact (changedBaseFactorData T iΛ B hS p x₀ xₗ hx₀ hxₗ η hp hηbase a).arrow_comp)

end Construction

end Deformation.Artin.Site
