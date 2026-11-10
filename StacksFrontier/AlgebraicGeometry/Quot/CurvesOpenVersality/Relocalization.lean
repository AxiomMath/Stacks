module

public import StacksFrontier.AlgebraicGeometry.Descent.Germ.OfSchemeHom
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.FiberDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SmoothnessOverNoetherianBase
public import StacksFrontier.AlgebraicGeometry.Quot.CartesianFamilies
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesOverSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.Artin.Versality.Openness
import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
import StacksFrontier.AlgebraicGeometry.Spaces.Points
import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart
import StacksFrontier.AlgebraicGeometry.Spaces.StronglyCartesian
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import all StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SmoothnessOverNoetherianBase
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenVersality.OverIntegers
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenVersality.ProperFlatFamilies
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenVersality.OverIntegers

/-!
# Relocalization of algebraic spaces along a morphism of bases

Étale-chart properties over a larger base, field-valued points over a larger and a smaller
base and the equivalences and homeomorphisms of point spaces they induce, and the behaviour of
étaleness, quasi-compactness, closedness, separatedness and universal closedness under
relocalization to a smaller base.
-/

@[expose] public section

attribute [local implicit_reducible] AlgebraicGeometry.curvesProjectionOver

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Deformation.Artin

universe u

namespace CurvesVersality

/-- Pullbacks, binary products and products of presheaves on the big fppf category over an
object, given directly: instance search for them times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_Relocalization
    (B : BigFppfSite.{u}) (T : B.Schemes) :
    HasPullbacks ((Over T)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_Relocalization
    (B : BigFppfSite.{u}) (T : B.Schemes)
    {X Y Z : (Over T)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_Relocalization B T).has_limit _

local instance (priority := high) hasProducts_presheaf_Relocalization
    (B : BigFppfSite.{u}) (T : B.Schemes) :
    HasProducts.{0} ((Over T)ᵒᵖ ⥤ Type u) :=
  fun _ => Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasProducts_presheaf_u_Relocalization
    (B : BigFppfSite.{u}) (T : B.Schemes) :
    HasProducts.{u} ((Over T)ᵒᵖ ⥤ Type u) :=
  fun _ => Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasBinaryProducts_presheaf_Relocalization
    (B : BigFppfSite.{u}) (T : B.Schemes) :
    HasBinaryProducts ((Over T)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasLimit_pair_presheaf_Relocalization
    (B : BigFppfSite.{u}) (T : B.Schemes)
    (X Y : (Over T)ᵒᵖ ⥤ Type u) : HasLimit (pair X Y) :=
  (hasBinaryProducts_presheaf_Relocalization B T).has_limit _

attribute [local instance] schemeCutoff_isClosedUnderIsomorphisms
attribute [local instance] schemeCutoff_isClosedUnderPullbacks
attribute [local instance] AlgebraicGeometry.BigFppfSite.hasPullbacks_schemes

private theorem holdsOnEveryEtaleChart_of_largerBase
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS') (P : MorphismProperty Scheme.{u})
    [MorphismProperty.IsLocalAtTarget (@Etale.{u}) Scheme.fppfPrecoverage]
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : Space.HoldsOnEveryEtaleChart B S' hS' P
      ((smallerBaseEquivalenceData
        B S S' hS hS' g).1.functor.map f).hom.left) :
    Space.HoldsOnEveryEtaleChart B S hS P f.hom := by
  intro U V a b h ha hb hw
  let e := (smallerBaseEquivalenceData B S S' hS hS' g).1
  let a₀ : schemeSpace_ U ⟶ X := ObjectProperty.homMk a
  let b₀ : schemeSpace_ V ⟶ Y := ObjectProperty.homMk b
  let ua := (schemeSpaceOverLargerBaseIso B S S' hS hS' g U).hom.hom.left
  let vb := (schemeSpaceOverLargerBaseIso B S S' hS hS' g V).hom.hom.left
  let a' := ua ≫ (e.functor.map a₀).hom.left
  let b' := vb ≫ (e.functor.map b₀).hom.left
  let Q := (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S' hS')).presheaf
  have key (W : AlgebraicGeometry.BigFppfOver B S hS) (Z : AlgebraicSpaces B S hS)
      (c : yoneda.obj W ⟶ Z.obj)
      (hc : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf c) :
      Q ((schemeSpaceOverLargerBaseIso B S S' hS hS' g W).hom.hom.left ≫
        (e.functor.map (ObjectProperty.homMk c : schemeSpace_ W ⟶ Z)).hom.left) := by
    let : IsIso (schemeSpaceOverLargerBaseIso B S S' hS hS' g W).hom.hom.left := by
      change IsIso ((ObjectProperty.ι _ ⋙ Over.forget _).map
        (schemeSpaceOverLargerBaseIso B S S' hS hS' g W).hom)
      infer_instance
    exact MorphismProperty.RespectsIso.precomp (P := Q) _ _
      ((AlgebraicGeometry.presheaf_property_map_base_iff B S S' hS hS' g
        (@Etale.{u}) W Z c).mpr hc)
  have ha' : Q a' := key U X a ha
  have hb' : Q b' := key V Y b hb
  have hcomm : schemeSpaceMap_ h ≫ b₀ = a₀ ≫ f := by
    apply ObjectProperty.hom_ext
    exact hw
  have hcomm' := congrArg (fun k => (e.functor.map k).hom.left) hcomm
  change (e.functor.map (schemeSpaceMap_ h ≫ b₀)).hom.left =
    (e.functor.map (a₀ ≫ f)).hom.left at hcomm'
  simp only [Functor.map_comp] at hcomm'
  change (e.functor.map (schemeSpaceMap_ h)).hom.left ≫
      (e.functor.map b₀).hom.left =
    (e.functor.map a₀).hom.left ≫ (e.functor.map f).hom.left at hcomm'
  have hw' : yoneda.map ((Over.map g).map h) ≫ b' =
      a' ≫ (e.functor.map f).hom.left := by
    dsimp [a', b']
    rw [← Category.assoc, schemeSpaceOverLargerBaseIso_naturality]
    simpa only [Category.assoc] using congrArg (fun k => ua ≫ k) hcomm'
  exact hf ((Over.map g).obj U) ((Over.map g).obj V) a' b'
    ((Over.map g).map h) ha' hb' hw'

private noncomputable def fieldPointOverLargerBase
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (p : Space.FieldValuedPoint B S hS F) :
    Space.FieldValuedPoint B S' hS'
      ((OverShriek.relocalizePresheafFunctor g).obj F) where
  carrier := p.carrier
  contained := p.contained
  toBase := p.toBase ≫ g.hom
  value := ⟨⟨⟨p.toBase⟩, p.value⟩, rfl⟩

private noncomputable def fieldPointOverSmallerBase
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (p : Space.FieldValuedPoint B S' hS'
      ((OverShriek.relocalizePresheafFunctor g).obj F)) :
    Space.FieldValuedPoint B S hS F where
  carrier := p.carrier
  contained := p.contained
  toBase := p.value.1.1.hom
  value := p.value.1.2

private theorem fieldPointOverLargerBase_dominates
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {p q : Space.FieldValuedPoint B S hS F}
    (h : Space.FieldValuedPoint.Dominates B S hS F p q) :
    Space.FieldValuedPoint.Dominates B S' hS'
      ((OverShriek.relocalizePresheafFunctor g).obj F)
      (fieldPointOverLargerBase B S S' hS hS' g F p)
      (fieldPointOverLargerBase B S S' hS hS' g F q) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨(Over.map g).map f, ?_⟩
  apply Subtype.ext
  change (⟨f.left ≫ ⟨q.toBase⟩, _⟩ : Σ a, F.obj (Opposite.op (Over.mk a))) =
    ⟨⟨p.toBase⟩, p.value⟩
  rw [← hf]
  exact OverShriek.sigmaMk_eq F q.value _ f rfl

private theorem fieldPointOverSmallerBase_dominates
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {p q : Space.FieldValuedPoint B S' hS'
      ((OverShriek.relocalizePresheafFunctor g).obj F)}
    (h : Space.FieldValuedPoint.Dominates B S' hS'
      ((OverShriek.relocalizePresheafFunctor g).obj F) p q) :
    Space.FieldValuedPoint.Dominates B S hS F
      (fieldPointOverSmallerBase B S S' hS hS' g F p)
      (fieldPointOverSmallerBase B S S' hS hS' g F q) := by
  obtain ⟨f, hf⟩ := h
  have hw : f.left ≫ q.value.1.1 = p.value.1.1 :=
    congrArg (fun z => z.1.1) hf
  let f' : (fieldPointOverSmallerBase B S S' hS hS' g F p).siteObject ⟶
      (fieldPointOverSmallerBase B S S' hS hS' g F q).siteObject :=
    Over.homMk f.left hw
  refine ⟨f', ?_⟩
  have hh := congrArg Subtype.val hf
  have hh' := OverShriek.sigmaMk_eq F q.value.1.2
    (Over.homMk f.left rfl : Over.mk (f.left ≫ q.value.1.1) ⟶
      Over.mk q.value.1.1) f' rfl
  exact eq_of_heq ((Sigma.mk.inj_iff.mp (hh'.symm.trans hh)).2)

private noncomputable def pointsOverLargerBaseEquiv
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    (F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    AlgebraicGeometry.Space.points B S hS F ≃ AlgebraicGeometry.Space.points B S' hS'
      ((OverShriek.relocalizePresheafFunctor g).obj F) where
  toFun := Quot.map (fieldPointOverLargerBase B S S' hS hS' g F) (by
    rintro p q ⟨r, hp, hq⟩
    exact ⟨fieldPointOverLargerBase B S S' hS hS' g F r,
      fieldPointOverLargerBase_dominates B S S' hS hS' g F hp,
      fieldPointOverLargerBase_dominates B S S' hS hS' g F hq⟩)
  invFun := Quot.map (fieldPointOverSmallerBase B S S' hS hS' g F) (by
    rintro p q ⟨r, hp, hq⟩
    exact ⟨fieldPointOverSmallerBase B S S' hS hS' g F r,
      fieldPointOverSmallerBase_dominates B S S' hS hS' g F hp,
      fieldPointOverSmallerBase_dominates B S S' hS hS' g F hq⟩)
  left_inv := by
    intro p
    induction p using Quot.inductionOn with | h p => rfl
  right_inv := by
    intro p
    induction p using Quot.inductionOn with
    | h p =>
      apply congrArg (Quot.mk _)
      rcases p with @⟨k, hk, hc, t, ⟨⟨a, v⟩, ha⟩⟩
      rcases a with ⟨a⟩
      change Spec (.of k) ⟶ S at a
      have ht : a ≫ g.hom = t := congrArg (fun f => f.hom) ha
      subst t
      rfl

private theorem pointsOverLargerBaseEquiv_naturality
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (x : AlgebraicGeometry.Space.points B S hS F) :
    pointsOverLargerBaseEquiv B S S' hS hS' g G (Space.pointsMap B S hS F f x) =
      Space.pointsMap B S' hS' _ ((OverShriek.relocalizePresheafFunctor g).map f)
        (pointsOverLargerBaseEquiv B S S' hS hS' g F x) := by
  induction x using Quot.inductionOn with | h x => rfl

private noncomputable def pointsIsoEquiv
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G) :
    AlgebraicGeometry.Space.points B S hS F ≃ AlgebraicGeometry.Space.points B S hS G where
  toFun := Space.pointsMap B S hS F e.hom
  invFun := Space.pointsMap B S hS G e.inv
  left_inv x := by rw [← Space.pointsMap_comp_apply, e.hom_inv_id, Space.pointsMap_id_apply]
  right_inv x := by rw [← Space.pointsMap_comp_apply, e.inv_hom_id, Space.pointsMap_id_apply]

private theorem presheaf_property_relocalize_iff
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS') (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (F : AlgebraicSpaces B S hS) (f : yoneda.obj U ⟶ F.obj) :
    (P.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme B S' hS')).presheaf
      ((relocalizedYonedaIso g U).hom ≫
        (OverShriek.relocalizePresheafFunctor g).map f) ↔
      (P.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f := by
  let d := smallerBaseEquivalenceData B S S' hS hS' g
  let a : schemeSpace_ U ⟶ F := ObjectProperty.homMk f
  let Q := (P.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme B S' hS')).presheaf
  let e := relocalizedYonedaIso g U ≪≫ (d.2.app (schemeSpace_ U)).symm
  have hw : e.hom ≫ (d.1.functor.map a).hom.left =
      ((relocalizedYonedaIso g U).hom ≫
        (OverShriek.relocalizePresheafFunctor g).map f) ≫ (d.2.app F).inv := by
    dsimp [e]
    simpa only [Category.assoc, Functor.comp_map, ObjectProperty.ι_map, Over.forget_map,
      ObjectProperty.homMk_hom, a] using
      congrArg (fun k => (relocalizedYonedaIso g U).hom ≫ k)
        (d.2.inv.naturality a).symm
  exact (Q.arrow_mk_iso_iff (Arrow.isoMk e (d.2.app F).symm hw)).trans
    (AlgebraicGeometry.presheaf_property_map_base_iff B S S' hS hS' g P U F f)

attribute [local instance] MorphismProperty.IsMultiplicative.toContainsIdentities
  MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  MorphismProperty.IsStableUnderBaseChange.respectsIso
  MorphismProperty.relative_isMultiplicative

private theorem isEtale_from_scheme_iff
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : yoneda.obj U ⟶ F) :
    AlgebraicGeometry.Space.IsEtale B S hS f ↔
      (MorphismProperty.inverseImage (@Etale.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f := by
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let Q := MorphismProperty.inverseImage (@Etale.{u}) T
  let : Q.IsMultiplicative := {
    id_mem := fun U => by change Etale (T.map (𝟙 U)); rw [T.map_id]; infer_instance
    comp_mem := fun a b ha hb => by
      change Etale (T.map (a ≫ b))
      rw [T.map_comp]
      let : Etale (T.map a) := ha
      let : Etale (T.map b) := hb
      infer_instance }
  let : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    @MorphismProperty.IsStableUnderBaseChange.respectsIso _ _ _ (inferInstance)
  let : Q.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  let P := Q.presheaf
  let : P.IsMultiplicative := MorphismProperty.relative_isMultiplicative _
  constructor
  · intro hf
    simpa only [Category.id_comp] using hf U (𝟙 _) (P.id_mem _)
  · intro hf V a ha
    exact P.comp_mem a f ha hf

private theorem isQuasiCompact_relocalize_iff
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    [MorphismProperty.IsLocalAtTarget (@Etale.{u}) Scheme.fppfPrecoverage]
    [MorphismProperty.IsLocalAtTarget (@Surjective.{u}) Scheme.fppfPrecoverage]
    (F : AlgebraicSpaces B S hS) :
    AlgebraicGeometry.Space.IsQuasiCompactSpace B S' hS'
        ((OverShriek.relocalizePresheafFunctor g).obj F.obj) ↔
      AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS F.obj := by
  constructor
  · rintro ⟨U, a, hU, ha, hae⟩
    let T := relocalizedChartBase g a
    let f := relocalizedChartMap g a
    let e := relocalizedChartIso g a
    have hfac : (relocalizedYonedaIso g T).hom ≫
        (OverShriek.relocalizePresheafFunctor g).map f = yoneda.map e.hom ≫ a := by
      have hh := congrArg (fun k => yoneda.map e.hom ≫ k)
        (relocalizedChartMap_fac g a)
      dsimp only [e] at hh
      rw [← Category.assoc, ← Category.assoc, ← yoneda.map_comp,
        Iso.hom_inv_id, yoneda.map_id, Category.id_comp] at hh
      exact hh
    refine ⟨T, f, hU, ?_, ?_⟩
    · apply (presheaf_property_relocalize_iff B S S' hS hS' g (@Surjective.{u}) T F f).mp
      rw [hfac]
      exact MorphismProperty.RespectsIso.precomp _ (yoneda.map e.hom) a ha
    · apply (isEtale_from_scheme_iff B S hS T f).mpr
      apply (presheaf_property_relocalize_iff B S S' hS hS' g (@Etale.{u}) T F f).mp
      rw [hfac]
      exact MorphismProperty.RespectsIso.precomp _ (yoneda.map e.hom) a
        ((isEtale_from_scheme_iff B S' hS' U a).mp hae)
  · rintro ⟨U, a, hU, ha, hae⟩
    let f := (relocalizedYonedaIso g U).hom ≫
      (OverShriek.relocalizePresheafFunctor g).map a
    refine ⟨(Over.map g).obj U, f, hU, ?_, ?_⟩
    · exact (presheaf_property_relocalize_iff B S S' hS hS' g (@Surjective.{u}) U F a).mpr ha
    · exact (isEtale_from_scheme_iff B S' hS' ((Over.map g).obj U) f).mpr
        ((presheaf_property_relocalize_iff B S S' hS hS' g (@Etale.{u}) U F a).mpr
          ((isEtale_from_scheme_iff B S hS U a).mp hae))

private noncomputable def pointsSchemeBaseEquiv
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS') (T : AlgebraicGeometry.BigFppfOver B S hS) :
    AlgebraicGeometry.Space.points B S hS (yoneda.obj T) ≃
      AlgebraicGeometry.Space.points B S' hS' (yoneda.obj ((Over.map g).obj T)) :=
  (pointsOverLargerBaseEquiv B S S' hS hS' g (yoneda.obj T)).trans
    (pointsIsoEquiv B S' hS' (relocalizedYonedaIso g T).symm)

private noncomputable def fieldPointSchemeOverLargerBase
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS') (T : AlgebraicGeometry.BigFppfOver B S hS)
    (p : Space.FieldValuedPoint B S hS (yoneda.obj T)) :
    Space.FieldValuedPoint B S' hS' (yoneda.obj ((Over.map g).obj T)) where
  carrier := p.carrier
  contained := p.contained
  toBase := p.toBase ≫ g.hom
  value := (Over.map g).map p.value

private noncomputable def fieldPointSchemeOverSmallerBase
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS') (T : AlgebraicGeometry.BigFppfOver B S hS)
    (p : Space.FieldValuedPoint B S' hS' (yoneda.obj ((Over.map g).obj T))) :
    Space.FieldValuedPoint B S hS (yoneda.obj T) where
  carrier := p.carrier
  contained := p.contained
  toBase := p.value.left.hom ≫ T.hom.hom
  value := Over.homMk p.value.left rfl

private theorem pointsSchemeBaseEquiv_class
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS') (T : AlgebraicGeometry.BigFppfOver B S hS)
    (p : Space.FieldValuedPoint B S hS (yoneda.obj T)) :
    pointsSchemeBaseEquiv B S S' hS hS' g T p.class =
      (fieldPointSchemeOverLargerBase B S S' hS hS' g T p).class := rfl

private theorem pointsSchemeBaseEquiv_symm_class
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS') (T : AlgebraicGeometry.BigFppfOver B S hS)
    (p : Space.FieldValuedPoint B S' hS' (yoneda.obj ((Over.map g).obj T))) :
    (pointsSchemeBaseEquiv B S S' hS hS' g T).symm p.class =
      (fieldPointSchemeOverSmallerBase B S S' hS hS' g T p).class := rfl

private noncomputable def pointsSchemeBaseHomeomorph
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS') (T : AlgebraicGeometry.BigFppfOver B S hS) :
    letI := spacePointTopology B S hS (yoneda.obj T)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T)
    letI := spacePointTopology B S' hS' (yoneda.obj ((Over.map g).obj T))
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S' hS' ((Over.map g).obj T))
    AlgebraicGeometry.Space.points B S hS (yoneda.obj T) ≃ₜ
      AlgebraicGeometry.Space.points B S' hS' (yoneda.obj ((Over.map g).obj T)) := by
  letI := spacePointTopology B S hS (yoneda.obj T)
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T)
  letI := spacePointTopology B S' hS' (yoneda.obj ((Over.map g).obj T))
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S' hS' ((Over.map g).obj T))
  refine ⟨pointsSchemeBaseEquiv B S S' hS hS' g T, ?_, ?_⟩
  · apply continuous_def.mpr
    intro W hW
    obtain ⟨V, hV, hp⟩ := (Space.pointTopologyFamily B S' hS').scheme
      ((Over.map g).obj T) W |>.mp hW
    apply ((Space.pointTopologyFamily B S hS).scheme T _).mpr
    refine ⟨V, hV, ?_⟩
    intro p
    change pointsSchemeBaseEquiv B S S' hS hS' g T p.class ∈ W ↔ _
    rw [pointsSchemeBaseEquiv_class]
    exact hp (fieldPointSchemeOverLargerBase B S S' hS hS' g T p)
  · apply continuous_def.mpr
    intro W hW
    obtain ⟨V, hV, hp⟩ := (Space.pointTopologyFamily B S hS).scheme T W |>.mp hW
    apply ((Space.pointTopologyFamily B S' hS').scheme ((Over.map g).obj T) _).mpr
    refine ⟨V, hV, ?_⟩
    intro p
    change (pointsSchemeBaseEquiv B S S' hS hS' g T).symm p.class ∈ W ↔ _
    rw [pointsSchemeBaseEquiv_symm_class]
    exact hp (fieldPointSchemeOverSmallerBase B S S' hS hS' g T p)

private theorem pointsSchemeBaseEquiv_naturality
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS') (T : AlgebraicGeometry.BigFppfOver B S hS)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : yoneda.obj T ⟶ F)
    (x : AlgebraicGeometry.Space.points B S hS (yoneda.obj T)) :
    pointsOverLargerBaseEquiv B S S' hS hS' g F (Space.pointsMap B S hS _ a x) =
      Space.pointsMap B S' hS' _
        ((relocalizedYonedaIso g T).hom ≫ (OverShriek.relocalizePresheafFunctor g).map a)
        (pointsSchemeBaseEquiv B S S' hS hS' g T x) := by
  rw [pointsOverLargerBaseEquiv_naturality]
  change _ = Space.pointsMap B S' hS' _ _
    (Space.pointsMap B S' hS' _ (relocalizedYonedaIso g T).inv
      (pointsOverLargerBaseEquiv B S S' hS hS' g (yoneda.obj T) x))
  rw [← Space.pointsMap_comp_apply, Iso.inv_hom_id_assoc]

private noncomputable def pointsOverLargerBaseHomeomorph
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    [MorphismProperty.IsLocalAtTarget (@Etale.{u}) Scheme.fppfPrecoverage]
    [MorphismProperty.IsLocalAtTarget (@Surjective.{u}) Scheme.fppfPrecoverage]
    (F : AlgebraicSpaces B S hS) :
    letI := spacePointTopology B S hS F.obj F.property
    letI := spacePointTopology B S' hS'
      ((OverShriek.relocalizePresheafFunctor g).obj F.obj)
      (AlgebraicGeometry.isAlgebraicSpace_viewOver B S S' hS hS' g F.obj F.property)
    AlgebraicGeometry.Space.points B S hS F.obj ≃ₜ AlgebraicGeometry.Space.points B S' hS'
      ((OverShriek.relocalizePresheafFunctor g).obj F.obj) := by
  let F' := (OverShriek.relocalizePresheafFunctor g).obj F.obj
  let hF' := AlgebraicGeometry.isAlgebraicSpace_viewOver B S S' hS hS' g F.obj F.property
  letI := spacePointTopology B S hS F.obj F.property
  letI := spacePointTopology B S' hS' F' hF'
  have hcont : Continuous (pointsOverLargerBaseEquiv B S S' hS hS' g F.obj) ∧
      Continuous (pointsOverLargerBaseEquiv B S S' hS hS' g F.obj).symm := by
    obtain ⟨U, a, hs, he⟩ := F.property.exists_atlas
    let U' := (Over.map g).obj U
    let hU := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U
    let hU' := AlgebraicGeometry.isAlgebraicSpace_yoneda B S' hS' U'
    let := spacePointTopology B S hS (yoneda.obj U) hU
    let := spacePointTopology B S' hS' (yoneda.obj U') hU'
    let a' := (relocalizedYonedaIso g U).hom ≫ (OverShriek.relocalizePresheafFunctor g).map a
    have hs' := (presheaf_property_relocalize_iff B S S' hS hS' g
      (@Surjective.{u}) U F a).mpr hs
    have he' := (presheaf_property_relocalize_iff B S S' hS hS' g
      (@Etale.{u}) U F a).mpr he
    let E := pointsOverLargerBaseEquiv B S S' hS hS' g F.obj
    let H := pointsSchemeBaseHomeomorph B S S' hS hS' g U
    let p := Space.pointsMap B S hS _ a
    let p' := Space.pointsMap B S' hS' _ a'
    have hq : Topology.IsQuotientMap p :=
      Space.isQuotientMap_pointsMap_of_presheafEtale B S hS a he
        ((Space.presheafSurjective_iff_isSurjective_yoneda B S hS F.obj F.property U a).mp hs)
    have hq' : Topology.IsQuotientMap p' :=
      Space.isQuotientMap_pointsMap_of_presheafEtale B S' hS' a' he'
        ((Space.presheafSurjective_iff_isSurjective_yoneda B S' hS' F' hF' U' a').mp hs')
    have hcomm (x) : E (p x) = p' (H x) :=
      pointsSchemeBaseEquiv_naturality B S S' hS hS' g U a x
    have hcomm' (x) : E.symm (p' x) = p (H.symm x) := by
      apply E.injective
      rw [E.apply_symm_apply, hcomm, H.apply_symm_apply]
    refine ⟨hq.continuous_iff.mpr ?_, hq'.continuous_iff.mpr ?_⟩
    · simpa only [Function.comp_def, ← hcomm] using hq'.continuous.comp H.continuous
    · simpa only [Function.comp_def, ← hcomm'] using hq.continuous.comp H.symm.continuous
  exact ⟨pointsOverLargerBaseEquiv B S S' hS hS' g F.obj, hcont.1, hcont.2⟩

private theorem isClosed_relocalize_iff
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    [MorphismProperty.IsLocalAtTarget (@Etale.{u}) Scheme.fppfPrecoverage]
    [MorphismProperty.IsLocalAtTarget (@Surjective.{u}) Scheme.fppfPrecoverage]
    {F G : AlgebraicSpaces B S hS} (f : F ⟶ G) :
    spaceIsClosedMorphism B S' hS'
        (AlgebraicGeometry.isAlgebraicSpace_viewOver B S S' hS hS' g F.obj F.property)
        (AlgebraicGeometry.isAlgebraicSpace_viewOver B S S' hS hS' g G.obj G.property)
        ((OverShriek.relocalizePresheafFunctor g).map f.hom) ↔
      spaceIsClosedMorphism B S hS F.property G.property f.hom := by
  let := spacePointTopology B S hS F.obj F.property
  let := spacePointTopology B S hS G.obj G.property
  let := spacePointTopology B S' hS'
    ((OverShriek.relocalizePresheafFunctor g).obj F.obj)
    (AlgebraicGeometry.isAlgebraicSpace_viewOver B S S' hS hS' g F.obj F.property)
  let := spacePointTopology B S' hS'
    ((OverShriek.relocalizePresheafFunctor g).obj G.obj)
    (AlgebraicGeometry.isAlgebraicSpace_viewOver B S S' hS hS' g G.obj G.property)
  let EF := pointsOverLargerBaseHomeomorph B S S' hS hS' g F
  let EG := pointsOverLargerBaseHomeomorph B S S' hS hS' g G
  let p := Space.pointsMap B S hS F.obj f.hom
  let p' := Space.pointsMap B S' hS' _ ((OverShriek.relocalizePresheafFunctor g).map f.hom)
  have hw (x) : EG (p x) = p' (EF x) :=
    pointsOverLargerBaseEquiv_naturality B S S' hS hS' g f.hom x
  constructor
  · intro hf
    change IsClosedMap p
    have h : IsClosedMap (EG.symm ∘ p' ∘ EF) :=
      EG.symm.isClosedMap.comp (IsClosedMap.comp hf EF.isClosedMap)
    simpa only [Function.comp_def, ← hw, EG.symm_apply_apply] using h
  · intro hf
    change IsClosedMap p'
    have hw' (x) : EG (p (EF.symm x)) = p' x := by
      rw [hw, EF.apply_symm_apply]
    have h : IsClosedMap (EG ∘ p ∘ EF.symm) :=
      EG.isClosedMap.comp (IsClosedMap.comp hf EF.symm.isClosedMap)
    simpa only [Function.comp_def, hw'] using h

private theorem relocalizePreservesPullbacks
    {C : Type*} [Category.{u} C] {U V : C} (f : V ⟶ U) :
    PreservesLimitsOfShape WalkingCospan
      (OverShriek.relocalizePresheafFunctor f) := by
  let PFV := OverShriek.presheafFunctorToOver (U := V)
  let PFU := OverShriek.presheafFunctorToOver (U := U)
  let RF := OverShriek.relocalizePresheafFunctor f
  let : PFV.IsEquivalence := (OverShriek.presheafEquivalence (U := V)).isEquivalence_functor
  let : PFU.IsEquivalence := (OverShriek.presheafEquivalence (U := U)).isEquivalence_functor
  let : PreservesLimitsOfShape WalkingCospan PFV := inferInstance
  let : PreservesLimitsOfShape WalkingCospan PFU := inferInstance
  let : ReflectsLimitsOfShape WalkingCospan PFU := inferInstance
  let : PreservesLimitsOfShape WalkingCospan
      (Over.map (yoneda.map f) ⋙ Over.forget (yoneda.obj U)) := by
    change PreservesLimitsOfShape WalkingCospan (Over.forget (yoneda.obj V))
    infer_instance
  let : PreservesLimitsOfShape WalkingCospan (Over.map (yoneda.map f)) :=
    preservesLimitsOfShape_of_reflects_of_preserves
      (Over.map (yoneda.map f)) (Over.forget (yoneda.obj U))
  let : PreservesLimitsOfShape WalkingCospan
      (PFV ⋙ Over.map (yoneda.map f)) := inferInstance
  let : PreservesLimitsOfShape WalkingCospan (RF ⋙ PFU) :=
    preservesLimitsOfShape_of_natIso
      (OverShriek.relocalizePresheafFunctorToOverIso f).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves RF PFU

attribute [local instance] relocalizePreservesPullbacks

private theorem presheaf_property_of_relocalize
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (hrep : yoneda.relativelyRepresentable f)
    (hf : (P.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme B S' hS')).presheaf
      ((OverShriek.relocalizePresheafFunctor g).map f)) :
    (P.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f := by
  let Q := P.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let Q' := P.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme B S' hS')
  let R := OverShriek.relocalizePresheafFunctor g
  let j := Over.map g
  let : Q.RespectsIso := inferInstance
  change Q.presheaf f
  apply MorphismProperty.relative.of_exists
  intro U a
  obtain ⟨T, b, c, hpb⟩ := hrep a
  let eU := relocalizedYonedaIso g U
  let eT := relocalizedYonedaIso g T
  let a' := eU.hom ≫ R.map a
  let c' := eT.hom ≫ R.map c
  have hpb' : IsPullback c' (yoneda.map (j.map b)) (R.map f) a' := by
    apply IsPullback.of_iso (hpb.map R) eT.symm (Iso.refl _) eU.symm (Iso.refl _)
    · simp [c']
    · have hn := relocalizedYonedaIso_naturality g b
      simpa [Category.assoc] using
        congrArg (fun k => eT.inv ≫ k ≫ eU.inv) hn.symm
    · simp
    · simp [a']
  refine ⟨T, c, b, hpb, ?_⟩
  exact hf.2 a' c' (j.map b) hpb'

private theorem relativeDiagonal_representable
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F) :
    yoneda.relativelyRepresentable (pullback.diagonal f) := by
  let q := prod.lift (pullback.fst f f) (pullback.snd f f)
  have hd : pullback.diagonal f ≫ q = Limits.diag F := by
    ext <;> simp [q]
  have hp : IsPullback (𝟙 F) (pullback.diagonal f) (Limits.diag F) q := by
    refine ⟨⟨hd.symm⟩, ⟨PullbackCone.IsLimit.mk hd.symm (fun s => s.fst) ?_ ?_ ?_⟩⟩
    · intro s; simp
    · intro s
      apply pullback.hom_ext
      · simpa [q] using congrArg (fun k => k ≫ prod.fst) s.condition
      · simpa [q] using congrArg (fun k => k ≫ prod.snd) s.condition
    · intro s m hm₁ hm₂; simpa using hm₁
  exact (Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback
    hp hF.diagonal_representable

private theorem separated_of_relocalize
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    {F G : AlgebraicSpaces B S hS} (f : F ⟶ G)
    (hf : AlgebraicGeometry.Space.IsSeparated B S' hS'
      ((OverShriek.relocalizePresheafFunctor g).map f.hom)) :
    AlgebraicGeometry.Space.IsSeparated B S hS f.hom := by
  let R := OverShriek.relocalizePresheafFunctor g
  let Q := (MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S' hS')).presheaf
  let : Q.RespectsIso := inferInstance
  let e := (IsPullback.of_hasPullback f.hom f.hom).map R |>.isoPullback
  have he : R.map (pullback.diagonal f.hom) ≫ e.hom =
      pullback.diagonal (R.map f.hom) := by
    apply pullback.hom_ext <;> simp [e, ← R.map_comp]
  have hclosed : Q (R.map (pullback.diagonal f.hom)) := by
    change Q (pullback.diagonal (R.map f.hom)) at hf
    apply (Q.arrow_mk_iso_iff
      (Arrow.isoMk (Iso.refl _) e (by simpa using he.symm) :
        Arrow.mk (R.map (pullback.diagonal f.hom)) ≅
          Arrow.mk (pullback.diagonal (R.map f.hom)))).mpr
    exact hf
  exact presheaf_property_of_relocalize B S S' hS hS' g
    (@AlgebraicGeometry.IsClosedImmersion.{u}) (pullback.diagonal f.hom)
    (relativeDiagonal_representable B S hS f.hom F.property) hclosed


private noncomputable def pointsIsoHomeomorph
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G) (e : F ≅ G) :
    letI := spacePointTopology B S hS F hF
    letI := spacePointTopology B S hS G hG
    AlgebraicGeometry.Space.points B S hS F ≃ₜ AlgebraicGeometry.Space.points B S hS G := by
  letI := spacePointTopology B S hS F hF
  letI := spacePointTopology B S hS G hG
  exact ⟨pointsIsoEquiv B S hS e,
    (Space.pointTopologyFamily B S hS).continuous hF hG e.hom,
    (Space.pointTopologyFamily B S hS).continuous hG hF e.inv⟩

private theorem isClosed_precomp_iso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F F' G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hF' : AlgebraicGeometry.IsAlgebraicSpace B S hS F')
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (e : F ≅ F') (f : F' ⟶ G) (hf : spaceIsClosedMorphism B S hS hF' hG f) :
    spaceIsClosedMorphism B S hS hF hG (e.hom ≫ f) := by
  let := spacePointTopology B S hS F hF
  let := spacePointTopology B S hS F' hF'
  let := spacePointTopology B S hS G hG
  have h := IsClosedMap.comp hf (pointsIsoHomeomorph B S hS hF hF' e).isClosedMap
  change IsClosedMap (Space.pointsMap B S hS F' f ∘
    Space.pointsMap B S hS F e.hom) at h
  simpa only [Function.comp_def, ← Space.pointsMap_comp_apply] using h

private theorem universallyClosed_of_relocalize
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    [MorphismProperty.IsLocalAtTarget (@Etale.{u}) Scheme.fppfPrecoverage]
    [MorphismProperty.IsLocalAtTarget (@Surjective.{u}) Scheme.fppfPrecoverage]
    {F G : AlgebraicSpaces B S hS} (f : F ⟶ G)
    (hf : spaceUniversallyClosed B S' hS'
      (AlgebraicGeometry.isAlgebraicSpace_viewOver B S S' hS hS' g F.obj F.property)
      (AlgebraicGeometry.isAlgebraicSpace_viewOver B S S' hS hS' g G.obj G.property)
      ((OverShriek.relocalizePresheafFunctor g).map f.hom)) :
    spaceUniversallyClosed B S hS F.property G.property f.hom := by
  intro Z hZ a
  let R := OverShriek.relocalizePresheafFunctor g
  let hP := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS a f.hom hZ F.property G.property
  let hZ' := AlgebraicGeometry.isAlgebraicSpace_viewOver B S S' hS hS' g Z hZ
  have h := hf (R.obj Z) hZ' (R.map a)
  let e := (IsPullback.of_hasPullback a f.hom).map R |>.isoPullback
  have h' := isClosed_precomp_iso B S' hS'
    (AlgebraicGeometry.isAlgebraicSpace_viewOver B S S' hS hS' g _ hP)
    (AlgebraicGeometry.isAlgebraicSpace_pullback B S' hS' (R.map a) (R.map f.hom) hZ'
      (AlgebraicGeometry.isAlgebraicSpace_viewOver B S S' hS hS' g F.obj F.property)
      (AlgebraicGeometry.isAlgebraicSpace_viewOver B S S' hS hS' g G.obj G.property))
    hZ' e (pullback.fst (R.map a) (R.map f.hom)) h
  have he : e.hom ≫ pullback.fst (R.map a) (R.map f.hom) = R.map (pullback.fst a f.hom) := by
    simp [e]
  rw [he] at h'
  exact (isClosed_relocalize_iff B S S' hS hS' g
    (F := ⟨_, hP⟩) (G := ⟨Z, hZ⟩) (ObjectProperty.homMk (pullback.fst a f.hom))).mp h'

private theorem exists_space_over_relocalized
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS') (F : AlgebraicSpaces B S hS)
    (Z : (AlgebraicGeometry.BigFppfOver B S' hS')ᵒᵖ ⥤ Type u)
    (hZ : AlgebraicGeometry.IsAlgebraicSpace B S' hS' Z)
    (a : Z ⟶ (OverShriek.relocalizePresheafFunctor g).obj F.obj) :
    ∃ (X : AlgebraicSpaces B S hS)
      (e : (OverShriek.relocalizePresheafFunctor g).obj X.obj ≅ Z)
      (b : X ⟶ F), e.hom ≫ a = (OverShriek.relocalizePresheafFunctor g).map b.hom := by
  let d := smallerBaseEquivalenceData B S S' hS hS' g
  let a₀ := a ≫ (d.2.app F).inv
  let Z₀ : SpacesOverSmallerBase B S S' hS hS' g :=
    ⟨Over.mk (a₀ ≫ (d.1.functor.obj F).obj.hom), hZ⟩
  let α : Z₀ ⟶ d.1.functor.obj F := ObjectProperty.homMk (Over.homMk a₀ rfl)
  let X := d.1.inverse.obj Z₀
  let b : X ⟶ F := d.1.functor.preimage (d.1.counitIso.hom.app Z₀ ≫ α)
  let H := ObjectProperty.ι (fun Y : Over (yoneda.obj (Over.mk g)) =>
    AlgebraicGeometry.IsAlgebraicSpace B S' hS' Y.left) ⋙ Over.forget _
  let e := (d.2.app X).symm ≪≫ H.mapIso (d.1.counitIso.app Z₀)
  refine ⟨X, e, b, ?_⟩
  have hn := d.2.hom.naturality b
  change (d.1.functor.map b).hom.left ≫ (d.2.app F).hom =
    (d.2.app X).hom ≫ (OverShriek.relocalizePresheafFunctor g).map b.hom at hn
  rw [show d.1.functor.map b = d.1.counitIso.hom.app Z₀ ≫ α from
    d.1.functor.map_preimage _] at hn
  have hh := congrArg (fun k => (d.2.app X).inv ≫ k) hn
  simpa [e, H, α, a₀, Category.assoc] using hh

end CurvesVersality

end AlgebraicGeometry

end
