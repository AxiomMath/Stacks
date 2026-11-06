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
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenVersality.CurvesOverBase
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenVersality.ProperFlatFamilies
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenVersality.OverIntegers
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenVersality.Relocalization
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenVersality.LargerBaseFamilies
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenVersality.CurvesOverBase

/-!
# Transport of versality and openness of versality for curves

The remaining properties preserved by relocalization (closedness, universal closedness, finite
presentation, properness, relative dimension), the full faithfulness of
`curveOverS_toProperFlatCurves` with its lifts of proper flat curves, the transport of versality
along a fully faithful functor, and the two main results: openness of versality for curves over
`Spec ℤ` and over a Noetherian scheme, with Stacks 0D3X carried as a hypothesis.
-/

@[expose] public section

attribute [local implicit_reducible] AlgebraicGeometry.curvesProjectionOver

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Deformation.Artin

universe u

namespace CurvesVersality

attribute [local instance] schemeCutoff_isClosedUnderIsomorphisms
attribute [local instance] schemeCutoff_isClosedUnderPullbacks
attribute [local instance] AlgebraicGeometry.BigFppfSite.hasPullbacks_schemes
attribute [local instance] MorphismProperty.IsMultiplicative.toContainsIdentities
attribute [local instance] relocalizePreservesPullbacks
attribute [local instance] relocalize_faithful

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_VersalityTransport
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_VersalityTransport
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on `Over T` (instance search times out without this shortcut). -/
local instance hasPullbacks_overPresheaf_VersalityTransport (T : Scheme.{u}) :
    HasPullbacks ((Over T)ᵒᵖ ⥤ Type u) := inferInstance

set_option synthInstance.maxHeartbeats 400000 in
/-- Small products of presheaves on `Over T` (instance search times out without this
shortcut). -/
local instance hasLimitsOfShape_discrete_overPresheaf_VersalityTransport (T : Scheme.{u})
    (J : Type) : HasLimitsOfShape (Discrete J) ((Over T)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_overPresheaf_VersalityTransport
    (T : Scheme.{u}) {X Y Z : (Over T)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

private theorem isClosed_of_arrowIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G F' G' : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} {f' : F' ⟶ G'}
    (hF : AlgebraicGeometry.IsAlgebraicSpace B S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (hF' : AlgebraicGeometry.IsAlgebraicSpace B S hS F')
    (hG' : AlgebraicGeometry.IsAlgebraicSpace B S hS G')
    (e : Arrow.mk f ≅ Arrow.mk f')
    (hf' : spaceIsClosedMorphism B S hS hF' hG' f') :
    spaceIsClosedMorphism B S hS hF hG f := by
  let := spacePointTopology B S hS F hF
  let := spacePointTopology B S hS G hG
  let := spacePointTopology B S hS F' hF'
  let := spacePointTopology B S hS G' hG'
  let ex := pointsIsoHomeomorph B S hS hF hF' (Arrow.leftFunc.mapIso e)
  let ey := pointsIsoHomeomorph B S hS hG hG' (Arrow.rightFunc.mapIso e)
  have h := ey.symm.isClosedMap.comp (IsClosedMap.comp hf' ex.isClosedMap)
  have hw : e.hom.left ≫ f' ≫ e.inv.right = f := by
    have he : e.hom.left ≫ f' = f ≫ e.hom.right := e.hom.w
    have hei : e.hom.right ≫ e.inv.right = 𝟙 G :=
      (Arrow.rightFunc.mapIso e).hom_inv_id
    rw [← Category.assoc, he, Category.assoc, hei, Category.comp_id]
  show IsClosedMap (Space.pointsMap B S hS F f)
  convert h using 1
  funext x
  show Space.pointsMap B S hS F f x =
    Space.pointsMap B S hS G' e.inv.right
      (Space.pointsMap B S hS F' f'
        (Space.pointsMap B S hS F e.hom.left x))
  rw [← Space.pointsMap_comp_apply, ← Space.pointsMap_comp_apply, hw]

private theorem universallyClosed_relocalize
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    [MorphismProperty.IsLocalAtTarget (@Etale.{u}) Scheme.fppfPrecoverage]
    [MorphismProperty.IsLocalAtTarget (@Surjective.{u}) Scheme.fppfPrecoverage]
    {F G : AlgebraicSpaces B S hS} (f : F ⟶ G)
    (hf : spaceUniversallyClosed B S hS F.property G.property f.hom) :
    spaceUniversallyClosed B S' hS'
      (AlgebraicGeometry.isAlgebraicSpace_viewOver B S S' hS hS' g F.obj F.property)
      (AlgebraicGeometry.isAlgebraicSpace_viewOver B S S' hS hS' g G.obj G.property)
      ((OverShriek.relocalizePresheafFunctor g).map f.hom) := by
  intro Z hZ a
  let R := OverShriek.relocalizePresheafFunctor g
  obtain ⟨X, e, b, hb⟩ := exists_space_over_relocalized B S S' hS hS' g G Z hZ a
  let hP := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS b.hom f.hom
    X.property F.property G.property
  have hp := (IsPullback.of_hasPullback b.hom f.hom).map R
  have hp' : IsPullback (R.map (pullback.fst b.hom f.hom) ≫ e.hom)
      (R.map (pullback.snd b.hom f.hom)) a (R.map f.hom) := by
    apply hp.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
    · simp
    · simp
    · simp only [Iso.refl_hom, Category.comp_id]; exact hb.symm
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  let α : Arrow.mk (R.map (pullback.fst b.hom f.hom)) ≅
      Arrow.mk (pullback.fst a (R.map f.hom)) :=
    Arrow.isoMk hp'.isoPullback e (by simp)
  exact isClosed_of_arrowIso B S' hS'
    (AlgebraicGeometry.isAlgebraicSpace_pullback B S' hS' a (R.map f.hom) hZ
      (AlgebraicGeometry.isAlgebraicSpace_viewOver B S S' hS hS' g F.obj F.property)
      (AlgebraicGeometry.isAlgebraicSpace_viewOver B S S' hS hS' g G.obj G.property))
    hZ (AlgebraicGeometry.isAlgebraicSpace_viewOver B S S' hS hS' g _ hP)
    (AlgebraicGeometry.isAlgebraicSpace_viewOver B S S' hS hS' g X.obj X.property) α.symm
    ((isClosed_relocalize_iff B S S' hS hS' g
      (F := ⟨_, hP⟩) (G := X) (ObjectProperty.homMk (pullback.fst b.hom f.hom))).mpr
      (hf X.obj X.property b.hom))

private theorem finitePresentation_relocalize
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    [MorphismProperty.IsLocalAtTarget (@Etale.{u}) Scheme.fppfPrecoverage]
    [MorphismProperty.IsLocalAtTarget (@Surjective.{u}) Scheme.fppfPrecoverage]
    {F G : AlgebraicSpaces B S hS} (f : F ⟶ G)
    (hf : AlgebraicGeometry.Space.IsFinitePresentation B S hS f.hom) :
    AlgebraicGeometry.Space.IsFinitePresentation B S' hS'
      ((OverShriek.relocalizePresheafFunctor g).map f.hom) := by
  refine ⟨holdsOnEveryEtaleChart_relocalize B S S' hS hS' g _ f hf.1,
    quasiCompact_relocalize B S S' hS hS' g f hf.2.1, ?_⟩
  let R := OverShriek.relocalizePresheafFunctor g
  let hP := AlgebraicGeometry.isAlgebraicSpace_pullback B S hS f.hom f.hom
    F.property F.property G.property
  let e := (IsPullback.of_hasPullback f.hom f.hom).map R |>.isoPullback
  have he : R.map (pullback.diagonal f.hom) ≫ e.hom =
      pullback.diagonal (R.map f.hom) := by
    apply pullback.hom_ext <;> simp [e, ← R.map_comp]
  have hd := quasiCompact_relocalize B S S' hS hS' g
    (ObjectProperty.homMk (pullback.diagonal f.hom) : F ⟶ ⟨_, hP⟩) hf.2.2
  show AlgebraicGeometry.Space.IsQuasiCompact B S' hS' (pullback.diagonal (R.map f.hom))
  rw [← he]
  exact quasiCompact_postcomp_iso B S' hS' e hd

private theorem proper_relocalize
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    [MorphismProperty.IsLocalAtTarget (@Etale.{u}) Scheme.fppfPrecoverage]
    [MorphismProperty.IsLocalAtTarget (@Surjective.{u}) Scheme.fppfPrecoverage]
    {F G : AlgebraicSpaces B S hS} (f : F ⟶ G)
    (hf : spaceIsProper B S hS F.property G.property f.hom) :
    spaceIsProper B S' hS'
      (AlgebraicGeometry.isAlgebraicSpace_viewOver B S S' hS hS' g F.obj F.property)
      (AlgebraicGeometry.isAlgebraicSpace_viewOver B S S' hS hS' g G.obj G.property)
      ((OverShriek.relocalizePresheafFunctor g).map f.hom) :=
  ⟨separated_relocalize B S S' hS hS' g f hf.1,
    ⟨holdsOnEveryEtaleChart_relocalize B S S' hS hS' g _ f hf.2.1.1,
      quasiCompact_relocalize B S S' hS hS' g f hf.2.1.2⟩,
    universallyClosed_relocalize B S S' hS hS' g f hf.2.2⟩

private theorem relativeDimensionLE_relocalize
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S')
    (g : B.obj hS ⟶ B.obj hS')
    [MorphismProperty.IsLocalAtTarget (@Etale.{u}) Scheme.fppfPrecoverage]
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : Space.HasRelativeDimensionLE 1 B S hS f.hom) :
    Space.HasRelativeDimensionLE 1 B S' hS'
      ((OverShriek.relocalizePresheafFunctor g).map f.hom) := by
  intro x
  let R := OverShriek.relocalizePresheafFunctor g
  let ex := pointsOverLargerBaseEquiv B S S' hS hS' g X.obj
  obtain ⟨d, hd, hdim⟩ := hf (ex.symm x)
  refine ⟨d, hd, ?_⟩
  intro c
  let U := relocalizedChartBase g c.a
  let V := relocalizedChartBase g c.b
  let a := relocalizedChartMap g c.a
  let b := relocalizedChartMap g c.b
  let h := relocalizedChartHom g f.hom c.a c.b c.h c.comm
  let p₀ : Space.FieldValuedPoint B S' hS' (yoneda.obj ((Over.map g).obj U)) := {
    carrier := c.representative.carrier
    contained := c.representative.contained
    toBase := c.representative.toBase
    value := c.representative.value ≫ (relocalizedChartIso g c.a).inv
  }
  let p := fieldPointSchemeOverSmallerBase B S S' hS hS' g U p₀
  have hp : pointsOverLargerBaseEquiv B S S' hS hS' g (yoneda.obj U) p.class =
      Space.pointsMap B S' hS' _ (relocalizedYonedaIso g U).hom p₀.class := by
    have hh := (pointsSchemeBaseEquiv B S S' hS hS' g U).apply_symm_apply p₀.class
    change Space.pointsMap B S' hS' _ (relocalizedYonedaIso g U).inv
      (pointsOverLargerBaseEquiv B S S' hS hS' g (yoneda.obj U) p.class) = p₀.class at hh
    rw [← hh, ← Space.pointsMap_comp_apply, Iso.inv_hom_id, Space.pointsMap_id_apply]
  have hp₀ : p₀.class = Space.pointsMap B S' hS' _
      (yoneda.map (relocalizedChartIso g c.a).inv) c.representative.class := rfl
  have hm : Space.pointsMap B S hS _ a p.class = ex.symm x := by
    apply ex.injective
    rw [ex.apply_symm_apply]
    show pointsOverLargerBaseEquiv B S S' hS hS' g X.obj
      (Space.pointsMap B S hS _ a p.class) = x
    rw [pointsOverLargerBaseEquiv_naturality, hp, hp₀,
      ← Space.pointsMap_comp_apply, ← Space.pointsMap_comp_apply]
    rw [relocalizedChartMap_fac]
    exact c.maps_to
  have hetale : ∀ {T : Over (B.obj hS')} {W : AlgebraicSpaces B S hS}
      (k : yoneda.obj T ⟶ R.obj W.obj),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S' hS')).presheaf k →
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf (relocalizedChartMap g k) := by
    intro T W k hk
    apply (presheaf_property_relocalize_iff B S S' hS hS' g (@Etale.{u}) _ W _).mp
    rw [relocalizedChartMap_fac']
    exact MorphismProperty.RespectsIso.precomp _ _ _ hk
  let c' : Space.EtaleChartAtPoint B S hS f.hom (ex.symm x) := {
    U := U
    V := V
    a := a
    b := b
    h := h
    a_etale := hetale _ c.a_etale
    b_etale := hetale _ c.b_etale
    comm := relocalizedChartHom_comm g f.hom c.a c.b c.h c.comm
    representative := p
    point := c.point
    maps_to := hm
  }
  have hpv : p.value.left.hom = c.representative.value.left.hom := by
    show (c.representative.value.left ≫ 𝟙 _).hom = _
    rw [Category.comp_id]
  have hs : c'.sourcePoint B S hS = c.sourcePoint B S' hS' := by
    show p.value.left.hom c.point = c.representative.value.left.hom c.point
    rw [hpv]
    rfl
  have hh : (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map c'.h =
      (AlgebraicGeometry.BigFppfOver.toScheme B S' hS').map c.h := rfl
  have hdim' := hdim c'
  change HasFiberDimensionAt (d : ℕ∞)
    (MorphismOfGerms.ofSchemeHom c.h.left.hom (c'.sourcePoint B S hS)) at hdim'
  rw [hs] at hdim'
  exact hdim'

private theorem isPullback_spacesOver_iff
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')
    {W X Y Z : SpacesOverSmallerBase B S S' hS hS' g}
    (f : W ⟶ X) (k : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z) :
    IsPullback f k h i ↔ IsPullback f.hom.left k.hom.left h.hom.left i.hom.left := by
  let H := ObjectProperty.ι (fun Y : Over (yoneda.obj (Over.mk g)) =>
    AlgebraicGeometry.IsAlgebraicSpace B S' hS' Y.left) ⋙ Over.forget _
  constructor
  · intro hp
    let P : SpacesOverSmallerBase B S S' hS hS' g :=
      ⟨Over.mk (pullback.fst h.hom.left i.hom.left ≫ X.obj.hom),
        AlgebraicGeometry.isAlgebraicSpace_pullback B S' hS' h.hom.left i.hom.left
          X.property Y.property Z.property⟩
    let p₁ : P ⟶ X := ObjectProperty.homMk (Over.homMk
      (pullback.fst h.hom.left i.hom.left) rfl)
    let p₂ : P ⟶ Y := ObjectProperty.homMk (Over.homMk
      (pullback.snd h.hom.left i.hom.left) (by
        show pullback.snd h.hom.left i.hom.left ≫ Y.obj.hom =
          pullback.fst h.hom.left i.hom.left ≫ X.obj.hom
        rw [← i.hom.w, ← h.hom.w, ← Category.assoc, ← Category.assoc,
          pullback.condition]))
    have hpP : IsPullback p₁ p₂ h i :=
      IsPullback.of_map_of_faithful H (IsPullback.of_hasPullback h.hom.left i.hom.left)
    let e := hp.isoIsPullback _ _ hpP
    apply IsPullback.of_iso_pullback ⟨congrArg (fun m => m.hom.left) hp.w⟩ (H.mapIso e)
    · show (e.hom ≫ p₁).hom.left = f.hom.left
      simp [e]
    · show (e.hom ≫ p₂).hom.left = k.hom.left
      simp [e]
  · exact IsPullback.of_map_of_faithful H

/-- A preimage along the inverse of an equivalence is determined by the square it makes after
transport along the unit. -/
private theorem preimage_comp_eq_of_unitInv_comm
    {C D : Type*} [Category C] [Category D] (e : C ≌ D)
    {U U' : C} {Z Z' W W' : D}
    (J : W ≅ e.functor.obj U) (J' : W' ≅ e.functor.obj U')
    (a : Z ⟶ W) (a' : Z' ⟶ W') (c : U ⟶ U')
    (ml : e.inverse.obj Z ⟶ e.inverse.obj Z')
    (hw : ml ≫ (e.inverse.map (a' ≫ J'.hom) ≫ e.unitIso.inv.app U') =
      (e.inverse.map (a ≫ J.hom) ≫ e.unitIso.inv.app U) ≫ c) :
    e.inverse.preimage ml ≫ a' = a ≫ (J.hom ≫ e.functor.map c ≫ J'.inv) := by
  have hi : e.inverse.map J'.inv ≫ e.inverse.map J'.hom ≫ e.unitIso.inv.app U' =
      e.unitIso.inv.app U' := by
    rw [← e.inverse.map_comp_assoc, J'.inv_hom_id, e.inverse.map_id, Category.id_comp]
  have hc : e.inverse.map (e.functor.map c) ≫ e.unitIso.inv.app U' =
      e.unitIso.inv.app U ≫ c := e.unitIso.inv.naturality c
  apply e.inverse.map_injective
  apply (cancel_mono (e.inverse.map J'.hom ≫ e.unitIso.inv.app U')).mp
  calc e.inverse.map (e.inverse.preimage ml ≫ a') ≫
        (e.inverse.map J'.hom ≫ e.unitIso.inv.app U')
      = ml ≫ (e.inverse.map (a' ≫ J'.hom) ≫ e.unitIso.inv.app U') := by
        simp only [Functor.map_comp, Functor.map_preimage, Category.assoc]
    _ = (e.inverse.map (a ≫ J.hom) ≫ e.unitIso.inv.app U) ≫ c := hw
    _ = e.inverse.map (a ≫ (J.hom ≫ e.functor.map c ≫ J'.inv)) ≫
        (e.inverse.map J'.hom ≫ e.unitIso.inv.app U') := by
        simp only [Functor.map_comp, Category.assoc, hi, hc]

private theorem spaceFamilyOfLargerBase_preimage_comm
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')
    {T T' : AlgebraicGeometry.BigFppfOver B S hS}
    {Z Z' : SpacesOverSmallerBase B S S' hS hS' g}
    (a : Z ⟶ schemeSpaceOverLargerBase B S S' hS hS' g T)
    (a' : Z' ⟶ schemeSpaceOverLargerBase B S S' hS hS' g T')
    (m : spaceFamilyOfLargerBase B S S' hS hS' g T Z a ⟶
      spaceFamilyOfLargerBase B S S' hS hS' g T' Z' a') :
    (smallerBaseEquivalenceData B S S' hS hS' g).1.inverse.preimage
        m.left ≫ a' = a ≫ schemeSpaceOverLargerBaseMap B S S' hS hS' g m.right := by
  let e := (smallerBaseEquivalenceData B S S' hS hS' g).1
  let I := schemeSpaceOverLargerBaseIso B S S' hS hS' g T
  let I' := schemeSpaceOverLargerBaseIso B S S' hS hS' g T'
  let c := schemeSpaceMap_ m.right
  have hw : m.left ≫ (e.inverse.map (a' ≫ I'.hom) ≫
        e.unitIso.inv.app (schemeSpace_ T')) =
      (e.inverse.map (a ≫ I.hom) ≫ e.unitIso.inv.app (schemeSpace_ T)) ≫ c := by
    apply ObjectProperty.hom_ext
    exact m.w
  exact preimage_comp_eq_of_unitInv_comm e I I' a a' c m.left hw

private theorem spaceFamilyOfLargerBaseMap_isPullback_iff
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')
    {T T' : AlgebraicGeometry.BigFppfOver B S hS} (b : T ⟶ T')
    {Z Z' : SpacesOverSmallerBase B S S' hS hS' g}
    (a : Z ⟶ schemeSpaceOverLargerBase B S S' hS hS' g T)
    (a' : Z' ⟶ schemeSpaceOverLargerBase B S S' hS hS' g T') (m : Z ⟶ Z')
    (hm : m ≫ a' = a ≫ schemeSpaceOverLargerBaseMap B S S' hS hS' g b) :
    IsPullback (spaceFamilyOfLargerBaseMap B S S' hS hS' g b a a' m hm).left.hom
      (spaceFamilyOfLargerBase B S S' hS hS' g T Z a).hom
      (spaceFamilyOfLargerBase B S S' hS hS' g T' Z' a').hom (yoneda.map b) ↔
        IsPullback m.hom.left a.hom.left a'.hom.left (yoneda.map ((Over.map g).map b)) := by
  refine ⟨?_, spaceFamilyOfLargerBaseMap_isPullback B S S' hS hS' g b a a' m hm⟩
  intro hp
  let e := (smallerBaseEquivalenceData B S S' hS hS' g).1
  let I := schemeSpaceOverLargerBaseIso B S S' hS hS' g T
  let I' := schemeSpaceOverLargerBaseIso B S S' hS hS' g T'
  let c := schemeSpaceMap_ b
  have hp₀ : IsPullback (e.inverse.map m)
      (e.inverse.map (a ≫ I.hom) ≫ e.unitIso.inv.app _)
      (e.inverse.map (a' ≫ I'.hom) ≫ e.unitIso.inv.app _) c :=
    (isPullback_spaces_iff B S hS _ _ _ _).mpr hp
  have hp₁ : IsPullback (e.inverse.map m) (e.inverse.map (a ≫ I.hom))
      (e.inverse.map (a' ≫ I'.hom)) (e.inverse.map (e.functor.map c)) := by
    apply hp₀.of_iso (Iso.refl _) (Iso.refl _) (e.unitIso.app _)
      (e.unitIso.app _)
    · simp
    · show (e.inverse.map (a ≫ I.hom) ≫ (e.unitIso.app _).inv) ≫
        (e.unitIso.app _).hom = 𝟙 _ ≫ e.inverse.map (a ≫ I.hom)
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    · show (e.inverse.map (a' ≫ I'.hom) ≫ (e.unitIso.app _).inv) ≫
        (e.unitIso.app _).hom = 𝟙 _ ≫ e.inverse.map (a' ≫ I'.hom)
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    · exact e.unitIso.hom.naturality c
  have hp₂ : IsPullback m (a ≫ I.hom) (a' ≫ I'.hom) (e.functor.map c) :=
    IsPullback.of_map_of_faithful e.inverse hp₁
  have hp₃ : IsPullback m a a' (schemeSpaceOverLargerBaseMap B S S' hS hS' g b) := by
    apply hp₂.of_iso (Iso.refl _) (Iso.refl _) I.symm I'.symm
    · simp
    · simp
    · simp
    · simp [schemeSpaceOverLargerBaseMap, I, I', e, c]
  have hh := (isPullback_spacesOver_iff B S S' hS hS' g _ _ _ _).mp hp₃
  rwa [schemeSpaceOverLargerBaseMap_left] at hh

private noncomputable def curveOverS_preimage
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : CostructuredArrow
      (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS)}
    (k : (curveOverS_toProperFlatCurves B hZ S hS).obj X ⟶
      (curveOverS_toProperFlatCurves B hZ S hS).obj Y) : X ⟶ Y := by
  let g : B.obj hS ⟶ B.obj hZ :=
    B.inclusion.preimage (specULiftZIsTerminal.from (B.obj hS).1)
  let e := (smallerBaseEquivalenceData B S
    integerBase hS hZ g).1
  let m := k.hom.hom.hom
  let n := e.inverse.preimage m.left
  let a := curveOverS_totalToBase B hZ S hS X
  let a' := curveOverS_totalToBase B hZ S hS Y
  have hn := spaceFamilyOfLargerBase_preimage_comm B S integerBase hS hZ g a a' m
  have hm : spaceFamilyOfLargerBaseMap B S integerBase hS hZ g
      m.right a a' n hn = m := by
    apply CommaMorphism.ext
    · exact e.inverse.map_preimage m.left
    · rfl
  have hp := (spaceFamilyOfLargerBaseMap_isPullback_iff B S integerBase
    hS hZ g m.right a a' n hn).mp (by
      rw [hm]
      exact properFlatHom_isPullback_over B S hS k.hom)
  have hX : X.hom ≫ g = X.left.base.hom := by
    apply B.inclusion.map_injective
    apply specULiftZIsTerminal.hom_ext
  have hY : Y.hom ≫ g = Y.left.base.hom := by
    apply B.inclusion.map_injective
    apply specULiftZIsTerminal.hom_ext
  let iX : (Over.map g).obj (Over.mk X.hom) ≅ X.left.base :=
    Over.isoMk (Iso.refl _) (by exact (Category.id_comp _).trans hX.symm)
  let iY : (Over.map g).obj (Over.mk Y.hom) ≅ Y.left.base :=
    Over.isoMk (Iso.refl _) (by exact (Category.id_comp _).trans hY.symm)
  let b : X.left.base ⟶ Y.left.base := Over.homMk m.right.left (by
    apply B.inclusion.map_injective
    apply specULiftZIsTerminal.hom_ext)
  have hc : ∀ {P Q : Over (B.obj hZ)} (i : P ≅ Q) {W : (Over (B.obj hZ))ᵒᵖ ⥤ Type u}
      (f : W ⟶ yoneda.obj Q), (f ≫ yoneda.map i.inv) ≫ yoneda.map i.hom = 𝟙 _ ≫ f := by
    intro P Q i W f
    rw [Category.assoc, ← yoneda.map_comp]
    simp
  have hp' : IsPullback n.hom.left (curveToBase X.left) (curveToBase Y.left) (yoneda.map b) := by
    apply hp.of_iso (Iso.refl _) (Iso.refl _) (yoneda.mapIso iX) (yoneda.mapIso iY)
    · exact (Category.id_comp _).symm
    · exact hc iX _
    · exact hc iY _
    · have hcomm : (Over.map g).map m.right ≫ iY.hom = iX.hom ≫ b := by
        apply Over.OverMorphism.ext
        exact (Category.comp_id (((Over.map g).map m.right).left)).trans
          (Category.id_comp (((Over.map g).map m.right).left)).symm
      change yoneda.map ((Over.map g).map m.right) ≫ yoneda.map iY.hom =
        yoneda.map iX.hom ≫ yoneda.map b
      exact ((yoneda.map_comp ((Over.map g).map m.right) iY.hom).symm.trans
        (congrArg yoneda.map hcomm)).trans (yoneda.map_comp iX.hom b)
  let l : X.left ⟶ Y.left := {
    baseMap := b
    totalMap := ObjectProperty.homMk n.hom.left
    cartesian := (isPullback_spaces_iff B integerBase hZ _ _ _ _).mpr hp'
  }
  exact CostructuredArrow.homMk l (by exact m.right.w)

/-- Morphisms of proper flat curves are equal when their underlying morphisms of families are. -/
private theorem properFlatCurves_hom_ext {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {X Y : ProperFlatCurves B S hS} {f g : X ⟶ Y}
    (h : f.hom.hom.hom = g.hom.hom.hom) : f = g := by
  apply ObjectProperty.hom_ext
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  exact h

private theorem curveOverS_map_preimage
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : CostructuredArrow
      (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS)}
    (k : (curveOverS_toProperFlatCurves B hZ S hS).obj X ⟶
      (curveOverS_toProperFlatCurves B hZ S hS).obj Y) :
    (curveOverS_toProperFlatCurves B hZ S hS).map (curveOverS_preimage B hZ S hS k) = k := by
  let g : B.obj hS ⟶ B.obj hZ :=
    B.inclusion.preimage (specULiftZIsTerminal.from (B.obj hS).1)
  let e := (smallerBaseEquivalenceData B S
    integerBase hS hZ g).1
  apply properFlatCurves_hom_ext
  apply CommaMorphism.ext
  · show e.inverse.map
      (curveOverS_totalOverSmallerBaseMap B hZ S hS (curveOverS_preimage B hZ S hS k)) =
        k.hom.hom.hom.left
    have hn : curveOverS_totalOverSmallerBaseMap B hZ S hS
        (curveOverS_preimage B hZ S hS k) = e.inverse.preimage k.hom.hom.hom.left := by
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      rfl
    rw [hn]
    exact e.inverse.map_preimage _
  · apply Over.OverMorphism.ext
    rfl

private theorem curveOverS_full
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S) :
    (curveOverS_toProperFlatCurves B hZ S hS).Full :=
  ⟨fun k => ⟨curveOverS_preimage B hZ S hS k, curveOverS_map_preimage B hZ S hS k⟩⟩

private theorem curveOverS_faithful
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S) :
    (curveOverS_toProperFlatCurves B hZ S hS).Faithful := by
  constructor
  intro X Y f k h
  let e := (smallerBaseEquivalenceData B S
    integerBase hS hZ
      (B.inclusion.preimage (specULiftZIsTerminal.from (B.obj hS).1))).1
  have ht := congrArg (fun m => m.hom.hom.hom.left) h
  change e.inverse.map (curveOverS_totalOverSmallerBaseMap B hZ S hS f) =
    e.inverse.map (curveOverS_totalOverSmallerBaseMap B hZ S hS k) at ht
  have ht' := congrArg (fun m => m.hom.left) (e.inverse.map_injective ht)
  have hb := congrArg (fun m => m.hom.hom.hom.right.left) h
  apply CostructuredArrow.hom_ext
  apply AlgebraicGeometry.CurveFamily.Hom.ext
  · exact Over.OverMorphism.ext hb
  · apply ObjectProperty.hom_ext
    exact ht'

private noncomputable def spaceFamilyOverSmallerBase
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')
    (C : spaceFamilies B S hS) : spaceFamilies B S' hS' := by
  let e := (smallerBaseEquivalenceData B S S' hS hS' g).1
  let t : C.left ⟶ schemeSpace_ C.right := ObjectProperty.homMk C.hom
  let I := schemeSpaceOverLargerBaseIso B S S' hS hS' g C.right
  exact ⟨⟨(e.functor.obj C.left).obj.left, (e.functor.obj C.left).property⟩,
    (Over.map g).obj C.right, (e.functor.map t ≫ I.inv).hom.left⟩

private noncomputable def spaceFamilyOverSmallerBase_arrowIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')
    (C : spaceFamilies B S hS) :
    Arrow.mk (spaceFamilyOverSmallerBase B S S' hS hS' g C).hom ≅
      Arrow.mk ((OverShriek.relocalizePresheafFunctor g).map C.hom) := by
  let d := smallerBaseEquivalenceData B S S' hS hS' g
  let t : C.left ⟶ schemeSpace_ C.right := ObjectProperty.homMk C.hom
  let I := schemeSpaceOverLargerBaseIso B S S' hS hS' g C.right
  refine Arrow.isoMk (d.2.app C.left) (relocalizedYonedaIso g C.right) ?_
  have ht := d.2.hom.naturality t
  change (d.2.app C.left).hom ≫ (OverShriek.relocalizePresheafFunctor g).map t.hom =
    ((d.1.functor.map t).hom.left ≫ I.inv.hom.left) ≫
      (relocalizedYonedaIso g C.right).hom
  have hI : I.inv.hom.left ≫ (relocalizedYonedaIso g C.right).hom =
      (d.2.app (schemeSpace_ C.right)).hom := by
    change ((d.2.app (schemeSpace_ C.right)).hom ≫
      (relocalizedYonedaIso g C.right).inv) ≫ (relocalizedYonedaIso g C.right).hom = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Category.assoc, hI]
  exact ht.symm

private noncomputable def properFlatCurveOverS
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S) (X : ProperFlatCurves B S hS) :
    CostructuredArrow (AlgebraicGeometry.curvesProjection B hZ ⋙ 𝟭 B.Schemes) (B.obj hS) := by
  let g : B.obj hS ⟶ B.obj hZ :=
    B.inclusion.preimage (specULiftZIsTerminal.from (B.obj hS).1)
  let C := X.obj.obj.obj
  let D := spaceFamilyOverSmallerBase B S integerBase hS hZ g C
  let t : C.left ⟶ schemeSpace_ C.right := ObjectProperty.homMk C.hom
  let α := spaceFamilyOverSmallerBase_arrowIso B S integerBase hS hZ g C
  let hXR := AlgebraicGeometry.isAlgebraicSpace_viewOver B S integerBase hS hZ g
    C.left.obj C.left.property
  let hYR := AlgebraicGeometry.isAlgebraicSpace_viewOver B S integerBase hS hZ g
    (yoneda.obj C.right) (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS C.right)
  let Y : AlgebraicGeometry.CurveFamily B hZ := {
    base := D.right
    total := D.left
    toBase := ObjectProperty.homMk D.hom
    flat := holdsOnEveryEtaleChart_of_arrowIso B integerBase hZ _ α
      (holdsOnEveryEtaleChart_relocalize B S integerBase hS hZ g _ t
        X.obj.obj.property.2.1)
    proper := proper_of_arrowIso B integerBase hZ D.left.property
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B integerBase hZ D.right)
      hXR hYR α (proper_relocalize B S integerBase hS hZ g t
        X.obj.obj.property.2.2)
    finitePresentation := finitePresentation_of_arrowIso B integerBase hZ α
      (finitePresentation_relocalize B S integerBase hS hZ g t X.obj.obj.property.1)
    relativeDimensionLE := relativeDimensionLE_of_arrowIso B integerBase hZ α
      (relativeDimensionLE_relocalize B S integerBase hS hZ g t X.property)
  }
  exact CostructuredArrow.mk (Y := Y) C.right.hom

private noncomputable def properFlatCurvesIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X Y : ProperFlatCurves B S hS) (e : X.obj.obj.obj ≅ Y.obj.obj.obj) : X ≅ Y where
  hom := ObjectProperty.homMk ⟨ObjectProperty.homMk e.hom, by
    change (spacesProjection B S hS).IsStronglyCartesian
      ((spacesProjection B S hS).map e.hom) e.hom
    infer_instance⟩
  inv := ObjectProperty.homMk ⟨ObjectProperty.homMk e.inv, by
    change (spacesProjection B S hS).IsStronglyCartesian
      ((spacesProjection B S hS).map e.inv) e.inv
    infer_instance⟩
  hom_inv_id := properFlatCurves_hom_ext e.hom_inv_id
  inv_hom_id := properFlatCurves_hom_ext e.inv_hom_id

private noncomputable def properFlatCurveOverS_iso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S) (X : ProperFlatCurves B S hS) :
    (curveOverS_toProperFlatCurves B hZ S hS).obj (properFlatCurveOverS B hZ S hS X) ≅ X := by
  let g : B.obj hS ⟶ B.obj hZ :=
    B.inclusion.preimage (specULiftZIsTerminal.from (B.obj hS).1)
  let e := (smallerBaseEquivalenceData B S
    integerBase hS hZ g).1
  let C := X.obj.obj.obj
  let t : C.left ⟶ schemeSpace_ C.right := ObjectProperty.homMk C.hom
  let I := schemeSpaceOverLargerBaseIso B S integerBase hS hZ g C.right
  let a := e.functor.map t ≫ I.inv
  let Y := properFlatCurveOverS B hZ S hS X
  let Z := curveOverS_totalOverSmallerBase B hZ S hS Y
  let δ : Z ≅ e.functor.obj C.left := ObjectProperty.isoMk _
    (Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ (e.functor.obj C.left).obj.hom =
        a.hom.left ≫ yoneda.map
          (Over.homMk C.right.hom : (Over.map g).obj C.right ⟶ Over.mk g)
      have hw : (e.functor.obj C.left).obj.hom =
          a.hom.left ≫ yoneda.map
            (Over.homMk C.right.hom : (Over.map g).obj C.right ⟶ Over.mk g) :=
        a.hom.w.symm
      exact (Category.id_comp _).trans hw))
  let a' := curveOverS_totalToBase B hZ S hS Y
  have ha : δ.hom ≫ e.functor.map t = a' ≫ I.hom := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    have hleft : a'.hom.left = a.hom.left := by
      change a.hom.left ≫ yoneda.map
        (Over.isoMk (Iso.refl _) (by exact Category.id_comp _) :
          (Over.map g).obj (Over.mk C.right.hom) ≅
          (Over.map g).obj C.right).inv = a.hom.left
      have hi : (Over.isoMk (Iso.refl _) (by exact Category.id_comp _) :
          (Over.map g).obj (Over.mk C.right.hom) ≅
          (Over.map g).obj C.right).inv = 𝟙 _ := by
        apply Over.OverMorphism.ext
        rfl
      rw [hi, yoneda.map_id]
      exact Category.comp_id a.hom.left
    change 𝟙 _ ≫ (e.functor.map t).hom.left = a'.hom.left ≫ I.hom.hom.left
    rw [hleft]
    change 𝟙 _ ≫ (e.functor.map t).hom.left = (a ≫ I.hom).hom.left
    simp [a]
  let ei := e.inverse.mapIso δ ≪≫ (e.unitIso.app C.left).symm
  let η : curveOverS_spaceFamily B hZ S hS Y ≅ C := Comma.isoMk ei (Iso.refl _) (by
    change (e.inverse.map δ.hom ≫ e.unitIso.inv.app C.left).hom ≫ C.hom =
      (e.inverse.map (a' ≫ I.hom) ≫ e.unitIso.inv.app (schemeSpace_ C.right)).hom ≫
        yoneda.map (𝟙 C.right)
    have hη : (e.inverse.map δ.hom ≫ e.unitIso.inv.app C.left) ≫ t =
        e.inverse.map (a' ≫ I.hom) ≫ e.unitIso.inv.app (schemeSpace_ C.right) := by
      have ht : e.inverse.map (e.functor.map t) ≫
          e.unitIso.inv.app (schemeSpace_ C.right) =
            e.unitIso.inv.app C.left ≫ t := e.unitIso.inv.naturality t
      rw [Category.assoc, ← ht, ← e.inverse.map_comp_assoc, ha]
    have hmapid : yoneda.map (𝟙 C.right) = 𝟙 (yoneda.obj C.right) :=
      yoneda.map_id C.right
    refine (congrArg (fun k => k.hom) hη).trans ?_
    rw [hmapid]
    exact (Category.comp_id _).symm)
  exact properFlatCurvesIso B S hS _ X η

private theorem properFlatCurveOverS_projection
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S) (X : ProperFlatCurves B S hS) :
    (properFlatCurvesProjection B S hS).obj
      ((curveOverS_toProperFlatCurves B hZ S hS).obj (properFlatCurveOverS B hZ S hS X)) =
        (properFlatCurvesProjection B S hS).obj X := rfl

private theorem properFlatCurveOverS_iso_map
    (B : AlgebraicGeometry.BigFppfSite.{u}) (hZ : B.Contains integerBase)
    (S : Scheme.{u}) (hS : B.Contains S) (X : ProperFlatCurves B S hS) :
    (properFlatCurvesProjection B S hS).map (properFlatCurveOverS_iso B hZ S hS X).hom =
      eqToHom (properFlatCurveOverS_projection B hZ S hS X) := by
  rfl

universe v₁ v₂ w₁ w₂

private theorem isVersalAt_of_fullyFaithful
    {S : Scheme.{u}} {X : Type v₁} [Category.{w₁} X]
    {Y : Type v₂} [Category.{w₂} Y] (F : X ⥤ Y) [F.Full] [F.Faithful]
    (q : Y ⥤ Over S) (U : Over S) (x : X)
    (hx : (F ⋙ q).obj x = U) (u₀ : U.left)
    (h : Deformation.Artin.IsVersalAt U q u₀ (F.obj x) hx) :
    Deformation.Artin.IsVersalAt U (F ⋙ q) u₀ x hx := by
  let := Deformation.Artin.residueFieldAlgebra U u₀
  intro A C f hf y z hy hz i hi a ha
  obtain ⟨b, hb⟩ := h A C f hf (F.obj y) (F.obj z) hy hz (F.map i) hi (F.map a) ha
  refine ⟨F.preimage b, F.map_injective ?_⟩
  simpa only [Functor.map_comp, Functor.map_preimage] using hb

private theorem isVersalAt_map_of_lifts
    {S : Scheme.{u}} {X : Type v₁} [Category.{w₁} X]
    {Y : Type v₂} [Category.{w₂} Y] (F : X ⥤ Y) [F.Full]
    (q : Y ⥤ Over S) (L : Y → X)
    (hL : ∀ y, q.obj (F.obj (L y)) = q.obj y)
    (e : ∀ y, F.obj (L y) ≅ y)
    (he : ∀ y, q.map (e y).hom = eqToHom (hL y))
    (U : Over S) (x : X) (hx : (F ⋙ q).obj x = U) (u₀ : U.left)
    (h : Deformation.Artin.IsVersalAt U (F ⋙ q) u₀ x hx) :
    Deformation.Artin.IsVersalAt U q u₀ (F.obj x) hx := by
  let := Deformation.Artin.residueFieldAlgebra U u₀
  have he' (y : Y) : q.map (e y).inv = eqToHom (hL y).symm := by
    apply (cancel_mono (q.map (e y).hom)).1
    rw [← q.map_comp, Iso.inv_hom_id, q.map_id, he]
    simp
  intro A C f hf y z hy hz i hi a ha
  let hy' := (hL y).trans hy
  let hz' := (hL z).trans hz
  let i' : L y ⟶ L z := F.preimage ((e y).hom ≫ i ≫ (e z).inv)
  let a' : L y ⟶ x := F.preimage ((e y).hom ≫ a)
  have hi' : eqToHom (congrArg Over.left hy').symm ≫
      ((F ⋙ q).map i').left ≫ eqToHom (congrArg Over.left hz') =
        Spec.map (CommRingCat.ofHom f.hom.toRingHom) := by
    simpa [i', hy', hz', Functor.map_comp, he, he', Category.assoc] using hi
  have ha' : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫
      eqToHom (congrArg Over.left hy').symm ≫ ((F ⋙ q).map a').left ≫
        eqToHom (congrArg Over.left hx) = U.left.fromSpecResidueField u₀ := by
    simpa [a', hy', Functor.map_comp, he, Category.assoc] using ha
  obtain ⟨b, hb⟩ := h A C f hf (L y) (L z) hy' hz' i' hi' a' ha'
  refine ⟨(e z).inv ≫ F.map b, ?_⟩
  have hb' := congrArg F.map hb
  simp only [Functor.map_comp, i', a', Functor.map_preimage] at hb'
  apply (cancel_epi (e y).hom).1
  simpa only [Category.assoc] using hb'

end CurvesVersality

open CurvesVersality

/-- **Stacks 0D59 over `Spec ℤ`, with Stacks 0D3X carried as a hypothesis.** Granted openness of
versality for the stack of finitely presented, flat and proper algebraic spaces over `Spec ℤ`,
the stack of curves has openness of versality over `Spec ℤ`.

`hPF` is openness of versality for the strictly larger stack of proper flat families of every
relative dimension, which is the content of Stacks 0D3X. -/
public theorem curves_openVersality_specZ_of_properFlatSpaces
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (hPF : OpenVersalityOf
      (cartesianProperFlatProjection B integerBase hZ ⋙ Over.post B.inclusion)) :
    OpenVersalityOf
      (curvesProjectionOver B hZ ⋙ Over.post B.inclusion) :=
  curves_openVersality_of_properFlat B hZ hPF

/-- **Stacks 0D59 over a Noetherian base, with Stacks 0D3X carried as a hypothesis.** Granted
openness of versality for the stack of finitely presented, flat and proper algebraic spaces over
a Noetherian scheme `S`, the stack of `S`-curves — the base change of Stacks 0D54 — has openness
of versality over `S`.

`hPF` is openness of versality over `S` for the strictly larger stack of proper flat families of
every relative dimension, which is the content of Stacks 0D3X over `S`. -/
public theorem curves_openVersality_of_properFlatSpaces
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (S : Scheme.{u}) [IsNoetherian S] (hS : B.Contains S)
    (hPF : OpenVersalityOf
      (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion)) :
    OpenVersalityOf
      (CostructuredArrow.pre (AlgebraicGeometry.curvesProjection B hZ)
        (𝟭 B.Schemes) (B.obj hS) ⋙ Over.post B.inclusion) := by
  let F := curveOverS_toProperFlatCurves B hZ S hS
  let q := properFlatCurvesProjection B S hS
  let : F.Full := curveOverS_full B hZ S hS
  let : F.Faithful := curveOverS_faithful B hZ S hS
  show OpenVersalityOf (F ⋙ q)
  intro U hU x hx u₀ hu hversal
  have hversal' := isVersalAt_map_of_lifts F q
    (properFlatCurveOverS B hZ S hS)
    (properFlatCurveOverS_projection B hZ S hS)
    (properFlatCurveOverS_iso B hZ S hS)
    (properFlatCurveOverS_iso_map B hZ S hS) U x hx u₀ hversal
  obtain ⟨V, huV, hV⟩ := properFlatCurves_openVersality B S hS hPF U hU
    (F.obj x) hx u₀ hu hversal'
  refine ⟨V, huV, ?_⟩
  intro v hv hvft
  exact isVersalAt_of_fullyFaithful F q U x hx v (hV v hv hvft)

end AlgebraicGeometry

end
