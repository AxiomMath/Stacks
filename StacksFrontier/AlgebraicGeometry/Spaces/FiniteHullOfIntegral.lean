module

public import StacksFrontier.AlgebraicGeometry.Spaces.FppfSingletonCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFppfLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeOverMapPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardAlgebraChartIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardAlgebraQuasicoherentQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalizationAlgebraCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSubalgebraContainingSections
public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedDirectImageAlgebraFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraSectionsCutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Morphisms.OpenImmersionIntoSubalgebraSpec

/-!
# Replacing an integral morphism by a finite one without losing a quasi-compact open

Let `X` be a quasi-compact and quasi-separated algebraic space, let `ν : N → X` be affine and
integral, and let `W → N` be a quasi-compact open immersion with `W → X` locally of finite type.
Then `ν` factors as `N → N' → X` with `N' → X` finite, `N → N'` surjective, and `W → N'` still an
open immersion.

## Main results

* `AlgebraicGeometry.Space.exists_isFinite_isOpenImmersion_comp_of_isIntegralHom`: the finite
  factorization of an integral affine morphism preserving a quasi-compact open of finite type.
* `AlgebraicGeometry.Space.isFinite_of_finite_algebraMap_chart`: an affine morphism of
  algebraic spaces is finite as soon as its functions over one affine surjective étale chart are
  finite over those of the chart.
* `AlgebraicGeometry.Space.isSurjective_of_injective_appTop_chart`: a morphism over `X` of
  affine spaces over `X`, with integral source, is surjective as soon as it is injective on
  functions over one affine surjective étale chart.

## References

* [Stacks, Tag 09YC], [Stacks, Tag 082C], [Stacks, Tag 0ABS]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_FiniteHullOfIntegral
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- Let `Q` be a property of morphisms of algebraic spaces which respects isomorphisms and is
local on the target for the fppf topology. In a cartesian square of presheaves, if `g` base changes
along a surjective étale `f` to a morphism with property `Q`, then `g` has property `Q`. -/
theorem of_isPullback_of_isEtale_of_isSurjective
    (Q : ∀ {P P' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, (P ⟶ P') → Prop)
    (hQiso : ∀ {P P' P'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : P ≅ P') (k : P' ⟶ P''),
      Q k → Q (e.hom ≫ k))
    [hQ : MorphismProperty.IsLocalAtTarget
      ((fun (_ _ : AlgebraicSpaces B S hS) f => Q f.hom) :
        MorphismProperty (AlgebraicSpaces B S hS))
      (Topology.fppf.precoverage.{u, u} B S hS)]
    {T X V P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hX : IsAlgebraicSpace B S hS X)
    (hV : IsAlgebraicSpace B S hS V)
    {g : T ⟶ X} {f : V ⟶ X} {fst : P ⟶ T} {snd : P ⟶ V} (sq : IsPullback fst snd g f)
    (hfe : IsEtale B S hS f) (hfs : IsSurjective B S hS f) (h : Q snd) : Q g := by
  let T' : AlgebraicSpaces B S hS := ⟨T, hT⟩
  let X' : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let V' : AlgebraicSpaces B S hS := ⟨V, hV⟩
  let g' : T' ⟶ X' := ObjectProperty.homMk g
  let f' : V' ⟶ X' := ObjectProperty.homMk f
  have key := prop_iff_pullbackSnd_of_fppf.{u, u} B S hS
    (fun (_ _ : AlgebraicSpaces B S hS) k => Q k.hom) g' f' hfs (isFlat_of_isEtale B S hS hfe)
    (isLocallyOfFinitePresentation_of_isEtale B S hS hfe)
  refine key.2 ?_
  have sqA := AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback g' f')
  have he : (sq.isoIsPullback _ _ sqA).inv ≫ snd = (pullback.snd g' f').hom :=
    sq.isoIsPullback_inv_snd _ _ sqA
  change Q (pullback.snd g' f').hom
  rw [← he]
  exact hQiso (sq.isoIsPullback _ _ sqA).symm snd h

variable {B S hS} in
/-- A finite morphism of the site is finite as a morphism of algebraic spaces. -/
theorem isFinite_yoneda_map_of_isFinite {C A : BigFppfOver B S hS} {p : C ⟶ A}
    (hp : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map p)) :
    IsFinite B S hS (schemeSpaceMap p).hom := by
  change IsFinite B S hS (yoneda.map p)
  let Q := MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let _ : Q.IsStableUnderBaseChange :=
    property_inverseImage_baseChange B S hS
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
  have h : Q.presheaf (yoneda.map p) := MorphismProperty.relative_map (P := Q) hp
  intro U hU a
  obtain ⟨V, q, i, hs⟩ := h.rep a
  have hq : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map q) :=
    h.property a i q hs
  exact ⟨V, q, i, isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map q), hq, hs⟩

/-- For `f : Y ⟶ Z` over `X` with representable structure morphisms, the square formed by the two
cartesian projections, `f` and the base-changed morphism `Y ×_X V ⟶ Z ×_X V`, is cartesian. -/
theorem isPullback_smallBaseChangeOverMap {X : AlgebraicSpaces B S hS} {Y Z : Over X}
    (f : Y ⟶ Z) (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) (V : SmallEtale B S hS X.1) :
    IsPullback (hY.fst V.obj.hom) (yoneda.map (smallBaseChangeOverMap B S hS f hY hZ V))
      f.left.hom (hZ.fst V.obj.hom) := by
  have hw : f.left.hom ≫ Z.hom.hom = Y.hom.hom :=
    congrArg (fun k : Y.left ⟶ X => k.hom) (Over.w f)
  refine IsPullback.of_bot ?_ (yoneda_map_smallBaseChangeOverMap_fst B S hS f hY hZ V).symm
    (hZ.isPullback V.obj.hom)
  rw [← yoneda.map_comp, smallBaseChangeOverMap_snd, hw]
  exact hY.isPullback V.obj.hom

/-- A morphism of affine schemes is `Spec` of its map on global sections, up to `isoSpec`. -/
private theorem eq_isoSpec_hom_comp_Spec_map_appTop {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) : f = X.isoSpec.hom ≫ Spec.map f.appTop ≫ Y.isoSpec.inv := by
  rw [← Category.assoc, Scheme.isoSpec_hom_naturality]
  simp

/-- The base change of a surjective étale morphism between algebraic spaces is étale and
surjective. -/
private theorem isEtale_and_isSurjective_fst_of_isPullback
    {T X V P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hX : IsAlgebraicSpace B S hS X)
    (hV : IsAlgebraicSpace B S hS V) (hP : IsAlgebraicSpace B S hS P)
    {g : T ⟶ X} {f : V ⟶ X} {fst : P ⟶ T} {snd : P ⟶ V} (sq : IsPullback fst snd g f)
    (hfe : IsEtale B S hS f) (hfs : IsSurjective B S hS f) :
    IsEtale B S hS fst ∧ IsSurjective B S hS fst := by
  refine ⟨isEtale_of_isPullback_of_isAlgebraicSpace B S hS sq hP hT hV hX hfe, fun x => ?_⟩
  obtain ⟨y, hy⟩ := hfs (pointsMap B S hS _ g x)
  obtain ⟨z, hz, -⟩ := exists_points_of_isPullback B S hS sq x y hy.symm
  exact ⟨z, hz⟩

/-- An algebraic space affine over `X` is finite over `X` as soon as its direct-image algebra is
finite over one affine surjective étale chart. -/
theorem isFinite_of_finite_algebraMap_chart {X : AlgebraicSpaces B S hS} (N' : AffineOver B S hS X)
    (V : SmallEtale B S hS X.1)
    (hVaff : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V))
    (haE : IsEtale B S hS V.obj.hom) (haS : IsSurjective B S hS V.obj.hom)
    (hfin' : RingHom.Finite ((pushforwardAlgebra B S hS N'.obj).algebraMap (op V))) :
    IsFinite B S hS N'.obj.hom.hom := by
  let F := BigFppfOver.toScheme B S hS
  have hrep' : yoneda.relativelyRepresentable N'.obj.hom.hom :=
    relativelyRepresentable_of_isAffineHom B S hS N'.obj.hom N'.property
  let N'V : BigFppfOver B S hS := hrep'.pullback V.obj.hom
  have hN'Vaff : IsAffine (F.obj N'V) :=
    isAffine_smallBaseChange_obj B S hS N'.obj.hom hrep' N'.property V hVaff
  have hUaff : IsAffine (F.obj V.obj.left) := hVaff
  let sndN' : N'V ⟶ V.obj.left := hrep'.snd V.obj.hom
  let e2 := pushforwardAlgebraSectionsIso B S hS (Over.mk N'.obj.hom) hrep' V
  have h3 : RingHom.Finite (e2.inv.hom.comp
      ((BigFppfOver.toScheme B S hS).map (hrep'.snd V.obj.hom)).appTop.hom) := by
    rwa [← pushforwardAlgebra_algebraMap_eq_comp B S hS N'.obj.hom hrep' V]
  have hfin : RingHom.Finite (F.map sndN').appTop.hom := by
    have h4 := (RingHom.Finite.of_surjective e2.hom.hom
      (ConcreteCategory.bijective_of_isIso e2.hom).2).comp h3
    have e3 : (F.map sndN').appTop.hom = (CommRingCat.Hom.hom e2.hom).comp
        ((CommRingCat.Hom.hom e2.inv).comp
          ((BigFppfOver.toScheme B S hS).map (hrep'.snd V.obj.hom)).appTop.hom) := by
      ext x
      exact (ConcreteCategory.congr_hom e2.inv_hom_id _).symm
    rwa [e3]
  have hsF : _root_.AlgebraicGeometry.IsFinite (F.map sndN') := by
    have h2 : _root_.AlgebraicGeometry.IsFinite (Spec.map (F.map sndN').appTop) :=
      (IsFinite.SpecMap_iff _).2 hfin
    rw [eq_isoSpec_hom_comp_Spec_map_appTop (F.map sndN')]
    infer_instance
  exact of_isPullback_of_isEtale_of_isSurjective B S hS (fun f => IsFinite B S hS f)
    (fun e k hk => isFinite_comp B S hS
      (isFinite_of_isClosedImmersion B S hS e.hom (isClosedImmersion_of_isIso B S hS e.hom)) hk)
    (hQ := isFinite_isLocalAtTarget_fppf.{u, u} B S hS) N'.obj.left.2 X.2
    (isAlgebraicSpace_yoneda B S hS _) (hrep'.isPullback V.obj.hom) haE haS
    (isFinite_yoneda_map_of_isFinite (p := sndN') hsF)

/-- A morphism over `X` of algebraic spaces affine over `X`, with integral source, is surjective
as soon as its map on functions over one affine surjective étale chart is injective. -/
theorem isSurjective_of_injective_appTop_chart {X : AlgebraicSpaces B S hS}
    (N N' : AffineOver B S hS X) (hN : IsIntegralHom B S hS N.obj.hom.hom) (h : N.obj ⟶ N'.obj)
    (V : SmallEtale B S hS X.1)
    (hVaff : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V))
    (haE : IsEtale B S hS V.obj.hom) (haS : IsSurjective B S hS V.obj.hom)
    (hrep : yoneda.relativelyRepresentable N.obj.hom.hom)
    (hrep' : yoneda.relativelyRepresentable N'.obj.hom.hom)
    (hinj : Function.Injective ((BigFppfOver.toScheme B S hS).map
      (smallBaseChangeOverMap B S hS h hrep hrep' V)).appTop.hom) :
    IsSurjective B S hS h.left.hom := by
  let F := BigFppfOver.toScheme B S hS
  let m := smallBaseChangeOverMap B S hS h hrep hrep' V
  have hNVaff : IsAffine (F.obj (hrep.pullback V.obj.hom)) :=
    isAffine_smallBaseChange_obj B S hS N.obj.hom hrep N.property V hVaff
  have hN'Vaff : IsAffine (F.obj (hrep'.pullback V.obj.hom)) :=
    isAffine_smallBaseChange_obj B S hS N'.obj.hom hrep' N'.property V hVaff
  have hUaff : IsAffine (F.obj V.obj.left) := hVaff
  obtain ⟨W, p, q, hpb, -, hp⟩ := hN V.1.left hVaff V.1.hom
  obtain ⟨e, he⟩ := exists_iso_comp_toScheme_map_snd B S hS N.obj.hom hrep V.1.hom p q hpb
  have hsnd : _root_.AlgebraicGeometry.IsIntegralHom (F.map (hrep.snd V.1.hom)) := by
    change _root_.AlgebraicGeometry.IsIntegralHom
      ((BigFppfOver.toScheme B S hS).map (hrep.snd V.1.hom))
    rw [he]
    infer_instance
  have happ : (F.map (hrep.snd V.1.hom)).appTop.hom.IsIntegral :=
    hsnd.isIntegral_app ⊤ (isAffineOpen_top _)
  have hcomp : (F.map (hrep.snd V.1.hom)).appTop =
      (F.map (hrep'.snd V.obj.hom)).appTop ≫ (F.map m).appTop := by
    rw [← Scheme.Hom.comp_appTop, ← F.map_comp, smallBaseChangeOverMap_snd]
  have hmint : (F.map m).appTop.hom.IsIntegral := by
    rw [hcomp, CommRingCat.hom_comp] at happ
    exact RingHom.IsIntegral.tower_top _ _ happ
  have hmsurj : Surjective (F.map m) := by
    have hS' : Surjective (Spec.map (F.map m).appTop) :=
      ⟨RingHom.IsIntegral.comap_surjective hmint hinj⟩
    rw [eq_isoSpec_hom_comp_Spec_map_appTop (F.map m)]
    infer_instance
  have hloc : MorphismProperty.IsLocalAtTarget
      ((fun (_ _ : AlgebraicSpaces B S hS) f => IsSurjective B S hS f.hom) :
        MorphismProperty (AlgebraicSpaces B S hS))
      (Topology.fppf.precoverage.{u, u} B S hS) :=
    (surjective_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
      (fppfPrecoverage_le_fpqcPrecoverage B S hS)
  obtain ⟨hfstN'e, hfstN's⟩ := isEtale_and_isSurjective_fst_of_isPullback B S hS N'.obj.left.2
    X.2 (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _)
    (hrep'.isPullback V.obj.hom) haE haS
  exact of_isPullback_of_isEtale_of_isSurjective B S hS (fun f => IsSurjective B S hS f)
    (fun e k hk => isSurjective_comp B S hS (isSurjective_of_isIso B S hS e.hom) hk)
    (hQ := hloc) N.obj.left.2 N'.obj.left.2 (isAlgebraicSpace_yoneda B S hS _)
    (isPullback_smallBaseChangeOverMap B S hS h hrep hrep' V) hfstN'e hfstN's
    (isSurjective_yoneda_map B S hS m hmsurj)

/-- Let `X` be a quasi-compact quasi-separated algebraic space, `N` an algebraic space integral
over `X`, and `w : W ⟶ N` an open immersion from a quasi-compact algebraic space locally of finite
type over `X`. Then there are an algebraic space `N'` finite over `X` and a surjective morphism
`h : N ⟶ N'` over `X` such that `w ≫ h` is an open immersion. -/
theorem exists_isFinite_isOpenImmersion_comp_of_isIntegralHom
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (N : AffineOver B S hS X) (hN : IsIntegralHom B S hS N.obj.hom.hom)
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (w : W ⟶ N.obj.left.1) (hw : IsOpenImmersion B S hS w)
    (hWqc : IsQuasiCompactSpace B S hS W)
    (hWlft : IsLocallyOfFiniteType B S hS (w ≫ N.obj.hom.hom)) :
    ∃ (N' : AffineOver B S hS X) (h : N.obj ⟶ N'.obj),
      IsFinite B S hS N'.obj.hom.hom ∧ IsOpenImmersion B S hS (w ≫ h.left.hom) ∧
        IsSurjective B S hS h.left.hom := by
  classical
  obtain ⟨U, a, hUaff, hasurj, haet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).mp hXqc
  let V : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk a, (isEtale_iff_presheaf_of_yoneda B S hS a).1 haet⟩
  have hVaff : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V) :=
    hUaff
  have haE : IsEtale B S hS a := haet
  have haS : IsSurjective B S hS a := isSurjective_of_presheafSurjective B S hS a hasurj
  let A := pushforwardAlgebra B S hS N.obj
  have hrep : yoneda.relativelyRepresentable N.obj.hom.hom :=
    relativelyRepresentable_of_isAffineHom B S hS N.obj.hom N.property
  have hAq : A.IsQuasicoherent :=
    isQuasicoherent_pushforwardAlgebra_of_qcqs B S hS N.obj.hom
      (isQuasiCompact_of_isAffineHom' B S hS N.obj.hom.hom N.obj.left.2 X.2 N.property)
      (isQuasiSeparated_of_isAffineHom B S hS N.obj.hom.hom N.obj.left.2 X.2 N.property)
  have hAint : A.IsIntegral := isIntegral_pushforwardAlgebra_of_isIntegralHom B S hS N.obj.hom hN
  have hAb : AlgebraSheaf.SectionsBelowCutoff B S hS A :=
    sectionsBelowCutoff_pushforwardAlgebra B S hS N.obj
  let F := BigFppfOver.toScheme B S hS
  let NV : BigFppfOver B S hS := hrep.pullback V.obj.hom
  have hNVaff : IsAffine (F.obj NV) :=
    isAffine_smallBaseChange_obj B S hS N.obj.hom hrep N.property V hVaff
  have hUaff' : IsAffine (F.obj U) := hUaff
  let fstN := hrep.fst V.obj.hom
  let sndN : NV ⟶ U := hrep.snd V.obj.hom
  let WV : BigFppfOver B S hS := hw.rep.pullback fstN
  let q : WV ⟶ NV := hw.rep.snd fstN
  have hq : _root_.AlgebraicGeometry.IsOpenImmersion (F.map q) :=
    hw.property fstN (hw.rep.fst fstN) q (hw.rep.isPullback fstN)
  have hsqW : IsPullback (hw.rep.fst fstN) (yoneda.map q) w fstN := hw.rep.isPullback fstN
  have hsqWX : IsPullback (hw.rep.fst fstN) (yoneda.map (q ≫ sndN)) (w ≫ N.obj.hom.hom) a := by
    rw [yoneda.map_comp]
    exact hsqW.paste_vert (hrep.isPullback V.obj.hom)
  have hWVlft : LocallyOfFiniteType (F.map (q ≫ sndN)) :=
    (isLocallyOfFiniteType_yoneda_map_iff B S hS _).1
      (IsLocallyOfFiniteType.of_isPullback B S hS hsqWX.flip hW X.2 hWlft)
  have hWVqc : CompactSpace (F.obj WV) := by
    have hP := isQuasiCompactSpace_pullback B S hS B.contains_terminal (w ≫ N.obj.hom.hom) a hW X.2
      hWqc (isQuasiCompactSpace_yoneda_obj B S hS (U := U) inferInstance) hXqs
    exact compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
      (IsQuasiCompactSpace.of_iso B S hS hP
        (hsqWX.isoPullback.symm : pullback (w ≫ N.obj.hom.hom) a ≅ yoneda.obj WV))
  have : LocallyOfFiniteType (F.map q ≫ F.map sndN) := by rw [← F.map_comp]; exact hWVlft
  obtain ⟨G, hG⟩ := exists_finset_isOpenImmersion_comp_of_isAffine (F.map sndN) (F.map q)
  let eV := pushforwardAlgebraSectionsIso B S hS N.obj hrep V
  obtain ⟨C, hC⟩ := exists_finiteSubalgebra_forall_mem B S hS X hXqc hXqs A hAq hAint hVaff
    (G.image eV.inv.hom)
  let A' : QuasicoherentAlgebra B S hS X :=
    ⟨(C.obj : AlgebraSheaf.{u, u} B S hS X.1 X.2), C.property.1⟩
  have hA'b : AlgebraSheaf.SectionsBelowCutoff B S hS A'.obj := fun V' =>
    lt_of_le_of_lt (Cardinal.mk_le_of_injective
      (AlgebraSheaf.injective_subobject_arrow_app C.obj (op V'))) (hAb V')
  obtain ⟨N', ⟨iso⟩⟩ : ∃ N' : AffineOver B S hS X,
      Nonempty (pushforwardAlgebra B S hS N'.obj ≅ A'.obj) :=
    ⟨_, ⟨pushforwardAlgebraBoundedRelativeSpecIso B S hS A' hA'b⟩⟩
  let φ : pushforwardAlgebra B S hS N'.obj ⟶ A := iso.hom ≫ C.obj.arrow
  obtain ⟨h, hh⟩ := exists_pushforwardAlgebraMap_eq B S hS N N' φ
  have hrep' : yoneda.relativelyRepresentable N'.obj.hom.hom :=
    relativelyRepresentable_of_isAffineHom B S hS N'.obj.hom N'.property
  let N'V : BigFppfOver B S hS := hrep'.pullback V.obj.hom
  have hN'Vaff : IsAffine (F.obj N'V) :=
    isAffine_smallBaseChange_obj B S hS N'.obj.hom hrep' N'.property V hVaff
  let m : NV ⟶ N'V := smallBaseChangeOverMap B S hS h hrep hrep' V
  let eV' := pushforwardAlgebraSectionsIso B S hS N'.obj hrep' V
  have happ : (F.map m).appTop = eV'.inv ≫ φ.right.hom.app (op V) ≫ eV.hom := by
    rw [← pushforwardRingMap_app_eq B S hS h hrep hrep' V, ← pushforwardAlgebraMap_right, hh]
  have hφapp : φ.right.hom.app (op V) =
      iso.hom.right.hom.app (op V) ≫ C.obj.arrow.right.hom.app (op V) := rfl
  have hpt : ∀ x, (F.map m).appTop x =
      eV.hom (C.obj.arrow.right.hom.app (op V) (iso.hom.right.hom.app (op V) (eV'.inv x))) := by
    intro x
    rw [happ, hφapp]
    rfl
  have hio1 : ∀ z, iso.inv.right.hom.app (op V) (iso.hom.right.hom.app (op V) z) = z := fun z => by
    change ((iso.hom ≫ iso.inv).right.hom.app (op V)) z = z
    rw [iso.hom_inv_id]
    rfl
  have hio2 : ∀ z, iso.hom.right.hom.app (op V) (iso.inv.right.hom.app (op V) z) = z := fun z => by
    change ((iso.inv ≫ iso.hom).right.hom.app (op V)) z = z
    rw [iso.inv_hom_id]
    rfl
  have hinj : Function.Injective (F.map m).appTop.hom := by
    intro x y hxy
    change (F.map m).appTop x = (F.map m).appTop y at hxy
    rw [hpt, hpt] at hxy
    have h1 := (ConcreteCategory.bijective_of_isIso eV.hom).1 hxy
    have h2 := AlgebraSheaf.injective_subobject_arrow_app C.obj (op V) h1
    have h3 : eV'.inv x = eV'.inv y := by
      have := congrArg (iso.inv.right.hom.app (op V)) h2
      rwa [hio1, hio1] at this
    exact (ConcreteCategory.bijective_of_isIso eV'.inv).1 h3
  have hrange : (G : Set Γ(F.obj NV, ⊤)) ⊆ Set.range (F.map m).appTop.hom := by
    intro g hg
    obtain ⟨c, hc⟩ := hC (eV.inv g) (Finset.mem_image_of_mem _ hg)
    refine ⟨eV'.hom (iso.inv.right.hom.app (op V) c), ?_⟩
    change (F.map m).appTop (eV'.hom (iso.inv.right.hom.app (op V) c)) = g
    refine (hpt _).trans ?_
    rw [Iso.hom_inv_id_apply, hio2, hc]
    exact ConcreteCategory.congr_hom eV.inv_hom_id g
  let sndN' : N'V ⟶ U := hrep'.snd V.obj.hom
  let fstN' := hrep'.fst V.obj.hom
  have hsndm : m ≫ sndN' = sndN := smallBaseChangeOverMap_snd B S hS h hrep hrep' V
  have hsq2 := isPullback_smallBaseChangeOverMap B S hS h hrep hrep' V
  obtain ⟨hfstN'e, hfstN's⟩ := isEtale_and_isSurjective_fst_of_isPullback B S hS N'.obj.left.2
    X.2 (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _)
    (hrep'.isPullback V.obj.hom) haE haS
  refine ⟨N', h, ?_, ?_, ?_⟩
  · refine isFinite_of_finite_algebraMap_chart B S hS N' V hVaff haE haS ?_
    have e1 : (pushforwardAlgebra B S hS N'.obj).algebraMap (op V) =
        (iso.inv.right.hom.app (op V)).hom.comp (A'.obj.algebraMap (op V)) :=
      RingHom.ext fun r => (iso.inv.comm (op V) r).symm
    rw [e1]
    exact (RingHom.Finite.of_surjective _ fun z => ⟨iso.hom.right.hom.app (op V) z, hio1 z⟩).comp
      (C.property.2 V hVaff)
  · have hopen : _root_.AlgebraicGeometry.IsOpenImmersion (F.map q ≫ F.map m) :=
      hG (F.map m) (F.map sndN') (by rw [← F.map_comp, hsndm]) hinj hrange
    rw [← F.map_comp] at hopen
    have hsqA : IsPullback (hw.rep.fst fstN) (yoneda.map (q ≫ m)) (w ≫ h.left.hom) fstN' := by
      rw [yoneda.map_comp]
      exact hsqW.paste_vert hsq2
    have := openImmersion_isLocalAtTarget_fppf.{u, u} B S hS
    exact of_isPullback_of_isEtale_of_isSurjective B S hS (fun f => IsOpenImmersion B S hS f)
      (fun e k hk => isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS e.hom) hk)
      hW N'.obj.left.2 (isAlgebraicSpace_yoneda B S hS _) hsqA hfstN'e hfstN's
      (isOpenImmersion_yoneda_map B S hS _ hopen)
  · exact isSurjective_of_injective_appTop_chart B S hS N N' hN h V hVaff haE haS hrep hrep' hinj

end AlgebraicGeometry.Space

end
