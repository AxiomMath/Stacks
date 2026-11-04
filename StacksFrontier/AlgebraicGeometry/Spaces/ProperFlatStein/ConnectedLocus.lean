module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStein.SectionsHomologyIdempotent
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStein.FibreBettiNumbers
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStein.Core
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStein.FibreConnectedComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricComponentCount
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Quot.StructureSheafMapIsoBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsFibreProductResidueIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.FieldFiber
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenSubsetsOfStructureMapIso
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSheafDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat

/-!
# The locus where the geometric fibres are connected is open

Let `g : P ⟶ h_U` be a proper, flat, finitely presented morphism of algebraic spaces with
geometrically reduced fibres.  The set of points of `h_U` over which the geometric fibre of `g` is
connected — where the number of geometric connected components of Stacks 0E1B is one — is open.
This is the part of Stacks 0E1E that the proof of Stacks 0E0D uses.

The argument is through the degree-zero Betti numbers `b(y) = dim_{κ(y)} H⁰(X_y, 𝒪)`, whose
properties used here are taken as inputs
(`AlgebraicGeometry.Space.ProperFlatStein.FibreBettiBaseChangeInput`,
`AlgebraicGeometry.Space.ProperFlatStein.UpperSemicontinuousFibreBettiInput` and
`AlgebraicGeometry.Space.ProperFlatStein.StructureSharpOfGeometricFibresInput`):

* where the geometric fibre is connected, it is connected and reduced at every geometric point of
  the fibre over `κ(y)`, so Stacks 0E0S makes `𝒪 ⟶ q_* 𝒪` invertible there and `b(y) = 1`;
* `b` is upper semicontinuous (Stacks 0E0R), so `b ≤ 1` near such a point, and the image of `g` is
  open (Stacks 042S);
* where `b ≤ 1` and the fibre is nonempty, the fibre over a geometric point is connected: its
  Betti number is `b` again (Stacks 0E0R, part (1)), so its idempotent global functions are
  `0` and `1`, by
  `AlgebraicGeometry.Space.ProperFlatStein.isIdempotentElem_eq_zero_or_one_of_finrank_le_one`.

## Main results

* `AlgebraicGeometry.Space.ProperFlatStein.fibreBettiFunction_structureModule_eq_one`: `b = 1`
  where the geometric fibre is connected.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space.ProperFlatStein

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Compare

variable {P Y Y' : AlgebraicSpaces B S hS} (g : P ⟶ Y) (h : Y' ⟶ Y)

/-- The fibre product of algebraic spaces, read as a presheaf, is the fibre product of
presheaves. -/
def pullbackObjIso : (pullback g h).obj ≅ pullback g.hom h.hom :=
  PreservesPullback.iso (ObjectProperty.ι _) g h

/-- The comparison `pullbackObjIso` followed by the second projection of the fibre product of
presheaves is the second projection of the fibre product of algebraic spaces. -/
theorem pullbackObjIso_hom_snd :
    (pullbackObjIso g h).hom ≫ pullback.snd g.hom h.hom = (pullback.snd g h).hom :=
  PreservesPullback.iso_hom_snd (ObjectProperty.ι _) g h

/-- The comparison `pullbackObjIso` followed by the first projection of the fibre product of
presheaves is the first projection of the fibre product of algebraic spaces. -/
theorem pullbackObjIso_hom_fst :
    (pullbackObjIso g h).hom ≫ pullback.fst g.hom h.hom = (pullback.fst g h).hom :=
  PreservesPullback.iso_hom_fst (ObjectProperty.ι _) g h

/-- The fibre product of presheaves of two morphisms of algebraic spaces, as an algebraic
space. -/
abbrev presheafPullback : AlgebraicSpaces B S hS :=
  ⟨pullback g.hom h.hom, isAlgebraicSpace_pullback B S hS g.hom h.hom P.2 Y'.2 Y.2⟩

/-- The comparison isomorphism of algebraic spaces between the two fibre products. -/
def pullbackPresheafIso : pullback g h ≅ presheafPullback g h :=
  (ObjectProperty.fullyFaithfulι _).preimageIso (pullbackObjIso g h)

/-- The comparison `pullbackPresheafIso` followed by the second projection of
`presheafPullback` is the second projection of the fibre product of algebraic spaces. -/
theorem pullbackPresheafIso_hom_snd :
    (pullbackPresheafIso g h).hom ≫ ObjectProperty.homMk (pullback.snd g.hom h.hom) =
      pullback.snd g h := by
  ext1
  exact pullbackObjIso_hom_snd g h

/-- The comparison `pullbackPresheafIso` followed by the first projection of
`presheafPullback` is the first projection of the fibre product of algebraic spaces. -/
theorem pullbackPresheafIso_hom_fst :
    (pullbackPresheafIso g h).hom ≫ ObjectProperty.homMk (pullback.fst g.hom h.hom) =
      pullback.fst g h := by
  ext1
  exact pullbackObjIso_hom_fst g h

/-- The square of the fibre product of presheaves, read in algebraic spaces, is cartesian. -/
theorem isPullback_presheafPullback :
    IsPullback (ObjectProperty.homMk (pullback.fst g.hom h.hom) :
        presheafPullback g h ⟶ P) (ObjectProperty.homMk (pullback.snd g.hom h.hom)) g h :=
  (IsPullback.of_hasPullback g h).of_iso (pullbackPresheafIso g h) (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (by rw [Iso.refl_hom, Category.comp_id, pullbackPresheafIso_hom_fst])
    (by rw [Iso.refl_hom, Category.comp_id, pullbackPresheafIso_hom_snd])
    (by simp) (by simp)

end Compare

section BettiOne

variable {U : BigFppfOver B S hS} {P : AlgebraicSpaces B S hS}
  (g : P ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)

/-- Every point of the spectrum of the residue field at `y` lies over `y`. -/
theorem pointsMap_residueFieldSiteHom (z : points B S hS (yoneda.obj U))
    (w : points B S hS (yoneda.obj (residueFieldSiteObj B S hS U (pointsToScheme B S hS U z)))) :
    pointsMap B S hS _ (yoneda.map (residueFieldSiteHom B S hS U (pointsToScheme B S hS U z))) w =
      z := by
  apply injective_pointsToScheme B S hS U
  rw [pointsToScheme_pointsMap_yoneda]
  exact Scheme.fromSpecResidueField_apply _ _

/-- The second projection of a fibre product of algebraic spaces is proper if `g` is. -/
private theorem isProper_pullback_snd {P Y Y' : AlgebraicSpaces B S hS} {g : P ⟶ Y} (h : Y' ⟶ Y)
    (hg : IsProper B S hS g.hom) : IsProper B S hS (pullback.snd g h).hom :=
  (isProper_isStableUnderBaseChange B S hS).of_isPullback (IsPullback.of_hasPullback g h) hg

/-- **`b(y) = 1` where the geometric fibre is connected.**  Let `g : P ⟶ h_U` be proper, flat
and of finite presentation with geometrically reduced fibres, and let `z` be a point of `h_U`
over which the geometric fibre of `g` is connected.  Then the degree-zero Betti number `b` is
one at the underlying point `y` of `U`: the fibre over `Spec κ(y)` has connected and reduced
geometric fibres, so its structure map is invertible by Stacks 0E0S, and `H⁰ = κ(y)`. -/
theorem fibreBettiFunction_structureModule_eq_one
    (h0E0S : StructureSharpOfGeometricFibresInput B S hS)
    (hg : IsProper B S hS g.hom) (hfl : IsFlat B S hS g.hom)
    (hfp : IsFinitePresentation B S hS g.hom)
    (hred : ∀ z, IsGeometricallyReducedFibreAt B S hS g.hom P.2
      (isAlgebraicSpace_yoneda B S hS U) z)
    (z : points B S hS (yoneda.obj U))
    (hz : numberGeometricConnectedComponents B S hS g.hom z = 1) :
    fibreBettiFunction g (structureModule P) 0 (pointsToScheme B S hS U z) = 1 := by
  set y := pointsToScheme B S hS U z
  let T := residueFieldSiteObj B S hS U y
  let t := residueFieldSiteHom B S hS U y
  have hU := isAlgebraicSpace_yoneda B S hS U
  have hT := isAlgebraicSpace_yoneda B S hS T
  have hQ' := isAlgebraicSpace_pullback B S hS g.hom (yoneda.map t) P.2 hT hU
  let q' : presheafPullback g (representedSpaceMap B S hS t) ⟶ ⟨yoneda.obj T, hT⟩ :=
    ObjectProperty.homMk (pullback.snd g.hom (yoneda.map t))
  have sq := isPullback_presheafPullback g (representedSpaceMap B S hS t)
  have hq'p : IsProper B S hS q'.hom :=
    (isProper_isStableUnderBaseChange B S hS).of_isPullback sq hg
  have hq'fl : IsFlat B S hS q'.hom := (isFlat_isStableUnderBaseChange B S hS).of_isPullback sq hfl
  have hq'fp : IsFinitePresentation B S hS q'.hom :=
    (isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hfp
  have hred' : ∀ w : GeometricPoint B S hS (yoneda.obj T),
      HasEtaleLocalProperty B (Spec (.of w.1.carrier)) w.1.contained
        (fibreOverFieldValuedPoint B S hS q'.hom w.1)
        (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced V) := fun w => by
    have hw : IsGeometricallyReducedFibreAt B S hS (pullback.snd g.hom (yoneda.map t)) hQ' hT
        w.image := by
      show w.image ∈ geometricallyReducedFibreLocus B S hS _ _ _
      rw [geometricallyReducedFibreLocus_pullback B S hS g.hom (yoneda.map t) P.2 hU hT]
      exact hred _
    exact (isGeometricallyReducedFibreAt_iff_forall_isReduced B S hS _ hQ' hT w.image).1 hw w.1
      rfl
  have hconn' : ∀ w : GeometricPoint B S hS (yoneda.obj T),
      ConnectedPoints B (Spec (.of w.1.carrier)) w.1.contained
        (fibreOverFieldValuedPoint B S hS q'.hom w.1) := fun w => by
    refine (connectedPoints_fibreOverFieldValuedPoint_iff B S hS hQ' hT q'.hom w.1).2 ?_
    refine connectedPullback_of_numberGeometricConnectedComponents_eq_one B S hS hQ' hT q'.hom w ?_
    show numberGeometricConnectedComponents B S hS (pullback.snd g.hom (yoneda.map t)) w.image = 1
    rw [numberGeometricConnectedComponents_baseChange B S hS P.2 hU hT g.hom (yoneda.map t),
      Function.comp_apply, pointsMap_residueFieldSiteHom]
    exact hz
  have hq' : IsIso (structureSharp B S hS q') := (h0E0S q' hq'p hq'fl hq'fp hred' hconn').1
  have hq : IsIso (structureSharp B S hS (pullback.snd g (representedSpaceMap B S hS t))) := by
    rw [← pullbackPresheafIso_hom_snd g (representedSpaceMap B S hS t)]
    exact (isIso_structureSharp_comp_iff _ _).2 hq'
  have hqp := isProper_pullback_snd (representedSpaceMap B S hS t) hg
  have : Nontrivial Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
    (isField_residueFieldSiteObj U y).nontrivial
  exact finrank_baseChangeSectionsHomology_zero_eq_one B S hS g t hqp.2.1.2
    (isQuasiSeparated_of_isSeparated B S hS hqp.1)

end BettiOne

section BettiAtMostOne

variable {U : BigFppfOver B S hS} {P : AlgebraicSpaces B S hS}
  (g : P ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)

/-- No point lies in the basic open of the zero function. -/
theorem notMem_basicOpen_of_eq_zero (X : Scheme.{u}) (f : Γ(X, ⊤)) (hf : f = 0) (x : X) :
    x ∉ X.basicOpen f := by
  subst hf
  rw [Scheme.basicOpen_zero]
  exact fun h => h

/-- Every point lies in the basic open of the unit function. -/
theorem mem_basicOpen_of_eq_one (X : Scheme.{u}) (f : Γ(X, ⊤)) (hf : f = 1) (x : X) :
    x ∈ X.basicOpen f := by
  subst hf
  rw [Scheme.basicOpen_one]
  trivial

/-- The support of a global function vanishing on every chart is empty. -/
theorem sectionSupport_eq_empty_of_val_eq_zero {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : globalFunctions B S hS F) (he : ∀ V, e.val V = 0) : sectionSupport B S hS F e = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨V, p, hp, -⟩
  exact notMem_basicOpen_of_eq_zero _ _ (he (op V)) _ hp

/-- The support of a global function equal to one on every chart of an algebraic space is
everything. -/
theorem sectionSupport_eq_univ_of_val_eq_one {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (e : globalFunctions B S hS F) (he : ∀ V, e.val V = 1) :
    sectionSupport B S hS F e = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨V, p, hp⟩ := exists_chart_point B S hS F hF x
  exact ⟨V, p, mem_basicOpen_of_eq_one _ _ (he (op V)) _, hp⟩

/-- An algebraic space whose idempotent global functions are `0` and `1` and whose point space is
nonempty has connected point space. -/
theorem connectedPoints_of_isIdempotentElem {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) [Nonempty (points B S hS F)]
    (h : ∀ e : globalFunctions B S hS F, IsIdempotentElem e →
      (∀ V, e.val V = 0) ∨ (∀ V, e.val V = 1)) :
    ConnectedPoints B S hS F := by
  let := pointTopology B S hS F
  have hpre : PreconnectedSpace (points B S hS F) := by
    refine preconnectedSpace_iff_clopen.2 fun C hC => ?_
    obtain ⟨e, he, hsupp⟩ := exists_isIdempotentElem_sectionSupport_eq B S hS F hF C hC
    rw [← hsupp]
    exact (h e he).imp (sectionSupport_eq_empty_of_val_eq_zero e)
      (sectionSupport_eq_univ_of_val_eq_one hF e)
  exact { toPreconnectedSpace := hpre, toNonempty := inferInstance }

/-- The inverse Yoneda image of the value of a geometric point is the Yoneda image of that
value. -/
private theorem yonedaEquiv_symm_value_eq_yoneda_map (p : GeometricPoint B S hS (yoneda.obj U)) :
    yonedaEquiv.symm p.val.value = yoneda.map p.val.value := by
  rw [Equiv.symm_apply_eq]
  exact (yonedaEquiv_yoneda_map _).symm

/-- Every point of the spectrum of the field of a geometric point `p` of `h_U` maps to the point
of `h_U` represented by `p`. -/
private theorem pointsMap_yonedaEquiv_symm_value_aux (p : GeometricPoint B S hS (yoneda.obj U))
    (w : points B S hS (yoneda.obj p.val.siteObject)) :
    pointsMap B S hS _ (yonedaEquiv.symm p.val.value) w = p.image := by
  rw [yonedaEquiv_symm_value_eq_yoneda_map]
  apply injective_pointsToScheme B S hS U
  rw [pointsToScheme_pointsMap_yoneda]
  exact (pointsToScheme_class_eq B S hS U p.val _).symm

/-- Base changing the fibre product `P ×_{h_U} h_{U'}` further along an isomorphism
`t' : T' ⟶ U'` gives, as a presheaf, the fibre product of presheaves of `g` and `h_t`. -/
private def pullbackPullbackSndObjIso {U' T' : BigFppfOver B S hS} (t : U' ⟶ U) (t' : T' ⟶ U')
    [IsIso t'] :
    (pullback (pullback.snd g (representedSpaceMap B S hS t))
        (representedSpaceMap B S hS t')).obj ≅ pullback g.hom (yoneda.map t) :=
  let E : (pullback g (representedSpaceMap B S hS t)).obj ≅ pullback g.hom (yoneda.map t) :=
    pullbackObjIso g (representedSpaceMap B S hS t)
  have hE : E.hom ≫ pullback.snd g.hom (yoneda.map t) =
      (pullback.snd g (representedSpaceMap B S hS t)).hom :=
    pullbackObjIso_hom_snd g (representedSpaceMap B S hS t)
  pullbackObjIso _ (representedSpaceMap B S hS t') ≪≫
    @asIso _ _ _ _ (pullback.map (pullback.snd g (representedSpaceMap B S hS t)).hom
      (yoneda.map t') (pullback.snd g.hom (yoneda.map t)) (yoneda.map t') E.hom (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, hE]) (by simp))
      (pullback.map_isIso _ _ _ _ _ _ _ _ _) ≪≫
    pullbackLeftPullbackSndIso g.hom (yoneda.map t) (yoneda.map t') ≪≫
    asIso (pullback.map g.hom (yoneda.map t' ≫ yoneda.map t) g.hom (yoneda.map t) (𝟙 _)
      (yoneda.map t') (𝟙 _) (by simp) (by simp))

/-- **The geometric fibre is connected where `b ≤ 1`.**  Let `g : P ⟶ h_U` be proper and of finite
presentation with `𝒪_P` flat over `h_U`, and let `z` be a point in the image of `g` at which the
degree-zero Betti number `b` is at most one.  Then the geometric fibre of `g` at `z` is
connected.  Over a geometric point `p` of `z` the Betti number is the same (Stacks 0E0R, part
(1)); there, the fibre over the residue field of the spectrum of the algebraically closed
field of `p` is the geometric fibre itself, and its idempotent global functions are `0` and `1`
(`AlgebraicGeometry.Space.ProperFlatStein.isIdempotentElem_eq_zero_or_one_of_finrank_le_one`). -/
theorem numberGeometricConnectedComponents_eq_one_of_fibreBettiFunction_le_one
    (hBC : FibreBettiBaseChangeInput B S hS)
    (hg : IsProper B S hS g.hom) (hfp : IsFinitePresentation B S hS g.hom)
    (hFflat : IsFlatOver B S hS P.2 g.hom (structureModule P))
    (z : points B S hS (yoneda.obj U)) (hz : z ∈ Set.range (pointsMap B S hS P.1 g.hom))
    (hb : fibreBettiFunction g (structureModule P) 0 (pointsToScheme B S hS U z) ≤ 1) :
    numberGeometricConnectedComponents B S hS g.hom z = 1 := by
  obtain ⟨p, rfl⟩ := exists_geometricRepresentative B S hS (yoneda.obj U) z
  let U' := p.val.siteObject
  let t : U' ⟶ U := p.val.value
  let g' := pullback.snd g (representedSpaceMap B S hS t)
  let F' := (modulePullback B S hS (pullback.fst g (representedSpaceMap B S hS t))).obj
    (structureModule P)
  have hbc := hBC g hg hfp (structureModule P)
    (SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite' _
      SheafOfModules.isFinitePresentationOnSite_unit) hFflat t 0
  let pt : (BigFppfOver.toScheme B S hS).obj U' := IsLocalRing.closedPoint p.val.carrier
  have hpt : ((BigFppfOver.toScheme B S hS).map t) pt = pointsToScheme B S hS U p.image :=
    (pointsToScheme_class_eq B S hS U p.val pt).symm
  have hb' : fibreBettiFunction g' F' 0 pt ≤ 1 := by rwa [hbc, Function.comp_apply, hpt]
  -- the fibre over the residue field of `Spec k`
  let T' := residueFieldSiteObj B S hS U' pt
  let t' := residueFieldSiteHom B S hS U' pt
  let Q := pullback g' (representedSpaceMap B S hS t')
  let q := pullback.snd g' (representedSpaceMap B S hS t')
  have hK : IsField Γ((BigFppfOver.toScheme B S hS).obj T', ⊤) := isField_residueFieldSiteObj U' pt
  let : Field Γ((BigFppfOver.toScheme B S hS).obj T', ⊤) := hK.toField
  have hqp : IsProper B S hS q.hom :=
    isProper_pullback_snd _ (isProper_pullback_snd (representedSpaceMap B S hS t) hg)
  let eF : (modulePullback B S hS (pullback.fst g' (representedSpaceMap B S hS t'))).obj F' ≅
      structureModule Q :=
    (modulePullback B S hS (pullback.fst g' (representedSpaceMap B S hS t'))).mapIso
        (modulePullbackUnitIso B S hS (pullback.fst g (representedSpaceMap B S hS t))) ≪≫
      modulePullbackUnitIso B S hS (pullback.fst g' (representedSpaceMap B S hS t'))
  have hidem := isIdempotentElem_eq_zero_or_one_of_finrank_le_one B S hS q hK hqp _ eF hb'
  -- the fibre over the residue field is the fibre over `p`
  have ht' : IsIso t' := by
    have : IsIso ((BigFppfOver.toScheme B S hS).map t') :=
      isIso_fromSpecResidueField_of_field p.val.carrier pt
    exact isIso_of_reflects_iso t' (BigFppfOver.toScheme B S hS)
  let eQ : Q.obj ≅ pullback g.hom (yonedaEquiv.symm p.val.value) :=
    pullbackPullbackSndObjIso g t t' ≪≫ eqToIso (by rw [yonedaEquiv_symm_value_eq_yoneda_map])
  -- the fibre over `p` is nonempty
  obtain ⟨x, hx⟩ := hz
  obtain ⟨w, -⟩ := surjective_pointsToScheme B S hS U' pt
  have hxw : pointsMap B S hS P.1 g.hom x =
      pointsMap B S hS (yoneda.obj U') (yonedaEquiv.symm p.val.value) w :=
    hx.trans (pointsMap_yonedaEquiv_symm_value_aux p w).symm
  obtain ⟨y₀, -⟩ := exists_points_of_isPullback B S hS
    (IsPullback.of_hasPullback g.hom (yonedaEquiv.symm p.val.value)) x w hxw
  have : Nonempty (points B S hS Q.obj) := ⟨(pointsHomeomorphOfIso B S hS eQ).symm y₀⟩
  have hQconn : ConnectedPoints B S hS Q.obj :=
    connectedPoints_of_isIdempotentElem Q.2 fun e he =>
      (hidem e he).imp (fun h V => congrArg (fun s => s.val V) h)
        (fun h V => congrArg (fun s => s.val V) h)
  have hfib : ConnectedPullback B S hS g.hom (yonedaEquiv.symm p.val.value) :=
    (pointsHomeomorphOfIso B S hS eQ).connectedSpace_iff.mp hQconn
  rw [numberGeometricConnectedComponents_eq B S hS P.2 (isAlgebraicSpace_yoneda B S hS U)
    g.hom p]
  show Cardinal.toENat (Cardinal.mk (ConnectedComponents
    (points B S hS (pullback g.hom (yonedaEquiv.symm p.val.value))))) = 1
  have := hfib
  rw [Cardinal.mk_eq_one, map_one]

end BettiAtMostOne

section Open

variable {U : BigFppfOver B S hS} {P : AlgebraicSpaces B S hS}
  (g : P ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)

/-- Every point of the spectrum of the field of a geometric point `p` of `h_U` maps to the point
of `h_U` represented by `p`. -/
theorem pointsMap_yonedaEquiv_symm_value (p : GeometricPoint B S hS (yoneda.obj U))
    (w : points B S hS (yoneda.obj p.val.siteObject)) :
    pointsMap B S hS _ (yonedaEquiv.symm p.val.value) w = p.image :=
  pointsMap_yonedaEquiv_symm_value_aux p w

/-- A point at which the number of geometric connected components is one is in the image. -/
theorem mem_range_of_numberGeometricConnectedComponents_eq_one (z : points B S hS (yoneda.obj U))
    (hz : numberGeometricConnectedComponents B S hS g.hom z = 1) :
    z ∈ Set.range (pointsMap B S hS P.1 g.hom) := by
  obtain ⟨p, rfl⟩ := exists_geometricRepresentative B S hS (yoneda.obj U) z
  have hc := connectedPullback_of_numberGeometricConnectedComponents_eq_one B S hS P.2
    (isAlgebraicSpace_yoneda B S hS U) g.hom p hz
  obtain ⟨w⟩ := hc.toNonempty
  refine ⟨pointsMap B S hS _ (pullback.fst g.hom (yonedaEquiv.symm p.val.value)) w, ?_⟩
  rw [← pointsMap_comp_apply, pullback.condition, pointsMap_comp_apply,
    pointsMap_yonedaEquiv_symm_value]

/-- **The locus where the geometric fibre is connected is open.**  For `g : P ⟶ h_U` proper,
flat and of finite presentation with geometrically reduced fibres, the set of points of `h_U`
over which the geometric fibre of `g` is connected is open, granted the three results on Betti
numbers stated as `AlgebraicGeometry.Space.ProperFlatStein.FibreBettiBaseChangeInput`,
`AlgebraicGeometry.Space.ProperFlatStein.UpperSemicontinuousFibreBettiInput` and
`AlgebraicGeometry.Space.ProperFlatStein.StructureSharpOfGeometricFibresInput`. -/
theorem isOpen_setOf_numberGeometricConnectedComponents_eq_one
    (hBC : FibreBettiBaseChangeInput B S hS) (hUSC : UpperSemicontinuousFibreBettiInput B S hS)
    (h0E0S : StructureSharpOfGeometricFibresInput B S hS)
    (hg : IsProper B S hS g.hom) (hfl : IsFlat B S hS g.hom)
    (hfp : IsFinitePresentation B S hS g.hom)
    (hred : ∀ z, IsGeometricallyReducedFibreAt B S hS g.hom P.2
      (isAlgebraicSpace_yoneda B S hS U) z) :
    IsOpen {z : points B S hS (yoneda.obj U) |
      numberGeometricConnectedComponents B S hS g.hom z = 1} := by
  have hU := isAlgebraicSpace_yoneda B S hS U
  have hFfp : (structureModule P).IsFinitePresentation :=
    SheafOfModules.isFinitePresentation_of_isFinitePresentationOnSite' _
      SheafOfModules.isFinitePresentationOnSite_unit
  have hFflat : IsFlatOver B S hS P.2 g.hom (structureModule P) := by
    have : (structureModule P).IsQuasicoherentOnSite := SheafOfModules.isQuasicoherentOnSite_unit _
    exact (isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS g (structureModule P)).2
      ((isFlat_iff_forall_isFlatOverAtGeometricPoint_structureSheafModule B S hS g).1 hfl)
  have husc := hUSC g hg hfp (structureModule P) hFfp hFflat 0
  have hopen : IsOpen (Set.range (pointsMap B S hS P.1 g.hom)) :=
    (isOpen_of_universallyOpen B S hS hU g.hom
      (universallyOpen_of_isFlat_of_isLocallyOfFinitePresentation B S hS P.2 hU g.hom hfl
        hfp.1)).isOpen_range
  let e := schemePointsHomeomorph B S hS U
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  have hb := fibreBettiFunction_structureModule_eq_one g h0E0S hg hfl hfp hred z hz
  have hev : ∀ᶠ y in nhds (e z), fibreBettiFunction g (structureModule P) 0 y < 2 :=
    husc (e z) 2 (by
      show fibreBettiFunction g (structureModule P) 0 (pointsToScheme B S hS U z) < 2
      rw [hb]
      norm_num)
  filter_upwards [e.continuous.continuousAt.eventually hev,
    hopen.mem_nhds (mem_range_of_numberGeometricConnectedComponents_eq_one
      g z hz)] with z' hz'b hz'r
  exact numberGeometricConnectedComponents_eq_one_of_fibreBettiFunction_le_one g hBC hg hfp hFflat
    z' hz'r (Nat.lt_succ_iff.mp hz'b)

end Open

end AlgebraicGeometry.Space.ProperFlatStein
