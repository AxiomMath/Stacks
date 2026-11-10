module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.CohenMacaulayDualizingComplex
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.CostructuredArrowTerminalPullback
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyTotalScheme
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesCohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Invariance
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackEquivalenceOfIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackCompositionCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenLiftOverHenselianPair
public import StacksFrontier.AlgebraicGeometry.Stacks.ParasiticLisseEtaleVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResidueFibreCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedRightAdjointDuality
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplexBaseChange

/-!
# The derived fibres of the relative dualizing complex of a family of curves

Let `X ⟶ S` be a family of curves which is Cohen–Macaulay of relative dimension one and
`(ω^•_{X/S}, τ)` a relative dualizing complex. The derived pullback of `ω^•_{X/S}` to the fibre
over any point of `S` has cohomology sheaves only in degree `-1`.

## Main results

* `AlgebraicGeometry.Space.representedDualityDerivedStructureSheafIso`: the equivalence
  `D_QCoh(𝒪_{X_0}) ≌ D_QCoh(𝒪_X)` carries `𝒪_{X_0}` to `𝒪_X`.
* `AlgebraicGeometry.Space.isZero_homology_quasicoherentDerivedRightAdjoint_representedSpaceMap`:
  for a represented morphism of quasi-compact quasi-separated schemes, the cohomology of `a(𝒪)`
  vanishes in every degree where that of the twisted inverse image of the morphism of schemes does.
* `AlgebraicGeometry.Space.homologyRepresentedDualityQuasicoherentDerivedEquivalenceFunctorObjIso`
  and `AlgebraicGeometry.Space.homologyQuasicoherentDerivedRightAdjointRepresentedSpaceMapIso`:
  the corresponding cohomology sheaves are the pullbacks of those on the scheme.
* `AlgebraicGeometry.CurveFamily.isZero_homology_relativeDualizingComplex_of_base_eq`: a relative
  dualizing complex of a Cohen–Macaulay curve over a field has cohomology only in degree `-1`.
* `AlgebraicGeometry.CurveFamily.isZero_homology_smallEtaleDerivedModulePullback_pullbackFst` and
  `AlgebraicGeometry.CurveFamily.isZero_homology_smallEtaleDerivedModulePullback_residueFibreι`:
  the derived pullbacks of a relative dualizing complex along the spectra of fields mapping to
  the base, and to the fibres over the points of the base, have cohomology only in degree `-1`.

## References

* [Stacks Project, Tag 0E6P](https://stacks.math.columbia.edu/tag/0E6P)
* [Stacks Project, Tag 0E6C](https://stacks.math.columbia.edu/tag/0E6C)
* [Stacks Project, Tag 0E6E](https://stacks.math.columbia.edu/tag/0E6E)
* [Stacks Project, Tag 0BS3](https://stacks.math.columbia.edu/tag/0BS3)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  SheafOfModules.instAbelian

section

attribute [local instance 10000] HasDerivedCategory.standard

/-- The equivalence `D_QCoh(𝒪_{X_0}) ≌ D_QCoh(𝒪_X)` carries the structure sheaf `𝒪_{X_0}` in
degree zero to the structure sheaf `𝒪_X` in degree zero. -/
def representedDualityDerivedStructureSheafIso (T : BigFppfOver B S hS) :
    (representedDualityQuasicoherentDerivedEquivalence B S hS T).functor.obj
        (Stacks.Duality.DerivedPushforward.derivedStructureSheaf
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T)) ≅
      derivedStructureSheaf B S hS (schemeSpace T).1 (schemeSpace T).2 := by
  refine ObjectProperty.isoMk _ ?_
  let O₀ :=
    SheafOfModules.unit (representedSchemeRepresentedZariskiRingedToposHom B S hS T).ringCatSheaf
  have e₁ := (representedZariskiDerivedPullbackIso B S hS T).app
    ((DerivedCategory.singleFunctor _ 0).obj O₀)
  have e₂ := ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS
    T).mapDerivedCategorySingleFunctor 0).app O₀
  have e₃ := (representedZariskiModulePullbackAssociatedModuleIsoRepresentedZariskiModuleAdjunction
      B S hS T).app O₀ ≪≫
    representedAssociatedModuleObjUnitIso B S hS T (isAlgebraicSpace_yoneda B S hS T)
  exact e₁ ≪≫ e₂ ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso e₃

end

/-- The equivalence `D_QCoh(𝒪_{X_0}) ≌ D_QCoh(𝒪_X)` carries an object with vanishing `i`-th
cohomology sheaf to one with vanishing `i`-th cohomology sheaf. -/
theorem isZero_homology_representedDualityQuasicoherentDerivedEquivalence_functor_obj
    (T : BigFppfOver B S hS)
    (M : Stacks.Duality.quasiCoherentDerivedCategory
      (representedSchemeRepresentedZariskiRingedToposHom B S hS T))
    (i : ℤ) (hM : IsZero ((DerivedCategory.homologyFunctor _ i).obj M.obj)) :
    IsZero ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) i).obj
      ((representedDualityQuasicoherentDerivedEquivalence B S hS T).functor.obj M).obj) := by
  let :=
    HasDerivedCategory.standard (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules
  have h₀ : IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((Stacks.Injectives.grothendieckModelEquiv _).inverse.obj M.obj)) :=
    hM.of_iso (((StacksDraft.DerivedModel.grothendieckModelEquivHomologyIso _ i).app _).symm ≪≫
      (@DerivedCategory.homologyFunctor _ _ _
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian _) i).mapIso
        ((Stacks.Injectives.grothendieckModelEquiv _).counitIso.app M.obj))
  let := HasDerivedCategory.standard (SheafOfModules
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (schemeSpace T).1
      (schemeSpace T).2).O))
  exact (Functor.map_isZero
      (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T) h₀).of_iso
    ((representedZariskiDerivedPullbackHomologyIso B S hS T i).app
      ((Stacks.Injectives.grothendieckModelEquiv _).inverse.obj M.obj))


/-- The equivalence `D_QCoh(𝒪_{X_0}) ≌ D_QCoh(𝒪_X)` carries the `i`-th cohomology sheaf of an
object to the pullback of that cohomology sheaf along `ε : X ⟶ X_0`. -/
def homologyRepresentedDualityQuasicoherentDerivedEquivalenceFunctorObjIso
    (T : BigFppfOver B S hS)
    (M : Stacks.Duality.quasiCoherentDerivedCategory
      (representedSchemeRepresentedZariskiRingedToposHom B S hS T)) (i : ℤ) :
    (@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) i).obj
        ((representedDualityQuasicoherentDerivedEquivalence B S hS T).functor.obj M).obj ≅
      (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T).obj
        ((DerivedCategory.homologyFunctor
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules i).obj M.obj) := by
  letI :=
    HasDerivedCategory.standard (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules
  letI := HasDerivedCategory.standard (SheafOfModules
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (schemeSpace T).1 (schemeSpace T).2).O))
  let C := (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules
  let N := (Stacks.Injectives.grothendieckModelEquiv C).inverse.obj M.obj
  let e₀ : (DerivedCategory.homologyFunctor C i).obj N ≅
      (@DerivedCategory.homologyFunctor C _ _
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian C) i).obj M.obj :=
    ((StacksDraft.DerivedModel.grothendieckModelEquivHomologyIso C i).app N).symm ≪≫
      (@DerivedCategory.homologyFunctor C _ _
        (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian C) i).mapIso
        ((Stacks.Injectives.grothendieckModelEquiv C).counitIso.app M.obj)
  exact (representedZariskiDerivedPullbackHomologyIso B S hS T i).app N ≪≫
    (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T).mapIso e₀

section

attribute [local instance 10000] HasDerivedCategory.standard

/-- An étale derived pullback carries an object with vanishing `i`-th cohomology sheaf to one with
vanishing `i`-th cohomology sheaf. -/
theorem isZero_homology_smallEtaleDerivedModulePullback_of_isEtale {X Y : AlgebraicSpaces B S hS}
    (a : X ⟶ Y) (ha : IsEtale B S hS a.hom) (K : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (i : ℤ) (hK : IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((smallEtaleDerivedModulePullback B S hS a).obj K)) := by
  have := etaleModulePullback_additive B S hS a ha
  have := preservesFiniteLimits_etaleModulePullback B S hS a ha
  have := preservesFiniteColimits_etaleModulePullback B S hS a ha
  exact (Functor.map_isZero (etaleModulePullback.{u, u} B S hS a ha) hK).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso
        ((smallEtaleDerivedModulePullbackIsoEtale B S hS a ha).app K) ≪≫
      ((etaleModulePullback.{u, u} B S hS a ha).mapDerivedCategoryHomologyIso i).app K)

/-- If `a ≫ b = c` with `a` étale, vanishing of the `i`-th cohomology sheaf of the derived pullback
along `b` implies that along `c`. -/
private theorem isZero_homology_smallEtaleDerivedModulePullback_of_comp_eq
    {X Y Z : AlgebraicSpaces B S hS} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (h : a ≫ b = c)
    (ha : IsEtale B S hS a.hom) (K : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)) (i : ℤ)
    (hK : IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((smallEtaleDerivedModulePullback B S hS b).obj K))) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((smallEtaleDerivedModulePullback B S hS c).obj K)) := by
  subst h
  exact (isZero_homology_smallEtaleDerivedModulePullback_of_isEtale a ha _ i hK).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso
      ((smallEtaleDerivedModulePullbackCompIso B S hS a b).app K).symm)

end

/-- **Cohomology of the right adjoint at the structure sheaf, for a represented morphism.** For
a morphism `g : T' ⟶ T` of the big fppf site between quasi-compact and quasi-separated schemes,
if the twisted inverse image `a_0(𝒪_T)` of the scheme morphism has vanishing `i`-th cohomology,
then so does the right adjoint `a(𝒪)` of `Rf_*` for the represented morphism of algebraic
spaces. -/
theorem isZero_homology_quasicoherentDerivedRightAdjoint_representedSpaceMap
    (hZ : B.Contains (⊤_ Scheme.{u})) {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (hXqc : IsQuasiCompactSpace B S hS (yoneda.obj T'))
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj T'))
    (hYqc : IsQuasiCompactSpace B S hS (yoneda.obj T))
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj T)) (i : ℤ)
    (h₀ : haveI : CompactSpace (B.inclusion.obj T'.left) :=
        compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hXqc
      haveI : QuasiSeparatedSpace (B.inclusion.obj T'.left) :=
        (isAbsolutelyQuasiSeparated_yoneda_iff_quasiSeparatedSpace B S hS hZ T').1 hXqs
      haveI : CompactSpace (B.inclusion.obj T.left) :=
        compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hYqc
      haveI : QuasiSeparatedSpace (B.inclusion.obj T.left) :=
        (isAbsolutelyQuasiSeparated_yoneda_iff_quasiSeparatedSpace B S hS hZ T).1 hYqs
      haveI :=
        Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs
          (B.inclusion.map g.left)
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((Stacks.Duality.DerivedPushforward.qcqsRestrictedDerivedPushforward
          (B.inclusion.map g.left)).rightAdjoint.obj
          (Stacks.Duality.DerivedPushforward.derivedStructureSheaf
            (representedSchemeRepresentedZariskiRingedToposHom B S hS T))).obj)) :
    IsZero ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) i).obj
      ((quasicoherentDerivedRightAdjoint hZ (schemeSpaceMap g) hXqc hXqs hYqs).obj
        (derivedStructureSheaf B S hS (schemeSpace T).1
          (schemeSpace T).2)).obj) := by
  have : CompactSpace (B.inclusion.obj T'.left) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hXqc
  have : QuasiSeparatedSpace (B.inclusion.obj T'.left) :=
    (isAbsolutelyQuasiSeparated_yoneda_iff_quasiSeparatedSpace B S hS hZ T').1 hXqs
  have : CompactSpace (B.inclusion.obj T.left) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hYqc
  have : QuasiSeparatedSpace (B.inclusion.obj T.left) :=
    (isAbsolutelyQuasiSeparated_yoneda_iff_quasiSeparatedSpace B S hS hZ T).1 hYqs
  have := Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs
    (B.inclusion.map g.left)
  have e := (quasicoherentDerivedRightAdjoint hZ (schemeSpaceMap g) hXqc hXqs
      hYqs).mapIso (representedDualityDerivedStructureSheafIso T).symm ≪≫
    ((representedRightAdjointIso hZ g hXqc hXqs hYqc hYqs).app
      (Stacks.Duality.DerivedPushforward.derivedStructureSheaf
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T))).symm
  exact (isZero_homology_representedDualityQuasicoherentDerivedEquivalence_functor_obj T' _ i
    h₀).of_iso ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) i).mapIso
      ((ObjectProperty.ι _).mapIso e))


/-- **Cohomology of the right adjoint at the structure sheaf, for a represented morphism.** For a
morphism `g : T' ⟶ T` of the big fppf site between quasi-compact and quasi-separated schemes, the
`i`-th cohomology sheaf of the right adjoint `a(𝒪)` of `Rf_*` for the represented morphism of
algebraic spaces is the pullback along `ε : X ⟶ X_0` of the `i`-th cohomology sheaf of the twisted
inverse image `a_0(𝒪_T)` of the morphism of schemes. -/
def homologyQuasicoherentDerivedRightAdjointRepresentedSpaceMapIso
    (hZ : B.Contains (⊤_ Scheme.{u})) {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (hXqc : IsQuasiCompactSpace B S hS (yoneda.obj T'))
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj T'))
    (hYqc : IsQuasiCompactSpace B S hS (yoneda.obj T))
    (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj T)) (i : ℤ) :
    haveI : CompactSpace (B.inclusion.obj T'.left) :=
      compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hXqc
    haveI : QuasiSeparatedSpace (B.inclusion.obj T'.left) :=
      (isAbsolutelyQuasiSeparated_yoneda_iff_quasiSeparatedSpace B S hS hZ T').1 hXqs
    haveI : CompactSpace (B.inclusion.obj T.left) :=
      compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hYqc
    haveI : QuasiSeparatedSpace (B.inclusion.obj T.left) :=
      (isAbsolutelyQuasiSeparated_yoneda_iff_quasiSeparatedSpace B S hS hZ T).1 hYqs
    haveI :=
      Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs
        (B.inclusion.map g.left)
    (@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) i).obj
        ((quasicoherentDerivedRightAdjoint hZ (schemeSpaceMap g) hXqc hXqs hYqs).obj
          (derivedStructureSheaf B S hS (schemeSpace T).1
            (schemeSpace T).2)).obj ≅
      (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T').obj
        ((DerivedCategory.homologyFunctor
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T').Modules i).obj
          ((Stacks.Duality.DerivedPushforward.qcqsRestrictedDerivedPushforward
            (B.inclusion.map g.left)).rightAdjoint.obj
            (Stacks.Duality.DerivedPushforward.derivedStructureSheaf
              (representedSchemeRepresentedZariskiRingedToposHom B S hS T))).obj) := by
  haveI : CompactSpace (B.inclusion.obj T'.left) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hXqc
  haveI : QuasiSeparatedSpace (B.inclusion.obj T'.left) :=
    (isAbsolutelyQuasiSeparated_yoneda_iff_quasiSeparatedSpace B S hS hZ T').1 hXqs
  haveI : CompactSpace (B.inclusion.obj T.left) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hYqc
  haveI : QuasiSeparatedSpace (B.inclusion.obj T.left) :=
    (isAbsolutelyQuasiSeparated_yoneda_iff_quasiSeparatedSpace B S hS hZ T).1 hYqs
  haveI := Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs
    (B.inclusion.map g.left)
  have e := (quasicoherentDerivedRightAdjoint hZ (schemeSpaceMap g) hXqc hXqs
      hYqs).mapIso (representedDualityDerivedStructureSheafIso T).symm ≪≫
    ((representedRightAdjointIso hZ g hXqc hXqs hYqc hYqs).app
      (Stacks.Duality.DerivedPushforward.derivedStructureSheaf
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T))).symm
  exact (@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) i).mapIso
      ((ObjectProperty.ι _).mapIso e) ≪≫
    homologyRepresentedDualityQuasicoherentDerivedEquivalenceFunctorObjIso T' _ i


end AlgebraicGeometry.Space

namespace AlgebraicGeometry

open Space

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  SheafOfModules.instAbelian

/-- **The relative dualizing complex of a Cohen–Macaulay curve over a field.** Let `Y ⟶ Spec k`
be a family of curves over a field which is Cohen–Macaulay of relative dimension one. Then every
relative dualizing complex of `Y` over `Spec k` has cohomology sheaves only in degree `-1`. -/
theorem CurveFamily.isZero_homology_relativeDualizingComplex_of_base_eq (Y : CurveFamily B hZ)
    (k : Type u) [Field k] (hK : (BigFppfOver.toScheme B integerBase hZ).obj Y.base = Spec (.of k))
    (hY : IsCohenMacaulayDimOneFamily B hZ Y)
    (D : RelativeDualizingComplex B.contains_terminal Y.toBase Y.proper Y.flat
      Y.finitePresentation) (i : ℤ) (hi : i ≠ -1) :
    IsZero ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) i).obj
      D.ω) := by
  obtain ⟨⟨⟨T₀, hT₀⟩, ⟨⟨⟩⟩, t⟩, total, toBase, hflat, hproper, hfp, hdim⟩ := Y
  change T₀ = Spec (.of k) at hK
  subst hK
  let T : BigFppfOver B integerBase hZ := ⟨⟨Spec (.of k), hT₀⟩, ⟨⟨⟩⟩, t⟩
  have hrep : total.obj.IsRepresentable :=
    CurveFamily.isRepresentable_total_of_base_eq
      ⟨T, total, toBase, hflat, hproper, hfp, hdim⟩ rfl
  let X₀ := total.obj.reprX
  let e : yoneda.obj X₀ ≅ total.obj := total.obj.reprW
  let e' : schemeSpace X₀ ≅ total := (ObjectProperty.fullyFaithfulι _).preimageIso e
  let g₀ : X₀ ⟶ T := Yoneda.fullyFaithful.preimage (e.hom ≫ toBase.hom)
  have hg₀ : yoneda.map g₀ = e.hom ≫ toBase.hom := Yoneda.fullyFaithful.map_preimage _
  have hcomm : e'.hom ≫ toBase = schemeSpaceMap g₀ ≫ 𝟙 _ := by
    refine ObjectProperty.hom_ext _ ?_
    change e.hom ≫ toBase.hom = yoneda.map g₀ ≫ 𝟙 _
    rw [hg₀]
    exact (Category.comp_id _).symm
  have sq : IsPullback e'.hom (schemeSpaceMap g₀) toBase (𝟙 _) :=
    @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ inferInstance (IsIso.id _) ⟨hcomm⟩
  have : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj T) :=
    (inferInstance : IsAffine (Spec (.of k)))
  have hY' : IsAffineSpace B integerBase hZ (schemeSpace T).1 :=
    isAffineSpace_yoneda B integerBase hZ T inferInstance
  have hpr' : Space.IsProper B integerBase hZ (schemeSpaceMap g₀).hom :=
    (isProper_isStableUnderBaseChange B integerBase hZ).of_isPullback sq hproper
  have hfl' : Space.IsFlat B integerBase hZ (schemeSpaceMap g₀).hom :=
    (isFlat_isStableUnderBaseChange B integerBase hZ).of_isPullback sq hflat
  have : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g₀) :=
    (isProper_yoneda_map_iff B integerBase hZ g₀).1 hpr'
  have : Flat ((BigFppfOver.toScheme B integerBase hZ).map g₀) :=
    (AlgebraicGeometry.Stack.isFlat_yoneda_map_iff B integerBase hZ g₀).1 hfl'
  have hcmS : Space.IsCohenMacaulay B integerBase hZ (schemeSpaceMap g₀).hom := fun x =>
    (isCohenMacaulayAt_iso_iff B integerBase hZ e (Iso.refl _) (yoneda.map g₀) toBase.hom
      (by rw [hg₀]; exact (Category.comp_id _).symm) x).2 (hY.1 _)
  have hcm : IsCohenMacaulay ((BigFppfOver.toScheme B integerBase hZ).obj X₀) :=
    (isCohenMacaulay_schemeSpaceMap_iff_of_target_eq_spec B hZ g₀ k rfl fun v =>
      inferInstanceAs (IsLocallyNoetherian (Limits.pullback
        ((BigFppfOver.toScheme B integerBase hZ).map g₀)
        (((BigFppfOver.toScheme B integerBase hZ).obj T).fromSpecResidueField v)))).1 hcmS
  have hrdS : Space.HasRelativeDimension 1 B integerBase hZ (schemeSpaceMap g₀).hom := fun x =>
    (holdsOnEveryEtaleChartAtPoint_iso_iff B integerBase hZ (@HasFiberDimensionAt.{u} (1 : ℕ∞))
      e (Iso.refl _) (yoneda.map g₀) toBase.hom (by rw [hg₀]; exact (Category.comp_id _).symm)
      x).2 (hY.2 _)
  obtain ⟨eω, -⟩ := D.isAffineBaseChangePair (schemeSpaceMap g₀) (𝟙 _)
    e'.hom sq hY'
  have hpull : IsZero ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _)
      i).obj ((smallEtaleDerivedModulePullback B integerBase hZ e'.hom).obj D.ω)) := by
    by_cases hne : Nonempty ((BigFppfOver.toScheme B integerBase hZ).obj X₀)
    · obtain ⟨hequi, hdim'⟩ := (hasRelativeDimension_schemeSpaceMap_iff_equidimensional B hZ 1 g₀ k
        rfl inferInstance hne).1 hrdS
      have hXqc := isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B integerBase hZ
        (schemeSpaceMap g₀)
        (isQuasiCompact_of_isPullback_of_isFinitePresentation sq hfp) hY'
      have hXqs := isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B integerBase
        hZ B.contains_terminal (schemeSpaceMap g₀)
        (isQuasiSeparated_of_isPullback_of_isFinitePresentation sq hfp) hY'
      have hYqs :=
        isAbsolutelyQuasiSeparated_of_isAffineSpace B integerBase hZ B.contains_terminal hY'
      have hYqc := isQuasiCompactSpace_yoneda_of_isAffine B integerBase hZ T inferInstance
      refine (isZero_homology_quasicoherentDerivedRightAdjoint_representedSpaceMap
        B.contains_terminal g₀ hXqc hXqs hYqc hYqs i ?_).of_iso
          ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) i).mapIso eω)
      exact Stacks.Duality.isZero_homology_dualizingComplexOverField_of_isCohenMacaulay
        ((BigFppfOver.toScheme B integerBase hZ).map g₀) hcm hequi (by exact_mod_cast hdim') i hi
    · have : IsEmpty ((BigFppfOver.toScheme B integerBase hZ).obj X₀) := not_nonempty_iff.1 hne
      have : IsEmpty (points B integerBase hZ (schemeSpace X₀).1) :=
        (pointsEquivScheme B integerBase hZ X₀).isEmpty
      exact isZero_of_supportOfSheaf_eq_empty B integerBase hZ (schemeSpace X₀) _
        (Set.eq_empty_of_isEmpty _)
  exact (isZero_homology_smallEtaleDerivedModulePullback_of_comp_eq e'.inv e'.hom (𝟙 _)
    e'.inv_hom_id (isEtale_hom_of_isIso B integerBase hZ e'.inv) _ i hpull).of_iso
      ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) i).mapIso
        ((smallEtaleDerivedModulePullbackIdIso B integerBase hZ total).app D.ω).symm)

/-- **The derived fibres of the relative dualizing complex of a Cohen–Macaulay family of curves**,
along an arbitrary morphism `r : R ⟶ S` from the spectrum of a field. Let `X ⟶ S` be a family of
curves which is Cohen–Macaulay of relative dimension one and `(ω, τ)` a relative dualizing
complex. Then the derived pullback of `ω` to `X ×_S R` has cohomology sheaves only in degree
`-1`. -/
theorem CurveFamily.isZero_homology_smallEtaleDerivedModulePullback_pullbackFst
    (X : CurveFamily B hZ) (hX : IsCohenMacaulayDimOneFamily B hZ X)
    (D : RelativeDualizingComplex B.contains_terminal X.toBase X.proper X.flat
      X.finitePresentation)
    {R : BigFppfOver B integerBase hZ} (r : R ⟶ X.base) (k : Type u) [Field k]
    (hR : (BigFppfOver.toScheme B integerBase hZ).obj R = Spec (.of k))
    (hP : IsAlgebraicSpace B integerBase hZ (pullback X.toBase.hom (yoneda.map r)))
    (i : ℤ) (hi : i ≠ -1) :
    IsZero ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) i).obj
      ((smallEtaleDerivedModulePullback B integerBase hZ
        (ObjectProperty.homMk (pullback.fst X.toBase.hom (yoneda.map r)) :
          (⟨_, hP⟩ : AlgebraicSpaces B integerBase hZ) ⟶ X.total)).obj D.ω)) := by
  obtain ⟨Y, hYR, φ, hφ⟩ :=
    Functor.IsFiberedInGroupoids.exists_lift_eqToHom (curvesFiberedCategory B hZ).2 X r
  change Y.base = R at hYR
  subst hYR
  have hr : r = φ.baseMap := by
    have h : eqToHom (rfl : Y.base = Y.base) ≫ r = φ.baseMap := hφ.symm
    rw [eqToHom_refl, Category.id_comp] at h
    exact h
  subst hr
  have hY : IsCohenMacaulayDimOneFamily B hZ Y :=
    CurveFamily.isCohenMacaulayDimOneFamily_of_hom B hZ φ hX
  have h₀ := CurveFamily.isZero_homology_relativeDualizingComplex_of_base_eq Y k hR hY
    (D.baseChange φ.cartesian) i hi
  have hpb := AlgebraicSpaces.isPullback_hom B integerBase hZ φ.cartesian
  let j := hpb.isoPullback
  let P : AlgebraicSpaces B integerBase hZ := ⟨_, hP⟩
  let j' : Y.total ≅ P := (ObjectProperty.fullyFaithfulι _).preimageIso j
  have hj : j'.inv ≫ φ.totalMap = ObjectProperty.homMk (pullback.fst X.toBase.hom
      (yoneda.map φ.baseMap)) := by
    refine ObjectProperty.hom_ext _ ?_
    change j.inv ≫ φ.totalMap.hom = pullback.fst _ _
    exact hpb.isoPullback_inv_fst
  exact isZero_homology_smallEtaleDerivedModulePullback_of_comp_eq j'.inv φ.totalMap _ hj
    (isEtale_hom_of_isIso B integerBase hZ j'.inv) _ i h₀

/-- **The derived fibres of the relative dualizing complex of a Cohen–Macaulay family of curves**
over the points of the base live in degree `-1`. -/
theorem CurveFamily.isZero_homology_smallEtaleDerivedModulePullback_residueFibreι
    (X : CurveFamily B hZ) (hX : IsCohenMacaulayDimOneFamily B hZ X)
    (D : RelativeDualizingComplex B.contains_terminal X.toBase X.proper X.flat
      X.finitePresentation)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) (i : ℤ) (hi : i ≠ -1) :
    IsZero ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) i).obj
      ((smallEtaleDerivedModulePullback B integerBase hZ
        (residueFibreι (X.toBase : X.total ⟶ schemeSpace X.base) s)).obj
          D.ω)) :=
  CurveFamily.isZero_homology_smallEtaleDerivedModulePullback_pullbackFst X hX D
    (residueFieldValuedPoint B integerBase hZ X.base s).value _ rfl _ i hi


end AlgebraicGeometry

end
