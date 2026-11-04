module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.ReductionTypes
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberConnected
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyStructureSheafCohomology
public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilyOfSchemes
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverField
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesGenericFibre
public import StacksFrontier.Deformation.Examples.Geometric.CurvesDeformationComparison
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmoothingGenericFibre
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.SeparableDegreeFibres
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusNormalizationBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.FirstVanishing.GenericFibre
public import StacksFrontier.AlgebraicGeometry.Topologies.V.PhVFlatteningModification
public import StacksFrontier.AlgebraicGeometry.Models.BaseChange

/-!
# The minimal model of a curve with semistable reduction, as a prestable family of curves

Let `R` be a discrete valuation ring with fraction field `K` and `C` a smooth projective curve
over `K` with `H⁰(C, 𝒪_C) = K` which has semistable reduction ([Stacks, Tag 0CDH]). Its minimal
model `Y ⟶ Spec R` is at-worst-nodal of relative dimension one ([Stacks, Tag 0CDG]) and has
geometrically connected fibres ([Stacks, Tag 0C62]), so it is proper and flat with
`f_*𝒪_Y = 𝒪_{Spec R}` universally ([Stacks, Tag 0E0L], [Stacks, Tag 0GKA]). This file records
the family of curves it defines: it is prestable ([Stacks, Tag 0E6T]) and `C` is its generic
fibre.

## Main results

* `Stacks.Models.exists_isPrestableCurveFamily_of_hasSemistableReduction`: a curve with semistable
  reduction is the generic fibre of a prestable family of curves of its genus.
* `Stacks.Models.contains_spec_of_isFractionRing`: the spectrum of the fraction field lies in
  every big fppf site containing `Spec R`.
* `Stacks.Models.exists_isMinimalModel_isAtWorstNodal_geometricallyConnected`: the minimal
  model of a curve with semistable reduction is at-worst-nodal, with geometrically connected
  fibres.
* `hasUniversallyBijectiveGlobalFunctions_curveFamilyOfFiberDimensionLE_of_isIso_c`: `f_*𝒪 = 𝒪`
  universally for the family of curves of a morphism of schemes whose base changes have
  invertible structure maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **`f_*𝒪 = 𝒪` universally for the family of curves of a morphism of schemes with fibres of
dimension at most one**, as soon as the structure map of every base change along a scheme of the
site is invertible. -/
theorem hasUniversallyBijectiveGlobalFunctions_curveFamilyOfFiberDimensionLE_of_isIso_c
    {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U)
    (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hfib : ∀ x, topologicalKrullDimAt
      (((BigFppfOver.toScheme B integerBase hZ).map g).fiber
        (((BigFppfOver.toScheme B integerBase hZ).map g) x))
      (((BigFppfOver.toScheme B integerBase hZ).map g).asFiber x) ≤ 1)
    (hc : ∀ (V : BigFppfOver B integerBase hZ) (v : V ⟶ U),
      IsIso ((BigFppfOver.toScheme B integerBase hZ).map (pullback.snd g v)).c) :
    HasUniversallyBijectiveGlobalFunctions B hZ
      (curveFamilyOfFiberDimensionLE B hZ g hflat hproper hlfp hfib) := by
  intro Y' g'
  refine Space.bijective_globalFunctionsMap_of_forall_schemeSpace _ fun V t => ?_
  let hff := schemeSpaceFunctorFullyFaithful B (S := integerBase) hZ
  let v : V ⟶ U := hff.preimage (t ≫ g')
  have hv : schemeSpaceMap v = t ≫ g' := hff.map_preimage _
  have hsite : IsPullback (yoneda.map (pullback.fst g v)) (yoneda.map (pullback.snd g v))
      (yoneda.map g) (yoneda.map v) :=
    Functor.map_isPullback yoneda (IsPullback.of_hasPullback g v)
  have hsp0 : IsPullback (schemeSpaceMap (pullback.fst g v)) (schemeSpaceMap (pullback.snd g v))
      (schemeSpaceMap g) (schemeSpaceMap v) :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ hsite.w) hsite
  have hsp : IsPullback (schemeSpaceMap (pullback.fst g v)) (schemeSpaceMap (pullback.snd g v))
      (curveFamilyOfFiberDimensionLE B hZ g hflat hproper hlfp hfib).toBase
      (t ≫ g') := hv ▸ hsp0
  have sq := (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ
    (ObjectProperty.homMk (pullback.snd
      (curveFamilyOfFiberDimensionLE B hZ g hflat hproper hlfp hfib).toBase.hom
        g'.hom) :
      AlgebraicSpaces.fiberProduct B integerBase hZ
        (curveFamilyOfFiberDimensionLE B hZ g hflat hproper hlfp hfib).toBase g' ⟶
          Y') t).paste_horiz
    (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ
      (curveFamilyOfFiberDimensionLE B hZ g hflat hproper hlfp hfib).toBase g')
  let e := sq.isoIsPullback _ _ hsp
  have he : (ObjectProperty.homMk (pullback.snd (ObjectProperty.homMk (pullback.snd
      (curveFamilyOfFiberDimensionLE B hZ g hflat hproper hlfp hfib).toBase.hom
        g'.hom) :
        AlgebraicSpaces.fiberProduct B integerBase hZ
          (curveFamilyOfFiberDimensionLE B hZ g hflat hproper hlfp hfib).toBase g' ⟶
            Y').hom t.hom) :
      AlgebraicSpaces.fiberProduct B integerBase hZ _ t ⟶ schemeSpace V) =
      e.hom ≫ schemeSpaceMap (pullback.snd g v) :=
    (IsPullback.isoIsPullback_hom_snd _ _ _ _).symm
  rw [he, Space.globalFunctionsMap_comp, RingHom.coe_comp]
  refine ((Space.globalFunctionsMapEquiv B integerBase hZ e).bijective.of_comp_iff' _).2 ?_
  rw [Space.bijective_globalFunctionsMap_schemeSpaceMap_iff]
  have := hc V v
  exact (ConcreteCategory.isIso_iff_bijective _).1
    (inferInstanceAs (IsIso (((BigFppfOver.toScheme B integerBase hZ).map
      (pullback.snd g v)).c.app (Opposite.op ⊤))))

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- The fibres of a morphism of schemes which is at-worst-nodal of relative dimension one, with
geometrically connected fibres, have local dimension at most one. -/
theorem topologicalKrullDimAt_fiber_le_one_of_isAtWorstNodal {X S : Scheme.{u}} (f : X ⟶ S)
    [GeometricallyConnected f] (hf : IsAtWorstNodalOfRelativeDimensionOne f) (x : X) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ 1 :=
  (topologicalKrullDimAt_le_topologicalKrullDim _).trans
    (Stacks.AlgebraicGeometry.NodalFamilyCohomology.topologicalKrullDim_fiber_le_one f hf (f x))

/-- **The family of curves of a nodal morphism with geometrically connected fibres is
prestable** ([Stacks, Tag 0E6T]). -/
theorem isPrestableCurveFamily_curveFamilyOfFiberDimensionLE_of_isAtWorstNodal
    {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U)
    (hflat : Flat ((𝒯).map g)) (hproper : IsProper ((𝒯).map g))
    (hlfp : LocallyOfFinitePresentation ((𝒯).map g))
    (hfib : ∀ x, topologicalKrullDimAt (((𝒯).map g).fiber (((𝒯).map g) x))
      (((𝒯).map g).asFiber x) ≤ 1)
    [GeometricallyConnected ((𝒯).map g)]
    (hn : IsAtWorstNodalOfRelativeDimensionOne ((𝒯).map g)) :
    IsPrestableCurveFamily B hZ
      (curveFamilyOfFiberDimensionLE B hZ g hflat hproper hlfp hfib) := by
  refine ⟨(Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
    isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget g).2 hn, ?_⟩
  refine hasUniversallyBijectiveGlobalFunctions_curveFamilyOfFiberDimensionLE_of_isIso_c g
    hflat hproper hlfp hfib fun V v => ?_
  open Stacks.AlgebraicGeometry.NodalFamilyCohomology in
  exact (isIso_c_and_isIso_c_of_isPullback_of_isAtWorstNodal ((𝒯).map g) hn).2
    ((IsPullback.of_hasPullback g v).map (𝒯))

/-- A pullback of `g` along a map factoring through a residue field point is the pullback of
the fibre over that point along the map to the residue field. -/
private theorem exists_isPullback_fiberToSpecResidueField {X S W P : Scheme.{u}} (g : X ⟶ S)
    (x : S) (a : W ⟶ Spec (S.residueField x)) {f : P ⟶ X} {h : P ⟶ W}
    (hP : IsPullback f h g (a ≫ S.fromSpecResidueField x)) :
    ∃ l, IsPullback l h (g.fiberToSpecResidueField x) a := by
  refine ⟨pullback.lift f (h ≫ a) (by rw [hP.w, Category.assoc]),
    IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback g _)⟩
  convert hP using 1
  exact pullback.lift_fst _ _ _

open ProperFlatFibreEulerCharacteristic in
/-- **The genus of the fibres of a proper flat family over a connected base is constant**, when
every fibre has dimension at most one and only constant global functions. -/
theorem genus_fiberToSpecResidueField_eq_of_preconnectedSpace {Y S : Scheme.{u}} (g : Y ⟶ S)
    [IsProper g] [Flat g] [LocallyOfFinitePresentation g] [PreconnectedSpace S]
    (hdim : ∀ s, topologicalKrullDim (g.fiber s) ≤ 1)
    (h0 : ∀ s, IsIso ((Scheme.ΓSpecIso (.of (S.residueField s))).inv ≫
      (g.fiberToSpecResidueField s).appTop)) (s t : S) :
    genus (g.fiberToSpecResidueField s) = genus (g.fiberToSpecResidueField t) := by
  obtain ⟨hOfp, hOflat⟩ := isFinitePresentation_and_isFlatOver_of_isInvertible g
    (SheafOfModules.unit Y.ringCatSheaf) (Stacks.SheafOfModules.isInvertible_unit _ _)
  have hfp : FinitePresentation g :=
    FinitePresentation.mk inferInstance inferInstance inferInstance
  have hlc := isLocallyConstant_fibreEulerCharacteristic g hfp _ hOfp hOflat
  have hprop : ∀ y, IsProper (g.fiberToSpecResidueField y) := fun y =>
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback g (S.fromSpecResidueField y))
      inferInstance
  have hχ : ∀ y, fibreEulerCharacteristic g (SheafOfModules.unit Y.ringCatSheaf) y =
      (Module.finrank (S.residueField y)
        (cohomologyOverField (S.residueField y) (g.fiberToSpecResidueField y)
        (SheafOfModules.unit (g.fiber y).ringCatSheaf) 0) : ℤ) -
        (genus (g.fiberToSpecResidueField y) : ℤ) := fun y => by
    have := hprop y
    exact (eulerSum_congr _ _ (Scheme.Modules.pullbackUnitIso (g.fiberι y))).trans
      (PowerSeriesFamily.eulerSum_unit_eq_finrank_sub_genus _ (hdim y))
  have h1 : ∀ y, Module.finrank (S.residueField y)
      (cohomologyOverField (S.residueField y) (g.fiberToSpecResidueField y)
        (SheafOfModules.unit (g.fiber y).ringCatSheaf) 0) = 1 := fun y => by
    have := h0 y
    exact finrank_cohomologyOverField_unit_zero_eq_one _
  have hconst := hlc.apply_eq_of_preconnectedSpace s t
  rw [hχ, hχ, h1, h1] at hconst
  omega

/-- **The genus of a fibre of the family of curves of a morphism of schemes over a field-valued
point.** If every fibre of `g` over a point of its base has genus `g₀`, so does every scheme `V`
presenting the fibre of the family of curves of `g` over a field-valued point `Spec L ⟶ U`. -/
theorem genus_eq_of_isPullback_curveFamilyOfFiberDimensionLE
    {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U)
    (hflat : Flat ((𝒯).map g)) (hproper : IsProper ((𝒯).map g))
    (hlfp : LocallyOfFinitePresentation ((𝒯).map g))
    (hfib : ∀ x, topologicalKrullDimAt (((𝒯).map g).fiber (((𝒯).map g) x))
      (((𝒯).map g).asFiber x) ≤ 1) {g₀ : ℕ}
    (hg : ∀ s, genus (((𝒯).map g).fiberToSpecResidueField s) = g₀)
    {p : Space.FieldValuedPoint B integerBase hZ
      (schemeSpace (curveFamilyOfFiberDimensionLE B hZ g hflat hproper hlfp hfib).base).obj}
    {V : BigFppfOver B integerBase hZ} {v : V ⟶ p.siteObject}
    {q : yoneda.obj V ⟶ (curveFamilyOfFiberDimensionLE B hZ g hflat hproper hlfp hfib).total.obj}
    (hq : IsPullback q (yoneda.map v)
      (curveFamilyOfFiberDimensionLE B hZ g hflat hproper hlfp hfib).toBase.hom
      (yonedaEquiv.symm p.value)) :
    genus ((𝒯).map v) = g₀ := by
  have hval : yonedaEquiv.symm p.value = yoneda.map p.value :=
    yonedaEquiv.symm_apply_eq.mpr (yonedaEquiv_yoneda_map _).symm
  rw [hval] at hq
  let q' := Yoneda.fullyFaithful.preimage q
  have hq' : yoneda.map q' = q := Yoneda.fullyFaithful.map_preimage q
  rw [← hq'] at hq
  have hsite : IsPullback q' v g p.value :=
    IsPullback.of_map yoneda (Yoneda.fullyFaithful.map_injective (by
      rw [Functor.map_comp]
      exact hq.w)) hq
  have hsch := hsite.map (𝒯)
  have : IsProper ((𝒯).map g) := hproper
  set t : Spec (.of p.carrier) ⟶ (𝒯).obj U := (𝒯).map p.value
  let x := (Scheme.SpecToEquivOfField p.carrier _ t).1
  let ψ := (Scheme.SpecToEquivOfField p.carrier _ t).2
  have hφ : t = Spec.map ψ ≫ ((𝒯).obj U).fromSpecResidueField x :=
    ((Scheme.SpecToEquivOfField p.carrier _).symm_apply_apply t).symm
  have hright := IsPullback.of_hasPullback ((𝒯).map g) (((𝒯).obj U).fromSpecResidueField x)
  have hright := IsPullback.of_hasPullback ((𝒯).map g) (((𝒯).obj U).fromSpecResidueField x)
  obtain ⟨l, hleft⟩ := exists_isPullback_fiberToSpecResidueField ((𝒯).map g) x (Spec.map ψ)
    (by rw [← hφ]; exact hsch)
  have : IsProper (((𝒯).map g).fiberToSpecResidueField x) :=
    MorphismProperty.of_isPullback hright inferInstance
  rw [genus_eq_of_isPullback _ _ ψ.hom l ((𝒯).map v) _ hleft]
  exact hg x

end AlgebraicGeometry

namespace Stacks.Models

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The spectrum of the fraction field of a discrete valuation ring lies in every big fppf site
containing the spectrum of the ring. -/
theorem contains_spec_of_isFractionRing {B : BigFppfSite.{u}} (hR : B.Contains (Spec (.of R))) :
    B.Contains (Spec (.of K)) := by
  have := genericFiberSpec_isOpenImmersion (R := R) (K := K)
  exact lt_of_le_of_lt
    (Scheme.size_le_of_mono_quasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R K)))) hR

/-- A curve with semistable reduction has a minimal model which is at-worst-nodal of relative
dimension one, with geometrically connected fibres. -/
theorem exists_isMinimalModel_isAtWorstNodal_geometricallyConnected {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c] (hc : IsProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)] (h : HasSemistableReduction R c hc) :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of R))
      (eY : C ≅ pullback q (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      IsMinimalModel c q eY ∧ IsAtWorstNodalOfRelativeDimensionOne q ∧
        GeometricallyConnected q := by
  obtain ⟨Y, q, eY, hY, hn⟩ := exists_isMinimalModel_isAtWorstNodal_of_hasSemistableReduction c hc h
  refine ⟨Y, q, eY, hY, hn, ?_⟩
  have := hY.isProper
  obtain ⟨hflat, hlft, hqc, hce⟩ := hY.isModel
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let S : RegularProperModelSituation.{u} :=
    { R := R, K := K, k := IsLocalRing.ResidueField R, residueEquiv := AlgEquiv.refl,
      C := C, C_to_K := c, X := Y, X_to_R := q, flat := hflat,
      locallyOfFiniteType := hlft, quasiCompact := hqc, regular := hY.regular,
      genericFiberIso := eY, genericFiberIso_over_K := hce,
      π := π, uniformizer := hπ, curveProjective := hY.curveProjective }
  exact S.geometricallyConnected_X_to_R

/-- **The fibres of a nodal model with geometrically connected fibres.** Let `q : Y ⟶ Spec R` be
a proper model of `C` which is at-worst-nodal of relative dimension one, with geometrically
connected fibres. Every fibre of `q` has dimension at most one, only constant global functions
([Stacks, Tag 0GKA] (a)), and the genus of `C`. -/
theorem fibres_of_isAtWorstNodal {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsProper c]
    {Y : Scheme.{u}} {q : Y ⟶ Spec (.of R)}
    {eY : C ≅ pullback q (Spec.map (CommRingCat.ofHom (algebraMap R K)))} (hY : IsModel c q eY)
    [IsProper q] [GeometricallyConnected q] (hn : IsAtWorstNodalOfRelativeDimensionOne q) :
    (∀ s, topologicalKrullDim (q.fiber s) ≤ 1) ∧
      (∀ s, IsIso ((Scheme.ΓSpecIso (.of ((Spec (.of R)).residueField s))).inv ≫
        (q.fiberToSpecResidueField s).appTop)) ∧
      ∀ s, genus (q.fiberToSpecResidueField s) = genus c := by
  have hdim : ∀ s, topologicalKrullDim (q.fiber s) ≤ 1 := fun s =>
    Stacks.AlgebraicGeometry.NodalFamilyCohomology.topologicalKrullDim_fiber_le_one q hn s
  have h0 : ∀ s, IsIso ((Scheme.ΓSpecIso (.of ((Spec (.of R)).residueField s))).inv ≫
      (q.fiberToSpecResidueField s).appTop) := fun s => by
    have : IsIso (q.fiberToSpecResidueField s).c :=
      (AlgebraicGeometry.NodalFamilyCohomology.isIso_c_and_isIso_c_of_isPullback_of_isAtWorstNodal
        q hn).2 (IsPullback.of_hasPullback q ((Spec (.of R)).fromSpecResidueField s) :
          IsPullback (q.fiberι s) (q.fiberToSpecResidueField s) q _)
    have : IsIso (q.fiberToSpecResidueField s).appTop :=
      PowerSeriesFamily.isIso_appTop_of_isIso_c _
    infer_instance
  refine ⟨hdim, h0, fun s => ?_⟩
  have : Flat q := hY.1
  have : LocallyOfFinitePresentation q :=
    (Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff q).mpr hn |>.2.1
  rw [genus_fiberToSpecResidueField_eq_of_preconnectedSpace q hdim h0 s
    (genericPoint (Spec (.of R)))]
  have := isSchemeTheoreticallyDominant_Spec_map_algebraMap_of_isFractionRing R K
  obtain ⟨φ, hφ⟩ :=
    Stacks.EtaleCohomology.SmoothBaseChange.exists_spec_map_comp_fromSpecResidueField_eq
      (genericPointInclusion R K)
  have hsq : IsPullback (q.fiberι (genericPoint (Spec (.of R))))
      (q.fiberToSpecResidueField (genericPoint (Spec (.of R)))) q
      ((Spec (.of R)).fromSpecResidueField (genericPoint (Spec (.of R)))) :=
    IsPullback.of_hasPullback q _
  have hP : IsPullback (pullback.fst q (genericPointInclusion R K))
      (pullback.snd q (genericPointInclusion R K)) q
      (Spec.map φ ≫ (Spec (.of R)).fromSpecResidueField (genericPoint (Spec (.of R)))) := by
    rw [hφ]
    exact IsPullback.of_hasPullback q _
  obtain ⟨l, hl⟩ := exists_isPullback_fiberToSpecResidueField q _ _ hP
  have : IsProper (q.fiberToSpecResidueField (genericPoint (Spec (.of R)))) :=
    MorphismProperty.of_isPullback hsq inferInstance
  have hgen := genus_eq_of_isPullback ((Spec (.of R)).residueField (genericPoint (Spec (.of R))))
    K φ.hom l (pullback.snd q (genericPointInclusion R K)) _ hl
  have : IsProper (pullback.snd q (genericPointInclusion R K)) := inferInstance
  refine hgen.symm.trans ?_
  rw [← hY.2.2.2, genus_comp_iso_eq K _ eY]

/-- **A curve with semistable reduction is the generic fibre of a prestable family of curves of
its genus.** Let `C` be a smooth projective curve over `K` with `H⁰(C, 𝒪_C) = K` which has
semistable reduction. Its minimal model `q : Y ⟶ Spec R` defines a family of curves over `Spec R`
which is prestable ([Stacks, Tag 0E6T]), all of whose fibres over fields have the genus of `C`,
and of which `C` is the generic fibre: a morphism of families of curves from the family of `C`
over `Spec K` lying over `Spec K ⟶ Spec R`. -/
theorem exists_isPrestableCurveFamily_of_hasSemistableReduction (B : BigFppfSite.{u})
    (hZ : B.Contains integerBase) (hR : B.Contains (Spec (.of R))) {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsCurve K c] [Smooth c] (hc : IsProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)] (h : HasSemistableReduction R c hc) :
    ∃ (Y : Scheme.{u}) (hY : B.Contains Y) (q : Y ⟶ Spec (.of R)) (hflat : Flat q)
      (hproper : IsProper q) (hlfp : LocallyOfFinitePresentation q)
      (hfib : ∀ x, topologicalKrullDimAt (q.fiber (q x)) (q.asFiber x) ≤ 1),
      IsPrestableCurveFamily B hZ
          (curveFamilyOfFiberDimensionLE B hZ (integerSiteMap B hZ hY hR q) hflat hproper hlfp
            hfib) ∧
        (∀ (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace
            (curveFamilyOfFiberDimensionLE B hZ (integerSiteMap B hZ hY hR q) hflat hproper hlfp
              hfib).base).obj)
          (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
          (q' : yoneda.obj V ⟶ (curveFamilyOfFiberDimensionLE B hZ (integerSiteMap B hZ hY hR q)
            hflat hproper hlfp hfib).total.obj),
          IsPullback q' (yoneda.map v) (curveFamilyOfFiberDimensionLE B hZ
            (integerSiteMap B hZ hY hR q) hflat hproper hlfp hfib).toBase.hom
            (yonedaEquiv.symm p.value) →
          genus ((BigFppfOver.toScheme B integerBase hZ).map v) = genus c) ∧
        ∃ φ : @curveFamilyOfScheme K _ (Over.mk c) hc.isProper B hZ
            (contains_spec_of_isFractionRing hR)
            (IsCurve.topologicalKrullDim_eq_one (k := K) (f := c)).le ⟶
            curveFamilyOfFiberDimensionLE B hZ (integerSiteMap B hZ hY hR q) hflat hproper hlfp
              hfib,
          φ.baseMap = integerSiteMap B hZ (contains_spec_of_isFractionRing hR) hR
            (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  have : IsProper c := hc.isProper
  have hK : B.Contains (Spec (.of K)) := contains_spec_of_isFractionRing hR
  obtain ⟨Y, q, eY, hYm, hn, hgc⟩ :=
    exists_isMinimalModel_isAtWorstNodal_geometricallyConnected c hc h
  have := hYm.isProper
  have := hgc
  obtain ⟨hflat, hlfp, -⟩ := (Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff q).mpr hn
  have hY : B.Contains Y := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact q hR
  have hfib := topologicalKrullDimAt_fiber_le_one_of_isAtWorstNodal q hn
  obtain ⟨-, -, hgen⟩ := fibres_of_isAtWorstNodal c hYm.isModel hn
  have : GeometricallyConnected
      ((BigFppfOver.toScheme B integerBase hZ).map (integerSiteMap B hZ hY hR q)) := hgc
  refine ⟨Y, hY, q, hflat, inferInstance, hlfp, hfib,
    isPrestableCurveFamily_curveFamilyOfFiberDimensionLE_of_isAtWorstNodal _ _ _ _ _ hn,
    fun p V v q' hq' => genus_eq_of_isPullback_curveFamilyOfFiberDimensionLE
      (integerSiteMap B hZ hY hR q) _ _ _ _ hgen hq',
    ?_⟩
  have he : eY.hom ≫ pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap R K))) = c :=
    hYm.isModel.2.2.2
  have hcart : IsPullback (eY.hom ≫ pullback.fst q (Spec.map (CommRingCat.ofHom
      (algebraMap R K)))) c q (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    IsPullback.of_iso_pullback ⟨by rw [Category.assoc, pullback.condition, ← he,
      Category.assoc]⟩ eY rfl he
  exact ⟨{ baseMap := integerSiteMap B hZ hK hR (Spec.map (CommRingCat.ofHom (algebraMap R K)))
           totalMap := schemeSpaceMap (integerSiteMap B hZ
             (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact c hK) hY
             (eY.hom ≫ pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
           cartesian := isPullback_schemeSpaceMap_integerSiteMap hcart }, rfl⟩

end Stacks.Models

end
