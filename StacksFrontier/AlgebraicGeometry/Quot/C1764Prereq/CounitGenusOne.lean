module

public import StacksFrontier.AlgebraicGeometry.Quot.C1764Prereq.CounitFibre
public import StacksFrontier.AlgebraicGeometry.Quot.C1764Prereq.DualizingSheafFibre
public import StacksFrontier.AlgebraicGeometry.Quot.C1764Prereq.GenusOneEtaleSummand
public import StacksFrontier.AlgebraicGeometry.Quot.C1764Prereq.GenusOneFibreTrivial
public import StacksFrontier.AlgebraicGeometry.Quot.C1764Prereq.IsoLocusNearFibre
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableNearFibre
public import StacksFrontier.AlgebraicGeometry.Quot.InvertibleTwistPower
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedTwistedCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePreimageStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction

/-!
# Surjectivity of the counit near a fibre of genus one

Let `f : X → S` be a prestable family of curves with relative dualizing complex `ω^•_{X/S}`, let
`ω_{X/S} = H^{-1}(ω^•_{X/S})`, and let `s ∈ S` be a point whose fibre `X_s` has genus one and no
rational tail. Then for every `m` the counit `f^*f_*ω_{X/S}^{⊗ m} ⟶ ω_{X/S}^{⊗ m}` is surjective
over `f⁻¹(U)` for some open `U ∋ s`.

## Main results

* `AlgebraicGeometry.C1764Prereq.isCounitSurjectiveAbove_of_genus_eq_one`: for a prestable family
  of curves and a fibre of genus one without rational tail, the counit
  `f^*f_*ω_{X/S}^{⊗ m} ⟶ ω_{X/S}^{⊗ m}` is surjective over a neighbourhood of the fibre.

## References

* [Stacks Project, Tag 0E6Y](https://stacks.math.columbia.edu/tag/0E6Y)
* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0E3K](https://stacks.math.columbia.edu/tag/0E3K)
* [Stacks Project, Tag 0E5X](https://stacks.math.columbia.edu/tag/0E5X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace C1764Prereq

/-- For an adjunction `F ⊣ G`, the counit is an epimorphism at every object isomorphic to an
object `F A`. -/
private theorem epi_counit_app_of_iso {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) {L : D} {A : C} (i : L ≅ F.obj A) : Epi (adj.counit.app L) := by
  have : IsSplitEpi (adj.counit.app (F.obj A)) :=
    IsSplitEpi.mk' ⟨F.map (adj.unit.app A), adj.left_triangle_components A⟩
  have h : adj.counit.app L = F.map (G.map i.hom) ≫ adj.counit.app (F.obj A) ≫ i.inv := by
    have := adj.counit.naturality i.hom
    simp only [Functor.comp_map, Functor.id_map] at this
    rw [reassoc_of% this, Iso.hom_inv_id, Category.comp_id]
  rw [h]
  infer_instance

/-- The structure sheaf of the spectrum of a field, placed in degree zero, is not zero. -/
private theorem not_isZero_derivedStructureSheaf_residuePoint (Y : CurveFamily B hZ)
    (t : (BigFppfOver.toScheme B integerBase hZ).obj Y.base) :
    ¬ IsZero (Space.derivedStructureSheaf B integerBase hZ
      (schemeSpace (CurveFamily.residuePoint B hZ Y t)).1
      (schemeSpace (CurveFamily.residuePoint B hZ Y t)).2).obj := by
  intro h
  have h₀ := ((DerivedCategory.homologyFunctor _ 0).map_isZero h).of_iso
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).symm
  refine Space.one_ne_zero_structureRingSheaf_obj B integerBase hZ
    (X := schemeSpace (CurveFamily.residuePoint B hZ Y t))
    (Space.idEtaleChart B integerBase hZ (CurveFamily.residuePoint B hZ Y t))
    (IsLocalRing.closedPoint
      (((BigFppfOver.toScheme B integerBase hZ).obj Y.base).residueField t)) ?_
  let x : ToType ((Space.structureRingSheaf B integerBase hZ
      (schemeSpace (CurveFamily.residuePoint B hZ Y t))).obj.obj (Opposite.op
        (Space.idEtaleChart B integerBase hZ (CurveFamily.residuePoint B hZ Y t)))) := 1
  exact congrArg (fun φ => φ.val.app (Opposite.op
    (Space.idEtaleChart B integerBase hZ (CurveFamily.residuePoint B hZ Y t))) x)
    (h₀.eq_of_src (𝟙 _) 0)

/-- The structure sheaf, as a module over itself, is invertible (in the form used below). -/
private theorem isInvertible_unit_ringSheaf {Z : AlgebraicSpaces B integerBase hZ}
    (L : Space.Modules.{u, u} B integerBase hZ Z.1 Z.2)
    [Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ Z.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ Z.1 Z.2).O)).property L] :
    Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ Z.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ Z.1 Z.2).O)).property
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ Z.1 Z.2).O))) :=
  Space.isInvertible_invertibleTensorPower B integerBase hZ Z.1 Z.2 L 0

/-- The integer tensor powers of a module isomorphic to the structure sheaf are isomorphic to
the structure sheaf. -/
private theorem nonempty_invertibleTensorPower_iso_unit {Z : AlgebraicSpaces B integerBase hZ}
    (L : Space.Modules.{u, u} B integerBase hZ Z.1 Z.2)
    [Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ Z.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ Z.1 Z.2).O)).property L]
    (e : L ≅ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.smallEtaleRingedSite B integerBase hZ Z.1 Z.2).O))) (m : ℤ) :
    Nonempty (Space.invertibleTensorPower B integerBase hZ Z.1 Z.2 L m ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ Z.1 Z.2).O))) := by
  have hU := isInvertible_unit_ringSheaf L
  let e₀ : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.smallEtaleRingedSite B integerBase hZ Z.1 Z.2).O)) ≅
      Space.invertibleTensorPower B integerBase hZ Z.1 Z.2
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
          (Space.smallEtaleRingedSite B integerBase hZ Z.1 Z.2).O))) 0 := Iso.refl _
  exact ⟨Space.invertibleTensorPowerCongr B integerBase hZ Z.1 Z.2 e m ≪≫
    Space.invertibleTensorPowerCongr B integerBase hZ Z.1 Z.2 e₀ m ≪≫
    Space.invertibleTensorPowerTensorPowerIso B integerBase hZ Z.1 Z.2 _ 0 m ≪≫
    eqToIso (congrArg (fun k => Space.invertibleTensorPower B integerBase hZ Z.1 Z.2
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ Z.1 Z.2).O))) k) (zero_mul m)) ≪≫ e₀.symm⟩

/-- **The counit is surjective near a fibre of genus one.** Let `f : X → S` be a prestable family
of curves with relative dualizing complex `ω^•_{X/S}`, `ω_{X/S} = H^{-1}(ω^•_{X/S})`, and let `V`
present a fibre `X_s` of genus one without rational tail. Then for every `m` the counit
`f^*f_*ω_{X/S}^{⊗ m} ⟶ ω_{X/S}^{⊗ m}` is surjective over `f⁻¹(U)` for some open `U ∋ s`. -/
theorem isCounitSurjectiveAbove_of_genus_eq_one {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X)
    (D : Space.RelativeDualizingComplex B.contains_terminal X.toBase X.proper X.flat
      X.finitePresentation)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) {V : BigFppfOver B integerBase hZ}
    {v : V ⟶ CurveFamily.residuePoint B hZ X s} {q : yoneda.obj V ⟶ X.total.obj}
    (hq : CurveFamily.IsFibrePresentation B hZ X s v q)
    (hg : genus (CurveFamily.fibreMap B hZ X s v) = 1)
    (htail :
      letI : Scheme.Over ((BigFppfOver.toScheme B integerBase hZ).obj V)
          (Spec (.of (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s))) :=
        ⟨CurveFamily.fibreMap B hZ X s v⟩
      ∀ C : ((BigFppfOver.toScheme B integerBase hZ).obj V).IdealSheafData,
        ¬ IsRationalTail (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s)
          ((BigFppfOver.toScheme B integerBase hZ).obj V) C)
    (m : ℤ) :
    X.IsCounitSurjectiveAbove
      (@Space.invertibleTensorPower B integerBase hZ X.total.1 X.total.2
        (X.dualizingSheafOfComplex D) (CurveFamily.isInvertible_dualizingSheafOfComplex hX D) m)
      s := by
  have hωinv := CurveFamily.isInvertible_dualizingSheafOfComplex hX D
  obtain ⟨T, c, t, hT, hc, ht, π, hπ⟩ :=
    exists_etale_isSplitEpi_of_genus_ne_zero hX s hq (by rw [hg]; exact one_ne_zero)
  have sq : IsPullback (X.baseChangeHom c).totalMap (X.baseChange c).toBase X.toBase
      (schemeSpaceMap c) := (X.baseChangeHom c).cartesian
  have hY' : Space.IsAffineSpace B integerBase hZ (schemeSpace T).1 :=
    Space.isAffineSpace_yoneda B integerBase hZ T hT
  obtain ⟨e₁, -⟩ := D.isAffineBaseChangePair (X.baseChange c).toBase (schemeSpaceMap c)
    (X.baseChangeHom c).totalMap sq hY'
  obtain ⟨e₀⟩ := nonempty_relDualizing_iso_single hX D
  have hωflat := Stacks.SheafOfModules.isFlat_of_isInvertible_ringedSite
      (Space.smallEtaleRingedSite B integerBase hZ X.total.1 X.total.2).O _ _ hωinv
  have hω'inv := Space.stacksIsInvertible_modulePullback_obj B integerBase hZ
    (X.baseChangeHom c).totalMap (X.dualizingSheafOfComplex D)
  have hω'flat := Stacks.SheafOfModules.isFlat_of_isInvertible_ringedSite
      (Space.smallEtaleRingedSite B integerBase hZ (X.baseChange c).total.1
        (X.baseChange c).total.2).O _ _ hω'inv
  let e : ((Space.affineBaseChangeRightAdjoint B.contains_terminal sq X.finitePresentation
      hY').obj (Space.derivedStructureSheaf B integerBase hZ (schemeSpace T).1
        (schemeSpace T).2)).obj ≅
      (DerivedCategory.singleFunctor _ (-1)).obj
        ((Space.modulePullback B integerBase hZ (X.baseChangeHom c).totalMap).obj
          (X.dualizingSheafOfComplex D)) :=
    e₁.symm ≪≫ (Space.smallEtaleDerivedModulePullback B integerBase hZ
        (X.baseChangeHom c).totalMap).mapIso e₀ ≪≫
      Space.smallEtaleDerivedModulePullbackSingleIsoOfFlat (X.baseChangeHom c).totalMap
        (X.dualizingSheafOfComplex D) (-1) hωflat ≪≫
      eqToIso (by rw [Space.pullbackModules_smallEtaleRingedToposHom]; rfl)
  obtain ⟨σ, hσ⟩ := exists_section_ne_zero_of_isSplitEpi B.contains_terminal sq
    X.finitePresentation hY' (X.baseChange c).flat _ hω'flat e π hπ
  obtain ⟨V', v', q', hq'⟩ :=
    C1590Private.exists_presentation_of_fieldValuedPoint (X.baseChange c)
      ((X.baseChange c).residueFieldPoint t)
  have hq'' : CurveFamily.IsFibrePresentation B hZ (X.baseChange c) t v' q' := hq'
  have hσV := hσ (ObjectProperty.homMk q' : schemeSpace V' ⟶ (X.baseChange c).total)
    (schemeSpaceMap v') (schemeSpaceMap (CurveFamily.residuePointMap B hZ (X.baseChange c) t))
    (isPullback_fibre hq'') (not_isZero_derivedStructureSheaf_residuePoint (X.baseChange c) t)
  have hisoV := isIso_modulePullback_map_fibre_of_ne_zero hX (X.dualizingSheafOfComplex D) hωinv
    (isDualizingOnFibres_dualizingSheafOfComplex hX D) s hq hg htail c t ht hq'' σ hσV
  obtain ⟨O, htO, hO⟩ := exists_opens_isIso_baseChange_of_epi_fibre (X.baseChange c)
    (isInvertible_unit_ringSheaf
      ((Space.modulePullback B integerBase hZ (X.baseChangeHom c).totalMap).obj
        (X.dualizingSheafOfComplex D))) hω'inv σ
    t hq'' (@IsIso.epi_of_iso _ _ _ _ _ hisoV)
  let φ : (X.baseChange c).baseChange (Space.openSubHom (X.baseChange c).base O) ⟶ X :=
    (X.baseChange c).baseChangeHom (Space.openSubHom (X.baseChange c).base O) ≫ X.baseChangeHom c
  have hmc := (BigFppfOver.toScheme B integerBase hZ).map_comp
    (Space.openSubHom (X.baseChange c).base O) c
  have hφ : Etale ((BigFppfOver.toScheme B integerBase hZ).map φ.baseMap) :=
    hmc ▸ MorphismProperty.comp_mem @Etale _ ((BigFppfOver.toScheme B integerBase hZ).map c)
      (Space.etale_toScheme_map_openSubHom B integerBase hZ (X.baseChange c).base O) hc
  let t' : (BigFppfOver.toScheme B integerBase hZ).obj (Space.openSub (X.baseChange c).base O) :=
    ⟨t, htO⟩
  have ht' : (BigFppfOver.toScheme B integerBase hZ).map φ.baseMap t' = s := by
    have h1 := congrArg (fun k => k t') hmc
    have h2 : (BigFppfOver.toScheme B integerBase hZ).map
        (Space.openSubHom (X.baseChange c).base O) t' = t := by
      rw [Space.toScheme_map_openSubHom]
      rfl
    exact h1.trans ((Scheme.Hom.comp_apply _ _ _).trans
      ((congrArg ((BigFppfOver.toScheme B integerBase hZ).map c) h2).trans ht))
  let L := Space.invertibleTensorPower B integerBase hZ X.total.1 X.total.2
    (X.dualizingSheafOfComplex D) m
  have hLinv : Stacks.SheafOfModules.IsInvertible
      (Space.structurePresheaf B integerBase hZ X.total.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ X.total.1 X.total.2).O)).property L :=
    Space.isInvertible_invertibleTensorPower B integerBase hZ _ _ _ m
  have hLa := Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hLinv
  have hLq : L.IsQuasicoherentOnSite :=
    Space.isQuasicoherentOnSite_of_isInvertible B integerBase hZ X.total L hLa
  have hLft : SheafOfModules.IsFiniteTypeOnSite L := by
    have : L.IsFinitePresentationOnSite :=
      SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite
        (Space.isFiniteLocallyFreeOfRank_one_of_isInvertible B integerBase hZ X.total L
          hLa).isFiniteLocallyFreeOnSite
    infer_instance
  let ι' := ((X.baseChange c).baseChangeHom (Space.openSubHom (X.baseChange c).base O)).totalMap
  have hφt : φ.totalMap = ι' ≫ (X.baseChangeHom c).totalMap := rfl
  let eω := eqToIso (congrArg (fun k => (Space.modulePullback B integerBase hZ k).obj
      (X.dualizingSheafOfComplex D)) hφt) ≪≫
    ((Space.modulePullbackCompIso B integerBase hZ ι' (X.baseChangeHom c).totalMap).app
        (X.dualizingSheafOfComplex D)).symm ≪≫
      (@asIso _ _ _ _ ((Space.modulePullback B integerBase hZ ι').map σ) hO).symm ≪≫
      Space.modulePullbackUnitIso B integerBase hZ ι'
  have := Space.stacksIsInvertible_modulePullback_obj B integerBase hZ φ.totalMap
    (X.dualizingSheafOfComplex D)
  obtain ⟨eL⟩ := nonempty_invertibleTensorPower_iso_unit _ eω m
  let eL' := Space.modulePullbackInvertibleTensorPowerIso B integerBase hZ φ.totalMap
    (X.dualizingSheafOfComplex D) m ≪≫ eL ≪≫
    (Space.modulePullbackUnitIso B integerBase hZ
      ((X.baseChange c).baseChange (Space.openSubHom (X.baseChange c).base O)).toBase).symm
  have hε := epi_counit_app_of_iso
    (Space.modulePullbackAdjunction B integerBase hZ
      ((X.baseChange c).baseChange (Space.openSubHom (X.baseChange c).base O)).toBase) eL'
  have key : ((X.baseChange c).baseChange
      (Space.openSubHom (X.baseChange c).base O)).IsCounitSurjectiveAbove
      ((Space.modulePullback B integerBase hZ φ.totalMap).obj L) t' := by
    refine ⟨⊤, trivial, ?_⟩
    have : (Space.modulePullback B integerBase hZ (Space.openSubspaceHom B integerBase hZ
        (((X.baseChange c).baseChange (Space.openSubHom (X.baseChange c).base O)).preimageOpens ⊤)
        (((X.baseChange c).baseChange
          (Space.openSubHom (X.baseChange c).base O)).isOpenSubspace_preimageOpens
          ⊤))).IsLeftAdjoint :=
      ⟨_, ⟨Space.modulePullbackAdjunction B integerBase hZ _⟩⟩
    exact Functor.map_epi _ _
  exact ht' ▸ isCounitSurjectiveAbove_of_hom_of_etale φ hφ L hLq hLft t' key

end C1764Prereq

end AlgebraicGeometry
