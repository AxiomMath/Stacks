module

public import StacksFrontier.AlgebraicGeometry.Quot.C1764Prereq.DualizingSheafOfComplex
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.CanonicalNodal
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleModuleTriviality
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleChartGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyBaseChangeFieldFibre
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.PrestableFibre
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSemistableGenus
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedTwistedCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction

/-!
# A nonzero section of `ω` on a fibre of genus one is a basis

Let `f : X → S` be a prestable family of curves, `ω` an invertible `𝒪_X`-module restricting on
every fibre to its dualizing sheaf, and `s ∈ S` a point whose fibre `X_s` has genus one and no
rational tail. Then `ω|_{X_s} ≅ ω_{X_s} ≅ 𝒪_{X_s}` (Stacks 0E3K). For `c : T ⟶ S` and `t ∈ T`
over `s`, the fibre `V'` of `X_T = X ×_S T` over `t` maps to `X_s`, so `ω` is trivial on `V'` too,
and `H⁰(V', 𝒪_{V'}) = κ(t)` is a field. Hence every nonzero map `𝒪_{V'} ⟶ ω|_{V'}` is an
isomorphism. This is the step of the genus one case of the proof of [Stacks, Tag 0E6Y] saying
that a section of `ω_{X/S}` nonzero on the fibre is a basis there.

The triviality of `ω` on the fibre is given on the Zariski site of the fibre; it is transported
to the small étale site by the associated-module functor of Stacks 03DX.

## Main results

* `AlgebraicGeometry.C1764Prereq.associatedRestrictToChartSchemeIso`: a quasi-coherent module on
  the small étale site of a scheme is the module associated with its Zariski reading.
* `AlgebraicGeometry.C1764Prereq.nonempty_modulePullback_iso_unit_of_zariski_iso_unit`: a
  module trivial on the Zariski site of a scheme is trivial on its small étale site.
* `AlgebraicGeometry.C1764Prereq.isIso_modulePullback_map_fibre_of_ne_zero`: a nonzero section of
  `ω` on a fibre of genus one without rational tail is a basis.

## References

* [Stacks Project, Tag 0E6Y](https://stacks.math.columbia.edu/tag/0E6Y)
* [Stacks Project, Tag 0E3K](https://stacks.math.columbia.edu/tag/0E3K)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
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

/-- **A quasi-coherent module on a scheme is the module associated with its Zariski reading.**
For a quasi-coherent module `M` on the small étale site of the algebraic space represented by a
scheme `V`, the module obtained from its Zariski reading `M|_V` by the associated-module functor
(Stacks 03DX) and the equivalence of the small étale sites of `V` and of `yoneda.obj V` is `M`. -/
def associatedRestrictToChartSchemeIso (V : BigFppfOver B integerBase hZ)
    (M : Space.Modules.{u, u} B integerBase hZ (yoneda.obj V)
      (isAlgebraicSpace_yoneda B integerBase hZ V))
    (hM : M.IsQuasicoherentOnSite) :
    (Space.representedSmallEtaleModuleEquivalence B integerBase hZ V).functor.obj
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B integerBase hZ).obj V) V.left.property).obj
          (Space.restrictToChartScheme B integerBase hZ (yoneda.obj V)
            (isAlgebraicSpace_yoneda B integerBase hZ V) M
            (Space.idEtaleChart B integerBase hZ V))) ≅ M := by
  refine (Space.representedSmallEtaleModuleEquivalence B integerBase hZ V).functor.mapIso
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B integerBase hZ).obj V) V.left.property).mapIso
      (Space.restrictToChartSchemeIsoRestrictModule B integerBase hZ (schemeSpace V) M hM
          (Space.idEtaleChart B integerBase hZ V) ≪≫
        (Space.chartSchemeModuleIsoRestrictModule B integerBase hZ (schemeSpace V) M hM
          (Space.idEtaleChart B integerBase hZ V)).symm) ≪≫
      Space.associatedModuleChartSchemeModuleIso B integerBase hZ (schemeSpace V) M hM
        (Space.idEtaleChart B integerBase hZ V)) ≪≫
    (ObjectProperty.ι _).mapIso
      ((Space.representedQuasicoherentEquivalence B integerBase hZ V).counitIso.app
        (Space.chartSmallEtaleQcoh B integerBase hZ (schemeSpace V) M hM
          (Space.idEtaleChart B integerBase hZ V))) ≪≫
    (Space.chartModuleRestrictionIsoChartSmallEtaleRestriction B integerBase hZ (schemeSpace V) M
      (Space.idEtaleChart B integerBase hZ V)).symm ≪≫ ?_
  have h : Space.chartToSpace B integerBase hZ (schemeSpace V)
      (Space.idEtaleChart B integerBase hZ V) = 𝟙 (schemeSpace V) :=
    ObjectProperty.hom_ext _ rfl
  change (Space.modulePullback B integerBase hZ (Space.chartToSpace B integerBase hZ
    (schemeSpace V) (Space.idEtaleChart B integerBase hZ V))).obj M ≅ M
  rw [h]
  exact (Space.modulePullbackIdIso B integerBase hZ (schemeSpace V)).app M

/-- **A module trivial on the Zariski site of a scheme over it is trivial on its small étale
site.** If `p : V ⟶ X` and the reading `baseChangeModule ω V p` of `ω` on the Zariski site of `V`
is `𝒪_V`, then so is the pullback of `ω` to the small étale site of `V` (Stacks 03DX). -/
theorem nonempty_modulePullback_iso_unit_of_zariski_iso_unit
    {X : AlgebraicSpaces B integerBase hZ} (ω : Space.Modules.{u, u} B integerBase hZ X.1 X.2)
    (V : BigFppfOver B integerBase hZ) (p : yoneda.obj V ⟶ X.1)
    (hω : ((Space.modulePullback B integerBase hZ
      (ObjectProperty.homMk p : schemeSpace V ⟶ X)).obj ω).IsQuasicoherentOnSite)
    (e : Space.baseChangeModule B integerBase hZ ω V p ≅
      SheafOfModules.unit ((BigFppfOver.toScheme B integerBase hZ).obj V).ringCatSheaf) :
    Nonempty ((Space.modulePullback B integerBase hZ
        (ObjectProperty.homMk p : schemeSpace V ⟶ X)).obj ω ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ (yoneda.obj V)
          (isAlgebraicSpace_yoneda B integerBase hZ V)).O))) :=
  ⟨(associatedRestrictToChartSchemeIso V _ hω).symm ≪≫
    (Space.representedSmallEtaleModuleEquivalence B integerBase hZ V).functor.mapIso
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B integerBase hZ).obj V) V.left.property).mapIso e) ≪≫
    Space.representedAssociatedModuleUnitIso B integerBase hZ V⟩

/-- **A nonzero map between trivial modules on a space whose global functions form a field is an
isomorphism**: through the trivializations it is a nonzero endomorphism of `𝒪`. -/
theorem isIso_of_ne_zero_between_trivial {Z : AlgebraicSpaces B integerBase hZ}
    (hfield : IsField (Space.globalFunctions B integerBase hZ Z.1))
    {M L : Space.Modules.{u, u} B integerBase hZ Z.1 Z.2}
    (a : M ≅ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.smallEtaleRingedSite B integerBase hZ Z.1 Z.2).O)))
    (b : L ≅ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.smallEtaleRingedSite B integerBase hZ Z.1 Z.2).O)))
    (σ : M ⟶ L) (hσ : σ ≠ 0) : IsIso σ := by
  have h' : σ = a.hom ≫ (a.inv ≫ σ ≫ b.hom) ≫ b.inv := by simp
  have hψ : a.inv ≫ σ ≫ b.hom ≠ 0 := fun h => hσ (by rw [h', h, zero_comp, comp_zero])
  have : IsIso (a.inv ≫ σ ≫ b.hom) :=
    Space.isIso_of_ne_zero B integerBase hZ Z.1 Z.2 hfield _ hψ
  rw [h']
  infer_instance

/-- **The global functions of a fibre presentation form a field**: `H⁰(V, 𝒪_V) = κ`. -/
theorem isField_globalFunctions_yoneda_of_isIso_appTop {R : CommRingCat.{u}} (hR : IsField R)
    {V : BigFppfOver B integerBase hZ} (φ : (BigFppfOver.toScheme B integerBase hZ).obj V ⟶ Spec R)
    (h : IsIso ((Scheme.ΓSpecIso R).inv ≫ φ.appTop)) :
    IsField (Space.globalFunctions B integerBase hZ (yoneda.obj V)) := by
  let e₁ : R ≃+* Γ((BigFppfOver.toScheme B integerBase hZ).obj V, ⊤) :=
    (asIso ((Scheme.ΓSpecIso R).inv ≫ φ.appTop)).commRingCatIsoToRingEquiv
  let e := (Space.globalFunctionsYonedaRingEquiv B integerBase hZ V).trans e₁.symm
  exact MulEquiv.isField hR e.toMulEquiv


/-- **`ω` is trivial on a fibre of genus one without rational tail**: `ω|_{X_s} ≅ ω_{X_s} ≅ 𝒪`
on the small étale site of a presentation `V` of the fibre `X_s` (Stacks 0E3K). -/
private theorem nonempty_modulePullback_fibre_iso_unit_of_genus_eq_one {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X)
    (ω : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
    (hωinv : Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ X.total.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ X.total.1 X.total.2).O)).property ω)
    (hω : CurveFamily.IsDualizingOnFibres B hZ X ω)
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
          ((BigFppfOver.toScheme B integerBase hZ).obj V) C) :
    Nonempty ((Space.modulePullback B integerBase hZ
        (ObjectProperty.homMk q : schemeSpace V ⟶ X.total)).obj ω ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ (yoneda.obj V)
          (isAlgebraicSpace_yoneda B integerBase hZ V)).O))) := by
  have hqP : IsPullback q (yoneda.map v) X.toBase.hom
      (yonedaEquiv.symm (X.residueFieldPoint s).value) := hq
  obtain ⟨hprop, hdim, hH0, hnodal⟩ :=
    C1590Private.fibre_properties_of_isPrestableCurveFamily hX (X.residueFieldPoint s) v q hqP
  let : ((BigFppfOver.toScheme B integerBase hZ).obj V).Over
      (Spec (.of (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s))) :=
    ⟨CurveFamily.fibreMap B hZ X _ v⟩
  have : IsProper (((BigFppfOver.toScheme B integerBase hZ).obj V) ↘
      Spec (.of (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s))) := hprop
  have : IsIso ((Scheme.ΓSpecIso (.of (((BigFppfOver.toScheme B integerBase hZ).obj
      X.base).residueField s))).inv ≫
        (((BigFppfOver.toScheme B integerBase hZ).obj V) ↘
        Spec (.of (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField
          s))).appTop) := hH0
  -- `ω|_V ≅ ω_V ≅ 𝒪_V` (Stacks 0E3K)
  have hnodal' : Stacks.Curves.HasAtWorstNodalSingularities
      (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s)
      ((BigFppfOver.toScheme B integerBase hZ).obj V) := hnodal
  obtain ⟨e₀⟩ := nonempty_dualizingSheafOverField_iso_unit_of_forall_not_isRationalTail
    (k := ((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueField s)
    hdim hnodal' htail hg
  obtain ⟨e₁⟩ := hω _ V v q hq
  have hqc : ((Space.modulePullback B integerBase hZ
      (ObjectProperty.homMk q : schemeSpace V ⟶ X.total)).obj ω).IsQuasicoherentOnSite :=
    Space.isQuasicoherentOnSite_modulePullback_of_isInvertible _ ω hωinv
  exact nonempty_modulePullback_iso_unit_of_zariski_iso_unit ω V q hqc (e₁ ≪≫ e₀)

/-- **The fibre of a base change maps to the fibre**: for `c : T ⟶ S` and `t ∈ T`, a presentation
`V'` of the fibre of `X_T` over `t` maps to a presentation `V` of the fibre of `X` over `c t`,
compatibly with the maps to `X_T` and `X`. -/
private theorem exists_schemeSpaceMap_comp_homMk_eq_of_isFibrePresentation {X : CurveFamily B hZ}
    {T : BigFppfOver B integerBase hZ} (c : T ⟶ X.base)
    (t : (BigFppfOver.toScheme B integerBase hZ).obj T) {V : BigFppfOver B integerBase hZ}
    {v : V ⟶ CurveFamily.residuePoint B hZ X ((BigFppfOver.toScheme B integerBase hZ).map c t)}
    {q : yoneda.obj V ⟶ X.total.obj}
    (hq : CurveFamily.IsFibrePresentation B hZ X _ v q)
    {V' : BigFppfOver B integerBase hZ} {v' : V' ⟶ CurveFamily.residuePoint B hZ (X.baseChange c) t}
    {q' : yoneda.obj V' ⟶ (X.baseChange c).total.obj}
    (hq' : CurveFamily.IsFibrePresentation B hZ (X.baseChange c) t v' q') :
    ∃ r : V' ⟶ V, schemeSpaceMap r ≫ (ObjectProperty.homMk q : schemeSpace V ⟶ X.total) =
      (ObjectProperty.homMk q' : schemeSpace V' ⟶ (X.baseChange c).total) ≫
        (X.baseChangeHom c).totalMap := by
  let ρ := Space.residueFieldObjectMap B integerBase hZ T X.base c t
  have hρ := Space.residueFieldObjectMap_comp B integerBase hZ T X.base c t
  have h₁ : (X.baseChangeHom c).totalMap.hom ≫ X.toBase.hom =
      (X.baseChange c).toBase.hom ≫ yoneda.map c :=
    congrArg (fun k => k.hom) (X.baseChangeHom c).cartesian.w
  have hcomm : (q' ≫ (X.baseChangeHom c).totalMap.hom) ≫ X.toBase.hom =
      yoneda.map (v' ≫ ρ) ≫ yoneda.map (CurveFamily.residuePointMap B hZ X _) := by
    have a₁ : (q' ≫ (X.baseChangeHom c).totalMap.hom) ≫ X.toBase.hom =
        q' ≫ ((X.baseChange c).toBase.hom ≫ yoneda.map c) :=
      (Category.assoc _ _ _).trans (congrArg (q' ≫ ·) h₁)
    have a₂ : q' ≫ ((X.baseChange c).toBase.hom ≫ yoneda.map c) =
        (yoneda.map v' ≫ yoneda.map (CurveFamily.residuePointMap B hZ (X.baseChange c) t)) ≫
          yoneda.map c :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ yoneda.map c) hq'.w)
    have a₃ : (yoneda.map v' ≫ yoneda.map (CurveFamily.residuePointMap B hZ (X.baseChange c) t)) ≫
        yoneda.map c =
          yoneda.map ((v' ≫ CurveFamily.residuePointMap B hZ (X.baseChange c) t) ≫ c) :=
      (congrArg (· ≫ yoneda.map c) (yoneda.map_comp _ _).symm).trans (yoneda.map_comp _ _).symm
    have a₄ : yoneda.map ((v' ≫ CurveFamily.residuePointMap B hZ (X.baseChange c) t) ≫ c) =
        yoneda.map (v' ≫ (ρ ≫ CurveFamily.residuePointMap B hZ X _)) :=
      congrArg yoneda.map ((Category.assoc _ _ _).trans (congrArg (v' ≫ ·) hρ.symm))
    have a₅ : yoneda.map (v' ≫ (ρ ≫ CurveFamily.residuePointMap B hZ X _)) =
        yoneda.map (v' ≫ ρ) ≫ yoneda.map (CurveFamily.residuePointMap B hZ X _) :=
      (congrArg yoneda.map (Category.assoc _ _ _).symm).trans (yoneda.map_comp _ _)
    exact a₁.trans (a₂.trans (a₃.trans (a₄.trans a₅)))
  let r₀ := hq.lift (q' ≫ (X.baseChangeHom c).totalMap.hom) (yoneda.map (v' ≫ ρ)) hcomm
  exact ⟨Yoneda.fullyFaithful.preimage r₀, ObjectProperty.hom_ext _
    ((congrArg (· ≫ q) (Yoneda.fullyFaithful.map_preimage r₀)).trans (hq.lift_fst _ _ _))⟩

/-- **A nonzero section of `ω` on a fibre of genus one without rational tail is a basis.** Let
`X_s` have genus one and no rational tail, `ω` an invertible module restricting on the fibres to
their dualizing sheaves, `c : T ⟶ S` and `t ∈ T` over `s`, and `V'` a presentation of the fibre of
`X_T` over `t`. Then every nonzero map `𝒪 ⟶ ω` on `V'`, pulled back from a map
`σ : 𝒪_{X_T} ⟶ ω|_{X_T}`, is an isomorphism: `ω|_{V'}` is pulled back from `ω|_{X_s} ≅ ω_{X_s} ≅ 𝒪`
(Stacks 0E3K), and `H⁰(V', 𝒪) = κ(t)` is a field. -/
theorem isIso_modulePullback_map_fibre_of_ne_zero {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X)
    (ω : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
    (hωinv : Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ X.total.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ X.total.1 X.total.2).O)).property ω)
    (hω : CurveFamily.IsDualizingOnFibres B hZ X ω)
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
    {T : BigFppfOver B integerBase hZ} (c : T ⟶ X.base)
    (t : (BigFppfOver.toScheme B integerBase hZ).obj T)
    (ht : (BigFppfOver.toScheme B integerBase hZ).map c t = s)
    {V' : BigFppfOver B integerBase hZ} {v' : V' ⟶ CurveFamily.residuePoint B hZ (X.baseChange c) t}
    {q' : yoneda.obj V' ⟶ (X.baseChange c).total.obj}
    (hq' : CurveFamily.IsFibrePresentation B hZ (X.baseChange c) t v' q')
    (σ : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ (X.baseChange c).total.1
          (X.baseChange c).total.2).O)) ⟶
        (Space.modulePullback B integerBase hZ (X.baseChangeHom c).totalMap).obj ω)
    (hσ : (Space.modulePullback B integerBase hZ
      (ObjectProperty.homMk q' : schemeSpace V' ⟶ (X.baseChange c).total)).map σ ≠ 0) :
    IsIso ((Space.modulePullback B integerBase hZ
      (ObjectProperty.homMk q' : schemeSpace V' ⟶ (X.baseChange c).total)).map σ) := by
  subst ht
  obtain ⟨e₂⟩ :=
    nonempty_modulePullback_fibre_iso_unit_of_genus_eq_one hX ω hωinv hω _ hq hg htail
  obtain ⟨r, hr⟩ := exists_schemeSpaceMap_comp_homMk_eq_of_isFibrePresentation c t hq hq'
  let e' : (Space.modulePullback B integerBase hZ
      (ObjectProperty.homMk q' : schemeSpace V' ⟶ (X.baseChange c).total)).obj
        ((Space.modulePullback B integerBase hZ (X.baseChangeHom c).totalMap).obj ω) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ (yoneda.obj V')
          (isAlgebraicSpace_yoneda B integerBase hZ V')).O)) :=
    (Space.modulePullbackCompIso B integerBase hZ _ _).app ω ≪≫
      eqToIso (congrArg (fun k => (Space.modulePullback B integerBase hZ k).obj ω) hr.symm) ≪≫
      ((Space.modulePullbackCompIso B integerBase hZ _ _).app ω).symm ≪≫
      (Space.modulePullback B integerBase hZ (schemeSpaceMap r)).mapIso e₂ ≪≫
      Space.modulePullbackUnitIso B integerBase hZ (schemeSpaceMap r)
  have hqP' : IsPullback q' (yoneda.map v') (X.baseChange c).toBase.hom
      (yonedaEquiv.symm ((X.baseChange c).residueFieldPoint t).value) := hq'
  obtain ⟨-, -, hH0', -⟩ :=
    C1590Private.fibre_properties_of_isPrestableCurveFamily
      (CurveFamily.isPrestableCurveFamily_of_hom (X.baseChangeHom c) hX)
      ((X.baseChange c).residueFieldPoint t) v' q' hqP'
  have hfield := isField_globalFunctions_yoneda_of_isIso_appTop
    (Field.toIsField (((BigFppfOver.toScheme B integerBase hZ).obj T).residueField t))
    (CurveFamily.fibreMap B hZ (X.baseChange c) t v') hH0'
  exact isIso_of_ne_zero_between_trivial (Z := schemeSpace V') hfield
    (Space.modulePullbackUnitIso B integerBase hZ
      (ObjectProperty.homMk q' : schemeSpace V' ⟶ (X.baseChange c).total)) e' _ hσ

end C1764Prereq

end AlgebraicGeometry
