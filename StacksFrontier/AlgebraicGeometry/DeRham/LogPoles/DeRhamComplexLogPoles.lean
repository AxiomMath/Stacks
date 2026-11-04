module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogResidueSequence
public import StacksCore.Tactic.StacksAttribute

/-!
# The de Rham complex of log poles

Let `f : X ⟶ S` be a morphism of schemes and let `Y ⊆ X` be an effective Cartier divisor, cut out
by `I`, for which the de Rham complex of log poles is defined ([Stacks, Tag 0FMV],
`AlgebraicGeometry.Scheme.Hom.HasLogPolesDeRhamComplex`). [Stacks, Tag 0FUA] names the complex
`Ω^•_{X/S}(log Y)` of [Stacks, Tag 0FMW] the *de Rham complex of log poles for `Y ⊆ X` over `S`*.
This file constructs it as a complex of sheaves of `f⁻¹𝒪_S`-modules on `X`, in the category in
which the relative de Rham complex `AlgebraicGeometry.Scheme.Hom.deRhamComplex` lives.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.logDBaseHom`: the differential
  `Ω^p_{X/S}(log Y) ⟶ Ω^{p+1}_{X/S}(log Y)`, as a morphism of sheaves of `f⁻¹𝒪_S`-modules.
* `AlgebraicGeometry.Scheme.Hom.deRhamComplexLogPoles`: the de Rham complex of log poles
  `Ω^•_{X/S}(log Y)`.
* `AlgebraicGeometry.Scheme.Hom.deRhamComplexLogPolesInclusion`: the inclusion
  `Ω^•_{X/S} ⟶ Ω^•_{X/S}(log Y)` of the forms with no pole, a monomorphism of complexes
  (`AlgebraicGeometry.Scheme.Hom.mono_deRhamComplexLogPolesInclusion`).
* `AlgebraicGeometry.Scheme.Hom.deRhamComplexLogPolesAbIso`: forgetting the module structure gives
  the complex of abelian sheaves `AlgebraicGeometry.Scheme.Hom.logDeRhamComplex` of the residue
  sequence `AlgebraicGeometry.Scheme.Hom.logResidueShortComplex_shortExact` ([Stacks, Tag 0FMW]).
* `AlgebraicGeometry.Scheme.Hom.deRhamComplexLogPolesInt`: the same complex indexed by `ℤ`, in the
  shape of `AlgebraicGeometry.SheafOfModules.deRhamComplexInt`, with its inclusion
  `AlgebraicGeometry.Scheme.Hom.deRhamComplexLogPolesIntInclusion`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.logD_baseSMul`: the differential is `f⁻¹𝒪_S`-linear.

On an open `U` carrying a trivialization of the ideal sheaf with local equation `t`, write
`ω + dlog t ∧ η` for the section `Stacks.Divisors.IdealTrivialization.logPolesChartForm`:

* `Stacks.Divisors.IdealTrivialization.exists_map_eq_logPolesChartForm`: every local section is,
  near every point, of the form `ω + dlog t ∧ η`;
* `Stacks.Divisors.IdealTrivialization.logPolesFormsInclusion_eq_logPolesChartForm`: the forms
  with no pole are the `ω + dlog t ∧ 0`;
* `Stacks.Divisors.IdealTrivialization.logPolesChartForm_eq_zero_iff`: `ω + dlog t ∧ η = 0`
  exactly when `t ω + dt ∧ η = 0`, the relations of the pair model
  `Stacks.LogPoles.deRhamComplexLogPoles` of the affine case;
* `Stacks.Divisors.IdealTrivialization.logD_logPolesChartForm`: the differential is
  `d(ω + dlog t ∧ η) = dω - dlog t ∧ dη`, the differential `(ω, η) ↦ (dω, -dη)` of the pair model;
* `Stacks.Divisors.IdealTrivialization.logRes_logPolesChartForm`: the residue is `η|_Y`.

## References

* [Stacks Project, Tag 0FUA](https://stacks.math.columbia.edu/tag/0FUA)
* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW)
* [Stacks Project, Tag 0FMV](https://stacks.math.columbia.edu/tag/0FMV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Perfect.AbelianFraction

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The ring sheaf `f⁻¹𝒪_S` over which `Ω^•_{X/S}` is a complex. -/
abbrev baseRingSheaf : Sheaf (Opens.grothendieckTopology X.carrier) RingCat.{u} :=
  AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)

/-- The structural map `f⁻¹𝒪_S ⟶ 𝒪_X`, on the underlying sheaves of rings. -/
abbrev baseRingHom : baseRingSheaf f ⟶ X.ringCatSheaf :=
  AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap f)

/-- A local section of `f⁻¹𝒪_S`, read as a local function on `X` through the structural map. -/
abbrev baseFn {V : X.Opens} (s : (baseRingSheaf f).obj.obj (op V)) : Γ(X, V) :=
  (baseRingHom f).hom.app (op V) s

/-- The relative de Rham differential is `f⁻¹𝒪_S`-linear on sections. -/
theorem deRhamD_baseSMul (p : ℕ) (V : X.Opens) (s : (baseRingSheaf f).obj.obj (op V))
    (β : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    deRhamD f p V (baseFn f s • β) = baseFn f s • deRhamD f p V β :=
  (((deRhamComplex f).d p (p + 1)).val.app (op V)).hom.map_smul s β

variable {f}

/-- `d s ∧ β = 0` for a local section `s` of `f⁻¹𝒪_S`. -/
theorem exactWedge_baseFn (p : ℕ) (V : X.Opens) (s : (baseRingSheaf f).obj.obj (op V))
    (β : Γ(relativeDifferentialForms f (p : ℤ), V)) :
    exactWedge f p V (baseFn f s) β = 0 := by
  have h := deRhamD_baseSMul f p V s β
  rwa [deRhamD_smul, add_eq_right] at h

/-- The structural map commutes with restriction to a smaller open. -/
theorem baseFn_res {V V' : X.Opens} (h : V' ≤ V) (s : (baseRingSheaf f).obj.obj (op V)) :
    X.presheaf.map (homOfLE h).op (baseFn f s) =
      baseFn f ((baseRingSheaf f).obj.map (homOfLE h).op s) :=
  (ConcreteCategory.congr_hom ((baseRingHom f).hom.naturality (homOfLE h).op) s).symm

variable {I : X.IdealSheafData} (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
  (hlog : f.HasLogPolesDeRhamComplex I)

/-- **The differential of forms with logarithmic poles is `f⁻¹𝒪_S`-linear.** -/
theorem logD_baseSMul {p : ℕ} {W : X.Opens} (s : (baseRingSheaf f).obj.obj (op W))
    (φ : (logPolesForms f I p).val.obj (op W)) :
    logD hI hlog ((show X.ringCatSheaf.obj.obj (op W) from baseFn f s) • φ) =
      (show X.ringCatSheaf.obj.obj (op W) from baseFn f s) • logD hI hlog φ := by
  refine logD_eq hI hlog _ _ fun W' hW' b V' hV' a => ?_
  have key := leibnizRel_logDValue hI hlog φ hW' b V' hV' a
  rw [leibnizRHS] at key
  have hres : X.presheaf.map (homOfLE hV').op (X.presheaf.map (homOfLE hW').op (baseFn f s)) =
      X.presheaf.map (homOfLE (hV'.trans hW')).op (baseFn f s) := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  rw [logEval_smul_left, logEval_logD, forms_map_smul, hres, leibnizRHS,
    logEval_smul_left, logEval_smul_left, baseFn_res, deRhamD_smul, exactWedge_baseFn,
    zero_add, exactWedge_smul_right, smul_comm, key]
  module

/-! ### The complex of sheaves of `f⁻¹𝒪_S`-modules -/

variable (f I)

/-- The sheaf `Ω^p_{X/S}(log Y)`, read as a sheaf of `f⁻¹𝒪_S`-modules along the structural map. -/
abbrev logPolesFormsBase (p : ℕ) : _root_.SheafOfModules.{u} (baseRingSheaf f) :=
  (_root_.SheafOfModules.restrictScalars (baseRingHom f)).obj (logPolesForms f I p)

/-- **The differential `d : Ω^p_{X/S}(log Y) ⟶ Ω^{p+1}_{X/S}(log Y)`**, a morphism of sheaves of
`f⁻¹𝒪_S`-modules. -/
def logDBaseHom (p : ℕ) : logPolesFormsBase f I p ⟶ logPolesFormsBase f I (p + 1) :=
  ⟨PresheafOfModules.homMk (logDPresheafHom f I hI hlog p) fun W s φ =>
    logD_baseSMul hI hlog (W := W.unop) s φ⟩

/-- On sections the differential is `AlgebraicGeometry.Scheme.Hom.logD`. -/
theorem logDBaseHom_app (p : ℕ) (W : X.Opens) (φ : (logPolesForms f I p).val.obj (op W)) :
    (logDBaseHom f I hI hlog p).val.app (op W) φ = logD hI hlog φ :=
  rfl

/-- `d ∘ d = 0`. -/
theorem logDBaseHom_comp_logDBaseHom (p : ℕ) :
    logDBaseHom f I hI hlog p ≫ logDBaseHom f I hI hlog (p + 1) = 0 := by
  refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W =>
    ModuleCat.hom_ext (LinearMap.ext fun φ => ?_))
  exact logD_logD hI hlog (W := W.unop) φ

/-- **The de Rham complex of log poles** `Ω^•_{X/S}(log Y)` for a
morphism of schemes `f : X ⟶ S` and an effective Cartier divisor `Y ⊆ X`, cut out by `I`, for
which the de Rham complex of log poles is defined ([Stacks, Tag 0FMV]): the complex of sheaves
of `f⁻¹𝒪_S`-modules on `X` constructed in [Stacks, Tag 0FMW]. -/
@[stacks 0FUA "the complex of sheaves of f⁻¹𝒪_S-modules on X, for an arbitrary morphism of \
schemes and an arbitrary effective Cartier divisor for which the de Rham complex of log poles is \
defined (0FMV)"]
def deRhamComplexLogPoles :
    CochainComplex (_root_.SheafOfModules.{u} (baseRingSheaf f)) ℕ :=
  CochainComplex.of (logPolesFormsBase f I) (logDBaseHom f I hI hlog)
    (logDBaseHom_comp_logDBaseHom f I hI hlog)

/-- The degree-`p` term is `Ω^p_{X/S}(log Y)`, read as a sheaf of `f⁻¹𝒪_S`-modules. -/
theorem deRhamComplexLogPoles_X (p : ℕ) :
    (deRhamComplexLogPoles f I hI hlog).X p = logPolesFormsBase f I p :=
  rfl

/-- The differential out of degree `p` is `AlgebraicGeometry.Scheme.Hom.logDBaseHom`. -/
theorem deRhamComplexLogPoles_d (p : ℕ) :
    (deRhamComplexLogPoles f I hI hlog).d p (p + 1) = logDBaseHom f I hI hlog p :=
  CochainComplex.of_d _ _ p

/-- **The forms with no pole form a subcomplex**: the inclusion `Ω^•_{X/S} ⟶ Ω^•_{X/S}(log Y)`
is a map of complexes of sheaves of `f⁻¹𝒪_S`-modules. -/
def deRhamComplexLogPolesInclusion : f.deRhamComplex ⟶ deRhamComplexLogPoles f I hI hlog where
  f p := (_root_.SheafOfModules.restrictScalars (baseRingHom f)).map (logPolesFormsInclusion f I p)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [deRhamComplexLogPoles_d]
    refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W =>
      ModuleCat.hom_ext (LinearMap.ext fun ω => ?_))
    exact logD_logPolesFormsInclusion hI hlog (W := W.unop) ω

/-- In degree `p` the inclusion is `AlgebraicGeometry.Scheme.Hom.logPolesFormsInclusion`. -/
theorem deRhamComplexLogPolesInclusion_f (p : ℕ) :
    (deRhamComplexLogPolesInclusion f I hI hlog).f p =
      (_root_.SheafOfModules.restrictScalars (baseRingHom f)).map
        (logPolesFormsInclusion f I p) :=
  rfl

/-- The forms with no pole are a subcomplex: the inclusion is a monomorphism of complexes of
sheaves of `f⁻¹𝒪_S`-modules. -/
instance mono_deRhamComplexLogPolesInclusion :
    Mono (deRhamComplexLogPolesInclusion f I hI hlog) := by
  refine HomologicalComplex.mono_of_mono_f _ fun p => ?_
  have hmono : Mono (logInclusionMap f I hI hlog) :=
    (logResidueShortComplex_shortExact f I hI hlog).mono_f
  have hp : Mono ((HomologicalComplex.eval _ _ p).map (logInclusionMap f I hI hlog)) :=
    inferInstance
  exact (_root_.SheafOfModules.toSheaf (baseRingSheaf f)).mono_of_mono_map hp

/-- Forgetting the `f⁻¹𝒪_S`-module structure, the de Rham complex of log poles is the complex of
sheaves of abelian groups `AlgebraicGeometry.Scheme.Hom.logDeRhamComplex` of [Stacks, Tag 0FMW]. -/
def deRhamComplexLogPolesAbIso :
    ((_root_.SheafOfModules.toSheaf (baseRingSheaf f)).mapHomologicalComplex _).obj
        (deRhamComplexLogPoles f I hI hlog) ≅ logDeRhamComplex f I hI hlog :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) fun i j hij => by
    obtain rfl : i + 1 = j := hij
    simp only [Iso.refl_hom, Functor.mapHomologicalComplex_obj_d, deRhamComplexLogPoles_d,
      logDeRhamComplex_d]
    rfl

/-- The de Rham complex of log poles, extended by zero to a complex indexed by `ℤ`, in the shape
of `AlgebraicGeometry.SheafOfModules.deRhamComplexInt`. -/
abbrev deRhamComplexLogPolesInt :
    CochainComplex (_root_.SheafOfModules.{u} (baseRingSheaf f)) ℤ :=
  (deRhamComplexLogPoles f I hI hlog).extend ComplexShape.embeddingUpNat

/-- The inclusion `Ω^•_{X/S} ⟶ Ω^•_{X/S}(log Y)` of complexes indexed by `ℤ`. -/
abbrev deRhamComplexLogPolesIntInclusion :
    AlgebraicGeometry.SheafOfModules.deRhamComplexInt (deRhamAlgebras f)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (deRhamAlgebras f)) ⟶
      deRhamComplexLogPolesInt f I hI hlog :=
  HomologicalComplex.extendMap (deRhamComplexLogPolesInclusion f I hI hlog)
    ComplexShape.embeddingUpNat

end AlgebraicGeometry.Scheme.Hom

/-! ### Agreement with the local construction on a chart -/

namespace Stacks.Divisors.IdealTrivialization

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} {f : X ⟶ S} {I : X.IdealSheafData} {U : X.Opens}
  (e : IdealTrivialization I U)

/-- The local equation is the function of the basis element of the ideal sheaf. -/
theorem equationAt_eq_idealFn {W : X.Opens} (hW : W ≤ U) :
    e.equationAt hW = idealFn (e.basisLE hW) :=
  rfl

/-- `t ω + dt ∧ η` vanishes on `Y`, for `t` the local equation. -/
theorem formRes_smul_add_exactWedge {p : ℕ} {W : X.Opens} (hW : W ≤ U)
    (ω : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), W))
    (η : Γ(relativeDifferentialForms f (p : ℤ), W)) :
    formRes I.subschemeι ((p + 1 : ℕ) : ℤ) W
      (e.equationAt hW • ω + exactWedge f p W (e.equationAt hW) η) = 0 := by
  rw [formRes_add, e.equationAt_eq_idealFn hW, formRes_idealFn_smul, formRes_exactWedge_idealFn,
    add_zero]

/-- **The form `ω + dlog t ∧ η` with a logarithmic pole**, over an open `W` inside a chart `U`
of the ideal sheaf with local equation `t`: the section `t⁻¹(t ω + dt ∧ η)` of
`Ω^{p+1}_{X/S}(log Y)`. -/
def logPolesChartForm {p : ℕ} {W : X.Opens} (hW : W ≤ U)
    (ω : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), W))
    (η : Γ(relativeDifferentialForms f (p : ℤ), W)) :
    (logPolesForms f I (p + 1)).val.obj (op W) :=
  e.logOfCoord hW _ (e.formRes_smul_add_exactWedge hW ω η)

/-- A form with logarithmic poles over an open inside the chart is `t⁻¹` times its value at the
basis element. -/
theorem logOfCoord_logEval_basisLE {p : ℕ} {W : X.Opens} (hW : W ≤ U)
    (φ : (logPolesForms f I p).val.obj (op W)) :
    e.logOfCoord hW (logEval f I φ (le_refl W) (e.basisLE hW))
      (formRestriction_logEval φ _ _) = φ := by
  refine logEval_ext fun W' h a => ?_
  rw [logEval_logOfCoord, e.logEval_eq_coord_smul φ h (h.trans hW) a,
    ← e.logEval_basisLE_res φ (le_refl W) hW h]

/-- **On a chart, `Ω^{p+1}_{X/S}(log Y)` is generated by `Ω^{p+1}_{X/S}` and
`dlog t ∧ Ω^p_{X/S}`**: every local section is, near every point, of the form `ω + dlog t ∧ η`. -/
theorem exists_map_eq_logPolesChartForm {p : ℕ} {W : X.Opens} (hW : W ≤ U)
    (φ : (logPolesForms f I (p + 1)).val.obj (op W)) (x : X) (hx : x ∈ W) :
    ∃ (V : X.Opens) (hV : V ≤ W), x ∈ V ∧
      ∃ (ω : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), V))
        (η : Γ(relativeDifferentialForms f (p : ℤ), V)),
        (logPolesForms f I (p + 1)).val.map (homOfLE hV).op φ =
          e.logPolesChartForm (hV.trans hW) ω η := by
  obtain ⟨V, hV, hxV, ω, η, hωη⟩ := e.exists_local_eq_smul_add_exactWedge hW p
    (logEval f I φ (le_refl W) (e.basisLE hW)) (formRestriction_logEval φ _ _) x hx
  refine ⟨V, hV, hxV, ω, η, ?_⟩
  rw [← e.logOfCoord_logEval_basisLE (hV.trans hW)
    ((logPolesForms f I (p + 1)).val.map (homOfLE hV).op φ)]
  refine e.logOfCoord_congr (hV.trans hW) ?_ _ _
  rw [logEval_res, e.logEval_basisLE_res φ (le_refl W) hW hV]
  exact hωη

/-- **The forms with no pole** are the forms `ω + dlog t ∧ 0`. -/
theorem logPolesFormsInclusion_eq_logPolesChartForm {p : ℕ} {W : X.Opens} (hW : W ≤ U)
    (ω : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), W)) :
    (logPolesFormsInclusion f I (p + 1)).val.app (op W) ω = e.logPolesChartForm hW ω 0 := by
  refine logEval_ext fun W' h a => ?_
  rw [logEval_logPolesFormsInclusion]
  change _ = e.coordLE (h.trans hW) a • (relativeDifferentialForms f ((p + 1 : ℕ) : ℤ)).presheaf.map
    (homOfLE h).op (e.equationAt hW • ω + exactWedge f p W (e.equationAt hW) 0)
  rw [exactWedge_zero_right, add_zero, forms_map_smul, smul_smul, e.equationAt_res hW h,
    ← e.idealFn_eq_mul (h.trans hW) a]

/-- `ω + dlog t ∧ η = 0` exactly when `t ω + dt ∧ η = 0`. -/
theorem logPolesChartForm_eq_zero_iff {p : ℕ} {W : X.Opens} (hW : W ≤ U)
    (ω : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), W))
    (η : Γ(relativeDifferentialForms f (p : ℤ), W)) :
    e.logPolesChartForm hW ω η = 0 ↔
      e.equationAt hW • ω + exactWedge f p W (e.equationAt hW) η = 0 := by
  refine ⟨fun h => ?_, fun h =>
    (e.logOfCoord_congr hW h _ (formRes_zero _ _ _)).trans (e.logOfCoord_zero hW _)⟩
  rw [← e.logEval_logOfCoord_basisLE hW _ (e.formRes_smul_add_exactWedge hW ω η)]
  change logEval f I (e.logPolesChartForm hW ω η) (le_refl W) (e.basisLE hW) = 0
  rw [h]
  exact logEval_zero _ _

variable (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) (hlog : f.HasLogPolesDeRhamComplex I)

/-- On a chart, the differential is `d(ω + dlog t ∧ η) = dω - dlog t ∧ dη`. -/
theorem logD_logPolesChartForm {p : ℕ} {W : X.Opens} (hW : W ≤ U)
    (ω : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), W))
    (η : Γ(relativeDifferentialForms f (p : ℤ), W)) :
    logD hI hlog (e.logPolesChartForm hW ω η) =
      e.logPolesChartForm hW (deRhamD f (p + 1) W ω) (-deRhamD f p W η) := by
  have hz : logEval f I (e.logPolesChartForm hW ω η) (le_refl W) (e.basisLE hW) =
      e.equationAt hW • ω + exactWedge f p W (e.equationAt hW) η :=
    e.logEval_logOfCoord_basisLE hW _ _
  have hd : e.IsChartDecomp hW
      (logEval f I (e.logPolesChartForm hW ω η) (le_refl W) (e.basisLE hW))
      ω (exactWedge f p W (e.equationAt hW) η) := by
    rw [hz]
    refine ⟨rfl, exactWedge_exactWedge_self p W _ η, ?_, ?_⟩
    · rw [deRhamD_exactWedge, exactWedge_neg_right, exactWedge_exactWedge_self, neg_zero]
    · rw [deRhamD_exactWedge, formRes_neg, e.equationAt_eq_idealFn hW,
        formRes_exactWedge_idealFn, neg_zero]
  have key := e.logD_map_eq_logOfCoord hI hlog (e.logPolesChartForm hW ω η) (le_refl W) hW hd
  have hmap : (logPolesForms f I (p + 1)).val.map (homOfLE (le_refl W)).op
      (e.logPolesChartForm hW ω η) = e.logPolesChartForm hW ω η := by
    rw [show homOfLE (le_refl W) = 𝟙 W from Subsingleton.elim _ _, op_id,
      PresheafOfModules.map_id]
    rfl
  rw [hmap] at key
  refine key.trans (e.logOfCoord_congr hW ?_ _ _)
  rw [deRhamD_exactWedge, exactWedge_neg_right]

/-- On a chart, the residue is `Res(ω + dlog t ∧ η) = η|_Y`. -/
theorem logRes_logPolesChartForm {p : ℕ} {W : X.Opens} (hW : W ≤ U)
    (ω : Γ(relativeDifferentialForms f ((p + 1 : ℕ) : ℤ), W))
    (η : Γ(relativeDifferentialForms f (p : ℤ), W)) :
    logRes hI hlog (e.logPolesChartForm hW ω η) = formRes I.subschemeι (p : ℤ) W η := by
  have hd : e.IsResidueDecomp (e.logPolesChartForm hW ω η) (le_refl W) hW ω η :=
    e.logEval_logOfCoord_basisLE hW _ _
  have key := logRes_map_eq hI hlog e (e.logPolesChartForm hW ω η) (le_refl W) hW hd
  rwa [show homOfLE (le_refl W) = 𝟙 W from Subsingleton.elim _ _, op_id,
    CategoryTheory.Functor.map_id] at key

end Stacks.Divisors.IdealTrivialization

end
