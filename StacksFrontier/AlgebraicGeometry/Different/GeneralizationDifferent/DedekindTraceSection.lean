module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.GeneralizationDifferent.DedekindTraceElement
public import StacksFrontier.AlgebraicGeometry.Different.GeneralizationDifferent.TheDifferent
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeTraceSection
public import StacksFrontier.AlgebraicGeometry.Different.GeneralizationDifferent.DedekindComparison
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.AnnihilatorAffineTilde

/-!
# The extension of the trace element when the Dedekind different is defined

Let `f : Y ⟶ X` be a locally quasi-finite morphism of locally Noetherian schemes.  A global
section `s` of the relative dualizing module `ω_{Y/X}` *is the trace element on* a chart
`V ⊆ f⁻¹ U` of affine opens if, when the coordinate-ring map of the chart is flat, `s|_V` is the
trace element of that map.  This file shows that this condition is local: it may be checked on
principal opens of the source chart and does not change when the base chart is shrunk to a
principal open.

For affine `X` and `Y` with global sections `A → B` for which the Dedekind different is defined,
it follows that a section is the trace element on every chart, that is, extends the trace
element `τ_{V/X}` of the flat locus, exactly when its image `φ ∈ Hom_A(B, A)` induces the trace of
the generic fibre.  Hence such an extension exists exactly when `1` lies in the complementary
module `L_{B/A}`.

## Main definitions

* `Stacks.Discriminant.IsTraceSectionOn`: the section is the trace element on a chart.

## Main results

* `Stacks.Discriminant.IsTraceSectionOn.of_basicOpen_cover`: the condition is local on the
  source chart.
* `Stacks.Discriminant.isTraceSectionOn_basicOpen_base_iff`: the base chart may be shrunk to a
  principal open.
* `Stacks.Discriminant.nonempty_generalizedTraceSection_iff_of_isAffine`: for affine `X` and `Y`
  with the Dedekind different of `Γ(X, ⊤) → Γ(Y, ⊤)` defined, the trace element `τ_{V/X}` comes
  from a global section exactly when `1 ∈ L_{B/A}`.

## References

* [Stacks Project, Tag 0BWN](https://stacks.math.columbia.edu/tag/0BWN)
* [Stacks Project, Tag 0BWM](https://stacks.math.columbia.edu/tag/0BWM)
* [Stacks Project, Tag 0BT2](https://stacks.math.columbia.edu/tag/0BT2)
* [Stacks Project, Tag 0BT9](https://stacks.math.columbia.edu/tag/0BT9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped AlgebraicGeometry TensorProduct

universe u

namespace Stacks.Discriminant

open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

attribute [local instance] algebraDualModule Module.finitePresentation_of_finite

variable {X Y : Scheme.{u}} {f : Y ⟶ X}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyQuasiFinite f]

/-- A global section `s` of the relative dualizing module *is the trace element on* the chart
`V ⊆ f⁻¹ U` when, if the coordinate-ring map of the chart is flat, the image of `s|_V` in the
algebraic relative dualizing module of the chart is a trace element, for every finite-open
factorization. -/
def IsTraceSectionOn (ω : RelativeDualizingModuleData f) (s : Γ(ω.sheaf, ⊤)) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) : Prop :=
  letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  letI : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  ∀ hflat : Module.Flat Γ(X, U.1) Γ(Y, V.1),
    letI : Module.Flat Γ(X, U.1) Γ(Y, V.1) := hflat
    letI : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
      RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
    ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1),
      IsTraceElement.{u, u, u, u, u, u} F
        (ω.localEquiv U V hVU F (restrictₗ ω.sheaf (show V.1 ≤ ⊤ from le_top) s))

/-- A section extends the trace element of the flat locus exactly when it is the trace element on
every chart. -/
theorem nonempty_generalizedTraceSection_iff (ω : RelativeDualizingModuleData f) :
    Nonempty (GeneralizedTraceSection ω) ↔
      ∃ s : Γ(ω.sheaf, ⊤), ∀ (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1),
        IsTraceSectionOn ω s U V hVU :=
  ⟨fun ⟨τ⟩ => ⟨τ.sect, τ.isTraceElement_localEquiv⟩, fun ⟨s, hs⟩ => ⟨⟨s, hs⟩⟩⟩

/-- Being the trace element on a chart is invariant under replacing the base and source charts
by equal ones, whatever the proofs of `V ≤ f⁻¹ U` used. -/
theorem IsTraceSectionOn.congr {ω : RelativeDualizingModuleData f} {s : Γ(ω.sheaf, ⊤)}
    {U U' : X.affineOpens} {V V' : Y.affineOpens} (hU : U = U') (hV : V = V')
    (h : V.1 ≤ f ⁻¹ᵁ U.1) (h' : V'.1 ≤ f ⁻¹ᵁ U'.1) :
    IsTraceSectionOn ω s U V h ↔ IsTraceSectionOn ω s U' V' h' := by
  subst hU hV
  rfl

/-! ### The trace element of a flat chart, as a section -/

/-- The section of `ω_{Y/X}` over the source of a flat chart which is the trace element of the
chart. -/
def chartTraceSection (ω : RelativeDualizingModuleData f) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (hflat : letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
      Module.Flat Γ(X, U.1) Γ(Y, V.1)) : Γ(ω.sheaf, V.1) :=
  letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  letI : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  letI : Module.Flat Γ(X, U.1) Γ(Y, V.1) := hflat
  letI : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
  letI F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1) :=
    Classical.choice (ω.factorization U V hVU)
  (ω.localEquiv U V hVU F).symm (dualizingModule.traceCandidate F)

/-- On a flat chart, for every finite-open factorization `F`, the trace section of the chart is
sent by the local identification `ω.localEquiv` of `F` to the trace candidate of `F`. -/
theorem localEquiv_chartTraceSection (ω : RelativeDualizingModuleData f) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (hflat : letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
      Module.Flat Γ(X, U.1) Γ(Y, V.1)) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    letI : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
    letI : Module.Flat Γ(X, U.1) Γ(Y, V.1) := hflat
    letI : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
      RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
    ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1),
      ω.localEquiv U V hVU F (chartTraceSection ω U V hVU hflat) =
        dualizingModule.traceCandidate F := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  let : Module.Flat Γ(X, U.1) Γ(Y, V.1) := hflat
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
  intro F
  let G : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1) :=
    Classical.choice (ω.factorization U V hVU)
  change ω.localEquiv U V hVU F
    ((ω.localEquiv U V hVU G).symm (dualizingModule.traceCandidate G)) = _
  rw [ω.localEquiv_natural U V hVU G F]
  simpa using dualizingModuleEquiv_traceCandidate G F

/-- On a flat chart, a section is the trace element exactly when it restricts to the chart's
trace section. -/
theorem isTraceSectionOn_iff (ω : RelativeDualizingModuleData f) (s : Γ(ω.sheaf, ⊤))
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    IsTraceSectionOn ω s U V hVU ↔
      ∀ hflat, restrictₗ ω.sheaf (show V.1 ≤ ⊤ from le_top) s =
        chartTraceSection ω U V hVU hflat := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  refine forall_congr' fun hflat => ?_
  let : Module.Flat Γ(X, U.1) Γ(Y, V.1) := hflat
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
  let G : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1) :=
    Classical.choice (ω.factorization U V hVU)
  constructor
  · intro h
    refine (ω.localEquiv U V hVU G).injective ?_
    rw [localEquiv_chartTraceSection ω U V hVU hflat G]
    exact (isTraceElement_iff_eq_traceCandidate G _).mp (h G)
  · intro h F
    rw [h, localEquiv_chartTraceSection ω U V hVU hflat F]
    exact isTraceElement_traceCandidate F

/-! ### Shrinking the charts -/

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyQuasiFinite f] in
/-- A principal open of the source of a flat chart gives a flat chart. -/
theorem flat_basicOpen_source (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (g : Γ(Y, V.1))
    (hflat : letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
      Module.Flat Γ(X, U.1) Γ(Y, V.1)) :
    letI : Algebra Γ(X, U.1) Γ(Y, Y.basicOpen g) :=
      (f.appLE U (Y.basicOpen g) ((Y.basicOpen_le g).trans hVU)).hom.toAlgebra
    Module.Flat Γ(X, U.1) Γ(Y, Y.basicOpen g) := by
  let W : Y.affineOpens := ⟨Y.basicOpen g, V.2.basicOpen g⟩
  have hWU : W.1 ≤ f ⁻¹ᵁ U.1 := (Y.basicOpen_le g).trans hVU
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(Y, W.1) := (f.appLE U W hWU).hom.toAlgebra
  let : Algebra Γ(Y, V.1) Γ(Y, W.1) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom.toAlgebra
  let : IsLocalization.Away g Γ(Y, W.1) := V.2.isLocalization_basicOpen g
  let : IsScalarTower Γ(X, U.1) Γ(Y, V.1) Γ(Y, W.1) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (f.appLE_map hVU (homOfLE (Y.basicOpen_le g)).op).symm)
  let : Module.Flat Γ(X, U.1) Γ(Y, V.1) := hflat
  let : Module.Flat Γ(Y, V.1) Γ(Y, W.1) := IsLocalization.flat (Γ(Y, W.1)) (Submonoid.powers g)
  exact Module.Flat.trans Γ(X, U.1) Γ(Y, V.1) Γ(Y, W.1)

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyQuasiFinite f] in
/-- Shrinking the base chart of a chart to a principal open containing the image of the source
does not change flatness of the coordinate-ring map. -/
theorem flat_basicOpen_base_iff (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (a : Γ(X, U.1)) (hVa : V.1 ≤ f ⁻¹ᵁ (X.basicOpen a)) :
    @Module.Flat Γ(X, U.1) Γ(Y, V.1) _ _ (f.appLE U V hVU).hom.toAlgebra.toModule ↔
      @Module.Flat Γ(X, X.basicOpen a) Γ(Y, V.1) _ _
        (f.appLE (X.basicOpen a) V hVa).hom.toAlgebra.toModule := by
  let Ua : X.affineOpens := ⟨X.basicOpen a, U.2.basicOpen a⟩
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : Algebra Γ(X, Ua.1) Γ(Y, V.1) := (f.appLE Ua V hVa).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(X, Ua.1) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom.toAlgebra
  let : IsLocalization.Away a Γ(X, Ua.1) := U.2.isLocalization_basicOpen a
  let : IsScalarTower Γ(X, U.1) Γ(X, Ua.1) Γ(Y, V.1) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (f.map_appLE hVa (homOfLE (X.basicOpen_le a)).op).symm)
  exact (Module.flat_iff_of_isLocalization Γ(X, Ua.1) (Submonoid.powers a) Γ(Y, V.1)).symm

/-- **Shrinking the source chart to a principal open.** The trace section of a flat chart
restricts to the trace section of a principal open of its source. -/
theorem chartTraceSection_sourceRestrict (ω : RelativeDualizingModuleData f)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (g : Γ(Y, V.1))
    (hflat : letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
      Module.Flat Γ(X, U.1) Γ(Y, V.1)) :
    restrictₗ ω.sheaf (Y.basicOpen_le g) (chartTraceSection ω U V hVU hflat) =
      chartTraceSection ω U ⟨Y.basicOpen g, V.2.basicOpen g⟩ ((Y.basicOpen_le g).trans hVU)
        (flat_basicOpen_source U V hVU g hflat) := by
  set W : Y.affineOpens := ⟨Y.basicOpen g, V.2.basicOpen g⟩
  set hWU : W.1 ≤ f ⁻¹ᵁ U.1 := (Y.basicOpen_le g).trans hVU
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  let : Module.Flat Γ(X, U.1) Γ(Y, V.1) := hflat
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
  let : Algebra Γ(X, U.1) Γ(Y, W.1) := (f.appLE U W hWU).hom.toAlgebra
  let : Algebra Γ(Y, V.1) Γ(Y, W.1) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom.toAlgebra
  let : IsNoetherianRing Γ(Y, W.1) := IsLocallyNoetherian.component_noetherian W
  let : IsLocalization.Away g Γ(Y, W.1) := V.2.isLocalization_basicOpen g
  let : IsScalarTower Γ(X, U.1) Γ(Y, V.1) Γ(Y, W.1) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (f.appLE_map hVU (homOfLE (Y.basicOpen_le g)).op).symm)
  let : Module.Flat Γ(X, U.1) Γ(Y, W.1) := flat_basicOpen_source U V hVU g hflat
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, W.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 W.2 hWU)
  let F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1) :=
    Classical.choice (ω.factorization U V hVU)
  let G : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, W.1) :=
    Classical.choice (ω.factorization U W hWU)
  let : Module Γ(Y, V.1) (dualizingModule G) :=
    Module.compHom (dualizingModule G) (algebraMap Γ(Y, V.1) Γ(Y, W.1))
  let : IsScalarTower Γ(Y, V.1) Γ(Y, W.1) (dualizingModule G) :=
    IsScalarTower.of_compHom Γ(Y, V.1) Γ(Y, W.1) _
  obtain ⟨r, hr, hrestrict, hlocalId⟩ := ω.localEquiv_basicOpen U V hVU g F G
  have htrace := isTraceElement_localization.{u, u, u, u, u, u, u, u, u} g F G r hr
    (isTraceElement_traceCandidate F)
  rw [hlocalId (r (dualizingModule.traceCandidate F))] at htrace
  refine (ω.localEquiv U W hWU G).injective ?_
  rw [localEquiv_chartTraceSection ω U W hWU _ G, hrestrict,
    localEquiv_chartTraceSection ω U V hVU hflat F]
  exact (isTraceElement_iff_eq_traceCandidate G _).mp htrace

/-- **Shrinking the base chart to a principal open.** The trace section of a flat chart does not
change when the base chart is replaced by a principal open still containing the image of the
source. -/
theorem chartTraceSection_baseRestrict (ω : RelativeDualizingModuleData f)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (a : Γ(X, U.1))
    (hVa : V.1 ≤ f ⁻¹ᵁ (X.basicOpen a))
    (hflat : letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
      Module.Flat Γ(X, U.1) Γ(Y, V.1)) :
    chartTraceSection ω U V hVU hflat =
      chartTraceSection ω ⟨X.basicOpen a, U.2.basicOpen a⟩ V hVa
        ((flat_basicOpen_base_iff U V hVU a hVa).mp hflat) := by
  set Ua : X.affineOpens := ⟨X.basicOpen a, U.2.basicOpen a⟩
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  let : Module.Flat Γ(X, U.1) Γ(Y, V.1) := hflat
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
  let : Algebra Γ(X, Ua.1) Γ(Y, V.1) := (f.appLE Ua V hVa).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(X, Ua.1) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom.toAlgebra
  let : IsNoetherianRing Γ(X, Ua.1) := IsLocallyNoetherian.component_noetherian Ua
  let : IsLocalization.Away a Γ(X, Ua.1) := U.2.isLocalization_basicOpen a
  let : IsScalarTower Γ(X, U.1) Γ(X, Ua.1) Γ(Y, V.1) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (f.map_appLE hVa (homOfLE (X.basicOpen_le a)).op).symm)
  let : Module.Flat Γ(X, Ua.1) Γ(Y, V.1) := (flat_basicOpen_base_iff U V hVU a hVa).mp hflat
  let : Algebra.QuasiFinite Γ(X, Ua.1) Γ(Y, V.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE Ua.2 V.2 hVa)
  let F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1) :=
    Classical.choice (ω.factorization U V hVU)
  let G : FiniteOpenFactorization.{u, u, u} Γ(X, Ua.1) Γ(Y, V.1) :=
    Classical.choice (ω.factorization Ua V hVa)
  have hF := isTraceElement_of_isLocalization_away a F G
    (dualizingModule.traceCandidate G) (isTraceElement_traceCandidate G)
  have heInv := (isTraceElement_iff_eq_traceCandidate F
    ((dualizingModule_equiv_of_isLocalization_away a F G).symm
      (dualizingModule.traceCandidate G))).mp hF
  have heTrace : dualizingModule_equiv_of_isLocalization_away a F G
      (dualizingModule.traceCandidate F) = dualizingModule.traceCandidate G := by
    simpa using (congrArg (dualizingModule_equiv_of_isLocalization_away a F G) heInv).symm
  refine (ω.localEquiv Ua V hVa G).injective ?_
  rw [localEquiv_chartTraceSection ω Ua V hVa _ G,
    ω.localEquiv_baseBasicOpen U V hVU a hVa F G (chartTraceSection ω U V hVU hflat),
    localEquiv_chartTraceSection ω U V hVU hflat F, heTrace]

/-- The condition of being the trace element on a chart does not change when the base chart is
shrunk to a principal open containing the image of the source. -/
theorem isTraceSectionOn_basicOpen_base_iff (ω : RelativeDualizingModuleData f)
    (s : Γ(ω.sheaf, ⊤)) (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (a : Γ(X, U.1)) (hVa : V.1 ≤ f ⁻¹ᵁ (X.basicOpen a)) :
    IsTraceSectionOn ω s U V hVU ↔
      IsTraceSectionOn ω s ⟨X.basicOpen a, U.2.basicOpen a⟩ V hVa := by
  rw [isTraceSectionOn_iff, isTraceSectionOn_iff]
  constructor
  · intro h hflat'
    rw [h ((flat_basicOpen_base_iff U V hVU a hVa).mpr hflat'),
      chartTraceSection_baseRestrict ω U V hVU a hVa]
  · intro h hflat
    rw [h ((flat_basicOpen_base_iff U V hVU a hVa).mp hflat),
      chartTraceSection_baseRestrict ω U V hVU a hVa hflat]

/-- **The condition is local on the source chart.** If every point of the source of a chart has
a principal open neighbourhood in it on which the section is the trace element, then the section
is the trace element on the chart. -/
theorem IsTraceSectionOn.of_basicOpen_cover {ω : RelativeDualizingModuleData f}
    {s : Γ(ω.sheaf, ⊤)} {U : X.affineOpens} {V : Y.affineOpens} (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (h : ∀ y ∈ V.1, ∃ g : Γ(Y, V.1), y ∈ Y.basicOpen g ∧
      IsTraceSectionOn ω s U ⟨Y.basicOpen g, V.2.basicOpen g⟩ ((Y.basicOpen_le g).trans hVU)) :
    IsTraceSectionOn ω s U V hVU := by
  rw [isTraceSectionOn_iff]
  intro hflat
  choose g hg hgs using h
  refine TopCat.Sheaf.eq_of_locally_eq'
    (⟨ω.sheaf.presheaf, ω.sheaf.isSheaf⟩ : TopCat.Sheaf Ab (Y : TopCat.{u}))
    (fun y : V.1 => Y.basicOpen (g y.1 y.2)) V.1 (fun y => homOfLE (Y.basicOpen_le _))
    (fun y hy => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hg y hy⟩) _ _ fun y => ?_
  have h1 := (isTraceSectionOn_iff ω s U _ _).mp (hgs y.1 y.2)
    (flat_basicOpen_source U V hVU (g y.1 y.2) hflat)
  have h2 := chartTraceSection_sourceRestrict ω U V hVU (g y.1 y.2) hflat
  change restrictₗ ω.sheaf (Y.basicOpen_le _) (restrictₗ ω.sheaf (show V.1 ≤ ⊤ from le_top) s) =
    restrictₗ ω.sheaf (Y.basicOpen_le _) (chartTraceSection ω U V hVU hflat)
  rw [h2, restrictₗ_restrictₗ, ← h1]

/-! ### Affine source and base -/

section Affine

variable [IsAffine X] [IsAffine Y]

/-- The whole of the affine base, as an affine chart. -/
abbrev topChartX : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩

/-- The whole of the affine source, as an affine chart. -/
abbrev topChartY : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩

/-- A principal open of the affine source, as an affine chart. -/
abbrev basicChartY (g : Γ(Y, ⊤)) : Y.affineOpens :=
  ⟨Y.basicOpen g, (isAffineOpen_top Y).basicOpen g⟩

/-- A principal open of the affine base, as an affine chart. -/
abbrev basicChartX (a : Γ(X, ⊤)) : X.affineOpens :=
  ⟨X.basicOpen a, (isAffineOpen_top X).basicOpen a⟩

omit [IsLocallyNoetherian Y] [IsAffine X] [IsAffine Y] in
/-- Restricting a global section of an `𝒪_Y`-module along `⊤ ≤ ⊤` gives the same section. -/
theorem restrictₗ_top_self (M : Y.Modules) (x : Γ(M, ⊤)) :
    restrictₗ M (le_refl (⊤ : Y.Opens)) x = x := by
  change (M.presheaf.map (homOfLE (le_refl (⊤ : Y.Opens))).op) x = x
  rw [show (homOfLE (le_refl (⊤ : Y.Opens))).op = 𝟙 _ from Subsingleton.elim _ _,
    M.presheaf.map_id]
  rfl

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyQuasiFinite f] [IsAffine X]
  [IsAffine Y] in
/-- For `g ∈ Γ(Y, ⊤)`, the coordinate-ring maps `Γ(X, ⊤) → Γ(Y, ⊤) → Γ(Y, D(g))` induced by `f`
and by restriction form a scalar tower. -/
theorem isScalarTower_basicChartY (g : Γ(Y, ⊤)) :
    letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := (f.appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI : Algebra Γ(Y, ⊤) Γ(Y, Y.basicOpen g) :=
      (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom.toAlgebra
    letI : Algebra Γ(X, ⊤) Γ(Y, Y.basicOpen g) := (f.appLE ⊤ (Y.basicOpen g) le_top).hom.toAlgebra
    IsScalarTower Γ(X, ⊤) Γ(Y, ⊤) Γ(Y, Y.basicOpen g) :=
  let : Algebra Γ(X, ⊤) Γ(Y, ⊤) := (f.appLE ⊤ ⊤ le_top).hom.toAlgebra
  let : Algebra Γ(Y, ⊤) Γ(Y, Y.basicOpen g) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom.toAlgebra
  let : Algebra Γ(X, ⊤) Γ(Y, Y.basicOpen g) := (f.appLE ⊤ (Y.basicOpen g) le_top).hom.toAlgebra
  IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (f.appLE_map le_top (homOfLE (Y.basicOpen_le g)).op).symm)

/-- **The trace condition on a principal open of the affine source.** Over the whole affine
base, a section is the trace element on the chart `D(g)` exactly when the image in `ω_{B_g/A}` of
its image `φ ∈ ω_{B/A}` on the whole source is a trace element, if `A → B_g` is flat. -/
theorem isTraceSectionOn_basicChartY_iff (ω : RelativeDualizingModuleData f) (s : Γ(ω.sheaf, ⊤))
    (setup : @DedekindDifferentSetup Γ(X, ⊤) Γ(Y, ⊤) _ _ (f.appLE ⊤ ⊤ le_top).hom.toAlgebra)
    (g : Γ(Y, ⊤)) :
    letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := (f.appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI : Module.Finite Γ(X, ⊤) Γ(Y, ⊤) := setup.finite
    letI : Algebra Γ(Y, ⊤) Γ(Y, Y.basicOpen g) :=
      (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom.toAlgebra
    letI : Algebra Γ(X, ⊤) Γ(Y, Y.basicOpen g) := (f.appLE ⊤ (Y.basicOpen g) le_top).hom.toAlgebra
    letI := isScalarTower_basicChartY (f := f) g
    letI : IsLocalization.Away g Γ(Y, Y.basicOpen g) :=
      (isAffineOpen_top Y).isLocalization_basicOpen g
    IsTraceSectionOn ω s topChartX (basicChartY g) le_top ↔
      ∀ [Module.Flat Γ(X, ⊤) Γ(Y, Y.basicOpen g)],
        letI : IsNoetherianRing Γ(X, ⊤) := setup.isNoetherianRing
        letI := DedekindTraceElement.isNoetherianRing_loc (setup := setup)
          (Bg := Γ(Y, Y.basicOpen g)) g
        letI := DedekindTraceElement.quasiFinite_loc (setup := setup) (Bg := Γ(Y, Y.basicOpen g)) g
        IsTraceElement.{u, u, u, u, u, u}
          (DedekindTraceElement.locF (setup := setup) (Bg := Γ(Y, Y.basicOpen g)) g)
          (DedekindTraceElement.locElt (setup := setup) (Bg := Γ(Y, Y.basicOpen g)) g
            (ω.localEquiv topChartX topChartY le_top (selfFactorization Γ(X, ⊤) Γ(Y, ⊤))
              (restrictₗ ω.sheaf (le_top : (⊤ : Y.Opens) ≤ ⊤) s))) := by
  let : Algebra Γ(X, ⊤) Γ(Y, ⊤) := (f.appLE ⊤ ⊤ le_top).hom.toAlgebra
  let : Module.Finite Γ(X, ⊤) Γ(Y, ⊤) := setup.finite
  let : Algebra Γ(Y, ⊤) Γ(Y, Y.basicOpen g) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom.toAlgebra
  let : Algebra Γ(X, ⊤) Γ(Y, Y.basicOpen g) := (f.appLE ⊤ (Y.basicOpen g) le_top).hom.toAlgebra
  let := isScalarTower_basicChartY (f := f) g
  let : IsLocalization.Away g Γ(Y, Y.basicOpen g) :=
    (isAffineOpen_top Y).isLocalization_basicOpen g
  let : IsNoetherianRing Γ(X, ⊤) := IsLocallyNoetherian.component_noetherian topChartX
  let : IsNoetherianRing Γ(Y, ⊤) := IsLocallyNoetherian.component_noetherian topChartY
  let : IsNoetherianRing Γ(Y, Y.basicOpen g) :=
    IsLocallyNoetherian.component_noetherian (basicChartY g)
  let : Algebra.QuasiFinite Γ(X, ⊤) Γ(Y, ⊤) :=
    RingHom.quasiFinite_algebraMap.mp
      (LocallyQuasiFinite.quasiFinite_appLE (isAffineOpen_top X) (isAffineOpen_top Y) le_top)
  let F := selfFactorization Γ(X, ⊤) Γ(Y, ⊤)
  have key : ∀ (hflat : Module.Flat Γ(X, ⊤) Γ(Y, Y.basicOpen g))
      (G : FiniteOpenFactorization.{u, u, u} Γ(X, ⊤) Γ(Y, Y.basicOpen g)),
      let : Algebra.QuasiFinite Γ(X, ⊤) Γ(Y, Y.basicOpen g) :=
        RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE
          (isAffineOpen_top X) ((isAffineOpen_top Y).basicOpen g) le_top)
      (IsTraceElement.{u, u, u, u, u, u} G
          (ω.localEquiv topChartX (basicChartY g) le_top G
            (restrictₗ ω.sheaf (le_top : Y.basicOpen g ≤ ⊤) s)) ↔
        IsTraceElement.{u, u, u, u, u, u}
          (DedekindTraceElement.locF (setup := setup) (Bg := Γ(Y, Y.basicOpen g)) g)
          (DedekindTraceElement.locElt (setup := setup) (Bg := Γ(Y, Y.basicOpen g)) g
            (ω.localEquiv topChartX topChartY le_top F
              (restrictₗ ω.sheaf (le_top : (⊤ : Y.Opens) ≤ ⊤) s)))) := by
    intro hflat G
    let : Module Γ(Y, ⊤) (dualizingModule G) :=
      Module.compHom (dualizingModule G) (algebraMap Γ(Y, ⊤) Γ(Y, Y.basicOpen g))
    let : IsScalarTower Γ(Y, ⊤) Γ(Y, Y.basicOpen g) (dualizingModule G) :=
      IsScalarTower.of_compHom Γ(Y, ⊤) Γ(Y, Y.basicOpen g) _
    obtain ⟨r, hr, hrestrict, hlocalId⟩ := ω.localEquiv_basicOpen topChartX topChartY le_top g F G
    have hs : restrictₗ ω.sheaf (le_top : Y.basicOpen g ≤ ⊤) s =
        restrictₗ ω.sheaf (Y.basicOpen_le g) (restrictₗ ω.sheaf (le_top : (⊤ : Y.Opens) ≤ ⊤) s) :=
      (restrictₗ_restrictₗ ω.sheaf _ _ s).symm
    rw [hs, hrestrict, ← hlocalId (r _)]
    exact DedekindTraceElement.isTraceElement_localized_iff (setup := setup) g G r hr _
  constructor
  · intro h hflat
    let G : FiniteOpenFactorization.{u, u, u} Γ(X, ⊤) Γ(Y, Y.basicOpen g) :=
      Classical.choice (ω.factorization topChartX (basicChartY g) le_top)
    exact (key hflat G).mp (h hflat G)
  · intro h hflat G
    exact (key hflat G).mpr (@h hflat)

/-- The image on the whole affine source of a global section of `ω_{Y/X}`, in the relative
dualizing module `ω_{B/A} = Hom_A(B, A) ⊗_B B` of the global sections. -/
def topImage (ω : RelativeDualizingModuleData f) (s : Γ(ω.sheaf, ⊤))
    (setup : @DedekindDifferentSetup Γ(X, ⊤) Γ(Y, ⊤) _ _ (f.appLE ⊤ ⊤ le_top).hom.toAlgebra) :
    letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := (f.appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI : Module.Finite Γ(X, ⊤) Γ(Y, ⊤) := setup.finite
    dualizingModule (selfFactorization Γ(X, ⊤) Γ(Y, ⊤)) :=
  letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := (f.appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI : Module.Finite Γ(X, ⊤) Γ(Y, ⊤) := setup.finite
  ω.localEquiv topChartX topChartY le_top (selfFactorization Γ(X, ⊤) Γ(Y, ⊤))
    (restrictₗ ω.sheaf (le_top : (⊤ : Y.Opens) ≤ ⊤) s)

/-- **The trace condition on the whole source.** Over affine `X` and `Y` with the Dedekind
different of `A = Γ(X, ⊤) → B = Γ(Y, ⊤)` defined, a global section of `ω_{Y/X}` is the trace
element on every chart exactly when its image `φ ∈ Hom_A(B, A)` induces the trace of the
generic fibre. -/
theorem forall_isTraceSectionOn_iff (ω : RelativeDualizingModuleData f) (s : Γ(ω.sheaf, ⊤))
    (setup : @DedekindDifferentSetup Γ(X, ⊤) Γ(Y, ⊤) _ _ (f.appLE ⊤ ⊤ le_top).hom.toAlgebra) :
    letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := (f.appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI : Module.Finite Γ(X, ⊤) Γ(Y, ⊤) := setup.finite
    letI : Algebra (FractionRing Γ(X, ⊤)) (Γ(Y, ⊤) ⊗[Γ(X, ⊤)] FractionRing Γ(X, ⊤)) :=
      Algebra.TensorProduct.rightAlgebra
    (∀ (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1),
        IsTraceSectionOn ω s U V hVU) ↔
      ∀ b : Γ(Y, ⊤), algebraMap Γ(X, ⊤) (FractionRing Γ(X, ⊤))
          (selfFactorizationDualEquiv (topImage ω s setup) b) =
        setup.trace (algebraMap Γ(Y, ⊤) (Γ(Y, ⊤) ⊗[Γ(X, ⊤)] FractionRing Γ(X, ⊤)) b) := by
  let : Algebra Γ(X, ⊤) Γ(Y, ⊤) := (f.appLE ⊤ ⊤ le_top).hom.toAlgebra
  let : Module.Finite Γ(X, ⊤) Γ(Y, ⊤) := setup.finite
  let : IsNoetherianRing Γ(X, ⊤) := setup.isNoetherianRing
  let : Algebra (FractionRing Γ(X, ⊤)) (Γ(Y, ⊤) ⊗[Γ(X, ⊤)] FractionRing Γ(X, ⊤)) :=
    Algebra.TensorProduct.rightAlgebra
  rw [← DedekindTraceElement.baseChange_eq_traceK_iff (setup := setup)]
  constructor
  · intro h
    let : ∀ g : Γ(Y, ⊤), Algebra Γ(Y, ⊤) Γ(Y, Y.basicOpen g) := fun g =>
      (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom.toAlgebra
    let : ∀ g : Γ(Y, ⊤), Algebra Γ(X, ⊤) Γ(Y, Y.basicOpen g) := fun g =>
      (f.appLE ⊤ (Y.basicOpen g) le_top).hom.toAlgebra
    let : ∀ g : Γ(Y, ⊤), IsScalarTower Γ(X, ⊤) Γ(Y, ⊤) Γ(Y, Y.basicOpen g) := fun g =>
      isScalarTower_basicChartY (f := f) g
    let : ∀ g : Γ(Y, ⊤), IsLocalization.Away g Γ(Y, Y.basicOpen g) := fun g =>
      (isAffineOpen_top Y).isLocalization_basicOpen g
    refine DedekindTraceElement.baseChange_eq_traceK_of_isTraceElement (setup := setup)
      (fun g => Γ(Y, Y.basicOpen g)) _ fun g _ => ?_
    exact (isTraceSectionOn_basicChartY_iff ω s setup g).mp (h topChartX (basicChartY g) le_top)
  · intro h U V hVU
    refine IsTraceSectionOn.of_basicOpen_cover hVU fun y hy => ?_
    obtain ⟨a, haU, hya⟩ := (isAffineOpen_top X).exists_basicOpen_le
      (⟨f.base y, hVU hy⟩ : U.1) trivial
    obtain ⟨g, hgV, hyg⟩ := (isAffineOpen_top Y).exists_basicOpen_le
      (⟨y, hy, hya⟩ : (V.1 ⊓ f ⁻¹ᵁ X.basicOpen a : Y.Opens)) trivial
    let gV : Γ(Y, V.1) := Y.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op g
    let aU : Γ(X, U.1) := X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op a
    have hgV' : Y.basicOpen gV = Y.basicOpen g := by
      rw [Scheme.basicOpen_res]
      exact inf_eq_right.mpr (hgV.trans inf_le_left)
    have haU' : X.basicOpen aU = X.basicOpen a := by
      rw [Scheme.basicOpen_res]
      exact inf_eq_right.mpr haU
    refine ⟨gV, hgV' ▸ hyg, ?_⟩
    have hga : Y.basicOpen g ≤ f ⁻¹ᵁ X.basicOpen a := hgV.trans inf_le_right
    have hgU : Y.basicOpen g ≤ f ⁻¹ᵁ U.1 := hga.trans fun _ hz => haU hz
    rw [IsTraceSectionOn.congr rfl (Subtype.ext hgV' : (⟨Y.basicOpen gV, V.2.basicOpen gV⟩ :
      Y.affineOpens) = basicChartY g) _ hgU,
      isTraceSectionOn_basicOpen_base_iff ω s U (basicChartY g) hgU aU (haU' ▸ hga),
      IsTraceSectionOn.congr (Subtype.ext haU' : (⟨X.basicOpen aU, U.2.basicOpen aU⟩ :
      X.affineOpens) = basicChartX a) rfl _ hga,
      ← isTraceSectionOn_basicOpen_base_iff ω s topChartX (basicChartY g) le_top a hga]
    refine (isTraceSectionOn_basicChartY_iff ω s setup g).mpr fun {_} => ?_
    let : Algebra Γ(Y, ⊤) Γ(Y, Y.basicOpen g) :=
      (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom.toAlgebra
    let : Algebra Γ(X, ⊤) Γ(Y, Y.basicOpen g) := (f.appLE ⊤ (Y.basicOpen g) le_top).hom.toAlgebra
    let := isScalarTower_basicChartY (f := f) g
    let : IsLocalization.Away g Γ(Y, Y.basicOpen g) :=
      (isAffineOpen_top Y).isLocalization_basicOpen g
    exact DedekindTraceElement.isTraceElement_locElt_of_baseChange_eq (setup := setup)
      (Bg := Γ(Y, Y.basicOpen g)) g _ h

/-- **[Stacks, Tag 0BWN], the trace element extends exactly when `1 ∈ L_{B/A}`.** Over affine
`X` and `Y` with the Dedekind different of `A = Γ(X, ⊤) → B = Γ(Y, ⊤)` defined, the trace
element of the flat locus comes from a global section of `ω_{Y/X}` exactly when `1` lies in the
complementary module. -/
theorem nonempty_generalizedTraceSection_iff_of_isAffine (ω : RelativeDualizingModuleData f)
    (setup : @DedekindDifferentSetup Γ(X, ⊤) Γ(Y, ⊤) _ _ (f.appLE ⊤ ⊤ le_top).hom.toAlgebra) :
    letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := (f.appLE ⊤ ⊤ le_top).hom.toAlgebra
    Nonempty (GeneralizedTraceSection ω) ↔
      (1 : Γ(Y, ⊤) ⊗[Γ(X, ⊤)] FractionRing Γ(X, ⊤)) ∈ setup.complementaryModule := by
  let : Algebra Γ(X, ⊤) Γ(Y, ⊤) := (f.appLE ⊤ ⊤ le_top).hom.toAlgebra
  let : Module.Finite Γ(X, ⊤) Γ(Y, ⊤) := setup.finite
  rw [nonempty_generalizedTraceSection_iff, ← exists_dual_trace_iff_one_mem_complementaryModule]
  constructor
  · exact fun ⟨s, hs⟩ => ⟨_, (forall_isTraceSectionOn_iff ω s setup).mp hs⟩
  · rintro ⟨φ₀, hφ₀⟩
    let s : Γ(ω.sheaf, ⊤) := (ω.localEquiv topChartX topChartY le_top
      (selfFactorization Γ(X, ⊤) Γ(Y, ⊤))).symm (selfFactorizationDualEquiv.symm φ₀)
    have htop : selfFactorizationDualEquiv (topImage ω s setup) = φ₀ := by
      change selfFactorizationDualEquiv (ω.localEquiv topChartX topChartY le_top _
        (restrictₗ ω.sheaf (le_top : (⊤ : Y.Opens) ≤ ⊤) s)) = φ₀
      rw [restrictₗ_top_self, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact ⟨s, (forall_isTraceSectionOn_iff ω s setup).mpr (htop ▸ hφ₀)⟩

/-- **[Stacks, Tag 0BWN], the generalized different is the Dedekind different.** Over affine `X`
and `Y` with the Dedekind different of `A = Γ(X, ⊤) → B = Γ(Y, ⊤)` defined and `1 ∈ L_{B/A}`,
the generalized different of the extension of the trace element is the sheaf of ideals
`(𝔇_{B/A})~` attached to the Dedekind different ideal. -/
theorem generalizedDifferent_eq_unitSubmodule_of_isAffine (ω : RelativeDualizingModuleData f)
    (setup : @DedekindDifferentSetup Γ(X, ⊤) Γ(Y, ⊤) _ _ (f.appLE ⊤ ⊤ le_top).hom.toAlgebra)
    (h1 : letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := (f.appLE ⊤ ⊤ le_top).hom.toAlgebra
      (1 : Γ(Y, ⊤) ⊗[Γ(X, ⊤)] FractionRing Γ(X, ⊤)) ∈ setup.complementaryModule)
    (τ : GeneralizedTraceSection ω) :
    letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := (f.appLE ⊤ ⊤ le_top).hom.toAlgebra
    generalizedDifferent ω τ =
      (Scheme.IdealSheafData.ofIdealTop (dedekindDifferentIdeal setup)).unitSubmodule := by
  let : Algebra Γ(X, ⊤) Γ(Y, ⊤) := (f.appLE ⊤ ⊤ le_top).hom.toAlgebra
  let : Module.Finite Γ(X, ⊤) Γ(Y, ⊤) := setup.finite
  have hT := (forall_isTraceSectionOn_iff ω τ.sect setup).mp τ.isTraceElement_localEquiv
  have hφ := eq_complementaryModuleEquivDualizingModule_one setup h1 _ hT
  have hsec := annihilatorSectionCokernel_obj_affine_eq_dedekindDifferentIdeal ω τ.sect
    topChartX topChartY le_top setup h1 hφ
  change annihilatorSectionCokernel ω τ.sect = _
  rw [annihilatorSectionCokernel_eq_unitSubmodule_ofIdealTop ω τ.sect, hsec]

end Affine

end Stacks.Discriminant
