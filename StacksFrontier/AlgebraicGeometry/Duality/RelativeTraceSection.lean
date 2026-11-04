module

public import StacksFrontier.AlgebraicGeometry.Discriminant.TraceElementUnique
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModuleData0BVG
public import StacksFrontier.RingTheory.TraceElement.BaseLocalization
public import StacksFrontier.RingTheory.TraceElement.Existence
public import StacksFrontier.RingTheory.TraceElement.TargetLocalization

/-!
# The global relative trace section

Let `f : Y ⟶ X` be a flat locally quasi-finite morphism of locally Noetherian schemes and let
`ω_{Y/X}` be a relative dualizing module for it, in the sense of the chart data
`Stacks.Discriminant.RelativeDualizingModuleData` of Tag 0BVG.  On every pair of affine charts
`V ⊆ f⁻¹ U` the algebraic relative dualizing module `ω_{Γ(Y,V)/Γ(X,U)}` has a unique trace
element, by the existence of Tag 0BTB and the uniqueness of Tag 0BT7.  These chart-local
elements are carried to one another by the localization comparisons of Tag 0BT9, so they agree
on overlaps and glue to a single global section `τ_{Y/X} ∈ Γ(Y, ω_{Y/X})`.

## Main definitions

* `Stacks.Discriminant.localTraceSection` is the section of `ω_{Y/X}` over an affine chart of
  the source corresponding to the trace element of the chart's coordinate-ring map.
* `Stacks.Discriminant.relativeTraceSection` is the global section `τ_{Y/X}`, obtained by
  gluing those chart sections along the cover of the source by chart pairs.

## Main results

* `Stacks.Discriminant.isTraceElement_iff_eq_traceCandidate` identifies the canonical element
  of an algebraic relative dualizing module as its unique trace element, and
  `Stacks.Discriminant.dualizingModuleEquiv_traceCandidate` says the comparison of Tag 0BT1
  preserves it.
* `Stacks.Discriminant.localTraceSection_sourceRestrict` and
  `Stacks.Discriminant.localTraceSection_baseRestrict`: the chart sections are unchanged by
  shrinking the source chart to a principal open and by shrinking the base chart to a
  principal open.
* `Stacks.Discriminant.localEquiv_relativeTraceSection` is the defining property of `τ_{Y/X}`:
  on every pair of affine charts it restricts to the trace element of the coordinate-ring map,
  under the canonical identification of Tag 0BVG.
* `Stacks.Discriminant.existsUnique_relativeTraceSection` says `τ_{Y/X}` is the only global
  section with that property.

## Implementation notes

The relative dualizing module is taken as a hypothesis, in the form of a chart datum for `f`,
because that is how Tag 0BVJ reads the sheaf: it is the object of the preceding remark, and
nothing about its construction is used.  The trace element of a chart is transported into the
sheaf along `RelativeDualizingModuleData.localEquiv` for a finite-open factorization taken from
the `factorization` field, which is `Nonempty` rather than a chosen factorization;
`RelativeDualizingModuleData.localEquiv_natural` together with
`Stacks.Discriminant.dualizingModuleEquiv_traceCandidate` show the resulting section does not
depend on that, which is the content of
`Stacks.Discriminant.localEquiv_localTraceSection`.

Agreement of two chart sections at a point of the overlap of their source charts is reached in
three principal steps, which are the only comparisons Tag 0BT2 supplies: the two base charts
are shrunk to a common principal open, the first source chart is shrunk to a principal open
inside the second, and the two source charts are then shrunk to a common principal open.

## References

* [Stacks Project, Tag 0BT1](https://stacks.math.columbia.edu/tag/0BT1)
* [Stacks Project, Tag 0BT7](https://stacks.math.columbia.edu/tag/0BT7)
* [Stacks Project, Tag 0BT9](https://stacks.math.columbia.edu/tag/0BT9)
* [Stacks Project, Tag 0BTB](https://stacks.math.columbia.edu/tag/0BTB)
* [Stacks Project, Tag 0BVG](https://stacks.math.columbia.edu/tag/0BVG)
* [Stacks Project, Tag 0BVJ](https://stacks.math.columbia.edu/tag/0BVJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

universe u v w x

namespace Stacks.Discriminant

open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

attribute [local instance] algebraDualModule Module.finitePresentation_of_finite

section TraceCandidate

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B] [Algebra.QuasiFinite A B]

/-- The canonical element of the relative dualizing module of a flat quasi-finite map of
Noetherian rings is a trace element, and it is the only one. -/
theorem isTraceElement_iff_eq_traceCandidate (F : FiniteOpenFactorization.{u, v, w} A B)
    (τ : dualizingModule F) :
    IsTraceElement.{u, v, w, u, max u v, max u v} F τ ↔
      τ = dualizingModule.traceCandidate F :=
  ⟨fun hτ => isTraceElement_unique F hτ (isTraceElement_traceCandidate F),
    fun hτ => hτ ▸ isTraceElement_traceCandidate F⟩

/-- The comparison of the relative dualizing modules attached to two finite-open
factorizations carries the trace element to the trace element. -/
theorem dualizingModuleEquiv_traceCandidate (F : FiniteOpenFactorization.{u, v, w} A B)
    (G : FiniteOpenFactorization.{u, v, x} A B) :
    dualizingModuleEquiv F G (dualizingModule.traceCandidate F) =
      dualizingModule.traceCandidate G :=
  (isTraceElement_iff_eq_traceCandidate G _).mp
    ((isTraceElement_congr.{u, v, w, x, u, max u v, max u v} F G
      (dualizingModule.traceCandidate F)).mp (isTraceElement_traceCandidate F))

end TraceCandidate

section Restriction

variable {Y : Scheme.{u}}

/-- Restriction of sections of a sheaf of modules composes. -/
theorem restrictₗ_restrictₗ (M : Y.Modules) {U V W : Y.Opens} (h₁ : U ≤ V) (h₂ : V ≤ W)
    (s : Γ(M, W)) : restrictₗ M h₁ (restrictₗ M h₂ s) = restrictₗ M (h₁.trans h₂) s := by
  show (M.presheaf.map (homOfLE h₁).op).hom ((M.presheaf.map (homOfLE h₂).op).hom s) =
    (M.presheaf.map (homOfLE (h₁.trans h₂)).op).hom s
  show ((M.presheaf.map (homOfLE h₂).op) ≫ (M.presheaf.map (homOfLE h₁).op)).hom s =
    (M.presheaf.map (homOfLE (h₁.trans h₂)).op).hom s
  rw [← M.presheaf.map_comp]
  congr 2

/-- Two restrictions of a section to opens that happen to be equal agree. -/
theorem restrictₗ_heq_of_eq (M : Y.Modules) {U U' V : Y.Opens} (hU : U = U') (h : U ≤ V)
    (h' : U' ≤ V) (s : Γ(M, V)) : HEq (restrictₗ M h s) (restrictₗ M h' s) := by
  cases hU
  rfl

end Restriction

section Charts

variable {X Y : Scheme.{u}} {f : Y ⟶ X} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  [LocallyQuasiFinite f] [Flat f]

/-- The section of the relative dualizing module over an affine chart of the source
corresponding to the trace element of the chart's coordinate-ring map. -/
def localTraceSection (D : RelativeDualizingModuleData f) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) : Γ(D.sheaf, V.1) :=
  letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  letI : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  letI : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
  letI : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
  letI F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1) :=
    Classical.choice (D.factorization U V hVU)
  (D.localEquiv U V hVU F).symm (dualizingModule.traceCandidate F)

/-- Two chart sections for chart pairs that are equal agree. -/
theorem localTraceSection_heq (D : RelativeDualizingModuleData f) (U U' : X.affineOpens)
    (V V' : Y.affineOpens) (hU : U = U') (hV : V = V') (h : V.1 ≤ f ⁻¹ᵁ U.1)
    (h' : V'.1 ≤ f ⁻¹ᵁ U'.1) :
    HEq (localTraceSection D U V h) (localTraceSection D U' V' h') := by
  cases hU
  cases hV
  rfl

/-- **The chart section is the trace element of the chart.** Under the identification of the
sections over an affine chart of the source with the algebraic relative dualizing module of
that chart, through any finite-open factorization, the chart section is the trace element. -/
theorem localEquiv_localTraceSection (D : RelativeDualizingModuleData f) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    letI : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
    letI : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
      RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
    letI : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
      RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
    ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1),
      D.localEquiv U V hVU F (localTraceSection D U V hVU) =
        dualizingModule.traceCandidate F := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  let : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
  intro F
  let G : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1) :=
    Classical.choice (D.factorization U V hVU)
  show D.localEquiv U V hVU F
    ((D.localEquiv U V hVU G).symm (dualizingModule.traceCandidate G)) = _
  rw [D.localEquiv_natural U V hVU G F]
  simpa using dualizingModuleEquiv_traceCandidate G F

/-- **Shrinking the source chart to a principal open.** The chart section of a source chart
restricts to the chart section of a principal open of it. -/
theorem localTraceSection_sourceRestrict (D : RelativeDualizingModuleData f)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (g : Γ(Y, V.1)) :
    restrictₗ D.sheaf (Y.basicOpen_le g) (localTraceSection D U V hVU) =
      localTraceSection D U ⟨Y.basicOpen g, V.2.basicOpen g⟩ ((Y.basicOpen_le g).trans hVU) := by
  set W : Y.affineOpens := ⟨Y.basicOpen g, V.2.basicOpen g⟩
  set hWU : W.1 ≤ f ⁻¹ᵁ U.1 := (Y.basicOpen_le g).trans hVU
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  let : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
  let : Algebra Γ(X, U.1) Γ(Y, W.1) := (f.appLE U W hWU).hom.toAlgebra
  let : Algebra Γ(Y, V.1) Γ(Y, W.1) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom.toAlgebra
  let : IsNoetherianRing Γ(Y, W.1) := IsLocallyNoetherian.component_noetherian W
  let : IsLocalization.Away g Γ(Y, W.1) := V.2.isLocalization_basicOpen g
  let : IsScalarTower Γ(X, U.1) Γ(Y, V.1) Γ(Y, W.1) :=
    IsScalarTower.of_algebraMap_eq' (by
      show (f.appLE U W hWU).hom =
        ((Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom).comp (f.appLE U V hVU).hom
      rw [← CommRingCat.hom_comp, ← f.appLE_map hVU (homOfLE (Y.basicOpen_le g)).op])
  let : Module.Flat Γ(Y, V.1) Γ(Y, W.1) := IsLocalization.flat (Γ(Y, W.1)) (Submonoid.powers g)
  let : Module.Flat Γ(X, U.1) Γ(Y, W.1) :=
    Module.Flat.trans Γ(X, U.1) Γ(Y, V.1) Γ(Y, W.1)
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, W.1) :=
    Algebra.QuasiFinite.of_isLocalization (Submonoid.powers g)
  let F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1) :=
    Classical.choice (D.factorization U V hVU)
  let G : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, W.1) :=
    Classical.choice (D.factorization U W hWU)
  let : Module Γ(Y, V.1) (dualizingModule G) :=
    Module.compHom (dualizingModule G) (algebraMap Γ(Y, V.1) Γ(Y, W.1))
  let : IsScalarTower Γ(Y, V.1) Γ(Y, W.1) (dualizingModule G) :=
    IsScalarTower.of_compHom Γ(Y, V.1) Γ(Y, W.1) _
  obtain ⟨r, hr, hrestrict, hlocalId⟩ := D.localEquiv_basicOpen U V hVU g F G
  have htrace := isTraceElement_localization.{u, u, u, u, u, u, u, u, u} g F G r hr
    (isTraceElement_traceCandidate F)
  rw [hlocalId (r (dualizingModule.traceCandidate F))] at htrace
  have hEq := (isTraceElement_iff_eq_traceCandidate G
    (r (dualizingModule.traceCandidate F))).mp htrace
  refine (D.localEquiv U W hWU G).injective ?_
  rw [localEquiv_localTraceSection D U W hWU G, hrestrict,
    localEquiv_localTraceSection D U V hVU F]
  exact hEq

/-- **Shrinking the base chart to a principal open.** The chart section does not change when
the affine chart of the base is replaced by a principal open of it still containing the image
of the source chart. -/
theorem localTraceSection_baseRestrict (D : RelativeDualizingModuleData f)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (a : Γ(X, U.1))
    (hVa : V.1 ≤ f ⁻¹ᵁ (X.basicOpen a)) :
    localTraceSection D U V hVU =
      localTraceSection D ⟨X.basicOpen a, U.2.basicOpen a⟩ V hVa := by
  set Ua : X.affineOpens := ⟨X.basicOpen a, U.2.basicOpen a⟩
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  let : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
  let : Algebra Γ(X, Ua.1) Γ(Y, V.1) := (f.appLE Ua V hVa).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(X, Ua.1) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom.toAlgebra
  let : IsNoetherianRing Γ(X, Ua.1) := IsLocallyNoetherian.component_noetherian Ua
  let : IsLocalization.Away a Γ(X, Ua.1) := U.2.isLocalization_basicOpen a
  let : IsScalarTower Γ(X, U.1) Γ(X, Ua.1) Γ(Y, V.1) :=
    IsScalarTower.of_algebraMap_eq' (by
      show (f.appLE U V hVU).hom =
        ((f.appLE Ua V hVa).hom).comp
          (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom
      rw [← CommRingCat.hom_comp, f.map_appLE hVa (homOfLE (X.basicOpen_le a)).op])
  let : Module.Flat Γ(X, U.1) Γ(X, Ua.1) :=
    IsLocalization.flat (Γ(X, Ua.1)) (Submonoid.powers a)
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(X, Ua.1) :=
    Algebra.QuasiFinite.of_isLocalization (Submonoid.powers a)
  let : Module.Flat Γ(X, Ua.1) Γ(Y, V.1) :=
    RingHom.flat_algebraMap_iff.mp (f.flat_appLE Ua.2 V.2 hVa)
  let : Algebra.QuasiFinite Γ(X, Ua.1) Γ(Y, V.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE Ua.2 V.2 hVa)
  let F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1) :=
    Classical.choice (D.factorization U V hVU)
  let G : FiniteOpenFactorization.{u, u, u} Γ(X, Ua.1) Γ(Y, V.1) :=
    Classical.choice (D.factorization Ua V hVa)
  have hF := isTraceElement_of_isLocalization_away a F G
    (dualizingModule.traceCandidate G) (isTraceElement_traceCandidate G)
  have heInv := (isTraceElement_iff_eq_traceCandidate F
    ((dualizingModule_equiv_of_isLocalization_away a F G).symm
      (dualizingModule.traceCandidate G))).mp hF
  have heTrace : dualizingModule_equiv_of_isLocalization_away a F G
      (dualizingModule.traceCandidate F) = dualizingModule.traceCandidate G := by
    simpa using (congrArg (dualizingModule_equiv_of_isLocalization_away a F G) heInv).symm
  refine (D.localEquiv Ua V hVa G).injective ?_
  rwa [localEquiv_localTraceSection D Ua V hVa G,
    D.localEquiv_baseBasicOpen U V hVU a hVa F G (localTraceSection D U V hVU),
    localEquiv_localTraceSection D U V hVU F]

/-- **The chart sections agree on overlaps.** -/
theorem isCompatible_localTraceSection (D : RelativeDualizingModuleData f) :
    TopCat.Presheaf.IsCompatible D.sheaf.presheaf
      (fun p : AffineChartPair f => ((p.1).2).1)
      (fun p => localTraceSection D (p.1).1 (p.1).2 p.2) := by
  intro p q
  obtain ⟨⟨U₁, V₁⟩, hV₁U₁⟩ := p
  obtain ⟨⟨U₂, V₂⟩, hV₂U₂⟩ := q
  refine (Scheme.Modules.isSheaf D.sheaf).section_ext ?_
  intro y hy
  obtain ⟨hy₁, hy₂⟩ : y ∈ V₁.1 ∧ y ∈ V₂.1 := hy
  -- Step 1: a common principal open of the two base charts around the image of `y`.
  obtain ⟨a₁, a₂, ha, hya⟩ :=
    exists_basicOpen_le_affine_inter U₁.2 U₂.2 (f.base y) ⟨hV₁U₁ hy₁, hV₂U₂ hy₂⟩
  set Ua₁ : X.affineOpens := ⟨X.basicOpen a₁, U₁.2.basicOpen a₁⟩ with hUa₁
  set Ua₂ : X.affineOpens := ⟨X.basicOpen a₂, U₂.2.basicOpen a₂⟩ with hUa₂
  have hUa : Ua₁ = Ua₂ := Subtype.ext ha
  have hyUa : y ∈ f ⁻¹ᵁ Ua₁.1 := hya
  -- Step 2: a principal open of the first source chart inside the second and over `Ua₁`.
  obtain ⟨g, hg, hyg⟩ := V₁.2.exists_basicOpen_le
    ⟨y, show y ∈ V₂.1 ⊓ f ⁻¹ᵁ Ua₁.1 from ⟨hy₂, hyUa⟩⟩ hy₁
  set W₁ : Y.affineOpens := ⟨Y.basicOpen g, V₁.2.basicOpen g⟩ with hW₁
  have hW₁V₁ : W₁.1 ≤ V₁.1 := Y.basicOpen_le g
  have hW₁V₂ : W₁.1 ≤ V₂.1 := hg.trans inf_le_left
  have hW₁Ua₁ : W₁.1 ≤ f ⁻¹ᵁ Ua₁.1 := hg.trans inf_le_right
  -- Step 3: a common principal open of `W₁` and of the second source chart around `y`.
  obtain ⟨b₁, b₂, hb, hyb⟩ := exists_basicOpen_le_affine_inter W₁.2 V₂.2 y ⟨hyg, hy₂⟩
  set T₁ : Y.affineOpens := ⟨Y.basicOpen b₁, W₁.2.basicOpen b₁⟩ with hT₁
  set T₂ : Y.affineOpens := ⟨Y.basicOpen b₂, V₂.2.basicOpen b₂⟩ with hT₂
  have hT : T₁ = T₂ := Subtype.ext hb
  have hT₁W₁ : T₁.1 ≤ W₁.1 := Y.basicOpen_le b₁
  have hT₁V₁ : T₁.1 ≤ V₁.1 := hT₁W₁.trans hW₁V₁
  have hT₂V₂ : T₂.1 ≤ V₂.1 := Y.basicOpen_le b₂
  have hT₁Ua₁ : T₁.1 ≤ f ⁻¹ᵁ Ua₁.1 := hT₁W₁.trans hW₁Ua₁
  have hT₂Ua₂ : T₂.1 ≤ f ⁻¹ᵁ Ua₂.1 := by rwa [← hT, ← hUa]
  have hT₁V₂ : T₁.1 ≤ V₂.1 := by rwa [hT]
  refine ⟨T₁.1, le_inf hT₁V₁ hT₁V₂, hyb, ?_⟩
  -- The first chart section restricted to `T₁` is the chart section of `(Ua₁, T₁)`.
  have hRestr₁ : restrictₗ D.sheaf hT₁V₁ (localTraceSection D U₁ V₁ hV₁U₁) =
      localTraceSection D Ua₁ T₁ hT₁Ua₁ := by
    rw [← restrictₗ_restrictₗ D.sheaf hT₁W₁ hW₁V₁,
      localTraceSection_sourceRestrict D U₁ V₁ hV₁U₁ g,
      localTraceSection_baseRestrict D U₁ W₁ (hW₁V₁.trans hV₁U₁) a₁ hW₁Ua₁,
      localTraceSection_sourceRestrict D Ua₁ W₁ hW₁Ua₁ b₁]
  -- The second chart section restricted to `T₂` is the chart section of `(Ua₂, T₂)`.
  have hRestr₂ : restrictₗ D.sheaf hT₂V₂ (localTraceSection D U₂ V₂ hV₂U₂) =
      localTraceSection D Ua₂ T₂ hT₂Ua₂ := by
    rw [localTraceSection_sourceRestrict D U₂ V₂ hV₂U₂ b₂,
      localTraceSection_baseRestrict D U₂ T₂ (hT₂V₂.trans hV₂U₂) a₂ hT₂Ua₂]
  have hmain : HEq (restrictₗ D.sheaf hT₁V₁ (localTraceSection D U₁ V₁ hV₁U₁))
      (restrictₗ D.sheaf hT₁V₂ (localTraceSection D U₂ V₂ hV₂U₂)) :=
    ((heq_of_eq hRestr₁).trans
      ((localTraceSection_heq D Ua₁ Ua₂ T₁ T₂ hUa hT hT₁Ua₁ hT₂Ua₂).trans
        (heq_of_eq hRestr₂).symm)).trans
      (restrictₗ_heq_of_eq D.sheaf hb hT₁V₂ hT₂V₂ (localTraceSection D U₂ V₂ hV₂U₂)).symm
  show restrictₗ D.sheaf (le_inf hT₁V₁ hT₁V₂)
      (restrictₗ D.sheaf inf_le_left (localTraceSection D U₁ V₁ hV₁U₁)) =
    restrictₗ D.sheaf (le_inf hT₁V₁ hT₁V₂)
      (restrictₗ D.sheaf inf_le_right (localTraceSection D U₂ V₂ hV₂U₂))
  rw [restrictₗ_restrictₗ, restrictₗ_restrictₗ]
  exact eq_of_heq hmain

/-- **Stacks Project, Tag 0BVJ.** The relative trace section `τ_{Y/X}` of a flat locally
quasi-finite morphism of locally Noetherian schemes: the global section of the relative
dualizing module obtained by gluing the trace elements of the affine charts along the cover of
the source by the source charts of the chart pairs. -/
@[stacks 0BVJ]
def relativeTraceSection (D : RelativeDualizingModuleData f) : Γ(D.sheaf, ⊤) :=
  (TopCat.Sheaf.existsUnique_gluing'
    (⟨D.sheaf.presheaf, D.sheaf.isSheaf⟩ : TopCat.Sheaf Ab (Y : TopCat.{u}))
    (fun p : AffineChartPair f => ((p.1).2).1) ⊤ (fun _ => homOfLE le_top)
    (le_of_eq (iSup_affineChartPair_eq_top f).symm)
    (fun p => localTraceSection D (p.1).1 (p.1).2 p.2)
    (isCompatible_localTraceSection D)).exists.choose

/-- The relative trace section restricts to the chart section on the source chart of every
chart pair. -/
theorem restrictₗ_relativeTraceSection (D : RelativeDualizingModuleData f)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    restrictₗ D.sheaf (le_top : V.1 ≤ ⊤) (relativeTraceSection D) =
      localTraceSection D U V hVU :=
  (TopCat.Sheaf.existsUnique_gluing'
    (⟨D.sheaf.presheaf, D.sheaf.isSheaf⟩ : TopCat.Sheaf Ab (Y : TopCat.{u}))
    (fun p : AffineChartPair f => ((p.1).2).1) ⊤ (fun _ => homOfLE le_top)
    (le_of_eq (iSup_affineChartPair_eq_top f).symm)
    (fun p => localTraceSection D (p.1).1 (p.1).2 p.2)
    (isCompatible_localTraceSection D)).exists.choose_spec ⟨(U, V), hVU⟩

/-- **Stacks Project, Tag 0BVJ.** On every pair of affine opens `Spec B = V ⊆ Y`,
`Spec A = U ⊆ X` with `f(V) ⊆ U`, the relative trace section restricts to the trace element
`τ_{B/A}` of the relative dualizing module `ω_{B/A}`, under the canonical identification of
the sections over `V` with `ω_{B/A}`. -/
@[stacks 0BVJ]
theorem localEquiv_relativeTraceSection (D : RelativeDualizingModuleData f)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    letI : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
    letI : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
      RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
    letI : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
      RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
    ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1),
      D.localEquiv U V hVU F
          (restrictₗ D.sheaf (le_top : V.1 ≤ ⊤) (relativeTraceSection D)) =
        dualizingModule.traceCandidate F := by
  rw [restrictₗ_relativeTraceSection D U V hVU]
  exact localEquiv_localTraceSection D U V hVU

/-- The relative trace section is the only global section of the relative dualizing module
restricting to the trace element of every affine chart. -/
theorem existsUnique_relativeTraceSection (D : RelativeDualizingModuleData f) :
    ∃! τ : Γ(D.sheaf, ⊤),
      ∀ (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1),
        letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
        letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
        letI : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
        letI : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
          RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
        letI : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
          RingHom.quasiFinite_algebraMap.mp
            (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
        ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1),
          D.localEquiv U V hVU F (restrictₗ D.sheaf (le_top : V.1 ≤ ⊤) τ) =
            dualizingModule.traceCandidate F := by
  refine ⟨relativeTraceSection D, localEquiv_relativeTraceSection D, fun τ hτ => ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq'
    (⟨D.sheaf.presheaf, D.sheaf.isSheaf⟩ : TopCat.Sheaf Ab (Y : TopCat.{u}))
    (fun p : AffineChartPair f => ((p.1).2).1) ⊤ (fun _ => homOfLE le_top)
    (le_of_eq (iSup_affineChartPair_eq_top f).symm) _ _ fun p => ?_
  obtain ⟨⟨U, V⟩, hVU⟩ := p
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  let : Module.Flat Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.flat_algebraMap_iff.mp (f.flat_appLE U.2 V.2 hVU)
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
  let F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1) :=
    Classical.choice (D.factorization U V hVU)
  refine (D.localEquiv U V hVU F).injective ?_
  exact (hτ U V hVU F).trans (localEquiv_relativeTraceSection D U V hVU F).symm

end Charts

end Stacks.Discriminant

end
