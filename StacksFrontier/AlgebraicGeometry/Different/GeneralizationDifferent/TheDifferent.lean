module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.AssociatedPrimes
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.Basic
public import StacksFrontier.AlgebraicGeometry.Discriminant.TraceElementUnique
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Restriction
public import StacksFrontier.RingTheory.AssociatedPrime.Spellings

/-!
# The different of a quasi-finite morphism which is flat near the associated points

Let `f : Y ⟶ X` be a quasi-finite morphism of locally Noetherian schemes and let `V ⊆ Y` be the
open where `f` is flat.  Suppose `V` contains `Ass(𝒪_Y)` and `f⁻¹(Ass(𝒪_X))`, and that the trace
element `τ_{V/X}` extends to a global section `τ ∈ Γ(Y, ω_{Y/X})`.  Then `V` also contains the
associated points of `ω_{Y/X}`, the extension `τ` is unique, and the *generalized different*
`𝔇_f` is the annihilator of `Coker(τ : 𝒪_Y → ω_{Y/X})`.

## Main definitions

* `Stacks.Discriminant.GeneralizedDifferentSituation`: a quasi-finite morphism together with an
  open over which it is flat and which contains the associated points of source and base.
* `Stacks.Discriminant.GeneralizedTraceSection`: a global section of the relative dualizing
  module which is the trace element on every flat affine chart, that is, which extends
  `τ_{V/X}`.
* `Stacks.Discriminant.generalizedDifferent`: the different `𝔇_f` of such a section.

## Main results

* `Stacks.Discriminant.associatedPoints_subset_preimage_schemeAssociatedPoints`: the associated
  points of `ω_{Y/X}` lie over the associated points of `X`.
* `Stacks.Discriminant.associatedPoints_subset_of_preimage_subset`: hence `V` contains the
  associated points of `ω_{Y/X}`.
* `Stacks.Discriminant.GeneralizedTraceSection.sect_eq`: the extension of `τ_{V/X}` is unique.

## Implementation notes

The source takes `V` to be the whole flat locus; the structure below takes an arbitrary open
over which `f` is flat, which makes the hypothesis on associated points no weaker and the
conclusion about `ω_{Y/X}` no weaker.  Flatness over `V` is spelled chartwise, as flatness of
the coordinate-ring map of every affine chart of the source contained in `V` and lying over an
affine chart of the base; this is the form in which the trace element of [Stacks, Tag 0BT6] is
available.  For the same reason `Stacks.Discriminant.GeneralizedTraceSection` asks for the
trace-element condition exactly on the charts whose coordinate-ring map is flat, which are
precisely the charts inside the flat locus.

That the associated points of `ω_{Y/X}` lie over those of `X` is [Stacks, Tag 0BVD] read on a
chart, and uniqueness of the extension is injectivity of restriction to an open containing all
associated points, [Stacks, Tag 0B3L].

## References

* [Stacks Project, Tag 0BWM](https://stacks.math.columbia.edu/tag/0BWM)
* [Stacks Project, Tag 0BVD](https://stacks.math.columbia.edu/tag/0BVD)
* [Stacks Project, Tag 0B3L](https://stacks.math.columbia.edu/tag/0B3L)
* [Stacks Project, Tag 0BT7](https://stacks.math.columbia.edu/tag/0BT7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

universe u

namespace Stacks.Discriminant

open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

variable {X Y : Scheme.{u}} {f : Y ⟶ X}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyQuasiFinite f]

/-! ### Associated points of the relative dualizing module -/

/-- **[Stacks, Tag 0BVD], globally.** Every associated point of the relative dualizing module of
a locally quasi-finite morphism of locally Noetherian schemes lies over an associated point of
the base. -/
theorem associatedPoints_subset_preimage_schemeAssociatedPoints
    (ω : RelativeDualizingModuleData f) :
    Stacks.Divisors.associatedPoints ω.sheaf ⊆
      f.base ⁻¹' Stacks.Divisors.schemeAssociatedPoints X := by
  intro y hy
  obtain ⟨U, W, hyW, hWU⟩ := exists_affineChartPair f y
  let : Algebra Γ(X, U.1) Γ(Y, W.1) := (f.appLE U W hWU).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsNoetherianRing Γ(Y, W.1) := IsLocallyNoetherian.component_noetherian W
  let : ω.sheaf.IsQuasicoherent := ω.isQuasicoherent
  let F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, W.1) :=
    Classical.choice (ω.factorization U W hWU)
  have hq : (W.2.primeIdealOf ⟨y, hyW⟩).asIdeal ∈
      associatedPrimes Γ(Y, W.1) Γ(ω.sheaf, W.1) :=
    (Stacks.RingTheory.AssociatedPrimeStacks.assStacks_eq_associatedPrimes
      Γ(Y, W.1) Γ(ω.sheaf, W.1)) ▸
      ((isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian
        ω.sheaf W.1 W.2 hyW).mpr hy)
  have hqF : (W.2.primeIdealOf ⟨y, hyW⟩).asIdeal ∈
      associatedPrimes Γ(Y, W.1) (dualizingModule F) := by
    rwa [← LinearEquiv.AssociatedPrimes.eq (ω.localEquiv U W hWU F)]
  -- Tag 0BVD: it lies over an associated prime of `Γ(X, U)`
  have hcomap := (mem_associatedPrimes_dualizingModule_iff F (W.2.primeIdealOf ⟨y, hyW⟩)).mp hqF
  have heq : (U.2.primeIdealOf ⟨f.base y, hWU hyW⟩).asIdeal =
      Ideal.comap (algebraMap Γ(X, U.1) Γ(Y, W.1))
        (W.2.primeIdealOf ⟨y, hyW⟩).asIdeal :=
    (congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE U.1 U.2 W.1 W.2 hWU hyW)).symm
  let : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
  let : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
      (SheafOfModules.unit X.ringCatSheaf)).1
  have hstacks : (U.2.primeIdealOf ⟨f.base y, hWU hyW⟩).asIdeal ∈
      assStacks Γ(X, U.1) Γ(X, U.1) := by
    rw [Stacks.RingTheory.AssociatedPrimeStacks.assStacks_eq_associatedPrimes]
    exact Set.mem_of_eq_of_mem heq hcomap
  exact isAssociatedPoint_of_isAssociatedPrime_sections (SheafOfModules.unit X.ringCatSheaf)
    U.1 U.2 (hWU hyW) hstacks

/-- **[Stacks, Tag 0BWM], condition (1).** An open of the source containing the inverse image of
the associated points of the base contains the associated points of the relative dualizing
module. -/
@[stacks 0BWM "the associated points of the relative dualizing module lie in the flat locus"]
theorem associatedPoints_subset_of_preimage_subset (ω : RelativeDualizingModuleData f)
    (V : Y.Opens)
    (hV : f.base ⁻¹' Stacks.Divisors.schemeAssociatedPoints X ⊆ (V : Set Y)) :
    Stacks.Divisors.associatedPoints ω.sheaf ⊆ (V : Set Y) :=
  (associatedPoints_subset_preimage_schemeAssociatedPoints ω).trans hV

/-- A global section of the relative dualizing module is determined by its restriction to an
open containing the inverse image of the associated points of the base.  This is [Stacks,
Tag 0B3L] combined with the preceding lemma. -/
theorem sect_eq_of_restrictₗ_eq (ω : RelativeDualizingModuleData f) (V : Y.Opens)
    (hV : f.base ⁻¹' Stacks.Divisors.schemeAssociatedPoints X ⊆ (V : Set Y))
    {s t : Γ(ω.sheaf, ⊤)}
    (h : restrictₗ ω.sheaf (show V ≤ ⊤ from le_top) s =
      restrictₗ ω.sheaf (show V ≤ ⊤ from le_top) t) :
    s = t :=
  let : ω.sheaf.IsQuasicoherent := ω.isQuasicoherent
  restriction_injective_of_associatedPoints_subset Y ω.sheaf V
    (associatedPoints_subset_of_preimage_subset ω V hV) h

/-! ### The situation of the generalized different -/

/-- The hypotheses of [Stacks, Tag 0BWM] on a quasi-finite morphism `f : Y ⟶ X` of locally
Noetherian schemes: an open `V ⊆ Y` over which `f` is flat and which contains `Ass(𝒪_Y)` and
`f⁻¹(Ass(𝒪_X))`. -/
structure GeneralizedDifferentSituation {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyQuasiFinite f] where
  /-- The open over which `f` is flat. -/
  V : Y.Opens
  /-- `f` is flat over `V`: every affine chart of the source inside `V` lying over an affine
  chart of the base has flat coordinate-ring map. -/
  flat : ∀ (U : X.affineOpens) (W : Y.affineOpens) (hWU : W.1 ≤ f ⁻¹ᵁ U.1), W.1 ≤ V →
    letI : Algebra Γ(X, U.1) Γ(Y, W.1) := (f.appLE U W hWU).hom.toAlgebra
    Module.Flat Γ(X, U.1) Γ(Y, W.1)
  /-- `V` contains the associated points of the source. -/
  schemeAssociatedPoints_source_subset :
    Stacks.Divisors.schemeAssociatedPoints Y ⊆ (V : Set Y)
  /-- `V` contains the inverse image of the associated points of the base. -/
  preimage_schemeAssociatedPoints_base_subset :
    f.base ⁻¹' Stacks.Divisors.schemeAssociatedPoints X ⊆ (V : Set Y)

namespace GeneralizedDifferentSituation

/-- An affine chart pair of `f` whose source chart is contained in `V`.  The coordinate-ring map
of such a pair is flat, and the source charts of these pairs cover `V`. -/
def ChartPairIn (S : GeneralizedDifferentSituation f) : Type u :=
  {p : X.affineOpens × Y.affineOpens // (p.2).1 ≤ f ⁻¹ᵁ (p.1).1 ∧ (p.2).1 ≤ S.V}

/-- Every point of `V` lies in an affine chart of the source contained in `V` and lying over an
affine chart of the base. -/
theorem exists_chartPairIn (S : GeneralizedDifferentSituation f) {y : Y} (hy : y ∈ S.V) :
    ∃ p : S.ChartPairIn, y ∈ ((p.1).2).1 := by
  obtain ⟨-, ⟨U, hU, rfl⟩, hfy, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f.base y)) isOpen_univ
  obtain ⟨-, ⟨W, hW, rfl⟩, hyW, hWsub⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ ((f ⁻¹ᵁ U) ⊓ S.V : Y.Opens).1 from ⟨hfy, hy⟩) ((f ⁻¹ᵁ U) ⊓ S.V).2
  exact ⟨⟨(⟨U, hU⟩, ⟨W, hW⟩), fun _ hz ↦ (hWsub hz).1, fun _ hz ↦ (hWsub hz).2⟩, hyW⟩

/-- The source charts of the chart pairs inside `V` cover `V`. -/
theorem le_iSup_chartPairIn (S : GeneralizedDifferentSituation f) :
    S.V ≤ ⨆ p : S.ChartPairIn, ((p.1).2).1 := by
  intro y hy
  obtain ⟨p, hyp⟩ := S.exists_chartPairIn hy
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨p, hyp⟩

end GeneralizedDifferentSituation

/-! ### The trace extension and the generalized different -/

/-- The extension of the trace element `τ_{V/X}` of [Stacks, Tag 0BVJ] to the whole source, as
data: a global section of the relative dualizing module whose image under the affine
identification of every chart with *flat* coordinate-ring map is a trace element in the sense of
[Stacks, Tag 0BT6].  The flat charts are exactly the charts inside the flat locus, so this says
that the section restricts to `τ_{V/X}` on `V`. -/
structure GeneralizedTraceSection (ω : RelativeDualizingModuleData f) where
  /-- The global section of the relative dualizing module. -/
  sect : Γ(ω.sheaf, ⊤)
  /-- On every affine chart with flat coordinate-ring map the section is the trace element. -/
  isTraceElement_localEquiv :
    ∀ (U : X.affineOpens) (W : Y.affineOpens) (hWU : W.1 ≤ f ⁻¹ᵁ U.1),
      letI : Algebra Γ(X, U.1) Γ(Y, W.1) := (f.appLE U W hWU).hom.toAlgebra
      letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
      letI : IsNoetherianRing Γ(Y, W.1) := IsLocallyNoetherian.component_noetherian W
      ∀ hflat : Module.Flat Γ(X, U.1) Γ(Y, W.1),
        letI : Module.Flat Γ(X, U.1) Γ(Y, W.1) := hflat
        letI : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, W.1) :=
          RingHom.quasiFinite_algebraMap.mp
            (LocallyQuasiFinite.quasiFinite_appLE U.2 W.2 hWU)
        ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, W.1),
          IsTraceElement.{u, u, u, u, u, u} F
            (ω.localEquiv U W hWU F (restrictₗ ω.sheaf (show W.1 ≤ ⊤ from le_top) sect))

namespace GeneralizedTraceSection

/-- Two extensions of the trace element agree on every affine chart with flat coordinate-ring
map. -/
theorem restrictₗ_eq (ω : RelativeDualizingModuleData f) (τ₁ τ₂ : GeneralizedTraceSection ω)
    (U : X.affineOpens) (W : Y.affineOpens) (hWU : W.1 ≤ f ⁻¹ᵁ U.1)
    (hflat : letI : Algebra Γ(X, U.1) Γ(Y, W.1) := (f.appLE U W hWU).hom.toAlgebra
      Module.Flat Γ(X, U.1) Γ(Y, W.1)) :
    restrictₗ ω.sheaf (show W.1 ≤ ⊤ from le_top) τ₁.sect =
      restrictₗ ω.sheaf (show W.1 ≤ ⊤ from le_top) τ₂.sect := by
  let : Algebra Γ(X, U.1) Γ(Y, W.1) := (f.appLE U W hWU).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsNoetherianRing Γ(Y, W.1) := IsLocallyNoetherian.component_noetherian W
  let : Module.Flat Γ(X, U.1) Γ(Y, W.1) := hflat
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, W.1) :=
    RingHom.quasiFinite_algebraMap.mp (LocallyQuasiFinite.quasiFinite_appLE U.2 W.2 hWU)
  let F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, W.1) :=
    Classical.choice (ω.factorization U W hWU)
  exact (ω.localEquiv U W hWU F).injective
    (isTraceElement_unique F (τ₁.isTraceElement_localEquiv U W hWU hflat F)
      (τ₂.isTraceElement_localEquiv U W hWU hflat F))

/-- **[Stacks, Tag 0BWM], uniqueness of the extension.** In the situation of Tag 0BWM a global
section of the relative dualizing module extending the trace element `τ_{V/X}` is unique. -/
@[stacks 0BWM "uniqueness of the extension of the trace element"]
theorem sect_eq (S : GeneralizedDifferentSituation f) (ω : RelativeDualizingModuleData f)
    (τ₁ τ₂ : GeneralizedTraceSection ω) : τ₁.sect = τ₂.sect := by
  refine sect_eq_of_restrictₗ_eq ω S.V S.preimage_schemeAssociatedPoints_base_subset ?_
  refine TopCat.Sheaf.eq_of_locally_eq'
    (⟨ω.sheaf.presheaf, ω.sheaf.isSheaf⟩ : TopCat.Sheaf Ab (Y : TopCat.{u}))
    (fun p : S.ChartPairIn => ((p.1).2).1) S.V (fun p => homOfLE p.2.2)
    S.le_iSup_chartPairIn _ _ fun p => ?_
  obtain ⟨⟨U, W⟩, hWU, hWV⟩ := p
  have key : ∀ τ : GeneralizedTraceSection ω,
      (ω.sheaf.presheaf.map (homOfLE hWV).op)
          (restrictₗ ω.sheaf (show S.V ≤ ⊤ from le_top) τ.sect) =
        restrictₗ ω.sheaf (show W.1 ≤ ⊤ from le_top) τ.sect := by
    intro τ
    exact restrictₗ_restrictₗ ω.sheaf _ _ τ.sect
  rw [key τ₁, key τ₂]
  exact restrictₗ_eq ω τ₁ τ₂ U W hWU (S.flat U W hWU hWV)

end GeneralizedTraceSection

/-! ### The generalized different -/

/-- **[Stacks, Tag 0BWM].** The *generalized different* `𝔇_f` of a quasi-finite morphism of
locally Noetherian schemes which is flat near the associated points: the annihilator of the
cokernel of the map `𝒪_Y → ω_{Y/X}` given by the extension `τ` of the trace element
`τ_{V/X}`. -/
@[stacks 0BWM "the generalized different"]
def generalizedDifferent (ω : RelativeDualizingModuleData f) (τ : GeneralizedTraceSection ω) :
    (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)).Submodule :=
  annihilatorSectionCokernel ω τ.sect

/-- The generalized different is a coherent ideal of `𝒪_Y`. -/
theorem isCoherent_generalizedDifferent (ω : RelativeDualizingModuleData f)
    (τ : GeneralizedTraceSection ω) :
    Stacks.SheafOfModules.IsCoherent (generalizedDifferent ω τ).toSheafOfModules :=
  isCoherent_annihilatorSectionCokernel ω τ.sect

end Stacks.Discriminant

end
