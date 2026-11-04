module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.AdaptedOpens
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ChartInfrastructure
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModuleData0BVG
public import StacksFrontier.AlgebraicGeometry.Modules.BasisSectionExtension

/-!
# Uniqueness of the relative dualizing module of a locally quasi-finite morphism

Let `f : Y ⟶ X` be a locally quasi-finite morphism of locally Noetherian schemes.  A relative
dualizing module for `f` is a coherent `𝒪_Y`-module together with the identification of its
sections over every affine chart `Spec(B) = V ⊆ Y`, `Spec(A) = U ⊆ X` with `f(V) ⊆ U` with the
algebraic relative dualizing module `ω_{B/A}` of Tag 0BSZ, compatibly with the comparisons of
Tag 0BT2; this is the structure `Stacks.Discriminant.RelativeDualizingModuleData`.  This file
shows that such a module is unique: any two carry a *unique* isomorphism of sheaves of modules
compatible with all of those identifications.

Uniqueness is read in the sense of the source, namely up to the canonical isomorphism: two
relative dualizing modules are two sheaves, so they cannot be literally equal, and the content
of the assertion is that the identifications with the `ω_{B/A}` leave no freedom in comparing
them.

The comparison over a single affine chart is immediate — compose one chart identification with
the inverse of the other — and the work is to see that it does not depend on the chart and glues.
Three facts do that, and each is one of the compatibilities the structure carries, used twice:

* independence of the finite-open factorization computing `ω_{B/A}`, from
  `Stacks.Discriminant.RelativeDualizingModuleData.localEquiv_natural`;
* invariance under shrinking the base chart to a principal open, from
  `Stacks.Discriminant.RelativeDualizingModuleData.localEquiv_baseBasicOpen`;
* compatibility with restriction to a principal open of the source chart, from
  `Stacks.Discriminant.RelativeDualizingModuleData.localEquiv_basicOpen` together with the
  uniqueness of the
  normalised localization map `Stacks.Discriminant.localizedDualizingModuleMap_eq_of_eq_id` —
  without which the two data would be compared through two possibly different localization maps.

## Main definitions

* `Stacks.Discriminant.chartComparison`: the comparison of the sections of two relative
  dualizing modules over an affine chart, characterized by
  `Stacks.Discriminant.localEquiv_chartComparison`.

## Main results

* `Stacks.Discriminant.exists_affineChartPair_le`: the source opens of the affine chart pairs of
  `f` form a basis of the source.
* `Stacks.Discriminant.chartComparison_basicOpen` and
  `Stacks.Discriminant.chartComparison_baseBasicOpen`: the chart comparison commutes with
  shrinking the source chart to a principal open, and is unchanged by shrinking the base chart
  to a principal open.
* `Stacks.Discriminant.chartComparison_restrict`: the chart comparison commutes with restriction
  between *arbitrary* nested affine charts.
* `Stacks.Discriminant.existsUnique_relativeDualizingComparison`: **Tag 0BVG, uniqueness.** Any
  two relative dualizing modules of `f` are related by a unique isomorphism of their sheaves of
  sections, over every open, compatible with the restriction maps and with the identifications
  of the sections over every affine chart with the algebraic relative dualizing module of that
  chart.

## Implementation notes

The chart comparison is produced by `Stacks.Discriminant.exists_chartComparison` and named by
`Exists.choose`, so that the only thing ever known about it is the characterizing property
`Stacks.Discriminant.localEquiv_chartComparison`; the finite-open factorization used to build it
is then invisible, and no statement below has to quantify over one.

The two principal-shrinking lemmas are stated in the presented form `Y.basicOpen g` and
`X.basicOpen a`, because that is the form the compatibilities of
`Stacks.Discriminant.RelativeDualizingModuleData` take.
`Stacks.Discriminant.chartComparison_restrict_of_good` puts them together for an affine chart
which is a principal open of a given chart over a principal open of its base, taking the
presentations as equalities of opens and substituting them; this is what lets it be applied at an
`Stacks.Discriminant.AdaptedOpen` good for a chart, whose opens are not syntactically presented.

Compatibility with restriction between two arbitrary nested affine charts is then proved by
separation along a basis of the smaller one, and the basis used is the adapted opens good for
*both* charts: `Stacks.Discriminant.AdaptedOpen.exists_good_pair` says those form a basis of the
overlap of the two source charts, and goodness for a chart is exactly the hypothesis of
`Stacks.Discriminant.chartComparison_restrict_of_good`.  The extension from the chart opens to
all opens is `Stacks.Modules.exists_sectionEquiv_of_basis`, and uniqueness is
`Stacks.Modules.sectionsMap_eq_of_basis`.

## References

* [Stacks Project, Tag 0BSZ](https://stacks.math.columbia.edu/tag/0BSZ)
* [Stacks Project, Tag 0BT1](https://stacks.math.columbia.edu/tag/0BT1)
* [Stacks Project, Tag 0BT2](https://stacks.math.columbia.edu/tag/0BT2)
* [Stacks Project, Tag 0BVG](https://stacks.math.columbia.edu/tag/0BVG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.Discriminant

section Basis

variable {X Y : Scheme.{u}}

/-- **The source opens of the affine chart pairs form a basis of the source.** Every point of
every open of the source lies in an affine open contained in that open and mapping into an
affine open of the base. -/
public theorem exists_affineChartPair_le (f : Y ⟶ X) (W : Y.Opens) (y : Y) (hy : y ∈ W) :
    ∃ p : AffineChartPair f, y ∈ ((p.1).2).1 ∧ ((p.1).2).1 ≤ W := by
  obtain ⟨-, ⟨U, hU, rfl⟩, hfy, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f.base y)) isOpen_univ
  obtain ⟨-, ⟨V, hV, rfl⟩, hyV, hVW⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ (W ⊓ f ⁻¹ᵁ U).1 from ⟨hy, hfy⟩) (W ⊓ f ⁻¹ᵁ U).2
  exact ⟨⟨(⟨U, hU⟩, ⟨V, hV⟩), hVW.trans inf_le_right⟩, hyV, hVW.trans inf_le_left⟩

/-- The source opens of the affine chart pairs form a basis of every open of the source, in the
form the extension and separation lemmas of `Stacks.Modules` ask for. -/
public theorem isBasis_affineChartPair (f : Y ⟶ X) (T : Y.Opens) :
    ∀ W : Y.Opens, W ≤ T → ∀ y ∈ W, ∃ p : AffineChartPair f,
      y ∈ ((p.1).2).1 ∧ ((p.1).2).1 ≤ W :=
  fun W _ ↦ exists_affineChartPair_le f W

/-- Restriction of sections through an intermediate open is restriction to the smaller open. -/
private theorem restrictₗ_trans (M : Y.Modules) {V W T : Y.Opens} (h₁ : T ≤ W) (h₂ : W ≤ V)
    (s : Γ(M, V)) : restrictₗ M h₁ (restrictₗ M h₂ s) = restrictₗ M (h₁.trans h₂) s := by
  show ((M.presheaf.map (homOfLE h₂).op) ≫ (M.presheaf.map (homOfLE h₁).op)).hom s =
    (M.presheaf.map (homOfLE (h₁.trans h₂)).op).hom s
  rw [← M.presheaf.map_comp]
  congr 2

end Basis

section Comparison

variable {X Y : Scheme.{u}} {f : Y ⟶ X} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  [LocallyQuasiFinite f]

/-- Two sections over an affine chart are equal as soon as they have the same image in the
algebraic relative dualizing module for every finite-open factorization. -/
private theorem eq_of_forall_localEquiv_eq (D : RelativeDualizingModuleData f) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (s t : Γ(D.sheaf, V.1))
    (h : letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
      ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1),
        D.localEquiv U V hVU F s = D.localEquiv U V hVU F t) : s = t := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  exact (D.localEquiv U V hVU (Classical.choice (D.factorization U V hVU))).injective (h _)

/-- **The comparison of two relative dualizing modules over one affine chart exists.** Composing
the identification of the sections of the first with the algebraic relative dualizing module of
the chart with the inverse of the identification of the second gives an isomorphism which, by
independence of the finite-open factorization, intertwines the two identifications for *every*
factorization. -/
public theorem exists_chartComparison (D D' : RelativeDualizingModuleData f) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    ∃ c : Γ(D.sheaf, V.1) ≃ₗ[Γ(Y, V.1)] Γ(D'.sheaf, V.1),
      letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
      ∀ (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1)) (s : Γ(D.sheaf, V.1)),
        D'.localEquiv U V hVU F (c s) = D.localEquiv U V hVU F s := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let F₀ : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1) :=
    Classical.choice (D.factorization U V hVU)
  refine ⟨(D.localEquiv U V hVU F₀).trans (D'.localEquiv U V hVU F₀).symm, fun F s ↦ ?_⟩
  rw [D'.localEquiv_natural U V hVU F₀ F, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  exact (D.localEquiv_natural U V hVU F₀ F s).symm

/-- **The comparison of two relative dualizing modules over one affine chart.** -/
public def chartComparison (D D' : RelativeDualizingModuleData f) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    Γ(D.sheaf, V.1) ≃ₗ[Γ(Y, V.1)] Γ(D'.sheaf, V.1) :=
  (exists_chartComparison D D' U V hVU).choose

/-- **The characterizing property of the chart comparison.** It carries the identification of the
sections of the first module with the algebraic relative dualizing module of the chart to that of
the second, through every finite-open factorization. -/
public theorem localEquiv_chartComparison (D D' : RelativeDualizingModuleData f)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    ∀ (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1)) (s : Γ(D.sheaf, V.1)),
      D'.localEquiv U V hVU F (chartComparison D D' U V hVU s) =
        D.localEquiv U V hVU F s :=
  (exists_chartComparison D D' U V hVU).choose_spec

/-- **Shrinking the base chart to a principal open does not change the chart comparison.** -/
public theorem chartComparison_baseBasicOpen (D D' : RelativeDualizingModuleData f)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (a : Γ(X, U.1))
    (hVa : V.1 ≤ f ⁻¹ᵁ (X.basicOpen a)) (s : Γ(D.sheaf, V.1)) :
    chartComparison D D' ⟨X.basicOpen a, U.2.basicOpen a⟩ V hVa s =
      chartComparison D D' U V hVU s := by
  set Ua : X.affineOpens := ⟨X.basicOpen a, U.2.basicOpen a⟩
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : Algebra Γ(X, Ua.1) Γ(Y, V.1) := (f.appLE Ua V hVa).hom.toAlgebra
  let : IsNoetherianRing Γ(X, Ua.1) := IsLocallyNoetherian.component_noetherian Ua
  let F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1) :=
    Classical.choice (D.factorization U V hVU)
  refine eq_of_forall_localEquiv_eq D' Ua V hVa _ _ fun G ↦ ?_
  rw [localEquiv_chartComparison D D' Ua V hVa G,
    D'.localEquiv_baseBasicOpen U V hVU a hVa F G (chartComparison D D' U V hVU s),
    localEquiv_chartComparison D D' U V hVU F]
  exact D.localEquiv_baseBasicOpen U V hVU a hVa F G s

/-- **The chart comparison commutes with restriction to a principal open of the source chart.**
The two relative dualizing modules localize along *the same* map of algebraic relative dualizing
modules, because the normalised localization map of Tag 0BT2 part (2) is unique. -/
public theorem chartComparison_basicOpen (D D' : RelativeDualizingModuleData f)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (g : Γ(Y, V.1))
    (s : Γ(D.sheaf, V.1)) :
    chartComparison D D' U ⟨Y.basicOpen g, V.2.basicOpen g⟩ ((Y.basicOpen_le g).trans hVU)
        (restrictₗ D.sheaf (Y.basicOpen_le g) s) =
      restrictₗ D'.sheaf (Y.basicOpen_le g) (chartComparison D D' U V hVU s) := by
  set W : Y.affineOpens := ⟨Y.basicOpen g, V.2.basicOpen g⟩
  set hWU : W.1 ≤ f ⁻¹ᵁ U.1 := (Y.basicOpen_le g).trans hVU
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let : Algebra Γ(X, U.1) Γ(Y, W.1) := (f.appLE U W hWU).hom.toAlgebra
  let : Algebra Γ(Y, V.1) Γ(Y, W.1) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom.toAlgebra
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : IsNoetherianRing Γ(Y, V.1) := IsLocallyNoetherian.component_noetherian V
  let : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
    (RingHom.quasiFinite_algebraMap).mp (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
  let : IsLocalization.Away g Γ(Y, W.1) := V.2.isLocalization_basicOpen g
  let : IsScalarTower Γ(X, U.1) Γ(Y, V.1) Γ(Y, W.1) :=
    IsScalarTower.of_algebraMap_eq' (by
      show (f.appLE U W hWU).hom =
        ((Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom).comp (f.appLE U V hVU).hom
      rw [← CommRingCat.hom_comp, ← f.appLE_map hVU (homOfLE (Y.basicOpen_le g)).op])
  let F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1) :=
    Classical.choice (D.factorization U V hVU)
  refine eq_of_forall_localEquiv_eq D' U W hWU _ _ fun G ↦ ?_
  let : Module Γ(Y, V.1) (dualizingModule G) :=
    Module.compHom (dualizingModule G) (algebraMap Γ(Y, V.1) Γ(Y, W.1))
  let : IsScalarTower Γ(Y, V.1) Γ(Y, W.1) (dualizingModule G) :=
    IsScalarTower.of_compHom Γ(Y, V.1) Γ(Y, W.1) _
  obtain ⟨r₁, hr₁, hres₁, hnorm₁⟩ := D.localEquiv_basicOpen U V hVU g F G
  obtain ⟨r₂, hr₂, hres₂, hnorm₂⟩ := D'.localEquiv_basicOpen U V hVU g F G
  rw [localEquiv_chartComparison D D' U W hWU G, hres₂ (chartComparison D D' U V hVU s),
    localEquiv_chartComparison D D' U V hVU F,
    ← localizedDualizingModuleMap_eq_of_eq_id g F G r₁ r₂ hr₁ hr₂ hnorm₁ hnorm₂]
  exact hres₁ s

/-- **The chart comparison commutes with restriction to an affine chart which is a principal
open of the given one over a principal open of its base.** This is the two principal-shrinking
lemmas composed, with the presentations of the two smaller opens taken as hypotheses rather than
substituted into the statement. -/
public theorem chartComparison_restrict_of_good (D D' : RelativeDualizingModuleData f)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (U' : X.affineOpens) (V' : Y.affineOpens) (hV'U' : V'.1 ≤ f ⁻¹ᵁ U'.1)
    (g : Γ(Y, V.1)) (hg : V'.1 = Y.basicOpen g) (a : Γ(X, U.1)) (ha : U'.1 = X.basicOpen a)
    (hV'V : V'.1 ≤ V.1) (s : Γ(D.sheaf, V.1)) :
    chartComparison D D' U' V' hV'U' (restrictₗ D.sheaf hV'V s) =
      restrictₗ D'.sheaf hV'V (chartComparison D D' U V hVU s) := by
  obtain rfl : V' = ⟨Y.basicOpen g, V.2.basicOpen g⟩ := Subtype.ext hg
  obtain rfl : U' = ⟨X.basicOpen a, U.2.basicOpen a⟩ := Subtype.ext ha
  exact (chartComparison_baseBasicOpen D D' U ⟨Y.basicOpen g, V.2.basicOpen g⟩
      ((Y.basicOpen_le g).trans hVU) a hV'U' (restrictₗ D.sheaf hV'V s)).trans
    (chartComparison_basicOpen D D' U V hVU g s)

/-- **The chart comparison commutes with restriction between arbitrary nested affine charts.**
Separation along a basis of the smaller source chart reduces this to the case of an adapted open
good for both charts, which is `chartComparison_restrict_of_good`; the adapted opens good for
both charts form such a basis. -/
public theorem chartComparison_restrict (D D' : RelativeDualizingModuleData f)
    (p q : AffineChartPair f) (h : ((q.1).2).1 ≤ ((p.1).2).1)
    (s : Γ(D.sheaf, ((p.1).2).1)) :
    chartComparison D D' (q.1).1 (q.1).2 q.2 (restrictₗ D.sheaf h s) =
      restrictₗ D'.sheaf h (chartComparison D D' (p.1).1 (p.1).2 p.2 s) := by
  refine Stacks.Modules.sections_eq_of_basis (T := ((q.1).2).1)
    (W := fun k : {k : AdaptedOpen f //
      k.Good ((p.1).2) ((p.1).1) ∧ k.Good ((q.1).2) ((q.1).1)} ↦ (k.1).source.1)
    D'.sheaf ?_ le_rfl _ _ ?_
  · intro T hT y hy
    obtain ⟨k, hkp, hkq, hyk, hkT⟩ := AdaptedOpen.exists_good_pair
      (fun r : AffineChartPair f ↦ (r.1).2) (fun r : AffineChartPair f ↦ (r.1).1)
      (fun r ↦ r.2) p q T (hT.trans (le_inf h le_rfl)) y hy
    exact ⟨⟨k, hkp, hkq⟩, hyk, hkT⟩
  · intro k hk
    have key : ∀ (r : AffineChartPair f) (hr : (k.1).Good ((r.1).2) ((r.1).1))
        (t : Γ(D.sheaf, ((r.1).2).1)),
        chartComparison D D' (k.1).base (k.1).source (k.1).source_le (restrictₗ D.sheaf hr.le t) =
          restrictₗ D'.sheaf hr.le (chartComparison D D' (r.1).1 (r.1).2 r.2 t) := by
      intro r hr t
      obtain ⟨g, hg⟩ := hr.1
      obtain ⟨a, ha⟩ := hr.2
      exact chartComparison_restrict_of_good D D' (r.1).1 (r.1).2 r.2 (k.1).base
        (k.1).source (k.1).source_le g hg.symm a ha.symm hr.le t
    have hq := key q (k.2).2 (restrictₗ D.sheaf h s)
    have hp := key p (k.2).1 s
    show restrictₗ D'.sheaf hk (chartComparison D D' (q.1).1 (q.1).2 q.2
        (restrictₗ D.sheaf h s)) =
      restrictₗ D'.sheaf hk (restrictₗ D'.sheaf h (chartComparison D D' (p.1).1 (p.1).2 p.2 s))
    rw [restrictₗ_trans D'.sheaf hk h, ← hp, ← hq, restrictₗ_trans D.sheaf (k.2).2.le h]

end Comparison

section Uniqueness

variable {X Y : Scheme.{u}} {f : Y ⟶ X} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  [LocallyQuasiFinite f]

/-- **Two relative dualizing modules of `f` have isomorphic sheaves of sections.** The chart
comparisons extend from the affine charts, which form a basis of the source, to an isomorphism of
the sections over every open compatible with the restriction maps. -/
public theorem exists_relativeDualizingComparison (D D' : RelativeDualizingModuleData f) :
    ∃ E : ∀ W : Y.Opens, Γ(D.sheaf, W) ≃ₗ[Γ(Y, W)] Γ(D'.sheaf, W),
      (∀ (W W' : Y.Opens) (h : W' ≤ W) (s : Γ(D.sheaf, W)),
          E W' (restrictₗ D.sheaf h s) = restrictₗ D'.sheaf h (E W s)) ∧
        ∀ (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
          (s : Γ(D.sheaf, V.1)), E V.1 s = chartComparison D D' U V hVU s := by
  obtain ⟨E, hnat, hchart⟩ := Stacks.Modules.exists_sectionEquiv_of_basis D.sheaf D'.sheaf ⊤
    (fun p : AffineChartPair f ↦ ((p.1).2).1) (isBasis_affineChartPair f ⊤)
    (fun p ↦ chartComparison D D' (p.1).1 (p.1).2 p.2)
    (chartComparison_restrict D D')
  exact ⟨fun W ↦ E W le_top, fun W W' hW s ↦ hnat W W' le_top le_top hW s,
    fun U V hVU s ↦ hchart ⟨(U, V), hVU⟩ le_top s⟩

/-- **Stacks Project, Tag 0BVG, uniqueness.** The relative dualizing module of a locally
quasi-finite morphism of locally Noetherian schemes is unique: any two coherent `𝒪_Y`-modules
carrying the chart data of Tag 0BVG are related by one and only one isomorphism of their sections
over every open of the source which is compatible with the restriction maps and which carries the
identification of the sections over every affine chart `Spec(B) = V ⊆ Y`, `Spec(A) = U ⊆ X` with
`f(V) ⊆ U` with `ω_{B/A}` to the other.

As in the source, uniqueness is uniqueness up to the canonical isomorphism: the two modules are
two sheaves and cannot be literally equal, and what is asserted is that the identifications
`H⁰(V, ω_{Y/X}) = ω_{B/A}` determine the comparison between them completely. -/
@[stacks 0BVG "uniqueness"]
public theorem existsUnique_relativeDualizingComparison
    (D D' : RelativeDualizingModuleData f) [LocallyOfFiniteType f] :
    ∃! E : ∀ W : Y.Opens, Γ(D.sheaf, W) ≃ₗ[Γ(Y, W)] Γ(D'.sheaf, W),
      (∀ (W W' : Y.Opens) (h : W' ≤ W) (s : Γ(D.sheaf, W)),
          E W' (restrictₗ D.sheaf h s) = restrictₗ D'.sheaf h (E W s)) ∧
        ∀ (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1),
          letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
          ∀ (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
            (s : Γ(D.sheaf, V.1)),
            D'.localEquiv U V hVU F (E V.1 s) = D.localEquiv U V hVU F s := by
  obtain ⟨E₀, hnat₀, hchart₀⟩ := exists_relativeDualizingComparison D D'
  have hagree : ∀ (E : ∀ W : Y.Opens, Γ(D.sheaf, W) ≃ₗ[Γ(Y, W)] Γ(D'.sheaf, W)),
      (∀ (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1),
        letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
        ∀ (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
          (s : Γ(D.sheaf, V.1)),
          D'.localEquiv U V hVU F (E V.1 s) = D.localEquiv U V hVU F s) →
      ∀ (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
        (s : Γ(D.sheaf, V.1)), E V.1 s = chartComparison D D' U V hVU s := by
    intro E hE U V hVU s
    refine eq_of_forall_localEquiv_eq D' U V hVU _ _ fun F ↦ ?_
    rw [hE U V hVU F s, localEquiv_chartComparison D D' U V hVU F s]
  refine ⟨E₀, ⟨hnat₀, fun U V hVU F s ↦ ?_⟩, fun E hE ↦ ?_⟩
  · rw [hchart₀ U V hVU s, localEquiv_chartComparison D D' U V hVU F s]
  · funext W
    refine LinearEquiv.ext fun s ↦ ?_
    refine Stacks.Modules.sectionsMap_eq_of_basis (T := (⊤ : Y.Opens))
      (W := fun p : AffineChartPair f ↦ ((p.1).2).1) D.sheaf D'.sheaf
      (isBasis_affineChartPair f ⊤) (fun V _ s ↦ E V s) (fun V _ s ↦ E₀ V s)
      (fun V V' _ _ hV' s ↦ hE.1 V V' hV' s) (fun V V' _ _ hV' s ↦ hnat₀ V V' hV' s)
      (fun p _ s ↦ ?_) le_top s
    rw [hagree E hE.2 (p.1).1 (p.1).2 p.2 s, hchart₀ (p.1).1 (p.1).2 p.2 s]

end Uniqueness

end Stacks.Discriminant

end
