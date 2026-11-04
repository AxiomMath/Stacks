module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.NonAlgebraizableLevelKernel

/-!
# `lim H⁰(U, 𝓛ₙ)` for the non-algebraizable example

The second proof of non-algebraizability in [Stacks, Tag 0EHE] rests on the module
`lim H⁰(U, 𝓛ₙ)` of the system `(𝓛ₙ)`: it is nonzero for the degenerate choice `aₘ = 0`, and zero
for `aₘ = 1` with `φ(m) = 2ᵐ` or `φ(m) = m²`. Both computations are carried out in
`Stacks.Algebraization.NonAlgebraizableExample.sectionsLimit`, the module of compatible systems of
pairs of chart functions matched by the transition elements
(`Stacks.Algebraization.NonAlgebraizableExample.sectionsLimit_ne_bot` and
`Stacks.Algebraization.NonAlgebraizableExample.sectionsLimit_eq_bot`). This file identifies that
module with the limit of the actual global sections, `Stacks.Algebraization.limitGlobalSections` of
the object `Stacks.Algebraization.NonAlgebraizableExample.levelCoherentAdicSystem` of
`Coh(U, I𝒪_U)`, so that the two computations are statements about `lim H⁰(U, 𝓛ₙ)`.

## Main definitions

* `Stacks.SheafOfModules.twoChartCoords` — the two chart coordinates of a section of a module glued
  from a unit on the overlap of a two-chart cover, over an open containing both charts.
* `Stacks.Algebraization.NonAlgebraizableExample.levelSectionsAddEquiv` — `H⁰(U, 𝓛ₘ₊₁)` is the
  module of pairs of chart functions modulo `tᵐ⁺¹` matched by the transition element.
* `Stacks.Algebraization.NonAlgebraizableExample.sectionsLimitLinearEquiv` — `sectionsLimit` is
  `lim H⁰(U, 𝓛ₙ)`, as `A`-modules.

## Main results

* `Stacks.SheafOfModules.twoChartCoords_match`, `Stacks.SheafOfModules.twoChartCoords_injective`
  and `Stacks.SheafOfModules.exists_twoChartCoords_eq` — a section of a two-chart glue over an
  open containing both charts is the same as a pair of chart functions matched by the overlap unit.
* `Stacks.Algebraization.NonAlgebraizableExample.levelSectionsCoords_levelTransitionOnOpen` — the
  maps of the system on global sections are the reductions of chart functions.
* `Stacks.Algebraization.NonAlgebraizableExample.nontrivial_limitGlobalSections` —
  `lim H⁰(U, 𝓛ₙ) ≠ 0` when `aₘ = 0` for `m ≥ 2`.
* `Stacks.Algebraization.NonAlgebraizableExample.subsingleton_limitGlobalSections` —
  `lim H⁰(U, 𝓛ₙ) = 0` when `aₘ = 1` for `m ≥ 2` and `φ(m) = 2ᵐ` or `φ(m) = m²`.

## Implementation notes

A section of the glued module over an open `W` is, by construction, a compatible family of local
coordinates over the opens `W ∩ Uᵢ`; when `W` contains both charts the coordinate on `Uᵢ` is its
restriction along `Uᵢ ≤ W ∩ Uᵢ`, and that restriction is an isomorphism. The chart coordinates in
the chart rings are read through
`Stacks.Algebraization.NonAlgebraizableExample.levelChartRingEquiv`.

The system `levelCoherentAdicSystem` has `𝓛ₘ₊₁` as its `m`-th term, while `sectionsLimit` is
indexed from order `0`; the term of order `0` is zero on the chart rings `A_r/t⁰A_r = 0`, so the
two limits agree.

The ring of the algebraization situation `situation k` is `A = k[x,y][[t]]` by definition, but not
reducibly so; the `A`-module structure of `sectionsLimit` is restated over `(situation k).A` by
`moduleSituationSectionsLimit` so that the identification can be stated as a linear equivalence.

## References

* [Stacks Project, Tag 0EHE](https://stacks.math.columbia.edu/tag/0EHE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] Stacks.SheafOfModules.UnitTransitionCocycle.sectionsProductModule

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}} {U₀ U₁ : Opens X.carrier}

private theorem map_map_apply {T : TopCat.{u}} {F : TopCat.Presheaf CommRingCat.{u} T}
    {V₁ V₂ V₃ : Opens T} (h₁ : V₂ ≤ V₁) (h₂ : V₃ ≤ V₂) (z : F.obj (op V₁)) :
    (F.map (homOfLE h₂).op).hom ((F.map (homOfLE h₁).op).hom z) =
      (F.map (homOfLE (h₂.trans h₁)).op).hom z := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← CategoryTheory.Functor.map_comp]
  rfl

private theorem map_self_apply {T : TopCat.{u}} {F : TopCat.Presheaf CommRingCat.{u} T}
    {V : Opens T} (h : V ≤ V) (z : F.obj (op V)) :
    (F.map (homOfLE h).op).hom z = z := by
  rw [show (homOfLE h).op = 𝟙 (op V) from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
  rfl

/-- The two chart coordinates of a section of the module glued from a unit on the overlap of a
two-chart cover, over an open containing both charts. -/
public def twoChartCoords (u : (X.presheaf.obj (op (U₀ ⊓ U₁)))ˣ) {W : Opens X.carrier}
    (h₀ : U₀ ≤ W) (h₁ : U₁ ≤ W) :
    (twoChartCocycle u).sectionsSubmodule W →+
      X.presheaf.obj (op U₀) × X.presheaf.obj (op U₁) where
  toFun s := ((X.presheaf.map (homOfLE (le_inf h₀ le_rfl :
      U₀ ≤ W ⊓ twoChartFamily U₀ U₁ ⟨false⟩)).op).hom (s.val ⟨false⟩),
    (X.presheaf.map (homOfLE (le_inf h₁ le_rfl :
      U₁ ≤ W ⊓ twoChartFamily U₀ U₁ ⟨true⟩)).op).hom (s.val ⟨true⟩))
  map_zero' := by
    ext <;> exact map_zero _
  map_add' s t := by
    ext <;> exact map_add _ _ _

/-- The two chart coordinates of a section are matched by the overlap unit. -/
public theorem twoChartCoords_match (u : (X.presheaf.obj (op (U₀ ⊓ U₁)))ˣ)
    {W : Opens X.carrier} (h₀ : U₀ ≤ W) (h₁ : U₁ ≤ W)
    (s : (twoChartCocycle u).sectionsSubmodule W) :
    (X.presheaf.map (homOfLE (inf_le_right : U₀ ⊓ U₁ ≤ U₁)).op).hom
        (twoChartCoords u h₀ h₁ s).2 =
      u.val * (X.presheaf.map (homOfLE (inf_le_left : U₀ ⊓ U₁ ≤ U₀)).op).hom
        (twoChartCoords u h₀ h₁ s).1 := by
  have hP : U₀ ⊓ U₁ ≤ W ⊓ twoChartFamily U₀ U₁ ⟨false⟩ ⊓ (W ⊓ twoChartFamily U₀ U₁ ⟨true⟩) :=
    le_inf (le_inf (inf_le_left.trans h₀) inf_le_left) (le_inf (inf_le_right.trans h₁) inf_le_right)
  have hs := congrArg (X.presheaf.map (homOfLE hP).op).hom (s.2 ⟨false⟩ ⟨true⟩)
  rw [map_mul, map_map_apply, map_map_apply] at hs
  have hu := congrArg Units.val ((twoChartCocycle u).restrict (i := ⟨false⟩) (j := ⟨true⟩)
    (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) hP)
  change (X.presheaf.map (homOfLE hP).op).hom _ = _ at hu
  rw [hu] at hs
  change (X.presheaf.map (homOfLE _).op).hom u.val * _ = _ at hs
  rw [map_self_apply] at hs
  show (X.presheaf.map (homOfLE inf_le_right).op).hom
      ((X.presheaf.map (homOfLE _).op).hom _) =
    u.val * (X.presheaf.map (homOfLE inf_le_left).op).hom ((X.presheaf.map (homOfLE _).op).hom _)
  rw [map_map_apply, map_map_apply]
  exact hs.symm

/-- A section over an open containing both charts is determined by its two chart coordinates. -/
public theorem twoChartCoords_injective (u : (X.presheaf.obj (op (U₀ ⊓ U₁)))ˣ)
    {W : Opens X.carrier} (h₀ : U₀ ≤ W) (h₁ : U₁ ≤ W) :
    Function.Injective (twoChartCoords u h₀ h₁) := by
  intro s t hst
  have key : ∀ (i : ULift.{u} Bool) (h : twoChartFamily U₀ U₁ i ≤ W)
      (z : X.presheaf.obj (op (W ⊓ twoChartFamily U₀ U₁ i))),
      z = (X.presheaf.map (homOfLE (inf_le_right : W ⊓ twoChartFamily U₀ U₁ i ≤ _)).op).hom
        ((X.presheaf.map (homOfLE (le_inf h le_rfl :
          twoChartFamily U₀ U₁ i ≤ W ⊓ twoChartFamily U₀ U₁ i)).op).hom z) := by
    intro i h z
    rw [map_map_apply, map_self_apply]
  refine Subtype.ext (funext fun i => ?_)
  rcases i with ⟨_ | _⟩
  · rw [key ⟨false⟩ h₀ (s.val ⟨false⟩), key ⟨false⟩ h₀ (t.val ⟨false⟩)]
    exact congrArg _ (congrArg Prod.fst hst)
  · rw [key ⟨true⟩ h₁ (s.val ⟨true⟩), key ⟨true⟩ h₁ (t.val ⟨true⟩)]
    exact congrArg _ (congrArg Prod.snd hst)

/-- Every pair of chart functions matched by the overlap unit is the pair of chart coordinates of
a section over an open containing both charts. -/
public theorem exists_twoChartCoords_eq (u : (X.presheaf.obj (op (U₀ ⊓ U₁)))ˣ)
    {W : Opens X.carrier} (h₀ : U₀ ≤ W) (h₁ : U₁ ≤ W)
    (c : X.presheaf.obj (op U₀) × X.presheaf.obj (op U₁))
    (hc : (X.presheaf.map (homOfLE (inf_le_right : U₀ ⊓ U₁ ≤ U₁)).op).hom c.2 =
      u.val * (X.presheaf.map (homOfLE (inf_le_left : U₀ ⊓ U₁ ≤ U₀)).op).hom c.1) :
    ∃ s, twoChartCoords u h₀ h₁ s = c := by
  have key : ∀ (V : Opens X.carrier) (hV : V ≤ U₀ ⊓ U₁),
      (overlapUnit u V hV).val * (X.presheaf.map (homOfLE (hV.trans inf_le_left)).op).hom c.1 =
        (X.presheaf.map (homOfLE (hV.trans inf_le_right)).op).hom c.2 := by
    intro V hV
    show (X.presheaf.map (homOfLE hV).op).hom u.val * _ = _
    rw [← map_map_apply (inf_le_left : U₀ ⊓ U₁ ≤ U₀) hV, ← map_mul, ← hc, map_map_apply]
  let cc : (i : ULift.{u} Bool) → X.presheaf.obj (op (twoChartFamily U₀ U₁ i)) := fun i =>
    match i with
    | ⟨false⟩ => c.1
    | ⟨true⟩ => c.2
  refine ⟨⟨fun i => (X.presheaf.map (homOfLE (inf_le_right :
      W ⊓ twoChartFamily U₀ U₁ i ≤ twoChartFamily U₀ U₁ i)).op).hom (cc i), ?_⟩, ?_⟩
  · rintro ⟨_ | _⟩ ⟨_ | _⟩
    · show (1 : (X.presheaf.obj (op _))ˣ).val * _ = _
      rw [Units.val_one, one_mul]
    · show (overlapUnit u _ _).val * _ = _
      rw [map_map_apply, map_map_apply]
      exact key _ _
    · show ((overlapUnit u _ _)⁻¹).val * _ = _
      rw [map_map_apply, map_map_apply, Units.inv_mul_eq_iff_eq_mul]
      exact (key _ _).symm
    · show (1 : (X.presheaf.obj (op _))ˣ).val * _ = _
      rw [Units.val_one, one_mul]
  · refine Prod.ext ?_ ?_ <;> exact (map_map_apply _ _ _).trans (map_self_apply _ _)

/-- In the chart trivialization over an open `P` inside a chart, the restriction of a section is
the restriction of its coordinate on that chart. -/
public theorem UnitTransitionCocycle.chartLinearEquiv_sectionsMap {ι : Type u}
    {U : ι → Opens X.carrier} (D : UnitTransitionCocycle X U) (i : ι) {W P : Opens X.carrier}
    (h : P ≤ W) (hP : P ≤ U i) (s : D.sectionsSubmodule W) :
    D.chartLinearEquiv i hP (D.sectionsMap h s) =
      (X.presheaf.map (homOfLE (le_inf h hP : P ≤ W ⊓ U i)).op).hom (s.val i) := by
  show (X.presheaf.map (homOfLE (le_inf le_rfl hP)).op).hom ((D.sectionsMap h s).val i) = _
  rw [UnitTransitionCocycle.sectionsMap_val, map_map_apply]

end Stacks.SheafOfModules

namespace Stacks.Algebraization.NonAlgebraizableExample

variable (k : Type u) [Field k] (a : ℕ → PlaneRing k) (φ : ℕ → ℕ)

/-- The two-chart family of the punctured spectrum of `A/tⁿA`. -/
local notation "chartFam " n => Stacks.SheafOfModules.twoChartFamily
  (levelChart k (xVar k) n) (levelChart k (yVar k) n)

/-- The coordinate in the chart ring `A_r/tⁿA_r` of a section of `𝓛ₙ`, read on the `i`-th member
of the two-chart family, which contains the chart `D(r̄)`. -/
public def levelCoord (n : ℕ) (r : AmbientRing k) (i : ULift.{u} Bool)
    (hle : chartOpen k r n ≤ levelOpen k n) (hri : levelChart k r n ≤ (chartFam n) i)
    {W : (levelOpen k n).toScheme.Opens} (hW : (chartFam n) i ≤ W) :
    (Stacks.SheafOfModules.twoChartCocycle (levelOverlapUnit k a φ n)).sectionsSubmodule W →+
      chartRing k r n where
  toFun σ := (levelChartRingEquiv k r n hle).symm
    (((levelOpen k n).toScheme.presheaf.map
      (homOfLE (le_inf (hri.trans hW) hri : levelChart k r n ≤ W ⊓ (chartFam n) i)).op).hom
        (σ.val i))
  map_zero' := by
    change (levelChartRingEquiv k r n hle).symm
      (((levelOpen k n).toScheme.presheaf.map _).hom 0) = 0
    rw [map_zero, map_zero]
  map_add' σ τ := by
    change (levelChartRingEquiv k r n hle).symm (((levelOpen k n).toScheme.presheaf.map _).hom
      (σ.val i + τ.val i)) = _
    rw [map_add, map_add]

/-- The chart coordinate, read back as a section over the chart, is the restriction of the
section's local coordinate. -/
public theorem levelChartRingEquiv_levelCoord (n : ℕ) (r : AmbientRing k) (i : ULift.{u} Bool)
    (hle : chartOpen k r n ≤ levelOpen k n) (hri : levelChart k r n ≤ (chartFam n) i)
    {W : (levelOpen k n).toScheme.Opens} (hW : (chartFam n) i ≤ W)
    (σ : (Stacks.SheafOfModules.twoChartCocycle (levelOverlapUnit k a φ n)).sectionsSubmodule W) :
    levelChartRingEquiv k r n hle (levelCoord k a φ n r i hle hri hW σ) =
      ((levelOpen k n).toScheme.presheaf.map
        (homOfLE (le_inf (hri.trans hW) hri : levelChart k r n ≤ W ⊓ (chartFam n) i)).op).hom
          (σ.val i) :=
  (levelChartRingEquiv k r n hle).apply_symm_apply _

/-- The identification of the chart ring with the sections over the chart, through the inclusion
of the punctured spectrum. -/
public theorem levelChartRingEquiv_eq_appLE (r : AmbientRing k) (n : ℕ)
    (hle : chartOpen k r n ≤ levelOpen k n) (v : chartRing k r n) :
    levelChartRingEquiv k r n hle v =
      ((levelOpen k n).ι.appLE (chartOpen k r n) (levelChart k r n) le_rfl).hom
        (chartOpenEquiv k r n v) := by
  rw [levelChartRingEquiv_apply, Scheme.Opens.ι_appLE]
  exact congrArg (fun f => ((levelScheme k n).presheaf.map f).hom (chartOpenEquiv k r n v))
    (Subsingleton.elim _ _)

/-- **The transition map `𝓛ₙ₊₁ ⟶ 𝓛ₙ` on chart coordinates is the reduction of chart rings.** -/
public theorem levelCoord_levelTransition (n : ℕ) (r : AmbientRing k) (i : ULift.{u} Bool)
    (hle : chartOpen k r (n + 1) ≤ levelOpen k (n + 1)) (hle' : chartOpen k r n ≤ levelOpen k n)
    (hri : levelChart k r (n + 1) ≤ (chartFam (n + 1)) i) (hri' : levelChart k r n ≤ (chartFam n) i)
    {W : (levelOpen k (n + 1)).toScheme.Opens} (hW : (chartFam (n + 1)) i ≤ W)
    (hW' : (chartFam n) i ≤ levelOpenMap k n ⁻¹ᵁ W)
    (σ : (Stacks.SheafOfModules.twoChartCocycle
      (levelOverlapUnit k a φ (n + 1))).sectionsSubmodule W) :
    levelCoord k a φ n r i hle' hri' hW' ((levelTransition k a φ n).val.app (op W) σ) =
      chartReduction k r n (levelCoord k a φ (n + 1) r i hle hri hW σ) := by
  have hP'eq := preimage_levelChart k r n hle
  have hV' : levelOpenMap k n ⁻¹ᵁ levelChart k r (n + 1) ≤ (chartFam n) i := hP'eq.le.trans hri'
  have hnat := PresheafOfModules.naturality_apply (levelTransition k a φ n).val
    (homOfLE (hri.trans hW)).op σ
  have key := chartLinearEquiv_levelTransition k a φ n i hri hV'
    ((Stacks.SheafOfModules.twoChartCocycle (levelOverlapUnit k a φ (n + 1))).sectionsMap
      (hri.trans hW) σ)
  change (Stacks.SheafOfModules.twoChartCocycle (levelOverlapUnit k a φ n)).chartLinearEquiv i hV'
    ((levelTransition k a φ n).val.app (op (levelChart k r (n + 1)))
      ((levelModule k a φ (n + 1)).val.map (homOfLE (hri.trans hW)).op σ)) = _ at key
  rw [hnat] at key
  change (Stacks.SheafOfModules.twoChartCocycle (levelOverlapUnit k a φ n)).chartLinearEquiv i hV'
    ((Stacks.SheafOfModules.twoChartCocycle (levelOverlapUnit k a φ n)).sectionsMap
      ((levelOpenMap k n).preimage_mono (hri.trans hW))
      ((levelTransition k a φ n).val.app (op W) σ)) = _ at key
  have e1 := Stacks.SheafOfModules.UnitTransitionCocycle.chartLinearEquiv_sectionsMap
    (Stacks.SheafOfModules.twoChartCocycle (levelOverlapUnit k a φ n)) i
    ((levelOpenMap k n).preimage_mono (hri.trans hW)) hV'
    ((levelTransition k a φ n).val.app (op W) σ)
  have key' := e1.symm.trans key
  rw [Stacks.SheafOfModules.UnitTransitionCocycle.chartLinearEquiv_sectionsMap,
    ← levelChartRingEquiv_levelCoord k a φ (n + 1) r i hle hri hW σ,
    levelChartRingEquiv_eq_appLE,
    app_levelOpenMap_appLE_ι_chartOpenEquiv k r n le_rfl hP'eq.le] at key'
  refine (levelChartRingEquiv k r n hle').symm_apply_eq.mpr ?_
  rw [levelChartRingEquiv_eq_appLE]
  have h2 := congrArg ((levelOpen k n).toScheme.presheaf.map (homOfLE hP'eq.ge).op).hom key'
  rw [Stacks.SheafOfModules.map_map_apply] at h2
  refine h2.trans ?_
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (Scheme.Hom.appLE_map (levelOpen k n).ι (U := chartOpen k r n) hP'eq.le
      (homOfLE hP'eq.ge).op)) _

/-- The pair of chart coordinates of a section of `𝓛ₙ` over the whole punctured spectrum of
`A/tⁿA`: its function on `D(x̄)` and its function on `D(ȳ)`. -/
public def levelSectionsCoords (n : ℕ) :
    (Stacks.SheafOfModules.twoChartCocycle (levelOverlapUnit k a φ n)).sectionsSubmodule ⊤ →+
      chartRing k (xVar k) n × chartRing k (yVar k) n :=
  (levelCoord k a φ n (xVar k) ⟨false⟩ le_sup_left le_rfl le_top).prod
    (levelCoord k a φ n (yVar k) ⟨true⟩ le_sup_right le_rfl le_top)

/-- The overlap unit is the transition element, read as a section over the overlap. -/
public theorem levelOverlapUnit_val (n : ℕ) :
    (levelOverlapUnit k a φ n).val = levelOverlapRingEquiv k n (transitionElement k a φ n) := by
  show levelOverlapRingEquiv k n ((isUnit_transitionElement k a φ n).unit.val) = _
  rw [IsUnit.unit_spec]

/-- Restriction from the chart of `x̄` to the overlap, on chart coordinates. -/
private theorem map_levelChartRingEquiv_x (n : ℕ) (v : chartRing k (xVar k) n) :
    ((levelOpen k n).toScheme.presheaf.map
        (homOfLE (inf_le_left : levelOverlap k n ≤ levelChart k (xVar k) n)).op).hom
        (levelChartRingEquiv k (xVar k) n le_sup_left v) =
      levelOverlapRingEquiv k n (xChartToOverlap k n v) :=
  map_levelChartRingEquiv_overlap k (xVar k) n (dvd_mul_right _ _) le_sup_left
    ((chartOpen_mul k n).le.trans inf_le_left) inf_le_left v

/-- Restriction from the chart of `ȳ` to the overlap, on chart coordinates. -/
private theorem map_levelChartRingEquiv_y (n : ℕ) (v : chartRing k (yVar k) n) :
    ((levelOpen k n).toScheme.presheaf.map
        (homOfLE (inf_le_right : levelOverlap k n ≤ levelChart k (yVar k) n)).op).hom
        (levelChartRingEquiv k (yVar k) n le_sup_right v) =
      levelOverlapRingEquiv k n (yChartToOverlap k n v) :=
  map_levelChartRingEquiv_overlap k (yVar k) n (dvd_mul_left _ _) le_sup_right
    ((chartOpen_mul k n).le.trans inf_le_right) inf_le_right v

/-- The two chart coordinates of a global section, in the chart rings. -/
private theorem twoChartCoords_levelSectionsCoords (n : ℕ)
    (σ : (Stacks.SheafOfModules.twoChartCocycle (levelOverlapUnit k a φ n)).sectionsSubmodule ⊤) :
    Stacks.SheafOfModules.twoChartCoords (levelOverlapUnit k a φ n) le_top le_top σ =
      (levelChartRingEquiv k (xVar k) n le_sup_left (levelSectionsCoords k a φ n σ).1,
        levelChartRingEquiv k (yVar k) n le_sup_right (levelSectionsCoords k a φ n σ).2) :=
  Prod.ext
    (levelChartRingEquiv_levelCoord k a φ n (xVar k) ⟨false⟩ le_sup_left le_rfl le_top σ).symm
    (levelChartRingEquiv_levelCoord k a φ n (yVar k) ⟨true⟩ le_sup_right le_rfl le_top σ).symm

/-- Chart functions are matched by the overlap unit exactly when they are matched by the
transition element. -/
private theorem levelChartRingEquiv_match_iff (n : ℕ)
    (v : chartRing k (xVar k) n × chartRing k (yVar k) n) :
    ((levelOpen k n).toScheme.presheaf.map
        (homOfLE (inf_le_right : levelOverlap k n ≤ levelChart k (yVar k) n)).op).hom
        (levelChartRingEquiv k (yVar k) n le_sup_right v.2) =
      (levelOverlapUnit k a φ n).val * ((levelOpen k n).toScheme.presheaf.map
        (homOfLE (inf_le_left : levelOverlap k n ≤ levelChart k (xVar k) n)).op).hom
        (levelChartRingEquiv k (xVar k) n le_sup_left v.1) ↔
      v ∈ gluedSections k n (transitionElement k a φ n) := by
  rw [map_levelChartRingEquiv_x, map_levelChartRingEquiv_y, levelOverlapUnit_val, ← map_mul,
    (levelOverlapRingEquiv k n).injective.eq_iff]
  exact Iff.rfl

/-- The chart coordinates of a global section of `𝓛ₙ` are matched by the transition element. -/
public theorem levelSectionsCoords_mem (n : ℕ)
    (σ : (Stacks.SheafOfModules.twoChartCocycle (levelOverlapUnit k a φ n)).sectionsSubmodule ⊤) :
    levelSectionsCoords k a φ n σ ∈ gluedSections k n (transitionElement k a φ n) := by
  have hm := Stacks.SheafOfModules.twoChartCoords_match (levelOverlapUnit k a φ n)
    (le_top : levelChart k (xVar k) n ≤ ⊤) (le_top : levelChart k (yVar k) n ≤ ⊤) σ
  rw [twoChartCoords_levelSectionsCoords] at hm
  exact (levelChartRingEquiv_match_iff k a φ n _).mp hm

/-- Every pair of chart functions matched by the transition element is the pair of chart
coordinates of a global section of `𝓛ₙ`. -/
public theorem exists_levelSectionsCoords_eq (n : ℕ)
    (v : chartRing k (xVar k) n × chartRing k (yVar k) n)
    (hv : v ∈ gluedSections k n (transitionElement k a φ n)) :
    ∃ σ, levelSectionsCoords k a φ n σ = v := by
  obtain ⟨σ, hσ⟩ := Stacks.SheafOfModules.exists_twoChartCoords_eq (levelOverlapUnit k a φ n)
    (le_top : levelChart k (xVar k) n ≤ ⊤) (le_top : levelChart k (yVar k) n ≤ ⊤)
    (levelChartRingEquiv k (xVar k) n le_sup_left v.1,
      levelChartRingEquiv k (yVar k) n le_sup_right v.2)
    ((levelChartRingEquiv_match_iff k a φ n v).mpr hv)
  rw [twoChartCoords_levelSectionsCoords] at hσ
  exact ⟨σ, Prod.ext ((levelChartRingEquiv k (xVar k) n le_sup_left).injective
    (congrArg Prod.fst hσ)) ((levelChartRingEquiv k (yVar k) n le_sup_right).injective
    (congrArg Prod.snd hσ))⟩

/-- A global section of `𝓛ₙ` is determined by its chart coordinates. -/
public theorem levelSectionsCoords_injective (n : ℕ) :
    Function.Injective (levelSectionsCoords k a φ n) := by
  intro σ τ h
  refine Stacks.SheafOfModules.twoChartCoords_injective (levelOverlapUnit k a φ n)
    (le_top : levelChart k (xVar k) n ≤ ⊤) (le_top : levelChart k (yVar k) n ≤ ⊤) ?_
  rw [twoChartCoords_levelSectionsCoords, twoChartCoords_levelSectionsCoords, h]

/-- The chart coordinate of the restriction of a section is the chart coordinate of the
section. -/
public theorem levelCoord_sectionsMap (n : ℕ) (r : AmbientRing k) (i : ULift.{u} Bool)
    (hle : chartOpen k r n ≤ levelOpen k n) (hri : levelChart k r n ≤ (chartFam n) i)
    {W W' : (levelOpen k n).toScheme.Opens} (h : W' ≤ W) (hW : (chartFam n) i ≤ W')
    (σ : (Stacks.SheafOfModules.twoChartCocycle (levelOverlapUnit k a φ n)).sectionsSubmodule W) :
    levelCoord k a φ n r i hle hri hW
        ((Stacks.SheafOfModules.twoChartCocycle (levelOverlapUnit k a φ n)).sectionsMap h σ) =
      levelCoord k a φ n r i hle hri (hW.trans h) σ := by
  show (levelChartRingEquiv k r n hle).symm (((levelOpen k n).toScheme.presheaf.map _).hom
      (((Stacks.SheafOfModules.twoChartCocycle (levelOverlapUnit k a φ n)).sectionsMap h σ).val i))
    = _
  rw [Stacks.SheafOfModules.UnitTransitionCocycle.sectionsMap_val,
    Stacks.SheafOfModules.map_map_apply]
  rfl

/-- **The transition map of the system on global sections, in chart coordinates.** The
transition map `𝓛ₙ₊₁ ⟶ 𝓛ₙ` on `U` carries a global section with chart coordinates `(f, h)` to
the global section with chart coordinates the reductions of `f` and `h` modulo `tⁿ`. -/
public theorem levelSectionsCoords_levelTransitionOnOpen (n : ℕ)
    (σ : (Stacks.SheafOfModules.twoChartCocycle
      (levelOverlapUnit k a φ (n + 1))).sectionsSubmodule ⊤) :
    levelSectionsCoords k a φ n ((levelTransitionOnOpen k a φ n).app ⊤ σ) =
      (chartReduction k (xVar k) n (levelSectionsCoords k a φ (n + 1) σ).1,
        chartReduction k (yVar k) n (levelSectionsCoords k a φ (n + 1) σ).2) := by
  show levelSectionsCoords k a φ n
      ((Stacks.SheafOfModules.twoChartCocycle (levelOverlapUnit k a φ n)).sectionsMap
        (le_top : (⊤ : (levelOpen k n).toScheme.Opens) ≤ levelOpenMap k n ⁻¹ᵁ ⊤)
        ((levelTransition k a φ n).val.app (op ⊤) σ)) = _
  refine Prod.ext ?_ ?_
  · exact (levelCoord_sectionsMap k a φ n (xVar k) ⟨false⟩ le_sup_left le_rfl le_top le_top
      _).trans (levelCoord_levelTransition k a φ n (xVar k) ⟨false⟩ le_sup_left le_sup_left le_rfl
        le_rfl le_top _ σ)
  · exact (levelCoord_sectionsMap k a φ n (yVar k) ⟨true⟩ le_sup_right le_rfl le_top le_top
      _).trans (levelCoord_levelTransition k a φ n (yVar k) ⟨true⟩ le_sup_right le_sup_right
        le_rfl le_rfl le_top _ σ)

/-- The chart coordinate of a multiple of a section is the product of the restricted function, read
in the chart ring, with the chart coordinate of the section. -/
public theorem levelCoord_smul (n : ℕ) (r : AmbientRing k) (i : ULift.{u} Bool)
    (hle : chartOpen k r n ≤ levelOpen k n) (hri : levelChart k r n ≤ (chartFam n) i)
    {W : (levelOpen k n).toScheme.Opens} (hW : (chartFam n) i ≤ W)
    (c : Γ((levelOpen k n).toScheme, W))
    (σ : (Stacks.SheafOfModules.twoChartCocycle (levelOverlapUnit k a φ n)).sectionsSubmodule W) :
    levelCoord k a φ n r i hle hri hW (c • σ) =
      (levelChartRingEquiv k r n hle).symm
          (((levelOpen k n).toScheme.presheaf.map (homOfLE (hri.trans hW)).op).hom c) *
        levelCoord k a φ n r i hle hri hW σ := by
  show (levelChartRingEquiv k r n hle).symm (((levelOpen k n).toScheme.presheaf.map _).hom
      (((levelOpen k n).toScheme.presheaf.map
        (homOfLE (inf_le_left : W ⊓ (chartFam n) i ≤ W)).op).hom c * σ.val i)) = _
  rw [map_mul, Stacks.SheafOfModules.map_map_apply, map_mul]
  rfl

/-- An element of `A`, restricted to `U`, pulled back to the punctured spectrum of `A/tⁿA` and
restricted to the chart `D(r̄)`, is its image in the chart ring `A_r/tⁿA_r`. -/
public theorem levelChartRingEquiv_symm_map_app_scalarMap (n : ℕ) (r : AmbientRing k)
    (hle : chartOpen k r n ≤ levelOpen k n) (z : AmbientRing k) :
    (levelChartRingEquiv k r n hle).symm
        (((levelOpen k n).toScheme.presheaf.map
          (homOfLE (le_top : levelChart k r n ≤ ⊤)).op).hom
          ((levelStructureMap k n).appTop.hom (scalarMap (situation k) z))) =
      algebraMap (AmbientRing k) (chartRing k r n) z := by
  refine (levelChartRingEquiv k r n hle).symm_apply_eq.mpr ?_
  have h := appLE_levelStructureMap_chartOpenEquiv k r n (V := ⊤) (P := levelChart k r n)
    le_top le_rfl z
  rw [← levelChartRingEquiv_eq_appLE k r n hle, levelToChart_mk] at h
  refine Eq.trans ?_ h
  rfl

/-- **Global sections of `𝓛ₙ₊₁` are glued pairs.** The group `H⁰(U, 𝓛ₙ₊₁)`, the `m`-th term of
the inverse system of global sections of `(𝓛ₙ)`, is the module of pairs of chart functions modulo
`tᵐ⁺¹` matched by the transition element, through the chart coordinates. The identification is
`A`-linear, `levelSectionsAddEquiv_smul`. -/
public def levelSectionsAddEquiv (m : ℕ) :
    (globalSectionsSystem (situation k) (levelCoherentAdicSystem k a φ)).obj (op m) ≃+
      gluedSections k (m + 1) (transitionElement k a φ (m + 1)) :=
  AddEquiv.ofBijective
    ({ toFun := fun σ => ⟨levelSectionsCoords k a φ (m + 1) σ,
        levelSectionsCoords_mem k a φ (m + 1) σ⟩
       map_zero' := Subtype.ext (map_zero (levelSectionsCoords k a φ (m + 1)))
       map_add' := fun σ τ => Subtype.ext (map_add (levelSectionsCoords k a φ (m + 1)) σ τ) } :
      (globalSectionsSystem (situation k) (levelCoherentAdicSystem k a φ)).obj (op m) →+
        gluedSections k (m + 1) (transitionElement k a φ (m + 1)))
    ⟨fun σ τ h => levelSectionsCoords_injective k a φ (m + 1) (congrArg Subtype.val h),
      fun v => by
        obtain ⟨σ, hσ⟩ := exists_levelSectionsCoords_eq k a φ (m + 1) v.1 v.2
        exact ⟨σ, Subtype.ext hσ⟩⟩

/-- The identification of `H⁰(U, 𝓛ₘ₊₁)` with glued pairs is the pair of chart coordinates. -/
public theorem coe_levelSectionsAddEquiv (m : ℕ)
    (σ : (globalSectionsSystem (situation k) (levelCoherentAdicSystem k a φ)).obj (op m)) :
    (levelSectionsAddEquiv k a φ m σ :
        chartRing k (xVar k) (m + 1) × chartRing k (yVar k) (m + 1)) =
      levelSectionsCoords k a φ (m + 1) σ := by
  rfl

/-- The chart coordinates of global sections of `𝓛ₙ` are `A`-linear, `A` acting on the sections
through `A → Γ(U, 𝒪_U)` and the structure map. -/
public theorem levelSectionsCoords_smul (n : ℕ) (z : AmbientRing k)
    (σ : (Stacks.SheafOfModules.twoChartCocycle (levelOverlapUnit k a φ n)).sectionsSubmodule ⊤) :
    levelSectionsCoords k a φ n
        ((levelStructureMap k n).appTop.hom (scalarMap (situation k) z) • σ) =
      z • levelSectionsCoords k a φ n σ := by
  refine Prod.ext ?_ ?_
  · exact (levelCoord_smul k a φ n (xVar k) ⟨false⟩ le_sup_left le_rfl le_top _ _).trans
      ((congrArg (· * levelCoord k a φ n (xVar k) ⟨false⟩ le_sup_left le_rfl le_top σ)
        (levelChartRingEquiv_symm_map_app_scalarMap k n (xVar k) le_sup_left z)).trans
          (Algebra.smul_def z _).symm)
  · exact (levelCoord_smul k a φ n (yVar k) ⟨true⟩ le_sup_right le_rfl le_top _ _).trans
      ((congrArg (· * levelCoord k a φ n (yVar k) ⟨true⟩ le_sup_right le_rfl le_top σ)
        (levelChartRingEquiv_symm_map_app_scalarMap k n (yVar k) le_sup_right z)).trans
          (Algebra.smul_def z _).symm)

/-- The identification of `H⁰(U, 𝓛ₙ₊₁)` with glued pairs is `A`-linear. -/
public theorem levelSectionsAddEquiv_smul (m : ℕ) (z : (situation k).A)
    (σ : (globalSectionsSystem (situation k) (levelCoherentAdicSystem k a φ)).obj (op m)) :
    levelSectionsAddEquiv k a φ m (z • σ) =
      (id z : AmbientRing k) • levelSectionsAddEquiv k a φ m σ :=
  Subtype.ext (levelSectionsCoords_smul k a φ (m + 1) z σ)

/-- The maps of the inverse system of global sections, from `H⁰(U, 𝓛ₘ₊₂)` to `H⁰(U, 𝓛ₘ₊₁)`, are
the reductions of chart functions modulo `tᵐ⁺¹`. -/
public theorem levelSectionsAddEquiv_map (m : ℕ)
    (σ : (globalSectionsSystem (situation k) (levelCoherentAdicSystem k a φ)).obj (op (m + 1))) :
    (levelSectionsAddEquiv k a φ m
        (((globalSectionsSystem (situation k) (levelCoherentAdicSystem k a φ)).map
          (homOfLE (Nat.le_succ m)).op).hom σ) :
        chartRing k (xVar k) (m + 1) × chartRing k (yVar k) (m + 1)) =
      (chartReduction k (xVar k) (m + 1) (levelSectionsAddEquiv k a φ (m + 1) σ).1.1,
        chartReduction k (yVar k) (m + 1) (levelSectionsAddEquiv k a φ (m + 1) σ).1.2) := by
  have h : (((globalSectionsSystem (situation k) (levelCoherentAdicSystem k a φ)).map
      (homOfLE (Nat.le_succ m)).op).hom σ) =
      ((levelTransitionOnOpen k a φ (m + 1)).app ⊤).hom σ := by
    show ((((levelSystem k a φ).map (homOfLE (Nat.le_succ m)).op).app ⊤).hom σ) = _
    rw [levelSystem_map_succ]
    rfl
  rw [coe_levelSectionsAddEquiv, h]
  exact levelSectionsCoords_levelTransitionOnOpen k a φ (m + 1) σ

/-- `sectionsLimit` as a module over the ring of the algebraization situation, which is `A` by
definition. -/
public instance moduleSituationSectionsLimit : Module (situation k).A (sectionsLimit k a φ) :=
  inferInstanceAs (Module (AmbientRing k) (sectionsLimit k a φ))

/-- The `n`-th term of a compatible system of glued pairs. -/
public def sectionsLimitProj (n : ℕ) :
    sectionsLimit k a φ →+ gluedSections k n (transitionElement k a φ n) where
  toFun s := ⟨s.1 n, s.2.1 n⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The projection from compatible systems of glued pairs to `H⁰(U, 𝓛ₘ₊₁)`. -/
public def sectionsLimitπ (m : ℕ) :
    sectionsLimit k a φ →ₗ[(situation k).A]
      (globalSectionsSystem (situation k) (levelCoherentAdicSystem k a φ)).obj (op m) where
  toAddHom := ((levelSectionsAddEquiv k a φ m).symm.toAddMonoidHom.comp
    (sectionsLimitProj k a φ (m + 1))).toAddHom
  map_smul' z s := (levelSectionsAddEquiv k a φ m).injective <|
    ((levelSectionsAddEquiv k a φ m).apply_symm_apply _).trans <|
      (Subtype.ext rfl : sectionsLimitProj k a φ (m + 1) (z • s) =
        (id z : AmbientRing k) • sectionsLimitProj k a φ (m + 1) s).trans <|
        (congrArg (fun v => (id z : AmbientRing k) • v)
          ((levelSectionsAddEquiv k a φ m).apply_symm_apply _).symm).trans
            (levelSectionsAddEquiv_smul k a φ m z _).symm

/-- The projection of a compatible system to `H⁰(U, 𝓛ₘ₊₁)` has chart coordinates the
`(m + 1)`-st term of the system. -/
public theorem levelSectionsAddEquiv_sectionsLimitπ (m : ℕ) (s : sectionsLimit k a φ) :
    (levelSectionsAddEquiv k a φ m (sectionsLimitπ k a φ m s) :
        chartRing k (xVar k) (m + 1) × chartRing k (yVar k) (m + 1)) = s.1 (m + 1) := by
  show ((levelSectionsAddEquiv k a φ m ((levelSectionsAddEquiv k a φ m).symm _) :
    chartRing k (xVar k) (m + 1) × chartRing k (yVar k) (m + 1))) = _
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- Compatible systems of glued pairs as a cone over the inverse system of global sections of
`(𝓛ₙ)`. -/
public def sectionsLimitCone :
    Cone (globalSectionsSystem (situation k) (levelCoherentAdicSystem k a φ)) where
  pt := ModuleCat.of (situation k).A (sectionsLimit k a φ)
  π := NatTrans.ofOpSequence
    (F := (Functor.const ℕᵒᵖ).obj (ModuleCat.of (situation k).A (sectionsLimit k a φ)))
    (G := globalSectionsSystem (situation k) (levelCoherentAdicSystem k a φ))
    (fun m => (ModuleCat.ofHom (Y := (globalSectionsSystem (situation k)
        (levelCoherentAdicSystem k a φ)).obj (op m)) (sectionsLimitπ k a φ m) :
      ModuleCat.of (situation k).A (sectionsLimit k a φ) ⟶
        (globalSectionsSystem (situation k) (levelCoherentAdicSystem k a φ)).obj (op m)))
    (fun m => by
    ext s
    apply (levelSectionsAddEquiv k a φ m).injective
    apply Subtype.ext
    change (levelSectionsAddEquiv k a φ m (sectionsLimitπ k a φ m s) :
        chartRing k (xVar k) (m + 1) × chartRing k (yVar k) (m + 1)) =
      levelSectionsAddEquiv k a φ m
        (((globalSectionsSystem (situation k) (levelCoherentAdicSystem k a φ)).map
          (homOfLE (Nat.le_succ m)).op).hom (sectionsLimitπ k a φ (m + 1) s))
    rw [levelSectionsAddEquiv_map, levelSectionsAddEquiv_sectionsLimitπ,
      levelSectionsAddEquiv_sectionsLimitπ]
    exact (s.2.2 (m + 1)).symm)

/-- The chart rings modulo `t⁰` are zero. -/
public instance subsingleton_chartRing_zero (r : AmbientRing k) :
    Subsingleton (chartRing k r 0) :=
  Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.span_singleton_one])

/-- The comparison from compatible systems of glued pairs to `lim H⁰(U, 𝓛ₙ)`. -/
public abbrev sectionsLimitLift :
    ModuleCat.of (situation k).A (sectionsLimit k a φ) ⟶
      limitGlobalSections (situation k) (levelCoherentAdicSystem k a φ) :=
  limit.lift _ (sectionsLimitCone k a φ)

/-- The comparison map followed by the projection of the limit is the projection of the cone. -/
public theorem π_sectionsLimitLift_apply (m : ℕ) (s : sectionsLimit k a φ) :
    (limit.π (globalSectionsSystem (situation k) (levelCoherentAdicSystem k a φ)) (op m)).hom
        ((sectionsLimitLift k a φ).hom s) = sectionsLimitπ k a φ m s :=
  congrArg (fun f => f.hom s) (limit.lift_π (sectionsLimitCone k a φ) (op m))

/-- The comparison from compatible systems of glued pairs to `lim H⁰(U, 𝓛ₙ)` is bijective: the
chart coordinates identify each term, and the term of order `0` is zero on both sides. -/
public theorem bijective_sectionsLimitLift :
    Function.Bijective (sectionsLimitLift k a φ).hom := by
  refine ⟨fun s t h => Subtype.ext (funext fun n => ?_), fun ℓ => ?_⟩
  · rcases n with _ | m
    · exact Subsingleton.elim _ _
    · have hm := congrArg (fun x => (levelSectionsAddEquiv k a φ m
        ((limit.π (globalSectionsSystem (situation k) (levelCoherentAdicSystem k a φ))
          (op m)).hom x) : chartRing k (xVar k) (m + 1) × chartRing k (yVar k) (m + 1))) h
      rw [π_sectionsLimitLift_apply, π_sectionsLimitLift_apply,
        levelSectionsAddEquiv_sectionsLimitπ, levelSectionsAddEquiv_sectionsLimitπ] at hm
      exact hm
  · let G := globalSectionsSystem (situation k) (levelCoherentAdicSystem k a φ)
    let f : (n : ℕ) → chartRing k (xVar k) n × chartRing k (yVar k) n := fun n =>
      match n with
      | 0 => 0
      | m + 1 => (levelSectionsAddEquiv k a φ m ((limit.π G (op m)).hom ℓ) :
          chartRing k (xVar k) (m + 1) × chartRing k (yVar k) (m + 1))
    have hf : f ∈ sectionsLimit k a φ := by
      refine ⟨fun n => ?_, fun n => ?_⟩
      · rcases n with _ | m
        · exact Submodule.zero_mem _
        · exact (levelSectionsAddEquiv k a φ m ((limit.π G (op m)).hom ℓ)).2
      · rcases n with _ | m
        · exact Subsingleton.elim _ _
        · have hw := congrArg (fun x => (levelSectionsAddEquiv k a φ m x :
            chartRing k (xVar k) (m + 1) × chartRing k (yVar k) (m + 1)))
            (congrArg (fun g => g.hom ℓ) (limit.w G (homOfLE (Nat.le_succ m)).op))
          change (levelSectionsAddEquiv k a φ m
            ((G.map (homOfLE (Nat.le_succ m)).op).hom ((limit.π G (op (m + 1))).hom ℓ)) :
              chartRing k (xVar k) (m + 1) × chartRing k (yVar k) (m + 1)) = _ at hw
          rw [levelSectionsAddEquiv_map] at hw
          exact hw
    refine ⟨⟨f, hf⟩, Concrete.limit_ext G _ _ fun ⟨m⟩ => ?_⟩
    refine (π_sectionsLimitLift_apply k a φ m ⟨f, hf⟩).trans
      ((levelSectionsAddEquiv k a φ m).injective ?_)
    exact Subtype.ext (levelSectionsAddEquiv_sectionsLimitπ k a φ m ⟨f, hf⟩)

/-- **Stacks Project, Tag 0EHE (`lim H⁰(U, 𝓛ₙ)` is the module of compatible glued pairs).** The
`A`-module `lim H⁰(U, 𝓛ₙ)` of the object `(𝓛ₙ)` of `Coh(U, I𝒪_U)` is the module `sectionsLimit` of
compatible systems of pairs of chart functions matched by the transition elements: a global
section of `𝓛ₙ` is read through its functions on the charts `D(x̄)` and `D(ȳ)`, and the maps of the
system become the reductions modulo `tⁿ`. -/
@[stacks 0EHE "lim H^0(U, L_n) is the module of compatible systems of glued chart pairs"]
public def sectionsLimitLinearEquiv :
    sectionsLimit k a φ ≃ₗ[(situation k).A]
      limitGlobalSections (situation k) (levelCoherentAdicSystem k a φ) :=
  LinearEquiv.ofBijective (sectionsLimitLift k a φ).hom (bijective_sectionsLimitLift k a φ)

/-- **Stacks Project, Tag 0EHE (`lim H⁰(U, 𝓛ₙ) ≠ 0` for the degenerate choice).** When the higher
coefficients `aₘ` vanish, the module `lim H⁰(U, 𝓛ₙ)` of the system `(𝓛ₙ)` is nonzero. -/
@[stacks 0EHE "lim H^0(U, L_n) is nonzero when a_m = 0 for m ≥ 2"]
public theorem nontrivial_limitGlobalSections (ha : ∀ m : ℕ, 2 ≤ m → a m = 0) :
    Nontrivial (limitGlobalSections (situation k) (levelCoherentAdicSystem k a φ)) := by
  have : Nontrivial (sectionsLimit k a φ) :=
    Submodule.nontrivial_iff_ne_bot.mpr (sectionsLimit_ne_bot k a φ ha)
  exact (sectionsLimitLinearEquiv k a φ).symm.toEquiv.nontrivial

/-- **Stacks Project, Tag 0EHE (`lim H⁰(U, 𝓛ₙ) = 0`).** When every higher coefficient `aₘ` is
`1` and the exponents are `φ(m) = 2ᵐ` or `φ(m) = m²`, the module `lim H⁰(U, 𝓛ₙ)` of the system
`(𝓛ₙ)` is zero. -/
@[stacks 0EHE "lim H^0(U, L_n) = 0 for a_m = 1 and φ(m) = 2^m or m^2"]
public theorem subsingleton_limitGlobalSections (ha : ∀ m : ℕ, 2 ≤ m → a m = 1)
    (hφ : (∀ m : ℕ, 2 ≤ m → φ m = 2 ^ m) ∨ (∀ m : ℕ, 2 ≤ m → φ m = m ^ 2)) :
    Subsingleton (limitGlobalSections (situation k) (levelCoherentAdicSystem k a φ)) := by
  have hbot := sectionsLimit_eq_bot k a φ ha hφ
  have hz : ∀ v ∈ sectionsLimit k a φ, v = 0 := fun v hv =>
    (Submodule.mem_bot _).mp (hbot.le hv)
  have : Subsingleton (sectionsLimit k a φ) := ⟨fun x y => Subtype.ext <|
    (hz _ x.2).trans (hz _ y.2).symm⟩
  exact (sectionsLimitLinearEquiv k a φ).symm.toEquiv.subsingleton

end Stacks.Algebraization.NonAlgebraizableExample
