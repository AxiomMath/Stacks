module

public import Mathlib.RingTheory.Smooth.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.RelativeSections
public import StacksFrontier.RingTheory.Smooth.SquareZeroLifts

/-!
# Infinitesimal lifts through an étale chart

In the setting of `StacksFrontier/AlgebraicGeometry/Spaces/FormallySmooth/RelativeSections.lean`
(an algebraic space `X` with a morphism `p : X ⟶ h_{Spec A'}`), let `φ` be a section of `X` over
the spectrum of an `A'`-algebra `C` lying over `Spec A'` which has **unique infinitesimal lifts**
(`AlgebraicGeometry.Space.ChartUniqueLifts`): for every surjection `π : E → F` of `A'`-algebras
with square-zero kernel and every map `ζ : C → F`, a section over `Spec E` restricting over
`Spec F` to the pull-back of `φ` along `ζ` is the pull-back of `φ` along exactly one lift
`q : C → E` of `ζ`. This is the formal étaleness of an étale chart of `X`, written in terms of
rings.

Through such a chart the lifts of a section over `Spec F` to `Spec E` become lifts of ring maps
(`AlgebraicGeometry.Space.relChartLift`). Two charts `ζ, ζ'` presenting the same section over
`Spec F` give two such descriptions, and this file compares them: the **transition**
`AlgebraicGeometry.Space.transition` between the lifts of `ζ` and those of `ζ'` is affine, and
its linear part `AlgebraicGeometry.Space.transitionDiff` is an `E`-linear isomorphism between the
modules of differences of lifts. This is what makes the difference of two lifts of a section of
an algebraic space a well-defined element of a module, independently of the chart — the
pseudo-torsor of Stacks 061C on one affine object, without the sheaf of differentials of `X`.

The proofs only use the uniqueness of chart lifts, applied to the algebras
`Stacks.SquareZeroLift.thick π n` of tuples of elements of `E` with a common image in `F`, and
the two ring maps `Stacks.SquareZeroLift.thickTranslate` and `Stacks.SquareZeroLift.thickScale`
between them.

## Main definitions

* `AlgebraicGeometry.Space.ChartUniqueLifts`.
* `AlgebraicGeometry.Space.relChartLift`: the lift of `ζ` presenting a given section.
* `AlgebraicGeometry.Space.transition`: the transition between the lifts of two charts.
* `AlgebraicGeometry.Space.transitionDiff`: its linear part.
* `AlgebraicGeometry.Space.diffMap`: the push-forward of differences along a map of algebras.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Stacks.SquareZeroLift

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A' : Type u} [CommRing A'] {s₀ : Spec (.of A') ⟶ S} {hA' : B.Contains (Spec (.of A'))}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : X ⟶ yoneda.obj (specOver B S hS s₀ A' hA')}
  {C : Type u} [CommRing C] [Algebra A' C] [InSite B C]

/-- **Unique infinitesimal lifts through a chart.** For every surjection `π : E → F` of
`A'`-algebras with square-zero kernel, every `ζ : C → F` and every section `z` over `Spec E`
restricting over `Spec F` to the pull-back of `φ` along `ζ`, there is exactly one lift `q` of
`ζ` along which `φ` pulls back to `z`. -/
def ChartUniqueLifts (φ : RelSec p C) : Prop :=
  ∀ ⦃E F : Type u⦄ [CommRing E] [CommRing F] [Algebra A' E] [Algebra A' F] [InSite B E]
    [InSite B F] (π : E →ₐ[A'] F), Function.Surjective π → IsSqZero π →
    ∀ (ζ : C →ₐ[A'] F) (z : RelSec p E), RelSec.map π z = RelSec.map ζ φ →
      ∃! q : C →ₐ[A'] E, π.comp q = ζ ∧ RelSec.map q φ = z

variable {φ : RelSec p C}

section Lift

variable (hφ : ChartUniqueLifts φ)
  {E F : Type u} [CommRing E] [CommRing F] [Algebra A' E] [Algebra A' F]
  [InSite B E] [InSite B F] {π : E →ₐ[A'] F}
  (hπ : Function.Surjective π) (hsq : IsSqZero π)

/-- **The lift of `ζ` presenting a section over `Spec E`.** -/
def relChartLift (ζ : C →ₐ[A'] F) (z : RelSec p E)
    (hz : RelSec.map π z = RelSec.map ζ φ) : C →ₐ[A'] E :=
  (hφ π hπ hsq ζ z hz).exists.choose

/-- The lift `relChartLift` is a lift of `ζ` along `π`. -/
theorem comp_chartLift (ζ : C →ₐ[A'] F) (z : RelSec p E)
    (hz : RelSec.map π z = RelSec.map ζ φ) :
    π.comp (relChartLift hφ hπ hsq ζ z hz) = ζ :=
  (hφ π hπ hsq ζ z hz).exists.choose_spec.1

/-- The section pulled back along `relChartLift` is the given section `z`. -/
theorem map_chartLift (ζ : C →ₐ[A'] F) (z : RelSec p E)
    (hz : RelSec.map π z = RelSec.map ζ φ) :
    RelSec.map (relChartLift hφ hπ hsq ζ z hz) φ = z :=
  (hφ π hπ hsq ζ z hz).exists.choose_spec.2

/-- A lift of `ζ` along which `φ` pulls back to `z` is `relChartLift`. -/
theorem eq_chartLift {ζ : C →ₐ[A'] F} {z : RelSec p E}
    (hz : RelSec.map π z = RelSec.map ζ φ) {q : C →ₐ[A'] E} (hq : π.comp q = ζ)
    (hqz : RelSec.map q φ = z) : q = relChartLift hφ hπ hsq ζ z hz :=
  (hφ π hπ hsq ζ z hz).unique ⟨hq, hqz⟩
    ⟨comp_chartLift hφ hπ hsq ζ z hz, map_chartLift hφ hπ hsq ζ z hz⟩

/-- The section presented by a lift `q` of `ζ` restricts over `Spec F` to the pull-back of `φ`
along `ζ`. -/
theorem map_comp_eq_map {ζ : C →ₐ[A'] F} {q : C →ₐ[A'] E} (hq : π.comp q = ζ) :
    RelSec.map π (RelSec.map q φ) = RelSec.map ζ φ := by
  rw [RelSec.map_map, hq]

/-- A section presented by a lift is presented by that lift. -/
theorem chartLift_map {ζ : C →ₐ[A'] F} {q : C →ₐ[A'] E} (hq : π.comp q = ζ) :
    relChartLift hφ hπ hsq ζ (RelSec.map q φ) (map_comp_eq_map hq) = q :=
  (eq_chartLift hφ hπ hsq _ hq rfl).symm

include hφ hπ hsq in
/-- Two lifts presenting the same section agree. -/
theorem eq_of_map_eq {ζ : C →ₐ[A'] F} {q q' : C →ₐ[A'] E} (hq : π.comp q = ζ)
    (hq' : π.comp q' = ζ) (h : RelSec.map q φ = RelSec.map q' φ) :
    q = q' :=
  (eq_chartLift hφ hπ hsq (map_comp_eq_map hq') hq h).trans
    (chartLift_map hφ hπ hsq hq')

/-- A lift of `ζ` along `π` is carried by a map of thickenings `(τ, τ')` to a lift of `τ' ∘ ζ`. -/
private theorem comp_comp_eq_of_comp_eq {E₂ F₂ : Type u} [CommRing E₂] [CommRing F₂]
    [Algebra A' E₂] [Algebra A' F₂] {π₂ : E₂ →ₐ[A'] F₂} {τ : E →ₐ[A'] E₂} {τ' : F →ₐ[A'] F₂}
    (hτ : π₂.comp τ = τ'.comp π) {ζ : C →ₐ[A'] F} {q : C →ₐ[A'] E} (hq : π.comp q = ζ) :
    π₂.comp (τ.comp q) = τ'.comp ζ := by
  rw [← AlgHom.comp_assoc, hτ, AlgHom.comp_assoc, hq]

/-- **Naturality of chart lifts.** Along a map of thickenings `(τ, τ̄)`, the lift presenting the
restriction of a section is the composite of `τ` with the lift presenting the section. -/
theorem chartLift_algHom_naturality
    {E₂ F₂ : Type u} [CommRing E₂] [CommRing F₂] [Algebra A' E₂] [Algebra A' F₂]
    [InSite B E₂] [InSite B F₂] {π₂ : E₂ →ₐ[A'] F₂}
    (hπ₂ : Function.Surjective π₂) (hsq₂ : IsSqZero π₂) (τ : E →ₐ[A'] E₂) (τ' : F →ₐ[A'] F₂)
    (hτ : π₂.comp τ = τ'.comp π) {ζ : C →ₐ[A'] F} {z : RelSec p E}
    (hz : RelSec.map π z = RelSec.map ζ φ)
    (hz₂ : RelSec.map π₂ (RelSec.map τ z) =
      RelSec.map (τ'.comp ζ) φ) :
    relChartLift hφ hπ₂ hsq₂ (τ'.comp ζ) (RelSec.map τ z) hz₂ =
      τ.comp (relChartLift hφ hπ hsq ζ z hz) := by
  refine (eq_chartLift hφ hπ₂ hsq₂ hz₂ ?_ ?_).symm
  · exact comp_comp_eq_of_comp_eq hτ (comp_chartLift hφ hπ hsq ζ z hz)
  · rw [← RelSec.map_map, map_chartLift]

end Lift

/-! ### The transition between two charts -/

section Transition

variable (hφ : ChartUniqueLifts φ)
  {E F : Type u} [CommRing E] [CommRing F] [Algebra A' E] [Algebra A' F]
  [InSite B E] [InSite B F] {π : E →ₐ[A'] F}
  (hπ : Function.Surjective π) (hsq : IsSqZero π)
  {ζ ζ' : C →ₐ[A'] F} (hζ : RelSec.map ζ φ = RelSec.map ζ' φ)

/-- **The transition from the lifts of `ζ` to those of `ζ'`**: the lift of `ζ'` presenting the
section presented by a lift of `ζ`. -/
def transition {q : C →ₐ[A'] E} (hq : π.comp q = ζ) : C →ₐ[A'] E :=
  relChartLift hφ hπ hsq ζ' (RelSec.map q φ) ((map_comp_eq_map hq).trans hζ)

/-- The transition of a lift of `ζ` is a lift of `ζ'`. -/
theorem comp_transition {q : C →ₐ[A'] E} (hq : π.comp q = ζ) :
    π.comp (transition hφ hπ hsq hζ hq) = ζ' :=
  comp_chartLift hφ hπ hsq _ _ _

/-- The transition of a lift `q` presents the same section as `q`. -/
theorem map_transition {q : C →ₐ[A'] E} (hq : π.comp q = ζ) :
    RelSec.map (transition hφ hπ hsq hζ hq) φ = RelSec.map q φ :=
  map_chartLift hφ hπ hsq _ _ _

/-- **Naturality of the transition** along a map of thickenings. -/
theorem transition_naturality
    {E₂ F₂ : Type u} [CommRing E₂] [CommRing F₂] [Algebra A' E₂] [Algebra A' F₂]
    [InSite B E₂] [InSite B F₂] {π₂ : E₂ →ₐ[A'] F₂}
    (hπ₂ : Function.Surjective π₂) (hsq₂ : IsSqZero π₂) (τ : E →ₐ[A'] E₂) (τ' : F →ₐ[A'] F₂)
    (hτ : π₂.comp τ = τ'.comp π)
    (hζ₂ : RelSec.map (τ'.comp ζ) φ = RelSec.map (τ'.comp ζ') φ)
    {q : C →ₐ[A'] E} (hq : π.comp q = ζ) (hq₂ : π₂.comp (τ.comp q) = τ'.comp ζ) :
    transition hφ hπ₂ hsq₂ hζ₂ hq₂ = τ.comp (transition hφ hπ hsq hζ hq) := by
  refine eq_of_map_eq hφ hπ₂ hsq₂ (comp_transition hφ hπ₂ hsq₂ hζ₂ hq₂) ?_ ?_
  · exact comp_comp_eq_of_comp_eq hτ (comp_transition hφ hπ hsq hζ hq)
  · rw [map_transition, ← RelSec.map_map, ← RelSec.map_map, map_transition]

end Transition

/-! ### Containment of the algebras of tuples in the site -/

/-- The algebra `thick π n` of `n`-tuples of elements of `E` with a common image in `F` lies in
the site whenever `E` does. -/
instance inSite_thick {E F : Type u} [CommRing E] [CommRing F] [Algebra A' E] [Algebra A' F]
    [hE : InSite B E] (π : E →ₐ[A'] F) (n : ℕ) : InSite B (thick π n) := by
  refine ⟨Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hE.out ?_⟩
  calc Cardinal.mk (thick π n) ≤ Cardinal.mk (Fin n → E) :=
        Cardinal.mk_le_of_injective Subtype.val_injective
    _ = Cardinal.mk E ^ n := by simp
    _ ≤ max Cardinal.aleph0 (Cardinal.mk E) := by
        rcases le_or_gt Cardinal.aleph0 (Cardinal.mk E) with h | h
        · exact (Cardinal.power_nat_le h).trans (le_max_right _ _)
        · exact (Cardinal.power_lt_aleph0 h (Cardinal.natCast_lt_aleph0 (n := n))).le.trans
            (le_max_left _ _)

/-! ### The transition is affine -/

section Affine

variable (hφ : ChartUniqueLifts φ)
  {E F : Type u} [CommRing E] [CommRing F] [Algebra A' E] [Algebra A' F]
  [InSite B E] [InSite B F] {π : E →ₐ[A'] F}
  (hπ : Function.Surjective π) (hsq : IsSqZero π)
  {ζ ζ' : C →ₐ[A'] F} (hζ : RelSec.map ζ φ = RelSec.map ζ' φ)

/-- **The transition is characterised by the section it presents.** -/
theorem eq_transition {q : C →ₐ[A'] E} (hq : π.comp q = ζ) {q' : C →ₐ[A'] E}
    (hq' : π.comp q' = ζ') (h : RelSec.map q' φ = RelSec.map q φ) :
    q' = transition hφ hπ hsq hζ hq :=
  eq_of_map_eq hφ hπ hsq hq' (comp_transition hφ hπ hsq hζ hq)
    (h.trans (map_transition hφ hπ hsq hζ hq).symm)

/-- The transition on tuples, read off at each coordinate. -/
theorem thickEval_comp_transition {n : ℕ} (q : Fin (n + 1) → (C →ₐ[A'] E))
    (hq : ∀ i, π.comp (q i) = ζ) (i : Fin (n + 1)) :
    (thickEval π i).comp (transition hφ
      (thickπ_surjective hπ n) (isSqZero_thickπ hsq n) hζ (thickπ_comp_thickLift q hq)) =
      transition hφ hπ hsq hζ (hq i) := by
  refine eq_transition hφ hπ hsq hζ (hq i) ?_ ?_
  · rw [← AlgHom.comp_assoc, comp_thickEval, comp_transition]
  · rw [← RelSec.map_map, map_transition, RelSec.map_map, thickEval_comp_thickLift]

/-- The transition on tuples is compatible with a map of tuple algebras sending one tuple of
lifts to another. -/
private theorem comp_transition_thickLift {n m : ℕ} (ρ : thick π (n + 1) →ₐ[A'] thick π (m + 1))
    (hρ : (thickπ π m).comp ρ = thickπ π n) {q : Fin (n + 1) → (C →ₐ[A'] E)}
    {q' : Fin (m + 1) → (C →ₐ[A'] E)} (hq : ∀ i, π.comp (q i) = ζ) (hq' : ∀ i, π.comp (q' i) = ζ)
    (h : ρ.comp (thickLift q hq) = thickLift q' hq') :
    ρ.comp (transition hφ (thickπ_surjective hπ n) (isSqZero_thickπ hsq n) hζ
      (thickπ_comp_thickLift q hq)) =
      transition hφ (thickπ_surjective hπ m) (isSqZero_thickπ hsq m) hζ
        (thickπ_comp_thickLift q' hq') := by
  refine eq_transition hφ (thickπ_surjective hπ m) (isSqZero_thickπ hsq m) hζ
    (thickπ_comp_thickLift q' hq') ?_ ?_
  · rw [← AlgHom.comp_assoc, hρ, comp_transition]
  · rw [← RelSec.map_map, map_transition, RelSec.map_map, h]

/-- **The transition is affine.** If two pairs of lifts of `ζ` have the same difference, so do
their transitions. -/
theorem transition_sub_eq {q₁ q₂ q₃ q₄ : C →ₐ[A'] E} (h₁ : π.comp q₁ = ζ) (h₂ : π.comp q₂ = ζ)
    (h₃ : π.comp q₃ = ζ) (h₄ : π.comp q₄ = ζ) (h : ∀ c, q₂ c - q₁ c = q₄ c - q₃ c) (c : C) :
    transition hφ hπ hsq hζ h₂ c - transition hφ hπ hsq hζ h₁ c =
      transition hφ hπ hsq hζ h₄ c - transition hφ hπ hsq hζ h₃ c := by
  let q : Fin 3 → (C →ₐ[A'] E) := ![q₁, q₂, q₃]
  have hq : ∀ i, π.comp (q i) = ζ := by
    intro i
    fin_cases i
    exacts [h₁, h₂, h₃]
  let q' : Fin 2 → (C →ₐ[A'] E) := ![q₃, q₄]
  have hq' : ∀ i, π.comp (q' i) = ζ := by
    intro i
    fin_cases i
    exacts [h₃, h₄]
  set Φ3 := transition hφ (thickπ_surjective hπ 2) (isSqZero_thickπ hsq 2) hζ
    (thickπ_comp_thickLift q hq) with hΦ3
  set Φ2 := transition hφ (thickπ_surjective hπ 1) (isSqZero_thickπ hsq 1) hζ
    (thickπ_comp_thickLift q' hq') with hΦ2
  -- the translate of the triple of lifts is the pair `(q₃, q₄)`
  have htr : (thickTranslate hsq).comp (thickLift q hq) = thickLift q' hq' := by
    refine thick_algHom_ext fun i => AlgHom.ext fun c => ?_
    fin_cases i
    · rfl
    · show q₃ c + q₂ c - q₁ c = q₄ c
      rw [add_sub_assoc, h c]
      ring
  -- so the translate of the transition of the triple is the transition of the pair
  have hkey : (thickTranslate hsq).comp Φ3 = Φ2 := by
    exact comp_transition_thickLift hφ hπ hsq hζ _ (thickπ_comp_thickTranslate hsq) hq hq' htr
  have e : (Φ3 c).1 2 + (Φ3 c).1 1 - (Φ3 c).1 0 = (Φ2 c).1 1 :=
    AlgHom.congr_fun (congrArg (fun g => (thickEval π 1).comp g) hkey) c
  have c₁ : (Φ3 c).1 0 = transition hφ hπ hsq hζ h₁ c :=
    AlgHom.congr_fun (thickEval_comp_transition hφ hπ hsq hζ q hq 0) c
  have c₂ : (Φ3 c).1 1 = transition hφ hπ hsq hζ h₂ c :=
    AlgHom.congr_fun (thickEval_comp_transition hφ hπ hsq hζ q hq 1) c
  have c₃ : (Φ3 c).1 2 = transition hφ hπ hsq hζ h₃ c :=
    AlgHom.congr_fun (thickEval_comp_transition hφ hπ hsq hζ q hq 2) c
  have c₄ : (Φ2 c).1 1 = transition hφ hπ hsq hζ h₄ c :=
    AlgHom.congr_fun (thickEval_comp_transition hφ hπ hsq hζ q' hq' 1) c
  rw [c₁, c₂, c₃, c₄] at e
  linear_combination e

/-- **The transition is compatible with scaling differences.** -/
theorem transition_smul_eq {q₁ q₂ q₃ : C →ₐ[A'] E} (h₁ : π.comp q₁ = ζ) (h₂ : π.comp q₂ = ζ)
    (h₃ : π.comp q₃ = ζ) (e : E) (h : ∀ c, q₃ c = q₁ c + e * (q₂ c - q₁ c)) (c : C) :
    transition hφ hπ hsq hζ h₃ c = transition hφ hπ hsq hζ h₁ c +
      e * (transition hφ hπ hsq hζ h₂ c - transition hφ hπ hsq hζ h₁ c) := by
  let q : Fin 2 → (C →ₐ[A'] E) := ![q₁, q₂]
  have hq : ∀ i, π.comp (q i) = ζ := by
    intro i
    fin_cases i
    exacts [h₁, h₂]
  let q' : Fin 2 → (C →ₐ[A'] E) := ![q₁, q₃]
  have hq' : ∀ i, π.comp (q' i) = ζ := by
    intro i
    fin_cases i
    exacts [h₁, h₃]
  set Φ := transition hφ (thickπ_surjective hπ 1) (isSqZero_thickπ hsq 1) hζ
    (thickπ_comp_thickLift q hq) with hΦ
  set Φ' := transition hφ (thickπ_surjective hπ 1) (isSqZero_thickπ hsq 1) hζ
    (thickπ_comp_thickLift q' hq') with hΦ'
  have hsc : (thickScale hsq e).comp (thickLift q hq) = thickLift q' hq' := by
    refine thick_algHom_ext fun i => AlgHom.ext fun c => ?_
    fin_cases i
    · rfl
    · exact (h c).symm
  have hkey : (thickScale hsq e).comp Φ = Φ' := by
    exact comp_transition_thickLift hφ hπ hsq hζ _ (thickπ_comp_thickScale hsq e) hq hq' hsc
  have k : (Φ c).1 0 + e * ((Φ c).1 1 - (Φ c).1 0) = (Φ' c).1 1 :=
    AlgHom.congr_fun (congrArg (fun g => (thickEval π 1).comp g) hkey) c
  have c₁ : (Φ c).1 0 = transition hφ hπ hsq hζ h₁ c :=
    AlgHom.congr_fun (thickEval_comp_transition hφ hπ hsq hζ q hq 0) c
  have c₂ : (Φ c).1 1 = transition hφ hπ hsq hζ h₂ c :=
    AlgHom.congr_fun (thickEval_comp_transition hφ hπ hsq hζ q hq 1) c
  have c₃ : (Φ' c).1 1 = transition hφ hπ hsq hζ h₃ c :=
    AlgHom.congr_fun (thickEval_comp_transition hφ hπ hsq hζ q' hq' 1) c
  rw [c₁, c₂, c₃] at k
  exact k.symm

end Affine

/-! ### The linear part of the transition -/

section Linear

variable (hφ : ChartUniqueLifts φ) [Algebra.FormallySmooth A' C]
  {E F : Type u} [CommRing E] [CommRing F] [Algebra A' E] [Algebra A' F]
  [InSite B E] [InSite B F] {π : E →ₐ[A'] F}
  (hπ : Function.Surjective π) (hsq : IsSqZero π)

/-- A lift of `ζ`, which exists because `C` is formally smooth. -/
def someLift (ζ : C →ₐ[A'] F) : C →ₐ[A'] E :=
  Algebra.FormallySmooth.liftOfSurjective ζ π hπ (isNilpotent_ker_of_isSqZero hsq)

/-- The lift `someLift` is a lift of `ζ` along `π`. -/
theorem comp_someLift (ζ : C →ₐ[A'] F) : π.comp (someLift hπ hsq ζ) = ζ :=
  Algebra.FormallySmooth.comp_liftOfSurjective ζ π hπ _

variable {ζ ζ' : C →ₐ[A'] F} (hζ : RelSec.map ζ φ = RelSec.map ζ' φ)

/-- **The linear part of the transition**: the difference of two lifts of `ζ` is carried to the
difference of their transitions. -/
def transitionDiff : diff π ζ →ₗ[E] diff π ζ' where
  toFun D :=
    ⟨(transition hφ hπ hsq hζ (comp_addDiff hsq (comp_someLift hπ hsq ζ) D.2)).toLinearMap -
      (transition hφ hπ hsq hζ (comp_someLift hπ hsq ζ)).toLinearMap,
    sub_mem_diff hsq (comp_transition _ _ _ _ _) (comp_transition _ _ _ _ _)⟩
  map_add' D₁ D₂ := by
    refine Subtype.ext (LinearMap.ext fun c => ?_)
    simp only [Submodule.coe_add, LinearMap.add_apply, LinearMap.sub_apply,
      AlgHom.toLinearMap_apply]
    have h := transition_sub_eq hφ hπ hsq hζ
      (comp_addDiff hsq (comp_someLift hπ hsq ζ) D₁.2)
      (comp_addDiff hsq (comp_someLift hπ hsq ζ) (D₁ + D₂).2)
      (comp_someLift hπ hsq ζ) (comp_addDiff hsq (comp_someLift hπ hsq ζ) D₂.2)
      (fun c => by simp only [addDiff_apply, Submodule.coe_add, LinearMap.add_apply]; ring) c
    linear_combination h
  map_smul' e D := by
    refine Subtype.ext (LinearMap.ext fun c => ?_)
    simp only [SetLike.val_smul, LinearMap.smul_apply, LinearMap.sub_apply,
      AlgHom.toLinearMap_apply, RingHom.id_apply, smul_eq_mul]
    have h := transition_smul_eq hφ hπ hsq hζ (comp_someLift hπ hsq ζ)
      (comp_addDiff hsq (comp_someLift hπ hsq ζ) D.2)
      (comp_addDiff hsq (comp_someLift hπ hsq ζ) (e • D).2) e
      (fun c => by simp only [addDiff_apply, SetLike.val_smul, LinearMap.smul_apply,
        smul_eq_mul]; ring) c
    rw [h]
    ring

/-- **The transition carries the difference of two lifts to the difference of their
transitions.** -/
theorem transitionDiff_sub {q₁ q₂ : C →ₐ[A'] E} (h₁ : π.comp q₁ = ζ) (h₂ : π.comp q₂ = ζ) :
    (transitionDiff hφ hπ hsq hζ ⟨_, sub_mem_diff hsq h₁ h₂⟩).1 =
      (transition hφ hπ hsq hζ h₂).toLinearMap - (transition hφ hπ hsq hζ h₁).toLinearMap := by
  refine LinearMap.ext fun c => ?_
  show transition hφ hπ hsq hζ _ c - transition hφ hπ hsq hζ _ c = _
  exact transition_sub_eq hφ hπ hsq hζ (comp_someLift hπ hsq ζ)
    (comp_addDiff hsq (comp_someLift hπ hsq ζ) (sub_mem_diff hsq h₁ h₂)) h₁ h₂
    (fun c => by simp) c

/-- The transition of a lift translated by a difference. -/
theorem transition_addDiff {q : C →ₐ[A'] E} (hq : π.comp q = ζ) {D : C →ₗ[A'] E}
    (hD : D ∈ diff π ζ) (c : C) :
    transition hφ hπ hsq hζ (comp_addDiff hsq hq hD) c =
      transition hφ hπ hsq hζ hq c + (transitionDiff hφ hπ hsq hζ ⟨D, hD⟩).1 c := by
  have h := congrArg (fun f : C →ₗ[A'] E => f c) (transitionDiff_sub hφ hπ hsq hζ hq
    (comp_addDiff hsq hq hD))
  have hD' : (⟨_, sub_mem_diff hsq hq (comp_addDiff hsq hq hD)⟩ : diff π ζ) = ⟨D, hD⟩ :=
    Subtype.ext (LinearMap.ext fun c => by simp)
  rw [hD'] at h
  simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply] at h
  rw [h]
  ring

/-- **The linear part of the transition on a difference of chart lifts.** -/
theorem transitionDiff_chartLift_sub {z z' : RelSec p E}
    (hz : RelSec.map π z = RelSec.map ζ φ) (hz' : RelSec.map π z' = RelSec.map ζ φ) :
    (transitionDiff hφ hπ hsq hζ ⟨_, sub_mem_diff hsq (comp_chartLift hφ hπ hsq ζ z hz)
      (comp_chartLift hφ hπ hsq ζ z' hz')⟩).1 =
      (relChartLift hφ hπ hsq ζ' z' (hz'.trans hζ)).toLinearMap -
        (relChartLift hφ hπ hsq ζ' z (hz.trans hζ)).toLinearMap := by
  rw [transitionDiff_sub hφ hπ hsq hζ (comp_chartLift hφ hπ hsq ζ z hz)
    (comp_chartLift hφ hπ hsq ζ z' hz')]
  have e : ∀ (w : RelSec p E) (hw : RelSec.map π w = RelSec.map ζ φ),
      transition hφ hπ hsq hζ (comp_chartLift hφ hπ hsq ζ w hw) =
        relChartLift hφ hπ hsq ζ' w (hw.trans hζ) := fun w hw =>
    (eq_transition hφ hπ hsq hζ _ (comp_chartLift _ _ _ _ _ _)
      ((map_chartLift _ _ _ _ _ _).trans (map_chartLift _ _ _ _ _ _).symm)).symm
  rw [e, e]

/-- The linear part of the transition between equal charts is the identity. -/
theorem transitionDiff_of_eq (h : ζ = ζ') (D : diff π ζ) :
    (transitionDiff hφ hπ hsq hζ D).1 = D.1 := by
  subst h
  have e : ∀ {q : C →ₐ[A'] E} (hq : π.comp q = ζ), transition hφ hπ hsq hζ hq = q := fun hq =>
    (eq_transition hφ hπ hsq hζ hq hq rfl).symm
  refine LinearMap.ext fun c => ?_
  show transition hφ hπ hsq hζ _ c - transition hφ hπ hsq hζ _ c = D.1 c
  rw [e, e, addDiff_apply]
  ring

end Linear

/-- The linear part of the transition depends only on the underlying map of a difference and the
source chart up to equality. -/
theorem transitionDiff_congr (hφ : ChartUniqueLifts φ) [Algebra.FormallySmooth A' C]
    {E F : Type u} [CommRing E] [CommRing F] [Algebra A' E] [Algebra A' F]
    [InSite B E] [InSite B F] {π : E →ₐ[A'] F} (hπ : Function.Surjective π) (hsq : IsSqZero π)
    {ζ₁ ζ₂ ζ' : C →ₐ[A'] F} (h : ζ₁ = ζ₂) (hζ₁ : RelSec.map ζ₁ φ = RelSec.map ζ' φ)
    (hζ₂ : RelSec.map ζ₂ φ = RelSec.map ζ' φ) (D₁ : diff π ζ₁) (D₂ : diff π ζ₂)
    (hD : D₁.1 = D₂.1) :
    (transitionDiff hφ hπ hsq hζ₁ D₁).1 = (transitionDiff hφ hπ hsq hζ₂ D₂).1 := by
  subst h
  rw [show D₁ = D₂ from Subtype.ext hD]

/-! ### Push-forward of differences -/

section DiffMap

variable [Algebra.FormallySmooth A' C]
  {E F E₂ F₂ : Type u} [CommRing E] [CommRing F] [CommRing E₂] [CommRing F₂] [Algebra A' E]
  [Algebra A' F] [Algebra A' E₂] [Algebra A' F₂] {π : E →ₐ[A'] F} {π₂ : E₂ →ₐ[A'] F₂}
  (hπ : Function.Surjective π) (hsq : IsSqZero π) (hsq₂ : IsSqZero π₂)
  (τ : E →ₐ[A'] E₂) (τ' : F →ₐ[A'] F₂) (hτ : π₂.comp τ = τ'.comp π) (ζ : C →ₐ[A'] F)

/-- **The push-forward of differences** along a map of thickenings. -/
def diffMap : diff π ζ →ₗ[A'] diff π₂ (τ'.comp ζ) where
  toFun D := ⟨τ.toLinearMap ∘ₗ D.1, by
    refine mem_diff_of_leibniz hsq₂ (fun c => ?_) (q := τ.comp (someLift hπ hsq ζ)) ?_ ?_
    · change π₂ (τ (D.1 c)) = 0
      rw [← AlgHom.comp_apply, hτ, AlgHom.comp_apply, D.2.1 c, map_zero]
    · rw [← AlgHom.comp_assoc, hτ, AlgHom.comp_assoc, comp_someLift]
    · intro a b
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
        AlgHom.comp_apply]
      rw [leibniz_of_mem_diff D.2 (comp_someLift hπ hsq ζ), map_add, map_mul, map_mul]⟩
  map_add' _ _ := Subtype.ext (LinearMap.comp_add _ _ _)
  map_smul' _ _ := Subtype.ext (LinearMap.ext fun _ => by simp)

/-- The push-forward of a difference `D` evaluates at `c` to `τ (D c)`. -/
@[simp]
theorem diffMap_apply (D : diff π ζ) (c : C) :
    (diffMap hπ hsq hsq₂ τ τ' hτ ζ D).1 c = τ (D.1 c) :=
  rfl

/-- The push-forward of differences is semilinear along `τ`. -/
theorem diffMap_smul (e : E) (D : diff π ζ) :
    diffMap hπ hsq hsq₂ τ τ' hτ ζ (e • D) = τ e • diffMap hπ hsq hsq₂ τ τ' hτ ζ D :=
  Subtype.ext (LinearMap.ext fun c => by simp)

end DiffMap

/-- **Naturality of the linear part of the transition.** -/
theorem transitionDiff_naturality (hφ : ChartUniqueLifts φ) [Algebra.FormallySmooth A' C]
    {E F E₂ F₂ : Type u} [CommRing E] [CommRing F] [CommRing E₂] [CommRing F₂] [Algebra A' E]
    [Algebra A' F] [Algebra A' E₂] [Algebra A' F₂] [InSite B E] [InSite B F] [InSite B E₂]
    [InSite B F₂] {π : E →ₐ[A'] F} {π₂ : E₂ →ₐ[A'] F₂} (hπ : Function.Surjective π)
    (hsq : IsSqZero π) (hπ₂ : Function.Surjective π₂) (hsq₂ : IsSqZero π₂)
    (τ : E →ₐ[A'] E₂) (τ' : F →ₐ[A'] F₂) (hτ : π₂.comp τ = τ'.comp π) {ζ ζ' : C →ₐ[A'] F}
    (hζ : RelSec.map ζ φ = RelSec.map ζ' φ)
    (hζ₂ : RelSec.map (τ'.comp ζ) φ = RelSec.map (τ'.comp ζ') φ) (D : diff π ζ) :
    transitionDiff hφ hπ₂ hsq₂ hζ₂ (diffMap hπ hsq hsq₂ τ τ' hτ ζ D) =
      diffMap hπ hsq hsq₂ τ τ' hτ ζ' (transitionDiff hφ hπ hsq hζ D) := by
  set q₀ := someLift hπ hsq ζ
  have h₀ := comp_someLift hπ hsq ζ
  have ha := comp_addDiff hsq h₀ D.2
  have h₀₂ := comp_comp_eq_of_comp_eq hτ h₀
  have ha₂ := comp_comp_eq_of_comp_eq hτ ha
  have hD : diffMap hπ hsq hsq₂ τ τ' hτ ζ D = ⟨_, sub_mem_diff hsq₂ h₀₂ ha₂⟩ := by
    refine Subtype.ext (LinearMap.ext fun c => ?_)
    show τ (D.1 c) = τ (q₀ c + D.1 c) - τ (q₀ c)
    rw [map_add]
    abel
  rw [hD]
  refine Subtype.ext ?_
  rw [transitionDiff_sub hφ hπ₂ hsq₂ hζ₂ h₀₂ ha₂,
    transition_naturality hφ hπ hsq hζ hπ₂ hsq₂ τ τ' hτ hζ₂ h₀ h₀₂,
    transition_naturality hφ hπ hsq hζ hπ₂ hsq₂ τ τ' hτ hζ₂ ha ha₂]
  refine LinearMap.ext fun c => ?_
  simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, diffMap_apply]
  show _ = τ (transition hφ hπ hsq hζ ha c - transition hφ hπ hsq hζ h₀ c)
  rw [map_sub]

end AlgebraicGeometry.Space

end
