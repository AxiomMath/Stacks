module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartLifts
public import StacksFrontier.AlgebraicGeometry.Spaces.PrimeResidueFieldSite
public import StacksFrontier.RingTheory.Smooth.LiftDifferenceBaseChange

/-!
# Glueing infinitesimal lifts along an étale cover

Let `A' → A` be a surjection with square-zero kernel `I`, let `ξ` be a section of `X` over `Spec A`
lying over `Spec A'`, and suppose that `ξ` is presented on an étale, faithfully flat cover
`Spec (A ⊗_{A'} B') → Spec A` by a smooth chart `φ` over `Spec C` with unique infinitesimal lifts:
`ξ` restricted to `Spec (A ⊗_{A'} B')` is the pull-back of `φ` along a map
`ζ : C → A ⊗_{A'} B'`. This file proves that `ξ` then extends to a section over `Spec A'`
(`AlgebraicGeometry.Space.RelSec.exists_lift_of_chart`).

This is step (II) of the proof of Stacks 04AM in the case of an affine test object. Over the cover
the section lifts, through the chart, because `C` is smooth. Two lifts of the pull-backs of `ξ`
to `Spec (B' ⊗_{A'} B')` differ by an element of the module of differences of lifts, and the
difference of the two pull-backs of one lift over `Spec B'` is a Čech `1`-cocycle; it is a
coboundary because that module commutes with the flat base change `- ⊗_{A'} B'`
(`Stacks.SquareZeroLift.diffBaseChange_bijective`) and `B'` is faithfully flat. Correcting the lift
by the coboundary makes the two pull-backs agree, and the lift descends along the étale cover.

The module of differences on `B' ⊗_{A'} B'` is computed in the chart of the first factor, and the
pull-back along the second factor is compared with it through the linear part of the chart
transition, `AlgebraicGeometry.Space.transitionDiff`.

## Main results

* `AlgebraicGeometry.Space.RelSec.exists_lift_of_chart`.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Stacks.SquareZeroLift Stacks.LocalThickening TensorProduct

universe u

namespace AlgebraicGeometry.Space

/-- A tensor product of two algebras in the site is in the site. -/
instance inSite_tensorProduct {B : BigFppfSite.{u}} {K R R' : Type u} [CommRing K] [CommRing R]
    [CommRing R'] [Algebra K R] [Algebra K R'] [hR : InSite B R] [hR' : InSite B R'] :
    InSite B (R ⊗[K] R') :=
  ⟨BigFppfSite.contains_spec_tensorProduct B hR.out hR'.out⟩

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A' : Type u} [CommRing A'] {s₀ : Spec (.of A') ⟶ S} {hA' : B.Contains (Spec (.of A'))}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : X ⟶ yoneda.obj (specOver B S hS s₀ A' hA')}
  {A : Type u} [CommRing A] [Algebra A' A] [InSite B A]
  {C : Type u} [CommRing C] [Algebra A' C] [InSite B C]

/-! ### Charts and lifts of a section over `Spec A` -/

section Lifts

variable (φ : RelSec p C) (ξ : RelSec p A)

/-- `ζ` presents `ξ` over `Spec (A ⊗_{A'} E)` through the chart `φ`. -/
def IsChartOf {E : Type u} [CommRing E] [Algebra A' E] [InSite B E]
    (ζ : C →ₐ[A'] A ⊗[A'] E) : Prop :=
  RelSec.map ζ φ = RelSec.map (Algebra.TensorProduct.includeLeft : A →ₐ[A'] A ⊗[A'] E) ξ

/-- `z` is a lift of `ξ` to `Spec E`: its restriction to `Spec (A ⊗_{A'} E)` is that of `ξ`. -/
def IsLiftOf {E : Type u} [CommRing E] [Algebra A' E] [InSite B E] (z : RelSec p E) : Prop :=
  RelSec.map (redπ A' A E) z =
    RelSec.map (Algebra.TensorProduct.includeLeft : A →ₐ[A'] A ⊗[A'] E) ξ

variable {φ ξ}
variable {E E₂ : Type u} [CommRing E] [CommRing E₂] [Algebra A' E] [Algebra A' E₂] [InSite B E]
  [InSite B E₂]

/-- `redMap A ρ` commutes with the inclusions of `A`. -/
theorem redMap_comp_includeLeft (ρ : E →ₐ[A'] E₂) :
    (redMap A ρ).comp (Algebra.TensorProduct.includeLeft : A →ₐ[A'] A ⊗[A'] E) =
      Algebra.TensorProduct.includeLeft :=
  AlgHom.ext fun a => by simp

/-- A presentation of `ξ` through `φ` pushes forward along `ρ : E → E₂`. -/
theorem IsChartOf.map {ζ : C →ₐ[A'] A ⊗[A'] E} (hζ : IsChartOf φ ξ ζ) (ρ : E →ₐ[A'] E₂) :
    IsChartOf φ ξ ((redMap A ρ).comp ζ) := by
  unfold IsChartOf at hζ ⊢
  rw [← RelSec.map_map, hζ, RelSec.map_map, redMap_comp_includeLeft]

/-- A lift of `ξ` to `Spec E` pulls back to a lift of `ξ` to `Spec E₂` along `ρ`. -/
theorem IsLiftOf.map {z : RelSec p E} (hz : IsLiftOf ξ z) (ρ : E →ₐ[A'] E₂) :
    IsLiftOf ξ (RelSec.map ρ z) := by
  unfold IsLiftOf at hz ⊢
  rw [RelSec.map_map, ← redMap_comp_redπ, ← RelSec.map_map, hz, RelSec.map_map,
    redMap_comp_includeLeft]

/-- The pull-back of `φ` along a lift `q` of a presentation `ζ` of `ξ` is a lift of `ξ`. -/
theorem isLiftOf_map {ζ : C →ₐ[A'] A ⊗[A'] E} (hζ : IsChartOf φ ξ ζ) {q : C →ₐ[A'] E}
    (hq : (redπ A' A E).comp q = ζ) : IsLiftOf ξ (RelSec.map q φ) := by
  unfold IsLiftOf
  rw [RelSec.map_map, hq]
  exact hζ

/-- Two presentations of `ξ` through `φ` pull `φ` back to the same section. -/
theorem IsChartOf.compat {ζ ζ' : C →ₐ[A'] A ⊗[A'] E} (hζ : IsChartOf φ ξ ζ)
    (hζ' : IsChartOf φ ξ ζ') : RelSec.map ζ φ = RelSec.map ζ' φ :=
  hζ.trans hζ'.symm

variable (hA : Function.Surjective (algebraMap A' A)) (hI : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)
  (hφ : ChartUniqueLifts φ)

/-- **The lift of a chart presenting a lift of `ξ`.** -/
def qL {ζ : C →ₐ[A'] A ⊗[A'] E} (hζ : IsChartOf φ ξ ζ) {z : RelSec p E} (hz : IsLiftOf ξ z) :
    C →ₐ[A'] E :=
  relChartLift hφ (redπ_surjective hA E) (isSqZero_redπ hA hI E) ζ z (hz.trans hζ.symm)

/-- `qL` lifts the presentation `ζ`. -/
theorem comp_qL {ζ : C →ₐ[A'] A ⊗[A'] E} (hζ : IsChartOf φ ξ ζ) {z : RelSec p E}
    (hz : IsLiftOf ξ z) : (redπ A' A E).comp (qL hA hI hφ hζ hz) = ζ :=
  comp_chartLift _ _ _ _ _ _

/-- The pull-back of `φ` along `qL` is the lift `z`. -/
theorem map_qL {ζ : C →ₐ[A'] A ⊗[A'] E} (hζ : IsChartOf φ ξ ζ) {z : RelSec p E}
    (hz : IsLiftOf ξ z) : RelSec.map (qL hA hI hφ hζ hz) φ = z :=
  map_chartLift _ _ _ _ _ _

/-- `qL` depends only on the presentation and the lift, not on the proofs. -/
theorem qL_congr {ζ₁ ζ₂ : C →ₐ[A'] A ⊗[A'] E} (hζ₁ : IsChartOf φ ξ ζ₁)
    (hζ₂ : IsChartOf φ ξ ζ₂) (hζ : ζ₁ = ζ₂) {z₁ z₂ : RelSec p E} (hz₁ : IsLiftOf ξ z₁)
    (hz₂ : IsLiftOf ξ z₂) (hz : z₁ = z₂) : qL hA hI hφ hζ₁ hz₁ = qL hA hI hφ hζ₂ hz₂ := by
  subst hζ hz
  rfl

/-- `qL` of the pull-back of `φ` along a lift `q` of `ζ` is `q`. -/
theorem qL_map {ζ : C →ₐ[A'] A ⊗[A'] E} (hζ : IsChartOf φ ξ ζ) {q : C →ₐ[A'] E}
    (hq : (redπ A' A E).comp q = ζ) : qL hA hI hφ hζ (isLiftOf_map hζ hq) = q :=
  chartLift_map _ _ _ hq

/-- `qL` is natural in `E`: it commutes with composition with `ρ : E → E₂`. -/
theorem qL_naturality {ζ : C →ₐ[A'] A ⊗[A'] E} (hζ : IsChartOf φ ξ ζ) {z : RelSec p E}
    (hz : IsLiftOf ξ z) (ρ : E →ₐ[A'] E₂) :
    qL hA hI hφ (hζ.map ρ) (hz.map ρ) = ρ.comp (qL hA hI hφ hζ hz) :=
  chartLift_algHom_naturality hφ _ _ _ _ ρ (redMap A ρ) (redMap_comp_redπ ρ).symm _ _

/-- The difference of `qL` at two lifts of `ξ` is a difference of lifts of `ζ`. -/
theorem qL_sub_mem {ζ : C →ₐ[A'] A ⊗[A'] E} (hζ : IsChartOf φ ξ ζ) {z z' : RelSec p E}
    (hz : IsLiftOf ξ z) (hz' : IsLiftOf ξ z') :
    (qL hA hI hφ hζ hz').toLinearMap - (qL hA hI hφ hζ hz).toLinearMap ∈ diff (redπ A' A E) ζ :=
  sub_mem_diff (isSqZero_redπ hA hI E) (comp_qL hA hI hφ hζ hz) (comp_qL hA hI hφ hζ hz')

/-- The linear part of the transition between two presentations maps the difference of `qL` at
two lifts in the first presentation to their difference in the second. -/
theorem transitionDiff_qL [Algebra.FormallySmooth A' C] {ζ ζ' : C →ₐ[A'] A ⊗[A'] E}
    (hζ : IsChartOf φ ξ ζ) (hζ' : IsChartOf φ ξ ζ') {z z' : RelSec p E} (hz : IsLiftOf ξ z)
    (hz' : IsLiftOf ξ z') :
    (transitionDiff hφ (redπ_surjective hA E) (isSqZero_redπ hA hI E) (hζ.compat hζ')
      ⟨_, qL_sub_mem hA hI hφ hζ hz hz'⟩).1 =
      (qL hA hI hφ hζ' hz').toLinearMap - (qL hA hI hφ hζ' hz).toLinearMap :=
  transitionDiff_chartLift_sub hφ _ _ _ _ _

/-- Two lifts of `ξ` with the same `qL` are equal. -/
theorem qL_injective {ζ : C →ₐ[A'] A ⊗[A'] E} (hζ : IsChartOf φ ξ ζ) {z z' : RelSec p E}
    (hz : IsLiftOf ξ z) (hz' : IsLiftOf ξ z') (h : qL hA hI hφ hζ hz = qL hA hI hφ hζ hz') :
    z = z' := by
  rw [← map_qL hA hI hφ hζ hz, ← map_qL hA hI hφ hζ hz', h]

end Lifts

/-! ### The Čech argument -/

section Cech

variable {B' : Type u} [CommRing B'] [Algebra A' B'] [InSite B B']

/-- The first inclusion `B' → B' ⊗_{A'} B'`. -/
abbrev inl₂ : B' →ₐ[A'] B' ⊗[A'] B' := incl A' B' B'

/-- The second inclusion `B' → B' ⊗_{A'} B'`. -/
abbrev inr₂ : B' →ₐ[A'] B' ⊗[A'] B' :=
  (Algebra.TensorProduct.includeRight : B' →ₐ[A'] B' ⊗[A'] B').restrictScalars A'

/-- The inclusion `B' ⊗ B' → (B' ⊗ B') ⊗ B'` of the first two factors. -/
abbrev inl₃ : B' ⊗[A'] B' →ₐ[A'] (B' ⊗[A'] B') ⊗[A'] B' := incl A' (B' ⊗[A'] B') B'

/-- The map `B' ⊗ B' → (B' ⊗ B') ⊗ B'` onto the first and third factors. -/
abbrev face₁₃ : B' ⊗[A'] B' →ₐ[A'] (B' ⊗[A'] B') ⊗[A'] B' :=
  Algebra.TensorProduct.map (inl₂ (B' := B')) (AlgHom.id A' B')

/-- The map `B' ⊗ B' → (B' ⊗ B') ⊗ B'` onto the second and third factors. -/
abbrev face₂₃ : B' ⊗[A'] B' →ₐ[A'] (B' ⊗[A'] B') ⊗[A'] B' :=
  Algebra.TensorProduct.map (inr₂ (B' := B')) (AlgHom.id A' B')

/-- `face₁₃ ∘ inl₂ = inl₃ ∘ inl₂`. -/
theorem face₁₃_comp_inl₂ :
    (face₁₃ (A' := A') (B' := B')).comp inl₂ = (inl₃ (A' := A') (B' := B')).comp inl₂ :=
  AlgHom.ext fun b => by simp

/-- `face₂₃ ∘ inl₂ = inl₃ ∘ inr₂`. -/
theorem face₂₃_comp_inl₂ :
    (face₂₃ (A' := A') (B' := B')).comp inl₂ = (inl₃ (A' := A') (B' := B')).comp inr₂ :=
  AlgHom.ext fun b => by simp

/-- `face₁₃ ∘ inr₂` is the inclusion of the third factor. -/
theorem face₁₃_comp_inr₂ : (face₁₃ (A' := A') (B' := B')).comp inr₂ =
    (Algebra.TensorProduct.includeRight : B' →ₐ[A'] (B' ⊗[A'] B') ⊗[A'] B') :=
  AlgHom.ext fun b => by simp [Algebra.TensorProduct.one_def]

/-- `face₂₃ ∘ inr₂` is the inclusion of the third factor. -/
theorem face₂₃_comp_inr₂ : (face₂₃ (A' := A') (B' := B')).comp inr₂ =
    (Algebra.TensorProduct.includeRight : B' →ₐ[A'] (B' ⊗[A'] B') ⊗[A'] B') :=
  AlgHom.ext fun b => by simp [Algebra.TensorProduct.one_def]

variable {φ : RelSec p C} {ξ : RelSec p A}
  (hA : Function.Surjective (algebraMap A' A)) (hI : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)
  (hφ : ChartUniqueLifts φ) [Algebra.FormallySmooth A' C]

omit [Algebra.FormallySmooth A' C] in
/-- `redMap` is compatible with composition, after composing with `ζ`. -/
theorem redMap_comp_comp {E₁ E₂ E₃ : Type u} [CommRing E₁] [CommRing E₂] [CommRing E₃]
    [Algebra A' E₁] [Algebra A' E₂] [Algebra A' E₃] (τ : E₁ →ₐ[A'] E₂) (ρ : E₂ →ₐ[A'] E₃)
    (ζ : C →ₐ[A'] A ⊗[A'] E₁) :
    (redMap A ρ).comp ((redMap A τ).comp ζ) = (redMap A (ρ.comp τ)).comp ζ := by
  rw [← AlgHom.comp_assoc, redMap_comp]

variable {ζ : C →ₐ[A'] A ⊗[A'] B'} (hζ : IsChartOf φ ξ ζ)

/-- **The coboundary operator** `D ↦ D₁ - D₂` on the differences over `B'`, computed in the chart
of the first factor of `B' ⊗_{A'} B'`. -/
def cechD₁ : diff (redπ A' A B') ζ →ₗ[A'] diff (redπ A' A (B' ⊗[A'] B'))
    ((redMap A (inl₂ (B' := B'))).comp ζ) :=
  diffMap (redπ_surjective hA B') (isSqZero_redπ hA hI B') (isSqZero_redπ hA hI _) inl₂
      (redMap A inl₂) (redMap_comp_redπ _).symm ζ -
    (transitionDiff hφ (redπ_surjective hA _) (isSqZero_redπ hA hI _)
      ((hζ.map inr₂).compat (hζ.map inl₂))).restrictScalars A' ∘ₗ
      diffMap (redπ_surjective hA B') (isSqZero_redπ hA hI B') (isSqZero_redπ hA hI _) inr₂
        (redMap A inr₂) (redMap_comp_redπ _).symm ζ

omit [Algebra.FormallySmooth A' C] in
/-- Pushing the first-factor presentation forward along `face₁₃` or along `inl₃` gives the same
presentation over `(B' ⊗ B') ⊗ B'`. -/
theorem chart_face₁₃ :
    (redMap A (face₁₃ (A' := A') (B' := B'))).comp ((redMap A inl₂).comp ζ) =
      (redMap A inl₃).comp ((redMap A inl₂).comp ζ) := by
  rw [redMap_comp_comp, redMap_comp_comp, face₁₃_comp_inl₂]

omit [Algebra.FormallySmooth A' C] in
/-- Pushing the first-factor presentation forward along `face₂₃` gives the push-forward along
`inl₃` of the second-factor presentation. -/
theorem chart_face₂₃ :
    (redMap A (face₂₃ (A' := A') (B' := B'))).comp ((redMap A inl₂).comp ζ) =
      (redMap A inl₃).comp ((redMap A inr₂).comp ζ) := by
  rw [redMap_comp_comp, redMap_comp_comp, face₂₃_comp_inl₂]

/-- **The coboundary operator** in the next degree, on the differences over `B' ⊗_{A'} B'`
computed in the chart of the first factor, with values in those over `(B' ⊗ B') ⊗ B'` computed in
the chart of the first factor: `c ↦ c₁₂ + c₂₃ - c₁₃`. -/
def cechD₂ : diff (redπ A' A (B' ⊗[A'] B')) ((redMap A (inl₂ (B' := B'))).comp ζ) →ₗ[A']
    diff (redπ A' A ((B' ⊗[A'] B') ⊗[A'] B'))
      ((redMap A (inl₃ (B' := B'))).comp ((redMap A inl₂).comp ζ)) :=
  diffMap (redπ_surjective hA _) (isSqZero_redπ hA hI _) (isSqZero_redπ hA hI _) inl₃
      (redMap A inl₃) (redMap_comp_redπ _).symm ((redMap A inl₂).comp ζ) +
    (transitionDiff hφ (redπ_surjective hA _) (isSqZero_redπ hA hI _)
      (((hζ.map inl₂).map face₂₃).compat ((hζ.map inl₂).map inl₃))).restrictScalars A' ∘ₗ
      diffMap (redπ_surjective hA _) (isSqZero_redπ hA hI _) (isSqZero_redπ hA hI _) face₂₃
        (redMap A face₂₃) (redMap_comp_redπ _).symm ((redMap A inl₂).comp ζ) -
    (transitionDiff hφ (redπ_surjective hA _) (isSqZero_redπ hA hI _)
      (((hζ.map inl₂).map face₁₃).compat ((hζ.map inl₂).map inl₃))).restrictScalars A' ∘ₗ
      diffMap (redπ_surjective hA _) (isSqZero_redπ hA hI _) (isSqZero_redπ hA hI _) face₁₃
        (redMap A face₁₃) (redMap_comp_redπ _).symm ((redMap A inl₂).comp ζ)

/-! #### The cocycle of a lift -/

/-- **The difference of the two pull-backs of a lift over `B'`**, in the chart of the first
factor of `B' ⊗_{A'} B'`. -/
def cocycle {z : RelSec p B'} (hz : IsLiftOf ξ z) :
    diff (redπ A' A (B' ⊗[A'] B')) ((redMap A (inl₂ (B' := B'))).comp ζ) :=
  ⟨_, qL_sub_mem hA hI hφ (hζ.map inl₂) (hz.map inl₂) (hz.map inr₂)⟩

omit [Algebra.FormallySmooth A' C] in
/-- The underlying map of `cocycle` is the difference of the chart lifts of the two pull-backs. -/
theorem cocycle_val {z : RelSec p B'} (hz : IsLiftOf ξ z) :
    (cocycle hA hI hφ hζ hz).1 = (qL hA hI hφ (hζ.map inl₂) (hz.map inr₂)).toLinearMap -
      (qL hA hI hφ (hζ.map inl₂) (hz.map inl₂)).toLinearMap :=
  rfl

omit [Algebra.FormallySmooth A' C] in
/-- **A lift over `B'` whose cocycle vanishes has equal pull-backs to `B' ⊗_{A'} B'`.** -/
theorem map_inl₂_eq_map_inr₂ {z : RelSec p B'} (hz : IsLiftOf ξ z)
    (h : cocycle hA hI hφ hζ hz = 0) :
    RelSec.map inl₂ z = (RelSec.map inr₂ z : RelSec p (B' ⊗[A'] B')) := by
  refine qL_injective hA hI hφ (hζ.map inl₂) (hz.map inl₂) (hz.map inr₂) ?_
  have h' := congrArg Subtype.val h
  rw [cocycle_val] at h'
  exact (AlgHom.toLinearMap_injective (sub_eq_zero.1 h')).symm

omit [Algebra.FormallySmooth A' C] in
/-- `qL` of a pull-back along `ρ` is `ρ` composed with `qL`, for presentations and lifts given up
to equality. -/
theorem qL_map_eq {E E₂ : Type u} [CommRing E] [CommRing E₂] [Algebra A' E] [Algebra A' E₂]
    [InSite B E] [InSite B E₂] {χ : C →ₐ[A'] A ⊗[A'] E} (hχ : IsChartOf φ ξ χ)
    {w : RelSec p E} (hw : IsLiftOf ξ w) {ρ ρ' : E →ₐ[A'] E₂} {σ : E₂ →ₐ[A'] E₂}
    {χ' : C →ₐ[A'] A ⊗[A'] E₂} (hχ' : IsChartOf φ ξ χ') (hχχ : (redMap A ρ).comp χ = χ')
    (hρ : ρ = ρ') {w' : RelSec p E₂} (hw' : IsLiftOf ξ w') (hww : RelSec.map ρ' w = w') :
    qL hA hI hφ hχ' hw' = ρ.comp (qL hA hI hφ hχ hw) := by
  subst hρ hχχ hww
  exact qL_naturality hA hI hφ hχ hw ρ

/-- Pushing the cocycle forward along `f : B' ⊗ B' → T` gives the difference of the chart lifts of
the pull-backs of `z` along the two restrictions `j`, `j'` of `f`. -/
private theorem diffMap_cocycle {T : Type u} [CommRing T] [Algebra A' T] [InSite B T]
    {z : RelSec p B'} (hz : IsLiftOf ξ z) (f : B' ⊗[A'] B' →ₐ[A'] T) {j j' : B' →ₐ[A'] T}
    (hj : f.comp inl₂ = j) (hj' : f.comp inr₂ = j') :
    diffMap (redπ_surjective hA _) (isSqZero_redπ hA hI _) (isSqZero_redπ hA hI _) f
      (redMap A f) (redMap_comp_redπ _).symm ((redMap A inl₂).comp ζ) (cocycle hA hI hφ hζ hz) =
      ⟨_, qL_sub_mem hA hI hφ ((hζ.map inl₂).map f) (hz.map j) (hz.map j')⟩ := by
  refine Subtype.ext (LinearMap.ext fun c => ?_)
  simp only [diffMap_apply, cocycle_val, LinearMap.sub_apply, AlgHom.toLinearMap_apply, map_sub]
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply,
    ← qL_naturality hA hI hφ (hζ.map inl₂) (hz.map inr₂) f,
    ← qL_naturality hA hI hφ (hζ.map inl₂) (hz.map inl₂) f,
    qL_congr hA hI hφ _ ((hζ.map inl₂).map f) rfl _ (hz.map j')
      ((RelSec.map_map _ _ _).trans (RelSec.map_congr hj' _)),
    qL_congr hA hI hφ _ ((hζ.map inl₂).map f) rfl _ (hz.map j)
      ((RelSec.map_map _ _ _).trans (RelSec.map_congr hj _))]

/-- The linear part of the transition to the chart `inl₃` maps the pushed-forward cocycle to the
difference of the chart lifts of the pull-backs of `z` along `j`, `j'`. -/
private theorem transitionDiff_diffMap_cocycle {z : RelSec p B'} (hz : IsLiftOf ξ z)
    (f : B' ⊗[A'] B' →ₐ[A'] (B' ⊗[A'] B') ⊗[A'] B') {j j' : B' →ₐ[A'] (B' ⊗[A'] B') ⊗[A'] B'}
    (hj : f.comp inl₂ = j) (hj' : f.comp inr₂ = j') :
    (transitionDiff hφ (redπ_surjective hA _) (isSqZero_redπ hA hI _)
      (((hζ.map inl₂).map f).compat ((hζ.map inl₂).map inl₃))
      (diffMap (redπ_surjective hA _) (isSqZero_redπ hA hI _) (isSqZero_redπ hA hI _) f
        (redMap A f) (redMap_comp_redπ _).symm ((redMap A inl₂).comp ζ)
        (cocycle hA hI hφ hζ hz))).1 =
      (qL hA hI hφ ((hζ.map inl₂).map inl₃) (hz.map j')).toLinearMap -
        (qL hA hI hφ ((hζ.map inl₂).map inl₃) (hz.map j)).toLinearMap := by
  rw [diffMap_cocycle hA hI hφ hζ hz f hj hj', transitionDiff_qL]

/-- **The cocycle condition.** -/
theorem cechD₂_cocycle {z : RelSec p B'} (hz : IsLiftOf ξ z) :
    cechD₂ hA hI hφ hζ (cocycle hA hI hφ hζ hz) = 0 := by
  have hχ := (hζ.map inl₂).map (inl₃ (B' := B'))
  set j₁ : B' →ₐ[A'] (B' ⊗[A'] B') ⊗[A'] B' := inl₃.comp inl₂
  set j₂ : B' →ₐ[A'] (B' ⊗[A'] B') ⊗[A'] B' := inl₃.comp inr₂
  set j₃ : B' →ₐ[A'] (B' ⊗[A'] B') ⊗[A'] B' :=
    (Algebra.TensorProduct.includeRight : B' →ₐ[A'] (B' ⊗[A'] B') ⊗[A'] B')
  set Q : (B' →ₐ[A'] (B' ⊗[A'] B') ⊗[A'] B') → (C →ₐ[A'] (B' ⊗[A'] B') ⊗[A'] B') :=
    fun ρ => qL hA hI hφ hχ (hz.map ρ)
  have t₁ := congrArg Subtype.val (diffMap_cocycle hA hI hφ hζ hz (inl₃ (B' := B')) rfl rfl)
  have t₂ := transitionDiff_diffMap_cocycle hA hI hφ hζ hz face₂₃ face₂₃_comp_inl₂
    face₂₃_comp_inr₂
  have t₃ := transitionDiff_diffMap_cocycle hA hI hφ hζ hz face₁₃ face₁₃_comp_inl₂
    face₁₃_comp_inr₂
  refine Subtype.ext (LinearMap.ext fun c => ?_)
  have e₁ := LinearMap.congr_fun t₁ c
  have e₂ := LinearMap.congr_fun t₂ c
  have e₃ := LinearMap.congr_fun t₃ c
  simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply] at e₁ e₂ e₃
  simp only [cechD₂, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, Submodule.coe_sub, Submodule.coe_add, LinearMap.sub_apply,
    LinearMap.add_apply, ZeroMemClass.coe_zero, LinearMap.zero_apply]
  rw [e₁, e₂, e₃]
  ring

/-! #### Correcting a lift -/

omit [Algebra.FormallySmooth A' C] in
/-- The chart lift of a section presented in another chart is the transition. -/
theorem qL_eq_transition {E : Type u} [CommRing E] [Algebra A' E] [InSite B E]
    {χ χ' : C →ₐ[A'] A ⊗[A'] E} (hχ : IsChartOf φ ξ χ) (hχ' : IsChartOf φ ξ χ')
    {w : RelSec p E} (hw : IsLiftOf ξ w) :
    qL hA hI hφ hχ' hw = transition hφ (redπ_surjective hA E) (isSqZero_redπ hA hI E)
      (hχ.compat hχ') (comp_qL hA hI hφ hχ hw) :=
  eq_transition hφ _ _ _ _ (comp_qL hA hI hφ hχ' hw)
    ((map_qL hA hI hφ hχ' hw).trans (map_qL hA hI hφ hχ hw).symm)

variable {z : RelSec p B'} (hz : IsLiftOf ξ z)

/-- A lift over `B'` corrected by a difference `e`. -/
def correct (e : diff (redπ A' A B') ζ) : RelSec p B' :=
  RelSec.map (addDiff (isSqZero_redπ hA hI B') (comp_qL hA hI hφ hζ hz) e.2) φ

omit [Algebra.FormallySmooth A' C] in
/-- A corrected lift is a lift of `ξ`. -/
theorem isLiftOf_correct (e : diff (redπ A' A B') ζ) :
    IsLiftOf ξ (correct hA hI hφ hζ hz e) :=
  isLiftOf_map hζ (comp_addDiff _ _ _)

/-- **Correcting a lift by `e` changes its cocycle by the coboundary of `e`.** -/
theorem cocycle_correct (e : diff (redπ A' A B') ζ) :
    cocycle hA hI hφ hζ (isLiftOf_correct hA hI hφ hζ hz e) =
      cocycle hA hI hφ hζ hz - cechD₁ hA hI hφ hζ e := by
  set q₀ := qL hA hI hφ hζ hz with hq₀
  set q₁ := addDiff (isSqZero_redπ hA hI B') (comp_qL hA hI hφ hζ hz) e.2 with hq₁
  have hz' := isLiftOf_correct hA hI hφ hζ hz e
  have hqe : qL hA hI hφ hζ hz' = q₁ := qL_map hA hI hφ hζ (comp_addDiff _ _ _)
  have h₁ : qL hA hI hφ (hζ.map inl₂) (hz'.map inl₂) = inl₂.comp q₁ := by
    rw [qL_naturality hA hI hφ hζ hz' inl₂, hqe]
  have h₂ : qL hA hI hφ (hζ.map inr₂) (hz'.map inr₂) = inr₂.comp q₁ := by
    rw [qL_naturality hA hI hφ hζ hz' inr₂, hqe]
  have h₂z : qL hA hI hφ (hζ.map inr₂) (hz.map inr₂) = inr₂.comp q₀ := qL_naturality _ _ _ _ _ _
  have h₁z : qL hA hI hφ (hζ.map inl₂) (hz.map inl₂) = inl₂.comp q₀ := qL_naturality _ _ _ _ _ _
  have hc₀ : (redπ A' A (B' ⊗[A'] B')).comp (inr₂.comp q₀) = (redMap A inr₂).comp ζ := by
    rw [← AlgHom.comp_assoc, ← redMap_comp_redπ, AlgHom.comp_assoc, hq₀, comp_qL]
  have hinr : inr₂.comp q₁ = addDiff (isSqZero_redπ hA hI _) hc₀
      (diffMap (redπ_surjective hA B') (isSqZero_redπ hA hI B') (isSqZero_redπ hA hI _) inr₂
        (redMap A inr₂) (redMap_comp_redπ _).symm ζ e).2 := by
    ext c
    simp [q₁, hq₀, tmul_add]
  have k₂ := qL_eq_transition hA hI hφ (hζ.map inr₂) (hζ.map inl₂) (hz'.map inr₂)
  have k₂z := qL_eq_transition hA hI hφ (hζ.map inr₂) (hζ.map inl₂) (hz.map inr₂)
  refine Subtype.ext (LinearMap.ext fun c => ?_)
  have key : qL hA hI hφ (hζ.map inl₂) (hz'.map inr₂) c =
      qL hA hI hφ (hζ.map inl₂) (hz.map inr₂) c +
        (transitionDiff hφ (redπ_surjective hA _) (isSqZero_redπ hA hI _)
          ((hζ.map inr₂).compat (hζ.map inl₂))
          (diffMap (redπ_surjective hA B') (isSqZero_redπ hA hI B') (isSqZero_redπ hA hI _) inr₂
            (redMap A inr₂) (redMap_comp_redπ _).symm ζ e)).1 c := by
    rw [k₂, k₂z]
    have hc := transition_addDiff hφ (redπ_surjective hA _) (isSqZero_redπ hA hI _)
      ((hζ.map inr₂).compat (hζ.map inl₂))
      hc₀ (diffMap (redπ_surjective hA B') (isSqZero_redπ hA hI B') (isSqZero_redπ hA hI _) inr₂
        (redMap A inr₂) (redMap_comp_redπ _).symm ζ e).2 c
    have ht₁ : transition hφ (redπ_surjective hA _) (isSqZero_redπ hA hI _)
        ((hζ.map inr₂).compat (hζ.map inl₂)) (comp_qL hA hI hφ (hζ.map inr₂) (hz'.map inr₂)) =
        transition hφ (redπ_surjective hA _) (isSqZero_redπ hA hI _)
        ((hζ.map inr₂).compat (hζ.map inl₂)) (comp_addDiff (isSqZero_redπ hA hI _) hc₀
          (diffMap (redπ_surjective hA B') (isSqZero_redπ hA hI B') (isSqZero_redπ hA hI _)
            inr₂ (redMap A inr₂) (redMap_comp_redπ _).symm ζ e).2) := by
      congr 1
      rw [h₂, hinr]
    have ht₂ : transition hφ (redπ_surjective hA _) (isSqZero_redπ hA hI _)
        ((hζ.map inr₂).compat (hζ.map inl₂)) (comp_qL hA hI hφ (hζ.map inr₂) (hz.map inr₂)) =
        transition hφ (redπ_surjective hA _) (isSqZero_redπ hA hI _)
        ((hζ.map inr₂).compat (hζ.map inl₂)) hc₀ := by
      congr 1
    rw [ht₁, hc, ht₂]
  simp only [cocycle_val, LinearMap.sub_apply, AlgHom.toLinearMap_apply, Submodule.coe_sub,
    cechD₁, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    diffMap_apply]
  rw [key, h₁, h₁z]
  simp only [AlgHom.comp_apply, q₁, addDiff_apply, map_add]
  ring

/-! #### The base-changed coboundary and faithful flatness -/

/-- **The coboundary operator of the base-changed cover** `B' ⊗ B' → B'`, on the differences
over `B' ⊗_{A'} B'`: `c ↦ c₁₃ - c₂₃`. -/
def cechD₁B : diff (redπ A' A (B' ⊗[A'] B')) ((redMap A (inl₂ (B' := B'))).comp ζ) →ₗ[A']
    diff (redπ A' A ((B' ⊗[A'] B') ⊗[A'] B'))
      ((redMap A (inl₃ (B' := B'))).comp ((redMap A inl₂).comp ζ)) :=
  (transitionDiff hφ (redπ_surjective hA _) (isSqZero_redπ hA hI _)
      (((hζ.map inl₂).map face₁₃).compat ((hζ.map inl₂).map inl₃))).restrictScalars A' ∘ₗ
      diffMap (redπ_surjective hA _) (isSqZero_redπ hA hI _) (isSqZero_redπ hA hI _) face₁₃
        (redMap A face₁₃) (redMap_comp_redπ _).symm ((redMap A inl₂).comp ζ) -
    (transitionDiff hφ (redπ_surjective hA _) (isSqZero_redπ hA hI _)
      (((hζ.map inl₂).map face₂₃).compat ((hζ.map inl₂).map inl₃))).restrictScalars A' ∘ₗ
      diffMap (redπ_surjective hA _) (isSqZero_redπ hA hI _) (isSqZero_redπ hA hI _) face₂₃
        (redMap A face₂₃) (redMap_comp_redπ _).symm ((redMap A inl₂).comp ζ)

/-- On a cocycle, the base-changed coboundary is the inclusion of the first two factors. -/
theorem cechD₁B_of_cechD₂_eq_zero
    (c : diff (redπ A' A (B' ⊗[A'] B')) ((redMap A (inl₂ (B' := B'))).comp ζ))
    (h : cechD₂ hA hI hφ hζ c = 0) :
    cechD₁B hA hI hφ hζ c = diffMap (redπ_surjective hA _) (isSqZero_redπ hA hI _)
      (isSqZero_redπ hA hI _) inl₃ (redMap A inl₃) (redMap_comp_redπ _).symm
      ((redMap A inl₂).comp ζ) c := by
  have e : cechD₁B hA hI hφ hζ c = diffMap (redπ_surjective hA _) (isSqZero_redπ hA hI _)
      (isSqZero_redπ hA hI _) inl₃ (redMap A inl₃) (redMap_comp_redπ _).symm
      ((redMap A inl₂).comp ζ) c - cechD₂ hA hI hφ hζ c := by
    simp only [cechD₁B, cechD₂, LinearMap.sub_apply, LinearMap.add_apply]
    abel
  rw [e, h, sub_zero]

/-- `diffBaseChange` sends `c ⊗ 1` to the push-forward of `c` along `inl₃`. -/
theorem diffBaseChange_tmul_one
    (c : diff (redπ A' A (B' ⊗[A'] B')) ((redMap A (inl₂ (B' := B'))).comp ζ)) :
    diffBaseChange ((redMap A inl₂).comp ζ) hA hI (c ⊗ₜ (1 : B')) =
      diffMap (redπ_surjective hA _) (isSqZero_redπ hA hI _) (isSqZero_redπ hA hI _) inl₃
        (redMap A inl₃) (redMap_comp_redπ _).symm ((redMap A inl₂).comp ζ) c :=
  Subtype.ext (LinearMap.ext fun _ => rfl)

/-- **The coboundary operators commute with the flat base change.** -/
theorem diffBaseChange_cechD₁ (t : diff (redπ A' A B') ζ ⊗[A'] B') :
    diffBaseChange ((redMap A inl₂).comp ζ) hA hI ((cechD₁ hA hI hφ hζ).rTensor B' t) =
      cechD₁B hA hI hφ hζ (diffBaseChange ζ hA hI t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add, map_add]
  | tmul D b =>
    rw [LinearMap.rTensor_tmul]
    refine Subtype.ext (LinearMap.ext fun x => ?_)
    rw [diffBaseChange_tmul_apply]
    have e₁ := transitionDiff_of_eq hφ (redπ_surjective hA _) (isSqZero_redπ hA hI _)
      (((hζ.map inl₂).map face₁₃).compat ((hζ.map inl₂).map inl₃)) (chart_face₁₃ (A := A))
      (diffMap (redπ_surjective hA _) (isSqZero_redπ hA hI _) (isSqZero_redπ hA hI _) face₁₃
        (redMap A face₁₃) (redMap_comp_redπ _).symm ((redMap A inl₂).comp ζ)
        (diffBaseChange ζ hA hI (D ⊗ₜ b)))
    set W := diffMap (redπ_surjective hA B') (isSqZero_redπ hA hI B') (isSqZero_redπ hA hI _)
      inr₂ (redMap A inr₂) (redMap_comp_redπ _).symm ζ D with hW
    set Y := diffMap (redπ_surjective hA _) (isSqZero_redπ hA hI _) (isSqZero_redπ hA hI _)
      inl₃ (redMap A inl₃) (redMap_comp_redπ _).symm ((redMap A inr₂).comp ζ) W with hY
    set b₃ : (B' ⊗[A'] B') ⊗[A'] B' := (1 : B' ⊗[A'] B') ⊗ₜ b with hb₃
    have e₂ := transitionDiff_congr hφ (redπ_surjective hA _) (isSqZero_redπ hA hI _)
      (chart_face₂₃ (A := A))
      (((hζ.map inl₂).map face₂₃).compat ((hζ.map inl₂).map inl₃))
      (((hζ.map inr₂).map inl₃).compat ((hζ.map inl₂).map inl₃))
      (diffMap (redπ_surjective hA _) (isSqZero_redπ hA hI _) (isSqZero_redπ hA hI _) face₂₃
        (redMap A face₂₃) (redMap_comp_redπ _).symm ((redMap A inl₂).comp ζ)
        (diffBaseChange ζ hA hI (D ⊗ₜ b))) (b₃ • Y) (LinearMap.ext fun y => by
          show face₂₃ (D.1 y ⊗ₜ b) = b₃ * inl₃ (inr₂ (D.1 y))
          simp [hb₃])
    have e₃ := transitionDiff_naturality hφ (redπ_surjective hA _) (isSqZero_redπ hA hI _)
      (redπ_surjective hA _) (isSqZero_redπ hA hI _) inl₃ (redMap A inl₃)
      (redMap_comp_redπ _).symm ((hζ.map inr₂).compat (hζ.map inl₂))
      (((hζ.map inr₂).map inl₃).compat ((hζ.map inl₂).map inl₃)) W
    simp only [cechD₁B, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, Submodule.coe_sub, LinearMap.sub_apply]
    rw [e₁, e₂, map_smul, hY, e₃]
    simp only [SetLike.val_smul, LinearMap.smul_apply, smul_eq_mul, diffMap_apply,
      diffBaseChange_tmul_apply, cechD₁, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, Submodule.coe_sub, sub_tmul, hb₃, ← hW]
    simp

variable [Algebra.Smooth A' C] [Module.FaithfullyFlat A' B']

/-- **A cocycle is a coboundary**, because the differences commute with the flat base change
and `B'` is faithfully flat. -/
theorem exists_cechD₁_eq
    (c : diff (redπ A' A (B' ⊗[A'] B')) ((redMap A (inl₂ (B' := B'))).comp ζ))
    (h : cechD₂ hA hI hφ hζ c = 0) : ∃ e, cechD₁ hA hI hφ hζ e = c := by
  obtain ⟨t, ht⟩ := (diffBaseChange_bijective ζ hA hI (B' := B')).2 c
  have h₁ : (cechD₁ hA hI hφ hζ).rTensor B' t = c ⊗ₜ (1 : B') := by
    refine (diffBaseChange_bijective ((redMap A inl₂).comp ζ) hA hI (B' := B')).1 ?_
    rw [diffBaseChange_cechD₁, ht, cechD₁B_of_cechD₂_eq_zero hA hI hφ hζ c h,
      diffBaseChange_tmul_one]
  let Q := (LinearMap.range (cechD₁ hA hI hφ hζ)).mkQ
  have h₂ : Q.rTensor B' (c ⊗ₜ (1 : B')) = 0 := by
    rw [← h₁, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    have : Q ∘ₗ cechD₁ hA hI hφ hζ = 0 := by
      ext e
      simp [Q]
    rw [this, LinearMap.rTensor_zero, LinearMap.zero_apply]
  rw [LinearMap.rTensor_tmul] at h₂
  have h₃ : (1 : B') ⊗ₜ[A'] Q c = 0 := by
    rw [← TensorProduct.comm_tmul A' _ B', h₂, LinearEquiv.map_zero]
  rw [Module.FaithfullyFlat.one_tmul_eq_zero_iff, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, LinearMap.mem_range] at h₃
  exact h₃

/-! #### The lift -/

variable [Algebra.Etale A' B']

include hA hI hφ hζ in
/-- **A section over `Spec A` presented by a smooth chart on an étale cover extends over
`Spec A'`.** Let `A' → A` be surjective with square-zero kernel, `ξ` a section of `X` over
`Spec A` lying over `Spec A'`, `B'` an étale, faithfully flat `A'`-algebra and `φ` a section
over the spectrum of a smooth `A'`-algebra `C` with unique infinitesimal lifts, along which `ξ`
pulls back over `Spec (A ⊗_{A'} B')` through `ζ`. Then `ξ` is the restriction of a section over
`Spec A'` lying over `Spec A'`. -/
theorem RelSec.exists_lift_of_chart (hX : IsAlgebraicSpace B S hS X) [hA'' : InSite B A'] :
    ∃ w : RelSec p A', RelSec.map (Algebra.ofId A' A) w = ξ := by
  set g := someLift (redπ_surjective hA B') (isSqZero_redπ hA hI B') ζ with hg
  have hgz := comp_someLift (redπ_surjective hA B') (isSqZero_redπ hA hI B') ζ
  have hz := isLiftOf_map hζ hgz
  obtain ⟨e, he⟩ := exists_cechD₁_eq hA hI hφ hζ _ (cechD₂_cocycle hA hI hφ hζ hz)
  set z' := correct hA hI hφ hζ hz e
  have hz' := isLiftOf_correct hA hI hφ hζ hz e
  have hcoc : cocycle hA hI hφ hζ hz' = 0 := by
    rw [cocycle_correct, he, sub_self]
  have hdesc := map_inl₂_eq_map_inr₂ hA hI hφ hζ hz' hcoc
  obtain ⟨w, hw, -⟩ := RelSec.existsUnique_descend (R := A') (R' := B') hX z' hdesc
  refine ⟨w, ?_⟩
  have hdA := RelSec.existsUnique_descend (R := A) (R' := A ⊗[A'] B') hX
    (RelSec.map (Algebra.TensorProduct.includeLeft : A →ₐ[A'] A ⊗[A'] B') ξ) (by
      rw [RelSec.map_map, RelSec.map_map]
      refine RelSec.map_congr (AlgHom.ext fun a => ?_) ξ
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
        AlgHom.coe_restrictScalars', Algebra.TensorProduct.includeRight_apply]
      rw [← mul_one a, ← smul_eq_mul, ← TensorProduct.smul_tmul', TensorProduct.smul_tmul,
        Algebra.TensorProduct.one_def])
  refine hdA.unique ?_ ?_
  · rw [RelSec.map_map]
    have h1 : (IsScalarTower.toAlgHom A' A (A ⊗[A'] B')).comp (Algebra.ofId A' A) =
        (redπ A' A B').comp (IsScalarTower.toAlgHom A' A' B') := algHom_self_ext _ _
    rw [h1, ← RelSec.map_map, hw]
    exact hz'
  · exact RelSec.map_congr (AlgHom.ext fun a => rfl) ξ

end Cech

end AlgebraicGeometry.Space

end
