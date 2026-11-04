module

public import StacksFrontier.RingTheory.FormsTrace.Framed

/-!
# The framed trace does not depend on the frame

Let `f₁ = (e₁, g₁)` and `f₂ = (e₂, g₂)` be two frames (`Stacks.FormsTrace.ChartFrame`) of the
same finite free `A`-algebra `B` of rank `d`. Both presentations of `B/A` refine into a single one,
over the polynomial ring `T = R''[x_a : a ∈ A]` on the comparison ring `R''` of
`Stacks.FormsTrace.comparisonRing` (built from the unit-fixing group of Stacks 05YQ), which maps
onto `A` by the polynomial extension of `Stacks.FormsTrace.comparisonPsi`:

* the chart ring `N_{g₁}[x_a]` maps to `T` along `pr : N_{g₁} → R''`, and the universal algebras
  form a pushout square;
* the chart ring `N_{g₂}[x_a]` maps to `T` along `act : N_{g₂} → R''`; the base change of its
  universal algebra is the base change along `act`, which is identified with the base change
  along `pr` by the comparison isomorphism `Stacks.FormsTrace.comparisonEquiv`, and after
  evaluation that identification is the identity of `B`.

Given a family `Θ_T` with property (1) of Stacks, Lemma 0FLB on the base change along `pr` of the
universal family to `T`, `Stacks.FormsTrace.descendForms_eq_of_refinement` identifies both
framed traces with the descent of `Θ_T` (`Stacks.FormsTrace.ChartFrame.framedTrace_eq`).

## Main definitions

* `Stacks.FormsTrace.carrierEquivMap`: the base change of an isomorphism of algebras of tables.
* `Stacks.FormsTrace.ChartFrame.comparisonEval`: the map `T → A`.

## Main results

* `Stacks.FormsTrace.carrierLift_carrierEquivMap`: base changed isomorphisms compatible with two
  bases after evaluation stay compatible.
* `Stacks.FormsTrace.ChartFrame.refinementActMap_refinementEquiv`: after evaluation the comparison
  isomorphism over the refinement is the identity of `B`.
* `Stacks.FormsTrace.ChartFrame.framedTrace_eq`: independence of the frame.

## References

* [Stacks Project, Tag 0FLB](https://stacks.math.columbia.edu/tag/0FLB)
* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.FiniteFreeAlgebra
open scoped TensorProduct nonZeroDivisors

universe u

namespace Stacks.FormsTrace

variable {d : ℕ} [NeZero d]

section CarrierEquiv

variable {R T : Type u} [CommRing R] [CommRing T]

/-- **The base change of an isomorphism of algebras of tables** along a ring map `φ : R → T`:
the isomorphism of the algebras of the base changed tables with the base changed matrix. -/
def carrierEquivMap (φ : R →+* T) {m n : FiniteFreeAlgebra R d} (Φ : Carrier m ≃ₐ[R] Carrier n) :
    Carrier (FiniteFreeAlgebra.map φ m) ≃ₐ[T] Carrier (FiniteFreeAlgebra.map φ n) :=
  (StructureIso.map φ (structureIsoOfAlgEquiv Φ)).toAlgEquiv

/-- `Stacks.FormsTrace.carrierEquivMap` in coordinates. -/
theorem carrierEquivMap_apply (φ : R →+* T) {m n : FiniteFreeAlgebra R d}
    (Φ : Carrier m ≃ₐ[R] Carrier n) (x : Carrier (FiniteFreeAlgebra.map φ m)) (k : Fin d) :
    carrierEquivMap φ Φ x k = ∑ i, φ (Φ (Carrier.basisVector m i) k) * x i :=
  structureIso_toAlgEquiv_apply _ x k

/-- A ring map out of the algebra of a table, semilinear along `ψ` and carrying the standard basis
to a family `b`, is `x ↦ ∑ₖ ψ(x k) • b k`. -/
theorem ringHom_carrier_apply {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (ψ : R →+* A) {m : FiniteFreeAlgebra R d} (χ : Carrier m →+* B)
    (hχ : ∀ r, χ (algebraMap R (Carrier m) r) = algebraMap A B (ψ r)) (b : Fin d → B)
    (hb : ∀ i, χ (Carrier.basisVector m i) = b i) (x : Carrier m) :
    χ x = ∑ k, ψ (x k) • b k := by
  conv_lhs => rw [← Carrier.sum_smul_basisVector x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def, map_mul, hχ, hb, ← Algebra.smul_def]

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- **Base changed isomorphisms stay compatible with the bases after evaluation.** Let
`Φ : Carrier m ≃ Carrier n` over `R`, let `φ : R → T` and `ψ : T → A`, and let `b₁`, `b₂` be bases
of `B` over `A` whose tables are the base changes of `m`, `n` along `ψ ∘ φ`. If after evaluation
`Φ` carries the standard basis vector `i` to `b₁ i`, expressed in `b₂`, then the evaluations of
the base changes along `φ` of the two algebras satisfy `χ₂ ∘ (Φ ⊗ T) = χ₁`. -/
theorem carrierLift_carrierEquivMap (φ : R →+* T) (ψ : T →+* A) {m n : FiniteFreeAlgebra R d}
    (Φ : Carrier m ≃ₐ[R] Carrier n) (b₁ b₂ : Module.Basis (Fin d) A B) (hb₁ : b₁ 0 = 1)
    (hb₂ : b₂ 0 = 1) (h₁ : FiniteFreeAlgebra.map ψ (FiniteFreeAlgebra.map φ m) = ofBasis b₁ hb₁)
    (h₂ : FiniteFreeAlgebra.map ψ (FiniteFreeAlgebra.map φ n) = ofBasis b₂ hb₂)
    (hΦ : ∀ i, ∑ k, ψ (φ (Φ (Carrier.basisVector m i) k)) • b₂ k = b₁ i)
    (x : Carrier (FiniteFreeAlgebra.map φ m)) :
    carrierLift ψ _ b₂ hb₂ h₂ (carrierEquivMap φ Φ x) = carrierLift ψ _ b₁ hb₁ h₁ x := by
  rw [carrierLift_apply, carrierLift_apply]
  simp only [carrierEquivMap_apply, map_sum, map_mul]
  calc ∑ k, (∑ i, ψ (φ (Φ (Carrier.basisVector m i) k)) * ψ (x i)) • b₂ k
      = ∑ i, ψ (x i) • ∑ k, ψ (φ (Φ (Carrier.basisVector m i) k)) • b₂ k := by
        simp only [Finset.sum_smul, Finset.smul_sum, smul_smul, mul_comm]
        exact Finset.sum_comm
    _ = ∑ i, ψ (x i) • b₁ i := by simp only [hΦ]

end CarrierEquiv

namespace ChartFrame

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (f₁ f₂ : ChartFrame d A B)

/-- The comparison ring `R''` of two frames. -/
abbrev ComparisonBaseRing : Type u := comparisonRing.{u} f₁.g f₂.g

/-- The common refinement `T = R''[x_a : a ∈ A]` of the presentations of two frames. -/
abbrev Refinement : Type u := comparisonChartRing f₁.g f₂.g A

/-- The base change along `pr` of the universal family to the common refinement. -/
abbrev RefinementAlgebra : Type u := Carrier (tableOfHom (comparisonChartClassify f₁.g f₂.g A))

/-- The map `ψ : R'' → A` of two frames. -/
def comparisonPsiOf : f₁.ComparisonBaseRing f₂ →+* A :=
  comparisonPsi f₁.basis f₂.basis f₁.basis_zero f₂.basis_zero f₁.isUnit f₂.isUnit

/-- **The evaluation of the common refinement** `T = R''[x_a] → A`: `x_a ↦ a`, and `ψ` on `R''`. -/
def comparisonEval : f₁.Refinement f₂ →+* A := MvPolynomial.eval₂Hom (f₁.comparisonPsiOf f₂) id

/-- The evaluation of the refinement is surjective. -/
theorem comparisonEval_surjective : Function.Surjective (f₁.comparisonEval f₂) := fun a =>
  ⟨MvPolynomial.X a, MvPolynomial.eval₂_X _ _ a⟩

/-- The evaluation of the refinement restricts to `ψ` on `R''`. -/
theorem comparisonEval_algebraMap (r : f₁.ComparisonBaseRing f₂) :
    f₁.comparisonEval f₂ (algebraMap _ (f₁.Refinement f₂) r) = f₁.comparisonPsiOf f₂ r :=
  MvPolynomial.eval₂_C _ _ r

/-- The map `N_{g₁}[x_a] → T` along `pr`. -/
def toRefinement₁ : f₁.Chart →+* f₁.Refinement f₂ := MvPolynomial.map (comparisonPr.{u} f₁.g f₂.g)

/-- The map `N_{g₂}[x_a] → T` along `act`. -/
def toRefinement₂ : f₂.Chart →+* f₁.Refinement f₂ :=
  MvPolynomial.map (comparisonAct.{u} f₁.g f₂.g)

/-- `toRefinement₁` on `N_{g₁}`. -/
theorem toRefinement₁_algebraMap (n : universalChartBase.{u} f₁.g) :
    f₁.toRefinement₁ f₂ (algebraMap _ f₁.Chart n) =
      algebraMap _ (f₁.Refinement f₂) (comparisonPr.{u} f₁.g f₂.g n) :=
  MvPolynomial.map_C _ n

/-- `toRefinement₂` on `N_{g₂}`. -/
theorem toRefinement₂_algebraMap (n : universalChartBase.{u} f₂.g) :
    f₁.toRefinement₂ f₂ (algebraMap _ f₂.Chart n) =
      algebraMap _ (f₁.Refinement f₂) (comparisonAct.{u} f₁.g f₂.g n) :=
  MvPolynomial.map_C _ n

/-- The refinement is compatible with the evaluation of the first frame. -/
theorem comparisonEval_toRefinement₁ (x : f₁.Chart) :
    f₁.comparisonEval f₂ (f₁.toRefinement₁ f₂ x) = f₁.eval x := by
  refine (MvPolynomial.eval₂Hom_map_hom _ _ _ x).trans ?_
  rw [comparisonPsiOf, comparisonPsi_comp_pr]
  rfl

/-- The refinement is compatible with the evaluation of the second frame. -/
theorem comparisonEval_toRefinement₂ (x : f₂.Chart) :
    f₁.comparisonEval f₂ (f₁.toRefinement₂ f₂ x) = f₂.eval x := by
  refine (MvPolynomial.eval₂Hom_map_hom _ _ _ x).trans ?_
  rw [comparisonPsiOf, comparisonPsi_comp_act]
  rfl

/-- The table of the first chart, base changed to the refinement. -/
theorem map_table_toRefinement₁ :
    FiniteFreeAlgebra.map (f₁.toRefinement₁ f₂) (tableOfHom (universalChartClassify A f₁.g)) =
      tableOfHom (comparisonChartClassify f₁.g f₂.g A) := by
  rw [map_tableOfHom]
  congr 1
  exact RingHom.ext fun x => f₁.toRefinement₁_algebraMap f₂ _

/-- The classifying map of the base change along `act` of the universal family to `T`. -/
abbrev actClassify : universalRing d →+* f₁.Refinement f₂ :=
  (algebraMap (f₁.ComparisonBaseRing f₂) (f₁.Refinement f₂)).comp
    ((comparisonAct.{u} f₁.g f₂.g).comp (universalChartBaseClassify.{u} f₂.g))

/-- The table of the second chart, base changed to the refinement. -/
theorem map_table_toRefinement₂ :
    FiniteFreeAlgebra.map (f₁.toRefinement₂ f₂) (tableOfHom (universalChartClassify A f₂.g)) =
      tableOfHom (f₁.actClassify f₂) := by
  rw [map_tableOfHom]
  congr 1
  exact RingHom.ext fun x => f₁.toRefinement₂_algebraMap f₂ _

/-- The table of the refinement along `pr` is the base change of the table of `pr`. -/
theorem table_refinement_eq :
    tableOfHom (comparisonChartClassify f₁.g f₂.g A) = FiniteFreeAlgebra.map
      (algebraMap (f₁.ComparisonBaseRing f₂) (f₁.Refinement f₂))
      (tableOfHom ((comparisonPr.{u} f₁.g f₂.g).comp (universalChartBaseClassify.{u} f₁.g))) := by
  rw [map_tableOfHom]
  rfl

/-- The table of the refinement along `act` is the base change of the table of `act`. -/
theorem table_act_eq :
    FiniteFreeAlgebra.map (algebraMap (f₁.ComparisonBaseRing f₂) (f₁.Refinement f₂))
      (tableOfHom ((comparisonAct.{u} f₁.g f₂.g).comp (universalChartBaseClassify.{u} f₂.g))) =
      tableOfHom (f₁.actClassify f₂) :=
  map_tableOfHom _ _

/-- **The comparison isomorphism over the refinement**: the base change along `pr` and the base
change along `act` of the universal family to `T` are isomorphic `T`-algebras. -/
def refinementEquiv : f₁.RefinementAlgebra f₂ ≃ₐ[f₁.Refinement f₂]
    Carrier (tableOfHom (f₁.actClassify f₂)) :=
  (carrierCongr (f₁.table_refinement_eq f₂)).trans
    ((carrierEquivMap (algebraMap (f₁.ComparisonBaseRing f₂) (f₁.Refinement f₂))
      (comparisonEquiv.{u} f₁.g f₂.g)).trans (carrierCongr (f₁.table_act_eq f₂)))

/-- The evaluation of the table along `pr` is the table of the first basis. -/
theorem map_table_refinement :
    FiniteFreeAlgebra.map (f₁.comparisonEval f₂)
        (tableOfHom (comparisonChartClassify f₁.g f₂.g A)) =
      ofBasis f₁.basis f₁.basis_zero := by
  rw [map_tableOfHom]
  have hc : comparisonChartClassify f₁.g f₂.g A =
      (f₁.toRefinement₁ f₂).comp (universalChartClassify A f₁.g) :=
    RingHom.ext fun x => (f₁.toRefinement₁_algebraMap f₂ _).symm
  have h : (f₁.comparisonEval f₂).comp (comparisonChartClassify f₁.g f₂.g A) =
      (f₁.eval).comp (universalChartClassify A f₁.g) := by
    rw [hc, ← RingHom.comp_assoc]
    exact RingHom.ext fun x => f₁.comparisonEval_toRefinement₁ f₂ _
  rw [h, ← map_tableOfHom, map_table]

/-- The evaluation of the table along `act` is the table of the second basis. -/
theorem map_table_act :
    FiniteFreeAlgebra.map (f₁.comparisonEval f₂) (tableOfHom (f₁.actClassify f₂)) =
      ofBasis f₂.basis f₂.basis_zero := by
  rw [← f₁.map_table_toRefinement₂ f₂, map_tableOfHom, map_tableOfHom]
  have h : (f₁.comparisonEval f₂).comp ((f₁.toRefinement₂ f₂).comp
      (universalChartClassify A f₂.g)) = (f₂.eval).comp (universalChartClassify A f₂.g) :=
    RingHom.ext fun x => f₁.comparisonEval_toRefinement₂ f₂ _
  rw [h, ← map_tableOfHom, map_table]

/-- The evaluation `T`-carrier along `pr` → `B`, by the first basis. -/
def refinementMap : f₁.RefinementAlgebra f₂ →+* B :=
  carrierLift (f₁.comparisonEval f₂) _ f₁.basis f₁.basis_zero (f₁.map_table_refinement f₂)

/-- The evaluation `T`-carrier along `act` → `B`, by the second basis. -/
def refinementActMap : Carrier (tableOfHom (f₁.actClassify f₂)) →+* B :=
  carrierLift (f₁.comparisonEval f₂) _ f₂.basis f₂.basis_zero (f₁.map_table_act f₂)

/-- The comparison isomorphism over the refinement in coordinates. -/
theorem refinementEquiv_apply (x : f₁.RefinementAlgebra f₂) (k : Fin d) :
    f₁.refinementEquiv f₂ x k = ∑ i, algebraMap (f₁.ComparisonBaseRing f₂) (f₁.Refinement f₂)
      (comparisonEquiv.{u} f₁.g f₂.g (Carrier.basisVector _ i) k) * x i := by
  rw [refinementEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply]
  refine (carrierCongr_apply _ _ k).trans ((carrierEquivMap_apply _ _ _ k).trans ?_)
  exact Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) rfl (carrierCongr_apply _ x i)

/-- After evaluation, the comparison isomorphism over the refinement is the identity of `B`. -/
theorem refinementActMap_refinementEquiv (x : f₁.RefinementAlgebra f₂) :
    f₁.refinementActMap f₂ (f₁.refinementEquiv f₂ x) = f₁.refinementMap f₂ x := by
  classical
  obtain ⟨χ₁, χ₂, hχ₁, hχ₂, hb₁, hb₂, hc⟩ := exists_comparisonEquiv_compatible f₁.basis f₂.basis
    f₁.basis_zero f₂.basis_zero f₁.isUnit f₂.isUnit
  set c : Fin d → Fin d → A := fun i k => f₁.comparisonEval f₂ (algebraMap _ (f₁.Refinement f₂)
      (comparisonEquiv.{u} f₁.g f₂.g (Carrier.basisVector _ i) k)) with hcdef
  have hΦ : ∀ i, ∑ k, c i k • f₂.basis k = f₁.basis i := by
    intro i
    have h1 := ringHom_carrier_apply (f₁.comparisonPsiOf f₂) χ₂ hχ₂ f₂.basis (fun k => by
      rw [← Carrier.basis_apply]; exact hb₂ k) (comparisonEquiv.{u} f₁.g f₂.g
        (Carrier.basisVector _ i))
    have h2 : χ₁ (Carrier.basisVector _ i) = f₁.basis i := by
      rw [← Carrier.basis_apply]; exact hb₁ i
    rw [hc, h2] at h1
    rw [h1]
    exact Finset.sum_congr rfl fun k _ =>
      congrArg (· • f₂.basis k) (f₁.comparisonEval_algebraMap f₂ _)
  rw [refinementActMap, refinementMap, carrierLift_apply, carrierLift_apply]
  have hx : ∀ k, f₁.comparisonEval f₂ (f₁.refinementEquiv f₂ x k) =
      ∑ i, c i k * f₁.comparisonEval f₂ (x i) := fun k => by
    rw [refinementEquiv_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => map_mul _ _ _
  simp only [hx]
  calc ∑ k, (∑ i, c i k * f₁.comparisonEval f₂ (x i)) • f₂.basis k
      = ∑ k, ∑ i, f₁.comparisonEval f₂ (x i) • c i k • f₂.basis k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, mul_comm]
    _ = ∑ i, f₁.comparisonEval f₂ (x i) • ∑ k, c i k • f₂.basis k := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => (Finset.smul_sum ..).symm
    _ = ∑ i, f₁.comparisonEval f₂ (x i) • f₁.basis i := by simp only [hΦ]

/-- **Independence of the frame** (Stacks 0FLB, 0FLC). Two frames `f₁`, `f₂` of the same finite
free `A`-algebra `B` give the same framed trace, for any families `Θ₁`, `Θ₂` with property (1) of
Stacks, Lemma 0FLB on their chart rings, as soon as such a family `Θ_T` exists on the base change
along `pr` of the universal family to the common refinement `T = R''[x_a : a ∈ A]`. -/
theorem framedTrace_eq
    {Θ₁ : ∀ p : ℕ, ⋀[f₁.ChartAlgebra]^p Ω[f₁.ChartAlgebra⁄ℤ] →ₗ[f₁.Chart]
      ⋀[f₁.Chart]^p Ω[f₁.Chart⁄ℤ]} (hΘ₁ : IsFormsTrace f₁.Chart f₁.ChartAlgebra Θ₁)
    {Θ₂ : ∀ p : ℕ, ⋀[f₂.ChartAlgebra]^p Ω[f₂.ChartAlgebra⁄ℤ] →ₗ[f₂.Chart]
      ⋀[f₂.Chart]^p Ω[f₂.Chart⁄ℤ]} (hΘ₂ : IsFormsTrace f₂.Chart f₂.ChartAlgebra Θ₂)
    {ΘT : ∀ p : ℕ, ⋀[f₁.RefinementAlgebra f₂]^p Ω[f₁.RefinementAlgebra f₂⁄ℤ]
      →ₗ[f₁.Refinement f₂] ⋀[f₁.Refinement f₂]^p Ω[f₁.Refinement f₂⁄ℤ]}
    (hΘT : IsFormsTrace (f₁.Refinement f₂) (f₁.RefinementAlgebra f₂) ΘT) :
    f₁.framedTrace Θ₁ hΘ₁ = f₂.framedTrace Θ₂ hΘ₂ := by
  classical
  set T := f₁.Refinement f₂
  set U := f₁.RefinementAlgebra f₂
  -- the two presentations
  let := f₁.algebraChart
  let := f₁.algebraCarrier
  let := f₁.algebraChartTarget
  have := f₁.isScalarTower_chart
  have := f₁.isScalarTower_carrier
  have := f₁.isPushout
  let := f₂.algebraChart
  let := f₂.algebraCarrier
  let := f₂.algebraChartTarget
  have := f₂.isScalarTower_chart
  have := f₂.isScalarTower_carrier
  have := f₂.isPushout
  have : Module.Finite A B := Module.Finite.of_basis f₁.basis
  have : Module.Free A B := Module.Free.of_basis f₁.basis
  -- the common refinement
  let : Algebra T A := (f₁.comparisonEval f₂).toAlgebra
  let : Algebra U B := (f₁.refinementMap f₂).toAlgebra
  let : Algebra T B := ((algebraMap A B).comp (f₁.comparisonEval f₂)).toAlgebra
  have : IsScalarTower T A B := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower T U B := IsScalarTower.of_algebraMap_eq fun r =>
    (carrierLift_algebraMap _ _ _ _ _ r).symm
  have : Algebra.IsPushout T U A B :=
    isPushout_of_bases_one (Carrier.basis _) f₁.basis fun x => carrierLift_apply _ _ _ _ _ x
  -- the refinement of the first presentation
  let σ₁ : f₁.ChartAlgebra →+* U := (carrierCongr (f₁.map_table_toRefinement₁ f₂)).toRingHom.comp
    (Carrier.mapRingHom (f₁.toRefinement₁ f₂) _)
  have hσ₁ : ∀ x k, σ₁ x k = f₁.toRefinement₁ f₂ (x k) := fun x k => carrierCongr_apply _ _ k
  let : Algebra f₁.Chart T := (f₁.toRefinement₁ f₂).toAlgebra
  let : Algebra f₁.ChartAlgebra U := σ₁.toAlgebra
  let : Algebra f₁.Chart U := ((algebraMap T U).comp (f₁.toRefinement₁ f₂)).toAlgebra
  have : IsScalarTower f₁.Chart T U := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower f₁.Chart f₁.ChartAlgebra U := IsScalarTower.of_algebraMap_eq fun r => by
    refine Carrier.ext fun k => ?_
    change (algebraMap T U (f₁.toRefinement₁ f₂ r)) k = σ₁ (algebraMap f₁.Chart _ r) k
    rw [hσ₁, Carrier.algebraMap_coord, Carrier.algebraMap_coord]
    split_ifs <;> simp
  have : Algebra.IsPushout f₁.Chart f₁.ChartAlgebra T U := by
    refine isPushout_of_bases_one (Carrier.basis _) (Carrier.basis _) fun x => ?_
    refine Carrier.ext fun k => ?_
    change σ₁ x k = _
    rw [hσ₁, Carrier.sum_apply]
    have hterm : ∀ i : Fin d, (algebraMap f₁.Chart T ((Carrier.basis _).repr x i) •
        Carrier.basis (tableOfHom (comparisonChartClassify f₁.g f₂.g A)) i) k =
          f₁.toRefinement₁ f₂ (x i) * (if k = i then 1 else 0) := fun i => by
      rw [Carrier.smul_apply, Carrier.basis_apply, Carrier.basisVector_apply,
        Carrier.basis_repr_apply]
      rfl
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_eq_single k
      (fun i _ hi => by simp [Ne.symm hi]) (fun h => absurd (Finset.mem_univ k) h)]
    simp
  have : IsScalarTower f₁.Chart T A := IsScalarTower.of_algebraMap_eq fun r =>
    (f₁.comparisonEval_toRefinement₁ f₂ r).symm
  have : IsScalarTower f₁.ChartAlgebra U B := IsScalarTower.of_algebraMap_eq fun x => by
    change f₁.carrierMap x = f₁.refinementMap f₂ (σ₁ x)
    rw [carrierMap, refinementMap, carrierLift_apply, carrierLift_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [hσ₁, comparisonEval_toRefinement₁]
  -- the refinement of the second presentation
  let σ₂ : f₂.ChartAlgebra →+* U := (f₁.refinementEquiv f₂).symm.toRingHom.comp
    ((carrierCongr (f₁.map_table_toRefinement₂ f₂)).toRingHom.comp
      (Carrier.mapRingHom (f₁.toRefinement₂ f₂) _))
  let τ₂ : f₂.ChartAlgebra →+* Carrier (tableOfHom (f₁.actClassify f₂)) :=
    (carrierCongr (f₁.map_table_toRefinement₂ f₂)).toRingHom.comp
      (Carrier.mapRingHom (f₁.toRefinement₂ f₂) _)
  have hτ₂ : ∀ x k, τ₂ x k = f₁.toRefinement₂ f₂ (x k) := fun x k => carrierCongr_apply _ _ k
  have hσ₂ : ∀ x, σ₂ x = (f₁.refinementEquiv f₂).symm (τ₂ x) := fun _ => rfl
  have hτ₂alg : ∀ r, τ₂ (algebraMap f₂.Chart f₂.ChartAlgebra r) =
      algebraMap T _ (f₁.toRefinement₂ f₂ r) := fun r => by
    refine Carrier.ext fun k => ?_
    rw [hτ₂, Carrier.algebraMap_coord, Carrier.algebraMap_coord]
    split_ifs <;> simp
  have hτ₂sum : ∀ x, τ₂ x = ∑ i, f₁.toRefinement₂ f₂ (x i) •
      Carrier.basis (tableOfHom (f₁.actClassify f₂)) i := fun x => by
    refine Carrier.ext fun k => ?_
    rw [hτ₂, Carrier.sum_apply]
    have hterm : ∀ i : Fin d, (f₁.toRefinement₂ f₂ (x i) •
        Carrier.basis (tableOfHom (f₁.actClassify f₂)) i) k =
          f₁.toRefinement₂ f₂ (x i) * (if k = i then 1 else 0) := fun i => by
      rw [Carrier.smul_apply, Carrier.basis_apply, Carrier.basisVector_apply]
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_eq_single k
      (fun i _ hi => by simp [Ne.symm hi]) (fun h => absurd (Finset.mem_univ k) h)]
    simp
  let : Algebra f₂.Chart T := (f₁.toRefinement₂ f₂).toAlgebra
  let : Algebra f₂.ChartAlgebra U := σ₂.toAlgebra
  let : Algebra f₂.Chart U := ((algebraMap T U).comp (f₁.toRefinement₂ f₂)).toAlgebra
  have : IsScalarTower f₂.Chart T U := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower f₂.Chart f₂.ChartAlgebra U := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap T U (f₁.toRefinement₂ f₂ r) = σ₂ (algebraMap f₂.Chart _ r)
    rw [hσ₂, hτ₂alg, AlgEquiv.commutes]
  have : Algebra.IsPushout f₂.Chart f₂.ChartAlgebra T U := by
    refine isPushout_of_bases_one (Carrier.basis _)
      ((Carrier.basis (tableOfHom (f₁.actClassify f₂))).map
        (f₁.refinementEquiv f₂).symm.toLinearEquiv) fun x => ?_
    change σ₂ x = _
    rw [hσ₂, hτ₂sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Module.Basis.map_apply, Carrier.basis_repr_apply]
    rfl
  have : IsScalarTower f₂.Chart T A := IsScalarTower.of_algebraMap_eq fun r =>
    (f₁.comparisonEval_toRefinement₂ f₂ r).symm
  have : IsScalarTower f₂.ChartAlgebra U B := IsScalarTower.of_algebraMap_eq fun x => by
    change f₂.carrierMap x = f₁.refinementMap f₂ (σ₂ x)
    rw [hσ₂, ← f₁.refinementActMap_refinementEquiv f₂, AlgEquiv.apply_symm_apply, carrierMap,
      refinementActMap, carrierLift_apply, carrierLift_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [hτ₂, comparisonEval_toRefinement₂]
  -- the nice elements
  have hTnice := discr_comparisonChartRing_nice (g' := f₂.g) A f₁.good
  obtain ⟨N₁, hN₁⟩ := f₁.nice.pow_smul_kaehler
  obtain ⟨N₂, hN₂⟩ := f₂.nice.pow_smul_kaehler
  have hΔT : Algebra.discr T (Carrier.basis (tableOfHom (comparisonChartClassify f₁.g f₂.g A))) =
      algebraMap (f₁.ComparisonBaseRing f₂) T
        (comparisonPr.{u} f₁.g f₂.g (universalChartBaseClassify.{u} f₁.g (universalDiscr d))) := by
    rw [discr_tableOfHom]
    rfl
  have hreg₁ : ∀ p, IsSMulRegular (⋀[T]^p Ω[T⁄ℤ]) (algebraMap f₁.Chart T
      (Algebra.discr f₁.Chart (Carrier.basis (tableOfHom (universalChartClassify A f₁.g))))) := by
    intro p
    have h : algebraMap f₁.Chart T
        (Algebra.discr f₁.Chart (Carrier.basis (tableOfHom (universalChartClassify A f₁.g)))) =
        Algebra.discr T (Carrier.basis (tableOfHom (comparisonChartClassify f₁.g f₂.g A))) := by
      rw [hΔT, discr_tableOfHom]
      exact f₁.toRefinement₁_algebraMap f₂ _
    rw [h]
    exact hTnice.regular p
  obtain ⟨v, hv, hact⟩ := comparisonAct_discr.{u} f₁.g f₂.g
  have hreg₂ : ∀ p, IsSMulRegular (⋀[T]^p Ω[T⁄ℤ]) (algebraMap f₂.Chart T
      (Algebra.discr f₂.Chart (Carrier.basis (tableOfHom (universalChartClassify A f₂.g))))) := by
    intro p
    have h : algebraMap f₂.Chart T
        (Algebra.discr f₂.Chart (Carrier.basis (tableOfHom (universalChartClassify A f₂.g)))) =
        algebraMap (f₁.ComparisonBaseRing f₂) T v *
          Algebra.discr T (Carrier.basis (tableOfHom (comparisonChartClassify f₁.g f₂.g A))) := by
      rw [hΔT, discr_tableOfHom, ← map_mul, ← hact]
      exact f₁.toRefinement₂_algebraMap f₂ _
    rw [h]
    exact ((hv.map _).isSMulRegular _).mul (hTnice.regular p)
  have hwT := hΘT.isWedgeLinear_of_isNiceElement hTnice
  have e₁ := descendForms_eq_of_refinement (R' := f₁.Chart) (S' := f₁.ChartAlgebra) (A' := A)
    (B' := B) (T := T) (U := U) f₁.eval_surjective (f₁.comparisonEval_surjective f₂) hN₁ hreg₁ hΘ₁
    (hΘ₁.isWedgeLinear_of_isNiceElement f₁.nice) hΘT hwT
  have e₂ := descendForms_eq_of_refinement (R' := f₂.Chart) (S' := f₂.ChartAlgebra) (A' := A)
    (B' := B) (T := T) (U := U) f₂.eval_surjective (f₁.comparisonEval_surjective f₂) hN₂ hreg₂ hΘ₂
    (hΘ₂.isWedgeLinear_of_isNiceElement f₂.nice) hΘT hwT
  exact e₁.trans e₂.symm

end ChartFrame

end Stacks.FormsTrace

end
