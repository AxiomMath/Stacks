module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedBaseChangeCancel
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamFormsDataCompletion
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamUnit
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedFormsOfCompletion

/-!
# The structure module of a ring with forms

For a ring with forms `R = (D, Ω^*_D)` (`Crystalline.FormsData`) with `D` `p`-adically complete,
the module `D` itself with the connection `∇ x = 1 ⊗ d x` is a module with an integrable completed
connection: `Crystalline.FormsData.unitConnModule`.  It is the pair of the structure sheaf
`𝒪_{X/S}` under the correspondence of [Stacks, Proposition 60.17.4, Tag 07JH].

This module proves that it is stable under base change: for a morphism `g : R → R'` of rings with
forms, the base change `D ⊗̂_D D'` of the structure module of `R` is the structure module of
`R'`, by a horizontal isomorphism (`Crystalline.FormsData.baseChangeUnitHom`).

## Main definitions

* `Crystalline.FormsData.unitConnModule` — the structure module `(D, ∇ = 1 ⊗ d)`.
* `Crystalline.FormsData.baseChangeUnitEquiv` and `Crystalline.FormsData.baseChangeUnitHom` —
  `D ⊗̂_D D' ≃ D'`, horizontal.
* `Crystalline.FormsData.formsComplex` — the completed divided power de Rham complex
  `D → Ω̂¹_D → Ω̂²_D → ⋯` of a divided power ring, and
  `Crystalline.FormsData.unitComplexIso` — the complex `D ⊗^∧_D Ω^*_D` of the structure module is
  that complex.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public noncomputable section

open DividedPowers
open scoped TensorProduct

universe u

namespace Crystalline

namespace FormsData

variable {p : ℕ} (R : FormsData.{u} p)

/-- The universal differential of a ring with forms kills `1`. -/
theorem diff_one : R.diff 1 = 0 :=
  CompletedConnection.eq_zero_of_leibniz R.diff_mul

/-- **The connection `∇ x = 1 ⊗ d x` of the structure module.** -/
def unitNabla : CompletedConnection p R.ring (R.Om 1) R.diff R.ring :=
  CompletedDeRham.unitConnection p R.ring (R.Om 1) R.diff R.diff_add R.diff_mul

/-- The connection of the structure module sends `x` to `1 ⊗ d x`. -/
theorem unitNabla_apply (x : R.ring) :
    R.unitNabla x = toCompletedTensor p R.ring (R.Om 1) R.ring ((1 : R.ring) ⊗ₜ R.diff x) :=
  rfl

/-- `∇ 1 = 0` for the structure module. -/
theorem unitNabla_one : R.unitNabla 1 = 0 := by
  rw [unitNabla_apply, diff_one, TensorProduct.tmul_zero, map_zero]

/-- **The connection of the structure module is integrable**: `∇(∇ x) = ∇(1 ⊗ d x) =
d x ∧ ∇ 1 + 1 ⊗ d(d x) = 0`. -/
theorem isCurvatureZero_unitNabla :
    CompletedDeRham.IsCurvatureZero p R.ring R.Om R.wedge R.deRham R.ring R.unitNabla
      R.isGradedLeibniz := by
  intro x
  rw [unitNabla_apply, CompletedDeRham.differential_of_tmul, unitNabla_one, map_zero, zero_add,
    R.deRham_diff, TensorProduct.tmul_zero, map_zero]

/-- **The structure module `(D, ∇ = 1 ⊗ d)` of a ring with forms whose ring is `p`-adically
complete.** -/
abbrev unitConnModule (hR : IsPAdicallyComplete p R.ring R.ring) : ConnModule R where
  carrier := R.ring
  isPAdicallyComplete := hR
  nabla := R.unitNabla
  isCurvatureZero := R.isCurvatureZero_unitNabla

/-- The underlying module of the structure module is `D`. -/
@[simp] theorem unitConnModule_carrier (hR : IsPAdicallyComplete p R.ring R.ring) :
    (R.unitConnModule hR).carrier = R.ring := rfl

/-! ### Base change of the structure module -/

section BaseChange

variable {R} {R' : FormsData.{u} p} (g : Hom R R') (hR : IsPAdicallyComplete p R.ring R.ring)
  (hR' : IsPAdicallyComplete p R'.ring R'.ring)

/-- **The base change `D ⊗̂_D D'` of the structure module is `D'`**: the completion of
`D' ⊗_D D ≃ D'`, followed by the completeness of `D'`. -/
def baseChangeUnitEquiv :
    letI : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
    CompletedConnection.baseChangeCarrier p R.ring R'.ring R.ring ≃ₗ[R'.ring] R'.ring :=
  letI : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
  haveI : IsAdicComplete (pAdicIdeal (A := R'.ring) p) R'.ring := hR'
  ((AdicCompletion.congr (pAdicIdeal (A := R'.ring) p)
      (TensorProduct.AlgebraTensorModule.rid R.ring R'.ring R'.ring)).restrictScalars
      R'.ring).trans (AdicCompletion.ofLinearEquiv (pAdicIdeal (A := R'.ring) p) R'.ring).symm

/-- Completing a linear equivalence and then identifying with the complete target is `e`. -/
private theorem ofLinearEquiv_symm_congr_of {A M N : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] [AddCommGroup N] [Module A N] (I : Ideal A) [IsAdicComplete I N] (e : M ≃ₗ[A] N)
    (m : M) :
    (AdicCompletion.ofLinearEquiv I N).symm (AdicCompletion.congr I e (AdicCompletion.of I M m)) =
      e m := by
  change (AdicCompletion.ofLinearEquiv I N).symm (AdicCompletion.map _ _ (AdicCompletion.of _ _ m))
    = _
  rw [AdicCompletion.map_of, AdicCompletion.ofLinearEquiv_symm_of]
  rfl

/-- The isomorphism `D ⊗̂_D D' ≃ D'` sends the class of `b ⊗ r` to `b · g(r)`. -/
theorem baseChangeUnitEquiv_of_tmul (b : R'.ring) (r : R.ring) :
    letI : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
    baseChangeUnitEquiv g hR' (AdicCompletion.of _ _ (b ⊗ₜ[R.ring] r)) = b * g.toRingHom r := by
  let : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
  have : IsAdicComplete (pAdicIdeal (A := R'.ring) p) R'.ring := hR'
  refine (ofLinearEquiv_symm_congr_of _ (TensorProduct.AlgebraTensorModule.rid R.ring R'.ring
    R'.ring) _).trans ?_
  change r • b = _
  rw [Algebra.smul_def, mul_comm]
  rfl

/-- The inverse of `D ⊗̂_D D' ≃ D'` sends `b` to `b · (1 ⊗ 1)`. -/
theorem baseChangeUnitEquiv_symm_apply (b : R'.ring) :
    letI : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
    (baseChangeUnitEquiv g hR').symm b =
      b • CompletedConnection.baseChangeInclusion p R.ring R'.ring R.ring 1 := by
  let : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
  rw [LinearEquiv.symm_apply_eq, LinearEquiv.map_smul,
    CompletedConnection.baseChangeInclusion_apply, baseChangeUnitEquiv_of_tmul, map_one,
    mul_one, smul_eq_mul, mul_one]

/-- **The base change of the structure module is the structure module**, by the horizontal
isomorphism `b ↦ b · (1 ⊗ 1)`: the base-changed connection kills `1 ⊗ 1` because the
connection of the structure module kills `1`. -/
def baseChangeUnitHom :
    ConnModule.Hom (R'.unitConnModule hR') ((R.unitConnModule hR).baseChange g) :=
  letI : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
  { toLinearMap := (baseChangeUnitEquiv g hR').symm.toLinearMap
    horizontal := by
      intro b
      have h0 : ((R.unitConnModule hR).baseChange g).nabla
          (CompletedConnection.baseChangeInclusion p R.ring R'.ring R.ring 1) = 0 :=
        (CompletedConnection.baseChange_inclusion p R.ring R'.ring R.ring (R.Om 1) (R'.Om 1)
          R'.diff (g.psi 1) R.unitNabla R'.diff_add R'.diff_mul g.psi_diff 1).trans
          (by rw [unitNabla_one]; exact map_zero _)
      have hf : ∀ c : R'.ring, (baseChangeUnitEquiv g hR').symm.toLinearMap c =
          c • CompletedConnection.baseChangeInclusion p R.ring R'.ring R.ring 1 :=
        fun c ↦ baseChangeUnitEquiv_symm_apply g hR' c
      refine (congrArg _ (hf b)).trans ?_
      refine ((CompletedConnection.leibniz _ b _).trans ?_).trans (AdicCompletion.map_of _ _ _).symm
      refine ((congrArg (· + _) ((congrArg (b • ·) h0).trans (smul_zero b))).trans
        (zero_add _)).trans (congrArg (AdicCompletion.of _ _) ?_)
      refine Eq.trans ?_ (TensorProduct.map_tmul _ _ _ _).symm
      exact congrArg (· ⊗ₜ[R'.ring] R'.diff b) ((one_smul _ _).symm.trans (hf 1).symm) }

/-- The isomorphism `D' ≃ D ⊗̂_D D'` of the structure modules is bijective. -/
theorem baseChangeUnitHom_bijective :
    Function.Bijective (baseChangeUnitHom g hR hR').toLinearMap :=
  let : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
  (baseChangeUnitEquiv g hR').symm.bijective

end BaseChange

/-! ### The complex of the structure module is the de Rham complex -/

section OfDividedPowers

variable (p) (A : Type u) [CommRing A] {B : Type u} [CommRing B] [Algebra A B] {J : Ideal B}
  (hJ : DividedPowers J)

local notation "R₀" => ofDividedPowers p A hJ

/-- The completion `B̂` is `p`-adically complete over itself. -/
theorem isPAdicallyComplete_ofDividedPowers : IsPAdicallyComplete p (R₀).ring (R₀).ring :=
  isAdicComplete_adicCompletion_completion p B

/-- The completed forms `Ω̂^i_B` are `p`-adically complete over `B̂`. -/
theorem isAdicComplete_ofDividedPowers_Om (i : ℕ) :
    IsAdicComplete (pAdicIdeal (A := (R₀).ring) p) ((R₀).Om i) :=
  isAdicComplete_adicCompletion_completion p (dividedPowerDifferentialForms (A := A) hJ i)

/-- **The completed divided power de Rham complex `B̂ → Ω̂¹_B → Ω̂²_B → ⋯`** of a divided power
ring `(B, J, δ)` over `A`: the `p`-adic completions of the divided power forms of
[Stacks, Tag 07HZ] with the completed de Rham differential. -/
def formsComplex : CochainComplex AddCommGrpCat.{u} ℕ :=
  CochainComplex.of (fun i ↦ AddCommGrpCat.of ((R₀).Om i))
    (fun i ↦ AddCommGrpCat.ofHom ((R₀).deRham i))
    (fun i ↦ AddCommGrpCat.ext fun x ↦
      (isGradedExterior_completedDividedPower p A hJ).deRham_deRham i x)

/-- The degree `i` term of the completed divided power de Rham complex is `Ω̂^i_B`. -/
theorem formsComplex_X (i : ℕ) :
    (formsComplex p A hJ).X i = AddCommGrpCat.of (completedDividedPowerForms p A hJ i) := rfl

/-- The differential of the completed divided power de Rham complex is the completed de Rham
differential. -/
theorem formsComplex_d (i : ℕ) (x : (R₀).Om i) :
    (formsComplex p A hJ).d i (i + 1) x = (R₀).deRham i x := by
  simp only [formsComplex, CochainComplex.of, CochainComplex.of_d]
  rfl

/-- The degree `i` term of `D ⊗^∧_D Ω^*_D` for the structure module `D` is `Ω̂^i`:
`D ⊗̂_D Ω̂^i ≅ (Ω̂^i)^∧ ≅ Ω̂^i`. -/
def unitTermEquiv (i : ℕ) :
    CompletedTensor p (R₀).ring ((R₀).Om i) (R₀).ring ≃+ (R₀).Om i :=
  haveI := isAdicComplete_ofDividedPowers_Om p A hJ i
  (AdicCompletion.congr _ (TensorProduct.lid (R₀).ring ((R₀).Om i))).toAddEquiv.trans
    (AdicCompletion.ofLinearEquiv (pAdicIdeal (A := (R₀).ring) p) ((R₀).Om i)).symm.toAddEquiv

/-- The identification `D ⊗̂_D Ω̂^i ≅ Ω̂^i` sends `r ⊗ ω` to `r ω`. -/
theorem unitTermEquiv_tmul (i : ℕ) (r : (R₀).ring) (ω : (R₀).Om i) :
    unitTermEquiv p A hJ i (toCompletedTensor p _ _ _ (r ⊗ₜ ω)) = r • ω := by
  have := isAdicComplete_ofDividedPowers_Om p A hJ i
  exact ofLinearEquiv_symm_congr_of _ (TensorProduct.lid (R₀).ring ((R₀).Om i)) (r ⊗ₜ ω)

/-- **The identification `D ⊗̂_D Ω̂^i ≅ Ω̂^i` carries the differential of the structure module to
the de Rham differential**: on `r ⊗ ω` the former is `1 ⊗ (ω ∧ d r) + r ⊗ d ω`, which is
`d (r ω)` by the Leibniz rule. -/
theorem unitTermEquiv_differential (i : ℕ)
    (x : CompletedTensor p (R₀).ring ((R₀).Om i) (R₀).ring) :
    unitTermEquiv p A hJ (i + 1)
        (CompletedDeRham.differential p (R₀).ring (R₀).Om (R₀).wedge (R₀).deRham (R₀).ring
          (R₀).unitNabla (R₀).isGradedLeibniz i x) =
      (R₀).deRham i (unitTermEquiv p A hJ i x) := by
  let F := (unitTermEquiv p A hJ (i + 1)).toAddMonoidHom.comp
    (CompletedDeRham.differential p (R₀).ring (R₀).Om (R₀).wedge (R₀).deRham (R₀).ring
      (R₀).unitNabla (R₀).isGradedLeibniz i)
  let G := ((R₀).deRham i).comp (unitTermEquiv p A hJ i).toAddMonoidHom
  have hFG : F = G := by
    refine completedTensor_addMonoidHom_ext p fun r ω ↦ ?_
    change unitTermEquiv p A hJ (i + 1) (CompletedDeRham.differential p _ _ _ _ _ _ _ i
        (toCompletedTensor p _ _ _ (r ⊗ₜ ω))) =
      (R₀).deRham i (unitTermEquiv p A hJ i (toCompletedTensor p _ _ _ (r ⊗ₜ ω)))
    rw [CompletedDeRham.differential_of_tmul, unitNabla_apply, CompletedDeRham.wedgeMap_of_tmul,
      map_add, unitTermEquiv_tmul, unitTermEquiv_tmul, unitTermEquiv_tmul, one_smul,
      (R₀).isGradedLeibniz i r ω]
    exact add_comm _ _
  exact DFunLike.congr_fun hFG x

/-- **The complex `D ⊗^∧_D Ω^*_D` of the structure module of `B̂` is the completed divided power de
Rham complex of `B`.** -/
def unitComplexIso :
    ((R₀).unitConnModule (isPAdicallyComplete_ofDividedPowers p A hJ)).complex ≅
      formsComplex p A hJ :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ (unitTermEquiv p A hJ i).toAddCommGrpIso)
    (by
      rintro i j (rfl : i + 1 = j)
      refine AddCommGrpCat.ext fun x ↦ ?_
      change (formsComplex p A hJ).d i (i + 1) (unitTermEquiv p A hJ i x) =
        unitTermEquiv p A hJ (i + 1) (((R₀).unitConnModule
          (isPAdicallyComplete_ofDividedPowers p A hJ)).complex.d i (i + 1) x)
      refine (formsComplex_d p A hJ i _).trans ?_
      refine (unitTermEquiv_differential p A hJ i x).symm.trans ?_
      congr 1
      simp only [ConnModule.complex, CompletedDeRham.complex, CochainComplex.of,
        CochainComplex.of_d]
      rfl)

end OfDividedPowers

end FormsData

end Crystalline

end
