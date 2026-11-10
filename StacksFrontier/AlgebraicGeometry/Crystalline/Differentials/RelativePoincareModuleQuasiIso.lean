module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativePoincareModule

/-!
# The crystalline Poincaré lemma for a module with an integrable connection

This module proves the first clause of [Stacks, Lemma 60.19.2, Tag 07LD],
`Crystalline.DividedPowerPolynomial.quasiIso_polyDeRhamComparison`: for a divided power ring
`(B, I, δ)` over `A`, the divided power polynomial ring `P = B⟨x_w : w ∈ W⟩` on an arbitrary family
of variables, and a `B`-module `M` with an integrable connection, the canonical map of de Rham
complexes `M ⊗_B Ω^*_{B/A,δ} ⟶ M ⊗_P Ω^*_{P/A,δ}` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/RelativePoincareModule.lean` is a
quasi-isomorphism.

## The argument

The terms `(P ⊗_B M) ⊗_P Ω^n_{P/A,δ}` of the target are rewritten as `M ⊗_B Ω^n_{P/A,δ}`, where
the differential is `m ⊗ ω ↦ ψ(∇ m) ∧ ω + m ⊗ d ω`.  Splitting `d = d_rel + d_base` on the forms
of `P`, `1_M ⊗ d_rel` is contracted onto `M ⊗_B Ω^*_{B/A,δ}` by `1_M ⊗ h`, `h` the relative
Poincaré homotopy, as a special deformation retract; the remaining part of the differential raises
the number of coefficient differentials, so composed with `1_M ⊗ h` it is nilpotent in each
degree.  The basic perturbation lemma
`Crystalline.FinitePerturbation.exists_homotopyEquivOfInclusion_of_chainMap` then gives a
retraction of `1_M ⊗ ψ` which is a map of complexes and a homotopy from the other composite to the
identity.  This is done once abstractly, for any graded module with such data, and then
instantiated at the forms of `P`.  The homotopy and the retraction are additive, so the
conclusion is read on the underlying complexes of abelian groups, where the forgetful functor
reflects quasi-isomorphisms.

The source runs the spectral sequence of the filtration by the number of coefficient
differentials instead; the filtration is finite in each degree, which is what makes the
perturbation series finite here.

## Main results

* `Crystalline.DividedPowerPolynomial.quasiIso_polyDeRhamComparison` — the first clause of
  [Stacks, Tag 07LD].
* `Crystalline.DividedPowerPolynomial.stacks07LD` — **[Stacks, Tag 07LD]**, both clauses.

## References

* [Stacks Project, Lemma 60.19.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
-/

open CategoryTheory
open DividedPowers
open scoped TensorProduct
open Stacks.DeRham.DifferentialDescent

universe u w

noncomputable section

namespace Crystalline

namespace DividedPowerPolynomial

section Formulas

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A B] (W : Type u)
  {M : Type w} [AddCommGroup M] [Module (B : Type u) M]

/-- Cancelling the base change after wedging the base-changed values of a one-form with `ω`
is tensoring with the wedge `polyWedgeOne`. -/
private theorem polyCancel_map_baseChangeValues (p : ℕ)
    (omega : dividedPowerPolynomialForms A B W p)
    (z : M ⊗[(B : Type u)] dividedPowerDifferentials (A := A) B.dividedPowers) :
    polyCancel A B W M (p + 1) (TensorProduct.map LinearMap.id ((leftWedge p).flip omega)
        (Connection.baseChangeValues (oneFormComparison A B W) z)) =
      LinearMap.lTensor M (polyWedgeOne A B W p omega) z := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul m' eta =>
    calc polyCancel A B W M (p + 1) (TensorProduct.map LinearMap.id ((leftWedge p).flip omega)
          (Connection.baseChangeValues (oneFormComparison A B W) (m' ⊗ₜ eta)))
        = polyCancel A B W M (p + 1)
            (((1 : setIndexedDividedPowerPolynomialAlgebra B W) ⊗ₜ[(B : Type u)] m') ⊗ₜ
              leftWedge p (oneFormComparison A B W eta) omega) := rfl
      _ = m' ⊗ₜ ((1 : setIndexedDividedPowerPolynomialAlgebra B W) •
            leftWedge p (oneFormComparison A B W eta) omega) := polyCancel_tmul A B W M _ _ _ _
      _ = _ :=
        congrArg (m' ⊗ₜ[(B : Type u)] ·)
          ((one_smul _ _).trans (polyWedgeOne_apply A B W p omega eta).symm)

/-- **The differential of `M ⊗_P Ω^*_{P/A,δ'}`, read with the base change cancelled**:
`∇'(m ⊗ ω) = ψ(∇ m) ∧ ω + m ⊗ d ω`. -/
private theorem polyTermEquiv_extendedConnection
    (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M) (p : ℕ) (m : M)
    (omega : dividedPowerPolynomialForms A B W p) :
    polyTermEquiv A B W M (p + 1) ((extendedConnection (polySource A B W) (polyProjection A B W)
        (Submodule.mkQ_surjective _) (polyGenerationHypothesis A B W)
        (polyBaseChangeConnection A B W nabla)).toLinearMap p
          ((polyTermEquiv A B W M p).symm (m ⊗ₜ omega))) =
      LinearMap.lTensor M (polyWedgeOne A B W p omega) (nabla m) +
        m ⊗ₜ dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) p omega := by
  have hmt := (extendedConnection (polySource A B W) (polyProjection A B W)
    (Submodule.mkQ_surjective _) (polyGenerationHypothesis A B W)
    (polyBaseChangeConnection A B W nabla)).map_tmul p
    ((1 : setIndexedDividedPowerPolynomialAlgebra B W) ⊗ₜ[(B : Type u)] m) omega
  have hd : RestrictScalars.addEquiv A (setIndexedDividedPowerPolynomialAlgebra B W) _
      ((extendedConnection (polySource A B W) (polyProjection A B W)
        (Submodule.mkQ_surjective _) (polyGenerationHypothesis A B W)
        (polyBaseChangeConnection A B W nabla)).deRhamDifferential p omega) =
      dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) p omega := by
    rw [extendedConnection_deRhamDifferential]
    rfl
  calc polyTermEquiv A B W M (p + 1) ((extendedConnection (polySource A B W) (polyProjection A B W)
        (Submodule.mkQ_surjective _) (polyGenerationHypothesis A B W)
        (polyBaseChangeConnection A B W nabla)).toLinearMap p
          ((polyTermEquiv A B W M p).symm (m ⊗ₜ omega)))
      = polyCancel A B W M (p + 1) (RestrictScalars.addEquiv A _ _
          ((extendedConnection (polySource A B W) (polyProjection A B W)
            (Submodule.mkQ_surjective _) (polyGenerationHypothesis A B W)
            (polyBaseChangeConnection A B W nabla)).toLinearMap p
              ((1 : setIndexedDividedPowerPolynomialAlgebra B W) ⊗ₜ[(B : Type u)] m ⊗ₜ
                omega))) := rfl
    _ = polyCancel A B W M (p + 1) (TensorProduct.map LinearMap.id ((leftWedge p).flip omega)
            (polyBaseChangeConnection A B W nabla
              ((1 : setIndexedDividedPowerPolynomialAlgebra B W) ⊗ₜ[(B : Type u)] m)) +
          ((1 : setIndexedDividedPowerPolynomialAlgebra B W) ⊗ₜ[(B : Type u)] m) ⊗ₜ
            RestrictScalars.addEquiv A (setIndexedDividedPowerPolynomialAlgebra B W) _
              ((extendedConnection (polySource A B W) (polyProjection A B W)
                (Submodule.mkQ_surjective _) (polyGenerationHypothesis A B W)
                (polyBaseChangeConnection A B W nabla)).deRhamDifferential p omega)) :=
        congrArg (polyCancel A B W M (p + 1)) hmt
    _ = polyCancel A B W M (p + 1) (TensorProduct.map LinearMap.id ((leftWedge p).flip omega)
            (Connection.baseChangeValues (oneFormComparison A B W) (nabla m))) +
          m ⊗ₜ ((1 : setIndexedDividedPowerPolynomialAlgebra B W) •
          dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) p omega) :=
        (map_add (polyCancel A B W M (p + 1)) _ _).trans (congrArg₂ (· + ·)
          (congrArg (fun z ↦ polyCancel A B W M (p + 1)
            (TensorProduct.map LinearMap.id ((leftWedge p).flip omega) z))
            (polyBaseChangeConnection_one_tmul A B W nabla m))
          ((congrArg (fun z ↦ polyCancel A B W M (p + 1)
            (((1 : setIndexedDividedPowerPolynomialAlgebra B W) ⊗ₜ[(B : Type u)] m) ⊗ₜ z)) hd).trans
            (polyCancel_tmul A B W M _ _ _ _)))
    _ = _ := congrArg₂ (· + ·) (polyCancel_map_baseChangeValues A B W p omega (nabla m))
          (congrArg (m ⊗ₜ[(B : Type u)] ·) (one_smul _ _))

end Formulas

/-! ### The form-level maps, read `B`-linearly -/

section FormMaps

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A B] (W : Type u)
  [LinearOrder W]

/-- The relative Poincaré homotopy `h`, as a `B`-linear map. -/
private def relHomB (n : ℕ) :
    dividedPowerPolynomialForms A B W (n + 1) →ₗ[(B : Type u)] dividedPowerPolynomialForms A B W n
    where
  toFun := relativeFormsHomotopy A B W n
  map_add' := map_add _
  map_smul' := relativeFormsHomotopy_smul A B W n

/-- The coefficient retraction `ε`, as a `B`-linear map. -/
private def retrB (n : ℕ) :
    dividedPowerPolynomialForms A B W n →ₗ[(B : Type u)]
      dividedPowerDifferentialForms (A := A) B.dividedPowers n where
  toFun := relativeFormsRetraction A B W n
  map_add' := map_add _
  map_smul' := relativeFormsRetraction_smul A B W n

/-- The bidegree projection, as a `B`-linear map. -/
private def projB (n i : ℕ) :
    dividedPowerPolynomialForms A B W n →ₗ[(B : Type u)] dividedPowerPolynomialForms A B W n where
  toFun := formsBidegreeProjection A B W n i
  map_add' := map_add _
  map_smul' := formsBidegreeProjection_smul A B W n i

/-- Wedging with a one-form of `B` and projecting to a coefficient degree at most that of the
other factor gives zero. -/
private theorem projB_comp_polyWedgeOne (n l i : ℕ) (hli : l ≤ i)
    (omega : dividedPowerPolynomialForms A B W n) :
    projB A B W (n + 1) l ∘ₗ polyWedgeOne A B W n (formsBidegreeProjection A B W n i omega) =
      0 := by
  refine LinearMap.ext fun eta ↦ ?_
  have h11 := formsBidegreeProjection_coefficientFormsMap A B W 1 1
    ((exteriorPower.oneEquiv (B : Type u) _).symm eta)
  rw [ite_eq_left rfl] at h11
  change formsBidegreeProjection A B W (n + 1) l
      (dividedPowerWedge (setIndexedDividedPowerPolynomialDividedPowers B W) n
        (formsBidegreeProjection A B W n i omega)
        (coefficientFormsMap A B W 1 ((exteriorPower.oneEquiv (B : Type u) _).symm eta))) = 0
  rw [← h11]
  exact formsBidegreeProjection_wedge_formsBidegreeProjection_eq_zero A B W n l i hli omega _

end FormMaps

/-! ### The data of the perturbation argument -/

section Perturbation

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A B] (W : Type u)
  {M : Type w} [AddCommGroup M] [Module (B : Type u) M]
  (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)

/-- **The differential of `M ⊗_P Ω^*_{P/A,δ'}`, transported to `M ⊗_B Ω^*_{P/A,δ'}`.** -/
private def dC (n : ℕ) :
    M ⊗[(B : Type u)] dividedPowerPolynomialForms A B W n →+
      M ⊗[(B : Type u)] dividedPowerPolynomialForms A B W (n + 1) :=
  (polyTermEquiv A B W M (n + 1)).toAddMonoidHom.comp
    (((extendedConnection (polySource A B W) (polyProjection A B W)
      (Submodule.mkQ_surjective _) (polyGenerationHypothesis A B W)
      (polyBaseChangeConnection A B W nabla)).toLinearMap n).toAddMonoidHom.comp
      (polyTermEquiv A B W M n).symm.toAddMonoidHom)

/-- The extended connection of the base change, read with the base change cancelled, is `dC`. -/
private theorem polyTermEquiv_extendedConnection_apply (n : ℕ)
    (y : polyTargetTerm A B W M n) :
    polyTermEquiv A B W M (n + 1) ((extendedConnection (polySource A B W) (polyProjection A B W)
        (Submodule.mkQ_surjective _) (polyGenerationHypothesis A B W)
        (polyBaseChangeConnection A B W nabla)).toLinearMap n y) =
      dC A B W nabla n (polyTermEquiv A B W M n y) :=
  congrArg (fun z ↦ polyTermEquiv A B W M (n + 1) ((extendedConnection (polySource A B W)
    (polyProjection A B W) (Submodule.mkQ_surjective _) (polyGenerationHypothesis A B W)
    (polyBaseChangeConnection A B W nabla)).toLinearMap n z))
    ((polyTermEquiv A B W M n).symm_apply_apply y).symm

private theorem dC_tmul (n : ℕ) (m : M) (omega : dividedPowerPolynomialForms A B W n) :
    dC A B W nabla n (m ⊗ₜ omega) =
      LinearMap.lTensor M (polyWedgeOne A B W n omega) (nabla m) +
        m ⊗ₜ dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n omega :=
  polyTermEquiv_extendedConnection A B W nabla n m omega

private theorem dC_dC
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla)
    (n : ℕ) (x : M ⊗[(B : Type u)] dividedPowerPolynomialForms A B W n) :
    dC A B W nabla (n + 1) (dC A B W nabla n x) = 0 := by
  have h := LinearMap.congr_fun (extendedConnection_comp_self_eq_zero (polySource A B W)
    (polyProjection A B W) (Submodule.mkQ_surjective _) (polyGenerationHypothesis A B W)
    (polyBaseChangeConnection A B W nabla)
    (polyBaseChangeConnection_isIntegrable A B W nabla hint) n) ((polyTermEquiv A B W M n).symm x)
  exact (polyTermEquiv_extendedConnection_apply A B W nabla (n + 1) _).symm.trans
    ((congrArg (polyTermEquiv A B W M (n + 1 + 1)) h).trans (map_zero _))

end Perturbation

/-! ### The perturbation argument for a module, abstractly -/

section Abstract

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Module R (X n)]
  {Y : ℕ → Type*} [∀ n, AddCommGroup (Y n)] [∀ n, Module R (Y n)]
  {Om : Type*} [AddCommGroup Om] [Module R Om]

/-- `1_M ⊗ g` after `1_M ⊗ f` is `1_M ⊗ (g ∘ f)`. -/
private theorem lTensor_lTensor_apply {P Q S : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] [AddCommGroup S] [Module R S] (f : P →ₗ[R] Q) (g : Q →ₗ[R] S)
    (x : M ⊗[R] P) :
    LinearMap.lTensor M g (LinearMap.lTensor M f x) = LinearMap.lTensor M (g ∘ₗ f) x := by
  rw [LinearMap.lTensor_comp, LinearMap.comp_apply]

/-- `1_M ⊗ g` kills `1_M ⊗ f` as soon as `g ∘ f = 0`. -/
private theorem lTensor_lTensor_eq_zero' {P Q S : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] [AddCommGroup S] [Module R S] (f : P →ₗ[R] Q) (g : Q →ₗ[R] S)
    (hgf : ∀ p, g (f p) = 0) (x : M ⊗[R] P) :
    LinearMap.lTensor M g (LinearMap.lTensor M f x) = 0 := by
  have e : g ∘ₗ f = 0 := LinearMap.ext hgf
  rw [lTensor_lTensor_apply, e, LinearMap.lTensor_zero, LinearMap.zero_apply]

/-- `1_M ⊗ g` undoes `1_M ⊗ f` as soon as `g` undoes `f`. -/
private theorem lTensor_lTensor_eq_self {P Q : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (f : P →ₗ[R] Q) (g : Q →ₗ[R] P) (hgf : ∀ p, g (f p) = p)
    (x : M ⊗[R] P) : LinearMap.lTensor M g (LinearMap.lTensor M f x) = x := by
  have e : g ∘ₗ f = LinearMap.id := LinearMap.ext hgf
  rw [lTensor_lTensor_apply, e, LinearMap.lTensor_id, LinearMap.id_apply]

/-- A decomposition `g ∘ f + g' ∘ f' = 1` of the identity survives `1_M ⊗ -`. -/
private theorem lTensor_add_lTensor_eq_self {P Q S : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] [AddCommGroup S] [Module R S] (f : P →ₗ[R] Q) (g : Q →ₗ[R] P)
    (f' : P →ₗ[R] S) (g' : S →ₗ[R] P) (h : ∀ p, g (f p) + g' (f' p) = p) (x : M ⊗[R] P) :
    LinearMap.lTensor M g (LinearMap.lTensor M f x) +
      LinearMap.lTensor M g' (LinearMap.lTensor M f' x) = x := by
  have e : g ∘ₗ f + g' ∘ₗ f' = LinearMap.id := LinearMap.ext h
  rw [lTensor_lTensor_apply, lTensor_lTensor_apply, ← LinearMap.add_apply,
    ← LinearMap.lTensor_add, e, LinearMap.lTensor_id, LinearMap.id_apply]

/-- A decomposition `g ∘ f + g' ∘ f' + g'' ∘ f'' = 1` of the identity survives `1_M ⊗ -`. -/
private theorem lTensor_add_lTensor_add_lTensor_eq_self {P Q S T : Type*} [AddCommGroup P]
    [Module R P] [AddCommGroup Q] [Module R Q] [AddCommGroup S] [Module R S] [AddCommGroup T]
    [Module R T] (f : P →ₗ[R] Q) (g : Q →ₗ[R] P) (f' : P →ₗ[R] S) (g' : S →ₗ[R] P)
    (f'' : P →ₗ[R] T) (g'' : T →ₗ[R] P) (h : ∀ p, g (f p) + g' (f' p) + g'' (f'' p) = p)
    (x : M ⊗[R] P) :
    LinearMap.lTensor M g (LinearMap.lTensor M f x) +
      LinearMap.lTensor M g' (LinearMap.lTensor M f' x) +
        LinearMap.lTensor M g'' (LinearMap.lTensor M f'' x) = x := by
  have e : g ∘ₗ f + g' ∘ₗ f' + g'' ∘ₗ f'' = LinearMap.id := LinearMap.ext h
  rw [lTensor_lTensor_apply, lTensor_lTensor_apply, lTensor_lTensor_apply,
    ← LinearMap.add_apply, ← LinearMap.add_apply, ← LinearMap.lTensor_add,
    ← LinearMap.lTensor_add, e, LinearMap.lTensor_id, LinearMap.id_apply]

/-- `1_M ⊗ -` commutes with finite sums of maps. -/
private theorem lTensor_sum_apply {ι P Q : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (s : Finset ι) (f : ι → P →ₗ[R] Q) (x : M ⊗[R] P) :
    ∑ i ∈ s, LinearMap.lTensor M (f i) x = LinearMap.lTensor M (∑ i ∈ s, f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, LinearMap.lTensor_zero, LinearMap.zero_apply]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, LinearMap.lTensor_add,
      LinearMap.add_apply]

/-- The perturbation `dC - 1_M ⊗ rel` raises the coefficient degree. -/
private theorem lTensor_proj_perturbation_eq_zero {rel : ∀ n, X n →ₗ[R] X (n + 1)}
    {base : ∀ n, X n →+ X (n + 1)} {proj : ∀ n, ℕ → X n →ₗ[R] X n}
    {wedgeOne : ∀ n, X n → Om →ₗ[R] X (n + 1)} {nabla : M →+ M ⊗[R] Om}
    {dC : ∀ n, M ⊗[R] X n →+ M ⊗[R] X (n + 1)}
    (hdC : ∀ (n : ℕ) (m : M) (ω : X n),
      dC n (m ⊗ₜ ω) = LinearMap.lTensor M (wedgeOne n ω) (nabla m) + m ⊗ₜ (rel n ω + base n ω))
    (hprojbase : ∀ (n l i : ℕ), l ≤ i → ∀ ω : X n, proj (n + 1) l (base n (proj n i ω)) = 0)
    (hprojwedge : ∀ (n l i : ℕ), l ≤ i → ∀ ω : X n,
      proj (n + 1) l ∘ₗ wedgeOne n (proj n i ω) = 0)
    (n l i : ℕ) (hli : l ≤ i) (x : M ⊗[R] X n) :
    LinearMap.lTensor M (proj (n + 1) l) ((dC n - (LinearMap.lTensor M (rel n)).toAddMonoidHom)
      (LinearMap.lTensor M (proj n i) x)) = 0 := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb, add_zero]
  | tmul m ω =>
    change LinearMap.lTensor M (proj (n + 1) l) (dC n (m ⊗ₜ proj n i ω) -
      LinearMap.lTensor M (rel n) (m ⊗ₜ proj n i ω)) = 0
    rw [hdC, LinearMap.lTensor_tmul, add_sub_assoc, TensorProduct.tmul_add, add_sub_cancel_left,
      map_add, lTensor_lTensor_apply, hprojwedge n l i hli ω, LinearMap.lTensor_zero,
      LinearMap.zero_apply, zero_add, LinearMap.lTensor_tmul, hprojbase n l i hli ω,
      TensorProduct.tmul_zero]

/-- The composite of the perturbation `dC - 1_M ⊗ rel` with `1_M ⊗ hh` is nilpotent in each
degree. -/
private theorem iterate_perturbation_eq_zero {rel : ∀ n, X n →ₗ[R] X (n + 1)}
    {base : ∀ n, X n →+ X (n + 1)} {hh : ∀ n, X (n + 1) →ₗ[R] X n}
    {proj : ∀ n, ℕ → X n →ₗ[R] X n} {wedgeOne : ∀ n, X n → Om →ₗ[R] X (n + 1)}
    {nabla : M →+ M ⊗[R] Om} {dC : ∀ n, M ⊗[R] X n →+ M ⊗[R] X (n + 1)}
    (hdC : ∀ (n : ℕ) (m : M) (ω : X n),
      dC n (m ⊗ₜ ω) = LinearMap.lTensor M (wedgeOne n ω) (nabla m) + m ⊗ₜ (rel n ω + base n ω))
    (hprojsum : ∀ (n : ℕ) (ω : X n), ∑ i ∈ Finset.range (n + 1), proj n i ω = ω)
    (hprojh : ∀ (n i : ℕ) (ω : X (n + 1)), hh n (proj (n + 1) i ω) = proj n i (hh n ω))
    (hprojbase : ∀ (n l i : ℕ), l ≤ i → ∀ ω : X n, proj (n + 1) l (base n (proj n i ω)) = 0)
    (hprojwedge : ∀ (n l i : ℕ), l ≤ i → ∀ ω : X n,
      proj (n + 1) l ∘ₗ wedgeOne n (proj n i ω) = 0)
    (n : ℕ) (x : M ⊗[R] X (n + 1)) :
    (fun y ↦ (dC n - (LinearMap.lTensor M (rel n)).toAddMonoidHom)
      (LinearMap.lTensor M (hh n) y))^[n + 2] x = 0 := by
  let projT : ℕ → M ⊗[R] X (n + 1) →+ M ⊗[R] X (n + 1) :=
    fun i ↦ (LinearMap.lTensor M (proj (n + 1) i)).toAddMonoidHom
  have e : ∑ i ∈ Finset.range (n + 2), proj (n + 1) i = LinearMap.id :=
    LinearMap.ext fun ω ↦ (LinearMap.sum_apply _ _ ω).trans (hprojsum (n + 1) ω)
  refine DividedPowerPolynomial.iterate_eq_zero_of_raisesProjectionDegree (n + 2) projT
    ((dC n - (LinearMap.lTensor M (rel n)).toAddMonoidHom).comp
      (LinearMap.lTensor M (hh n)).toAddMonoidHom) (fun y ↦ ?_) (fun l j hlj y ↦ ?_) x
  · change ∑ i ∈ Finset.range (n + 2), LinearMap.lTensor M (proj (n + 1) i) y = y
    rw [lTensor_sum_apply, e, LinearMap.lTensor_id, LinearMap.id_apply]
  · have e' : hh n ∘ₗ proj (n + 1) j = proj n j ∘ₗ hh n := LinearMap.ext (hprojh n j)
    change LinearMap.lTensor M (proj (n + 1) l)
      ((dC n - (LinearMap.lTensor M (rel n)).toAddMonoidHom)
        (LinearMap.lTensor M (hh n) (LinearMap.lTensor M (proj (n + 1) j) y))) = 0
    rw [lTensor_lTensor_apply, e', ← lTensor_lTensor_apply]
    exact lTensor_proj_perturbation_eq_zero hdC hprojbase hprojwedge n l j hlj _

/-- **The perturbation argument for `M ⊗ X^*` with a connection, abstractly.**  `X^*` carries a
splitting `d = rel + base` of its differential with `rel` linear and contracted onto `Y^*` by
`hh` as a special deformation retract (`coef`, `retr`), and bidegree projections in which `hh`
preserves the coefficient degree and `base` and the wedge with a one-form raise it.  The
differential `dC` of `M ⊗ X^*` is `m ⊗ ω ↦ ∇ m ∧ ω + m ⊗ d ω`, it squares to zero, and
`1_M ⊗ coef` is a map of complexes from `(M ⊗ Y^*, dL)`.  Then `1_M ⊗ coef` has a retraction
which is a map of complexes, and the composite the other way is homotopic to the identity. -/
private theorem exists_retraction_abstract
    (rel : ∀ n, X n →ₗ[R] X (n + 1)) (base : ∀ n, X n →+ X (n + 1))
    (hh : ∀ n, X (n + 1) →ₗ[R] X n) (coef : ∀ n, Y n →ₗ[R] X n) (retr : ∀ n, X n →ₗ[R] Y n)
    (proj : ∀ n, ℕ → X n →ₗ[R] X n) (wedgeOne : ∀ n, X n → Om →ₗ[R] X (n + 1))
    (nabla : M →+ M ⊗[R] Om)
    (dC : ∀ n, M ⊗[R] X n →+ M ⊗[R] X (n + 1)) (dL : ∀ n, M ⊗[R] Y n →+ M ⊗[R] Y (n + 1))
    (hdC : ∀ (n : ℕ) (m : M) (ω : X n),
      dC n (m ⊗ₜ ω) = LinearMap.lTensor M (wedgeOne n ω) (nabla m) + m ⊗ₜ (rel n ω + base n ω))
    (hdd : ∀ (n : ℕ) (x : M ⊗[R] X n), dC (n + 1) (dC n x) = 0)
    (hrel : ∀ (n : ℕ) (ω : X n), rel (n + 1) (rel n ω) = 0)
    (hcon0 : ∀ ω : X 0, hh 0 (rel 0 ω) + coef 0 (retr 0 ω) = ω)
    (hcon : ∀ (n : ℕ) (ω : X (n + 1)),
      rel n (hh n ω) + hh (n + 1) (rel (n + 1) ω) + coef (n + 1) (retr (n + 1) ω) = ω)
    (hhh : ∀ (n : ℕ) (ω : X (n + 2)), hh n (hh (n + 1) ω) = 0)
    (hhcoef : ∀ (n : ℕ) (y : Y (n + 1)), hh n (coef (n + 1) y) = 0)
    (hretrh : ∀ (n : ℕ) (ω : X (n + 1)), retr n (hh n ω) = 0)
    (hretrcoef : ∀ (n : ℕ) (y : Y n), retr n (coef n y) = y)
    (hchain : ∀ (n : ℕ) (y : M ⊗[R] Y n),
      dC n (LinearMap.lTensor M (coef n) y) = LinearMap.lTensor M (coef (n + 1)) (dL n y))
    (hprojsum : ∀ (n : ℕ) (ω : X n), ∑ i ∈ Finset.range (n + 1), proj n i ω = ω)
    (hprojh : ∀ (n i : ℕ) (ω : X (n + 1)), hh n (proj (n + 1) i ω) = proj n i (hh n ω))
    (hprojbase : ∀ (n l i : ℕ), l ≤ i → ∀ ω : X n, proj (n + 1) l (base n (proj n i ω)) = 0)
    (hprojwedge : ∀ (n l i : ℕ), l ≤ i → ∀ ω : X n,
      proj (n + 1) l ∘ₗ wedgeOne n (proj n i ω) = 0) :
    ∃ (pi' : ∀ n, M ⊗[R] X n →+ M ⊗[R] Y n) (H : ∀ n, M ⊗[R] X (n + 1) →+ M ⊗[R] X n),
      (∀ (n : ℕ) (y : M ⊗[R] Y n), pi' n (LinearMap.lTensor M (coef n) y) = y) ∧
        (∀ (n : ℕ) (z : M ⊗[R] X n), pi' (n + 1) (dC n z) = dL n (pi' n z)) ∧
          (∀ x : M ⊗[R] X 0,
            H 0 (dC 0 x) + LinearMap.lTensor M (coef 0) (pi' 0 x) = x) ∧
            ∀ (n : ℕ) (x : M ⊗[R] X (n + 1)),
              dC n (H n x) + H (n + 1) (dC (n + 1) x) +
                LinearMap.lTensor M (coef (n + 1)) (pi' (n + 1) x) = x := by
  let d0 : ∀ n, M ⊗[R] X n →+ M ⊗[R] X (n + 1) :=
    fun n ↦ (LinearMap.lTensor M (rel n)).toAddMonoidHom
  let t : ∀ n, M ⊗[R] X n →+ M ⊗[R] X (n + 1) := fun n ↦ dC n - d0 n
  let h : ∀ n, M ⊗[R] X (n + 1) →+ M ⊗[R] X n := fun n ↦ (LinearMap.lTensor M (hh n)).toAddMonoidHom
  let iota : ∀ n, M ⊗[R] Y n →+ M ⊗[R] X n := fun n ↦ (LinearMap.lTensor M (coef n)).toAddMonoidHom
  let pi : ∀ n, M ⊗[R] X n →+ M ⊗[R] Y n := fun n ↦ (LinearMap.lTensor M (retr n)).toAddMonoidHom
  have hcon0' : ∀ x : M ⊗[R] X 0, h 0 (d0 0 x) + iota 0 (pi 0 x) = x :=
    lTensor_add_lTensor_eq_self (rel 0) (hh 0) (retr 0) (coef 0) hcon0
  have hcon' : ∀ (n : ℕ) (x : M ⊗[R] X (n + 1)),
      d0 n (h n x) + h (n + 1) (d0 (n + 1) x) + iota (n + 1) (pi (n + 1) x) = x := fun n ↦
    lTensor_add_lTensor_add_lTensor_eq_self (hh n) (rel n) (rel (n + 1)) (hh (n + 1))
      (retr (n + 1)) (coef (n + 1)) (hcon n)
  have hpiiota : ∀ (n : ℕ) (y : M ⊗[R] Y n), pi n (iota n y) = y :=
    fun n ↦ lTensor_lTensor_eq_self (coef n) (retr n) (hretrcoef n)
  have hhiota : ∀ (n : ℕ) (y : M ⊗[R] Y (n + 1)), h n (iota (n + 1) y) = 0 :=
    fun n ↦ lTensor_lTensor_eq_zero' (coef (n + 1)) (hh n) (hhcoef n)
  have hd : ∀ (n : ℕ) (x : M ⊗[R] X n), dC n x = d0 n x + t n x := fun n x ↦ by
    change dC n x = d0 n x + (dC n x - d0 n x)
    abel
  have hd0d0 : ∀ (n : ℕ) (x : M ⊗[R] X n), d0 (n + 1) (d0 n x) = 0 :=
    fun n ↦ lTensor_lTensor_eq_zero' (rel n) (rel (n + 1)) (hrel n)
  have hcross : ∀ (n : ℕ) (x : M ⊗[R] X n), t (n + 1) (dC n x) + d0 (n + 1) (t n x) = 0 := by
    intro n x
    change dC (n + 1) (dC n x) - d0 (n + 1) (dC n x) + d0 (n + 1) (dC n x - d0 n x) = 0
    rw [map_sub, hdd, hd0d0]
    abel
  have hhd0iota : ∀ (n : ℕ) (y : M ⊗[R] Y n), h n (d0 n (iota n y)) = 0 := by
    intro n y
    cases n with
    | zero =>
      have := hcon0' (iota 0 y)
      rw [hpiiota] at this
      exact add_eq_right.mp this
    | succ n =>
      have := hcon' n (iota (n + 1) y)
      rw [hpiiota, hhiota, map_zero, zero_add] at this
      exact add_eq_right.mp this
  have hhtiota : ∀ (n : ℕ) (y : M ⊗[R] Y n), h n (t n (iota n y)) = 0 := by
    intro n y
    change h n (dC n (iota n y) - d0 n (iota n y)) = 0
    rw [map_sub, hhd0iota, sub_zero]
    change h n (dC n (LinearMap.lTensor M (coef n) y)) = 0
    rw [hchain]
    exact hhiota n (dL n y)
  have hnil : ∀ (n : ℕ) (x : M ⊗[R] X (n + 1)), (fun y ↦ t n (h n y))^[n + 2] x = 0 :=
    iterate_perturbation_eq_zero hdC hprojsum hprojh hprojbase hprojwedge
  exact FinitePerturbation.exists_homotopyEquivOfInclusion_of_chainMap d0 t dC h iota pi dL hd
    hdd hcon0' hcon' hcross (fun n x ↦ lTensor_lTensor_eq_zero' (hh (n + 1)) (hh n) (hhh n) x)
    hhiota (fun n x ↦ lTensor_lTensor_eq_zero' (hh n) (retr n) (hretrh n) x) hpiiota hhtiota
    hchain (fun n ↦ n + 2) hnil

end Abstract

/-! ### A quasi-isomorphism of complexes of modules from an additive homotopy inverse -/

section QuasiIsoOfRetraction

/-- **A map of complexes of modules with an additive homotopy inverse is a quasi-isomorphism.**
If `f : K ⟶ L` has additive maps `g_i : L^i → K^i` back, commuting with the differentials, with
`g ∘ f = 1` and `f ∘ g` homotopic to the identity through additive maps `H`, then `f` is a
quasi-isomorphism: forgetting to abelian groups, `f` becomes a homotopy equivalence, and the
forgetful functor preserves and reflects homology isomorphisms. -/
private theorem quasiIso_of_additiveRetraction {R : Type*} [Ring R]
    {K L : CochainComplex (ModuleCat.{w} R) ℕ} (f : K ⟶ L) (g : ∀ i, L.X i →+ K.X i)
    (H : ∀ i, L.X (i + 1) →+ L.X i)
    (hgf : ∀ (i : ℕ) (x : K.X i), g i ((f.f i).hom x) = x)
    (hg : ∀ (i : ℕ) (y : L.X i), g (i + 1) ((L.d i (i + 1)).hom y) = (K.d i (i + 1)).hom (g i y))
    (h0 : ∀ y : L.X 0, H 0 ((L.d 0 (0 + 1)).hom y) + (f.f 0).hom (g 0 y) = y)
    (hs : ∀ (n : ℕ) (y : L.X (n + 1)),
      (L.d n (n + 1)).hom (H n y) + H (n + 1) ((L.d (n + 1) (n + 1 + 1)).hom y) +
        (f.f (n + 1)).hom (g (n + 1) y) = y) :
    QuasiIso f := by
  let F := forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology f F]
  let K' := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  let L' := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj L
  let inv : L' ⟶ K' :=
    { f := fun i ↦ AddCommGrpCat.ofHom (g i)
      comm' := fun i j hij ↦ by
        obtain rfl : i + 1 = j := hij
        exact AddCommGrpCat.ext fun y ↦ (hg i y).symm }
  let e : HomotopyEquiv K' L' :=
    { hom := (F.mapHomologicalComplex (ComplexShape.up ℕ)).map f
      inv := inv
      homotopyHomInvId := Homotopy.ofEq (HomologicalComplex.hom_ext _ _ fun i ↦
        AddCommGrpCat.ext fun x ↦ hgf i x)
      homotopyInvHomId := (cochainHomotopyOfDegreewise
        (fun i ↦ AddCommGrpCat.ofHom (H i))
        (AddCommGrpCat.ext fun y ↦ (h0 y).symm)
        (fun n ↦ AddCommGrpCat.ext fun y ↦ by
          change y = H (n + 1) ((L.d (n + 1) (n + 1 + 1)).hom y) +
            (L.d n (n + 1)).hom (H n y) + (f.f (n + 1)).hom (g (n + 1) y)
          rw [add_comm (H (n + 1) _)]
          exact (hs n y).symm)).symm }
  exact e.quasiIso_hom

end QuasiIsoOfRetraction

/-! ### The perturbation argument at the divided power polynomial algebra -/

section Instance

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A B] (W : Type u)
  {M : Type w} [AddCommGroup M] [Module (B : Type u) M]
  (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
  (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
    (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla)

/-- The differential of `M ⊗_B Ω^*_{B/A,δ}`, without the restriction of scalars. -/
private def dL (n : ℕ) :
    M ⊗[(B : Type u)] dividedPowerDifferentialForms (A := A) B.dividedPowers n →+
      M ⊗[(B : Type u)] dividedPowerDifferentialForms (A := A) B.dividedPowers (n + 1) :=
  (baseTermEquiv A B M (n + 1)).toAddMonoidHom.comp
    (((extendedConnection (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla).toLinearMap
        n).toAddMonoidHom.comp (baseTermEquiv A B M n).symm.toAddMonoidHom)

include hint in
/-- `1_M ⊗ ψ` is a map of complexes, read with the base change cancelled. -/
private theorem dC_lTensor_coefficientFormsMap (n : ℕ)
    (y : M ⊗[(B : Type u)] dividedPowerDifferentialForms (A := A) B.dividedPowers n) :
    dC A B W nabla n (LinearMap.lTensor M (coefficientFormsMap A B W n) y) =
      LinearMap.lTensor M (coefficientFormsMap A B W (n + 1)) (dL A B nabla n y) := by
  let E' := extendedConnection (polySource A B W) (polyProjection A B W)
    (Submodule.mkQ_surjective _) (polyGenerationHypothesis A B W)
    (polyBaseChangeConnection A B W nabla)
  let E := extendedConnection (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
    (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla
  let c := polyComparison A B W nabla hint
  calc dC A B W nabla n (LinearMap.lTensor M (coefficientFormsMap A B W n) y)
      = dC A B W nabla n (polyTermEquiv A B W M n (c n ((baseTermEquiv A B M n).symm y))) :=
        congrArg (dC A B W nabla n) (polyTermEquiv_polyComparison A B W nabla hint n y).symm
    _ = polyTermEquiv A B W M (n + 1) ((E'.toLinearMap n) (c n ((baseTermEquiv A B M n).symm y))) :=
        (polyTermEquiv_extendedConnection_apply A B W nabla n _).symm
    _ = polyTermEquiv A B W M (n + 1) (c (n + 1) ((E.toLinearMap n)
          ((baseTermEquiv A B M n).symm y))) :=
        congrArg (polyTermEquiv A B W M (n + 1))
          (polyComparison_comm A B W nabla hint n ((baseTermEquiv A B M n).symm y)).symm
    _ = polyTermEquiv A B W M (n + 1) (c (n + 1) ((baseTermEquiv A B M (n + 1)).symm
          (baseTermEquiv A B M (n + 1) ((E.toLinearMap n) ((baseTermEquiv A B M n).symm y))))) :=
        congrArg (fun z ↦ polyTermEquiv A B W M (n + 1) (c (n + 1) z))
          ((baseTermEquiv A B M (n + 1)).symm_apply_apply _).symm
    _ = LinearMap.lTensor M (coefficientFormsMap A B W (n + 1)) (dL A B nabla n y) :=
        polyTermEquiv_polyComparison A B W nabla hint (n + 1) _

include hint in
/-- **The perturbation argument at the divided power polynomial algebra**: with the base change
cancelled, `1_M ⊗ ψ : M ⊗_B Ω^*_{B/A,δ} → M ⊗_B Ω^*_{P/A,δ'}` has a retraction which is a map of
complexes, and the composite the other way is homotopic to the identity. -/
private theorem exists_retraction_poly [LinearOrder W] :
    ∃ (pi' : ∀ n, M ⊗[(B : Type u)] dividedPowerPolynomialForms A B W n →+
        M ⊗[(B : Type u)] dividedPowerDifferentialForms (A := A) B.dividedPowers n)
      (H : ∀ n, M ⊗[(B : Type u)] dividedPowerPolynomialForms A B W (n + 1) →+
        M ⊗[(B : Type u)] dividedPowerPolynomialForms A B W n),
      (∀ (n : ℕ) (y : M ⊗[(B : Type u)] dividedPowerDifferentialForms (A := A) B.dividedPowers n),
          pi' n (LinearMap.lTensor M (coefficientFormsMap A B W n) y) = y) ∧
        (∀ (n : ℕ) (z : M ⊗[(B : Type u)] dividedPowerPolynomialForms A B W n),
            pi' (n + 1) (dC A B W nabla n z) = dL A B nabla n (pi' n z)) ∧
          (∀ x : M ⊗[(B : Type u)] dividedPowerPolynomialForms A B W 0,
            H 0 (dC A B W nabla 0 x) +
              LinearMap.lTensor M (coefficientFormsMap A B W 0) (pi' 0 x) = x) ∧
            ∀ (n : ℕ) (x : M ⊗[(B : Type u)] dividedPowerPolynomialForms A B W (n + 1)),
              dC A B W nabla n (H n x) + H (n + 1) (dC A B W nabla (n + 1) x) +
                LinearMap.lTensor M (coefficientFormsMap A B W (n + 1)) (pi' (n + 1) x) = x :=
  exists_retraction_abstract (R := (B : Type u)) (M := M)
    (X := dividedPowerPolynomialForms A B W)
    (Y := fun n ↦ dividedPowerDifferentialForms (A := A) B.dividedPowers n)
    (Om := dividedPowerDifferentials (A := A) B.dividedPowers)
    (formsRelDifferential A B W) (fun n ↦ (formsBaseDifferential A B W n).toAddMonoidHom)
    (relHomB A B W) (coefficientFormsMap A B W) (retrB A B W) (projB A B W)
    (polyWedgeOne A B W) nabla.toAddMonoidHom (dC A B W nabla) (dL A B nabla)
    (fun n m ω ↦ (dC_tmul A B W nabla n m ω).trans (congrArg
      (fun z ↦ LinearMap.lTensor M (polyWedgeOne A B W n ω) (nabla m) + m ⊗ₜ z)
      (dividedPowerDeRham_eq_formsRelDifferential_add_formsBaseDifferential A B W n ω)))
    (dC_dC A B W nabla hint) (formsRelDifferential_formsRelDifferential A B W)
    (relativeFormsHomotopy_relContraction_zero A B W)
    (relativeFormsHomotopy_relContraction A B W)
    (relativeFormsHomotopy_relativeFormsHomotopy A B W)
    (relativeFormsHomotopy_coefficientFormsMap A B W)
    (relativeFormsRetraction_relativeFormsHomotopy A B W)
    (relativeFormsRetraction_coefficientFormsMap A B W)
    (dC_lTensor_coefficientFormsMap A B W nabla hint)
    (formsBidegreeProjection_sum A B W)
    (relativeFormsHomotopy_formsBidegreeProjection A B W)
    (fun n l i ↦ formsBidegreeProjection_formsBaseDifferential_eq_zero A B W n (l := l) (i := i))
    (projB_comp_polyWedgeOne A B W)

end Instance

/-! ### The first clause of Tag 07LD -/

section Clause

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A B] (W : Type u)
  {M : Type w} [AddCommGroup M] [Module (B : Type u) M]
  (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
  (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
    (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla)

/-- `ψ`, read with the base change cancelled, is `1_M ⊗ ψ`. -/
private theorem polyTermEquiv_polyComparison_apply (i : ℕ) (x : oneVariableSourceTerm A B M i) :
    polyTermEquiv A B W M i (polyComparison A B W nabla hint i x) =
      LinearMap.lTensor M (coefficientFormsMap A B W i) (baseTermEquiv A B M i x) :=
  (congrArg (fun z ↦ polyTermEquiv A B W M i (polyComparison A B W nabla hint i z))
    ((baseTermEquiv A B M i).symm_apply_apply x).symm).trans
    (polyTermEquiv_polyComparison A B W nabla hint i (baseTermEquiv A B M i x))

/-- The differential of `M ⊗_P Ω^*_{P/A,δ'}`, read with the base change cancelled, is `dC`. -/
private theorem polyTermEquiv_polyTargetDeRhamComplex_d (i : ℕ) (y : polyTargetTerm A B W M i) :
    polyTermEquiv A B W M (i + 1) (((polyTargetDeRhamComplex A B W nabla hint).d i (i + 1)).hom y) =
      dC A B W nabla i (polyTermEquiv A B W M i y) :=
  (congrArg (polyTermEquiv A B W M (i + 1)) (LinearMap.congr_fun (connectionDeRhamComplex_hom_d
    (polySource A B W) (polyProjection A B W) (Submodule.mkQ_surjective _)
    (polyGenerationHypothesis A B W) (polyBaseChangeConnection A B W nabla)
    (polyBaseChangeConnection_isIntegrable A B W nabla hint) i) y)).trans
    (polyTermEquiv_extendedConnection_apply A B W nabla i y)

/-- **[Stacks, Lemma 60.19.2, Tag 07LD], the first clause.**

Let `A` be a ring, let `(B, I, δ)` be a divided power ring which is an `A`-algebra, and let
`P = B⟨x_w : w ∈ W⟩` be the divided power polynomial ring over `B` on an arbitrary family `W` of
variables, with divided power ideal `J = IP + B⟨x_w⟩₊`
(`DividedPowers.setIndexedDividedPowerPolynomialDividedPowers`).  Let `M` be a `B`-module with an
integrable connection `∇ : M → M ⊗_B Ω¹_{B/A,δ}`.  Then the map of de Rham complexes

`M ⊗_B Ω^*_{B/A,δ} ⟶ M ⊗_P Ω^*_{P/A,δ}`

is a quasi-isomorphism.  The target is the de Rham complex of the base change of `(M, ∇)` to `P`,
`Crystalline.DividedPowerPolynomial.polyTargetDeRhamComplex`, with terms
`(P ⊗_B M) ⊗_P Ω^i_{P/A,δ}`, and the map is the canonical one of [Stacks, Tag 07PY],
`Crystalline.DividedPowerPolynomial.polyDeRhamComparison`.  The family of variables lives in the
universe of `B`.  Together with the clause over the completions this is
`Crystalline.DividedPowerPolynomial.stacks07LD`. -/
public theorem quasiIso_polyDeRhamComparison :
    QuasiIso (polyDeRhamComparison A B W nabla hint) := by
  let : LinearOrder W := IsWellOrder.linearOrder WellOrderingRel
  obtain ⟨pi', H, h1, h2, h3, h4⟩ := exists_retraction_poly A B W nabla hint
  let pT := polyTermEquiv A B W M
  let bT := baseTermEquiv A B M
  let c := polyComparison A B W nabla hint
  have hc := polyTermEquiv_polyComparison_apply A B W nabla hint
  have hL := polyTermEquiv_polyTargetDeRhamComplex_d A B W nabla hint
  refine quasiIso_of_additiveRetraction (polyDeRhamComparison A B W nabla hint)
    (fun i ↦ (bT i).symm.toAddMonoidHom.comp ((pi' i).comp (pT i).toAddMonoidHom))
    (fun i ↦ (pT i).symm.toAddMonoidHom.comp ((H i).comp (pT (i + 1)).toAddMonoidHom))
    ?_ ?_ ?_ ?_
  · intro i x
    change (bT i).symm (pi' i (pT i (c i x))) = x
    exact (congrArg (fun z ↦ (bT i).symm (pi' i z)) (hc i x)).trans
      ((congrArg (bT i).symm (h1 i (bT i x))).trans ((bT i).symm_apply_apply x))
  · intro i y
    change (bT (i + 1)).symm (pi' (i + 1) (pT (i + 1)
        (((polyTargetDeRhamComplex A B W nabla hint).d i (i + 1)).hom y))) =
      ((oneVariableSourceDeRhamComplex A B nabla hint).d i (i + 1)).hom
        ((bT i).symm (pi' i (pT i y)))
    exact (congrArg (fun z ↦ (bT (i + 1)).symm (pi' (i + 1) z)) (hL i y)).trans
      ((congrArg (bT (i + 1)).symm (h2 i (pT i y))).trans (((bT (i + 1)).symm_apply_apply _).trans
        (LinearMap.congr_fun (oneVariableSourceDeRhamComplex_hom_d A B nabla hint i) _).symm))
  · intro y
    apply (pT 0).injective
    change pT 0 ((pT 0).symm (H 0 (pT (0 + 1)
        (((polyTargetDeRhamComplex A B W nabla hint).d 0 (0 + 1)).hom y))) +
      c 0 ((bT 0).symm (pi' 0 (pT 0 y)))) = pT 0 y
    refine (map_add (pT 0) _ _).trans ?_
    refine Eq.trans (congrArg₂ (· + ·) ((pT 0).apply_symm_apply _)
      ((hc 0 _).trans (congrArg _ ((bT 0).apply_symm_apply _)))) ?_
    refine Eq.trans (congrArg (fun z ↦ H 0 z +
      LinearMap.lTensor M (coefficientFormsMap A B W 0) (pi' 0 (pT 0 y))) (hL 0 y)) ?_
    exact h3 (pT 0 y)
  · intro n y
    apply (pT (n + 1)).injective
    have hL' : pT (n + 1) (((polyTargetDeRhamComplex A B W nabla hint).d n (n + 1)).hom
        ((pT n).symm (H n (pT (n + 1) y)))) = dC A B W nabla n (H n (pT (n + 1) y)) :=
      (hL n _).trans (congrArg (dC A B W nabla n) ((pT n).apply_symm_apply _))
    refine (map_add (pT (n + 1)) _ _).trans ?_
    refine Eq.trans (congrArg₂ (· + ·) (map_add (pT (n + 1)) _ _)
      ((hc (n + 1) _).trans (congrArg _ ((bT (n + 1)).apply_symm_apply _)))) ?_
    refine Eq.trans (congrArg (fun z ↦ z +
      LinearMap.lTensor M (coefficientFormsMap A B W (n + 1)) (pi' (n + 1) (pT (n + 1) y)))
      (congrArg₂ (· + ·) hL' (((pT (n + 1)).apply_symm_apply _).trans
        (congrArg (H (n + 1)) (hL (n + 1) y))))) ?_
    exact h4 n (pT (n + 1) y)

/-! ### Both clauses of Tag 07LD -/

/-- **[Stacks, Lemma 60.19.2, Tag 07LD].**

Let `A` be a ring, let `(B, I, δ)` be a divided power ring which is an `A`-algebra, and let
`P = B⟨x_w : w ∈ W⟩` be the divided power polynomial ring over `B` on an arbitrary family `W` of
variables, with divided power ideal `J = IP + B⟨x_w⟩₊`.

1. For every `B`-module `M` with an integrable connection `∇ : M → M ⊗_B Ω¹_{B/A,δ}`, the map of
   de Rham complexes `M ⊗_B Ω^*_{B/A,δ} ⟶ M ⊗_P Ω^*_{P/A,δ}` is a quasi-isomorphism
   (`Crystalline.DividedPowerPolynomial.quasiIso_polyDeRhamComparison`).
2. Let `D`, resp. `D'`, be the `p`-adic completion of `B`, resp. `P`, and `Ω̂^i_D`, resp.
   `Ω̂^i_{D'}`, the `p`-adic completion of `Ω^i_{B/A,δ}`, resp. `Ω^i_{P/A,δ}`.  For every
   `D`-module `M` with an integrable connection `∇ : M → M ⊗̂_D Ω̂¹_D` (the composite
   `M → M ⊗̂_D Ω̂¹_D → M ⊗̂_D Ω̂²_D` vanishes), the map of de Rham complexes
   `M ⊗̂_D Ω̂^*_D ⟶ M ⊗̂_D Ω̂^*_{D'}` is a quasi-isomorphism
   (`Crystalline.DividedPowerPolynomial.quasiIso_completedDeRhamComparison`).

The second clause holds without the source's hypothesis that `M` is `p`-adically complete, so it
is not made.  The variables, and the ring `A`, live in the universe of `B`. -/
@[stacks 07LD "both clauses: the comparison of de Rham complexes for P = B⟨x_w⟩ on any family \
of variables is a quasi-isomorphism, for a B-module with integrable connection and, over the \
p-adic completions D and D', for a D-module with integrable connection"]
public theorem stacks07LD (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A B]
    (W : Type u) :
    (∀ (M : Type w) [AddCommGroup M] [Module (B : Type u) M]
        (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
        (hint : Connection.IsIntegrable (oneVariableBaseSource A B)
          (oneVariableBaseProjection A B) (Submodule.mkQ_surjective _)
          (oneVariableBaseGenerationHypothesis A B) nabla),
        QuasiIso (polyDeRhamComparison A B W nabla hint)) ∧
      ∀ (p : ℕ) (M : Type w) [AddCommGroup M]
        [Module (completedDividedPowerRing p (B := (B : Type u))) M]
        (nabla : CompletedConnection p (completedDividedPowerRing p (B := (B : Type u)))
          (completedDividedPowerForms p A B.dividedPowers 1)
          (completedFormsDifferential p A B.dividedPowers) M)
        (hint : CompletedDeRham.HasIntegrableConnection p
          (completedDividedPowerRing p (B := (B : Type u)))
          (completedDividedPowerForms p A B.dividedPowers)
          (completedDividedPowerWedge p A B.dividedPowers)
          (completedDividedPowerDeRham p A B.dividedPowers) M nabla
          (isGradedLeibniz_completedDividedPower p A B.dividedPowers)),
        QuasiIso (completedDeRhamComparison A B W p M nabla hint) :=
  ⟨fun _ _ _ nabla hint ↦ quasiIso_polyDeRhamComparison A B W nabla hint,
    fun p M _ _ nabla hint ↦ quasiIso_completedDeRhamComparison A B W p M nabla hint⟩

end Clause

end DividedPowerPolynomial

end Crystalline

end
