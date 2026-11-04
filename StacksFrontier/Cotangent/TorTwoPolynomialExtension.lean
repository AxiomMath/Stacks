module

public import Mathlib.Algebra.MvPolynomial.Derivation
public import StacksFrontier.Cotangent.TorTwoMulKernelFunctoriality
public import StacksFrontier.RingTheory.Koszul.Variables

/-!
# `Tor₂` of a polynomial extension with variables augmented to zero

Let `ε : R → B` be a surjective ring map with kernel `J`, let `T` be a set and let
`S = R[x_t, t ∈ T]`, augmented to `B` by `x_t ↦ 0` followed by `ε`, with kernel `J₁`. This is the
situation of the degree-one term `P₁ = P₀[x_t]` of the resolution of Stacks Example 09D4, and the
computation of Stacks Remark 09D6 is

`Tor₂^{S}(B, B) = ∧²(⨁_{t ∈ T} B) ⊕ ⨁_{t ∈ T} J/J² ⊕ Tor₂^R(B, B)`,

where, in the tensor-kernel model `Ker(J₁ ⊗_S J₁ → J₁²)` of `Tor₂^S(B, B)`, the basis element
`x_t ∧ x_{t'}` of the first summand is `x_t ⊗ x_{t'} - x_{t'} ⊗ x_t`, the element `x_t ⊗ f̄` of the
second summand (`f ∈ J`) is `x_t ⊗ f - f ⊗ x_t`, and the last summand is embedded by the
inclusion `s₀ : R → S`.

If moreover `f_t ∈ J` (`t ∈ T`) and `d₀, d₁ : S → R` are the `R`-algebra maps with `d₀(x_t) = 0`
and `d₁(x_t) = f_t`, then `d₀ - d₁ : Tor₂^S(B, B) → Tor₂^R(B, B)` is zero on the last summand,
sends `x_t ⊗ f̄` to `f ⊗ f_t - f_t ⊗ f` and `x_t ∧ x_{t'}` to `f_{t'} ⊗ f_t - f_t ⊗ f_{t'}`; and if
the `f_t` generate `J`, its image is the image of the antisymmetrisation
`∧²_B(J/J²) → Tor₂^R(B, B)`, so that

`∧²_B(J/J²) → Tor₂^R(B, B) → Coker(d₀ - d₁) → 0`

is exact.

## Main definitions

* `Stacks.Cotangent.TorTwo.polyAug`: the augmentation `S = R[x_t] → B`, `x_t ↦ 0`.
* `Stacks.Cotangent.TorTwo.polyWedge`, `polyMixed`, `polyDegen`: the three summands.
* `Stacks.Cotangent.TorTwo.polyDecomposition`: **the decomposition**, a `B`-linear equivalence.
* `Stacks.Cotangent.TorTwo.polyFace`: `d₀ - d₁` on the model.

## Main results

* `Stacks.Cotangent.TorTwo.polyDecomposition_wedge`, `polyDecomposition_mixed`,
  `polyDecomposition_degen`: the three correspondences of the source.
* `Stacks.Cotangent.TorTwo.polyFace_degen`, `polyFace_mixed`, `polyFace_wedge`: the values of
  `d₀ - d₁` on the three summands.
* `Stacks.Cotangent.TorTwo.range_polyFace`: the image of `d₀ - d₁` is that of `∧²_B(J/J²)`.
* `Stacks.Cotangent.TorTwo.exact_wedgeAntisymm_polyFace`: the exact sequence.

## Implementation notes

Injectivity of the decomposition is witnessed by an explicit left inverse, built from the
derivation `S → ⨁_T S`, `x_t ↦ e_t`, and the constant term `S → R`; on the first summand that
inverse uses a linear order on `T`, chosen inside the proof. Surjectivity reduces every element of
`J₁ ⊗_S J₁` to a normal form and then uses the exactness of the Koszul complex of the variables
of `S` in degree one (`MvPolynomial.variableKoszul_exact_positive`), which holds for an
arbitrary set of variables and over an arbitrary coefficient ring.

## References

* [Stacks Project, Tag 09D6](https://stacks.math.columbia.edu/tag/09D6)
* [Stacks Project, Tag 09D4](https://stacks.math.columbia.edu/tag/09D4)
-/

@[expose] public noncomputable section

open scoped TensorProduct
open MvPolynomial

universe u v w

namespace Stacks.Cotangent.TorTwo

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] (ε : R →+* B) (T : Type w)

/-! ### The augmentation and the elements -/

/-- The augmentation `R[x_t] → R → B`, `x_t ↦ 0` followed by `ε`. -/
def polyAug : MvPolynomial T R →+* B := ε.comp constantCoeff

/-- The augmentation sends `p` to `ε` of its constant coefficient. -/
theorem polyAug_apply (p : MvPolynomial T R) : polyAug ε T p = ε (constantCoeff p) := rfl

/-- The augmentation restricted to the constants `R → R[x_t]` is `ε`. -/
theorem polyAug_comp_C : (polyAug ε T).comp C = ε := by
  ext r
  simp [polyAug]

/-- The constant coefficient followed by `ε` is the augmentation. -/
theorem comp_constantCoeff : ε.comp constantCoeff = polyAug ε T := rfl

/-- If `ε (f t) = 0` for every `t`, then evaluation at `f` followed by `ε` is the augmentation. -/
theorem comp_eval {f : T → R} (hf : ∀ t, ε (f t) = 0) : ε.comp (eval f) = polyAug ε T := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [polyAug]
  · intro t
    simp [polyAug, hf t]

/-- If `ε` is surjective, so is the augmentation `R[x_t] → B`. -/
instance [Fact (Function.Surjective ε)] : Fact (Function.Surjective (polyAug ε T)) :=
  ⟨fun b => by
    obtain ⟨r, rfl⟩ := (Fact.out : Function.Surjective ε) b
    exact ⟨C r, by simp [polyAug]⟩⟩

variable {ε T}

/-- The variable `x_t` as an element of `J₁ = ker(R[x_t] → B)`. -/
def xVar (t : T) : RingHom.ker (polyAug ε T) := ⟨X t, by simp [polyAug]⟩

/-- The underlying polynomial of `xVar t` is `X t`. -/
@[simp]
theorem coe_xVar (t : T) : (xVar (ε := ε) t : MvPolynomial T R) = X t := rfl

/-- `s₀ : J → J₁`, the inclusion of constants. -/
def constIdeal : RingHom.ker ε →+ RingHom.ker (polyAug ε T) := kerMap C (polyAug_comp_C ε T)

/-- The underlying polynomial of `constIdeal a` is the constant `C a`. -/
@[simp]
theorem coe_constIdeal (a : RingHom.ker ε) :
    (constIdeal (T := T) a : MvPolynomial T R) = C (a : R) := rfl

/-- `constIdeal (r • a) = C r • constIdeal a`. -/
theorem constIdeal_smul (r : R) (a : RingHom.ker ε) :
    constIdeal (T := T) (r • a) = (C r : MvPolynomial T R) • constIdeal a :=
  kerMap_smul _ _ r a

/-- The `S`-linear map `S^{(T)} → J₁`, `e_t ↦ x_t`. -/
def varComb : (T →₀ MvPolynomial T R) →ₗ[MvPolynomial T R] RingHom.ker (polyAug ε T) :=
  Finsupp.linearCombination _ xVar

/-- The underlying polynomial of `varComb q` is `∑_t q_t x_t`. -/
theorem coe_varComb (q : T →₀ MvPolynomial T R) :
    (varComb (ε := ε) q : MvPolynomial T R) = Finsupp.linearCombination _ X q := by
  rw [varComb, ← Submodule.subtype_apply, Finsupp.apply_linearCombination]
  rfl

/-- Reduction `S^{(T)} → B^{(T)}` along the augmentation. -/
def reduceVec : (T →₀ MvPolynomial T R) →+ (T →₀ B) :=
  Finsupp.mapRange.addMonoidHom (polyAug ε T).toAddMonoidHom

/-- Reduction sends `s e_t` to `s̄ e_t`, where `s̄` is the augmentation of `s`. -/
@[simp]
theorem reduceVec_single (t : T) (s : MvPolynomial T R) :
    reduceVec (ε := ε) (Finsupp.single t s) = Finsupp.single t (polyAug ε T s) := by
  simp [reduceVec]

/-- Reduction is semilinear along the augmentation. -/
theorem reduceVec_smul (s : MvPolynomial T R) (q : T →₀ MvPolynomial T R) :
    reduceVec (ε := ε) (s • q) = polyAug ε T s • reduceVec (ε := ε) q := by
  ext t
  simp [reduceVec]

variable [Fact (Function.Surjective ε)]

/-! ### The three summands -/

/-- The bilinear map `B^{(T)} × B^{(T)} → Ker(J₁ ⊗ J₁ → J₁²)`, `(e_t, e_{t'}) ↦ x_t ⊗ x_{t'} -
x_{t'} ⊗ x_t`. -/
def polyWedgeBilin :
    (T →₀ B) →ₗ[B] (T →₀ B) →ₗ[B] mulKernel (polyAug ε T) :=
  Finsupp.linearCombination B fun t =>
    Finsupp.linearCombination B fun t' => antisymm (xVar t) (xVar t')

/-- `polyWedgeBilin (b e_t) (b' e_{t'}) = b b' (x_t ⊗ x_{t'} - x_{t'} ⊗ x_t)`. -/
theorem polyWedgeBilin_single (t t' : T) (b b' : B) :
    polyWedgeBilin (ε := ε) (Finsupp.single t b) (Finsupp.single t' b') =
      b • b' • antisymm (xVar t) (xVar t') := by
  simp [polyWedgeBilin]

/-- The antisymmetric tensor of `∑_t q_t x_t` and `∑_t q'_t x_t` is `polyWedgeBilin` of the
reductions of `q` and `q'`. -/
theorem antisymm_varComb (q q' : T →₀ MvPolynomial T R) :
    antisymm (varComb (ε := ε) q) (varComb q') =
      polyWedgeBilin (reduceVec (ε := ε) q) (reduceVec (ε := ε) q') := by
  induction q using Finsupp.induction_linear with
  | zero => simp [antisymm_zero_left]
  | add q₁ q₂ h₁ h₂ => rw [map_add, antisymm_add_left, h₁, h₂, map_add, map_add,
      LinearMap.add_apply]
  | single t s =>
    induction q' using Finsupp.induction_linear with
    | zero => simp [antisymm_zero_right]
    | add q₁ q₂ h₁ h₂ => rw [map_add, antisymm_add_right, h₁, h₂, map_add, map_add]
    | single t' s' =>
      rw [reduceVec_single, reduceVec_single, polyWedgeBilin_single, varComb,
        Finsupp.linearCombination_single, Finsupp.linearCombination_single,
        antisymm_smul_left, antisymm_smul_right, algebraMap_smul_mulKernel,
        algebraMap_smul_mulKernel, smul_comm]

/-- `polyWedgeBilin` is alternating. -/
theorem polyWedgeBilin_self (v : T →₀ B) : polyWedgeBilin (ε := ε) v v = 0 := by
  obtain ⟨q, rfl⟩ : ∃ q, reduceVec (ε := ε) q = v :=
    Finsupp.mapRange_surjective _ (map_zero _) (Fact.out : Function.Surjective (polyAug ε T)) v
  rw [← antisymm_varComb, antisymm_self]

/-- **The first summand**: `∧²_B(B^{(T)}) → Tor₂^S(B, B)`, `x_t ∧ x_{t'} ↦ x_t ⊗ x_{t'} -
x_{t'} ⊗ x_t`. -/
def polyWedge : ⋀[B]^2 (T →₀ B) →ₗ[B] mulKernel (polyAug ε T) :=
  exteriorTwoLift polyWedgeBilin polyWedgeBilin_self

/-- `polyWedge (v ∧ w) = polyWedgeBilin v w`. -/
theorem polyWedge_wedge (v w : T →₀ B) :
    polyWedge (ε := ε) (wedgeBilin v w) = polyWedgeBilin v w :=
  exteriorTwoLift_wedgeBilin _ _ _ _

/-- `polyWedge (e_t ∧ e_{t'}) = x_t ⊗ x_{t'} - x_{t'} ⊗ x_t`. -/
theorem polyWedge_single (t t' : T) :
    polyWedge (ε := ε) (wedgeBilin (Finsupp.single t 1) (Finsupp.single t' 1)) =
      antisymm (xVar t) (xVar t') := by
  rw [polyWedge_wedge, polyWedgeBilin_single, one_smul, one_smul]

/-- For fixed `t`, the map `J/J² → Tor₂^S(B, B)`, `f̄ ↦ x_t ⊗ f - f ⊗ x_t`. -/
def polyMixedAt (t : T) : (RingHom.ker ε).Cotangent →ₗ[B] mulKernel (polyAug ε T) :=
  cotangentLift
    { toFun := fun a => antisymm (xVar t) (constIdeal a)
      map_zero' := by rw [map_zero, antisymm_zero_right]
      map_add' := fun a a' => by rw [map_add, antisymm_add_right] }
    fun r a => by
      change antisymm (xVar t) (constIdeal (r • a)) = ε r • antisymm (xVar t) (constIdeal a)
      rw [constIdeal_smul, antisymm_smul_right, ← algebraMap_smul_mulKernel, ← RingHom.comp_apply,
        polyAug_comp_C]

/-- `polyMixedAt t` sends the class of `a ∈ J` to `x_t ⊗ a - a ⊗ x_t`. -/
@[simp]
theorem polyMixedAt_toCotangent (t : T) (a : RingHom.ker ε) :
    polyMixedAt t ((RingHom.ker ε).toCotangent a) = antisymm (xVar t) (constIdeal a) :=
  cotangentLift_toCotangent _ _ a

/-- **The second summand**: `⨁_T J/J² → Tor₂^S(B, B)`, `x_t ⊗ f̄ ↦ x_t ⊗ f - f ⊗ x_t`. -/
def polyMixed : (T →₀ (RingHom.ker ε).Cotangent) →ₗ[B] mulKernel (polyAug ε T) :=
  Finsupp.lsum ℕ polyMixedAt

/-- `polyMixed` on the component `t` is `polyMixedAt t`. -/
@[simp]
theorem polyMixed_single (t : T) (c : (RingHom.ker ε).Cotangent) :
    polyMixed (Finsupp.single t c) = polyMixedAt t c := by
  simp [polyMixed]

/-- **The third summand**: `s₀ : Tor₂^R(B, B) → Tor₂^S(B, B)`. -/
def polyDegen : mulKernel ε →ₗ[B] mulKernel (polyAug ε T) :=
  mulKernelMap C (polyAug_comp_C ε T)

/-- The map from the three summands. -/
def polyDecompositionMap :
    (⋀[B]^2 (T →₀ B) × (T →₀ (RingHom.ker ε).Cotangent) × mulKernel ε) →ₗ[B]
      mulKernel (polyAug ε T) :=
  polyWedge.coprod (polyMixed.coprod polyDegen)

/-! ### A left inverse of the decomposition -/

section LeftInverse

/-- Two `B`-bilinear maps out of `B^{(T)}` agreeing on pairs of basis vectors agree. -/
theorem finsupp_bilin_ext {N : Type*} [AddCommGroup N] [Module B N]
    {β γ : (T →₀ B) →ₗ[B] (T →₀ B) →ₗ[B] N}
    (h : ∀ t t' : T, β (Finsupp.single t 1) (Finsupp.single t' 1) =
      γ (Finsupp.single t 1) (Finsupp.single t' 1)) : β = γ :=
  (Finsupp.basisSingleOne).ext fun t => (Finsupp.basisSingleOne).ext fun t' => by
    simpa using h t t'

variable (R T) in
/-- The derivation `S → S^{(T)}`, `x_t ↦ e_t`. -/
def varDerivation : Derivation R (MvPolynomial T R) (T →₀ MvPolynomial T R) :=
  MvPolynomial.mkDerivation R fun t => Finsupp.single t 1

/-- `J₁ → B^{(T)}`: the coefficients of the variables, reduced to `B`. -/
def linearPart : RingHom.ker (polyAug ε T) →+ (T →₀ B) :=
  (reduceVec (ε := ε)).comp ((varDerivation R T).toLinearMap.toAddMonoidHom.comp
    (RingHom.ker (polyAug ε T)).subtype.toAddMonoidHom)

omit [Fact (Function.Surjective ε)] in
/-- `linearPart a` is the reduction of `varDerivation R T a`. -/
theorem linearPart_apply (a : RingHom.ker (polyAug ε T)) :
    linearPart a = reduceVec (ε := ε) (varDerivation R T (a : MvPolynomial T R)) := rfl

omit [Fact (Function.Surjective ε)] in
/-- `linearPart` is semilinear along the augmentation. -/
theorem linearPart_smul (s : MvPolynomial T R) (a : RingHom.ker (polyAug ε T)) :
    linearPart (s • a) = polyAug ε T s • linearPart a := by
  rw [linearPart_apply, linearPart_apply, Submodule.coe_smul, smul_eq_mul, Derivation.leibniz,
    map_add, reduceVec_smul, reduceVec_smul,
    show polyAug ε T (a : MvPolynomial T R) = 0 from a.2, zero_smul, add_zero]

omit [Fact (Function.Surjective ε)] in
/-- `linearPart x_t = e_t`. -/
@[simp]
theorem linearPart_xVar (t : T) : linearPart (xVar (ε := ε) t) = Finsupp.single t 1 := by
  rw [linearPart_apply, coe_xVar, varDerivation, MvPolynomial.mkDerivation_X, reduceVec_single,
    map_one]

omit [Fact (Function.Surjective ε)] in
/-- `linearPart` vanishes on constants. -/
@[simp]
theorem linearPart_constIdeal (a : RingHom.ker ε) : linearPart (constIdeal (T := T) a) = 0 := by
  rw [linearPart_apply, coe_constIdeal, MvPolynomial.derivation_C, map_zero]

/-- `J₁ → J/J²`: the class of the constant term. -/
def constPart : RingHom.ker (polyAug ε T) →+ (RingHom.ker ε).Cotangent :=
  (RingHom.ker ε).toCotangent.toAddMonoidHom.comp (kerMap constantCoeff (comp_constantCoeff ε T))

/-- `constPart` is semilinear along the augmentation. -/
theorem constPart_smul (s : MvPolynomial T R) (a : RingHom.ker (polyAug ε T)) :
    constPart (s • a) = polyAug ε T s • constPart a := by
  simp only [constPart, AddMonoidHom.coe_comp, Function.comp_apply, kerMap_smul,
    LinearMap.toAddMonoidHom_coe, map_smul]
  rw [polyAug_apply, algebraMap_smul_cotangent]

omit [Fact (Function.Surjective ε)] in
/-- `constPart x_t = 0`. -/
@[simp]
theorem constPart_xVar (t : T) : constPart (xVar (ε := ε) t) = 0 := by
  have : kerMap constantCoeff (comp_constantCoeff ε T) (xVar t) = 0 :=
    Subtype.ext (by simp)
  simp [constPart, this]

omit [Fact (Function.Surjective ε)] in
/-- `constPart` sends the constant `a ∈ J` to its class in `J/J²`. -/
@[simp]
theorem constPart_constIdeal (a : RingHom.ker ε) :
    constPart (constIdeal (T := T) a) = (RingHom.ker ε).toCotangent a := by
  have : kerMap constantCoeff (comp_constantCoeff ε T) (constIdeal a) = a :=
    Subtype.ext (by simp)
  simp [constPart, this]

omit [Fact (Function.Surjective ε)] in
/-- The constant coefficient of `x_t` is `0`, as an element of `J`. -/
theorem kerMap_constantCoeff_xVar (t : T) :
    kerMap constantCoeff (comp_constantCoeff ε T) (xVar t) = 0 :=
  Subtype.ext (by simp)

omit [Fact (Function.Surjective ε)] in
/-- The constant coefficient of the constant `a ∈ J` is `a`. -/
theorem kerMap_constantCoeff_constIdeal (a : RingHom.ker ε) :
    kerMap constantCoeff (comp_constantCoeff ε T) (constIdeal a) = a :=
  Subtype.ext (by simp)

/-- The bilinear map `B^{(T)} × J/J² → (J/J²)^{(T)}`, `(e_t, c) ↦ c` in position `t`. -/
def tensorSingle :
    (T →₀ B) →ₗ[B] (RingHom.ker ε).Cotangent →ₗ[B] (T →₀ (RingHom.ker ε).Cotangent) :=
  Finsupp.linearCombination B fun t => Finsupp.lsingle t

/-- `tensorSingle (b e_t) c` is `b • c` in position `t`. -/
@[simp]
theorem tensorSingle_single (t : T) (b : B) (c : (RingHom.ker ε).Cotangent) :
    tensorSingle (Finsupp.single t b) c = Finsupp.single t (b • c) := by
  simp [tensorSingle]

/-- `J₁ ⊗_S J₁ → (J/J²)^{(T)}`, `a ⊗ b ↦ λ(a) ⊗ ρ(b)`. -/
def mixedPart :
    RingHom.ker (polyAug ε T) ⊗[MvPolynomial T R] RingHom.ker (polyAug ε T) →+
      (T →₀ (RingHom.ker ε).Cotangent) :=
  TensorProduct.liftAddHom
    { toFun := fun a => (tensorSingle (linearPart a)).toAddMonoidHom.comp constPart
      map_zero' := by ext b; simp
      map_add' := fun a a' => by ext b; simp }
    fun s a b => by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mk,
        ZeroHom.coe_mk, LinearMap.toAddMonoidHom_coe, linearPart_smul, constPart_smul, map_smul,
        LinearMap.smul_apply]

/-- `mixedPart (a ⊗ b) = tensorSingle (linearPart a) (constPart b)`. -/
@[simp]
theorem mixedPart_tmul (a b : RingHom.ker (polyAug ε T)) :
    mixedPart (a ⊗ₜ[MvPolynomial T R] b) = tensorSingle (linearPart a) (constPart b) := rfl

/-- `mixedPart` is semilinear along the augmentation. -/
theorem mixedPart_smul (s : MvPolynomial T R)
    (x : RingHom.ker (polyAug ε T) ⊗[MvPolynomial T R] RingHom.ker (polyAug ε T)) :
    mixedPart (s • x) = polyAug ε T s • mixedPart x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [TensorProduct.smul_tmul', mixedPart_tmul, mixedPart_tmul, linearPart_smul,
      map_smul, LinearMap.smul_apply]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- A linear map out of `Tor₂^S(B, B)` is determined on `polyWedge` by its values on
`x_t ⊗ x_{t'} - x_{t'} ⊗ x_t`. -/
private theorem map_polyWedge_eq {N : Type*} [AddCommGroup N] [Module B N]
    (g : mulKernel (polyAug ε T) →ₗ[B] N) (g' : ⋀[B]^2 (T →₀ B) →ₗ[B] N)
    (h : ∀ t t' : T, g (antisymm (xVar t) (xVar t')) =
      g' (wedgeBilin (Finsupp.single t 1) (Finsupp.single t' 1))) (w : ⋀[B]^2 (T →₀ B)) :
    g (polyWedge w) = g' w := by
  have h' : g ∘ₗ polyWedge = g' := by
    refine exteriorTwo_ext fun v w => ?_
    rw [LinearMap.comp_apply, polyWedge_wedge]
    refine LinearMap.congr_fun₂ (f := polyWedgeBilin.compr₂ g) (g := wedgeBilin.compr₂ g')
      (finsupp_bilin_ext fun t t' => ?_) v w
    rw [LinearMap.compr₂_apply, LinearMap.compr₂_apply, polyWedgeBilin_single, one_smul, one_smul,
      h]
  exact LinearMap.congr_fun h' w

/-- A linear map out of `Tor₂^S(B, B)` is determined on `polyMixed` by its values on
`x_t ⊗ f - f ⊗ x_t`. -/
private theorem map_polyMixed_eq {N : Type*} [AddCommGroup N] [Module B N]
    (g : mulKernel (polyAug ε T) →ₗ[B] N) (g' : (T →₀ (RingHom.ker ε).Cotangent) →ₗ[B] N)
    (h : ∀ (t : T) (a : RingHom.ker ε), g (antisymm (xVar t) (constIdeal a)) =
      g' (Finsupp.single t ((RingHom.ker ε).toCotangent a))) (m : T →₀ (RingHom.ker ε).Cotangent) :
    g (polyMixed m) = g' m := by
  have h' : g ∘ₗ polyMixed = g' := by
    refine Finsupp.lhom_ext fun t c => ?_
    obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective _ c
    rw [LinearMap.comp_apply, polyMixed_single, polyMixedAt_toCotangent, h]
  exact LinearMap.congr_fun h' m

variable [LinearOrder T]

/-- The ordered half of the wedge product: `(e_s, e_{s'}) ↦ e_s ∧ e_{s'}` if `s < s'`, else `0`. -/
def orderedWedge : (T →₀ B) →ₗ[B] (T →₀ B) →ₗ[B] ⋀[B]^2 (T →₀ B) :=
  Finsupp.linearCombination B fun s => Finsupp.linearCombination B fun s' =>
    if s < s' then wedgeBilin (Finsupp.single s 1) (Finsupp.single s' 1) else 0

/-- The antisymmetrisation of `orderedWedge` is the wedge product. -/
theorem orderedWedge_sub (v w : T →₀ B) :
    orderedWedge v w - orderedWedge w v = wedgeBilin v w := by
  have h : orderedWedge - orderedWedge.flip =
      (wedgeBilin : (T →₀ B) →ₗ[B] (T →₀ B) →ₗ[B] ⋀[B]^2 (T →₀ B)) := by
    refine finsupp_bilin_ext fun s s' => ?_
    simp only [LinearMap.sub_apply, LinearMap.flip_apply, orderedWedge,
      Finsupp.linearCombination_single, one_smul]
    rcases lt_trichotomy s s' with h | rfl | h
    · rw [ite_eq_left h, ite_eq_right (not_lt_of_gt h), sub_zero]
    · rw [ite_eq_right (lt_irrefl s), sub_zero, wedgeBilin_self]
    · rw [ite_eq_right (not_lt_of_gt h), ite_eq_left h, zero_sub, wedgeBilin_swap, neg_neg]
  exact LinearMap.congr_fun₂ h v w

/-- `J₁ ⊗_S J₁ → ∧²_B(B^{(T)})`, `a ⊗ b ↦` the ordered half of `λ(a) ∧ λ(b)`. -/
def wedgePart :
    RingHom.ker (polyAug ε T) ⊗[MvPolynomial T R] RingHom.ker (polyAug ε T) →+
      ⋀[B]^2 (T →₀ B) :=
  TensorProduct.liftAddHom
    { toFun := fun a => (orderedWedge (linearPart a)).toAddMonoidHom.comp linearPart
      map_zero' := by ext b; simp
      map_add' := fun a a' => by ext b; simp }
    fun s a b => by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mk,
        ZeroHom.coe_mk, LinearMap.toAddMonoidHom_coe, linearPart_smul, map_smul,
        LinearMap.smul_apply]

omit [Fact (Function.Surjective ε)] in
/-- `wedgePart (a ⊗ b) = orderedWedge (linearPart a) (linearPart b)`. -/
@[simp]
theorem wedgePart_tmul (a b : RingHom.ker (polyAug ε T)) :
    wedgePart (a ⊗ₜ[MvPolynomial T R] b) = orderedWedge (linearPart a) (linearPart b) := rfl

omit [Fact (Function.Surjective ε)] in
/-- `wedgePart` is semilinear along the augmentation. -/
theorem wedgePart_smul (s : MvPolynomial T R)
    (x : RingHom.ker (polyAug ε T) ⊗[MvPolynomial T R] RingHom.ker (polyAug ε T)) :
    wedgePart (s • x) = polyAug ε T s • wedgePart x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [TensorProduct.smul_tmul', wedgePart_tmul, wedgePart_tmul, linearPart_smul,
      map_smul, LinearMap.smul_apply]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- The wedge component of the retraction, `B`-linear on the model. -/
def wedgeRetraction : mulKernel (polyAug ε T) →ₗ[B] ⋀[B]^2 (T →₀ B) where
  toFun x := wedgePart (x : RingHom.ker (polyAug ε T) ⊗[MvPolynomial T R] _)
  map_add' x y := map_add _ _ _
  map_smul' b x := by
    rw [smul_mulKernel_def, Submodule.coe_smul, wedgePart_smul,
      Function.surjInv_eq (Fact.out : Function.Surjective (polyAug ε T))]
    rfl

/-- The mixed component of the retraction, `B`-linear on the model. -/
def mixedRetraction : mulKernel (polyAug ε T) →ₗ[B] (T →₀ (RingHom.ker ε).Cotangent) where
  toFun x := mixedPart (x : RingHom.ker (polyAug ε T) ⊗[MvPolynomial T R] _)
  map_add' x y := map_add _ _ _
  map_smul' b x := by
    rw [smul_mulKernel_def, Submodule.coe_smul, mixedPart_smul,
      Function.surjInv_eq (Fact.out : Function.Surjective (polyAug ε T))]
    rfl

/-- The constant-term component of the retraction: `d₀ : Tor₂^S(B, B) → Tor₂^R(B, B)`. -/
def constRetraction : mulKernel (polyAug ε T) →ₗ[B] mulKernel ε :=
  mulKernelMap constantCoeff (comp_constantCoeff ε T)

/-- The value of `wedgeRetraction` on `a ⊗ b - b ⊗ a`. -/
theorem wedgeRetraction_antisymm (a b : RingHom.ker (polyAug ε T)) :
    wedgeRetraction (antisymm a b) =
      orderedWedge (linearPart a) (linearPart b) - orderedWedge (linearPart b) (linearPart a) := by
  change wedgePart (a ⊗ₜ b - b ⊗ₜ a) = _
  rw [map_sub, wedgePart_tmul, wedgePart_tmul]

omit [LinearOrder T] in
/-- The value of `mixedRetraction` on `a ⊗ b - b ⊗ a`. -/
theorem mixedRetraction_antisymm (a b : RingHom.ker (polyAug ε T)) :
    mixedRetraction (antisymm a b) =
      tensorSingle (linearPart a) (constPart b) - tensorSingle (linearPart b) (constPart a) := by
  change mixedPart (a ⊗ₜ b - b ⊗ₜ a) = _
  rw [map_sub, mixedPart_tmul, mixedPart_tmul]

/-- `wedgeRetraction` is a left inverse of `polyWedge`. -/
theorem wedgeRetraction_polyWedge (w : ⋀[B]^2 (T →₀ B)) :
    wedgeRetraction (polyWedge (ε := ε) w) = w :=
  map_polyWedge_eq wedgeRetraction LinearMap.id (fun t t' => by
    rw [wedgeRetraction_antisymm, linearPart_xVar, linearPart_xVar, orderedWedge_sub,
      LinearMap.id_apply]) w

omit [LinearOrder T] in
/-- `mixedRetraction` vanishes on the image of `polyWedge`. -/
theorem mixedRetraction_polyWedge (w : ⋀[B]^2 (T →₀ B)) :
    mixedRetraction (polyWedge (ε := ε) w) = 0 :=
  map_polyWedge_eq mixedRetraction 0 (fun t t' => by
    rw [mixedRetraction_antisymm, constPart_xVar, constPart_xVar]
    simp) w

omit [LinearOrder T] in
/-- `constRetraction` vanishes on the image of `polyWedge`. -/
theorem constRetraction_polyWedge (w : ⋀[B]^2 (T →₀ B)) :
    constRetraction (polyWedge (ε := ε) w) = 0 :=
  map_polyWedge_eq constRetraction 0 (fun t t' => by
    rw [constRetraction, mulKernelMap_antisymm, kerMap_constantCoeff_xVar,
      kerMap_constantCoeff_xVar, antisymm_self]
    simp) w

/-- `wedgeRetraction` vanishes on the image of `polyMixed`. -/
theorem wedgeRetraction_polyMixed (m : T →₀ (RingHom.ker ε).Cotangent) :
    wedgeRetraction (polyMixed m) = 0 :=
  map_polyMixed_eq wedgeRetraction 0 (fun t a => by
    rw [wedgeRetraction_antisymm, linearPart_constIdeal]
    simp) m

omit [LinearOrder T] in
/-- `mixedRetraction` is a left inverse of `polyMixed`. -/
theorem mixedRetraction_polyMixed (m : T →₀ (RingHom.ker ε).Cotangent) :
    mixedRetraction (polyMixed m) = m :=
  map_polyMixed_eq mixedRetraction LinearMap.id (fun t a => by
    rw [mixedRetraction_antisymm, linearPart_constIdeal, map_zero, LinearMap.zero_apply,
      sub_zero, linearPart_xVar, constPart_constIdeal, tensorSingle_single, one_smul,
      LinearMap.id_apply]) m

omit [LinearOrder T] in
/-- `constRetraction` vanishes on the image of `polyMixed`. -/
theorem constRetraction_polyMixed (m : T →₀ (RingHom.ker ε).Cotangent) :
    constRetraction (polyMixed m) = 0 :=
  map_polyMixed_eq constRetraction 0 (fun t a => by
    rw [constRetraction, mulKernelMap_antisymm, kerMap_constantCoeff_xVar, antisymm_zero_left,
      LinearMap.zero_apply]) m

omit [Fact (Function.Surjective ε)] in
/-- `wedgePart` vanishes on the image of `J ⊗_R J` under `s₀`. -/
theorem wedgePart_tensorMap_C (y : RingHom.ker ε ⊗[R] RingHom.ker ε) :
    wedgePart (tensorMap C (polyAug_comp_C ε T) y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [tensorMap_tmul, wedgePart_tmul]
    change orderedWedge (linearPart (constIdeal a)) (linearPart (constIdeal b)) = 0
    rw [linearPart_constIdeal]
    simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

omit [LinearOrder T] in
/-- `mixedPart` vanishes on the image of `J ⊗_R J` under `s₀`. -/
theorem mixedPart_tensorMap_C (y : RingHom.ker ε ⊗[R] RingHom.ker ε) :
    mixedPart (tensorMap C (polyAug_comp_C ε T) y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [tensorMap_tmul, mixedPart_tmul]
    change tensorSingle (linearPart (constIdeal a)) (constPart (constIdeal b)) = 0
    rw [linearPart_constIdeal]
    simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/-- `wedgeRetraction` vanishes on the image of `polyDegen`. -/
theorem wedgeRetraction_polyDegen (k : mulKernel ε) :
    wedgeRetraction (polyDegen (T := T) k) = 0 :=
  wedgePart_tensorMap_C _

omit [LinearOrder T] in
/-- `mixedRetraction` vanishes on the image of `polyDegen`. -/
theorem mixedRetraction_polyDegen (k : mulKernel ε) :
    mixedRetraction (polyDegen (T := T) k) = 0 :=
  mixedPart_tensorMap_C _

omit [LinearOrder T] in
/-- `constRetraction` is a left inverse of `polyDegen`. -/
theorem constRetraction_polyDegen (k : mulKernel ε) :
    constRetraction (polyDegen (T := T) k) = k := by
  rw [constRetraction, polyDegen, ← mulKernelMap_comp]
  rw [mulKernelMap_congr (constantCoeff_comp_C R T) _ (RingHom.comp_id ε), mulKernelMap_id]

/-- The retraction of the decomposition map. -/
def polyRetraction :
    mulKernel (polyAug ε T) →ₗ[B]
      (⋀[B]^2 (T →₀ B) × (T →₀ (RingHom.ker ε).Cotangent) × mulKernel ε) :=
  wedgeRetraction.prod (mixedRetraction.prod constRetraction)

/-- `polyRetraction` is a left inverse of `polyDecompositionMap`. -/
theorem polyRetraction_polyDecompositionMap
    (z : ⋀[B]^2 (T →₀ B) × (T →₀ (RingHom.ker ε).Cotangent) × mulKernel ε) :
    polyRetraction (polyDecompositionMap z) = z := by
  obtain ⟨w, m, k⟩ := z
  have hd : polyDecompositionMap (w, m, k) = polyWedge w + (polyMixed m + polyDegen k) := rfl
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change wedgeRetraction (polyDecompositionMap (w, m, k)) = w
    rw [hd, map_add, map_add, wedgeRetraction_polyWedge, wedgeRetraction_polyMixed,
      wedgeRetraction_polyDegen, add_zero, add_zero]
  · change mixedRetraction (polyDecompositionMap (w, m, k)) = m
    rw [hd, map_add, map_add, mixedRetraction_polyWedge, mixedRetraction_polyMixed,
      mixedRetraction_polyDegen, add_zero, zero_add]
  · change constRetraction (polyDecompositionMap (w, m, k)) = k
    rw [hd, map_add, map_add, constRetraction_polyWedge, constRetraction_polyMixed,
      constRetraction_polyDegen, zero_add, zero_add]

end LeftInverse

/-- The map from the three summands is injective. -/
theorem polyDecompositionMap_injective :
    Function.Injective (polyDecompositionMap (ε := ε) (T := T)) := by
  classical
  let : LinearOrder T := linearOrderOfSTO WellOrderingRel
  exact Function.LeftInverse.injective polyRetraction_polyDecompositionMap

/-! ### Surjectivity of the decomposition -/

section Surjectivity

/-- `J₁^{(T)} → J₁ ⊗_S J₁`, `y ↦ Σ_t x_t ⊗ y_t`. -/
def varTensor :
    (T →₀ RingHom.ker (polyAug ε T)) →+
      RingHom.ker (polyAug ε T) ⊗[MvPolynomial T R] RingHom.ker (polyAug ε T) :=
  Finsupp.liftAddHom fun t => (TensorProduct.mk (MvPolynomial T R) _ _ (xVar t)).toAddMonoidHom

omit [Fact (Function.Surjective ε)] in
/-- `varTensor (a e_t) = x_t ⊗ a`. -/
@[simp]
theorem varTensor_single (t : T) (a : RingHom.ker (polyAug ε T)) :
    varTensor (Finsupp.single t a) = xVar t ⊗ₜ[MvPolynomial T R] a :=
  Finsupp.liftAddHom_apply_single _ _ _

omit [Fact (Function.Surjective ε)] in
/-- `varTensor` is `S`-linear. -/
theorem varTensor_smul (s : MvPolynomial T R) (y : T →₀ RingHom.ker (polyAug ε T)) :
    varTensor (s • y) = s • varTensor y := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y₁ y₂ h₁ h₂ => rw [smul_add, map_add, h₁, h₂, map_add, smul_add]
  | single t a => rw [Finsupp.smul_single, varTensor_single, varTensor_single,
      TensorProduct.tmul_smul]

/-- Scaling a vector of `S^{(T)}` by an element `j` of `J₁`. -/
def scaleVec (j : RingHom.ker (polyAug ε T)) :
    (T →₀ MvPolynomial T R) →+ (T →₀ RingHom.ker (polyAug ε T)) :=
  Finsupp.mapRange.addMonoidHom (LinearMap.toSpanSingleton _ _ j).toAddMonoidHom

omit [Fact (Function.Surjective ε)] in
/-- `scaleVec j (s e_t) = (s • j) e_t`. -/
@[simp]
theorem scaleVec_single (j : RingHom.ker (polyAug ε T)) (t : T) (s : MvPolynomial T R) :
    scaleVec j (Finsupp.single t s) = Finsupp.single t (s • j) := by
  simp [scaleVec]

omit [Fact (Function.Surjective ε)] in
/-- `varTensor (scaleVec j q) = (∑_t q_t x_t) ⊗ j`. -/
theorem varTensor_scaleVec (j : RingHom.ker (polyAug ε T)) (q : T →₀ MvPolynomial T R) :
    varTensor (scaleVec j q) = varComb q ⊗ₜ[MvPolynomial T R] j := by
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q₁ q₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, TensorProduct.add_tmul]
  | single t s => rw [scaleVec_single, varTensor_single, varComb,
      Finsupp.linearCombination_single, TensorProduct.smul_tmul]

/-- The underlying vector of `S^{(T)}` of a vector of `J₁^{(T)}`. -/
def subVec : (T →₀ RingHom.ker (polyAug ε T)) →+ (T →₀ MvPolynomial T R) :=
  Finsupp.mapRange.addMonoidHom (RingHom.ker (polyAug ε T)).subtype.toAddMonoidHom

omit [Fact (Function.Surjective ε)] in
/-- `subVec` is injective. -/
theorem subVec_injective : Function.Injective (subVec (ε := ε) (T := T)) :=
  Finsupp.mapRange_injective _ (map_zero _) Subtype.val_injective

omit [Fact (Function.Surjective ε)] in
/-- `subVec` is `S`-linear. -/
theorem subVec_smul (s : MvPolynomial T R) (y : T →₀ RingHom.ker (polyAug ε T)) :
    subVec (s • y) = s • subVec y := by
  ext t
  simp [subVec]

omit [Fact (Function.Surjective ε)] in
/-- The underlying vector of `scaleVec j q` is `j • q`. -/
theorem subVec_scaleVec (j : RingHom.ker (polyAug ε T)) (q : T →₀ MvPolynomial T R) :
    subVec (scaleVec j q) = (j : MvPolynomial T R) • q := by
  ext t
  simp [subVec, scaleVec, mul_comm]

omit [Fact (Function.Surjective ε)] in
/-- The underlying polynomial of `varComb q` is `variableKoszulDual R T q`. -/
theorem coe_varComb_eq (q : T →₀ MvPolynomial T R) :
    (varComb (ε := ε) q : MvPolynomial T R) = MvPolynomial.variableKoszulDual R T q :=
  coe_varComb q

omit [Fact (Function.Surjective ε)] in
/-- Multiplication sends `varTensor y = ∑_t x_t ⊗ y_t` to `∑_t x_t y_t`. -/
theorem mulMap_varTensor (y : T →₀ RingHom.ker (polyAug ε T)) :
    Submodule.mulMap (RingHom.ker (polyAug ε T)) (RingHom.ker (polyAug ε T)) (varTensor y) =
      MvPolynomial.variableKoszulDual R T (subVec y) := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y₁ y₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]
  | single t a =>
    rw [varTensor_single, Submodule.mulMap_tmul]
    simp [subVec, MvPolynomial.variableKoszulDual, mul_comm]

/-- `∑_t w_t x_t` has constant coefficient `0`. -/
theorem constantCoeff_variableKoszulDual (w : T →₀ MvPolynomial T R) :
    constantCoeff (MvPolynomial.variableKoszulDual R T w) = 0 := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add w₁ w₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, add_zero]
  | single t s => simp [MvPolynomial.variableKoszulDual]

omit [Fact (Function.Surjective ε)] in
/-- Every element of `J₁` is a constant of `J` plus a combination of the variables. -/
theorem exists_constIdeal_add_varComb (a : RingHom.ker (polyAug ε T)) :
    ∃ (a₀ : RingHom.ker ε) (q : T →₀ MvPolynomial T R), a = constIdeal a₀ + varComb q := by
  set a₀ := kerMap constantCoeff (comp_constantCoeff ε T) a
  have hp : (a : MvPolynomial T R) - C (constantCoeff (a : MvPolynomial T R)) ∈
      (Ideal.span (Set.range MvPolynomial.X) : Ideal (MvPolynomial T R)) := by
    rw [← MvPolynomial.augmentation_ker_eq_variableIdeal, MvPolynomial.eval₂Hom_zero,
      RingHom.mem_ker]
    simp
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hp
  refine ⟨a₀, c, Subtype.ext ?_⟩
  rw [Submodule.coe_add, coe_constIdeal, coe_varComb, Finsupp.linearCombination_apply, hc]
  change _ = C (constantCoeff (a : MvPolynomial T R)) + _
  ring

/-- Scaling a vector of `S^{(T)}` into `(J/J²)^{(T)}` by a class `c`. -/
def cotScale (c : (RingHom.ker ε).Cotangent) :
    (T →₀ MvPolynomial T R) →+ (T →₀ (RingHom.ker ε).Cotangent) :=
  Finsupp.mapRange.addMonoidHom
    ((LinearMap.toSpanSingleton B _ c).toAddMonoidHom.comp (polyAug ε T).toAddMonoidHom)

/-- `polyMixed (cotScale ā₀ q)` is the antisymmetric tensor of `∑_t q_t x_t` and `a₀`. -/
theorem polyMixed_cotScale (a₀ : RingHom.ker ε) (q : T →₀ MvPolynomial T R) :
    polyMixed (cotScale ((RingHom.ker ε).toCotangent a₀) q) =
      antisymm (varComb q) (constIdeal a₀) := by
  induction q using Finsupp.induction_linear with
  | zero => simp [antisymm_zero_left]
  | add q₁ q₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, antisymm_add_left]
  | single t s =>
    simp only [cotScale, Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single,
      AddMonoidHom.coe_comp, Function.comp_apply, RingHom.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe, LinearMap.toAddMonoidHom_coe, LinearMap.toSpanSingleton_apply,
      polyMixed_single, map_smul, polyMixedAt_toCotangent]
    rw [algebraMap_smul_mulKernel, varComb, Finsupp.linearCombination_single, antisymm_smul_left]

/-- **Normal form** of an element of `J₁ ⊗_S J₁`. -/
theorem exists_normalForm
    (y : RingHom.ker (polyAug ε T) ⊗[MvPolynomial T R] RingHom.ker (polyAug ε T)) :
    ∃ (u : RingHom.ker ε ⊗[R] RingHom.ker ε) (v : T →₀ RingHom.ker (polyAug ε T))
      (m : T →₀ (RingHom.ker ε).Cotangent),
      y = tensorMap C (polyAug_comp_C ε T) u + varTensor v +
        (polyMixed m : RingHom.ker (polyAug ε T) ⊗[MvPolynomial T R] _) := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, 0, by simp⟩
  | add x y hx hy =>
    obtain ⟨u, v, m, rfl⟩ := hx
    obtain ⟨u', v', m', rfl⟩ := hy
    refine ⟨u + u', v + v', m + m', ?_⟩
    rw [map_add, map_add, map_add, Submodule.coe_add]
    abel
  | tmul a b =>
    obtain ⟨a₀, q, rfl⟩ := exists_constIdeal_add_varComb a
    obtain ⟨b₀, q', rfl⟩ := exists_constIdeal_add_varComb b
    refine ⟨a₀ ⊗ₜ b₀, scaleVec (constIdeal a₀) q' + scaleVec (constIdeal b₀) q +
      scaleVec (varComb q') q, -cotScale ((RingHom.ker ε).toCotangent a₀) q', ?_⟩
    rw [tensorMap_tmul, map_add, map_add, varTensor_scaleVec, varTensor_scaleVec,
      varTensor_scaleVec, map_neg, polyMixed_cotScale, Submodule.coe_neg, coe_antisymm,
      TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.tmul_add]
    change _ = constIdeal a₀ ⊗ₜ constIdeal b₀ + _ + _
    abel

/-- The Koszul differential of the variables sends `a ∧ b` to `φ(a) b - φ(b) a`, where
`φ = variableKoszulDual R T`. -/
theorem koszul_d_ιMulti (a b : T →₀ MvPolynomial T R) :
    exteriorPower.oneEquiv _ _
        (Koszul.d (MvPolynomial.variableKoszulDual R T) 1
          (exteriorPower.ιMulti (MvPolynomial T R) 2 ![a, b])) =
      MvPolynomial.variableKoszulDual R T a • b - MvPolynomial.variableKoszulDual R T b • a := by
  set φ := MvPolynomial.variableKoszulDual R T
  have h : Koszul.d φ 1 (exteriorPower.ιMulti (MvPolynomial T R) 2 ![a, b]) =
      φ a • exteriorPower.ιMulti (MvPolynomial T R) 1 ![b] -
        φ b • exteriorPower.ιMulti (MvPolynomial T R) 1 ![a] := by
    apply Subtype.ext
    have e0 : (![a, b] ∘ (0 : Fin 2).succAbove) = ![b] := by
      funext i; fin_cases i; rfl
    have e1 : (![a, b] ∘ (1 : Fin 2).succAbove) = ![a] := by
      funext i; fin_cases i; rfl
    rw [Koszul.d_apply_coe, exteriorPower.ιMulti_apply_coe, Koszul.contraction_ιMulti,
      Fin.sum_univ_two, e0, e1]
    simp [sub_eq_add_neg]
  rw [h, map_sub, map_smul, map_smul, exteriorPower.oneEquiv_ιMulti,
    exteriorPower.oneEquiv_ιMulti]
  rfl

/-- Every Koszul boundary `d w` of the variables is the underlying vector of some
`y ∈ J₁^{(T)}` with `varTensor y` in the image of `polyWedge`. -/
theorem exists_koszulLift [LinearOrder T]
    (w : ⋀[MvPolynomial T R]^2 (T →₀ MvPolynomial T R)) :
    ∃ y : T →₀ RingHom.ker (polyAug ε T),
      subVec y = exteriorPower.oneEquiv _ _ (Koszul.d (MvPolynomial.variableKoszulDual R T) 1 w) ∧
        ∃ z : ⋀[B]^2 (T →₀ B),
          (polyWedge (ε := ε) z : RingHom.ker (polyAug ε T) ⊗[MvPolynomial T R] _) =
            varTensor y := by
  have hw : w ∈ Submodule.span (MvPolynomial T R)
      (Set.range (exteriorPower.ιMulti (MvPolynomial T R) 2)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
    rw [hv, koszul_d_ιMulti]
    refine ⟨scaleVec (varComb (v 0)) (v 1) - scaleVec (varComb (v 1)) (v 0), ?_,
      wedgeBilin (reduceVec (ε := ε) (v 1)) (reduceVec (ε := ε) (v 0)), ?_⟩
    · rw [map_sub, subVec_scaleVec, subVec_scaleVec, coe_varComb_eq, coe_varComb_eq]
    · rw [polyWedge_wedge, ← antisymm_varComb, coe_antisymm, map_sub, varTensor_scaleVec,
        varTensor_scaleVec]
  | zero => exact ⟨0, by simp, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨y₁, h₁, z₁, hz₁⟩ := hx
    obtain ⟨y₂, h₂, z₂, hz₂⟩ := hy
    exact ⟨y₁ + y₂, by rw [map_add, h₁, h₂, map_add, map_add], z₁ + z₂, by
      rw [map_add, Submodule.coe_add, hz₁, hz₂, map_add]⟩
  | smul s x _ hx =>
    obtain ⟨y₁, h₁, z₁, hz₁⟩ := hx
    refine ⟨s • y₁, by rw [subVec_smul, h₁, map_smul, map_smul], polyAug ε T s • z₁, ?_⟩
    rw [map_smul, algebraMap_smul_mulKernel, Submodule.coe_smul, hz₁, varTensor_smul]

/-- If `∑_t x_t y_t = 0`, then `varTensor y` lies in the image of `polyWedge`. -/
theorem exists_polyWedge_eq_varTensor (y : T →₀ RingHom.ker (polyAug ε T))
    (hy : MvPolynomial.variableKoszulDual R T (subVec y) = 0) :
    ∃ z : ⋀[B]^2 (T →₀ B),
      (polyWedge (ε := ε) z : RingHom.ker (polyAug ε T) ⊗[MvPolynomial T R] _) =
        varTensor y := by
  classical
  let : LinearOrder T := linearOrderOfSTO WellOrderingRel
  set φ := MvPolynomial.variableKoszulDual R T
  set x := (exteriorPower.oneEquiv (MvPolynomial T R) (T →₀ MvPolynomial T R)).symm (subVec y)
  have hx : x ∈ LinearMap.ker (Koszul.d φ 0) := by
    rw [LinearMap.mem_ker]
    apply (exteriorPower.zeroEquiv (MvPolynomial T R) (T →₀ MvPolynomial T R)).injective
    rw [MvPolynomial.koszul_zeroEquiv_d_zero, LinearEquiv.apply_symm_apply, hy, map_zero]
  rw [← MvPolynomial.variableKoszul_exact_positive R T 0] at hx
  obtain ⟨w, hw⟩ := hx
  obtain ⟨y', hy', hz⟩ := exists_koszulLift (ε := ε) w
  have : y' = y := by
    apply subVec_injective
    rw [hy']
    change exteriorPower.oneEquiv _ _ (Koszul.d φ (0 + 1) w) = _
    rw [hw, LinearEquiv.apply_symm_apply]
  rwa [this] at hz

/-- The map from the three summands is surjective. -/
theorem polyDecompositionMap_surjective :
    Function.Surjective (polyDecompositionMap (ε := ε) (T := T)) := by
  intro x
  obtain ⟨u, v, m, hy⟩ := exists_normalForm (x : RingHom.ker (polyAug ε T) ⊗[_] _)
  have hmul := (mem_mulKernel_iff _).mp x.2
  rw [hy, map_add, map_add, mulMap_tensorMap, mulMap_varTensor,
    (mem_mulKernel_iff _).mp (polyMixed m).2, add_zero] at hmul
  have hu : Submodule.mulMap (RingHom.ker ε) (RingHom.ker ε) u = 0 := by
    have := congrArg constantCoeff hmul
    rwa [map_add, constantCoeff_C, constantCoeff_variableKoszulDual, add_zero, map_zero] at this
  have hv : MvPolynomial.variableKoszulDual R T (subVec v) = 0 := by
    rwa [hu, map_zero, zero_add] at hmul
  obtain ⟨z, hz⟩ := exists_polyWedge_eq_varTensor v hv
  refine ⟨(z, m, ⟨u, (mem_mulKernel_iff u).mpr hu⟩), Subtype.ext ?_⟩
  change (polyWedge (ε := ε) z :
      RingHom.ker (polyAug ε T) ⊗[MvPolynomial T R] RingHom.ker (polyAug ε T)) +
    ((polyMixed m : RingHom.ker (polyAug ε T) ⊗[MvPolynomial T R] RingHom.ker (polyAug ε T)) +
      (tensorMap C (polyAug_comp_C ε T) u)) = x
  rw [hy, hz]
  abel

end Surjectivity

/-! ### The decomposition -/

/-- **Stacks 09D6, the decomposition of `Tor₂^{P₁}(B, B)`.** For `S = R[x_t, t ∈ T]` augmented
to `B` through `x_t ↦ 0` and the surjection `ε : R → B` with kernel `J`,

`Tor₂^S(B, B) = ∧²_B(⨁_{t ∈ T} B) ⊕ ⨁_{t ∈ T} J/J² ⊕ Tor₂^R(B, B)`

in the tensor-kernel model, as `B`-modules. The three correspondences are
`polyDecomposition_wedge`, `polyDecomposition_mixed` and `polyDecomposition_degen`. -/
def polyDecomposition :
    (⋀[B]^2 (T →₀ B) × (T →₀ (RingHom.ker ε).Cotangent) × mulKernel ε) ≃ₗ[B]
      mulKernel (polyAug ε T) :=
  LinearEquiv.ofBijective polyDecompositionMap
    ⟨polyDecompositionMap_injective, polyDecompositionMap_surjective⟩

/-- The basis element `x_t ∧ x_{t'}` of the first summand is `x_t ⊗ x_{t'} - x_{t'} ⊗ x_t`. -/
theorem polyDecomposition_wedge (t t' : T) :
    polyDecomposition (ε := ε)
        (wedgeBilin (Finsupp.single t 1) (Finsupp.single t' 1), 0, 0) =
      antisymm (xVar t) (xVar t') := by
  change polyWedge (ε := ε) (wedgeBilin (Finsupp.single t 1) (Finsupp.single t' 1)) +
    (polyMixed 0 + polyDegen 0) = _
  rw [map_zero, map_zero, add_zero, add_zero, polyWedge_single]

/-- The element `x_t ⊗ f̄` of the second summand (`f ∈ J`) is `x_t ⊗ s₀(f) - s₀(f) ⊗ x_t`. -/
theorem polyDecomposition_mixed (t : T) (f : RingHom.ker ε) :
    polyDecomposition (ε := ε) (0, Finsupp.single t ((RingHom.ker ε).toCotangent f), 0) =
      antisymm (xVar t) (constIdeal f) := by
  change polyWedge 0 + (polyMixed (Finsupp.single t ((RingHom.ker ε).toCotangent f)) +
    polyDegen 0) = _
  rw [map_zero, map_zero, add_zero, zero_add, polyMixed_single, polyMixedAt_toCotangent]

/-- The last summand is embedded by `s₀ : R → S`. -/
theorem polyDecomposition_degen (k : mulKernel ε) :
    polyDecomposition (ε := ε) (T := T) (0, 0, k) = mulKernelMap C (polyAug_comp_C ε T) k := by
  change polyWedge 0 + (polyMixed 0 + polyDegen k) = _
  rw [map_zero, map_zero, zero_add, zero_add]
  rfl

/-! ### The alternating face `d₀ - d₁` -/

section Faces

variable {f : T → R} (hf : ∀ t, ε (f t) = 0)

/-- The generator `f_t` as an element of `J`. -/
def relationIdeal (t : T) : RingHom.ker ε := ⟨f t, hf t⟩

/-- Evaluation at `f` restricted to the constants is the identity of `R`. -/
theorem eval_comp_C : (eval f).comp (C : R →+* MvPolynomial T R) = RingHom.id R := by
  ext r
  simp

/-- **`d₀ - d₁ : Tor₂^S(B, B) → Tor₂^R(B, B)`** on the model, for the `R`-algebra maps
`d₀, d₁ : S → R` with `d₀(x_t) = 0` and `d₁(x_t) = f_t`. -/
def polyFace : mulKernel (polyAug ε T) →ₗ[B] mulKernel ε :=
  mulKernelMap constantCoeff (comp_constantCoeff ε T) - mulKernelMap (eval f) (comp_eval ε T hf)

omit [Fact (Function.Surjective ε)] in
/-- `d₁(x_t) = f_t`, as an element of `J`. -/
theorem kerMap_eval_xVar (t : T) :
    kerMap (eval f) (comp_eval ε T hf) (xVar t) = relationIdeal hf t :=
  Subtype.ext (by simp [relationIdeal])

omit [Fact (Function.Surjective ε)] in
/-- `d₁` fixes the constant `a ∈ J`. -/
theorem kerMap_eval_constIdeal (a : RingHom.ker ε) :
    kerMap (eval f) (comp_eval ε T hf) (constIdeal a) = a :=
  Subtype.ext (by simp)

/-- `d₀ - d₁` vanishes on the image of `s₀`, since `d₀ s₀ = d₁ s₀ = id`. -/
theorem polyFace_degen (k : mulKernel ε) :
    polyFace hf (mulKernelMap C (polyAug_comp_C ε T) k) = 0 := by
  rw [polyFace, LinearMap.sub_apply, ← mulKernelMap_comp, ← mulKernelMap_comp,
    mulKernelMap_congr (constantCoeff_comp_C R T) _ (RingHom.comp_id ε),
    mulKernelMap_congr (eval_comp_C (f := f)) _ (RingHom.comp_id ε), sub_self]

/-- `d₀ - d₁` sends `x_t ⊗ f - f ⊗ x_t` to `f ⊗ f_t - f_t ⊗ f`. -/
theorem polyFace_mixed (t : T) (a : RingHom.ker ε) :
    polyFace hf (antisymm (xVar t) (constIdeal a)) = antisymm a (relationIdeal hf t) := by
  rw [polyFace, LinearMap.sub_apply, mulKernelMap_antisymm, mulKernelMap_antisymm,
    kerMap_constantCoeff_xVar, antisymm_zero_left, kerMap_eval_xVar hf, kerMap_eval_constIdeal hf,
    zero_sub, ← antisymm_swap]

/-- `d₀ - d₁` sends `x_t ⊗ x_{t'} - x_{t'} ⊗ x_t` to `f_{t'} ⊗ f_t - f_t ⊗ f_{t'}`. -/
theorem polyFace_wedge (t t' : T) :
    polyFace hf (antisymm (xVar t) (xVar t')) =
      antisymm (relationIdeal hf t') (relationIdeal hf t) := by
  rw [polyFace, LinearMap.sub_apply, mulKernelMap_antisymm, mulKernelMap_antisymm,
    kerMap_constantCoeff_xVar, antisymm_zero_left, kerMap_eval_xVar hf, kerMap_eval_xVar hf,
    zero_sub, ← antisymm_swap]

/-- `B^{(T)} → J/J²`, `e_t ↦ f̄_t`. -/
def relationCotangent : (T →₀ B) →ₗ[B] (RingHom.ker ε).Cotangent :=
  Finsupp.linearCombination B fun t => (RingHom.ker ε).toCotangent (relationIdeal hf t)

/-- `(J/J²)^{(T)} → ∧²(J/J²)`, `c e_t ↦ c ∧ f̄_t`. -/
def mixedWedge : (T →₀ (RingHom.ker ε).Cotangent) →ₗ[B] ⋀[B]^2 (RingHom.ker ε).Cotangent :=
  Finsupp.lsum ℕ fun t => wedgeBilin.flip ((RingHom.ker ε).toCotangent (relationIdeal hf t))

/-- On the first summand, `d₀ - d₁` is minus the antisymmetrisation of `∧²` of `e_t ↦ f̄_t`. -/
theorem polyFace_polyWedge (w : ⋀[B]^2 (T →₀ B)) :
    polyFace hf (polyWedge w) =
      wedgeAntisymm (-(exteriorPower.map 2 (relationCotangent hf) w)) :=
  map_polyWedge_eq (polyFace hf) (wedgeAntisymm ∘ₗ (-(exteriorPower.map 2 (relationCotangent hf))))
    (fun t t' => by
      rw [polyFace_wedge, LinearMap.comp_apply, LinearMap.neg_apply, wedgeBilin_apply,
        exteriorPower.map_apply_ιMulti]
      have e : (relationCotangent hf ∘ ![Finsupp.single t (1 : B), Finsupp.single t' 1]) =
          ![(RingHom.ker ε).toCotangent (relationIdeal hf t),
            (RingHom.ker ε).toCotangent (relationIdeal hf t')] := by
        funext i; fin_cases i <;> simp [relationCotangent]
      rw [e, ← wedgeBilin_apply, map_neg, wedgeAntisymm_wedge, antisymm_swap]) w

/-- On the second summand, `d₀ - d₁` is the antisymmetrisation of `mixedWedge`. -/
theorem polyFace_polyMixed (m : T →₀ (RingHom.ker ε).Cotangent) :
    polyFace hf (polyMixed m) = wedgeAntisymm (mixedWedge hf m) :=
  map_polyMixed_eq (polyFace hf) (wedgeAntisymm ∘ₗ mixedWedge hf) (fun t a => by
    rw [polyFace_mixed, LinearMap.comp_apply, mixedWedge, Finsupp.lsum_single,
      LinearMap.flip_apply, wedgeAntisymm_wedge]) m

/-- **The image of `d₀ - d₁` is the image of `∧²_B(J/J²)`**, when the `f_t` generate `J`. -/
theorem range_polyFace (hspan : Ideal.span (Set.range f) = RingHom.ker ε) :
    LinearMap.range (polyFace (T := T) hf) = LinearMap.range (wedgeAntisymm (φ := ε)) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨⟨w, m, k⟩, rfl⟩ := polyDecompositionMap_surjective (ε := ε) (T := T) x
    have hd : polyDecompositionMap (w, m, k) = polyWedge w + (polyMixed m + polyDegen k) := rfl
    rw [hd, map_add, map_add, polyFace_polyWedge, polyFace_polyMixed, polyDegen, polyFace_degen,
      add_zero, ← map_add]
    exact LinearMap.mem_range_self _ _
  · rw [LinearMap.range_eq_map, ← exteriorPower.ιMulti_span, Submodule.map_span_le]
    rintro _ ⟨v, rfl⟩
    rw [ιMulti_eq_wedgeBilin]
    obtain ⟨a, ha⟩ := Ideal.toCotangent_surjective _ (v 0)
    obtain ⟨b, hb⟩ := Ideal.toCotangent_surjective _ (v 1)
    rw [← ha, ← hb]
    have hbmem : (b : R) ∈ Submodule.span R (Set.range f) := by
      rw [← Ideal.span, hspan]
      exact b.2
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hbmem
    have hbc : b = Finsupp.linearCombination R (relationIdeal hf) c := by
      apply Subtype.ext
      change _ = (RingHom.ker ε).subtype (Finsupp.linearCombination R (relationIdeal hf) c)
      rw [Finsupp.apply_linearCombination, Finsupp.linearCombination_apply, ← hc]
      rfl
    rw [hbc]
    clear hbc hc hbmem hb ha
    induction c using Finsupp.induction_linear with
    | zero =>
      simp only [map_zero]
      exact Submodule.zero_mem _
    | add c₁ c₂ h₁ h₂ =>
      rw [map_add, map_add, map_add, map_add]
      exact Submodule.add_mem _ h₁ h₂
    | single t r =>
      rw [Finsupp.linearCombination_single, map_smul, ← algebraMap_smul_cotangent, map_smul,
        map_smul, wedgeAntisymm_wedge, ← polyFace_mixed hf t a, ← map_smul]
      exact LinearMap.mem_range_self _ _

/-- **The exact sequence `∧²_B(J/J²) → Tor₂^R(B, B) → Coker(d₀ - d₁) → 0`**, exactness in the
middle, when the `f_t` generate `J`. -/
theorem exact_wedgeAntisymm_polyFace (hspan : Ideal.span (Set.range f) = RingHom.ker ε) :
    Function.Exact (wedgeAntisymm (φ := ε)) (LinearMap.range (polyFace (T := T) hf)).mkQ := by
  rw [LinearMap.exact_iff, Submodule.ker_mkQ, range_polyFace hf hspan]

end Faces

end Stacks.Cotangent.TorTwo

end
