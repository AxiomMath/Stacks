module

import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Tactic.LinearCombination
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Presentations of symmetric and exterior powers from a presentation of the module

Let `R` be a commutative ring and `M` an `R`-module. For `n ≥ 0`, the `n`-th symmetric power
`Symⁿ_R(M)` is the degree-`n` graded piece of the symmetric algebra `Sym_R(M)`, and the `n`-th
exterior power `⋀ⁿ_R(M)` is the degree-`n` graded piece of the exterior algebra `⋀_R(M)`. Both
are functorial: an `R`-module homomorphism `f : M → N` induces `Symⁿ(f)` and `⋀ⁿ(f)`.

## Main results

Let `M₂ --g--> M₁ --f--> M → 0` be an exact sequence of `R`-modules, so `f` is surjective and
`im g = ker f`, and fix `n ≥ 1`. Then there are exact sequences

* `M₂ ⊗ Sym^{n-1}(M₁) --α--> Symⁿ(M₁) --Symⁿ(f)--> Symⁿ(M) → 0`, with `Symⁿ(f)` surjective and
  `α (m₂ ⊗ (y₁⋯y_{n-1})) = g(m₂) · y₁⋯y_{n-1}`;
* `M₂ ⊗ ⋀^{n-1}(M₁) --β--> ⋀ⁿ(M₁) --⋀ⁿ(f)--> ⋀ⁿ(M) → 0`, with `⋀ⁿ(f)` surjective and
  `β (m₂ ⊗ (y₁∧⋯∧y_{n-1})) = g(m₂) ∧ y₁ ∧ ⋯ ∧ y_{n-1}`.

## Implementation notes

The index is reindexed as `n = k + 1` with `k ≥ 0`, which is equivalent to `n ≥ 1` and avoids
natural-number subtraction; then `Sym^{n-1} = Sym^k` and `⋀^{n-1} = ⋀^k`.

The exterior power `⋀[R]^n M` is Mathlib's `exteriorPower`, the `n`-th power of
`LinearMap.range (ExteriorAlgebra.ι R)` inside `ExteriorAlgebra R M`, i.e. the degree-`n` graded
piece. The symmetric power is modelled analogously as the `n`-th power of
`LinearMap.range (SymmetricAlgebra.ι R M)` inside `SymmetricAlgebra R M`.

The functorial map on exterior powers is `exteriorPower.map`; the functorial map on symmetric
powers is built as the restriction of the induced algebra homomorphism on symmetric algebras.

Both `α` and `β` are "apply `g` to the first factor, then multiply (respectively wedge) in the
symmetric (respectively exterior) algebra".
-/

@[expose] public section

open scoped TensorProduct

/-! ## Symmetric powers -/

namespace SymPow

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- The functorial algebra homomorphism on symmetric algebras induced by `f : M →ₗ[R] N`. -/
@[ega "II 1.7.1" "partial",
  ega "II 1.7.2" "special case",
  ega "II 2.9.5" "symmetric-algebra target",
  ega "II 4.1.2" "special case"]
noncomputable def symAlgMap (f : M →ₗ[R] N) :
    SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R N :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι R N).comp f)

/-- On degree-`1` generators, `Sym(f)` sends `x` to `f x`, i.e. `Sym^n(f)`
sends `x₁⋯xₙ` to `f(x₁)⋯f(xₙ)`. -/
@[ega "II 1.7.1" "partial", ega "II 2.9.5" "special case"]
theorem symAlgMap_ι (f : M →ₗ[R] N) (m : M) :
    symAlgMap f (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι R N (f m) := by
  simp [symAlgMap, SymmetricAlgebra.lift_ι_apply]

section Functoriality

variable {P : Type*} [AddCommMonoid P] [Module R P]

/-- The induced algebra homomorphism sends a product of degree-one generators `ι (v i)` to the
product of the `ι (f (v i))`. -/
theorem symAlgMap_prod_ι (f : M →ₗ[R] N) (n : ℕ) (v : Fin n → M) :
    symAlgMap f (∏ i : Fin n, SymmetricAlgebra.ι R M (v i)) =
      ∏ i : Fin n, SymmetricAlgebra.ι R N (f (v i)) :=
  (map_prod (symAlgMap f) _ Finset.univ).trans
    (Finset.prod_congr rfl fun i _ => symAlgMap_ι f (v i))

end Functoriality

/-- The `n`-th symmetric power `Sym^n_R(M)`: the degree-`n` graded piece of the
symmetric algebra, i.e. the `n`-th power of the degree-`1` part. -/
@[ega "II 1.7.1", sga "3 VIIA 4.3.3", sga "3 VIIB 1.2.4" "special case", sga "6 II AppII.1.2.4"]
abbrev symmetricPower (n : ℕ) (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M] :
    Submodule R (SymmetricAlgebra R M) :=
  (LinearMap.range (SymmetricAlgebra.ι R M)) ^ n

/-- The image of `symmetricPower n R M` under `symAlgMap f` lies in `symmetricPower n R N`. -/
private theorem map_symmetricPower_le (n : ℕ) (f : M →ₗ[R] N) :
    (symmetricPower n R M).map (symAlgMap f).toLinearMap ≤ symmetricPower n R N := by
  unfold symmetricPower
  rw [Submodule.map_pow]
  apply pow_le_pow_left'
  rintro _ ⟨x, ⟨m, rfl⟩, rfl⟩
  exact ⟨f m, by simp [symAlgMap_ι]⟩

/-- `symAlgMap f` maps the degree-`n` piece of `M` into the degree-`n` piece of `N`. -/
@[ega "II 4.1.2" "Affine case"]
theorem symAlgMap_mapsTo (n : ℕ) (f : M →ₗ[R] N) :
    ∀ x ∈ symmetricPower n R M, (symAlgMap f).toLinearMap x ∈ symmetricPower n R N :=
  fun x hx => map_symmetricPower_le n f ⟨x, hx, rfl⟩

/-- `Sym^n(f)`: the functorial map on symmetric powers induced by `f : M →ₗ[R] N`. -/
@[ega "II 4.1.2" "Affine case"]
noncomputable def symMap (n : ℕ) (f : M →ₗ[R] N) :
    symmetricPower n R M →ₗ[R] symmetricPower n R N :=
  (symAlgMap f).toLinearMap.restrict (symAlgMap_mapsTo n f)

/-- The image of `symmetricPower n R M` under `symAlgMap f` equals `symmetricPower n R N`
when `f` is surjective. -/
@[ega "0 19.5.1" "partial", ega "II 4.1.2" "special case"]
theorem symmetricPower_map_eq (n : ℕ) (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    (symmetricPower n R M).map (symAlgMap f).toLinearMap = symmetricPower n R N := by
  refine (map_symmetricPower_le n f).antisymm ?_
  unfold symmetricPower
  rw [Submodule.map_pow]
  apply pow_le_pow_left'
  rintro _ ⟨n0, rfl⟩
  obtain ⟨m, rfl⟩ := hf n0
  exact ⟨SymmetricAlgebra.ι R M m, ⟨m, rfl⟩, by simp [symAlgMap_ι]⟩

/-- `Sym^n(f)` is computed by applying the underlying algebra homomorphism. -/
theorem symMap_coe (n : ℕ) (f : M →ₗ[R] N) (x : symmetricPower n R M) :
    (symMap n f x : SymmetricAlgebra R N) = symAlgMap f x := rfl

/-- `Sym^n(f)` is surjective when `f` is surjective. -/
@[ega "II 4.1.2" "special case"]
theorem symMap_surjective (n : ℕ) (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Function.Surjective (symMap n f) := by
  rintro ⟨z, hz⟩
  rw [← symmetricPower_map_eq n f hf] at hz
  obtain ⟨x, hx, hxz⟩ := hz
  exact ⟨⟨x, hx⟩, Subtype.ext (by simpa [symMap_coe] using hxz)⟩

section SymMapFunctoriality

variable {P : Type*} [AddCommMonoid P] [Module R P]

/-- The map induced on `Symⁿ` by a composite is the composite of the induced maps. -/
theorem symMap_comp (n : ℕ) (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    symMap n (g ∘ₗ f) = (symMap n g).comp (symMap n f) :=
  LinearMap.ext fun x => Subtype.ext <| DFunLike.congr_fun
    (show symAlgMap (g ∘ₗ f) = (symAlgMap g).comp (symAlgMap f) from
      SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => by simp [symAlgMap_ι]))
    (x : SymmetricAlgebra R M)

/-- The map induced on `Symⁿ` by the identity is the identity. -/
theorem symMap_id (n : ℕ) : symMap n (LinearMap.id : M →ₗ[R] M) = LinearMap.id :=
  LinearMap.ext fun x => Subtype.ext <| DFunLike.congr_fun
    (show symAlgMap (LinearMap.id : M →ₗ[R] M) = AlgHom.id R _ from
      SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => by simp [symAlgMap_ι]))
    (x : SymmetricAlgebra R M)

/-- A linear map with a left inverse induces an injective map on `Symⁿ`. -/
theorem symMap_injective_of_leftInverse (n : ℕ) (f : M →ₗ[R] N) (g : N →ₗ[R] M)
    (hgf : g ∘ₗ f = LinearMap.id) : Function.Injective (symMap n f) := by
  intro x y hxy
  have h : symMap n g (symMap n f x) = symMap n g (symMap n f y) := congrArg _ hxy
  rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← symMap_comp, hgf, symMap_id,
    LinearMap.id_apply, LinearMap.id_apply] at h

/-- `Symⁿ` of a linear equivalence composed with `Symⁿ` of its inverse is the identity. -/
theorem symMap_comp_symMap_symm (n : ℕ) (e : M ≃ₗ[R] N) :
    (symMap n (e : M →ₗ[R] N)).comp (symMap n (e.symm : N →ₗ[R] M)) = LinearMap.id := by
  rw [← symMap_comp n (e.symm : N →ₗ[R] M) (e : M →ₗ[R] N),
    show ((e : M →ₗ[R] N) ∘ₗ (e.symm : N →ₗ[R] M)) = LinearMap.id from
      LinearMap.ext fun y => e.apply_symm_apply y]
  exact symMap_id n

/-- The degree-`n` equivalence of symmetric powers induced by a linear equivalence. -/
noncomputable def symmetricPowerCongr (n : ℕ) (e : M ≃ₗ[R] N) :
    symmetricPower n R M ≃ₗ[R] symmetricPower n R N :=
  LinearEquiv.ofLinear (symMap n (e : M →ₗ[R] N)) (symMap n (e.symm : N →ₗ[R] M))
    (symMap_comp_symMap_symm n e)
    (by simpa using symMap_comp_symMap_symm n e.symm)

/-- The equivalence `symmetricPowerCongr n e` acts as the map `symMap n e` induced by `e`. -/
@[simp] theorem symmetricPowerCongr_apply (n : ℕ) (e : M ≃ₗ[R] N)
    (y : symmetricPower n R M) : symmetricPowerCongr n e y = symMap n (e : M →ₗ[R] N) y :=
  rfl

end SymMapFunctoriality

variable {M₁ M₂ : Type*} [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]

/-- Multiplying a degree-`1` element `ι m` by a degree-`k` element lands in degree `k+1`. -/
theorem mul_mem_succ (k : ℕ) (m : M₁) (y : symmetricPower k R M₁) :
    SymmetricAlgebra.ι R M₁ m * (y : SymmetricAlgebra R M₁) ∈ symmetricPower (k+1) R M₁ := by
  unfold symmetricPower
  rw [pow_succ']
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ m) y.property

/-- The bilinear map `(m₂, y) ↦ ι(g m₂) * y` into `Sym^{k+1}(M₁)`. -/
noncomputable def symMulMapBil (k : ℕ) (g : M₂ →ₗ[R] M₁) :
    M₂ →ₗ[R] symmetricPower k R M₁ →ₗ[R] symmetricPower (k+1) R M₁ where
  toFun m₂ :=
    { toFun := fun y => ⟨SymmetricAlgebra.ι R M₁ (g m₂) * (y : SymmetricAlgebra R M₁),
        mul_mem_succ k (g m₂) y⟩
      map_add' := by intro y z; ext; simp [mul_add]
      map_smul' := by intro c y; ext; simp }
  map_add' := by intro a b; ext y; simp [map_add, add_mul]
  map_smul' := by intro c a; ext y; simp [map_smul]

/-- The map `α : M₂ ⊗ Sym^k(M₁) → Sym^{k+1}(M₁)`,
`m₂ ⊗ (y₁⋯y_k) ↦ g(m₂)·y₁⋯y_k`. -/
noncomputable def symMulMap (k : ℕ) (g : M₂ →ₗ[R] M₁) :
    M₂ ⊗[R] symmetricPower k R M₁ →ₗ[R] symmetricPower (k+1) R M₁ :=
  TensorProduct.lift (symMulMapBil k g)

/-- `α(m₂ ⊗ (y₁⋯y_k)) = g(m₂)·y₁⋯y_k`. -/
theorem symMulMap_tmul (k : ℕ) (g : M₂ →ₗ[R] M₁) (m₂ : M₂) (y : symmetricPower k R M₁) :
    (symMulMap k g (m₂ ⊗ₜ y) : SymmetricAlgebra R M₁)
      = SymmetricAlgebra.ι R M₁ (g m₂) * (y : SymmetricAlgebra R M₁) := rfl

end SymPow

/-- A conditional element `if p then a else 0` lies in `S` once `a ∈ S` whenever `p` holds. -/
private theorem ite_zero_mem {R A : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    (S : Submodule R A) {p : Prop} [Decidable p] {a : A} (h : p → a ∈ S) :
    (if p then a else 0) ∈ S :=
  ite_mem.2 ⟨h, fun _ => S.zero_mem⟩

/-! ### The degree map and the section map for symmetric algebras

The degree-tracking algebra map `degreeMap : Sym(M₁) → Sym(M₁)[X]`, sending `ι m ↦ C(ι m)·X`,
and the section algebra map `sectionAlgHom : Sym(M) → Sym(M₁)/I`, where `I` is the ideal
generated by `ι(range g)`. -/

namespace SymPow

section

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

open Polynomial

/-- The degree-tracking linear map `m ↦ C(ι m) * X`. -/
noncomputable def degreeMapLin : M →ₗ[R] Polynomial (SymmetricAlgebra R M) :=
  (LinearMap.mulRight R (Polynomial.X : Polynomial (SymmetricAlgebra R M))).comp
    ((Polynomial.CAlgHom.toLinearMap).comp (SymmetricAlgebra.ι R M))

/-- The degree-tracking algebra map `degreeMap : Sym(M) → Sym(M)[X]`, `ι m ↦ C(ι m)·X`.
On a degree-`d` element `w`, `degreeMap w = C w · X^d`. -/
noncomputable def degreeMap : SymmetricAlgebra R M →ₐ[R] Polynomial (SymmetricAlgebra R M) :=
  SymmetricAlgebra.lift degreeMapLin

/-- `degreeMap` sends a degree-`1` generator `ι m` to `C (ι m) * X`. -/
theorem degreeMap_ι (m : M) : degreeMap (SymmetricAlgebra.ι R M m)
    = Polynomial.C (SymmetricAlgebra.ι R M m) * Polynomial.X := by
  rw [degreeMap, SymmetricAlgebra.lift_ι_apply, degreeMapLin, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply,
    Polynomial.CAlgHom_apply]

/-- On degree-`d` elements, `degreeMap w = C w · X^d`. -/
theorem degreeMap_eq_of_mem (d : ℕ) (w : SymmetricAlgebra R M) (hw : w ∈ symmetricPower d R M) :
    degreeMap w = Polynomial.C w * Polynomial.X ^ d := by
  induction d generalizing w with
  | zero =>
    rw [symmetricPower, pow_zero, Submodule.mem_one] at hw
    obtain ⟨r, rfl⟩ := hw
    simp
  | succ n ih =>
    rw [symmetricPower, pow_succ'] at hw
    refine Submodule.mul_induction_on hw ?_ ?_
    · rintro _ ⟨x, rfl⟩ b hb
      rw [map_mul, degreeMap_ι, ih b hb, Polynomial.C_mul, pow_succ]
      ring
    · intro x y hx hy
      rw [map_add, hx, hy, map_add, add_mul]

/-- The symmetric algebra is generated as an `R`-algebra by the image of `ι`. -/
theorem adjoin_range_ι :
    Algebra.adjoin R (Set.range (SymmetricAlgebra.ι R M)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using SymmetricAlgebra.induction with
  | algebraMap r => exact Subalgebra.algebraMap_mem _ r
  | ι m => exact Algebra.subset_adjoin ⟨m, rfl⟩
  | mul a b ha hb => exact mul_mem ha hb
  | add a b ha hb => exact add_mem ha hb

/-- The degree-`i` coefficient of `degreeMap a` lies in `Sym^i`. -/
theorem coeff_degreeMap_mem (a : SymmetricAlgebra R M) (i : ℕ) :
    (degreeMap a).coeff i ∈ symmetricPower i R M := by
  have hmem : a ∈ Algebra.adjoin R (Set.range (SymmetricAlgebra.ι R M)) := by
    rw [adjoin_range_ι]; trivial
  induction hmem using Algebra.adjoin_induction generalizing i with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    rw [degreeMap_ι, Polynomial.coeff_C_mul_X]
    refine ite_zero_mem _ fun h => ?_
    rw [h, symmetricPower, pow_one]; exact ⟨m, rfl⟩
  | algebraMap r =>
    rw [AlgHom.commutes, Polynomial.algebraMap_apply, Polynomial.coeff_C]
    refine ite_zero_mem _ fun h => ?_
    rw [h, symmetricPower, pow_zero, Submodule.mem_one]
    exact ⟨r, rfl⟩
  | add x y hx hy ihx ihy =>
    rw [map_add, Polynomial.coeff_add]
    exact Submodule.add_mem _ (ihx i) (ihy i)
  | mul x y hx hy ihx ihy =>
    rw [map_mul, Polynomial.coeff_mul]
    apply Submodule.sum_mem
    rintro ⟨p, q⟩ hpq
    replace hpq := Finset.HasAntidiagonal.mem_antidiagonal.mp hpq
    rw [← hpq, symmetricPower, pow_add]
    exact Submodule.mul_mem_mul (ihx p) (ihy q)

variable {M₁ M₂ : Type*} [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]

/-- The ideal of `Sym(M₁)` generated by `ι(range g)`. -/
noncomputable def rangeIdeal (g : M₂ →ₗ[R] M₁) : Ideal (SymmetricAlgebra R M₁) :=
  Ideal.span (Set.range (fun a : M₂ => SymmetricAlgebra.ι R M₁ (g a)))

/-- `ι v` lies in the ideal `rangeIdeal g` whenever `v` is in the range of `g`. -/
theorem ι_mem_rangeIdeal (g : M₂ →ₗ[R] M₁) {v : M₁} (hv : v ∈ LinearMap.range g) :
    SymmetricAlgebra.ι R M₁ v ∈ rangeIdeal g := by
  obtain ⟨a, rfl⟩ := hv; exact Ideal.subset_span ⟨a, rfl⟩

/-- The degree-`1` submodule `ι (g M₂)`. -/
noncomputable abbrev rangeSubmodule (g : M₂ →ₗ[R] M₁) : Submodule R (SymmetricAlgebra R M₁) :=
  LinearMap.range ((SymmetricAlgebra.ι R M₁).comp g)

/-- The image of `α` (pushed into the full algebra) equals `rangeSubmodule * Sym^k`. -/
theorem range_symMulMap (k : ℕ) (g : M₂ →ₗ[R] M₁) :
    (LinearMap.range (symMulMap k g)).map (symmetricPower (k+1) R M₁).subtype
      = rangeSubmodule g * symmetricPower k R M₁ := by
  apply le_antisymm
  · rintro _ ⟨w, ⟨t, rfl⟩, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul m₂ y =>
      rw [Submodule.subtype_apply, symMulMap_tmul]
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ m₂) y.property
    | add a b ha hb =>
      rw [map_add]; exact Submodule.add_mem _ ha hb
  · rw [Submodule.mul_le]
    rintro _ ⟨m₂, rfl⟩ y hy
    refine ⟨symMulMap k g (m₂ ⊗ₜ ⟨y, hy⟩), ⟨_, rfl⟩, ?_⟩
    rw [Submodule.subtype_apply, symMulMap_tmul, LinearMap.comp_apply]

/-- Multiplying `P * Sym^e` by `Sym^p` gives `P * Sym^{p+e}`, for any submodule `P`. -/
theorem sym_mul_le (P : Submodule R (SymmetricAlgebra R M₁)) (p e : ℕ) :
    symmetricPower p R M₁ * (P * symmetricPower e R M₁) =
      P * symmetricPower (p+e) R M₁ := by
  rw [mul_left_comm, ← pow_add]

/-- The graded decomposition of ideal elements: an element of `I` has no degree-`0` part, and its
degree-`(d+1)` part lies in `rangeSubmodule * Sym^d`. -/
theorem rangeIdeal_degree (g : M₂ →ₗ[R] M₁) {z : SymmetricAlgebra R M₁} (hz : z ∈ rangeIdeal g) :
    (degreeMap z).coeff 0 = 0 ∧
      ∀ d : ℕ, (degreeMap z).coeff (d+1) ∈ rangeSubmodule g * symmetricPower d R M₁ := by
  rw [rangeIdeal] at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [degreeMap_ι]
    refine ⟨by simp, fun d => ?_⟩
    rw [Polynomial.coeff_C_mul_X]
    refine ite_zero_mem _ fun h => ?_
    obtain rfl := Nat.succ.inj h
    rw [symmetricPower, pow_zero, Submodule.mul_one]
    exact LinearMap.mem_range_self _ a
  | zero => simp
  | add x y hx hy ihx ihy =>
    refine ⟨?_, ?_⟩
    · rw [map_add, Polynomial.coeff_add, ihx.left, ihy.left, add_zero]
    · intro d
      rw [map_add, Polynomial.coeff_add]
      exact Submodule.add_mem _ (ihx.right d) (ihy.right d)
  | smul a x hx ih =>
    rw [smul_eq_mul, map_mul]
    refine ⟨?_, ?_⟩
    · rw [Polynomial.mul_coeff_zero, ih.left, mul_zero]
    · intro d
      rw [Polynomial.coeff_mul]
      apply Submodule.sum_mem
      rintro ⟨p, q⟩ hpq
      replace hpq := Finset.HasAntidiagonal.mem_antidiagonal.mp hpq
      rcases q with _ | e
      · rw [ih.left, mul_zero]
        exact Submodule.zero_mem _
      · rw [← show p + e = d by omega]
        exact (sym_mul_le (rangeSubmodule g) p e).le
          (Submodule.mul_mem_mul (coeff_degreeMap_mem a p) (ih.right e))

end

section

variable {R M M₁ M₂ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

/-- Two lifts of the same element have equal `ι`-image mod `I` when `ker f ≤ range g`. -/
theorem mk_ι_eq (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M)
    (hexact : LinearMap.ker f ≤ LinearMap.range g) {u v : M₁} (huv : f u = f v) :
    Ideal.Quotient.mk (rangeIdeal g) (SymmetricAlgebra.ι R M₁ u)
      = Ideal.Quotient.mk (rangeIdeal g) (SymmetricAlgebra.ι R M₁ v) := by
  rw [Ideal.Quotient.eq, ← map_sub]; apply ι_mem_rangeIdeal
  apply hexact
  rw [LinearMap.mem_ker, map_sub, huv, sub_self]

/-- The quotient map `Sym(M₁) → Sym(M₁)/I` is `R`-linear. -/
theorem mk_smul (g : M₂ →ₗ[R] M₁) (c : R) (x : SymmetricAlgebra R M₁) :
    c • Ideal.Quotient.mk (rangeIdeal g) x = Ideal.Quotient.mk (rangeIdeal g) (c • x) := by
  rw [← Ideal.Quotient.mkₐ_eq_mk R, map_smul]

/-- The well-defined linear "section" `M → Sym(M₁)/I` (via a set-theoretic section of `f`). -/
noncomputable def phiMap (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M)
    (hf : Function.Surjective f) (hexact : LinearMap.ker f ≤ LinearMap.range g) :
    M →ₗ[R] (SymmetricAlgebra R M₁ ⧸ rangeIdeal g) where
  toFun m := Ideal.Quotient.mk (rangeIdeal g) (SymmetricAlgebra.ι R M₁ (Function.surjInv hf m))
  map_add' a b := by
    have hf' : ∀ x, f (Function.surjInv hf x) = x := Function.rightInverse_surjInv hf
    rw [← map_add, ← map_add]; exact mk_ι_eq g f hexact (by rw [hf', map_add, hf', hf'])
  map_smul' c a := by
    simp only [RingHom.id_apply]
    have hf' : ∀ x, f (Function.surjInv hf x) = x := Function.rightInverse_surjInv hf
    rw [mk_smul, ← map_smul]; exact mk_ι_eq g f hexact (by rw [hf', map_smul, hf'])

/-- `phiMap` sends `m` to the class of `ι (surjInv f m)` in `Sym(M₁)/I`. -/
theorem phiMap_apply (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M)
    (hf : Function.Surjective f) (hexact : LinearMap.ker f ≤ LinearMap.range g) (m : M) :
    phiMap g f hf hexact m
      = Ideal.Quotient.mk (rangeIdeal g) (SymmetricAlgebra.ι R M₁ (Function.surjInv hf m)) := rfl

/-- The section algebra map `Ψ : Sym(M) → Sym(M₁)/I`. -/
noncomputable def sectionAlgHom (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M)
    (hf : Function.Surjective f) (hexact : LinearMap.ker f ≤ LinearMap.range g) :
    SymmetricAlgebra R M →ₐ[R] (SymmetricAlgebra R M₁ ⧸ rangeIdeal g) :=
  SymmetricAlgebra.lift (phiMap g f hf hexact)

/-- `Ψ` sends a degree-`1` generator `ι m` to `phiMap m`. -/
theorem sectionAlgHom_ι (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M)
    (hf : Function.Surjective f) (hexact : LinearMap.ker f ≤ LinearMap.range g) (m : M) :
    sectionAlgHom g f hf hexact (SymmetricAlgebra.ι R M m) = phiMap g f hf hexact m := by
  unfold sectionAlgHom; rw [SymmetricAlgebra.lift_ι_apply]

/-- The composite `Ψ ∘ (symAlgMap f)` is the quotient map `Sym(M₁) → Sym(M₁)/I`. -/
theorem sectionAlgHom_comp (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M)
    (hf : Function.Surjective f) (hexact : LinearMap.ker f ≤ LinearMap.range g) :
    (sectionAlgHom g f hf hexact).comp (symAlgMap f) = Ideal.Quotient.mkₐ R (rangeIdeal g) := by
  ext x
  simp only [LinearMap.comp_apply, LinearMap.coe_coe, AlgHom.comp_apply, symAlgMap_ι,
    sectionAlgHom_ι, phiMap_apply, Ideal.Quotient.mkₐ_eq_mk]
  exact mk_ι_eq g f hexact (Function.rightInverse_surjInv hf (f x))

/-- The kernel of `symAlgMap f` is contained in `I`. -/
theorem ker_symAlgMap_le_rangeIdeal (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M)
    (hf : Function.Surjective f) (hexact : LinearMap.ker f ≤ LinearMap.range g)
    {z : SymmetricAlgebra R M₁} (hz : symAlgMap f z = 0) : z ∈ rangeIdeal g := by
  have h := congrArg (fun φ => φ z) (sectionAlgHom_comp g f hf hexact)
  simp only [AlgHom.comp_apply] at h
  rw [hz, map_zero, Ideal.Quotient.mkₐ_eq_mk] at h
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact h.symm

end

end SymPow

/-! ## Exterior powers

We use Mathlib's `exteriorPower` (notation `⋀[R]^n M`) and `exteriorPower.map`. -/

namespace ExtPow

variable {R M₁ M₂ : Type*} [CommRing R] [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂]

/-- Wedging a degree-`1` element `ι m` with a degree-`k` element lands in degree `k+1`. -/
theorem wedge_mem_succ (k : ℕ) (m : M₁) (y : ⋀[R]^k M₁) :
    ExteriorAlgebra.ι R m * (y : ExteriorAlgebra R M₁) ∈ ⋀[R]^(k+1) M₁ := by
  rw [ExteriorAlgebra.exteriorPower, pow_succ']
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ m) y.property

/-- The bilinear map `(m₂, y) ↦ ι(g m₂) ∧ y` into `∧^{k+1}(M₁)`. -/
noncomputable def betaBil (k : ℕ) (g : M₂ →ₗ[R] M₁) :
    M₂ →ₗ[R] (⋀[R]^k M₁) →ₗ[R] (⋀[R]^(k+1) M₁) where
  toFun m₂ :=
    { toFun := fun y => ⟨ExteriorAlgebra.ι R (g m₂) * (y : ExteriorAlgebra R M₁),
        wedge_mem_succ k (g m₂) y⟩
      map_add' := by intro y z; ext; simp [mul_add]
      map_smul' := by intro c y; ext; simp }
  map_add' := by intro a b; ext y; simp [map_add, add_mul]
  map_smul' := by intro c a; ext y; simp [map_smul]

/-- The map `β : M₂ ⊗ ∧^k(M₁) → ∧^{k+1}(M₁)`,
`m₂ ⊗ (y₁∧⋯∧y_k) ↦ g(m₂)∧y₁∧⋯∧y_k`. -/
noncomputable def beta (k : ℕ) (g : M₂ →ₗ[R] M₁) :
    M₂ ⊗[R] (⋀[R]^k M₁) →ₗ[R] (⋀[R]^(k+1) M₁) :=
  TensorProduct.lift (betaBil k g)

/-- `β(m₂ ⊗ (y₁∧⋯∧y_k)) = g(m₂)∧y₁∧⋯∧y_k`. -/
theorem beta_tmul (k : ℕ) (g : M₂ →ₗ[R] M₁) (m₂ : M₂) (y : ⋀[R]^k M₁) :
    (beta k g (m₂ ⊗ₜ y) : ExteriorAlgebra R M₁)
      = ExteriorAlgebra.ι R (g m₂) * (y : ExteriorAlgebra R M₁) := rfl

end ExtPow

/-! ## Main statements -/

open SymPow ExtPow

/-! ### Exactness for symmetric powers -/

/-- If `range g ≤ ker f`, then `im(α) ⊆ ker(Sym^{k+1}(f))`. -/
theorem symmetric_im_alpha_le_ker
    {R : Type*} [CommSemiring R]
    {M M₁ M₂ : Type*}
    [AddCommMonoid M] [Module R M] [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂]
    (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M)
    (hexact : LinearMap.range g ≤ LinearMap.ker f)
    (k : ℕ) :
    LinearMap.range (symMulMap k g) ≤ LinearMap.ker (symMap (k+1) f) := by
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.mem_ker]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m₂ y =>
    have hfg : f (g m₂) = 0 :=
      LinearMap.mem_ker.mp (hexact (LinearMap.mem_range_self g m₂))
    rw [← Submodule.coe_eq_zero, symMap_coe, symMulMap_tmul, map_mul, symAlgMap_ι, hfg,
      map_zero, zero_mul]
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb, add_zero]

/-- If `f` is surjective and `ker f ≤ range g`, then `ker(Sym^{k+1}(f)) ⊆ im(α)`. -/
theorem symmetric_ker_le_im_alpha
    {R : Type*} [CommRing R]
    {M M₁ M₂ : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M)
    (hf : Function.Surjective f) (hexact : LinearMap.ker f ≤ LinearMap.range g)
    (k : ℕ) :
    LinearMap.ker (symMap (k+1) f) ≤ LinearMap.range (symMulMap k g) := by
  rintro ⟨z, hz⟩ hker
  have hz0 : SymPow.symAlgMap f z = 0 := by
    simpa [SymPow.symMap_coe] using Subtype.ext_iff.mp (LinearMap.mem_ker.mp hker)
  have hzI : z ∈ SymPow.rangeIdeal g := SymPow.ker_symAlgMap_le_rangeIdeal g f hf hexact hz0
  have hcoeff : (SymPow.degreeMap z).coeff (k+1) ∈
      SymPow.rangeSubmodule g * SymPow.symmetricPower k R M₁ :=
    (SymPow.rangeIdeal_degree g hzI).right k
  have hzeq : (SymPow.degreeMap z).coeff (k+1) = z := by
    rw [SymPow.degreeMap_eq_of_mem (k+1) z hz, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp
  rw [hzeq, ← SymPow.range_symMulMap k g] at hcoeff
  obtain ⟨_, ⟨t, rfl⟩, hvz⟩ := hcoeff
  exact ⟨t, Subtype.ext hvz⟩

/-- For an exact sequence
`M₂ --g--> M₁ --f--> M → 0` (`f` surjective, `im(g) = ker(f)`) and `n = k+1 ≥ 1`,
the sequence
`M₂ ⊗ Sym^k(M₁) --α--> Sym^{k+1}(M₁) --Sym^{k+1}(f)--> Sym^{k+1}(M) → 0`
is exact:
`Sym^{k+1}(f)` is surjective, and `im(α) = ker(Sym^{k+1}(f))`. -/
@[ega "0 19.5.1" "(V)", sga "5 VII 3.6.1" "partial"]
theorem symmetric_power_presentation
    {R : Type*} [CommRing R]
    {M M₁ M₂ : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M)
    (hf : Function.Surjective f) (hexact : LinearMap.range g = LinearMap.ker f)
    (k : ℕ) :
    Function.Surjective (symMap (k+1) f) ∧
      LinearMap.range (symMulMap k g) = LinearMap.ker (symMap (k+1) f) :=
  ⟨symMap_surjective (k+1) f hf, le_antisymm (symmetric_im_alpha_le_ker g f hexact.le k)
    (symmetric_ker_le_im_alpha g f hf hexact.ge k)⟩

/-! ### Exterior powers -/

/-- `exteriorPower.map n f`, viewed in the exterior algebra via the coercion, agrees with the
algebra map `ExteriorAlgebra.map f`. -/
theorem ExtPow.map_coe
    {R : Type*} [CommRing R] {M₁ N : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup N] [Module R N] (f : M₁ →ₗ[R] N) (n : ℕ) (x : ⋀[R]^n M₁) :
    ((exteriorPower.map n f x : ExteriorAlgebra R N))
      = ExteriorAlgebra.map f (x : ExteriorAlgebra R M₁) :=
  exteriorPower.coe_map f x

/-! ### The degree map and the section map for exterior algebras

The degree-tracking algebra map `degreeMap : ∧(M₁) → ∧(M₁)[X]`, sending `ι m ↦ C(ι m)·X`, and the
section algebra map `sectionAlgHom : ∧(M) → ∧(M₁)/I`, where `I` is the *two-sided* ideal
generated by `ι(range g)`. -/

namespace ExtPow

open Polynomial

section DegreeMap
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The degree-tracking linear map `m ↦ C(ι m) * X`. -/
noncomputable def degreeMapLin : M →ₗ[R] Polynomial (ExteriorAlgebra R M) :=
  (LinearMap.mulRight R (Polynomial.X : Polynomial (ExteriorAlgebra R M))).comp
    ((Polynomial.CAlgHom.toLinearMap).comp (ExteriorAlgebra.ι R))

/-- The linear map `degreeMapLin` has square zero, so it factors through the exterior algebra. -/
theorem degreeMapLin_mul_self (m : M) :
    degreeMapLin (R := R) (M := M) m * degreeMapLin (R := R) (M := M) m = 0 := by
  simp only [degreeMapLin, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply,
    Polynomial.CAlgHom_apply]
  rw [mul_assoc, ← mul_assoc Polynomial.X, Polynomial.X_mul, mul_assoc, ← pow_two, ← mul_assoc,
    ← Polynomial.C_mul, ExteriorAlgebra.ι_sq_zero, map_zero, zero_mul]

/-- The degree-tracking algebra map `degreeMap : ∧(M) → ∧(M)[X]`, `ι m ↦ C(ι m)·X`.
On a degree-`d` element `w`, `degreeMap w = C w · X^d`. -/
noncomputable def degreeMap : ExteriorAlgebra R M →ₐ[R] Polynomial (ExteriorAlgebra R M) :=
  ExteriorAlgebra.lift R ⟨degreeMapLin, degreeMapLin_mul_self⟩

/-- `degreeMap` sends a degree-`1` generator `ι m` to `C (ι m) * X`. -/
theorem degreeMap_ι (m : M) : degreeMap (ExteriorAlgebra.ι R m)
    = Polynomial.C (ExteriorAlgebra.ι R m) * Polynomial.X := by
  unfold degreeMap
  rw [ExteriorAlgebra.lift_ι_apply]
  rw [degreeMapLin, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.mulRight_apply,
    AlgHom.toLinearMap_apply, Polynomial.CAlgHom_apply]

/-- On degree-`d` elements, `degreeMap w = C w · X^d`. -/
theorem degreeMap_eq_of_mem (d : ℕ) (w : ExteriorAlgebra R M) (hw : w ∈ ⋀[R]^d M) :
    degreeMap w = Polynomial.C w * Polynomial.X ^ d := by
  induction d generalizing w with
  | zero =>
    rw [ExteriorAlgebra.exteriorPower, pow_zero, Submodule.mem_one] at hw
    obtain ⟨r, rfl⟩ := hw
    simp
  | succ n ih =>
    rw [ExteriorAlgebra.exteriorPower, pow_succ'] at hw
    refine Submodule.mul_induction_on hw ?_ ?_
    · rintro a ⟨m, rfl⟩ b hb
      have hcb : Polynomial.X * Polynomial.C b = Polynomial.C b * Polynomial.X :=
        (Polynomial.commute_X (Polynomial.C b)).eq
      have hxn : Polynomial.X * Polynomial.X ^ n = Polynomial.X ^ n * Polynomial.X :=
        ((Commute.refl (Polynomial.X : Polynomial (ExteriorAlgebra R M))).pow_right n).eq
      rw [map_mul, degreeMap_ι, ih b hb, Polynomial.C_mul, pow_succ,
        mul_assoc, ← mul_assoc Polynomial.X, hcb, mul_assoc (Polynomial.C b), hxn,
        ← mul_assoc, ← mul_assoc]
    · intro x y hx hy
      rw [map_add, hx, hy, map_add, add_mul]

/-- The degree-`i` coefficient of `degreeMap a` lies in `∧^i`. -/
theorem coeff_degreeMap_mem (a : ExteriorAlgebra R M) (i : ℕ) :
    (degreeMap a).coeff i ∈ ⋀[R]^i M := by
  have hmem : a ∈ Algebra.adjoin R (Set.range (ExteriorAlgebra.ι R (M := M))) := by
    rw [CliffordAlgebra.adjoin_range_ι]; trivial
  induction hmem using Algebra.adjoin_induction generalizing i with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    rw [degreeMap_ι, Polynomial.coeff_C_mul_X]
    refine ite_zero_mem _ fun h => ?_
    rw [h, ExteriorAlgebra.exteriorPower, pow_one]
    exact LinearMap.mem_range_self _ m
  | algebraMap r =>
    rw [AlgHom.commutes, Polynomial.algebraMap_apply, Polynomial.coeff_C]
    refine ite_zero_mem _ fun h => ?_
    rw [h, ExteriorAlgebra.exteriorPower, pow_zero, Submodule.mem_one]
    exact ⟨r, rfl⟩
  | add x y hx hy ihx ihy =>
    rw [map_add, Polynomial.coeff_add]
    exact Submodule.add_mem _ (ihx i) (ihy i)
  | mul x y hx hy ihx ihy =>
    rw [map_mul, Polynomial.coeff_mul]
    apply Submodule.sum_mem
    rintro ⟨p, q⟩ hpq
    replace hpq := Finset.HasAntidiagonal.mem_antidiagonal.mp hpq
    rw [← hpq, ExteriorAlgebra.exteriorPower, pow_add]
    exact Submodule.mul_mem_mul (ihx p) (ihy q)

end DegreeMap

section Ideal
variable {R : Type*} [CommRing R]
variable {M M₁ M₂ : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

/-- The two-sided ideal of `∧(M₁)` generated by `ι(range g)`. -/
noncomputable def rangeIdeal (g : M₂ →ₗ[R] M₁) : TwoSidedIdeal (ExteriorAlgebra R M₁) :=
  TwoSidedIdeal.span (Set.range (fun a : M₂ => ExteriorAlgebra.ι R (g a)))

/-- The quotient ring `∧(M₁) / rangeIdeal g`. -/
abbrev RangeIdealQuot (g : M₂ →ₗ[R] M₁) : Type _ := (rangeIdeal g).ringCon.Quotient

/-- The quotient algebra map. -/
noncomputable def mkA (g : M₂ →ₗ[R] M₁) : ExteriorAlgebra R M₁ →ₐ[R] RangeIdealQuot g :=
  { (rangeIdeal g).ringCon.mk' with commutes' := fun _ => rfl }

/-- `mkA g` is the quotient map of the two-sided ideal `rangeIdeal g`. -/
theorem mkA_apply (g : M₂ →ₗ[R] M₁) (x : ExteriorAlgebra R M₁) :
    mkA g x = (rangeIdeal g).ringCon.mk' x := rfl

/-- `ι v` lies in the ideal `rangeIdeal g` whenever `v` is in the range of `g`. -/
theorem ι_mem_rangeIdeal (g : M₂ →ₗ[R] M₁) {v : M₁} (hv : v ∈ LinearMap.range g) :
    ExteriorAlgebra.ι R v ∈ rangeIdeal g := by
  obtain ⟨a, rfl⟩ := hv; exact TwoSidedIdeal.subset_span ⟨a, rfl⟩

/-- An element dies in the quotient by `rangeIdeal g` exactly when it lies in `rangeIdeal g`. -/
theorem mkA_eq_zero_iff (g : M₂ →ₗ[R] M₁) (x : ExteriorAlgebra R M₁) :
    mkA g x = 0 ↔ x ∈ rangeIdeal g := by
  rw [mkA_apply, TwoSidedIdeal.mem_iff]
  constructor
  · intro h; have := (rangeIdeal g).ringCon.eq.mp h; simpa using this
  · intro h; exact (rangeIdeal g).ringCon.eq.mpr (by simpa using h)

/-- Two lifts of the same element have equal `ι`-image mod `I` when `ker f ≤ range g`. -/
theorem mk_ι_eq (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M)
    (hexact : LinearMap.ker f ≤ LinearMap.range g) {u v : M₁} (huv : f u = f v) :
    mkA g (ExteriorAlgebra.ι R u) = mkA g (ExteriorAlgebra.ι R v) := by
  rw [← sub_eq_zero, ← map_sub, mkA_eq_zero_iff, ← map_sub]
  apply ι_mem_rangeIdeal
  apply hexact
  rw [LinearMap.mem_ker, map_sub, huv, sub_self]

/-- The well-defined linear "section" `M → ∧(M₁)/I` (via a set-theoretic section of `f`). -/
noncomputable def phiMap (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M)
    (hf : Function.Surjective f) (hexact : LinearMap.ker f ≤ LinearMap.range g) :
    M →ₗ[R] RangeIdealQuot g where
  toFun m := mkA g (ExteriorAlgebra.ι R (Function.surjInv hf m))
  map_add' a b := by
    have hf' : ∀ x, f (Function.surjInv hf x) = x := Function.rightInverse_surjInv hf
    rw [← map_add, ← map_add]; exact mk_ι_eq g f hexact (by rw [hf', map_add, hf', hf'])
  map_smul' c a := by
    simp only [RingHom.id_apply, ← map_smul]
    have hf' : ∀ x, f (Function.surjInv hf x) = x := Function.rightInverse_surjInv hf
    exact mk_ι_eq g f hexact (by rw [hf', map_smul, hf'])

/-- `phiMap` sends `m` to the class of `ι (surjInv f m)` in `∧(M₁)/I`. -/
theorem phiMap_apply (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M)
    (hf : Function.Surjective f) (hexact : LinearMap.ker f ≤ LinearMap.range g) (m : M) :
    phiMap g f hf hexact m = mkA g (ExteriorAlgebra.ι R (Function.surjInv hf m)) := rfl

/-- The image of `phiMap` consists of square-zero elements. -/
theorem phiMap_sq (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M)
    (hf : Function.Surjective f) (hexact : LinearMap.ker f ≤ LinearMap.range g) (m : M) :
    phiMap g f hf hexact m * phiMap g f hf hexact m = 0 := by
  rw [phiMap_apply, ← map_mul, ExteriorAlgebra.ι_sq_zero, map_zero]

/-- The section algebra map `Ψ : ∧(M) → ∧(M₁)/I`. -/
noncomputable def sectionAlgHom (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M)
    (hf : Function.Surjective f) (hexact : LinearMap.ker f ≤ LinearMap.range g) :
    ExteriorAlgebra R M →ₐ[R] RangeIdealQuot g :=
  ExteriorAlgebra.lift R ⟨phiMap g f hf hexact, phiMap_sq g f hf hexact⟩

/-- `Ψ` sends a degree-`1` generator `ι m` to `phiMap m`. -/
theorem sectionAlgHom_ι (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M)
    (hf : Function.Surjective f) (hexact : LinearMap.ker f ≤ LinearMap.range g) (m : M) :
    sectionAlgHom g f hf hexact (ExteriorAlgebra.ι R m) = phiMap g f hf hexact m := by
  unfold sectionAlgHom; rw [ExteriorAlgebra.lift_ι_apply]

/-- The composite `Ψ ∘ (ExteriorAlgebra.map f)` is the quotient map `∧(M₁) → ∧(M₁)/I`. -/
theorem sectionAlgHom_comp (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M)
    (hf : Function.Surjective f) (hexact : LinearMap.ker f ≤ LinearMap.range g) :
    (sectionAlgHom g f hf hexact).comp (ExteriorAlgebra.map f) = mkA g := by
  apply ExteriorAlgebra.hom_ext
  ext x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    AlgHom.toLinearMap_apply, AlgHom.comp_apply]
  rw [ExteriorAlgebra.map_apply_ι, sectionAlgHom_ι, phiMap_apply]
  exact mk_ι_eq g f hexact (Function.rightInverse_surjInv hf (f x))

/-- The kernel of `ExteriorAlgebra.map f` is contained in `I`. -/
theorem ker_extMap_le_rangeIdeal (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M)
    (hf : Function.Surjective f) (hexact : LinearMap.ker f ≤ LinearMap.range g)
    {z : ExteriorAlgebra R M₁} (hz : ExteriorAlgebra.map f z = 0) : z ∈ rangeIdeal g := by
  have h := congrArg (fun φ => φ z) (sectionAlgHom_comp g f hf hexact)
  simp only [AlgHom.comp_apply] at h
  rw [hz, map_zero] at h
  rw [← mkA_eq_zero_iff]
  exact h.symm

end Ideal

section Degree
variable {R : Type*} [CommRing R]
variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

/-- The degree-`1` submodule `ι (g M₂)`. -/
noncomputable abbrev rangeSubmodule (g : M₂ →ₗ[R] M₁) : Submodule R (ExteriorAlgebra R M₁) :=
  LinearMap.range ((ExteriorAlgebra.ι R (M := M₁)).comp g)

local notation "𝕀" => (LinearMap.range (ExteriorAlgebra.ι R (M := M₁)))

/-- The image of `β` (pushed into the full algebra) equals `rangeSubmodule * ∧^k`. -/
theorem range_beta_map (k : ℕ) (g : M₂ →ₗ[R] M₁) :
    (LinearMap.range (beta k g)).map (⋀[R]^(k+1) M₁).subtype
      = rangeSubmodule g * ⋀[R]^k M₁ := by
  apply le_antisymm
  · rintro _ ⟨w, ⟨t, rfl⟩, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul m₂ y =>
      rw [Submodule.subtype_apply, beta_tmul]
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self (ExteriorAlgebra.ι R ∘ₗ g) m₂)
        y.property
    | add a b ha hb =>
      rw [map_add]; exact Submodule.add_mem _ ha hb
  · rw [Submodule.mul_le]
    rintro _ ⟨m₂, rfl⟩ y hy
    refine Submodule.mem_map.2 ⟨beta k g (m₂ ⊗ₜ ⟨y, hy⟩), LinearMap.mem_range_self _ _, ?_⟩
    rw [Submodule.subtype_apply, beta_tmul, LinearMap.comp_apply]

/-- `range ι * rangeSubmodule ≤ rangeSubmodule * range ι` (anticommutation of degree-1
elements). -/
theorem range_ι_mul_rangeSubmodule_le (g : M₂ →ₗ[R] M₁) :
    𝕀 * rangeSubmodule g ≤ rangeSubmodule g * 𝕀 := by
  rw [Submodule.mul_le]
  rintro _ ⟨a, rfl⟩ _ ⟨m₂, rfl⟩
  rw [LinearMap.comp_apply, eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap a (g m₂))]
  exact Submodule.neg_mem _ (Submodule.mul_mem_mul
    (LinearMap.mem_range_self (ExteriorAlgebra.ι R ∘ₗ g) m₂) (LinearMap.mem_range_self _ a))

/-- `range ι ^ p * rangeSubmodule ≤ rangeSubmodule * range ι ^ p`. -/
theorem pow_range_ι_mul_rangeSubmodule_le (g : M₂ →ₗ[R] M₁) (p : ℕ) :
    𝕀 ^ p * rangeSubmodule g ≤ rangeSubmodule g * 𝕀 ^ p := by
  induction p with
  | zero => simp
  | succ n ih =>
    have step1 : 𝕀 ^ (n+1) * rangeSubmodule g = 𝕀 * (𝕀 ^ n * rangeSubmodule g) := by
      rw [pow_succ', mul_assoc]
    have step2 : rangeSubmodule g * 𝕀 ^ (n+1) = (rangeSubmodule g * 𝕀) * 𝕀 ^ n := by
      rw [pow_succ', mul_assoc]
    rw [step1, step2]
    calc 𝕀 * (𝕀 ^ n * rangeSubmodule g) ≤ 𝕀 * (rangeSubmodule g * 𝕀 ^ n) := mul_le_mul_right ih _
      _ = (𝕀 * rangeSubmodule g) * 𝕀 ^ n := by rw [mul_assoc]
      _ ≤ (rangeSubmodule g * 𝕀) * 𝕀 ^ n := mul_le_mul_left (range_ι_mul_rangeSubmodule_le g) _

/-- Left multiplication: `∧^p * (rangeSubmodule * ∧^e) ≤ rangeSubmodule * ∧^(p+e)`. -/
theorem ext_mul_le_left (g : M₂ →ₗ[R] M₁) (p e : ℕ) :
    𝕀 ^ p * (rangeSubmodule g * 𝕀 ^ e) ≤ rangeSubmodule g * 𝕀 ^ (p + e) := by
  have step1 : 𝕀 ^ p * (rangeSubmodule g * 𝕀 ^ e) = (𝕀 ^ p * rangeSubmodule g) * 𝕀 ^ e := by
    rw [mul_assoc]
  have step2 : rangeSubmodule g * 𝕀 ^ (p+e) = (rangeSubmodule g * 𝕀 ^ p) * 𝕀 ^ e := by
    rw [pow_add, mul_assoc]
  rw [step1, step2]
  exact mul_le_mul_left (pow_range_ι_mul_rangeSubmodule_le g p) _

/-- Right multiplication: `(rangeSubmodule * ∧^e) * ∧^q ≤ rangeSubmodule * ∧^(e+q)`. -/
theorem ext_mul_le_right (g : M₂ →ₗ[R] M₁) (e q : ℕ) :
    (rangeSubmodule g * 𝕀 ^ e) * 𝕀 ^ q ≤ rangeSubmodule g * 𝕀 ^ (e + q) := by
  rw [mul_assoc, ← pow_add]

/-- The graded decomposition of (two-sided) ideal elements: an element of `I` has no degree-`0`
part, and its degree-`(d+1)` part lies in `rangeSubmodule * ∧^d`. -/
theorem rangeIdeal_degree (g : M₂ →ₗ[R] M₁) {z : ExteriorAlgebra R M₁} (hz : z ∈ rangeIdeal g) :
    (degreeMap z).coeff 0 = 0 ∧
      ∀ d : ℕ, (degreeMap z).coeff (d+1) ∈ rangeSubmodule g * ⋀[R]^d M₁ := by
  rw [rangeIdeal] at hz
  induction hz using TwoSidedIdeal.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [degreeMap_ι]
    refine ⟨by simp, fun d => ?_⟩
    rw [Polynomial.coeff_C_mul_X]
    refine ite_zero_mem _ fun h => ?_
    obtain rfl := Nat.succ.inj h
    rw [ExteriorAlgebra.exteriorPower, pow_zero, Submodule.mul_one]
    exact LinearMap.mem_range_self (ExteriorAlgebra.ι R ∘ₗ g) a
  | zero => simp
  | add x y hx hy ihx ihy =>
    refine ⟨?_, ?_⟩
    · rw [map_add, Polynomial.coeff_add, ihx.left, ihy.left, add_zero]
    · intro d
      rw [map_add, Polynomial.coeff_add]
      exact Submodule.add_mem _ (ihx.right d) (ihy.right d)
  | neg x hx ih =>
    refine ⟨?_, ?_⟩
    · rw [map_neg, Polynomial.coeff_neg, ih.left, neg_zero]
    · intro d
      rw [map_neg, Polynomial.coeff_neg]
      exact Submodule.neg_mem _ (ih.right d)
  | left_absorb a x hx ih =>
    rw [map_mul]
    refine ⟨?_, ?_⟩
    · rw [Polynomial.mul_coeff_zero, ih.left, mul_zero]
    · intro d
      rw [Polynomial.coeff_mul]
      apply Submodule.sum_mem
      rintro ⟨p, q⟩ hpq
      replace hpq := Finset.HasAntidiagonal.mem_antidiagonal.mp hpq
      rcases q with _ | e
      · rw [ih.left, mul_zero]; exact Submodule.zero_mem _
      · rw [← show p + e = d by omega]
        exact ext_mul_le_left g p e (Submodule.mul_mem_mul (coeff_degreeMap_mem a p) (ih.right e))
  | right_absorb b x hx ih =>
    rw [map_mul]
    refine ⟨?_, ?_⟩
    · rw [Polynomial.mul_coeff_zero, ih.left, zero_mul]
    · intro d
      rw [Polynomial.coeff_mul]
      apply Submodule.sum_mem
      rintro ⟨p, q⟩ hpq
      replace hpq := Finset.HasAntidiagonal.mem_antidiagonal.mp hpq
      rcases p with _ | e
      · rw [ih.left, zero_mul]; exact Submodule.zero_mem _
      · rw [← show e + q = d by omega]
        exact ext_mul_le_right g e q (Submodule.mul_mem_mul (ih.right e) (coeff_degreeMap_mem b q))

end Degree

end ExtPow

/-! ### Exactness for exterior powers -/

/-- If `range g ≤ ker f`, then `im(β) ⊆ ker(∧^{k+1}(f))`. -/
theorem exterior_im_beta_le_ker
    {R : Type*} [CommRing R]
    {M M₁ M₂ : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M)
    (hexact : LinearMap.range g ≤ LinearMap.ker f)
    (k : ℕ) :
    LinearMap.range (beta k g) ≤ LinearMap.ker (exteriorPower.map (k+1) f) := by
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.mem_ker]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m₂ y =>
    have hfg : f (g m₂) = 0 :=
      LinearMap.mem_ker.mp (hexact (LinearMap.mem_range_self g m₂))
    rw [← Submodule.coe_eq_zero, exteriorPower.coe_map, beta_tmul, map_mul,
      ExteriorAlgebra.map_apply_ι, hfg, map_zero, zero_mul]
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb, add_zero]

/-- If `f` is surjective and `ker f ≤ range g`, then `ker(∧^{k+1}(f)) ⊆ im(β)`. -/
theorem exterior_ker_le_im_beta
    {R : Type*} [CommRing R]
    {M M₁ M₂ : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M)
    (hf : Function.Surjective f) (hexact : LinearMap.ker f ≤ LinearMap.range g)
    (k : ℕ) :
    LinearMap.ker (exteriorPower.map (k+1) f) ≤ LinearMap.range (beta k g) := by
  rintro ⟨z, hz⟩ hker
  have hz0 : ExteriorAlgebra.map f z = 0 := by
    have h2 := Subtype.ext_iff.mp (LinearMap.mem_ker.mp hker)
    rw [ExtPow.map_coe] at h2
    simpa using h2
  have hzI : z ∈ ExtPow.rangeIdeal g := ExtPow.ker_extMap_le_rangeIdeal g f hf hexact hz0
  have hcoeff : (ExtPow.degreeMap z).coeff (k+1) ∈ ExtPow.rangeSubmodule g * ⋀[R]^k M₁ :=
    (ExtPow.rangeIdeal_degree g hzI).right k
  have hzeq : (ExtPow.degreeMap z).coeff (k+1) = z := by
    rw [ExtPow.degreeMap_eq_of_mem (k+1) z hz, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp
  rw [hzeq, ← ExtPow.range_beta_map k g] at hcoeff
  obtain ⟨_, ⟨t, rfl⟩, hvz⟩ := hcoeff
  exact ⟨t, Subtype.ext hvz⟩

/-- For an exact sequence
`M₂ --g--> M₁ --f--> M → 0` (`f` surjective, `im(g) = ker(f)`) and `n = k+1 ≥ 1`,
the sequence
`M₂ ⊗ ∧^k(M₁) --β--> ∧^{k+1}(M₁) --∧^{k+1}(f)--> ∧^{k+1}(M) → 0`
is exact:
`∧^{k+1}(f)` is surjective, and `im(β) = ker(∧^{k+1}(f))`. -/
@[sga "6 V 2.2.1" "special case"]
theorem exterior_power_presentation
    {R : Type*} [CommRing R]
    {M M₁ M₂ : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M)
    (hf : Function.Surjective f) (hexact : LinearMap.range g = LinearMap.ker f)
    (k : ℕ) :
    Function.Surjective (exteriorPower.map (k+1) f) ∧
      LinearMap.range (beta k g) = LinearMap.ker (exteriorPower.map (k+1) f) :=
  ⟨exteriorPower.map_surjective hf, le_antisymm (exterior_im_beta_le_ker g f hexact.le k)
    (exterior_ker_le_im_beta g f hf hexact.ge k)⟩

/-- Let `R` be a commutative ring and let
`M₂ --g--> M₁ --f--> M → 0` be an exact sequence of `R`-modules (`f` surjective and
`range g = ker f`).  With `n = k + 1 ≥ 1`, both presentation sequences are exact:

* symmetric: `M₂ ⊗ Sym^k(M₁) --α--> Sym^{k+1}(M₁) --Sym^{k+1}(f)--> Sym^{k+1}(M) → 0`;
* exterior:  `M₂ ⊗ ∧^k(M₁) --β--> ∧^{k+1}(M₁) --∧^{k+1}(f)--> ∧^{k+1}(M) → 0`.

In each case the right-hand map is surjective and the image of the left-hand connecting
map equals the kernel of the right-hand map. -/
@[stacks 00DO]
theorem symmetric_and_exterior_power_presentation
    {R : Type*} [CommRing R]
    {M M₁ M₂ : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    (g : M₂ →ₗ[R] M₁) (f : M₁ →ₗ[R] M)
    (hf : Function.Surjective f) (hexact : LinearMap.range g = LinearMap.ker f)
    (k : ℕ) :
    (Function.Surjective (symMap (k + 1) f) ∧
        LinearMap.range (symMulMap k g) = LinearMap.ker (symMap (k + 1) f)) ∧
      (Function.Surjective (exteriorPower.map (k + 1) f) ∧
        LinearMap.range (beta k g) = LinearMap.ker (exteriorPower.map (k + 1) f)) :=
  ⟨symmetric_power_presentation g f hf hexact k,
    exterior_power_presentation g f hf hexact k⟩

end
