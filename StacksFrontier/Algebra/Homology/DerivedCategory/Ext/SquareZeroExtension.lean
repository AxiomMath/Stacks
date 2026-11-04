module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Ext groups over a trivial square-zero extension

Let `R` be a commutative ring and let `A = R[ε]` be the trivial square-zero extension of `R`,
so `ε² = 0` and `A/(ε) = R`. Write `B` for `R` viewed as an `A`-module. Multiplication by `ε`
and the projection `A → R` fit into a short exact sequence `0 → B → A → B → 0`, and splicing
it into itself is the free periodic resolution `… → A → A → A` of `B` with all maps given by
multiplication by `ε`.

Consequently, for every `A`-module `M` annihilated by `ε` the groups `Extⁱ_A(B, M)` are all
equal to `M`: the periodic resolution has all its differentials acting as zero on such an `M`.

The final section records the instance of this computation appearing in
[Stacks, Tag 0A9M]: over `A = k[x][ε]` and for `Mₙ = A/(ε, xⁿ)` one has `Extⁱ_A(B, Mₙ) = Mₙ`
for all `i ≥ 0`, each `Mₙ` is annihilated by `xⁿ`, and yet the product `∏ₙ Mₙ` contains an
element annihilated by no power of `x`.

## Main definitions

* `Stacks.SquareZeroExt.residue`: `R` as a module over `R[ε]`, i.e. the `R[ε]`-module `R[ε]/(ε)`.
* `Stacks.SquareZeroExt.epsSequence`: the short exact sequence `0 → B → A → B → 0`.
* `Stacks.SquareZeroExt.IsEpsTrivial`: the condition that `ε` annihilate a module.
* `Stacks.SquareZeroExt.extEquiv`: the identification `Extⁱ_A(B, M) ≃ₗ[A] M`.
* `Stacks.SquareZeroExt.coefficientModule`: the module `Mₙ = A/(ε, xⁿ)` over `A = k[x][ε]`.

## Main results

* `Stacks.SquareZeroExt.epsSequence_shortExact`: the sequence above is short exact.
* `TrivSqZeroExt.isNoetherianRing`: `R[M]` is Noetherian for `R` Noetherian and `M` finite.
* `Stacks.SquareZeroExt.extSuccEquiv`: the connecting map `Extⁱ_A(B, M) ≃ₗ[A] Extⁱ⁺¹_A(B, M)`.
* `Stacks.SquareZeroExt.coefficientModule_ext`: `Extⁱ_A(B, Mₙ) ≃ₗ[A] Mₙ` for all `i`.
* `Stacks.SquareZeroExt.coefficientModule_xpow_smul`: `xⁿ` annihilates `Mₙ`.
* `Stacks.SquareZeroExt.coefficientModuleProduct_not_powerTorsion`: `∏ₙ Mₙ₊₁` has an element
  annihilated by no power of `x`.

## References

* [Stacks Project, Tag 0A9M](https://stacks.math.columbia.edu/tag/0A9M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.SquareZeroExt

/-! ### The square-zero extension and its residue module -/

section Residue

variable (R : Type u) [CommRing R]

/-- The projection `R[ε] → R` killing `ε`, as a ring homomorphism. -/
def proj : DualNumber R →+* R :=
  (TrivSqZeroExt.fstHom R R R).toRingHom

/-- The projection `R[ε] → R` sends `a` to its first component. -/
@[simp]
theorem proj_apply (a : DualNumber R) : proj R a = a.fst := rfl

/-- The `R[ε]`-module structure on `R` obtained by restricting scalars along the projection
killing `ε`. -/
scoped instance residueModule : Module (DualNumber R) R := Module.compHom R (proj R)

/-- An element `a` of `R[ε]` acts on `R` by multiplication by its first component. -/
theorem residueModule_smul (a : DualNumber R) (b : R) : a • b = a.fst * b := rfl

/-- `R` regarded as a module over the trivial square-zero extension `R[ε]` through the
projection killing `ε`; this is the `R[ε]`-module `R[ε]/(ε)`. -/
abbrev residue : ModuleCat.{u} (DualNumber R) := ModuleCat.of (DualNumber R) R

/-- Multiplication by `ε`, as an `R[ε]`-linear map `R[ε]/(ε) → R[ε]`. Its image is the ideal
`(ε)`. -/
def epsMul : residue R ⟶ ModuleCat.of (DualNumber R) (DualNumber R) :=
  ModuleCat.ofHom (X := residue R) (Y := ModuleCat.of (DualNumber R) (DualNumber R))
    { toFun := fun b => TrivSqZeroExt.inr b
      map_add' := fun a b => TrivSqZeroExt.inr_add R a b
      map_smul' := fun a b => by
        change (TrivSqZeroExt.inr (a.fst * b) : DualNumber R) = a * TrivSqZeroExt.inr b
        ext <;> simp [mul_comm] }

/-- Multiplication by `ε` sends `b` to `b ε`. -/
@[simp]
theorem epsMul_apply (b : R) :
    ConcreteCategory.hom (epsMul R) b = TrivSqZeroExt.inr b := rfl

/-- The projection `R[ε] → R[ε]/(ε)`, as an `R[ε]`-linear map. -/
def projMap : ModuleCat.of (DualNumber R) (DualNumber R) ⟶ residue R :=
  ModuleCat.ofHom (X := ModuleCat.of (DualNumber R) (DualNumber R)) (Y := residue R)
    { toFun := fun a => a.fst
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- The projection `R[ε] → R[ε]/(ε)` sends `a` to its first component. -/
@[simp]
theorem projMap_apply (a : DualNumber R) :
    ConcreteCategory.hom (projMap R) a = a.fst := rfl

/-- The short exact sequence `0 → R[ε]/(ε) → R[ε] → R[ε]/(ε) → 0` whose first map is
multiplication by `ε`. -/
def epsSequence : ShortComplex (ModuleCat.{u} (DualNumber R)) :=
  ShortComplex.mk (epsMul R) (projMap R) (by
    refine ModuleCat.hom_ext (LinearMap.ext fun b => ?_)
    change (TrivSqZeroExt.inr b : DualNumber R).fst = 0
    exact TrivSqZeroExt.fst_inr R b)

/-- The first map of `epsSequence` is multiplication by `ε`. -/
@[simp] theorem epsSequence_f : (epsSequence R).f = epsMul R := rfl

/-- The second map of `epsSequence` is the projection `R[ε] → R[ε]/(ε)`. -/
@[simp] theorem epsSequence_g : (epsSequence R).g = projMap R := rfl

/-- The kernel of the projection `R[ε] → R` is the image of multiplication by `ε`, which is
the ideal `(ε)`. -/
theorem exact_inr_fst :
    Function.Exact (TrivSqZeroExt.inr : R → DualNumber R)
      (TrivSqZeroExt.fst : DualNumber R → R) := by
  intro a
  constructor
  · intro ha
    refine ⟨a.snd, ?_⟩
    ext
    · exact (TrivSqZeroExt.fst_inr R a.snd).trans ha.symm
    · exact TrivSqZeroExt.snd_inr R a.snd
  · rintro ⟨b, rfl⟩
    exact TrivSqZeroExt.fst_inr R b

/-- The sequence `0 → R[ε]/(ε) → R[ε] → R[ε]/(ε) → 0` of `epsSequence` is short exact. -/
theorem epsSequence_shortExact : (epsSequence R).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr (exact_inr_fst R)
  · exact (ModuleCat.mono_iff_injective _).mpr fun _ _ h => TrivSqZeroExt.inr_injective h
  · exact (ModuleCat.epi_iff_surjective _).mpr
      fun b => ⟨TrivSqZeroExt.inl b, TrivSqZeroExt.fst_inl R b⟩

end Residue

/-! ### Modules annihilated by `ε` -/

section EpsTrivial

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} (DualNumber R))

/-- An `R[ε]`-module is *`ε`-trivial* when `ε` annihilates it, equivalently when its module
structure is restricted from the quotient `R[ε]/(ε) = R`. -/
def IsEpsTrivial : Prop := ∀ m : M, (DualNumber.eps : DualNumber R) • m = 0

variable {M}

/-- Every element `b ε` of the ideal `(ε)` annihilates an `ε`-trivial module. -/
theorem smul_inr_eq_zero (hM : IsEpsTrivial M) (b : R) (m : M) :
    (TrivSqZeroExt.inr b : DualNumber R) • m = 0 := by
  rw [show (TrivSqZeroExt.inr b : DualNumber R) = TrivSqZeroExt.inl b * DualNumber.eps by
    simp only [DualNumber.eps, TrivSqZeroExt.inl_mul_inr, smul_eq_mul, mul_one],
    mul_smul, hM m, smul_zero]

/-- On an `ε`-trivial module, an element of `R[ε]` acts as its first component does. -/
theorem smul_eq_inl_fst_smul (hM : IsEpsTrivial M) (a : DualNumber R) (m : M) :
    a • m = (TrivSqZeroExt.inl a.fst : DualNumber R) • m := by
  conv_lhs => rw [← a.inl_fst_add_inr_snd_eq]
  rw [add_smul, smul_inr_eq_zero hM, add_zero]

/-- Evaluation at `1` identifies `Hom_{R[ε]}(R[ε]/(ε), M)` with `M` whenever `ε` annihilates
`M`. -/
def homResidueEquiv (hM : IsEpsTrivial M) :
    (residue R ⟶ M) ≃ₗ[DualNumber R] M := by
  letI : Module (DualNumber R) R := residueModule R
  let ev : (residue R ⟶ M) →ₗ[DualNumber R] M :=
    { toFun := fun f => f (1 : R)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine LinearEquiv.ofBijective ev ⟨fun f g h => ?_, fun m => ?_⟩
  · ext b
    have hb : b = (TrivSqZeroExt.inl b : DualNumber R) • (1 : R) := (mul_one b).symm
    rw [hb, map_smul, map_smul]
    exact congrArg (fun m : M => (TrivSqZeroExt.inl b : DualNumber R) • m) h
  · have hsm : ∀ (a : DualNumber R) (b : R),
        (TrivSqZeroExt.inl (a.fst * b) : DualNumber R) • m
          = a • ((TrivSqZeroExt.inl b : DualNumber R) • m) := fun a b => by
      rw [smul_eq_inl_fst_smul hM a, ← mul_smul, TrivSqZeroExt.inl_mul_inl]
    refine ⟨ModuleCat.ofHom (X := residue R) (Y := M)
      { toFun := fun b => (TrivSqZeroExt.inl b : DualNumber R) • m
        map_add' := fun a b => by rw [TrivSqZeroExt.inl_add, add_smul]
        map_smul' := hsm }, ?_⟩
    change (TrivSqZeroExt.inl (1 : R) : DualNumber R) • m = m
    simp

/-- Precomposition with multiplication by `ε` annihilates `Extⁱ_A(A, M)` for an `ε`-trivial
`M`. -/
theorem epsSequence_precomp_eq_zero (hM : IsEpsTrivial M) (i : ℕ)
    (x : Abelian.Ext.{u} (epsSequence R).X₂ M i) :
    (Abelian.Ext.mk₀ (epsSequence R).f).comp x (zero_add i) = 0 := by
  cases i with
  | zero =>
    obtain ⟨g, rfl⟩ := (Abelian.Ext.linearEquiv₀ (R := DualNumber R)).symm.surjective x
    rw [Abelian.Ext.linearEquiv₀_symm_apply, Abelian.Ext.mk₀_comp_mk₀]
    change ModuleCat.of (DualNumber R) (DualNumber R) ⟶ M at g
    have hg : (epsSequence R).f ≫ g = 0 := by
      ext b
      have h := (ModuleCat.Hom.hom g).map_smul
        (TrivSqZeroExt.inr b : DualNumber R) (1 : DualNumber R)
      rw [smul_eq_mul, mul_one] at h
      simp only [epsSequence_f, ModuleCat.hom_zero, LinearMap.zero_apply]
      show (ModuleCat.Hom.hom g) (TrivSqZeroExt.inr b) = 0
      rw [h]
      exact smul_inr_eq_zero hM b _
    rw [hg, Abelian.Ext.mk₀_zero]
  | succ i =>
    have : Projective (epsSequence R).X₂ := by
      show Projective (ModuleCat.of (DualNumber R) (DualNumber R))
      infer_instance
    rw [Abelian.Ext.eq_zero_of_projective x, Abelian.Ext.comp_zero]

/-- The connecting map of `0 → B → A → B → 0` is an isomorphism `Extⁱ_A(B, M) ≃ Extⁱ⁺¹_A(B, M)`
for an `ε`-trivial `M`. -/
def extSuccEquiv (hM : IsEpsTrivial M) (i : ℕ) :
    Abelian.Ext.{u} (residue R) M i ≃ₗ[DualNumber R]
      Abelian.Ext.{u} (residue R) M (i + 1) := by
  have hS := epsSequence_shortExact R
  have hi : 1 + i = i + 1 := add_comm 1 i
  refine LinearEquiv.ofBijective (hS.extClass.precompOfLinear (DualNumber R) M hi)
    ⟨(injective_iff_map_eq_zero _).mpr fun x hx => ?_, fun x => ?_⟩
  · obtain ⟨y, hy⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS M x hi hx
    exact hy.symm.trans (epsSequence_precomp_eq_zero hM i y)
  · have : Projective (epsSequence R).X₂ := by
      change Projective (ModuleCat.of (DualNumber R) (DualNumber R))
      infer_instance
    exact Abelian.Ext.contravariant_sequence_exact₃ hS M x
      (Abelian.Ext.eq_zero_of_projective _) hi

/-- **Every `Ext` group of `B = R[ε]/(ε)` with coefficients in an `ε`-trivial module `M` is
`M` itself.** The identification is evaluation at `1` in degree `0`, iterated along the
connecting maps of the periodic resolution in higher degrees. -/
def extEquiv (hM : IsEpsTrivial M) :
    (i : ℕ) → Abelian.Ext.{u} (residue R) M i ≃ₗ[DualNumber R] M
  | 0 => (Abelian.Ext.linearEquiv₀ (R := DualNumber R)).trans (homResidueEquiv hM)
  | (i + 1) => (extSuccEquiv hM i).symm.trans (extEquiv hM i)

end EpsTrivial

/-! ### Noetherianity -/

/-- **A trivial square-zero extension of a Noetherian ring by a finite module is Noetherian**. -/
instance _root_.TrivSqZeroExt.isNoetherianRing {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [Module.Finite R M] :
    IsNoetherianRing (TrivSqZeroExt R M) :=
  have : Module.Finite R (TrivSqZeroExt R M) := inferInstanceAs (Module.Finite R (R × M))
  IsNoetherianRing.of_finite R (TrivSqZeroExt R M)

/-! ### The modules `Mₙ = A/(ε, xⁿ)` over `A = k[x][ε]` -/

section Example

variable (k : Type u) [Field k]

/-- The ring `A = k[x][ε]` with `ε² = 0` of [Stacks, Tag 0A9M]. -/
abbrev sourceRing : Type u := DualNumber (Polynomial k)

/-- The ideal `(ε, xⁿ)` of `A = k[x][ε]`. -/
def coefficientIdeal (n : ℕ) : Ideal (sourceRing k) :=
  Ideal.span ({DualNumber.eps,
    TrivSqZeroExt.inl ((Polynomial.X : Polynomial k) ^ n)} : Set (sourceRing k))

/-- The `A`-module `Mₙ = A/(ε, xⁿ)` of [Stacks, Tag 0A9M]. -/
abbrev coefficientModule (n : ℕ) : ModuleCat.{u} (sourceRing k) :=
  ModuleCat.of (sourceRing k) ((sourceRing k) ⧸ coefficientIdeal k n)

/-- `ε` lies in the ideal `(ε, xⁿ)`. -/
theorem eps_mem_coefficientIdeal (n : ℕ) :
    (DualNumber.eps : sourceRing k) ∈ coefficientIdeal k n :=
  Ideal.subset_span (by simp)

/-- `ε` annihilates `Mₙ = A/(ε, xⁿ)`. -/
theorem coefficientModule_isEpsTrivial (n : ℕ) :
    IsEpsTrivial (coefficientModule k n) := by
  intro m
  induction m using Submodule.Quotient.induction_on with
  | _ a =>
    show Submodule.Quotient.mk ((DualNumber.eps : sourceRing k) * a) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (Ideal.mul_mem_right _ _ (eps_mem_coefficientIdeal k n))

/-- **The `Ext` groups of [Stacks, Tag 0A9M]**: `Extⁱ_A(B, Mₙ) = Mₙ` for every `i ≥ 0`, where
`A = k[x][ε]`, `B = A/(ε) = k[x]` and `Mₙ = A/(ε, xⁿ)`. -/
def coefficientModule_ext (n i : ℕ) :
    Abelian.Ext.{u} (residue (Polynomial k)) (coefficientModule k n) i ≃ₗ[sourceRing k]
      coefficientModule k n :=
  extEquiv (coefficientModule_isEpsTrivial k n) i

/-- The `n`-th power of `x` in `A = k[x][ε]` is the image of `xⁿ ∈ k[x]`. -/
private theorem inl_pow_X (n : ℕ) :
    (TrivSqZeroExt.inl (Polynomial.X : Polynomial k) : sourceRing k) ^ n =
      TrivSqZeroExt.inl ((Polynomial.X : Polynomial k) ^ n) :=
  (map_pow (algebraMap (Polynomial k) (sourceRing k)) Polynomial.X n).symm

/-- `xⁿ` annihilates `Mₙ = A/(ε, xⁿ)`. -/
theorem coefficientModule_xpow_smul (n : ℕ) (m : coefficientModule k n) :
    (TrivSqZeroExt.inl (Polynomial.X : Polynomial k) : sourceRing k) ^ n • m = 0 := by
  induction m using Submodule.Quotient.induction_on with
  | _ a =>
    show Submodule.Quotient.mk
      ((TrivSqZeroExt.inl (Polynomial.X : Polynomial k) : sourceRing k) ^ n * a) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    refine Ideal.mul_mem_right _ _ ?_
    rw [inl_pow_X]
    exact Ideal.subset_span (by simp)

/-- The `n`-th power of `x` in `A = k[x][ε]` is the image of `xⁿ ∈ k[x]`. -/
theorem inl_xpow_eq (n : ℕ) :
    (TrivSqZeroExt.inl (Polynomial.X : Polynomial k) : sourceRing k) ^ n =
      TrivSqZeroExt.inl ((Polynomial.X : Polynomial k) ^ n) :=
  inl_pow_X k n

/-- `xⁿ` does not lie in the ideal `(ε, xⁿ⁺¹)` of `A = k[x][ε]`. -/
theorem inl_xpow_notMem_coefficientIdeal_succ (n : ℕ) :
    TrivSqZeroExt.inl ((Polynomial.X : Polynomial k) ^ n) ∉ coefficientIdeal k (n + 1) := by
  intro hx
  have hX : (Polynomial.X : Polynomial k) ≠ 0 := Polynomial.X_ne_zero
  have hmap : Ideal.map (proj (Polynomial k)) (coefficientIdeal k (n + 1)) ≤
      Ideal.span {(Polynomial.X : Polynomial k) ^ (n + 1)} := by
    rw [coefficientIdeal, Ideal.map_span]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨x, rfl | rfl, rfl⟩
    · rw [SetLike.mem_coe, proj_apply, DualNumber.fst_eps]
      exact Submodule.zero_mem _
    · rw [SetLike.mem_coe, proj_apply, TrivSqZeroExt.fst_inl]
      exact Ideal.mem_span_singleton_self _
  have hxJ : (Polynomial.X : Polynomial k) ^ n ∈
      Ideal.span {(Polynomial.X : Polynomial k) ^ (n + 1)} :=
    hmap (Ideal.mem_map_of_mem (proj (Polynomial k)) hx)
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp hxJ
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact pow_ne_zero n hX (by simpa using hq.symm)
  rw [mul_comm q ((Polynomial.X : Polynomial k) ^ (n + 1))] at hq
  have hdeg := congrArg Polynomial.natDegree hq
  rw [Polynomial.natDegree_mul (pow_ne_zero _ hX) hq0] at hdeg
  simp only [Polynomial.natDegree_X_pow] at hdeg
  omega

/-- **The product side of [Stacks, Tag 0A9M]**: the element `(1, 1, 1, …)` of `∏ₙ Mₙ₊₁` is
annihilated by no power of `x`, although each factor `Mₙ₊₁` is annihilated by `xⁿ⁺¹`. -/
theorem coefficientModuleProduct_not_powerTorsion :
    ∃ m : (∀ n : ℕ, coefficientModule k (n + 1)),
      ∀ n : ℕ,
        (TrivSqZeroExt.inl (Polynomial.X : Polynomial k) : sourceRing k) ^ n • m ≠ 0 := by
  refine ⟨fun n => Submodule.Quotient.mk (1 : sourceRing k), fun n hzero => ?_⟩
  have hz := congrFun hzero n
  change Submodule.Quotient.mk
    ((TrivSqZeroExt.inl (Polynomial.X : Polynomial k) : sourceRing k) ^ n * 1) = 0 at hz
  rw [mul_one, Submodule.Quotient.mk_eq_zero, inl_xpow_eq] at hz
  exact inl_xpow_notMem_coefficientIdeal_succ k n hz

end Example

end Stacks.SquareZeroExt

end
