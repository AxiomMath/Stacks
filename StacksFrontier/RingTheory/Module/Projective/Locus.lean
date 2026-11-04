module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import StacksCore.LinearAlgebra.Matrix.CommSemiring
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Injectivity, surjectivity and isomorphism loci of a map of finite projective modules

Let `R` be a commutative ring and `φ : P₁ → P₂` an `R`-linear map between finite projective
`R`-modules. The loci in `Spec R` where the fibre of `φ` is injective, surjective or
bijective are open, and over a basic open contained in such a locus the localized map is
injective (resp. surjective, bijective) with finite projective cokernel (resp. kernel).
This is Stacks Tag 00O0.

## Main definitions

* **Residue field.** For a prime `p`, the residue field at `p` is
  `κ(p) = R_p / p R_p ≅ Frac (R / p)`, an `R`-algebra; in Mathlib `p.ResidueField`.
* **Fibre map.** The fibre of `φ` at `p` is the `κ(p)`-linear base change
  `φ ⊗_R κ(p) : P₁ ⊗_R κ(p) → P₂ ⊗_R κ(p)`, realized here as
  `LinearMap.baseChange p.ResidueField φ`, so the domain is `κ(p) ⊗_R P₁`. Since the `Pᵢ`
  are finite projective, `κ(p) ⊗_R Pᵢ` are finite-dimensional `κ(p)`-vector spaces.
* **Zariski topology.** `Spec R = PrimeSpectrum R` carries the Zariski topology, with basic
  opens `D(f) = {p | f ∉ p} = PrimeSpectrum.basicOpen f` for `f : R`.
* **Localization at an element.** For `f : R`, `R_f = R[1/f]` is `Localization.Away f`, and
  `M_f = M ⊗_R R_f ≅ M[1/f]` for an `R`-module `M`. The localized map is
  `φ_f = LinearMap.baseChange (Localization.Away f) φ`, with domain `R_f ⊗_R P₁`.
* **Cokernel and kernel.** `Coker φ = P₂ ⧸ LinearMap.range φ` and `Ker φ = LinearMap.ker φ`.
  Localization is exact, so `(Coker φ)_f ≅ Coker (φ_f)` and `(Ker φ)_f ≅ Ker (φ_f)`; we work
  throughout with the base-changed modules `R_f ⊗_R Coker φ` and `R_f ⊗_R Ker φ`.
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.FiniteProjective.MapLocus

universe u v w t

variable {R : Type*} [CommRing R]
variable {P₁ P₂ : Type*} [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂]

/-- The fiber map of `φ` at a prime `p`, the `κ(p)`-linear base change of `φ`
along `R → κ(p)`. -/
noncomputable def fiberMap (φ : P₁ →ₗ[R] P₂) (p : Ideal R) [p.IsPrime] :
    p.ResidueField ⊗[R] P₁ →ₗ[p.ResidueField] p.ResidueField ⊗[R] P₂ :=
  LinearMap.baseChange p.ResidueField φ

/-- The localized map `φ_f : R_f ⊗_R P₁ → R_f ⊗_R P₂`. -/
noncomputable def localizedMap (φ : P₁ →ₗ[R] P₂) (f : R) :
    Localization.Away f ⊗[R] P₁ →ₗ[Localization.Away f] Localization.Away f ⊗[R] P₂ :=
  LinearMap.baseChange (Localization.Away f) φ

/-- The injectivity locus: primes where the fiber map of `φ` is injective. -/
def injLocus (φ : P₁ →ₗ[R] P₂) : Set (PrimeSpectrum R) :=
  {p | Function.Injective (fiberMap φ p.asIdeal)}

/-- The surjectivity locus: primes where the fiber map of `φ` is surjective. -/
def surjLocus (φ : P₁ →ₗ[R] P₂) : Set (PrimeSpectrum R) :=
  {p | Function.Surjective (fiberMap φ p.asIdeal)}

/-- The isomorphism locus: primes where the fiber map of `φ` is bijective. -/
def isoLocus (φ : P₁ →ₗ[R] P₂) : Set (PrimeSpectrum R) :=
  {p | Function.Bijective (fiberMap φ p.asIdeal)}

/-! ## Decomposition into sub-lemmas

The proof of all three theorems is obtained by a one-level decomposition into the
following named sub-lemmas. Theorem 3 (isomorphism locus) is a *formal*
consequence of Theorems 1 and 2 via `isoLocus_eq` below. Theorems 1 and 2 split
into three pieces each:

* openness of the locus (`isOpen_injLocus` / `isOpen_surjLocus`);
* the localized injectivity / surjectivity claim
  (`injective_localizedMap_of_subset` / `surjective_localizedMap_of_subset`);
* the localized finite-projectivity claim for the cokernel / kernel
  (`finiteProjective_coker_localized` / `finiteProjective_ker_localized`).
-/

/-- `isoLocus φ = injLocus φ ∩ surjLocus φ`. Purely formal: `Function.Bijective`
unfolds to `Injective ∧ Surjective`. -/
theorem isoLocus_eq (φ : P₁ →ₗ[R] P₂) :
    isoLocus φ = injLocus φ ∩ surjLocus φ := by
  ext p
  simp only [isoLocus, injLocus, surjLocus, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Function.Bijective]

/- **Openness of the injectivity locus.**

Argument (Stacks 00O0). Let `C = Coker(φ) = P₂ ⧸ range φ`, a finite `R`-module.
For a prime `p`, the right-exact sequence `P₁ → P₂ → C → 0` base-changes along
`R → κ(p)` to a right-exact sequence
`κ(p)⊗P₁ →[φ⊗κ(p)] κ(p)⊗P₂ → κ(p)⊗C → 0`; hence
`dim_{κ(p)} (κ(p)⊗C) = dim(κ(p)⊗P₂) − rank(φ⊗κ(p))`. Since `P₂` is finite
projective of locally constant rank `r₂`, `dim_{κ(p)}(κ(p)⊗P₂) = r₂(p)` is locally
constant, and `φ⊗κ(p)` is injective iff `rank(φ⊗κ(p)) = dim_{κ(p)}(κ(p)⊗P₁) =
r₁(p)`, i.e. iff the fibre dimension `dim_{κ(p)}(κ(p)⊗C) = r₂(p) − r₁(p)` attains
its *minimum* possible value. By upper semicontinuity of fibre dimension of a
finite module (`Coker`), the locus where `dim κ(p)⊗C` is `≤ r₂ − r₁` is open; the
reverse inequality is automatic, so `injLocus φ` is exactly this open set.
Equivalently and more directly: `p ∈ injLocus φ` ⇔ `C = Coker φ` is free (flat)
at `p` of the locally constant rank `r₂ − r₁`; the locus where a finite module is
flat/locally free is open. Concretely, openness is established by exhibiting, for
each `p ∈ injLocus φ`, an `f ∉ p` with `D(f) ⊆ injLocus φ` (this is exactly the
content of `injective_localizedMap_of_subset` applied at a neighbourhood obtained
by Nakayama), giving `injLocus φ = ⋃ {D(f) : D(f) ⊆ injLocus φ}`, a union of
basic opens.

The proof is given below (`isOpen_injLocus`), after the auxiliary lemmas it relies
on (`injLocus_subset_freeLocus`, etc.). -/

/-- Base change along `R → A` of `φ` and of the quotient map onto `P₂ ⧸ range φ` is exact. -/
private theorem exact_baseChange_mkQ_range (A : Type*) [CommRing A] [Algebra R A]
    (φ : P₁ →ₗ[R] P₂) :
    Function.Exact (LinearMap.baseChange A φ)
      (LinearMap.baseChange A (Submodule.mkQ (LinearMap.range φ))) := by
  simpa only [LinearMap.baseChange_eq_ltensor] using
    lTensor_exact A (LinearMap.exact_map_mkQ_range φ) (Submodule.mkQ_surjective _)

/-- Base change of the quotient map `P₂ → P₂ ⧸ range φ` is surjective. -/
private theorem surjective_baseChange_mkQ_range (A : Type*) [CommRing A] [Algebra R A]
    (φ : P₁ →ₗ[R] P₂) :
    Function.Surjective (LinearMap.baseChange A (Submodule.mkQ (LinearMap.range φ))) := by
  rw [LinearMap.baseChange_eq_ltensor]
  exact LinearMap.lTensor_surjective A (Submodule.mkQ_surjective _)

/-- `A ⊗ φ` is surjective iff `A ⊗ (P₂ ⧸ range φ)` is a subsingleton (right-exactness of `⊗`). -/
private theorem surjective_baseChange_iff_subsingleton (A : Type*) [CommRing A] [Algebra R A]
    (φ : P₁ →ₗ[R] P₂) :
    Function.Surjective (LinearMap.baseChange A φ) ↔
      Subsingleton (A ⊗[R] (P₂ ⧸ LinearMap.range φ)) := by
  have hex := exact_baseChange_mkQ_range A φ
  constructor
  · intro hsurj
    rw [subsingleton_iff_forall_eq 0]
    intro y
    obtain ⟨x, rfl⟩ := surjective_baseChange_mkQ_range A φ y
    have hx : x ∈ LinearMap.range (LinearMap.baseChange A φ) := by
      rw [LinearMap.range_eq_top.mpr hsurj]; trivial
    rw [← hex.linearMap_ker_eq] at hx
    exact hx
  · intro hsub
    rw [← LinearMap.range_eq_top, ← hex.linearMap_ker_eq, LinearMap.ker_eq_top]
    ext x
    exact Subsingleton.elim _ _

/-- **Openness of the surjectivity locus.**

Argument (Stacks 00O0, Nakayama). Let `C = Coker(φ)`, finite over `R`. By
right-exactness of base change, `κ(p) ⊗ C ≅ Coker(φ⊗κ(p))`. So `φ⊗κ(p)` is
surjective iff `κ(p) ⊗ C = 0`, i.e. iff `C_p / p C_p = 0`, i.e. (Nakayama, `C`
finite) iff `C_p = 0`, i.e. iff `p ∉ Supp(C)`. The support `Supp(C) = V(Ann C)`
of a finite module is closed (`Module.support_eq_zeroLocus` /
`PrimeSpectrum.zeroLocus`), so `surjLocus φ = Spec R \ Supp(C)` is open. Mathlib
tools: `Module.support` / `Module.support_eq_zeroLocus`,
`PrimeSpectrum.basicOpen`, and the fact that `κ(p)⊗ C = 0 ↔ p ∉ Supp C` for a
finite module via Nakayama (`Module.support` membership characterization). -/
theorem isOpen_surjLocus (φ : P₁ →ₗ[R] P₂) [Module.Finite R P₁] [Module.Projective R P₁]
    [Module.Finite R P₂] [Module.Projective R P₂] :
    IsOpen (surjLocus φ) := by
  -- `surjLocus φ` is the complement of the support of the cokernel `C = P₂ ⧸ range φ`,
  -- which is the (closed) zero locus of its annihilator.
  have hset : surjLocus φ = (Module.support R (P₂ ⧸ LinearMap.range φ))ᶜ := by
    ext p
    simp only [surjLocus, Set.mem_ofPred_eq, Set.mem_compl_iff]
    rw [fiberMap, surjective_baseChange_iff_subsingleton,
      Module.mem_support_iff_nontrivial_residueField_tensorProduct,
      not_nontrivial_iff_subsingleton]
  rw [hset, Module.support_eq_zeroLocus]
  exact (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl

/-- Auxiliary: injectivity of a base change `κ ⊗ φ` is preserved under an
`R`-algebra isomorphism `κ₁ ≃ₐ[R] κ₂` of the scalar ring. -/
theorem transfer_baseChange_injective {R : Type u} [CommRing R] {P₁ : Type v} {P₂ : Type w}
    [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂]
    (φ : P₁ →ₗ[R] P₂) {κ₁ κ₂ : Type t} [CommRing κ₁] [CommRing κ₂] [Algebra R κ₁] [Algebra R κ₂]
    (e : κ₁ ≃ₐ[R] κ₂)
    (h : Function.Injective (LinearMap.baseChange κ₁ φ)) :
    Function.Injective (LinearMap.baseChange κ₂ φ) := by
  set E₁ : κ₁ ⊗[R] P₁ ≃ₗ[R] κ₂ ⊗[R] P₁ :=
    TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R P₁) with hE₁
  set E₂ : κ₁ ⊗[R] P₂ ≃ₗ[R] κ₂ ⊗[R] P₂ :=
    TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R P₂) with hE₂
  have hcomm : ∀ x, (LinearMap.baseChange κ₂ φ) (E₁ x) = E₂ ((LinearMap.baseChange κ₁ φ) x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c p =>
        simp only [hE₁, hE₂, TensorProduct.congr_tmul, AlgEquiv.toLinearEquiv_apply,
          LinearEquiv.refl_apply, LinearMap.baseChange_tmul]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  intro a b hab
  apply E₁.symm.injective
  apply h
  apply E₂.injective
  rw [← hcomm (E₁.symm a), ← hcomm (E₁.symm b), LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, hab]

/-- Auxiliary: over a local `A`-algebra `S`, fibrewise injectivity (along the
residue field of `S`) of `S ⊗ ψ` implies injectivity of `S ⊗ ψ`. -/
theorem local_baseChange_injective {A : Type u} [CommRing A] (S : Type u) [CommRing S]
    [IsLocalRing S] [Algebra A S] {Q₁ : Type v} {Q₂ : Type w} [AddCommGroup Q₁] [Module A Q₁]
    [AddCommGroup Q₂] [Module A Q₂] [Module.Finite A Q₁] [Module.Projective A Q₁]
    [Module.Finite A Q₂] [Module.Projective A Q₂]
    (ψ : Q₁ →ₗ[A] Q₂)
    (hfib : Function.Injective
      (LinearMap.baseChange (IsLocalRing.ResidueField S) (LinearMap.baseChange S ψ))) :
    Function.Injective (LinearMap.baseChange S ψ) := by
  have : Module.Free S (S ⊗[A] Q₂) := Module.free_of_flat_of_isLocalRing
  obtain ⟨l', hl'⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective
    (LinearMap.baseChange S ψ)).mpr (by rwa [← LinearMap.baseChange_eq_ltensor])
  exact Function.LeftInverse.injective (g := l') (LinearMap.congr_fun hl')

/-- Auxiliary: base-change cancellation. If `T` is an algebra over `B` over `R`,
injectivity of `T ⊗_R ψ` gives injectivity of `T ⊗_B (B ⊗_R ψ)`. -/
theorem reduce_baseChange_injective {R : Type u} [CommRing R] {M₁ : Type v} {M₂ : Type w}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    (ψ : M₁ →ₗ[R] M₂)
    (B : Type u) [CommRing B] [Algebra R B] (T : Type u) [CommRing T] [Algebra R T]
    [Algebra B T] [IsScalarTower R B T]
    (h : Function.Injective (LinearMap.baseChange T ψ)) :
    Function.Injective (LinearMap.baseChange T (LinearMap.baseChange B ψ)) := by
  rw [LinearMap.baseChange_baseChange]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact ((TensorProduct.AlgebraTensorModule.cancelBaseChange R B T T M₂).symm.injective.comp
    h).comp (TensorProduct.AlgebraTensorModule.cancelBaseChange R B T T M₁).injective

/-- Auxiliary: combine the residue-field fibre injectivity with the local lemma
and base-change cancellation. With `A` an `R`-algebra and `S` a local `A`-algebra
(and a scalar tower over `R`), injectivity of `κ(S) ⊗_R φ` gives injectivity of
`S ⊗_A (A ⊗_R φ)`. Stated with `A`, `S` as opaque parameters to keep elaboration
fast (avoids `whnf` blowup on `Localization` `let`-bindings). -/
theorem fibre_baseChange_injective {R : Type u} [CommRing R] {P₁ : Type v} {P₂ : Type w}
    [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂]
    (φ : P₁ →ₗ[R] P₂)
    (A : Type u) [CommRing A] [Algebra R A]
    (S : Type u) [CommRing S] [IsLocalRing S] [Algebra A S] [Algebra R S] [IsScalarTower R A S]
    [Module.Finite A (A ⊗[R] P₁)] [Module.Projective A (A ⊗[R] P₁)]
    [Module.Finite A (A ⊗[R] P₂)] [Module.Projective A (A ⊗[R] P₂)]
    (hfib : Function.Injective (LinearMap.baseChange (IsLocalRing.ResidueField S) φ)) :
    Function.Injective (LinearMap.baseChange S (LinearMap.baseChange A φ)) := by
  apply local_baseChange_injective S (LinearMap.baseChange A φ)
  exact reduce_baseChange_injective (LinearMap.baseChange A φ) S (IsLocalRing.ResidueField S)
    (reduce_baseChange_injective φ A (IsLocalRing.ResidueField S) hfib)

/-- If `D(f) ⊆ injLocus φ`, then `φ` is injective after base change to the residue field of
the localization of `R_f` at any maximal ideal `J`. -/
private theorem injective_baseChange_residueField_of_subset (φ : P₁ →ₗ[R] P₂) (f : R)
    (hf : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ injLocus φ)
    (J : Ideal (Localization.Away f)) (hJ : J.IsMaximal) :
    Function.Injective
      (LinearMap.baseChange (IsLocalRing.ResidueField (Localization.AtPrime J)) φ) := by
  set A := Localization.Away f with hA
  set S := Localization.AtPrime J with hS
  -- Scalar tower data and the prime `q` of `R` lying under `J`.
  have hRAS : IsScalarTower R A S := IsScalarTower.of_algebraMap_eq (fun x => by rfl)
  -- The prime `q` of `R` lying under `J`, as a point of `Spec R`.
  have hqp0 : (J.comap (algebraMap R A)).IsPrime := Ideal.IsPrime.comap _
  set p₀ : PrimeSpectrum R := ⟨J.comap (algebraMap R A), hqp0⟩ with hp₀
  set q : Ideal R := p₀.asIdeal with hq
  have hqp : q.IsPrime := hqp0
  have : IsLocalization.AtPrime S q :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (Submonoid.powers f) S J
  -- `q ∈ D(f)`: `f` is a unit in `A = R_f`, so `algebraMap R A f ∉ J`, i.e. `f ∉ q`.
  have hfnotq : f ∉ q := by
    rw [hq, hp₀, Ideal.mem_comap]
    intro hmem
    have hunit : IsUnit (algebraMap R A f) := IsLocalization.Away.algebraMap_isUnit f
    exact (hJ.ne_top) (J.eq_top_of_isUnit_mem hmem hunit)
  -- fibre injectivity at `q`.
  have hqinj : Function.Injective (fiberMap φ q) := by
    have hmem : p₀ ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
      (PrimeSpectrum.mem_basicOpen f _).mpr hfnotq
    exact hf hmem
  -- Build the `R`-algebra isomorphism `q.ResidueField ≃ₐ[R] ResidueField S`.
  have hRSres : IsScalarTower R S (IsLocalRing.ResidueField S) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply R S (IsLocalRing.ResidueField S)])
  have hRAres : IsScalarTower R A (IsLocalRing.ResidueField S) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply R A (IsLocalRing.ResidueField S)])
  set ealg : S ≃ₐ[R] Localization.AtPrime q :=
    IsLocalization.algEquiv q.primeCompl S (Localization.AtPrime q) with healg
  set e0 : q.ResidueField ≃+* IsLocalRing.ResidueField S :=
    IsLocalRing.ResidueField.mapEquiv ealg.symm.toRingEquiv with he0
  have hcomm : ∀ r : R, e0 (algebraMap R q.ResidueField r) = algebraMap R (IsLocalRing.ResidueField
      S) r := by
    intro r
    have hr1 : algebraMap R q.ResidueField r
        = IsLocalRing.residue (Localization.AtPrime q) (algebraMap R (Localization.AtPrime q)
            r) := by
      rw [← IsLocalRing.ResidueField.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply R (Localization.AtPrime q) q.ResidueField]
    have hr2 : algebraMap R (IsLocalRing.ResidueField S) r
        = IsLocalRing.residue S (algebraMap R S r) := by
      rw [← IsLocalRing.ResidueField.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply R S (IsLocalRing.ResidueField S)]
    rw [hr1, hr2, he0, IsLocalRing.ResidueField.mapEquiv_apply,
      IsLocalRing.ResidueField.map_residue]
    congr 1
    exact ealg.symm.commutes r
  set ealgRF : q.ResidueField ≃ₐ[R] IsLocalRing.ResidueField S :=
    AlgEquiv.ofRingEquiv (f := e0) hcomm with healgRF
  exact transfer_baseChange_injective φ ealgRF hqinj

/-- **Localized injectivity.** If `D(f) ⊆ injLocus φ` then `φ_f` is injective.

Argument (Stacks 00O0). It suffices (`injective_of_localized_maximal`, 00HN) to
check that `(φ_f)_{m}` is injective for every maximal ideal `m` of `R_f`. Such an
`m` corresponds to a prime `q` of `R` with `f ∉ q`, i.e. `q ∈ D(f) ⊆ injLocus φ`;
the localization `R_f` at `m` is the localization `R_q`. So we must show:
if `φ ⊗ κ(q)` is injective (the hypothesis `q ∈ injLocus φ`) then `φ_q : (P₁)_q →
(P₂)_q` is injective. Over the local ring `R_q`, `(P₁)_q, (P₂)_q` are finite free,
and `K = Ker(φ_q)` is finite (kernel of a map of finite modules over a Noetherian-
free situation; in general use that `(P₁)_q` is finite projective so `K` is finite
since `(P₂)_q` is finite presented and the image is finite). Base-changing the
exact `0 → K → (P₁)_q → (P₂)_q` to `κ(q)` and using injectivity of `φ⊗κ(q)`:
`Tor` / right-exactness gives `K ⊗ κ(q) → (P₁)_q ⊗ κ(q) → (P₂)_q ⊗ κ(q)`, where
the second map is injective, forcing the image of `K ⊗ κ(q)` to be `0`. Since
`(P₁)_q ⊗ κ(q) = (P₁)_q / q (P₁)_q` and the composite `K → (P₁)_q → (P₁)_q/q…`
shows `K ⊆ q (P₁)_q`, i.e. `K = q K` (as `K` is a submodule with `K ⊆ qP₁ ∩ K`,
and `K` maps to `0`), so by Nakayama (`K` finite over local `R_q`) `K = 0`, i.e.
`φ_q` injective. Make `K` finite via: `K = ker φ_q` is a direct summand statement
not available a priori, so instead phrase via `LinearMap.range φ_q` and the
charpoly/`exists_monic_and_coeff_mem_pow…` (05G7) trick to produce the Nakayama
multiplier. -/
theorem injective_localizedMap_of_subset (φ : P₁ →ₗ[R] P₂) [Module.Finite R P₁]
    [Module.Projective R P₁] [Module.Finite R P₂] [Module.Projective R P₂] (f : R)
    (hf : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ injLocus φ) :
    Function.Injective (localizedMap φ f) := by
  set A := Localization.Away f with hA
  set F : (A ⊗[R] P₁) →ₗ[A] (A ⊗[R] P₂) := localizedMap φ f with hF
  apply injective_of_isLocalized_maximal
    (fun (J : Ideal A) _ => Localization.AtPrime J ⊗[A] (A ⊗[R] P₁))
    (fun (J : Ideal A) _ => (TensorProduct.mk A (Localization.AtPrime J) (A ⊗[R] P₁)) 1)
    (fun (J : Ideal A) _ => Localization.AtPrime J ⊗[A] (A ⊗[R] P₂))
    (fun (J : Ideal A) _ => (TensorProduct.mk A (Localization.AtPrime J) (A ⊗[R] P₂)) 1)
    F
  intro J hJ
  set S := Localization.AtPrime J with hS
  -- Identify the localized map with `lTensor S F`.
  have hmapeq : IsLocalizedModule.map J.primeCompl
      ((TensorProduct.mk A S (A ⊗[R] P₁)) 1) ((TensorProduct.mk A S (A ⊗[R] P₂)) 1) F
      = LinearMap.lTensor S F := by
    apply IsLocalizedModule.linearMap_ext J.primeCompl
      ((TensorProduct.mk A S (A ⊗[R] P₁)) 1) ((TensorProduct.mk A S (A ⊗[R] P₂)) 1)
    rw [IsLocalizedModule.map_comp]
    ext m
    rfl
  rw [hmapeq, ← LinearMap.baseChange_eq_ltensor]
  -- Reduce to `S ⊗_A (A ⊗_R φ)` (since `F = A ⊗_R φ`).
  show Function.Injective (LinearMap.baseChange S (LinearMap.baseChange A φ))
  -- Now prove the residue-field fibre is injective.
  have hRAS : IsScalarTower R A S := IsScalarTower.of_algebraMap_eq (fun x => by rfl)
  have hRSres : IsScalarTower R S (IsLocalRing.ResidueField S) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply R S (IsLocalRing.ResidueField S)])
  have hRAres : IsScalarTower R A (IsLocalRing.ResidueField S) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply R A (IsLocalRing.ResidueField S)])
  exact fibre_baseChange_injective φ A S
    (injective_baseChange_residueField_of_subset φ f hf J hJ)

/-- **Localized surjectivity.** If `D(f) ⊆ surjLocus φ` then `φ_f` is surjective.

Argument (Stacks 00O0, Nakayama). Let `C = Coker φ`, finite over `R`. Then
`C_f = R_f ⊗ C ≅ Coker(φ_f)` by right-exactness of localization
(`LocalizedModule.map_exact`/`Module.Flat.lTensor_exact`). `φ_f` is surjective iff
`C_f = 0`. By `Module.eq_zero_of_localization`-style / `Module.support` arguments,
`C_f = 0` iff `Supp(C) ∩ D(f) = ∅`, iff `D(f) ⊆ Supp(C)ᶜ`. Now for each
`q ∈ D(f) ⊆ surjLocus φ`, `φ⊗κ(q)` is surjective so `κ(q)⊗C = C_q/qC_q = 0`,
hence by Nakayama `C_q = 0`, i.e. `q ∉ Supp(C)`. Thus `D(f) ∩ Supp(C) = ∅`,
giving `C_f = 0` and `φ_f` surjective. (Equivalently: `C` is a finite module with
`C_q = 0` for all `q ∈ D(f)`, so `C_f` is a finite `R_f`-module vanishing at every
prime, hence `C_f = 0`.) -/
theorem surjective_localizedMap_of_subset (φ : P₁ →ₗ[R] P₂) [Module.Finite R P₁]
    [Module.Projective R P₁] [Module.Finite R P₂] [Module.Projective R P₂] (f : R)
    (hf : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ surjLocus φ) :
    Function.Surjective (localizedMap φ f) := by
  -- Step A: `Supp C ⊆ V(f)`, where `C = P₂ ⧸ range φ`. For `p ∈ Supp C`, if `f ∉ p` then
  -- `p ∈ D(f) ⊆ surjLocus φ`, so the fibre map is surjective, i.e. `κ(p) ⊗ C` is a subsingleton;
  -- but `p ∈ Supp C` means `κ(p) ⊗ C` is nontrivial — contradiction. Hence `f ∈ p`.
  have hsupp : Module.support R (P₂ ⧸ LinearMap.range φ) ⊆ PrimeSpectrum.zeroLocus {f} := by
    intro p hp
    rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
    by_contra hfp
    have hpD : p ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := hfp
    have hsurjp : Function.Surjective (fiberMap φ p.asIdeal) := hf hpD
    rw [fiberMap, surjective_baseChange_iff_subsingleton _ φ] at hsurjp
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
      ← not_subsingleton_iff_nontrivial] at hp
    exact hp hsurjp
  -- Step B: since `Supp C = V(Ann C) ⊆ V(f)`, we have `f ∈ √(Ann C)`, i.e. `f ^ n ∈ Ann C`.
  have hann : ∃ n, f ^ n ∈ Module.annihilator R (P₂ ⧸ LinearMap.range φ) := by
    have hf_mem : f ∈ PrimeSpectrum.vanishingIdeal
        (Module.support R (P₂ ⧸ LinearMap.range φ)) := by
      rw [PrimeSpectrum.mem_vanishingIdeal]
      intro x hx
      have := hsupp hx
      rw [PrimeSpectrum.mem_zeroLocus] at this
      exact this (Set.mem_singleton f)
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical,
      Ideal.mem_radical_iff] at hf_mem
    exact hf_mem
  -- Step C: `f ^ n ∈ Ann C` and `f` invertible in `R_f` force `R_f ⊗ C` to be a subsingleton,
  -- which by the bridge is exactly surjectivity of `φ_f = localizedMap φ f`.
  obtain ⟨n, hn⟩ := hann
  rw [localizedMap, surjective_baseChange_iff_subsingleton _ φ]
  rw [subsingleton_iff_forall_eq 0]
  intro y
  induction y using TensorProduct.induction_on with
  | zero => rfl
  | tmul a c =>
      have hc : (f ^ n) • c = 0 := Module.mem_annihilator.mp hn c
      have hzero : (f ^ n : R) • (a ⊗ₜ[R] c :
          Localization.Away f ⊗[R] (P₂ ⧸ LinearMap.range φ)) = 0 := by
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, hc, TensorProduct.tmul_zero]
      have hsmul : (f ^ n : R) • (a ⊗ₜ[R] c :
            Localization.Away f ⊗[R] (P₂ ⧸ LinearMap.range φ))
          = (algebraMap R (Localization.Away f) (f ^ n)) • (a ⊗ₜ[R] c) := by
        rw [algebraMap_smul]
      rw [hsmul] at hzero
      have hunit : IsUnit (algebraMap R (Localization.Away f) (f ^ n)) := by
        rw [map_pow]
        exact (IsLocalization.Away.algebraMap_isUnit f).pow n
      obtain ⟨u, hu⟩ := hunit
      rw [← hu] at hzero
      have huc : u • (a ⊗ₜ[R] c :
          Localization.Away f ⊗[R] (P₂ ⧸ LinearMap.range φ)) = 0 := hzero
      have hrw : (a ⊗ₜ[R] c : Localization.Away f ⊗[R] (P₂ ⧸ LinearMap.range φ))
          = u⁻¹ • (u • (a ⊗ₜ[R] c)) := by
        rw [smul_smul, inv_mul_cancel, one_smul]
      rw [hrw, huc, smul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

/-- Auxiliary (local cokernel projectivity): over a local ring `S`, if `u : M₁ → M₂`
is a map of finite `S`-modules with `M₂` free and the residue-field base change of `u`
is injective, then the cokernel `M₂ ⧸ range u` is projective. The injectivity of
`u ⊗ κ(S)` makes `u` a *split* injection (`split_injective_iff_lTensor_residueField_injective`),
and the splitting idempotent descends to a section of `M₂ → M₂ ⧸ range u`. -/
theorem coker_proj_local {S : Type u} [CommRing S] [IsLocalRing S] {M₁ : Type v} {M₂ : Type w}
    [AddCommGroup M₁] [Module S M₁] [AddCommGroup M₂] [Module S M₂]
    [Module.Finite S M₁] [Module.Finite S M₂] [Module.Free S M₂]
    (u : M₁ →ₗ[S] M₂)
    (hfib : Function.Injective (LinearMap.lTensor (IsLocalRing.ResidueField S) u)) :
    Module.Projective S (M₂ ⧸ LinearMap.range u) := by
  obtain ⟨l', hl'⟩ :=
    (IsLocalRing.split_injective_iff_lTensor_residueField_injective u).mpr hfib
  have hl'app : ∀ x, l' (u x) = x := LinearMap.congr_fun hl'
  set e : M₂ →ₗ[S] M₂ := LinearMap.id - u ∘ₗ l' with he
  have hek : LinearMap.range u ≤ LinearMap.ker e := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, he, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, hl'app, sub_self]
  set ē : (M₂ ⧸ LinearMap.range u) →ₗ[S] M₂ :=
    Submodule.liftQ (LinearMap.range u) e hek with heb
  set q : M₂ →ₗ[S] (M₂ ⧸ LinearMap.range u) := Submodule.mkQ (LinearMap.range u) with hq
  have hsec : q ∘ₗ ē = LinearMap.id := by
    apply LinearMap.ext
    intro w
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range u) w
    rw [LinearMap.comp_apply, LinearMap.id_apply, heb, hq]
    simp only [Submodule.mkQ_apply]
    rw [Submodule.liftQ_apply, he, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    refine (Submodule.Quotient.eq _).mpr ?_
    have hcalc : z - u (l' z) - z = -u (l' z) := by abel
    rw [hcalc]
    exact Submodule.neg_mem _ (LinearMap.mem_range_self u (l' z))
  exact Module.Projective.of_split ē q hsec

/-- Auxiliary: for a right-exact sequence `M₁ →[ψ] M₂ →[π] N → 0` of `A`-modules,
base change along `A → S` identifies `S ⊗ N` with the cokernel `(S ⊗ M₂) ⧸ range (S ⊗ ψ)`
(right-exactness of `S ⊗ -`). -/
noncomputable def coker_tensor_equiv {A : Type u} [CommRing A] (S : Type u) [CommRing S]
    [Algebra A S] {M₁ : Type v} {M₂ : Type w} {N : Type t}
    [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂] [AddCommGroup N] [Module A N]
    (ψ : M₁ →ₗ[A] M₂) (π : M₂ →ₗ[A] N) (hπ : Function.Surjective π)
    (hex : Function.Exact ψ π) :
    (S ⊗[A] N) ≃ₗ[S] (S ⊗[A] M₂) ⧸ LinearMap.range (LinearMap.baseChange S ψ) := by
  have hexT : Function.Exact (LinearMap.lTensor S ψ) (LinearMap.lTensor S π) :=
    lTensor_exact S hex hπ
  have hπT : Function.Surjective (LinearMap.baseChange S π) := by
    rw [LinearMap.baseChange_eq_ltensor]; exact LinearMap.lTensor_surjective S hπ
  have hker : LinearMap.range (LinearMap.baseChange S ψ)
      = LinearMap.ker (LinearMap.baseChange S π) := by
    ext x
    rw [LinearMap.mem_range, LinearMap.mem_ker, LinearMap.baseChange_eq_ltensor,
      LinearMap.baseChange_eq_ltensor]
    have := hexT x
    rw [Set.mem_range] at this
    exact this.symm
  refine LinearEquiv.symm ?_
  rw [hker]
  exact LinearMap.quotKerEquivOfSurjective (LinearMap.baseChange S π) hπT

/-- Auxiliary (local cokernel projectivity, full form): with `A` an `R₀`-algebra,
`S` a local `A`-algebra over `R₀`, `A ⊗ Pᵢ` finite projective, and `N` the cokernel of
`A ⊗ φ`, the residue-field fibre injectivity of `φ` at `S` forces `S ⊗_A N` to be
projective over `S`. Combines `coker_tensor_equiv`, the base-change cancellation
lemmas, and `coker_proj_local`. Stated with all rings in universe `u` to match the
base-change cancellation helpers. -/
theorem coker_proj_local_full {R₀ : Type u} [CommRing R₀] {P₁' : Type v} {P₂' : Type w}
    [AddCommGroup P₁'] [Module R₀ P₁'] [AddCommGroup P₂'] [Module R₀ P₂']
    (φ : P₁' →ₗ[R₀] P₂')
    (A : Type u) [CommRing A] [Algebra R₀ A]
    (S : Type u) [CommRing S] [IsLocalRing S] [Algebra A S] [Algebra R₀ S] [IsScalarTower R₀ A S]
    [Module.Finite A (A ⊗[R₀] P₁')] [Module.Projective A (A ⊗[R₀] P₁')]
    [Module.Finite A (A ⊗[R₀] P₂')] [Module.Projective A (A ⊗[R₀] P₂')]
    {N : Type t} [AddCommGroup N] [Module A N]
    (π : (A ⊗[R₀] P₂') →ₗ[A] N) (hπ : Function.Surjective π)
    (hex : Function.Exact (LinearMap.baseChange A φ) π)
    (hbcκ : Function.Injective (LinearMap.baseChange (IsLocalRing.ResidueField S) φ)) :
    Module.Projective S (S ⊗[A] N) := by
  have : IsScalarTower R₀ S (IsLocalRing.ResidueField S) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply R₀ S (IsLocalRing.ResidueField S)])
  have : IsScalarTower R₀ A (IsLocalRing.ResidueField S) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply R₀ A (IsLocalRing.ResidueField S)])
  have : Module.Free S (S ⊗[A] (A ⊗[R₀] P₂')) := Module.free_of_flat_of_isLocalRing
  have step1 : Function.Injective
      (LinearMap.baseChange (IsLocalRing.ResidueField S) (LinearMap.baseChange A φ)) :=
    reduce_baseChange_injective φ A (IsLocalRing.ResidueField S) hbcκ
  have hfib : Function.Injective (LinearMap.lTensor (IsLocalRing.ResidueField S)
      (LinearMap.baseChange S (LinearMap.baseChange A φ))) := by
    rw [← LinearMap.baseChange_eq_ltensor]
    exact reduce_baseChange_injective (LinearMap.baseChange A φ) S
      (IsLocalRing.ResidueField S) step1
  have hproj : Module.Projective S
      ((S ⊗[A] (A ⊗[R₀] P₂')) ⧸
        LinearMap.range (LinearMap.baseChange S (LinearMap.baseChange A φ))) :=
    coker_proj_local (LinearMap.baseChange S (LinearMap.baseChange A φ)) hfib
  have e := coker_tensor_equiv S (LinearMap.baseChange A φ) π hπ hex
  exact Module.Projective.of_equiv e.symm

/-- Auxiliary (global cokernel projectivity): if `D(f) ⊆ injLocus φ`, then `R_f ⊗ Coker φ`
is projective over `R_f`. Checked at each maximal ideal of `R_f` via
`Module.projective_of_localization_maximal`: the maximal ideal corresponds to a prime
`q ∈ D(f) ⊆ injLocus φ`, where fibrewise injectivity transfers (`transfer_baseChange_injective`)
to the residue field of the localization and `coker_proj_local_full` applies. Finite
presentation of `R_f ⊗ Coker φ` comes from it being the cokernel of a map of finite
projective (hence finitely presented) modules. -/
theorem coker_proj_global (φ : P₁ →ₗ[R] P₂) [Module.Finite R P₁]
    [Module.Projective R P₁] [Module.Finite R P₂] [Module.Projective R P₂] (f : R)
    (hf : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ injLocus φ) :
    Module.Projective (Localization.Away f)
        (Localization.Away f ⊗[R] (P₂ ⧸ LinearMap.range φ)) := by
  set A := Localization.Away f with hA
  set N := A ⊗[R] (P₂ ⧸ LinearMap.range φ)
  set π : (A ⊗[R] P₂) →ₗ[A] N :=
    LinearMap.baseChange A (Submodule.mkQ (LinearMap.range φ)) with hπdef
  have hπsurj : Function.Surjective π := surjective_baseChange_mkQ_range A φ
  have hex : Function.Exact (LinearMap.baseChange A φ) π := exact_baseChange_mkQ_range A φ
  have : Module.FinitePresentation A (A ⊗[R] P₂) := Module.finitePresentation_of_projective A _
  have hNfp : Module.FinitePresentation A N := by
    have hkerFG : (LinearMap.ker π).FG := by
      have hkr : LinearMap.ker π = LinearMap.range (LinearMap.baseChange A φ) :=
        hex.linearMap_ker_eq
      rw [hkr]; exact Submodule.fg_range _
    exact Module.finitePresentation_of_surjective π hπsurj hkerFG
  apply Module.projective_of_localization_maximal
  intro J hJ
  set S := Localization.AtPrime J with hS
  suffices h : Module.Projective S (S ⊗[A] N) by
    have e := LocalizedModule.equivTensorProduct J.primeCompl N
    exact Module.Projective.of_equiv (R := S) e.symm
  have hRAS : IsScalarTower R A S := IsScalarTower.of_algebraMap_eq (fun x => by rfl)
  have hbcκ := injective_baseChange_residueField_of_subset φ f hf J hJ
  exact coker_proj_local_full φ A S π hπsurj hex hbcκ

/-- Forward inclusion for openness: if `φ` is fibrewise injective at `p`, then the
cokernel `C = P₂ ⧸ range φ` is free at `p`, i.e. `p ∈ freeLocus R C`. -/
theorem injLocus_subset_freeLocus (φ : P₁ →ₗ[R] P₂) [Module.Finite R P₁]
    [Module.Projective R P₁] [Module.Finite R P₂] [Module.Projective R P₂] :
    injLocus φ ⊆ Module.freeLocus R (P₂ ⧸ LinearMap.range φ) := by
  intro p hp
  set q : Ideal R := p.asIdeal with hq
  set S := Localization.AtPrime q with hS
  set N := R ⊗[R] (P₂ ⧸ LinearMap.range φ) with hN
  set π : (R ⊗[R] P₂) →ₗ[R] N :=
    LinearMap.baseChange R (Submodule.mkQ (LinearMap.range φ)) with hπdef
  have hπsurj : Function.Surjective π := surjective_baseChange_mkQ_range R φ
  have hex : Function.Exact (LinearMap.baseChange R φ) π := exact_baseChange_mkQ_range R φ
  have hRAS : IsScalarTower R R S := IsScalarTower.of_algebraMap_eq (fun x => by rfl)
  have hRSres : IsScalarTower R S (IsLocalRing.ResidueField S) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply R S (IsLocalRing.ResidueField S)])
  -- Since `q.ResidueField` is definitionally `IsLocalRing.ResidueField S`,
  -- fibrewise injectivity at `q` is exactly residue-field injectivity for `S`.
  have hbcκ : Function.Injective (LinearMap.baseChange (IsLocalRing.ResidueField S) φ) := hp
  -- `S ⊗ N` is projective over `S`.
  have hproj : Module.Projective S (S ⊗[R] N) :=
    coker_proj_local_full φ R S π hπsurj hex hbcκ
  -- transfer projectivity to `LocalizedModule q.primeCompl C`, then conclude freeness.
  set C := P₂ ⧸ LinearMap.range φ with hC
  have eN : N ≃ₗ[R] C := TensorProduct.lid R C
  have eSN : (S ⊗[R] N) ≃ₗ[S] (S ⊗[R] C) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) eN
  have : Module.Projective S (S ⊗[R] C) := Module.Projective.of_equiv eSN
  -- `LocalizedModule q.primeCompl C ≃ₗ[S] S ⊗[R] C`.
  have eLoc := LocalizedModule.equivTensorProduct q.primeCompl C
  have : Module.Projective S (LocalizedModule q.primeCompl C) :=
    Module.Projective.of_equiv eLoc.symm
  have : Module.Finite S (LocalizedModule q.primeCompl C) := by
    have : Module.Finite R C := by
      have hsurj : Function.Surjective (Submodule.mkQ (LinearMap.range φ)) :=
        Submodule.mkQ_surjective _
      exact Module.Finite.of_surjective _ hsurj
    infer_instance
  rw [Module.mem_freeLocus]
  exact Module.free_of_flat_of_isLocalRing

/-- Field-level rank–nullity: a linear map `g : V → W` of finite-dimensional vector
spaces over a field `K` is injective iff `dim V + dim (coker g) = dim W`. -/
theorem injective_iff_finrank_eq {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (g : V →ₗ[K] W) :
    Function.Injective g ↔
      Module.finrank K V + Module.finrank K (W ⧸ LinearMap.range g) = Module.finrank K W := by
  have := Submodule.finrank_quotient_add_finrank (LinearMap.range g)
  have := LinearMap.finrank_range_add_finrank_ker g
  rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
  omega

/-- Bridge: if `M` is free at `q` (i.e. `Localization.AtPrime q ⊗ M` is free), then its
rank at the stalk equals the fibre dimension over the residue field of `Localization.AtPrime q`. -/
@[ega "III 7.9.1" "more general"]
theorem rankAtStalk_eq_finrank_residueField {R : Type u} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (q : Ideal R) [q.IsPrime]
    [Module.Free (Localization.AtPrime q) (Localization.AtPrime q ⊗[R] M)]
    [Module.Finite (Localization.AtPrime q) (Localization.AtPrime q ⊗[R] M)] :
    Module.finrank (Localization.AtPrime q) (Localization.AtPrime q ⊗[R] M)
      = Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
          (IsLocalRing.ResidueField (Localization.AtPrime q) ⊗[R] M) := by
  set S := Localization.AtPrime q
  set κ := IsLocalRing.ResidueField S
  have : IsScalarTower R S κ := IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply R S κ])
  have e : κ ⊗[S] (S ⊗[R] M) ≃ₗ[κ] κ ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S κ κ M
  rw [← Module.finrank_baseChange (R := κ) (S := S) (M' := S ⊗[R] M), e.finrank_eq]

/-- **Localized cokernel is finite projective.** If `D(f) ⊆ injLocus φ` then
`R_f ⊗ Coker φ` is finite projective over `R_f`.

Argument (Stacks 00O0). Write `C = Coker φ`, finite over `R`. By right-exact
localization `R_f ⊗ C ≅ Coker(φ_f)`, and by `injective_localizedMap_of_subset`
`φ_f` is injective, so there is a *short* exact sequence of `R_f`-modules
`0 → (P₁)_f →[φ_f] (P₂)_f → R_f⊗C → 0` with `(P₁)_f, (P₂)_f` finite projective
over `R_f`. Finiteness of `R_f⊗C`: it is a quotient of the finite module `(P₂)_f`
(`Module.Finite.quotient`/`Submodule.Quotient`), so finite. Projectivity: for
each prime `q ∈ D(f)`, base-changing the short exact sequence to `κ(q)` stays
*left* exact because `φ_f` is fibrewise injective (this is exactly `q ∈ injLocus`,
so `Tor₁(R_f⊗C, κ(q)) = 0`); thus `R_f⊗C` is flat at every prime of `R_f`, i.e.
flat, and a finitely-presented flat module is projective
(`Module.Projective` from flat + finitely presented, or
`Module.projective_of_localization_maximal` 0FWT checking each maximal localization
is free: each localization `(R_f⊗C)_m` is free since it is the cokernel of an
injective map of finite frees over a local ring with locally free cokernel). The
finite presentation of `R_f⊗C` comes from `Coker` of a map of finite projective
(hence finitely presented) modules. -/
@[ega "IV 11.3.7" "(b) ⇒ (a)"]
theorem finiteProjective_coker_localized (φ : P₁ →ₗ[R] P₂) [Module.Finite R P₁]
    [Module.Projective R P₁] [Module.Finite R P₂] [Module.Projective R P₂] (f : R)
    (hf : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ injLocus φ) :
    Module.Finite (Localization.Away f)
        (Localization.Away f ⊗[R] (P₂ ⧸ LinearMap.range φ)) ∧
      Module.Projective (Localization.Away f)
        (Localization.Away f ⊗[R] (P₂ ⧸ LinearMap.range φ)) := by
  refine ⟨?_, coker_proj_global φ f hf⟩
  -- Finiteness: `R_f ⊗ Coker φ` is a surjective image of the finite module `R_f ⊗ P₂`.
  exact Module.Finite.of_surjective _ (surjective_baseChange_mkQ_range _ φ)


/-- **Localized kernel is finite projective.** If `D(f) ⊆ surjLocus φ` then
`R_f ⊗ Ker φ` is finite projective over `R_f`.

Argument (Stacks 00O0). By `surjective_localizedMap_of_subset`, `φ_f` is
surjective, and by left-exact localization `R_f ⊗ Ker φ ≅ Ker(φ_f)`. So we have a
short exact sequence of `R_f`-modules
`0 → R_f⊗Ker φ → (P₁)_f →[φ_f] (P₂)_f → 0` with `(P₂)_f` finite projective. A
short exact sequence ending in a projective module *splits*
(`Module.Projective` lifting property): there is a section `(P₂)_f → (P₁)_f` of
`φ_f`, hence `(P₁)_f ≅ (R_f⊗Ker φ) ⊕ (P₂)_f`. Therefore `R_f⊗Ker φ` is a direct
summand of the finite projective module `(P₁)_f`, so it is itself finite
projective (`Module.Projective.of_split`, and finite since it is a quotient/summand
of the finite module `(P₁)_f`). -/
@[sga "6 I 1.3" "special case"]
theorem finiteProjective_ker_localized (φ : P₁ →ₗ[R] P₂) [Module.Finite R P₁]
    [Module.Projective R P₁] [Module.Finite R P₂] [Module.Projective R P₂] (f : R)
    (hf : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ surjLocus φ) :
    Module.Finite (Localization.Away f)
        (Localization.Away f ⊗[R] (LinearMap.ker φ)) ∧
      Module.Projective (Localization.Away f)
        (Localization.Away f ⊗[R] (LinearMap.ker φ)) := by
  set A := Localization.Away f
  have : Module.Flat R A := inferInstance
  -- `φ_f` is surjective by the companion lemma.
  have hsurj : Function.Surjective (localizedMap φ f) :=
    surjective_localizedMap_of_subset φ f hf
  set ψ := localizedMap φ f with hψ
  -- Step 1: `ker ψ` is finite projective over `A`, since the split surjection `ψ`
  -- exhibits it as a direct summand of the finite projective module `A ⊗ P₁`.
  obtain ⟨g, hg⟩ :=
    LinearMap.exists_rightInverse_of_surjective ψ (LinearMap.range_eq_top.mpr hsurj)
  have hgapp : ∀ y, ψ (g y) = y := LinearMap.congr_fun hg
  set proj : (A ⊗[R] P₁) →ₗ[A] (A ⊗[R] P₁) := LinearMap.id - g ∘ₗ ψ with hprojdef
  have hproj : ∀ x, proj x ∈ LinearMap.ker ψ := by
    intro x
    rw [LinearMap.mem_ker, hprojdef, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, map_sub, hgapp, sub_self]
  set s : (A ⊗[R] P₁) →ₗ[A] (LinearMap.ker ψ) :=
    LinearMap.codRestrict (LinearMap.ker ψ) proj hproj with hsdef
  have hsi : s ∘ₗ (LinearMap.ker ψ).subtype = LinearMap.id := by
    ext k
    simp only [LinearMap.comp_apply, hsdef, LinearMap.id_apply]
    rw [LinearMap.codRestrict_apply, hprojdef, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, Submodule.coe_subtype]
    have hk0 : ψ (k : A ⊗[R] P₁) = 0 := k.property
    rw [hk0, map_zero, sub_zero]
  have hkerFin : Module.Finite A (LinearMap.ker ψ) := by
    have hssurj : Function.Surjective s := fun k =>
      ⟨(LinearMap.ker ψ).subtype k, by rw [← LinearMap.comp_apply, hsi, LinearMap.id_apply]⟩
    exact Module.Finite.of_surjective s hssurj
  have hkerProj : Module.Projective A (LinearMap.ker ψ) :=
    Module.Projective.of_split (LinearMap.ker ψ).subtype s hsi
  -- Step 2: `A ⊗ ker φ ≃ₗ[A] ker ψ`, by flatness of `A` over `R`.
  set b : (A ⊗[R] (LinearMap.ker φ)) →ₗ[A] (A ⊗[R] P₁) :=
    LinearMap.baseChange A (LinearMap.ker φ).subtype with hbdef
  have hbinj : Function.Injective b := by
    rw [hbdef, LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap (LinearMap.ker φ).subtype
      (Submodule.injective_subtype _)
  have hrange : LinearMap.range b = LinearMap.ker ψ := by
    have hexT : Function.Exact (LinearMap.lTensor A (LinearMap.ker φ).subtype)
        (LinearMap.lTensor A φ) :=
      Module.Flat.lTensor_exact A (LinearMap.exact_subtype_ker_map φ)
    ext x
    rw [LinearMap.mem_range, LinearMap.mem_ker, ← Set.mem_range]
    exact (hexT x).symm
  set e : (A ⊗[R] (LinearMap.ker φ)) ≃ₗ[A] (LinearMap.ker ψ) :=
    (LinearEquiv.ofInjective b hbinj).trans (LinearEquiv.ofEq _ _ hrange) with hedef
  -- Step 3: transport finiteness and projectivity along `e`.
  exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩

/-- On the free locus of the cokernel `C = P₂ ⧸ range φ`, fibrewise injectivity of `φ`
at a prime `p` is equivalent to the rank equality
`rank P₁ p + rank C p = rank P₂ p` (rank–nullity in the fibre). -/
theorem mem_injLocus_iff_rank (φ : P₁ →ₗ[R] P₂) [Module.Finite R P₁] [Module.Projective R P₁]
    [Module.Finite R P₂] [Module.Projective R P₂] (p : PrimeSpectrum R)
    (hp : p ∈ Module.freeLocus R (P₂ ⧸ LinearMap.range φ)) :
    p ∈ injLocus φ ↔
      Module.rankAtStalk P₁ p + Module.rankAtStalk (P₂ ⧸ LinearMap.range φ) p
        = Module.rankAtStalk P₂ p := by
  set q : Ideal R := p.asIdeal with hq
  set K := q.ResidueField with hK
  set C := P₂ ⧸ LinearMap.range φ with hC
  -- the coker of the fibre map identifies with `K ⊗ C`.
  have hπsurj : Function.Surjective (Submodule.mkQ (LinearMap.range φ)) :=
    Submodule.mkQ_surjective _
  have hexK : Function.Exact φ (Submodule.mkQ (LinearMap.range φ)) :=
    LinearMap.exact_map_mkQ_range φ
  have ecoker : (K ⊗[R] C) ≃ₗ[K]
      (K ⊗[R] P₂) ⧸ LinearMap.range (LinearMap.baseChange K φ) :=
    coker_tensor_equiv K φ (Submodule.mkQ (LinearMap.range φ)) hπsurj hexK
  -- finite-dimensionality of the fibres over the field `K`.
  have : Module.Finite K (K ⊗[R] P₁) := inferInstance
  have : Module.Finite K (K ⊗[R] P₂) := inferInstance
  have : Module.Finite K (K ⊗[R] C) := by
    have : Module.Finite R C := Module.Finite.of_surjective _ hπsurj
    infer_instance
  -- the fibre map is `baseChange K φ`.
  have hinj : Function.Injective (fiberMap φ q) ↔
      Module.finrank K (K ⊗[R] P₁)
        + Module.finrank K ((K ⊗[R] P₂) ⧸ LinearMap.range (LinearMap.baseChange K φ))
        = Module.finrank K (K ⊗[R] P₂) := by
    rw [fiberMap]
    exact injective_iff_finrank_eq (LinearMap.baseChange K φ)
  -- rewrite the coker finrank as `finrank K (K ⊗ C)`.
  have hcoker : Module.finrank K ((K ⊗[R] P₂) ⧸ LinearMap.range (LinearMap.baseChange K φ))
      = Module.finrank K (K ⊗[R] C) := (ecoker.finrank_eq).symm
  -- ranks of `P₁, P₂` via flat-finite fibre dimension.
  have hr1 : Module.finrank K (K ⊗[R] P₁) = Module.rankAtStalk P₁ p :=
    Ideal.finrank_fiber_eq_rankAtStalk q
  have hr2 : Module.finrank K (K ⊗[R] P₂) = Module.rankAtStalk P₂ p :=
    Ideal.finrank_fiber_eq_rankAtStalk q
  -- rank of `C` via the bridge (using `C` free at `p`).
  have hCfin : Module.Finite R C := Module.Finite.of_surjective _ hπsurj
  have hfree : Module.Free (Localization.AtPrime q) (Localization.AtPrime q ⊗[R] C) :=
    (Module.mem_freeLocus_iff_tensor p (Localization.AtPrime q)).mp hp
  have hfin : Module.Finite (Localization.AtPrime q) (Localization.AtPrime q ⊗[R] C) :=
    inferInstance
  have hrC : Module.finrank K (K ⊗[R] C) = Module.rankAtStalk C p := by
    rw [Module.rankAtStalk_eq_finrank_tensorProduct]
    exact (rankAtStalk_eq_finrank_residueField (M := C) q).symm
  have hmem : (p ∈ injLocus φ) ↔ Function.Injective (fiberMap φ q) := Iff.rfl
  rw [hmem, hinj, hcoker, hr1, hr2, hrC]

/-- **Openness of the injectivity locus.** `injLocus φ` is the subset of the open free
locus of `C = P₂ ⧸ range φ` cut out by the (locally constant) rank equation, hence open. -/
@[ega "IV 11.3.7" "special case"]
theorem isOpen_injLocus (φ : P₁ →ₗ[R] P₂) [Module.Finite R P₁] [Module.Projective R P₁]
    [Module.Finite R P₂] [Module.Projective R P₂] :
    IsOpen (injLocus φ) := by
  have hP1fp : Module.FinitePresentation R P₁ := Module.finitePresentation_of_projective R P₁
  have hP2fp : Module.FinitePresentation R P₂ := Module.finitePresentation_of_projective R P₂
  have hCfp : Module.FinitePresentation R (P₂ ⧸ LinearMap.range φ) := by
    have hsurj : Function.Surjective (Submodule.mkQ (LinearMap.range φ)) :=
      Submodule.mkQ_surjective _
    have hkerFG : (LinearMap.ker (Submodule.mkQ (LinearMap.range φ))).FG := by
      rw [Submodule.ker_mkQ]
      have h1 : (⊤ : Submodule R P₁).FG := Module.Finite.fg_top
      have h2 := h1.map φ
      simp only [Submodule.map_top] at h2
      exact h2
    exact Module.finitePresentation_of_surjective _ hsurj hkerFG
  -- The open free locus of `C = P₂ ⧸ range φ`.
  set U : Set (PrimeSpectrum R) := Module.freeLocus R (P₂ ⧸ LinearMap.range φ) with hU
  have hUopen : IsOpen U := Module.isOpen_freeLocus
  -- On the subtype `↥U`, the rank discrepancy function is locally constant.
  set h : U → ℤ := fun x =>
    (Module.rankAtStalk P₁ (x : PrimeSpectrum R) : ℤ)
      + (Module.rankAtStalk (P₂ ⧸ LinearMap.range φ) (x : PrimeSpectrum R) : ℤ)
      - (Module.rankAtStalk P₂ (x : PrimeSpectrum R) : ℤ) with hh
  have hlcP1 : IsLocallyConstant fun x : U => Module.rankAtStalk P₁ (x : PrimeSpectrum R) :=
    (Module.isLocallyConstant_rankAtStalk (M := P₁)).comp_continuous continuous_subtype_val
  have hlcP2 : IsLocallyConstant fun x : U => Module.rankAtStalk P₂ (x : PrimeSpectrum R) :=
    (Module.isLocallyConstant_rankAtStalk (M := P₂)).comp_continuous continuous_subtype_val
  have hlcC : IsLocallyConstant fun x : U =>
      Module.rankAtStalk (P₂ ⧸ LinearMap.range φ) (x : PrimeSpectrum R) :=
    Module.isLocallyConstant_rankAtStalk_freeLocus
  have hlch : IsLocallyConstant h := by
    have h1 : IsLocallyConstant fun x : U =>
        (Module.rankAtStalk P₁ (x : PrimeSpectrum R) : ℤ)
          + (Module.rankAtStalk (P₂ ⧸ LinearMap.range φ) (x : PrimeSpectrum R) : ℤ) :=
      hlcP1.comp₂ hlcC (fun a b => (a : ℤ) + (b : ℤ))
    exact h1.comp₂ hlcP2 (fun a b => a - (b : ℤ))
  -- `{x : ↥U | h x = 0}` is open in `↥U`.
  have hfiber : IsOpen {x : U | h x = 0} := hlch.isOpen_fiber 0
  -- transport to an open subset of `Spec R` contained in `U`.
  obtain ⟨V, hVopen, hV⟩ := isOpen_induced_iff.mp hfiber
  -- show `injLocus φ = V ∩ U`.
  have hset : injLocus φ = V ∩ U := by
    ext p
    constructor
    · intro hpinj
      have hpU : p ∈ U := injLocus_subset_freeLocus φ hpinj
      have hrank := (mem_injLocus_iff_rank φ p hpU).mp hpinj
      refine ⟨?_, hpU⟩
      have hmem0 : (⟨p, hpU⟩ : U) ∈ {x : U | h x = 0} := by
        simp only [Set.mem_ofPred_eq, hh]
        omega
      rwa [← hV] at hmem0
    · rintro ⟨hpV, hpU⟩
      have hmemf : (⟨p, hpU⟩ : U) ∈ {x : U | h x = 0} := by
        rwa [← hV]
      simp only [Set.mem_ofPred_eq, hh] at hmemf
      have hrank : Module.rankAtStalk P₁ p
          + Module.rankAtStalk (P₂ ⧸ LinearMap.range φ) p = Module.rankAtStalk P₂ p := by
        omega
      exact (mem_injLocus_iff_rank φ p hpU).mpr hrank
  rw [hset]
  exact hVopen.inter hUopen

/-- **(Injectivity locus.)** The injectivity locus `U` is open, and for every
`f` with `D(f) ⊆ U`:
(a) the localized map `φ_f` is injective; and
(b) `Coker(φ)_f` is finite projective over `R_f`. -/
@[stacks 00O0 "(1)",
  ega "0 19.1.12" "P₁,P₂ finite projective",
  ega "IV 11.3.7" "affine case, b)=>a)"]
theorem isOpen_injLocus_and_localized
    (φ : P₁ →ₗ[R] P₂) [Module.Finite R P₁] [Module.Projective R P₁]
    [Module.Finite R P₂] [Module.Projective R P₂] :
    IsOpen (injLocus φ) ∧
    ∀ f : R, (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ injLocus φ →
      Function.Injective (localizedMap φ f) ∧
      Module.Finite (Localization.Away f)
        (Localization.Away f ⊗[R] (P₂ ⧸ LinearMap.range φ)) ∧
      Module.Projective (Localization.Away f)
        (Localization.Away f ⊗[R] (P₂ ⧸ LinearMap.range φ)) := by
  refine ⟨isOpen_injLocus φ, fun f hf => ⟨injective_localizedMap_of_subset φ f hf, ?_, ?_⟩⟩
  · exact (finiteProjective_coker_localized φ f hf).left
  · exact (finiteProjective_coker_localized φ f hf).right

/-- **(Surjectivity locus.)** The surjectivity locus `W` is open, and for every
`f` with `D(f) ⊆ W`:
(a) the localized map `φ_f` is surjective; and
(b) `Ker(φ)_f` is finite projective over `R_f`. -/
@[stacks 00O0 "(2)"]
theorem isOpen_surjLocus_and_localized
    (φ : P₁ →ₗ[R] P₂) [Module.Finite R P₁] [Module.Projective R P₁]
    [Module.Finite R P₂] [Module.Projective R P₂] :
    IsOpen (surjLocus φ) ∧
    ∀ f : R, (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ surjLocus φ →
      Function.Surjective (localizedMap φ f) ∧
      Module.Finite (Localization.Away f)
        (Localization.Away f ⊗[R] (LinearMap.ker φ)) ∧
      Module.Projective (Localization.Away f)
        (Localization.Away f ⊗[R] (LinearMap.ker φ)) := by
  refine ⟨isOpen_surjLocus φ, fun f hf => ⟨surjective_localizedMap_of_subset φ f hf, ?_, ?_⟩⟩
  · exact (finiteProjective_ker_localized φ f hf).left
  · exact (finiteProjective_ker_localized φ f hf).right

/-- **(Isomorphism locus.)** The isomorphism locus `V` is open, and for every
`f` with `D(f) ⊆ V`, the localized map `φ_f` is bijective.

Formal consequence of Theorems 1 and 2: `isoLocus φ = injLocus φ ∩ surjLocus φ`
(`isoLocus_eq`), so it is open as an intersection of two opens; and on
`D(f) ⊆ isoLocus φ ⊆ injLocus φ` (resp. `⊆ surjLocus φ`) the localized map is both
injective (`injective_localizedMap_of_subset`) and surjective
(`surjective_localizedMap_of_subset`), hence bijective. -/
@[stacks 00O0 "(3)"]
theorem isOpen_isoLocus_and_localized
    (φ : P₁ →ₗ[R] P₂) [Module.Finite R P₁] [Module.Projective R P₁]
    [Module.Finite R P₂] [Module.Projective R P₂] :
    IsOpen (isoLocus φ) ∧
    ∀ f : R, (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ isoLocus φ →
      Function.Bijective (localizedMap φ f) := by
  have hsub : isoLocus φ = injLocus φ ∩ surjLocus φ := isoLocus_eq φ
  refine ⟨?_, fun f hf => ?_⟩
  · rw [hsub]
    exact (isOpen_injLocus φ).inter (isOpen_surjLocus φ)
  · have hinj : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ injLocus φ := by
      rw [hsub] at hf; exact hf.trans Set.inter_subset_left
    have hsurj : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆ surjLocus φ := by
      rw [hsub] at hf; exact hf.trans Set.inter_subset_right
    exact ⟨injective_localizedMap_of_subset φ f hinj,
      surjective_localizedMap_of_subset φ f hsurj⟩

end Stacks.FiniteProjective.MapLocus
