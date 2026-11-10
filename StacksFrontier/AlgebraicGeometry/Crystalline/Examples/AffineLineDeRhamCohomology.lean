module

public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import StacksCore.Tactic.StacksAttribute

/-!
# The two term complex of [Stacks, Tag 07LK] for `r = 1`

[Stacks, Tag 07LK] draws four conclusions from the complex `D → Ω¹_D → ⋯ → Ω^r_D`, and then
works out what that complex is for `r = 1`: it is the two term complex of `p`-adically complete
modules

`d : D = (⨁_{n ≥ 0} 𝐙_p x^n)^∧ ⟶ Ω¹_D = (⨁_{n ≥ 1} 𝐙_p x^{n-1} dx)^∧`,

whose map "is given by `diag(0, 1, 2, 3, 4, …)` except that the first summand is missing on the
right hand side".  This module builds that complex and proves for it the conclusions (2), (3) and
(4) of the source, by the source's own arguments.

Writing `x^n ↦ e_n` for the left hand side and `x^{n-1} dx ↦ e_{n-1}` for the right hand side,
both modules are the `p`-adic completion `Crystalline.AffineLineDeRham.completedMonomials` of the
free `𝐙_p`-module `ℕ →₀ 𝐙_p`, and the map is
`Crystalline.AffineLineDeRham.completedDifferential`, the completion of `e_n ↦ n e_{n-1}`; on
coefficients it is `c_n ↦ (n + 1) c_{n+1}`, which is the source's `diag(0, 1, 2, 3, …)` with the
`n = 0` column zero.

## Main definitions

* `Crystalline.AffineLineDeRham.monomials` and
  `Crystalline.AffineLineDeRham.completedMonomials` — the free module `⨁_n 𝐙_p x^n` on the
  monomials and its `p`-adic completion, which is both terms of the displayed complex.
* `Crystalline.AffineLineDeRham.differential` and
  `Crystalline.AffineLineDeRham.completedDifferential` — the map `diag(0, 1, 2, 3, …)` and its
  completion.
* `Crystalline.AffineLineDeRham.coeff` — the `n`-th coefficient of an element of the completion,
  a `𝐙_p`-linear functional, which is what every computation below is carried out with.
* `Crystalline.AffineLineDeRham.cohomologyOne` — the cokernel of the displayed map, that is the
  degree one cohomology of the two term complex.
* `Crystalline.AffineLineDeRham.omega` and `Crystalline.AffineLineDeRham.eta` — the source's two
  elements `ω = ∑_{e > 0} p^e x^{p^{2e} - 1} dx` and `η = ∑_{e > 0} p^e x^{p^e - 1} dx`.

## Main results

* `Crystalline.AffineLineDeRham.completedDifferential_eq_zero_iff` and
  `Crystalline.AffineLineDeRham.kerEquiv` — **conclusion (2) for the displayed complex**: the
  kernel of the map is the constants, so the degree zero cohomology of the two term complex is
  `𝐙_p`.
* `Crystalline.AffineLineDeRham.infinite_cohomologyOne` and
  `Crystalline.AffineLineDeRham.not_isTorsion_cohomologyOne` — **conclusion (3)**: the cokernel
  is infinite, and the class of `ω` is not a torsion element, so the cokernel is not a torsion
  abelian group.
* `Crystalline.AffineLineDeRham.not_isHausdorff_cohomologyOne` — **conclusion (4)**: the class of
  `η` is nonzero and lies in every `p^t · H¹`, so the cokernel is not separated for the `p`-adic
  topology.

## How the computations are done

Everything is read off coefficients.  `Crystalline.AffineLineDeRham.coeff` is the completion of
the `n`-th coordinate `ℕ →₀ 𝐙_p → 𝐙_p` followed by the inverse of `𝐙_p ≅ (𝐙_p)^∧`, and
`Crystalline.AffineLineDeRham.coeff_sub_mem` says that it agrees modulo `p^e` with the `n`-th
coefficient of any representative of the level `e` of the element.  That single lemma gives the
coefficients of the completed differential
(`Crystalline.AffineLineDeRham.coeff_completedDifferential`), the fact that an element is
determined by its coefficients (`Crystalline.AffineLineDeRham.ext_coeff`, which needs that a
finitely supported family all of whose coefficients are divisible by `p^e` is `p^e` times a
finitely supported family), and the coefficients of `ω` and of `η`, which are defined as the
limits of their own partial sums.

The three conclusions are then the source's own arguments.  If `n ω = d(y)` then comparing the
coefficient at `x^{p^{2e} - 1} dx` gives `n = p^e c` for every `e`, so `n = 0`; this is where the
exponent `p^{2e}` paired with the coefficient `p^e` does its work.  The element `η` has, by
construction, partial sums which are themselves in the image of `d` — the partial sum up to `t`
is `d(∑_{0 < e ≤ t} x^{p^e})` — so its class is divisible by `p^t` for every `t`; and `η` is not
in the image of `d`, because a preimage would have to have coefficient `1` at `x^{p^e}` for every
`e`, while an element of the completion has all but finitely many coefficients in `(p)`.

## The relation to the rest of the example

What this module is about is the explicit two term complex the source itself writes down for
`r = 1`, with its two terms the completions of the free modules on the monomials and on the
`x^{n-1} dx`, and the source's own arguments on it.  The four conclusions of the example are proved
for `H^j(Cris(X/S), 𝒪_{X/S})` itself, at every rank `r`, in
`StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineSpaceCrystallineCohomology`, from the
completed divided power de Rham complex of `D = 𝐙_p[x_1, …, x_r]^∧`
(`StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineSpaceDeRhamTopDegree` for the top
degree).

## References

* [Stacks Project, Tag 07LK](https://stacks.math.columbia.edu/tag/07LK)
* [Stacks Project, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public noncomputable section

namespace Crystalline

namespace AffineLineDeRham

variable (p : ℕ) [Fact p.Prime]

/-! ### The modules of the displayed complex -/

/-- The divided power ideal `(p) ⊆ 𝐙_p` of the crystalline base of [Stacks, Tag 07LK]. -/
public abbrev baseIdeal : Ideal ℤ_[p] := Ideal.span {(p : ℤ_[p])}

/-- `𝐙_p` is `p`-adically complete. -/
public instance instIsAdicCompleteBase : IsAdicComplete (baseIdeal p) ℤ_[p] := by
  change IsAdicComplete (Ideal.span {(p : ℤ_[p])}) ℤ_[p]
  rw [← PadicInt.maximalIdeal_eq_span_p]
  infer_instance

/-- The free `𝐙_p`-module `⨁_{n ≥ 0} 𝐙_p x^n` on the monomials of `𝐙_p[x]`, the monomial `x^n`
being the basis vector `e_n`. -/
public abbrev monomials : Type := ℕ →₀ ℤ_[p]

/-- The `p`-adic completion `(⨁_{n ≥ 0} 𝐙_p x^n)^∧` of the module of monomials.  This is both
terms of the two term complex displayed in [Stacks, Tag 07LK] for `r = 1`: on the left `e_n` is
`x^n`, and on the right `e_n` is `x^n dx`, so that the right hand side is the completion of
`⨁_{n ≥ 1} 𝐙_p x^{n-1} dx`. -/
public abbrev completedMonomials : Type := AdicCompletion (baseIdeal p) (monomials p)

/-! ### Divisibility by powers of `p` -/

/-- A multiple of `p^e` lies in the `e`-th step of the `p`-adic filtration. -/
private lemma pow_smul_mem {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] (e : ℕ) (v : M) :
    (p : ℤ_[p]) ^ e • v ∈ (baseIdeal p ^ e • (⊤ : Submodule ℤ_[p] M)) := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
  exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨v, Submodule.mem_top, rfl⟩

/-- An element of the `e`-th step of the `p`-adic filtration is a multiple of `p^e`. -/
private lemma exists_eq_pow_smul {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] {e : ℕ} {v : M}
    (h : v ∈ (baseIdeal p ^ e • (⊤ : Submodule ℤ_[p] M))) : ∃ w, v = (p : ℤ_[p]) ^ e • w := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at h
  obtain ⟨w, -, hw⟩ := h
  exact ⟨w, hw.symm⟩

/-- The `p`-adic filtration is decreasing. -/
private lemma pow_smul_le {M : Type*} [AddCommGroup M] [Module ℤ_[p] M] {e f : ℕ} (h : e ≤ f) :
    (baseIdeal p ^ f • (⊤ : Submodule ℤ_[p] M)) ≤ (baseIdeal p ^ e • ⊤) :=
  Submodule.smul_mono (Ideal.pow_le_pow_right h) le_rfl

/-- Two `p`-adic integers congruent modulo every power of `p` are equal. -/
private lemma eq_of_forall_sub_mem {a b : ℤ_[p]}
    (h : ∀ e : ℕ, a - b ∈ (baseIdeal p ^ e • (⊤ : Submodule ℤ_[p] ℤ_[p]))) : a = b :=
  (IsHausdorff.eq_iff_smodEq (I := baseIdeal p)).mpr fun e ↦ SModEq.sub_mem.mpr (h e)

/-- The image of a multiple of `p^e` in a quotient is a multiple of `p^e`. -/
private lemma mkQ_mem_pow_smul {M : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    (N : Submodule ℤ_[p] M) {e : ℕ} {v : M}
    (h : v ∈ (baseIdeal p ^ e • (⊤ : Submodule ℤ_[p] M))) :
    N.mkQ v ∈ (baseIdeal p ^ e • (⊤ : Submodule ℤ_[p] (M ⧸ N))) := by
  obtain ⟨w, rfl⟩ := exists_eq_pow_smul p h
  rw [map_smul]
  exact pow_smul_mem p e _

/-- A finitely supported family all of whose coefficients are divisible by `p^e` is `p^e` times a
finitely supported family. -/
private lemma mem_pow_smul_top_iff (e : ℕ) (f : monomials p) :
    f ∈ (baseIdeal p ^ e • (⊤ : Submodule ℤ_[p] (monomials p))) ↔
      ∀ n, f n ∈ (baseIdeal p ^ e • (⊤ : Submodule ℤ_[p] ℤ_[p])) := by
  classical
  refine ⟨fun h n ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨g, rfl⟩ := exists_eq_pow_smul p h
    rw [Finsupp.smul_apply]
    exact pow_smul_mem p e (g n)
  · choose g hg using fun n ↦ exists_eq_pow_smul p (h n)
    have hp0 : ((p : ℤ_[p]) ^ e) ≠ 0 :=
      pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    have hsupp : ∀ n, g n ≠ 0 → n ∈ f.support := by
      intro n hn
      refine Finsupp.mem_support_iff.mpr ?_
      rw [hg n]
      exact smul_ne_zero hp0 hn
    have hf : f = (p : ℤ_[p]) ^ e • Finsupp.onFinset f.support g hsupp := by
      ext n
      rw [Finsupp.smul_apply, Finsupp.onFinset_apply, ← hg n]
    rw [hf]
    exact pow_smul_mem p e _

/-- A monomial with coefficient divisible by `p^k` lies in the `t`-th step of the `p`-adic
filtration, for every `t ≤ k`. -/
private lemma single_pow_mem {t k : ℕ} (h : t ≤ k) (m : ℕ) :
    Finsupp.single m ((p : ℤ_[p]) ^ k) ∈
      (baseIdeal p ^ t • (⊤ : Submodule ℤ_[p] (monomials p))) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, ← smul_eq_mul, ← Finsupp.smul_single]
  exact pow_smul_mem p t _

/-! ### The differential `diag(0, 1, 2, 3, …)` -/

/-- The map of the displayed complex, before completion: `x^n ↦ n x^{n-1} dx`, which in the
matched indexing of the two sides is `diag(0, 1, 2, 3, …)`.  In coefficients, the `n`-th
coefficient of `d(f)` is `(n + 1)` times the `(n+1)`-st coefficient of `f`. -/
public def differential : monomials p →ₗ[ℤ_[p]] monomials p where
  toFun f :=
    Finsupp.onFinset (f.support.image (· - 1)) (fun m ↦ ((m + 1 : ℕ) : ℤ_[p]) * f (m + 1))
      (by
        intro m hm
        refine Finset.mem_image.mpr ⟨m + 1, Finsupp.mem_support_iff.mpr ?_, by simp⟩
        exact right_ne_zero_of_mul hm)
  map_add' f g := by
    ext m
    simp [Finsupp.onFinset_apply, mul_add]
  map_smul' c f := by
    ext m
    simp only [Finsupp.onFinset_apply, Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The `m`-th coefficient of `differential p f` is `(m + 1)` times the `(m + 1)`-st coefficient of
`f`. -/
@[simp]
public theorem differential_apply (f : monomials p) (m : ℕ) :
    differential p f m = ((m + 1 : ℕ) : ℤ_[p]) * f (m + 1) := rfl

/-- The map of the two term complex displayed in [Stacks, Tag 07LK] for `r = 1`: the `p`-adic
completion of `diag(0, 1, 2, 3, …)`. -/
public def completedDifferential : completedMonomials p →ₗ[ℤ_[p]] completedMonomials p :=
  (AdicCompletion.map (baseIdeal p) (differential p)).restrictScalars ℤ_[p]

/-- The completed differential agrees with `diag(0, 1, 2, 3, …)` on the dense image of the
monomials. -/
public theorem completedDifferential_of (f : monomials p) :
    completedDifferential p (AdicCompletion.of (baseIdeal p) (monomials p) f)
      = AdicCompletion.of (baseIdeal p) (monomials p) (differential p f) :=
  AdicCompletion.map_of _ _ _

/-! ### Coefficients -/

/-- The `n`-th coefficient of an element of `(⨁_{n ≥ 0} 𝐙_p x^n)^∧`. -/
public def coeff (n : ℕ) : completedMonomials p →ₗ[ℤ_[p]] ℤ_[p] :=
  (AdicCompletion.ofLinearEquiv (baseIdeal p) ℤ_[p]).symm.toLinearMap ∘ₗ
    (AdicCompletion.map (baseIdeal p) (Finsupp.lapply (M := ℤ_[p]) (R := ℤ_[p]) n)).restrictScalars
      ℤ_[p]

/-- The `n`-th coefficient of the image of `f` in the completion is the `n`-th coefficient of `f`.
-/
@[simp]
public theorem coeff_of (n : ℕ) (f : monomials p) :
    coeff p n (AdicCompletion.of (baseIdeal p) (monomials p) f) = f n := by
  simp only [coeff, LinearMap.comp_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    AdicCompletion.map_of, AdicCompletion.ofLinearEquiv_symm_of,
    Finsupp.lapply_apply]

private lemma of_coeff (n : ℕ) (x : completedMonomials p) :
    AdicCompletion.of (baseIdeal p) ℤ_[p] (coeff p n x)
      = AdicCompletion.map (baseIdeal p) (Finsupp.lapply (M := ℤ_[p]) (R := ℤ_[p]) n) x := by
  simp only [coeff, LinearMap.comp_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  exact AdicCompletion.of_ofLinearEquiv_symm _ _

/-- **The coefficients are computed at any level.**  The `n`-th coefficient of `x` agrees modulo
`p^e` with the `n`-th coefficient of any representative of the level `e` of `x`. -/
public theorem coeff_sub_mem (n : ℕ) {e : ℕ} (x : completedMonomials p) (f : monomials p)
    (hf : x.val e = Submodule.Quotient.mk f) :
    coeff p n x - f n ∈ (baseIdeal p ^ e • (⊤ : Submodule ℤ_[p] ℤ_[p])) := by
  have h1 : (AdicCompletion.of (baseIdeal p) ℤ_[p] (coeff p n x)).val e
      = Submodule.Quotient.mk (f n) := by
    rw [of_coeff, AdicCompletion.map_val_apply, hf]
    rfl
  rw [AdicCompletion.of_apply, Submodule.mkQ_apply] at h1
  exact (Submodule.Quotient.eq _).mp h1

/-- The level `t` of the limit of a Cauchy sequence of monomials is the class of its `t`-th
term. -/
private lemma val_mk (g : ℕ → monomials p)
    (hg : ∀ n, g n ≡ g (n + 1)
      [SMOD (baseIdeal p ^ n • (⊤ : Submodule ℤ_[p] (monomials p)))]) (t : ℕ) :
    (AdicCompletion.mk (baseIdeal p) (monomials p)
        (AdicCompletion.AdicCauchySequence.mk (I := baseIdeal p) (M := monomials p) g hg)).val t
      = Submodule.Quotient.mk (g t) := rfl

/-- **An element of the completion is determined by its coefficients.** -/
public theorem ext_coeff {x y : completedMonomials p} (h : ∀ n, coeff p n x = coeff p n y) :
    x = y := by
  have hz : ∀ n, coeff p n (x - y) = 0 := by
    intro n
    rw [map_sub, h n, sub_self]
  have hval : ∀ e, (x - y).val e = 0 := by
    intro e
    obtain ⟨f, hf⟩ := Submodule.Quotient.mk_surjective
      (baseIdeal p ^ e • (⊤ : Submodule ℤ_[p] (monomials p))) ((x - y).val e)
    have hmem : f ∈ (baseIdeal p ^ e • (⊤ : Submodule ℤ_[p] (monomials p))) := by
      rw [mem_pow_smul_top_iff]
      intro n
      have h' := coeff_sub_mem p n (x - y) f hf.symm
      rwa [hz n, zero_sub, neg_mem_iff] at h'
    rw [← hf, Submodule.Quotient.mk_eq_zero]
    exact hmem
  have := AdicCompletion.ext (x := x - y) (y := 0) hval
  rwa [sub_eq_zero] at this

/-- **The source's `diag(0, 1, 2, 3, …)`, in coefficients.**  The `n`-th coefficient of `d(x)` is
`(n + 1)` times the `(n+1)`-st coefficient of `x`; in particular the `n = 0` column of the matrix
is zero, which is the source's "the first summand is missing on the right hand side". -/
public theorem coeff_completedDifferential (n : ℕ) (x : completedMonomials p) :
    coeff p n (completedDifferential p x) = ((n + 1 : ℕ) : ℤ_[p]) * coeff p (n + 1) x := by
  refine eq_of_forall_sub_mem p fun e ↦ ?_
  obtain ⟨f, hf⟩ := Submodule.Quotient.mk_surjective
    (baseIdeal p ^ e • (⊤ : Submodule ℤ_[p] (monomials p))) (x.val e)
  have hd : (completedDifferential p x).val e = Submodule.Quotient.mk (differential p f) := by
    change (AdicCompletion.map (baseIdeal p) (differential p) x).val e = _
    rw [AdicCompletion.map_val_apply, ← hf]
    rfl
  have h1 := coeff_sub_mem p n (completedDifferential p x) (differential p f) hd
  have h2 := coeff_sub_mem p (n + 1) x f hf.symm
  have key : coeff p n (completedDifferential p x) - ((n + 1 : ℕ) : ℤ_[p]) * coeff p (n + 1) x
      = (coeff p n (completedDifferential p x) - differential p f n)
        - ((n + 1 : ℕ) : ℤ_[p]) • (coeff p (n + 1) x - f (n + 1)) := by
    rw [differential_apply]
    simp only [smul_eq_mul]
    ring
  rw [key]
  exact Submodule.sub_mem _ h1 (Submodule.smul_mem _ _ h2)

/-! ### Conclusion (2): the kernel is `𝐙_p` -/

/-- The constants are in the kernel: `d(a) = 0`. -/
public theorem completedDifferential_of_single_zero (a : ℤ_[p]) :
    completedDifferential p
        (AdicCompletion.of (baseIdeal p) (monomials p) (Finsupp.single 0 a)) = 0 := by
  have h : differential p (Finsupp.single 0 a) = 0 := by
    ext n
    rw [differential_apply, Finsupp.single_apply]
    simp
  rw [completedDifferential_of, h, map_zero]

/-- **Conclusion (2) of [Stacks, Tag 07LK] for the displayed complex.**  An element of
`D = (⨁_{n ≥ 0} 𝐙_p x^n)^∧` is killed by `diag(0, 1, 2, 3, …)` exactly when it is a constant. -/
public theorem completedDifferential_eq_zero_iff (x : completedMonomials p) :
    completedDifferential p x = 0 ↔
      x = AdicCompletion.of (baseIdeal p) (monomials p) (Finsupp.single 0 (coeff p 0 x)) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine ext_coeff p fun n ↦ ?_
    rw [coeff_of]
    match n with
    | 0 => rw [Finsupp.single_eq_same]
    | (m + 1) =>
      have hc := coeff_completedDifferential p m x
      rw [h, map_zero] at hc
      have hne : ((m + 1 : ℕ) : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
      have hz : coeff p (m + 1) x = 0 := by
        rcases mul_eq_zero.mp hc.symm with h' | h'
        · exact absurd h' hne
        · exact h'
      rw [hz, Finsupp.single_apply, ite_eq_right (Nat.succ_ne_zero m).symm]
  · rw [h]
    exact completedDifferential_of_single_zero p _

/-- **Conclusion (2) of [Stacks, Tag 07LK] for the displayed complex, as an identification.**
The degree zero cohomology of the two term complex the source works out for `r = 1` — the kernel
of `diag(0, 1, 2, 3, …)` — is `𝐙_p`, by the constant coefficient. -/
public def kerEquiv : LinearMap.ker (completedDifferential p) ≃ₗ[ℤ_[p]] ℤ_[p] := by
  refine LinearEquiv.ofBijective
    ((coeff p 0).comp (LinearMap.ker (completedDifferential p)).subtype) ⟨?_, ?_⟩
  · intro u v huv
    simp only [LinearMap.comp_apply, Submodule.coe_subtype] at huv
    have hu := (completedDifferential_eq_zero_iff p u.1).mp (LinearMap.mem_ker.mp u.2)
    have hv := (completedDifferential_eq_zero_iff p v.1).mp (LinearMap.mem_ker.mp v.2)
    exact Subtype.ext (by rw [hu, hv, huv])
  · intro a
    refine ⟨⟨AdicCompletion.of (baseIdeal p) (monomials p) (Finsupp.single 0 a),
      LinearMap.mem_ker.mpr (completedDifferential_of_single_zero p a)⟩, ?_⟩
    simp only [LinearMap.comp_apply, Submodule.coe_subtype, coeff_of]
    exact Finsupp.single_eq_same

/-! ### The cokernel -/

/-- The degree one cohomology of the two term complex displayed in [Stacks, Tag 07LK] for
`r = 1`: the cokernel of `diag(0, 1, 2, 3, …)`. -/
public abbrev cohomologyOne : Type :=
  completedMonomials p ⧸ LinearMap.range (completedDifferential p)

/-- The class of an element of `Ω¹_D` in the degree one cohomology. -/
public def mkCohomologyOne : completedMonomials p →ₗ[ℤ_[p]] cohomologyOne p :=
  (LinearMap.range (completedDifferential p)).mkQ

/-- A class in the degree one cohomology vanishes exactly when the element is a value of the
differential. -/
public theorem mkCohomologyOne_eq_zero_iff (x : completedMonomials p) :
    mkCohomologyOne p x = 0 ↔ x ∈ LinearMap.range (completedDifferential p) := by
  change (LinearMap.range (completedDifferential p)).mkQ x = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

/-! ### Conclusion (3): the cokernel is infinite and not torsion -/

/-- Partial sums `∑_{e < t} p^{e+1} x^{m e}` of monomials with growing `p`-power coefficients form
a `p`-adic Cauchy sequence. -/
private lemma sum_single_cauchy (m : ℕ → ℕ) (t : ℕ) :
    (∑ e ∈ Finset.range t, Finsupp.single (m e) ((p : ℤ_[p]) ^ (e + 1)) : monomials p) ≡
      ∑ e ∈ Finset.range (t + 1), Finsupp.single (m e) ((p : ℤ_[p]) ^ (e + 1))
      [SMOD (baseIdeal p ^ t • (⊤ : Submodule ℤ_[p] (monomials p)))] := by
  rw [SModEq.sub_mem, Finset.sum_range_succ, sub_add_eq_sub_sub, sub_self, zero_sub, neg_mem_iff]
  exact single_pow_mem p (Nat.le_succ t) _

/-- The partial sums `∑_{0 < e ≤ t} p^e x^{p^{2e} - 1} dx` of the source's element `ω`. -/
public def omegaPartial (t : ℕ) : monomials p :=
  ∑ e ∈ Finset.range t, Finsupp.single (p ^ (2 * (e + 1)) - 1) ((p : ℤ_[p]) ^ (e + 1))

/-- The partial sums of `ω` form a `p`-adic Cauchy sequence. -/
public theorem omegaPartial_cauchy (t : ℕ) :
    omegaPartial p t ≡ omegaPartial p (t + 1)
      [SMOD (baseIdeal p ^ t • (⊤ : Submodule ℤ_[p] (monomials p)))] :=
  sum_single_cauchy p _ t

/-- The source's element `ω = ∑_{e > 0} p^e x^{p^{2e} - 1} dx` of `Ω¹_D`. -/
public def omega : completedMonomials p :=
  AdicCompletion.mk (baseIdeal p) (monomials p)
    (AdicCompletion.AdicCauchySequence.mk (I := baseIdeal p) (M := monomials p)
      (omegaPartial p) (omegaPartial_cauchy p))

/-- The `p^(u e) - 1`-st coefficient of `∑_{j < s} p^{j+1} x^{p^(u j) - 1}` is `p^{e+1}` for
`e < s`, as `u` is injective. -/
private lemma sum_single_pow_apply {u : ℕ → ℕ} (hu : Function.Injective u) {s e : ℕ} (h : e < s) :
    (∑ j ∈ Finset.range s, Finsupp.single (p ^ u j - 1) ((p : ℤ_[p]) ^ (j + 1)) : monomials p)
      (p ^ u e - 1) = (p : ℤ_[p]) ^ (e + 1) := by
  classical
  have hp : p.Prime := Fact.out
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single_of_mem e (Finset.mem_range.mpr h)]
  · exact Finsupp.single_eq_same
  · intro j _ hj
    refine Finsupp.single_eq_of_ne fun hcontra ↦ hj ?_
    have h1 : 1 ≤ p ^ u j := Nat.one_le_pow _ _ hp.pos
    have h2 : 1 ≤ p ^ u e := Nat.one_le_pow _ _ hp.pos
    have h3 : p ^ u j = p ^ u e := by omega
    exact hu (Nat.pow_right_injective hp.two_le h3)

private lemma omegaPartial_apply {s e : ℕ} (h : e < s) :
    omegaPartial p s (p ^ (2 * (e + 1)) - 1) = (p : ℤ_[p]) ^ (e + 1) :=
  sum_single_pow_apply p (u := fun j ↦ 2 * (j + 1)) (fun a b hab ↦ by simp only at hab; omega) h

/-- If the levels of `x` are the classes of the `g t`, and `g s` has `n`-th coefficient `c` for all
large `s`, then the `n`-th coefficient of `x` is `c`. -/
private lemma coeff_eq_of_val_eq {x : completedMonomials p} {g : ℕ → monomials p}
    (hx : ∀ t, x.val t = Submodule.Quotient.mk (g t)) {n e : ℕ} {c : ℤ_[p]}
    (hg : ∀ s, e ≤ s → g s n = c) : coeff p n x = c := by
  refine eq_of_forall_sub_mem p fun t ↦ ?_
  refine pow_smul_le p (le_max_left t e) ?_
  have h := coeff_sub_mem p n x (g (max t e)) (hx _)
  rwa [hg _ (le_max_right t e)] at h

/-- The coefficient of `ω` at `x^{p^{2e} - 1} dx` is `p^e`. -/
public theorem coeff_omega (e : ℕ) :
    coeff p (p ^ (2 * (e + 1)) - 1) (omega p) = (p : ℤ_[p]) ^ (e + 1) := by
  exact coeff_eq_of_val_eq p (fun t ↦ val_mk p (omegaPartial p) (omegaPartial_cauchy p) t)
    (e := e + 1) fun s hs ↦ omegaPartial_apply p hs

/-- **The source's `ω` is not a torsion element.**  No positive multiple of
`ω = ∑_{e > 0} p^e x^{p^{2e} - 1} dx` is a value of `diag(0, 1, 2, 3, …)`: comparing coefficients
at `x^{p^{2e} - 1} dx` makes `n` divisible by `p^e` for every `e`. -/
public theorem nsmul_omega_notMem_range {n : ℕ} (hn : n ≠ 0) :
    n • omega p ∉ LinearMap.range (completedDifferential p) := by
  have hp : p.Prime := Fact.out
  intro hmem
  obtain ⟨y, hy⟩ := hmem
  have hp0 : ∀ k : ℕ, ((p : ℤ_[p]) ^ k) ≠ 0 := fun k ↦
    pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
  have key : ∀ e : ℕ, (n : ℤ_[p]) ∈ (baseIdeal p ^ (e + 1) • (⊤ : Submodule ℤ_[p] ℤ_[p])) := by
    intro e
    have h1 : coeff p (p ^ (2 * (e + 1)) - 1) (n • omega p)
        = (n : ℤ_[p]) * (p : ℤ_[p]) ^ (e + 1) := by
      rw [map_nsmul, coeff_omega, nsmul_eq_mul]
    have h2 : coeff p (p ^ (2 * (e + 1)) - 1) (completedDifferential p y)
        = ((p : ℤ_[p]) ^ (2 * (e + 1))) * coeff p (p ^ (2 * (e + 1))) y := by
      have h3 := coeff_completedDifferential p (p ^ (2 * (e + 1)) - 1) y
      rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)] at h3
      rw [h3]
      norm_cast
    rw [hy, h1] at h2
    have h4 : (n : ℤ_[p]) * (p : ℤ_[p]) ^ (e + 1)
        = ((p : ℤ_[p]) ^ (e + 1) * coeff p (p ^ (2 * (e + 1))) y) * (p : ℤ_[p]) ^ (e + 1) := by
      rw [h2, two_mul, pow_add]
      ring
    have h5 := mul_right_cancel₀ (hp0 (e + 1)) h4
    rw [h5, ← smul_eq_mul]
    exact pow_smul_mem p (e + 1) _
  have hzero : (n : ℤ_[p]) = 0 := by
    refine eq_of_forall_sub_mem p fun t ↦ ?_
    rw [sub_zero]
    exact pow_smul_le p (Nat.le_succ t) (key t)
  exact hn (Nat.cast_eq_zero.mp hzero)

/-- **Conclusion (3) of [Stacks, Tag 07LK] for the displayed complex, second clause.**  The
cokernel of `diag(0, 1, 2, 3, …)` is not a torsion abelian group: the class of the source's
`ω = ∑_{e > 0} p^e x^{p^{2e} - 1} dx` has no positive multiple equal to zero. -/
public theorem not_isTorsion_cohomologyOne : ¬ IsAddTorsion (cohomologyOne p) := by
  intro htor
  obtain ⟨n, hn, hzero⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp (htor (mkCohomologyOne p (omega p)))
  rw [← map_nsmul, mkCohomologyOne_eq_zero_iff] at hzero
  exact nsmul_omega_notMem_range p hn.ne' hzero

/-- **Conclusion (3) of [Stacks, Tag 07LK] for the displayed complex, first clause.**  The
cokernel of `diag(0, 1, 2, 3, …)` is infinite: the multiples of the class of `ω` are pairwise
distinct. -/
public theorem infinite_cohomologyOne : Infinite (cohomologyOne p) := by
  have hne : ∀ k : ℕ, k ≠ 0 → k • mkCohomologyOne p (omega p) ≠ 0 := by
    intro k hk hzero
    rw [← map_nsmul, mkCohomologyOne_eq_zero_iff] at hzero
    exact nsmul_omega_notMem_range p hk hzero
  have key : ∀ a b : ℕ, a ≤ b → a • mkCohomologyOne p (omega p)
      = b • mkCohomologyOne p (omega p) → a = b := by
    intro a b hle heq
    have hsplit : (b - a) • mkCohomologyOne p (omega p) + a • mkCohomologyOne p (omega p)
        = b • mkCohomologyOne p (omega p) := by
      rw [← add_nsmul, Nat.sub_add_cancel hle]
    have : (b - a) • mkCohomologyOne p (omega p) = 0 := by
      have h0 : (b - a) • mkCohomologyOne p (omega p) + a • mkCohomologyOne p (omega p)
          = 0 + a • mkCohomologyOne p (omega p) := by
        rw [hsplit, zero_add, heq]
      exact add_right_cancel h0
    by_contra hne'
    exact hne (b - a) (by omega) this
  refine Infinite.of_injective (fun k : ℕ ↦ k • mkCohomologyOne p (omega p)) ?_
  intro a b hab
  have hab' : a • mkCohomologyOne p (omega p) = b • mkCohomologyOne p (omega p) := hab
  rcases Nat.le_total a b with h | h
  · exact key a b h hab'
  · exact (key b a h hab'.symm).symm

/-! ### Conclusion (4): the cokernel is not `p`-adically separated -/

/-- The polynomial `∑_{0 < e ≤ t} x^{p^e}`, whose differential is the `t`-th partial sum of the
source's element `η`. -/
private def etaPoly (t : ℕ) : monomials p :=
  ∑ e ∈ Finset.range t, Finsupp.single (p ^ (e + 1)) 1

/-- The partial sums `∑_{0 < e ≤ t} p^e x^{p^e - 1} dx` of the source's element `η`. -/
public def etaPartial (t : ℕ) : monomials p :=
  ∑ e ∈ Finset.range t, Finsupp.single (p ^ (e + 1) - 1) ((p : ℤ_[p]) ^ (e + 1))

private lemma differential_single_one {m : ℕ} (hm : 1 ≤ m) :
    differential p (Finsupp.single m 1) = Finsupp.single (m - 1) ((m : ℕ) : ℤ_[p]) := by
  ext n
  rw [differential_apply, Finsupp.single_apply, Finsupp.single_apply]
  by_cases h : m = n + 1
  · subst h
    simp
  · rw [ite_eq_right h, mul_zero, ite_eq_right (by omega)]

/-- The `t`-th partial sum of `η` is the differential of `∑_{0 < e ≤ t} x^{p^e}`. -/
private lemma differential_etaPoly (t : ℕ) : differential p (etaPoly p t) = etaPartial p t := by
  have hp : p.Prime := Fact.out
  rw [etaPoly, etaPartial, map_sum]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [differential_single_one p (Nat.one_le_pow _ _ hp.pos)]
  norm_cast

/-- The partial sums of `η` form a `p`-adic Cauchy sequence. -/
public theorem etaPartial_cauchy (t : ℕ) :
    etaPartial p t ≡ etaPartial p (t + 1)
      [SMOD (baseIdeal p ^ t • (⊤ : Submodule ℤ_[p] (monomials p)))] :=
  sum_single_cauchy p _ t

/-- The source's element `η = ∑_{e > 0} p^e x^{p^e - 1} dx` of `Ω¹_D`. -/
public def eta : completedMonomials p :=
  AdicCompletion.mk (baseIdeal p) (monomials p)
    (AdicCompletion.AdicCauchySequence.mk (I := baseIdeal p) (M := monomials p)
      (etaPartial p) (etaPartial_cauchy p))

/-- The level `t` of `η` is the class of its `t`-th partial sum. -/
private lemma eta_val (t : ℕ) : (eta p).val t = Submodule.Quotient.mk (etaPartial p t) :=
  val_mk p (etaPartial p) (etaPartial_cauchy p) t

private lemma etaPartial_apply {s e : ℕ} (h : e < s) :
    etaPartial p s (p ^ (e + 1) - 1) = (p : ℤ_[p]) ^ (e + 1) :=
  sum_single_pow_apply p (u := fun j ↦ j + 1) (fun a b hab ↦ by simp only at hab; omega) h

/-- The coefficient of `η` at `x^{p^e - 1} dx` is `p^e`. -/
public theorem coeff_eta (e : ℕ) :
    coeff p (p ^ (e + 1) - 1) (eta p) = (p : ℤ_[p]) ^ (e + 1) := by
  exact coeff_eq_of_val_eq p (eta_val p) (e := e + 1) fun s hs ↦ etaPartial_apply p hs

/-- **The source's `η` is not a value of the differential.**  A preimage would have to have
coefficient `1` at `x^{p^e}` for every `e`, and an element of the completion has all but finitely
many coefficients divisible by `p`. -/
public theorem eta_notMem_range : eta p ∉ LinearMap.range (completedDifferential p) := by
  classical
  have hp : p.Prime := Fact.out
  intro hmem
  obtain ⟨y, hy⟩ := hmem
  have hp0 : ∀ k : ℕ, ((p : ℤ_[p]) ^ k) ≠ 0 := fun k ↦
    pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hone : ∀ e : ℕ, coeff p (p ^ (e + 1)) y = 1 := by
    intro e
    have h3 := coeff_completedDifferential p (p ^ (e + 1) - 1) y
    rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos), hy, coeff_eta] at h3
    push_cast at h3
    have h4 : (p : ℤ_[p]) ^ (e + 1) * coeff p (p ^ (e + 1)) y = (p : ℤ_[p]) ^ (e + 1) * 1 := by
      rw [mul_one]
      exact h3.symm
    exact mul_left_cancel₀ (hp0 (e + 1)) h4
  obtain ⟨f, hf⟩ := Submodule.Quotient.mk_surjective
    (baseIdeal p ^ 1 • (⊤ : Submodule ℤ_[p] (monomials p))) (y.val 1)
  have hsupp : ∀ e : ℕ, p ^ (e + 1) ∈ f.support := by
    intro e
    refine Finsupp.mem_support_iff.mpr fun hzero ↦ ?_
    have h := coeff_sub_mem p (p ^ (e + 1)) y f hf.symm
    rw [hone e, hzero, sub_zero] at h
    obtain ⟨w, hw⟩ := exists_eq_pow_smul p h
    rw [pow_one, smul_eq_mul] at hw
    exact (PadicInt.p_nonunit (p := p)) (IsUnit.of_mul_eq_one w hw.symm)
  have hinj : Function.Injective fun e : ℕ ↦ p ^ (e + 1) := by
    intro a b hab
    have := Nat.pow_right_injective hp.two_le hab
    omega
  have hle := Finset.le_sup (f := id) (hsupp (f.support.sup id))
  have h1 : f.support.sup id < p ^ (f.support.sup id) := Nat.lt_pow_self hp.one_lt
  have h2 : p ^ (f.support.sup id) ≤ p ^ (f.support.sup id + 1) :=
    Nat.pow_le_pow_right hp.pos (Nat.le_succ _)
  simp only [id_eq] at hle
  omega

/-- The class of `η` is divisible by `p^t` for every `t`: the difference between `η` and its
`t`-th partial sum lies in `p^t Ω¹_D`, and that partial sum is the differential of
`∑_{0 < e ≤ t} x^{p^e}`. -/
public theorem mk_eta_mem_pow_smul (t : ℕ) :
    mkCohomologyOne p (eta p) ∈
      (baseIdeal p ^ t • (⊤ : Submodule ℤ_[p] (cohomologyOne p))) := by
  have hsub : eta p - AdicCompletion.of (baseIdeal p) (monomials p) (etaPartial p t)
      ∈ (baseIdeal p ^ t • (⊤ : Submodule ℤ_[p] (completedMonomials p))) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _),
      LinearMap.mem_ker, map_sub, sub_eq_zero]
    simp only [AdicCompletion.eval_apply, AdicCompletion.of_apply, Submodule.mkQ_apply,
      eta_val p]
  have heq : mkCohomologyOne p (eta p)
      = mkCohomologyOne p
        (eta p - AdicCompletion.of (baseIdeal p) (monomials p) (etaPartial p t)) := by
    rw [map_sub, eq_comm, sub_eq_self, mkCohomologyOne_eq_zero_iff]
    exact ⟨AdicCompletion.of (baseIdeal p) (monomials p) (etaPoly p t), by
      rw [completedDifferential_of, differential_etaPoly]⟩
  rw [heq]
  exact mkQ_mem_pow_smul p _ hsub

/-- **Conclusion (4) of [Stacks, Tag 07LK] for the displayed complex.**  The cokernel of
`diag(0, 1, 2, 3, …)` is not separated for the `p`-adic topology: the class of the source's
`η = ∑_{e > 0} p^e x^{p^e - 1} dx` is nonzero and divisible by every power of `p`. -/
public theorem not_isHausdorff_cohomologyOne :
    ¬ IsHausdorff (baseIdeal p) (cohomologyOne p) := by
  intro hhaus
  have hzero : mkCohomologyOne p (eta p) = 0 :=
    hhaus.haus _ fun t ↦ SModEq.zero.mpr (mk_eta_mem_pow_smul p t)
  rw [mkCohomologyOne_eq_zero_iff] at hzero
  exact eta_notMem_range p hzero

end AffineLineDeRham

end Crystalline

end
