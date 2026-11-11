module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Lattice.Defs
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# The order of vanishing of a norm

All rings are commutative with unit. The data is a ring map `A → B` in which `A` is a Noetherian
local domain of Krull dimension `1` and `A ⊆ B` is a finite extension of domains, so `A → B` is
injective, `B` is an integral domain, and `B` is finite as an `A`-module. Write `K = Frac A` and
`L = Frac B` for the fraction fields, so that `L/K` is a finite field extension.

The main result: for `y ∈ L*` with `x = Nm_{L/K}(y) ∈ K*`, and `m₁, …, m_n` the maximal ideals of
the semi-local ring `B`,

`ord_A(x) = ∑_{i=1}^{n} [κ(mᵢ) : κ(m_A)] · ord_{B_{mᵢ}}(y)`.
-/

@[expose] public section


open Ring

/-! ## The order of vanishing (Stacks 02MD)

Let `R` be a Noetherian local domain of dimension `1` with fraction field `K`. The order of
vanishing `ord_R : K* → ℤ` is the group homomorphism taking a nonzero `r ∈ R` to
`length_R (R / (r))`, extended to `K*` by `ord_R(x/y) = ord_R(x) - ord_R(y)`.

In Mathlib this is `Ring.ordFrac R : K →*₀ WithZero (Multiplicative ℤ)`, a monoid-with-zero
homomorphism sending `0` to `0`. For nonzero `x ∈ K*` the value `Ring.ordFrac R x` is a nonzero
element of `WithZero (Multiplicative ℤ)`, and the integer `ord_R(x)` is recovered by
`Multiplicative.toAdd (WithZero.unzero ...)`. The definition below packages that extraction into
an integer-valued order function.
-/

/-! ### Correctness of `ordInt`

The two statements below characterize `ordInt` as the order of vanishing: it is a group
homomorphism `K* → ℤ`, and on a nonzero `r ∈ R` it equals `length_R (R / (r))`, a length that
is finite under the standing hypotheses.
-/

/-- `ordInt` is additive on `K^*`, i.e. it is a group homomorphism to `Z`. -/
theorem ordInt_mul (R : Type*) [CommRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] [Nontrivial R]
    (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    ordInt R (x * y) (mul_ne_zero hx hy) = ordInt R x hx + ordInt R y hy := by
  unfold ordInt
  rw [← toAdd_mul]
  congr 1
  rw [← WithZero.coe_inj]
  rw [WithZero.coe_mul]
  rw [WithZero.coe_unzero, WithZero.coe_unzero, WithZero.coe_unzero]
  exact map_mul (Ring.ordFrac R) x y

/-- On a nonzero `r : R`, the order of vanishing equals the length `length_R (R / (r))`.
Here `Module.length` is valued in `ℕ∞`; under the dimension-`1` Noetherian hypotheses this
length is finite, and `.toNat` recovers the integer.

No locality is required: the proof below does not use `[IsLocalRing R]`. Requiring it would
exclude real cases — `A / 𝔮` is *not* local for a height-one prime of a two-dimensional ring,
so a consumer working with a height-one prime of a surface could not apply this lemma. -/
theorem ordInt_algebraMap (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (r : R) (hr : r ≠ 0) (hr' : algebraMap R K r ≠ 0) :
    ordInt R (algebraMap R K r) hr' =
      ((Module.length R (R ⧸ Ideal.span {r})).toNat : ℤ) := by
  have helper : ∀ {w : WithZero (Multiplicative ℤ)} (h : w ≠ 0) (k : ℤ),
      w = ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
      Multiplicative.toAdd (WithZero.unzero h) = k := by
    intro w h k hw
    have : WithZero.unzero h = (Multiplicative.ofAdd k : Multiplicative ℤ) := by
      rw [← WithZero.coe_inj, WithZero.coe_unzero, hw]
    rw [this]; simp
  set n := (Module.length R (R ⧸ Ideal.span {r})).toNat with hn
  unfold ordInt
  apply helper
  rw [Ring.ordFrac_eq_ord R (x := r) hr]
  have hr0 : r ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hr
  have hord : Ring.ord R r = Module.length R (R ⧸ Ideal.span {r}) := rfl
  -- key: evaluate the monoid hom on a nonzero divisor with a known finite order.
  have hval : ∀ m : ℕ, Ring.ord R r = (m : ℕ∞) →
      Ring.ordMonoidWithZeroHom R r
        = ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro m hm
    simp only [Ring.ordMonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, hr0, ite_true,
        hm]
    rfl
  have hne : Ring.ord R r ≠ ⊤ := by
    intro htop
    have h0 : Ring.ordMonoidWithZeroHom R r = 0 := by
      simp only [Ring.ordMonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, hr0, ite_true,
        htop]
      rfl
    have hu : Ring.ordFrac R (K := K) (algebraMap R K r) ≠ 0 :=
      (hr'.isUnit.map (Ring.ordFrac R)).ne_zero
    rw [Ring.ordFrac_eq_ord R (x := r) hr, h0] at hu
    exact hu rfl
  have hcoe : Ring.ord R r = (n : ℕ∞) := by
    rw [hn, hord]; rw [hord] at hne; exact (ENat.natCast_toNat (by rw [← hord]; exact hne)).symm
  exact hval n hcoe

/-! ### Norms, the local rings of `B`, and residue degrees

For the finite field extension `L/K` and `y ∈ L`, the norm `Nm_{L/K}(y) = det_K(mul_y)` is the
determinant of multiplication by `y` on the `K`-vector space `L`, which is `Algebra.norm K`.

Under the standing hypotheses `B` is semi-local, with finitely many maximal ideals, indexed here
by the finite type `MaximalSpectrum B`. For each `v`, the localization
`B_v = Localization.AtPrime v.asIdeal` is a Noetherian local domain of dimension `1` with
fraction field `L`, so `ord_{B_v}` is defined as above with `R = B_v` and `K = L`.

Let `m_A` be the maximal ideal of `A`. Each maximal ideal `mᵢ` of `B` lies over `m_A`, and the
residue degree `[κ(mᵢ) : κ(m_A)] = finrank_{A/m_A} (B/mᵢ)` is finite; it is
`Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) mᵢ`, which equals
`Module.finrank (A / m_A) (B / mᵢ)` when `mᵢ` lies over `m_A`.
-/

/-! ### The norm-length identity (Stacks 02MI)

For a nonzero `b : B`, the order of vanishing of its norm equals the `A`-length of the cyclic
quotient `B / bB`:

`ord_A (Nm_{L/K}(b)) = length_A (B / bB)`.

Let `μ_b : L → L` be multiplication by `y = algebraMap B L b`, a `K`-linear endomorphism of the
finite `K`-vector space `L`, so that `Nm_{L/K}(y) = det_K(μ_b)` by definition. Since `b` is a
nonzerodivisor of `B`, multiplication by `b` is an injective map `B → B` with cokernel `B/bB` of
finite `A`-length: `B/bB` is a finite `A`-module supported only at `m_A`, being killed by some
power of `m_A` because `dim A = 1` and `b ≠ 0`. The determinant `det_K(μ_b)` is, up to a unit, the
`A`-norm of `b`, an element of `A`, and `ord_A` of it is the length of `A / (Nm b)`.

Concretely, one pushes `Nm_{L/K}(y)` into `A`, as `algebraMap A K (Algebra.norm A b)` via
`Algebra.norm_localization`, applies `ordInt_algebraMap` to turn `ord_A` into
`length_A (A / (Nm b))`, and finally invokes the length identity
`length_A (A / (Nm b)·A) = length_A (B / bB)`.

The route through `Algebra.norm_localization` or `relNorm` is not available here: it needs
`[Module.Free A B]`, respectively `[IsIntegrallyClosed A]`, and `A` is only a one-dimensional
Noetherian local domain while `B` is finite and torsion-free but not free. An additivity-only
strategy is also genuinely insufficient: the discrepancy `D = length − ord ∘ Nm` is an additive
homomorphism vanishing on `A`, which does not force `D ≡ 0`. The decisive content is Stacks
02QH: for a finite `A`-module `M` and an `A`-linear endomorphism `φ` with `det_K(φ ⊗ K) ≠ 0`,
`ord_A(det_K(φ ⊗ K)) = length_A(coker φ)`. It is applied with `M = B` and `φ = lmul_A b`.

The identity is therefore assembled from `ordInt_baseChangeDet_eq_length_cokernel`, the 02QH
determinant-length kernel, and `baseChangeDet_lmul_eq_norm`, identifying the determinant of
`lmul_A b ⊗ K` with `Nm_{L/K}(b)` through the `K`-algebra isomorphism `B ⊗[A] K ≅ L`, together
with the inline identification `range (lmul_A b) = span {b}` making the cokernel `B/bB`.
-/

/-! ### Background on the matrix base case

For a square matrix `T` over a one-dimensional Noetherian local domain `A` with `det T ≠ 0`, the
`A`-length of the cokernel `Aᵐ ⧸ T·Aᵐ` equals `ord_A(det T) = length_A(A/(det T))`.

An additivity-only strategy cannot reach this. The two functions `L(T) = length_A(Aᵐ/T·Aᵐ)` and
`Δ(T) = ord_A(det T)` are both additive under matrix multiplication and agree on scalar matrices
`cI` and on `GLₘ(A)`, but that yields only the single relation `δ(T) + δ(adj T) = 0` for
`δ = L − Δ`, which does not force `δ ≡ 0`; and triangularizing to a pivot would require a
principal ideal domain, which `A` is not. The correct route is a filtration and dévissage
argument, or base change to the completion `Â`, where `ℓ_A(N) = ℓ_Â(N̂)` for finite-length `N`.

The reusable building blocks are: additivity of length along short exact sequences; the
isomorphism `Aᵐ/aAᵐ ≅ (A/aA)ᵐ`, giving `L(aI) = m·ord_A(a)`; multiplicativity
`L(T₁T₂) = L(T₁) + L(T₂)` via `0 → T₁Aᵐ/T₁T₂Aᵐ → Aᵐ/T₁T₂Aᵐ → Aᵐ/T₁Aᵐ → 0` together with the
isomorphism `Aᵐ/T₂Aᵐ ≅ T₁Aᵐ/T₁T₂Aᵐ` for injective `T₁`; and the chain
`(det T)Aᵐ ⊆ TAᵐ ⊆ Aᵐ` with `Matrix.adjugate_mul` and `Matrix.det_adjugate`, giving
`L(T) + L(adj T) = m·ord_A(det T)`.
-/

/-! ### Multiplicativity of the cokernel length under matrix product

For square matrices `T₁ T₂` over a one-dimensional Noetherian local domain `A`, with both
determinants nonzero, so that both `toLin'` are injective over the domain `A`,
`length_A(Aᵐ/range(toLin'(T₁*T₂)))`
`= length_A(Aᵐ/range(toLin' T₁)) + length_A(Aᵐ/range(toLin' T₂))`.
The route: `Matrix.toLin'_mul` turns `toLin'(T₁*T₂)` into the
composition `toLin' T₁ ∘ₗ toLin' T₂`; the nested-submodule SES
`0 → range φ ⧸ range(φ∘ψ) → Aᵐ ⧸ range(φ∘ψ) → Aᵐ ⧸ range φ → 0` (`Module.length_eq_add_of_exact`)
plus the iso `range φ ⧸ range(φ∘ψ) ≅ Aᵐ ⧸ range ψ` (from `LinearEquiv.ofInjective φ` and
`Submodule.Quotient.equiv`) give the additivity.
-/

open Submodule LinearMap in
/-- The abstract multiplicativity behind `matrix_cokerLen_mul`, for an arbitrary injective `φ`
and any `ψ` on a module `M`.

It comes from the short exact sequence
`0 → M ⧸ range ψ →[f] M ⧸ range (φ∘ψ) →[g] M ⧸ range φ → 0`, where `f : [x] ↦ [φ x]` is injective
because `φ` is injective and `comap φ (map φ (range ψ)) = range ψ`, and `g` is the natural
projection, surjective with `ker g = map (range (φ∘ψ)).mkQ (range φ) = range f`. -/
private theorem matrix_cokerLen_mul_helper (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (φ ψ : M →ₗ[R] M) (hφ : Function.Injective φ) :
    Module.length R (M ⧸ LinearMap.range (φ ∘ₗ ψ))
      = Module.length R (M ⧸ LinearMap.range ψ) + Module.length R (M ⧸ LinearMap.range φ) := by
  set S := LinearMap.range (φ ∘ₗ ψ) with hS
  set T := LinearMap.range φ with hT
  have hSmap : S = Submodule.map φ (LinearMap.range ψ) := by
    rw [hS, LinearMap.range_comp]
  have hST : S ≤ T := LinearMap.range_comp_le_range ψ φ
  have hf : LinearMap.range ψ ≤ Submodule.comap φ S := by
    rw [hSmap]
    exact fun _ hx => Submodule.mem_map_of_mem hx
  let f : (M ⧸ LinearMap.range ψ) →ₗ[R] (M ⧸ S) := Submodule.mapQ (LinearMap.range ψ) S φ hf
  have hg : S ≤ Submodule.comap LinearMap.id T := by
    rw [Submodule.comap_id]; exact hST
  let g : (M ⧸ S) →ₗ[R] (M ⧸ T) := Submodule.mapQ S T LinearMap.id hg
  have hcomap : Submodule.comap φ S = LinearMap.range ψ := by
    rw [hSmap, Submodule.comap_map_eq_of_injective hφ]
  have hfrange : f.range = Submodule.map S.mkQ T := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range ψ) z
      refine ⟨φ x, ?_, ?_⟩
      · rw [hT]; exact LinearMap.mem_range_self φ x
      · simp only [f, Submodule.mkQ_apply, Submodule.mapQ_apply]
    · rintro _ ⟨y, hy, rfl⟩
      rw [hT] at hy
      obtain ⟨x, rfl⟩ := hy
      refine ⟨Submodule.mkQ _ x, ?_⟩
      simp only [f, Submodule.mkQ_apply, Submodule.mapQ_apply]
  apply Module.length_eq_add_of_exact f g
  · rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, hcomap, Submodule.mkQ_map_self]
  · exact (Submodule.mkQ_surjective T).forall.2 fun x => ⟨Submodule.mkQ S x, rfl⟩
  · rw [LinearMap.exact_iff, Submodule.ker_mapQ, Submodule.comap_id, hfrange]

/-- Multiplicativity of the cokernel length: for square matrices over a one-dimensional
Noetherian local domain, with the first determinant nonzero, the cokernel length of a product
is the sum of the cokernel lengths. -/
theorem matrix_cokerLen_mul
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (m : ℕ) (T₁ T₂ : Matrix (Fin m) (Fin m) A) (h₁ : T₁.det ≠ 0) :
    Module.length A ((Fin m → A) ⧸ LinearMap.range (Matrix.toLin' (T₁ * T₂)))
      = Module.length A ((Fin m → A) ⧸ LinearMap.range (Matrix.toLin' T₁))
        + Module.length A ((Fin m → A) ⧸ LinearMap.range (Matrix.toLin' T₂)) := by
  have hinj : Function.Injective (Matrix.toLin' T₁) :=
    (injective_iff_map_eq_zero _).2 fun x hx =>
      Matrix.eq_zero_of_mulVec_eq_zero h₁ (by rwa [Matrix.toLin'_apply] at hx)
  rw [Matrix.toLin'_mul, matrix_cokerLen_mul_helper A (Fin m → A) _ _ hinj, add_comm]

/-- SCALAR BASE CASE of the matrix base case.  For `a : A` (with `a ≠ 0`) the cokernel of the
scalar matrix `a • 1 : Matrix (Fin m) (Fin m) A` has `A`-length `m · length_A(A ⧸ span{a})`.
The map `Matrix.toLin' (a • 1)` is the diagonal map `x ↦ a • x` on `Fin m → A`, so the cokernel
is `(Fin m → A) ⧸ (a • ⊤) ≅ ∏ (A ⧸ span{a})`, whence `Module.length_pi`. -/
@[ega "IV 21.10.13" "special case"]
theorem matrix_cokerLen_scalar
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (m : ℕ) (a : A) :
    Module.length A ((Fin m → A) ⧸ LinearMap.range (Matrix.toLin' (a • (1 : Matrix (Fin m) (Fin m)
        A))))
      = m * Module.length A (A ⧸ Ideal.span {a}) := by
  -- Submodule.quotientPi + Module.length_pi; even true without `a ≠ 0`).
  have hrange :
      LinearMap.range (Matrix.toLin' (a • (1 : Matrix (Fin m) (Fin m) A)))
        = Submodule.pi Set.univ (fun _ : Fin m => Ideal.span {a}) := by
    have hmul : ∀ x : Fin m → A,
        Matrix.toLin' (a • (1 : Matrix (Fin m) (Fin m) A)) x = a • x := by
      intro x; ext i; simp
    ext x
    simp only [LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, forall_true_left,
      Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, rfl⟩ i
      rw [hmul]
      exact ⟨y i, by simp⟩
    · intro h
      choose c hc using h
      refine ⟨c, ?_⟩
      rw [hmul]
      ext i
      simp [hc i]
  rw [hrange, (Submodule.quotientPi (fun _ : Fin m => Ideal.span {a})).length_eq, Module.length_pi,
    ENat.card_eq_coe_fintype_card]
  simp

/-! ### The dévissage step

This is the conceptual crux of the matrix base case, for a block-triangular or, more generally,
`N`-preserving endomorphism.

For an `A`-linear endomorphism `φ` of `M` that maps a submodule `N` into itself (`hφN`), inducing
`φ̄ := N.mapQ N φ hφN` on the quotient `M ⧸ N`, IF `φ̄` is injective then the cokernel length is
additive along the flag `N ⊆ M`:
  `length(M ⧸ range φ) = length(N ⧸ range(φ|_N)) + length((M ⧸ N) ⧸ range φ̄)`.

This comes from the snake lemma applied to `0 → N → M → M ⧸ N → 0` with the `φ`-action: the
boundary map `ker φ̄ → coker(φ|_N)` vanishes because `φ̄` is injective (`ker φ̄ = 0`), leaving the
genuine short exact sequence of cokernels
  `0 → N ⧸ range(φ|_N) → M ⧸ range φ → (M ⧸ N) ⧸ range φ̄ → 0`,
whose additivity (`Module.length_eq_add_of_exact`, in `ℕ∞`, unconditional) gives the identity.
THIS is the piece that defeats the "additivity-only is insufficient" obstruction (it splits the
cokernel along a flag, not merely under a product).  No domain/local/finite-length hypothesis is
needed (the identity holds over any `CommRing`, in `ℕ∞`).
-/

open Submodule LinearMap in
/-- Dévissage for cokernel lengths along an invariant submodule: for `φ` preserving `N` with
injective induced map on `M ⧸ N`, the cokernel length of `φ` splits as the sum of the cokernel
lengths of `φ|_N` and of the induced map. -/
theorem matrix_cokerLen_devissage
    (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M]
    (N : Submodule A M) (φ : M →ₗ[A] M) (hφN : N ≤ Submodule.comap φ N)
    (hbar_inj : Function.Injective (N.mapQ N φ hφN)) :
    Module.length A (M ⧸ LinearMap.range φ)
      = Module.length A (N ⧸ LinearMap.range (φ.restrict hφN))
        + Module.length A ((M ⧸ N) ⧸ LinearMap.range (N.mapQ N φ hφN)) := by
  -- hypotheses; the SES of cokernels 0→coker(φ|N)→coker φ→coker φ̄→0 via
  -- Module.length_eq_add_of_exact).
  set φbar := N.mapQ N φ hφN with hφbar
  set φN := φ.restrict hφN with hφN'
  -- f : N ⧸ range φN → M ⧸ range φ induced by N.subtype
  have hf : LinearMap.range φN ≤ Submodule.comap N.subtype (LinearMap.range φ) := by
    rintro _ ⟨z, rfl⟩
    rw [Submodule.mem_comap]
    refine ⟨(z : M), ?_⟩
    simp [hφN', LinearMap.coe_restrict_apply]
  let f : (N ⧸ LinearMap.range φN) →ₗ[A] (M ⧸ LinearMap.range φ) :=
    Submodule.mapQ (LinearMap.range φN) (LinearMap.range φ) N.subtype hf
  -- g : M ⧸ range φ → (M ⧸ N) ⧸ range φbar induced by N.mkQ
  have hg : LinearMap.range φ ≤ Submodule.comap N.mkQ (LinearMap.range φbar) := by
    rintro _ ⟨m, rfl⟩
    rw [Submodule.mem_comap]
    refine ⟨N.mkQ m, ?_⟩
    rw [hφbar, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.mkQ_apply]
  let g : (M ⧸ LinearMap.range φ) →ₗ[A] ((M ⧸ N) ⧸ LinearMap.range φbar) :=
    Submodule.mapQ (LinearMap.range φ) (LinearMap.range φbar) N.mkQ hg
  apply Module.length_eq_add_of_exact f g
  · -- f injective
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range φN) z
    rw [LinearMap.mem_ker] at hz
    simp only [f, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.subtype_apply] at hz
    rw [Submodule.Quotient.mk_eq_zero] at hz
    obtain ⟨m, hm⟩ := hz
    -- φ m = ↑x, so φbar [m] = [↑x] = 0, hence [m] = 0, m ∈ N
    have hbar0 : φbar (N.mkQ m) = 0 := by
      rw [hφbar, Submodule.mkQ_apply, Submodule.mapQ_apply,
        Submodule.Quotient.mk_eq_zero, hm]
      exact x.property
    have hmN : N.mkQ m = 0 := hbar_inj (by rw [hbar0, map_zero])
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmN
    -- x = φN ⟨m, hmN⟩ ∈ range φN
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨⟨m, hmN⟩, ?_⟩
    apply Subtype.ext
    rwa [hφN', LinearMap.coe_restrict_apply]
  · -- g surjective
    intro w
    obtain ⟨q, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range φbar) w
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective N q
    refine ⟨(LinearMap.range φ).mkQ m, ?_⟩
    simp only [g, Submodule.mkQ_apply, Submodule.mapQ_apply]
  · -- Function.Exact f g
    rw [LinearMap.exact_iff]
    apply le_antisymm
    · -- ker g ≤ range f
      intro z hz
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range φ) z
      rw [LinearMap.mem_ker] at hz
      simp only [g, Submodule.mkQ_apply, Submodule.mapQ_apply] at hz
      rw [Submodule.Quotient.mk_eq_zero] at hz
      obtain ⟨q, hq⟩ := hz
      obtain ⟨m', rfl⟩ := Submodule.mkQ_surjective N q
      rw [hφbar, Submodule.mkQ_apply, Submodule.mapQ_apply] at hq
      -- hq : Quotient.mk (φ m') = Quotient.mk m, so m - φ m' ∈ N
      have hmem : m - φ m' ∈ N := (Submodule.Quotient.eq N).mp hq.symm
      -- m - φ m' ∈ N, call it x
      set x : M := m - φ m' with hx
      refine ⟨(LinearMap.range φN).mkQ ⟨x, hmem⟩, ?_⟩
      simp only [f, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.subtype_apply]
      rw [Submodule.Quotient.eq]
      refine ⟨-m', ?_⟩
      rw [hx]
      simp
    · -- range f ≤ ker g
      rintro _ ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range φN) z
      rw [LinearMap.mem_ker]
      simp only [f, g, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.subtype_apply]
      rw [Submodule.Quotient.mk_eq_zero]
      -- the element (↑x : M) is in N, hence its class in M ⧸ N is 0, so it lies in range φbar
      have : (Submodule.Quotient.mk (x : M) : M ⧸ N) = 0 :=
        (Submodule.Quotient.mk_eq_zero N).mpr x.property
      rw [this]
      exact zero_mem _

/-! ### Additivity of `length (A ⧸ span{·})` under multiplication

This is the span side of the determinant
relation).  Over a domain `A`, for nonzero `a b`, the SES
`0 → A/span{b} →(·a) A/span{a*b} → A/span{a} → 0` (`Module.length_eq_add_of_exact`) gives
`length (A/span{a*b}) = length (A/span{b}) + length (A/span{a})`.
-/
open Submodule LinearMap in
/-- Over a domain, for `a ≠ 0`, `length (A ⧸ span {a * b})` is the sum of
`length (A ⧸ span {b})` and `length (A ⧸ span {a})`. -/
@[sga "7 X 2.14" "partial"]
theorem length_span_mul
    (A : Type*) [CommRing A] [IsDomain A]
    (a b : A) (ha : a ≠ 0) :
    Module.length A (A ⧸ Ideal.span {a * b})
      = Module.length A (A ⧸ Ideal.span {b}) + Module.length A (A ⧸ Ideal.span {a}) := by
  set μ : A →ₗ[A] A := LinearMap.toSpanSingleton A A a with hμ
  have hμapp : ∀ x : A, μ x = a * x := by intro x; rw [hμ]; simp [mul_comm]
  have hf : (Ideal.span {b}).restrictScalars A ≤
      Submodule.comap μ ((Ideal.span {a*b}).restrictScalars A) := by
    intro x hx
    simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton] at hx ⊢
    rw [Submodule.mem_comap, Submodule.restrictScalars_mem, Ideal.mem_span_singleton, hμapp]
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c, by ring⟩
  let f : (A ⧸ (Ideal.span {b}).restrictScalars A) →ₗ[A]
      (A ⧸ (Ideal.span {a*b}).restrictScalars A) :=
    Submodule.mapQ _ _ μ hf
  have hg : (Ideal.span {a*b}).restrictScalars A ≤
      Submodule.comap LinearMap.id ((Ideal.span {a}).restrictScalars A) := by
    rw [Submodule.comap_id]
    intro x hx
    simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton] at hx ⊢
    obtain ⟨c, rfl⟩ := hx
    exact ⟨b * c, by ring⟩
  let g : (A ⧸ (Ideal.span {a*b}).restrictScalars A) →ₗ[A]
      (A ⧸ (Ideal.span {a}).restrictScalars A) :=
    Submodule.mapQ _ _ LinearMap.id hg
  have hlen : Module.length A (A ⧸ (Ideal.span {a*b}).restrictScalars A)
      = Module.length A (A ⧸ (Ideal.span {b}).restrictScalars A)
        + Module.length A (A ⧸ (Ideal.span {a}).restrictScalars A) := by
    apply Module.length_eq_add_of_exact f g
    · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro z hz
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
      rw [LinearMap.mem_ker] at hz
      simp only [f, Submodule.mkQ_apply, Submodule.mapQ_apply] at hz
      rw [Submodule.Quotient.mk_eq_zero] at hz
      simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton] at hz
      rw [hμapp] at hz
      obtain ⟨c, hc⟩ := hz
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
      refine ⟨c, ?_⟩
      have : a * x = a * (b * c) := by rw [hc]; ring
      exact mul_left_cancel₀ ha this
    · intro w
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ w
      exact ⟨Submodule.mkQ _ x, rfl⟩
    · rw [LinearMap.exact_iff]
      apply le_antisymm
      · intro z hz
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
        rw [LinearMap.mem_ker] at hz
        simp only [g, Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.id_coe, id_eq] at hz
        rw [Submodule.Quotient.mk_eq_zero] at hz
        simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton] at hz
        obtain ⟨c, rfl⟩ := hz
        refine ⟨Submodule.mkQ _ c, ?_⟩
        simp only [f, Submodule.mkQ_apply, Submodule.mapQ_apply]
        rw [hμapp]
      · rintro _ ⟨z, rfl⟩
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
        rw [LinearMap.mem_ker]
        simp only [f, g, Submodule.mkQ_apply, Submodule.mapQ_apply, LinearMap.id_coe, id_eq]
        rw [Submodule.Quotient.mk_eq_zero]
        simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
        rw [hμapp]
        exact ⟨x, by ring⟩
  exact hlen

/-- Cokernel length is invariant under conjugation by linear equivalences. -/
theorem cokerLen_conj_eq (A : Type*) [CommRing A] {M P : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup P] [Module A P]
    (φ : M →ₗ[A] M) (f : P ≃ₗ[A] M) (g : M ≃ₗ[A] P) :
    Module.length A (P ⧸ LinearMap.range ((g : M →ₗ[A] P) ∘ₗ φ ∘ₗ (f : P →ₗ[A] M)))
      = Module.length A (M ⧸ LinearMap.range φ) := by
  have hrange : LinearMap.range ((g : M →ₗ[A] P) ∘ₗ φ ∘ₗ (f : P →ₗ[A] M))
      = Submodule.map (g : M →ₗ[A] P) (LinearMap.range φ) := by
    rw [LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  rw [hrange]
  exact ((Submodule.Quotient.equiv (LinearMap.range φ) _ g rfl).length_eq).symm

/-- If a linear equivalence `α` intertwines `ψ` and `χ`, their cokernels have equal length. -/
theorem cokerLen_intertwine (A : Type*) [CommRing A] {X Y : Type*}
    [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (ψ : X →ₗ[A] X) (χ : Y →ₗ[A] Y) (α : X ≃ₗ[A] Y)
    (h : (α : X →ₗ[A] Y) ∘ₗ ψ = (χ : Y →ₗ[A] Y) ∘ₗ (α : X →ₗ[A] Y)) :
    Module.length A (X ⧸ LinearMap.range ψ) = Module.length A (Y ⧸ LinearMap.range χ) := by
  have hχ : χ = (α : X →ₗ[A] Y) ∘ₗ ψ ∘ₗ (α.symm : Y →ₗ[A] X) := by
    apply LinearMap.ext; intro y
    have := LinearMap.congr_fun h (α.symm y)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this ⊢
    rw [← this]
  rw [hχ]
  exact (cokerLen_conj_eq A ψ α.symm α).symm

/-- Cokernel length under reindexing of a square matrix is unchanged. -/
theorem cokerLen_reindex (A : Type*) [CommRing A] {k l : Type*}
    [Fintype k] [DecidableEq k] [Fintype l] [DecidableEq l]
    (e : k ≃ l) (T : Matrix k k A) :
    Module.length A ((l → A) ⧸ LinearMap.range (Matrix.toLin' (Matrix.reindex e e T)))
      = Module.length A ((k → A) ⧸ LinearMap.range (Matrix.toLin' T)) := by
  rw [Matrix.toLin'_reindex]
  exact cokerLen_conj_eq A (Matrix.toLin' T)
    (LinearEquiv.funCongrLeft A A e) (LinearEquiv.funCongrLeft A A e.symm)

/-- Cokernel of an invertible matrix (unit determinant) is trivial. -/
theorem cokerLen_isUnit (A : Type*) [CommRing A] {m : Type*} [Fintype m] [DecidableEq m]
    (T : Matrix m m A) (hT : IsUnit T.det) :
    Module.length A ((m → A) ⧸ LinearMap.range (Matrix.toLin' T)) = 0 := by
  apply Module.length_eq_zero_iff.mpr
  have hsurj : Function.Surjective (Matrix.toLin' T) := by
    intro y
    refine ⟨T⁻¹.mulVec y, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv T hT, Matrix.one_mulVec]
  rw [← LinearMap.range_eq_top] at hsurj
  rw [hsurj, Submodule.Quotient.subsingleton_iff]

/-- `length (A ⧸ span {a}) = 0` when `a` is a unit. -/
theorem spanLen_isUnit (A : Type*) [CommRing A] (a : A) (ha : IsUnit a) :
    Module.length A (A ⧸ Ideal.span {a}) = 0 := by
  apply Module.length_eq_zero_iff.mpr
  rw [Submodule.Quotient.subsingleton_iff, Ideal.span_singleton_eq_top.mpr ha]

open Matrix in
/-- For a block-upper-triangular matrix `fromBlocks C D 0 S` with `det C ≠ 0` and `det S ≠ 0`,
the cokernel length splits as `cokerLen C + cokerLen S`. -/
theorem block_cokerLen (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (C : Matrix ι ι A) (D : Matrix ι κ A) (S : Matrix κ κ A)
    (hSdet : S.det ≠ 0) :
    Module.length A (((ι ⊕ κ) → A) ⧸ LinearMap.range (Matrix.toLin' (Matrix.fromBlocks C D 0 S)))
      = Module.length A ((ι → A) ⧸ LinearMap.range (Matrix.toLin' C))
        + Module.length A ((κ → A) ⧸ LinearMap.range (Matrix.toLin' S)) := by
  set B := Matrix.fromBlocks C D 0 S with hB
  set φ : ((ι ⊕ κ) → A) →ₗ[A] ((ι ⊕ κ) → A) := Matrix.toLin' B with hφ
  set pr : ((ι ⊕ κ) → A) →ₗ[A] (κ → A) := LinearMap.funLeft A A Sum.inr with hpr
  set N : Submodule A ((ι ⊕ κ) → A) := LinearMap.ker pr with hN
  have hφapp : ∀ (g : (ι ⊕ κ) → A),
      φ g = Sum.elim (C.mulVec (g ∘ Sum.inl) + D.mulVec (g ∘ Sum.inr))
        (S.mulVec (g ∘ Sum.inr)) := by
    intro g
    rw [hφ, Matrix.toLin'_apply, hB, Matrix.fromBlocks_mulVec]
    simp [Matrix.zero_mulVec]
  have hmemN : ∀ g, g ∈ N ↔ g ∘ Sum.inr = 0 := by
    intro g; rw [hN, LinearMap.mem_ker, hpr]; rfl
  have hφinr : ∀ g, (φ g) ∘ Sum.inr = S.mulVec (g ∘ Sum.inr) := by
    intro g; rw [hφapp]; rfl
  have hφinl : ∀ g, (φ g) ∘ Sum.inl = C.mulVec (g ∘ Sum.inl) + D.mulVec (g ∘ Sum.inr) := by
    intro g; rw [hφapp]; rfl
  have hSinj : Function.Injective (Matrix.toLin' S) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hx
    exact Matrix.eq_zero_of_mulVec_eq_zero hSdet hx
  have hφN : N ≤ Submodule.comap φ N := by
    intro g hg
    rw [Submodule.mem_comap, hmemN]
    rw [hmemN] at hg
    rw [hφinr, hg, Matrix.mulVec_zero]
  have hbar_inj : Function.Injective (N.mapQ N φ hφN) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective N z
    rw [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.mapQ_apply,
      Submodule.Quotient.mk_eq_zero] at hz
    rw [hmemN, hφinr] at hz
    have hgr : g ∘ Sum.inr = 0 := hSinj (by
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hz, Matrix.mulVec_zero])
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hmemN]
    exact hgr
  rw [matrix_cokerLen_devissage A _ N φ hφN hbar_inj]
  -- Identify the two pieces.
  -- Quotient piece: (M/N) ⧸ range φ̄  ≅  cokerLen S
  have hprsurj : Function.Surjective pr :=
    LinearMap.funLeft_surjective_of_injective A A Sum.inr Sum.inr_injective
  let β : (((ι ⊕ κ) → A) ⧸ N) ≃ₗ[A] (κ → A) :=
    LinearMap.quotKerEquivOfSurjective pr hprsurj
  have hβ : ∀ g, β (Submodule.Quotient.mk g) = g ∘ Sum.inr := fun g => rfl
  have hpieceS : Module.length A ((((ι ⊕ κ) → A) ⧸ N) ⧸ LinearMap.range (N.mapQ N φ hφN))
      = Module.length A ((κ → A) ⧸ LinearMap.range (Matrix.toLin' S)) := by
    refine cokerLen_intertwine A (N.mapQ N φ hφN) (Matrix.toLin' S) β (LinearMap.ext fun z => ?_)
    obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective N z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, hβ, hβ, Matrix.toLin'_apply]
    exact hφinr g
  -- Sub piece: N ⧸ range (φ.restrict) ≅ cokerLen C
  let fwd : N →ₗ[A] (ι → A) := (LinearMap.funLeft A A Sum.inl).comp N.subtype
  let bwd : (ι → A) →ₗ[A] N :=
    { toFun := fun h => ⟨Sum.elim h 0, by rw [hmemN]; ext j; simp⟩
      map_add' := by intro x y; apply Subtype.ext; ext i; cases i <;> simp [Sum.elim]
      map_smul' := by intro c x; apply Subtype.ext; ext i; cases i <;> simp [Sum.elim] }
  let γ : N ≃ₗ[A] (ι → A) := LinearEquiv.ofLinearMap fwd bwd
    (LinearMap.ext fun _ => rfl)
    (by
      apply LinearMap.ext; intro g; apply Subtype.ext; apply funext; intro i
      cases i with
      | inl a => rfl
      | inr b =>
        simp only [fwd, bwd, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.coe_mk,
          AddHom.coe_mk, LinearMap.id_coe, id_eq, Sum.elim_inr, Pi.zero_apply]
        exact (congrFun ((hmemN g.val).mp g.property) b).symm)
  have hγ : ∀ (g : N), γ g = (g : (ι ⊕ κ) → A) ∘ Sum.inl := fun g => rfl
  have hpieceC : Module.length A (N ⧸ LinearMap.range (φ.restrict hφN))
      = Module.length A ((ι → A) ⧸ LinearMap.range (Matrix.toLin' C)) := by
    apply cokerLen_intertwine A (φ.restrict hφN) (Matrix.toLin' C) γ
    apply LinearMap.ext
    intro g
    have hg := (hmemN g.val).mp g.property
    have hkey : (φ (g : (ι ⊕ κ) → A)) ∘ Sum.inl = C.mulVec ((g : (ι ⊕ κ) → A) ∘ Sum.inl) := by
      rw [hφinl, hg, Matrix.mulVec_zero, add_zero]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.restrict_apply]
    change (φ (g : (ι ⊕ κ) → A)) ∘ Sum.inl = Matrix.toLin' C (γ g)
    rw [hγ, Matrix.toLin'_apply]
    exact hkey
  rw [hpieceC, hpieceS]

open Matrix in
/-- The block-lower-triangular counterpart: for `fromBlocks C 0 W S`, the cokernel length
splits as `cokerLen C + cokerLen S`. -/
theorem block_cokerLen_lower (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [Ring.KrullDimLE 1 A]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (C : Matrix ι ι A) (W : Matrix κ ι A) (S : Matrix κ κ A)
    (hCdet : C.det ≠ 0) :
    Module.length A (((ι ⊕ κ) → A) ⧸ LinearMap.range (Matrix.toLin' (Matrix.fromBlocks C 0 W S)))
      = Module.length A ((ι → A) ⧸ LinearMap.range (Matrix.toLin' C))
        + Module.length A ((κ → A) ⧸ LinearMap.range (Matrix.toLin' S)) := by
  have hswap : Matrix.reindex (Equiv.sumComm ι κ) (Equiv.sumComm ι κ) (Matrix.fromBlocks C 0 W S)
      = Matrix.fromBlocks S W 0 C := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.reindex, Matrix.fromBlocks, Matrix.submatrix]
  rw [← cokerLen_reindex A (Equiv.sumComm ι κ) (Matrix.fromBlocks C 0 W S), hswap,
    block_cokerLen A S W C hCdet, add_comm]

open Ring in
/-- Over a one-dimensional Noetherian local domain, `length (A ⧸ span {a})` is finite for
`a ≠ 0`. -/
@[ega "IV 21.10.13" "(i) for M=A, A a domain", ega "IV 21.6.5" "special case"]
theorem spanLen_ne_top (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A] (a : A) (ha : a ≠ 0) :
    Module.length A (A ⧸ Ideal.span {a}) ≠ ⊤ := by
  set K := FractionRing A
  have ha' : algebraMap A K a ≠ 0 := by
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact ha
  have ha0 : a ∈ nonZeroDivisors A := mem_nonZeroDivisors_of_ne_zero ha
  have hord : Ring.ord A a = Module.length A (A ⧸ Ideal.span {a}) := rfl
  rw [← hord]
  intro htop
  have h0 : Ring.ordMonoidWithZeroHom A a = 0 := by
    simp only [Ring.ordMonoidWithZeroHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, ha0, ite_true,
      htop]
    rfl
  have hu : Ring.ordFrac A (K := K) (algebraMap A K a) ≠ 0 :=
    (ha'.isUnit.map (Ring.ordFrac A)).ne_zero
  rw [Ring.ordFrac_eq_ord A (x := a) ha, h0] at hu
  exact hu rfl

/-- `length (A ⧸ span {a ^ k}) = k · length (A ⧸ span {a})`. -/
@[sga "7 X 2.14" "partial"]
theorem spanLen_pow (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A] (a : A) (ha : a ≠ 0) (k : ℕ) :
    Module.length A (A ⧸ Ideal.span {a ^ k}) = k * Module.length A (A ⧸ Ideal.span {a}) := by
  induction k with
  | zero => simp [Submodule.Quotient.subsingleton_iff, Ideal.span_singleton_one]
  | succ m ih =>
    have hak : a ^ m ≠ 0 := pow_ne_zero m ha
    rw [pow_succ, length_span_mul A (a ^ m) a hak, ih]
    push_cast
    ring

/-- Multiplicativity of cokernel length under matrix product, for arbitrary (finite) index. -/
theorem cokerLen_mul (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T₁ T₂ : Matrix ι ι A) (h₁ : T₁.det ≠ 0) :
    Module.length A ((ι → A) ⧸ LinearMap.range (Matrix.toLin' (T₁ * T₂)))
      = Module.length A ((ι → A) ⧸ LinearMap.range (Matrix.toLin' T₁))
        + Module.length A ((ι → A) ⧸ LinearMap.range (Matrix.toLin' T₂)) := by
  have hinj : ∀ (T : Matrix ι ι A), T.det ≠ 0 → Function.Injective (Matrix.toLin' T) := by
    intro T hT
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hx
    exact Matrix.eq_zero_of_mulVec_eq_zero hT hx
  rw [Matrix.toLin'_mul]
  rw [matrix_cokerLen_mul_helper A (ι → A) (Matrix.toLin' T₁) (Matrix.toLin' T₂) (hinj T₁ h₁)]
  rw [add_comm]

/-! ### The matrix base case in length form (Stacks 02QH)

For a square matrix `T` over a one-dimensional Noetherian local domain `A` with `T.det ≠ 0`, the
`A`-length of the cokernel of `T : Aᵐ → Aᵐ` equals the `A`-length of `A ⧸ (det T)`.

This is the analytic content of the matrix base case, stated without the `ordInt` and `.toNat`
wrappers so that the proof works purely with `Module.length`, valued in `ℕ∞`, which is additive
over short exact sequences with no finiteness bookkeeping at intermediate steps.

Both sides are multiplicative under matrix product and agree on scalar matrices, and the closure
is an induction on `m` by Schur clearing, needing no Smith normal form or principal ideal domain.
The pieces are: multiplicativity `cokerLen (T₁ * T₂) = cokerLen T₁ + cokerLen T₂`; the scalar
case `cokerLen (a • 1) = m * length (A ⧸ span {a})`; the dévissage step for a block-triangular
`T`, resting on the short exact sequence of cokernels
`0 → coker(φ|_N) → coker φ → coker φ̄ → 0` for an `N`-preserving endomorphism; and the induction
on `m` wiring these together with the Schur clearing `E₋ · T` block-upper-triangular,
`det E₋ = t₁₁ᵐ`, and Schur complement `S = t₁₁ T₀ - w vᵀ` with `det S ≠ 0`, peeled off by
multiplicativity.

Both `cokerLen` and `length (A ⧸ span {det})` are finite, since `det T ≠ 0` makes `toLin' T`
injective over a domain and so the cokernel torsion of finite length, but the `ℕ∞` statement
needs no `.toNat` juggling.
-/
open Matrix in
/-- The corner core of the Schur-clearing inductive step, on `Fin 1 ⊕ Fin n`-indexed matrices
with nonzero `(0,0)` entry. -/
theorem step_sumform_corner (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [Ring.KrullDimLE 1 A] (n : ℕ)
    (IH : ∀ (S : Matrix (Fin n) (Fin n) A), S.det ≠ 0 →
      Module.length A ((Fin n → A) ⧸ LinearMap.range (Matrix.toLin' S))
        = Module.length A (A ⧸ Ideal.span {S.det}))
    (T' : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) A) (hT' : T'.det ≠ 0)
    (ha : T' (Sum.inl 0) (Sum.inl 0) ≠ 0) :
    Module.length A (((Fin 1 ⊕ Fin n) → A) ⧸ LinearMap.range (Matrix.toLin' T'))
      = Module.length A (A ⧸ Ideal.span {T'.det}) := by
  set a := T' (Sum.inl 0) (Sum.inl 0) with hadef
  set t := T'.toBlocks₁₁ with htdef
  set v := T'.toBlocks₁₂ with hvdef
  set w := T'.toBlocks₂₁ with hwdef
  set T0 := T'.toBlocks₂₂ with hT0def
  have hTblock : T' = Matrix.fromBlocks t v w T0 := (Matrix.fromBlocks_toBlocks T').symm
  have hta : t = a • (1 : Matrix (Fin 1) (Fin 1) A) := by
    ext i j; fin_cases i; fin_cases j; simp [htdef, Matrix.toBlocks₁₁, hadef]
  set Em := Matrix.fromBlocks (a • (1 : Matrix (Fin 1) (Fin 1) A)) 0 (-w)
    (a • (1 : Matrix (Fin n) (Fin n) A)) with hEmdef
  set S := a • T0 - w * v with hSdef
  have hprod : Em * T' = Matrix.fromBlocks (a • t) (a • v) 0 S := by
    rw [hEmdef, hTblock, Matrix.fromBlocks_multiply]
    congr 1
    · simp
    · simp
    · rw [hta]; simp [Matrix.mul_smul, Matrix.smul_mul]
    · simp [hSdef]; abel
  have hat : a • t = (a * a) • (1 : Matrix (Fin 1) (Fin 1) A) := by rw [hta, smul_smul]
  have hdetEm : Em.det = a ^ (n + 1) := by
    rw [hEmdef, Matrix.det_fromBlocks_zero₁₂, Matrix.det_smul, Matrix.det_smul,
      Matrix.det_one, Matrix.det_one, mul_one, mul_one, Fintype.card_fin, Fintype.card_fin, pow_one]
    ring
  have hdetEm_ne : Em.det ≠ 0 := by rw [hdetEm]; exact pow_ne_zero _ ha
  have hdetC : (a • t).det = a ^ 2 := by
    rw [hat, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, pow_one]; ring
  have : (a • t).det ≠ 0 := by rw [hdetC]; exact pow_ne_zero _ ha
  have hdetprod1 : (Em * T').det = a ^ (n + 1) * T'.det := by rw [Matrix.det_mul, hdetEm]
  have hdetprod2 : (Em * T').det = a ^ 2 * S.det := by
    rw [hprod, Matrix.det_fromBlocks_zero₂₁, hdetC]
  have hdetrel : a ^ (n + 1) * T'.det = a ^ 2 * S.det := by rw [← hdetprod1, hdetprod2]
  have hSdet_ne : S.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdetrel
    exact (mul_ne_zero (pow_ne_zero _ ha) hT') hdetrel
  have hcok1 : Module.length A (((Fin 1 ⊕ Fin n) → A) ⧸ LinearMap.range (Matrix.toLin' (Em * T')))
      = Module.length A (((Fin 1 ⊕ Fin n) → A) ⧸ LinearMap.range (Matrix.toLin' Em))
        + Module.length A (((Fin 1 ⊕ Fin n) → A) ⧸ LinearMap.range (Matrix.toLin' T')) :=
    cokerLen_mul A Em T' hdetEm_ne
  have hcok2 : Module.length A (((Fin 1 ⊕ Fin n) → A) ⧸ LinearMap.range (Matrix.toLin' (Em * T')))
      = Module.length A ((Fin 1 → A) ⧸ LinearMap.range (Matrix.toLin' (a • t)))
        + Module.length A ((Fin n → A) ⧸ LinearMap.range (Matrix.toLin' S)) := by
    rw [hprod]; exact block_cokerLen A (a • t) (a • v) S hSdet_ne
  have hcokEm : Module.length A (((Fin 1 ⊕ Fin n) → A) ⧸ LinearMap.range (Matrix.toLin' Em))
      = Module.length A ((Fin 1 → A) ⧸ LinearMap.range (Matrix.toLin' (a • (1 : Matrix (Fin 1) (Fin
          1) A))))
        + Module.length A ((Fin n → A) ⧸ LinearMap.range
            (Matrix.toLin' (a • (1 : Matrix (Fin n) (Fin n) A)))) := by
    rw [hEmdef]
    exact block_cokerLen_lower A (a • (1 : Matrix (Fin 1) (Fin 1) A)) (-w)
      (a • (1 : Matrix (Fin n) (Fin n) A))
      (by rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, pow_one]; exact ha)
  set sa := Module.length A (A ⧸ Ideal.span {a}) with hsa
  have hsa_ne : sa ≠ ⊤ := spanLen_ne_top A a ha
  have hcokEm_val : Module.length A (((Fin 1 ⊕ Fin n) → A) ⧸ LinearMap.range (Matrix.toLin' Em))
      = (↑(n + 1) : ℕ∞) * sa := by
    rw [hcokEm, matrix_cokerLen_scalar A 1 a, matrix_cokerLen_scalar A n a, ← hsa]
    push_cast; ring
  have hcokC_val : Module.length A ((Fin 1 → A) ⧸ LinearMap.range (Matrix.toLin' (a • t)))
      = (2 : ℕ∞) * sa := by
    rw [hat, matrix_cokerLen_scalar A 1 (a * a),
      length_span_mul A a a ha, ← hsa]
    push_cast; ring
  have hcokS : Module.length A ((Fin n → A) ⧸ LinearMap.range (Matrix.toLin' S))
      = Module.length A (A ⧸ Ideal.span {S.det}) := IH S hSdet_ne
  have hcokEq : (↑(n + 1) : ℕ∞) * sa
        + Module.length A (((Fin 1 ⊕ Fin n) → A) ⧸ LinearMap.range (Matrix.toLin' T'))
      = (2 : ℕ∞) * sa + Module.length A (A ⧸ Ideal.span {S.det}) := by
    rw [← hcokEm_val, ← hcokC_val, ← hcokS, ← hcok1, ← hcok2]
  have hdet_eq : (↑(n + 1) : ℕ∞) * sa + Module.length A (A ⧸ Ideal.span {T'.det})
      = (2 : ℕ∞) * sa + Module.length A (A ⧸ Ideal.span {S.det}) := by
    have key : Module.length A (A ⧸ Ideal.span {a ^ (n + 1) * T'.det})
        = Module.length A (A ⧸ Ideal.span {a ^ 2 * S.det}) := by rw [hdetrel]
    rw [length_span_mul A (a ^ (n + 1)) T'.det (pow_ne_zero _ ha),
      length_span_mul A (a ^ 2) S.det (pow_ne_zero _ ha),
      spanLen_pow A a ha, spanLen_pow A a ha, ← hsa] at key
    -- key : L(T'.det) + (n+1)*sa = L(S.det) + 2*sa
    rw [add_comm ((↑(n + 1) : ℕ∞) * sa), add_comm ((2 : ℕ∞) * sa)]
    exact key
  have hfin : (↑(n + 1) : ℕ∞) * sa ≠ ⊤ := WithTop.mul_ne_top (ENat.natCast_ne_top _) hsa_ne
  exact WithTop.add_left_cancel hfin (hcokEq.trans hdet_eq.symm)

open Matrix in
/-- The inductive step after a permutation reduction arranging a nonzero `(0,0)` corner. -/
theorem step_sumform (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] [Ring.KrullDimLE 1 A] (n : ℕ)
    (IH : ∀ (S : Matrix (Fin n) (Fin n) A), S.det ≠ 0 →
      Module.length A ((Fin n → A) ⧸ LinearMap.range (Matrix.toLin' S))
        = Module.length A (A ⧸ Ideal.span {S.det}))
    (T' : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) A) (hT' : T'.det ≠ 0) :
    Module.length A (((Fin 1 ⊕ Fin n) → A) ⧸ LinearMap.range (Matrix.toLin' T'))
      = Module.length A (A ⧸ Ideal.span {T'.det}) := by
  -- column `inl 0` is nonzero
  obtain ⟨r, hr⟩ : ∃ i, T' i (Sum.inl 0) ≠ 0 := by
    by_contra h
    push Not at h
    exact hT' (Matrix.det_eq_zero_of_column_eq_zero (Sum.inl 0) h)
  set σ := Equiv.swap (Sum.inl 0 : Fin 1 ⊕ Fin n) r with hσ
  set P := σ.permMatrix A with hP
  have hPunit : IsUnit P.det := by
    rw [hP, Matrix.det_permutation]
    exact (Int.isUnit_iff.mpr (by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h])).map (Int.castRingHom
          A)
  have hPdet_ne : P.det ≠ 0 := hPunit.ne_zero
  -- corner of P * T'
  have hcorner : (P * T') (Sum.inl 0) (Sum.inl 0) ≠ 0 := by
    have happ : (P * T') (Sum.inl 0) (Sum.inl 0) = T' (σ (Sum.inl 0)) (Sum.inl 0) := by
      rw [hP]
      simp [Equiv.Perm.permMatrix, Matrix.mul_apply, PEquiv.toMatrix, Equiv.toPEquiv_apply]
    rw [happ, hσ, Equiv.swap_apply_left]
    exact hr
  have hPT'det : (P * T').det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero hPdet_ne hT'
  -- cokernel: cokerLen (P*T') = cokerLen P + cokerLen T' = cokerLen T'
  have hcokP : Module.length A (((Fin 1 ⊕ Fin n) → A) ⧸ LinearMap.range (Matrix.toLin' P)) = 0 :=
    cokerLen_isUnit A P hPunit
  have hcok : Module.length A (((Fin 1 ⊕ Fin n) → A) ⧸ LinearMap.range (Matrix.toLin' (P * T')))
      = Module.length A (((Fin 1 ⊕ Fin n) → A) ⧸ LinearMap.range (Matrix.toLin' T')) := by
    rw [cokerLen_mul A P T' hPdet_ne, hcokP, zero_add]
  -- span: spanLen (det (P*T')) = spanLen (det T')
  have hspan : Module.length A (A ⧸ Ideal.span {(P * T').det})
      = Module.length A (A ⧸ Ideal.span {T'.det}) := by
    rw [Matrix.det_mul, length_span_mul A P.det T'.det hPdet_ne, spanLen_isUnit A P.det hPunit,
      add_zero]
  -- apply the corner core to P * T'
  have hcore := step_sumform_corner A n IH (P * T') hPT'det hcorner
  rw [← hcok, hcore, hspan]

/-! ### The inductive step of `matrix_cokerLen_eq_spanLen`

Given the identity for all `n × n` matrices as induction hypothesis, prove it for an
`(n+1) × (n+1)` matrix `T` with `T.det ≠ 0`. This is the Schur clearing step:

  * Permutation reduction (II.4b): a permutation `P` (an isomorphism, `cokerLen P = 0`, and
    `det P = ±1` a unit so `length (A/span{det P}) = 0`) moves a row with nonzero first entry to
    the top, so WLOG `T 0 0 ≠ 0`.  Peel `P` via `matrix_cokerLen_mul` + `length_span_mul`.
  * Schur clearing: left-multiply `T` by the block-lower-triangular clearing matrix
    `E₋ = [[t₀₀, 0], [-w, t₀₀ • I]]` (`w` the first column below `t₀₀`); `det E₋ = t₀₀^(n+1)` and
    `E₋ T` is block-UPPER-triangular with diagonal blocks `t₀₀²` (a `1×1`) and the Schur
    complement `S = t₀₀ • T₀ - w ⬝ vᵀ ∈ M_n(A)`, with `det (E₋ T) = t₀₀² · det S` and
    `det (E₋ T) = t₀₀^(n+1) · det T`, so `det S ≠ 0`.
  * Block-upper-triangular dévissage (II.4a, via `matrix_cokerLen_devissage` with `N = A·e₀`):
    `cokerLen (E₋ T) = length (A/span{t₀₀²}) + cokerLen S`, and by `IH` on `S`,
    `cokerLen S = length (A/span{det S})`.
  * Recombine on the span side with `length_span_mul` using the two determinant relations.
-/

/-- Over a one-dimensional Noetherian local domain `A`, if the cokernel length of `toLin' S`
equals `length (A ⧸ span {det S})` for every `n × n` matrix `S` with `det S ≠ 0`, then the same
holds for every `(n+1) × (n+1)` matrix `T` with `det T ≠ 0`. -/
theorem matrix_cokerLen_eq_spanLen_step
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (n : ℕ)
    (IH : ∀ (S : Matrix (Fin n) (Fin n) A), S.det ≠ 0 →
      Module.length A ((Fin n → A) ⧸ LinearMap.range (Matrix.toLin' S))
        = Module.length A (A ⧸ Ideal.span {S.det}))
    (T : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (hT : T.det ≠ 0) :
    Module.length A ((Fin (n + 1) → A) ⧸ LinearMap.range (Matrix.toLin' T))
      = Module.length A (A ⧸ Ideal.span {T.det}) := by
  -- Reindex to `Fin 1 ⊕ Fin n` and apply the Schur-clearing reduction `step_sumform`.
  set e : Fin (n + 1) ≃ (Fin 1 ⊕ Fin n) :=
    (finCongr (add_comm n 1)).trans finSumFinEquiv.symm with he
  set T' := Matrix.reindex e e T with hT'def
  have hdetT' : T'.det = T.det := by rw [hT'def, Matrix.det_reindex_self]
  have hT'ne : T'.det ≠ 0 := by rw [hdetT']; exact hT
  have hcok : Module.length A (((Fin 1 ⊕ Fin n) → A) ⧸ LinearMap.range (Matrix.toLin' T'))
      = Module.length A ((Fin (n + 1) → A) ⧸ LinearMap.range (Matrix.toLin' T)) :=
    cokerLen_reindex A e T
  rw [← hcok, step_sumform A n IH T' hT'ne, hdetT']

/-- For a square matrix `T` over a one-dimensional Noetherian local domain with `det T ≠ 0`,
the cokernel length of `toLin' T` equals `length (A ⧸ span {det T})`. -/
@[ega "IV 21.10.17.3" "special case"]
theorem matrix_cokerLen_eq_spanLen
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (m : ℕ) (T : Matrix (Fin m) (Fin m) A) (hT : T.det ≠ 0) :
    Module.length A ((Fin m → A) ⧸ LinearMap.range (Matrix.toLin' T))
      = Module.length A (A ⧸ Ideal.span {T.det}) := by
  -- Stacks 02QH; the standard length-of-cokernel = ord-of-det identity).
  -- WIRING (VERIFIED): induction on `m`.  Base case `m = 0` is the zero module on both sides;
  -- the inductive step is `matrix_cokerLen_eq_spanLen_step` (the Part-II.4 Schur-clearing core).
  -- `T`/`hT` depend on `m`, so prove the universally-quantified statement by induction.
  suffices h : ∀ (k : ℕ) (S : Matrix (Fin k) (Fin k) A), S.det ≠ 0 →
      Module.length A ((Fin k → A) ⧸ LinearMap.range (Matrix.toLin' S))
        = Module.length A (A ⧸ Ideal.span {S.det}) by
    exact h m T hT
  intro k
  induction k with
  | zero =>
    intro S _
    have hdet : S.det = 1 := by simp [Matrix.det_fin_zero]
    rw [hdet, Ideal.span_singleton_one]
    have hl : Module.length A ((Fin 0 → A) ⧸ LinearMap.range (Matrix.toLin' S)) = 0 :=
      Module.length_eq_zero_iff.mpr ⟨fun a b => Subsingleton.elim a b⟩
    rw [hl]
    symm
    exact Module.length_eq_zero_iff.mpr ⟨fun a b => Subsingleton.elim a b⟩
  | succ n IH =>
    intro S hS
    exact matrix_cokerLen_eq_spanLen_step A n IH S hS

/-- The order of vanishing of `det T` equals the length of the cokernel of `toLin' T`. -/
@[ega "IV 21.10.17.3" "special case"]
theorem ordInt_matrix_det_eq_length_cokernel
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (m : ℕ) (T : Matrix (Fin m) (Fin m) A) (hT : T.det ≠ 0)
    (hTK : algebraMap A K T.det ≠ 0) :
    ordInt A (algebraMap A K T.det) hTK =
      ((Module.length A ((Fin m → A) ⧸ LinearMap.range (Matrix.toLin' T))).toNat : ℤ) := by
  -- CITATION: Stacks Tag 02QH matrix base case.  Reduced (this iteration) to the pure `ℕ∞`
  -- length identity `matrix_cokerLen_eq_spanLen` via the already-proven `ordInt_algebraMap`
  -- applied to `r = T.det`.  SANITY CHECK PASSED.
  rw [ordInt_algebraMap A T.det hT hTK]
  rw [matrix_cokerLen_eq_spanLen A m T hT]

/-! ## Inputs for the 02QH kernel `ordInt_baseChangeDet_eq_length_cokernel`

The proof works with the integer
**defect** of an injective endomorphism `ψ` of a finite torsion-free `A`-module `N` whose base
change is a `K`-automorphism:

  `Δ(N,ψ) := (length_A (N ⧸ range ψ)).toNat  −  ordInt A (det (ψ.baseChange K))`.

The goal `ordInt_baseChangeDet_eq_length_cokernel` is exactly `Δ(M,φ) = 0`.

The argument (Route γ) is:
* (Lemma C) `Δ` of an endomorphism of a finite-length module is `0` (`length ker = length coker`);
* (Lemma B) `Δ(Aʳ, T) = 0` for a matrix `T` with `det T ≠ 0` — this is the PROVEN matrix base
  case `ordInt_matrix_det_eq_length_cokernel`;
* (Step 1) a full-rank free submodule `F ≅ Aʳ ⊆ M` with finite-length quotient `Q = M/F`;
* (Lemma A) `Δ` is additive over the SES `0 → F → M → Q → 0` when the endomorphism preserves `F`;
* (Step 2) replace `φ` by `ψ = a·φ` (`a ≠ 0 ∈ A`) so that `ψ` preserves `F`; then
  `Δ(M,ψ) = Δ(F,ψ|F) + Δ(Q,ψ̄) = 0 + 0 = 0` (Lemmas A,B,C);
* (Lemma D) the scalar identity `Δ(M, a·id) = 0` (same machinery, A+B+C);
* (comp) `Δ` is additive under composition `Δ(M, a·φ) = Δ(M, a·id) + Δ(M, φ)`,
  hence `Δ(M,φ) = Δ(M,ψ) − Δ(M, a·id) = 0`.

The reusable analytic content is packaged as the four lemmas
`length_ker_eq_length_coker_finiteLength`, `length_quot_smul_eq_rank_mul_ord`,
`exists_fullRank_free_submodule` and `defect_devissage_free`, assembled in the kernel proof.
-/

/-- For an endomorphism `ψ` of a finite-length `A`-module `L`, the kernel and cokernel have equal
`A`-length. Both `0 → ker ψ → L → im ψ → 0` and `0 → im ψ → L → coker ψ → 0` are short exact, so
additivity of `Module.length` gives
`length L = length ker + length im = length im + length coker`. -/
@[ega "IV 21.10.13" "(iii)"]
theorem length_ker_eq_length_coker_finiteLength
    (A : Type*) [CommRing A]
    (L : Type*) [AddCommGroup L] [Module A L] (hL : Module.length A L ≠ ⊤)
    (ψ : L →ₗ[A] L) :
    Module.length A (LinearMap.ker ψ) = Module.length A (L ⧸ LinearMap.range ψ) := by
  -- Use `Module.length_eq_add_of_exact` on the two SES through `im ψ ≅ L ⧸ ker ψ`.
  -- SES (1): 0 → ker ψ → L → L ⧸ ker ψ → 0
  have h1 : Module.length A L
      = Module.length A (LinearMap.ker ψ) + Module.length A (L ⧸ LinearMap.ker ψ) :=
    Module.length_eq_add_of_exact (LinearMap.ker ψ).subtype (LinearMap.ker ψ).mkQ
      Subtype.coe_injective (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  -- L ⧸ ker ψ ≅ range ψ
  have heq : Module.length A (L ⧸ LinearMap.ker ψ) = Module.length A (LinearMap.range ψ) :=
    (LinearMap.quotKerEquivRange ψ).length_eq
  -- SES (2): 0 → range ψ → L → L ⧸ range ψ → 0
  have h2 : Module.length A L
      = Module.length A (LinearMap.range ψ) + Module.length A (L ⧸ LinearMap.range ψ) :=
    Module.length_eq_add_of_exact (LinearMap.range ψ).subtype (LinearMap.range ψ).mkQ
      Subtype.coe_injective (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  -- combine: length(ker) + length(range) = length(range) + length(coker)
  rw [heq] at h1
  rw [h1, add_comm (Module.length A (LinearMap.ker ψ))] at h2
  -- h2 : range + ker = range + coker
  have hrange_ne : Module.length A (LinearMap.range ψ) ≠ ⊤ := by
    have hle := Module.length_le_of_injective (LinearMap.range ψ).subtype Subtype.coe_injective
    intro h; apply hL; exact top_le_iff.mp (h ▸ hle)
  exact WithTop.add_left_cancel hrange_ne h2

/-- STEP 1 (Route γ).  A finitely generated torsion-free module `M` over the `1`-dimensional
Noetherian local domain `A` contains a free `A`-submodule `F ≅ Aʳ` of full rank
`r = finrank K (M ⊗ K)` whose quotient `M ⧸ F` has finite length. Concretely there is an
injective `A`-linear map `j : (Fin r → A) →ₗ[A] M` with
`Module.length A (M ⧸ LinearMap.range j) ≠ ⊤`.
(Choose `x₁,…,x_r ∈ M` mapping to a `K`-basis of `M ⊗ K`; torsion-freeness ⟹ `A`-independent ⟹ `F`
free; `(M/F) ⊗ K = 0` ⟹ `M/F` torsion f.g. ⟹ finite length.) -/
theorem exists_fullRank_free_submodule
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] [NoZeroSMulDivisors A M] :
    ∃ j : (Fin (Module.finrank K (TensorProduct A K M)) → A) →ₗ[A] M,
      Function.Injective j ∧ Module.length A (M ⧸ LinearMap.range j) ≠ ⊤ := by
  classical
  have : FiniteDimensional K (TensorProduct A K M) := inferInstance
  -- Artinian helper: A/(a) is Artinian for a ≠ 0 (dim A/(a) ≤ dim A - 1 = 0).
  have hArt : ∀ (a : A), a ≠ 0 → IsArtinianRing (A ⧸ Ideal.span {a}) := by
    intro a ha
    rw [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
    refine ⟨inferInstance, ?_⟩
    rw [Ring.krullDimLE_iff]
    have hmem : a ∈ nonZeroDivisors A := mem_nonZeroDivisors_of_ne_zero ha
    have hq := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hmem
    have hA : ringKrullDim A ≤ ((1:ℕ):WithBot ℕ∞) := Ring.krullDimLE_iff.mp inferInstance
    have h : ringKrullDim (A ⧸ Ideal.span {a}) + 1 ≤ ((1:ℕ):WithBot ℕ∞) := le_trans hq hA
    set d := ringKrullDim (A ⧸ Ideal.span {a}) with hd
    have h' : d + 1 ≤ ((1:ℕ∞):WithBot ℕ∞) := by rw [← WithBot.coe_natCast] at h; exact_mod_cast h
    change d ≤ ((0:ℕ):WithBot ℕ∞)
    rw [show ((0:ℕ):WithBot ℕ∞) = ((0:ℕ∞):WithBot ℕ∞) by norm_cast]
    rw [WithBot.le_coe_iff]
    intro a' hda
    rw [hda] at h'
    have h2 : a' + 1 ≤ 1 := by exact_mod_cast h'
    cases a' with
    | top => simp at h2
    | coe n =>
      rw [← ENat.natCast_one, ← ENat.natCast_add, ENat.natCast_le_natCast] at h2
      have : n = 0 := by omega
      subst this; simp
  -- The image of `M → K ⊗ M` (via `m ↦ 1 ⊗ₜ m`) `K`-spans `K ⊗ M`.
  have hspan : Submodule.span K (Set.range (fun m : M => (1:K) ⊗ₜ[A] m)) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    induction z using TensorProduct.inductionOn with
    | tmul k m =>
        have hkm : k ⊗ₜ[A] m = k • ((1:K) ⊗ₜ[A] m) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hkm]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
    | add p q hp hq => exact Submodule.add_mem _ (hp Submodule.mem_top) (hq Submodule.mem_top)
  -- Choose `x₁,…,x_r ∈ M` whose images `1 ⊗ₜ xᵢ` form a `K`-basis of `K ⊗ M`.
  obtain ⟨x, bM, hbM⟩ :
      ∃ (x : Fin (Module.finrank K (TensorProduct A K M)) → M)
        (bM : Module.Basis (Fin (Module.finrank K (TensorProduct A K M))) K (TensorProduct A K M)),
        ∀ i, bM i = (1:K) ⊗ₜ[A] x i := by
    obtain ⟨b, hbsub, hbspan, hbli⟩ :=
      exists_linearIndependent K (Set.range (fun m : M => (1:K) ⊗ₜ[A] m))
    rw [hspan] at hbspan
    have hsple : ⊤ ≤ Submodule.span K (Set.range (Subtype.val : ↥b → TensorProduct A K M)) := by
      rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hbspan]
    set basis : Module.Basis (↥b) K (TensorProduct A K M) := Module.Basis.mk hbli hsple with hbasis
    have : Fintype (↥b) := FiniteDimensional.fintypeBasisIndex basis
    have hcard : Fintype.card (↥b) = Module.finrank K (TensorProduct A K M) :=
      (Module.finrank_eq_card_basis basis).symm
    set eqv : Fin (Module.finrank K (TensorProduct A K M)) ≃ ↥b :=
      (Fintype.equivFinOfCardEq hcard).symm with heqv
    have hmem : ∀ i, ((eqv i : TensorProduct A K M)) ∈
        Set.range (fun m : M => (1:K) ⊗ₜ[A] m) := fun i => hbsub (eqv i).property
    choose x hx using hmem
    refine ⟨x, basis.reindex eqv.symm, ?_⟩
    intro i
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, hbasis, Module.Basis.mk_apply]
    exact (hx i).symm
  -- The (injective) embedding `ι : M → K ⊗ M`, `m ↦ 1 ⊗ₜ m`, via localization.
  set ι : M →ₗ[A] TensorProduct A K M := (TensorProduct.mk A K M) 1 with hιdef
  have hιinj : Function.Injective ι := by
    have : IsLocalizedModule (nonZeroDivisors A) ι := by
      rw [hιdef, isLocalizedModule_iff_isBaseChange (nonZeroDivisors A) K]
      exact TensorProduct.isBaseChange A M K
    intro m m' h
    rw [← sub_eq_zero] at h ⊢
    rw [← map_sub, IsLocalizedModule.eq_zero_iff (nonZeroDivisors A)] at h
    obtain ⟨s, hs⟩ := h
    have hs0 : (s : A) ≠ 0 := nonZeroDivisors.ne_zero s.property
    refine smul_right_injective M hs0 ?_
    simp only [smul_zero]; exact hs
  have hιx : ∀ i, ι (x i) = bM i := fun i => by rw [hιdef]; exact (hbM i).symm
  -- The candidate map `j : Aʳ → M`, `eᵢ ↦ xᵢ`.
  set j : (Fin (Module.finrank K (TensorProduct A K M)) → A) →ₗ[A] M :=
    Fintype.linearCombination A x with hjdef
  -- Injectivity of `j` from `K`-independence of `1 ⊗ₜ xᵢ` and injectivity of `A → K`.
  have hjinj : Function.Injective j := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h0 : ι (j v) = 0 := by rw [hv]; exact map_zero ι
    rw [hjdef, Fintype.linearCombination_apply, map_sum] at h0
    have h0' : ∑ i, (algebraMap A K (v i)) • bM i = 0 := by
      rw [← h0]; apply Finset.sum_congr rfl; intro i _
      rw [map_smul, hιx i, algebraMap_smul]
    have hli := bM.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    have hz := hli (fun i => algebraMap A K (v i)) h0'
    funext i
    exact (FaithfulSMul.algebraMap_injective A K) ((hz i).trans (map_zero _).symm)
  refine ⟨j, hjinj, ?_⟩
  -- Every element of `M` becomes a `K`-combination of the `1 ⊗ₜ xᵢ`; clearing denominators
  -- shows some nonzero scalar carries it into `range j`.
  have htorM : ∀ m : M, ∃ a : A, a ≠ 0 ∧ a • m ∈ LinearMap.range j := by
    intro m
    set c := fun i => (bM.repr (ι m)) i with hc
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A) c
    set a : A := (b : A) with ha
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero b.property
    choose d hd using hb
    refine ⟨a, ha0, ⟨d, ?_⟩⟩
    apply hιinj
    rw [hjdef, Fintype.linearCombination_apply, map_smul, map_sum]
    conv_rhs => rw [← Module.Basis.sum_repr bM (ι m)]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, hιx i, ← algebraMap_smul (R := A) K (d i) (bM i), hd i, smul_assoc]
  -- Hence `Q = M ⧸ range j` is a torsion module: each element is killed by a nonzero scalar.
  have htorQ : ∀ q : M ⧸ LinearMap.range j, ∃ a : A, a ≠ 0 ∧ a • q = 0 := by
    intro q
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨a, ha0, hmem⟩ := htorM m
    refine ⟨a, ha0, ?_⟩
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hmem
  -- `Q` is finitely generated and torsion, hence annihilated by a single nonzero `a`.
  obtain ⟨a, ha0, hann⟩ : ∃ a : A, a ≠ 0 ∧ ∀ q : M ⧸ LinearMap.range j, a • q = 0 := by
    obtain ⟨s, hs⟩ := (Module.finite_def.mp (by infer_instance) :
      (⊤ : Submodule A (M ⧸ LinearMap.range j)).FG)
    choose f hf0 hf using htorQ
    set a : A := ∏ g ∈ s, f g with ha
    have ha0 : a ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun g _ => hf0 g)
    refine ⟨a, ha0, ?_⟩
    have hgen : ∀ g ∈ s, a • g = 0 := by
      intro g hg
      rw [ha, ← Finset.prod_erase_mul _ _ hg, mul_smul, hf g, smul_zero]
    intro q
    have hq : q ∈ (⊤ : Submodule A (M ⧸ LinearMap.range j)) := Submodule.mem_top
    rw [← hs] at hq
    induction hq using Submodule.span_induction with
    | mem y hy => exact hgen y hy
    | zero => exact smul_zero a
    | add y z _ _ hy hz => rw [smul_add, hy, hz, add_zero]
    | smul c y _ hy => rw [smul_comm, hy, smul_zero]
  -- `Q` is a finite module over the Artinian ring `A/(a)`, hence Artinian over `A`.
  have hArtQ : IsArtinian A (M ⧸ LinearMap.range j) := by
    set I : Ideal A := Ideal.span {a} with hI
    have htor : Module.IsTorsionBySet A (M ⧸ LinearMap.range j) (I : Set A) := by
      intro q r
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp r.property
      rw [← hc, mul_smul, hann]; simp
    let : Module (A ⧸ I) (M ⧸ LinearMap.range j) := htor.module
    have : IsScalarTower A (A ⧸ I) (M ⧸ LinearMap.range j) := htor.isScalarTower
    have : Module.Finite (A ⧸ I) (M ⧸ LinearMap.range j) :=
      Module.Finite.of_restrictScalars_finite A (A ⧸ I) (M ⧸ LinearMap.range j)
    have : IsArtinianRing (A ⧸ I) := hArt a ha0
    have : IsArtinian (A ⧸ I) (M ⧸ LinearMap.range j) := isArtinian_of_fg_of_artinian'
    exact isArtinian_of_surjective_algebraMap (S := A) (R := A ⧸ I)
      (M := M ⧸ LinearMap.range j) Ideal.Quotient.mk_surjective
  -- Noetherian + Artinian = finite length, so the length is not `⊤`.
  rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨inferInstance, hArtQ⟩

/-- DÉVISSAGE — MATRIX OF `ψ` ON THE FREE SUBMODULE (Route γ, Step 0).  If `ψ` preserves the
submodule `range j` for an INJECTIVE `j`, then there is a (unique) `A`-linear `S : Aʳ → Aʳ` with
`ψ ∘ₗ j = j ∘ₗ S`.  (Universal property of the injective `j`: each `ψ (j x) ∈ range j` has a unique
preimage under `j`; assemble into a linear map via the linear equiv `Aʳ ≃ range j` coming
from injectivity, using `LinearEquiv.ofInjective j` and `LinearMap.codRestrict`.) -/
theorem exists_matrix_of_preserves_range
    (A : Type*) [CommRing A]
    (M : Type*) [AddCommGroup M] [Module A M]
    (n : ℕ)
    (ψ : M →ₗ[A] M)
    (j : (Fin n → A) →ₗ[A] M)
    (hjinj : Function.Injective j)
    (hpres : ∀ x, ψ (j x) ∈ LinearMap.range j) :
    ∃ S : (Fin n → A) →ₗ[A] (Fin n → A), ψ ∘ₗ j = j ∘ₗ S := by
  refine ⟨(LinearEquiv.ofInjective j hjinj).symm.toLinearMap ∘ₗ
      (LinearMap.codRestrict (LinearMap.range j) (ψ ∘ₗ j) hpres), ?_⟩
  ext x
  simp only [LinearMap.comp_apply]
  have : (LinearEquiv.ofInjective j hjinj) ((LinearEquiv.ofInjective j hjinj).symm
      ⟨ψ (j x), hpres x⟩) = ⟨ψ (j x), hpres x⟩ :=
    (LinearEquiv.ofInjective j hjinj).apply_symm_apply _
  have h2 := congrArg (Submodule.subtype (LinearMap.range j)) this
  simp

/-- DÉVISSAGE — DET SIDE (Route γ).  If `ψ` preserves the full-rank free submodule `range j`
(with `j` injective, finite-length quotient), and `S : Aʳ → Aʳ` is the matrix of `ψ` on that free
submodule (the unique map with `j ∘ₗ S = ψ ∘ₗ j`), then the base-change determinant of `ψ` equals
`algebraMap A K (det S)`.

*Proof.* Tensor `ψ ∘ₗ j = j ∘ₗ S` with the flat `A`-algebra `K` to get
`(ψ⊗K) ∘ (j⊗K) = (j⊗K) ∘ (S⊗K)`. Now `j⊗K` is a `K`-isomorphism, by full rank `r`,
torsion cokernel `Q⊗K = 0` and flatness of `K`, so `ψ⊗K` is conjugate to `S⊗K`. Finally
`det` is conjugation-invariant
(`LinearMap.det_conj`) and `det (S.baseChange K) = algebraMap A K (det S)`
(`LinearMap.det_baseChange`, `S` an endo of the free module `Fin r → A`). -/
@[ega "II 6.4.2" "special case"]
theorem det_baseChange_eq_algebraMap_det
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] [NoZeroSMulDivisors A M]
    (ψ : M →ₗ[A] M)
    (j : (Fin (Module.finrank K (TensorProduct A K M)) → A) →ₗ[A] M)
    (hjinj : Function.Injective j)
    (S : (Fin (Module.finrank K (TensorProduct A K M)) → A) →ₗ[A]
        (Fin (Module.finrank K (TensorProduct A K M)) → A))
    (hS : ψ ∘ₗ j = j ∘ₗ S) :
    LinearMap.det (ψ.baseChange K) = algebraMap A K (LinearMap.det S) := by
  have : Module.Flat A K := IsLocalization.flat K (nonZeroDivisors A)
  have hjKinj : Function.Injective (j.baseChange K) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap j hjinj
  have : FiniteDimensional K (TensorProduct A K M) := inferInstance
  have : FiniteDimensional K (TensorProduct A K (Fin (Module.finrank K (TensorProduct A K M)) →
      A)) :=
    inferInstance
  have hdim : Module.finrank K (TensorProduct A K (Fin (Module.finrank K (TensorProduct A K M)) →
      A))
      = Module.finrank K (TensorProduct A K M) := by
    rw [Module.finrank_baseChange]; simp
  have hbij : Function.Bijective (j.baseChange K) := by
    refine ⟨hjKinj, ?_⟩
    have hr : Module.finrank K (LinearMap.range (j.baseChange K))
        = Module.finrank K (TensorProduct A K M) := by
      rw [LinearMap.finrank_range_of_inj hjKinj, hdim]
    rw [← LinearMap.range_eq_top]
    exact Submodule.eq_top_of_finrank_eq hr
  set e : (TensorProduct A K (Fin (Module.finrank K (TensorProduct A K M)) → A)) ≃ₗ[K]
      (TensorProduct A K M) := LinearEquiv.ofBijective (j.baseChange K) hbij with he
  have hint : (ψ.baseChange K) ∘ₗ (j.baseChange K) = (j.baseChange K) ∘ₗ (S.baseChange K) := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hS]
  have hconj : ψ.baseChange K = (e : _ →ₗ[K] _) ∘ₗ (S.baseChange K) ∘ₗ (e.symm : _ →ₗ[K] _) := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    have hey : e y = (j.baseChange K) y := rfl
    rw [hey]
    have := LinearMap.congr_fun hint y
    simp only [LinearMap.comp_apply] at this
    exact this
  rw [hconj, LinearMap.det_conj, LinearMap.det_baseChange]

/-- Dévissage on the length side. With `ψ` injective preserving the full-rank free submodule
`range j` (finite-length quotient `Q = M ⧸ range j`) and `S : Aʳ → Aʳ` its matrix on the free part
(`j ∘ₗ S = ψ ∘ₗ j`), the cokernel of `ψ` on `M` has the SAME length as the cokernel of `S` on `Aʳ`.

*Proof.* The map `j` carries `range S` onto `range (ψ|F)`, giving
`length(Aʳ/range S) = length(F/range(ψ|F))`.  The snake lemma for the SES `0 → F → M → Q → 0` with
`ψ` acting (`ψ|F` on `F`, `ψ̄` on `Q`) yields a 6-term exact sequence; `ker ψ = 0`, `ker (ψ|F) = 0`
reduce it to `0 → ker ψ̄ → F/range(ψ|F) → M/range ψ → Q/range ψ̄ → 0`.  Splitting into two SES and
using `Module.length_eq_add_of_exact` gives `length(M/range ψ) − length(F/range(ψ|F)) =
length(Q/range ψ̄) − length(ker ψ̄)`, which vanishes by Lemma C
(`length_ker_eq_length_coker_finiteLength`, `Q` finite length — `ψ̄` need NOT be injective). -/
theorem length_quot_range_eq_of_intertwine
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] [NoZeroSMulDivisors A M]
    (ψ : M →ₗ[A] M) (hψinj : Function.Injective ψ)
    (j : (Fin (Module.finrank K (TensorProduct A K M)) → A) →ₗ[A] M)
    (hjinj : Function.Injective j)
    (hjlen : Module.length A (M ⧸ LinearMap.range j) ≠ ⊤)
    (S : (Fin (Module.finrank K (TensorProduct A K M)) → A) →ₗ[A]
        (Fin (Module.finrank K (TensorProduct A K M)) → A))
    (hS : ψ ∘ₗ j = j ∘ₗ S) :
    Module.length A (M ⧸ LinearMap.range ψ) =
      Module.length A ((Fin (Module.finrank K (TensorProduct A K M)) → A) ⧸ LinearMap.range S) := by
  classical
  set F := LinearMap.range j with hFdef
  -- ψ preserves F = range j, since ψ (j x) = j (S x) ∈ range j.
  have hjSeq : ∀ x, ψ (j x) = j (S x) := by
    intro x
    have := LinearMap.congr_fun hS x
    simp only [LinearMap.comp_apply] at this
    exact this
  have hψFmem : ∀ x ∈ F, ψ x ∈ F := by
    rintro _ ⟨x, rfl⟩
    rw [hjSeq x]
    exact ⟨S x, rfl⟩
  have hψF : F ≤ Submodule.comap ψ F := hψFmem
  set ψF := ψ.restrict hψFmem with hψFdef
  set ψbar := F.mapQ F ψ hψF with hψbardef
  -- STEP 1: length(Aʳ/range S) = length(F/range ψF), via the iso j : Aʳ ≃ₗ F.
  have step1 : Module.length A ((Fin (Module.finrank K (TensorProduct A K M)) → A) ⧸
      LinearMap.range S)
      = Module.length A (LinearMap.range j ⧸ LinearMap.range ψF) := by
    apply cokerLen_intertwine A S ψF (LinearEquiv.ofInjective j hjinj)
    refine LinearMap.ext fun x => Subtype.ext ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hψFdef, LinearMap.coe_restrict_apply]
    rw [LinearEquiv.ofInjective_apply, LinearEquiv.ofInjective_apply]
    exact (hjSeq x).symm
  -- Q-finite-length: length(M/F) ≠ ⊤
  have hQfin : Module.length A (M ⧸ F) ≠ ⊤ := by rw [hFdef]; exact hjlen
  -- f : F/range ψF → M/range ψ  induced by F.subtype
  have hf : LinearMap.range ψF ≤ Submodule.comap F.subtype (LinearMap.range ψ) := by
    rintro _ ⟨z, rfl⟩
    rw [Submodule.mem_comap]
    refine ⟨(z : M), ?_⟩
    rw [hψFdef, Submodule.subtype_apply, LinearMap.coe_restrict_apply]
  set f : (F ⧸ LinearMap.range ψF) →ₗ[A] (M ⧸ LinearMap.range ψ) :=
    Submodule.mapQ (LinearMap.range ψF) (LinearMap.range ψ) F.subtype hf with hfdef
  -- g : M/range ψ → Q/range ψbar  induced by F.mkQ
  have hg : LinearMap.range ψ ≤ Submodule.comap F.mkQ (LinearMap.range ψbar) := by
    rintro _ ⟨m, rfl⟩
    rw [Submodule.mem_comap]
    refine ⟨F.mkQ m, ?_⟩
    rw [hψbardef, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.mkQ_apply]
  set g : (M ⧸ LinearMap.range ψ) →ₗ[A] ((M ⧸ F) ⧸ LinearMap.range ψbar) :=
    Submodule.mapQ (LinearMap.range ψ) (LinearMap.range ψbar) F.mkQ hg with hgdef
  -- g is surjective
  have hgsurj : Function.Surjective g := by
    intro w
    obtain ⟨q, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range ψbar) w
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective F q
    refine ⟨(LinearMap.range ψ).mkQ m, ?_⟩
    simp only [hgdef, Submodule.mkQ_apply, Submodule.mapQ_apply]
  -- exactness at M/range ψ : range f = ker g
  have hexact : LinearMap.range f = LinearMap.ker g := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range ψF) z
      rw [LinearMap.mem_ker]
      simp only [hfdef, hgdef, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.subtype_apply]
      rw [Submodule.Quotient.mk_eq_zero]
      have hx0 : (Submodule.Quotient.mk (x : M) : M ⧸ F) = 0 :=
        (Submodule.Quotient.mk_eq_zero F).mpr x.property
      rw [hx0]
      exact zero_mem _
    · intro z hz
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range ψ) z
      rw [LinearMap.mem_ker] at hz
      simp only [hgdef, Submodule.mkQ_apply, Submodule.mapQ_apply] at hz
      rw [Submodule.Quotient.mk_eq_zero] at hz
      obtain ⟨q, hq⟩ := hz
      obtain ⟨m', rfl⟩ := Submodule.mkQ_surjective F q
      rw [hψbardef, Submodule.mkQ_apply, Submodule.mapQ_apply] at hq
      have hmem : m - ψ m' ∈ F := (Submodule.Quotient.eq F).mp hq.symm
      refine ⟨(LinearMap.range ψF).mkQ ⟨m - ψ m', hmem⟩, ?_⟩
      simp only [hfdef, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.subtype_apply]
      rw [Submodule.Quotient.eq]
      exact ⟨-m', by simp⟩
  -- eq1: SES  0 → range f → M/range ψ → Q/range ψbar → 0
  have eq1 : Module.length A (M ⧸ LinearMap.range ψ)
      = Module.length A (LinearMap.range f)
        + Module.length A ((M ⧸ F) ⧸ LinearMap.range ψbar) :=
    Module.length_eq_add_of_exact (LinearMap.range f).subtype g Subtype.coe_injective hgsurj
      (by rw [LinearMap.exact_iff, Submodule.range_subtype, hexact])
  -- eq2: SES  0 → ker f → F/range ψF → range f → 0
  have eq2 : Module.length A (F ⧸ LinearMap.range ψF)
      = Module.length A (LinearMap.ker f) + Module.length A (LinearMap.range f) :=
    Module.length_eq_add_of_exact (LinearMap.ker f).subtype f.rangeRestrict Subtype.coe_injective
      f.surjective_rangeRestrict
      (by rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_rangeRestrict])
  -- eq4: Lemma C on the finite-length quotient Q = M/F, applied to ψbar
  have eq4 : Module.length A (LinearMap.ker ψbar)
      = Module.length A ((M ⧸ F) ⧸ LinearMap.range ψbar) :=
    length_ker_eq_length_coker_finiteLength A (M ⧸ F) hQfin ψbar
  -- eq3: ker f ≅ ker ψbar  (the snake connecting iso), so equal length.
  have eq3 : Module.length A (LinearMap.ker f) = Module.length A (LinearMap.ker ψbar) := by
    -- G = preimage of F under ψ;  F ≤ G.
    set G := Submodule.comap ψ F with hGdef
    have hFG : F ≤ G := hψF
    -- θ : G →ₗ F  is ψ restricted (lands in F since G = comap ψ F).
    have hθmem : ∀ x ∈ G, ψ x ∈ F := fun x hx => hx
    set θ : G →ₗ[A] F := ψ.restrict hθmem with hθdef
    -- surjG : G →ₗ ker ψbar,  x ↦ [x]_F
    have hsg : ∀ x : G, F.mkQ (G.subtype x) ∈ LinearMap.ker ψbar := by
      intro x
      rw [LinearMap.mem_ker, hψbardef, Submodule.mkQ_apply, Submodule.mapQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact x.property
    set surjG : G →ₗ[A] (LinearMap.ker ψbar) :=
      LinearMap.codRestrict (LinearMap.ker ψbar) (F.mkQ ∘ₗ G.subtype) hsg with hsgdef
    -- θ' : G →ₗ ker f,  x ↦ [ψ x]_{range ψF}
    have htf : ∀ x : G, (LinearMap.range ψF).mkQ (θ x) ∈ LinearMap.ker f := by
      intro x
      rw [LinearMap.mem_ker, hfdef, Submodule.mkQ_apply, Submodule.mapQ_apply,
        Submodule.subtype_apply, Submodule.Quotient.mk_eq_zero]
      refine ⟨G.subtype x, ?_⟩
      rw [hθdef, Submodule.subtype_apply, LinearMap.coe_restrict_apply]
    set θ' : G →ₗ[A] (LinearMap.ker f) :=
      LinearMap.codRestrict (LinearMap.ker f) ((LinearMap.range ψF).mkQ ∘ₗ θ) htf with hθ'def
    -- surjG surjective
    have hsg_surj : Function.Surjective surjG := by
      rintro ⟨z, hz⟩
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective F z
      rw [LinearMap.mem_ker, hψbardef, Submodule.mkQ_apply, Submodule.mapQ_apply,
        Submodule.Quotient.mk_eq_zero] at hz
      refine ⟨⟨m, hz⟩, ?_⟩
      apply Subtype.ext
      simp only [hsgdef, LinearMap.codRestrict_apply, LinearMap.comp_apply,
        Submodule.subtype_apply, Submodule.mkQ_apply]
    -- θ' surjective
    have hθ'_surj : Function.Surjective θ' := by
      rintro ⟨z, hz⟩
      obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range ψF) z
      rw [LinearMap.mem_ker, hfdef, Submodule.mkQ_apply, Submodule.mapQ_apply,
        Submodule.subtype_apply, Submodule.Quotient.mk_eq_zero] at hz
      obtain ⟨m, hm⟩ := hz
      have hmG : m ∈ G := by rw [hGdef, Submodule.mem_comap, hm]; exact w.property
      refine ⟨⟨m, hmG⟩, ?_⟩
      apply Subtype.ext
      simp only [hθ'def, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.mkQ_apply]
      congr 1
      exact Subtype.ext (by rwa [hθdef, LinearMap.coe_restrict_apply])
    -- ker surjG = ker θ' = F restricted to G
    have hkereq : LinearMap.ker surjG = LinearMap.ker θ' := by
      ext x
      constructor
      · intro hx
        rw [LinearMap.mem_ker] at hx ⊢
        -- from hx : surjG x = 0 get ↑x ∈ F
        have hx0 : F.mkQ (G.subtype x) = 0 := by
          simpa [hsgdef, LinearMap.codRestrict_apply, LinearMap.comp_apply] using
            congrArg Subtype.val hx
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx0
        -- so ψ ↑x = ψ-image of an element of F, i.e. θ x ∈ range ψF
        apply Subtype.ext
        simp only [hθ'def, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
          ZeroMemClass.coe_zero]
        rw [Submodule.Quotient.mk_eq_zero]
        refine ⟨⟨G.subtype x, hx0⟩, ?_⟩
        apply Subtype.ext
        simp only [hθdef, hψFdef, LinearMap.coe_restrict_apply, Submodule.subtype_apply]
      · intro hx
        rw [LinearMap.mem_ker] at hx ⊢
        have hx0 : (LinearMap.range ψF).mkQ (θ x) = 0 := by
          simpa [hθ'def, LinearMap.codRestrict_apply, LinearMap.comp_apply] using
            congrArg Subtype.val hx
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx0
        obtain ⟨y, hy⟩ := hx0
        -- hy : ψF y = θ x, i.e. ψ ↑y = ψ ↑x, ψ inj ⟹ ↑x = ↑y ∈ F
        have hxF : (G.subtype x : M) ∈ F := by
          have h1 : ψ (G.subtype x) = ψ (y : M) := by
            simpa only [hθdef, hψFdef, LinearMap.coe_restrict_apply, Submodule.subtype_apply]
              using (congrArg Subtype.val hy).symm
          rw [hψinj h1]; exact y.property
        apply Subtype.ext
        simp only [hsgdef, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
          ZeroMemClass.coe_zero]
        rw [Submodule.Quotient.mk_eq_zero]
        exact hxF
    -- assemble via the two quotient-by-kernel equivalences
    have e1 := LinearMap.quotKerEquivOfSurjective surjG hsg_surj
    have e2 := LinearMap.quotKerEquivOfSurjective θ' hθ'_surj
    rw [← e2.length_eq, ← hkereq, e1.length_eq]
  -- Assemble step 2.
  have step2 : Module.length A (M ⧸ LinearMap.range ψ)
      = Module.length A (F ⧸ LinearMap.range ψF) := by
    rw [eq1, eq2, eq3, eq4, add_comm]
  rw [step2, ← step1]

/-- LEMMA A + assembly (Route γ).  Defect dévissage over a full-rank free submodule.  If `M` is
finite torsion-free over the `1`-dim Noetherian local domain `A`, `ψ : M →ₗ M` is injective with
`det (ψ.baseChange K) ≠ 0`, and `ψ` preserves a full-rank free submodule (equivalently the defect
splits over the SES `0 → F → M → Q → 0`), then `Δ(M,ψ) = 0`, i.e.
`ordInt A (det (ψ.baseChange K)) = (length_A (M ⧸ range ψ)).toNat`.

This bundles Lemma A (snake-lemma additivity of `Δ` over the SES, with block-triangular det
multiplicativity), Lemma B (matrix base case on `F`), and Lemma C (finite-length quotient `Q`).
It is the heaviest remaining analytic obligation; it is the defect-vanishing for a SINGLE
endomorphism that preserves a chosen full-rank free submodule. -/
@[ega "IV 21.10.17.3" "special case"]
theorem defect_devissage_free
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] [NoZeroSMulDivisors A M]
    (ψ : M →ₗ[A] M) (hψinj : Function.Injective ψ)
    (j : (Fin (Module.finrank K (TensorProduct A K M)) → A) →ₗ[A] M)
    (hjinj : Function.Injective j)
    (hjlen : Module.length A (M ⧸ LinearMap.range j) ≠ ⊤)
    (hpres : ∀ x, ψ (j x) ∈ LinearMap.range j)
    (hdet : LinearMap.det (ψ.baseChange K) ≠ 0) :
    ordInt A (LinearMap.det (ψ.baseChange K)) hdet =
      ((Module.length A (M ⧸ LinearMap.range ψ)).toNat : ℤ) := by
  classical
  -- Step 0: build the matrix `S : Aʳ → Aʳ` of `ψ` on the free submodule `range j`, via the
  -- universal property of the injective `j`: each `ψ (j eᵢ) ∈ range j` has a unique preimage.
  -- `S := j.comp⁻¹ (ψ ∘ₗ j)`; concretely choose preimages with `Classical.choice`/`hpres`.
  -- Use `LinearMap.range j ≅ (Fin r → A)` (j injective) to define S with `j ∘ₗ S = ψ ∘ₗ j`.
  have hSexists : ∃ S : (Fin (Module.finrank K (TensorProduct A K M)) → A) →ₗ[A]
      (Fin (Module.finrank K (TensorProduct A K M)) → A), ψ ∘ₗ j = j ∘ₗ S :=
    exists_matrix_of_preserves_range A M _ ψ j hjinj hpres
  obtain ⟨S, hS⟩ := hSexists
  -- Step 0 (det): det(ψ⊗K) = algebraMap A K (det S).
  have hdetS : LinearMap.det (ψ.baseChange K) = algebraMap A K (LinearMap.det S) :=
    det_baseChange_eq_algebraMap_det A K M ψ j hjinj S hS
  -- det S ≠ 0 (algebraMap injective on the domain A).
  have hSne : LinearMap.det S ≠ 0 := by
    intro h
    apply hdet
    rw [hdetS, h, map_zero]
  have hSneK : algebraMap A K (LinearMap.det S) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hSne
  -- Step 1 (matrix base case via the matrix `T := toMatrix' S`, `S = toLin' T`, `det S = det T`).
  set T := LinearMap.toMatrix' S with hT
  have hST : S = Matrix.toLin' T := by rw [hT, Matrix.toLin'_toMatrix']
  have hTdet : T.det = LinearMap.det S := by rw [hT, LinearMap.det_toMatrix']
  have hTne : T.det ≠ 0 := by rw [hTdet]; exact hSne
  have hTneK : algebraMap A K T.det ≠ 0 := by rw [hTdet]; exact hSneK
  -- matrix base case: ord(alg(det T)) = length(Aʳ/range(toLin' T)).toNat
  have hmbc :
      ordInt A (algebraMap A K T.det) hTneK =
        ((Module.length A ((Fin (Module.finrank K (TensorProduct A K M)) → A) ⧸
            LinearMap.range (Matrix.toLin' T))).toNat : ℤ) :=
    ordInt_matrix_det_eq_length_cokernel A K (Module.finrank K (TensorProduct A K M)) T hTne hTneK
  -- Step 2 (length side): length(M/range ψ) = length(Aʳ/range S) = length(Aʳ/range(toLin' T)).
  have hlen : Module.length A (M ⧸ LinearMap.range ψ) =
      Module.length A ((Fin (Module.finrank K (TensorProduct A K M)) → A) ⧸ LinearMap.range S) :=
    length_quot_range_eq_of_intertwine A K M ψ hψinj j hjinj hjlen S hS
  -- Assemble. Rewrite ordInt(det(ψ⊗K)) to ordInt(alg(det T)) via proof-irrelevant congruence.
  have ordA_congr : ∀ (x y : K) (hx : x ≠ 0) (hy : y ≠ 0), x = y →
      ordInt A x hx = ordInt A y hy := by
    intro x y hx hy h; subst h; rfl
  have e1 : ordInt A (LinearMap.det (ψ.baseChange K)) hdet =
      ordInt A (algebraMap A K T.det) hTneK :=
    ordA_congr _ _ _ _ (by rw [hdetS, hTdet])
  rw [e1, hmbc, hlen, hST]

/-- COMPOSITION ADDITIVITY (Route γ, the cokernel-length part of `comp`).  For injective
endomorphisms `f, g` of a finite torsion-free `A`-module `M`, both base-changing to
`K`-automorphisms
(so all three cokernels are torsion of finite length), the cokernel length is additive under
composition:
`length_A (M ⧸ range (g ∘ f)) = length_A (M ⧸ range f) + length_A (M ⧸ range g)`.
(Snake lemma `0 → coker f → coker (g∘f) → coker g → 0`; `Module.length_eq_add_of_exact`.)  The
`ord∘det` side is multiplicative by `LinearMap.det_comp` + `map_mul` + `ordInt_mul`, handled inline
in the kernel.  Compare the matrix analogue `matrix_cokerLen_mul`, already proven. -/
theorem cokerLen_comp_add
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] [NoZeroSMulDivisors A M]
    (f g : M →ₗ[A] M) (hg : Function.Injective g) :
    Module.length A (M ⧸ LinearMap.range (g ∘ₗ f)) =
      Module.length A (M ⧸ LinearMap.range f) + Module.length A (M ⧸ LinearMap.range g) := by
  -- Directly reuse the proven general helper with φ = g, ψ = f (only g-injectivity needed).
  exact matrix_cokerLen_mul_helper A M g f hg

/-- STEP 2 (Route γ).  Clearing scalar.  Given a full-rank free submodule `range j ⊆ M` (with `j`
the embedding from `exists_fullRank_free_submodule`) and any `A`-linear `φ : M →ₗ M`, there is a
nonzero `a ∈ A` such that `a • φ` carries `range j` into `range j`, i.e.
`∀ x, (a • φ) (j x) ∈ range j`.  (Each `φ (j x_i)` is a `K`-combination of the basis `j x_i` in
`M ⊗ K`; clear the finitely many denominators by a single nonzero `a ∈ A`; torsion-freeness pushes
the relation back into `M`.) -/
theorem exists_clearing_scalar
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] [NoZeroSMulDivisors A M]
    (j : (Fin (Module.finrank K (TensorProduct A K M)) → A) →ₗ[A] M)
    (hjinj : Function.Injective j)
    (hjlen : Module.length A (M ⧸ LinearMap.range j) ≠ ⊤)
    (φ : M →ₗ[A] M) :
    ∃ a : A, a ≠ 0 ∧ ∀ x, (a • φ) (j x) ∈ LinearMap.range j := by
  set R := LinearMap.range j with hRdef
  have hQfl : IsFiniteLength A (M ⧸ R) := Module.length_ne_top_iff.mp hjlen
  by_cases hf : IsField A
  · -- Field case: `range j` is a full-rank subspace of the finite-dimensional `A`-space `M`,
    -- so `range j = ⊤` and any scalar (e.g. `a = 1`) works.
    refine ⟨1, one_ne_zero, fun x => ?_⟩
    have htop : R = ⊤ := by
      let : Field A := hf.toField
      have : Module.Free A M := inferInstance
      have : FiniteDimensional A M := inferInstance
      have hn : Module.finrank K (TensorProduct A K M) = Module.finrank A M :=
        Module.finrank_baseChange
      have hdom : Module.finrank A (Fin (Module.finrank K (TensorProduct A K M)) → A)
          = Module.finrank A M := by
        rw [Module.finrank_fin_fun, hn]
      rw [hRdef, LinearMap.range_eq_top]
      exact (LinearMap.linearEquivOfInjective j hjinj hdom).surjective
    rw [htop]; exact Submodule.mem_top
  · -- Non-field case: `Q := M ⧸ range j` has finite length over the `1`-dimensional Noetherian
    -- local domain `A`, hence is torsion: each element is killed by a nonzero `a ∈ A` (otherwise a
    -- copy of `A` would have finite length, forcing `A` Artinian, hence a field — contradiction).
    set g : (Fin (Module.finrank K (TensorProduct A K M)) → A) →ₗ[A] (M ⧸ R) :=
      R.mkQ ∘ₗ φ ∘ₗ j with hgdef
    have key : ∀ y : (M ⧸ R), ∃ a : A, a ≠ 0 ∧ a • y = 0 := by
      intro y
      by_contra h
      push Not at h
      have hker : (LinearMap.toSpanSingleton A (M ⧸ R) y).ker = ⊥ := by
        rw [LinearMap.ker_eq_bot']
        intro a ha; by_contra hne; exact h a hne ha
      have hinj : Function.Injective (LinearMap.toSpanSingleton A (M ⧸ R) y) := by
        rw [← LinearMap.ker_eq_bot]; exact hker
      have hfl : IsFiniteLength A A := by
        have hle : Module.length A A ≤ Module.length A (M ⧸ R) :=
          Module.length_le_of_injective _ hinj
        rw [← Module.length_ne_top_iff] at hQfl ⊢
        intro htop; rw [htop] at hle; exact hQfl (top_le_iff.mp hle)
      have : IsArtinianRing A := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).right
      exact hf (IsArtinianRing.isField_of_isDomain A)
    -- Choose a nonzero annihilator `c i` for each generator `g eᵢ` and take their product `a`.
    choose c hc0 hc using fun i => key (g (Pi.single i 1))
    set a : A := ∏ i, c i with hadef
    have ha0 : a ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hc0 i)
    have hgen : ∀ i, a • g (Pi.single i 1) = 0 := by
      intro i
      rw [hadef, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul, hc i, smul_zero]
    -- `x ↦ a • g x` is `A`-linear and vanishes on the standard basis, hence is identically zero.
    have hzero : ∀ x, a • g x = 0 := by
      have hlin : (a • g) = 0 := by
        apply (Pi.basisFun A (Fin (Module.finrank K (TensorProduct A K M)))).ext
        intro i
        simp only [LinearMap.smul_apply, Pi.basisFun_apply, LinearMap.zero_apply]
        exact hgen i
      intro x
      have := LinearMap.congr_fun hlin x
      simpa using this
    refine ⟨a, ha0, fun x => ?_⟩
    have hx : a • g x = 0 := hzero x
    rw [hgdef] at hx
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hx ⊢
    rw [← map_smul] at hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    exact hx

/-- DET HELPER (Route γ).  The `K`-base change of `a • φ` has determinant
`a ^ r · det (φ.baseChange K)` where `r = finrank K (M ⊗ K)`.  (`(a•φ).baseChange K =
(algebraMap A K a) • (φ.baseChange K)`, and `det (c • L) = c ^ (finrank) · det L` for an
endomorphism
`L` of a `finrank`-dimensional space.)  Used in the kernel assembly. -/
@[ega "II 6.4.9" "special case"]
theorem det_baseChange_smul
    (A : Type*) [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a : A) (φ : M →ₗ[A] M) :
    LinearMap.det ((a • φ).baseChange K) =
      (algebraMap A K a) ^ (Module.finrank K (TensorProduct A K M)) *
        LinearMap.det (φ.baseChange K) := by
  have h : (a • φ).baseChange K = (algebraMap A K a) • (φ.baseChange K) := by
    rw [LinearMap.baseChange_smul, algebraMap_smul]
  rw [h, LinearMap.det_smul]

/-- SCALAR IDENTITY (Route γ).  For multiplication-by-`a` (`a ≠ 0`) on a finite torsion-free module
`M` over a 1-dim Noetherian local domain `A`, the cokernel length equals `r · ord_A(a)` where
`r = finrank K (M ⊗ K)`. -/
@[ega "IV 21.10.13" "special case"]
theorem length_quot_smul_eq_rank_mul_ord
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] [NoZeroSMulDivisors A M]
    (a : A) (ha : a ≠ 0) (haK : algebraMap A K a ≠ 0) :
    ((Module.length A (M ⧸ LinearMap.range (LinearMap.lsmul A M a))).toNat : ℤ) =
      (Module.finrank K (TensorProduct A K M) : ℤ) * ordInt A (algebraMap A K a) haK := by
  -- cusp k[[t²,t³]] match)
  classical
  -- Proof-irrelevance helper for `ordInt` in its nonzero-witness argument, plus value congruence.
  have ordA_congr : ∀ (x y : K) (hx : x ≠ 0) (hy : y ≠ 0), x = y →
      ordInt A x hx = ordInt A y hy := by
    intro x y hx hy h; subst h; rfl
  set r := Module.finrank K (TensorProduct A K M) with hr
  -- Step 1: full-rank free submodule.
  obtain ⟨j, hjinj, hjlen⟩ := exists_fullRank_free_submodule A K M
  -- abbreviation: ψ = multiplication-by-a on M.
  set ψ : M →ₗ[A] M := LinearMap.lsmul A M a with hψ
  -- `ψ = a • id`
  have hψsmul : ψ = a • (LinearMap.id : M →ₗ[A] M) := by
    ext x; simp [hψ, LinearMap.lsmul_apply]
  -- `ψ` injective (torsion-free, `a ≠ 0`)
  have hψinj : Function.Injective ψ := by
    intro x y h
    simp only [hψ, LinearMap.lsmul_apply] at h
    exact smul_right_injective M ha h
  -- `ψ` preserves `range j`
  have hpres : ∀ x, ψ (j x) ∈ LinearMap.range j := by
    intro x
    have : ψ (j x) = j (a • x) := by
      simp [hψ, LinearMap.lsmul_apply, map_smul]
    rw [this]
    exact LinearMap.mem_range_self j (a • x)
  -- determinant of base change of `ψ = a • id`
  have hdetψeq : LinearMap.det (ψ.baseChange K) = (algebraMap A K a) ^ r := by
    rw [hψsmul, det_baseChange_smul A K M a (LinearMap.id : M →ₗ[A] M)]
    have : LinearMap.det ((LinearMap.id : M →ₗ[A] M).baseChange K) = 1 := by
      rw [LinearMap.baseChange_id]; exact LinearMap.det_id
    rw [this, mul_one]
  have hdetψ : LinearMap.det (ψ.baseChange K) ≠ 0 := by
    rw [hdetψeq]; exact pow_ne_zero _ haK
  -- Step 3: defect dévissage for `ψ`.
  have hdev :
      ordInt A (LinearMap.det (ψ.baseChange K)) hdetψ =
        ((Module.length A (M ⧸ LinearMap.range ψ)).toNat : ℤ) :=
    defect_devissage_free A K M ψ hψinj j hjinj hjlen hpres hdetψ
  -- ord of a power: `ordInt A (x^k) = k * ordInt A x`.
  have hpow : ∀ k : ℕ, ∀ (h : (algebraMap A K a) ^ k ≠ 0),
      ordInt A ((algebraMap A K a) ^ k) h = (k : ℤ) * ordInt A (algebraMap A K a) haK := by
    intro k
    induction k with
    | zero =>
        intro h
        simp only [Nat.cast_zero, zero_mul]
        have h1 : ordInt A ((algebraMap A K a) ^ 0) h = ordInt A (1 : K) (by norm_num) :=
          ordA_congr _ _ _ _ (by rw [pow_zero])
        rw [h1]
        have hval : ordInt A ((1 : K) * 1) (by norm_num : (1 : K) * 1 ≠ 0) =
            ordInt A (1 : K) (by norm_num) + ordInt A (1 : K) (by norm_num) :=
          ordInt_mul A (1 : K) (1 : K) (by norm_num) (by norm_num)
        simp only [mul_one] at hval
        omega
    | succ n ih =>
        intro h
        have hpn : (algebraMap A K a) ^ n ≠ 0 := pow_ne_zero _ haK
        have hsplit :
            ordInt A ((algebraMap A K a) ^ n * algebraMap A K a)
              (mul_ne_zero hpn haK) =
              ordInt A ((algebraMap A K a) ^ n) hpn +
                ordInt A (algebraMap A K a) haK :=
          ordInt_mul A _ _ hpn haK
        have hcong : ordInt A ((algebraMap A K a) ^ (n + 1)) h =
            ordInt A ((algebraMap A K a) ^ n * algebraMap A K a) (mul_ne_zero hpn haK) :=
          ordA_congr _ _ _ _ (by rw [pow_succ])
        rw [hcong, hsplit, ih hpn]
        push_cast
        ring
  -- Assemble: ordInt(det ψ⊗K) = ordInt((alg a)^r) = r * ordInt(alg a) = length.
  have hpowne : (algebraMap A K a) ^ r ≠ 0 := pow_ne_zero _ haK
  have e1 : ordInt A (LinearMap.det (ψ.baseChange K)) hdetψ =
      ordInt A ((algebraMap A K a) ^ r) hpowne :=
    ordA_congr _ _ _ _ hdetψeq
  rw [hdev] at e1
  rw [e1, hpow r hpowne]

/-- If the `K`-base change of `φ : M →ₗ M`, for a finite `A`-module `M`, has
nonzero determinant — equivalently `φ.baseChange K` is a `K`-automorphism — then the cokernel
`M ⧸ range φ` has finite `A`-length.  (`(M ⧸ range φ) ⊗ K = coker (φ.baseChange K) = 0` since the
base change is onto; a finite `A`-module killed by `⊗ K` is torsion, supported on `{𝔪}`, hence of
finite length over the 1-dim Noetherian local ring `A`.) -/
@[ega "IV 21.10.13" "(i)"]
theorem cokerLen_ne_top_of_baseChangeDet_ne_zero
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (φ : M →ₗ[A] M) (hdet : LinearMap.det (φ.baseChange K) ≠ 0) :
    Module.length A (M ⧸ LinearMap.range φ) ≠ ⊤ := by
  classical
  have : FiniteDimensional K (TensorProduct A K M) := inferInstance
  -- Surjectivity of `φ.baseChange K` (nonzero det ⟹ unit ⟹ bijective on a fin-dim space).
  have hsurj : Function.Surjective (φ.baseChange K) := by
    have hd : IsUnit (LinearMap.det (φ.baseChange K)) := isUnit_iff_ne_zero.mpr hdet
    have hu : IsUnit (φ.baseChange K) := (LinearMap.isUnit_iff_isUnit_det _).mpr hd
    obtain ⟨u, hu⟩ := hu
    intro v
    refine ⟨u.inv v, ?_⟩
    have h2 : (↑u : TensorProduct A K M →ₗ[K] TensorProduct A K M) (u.inv v) = v := by
      calc (↑u : TensorProduct A K M →ₗ[K] TensorProduct A K M) (u.inv v)
            = (↑u * u.inv) v := rfl
        _ = v := by rw [u.val_inv]; rfl
    rw [hu] at h2; exact h2
  -- Tensoring the exact sequence `M --φ--> M --mkQ--> N → 0` with `K` (right-exactness).
  have hexact : Function.Exact φ (LinearMap.range φ).mkQ := by
    rw [LinearMap.exact_iff, Submodule.ker_mkQ]
  have hsmkQ : Function.Surjective (LinearMap.range φ).mkQ := Submodule.mkQ_surjective _
  have hTexact := lTensor_exact K hexact hsmkQ
  have hTsurj : Function.Surjective (LinearMap.lTensor K (LinearMap.range φ).mkQ) :=
    LinearMap.lTensor_surjective K hsmkQ
  have hsurjT : Function.Surjective (LinearMap.lTensor K φ) := by
    rw [← LinearMap.baseChange_eq_lTensor]; exact hsurj
  -- `lTensor K mkQ = 0` (its kernel is `range (lTensor K φ) = ⊤`), and it is surjective, so
  -- `K ⊗ N = 0`.
  have hKN : ∀ z : TensorProduct A K (M ⧸ LinearMap.range φ), z = 0 := by
    intro z
    obtain ⟨y, rfl⟩ := hTsurj z
    rw [hTexact y]; exact hsurjT y
  -- Hence `N = M ⧸ range φ` is torsion: each element is killed by a nonzero scalar.
  have htorQ : ∀ q : M ⧸ LinearMap.range φ, ∃ a : A, a ≠ 0 ∧ a • q = 0 := by
    intro q
    set ιN : (M ⧸ LinearMap.range φ) →ₗ[A] TensorProduct A K (M ⧸ LinearMap.range φ) :=
      (TensorProduct.mk A K (M ⧸ LinearMap.range φ)) 1 with hιdef
    have : IsLocalizedModule (nonZeroDivisors A) ιN := by
      rw [hιdef, isLocalizedModule_iff_isBaseChange (nonZeroDivisors A) K]
      exact TensorProduct.isBaseChange A (M ⧸ LinearMap.range φ) K
    have h0 : ιN q = 0 := hKN _
    rw [IsLocalizedModule.eq_zero_iff (nonZeroDivisors A)] at h0
    obtain ⟨s, hs⟩ := h0
    exact ⟨(s : A), nonZeroDivisors.ne_zero s.property, hs⟩
  -- Artinian helper: `A/(a)` is Artinian for `a ≠ 0` (`dim A/(a) ≤ dim A - 1 = 0`).
  have hArt : ∀ (a : A), a ≠ 0 → IsArtinianRing (A ⧸ Ideal.span {a}) := by
    intro a ha
    rw [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
    refine ⟨inferInstance, ?_⟩
    rw [Ring.krullDimLE_iff]
    have hmem : a ∈ nonZeroDivisors A := mem_nonZeroDivisors_of_ne_zero ha
    have hq := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hmem
    have hA : ringKrullDim A ≤ ((1:ℕ):WithBot ℕ∞) := Ring.krullDimLE_iff.mp inferInstance
    have h : ringKrullDim (A ⧸ Ideal.span {a}) + 1 ≤ ((1:ℕ):WithBot ℕ∞) := le_trans hq hA
    set d := ringKrullDim (A ⧸ Ideal.span {a}) with hd
    have h' : d + 1 ≤ ((1:ℕ∞):WithBot ℕ∞) := by rw [← WithBot.coe_natCast] at h; exact_mod_cast h
    change d ≤ ((0:ℕ):WithBot ℕ∞)
    rw [show ((0:ℕ):WithBot ℕ∞) = ((0:ℕ∞):WithBot ℕ∞) by norm_cast]
    rw [WithBot.le_coe_iff]
    intro a' hda
    rw [hda] at h'
    have h2 : a' + 1 ≤ 1 := by exact_mod_cast h'
    cases a' with
    | top => simp at h2
    | coe n =>
      rw [← ENat.natCast_one, ← ENat.natCast_add, ENat.natCast_le_natCast] at h2
      have : n = 0 := by omega
      subst this; simp
  -- `N` is finitely generated and torsion, hence annihilated by a single nonzero `a`.
  obtain ⟨a, ha0, hann⟩ : ∃ a : A, a ≠ 0 ∧ ∀ q : M ⧸ LinearMap.range φ, a • q = 0 := by
    obtain ⟨s, hs⟩ := (Module.finite_def.mp (by infer_instance) :
      (⊤ : Submodule A (M ⧸ LinearMap.range φ)).FG)
    choose f hf0 hf using htorQ
    set a : A := ∏ g ∈ s, f g with ha
    have ha0 : a ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun g _ => hf0 g)
    refine ⟨a, ha0, ?_⟩
    have hgen : ∀ g ∈ s, a • g = 0 := by
      intro g hg
      rw [ha, ← Finset.prod_erase_mul _ _ hg, mul_smul, hf g, smul_zero]
    intro q
    have hq : q ∈ (⊤ : Submodule A (M ⧸ LinearMap.range φ)) := Submodule.mem_top
    rw [← hs] at hq
    induction hq using Submodule.span_induction with
    | mem y hy => exact hgen y hy
    | zero => exact smul_zero a
    | add y z _ _ hy hz => rw [smul_add, hy, hz, add_zero]
    | smul c y _ hy => rw [smul_comm, hy, smul_zero]
  -- `N` is a finite module over the Artinian ring `A/(a)`, hence Artinian over `A`.
  have hArtQ : IsArtinian A (M ⧸ LinearMap.range φ) := by
    set I : Ideal A := Ideal.span {a} with hI
    have htor : Module.IsTorsionBySet A (M ⧸ LinearMap.range φ) (I : Set A) := by
      intro q r
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp r.property
      rw [← hc, mul_smul, hann]; simp
    let : Module (A ⧸ I) (M ⧸ LinearMap.range φ) := htor.module
    have : IsScalarTower A (A ⧸ I) (M ⧸ LinearMap.range φ) := htor.isScalarTower
    have : Module.Finite (A ⧸ I) (M ⧸ LinearMap.range φ) :=
      Module.Finite.of_restrictScalars_finite A (A ⧸ I) (M ⧸ LinearMap.range φ)
    have : IsArtinianRing (A ⧸ I) := hArt a ha0
    have : IsArtinian (A ⧸ I) (M ⧸ LinearMap.range φ) := isArtinian_of_fg_of_artinian'
    exact isArtinian_of_surjective_algebraMap (S := A) (R := A ⧸ I)
      (M := M ⧸ LinearMap.range φ) Ideal.Quotient.mk_surjective
  -- Noetherian + Artinian = finite length, so the length is not `⊤`.
  rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨inferInstance, hArtQ⟩

/-- KERNEL (Stacks Tag 02QH).  For a finite **torsion-free** `A`-module `M` over a `1`-dimensional
Noetherian local domain `A` with fraction field `K`, and an INJECTIVE `A`-linear endomorphism `φ`
of `M` whose base change to `K` has nonzero determinant, the order of vanishing of that determinant
equals the `A`-length of the cokernel `M ⧸ range φ`.

This is the genuine analytic content of Stacks 02MI.  Carries `[NoZeroSMulDivisors A M]`
(torsion-free `M`); the use site `M = B` (a domain over `A`) supplies it.

*Proof.* Pick a full-rank free submodule
`F ≅ Aʳ ⊆ M` with finite-length quotient (`exists_fullRank_free_submodule`).  `φ` need not preserve
`F`, but a scalar multiple `ψ = a·φ = μ_a ∘ φ` (`a ≠ 0`) does; then `Δ(M,ψ) = 0`
(`defect_devissage_free`: snake additivity over `0→F→M→Q→0`, matrix base case on `F`, finite-length
on `Q`).  Undo the scalar via the scalar identity `Δ(M, μ_a) = 0`
(`length_quot_smul_eq_rank_mul_ord`) and the composition additivity `Δ(M, μ_a ∘ φ) = Δ(M, μ_a) +
Δ(M, φ)` (`defect_comp`), giving `Δ(M,φ) = 0`. -/
@[ega "IV 21.10.17.3" "special case"]
theorem ordInt_baseChangeDet_eq_length_cokernel
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] [NoZeroSMulDivisors A M]
    (φ : M →ₗ[A] M)
    (hφinj : Function.Injective φ)
    (hdet : LinearMap.det (φ.baseChange K) ≠ 0) :
    ordInt A (LinearMap.det (φ.baseChange K)) hdet =
      ((Module.length A (M ⧸ LinearMap.range φ)).toNat : ℤ) := by
  classical
  -- Proof-irrelevance helper for `ordInt` in its nonzero-witness argument, plus value congruence.
  have ordA_congr : ∀ (x y : K) (hx : x ≠ 0) (hy : y ≠ 0), x = y →
      ordInt A x hx = ordInt A y hy := by
    intro x y hx hy h; subst h; rfl
  set r := Module.finrank K (TensorProduct A K M) with hr
  -- Step 1: full-rank free submodule.
  obtain ⟨j, hjinj, hjlen⟩ := exists_fullRank_free_submodule A K M
  -- Step 2: clearing scalar.
  obtain ⟨a, ha, hpres⟩ := exists_clearing_scalar A K M j hjinj hjlen φ
  -- abbreviations
  set μ : M →ₗ[A] M := LinearMap.lsmul A M a with hμ
  -- `a • φ = μ ∘ₗ φ`
  have hψeq : a • φ = μ ∘ₗ φ := by
    ext x; simp [hμ, LinearMap.lsmul_apply]
  -- `μ` injective (torsion-free, `a ≠ 0`)
  have hμinj : Function.Injective μ := by
    intro x y h
    simp only [hμ, LinearMap.lsmul_apply] at h
    exact smul_right_injective M ha h
  -- `ψ := a • φ` injective
  have hψinj : Function.Injective (a • φ) := by
    rw [hψeq]; exact hμinj.comp hφinj
  -- `algebraMap A K a ≠ 0`
  have haK : algebraMap A K a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ha
  -- determinant of base change of `a • φ`
  have hdetsmul : LinearMap.det ((a • φ).baseChange K) =
      (algebraMap A K a) ^ r * LinearMap.det (φ.baseChange K) :=
    det_baseChange_smul A K M a φ
  -- nonzero determinant of `(a•φ).baseChange K`
  have hdetψ : LinearMap.det ((a • φ).baseChange K) ≠ 0 := by
    rw [hdetsmul]
    exact mul_ne_zero (pow_ne_zero _ haK) hdet
  -- determinant of base change of `μ` (= scalar `a • id`)
  have hμsmul : μ = a • (LinearMap.id : M →ₗ[A] M) := by
    ext x; simp [hμ, LinearMap.lsmul_apply]
  have hdetμeq : LinearMap.det (μ.baseChange K) = (algebraMap A K a) ^ r := by
    rw [hμsmul, det_baseChange_smul A K M a (LinearMap.id : M →ₗ[A] M)]
    have : LinearMap.det ((LinearMap.id : M →ₗ[A] M).baseChange K) = 1 := by
      rw [LinearMap.baseChange_id]; exact LinearMap.det_id
    rw [this, mul_one]
  have hdetμ : LinearMap.det (μ.baseChange K) ≠ 0 := by
    rw [hdetμeq]; exact pow_ne_zero _ haK
  -- Step 3: defect dévissage for `ψ = a • φ`.
  have hdev :
      ordInt A (LinearMap.det ((a • φ).baseChange K)) hdetψ =
        ((Module.length A (M ⧸ LinearMap.range (a • φ))).toNat : ℤ) :=
    defect_devissage_free A K M (a • φ) hψinj j hjinj hjlen hpres hdetψ
  -- finiteness of cokernels
  have hcfφ : Module.length A (M ⧸ LinearMap.range φ) ≠ ⊤ :=
    cokerLen_ne_top_of_baseChangeDet_ne_zero A K M φ hdet
  have hcfμ : Module.length A (M ⧸ LinearMap.range μ) ≠ ⊤ :=
    cokerLen_ne_top_of_baseChangeDet_ne_zero A K M μ hdetμ
  -- Step 8: composition additivity of cokernel length, in ℕ∞.
  have hcomp :
      Module.length A (M ⧸ LinearMap.range (a • φ)) =
        Module.length A (M ⧸ LinearMap.range φ) +
          Module.length A (M ⧸ LinearMap.range μ) := by
    rw [hψeq]
    exact cokerLen_comp_add A M φ μ hμinj
  -- Step 9: `.toNat` is additive on the two finite summands.
  have htoNat :
      (Module.length A (M ⧸ LinearMap.range (a • φ))).toNat =
        (Module.length A (M ⧸ LinearMap.range φ)).toNat +
          (Module.length A (M ⧸ LinearMap.range μ)).toNat := by
    rw [hcomp, ENat.toNat_add hcfφ hcfμ]
  -- Step 11: scalar identity gives the length of `M ⧸ range μ`.
  have hscalar :
      ((Module.length A (M ⧸ LinearMap.range μ)).toNat : ℤ) =
        (r : ℤ) * ordInt A (algebraMap A K a) haK :=
    length_quot_smul_eq_rank_mul_ord A K M a ha haK
  -- ord of a power: `ordInt A (x^k) = k * ordInt A x`.
  have hpow : ∀ k : ℕ, ∀ (h : (algebraMap A K a) ^ k ≠ 0),
      ordInt A ((algebraMap A K a) ^ k) h = (k : ℤ) * ordInt A (algebraMap A K a) haK := by
    intro k
    induction k with
    | zero =>
        intro h
        simp only [Nat.cast_zero, zero_mul]
        have h1 : ordInt A ((algebraMap A K a) ^ 0) h = ordInt A (1 : K) (by norm_num) :=
          ordA_congr _ _ _ _ (by rw [pow_zero])
        rw [h1]
        have hval : ordInt A ((1 : K) * 1) (by norm_num : (1 : K) * 1 ≠ 0) =
            ordInt A (1 : K) (by norm_num) + ordInt A (1 : K) (by norm_num) :=
          ordInt_mul A (1 : K) (1 : K) (by norm_num) (by norm_num)
        simp only [mul_one] at hval
        omega
    | succ n ih =>
        intro h
        have hpn : (algebraMap A K a) ^ n ≠ 0 := pow_ne_zero _ haK
        have hsplit :
            ordInt A ((algebraMap A K a) ^ n * algebraMap A K a)
              (mul_ne_zero hpn haK) =
              ordInt A ((algebraMap A K a) ^ n) hpn +
                ordInt A (algebraMap A K a) haK :=
          ordInt_mul A _ _ hpn haK
        have hcong : ordInt A ((algebraMap A K a) ^ (n + 1)) h =
            ordInt A ((algebraMap A K a) ^ n * algebraMap A K a) (mul_ne_zero hpn haK) :=
          ordA_congr _ _ _ _ (by rw [pow_succ])
        rw [hcong, hsplit, ih hpn]
        push_cast
        ring
  -- Step 10: ord of `det (ψ.baseChange K)` splits via `det_baseChange_smul` + `ordInt_mul`.
  have hordψ :
      ordInt A (LinearMap.det ((a • φ).baseChange K)) hdetψ =
        (r : ℤ) * ordInt A (algebraMap A K a) haK +
          ordInt A (LinearMap.det (φ.baseChange K)) hdet := by
    have hpowne : (algebraMap A K a) ^ r ≠ 0 := pow_ne_zero _ haK
    -- rewrite the value inside ordInt via congruence (proof-irrelevant witness)
    have e1 : ordInt A (LinearMap.det ((a • φ).baseChange K)) hdetψ =
        ordInt A ((algebraMap A K a) ^ r * LinearMap.det (φ.baseChange K))
          (mul_ne_zero hpowne hdet) :=
      ordA_congr _ _ _ _ hdetsmul
    rw [e1, ordInt_mul A _ _ hpowne hdet, hpow r hpowne]
  -- Assemble.
  -- From hdev + hordψ : r*c + D = (length (M ⧸ range (a•φ))).toNat
  -- From htoNat + hscalar : (length (M ⧸ range (a•φ))).toNat = Lφ + r*c
  have key1 :
      (r : ℤ) * ordInt A (algebraMap A K a) haK +
          ordInt A (LinearMap.det (φ.baseChange K)) hdet =
        ((Module.length A (M ⧸ LinearMap.range (a • φ))).toNat : ℤ) := by
    rw [← hordψ, hdev]
  have key2 :
      ((Module.length A (M ⧸ LinearMap.range (a • φ))).toNat : ℤ) =
        ((Module.length A (M ⧸ LinearMap.range φ)).toNat : ℤ) +
          (r : ℤ) * ordInt A (algebraMap A K a) haK := by
    rw [htoNat]
    push_cast
    rw [hscalar]
  rw [key2] at key1
  -- key1 : r*c + D = Lφ + r*c
  linarith [key1]

/-- BRIDGE.  The determinant of the `K`-base change of `A`-linear multiplication-by-`b` on `B`
equals the field norm `Nm_{L/K}(algebraMap B L b)`.

Uses the canonical `K`-algebra isomorphism `B ⊗[A] K ≅ L` (`B` is finite over `A`, `L = Frac B`,
`K = Frac A`), under which `(lmul_A b).baseChange K` corresponds to multiplication-by-`b` on `L`
as a `K`-vector space, whose `K`-determinant is by definition `Algebra.norm K`.  Candidate hooks:
`IsLocalization` / `FractionRing` tensor-product identification, `Algebra.norm` as `LinearMap.det`
of `lmul`, `LinearMap.det_baseChange` / `LinearMap.baseChange` naturality.  Its own subtask. -/
theorem baseChangeDet_lmul_eq_norm
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B]
    (K L : Type*) [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    (b : B) :
    LinearMap.det ((Algebra.lmul A B b).baseChange K) = Algebra.norm K (algebraMap B L b) := by
  -- once FiniteDimensional K L, which is forced by Module.Finite A B + L=Frac B/K=Frac A).
  classical
  -- B is integral over A (module-finite), hence the image of A∖{0} lies in B∖{0} and every
  -- nonzero element of B divides a nonzero element of A; so inverting A∖{0} in B yields L.
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have : Algebra.IsAlgebraic A B := Algebra.IsIntegral.isAlgebraic
  -- `A → B` is injective: A is a domain and B is a nonzero A-algebra (a domain), and any
  -- finite faithful... actually we get it from `NoZeroSMulDivisors`/integrality is not needed;
  -- use that nonzero divisors map to nonzero divisors via algebra being injective on Frac data.
  have hAB : Function.Injective (algebraMap A B) := by
    have h1 : Function.Injective (algebraMap A L) :=
      (IsScalarTower.algebraMap_eq A K L ▸ (FaithfulSMul.algebraMap_injective K L).comp
        (IsFractionRing.injective A K))
    have h2 : (algebraMap A L) = (algebraMap B L).comp (algebraMap A B) :=
      IsScalarTower.algebraMap_eq A B L
    intro x y hxy
    apply h1
    rw [h2]
    simp only [RingHom.comp_apply]
    rw [hxy]
  have hMN : Algebra.algebraMapSubmonoid B (nonZeroDivisors A) ≤ nonZeroDivisors B := by
    rintro x ⟨a, ha, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    have : a ≠ 0 := nonZeroDivisors.ne_zero ha
    rw [ne_eq, ← (algebraMap A B).map_zero]
    exact fun h => this (hAB h)
  have hdvd : ∀ n ∈ nonZeroDivisors B,
      ∃ m ∈ Algebra.algebraMapSubmonoid B (nonZeroDivisors A), n ∣ m := by
    intro n hn
    obtain ⟨c, d, hd, hdc⟩ :=
      Algebra.IsAlgebraic.exists_smul_eq_mul A (1 : B) (b := n) (nonZeroDivisors.ne_zero hn)
    refine ⟨algebraMap A B d, ?_, ?_⟩
    · rw [Algebra.algebraMapSubmonoid, Submonoid.mem_map]
      exact ⟨d, mem_nonZeroDivisors_of_ne_zero hd, rfl⟩
    · rw [Algebra.smul_def, mul_one] at hdc
      exact ⟨c, hdc⟩
  have hLocB : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L :=
    (IsLocalization.iff_of_le_of_exists_dvd (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))
      (nonZeroDivisors B) hMN hdvd).mpr inferInstance
  -- L is the localization of the A-module B at A∖{0}.
  have hLM : IsLocalizedModule (nonZeroDivisors A)
      (IsScalarTower.toAlgHom A B L).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr hLocB
  -- Base change: K ⊗[A] B ≃ₗ[K] L.
  have hbc : IsBaseChange K (IsScalarTower.toAlgHom A B L).toLinearMap :=
    IsLocalizedModule.isBaseChange (nonZeroDivisors A) K (IsScalarTower.toAlgHom A B L).toLinearMap
  set e : (TensorProduct A K B) ≃ₗ[K] L := hbc.equiv with he
  -- The conjugation identity: e ∘ (lmul b).baseChange = (lmul (algMap b)) ∘ e.
  have hconj : (Algebra.lmul A B b).baseChange K
      = (e.symm : L →ₗ[K] (TensorProduct A K B)) ∘ₗ
          (Algebra.lmul K L (algebraMap B L b)) ∘ₗ (e : (TensorProduct A K B) →ₗ[K] L) := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext k
    simp only [ TensorProduct.AlgebraTensorModule.curry_apply,
      TensorProduct.curry_apply, LinearMap.coe_restrictScalars, LinearMap.baseChange_tmul,
      LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, he]
    rw [LinearEquiv.eq_symm_apply, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul]
    simp only [one_smul, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom']
    change algebraMap B L ((Algebra.lmul A B b) k) = (Algebra.lmul K L (algebraMap B L b))
        (algebraMap B L k)
    have h1 : (Algebra.lmul A B b) k = b * k := by simp [Algebra.lmul]
    have h2 : (Algebra.lmul K L (algebraMap B L b)) (algebraMap B L k)
        = algebraMap B L b * algebraMap B L k := by simp [Algebra.lmul]
    rw [h1, h2, map_mul]
  rw [Algebra.norm_apply, hconj]
  have := LinearMap.det_conj (Algebra.lmul K L (algebraMap B L b)) e.symm
  simp only [LinearEquiv.symm_symm] at this
  rw [this]

/-- The order of vanishing of the norm of `b` equals the length of `B ⧸ bB` over `A`. -/
theorem ordInt_norm_eq_length_quotient
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B]
    [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
    (K L : Type*) [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    (hAB : Function.Injective (algebraMap A B))
    (b : B) (hb : b ≠ 0)
    (hx0 : Algebra.norm K (algebraMap B L b) ≠ 0) :
    ordInt A (Algebra.norm K (algebraMap B L b)) hx0 =
      ((Module.length A (B ⧸ Ideal.span {b})).toNat : ℤ) := by
  -- Reduce to the 02QH kernel with M = B, φ = A-linear multiplication-by-b.
  -- ordInt is proof-irrelevant in its nonzero proof; transport along equalities of values.
  have ordA_congr : ∀ (a a' : K) (ha : a ≠ 0) (ha' : a' ≠ 0),
      a = a' → ordInt A a ha = ordInt A a' ha' := by
    intro a a' ha ha' h; subst h; rfl
  set φ : B →ₗ[A] B := Algebra.lmul A B b with hφ
  -- BRIDGE 1 (det = norm): cited as `baseChangeDet_lmul_eq_norm`.
  have hbridgeDet : LinearMap.det (φ.baseChange K) = Algebra.norm K (algebraMap B L b) :=
    baseChangeDet_lmul_eq_norm A B K L b
  -- BRIDGE 2 (cokernel = B/bB): range of multiplication-by-b is the ideal span {b} (PROVEN).
  have hbridgeCoker :
      Module.length A (B ⧸ LinearMap.range φ) = Module.length A (B ⧸ Ideal.span {b}) := by
    have hrange : LinearMap.range φ = (Ideal.span {b}).restrictScalars A := by
      ext x
      simp only [hφ, LinearMap.mem_range, Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
      constructor <;> rintro ⟨y, rfl⟩ <;> exact ⟨y, by simp [Algebra.lmul]⟩
    rw [hrange]
    rfl
  -- Combine via the 02QH kernel.
  have hdet : LinearMap.det (φ.baseChange K) ≠ 0 := by rwa [hbridgeDet]
  have hφinj : Function.Injective φ := by
    rw [hφ]
    exact fun u v huv => mul_left_cancel₀ hb (by simpa [Algebra.lmul] using huv)
  have : NoZeroSMulDivisors A B := by
    refine ⟨fun {a c} hac => ?_⟩
    rw [Algebra.smul_def] at hac
    rcases mul_eq_zero.mp hac with h | h
    · left; exact hAB (by simpa using h)
    · right; exact h
  rw [← ordA_congr _ _ hdet hx0 hbridgeDet,
    ordInt_baseChangeDet_eq_length_cokernel A K B φ hφinj hdet, hbridgeCoker]

/-
## Sub-lemma (Step D = Stacks Tag 02M0, Lemma 10.52.12): localization decomposition of length.

For a nonzero `b : B`, the residue-degree-weighted sum of the local orders equals the `A`-length
of `B / bB`:

    Σ_v [κ(m_v):κ(m_A)] · ord_{B_v}(b) = length_A (B / bB).

INFORMAL ARGUMENT. Two ingredients:
(a) For each maximal ideal `m_v` of `B`, `ord_{B_v}(b) = length_{B_v}((B/bB)_{m_v})` by definition
    of `ord` (Definition 1) applied to the 1-dim Noetherian local domain `B_v = B_{m_v}` with
    fraction field `L`: indeed `ord_{B_v}(algebraMap B_v L b) = length_{B_v}(B_v / b·B_v)`
    (`ordInt_algebraMap` for `R = B_v`), and `(B/bB)_{m_v} ≅ B_v / b·B_v`.
(b) Change of rings for length along the residue field: if `M` is a finite-length module over the
    local ring `B_v` with residue field `κ(m_v)`, then `length_A(M) = [κ(m_v):κ(m_A)] ·
    length_{B_v}(M)` — because `A → B_v` is local with residue extension `κ(m_A) → κ(m_v)` of
    degree `[κ(m_v):κ(m_A)] = inertiaDeg`, and length multiplies by the residue degree under such
    a finite local extension (Jordan–Hölder: each `B_v`-composition factor `κ(m_v)` has
    `A`-length `[κ(m_v):κ(m_A)]`). Applied to `M = (B/bB)_{m_v}`:
        length_A((B/bB)_{m_v}) = [κ(m_v):κ(m_A)] · length_{B_v}((B/bB)_{m_v}).
(c) Tag 02M0 (Lemma 10.52.12): a finite-length module over the semilocal `B` is the (finite)
    direct sum of its localizations at the maximal ideals, so length is additive:
        length_A (B/bB) = Σ_v length_A((B/bB)_{m_v}).
    (`B/bB` is Artinian — finite `A`-length, killed by a power of `m_A` — hence its support is the
     finite set of maximal ideals of `B`, and `M ≅ ⊕_v M_{m_v}`.)
Combining (a)+(b)+(c):
    length_A(B/bB) = Σ_v length_A((B/bB)_{m_v}) = Σ_v [κ(m_v):κ(m_A)] · length_{B_v}((B/bB)_{m_v})
                   = Σ_v [κ(m_v):κ(m_A)] · ord_{B_v}(b).
This is a substantial, separable lemma (its own subtree); the chief Mathlib gap is the
finite-direct-sum-of-localizations decomposition (02M0) and the residue-degree length change (b).
-/

/-- **Ingredient (a)** (localization-quotient iso). For each maximal ideal `m_v` of `B`, the
localization of `B/bB` at `m_v` is `B_v`-isomorphic to `B_v / b·B_v`, so they have the same
`B_v`-length. Proof route: localization is exact, so applying `LocalizedModule v.primeCompl (-)`
to the cokernel presentation `B --·b--> B → B/bB → 0` yields `B_v --·b--> B_v → (B/bB)_{m_v} → 0`,
i.e. `(B/bB)_{m_v} ≅ B_v / (algebraMap B B_v b)·B_v`. Mathlib hooks to explore:
`LocalizedModule`/`IsLocalizedModule` flatness, `Localization.quotientEquiv`-style isos, or build
the
`B_v`-linear equiv by hand from `IsLocalizedModule.mk'`/`LinearEquiv` on the cokernel. -/
theorem length_localizedModule_quot_eq
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B]
    [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
    (v : MaximalSpectrum B) (b : B) :
    Module.length (Localization.AtPrime v.asIdeal)
        (LocalizedModule v.asIdeal.primeCompl (B ⧸ Ideal.span {b})) =
      Module.length (Localization.AtPrime v.asIdeal)
        ((Localization.AtPrime v.asIdeal) ⧸
          Ideal.span {algebraMap B (Localization.AtPrime v.asIdeal) b}) := by
  set p := v.asIdeal.primeCompl with hp
  set Bv := Localization.AtPrime v.asIdeal with hBv
  have hsub : Submodule.localized' Bv p (Algebra.linearMap B Bv) (Ideal.span {b})
      = Ideal.span {algebraMap B Bv b} := by
    rw [Submodule.localized'_span]
    simp [Algebra.linearMap_apply, Ideal.span]
  have e : LocalizedModule p (B ⧸ Ideal.span {b}) ≃ₗ[B]
      (Bv ⧸ Submodule.localized' Bv p (Algebra.linearMap B Bv) (Ideal.span {b})) :=
    IsLocalizedModule.iso p
      (Submodule.toLocalizedQuotient' Bv p (Algebra.linearMap B Bv) (Ideal.span {b}))
  have e' : LocalizedModule p (B ⧸ Ideal.span {b}) ≃ₗ[Bv]
      (Bv ⧸ Submodule.localized' Bv p (Algebra.linearMap B Bv) (Ideal.span {b})) :=
    LinearEquiv.extendScalarsOfIsLocalization p Bv e
  rw [LinearEquiv.length_eq e', hsub]

-- `Ideal.inertiaDeg'` has no semantics-preserving replacement here: `Ideal.inertiaDeg` is a
-- different definition (residue fields of localizations), equal only under `LiesOver` plus
-- maximality, so migrating would change this statement.
set_option linter.deprecated false in
/-- **Ingredient (b)** (residue-degree change of rings for length). For a module `N` over
`B_v = Localization.AtPrime m_v` which is also an `A`-module compatibly (`IsScalarTower`), the
`A`-length is `[κ(m_v):κ(m_A)]` times the `B_v`-length. Proof route (Jordan–Hölder): the residue
field `κ(m_v) = B_v/m_vB_v ≅ B/m_v` is a finite extension of `κ(m_A) = A/m_A` of degree
`inertiaDeg(m_A, m_v) = finrank_{κ(m_A)}(B/m_v)`; the unique simple `B_v`-module `κ(m_v)` has
`A`-length `= finrank_{κ(m_A)}(κ(m_v))` (length of a vector space = `finrank`, since `m_A` kills
`κ(m_v)`); then `length_A` is additive (`Module.length_eq_add_of_exact`) along a `B_v`-composition
series of `N`, each factor contributing `inertiaDeg`. Likely needs its own subtree (composition
series / `Module.length` induction). NOTE: the statement is unconditional in `N`; for `N = ⊤`
(length
`⊤`) both sides are `⊤` (if `inertiaDeg ≠ 0`) — the genuine content is the finite-length case. -/
@[sga "2 IV 5.2" "special case"]
theorem length_restrictScalars_eq_inertiaDeg_mul
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B]
    [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
    (v : MaximalSpectrum B)
    (N : Type*) [AddCommGroup N]
    [Module (Localization.AtPrime v.asIdeal) N] [Module A N]
    [IsScalarTower A (Localization.AtPrime v.asIdeal) N]
    (hN : Module.length (Localization.AtPrime v.asIdeal) N ≠ ⊤) :
    Module.length A N =
      (Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) v.asIdeal : ℕ∞) *
        Module.length (Localization.AtPrime v.asIdeal) N := by
  -- finrank_{κ(m_A)}(B/m_v))
  set Bv := Localization.AtPrime v.asIdeal with hBv
  have hvmax : v.asIdeal.IsMaximal := v.isMaximal
  have : IsLocalRing Bv := Localization.AtPrime.isLocalRing v.asIdeal
  -- generic length-over-restriction lemma: if `A → K` is a surjective ring map and `M` is a
  -- `K`-module (compatible `A`-action), then the `A`- and `K`-submodule lattices coincide,
  -- hence the lengths agree.
  have len_eq_aux : ∀ (A K : Type _) [CommRing A] [CommRing K] [Algebra A K]
      (_ : Function.Surjective (algebraMap A K))
      (M : Type _) [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower A K M],
      Module.length A M = Module.length K M := by
    intro A K _ _ _ hsurj M _ _ _ _
    let toK : Submodule A M → Submodule K M := fun N =>
    { carrier := N, add_mem' := N.add_mem, zero_mem' := N.zero_mem
      smul_mem' := fun k m hm => by
        obtain ⟨a, rfl⟩ := hsurj k; rw [algebraMap_smul]; exact N.smul_mem a hm }
    let e : Submodule K M ≃o Submodule A M :=
    { toFun := fun N => N.restrictScalars A, invFun := toK
      left_inv := fun N => by ext x; simp [toK]
      right_inv := fun N => by ext x; simp [toK]
      map_rel_iff' := by intro N₁ N₂; exact Iff.rfl }
    unfold Module.length; congr 1; exact (Order.krullDim_eq_of_orderIso e).symm
  -- key induction (Jordan–Hölder): for finite-length `Bv`-modules `M`,
  -- `length_A M = length_A(κ(m_v)) * length_{Bv} M`.
  have key : ∀ (M : Type _) [AddCommGroup M] [Module Bv M] (_ : IsFiniteLength Bv M)
      [Module A M] [IsScalarTower A Bv M],
      Module.length A M
        = Module.length A (Bv ⧸ IsLocalRing.maximalIdeal Bv) * Module.length Bv M := by
    set c := Module.length A (Bv ⧸ IsLocalRing.maximalIdeal Bv) with hc
    -- `A`-length is additive along the canonical SES `0 → N → M → M/N → 0`.
    have addA : ∀ (M : Type _) [AddCommGroup M] [Module Bv M] [Module A M] [IsScalarTower A Bv M]
        (N : Submodule Bv M),
        Module.length A M = Module.length A N + Module.length A (M ⧸ N) := by
      intro M _ _ _ _ N
      have hex : Function.Exact (N.subtype) (N.mkQ) := by
        rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_subtype]
      exact Module.length_eq_add_of_exact
        ((N.subtype).restrictScalars A) ((N.mkQ).restrictScalars A)
        N.subtype_injective N.mkQ_surjective hex
    -- a simple `Bv`-module is `≅ κ(m_v)` (since `Bv` is local), so has `A`-length `c`.
    have simpleA : ∀ (Q : Type _) [AddCommGroup Q] [Module Bv Q] [Module A Q] [IsScalarTower A Bv
        Q],
        IsSimpleModule Bv Q → Module.length A Q = c := by
      intro Q _ _ _ _ hQ
      obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hQ
      have hImax : I = IsLocalRing.maximalIdeal Bv := IsLocalRing.eq_maximalIdeal hI
      subst hImax
      exact (e.restrictScalars A).length_eq
    intro M _ _ h
    induction h with
    | @of_subsingleton M _ _ _ =>
        intro instA _
        have h1 : Module.length A M = 0 := Module.length_eq_zero_iff.mpr ‹_›
        have h2 : Module.length Bv M = 0 := Module.length_eq_zero_iff.mpr ‹_›
        rw [h1, h2, mul_zero]
    | @of_simple_quotient M _ _ N hsimp a ih =>
        intro instA _
        have hAadd := addA M N
        have hBadd : Module.length Bv M = Module.length Bv N + Module.length Bv (M ⧸ N) := by
          have hex : Function.Exact (N.subtype) (N.mkQ) := by
            rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_subtype]
          exact Module.length_eq_add_of_exact N.subtype N.mkQ
            N.subtype_injective N.mkQ_surjective hex
        have hQlen : Module.length A (M ⧸ N) = c := simpleA (M ⧸ N) hsimp
        have hQBlen : Module.length Bv (M ⧸ N) = 1 := Module.length_eq_one_iff.mpr hsimp
        have hIH : Module.length A N = c * Module.length Bv N := ih
        rw [hAadd, hIH, hQlen, hBadd, hQBlen, mul_add, mul_one]
  -- the per-step constant equals the residue degree `inertiaDeg`.
  have hconst : Module.length A (Bv ⧸ IsLocalRing.maximalIdeal Bv)
      = (Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) v.asIdeal : ℕ∞) := by
    have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
    have hlo : v.asIdeal.LiesOver (IsLocalRing.maximalIdeal A) :=
      have hmax : (Ideal.comap (algebraMap A B) v.asIdeal).IsMaximal :=
        Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) v.asIdeal
      ⟨(IsLocalRing.eq_maximalIdeal hmax).symm⟩
    change Module.length A v.asIdeal.ResidueField = _
    have : IsScalarTower A (B ⧸ v.asIdeal) v.asIdeal.ResidueField :=
      IsScalarTower.of_algebraMap_eq (fun x => by
        rw [IsScalarTower.algebraMap_apply A B (B ⧸ v.asIdeal)]; rfl)
    -- `κ(m_v) ≅ B/m_v` as `A`-modules, since `m_v` is maximal.
    let alg : (B ⧸ v.asIdeal) ≃ₐ[B ⧸ v.asIdeal] v.asIdeal.ResidueField :=
      AlgEquiv.ofBijective (Algebra.ofId (B ⧸ v.asIdeal) v.asIdeal.ResidueField)
        (Ideal.bijective_algebraMap_quotient_residueField v.asIdeal)
    have hlen1 : Module.length A v.asIdeal.ResidueField = Module.length A (B ⧸ v.asIdeal) :=
      ((alg.symm.toLinearEquiv.restrictScalars A)).length_eq
    rw [hlen1]
    have hmaxA : (IsLocalRing.maximalIdeal A).IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
    have : Module.Finite A (B ⧸ v.asIdeal) := Module.Finite.of_surjective
      ((Submodule.mkQ v.asIdeal).restrictScalars A) (Submodule.mkQ_surjective v.asIdeal)
    have : Module.Finite (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ v.asIdeal) :=
      Module.Finite.of_restrictScalars_finite A _ _
    have hsurj : Function.Surjective (algebraMap A (A ⧸ IsLocalRing.maximalIdeal A)) := by
      rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective
    -- `length_A (B/m_v) = length_{κ(m_A)} (B/m_v) = finrank_{κ(m_A)} (B/m_v) = inertiaDeg`.
    rw [len_eq_aux A (A ⧸ IsLocalRing.maximalIdeal A) hsurj (B ⧸ v.asIdeal)]
    rw [Ideal.inertiaDeg'_algebraMap]
    let fld : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
    exact Module.length_eq_finrank (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ v.asIdeal)
  -- combine: `N` is finite length over `Bv`, then apply `key` and `hconst`.
  have hfl : IsFiniteLength Bv N := Module.length_ne_top_iff.mp hN
  rw [key N hfl, hconst]

/-- **(c) sub-lemma 1.** `M = B/bB` is an Artinian `B`-module for `b ≠ 0`. It has finite
`A`-length (it is a quotient of `B/aB` for a nonzero `a ∈ A` with `aB ⊆ bB`, and `B/aB` is finite
over the Artinian ring `A/aA`), hence is Artinian over `A`, hence Artinian over `B` (the `B`-
submodule lattice embeds in the `A`-submodule lattice since `A → B` is module-finite — use
`isArtinian_of_tower` / `IsArtinian` transfer). Used to compute the support of `M` (a finite set of
maximal ideals) for the localization decomposition. -/
theorem isArtinian_quot_span_of_ne_zero
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B]
    [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
    (b : B) (hb : b ≠ 0) :
    IsArtinian B (B ⧸ Ideal.span {b}) := by
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  -- Step 1: B has Krull dimension ≤ 1 (nonzero primes are maximal, via going-up over A).
  have hB1 : Ring.KrullDimLE 1 B := by
    rw [Ring.krullDimLE_one_iff_of_noZeroDivisors]
    intro I hIne hIp
    have hcomap_ne : Ideal.comap (algebraMap A B) I ≠ ⊥ :=
      Ideal.IsIntegral.under_ne_bot A hIne
    have hmax : (Ideal.comap (algebraMap A B) I).IsMaximal :=
      Ideal.isMaximal_of_isPrime_of_ne_bot _ hcomap_ne
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) I hmax
  -- Step 2: B is a Noetherian ring (finite over Noetherian A).
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  -- Step 3: B ⧸ (b) has Krull dimension 0.
  have hk0 : Ring.KrullDimLE 0 (B ⧸ Ideal.span {b}) := by
    rw [Ring.krullDimLE_iff]
    have hmem : b ∈ nonZeroDivisors B := mem_nonZeroDivisors_of_ne_zero hb
    have hq := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hmem
    have hB : ringKrullDim B ≤ ((1:ℕ):WithBot ℕ∞) := Ring.krullDimLE_iff.mp inferInstance
    have h : ringKrullDim (B ⧸ Ideal.span {b}) + 1 ≤ ((1:ℕ):WithBot ℕ∞) := le_trans hq hB
    set d := ringKrullDim (B ⧸ Ideal.span {b}) with hd
    have h' : d + 1 ≤ ((1:ℕ∞):WithBot ℕ∞) := by rw [← WithBot.coe_natCast] at h; exact_mod_cast h
    change d ≤ ((0:ℕ):WithBot ℕ∞)
    rw [show ((0:ℕ):WithBot ℕ∞) = ((0:ℕ∞):WithBot ℕ∞) by norm_cast]
    rw [WithBot.le_coe_iff]
    intro a' hda
    rw [hda] at h'
    have h2 : a' + 1 ≤ 1 := by exact_mod_cast h'
    cases a' with
    | top => simp at h2
    | coe n =>
      rw [← ENat.natCast_one, ← ENat.natCast_add, ENat.natCast_le_natCast] at h2
      have : n = 0 := by omega
      subst this; simp
  -- Step 4: a Noetherian ring of dimension 0 is Artinian.
  have : IsArtinianRing (B ⧸ Ideal.span {b}) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  -- Step 5: restrict scalars from (B ⧸ (b)) to B.
  exact isArtinian_of_surjective_algebraMap (S := B) (R := B ⧸ Ideal.span {b})
    Ideal.Quotient.mk_surjective

-- needed: `localizedModule_offdiag_subsingleton`'s `simpa` produces an `(Submodule B M)ᵒᵈ`
-- equality that only typechecks once `OrderDual` unfolds at `default` transparency
set_option backward.isDefEq.respectTransparency false in
/-- **(c) sub-lemma 2** (off-diagonal vanishing of double localization). For distinct maximal
ideals `v ≠ w` of `B`, the localization at `m_w` of the localization at `m_v` of the Artinian
module `M = B/bB` vanishes. Reason: `M_{m_v}` is supported only at `m_v` (it is Artinian with
support `⊆ {m_v}`), so localizing it further at `m_w ≠ m_v` kills it (the localization of a module
whose support misses `m_w` is `0`). Mathlib hooks: `Module.support`, `LocalizedModule`,
`LocalizedModule.subsingleton_iff` / support-disjointness; uses `isArtinian_quot_span_of_ne_zero`.
-/
theorem localizedModule_offdiag_subsingleton
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B]
    [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
    (b : B) (hb : b ≠ 0)
    (v w : MaximalSpectrum B) (hvw : v ≠ w) :
    Subsingleton (LocalizedModule w.asIdeal.primeCompl
      (LocalizedModule v.asIdeal.primeCompl (B ⧸ Ideal.span {b}))) := by
  classical
  set M := B ⧸ Ideal.span {b} with hM
  have : IsArtinian B M := isArtinian_quot_span_of_ne_zero A B b hb
  -- choose `s ∈ m_v` with `s ∉ m_w` (distinct maximal ideals are incomparable)
  have hsExists : ∃ s ∈ v.asIdeal, s ∉ w.asIdeal := IsConcreteLE.not_le_iff_exists.mp fun hle =>
    hvw (MaximalSpectrum.ext (v.isMaximal.eq_of_le w.isMaximal.ne_top hle))
  obtain ⟨s, hsv, hsw⟩ := hsExists
  rw [LocalizedModule.subsingleton_iff]
  intro n
  -- write `n = mk c u`
  induction n using LocalizedModule.induction_on with
  | _ c u =>
    -- Artinian stabilization of the descending cyclic chain `B ∙ sᵐ • c`:
    -- ∃ k β, sᵏ • c = β • (sᵏ⁺¹ • c)
    have hstab : ∃ (k : ℕ) (β : B), s^k • c = β • (s^(k+1) • c) := by
      set g : ℕ → Submodule B M := fun m => Submodule.span B {s^m • c} with hg
      have hanti : Antitone g := by
        intro a c' hac
        rw [hg]; simp only
        rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hac
        rw [pow_add, mul_smul, smul_comm]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      let f : ℕ →o (Submodule B M)ᵒᵈ :=
        ⟨fun m => OrderDual.toDual (g m), fun a c' hac => hanti hac⟩
      obtain ⟨k, hk⟩ := IsArtinian.monotone_stabilizes f
      have key : g k = g (k+1) := by simpa [f] using hk (k+1) (Nat.le_succ k)
      have hmem : s^k • c ∈ g (k+1) := by
        rw [← key]; exact Submodule.mem_span_singleton_self _
      simp only [hg, Submodule.mem_span_singleton] at hmem
      obtain ⟨β, hβ⟩ := hmem
      exact ⟨k, β, hβ.symm⟩
    obtain ⟨k, β, hβ⟩ := hstab
    -- the scalar `sᵏ ∈ w.primeCompl` annihilates `n`; the witness `(1 - β·s) ∈ v.primeCompl`
    refine ⟨s^k, ?_, ?_⟩
    · -- `sᵏ ∈ w.asIdeal.primeCompl` since `s ∉ w.asIdeal` and `w.asIdeal` is prime
      have hwp : w.asIdeal.IsPrime := w.isMaximal.isPrime
      simp only [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
        SetLike.mem_coe]
      intro hpow
      exact hsw (hwp.mem_of_pow_mem k hpow)
    · -- `sᵏ • (mk c u) = mk (sᵏ • c) u = 0`, witnessed by `(1 - β·s) ∈ v.primeCompl`
      rw [LocalizedModule.smul'_mk]
      have hkill : (1 - β * s) • (s^k • c) = 0 := by
        rw [sub_smul, one_smul, mul_smul]
        have hss : s • (s^k • c) = s^(k+1) • c := by rw [← mul_smul, ← pow_succ']
        rw [hss, ← hβ, sub_self]
      have hv : (1 - β * s) ∈ v.asIdeal.primeCompl := by
        simp only [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
          SetLike.mem_coe]
        intro hmem
        have hone : (1 : B) ∈ v.asIdeal := by
          have hbs : β * s ∈ v.asIdeal := Ideal.mul_mem_left _ _ hsv
          have := Ideal.add_mem _ hmem hbs
          simpa using this
        exact v.isMaximal.ne_top (Ideal.eq_top_of_isUnit_mem _ hone isUnit_one)
      rw [show (0 : LocalizedModule v.asIdeal.primeCompl M) =
          LocalizedModule.mk 0 u from (LocalizedModule.zero_mk u).symm]
      rw [LocalizedModule.mk_eq]
      refine ⟨⟨1 - β*s, hv⟩, ?_⟩
      simp only [Submonoid.mk_smul, smul_zero]
      rw [smul_comm, hkill, smul_zero]

/-- **(c) sub-lemma 3** (the localization-decomposition iso, Stacks Tag 02M0 core). The canonical
`B`-linear map `M → ∏_v M_{m_v}` from the finite-length `B`-module `M = B/bB` to the (finite)
product of its localizations at the maximal ideals is an isomorphism. Proof route (closer-verified
reduction): apply `bijective_of_isLocalized_maximal` over the base ring `B` to the natural map
`LinearMap.pi (fun v => LocalizedModule.mkLinearMap v.asIdeal.primeCompl M)`; the resulting per-
maximal stalk goal at `P = m_w` is bijectivity of `M_{m_w} → ∏_v (M_{m_v})_{m_w}`, which holds
componentwise: the diagonal `v = w` component is `isLocalizedModule_id` (re-localizing a module
already local at `m_w`), and the off-diagonal `v ≠ w` components vanish by
`localizedModule_offdiag_subsingleton`. -/
theorem quot_span_nonempty_equiv_pi_localized
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B]
    [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
    [Finite (MaximalSpectrum B)]
    (b : B) (hb : b ≠ 0) :
    Nonempty ((B ⧸ Ideal.span {b}) ≃ₗ[B]
      (∀ v : MaximalSpectrum B,
        LocalizedModule v.asIdeal.primeCompl (B ⧸ Ideal.span {b}))) := by
  classical
  have := Fintype.ofFinite (MaximalSpectrum B)
  refine ⟨LinearEquiv.ofBijective
    (LinearMap.pi (fun v =>
      LocalizedModule.mkLinearMap v.asIdeal.primeCompl (B ⧸ Ideal.span {b}))) ?_⟩
  apply bijective_of_isLocalized_maximal
    (fun P _ => LocalizedModule P.primeCompl (B ⧸ Ideal.span {b}))
    (fun P _ => LocalizedModule.mkLinearMap P.primeCompl (B ⧸ Ideal.span {b}))
    (fun P _ => ∀ v : MaximalSpectrum B,
       LocalizedModule P.primeCompl (LocalizedModule v.asIdeal.primeCompl (B ⧸ Ideal.span {b})))
    (fun P _ => LinearMap.pi (fun v =>
       (LocalizedModule.mkLinearMap P.primeCompl _).comp (LinearMap.proj v)))
    _
  intro P hP
  -- The composite `g ∘ F : M → ∏_v (M_v)_{m_P}` is a localization of `M` at `m_P`: off-diagonal
  -- factors vanish (`localizedModule_offdiag_subsingleton`), so the product is iso to the diagonal
  -- factor `(M_w)_{m_w} ≅ M_{m_w}` (re-localizing the already-local `M_w`, via
  -- `isLocalizedModule_id`).
  have hcomp : IsLocalizedModule P.primeCompl
      ((LinearMap.pi (fun v : MaximalSpectrum B =>
          (LocalizedModule.mkLinearMap P.primeCompl
            (LocalizedModule v.asIdeal.primeCompl (B ⧸ Ideal.span {b}))).comp
          (LinearMap.proj v))).comp
        (LinearMap.pi (fun v : MaximalSpectrum B =>
          LocalizedModule.mkLinearMap v.asIdeal.primeCompl (B ⧸ Ideal.span {b})))) := by
    set M := B ⧸ Ideal.span {b} with hM
    set w : MaximalSpectrum B := ⟨P, hP⟩ with hw
    set l := (LinearMap.pi (fun v : MaximalSpectrum B =>
            (LocalizedModule.mkLinearMap P.primeCompl
              (LocalizedModule v.asIdeal.primeCompl M)).comp
            (LinearMap.proj v))).comp
          (LinearMap.pi (fun v : MaximalSpectrum B =>
            LocalizedModule.mkLinearMap v.asIdeal.primeCompl M)) with hl
    let mkw := LocalizedModule.mkLinearMap w.asIdeal.primeCompl M
    let mkP := LocalizedModule.mkLinearMap P.primeCompl (LocalizedModule w.asIdeal.primeCompl M)
    have hid : IsLocalizedModule P.primeCompl
        (LinearMap.id (R := B) (M := LocalizedModule w.asIdeal.primeCompl M)) :=
      isLocalizedModule_id P.primeCompl (LocalizedModule w.asIdeal.primeCompl M)
        (Localization P.primeCompl)
    have hmkP_bij : Function.Bijective mkP := by
      have hcoe : ⇑mkP = ⇑(IsLocalizedModule.linearEquiv P.primeCompl
            (LinearMap.id (R := B) (M := LocalizedModule w.asIdeal.primeCompl M)) mkP) := by
        funext x
        simpa only [LinearMap.id_coe, id_eq] using (IsLocalizedModule.linearEquiv_apply P.primeCompl
          (LinearMap.id (R := B) (M := LocalizedModule w.asIdeal.primeCompl M)) mkP x).symm
      rw [hcoe]
      exact (IsLocalizedModule.linearEquiv P.primeCompl
        (LinearMap.id (R := B) (M := LocalizedModule w.asIdeal.primeCompl M)) mkP).bijective
    let mkPe : LocalizedModule w.asIdeal.primeCompl M ≃ₗ[B]
        LocalizedModule P.primeCompl (LocalizedModule w.asIdeal.primeCompl M) :=
      LinearEquiv.ofBijective mkP hmkP_bij
    have hd : IsLocalizedModule P.primeCompl (mkPe.toLinearMap.comp mkw) :=
      IsLocalizedModule.of_linearEquiv P.primeCompl mkw mkPe
    have hproj : Function.Bijective
        (LinearMap.proj w : (∀ v : MaximalSpectrum B,
            LocalizedModule P.primeCompl (LocalizedModule v.asIdeal.primeCompl M))
          →ₗ[B] LocalizedModule P.primeCompl (LocalizedModule w.asIdeal.primeCompl M)) := by
      refine ⟨fun y₁ y₂ hyy => funext fun v => ?_, fun z => ⟨Pi.single w z, by simp⟩⟩
      by_cases hv : v = w
      · subst hv; exact hyy
      · exact (localizedModule_offdiag_subsingleton A B b hb v w hv).allEq _ _
    let pe := LinearEquiv.ofBijective (LinearMap.proj w : (∀ v : MaximalSpectrum B,
            LocalizedModule P.primeCompl (LocalizedModule v.asIdeal.primeCompl M))
          →ₗ[B] LocalizedModule P.primeCompl (LocalizedModule w.asIdeal.primeCompl M)) hproj
    have hkey : l = (pe.symm.toLinearMap.comp (mkPe.toLinearMap.comp mkw)) := by
      refine LinearMap.ext fun m => ?_
      apply pe.injective
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply]
      change (l m) w = _
      simp only [hl, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.proj_apply]
      rfl
    rw [hkey]
    exact IsLocalizedModule.of_linearEquiv P.primeCompl (mkPe.toLinearMap.comp mkw) pe.symm
  -- The induced localization map is bijective because `g ∘ F` is itself a localization (`hcomp`):
  -- it then agrees with the canonical iso between the two localizations of `M`.
  set f := LocalizedModule.mkLinearMap P.primeCompl (B ⧸ Ideal.span {b}) with hf
  set g := LinearMap.pi (fun v : MaximalSpectrum B =>
      (LocalizedModule.mkLinearMap P.primeCompl
        (LocalizedModule v.asIdeal.primeCompl (B ⧸ Ideal.span {b}))).comp
      (LinearMap.proj v)) with hg
  set F := LinearMap.pi (fun v : MaximalSpectrum B =>
      LocalizedModule.mkLinearMap v.asIdeal.primeCompl (B ⧸ Ideal.span {b})) with hFdef
  have key : (IsLocalizedModule.map P.primeCompl f g F)
      = ((IsLocalizedModule.iso P.primeCompl (g.comp F)).toLinearMap.comp
          (IsLocalizedModule.iso P.primeCompl f).symm.toLinearMap) := by
    apply IsLocalizedModule.ext P.primeCompl f
      (fun x => IsLocalizedModule.map_units (g.comp F) x)
    rw [IsLocalizedModule.map_comp]
    refine LinearMap.ext fun m => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [show (IsLocalizedModule.iso P.primeCompl f).symm (f m) = LocalizedModule.mk m 1 from ?_]
    · rw [IsLocalizedModule.iso_apply_mk]; simp
    · rw [IsLocalizedModule.iso_symm_apply' P.primeCompl f (f m) m 1 (by simp)]
  rw [key, LinearMap.coe_comp]
  exact (IsLocalizedModule.iso P.primeCompl (g.comp F)).bijective.comp
    (IsLocalizedModule.iso P.primeCompl f).symm.bijective

/-- **Ingredient (c)** (finite-direct-sum-of-localizations decomposition, Stacks Tag 02M0 core).
For nonzero `b`, the finite-`A`-length module `M = B/bB` over the semilocal ring `B` is the finite
direct sum of its localizations at the maximal ideals, so `A`-length is additive:
`length_A(B/bB) = Σ_v length_A((B/bB)_{m_v})`. Proof (closer-verified): the `B`-linear iso
`M ≃ₗ[B] ∏_v M_{m_v}` (`quot_span_nonempty_equiv_pi_localized`) restricts to an `A`-linear iso,
and `Module.length_pi_of_fintype` turns the product length into the sum. -/
theorem length_quot_eq_sum_localizations
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B]
    [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
    [Fintype (MaximalSpectrum B)]
    (b : B) (hb : b ≠ 0) :
    Module.length A (B ⧸ Ideal.span {b}) =
      ∑ v : MaximalSpectrum B,
        Module.length A (LocalizedModule v.asIdeal.primeCompl (B ⧸ Ideal.span {b})) := by
  -- The B-linear iso `M ≃ₗ[B] ∏_v M_{m_v}` restricts to an A-linear iso;
  -- `Module.length_pi_of_fintype`
  -- turns the product length into the sum.
  obtain ⟨e⟩ := quot_span_nonempty_equiv_pi_localized A B b hb
  rw [(e.restrictScalars A).length_eq, Module.length_pi_of_fintype]

/-- **Finiteness** of each localized factor: `(B/bB)_{m_v}` has finite `B_v`-length for `b ≠ 0`.
Used to push `.toNat`/casts through the finite sum/product in the assembly. Route: it is
`B_v`-isomorphic to `B_v / b·B_v` (ingredient (a)) whose length is finite because `B_v` is a
1-dim Noetherian local domain and `algebraMap B B_v b ≠ 0` (so `ordInt_algebraMap`/`spanLen_ne_top`
machinery applies), or directly because `(B/bB)_{m_v}` is a localization of the finite-`A`-length
`B/bB`. -/
theorem length_localizedModule_ne_top
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B]
    [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
    [∀ v : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime v.asIdeal)]
    [∀ v : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime v.asIdeal)]
    (v : MaximalSpectrum B) (b : B)
    (hbv : algebraMap B (Localization.AtPrime v.asIdeal) b ≠ 0) :
    Module.length (Localization.AtPrime v.asIdeal)
        (LocalizedModule v.asIdeal.primeCompl (B ⧸ Ideal.span {b})) ≠ ⊤ := by
  -- Ingredient (a): the localized factor has the same B_v-length as B_v/span{algebraMap b}.
  rw [length_localizedModule_quot_eq A B v b]
  -- B_v is a 1-dim Noetherian local domain and `algebraMap B B_v b ≠ 0`, so `spanLen_ne_top`.
  exact spanLen_ne_top (Localization.AtPrime v.asIdeal) _ hbv

-- `Ideal.inertiaDeg'` has no semantics-preserving replacement here: `Ideal.inertiaDeg` is a
-- different definition (residue fields of localizations), equal only under `LiesOver` plus
-- maximality, so migrating would change this statement.
set_option linter.deprecated false in
/-- The length of `B ⧸ bB` over `A` is the sum, over the maximal ideals `v` of `B`, of the
inertia degree of `v` times the order of vanishing of `b` in `B_v`. -/
theorem sum_inertiaDeg_ordInt_eq_length_quotient
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B]
    [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
    (L : Type*) [Field L]
    [Algebra B L] [IsFractionRing B L]
    [Fintype (MaximalSpectrum B)]
    [∀ v : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime v.asIdeal)]
    [∀ v : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime v.asIdeal)]
    [∀ v : MaximalSpectrum B, Algebra (Localization.AtPrime v.asIdeal) L]
    [∀ v : MaximalSpectrum B, IsScalarTower B (Localization.AtPrime v.asIdeal) L]
    [∀ v : MaximalSpectrum B, IsFractionRing (Localization.AtPrime v.asIdeal) L]
    (b : B) (hb : b ≠ 0)
    (hbL : ∀ _ : MaximalSpectrum B, (algebraMap B L b) ≠ 0) :
    ∑ v : MaximalSpectrum B,
        (Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) v.asIdeal : ℤ) *
          ordInt (Localization.AtPrime v.asIdeal) (algebraMap B L b) (hbL v) =
      ((Module.length A (B ⧸ Ideal.span {b})).toNat : ℤ) := by
  -- Stacks 02M0)
  -- image of `b` in each `B_v` is nonzero.
  have hbv : ∀ v : MaximalSpectrum B,
      algebraMap B (Localization.AtPrime v.asIdeal) b ≠ 0 := by
    intro v
    have h := hbL v
    rw [IsScalarTower.algebraMap_apply B (Localization.AtPrime v.asIdeal) L b] at h
    intro hz; apply h; rw [hz]; simp
  -- finiteness of each `B_v`-length.
  have hfin : ∀ v : MaximalSpectrum B,
      Module.length (Localization.AtPrime v.asIdeal)
        (LocalizedModule v.asIdeal.primeCompl (B ⧸ Ideal.span {b})) ≠ ⊤ := fun v =>
    length_localizedModule_ne_top A B v b (hbv v)
  -- Step (a)+def: each local order equals the `B_v`-length of `(B/bB)_{m_v}`, as a `.toNat`.
  have hord : ∀ v : MaximalSpectrum B,
      ordInt (Localization.AtPrime v.asIdeal) (algebraMap B L b) (hbL v) =
        ((Module.length (Localization.AtPrime v.asIdeal)
          (LocalizedModule v.asIdeal.primeCompl (B ⧸ Ideal.span {b}))).toNat : ℤ) := by
    intro v
    have key := ordInt_algebraMap (Localization.AtPrime v.asIdeal)
      (K := L) (algebraMap B (Localization.AtPrime v.asIdeal) b) (hbv v)
      (by rw [← IsScalarTower.algebraMap_apply B (Localization.AtPrime v.asIdeal) L b];
          exact hbL v)
    rw [length_localizedModule_quot_eq A B v b, ← key]
    congr 1
    exact (IsScalarTower.algebraMap_apply B (Localization.AtPrime v.asIdeal) L b)
  -- Reduce the LHS sum to integer casts of the `B_v`-lengths.
  rw [Finset.sum_congr rfl (fun v _ => by rw [hord v])]
  -- Step (c): `length_A(B/bB) = Σ_v length_A((B/bB)_{m_v})` (in ℕ∞).
  rw [length_quot_eq_sum_localizations A B b hb]
  -- Step (b): `length_A((B/bB)_{m_v}) = inertiaDeg_v * length_{B_v}(...)` (in ℕ∞).
  rw [Finset.sum_congr rfl (fun v _ =>
    length_restrictScalars_eq_inertiaDeg_mul A B v _ (hfin v))]
  -- Now both sides are finite; push `.toNat` through the finite sum and product.
  have hprodfin : ∀ v ∈ (Finset.univ : Finset (MaximalSpectrum B)),
      (Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) v.asIdeal : ℕ∞) *
        Module.length (Localization.AtPrime v.asIdeal)
          (LocalizedModule v.asIdeal.primeCompl (B ⧸ Ideal.span {b})) ≠ ⊤ := by
    intro v _
    exact WithTop.mul_ne_top (ENat.natCast_ne_top _) (hfin v)
  rw [ENat.toNat_sum hprodfin]
  push_cast
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [ENat.toNat_mul, ENat.toNat_natCast]
  push_cast [ENat.natCast_toNat (hfin v)]
  ring

/-- If `B` is a module-finite extension of a one-dimensional local domain `A`, with `A → B`
injective, then the fraction field `L` of `B` is finite-dimensional over the fraction field `K`
of `A`. -/
theorem finiteDimensional_fractionRing_of_finite
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B]
    [IsLocalRing A] [Ring.KrullDimLE 1 A]
    (K L : Type*) [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    (hAB : Function.Injective (algebraMap A B)) :
    Module.Finite K L := by
  -- B is integral (hence algebraic) over A since it is module-finite.
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have : Algebra.IsAlgebraic A B := Algebra.IsIntegral.isAlgebraic
  -- The image of `A \ {0}` lies in `B \ {0}` (injectivity + domain).
  have hMN : Algebra.algebraMapSubmonoid B (nonZeroDivisors A) ≤ nonZeroDivisors B := by
    rintro x ⟨a, ha, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    have : a ≠ 0 := nonZeroDivisors.ne_zero ha
    rw [ne_eq, ← (algebraMap A B).map_zero]
    exact fun h => this (hAB h)
  -- Every nonzero `n : B` divides a nonzero element of `A` (it is algebraic over `A`):
  -- by `exists_smul_eq_mul`, `d • 1 = n * c` with `d ≠ 0`, so `n ∣ algebraMap A B d`.
  have hdvd : ∀ n ∈ nonZeroDivisors B,
      ∃ m ∈ Algebra.algebraMapSubmonoid B (nonZeroDivisors A), n ∣ m := by
    intro n hn
    obtain ⟨c, d, hd, hdc⟩ :=
      Algebra.IsAlgebraic.exists_smul_eq_mul A (1 : B) (b := n) (nonZeroDivisors.ne_zero hn)
    refine ⟨algebraMap A B d, ?_, ?_⟩
    · rw [Algebra.algebraMapSubmonoid, Submonoid.mem_map]
      exact ⟨d, mem_nonZeroDivisors_of_ne_zero hd, rfl⟩
    · rw [Algebra.smul_def, mul_one] at hdc
      exact ⟨c, hdc⟩
  -- Hence inverting `A \ {0}` in `B` already produces all of `L = Frac B`.
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L :=
    (IsLocalization.iff_of_le_of_exists_dvd (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))
      (nonZeroDivisors B) hMN hdvd).mpr inferInstance
  -- `Module.Finite A B` localizes to `Module.Finite K L`.
  exact Module.Finite.of_isLocalization A B (nonZeroDivisors A)

-- `Ideal.inertiaDeg'` has no semantics-preserving replacement here: `Ideal.inertiaDeg` is a
-- different definition (residue fields of localizations), equal only under `LiesOver` plus
-- maximality, so migrating would change this statement.
set_option linter.deprecated false in
/-- **The norm formula of Stacks 02MJ, with the data on `B` supplied.** The order of vanishing
of the norm of `y` is the sum, over the maximal ideals `v` of `B`, of the inertia degree of `v`
times the order of vanishing of `y` in `B_v`.

Stacks 02MJ itself, under the source's hypotheses only and with "`B` is semi-local" among its
conclusions, is `finite_maximalSpectrum_and_ordInt_norm_eq_finsum_inertiaDeg_mul_ordInt` in
`StacksFrontier/RingTheory/OrderOfVanishing/Degree.lean`, which derives the instance hypotheses
below and applies this theorem.

The localization data for each maximal ideal of `B` is supplied as instance hypotheses: for
each `v : MaximalSpectrum B` the localization `Localization.AtPrime v.asIdeal` is a Noetherian
ring of Krull dimension at most `1`, carries an algebra structure to `L` compatible with
`B → L`, the `IsScalarTower` hypothesis pinning it down as the canonical localization map, and
is a fraction ring of `L`. These say exactly that each `B_{mᵢ}` is a one-dimensional Noetherian
local domain with fraction field `L`. -/
theorem ord_norm_eq_sum_inertiaDeg_mul_ord
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] [Module.Finite A B]
    [IsNoetherianRing A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
    (K L : Type*) [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [Fintype (MaximalSpectrum B)]
    [∀ v : MaximalSpectrum B, IsNoetherianRing (Localization.AtPrime v.asIdeal)]
    [∀ v : MaximalSpectrum B, Ring.KrullDimLE 1 (Localization.AtPrime v.asIdeal)]
    [∀ v : MaximalSpectrum B, Algebra (Localization.AtPrime v.asIdeal) L]
    [∀ v : MaximalSpectrum B, IsScalarTower B (Localization.AtPrime v.asIdeal) L]
    [∀ v : MaximalSpectrum B, IsFractionRing (Localization.AtPrime v.asIdeal) L]
    (hAB : Function.Injective (algebraMap A B))
    (y : L) (hy : y ≠ 0)
    (x : K) (hx : x = Algebra.norm K y)
    (hx0 : x ≠ 0) :
    ordInt A x hx0 =
      ∑ v : MaximalSpectrum B,
        (Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) v.asIdeal : ℤ) *
          ordInt (Localization.AtPrime v.asIdeal) y hy := by
  -- PROOF (Stacks Tag 02MJ).  Define F y := ordInt A (Nm_{L/K} y) and
  -- G y := Σ_v [κ(m_v):κ(m_A)] · ordInt(B_v) y.  Both are additive in y; reduce y to a ratio
  -- b/b' of elements of B (`IsFractionRing.div_surjective`), then on each b∈B both F and G equal
  -- length_A(B/bB) (the two analytic kernels 02MI/02M0), hence F = G.
  -- L/K is finite (B finite over A; named side-lemma).
  have hKL : Module.Finite K L := finiteDimensional_fractionRing_of_finite A B K L hAB
  have : FiniteDimensional K L := hKL
  have hnorm_ne : ∀ z : L, z ≠ 0 → Algebra.norm K z ≠ 0 :=
    fun z hz => Algebra.norm_ne_zero_iff.mpr hz
  have ordA_congr : ∀ (a a' : K) (ha : a ≠ 0) (ha' : a' ≠ 0),
      a = a' → ordInt A a ha = ordInt A a' ha' := by
    intro a a' ha ha' h; subst h; rfl
  set F : (z : L) → z ≠ 0 → ℤ := fun z hz => ordInt A (Algebra.norm K z) (hnorm_ne z hz) with hF
  set G : (z : L) → z ≠ 0 → ℤ := fun z hz =>
    ∑ v : MaximalSpectrum B,
      (Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) v.asIdeal : ℤ) *
        ordInt (Localization.AtPrime v.asIdeal) z hz with hG
  have hFcongr : ∀ (a a' : L) (ha : a ≠ 0) (ha' : a' ≠ 0), a = a' → F a ha = F a' ha' := by
    intro a a' ha ha' h; subst h; rfl
  have hGcongr : ∀ (a a' : L) (ha : a ≠ 0) (ha' : a' ≠ 0), a = a' → G a ha = G a' ha' := by
    intro a a' ha ha' h; subst h; rfl
  -- F additive (ordInt_mul on A + multiplicativity of the norm).
  have hFmul : ∀ (z w : L) (hz : z ≠ 0) (hw : w ≠ 0),
      F (z * w) (mul_ne_zero hz hw) = F z hz + F w hw := by
    intro z w hz hw
    simp only [hF]
    rw [ordA_congr (Algebra.norm K (z * w)) (Algebra.norm K z * Algebra.norm K w)
        (hnorm_ne _ (mul_ne_zero hz hw)) (mul_ne_zero (hnorm_ne z hz) (hnorm_ne w hw))
        (map_mul (Algebra.norm K) z w)]
    rw [ordInt_mul A (Algebra.norm K z) (Algebra.norm K w) (hnorm_ne z hz) (hnorm_ne w hw)]
  -- G additive (ordInt_mul on each B_v, summed).
  have hGmul : ∀ (z w : L) (hz : z ≠ 0) (hw : w ≠ 0),
      G (z * w) (mul_ne_zero hz hw) = G z hz + G w hw := by
    intro z w hz hw
    simp only [hG]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rw [ordInt_mul (Localization.AtPrime v.asIdeal) z w hz hw, mul_add]
  -- key (b ∈ B case): F (b) = G (b), both equal length_A (B / bB).
  have key : ∀ (c : B) (hc : c ≠ 0) (hcL : algebraMap B L c ≠ 0),
      F (algebraMap B L c) hcL = G (algebraMap B L c) hcL := by
    intro c hc hcL
    have hnc : Algebra.norm K (algebraMap B L c) ≠ 0 := hnorm_ne _ hcL
    have h1 : F (algebraMap B L c) hcL = ((Module.length A (B ⧸ Ideal.span {c})).toNat : ℤ) := by
      simp only [hF]
      exact ordInt_norm_eq_length_quotient A B K L hAB c hc hnc
    have h2 : G (algebraMap B L c) hcL = ((Module.length A (B ⧸ Ideal.span {c})).toNat : ℤ) := by
      simp only [hG]
      exact sum_inertiaDeg_ordInt_eq_length_quotient A B L c hc (fun _ => hcL)
    rw [h1, h2]
  -- ratio representation y = bL / b'L with b, b' ∈ B nonzero.
  obtain ⟨b, b', hb'mem, hyeq⟩ := IsFractionRing.div_surjective (A := B) (K := L) y
  have hb'ne : b' ≠ 0 := nonZeroDivisors.ne_zero hb'mem
  have hb'L : algebraMap B L b' ≠ 0 := by
    rw [ne_eq, ← (algebraMap B L).map_zero]
    exact fun h => hb'ne (IsFractionRing.injective B L h)
  have hbeq : algebraMap B L b = y * algebraMap B L b' := by
    field_simp at hyeq; rw [mul_comm]; exact hyeq
  have hbL : algebraMap B L b ≠ 0 := by rw [hbeq]; exact mul_ne_zero hy hb'L
  have hbne : b ≠ 0 := by intro h; apply hbL; rw [h, (algebraMap B L).map_zero]
  -- additivity gives F(bL) = F y + F(b'L), G(bL) = G y + G(b'L).
  have hFy : F (algebraMap B L b) hbL = F y hy + F (algebraMap B L b') hb'L := by
    have h := hFmul y (algebraMap B L b') hy hb'L
    rw [hFcongr (algebraMap B L b) (y * algebraMap B L b') hbL (mul_ne_zero hy hb'L) hbeq]
    exact h
  have hGy : G (algebraMap B L b) hbL = G y hy + G (algebraMap B L b') hb'L := by
    have h := hGmul y (algebraMap B L b') hy hb'L
    rw [hGcongr (algebraMap B L b) (y * algebraMap B L b') hbL (mul_ne_zero hy hb'L) hbeq]
    exact h
  -- combine with key at b and b' to get F y = G y.
  have hFG_y : F y hy = G y hy := by
    have e1 : F (algebraMap B L b) hbL = G (algebraMap B L b) hbL := key b hbne hbL
    have e2 : F (algebraMap B L b') hb'L = G (algebraMap B L b') hb'L := key b' hb'ne hb'L
    omega
  have hxF : ordInt A x hx0 = F y hy := by simp only [hF]; subst hx; rfl
  rw [hxF, hFG_y]
