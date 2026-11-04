module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.PullbackCohomology
import StacksCore.Tactic.StacksAttribute

/-!
# Maps into the subquotients of `A` become `I^c`-divisible after twisting down

This file formalizes Stacks Tag 0GAC, the fourth lemma of the section *A bit of uniformity, III*
of the chapter *Local Cohomology* (Tag 0GA6).
-/

@[expose] public section

universe u

namespace Stacks.LocalCohomology.UniformityIII

open scoped TensorProduct

section Scalars

variable {A : Type u} [CommRing A] (I : Ideal A) (n q : ℕ)

/-- Multiplication by a scalar of `A/Iⁿ` on a fixed element `x` of the subquotient
`I^q/I^{q+n}`, as an `A`-linear map `A/Iⁿ → I^q/I^{q+n}`. It is well defined because
`Iⁿ·I^q ⊆ I^{q+n}`, so `Iⁿ` annihilates `I^q/I^{q+n}`. -/
noncomputable def powQuotScalar (x : powQuot I q n) : (A ⧸ I ^ n) →ₗ[A] powQuot I q n :=
  Submodule.liftQ _ (LinearMap.toSpanSingleton A (powQuot I q n) x) (by
    intro a ha
    simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    induction x using Submodule.Quotient.induction_on with
    | H y =>
      change (Submodule.Quotient.mk (a • y) : powQuot I q n) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      simp only [powSub, Submodule.mem_comap, Submodule.coe_subtype, SetLike.val_smul,
        smul_eq_mul]
      have h : a * (y : A) ∈ I ^ n * I ^ q := Ideal.mul_mem_mul ha y.2
      rw [← pow_add] at h
      exact Ideal.pow_le_pow_right (by omega) h)

/-- `powQuotScalar` sends the class of `a ∈ A` to `a • x`. -/
theorem powQuotScalar_apply_mk (x : powQuot I q n) (a : A) :
    powQuotScalar I n q x (Ideal.Quotient.mk (I ^ n) a) = a • x := rfl

/-- `powQuotScalar` turns multiplication by the class of `a ∈ A` into the action of `a`. -/
theorem powQuotScalar_mul (x : powQuot I q n) (a : A) (t : A ⧸ I ^ n) :
    powQuotScalar I n q x (Ideal.Quotient.mk (I ^ n) a * t) =
      a • powQuotScalar I n q x t := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [← map_mul, powQuotScalar_apply_mk, powQuotScalar_apply_mk, mul_smul]

/-- `powQuotScalar` is additive in the element `x` it multiplies. -/
theorem powQuotScalar_add (x y : powQuot I q n) (t : A ⧸ I ^ n) :
    powQuotScalar I n q (x + y) t =
      powQuotScalar I n q x t + powQuotScalar I n q y t := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [powQuotScalar_apply_mk, powQuotScalar_apply_mk, powQuotScalar_apply_mk, smul_add]

/-- `powQuotScalar` is `A`-homogeneous in the element `x` it multiplies. -/
theorem powQuotScalar_smul (a : A) (x : powQuot I q n) (t : A ⧸ I ^ n) :
    powQuotScalar I n q (a • x) t = a • powQuotScalar I n q x t := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [powQuotScalar_apply_mk, powQuotScalar_apply_mk, smul_comm]

/-- Any `A`-linear map between subquotients of `A` commutes with `powQuotScalar`, because the
scalar action of `A/Iⁿ` is induced by the `A`-action. The two instances used below are
`powQuotLe` (the twisting-down maps) and `powQuotSmul` (multiplication by an element of
`I^c`). -/
theorem map_powQuotScalar {r : ℕ} (F : powQuot I q n →ₗ[A] powQuot I r n) (x : powQuot I q n)
    (t : A ⧸ I ^ n) : F (powQuotScalar I n q x t) = powQuotScalar I n r (F x) t := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective t
  rw [powQuotScalar_apply_mk, map_smul, powQuotScalar_apply_mk]

end Scalars

/-- The twisting-down map from a twist to itself is the identity. -/
theorem powQuotLe_self {A : Type u} [CommRing A] (I : Ideal A) (n q : ℕ) (h : q ≤ q)
    (x : powQuot I q n) : powQuotLe I h x = x := by
  induction x using Submodule.Quotient.induction_on with
  | H z => rfl

section DualHom

variable {A : Type u} [CommRing A] (I : Ideal A) (n q : ℕ)
  {M : ModuleCat.{u} (A ⧸ I ^ n)}

/-- The homomorphism `M → I^q/I^{q+n}`, `z ↦ λ(z)·x`, determined by an element `x` of
`I^q/I^{q+n}` and an element `λ` of the dual `M^∨ = Hom_{A/Iⁿ}(M, A/Iⁿ)`.

This is the construction with which the proof of Tag 0GAC manufactures the maps `ψᵢ` from the
elements `τᵢ ∈ I^{n-(2+d)c}M^∨`: "`τᵢ` determines a homomorphism of modules
`ψᵢ : M → I^{n-(2+d)c}/I^{2n-(2+d)c}` using the evaluation map `M ⊗ M^∨ → A/Iⁿ`". -/
noncomputable def dualHom (lam : Module.Dual (A ⧸ I ^ n) M) (x : powQuot I q n) :
    resModule I n M →ₗ[A] powQuot I q n where
  toFun z := powQuotScalar I n q x (lam z)
  map_add' z w := by
    have h : lam (z + w) = lam z + lam w := map_add lam z w
    simp only [h, map_add]
  map_smul' a z := by
    have h : lam (a • z) = Ideal.Quotient.mk (I ^ n) a * lam z := by
      rw [ModuleCat.restrictScalars.smul_def]
      exact map_smul lam _ z
    simp only [h, powQuotScalar_mul, RingHom.id_apply]

/-- `dualHom I n q λ x` sends `z` to `λ(z)·x`. -/
theorem dualHom_apply (lam : Module.Dual (A ⧸ I ^ n) M) (x : powQuot I q n)
    (z : resModule I n M) : dualHom I n q lam x z = powQuotScalar I n q x (lam z) := rfl

/-- `dualHom` is `A`-linear in the element of `I^q/I^{q+n}`. -/
noncomputable def dualHomₗ (lam : Module.Dual (A ⧸ I ^ n) M) :
    powQuot I q n →ₗ[A] (resModule I n M →ₗ[A] powQuot I q n) where
  toFun x := dualHom I n q lam x
  map_add' x y := LinearMap.ext fun z => powQuotScalar_add I n q x y (lam z)
  map_smul' a x := LinearMap.ext fun z => powQuotScalar_smul I n q a x (lam z)

/-- `dualHomₗ I n q λ` sends `x` to `dualHom I n q λ x`. -/
@[simp] theorem dualHomₗ_apply (lam : Module.Dual (A ⧸ I ^ n) M) (x : powQuot I q n) :
    dualHomₗ I n q lam x = dualHom I n q lam x := rfl

/-- Postcomposing `dualHom` with an `A`-linear map of subquotients moves that map onto the
element: this is `map_powQuotScalar` read as an identity of homomorphisms out of `M`. -/
theorem comp_dualHom {r : ℕ} (F : powQuot I q n →ₗ[A] powQuot I r n)
    (lam : Module.Dual (A ⧸ I ^ n) M) (x : powQuot I q n) :
    F.comp (dualHom I n q lam x) = dualHom I n r lam (F x) :=
  LinearMap.ext fun z => map_powQuotScalar I n q F x (lam z)

end DualHom

section Divisible

variable {A : Type u} [CommRing A] (I : Ideal A) (n c : ℕ) {g f : ℕ}

/-- Multiplication by an element of the ideal `I^c`, as a map `I^g/I^{g+n} → I^f/I^{f+n}` for
`f = g + c`. This is `powQuotSmul` with the element and its membership proof packaged into the
subtype `I^c`, so that the map depends on no proof argument. -/
noncomputable def powQuotSmulIdeal (hgf : g + c = f) (a : (I ^ c : Ideal A)) :
    powQuot I g n →ₗ[A] powQuot I f n :=
  powQuotSmul I a.2 hgf

/-- `powQuotSmulIdeal` at `⟨a, ha⟩` is multiplication by `a`, i.e. `powQuotSmul I ha hgf`. -/
theorem powQuotSmulIdeal_eq (hgf : g + c = f) {a : A} (ha : a ∈ (I ^ c : Ideal A)) :
    powQuotSmulIdeal I n c hgf ⟨a, ha⟩ = powQuotSmul (n := n) I ha hgf := rfl

/-- The `A`-submodule of `Hom_A(M, I^f/I^{f+n})` consisting of the maps of the form
`∑ aᵢψᵢ` with `aᵢ ∈ I^c` and `ψᵢ : M → I^g/I^{g+n}`, for `f = g + c`. This is the shape of the
conclusion of Stacks Tag 0GAC.

It is a submodule and not merely a set because the single-term maps `aψ` are already closed
under multiplication by a scalar of `A` (absorb the scalar into `ψ`), so the span adds nothing
beyond finite sums; `exists_sum_of_mem_divisibleMaps` turns membership back into an explicit
finite sum. -/
noncomputable def divisibleMaps (hgf : g + c = f) (M : ModuleCat.{u} (A ⧸ I ^ n)) :
    Submodule A (resModule I n M →ₗ[A] powQuot I f n) :=
  Submodule.span A {ξ | ∃ (a : (I ^ c : Ideal A)) (ψ : resModule I n M →ₗ[A] powQuot I g n),
    ξ = (powQuotSmulIdeal I n c hgf a).comp ψ}

/-- A single term `aψ`, with `a ∈ I^c` and `ψ : M → I^g/I^{g+n}`, lies in `divisibleMaps`. -/
theorem mem_divisibleMaps_of_single (hgf : g + c = f) {M : ModuleCat.{u} (A ⧸ I ^ n)}
    (a : (I ^ c : Ideal A)) (ψ : resModule I n M →ₗ[A] powQuot I g n) :
    (powQuotSmulIdeal I n c hgf a).comp ψ ∈ divisibleMaps I n c hgf M :=
  Submodule.subset_span ⟨a, ψ, rfl⟩

/-- `I^f/I^{f+n}` is generated as an `A`-module by the images of the multiplication maps
`I^g/I^{g+n} → I^f/I^{f+n}` by the elements of `I^c`, since `I^f = I^g·I^c` for `f = g + c`.

This is the step "write `τ = ∑ aᵢτᵢ` with `τᵢ ∈ I^{n-(2+d)c}M^∨`" of the proof of Tag 0GAC,
carried out on the subquotients of `A` rather than on `M^∨`. -/
theorem mem_span_powQuotSmulIdeal (hgf : g + c = f) (x : powQuot I f n) :
    x ∈ Submodule.span A {w : powQuot I f n |
      ∃ (a : (I ^ c : Ideal A)) (y : powQuot I g n), w = powQuotSmulIdeal I n c hgf a y} := by
  have hJ : (I ^ g : Ideal A) * (I ^ c : Ideal A) = I ^ f := by rw [← pow_add, hgf]
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨z, hz⟩ := z
    refine Submodule.mul_induction_on'
      (C := fun r hr => (Submodule.Quotient.mk ⟨r, hJ ▸ hr⟩ : powQuot I f n) ∈ _)
      ?_ ?_ (show z ∈ (I ^ g : Ideal A) * (I ^ c : Ideal A) from hJ ▸ hz)
    · intro m hm k hk
      refine Submodule.subset_span ⟨⟨k, hk⟩, Submodule.Quotient.mk ⟨m, hm⟩, ?_⟩
      exact (powQuotSmul_mk I hk hgf ⟨m, hm⟩ ⟨m * k, _⟩ (mul_comm m k)).symm
    · intro x hx y hy hx' hy'
      exact Submodule.add_mem _ hx' hy'

/-- Every homomorphism of the form `z ↦ λ(z)·x` into `I^f/I^{f+n}` is of the form `∑ aᵢψᵢ`:
decompose `x` along `I^f = I^g·I^c` and move the factors onto the maps. -/
theorem dualHom_mem_divisibleMaps (hgf : g + c = f) {M : ModuleCat.{u} (A ⧸ I ^ n)}
    (lam : Module.Dual (A ⧸ I ^ n) M) (x : powQuot I f n) :
    dualHom I n f lam x ∈ divisibleMaps I n c hgf M := by
  have hle : Submodule.span A {w : powQuot I f n |
        ∃ (a : (I ^ c : Ideal A)) (y : powQuot I g n), w = powQuotSmulIdeal I n c hgf a y} ≤
      (divisibleMaps I n c hgf M).comap (dualHomₗ I n f lam) := by
    rw [Submodule.span_le]
    rintro w ⟨a, y, rfl⟩
    simp only [Submodule.mem_comap, SetLike.mem_coe, dualHomₗ_apply]
    rw [← comp_dualHom I n g (powQuotSmulIdeal I n c hgf a) lam y]
    exact mem_divisibleMaps_of_single I n c hgf a _
  exact hle (mem_span_powQuotSmulIdeal I n c hgf x)

/-- Membership in `divisibleMaps` unwound into the explicit form `∑ aᵢψᵢ` of Tag 0GAC: a
natural number of terms, scalars `aᵢ ∈ I^c` and maps `ψᵢ : M → I^g/I^{g+n}`. -/
theorem exists_sum_of_mem_divisibleMaps (hgf : g + c = f) {M : ModuleCat.{u} (A ⧸ I ^ n)}
    {ξ : resModule I n M →ₗ[A] powQuot I f n} (hξ : ξ ∈ divisibleMaps I n c hgf M) :
    ∃ (N : ℕ) (a : Fin N → A) (ha : ∀ i, a i ∈ I ^ c)
      (ψ : Fin N → (resModule I n M →ₗ[A] powQuot I g n)),
      ξ = ∑ i, (powQuotSmul I (ha i) hgf).comp (ψ i) := by
  obtain ⟨N, t, w, hsum⟩ := Submodule.mem_span_set'.mp hξ
  choose a ψ hw using fun i => (w i).2
  refine ⟨N, fun i => ((a i : A)), fun i => (a i).2, fun i => t i • ψ i, ?_⟩
  rw [← hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hw i]
  ext z
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
  rfl

end Divisible

/-- The data and the standing hypotheses used by Stacks Tag 0GAC: a `TwistedModuleSituation`
together with the *evaluation dictionary* of Remark 0GAB, which turns a section of
`p^*(M^∨)(q)` into a homomorphism `M → I^q/I^{q+n}`.

For `z ∈ M` the source forms the evaluation `e_z : M^∨ → A/Iⁿ`, pulls it back to
`p^*e_z : p^*(M^∨) → 𝒪_{Yₙ}` and evaluates a section `σ'` of `p^*(M^∨)(q)` against it,
landing in `Γ(Y_n, 𝒪_{Yₙ}(q))`, which Tag 0GA7(2) identifies with `I^q/I^{q+n}` for
`q ≥ q(S)`. The resulting map `ev` is carried here as data, together with the two
compatibilities the proof of Tag 0GAC uses: it is natural in the twist, and on the canonical
sections coming from `I^q ⊗_A M^∨` it is the evaluation pairing `dualHom`. The restriction to
`q ≥ q(S)` is exactly what makes the target `I^q/I^{q+n}` rather than `Γ(Y_n, 𝒪_{Yₙ}(q))`.

Like every other geometric input to this section (`TwistedModuleSituation.dotted`,
`ModuleSituation.freeIso`, …) the dictionary is data rather than a theorem: `𝒪_{Yₙ}(n)` being
invertible, the functoriality of `can` and Tag 0GA7(2) are inputs the library does not carry.
See `affineDualSituation` for a non-degenerate witness. -/
structure DualSituation (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (n c : ℕ) extends TwistedModuleSituation A I n c where
  /-- Evaluating a section of `p^*(M^∨)(q)` against the elements of `M`, as a map
  `H⁰(X, p^*(M^∨)(q)) → Hom_A(M, I^q/I^{q+n})`, defined for `q ≥ q(S)`. -/
  ev : ∀ (M : ANCModule I n c) (q : ℕ), toSituation.q₀ ≤ q →
    toModuleSituation.H M.dual 0 (q : ℤ) →ₗ[A] (resModule I n M.1 →ₗ[A] powQuot I q n)
  /-- The dictionary is natural in the twist: evaluating the image of a section under
  `H⁰(X, p^*(M^∨)(q)) → H⁰(X, p^*(M^∨)(q'))` is evaluating the section and then composing
  with `I^q/I^{q+n} → I^{q'}/I^{q'+n}`. -/
  ev_Htr : ∀ (M : ANCModule I n c) (q q' : ℕ) (hq : toSituation.q₀ ≤ q)
      (hq' : toSituation.q₀ ≤ q') (h : q' ≤ q) (h' : (q' : ℤ) ≤ (q : ℤ))
      (x : toModuleSituation.H M.dual 0 (q : ℤ)),
    ev M q' hq' (toTwistedModuleSituation.Htr M.dual 0 (q : ℤ) (q' : ℤ) h' x) =
      (powQuotLe I h).comp (ev M q hq x)
  /-- On the canonical sections the dictionary is the evaluation pairing: the section of
  `p^*(M^∨)(q)` attached to `x ⊗ λ` with `x ∈ I^q/I^{q+n}` and `λ ∈ M^∨` evaluates on `z ∈ M`
  to `λ(z)·x`. -/
  ev_secM : ∀ (M : ANCModule I n c) (q : ℕ) (hq : toSituation.q₀ ≤ q) (x : powQuot I q n)
      (lam : resModule I n (M.dual).1),
    ev M q hq (toTwistedModuleSituation.secM M.dual q (x ⊗ₜ[A] lam)) = dualHom I n q lam x

namespace DualSituation

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A} {n c : ℕ}
  (S : DualSituation A I n c)

/-- The evaluation of a section of `p^*(M^∨)(f)` that comes from `I^f ⊗_A M^∨` is of the form
`∑ aᵢψᵢ` with `aᵢ ∈ I^c` and `ψᵢ : M → I^g/I^{g+n}`, for `f = g + c`.

This is the last step of the proof of Tag 0GAC: the element `τ ∈ I^{n-(1+d)c}M^∨` is written
`τ = ∑ aᵢτᵢ` with `τᵢ ∈ I^{n-(2+d)c}M^∨`, and each `τᵢ` determines a `ψᵢ` by the evaluation
map. Here the decomposition happens on the subquotients of `A` and is
`mem_span_powQuotSmulIdeal`, while the passage from `τᵢ` to `ψᵢ` is `ev_secM`. -/
theorem ev_secM_mem_divisibleMaps (M : ANCModule I n c) {g f : ℕ} (hgf : g + c = f)
    (hq : S.q₀ ≤ f) (t : powTensor I n f (M.dual).1) :
    S.ev M f hq (S.secM M.dual f t) ∈ divisibleMaps I n c hgf M.1 := by
  induction t using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero]
    exact Submodule.zero_mem _
  | tmul x lam =>
    rw [S.ev_secM M f hq x lam]
    exact dualHom_mem_divisibleMaps I n c hgf lam x
  | add t₁ t₂ h₁ h₂ =>
    rw [map_add, map_add]
    exact Submodule.add_mem _ h₁ h₂

/-- The level drop of the proof of Tag 0GAC: from the level-`e = n - 2c` section `σ'` of
`p^*(M^∨)` the proof produces, at level `f`, a section that comes from `I^f ⊗_A M^∨`.

Here `k` is `d - 1` for `d ≥ 1` and `0` for `d = 0`, i.e. `k + 1 = max(d, 1)`, and `f + kc = e`.

* For `d ≥ 2` this is Tag 0GAA, clause (5) applied to the `(A, n, c)`-module `M^∨`: the image
  of `H⁰(X, p^*(M^∨)(e))` in `H⁰(X, p^*(M^∨)(e - (d-1)c))` lies in the image of the canonical
  map out of `I^{e-(d-1)c} ⊗_A M^∨`, and `e - (d-1)c = f`. This is the only place the `(d-1)c`
  drop comes from.
* For `d ≤ 1` one has `k = 0` and `f = e`, and this is Tag 0GAA, clause (4) applied to `M^∨`:
  the canonical map `I^e ⊗_A M^∨ → H⁰(X, p^*(M^∨)(e))` is surjective, so no drop is needed. -/
theorem exists_ev_secM_eq (M : ANCModule I n c) {e f k : ℕ}
    (hk : max S.d 1 = k + 1) (he : f + k * c = e) (hq : S.q₀ ≤ f)
    (σ' : S.H M.dual 0 (e : ℤ)) :
    ∃ t : powTensor I n f (M.dual).1,
      S.ev M f hq (S.secM M.dual f t) =
        (powQuotLe I (Nat.le.intro he)).comp (S.ev M e (hq.trans (Nat.le.intro he)) σ') := by
  rcases le_or_gt S.d 1 with hd | hd
  · have hk0 : k = 0 := by rw [max_eq_right hd] at hk; omega
    subst hk0
    obtain rfl : e = f := by simpa using he.symm
    obtain ⟨t, ht⟩ := S.surjective_secM M.dual hd hq σ'
    refine ⟨t, ?_⟩
    rw [ht]
    exact LinearMap.ext fun z => (powQuotLe_self I n e (le_refl e) _).symm
  · have hdk : S.d = k + 1 := by rwa [max_eq_left (by omega : 1 ≤ S.d)] at hk
    have hk1 : 1 ≤ k := by omega
    have hfe : (f : ℤ) ≤ (e : ℤ) := by exact_mod_cast Nat.le.intro he
    have hr : (f : ℤ) + k * c = (e : ℤ) := by exact_mod_cast he
    have hqe : (S.q₀ : ℤ) + k * c ≤ (e : ℤ) := by
      have : (S.q₀ : ℤ) ≤ (f : ℤ) := by exact_mod_cast hq
      linarith
    obtain ⟨t, ht⟩ :=
      S.range_Htr_le M.dual hfe hk1 hdk.symm hr hqe ⟨σ', rfl⟩
    refine ⟨t, ?_⟩
    rw [ht]
    exact S.ev_Htr M e f (hq.trans (Nat.le.intro he)) hq (Nat.le.intro he) hfe σ'

/-- **Stacks Project, Tag 0GAC.** With `q₀ = q(S)` and `d = d(S)`, let `M` be an
`(A, n, c)`-module and `φ : M → Iⁿ/I^{2n}` an `A`-linear map. Write `D = max(d, 1)` and assume
`n ≥ q₀ + (1 + D)c` and `n ≥ (2 + D)c`. Then the composition

`M --φ--> Iⁿ/I^{2n} → I^{n-(1+D)c}/I^{2n-(1+D)c}`

is of the form `∑ aᵢψᵢ` with `aᵢ ∈ I^c` and `ψᵢ : M → I^{n-(2+D)c}/I^{2n-(2+D)c}`.

The levels are carried as parameters so that no truncated subtraction appears in a type:
`k + 1 = D`, `g + c = f`, `f + kc = e` and `e + 2c = n`, so that `f = n - (1 + D)c`,
`g = n - (2 + D)c` and `e = n - 2c`; the two numerical hypotheses of the source are the
existence of `g` as a natural number (`n ≥ (2 + D)c`) and `q₀ ≤ f` (`n ≥ q₀ + (1 + D)c`).

**Deviation from the source, at `d = 0`.** The source writes `d` where this statement writes
`D = max(d, 1)`, and adds for `d = 0` the hypothesis `n ≥ q₀ + 2c`. For `d ≥ 1` the two agree
exactly. For `d = 0` the source's own argument does not reach the level it asserts: it produces
`σ'` at level `n - 2c` — the cost of factoring through `can : p^*(M^∨) → (p^*M)^∨`, whose
kernel and cokernel are supported on `Y_c`, and which is independent of `d` — and then applies
clause (4) of Tag 0GAA at that level, which gives no further drop, so the argument ends at
`n - 2c` while the statement asserts `n - (1 + 0)c = n - c`, a discrepancy of `c` in the wrong
direction. The source's extra hypothesis `n ≥ q₀ + 2c` for `d = 0` is precisely what makes
clause (4) applicable at `n - 2c`, which corroborates that `n - 2c` is the level reached. So
for `d = 0` the levels stated here are the ones the argument supports, namely the `d = 1`
numbers `2c` and `3c`; the hypothesis `n ≥ 3c` this needs is not implied by the source's `d = 0`
hypotheses and is therefore part of `n ≥ (2 + D)c` above. Twisting the identity proved here
down by `c` recovers the source's numbering, so the source's `d = 0` form is strictly stronger
than what its argument establishes.

**The one open input.** The level-`(n - 2c)` section `σ'` is a hypothesis, not a conclusion:
producing it is the duality step of the source, which rests on the kernel and cokernel of `can`
being scheme-theoretically supported on `Y_c` — a statement about the blowup situation that
`Stacks.SheafOfModules.PullbackDual` (Tag 0GAB) explicitly does not prove. Everything after it
is derived: the `(d-1)c` drop is Tag 0GAA clause (5) for `d ≥ 2` and clause (4) for `d ≤ 1`
(`exists_ev_secM_eq`), and the passage from the resulting element of `I^f ⊗_A M^∨` to the sum
`∑ aᵢψᵢ` is `ev_secM_mem_divisibleMaps`. -/
@[stacks 0GAC "with max(d, 1) in place of d, since at d = 0 the source's own argument reaches \
only level n - 2c while the source states n - c; its one open input is the level-(n-2c) \
section σ' of p^*(M^∨) produced by factoring through can, hypothesis `hσ`"]
theorem exists_sum_powQuotSmul (M : ANCModule I n c)
    (φ : resModule I n M.1 →ₗ[A] powQuot I n n) {g f e k : ℕ}
    (hgf : g + c = f) (hk : max S.d 1 = k + 1) (he : f + k * c = e) (hen : e + 2 * c = n)
    (hq : S.q₀ ≤ f) (σ' : S.H M.dual 0 (e : ℤ))
    (hσ : S.ev M e (hq.trans (Nat.le.intro he)) σ' =
      (powQuotLe I (Nat.le.intro hen)).comp φ) :
    ∃ (N : ℕ) (a : Fin N → A) (ha : ∀ i, a i ∈ I ^ c)
      (ψ : Fin N → (resModule I n M.1 →ₗ[A] powQuot I g n)),
      (powQuotLe I ((Nat.le.intro he).trans (Nat.le.intro hen))).comp φ =
        ∑ i, (powQuotSmul I (ha i) hgf).comp (ψ i) := by
  obtain ⟨t, ht⟩ := S.exists_ev_secM_eq M hk he hq σ'
  have key : (powQuotLe I ((Nat.le.intro he).trans (Nat.le.intro hen))).comp φ =
      S.ev M f hq (S.secM M.dual f t) := by
    rw [ht, hσ]
    exact LinearMap.ext fun z =>
      (powQuotLe_powQuotLe I n (Nat.le.intro hen) (Nat.le.intro he) (φ z)).symm
  rw [key]
  exact exists_sum_of_mem_divisibleMaps I n c hgf (S.ev_secM_mem_divisibleMaps M hgf hq t)

end DualSituation

section AffineDualWitness

variable {A : Type u} [CommRing A] (I : Ideal A) (n c : ℕ)

/-- An element of `resModule I n (M^∨)` read as an `A/Iⁿ`-linear functional on `M`; the two
types are the same, the first carrying the `A`-module structure along `A → A/Iⁿ`. -/
abbrev asDual {M : ModuleCat.{u} (A ⧸ I ^ n)}
    (lam : resModule I n (ModuleCat.of (A ⧸ I ^ n) (Module.Dual (A ⧸ I ^ n) M))) :
    Module.Dual (A ⧸ I ^ n) M := lam

/-- The evaluation dictionary in the case of an isomorphism `p`, where `H⁰(X, p^*(M^∨)(q))` is
`I^q ⊗_A M^∨`: the canonical map `(I^q/I^{q+n}) ⊗_A M^∨ → Hom_A(M, I^q/I^{q+n})` sending
`x ⊗ λ` to `z ↦ λ(z)·x`. -/
noncomputable def dualHomTensorLift (q : ℕ) (M : ModuleCat.{u} (A ⧸ I ^ n)) :
    powTensor I n q (ModuleCat.of (A ⧸ I ^ n) (Module.Dual (A ⧸ I ^ n) M)) →ₗ[A]
      (resModule I n M →ₗ[A] powQuot I q n) :=
  TensorProduct.lift
    (LinearMap.flip
      { toFun := fun lam => dualHomₗ I n q (asDual I n lam)
        map_add' := fun lam mu => by
          refine LinearMap.ext fun x => LinearMap.ext fun z => ?_
          change powQuotScalar I n q x (asDual I n lam z + asDual I n mu z) =
            powQuotScalar I n q x (asDual I n lam z) + powQuotScalar I n q x (asDual I n mu z)
          rw [map_add]
        map_smul' := fun a lam => by
          refine LinearMap.ext fun x => LinearMap.ext fun z => ?_
          change powQuotScalar I n q x (Ideal.Quotient.mk (I ^ n) a * asDual I n lam z) =
            a • powQuotScalar I n q x (asDual I n lam z)
          rw [powQuotScalar_mul] })

/-- `dualHomTensorLift` sends `x ⊗ λ` to the homomorphism `z ↦ λ(z)·x`. -/
@[simp] theorem dualHomTensorLift_tmul (q : ℕ) (M : ModuleCat.{u} (A ⧸ I ^ n))
    (x : powQuot I q n)
    (lam : resModule I n (ModuleCat.of (A ⧸ I ^ n) (Module.Dual (A ⧸ I ^ n) M))) :
    dualHomTensorLift I n q M (x ⊗ₜ[A] lam) = dualHom I n q (asDual I n lam) x :=
  TensorProduct.lift.tmul _ _

/-- The dictionary of the affine witness is natural in the twist. -/
theorem dualHomTensorLift_powTensorLe {q q' : ℕ} (h : q' ≤ q) (M : ModuleCat.{u} (A ⧸ I ^ n))
    (t : powTensor I n q (ModuleCat.of (A ⧸ I ^ n) (Module.Dual (A ⧸ I ^ n) M))) :
    dualHomTensorLift I n q' M
        (powTensorLe I n (ModuleCat.of (A ⧸ I ^ n) (Module.Dual (A ⧸ I ^ n) M)) h t) =
      (powQuotLe I h).comp (dualHomTensorLift I n q M t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.comp_zero]
  | tmul x lam =>
    rw [powTensorLe, LinearMap.rTensor_tmul, dualHomTensorLift_tmul, dualHomTensorLift_tmul,
      comp_dualHom]
  | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, LinearMap.comp_add]

variable [IsNoetherianRing A]

/-- The `DualSituation` of Tag 0GA6 built on `affineTwistedModuleSituation`: the blowing up is
an isomorphism, so `H⁰(X, p^*(M^∨)(q))` is `I^q ⊗_A M^∨` and the evaluation dictionary of
Remark 0GAB is the canonical map `(I^q/I^{q+n}) ⊗_A M^∨ → Hom_A(M, I^q/I^{q+n})`.

Unlike `topTwistedModuleSituation` this witness is not degenerate; see
`nontrivial_affineTwistedModuleSituation_H`,
`bijective_affineTwistedModuleSituation_secM` and `not_free_quotPowANCModule`. -/
noncomputable def affineDualSituation (hcn : c ≤ n) : DualSituation A I n c :=
  { affineTwistedModuleSituation I n c hcn with
    ev := fun M q _ => dualHomTensorLift I n q M.1
    ev_Htr := fun M _q _q' _ _ h _ x => dualHomTensorLift_powTensorLe I n h M.1 x
    ev_secM := fun _ _ _ _ _ => rfl }

/-- The evaluation dictionary of `affineDualSituation` at level `q` is `dualHomTensorLift`. -/
@[simp] theorem affineDualSituation_ev (hcn : c ≤ n) (M : ANCModule I n c) (q : ℕ)
    (hq : (affineDualSituation I n c hcn).q₀ ≤ q) :
    (affineDualSituation I n c hcn).ev M q hq = dualHomTensorLift I n q M.1 := rfl

/-- In the affine witness the open input `hσ` of Tag 0GAC is satisfied by every `φ` of the form
`z ↦ λ(z)·y`: the section `σ'` is `y ⊗ λ` twisted down to level `e`. -/
theorem affineDualSituation_ev_tmul (hcn : c ≤ n) (M : ANCModule I n c) {e : ℕ} (hen : e ≤ n)
    (hq : (affineDualSituation I n c hcn).q₀ ≤ e)
    (lam : resModule I n (M.dual).1) (y : powQuot I n n) :
    (affineDualSituation I n c hcn).ev M e hq (powQuotLe I hen y ⊗ₜ[A] lam) =
      (powQuotLe I hen).comp (dualHom I n n (asDual I n lam) y) :=
  (dualHomTensorLift_tmul I n e M.1 (powQuotLe I hen y) lam).trans
    (comp_dualHom I n n (powQuotLe I hen) (asDual I n lam) y).symm

end AffineDualWitness

section CyclicANCModules

variable {A : Type u} [CommRing A] (I : Ideal A) (n j q : ℕ)

/-- The cyclic `A ⧸ Iⁿ`-module `(A/Iⁿ)/I^j(A/Iⁿ)`. For `j = c` it is the module
`quotPowANCModule` of `PullbackCohomology`; the `(A, n, c)`-modules used here need `j` larger
than `c`, since for `j ≤ c` every map `M → Iⁿ/I^{2n}` dies on twisting down to level
`n - (1 + D)c`. -/
abbrev quotPowModule : ModuleCat.{u} (A ⧸ I ^ n) :=
  ModuleCat.of (A ⧸ I ^ n) ((A ⧸ I ^ n) ⧸ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ j))

/-- The homomorphism `(A/Iⁿ)/I^j(A/Iⁿ) → I^q/I^{q+n}` sending the class of `r ∈ A/Iⁿ` to
`r·x`, for an element `x` of `I^q/I^{q+n}` annihilated by `I^j`. -/
noncomputable def quotPowHom (x : powQuot I q n) (hx : ∀ a ∈ (I ^ j : Ideal A), a • x = 0) :
    resModule I n (quotPowModule I n j) →ₗ[A] powQuot I q n where
  toFun z := Quotient.liftOn z (fun r => powQuotScalar I n q x r) (by
    intro a b hab
    have hmem : a - b ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ j) :=
      (Submodule.quotientRel_def _).mp hab
    obtain ⟨y, hy, hya⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hmem
    refine sub_eq_zero.mp ?_
    rw [← map_sub, ← hya, powQuotScalar_apply_mk, hx y hy])
  map_add' z w := by
    induction z using Submodule.Quotient.induction_on with
    | H a =>
      induction w using Submodule.Quotient.induction_on with
      | H b => exact map_add (powQuotScalar I n q x) a b
  map_smul' a z := by
    induction z using Submodule.Quotient.induction_on with
    | H b =>
      change powQuotScalar I n q x (Ideal.Quotient.mk (I ^ n) a * b) =
        (RingHom.id A) a • powQuotScalar I n q x b
      rw [powQuotScalar_mul, RingHom.id_apply]

/-- `quotPowHom` sends the class of `r ∈ A/Iⁿ` to `r·x`. -/
@[simp] theorem quotPowHom_mk (x : powQuot I q n) (hx : ∀ a ∈ (I ^ j : Ideal A), a • x = 0)
    (r : A ⧸ I ^ n) :
    quotPowHom I n j q x hx (Submodule.Quotient.mk r) = powQuotScalar I n q x r := rfl

/-- The `A/Iⁿ`-linear functional on `(A/Iⁿ)/I^j(A/Iⁿ)` given by multiplication by the class of
an element of `I^i`, which is well defined as soon as `i + j ≥ n`. -/
noncomputable def quotPowDual {i : ℕ} {t : A} (ht : t ∈ (I ^ i : Ideal A)) (hij : n ≤ i + j) :
    Module.Dual (A ⧸ I ^ n) (quotPowModule I n j) :=
  Submodule.liftQ _ (LinearMap.lsmul (A ⧸ I ^ n) (A ⧸ I ^ n) (Ideal.Quotient.mk (I ^ n) t))
    (by
      intro u hu
      obtain ⟨b, hb, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hu
      have h : t * b ∈ (I ^ n : Ideal A) := by
        have := Ideal.mul_mem_mul ht hb
        rw [← pow_add] at this
        exact Ideal.pow_le_pow_right hij this
      simp only [LinearMap.mem_ker, LinearMap.lsmul_apply, smul_eq_mul, ← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.2 h)

/-- `quotPowDual` sends the class of `r ∈ A/Iⁿ` to `t·r`. -/
@[simp] theorem quotPowDual_mk {i : ℕ} {t : A} (ht : t ∈ (I ^ i : Ideal A)) (hij : n ≤ i + j)
    (r : A ⧸ I ^ n) :
    quotPowDual I n j ht hij (Submodule.Quotient.mk r) = Ideal.Quotient.mk (I ^ n) t * r := rfl

/-- Multiplication by an element of `I^c` kills `(A/Iⁿ)/I^j(A/Iⁿ)` up to a factorization
through the free module `A/Iⁿ`, so the module is `I^c/Iⁿ`-projective by Tag 0G93 as soon as
`j + c ≥ n`: the map `z ↦ az` lifts to `A/Iⁿ` because `I^{j+c} ⊆ Iⁿ`. -/
theorem isIProjective_quotient_of_mul_eq_zero {R : Type u} [CommRing R] (J K : Ideal R)
    (h : ∀ a ∈ J, ∀ b ∈ K, a * b = 0) : Module.IsIProjective R J (R ⧸ K) := fun a ha =>
  FactorsThroughProj.mk'
    (Submodule.liftQ K (LinearMap.lsmul R R a) (fun b hb => by
      simp only [LinearMap.mem_ker, LinearMap.lsmul_apply, smul_eq_mul]
      exact h a ha b hb))
    K.mkQ
    (LinearMap.ext fun z => by
      induction z using Submodule.Quotient.induction_on with
      | H w => rfl)

/-- `(A/Iⁿ)/I^j(A/Iⁿ)` is an `(A, n, c)`-module when `j + c ≥ n`. -/
theorem isANCModule_quotPowModule {c : ℕ} (hj : n ≤ j + c) :
    IsANCModule I n c (quotPowModule I n j) :=
  ⟨Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _),
    isIProjective_quotient_of_mul_eq_zero _ _ (by
      intro a ha b hb
      obtain ⟨y, hy, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 ha
      obtain ⟨z, hz, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hb
      have h : y * z ∈ (I ^ n : Ideal A) := by
        have := Ideal.mul_mem_mul hy hz
        rw [← pow_add] at this
        exact Ideal.pow_le_pow_right (by omega) this
      rw [← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.2 h)⟩

/-- `(A/Iⁿ)/I^j(A/Iⁿ)` as an `(A, n, c)`-module, for `j + c ≥ n`. -/
noncomputable def quotPowANCModule' (c : ℕ) (hj : n ≤ j + c) : ANCModule I n c :=
  ⟨quotPowModule I n j, isANCModule_quotPowModule I n j hj⟩

end CyclicANCModules

end Stacks.LocalCohomology.UniformityIII

end
