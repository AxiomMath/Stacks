module

public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Étale algebras commute with products of modules over residue fields

Let `C` be an étale `R`-algebra and `(Vᵢ)` a family of `R`-modules, each `Vᵢ` killed by a maximal
ideal `𝔫ᵢ` of `R`. Then the canonical map `C ⊗[R] ∏ᵢ Vᵢ → ∏ᵢ (C ⊗[R] Vᵢ)` is bijective. For an
arbitrary flat `C` this fails (`C = R[x]` and `R = Vᵢ = k` give `(∏ k)[x] ≠ ∏ k[x]`); what makes it
work is a uniform bound on the fibres `κ(𝔫ᵢ) ⊗[R] C`.

The proof follows the plan of the special-tower route to the effectivity hypothesis of Stacks
0D5A (piece (B)):

* localization away from `g` commutes with a product of modules `Wᵢ` as soon as `g` satisfies a
  uniform *Fitting bound* `g ^ d ∈ g ^ (d + 1) A` modulo the annihilator of every `Wᵢ`
  (`Stacks.C1590Private.isLocalizedModule_pi`);
* tensoring with a finite free module commutes with products
  (`Stacks.C1590Private.bijective_piRightHom_of_free`);
* for `B = R[x]/(f)` with `f` monic, the fibres `κ(𝔫ᵢ) ⊗ B` have dimension `deg f`, which gives
  the Fitting bound `d = deg f` for every `g ∈ B`, so the statement passes to `B[1/g]`, hence to
  every standard étale algebra;
* for `C` étale the fibres `κ(𝔫ᵢ) ⊗ C` are finite products of fields, which gives the Fitting
  bound `d = 1` for every `g ∈ C`, so the statement is local on `Spec C`
  (`Stacks.C1590Private.bijective_piRightHom_of_span`), and `C` is Zariski locally standard étale
  (`Algebra.IsEtaleAt.exists_isStandardEtale`).

## Main results

* `Stacks.C1590Private.bijective_piRightHom_of_etale`: the statement above.

## References

* [Stacks Project, Tag 00UE](https://stacks.math.columbia.edu/tag/00UE) (local structure of
  étale ring maps)
-/

@[expose] public section

open TensorProduct

universe u

namespace Stacks.C1590Private

section PiLocalization

variable {A : Type*} [CommRing A] (g : A)

/-- Iterating a Fitting bound: `g ^ d ≡ g ^ (d + 1) a` gives `g ^ d ≡ g ^ (d + k) a ^ k`. -/
theorem sub_pow_mul_pow_mem_annihilator {M : Type*} [AddCommGroup M] [Module A M] {d : ℕ}
    {a : A} (h : g ^ d - g ^ (d + 1) * a ∈ Module.annihilator A M) (k : ℕ) :
    g ^ d - g ^ (d + k) * a ^ k ∈ Module.annihilator A M := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : g ^ d - g ^ (d + (k + 1)) * a ^ (k + 1) =
        (g ^ d - g ^ (d + k) * a ^ k) + g ^ k * a ^ k * (g ^ d - g ^ (d + 1) * a) := by ring
    rw [e]
    exact Submodule.add_mem _ ih (Ideal.mul_mem_left _ _ h)

/-- The iterated Fitting bound, applied to an element. -/
theorem pow_smul_eq_of_mem_annihilator {M : Type*} [AddCommGroup M] [Module A M] {d : ℕ}
    {a : A} (h : g ^ d - g ^ (d + 1) * a ∈ Module.annihilator A M) (k : ℕ) (w : M) :
    g ^ d • w = (g ^ (d + k) * a ^ k) • w := by
  rw [← sub_eq_zero, ← sub_smul]
  exact Module.mem_annihilator.mp (sub_pow_mul_pow_mem_annihilator g h k) w

variable {ι : Type*} {W W' : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module A (W i)]
  [∀ i, AddCommGroup (W' i)] [∀ i, Module A (W' i)]

/-- Localization away from `g` commutes with a product of modules on which `g` satisfies a
uniform Fitting bound `g ^ d ∈ g ^ (d + 1) A` (modulo the annihilator). -/
theorem isLocalizedModule_pi (ℓ : ∀ i, W i →ₗ[A] W' i)
    [∀ i, IsLocalizedModule (.powers g) (ℓ i)] (d : ℕ)
    (hd : ∀ i, ∃ a : A, g ^ d - g ^ (d + 1) * a ∈ Module.annihilator A (W i)) :
    IsLocalizedModule (.powers g) (LinearMap.pi fun i => ℓ i ∘ₗ LinearMap.proj i) where
  map_units s := by
    have hs : ∀ i, Function.Bijective (algebraMap A (Module.End A (W' i)) s) := fun i =>
      (Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units (ℓ i) s)
    rw [Module.End.isUnit_iff]
    refine ⟨fun x y hxy => funext fun i => (hs i).1 ?_, fun y => ?_⟩
    · simpa only [Module.algebraMap_end_apply, Pi.smul_apply] using congrFun hxy i
    · choose x hx using fun i => (hs i).2 (y i)
      exact ⟨x, funext fun i => by
        simpa only [Module.algebraMap_end_apply, Pi.smul_apply] using hx i⟩
  surj y := by
    choose a ha using hd
    have key : ∀ i, ∃ z : W i, ℓ i z = y i := by
      intro i
      obtain ⟨⟨w, s⟩, hs⟩ := IsLocalizedModule.surj (.powers g) (ℓ i) (y i)
      obtain ⟨k, hk⟩ := s.2
      simp only [Submonoid.smul_def, ← hk] at hs
      refine ⟨a i ^ k • w, ?_⟩
      refine ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units (ℓ i)
        (⟨g ^ (d + k), d + k, rfl⟩ : Submonoid.powers g))).1 ?_
      simp only [Module.algebraMap_end_apply]
      rw [← map_smul, smul_smul, ← pow_smul_eq_of_mem_annihilator g (ha i) k, map_smul,
        ← hs, smul_smul, ← pow_add]
    choose z hz using key
    exact ⟨⟨z, 1⟩, funext fun i => by simp [hz]⟩
  exists_of_eq {x₁ x₂} h := by
    choose a ha using hd
    refine ⟨⟨g ^ d, d, rfl⟩, funext fun i => ?_⟩
    obtain ⟨⟨_, k, rfl⟩, hc⟩ := IsLocalizedModule.exists_of_eq (S := .powers g) (f := ℓ i)
      (congrFun h i)
    simp only [Submonoid.smul_def, LinearMap.proj_apply] at hc
    change g ^ d • x₁ i = g ^ d • x₂ i
    have e : ∀ w : W i, g ^ d • w = (g ^ d * a i ^ k) • (g ^ k • w) := fun w => by
      rw [pow_smul_eq_of_mem_annihilator g (ha i) k w, smul_smul, pow_add]
      congr 1
      ring
    rw [e, e (x₂ i), hc]

end PiLocalization

section Fibre

variable {R : Type*} [CommRing R] (𝔫 : Ideal R) {B : Type*} [CommRing B] [Algebra R B]
  {V : Type*} [AddCommGroup V] [Module R V]

/-- An ideal killing `V` kills `B ⊗[R] V`. -/
theorem smul_tensor_eq_zero (h𝔫 : ∀ r ∈ 𝔫, ∀ v : V, r • v = 0) {r : R} (hr : r ∈ 𝔫)
    (t : B ⊗[R] V) : r • t = 0 := by
  induction t using TensorProduct.inductionOn with
  | tmul b v => rw [← TensorProduct.tmul_smul, h𝔫 r hr v, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

/-- An element of `B` vanishing in the fibre `(R ⧸ 𝔫) ⊗[R] B` kills `B ⊗[R] V` for every `V`
killed by `𝔫`. -/
theorem mem_annihilator_tensor (h𝔫 : ∀ r ∈ 𝔫, ∀ v : V, r • v = 0) {x : B}
    (hx : (1 : R ⧸ 𝔫) ⊗ₜ[R] x = 0) : x ∈ Module.annihilator B (B ⊗[R] V) := by
  have hx' : x ∈ 𝔫 • (⊤ : Submodule R B) := by
    have := congrArg (TensorProduct.quotTensorEquivQuotSMul B 𝔫) hx
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero] at this
    exact (Submodule.Quotient.mk_eq_zero _).mp this
  refine Submodule.smul_induction_on hx' (fun r hr b _ => ?_)
    (fun _ _ => Submodule.add_mem _)
  exact Module.mem_annihilator.mpr fun t => by rw [smul_assoc, smul_tensor_eq_zero 𝔫 h𝔫 hr]

/-- A Fitting bound for `b` in the fibre `κ ⊗ B` gives one on every `B ⊗ V` with `V` killed by
`𝔫`. -/
theorem exists_mem_annihilator_tensor (h𝔫 : ∀ r ∈ 𝔫, ∀ v : V, r • v = 0) (b : B) (d : ℕ)
    (y : (R ⧸ 𝔫) ⊗[R] B)
    (hy : ((1 : R ⧸ 𝔫) ⊗ₜ[R] b) ^ d = ((1 : R ⧸ 𝔫) ⊗ₜ[R] b) ^ (d + 1) * y) :
    ∃ a : B, b ^ d - b ^ (d + 1) * a ∈ Module.annihilator B (B ⊗[R] V) := by
  obtain ⟨a, rfl⟩ := Algebra.TensorProduct.includeRight_surjective B
    (Ideal.Quotient.mk_surjective (I := 𝔫)) y
  refine ⟨a, mem_annihilator_tensor 𝔫 h𝔫 ?_⟩
  have : (Algebra.TensorProduct.includeRight : B →ₐ[R] (R ⧸ 𝔫) ⊗[R] B)
      (b ^ d - b ^ (d + 1) * a) = 0 := by
    rw [map_sub, map_mul, map_pow, map_pow, Algebra.TensorProduct.includeRight_apply, hy,
      sub_self]
  simpa using this

end Fibre

section Field

/-- An étale algebra over a field is von Neumann regular. -/
theorem exists_pow_one_eq_of_etale (K : Type*) (A : Type u) [Field K] [CommRing A] [Algebra K A]
    [Algebra.Etale K A] (x : A) : ∃ a : A, x ^ 1 = x ^ (1 + 1) * a := by
  obtain ⟨I, _, Ai, _, _, e, -⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K A).mp ‹_›
  refine ⟨e.symm fun i => (e x i)⁻¹, e.injective ?_⟩
  funext i
  simp [pow_two]

/-- In an algebra of dimension at most `d` over a field, `x ^ d ∈ x ^ (d + 1) A`. -/
theorem exists_pow_eq_pow_succ_mul (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A] {d : ℕ} (hd : Module.finrank K A ≤ d) (x : A) :
    ∃ a : A, x ^ d = x ^ (d + 1) * a := by
  have hpow : ∀ n, (LinearMap.mulLeft K x) ^ n = LinearMap.mulLeft K (x ^ n) :=
    fun n => LinearMap.pow_mulLeft (R := K) (A := A) (a := x) (n := n)
  have hker : LinearMap.ker (LinearMap.mulLeft K (x ^ d)) =
      LinearMap.ker (LinearMap.mulLeft K (x ^ (d + 1))) := by
    rw [← hpow, ← hpow, Module.End.ker_pow_eq_ker_pow_finrank_of_le hd,
      Module.End.ker_pow_eq_ker_pow_finrank_of_le (hd.trans d.le_succ)]
  have hle : LinearMap.range (LinearMap.mulLeft K (x ^ (d + 1))) ≤
      LinearMap.range (LinearMap.mulLeft K (x ^ d)) := by
    rintro _ ⟨y, rfl⟩
    exact ⟨x * y, by simp [pow_succ]⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker (LinearMap.mulLeft K (x ^ d))
  have h2 := LinearMap.finrank_range_add_finrank_ker (LinearMap.mulLeft K (x ^ (d + 1)))
  rw [hker] at h1
  have hmem : x ^ d ∈ LinearMap.range (LinearMap.mulLeft K (x ^ d)) := ⟨1, by simp⟩
  rw [← Submodule.eq_of_le_of_finrank_eq hle (by omega)] at hmem
  obtain ⟨a, ha⟩ := hmem
  exact ⟨a, by simpa using ha.symm⟩

end Field

section PiRight

variable (R : Type*) [CommRing R] {ι : Type*} (V : ι → Type*) [∀ i, AddCommGroup (V i)]
  [∀ i, Module R (V i)]

/-- The underlying function of `TensorProduct.piRightHom` does not depend on the scalars. -/
theorem coe_piRightHom (S N : Type*) [CommRing S] [Algebra R S] [AddCommGroup N] [Module R N]
    [Module S N] [IsScalarTower R S N] :
    ⇑(piRightHom R S N V) = ⇑(piRightHom R R N V) := by
  funext x
  induction x using TensorProduct.inductionOn with
  | tmul n v => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- Tensoring with a finite free module commutes with products. -/
theorem bijective_piRightHom_of_free (N : Type*) [AddCommGroup N] [Module R N] [Module.Free R N]
    [Module.Finite R N] : Function.Bijective (piRightHom R R N V) := by
  classical
  let b := Module.Free.chooseBasis R N
  let κ := Module.Free.ChooseBasisIndex R N
  let Φ₁ : N ⊗[R] (∀ i, V i) ≃ₗ[R] (κ → ∀ i, V i) :=
    b.equivFun.rTensor _ ≪≫ₗ TensorProduct.comm R _ _ ≪≫ₗ
      TensorProduct.piScalarRight R R (∀ i, V i) κ
  let Φ₂ : (∀ i, N ⊗[R] V i) ≃ₗ[R] ∀ i, κ → V i :=
    LinearEquiv.piCongrRight fun i => b.equivFun.rTensor _ ≪≫ₗ TensorProduct.comm R _ _ ≪≫ₗ
      TensorProduct.piScalarRight R R (V i) κ
  have key : ∀ x, Φ₂ (piRightHom R R N V x) = Equiv.piComm _ (Φ₁ x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul n v =>
      funext i k
      simp [Φ₁, Φ₂, Equiv.piComm, Function.swap]
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add]
      rfl
  rw [← Function.Bijective.of_comp_iff' Φ₂.bijective,
    show ⇑Φ₂ ∘ ⇑(piRightHom R R N V) = ⇑(Equiv.piComm _) ∘ ⇑Φ₁ from funext key]
  exact (Equiv.bijective _).comp Φ₁.bijective

/-- Commuting with products is invariant under linear equivalence. -/
theorem bijective_piRightHom_of_linearEquiv {N N' : Type*} [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N'] (e : N ≃ₗ[R] N')
    (h : Function.Bijective (piRightHom R R N V)) :
    Function.Bijective (piRightHom R R N' V) := by
  let Ψ : (∀ i, N ⊗[R] V i) ≃ₗ[R] ∀ i, N' ⊗[R] V i :=
    LinearEquiv.piCongrRight fun i => e.rTensor _
  have key : ∀ x, piRightHom R R N' V (e.rTensor _ x) = Ψ (piRightHom R R N V x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul n v =>
      funext i
      simp [Ψ]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have : ⇑(piRightHom R R N' V) = ⇑Ψ ∘ ⇑(piRightHom R R N V) ∘ ⇑(e.rTensor (∀ i, V i)).symm := by
    funext x
    obtain ⟨y, rfl⟩ := (e.rTensor (∀ i, V i)).surjective x
    simp only [Function.comp_apply, LinearEquiv.symm_apply_apply, key]
  rw [this]
  exact Ψ.bijective.comp (h.comp (LinearEquiv.bijective _))

end PiRight

section Localization

variable (R : Type*) [CommRing R] {ι : Type*} (V : ι → Type*) [∀ i, AddCommGroup (V i)]
  [∀ i, Module R (V i)] {A : Type*} [CommRing A] [Algebra R A] (g : A) (A' : Type*) [CommRing A']
  [Algebra R A'] [Algebra A A'] [IsScalarTower R A A'] [IsLocalization.Away g A']

/-- `TensorProduct.piRightHom` is natural in the localization `A → A'`. -/
theorem piRightHom_comp_rTensor :
    (piRightHom R A' A' V).restrictScalars A ∘ₗ
        AlgebraTensorModule.rTensor R (∀ i, V i) (Algebra.linearMap A A') =
      (LinearMap.pi fun i => AlgebraTensorModule.rTensor R (V i) (Algebra.linearMap A A') ∘ₗ
        LinearMap.proj i) ∘ₗ piRightHom R A A V := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul a v => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

variable {R V g} in
/-- Under a uniform Fitting bound, `TensorProduct.piRightHom` for `A' = A[1/g]` is the
localization of `TensorProduct.piRightHom` for `A`. -/
theorem map_piRightHom (d : ℕ)
    (hd : ∀ i, ∃ a : A, g ^ d - g ^ (d + 1) * a ∈ Module.annihilator A (A ⊗[R] V i)) :
    haveI := isLocalizedModule_pi g
      (fun i => AlgebraTensorModule.rTensor R (V i) (Algebra.linearMap A A')) d hd
    IsLocalizedModule.map (.powers g)
        (AlgebraTensorModule.rTensor R (∀ i, V i) (Algebra.linearMap A A'))
        (LinearMap.pi fun i => AlgebraTensorModule.rTensor R (V i) (Algebra.linearMap A A') ∘ₗ
          LinearMap.proj i) (piRightHom R A A V) =
      (piRightHom R A' A' V).restrictScalars A := by
  have := isLocalizedModule_pi g
    (fun i => AlgebraTensorModule.rTensor R (V i) (Algebra.linearMap A A')) d hd
  refine IsLocalizedModule.linearMap_ext (.powers g)
    (AlgebraTensorModule.rTensor R (∀ i, V i) (Algebra.linearMap A A'))
    (LinearMap.pi fun i => AlgebraTensorModule.rTensor R (V i) (Algebra.linearMap A A') ∘ₗ
      LinearMap.proj i) ?_
  rw [IsLocalizedModule.map_comp, piRightHom_comp_rTensor]

variable {R V g} in
/-- Commuting with products passes to a localization `A[1/g]` under a uniform Fitting bound for
`g` on the `A ⊗ Vᵢ`. -/
theorem bijective_piRightHom_away (d : ℕ)
    (hd : ∀ i, ∃ a : A, g ^ d - g ^ (d + 1) * a ∈ Module.annihilator A (A ⊗[R] V i))
    (h : Function.Bijective (piRightHom R R A V)) :
    Function.Bijective (piRightHom R R A' V) := by
  have := isLocalizedModule_pi g
    (fun i => AlgebraTensorModule.rTensor R (V i) (Algebra.linearMap A A')) d hd
  rw [← coe_piRightHom R V A']
  rw [← coe_piRightHom R V A] at h
  rw [← LinearMap.coe_restrictScalars A, ← map_piRightHom A' d hd]
  exact ⟨IsLocalizedModule.map_injective _ _ _ _ h.1, IsLocalizedModule.map_surjective _ _ _ _ h.2⟩

end Localization

section Span

variable (R : Type*) [CommRing R] {ι : Type*} (V : ι → Type*) [∀ i, AddCommGroup (V i)]
  [∀ i, Module R (V i)] {C : Type*} [CommRing C] [Algebra R C]

variable {R V} in
/-- Commuting with products is local on `Spec C`, for covers by basic opens on which uniform
Fitting bounds hold. -/
theorem bijective_piRightHom_of_span (s : Set C) (hs : Ideal.span s = ⊤)
    (hd : ∀ g ∈ s, ∃ d, ∀ i, ∃ a : C, g ^ d - g ^ (d + 1) * a ∈ Module.annihilator C (C ⊗[R] V i))
    (H : ∀ g ∈ s, Function.Bijective (piRightHom R R (Localization.Away g) V)) :
    Function.Bijective (piRightHom R R C V) := by
  choose d hd using hd
  have : ∀ r : s, IsLocalizedModule.Away r.1 (LinearMap.pi fun i =>
      AlgebraTensorModule.rTensor R (V i) (Algebra.linearMap C (Localization.Away r.1)) ∘ₗ
        LinearMap.proj i) := fun r =>
    isLocalizedModule_pi r.1 _ (d r.1 r.2) (hd r.1 r.2)
  rw [← coe_piRightHom R V C]
  refine bijective_of_isLocalized_span s hs (fun r => Localization.Away r.1 ⊗[R] ∀ i, V i)
    (fun r => AlgebraTensorModule.rTensor R _ (Algebra.linearMap C (Localization.Away r.1)))
    (fun r => ∀ i, Localization.Away r.1 ⊗[R] V i)
    (fun r => LinearMap.pi fun i =>
      AlgebraTensorModule.rTensor R (V i) (Algebra.linearMap C (Localization.Away r.1)) ∘ₗ
        LinearMap.proj i) (piRightHom R C C V) fun r => ?_
  rw [map_piRightHom (Localization.Away r.1) (d r.1 r.2) (hd r.1 r.2),
    LinearMap.coe_restrictScalars, coe_piRightHom R V]
  exact H r.1 r.2

end Span

section Etale

variable {R : Type*} [CommRing R] {ι : Type*} {V : ι → Type*} [∀ i, AddCommGroup (V i)]
  [∀ i, Module R (V i)] (𝔫 : ι → Ideal R) [∀ i, (𝔫 i).IsMaximal]
  (h𝔫 : ∀ i, ∀ r ∈ 𝔫 i, ∀ v : V i, r • v = 0)
include h𝔫

open Polynomial in
/-- The statement for `(R[x] ⧸ (f))[1/g]` with `f` monic: the fibres of `R[x] ⧸ (f)` have dimension
`deg f`, a uniform Fitting bound for `g`. -/
theorem bijective_piRightHom_adjoinRoot_away {f : R[X]} (hf : f.Monic) (g : AdjoinRoot f) :
    Function.Bijective (piRightHom R R (Localization.Away g) V) := by
  let pb := AdjoinRoot.powerBasis' hf
  have : Module.Free R (AdjoinRoot f) := .of_basis pb.basis
  have : Module.Finite R (AdjoinRoot f) := .of_basis pb.basis
  refine bijective_piRightHom_away (g := g) (Localization.Away g) pb.dim (fun i => ?_)
    (bijective_piRightHom_of_free R V (AdjoinRoot f))
  let := Ideal.Quotient.field (𝔫 i)
  let b := pb.basis.baseChange (R ⧸ 𝔫 i)
  have : FiniteDimensional (R ⧸ 𝔫 i) ((R ⧸ 𝔫 i) ⊗[R] AdjoinRoot f) := .of_basis b
  obtain ⟨y, hy⟩ := exists_pow_eq_pow_succ_mul (R ⧸ 𝔫 i) ((R ⧸ 𝔫 i) ⊗[R] AdjoinRoot f)
    (d := pb.dim) (by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]) (1 ⊗ₜ g)
  exact exists_mem_annihilator_tensor (𝔫 i) (h𝔫 i) g pb.dim y hy

/-- The statement for standard étale algebras. -/
theorem bijective_piRightHom_of_isStandardEtale (X : Type*) [CommRing X] [Algebra R X]
    [Algebra.IsStandardEtale R X] : Function.Bijective (piRightHom R R X V) := by
  let P : StandardEtalePresentation R X :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  let e : X ≃ₐ[R] _ := P.equivRing.trans P.P.equivAwayAdjoinRoot
  exact bijective_piRightHom_of_linearEquiv R V e.symm.toLinearEquiv
    (bijective_piRightHom_adjoinRoot_away 𝔫 h𝔫 P.monic_f _)

/-- **Étale algebras commute with products of modules over residue fields.** Let `C` be an étale
`R`-algebra and `Vᵢ` a family of `R`-modules, each killed by a maximal ideal `𝔫ᵢ`. Then
`C ⊗[R] ∏ Vᵢ → ∏ (C ⊗[R] Vᵢ)` is bijective. -/
theorem bijective_piRightHom_of_etale (C : Type*) [CommRing C] [Algebra R C] [Algebra.Etale R C] :
    Function.Bijective (piRightHom R R C V) := by
  refine bijective_piRightHom_of_span
    {g : C | Function.Bijective (piRightHom R R (Localization.Away g) V)} ?_ ?_ fun g hg => hg
  · by_contra hne
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
    have := hQ.isPrime
    obtain ⟨f, hfQ, hf⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) Q
    exact hfQ (hle (Ideal.subset_span (bijective_piRightHom_of_isStandardEtale 𝔫 h𝔫 _)))
  · intro g _
    refine ⟨1, fun i => ?_⟩
    let := Ideal.Quotient.field (𝔫 i)
    obtain ⟨y, hy⟩ := exists_pow_one_eq_of_etale (R ⧸ 𝔫 i) ((R ⧸ 𝔫 i) ⊗[R] C) (1 ⊗ₜ g)
    exact exists_mem_annihilator_tensor (𝔫 i) (h𝔫 i) g 1 y hy

end Etale

end Stacks.C1590Private
