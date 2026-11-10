module

public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import StacksCore.Algebra.Module.FinitePresentation
public import StacksFrontier.RingTheory.Flat.BlowupFiniteTypeReduction

/-!
# Finite presentation of a graded algebra from its tail

Two pieces of commutative algebra used by steps (a)–(i) of the proof of [Stacks, Tag 0D4F].

* `Algebra.FinitePresentation.of_subalgebra_of_quotient`: if `C ⊆ A` is a finitely presented
  `R`-subalgebra and `A / C` is a finitely presented `R`-module, then `A` is a finitely presented
  `R`-algebra.  This is steps (e)–(i) of the source: `A / C` is finitely presented over `C`
  ([Stacks, Tag 0561]), hence so is `A` as a `C`-module ([Stacks, Tag 0519]), hence as a
  `C`-algebra ([Stacks, Tag 0D46]), hence as an `R`-algebra ([Stacks, Tag 00F4]).
* `GradedTailFinitePresentation.finitePresentation_of_isBaseChange`: let `A = ⨁ 𝒜 n` be a graded
  `R`-algebra with `𝒜 0 = R`, and let `B = ⨁ ℬ n` be a finitely presented graded `R₀`-algebra with
  `ℬ 0` spanned by `1` and `ℬ n = 0` for `0 < n < e`.  If a graded `R₀`-algebra map `φ : B → A`
  exhibits every `𝒜 n`, `n ≥ e`, as the base change of `ℬ n` along `R₀ → R`, and the pieces
  `𝒜 n`, `0 < n < e`, are finitely presented `R`-modules, then `A` is a finitely presented
  `R`-algebra.  This is steps (c)–(i): the subalgebra `R ⊕ ⨁_{n ≥ e} 𝒜 n` is the base change
  `R ⊗_{R₀} B`, finitely presented by right exactness of the tensor product.

## References

* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
* [Stacks Project, Tag 0561](https://stacks.math.columbia.edu/tag/0561)
* [Stacks Project, Tag 0519](https://stacks.math.columbia.edu/tag/0519)
* [Stacks Project, Tag 0D46](https://stacks.math.columbia.edu/tag/0D46)
* [Stacks Project, Tag 00F4](https://stacks.math.columbia.edu/tag/00F4)
-/

@[expose] public section

open DirectSum TensorProduct

/-- **A finite product of finitely presented modules is finitely presented.** -/
theorem Module.FinitePresentation.pi_fin {R : Type*} [Ring R] :
    ∀ (k : ℕ) (M : Fin k → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
      [∀ i, Module.FinitePresentation R (M i)], Module.FinitePresentation R (∀ i, M i)
  | 0, M, _, _, _ => by
    have : Subsingleton (∀ i, M i) := ⟨fun x y => funext fun i => Fin.elim0 i⟩
    exact Module.finitePresentation_of_projective R _
  | k + 1, M, _, _, _ => by
    have := Module.FinitePresentation.pi_fin (R := R) k (fun i => M i.succ)
    exact Module.FinitePresentation.of_equiv (Fin.consLinearEquiv R M)

/-- **Steps (e)–(i) of the proof of [Stacks, Tag 0D4F].**  If `C` is a finitely presented
`R`-subalgebra of `A` and the quotient `A / C` is a finitely presented `R`-module, then `A` is a
finitely presented `R`-algebra: `A / C` is finitely presented over `C` ([Stacks, Tag 0561]), so
`A` is a finitely presented `C`-module ([Stacks, Tag 0519]), hence a finitely presented
`C`-algebra ([Stacks, Tag 0D46]), hence a finitely presented `R`-algebra ([Stacks, Tag 00F4]). -/
theorem Algebra.FinitePresentation.of_subalgebra_of_quotient {R A : Type*} [CommRing R]
    [CommRing A] [Algebra R A] (C : Subalgebra R A) [Algebra.FinitePresentation R C]
    [Module.FinitePresentation R (A ⧸ Subalgebra.toSubmodule C)] :
    Algebra.FinitePresentation R A := by
  let N : Submodule C A := LinearMap.range (Algebra.linearMap C A)
  have hN : N.restrictScalars R = Subalgebra.toSubmodule C := by
    ext x
    simp only [Submodule.restrictScalars_mem, LinearMap.mem_range, Algebra.linearMap_apply,
      Subalgebra.mem_toSubmodule, N]
    exact ⟨fun ⟨c, hc⟩ => hc ▸ c.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have : Module.FinitePresentation R (A ⧸ N) :=
    Module.FinitePresentation.of_equiv
      ((Submodule.quotEquivOfEq _ _ hN.symm).trans
        (Submodule.Quotient.restrictScalarsEquiv R N))
  have : Module.FinitePresentation C (A ⧸ N) :=
    Module.FinitePresentation.of_restrictScalars_of_finiteType R C (A ⧸ N)
  have : Module.FinitePresentation C A :=
    Module.FinitePresentation.of_exact_fst (Algebra.linearMap C A) N.mkQ
      (LinearMap.exact_iff.mpr (Submodule.ker_mkQ N))
      (fun x y h => Subtype.ext h) (Submodule.mkQ_surjective N)
  exact Algebra.FinitePresentation.trans R C A

namespace GradedTailFinitePresentation

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- The components of `x` in the degrees `1, …, e - 1`. -/
noncomputable def bandProj (e : ℕ) : A →ₗ[R] ∀ i : Fin (e - 1), 𝒜 ((i : ℕ) + 1) :=
  LinearMap.pi fun i => (GradedAlgebra.proj 𝒜 ((i : ℕ) + 1)).codRestrict _
    fun x => by rw [GradedAlgebra.proj_apply]; exact SetLike.coe_mem _

/-- The `i`-th entry of `bandProj 𝒜 e x` is the homogeneous component of `x` in degree `i + 1`. -/
theorem bandProj_apply (e : ℕ) (x : A) (i : Fin (e - 1)) :
    ((bandProj 𝒜 e x i : 𝒜 ((i : ℕ) + 1)) : A) = decompose 𝒜 x ((i : ℕ) + 1) :=
  GradedAlgebra.proj_apply _ _ _

/-- The map `bandProj 𝒜 e` to the components in degrees `1, …, e - 1` is surjective. -/
theorem surjective_bandProj (e : ℕ) : Function.Surjective (bandProj 𝒜 e) := by
  classical
  intro y
  refine ⟨∑ i : Fin (e - 1), (y i : A), funext fun j => Subtype.ext ?_⟩
  rw [bandProj_apply, decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum,
    Finset.sum_eq_single j]
  · exact decompose_of_mem_same 𝒜 (y j).2
  · intro i _ hij
    refine decompose_of_mem_ne 𝒜 (y i).2 fun h => hij (Fin.ext ?_)
    omega
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- **The quotient of a graded algebra by the subalgebra `R ⊕ ⨁_{n ≥ e} 𝒜 n` is the band
`⨁_{0 < n < e} 𝒜 n`**, so it is finitely presented when the pieces of the band are.  The
subalgebra is given as any `C` containing `𝒜 0` and every `𝒜 n`, `n ≥ e`, and having no
component in the band. -/
theorem finitePresentation_quotient (e : ℕ)
    (h0 : ∀ a ∈ 𝒜 0, ∃ r : R, algebraMap R A r = a)
    (hband : ∀ n, 0 < n → n < e → Module.FinitePresentation R (𝒜 n))
    (C : Subalgebra R A) (hC : ∀ n, e ≤ n → ∀ a ∈ 𝒜 n, a ∈ C)
    (hCband : ∀ c ∈ C, ∀ n, 0 < n → n < e → (decompose 𝒜 c n : A) = 0) :
    Module.FinitePresentation R (A ⧸ Subalgebra.toSubmodule C) := by
  classical
  have hker : LinearMap.ker (bandProj 𝒜 e) = Subalgebra.toSubmodule C := by
    ext x
    simp only [LinearMap.mem_ker, Subalgebra.mem_toSubmodule]
    constructor
    · intro hx
      rw [← sum_support_decompose 𝒜 x]
      refine Subalgebra.sum_mem _ fun n _ => ?_
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · obtain ⟨r, hr⟩ := h0 _ (SetLike.coe_mem _)
        rw [← hr]
        exact C.algebraMap_mem r
      · by_cases hne : n < e
        · have := congrArg (fun y => ((y ⟨n - 1, by omega⟩ : 𝒜 _) : A)) hx
          simp only [bandProj_apply, Pi.zero_apply, ZeroMemClass.coe_zero] at this
          rw [show n - 1 + 1 = n by omega] at this
          rw [this]
          exact C.zero_mem
        · exact hC n (by omega) _ (SetLike.coe_mem _)
    · intro hx
      funext i
      refine Subtype.ext ?_
      rw [bandProj_apply]
      exact hCband x hx _ (by omega) (by omega)
  have : ∀ i : Fin (e - 1), Module.FinitePresentation R (𝒜 ((i : ℕ) + 1)) :=
    fun i => hband _ (by omega) (by omega)
  have := Module.FinitePresentation.pi_fin (R := R) (e - 1) fun i => 𝒜 ((i : ℕ) + 1)
  exact Module.FinitePresentation.of_equiv
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans
      (LinearMap.quotKerEquivOfSurjective _ (surjective_bandProj 𝒜 e))).symm

section BaseChange

variable {R₀ B : Type*} [CommRing R₀] [CommRing B] [Algebra R₀ B]
  (ℬ : ℕ → Submodule R₀ B) [GradedAlgebra ℬ]
  [Algebra R₀ R] [Algebra R₀ A] [IsScalarTower R₀ R A]

/-- The degree-`n` component `ℬ n → 𝒜 n` of a graded `R₀`-algebra map `φ : B → A`. -/
noncomputable def pieceMap (φ : B →ₐ[R₀] A) (hφ : ∀ n, ∀ b ∈ ℬ n, φ b ∈ 𝒜 n) (n : ℕ) :
    ℬ n →ₗ[R₀] 𝒜 n where
  toFun b := ⟨φ b, hφ n b b.2⟩
  map_add' x y := Subtype.ext (map_add φ (x : B) y)
  map_smul' r x := Subtype.ext (φ.toLinearMap.map_smul r x)

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
/-- The map `pieceMap 𝒜 ℬ φ hφ n` sends `b : ℬ n` to `φ b`. -/
theorem coe_pieceMap (φ : B →ₐ[R₀] A) (hφ : ∀ n, ∀ b ∈ ℬ n, φ b ∈ 𝒜 n) (n : ℕ) (b : ℬ n) :
    (pieceMap 𝒜 ℬ φ hφ n b : A) = φ b := rfl

variable {𝒜 ℬ} in
omit [Algebra R₀ R] [IsScalarTower R₀ R A] in
/-- A graded map commutes with taking homogeneous components. -/
theorem decompose_map_apply (φ : B →ₐ[R₀] A) (hφ : ∀ n, ∀ b ∈ ℬ n, φ b ∈ 𝒜 n) (b : B)
    (n : ℕ) : (decompose 𝒜 (φ b) n : A) = φ (decompose ℬ b n) := by
  classical
  conv_lhs => rw [← sum_support_decompose ℬ b]
  rw [map_sum, decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum,
    Finset.sum_eq_single n]
  · exact decompose_of_mem_same 𝒜 (hφ n _ (SetLike.coe_mem _))
  · intro m _ hmn
    exact decompose_of_mem_ne 𝒜 (hφ m _ (SetLike.coe_mem _)) hmn
  · intro hn
    rw [DFinsupp.notMem_support_iff.mp hn, ZeroMemClass.coe_zero, map_zero,
      decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]

/-- **Steps (c)–(i) of the proof of [Stacks, Tag 0D4F].**  Let `A = ⨁ 𝒜 n` be a graded
`R`-algebra whose degree-zero part is `R`, and `B = ⨁ ℬ n` a finitely presented graded
`R₀`-algebra whose degree-zero part is spanned by `1` and which vanishes in the degrees
`0 < n < e`.  If a graded `R₀`-algebra map `φ : B → A` exhibits every `𝒜 n`, `n ≥ e`, as the base
change of `ℬ n` along `R₀ → R`, and the pieces `𝒜 n`, `0 < n < e`, are finitely presented
`R`-modules, then `A` is a finitely presented `R`-algebra.

The induced map `R ⊗_{R₀} B → A` is injective with image `R ⊕ ⨁_{n ≥ e} 𝒜 n`, which is therefore
finitely presented (right exactness of the tensor product), and
`Algebra.FinitePresentation.of_subalgebra_of_quotient` finishes. -/
theorem finitePresentation_of_isBaseChange [Algebra.FinitePresentation R₀ B] (e : ℕ)
    (h0 : ∀ a ∈ 𝒜 0, ∃ r : R, algebraMap R A r = a)
    (hinj : Function.Injective (algebraMap R A))
    (hband : ∀ n, 0 < n → n < e → Module.FinitePresentation R (𝒜 n))
    (hB0 : ∀ b ∈ ℬ 0, ∃ s : R₀, algebraMap R₀ B s = b)
    (hBband : ∀ n, 0 < n → n < e → ∀ b ∈ ℬ n, b = 0)
    (φ : B →ₐ[R₀] A) (hφ : ∀ n, ∀ b ∈ ℬ n, φ b ∈ 𝒜 n)
    (hbc : ∀ n, e ≤ n → IsBaseChange R (pieceMap 𝒜 ℬ φ hφ n)) :
    Algebra.FinitePresentation R A := by
  classical
  let Ψ : R ⊗[R₀] B →ₐ[R] A :=
    Algebra.TensorProduct.lift (Algebra.ofId R A) φ fun _ _ => Commute.all _ _
  have hΨ : ∀ (r : R) (b : B), Ψ (r ⊗ₜ b) = r • φ b := fun r b => by
    rw [Algebra.smul_def]
    rfl
  let ψ : ∀ n, R ⊗[R₀] ℬ n →ₗ[R] 𝒜 n := fun n => (pieceMap 𝒜 ℬ φ hφ n).liftBaseChange R
  let E : R ⊗[R₀] B ≃ₗ[R₀] ⨁ n, R ⊗[R₀] ℬ n :=
    (TensorProduct.congr (LinearEquiv.refl R₀ R) (decomposeLinearEquiv ℬ)).trans
      (TensorProduct.directSumRight R₀ R₀ R fun n => ℬ n)
  have hEsymm : ∀ (n : ℕ) (r : R) (b : ℬ n),
      E.symm (DirectSum.lof R₀ ℕ (fun n => R ⊗[R₀] ℬ n) n (r ⊗ₜ b)) = r ⊗ₜ (b : B) := by
    intro n r b
    simp only [E, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
      TensorProduct.directSumRight_symm_lof_tmul, TensorProduct.congr_symm_tmul,
      LinearEquiv.refl_symm, LinearEquiv.refl_apply, decomposeLinearEquiv_symm_lof]
  -- `Ψ`, read through `E`, is the direct sum of the degreewise maps `ψ n`.
  have hkey : ∀ x, Ψ (E.symm x) = (decomposeLinearEquiv 𝒜).symm (DirectSum.lmap ψ x) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | of n t =>
      rw [← DirectSum.lof_eq_of R₀]
      induction t using TensorProduct.inductionOn with
      | tmul r b =>
        rw [hEsymm, hΨ]
        change _ = (decomposeLinearEquiv 𝒜).symm
          (DirectSum.lmap ψ (DirectSum.lof R ℕ (fun n => R ⊗[R₀] ℬ n) n (r ⊗ₜ b)))
        rw [DirectSum.lmap_lof, decomposeLinearEquiv_symm_lof]
        simp only [ψ, LinearMap.liftBaseChange_tmul, Submodule.coe_smul, coe_pieceMap]
      | add t t' ht ht' => simp only [map_add, ht, ht']
    | add x y hx hy => simp only [map_add, hx, hy]
  -- The band pieces `R ⊗ ℬ n` vanish.
  have hz : ∀ n, 0 < n → n < e → ∀ s : R ⊗[R₀] ℬ n, s = 0 := by
    intro n hn hne s
    induction s using TensorProduct.inductionOn with
    | tmul r b =>
      rw [show b = 0 from Subtype.ext (hBband n hn hne b b.2), TensorProduct.tmul_zero]
    | add s s' hs hs' => rw [hs, hs', add_zero]
  -- Beyond the band, `ψ n` is the base change equivalence.
  have heq : ∀ n (hn : e ≤ n) t, ψ n t = (hbc n hn).equiv t := by
    intro n hn t
    induction t using TensorProduct.inductionOn with
    | tmul r b => rw [IsBaseChange.equiv_tmul]; rfl
    | add t t' ht ht' => simp only [map_add, ht, ht']
  -- Each `ψ n` is injective.
  have hψinj : ∀ n, Function.Injective (ψ n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hform : ∀ t : R ⊗[R₀] ℬ 0, ∃ r : R, t = r ⊗ₜ ⟨1, SetLike.GradedOne.one_mem⟩ := by
        intro t
        induction t using TensorProduct.inductionOn with
        | tmul r b =>
          obtain ⟨s, hs⟩ := hB0 b b.2
          refine ⟨s • r, ?_⟩
          rw [TensorProduct.smul_tmul]
          congr 1
          exact Subtype.ext (by rw [Submodule.coe_smul, ← hs, Algebra.algebraMap_eq_smul_one])
        | add t t' ht ht' =>
          obtain ⟨r, rfl⟩ := ht
          obtain ⟨r', rfl⟩ := ht'
          exact ⟨r + r', (TensorProduct.add_tmul _ _ _).symm⟩
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro t ht
      obtain ⟨r, rfl⟩ := hform t
      have h1 := congrArg Subtype.val ht
      simp only [ψ, LinearMap.liftBaseChange_tmul, Submodule.coe_smul, coe_pieceMap, map_one,
        ZeroMemClass.coe_zero] at h1
      rw [← Algebra.algebraMap_eq_smul_one] at h1
      rw [hinj (h1.trans (map_zero _).symm), TensorProduct.zero_tmul]
    · by_cases hne : n < e
      · intro t t' _
        rw [hz n hn hne t, hz n hn hne t']
      · intro t t' h
        rw [heq n (by omega), heq n (by omega)] at h
        exact (hbc n (by omega)).equiv.injective h
  have hΨinj : Function.Injective Ψ := by
    refine (injective_iff_map_eq_zero Ψ).mpr fun t ht => ?_
    have h1 : DirectSum.lmap ψ (E t) = 0 := by
      have := hkey (E t)
      rw [LinearEquiv.symm_apply_apply] at this
      apply (decomposeLinearEquiv 𝒜).symm.injective
      rw [← this, map_zero]
      exact ht
    have h2 : E t = 0 := ((DirectSum.lmap_injective ψ).mpr hψinj) (h1.trans (map_zero _).symm)
    exact E.injective (h2.trans (map_zero E).symm)
  let C : Subalgebra R A := Ψ.range
  have : Algebra.FinitePresentation R C :=
    Algebra.FinitePresentation.equiv (AlgEquiv.ofInjective Ψ hΨinj)
  -- The components of an element of `C`.
  have hdecC : ∀ x, decompose 𝒜 (Ψ (E.symm x)) = DirectSum.lmap ψ x := fun x => by
    rw [hkey]
    exact (decomposeLinearEquiv 𝒜).apply_symm_apply _
  have hC : ∀ n, e ≤ n → ∀ a ∈ 𝒜 n, a ∈ C := by
    intro n hn a ha
    obtain ⟨t, ht⟩ := (hbc n hn).equiv.surjective ⟨a, ha⟩
    refine ⟨E.symm (DirectSum.lof R₀ ℕ (fun n => R ⊗[R₀] ℬ n) n t), ?_⟩
    change Ψ _ = a
    rw [hkey]
    change (decomposeLinearEquiv 𝒜).symm
      (DirectSum.lmap ψ (DirectSum.lof R ℕ (fun n => R ⊗[R₀] ℬ n) n t)) = a
    rw [DirectSum.lmap_lof, decomposeLinearEquiv_symm_lof, heq n hn, ht]
  have hCband : ∀ c ∈ C, ∀ n, 0 < n → n < e → (decompose 𝒜 c n : A) = 0 := by
    rintro c ⟨t, rfl⟩ n hn hne
    change (decompose 𝒜 (Ψ t) n : A) = 0
    rw [← E.symm_apply_apply t, hdecC, DirectSum.lmap_apply]
    rw [hz n hn hne (E t n), map_zero, ZeroMemClass.coe_zero]
  have := finitePresentation_quotient 𝒜 e h0 hband C hC hCband
  exact Algebra.FinitePresentation.of_subalgebra_of_quotient C

end BaseChange

end GradedTailFinitePresentation

end
