module

public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Rank
public import StacksFrontier.RingTheory.Fitting.Rank
public import StacksFrontier.RingTheory.Fitting.Basic
import all StacksFrontier.RingTheory.Fitting.Basic
import all StacksFrontier.RingTheory.Fitting.Rank

/-!
# The locus where the kernel of a matrix is free of a given rank, universally

Let `A` be an `m × n` matrix over a commutative ring `R` and let `C_A` be the cokernel of its
transpose `Aᵀ : R^m → R^n`, so that `Hom(C_A, R) = ker A`. The Fitting ideals of `C_A` cut out
the locus over which the kernel of `A` is a free direct summand of rank `r` after every base
change: this happens exactly when `C_A` is finite locally free of rank `r`, that is when
`Fit_{r-1}(C_A) = 0` and `Fit_r(C_A) = R`.

## Main definitions

* `Matrix.cokerTransposeKernelRankStratum`: the module `C_A = R^n / Aᵀ(R^m)`.
* `Matrix.HasFreeKernelSplittingKernelRankStratum`: matrices `U`, `V`, `W` with `V U = 1`,
  `A U = 0` and `W A + U V = 1`, exhibiting `ker A` as a free direct summand of rank `r` on whose
  complement `A` is split injective. These identities survive every base change.

## Main results

* `Matrix.hasFreeKernelSplitting_of_basis_kernelRankStratum`: a basis of `C_A` of cardinality
  `r` gives a splitting.
* `Matrix.exists_span_hasFreeKernelSplitting_kernelRankStratum`: if `Fit_{r-1}(C_A) = 0` and
  `Fit_r(C_A) = R`, then `A` has a splitting over the localizations at a family of elements
  generating the unit ideal.
* `Matrix.fittingIdeal_cokerTranspose_eq_top_of_finrank_ker_le_kernelRankStratum`: if the kernel
  of `A` over a field point above every prime has dimension at most `r`, then `Fit_r(C_A) = R`.
* `Matrix.fittingIdeal_cokerTranspose_pred_eq_bot_kernelRankStratum`: if `Fit_r(C_A) = R` and
  `ker A` is free of rank `r`, then `Fit_{r-1}(C_A) = 0`.

## References

* [Stacks Project, Tag 0BDL](https://stacks.math.columbia.edu/tag/0BDL)
* [Stacks Project, Tag 07ZD](https://stacks.math.columbia.edu/tag/07ZD)
-/

@[expose] public noncomputable section

universe u

open Module

namespace Matrix

variable {R S : Type*} [CommRing R] [CommRing S] {m n : ℕ}

/-- The cokernel `R^n / Aᵀ(R^m)` of the transpose of an `m × n` matrix `A`. Its `R`-dual is the
kernel of `A`. -/
abbrev cokerTransposeKernelRankStratum (A : Matrix (Fin m) (Fin n) R) : Type _ :=
  (Fin n → R) ⧸ LinearMap.range Aᵀ.mulVecLin

/-- A *free kernel splitting of rank `r`* of an `m × n` matrix `A`: matrices `U`, `V`, `W` with
`V U = 1`, `A U = 0` and `W A + U V = 1`. Then the columns of `U` form a basis of `ker A`, the
projection `U V` onto it is complemented by `W A`, and `A` is split injective on the
complement. -/
def HasFreeKernelSplittingKernelRankStratum (A : Matrix (Fin m) (Fin n) R) (r : ℕ) : Prop :=
  ∃ (U : Matrix (Fin n) (Fin r) R) (V : Matrix (Fin r) (Fin n) R)
    (W : Matrix (Fin n) (Fin m) R), V * U = 1 ∧ A * U = 0 ∧ W * A + U * V = 1

/-- A free kernel splitting survives every ring homomorphism. -/
theorem HasFreeKernelSplittingKernelRankStratum.map {A : Matrix (Fin m) (Fin n) R} {r : ℕ}
    (h : A.HasFreeKernelSplittingKernelRankStratum r) (f : R →+* S) :
    (A.map f).HasFreeKernelSplittingKernelRankStratum r := by
  obtain ⟨U, V, W, h₁, h₂, h₃⟩ := h
  refine ⟨U.map f, V.map f, W.map f, ?_, ?_, ?_⟩
  · rw [← Matrix.map_mul, h₁, Matrix.map_one f f.map_zero f.map_one]
  · rw [← Matrix.map_mul, h₂, Matrix.map_zero f f.map_zero]
  · rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add f f.map_add, h₃,
      Matrix.map_one f f.map_zero f.map_one]

/-- **A basis of the cokernel of `Aᵀ` gives a free kernel splitting.** If `C_A` is free of rank
`r`, then `A` has a free kernel splitting of rank `r`. -/
theorem hasFreeKernelSplitting_of_basis_kernelRankStratum (A : Matrix (Fin m) (Fin n) R) {r : ℕ}
    (b : Basis (Fin r) R A.cokerTransposeKernelRankStratum) :
    A.HasFreeKernelSplittingKernelRankStratum r := by
  classical
  let N := LinearMap.range Aᵀ.mulVecLin
  let q : (Fin n → R) →ₗ[R] (Fin r → R) := b.equivFun.toLinearMap ∘ₗ N.mkQ
  have hq : Function.Surjective q :=
    b.equivFun.surjective.comp (Submodule.mkQ_surjective N)
  have hkerq : LinearMap.ker q = N := by
    rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot, Submodule.ker_mkQ]
  let σ : (Fin r → R) →ₗ[R] (Fin n → R) :=
    (Pi.basisFun R (Fin r)).constr R fun i => (hq (Pi.single i 1)).choose
  have hσ : q ∘ₗ σ = LinearMap.id := by
    refine (Pi.basisFun R (Fin r)).ext fun i => ?_
    rw [LinearMap.comp_apply, Basis.constr_basis, LinearMap.id_apply, Pi.basisFun_apply]
    exact (hq (Pi.single i 1)).choose_spec
  let ε : (Fin n → R) →ₗ[R] (Fin n → R) := LinearMap.id - σ ∘ₗ q
  have hmem : ∀ j : Fin n, ε (Pi.single j 1) ∈ N := by
    intro j
    rw [← hkerq, LinearMap.mem_ker]
    simp only [ε, LinearMap.sub_apply, map_sub, LinearMap.id_apply]
    rw [← LinearMap.comp_apply q (σ ∘ₗ q), ← LinearMap.comp_assoc, hσ, LinearMap.id_comp,
      sub_self]
  let τ : (Fin n → R) →ₗ[R] (Fin m → R) :=
    (Pi.basisFun R (Fin n)).constr R fun j => (hmem j).choose
  have hτ : Aᵀ.mulVecLin ∘ₗ τ = ε := by
    refine (Pi.basisFun R (Fin n)).ext fun j => ?_
    rw [LinearMap.comp_apply, Basis.constr_basis, Pi.basisFun_apply]
    exact (hmem j).choose_spec
  have hqA : q ∘ₗ Aᵀ.mulVecLin = 0 := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.zero_apply, ← LinearMap.mem_ker, hkerq]
    exact LinearMap.mem_range_self _ x
  let Q := LinearMap.toMatrix' q
  let Sg := LinearMap.toMatrix' σ
  let T := LinearMap.toMatrix' τ
  have e₁ : Q * Sg = 1 := by
    rw [← LinearMap.toMatrix'_comp, hσ, LinearMap.toMatrix'_id]
  have e₂ : Q * Aᵀ = 0 := by
    rw [← LinearMap.toMatrix'_toLin' Aᵀ, ← LinearMap.toMatrix'_comp, Matrix.toLin'_apply',
      hqA, map_zero]
  have e₃ : Aᵀ * T + Sg * Q = 1 := by
    rw [← LinearMap.toMatrix'_toLin' Aᵀ, ← LinearMap.toMatrix'_comp,
      ← LinearMap.toMatrix'_comp, ← map_add, Matrix.toLin'_apply', hτ, sub_add_cancel,
      LinearMap.toMatrix'_id]
  refine ⟨Qᵀ, Sgᵀ, Tᵀ, ?_, ?_, ?_⟩
  · rw [← Matrix.transpose_mul, e₁, Matrix.transpose_one]
  · rw [← Matrix.transpose_transpose A, ← Matrix.transpose_mul, e₂, Matrix.transpose_zero]
  · rw [← Matrix.transpose_transpose A, ← Matrix.transpose_mul, ← Matrix.transpose_mul,
      ← Matrix.transpose_add, e₃, Matrix.transpose_one]

/-! ### Localization -/

section Localization

variable (p : Submonoid R)

/-- Coordinatewise localization `R^k → (R_p)^k`. -/
abbrev piLocalizationKernelRankStratum (p : Submonoid R) (k : ℕ) :
    (Fin k → R) →ₗ[R] (Fin k → Localization p) :=
  LinearMap.pi fun i => Algebra.linearMap R (Localization p) ∘ₗ LinearMap.proj i

/-- Multiplication by a matrix commutes with coordinatewise localization. -/
theorem piLocalization_mulVecLin_kernelRankStratum {k l : ℕ} (B : Matrix (Fin l) (Fin k) R) :
    (B.map (algebraMap R (Localization p))).mulVecLin.restrictScalars R ∘ₗ
        piLocalizationKernelRankStratum p k =
      piLocalizationKernelRankStratum p l ∘ₗ B.mulVecLin := by
  refine LinearMap.ext fun x => funext fun i => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
    Matrix.mulVecLin_apply, LinearMap.pi_apply, LinearMap.coe_proj, Function.eval,
    Algebra.linearMap_apply]
  exact (RingHom.map_mulVec (algebraMap R (Localization p)) B x i).symm

/-- The localization of a matrix map is the map of the localized matrix. -/
theorem map_piLocalization_mulVecLin_kernelRankStratum {k l : ℕ} (B : Matrix (Fin l) (Fin k) R) :
    IsLocalizedModule.map p (piLocalizationKernelRankStratum p k)
        (piLocalizationKernelRankStratum p l) B.mulVecLin =
      (B.map (algebraMap R (Localization p))).mulVecLin.restrictScalars R :=
  IsLocalizedModule.ext p (piLocalizationKernelRankStratum p k)
    (IsLocalizedModule.map_units (piLocalizationKernelRankStratum p l))
    ((IsLocalizedModule.map_comp p (piLocalizationKernelRankStratum p k)
        (piLocalizationKernelRankStratum p l) _).trans
      (piLocalization_mulVecLin_kernelRankStratum p B).symm)

/-- The localization of the range of `Aᵀ` is the range of the transpose of the localized
matrix. -/
theorem range_transpose_mulVecLin_localized_kernelRankStratum (A : Matrix (Fin m) (Fin n) R) :
    (LinearMap.range Aᵀ.mulVecLin).localized' (Localization p) p
        (piLocalizationKernelRankStratum p n) =
      LinearMap.range (A.map (algebraMap R (Localization p)))ᵀ.mulVecLin := by
  rw [LinearMap.localized'_range_eq_range_localizedMap (Localization p) p
    (piLocalizationKernelRankStratum p m) (piLocalizationKernelRankStratum p n),
    map_piLocalization_mulVecLin_kernelRankStratum, ← Matrix.transpose_map]
  ext x
  simp only [LinearMap.mem_range, LinearMap.extendScalarsOfIsLocalization_apply]

/-- The localization map `C_A → C_{A_p}`. -/
def cokerTransposeLocalizationKernelRankStratum (A : Matrix (Fin m) (Fin n) R) :
    A.cokerTransposeKernelRankStratum →ₗ[R]
      (A.map (algebraMap R (Localization p))).cokerTransposeKernelRankStratum :=
  (Submodule.quotEquivOfEq _ _
      (range_transpose_mulVecLin_localized_kernelRankStratum p A)).toLinearMap.restrictScalars R ∘ₗ
    (LinearMap.range Aᵀ.mulVecLin).toLocalizedQuotient' (Localization p) p
      (piLocalizationKernelRankStratum p n)

/-- The map `C_A → C_{A_p}` is a localization at `p`. -/
instance (A : Matrix (Fin m) (Fin n) R) :
    IsLocalizedModule p (cokerTransposeLocalizationKernelRankStratum p A) :=
  IsLocalizedModule.of_linearEquiv p _
    ((Submodule.quotEquivOfEq _ _
      (range_transpose_mulVecLin_localized_kernelRankStratum p A)).restrictScalars R)

/-- The localization of `C_A` is `C_{A_p}`, as modules over the localized ring. -/
def localizedCokerTransposeEquivKernelRankStratum (A : Matrix (Fin m) (Fin n) R) :
    LocalizedModule p A.cokerTransposeKernelRankStratum ≃ₗ[Localization p]
      (A.map (algebraMap R (Localization p))).cokerTransposeKernelRankStratum :=
  (IsLocalizedModule.linearEquiv p (LocalizedModule.mkLinearMap p A.cokerTransposeKernelRankStratum)
    (cokerTransposeLocalizationKernelRankStratum p A)).extendScalarsOfIsLocalization p
      (Localization p)

end Localization

/-! ### Fitting ideals of `C_A` -/

/-- The Fitting ideals of `C_A` are minor ideals of `Aᵀ`. -/
theorem fittingIdeal_cokerTranspose_kernelRankStratum (A : Matrix (Fin m) (Fin n) R) (k : ℕ) :
    fittingIdeal (R := R) (M := A.cokerTransposeKernelRankStratum) (k : ℤ) =
      _root_.minorIdeal Aᵀ (n - k) :=
  fittingIdeal_eq_minorIdeal_of_presentation Aᵀ k
    (Submodule.quotEquivOfEq _ _ (Matrix.range_mulVecLin Aᵀ).symm)

/-- The Fitting ideals of `C_A` commute with every base change. -/
theorem fittingIdeal_cokerTranspose_map_kernelRankStratum (A : Matrix (Fin m) (Fin n) R)
    (f : R →+* S) (k : ℤ) :
    fittingIdeal (R := S) (M := (A.map f).cokerTransposeKernelRankStratum) k =
      Ideal.map f (fittingIdeal (R := R) (M := A.cokerTransposeKernelRankStratum) k) := by
  rcases lt_or_ge k 0 with hk | hk
  · rw [fittingIdeal_eq_bot_of_lt_zero hk, fittingIdeal_eq_bot_of_lt_zero hk, Ideal.map_bot]
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [fittingIdeal_cokerTranspose_kernelRankStratum,
      fittingIdeal_cokerTranspose_kernelRankStratum, ← Matrix.transpose_map, ← minorIdeal_map]

/-- The Fitting ideals of `C_A` are finitely generated. -/
theorem fg_fittingIdeal_cokerTranspose_kernelRankStratum (A : Matrix (Fin m) (Fin n) R) (k : ℤ) :
    (fittingIdeal (R := R) (M := A.cokerTransposeKernelRankStratum) k).FG := by
  rcases lt_or_ge k 0 with hk | hk
  · rw [fittingIdeal_eq_bot_of_lt_zero hk]
    exact Submodule.fg_bot
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [fittingIdeal_cokerTranspose_kernelRankStratum]
    exact minorIdeal_fg _ _

/-! ### The local splitting -/

/-- **On the rank `r` Fitting stratum the kernel splits locally.** If `Fit_{r-1}(C_A) = 0` and
`Fit_r(C_A) = R`, then `A` has a free kernel splitting of rank `r` over the localizations at a
family of elements generating the unit ideal. -/
theorem exists_span_hasFreeKernelSplitting_kernelRankStratum {R : Type u} [CommRing R]
    (A : Matrix (Fin m) (Fin n) R) (r : ℕ)
    (h₁ : fittingIdeal (R := R) (M := A.cokerTransposeKernelRankStratum) ((r : ℤ) - 1) = ⊥)
    (h₂ : fittingIdeal (R := R) (M := A.cokerTransposeKernelRankStratum) (r : ℤ) = ⊤) :
    ∃ (ι : Type u) (f : ι → R), Ideal.span (Set.range f) = ⊤ ∧
      ∀ i, (A.map (algebraMap R (Localization.Away (f i)))).HasFreeKernelSplittingKernelRankStratum
        r := by
  have hfl : Module.IsFiniteLocallyFreeOfRank R A.cokerTransposeKernelRankStratum r :=
    ((finiteLocallyFreeOfRank_fittingIdeal_tfae (R := R) (M := A.cokerTransposeKernelRankStratum)
      r).out 1 2).mpr (And.intro h₁ h₂)
  obtain ⟨ι, f, hf, hb⟩ := hfl
  exact ⟨ι, f, hf, fun i => hasFreeKernelSplitting_of_basis_kernelRankStratum _
    ((hb i).some.map (localizedCokerTransposeEquivKernelRankStratum (Submonoid.powers (f i)) A))⟩

/-! ### Fibres -/

/-- Over a field, the dimension of `C_A` is that of the kernel of `A`. -/
theorem finrank_cokerTranspose_kernelRankStratum {K : Type*} [Field K]
    (A : Matrix (Fin m) (Fin n) K) :
    Module.finrank K A.cokerTransposeKernelRankStratum =
      Module.finrank K (LinearMap.ker A.mulVecLin) := by
  have h₁ := Submodule.finrank_quotient_add_finrank (LinearMap.range Aᵀ.mulVecLin)
  have h₂ := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have h₃ : Module.finrank K (LinearMap.range Aᵀ.mulVecLin) =
      Module.finrank K (LinearMap.range A.mulVecLin) := by
    rw [← Matrix.rank, ← Matrix.rank, Matrix.rank_transpose]
  rw [Module.finrank_fin_fun] at h₁ h₂
  show finrank K ((Fin n → K) ⧸ LinearMap.range Aᵀ.mulVecLin) = _
  omega

/-- **The rank `r` Fitting ideal is not in a prime above which the kernel has dimension at most
`r`.** If `φ : R → K` is a homomorphism to a field with kernel `p` and the kernel of the matrix
`φ(A)` has dimension at most `r`, then `Fit_r(C_A) ⊄ p`. -/
theorem not_fittingIdeal_cokerTranspose_le_kernelRankStratum {K : Type*} [Field K]
    (A : Matrix (Fin m) (Fin n) R) (φ : R →+* K) (r : ℕ)
    (hr : Module.finrank K (LinearMap.ker (A.map φ).mulVecLin) ≤ r) :
    ¬ fittingIdeal (R := R) (M := A.cokerTransposeKernelRankStratum) (r : ℤ) ≤ RingHom.ker φ := by
  intro hle
  have htop : fittingIdeal (R := K) (M := (A.map φ).cokerTransposeKernelRankStratum) (r : ℤ) = ⊤ :=
    (fittingIdeal_eq_top_iff_finrank_le r).2
      ((finrank_cokerTranspose_kernelRankStratum _).trans_le hr)
  rw [fittingIdeal_cokerTranspose_map_kernelRankStratum] at htop
  have hbot :
      Ideal.map φ (fittingIdeal (R := R) (M := A.cokerTransposeKernelRankStratum) (r : ℤ)) = ⊥ :=
    (Ideal.map_eq_bot_iff_le_ker φ).mpr hle
  rw [hbot] at htop
  exact bot_ne_top htop

/-- **Pointwise kernel dimensions at most `r` make `Fit_r(C_A)` the unit ideal.** If above every
prime of `R` there is a field point at which the kernel of `A` has dimension at most `r`, then
`Fit_r(C_A) = R`. -/
theorem fittingIdeal_cokerTranspose_eq_top_of_finrank_ker_le_kernelRankStratum
    (A : Matrix (Fin m) (Fin n) R) (r : ℕ)
    (h : ∀ p : Ideal R, p.IsPrime → ∃ (K : Type u) (_ : Field K) (φ : R →+* K),
      RingHom.ker φ = p ∧ Module.finrank K (LinearMap.ker (A.map φ).mulVecLin) ≤ r) :
    fittingIdeal (R := R) (M := A.cokerTransposeKernelRankStratum) (r : ℤ) = ⊤ := by
  by_contra hne
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨K, _, φ, hker, hdim⟩ := h p hp.isPrime
  exact not_fittingIdeal_cokerTranspose_le_kernelRankStratum A φ r hdim (hker ▸ hle)

/-! ### The kernel test -/

/-- **A free kernel of rank `r` makes an `r`-generated `C_A` free.** If `C_A` is generated by `r`
elements and there is an injective `J : R^r → R^n` with `A J = 0`, then the surjection
`R^r → C_A` is injective. -/
theorem injective_linearCombination_of_mul_eq_zero_kernelRankStratum
    (A : Matrix (Fin m) (Fin n) R) {r : ℕ}
    (g : Fin r → A.cokerTransposeKernelRankStratum) (hg : Submodule.span R (Set.range g) = ⊤)
    (J : Matrix (Fin n) (Fin r) R) (hJ : A * J = 0) (hJinj : Function.Injective J.mulVec) :
    Function.Injective (Fintype.linearCombination R g) := by
  classical
  let N := LinearMap.range Aᵀ.mulVecLin
  choose ℓ hℓ using fun j => Submodule.mkQ_surjective N (g j)
  let L : Matrix (Fin n) (Fin r) R := Matrix.of fun i j => ℓ j i
  have hL : ∀ c : Fin r → R, N.mkQ (L *ᵥ c) = Fintype.linearCombination R g c := by
    intro c
    have : L *ᵥ c = ∑ j, c j • ℓ j := by
      ext i
      simp [L, Matrix.mulVec, dotProduct, mul_comm]
    rw [this, map_sum, Fintype.linearCombination_apply]
    simp [hℓ]
  have hdecomp : ∀ x : Fin n → R, ∃ c : Fin r → R, ∃ w : Fin m → R, x = L *ᵥ c + Aᵀ *ᵥ w := by
    intro x
    have hx : N.mkQ x ∈ Submodule.span R (Set.range g) := hg ▸ Submodule.mem_top
    rw [← Fintype.range_linearCombination] at hx
    obtain ⟨c, hc⟩ := hx
    rw [← hL] at hc
    have hmem : x - L *ᵥ c ∈ N := by
      rw [← Submodule.Quotient.eq]
      exact hc.symm
    obtain ⟨w, hw⟩ := hmem
    refine ⟨c, w, ?_⟩
    rw [Matrix.mulVecLin_apply] at hw
    rw [hw, add_sub_cancel]
  let M : Matrix (Fin r) (Fin r) R := Lᵀ * J
  have hMinj : Function.Injective M.mulVec := by
    intro y y' hyy'
    rw [← sub_eq_zero] at hyy' ⊢
    rw [← Matrix.mulVec_sub] at hyy'
    set y₀ := y - y'
    have hy : Lᵀ *ᵥ (J *ᵥ y₀) = 0 := by
      rw [Matrix.mulVec_mulVec]
      exact hyy'
    have hAv : A *ᵥ (J *ᵥ y₀) = 0 := by
      rw [Matrix.mulVec_mulVec, hJ, Matrix.zero_mulVec]
    have hv0 : J *ᵥ y₀ = 0 := by
      ext k
      obtain ⟨c, w, hx⟩ := hdecomp (Pi.single k 1)
      have hdot : (J *ᵥ y₀) ⬝ᵥ Pi.single k 1 = 0 := by
        rw [hx, dotProduct_add, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
          ← Matrix.mulVec_transpose, Matrix.vecMul_transpose, hy, hAv, zero_dotProduct,
          zero_dotProduct, add_zero]
      simpa [dotProduct_single] using hdot
    exact hJinj (hv0.trans (Matrix.mulVec_zero J).symm)
  have hMtinj : Function.Injective Mᵀ.mulVec := by
    have hnons : M.Nonsingular :=
      Matrix.Nonsingular.of_linearIndependent_col (by
        rw [← Matrix.mulVec_injective_iff]
        exact hMinj)
    rw [Matrix.mulVec_injective_iff]
    simpa [Matrix.col_transpose] using hnons.linearIndependent_row
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro k hk
  rw [← hL, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hk
  obtain ⟨w, hw⟩ := hk
  rw [Matrix.mulVecLin_apply] at hw
  apply hMtinj
  rw [Matrix.mulVec_zero]
  calc Mᵀ *ᵥ k = Jᵀ *ᵥ (L *ᵥ k) := by
        rw [Matrix.mulVec_mulVec, Matrix.transpose_mul, Matrix.transpose_transpose]
    _ = (A * J)ᵀ *ᵥ w := by
        rw [← hw, Matrix.mulVec_mulVec, Matrix.transpose_mul]
    _ = 0 := by rw [hJ, Matrix.transpose_zero, Matrix.zero_mulVec]

/-- Fitting ideals are invariant under linear equivalence, in every integer degree. -/
theorem fittingIdeal_int_eq_of_linearEquiv_kernelRankStratum {M N : Type*} [AddCommGroup M]
    [Module R M] [Module.Finite R M] [AddCommGroup N] [Module R N] [Module.Finite R N]
    (e : M ≃ₗ[R] N) (k : ℤ) :
    fittingIdeal (R := R) (M := M) k = fittingIdeal (R := R) (M := N) k :=
  fittingIdeal_eq_of_linearEquiv_int e k

/-- **A free kernel of rank `r` forces `Fit_{r-1}(C_A) = 0` where `Fit_r(C_A) = R`.** If the
`r`th Fitting ideal of `C_A` is the unit ideal and there is an injective `J : R^r → R^n` with
`A J = 0`, then the `(r - 1)`st Fitting ideal of `C_A` vanishes. -/
theorem fittingIdeal_cokerTranspose_pred_eq_bot_kernelRankStratum
    (A : Matrix (Fin m) (Fin n) R) {r : ℕ}
    (h : fittingIdeal (R := R) (M := A.cokerTransposeKernelRankStratum) (r : ℤ) = ⊤)
    (J : Matrix (Fin n) (Fin r) R) (hJ : A * J = 0) (hJinj : Function.Injective J.mulVec) :
    fittingIdeal (R := R) (M := A.cokerTransposeKernelRankStratum) ((r : ℤ) - 1) = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  by_contra hx0
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal (Ideal.span {y : R | y * x = 0}) (by
    rw [Ne, Ideal.eq_top_iff_one]
    intro h1
    refine hx0 ?_
    have : ∀ y ∈ Ideal.span {y : R | y * x = 0}, y * x = 0 := by
      intro y hy
      refine Submodule.span_induction (fun z hz => hz) (zero_mul x) (fun a b _ _ ha hb => ?_)
        (fun a b _ hb => ?_) hy
      · rw [add_mul, ha, hb, add_zero]
      · rw [smul_eq_mul, mul_assoc, hb, mul_zero]
    simpa using this 1 h1)
  have hnot : ¬ fittingIdeal (R := R) (M := A.cokerTransposeKernelRankStratum) (r : ℤ) ≤ p := by
    rw [h, top_le_iff]
    exact hp.ne_top
  obtain ⟨f, hf, g, hg⟩ := ((fittingIdeal_local_generation_tfae (R := R)
    (M := A.cokerTransposeKernelRankStratum) r p).out 1 4).1 hnot
  let P := Submonoid.powers f
  let e := localizedCokerTransposeEquivKernelRankStratum P A
  let Af := A.map (algebraMap R (Localization P))
  let Jf := J.map (algebraMap R (Localization P))
  have hJf : Af * Jf = 0 := by
    rw [← Matrix.map_mul, hJ, Matrix.map_zero _ (map_zero _)]
  have hJfinj : Function.Injective Jf.mulVec := by
    have := IsLocalizedModule.map_injective P (piLocalizationKernelRankStratum P r)
      (piLocalizationKernelRankStratum P n) J.mulVecLin hJinj
    rw [map_piLocalization_mulVecLin_kernelRankStratum] at this
    exact this
  have hg' : Submodule.span (Localization P) (Set.range (e ∘ g)) = ⊤ := by
    rw [Set.range_comp]
    have := Submodule.map_span e.toLinearMap (Set.range g)
    rw [LinearEquiv.coe_toLinearMap] at this
    rw [← this, hg, Submodule.map_top, LinearMap.range_eq_top]
    exact e.surjective
  have hinj :=
    injective_linearCombination_of_mul_eq_zero_kernelRankStratum Af (e ∘ g) hg' Jf hJf hJfinj
  have hsurj : Function.Surjective (Fintype.linearCombination (Localization P) (e ∘ g)) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hg']
  let eq := LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩
  have hbot : fittingIdeal (R := Localization P) (M := Af.cokerTransposeKernelRankStratum)
      ((r : ℤ) - 1) = ⊥ := by
    rw [← fittingIdeal_int_eq_of_linearEquiv_kernelRankStratum eq, fittingIdeal_fin_eq_bot_or_top,
      if_pos (by omega)]
  rw [fittingIdeal_cokerTranspose_map_kernelRankStratum, Ideal.map_eq_bot_iff_le_ker] at hbot
  have hxk := hbot hx
  rw [RingHom.mem_ker, IsLocalization.map_eq_zero_iff P] at hxk
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := hxk
  exact hf (hp.isPrime.mem_of_pow_mem k (hle (Ideal.subset_span hk)))

/-- **`Fit_0(C_A)` gives left inverses of `A` up to a scalar.** If `x` lies in the zeroth Fitting
ideal of `C_A = coker Aᵀ`, then there is a matrix `N` with `N A = x · 1`. -/
theorem exists_mul_eq_smul_one_of_mem_fittingIdeal_zero_kernelRankStratum
    (A : Matrix (Fin m) (Fin n) R) {x : R}
    (hx : x ∈ fittingIdeal (R := R) (M := A.cokerTransposeKernelRankStratum) 0) :
    ∃ N : Matrix (Fin n) (Fin m) R, N * A = x • (1 : Matrix (Fin n) (Fin n) R) := by
  classical
  have hann :=
    (fittingIdeal_basic_properties.{_, _, 0, 0} (R := R)
      (M := A.cokerTransposeKernelRankStratum)).2.2.2.2.2.1 hx
  rw [Module.mem_annihilator] at hann
  have hv : ∀ j : Fin n, ∃ v : Fin m → R, Aᵀ *ᵥ v = x • Pi.single j 1 := by
    intro j
    have h := hann (Submodule.Quotient.mk (Pi.single j 1))
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
    exact h
  choose v hv using hv
  refine ⟨Matrix.of v, ?_⟩
  ext j k
  have hjk := congrFun (hv j) k
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.smul_apply, Pi.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero] at hjk
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  simp only [eq_comm (a := j)]
  rw [← hjk]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end Matrix
