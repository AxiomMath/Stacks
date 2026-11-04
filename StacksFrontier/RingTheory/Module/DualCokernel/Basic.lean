module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.OrzechProperty
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import StacksFrontier.RingTheory.Ideal.LocallyPrincipalInvertible
public import StacksFrontier.RingTheory.Norm.Projective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cokernel of the transpose of a linear map

Let `S` be a commutative ring and `d : M →ₗ[S] N` a linear map. The *dual cokernel* of `d` is the
cokernel `M^∨ ⧸ d^∨(N^∨)` of its transpose. When `M` is finite projective and `N` is projective,
the kernel of `d` is the dual of the dual cokernel.

The second result is a statement about modules alone: a module `Q` which is a quotient of
`S^r` and whose dual is free of rank `r` is itself free of rank `r`, the quotient map being
injective. The proof is McCoy's theorem: the transpose of the quotient map is an injective
endomorphism of `S^r`, so its determinant `δ` is a nonzerodivisor, and `δ` times every linear
form on `S^r` factors through `Q`.

## Main definitions

* `LinearMap.DualCoker`: the cokernel of the transpose of a linear map.

## Main results

* `LinearMap.kerEquivDualDualCoker`: `ker d ≃ (M^∨ ⧸ d^∨(N^∨))^∨`.
* `LinearMap.injective_of_surjective_of_dual_equiv`: a surjection `S^r ↠ Q` with `Q^∨ ≅ S^r` is
  injective.
-/

@[expose] public noncomputable section

open Module

universe u

namespace LinearMap

variable {S : Type u} [CommRing S] {M N : Type u} [AddCommGroup M] [Module S M]
  [AddCommGroup N] [Module S N]

/-- **The dual cokernel of a linear map.** For `d : M →ₗ[S] N`, the cokernel of the transpose
`d^∨ : N^∨ ⟶ M^∨`. -/
@[ega "III 7.6.11"]
abbrev DualCoker (d : M →ₗ[S] N) : Type _ := Dual S M ⧸ range d.dualMap

/-- The kernel of `d`, carried into the double dual, is the annihilator of the image of the
transpose. -/
theorem map_ker_evalEquiv [IsReflexive S M] [Projective S N] (d : M →ₗ[S] N) :
    (ker d).map (evalEquiv S M : M →ₗ[S] Dual S (Dual S M)) =
      (range d.dualMap).dualAnnihilator := by
  ext ψ
  simp only [Submodule.mem_map, mem_ker, LinearEquiv.coe_coe, Submodule.mem_dualAnnihilator,
    mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  constructor
  · rintro ⟨m, hm, rfl⟩ φ
    simp [hm]
  · intro h
    refine ⟨(evalEquiv S M).symm ψ, ?_, by simp⟩
    refine (forall_dual_apply_eq_zero_iff S _).1 fun φ => ?_
    have := h φ
    rwa [← (evalEquiv S M).apply_symm_apply ψ, evalEquiv_apply, Dual.eval_apply,
      dualMap_apply] at this

/-- **The kernel of `d` is the dual of the dual cokernel.** For `M` reflexive and `N` projective,
evaluation identifies `ker d` with the linear forms on `M^∨` vanishing on the image of `d^∨`. -/
@[ega "III 7.6.11" "partial"]
def kerEquivDualDualCoker [IsReflexive S M] [Projective S N] (d : M →ₗ[S] N) :
    ker d ≃ₗ[S] Dual S (DualCoker d) :=
  (LinearEquiv.ofSubmodules (evalEquiv S M) (ker d) (range d.dualMap).dualAnnihilator
      (map_ker_evalEquiv d)).trans
    (Submodule.dualQuotEquivDualAnnihilator (range d.dualMap)).symm

/-- **McCoy's theorem.** A surjection `π : S^r ↠ Q` onto a module whose dual is free of rank `r`
is injective. -/
theorem injective_of_surjective_of_dual_equiv {Q : Type*} [AddCommGroup Q] [Module S Q] {r : ℕ}
    (π : (Fin r → S) →ₗ[S] Q) (hπ : Function.Surjective π) (e : Dual S Q ≃ₗ[S] (Fin r → S)) :
    Function.Injective π := by
  classical
  let c : Dual S (Fin r → S) ≃ₗ[S] (Fin r → S) := (Pi.basisFun S (Fin r)).dualBasis.equivFun
  let ι : (Fin r → S) →ₗ[S] (Fin r → S) := c.toLinearMap ∘ₗ π.dualMap ∘ₗ e.symm.toLinearMap
  have hι : Function.Injective ι :=
    c.injective.comp ((dualMap_injective_of_surjective hπ).comp e.symm.injective)
  let A : Matrix (Fin r) (Fin r) S := LinearMap.toMatrix' ι
  have hmv (w : Fin r → S) : ι w = A.mulVec w := (LinearMap.toMatrix'_mulVec ι w).symm
  have hA : Function.Injective A.mulVec := fun v w h =>
    hι ((hmv v).trans (h.trans (hmv w).symm))
  have hdet : A.det ∈ nonZeroDivisors S :=
    Matrix.nonsingular_iff_det_mem_nonZeroDivisors.1
      (Matrix.linearIndependent_col_iff.1 (Matrix.mulVec_injective_iff.1 hA))
  have hrange (v : Fin r → S) : A.det • v ∈ range ι := by
    refine ⟨(Matrix.adjugate A).mulVec v, ?_⟩
    rw [hmv, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  funext i
  obtain ⟨w, hw⟩ := hrange (c (LinearMap.proj i))
  have h1 : (A.det • (LinearMap.proj i : Dual S (Fin r → S))) = π.dualMap (e.symm w) :=
    c.injective ((map_smul c _ _).trans hw.symm)
  have h2 := congrArg (fun φ : Dual S (Fin r → S) => φ x) h1
  simp only [smul_apply, proj_apply, dualMap_apply, mem_ker.1 hx, map_zero, smul_eq_mul] at h2
  exact (mem_nonZeroDivisors_iff_right.1 hdet) _ (by rwa [mul_comm])

section BaseChange

open TensorProduct

variable (T : Type u) [CommRing T] [Algebra S T]

/-- **Duals commute with base change, for finite free modules.** The `T`-linear identification
`T ⊗ M^∨ ≅ (T ⊗ M)^∨` sending `t ⊗ φ` to `t · (1 ⊗ φ)`. -/
abbrev dualBaseChangeEquiv (M : Type u) [AddCommGroup M] [Module S M] [Module.Free S M]
    [Module.Finite S M] : T ⊗[S] Dual S M ≃ₗ[T] Dual T (T ⊗[S] M) :=
  (TensorProduct.isBaseChange S M T).toDualBaseChange

/-- The linear form `dualBaseChangeEquiv T M (t ⊗ φ)` sends `1 ⊗ m` to `t · φ(m)`. -/
theorem dualBaseChangeEquiv_tmul_tmul (M : Type u) [AddCommGroup M] [Module S M]
    [Module.Free S M] [Module.Finite S M] (t : T) (φ : Dual S M) (m : M) :
    dualBaseChangeEquiv T M (t ⊗ₜ φ) (1 ⊗ₜ m) = t * algebraMap S T (φ m) :=
  (TensorProduct.isBaseChange S M T).toDualBaseChange_tmul t φ m

variable [Module.Free S M] [Module.Finite S M] [Module.Free S N] [Module.Finite S N]

/-- The identification of duals with base change intertwines the base change of the transpose
with the transpose of the base change. -/
theorem dualBaseChangeEquiv_comp_baseChange_dualMap (d : M →ₗ[S] N) :
    (dualBaseChangeEquiv T M).toLinearMap ∘ₗ d.dualMap.baseChange T =
      (d.baseChange T).dualMap ∘ₗ (dualBaseChangeEquiv T N).toLinearMap := by
  refine TensorProduct.AlgebraTensorModule.ext fun t ψ => ?_
  refine TensorProduct.AlgebraTensorModule.ext fun t' m => ?_
  have h {P : Type u} [AddCommGroup P] [Module S P] (p : P) :
      (t' ⊗ₜ[S] p : T ⊗[S] P) = t' • (1 ⊗ₜ[S] p) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, baseChange_tmul,
    dualMap_apply]
  rw [h m, map_smul, h (d m), map_smul, dualBaseChangeEquiv_tmul_tmul,
    dualBaseChangeEquiv_tmul_tmul, dualMap_apply]

/-- **The dual cokernel commutes with base change.** For finite free `M` and `N`, the dual
cokernel of `d ⊗ T` is `T ⊗` the dual cokernel of `d`. -/
def dualCokerBaseChangeEquiv (d : M →ₗ[S] N) :
    DualCoker (d.baseChange T) ≃ₗ[T] T ⊗[S] DualCoker d :=
  (Submodule.Quotient.equiv _ _ (dualBaseChangeEquiv T M).symm (by
      set e := dualBaseChangeEquiv (S := S) T M
      set L := d.dualMap.baseChange T
      have key : LinearMap.range (d.baseChange T).dualMap =
          LinearMap.range (e.toLinearMap ∘ₗ L) := by
        rw [dualBaseChangeEquiv_comp_baseChange_dualMap]
        exact (LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)).symm
      have hL : LinearMap.range L = LinearMap.range
          (AlgebraTensorModule.lTensor T T
            ((LinearMap.range d.dualMap).subtype.restrictScalars S)) := by
        have hfac : L = AlgebraTensorModule.lTensor T T
            ((LinearMap.range d.dualMap).subtype.restrictScalars S) ∘ₗ
              AlgebraTensorModule.lTensor T T d.dualMap.rangeRestrict :=
          TensorProduct.AlgebraTensorModule.ext fun _ _ => rfl
        rw [hfac]
        exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2
          (LinearMap.lTensor_surjective T d.dualMap.surjective_rangeRestrict))
      rw [key, ← hL, ← LinearMap.range_comp]
      congr 1
      ext x
      simp)).trans
    (AlgebraTensorModule.tensorQuotientEquiv T S T (LinearMap.range d.dualMap)).symm

/-- **Over a field the kernel and the dual cokernel have the same dimension.** -/
@[ega "III 7.6.11" "partial"]
theorem finrank_ker_baseChange_eq (K : Type u) [Field K] [Algebra S K] (d : M →ₗ[S] N) :
    finrank K (ker (d.baseChange K)) = finrank K (K ⊗[S] DualCoker d) := by
  rw [(kerEquivDualDualCoker (d.baseChange K)).finrank_eq, Subspace.dual_finrank_eq,
    (dualCokerBaseChangeEquiv K d).finrank_eq]

/-- The dual of the base changed dual cokernel is the kernel of the base change. -/
@[ega "III 7.6.11" "partial"]
def dualBaseChangeDualCokerEquivKer (d : M →ₗ[S] N) :
    Dual T (T ⊗[S] DualCoker d) ≃ₗ[T] ker (d.baseChange T) :=
  (Module.Dual.congr (dualCokerBaseChangeEquiv T d)).symm.trans
    (kerEquivDualDualCoker (d.baseChange T)).symm

/-- **Over a local ring, a free kernel of rank `r` and a fibre of the dual cokernel of dimension
at most `r` make the dual cokernel free of rank `r`.** -/
theorem nonempty_baseChange_dualCoker_equiv_of_isLocalRing [IsLocalRing T] (d : M →ₗ[S] N)
    {r : ℕ} (e : ker (d.baseChange T) ≃ₗ[T] (Fin r → T))
    (h : finrank (IsLocalRing.ResidueField T)
        (IsLocalRing.ResidueField T ⊗[T] (T ⊗[S] DualCoker d)) ≤ r) :
    Nonempty ((T ⊗[S] DualCoker d) ≃ₗ[T] (Fin r → T)) := by
  classical
  set k := IsLocalRing.ResidueField T
  set Q := T ⊗[S] DualCoker d
  set s := finrank k (k ⊗[T] Q)
  let b : Basis (Fin s) k (k ⊗[T] Q) := Module.finBasis k (k ⊗[T] Q)
  choose v hv using fun i =>
    TensorProduct.mk_surjective T Q k IsLocalRing.residue_surjective (b i)
  have hspan : Submodule.span T (Set.range v) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis v b hv
  let w : Fin r → Q := fun i => if hi : (i : ℕ) < s then v ⟨i, hi⟩ else 0
  let π : (Fin r → T) →ₗ[T] Q := Fintype.linearCombination T w
  have hπ : Function.Surjective π := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, eq_top_iff, ← hspan]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨i, lt_of_lt_of_le i.2 h⟩, ?_⟩
    simp [w, i.2]
  exact ⟨(LinearEquiv.ofBijective π ⟨injective_of_surjective_of_dual_equiv π hπ
    ((dualBaseChangeDualCokerEquivKer T d).trans e), hπ⟩).symm⟩

/-- **Kernels of base changes along a flat algebra.** For `T → T'` flat, the kernel of `d ⊗ T'` is
the base change to `T'` of the kernel of `d ⊗ T`. -/
def kerBaseChangeEquiv (T' : Type u) [CommRing T'] [Algebra T T'] [Algebra S T']
    [IsScalarTower S T T'] [Module.Flat T T'] (d : M →ₗ[S] N) :
    T' ⊗[T] ker (d.baseChange T) ≃ₗ[T'] ker (d.baseChange T') :=
  (LinearMap.tensorKerEquiv T' T' (d.baseChange T)).trans
    (LinearEquiv.ofSubmodules (AlgebraTensorModule.cancelBaseChange S T T' T' M) _ _ (by
      have hc : AlgebraTensorModule.lTensor T' T' (d.baseChange T) =
          (AlgebraTensorModule.cancelBaseChange S T T' T' N).symm.toLinearMap ∘ₗ
            d.baseChange T' ∘ₗ
              (AlgebraTensorModule.cancelBaseChange S T T' T' M).toLinearMap :=
        LinearMap.baseChange_baseChange d
      rw [hc, LinearEquiv.ker_comp, LinearMap.ker_comp,
        Submodule.map_comap_eq_of_surjective (LinearEquiv.surjective _)]))

/-- A family generating the unit ideal has a member outside any proper ideal. -/
private theorem _root_.Ideal.exists_notMem_of_span_range_eq_top {R ι : Type*} [CommSemiring R]
    {f : ι → R} (hf : Ideal.span (Set.range f) = ⊤) {p : Ideal R} (hp : p ≠ ⊤) :
    ∃ i, f i ∉ p := by
  by_contra! h
  refine hp (eq_top_iff.2 ?_)
  rw [← hf, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact h i

/-- A base change which is finite locally free of rank `r` is free of rank `r` on a principal
open around each prime. -/
private theorem exists_away_baseChange_equiv_aux {Q : Type u} [AddCommGroup Q] [Module S Q]
    {r : ℕ}
    (h : Module.IsFiniteLocallyFreeOfRank T (T ⊗[S] Q) r) (p : Ideal T) [p.IsPrime] :
    ∃ g : T, g ∉ p ∧ Nonempty (Localization.Away g ⊗[S] Q ≃ₗ[Localization.Away g]
      (Fin r → Localization.Away g)) := by
  obtain ⟨ι, f, hspan, hb⟩ := h
  obtain ⟨i, hi⟩ := Ideal.exists_notMem_of_span_range_eq_top hspan ‹p.IsPrime›.ne_top
  exact ⟨f i, hi, ⟨(TensorProduct.AlgebraTensorModule.cancelBaseChange S T
    (Localization.Away (f i)) (Localization.Away (f i)) Q).symm.trans
      (((LocalizedModule.isBaseChange (Submonoid.powers (f i)) (T ⊗[S] Q)).equiv).trans
        (hb i).some.equivFun)⟩⟩

end BaseChange

section Local

open TensorProduct

variable [Module.Free S M] [Module.Finite S M] [Module.Free S N] [Module.Finite S N]

/-- For `M` and `N` finite free, the dual cokernel of `d : M →ₗ[S] N` is finitely presented. -/
instance (d : M →ₗ[S] N) : Module.FinitePresentation S (DualCoker d) :=
  haveI := Module.finitePresentation_of_projective S (Dual S M)
  Module.finitePresentation_of_surjective (range d.dualMap).mkQ (Submodule.mkQ_surjective _)
    (by
      rw [Submodule.ker_mkQ, LinearMap.range_eq_map]
      exact Module.Finite.fg_top.map _)

/-- A finite locally free module of rank `r` is finite and flat. -/
theorem _root_.Module.IsFiniteLocallyFreeOfRank.finite_flat {T K : Type u} [CommRing T]
    [AddCommGroup K] [Module T K] {r : ℕ} (h : Module.IsFiniteLocallyFreeOfRank T K r) :
    Module.Finite T K ∧ Module.Flat T K := by
  obtain ⟨ι, f, hspan, hbasis⟩ := h
  have hS : Ideal.span (Set.range f) = ⊤ := hspan
  refine ⟨Module.Finite.of_localizationSpan (Set.range f) hS ?_,
    Module.flat_of_localized_span T K (Set.range f) hS ?_⟩
  · rintro ⟨r, ⟨i, rfl⟩⟩
    exact Module.Finite.of_basis (hbasis i).some
  · rintro ⟨r, ⟨i, rfl⟩⟩
    have : Module.Free (Localization.Away (f i))
        (LocalizedModule (Submonoid.powers (f i)) K) := Module.Free.of_basis (hbasis i).some
    exact Module.Flat.trans T (Localization.Away (f i)) _

/-- **The localization at a prime of a finite locally free module of rank `r` is free of rank
`r`.** -/
theorem _root_.Module.IsFiniteLocallyFreeOfRank.nonempty_localizedModule_equiv {T K : Type u}
    [CommRing T] [AddCommGroup K] [Module T K] {r : ℕ}
    (h : Module.IsFiniteLocallyFreeOfRank T K r) (p : Ideal T) [p.IsPrime] :
    Nonempty (LocalizedModule p.primeCompl K ≃ₗ[Localization.AtPrime p]
      (Fin r → Localization.AtPrime p)) := by
  obtain ⟨_, _⟩ := h.finite_flat
  have : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl K) :=
    Module.free_of_flat_of_isLocalRing
  have hrank : finrank (Localization.AtPrime p) (LocalizedModule p.primeCompl K) = r :=
    rankAtStalk_eq_of_isFiniteLocallyFreeOfRank r h ⟨p, inferInstance⟩
  exact ⟨(Module.finBasisOfFinrankEq _ _ hrank).equivFun⟩

variable (T : Type u) [CommRing T] [Algebra S T]

/-- **The dual cokernel of a base change is finite locally free of rank `r` when the kernel is
finite locally free of rank `r` and the kernels of the base changes to the residue fields at the
maximal ideals have dimension at most `r`.** -/
theorem isFiniteLocallyFreeOfRank_baseChange_dualCoker (d : M →ₗ[S] N) {r : ℕ}
    (hker : Module.IsFiniteLocallyFreeOfRank T (ker (d.baseChange T)) r)
    (hfib : ∀ (p : Ideal T) [p.IsMaximal],
      finrank p.ResidueField (ker (d.baseChange p.ResidueField)) ≤ r) :
    Module.IsFiniteLocallyFreeOfRank T (T ⊗[S] DualCoker d) r := by
  refine Module.isFiniteLocallyFreeOfRank_of_forall_isMaximal r fun p hp => ?_
  set Tp := Localization.AtPrime p
  obtain ⟨eK⟩ := hker.nonempty_localizedModule_equiv p
  have eker : ker (d.baseChange Tp) ≃ₗ[Tp] (Fin r → Tp) :=
    (kerBaseChangeEquiv T Tp d).symm.trans
      (((LocalizedModule.isBaseChange p.primeCompl (ker (d.baseChange T))).equiv).trans eK)
  have hfib' : finrank (IsLocalRing.ResidueField Tp)
      (IsLocalRing.ResidueField Tp ⊗[Tp] (Tp ⊗[S] DualCoker d)) ≤ r := by
    rw [(AlgebraTensorModule.cancelBaseChange S Tp p.ResidueField p.ResidueField
      (DualCoker d)).finrank_eq, ← finrank_ker_baseChange_eq]
    exact hfib p
  obtain ⟨eQ⟩ := nonempty_baseChange_dualCoker_equiv_of_isLocalRing Tp d eker hfib'
  let g : (T ⊗[S] DualCoker d) →ₗ[T] Tp ⊗[S] DualCoker d :=
    (AlgebraTensorModule.cancelBaseChange S T Tp Tp (DualCoker d)).toLinearMap.restrictScalars T
      ∘ₗ TensorProduct.mk T Tp (T ⊗[S] DualCoker d) 1
  have : IsLocalizedModule p.primeCompl g :=
    (isLocalizedModule_iff_isBaseChange p.primeCompl Tp g).2
      (IsBaseChange.of_equiv (AlgebraTensorModule.cancelBaseChange S T Tp Tp (DualCoker d))
        fun _ => rfl)
  obtain ⟨s, hs, b', -⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
    p.primeCompl g Tp (Basis.ofEquivFun eQ)
  exact ⟨s, hs, ⟨b'⟩⟩

/-- **The kernel of a base change is finite locally free of rank `r` when the dual cokernel is.**
If `T ⊗ DualCoker d` is finite locally free of rank `r` over `T`, so is the kernel of `d ⊗ T`. -/
theorem isFiniteLocallyFreeOfRank_ker_baseChange (d : M →ₗ[S] N) {r : ℕ}
    (hQ : Module.IsFiniteLocallyFreeOfRank T (T ⊗[S] DualCoker d) r) :
    Module.IsFiniteLocallyFreeOfRank T (ker (d.baseChange T)) r := by
  classical
  refine Module.isFiniteLocallyFreeOfRank_of_forall_isMaximal r fun p hp => ?_
  obtain ⟨g, hg, ⟨e1⟩⟩ := exists_away_baseChange_equiv_aux T hQ p
  let Tg := Localization.Away g
  let c : Dual Tg (Fin r → Tg) ≃ₗ[Tg] (Fin r → Tg) := (Pi.basisFun Tg (Fin r)).dualBasis.equivFun
  let ek : ker (d.baseChange Tg) ≃ₗ[Tg] (Fin r → Tg) :=
    (dualBaseChangeDualCokerEquivKer Tg d).symm.trans
      ((Module.Dual.congr e1).trans c)
  let eL : LocalizedModule (Submonoid.powers g) (ker (d.baseChange T)) ≃ₗ[Tg] (Fin r → Tg) :=
    (LocalizedModule.isBaseChange (Submonoid.powers g) (ker (d.baseChange T))).equiv.symm.trans
      ((kerBaseChangeEquiv T Tg d).trans ek)
  exact ⟨g, hg, ⟨Basis.ofEquivFun eL⟩⟩

/-- **A free dual cokernel of the rank of the source forces the base changed map to vanish.**
If `M` is free of rank `r` and `T ⊗ DualCoker d` is free of rank `r`, then `d ⊗ T = 0`. -/
theorem baseChange_eq_zero_of_dualCoker_equiv (d : M →ₗ[S] N) {r : ℕ}
    (eM : M ≃ₗ[S] (Fin r → S)) (eQ : T ⊗[S] DualCoker d ≃ₗ[T] (Fin r → T)) :
    d.baseChange T = 0 := by
  classical
  set d' := d.baseChange T
  let eD : Dual T (T ⊗[S] M) ≃ₗ[T] (Fin r → T) :=
    (Module.Dual.congr ((LinearEquiv.baseChange S T M (Fin r → S) eM).trans
      (TensorProduct.piScalarRight S T T (Fin r)))).trans
      (Pi.basisFun T (Fin r)).dualBasis.equivFun
  let eC : DualCoker d' ≃ₗ[T] (Fin r → T) := (dualCokerBaseChangeEquiv T d).trans eQ
  let π := (LinearMap.range d'.dualMap).mkQ
  have hsurj : Function.Surjective (eC.toLinearMap ∘ₗ π ∘ₗ eD.symm.toLinearMap) :=
    eC.surjective.comp ((Submodule.mkQ_surjective _).comp eD.symm.surjective)
  have hinj := OrzechProperty.injective_of_surjective_endomorphism _ hsurj
  have hπ : Function.Injective π := by
    intro x y hxy
    have h := @hinj (eD x) (eD y) (by
      simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearEquiv.symm_apply_apply]
      rw [hxy])
    exact eD.injective h
  have hrange : LinearMap.range d'.dualMap = ⊥ :=
    (Submodule.ker_mkQ (LinearMap.range d'.dualMap)).symm.trans (LinearMap.ker_eq_bot.2 hπ)
  refine LinearMap.ext fun m => (forall_dual_apply_eq_zero_iff T _).1 fun φ => ?_
  exact congrArg (fun ψ : Dual T (T ⊗[S] M) => ψ m)
    (LinearMap.congr_fun (LinearMap.range_eq_bot.1 hrange) φ)

end Local

open TensorProduct in
/-- **A base change which is finite locally free of rank `r` is free of rank `r` on a principal
open around each prime.** -/
theorem _root_.Module.IsFiniteLocallyFreeOfRank.exists_away_baseChange_equiv
    {S : Type u} [CommRing S] {Q : Type u} [AddCommGroup Q] [Module S Q] (T : Type u)
    [CommRing T] [Algebra S T] {r : ℕ}
    (h : Module.IsFiniteLocallyFreeOfRank T (T ⊗[S] Q) r) (p : Ideal T) [p.IsPrime] :
    ∃ g : T, g ∉ p ∧ Nonempty (Localization.Away g ⊗[S] Q ≃ₗ[Localization.Away g]
      (Fin r → Localization.Away g)) := by
  exact exists_away_baseChange_equiv_aux T h p

end LinearMap
