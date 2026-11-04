module

public import StacksFrontier.AlgebraicGeometry.Picard.TorsionCharpoly
public import StacksFrontier.Algebra.Polynomial.PadicResultant

/-!
# The `ℓ`-adic characteristic polynomial from kernel counts given by a rational norm form

The variant of `Stacks.Picard.charpoly_levelMatrix_eq` ([Mumford, *Abelian varieties*, §19,
Theorem 4]) for a monic `χ ∈ ℚ[X]`: if `#Ker R(u) = N(R mod χ)` for every `R ∈ ℤ[X]` with
`p ∤ R(0)`, then the characteristic polynomials of `u` on the `P[ℓ^n]` are the reductions of one
`F ∈ ℤ_ℓ[X]`, and `F = χ` in `ℚ_ℓ[X]`; in particular `χ` has `ℓ`-integral coefficients. This is
the form in which the degree of a polynomial in an endomorphism of an abelian variety comes,
as a norm form `Stacks.Polynomial.normForm`.

## Main results

* `Stacks.Picard.exists_charpoly_levelMatrix_eq_of_normForm`.
-/

@[expose] public noncomputable section

open Polynomial Stacks.TorsionCount

namespace Stacks.Picard

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {P : Type*} [AddCommGroup P] (u : P →+ P) {r : ℕ}
  [∀ n : ℕ, Module (ZMod (ℓ ^ n)) (Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ n))]

/-- A polynomial over `ℤ_ℓ` whose reductions mod `ℓ^N` are characteristic polynomials of `r × r`
matrices has `r`-th coefficient `1`. -/
private theorem coeff_eq_one_of_map_toZModPow_eq_charpoly {F : ℤ_[ℓ][X]}
    {A : ∀ N : ℕ, Matrix (Fin r) (Fin r) (ZMod (ℓ ^ N))}
    (hF : ∀ N, F.map (PadicInt.toZModPow N) = (A N).charpoly) : F.coeff r = 1 := by
  refine PadicInt.ext_of_toZModPow.1 fun N => ?_
  rw [map_one, ← coeff_map, hF N]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : Subsingleton (ZMod (ℓ ^ 0)) := by
      rw [pow_zero]
      infer_instance
    exact Subsingleton.elim _ _
  · have : Fact (1 < ℓ ^ N) := ⟨Nat.one_lt_pow hN.ne' hℓ.out.one_lt⟩
    have := (A N).charpoly_monic.coeff_natDegree
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this

omit hℓ in
/-- If an integral matrix `B` lifts `R` of the level matrix of `u` at level `N`, the kernel of `B`
mod `ℓ^N` has as many elements as the `ℓ^N`-torsion of `Ker R(u)`. -/
private theorem natCard_ker_mulVecMod_eq_natCard_tors {N : ℕ}
    (E : Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ N) ≃+ (Fin r → ZMod (ℓ ^ N))) (R : ℤ[X])
    {B : Matrix (Fin r) (Fin r) ℤ}
    (hB : (Int.castRingHom (ZMod (ℓ ^ N))).mapMatrix B = aeval (levelMatrix u N E) R) :
    Nat.card (mulVecMod (ℓ := ℓ) B N).ker = Nat.card (tors (aeval (asEnd u) R).ker (ℓ ^ N)) :=
  Nat.card_congr
    { toFun := fun z => ⟨⟨E.symm z.1, by
        show (aeval (asEnd u) R) _ = 0
        rw [← aeval_levelMatrix_mulVec]
        have hz := z.2
        rw [AddMonoidHom.mem_ker] at hz
        change (B.map (Int.castRingHom (ZMod (ℓ ^ N)))).mulVec z.1 = 0 at hz
        rw [← RingHom.mapMatrix_apply, hB] at hz
        rw [hz, map_zero]
        rfl⟩, by
          rw [mem_tors]
          apply Subtype.ext
          have := (E.symm z.1).2
          rw [Submodule.mem_torsionBy_iff] at this
          rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero, ← natCast_zsmul]
          push_cast
          exact this⟩
      invFun := fun x => ⟨E ⟨x.1.1, by
          rw [Submodule.mem_torsionBy_iff]
          have h' := congrArg Subtype.val (mem_tors.1 x.2)
          rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero, ← natCast_zsmul] at h'
          push_cast at h'
          exact h'⟩, by
          rw [AddMonoidHom.mem_ker]
          show (B.map (Int.castRingHom (ZMod (ℓ ^ N)))).mulVec _ = 0
          rw [← RingHom.mapMatrix_apply, hB]
          refine E.symm.injective (Subtype.ext ?_)
          rw [map_zero, Submodule.coe_zero, aeval_levelMatrix_mulVec, AddEquiv.symm_apply_apply]
          exact x.1.2⟩
      left_inv := fun z => by
        apply Subtype.ext
        simp only
        rw [show (⟨(E.symm z.1 : P), _⟩ : Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ N)) =
          E.symm z.1 from rfl, AddEquiv.apply_symm_apply]
      right_inv := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        simp only [AddEquiv.symm_apply_apply] }

/-- If the reductions mod `ℓ^N` of `F ∈ ℤ_ℓ[X]` are the characteristic polynomials of `u` on the
`P[ℓ^N]`, then for every `R ∈ ℤ[X]` with `Ker R(u)` finite, the resultant of `F` and `R` has the
`ℓ`-adic norm of `#Ker R(u)`. -/
private theorem norm_resultant_eq_norm_natCard_ker
    (E : ∀ N, Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ N) ≃+ (Fin r → ZMod (ℓ ^ N))) {F : ℤ_[ℓ][X]}
    (hF : ∀ N, F.map (PadicInt.toZModPow N) = (levelMatrix u N (E N)).charpoly) {R : ℤ[X]}
    (hR : Nat.card (aeval (asEnd u) R).ker ≠ 0) :
    ‖F.resultant (R.map (Int.castRingHom ℤ_[ℓ])) r R.natDegree‖ =
      ‖(((Nat.card (aeval (asEnd u) R).ker : ℕ) : ℤ) : ℤ_[ℓ])‖ := by
  have : Finite (aeval (asEnd u) R).ker := Nat.finite_of_card_ne_zero hR
  set d : ℤ := ((Nat.card (aeval (asEnd u) R).ker : ℕ) : ℤ)
  have hK : Nat.card (aeval (asEnd u) R).ker = d.natAbs := (Int.natAbs_natCast _).symm
  have hres : d ≠ 0 := Int.natCast_ne_zero.2 hR
  set e := d.natAbs.factorization ℓ
  set N := e + 1
  set A := levelMatrix u N (E N)
  set B : Matrix (Fin r) (Fin r) ℤ := A.map fun x => ((x.val : ℕ) : ℤ)
  have hB : B.map (Int.castRingHom (ZMod (ℓ ^ N))) = A := by
    ext i j
    simp [B]
  set BR := aeval B R
  have hBR : (Int.castRingHom (ZMod (ℓ ^ N))).mapMatrix BR = aeval A R := by
    rw [Stacks.Polynomial.mapMatrix_aeval, RingHom.mapMatrix_apply, hB,
      show Int.castRingHom (ZMod (ℓ ^ N)) = algebraMap ℤ (ZMod (ℓ ^ N)) from RingHom.ext_int _ _,
      aeval_map_algebraMap]
  have hcard : Nat.card (mulVecMod (ℓ := ℓ) BR N).ker = ℓ ^ e := by
    rw [natCard_ker_mulVecMod_eq_natCard_tors u (E N) R hBR,
      natCard_tors_pow_eq N (by rw [hK]; omega), hK]
  have hlt : Nat.card (mulVecMod (ℓ := ℓ) BR N).ker < ℓ ^ N := by
    rw [hcard]
    exact Nat.pow_lt_pow_right hℓ.out.one_lt (Nat.lt_succ_self e)
  obtain ⟨hdet0, -, hdetcard⟩ := natCard_ker_mulVecMod_of_lt BR N hlt
  have hv : BR.det.natAbs.factorization ℓ = e :=
    Nat.pow_right_injective hℓ.out.two_le (hdetcard.symm.trans hcard)
  have hmod : PadicInt.toZModPow N (F.resultant (R.map (Int.castRingHom ℤ_[ℓ])) r R.natDegree) =
      PadicInt.toZModPow N (BR.det : ℤ_[ℓ]) := by
    rw [← resultant_map_map, hF N, Polynomial.map_map, map_intCast,
      Stacks.Polynomial.det_aeval_eq_resultant_charpoly_int,
      show (PadicInt.toZModPow N).comp (Int.castRingHom ℤ_[ℓ]) =
        Int.castRingHom (ZMod (ℓ ^ N)) from RingHom.ext_int _ _]
    show A.charpoly.resultant _ r R.natDegree = _
    rw [← hB, Matrix.charpoly_map, resultant_map_map, eq_intCast]
  have hsub : ‖F.resultant (R.map (Int.castRingHom ℤ_[ℓ])) r R.natDegree - (BR.det : ℤ_[ℓ])‖ ≤
      (ℓ : ℝ) ^ (-(N : ℤ)) := by
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
      map_sub, hmod, sub_self]
  have hDnorm : (ℓ : ℝ) ^ (-(N : ℤ)) < ‖(BR.det : ℤ_[ℓ])‖ := by
    refine lt_of_not_ge fun hle => ?_
    have hdvd : ℓ ^ (e + 1) ∣ BR.det.natAbs := by
      rw [← Int.natCast_dvd_natCast, Int.natCast_natAbs, dvd_abs]
      exact_mod_cast PadicInt.norm_int_le_pow_iff_dvd.1 hle
    exact Nat.pow_succ_factorization_not_dvd (Int.natAbs_ne_zero.2 hdet0) hℓ.out (hv ▸ hdvd)
  rw [padicInt_norm_eq_of_norm_sub_lt (hsub.trans_lt hDnorm),
    padicInt_norm_intCast_eq hdet0 hres hv]

/-- **The `ℓ`-adic characteristic polynomial of an endomorphism with kernel counts given by a
rational norm form.** Let `P[ℓ^N] ≅ (ℤ/ℓ^N)^r` for all `N`, `p ≠ ℓ` primes, `χ ∈ ℚ[X]` monic of
degree `r` with `#Ker R(u) = N(R mod χ)` whenever `p ∤ R(0)`. Then there is `F ∈ ℤ_ℓ[X]` equal to
`χ` in `ℚ_ℓ[X]` whose reduction mod `ℓ^n` is the characteristic polynomial of `u` on `P[ℓ^n]`. -/
theorem exists_charpoly_levelMatrix_eq_of_normForm (p : ℕ) (hp : p.Prime) (hpℓ : p ≠ ℓ)
    (hP : ∀ N, Nonempty (Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ N) ≃+ (Fin r → ZMod (ℓ ^ N))))
    (χ : ℚ[X]) (hχ : χ.Monic) (hχr : χ.natDegree = r)
    (hker : ∀ R : ℤ[X], ¬ (p : ℤ) ∣ R.coeff 0 →
      (Nat.card (aeval (asEnd u) R).ker : ℚ) = Stacks.Polynomial.normForm χ R) :
    ∃ F : ℤ_[ℓ][X], F.map PadicInt.Coe.ringHom = χ.map (algebraMap ℚ ℚ_[ℓ]) ∧
      ∀ (n : ℕ) (E : Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ n) ≃+ (Fin r → ZMod (ℓ ^ n))),
        (levelMatrix u n E).charpoly = F.map (PadicInt.toZModPow n) := by
  classical
  have E' : ∀ N, Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ N) ≃+ (Fin r → ZMod (ℓ ^ N)) :=
    fun N => (hP N).some
  set c : ∀ N : ℕ, (ZMod (ℓ ^ N))[X] := fun N => (levelMatrix u N (E' N)).charpoly
  obtain ⟨F, hFdeg, hF⟩ := exists_map_toZModPow_eq (ℓ := ℓ) c r
    (fun N => natDegree_charpoly_le _)
    (fun n N h => charpoly_levelMatrix_map u N (E' N) h (E' n))
  have hFr : F.coeff r = 1 :=
    coeff_eq_one_of_map_toZModPow_eq_charpoly (A := fun N => levelMatrix u N (E' N)) hF
  have hFm : F.Monic := Polynomial.monic_of_natDegree_le_of_coeff_eq_one r hFdeg hFr
  have hFn : F.natDegree = r := natDegree_eq_of_le_of_coeff_ne_zero hFdeg (by simp [hFr])
  set ιQ := algebraMap ℚ ℚ_[ℓ]
  have hinj : Function.Injective (PadicInt.Coe.ringHom (p := ℓ)) := Subtype.val_injective
  have hQinj : Function.Injective ιQ := ιQ.injective
  refine ⟨F, ?_, fun n E => ?_⟩
  · refine Stacks.Polynomial.eq_of_norm_resultant_intPoly_eq p hp hpℓ (χ.map ιQ)
      (F.map PadicInt.Coe.ringHom) 1 (hχ.map _) (hFm.map _) ?_ one_ne_zero fun R hR0 hres => ?_
    · rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hQinj, hFn, hχr]
    have hRQ : R.map (Int.castRingHom ℚ_[ℓ]) =
        (R.map (Int.castRingHom ℤ_[ℓ])).map PadicInt.Coe.ringHom := by
      rw [Polynomial.map_map, show (PadicInt.Coe.ringHom (p := ℓ)).comp (Int.castRingHom ℤ_[ℓ]) =
        Int.castRingHom ℚ_[ℓ] from RingHom.ext_int _ _]
    have hRQ' : R.map (Int.castRingHom ℚ_[ℓ]) = (R.map (Int.castRingHom ℚ)).map ιQ := by
      rw [Polynomial.map_map]
      congr 1
    have hχres : (χ.map ιQ).resultant (R.map (Int.castRingHom ℚ_[ℓ])) =
        ιQ (Stacks.Polynomial.normForm χ R) := by
      rw [Stacks.Polynomial.normForm_eq_resultant hχ, hRQ', natDegree_map_eq_of_injective hQinj,
        natDegree_map_eq_of_injective hQinj, resultant_map_map]
    have hFres : (F.map PadicInt.Coe.ringHom).resultant (R.map (Int.castRingHom ℚ_[ℓ])) =
        PadicInt.Coe.ringHom (F.resultant (R.map (Int.castRingHom ℤ_[ℓ])) r R.natDegree) := by
      rw [natDegree_map_eq_of_injective (RingHom.injective_int _) R,
        natDegree_map_eq_of_injective hinj, hFn, hRQ, resultant_map_map]
    rw [one_mul, hχres] at hres
    have hR : Nat.card (aeval (asEnd u) R).ker ≠ 0 := fun h0 =>
      hres (by rw [← hker R hR0, h0, Nat.cast_zero, map_zero])
    rw [hχres, hFres, ← hker R hR0]
    show ‖((F.resultant (R.map (Int.castRingHom ℤ_[ℓ])) r R.natDegree : ℤ_[ℓ]) : ℚ_[ℓ])‖ =
      ‖ιQ ((Nat.card (aeval (asEnd u) R).ker : ℕ) : ℚ)‖
    rw [PadicInt.padic_norm_e_of_padicInt, norm_resultant_eq_norm_natCard_ker u E' hF hR,
      ← PadicInt.padic_norm_e_of_padicInt, PadicInt.coe_intCast, map_natCast]
    norm_cast
  · rw [← charpoly_levelMatrix_map u n (E' n) le_rfl E, ZMod.castHom_self, Polynomial.map_id]
    exact (hF n).symm

end Stacks.Picard
