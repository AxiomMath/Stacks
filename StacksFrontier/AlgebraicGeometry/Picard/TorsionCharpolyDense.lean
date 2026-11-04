module

public import StacksFrontier.AlgebraicGeometry.Picard.TorsionCharpolyRat
public import StacksFrontier.Algebra.Polynomial.PadicResultantDense

/-!
# The `ℓ`-adic characteristic polynomial from kernel counts on a dense set of polynomials

`Stacks.Picard.exists_charpoly_levelMatrix_eq_of_normForm` identifies the characteristic
polynomials of an endomorphism `u` on the `P[ℓ^n]` with a rational polynomial `χ`, given that
`#Ker R(u) = N(R mod χ)` for every `R ∈ ℤ[X]` with `p ∤ R(0)`. This file proves the same
conclusion from the kernel counts on any set of integral polynomials which is `ℓ`-adically dense
in the sense of `Stacks.Polynomial.eq_of_norm_resultant_intPoly_eq_of_dense`.

For an arbitrary endomorphism `α` of an abelian variety in characteristic `p` the kernel count
`#Ker R(α) = deg R(α)` is only available when `R(α)` is étale, which holds for `R` congruent to a
constant prime to `p` modulo `p` but not for every `R` with `p ∤ R(0)`
([Mumford, *Abelian varieties*, §19, Theorem 4]).

## Main results

* `Stacks.Picard.exists_charpoly_levelMatrix_eq_of_normForm_of_dense`.
-/

@[expose] public noncomputable section

open Polynomial Stacks.TorsionCount

namespace Stacks.Picard

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {P : Type*} [AddCommGroup P] (u : P →+ P) {r : ℕ}
  [∀ n : ℕ, Module (ZMod (ℓ ^ n)) (Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ n))]

/-- A polynomial over `ℤ_ℓ` reducing modulo every `ℓ^N` to the characteristic polynomial of an
`r × r` matrix has `X^r`-coefficient `1`. -/
private theorem coeff_eq_one_of_map_toZModPow_eq_charpoly {F : ℤ_[ℓ][X]}
    (M : ∀ N : ℕ, Matrix (Fin r) (Fin r) (ZMod (ℓ ^ N)))
    (hF : ∀ N, F.map (PadicInt.toZModPow N) = (M N).charpoly) : F.coeff r = 1 := by
  refine PadicInt.ext_of_toZModPow.1 fun N => ?_
  rw [map_one, ← coeff_map, hF N]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : Subsingleton (ZMod (ℓ ^ 0)) := by
      rw [pow_zero]
      infer_instance
    exact Subsingleton.elim _ _
  · have : Fact (1 < ℓ ^ N) := ⟨Nat.one_lt_pow hN.ne' hℓ.out.one_lt⟩
    have hd := Matrix.charpoly_natDegree_eq_dim (M N)
    rw [Fintype.card_fin] at hd
    have := (Matrix.charpoly_monic (M N)).coeff_natDegree
    rwa [hd] at this

/-- An element of a subgroup `K` is `n`-torsion in `K` iff it is `n`-torsion in the ambient
group. -/
private theorem coe_mem_torsionBy_iff_mem_tors {Q : Type*} [AddCommGroup Q] {K : AddSubgroup Q}
    {n : ℕ} (x : K) : (x : Q) ∈ Submodule.torsionBy ℤ Q (n : ℤ) ↔ x ∈ tors K n := by
  rw [mem_tors, Submodule.mem_torsionBy_iff, ← Subtype.coe_inj, AddSubgroup.coe_nsmul,
    AddSubgroup.coe_zero, natCast_zsmul]

/-- For an integer matrix `M` reducing modulo `ℓ^N` to `R` evaluated at the level-`N` matrix of
`u`, the kernel of `M` on `(ℤ/ℓ^N)^r` is the `ℓ^N`-torsion of `Ker R(u)`. -/
private def kerMulVecModEquivTors (R : ℤ[X]) (N : ℕ)
    (E : Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ N) ≃+ (Fin r → ZMod (ℓ ^ N)))
    (M : Matrix (Fin r) (Fin r) ℤ)
    (hM : (Int.castRingHom (ZMod (ℓ ^ N))).mapMatrix M = aeval (levelMatrix u N E) R) :
    (mulVecMod (ℓ := ℓ) M N).ker ≃ tors (aeval (asEnd u) R).ker (ℓ ^ N) :=
  { toFun := fun z => ⟨⟨E.symm z.1, by
      change (aeval (asEnd u) R) _ = 0
      rw [← aeval_levelMatrix_mulVec]
      have hz := z.2
      rw [AddMonoidHom.mem_ker] at hz
      change (M.map (Int.castRingHom (ZMod (ℓ ^ N)))).mulVec z.1 = 0 at hz
      rw [← RingHom.mapMatrix_apply, hM] at hz
      rw [hz, map_zero]
      rfl⟩, by
        exact (coe_mem_torsionBy_iff_mem_tors _).1 (by exact_mod_cast (E.symm z.1).2)⟩
    invFun := fun x => ⟨E ⟨x.1.1, by exact_mod_cast (coe_mem_torsionBy_iff_mem_tors _).2 x.2⟩, by
        rw [AddMonoidHom.mem_ker]
        change (M.map (Int.castRingHom (ZMod (ℓ ^ N)))).mulVec _ = 0
        rw [← RingHom.mapMatrix_apply, hM]
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

/-- An `ℓ`-adic integer congruent modulo `ℓ^(e+1)` to a nonzero integer `D` with `v_ℓ(D) = e` has
the norm of `D`. -/
private theorem norm_eq_of_toZModPow_eq {x : ℤ_[ℓ]} {D : ℤ} (hD : D ≠ 0) {e : ℕ}
    (he : D.natAbs.factorization ℓ = e)
    (hx : PadicInt.toZModPow (e + 1) x = PadicInt.toZModPow (e + 1) (D : ℤ_[ℓ])) :
    ‖x‖ = ‖(D : ℤ_[ℓ])‖ := by
  have hsub : ‖x - (D : ℤ_[ℓ])‖ ≤ (ℓ : ℝ) ^ (-((e + 1 : ℕ) : ℤ)) := by
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
      map_sub, hx, sub_self]
  refine padicInt_norm_eq_of_norm_sub_lt (hsub.trans_lt (lt_of_not_ge fun hle => ?_))
  have := PadicInt.norm_int_le_pow_iff_dvd.1 hle
  have hdvd : ℓ ^ (e + 1) ∣ D.natAbs := by
    rw [← Int.natCast_dvd_natCast, Int.natCast_natAbs, dvd_abs]
    exact_mod_cast this
  exact Nat.pow_succ_factorization_not_dvd (Int.natAbs_ne_zero.2 hD) hℓ.out (he ▸ hdvd)

/-- If `F ∈ ℤ_ℓ[X]` reduces modulo every `ℓ^N` to the characteristic polynomial of `u` on `P[ℓ^N]`
and `Ker R(u)` is finite, then the resultant of `F` and `R` has the norm of `#Ker R(u)`. -/
private theorem norm_resultant_eq_norm_natCard_ker {F : ℤ_[ℓ][X]}
    (E' : ∀ N, Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ N) ≃+ (Fin r → ZMod (ℓ ^ N)))
    (hF : ∀ N, F.map (PadicInt.toZModPow N) = (levelMatrix u N (E' N)).charpoly)
    (R : ℤ[X]) (hR : Nat.card (aeval (asEnd u) R).ker ≠ 0) :
    ‖F.resultant (R.map (Int.castRingHom ℤ_[ℓ])) r R.natDegree‖ =
      ‖(((Nat.card (aeval (asEnd u) R).ker : ℕ) : ℤ) : ℤ_[ℓ])‖ := by
  set K := (aeval (asEnd u) R).ker
  set d : ℤ := ((Nat.card K : ℕ) : ℤ)
  have hK : Nat.card K = d.natAbs := (Int.natAbs_natCast _).symm
  have : Finite K := Nat.finite_of_card_ne_zero hR
  set e := d.natAbs.factorization ℓ
  set N := e + 1
  set A := levelMatrix u N (E' N)
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
    rw [Nat.card_congr (kerMulVecModEquivTors u R N (E' N) BR hBR),
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
      show (PadicInt.toZModPow N).comp (Int.castRingHom ℤ_[ℓ]) = Int.castRingHom (ZMod (ℓ ^ N))
        from RingHom.ext_int _ _]
    show A.charpoly.resultant _ r R.natDegree = _
    rw [← hB, Matrix.charpoly_map, resultant_map_map, eq_intCast]
  rw [norm_eq_of_toZModPow_eq hdet0 hv hmod,
    padicInt_norm_intCast_eq hdet0 (Int.natCast_ne_zero.2 hR) hv]

/-- **The `ℓ`-adic characteristic polynomial of an endomorphism with kernel counts given by a
rational norm form, on a dense set of polynomials.** Let `P[ℓ^N] ≅ (ℤ/ℓ^N)^r` for all `N`, let
`good` be a set of integral polynomials such that every `S ∈ ℤ_ℓ[X]` is, modulo every `ℓ^N`,
congruent to a member of `good` of the same degree, and let `χ ∈ ℚ[X]` be monic of degree `r`
with `#Ker R(u) = N(R mod χ)` for every `R ∈ good` with `N(R mod χ) ≠ 0`. Then there is
`F ∈ ℤ_ℓ[X]` equal to `χ` in `ℚ_ℓ[X]` whose reduction mod `ℓ^n` is the characteristic polynomial
of `u` on `P[ℓ^n]`. -/
theorem exists_charpoly_levelMatrix_eq_of_normForm_of_dense (good : ℤ[X] → Prop)
    (hdense : ∀ (S : ℤ_[ℓ][X]) (N : ℕ), ∃ R : ℤ[X], R.natDegree = S.natDegree ∧ good R ∧
      (R.map (Int.castRingHom ℤ_[ℓ])).map (PadicInt.toZModPow N) = S.map (PadicInt.toZModPow N))
    (hP : ∀ N, Nonempty (Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ N) ≃+ (Fin r → ZMod (ℓ ^ N))))
    (χ : ℚ[X]) (hχ : χ.Monic) (hχr : χ.natDegree = r)
    (hker : ∀ R : ℤ[X], good R → Stacks.Polynomial.normForm χ R ≠ 0 →
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
    coeff_eq_one_of_map_toZModPow_eq_charpoly (fun N => levelMatrix u N (E' N)) hF
  have hFm : F.Monic := Polynomial.monic_of_natDegree_le_of_coeff_eq_one r hFdeg hFr
  have hFn : F.natDegree = r := natDegree_eq_of_le_of_coeff_ne_zero hFdeg (by simp [hFr])
  set ιQ := algebraMap ℚ ℚ_[ℓ]
  have hinj : Function.Injective (PadicInt.Coe.ringHom (p := ℓ)) := Subtype.val_injective
  refine ⟨F, ?_, fun n E => ?_⟩
  · refine Stacks.Polynomial.eq_of_norm_resultant_intPoly_eq_of_dense good hdense (χ.map ιQ)
      (F.map PadicInt.Coe.ringHom) 1 (hχ.map _) (hFm.map _) ?_ one_ne_zero fun R hR0 hres => ?_
    · rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective ιQ.injective, hFn, hχr]
    have hRQ : R.map (Int.castRingHom ℚ_[ℓ]) =
        (R.map (Int.castRingHom ℤ_[ℓ])).map PadicInt.Coe.ringHom := by
      rw [Polynomial.map_map]
      congr 1
    have hRQ' : R.map (Int.castRingHom ℚ_[ℓ]) = (R.map (Int.castRingHom ℚ)).map ιQ := by
      rw [Polynomial.map_map]
      congr 1
    have hχres : (χ.map ιQ).resultant (R.map (Int.castRingHom ℚ_[ℓ])) =
        ιQ (Stacks.Polynomial.normForm χ R) := by
      rw [Stacks.Polynomial.normForm_eq_resultant hχ, hRQ',
        natDegree_map_eq_of_injective ιQ.injective, natDegree_map_eq_of_injective ιQ.injective,
        resultant_map_map]
    have hFres : (F.map PadicInt.Coe.ringHom).resultant (R.map (Int.castRingHom ℚ_[ℓ])) =
        PadicInt.Coe.ringHom (F.resultant (R.map (Int.castRingHom ℤ_[ℓ])) r R.natDegree) := by
      rw [natDegree_map_eq_of_injective (RingHom.injective_int _) R,
        natDegree_map_eq_of_injective hinj, hFn, hRQ, resultant_map_map]
    rw [one_mul, hχres] at hres
    have hres' : Stacks.Polynomial.normForm χ R ≠ 0 := fun h0 => hres (by rw [h0, map_zero])
    have hK : Nat.card (aeval (asEnd u) R).ker ≠ 0 := fun h0 =>
      hres' (by rw [← hker R hR0 hres', h0, Nat.cast_zero])
    rw [hχres, hFres, ← hker R hR0 hres']
    show ‖((F.resultant (R.map (Int.castRingHom ℤ_[ℓ])) r R.natDegree : ℤ_[ℓ]) : ℚ_[ℓ])‖ =
      ‖ιQ ((Nat.card (aeval (asEnd u) R).ker : ℕ) : ℚ)‖
    rw [PadicInt.padic_norm_e_of_padicInt, norm_resultant_eq_norm_natCard_ker u E' hF R hK,
      ← PadicInt.padic_norm_e_of_padicInt, PadicInt.coe_intCast, map_natCast]
    norm_cast
  · rw [← charpoly_levelMatrix_map u n (E' n) le_rfl E, ZMod.castHom_self, Polynomial.map_id]
    exact (hF n).symm

end Stacks.Picard
