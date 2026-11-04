module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Etale.AssociatedGraded
public import StacksFrontier.RingTheory.Etale.Basic
public import StacksFrontier.RingTheory.Etale.LiftUnitsIdempotents
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow
public import StacksFrontier.RingTheory.Ideal.Quotient.MapBijective

/-!
# Lifting a factorization of a monic polynomial along an étale extension

Let `A` be a commutative ring, `I` an ideal, and `f ∈ A[X]` monic. A factorization `f = g h`
modulo `I` into coprime factors lifts, after an étale extension `A → A'` that does not change the
quotient by `I`, to a factorization of `f` over `A'` reducing to the given one — provided the
leading coefficient of `g` is a unit modulo `I`. This file proves the monic case, deduces the
unit-leading-coefficient case from it, and records the counterexample showing that the hypothesis
on the leading coefficient cannot simply be dropped.

## Main results

* `exists_etale_lift_of_isCoprime_factorization`: the lift when both factors are monic.
* `exists_etale_lift_of_isUnit_leadingCoeff_isCoprime_factorization`: the lift when the leading
  coefficient of the first factor is a unit.
* `counterexample_to_etale_lift_without_isUnit_leadingCoeff`: over `ℤ` with `I = (4)` the
  polynomial `1` factors as `(2X² + 2X + 1)²` with coprime factors and non-unit leading
  coefficient, and no étale extension unchanged modulo `4` carries a corresponding factorization.

## Implementation notes

The monic case is reduced to the universal coprime factorization ring of
`Mathlib.RingTheory.Polynomial.UniversalFactorizationRing`: it carries a tautological
factorization of `f`, the given factorization modulo `I` is a retraction of it onto `A ⧸ I`, and
that retraction is étale, so it is cut out by an idempotent which can be inverted to give `A'`.

The unit case follows by first lifting the leading coefficient to a unit of an étale extension
(Stacks 07LX, `Algebra.exists_etale_bijective_quotientMap_isUnit`) and rescaling `g` and `h` so
that both become monic.

The counterexample is arithmetic rather than formal: an étale `ℤ`-algebra unchanged modulo `4`
has `2`-adic completion `ℤ_[2]`, and no polynomial over `ℤ_[2]` congruent to `2X² + 2X + 1`
modulo `4` is a unit, so the two reduction equalities of Stacks 07M1 cannot both hold. Its
elaboration needs raised limits and the pre-`respectTransparency` defeq behaviour, so it is kept
in its own section: setting those options for the whole file changes how `rfl`-like goals close in
the two lifting proofs above.

## References

* [Stacks Project, Tag 0ALH](https://stacks.math.columbia.edu/tag/0ALH)
* [Stacks Project, Tag 07M1](https://stacks.math.columbia.edu/tag/07M1)
* [Stacks Project, Tag 07M2](https://stacks.math.columbia.edu/tag/07M2)
-/

open Polynomial

universe u v

@[expose] public section

/-- **Stacks 0ALH.** A factorization of a monic polynomial into coprime monic factors modulo an
ideal lifts to a factorization into monic polynomials over an étale algebra which induces an
isomorphism modulo the extended ideal. -/
@[stacks 0ALH]
theorem exists_etale_lift_of_isCoprime_factorization
    {A : Type u} [CommRing A] (I : Ideal A) (f : Polynomial A)
    (gbar hbar : Polynomial (A ⧸ I)) (hf : f.Monic) (hgbar : gbar.Monic)
    (hhbar : hbar.Monic) (hfac : f.map (Ideal.Quotient.mk I) = gbar * hbar)
    (hcoprime : IsCoprime gbar hbar) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (g' h' : Polynomial A'),
      Algebra.Etale A A' ∧
      Function.Bijective
        (Ideal.quotientMap (I.map (algebraMap A A')) (algebraMap A A')
          Ideal.le_comap_map) ∧
      g'.Monic ∧ h'.Monic ∧ IsCoprime g' h' ∧
      f.map (algebraMap A A') = g' * h' ∧
      gbar.map
          (Ideal.quotientMap (I.map (algebraMap A A')) (algebraMap A A')
            Ideal.le_comap_map) =
        g'.map (Ideal.Quotient.mk (I.map (algebraMap A A'))) ∧
      hbar.map
          (Ideal.quotientMap (I.map (algebraMap A A')) (algebraMap A A')
            Ideal.le_comap_map) =
        h'.map (Ideal.Quotient.mk (I.map (algebraMap A A'))) := by
  cases subsingleton_or_nontrivial (A ⧸ I) with
  | inl htriv =>
    have : Subsingleton (Localization.Away (0 : A)) := subsingleton_of_zero_eq_one <|
      isUnit_zero_iff.mp <| by
        simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (0 : A)) (0 : A)
    exact ⟨Localization.Away (0 : A), inferInstance, inferInstance, 0, 0, inferInstance,
      ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ y⟩⟩,
      monic_of_subsingleton _, monic_of_subsingleton _, ⟨0, 0, Subsingleton.elim _ _⟩,
      Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  | inr hnontriv =>
  let n := gbar.natDegree
  let m := hbar.natDegree
  have hdeg : f.natDegree = n + m := by
    simpa [n, m, hgbar.natDegree_mul hhbar, hf.natDegree_map] using
      congrArg Polynomial.natDegree hfac
  let p : MonicDegreeEq A (n + m) := .mk f hf hdeg
  let B := UniversalCoprimeFactorizationRing n m rfl p
  let φ : B →ₐ[A] A ⧸ I :=
    (UniversalCoprimeFactorizationRing.homEquiv (A ⧸ I) n m rfl p).symm
      ⟨⟨.mk gbar hgbar rfl, .mk hbar hhbar rfl⟩, by simpa [p] using hfac.symm, hcoprime⟩
  let J : Ideal B := I.map (algebraMap A B)
  let C := B ⧸ J
  let : Algebra (A ⧸ I) C := by
    dsimp [C, J]
    infer_instance
  let q : A ⧸ I →+* C := algebraMap (A ⧸ I) C
  let eBC : C ≃ₐ[A ⧸ I] TensorProduct A (A ⧸ I) B :=
    by
      show (B ⧸ I.map (algebraMap A B)) ≃ₐ[A ⧸ I] TensorProduct A (A ⧸ I) B
      exact Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I
  let : Algebra.Etale (A ⧸ I) C := by
    exact Algebra.Etale.of_equiv eBC.symm
  have hJφ : J ≤ RingHom.ker φ.toRingHom := by
    dsimp [J]
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    show φ (algebraMap A B a) = 0
    rw [φ.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  let σr : C →+* A ⧸ I := Ideal.Quotient.lift J φ.toRingHom hJφ
  have hσq : σr.comp q = RingHom.id (A ⧸ I) := by
    ext a
    show σr (q (Ideal.Quotient.mk I a)) = Ideal.Quotient.mk I a
    rw [show q (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J (algebraMap A B a) by
      exact Ideal.quotientMap_mk]
    dsimp [σr]
    show (Ideal.Quotient.lift J φ.toRingHom hJφ)
      (Ideal.Quotient.mk J (algebraMap A B a)) = Ideal.Quotient.mk I a
    show φ (algebraMap A B a) = Ideal.Quotient.mk I a
    rw [φ.commutes]
    exact DFunLike.congr_fun (Ideal.Quotient.algebraMap_eq I) a
  let : Algebra C (A ⧸ I) := σr.toAlgebra
  have hσsurj : Function.Surjective (algebraMap C (A ⧸ I)) := by
    intro a
    exact ⟨q a, DFunLike.congr_fun hσq a⟩
  have : Algebra.Etale C (A ⧸ I) := by
    rw [← RingHom.etale_algebraMap]
    apply RingHom.Etale.of_comp (f := q) (g := σr)
    · show (algebraMap (A ⧸ I) C).FormallyUnramified
      exact RingHom.formallyUnramified_algebraMap.mpr
        (inferInstance : Algebra.FormallyUnramified (A ⧸ I) C)
    · show (algebraMap (A ⧸ I) C).FiniteType
      exact RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType (A ⧸ I) C)
    · rw [hσq]
      show (algebraMap (A ⧸ I) (A ⧸ I)).Etale
      exact (RingHom.etale_algebraMap (R := A ⧸ I) (S := A ⧸ I)).mpr inferInstance
  obtain ⟨e, he, hker, heLoc⟩ :=
    Algebra.exists_isIdempotentElem_isLocalizationAway_of_surjective C (A ⧸ I) hσsurj
  obtain ⟨h, hh⟩ := Ideal.Quotient.mk_surjective e
  let A' := Localization.Away h
  let g' : Polynomial A' :=
    (UniversalCoprimeFactorizationRing.factor₁ n m rfl p).1.map (algebraMap B A')
  let h' : Polynomial A' :=
    (UniversalCoprimeFactorizationRing.factor₂ n m rfl p).1.map (algebraMap B A')
  let K : Ideal A' := I.map (algebraMap A A')
  let D := A' ⧸ K
  let k : A ⧸ I →+* D := Ideal.quotientMap K (algebraMap A A') Ideal.le_comap_map
  let ρ : B →+* D := (Ideal.Quotient.mk K).comp (algebraMap B A')
  have hJρ : J ≤ RingHom.ker ρ := by
    dsimp [J]
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    show Ideal.Quotient.mk K (algebraMap B A' (algebraMap A B a)) = 0
    rw [← IsScalarTower.algebraMap_apply A B A']
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha)
  let t : C →+* D := Ideal.Quotient.lift J ρ hJρ
  have hφh : φ h = algebraMap C (A ⧸ I) e := by
    show φ h = σr e
    rw [← hh]
    rfl
  have hφhUnit : IsUnit (φ h) := by
    rw [hφh]
    exact IsLocalization.map_units (A ⧸ I) ⟨e, Submonoid.mem_powers _⟩
  let ψ : A' →+* A ⧸ I := IsLocalization.Away.lift h hφhUnit
  have hIψ : K ≤ RingHom.ker ψ := by
    dsimp [K]
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    show ψ (algebraMap A A' a) = 0
    rw [show algebraMap A A' a = algebraMap B A' (algebraMap A B a) by
      exact IsScalarTower.algebraMap_apply A B A' a]
    rw [IsLocalization.Away.lift_eq]
    show φ (algebraMap A B a) = 0
    rw [φ.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  let ψq : D →+* A ⧸ I := Ideal.Quotient.lift K ψ hIψ
  have hkψ_left : ψq.comp k = RingHom.id (A ⧸ I) := by
    ext a
    show ψq (k (Ideal.Quotient.mk I a)) = Ideal.Quotient.mk I a
    rw [show k (Ideal.Quotient.mk I a) = Ideal.Quotient.mk K (algebraMap A A' a) by
      exact Ideal.quotientMap_mk]
    dsimp [ψq]
    show (Ideal.Quotient.lift K ψ hIψ) (Ideal.Quotient.mk K (algebraMap A A' a)) =
      Ideal.Quotient.mk I a
    show ψ (algebraMap A A' a) = Ideal.Quotient.mk I a
    dsimp [ψ]
    rw [show algebraMap A A' a = algebraMap B A' (algebraMap A B a) by
      exact IsScalarTower.algebraMap_apply A B A' a]
    have hlift := IsLocalization.Away.lift_eq (S := A') h hφhUnit (algebraMap A B a)
    exact hlift.trans ((φ.commutes a).trans
      (DFunLike.congr_fun (Ideal.Quotient.algebraMap_eq I) a))
  have hkey (b : B) : k (φ b) = Ideal.Quotient.mk K (algebraMap B A' b) := by
    let c : C := Ideal.Quotient.mk J b
    have hd : c - q (φ b) ∈ RingHom.ker σr := by
      rw [RingHom.mem_ker, map_sub]
      have hc : σr c = φ b := by
        dsimp [c, σr]
        rfl
      have hq : σr (q (φ b)) = φ b := by
        exact DFunLike.congr_fun hσq (φ b)
      rw [hc, hq, sub_self]
    change c - q (φ b) ∈ RingHom.ker (algebraMap C (A ⧸ I)) at hd
    rw [hker, Ideal.mem_span_singleton] at hd
    obtain ⟨z, hz⟩ := hd
    have hteUnit : IsUnit (t e) := by
      rw [← hh]
      show IsUnit (Ideal.Quotient.mk K (algebraMap B A' h))
      exact (IsLocalization.Away.algebraMap_isUnit (S := A') h).map (Ideal.Quotient.mk K)
    have hte : t e = 1 :=
      (IsIdempotentElem.iff_eq_one_of_isUnit hteUnit).mp (he.map t)
    have htd : t (c - q (φ b)) = 0 := by
      rw [hz, map_mul, map_sub, map_one, hte, sub_self]
      exact zero_mul (t z)
    have htq (a : A ⧸ I) : t (q a) = k a := by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      show t (Ideal.Quotient.mk J (algebraMap A B a)) =
        Ideal.Quotient.mk K (algebraMap A A' a)
      show ρ (algebraMap A B a) = Ideal.Quotient.mk K (algebraMap A A' a)
      simp [ρ, IsScalarTower.algebraMap_apply A B A']
    have htc : t c = Ideal.Quotient.mk K (algebraMap B A' b) := by
      show ρ b = Ideal.Quotient.mk K (algebraMap B A' b)
      rfl
    rw [map_sub, htc, htq] at htd
    exact sub_eq_zero.mp htd |>.symm
  have hkψ_right : k.comp ψq = RingHom.id D := by
    apply Ideal.Quotient.ringHom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers h)
    ext b
    simp only [RingHom.comp_apply]
    show k (ψ (algebraMap B A' b)) = Ideal.Quotient.mk K (algebraMap B A' b)
    rw [IsLocalization.Away.lift_eq]
    exact hkey b
  have hmaps : k.comp φ.toRingHom = (Ideal.Quotient.mk K).comp (algebraMap B A') := by
    ext b
    exact hkey b
  have hφ := (UniversalCoprimeFactorizationRing.homEquiv (A ⧸ I) n m rfl p).apply_symm_apply
    ⟨⟨.mk gbar hgbar rfl, .mk hbar hhbar rfl⟩, by simpa [p] using hfac.symm, hcoprime⟩
  have hgφ :
      (UniversalCoprimeFactorizationRing.factor₁ n m rfl p).1.map φ.toRingHom = gbar :=
    (congrArg Subtype.val (UniversalCoprimeFactorizationRing.homEquiv_comp_fst
      B n m rfl p (AlgHom.id A B) φ)).symm.trans
      (congrArg (fun z => z.1.1.1) hφ)
  have hhφ :
      (UniversalCoprimeFactorizationRing.factor₂ n m rfl p).1.map φ.toRingHom = hbar :=
    (congrArg Subtype.val (UniversalCoprimeFactorizationRing.homEquiv_comp_snd
      B n m rfl p (AlgHom.id A B) φ)).symm.trans
      (congrArg (fun z => z.1.2.1) hφ)
  refine ⟨A', inferInstance, inferInstance, g', h', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Algebra.Etale.comp A B A'
  · exact ⟨fun _ _ H => by
      calc
        _ = ψq (k _) := (DFunLike.congr_fun hkψ_left _).symm
        _ = ψq (k _) := congrArg ψq H
        _ = _ := DFunLike.congr_fun hkψ_left _,
      fun y => ⟨ψq y, by
        have := DFunLike.congr_fun hkψ_right y
        exact this⟩⟩
  · exact (UniversalCoprimeFactorizationRing.factor₁ n m rfl p).monic.map _
  · exact (UniversalCoprimeFactorizationRing.factor₂ n m rfl p).monic.map _
  · exact (UniversalCoprimeFactorizationRing.isCoprime_factor₁_factor₂ n m rfl p).map
      (Polynomial.mapRingHom (algebraMap B A'))
  · rw [show algebraMap A A' = (algebraMap B A').comp (algebraMap A B) from rfl]
    simpa [g', h', p, ← Polynomial.map_mul, Polynomial.map_map] using
      congrArg (Polynomial.map (algebraMap B A'))
        (UniversalCoprimeFactorizationRing.factor₁_mul_factor₂ n m rfl p).symm
  · rw [← hgφ, Polynomial.map_map, hmaps, ← Polynomial.map_map]
  · rw [← hhφ, Polynomial.map_map, hmaps, ← Polynomial.map_map]

/-- **Stacks 07M1.** A coprime factorization modulo an ideal, with invertible leading coefficient
of the first factor, lifts to a factorization over an étale algebra which induces an isomorphism
modulo the extended ideal. -/
@[stacks 07M1]
theorem exists_etale_lift_of_isUnit_leadingCoeff_isCoprime_factorization
    {A : Type u} [CommRing A] (I : Ideal A) (f : Polynomial A)
    (gbar hbar : Polynomial (A ⧸ I)) (hf : f.Monic)
    (hgbar : IsUnit gbar.leadingCoeff)
    (hfac : f.map (Ideal.Quotient.mk I) = gbar * hbar)
    (hcoprime : IsCoprime gbar hbar) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (g' h' : Polynomial A'),
      Algebra.Etale A A' ∧
      Function.Bijective
        (Ideal.quotientMap (I.map (algebraMap A A')) (algebraMap A A')
          Ideal.le_comap_map) ∧
      f.map (algebraMap A A') = g' * h' ∧
      gbar.map
          (Ideal.quotientMap (I.map (algebraMap A A')) (algebraMap A A')
            Ideal.le_comap_map) =
        g'.map (Ideal.Quotient.mk (I.map (algebraMap A A'))) ∧
      hbar.map
          (Ideal.quotientMap (I.map (algebraMap A A')) (algebraMap A A')
            Ideal.le_comap_map) =
        h'.map (Ideal.Quotient.mk (I.map (algebraMap A A'))) := by
  obtain ⟨B, instB, instAB, v, hetAB, hv, hqAB, hvbar⟩ :=
    Algebra.exists_etale_bijective_quotientMap_isUnit I gbar.leadingCoeff hgbar
  let J : Ideal B := I.map (algebraMap A B)
  let qAB : A ⧸ I →+* B ⧸ J := Ideal.quotientMap J (algebraMap A B) Ideal.le_comap_map
  let vb : B ⧸ J := Ideal.Quotient.mk J v
  let vinv : B ⧸ J := ↑(hv.map (Ideal.Quotient.mk J)).unit⁻¹
  let G : Polynomial (B ⧸ J) := Polynomial.C vinv * gbar.map qAB
  let H : Polynomial (B ⧸ J) := Polynomial.C vb * hbar.map qAB
  have hqinj : Function.Injective qAB := hqAB.1
  have hlc : (gbar.map qAB).leadingCoeff = vb := by
    rw [Polynomial.leadingCoeff_map_of_injective hqinj]
    exact hvbar.symm
  have hvb : IsUnit vb := hv.map (Ideal.Quotient.mk J)
  have hG : G.Monic := by
    apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [hlc]
    exact (hv.map (Ideal.Quotient.mk J)).unit.inv_mul
  have hprod : (f.map (algebraMap A B)).map (Ideal.Quotient.mk J) = G * H := by
    rw [Polynomial.map_map]
    show f.map (qAB.comp (Ideal.Quotient.mk I)) = _
    rw [← Polynomial.map_map, hfac, Polynomial.map_mul]
    show gbar.map qAB * hbar.map qAB =
      (Polynomial.C vinv * gbar.map qAB) * (Polynomial.C vb * hbar.map qAB)
    rw [mul_assoc, ← mul_assoc (gbar.map qAB), mul_comm (gbar.map qAB) (Polynomial.C vb),
      mul_assoc, ← mul_assoc, ← Polynomial.C_mul]
    have huv : vinv * vb = 1 := (hv.map (Ideal.Quotient.mk J)).unit.inv_mul
    rw [huv, Polynomial.C_1, one_mul]
  have hH : H.Monic := hG.of_mul_monic_left
    (hprod ▸ (hf.map (algebraMap A B)).map (Ideal.Quotient.mk J))
  have hcop : IsCoprime G H := by
    simp only [G, H]
    exact (isCoprime_mul_units_left
      (Polynomial.isUnit_C.mpr (by
        simp [vinv]))
      (Polynomial.isUnit_C.mpr hvb)
      (gbar.map qAB) (hbar.map qAB)).2 (hcoprime.map (Polynomial.mapRingHom qAB))
  obtain ⟨C, instC, instBC, g₀, h₀, hetBC, hqBC, hg₀, hh₀, _, hfac₀, hg₀bar, hh₀bar⟩ :=
    exists_etale_lift_of_isCoprime_factorization J
      (f.map (algebraMap A B)) G H (hf.map _) hG hH hprod hcop
  let : Algebra A C := (inferInstance : Algebra B C).restrictScalars A
  let : IsScalarTower A B C := .of_algebraMap_eq' rfl
  have hJK : J.map (algebraMap B C) = I.map (algebraMap A C) := by
    simp [J, Ideal.map_map, IsScalarTower.algebraMap_eq A B C]
  let g' : Polynomial C := Polynomial.C (algebraMap B C v) * g₀
  let winv : C := ↑(hv.map (algebraMap B C)).unit⁻¹
  let h' : Polynomial C := Polynomial.C winv * h₀
  let L : Ideal C := J.map (algebraMap B C)
  let K : Ideal C := I.map (algebraMap A C)
  let e : RingEquiv (C ⧸ L) (C ⧸ K) := Ideal.quotEquivOfEq hJK
  let qBC : B ⧸ J →+* C ⧸ L :=
    Ideal.quotientMap L (algebraMap B C) Ideal.le_comap_map
  let qAC : A ⧸ I →+* C ⧸ K :=
    Ideal.quotientMap K (algebraMap A C) Ideal.le_comap_map
  have hcomp : qAC = e.toRingHom.comp (qBC.comp qAB) := by
    ext x
    show Ideal.Quotient.mk K (algebraMap A C x) =
      e (Ideal.Quotient.mk L (algebraMap B C (algebraMap A B x)))
    rw [IsScalarTower.algebraMap_apply A B C, Ideal.quotEquivOfEq_mk]
  have hmk : e.toRingHom.comp (Ideal.Quotient.mk L) = Ideal.Quotient.mk K := by
    ext x
    exact Ideal.quotEquivOfEq_mk hJK x
  have hbarK (P : Polynomial (B ⧸ J)) (Q : Polynomial C)
      (hPQ : P.map qBC = Q.map (Ideal.Quotient.mk L)) :
      P.map (e.toRingHom.comp qBC) = Q.map (Ideal.Quotient.mk K) := by
    calc
      _ = (P.map qBC).map e.toRingHom := by rw [Polynomial.map_map]
      _ = (Q.map (Ideal.Quotient.mk L)).map e.toRingHom :=
        congrArg (Polynomial.map e.toRingHom) hPQ
      _ = Q.map (Ideal.Quotient.mk K) := by rw [Polynomial.map_map, hmk]
  have hg₀barK := hbarK G g₀ hg₀bar
  have hh₀barK := hbarK H h₀ hh₀bar
  have hvimage : e.toRingHom.comp qBC vb = Ideal.Quotient.mk K (algebraMap B C v) := by
    show e (Ideal.Quotient.mk L (algebraMap B C v)) = Ideal.Quotient.mk K (algebraMap B C v)
    exact DFunLike.congr_fun hmk (algebraMap B C v)
  refine ⟨C, instC, inferInstance, g', h', ?_, ?_, ?_, ?_, ?_⟩
  · let := hetAB
    let := hetBC
    exact Algebra.Etale.comp A B C
  · show Function.Bijective qAC
    rw [hcomp]
    exact e.bijective.comp (hqBC.comp hqAB)
  · rw [IsScalarTower.algebraMap_eq A B C, ← Polynomial.map_map, hfac₀]
    show g₀ * h₀ = Polynomial.C (algebraMap B C v) * g₀ * (Polynomial.C winv * h₀)
    rw [mul_mul_mul_comm, ← Polynomial.C_mul,
      show algebraMap B C v * winv = 1 from (hv.map (algebraMap B C)).unit.mul_inv,
      Polynomial.C_1, one_mul]
  · let r : B ⧸ J →+* C ⧸ K := e.toRingHom.comp qBC
    have huv : r vinv * r vb = 1 := by
      rw [← map_mul]
      show r (↑(hv.map (Ideal.Quotient.mk J)).unit⁻¹ *
        ↑(hv.map (Ideal.Quotient.mk J)).unit) = 1
      simpa only [map_one] using
        congrArg r (hv.map (Ideal.Quotient.mk J)).unit.inv_mul
    show gbar.map qAC = g'.map (Ideal.Quotient.mk K)
    rw [hcomp, ← Polynomial.map_map, ← Polynomial.map_map]
    simp only [g', Polynomial.map_mul, Polynomial.map_C]
    rw [← hg₀barK]
    simp only [G, Polynomial.map_mul, Polynomial.map_C]
    rw [Polynomial.map_map]
    dsimp only [r] at huv
    have huv' : (e.toRingHom.comp qBC) vb * (e.toRingHom.comp qBC) vinv = 1 := by
      simpa only [mul_comm] using huv
    show (gbar.map qAB).map (e.toRingHom.comp qBC) =
      Polynomial.C (Ideal.Quotient.mk K (algebraMap B C v)) *
        (Polynomial.C ((e.toRingHom.comp qBC) vinv) *
          (gbar.map qAB).map (e.toRingHom.comp qBC))
    rw [← mul_assoc, ← Polynomial.C_mul, ← hvimage, huv',
      Polynomial.C_1, one_mul]
  · let r : B ⧸ J →+* C ⧸ K := e.toRingHom.comp qBC
    have huv : Ideal.Quotient.mk K winv * r vb = 1 := by
      rw [hvimage, ← map_mul]
      show Ideal.Quotient.mk K (↑(hv.map (algebraMap B C)).unit⁻¹ *
        ↑(hv.map (algebraMap B C)).unit) = 1
      simpa only [map_one] using congrArg (Ideal.Quotient.mk K)
        (hv.map (algebraMap B C)).unit.inv_mul
    show hbar.map qAC = h'.map (Ideal.Quotient.mk K)
    rw [hcomp, ← Polynomial.map_map, ← Polynomial.map_map]
    simp only [h', Polynomial.map_mul, Polynomial.map_C]
    rw [← hh₀barK]
    simp only [H, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map]
    rw [RingHom.comp_assoc]
    dsimp only [r] at huv
    show hbar.map ((e.toRingHom.comp qBC).comp qAB) =
      Polynomial.C (Ideal.Quotient.mk K winv) *
        (Polynomial.C ((e.toRingHom.comp qBC) vb) *
          hbar.map ((e.toRingHom.comp qBC).comp qAB))
    rw [← mul_assoc, ← Polynomial.C_mul, huv, Polynomial.C_1, one_mul]

/-! ### The leading-coefficient hypothesis cannot be dropped -/

section Counterexample

private theorem quotientMap_pow_bijective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (hf : RingHom.FormallyEtale f)
    (h : Function.Bijective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map)) (n : ℕ) :
    Function.Bijective (Ideal.quotientMap ((I.map f) ^ n) f
      (show I ^ n ≤ Ideal.comap f ((I.map f) ^ n) from
        (Ideal.map_le_iff_le_comap).mp (by rw [Ideal.map_pow]))) := by
  have hI : FormallyEtaleH1D.Iideal f (I.map f) = I := by
    ext x
    show (Ideal.Quotient.mk (I.map f)) (f x) = 0 ↔ x ∈ I
    rw [← Ideal.quotientMap_mk (H := Ideal.le_comap_map),
      map_eq_zero_iff _ h.1, Ideal.Quotient.eq_zero_iff_mem]
  have hs : Function.Surjective ((Ideal.Quotient.mk (I.map f)).comp f) := by
    rw [← Ideal.quotientMap_comp_mk Ideal.le_comap_map]
    exact h.2.comp Ideal.Quotient.mk_surjective
  cases n with
  | zero =>
    have : Subsingleton (R ⧸ I ^ 0) := by rw [pow_zero, Ideal.one_eq_top]; infer_instance
    have : Subsingleton (S ⧸ (I.map f) ^ 0) := by rw [pow_zero, Ideal.one_eq_top]; infer_instance
    exact ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩
  | succ n =>
    have hh := FormallyEtaleH1D.quotMap_bijective f (I.map f) hf hs (n + 1) (by omega)
    let e := Ideal.quotEquivOfEq (congrArg (fun K : Ideal R => K ^ (n + 1)) hI.symm)
    have hb := hh.comp e.bijective
    convert hb using 1
    ext x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [e, FormallyEtaleH1D.quotMap]

private theorem nonempty_adicCompletion_equiv_padicInt {R : Type*} [CommRing R]
    (I : Ideal R) (p : ℕ) [Fact p.Prime]
    (e : ∀ n : ℕ, ZMod (p ^ n) ≃+* R ⧸ I ^ n) :
    Nonempty (AdicCompletion I R ≃+* ℤ_[p]) := by
  let t := fun {m n : ℕ} (h : m ≤ n) =>
    ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))
  have he {m n : ℕ} (h : m ≤ n) :
      (Ideal.Quotient.factorPow I h).comp (e n : _ →+* _) =
        (e m : _ →+* _).comp (t h) := Subsingleton.elim _ _
  let f : (n : ℕ) → AdicCompletion I R →+* ZMod (p ^ n) := fun n =>
    ((e n).symm : _ →+* _).comp (AdicCompletion.evalₐ I n).toRingHom
  have hf : ∀ m n (h : m ≤ n), (t h).comp (f n) = f m := by
    intro m n h
    ext x
    apply (e m).injective
    have hc := RingHom.congr_fun (he h) ((e n).symm (AdicCompletion.evalₐ I n x))
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] at hc
    simpa [f] using hc.symm.trans (AdicCompletion.factorPow_evalₐ I h x)
  let F : AdicCompletion I R →+* ℤ_[p] := PadicInt.lift hf
  let g : (n : ℕ) → ℤ_[p] →+* R ⧸ I ^ n := fun n => (e n : _ →+* _).comp (PadicInt.toZModPow n)
  have hg : ∀ {m n} (h : m ≤ n), (Ideal.Quotient.factorPow I h).comp (g n) = g m := by
    intro m n h
    dsimp [g]
    rw [← RingHom.comp_assoc, he h, RingHom.comp_assoc,
      PadicInt.zmod_cast_comp_toZModPow _ _ h]
  let G : ℤ_[p] →+* AdicCompletion I R := AdicCompletion.liftRingHom I g hg
  have hF (n : ℕ) (x : AdicCompletion I R) :
      PadicInt.toZModPow n (F x) = (e n).symm (AdicCompletion.evalₐ I n x) :=
    RingHom.congr_fun (PadicInt.lift_spec hf n) x
  have hG (n : ℕ) (x : ℤ_[p]) :
      AdicCompletion.evalₐ I n (G x) = e n (PadicInt.toZModPow n x) :=
    AdicCompletion.evalₐ_liftRingHom I g hg n x
  refine ⟨{ F with invFun := G, left_inv := ?_, right_inv := ?_ }⟩
  · intro x
    show G (F x) = x
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [hG, hF, RingEquiv.apply_symm_apply]
  · intro x
    show F (G x) = x
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    rw [hF, hG, RingEquiv.symm_apply_apply]

private theorem nonempty_adicCompletion_equiv_padicInt_of_formallyEtale
    {R : Type*} [CommRing R] [Algebra ℤ R] (p : ℕ) [Fact p.Prime]
    (hf : Algebra.FormallyEtale ℤ R)
    (h : Function.Bijective (Ideal.quotientMap
      ((Ideal.span {(p : ℤ)}).map (algebraMap ℤ R)) (algebraMap ℤ R)
      Ideal.le_comap_map)) :
    Nonempty (AdicCompletion (Ideal.span {(p : R)}) R ≃+* ℤ_[p]) := by
  let I : Ideal ℤ := Ideal.span {(p : ℤ)}
  let J : Ideal R := I.map (algebraMap ℤ R)
  have hJ : J = Ideal.span {(p : R)} := by simp [J, I, Ideal.map_span]
  rw [← hJ]
  apply nonempty_adicCompletion_equiv_padicInt J p
  intro n
  have hpow : I ^ n = Ideal.span {((p ^ n : ℕ) : ℤ)} := by
    simp [I, Ideal.span_singleton_pow]
  let a : ZMod (p ^ n) ≃+* ℤ ⧸ I ^ n :=
    (Int.quotientSpanNatEquivZMod (p ^ n)).symm.trans (Ideal.quotEquivOfEq hpow.symm)
  exact a.trans (RingEquiv.ofBijective _ (quotientMap_pow_bijective (algebraMap ℤ R) I
    (RingHom.formallyEtale_algebraMap.mpr hf) h n))

private theorem nonempty_twoAdicCompletion_equiv {R : Type*} [CommRing R] [Algebra ℤ R]
    (hf : Algebra.Etale ℤ R)
    (h : Function.Bijective (Ideal.quotientMap
      ((Ideal.span {(4 : ℤ)}).map (algebraMap ℤ R)) (algebraMap ℤ R)
      Ideal.le_comap_map)) :
    Nonempty (AdicCompletion (Ideal.span {(algebraMap ℤ R 2)}) R ≃+* ℤ_[2]) := by
  rw [map_ofNat]
  exact nonempty_adicCompletion_equiv_padicInt_of_formallyEtale 2 inferInstance
    (Ideal.quotientMap_bijective_of_le (algebraMap ℤ R)
      (Ideal.span_singleton_le_span_singleton.mpr (by norm_num)) h)

private theorem not_isUnit_of_coeff_two_sub_two_mem (g : Polynomial ℤ_[2])
    (hg : g.coeff 2 - 2 ∈ Ideal.span {(4 : ℤ_[2])}) : ¬ IsUnit g := by
  intro hu
  obtain ⟨r, hr, rfl⟩ := Polynomial.isUnit_iff.mp hu
  have hz : -(2 : ℤ_[2]) ∈ Ideal.span {(4 : ℤ_[2])} := by simpa using hg
  have hm : Ideal.span {(4 : ℤ_[2])} = RingHom.ker (PadicInt.toZModPow (p := 2) 2) := by
    rw [PadicInt.ker_toZModPow]
    norm_num
  rw [hm, RingHom.mem_ker] at hz
  norm_num only [map_neg, map_ofNat, neg_eq_zero] at hz
  exact (by decide : (2 : ZMod (2 ^ 2)) ≠ 0) hz

private theorem coeff_two_quadratic {R : Type*} [Semiring R] :
    (2 * Polynomial.X ^ 2 + 2 * Polynomial.X + 1 : Polynomial R).coeff 2 = 2 := by
  simp [Polynomial.coeff_X, Polynomial.coeff_one]

private theorem not_isUnit_of_congr_mod_four (g : Polynomial ℤ_[2])
    (hg : ∀ n : ℕ, g.coeff n -
        (2 * Polynomial.X ^ 2 + 2 * Polynomial.X + 1 : Polynomial ℤ_[2]).coeff n ∈
        Ideal.span {(4 : ℤ_[2])}) : ¬ IsUnit g :=
  not_isUnit_of_coeff_two_sub_two_mem g (by simpa only [coeff_two_quadratic] using hg 2)

private theorem not_isUnit_of_map_eq_quadratic {R : Type*} [CommRing R]
    (f : R →+* ℤ_[2]) (g : Polynomial R)
    (hg : g.map (Ideal.Quotient.mk (Ideal.span {(4 : R)})) =
      (2 * Polynomial.X ^ 2 + 2 * Polynomial.X + 1)) : ¬ IsUnit g := by
  intro hu
  apply not_isUnit_of_coeff_two_sub_two_mem (g.map f) _ (hu.map (Polynomial.mapRingHom f))
  have hc := congrArg (fun p => Polynomial.coeff p 2) hg
  rw [Polynomial.coeff_map, coeff_two_quadratic] at hc
  have hm : g.coeff 2 - 2 ∈ Ideal.span {(4 : R)} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa [map_ofNat] using sub_eq_zero.mpr hc
  simpa [Ideal.map_span, map_ofNat] using Ideal.mem_map_of_mem f hm

private theorem quadratic_mod_four_properties :
    let I : Ideal ℤ := Ideal.span {(4 : ℤ)}
    let p : Polynomial (ℤ ⧸ I) := 2 * Polynomial.X ^ 2 + 2 * Polynomial.X + 1
    (1 : Polynomial ℤ).Monic ∧
    (1 : Polynomial ℤ).map (Ideal.Quotient.mk I) = p * p ∧
    IsCoprime p p ∧
    ¬ IsUnit p.leadingCoeff := by
  dsimp only
  let p : Polynomial (ℤ ⧸ Ideal.span {(4 : ℤ)}) :=
    2 * Polynomial.X ^ 2 + 2 * Polynomial.X + 1
  have h4 : (4 : ℤ ⧸ Ideal.span {(4 : ℤ)}) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self 4)
  have h4p : (4 : Polynomial (ℤ ⧸ Ideal.span {(4 : ℤ)})) = 0 := by
    show Polynomial.C 4 = 0
    rw [h4, Polynomial.C_0]
  have hsq : p * p = 1 :=
    calc
      p * p = 1 + 4 * (Polynomial.X ^ 4 + 2 * Polynomial.X ^ 3 +
        2 * Polynomial.X ^ 2 + Polynomial.X) := by
        dsimp [p]
        ring
      _ = 1 := by rw [h4p, zero_mul, add_zero]
  refine ⟨Polynomial.monic_one, ?_, ?_, ?_⟩
  · simpa only [Polynomial.map_one] using hsq.symm
  · rw [isCoprime_self]
    exact isUnit_iff_exists_inv.mpr ⟨p, hsq⟩
  · have h2 : (2 : ℤ ⧸ Ideal.span {(4 : ℤ)}) ≠ 0 := by
      show ¬ Ideal.Quotient.mk (Ideal.span {(4 : ℤ)}) 2 = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      norm_num
    have hd : p.natDegree = 2 := by
      dsimp [p]
      compute_degree <;> simp [h2]
    show ¬ IsUnit p.leadingCoeff
    rw [Polynomial.leadingCoeff, hd, coeff_two_quadratic]
    intro hu
    have hm := hu.map (Int.quotientSpanNatEquivZMod 4).toRingHom
    rw [map_ofNat] at hm
    exact (by decide : ¬ IsUnit (2 : ZMod 4)) hm

/-- **Stacks 07M2.** The monic polynomial `1` factors modulo `4` as `(2X² + 2X + 1)²`, with
coprime factors but non-invertible leading coefficient. Nevertheless there is no étale extension
of `ℤ`, unchanged modulo `4`, carrying a factorization together with the two canonical reduction
equalities asserted in Stacks 07M1. The two completion-theoretic facts giving the obstruction are
recorded as well. -/
@[stacks 07M2]
theorem counterexample_to_etale_lift_without_isUnit_leadingCoeff :
    let I : Ideal ℤ := Ideal.span {(4 : ℤ)}
    let p : Polynomial (ℤ ⧸ I) := 2 * Polynomial.X ^ 2 + 2 * Polynomial.X + 1
    (1 : Polynomial ℤ).Monic ∧
    (1 : Polynomial ℤ).map (Ideal.Quotient.mk I) = p * p ∧
    IsCoprime p p ∧
    ¬ IsUnit p.leadingCoeff ∧
    (∀ (A' : Type v) (_ : CommRing A') (_ : Algebra ℤ A'),
      Algebra.Etale ℤ A' →
      Function.Bijective
        (Ideal.quotientMap
          (I.map (algebraMap ℤ A'))
          (algebraMap ℤ A') Ideal.le_comap_map) →
      Nonempty
        (AdicCompletion (Ideal.span {(algebraMap ℤ A' 2)}) A' ≃+* ℤ_[2])) ∧
    (∀ g' : Polynomial ℤ_[2],
      (∀ n : ℕ,
        g'.coeff n -
            (2 * Polynomial.X ^ 2 + 2 * Polynomial.X + 1 : Polynomial ℤ_[2]).coeff n ∈
          Ideal.span {(4 : ℤ_[2])}) →
      ¬ IsUnit g') ∧
    ¬ ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra ℤ A')
        (g' h' : Polynomial A'),
      Algebra.Etale ℤ A' ∧
      Function.Bijective
        (Ideal.quotientMap (I.map (algebraMap ℤ A')) (algebraMap ℤ A')
          Ideal.le_comap_map) ∧
      (1 : Polynomial ℤ).map (algebraMap ℤ A') = g' * h' ∧
      p.map
          (Ideal.quotientMap (I.map (algebraMap ℤ A')) (algebraMap ℤ A')
            Ideal.le_comap_map) =
        g'.map (Ideal.Quotient.mk (I.map (algebraMap ℤ A'))) ∧
      p.map
          (Ideal.quotientMap (I.map (algebraMap ℤ A')) (algebraMap ℤ A')
            Ideal.le_comap_map) =
        h'.map (Ideal.Quotient.mk (I.map (algebraMap ℤ A'))) := by
  dsimp only
  obtain ⟨hmonic, hfactor, hcoprime, hlead⟩ := quadratic_mod_four_properties
  refine ⟨hmonic, hfactor, hcoprime, hlead,
    fun _ _ _ het hbij => nonempty_twoAdicCompletion_equiv het hbij,
    not_isUnit_of_congr_mod_four, ?_⟩
  rintro ⟨R, _, _, g, h, het, hbij, hfactor, hg, _⟩
  obtain ⟨e⟩ := nonempty_twoAdicCompletion_equiv het hbij
  have hJ : (Ideal.span {(4 : ℤ)}).map (algebraMap ℤ R) = Ideal.span {(4 : R)} := by
    simp [Ideal.map_span]
  have hg' : g.map (Ideal.Quotient.mk (Ideal.span {(4 : R)})) =
      2 * Polynomial.X ^ 2 + 2 * Polynomial.X + 1 := by
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_one, Polynomial.map_ofNat] at hg
    rw [hJ] at hg
    exact hg.symm
  exact not_isUnit_of_map_eq_quadratic (e.toRingHom.comp (algebraMap R _)) g hg'
    (isUnit_iff_exists_inv.mpr ⟨h, by simpa only [Polynomial.map_one] using hfactor.symm⟩)

end Counterexample
