module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Formally étale maps and the associated graded ring

All rings are commutative with unit and all ring maps are unital.

A ring map `φ : R → S` is *formally étale* if for every commutative solid diagram of ring maps
```
  S  --->  A/I
  ^         ^
  |         |
  R  --->   A
```
in which `A` is a ring, `I` is a square-zero ideal of `A`, the right vertical map is the
canonical quotient and the square commutes, there is a *unique* ring map `S → A` making both
triangles commute. In Lean this is `RingHom.FormallyEtale φ`.

Fix a ring map `φ : R → S` and an ideal `J` of `S` such that the composite `R → S → S/J` is
surjective, and put `I = ker(R → S/J)`. Then `R/I → S/J` is an isomorphism. For each `n` one
has `φ(Iⁿ) ⊆ Jⁿ`, so `φ` induces canonical ring maps `φ̄ₙ : R/Iⁿ → S/Jⁿ`, compatible with the
quotient maps as `n` varies. Passing to associated graded pieces, `φ` induces a homomorphism of
graded rings `gr(φ) : ⊕ₙ Iⁿ/Iⁿ⁺¹ → ⊕ₙ Jⁿ/Jⁿ⁺¹`, with the convention `I⁰ = R`, `J⁰ = S`.

## Main definitions

* `FormallyEtaleH1D.Iideal`: the ideal `I = ker(R → S/J)`.
* `FormallyEtaleH1D.quotMap`: the ring map `φ̄ₙ : R/Iⁿ → S/Jⁿ` induced by `φ`.
* `FormallyEtaleH1D.grMap`: the degree-`n` component `Iⁿ/Iⁿ⁺¹ → Jⁿ/Jⁿ⁺¹` of `gr(φ)`.

## Main results

Assume `R → S` is formally étale. Then

* `FormallyEtaleH1D.quotMap_bijective`: for every `n ≥ 1` the canonical map `φ̄ₙ : R/Iⁿ → S/Jⁿ` is
  an isomorphism;
* `FormallyEtaleH1D.grMap_bijective`: the induced map of associated graded rings is an
  isomorphism.

## Implementation notes

The degree-`n` piece `Iⁿ/Iⁿ⁺¹` is realized as the ideal `(Iⁿ).map (Quotient.mk (Iⁿ⁺¹))` of
`R/Iⁿ⁺¹`, and likewise on the `S` side; the degree-`n` component `grMap n : Iⁿ/Iⁿ⁺¹ → Jⁿ/Jⁿ⁺¹` is
the restriction of `φ̄ₙ₊₁`. A homomorphism of graded rings is an isomorphism if and only if it is
bijective in every degree, so `grMap_bijective` states that `grMap n` is bijective for every `n`.
The degree-`0` component is `φ̄₁ : R/I → S/J`.

## References

* [Stacks Project, Tag 0H1D](https://stacks.math.columbia.edu/tag/0H1D)
-/

@[expose] public section

namespace FormallyEtaleH1D

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
variable (J : Ideal S)

/-- `I = ker(R → S/J)`, the kernel of the composite `R → S → S/J`. -/
@[ega "IV 16.1.1" "special case", sga "7 VI 5.8" "special case"]
noncomputable def Iideal : Ideal R := RingHom.ker ((Ideal.Quotient.mk J).comp φ)

/-- `φ(I) ⊆ J`, i.e. `I ≤ comap φ J`. -/
theorem Iideal_le_comap : Iideal φ J ≤ Ideal.comap φ J := by
  intro x hx
  simp only [Iideal, RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at hx
  exact hx

/-- For each `n`, `φ(I^n) ⊆ J^n`, i.e. `I^n ≤ comap φ (J^n)`. -/
@[ega "IV 16.2.1" "special case"]
theorem Iideal_pow_le_comap_pow (n : ℕ) : (Iideal φ J) ^ n ≤ Ideal.comap φ (J ^ n) :=
  le_trans (Ideal.pow_right_mono (Iideal_le_comap φ J) n) (Ideal.le_comap_pow φ n)

/-- The canonical ring map `φ̄ₙ : R/I^n → S/J^n` induced by `φ`. -/
@[ega "IV 16.2.1" "special case"]
noncomputable def quotMap (n : ℕ) : R ⧸ (Iideal φ J) ^ n →+* S ⧸ (J ^ n) :=
  Ideal.quotientMap (J ^ n) φ (Iideal_pow_le_comap_pow φ J n)

/-- The degree-`n` graded piece of the source, namely `I^n/I^{n+1}`, realized as
the ideal `(I^n).map (Quotient.mk (I^{n+1}))` of `R/I^{n+1}`. -/
@[ega "0 10.1.1" "partial",
  ega "IV 16.1.2" "special case",
  ega "IV 16.3.1" "special case",
  ega "IV 16.3.7",
  ega "IV 6.10.1" "special case", sga "1 II 4.14" "partial", sga "1 III 6.9", sga "6 VII 1.2"]
noncomputable def grSrc (n : ℕ) : Ideal (R ⧸ (Iideal φ J) ^ (n + 1)) :=
  Ideal.map (Ideal.Quotient.mk ((Iideal φ J) ^ (n + 1))) ((Iideal φ J) ^ n)

/-- The degree-`n` graded piece of the target, namely `J^n/J^{n+1}`, realized as
the ideal `(J^n).map (Quotient.mk (J^{n+1}))` of `S/J^{n+1}`. -/
@[ega "0 10.1.1" "partial",
  ega "IV 16.3.1" "special case",
  ega "IV 16.3.7",
  ega "IV 6.10.1" "special case", sga "1 II 4.14" "partial", sga "1 III 6.9", sga "6 VII 1.2"]
noncomputable def grTgt (n : ℕ) : Ideal (S ⧸ J ^ (n + 1)) :=
  Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) (J ^ n)

/-- The ring map `φ̄ₙ₊₁` carries the degree-`n` source piece into the degree-`n` target
piece. -/
theorem grMap_image_le (n : ℕ) :
    Ideal.map (quotMap φ J (n + 1)) (grSrc φ J n) ≤ grTgt J n := by
  rw [grSrc, grTgt, Ideal.map_map, Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap]
  simp only [RingHom.coe_comp, Function.comp_apply]
  have hx' : (quotMap φ J (n + 1)) (Ideal.Quotient.mk ((Iideal φ J) ^ (n + 1)) x)
      = Ideal.Quotient.mk (J ^ (n + 1)) (φ x) := by
    rw [quotMap, Ideal.quotientMap_mk]
  rw [hx']
  exact Ideal.mem_map_of_mem _ (Iideal_pow_le_comap_pow φ J n hx)

/-- The degree-`n` component `gr(φ)_n : I^n/I^{n+1} → J^n/J^{n+1}` of the induced map of
associated graded rings `gr(φ)`, the restriction of the canonical ring map
`φ̄ₙ₊₁ : R/I^{n+1} → S/J^{n+1}`. -/
@[ega "IV 16.2.1" "special case", ega "IV 16.2.6" "Affine, special case"]
noncomputable def grMap (n : ℕ) : grSrc φ J n → grTgt J n :=
  fun x => ⟨quotMap φ J (n + 1) x.val,
    grMap_image_le φ J n (Ideal.mem_map_of_mem _ x.property)⟩

/-- If `R → S/J` is surjective, then `φ̄₁ : R/I → S/J` is bijective. -/
@[ega "IV 16.1.1" "special case"]
theorem quotMap_one_bijective
    (hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp φ)) :
    Function.Bijective (quotMap φ J 1) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [quotMap, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem, pow_one] at ha
    rwa [Ideal.Quotient.eq_zero_iff_mem, pow_one, Iideal, RingHom.mem_ker, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem]
  · intro b
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨r, hr⟩ := hsurj s
    rw [RingHom.comp_apply] at hr
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    rw [quotMap, Ideal.quotientMap_mk]
    change Ideal.Quotient.mk (J ^ 1) (φ r) = Ideal.Quotient.mk (J ^ 1) s
    rw [pow_one, hr]

/-- If `φ` is formally étale and `φ̄ₙ : R/I^n → S/J^n` is bijective for some `n ≥ 1`, then so
is `φ̄ₙ₊₁ : R/I^{n+1} → S/J^{n+1}`. -/
theorem quotMap_succ_bijective
    (hφ : RingHom.FormallyEtale φ)
    (n : ℕ) (hn : 1 ≤ n)
    (ih : Function.Bijective (quotMap φ J n)) :
    Function.Bijective (quotMap φ J (n + 1)) := by
  let := φ.toAlgebra
  have hfe : Algebra.FormallyEtale R S := hφ
  obtain ⟨hur, hsm⟩ := Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mp hfe
  set I := Iideal φ J with hI
  set Bmk1 := Ideal.Quotient.mk (I ^ (n+1)) with hBmk1
  let φbarₐ : (m : ℕ) → (R ⧸ I^m) →ₐ[R] (S ⧸ J^m) := fun m =>
    Ideal.quotientMapₐ (J^m) (Algebra.ofId R S) (Iideal_pow_le_comap_pow φ J m)
  have hbij_n : Function.Bijective (φbarₐ n) := ih
  let e_n : (R ⧸ I^n) ≃ₐ[R] (S ⧸ J^n) := AlgEquiv.ofBijective (φbarₐ n) hbij_n
  set K : Ideal (R ⧸ I^(n+1)) := Ideal.map Bmk1 (I^n) with hK
  have hKnil : IsNilpotent K := by
    refine ⟨2, ?_⟩
    rw [hK, ← Ideal.map_pow, show (0 : Ideal (R ⧸ I^(n+1))) = ⊥ from rfl,
      Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    calc (I ^ n) ^ 2 = I ^ (n * 2) := by rw [← pow_mul]
      _ ≤ I ^ (n + 1) := Ideal.pow_le_pow_right (by omega)
  have hle_pow : I^(n+1) ≤ I^n := Ideal.pow_le_pow_right (by omega)
  have hdcomm : ∀ (x : R), (DoubleQuot.quotQuotEquivQuotOfLE hle_pow) (algebraMap R _ x)
      = algebraMap R (R ⧸ I^n) x := by
    intro x
    change (DoubleQuot.quotQuotEquivQuotOfLE hle_pow) (DoubleQuot.quotQuotMk (I^(n+1)) (I^n) x)
      = Ideal.Quotient.mk (I^n) x
    rw [DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk]
  let d : ((R ⧸ I^(n+1)) ⧸ K) ≃ₐ[R] (R ⧸ I^n) := AlgEquiv.ofRingEquiv hdcomm
  let mkJn : (S) →ₐ[R] (S ⧸ J^n) := Ideal.Quotient.mkₐ R (J^n)
  let g : S →ₐ[R] ((R ⧸ I^(n+1)) ⧸ K) :=
    (d.symm.toAlgHom).comp ((e_n.symm.toAlgHom).comp mkJn)
  let psit : S →ₐ[R] (R ⧸ I^(n+1)) := Algebra.FormallySmooth.lift K hKnil g
  have hcomp_lift : (Ideal.Quotient.mkₐ R K).comp psit = g :=
    Algebra.FormallySmooth.comp_lift K hKnil g
  let p : (R ⧸ I^(n+1)) →+* (R ⧸ I^n) := Ideal.Quotient.factor hle_pow
  have hpd : ∀ x : (R ⧸ I^(n+1)), p x = d (Ideal.Quotient.mk K x) := by
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.factor_mk]
    change _ = (DoubleQuot.quotQuotEquivQuotOfLE hle_pow) (DoubleQuot.quotQuotMk (I^(n+1)) (I^n) r)
    rw [DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk]
  have hp_psit : ∀ s : S, p (psit s) = e_n.symm (mkJn s) := by
    intro s
    rw [hpd]
    have : (Ideal.Quotient.mk K) (psit s) = g s := by
      have := AlgHom.congr_fun hcomp_lift s
      simpa using this
    rw [this]
    change d (g s) = e_n.symm (mkJn s)
    change d ((d.symm.toAlgHom).comp ((e_n.symm.toAlgHom).comp mkJn) s) = e_n.symm (mkJn s)
    simp
  have hkill : ∀ s ∈ J^(n+1), psit s = 0 := by
    have hJle : J ≤ (Ideal.map φ I) ⊔ J^n := by
      intro j hj
      obtain ⟨x, hx⟩ := ih.right (Ideal.Quotient.mk (J^n) j)
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [quotMap, Ideal.quotientMap_mk] at hx
      rw [Ideal.Quotient.eq] at hx
      have hφrJ : φ r ∈ J := by
        have h1 : φ r - j ∈ J := Ideal.pow_le_self (by omega) hx
        have := Ideal.add_mem J h1 hj
        simpa using this
      have hrI : r ∈ I := by
        simp only [hI, Iideal, RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
        exact hφrJ
      have hjeq : j = φ r - (φ r - j) := by ring
      rw [hjeq]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hrI)) (Ideal.mem_sup_right
          hx)
    set K1 : Ideal (R ⧸ I^(n+1)) := Ideal.map Bmk1 I with hK1
    have hpsitφ : psit.toRingHom.comp φ = Bmk1 := by
      apply RingHom.ext
      intro r
      change psit (φ r) = Bmk1 r
      have : psit (φ r) = psit (algebraMap R S r) := rfl
      rw [this, AlgHom.commutes]
      rfl
    have hmapφI : Ideal.map psit.toRingHom (Ideal.map φ I) = K1 := by
      rw [Ideal.map_map, hpsitφ]
    have hKK1 : K ≤ K1 := by
      rw [hK, hK1]
      exact Ideal.map_mono (Ideal.pow_le_self (by omega))
    have hmapJn : Ideal.map psit.toRingHom (J^n) ≤ K1 := by
      rw [Ideal.map_le_iff_le_comap]
      intro s hs
      rw [Ideal.mem_comap]
      apply hKK1
      rw [hK, ← Ideal.Quotient.factor_ker hle_pow, RingHom.mem_ker]
      change p (psit s) = 0
      rw [hp_psit]
      have : (mkJn s) = Ideal.Quotient.mk (J^n) s := rfl
      rw [this, (Ideal.Quotient.eq_zero_iff_mem).mpr hs]
      simp
    have hmapJ : Ideal.map psit.toRingHom J ≤ K1 := by
      apply le_trans (Ideal.map_mono hJle)
      rw [Ideal.map_sup, hmapφI]
      exact sup_le le_rfl hmapJn
    have hK1pow : K1^(n+1) = ⊥ := by
      rw [hK1, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, hBmk1, Ideal.mk_ker]
    intro s hs
    have : psit s ∈ Ideal.map psit.toRingHom (J^(n+1)) := Ideal.mem_map_of_mem _ hs
    rw [Ideal.map_pow] at this
    have hle2 : (Ideal.map psit.toRingHom J)^(n+1) ≤ K1^(n+1) := pow_le_pow_left' hmapJ _
    rw [hK1pow] at hle2
    have := hle2 this
    simpa using this
  let psi : (S ⧸ J^(n+1)) →+* (R ⧸ I^(n+1)) :=
    Ideal.Quotient.lift (J^(n+1)) psit.toRingHom (by intro a ha; exact hkill a ha)
  have hleft : psi.comp (quotMap φ J (n+1)) = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    ext r
    simp only [RingHom.comp_apply]
    change psi (quotMap φ J (n+1) (Ideal.Quotient.mk (I^(n+1)) r)) = Ideal.Quotient.mk (I^(n+1)) r
    rw [quotMap, Ideal.quotientMap_mk]
    change psi (Ideal.Quotient.mk (J^(n+1)) (φ r)) = _
    change Ideal.Quotient.lift (J^(n+1)) psit.toRingHom _ (Ideal.Quotient.mk (J^(n+1)) (φ r)) = _
    rw [Ideal.Quotient.lift_mk]
    change psit (φ r) = _
    have : psit (φ r) = psit (algebraMap R S r) := rfl
    rw [this, AlgHom.commutes]
    rfl
  have hright : (quotMap φ J (n+1)).comp psi = RingHom.id _ := by
    have hleJ : J^(n+1) ≤ J^n := Ideal.pow_le_pow_right (by omega)
    set Ktgt : Ideal (S ⧸ J^(n+1)) := Ideal.map (Ideal.Quotient.mk (J^(n+1))) (J^n) with hKtgt
    have hKtgt_nil : IsNilpotent Ktgt := by
      refine ⟨2, ?_⟩
      rw [hKtgt, ← Ideal.map_pow, show (0 : Ideal (S ⧸ J^(n+1))) = ⊥ from rfl,
        Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
      calc (J ^ n) ^ 2 = J ^ (n * 2) := by rw [← pow_mul]
        _ ≤ J ^ (n + 1) := Ideal.pow_le_pow_right (by omega)
    let pS : (S ⧸ J^(n+1)) →+* (S ⧸ J^n) := Ideal.Quotient.factor hleJ
    have hdtgt_comm : ∀ (x : S), (DoubleQuot.quotQuotEquivQuotOfLE hleJ) (algebraMap S _ x)
        = algebraMap S (S ⧸ J^n) x := by
      intro x
      change (DoubleQuot.quotQuotEquivQuotOfLE hleJ) (DoubleQuot.quotQuotMk (J^(n+1)) (J^n) x)
        = Ideal.Quotient.mk (J^n) x
      rw [DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk]
    let dtgt : ((S ⧸ J^(n+1)) ⧸ Ktgt) ≃ₐ[S] (S ⧸ J^n) := AlgEquiv.ofRingEquiv hdtgt_comm
    have hpSd : ∀ x : (S ⧸ J^(n+1)), pS x = dtgt (Ideal.Quotient.mk Ktgt x) := by
      intro x
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.Quotient.factor_mk]
      change _ = (DoubleQuot.quotQuotEquivQuotOfLE hleJ) (DoubleQuot.quotQuotMk (J^(n+1)) (J^n) s)
      rw [DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk]
    have hsq : ∀ x, pS (quotMap φ J (n+1) x) = quotMap φ J n (p x) := by
      intro x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      change pS (quotMap φ J (n+1) (Ideal.Quotient.mk (I^(n+1)) r)) = quotMap φ J n (p
          (Ideal.Quotient.mk (I^(n+1)) r))
      rw [quotMap, Ideal.quotientMap_mk]
      change pS (Ideal.Quotient.mk (J^(n+1)) (φ r)) = _
      rw [Ideal.Quotient.factor_mk]
      change _ = quotMap φ J n (Ideal.Quotient.factor hle_pow (Ideal.Quotient.mk (I^(n+1)) r))
      rw [Ideal.Quotient.factor_mk, quotMap, Ideal.quotientMap_mk]
    have hen_eq : ∀ x, e_n x = quotMap φ J n x := fun x => rfl
    have hkey : ∀ s : S, quotMap φ J (n+1) (psit s) = Ideal.Quotient.mk (J^(n+1)) s := by
      let g1 : S →ₐ[R] (S ⧸ J^(n+1)) := (φbarₐ (n+1)).comp psit
      let g2 : S →ₐ[R] (S ⧸ J^(n+1)) := Ideal.Quotient.mkₐ R (J^(n+1))
      have heq : g1 = g2 := by
        apply Algebra.FormallyUnramified.lift_unique Ktgt hKtgt_nil g1 g2
        apply AlgHom.ext
        intro s
        change (Ideal.Quotient.mk Ktgt) (g1 s) = (Ideal.Quotient.mk Ktgt) (g2 s)
        apply dtgt.injective
        rw [← hpSd, ← hpSd]
        change pS (quotMap φ J (n+1) (psit s)) = pS (Ideal.Quotient.mk (J^(n+1)) s)
        rw [hsq, Ideal.Quotient.factor_mk, hp_psit, ← hen_eq, AlgEquiv.apply_symm_apply]
        rfl
      exact fun s => AlgHom.congr_fun heq s
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro s
    simp only [RingHom.comp_apply, RingHom.id_apply]
    change quotMap φ J (n+1) (psi (Ideal.Quotient.mk (J^(n+1)) s)) = Ideal.Quotient.mk (J^(n+1)) s
    change quotMap φ J (n+1) (Ideal.Quotient.lift (J^(n+1)) psit.toRingHom _ (Ideal.Quotient.mk
        (J^(n+1)) s)) = _
    rw [Ideal.Quotient.lift_mk]
    exact hkey s
  rw [Function.bijective_iff_has_inverse]
  refine ⟨psi, ?_, ?_⟩
  · exact fun x => RingHom.congr_fun hleft x
  · exact fun y => by simpa using RingHom.congr_fun hright y

/-- If `φ : R → S` is formally étale and `R → S/J` is surjective, with `I = ker(R → S/J)`, then
for every `n ≥ 1` the canonical map `φ̄ₙ : R/I^n → S/J^n` is bijective. -/
@[stacks 0H1D "(1)"]
theorem quotMap_bijective
    (hφ : RingHom.FormallyEtale φ)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp φ))
    (n : ℕ) (hn : 1 ≤ n) :
    Function.Bijective (quotMap φ J n) := by
  induction n, hn using Nat.le_induction with
  | base => exact quotMap_one_bijective φ J hsurj
  | succ m hm ih => exact quotMap_succ_bijective φ J hφ m hm ih

/-- If `φ : R → S` is formally étale and `R → S/J` is surjective, with `I = ker(R → S/J)`, then
the induced map of associated graded rings `gr(φ) : ⊕_n I^n/I^{n+1} → ⊕_n J^n/J^{n+1}` is an
isomorphism: for every `n` its degree-`n` component `I^n/I^{n+1} → J^n/J^{n+1}` is bijective. -/
@[stacks 0H1D "(2)"]
theorem grMap_bijective
    (hφ : RingHom.FormallyEtale φ)
    (hsurj : Function.Surjective ((Ideal.Quotient.mk J).comp φ))
    (n : ℕ) :
    Function.Bijective (grMap φ J n) := by
  have hR : (Iideal φ J) ^ (n + 1) ≤ (Iideal φ J) ^ n := Ideal.pow_le_pow_right (by omega)
  have hS : J ^ (n + 1) ≤ J ^ n := Ideal.pow_le_pow_right (by omega)
  have hbij1 : Function.Bijective (quotMap φ J (n + 1)) :=
    quotMap_bijective φ J hφ hsurj (n + 1) (by omega)
  have hsquare : ∀ x : R ⧸ (Iideal φ J) ^ (n + 1),
      Ideal.Quotient.factor hS (quotMap φ J (n + 1) x)
        = quotMap φ J n (Ideal.Quotient.factor hR x) := by
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    unfold quotMap
    rw [Ideal.quotientMap_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk,
      Ideal.quotientMap_mk]
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply hbij1.left
    have : (grMap φ J n x).val = (grMap φ J n y).val := by rw [hxy]
    simpa [grMap] using this
  · intro y
    obtain ⟨x0, hx0⟩ := hbij1.right y.val
    have hx0mem : x0 ∈ grSrc φ J n := by
      rw [grSrc, ← Ideal.Quotient.factor_ker hR, RingHom.mem_ker]
      have hy : Ideal.Quotient.factor hS y.val = 0 := by
        have hmem : y.val ∈ Ideal.map (Ideal.Quotient.mk (J ^ (n + 1))) (J ^ n) := y.property
        rw [← Ideal.Quotient.factor_ker hS, RingHom.mem_ker] at hmem
        exact hmem
      have hzero : quotMap φ J n (Ideal.Quotient.factor hR x0) = 0 := by
        rw [← hsquare, hx0]; exact hy
      obtain rfl | hn := Nat.eq_zero_or_pos n
      · have : Subsingleton (R ⧸ (Iideal φ J) ^ 0) := by
          rw [pow_zero]
          exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
        exact Subsingleton.elim _ _
      · have hbij0 : Function.Bijective (quotMap φ J n) :=
          quotMap_bijective φ J hφ hsurj n hn
        have := hbij0.left (a₁ := Ideal.Quotient.factor hR x0) (a₂ := 0)
        rw [map_zero] at this
        exact this hzero
    refine ⟨⟨x0, hx0mem⟩, ?_⟩
    apply Subtype.ext
    simpa [grMap] using hx0

end FormallyEtaleH1D
