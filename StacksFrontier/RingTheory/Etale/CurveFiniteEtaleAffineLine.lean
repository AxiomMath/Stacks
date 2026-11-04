module

public import StacksFrontier.RingTheory.Etale.GenericFiniteEtale
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeOverField
public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Finite

/-!
# A curve is, away from finitely many points, finite étale over an open of the affine line

Let `A` be a domain of finite type and of Krull dimension one over a perfect field `k` (the ring
of functions of an affine integral curve). Then there are a nonzero `c ∈ A`, a `k`-algebra
embedding `φ : k[X] → A_c` and a nonzero `g ∈ k[X]` such that `(A_c)_{φ g}` is finite étale over
`k[X]_g`. Geometrically: removing the finitely many points `V(c ⋅ φ g)` of `Spec A`, the curve
becomes finite étale over the open `D(g)` of `𝔸¹_k`.

## Removing points cannot be avoided

The curve itself need not be finite étale over an open of `𝔸¹_k`: an étale `π : U → V` with `V`
open in `𝔸¹_k` gives `Ω_U = π^* Ω_V = O_U dt`, so `Ω_U` would be free. On the genus two curve
`X : y² = x⁵ + 1` over a finite field of odd characteristic, the rational point `P = (0, 1)` has
`y ≠ 0`, so it is not a Weierstrass point and `K_X` is not linearly equivalent to `2P`; for
`U = X - {P}` (smooth, affine, geometrically connected) `Pic U = Pic X / ℤP` and `K_X - mP` has
degree `2 - m`, so the class of `Ω_U = O(K_X)|_U` is not trivial. Hence the statement is made
after removing finitely many points, as in Deligne, Weil II 3.3 ("quitte à rétrécir X").

## Main results

* `Stacks.GenericFiniteEtale.exists_separating_away`: a separating transcendental element
  `a / b`.
* `Stacks.GenericFiniteEtale.exists_finite_etale_polynomial`: the finite étale map.
* `Stacks.GenericFiniteEtale.exists_finite_etale_away`: the same as a finite étale
  `k[X]_g → A_a` over `k`, with `D(a)` a basic open of `Spec A`.

## References

* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), 3.3.
-/

@[expose] public section

open Polynomial

namespace Stacks.GenericFiniteEtale

universe u

variable (k : Type u) [Field k] (A : Type u) [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

/-- **A separating transcendental element of a curve.** If `A` is a domain of finite type and of
Krull dimension one over a perfect field `k`, its fraction field is separable over `k(s₀)` for
a transcendental `s₀ = a / b` with `a, b ∈ A`, `b ≠ 0`. -/
theorem exists_separating_away [PerfectField k] (hA : ringKrullDim A = 1) :
    ∃ (a b : A), b ≠ 0 ∧ Transcendental k
        (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b) ∧
      Algebra.IsSeparable
        (IntermediateField.adjoin k
          {algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b})
        (FractionRing A) := by
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k
    (FractionRing A)
  have htr : Algebra.trdeg k (FractionRing A) = 1 := by
    have h := (ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg.{_, _, _, 0} k A
      (FractionRing A)).1
    rw [hA] at h
    exact Cardinal.toENat_eq_one.1 (by exact_mod_cast h.symm)
  have hcard : s.card = 1 := by
    have := hs.cardinalMk_eq_trdeg
    rw [htr, Cardinal.mk_coe_finset] at this
    exact_mod_cast this
  obtain ⟨s₀, rfl⟩ := Finset.card_eq_one.1 hcard
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := A) s₀
  refine ⟨a, b, nonZeroDivisors.ne_zero hb, ?_, ?_⟩
  · rw [hab]
    exact hs.1.transcendental ⟨s₀, Finset.mem_singleton_self s₀⟩
  · rwa [hab, ← Finset.coe_singleton]

/-- **A curve is, away from finitely many points, finite étale over an open of the affine
line.** If `A` is a domain of finite type and of Krull dimension one over a perfect field `k`,
there are a nonzero `c ∈ A`, an injective `k`-algebra map `φ : k[X] → A_c` and a nonzero
`g ∈ k[X]` such that, for the `k[X]`-algebra structure on `A_c` given by `φ`, the localization
`(A_c)_g = (A_c)_{φ g}` is finite and étale over `k[X]_g`. -/
theorem exists_finite_etale_polynomial [PerfectField k] (hA : ringKrullDim A = 1) :
    ∃ (c : A) (_ : c ≠ 0) (φ : k[X] →ₐ[k] Localization.Away c) (_ : Function.Injective φ)
      (g : k[X]) (_ : g ≠ 0),
      letI := φ.toRingHom.toAlgebra
      Module.Finite (Localization.Away g) (Loc (Localization.Away c) g) ∧
        Algebra.Etale (Localization.Away g) (Loc (Localization.Away c) g) := by
  obtain ⟨a, b, hb, htr, hsep⟩ := exists_separating_away k A hA
  set L := FractionRing A
  set s₀ : L := algebraMap A L a / algebraMap A L b with hs₀
  set B := Localization.Away b
  have : IsDomain B :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hb)
  have hbu : IsUnit (algebraMap A L b) :=
    (map_ne_zero_iff _ (IsFractionRing.injective A L)).2 hb |>.isUnit
  let ψ : B →+* L := IsLocalization.Away.lift b hbu
  have hψA : ψ.comp (algebraMap A B) = algebraMap A L := IsLocalization.Away.lift_comp b hbu
  let algBL : Algebra B L := ψ.toAlgebra
  have : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun x => (congrArg (· x) hψA).symm
  have : IsFractionRing B L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers b) B L
  set t : B := IsLocalization.mk' B a (⟨b, Submonoid.mem_powers b⟩ : Submonoid.powers b)
  have ht : ψ t = s₀ := by
    have h1 : t * algebraMap A B b = algebraMap A B a := IsLocalization.mk'_spec B a _
    have h2 := congrArg ψ h1
    rw [map_mul, show ψ (algebraMap A B b) = algebraMap A L b from congrArg (· b) hψA,
      show ψ (algebraMap A B a) = algebraMap A L a from congrArg (· a) hψA] at h2
    exact eq_div_of_mul_eq hbu.ne_zero h2
  have hψk : ψ.comp (algebraMap k B) = algebraMap k L := by
    rw [IsScalarTower.algebraMap_eq k A B, ← RingHom.comp_assoc, hψA,
      ← IsScalarTower.algebraMap_eq k A L]
  have hψaeval : ∀ p : k[X], ψ (aeval t p) = aeval s₀ p := fun p => by
    rw [aeval_def, aeval_def, Polynomial.hom_eval₂, hψk, ht]
  let φ : k[X] →ₐ[k] B := aeval t
  let ψk : B →ₐ[k] L := { ψ with commutes' := fun r => congrArg (· r) hψk }
  have hφinj : Function.Injective φ := by
    rw [← transcendental_iff_injective]
    exact fun h => htr (ht ▸ h.algHom ψk)
  refine ⟨b, hb, φ, hφinj, ?_⟩
  let : Algebra k[X] B := φ.toRingHom.toAlgebra
  have : IsScalarTower k k[X] B := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  have : FaithfulSMul k[X] B := (faithfulSMul_iff_algebraMap_injective _ _).2 hφinj
  have : Algebra.FiniteType k[X] B := Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  set K := IntermediateField.adjoin k {s₀}
  let s₁ : K := ⟨s₀, IntermediateField.mem_adjoin_simple_self k s₀⟩
  let : Algebra k[X] K := (aeval s₁).toRingHom.toAlgebra
  let : Algebra k[X] L := (aeval s₀).toRingHom.toAlgebra
  have : IsScalarTower k[X] K L := IsScalarTower.of_algebraMap_eq fun p => by
    change aeval s₀ p = K.val (aeval s₁ p)
    rw [← aeval_algHom_apply]
    rfl
  have : IsScalarTower k[X] B L := IsScalarTower.of_algebraMap_eq fun p => (hψaeval p).symm
  have hKinj : Function.Injective (algebraMap k[X] K) := by
    intro p q h
    have h' := congrArg K.val h
    change K.val (aeval s₁ p) = K.val (aeval s₁ q) at h'
    rw [← aeval_algHom_apply, ← aeval_algHom_apply] at h'
    exact (transcendental_iff_injective.1 htr) h'
  have : FaithfulSMul k[X] K := (faithfulSMul_iff_algebraMap_injective _ _).2 hKinj
  have : IsFractionRing k[X] K := IsFractionRing.of_field k[X] K fun z => by
    obtain ⟨r, q, hrq⟩ := (IntermediateField.mem_adjoin_simple_iff k (α := s₀) z.1).1 z.2
    refine ⟨r, q, Subtype.ext ?_⟩
    rw [hrq, IntermediateField.coe_div]
    change _ = K.val (aeval s₁ r) / K.val (aeval s₁ q)
    rw [← aeval_algHom_apply, ← aeval_algHom_apply]
    rfl
  have : Algebra.IsSeparable K L := hsep
  obtain ⟨g, hg, hfin, het⟩ := exists_finite_etale_localization (R := k[X]) (B := B) K L
  exact ⟨g, hg, hfin, het⟩

/-- **The finite étale map of a curve to the affine line on a basic open.** If `A` is a domain
of finite type and of Krull dimension one over a perfect field `k`, there are nonzero `a ∈ A` and
`g ∈ k[X]` and a finite étale ring map `ψ : k[X]_g → A_a` over `k`: the basic open `D(a)`, whose
complement in `Spec A` is finite, is finite étale over the open `D(g)` of `𝔸¹_k`. -/
theorem exists_finite_etale_away [PerfectField k] (hA : ringKrullDim A = 1) :
    ∃ (a : A) (_ : a ≠ 0) (g : k[X]) (_ : g ≠ 0)
      (ψ : Localization.Away g →+* Localization.Away a),
      ψ.Finite ∧ ψ.Etale ∧ ∀ x : k, ψ (algebraMap k (Localization.Away g) x) =
        algebraMap k (Localization.Away a) x := by
  obtain ⟨c, hc, φ, hφ, g, hg, H⟩ := exists_finite_etale_polynomial k A hA
  let : Algebra k[X] (Localization.Away c) := φ.toRingHom.toAlgebra
  obtain ⟨hfin, het⟩ := H
  set P := Loc (Localization.Away c) g
  obtain ⟨⟨d, ⟨_, ⟨m, rfl⟩⟩⟩, hd⟩ := IsLocalization.mk'_surjective (Submonoid.powers c) (φ g)
  dsimp only at hd
  have hφg : φ g ≠ 0 := fun h => hg (hφ (h.trans (map_zero φ).symm))
  have hassoc : Associated (algebraMap A (Localization.Away c) d) (φ g) := by
    rw [← hd, IsLocalization.mk'_eq_mul_mk'_one]
    exact associated_mul_unit_right _ _ (IsUnit.of_mul_eq_one _
      ((IsLocalization.mk'_spec (Localization.Away c) 1 _).trans (map_one _)))
  have hPaway : IsLocalization.Away (φ g) P := by
    have hpow : Algebra.algebraMapSubmonoid (Localization.Away c) (Submonoid.powers g) =
        Submonoid.powers (φ g) := Submonoid.map_powers _ _
    change IsLocalization (Submonoid.powers (φ g)) P
    rw [← hpow]; infer_instance
  have hA : IsLocalization.Away (c * d) P :=
    IsLocalization.Away.mul_of_associated c d (φ g) hassoc
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hφg (hassoc.eq_zero_iff.1 (map_zero _))
  set e : P ≃ₐ[A] Localization.Away (c * d) :=
    IsLocalization.algEquiv (Submonoid.powers (c * d)) P (Localization.Away (c * d))
  refine ⟨c * d, mul_ne_zero hc hd0, g, hg,
    e.toRingEquiv.toRingHom.comp (algebraMap (Localization.Away g) P), ?_, ?_, ?_⟩
  · exact RingHom.Finite.comp (RingHom.Finite.of_surjective _ e.surjective)
      (RingHom.finite_algebraMap.2 hfin)
  · exact RingHom.Etale.stableUnderComposition _ _ ((RingHom.etale_algebraMap).2 het)
      (RingHom.Etale.of_bijective e.bijective)
  · intro x
    change e (algebraMap (Localization.Away g) P (algebraMap k (Localization.Away g) x)) = _
    rw [IsScalarTower.algebraMap_apply k k[X] (Localization.Away g),
      ← IsScalarTower.algebraMap_apply k[X] (Localization.Away g) P,
      IsScalarTower.algebraMap_apply k[X] (Localization.Away c) P]
    change e (algebraMap _ P (φ (algebraMap k k[X] x))) = _
    rw [φ.commutes, IsScalarTower.algebraMap_apply k A (Localization.Away c),
      ← IsScalarTower.algebraMap_apply A (Localization.Away c) P, e.commutes,
      ← IsScalarTower.algebraMap_apply]

end Stacks.GenericFiniteEtale
