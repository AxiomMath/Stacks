module

public import StacksFrontier.RingTheory.Etale.GenericFiniteEtaleFinitePresentation
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeOverField
public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Finite

/-!
# A variety is, away from a divisor, finite étale over an open of affine space

Let `A` be a domain of finite type and of Krull dimension `d` over a perfect field `k`. Then
there are a nonzero `b ∈ A`, an injective `k`-algebra map `φ : k[x₁, …, x_d] → A_b` and a
nonzero `g ∈ k[x₁, …, x_d]` such that `(A_b)_{φ g}` is finite étale over `k[x₁, …, x_d]_g`.
Equivalently (`Stacks.GenericFiniteEtale.exists_finite_etale_away_mvPolynomial`) there are
nonzero `a ∈ A`, `g ∈ k[x₁, …, x_d]` and a finite étale `k`-algebra map
`k[x₁, …, x_d]_g → A_a`. For `d = 1` this is
`Stacks.GenericFiniteEtale.exists_finite_etale_polynomial`.

## Main results

* `Stacks.GenericFiniteEtale.exists_finite_etale_mvPolynomial`: `(A_b)_{φ g}` is finite étale
  over `k[x₁, …, x_d]_g` for an injective `φ : k[x₁, …, x_d] → A_b`.
* `Stacks.GenericFiniteEtale.exists_finite_etale_away_mvPolynomial`: a finite étale `k`-algebra
  map `k[x₁, …, x_d]_g → A_a`.

## References

* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), 3.3.
-/

@[expose] public section

open MvPolynomial

namespace Stacks.GenericFiniteEtale

universe u

variable (k : Type u) [Field k] (A : Type u) [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

/-- **A variety is, away from a divisor, finite étale over an open of affine space.** If `A` is
a domain of finite type and of Krull dimension `d` over a perfect field `k`, there are a nonzero
`c ∈ A`, an injective `k`-algebra map `φ : k[x₁, …, x_d] → A_c` and a nonzero
`g ∈ k[x₁, …, x_d]` such that, for the `k[x₁, …, x_d]`-algebra structure on `A_c` given by `φ`,
the localization `(A_c)_g = (A_c)_{φ g}` is finite and étale over `k[x₁, …, x_d]_g`. -/
theorem exists_finite_etale_mvPolynomial [PerfectField k] (d : ℕ) (hA : ringKrullDim A = d) :
    ∃ (c : A) (_ : c ≠ 0) (φ : MvPolynomial (Fin d) k →ₐ[k] Localization.Away c)
      (_ : Function.Injective φ) (g : MvPolynomial (Fin d) k) (_ : g ≠ 0),
      letI := φ.toRingHom.toAlgebra
      Module.Finite (Localization.Away g) (Loc (Localization.Away c) g) ∧
        Algebra.Etale (Localization.Away g) (Loc (Localization.Away c) g) := by
  set L := FractionRing A
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k L
  have hcard : s.card = d := by
    have h := (ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg.{_, _, _, 0} k A L).1
    rw [hA, ← hs.cardinalMk_eq_trdeg, Cardinal.mk_coe_finset, Cardinal.toENat_nat] at h
    exact_mod_cast h.symm
  set e : Fin d ≃ s := (s.equivFinOfCardEq hcard).symm
  set x : Fin d → L := fun i ↦ (e i : L)
  have hx : AlgebraicIndependent k x := hs.1.comp _ e.injective
  have hrange : Set.range x = (s : Set L) := by
    rw [show x = ((↑) : s → L) ∘ e from rfl, e.surjective.range_comp, Subtype.range_coe_subtype,
      Finset.setOfPred_mem]
  set K := IntermediateField.adjoin k (Set.range x)
  have : Algebra.IsSeparable K L := by
    have hK : K = IntermediateField.adjoin k (s : Set L) := by
      change IntermediateField.adjoin k (Set.range x) = _
      rw [hrange]
    exact hK ▸ hsep
  obtain ⟨⟨b, hb⟩, hbx⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors A)
    (Finset.univ : Finset (Fin d)) x
  choose a ha using fun i ↦ hbx i (Finset.mem_univ i)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set B := Localization.Away b
  have : IsDomain B :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hb0)
  have hbu : IsUnit (algebraMap A L b) :=
    (map_ne_zero_iff _ (IsFractionRing.injective A L)).2 hb0 |>.isUnit
  let ψ : B →+* L := IsLocalization.Away.lift b hbu
  have hψA : ∀ a, ψ (algebraMap A B a) = algebraMap A L a := IsLocalization.Away.lift_eq b hbu
  let algBL : Algebra B L := ψ.toAlgebra
  have : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun x ↦ (hψA x).symm
  have : IsFractionRing B L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers b) B L
  set t : Fin d → B := fun i ↦
    IsLocalization.mk' B (a i) (⟨b, Submonoid.mem_powers b⟩ : Submonoid.powers b)
  have ht : ∀ i, ψ (t i) = x i := fun i ↦ by
    have h1 : t i * algebraMap A B b = algebraMap A B (a i) := IsLocalization.mk'_spec B (a i) _
    have h2 := congrArg ψ h1
    rw [map_mul, hψA, hψA, ha i, Algebra.smul_def, mul_comm] at h2
    exact mul_left_cancel₀ hbu.ne_zero h2
  have hψk : ∀ r, ψ (algebraMap k B r) = algebraMap k L r := fun r ↦ by
    rw [IsScalarTower.algebraMap_apply k A B, hψA, ← IsScalarTower.algebraMap_apply]
  let ψk : B →ₐ[k] L := { ψ with commutes' := hψk }
  let φ : MvPolynomial (Fin d) k →ₐ[k] B := aeval t
  have hψφ : ∀ p, ψ (φ p) = aeval x p := fun p ↦ by
    change ψk (aeval t p) = _
    rw [← AlgHom.comp_apply, comp_aeval]
    exact congrArg (aeval · p) (funext ht)
  have hφinj : Function.Injective φ := fun p q h ↦ by
    apply algebraicIndependent_iff_injective_aeval.1 hx
    change aeval x p = aeval x q
    rw [← hψφ, ← hψφ, h]
  refine ⟨b, hb0, φ, hφinj, ?_⟩
  set P := MvPolynomial (Fin d) k
  let : Algebra P B := φ.toRingHom.toAlgebra
  have : IsScalarTower k P B := IsScalarTower.of_algebraMap_eq fun x ↦ (φ.commutes x).symm
  have : FaithfulSMul P B := (faithfulSMul_iff_algebraMap_injective _ _).2 hφinj
  have : Algebra.FiniteType P B := Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  have : Algebra.FinitePresentation P B := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  let eK := hx.aevalEquivField
  let : Algebra P K := (eK.toRingHom.comp (algebraMap P (FractionRing P))).toAlgebra
  let eK' : FractionRing P ≃ₐ[P] K := AlgEquiv.ofRingEquiv (f := eK.toRingEquiv) fun _ ↦ rfl
  have : IsFractionRing P K := IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors P) eK'
  let : Algebra P L := (aeval x).toRingHom.toAlgebra
  have : IsScalarTower P K L := IsScalarTower.of_algebraMap_eq fun p ↦
    (hx.aevalEquivField_algebraMap_apply_coe p).symm
  have : IsScalarTower P B L := IsScalarTower.of_algebraMap_eq fun p ↦ (hψφ p).symm
  obtain ⟨g, hg, H⟩ := exists_finite_etale_localization_of_finitePresentation (R := P) (B := B) K L
  exact ⟨g, hg, H⟩

/-- **The finite étale map of a variety to affine space on a basic open.** If `A` is a domain of
finite type and of Krull dimension `d` over a perfect field `k`, there are nonzero `a ∈ A` and
`g ∈ k[x₁, …, x_d]` and a finite étale ring map `ψ : k[x₁, …, x_d]_g → A_a` over `k`: the basic
open `D(a)` of `Spec A` is finite étale over the open `D(g)` of `𝔸^d_k`. -/
theorem exists_finite_etale_away_mvPolynomial [PerfectField k] (d : ℕ) (hA : ringKrullDim A = d) :
    ∃ (a : A) (_ : a ≠ 0) (g : MvPolynomial (Fin d) k) (_ : g ≠ 0)
      (ψ : Localization.Away g →+* Localization.Away a),
      ψ.Finite ∧ ψ.Etale ∧ ∀ x : k, ψ (algebraMap k (Localization.Away g) x) =
        algebraMap k (Localization.Away a) x := by
  obtain ⟨c, hc, φ, hφ, g, hg, H⟩ := exists_finite_etale_mvPolynomial k A d hA
  let : Algebra (MvPolynomial (Fin d) k) (Localization.Away c) := φ.toRingHom.toAlgebra
  obtain ⟨hfin, het⟩ := H
  set P := Loc (Localization.Away c) g
  obtain ⟨⟨e, ⟨_, ⟨m, rfl⟩⟩⟩, he⟩ := IsLocalization.mk'_surjective (Submonoid.powers c) (φ g)
  dsimp only at he
  have hφg : φ g ≠ 0 := fun h ↦ hg (hφ (h.trans (map_zero φ).symm))
  have hassoc : Associated (algebraMap A (Localization.Away c) e) (φ g) := by
    rw [← he, IsLocalization.mk'_eq_mul_mk'_one]
    exact associated_mul_unit_right _ _ (IsUnit.of_mul_eq_one _
      ((IsLocalization.mk'_spec (Localization.Away c) 1 _).trans (map_one _)))
  have hPaway : IsLocalization.Away (φ g) P := by
    have hpow : Algebra.algebraMapSubmonoid (Localization.Away c) (Submonoid.powers g) =
        Submonoid.powers (φ g) := Submonoid.map_powers _ _
    change IsLocalization (Submonoid.powers (φ g)) P
    rw [← hpow]; infer_instance
  have hA : IsLocalization.Away (c * e) P :=
    IsLocalization.Away.mul_of_associated c e (φ g) hassoc
  have he0 : e ≠ 0 := by
    rintro rfl
    exact hφg (hassoc.eq_zero_iff.1 (map_zero _))
  set ε : P ≃ₐ[A] Localization.Away (c * e) :=
    IsLocalization.algEquiv (Submonoid.powers (c * e)) P (Localization.Away (c * e))
  refine ⟨c * e, mul_ne_zero hc he0, g, hg,
    ε.toRingEquiv.toRingHom.comp (algebraMap (Localization.Away g) P), ?_, ?_, ?_⟩
  · exact RingHom.Finite.comp (RingHom.Finite.of_surjective _ ε.surjective)
      (RingHom.finite_algebraMap.2 hfin)
  · exact RingHom.Etale.stableUnderComposition _ _ ((RingHom.etale_algebraMap).2 het)
      (RingHom.Etale.of_bijective ε.bijective)
  · intro x
    change ε (algebraMap (Localization.Away g) P (algebraMap k (Localization.Away g) x)) = _
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin d) k) (Localization.Away g),
      ← IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) k) (Localization.Away g) P,
      IsScalarTower.algebraMap_apply (MvPolynomial (Fin d) k) (Localization.Away c) P]
    change ε (algebraMap _ P (φ (algebraMap k (MvPolynomial (Fin d) k) x))) = _
    rw [φ.commutes, IsScalarTower.algebraMap_apply k A (Localization.Away c),
      ← IsScalarTower.algebraMap_apply A (Localization.Away c) P, ε.commutes,
      ← IsScalarTower.algebraMap_apply]

end Stacks.GenericFiniteEtale
