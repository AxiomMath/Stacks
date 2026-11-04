module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.FieldTheory.KaehlerDifferential.CartierEquality
public import StacksFrontier.RingTheory.Artinian.FiniteType
public import StacksFrontier.RingTheory.Kaehler.BaseChange
public import StacksFrontier.RingTheory.Kaehler.Basic
public import StacksFrontier.RingTheory.Kaehler.Defs
public import StacksFrontier.RingTheory.KrullDimension.Defs
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeOverField
public import StacksFrontier.RingTheory.Support.FiniteDimensional
public import StacksFrontier.RingTheory.TranscendenceDegree.ResidueField

/-!
# Finite-dimensionality of the derivations of a finite type algebra (Stacks 0DY4)

Let `k` be a field and `P` a `k`-algebra of finite type. The `k`-derivations of `P` into
itself form a finite-dimensional `k`-vector space exactly when `P` has Krull dimension at
most zero.

If `dim P ≤ 0` then `P` is a finite-dimensional `k`-algebra, and a derivation is in
particular a `k`-linear endomorphism of `P`, so `Derivation k P P` embeds into the
finite-dimensional space `P →ₗ[k] P`.

Conversely `Derivation k P P ≅ Hom_P(Ω[P⁄k], P)` is a finite `P`-module, so
finite-dimensionality over `k` forces its support to consist of finitely many closed points
of `Spec(P)`. A minimal prime `𝔮` that is not maximal would lie in that support: the residue
field of `𝔮` has positive transcendence degree over `k` by comparison with a maximal ideal
above it, so `Ω` of that residue field is nonzero by Cartier's equality, hence so is
`Ω[A⁄k]` for `A = P_𝔮`. That `A` is Artinian local, so a nonzero finite `A`-module admits a
nonzero `A`-linear functional, and localizing `Hom_P(Ω[P⁄k], P)` at `𝔮` is nonzero. So every
minimal prime is maximal, which is `dim P ≤ 0`.

Tag 0DY4(1) states this for the infinitesimal automorphisms `Inf(𝓓_P)` of the deformation
category of `P`; those are canonically `Derivation k P P` by Tag 0DY3, and the statement is
recorded here on the derivations themselves, where the mathematics lives and where no choice
of an object over the dual numbers is involved.

## Main results

* `Algebra.finiteDimensional_derivation_iff_ringKrullDim_le_zero`: **Stacks 0DY4(1)**, the
  stated equivalence.

## Implementation notes

The `k`- and `P`-module structures on `Derivation k P P` form a scalar tower, so the support
criterion `Module.finiteDimensional_iff_support_finite_subset_closedPoints` applies to the
canonical `k`-structure with no transport of instances.

Nonvanishing of a localization of `Hom_P(Ω[P⁄k], P)` is obtained from nonvanishing of
`Hom_A(Ω[A⁄k], A)` by the compatibility of `Hom` out of a finitely presented module with
localization, rather than by exhibiting an explicit element.

## References

* [Stacks Project, Tag 0DY4](https://stacks.math.columbia.edu/tag/0DY4)
-/

@[expose] public section

universe u v

namespace Algebra

/-- At a prime that is not maximal, the module of differentials of the residue field is
nonzero: passing to a maximal ideal above it strictly drops the transcendence degree of the
residue field, so that degree is positive, and Cartier's equality bounds it by the rank of
the module of differentials. -/
private theorem nontrivial_kaehlerDifferential_residueField_of_not_isMaximal
    (k : Type u) (P : Type v) [Field k] [CommRing P] [Algebra k P]
    [Algebra.FiniteType k P] (q : Ideal P) [q.IsPrime] (hq : ¬ q.IsMaximal) :
    Nontrivial Ω[q.ResidueField⁄k] := by
  obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal q (Ideal.IsPrime.ne_top ‹q.IsPrime›)
  have hlt : q < m := hqm.lt_of_ne fun e => hq (e ▸ hm)
  have : IsScalarTower k P q.ResidueField := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.EssFiniteType k q.ResidueField := Algebra.EssFiniteType.comp k P _
  have hqpos : 0 < Cardinal.toNat (Algebra.trdeg k q.ResidueField) :=
    Cardinal.toNat_pos.mpr ⟨ne_of_gt (pos_of_gt
      (Ideal.trdeg_residueField_lt_trdeg_residueField_of_lt k hlt)), trdeg_lt_aleph0 k _⟩
  have hcart := trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k q.ResidueField
  by_contra hΩ
  have : Subsingleton Ω[q.ResidueField⁄k] := not_nontrivial_iff_subsingleton.mp hΩ
  have : FiniteDimensional q.ResidueField Ω[q.ResidueField⁄k] := hcart.1
  have hzero : Module.finrank q.ResidueField Ω[q.ResidueField⁄k] = 0 :=
    Module.finrank_eq_zero_of_subsingleton q.ResidueField Ω[q.ResidueField⁄k]
  have hdim := hcart.2.2
  rw [hzero] at hdim
  omega

/-- An Artinian local ring embeds its residue field as a module: the maximal ideal is an
associated prime of the ring, so it is the annihilator of some element, and dividing by it
gives an injection. -/
private theorem exists_injective_residueField_toSelf
    (A : Type v) [CommRing A] [IsLocalRing A] [IsArtinianRing A] :
    ∃ i : (A ⧸ IsLocalRing.maximalIdeal A) →ₗ[A] A, Function.Injective i := by
  classical
  let m := IsLocalRing.maximalIdeal A
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty A A
  obtain ⟨hpPrime, y, hpy⟩ := isAssociatedPrime_iff.mp (AssociatedPrimes.mem_iff.mp hp)
  have : p.IsPrime := hpPrime
  have hpeq : p = m := IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime p)
  have hker : m = (LinearMap.toSpanSingleton A A y).ker := by
    rw [← hpeq, hpy]
    simp [SetLike.ext_iff]
  exact ⟨Submodule.liftQ m (LinearMap.toSpanSingleton A A y) hker.le,
    LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ hker.le hker.ge)⟩

/-- A nonzero finite module over a local ring has nonzero reduction modulo the maximal
ideal, by Nakayama. -/
private theorem nontrivial_quotient_maximalIdeal_smul
    (A : Type v) (M : Type*) [CommRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M] :
    Nontrivial (M ⧸ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)) := by
  rw [Submodule.Quotient.nontrivial_iff]
  have hmjac : IsLocalRing.maximalIdeal A ≤ (Module.annihilator A M).jacobson :=
    IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator A M)
  exact (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
    (I := IsLocalRing.maximalIdeal A) hmjac).symm

/-- A nonzero vector space over a field admits a linear functional not vanishing
everywhere. -/
private theorem exists_ne_zero_dual_apply (F V : Type*) [Field F] [AddCommGroup V]
    [Module F V] [Nontrivial V] : ∃ (g : V →ₗ[F] F) (x : V), g x ≠ 0 := by
  have : Nontrivial (Module.Dual F V) := (Module.nontrivial_dual_iff F).mpr inferInstance
  obtain ⟨g, hg⟩ := exists_ne (α := Module.Dual F V) 0
  exact ⟨g, DFunLike.ne_iff.mp hg⟩

/-- A nonzero finite module over a local ring admits a functional on its reduction modulo the
maximal ideal that does not vanish everywhere. -/
private theorem exists_ne_zero_dual_apply_quotient_maximalIdeal_smul
    (A : Type v) (M : Type*) [CommRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M] :
    ∃ (g : (M ⧸ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)) →ₗ[
        A ⧸ IsLocalRing.maximalIdeal A] (A ⧸ IsLocalRing.maximalIdeal A))
      (x : M ⧸ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)), g x ≠ 0 := by
  classical
  let m := IsLocalRing.maximalIdeal A
  let Q := M ⧸ m • (⊤ : Submodule A M)
  have : m.IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  let : Module (A ⧸ m) Q := Module.instQuotientIdealSubmoduleHSMulTop M m
  have : Nontrivial Q := nontrivial_quotient_maximalIdeal_smul A M
  exact exists_ne_zero_dual_apply (A ⧸ m) Q

/-- A nonzero finite module over an Artinian local ring admits a nonzero linear functional
to the ring: reduce modulo the maximal ideal, take a functional on the resulting nonzero
vector space over the residue field that does not vanish everywhere, and embed the residue
field back into the ring. -/
private theorem exists_ne_zero_linearMap_toSelf
    (A : Type v) (M : Type*) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M] :
    ∃ f : M →ₗ[A] A, f ≠ 0 := by
  let m := IsLocalRing.maximalIdeal A
  obtain ⟨g, x, hxg⟩ := exists_ne_zero_dual_apply_quotient_maximalIdeal_smul A M
  obtain ⟨i, hi⟩ := exists_injective_residueField_toSelf A
  let gA := g.restrictScalars A
  refine ⟨i.comp (gA.comp (m • (⊤ : Submodule A M)).mkQ), fun hf => ?_⟩
  obtain ⟨z, hz⟩ := Submodule.mkQ_surjective (m • (⊤ : Submodule A M)) x
  have hfx : i (g x) = 0 := by
    have h := LinearMap.congr_fun hf z
    change i (gA ((m • (⊤ : Submodule A M)).mkQ z)) = 0 at h
    rwa [hz] at h
  exact hxg (hi (by simpa using hfx))

/-- The localization of a Noetherian ring at a minimal prime is Artinian: its Krull dimension
is the height of that prime, which is zero. -/
@[sga "3 VIA 1.1.2" "partial"]
private theorem isArtinianRing_localization_atPrime_of_mem_minimalPrimes
    (P : Type v) [CommRing P] [IsNoetherianRing P] (q : Ideal P) [q.IsPrime]
    (hq : q ∈ minimalPrimes P) : IsArtinianRing (Localization.AtPrime q) := by
  have hdim : ringKrullDim (Localization.AtPrime q) = (0 : WithBot ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q]
    simpa only [WithBot.coe_zero] using
      congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) (Ideal.height_eq_zero_iff.mpr hq)
  have : Ring.KrullDimLE 0 (Localization.AtPrime q) := Ring.krullDimLE_iff.mpr hdim.le
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

/-- If two localization maps out of the same module are given, nontriviality of one target
transfers to the other. -/
private theorem nontrivial_of_isLocalizedModule {R M N N' : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup N'] [Module R M] [Module R N]
    [Module R N'] (S : Submonoid R) (f : M →ₗ[R] N) (g : M →ₗ[R] N')
    [IsLocalizedModule S f] [IsLocalizedModule S g] [Nontrivial N] : Nontrivial N' :=
  (IsLocalizedModule.linearEquiv S f g).injective.nontrivial

/-- A minimal prime of a finite type algebra over a field that is not maximal lies in the
support of the module of derivations. -/
private theorem mem_support_derivation_of_mem_minimalPrimes_of_not_isMaximal
    (k : Type u) (P : Type v) [Field k] [CommRing P] [Algebra k P]
    [Algebra.FiniteType k P] (q : Ideal P) [q.IsPrime]
    (hq : q ∈ minimalPrimes P) (hnmax : ¬ q.IsMaximal) :
    (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum P) ∈ Module.support P (Derivation k P P) := by
  classical
  have : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing k P
  let A := Localization.AtPrime q
  have : IsArtinianRing A := isArtinianRing_localization_atPrime_of_mem_minimalPrimes P q hq
  have : IsScalarTower k P A := IsScalarTower.of_algebraMap_eq' rfl
  have := nontrivial_kaehlerDifferential_residueField_of_not_isMaximal k P q hnmax
  have hAΩ : Nontrivial Ω[A⁄k] :=
    (KaehlerDifferential.map_surjective_of_surjective k k A q.ResidueField
      (IsLocalRing.residue_surjective (R := A))).nontrivial
  have : IsLocalizedModule q.primeCompl (KaehlerDifferential.map k k P A) :=
    KaehlerDifferential.isLocalizedModule_map k P A q.primeCompl
  have : Module.Finite A Ω[A⁄k] :=
    Module.Finite.of_isLocalizedModule q.primeCompl (KaehlerDifferential.map k k P A)
  obtain ⟨fA, hfA⟩ := exists_ne_zero_linearMap_toSelf A Ω[A⁄k]
  have : Nontrivial (Ω[A⁄k] →ₗ[A] A) :=
    (nontrivial_iff_exists_ne (0 : Ω[A⁄k] →ₗ[A] A)).mpr ⟨fA, hfA⟩
  have : Algebra.FinitePresentation k P := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Module.FinitePresentation P Ω[P⁄k] := Module.finitePresentation_of_finite P Ω[P⁄k]
  have hAlg : IsLocalizedModule q.primeCompl
      (IsScalarTower.toAlgHom P P A).toLinearMap := by
    rw [isLocalizedModule_iff_isLocalization]
    simpa using (inferInstance : IsLocalization q.primeCompl A)
  let S := q.primeCompl
  let mH := LocalizedModule.mkLinearMap S (Ω[P⁄k] →ₗ[P] P)
  let fD := LocalizedModule.mkLinearMap S (Derivation k P P)
  let e := KaehlerDifferential.linearMapEquivDerivation k P (M := P)
  have : IsLocalizedModule S (fD ∘ₗ e.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right S fD e
  have : IsLocalizedModule S (IsLocalizedModule.mapExtendScalars S (KaehlerDifferential.map k k P A)
      (IsScalarTower.toAlgHom P P A).toLinearMap A) :=
    Module.FinitePresentation.isLocalizedModule_mapExtendScalars S
      (KaehlerDifferential.map k k P A) (IsScalarTower.toAlgHom P P A).toLinearMap A
  have : Nontrivial (LocalizedModule S (Ω[P⁄k] →ₗ[P] P)) :=
    nontrivial_of_isLocalizedModule S (IsLocalizedModule.mapExtendScalars S
      (KaehlerDifferential.map k k P A) (IsScalarTower.toAlgHom P P A).toLinearMap A) mH
  have hDloc : Nontrivial (LocalizedModule S (Derivation k P P)) :=
    nontrivial_of_isLocalizedModule S mH (fD ∘ₗ e.toLinearMap)
  rwa [Module.mem_support_iff]

/-- Derivations of a finite-dimensional algebra over a field are finite-dimensional, being a
subspace of the linear endomorphisms. -/
private theorem finiteDimensional_derivation_of_finite
    (k : Type u) (P : Type v) [Field k] [CommRing P] [Algebra k P] [Module.Finite k P] :
    FiniteDimensional k (Derivation k P P) :=
  FiniteDimensional.of_injective
    ({ toFun := Derivation.toLinearMap, map_add' := fun _ _ => rfl,
        map_smul' := fun _ _ => rfl } : Derivation k P P →ₗ[k] (P →ₗ[k] P))
    fun _ _ h => Derivation.ext (LinearMap.congr_fun h)

/-- **Stacks 0DY4(1).** For a `k`-algebra `P` of finite type over a field, the `k`-derivations
of `P` into itself are a finite-dimensional `k`-vector space if and only if `P` has Krull
dimension at most zero. Through Tag 0DY3 this is the finite-dimensionality criterion for the
infinitesimal automorphisms of the deformation category of `P`. -/
@[stacks 0DY4 "part (1)"]
theorem finiteDimensional_derivation_iff_ringKrullDim_le_zero
    (k : Type u) (P : Type v) [Field k] [CommRing P] [Algebra k P]
    [Algebra.FiniteType k P] :
    FiniteDimensional k (Derivation k P P) ↔ ringKrullDim P ≤ 0 := by
  refine ⟨fun hD => ?_, fun hdim => ?_⟩
  · have : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing k P
    have : Algebra.FinitePresentation k P :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    have : Module.Finite P (Derivation k P P) :=
      Module.Finite.equiv (KaehlerDifferential.linearMapEquivDerivation k P (M := P))
    have hsupp := (Module.finiteDimensional_iff_support_finite_subset_closedPoints
      k P (Derivation k P P)).mp hD
    refine Ring.krullDimLE_iff.mp (Ring.KrullDimLE.mk₀ fun p hp => ?_)
    obtain ⟨q, hq, hqp⟩ :=
      Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal P)) (J := p) bot_le
    have : q.IsPrime := hq.1.1
    have hqmax : q.IsMaximal := Classical.byContradiction fun hnmax =>
      hnmax ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp
        (mem_closedPoints_iff.mp (hsupp.2
          (mem_support_derivation_of_mem_minimalPrimes_of_not_isMaximal k P q hq hnmax))))
    rwa [← hqmax.eq_of_le hp.ne_top hqp]
  · have : Module.Finite k P :=
      ((Algebra.FiniteType.krullDimLE_zero_tfae k P).out 1 5).mp (Ring.krullDimLE_iff.mpr hdim)
    exact finiteDimensional_derivation_of_finite k P

end Algebra

end
