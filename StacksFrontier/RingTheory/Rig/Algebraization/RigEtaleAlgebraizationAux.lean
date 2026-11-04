module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import StacksFrontier.RingTheory.AdicCompletion.Algebraization
public import StacksFrontier.RingTheory.Rig.RigEtaleLocus

/-!
# Commutative algebra for the induction of Stacks 0AKA

Two facts used when the algebraizations of the quotients `B ⧸ aᵐ B` are assembled in the proof
of Stacks 0AKA.

* `Rig.exists_adicCompletion_algEquiv_away`: inverting an element `g ∈ 1 + J` does not change
  the `J`-adic completion.  The source uses this silently when it replaces an algebraization
  `C` by the localization `C_g` of Stacks 0ALQ.
* `Rig.flat_away_of_isEtaleOutside`: if `D` is of finite type over a Noetherian ring `R` and
  étale over `Spec R ∖ V(J)`, then for `x ∈ J` the localization at `x` of (any ring isomorphic
  to) the `J`-adic completion of `D` is flat over `R`.  This is the flatness input of the
  square-zero lifting step of Stacks 0AKA.

## References

* [Stacks Project, Tag 0AKA](https://stacks.math.columbia.edu/tag/0AKA)
* [Stacks Project, Tag 0ALQ](https://stacks.math.columbia.edu/tag/0ALQ)
-/

@[expose] public noncomputable section

namespace Rig

universe u v w

section Away

variable {R : Type u} [CommRing R] (J : Ideal R) {g : R}

/-- If `g ≡ 1` modulo `J`, then every power of `g` is `≡ 1` modulo `J`. -/
public theorem pow_sub_one_mem_of_sub_one_mem (hg : g - 1 ∈ J) (k : ℕ) : g ^ k - 1 ∈ J := by
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow g 1 k
  rw [one_pow] at hc
  rw [hc]
  exact J.mul_mem_right c hg

/-- If `g ≡ 1` modulo `J`, then `R ⧸ J → R_g ⧸ J R_g` is bijective. -/
public theorem bijective_quotientMap_away (hg : g - 1 ∈ J) :
    Function.Bijective (Ideal.quotientMap (J.map (algebraMap R (Localization.Away g)))
      (algebraMap R (Localization.Away g)) Ideal.le_comap_map) := by
  let L := Localization.Away g
  have hpow : ∀ k : ℕ, g ^ k - 1 ∈ J := pow_sub_one_mem_of_sub_one_mem J hg
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    obtain ⟨⟨⟨j, hj⟩, ⟨_, k, rfl⟩⟩, hjk⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers g) L).mp hx
    rw [← map_mul] at hjk
    obtain ⟨⟨_, l, rfl⟩, hl⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers g) L).mp hjk
    dsimp only at hl
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have hmem : g ^ l * g ^ k * r ∈ J := by
      have : g ^ l * (r * g ^ k) ∈ J := hl ▸ J.mul_mem_left _ hj
      rwa [mul_comm r, ← mul_assoc] at this
    rw [← pow_add] at hmem
    have hsub : (g ^ (l + k) - 1) * r ∈ J := J.mul_mem_right r (hpow _)
    have := J.sub_mem hmem hsub
    rwa [sub_mul, one_mul, sub_sub_cancel] at this
  · intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨⟨r, _, k, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) z
    refine ⟨Ideal.Quotient.mk J r, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
    have hspec := IsLocalization.mk'_spec L r (⟨g ^ k, k, rfl⟩ : Submonoid.powers g)
    have heq : algebraMap R L r - IsLocalization.mk' L r (⟨g ^ k, k, rfl⟩ : Submonoid.powers g) =
        IsLocalization.mk' L r (⟨g ^ k, k, rfl⟩ : Submonoid.powers g) *
          algebraMap R L (g ^ k - 1) := by
      rw [map_sub, map_one, mul_sub, mul_one, ← hspec]
    rw [heq]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hpow k))

/-- **Inverting `g ∈ 1 + J` does not change the `J`-adic completion.**  The localization map
`R → R_g` is flat and bijective modulo `J`, hence identifies the completions. -/
public theorem exists_adicCompletion_algEquiv_away (hg : g - 1 ∈ J) :
    ∃ E : AdicCompletion J R ≃ₐ[R]
        AdicCompletion (J.map (algebraMap R (Localization.Away g))) (Localization.Away g),
      ∀ r : R, E (algebraMap R (AdicCompletion J R) r) =
        algebraMap (Localization.Away g)
          (AdicCompletion (J.map (algebraMap R (Localization.Away g))) (Localization.Away g))
          (algebraMap R (Localization.Away g) r) := by
  have : Module.Flat R (Localization.Away g) :=
    IsLocalization.flat (Localization.Away g) (Submonoid.powers g)
  exact exists_adicCompletionAlgEquiv_of_flat J (bijective_quotientMap_away J hg)

end Away

section Flat

/-- Let `D` be a Noetherian `R`-algebra and `H` an `R`-algebra isomorphic to the `J`-adic
completion of `D`.  If the localization `D_x` is flat over `R`, so is `H_x`: it is the base change
of the flat `D`-module `H` along `D → D_x`. -/
public theorem flat_away_of_flat_away_of_algEquiv {R : Type u} [CommRing R] {J : Ideal R}
    {D : Type v} [CommRing D] [Algebra R D] [IsNoetherianRing D] {H : Type w} [CommRing H]
    [Algebra R H] (e : AdicCompletion (J.map (algebraMap R D)) D ≃ₐ[R] H) {x : R}
    (hx : Module.Flat R (Localization.Away (algebraMap R D x))) :
    Module.Flat R (Localization.Away (algebraMap R H x)) := by
  let Dh := AdicCompletion (J.map (algebraMap R D)) D
  let : Algebra D H := (e.toRingHom.comp (algebraMap D Dh)).toAlgebra
  have hDH : ∀ d : D, algebraMap D H d = e (algebraMap D Dh d) := fun _ => rfl
  have : IsScalarTower R D H := IsScalarTower.of_algebraMap_eq fun r => by
    rw [hDH, ← IsScalarTower.algebraMap_apply R D Dh, e.commutes]
  let e' : Dh ≃ₐ[D] H := AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun _ => rfl
  have : Module.Flat D H := Module.Flat.of_linearEquiv e'.symm.toLinearEquiv
  let L := Localization (Algebra.algebraMapSubmonoid H (Submonoid.powers (algebraMap R D x)))
  have : Module.Flat (Localization.Away (algebraMap R D x)) L := inferInstance
  have : IsScalarTower R (Localization.Away (algebraMap R D x)) L :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply R D (Localization.Away (algebraMap R D x)),
        ← IsScalarTower.algebraMap_apply D (Localization.Away (algebraMap R D x)) L,
        IsScalarTower.algebraMap_apply D H L, ← IsScalarTower.algebraMap_apply R D H,
        ← IsScalarTower.algebraMap_apply R H L]
  have : Module.Flat R L := Module.Flat.trans R (Localization.Away (algebraMap R D x)) L
  have hM : Algebra.algebraMapSubmonoid H (Submonoid.powers (algebraMap R D x)) =
      Submonoid.powers (algebraMap R H x) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers,
      ← IsScalarTower.algebraMap_apply]
  have key : ∀ M : Submonoid H, M = Submonoid.powers (algebraMap R H x) →
      Module.Flat R (Localization M) →
        Module.Flat R (Localization.Away (algebraMap R H x)) := by
    rintro M rfl h
    exact h
  exact key _ hM this

/-- **Flatness of the localized completions.**  Let `R` be a Noetherian ring, `J ⊆ R` an ideal and
`D` a finite type `R`-algebra which is étale over `Spec R ∖ V(J)`.  If `H` is `R`-isomorphic to
the `J`-adic completion of `D`, then for every `x ∈ J` the localization `H_x` is flat over `R`:
`D_x` is étale, hence flat, over `R`, and `H_x` is the base change of the flat `D`-module `H`
along `D → D_x`. -/
public theorem flat_away_of_isEtaleOutside {R : Type u} [CommRing R] [IsNoetherianRing R]
    {J : Ideal R} {D : Type v} [CommRing D] [Algebra R D] [Algebra.FiniteType R D]
    (hD : IsEtaleOutside J D) {H : Type w} [CommRing H] [Algebra R H]
    (e : AdicCompletion (J.map (algebraMap R D)) D ≃ₐ[R] H) {x : R} (hx : x ∈ J) :
    Module.Flat R (Localization.Away (algebraMap R H x)) := by
  have : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing R D
  have : Algebra.FinitePresentation R D :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hEt : Algebra.Etale R (Localization.Away (algebraMap R D x)) := by
    refine Algebra.basicOpen_subset_etaleLocus_iff_etale.mp fun p hp => hD ?_
    rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hp
    simp only [Set.mem_preimage, Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus,
      PrimeSpectrum.comap_asIdeal, SetLike.coe_subset_coe]
    exact fun hle => hp (Ideal.mem_comap.mp (hle hx))
  exact flat_away_of_flat_away_of_algEquiv e inferInstance

end Flat

end Rig

end
