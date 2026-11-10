module

public import StacksFrontier.RingTheory.HomogeneousLocalization.AwayDegreeOneLaurent
public import StacksFrontier.RingTheory.Depth.Nakayama
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Localization.Integral

/-!
# The fibres of the punctured cone over a standard open

Let `S = ⨁_{d ≥ 0} S_d` be a graded ring, `f ∈ S_1`, and `𝔭` a prime of `S` with `f ∉ 𝔭`. The
local ring `T = S_𝔭` is a localization of `S_f = S₍f₎[f, f⁻¹]`; let `𝔮` be the prime of `S₍f₎`
under its maximal ideal. Geometrically `Spec S_f` is the punctured cone over the standard open
`D₊(f) = Spec S₍f₎`, `𝔭` is a point of it lying over the point `𝔮` of the base, and `T / 𝔮T` is
the local ring of `𝔭` in the fibre over `𝔮`, a localization of the Laurent polynomial ring
`κ(𝔮)[f, f⁻¹]`. Either `𝔭` is the generic point of that fibre, `𝔪_T = 𝔮T`, and then `f` is
transcendental over `κ(𝔮)` in `κ(𝔭)`; or it is a closed point, and then `T / 𝔮T` is a domain which
is not a field, so it has depth at least one. In either case

`trdeg κ(𝔮) + 1 ≤ depth_T(T / 𝔮T) + trdeg κ(𝔭)`

over any field `k` contained in `S₀`.

## Main definitions

* `Stacks.GradedLocalization.awayToAtPrime`: the localization map `S_f → S_𝔭`.
* `Stacks.GradedLocalization.awayDegreeZeroToAtPrime`: the map `S₍f₎ → S_𝔭`.

## Main results

* `Stacks.GradedLocalization.isPrime_map_awayDegreeZeroToAtPrime`: `𝔮T` is prime.
* `Stacks.GradedLocalization.toENat_trdeg_add_one_le`: the inequality above.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
-/

@[expose] public noncomputable section

open IsLocalRing HomogeneousLocalization Stacks.GradedLaurent

namespace Stacks.GradedLocalization

variable {S : Type*} {σ : Type*} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : S}

/-- The localization map `S_f → S_𝔭`, for a prime `𝔭` not containing `f`. -/
def awayToAtPrime (p : Ideal S) [p.IsPrime] (hp : f ∉ p) :
    Localization.Away f →+* Localization.AtPrime p :=
  IsLocalization.Away.lift f (IsLocalization.map_units (Localization.AtPrime p)
    (⟨f, hp⟩ : p.primeCompl))

/-- The map `S_f → S_𝔭` is compatible with the localization maps from `S`. -/
theorem awayToAtPrime_algebraMap (p : Ideal S) [p.IsPrime] (hp : f ∉ p) (x : S) :
    awayToAtPrime p hp (algebraMap S (Localization.Away f) x) =
      algebraMap S (Localization.AtPrime p) x :=
  IsLocalization.Away.lift_eq f _ x

/-- The map `S₍f₎ → S_𝔭`, for a prime `𝔭` not containing `f`. -/
def awayDegreeZeroToAtPrime (p : Ideal S) [p.IsPrime] (hp : f ∉ p) :
    Away 𝒜 f →+* Localization.AtPrime p :=
  (awayToAtPrime p hp).comp (algebraMap (Away 𝒜 f) (Localization.Away f))

/-- The map `S₍f₎ → S_𝔭` sends `a` to the image under `S_f → S_𝔭` of `a` regarded in `S_f`. -/
theorem awayDegreeZeroToAtPrime_apply (p : Ideal S) [p.IsPrime] (hp : f ∉ p) (a : Away 𝒜 f) :
    awayDegreeZeroToAtPrime 𝒜 p hp a = awayToAtPrime p hp a.val := rfl

section Fibre

variable (p : Ideal S) [p.IsPrime] (hp : f ∉ p)

/-- `S_𝔭` is a localization of `S_f`. -/
theorem isLocalization_awayToAtPrime :
    letI := (awayToAtPrime p hp).toAlgebra
    IsLocalization (p.primeCompl.map (algebraMap S (Localization.Away f)))
      (Localization.AtPrime p) := by
  let := (awayToAtPrime p hp).toAlgebra
  have : IsScalarTower S (Localization.Away f) (Localization.AtPrime p) :=
    IsScalarTower.of_algebraMap_eq fun x => (awayToAtPrime_algebraMap p hp x).symm
  have hle : Submonoid.powers f ≤ p.primeCompl :=
    (Submonoid.powers_le (P := p.primeCompl)).2 hp
  exact IsLocalization.isLocalization_of_submonoid_le (Localization.Away f)
    (Localization.AtPrime p) (Submonoid.powers f) p.primeCompl hle

/-- The extension to `S_f` of a prime `𝔮` of `S₍f₎` lying under the maximal ideal of `S_𝔭` is
disjoint from the complement of `𝔭`. -/
theorem disjoint_map_algebraMap_away (Q : Ideal (Away 𝒜 f))
    (hQ : Q ≤ (maximalIdeal (Localization.AtPrime p)).comap (awayDegreeZeroToAtPrime 𝒜 p hp)) :
    Disjoint (↑(p.primeCompl.map (algebraMap S (Localization.Away f))) :
        Set (Localization.Away f))
      ↑(Q.map (algebraMap (Away 𝒜 f) (Localization.Away f))) := by
  rw [Set.disjoint_left]
  rintro _ ⟨s, hs, rfl⟩ hsQ
  have h1 : Q.map (algebraMap (Away 𝒜 f) (Localization.Away f)) ≤
      (maximalIdeal (Localization.AtPrime p)).comap (awayToAtPrime p hp) := by
    rwa [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
  have h2 := h1 hsQ
  rw [Ideal.mem_comap, awayToAtPrime_algebraMap] at h2
  exact hs ((IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p s).1 h2)

/-- **The extension `𝔮 S_𝔭` of the prime `𝔮` of the base is prime**: `T / 𝔮T` is a localization of
the domain `κ(𝔮)[f, f⁻¹]`. -/
theorem isPrime_map_awayDegreeZeroToAtPrime (hf : f ∈ 𝒜 1) (Q : Ideal (Away 𝒜 f)) [Q.IsPrime]
    (hQ : Q ≤ (maximalIdeal (Localization.AtPrime p)).comap (awayDegreeZeroToAtPrime 𝒜 p hp)) :
    (Q.map (awayDegreeZeroToAtPrime 𝒜 p hp)).IsPrime := by
  let := (awayToAtPrime p hp).toAlgebra
  have := isLocalization_awayToAtPrime p hp
  have h := IsLocalization.isPrime_of_isPrime_disjoint
    (p.primeCompl.map (algebraMap S (Localization.Away f))) (Localization.AtPrime p) _
    (isPrime_map_algebraMap_away 𝒜 hf Q) (disjoint_map_algebraMap_away 𝒜 p hp Q hQ)
  rwa [Ideal.map_map] at h

/-- The extension `𝔮 S_𝔭` contracts to `𝔮 S_f` in `S_f`. -/
theorem comap_map_awayDegreeZeroToAtPrime (hf : f ∈ 𝒜 1) (Q : Ideal (Away 𝒜 f)) [Q.IsPrime]
    (hQ : Q ≤ (maximalIdeal (Localization.AtPrime p)).comap (awayDegreeZeroToAtPrime 𝒜 p hp)) :
    (Q.map (awayDegreeZeroToAtPrime 𝒜 p hp)).comap (awayToAtPrime p hp) =
      Q.map (algebraMap (Away 𝒜 f) (Localization.Away f)) := by
  let := (awayToAtPrime p hp).toAlgebra
  have := isLocalization_awayToAtPrime p hp
  have h := IsLocalization.under_map_of_isPrime_disjoint
    (p.primeCompl.map (algebraMap S (Localization.Away f))) (Localization.AtPrime p)
    (isPrime_map_algebraMap_away 𝒜 hf Q) (disjoint_map_algebraMap_away 𝒜 p hp Q hQ)
  rwa [Ideal.map_map] at h

/-- The value at `f` of a polynomial over `S₍f₎`, read in the basis of powers of `f`: its
coordinates are the coefficients. -/
theorem awayZpowBasis_repr_eval₂ (hf : f ∈ 𝒜 1) (P : Polynomial (Away 𝒜 f)) (n : ℕ) :
    (awayZpowBasis 𝒜 hf).repr
        (Polynomial.eval₂ (algebraMap (Away 𝒜 f) (Localization.Away f))
          (algebraMap S (Localization.Away f) f) P) n = P.coeff n := by
  classical
  have hpow : ∀ i : ℕ, (algebraMap S (Localization.Away f) f) ^ i =
      awayZpowBasis 𝒜 hf (i : ℤ) := fun i => by
    rw [awayZpowBasis_apply, coe_awayUnit_zpow_natCast, map_pow]
  rw [Polynomial.eval₂_eq_sum_range, map_sum, Finsupp.finsetSum_apply]
  have hterm : ∀ i ∈ Finset.range (P.natDegree + 1),
      (awayZpowBasis 𝒜 hf).repr (algebraMap (Away 𝒜 f) (Localization.Away f) (P.coeff i) *
        (algebraMap S (Localization.Away f) f) ^ i) (n : ℤ) = if i = n then P.coeff n else 0 :=
    fun i _ => by
      rw [hpow, ← Algebra.smul_def, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
        Finsupp.single_apply]
      by_cases hin : i = n
      · subst hin; simp
      · rw [ite_eq_right (fun h => hin (by exact_mod_cast h)), ite_eq_right hin, smul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  split_ifs with hn
  · rfl
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hn)]

/-- The prime of `S₍f₎` under the maximal ideal of `S_𝔭`: the point of the base under `𝔭`. -/
abbrev baseIdeal : Ideal (Away 𝒜 f) :=
  (maximalIdeal (Localization.AtPrime p)).comap (awayDegreeZeroToAtPrime 𝒜 p hp)

/-- The local homomorphism `S₍f₎_𝔮 → S_𝔭` from the local ring of the base at `𝔮`. -/
def baseLocalHom : Localization.AtPrime (baseIdeal 𝒜 p hp) →+* Localization.AtPrime p :=
  IsLocalization.lift (M := (baseIdeal 𝒜 p hp).primeCompl)
    (S := Localization.AtPrime (baseIdeal 𝒜 p hp)) (g := awayDegreeZeroToAtPrime 𝒜 p hp)
    fun y => (IsLocalRing.notMem_maximalIdeal).1 (by exact y.2)

/-- On the image of `S₍f₎`, the map `S₍f₎_𝔮 → S_𝔭` is the map `S₍f₎ → S_𝔭`. -/
theorem baseLocalHom_algebraMap (b : Away 𝒜 f) :
    baseLocalHom 𝒜 p hp (algebraMap _ _ b) = awayDegreeZeroToAtPrime 𝒜 p hp b :=
  IsLocalization.lift_eq _ b

/-- The map `S₍f₎_𝔮 → S_𝔭` is a local homomorphism. -/
instance isLocalHom_baseLocalHom : IsLocalHom (baseLocalHom 𝒜 p hp) := by
  refine ((IsLocalRing.local_hom_TFAE _).out 1 4).2 ?_
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (baseIdeal 𝒜 p hp)
    (Localization.AtPrime (baseIdeal 𝒜 p hp)), Ideal.map_le_iff_le_comap, Ideal.comap_comap]
  intro b hb
  rwa [Ideal.mem_comap, RingHom.comp_apply, baseLocalHom_algebraMap]

/-- The residue field extension `κ(𝔮) → κ(𝔭)` of the point `𝔭` of the cone over the point `𝔮` of
the base. -/
def baseResidueMap : (baseIdeal 𝒜 p hp).ResidueField →+* ResidueField (Localization.AtPrime p) :=
  IsLocalRing.ResidueField.map (baseLocalHom 𝒜 p hp)

/-- The map `κ(𝔮) → κ(𝔭)` sends the residue class of `b ∈ S₍f₎` to the residue class of its
image in `S_𝔭`. -/
theorem baseResidueMap_algebraMap (b : Away 𝒜 f) :
    baseResidueMap 𝒜 p hp (algebraMap (Away 𝒜 f) (baseIdeal 𝒜 p hp).ResidueField b) =
      residue (Localization.AtPrime p) (awayDegreeZeroToAtPrime 𝒜 p hp b) := by
  rw [IsScalarTower.algebraMap_apply (Away 𝒜 f) (Localization.AtPrime (baseIdeal 𝒜 p hp))]
  change IsLocalRing.ResidueField.map _ (residue _ _) = _
  rw [IsLocalRing.ResidueField.map_residue, baseLocalHom_algebraMap]

/-- **At the generic point of the fibre, `f` is transcendental over the residue field of the
base.** If the maximal ideal of `S_𝔭` is `𝔮 S_𝔭`, then the image of `f` in `κ(𝔭)` is
transcendental over `κ(𝔮)`. -/
theorem transcendental_residue_of_maximalIdeal_le (hf : f ∈ 𝒜 1)
    (hmax : maximalIdeal (Localization.AtPrime p) ≤
      (baseIdeal 𝒜 p hp).map (awayDegreeZeroToAtPrime 𝒜 p hp)) :
    letI := (baseResidueMap 𝒜 p hp).toAlgebra
    Transcendental (baseIdeal 𝒜 p hp).ResidueField
      (residue (Localization.AtPrime p) (algebraMap S (Localization.AtPrime p) f)) := by
  set Q := baseIdeal 𝒜 p hp
  set φ := awayDegreeZeroToAtPrime 𝒜 p hp
  set B := Away 𝒜 f
  set T := Localization.AtPrime p
  set ψ := baseResidueMap 𝒜 p hp
  let : Algebra Q.ResidueField (ResidueField T) := ψ.toAlgebra
  set D := B ⧸ Q
  let : Algebra D (ResidueField T) := (ψ.comp (algebraMap D Q.ResidueField)).toAlgebra
  have : IsScalarTower D Q.ResidueField (ResidueField T) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hDB : ∀ b : B, algebraMap D (ResidueField T) (Ideal.Quotient.mk Q b) =
      residue T (φ b) := fun b => by
    change ψ (algebraMap D Q.ResidueField (Ideal.Quotient.mk Q b)) = _
    have h := IsScalarTower.algebraMap_apply B D Q.ResidueField b
    rw [Ideal.Quotient.algebraMap_eq] at h
    rw [← h]
    exact baseResidueMap_algebraMap 𝒜 p hp b
  rw [transcendental_iff]
  intro P hP
  have h1 := IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors D) P hP
  obtain ⟨P2, hP2⟩ := Polynomial.map_surjective (Ideal.Quotient.mk Q)
    Ideal.Quotient.mk_surjective (IsLocalization.integerNormalization (nonZeroDivisors D) P)
  rw [← hP2, Polynomial.aeval_def, Polynomial.eval₂_map] at h1
  have hcomp : (algebraMap D (ResidueField T)).comp (Ideal.Quotient.mk Q) =
      (residue T).comp φ := RingHom.ext hDB
  rw [hcomp, ← Polynomial.hom_eval₂] at h1
  have hmem : Polynomial.eval₂ φ (algebraMap S T f) P2 ∈ Q.map φ :=
    hmax ((IsLocalRing.residue_eq_zero_iff _).1 h1)
  have hθ : Polynomial.eval₂ φ (algebraMap S T f) P2 = awayToAtPrime p hp
      (Polynomial.eval₂ (algebraMap B (Localization.Away f))
        (algebraMap S (Localization.Away f) f) P2) := by
    rw [Polynomial.hom_eval₂, awayToAtPrime_algebraMap]
    rfl
  have hQle : Q ≤ (maximalIdeal T).comap φ := le_refl _
  have hmemf : Polynomial.eval₂ (algebraMap B (Localization.Away f))
      (algebraMap S (Localization.Away f) f) P2 ∈
        Q.map (algebraMap B (Localization.Away f)) := by
    rwa [← comap_map_awayDegreeZeroToAtPrime 𝒜 p hp hf Q hQle, Ideal.mem_comap, ← hθ]
  have hcoeff : ∀ n, P2.coeff n ∈ Q := fun n => by
    rw [← awayZpowBasis_repr_eval₂ 𝒜 hf P2 n]
    exact awayZpowBasis_repr_mem_of_mem_map 𝒜 hf Q hmemf n
  have hzero : IsLocalization.integerNormalization (nonZeroDivisors D) P = 0 := by
    rw [← hP2]
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact hcoeff n
  exact (IsLocalization.integerNormalization_eq_zero_iff le_rfl P).1 hzero

/-- **The depth–transcendence inequality on a fibre of the punctured cone.** For `𝔭` a prime of
`S` not containing `f ∈ S_1`, lying over the prime `𝔮` of `S₍f₎`, and `k` a field over which
the maps `S₍f₎ → S_𝔭` are compatible,

`trdeg_k κ(𝔮) + 1 ≤ depth(S_𝔭 / 𝔮 S_𝔭) + trdeg_k κ(𝔭)`. -/
theorem toENat_trdeg_add_one_le (hf : f ∈ 𝒜 1) (k : Type*) [Field k] [Algebra k S]
    [Algebra k (Away 𝒜 f)]
    (hk : ∀ a : k, awayDegreeZeroToAtPrime 𝒜 p hp (algebraMap k (Away 𝒜 f) a) =
      algebraMap k (Localization.AtPrime p) a) :
    Cardinal.toENat (Algebra.trdeg k (baseIdeal 𝒜 p hp).ResidueField) + 1 ≤
      Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p ⧸ (baseIdeal 𝒜 p hp).map (awayDegreeZeroToAtPrime 𝒜 p hp) •
            (⊤ : Submodule (Localization.AtPrime p) (Localization.AtPrime p))) +
        Cardinal.toENat (Algebra.trdeg k p.ResidueField) := by
  set T := Localization.AtPrime p
  set Q := baseIdeal 𝒜 p hp
  set φ := awayDegreeZeroToAtPrime 𝒜 p hp
  set ψ := baseResidueMap 𝒜 p hp
  let : Algebra Q.ResidueField p.ResidueField := ψ.toAlgebra
  have : IsScalarTower k Q.ResidueField p.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change _ = ψ _
      rw [IsScalarTower.algebraMap_apply k (Away 𝒜 f) Q.ResidueField, baseResidueMap_algebraMap,
        hk, IsScalarTower.algebraMap_apply k T (ResidueField T),
        IsLocalRing.ResidueField.algebraMap_eq]
  have : FaithfulSMul k Q.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap k _).injective
  have : FaithfulSMul Q.ResidueField p.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 ψ.injective
  have htot := trdeg_add_eq k Q.ResidueField (A := p.ResidueField)
  have htotE : Cardinal.toENat (Algebra.trdeg k Q.ResidueField) +
      Cardinal.toENat (Algebra.trdeg Q.ResidueField p.ResidueField) =
        Cardinal.toENat (Algebra.trdeg k p.ResidueField) := by
    rw [← map_add, htot]
  by_cases hcase : maximalIdeal T ≤ Q.map φ
  · have htr := transcendental_residue_of_maximalIdeal_le 𝒜 p hp hf hcase
    have hind : AlgebraicIndependent Q.ResidueField
        (fun _ : PUnit => residue T (algebraMap S T f)) :=
      algebraicIndependent_unique_type_iff.2 htr
    have h1 : (1 : Cardinal) ≤ Algebra.trdeg Q.ResidueField p.ResidueField := by
      simpa using hind.cardinalMk_le_trdeg
    have h1E : (1 : ℕ∞) ≤ Cardinal.toENat (Algebra.trdeg Q.ResidueField p.ResidueField) := by
      simpa using Cardinal.toENat.monotone' h1
    calc Cardinal.toENat (Algebra.trdeg k Q.ResidueField) + 1
        ≤ Cardinal.toENat (Algebra.trdeg k Q.ResidueField) +
            Cardinal.toENat (Algebra.trdeg Q.ResidueField p.ResidueField) := add_le_add_right h1E _
      _ = Cardinal.toENat (Algebra.trdeg k p.ResidueField) := htotE
      _ ≤ _ := le_add_self
  · obtain ⟨m, hm, hmQ⟩ := Set.not_subset.1 hcase
    have hprime : (Q.map φ).IsPrime :=
      isPrime_map_awayDegreeZeroToAtPrime 𝒜 p hp hf Q le_rfl
    have htop : (Q.map φ • (⊤ : Submodule T T)) = Q.map φ := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
    have hdepth : 1 ≤ Module.depth T (maximalIdeal T) (T ⧸ Q.map φ • (⊤ : Submodule T T)) := by
      refine (Module.one_le_depth_iff_exists_isSMulRegular _).2 ⟨m, hm, fun a b hab => ?_⟩
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
      change m • Submodule.Quotient.mk a = m • Submodule.Quotient.mk b at hab
      rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
        htop, smul_eq_mul, smul_eq_mul, ← mul_sub] at hab
      rw [Submodule.Quotient.eq, htop]
      exact (hprime.mem_or_mem hab).resolve_left hmQ
    have hle : Cardinal.toENat (Algebra.trdeg k Q.ResidueField) ≤
        Cardinal.toENat (Algebra.trdeg k p.ResidueField) := htotE ▸ le_self_add
    calc Cardinal.toENat (Algebra.trdeg k Q.ResidueField) + 1
        ≤ Cardinal.toENat (Algebra.trdeg k p.ResidueField) + 1 := add_le_add_left hle _
      _ ≤ _ := by rw [add_comm]; exact add_le_add_left hdepth _

end Fibre

end Stacks.GradedLocalization

end
