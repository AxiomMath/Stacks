module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.InseparableFirstCohomologyKill
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.InseparableFrobeniusSplitting
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.SeparableGoUpAssembly
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.ModificationATorsion
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRing
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.IntegralClosureBaseChange
public import StacksFrontier.FieldTheory.Separable.NoIntermediateField
public import StacksFrontier.RingTheory.Nagata.CompleteLocalRing
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.ZeroSchemeSectionsNormalization
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.CompleteLocalInduction

/-!
# Reduction to rational singularities through a purely inseparable extension of degree `p`

Let `A` be a complete regular local ring of dimension two and characteristic `p`, and `B` a normal
domain, finite over `A`, whose fraction field is purely inseparable of degree `p` over that of
`A`. The Frobenius route to [Stacks, Tag 0B4U]:

1. `sᵖ ∈ A` for every `s ∈ B` (`exists_algebraMap_eq_pow_of_isPurelyInseparable`), since every
   element of a purely inseparable extension of degree `p` has its `p`-th power in the base, and
   `A` is integrally closed;
2. `A` has a Frobenius splitting `θ` (`exists_frobeniusSplitting_of_isRegularLocalRing`, this is
   where completeness enters), whence `c s = ∑ᵢ θ(ρ(bᵢ) ρ(s)) βᵢ` on `B` for some `c ≠ 0`
   (`Stacks.ResolutionOfSurfaces.exists_smul_eq_sum_frobenius`);
3. `c` kills `H¹(Y, 𝒪_Y)` whenever `Y` is finite over a normal modification `X` of `Spec A` with
   `H¹(X, 𝒪_X) = 0` (`smul_firstCohomology_eq_zero_of_frobenius`);
4. every normal modification of `Spec B` is dominated by such a `Y`, and `H¹` only grows along
   the domination ([Stacks, Tag 0AXF]); the `c`-torsion of `H¹(Y, 𝒪_Y)` has uniformly bounded
   length ([Stacks, Tags 0AXJ, 0AXK]).

The domination of 4. and the vanishing `H¹(X, 𝒪_X) = 0` ([Stacks, Tag 0B4Q]) are taken as explicit
premises of `isReductionToRationalSingularitiesPossible_of_frobenius` below; no `@[stacks]`
attribute is attached to it.

## Main results

* `AlgebraicGeometry.SeparableGoUp.exists_algebraMap_eq_pow_of_isPurelyInseparable`: step 1.
* `AlgebraicGeometry.SeparableGoUp.isReductionToRationalSingularitiesPossible_of_frobenius`: the
  assembly.

## References

* [Stacks Project, Tag 0B4U](https://stacks.math.columbia.edu/tag/0B4U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Polynomial

universe u

namespace AlgebraicGeometry.SeparableGoUp

/-- **`p`-th powers of a purely inseparable extension of degree `p` lie in the base.** For a
normal domain `A` of characteristic `p` and a domain `B` integral over `A`, with fraction fields
`K ⊆ L` and `L / K` purely inseparable of degree `p`, every `sᵖ` with `s ∈ B` lies in `A`. -/
theorem exists_algebraMap_eq_pow_of_isPurelyInseparable' (A B K L : Type*) [CommRing A]
    [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B] [Algebra A B]
    [Algebra.IsIntegral A B] [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L]
    [IsFractionRing B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    (p : ℕ) [hp : Fact p.Prime] [CharP A p] [IsPurelyInseparable K L]
    (hdeg : Module.finrank K L = p) (s : B) :
    ∃ a : A, algebraMap A B a = s ^ p := by
  have : CharP K p := charP_of_injective_algebraMap (IsFractionRing.injective A K) p
  have : ExpChar K p := ExpChar.prime hp.out
  have : FiniteDimensional K L := Module.finite_of_finrank_pos (hdeg ▸ hp.out.pos)
  set x := algebraMap B L s
  obtain ⟨m, y, hmy⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C K p x
  have hdegle : (minpoly K x).natDegree ≤ p := hdeg ▸ minpoly.natDegree_le x
  have hnat : (minpoly K x).natDegree = p ^ m := by
    rw [hmy, natDegree_sub_C, natDegree_X_pow]
  have hm : m ≤ 1 := by
    by_contra hm
    have : p ^ 2 ≤ p ^ m := Nat.pow_le_pow_right hp.out.pos (by omega)
    have h2 : p < p ^ 2 := by nlinarith [hp.out.two_le]
    omega
  have hroot : x ^ p ^ m = algebraMap K L y := by
    simpa [hmy, sub_eq_zero] using minpoly.aeval K x
  obtain ⟨k, hk⟩ : ∃ k : K, algebraMap K L k = x ^ p := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with rfl | rfl
    · exact ⟨y ^ p, by rw [map_pow, ← hroot, pow_zero, pow_one]⟩
    · exact ⟨y, by rw [← hroot, pow_one]⟩
  have hkint : _root_.IsIntegral A k := by
    have hs : _root_.IsIntegral A (x ^ p) :=
      ((Algebra.IsIntegral.isIntegral (R := A) s).map (IsScalarTower.toAlgHom A B L)).pow p
    rw [← hk] at hs
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom A K L)
      (algebraMap K L).injective).mp hs
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hkint
  refine ⟨a, IsFractionRing.injective B L ?_⟩
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A K, ha, hk, map_pow]

/-- `exists_algebraMap_eq_pow_of_isPurelyInseparable'` for the fraction fields `FractionRing A` and
`FractionRing B`. -/
theorem exists_algebraMap_eq_pow_of_isPurelyInseparable (A B : Type u) [CommRing A]
    [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B] [Algebra A B]
    [Algebra.IsIntegral A B] [FaithfulSMul A B] (p : ℕ) [hp : Fact p.Prime] [CharP A p]
    (h : letI := FractionRing.liftAlgebra A (FractionRing B)
      IsPurelyInseparable (FractionRing A) (FractionRing B) ∧
        Module.finrank (FractionRing A) (FractionRing B) = p) (s : B) :
    ∃ a : A, algebraMap A B a = s ^ p := by
  let := FractionRing.liftAlgebra A (FractionRing B)
  have : IsScalarTower A (FractionRing A) (FractionRing B) :=
    FractionRing.isScalarTower_liftAlgebra A (FractionRing B)
  have := h.1
  exact exists_algebraMap_eq_pow_of_isPurelyInseparable' A B (FractionRing A) (FractionRing B) p
    h.2 s

/-- **Reduction to rational singularities through a purely inseparable extension of degree `p`,
from its two geometric inputs.** Let `R` be a complete regular local ring of dimension two and
characteristic `p`, and `B` a normal domain finite over `R` with `sᵖ ∈ R` for every `s ∈ B` (which
holds when `B` is normal with fraction field purely inseparable of degree `p` over that of `R`,
`exists_algebraMap_eq_pow_of_isPurelyInseparable`). Then reduction to rational singularities is
possible for `B`, given: `H¹(X, 𝒪_X) = 0` for every normal modification `X` of `Spec R` (`hrat`)
and the domination of normal modifications of `Spec B` by ones finite over normal modifications of
`Spec R` (`hdom`). The rest of the source's argument is replaced by the Frobenius route. -/
theorem isReductionToRationalSingularitiesPossible_of_frobenius (R B : Type u) [CommRing R]
    [IsRegularLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [IsDomain R] (p : ℕ)
    (hp : p.Prime) (hc : CharP R p) (hdim : ringKrullDim R = 2) [CommRing B] [IsNormalDomain B]
    [Algebra R B] [Module.Finite R B] [FaithfulSMul R B]
    (hpow : ∀ s : B, ∃ a : R, algebraMap R B a = s ^ p)
    (hrat : DefinesRationalSingularity R)
    (hdom : IsDominatedByFiniteOverBase R B) :
    IsReductionToRationalSingularitiesPossible B := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsNormalDomain R := isNormalDomain_of_isRegularLocalRing R
  have : Algebra.IsIntegral R B := Algebra.IsIntegral.of_finite R B
  -- the Frobenius lift and the splitting
  choose ρ hρ using hpow
  obtain ⟨θ, hθ, hθ1⟩ := Stacks.ResolutionOfSurfaces.exists_frobeniusSplitting_of_isRegularLocalRing
    (p := p) R
  obtain ⟨c, n, b, β, hc0, hcid⟩ := Stacks.ResolutionOfSurfaces.exists_smul_eq_sum_frobenius
    (p := p) ρ hρ θ hθ (by simp [hθ1])
  have hcB : algebraMap R B c ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R B)).mpr hc0
  -- the bound of [Stacks, Tag 0AXJ] for `B`
  have hBc := Stacks.ResolutionOfSurfaces.isNoetherianCompleteLocalRing_of_finite R B
  have : IsNoetherianRing B := hBc.isNoetherian
  have : IsLocalRing B := hBc.isLocal
  have : IsAdicComplete (IsLocalRing.maximalIdeal B) B := hBc.isComplete
  have : IsNagataRing B := IsNagataRing.of_isPrecomplete_maximalIdeal
  have hdimB : ringKrullDim B = 2 := (Algebra.IsIntegral.ringKrullDim_eq R B).symm.trans hdim
  obtain ⟨N, hN⟩ := exists_uniform_bound_length_quotient_baseToZeroSchemeSections hdimB hcB
  refine ⟨N, fun Y _ g hg => ?_⟩
  have : IsIntegral Y := hg.source_isIntegral
  obtain ⟨Y', X', g', f', π, q, _, _, hg', hf', _, _, hcomm, hq⟩ := hdom Y g hg
  have : IsIntegral Y' := hg'.source_isIntegral
  have hqmod : IsModification q := by
    subst hq
    exact isModification_of_comp hg hg'
  have h1 := length_firstCohomology_le_of_isModification g q hqmod
  rw [hq] at h1
  -- `c` kills `H¹(Y', 𝒪_{Y'})`
  have htop : Submodule.torsionBy B (firstCohomologyAsBaseModule Y' g') (algebraMap R B c) = ⊤ :=
    eq_top_iff.mpr fun x _ => (Submodule.mem_torsionBy_iff _ _).mpr
      (smul_firstCohomology_eq_zero_of_frobenius R B hdim p ρ hρ θ hθ c b β hcid f' g' π hf' hg'
        hcomm (hrat X' f' hf') x)
  have h2 : Module.length B (firstCohomologyAsBaseModule Y' g') =
      Module.length B (Submodule.torsionBy B (firstCohomologyAsBaseModule Y' g')
        (algebraMap R B c)) := by
    rw [htop]
    exact Submodule.topEquiv.length_eq.symm
  refine h1.trans ?_
  rw [h2, ← length_quotient_baseToZeroSchemeSections_eq Y' g' hg' hcB]
  exact_mod_cast hN Y' g' hg'

/-- **`isReductionToRationalSingularitiesPossible_of_frobenius` in the shape of the `insep` input
of [Stacks, Tag 0BGN]**: the fraction field of the normal domain `B` is purely inseparable of
degree `p` over that of `R`. -/
theorem isReductionToRationalSingularitiesPossible_of_isPurelyInseparable_of_frobenius
    (R B : Type u) [CommRing R] [IsRegularLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [IsDomain R] (p : ℕ) (hp : p.Prime)
    (hc : CharP R p) (hdim : ringKrullDim R = 2) [CommRing B] [IsNormalDomain B] [Algebra R B]
    [Module.Finite R B] [FaithfulSMul R B]
    (h : letI := FractionRing.liftAlgebra R (FractionRing B)
      IsPurelyInseparable (FractionRing R) (FractionRing B) ∧
        Module.finrank (FractionRing R) (FractionRing B) = p)
    (hrat : DefinesRationalSingularity R) (hdom : IsDominatedByFiniteOverBase R B) :
    IsReductionToRationalSingularitiesPossible B := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsNormalDomain R := isNormalDomain_of_isRegularLocalRing R
  have : Algebra.IsIntegral R B := Algebra.IsIntegral.of_finite R B
  exact isReductionToRationalSingularitiesPossible_of_frobenius R B p hp hc hdim
    (exists_algebraMap_eq_pow_of_isPurelyInseparable R B p h) hrat hdom

/-- An extension of prime degree has no intermediate fields besides its two ends. -/
theorem _root_.IntermediateField.eq_bot_or_eq_top_of_finrank_prime {K L : Type*} [Field K] [Field L]
    [Algebra K L] (hp : (Module.finrank K L).Prime) (M : IntermediateField K L) :
    M = ⊥ ∨ M = ⊤ := by
  have : FiniteDimensional K L := Module.finite_of_finrank_pos hp.pos
  have h := Module.finrank_mul_finrank K M L
  rcases (Nat.dvd_prime hp).mp (Dvd.intro _ h) with h1 | h1
  · exact Or.inl (IntermediateField.finrank_eq_one_iff.mp h1)
  · refine Or.inr (IntermediateField.finrank_eq_one_iff_eq_top.mp ?_)
    rw [h1] at h
    nlinarith [hp.pos, Nat.le_of_dvd hp.pos (Dvd.intro_left _ h)]

/-- **[Stacks, Tag 0B4U] at the source's hypotheses, from its two geometric inputs.** Let `A` be
a complete regular local ring of dimension two and characteristic `p`, `L / K` an inseparable
extension of degree `p` of its fraction field, and `B ⊆ L` the integral closure of `A`. Then
reduction to rational singularities is possible for `B`, given `H¹(X, 𝒪_X) = 0` on the normal
modifications of `Spec A` (`hrat`, [Stacks, Tag 0B4Q]) and the domination step of
[Stacks, Tag 0AXL] (`hdom`). -/
theorem isReductionToRationalSingularitiesPossible_integralClosure_of_frobenius (p : ℕ)
    (hp : p.Prime) (A : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [CharP A p] (hdim : ringKrullDim A = 2)
    (K L : Type u) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] (hdeg : Module.finrank K L = p)
    (hinsep : ¬ Algebra.IsSeparable K L)
    (hrat : letI := IsRegularLocalRing.isDomain A; DefinesRationalSingularity A)
    (hdom : letI := IsRegularLocalRing.isDomain A
      IsDominatedByFiniteOverBase A (integralClosure A L)) :
    IsReductionToRationalSingularitiesPossible (integralClosure A L) := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsDomain A := IsRegularLocalRing.isDomain A
  have : IsNormalDomain A := isNormalDomain_of_isRegularLocalRing A
  have : FiniteDimensional K L := Module.finite_of_finrank_pos (hdeg ▸ hp.pos)
  obtain ⟨-, hpi, -⟩ :=
    (IntermediateField.isSeparable_or_finrank_eq_ringChar_of_forall_eq_bot_or_eq_top
      (IntermediateField.eq_bot_or_eq_top_of_finrank_prime (hdeg ▸ hp))).resolve_left hinsep
  let B := integralClosure A L
  have : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  have : IsIntegrallyClosed B := integralClosure.isIntegrallyClosedOfFiniteExtension K
  have : IsNormalDomain B := ⟨inferInstance, inferInstance⟩
  have : Module.Finite A B :=
    module_finite_integralClosure_of_isNagataRing K L IsNagataRing.of_isPrecomplete_maximalIdeal
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr fun x y h =>
    hAL (by rw [IsScalarTower.algebraMap_apply A B L, h, ← IsScalarTower.algebraMap_apply])
  exact isReductionToRationalSingularitiesPossible_of_frobenius A B p hp ‹_› hdim
    (exists_algebraMap_eq_pow_of_isPurelyInseparable' A B K L p hdeg) hrat hdom

end AlgebraicGeometry.SeparableGoUp

end
