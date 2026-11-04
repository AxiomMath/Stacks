module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.InseparableFrobeniusReconstruction
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.InseparableFrobeniusSplitting
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.InseparableFrobeniusSplittingLocalization
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.SeparableGoUpFiniteCase
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.ZeroSchemeSectionsNormalization
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRing
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.TorsionInFirstCohomology
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability

/-!
# The Frobenius data of a purely inseparable extension of degree `p`

This file supplies the inputs of the Frobenius route to [Stacks, Tag 0B4U] in the purely
inseparable case. Let `R` be a two-dimensional complete regular local ring of characteristic `p`
and `A` a finite `R`-algebra which is a domain whose fraction field is an inseparable extension
of degree `p` of that of `R`. Then there is a nonzero `c₀ ∈ R` such that for every pair of
modifications `X ⟶ Spec R`, `Y ⟶ Spec A` and every dominant `π : Y ⟶ X` over
`Spec A ⟶ Spec R`:

* the function field of `X` has characteristic `p` and contains the `p`-th power of every
  rational function of `Y`;
* there are an additive `p⁻¹`-linear map `θ` of the function field of `X`, preserving the
  sections of `𝒪_X` over the opens lying over the punctured spectrum of `R`, and global functions
  `bᵢ` of `X` and `βᵢ` of `Y` with `c₀ y = ∑ᵢ βᵢ θ(bᵢ yᵖ)` for every rational function `y` of `Y`.

These are the hypotheses `hpow`, `hΘ` and `hid` of
`AlgebraicGeometry.PuncturedRestriction.smul_rightDerived_pushUnit_eq_zero`.

## Main results

* `AlgebraicGeometry.PuncturedRestriction.exists_algebraMap_eq_pow_of_finrank_eq`: in an
  inseparable extension of prime degree `p` in characteristic `p` every `p`-th power lies in the
  base field.
* `AlgebraicGeometry.PuncturedRestriction.exists_frobeniusData`: the statement above.

## Implementation notes

`θ` is a Frobenius splitting of `R` ([Stacks, Tag 0C0S] through
`Stacks.ResolutionOfSurfaces.exists_frobeniusSplitting_of_isRegularLocalRing`) extended to the
fraction field, which is the function field of `X` because `f` is birational. Over the punctured
spectrum `f` is an isomorphism (`AlgebraicGeometry.isIso_morphismRestrict_of_isModification`),
so the local rings of `X` there are localizations `R_𝔭`, which `θ` preserves since
`θ(r / s) = θ(r sᵖ⁻¹) / s`; the sections over an open are the rational functions lying in all of
its local rings. The identity `c₀ y = ∑ᵢ βᵢ θ(bᵢ yᵖ)` is
`Stacks.ResolutionOfSurfaces.exists_smul_eq_sum_frobenius` on `A`, extended to the function field
by writing `y = a / r` with `a ∈ A` and `r ∈ R`.

## References

* [Stacks Project, Tag 0B4U](https://stacks.math.columbia.edu/tag/0B4U)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.PuncturedRestriction

/-! ### Algebra -/

section Algebra

/-- In an inseparable extension of prime degree `p` in characteristic `p`, every `p`-th power
lies in the base field. -/
theorem exists_algebraMap_eq_pow_of_finrank_eq {K L : Type*} [Field K] [Field L] [Algebra K L]
    (p : ℕ) [hp : Fact p.Prime] [CharP K p] (hdeg : Module.finrank K L = p)
    (hsep : ¬ Algebra.IsSeparable K L) (y : L) : ∃ k : K, algebraMap K L k = y ^ p := by
  have : FiniteDimensional K L := Module.finite_of_finrank_pos (by rw [hdeg]; exact hp.out.pos)
  have : ExpChar K p := ExpChar.prime hp.out
  have hins : Field.finInsepDegree K L ≠ 1 := fun h =>
    hsep ((isSeparable_iff_finInsepDegree_eq_one K L).2 h)
  have hmul := Field.finSepDegree_mul_finInsepDegree K L
  rw [hdeg] at hmul
  have hsep1 : Field.finSepDegree K L = 1 := by
    rcases hp.out.eq_one_or_self_of_dvd _ (Dvd.intro _ hmul) with h | h
    · exact h
    · rw [h] at hmul
      exact absurd ((Nat.mul_eq_left hp.out.ne_zero).1 hmul) hins
  have : IsPurelyInseparable K L := isPurelyInseparable_of_finSepDegree_eq_one hsep1
  obtain ⟨n, c, hc⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C K p y
  have hle := minpoly.natDegree_le (A := K) y
  rw [hc, hdeg, Polynomial.natDegree_X_pow_sub_C] at hle
  have hn : n ≤ 1 := by
    by_contra h
    have : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right hp.out.pos (by omega)
    have h2 : p < p ^ 2 := by
      rw [pow_two]; exact lt_mul_left hp.out.pos hp.out.one_lt
    omega
  have hroot : y ^ p ^ n = algebraMap K L c := by
    have h0 := minpoly.aeval K y
    rwa [hc, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] at h0
  interval_cases n
  · refine ⟨c ^ p, ?_⟩
    rw [map_pow, ← hroot, pow_zero, pow_one]
  · exact ⟨c, by rw [← hroot, pow_one]⟩

/-- For a finite extension `A` of an integrally closed domain `R` of characteristic `p` whose
fraction field extension is inseparable of degree `p`, every `p`-th power of `A` lies in `R`. -/
theorem exists_algebraMap_eq_pow (p : ℕ) [Fact p.Prime] (R A : Type*) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CharP R p] [CommRing A] [IsDomain A] [Algebra R A]
    [Module.Finite R A] [FaithfulSMul R A]
    (hdeg : letI := FractionRing.liftAlgebra R (FractionRing A)
      Module.finrank (FractionRing R) (FractionRing A) = p ∧
        ¬ Algebra.IsSeparable (FractionRing R) (FractionRing A)) (s : A) :
    ∃ r : R, algebraMap R A r = s ^ p := by
  let := FractionRing.liftAlgebra R (FractionRing A)
  have : CharP (FractionRing R) p :=
    charP_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R)) p
  obtain ⟨k, hk⟩ := exists_algebraMap_eq_pow_of_finrank_eq p hdeg.1 hdeg.2
    (algebraMap A (FractionRing A) s)
  have hint : _root_.IsIntegral R (algebraMap (FractionRing R) (FractionRing A) k) := by
    rw [hk, ← map_pow]
    exact (Algebra.IsIntegral.isIntegral (R := R) (s ^ p)).map (IsScalarTower.toAlgHom R A _)
  have hint' : _root_.IsIntegral R k :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom R (FractionRing R) (FractionRing A))
      (algebraMap (FractionRing R) (FractionRing A)).injective).1 hint
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
  refine ⟨r, IsFractionRing.injective A (FractionRing A) ?_⟩
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R (FractionRing R)
    (FractionRing A), hr, hk, map_pow]

/-- If every `p`-th power of `A` lies in `R`, every element of the fraction field of `A` is a
quotient `a / r` with `a ∈ A` and `0 ≠ r ∈ R`. -/
theorem exists_mul_algebraMap_eq_of_forall_pow {R A K : Type*} [CommRing R] [CommRing A]
    [IsDomain A] [Algebra R A] [Field K] [Algebra A K] [IsFractionRing A K] {p : ℕ} (hp : 1 ≤ p)
    (ρ : A → R) (hρ : ∀ s, algebraMap R A (ρ s) = s ^ p) (y : K) :
    ∃ (a : A) (r : R), r ≠ 0 ∧ y * algebraMap A K (algebraMap R A r) = algebraMap A K a := by
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := A) y
  have hs0 : algebraMap A K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  refine ⟨a * s ^ (p - 1), ρ s, fun h => ?_, ?_⟩
  · have h1 := hρ s
    rw [h, map_zero] at h1
    exact nonZeroDivisors.ne_zero hs (pow_eq_zero_iff (by omega) |>.1 h1.symm)
  · rw [hρ s, map_mul, map_pow, map_pow, div_mul_eq_mul_div, div_eq_iff hs0,
      mul_assoc, ← pow_succ, Nat.sub_add_cancel hp]

/-- The identity `c₀ y = ∑ᵢ βᵢ θ(bᵢ yᵖ)` on fraction fields, deduced from `c₀ s = ∑ᵢ θ(bᵢ sᵖ) βᵢ`
on `A` by writing `y = a / r`. -/
theorem mul_eq_sum_frobenius_of_eq_pow {R A KX KY : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [Field KX] [Field KY] [Algebra R KX] [Algebra A KY] {p : ℕ} (φ : KX →+* KY)
    (hφ : ∀ r, φ (algebraMap R KX r) = algebraMap A KY (algebraMap R A r))
    (ρ : A → R) (hρ : ∀ s, algebraMap R A (ρ s) = s ^ p) (θ : R →+ R) (θK : KX →+ KX)
    (hθK : ∀ a x, θK (a ^ p * x) = a * θK x)
    (hθK1 : ∀ z, θK (algebraMap R KX z) = algebraMap R KX (θ z)) {c₀ : R} {n : ℕ}
    {bA βA : Fin n → A} (hcβ : ∀ s : A, c₀ • s = ∑ i, θ (ρ (bA i) * ρ s) • βA i) {a : A} {r : R}
    (hr : algebraMap A KY (algebraMap R A r) ≠ 0) {y : KY}
    (hy : y * algebraMap A KY (algebraMap R A r) = algebraMap A KY a) {k : KX}
    (hk : φ k = y ^ p) :
    φ (algebraMap R KX c₀) * y =
      ∑ i, algebraMap A KY (βA i) * φ (θK (algebraMap R KX (ρ (bA i)) * k)) := by
  have hk' : k = ((algebraMap R KX r)⁻¹) ^ p * algebraMap R KX (ρ a) := by
    apply φ.injective
    rw [hk, map_mul, map_pow, map_inv₀, hφ, hφ, hρ a, map_pow, ← hy, mul_pow, inv_pow,
      mul_comm (y ^ p), inv_mul_cancel_left₀ (pow_ne_zero _ hr)]
  have hy' : y = algebraMap A KY a * (algebraMap A KY (algebraMap R A r))⁻¹ := by
    rw [← hy, mul_inv_cancel_right₀ hr]
  have hterm : ∀ i, θK (algebraMap R KX (ρ (bA i)) * k) =
      (algebraMap R KX r)⁻¹ * algebraMap R KX (θ (ρ (bA i) * ρ a)) := by
    intro i
    rw [hk', mul_left_comm, hθK, ← map_mul, hθK1]
  simp_rw [hterm, map_mul, map_inv₀, hφ]
  have hsum := congrArg (algebraMap A KY) (hcβ a)
  simp_rw [Algebra.smul_def, map_mul, map_sum, map_mul] at hsum
  rw [hy', ← mul_assoc, hsum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

end Algebra


/-! ### Geometry -/

section Geometry

variable {R : Type u} [CommRing R]

/-- The function field maps of a commutative square over `Spec A ⟶ Spec R` are compatible with
the maps from `R` and `A`. -/
theorem dominantFunctionFieldMap_algebraMap {A : Type u} [CommRing A] [Algebra R A]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Spec (.of R))
    (g : Y ⟶ Spec (.of A)) (π : Y ⟶ X) [IsDominant π]
    (hcomm : π ≫ f = g ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))) (r : R) :
    letI := SeparableGoUp.baseFunctionFieldAlgebra f
    letI := SeparableGoUp.baseFunctionFieldAlgebra g
    dominantFunctionFieldMap π (algebraMap R X.functionField r) =
      algebraMap A Y.functionField (algebraMap R A r) := by
  rw [SeparableGoUp.baseFunctionFieldAlgebra_algebraMap,
    SeparableGoUp.baseFunctionFieldAlgebra_algebraMap,
    ← SeparableGoUp.baseSection_comp f g π hcomm]
  exact SeparableGoUp.dominantFunctionFieldMap_germ π ⊤ trivial (baseSection X f r)

/-- Over the punctured spectrum, an additive map `θK` of the function field of a modification with
`θK (r / s) = θ (r sᵖ⁻¹) / s` sends every rational function into the local rings of `X`. -/
theorem exists_algebraMap_stalk_eq_of_ne_closedPoint [IsLocalRing R] [IsNoetherianRing R]
    [IsNormalDomain R] (hR : ringKrullDim R = 2) {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of R)) (hf : IsModification f) {p : ℕ} (θ : R →+ R)
    (θK : X.functionField →+ X.functionField)
    (hθK : letI := SeparableGoUp.baseFunctionFieldAlgebra f
      ∀ z s : R, s ≠ 0 → θK (algebraMap R X.functionField z / algebraMap R X.functionField s) =
        algebraMap R X.functionField (θ (z * s ^ (p - 1))) / algebraMap R X.functionField s)
    {U : X.Opens} (a : Γ(X, U)) (hU : genericPoint X ∈ U) {x : X} (hxU : x ∈ U)
    (hx : f x ≠ closedPoint R) :
    ∃ w : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField w =
      θK (X.presheaf.germ U (genericPoint X) hU a) := by
  let := SeparableGoUp.baseFunctionFieldAlgebra f
  have : Nonempty U := ⟨⟨_, hU⟩⟩
  have : IsFractionRing R X.functionField :=
    SeparableGoUp.isFractionRing_of_isBirational f hf.isBirational
  have := ZeroScheme.isIso_stalkMap_of_ne_closedPoint f hR hf hx
  obtain ⟨r, s, hs, hrs⟩ :=
    ZeroScheme.exists_mul_baseRingToStalk_eq f x (X.presheaf.germ U x hxU a)
  have hu : IsUnit (baseRingToStalk f x s) := of_not_not fun h =>
    hs ((ZeroScheme.baseRingToStalk_mem_maximalIdeal_iff f x s).1 h)
  have halg : ∀ t : R, algebraMap (X.presheaf.stalk x) X.functionField
      (baseRingToStalk f x t) = algebraMap R X.functionField t := by
    intro t
    have : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
    have h1 : baseRingToStalk f x t = X.presheaf.germ ⊤ x trivial (baseSection X f t) :=
      Scheme.Hom.germ_stalkMap_apply f ⊤ x trivial ((Scheme.ΓSpecIso (.of R)).inv t)
    rw [h1]
    exact Scheme.algebraMap_germ_eq_germToFunctionField X (U := ⊤) trivial _
  have hs' : s ≠ 0 := fun h => hs (h ▸ Ideal.zero_mem _)
  have hs0 : algebraMap R X.functionField s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 hs'
  have hga : X.presheaf.germ U (genericPoint X) hU a =
      algebraMap R X.functionField r / algebraMap R X.functionField s := by
    rw [eq_div_iff hs0, ← halg, ← halg, ← hrs, map_mul,
      Scheme.algebraMap_germ_eq_germToFunctionField X hxU]
  refine ⟨baseRingToStalk f x (θ (r * s ^ (p - 1))) * ↑(hu.unit⁻¹), ?_⟩
  rw [hga, hθK r s hs', eq_div_iff hs0, map_mul,
    halg, mul_assoc, ← halg s, ← map_mul, IsUnit.val_inv_mul, map_one, mul_one]

end Geometry

/-- **The Frobenius data of [Stacks, Tag 0B4U] in the purely inseparable case.** Let `R` be a
two-dimensional complete regular local ring of characteristic `p` and `A` a finite `R`-algebra
which is a domain, with fraction field inseparable of degree `p` over that of `R`. There is a
nonzero `c₀ ∈ R` such that for all modifications `f : X ⟶ Spec R`, `g : Y ⟶ Spec A` and every
dominant `π : Y ⟶ X` over `Spec A ⟶ Spec R`: the function field of `X` has characteristic `p`
and contains `yᵖ` for every rational function `y` of `Y`, and there are an additive map `θ` of
the function field of `X`, realized on the sections over the opens lying over the punctured
spectrum of `R`, and global functions `bᵢ`, `βᵢ` with `c₀ y = ∑ᵢ βᵢ θ(bᵢ yᵖ)`. -/
theorem exists_frobeniusData (p : ℕ) [Fact p.Prime] (R A : Type u) [CommRing R]
    [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R] [CharP R p] [CommRing A]
    [IsDomain A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A] (hR : ringKrullDim R = 2)
    (hdeg : letI := IsRegularLocalRing.isDomain R
      letI := FractionRing.liftAlgebra R (FractionRing A)
      Module.finrank (FractionRing R) (FractionRing A) = p ∧
        ¬ Algebra.IsSeparable (FractionRing R) (FractionRing A)) :
    letI := IsRegularLocalRing.isDomain R
    ∃ c₀ : R, c₀ ≠ 0 ∧ ∀ (X Y : Scheme.{u}) [IsIntegral X] [IsIntegral Y]
      (f : X ⟶ Spec (.of R)) (g : Y ⟶ Spec (.of A)) (π : Y ⟶ X) [IsDominant π],
      IsModification f → IsModification g →
      π ≫ f = g ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) →
      CharP X.functionField p ∧
      (∀ y : Y.functionField, ∃ k : X.functionField, dominantFunctionFieldMap π k = y ^ p) ∧
      ∃ (n : ℕ) (b : Fin n → Γ(X, ⊤)) (β : Fin n → Γ(Y, ⊤))
        (θ : X.functionField →+ X.functionField) (Θ : ∀ U : X.Opens, Γ(X, U) → Γ(X, U)),
        (∀ (U : X.Opens),
          U ≤ f ⁻¹ᵁ ⟨{closedPoint R}ᶜ, (isClosed_singleton_closedPoint R).isOpen_compl⟩ →
          ∀ (a : Γ(X, U)) (hU : genericPoint X ∈ U),
          X.presheaf.germ U (genericPoint X) hU (Θ U a) =
            θ (X.presheaf.germ U (genericPoint X) hU a)) ∧
        (∀ (k : X.functionField) (y : Y.functionField), dominantFunctionFieldMap π k = y ^ p →
          dominantFunctionFieldMap π (X.presheaf.germ ⊤ (genericPoint X) trivial
              (f.appTop ((Scheme.ΓSpecIso (.of R)).inv c₀))) * y =
            ∑ i, Y.presheaf.germ ⊤ (genericPoint Y) trivial (β i) *
              dominantFunctionFieldMap π
                (θ (X.presheaf.germ ⊤ (genericPoint X) trivial (b i) * k))) := by
  let := IsRegularLocalRing.isDomain R
  classical
  have : IsNormalDomain R := isNormalDomain_of_isRegularLocalRing R
  have hpp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  choose ρ hρ using exists_algebraMap_eq_pow p R A hdeg
  obtain ⟨θ, hθ, hθ1⟩ :=
    Stacks.ResolutionOfSurfaces.exists_frobeniusSplitting_of_isRegularLocalRing p R
  obtain ⟨c₀, n, bA, βA, hc₀, hcβ⟩ := Stacks.ResolutionOfSurfaces.exists_smul_eq_sum_frobenius
    (A := R) (B := A) ρ hρ θ hθ (by rw [hθ1]; exact one_ne_zero)
  refine ⟨c₀, hc₀, fun X Y _ _ f g π _ hf hg hcomm => ?_⟩
  let := SeparableGoUp.baseFunctionFieldAlgebra f
  let := SeparableGoUp.baseFunctionFieldAlgebra g
  have : IsFractionRing R X.functionField :=
    SeparableGoUp.isFractionRing_of_isBirational f hf.isBirational
  have : IsFractionRing A Y.functionField :=
    SeparableGoUp.isFractionRing_of_isBirational g hg.isBirational
  have hφ := dominantFunctionFieldMap_algebraMap f g π hcomm
  have hne : ∀ r : R, r ≠ 0 → algebraMap A Y.functionField (algebraMap R A r) ≠ 0 :=
    fun r hr h => hr (FaithfulSMul.algebraMap_injective R A
      (IsFractionRing.injective A Y.functionField (by rw [h, map_zero, map_zero])))
  obtain ⟨θK, hθK, hθKfrac⟩ :=
    Stacks.ResolutionOfSurfaces.exists_frobeniusSplitting_fractionRing (K := X.functionField)
      hpp θ hθ
  have hθK1 : ∀ z : R, θK (algebraMap R X.functionField z) =
      algebraMap R X.functionField (θ z) := fun z => by simpa using hθKfrac z 1 one_ne_zero
  have hfrac := exists_mul_algebraMap_eq_of_forall_pow (K := Y.functionField) hpp ρ hρ
  refine ⟨charP_of_injective_algebraMap (IsFractionRing.injective R X.functionField) p, ?_, ?_⟩
  · intro y
    obtain ⟨a, r, hr, hy⟩ := hfrac y
    refine ⟨algebraMap R X.functionField (ρ a) / algebraMap R X.functionField r ^ p, ?_⟩
    rw [map_div₀, map_pow, hφ, hφ, hρ a, map_pow, ← hy, mul_pow,
      mul_div_cancel_right₀ _ (pow_ne_zero _ (hne r hr))]
  · refine ⟨n, fun i => baseSection X f (ρ (bA i)), fun i => baseSection Y g (βA i), θK,
      fun U a => if h : ∃ t : Γ(X, U), ∀ hU : genericPoint X ∈ U,
        X.presheaf.germ U (genericPoint X) hU t = θK (X.presheaf.germ U (genericPoint X) hU a)
        then h.choose else a, ?_, ?_⟩
    · intro U hUW a hU
      have : Nonempty U := ⟨⟨_, hU⟩⟩
      have hex : ∃ t : Γ(X, U), ∀ hU : genericPoint X ∈ U,
          X.presheaf.germ U (genericPoint X) hU t =
            θK (X.presheaf.germ U (genericPoint X) hU a) := by
        obtain ⟨t, ht⟩ := exists_germToFunctionField_eq_of_forall_mem_range X U _ fun x =>
          exists_algebraMap_stalk_eq_of_ne_closedPoint hR f hf θ θK hθKfrac a hU x.2 (hUW x.2)
        exact ⟨t, fun _ => ht⟩
      dsimp only
      rw [dite_eq_left hex]
      exact hex.choose_spec hU
    · intro k y hk
      obtain ⟨a, r, hr, hy⟩ := hfrac y
      exact mul_eq_sum_frobenius_of_eq_pow (dominantFunctionFieldMap π) hφ ρ hρ θ θK hθK hθK1
        hcβ (hne r hr) hy hk

end AlgebraicGeometry.PuncturedRestriction

end
