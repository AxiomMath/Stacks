module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import StacksFrontier.RingTheory.Catenary.Formal
public import StacksFrontier.RingTheory.CohenRing
public import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem
public import StacksFrontier.RingTheory.Etale.IndEtaleFibres
public import StacksFrontier.RingTheory.GRing.Criteria
public import StacksFrontier.RingTheory.GRing.EssFiniteType
public import StacksFrontier.RingTheory.MvPowerSeries.AdicTopology
public import StacksFrontier.RingTheory.MvPowerSeries.RegularLocal
public import StacksFrontier.RingTheory.Regular.RegularRingHom
public import StacksFrontier.RingTheory.RegularRing.Defs
public import StacksFrontier.RingTheory.Smoothing.PopescuTheorem
public import StacksFrontier.RingTheory.Smoothing.ReductionToBaseField
public import StacksFrontier.RingTheory.Smoothing.RegularRingMap
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohen presentation data for a Noetherian local ring

Let `B` be a Noetherian local ring with maximal ideal `𝔪_B` and completion `B^∧`. Rotthaus' proof
that a Noetherian local ring with the approximation property is a G-ring presents `B^∧` as a
quotient of a complete regular local ring `R` which is "approximated" by a ring of finite type
over the prime ring: there are

* a Noetherian ring `R₀` and a complete regular local ring `R`,
* ring maps `R₀ → R` and `R₀ → B` and a surjection `ρ : R → B^∧` with
  `ρ ∘ (R₀ → R) = (B → B^∧) ∘ (R₀ → B)`,
* such that `R₀ → R` is a regular ring map (hence, by Popescu's theorem, a filtered colimit of
  smooth `R₀`-algebras),
* and elements `y_1, …, y_e ∈ R₀` whose images lie in `𝔪_R` and generate an `𝔪_R`-primary ideal.

The construction is the classical one. Let `x_1, …, x_m` generate `𝔪_B`. By the Cohen structure
theorem `B^∧` has a coefficient ring map `Λ → B^∧`, surjective onto the residue field, where `Λ`
is the residue field of `B^∧` if this has characteristic zero and a Cohen ring with that residue
field otherwise; then `R = Λ[[X_1, …, X_m]] → B^∧`, `X_i ↦ x_i`, is surjective. Take
`R₀ = ℤ[X_1, …, X_m]`, mapping `X_i` to `X_i` in `R` and to `x_i` in `B`; the two composites to
`B^∧` agree because they agree on the variables and ring maps out of `ℤ` are unique. The `y`'s are
the residue characteristic `c` of `B^∧` together with the variables: `𝔪_Λ = (c)` (with `c = 0` in
the field case), so `𝔪_R = (c, X_1, …, X_m)`.

The map `R₀ → R` is the composite `ℤ[X] → Λ[X] → Λ[[X]]`. The ring `Λ` is a regular domain of
characteristic zero in which every prime integer is a unit or generates `𝔪_Λ`, so `ℤ → Λ` is
flat with fibres a localization of `Λ`, the residue field of `Λ`, or zero, all regular over the
perfect residue fields of `ℤ`; hence `ℤ → Λ` is regular. Its base change `ℤ[X] → Λ[X]` is regular
(Stacks 07C1). The polynomial ring `Λ[X]` is a G-ring, being of finite type over the complete
local ring `Λ` (Stacks 07PS, 07PX), so its completion map along `(X_1, …, X_m)` is regular (Stacks
0AH2), and that completion is `Λ[[X]]` (`MvPowerSeries.toAdicCompletionAlgEquiv`). The composite
is regular (Stacks 07QI), its fibres being Noetherian since `Λ[[X]]` is.

## Main results

* `Stacks.ApproximationProperty.exists_cohenData`: the Cohen presentation data, with `R₀ → R`
  satisfying `Stacks.Smoothing.IsRegularRingMap`.
* `Stacks.ApproximationProperty.exists_cohenData_indSmooth`: the same data with `R₀ → R`
  ind-smooth (`Stacks.Smoothing.IndSmooth`), by Popescu's theorem (Stacks 07GC).

## Implementation notes

The source takes `R₀ = P[X_1, …, X_m]` with `P = 𝔽_p` when `B^∧` contains a coefficient field of
characteristic `p`. The coefficient ring map used here is the one supplied by the Cohen structure
theorem, `Stacks.CompleteLocalRing.CohenStructure.hasCoefficientRingHom`, which in residue
characteristic `p > 0` always produces a Cohen ring (possibly with a kernel in `B^∧`), so `P = ℤ`
works uniformly. That datum records a field or a Cohen ring `Λ`, records that `Λ` is a Cohen ring
whenever the residue characteristic is positive, and pins the generator of `𝔪_Λ`; the
characteristic zero of `Λ` which the regularity of `ℤ → Λ` needs is read off from it in
`exists_cohenData_isRegularRingHom`. The variables of `R₀` are indexed by `ULift (Fin m)`, so that
`R₀` lies in the universe of `B`.

## References

* C. Rotthaus, *Rings with approximation property*, Math. Ann. 287 (1990), 455–466, §3.3–3.4
* [Stacks Project, Tag 032A](https://stacks.math.columbia.edu/tag/032A) (Cohen structure theorem)
* [Stacks Project, Tag 07C1](https://stacks.math.columbia.edu/tag/07C1) (base change)
* [Stacks Project, Tag 07QI](https://stacks.math.columbia.edu/tag/07QI) (composition)
* [Stacks Project, Tag 0AH2](https://stacks.math.columbia.edu/tag/0AH2) (completion of a G-ring)
* [Stacks Project, Tag 07PX](https://stacks.math.columbia.edu/tag/07PX) (examples of G-rings)
* [Stacks Project, Tag 07GC](https://stacks.math.columbia.edu/tag/07GC) (Popescu's theorem)
-/

@[expose] public section

open IsLocalRing

open scoped TensorProduct

namespace Stacks.ApproximationProperty

universe u

section Helpers

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Let `Λ` be a local domain of characteristic zero whose maximal ideal is generated by a
natural number `c` which is zero or prime. Then a prime integer is either a unit of `Λ` or
generates its maximal ideal, so the quotient of `Λ` by it is the zero ring or the residue field;
in both cases it is regular. -/
private theorem isRegularRing_quotient_span_intCast_cohenData {Λ : Type*} [CommRing Λ]
    [IsLocalRing Λ] [IsDomain Λ] [CharZero Λ] {c : ℕ} (hc : c = 0 ∨ c.Prime)
    (hm : maximalIdeal Λ = Ideal.span {(c : Λ)}) (a : ℤ) (ha : Prime a) :
    IsRegularRing (Λ ⧸ Ideal.span {(a : Λ)}) := by
  by_cases hu : IsUnit (a : Λ)
  · have : Subsingleton (Λ ⧸ Ideal.span {(a : Λ)}) :=
      Ideal.Quotient.subsingleton_iff.2 (Ideal.span_singleton_eq_top.2 hu)
    exact isRegularRing_of_subsingleton _
  · have hmem : (a : Λ) ∈ maximalIdeal Λ := (mem_maximalIdeal _).2 hu
    have heq : Ideal.span {(a : Λ)} = maximalIdeal Λ := by
      rcases hc with hc0 | hcp
      · exfalso
        rw [hm, hc0, Nat.cast_zero, Ideal.mem_span_singleton, zero_dvd_iff,
          Int.cast_eq_zero] at hmem
        exact ha.ne_zero hmem
      · have hp' : Prime (c : ℤ) := Nat.prime_iff_prime_int.mp hcp
        by_cases hdvd : (c : ℤ) ∣ a
        · rw [hm]
          have hassoc : Associated (a : Λ) (c : Λ) := by
            simpa using ((Prime.associated_of_dvd hp' ha hdvd).symm).map (Int.castRingHom Λ)
          exact Ideal.span_singleton_eq_span_singleton.2 hassoc
        · exfalso
          obtain ⟨u, v, huv⟩ := (Prime.coprime_iff_not_dvd hp').2 hdvd
          have hcm : (c : Λ) ∈ maximalIdeal Λ := hm ▸ Ideal.mem_span_singleton_self _
          have h1 : ((u * c + v * a : ℤ) : Λ) ∈ maximalIdeal Λ := by
            push_cast
            exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hcm) (Ideal.mul_mem_left _ _ hmem)
          rw [huv, Int.cast_one] at h1
          exact (maximalIdeal.isMaximal Λ).ne_top ((Ideal.eq_top_iff_one _).2 h1)
    rw [heq]
    exact IsRegularRing.of_ringEquiv (R := ResidueField Λ) (RingEquiv.refl _)

/-- Let `Λ` be a regular domain of characteristic zero such that the quotient of `Λ` by every
prime integer is regular. Then `ℤ → Λ` is a regular ring map: it is flat because `Λ` is
torsion free, the generic fibre is a localization of `Λ`, the fibre over a prime `a` is
`Λ/aΛ`, and the residue fields of `ℤ` are perfect, so these regular fibres are geometrically
regular. -/
private theorem isRegularRingHom_int_cohenData (Λ : Type*) [CommRing Λ] [IsDomain Λ]
    [CharZero Λ] [IsRegularRing Λ]
    (hq : ∀ a : ℤ, Prime a → IsRegularRing (Λ ⧸ Ideal.span {(a : Λ)})) :
    IsRegularRingHom (algebraMap ℤ Λ) := by
  rw [isRegularRingHom_algebraMap_iff]
  refine ⟨RingHom.flat_algebraMap_iff.mpr inferInstance,
    fun p _ => ⟨Ideal.isNoetherianRing_fiber p Λ, ?_⟩⟩
  rcases eq_or_ne p ⊥ with rfl | hp
  · have : CharZero (⊥ : Ideal ℤ).ResidueField := IsFractionRing.charZero_of_isFractionRing ℤ
    have : IsLocalization (Algebra.algebraMapSubmonoid Λ (nonZeroDivisors ℤ))
        ((⊥ : Ideal ℤ).Fiber Λ) :=
      (Algebra.isLocalization_iff_isPushout (nonZeroDivisors ℤ)
        (⊥ : Ideal ℤ).ResidueField).mpr inferInstance
    have : IsRegularRing ((⊥ : Ideal ℤ).Fiber Λ) :=
      isRegularRing_of_isLocalization (Algebra.algebraMapSubmonoid Λ (nonZeroDivisors ℤ))
    exact Stacks.GRing.isGeometricallyRegular_of_perfectField _ _
  · have hpm : p.IsMaximal := IsPrime.to_maximal_ideal hp
    obtain ⟨a, rfl⟩ := Submodule.IsPrincipal.principal p
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hp (by simp)
    have ha : Prime a := (Ideal.span_singleton_prime ha0).1 inferInstance
    have : NeZero a.natAbs := ⟨Int.natAbs_ne_zero.mpr ha0⟩
    have : Finite (ℤ ⧸ Ideal.span {a}) :=
      Finite.of_equiv _ (Int.quotientSpanEquivZMod a).toEquiv.symm
    have : Finite (Ideal.span {a}).ResidueField :=
      Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField _).2
    let m : Ideal ℤ := Ideal.span {a}
    let e₀ : (ℤ ⧸ m) ≃ₐ[ℤ] m.ResidueField :=
      AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℤ (ℤ ⧸ m) m.ResidueField)
        m.bijective_algebraMap_quotient_residueField
    let e₁ : m.Fiber Λ ≃ₐ[ℤ] Λ ⧸ m.map (algebraMap ℤ Λ) :=
      (Algebra.TensorProduct.congr e₀.symm (AlgEquiv.refl : Λ ≃ₐ[ℤ] Λ)).trans
        ((Algebra.TensorProduct.comm ℤ (ℤ ⧸ m) Λ).trans
          ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot Λ m).symm.restrictScalars ℤ))
    have hmap : m.map (algebraMap ℤ Λ) = Ideal.span {(a : Λ)} := by
      rw [Ideal.map_span, Set.image_singleton, eq_intCast]
    have : IsRegularRing (Λ ⧸ m.map (algebraMap ℤ Λ)) := hmap ▸ hq a ha
    have : IsRegularRing (m.Fiber Λ) := IsRegularRing.of_ringEquiv e₁.symm.toRingEquiv
    exact Stacks.GRing.isGeometricallyRegular_of_perfectField _ _

end Helpers

/-! ### Regularity of `ℤ[X_1, …, X_m] → Λ[[X_1, …, X_m]]` -/

section Regularity

/-- `ℤ[X_1, …, X_m] → Λ[X_1, …, X_m]` is regular if `ℤ → Λ` is: up to the isomorphism
`Λ ⊗_ℤ ℤ[X] ≅ Λ[X]` it is the base change of `ℤ → Λ` along the finite type map `ℤ → ℤ[X]`
(Stacks 07C1). The variables of the polynomial ring over `ℤ` are indexed by `ULift (Fin m)`, so
that it lies in the universe of `Λ`. -/
private theorem isRegularRingHom_mvPolynomial_cohenData (Λ : Type u) [CommRing Λ] (m : ℕ)
    (h : IsRegularRingHom (algebraMap ℤ Λ)) :
    IsRegularRingHom ((MvPolynomial.rename (fun i : ULift.{u} (Fin m) => i.down)).toRingHom.comp
      (MvPolynomial.map (algebraMap ℤ Λ))) := by
  let e : Λ ⊗[ℤ] MvPolynomial (ULift.{u} (Fin m)) ℤ ≃+* MvPolynomial (Fin m) Λ :=
    ((MvPolynomial.algebraTensorAlgEquiv ℤ Λ).trans
      (MvPolynomial.renameEquiv Λ Equiv.ulift)).toRingEquiv
  convert (isRegularRingHom_baseChange (R := ℤ) (Λ := Λ)
    (R' := MvPolynomial (ULift.{u} (Fin m)) ℤ) h).comp_ringEquiv e using 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [e]
  · intro i
    simp [e, MvPolynomial.algebraTensorAlgEquiv_tmul]

/-- For a Noetherian complete local ring `Λ`, the inclusion `Λ[X_1, …, X_m] → Λ[[X_1, …, X_m]]`
is regular: `Λ[X]` is a G-ring (Stacks 07PS, 07PX), so its completion map along `(X_1, …, X_m)` is
regular (Stacks 0AH2), and that completion is `Λ[[X]]`. -/
private theorem isRegularRingHom_mvPowerSeries_cohenData (Λ : Type u) [CommRing Λ]
    [IsNoetherianRing Λ] [IsLocalRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] (m : ℕ) :
    IsRegularRingHom (algebraMap (MvPolynomial (Fin m) Λ) (MvPowerSeries (Fin m) Λ)) := by
  have hG : IsGRing (MvPolynomial (Fin m) Λ) :=
    isGRing_basic_examples.{u, u}.2.2.2.2 Λ (MvPolynomial (Fin m) Λ)
      (isGRing_basic_examples.{u, u}.2.1 Λ)
  convert (isRegularRingHom_algebraMap_adicCompletion hG
    (MvPolynomial.idealOfVars (Fin m) Λ)).comp_ringEquiv
      (MvPowerSeries.toAdicCompletionAlgEquiv (Fin m) Λ).symm.toRingEquiv using 1
  exact RingHom.ext fun p =>
    ((MvPowerSeries.toAdicCompletionAlgEquiv (Fin m) Λ).symm.commutes p).symm

/-- The composite `ℤ[X_1, …, X_m] → Λ[X_1, …, X_m] → Λ[[X_1, …, X_m]]` is regular when `ℤ → Λ` is
regular and `Λ` is a complete regular local ring (Stacks 07QI; its fibres are Noetherian because
`Λ[[X]]` is). -/
private theorem isRegularRingHom_cohenData (Λ : Type u) [CommRing Λ] [IsRegularLocalRing Λ]
    [IsAdicComplete (maximalIdeal Λ) Λ] (m : ℕ) (h : IsRegularRingHom (algebraMap ℤ Λ)) :
    IsRegularRingHom ((algebraMap (MvPolynomial (Fin m) Λ) (MvPowerSeries (Fin m) Λ)).comp
      ((MvPolynomial.rename (fun i : ULift.{u} (Fin m) => i.down)).toRingHom.comp
        (MvPolynomial.map (algebraMap ℤ Λ)))) := by
  have : IsRegularLocalRing (MvPowerSeries (Fin m) Λ) := MvPowerSeries.isRegularLocalRing Λ m
  refine isRegularRingHom_comp _ _ (isRegularRingHom_mvPolynomial_cohenData Λ m h)
    (isRegularRingHom_mvPowerSeries_cohenData Λ m) fun p _ => ?_
  intro
  exact Ideal.isNoetherianRing_fiber p _

end Regularity

/-! ### The construction -/

section Construction

/-- If the maximal ideal of a local ring `Λ` is generated by `a`, then the maximal ideal of
`Λ[[X_1, …, X_m]]` is generated by `a` and the variables. -/
private theorem maximalIdeal_mvPowerSeries_le_cohenData (Λ : Type*) [CommRing Λ] [IsLocalRing Λ]
    (m : ℕ) (a : Λ) (ha : maximalIdeal Λ = Ideal.span {a}) :
    maximalIdeal (MvPowerSeries (Fin m) Λ) ≤
      Ideal.span (insert (MvPowerSeries.C a) (Set.range MvPowerSeries.X)) := by
  intro φ hφ
  have hc := (Stacks.MvPowerSeries.RegularParameters.mem_maximalIdeal_iff_constantCoeff_mem φ).1 hφ
  rw [ha, Ideal.mem_span_singleton'] at hc
  obtain ⟨t, ht⟩ := hc
  have h1 : φ - MvPowerSeries.C (MvPowerSeries.constantCoeff φ) ∈
      Ideal.span (Set.range (MvPowerSeries.X : Fin m → MvPowerSeries (Fin m) Λ)) := by
    rw [MvPowerSeries.span_X_eq_ker_constantCoeff, RingHom.mem_ker]
    simp
  have h2 : φ = MvPowerSeries.C t * MvPowerSeries.C a +
      (φ - MvPowerSeries.C (MvPowerSeries.constantCoeff φ)) := by
    rw [← map_mul, ht]
    ring
  rw [h2]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
    (Ideal.span_mono (Set.subset_insert _ _) h1)

/-- The construction of the Cohen presentation data out of a coefficient ring map `f : Λ → B^∧`
which is surjective onto the residue field, for `Λ` a complete regular local ring whose maximal
ideal is generated by an integer `c` and over which `ℤ → Λ` is regular: with `x_1, …, x_m`
generating `𝔪_B`, take `R = Λ[[X_1, …, X_m]] → B^∧`, `X_i ↦ x_i`, and `R₀ = ℤ[X_1, …, X_m]`,
mapping `X_i` to `X_i` in `R` and to `x_i` in `B`; the elements `c, X_1, …, X_m` of `R₀` generate
`𝔪_R`. -/
private theorem exists_cohenData_of_coefficientRingHom (B : Type u) [CommRing B]
    [IsLocalRing B] [IsNoetherianRing B] (Λ : Type u) [CommRing Λ] [IsRegularLocalRing Λ]
    [IsAdicComplete (maximalIdeal Λ) Λ] (hreg : IsRegularRingHom (algebraMap ℤ Λ)) (c : ℕ)
    (hc : maximalIdeal Λ = Ideal.span {(c : Λ)}) (f : Λ →+* AdicCompletion (maximalIdeal B) B)
    (hf : Function.Surjective ((residue (AdicCompletion (maximalIdeal B) B)).comp f)) :
    ∃ (R₀ R : Type u) (_ : CommRing R₀) (_ : CommRing R) (_ : IsNoetherianRing R₀)
      (_ : IsRegularLocalRing R) (_ : Algebra R₀ R) (_ : Algebra R₀ B),
      IsAdicComplete (maximalIdeal R) R ∧
      ∃ ρ : R →+* AdicCompletion (maximalIdeal B) B, Function.Surjective ρ ∧
        ρ.comp (algebraMap R₀ R) =
          (algebraMap B (AdicCompletion (maximalIdeal B) B)).comp (algebraMap R₀ B) ∧
        IsRegularRingHom (algebraMap R₀ R) ∧
        ∃ (e : ℕ) (y : Fin e → R₀), (∀ i, algebraMap R₀ R (y i) ∈ maximalIdeal R) ∧
          ∃ N : ℕ, maximalIdeal R ^ N ≤ Ideal.span (Set.range (algebraMap R₀ R ∘ y)) := by
  obtain ⟨m, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    (maximalIdeal B).fg_of_isNoetherianRing
  have hx₁ : Ideal.span (Set.range x) = maximalIdeal B := hx
  have hx' : Ideal.span (Set.range (algebraMap B (AdicCompletion (maximalIdeal B) B) ∘ x)) =
      maximalIdeal (AdicCompletion (maximalIdeal B) B) := by
    rw [AdicCompletion.maximalIdeal_eq_map, ← hx₁, Ideal.map_span, Set.range_comp]
  obtain ⟨F, hFsurj, hFX, -⟩ :=
    Stacks.CompleteLocalRing.CohenStructure.exists_surjective_eval₂Hom
      (maximalIdeal (AdicCompletion (maximalIdeal B) B)) _ hx' f hf
  have : IsRegularLocalRing (MvPowerSeries (Fin m) Λ) := MvPowerSeries.isRegularLocalRing Λ m
  set φ : MvPolynomial (ULift.{u} (Fin m)) ℤ →+* MvPowerSeries (Fin m) Λ :=
    (algebraMap (MvPolynomial (Fin m) Λ) (MvPowerSeries (Fin m) Λ)).comp
      ((MvPolynomial.rename (fun i : ULift.{u} (Fin m) => i.down)).toRingHom.comp
        (MvPolynomial.map (algebraMap ℤ Λ))) with hφ
  have hφX : ∀ i, φ (MvPolynomial.X i) = MvPowerSeries.X i.down := by
    intro i
    simp [hφ, MvPowerSeries.algebraMap_apply']
  set ψ : MvPolynomial (ULift.{u} (Fin m)) ℤ →+* B :=
    MvPolynomial.eval₂Hom (Int.castRingHom B) (fun i => x i.down) with hψ
  have hcm : (c : Λ) ∈ maximalIdeal Λ := hc ▸ Ideal.mem_span_singleton_self _
  refine ⟨MvPolynomial (ULift.{u} (Fin m)) ℤ, MvPowerSeries (Fin m) Λ, inferInstance,
    inferInstance, inferInstance, inferInstance, φ.toAlgebra, ψ.toAlgebra,
    MvPowerSeries.isAdicComplete_maximalIdeal m Λ inferInstance, F, hFsurj, ?_,
    isRegularRingHom_cohenData Λ m hreg, m + 1,
    Fin.cons (c : MvPolynomial (ULift.{u} (Fin m)) ℤ) (fun i => MvPolynomial.X (ULift.up i)),
    ?_, 1, ?_⟩
  · rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
    apply MvPolynomial.ringHom_ext
    · intro r
      rw [eq_intCast MvPolynomial.C r, map_intCast, map_intCast]
    · intro i
      rw [RingHom.comp_apply, hφX, RingHom.comp_apply, hψ, MvPolynomial.eval₂Hom_X', hFX]
      rfl
  · intro i
    rw [RingHom.algebraMap_toAlgebra]
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Fin.cons_zero, map_natCast,
        Stacks.MvPowerSeries.RegularParameters.mem_maximalIdeal_iff_constantCoeff_mem]
      simpa using hcm
    · rw [Fin.cons_succ, hφX,
        Stacks.MvPowerSeries.RegularParameters.mem_maximalIdeal_iff_constantCoeff_mem]
      simp
  · rw [pow_one, RingHom.algebraMap_toAlgebra]
    refine (maximalIdeal_mvPowerSeries_le_cohenData Λ m (c : Λ) hc).trans (Ideal.span_mono ?_)
    rintro _ (rfl | ⟨j, rfl⟩)
    · exact ⟨0, by simp⟩
    · exact ⟨j.succ, by simp [hφX]⟩

/-- The Cohen presentation data with `R₀ → R` regular in the sense of `IsRegularRingHom`. The
coefficient ring map `Λ → B^∧` comes from the Cohen structure theorem: `Λ` is the residue field
(residue characteristic zero) or a Cohen ring (residue characteristic `p > 0`); in both cases `Λ`
is a complete regular local ring of characteristic zero whose maximal ideal is generated by the
residue characteristic, and `ℤ → Λ` is regular. -/
@[sga "2 IV 4.8" "more general", sga "2 IX 2.3" "more general"]
private theorem exists_cohenData_isRegularRingHom (B : Type u) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] :
    ∃ (R₀ R : Type u) (_ : CommRing R₀) (_ : CommRing R) (_ : IsNoetherianRing R₀)
      (_ : IsRegularLocalRing R) (_ : Algebra R₀ R) (_ : Algebra R₀ B),
      IsAdicComplete (maximalIdeal R) R ∧
      ∃ ρ : R →+* AdicCompletion (maximalIdeal B) B, Function.Surjective ρ ∧
        ρ.comp (algebraMap R₀ R) =
          (algebraMap B (AdicCompletion (maximalIdeal B) B)).comp (algebraMap R₀ B) ∧
        IsRegularRingHom (algebraMap R₀ R) ∧
        ∃ (e : ℕ) (y : Fin e → R₀), (∀ i, algebraMap R₀ R (y i) ∈ maximalIdeal R) ∧
          ∃ N : ℕ, maximalIdeal R ^ N ≤ Ideal.span (Set.range (algebraMap R₀ R ∘ y)) := by
  obtain ⟨Λ, _, _, _, -, hcohen, hmax, f, -, hf⟩ :=
    Stacks.CompleteLocalRing.CohenStructure.hasCoefficientRingHom
      (AdicCompletion (maximalIdeal B) B)
  set c := ringChar (ResidueField (AdicCompletion (maximalIdeal B) B))
  have hcc : CharP (ResidueField (AdicCompletion (maximalIdeal B) B)) c := ringChar.charP _
  have hc : c = 0 ∨ c.Prime :=
    (CharP.char_is_prime_or_zero (ResidueField (AdicCompletion (maximalIdeal B) B)) c).symm
  have key : CharZero Λ ∧ IsAdicComplete (maximalIdeal Λ) Λ ∧ IsRegularRing Λ ∧
      IsRegularLocalRing Λ := by
    rcases eq_or_ne c 0 with hc0 | hcne
    · -- Residue characteristic zero: `𝔪_Λ = (0)`, so `Λ` is a field, and it has characteristic
      -- zero because it maps onto the residue field of `B^∧`, which has characteristic zero.
      have hmbot : maximalIdeal Λ = ⊥ := by
        rw [hmax, hc0, Nat.cast_zero, Ideal.span_singleton_eq_bot]
      let : Field Λ := (isField_iff_maximalIdeal_eq.2 hmbot).toField
      have : CharP (ResidueField (AdicCompletion (maximalIdeal B) B)) 0 := hc0 ▸ hcc
      have := CharP.charP_to_charZero (ResidueField (AdicCompletion (maximalIdeal B) B))
      refine ⟨((residue (AdicCompletion (maximalIdeal B) B)).comp f).charZero, ?_, inferInstance,
        inferInstance⟩
      rw [hmbot]
      infer_instance
    · -- Residue characteristic `c > 0`: `Λ` is a Cohen ring, hence a discrete valuation ring whose
      -- maximal ideal is generated by the prime `c`, so `c` is a nonzero nonunit of `Λ` and a
      -- positive characteristic `q` of `Λ` would make `c` either zero (`q = c`) or a unit
      -- (`q ≠ c`, the two being coprime).
      have hcohenΛ : IsCohenRing Λ := hcohen hcne
      exact ⟨charZero_of_isCohenRing Λ, hcohenΛ.isAdicComplete, inferInstance, inferInstance⟩
  obtain ⟨_, _, _, _⟩ := key
  exact exists_cohenData_of_coefficientRingHom B Λ (isRegularRingHom_int_cohenData Λ
    fun a ha => isRegularRing_quotient_span_intCast_cohenData hc hmax a ha) c hmax f hf

end Construction

/-! ### Main results -/

/-- **Cohen presentation data** (Rotthaus, §3.3–3.4). Let `B` be a Noetherian local ring with
completion `B^∧`. There are a Noetherian ring `R₀`, a complete regular local ring `R`, ring maps
`R₀ → R` and `R₀ → B`, and a surjection `ρ : R → B^∧` compatible with them, such that `R₀ → R`
is a regular ring map and some finitely many elements `y_1, …, y_e` of `R₀` have images in `R`
lying in `𝔪_R` and generating an `𝔪_R`-primary ideal.

Concretely `R = Λ[[X_1, …, X_m]]` for a coefficient field or Cohen ring `Λ` of `B^∧` (Cohen
structure theorem, Stacks 032A), `ρ` sends `X_i` to a generator `x_i` of `𝔪_B`, `R₀ = ℤ[X_1, …,
X_m]` maps to `R` by `X_i ↦ X_i` and to `B` by `X_i ↦ x_i`, and the `y`'s are the residue
characteristic and the variables. -/
@[sga "2 IV 4.8" "more general", sga "2 IX 2.3" "more general", sga "2 XIV 5.2" "more general"]
theorem exists_cohenData (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] :
    ∃ (R₀ R : Type u) (_ : CommRing R₀) (_ : CommRing R) (_ : IsNoetherianRing R₀)
      (_ : IsRegularLocalRing R) (_ : Algebra R₀ R) (_ : Algebra R₀ B),
      IsAdicComplete (maximalIdeal R) R ∧
      ∃ ρ : R →+* AdicCompletion (maximalIdeal B) B, Function.Surjective ρ ∧
        ρ.comp (algebraMap R₀ R) =
          (algebraMap B (AdicCompletion (maximalIdeal B) B)).comp (algebraMap R₀ B) ∧
        Stacks.Smoothing.IsRegularRingMap R₀ R ∧
        ∃ (e : ℕ) (y : Fin e → R₀), (∀ i, algebraMap R₀ R (y i) ∈ maximalIdeal R) ∧
          ∃ N : ℕ, maximalIdeal R ^ N ≤ Ideal.span (Set.range (algebraMap R₀ R ∘ y)) := by
  obtain ⟨R₀, R, i₁, i₂, i₃, i₄, i₅, i₆, hcompl, ρ, hρ, hcomp, hreg, hy⟩ :=
    exists_cohenData_isRegularRingHom B
  exact ⟨R₀, R, i₁, i₂, i₃, i₄, i₅, i₆, hcompl, ρ, hρ, hcomp,
    Stacks.Smoothing.isRegularRingMap_of_regularRingHom R₀ R hreg, hy⟩

/-- **Cohen presentation data, ind-smooth form.** The data of `exists_cohenData`, with `R` a
filtered colimit of smooth `R₀`-algebras: `R₀ → R` is a regular ring map of Noetherian rings, so
this is Popescu's theorem (Stacks 07GC, `Stacks.Smoothing.indSmooth_of_isRegularRingMap`). -/
theorem exists_cohenData_indSmooth (B : Type u) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] :
    ∃ (R₀ R : Type u) (_ : CommRing R₀) (_ : CommRing R) (_ : IsNoetherianRing R₀)
      (_ : IsRegularLocalRing R) (_ : Algebra R₀ R) (_ : Algebra R₀ B),
      IsAdicComplete (maximalIdeal R) R ∧
      ∃ ρ : R →+* AdicCompletion (maximalIdeal B) B, Function.Surjective ρ ∧
        ρ.comp (algebraMap R₀ R) =
          (algebraMap B (AdicCompletion (maximalIdeal B) B)).comp (algebraMap R₀ B) ∧
        Stacks.Smoothing.IndSmooth R₀ R ∧
        ∃ (e : ℕ) (y : Fin e → R₀), (∀ i, algebraMap R₀ R (y i) ∈ maximalIdeal R) ∧
          ∃ N : ℕ, maximalIdeal R ^ N ≤ Ideal.span (Set.range (algebraMap R₀ R ∘ y)) := by
  obtain ⟨R₀, R, i₁, i₂, i₃, i₄, i₅, i₆, hcompl, ρ, hρ, hcomp, hreg, hy⟩ := exists_cohenData B
  exact ⟨R₀, R, i₁, i₂, i₃, i₄, i₅, i₆, hcompl, ρ, hρ, hcomp,
    Stacks.Smoothing.indSmooth_of_isRegularRingMap R₀ R hreg, hy⟩

end Stacks.ApproximationProperty

end
