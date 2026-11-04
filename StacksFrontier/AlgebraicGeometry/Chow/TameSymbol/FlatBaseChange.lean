module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.FormulaTower
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.FlatBaseChangeFibre
public import StacksFrontier.RingTheory.Fitting.Rank

/-!
# Flat base change for the tame symbol

Let `(A, 𝔪, κ) → (A', 𝔪', κ')` be a local homomorphism of Noetherian local rings with `A → A'`
flat and `dim(A) = dim(A') = 1`, and set `m = length_{A'}(A' / 𝔪A')`. Stacks 0EPG: for
nonzerodivisors `a₁, a₂ ∈ A`, the element `∂_A(a₁, a₂) ^ m` maps to `∂_{A'}(a₁, a₂)` under
`κ → κ'`, where `∂` is the tame symbol of Stacks 0EAQ (`Stacks.Chow.tameSymbolFormula`).

The proof is the source's. If both elements are units both symbols are `1`. Otherwise choose a
finite extension `A ⊆ B` with local factorizations `a_i = u_{i,j} π_j ^ {e_{i,j}}` (Stacks
0EAG); its base change `B' = A' ⊗_A B` carries the image factorizations
(`AlgebraicGeometry.TameSymbolPreparation.baseChange`), and both symbols are computed by the
formula of Stacks 0EAQ, for `B` and for `B'` (`Stacks.Chow.tameSymbolFormula_eq_symbolValue`,
which is Stacks 0EAR). Grouping the maximal ideals `𝔪'_{j,l}` of `B'` by the maximal ideal
`𝔪_j` of `B` under them, it suffices to show, for every unit `u` of `B_j`,

`(Norm_{κ_j/κ}(ū)^{m_j})^m = ∏_l Norm_{κ'_{j,l}/κ'}(ū)^{m'_{j,l}}`   (0GU1).

With `M = B_j / π_j B_j`, the left side is `det_κ(u : M)^m` (More on Algebra 0GSZ), which maps to
`det_{κ'}(u : M ⊗_A A')` (0GT0); and `M ⊗_A A' = ∏_l B'_{j,l} / π_j B'_{j,l}`
(`AlgebraicGeometry.TameSymbolPreparation.fibrePoint_bijective`,
`AlgebraicGeometry.TameSymbolPreparation.det_localization_fibreRing`), so by multiplicativity
of the determinant (0GSY) and 0GSZ again it is the right side.

## Main results

* `Stacks.Chow.map_norm_pow_eq_prod_fibre` — the identity (0GU1).
* `Stacks.Chow.map_tameSymbolFormula_pow_eq` — Stacks 0EPG.

## References

* [Stacks Project, Tag 0EPG](https://stacks.math.columbia.edu/tag/0EPG)
* [Stacks Project, Tag 0EAQ](https://stacks.math.columbia.edu/tag/0EAQ)
* [Stacks Project, Tag 0GSZ](https://stacks.math.columbia.edu/tag/0GSZ)
* [Stacks Project, Tag 0GT0](https://stacks.math.columbia.edu/tag/0GT0)
-/

@[expose] public section

open IsLocalRing AlgebraicGeometry

open scoped TensorProduct

universe u v w

namespace Stacks.Chow

section Factor

variable {R : Type*} [CommRing R] [IsLocalRing R] {K : Type*} [Field K]
  [Algebra K (ResidueField R)]

/-- The unit `(-1)^{ef} u^f v^{-e}` of a local ring. -/
noncomputable def symbolUnit (u v : Rˣ) (e f : ℕ) : Rˣ :=
  (-1) ^ (e * f) * u ^ f * v⁻¹ ^ e

omit [IsLocalRing R] in
/-- A ring homomorphism `g` maps `symbolUnit u v e f` to `symbolUnit (g u) (g v) e f`. -/
theorem map_symbolUnit {R' : Type*} [CommRing R'] (g : R →+* R') (u v : Rˣ) (e f : ℕ) :
    Units.map g.toMonoidHom (symbolUnit u v e f) =
      symbolUnit (Units.map g.toMonoidHom u) (Units.map g.toMonoidHom v) e f := by
  have hneg : Units.map g.toMonoidHom (-1 : Rˣ) = -1 := Units.ext (by simp)
  simp only [symbolUnit, map_mul, map_pow, map_inv, hneg]

/-- The factor of the formula Stacks 0EAQ is a norm of a residue raised to a length. -/
theorem coe_map_norm_factorizationValue (π : R) (u v : Rˣ) (e f : ℕ) :
    ((Units.map (Algebra.norm K : ResidueField R →* K) (factorizationValue π u v e f) : Kˣ) :
      K) = Algebra.norm K (residue R (symbolUnit u v e f : R)) ^ (Ring.ord R π).toNat := by
  have h : Units.map (residue R).toMonoidHom (symbolUnit u v e f) =
      (-1) ^ (e * f) * Units.map (residue R).toMonoidHom u ^ f *
        (Units.map (residue R).toMonoidHom v)⁻¹ ^ e := by
    rw [map_symbolUnit]
    rfl
  rw [factorizationValue, ← h, map_pow, Units.val_pow_eq_pow_val, Units.coe_map]
  rfl

end Factor

section Fibre

variable {A : Type u} {A' : Type v} [CommRing A] [CommRing A'] [IsNoetherianRing A]
  [IsNoetherianRing A'] [IsLocalRing A] [IsLocalRing A'] [Algebra A A'] [Module.Flat A A']
  [IsLocalHom (algebraMap A A')] {B : Type w} [CommRing B] [Algebra A B] {r : ℕ} {a : Fin r → A}

/-- The maximal ideal of `B` under a maximal ideal of `A' ⊗_A B`. -/
noncomputable def underPoint (P : TameSymbolPreparation a B) (Q : MaximalSpectrum (A' ⊗[A] B)) :
    MaximalSpectrum B :=
  ⟨TameSymbolPreparation.underIdeal Q.asIdeal, P.underIdeal_isMaximal Q.asIdeal⟩

/-- A quotient of a localization of a finite extension of a one-dimensional Noetherian local
ring by a nonzerodivisor has finite length over that localization. -/
theorem isFiniteLength_quotient_localization [Ring.KrullDimLE 1 A]
    (P : TameSymbolPreparation a B) (q : Ideal B) [q.IsMaximal] {π : Localization.AtPrime q}
    (hπ : IsRegular π) :
    IsFiniteLength (Localization.AtPrime q) (Localization.AtPrime q ⧸ Ideal.span {π}) := by
  let := P.finite
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have : Ring.KrullDimLE 1 B := krullDimLE_one_of_isIntegral A B
  have : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
  have := Stacks.Localization.krullDimLE_one_localizationAtPrime q
  exact isFiniteLength_quotient_span_singleton _ (isRegular_iff_mem_nonZeroDivisors.mp hπ)

/-- Multiplication by `y` on `B_𝔮 / π` has determinant (over the base) the norm of `ȳ` raised to
the length of `B_𝔮 / π`. -/
private theorem exists_det_eq_norm_pow_length_quotient {R : Type*} {S : Type*} [CommRing R]
    [CommRing S] [IsNoetherianRing R] [IsLocalRing R] [Algebra R S] [Ring.KrullDimLE 1 R] {n : ℕ}
    {c : Fin n → R} (P : TameSymbolPreparation c S) (q : MaximalSpectrum S)
    [IsLocalHom (algebraMap R (Localization.AtPrime q.asIdeal))]
    (y : Localization.AtPrime q.asIdeal) :
    ∃ hM : IsFiniteLength R (Localization.AtPrime q.asIdeal ⧸ Ideal.span {P.parameter q.asIdeal}),
      FiniteLengthEndomorphism.det R hM
          ((LinearMap.lsmul (Localization.AtPrime q.asIdeal)
            (Localization.AtPrime q.asIdeal ⧸ Ideal.span {P.parameter q.asIdeal}) y).restrictScalars
            R) =
        Algebra.norm (ResidueField R) (residue (Localization.AtPrime q.asIdeal) y) ^
          (Ring.ord (Localization.AtPrime q.asIdeal) (P.parameter q.asIdeal)).toNat := by
  have := P.finiteDimensional_residueField q
  have hM' := isFiniteLength_quotient_localization P q.asIdeal (P.parameter_isRegular q.asIdeal)
  exact ⟨_, FiniteLengthEndomorphism.multiplication_det_eq_norm_pow_length R
    (Localization.AtPrime q.asIdeal) _ hM' y⟩

/-- **The identity (0GU1) in the proof of Stacks 0EPG.** Let `𝔮` be a maximal ideal of `B`
and `y` a family of elements of the local rings of `B`. With `m = length_{A'}(A'/𝔪A')`,

`(Norm_{κ(𝔮)/κ}(ȳ_𝔮)^{length(B_𝔮/π)})^m ↦ ∏_{𝔮' over 𝔮} Norm_{κ(𝔮')/κ'}(ȳ)^{length(B'_{𝔮'}/π)}`

under `κ → κ'`, the product over the maximal ideals `𝔮'` of `B' = A' ⊗_A B` over `𝔮`. -/
theorem map_norm_pow_eq_prod_fibre (hdim : ringKrullDim A = 1) (hdim' : ringKrullDim A' = 1)
    (P : TameSymbolPreparation a B) (hnot : ¬ ∀ i, IsUnit (a i)) (q : MaximalSpectrum B)
    (y : ∀ (p : Ideal B) [p.IsMaximal], Localization.AtPrime p)
    [Fintype (MaximalSpectrum (A' ⊗[A] B))] [DecidableEq (MaximalSpectrum B)]
    [∀ q : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))]
    [∀ Q : MaximalSpectrum (A' ⊗[A] B),
      IsLocalHom (algebraMap A' (Localization.AtPrime Q.asIdeal))] :
    ResidueField.map (algebraMap A A')
        ((Algebra.norm (ResidueField A) (residue (Localization.AtPrime q.asIdeal) (y q.asIdeal)) ^
          (Ring.ord (Localization.AtPrime q.asIdeal) (P.parameter q.asIdeal)).toNat) ^
          (Module.length A' (A' ⧸ Ideal.map (algebraMap A A') (maximalIdeal A))).toNat) =
      ∏ Q : MaximalSpectrum (A' ⊗[A] B) with underPoint P Q = q,
        haveI := P.underIdeal_isMaximal Q.asIdeal
        Algebra.norm (ResidueField A') (residue (Localization.AtPrime Q.asIdeal)
            (P.localMap Q.asIdeal (y (TameSymbolPreparation.underIdeal Q.asIdeal)))) ^
          (Ring.ord (Localization.AtPrime Q.asIdeal)
            (P.localMap Q.asIdeal
              (P.parameter (TameSymbolPreparation.underIdeal Q.asIdeal)))).toNat := by
  classical
  have : Ring.KrullDimLE 1 A := krullDimLE_one_of_ringKrullDim_eq_one hdim
  have : Ring.KrullDimLE 1 A' := krullDimLE_one_of_ringKrullDim_eq_one hdim'
  set m := (Module.length A' (A' ⧸ Ideal.map (algebraMap A A') (maximalIdeal A))).toNat
  have hm : Module.length A' (A' ⧸ Ideal.map (algebraMap A A') (maximalIdeal A)) = m :=
    (ENat.natCast_toNat (Module.length_ne_top_iff.mpr (isFiniteLength_closedFibre hdim hdim'))).symm
  obtain ⟨hMA, h0⟩ := exists_det_eq_norm_pow_length_quotient (R := A) P q (y q.asIdeal)
  obtain ⟨hV, hbase⟩ := TameSymbolPreparation.map_det_pow_eq_det_fibreRing m hm
    (P.parameter q.asIdeal) (y q.asIdeal) hMA
  have hV' : IsFiniteLength A' (TameSymbolPreparation.FibreRing A' P q.asIdeal) := hV
  have : IsArtinianRing (TameSymbolPreparation.FibreRing A' P q.asIdeal) :=
    isArtinianRing_iff.mpr (isArtinian_of_tower A'
      (isFiniteLength_iff_isNoetherian_isArtinian.mp hV').2)
  let := Fintype.ofFinite (MaximalSpectrum (TameSymbolPreparation.FibreRing A' P q.asIdeal))
  have hsplit := FiniteLengthEndomorphism.det_lsmul_eq_prod_localization hV'
    (Ideal.Quotient.mk (TameSymbolPreparation.fibreIdeal A' P q.asIdeal)
      (Algebra.TensorProduct.includeRight (y q.asIdeal)))
  let E := Equiv.ofBijective _ (TameSymbolPreparation.fibrePoint_bijective (P := P) hV' hnot)
  have hfac (p : MaximalSpectrum (TameSymbolPreparation.FibreRing A' P q.asIdeal)) :
      FiniteLengthEndomorphism.det A' (FiniteLengthEndomorphism.isFiniteLength_localization hV' p)
        ((LinearMap.lsmul (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)
          (algebraMap (TameSymbolPreparation.FibreRing A' P q.asIdeal)
            (Localization.AtPrime p.asIdeal)
            (Ideal.Quotient.mk (TameSymbolPreparation.fibreIdeal A' P q.asIdeal)
              (Algebra.TensorProduct.includeRight (y q.asIdeal))))).restrictScalars A') =
      have := P.underIdeal_isMaximal (E p).1.asIdeal
      Algebra.norm (ResidueField A') (residue (Localization.AtPrime (E p).1.asIdeal)
          (P.localMap (E p).1.asIdeal (y (TameSymbolPreparation.underIdeal (E p).1.asIdeal)))) ^
        (Ring.ord (Localization.AtPrime (E p).1.asIdeal)
          (P.localMap (E p).1.asIdeal
            (P.parameter (TameSymbolPreparation.underIdeal (E p).1.asIdeal)))).toNat := by
    set Q := (E p).1
    have := P.underIdeal_isMaximal Q.asIdeal
    let P' := P.baseChange (fun i ↦ algebraMap A A' (a i)) (fun _ ↦ rfl)
      (exists_maximalIdeal_pow_le_closedFibre hdim hdim')
    obtain ⟨_, h1⟩ := exists_det_eq_norm_pow_length_quotient (R := A') P' Q
      (P.localMap Q.asIdeal (y (TameSymbolPreparation.underIdeal Q.asIdeal)))
    exact (TameSymbolPreparation.det_localization_fibreRing hV' p Q rfl y _).trans h1
  rw [Finset.prod_subtype (Finset.univ.filter fun Q ↦ underPoint P Q = q)
    (p := fun Q ↦ TameSymbolPreparation.underIdeal Q.asIdeal = q.asIdeal)
    (fun Q ↦ by simp [underPoint, MaximalSpectrum.ext_iff])]
  rw [← Fintype.prod_equiv E _ _ fun _ ↦ rfl, ← Finset.prod_congr rfl fun p _ ↦ hfac p,
    ← hsplit]
  exact (congrArg (fun t ↦ ResidueField.map (algebraMap A A') (t ^ m)) h0).symm.trans hbase

end Fibre

section FlatBaseChange

variable {A : Type u} {A' : Type v} [CommRing A] [CommRing A'] [IsNoetherianRing A]
  [IsNoetherianRing A'] [IsLocalRing A] [IsLocalRing A'] [Algebra A A'] [Module.Flat A A']
  [IsLocalHom (algebraMap A A')]

/-- **Flat base change for the tame symbol.** Let `(A, 𝔪, κ) → (A', 𝔪', κ')` be a local
homomorphism of Noetherian local rings, with `A → A'` flat and `dim(A) = dim(A') = 1`, and let
`m = length_{A'}(A' / 𝔪A')` (finite, by `Stacks.Chow.isFiniteLength_closedFibre`). For
nonzerodivisors `a₁, a₂ ∈ A`, the element `∂_A(a₁, a₂)^m` maps to `∂_{A'}(a₁, a₂)` via
`κ → κ'`, where `∂` is the tame symbol `Stacks.Chow.tameSymbolFormula`. -/
@[stacks 0EPG]
theorem map_tameSymbolFormula_pow_eq (hdim : ringKrullDim A = 1) (hdim' : ringKrullDim A' = 1)
    {a₁ a₂ : A} (ha₁ : IsRegular a₁) (ha₂ : IsRegular a₂) :
    Units.map (ResidueField.map (algebraMap A A')).toMonoidHom
        (tameSymbolFormula hdim a₁ a₂ ha₁ ha₂ ^
          (Module.length A' (A' ⧸ Ideal.map (algebraMap A A') (maximalIdeal A))).toNat) =
      tameSymbolFormula hdim' (algebraMap A A' a₁) (algebraMap A A' a₂)
        (Stacks.Fitting.isRegular_algebraMap_of_flat ha₁)
        (Stacks.Fitting.isRegular_algebraMap_of_flat ha₂) := by
  classical
  by_cases hboth : IsUnit a₁ ∧ IsUnit a₂
  · rw [tameSymbolFormula_eq_one hdim ha₁ ha₂ hboth.1 hboth.2,
      tameSymbolFormula_eq_one hdim' _ _ (hboth.1.map _) (hboth.2.map _), one_pow, map_one]
  have hnot : ¬ ∀ i, IsUnit ((![a₁, a₂] : Fin 2 → A) i) := fun h ↦ hboth ⟨h 0, h 1⟩
  obtain ⟨B, _, _, ⟨P⟩⟩ := AlgebraicGeometry.exists_tameSymbolPreparation_of_ringKrullDim_eq_one
    (le_refl 2) ![a₁, a₂] (fun i ↦ by fin_cases i <;> assumption) hnot hdim
  let P' := P.baseChange ![algebraMap A A' a₁, algebraMap A A' a₂]
    (fun i ↦ by fin_cases i <;> rfl) (exists_maximalIdeal_pow_le_closedFibre hdim hdim')
  let := P.finite_maximalSpectrum
  let := Fintype.ofFinite (MaximalSpectrum B)
  have := fun q ↦ P.isLocalHom q
  let := P'.finite_maximalSpectrum
  let := Fintype.ofFinite (MaximalSpectrum (A' ⊗[A] B))
  have := fun Q ↦ P'.isLocalHom Q
  rw [tameSymbolFormula_eq_symbolValue hdim ha₁ ha₂ P,
    tameSymbolFormula_eq_symbolValue hdim' _ _ P']
  set m := (Module.length A' (A' ⧸ Ideal.map (algebraMap A A') (maximalIdeal A))).toNat
  let y : ∀ (p : Ideal B) [p.IsMaximal], Localization.AtPrime p := fun p _ ↦
    (symbolUnit (P.factorUnit p 0) (P.factorUnit p 1) (P.exponent p 0) (P.exponent p 1) :
      Localization.AtPrime p)
  have hF (q : MaximalSpectrum B) :
      ((Units.map (Algebra.norm (ResidueField A) :
          ResidueField (Localization.AtPrime q.asIdeal) →* ResidueField A)
        (factorizationValue (P.parameter q.asIdeal) (P.factorUnit q.asIdeal 0)
          (P.factorUnit q.asIdeal 1) (P.exponent q.asIdeal 0) (P.exponent q.asIdeal 1)) :
          (ResidueField A)ˣ) : ResidueField A) =
        Algebra.norm (ResidueField A) (residue _ (y q.asIdeal)) ^
          (Ring.ord _ (P.parameter q.asIdeal)).toNat :=
    coe_map_norm_factorizationValue _ _ _ _ _
  have hG (Q : MaximalSpectrum (A' ⊗[A] B)) :
      ((Units.map (Algebra.norm (ResidueField A') :
          ResidueField (Localization.AtPrime Q.asIdeal) →* ResidueField A')
        (factorizationValue (P'.parameter Q.asIdeal) (P'.factorUnit Q.asIdeal 0)
          (P'.factorUnit Q.asIdeal 1) (P'.exponent Q.asIdeal 0) (P'.exponent Q.asIdeal 1)) :
          (ResidueField A')ˣ) : ResidueField A') =
        have := P.underIdeal_isMaximal Q.asIdeal
        Algebra.norm (ResidueField A') (residue (Localization.AtPrime Q.asIdeal)
            (P.localMap Q.asIdeal (y (TameSymbolPreparation.underIdeal Q.asIdeal)))) ^
          (Ring.ord (Localization.AtPrime Q.asIdeal)
            (P.localMap Q.asIdeal
              (P.parameter (TameSymbolPreparation.underIdeal Q.asIdeal)))).toNat := by
    have := P.underIdeal_isMaximal Q.asIdeal
    have hsym : ((symbolUnit (P'.factorUnit Q.asIdeal 0) (P'.factorUnit Q.asIdeal 1)
        (P'.exponent Q.asIdeal 0) (P'.exponent Q.asIdeal 1) : (Localization.AtPrime Q.asIdeal)ˣ) :
          Localization.AtPrime Q.asIdeal) =
        P.localMap Q.asIdeal (y (TameSymbolPreparation.underIdeal Q.asIdeal)) :=
      congrArg Units.val (map_symbolUnit (P.localMap Q.asIdeal) _ _ _ _).symm
    rw [coe_map_norm_factorizationValue, hsym]
    rfl
  apply Units.ext
  calc ((Units.map (ResidueField.map (algebraMap A A')).toMonoidHom
          (P.symbolValue 0 1 ^ m) : (ResidueField A')ˣ) : ResidueField A')
      = ∏ q : MaximalSpectrum B, ResidueField.map (algebraMap A A')
          ((Algebra.norm (ResidueField A) (residue _ (y q.asIdeal)) ^
            (Ring.ord _ (P.parameter q.asIdeal)).toNat) ^ m) := by
        simp only [TameSymbolPreparation.symbolValue, Units.coe_map, Units.val_pow_eq_pow_val,
          Units.coe_prod, ← hF, Finset.prod_pow, map_prod, map_pow]
        rfl
    _ = ∏ q : MaximalSpectrum B, ∏ Q : MaximalSpectrum (A' ⊗[A] B) with underPoint P Q = q,
          have := P.underIdeal_isMaximal Q.asIdeal
          Algebra.norm (ResidueField A') (residue (Localization.AtPrime Q.asIdeal)
              (P.localMap Q.asIdeal (y (TameSymbolPreparation.underIdeal Q.asIdeal)))) ^
            (Ring.ord (Localization.AtPrime Q.asIdeal)
              (P.localMap Q.asIdeal
                (P.parameter (TameSymbolPreparation.underIdeal Q.asIdeal)))).toNat :=
        Finset.prod_congr rfl fun q _ ↦ map_norm_pow_eq_prod_fibre hdim hdim' P hnot q y
    _ = ∏ Q : MaximalSpectrum (A' ⊗[A] B),
          have := P.underIdeal_isMaximal Q.asIdeal
          Algebra.norm (ResidueField A') (residue (Localization.AtPrime Q.asIdeal)
              (P.localMap Q.asIdeal (y (TameSymbolPreparation.underIdeal Q.asIdeal)))) ^
            (Ring.ord (Localization.AtPrime Q.asIdeal)
              (P.localMap Q.asIdeal
                (P.parameter (TameSymbolPreparation.underIdeal Q.asIdeal)))).toNat :=
        Finset.prod_fiberwise _ _ _
    _ = ((P'.symbolValue 0 1 : (ResidueField A')ˣ) : ResidueField A') := by
        simp only [TameSymbolPreparation.symbolValue, Units.coe_prod, hG]

end FlatBaseChange

end Stacks.Chow

end
