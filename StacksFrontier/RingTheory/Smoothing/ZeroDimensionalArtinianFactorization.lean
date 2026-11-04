module

public import StacksFrontier.RingTheory.Smoothing.PositiveCharacteristicResolution

/-!
# The zero-dimensional case of the Artinian approximation data

Stacks 07FT — clauses (2) and (3) of Stacks 07FH taken together — is the one remaining gap in
the proof of Popescu's theorem in this repository. This file proves it under the added
hypothesis `dim Λ_𝔮 = 0`.

## Main results

* `Stacks.Smoothing.artinianApproximationDataAt_of_ringKrullDim_eq_zero`: the conclusion of
  `Stacks.Smoothing.ArtinianApproximationDataAt` when `ringKrullDim Λ_𝔮 = 0`.

## References

* [Stacks Project, Tag 07FT](https://stacks.math.columbia.edu/tag/07FT)
* [Stacks Project, Tag 07FH](https://stacks.math.columbia.edu/tag/07FH)
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

namespace Stacks.Smoothing

universe u

/-- A nontrivial commutative ring in which every nonzero element is a unit is a field. -/
private theorem isField_of_forall_isUnit {R : Type*} [CommRing R] [Nontrivial R]
    (hu : ∀ x : R, x ≠ 0 → IsUnit x) : IsField R :=
  ⟨exists_pair_ne R, mul_comm, fun {a} ha => (hu a ha).exists_right_inv⟩

/-- The quotient map by the zero ideal is bijective. -/
private theorem bijective_quotient_mk_of_eq_bot {R : Type*} [CommRing R] {I : Ideal R}
    (hI : I = ⊥) : Function.Bijective (Ideal.Quotient.mk I) :=
  ⟨(injective_iff_map_eq_zero _).2 fun a ha => by
    simpa [hI] using Ideal.Quotient.eq_zero_iff_mem.mp ha, Ideal.Quotient.mk_surjective⟩

/-- Localizing a ring whose nonzero elements are units at the zero prime changes nothing. -/
private theorem bijective_algebraMap_atPrime {R : Type u} [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime]
    (hbot : 𝔭 = ⊥) (hu : ∀ x : R, x ≠ 0 → IsUnit x) :
    Function.Bijective (algebraMap R (Localization.AtPrime 𝔭)) := by
  have hle : 𝔭.primeCompl ≤ IsUnit.submonoid R := by
    intro y hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hy (hbot ▸ Submodule.zero_mem 𝔭)
    exact (IsUnit.mem_submonoid_iff y).mpr (hu y hy0)
  exact (IsLocalization.atUnits R 𝔭.primeCompl hle).bijective

/-- Separability of a field extension passes to a subextension. -/
private theorem isSeparableExtension_of_algHom {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] (f : K →ₐ[k] L) [Algebra.IsSeparableExtension k L] :
    Algebra.IsSeparableExtension k K := by
  have : Algebra.IsGeometricallyReduced k L :=
    ((Algebra.isSeparableExtension_tfae k L (ringExpChar k)).out 1 4).mp
      (show Algebra.IsSeparableExtension k L from inferInstance)
  exact ((Algebra.isSeparableExtension_tfae k K (ringExpChar k)).out 4 1).mp
    (Algebra.IsGeometricallyReduced.of_injective f f.injective)

/-- A ring homomorphism out of a field is flat. -/
private theorem flat_ringHom_of_field {K R : Type*} [Field K] [CommRing R]
    (f : K →+* R) : f.Flat := by
  let : Algebra K R := f.toAlgebra
  rw [← RingHom.algebraMap_toAlgebra f]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- If `Λ` is a Noetherian geometrically regular `k`-algebra and `dim Λ_𝔮 = 0`, then the maximal
ideal of `Λ_𝔮` is zero. -/
private theorem maximalIdeal_atPrime_eq_bot_of_ringKrullDim_eq_zero (k : Type u) {Λ : Type u}
    [Field k] [CommRing Λ] [Algebra k Λ] [IsNoetherianRing Λ] [Algebra.IsGeometricallyRegular k Λ]
    (𝔮 : Ideal Λ) [𝔮.IsPrime] (hdim : ringKrullDim (Localization.AtPrime 𝔮) = 0) :
    maximalIdeal (Localization.AtPrime 𝔮) = ⊥ := by
  have : IsRegularRing Λ := by
    have : IsRegularRing (k ⊗[k] Λ) :=
      Algebra.IsGeometricallyRegular.isRegularRing_tensorProduct k
    exact IsRegularRing.of_ringEquiv (Algebra.TensorProduct.lid k Λ).toRingEquiv
  have : IsRegularLocalRing (Localization.AtPrime 𝔮) :=
    IsRegularRing.isRegularLocalRing_of_isLocalization 𝔮 (Localization.AtPrime 𝔮)
  have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := Localization.AtPrime 𝔮)
  rw [hdim] at h
  exact (Submodule.spanFinrank_eq_zero_iff_eq_bot
    (IsNoetherian.noetherian (maximalIdeal (Localization.AtPrime 𝔮)))).1 (by exact_mod_cast h)

/-- If `dim Λ_𝔮 = 0` and `n ≥ 1`, then `𝔮^nΛ_𝔮 = 0`. -/
private theorem map_pow_eq_bot_of_ringKrullDim_eq_zero (k : Type u) {Λ : Type u} [Field k]
    [CommRing Λ] [Algebra k Λ] [IsNoetherianRing Λ] [Algebra.IsGeometricallyRegular k Λ]
    (𝔮 : Ideal Λ) [𝔮.IsPrime] (hdim : ringKrullDim (Localization.AtPrime 𝔮) = 0) {n : ℕ}
    (hn : 1 ≤ n) :
    Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) (𝔮 ^ n) = ⊥ := by
  rw [Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal,
    maximalIdeal_atPrime_eq_bot_of_ringKrullDim_eq_zero k 𝔮 hdim, Ideal.bot_pow (by omega)]

/-- If `dim Λ_𝔮 = 0` and `n ≥ 1`, then `Λ_𝔮/𝔮^nΛ_𝔮` is a field. -/
private theorem isField_primePowerQuotient_of_ringKrullDim_eq_zero (k : Type u) {Λ : Type u}
    [Field k] [CommRing Λ] [Algebra k Λ] [IsNoetherianRing Λ] [Algebra.IsGeometricallyRegular k Λ]
    (𝔮 : Ideal Λ) [𝔮.IsPrime] (hdim : ringKrullDim (Localization.AtPrime 𝔮) = 0) {n : ℕ}
    (hn : 1 ≤ n) : IsField (primePowerQuotient 𝔮 n) :=
  MulEquiv.isField
    (IsLocalRing.isField_iff_maximalIdeal_eq.2
      (maximalIdeal_atPrime_eq_bot_of_ringKrullDim_eq_zero k 𝔮 hdim))
    (RingEquiv.ofBijective _ (bijective_quotient_mk_of_eq_bot
      (map_pow_eq_bot_of_ringKrullDim_eq_zero k 𝔮 hdim hn))).symm.toMulEquiv

/-- If `dim Λ_𝔮 = 0` and `n ≥ 1`, then `Λ_𝔮/𝔮^nΛ_𝔮 = κ(𝔮)` is formally smooth over `k`. -/
private theorem formallySmooth_primePowerQuotient_of_ringKrullDim_eq_zero (k : Type u) {Λ : Type u}
    [Field k] [CommRing Λ] [Algebra k Λ] [IsNoetherianRing Λ] [Algebra.IsGeometricallyRegular k Λ]
    (𝔮 : Ideal Λ) [𝔮.IsPrime] (hdim : ringKrullDim (Localization.AtPrime 𝔮) = 0) {n : ℕ}
    (hn : 1 ≤ n) : Algebra.FormallySmooth k (primePowerQuotient 𝔮 n) := by
  have hmaxQ := maximalIdeal_atPrime_eq_bot_of_ringKrullDim_eq_zero k 𝔮 hdim
  have : Algebra.FormallySmooth k 𝔮.ResidueField :=
    (Algebra.FormallySmooth.iff_isSeparableExtension k 𝔮.ResidueField).2
      (zeroDimensionalSeparableResidue k Λ 𝔮 hdim)
  have : IsScalarTower k (Localization.AtPrime 𝔮) 𝔮.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let e₁ : Localization.AtPrime 𝔮 ≃ₐ[k] 𝔮.ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom k (Localization.AtPrime 𝔮) 𝔮.ResidueField)
      (bijective_quotient_mk_of_eq_bot hmaxQ)
  let e₂ : Localization.AtPrime 𝔮 ≃ₐ[k] primePowerQuotient 𝔮 n :=
    AlgEquiv.ofBijective
      (IsScalarTower.toAlgHom k (Localization.AtPrime 𝔮) (primePowerQuotient 𝔮 n))
      (bijective_quotient_mk_of_eq_bot (map_pow_eq_bot_of_ringKrullDim_eq_zero k 𝔮 hdim hn))
  exact Algebra.FormallySmooth.of_equiv (e₁.symm.trans e₂)

/-- Every nonzero polynomial in no variables is a unit. -/
private theorem isUnit_of_ne_zero_of_isEmpty {σ k : Type*} [Field k] [IsEmpty σ]
    (x : MvPolynomial σ k) (hx : x ≠ 0) : IsUnit x := by
  obtain ⟨c, rfl⟩ := MvPolynomial.C_surjective σ x
  exact (isUnit_iff_ne_zero.mpr (by simpa using hx)).map MvPolynomial.C

/-- Every prime of a polynomial ring in no variables over a field is zero. -/
private theorem eq_bot_of_isEmpty {σ k : Type*} [Field k] [IsEmpty σ] (𝔭 : Ideal (MvPolynomial σ k))
    [𝔭.IsPrime] : 𝔭 = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  by_contra hne
  exact ‹𝔭.IsPrime›.ne_top
    (Ideal.eq_top_of_isUnit_mem _ hx (isUnit_of_ne_zero_of_isEmpty x (by simpa using hne)))

/-- For a prime `𝔭` of a polynomial ring in no variables and `n ≥ 1`, `𝔭^n k[y]_𝔭 = 0`. -/
private theorem map_pow_eq_bot_of_isEmpty {σ k : Type*} [Field k] [IsEmpty σ]
    (𝔭 : Ideal (MvPolynomial σ k)) [𝔭.IsPrime] {n : ℕ} (hn : 1 ≤ n) :
    Ideal.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime 𝔭)) (𝔭 ^ n) = ⊥ := by
  have hpow : 𝔭 ^ n = ⊥ := by rw [eq_bot_of_isEmpty 𝔭, Ideal.bot_pow (by omega)]
  rw [hpow, Ideal.map_bot]

/-- For a prime `𝔭` of a polynomial ring in no variables over `k` and `n ≥ 1`, the structure map
`k → k[y]_𝔭/𝔭^n` is bijective. -/
private theorem bijective_algebraMap_primePowerQuotient_of_isEmpty {σ k : Type*} [Field k]
    [IsEmpty σ] (𝔭 : Ideal (MvPolynomial σ k)) [𝔭.IsPrime] {n : ℕ} (hn : 1 ≤ n) :
    Function.Bijective (algebraMap k (primePowerQuotient 𝔭 n)) := by
  rw [IsScalarTower.algebraMap_eq k (Localization.AtPrime 𝔭) (primePowerQuotient 𝔭 n),
    IsScalarTower.algebraMap_eq k (MvPolynomial σ k) (Localization.AtPrime 𝔭),
    Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq, RingHom.coe_comp, RingHom.coe_comp]
  exact (bijective_quotient_mk_of_eq_bot (map_pow_eq_bot_of_isEmpty 𝔭 hn)).comp
    ((bijective_algebraMap_atPrime 𝔭 (eq_bot_of_isEmpty 𝔭) isUnit_of_ne_zero_of_isEmpty).comp
      ⟨MvPolynomial.C_injective σ k, MvPolynomial.C_surjective σ⟩)

/-- A formally smooth extension of fields `u : F → K` factors through the subfield `F(E)` of `K`
generated by a finite set `E`, as an essentially smooth map followed by a flat inclusion. -/
private theorem exists_subring_factorization_of_formallySmooth {F K : Type u} [Field F] [Field K]
    (u : F →+* K) (hu : u.FormallySmooth) (E : Finset K) :
    ∃ (D : Subring K) (a : F →+* D), D.subtype.comp a = u ∧ (∀ e ∈ E, e ∈ D) ∧
      ∃ (_ : IsLocalRing D) (_ : IsArtinianRing D), a.IsEssentiallySmooth ∧ D.subtype.Flat := by
  let : Algebra F K := u.toAlgebra
  have hua : algebraMap F K = u := RingHom.algebraMap_toAlgebra u
  have : Algebra.FormallySmooth F K := hu.toAlgebra
  have : Algebra.IsSeparableExtension F K :=
    (Algebra.FormallySmooth.iff_isSeparableExtension _ _).1 this
  let L : IntermediateField F K := IntermediateField.adjoin F (E : Set K)
  let D : Subring K := L.toSubalgebra.toSubring
  let : Field ↥D := inferInstanceAs (Field ↥L)
  let : Algebra F ↥D := inferInstanceAs (Algebra F ↥L)
  -- `F → D` is essentially smooth: `D/F` is finitely generated and separable
  have : Algebra.EssFiniteType F ↥L :=
    IntermediateField.essFiniteType_iff.mpr (IntermediateField.fg_adjoin_of_finite E.finite_toSet)
  have hES : (algebraMap F ↥L).IsEssentiallySmooth := by
    refine ⟨isEssentiallyOfFinitePresentation_of_essFiniteType, ?_⟩
    rw [toAlgebra_algebraMap]
    exact (Algebra.FormallySmooth.iff_isSeparableExtension _ _).2
      (isSeparableExtension_of_algHom L.val)
  exact ⟨D, (algebraMap F ↥L : F →+* ↥D), RingHom.ext fun _ => by rw [← hua]; rfl,
    fun e he => Subalgebra.mem_toSubring.mpr
      (IntermediateField.subset_adjoin _ _ (Finset.mem_coe.mpr he)),
    -- `D → K` is flat, `K` being a vector space over the field `D`
    inferInstance, inferInstance, hES, flat_ringHom_of_field D.subtype⟩

/-- If `k → F` is bijective and `u : F → K` is compatible with the structure maps, then `u` is
formally smooth as soon as `K` is formally smooth over `k`. -/
private theorem formallySmooth_of_bijective_algebraMap {k F K : Type u} [CommRing k] [CommRing F]
    [CommRing K] [Algebra k F] [Algebra k K] [Algebra.FormallySmooth k K] (u : F →+* K)
    (hu : ∀ c, u (algebraMap k F c) = algebraMap k K c)
    (hk : Function.Bijective (algebraMap k F)) : u.FormallySmooth := by
  let ek : k ≃+* F := RingEquiv.ofBijective _ hk
  have hcomp : u = (algebraMap k K).comp ek.symm.toRingHom := RingHom.ext fun x => by
    show u x = algebraMap k K (ek.symm x)
    rw [← hu]
    exact congrArg u (ek.apply_symm_apply x).symm
  rw [hcomp]
  exact RingHom.FormallySmooth.respectsIso.2 _ _ (RingHom.formallySmooth_algebraMap.mpr ‹_›)

/-- **The `dim Λ_𝔮 = 0` case of Stacks 07FT.** Let `k` be a field, let `Λ` be a Noetherian
geometrically regular `k`-algebra, let `𝔮` be a prime of `Λ` with `dim Λ_𝔮 = 0`, let `n ≥ 1` and
let `E` be a finite subset of `Λ̄ = Λ_𝔮/𝔮^nΛ_𝔮`. Then the Artinian approximation data of
`Stacks.Smoothing.ArtinianApproximationDataAt` exist.

THE ADDED HYPOTHESIS IS `ringKrullDim (Localization.AtPrime 𝔮) = 0`; the general case of Stacks
07FT is open in this repository (see `Stacks.Smoothing.HasArtinianApproximationData`), and this
theorem carries no `@[stacks 07FT]` tag because a special case is not the tag.

Why the zero-dimensional case avoids the difficulty of the general one. In general the source
must choose an approximating subring `D ⊆ Λ̄` drawn from the directed family of Stacks 07FG,
together with a coefficient field for it over which the λ-choice of Stacks 07FH is available;
that choice is what is unjustified as written, and clause (3) `E ⊆ D` pulls against the essential
smoothness of `k[y]_𝔭/𝔭^n → D` demanded by clause (2). When `dim Λ_𝔮 = 0` the regular local ring
`Λ_𝔮` has maximal ideal `(0)`, so it is a field, `𝔮^nΛ_𝔮 = 0` for every `n ≥ 1` and
`Λ̄ = Λ_𝔮 = κ(𝔮)`. The residue field extension `κ(𝔮)/k` is then automatically separable —
`Stacks.Smoothing.zeroDimensionalSeparableResidue` — so no approximation and no choice of
coefficient field is needed: one may take `m = 0`, whence `k[y_1, …, y_m] = k`, `𝔭 = (0)`,
`k[y]_𝔭/𝔭^n = k`, and for `D` the subfield `k(E)` of `κ(𝔮)` generated by the finitely many
elements of `E`. That is a finitely generated subextension of the separable extension `κ(𝔮)/k`,
hence separable, hence formally smooth (Stacks 0321), and essentially of finite type, hence
essentially smooth; and `D → Λ̄` is flat because `Λ̄` is a vector space over the field `D`. -/
theorem artinianApproximationDataAt_of_ringKrullDim_eq_zero (k Λ : Type u) [Field k] [CommRing Λ]
    [Algebra k Λ] [IsNoetherianRing Λ] [Algebra.IsGeometricallyRegular k Λ] (𝔮 : Ideal Λ)
    [𝔮.IsPrime] (hdim : ringKrullDim (Localization.AtPrime 𝔮) = 0) {n : ℕ} (hn : 1 ≤ n)
    (E : Finset (primePowerQuotient 𝔮 n)) :
    ArtinianApproximationDataAt k Λ 𝔮 n E := by
  classical
  -- `Λ_𝔮` is a regular local ring of dimension zero, hence a field; the ideal `𝔮^nΛ_𝔮` vanishes,
  -- so `Λ̄ = Λ_𝔮`; and `κ(𝔮) = Λ̄` is separable over `k`, hence formally smooth over `k`
  have := formallySmooth_primePowerQuotient_of_ringKrullDim_eq_zero k 𝔮 hdim hn
  let : Field (primePowerQuotient 𝔮 n) :=
    (isField_primePowerQuotient_of_ringKrullDim_eq_zero k 𝔮 hdim hn).toField
  -- the source side: `m = 0`, so `k[y_1, …, y_m] = k`
  let φ : MvPolynomial (Fin 0) k →ₐ[k] Λ := MvPolynomial.aeval fun _ => 0
  have h𝔭 : Ideal.comap φ.toRingHom 𝔮 = ⊥ := eq_bot_of_isEmpty _
  let eP : MvPolynomial (Fin 0) k ≃+* Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮) :=
    RingEquiv.ofBijective _ (bijective_algebraMap_atPrime _ h𝔭 isUnit_of_ne_zero_of_isEmpty)
  let : Field (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)) :=
    (MulEquiv.isField (isField_of_forall_isUnit isUnit_of_ne_zero_of_isEmpty)
      eP.symm.toMulEquiv).toField
  let eF : Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮) ≃+*
      primePowerQuotient (Ideal.comap φ.toRingHom 𝔮) n :=
    RingEquiv.ofBijective _ (bijective_quotient_mk_of_eq_bot (map_pow_eq_bot_of_isEmpty _ hn))
  let : Field (primePowerQuotient (Ideal.comap φ.toRingHom 𝔮) n) :=
    (MulEquiv.isField (Field.toIsField _) eF.symm.toMulEquiv).toField
  -- the flat map `g : k[y]_𝔭 → Λ_𝔮`, which is a map of fields
  let g : Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮) →+* Localization.AtPrime 𝔮 :=
    (algebraMap Λ (Localization.AtPrime 𝔮)).comp
      (φ.toRingHom.comp (eP.symm : Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮) →+*
        MvPolynomial (Fin 0) k))
  have hgφ : ∀ f, g (algebraMap (MvPolynomial (Fin 0) k)
        (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)) f)
      = algebraMap Λ (Localization.AtPrime 𝔮) (φ f) := fun f =>
    congrArg (fun x => algebraMap Λ (Localization.AtPrime 𝔮) (φ x)) (eP.symm_apply_apply f)
  -- the induced map `u : k[y]_𝔭/𝔭^n → Λ̄`, an extension of fields
  let u : primePowerQuotient (Ideal.comap φ.toRingHom 𝔮) n →+* primePowerQuotient 𝔮 n :=
    (Ideal.Quotient.mk (Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) (𝔮 ^ n))).comp
      (g.comp (eF.symm : primePowerQuotient (Ideal.comap φ.toRingHom 𝔮) n →+*
        Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)))
  have hu : ∀ y, u (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin 0) k)
          (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)))
          (Ideal.comap φ.toRingHom 𝔮 ^ n)) y)
      = Ideal.Quotient.mk (Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) (𝔮 ^ n)) (g y) :=
    fun y => congrArg (fun x => Ideal.Quotient.mk
      (Ideal.map (algebraMap Λ (Localization.AtPrime 𝔮)) (𝔮 ^ n)) (g x)) (eF.symm_apply_apply y)
  -- `u` is a `k`-algebra map and `k → k[y]_𝔭/𝔭^n` is bijective
  have hualg : ∀ c : k, u (algebraMap k (primePowerQuotient (Ideal.comap φ.toRingHom 𝔮) n) c)
      = algebraMap k (primePowerQuotient 𝔮 n) c := fun c => by
    rw [IsScalarTower.algebraMap_apply k (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮))
        (primePowerQuotient (Ideal.comap φ.toRingHom 𝔮) n), Ideal.Quotient.algebraMap_eq, hu,
      IsScalarTower.algebraMap_apply k (MvPolynomial (Fin 0) k)
        (Localization.AtPrime (Ideal.comap φ.toRingHom 𝔮)), hgφ, φ.commutes,
      ← IsScalarTower.algebraMap_apply k Λ (Localization.AtPrime 𝔮),
      IsScalarTower.algebraMap_apply k (Localization.AtPrime 𝔮) (primePowerQuotient 𝔮 n),
      Ideal.Quotient.algebraMap_eq]
  -- `Λ̄` as an extension of `F = k[y]_𝔭/𝔭^n`, and the subfield `D = F(E) = k(E)`
  obtain ⟨D, a, hDa, hED, h₁, h₂, hES, hDflat⟩ := exists_subring_factorization_of_formallySmooth u
    (formallySmooth_of_bijective_algebraMap u hualg
      (bijective_algebraMap_primePowerQuotient_of_isEmpty _ hn)) E
  refine ⟨0, φ, g, u, D, a, ?_, hgφ, flat_ringHom_of_field g, hu, hDa, hED, inferInstance,
    inferInstance, inferInstance, inferInstance, h₁, h₂, hES, hDflat⟩
  rw [h𝔭, Ideal.map_bot, IsLocalization.AtPrime.map_eq_maximalIdeal 𝔮 (Localization.AtPrime 𝔮),
    maximalIdeal_atPrime_eq_bot_of_ringKrullDim_eq_zero k 𝔮 hdim]

end Stacks.Smoothing

end
