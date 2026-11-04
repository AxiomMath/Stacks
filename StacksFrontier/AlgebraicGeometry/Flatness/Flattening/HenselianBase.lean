module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.HenselianQuotientStep
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.HenselianSquareZeroStep
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.PolynomialLocalizationReduction
public import StacksFrontier.RingTheory.Flat.FibreCriterionNilpotent
public import StacksFrontier.RingTheory.Flat.HenselianFlatteningTheorem
public import StacksFrontier.RingTheory.Flat.LocalCriterionEssFP

/-!
# Situation 0AT0 over a henselian base

Let `A → B` be a local homomorphism of local rings which is essentially of finite type, `M` a flat
`A`-module, `N` a finite `B`-module and `u : N → M` an `A`-linear map whose reduction
`N/𝔪_A N → M/𝔪_A M` is injective. If `A` is henselian, then `u` is `A`-universally injective,
`N` is of finite presentation over `B`, and `N` is flat over `A` (Stacks 0AT3).

The proof is the source's. By Stacks 0AT2 it suffices to treat `B` a localization of a polynomial
algebra over `A` and `N` finitely presented over `B`. If `N` is flat over `A`, Stacks 05U7 writes
`N` as a filtered colimit of free `A`-modules with transition maps injective modulo `𝔪_A`, and
Stacks 05FQ makes `u` universally injective
(`AlgebraicGeometry.universallyInjective_of_henselian_of_flat`). In general Stacks 05PG gives a
finitely generated ideal `I ⊆ 𝔪_A` with `N/IN` flat over `A/I` and `N/I²N` flat over `A/I²` only
if `I = 0`; the flat case over `A/I` makes `u mod I` universally injective, and the square-zero
local criterion (Stacks 051C) then makes `N/I²N` flat over `A/I²`, so `I = 0`.

## Main results

* `AlgebraicGeometry.exists_fg_flat_quotient_of_henselian`: the ideal of Stacks 05PG, read in
  Situation 0AT0.
* `AlgebraicGeometry.flat_quotient_sq_of_rTensor_mapQ_injective`: the square-zero step, over
  `A ⧸ I²`.
* `AlgebraicGeometry.flat_of_henselian_of_essentiallyOfFinitePresentation`: flatness of `N` when
  `B` is essentially of finite presentation and `N` finitely presented.
* `AlgebraicGeometry.injectiveModuloMaximalIdealConclusion_of_henselianLocalRing`:
  **Stacks 0AT3**.

## Implementation notes

The three conclusions are the conjunction `AlgebraicGeometry.InjectiveModuloMaximalIdealConclusion`
used by the reduction of Stacks 0AT2, with universal injectivity tested against modules in an
arbitrary universe. The reduction modulo an ideal `J` is the quotient by `J • ⊤` and the reduced
map is `Submodule.mapQ`, as in the bundle of Situation 0AT0.

## References

* [Stacks Project, Tag 0AT0](https://stacks.math.columbia.edu/tag/0AT0)
* [Stacks Project, Tag 0AT2](https://stacks.math.columbia.edu/tag/0AT2)
* [Stacks Project, Tag 0AT3](https://stacks.math.columbia.edu/tag/0AT3)
* [Stacks Project, Tag 05PG](https://stacks.math.columbia.edu/tag/05PG)
* [Stacks Project, Tag 05U7](https://stacks.math.columbia.edu/tag/05U7)
* [Stacks Project, Tag 051C](https://stacks.math.columbia.edu/tag/051C)
-/

@[expose] public section

open IsLocalRing TensorProduct

universe u v w u₁ u₂ u₃ u₄ u₅

namespace AlgebraicGeometry

/-! ### The local flattening ideal of the source module -/

/-- Flatness of `N ⧸ J N` over `A ⧸ J` does not depend on which of two equal `A`-module structures
on `N` is used to form `J N`. -/
private theorem flat_quotient_smul_top_congr {A N : Type*} [CommRing A] [AddCommGroup N]
    (i₁ i₂ : Module A N) (h : i₁ = i₂) (J : Ideal A) :
    (letI := i₁; Module.Flat (A ⧸ J) (N ⧸ (J • ⊤ : Submodule A N))) ↔
      (letI := i₂; Module.Flat (A ⧸ J) (N ⧸ (J • ⊤ : Submodule A N))) := by
  subst h
  rfl

/-- **The flattening ideal of Stacks 05PG, read in Situation 0AT0.** Over a henselian base, with
`B` essentially of finite presentation over `A` and `N` finitely presented over `B`, there is a
finitely generated ideal `I ⊆ 𝔪_A` such that `N ⧸ I N` is flat over `A ⧸ I`, and such that
`N ⧸ I² N` is flat over `A ⧸ I²` only if `I = 0`. -/
theorem exists_fg_flat_quotient_of_henselian
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄}) [HenselianLocalRing S.A]
    (hB : (algebraMap S.A S.B).EssentiallyOfFinitePresentation)
    (hN : Module.FinitePresentation S.B S.N) :
    ∃ I : Ideal S.A, I ≤ maximalIdeal S.A ∧
      Module.Flat (S.A ⧸ I) (S.N ⧸ (I • ⊤ : Submodule S.A S.N)) ∧
      (Module.Flat (S.A ⧸ I ^ 2) (S.N ⧸ (I ^ 2 • ⊤ : Submodule S.A S.N)) → I = ⊥) := by
  let F : Module.FlatAtPointSituation.{u₁, u₂, u₄} := { A := S.A, B := S.B, M := S.N }
  have : Algebra.EssFiniteType F.A F.B := S.essentiallyFiniteType
  have : Module.Finite F.B F.M := S.finiteN
  obtain ⟨I, hI, hfg⟩ :=
    Module.FlatAtPointSituation.exists_ideal_condition_iff_map_eq_bot_of_henselian.{u₁, u₂, u₄, u₁}
      F
  have hfl : ∀ J : Ideal S.A, F.Flattens J ↔ I ≤ J :=
    Module.FlatAtPointSituation.flattens_iff_le_of_condition_iff.{u₁, u₂, u₄, u₁} hI
  have hmod : Module.FlatAtPointSituation.moduleAM F = S.moduleAN :=
    Module.ext' _ _ fun a x ↦ (IsScalarTower.algebraMap_smul S.B a x : _)
  have hflat : ∀ J : Ideal S.A,
      Module.Flat (S.A ⧸ J) (S.N ⧸ (J • ⊤ : Submodule S.A S.N)) ↔ I ≤ J := fun J ↦
    ((flat_quotient_smul_top_congr _ _ hmod J).symm.trans
      (F.flattens_iff_flat_quotient J).symm).trans (hfl J)
  have hIm : I ≤ maximalIdeal S.A := (hfl _).mp F.flattens_maximalIdeal
  refine ⟨I, hIm, (hflat I).mpr le_rfl, fun h2 ↦ ?_⟩
  refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal S.A) I (hfg hB hN) ?_
    (maximalIdeal_le_jacobson ⊥)
  calc I ≤ I ^ 2 := (hflat _).mp h2
    _ = I * I := pow_two I
    _ ≤ maximalIdeal S.A * I := Ideal.mul_mono_left hIm

/-! ### The square-zero step over `A ⧸ I²` -/

/-- A module over a quotient `R'` of `R` tensors over `R'` exactly as over `R`: for `r' ∈ R'`
the element `(r' • p) ⊗ q` of `P ⊗[R] Q` is `p ⊗ (r' • q)`. -/
private theorem compatibleSMul_of_surjective {R R' : Type*} [CommRing R] [CommRing R']
    [Algebra R R'] (hR : Function.Surjective (algebraMap R R'))
    (P Q : Type*) [AddCommGroup P] [Module R' P] [Module R P] [IsScalarTower R R' P]
    [AddCommGroup Q] [Module R' Q] [Module R Q] [IsScalarTower R R' Q] :
    TensorProduct.CompatibleSMul R R' P Q := by
  refine ⟨fun r' p q ↦ ?_⟩
  obtain ⟨r, rfl⟩ := hR r'
  rw [algebraMap_smul, algebraMap_smul, TensorProduct.smul_tmul]

/-- Along a surjection `R → R'`, a map of `R'`-modules stays injective after tensoring over `R'`
with an `R'`-module `Q` as soon as it does after tensoring with `Q` over `R`. -/
private theorem rTensor_injective_of_restrictScalars {R R' : Type*} [CommRing R] [CommRing R']
    [Algebra R R'] (hR : Function.Surjective (algebraMap R R'))
    {X Y Q : Type*} [AddCommGroup X] [Module R' X] [Module R X] [IsScalarTower R R' X]
    [AddCommGroup Y] [Module R' Y] [Module R Y] [IsScalarTower R R' Y]
    [AddCommGroup Q] [Module R' Q] [Module R Q] [IsScalarTower R R' Q]
    (f : X →ₗ[R'] Y) (h : Function.Injective ((f.restrictScalars R).rTensor Q)) :
    Function.Injective (f.rTensor Q) := by
  have := compatibleSMul_of_surjective hR X Q
  have := compatibleSMul_of_surjective hR Y Q
  let eX := TensorProduct.equivOfCompatibleSMul R R' R' X Q
  let eY := TensorProduct.equivOfCompatibleSMul R R' R' Y Q
  have hsq : ∀ x : X ⊗[R'] Q, eY (f.rTensor Q x) = (f.restrictScalars R).rTensor Q (eX x) := by
    intro x
    induction x with
    | zero => simp
    | tmul x q => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  intro x y hxy
  apply eX.injective
  apply h
  rw [← hsq, ← hsq, hxy]

/-- Every element of an iterated submodule quotient is the class of an element of `N`. -/
private theorem exists_mk_mk {R S N : Type*} [Ring R] [Ring S] [AddCommGroup N] [Module R N]
    {P : Submodule R N} [Module S (N ⧸ P)] {Q : Submodule S (N ⧸ P)} (x : (N ⧸ P) ⧸ Q) :
    ∃ n : N, Submodule.Quotient.mk (Submodule.Quotient.mk n) = x := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨n, rfl⟩

/-- The double quotient `(N ⧸ I² N) ⧸ (I ⧸ I²)(N ⧸ I² N)` is `N ⧸ I N`, as `A`-modules. -/
private def quotQuotSqEquiv {A : Type*} [CommRing A] (I : Ideal A) (N : Type*) [AddCommGroup N]
    [Module A N] :
    ((N ⧸ (I ^ 2 • ⊤ : Submodule A N)) ⧸
      (I.map (algebraMap A (A ⧸ I ^ 2)) • ⊤ :
        Submodule (A ⧸ I ^ 2) (N ⧸ (I ^ 2 • ⊤ : Submodule A N))))
      ≃ₗ[A] N ⧸ (I • ⊤ : Submodule A N) :=
  let N' := N ⧸ (I ^ 2 • ⊤ : Submodule A N)
  have hle : (I ^ 2 • ⊤ : Submodule A N) ≤ I • ⊤ :=
    Submodule.smul_mono_left (Ideal.pow_le_self two_ne_zero)
  have hset : ((I.map (algebraMap A (A ⧸ I ^ 2)) • ⊤ : Submodule (A ⧸ I ^ 2) N') : Set N') =
      (((I • ⊤ : Submodule A N).map (I ^ 2 • ⊤ : Submodule A N).mkQ : Submodule A N') :
        Set N') := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
    exact Stacks.Flatness.FibrewiseCriterionEssFP.coe_map_smul_top (R := A) (A := A ⧸ I ^ 2)
      (M := N') I
  let φ := (Stacks.Flatness.FibrewiseCriterionEssFP.quotAddEquivOfCoeEq _ _ hset).trans
    (Submodule.quotientQuotientEquivQuotient _ _ hle).toAddEquiv
  { φ with
    map_smul' := fun a x ↦ by
      obtain ⟨x, rfl⟩ := exists_mk_mk x
      rfl }

private theorem quotQuotSqEquiv_mk_mk {A : Type*} [CommRing A] (I : Ideal A) {N : Type*}
    [AddCommGroup N] [Module A N] (n : N) :
    quotQuotSqEquiv I N (Submodule.Quotient.mk (Submodule.Quotient.mk n)) =
      Submodule.Quotient.mk n :=
  rfl

/-- **The square-zero step of the proof of Stacks 0AT3, over the base ring.** Let `I ⊆ A` be an
ideal, `M` a flat `A`-module and `u : N → M` an `A`-linear map. If `N ⧸ I N` is flat over `A ⧸ I`
and the reduction `ū : N ⧸ I N → M ⧸ I M` stays injective after tensoring over `A` with any
`A`-module, then `N ⧸ I² N` is flat over `A ⧸ I²`.

This is `AlgebraicGeometry.flat_of_sqZero_of_universallyInjective_mapQ` for the ring `A ⧸ I²` and
its square-zero ideal `I ⧸ I²`, whose quotient of `N ⧸ I² N` is `N ⧸ I N`. -/
theorem flat_quotient_sq_of_rTensor_mapQ_injective
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M] [Module.Flat A M]
    {N : Type w} [AddCommGroup N] [Module A N] (I : Ideal A) (u : N →ₗ[A] M)
    (hquot : Module.Flat (A ⧸ I) (N ⧸ (I • ⊤ : Submodule A N)))
    (hui : ∀ (Q : Type u) [AddCommGroup Q] [Module A Q],
      Function.Injective ((Submodule.mapQ (I • ⊤ : Submodule A N) (I • ⊤ : Submodule A M) u
        (Submodule.smul_top_le_comap_smul_top I u)).rTensor Q)) :
    Module.Flat (A ⧸ I ^ 2) (N ⧸ (I ^ 2 • ⊤ : Submodule A N)) := by
  let S := A ⧸ I ^ 2
  let N' := N ⧸ (I ^ 2 • ⊤ : Submodule A N)
  let M' := M ⧸ (I ^ 2 • ⊤ : Submodule A M)
  have hsurj : Function.Surjective (algebraMap A S) := Ideal.Quotient.mk_surjective
  let u' : N' →ₗ[S] M' :=
    (Submodule.mapQ _ _ u
      (Submodule.smul_top_le_comap_smul_top (I ^ 2) u)).extendScalarsOfSurjective hsurj
  let J : Ideal S := I.map (algebraMap A S)
  have hJ : J ^ 2 = ⊥ := by
    rw [← Ideal.map_pow]
    exact Ideal.map_quotient_self (I ^ 2)
  have : Module.Flat S M' := Module.Flat.quotient_smul_top (I ^ 2)
  let ū := Submodule.mapQ (I • ⊤ : Submodule A N) (I • ⊤ : Submodule A M) u
    (Submodule.smul_top_le_comap_smul_top I u)
  let φN := quotQuotSqEquiv I N
  let φM := quotQuotSqEquiv I M
  have hquot' : Module.Flat (S ⧸ J) (N' ⧸ (J • ⊤ : Submodule S N')) := by
    refine Stacks.Flatness.EssFPLocalCriterion.flat_of_ringEquiv_of_addEquiv
      (DoubleQuot.quotQuotEquivQuotOfLE (Ideal.pow_le_self two_ne_zero)) φN.toAddEquiv ?_
    intro r x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨x, rfl⟩ := exists_mk_mk x
    rfl
  refine flat_of_sqZero_of_universallyInjective_mapQ J hJ u' hquot' fun Q _ _ ↦ ?_
  let : Module A Q := Module.compHom Q (algebraMap A S)
  have : IsScalarTower A S Q := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  refine rTensor_injective_of_restrictScalars hsurj _ ?_
  have hfac : (Submodule.mapQ (J • ⊤ : Submodule S N') (J • ⊤ : Submodule S M') u'
      (Submodule.smul_top_le_comap_smul_top J u')).restrictScalars A =
      φM.symm.toLinearMap ∘ₗ ū ∘ₗ φN.toLinearMap := by
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨x, rfl⟩ := exists_mk_mk x
    apply φM.injective
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.apply_symm_apply]
    rfl
  rw [hfac, LinearMap.rTensor_comp, LinearMap.rTensor_comp, LinearMap.coe_comp,
    LinearMap.coe_comp]
  exact (φM.symm.rTensor Q).injective.comp ((hui Q).comp (φN.rTensor Q).injective)

/-! ### The henselian case -/

/-- Henselianness of the base ring transports along an equality of rings. -/
private theorem transportHenselianLocalRing {X Y : Type u₁} [rx : CommRing X] [ry : CommRing Y]
    (h : X = Y) (hh : HEq rx ry) (hX : HenselianLocalRing X) : HenselianLocalRing Y := by
  subst h
  cases hh
  exact hX

/-- A henselian base ring transports across `SameBaseLocalRing`. -/
theorem SameBaseLocalRing.henselianLocalRing {S T : InjectiveModuloMaximalIdealSituation}
    (h : SameBaseLocalRing S T) (hS : HenselianLocalRing S.A) : HenselianLocalRing T.A := by
  obtain ⟨hA, hR⟩ := h
  exact transportHenselianLocalRing (rx := S.commRingA) (ry := T.commRingA) hA hR hS

/-- **Flatness in the henselian case, for `B` essentially of finite presentation and `N` finitely
presented.** This is the second paragraph of the proof of Stacks 0AT3: the ideal `I` of Stacks
05PG has `N ⧸ I N` flat over `A ⧸ I`; the first paragraph over `A ⧸ I` makes the reduction of `u`
universally injective, so `N ⧸ I² N` is flat over `A ⧸ I²`, which forces `I = 0`. -/
theorem flat_of_henselian_of_essentiallyOfFinitePresentation
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄}) [HenselianLocalRing S.A]
    (hB : (algebraMap S.A S.B).EssentiallyOfFinitePresentation)
    (hN : Module.FinitePresentation S.B S.N) : Module.Flat S.A S.N := by
  obtain ⟨I, hIm, hflat, hsq⟩ := exists_fg_flat_quotient_of_henselian S hB hN
  obtain rfl : I = ⊥ := hsq (flat_quotient_sq_of_rTensor_mapQ_injective I S.u hflat
    (rTensor_mapQ_injective_of_henselian_of_flat_quotient.{u₁, u₂, u₃, u₄, u₁} S I hIm hflat))
  exact Stacks.Flatness.EssFPLocalCriterion.flat_of_ringEquiv_of_addEquiv
    (RingEquiv.quotientBot S.A).symm
    (Submodule.quotEquivOfEqBot ((⊥ : Ideal S.A) • (⊤ : Submodule S.A S.N))
      (Submodule.bot_smul ⊤)).symm.toAddEquiv fun _ _ ↦ rfl

/-- **Stacks Project, Tag 0AT3.** In Situation 0AT0 with `A` henselian the lemma holds: if
`A → B` is a local homomorphism of local rings essentially of finite type, `M` is a flat
`A`-module, `N` is a finite `B`-module and `u : N → M` is an `A`-linear map whose reduction
`N/𝔪_A N → M/𝔪_A M` is injective, then `u` is `A`-universally injective, `N` is of finite
presentation over `B`, and `N` is flat over `A`. -/
@[stacks 0AT3]
theorem injectiveModuloMaximalIdealConclusion_of_henselianLocalRing
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄}) [HenselianLocalRing S.A] :
    InjectiveModuloMaximalIdealConclusion.{u₅} S := by
  have h : ∀ (T : InjectiveModuloMaximalIdealSituation.{u₁, max u₁ u₂, u₃, max u₁ u₂ u₄}),
      SameBaseLocalRing S T → PolynomialLocalizationPresentation T.A T.B →
        Module.FinitePresentation T.B T.N →
          InjectiveModuloMaximalIdealConclusion.{max u₁ u₅} T := by
    intro T hST P hN
    have : HenselianLocalRing T.A := hST.henselianLocalRing ‹_›
    have hB : (algebraMap T.A T.B).EssentiallyOfFinitePresentation := by
      let := P.polynomialAlgebra
      have := P.scalarTower
      have := P.prime_isPrime
      have := P.isLocalization
      exact RingHom.EssentiallyOfFinitePresentation.of_isLocalization
        (C := MvPolynomial (Fin P.variableCount) T.A) P.prime.primeCompl
    have := flat_of_henselian_of_essentiallyOfFinitePresentation T hB hN
    exact ⟨universallyInjective_of_henselian_of_flat T, hN, inferInstance⟩
  exact ⟨universallyInjective_of_localizedPolynomial_cases S h,
    finitePresentation_of_localizedPolynomial_cases S h, flat_of_localizedPolynomial_cases S h⟩

end AlgebraicGeometry

end
