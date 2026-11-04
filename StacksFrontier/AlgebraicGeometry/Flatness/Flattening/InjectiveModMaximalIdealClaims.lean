module

public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.MaximalIdealResidueFibre
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.NilpotentIdealUniversalInjectivity
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.PolynomialLocalizationReduction
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.PureSpreadoutQuotient

/-!
# The two claims of the proof of Stacks 05U9

The proof of Stacks 05U9 in the source reduces, through Stacks 0AT2, to the case where the local
algebra `B` is the localization of a polynomial algebra over `A` at a prime and the module `N` is
of finite presentation over `B`, and then establishes two claims about that case:

* **Claim 1**: there is a nilpotent ideal `I ⊆ A` such that `N / IN` is flat over `A / I`; and
* **Claim 2**: for every prime `𝔭 ⊆ A` the map `u ⊗ id_{κ(𝔭)}` is injective.

This file proves that the two claims together give all three conclusions of Stacks 05U9. The
input used from the repository is Stacks 0AT2 (the reduction), Stacks 0AT9 (fibrewise injectivity
gives universal injectivity for a flat module in the finitely presented localized situation) and
the nilpotent-ideal reduction of
`Module.Flat.universallyInjectivePoly_of_annihilated_of_isNilpotent`.

## Main results

* `AlgebraicGeometry.universallyInjective_baseChange_of_flat_of_fibres`: in the finitely
  presented localized situation, fibrewise injectivity passes to a base change along any
  `A`-algebra over which the base-changed module is flat.
* `AlgebraicGeometry.universallyInjective_of_isNilpotent_of_flat_quotient_of_fibres`: Claim 1 and
  Claim 2 together give universal injectivity.
* `AlgebraicGeometry.conclusion_of_claims`: the three conclusions of Stacks 05U9 in Situation
  0AT0 from the two claims in the localized-polynomial case.

## Implementation notes

Nothing here proves Stacks 05U9, and nothing here carries its tag: the two claims are hypotheses.

## References

* [Stacks Project, Tag 0AT0](https://stacks.math.columbia.edu/tag/0AT0)
* [Stacks Project, Tag 0AT2](https://stacks.math.columbia.edu/tag/0AT2)
* [Stacks Project, Tag 0AT9](https://stacks.math.columbia.edu/tag/0AT9)
* [Stacks Project, Tag 05U9](https://stacks.math.columbia.edu/tag/05U9)
-/

@[expose] public section

universe u₁ u₂ u₃ u₄ u₅

open TensorProduct

namespace AlgebraicGeometry

/-- **Universal injectivity lifts through a nilpotent ideal of the base.** If `f : N → M` has
flat target and its base change to `R ⧸ I` is universally injective for a nilpotent ideal `I`,
then `f` is universally injective. -/
theorem universallyInjective_of_isNilpotent_of_baseChange
    {R : Type u₁} [CommRing R] {N : Type u₂} {M : Type u₃}
    [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M]
    [Module.Flat R M] (f : N →ₗ[R] M) (I : Ideal R) (hI : IsNilpotent I)
    (hf : UniversallyInjectivePoly.{u₁, u₄} (f.baseChange (R ⧸ I))) :
    UniversallyInjectivePoly.{u₁, u₄} f := by
  refine Module.Flat.universallyInjectivePoly_of_annihilated_of_isNilpotent f hI ?_
  intro Q _ _ hQ
  have hkill : Module.IsTorsionBySet R Q I := fun q r => hQ r.1 r.2 q
  let : Module (R ⧸ I) Q := hkill.module
  have : IsScalarTower R (R ⧸ I) Q := hkill.isScalarTower
  exact injective_rTensor_of_universallyInjective_baseChange f (R ⧸ I) hf Q

/-- A universally injective map into a flat module has flat source. -/
theorem flat_of_universallyInjective_into_flat
    {R : Type u₁} {N : Type u₂} {M : Type u₃} [CommRing R]
    [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M]
    [Module.Flat R M] [Small.{u₄} R]
    (f : N →ₗ[R] M) (hf : UniversallyInjectivePoly.{u₁, u₄} f) :
    Module.Flat R N := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap'.{u₄, u₁, u₂}]
  intro P P' _ _ _ _ g hg
  have h : Function.Injective (f.rTensor P' ∘ g.lTensor N) := by
    rw [← LinearMap.coe_comp, LinearMap.rTensor_comp_lTensor,
      ← LinearMap.lTensor_comp_rTensor, LinearMap.coe_comp]
    exact (Module.Flat.lTensor_preserves_injective_linearMap g hg).comp (hf P)
  exact h.of_comp

/-- Injectivity on every residue-field fibre gives injectivity after tensoring with any field
over the base. -/
theorem injective_lTensor_field_of_fibres
    {R N M : Type*} [CommRing R]
    [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M]
    (f : N →ₗ[R] M)
    (hf : ∀ (p : Ideal R) [p.IsPrime], Function.Injective (f.rTensor p.ResidueField))
    (K : Type*) [Field K] [Algebra R K] : Function.Injective (f.lTensor K) := by
  let p : Ideal R := RingHom.ker (algebraMap R K)
  have : p.IsPrime := RingHom.ker_isPrime (algebraMap R K)
  exact injective_lTensor_field_of_fibre f K p rfl (hf p)

/-- Precomposing with a linear equivalence does not change injectivity of `rTensor`. -/
private theorem injective_rTensor_comp_equiv_iff
    {R P N M : Type*} [CommRing R] [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] (g : N →ₗ[R] M) (e : P ≃ₗ[R] N)
    (Q : Type*) [AddCommGroup Q] [Module R Q] :
    Function.Injective ((g ∘ₗ e.toLinearMap).rTensor Q) ↔ Function.Injective (g.rTensor Q) := by
  rw [LinearMap.rTensor_comp]
  exact Function.Injective.of_comp_iff' _ (e.rTensor Q).bijective

/-- **Fibrewise injectivity survives a base change.** In the finitely presented localized
situation, if `f` is injective on every residue-field fibre of `R` and the base change of `N`
to an `R`-algebra `S` is `S`-flat, then `f ⊗ id_S` is universally injective over `S`. -/
theorem universallyInjective_baseChange_of_flat_of_fibres
    {R B₀ B N M : Type*} [CommRing R] [CommRing B₀] [CommRing B]
    [Algebra R B₀] [Algebra B₀ B] [Algebra R B] [IsScalarTower R B₀ B]
    [Algebra.FinitePresentation R B₀] (W : Submonoid B₀) [IsLocalization W B]
    [AddCommGroup N] [Module B N] [Module R N] [IsScalarTower R B N]
    [Module.FinitePresentation B N]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    (f : N →ₗ[R] M)
    (hf : ∀ (p : Ideal R) [p.IsPrime], Function.Injective (f.rTensor p.ResidueField))
    (S : Type*) [CommRing S] [Algebra R S] [Module.Flat S (S ⊗[R] N)] :
    UniversallyInjectivePoly.{_, u₅} (f.baseChange S) := by
  let B₀' := S ⊗[R] B₀
  let B' := S ⊗[R] B
  let g : B₀' →ₐ[S] B' :=
    Algebra.TensorProduct.map (AlgHom.id S S) (IsScalarTower.toAlgHom R B₀ B)
  let : Algebra B₀' B' := g.toRingHom.toAlgebra
  have : IsScalarTower S B₀' B' := IsScalarTower.of_algebraMap_eq' (by
    ext s
    exact (g.commutes s).symm)
  let : Algebra B B' := Algebra.TensorProduct.rightAlgebra
  let W' := W.map (Algebra.TensorProduct.includeRight (R := R) (A := S))
  have : IsLocalization W' B' :=
    IsLocalization.tensorProduct_tensorProduct_right R S W B (by
      ext b
      rfl)
  let N' := B' ⊗[B] N
  let eN : N' ≃ₗ[S] S ⊗[R] N := Algebra.IsPushout.cancelBaseChange R S B B' N
  have : Module.Flat S N' := Module.Flat.of_linearEquiv eN
  let f' := f.baseChange S ∘ₗ eN.toLinearMap
  have hf' : ∀ (p : Ideal S) [p.IsPrime], Function.Injective (f'.rTensor p.ResidueField) := by
    intro p _
    have h : Function.Injective ((f.baseChange S).lTensor p.ResidueField) :=
      (injective_lTensor_baseChange_iff f).mpr
        (injective_lTensor_field_of_fibres f hf p.ResidueField)
    exact (injective_rTensor_comp_equiv_iff _ eN _).mpr
      ((LinearMap.lTensor_inj_iff_rTensor_inj _ _).mp h)
  intro Q _ _
  have hQ := universallyInjective_of_flat_of_fibres (B₀ := B₀') (B := B') W' f' hf' Q
  exact (injective_rTensor_comp_equiv_iff _ eN _).mp hQ

/-- Flatness of `N ⧸ IN` over `R ⧸ I` read on the base change `(R ⧸ I) ⊗[R] N`. -/
theorem flat_baseChange_quotient_of_flat_quotient
    {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N] (I : Ideal R)
    [Module.Flat (R ⧸ I) (N ⧸ (I • (⊤ : Submodule R N)))] :
    Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] N) :=
  Module.Flat.of_linearEquiv
    (LinearEquiv.extendScalarsOfSurjective (S := R ⧸ I) Ideal.Quotient.mk_surjective
      (TensorProduct.quotTensorEquivQuotSMul N I))

/-- **The two claims of the proof of Stacks 05U9 give universal injectivity.** In the finitely
presented localized situation, a nilpotent ideal `I` with `N ⧸ IN` flat over `R ⧸ I` (Claim 1)
together with injectivity of `f` on every residue-field fibre (Claim 2) make `f` universally
injective. -/
theorem universallyInjective_of_isNilpotent_of_flat_quotient_of_fibres
    {R B₀ B N M : Type*} [CommRing R] [CommRing B₀] [CommRing B]
    [Algebra R B₀] [Algebra B₀ B] [Algebra R B] [IsScalarTower R B₀ B]
    [Algebra.FinitePresentation R B₀] (W : Submonoid B₀) [IsLocalization W B]
    [AddCommGroup N] [Module B N] [Module R N] [IsScalarTower R B N]
    [Module.FinitePresentation B N]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    (f : N →ₗ[R] M) (I : Ideal R) (hI : IsNilpotent I)
    [Module.Flat (R ⧸ I) (N ⧸ (I • (⊤ : Submodule R N)))]
    (hf : ∀ (p : Ideal R) [p.IsPrime], Function.Injective (f.rTensor p.ResidueField)) :
    UniversallyInjectivePoly.{_, u₅} f := by
  have := flat_baseChange_quotient_of_flat_quotient (N := N) I
  exact universallyInjective_of_isNilpotent_of_baseChange f I hI
    (universallyInjective_baseChange_of_flat_of_fibres (B := B) W f hf (R ⧸ I))

/-- **Stacks 05U9 from its two claims.** In Situation 0AT0, suppose that in every special case
singled out by Stacks 0AT2 — the local algebra a localization of a polynomial algebra over `A`
at a prime, the module finitely presented over it — the two claims of the source's proof hold:

* Claim 1: some nilpotent ideal `I ⊆ A` has `N ⧸ IN` flat over `A ⧸ I`; and
* Claim 2: `u ⊗ id_{κ(𝔭)}` is injective for every prime `𝔭` of `A`.

Then all three conclusions of Stacks 05U9 hold: `u` is `A`-universally injective, `N` is of
finite presentation over `B`, and `N` is flat over `A`. -/
theorem conclusion_of_claims
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    (hclaims : ∀ (T : InjectiveModuloMaximalIdealSituation.{u₁, max u₁ u₂, u₃, max u₁ u₂ u₄}),
      SameBaseLocalRing S T → ∀ _P : PolynomialLocalizationPresentation T.A T.B,
        Module.FinitePresentation T.B T.N →
        (∃ I : Ideal T.A, IsNilpotent I ∧
            Module.Flat (T.A ⧸ I) (T.N ⧸ (I • (⊤ : Submodule T.A T.N)))) ∧
          ∀ (p : Ideal T.A) [p.IsPrime],
            Function.Injective (T.u.rTensor p.ResidueField)) :
    UniversallyInjectivePoly.{_, u₅} S.u ∧
      Module.FinitePresentation S.B S.N ∧ Module.Flat S.A S.N := by
  have h : ∀ (T : InjectiveModuloMaximalIdealSituation.{u₁, max u₁ u₂, u₃, max u₁ u₂ u₄}),
      SameBaseLocalRing S T → PolynomialLocalizationPresentation T.A T.B →
        Module.FinitePresentation T.B T.N →
          InjectiveModuloMaximalIdealConclusion.{max u₁ u₅} T := by
    intro T hbase P hfp
    have := P.prime_isPrime
    let := P.polynomialAlgebra
    have := P.scalarTower
    have := P.isLocalization
    have := hfp
    obtain ⟨⟨I, hI, hflat⟩, hfibres⟩ := hclaims T hbase P hfp
    have := hflat
    have hu : UniversallyInjectivePoly.{_, max u₁ u₅} T.u :=
      universallyInjective_of_isNilpotent_of_flat_quotient_of_fibres
        (B := T.B) P.prime.primeCompl T.u I hI hfibres
    exact ⟨hu, hfp, flat_of_universallyInjective_into_flat T.u hu⟩
  exact ⟨universallyInjective_of_localizedPolynomial_cases S h,
    finitePresentation_of_localizedPolynomial_cases S h,
    flat_of_localizedPolynomial_cases S h⟩

/-- Situation 0AT0 read off unbundled data: a local homomorphism `A → B` of local rings which is
essentially of finite type, a flat `A`-module `M`, a finite `B`-module `N`, and an `A`-linear
`u : N → M` whose reduction modulo the maximal ideal of `A` is injective. -/
def situationOfData (A : Type u₁) (B : Type u₂) (M : Type u₃) (N : Type u₄)
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
    [AddCommGroup M] [Module A M] [Module.Flat A M]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N] [Module.Finite B N]
    (u : N →ₗ[A] M)
    (hu : Function.Injective
      (Submodule.mapQ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A N))
        (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)) u
        (Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal A) u))) :
    InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄} where
  A := A
  B := B
  M := M
  N := N
  u := u
  injective_mod_maximalIdeal := hu

/-- The map of the situation built from unbundled data is the given map. -/
@[simp]
theorem situationOfData_u (A : Type u₁) (B : Type u₂) (M : Type u₃) (N : Type u₄)
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
    [AddCommGroup M] [Module A M] [Module.Flat A M]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N] [Module.Finite B N]
    (u : N →ₗ[A] M)
    (hu : Function.Injective
      (Submodule.mapQ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A N))
        (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)) u
        (Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal A) u))) :
    (situationOfData A B M N u hu).u = u := rfl

/-- **Stacks 05U9 from its two claims, with the source's hypotheses unbundled.** The same
conclusion as `AlgebraicGeometry.conclusion_of_claims`, stated without Situation 0AT0. -/
theorem conclusion_of_claims_of_data {A : Type u₁} {B : Type u₂} {M : Type u₃} {N : Type u₄}
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
    [AddCommGroup M] [Module A M] [Module.Flat A M]
    [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N] [Module.Finite B N]
    (u : N →ₗ[A] M)
    (hu : Function.Injective
      (Submodule.mapQ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A N))
        (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)) u
        (Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal A) u)))
    (hclaims : ∀ (T : InjectiveModuloMaximalIdealSituation.{u₁, max u₁ u₂, u₃, max u₁ u₂ u₄}),
      SameBaseLocalRing (situationOfData A B M N u hu) T →
        ∀ _P : PolynomialLocalizationPresentation T.A T.B,
        Module.FinitePresentation T.B T.N →
        (∃ I : Ideal T.A, IsNilpotent I ∧
            Module.Flat (T.A ⧸ I) (T.N ⧸ (I • (⊤ : Submodule T.A T.N)))) ∧
          ∀ (p : Ideal T.A) [p.IsPrime],
            Function.Injective (T.u.rTensor p.ResidueField)) :
    UniversallyInjectivePoly.{_, u₅} u ∧
      Module.FinitePresentation B N ∧ Module.Flat A N :=
  conclusion_of_claims (situationOfData A B M N u hu) hclaims

end AlgebraicGeometry

end
