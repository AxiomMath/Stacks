module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.HenselianColimitFreeStep
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.PolynomialLocalizationReduction
public import StacksFrontier.RingTheory.Flat.FibreCriterionNilpotent
public import StacksFrontier.RingTheory.Flat.HenselianFlattening
public import StacksFrontier.RingTheory.Flat.LocalCriterionEssFP
public import StacksFrontier.RingTheory.Flat.MittagLeffler

/-!
# Situation 0AT0 over a quotient of the base ring

Fix Situation 0AT0: a local homomorphism `A → B` of local rings which is essentially of finite
type, a flat `A`-module `M`, a finite `B`-module `N` and an `A`-linear map `u : N → M` injective
modulo `𝔪_A`. For a proper ideal `E ⊆ A` the data

`A ⧸ E → B ⧸ EB`, `M ⧸ EM`, `N ⧸ EN`, `u mod E`

form Situation 0AT0 again. `AlgebraicGeometry.InjectiveModuloMaximalIdealSituation.quotient` is
that situation.

Reduction modulo `𝔪_{A ⧸ E}` is reduction modulo `𝔪_A`, because `E ⊆ 𝔪_A`, so the injectivity
hypothesis is inherited rather than reproved. Since a local ring has exactly one maximal ideal,
the hypothesis `E ≤ 𝔪_A` asks no more than `E ≠ ⊤`, which is forced: the quotient has to be
nontrivial to be local.

## Main definitions

* `AlgebraicGeometry.InjectiveModuloMaximalIdealSituation.quotient`: Situation 0AT0 over
  `A ⧸ E`.
* `AlgebraicGeometry.InjectiveModuloMaximalIdealSituation.quotientNEquiv` and
  `AlgebraicGeometry.InjectiveModuloMaximalIdealSituation.quotientMEquiv`: the two modules of
  the quotient situation, read as `N ⧸ EN` and `M ⧸ EM` over `A`.
* `AlgebraicGeometry.PolynomialLocalizationPresentation.quotient` and
  `AlgebraicGeometry.InjectiveModuloMaximalIdealSituation.quotientPresentation`: the
  presentation of `B ⧸ EB` as a localization at a prime of a polynomial algebra over `A ⧸ E`,
  in the same number of variables.

## Main results

* `AlgebraicGeometry.mkQ_mem_smul_top_iff`: membership in `J • X` is detected by the class
  modulo a submodule of `J • X`.
* `AlgebraicGeometry.PolynomialLocalizationPresentation.map_C_le_prime`: the extension of a
  proper ideal of `A` to the polynomial algebra lies in the prime of a presentation.
* `AlgebraicGeometry.InjectiveModuloMaximalIdealSituation.isScalarTower_quotient_N` and
  `AlgebraicGeometry.InjectiveModuloMaximalIdealSituation.isScalarTower_quotient_M`: the base
  `A` acts on the two modules of the quotient situation through `A ⧸ E`.
* `AlgebraicGeometry.InjectiveModuloMaximalIdealSituation.flat_quotient_N` and
  `AlgebraicGeometry.InjectiveModuloMaximalIdealSituation.flat_of_flat_quotient_N`: flatness of
  `N ⧸ EN` over `A ⧸ E` is flatness of the module of the quotient situation over its base.
* `AlgebraicGeometry.InjectiveModuloMaximalIdealSituation.finitePresentation_map_smul_top` and
  `AlgebraicGeometry.InjectiveModuloMaximalIdealSituation.finitePresentation_quotient_N`:
  `N ⧸ EN` is of finite presentation over `B ⧸ EB`.

## Implementation notes

The quotient `N ⧸ EN` has two descriptions: `N ⧸ (E • ⊤ : Submodule A N)`, which is the one the
statements of the claims in the proof of Stacks 05U9 use, and
`N ⧸ (EB • ⊤ : Submodule B N)`, which carries the `B ⧸ EB`-module structure Situation 0AT0 asks
for. The second is the module of the quotient situation; the two submodules have the same
elements (`Stacks.Flatness.FibrewiseCriterionEssFP.coe_map_smul_top`) and `quotientNEquiv` is
the resulting `A`-linear identification.

This construction occurs in the proof of Stacks 0AT3 — see
`AlgebraicGeometry.rTensor_mapQ_injective_of_henselian_of_flat_quotient`, which consumes it —
and again in the induction on the length of a generic flatness stratification in the proof of
Claim 1 of Stacks 05U9.

## References

* [Stacks Project, Tag 0AT0](https://stacks.math.columbia.edu/tag/0AT0)
* [Stacks Project, Tag 0AT3](https://stacks.math.columbia.edu/tag/0AT3)
* [Stacks Project, Tag 05U9](https://stacks.math.columbia.edu/tag/05U9)
-/

@[expose] public section

open IsLocalRing TensorProduct

universe u₁ u₂ u₃ u₄

namespace AlgebraicGeometry

/-- An element of `X` lies in `J • X` exactly when its class modulo a submodule `P ≤ J • X`
lies in `J • (X ⧸ P)`. -/
theorem mkQ_mem_smul_top_iff {A X : Type*} [CommRing A] [AddCommGroup X] [Module A X]
    (P : Submodule A X) (J : Ideal A) (hP : P ≤ J • ⊤) (x : X) :
    P.mkQ x ∈ J • (⊤ : Submodule A (X ⧸ P)) ↔ x ∈ J • (⊤ : Submodule A X) := by
  have h : J • (⊤ : Submodule A (X ⧸ P)) = (J • (⊤ : Submodule A X)).map P.mkQ := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  rw [h, ← Submodule.mem_comap, Submodule.comap_map_mkQ, sup_eq_right.mpr hP]

namespace PolynomialLocalizationPresentation

variable {A : Type u₁} [CommRing A] [IsLocalRing A] {B : Type u₂} [CommRing B] [IsLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)]

open MvPolynomial in
/-- **The extension of a proper ideal of `A` to the polynomial algebra lies in the prime of a
presentation.** The prime of a presentation is the contraction of `𝔪_B` along the polynomial
algebra, `E` lies in `𝔪_A`, and `A → B` is local. -/
theorem map_C_le_prime (P : PolynomialLocalizationPresentation A B) {E : Ideal A}
    (hE : E ≤ maximalIdeal A) :
    Ideal.map (C : A →+* MvPolynomial (Fin P.variableCount) A) E ≤ P.prime := by
  let := P.prime_isPrime
  let := P.polynomialAlgebra
  let := P.scalarTower
  let := P.isLocalization
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap]
  refine (IsLocalization.AtPrime.to_map_mem_maximal_iff B P.prime (C a)).mp ?_
  have h : algebraMap (MvPolynomial (Fin P.variableCount) A) B (C a) = algebraMap A B a := by
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  rw [h]
  exact Module.FlatAtPointSituation.map_maximalIdeal_le (algebraMap A B)
    (Ideal.mem_map_of_mem _ (hE ha))

open MvPolynomial in
/-- **A presentation of `B` over `A` reduces to one of `B ⧸ EB` over `A ⧸ E`.** If `B` is the
localization of `A[x_1, …, x_n]` at a prime `q` then `B ⧸ EB` is the localization of
`(A ⧸ E)[x_1, …, x_n]` at the image of `q`, in the same number of variables.

The reduction map `A[x] → (A ⧸ E)[x]` is surjective with kernel the extension of `E`
(`MvPolynomial.ker_map`), which lies inside `q` because `E ⊆ 𝔪_A` and `q` contracts `𝔪_B`. So
`IsLocalization.of_surjective` turns the localization of `A[x]` at `q` into a localization of
`(A ⧸ E)[x]` at the image of `q`, and the image of the prime complement of `q` is the prime
complement of its image. -/
noncomputable def quotient (P : PolynomialLocalizationPresentation A B) (E : Ideal A)
    (hE : E ≤ maximalIdeal A) :
    PolynomialLocalizationPresentation (A ⧸ E) (B ⧸ Ideal.map (algebraMap A B) E) := by
  letI := P.prime_isPrime
  letI := P.polynomialAlgebra
  letI := P.scalarTower
  letI := P.isLocalization
  set f : MvPolynomial (Fin P.variableCount) A →+*
      MvPolynomial (Fin P.variableCount) (A ⧸ E) := MvPolynomial.map (Ideal.Quotient.mk E) with hf
  have hfsurj : Function.Surjective f :=
    MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f = Ideal.map (C : A →+* MvPolynomial (Fin P.variableCount) A) E := by
    rw [hf, MvPolynomial.ker_map, Ideal.mk_ker]
  have hkerle : RingHom.ker f ≤ P.prime := hker ▸ P.map_C_le_prime hE
  have hcomp : (algebraMap (MvPolynomial (Fin P.variableCount) A) B).comp
      (C : A →+* MvPolynomial (Fin P.variableCount) A) = algebraMap A B := by
    rw [← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq A (MvPolynomial (Fin P.variableCount) A) B]
  have happ : ∀ a : A,
      algebraMap (MvPolynomial (Fin P.variableCount) A) B (C a) = algebraMap A B a := fun a ↦ by
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  letI algInst : Algebra (MvPolynomial (Fin P.variableCount) (A ⧸ E))
      (B ⧸ Ideal.map (algebraMap A B) E) :=
    (MvPolynomial.eval₂Hom (algebraMap (A ⧸ E) (B ⧸ Ideal.map (algebraMap A B) E))
      (fun i ↦ Ideal.Quotient.mk (Ideal.map (algebraMap A B) E)
        (algebraMap (MvPolynomial (Fin P.variableCount) A) B (X i)))).toAlgebra
  have hH : (Ideal.Quotient.mk (Ideal.map (algebraMap A B) E)).comp
      (algebraMap (MvPolynomial (Fin P.variableCount) A) B) =
      (algebraMap (MvPolynomial (Fin P.variableCount) (A ⧸ E))
        (B ⧸ Ideal.map (algebraMap A B) E)).comp f := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
    · simp only [RingHom.comp_apply, hf]
      change Ideal.Quotient.mk _ (algebraMap (MvPolynomial (Fin P.variableCount) A) B (C a)) =
        MvPolynomial.eval₂Hom _ _ (MvPolynomial.map (Ideal.Quotient.mk E) (C a))
      rw [happ, MvPolynomial.map_C, MvPolynomial.eval₂Hom_C,
        Ideal.Quotient.algebraMap_quotient_map_quotient]
    · simp only [RingHom.comp_apply, hf]
      change Ideal.Quotient.mk _ (algebraMap (MvPolynomial (Fin P.variableCount) A) B (X i)) =
        MvPolynomial.eval₂Hom _ _ (MvPolynomial.map (Ideal.Quotient.mk E) (X i))
      rw [MvPolynomial.map_X, MvPolynomial.eval₂Hom_X']
  have hH' : RingHom.ker (Ideal.Quotient.mk (Ideal.map (algebraMap A B) E)) ≤
      (RingHom.ker f).map (algebraMap (MvPolynomial (Fin P.variableCount) A) B) := by
    rw [Ideal.mk_ker, hker, Ideal.map_map, hcomp]
  haveI : IsLocalization (P.prime.primeCompl.map f) (B ⧸ Ideal.map (algebraMap A B) E) :=
    IsLocalization.of_surjective P.prime.primeCompl B f hfsurj
      (Ideal.Quotient.mk (Ideal.map (algebraMap A B) E)) Ideal.Quotient.mk_surjective hH hH'
  have hcomap : (P.prime.map f).comap f = P.prime := by
    rw [Ideal.comap_map_of_surjective f hfsurj, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.mpr hkerle
  have hmem : ∀ x, f x ∈ P.prime.map f ↔ x ∈ P.prime := fun x ↦ by
    rw [← Ideal.mem_comap, hcomap]
  haveI hq : (P.prime.map f).IsPrime := Ideal.map_isPrime_of_surjective hfsurj hkerle
  have hcompl : P.prime.primeCompl.map f = (P.prime.map f).primeCompl := by
    refine Submonoid.ext fun y ↦ ⟨?_, ?_⟩
    · rintro ⟨x, hx, rfl⟩
      exact fun hy ↦ hx ((hmem x).mp hy)
    · intro hy
      obtain ⟨x, rfl⟩ := hfsurj y
      exact ⟨x, fun hx ↦ hy (Ideal.mem_map_of_mem _ hx), rfl⟩
  exact { variableCount := P.variableCount
          prime := P.prime.map f
          prime_isPrime := hq
          polynomialAlgebra := algInst
          scalarTower := IsScalarTower.of_algebraMap_eq fun x ↦ by
            rw [MvPolynomial.algebraMap_eq]
            change _ = MvPolynomial.eval₂Hom _ _ (C x)
            rw [MvPolynomial.eval₂Hom_C]
          isLocalization := by
            have h : IsLocalization ((P.prime.map f).primeCompl)
                (B ⧸ Ideal.map (algebraMap A B) E) := hcompl ▸ inferInstance
            exact h }

end PolynomialLocalizationPresentation

namespace InjectiveModuloMaximalIdealSituation

variable (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄}) (E : Ideal S.A)

/-- **The two descriptions of `N ⧸ EN` agree.** The quotient of `N` by the `B`-submodule
`EB • ⊤`, which carries the `B ⧸ EB`-module structure, is the quotient of `N` by the
`A`-submodule `E • ⊤`, which is the description the claims in the proof of Stacks 05U9 use. The
two submodules have the same elements. -/
def quotientNAddEquiv :
    (S.N ⧸ (E.map (algebraMap S.A S.B) • ⊤ : Submodule S.B S.N)) ≃+
      S.N ⧸ (E • ⊤ : Submodule S.A S.N) :=
  Stacks.Flatness.FibrewiseCriterionEssFP.quotAddEquivOfCoeEq _ _
    (Stacks.Flatness.FibrewiseCriterionEssFP.coe_map_smul_top (R := S.A) (A := S.B)
      (M := S.N) E)

/-- The identification of the two descriptions of `N ⧸ EN` is `A`-linear. -/
theorem quotientNAddEquiv_smul (a : S.A)
    (x : S.N ⧸ (E.map (algebraMap S.A S.B) • ⊤ : Submodule S.B S.N)) :
    S.quotientNAddEquiv E (a • x) = a • S.quotientNAddEquiv E x := by
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

section Quotient

variable (hE : E ≤ maximalIdeal S.A)

include hE

/-- The extension of a proper ideal of `A` to `B` is proper. -/
theorem map_ne_top_of_le_maximalIdeal : E.map (algebraMap S.A S.B) ≠ ⊤ :=
  ne_top_of_le_ne_top (maximalIdeal.isMaximal S.B).ne_top
    ((Ideal.map_mono hE).trans
      (Module.FlatAtPointSituation.map_maximalIdeal_le (algebraMap S.A S.B)))

/-- **Situation 0AT0 over `A ⧸ E`.** For a proper ideal `E ⊆ A` the reduction
`A ⧸ E → B ⧸ EB`, `M ⧸ EM`, `N ⧸ EN`, `u mod E` of Situation 0AT0 is Situation 0AT0 again:
`A ⧸ E` and `B ⧸ EB` are local, the structure map between them is local and essentially of
finite type, `M ⧸ EM` is flat over `A ⧸ E`, `N ⧸ EN` is a finite `B ⧸ EB`-module, and the
reduction of `u mod E` modulo `𝔪_{A ⧸ E}` is the reduction of `u` modulo `𝔪_A`, hence
injective.

The module is `N ⧸ (EB • ⊤ : Submodule B N)`, the description carrying the `B ⧸ EB`-module
structure; `AlgebraicGeometry.InjectiveModuloMaximalIdealSituation.quotientNEquiv` identifies it
with `N ⧸ (E • ⊤ : Submodule A N)`. -/
def quotient : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄} := by
  have hEtop : E ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal S.A).ne_top hE
  have hJm : E.map (algebraMap S.A S.B) ≤ maximalIdeal S.B := (Ideal.map_mono hE).trans
    (Module.FlatAtPointSituation.map_maximalIdeal_le (algebraMap S.A S.B))
  have hJtop : E.map (algebraMap S.A S.B) ≠ ⊤ := S.map_ne_top_of_le_maximalIdeal E hE
  haveI : Nontrivial (S.A ⧸ E) := Ideal.Quotient.nontrivial_iff.mpr hEtop
  haveI : IsLocalRing (S.A ⧸ E) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk E) Ideal.Quotient.mk_surjective
  haveI : Nontrivial (S.B ⧸ E.map (algebraMap S.A S.B)) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  haveI : IsLocalRing (S.B ⧸ E.map (algebraMap S.A S.B)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (E.map (algebraMap S.A S.B)))
      Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (algebraMap (S.A ⧸ E) (S.B ⧸ E.map (algebraMap S.A S.B))) := by
    constructor
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    by_contra hna
    have ha' : a ∈ maximalIdeal S.A := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      exact fun h ↦ hna (h.map _)
    have hb : algebraMap S.A S.B a ∈ maximalIdeal S.B :=
      Module.FlatAtPointSituation.map_maximalIdeal_le (algebraMap S.A S.B)
        (Ideal.mem_map_of_mem _ ha')
    obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp ha
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient, ← map_mul,
      ← map_one (Ideal.Quotient.mk (E.map (algebraMap S.A S.B))), Ideal.Quotient.eq] at hc
    have h1 : (1 : S.B) ∈ maximalIdeal S.B := by
      have := (maximalIdeal S.B).sub_mem ((maximalIdeal S.B).mul_mem_right c hb) (hJm hc)
      simp at this
    exact (maximalIdeal.isMaximal S.B).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  haveI : Algebra.EssFiniteType (S.A ⧸ E) (S.B ⧸ E.map (algebraMap S.A S.B)) :=
    Algebra.EssFiniteType.of_comp S.A (S.A ⧸ E) (S.B ⧸ E.map (algebraMap S.A S.B))
  haveI : Module.Flat (S.A ⧸ E) (S.M ⧸ (E • ⊤ : Submodule S.A S.M)) :=
    Module.Flat.quotient_smul_top E
  letI : Module (S.A ⧸ E) (S.N ⧸ (E.map (algebraMap S.A S.B) • ⊤ : Submodule S.B S.N)) :=
    Module.compHom _ (algebraMap (S.A ⧸ E) (S.B ⧸ E.map (algebraMap S.A S.B)))
  haveI : IsScalarTower (S.A ⧸ E) (S.B ⧸ E.map (algebraMap S.A S.B))
      (S.N ⧸ (E.map (algebraMap S.A S.B) • ⊤ : Submodule S.B S.N)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  haveI : IsScalarTower S.A (S.A ⧸ E)
      (S.N ⧸ (E.map (algebraMap S.A S.B) • ⊤ : Submodule S.B S.N)) :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      change Submodule.Quotient.mk (algebraMap S.A S.B a • n) = Submodule.Quotient.mk (a • n)
      rw [algebraMap_smul]
  haveI : IsScalarTower S.A (S.A ⧸ E) (S.M ⧸ (E • ⊤ : Submodule S.A S.M)) :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl
  -- The identification of `N ⧸ EB • ⊤` with `N ⧸ E • ⊤`, and the reduction of `u`.
  let φL := (S.quotientNAddEquiv E).toLinearEquiv (S.quotientNAddEquiv_smul E)
  let ubar := Submodule.mapQ (E • ⊤ : Submodule S.A S.N) (E • ⊤ : Submodule S.A S.M) S.u
    (Submodule.smul_top_le_comap_smul_top E S.u)
  let uA : (S.N ⧸ (E.map (algebraMap S.A S.B) • ⊤ : Submodule S.B S.N)) →ₗ[S.A]
      S.M ⧸ (E • ⊤ : Submodule S.A S.M) := ubar ∘ₗ φL.toLinearMap
  let u' : (S.N ⧸ (E.map (algebraMap S.A S.B) • ⊤ : Submodule S.B S.N)) →ₗ[S.A ⧸ E]
      S.M ⧸ (E • ⊤ : Submodule S.A S.M) :=
    { toFun := uA
      map_add' := uA.map_add
      map_smul' := by
        intro r x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        rw [RingHom.id_apply, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul, algebraMap_smul,
          map_smul] }
  -- Reduction modulo the maximal ideal of `A ⧸ E` is reduction modulo `𝔪_A`.
  have hm : (maximalIdeal S.A).map (algebraMap S.A (S.A ⧸ E)) = maximalIdeal (S.A ⧸ E) :=
    Module.FlatAtPointSituation.maximalIdeal_quotient hEtop
  have hsetN : ∀ x : S.N ⧸ (E.map (algebraMap S.A S.B) • ⊤ : Submodule S.B S.N),
      x ∈ maximalIdeal (S.A ⧸ E) • (⊤ : Submodule (S.A ⧸ E) _) ↔
        x ∈ maximalIdeal S.A • (⊤ : Submodule S.A _) := by
    intro x
    rw [← hm, ← SetLike.mem_coe, Stacks.Flatness.FibrewiseCriterionEssFP.coe_map_smul_top,
      SetLike.mem_coe]
  have hsetM : ∀ y : S.M ⧸ (E • ⊤ : Submodule S.A S.M),
      y ∈ maximalIdeal (S.A ⧸ E) • (⊤ : Submodule (S.A ⧸ E) _) ↔
        y ∈ maximalIdeal S.A • (⊤ : Submodule S.A _) := by
    intro y
    rw [← hm, ← SetLike.mem_coe, Stacks.Flatness.FibrewiseCriterionEssFP.coe_map_smul_top,
      SetLike.mem_coe]
  have hEN : (E • ⊤ : Submodule S.A S.N) ≤ maximalIdeal S.A • ⊤ := Submodule.smul_mono_left hE
  have hEM : (E • ⊤ : Submodule S.A S.M) ≤ maximalIdeal S.A • ⊤ := Submodule.smul_mono_left hE
  have hinj : Function.Injective
      (Submodule.mapQ (maximalIdeal (S.A ⧸ E) • (⊤ : Submodule (S.A ⧸ E) _))
        (maximalIdeal (S.A ⧸ E) • (⊤ : Submodule (S.A ⧸ E) _)) u'
        (Submodule.smul_top_le_comap_smul_top (maximalIdeal (S.A ⧸ E)) u')) := by
    rw [Submodule.injective_mapQ_smul_top_iff]
    intro x hx
    rw [hsetM] at hx
    rw [hsetN, ← mem_smul_top_equiv_iff φL]
    obtain ⟨n, hn⟩ := Submodule.Quotient.mk_surjective _ (φL x)
    have hux : u' x = (E • ⊤ : Submodule S.A S.M).mkQ (S.u n) := by
      change ubar (φL x) = _
      rw [← hn]
      rfl
    rw [hux, mkQ_mem_smul_top_iff _ _ hEM] at hx
    rw [← hn]
    exact (mkQ_mem_smul_top_iff _ _ hEN n).mpr
      ((Submodule.injective_mapQ_smul_top_iff S.u _).mp S.injective_mod_maximalIdeal n hx)
  exact { A := S.A ⧸ E, B := S.B ⧸ E.map (algebraMap S.A S.B)
          M := S.M ⧸ (E • ⊤ : Submodule S.A S.M)
          N := S.N ⧸ (E.map (algebraMap S.A S.B) • ⊤ : Submodule S.B S.N)
          u := u', injective_mod_maximalIdeal := hinj }

/-- The base ring of the quotient situation is `A ⧸ E`. -/
theorem quotient_A : (S.quotient E hE).A = (S.A ⧸ E) := rfl

/-- The ring of the quotient situation is `B ⧸ E B`. -/
theorem quotient_B : (S.quotient E hE).B = (S.B ⧸ E.map (algebraMap S.A S.B)) := rfl

/-- The flat module of the quotient situation is `M ⧸ E M`. -/
theorem quotient_M : (S.quotient E hE).M = (S.M ⧸ (E • ⊤ : Submodule S.A S.M)) := rfl

/-- The module of the quotient situation is `N ⧸ E N`. -/
theorem quotient_N :
    (S.quotient E hE).N = (S.N ⧸ (E.map (algebraMap S.A S.B) • ⊤ : Submodule S.B S.N)) := rfl

/-- The base of the quotient situation is an `A`-algebra. Instance resolution does not see
through the projection, so the `A`-algebra structure on `A ⧸ E` is registered at it. -/
instance algebra_quotient_A : Algebra S.A (S.quotient E hE).A :=
  inferInstanceAs (Algebra S.A (S.A ⧸ E))

/-- The module of the quotient situation is an `A`-module. -/
instance module_quotient_N : Module S.A (S.quotient E hE).N :=
  inferInstanceAs
    (Module S.A (S.N ⧸ (E.map (algebraMap S.A S.B) • ⊤ : Submodule S.B S.N)))

/-- **The module of the quotient situation is an `A ⧸ E`-module.** The situation supplies the
action of its own base `(S.quotient E hE).A`, which is `A ⧸ E` by definition but not
syntactically, so instance resolution does not cross the projection; this registers the same
action at `A ⧸ E` written out. -/
instance module_quotientRing_N : Module (S.A ⧸ E) (S.quotient E hE).N :=
  (S.quotient E hE).moduleAN

/-- The flat module of the quotient situation is an `A`-module. -/
instance module_quotient_M : Module S.A (S.quotient E hE).M :=
  inferInstanceAs (Module S.A (S.M ⧸ (E • ⊤ : Submodule S.A S.M)))

/-- **The base acts on the module of the quotient situation through `A ⧸ E`.** -/
instance isScalarTower_quotient_N :
    IsScalarTower S.A (S.quotient E hE).A (S.quotient E hE).N :=
  IsScalarTower.of_algebraMap_smul fun a x ↦ by
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change Submodule.Quotient.mk (algebraMap S.A S.B a • n) = Submodule.Quotient.mk (a • n)
    rw [algebraMap_smul]

/-- **The base acts on the module of the quotient situation through `A ⧸ E` written out.** This
is `AlgebraicGeometry.InjectiveModuloMaximalIdealSituation.isScalarTower_quotient_N` with the
base of the quotient situation written as `A ⧸ E`, which is the form
`LinearEquiv.extendScalarsOfSurjective` needs in order to read an `A`-linear identification of
that module as an `A ⧸ E`-linear one. -/
instance isScalarTower_quotientRing_N :
    IsScalarTower S.A (S.A ⧸ E) (S.quotient E hE).N :=
  S.isScalarTower_quotient_N E hE

/-- **The base acts on the flat module of the quotient situation through `A ⧸ E`.** -/
instance isScalarTower_quotient_M :
    IsScalarTower S.A (S.quotient E hE).A (S.quotient E hE).M :=
  IsScalarTower.of_algebraMap_smul fun a x ↦ by
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

/-- The identification of the two descriptions of `N ⧸ EN` is semilinear over `A ⧸ E`. -/
private theorem quotientNAddEquiv_quotient_smul (r : S.A ⧸ E) (x : (S.quotient E hE).N) :
    S.quotientNAddEquiv E (r • x) = r • S.quotientNAddEquiv E x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul, algebraMap_smul]
  exact S.quotientNAddEquiv_smul E a x

/-- **Flatness of `N ⧸ EN` over `A ⧸ E` is flatness in the quotient situation.** The module of
the quotient situation is `N ⧸ EN` read over `B ⧸ EB`, so flatness over `A ⧸ E` of the
description `N ⧸ (E • ⊤ : Submodule A N)` used by the claims in the proof of Stacks 05U9 is
flatness of the module of the quotient situation over its base. -/
theorem flat_quotient_N
    (hflat : Module.Flat (S.A ⧸ E) (S.N ⧸ (E • ⊤ : Submodule S.A S.N))) :
    Module.Flat (S.quotient E hE).A (S.quotient E hE).N := by
  have := hflat
  exact Stacks.Flatness.EssFPLocalCriterion.flat_of_ringEquiv_of_addEquiv
    (R₂ := S.A ⧸ E) (Y := S.N ⧸ (E • ⊤ : Submodule S.A S.N))
    (RingEquiv.refl _) (S.quotientNAddEquiv E) (S.quotientNAddEquiv_quotient_smul E hE)

/-- **Flatness in the quotient situation is flatness of `N ⧸ EN` over `A ⧸ E`.** This is the
converse of `AlgebraicGeometry.InjectiveModuloMaximalIdealSituation.flat_quotient_N`, which is
what carries the flatness conclusion of Stacks 05U9 for the quotient situation back to the
statement of the claims. -/
theorem flat_of_flat_quotient_N
    (hflat : Module.Flat (S.quotient E hE).A (S.quotient E hE).N) :
    Module.Flat (S.A ⧸ E) (S.N ⧸ (E • ⊤ : Submodule S.A S.N)) := by
  have := hflat
  exact Stacks.Flatness.EssFPLocalCriterion.flat_of_ringEquiv_of_addEquiv
    (R₂ := (S.quotient E hE).A) (Y := (S.quotient E hE).N)
    (RingEquiv.refl _) (S.quotientNAddEquiv E).symm fun r x ↦
      (S.quotientNAddEquiv E).symm_apply_eq.mpr
        (by
          have h := S.quotientNAddEquiv_quotient_smul E hE r ((S.quotientNAddEquiv E).symm x)
          rw [AddEquiv.apply_symm_apply] at h
          exact h.symm)

/-- **The module of the quotient situation is `N ⧸ EN` as an `A`-module.** The quotient
situation carries `N ⧸ EN` in the description `N ⧸ (EB • ⊤ : Submodule B N)`, which has the
`B ⧸ EB`-module structure the situation asks for; this identifies it `A`-linearly with the
description `N ⧸ (E • ⊤ : Submodule A N)` in which the claims of the proof of Stacks 05U9 are
stated. -/
def quotientNEquiv : (S.quotient E hE).N ≃ₗ[S.A] S.N ⧸ (E • ⊤ : Submodule S.A S.N) :=
  (S.quotientNAddEquiv E).toLinearEquiv (S.quotientNAddEquiv_smul E)

/-- **The module of the quotient situation is `N ⧸ EN` as an `A ⧸ E`-module.** The `A`-linear
identification `AlgebraicGeometry.InjectiveModuloMaximalIdealSituation.quotientNEquiv` is linear
over `A ⧸ E` as well, because `A → A ⧸ E` is surjective. This is the form in which the induction
on the length of a generic flatness stratification in the proof of Claim 1 of Stacks 05U9 moves
statements over the base `A ⧸ E` between the two descriptions of `N ⧸ EN`. -/
def quotientNEquivBase :
    (S.quotient E hE).N ≃ₗ[S.A ⧸ E] S.N ⧸ (E • ⊤ : Submodule S.A S.N) :=
  (S.quotientNEquiv E hE).extendScalarsOfSurjective
    (S := S.A ⧸ E) Ideal.Quotient.mk_surjective

/-- **The flat module of the quotient situation is `M ⧸ EM` as an `A`-module.** -/
def quotientMEquiv : (S.quotient E hE).M ≃ₗ[S.A] S.M ⧸ (E • ⊤ : Submodule S.A S.M) where
  toFun := id
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The presentation of the quotient situation.** A presentation of `B` as a localization at a
prime of a polynomial algebra over `A` gives one for the quotient situation, in the same number
of variables. -/
noncomputable def quotientPresentation (P : PolynomialLocalizationPresentation S.A S.B) :
    PolynomialLocalizationPresentation (S.quotient E hE).A (S.quotient E hE).B :=
  P.quotient E hE

end Quotient

/-- **`N ⧸ EN` is of finite presentation over `B ⧸ EB`.** It is the base change of `N` along
`B → B ⧸ EB`. -/
theorem finitePresentation_map_smul_top [Module.FinitePresentation S.B S.N] :
    Module.FinitePresentation (S.B ⧸ E.map (algebraMap S.A S.B))
      (S.N ⧸ (E.map (algebraMap S.A S.B) • ⊤ : Submodule S.B S.N)) :=
  Module.FinitePresentation.of_equiv
    ((TensorProduct.quotTensorEquivQuotSMul S.N
      (E.map (algebraMap S.A S.B))).extendScalarsOfSurjective
        (S := S.B ⧸ E.map (algebraMap S.A S.B)) Ideal.Quotient.mk_surjective)

section Quotient

variable (hE : E ≤ maximalIdeal S.A)

include hE

/-- **The module of the quotient situation is of finite presentation.** -/
instance finitePresentation_quotient_N [Module.FinitePresentation S.B S.N] :
    Module.FinitePresentation (S.quotient E hE).B (S.quotient E hE).N :=
  S.finitePresentation_map_smul_top E

end Quotient

end InjectiveModuloMaximalIdealSituation

end AlgebraicGeometry

end
