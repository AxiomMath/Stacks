module

public import StacksFrontier.RingTheory.Rig.NaiveCotangent.Annihilation
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.ReductionComparison
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.ReductionHomology

/-!
# `NL_{Bₙ/Aₙ}` is the reduced complex, and Stacks 0AJU, (3) ⇔ (4)

Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal, let `B` be an object of the category
(Stacks 0AL4) and fix a completed polynomial presentation `B = A⟨x₁, …, x_r⟩ / J`.  Writing
`Aₙ = A / Iⁿ` and `Bₙ = B / IⁿB`, two of the equivalent conditions of Stacks 0AJU are

* (0AJW) some power of `I` annihilates `H^i(NL^∧_{B/A})`, `i = -1, 0`;
* (0AJX) some power of `I` annihilates `H^i(NL_{Bₙ/Aₙ})`, `i = -1, 0`, for every `n ≥ 1`.

`Rig/NaiveCotangent/Annihilation.lean` proves that equivalence with `NL_{Bₙ/Aₙ}` taken in the
shape Stacks 0AJS (1) produces, `Rig.CompletedNaiveCotangentComplex.reducedComplex`.  The
source's `NL_{Bₙ/Aₙ}`, and the condition as it is actually stated, is instead the
presentation-free naive cotangent complex of `Bₙ` over `Aₙ` — `Algebra.naiveCotangentComplex`,
built from the tautological presentation `Aₙ[Bₙ] → Bₙ`, whose two cohomology modules are the
categorical homology of a `HomologicalComplex.double` in degrees `1` and `0`.

This file closes the gap between the two.  Three identifications
are needed, and all three are now available:

* the homology of a `double` is the kernel and the cokernel of its one differential
  (`StacksFrontier/Homology/DoubleHomology.lean`);
* those two modules do not depend on the presentation
  (`StacksFrontier/RingTheory/NaiveCotangent/PresentationHomology.lean`, applied to
  `reductionGenerators` in `Rig/NaiveCotangent/ReductionHomology.lean`);
* `reducedComplex n` **is** `NL(Bₙ = Aₙ[x₁, …, x_r] / Jₙ)`.  Degree `-1` of that is
  `Rig/NaiveCotangent/ReductionComparison.lean`; degree `0` and the differential are here.

Degree `0` is the free module `⨁ᵢ Bₙ dxᵢ` on both sides, and the differentials match because
the formal partial derivative of the completion reduces to the polynomial partial derivative,
`ψₙ ∘ ∂/∂xᵢ = ∂/∂xᵢ ∘ ψₙ`.  That needs no derivation-uniqueness machinery: both sides are
additive, `ψₙ` kills `Iⁿ A⟨x⟩` and `∂/∂xᵢ` preserves it, so a single polynomial approximation
modulo `Iⁿ A⟨x⟩` settles it.

## Main definitions

* `Rig.CompletedPolynomialPresentation.freeToCotangentSpace`: `⨁ᵢ B dxᵢ → ⨁ᵢ Bₙ dxᵢ`, through
  `Algebra.Generators.cotangentSpaceBasis`.
* `Rig.CompletedPolynomialPresentation.reductionCotangentSpaceEquiv`: the degree-`0`
  identification `(⨁ᵢ B dxᵢ) / IⁿB · (⨁ᵢ B dxᵢ) ≃ ⨁ᵢ Bₙ dxᵢ`.

## Main results

* `NaiveCotangent.annihilatesCohomology_map_iff`: annihilation of the cohomology of a two-term
  complex transports along a degreewise isomorphism, **including a change of base ring** — the
  ideal is pushed forward.
* `Rig.CompletedNaiveCotangentComplex.mk_toAlgHom_partialDeriv`: the formal partial derivative
  of `A⟨x⟩` reduces to the partial derivative of `Aₙ[x]`.
* `Rig.CompletedNaiveCotangentComplex.reductionComparison_comm`: the two degreewise
  identifications commute with the differentials, i.e. `reducedComplex n` and
  `NL(Bₙ = Aₙ[x] / Jₙ)` are isomorphic as two-term complexes.
* `Rig.CompletedNaiveCotangentComplex.annihilatesCohomology_reducedComplex_iff`: `IᶜB`
  annihilates the cohomology of `reducedComplex n` exactly when `IᶜBₙ` annihilates that of
  `NL(Bₙ = Aₙ[x] / Jₙ)`.
* `Rig.isCohomologyAnnihilated_iff_isReductionCohomologyAnnihilated`: **Stacks 0AJU,
  (3) ⇔ (4)**, with both conditions exactly as the source states them — (3) through
  `LinearMap.ker` and `LinearMap.range` of the differential of
  `Rig.completedNaiveCotangentComplex`, and (4) through `Algebra.naiveCotangentComplex Aₙ Bₙ`
  and `HomologicalComplex.homology` in degrees `1` and `0`.

## Implementation notes

*The transport lemma changes the base ring, and it has to.*  `reducedComplex n` is a complex
of `B`-modules and `NL(Bₙ = Aₙ[x] / Jₙ)` one of `Bₙ`-modules; the two degreewise maps are only
`B`-linear.  `annihilatesCohomology_map_iff` is therefore stated for `X : TwoTerm S`,
`Y : TwoTerm S'` with `[Algebra S S']`, taking `S`-linear equivalences and concluding
annihilation by the pushed-forward ideal.  Its proof is elementwise, through
`mem_annihilator_H₁_iff` and `mem_annihilator_H₀_iff`, and that is what keeps it free of any
comparison of a `B`-submodule with a `Bₙ`-submodule of the same carrier — the comparison where
the instances stop being found.

*Why four instances are supplied by hand.*  `NaiveCotangent.NL` is a plain definition, so its
field projections do not reduce during instance search: `Module B.carrier (NL P').X₁` fails
even though `Module B.carrier P'.toExtension.Cotangent` succeeds.  The four instances are
installed with `let _ := inferInstanceAs …` inside the one proof that needs them; each is the
canonical instance on a definitionally equal type, so no diamond is created.

*What the tags record.*  `Rig/NaiveCotangent/Annihilation.lean` keeps its
`@[stacks 0AJU "(3) iff (4) for the reduced complexes"]`, which is a true statement about
`reducedComplex` and is the intermediate step this file consumes; the tag's bare
`(3) iff (4)` key now sits on
`Rig.isCohomologyAnnihilated_iff_isReductionCohomologyAnnihilated`.

## References

* [Stacks Project, Tag 0AJU](https://stacks.math.columbia.edu/tag/0AJU)
* [Stacks Project, Tag 0AJS](https://stacks.math.columbia.edu/tag/0AJS)
* [Stacks Project, Tag 0AJR](https://stacks.math.columbia.edu/tag/0AJR)
-/

@[expose] public noncomputable section

open Algebra MvPolynomial

namespace NaiveCotangent

universe ug vg wg

/-! ## Annihilation of the cohomology, elementwise and under transport -/

section Elementwise

variable {S : Type ug} [CommRing S] {X : TwoTerm.{ug, vg, wg} S} {a : S}

/-- An element annihilates `H⁻¹ X = ker d` exactly when it kills every element of the
degree-`1` term on which the differential vanishes. -/
public theorem mem_annihilator_H₁_iff :
    a ∈ (H₁ X).annihilator ↔ ∀ x : X.X₁, X.d x = 0 → a • x = 0 :=
  ⟨fun h x hx => Submodule.mem_annihilator.mp h x hx,
    fun h => Submodule.mem_annihilator.mpr fun x hx => h x hx⟩

/-- An element annihilates `H⁰ X = coker d` exactly when it carries every element of the
degree-`0` term into the image of the differential. -/
public theorem mem_annihilator_H₀_iff :
    a ∈ Module.annihilator S (H₀ X) ↔ ∀ y : X.X₀, a • y ∈ LinearMap.range X.d := by
  constructor
  · intro h y
    have hz : Submodule.mkQ (LinearMap.range X.d) (a • y) = 0 := by
      rw [map_smul]
      exact Module.mem_annihilator.mp h _
    rwa [← LinearMap.mem_ker, Submodule.ker_mkQ] at hz
  · intro h
    refine Module.mem_annihilator.mpr fun z => ?_
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range X.d) z
    rw [← map_smul, ← LinearMap.mem_ker, Submodule.ker_mkQ]
    exact h y

end Elementwise

section Transport

universe ug' vg' wg'

variable {S : Type ug} [CommRing S] {S' : Type ug'} [CommRing S'] [Algebra S S']
  {X : TwoTerm.{ug, vg, wg} S} {Y : TwoTerm.{ug', vg', wg'} S'}
  [Module S Y.X₁] [IsScalarTower S S' Y.X₁] [Module S Y.X₀] [IsScalarTower S S' Y.X₀]

/-- **Annihilation of the cohomology transports along a degreewise isomorphism, across a
change of base ring.**  If `X` is a two-term complex of `S`-modules, `Y` one of `S'`-modules
for an `S`-algebra `S'`, and `e₁`, `e₀` are `S`-linear isomorphisms of the corresponding terms
commuting with the two differentials, then an ideal `𝔞` of `S` annihilates the cohomology of
`X` exactly when its image in `S'` annihilates the cohomology of `Y`.

The proof is elementwise, which is what avoids ever comparing an `S`-submodule with an
`S'`-submodule of the same carrier. -/
public theorem annihilatesCohomology_map_iff (e₁ : X.X₁ ≃ₗ[S] Y.X₁) (e₀ : X.X₀ ≃ₗ[S] Y.X₀)
    (comm : ∀ x, e₀ (X.d x) = Y.d (e₁ x)) (𝔞 : Ideal S) :
    AnnihilatesCohomology 𝔞 X ↔ AnnihilatesCohomology (𝔞.map (algebraMap S S')) Y := by
  have hker : ∀ x : X.X₁, X.d x = 0 ↔ Y.d (e₁ x) = 0 := fun x => by
    rw [← comm x, e₀.map_eq_zero_iff]
  have hs₁ : ∀ (b : S) (x : X.X₁), e₁ (b • x) = (algebraMap S S' b) • e₁ x := fun b x => by
    rw [map_smul, algebraMap_smul]
  have hs₀ : ∀ (b : S) (y : X.X₀), e₀ (b • y) = (algebraMap S S' b) • e₀ y := fun b y => by
    rw [map_smul, algebraMap_smul]
  have hrange : ∀ y : X.X₀, y ∈ LinearMap.range X.d ↔ e₀ y ∈ LinearMap.range Y.d :=
    fun y => ⟨fun ⟨x, hx⟩ => ⟨e₁ x, by rw [← comm, hx]⟩,
      fun ⟨z, hz⟩ => ⟨e₁.symm z, e₀.injective (by rw [comm, e₁.apply_symm_apply, hz])⟩⟩
  constructor
  · intro h
    refine ⟨Ideal.map_le_iff_le_comap.mpr fun b hb => Ideal.mem_comap.mpr ?_,
      Ideal.map_le_iff_le_comap.mpr fun b hb => Ideal.mem_comap.mpr ?_⟩
    · refine mem_annihilator_H₁_iff.mpr fun z hz => ?_
      have hzero := mem_annihilator_H₁_iff.mp (h.hH₁ hb) (e₁.symm z)
        (by rwa [hker, e₁.apply_symm_apply])
      rw [← e₁.apply_symm_apply z, ← hs₁, hzero, map_zero]
    · refine mem_annihilator_H₀_iff.mpr fun w => ?_
      have hw := (hrange (b • e₀.symm w)).mp (mem_annihilator_H₀_iff.mp (h.hH₀ hb) (e₀.symm w))
      rwa [hs₀, e₀.apply_symm_apply] at hw
  · intro h
    refine ⟨fun b hb => mem_annihilator_H₁_iff.mpr fun x hx => ?_,
      fun b hb => mem_annihilator_H₀_iff.mpr fun y => ?_⟩
    · have hz := mem_annihilator_H₁_iff.mp (h.hH₁ (Ideal.mem_map_of_mem _ hb)) (e₁ x)
        ((hker x).mp hx)
      rwa [← hs₁, e₁.map_eq_zero_iff] at hz
    · refine (hrange (b • y)).mpr ?_
      have hw := mem_annihilator_H₀_iff.mp (h.hH₀ (Ideal.mem_map_of_mem _ hb)) (e₀ y)
      rwa [← hs₀] at hw

end Transport

end NaiveCotangent

namespace Rig

namespace CompletedPolynomialPresentation

/-! ## The degree-`0` identification `(⨁ᵢ B dxᵢ) / IⁿB ≃ ⨁ᵢ Bₙ dxᵢ` -/

universe u v

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
  {B : AdicFiniteTypeAlgebra.{u, v} A I} (P : CompletedPolynomialPresentation I B)

/-- The `B`-linear map `⨁ᵢ B dxᵢ → ⨁ᵢ Bₙ dxᵢ`: reduce each coordinate modulo `IⁿB` and read
the result in the basis `Algebra.Generators.cotangentSpaceBasis` of the degree-`0` term of
`NL(Bₙ = Aₙ[x₁, …, x_r] / Jₙ)`. -/
public def freeToCotangentSpace (n : ℕ) :
    (Fin P.variableCount → B.carrier) →ₗ[B.carrier]
      (P.reductionGenerators n).toExtension.CotangentSpace where
  toFun y := ∑ i, (algebraMap B.carrier (B.reductionPow n) (y i)) •
    (P.reductionGenerators n).cotangentSpaceBasis i
  map_add' y z := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.add_apply, map_add, add_smul]
  map_smul' b y := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, algebraMap_smul, RingHom.id_apply]

/-- The coordinates of `freeToCotangentSpace` are the reductions of the coordinates. -/
public theorem repr_freeToCotangentSpace (n : ℕ) (y : Fin P.variableCount → B.carrier)
    (j : Fin P.variableCount) :
    (P.reductionGenerators n).cotangentSpaceBasis.repr (P.freeToCotangentSpace n y) j
      = algebraMap B.carrier (B.reductionPow n) (y j) := by
  simp [freeToCotangentSpace, Finsupp.single_apply, Finset.sum_ite_eq']

/-- `⨁ᵢ B dxᵢ → ⨁ᵢ Bₙ dxᵢ` is surjective, because `B → Bₙ` is. -/
public theorem surjective_freeToCotangentSpace (n : ℕ) :
    Function.Surjective (P.freeToCotangentSpace n) := by
  intro m
  choose y hy using fun i : Fin P.variableCount =>
    Ideal.Quotient.mk_surjective
      ((P.reductionGenerators n).cotangentSpaceBasis.repr m i)
  refine ⟨y, (P.reductionGenerators n).cotangentSpaceBasis.repr.injective ?_⟩
  ext j
  rw [P.repr_freeToCotangentSpace n y j]
  exact hy j

/-- The kernel of `⨁ᵢ B dxᵢ → ⨁ᵢ Bₙ dxᵢ` is `IⁿB · (⨁ᵢ B dxᵢ)`: a tuple dies exactly when
every coordinate lies in `IⁿB`, and for a finite free module that is membership in the
submodule the ideal generates. -/
public theorem ker_freeToCotangentSpace (n : ℕ) :
    LinearMap.ker (P.freeToCotangentSpace n)
      = (B.adicIdeal ^ n) •
        (⊤ : Submodule B.carrier (Fin P.variableCount → B.carrier)) := by
  have hmem : ∀ y : B.carrier,
      algebraMap B.carrier (B.reductionPow n) y = 0 ↔ y ∈ B.adicIdeal ^ n := fun y => by
    rw [← B.adicIdealPow_eq n]
    exact Ideal.Quotient.eq_zero_iff_mem
  ext y
  rw [LinearMap.mem_ker, ← (P.reductionGenerators n).cotangentSpaceBasis.repr.map_eq_zero_iff,
    DFunLike.ext_iff]
  simp only [P.repr_freeToCotangentSpace, hmem, Finsupp.coe_zero, Pi.zero_apply]
  constructor
  · exact mem_smul_top_of_forall_mem
  · intro h j
    refine Submodule.smul_induction_on (p := fun w => w j ∈ B.adicIdeal ^ n) h
      (fun a ha m _ => ?_) (fun z w hz hw => ?_)
    · simpa using (B.adicIdeal ^ n).mul_mem_right (m j) ha
    · simpa using (B.adicIdeal ^ n).add_mem hz hw

/-- **The degree-`0` identification**: the degree-`0` term of
`Rig.CompletedNaiveCotangentComplex.reducedComplex n` is the degree-`0` term of
`NL(Bₙ = Aₙ[x₁, …, x_r] / Jₙ)`. -/
public def reductionCotangentSpaceEquiv (n : ℕ) :
    ((Fin P.variableCount → B.carrier) ⧸
        ((B.adicIdeal ^ n) • ⊤ :
          Submodule B.carrier (Fin P.variableCount → B.carrier)))
      ≃ₗ[B.carrier] (P.reductionGenerators n).toExtension.CotangentSpace :=
  (Submodule.quotEquivOfEq _ _ (P.ker_freeToCotangentSpace n).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (P.surjective_freeToCotangentSpace n))

/-- On the class of a tuple, the degree-`0` identification is `freeToCotangentSpace`. -/
public theorem reductionCotangentSpaceEquiv_mkQ (n : ℕ)
    (y : Fin P.variableCount → B.carrier) :
    P.reductionCotangentSpaceEquiv n
        (Submodule.mkQ ((B.adicIdeal ^ n) • ⊤ :
          Submodule B.carrier (Fin P.variableCount → B.carrier)) y)
      = P.freeToCotangentSpace n y := by
  simp [reductionCotangentSpaceEquiv, LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- On the class of a conormal class, the degree-`-1` identification of
`Rig/NaiveCotangent/ReductionComparison.lean` is `Algebra.Extension.Cotangent.map`. -/
public theorem cotangentQuotConormalSubEquiv_mkQ (n : ℕ) (z : P.extension.Cotangent) :
    P.cotangentQuotConormalSubEquiv n (Submodule.mkQ (P.conormalSub n) z)
      = Algebra.Extension.Cotangent.map (P.reductionHom n) z := by
  simp [cotangentQuotConormalSubEquiv, LinearMap.quotKerEquivOfSurjective_apply_mk]

end CompletedPolynomialPresentation

namespace CompletedNaiveCotangentComplex

/-! ## The differentials agree, and the annihilation conditions coincide -/

universe u v

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
  {B : AdicFiniteTypeAlgebra.{u, v} A I} {P : CompletedPolynomialPresentation I B}

/-- **The formal partial derivative of `A⟨x⟩` reduces to the partial derivative of
`Aₙ[x]`.**  Precisely: the class in `Bₙ` of `∂g/∂xᵢ` evaluated in `B` is the value at the
generators of `Bₙ` of `∂(ψₙ g)/∂xᵢ`.

No derivation-uniqueness machinery is needed.  Both sides are additive in `g`; `ψₙ` kills
`Iⁿ A⟨x⟩` and `∂/∂xᵢ` carries `Iⁿ A⟨x⟩` into itself, whose image in `Bₙ` is zero; so a single
polynomial approximation of `g` modulo `Iⁿ A⟨x⟩` reduces the claim to the polynomial case,
where it is `MvPolynomial.pderiv_map` together with the two facts
`partialDeriv_polynomial` and `aeval_reductionVal_map`. -/
public theorem mk_toAlgHom_partialDeriv (K : CompletedNaiveCotangentComplex P)
    (n : ℕ) (i : Fin P.variableCount) (g : P.completedPolynomialRing) :
    Ideal.Quotient.mk (B.adicIdealPow n) (P.toAlgHom (K.partialDeriv i g))
      = MvPolynomial.aeval (P.reductionVal n)
          (MvPolynomial.pderiv i (P.reductionAlgHom n g)) := by
  obtain ⟨q, hq⟩ := P.exists_sub_mem_adicPow n g
  have hdiff : K.partialDeriv i g - K.partialDeriv i
      (algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing q)
      ∈ P.completedAdicPow n := by
    rw [← map_sub]
    exact derivation_mem_map_of_mem_map (K.partialDeriv i) (I ^ n) hq
  have hL : Ideal.Quotient.mk (B.adicIdealPow n) (P.toAlgHom (K.partialDeriv i g))
      = Ideal.Quotient.mk (B.adicIdealPow n) (P.toAlgHom (K.partialDeriv i
          (algebraMap (MvPolynomial (Fin P.variableCount) A)
            P.completedPolynomialRing q))) := by
    refine Ideal.Quotient.eq.mpr ?_
    have hmem := P.toAlgHom_mem_adicIdealPow (n := n) hdiff
    rwa [map_sub] at hmem
  have hpsi : P.reductionAlgHom n g = MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) q :=
    (P.reductionAlgHom_eq_of_sub_mem n hq).trans (P.reductionAlgHom_polynomial n q)
  rw [hL, hpsi, MvPolynomial.pderiv_map, K.partialDeriv_polynomial i q]
  exact (P.aeval_reductionVal_map n (MvPolynomial.pderiv i q)).symm

/-- The degree-`0` identification carries the differential of `NL^∧_{B/A}` to the differential
of `NL(Bₙ = Aₙ[x₁, …, x_r] / Jₙ)`, on a conormal class. -/
public theorem freeToCotangentSpace_differential (K : CompletedNaiveCotangentComplex P) (n : ℕ)
    (g : P.extension.ker) :
    P.freeToCotangentSpace n (K.differential (Algebra.Extension.Cotangent.mk g))
      = (P.reductionGenerators n).toExtension.cotangentComplex
          (Algebra.Extension.Cotangent.map (P.reductionHom n)
            (Algebra.Extension.Cotangent.mk g)) := by
  refine (P.reductionGenerators n).cotangentSpaceBasis.repr.injective ?_
  ext j
  rw [K.differential_mk g, P.repr_freeToCotangentSpace n _ j,
    Algebra.Extension.Cotangent.map_mk, Algebra.Extension.cotangentComplex_mk,
    Algebra.Generators.cotangentSpaceBasis_repr_one_tmul, P.reductionGenerators_val n]
  exact K.mk_toAlgHom_partialDeriv n j (g : P.extension.Ring)

/-- **`reducedComplex n` and `NL(Bₙ = Aₙ[x₁, …, x_r] / Jₙ)` are isomorphic as two-term
complexes**: the degree-`-1` identification of `ReductionComparison.lean` and the degree-`0`
identification above commute with the two differentials. -/
public theorem reductionComparison_comm (K : CompletedNaiveCotangentComplex P) (n : ℕ)
    (x : P.extension.Cotangent ⧸ P.conormalSub n) :
    P.reductionCotangentSpaceEquiv n ((K.reducedComplex n).d x)
      = (P.reductionGenerators n).toExtension.cotangentComplex
          (P.cotangentQuotConormalSubEquiv n x) := by
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (P.conormalSub n) x
  obtain ⟨g, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective z
  have h1 : P.reductionCotangentSpaceEquiv n ((K.reducedComplex n).d
      (Submodule.mkQ (P.conormalSub n) (Algebra.Extension.Cotangent.mk g)))
      = P.freeToCotangentSpace n (K.differential (Algebra.Extension.Cotangent.mk g)) :=
    P.reductionCotangentSpaceEquiv_mkQ n _
  rw [h1, P.cotangentQuotConormalSubEquiv_mkQ]
  exact K.freeToCotangentSpace_differential n g

/-- **`IᶜB` annihilates the cohomology of `reducedComplex n` exactly when `IᶜBₙ` annihilates
that of `NL(Bₙ = Aₙ[x₁, …, x_r] / Jₙ)`.**  This is `reductionComparison_comm` fed to
`NaiveCotangent.annihilatesCohomology_map_iff`, whose change of base ring from `B` to `Bₙ` is
exactly the pushforward `IᶜB ↦ IᶜBₙ`. -/
public theorem annihilatesCohomology_reducedComplex_iff (K : CompletedNaiveCotangentComplex P)
    (n c : ℕ) :
    NaiveCotangent.AnnihilatesCohomology (B.adicIdeal ^ c) (K.reducedComplex n) ↔
      NaiveCotangent.AnnihilatesCohomology ((I ^ c).map (algebraMap A (B.reductionPow n)))
        (NaiveCotangent.NL (P.reductionGenerators n)) := by
  let _ : Module B.carrier (NaiveCotangent.NL (P.reductionGenerators n)).X₁ :=
    inferInstanceAs (Module B.carrier (P.reductionGenerators n).toExtension.Cotangent)
  let _ : IsScalarTower B.carrier (B.reductionPow n)
      (NaiveCotangent.NL (P.reductionGenerators n)).X₁ :=
    inferInstanceAs (IsScalarTower B.carrier (B.reductionPow n)
      (P.reductionGenerators n).toExtension.Cotangent)
  let _ : Module B.carrier (NaiveCotangent.NL (P.reductionGenerators n)).X₀ :=
    inferInstanceAs (Module B.carrier (P.reductionGenerators n).toExtension.CotangentSpace)
  let _ : IsScalarTower B.carrier (B.reductionPow n)
      (NaiveCotangent.NL (P.reductionGenerators n)).X₀ :=
    inferInstanceAs (IsScalarTower B.carrier (B.reductionPow n)
      (P.reductionGenerators n).toExtension.CotangentSpace)
  have hideal : ((B.adicIdeal ^ c).map (algebraMap B.carrier (B.reductionPow n)))
      = (I ^ c).map (algebraMap A (B.reductionPow n)) := by
    rw [← B.adicIdealPow_eq c, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq A B.carrier (B.reductionPow n)]
  rw [← hideal]
  exact NaiveCotangent.annihilatesCohomology_map_iff
    (P.cotangentQuotConormalSubEquiv n) (P.reductionCotangentSpaceEquiv n)
    (K.reductionComparison_comm n) (B.adicIdeal ^ c)

end CompletedNaiveCotangentComplex

/-! ## Stacks 0AJU, (3) ⇔ (4) -/

universe u v

/-- **Stacks 0AJU, the equivalence of conditions (3) and (4).**  For a completed polynomial
presentation `B = A⟨x₁, …, x_r⟩ / J` of an object `B` of the category (Stacks 0AL4) over a
Noetherian ring `A`, the following are equivalent:

* (3) some power `I^c` of `I` annihilates `H^{-1}` and `H^0` of `NL^∧_{B/A}`, that is, the
  kernel and the cokernel of the differential of `Rig.completedNaiveCotangentComplex B P`;
* (4) some power `I^c` of `I` annihilates, for every `n ≥ 1`, the degree-`1` and degree-`0`
  homology of `Algebra.naiveCotangentComplex Aₙ Bₙ`, where `Aₙ = A / Iⁿ` and `Bₙ = B / IⁿB`.

Condition (4) is the source's, and is *presentation-free*: `NL_{Bₙ/Aₙ}` is the naive cotangent
complex of the tautological presentation `Aₙ[Bₙ] → Bₙ` and its cohomology is the categorical
homology of a `HomologicalComplex.double`.  Three identifications turn it into a statement
about the presentation `Bₙ = Aₙ[x₁, …, x_r] / Jₙ` of Stacks 0AJS, through which the source's
argument runs: the homology of a `double` is the kernel and the cokernel of its differential;
those are independent of the presentation; and `reducedComplex n`, the quotient of
`NL^∧_{B/A}` by the image of `J ∩ Iⁿ A⟨x⟩` and by `IⁿB · (⨁ B dxᵢ)`, *is*
`NL(Bₙ = Aₙ[x] / Jₙ)`.  The transport of the annihilation statement across those is then
`Rig.CompletedNaiveCotangentComplex.exists_annihilator_twoTerm_iff_forall_reducedComplex`,
whose forward direction doubles the exponent and whose backward direction spends the shift of
Stacks 0AJS (1) and preserves it. -/
@[stacks 0AJU "(3) iff (4)"]
public theorem isCohomologyAnnihilated_iff_isReductionCohomologyAnnihilated
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B) :
    (∃ c : ℕ,
        (I ^ c).map (algebraMap A B.carrier) ≤
          Module.annihilator B.carrier
            (LinearMap.ker (completedNaiveCotangentComplex B P).differential) ∧
        (I ^ c).map (algebraMap A B.carrier) ≤
          Module.annihilator B.carrier
            ((Fin P.variableCount → B.carrier) ⧸
              LinearMap.range (completedNaiveCotangentComplex B P).differential)) ↔
      ∃ c : ℕ, ∀ n : ℕ, 1 ≤ n →
        ∀ a : A, a ∈ I ^ c →
          ((Ideal.Quotient.mk ((I ^ n).map (algebraMap A B.carrier))
                (algebraMap A B.carrier a)) ∈
              Module.annihilator (B.carrier ⧸ (I ^ n).map (algebraMap A B.carrier))
                ((Algebra.naiveCotangentComplex (A ⧸ I ^ n)
                  (B.carrier ⧸ (I ^ n).map (algebraMap A B.carrier))).homology 1) ∧
            (Ideal.Quotient.mk ((I ^ n).map (algebraMap A B.carrier))
                (algebraMap A B.carrier a)) ∈
              Module.annihilator (B.carrier ⧸ (I ^ n).map (algebraMap A B.carrier))
                ((Algebra.naiveCotangentComplex (A ⧸ I ^ n)
                  (B.carrier ⧸ (I ^ n).map (algebraMap A B.carrier))).homology 0)) := by
  have h3 : (∃ c : ℕ,
      (I ^ c).map (algebraMap A B.carrier) ≤
        Module.annihilator B.carrier
          (LinearMap.ker (completedNaiveCotangentComplex B P).differential) ∧
      (I ^ c).map (algebraMap A B.carrier) ≤
        Module.annihilator B.carrier
          ((Fin P.variableCount → B.carrier) ⧸
            LinearMap.range (completedNaiveCotangentComplex B P).differential)) ↔
      ∃ c : ℕ, NaiveCotangent.AnnihilatesCohomology (B.adicIdeal ^ c)
        (completedNaiveCotangentComplex B P).twoTerm := by
    refine exists_congr fun c => ?_
    rw [← B.adicIdealPow_eq c]
    exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.hH₁, h.hH₀⟩⟩
  rw [h3, (completedNaiveCotangentComplex B P).exists_annihilator_twoTerm_iff_forall_reducedComplex,
    ← P.exists_annihilatesCohomology_nl_reductionGenerators_iff]
  exact exists_congr fun c => forall_congr' fun n => imp_congr_right fun _ =>
    (completedNaiveCotangentComplex B P).annihilatesCohomology_reducedComplex_iff n c

end Rig

end
