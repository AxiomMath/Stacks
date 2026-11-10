module

public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.JacobiZariski
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.CombinedPresentation
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.ReductionComparison
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.Transitivity

/-!
# Stacks 0AQJ: injectivity at the left end of the transitivity sequence

Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal, let `B` and `C` be objects of the
category (Stacks 0AL4) of `I`-adically complete `A`-algebras of finite type modulo `I`, and let
`B → C` be a morphism.  Fix a completed polynomial presentation `B = A⟨x₁, …, x_r⟩ / J` and a
presentation `ψ : B⟨y₁, …, y_s⟩ ↠ C` of `C` over `B`, so that the combined presentation of
Stacks 0ALM presents `C = A⟨x, y⟩ / K`.  Writing `Bₙ = B / IⁿB` and `Cₙ = C / IⁿC`, **Stacks
0AQJ** says that if `Bₙ → Cₙ` is a local complete intersection homomorphism for every `n ≥ 1`,
then the first map

`H⁻¹(NL^∧_{B/A} ⊗_B C) ⟶ H⁻¹(NL^∧_{C/A})`

of the six-term sequence of Stacks 0ALM is injective.

The source argues by passing to the limit: `H⁻¹(NL^∧_{B/A} ⊗_B C)` is a finite `C`-module, hence
`I`-adically complete, so it is the limit of its reductions, which by Stacks 0AJS are the
`H⁻¹(NL_{Bₙ/Aₙ} ⊗_{Bₙ} Cₙ)`, and each of those injects into `H⁻¹(NL_{Cₙ/Aₙ})` by the
Jacobi–Zariski injectivity for local complete intersections (Stacks 07D4).  What this file
proves is that same argument, carried out one degree lower: the comparison
`C ⊗_B J/J² → K/K²` of conormal modules is injective *before* restricting to kernels, and the
statement of the lemma follows because `H⁻¹` is a submodule and the map on `H⁻¹` is the
restriction of that comparison.  Being a limit of injections is used in the form "an element of
an `I`-adically Hausdorff module killed by every reduction is zero", which is
`IsHausdorff.eq_iff_smodEq`; the two reductions of `C ⊗_{A⟨x⟩} J` that have to be controlled are
`C ↠ Cₙ` and `J ↠ Jₙ`, and the kernel of the second is where Artin–Rees
(`Ideal.exists_pow_inf_eq_pow_smul`) enters, producing the shift `c` by which the two inverse
systems of Stacks 0AJS differ.

## Main definitions

* `Rig.coeffReduction` — the reduction of coefficients `R⟨x_σ⟩ → (R / 𝔞ⁿ)[x_σ]`, for an
  arbitrary base pair `(R, 𝔞)` and an arbitrary variable type.  It is the generic form of
  `Rig.CompletedPolynomialPresentation.reductionAlgHom`, which is this map for the variables and
  the base pair of a presentation;
  `Rig.CompletedPolynomialPresentation.reductionAlgHom_eq_coeffReduction` identifies the two.
* `Rig.reducedGenerators` — the presentation `Sₙ = (R / 𝔞ⁿ)[x_σ] / (ker f)ₙ` induced by a
  presentation `f : R⟨x_σ⟩ ↠ S`, as an `Algebra.Generators`.  This is the generic form of
  Stacks 0AJS's reduced presentation and is applied both to `B = A⟨x⟩ / J` over `(A, I)` and to
  `C = B⟨y⟩ / J'` over `(B, IB)`.
* `Rig.reductionMap` — the reduction `B / IⁿB → C / IⁿC` of a morphism of (0AL4), the map whose
  local complete intersection property is the hypothesis of the lemma.

## Main results

* `Rig.CompletedPolynomialPresentation.injective_cotangentMap_innerExtensionHom_of_lci` — the
  comparison `C ⊗_B J/J² → K/K²` is injective.  This is stronger than the lemma and is where the
  work is.
* `Rig.CompletedPolynomialPresentation.injective_onH₁_chainMapInl_of_lci` — **Stacks 0AQJ**:
  `H⁻¹(NL^∧_{B/A} ⊗_B C) → H⁻¹(NL^∧_{C/A})` is injective.

## Implementation notes

*Why the reduced presentation is rebuilt generically.*  The library already has the reduced
presentation of Stacks 0AJS as `Rig.CompletedPolynomialPresentation.reductionGenerators`, but it
is spelled with the ideal `(Iⁿ)·B` (the power taken in the base) and indexed by
`Fin P.variableCount`.  The proof below needs the reduced presentation of `B` over `A` *and* the
reduced presentation of `C` over `B` to compose as `Algebra.Generators`, which forces the target
quotient of the first to be literally the base quotient of the second.  Those two are
`B / (Iⁿ)·B` and `B / (I·B)ⁿ`: equal ideals (`Rig.AdicFiniteTypeAlgebra.adicIdealPow_eq`) but not
the same term, so the two uses of `reductionGenerators` cannot be composed.  The generic
`Rig.reducedGenerators` below is stated in the `(𝔞·S)ⁿ` spelling throughout, which does compose,
and is more general in two further ways: the base pair is arbitrary, and the variable type is
arbitrary.  `Rig.reductionAlgHom_eq_coeffReduction` records that the coefficient reduction
underlying it is the library's `reductionAlgHom`, so nothing is proved twice about two unrelated
maps.

*The hypothesis is the source's.*  `Bₙ` and `Cₙ` are `B / IⁿB` and `C / IⁿC`, spelled
`B.carrier ⧸ B.adicIdeal ^ n` and `C.carrier ⧸ C.adicIdeal ^ n`, and the reduction
`Bₙ → Cₙ` is `Ideal.quotientMap`, so the hypothesis of the main theorems is literally the
source's "`B/IⁿB → C/IⁿC` is a local complete intersection homomorphism for all `n`", with `n`
written `n + 1` to range over `n ≥ 1`.

*Where the two presentations meet.*  The combined presentation of Stacks 0ALM has
`r + s` variables, split by `Fin.castAdd`/`Fin.natAdd`, while `Algebra.Generators.comp` indexes
the composite presentation by `Fin s ⊕ Fin r` with the *fiber* variables on the left.
`Rig.combinedIndex` is the resulting renaming, and
`Rig.CompletedPolynomialPresentation.reducedCombinedHom` is the morphism of extensions from the
combined presentation of `C` over `A` down to its reduction, through which the Stacks 07D4
injectivity at level `n` is pulled back.

## References

* [Stacks Project, Tag 0AQJ](https://stacks.math.columbia.edu/tag/0AQJ)
* [Stacks Project, Tag 0ALM](https://stacks.math.columbia.edu/tag/0ALM)
* [Stacks Project, Tag 0AJS](https://stacks.math.columbia.edu/tag/0AJS)
* [Stacks Project, Tag 07D4](https://stacks.math.columbia.edu/tag/07D4)
-/

@[expose] public noncomputable section

open MvPolynomial
open scoped TensorProduct

namespace Rig

/-! ## Reduction of coefficients `R⟨x_σ⟩ → (R / 𝔞ⁿ)[x_σ]` -/

section CoeffReduction

variable {R : Type*} [CommRing R] (𝔞 : Ideal R) (σ : Type*)

/-- `R[x_σ] ⧸ 𝔞ⁿ R[x_σ] ≃ (R / 𝔞ⁿ)[x_σ]`: reducing the coefficients of a polynomial modulo `𝔞ⁿ`
is the same as dividing by the ideal that `𝔞ⁿ` generates.  This is the generic form of
`Rig.CompletedPolynomialPresentation.polyQuotEquiv`. -/
public def coeffQuotEquiv (n : ℕ) :
    (MvPolynomial σ R ⧸ ((𝔞.map (C : R →+* MvPolynomial σ R)) ^ n)) ≃ₐ[R]
      MvPolynomial σ (R ⧸ 𝔞 ^ n) :=
  (Ideal.quotientEquivAlgOfEq R (by rw [← Ideal.map_pow])).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) (𝔞 ^ n)).symm

/-- On the class of a polynomial, `coeffQuotEquiv` reduces the coefficients modulo `𝔞ⁿ`. -/
public theorem coeffQuotEquiv_mk (n : ℕ) (q : MvPolynomial σ R) :
    coeffQuotEquiv 𝔞 σ n (Ideal.Quotient.mk _ q)
      = MvPolynomial.map (Ideal.Quotient.mk (𝔞 ^ n)) q := by
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]
  rfl

/-- **The reduction of coefficients `R⟨x_σ⟩ → (R / 𝔞ⁿ)[x_σ]`.**  It is `AdicCompletion.evalₐ`
at level `n`, whose target `R[x_σ] / 𝔞ⁿR[x_σ]` is `(R / 𝔞ⁿ)[x_σ]`. -/
public def coeffReduction (n : ℕ) :
    AdicCompletion (𝔞.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R) →ₐ[R]
      MvPolynomial σ (R ⧸ 𝔞 ^ n) :=
  (coeffQuotEquiv 𝔞 σ n).toAlgHom.comp
    ((AdicCompletion.evalₐ (𝔞.map (C : R →+* MvPolynomial σ R)) n).restrictScalars R)

/-- The coefficient reduction is surjective: `AdicCompletion.evalₐ` is, and the rest is an
isomorphism. -/
public theorem surjective_coeffReduction (n : ℕ) :
    Function.Surjective (coeffReduction 𝔞 σ n) :=
  (coeffQuotEquiv 𝔞 σ n).surjective.comp (AdicCompletion.surjective_evalₐ _ n)

/-- On a polynomial, the coefficient reduction reduces the coefficients modulo `𝔞ⁿ`. -/
public theorem coeffReduction_algebraMap (n : ℕ) (q : MvPolynomial σ R) :
    coeffReduction 𝔞 σ n (algebraMap (MvPolynomial σ R) _ q)
      = MvPolynomial.map (Ideal.Quotient.mk (𝔞 ^ n)) q := by
  have hof : algebraMap (MvPolynomial σ R)
      (AdicCompletion (𝔞.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)) q =
      AdicCompletion.of (𝔞.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R) q := by
    rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply]
  rw [coeffReduction, AlgHom.comp_apply, hof]
  rw [show (AdicCompletion.evalₐ (𝔞.map (C : R →+* MvPolynomial σ R)) n).restrictScalars R
        (AdicCompletion.of (𝔞.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R) q) =
      Ideal.Quotient.mk _ q from AdicCompletion.evalₐ_of _ n q]
  exact coeffQuotEquiv_mk 𝔞 σ n q

/-- The coefficient reduction sends the constant `a` to the constant of its class. -/
public theorem coeffReduction_coeff (n : ℕ) (a : R) :
    coeffReduction 𝔞 σ n (algebraMap R _ a) = C (Ideal.Quotient.mk (𝔞 ^ n) a) := by
  rw [IsScalarTower.algebraMap_apply R (MvPolynomial σ R), coeffReduction_algebraMap]
  simp only [MvPolynomial.algebraMap_eq, MvPolynomial.map_C]

/-- **The kernel of the coefficient reduction is `𝔞ⁿ R⟨x_σ⟩`.**  One inclusion is formal; the
other is `AdicCompletion.pow_smul_top_eq_ker_eval`, which identifies the kernel of the `n`-th
evaluation with `𝔞ⁿ R⟨x_σ⟩`. -/
public theorem ker_coeffReduction [IsNoetherianRing R] (n : ℕ) :
    RingHom.ker (coeffReduction 𝔞 σ n).toRingHom =
      (𝔞.map (algebraMap R
        (AdicCompletion (𝔞.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)))) ^ n := by
  have hfg : (𝔞.map (C : R →+* MvPolynomial σ R)).FG := (Ideal.fg_of_isNoetherianRing 𝔞).map _
  have hmap : (𝔞 ^ n).map (algebraMap R (MvPolynomial σ R)) =
      (𝔞.map (C : R →+* MvPolynomial σ R)) ^ n := by
    rw [MvPolynomial.algebraMap_eq, Ideal.map_pow]
  refine le_antisymm (fun x hx => ?_) ?_
  · -- An element killed by the reduction is killed by the `n`-th evaluation.
    have heval : AdicCompletion.evalₐ (𝔞.map (C : R →+* MvPolynomial σ R)) n x = 0 := by
      have h0 : coeffQuotEquiv 𝔞 σ n
          (AdicCompletion.evalₐ (𝔞.map (C : R →+* MvPolynomial σ R)) n x) = 0 :=
        RingHom.mem_ker.mp hx
      simpa using (coeffQuotEquiv 𝔞 σ n).injective (h0.trans (map_zero _).symm)
    have hker : x ∈ LinearMap.ker (AdicCompletion.eval
        (𝔞.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R) n) := by
      rw [LinearMap.mem_ker, ← AdicCompletion.factor_evalₐ_eq_eval
        (𝔞.map (C : R →+* MvPolynomial σ R)) x (by simp), heval, map_zero]
    rw [← AdicCompletion.pow_smul_top_eq_ker_eval hfg] at hker
    have hbridge := map_smul_top_le_map_smul_top (A := R) (R := MvPolynomial σ R)
      (S := AdicCompletion (𝔞.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R))
      (M := AdicCompletion (𝔞.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R)) (𝔞 ^ n)
    rw [Ideal.smul_eq_mul, Ideal.mul_top, hmap] at hbridge
    have hres := hbridge hker
    rw [Submodule.restrictScalars_mem, Ideal.map_pow] at hres
    exact hres
  · rw [← Ideal.map_pow]
    refine Ideal.map_le_iff_le_comap.mpr fun a ha => Ideal.mem_comap.mpr ?_
    rw [RingHom.mem_ker]
    change coeffReduction 𝔞 σ n (algebraMap R _ a) = 0
    rw [coeffReduction_coeff, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

/-- Two ring maps out of `R⟨x_σ⟩` which kill `𝔞ⁿ R⟨x_σ⟩` and agree on polynomials are equal:
every element agrees with a polynomial modulo that ideal. -/
public theorem coeffReduction_hom_ext {T : Type*} [CommRing T] (n : ℕ)
    (u w : AdicCompletion (𝔞.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R) →+* T)
    (hu : RingHom.ker (coeffReduction 𝔞 σ n).toRingHom ≤ RingHom.ker u)
    (hw : RingHom.ker (coeffReduction 𝔞 σ n).toRingHom ≤ RingHom.ker w)
    (he : u.comp (algebraMap (MvPolynomial σ R) _) =
      w.comp (algebraMap (MvPolynomial σ R) _)) : u = w := by
  refine RingHom.ext fun x => ?_
  obtain ⟨a, ha⟩ := MvPolynomial.map_surjective (σ := σ) (Ideal.Quotient.mk (𝔞 ^ n))
    Ideal.Quotient.mk_surjective (coeffReduction 𝔞 σ n x)
  have hx : x - algebraMap (MvPolynomial σ R) _ a ∈
      RingHom.ker (coeffReduction 𝔞 σ n).toRingHom := by
    rw [RingHom.sub_mem_ker_iff]
    change coeffReduction 𝔞 σ n x = coeffReduction 𝔞 σ n (algebraMap (MvPolynomial σ R) _ a)
    rw [coeffReduction_algebraMap, ha]
  exact ((RingHom.sub_mem_ker_iff u).mp (hu hx)).trans
    ((RingHom.congr_fun he a).trans ((RingHom.sub_mem_ker_iff w).mp (hw hx)).symm)

/-- **The coefficient reduction is natural in the variables.**  A continuous map of completed
polynomial algebras which fixes the coefficients and renames the variables along `v` reduces to
the renaming along `v`. -/
public theorem coeffReduction_naturality [IsNoetherianRing R] {τ : Type*} (v : σ → τ)
    (u : AdicCompletion (𝔞.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R) →+*
      AdicCompletion (𝔞.map (C : R →+* MvPolynomial τ R)) (MvPolynomial τ R))
    (hc : ∀ a : R, u (algebraMap R _ a) = algebraMap R _ a)
    (hv : ∀ i, u (algebraMap (MvPolynomial σ R) _ (X i)) =
      algebraMap (MvPolynomial τ R) _ (X (v i))) (n : ℕ) :
    (coeffReduction 𝔞 τ n).toRingHom.comp u =
      (MvPolynomial.rename v).toRingHom.comp (coeffReduction 𝔞 σ n).toRingHom := by
  refine coeffReduction_hom_ext 𝔞 σ n _ _ ?_ ?_ ?_
  · rw [← RingHom.comap_ker, ker_coeffReduction, ker_coeffReduction,
      ← Ideal.map_le_iff_le_comap, Ideal.map_pow, Ideal.map_map]
    rw [show u.comp (algebraMap R _) = algebraMap R _ from RingHom.ext hc]
  · intro x hx
    change MvPolynomial.rename v (coeffReduction 𝔞 σ n x) = 0
    rw [show coeffReduction 𝔞 σ n x = 0 from RingHom.mem_ker.mp hx, map_zero]
  · refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · change coeffReduction 𝔞 τ n (u (algebraMap R _ a)) =
        MvPolynomial.rename v (coeffReduction 𝔞 σ n
          (algebraMap (MvPolynomial σ R) _ (C a)))
      rw [hc, coeffReduction_coeff, coeffReduction_algebraMap, MvPolynomial.map_C,
        MvPolynomial.rename_C]
    · change coeffReduction 𝔞 τ n (u (algebraMap (MvPolynomial σ R) _ (X i))) =
        MvPolynomial.rename v (coeffReduction 𝔞 σ n
          (algebraMap (MvPolynomial σ R) _ (X i)))
      rw [hv, coeffReduction_algebraMap, coeffReduction_algebraMap, MvPolynomial.map_X,
        MvPolynomial.map_X, MvPolynomial.rename_X]

end CoeffReduction

/-! ## The reduced presentation `Sₙ = (R / 𝔞ⁿ)[x_σ] / (ker f)ₙ` -/

section ReducedGenerators

variable {R : Type*} [CommRing R] [IsNoetherianRing R] {S : Type*} [CommRing S] [Algebra R S]
  (𝔞 : Ideal R) (𝔟 : Ideal S) {σ : Type*}
  (f : AdicCompletion (𝔞.map (C : R →+* MvPolynomial σ R)) (MvPolynomial σ R) →ₐ[R] S)
  (hf : Function.Surjective f) (n : ℕ) [Algebra (R ⧸ 𝔞 ^ n) (S ⧸ 𝔟 ^ n)]
  (hb : 𝔞.map (algebraMap R S) = 𝔟)
  (hc : ∀ a : R, algebraMap (R ⧸ 𝔞 ^ n) (S ⧸ 𝔟 ^ n) (Ideal.Quotient.mk (𝔞 ^ n) a)
    = Ideal.Quotient.mk (𝔟 ^ n) (algebraMap R S a))

omit [Algebra (R ⧸ 𝔞 ^ n) (S ⧸ 𝔟 ^ n)] in
include hb in
/-- The presentation carries `𝔞ⁿ R⟨x_σ⟩`, the kernel of the coefficient reduction, onto `𝔟ⁿ`. -/
public theorem map_ker_coeffReduction_eq :
    (RingHom.ker (coeffReduction 𝔞 σ n).toRingHom).map f.toRingHom = 𝔟 ^ n := by
  rw [ker_coeffReduction, Ideal.map_pow, Ideal.map_map,
    show f.toRingHom.comp (algebraMap R _) = algebraMap R S from RingHom.ext f.commutes, hb]

omit [Algebra (R ⧸ 𝔞 ^ n) (S ⧸ 𝔟 ^ n)] in
include hb in
/-- The coefficient reduction's kernel is killed by the reduced presentation, so the latter
descends along it. -/
public theorem ker_coeffReduction_le_ker :
    RingHom.ker (coeffReduction 𝔞 σ n).toRingHom ≤
      RingHom.ker ((Ideal.Quotient.mk (𝔟 ^ n)).comp f.toRingHom) := by
  rw [← RingHom.comap_ker, Ideal.mk_ker, ← map_ker_coeffReduction_eq 𝔞 𝔟 f n hb]
  exact Ideal.le_comap_map

/-- **The reduced presentation map `(R / 𝔞ⁿ)[x_σ] → S / 𝔟ⁿ`.**  The coefficient reduction is
surjective with kernel `𝔞ⁿ R⟨x_σ⟩`, which `f` carries onto `𝔟ⁿ`, so `f` descends. -/
public def reducedRingHom : MvPolynomial σ (R ⧸ 𝔞 ^ n) →+* S ⧸ 𝔟 ^ n :=
  (coeffReduction 𝔞 σ n).toRingHom.liftOfSurjective (surjective_coeffReduction 𝔞 σ n)
    ⟨(Ideal.Quotient.mk (𝔟 ^ n)).comp f.toRingHom, ker_coeffReduction_le_ker 𝔞 𝔟 f n hb⟩

omit [Algebra (R ⧸ 𝔞 ^ n) (S ⧸ 𝔟 ^ n)] in
include hb in
/-- The defining square of the reduced presentation map. -/
public theorem reducedRingHom_comp :
    (reducedRingHom 𝔞 𝔟 f n hb).comp (coeffReduction 𝔞 σ n).toRingHom =
      (Ideal.Quotient.mk (𝔟 ^ n)).comp f.toRingHom :=
  RingHom.liftOfSurjective_comp ..

include hb hc in
/-- The reduced presentation map is an `Rₙ`-algebra map. -/
public theorem reducedRingHom_C (a : R ⧸ 𝔞 ^ n) :
    reducedRingHom 𝔞 𝔟 f n hb (C a) = algebraMap _ _ a := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  have he := RingHom.congr_fun (reducedRingHom_comp 𝔞 𝔟 f n hb) (algebraMap R _ a)
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at he
  rw [coeffReduction_coeff, f.commutes] at he
  rw [he, hc]

/-- The reduced presentation map as an `Rₙ`-algebra map. -/
public def reducedAlgHom : MvPolynomial σ (R ⧸ 𝔞 ^ n) →ₐ[R ⧸ 𝔞 ^ n] S ⧸ 𝔟 ^ n where
  __ := reducedRingHom 𝔞 𝔟 f n hb
  commutes' := reducedRingHom_C 𝔞 𝔟 f n hb hc

include hf hb in
/-- The reduced presentation map is surjective. -/
public theorem surjective_reducedAlgHom :
    Function.Surjective (reducedAlgHom 𝔞 𝔟 f n hb hc) := by
  intro y
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective.comp hf y
  exact ⟨coeffReduction 𝔞 σ n x,
    (RingHom.congr_fun (reducedRingHom_comp 𝔞 𝔟 f n hb) x).trans hx⟩

/-- **The reduced presentation `S / 𝔟ⁿ = (R / 𝔞ⁿ)[x_σ] / (ker f)ₙ`**, as a family of generators
indexed by the same variables as the presentation `f : R⟨x_σ⟩ ↠ S`.  This is the generic form of
the reduced presentation of Stacks 0AJS. -/
public def reducedGenerators : Algebra.Generators (R ⧸ 𝔞 ^ n) (S ⧸ 𝔟 ^ n) σ :=
  Algebra.Generators.ofAlgHom (reducedAlgHom 𝔞 𝔟 f n hb hc)
    (surjective_reducedAlgHom 𝔞 𝔟 f hf n hb hc)

include hf hb hc in
/-- The structure map of the reduced presentation is the reduced presentation map. -/
public theorem algebraMap_reducedGenerators :
    algebraMap (reducedGenerators 𝔞 𝔟 f hf n hb hc).Ring (S ⧸ 𝔟 ^ n) =
      reducedRingHom 𝔞 𝔟 f n hb := by
  change (MvPolynomial.aeval ((reducedAlgHom 𝔞 𝔟 f n hb hc) ∘ X)).toRingHom = _
  rw [show MvPolynomial.aeval ((reducedAlgHom 𝔞 𝔟 f n hb hc) ∘ X)
      = reducedAlgHom 𝔞 𝔟 f n hb hc by ext; simp]
  rfl

include hf hb hc in
/-- The generators are the classes of the images of the variables. -/
public theorem reducedGenerators_val (i : σ) :
    (reducedGenerators 𝔞 𝔟 f hf n hb hc).val i =
      Ideal.Quotient.mk _ (f (algebraMap (MvPolynomial σ R) _ (X i))) := by
  have he := RingHom.congr_fun (reducedRingHom_comp 𝔞 𝔟 f n hb)
    (algebraMap (MvPolynomial σ R) _ (X i))
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at he
  rw [coeffReduction_algebraMap, MvPolynomial.map_X] at he
  change reducedRingHom 𝔞 𝔟 f n hb (X i) = _
  exact he

omit [Algebra (R ⧸ 𝔞 ^ n) (S ⧸ 𝔟 ^ n)] in
include hf hb in
/-- **The ideal of the reduced presentation is the image of `ker f`.**  Modulo the kernel of the
coefficient reduction, which the presentation carries onto `𝔟ⁿ`, the two ideals have the same
preimage in `R⟨x_σ⟩`. -/
public theorem ker_reducedRingHom :
    RingHom.ker (reducedRingHom 𝔞 𝔟 f n hb) =
      (RingHom.ker f.toRingHom).map (coeffReduction 𝔞 σ n).toRingHom := by
  refine Ideal.comap_injective_of_surjective (coeffReduction 𝔞 σ n).toRingHom
    (surjective_coeffReduction 𝔞 σ n) ?_
  rw [RingHom.comap_ker, reducedRingHom_comp, ← RingHom.comap_ker, Ideal.mk_ker,
    ← map_ker_coeffReduction_eq 𝔞 𝔟 f n hb, Ideal.comap_map_of_surjective f.toRingHom hf,
    Ideal.comap_map_of_surjective (coeffReduction 𝔞 σ n).toRingHom
      (surjective_coeffReduction 𝔞 σ n), sup_comm]
  rfl

include hf hb hc in
/-- The ideal of the reduced presentation, as an ideal of `Rₙ[x_σ]`. -/
public theorem reducedGenerators_ker :
    (reducedGenerators 𝔞 𝔟 f hf n hb hc).ker =
      (RingHom.ker f.toRingHom).map (coeffReduction 𝔞 σ n).toRingHom := by
  have h1 : (reducedGenerators 𝔞 𝔟 f hf n hb hc).ker
      = RingHom.ker (reducedRingHom 𝔞 𝔟 f n hb) :=
    congrArg RingHom.ker (algebraMap_reducedGenerators 𝔞 𝔟 f hf n hb hc)
  rw [h1, ker_reducedRingHom 𝔞 𝔟 f hf n hb]

end ReducedGenerators

/-! ## The coefficient reduction of a presentation is the library's `reductionAlgHom` -/

namespace CompletedPolynomialPresentation

universe u v

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
  {B : AdicFiniteTypeAlgebra.{u, v} A I} (P : CompletedPolynomialPresentation I B)

/-- `Rig.coeffReduction`, at the base pair and the variables of a presentation, is the
coefficient reduction `Rig.CompletedPolynomialPresentation.reductionAlgHom` of Stacks 0AJS. -/
public theorem reductionAlgHom_eq_coeffReduction (n : ℕ) :
    (P.reductionAlgHom n).toRingHom = (coeffReduction I (Fin P.variableCount) n).toRingHom := by
  refine coeffReduction_hom_ext I (Fin P.variableCount) n _ _ ?_ le_rfl ?_
  · rw [ker_coeffReduction, ← Ideal.map_pow]
    exact P.adicPow_le_ker_reductionAlgHom n
  · refine RingHom.ext fun q => ?_
    change P.reductionAlgHom n
        (algebraMap (MvPolynomial (Fin P.variableCount) A) P.completedPolynomialRing q) =
      coeffReduction I (Fin P.variableCount) n (algebraMap _ _ q)
    rw [P.reductionAlgHom_polynomial n q, coeffReduction_algebraMap]

end CompletedPolynomialPresentation

/-! ## The index bookkeeping of the combined presentation -/

/-- The renaming of variables between the combined presentation of Stacks 0ALM, whose variables
are `Fin (r + s)` split by `Fin.castAdd`/`Fin.natAdd`, and the composite of two families of
generators, which `Algebra.Generators.comp` indexes by `Fin s ⊕ Fin r` with the fiber variables
on the left. -/
public def combinedIndex (r s : ℕ) : Fin (r + s) → Fin s ⊕ Fin r :=
  Fin.addCases (fun i => Sum.inr i) (fun j => Sum.inl j)

/-- `combinedIndex` sends `Fin.castAdd s i` to the base variable `Sum.inr i`. -/
@[simp] public theorem combinedIndex_castAdd (r s : ℕ) (i : Fin r) :
    combinedIndex r s (Fin.castAdd s i) = Sum.inr i :=
  Fin.addCases_left i

/-- `combinedIndex` sends `Fin.natAdd r j` to the fiber variable `Sum.inl j`. -/
@[simp] public theorem combinedIndex_natAdd (r s : ℕ) (j : Fin s) :
    combinedIndex r s (Fin.natAdd r j) = Sum.inl j :=
  Fin.addCases_right j

/-! ## Two tensor identifications -/

/-- `C ⊗_R N ≃ C ⊗_S N` when `R → S` is surjective: the two scalar actions on `N` agree. -/
public def tensorOverSurjectionEquiv (R S D : Type*) [CommRing R] [CommRing S] [CommRing D]
    [Algebra R S] [Algebra R D] [Algebra S D] [IsScalarTower R S D]
    (N : Type*) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (h : Function.Surjective (algebraMap R S)) : D ⊗[R] N ≃ₗ[D] D ⊗[S] N := by
  let : TensorProduct.CompatibleSMul R S D N := ⟨fun s c x ↦ by
    obtain ⟨r, rfl⟩ := h s
    simp only [algebraMap_smul, TensorProduct.smul_tmul]⟩
  exact (TensorProduct.equivOfCompatibleSMul R S D D N).symm

/-- `tensorOverSurjectionEquiv` sends `c ⊗ₜ[R] x` to `c ⊗ₜ[S] x`. -/
@[simp] public theorem tensorOverSurjectionEquiv_tmul (R S D : Type*) [CommRing R] [CommRing S]
    [CommRing D] [Algebra R S] [Algebra R D] [Algebra S D] [IsScalarTower R S D]
    (N : Type*) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (h : Function.Surjective (algebraMap R S)) (c : D) (x : N) :
    tensorOverSurjectionEquiv R S D N h (c ⊗ₜ[R] x) = c ⊗ₜ[S] x := rfl

/-- `D ⊗_{P.Ring} J ≃ D ⊗_S (J / J²)` for an extension `P` of `S` with kernel `J`: the
conormal module is `J ⊗_{P.Ring} S`. -/
public def conormalTensorEquiv {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension R S) (D : Type*) [CommRing D]
    [Algebra S D] [Algebra P.Ring D] [IsScalarTower P.Ring S D] :
    D ⊗[P.Ring] P.ker ≃ₗ[D] D ⊗[S] P.Cotangent :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange P.Ring S D D P.ker).symm ≪≫ₗ
    P.cotangentEquiv.baseChange (A := D)

/-- `conormalTensorEquiv` sends `c ⊗ₜ x` to `c ⊗ₜ Cotangent.mk x`. -/
@[simp] public theorem conormalTensorEquiv_tmul {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (P : Algebra.Extension R S) (D : Type*) [CommRing D]
    [Algebra S D] [Algebra P.Ring D] [IsScalarTower P.Ring S D] (c : D) (x : P.ker) :
    conormalTensorEquiv P D (c ⊗ₜ[P.Ring] x) = c ⊗ₜ[S] Algebra.Extension.Cotangent.mk x := by
  simp only [conormalTensorEquiv, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    LinearEquiv.baseChange_tmul, Algebra.Extension.cotangentEquiv_tmul, one_smul]

/-! ## Vanishing in a Hausdorff tensor product -/

/-- The kernel of a tensor product of two surjections with small kernels is small. -/
public theorem tensorProduct_map_ker_le_smul {R : Type*} [CommRing R] {M N M' N' : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
    [Module R M] [Module R N] [Module R M'] [Module R N']
    (𝔞 : Ideal R) (u : M →ₗ[R] M') (w : N →ₗ[R] N')
    (hu : Function.Surjective u) (hw : Function.Surjective w)
    (huk : u.ker ≤ 𝔞 • ⊤) (hwk : w.ker ≤ 𝔞 • ⊤) :
    (TensorProduct.map u w).ker ≤ 𝔞 • ⊤ := by
  rw [TensorProduct.map_ker (LinearMap.exact_subtype_ker_map u) hu
    (LinearMap.exact_subtype_ker_map w) hw]
  have key : ∀ (x : M) (y : N), x ∈ u.ker ∨ y ∈ w.ker → x ⊗ₜ[R] y ∈ 𝔞 • (⊤ : Submodule R _) := by
    rintro x y (hx | hy)
    · have hm := Submodule.mem_map_of_mem (f := (TensorProduct.mk R M N).flip y) (huk hx)
      rw [Submodule.map_smul''] at hm
      exact (Submodule.smul_mono le_rfl le_top) hm
    · have hm := Submodule.mem_map_of_mem (f := TensorProduct.mk R M N x) (hwk hy)
      rw [Submodule.map_smul''] at hm
      exact (Submodule.smul_mono le_rfl le_top) hm
  refine sup_le ?_ ?_ <;>
    simp only [LinearMap.lTensor_def, LinearMap.rTensor_def,
      TensorProduct.range_map_eq_span_tmul, Submodule.span_le]
  all_goals rintro _ ⟨x, y, rfl⟩
  · exact key _ _ (Or.inr y.2)
  · exact key _ _ (Or.inl x.2)

/-- **An element of a Hausdorff tensor product killed by every pair of reductions is zero.**
Here `M ⊗ N` is `𝔞`-adically Hausdorff, and the two inverse systems of reductions have kernels
that shrink into every power of `𝔞`. -/
public theorem tensorProduct_eq_zero_of_adic_projections {R : Type*} [CommRing R]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (𝔞 : Ideal R) [IsHausdorff 𝔞 (M ⊗[R] N)]
    {M' N' : ℕ → Type*} [∀ n, AddCommGroup (M' n)] [∀ n, AddCommGroup (N' n)]
    [∀ n, Module R (M' n)] [∀ n, Module R (N' n)]
    (u : ∀ n, M →ₗ[R] M' n) (w : ∀ n, N →ₗ[R] N' n)
    (hu : ∀ n, Function.Surjective (u n)) (hw : ∀ n, Function.Surjective (w n))
    (hk : ∀ k, ∃ n, (u n).ker ≤ 𝔞 ^ k • ⊤ ∧ (w n).ker ≤ 𝔞 ^ k • ⊤)
    (x : M ⊗[R] N) (hx : ∀ n, TensorProduct.map (u n) (w n) x = 0) :
    x = 0 := by
  refine (IsHausdorff.eq_iff_smodEq (I := 𝔞)).mpr fun k => ?_
  obtain ⟨n, hn, hn'⟩ := hk k
  exact SModEq.zero.mpr
    (tensorProduct_map_ker_le_smul (𝔞 ^ k) (u n) (w n) (hu n) (hw n) hn hn' (hx n))

/-- **Artin–Rees for the reductions of an ideal.**  There is a single `c` such that for every
`k`, the kernel of `J → J·Sₙ` lies in `𝔞ᵏ·J` as soon as `n ≥ k + c`, where `Sₙ` is any family
of `R`-algebras whose structure maps kill `𝔞ⁿ`.  The shift `c` is the Artin–Rees constant of
Stacks 00IN. -/
public theorem exists_ker_idealMap_le_pow_smul {R : Type*} [CommRing R] [IsNoetherianRing R]
    (𝔞 J : Ideal R) {S : ℕ → Type*} [∀ n, CommRing (S n)] [∀ n, Algebra R (S n)]
    (h : ∀ n, RingHom.ker (algebraMap R (S n)) ≤ 𝔞 ^ n) :
    ∃ c : ℕ, ∀ k n, k + c ≤ n → (Algebra.idealMap (S n) J).ker ≤ 𝔞 ^ k • ⊤ := by
  obtain ⟨c, hc⟩ := 𝔞.exists_pow_inf_eq_pow_smul (J : Submodule R R)
  refine ⟨c, fun k n hn x hx ↦ ?_⟩
  have hxI : (x : R) ∈ 𝔞 ^ n := h n (congrArg Subtype.val hx)
  have hx' : (x : R) ∈ 𝔞 ^ n • (⊤ : Submodule R R) ⊓ J := by
    simpa only [smul_eq_mul, Ideal.mul_top, Submodule.mem_inf] using And.intro hxI x.property
  rw [hc n (by omega)] at hx'
  have hx'' : (x : R) ∈ 𝔞 ^ k • J :=
    (Submodule.smul_mono (Ideal.pow_le_pow_right (by omega)) inf_le_right) hx'
  have he : (𝔞 ^ k • (⊤ : Submodule R J)).map J.subtype = 𝔞 ^ k • J := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  rw [← he] at hx''
  obtain ⟨y, hy, hyx⟩ := hx''
  exact (Subtype.ext hyx : y = x) ▸ hy

/-! ## The reductions `Bₙ → Cₙ` of a morphism of (0AL4) -/

section ReductionMap

universe u v

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- **The reduction `Bₙ → Cₙ` of a morphism of (0AL4)**, that is `B / IⁿB → C / IⁿC`.  It is
well defined because `IⁿB` maps into `IⁿC`. -/
public def reductionMap (B C : AdicFiniteTypeAlgebra.{u, v} A I) [Algebra B.carrier C.carrier]
    [IsScalarTower A B.carrier C.carrier] (n : ℕ) :
    (B.carrier ⧸ B.adicIdeal ^ n) →+* (C.carrier ⧸ C.adicIdeal ^ n) :=
  Ideal.quotientMap (C.adicIdeal ^ n) (algebraMap B.carrier C.carrier)
    (Ideal.map_le_iff_le_comap.mp
      (by rw [Ideal.map_pow, AdicFiniteTypeAlgebra.map_adicIdeal_tower]))

/-- `reductionMap` sends the class of `b` to the class of its image in `C`. -/
@[simp] public theorem reductionMap_mk (B C : AdicFiniteTypeAlgebra.{u, v} A I)
    [Algebra B.carrier C.carrier] [IsScalarTower A B.carrier C.carrier] (n : ℕ)
    (b : B.carrier) :
    reductionMap B C n (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk _ (algebraMap B.carrier C.carrier b) :=
  rfl

/-- `Bₙ = B / IⁿB` as an algebra over `Aₙ = A / Iⁿ`. -/
@[instance_reducible]
public def baseReductionAlgebra (B : AdicFiniteTypeAlgebra.{u, v} A I) (n : ℕ) :
    Algebra (A ⧸ I ^ n) (B.carrier ⧸ B.adicIdeal ^ n) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.map_le_iff_le_comap.mp (by rw [Ideal.map_pow]))

attribute [local instance] baseReductionAlgebra

/-- `Cₙ` as an algebra over `Bₙ`, through the reduction of `B → C`. -/
@[instance_reducible]
public def fiberReductionAlgebra (B C : AdicFiniteTypeAlgebra.{u, v} A I)
    [Algebra B.carrier C.carrier] [IsScalarTower A B.carrier C.carrier] (n : ℕ) :
    Algebra (B.carrier ⧸ B.adicIdeal ^ n) (C.carrier ⧸ C.adicIdeal ^ n) :=
  (reductionMap B C n).toAlgebra

attribute [local instance] fiberReductionAlgebra

/-- **`Aₙ → Bₙ → Cₙ` is a tower.**  Both composites send the class of `a ∈ A` to the class of
its image in `C`. -/
public theorem isScalarTower_reductionMap (B C : AdicFiniteTypeAlgebra.{u, v} A I)
    [Algebra B.carrier C.carrier] [IsScalarTower A B.carrier C.carrier] (n : ℕ) :
    IsScalarTower (A ⧸ I ^ n) (B.carrier ⧸ B.adicIdeal ^ n) (C.carrier ⧸ C.adicIdeal ^ n) := by
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact congrArg (Ideal.Quotient.mk (C.adicIdeal ^ n))
    (IsScalarTower.algebraMap_apply A B.carrier C.carrier a)

attribute [local instance] isScalarTower_reductionMap

/-- `A → Aₙ → Cₙ` is a tower. -/
public theorem isScalarTower_baseReduction (C : AdicFiniteTypeAlgebra.{u, v} A I) (n : ℕ) :
    IsScalarTower A (A ⧸ I ^ n) (C.carrier ⧸ C.adicIdeal ^ n) :=
  .of_algebraMap_eq fun _ ↦ rfl

attribute [local instance] isScalarTower_baseReduction

/-! ## The reduced presentations of `B` over `A` and of `C` over `B` -/

variable [IsNoetherianRing A] {B : AdicFiniteTypeAlgebra.{u, v} A I}
  (P : CompletedPolynomialPresentation I B) (s : ℕ)
  {C : AdicFiniteTypeAlgebra.{u, v} A I} [Algebra B.carrier C.carrier]
  [IsScalarTower A B.carrier C.carrier]
  (ψ : AdicCompletion.completedMvPolynomial B.adicIdeal (Fin s) →ₐ[B.carrier] C.carrier)
  (hψ : Function.Surjective (ψ.restrictScalars A))

namespace CompletedPolynomialPresentation

/-- **The reduced presentation `Bₙ = Aₙ[x₁, …, x_r] / Jₙ`** of Stacks 0AJS, in the spelling in
which `Bₙ` is `B / (IB)ⁿ`. -/
public def baseReducedGenerators (n : ℕ) :
    Algebra.Generators (A ⧸ I ^ n) (B.carrier ⧸ B.adicIdeal ^ n) (Fin P.variableCount) :=
  reducedGenerators I B.adicIdeal P.toAlgHom P.toAlgHom_surjective n rfl (fun _ => rfl)

/-- **The reduced presentation `Cₙ = Bₙ[y₁, …, y_s] / J'ₙ`** of the presentation of `C` over
`B`. -/
public def fiberReducedGenerators (n : ℕ) :
    Algebra.Generators (B.carrier ⧸ B.adicIdeal ^ n) (C.carrier ⧸ C.adicIdeal ^ n) (Fin s) :=
  reducedGenerators B.adicIdeal C.adicIdeal ψ hψ n
    AdicFiniteTypeAlgebra.map_adicIdeal_tower (fun _ => rfl)

/-- The generators of `Bₙ` are the classes of the images of the variables `xᵢ`. -/
public theorem baseReducedGenerators_val (n : ℕ) (i : Fin P.variableCount) :
    (P.baseReducedGenerators n).val i =
      Ideal.Quotient.mk _ (P.toAlgHom (algebraMap (MvPolynomial (Fin P.variableCount) A)
        P.completedPolynomialRing (X i))) :=
  reducedGenerators_val I B.adicIdeal P.toAlgHom P.toAlgHom_surjective n rfl (fun _ => rfl) i

/-- The generators of `Cₙ` are the classes of the images of the variables `yⱼ`. -/
public theorem fiberReducedGenerators_val (n : ℕ) (j : Fin s) :
    (fiberReducedGenerators s ψ hψ n).val j =
      Ideal.Quotient.mk _ (ψ (algebraMap (MvPolynomial (Fin s) B.carrier)
        (AdicCompletion.completedMvPolynomial B.adicIdeal (Fin s)) (X j))) :=
  reducedGenerators_val B.adicIdeal C.adicIdeal ψ hψ n
    AdicFiniteTypeAlgebra.map_adicIdeal_tower (fun _ => rfl) j

/-- The ideal of the reduced presentation of `B` is the image of `J`. -/
public theorem baseReducedGenerators_ker (n : ℕ) :
    (P.baseReducedGenerators n).ker =
      P.extension.ker.map (coeffReduction I (Fin P.variableCount) n).toRingHom :=
  reducedGenerators_ker I B.adicIdeal P.toAlgHom P.toAlgHom_surjective n rfl (fun _ => rfl)

/-! ## The reduction of the combined presentation -/

/-- The reduction of the combined presentation `C = A⟨x, y⟩ / K` of Stacks 0ALM: reduce the
coefficients modulo `Iⁿ` and rename the variables into the indexing
`Algebra.Generators.comp` uses. -/
public def reducedCombinedMap (n : ℕ) :
    AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin (P.variableCount + s)) A))
        (MvPolynomial (Fin (P.variableCount + s)) A) →+*
      ((fiberReducedGenerators s ψ hψ n).comp (P.baseReducedGenerators n)).Ring :=
  (MvPolynomial.rename (combinedIndex P.variableCount s)).toRingHom.comp
    (coeffReduction I (Fin (P.variableCount + s)) n).toRingHom

/-- The inclusion of the inner variables sends the variable `xᵢ` to `x_{castAdd i}`. -/
private theorem combinedInclusion_algebraMap_X (i : Fin P.variableCount) :
    P.combinedInclusion s (algebraMap (MvPolynomial (Fin P.variableCount) A) _ (X i)) =
      algebraMap (MvPolynomial (Fin (P.variableCount + s)) A)
        (AdicCompletion (I.map (MvPolynomial.C :
          A →+* MvPolynomial (Fin (P.variableCount + s)) A))
          (MvPolynomial (Fin (P.variableCount + s)) A)) (X (Fin.castAdd s i)) := by
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply,
    AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply]
  exact P.combinedInclusion_of_X s i

/-- The inclusion of the inner variables commutes with the reduction: its reduction is the
inclusion `Aₙ[x] → Aₙ[y, x]` of `Algebra.Generators.toComp`. -/
public theorem reducedCombinedMap_base (n : ℕ) :
    (P.reducedCombinedMap s ψ hψ n).comp (P.combinedInclusion s).toRingHom =
      ((fiberReducedGenerators s ψ hψ n).toComp
          (P.baseReducedGenerators n)).toAlgHom.toRingHom.comp
        (coeffReduction I (Fin P.variableCount) n).toRingHom := by
  refine RingHom.ext fun z => ?_
  change MvPolynomial.rename (combinedIndex P.variableCount s)
      (coeffReduction I (Fin (P.variableCount + s)) n (P.combinedInclusion s z)) =
    ((fiberReducedGenerators s ψ hψ n).toComp (P.baseReducedGenerators n)).toAlgHom
      (coeffReduction I (Fin P.variableCount) n z)
  rw [show coeffReduction I (Fin (P.variableCount + s)) n (P.combinedInclusion s z) =
      MvPolynomial.rename (Fin.castAdd s) (coeffReduction I (Fin P.variableCount) n z) from
    RingHom.congr_fun (coeffReduction_naturality I (Fin P.variableCount) (Fin.castAdd s)
      (P.combinedInclusion s).toRingHom
      (fun a => (P.combinedInclusion s).commutes a) (P.combinedInclusion_algebraMap_X s) n) z,
    Algebra.Generators.toComp_toAlgHom, MvPolynomial.rename_rename,
    show combinedIndex P.variableCount s ∘ Fin.castAdd s =
        (Sum.inr : Fin P.variableCount → Fin s ⊕ Fin P.variableCount) from
      funext fun i => combinedIndex_castAdd P.variableCount s i]

/-- Applying the reduction of the combined presentation: reduce the coefficients, then rename
the variables. -/
@[simp] public theorem reducedCombinedMap_apply (n : ℕ)
    (x : AdicCompletion (I.map (MvPolynomial.C :
        A →+* MvPolynomial (Fin (P.variableCount + s)) A))
      (MvPolynomial (Fin (P.variableCount + s)) A)) :
    P.reducedCombinedMap s ψ hψ n x =
      MvPolynomial.rename (combinedIndex P.variableCount s)
        (coeffReduction I (Fin (P.variableCount + s)) n x) :=
  rfl

/-- **Both readings of a variable of the combined presentation in `Cₙ` agree.**  For an inner
variable this is the inclusion-of-variables square of Stacks 0ALM; for an outer variable it is
`Rig.CompletedPolynomialPresentation.combinedProjection_of_X_natAdd`. -/
public theorem algebraMap_combinedVariable (n : ℕ) (k : Fin (P.variableCount + s)) :
    algebraMap ((fiberReducedGenerators s ψ hψ n).comp (P.baseReducedGenerators n)).Ring
        (C.carrier ⧸ C.adicIdeal ^ n) (X (combinedIndex P.variableCount s k)) =
      Ideal.Quotient.mk (C.adicIdeal ^ n)
        ((P.combinedPresentation s (ψ.restrictScalars A) hψ).toAlgHom
          (algebraMap (MvPolynomial (Fin (P.variableCount + s)) A)
            (AdicCompletion (I.map (MvPolynomial.C :
              A →+* MvPolynomial (Fin (P.variableCount + s)) A))
              (MvPolynomial (Fin (P.variableCount + s)) A)) (X k))) := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · rw [combinedIndex_castAdd, ← P.combinedInclusion_algebraMap_X s i,
      P.toAlgHom_combinedInclusion s ψ hψ,
      Algebra.Generators.algebraMap_apply, MvPolynomial.aeval_X,
      Algebra.Generators.comp_val, Sum.elim_inr, Function.comp_apply,
      P.baseReducedGenerators_val n i]
    rfl
  · have hX : algebraMap (MvPolynomial (Fin (P.variableCount + s)) A)
          (AdicCompletion (I.map (MvPolynomial.C :
            A →+* MvPolynomial (Fin (P.variableCount + s)) A))
            (MvPolynomial (Fin (P.variableCount + s)) A))
          (X (Fin.natAdd P.variableCount j)) =
        AdicCompletion.of (I.map (MvPolynomial.C :
            A →+* MvPolynomial (Fin (P.variableCount + s)) A))
          (MvPolynomial (Fin (P.variableCount + s)) A)
          (X (Fin.natAdd P.variableCount j)) := by
      rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply]
    have hψX : (P.combinedPresentation s (ψ.restrictScalars A) hψ).toAlgHom
          (AdicCompletion.of (I.map (MvPolynomial.C :
              A →+* MvPolynomial (Fin (P.variableCount + s)) A))
            (MvPolynomial (Fin (P.variableCount + s)) A)
            (X (Fin.natAdd P.variableCount j))) =
        ψ (algebraMap (MvPolynomial (Fin s) B.carrier)
          (AdicCompletion.completedMvPolynomial B.adicIdeal (Fin s)) (X j)) := by
      change ψ (P.combinedProjection s (AdicCompletion.of _
        (MvPolynomial (Fin (P.variableCount + s)) A)
        (X (Fin.natAdd P.variableCount j)))) = _
      rw [P.combinedProjection_of_X_natAdd s j, AdicCompletion.algebraMap_apply,
        Algebra.algebraMap_self_apply]
    rw [combinedIndex_natAdd, hX, hψX, Algebra.Generators.algebraMap_apply,
      MvPolynomial.aeval_X, Algebra.Generators.comp_val, Sum.elim_inl,
      fiberReducedGenerators_val (B := B) s ψ hψ n j]

/-- The two readings agree on the constants: both send `a ∈ A` to the class of its image
in `C`. -/
public theorem reducedCombinedMap_toC_C (n : ℕ) (a : A) :
    algebraMap ((fiberReducedGenerators s ψ hψ n).comp (P.baseReducedGenerators n)).Ring
        (C.carrier ⧸ C.adicIdeal ^ n)
        (P.reducedCombinedMap s ψ hψ n
          (algebraMap (MvPolynomial (Fin (P.variableCount + s)) A)
            (AdicCompletion (I.map (MvPolynomial.C :
              A →+* MvPolynomial (Fin (P.variableCount + s)) A))
              (MvPolynomial (Fin (P.variableCount + s)) A)) (MvPolynomial.C a))) =
      Ideal.Quotient.mk (C.adicIdeal ^ n)
        ((P.combinedPresentation s (ψ.restrictScalars A) hψ).toAlgHom
          (algebraMap (MvPolynomial (Fin (P.variableCount + s)) A)
            (AdicCompletion (I.map (MvPolynomial.C :
              A →+* MvPolynomial (Fin (P.variableCount + s)) A))
              (MvPolynomial (Fin (P.variableCount + s)) A)) (MvPolynomial.C a))) := by
  have hcom : (P.combinedPresentation s (ψ.restrictScalars A) hψ).toAlgHom
      (algebraMap A (AdicCompletion (I.map (MvPolynomial.C :
        A →+* MvPolynomial (Fin (P.variableCount + s)) A))
        (MvPolynomial (Fin (P.variableCount + s)) A)) a) = algebraMap A C.carrier a :=
    (P.combinedPresentation s (ψ.restrictScalars A) hψ).toAlgHom.commutes a
  rw [show (MvPolynomial.C a : MvPolynomial (Fin (P.variableCount + s)) A) =
      algebraMap A (MvPolynomial (Fin (P.variableCount + s)) A) a from rfl,
    ← IsScalarTower.algebraMap_apply, reducedCombinedMap_apply, coeffReduction_coeff,
    MvPolynomial.rename_C, Algebra.Generators.algebraMap_apply, MvPolynomial.aeval_C, hcom]
  rfl

/-- The two readings agree on the variables. -/
public theorem reducedCombinedMap_toC_X (n : ℕ) (k : Fin (P.variableCount + s)) :
    algebraMap ((fiberReducedGenerators s ψ hψ n).comp (P.baseReducedGenerators n)).Ring
        (C.carrier ⧸ C.adicIdeal ^ n)
        (P.reducedCombinedMap s ψ hψ n
          (algebraMap (MvPolynomial (Fin (P.variableCount + s)) A)
            (AdicCompletion (I.map (MvPolynomial.C :
              A →+* MvPolynomial (Fin (P.variableCount + s)) A))
              (MvPolynomial (Fin (P.variableCount + s)) A)) (X k))) =
      Ideal.Quotient.mk (C.adicIdeal ^ n)
        ((P.combinedPresentation s (ψ.restrictScalars A) hψ).toAlgHom
          (algebraMap (MvPolynomial (Fin (P.variableCount + s)) A)
            (AdicCompletion (I.map (MvPolynomial.C :
              A →+* MvPolynomial (Fin (P.variableCount + s)) A))
              (MvPolynomial (Fin (P.variableCount + s)) A)) (X k))) := by
  rw [reducedCombinedMap_apply, coeffReduction_algebraMap, MvPolynomial.map_X,
    MvPolynomial.rename_X]
  exact P.algebraMap_combinedVariable s ψ hψ n k

/-- The reduction of the combined presentation is a map of presentations: it commutes with the
two maps onto `Cₙ`. -/
public theorem reducedCombinedMap_toC (n : ℕ) :
    (algebraMap ((fiberReducedGenerators s ψ hψ n).comp (P.baseReducedGenerators n)).Ring
        (C.carrier ⧸ C.adicIdeal ^ n)).comp (P.reducedCombinedMap s ψ hψ n) =
      (Ideal.Quotient.mk (C.adicIdeal ^ n)).comp
        (P.combinedPresentation s (ψ.restrictScalars A) hψ).toAlgHom.toRingHom := by
  refine coeffReduction_hom_ext I (Fin (P.variableCount + s)) n _ _ ?_ ?_ ?_
  · intro x hx
    change algebraMap ((fiberReducedGenerators s ψ hψ n).comp (P.baseReducedGenerators n)).Ring
        (C.carrier ⧸ C.adicIdeal ^ n) (MvPolynomial.rename (combinedIndex P.variableCount s)
          (coeffReduction I (Fin (P.variableCount + s)) n x)) = 0
    rw [show coeffReduction I (Fin (P.variableCount + s)) n x = 0 from RingHom.mem_ker.mp hx,
      map_zero, map_zero]
  · intro x hx
    have hx0 : (P.combinedPresentation s (ψ.restrictScalars A) hψ).reductionAlgHom n x = 0 :=
      (RingHom.congr_fun
        ((P.combinedPresentation s (ψ.restrictScalars A) hψ).reductionAlgHom_eq_coeffReduction n)
        x).trans (RingHom.mem_ker.mp hx)
    have hx' : x ∈ (P.combinedPresentation s (ψ.restrictScalars A) hψ).completedAdicPow n :=
      ((P.combinedPresentation s (ψ.restrictScalars A) hψ).ker_reductionAlgHom n).le
        (RingHom.mem_ker.mpr hx0)
    have hmem := (P.combinedPresentation s (ψ.restrictScalars A) hψ).toAlgHom_mem_adicIdealPow hx'
    rw [AdicFiniteTypeAlgebra.adicIdealPow_eq] at hmem
    have hgoal : (Ideal.Quotient.mk (C.adicIdeal ^ n))
        ((P.combinedPresentation s (ψ.restrictScalars A) hψ).toAlgHom x) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    exact hgoal
  · exact MvPolynomial.ringHom_ext (P.reducedCombinedMap_toC_C s ψ hψ n)
      (P.reducedCombinedMap_toC_X s ψ hψ n)

/-- The reduction of the combined presentation, as a morphism of extensions from
`C = A⟨x, y⟩ / K` to its reduction `Cₙ = Aₙ[y, x] / Kₙ`. -/
public def reducedCombinedHom (n : ℕ) :
    (P.combinedPresentation s (ψ.restrictScalars A) hψ).extension.Hom
      ((fiberReducedGenerators s ψ hψ n).comp (P.baseReducedGenerators n)).toExtension where
  toRingHom := P.reducedCombinedMap s ψ hψ n
  toRingHom_algebraMap a := by
    change MvPolynomial.rename (combinedIndex P.variableCount s)
      (coeffReduction I (Fin (P.variableCount + s)) n (algebraMap A _ a)) = _
    rw [coeffReduction_coeff, MvPolynomial.rename_C]
    rfl
  algebraMap_toRingHom x := RingHom.congr_fun (P.reducedCombinedMap_toC s ψ hψ n) x

/-! ## Stacks 0AQJ -/

/-- The structure map of the reduced presentation of `B` is the coefficient reduction followed
by the presentation of `B`. -/
private theorem algebraMap_baseReducedGenerators_coeffReduction (n : ℕ) (y : P.extension.Ring) :
    algebraMap (P.baseReducedGenerators n).toExtension.Ring (B.carrier ⧸ B.adicIdeal ^ n)
        (coeffReduction I (Fin P.variableCount) n y) =
      Ideal.Quotient.mk (B.adicIdeal ^ n) (P.toAlgHom y) := by
  have h1 : algebraMap (P.baseReducedGenerators n).toExtension.Ring
        (B.carrier ⧸ B.adicIdeal ^ n) (coeffReduction I (Fin P.variableCount) n y) =
      algebraMap (P.baseReducedGenerators n).Ring (B.carrier ⧸ B.adicIdeal ^ n)
        (coeffReduction I (Fin P.variableCount) n y) := rfl
  rw [h1]
  exact (RingHom.congr_fun (algebraMap_reducedGenerators I B.adicIdeal P.toAlgHom
      P.toAlgHom_surjective n rfl (fun _ => rfl)) _).trans
    (RingHom.congr_fun (reducedRingHom_comp I B.adicIdeal P.toAlgHom n rfl) y)

/-- **The comparison `C ⊗_B J/J² → K/K²` of Stacks 0ALM is injective** when every reduction
`Bₙ → Cₙ` is a local complete intersection homomorphism.  This is the assertion of Stacks 0AQJ
one degree before passing to `H⁻¹`.

The proof is the source's.  The module `C ⊗_{A⟨x⟩} J` is `I`-adically Hausdorff because `C` is
`I`-adically complete, so an element is zero as soon as it dies in every pair of reductions
`C ↠ Cₙ`, `J ↠ Jₙ`, and the reductions of `J` shrink into every power of `I` by Artin–Rees
(`Rig.exists_ker_idealMap_le_pow_smul`).  At level `n` the comparison becomes the conormal
comparison of the reduced presentations `Bₙ = Aₙ[x] / Jₙ` and `Cₙ = Bₙ[y] / J'ₙ`, which is
injective by Stacks 07D4. -/
public theorem injective_cotangentMap_innerExtensionHom_of_lci
    (h : ∀ n : ℕ, RingHom.IsLocalCompleteIntersection (reductionMap B C (n + 1))) :
    Function.Injective
      ((Algebra.Extension.Cotangent.map (P.innerExtensionHom s ψ hψ)).liftBaseChange
        C.carrier) := by
  have : IsNoetherianRing P.extension.Ring :=
    AdicCompletion.isNoetherianRing
      (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin P.variableCount) A))
  have : Module.Finite P.extension.Ring P.extension.ker :=
    Module.Finite.of_fg P.extension.ker.fg_of_isNoetherianRing
  let : Algebra P.extension.Ring C.carrier :=
    ((algebraMap B.carrier C.carrier).comp (algebraMap P.extension.Ring B.carrier)).toAlgebra
  have : IsScalarTower P.extension.Ring B.carrier C.carrier := .of_algebraMap_eq fun _ => rfl
  have hH : (I.map (algebraMap A P.extension.Ring)).map
      (algebraMap P.extension.Ring C.carrier) = C.adicIdeal := by
    have he : (algebraMap P.extension.Ring C.carrier).comp (algebraMap A P.extension.Ring) =
        algebraMap A C.carrier := by
      refine RingHom.ext fun a => ?_
      change algebraMap B.carrier C.carrier (algebraMap P.extension.Ring B.carrier
        (algebraMap A P.extension.Ring a)) = algebraMap A C.carrier a
      rw [show algebraMap P.extension.Ring B.carrier (algebraMap A P.extension.Ring a) =
          algebraMap A B.carrier a from P.toAlgHom.commutes a, ← IsScalarTower.algebraMap_apply]
    rw [Ideal.map_map, he]
  have : IsAdicComplete C.adicIdeal C.carrier := C.isAdicallyComplete
  have : IsHausdorff C.adicIdeal (C.carrier ⊗[P.extension.Ring] P.extension.ker) :=
    IsHausdorff.of_le_jacobson _ _ (IsAdicComplete.le_jacobson_bot C.adicIdeal)
  have : IsHausdorff (I.map (algebraMap A P.extension.Ring))
      (C.carrier ⊗[P.extension.Ring] P.extension.ker) := IsHausdorff.of_map hH.le
  let : ∀ n : ℕ,
      Algebra P.extension.Ring (P.baseReducedGenerators (n + 1)).toExtension.Ring := fun n =>
    (coeffReduction I (Fin P.variableCount) (n + 1)).toRingHom.toAlgebra
  -- the two inverse systems of reductions, of `C` and of `J`
  let fred : ∀ n : ℕ, C.carrier →ₗ[P.extension.Ring] C.carrier ⧸ C.adicIdeal ^ (n + 1) :=
    fun n => (Ideal.Quotient.mkₐ P.extension.Ring (C.adicIdeal ^ (n + 1))).toLinearMap
  let gred : ∀ n : ℕ, P.extension.ker →ₗ[P.extension.Ring]
      (P.baseReducedGenerators (n + 1)).toExtension.ker := fun n =>
    ((Algebra.linearMap P.extension.Ring
        (P.baseReducedGenerators (n + 1)).toExtension.Ring).comp
      P.extension.ker.subtype).codRestrict
        ((P.baseReducedGenerators (n + 1)).toExtension.ker.restrictScalars
          P.extension.Ring) fun y => by
      change coeffReduction I (Fin P.variableCount) (n + 1) y.1 ∈
        (P.baseReducedGenerators (n + 1)).ker
      rw [P.baseReducedGenerators_ker (n + 1)]
      exact Ideal.mem_map_of_mem _ y.2
  have hfred : ∀ n, Function.Surjective (fred n) := fun _ => Ideal.Quotient.mk_surjective
  have hgred : ∀ n, Function.Surjective (gred n) := by
    rintro n ⟨y, hy⟩
    change y ∈ (P.baseReducedGenerators (n + 1)).ker at hy
    rw [P.baseReducedGenerators_ker (n + 1)] at hy
    obtain ⟨w, hw, he⟩ := (Ideal.mem_map_iff_of_surjective _
      (surjective_coeffReduction I (Fin P.variableCount) (n + 1))).mp hy
    exact ⟨⟨w, hw⟩, Subtype.ext he⟩
  obtain ⟨c, hc⟩ := exists_ker_idealMap_le_pow_smul (I.map (algebraMap A P.extension.Ring))
    P.extension.ker (S := fun n => (P.baseReducedGenerators (n + 1)).toExtension.Ring)
    (fun n => by
      change RingHom.ker (coeffReduction I (Fin P.variableCount) (n + 1)).toRingHom ≤ _
      rw [ker_coeffReduction]
      exact Ideal.pow_le_pow_right (Nat.le_succ n))
  have hk : ∀ k, ∃ n, (fred n).ker ≤ (I.map (algebraMap A P.extension.Ring)) ^ k • ⊤ ∧
      (gred n).ker ≤ (I.map (algebraMap A P.extension.Ring)) ^ k • ⊤ := by
    intro k
    refine ⟨k + c, fun y hy => ?_, fun y hy => ?_⟩
    · have hy' : y ∈ C.adicIdeal ^ (k + c + 1) := Ideal.Quotient.eq_zero_iff_mem.mp hy
      have hy'' : y ∈ C.adicIdeal ^ k := Ideal.pow_le_pow_right (by omega) hy'
      simpa only [Ideal.smul_top_eq_map, Ideal.map_pow, hH,
        Submodule.restrictScalars_mem] using hy''
    · refine hc k (k + c) le_rfl ?_
      change gred (k + c) y = 0 at hy
      exact Subtype.ext (congrArg
        (fun w : (P.baseReducedGenerators (k + c + 1)).toExtension.ker =>
          (w : (P.baseReducedGenerators (k + c + 1)).toExtension.Ring)) hy)
  rw [injective_iff_map_eq_zero]
  intro x hx
  let e : C.carrier ⊗[P.extension.Ring] P.extension.ker ≃ₗ[C.carrier]
      C.carrier ⊗[B.carrier] P.extension.Cotangent := conormalTensorEquiv P.extension C.carrier
  have hz : e.symm x = 0 := by
    refine tensorProduct_eq_zero_of_adic_projections (I.map (algebraMap A P.extension.Ring))
      fred gred hfred hgred hk _ fun n => ?_
    let : Algebra (P.baseReducedGenerators (n + 1)).toExtension.Ring
        (C.carrier ⧸ C.adicIdeal ^ (n + 1)) :=
      ((algebraMap (B.carrier ⧸ B.adicIdeal ^ (n + 1))
          (C.carrier ⧸ C.adicIdeal ^ (n + 1))).comp
        (algebraMap (P.baseReducedGenerators (n + 1)).toExtension.Ring
          (B.carrier ⧸ B.adicIdeal ^ (n + 1)))).toAlgebra
    have : IsScalarTower (P.baseReducedGenerators (n + 1)).toExtension.Ring
        (B.carrier ⧸ B.adicIdeal ^ (n + 1)) (C.carrier ⧸ C.adicIdeal ^ (n + 1)) :=
      .of_algebraMap_eq fun _ => rfl
    have : IsScalarTower P.extension.Ring
        (P.baseReducedGenerators (n + 1)).toExtension.Ring
        (C.carrier ⧸ C.adicIdeal ^ (n + 1)) := .of_algebraMap_eq fun y => by
      have h1 : algebraMap (P.baseReducedGenerators (n + 1)).toExtension.Ring
            (C.carrier ⧸ C.adicIdeal ^ (n + 1))
            (algebraMap P.extension.Ring
              (P.baseReducedGenerators (n + 1)).toExtension.Ring y) =
          algebraMap (B.carrier ⧸ B.adicIdeal ^ (n + 1)) (C.carrier ⧸ C.adicIdeal ^ (n + 1))
            (algebraMap (P.baseReducedGenerators (n + 1)).toExtension.Ring
              (B.carrier ⧸ B.adicIdeal ^ (n + 1))
              (coeffReduction I (Fin P.variableCount) (n + 1) y)) := rfl
      rw [h1, P.algebraMap_baseReducedGenerators_coeffReduction (n + 1) y]
      rfl
    let e' := tensorOverSurjectionEquiv P.extension.Ring
          (P.baseReducedGenerators (n + 1)).toExtension.Ring
          (C.carrier ⧸ C.adicIdeal ^ (n + 1))
          (P.baseReducedGenerators (n + 1)).toExtension.ker
          (surjective_coeffReduction I (Fin P.variableCount) (n + 1)) ≪≫ₗ
      conormalTensorEquiv (P.baseReducedGenerators (n + 1)).toExtension
        (C.carrier ⧸ C.adicIdeal ^ (n + 1))
    let jcomp := (Algebra.Extension.Cotangent.map
      ((fiberReducedGenerators s ψ hψ (n + 1)).toComp
        (P.baseReducedGenerators (n + 1))).toExtensionHom).liftBaseChange
          (C.carrier ⧸ C.adicIdeal ^ (n + 1))
    have hj : Function.Injective jcomp :=
      RingHom.cotangentMap_toComp_injective_of_isLocalCompleteIntersection
        (P.baseReducedGenerators (n + 1)) (fiberReducedGenerators s ψ hψ (n + 1)) (h n)
    have heq : ∀ t : C.carrier ⊗[P.extension.Ring] P.extension.ker,
        jcomp (e' (TensorProduct.map (fred n) (gred n) t)) =
          Algebra.Extension.Cotangent.map (P.reducedCombinedHom s ψ hψ (n + 1))
            ((Algebra.Extension.Cotangent.map
              (P.innerExtensionHom s ψ hψ)).liftBaseChange C.carrier (e t)) := by
      intro t
      induction t using TensorProduct.inductionOn with
      | add t w ht hw => simp only [LinearMap.map_add, LinearEquiv.map_add, ht, hw]
      | tmul a b =>
        have h1 : e' (TensorProduct.map (fred n) (gred n) (a ⊗ₜ[P.extension.Ring] b)) =
            (fred n) a ⊗ₜ[B.carrier ⧸ B.adicIdeal ^ (n + 1)]
              Algebra.Extension.Cotangent.mk ((gred n) b) :=
          (congrArg (conormalTensorEquiv (P.baseReducedGenerators (n + 1)).toExtension
              (C.carrier ⧸ C.adicIdeal ^ (n + 1)))
            (tensorOverSurjectionEquiv_tmul P.extension.Ring
              (P.baseReducedGenerators (n + 1)).toExtension.Ring
              (C.carrier ⧸ C.adicIdeal ^ (n + 1))
              (P.baseReducedGenerators (n + 1)).toExtension.ker
              (surjective_coeffReduction I (Fin P.variableCount) (n + 1))
              ((fred n) a) ((gred n) b))).trans
            (conormalTensorEquiv_tmul (P.baseReducedGenerators (n + 1)).toExtension
              (C.carrier ⧸ C.adicIdeal ^ (n + 1)) ((fred n) a) ((gred n) b))
        have h4 : e (a ⊗ₜ[P.extension.Ring] b) =
            a ⊗ₜ[B.carrier] Algebra.Extension.Cotangent.mk b :=
          conormalTensorEquiv_tmul P.extension C.carrier a b
        simp only [jcomp, h1, h4, LinearMap.liftBaseChange_tmul,
          Algebra.Extension.Cotangent.map_mk, map_smul]
        rw [← algebraMap_smul (C.carrier ⧸ C.adicIdeal ^ (n + 1)) a]
        refine congrArg₂ (fun (c : C.carrier ⧸ C.adicIdeal ^ (n + 1))
            (z : ((fiberReducedGenerators s ψ hψ (n + 1)).comp
              (P.baseReducedGenerators (n + 1))).toExtension.ker) =>
            c • Algebra.Extension.Cotangent.mk z) rfl (Subtype.ext ?_)
        change (((fiberReducedGenerators s ψ hψ (n + 1)).toComp
            (P.baseReducedGenerators (n + 1))).toExtensionHom.toRingHom) ((gred n) b).1 =
          (P.reducedCombinedMap s ψ hψ (n + 1)) ((P.combinedInclusion s) b.1)
        exact (RingHom.congr_fun (P.reducedCombinedMap_base s ψ hψ (n + 1)) b.1).symm
    refine e'.injective (hj ?_)
    rw [LinearEquiv.map_zero, LinearMap.map_zero, heq, e.apply_symm_apply, hx,
      LinearMap.map_zero]
  exact e.symm.injective (hz.trans (e.symm.map_zero).symm)

/-- **Stacks 0AQJ.**  Let `A` be Noetherian, `I ⊆ A` an ideal, `B → C` a morphism of the
category (Stacks 0AL4), `B = A⟨x₁, …, x_r⟩ / J` a completed polynomial presentation and
`ψ : B⟨y₁, …, y_s⟩ ↠ C` a presentation of `C` over `B`.  Assume that `B / IⁿB → C / IⁿC` is a
local complete intersection homomorphism for every `n ≥ 1`.  Then the first map

`H⁻¹(NL^∧_{B/A} ⊗_B C) ⟶ H⁻¹(NL^∧_{C/A})`

of the six-term sequence of Stacks 0ALM is injective.  The map is the one induced on `H⁻¹` by
the left-hand chain map of that sequence, namely the chain map of
`Rig.CompletedPolynomialPresentation.combinedDifferential_comp_innerCotangentMap`. -/
@[stacks 0AQJ]
public theorem injective_onH₁_chainMapInl_of_lci
    (KB : CompletedNaiveCotangentComplex P)
    (KC : CompletedNaiveCotangentComplex
      (P.combinedPresentation s (ψ.restrictScalars A) hψ))
    (h : ∀ n : ℕ, RingHom.IsLocalCompleteIntersection (reductionMap B C (n + 1))) :
    Function.Injective (NaiveCotangent.chainMapInl _
      (P.combinedDifferential_comp_innerCotangentMap s ψ hψ KB KC)).onH₁ :=
  fun _ _ hyz => Subtype.ext (P.injective_cotangentMap_innerExtensionHom_of_lci s ψ hψ h
    (congrArg Subtype.val hyz))

end CompletedPolynomialPresentation

end ReductionMap

end Rig
