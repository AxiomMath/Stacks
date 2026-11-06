module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import StacksFrontier.RingTheory.AdicCompletion.Finiteness
import StacksFrontier.RingTheory.AdicCompletion.QuotPow
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.AdicCompletion.QuotEquivMapPow
public import StacksFrontier.RingTheory.AdicCompletion.SmulTopPow
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow
public import StacksFrontier.RingTheory.Localization.AtPrimeQuotient
public import StacksFrontier.RingTheory.AdicCompletion.CompletionMap
public import StacksFrontier.RingTheory.AdicCompletion.OfTensorProductBijective

/-!
# Completions of finite algebras over local rings

Let `R → S` be a local homomorphism of local rings `(R, m)` and `(S, n)` with `m` finitely
generated, such that the fibre `S ⧸ mS` is a finite `R`-module. Then the `n`-adic completion of
`S` is, as an `S`-algebra, the `mS`-adic completion of `S`, and the `m`-adic completion of `S` is a
finite module over the `m`-adic completion of `R`.

Let `R` be a Noetherian ring, `S` a finite `R`-algebra and `p` a prime of `R`. Then the base change
of `S` along the completion `Rₚ^∧` of the local ring `Rₚ` is, as an `S`-algebra, the product of
the completions `S_q^∧` of the local rings `S_q` at their maximal ideals, over the primes `q` of
`S` lying over `p`.

## Main results

* `AdicCompletion.nonempty_algEquiv_map_and_finite`: for a local homomorphism of local rings with
  finitely generated maximal ideal downstairs and finite fibre, the completion of `S` along `n` is,
  as an `S`-algebra, the completion of `S` along `mS`, and the completion of `S` along `m` is a
  finite module over the completion of `R` along `m`.
* `AdicCompletion.nonempty_algEquiv_pi_primesOver`: for `R` Noetherian, `S` a finite `R`-algebra
  and `p` a prime of `R`, the base change `S ⊗[R] Rₚ^∧` is, as an `S`-algebra, the product over
  the primes `q` of `S` lying over `p` of the completions `S_q^∧`.

## Implementation notes

In `AdicCompletion.nonempty_algEquiv_map_and_finite` the source's hypothesis that `n` is finitely
generated is not assumed. The `m`-adic completion of `S` appears as the completion
`AdicCompletion ((maximalIdeal R).map (algebraMap R S)) S` of the ring `S` along `mS` in the first
conjunct, and as the completion `AdicCompletion (maximalIdeal R) S` of the `R`-module `S` along
`m` in the second; both are the inverse limit of the same tower of quotients
(`Ideal.smul_top_eq_map`).

In `AdicCompletion.nonempty_algEquiv_pi_primesOver` the tensor product is written `S ⊗[R] Rₚ^∧`
rather than `Rₚ^∧ ⊗[R] S`, so that its `S`-algebra structure is the global instance, and the
primes of `S` lying over `p` are indexed by `p.primesOver S`. The source's middle term `(S_p)^∧`
is Mathlib's `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian` over `Rₚ`.

## References

* [Stacks Project, Tag 0394](https://stacks.math.columbia.edu/tag/0394)
* [Stacks Project, Tag 07N9](https://stacks.math.columbia.edu/tag/07N9)
* [Stacks Project, Tag 0319](https://stacks.math.columbia.edu/tag/0319)
* [Stacks Project, Tag 031D](https://stacks.math.columbia.edu/tag/031D)
* [Stacks Project, Tag 05GG](https://stacks.math.columbia.edu/tag/05GG)
* [Stacks Project, Tag 00MA](https://stacks.math.columbia.edu/tag/00MA)
* [Stacks Project, Tag 00JB](https://stacks.math.columbia.edu/tag/00JB)
* [Stacks Project, Tag 00KJ](https://stacks.math.columbia.edu/tag/00KJ)

## Tags

adic completion, local ring, finite module, primes lying over, product decomposition
-/

@[expose] public section

@[expose] public section

namespace Stacks.AdicCompletion.LocalFiniteFibre

open IsLocalRing _root_.AdicCompletion

section Cofinal

variable {S : Type*} [CommRing S]

/-- Two successive `Ideal.Quotient.factorₐ` maps compose to the one for the composed inequality.
-/
private theorem factorₐ_factorₐ {I J K : Ideal S} (h₁ : I ≤ J) (h₂ : J ≤ K) (y : S ⧸ I) :
    Ideal.Quotient.factorₐ S h₂ (Ideal.Quotient.factorₐ S h₁ y)
      = Ideal.Quotient.factorₐ S (h₁.trans h₂) y :=
  DFunLike.congr_fun (Ideal.Quotient.factorₐ_comp S h₁ h₂) y

/-- For `m ≤ n` and an ideal `K` containing `I ^ m`, the level-`n` component of `x` and its
level-`m` component have the same image in `S ⧸ K`. -/
private theorem factorₐ_evalₐ {I K : Ideal S} {m n : ℕ} (hmn : m ≤ n) (h : I ^ m ≤ K)
    (x : AdicCompletion I S) :
    Ideal.Quotient.factorₐ S ((Ideal.pow_le_pow_right hmn).trans h) (evalₐ I n x)
      = Ideal.Quotient.factorₐ S h (evalₐ I m x) := by
  obtain ⟨f, rfl⟩ := AdicCompletion.mk_surjective I S x
  rw [evalₐ_mk, evalₐ_mk, Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factorₐ_apply,
    Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
  exact h (by simpa [smul_eq_mul, Ideal.mul_top] using SModEq.sub_mem.mp (f.property hmn).symm)

/-- All levels of an adic completion agree in a common quotient: for any ideal `K` containing both
`I ^ m` and `I ^ n`, the level-`m` and the level-`n` component of `x` have the same image in
`S ⧸ K`. -/
private theorem factorₐ_evalₐ_eq {I K : Ideal S} {m n : ℕ} (h₁ : I ^ m ≤ K) (h₂ : I ^ n ≤ K)
    (x : AdicCompletion I S) :
    Ideal.Quotient.factorₐ S h₁ (evalₐ I m x) = Ideal.Quotient.factorₐ S h₂ (evalₐ I n x) := by
  rcases le_total m n with h | h
  · exact (factorₐ_evalₐ h h₁ x).symm
  · exact factorₐ_evalₐ h h₂ x

/-- If `I ^ a ≤ J` then `I ^ (a * t) ≤ J ^ t`. -/
private theorem pow_mul_le_pow {I J : Ideal S} {a : ℕ} (hIJ : I ^ a ≤ J) (t : ℕ) :
    I ^ (a * t) ≤ J ^ t :=
  (pow_mul I a t).symm ▸ pow_le_pow_left' hIJ t

/-- For `J ^ n ≤ J ^ m`, the level-`a * n` component, pushed into `S ⧸ J ^ n` and then into
`S ⧸ J ^ m`, is the level-`a * m` component pushed into `S ⧸ J ^ m`. -/
private theorem factorₐ_comp_factorₐ_comp_evalₐ {I J : Ideal S} {a : ℕ} (hIJ : I ^ a ≤ J)
    {m n : ℕ} (h : J ^ n ≤ J ^ m) :
    (Ideal.Quotient.factorₐ S h).comp
        ((Ideal.Quotient.factorₐ S (pow_mul_le_pow hIJ n)).comp (evalₐ I (a * n)))
      = (Ideal.Quotient.factorₐ S (pow_mul_le_pow hIJ m)).comp (evalₐ I (a * m)) := by
  rw [← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]
  exact AlgHom.ext fun x =>
    factorₐ_evalₐ_eq ((pow_mul_le_pow hIJ n).trans h) (pow_mul_le_pow hIJ m) x

/-- The comparison map `S^∧_I → S^∧_J` of `S`-algebras attached to `I ^ a ≤ J`: its level-`t`
component is the level-`a * t` component of the source, pushed forward along
`I ^ (a * t) ≤ J ^ t`. -/
private noncomputable def cmapₐ (I J : Ideal S) {a : ℕ} (hIJ : I ^ a ≤ J) :
    AdicCompletion I S →ₐ[S] AdicCompletion J S :=
  liftAlgHom J
    (fun t => (Ideal.Quotient.factorₐ S (pow_mul_le_pow hIJ t)).comp (evalₐ I (a * t)))
    fun hle => factorₐ_comp_factorₐ_comp_evalₐ hIJ (Ideal.pow_le_pow_right hle)

/-- The level-`t` component of `cmapₐ I J hIJ x` is the level-`a * t` component of `x`, pushed
into `S ⧸ J ^ t`. -/
private theorem evalₐ_cmapₐ (I J : Ideal S) {a : ℕ} (hIJ : I ^ a ≤ J) (t : ℕ)
    (x : AdicCompletion I S) :
    evalₐ J t (cmapₐ I J hIJ x)
      = Ideal.Quotient.factorₐ S (pow_mul_le_pow hIJ t) (evalₐ I (a * t) x) :=
  AdicCompletion.evalₐ_liftAlgHom J _
    (fun hle => factorₐ_comp_factorₐ_comp_evalₐ hIJ (Ideal.pow_le_pow_right hle)) t x

/-- The comparison maps attached to `I ^ a ≤ J` and `J ^ b ≤ I` compose to the identity of the
`I`-adic completion of `S`. -/
private theorem cmapₐ_comp_cmapₐ (I J : Ideal S) {a b : ℕ} (hIJ : I ^ a ≤ J) (hJI : J ^ b ≤ I) :
    (cmapₐ J I hJI).comp (cmapₐ I J hIJ) = AlgHom.id S (AdicCompletion I S) :=
  AlgHom.ext fun x => ext_evalₐ fun t => by
    rw [AlgHom.comp_apply, AlgHom.id_apply, evalₐ_cmapₐ, evalₐ_cmapₐ, factorₐ_factorₐ,
      factorₐ_evalₐ_eq _ (le_refl (I ^ t)) x]
    simp

/-- If `I ^ a ≤ J` and `J ^ b ≤ I`, the comparison maps are mutually inverse `S`-algebra
isomorphisms between the `I`-adic and the `J`-adic completion of `S`. -/
private noncomputable def algEquivOfPowLe (I J : Ideal S) {a b : ℕ} (hIJ : I ^ a ≤ J)
    (hJI : J ^ b ≤ I) : AdicCompletion I S ≃ₐ[S] AdicCompletion J S :=
  AlgEquiv.ofAlgHom (cmapₐ I J hIJ) (cmapₐ J I hJI) (cmapₐ_comp_cmapₐ J I hJI hIJ)
    (cmapₐ_comp_cmapₐ I J hIJ hJI)

end Cofinal

section Finite

/-- If `N ⧸ IN` is a finite `R`-module, then `N ⧸ (IA)N` is a finite `A ⧸ IA`-module. -/
private theorem finite_quotient_map_smul_top {R A N : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N] (I : Ideal R)
    (h : Module.Finite R (N ⧸ (I • ⊤ : Submodule R N))) :
    Module.Finite (A ⧸ I.map (algebraMap R A))
      (N ⧸ (I.map (algebraMap R A) • ⊤ : Submodule A N)) := by
  have hres : Module.Finite R
      (N ⧸ ((I.map (algebraMap R A) • (⊤ : Submodule A N)).restrictScalars R)) := by
    rw [Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top]
    exact h
  have := hres.equiv (Submodule.Quotient.restrictScalarsEquiv R _)
  have := Module.Finite.of_restrictScalars_finite R A
    (N ⧸ (I.map (algebraMap R A) • ⊤ : Submodule A N))
  exact Module.Finite.of_restrictScalars_finite A (A ⧸ I.map (algebraMap R A)) _

/-- For a finitely generated ideal `I` of `R` and an `R`-module `M` whose reduction `M ⧸ IM` is a
finite `R`-module, the `I`-adic completion of `M` is a finite module over the `I`-adic completion
of `R`. -/
@[ega "0 7.2.12" "special case"]
private theorem finite_adicCompletion {R : Type*} [CommRing R] {I : Ideal R} (hI : I.FG)
    (M : Type*) [AddCommGroup M] [Module R M]
    (hfib : Module.Finite R (M ⧸ (I • ⊤ : Submodule R M))) :
    Module.Finite (AdicCompletion I R) (AdicCompletion I M) := by
  have : IsPrecomplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R) :=
    (AdicCompletion.isAdicComplete_self I hI).toIsPrecomplete
  have e := AdicCompletion.quotPowSMulTopEquiv hI M 1
  rw [pow_one] at e
  exact Module.Finite.of_iInf_pow_smul_top_eq_bot_of_finite_quotient_smul_top _
    (IsHausdorff.map_algebraMap_iff.mpr (AdicCompletion.instIsHausdorff I M)).iInf_pow_smul
    (finite_quotient_map_smul_top I (hfib.equiv e.symm))

end Finite

section Artinian

/-- If `R ⧸ I` is an Artinian ring and `S ⧸ IS` is a finite `R`-module, then `S ⧸ IS` is an
Artinian ring. -/
private theorem isArtinianRing_quotient_map {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) [IsArtinianRing (R ⧸ I)]
    [Module.Finite R (S ⧸ I.map (algebraMap R S))] :
    IsArtinianRing (S ⧸ I.map (algebraMap R S)) := by
  let _ : Algebra (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have : IsScalarTower R (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
    Module.Finite.of_restrictScalars_finite R _ _
  exact IsArtinianRing.of_finite (R ⧸ I) _

end Artinian

/-- Let `R → S` be a local homomorphism of local rings `(R, m)` and `(S, n)` with `m` finitely
generated and `S ⧸ mS` a finite `R`-module. Then the `n`-adic completion of `S` is, as an
`S`-algebra, the `mS`-adic completion of `S`, and the `m`-adic completion of `S` is a finite
module over the `m`-adic completion of `R`. -/
public theorem solution
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] (hm : (maximalIdeal R).FG)
    [Module.Finite R (S ⧸ (maximalIdeal R).map (algebraMap R S))] :
    Nonempty (AdicCompletion (maximalIdeal S) S ≃ₐ[S]
        AdicCompletion ((maximalIdeal R).map (algebraMap R S)) S) ∧
      Module.Finite (AdicCompletion (maximalIdeal R) R) (AdicCompletion (maximalIdeal R) S) := by
  have : IsArtinianRing (R ⧸ maximalIdeal R) := inferInstanceAs (IsArtinianRing (ResidueField R))
  have := isArtinianRing_quotient_map (S := S) (maximalIdeal R)
  obtain ⟨k, hk⟩ := IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient
    ((maximalIdeal R).map (algebraMap R S))
  refine ⟨⟨algEquivOfPowLe (maximalIdeal S) ((maximalIdeal R).map (algebraMap R S)) hk (b := 1)
    (by simpa using IsLocalRing.map_maximalIdeal_le (algebraMap R S))⟩, ?_⟩
  exact finite_adicCompletion hm S <| by
    rw [Ideal.smul_top_eq_map]
    exact inferInstanceAs (Module.Finite R (S ⧸ (maximalIdeal R).map (algebraMap R S)))

end Stacks.AdicCompletion.LocalFiniteFibre

@[expose] public section

open IsLocalRing

/-- Let `R → S` be a local homomorphism of local rings `(R, m)` and `(S, n)` with `m` finitely
generated, and assume that the fibre `S/mS` is a finite `R`-module, i.e. `dim_{κ(m)} S/mS < ∞`.
Then the completion `S^∧ = lim S/nᵏ` is, as an `S`-algebra, the `m`-adic completion `lim S/mᵏS`
of `S`, and the latter is a finite module over `R^∧ = lim R/mᵏ`. -/
@[stacks 0394 "Stated without the source's finite generation of `n`, which no step needs; the \
`m`-adic completion of `S` appears as a completion along the ideal `mS` of `S` in the first \
conjunct and along `m` in the second. See the module docstring.", sga "1 I 2.1" "(i) => (iii)"]
public theorem AdicCompletion.nonempty_algEquiv_map_and_finite
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] (hm : (maximalIdeal R).FG)
    [Module.Finite R (S ⧸ (maximalIdeal R).map (algebraMap R S))] :
    Nonempty (AdicCompletion (maximalIdeal S) S ≃ₐ[S]
        AdicCompletion ((maximalIdeal R).map (algebraMap R S)) S) ∧
      Module.Finite (AdicCompletion (maximalIdeal R) R) (AdicCompletion (maximalIdeal R) S) :=
  Stacks.AdicCompletion.LocalFiniteFibre.solution hm

end

@[expose] public section

namespace Stacks.AdicCompletion.PrimesOverProduct

open TensorProduct IsLocalRing

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The `R`-algebra `S ⊗[R] Rₚ` is an `Rₚ`-algebra through its right factor, compatibly with its
`R`-algebra structure. -/
private theorem isScalarTower_tensor {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (Rp : Type*) [CommRing Rp] [Algebra R Rp] : IsScalarTower R Rp (S ⊗[R] Rp) :=
  IsScalarTower.of_algebraMap_eq fun r ↦ by
    simp [Algebra.algebraMap_eq_smul_one]

/-- The base change of `S` along the completion of `Rₚ` is, as an `S`-algebra, the base change of
`S ⊗[R] Rₚ` along it. -/
private theorem nonempty_algEquiv_tensor_tensor {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (p : Ideal R) [p.IsPrime]
    (Rp : Type*) [CommRing Rp] [Algebra R Rp] [IsLocalization.AtPrime Rp p] [IsLocalRing Rp] :
    Nonempty (S ⊗[R] AdicCompletion (maximalIdeal Rp) Rp ≃ₐ[S]
      (S ⊗[R] Rp) ⊗[Rp] AdicCompletion (maximalIdeal Rp) Rp) := by
  have := isScalarTower_tensor (R := R) (S := S) Rp
  have : Algebra.IsPushout R S Rp (S ⊗[R] Rp) :=
    Algebra.isPushout_of_isLocalization p.primeCompl Rp _ _
  exact ⟨(Algebra.IsPushout.cancelBaseChangeAlg R S Rp (S ⊗[R] Rp)
    (AdicCompletion (maximalIdeal Rp) Rp)).symm⟩

section AdicCompletionPi

open _root_.AdicCompletion

/-- Any two levels of an element of an adic completion have a common representative. -/
public theorem exists_evalₐ_eq_mk {R : Type*} [CommRing R] (I : Ideal R) {m n : ℕ} (hmn : m ≤ n)
    (x : AdicCompletion I R) : ∃ t : R, evalₐ I n x = Ideal.Quotient.mk (I ^ n) t ∧
      evalₐ I m x = Ideal.Quotient.mk (I ^ m) t := by
  obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
  refine ⟨t, evalₐ_eq_mk I n x t ht.symm, evalₐ_eq_mk I m x t ?_⟩
  rw [← x.property hmn, ← ht]; rfl

variable {T : Type*} [CommRing T] (J : Ideal T) {ι : Type*} (U : ι → Type*)
  [∀ i, CommRing (U i)] [∀ i, Algebra T (U i)]

/-- The canonical map `T ⧸ Jⁿ → ∀ i, U i ⧸ Jⁿ U i`. -/
private noncomputable def quotientPiAlgHom (n : ℕ) :
    T ⧸ J ^ n →ₐ[T] ∀ i, U i ⧸ (J ^ n).map (algebraMap T (U i)) :=
  IsScalarTower.toAlgHom T _ _

private theorem quotientPiAlgHom_mk (n : ℕ) (t : T) :
    quotientPiAlgHom J U n (Ideal.Quotient.mk _ t) =
      fun i => Ideal.Quotient.mk _ (algebraMap T (U i) t) := by
  funext i
  simp [quotientPiAlgHom, Ideal.Quotient.algebraMap_quotient_map_quotient]

/-- The `n`-th level of the comparison map, on the `i`-th factor. -/
private noncomputable def piLevel (i : ι) (n : ℕ) :
    AdicCompletion J T →ₐ[T] U i ⧸ (J.map (algebraMap T (U i))) ^ n :=
  ((Ideal.quotientMapPowAlgEquiv (B := U i) J n).toAlgHom.comp
    ((Pi.evalAlgHom T _ i).comp (quotientPiAlgHom J U n))).comp (evalₐ J n)

private theorem piLevel_eq (i : ι) (n : ℕ) (x : AdicCompletion J T) :
    piLevel J U i n x =
      Ideal.quotientMapPowAlgEquiv (B := U i) J n (quotientPiAlgHom J U n (evalₐ J n x) i) := rfl

private theorem piLevel_apply (i : ι) (n : ℕ) (x : AdicCompletion J T) (t : T)
    (ht : evalₐ J n x = Ideal.Quotient.mk (J ^ n) t) :
    piLevel J U i n x = Ideal.Quotient.mk _ (algebraMap T (U i) t) := by
  rw [piLevel_eq, ht, quotientPiAlgHom_mk, Ideal.quotientMapPowAlgEquiv_mk]

private theorem factorₐ_comp_piLevel (i : ι) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ T (Ideal.pow_le_pow_right hmn)).comp (piLevel J U i n) =
      piLevel J U i m := by
  refine AlgHom.ext fun x => ?_
  obtain ⟨t, htn, htm⟩ := exists_evalₐ_eq_mk J hmn x
  rw [AlgHom.comp_apply, piLevel_apply J U i n x t htn, piLevel_apply J U i m x t htm]
  rfl

/-- The comparison map from the `J`-adic completion of `T` into the `J U i`-adic completion of
`U i`. -/
private noncomputable def piFactor (i : ι) :
    AdicCompletion J T →ₐ[T] AdicCompletion (J.map (algebraMap T (U i))) (U i) :=
  liftAlgHom _ (piLevel J U i) fun hle => factorₐ_comp_piLevel J U i hle

private theorem evalₐ_piFactor (i : ι) (n : ℕ) (x : AdicCompletion J T) :
    evalₐ (J.map (algebraMap T (U i))) n (piFactor J U i x) = piLevel J U i n x :=
  evalₐ_liftAlgHom _ _ _ _ _

/-- The `n`-th level of the inverse comparison map. -/
private noncomputable def invLevel (n : ℕ) :
    (∀ i, AdicCompletion (J.map (algebraMap T (U i))) (U i)) →ₐ[T]
      ∀ i, U i ⧸ (J ^ n).map (algebraMap T (U i)) :=
  AlgHom.pi fun i => ((Ideal.quotientMapPowAlgEquiv (B := U i) J n).symm.toAlgHom.comp
    ((evalₐ (J.map (algebraMap T (U i))) n).restrictScalars T)).comp (Pi.evalAlgHom T _ i)

private theorem invLevel_apply (n : ℕ)
    (y : ∀ i, AdicCompletion (J.map (algebraMap T (U i))) (U i)) (i : ι) :
    invLevel J U n y i =
      (Ideal.quotientMapPowAlgEquiv (B := U i) J n).symm
        (evalₐ (J.map (algebraMap T (U i))) n (y i)) := rfl

/-- The `n`-th level of the comparison, as an isomorphism. -/
private noncomputable def levelAlgEquiv
    (hlvl : ∀ n : ℕ, Function.Bijective (quotientPiAlgHom J U n))
    (n : ℕ) :
    (T ⧸ J ^ n) ≃ₐ[T] ∀ i, U i ⧸ (J ^ n).map (algebraMap T (U i)) :=
  AlgEquiv.ofBijective (quotientPiAlgHom J U n) (hlvl n)

/-- The `n`-th level isomorphism is inverted by the canonical map `T ⧸ Jⁿ → ∀ i, U i ⧸ Jⁿ U i`. -/
private theorem quotientPiAlgHom_levelAlgEquiv_symm
    (hlvl : ∀ n : ℕ, Function.Bijective (quotientPiAlgHom J U n)) (n : ℕ)
    (z : ∀ i, U i ⧸ (J ^ n).map (algebraMap T (U i))) :
    quotientPiAlgHom J U n ((levelAlgEquiv J U hlvl n).symm z) = z :=
  (levelAlgEquiv J U hlvl n).apply_symm_apply z

/-- For `m ≤ n`, reducing the canonical map `T ⧸ Jⁿ → ∀ i, U i ⧸ Jⁿ U i` modulo `Jᵐ` gives the
canonical map `T ⧸ Jᵐ → ∀ i, U i ⧸ Jᵐ U i`. -/
private theorem factorₐ_quotientPiAlgHom {m n : ℕ} (hmn : m ≤ n) (x : T ⧸ J ^ n) (i : ι) :
    Ideal.Quotient.factorₐ T (Ideal.map_mono (Ideal.pow_le_pow_right (I := J) hmn))
        (quotientPiAlgHom J U n x i)
      = quotientPiAlgHom J U m (Ideal.Quotient.factorₐ T (Ideal.pow_le_pow_right hmn) x) i := by
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [show Ideal.Quotient.factorₐ T (Ideal.pow_le_pow_right (I := J) hmn)
      (Ideal.Quotient.mk (J ^ n) t) = Ideal.Quotient.mk (J ^ m) t from rfl,
    quotientPiAlgHom_mk, quotientPiAlgHom_mk]
  rfl

/-- For `m ≤ n`, the level-`n` map `invLevel J U n`, reduced modulo `Jᵐ`, is the level-`m` map
`invLevel J U m`. -/
private theorem factorₐ_invLevel {m n : ℕ} (hmn : m ≤ n)
    (y : ∀ i, AdicCompletion (J.map (algebraMap T (U i))) (U i)) (i : ι) :
    Ideal.Quotient.factorₐ T (Ideal.map_mono (Ideal.pow_le_pow_right (I := J) hmn))
      (invLevel J U n y i) = invLevel J U m y i := by
  obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective
    (evalₐ (J.map (algebraMap T (U i))) n (y i))
  have hm : evalₐ (J.map (algebraMap T (U i))) m (y i) = Ideal.Quotient.mk _ u := by
    rw [← factorPow_evalₐ _ hmn, ← hu]; rfl
  rw [invLevel_apply, invLevel_apply, ← hu, hm, Ideal.quotientMapPowAlgEquiv_symm_mk,
    Ideal.quotientMapPowAlgEquiv_symm_mk]
  rfl

/-- The levels of the inverse comparison map are compatible with the transition maps. -/
private theorem factorₐ_comp_invLevel
    (hlvl : ∀ n : ℕ, Function.Bijective (quotientPiAlgHom J U n))
    {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ T (Ideal.pow_le_pow_right (I := J) hmn)).comp
        ((levelAlgEquiv J U hlvl n).symm.toAlgHom.comp (invLevel J U n)) =
      (levelAlgEquiv J U hlvl m).symm.toAlgHom.comp (invLevel J U m) := by
  refine AlgHom.ext fun y => (hlvl m).injective (funext fun i => ?_)
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [quotientPiAlgHom_levelAlgEquiv_symm, ← factorₐ_quotientPiAlgHom J U hmn,
    quotientPiAlgHom_levelAlgEquiv_symm, factorₐ_invLevel J U hmn]

/-- The inverse of the comparison map. -/
private noncomputable def invAlgHom
    (hlvl : ∀ n : ℕ, Function.Bijective (quotientPiAlgHom J U n))
    :
    (∀ i, AdicCompletion (J.map (algebraMap T (U i))) (U i)) →ₐ[T] AdicCompletion J T :=
  liftAlgHom J (fun n => (levelAlgEquiv J U hlvl n).symm.toAlgHom.comp (invLevel J U n))
    fun hle => factorₐ_comp_invLevel J U hlvl hle

private theorem evalₐ_invAlgHom
    (hlvl : ∀ n : ℕ, Function.Bijective (quotientPiAlgHom J U n))
    (n : ℕ)
    (y : ∀ i, AdicCompletion (J.map (algebraMap T (U i))) (U i)) :
    evalₐ J n (invAlgHom J U hlvl y) = (levelAlgEquiv J U hlvl n).symm (invLevel J U n y) :=
  evalₐ_liftAlgHom _ _ _ _ _

private theorem piFactor_invAlgHom
    (hlvl : ∀ n : ℕ, Function.Bijective (quotientPiAlgHom J U n))
    (y : ∀ i, AdicCompletion (J.map (algebraMap T (U i))) (U i))
    (i : ι) : piFactor J U i (invAlgHom J U hlvl y) = y i := by
  refine ext_evalₐ fun n => ?_
  rw [evalₐ_piFactor, piLevel_eq, evalₐ_invAlgHom, quotientPiAlgHom_levelAlgEquiv_symm,
    invLevel_apply]
  exact (Ideal.quotientMapPowAlgEquiv (B := U i) J n).apply_symm_apply _

private theorem invAlgHom_piFactor
    (hlvl : ∀ n : ℕ, Function.Bijective (quotientPiAlgHom J U n))
    (x : AdicCompletion J T) :
    invAlgHom J U hlvl (fun i => piFactor J U i x) = x := by
  refine ext_evalₐ fun n => ?_
  rw [evalₐ_invAlgHom]
  have hkey : invLevel J U n (fun i => piFactor J U i x)
      = quotientPiAlgHom J U n (evalₐ J n x) := by
    funext i
    rw [invLevel_apply, evalₐ_piFactor, piLevel_eq]
    exact (Ideal.quotientMapPowAlgEquiv (B := U i) J n).symm_apply_apply _
  rw [hkey]
  exact (levelAlgEquiv J U hlvl n).symm_apply_apply _

/-- If for every `n` the canonical map `T ⧸ Jⁿ → ∀ i, U i ⧸ Jⁿ U i` is bijective, then the
canonical map from the `J`-adic completion of `T` to the product of the `J U i`-adic completions
of the `U i` is an isomorphism of `T`-algebras. -/
private noncomputable def adicCompletionPiAlgEquiv
    (hlvl : ∀ n : ℕ, Function.Bijective (quotientPiAlgHom J U n))
    :
    AdicCompletion J T ≃ₐ[T] ∀ i, AdicCompletion (J.map (algebraMap T (U i))) (U i) :=
  AlgEquiv.ofAlgHom (AlgHom.pi (piFactor J U)) (invAlgHom J U hlvl)
    (AlgHom.ext fun y => funext fun i => piFactor_invAlgHom J U hlvl y i)
    (AlgHom.ext fun x => invAlgHom_piFactor J U hlvl x)

/-- If `J = K` and the canonical map `T ⧸ K → ∀ i, U i ⧸ K U i` is bijective, then so is the
canonical map `T ⧸ J → ∀ i, U i ⧸ J U i`. -/
private theorem bijective_algebraMap_pi_quotient_of_eq {J K : Ideal T} (hJK : J = K)
    (h : Function.Bijective (algebraMap (T ⧸ K) (∀ i, U i ⧸ K.map (algebraMap T (U i))))) :
    Function.Bijective (algebraMap (T ⧸ J) (∀ i, U i ⧸ J.map (algebraMap T (U i)))) :=
  hJK ▸ h

/-- Let `I` be an ideal of `A`, let `T` be an `A`-algebra and let `U i` be `T`-algebras. If for
every `n` the canonical map `T ⧸ Iⁿ T → ∀ i, U i ⧸ Iⁿ U i` is bijective, then the `I T`-adic
completion of `T` is the product of the `I U i`-adic completions of the `U i`, as `T`-algebras. -/
private noncomputable def adicCompletionMapPiAlgEquiv {A : Type*} [CommRing A] [Algebra A T]
    (I : Ideal A)
    (h : ∀ n : ℕ, Function.Bijective (algebraMap (T ⧸ (I ^ n).map (algebraMap A T))
      (∀ i, U i ⧸ ((I ^ n).map (algebraMap A T)).map (algebraMap T (U i))))) :
    AdicCompletion (I.map (algebraMap A T)) T ≃ₐ[T]
      ∀ i, AdicCompletion ((I.map (algebraMap A T)).map (algebraMap T (U i))) (U i) :=
  adicCompletionPiAlgEquiv _ U fun n => by
    simp only [quotientPiAlgHom, IsScalarTower.coe_toAlgHom']
    exact bijective_algebraMap_pi_quotient_of_eq U
      (Ideal.map_pow (algebraMap A T) I n).symm (h n)

end AdicCompletionPi

/-- An Artinian ring `B` is the product of its localizations at its maximal ideals: if a family
`Bq` of localizations of `B` is indexed, bijectively, by the maximal ideals of `B`, then the
canonical map `B → ∀ i, Bq i` is bijective. -/
@[ega "I 6.2.2" "affine, special case", sga "3 VIIB 0.1.1" "partial"]
private theorem bijective_algebraMap_pi_of_isArtinianRing {B : Type*} [CommRing B]
    [IsArtinianRing B] {ι : Type*} (𝔪 : ι → MaximalSpectrum B) (hbij : Function.Bijective 𝔪)
    (Bq : ι → Type*) [∀ i, CommRing (Bq i)] [∀ i, Algebra B (Bq i)]
    [∀ i, IsLocalization.AtPrime (Bq i) (𝔪 i).asIdeal] :
    Function.Bijective (algebraMap B (∀ i, Bq i)) := by
  classical
  let E : ∀ i : ι, Bq i ≃ₐ[B] Localization.AtPrime (𝔪 i).asIdeal := fun i =>
    IsLocalization.algEquiv (𝔪 i).asIdeal.primeCompl (Bq i)
      (Localization.AtPrime (𝔪 i).asIdeal)
  let F : (∀ j : MaximalSpectrum B, Localization.AtPrime j.asIdeal) ≃ (∀ i, Bq i) :=
    (Equiv.piCongrLeft (fun j : MaximalSpectrum B => Localization.AtPrime j.asIdeal)
      (Equiv.ofBijective 𝔪 hbij)).symm.trans (Equiv.piCongrRight fun i => (E i).symm.toEquiv)
  have key : F ∘ MaximalSpectrum.toPiLocalizationEquiv B = algebraMap B (∀ i, Bq i) := by
    refine funext fun x => funext fun i => ?_
    show (E i).symm ((Equiv.piCongrLeft _ (Equiv.ofBijective 𝔪 hbij)).symm
      (MaximalSpectrum.toPiLocalizationEquiv B x) i) = _
    rw [Equiv.piCongrLeft_symm_apply, MaximalSpectrum.toPiLocalizationEquiv_apply_apply]
    exact (E i).symm.commutes x
  rw [← key]
  exact F.bijective.comp (MaximalSpectrum.toPiLocalizationEquiv B).bijective

/-- For `A` a Noetherian local ring with maximal ideal `m` and `T` a finite `A`-algebra, the ring
`T ⧸ mⁿT` is Artinian for every `n ≥ 1`. -/
private theorem isArtinianRing_quotient_map_pow {A : Type*} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (T : Type*) [CommRing T] [Algebra A T] [Module.Finite A T] {n : ℕ}
    (hn : n ≠ 0) : IsArtinianRing (T ⧸ (maximalIdeal A ^ n).map (algebraMap A T)) := by
  have hA : IsArtinianRing (A ⧸ maximalIdeal A ^ n) := by
    refine IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _
      ⟨⟨inferInstance, Ideal.pow_le_self hn⟩, fun q hq _ => ?_⟩
    exact (Ideal.IsPrime.pow_le_iff (hP := hq.1) hn).mp hq.2
  have h1 : Module.Finite A (T ⧸ (maximalIdeal A ^ n).map (algebraMap A T)) := inferInstance
  exact LocalFiniteFibre.isArtinianRing_quotient_map (S := T) (maximalIdeal A ^ n)

/-- Let `J` be an ideal of `T` with `T ⧸ J` Artinian, and let `𝔫 i` be primes of `T` localizing to
`Tq i` whose images `𝔮 i` in `T ⧸ J` are, bijectively, all the maximal ideals of `T ⧸ J`. Then the
canonical map `T ⧸ J → ∀ i, Tq i ⧸ J Tq i` is bijective. -/
@[ega "I 6.2.2" "affine, special case", sga "3 VIIB 0.1.1" "partial"]
private theorem bijective_algebraMap_pi_quotient {T : Type*} [CommRing T] (J : Ideal T)
    [IsArtinianRing (T ⧸ J)] {ι : Type*} (𝔫 : ι → Ideal T) [∀ i, (𝔫 i).IsPrime]
    (Tq : ι → Type*) [∀ i, CommRing (Tq i)] [∀ i, Algebra T (Tq i)]
    [∀ i, IsLocalization.AtPrime (Tq i) (𝔫 i)]
    (𝔮 : ι → MaximalSpectrum (T ⧸ J)) (hbij : Function.Bijective 𝔮)
    (hcomap : ∀ i, (𝔮 i).asIdeal.comap (Ideal.Quotient.mk J) = 𝔫 i) :
    Function.Bijective
      (algebraMap (T ⧸ J) (∀ i, Tq i ⧸ J.map (algebraMap T (Tq i)))) := by
  have : ∀ i, IsLocalization.AtPrime (Tq i ⧸ J.map (algebraMap T (Tq i))) (𝔮 i).asIdeal :=
    fun i => isLocalization_atPrime_quotient (𝔫 i) (Tq i) J (𝔮 i).asIdeal (hcomap i)
  exact bijective_algebraMap_pi_of_isArtinianRing 𝔮 hbij _

/-- The image of `p.primeCompl` in `S` misses every prime of `S` lying over `p`. -/
private theorem algebraMapSubmonoid_le_primeCompl {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    Algebra.algebraMapSubmonoid S p.primeCompl ≤ q.primeCompl := by
  rintro _ ⟨x, hx, rfl⟩ hmem
  exact hx (by rw [Ideal.over_def q p]; exact hmem)

/-- The image of `p.primeCompl` in `S` is disjoint from every prime of `S` lying over `p`. -/
private theorem disjoint_algebraMapSubmonoid {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    Disjoint ((Algebra.algebraMapSubmonoid S p.primeCompl : Submonoid S) : Set S) (q : Set S) :=
  Set.disjoint_left.mpr fun _ ha => algebraMapSubmonoid_le_primeCompl p q ha

/-- For `Rₚ` the local ring of `R` at `p` and `T` an `Rₚ`-algebra, an ideal of `T` lies over the
maximal ideal of `Rₚ` if and only if it lies over `p`. -/
private theorem under_eq_maximalIdeal_iff_under_eq {R T : Type*} [CommRing R] [CommRing T]
    [Algebra R T] (p : Ideal R) [p.IsPrime] (Rp : Type*) [CommRing Rp] [Algebra R Rp]
    [IsLocalization.AtPrime Rp p] [IsLocalRing Rp] [Algebra Rp T] [IsScalarTower R Rp T]
    (𝔫 : Ideal T) :
    𝔫.under Rp = maximalIdeal Rp ↔ 𝔫.under R = p := by
  have hmap : ∀ J : Ideal Rp, (J.under R).map (algebraMap R Rp) = J := fun J =>
    IsLocalization.map_under p.primeCompl Rp J
  have hm : (maximalIdeal Rp).under R = p := IsLocalization.AtPrime.under_maximalIdeal Rp p
  have hu : (𝔫.under Rp).under R = 𝔫.under R := Ideal.under_under 𝔫
  refine ⟨fun h => by rw [← hu, h, hm], fun h => ?_⟩
  rw [← hmap (𝔫.under Rp), hu, h, ← hm, hmap]

/-- Let `T` be the localization of `S` at the image of `R ∖ p`. For `q` a prime of `S` lying over
`p`, the ideal `qT` is prime. -/
private theorem isPrime_map_of_liesOver {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] (p : Ideal R) [p.IsPrime]
    [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) T]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p] : (q.map (algebraMap S T)).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint (Algebra.algebraMapSubmonoid S p.primeCompl) T q
    inferInstance (disjoint_algebraMapSubmonoid p q)

/-- Let `T` be the localization of `S` at the image of `R ∖ p`. For `q` a prime of `S` lying over
`p`, the ideal `qT` contracts to `q`. -/
private theorem under_map_eq {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] (p : Ideal R) [p.IsPrime]
    [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) T]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p] : (q.map (algebraMap S T)).under S = q :=
  IsLocalization.under_map_of_isPrime_disjoint (Algebra.algebraMapSubmonoid S p.primeCompl) T
    inferInstance (disjoint_algebraMapSubmonoid p q)

/-- Let `T` be the localization of `S` at the image of `p.primeCompl` and let `q` be a prime of
`S` lying over `p`. Then the localization `S_q` of `S` at `q` is the localization of `T` at the
prime `qT`. -/
private theorem isLocalization_atPrime_map {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] (p : Ideal R) [p.IsPrime]
    [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) T]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p] [hqT : (q.map (algebraMap S T)).IsPrime]
    (Sq : Type*) [CommRing Sq] [Algebra S Sq] [IsLocalization.AtPrime Sq q]
    [Algebra T Sq] [IsScalarTower S T Sq] :
    IsLocalization (q.map (algebraMap S T)).primeCompl Sq := by
  have hMle : Algebra.algebraMapSubmonoid S p.primeCompl ≤ q.primeCompl :=
    algebraMapSubmonoid_le_primeCompl p q
  have hunder : (q.map (algebraMap S T)).under S = q := under_map_eq p q
  have hle : q.primeCompl.map (algebraMap S T) ≤ (q.map (algebraMap S T)).primeCompl := by
    rintro _ ⟨x, hx, rfl⟩ hmem
    exact hx (by rw [← hunder]; exact hmem)
  have h1 : IsLocalization (q.primeCompl.map (algebraMap S T)) Sq :=
    IsLocalization.isLocalization_of_submonoid_le T Sq _ q.primeCompl hMle
  refine IsLocalization.of_le (q.primeCompl.map (algebraMap S T)) _ hle ?_
  intro y hy
  obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid S p.primeCompl) y
  have hs : (s : S) ∉ q := hMle s.2
  have hsc : algebraMap S T (s : S) ∈ (q.map (algebraMap S T)).primeCompl := hle ⟨s, hs, rfl⟩
  have hxq : x ∉ q := by
    intro hxq
    have h2 : y * algebraMap S T (s : S) ∈ q.map (algebraMap S T) := by
      rw [hxs]; exact Ideal.mem_map_of_mem _ hxq
    exact (hqT.mem_or_mem h2).elim hy hsc
  have key : algebraMap T Sq y * algebraMap S Sq (s : S) = algebraMap S Sq x := by
    rw [IsScalarTower.algebraMap_apply S T Sq (s : S), IsScalarTower.algebraMap_apply S T Sq x,
      ← map_mul, hxs]
  have hu : IsUnit (algebraMap T Sq y * algebraMap S Sq (s : S)) := by
    rw [key]; exact IsLocalization.map_units (M := q.primeCompl) Sq ⟨x, hxq⟩
  exact isUnit_of_mul_isUnit_left hu

/-- Let `T` be the localization of `S` at the image of `R ∖ p` and `q` a prime of `S` lying over
`p`. Then the prime `qT` of `T` contracts to the maximal ideal of `Rₚ`. -/
private theorem under_map_eq_maximalIdeal {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] (p : Ideal R) [p.IsPrime]
    [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) T]
    (Rp : Type*) [CommRing Rp] [Algebra R Rp] [IsLocalization.AtPrime Rp p] [IsLocalRing Rp]
    [Algebra Rp T] [IsScalarTower R Rp T]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    (q.map (algebraMap S T)).under Rp = maximalIdeal Rp := by
  refine (under_eq_maximalIdeal_iff_under_eq p Rp _).mpr ?_
  rw [← Ideal.under_under (A := R) (B := S) (q.map (algebraMap S T)), under_map_eq p q,
    ← Ideal.over_def q p]

/-- Let `T` be the localization `S_p` of `S` at `p`, a finite algebra over the local ring `Rₚ` with
maximal ideal `m`, and for each prime `q` of `S` lying over `p` let `S_q` be the localization of
`S` at `q`, viewed as a `T`-algebra. Then for every `n` the canonical map

`T ⧸ mⁿT → ∀ q, S_q ⧸ mⁿ S_q`

is bijective. -/
private theorem bijective_algebraMap_pi_quotient_pow
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
    [Algebra R T] [IsScalarTower R S T] (p : Ideal R) [p.IsPrime]
    [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) T]
    (Rp : Type*) [CommRing Rp] [Algebra R Rp] [IsLocalization.AtPrime Rp p] [IsLocalRing Rp]
    [IsNoetherianRing Rp] [Algebra Rp T] [IsScalarTower R Rp T] [Module.Finite Rp T]
    (Sq : p.primesOver S → Type*) [∀ q, CommRing (Sq q)] [∀ q, Algebra S (Sq q)]
    [∀ q, IsLocalization.AtPrime (Sq q) q.1]
    [∀ q, Algebra T (Sq q)] [∀ q, IsScalarTower S T (Sq q)] (n : ℕ) :
    Function.Bijective (algebraMap (T ⧸ ((maximalIdeal Rp) ^ n).map (algebraMap Rp T))
      (∀ q, Sq q ⧸ (((maximalIdeal Rp) ^ n).map (algebraMap Rp T)).map (algebraMap T (Sq q)))) := by
  classical
  rcases eq_or_ne n 0 with rfl | hn
  · have h1 : ((maximalIdeal Rp) ^ 0).map (algebraMap Rp T) = ⊤ := by
      rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]
    have : Subsingleton (T ⧸ ((maximalIdeal Rp) ^ 0).map (algebraMap Rp T)) :=
      Ideal.Quotient.subsingleton_iff.mpr h1
    have : ∀ q : p.primesOver S, Subsingleton
        (Sq q ⧸ (((maximalIdeal Rp) ^ 0).map (algebraMap Rp T)).map (algebraMap T (Sq q))) :=
      fun q => Ideal.Quotient.subsingleton_iff.mpr (by rw [h1, Ideal.map_top])
    exact ⟨fun x y _ => Subsingleton.elim x y, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  have hart : IsArtinianRing (T ⧸ ((maximalIdeal Rp) ^ n).map (algebraMap Rp T)) :=
    isArtinianRing_quotient_map_pow (A := Rp) T hn
  have hprime : ∀ q : p.primesOver S, (q.1.map (algebraMap S T)).IsPrime := fun q =>
    isPrime_map_of_liesOver p q.1
  have hloc : ∀ q : p.primesOver S, IsLocalization (q.1.map (algebraMap S T)).primeCompl (Sq q) :=
    fun q => isLocalization_atPrime_map p q.1 (Sq q)
  have hJle : ∀ 𝔫 : Ideal T, 𝔫.IsPrime → 𝔫.under Rp = maximalIdeal Rp →
      ((maximalIdeal Rp) ^ n).map (algebraMap Rp T) ≤ 𝔫 := by
    intro 𝔫 _ h
    rw [Ideal.map_le_iff_le_comap, ← Ideal.under_def, h]
    exact Ideal.pow_le_self hn
  have hunderq : ∀ q : p.primesOver S, (q.1.map (algebraMap S T)).under Rp = maximalIdeal Rp :=
    fun q => under_map_eq_maximalIdeal p Rp q.1
  have hunderS : ∀ q : p.primesOver S, (q.1.map (algebraMap S T)).under S = q.1 := fun q =>
    under_map_eq p q.1
  have hmax : ∀ q : p.primesOver S,
      ((q.1.map (algebraMap S T)).map (Ideal.Quotient.mk
        (((maximalIdeal Rp) ^ n).map (algebraMap Rp T)))).IsMaximal := by
    intro q
    have : ((q.1.map (algebraMap S T)).map (Ideal.Quotient.mk
        (((maximalIdeal Rp) ^ n).map (algebraMap Rp T)))).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact hJle _ inferInstance (hunderq q))
    exact (IsArtinianRing.isPrime_iff_isMaximal _).mp inferInstance
  have hcomapaux : ∀ q : p.primesOver S,
      ((q.1.map (algebraMap S T)).map (Ideal.Quotient.mk
          (((maximalIdeal Rp) ^ n).map (algebraMap Rp T)))).comap (Ideal.Quotient.mk
          (((maximalIdeal Rp) ^ n).map (algebraMap Rp T))) = q.1.map (algebraMap S T) := by
    intro q
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left, Ideal.mk_ker]
    exact hJle _ inferInstance (hunderq q)
  refine bijective_algebraMap_pi_quotient _ (fun q => q.1.map (algebraMap S T)) Sq
    (fun q => ⟨_, hmax q⟩) ⟨?_, ?_⟩ (fun q => hcomapaux q)
  · intro q q' hqq'
    have h1 := congrArg MaximalSpectrum.asIdeal hqq'
    have h2 : q.1.map (algebraMap S T) = q'.1.map (algebraMap S T) := by
      rw [← hcomapaux q, ← hcomapaux q']
      exact congrArg (Ideal.comap (Ideal.Quotient.mk
        (((maximalIdeal Rp) ^ n).map (algebraMap Rp T)))) h1
    exact Subtype.ext (by rw [← hunderS q, ← hunderS q', h2])
  · intro 𝔯
    have : 𝔯.asIdeal.IsPrime := 𝔯.isMaximal.isPrime
    set 𝔫 := 𝔯.asIdeal.comap (Ideal.Quotient.mk
      (((maximalIdeal Rp) ^ n).map (algebraMap Rp T))) with h𝔫
    have : 𝔫.IsPrime := Ideal.comap_isPrime _ _
    have hJ𝔫 : ((maximalIdeal Rp) ^ n).map (algebraMap Rp T) ≤ 𝔫 := fun x hx => by
      rw [h𝔫, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact 𝔯.asIdeal.zero_mem
    have hRp : 𝔫.under Rp = maximalIdeal Rp := by
      have : (𝔫.under Rp).IsPrime := Ideal.comap_isPrime (algebraMap Rp T) 𝔫
      exact ((IsLocalRing.maximalIdeal.isMaximal Rp).eq_of_le (Ideal.IsPrime.ne_top inferInstance)
        ((Ideal.IsPrime.pow_le_iff hn).mp (Ideal.map_le_iff_le_comap.mp hJ𝔫))).symm
    have hR : 𝔫.under R = p := (under_eq_maximalIdeal_iff_under_eq p Rp 𝔫).mp hRp
    have hqp : (𝔫.under S).IsPrime := Ideal.comap_isPrime (algebraMap S T) 𝔫
    have : (𝔫.under S).LiesOver p := ⟨by rw [Ideal.under_under (A := R) (B := S) 𝔫, hR]⟩
    have hmapback : (𝔫.under S).map (algebraMap S T) = 𝔫 :=
      IsLocalization.map_under (Algebra.algebraMapSubmonoid S p.primeCompl) T 𝔫
    have hgoal : ((𝔫.under S).map (algebraMap S T)).map (Ideal.Quotient.mk
        (((maximalIdeal Rp) ^ n).map (algebraMap Rp T))) = 𝔯.asIdeal := by
      rw [hmapback, h𝔫, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    exact ⟨⟨𝔫.under S, ⟨hqp, inferInstance⟩⟩, MaximalSpectrum.ext hgoal⟩

/-- The `Rₚ`-module `S ⊗[R] Rₚ` is finite as soon as `S` is a finite `R`-module. -/
private theorem finite_tensor {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] (Rp : Type*) [CommRing Rp] [Algebra R Rp] :
    Module.Finite Rp (S ⊗[R] Rp) := by
  have h : Module.Finite Rp (Rp ⊗[R] S) := Module.Finite.base_change R Rp S
  have e : (Rp ⊗[R] S) ≃ₗ[Rp] (S ⊗[R] Rp) :=
    { (Algebra.TensorProduct.comm R Rp S).toLinearEquiv with
      map_smul' := fun c x => by
        induction x with
        | tmul a b =>
            simp [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply,
              Algebra.TensorProduct.tmul_mul_tmul]
        | add x y hx hy => simp_all }
  exact Module.Finite.equiv e

/-- The comparison `adicCompletionLinearEquivMap` takes `x • of b`, the image of `x ⊗ b` under
`AdicCompletion.ofTensorProduct`, to the product of `b` and the image of `x` in the `IB`-adic
completion of `B`. -/
private theorem adicCompletionLinearEquivMap_smul_of {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (I : Ideal A) (x : AdicCompletion I A) (b : B) :
    adicCompletionLinearEquivMap I B (x • AdicCompletion.of I B b)
      = algebraMap B (AdicCompletion (I.map (algebraMap A B)) B) b *
        AdicCompletion.completionMap I x := by
  refine Subtype.ext (funext fun n => ?_)
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective (I ^ n • (⊤ : Submodule A A)) (x.val n)
  have hab : a • b = b * algebraMap A B a := by rw [Algebra.smul_def, mul_comm]
  have hL : (x • AdicCompletion.of I B b).val n
      = Submodule.Quotient.mk (b * algebraMap A B a) := by
    rw [AdicCompletion.smul_eval, ← ha, ← hab]
    rfl
  have hR : (AdicCompletion.completionMap (B := B) I x).val n =
      Submodule.Quotient.mk (algebraMap A B a) :=
    AdicCompletion.val_completionMap I n x a ha.symm
  have hb : (algebraMap B (AdicCompletion (I.map (algebraMap A B)) B) b).val n
      = Submodule.Quotient.mk b := rfl
  rw [adicCompletionLinearEquivMap_val, hL, quotEquivMapPow_mk, AdicCompletion.val_mul, hR, hb]
  rfl

/-- For an `A`-algebra `B` and an ideal `I` of `A`, the canonical `B`-algebra map
`B ⊗[A] A^∧ → B^∧` to the `IB`-adic completion of `B`, `b ⊗ x ↦ b · x`. -/
private noncomputable def ofTensorAlgHom {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) :
    B ⊗[A] AdicCompletion I A →ₐ[B] AdicCompletion (I.map (algebraMap A B)) B :=
  letI : IsScalarTower A B (AdicCompletion (I.map (algebraMap A B)) B) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  AlgHom.liftEquiv A B (AdicCompletion I A) (AdicCompletion (I.map (algebraMap A B)) B)
    (AdicCompletion.completionMap I)

private theorem ofTensorAlgHom_tmul {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (b : B) (x : AdicCompletion I A) :
    ofTensorAlgHom I (b ⊗ₜ x)
      = algebraMap B (AdicCompletion (I.map (algebraMap A B)) B) b *
        AdicCompletion.completionMap I x :=
  Algebra.smul_def b (AdicCompletion.completionMap I x)

/-- For `A` Noetherian and `B` an `A`-algebra finite as an `A`-module, the canonical `B`-algebra
map `ofTensorAlgHom I : B ⊗[A] A^∧ → B^∧` to the `IB`-adic completion of the ring `B` is
bijective. -/
@[ega "0 7.3.3" "special case", ega "0 7.7.8" "B = Â"]
private theorem bijective_ofTensorAlgHom {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Finite A B] (I : Ideal A) :
    Function.Bijective (ofTensorAlgHom (A := A) (B := B) I) := by
  have hfun : (⇑(ofTensorAlgHom (A := A) (B := B) I)) ∘
        (⇑(Algebra.TensorProduct.comm A (AdicCompletion I A) B))
      = ⇑(adicCompletionLinearEquivMap I B) ∘ ⇑(AdicCompletion.ofTensorProduct I B) := by
    refine funext fun z => ?_
    induction z with
    | tmul x b =>
        rw [Function.comp_apply, Function.comp_apply, Algebra.TensorProduct.comm_tmul,
          ofTensorAlgHom_tmul, AdicCompletion.ofTensorProduct_tmul,
          adicCompletionLinearEquivMap_smul_of]
    | add z w hz hw =>
        simp only [Function.comp_apply, map_add] at hz hw ⊢
        rw [hz, hw]
  refine (Function.Bijective.of_comp_iff _
    (Algebra.TensorProduct.comm A (AdicCompletion I A) B).bijective).mp ?_
  exact hfun ▸ (adicCompletionLinearEquivMap I B).bijective.comp
    (AdicCompletion.bijective_ofTensorProduct I B)

/-- For `U` an algebra over an `A`-algebra `T`, the `(I T) U`-adic and the `I U`-adic completions
of `U` are isomorphic as `U`-algebras. -/
private noncomputable def adicCompletionMapMapAlgEquiv {A T U : Type*} [CommRing A] [CommRing T]
    [CommRing U] [Algebra A T] [Algebra T U] [Algebra A U] [IsScalarTower A T U] (I : Ideal A) :
    AdicCompletion ((I.map (algebraMap A T)).map (algebraMap T U)) U ≃ₐ[U]
      AdicCompletion (I.map (algebraMap A U)) U := by
  have h : (I.map (algebraMap A T)).map (algebraMap T U) = I.map (algebraMap A U) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  rw [h]

/-- If `T ⧸ J` is a finite `A`-module and the canonical map `T ⧸ J → V ⧸ JV` is surjective, then
`V ⧸ JV` is a finite `A`-module. -/
private theorem finite_quotient_map_of_surjective {A T V : Type*} [CommRing A] [CommRing T]
    [CommRing V] [Algebra A T] [Algebra T V] [Algebra A V] [IsScalarTower A T V]
    (J : Ideal T) [Module.Finite A (T ⧸ J)]
    (hsurj : Function.Surjective (algebraMap (T ⧸ J) (V ⧸ J.map (algebraMap T V)))) :
    Module.Finite A (V ⧸ J.map (algebraMap T V)) := by
  have htower : IsScalarTower A (T ⧸ J) (V ⧸ J.map (algebraMap T V)) := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    have h1 : algebraMap A (T ⧸ J) a = Ideal.Quotient.mk J (algebraMap A T a) := rfl
    have h2 : Ideal.Quotient.mk (J.map (algebraMap T V)) (algebraMap A V a)
        = algebraMap A (V ⧸ J.map (algebraMap T V)) a := rfl
    rw [h1, Ideal.Quotient.algebraMap_quotient_map_quotient,
      ← IsScalarTower.algebraMap_apply A T V, h2]
  have : Module.Finite (T ⧸ J) (V ⧸ J.map (algebraMap T V)) :=
    Module.Finite.of_surjective (Algebra.linearMap (T ⧸ J) _) hsurj
  exact Module.Finite.trans (T ⧸ J) _

/-- Let `m` be the maximal ideal of `Rₚ`, let `S_p = S ⊗[R] Rₚ`, and let the local rings `S_q` at
the primes `q` of `S` lying over `p` be `S_p`-algebras. If for every `n` the canonical map
`S_p ⧸ mⁿ S_p → ∀ q, S_q ⧸ mⁿ S_q` is bijective, then `S_p ⊗[Rₚ] Rₚ^∧` is, as an `S`-algebra, the
product of the completions of the `S_q` at their maximal ideals. -/
private theorem nonempty_algEquiv_pi_of_bijective_of_bijective_quotient {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime]
    (Rp : Type*) [CommRing Rp] [Algebra R Rp] [IsLocalization.AtPrime Rp p] [IsLocalRing Rp]
    (Sq : p.primesOver S → Type*) [∀ q, CommRing (Sq q)] [∀ q, Algebra S (Sq q)]
    [∀ q, IsLocalization.AtPrime (Sq q) q.1] [∀ q, IsLocalRing (Sq q)]
    [∀ q, Algebra (S ⊗[R] Rp) (Sq q)] [∀ q, IsScalarTower S (S ⊗[R] Rp) (Sq q)]
    (hlevel : ∀ n : ℕ, Function.Bijective
      (algebraMap ((S ⊗[R] Rp) ⧸ ((maximalIdeal Rp) ^ n).map (algebraMap Rp (S ⊗[R] Rp)))
        (∀ q, Sq q ⧸ (((maximalIdeal Rp) ^ n).map (algebraMap Rp (S ⊗[R] Rp))).map
          (algebraMap (S ⊗[R] Rp) (Sq q))))) :
    Nonempty ((S ⊗[R] Rp) ⊗[Rp] AdicCompletion (maximalIdeal Rp) Rp ≃ₐ[S]
      ∀ q, AdicCompletion (maximalIdeal (Sq q)) (Sq q)) := by
  have htower : IsScalarTower R Rp (S ⊗[R] Rp) := isScalarTower_tensor (R := R) (S := S) Rp
  have hfinT : Module.Finite Rp (S ⊗[R] Rp) := finite_tensor (R := R) (S := S) Rp
  have hnoethRp : IsNoetherianRing Rp := IsLocalization.isNoetherianRing p.primeCompl Rp ‹_›
  have hnoethS : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  have hprime : ∀ q : p.primesOver S, (q.1.map (algebraMap S (S ⊗[R] Rp))).IsPrime := fun q =>
    isPrime_map_of_liesOver p q.1
  have hloc : ∀ q : p.primesOver S,
      IsLocalization (q.1.map (algebraMap S (S ⊗[R] Rp))).primeCompl (Sq q) := fun q =>
    isLocalization_atPrime_map p q.1 (Sq q)
  let algRpSq : ∀ q : p.primesOver S, Algebra Rp (Sq q) := fun q =>
    ((algebraMap (S ⊗[R] Rp) (Sq q)).comp (algebraMap Rp (S ⊗[R] Rp))).toAlgebra
  have htowerRp : ∀ q : p.primesOver S, IsScalarTower Rp (S ⊗[R] Rp) (Sq q) := fun q =>
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hlocalHom : ∀ q : p.primesOver S, IsLocalHom (algebraMap Rp (Sq q)) := by
    intro q
    have hcomapT : (maximalIdeal (Sq q)).comap (algebraMap (S ⊗[R] Rp) (Sq q))
        = q.1.map (algebraMap S (S ⊗[R] Rp)) :=
      IsLocalization.AtPrime.under_maximalIdeal (Sq q) (q.1.map (algebraMap S (S ⊗[R] Rp)))
    have hcomapS : (q.1.map (algebraMap S (S ⊗[R] Rp))).comap (algebraMap Rp (S ⊗[R] Rp))
        = maximalIdeal Rp := under_map_eq_maximalIdeal p Rp q.1
    have hcomapRp : (maximalIdeal (Sq q)).comap (algebraMap Rp (Sq q)) = maximalIdeal Rp := by
      rw [show algebraMap Rp (Sq q)
          = (algebraMap (S ⊗[R] Rp) (Sq q)).comp (algebraMap Rp (S ⊗[R] Rp)) from rfl,
        ← Ideal.comap_comap, hcomapT, hcomapS]
    exact ((IsLocalRing.local_hom_TFAE (algebraMap Rp (Sq q))).out 5 1).mp hcomapRp
  have hfinquot :
      Module.Finite Rp ((S ⊗[R] Rp) ⧸ ((maximalIdeal Rp) ^ 1).map (algebraMap Rp (S ⊗[R] Rp))) :=
    inferInstance
  have hsurj : ∀ q : p.primesOver S, Function.Surjective
      (algebraMap ((S ⊗[R] Rp) ⧸ ((maximalIdeal Rp) ^ 1).map (algebraMap Rp (S ⊗[R] Rp)))
        (Sq q ⧸ (((maximalIdeal Rp) ^ 1).map (algebraMap Rp (S ⊗[R] Rp))).map
          (algebraMap (S ⊗[R] Rp) (Sq q)))) := fun q =>
    (Function.surjective_eval q).comp (hlevel 1).surjective
  have hfibre : ∀ q : p.primesOver S,
      Module.Finite Rp (Sq q ⧸ (maximalIdeal Rp).map (algebraMap Rp (Sq q))) := by
    intro q
    have hideal : (maximalIdeal Rp).map (algebraMap Rp (Sq q))
        = (((maximalIdeal Rp) ^ 1).map (algebraMap Rp (S ⊗[R] Rp))).map
          (algebraMap (S ⊗[R] Rp) (Sq q)) := by
      rw [pow_one, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    rw [hideal]
    exact finite_quotient_map_of_surjective _ (hsurj q)
  let eL : (S ⊗[R] Rp) ⊗[Rp] AdicCompletion (maximalIdeal Rp) Rp ≃ₐ[S ⊗[R] Rp]
      AdicCompletion ((maximalIdeal Rp).map (algebraMap Rp (S ⊗[R] Rp))) (S ⊗[R] Rp) :=
    AlgEquiv.ofBijective (ofTensorAlgHom (maximalIdeal Rp)) (bijective_ofTensorAlgHom _)
  let eM := adicCompletionMapPiAlgEquiv (T := S ⊗[R] Rp) Sq (maximalIdeal Rp) hlevel
  have eC : ∀ q : p.primesOver S, Nonempty
      (AdicCompletion ((((maximalIdeal Rp).map (algebraMap Rp (S ⊗[R] Rp))).map
          (algebraMap (S ⊗[R] Rp) (Sq q)))) (Sq q) ≃ₐ[Sq q]
        AdicCompletion (maximalIdeal (Sq q)) (Sq q)) := by
    intro q
    have : IsNoetherianRing (Sq q) :=
      IsLocalization.isNoetherianRing q.1.primeCompl (Sq q) hnoethS
    exact (AdicCompletion.nonempty_algEquiv_map_and_finite (R := Rp) (S := Sq q)
      (IsNoetherian.noetherian _)).1.map fun e => (adicCompletionMapMapAlgEquiv _).trans e.symm
  have htowerL : IsScalarTower S (S ⊗[R] Rp)
      ((S ⊗[R] Rp) ⊗[Rp] AdicCompletion (maximalIdeal Rp) Rp) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have htowerC : ∀ (q : p.primesOver S) (I : Ideal (Sq q)),
      IsScalarTower S (Sq q) (AdicCompletion I (Sq q)) := fun _ _ =>
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have htowerM : ∀ I : Ideal (S ⊗[R] Rp),
      IsScalarTower S (S ⊗[R] Rp) (AdicCompletion I (S ⊗[R] Rp)) := fun _ =>
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have htowerPi : IsScalarTower S (S ⊗[R] Rp) (∀ q : p.primesOver S,
      AdicCompletion ((((maximalIdeal Rp).map (algebraMap Rp (S ⊗[R] Rp))).map
        (algebraMap (S ⊗[R] Rp) (Sq q)))) (Sq q)) := by
    refine IsScalarTower.of_algebraMap_eq fun s => funext fun q => ?_
    rw [Pi.algebraMap_apply, Pi.algebraMap_apply, AdicCompletion.algebraMap_apply,
      AdicCompletion.algebraMap_apply, IsScalarTower.algebraMap_apply S (S ⊗[R] Rp) (Sq q)]
  exact ⟨(eL.restrictScalars S).trans ((eM.restrictScalars S).trans
    (AlgEquiv.piCongrRight fun q => ((eC q).some.restrictScalars S)))⟩

/-- The base change of `S_p = S ⊗[R] Rₚ` along the completion of `Rₚ` is, as an `S`-algebra, the
product, over the primes `q` of `S` lying over `p`, of the completions of the local rings `S_q` at
their maximal ideals. -/
private theorem nonempty_algEquiv_pi_of_tensor {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [Module.Finite R S] (p : Ideal R) [p.IsPrime]
    (Rp : Type*) [CommRing Rp] [Algebra R Rp] [IsLocalization.AtPrime Rp p] [IsLocalRing Rp]
    (Sq : p.primesOver S → Type*) [∀ q, CommRing (Sq q)] [∀ q, Algebra S (Sq q)]
    [∀ q, IsLocalization.AtPrime (Sq q) q.1] [∀ q, IsLocalRing (Sq q)] :
    Nonempty ((S ⊗[R] Rp) ⊗[Rp] AdicCompletion (maximalIdeal Rp) Rp ≃ₐ[S]
      ∀ q, AdicCompletion (maximalIdeal (Sq q)) (Sq q)) := by
  have htower := isScalarTower_tensor (R := R) (S := S) Rp
  have hfin : Module.Finite Rp (S ⊗[R] Rp) := finite_tensor (R := R) (S := S) Rp
  have hnoeth : IsNoetherianRing Rp := IsLocalization.isNoetherianRing p.primeCompl Rp ‹_›
  let halg : ∀ q : p.primesOver S, Algebra (S ⊗[R] Rp) (Sq q) := fun q =>
    IsLocalization.localizationAlgebraOfSubmonoidLe (R := S) (S := S ⊗[R] Rp) (T := Sq q)
      (Algebra.algebraMapSubmonoid S p.primeCompl) q.1.primeCompl
      (algebraMapSubmonoid_le_primeCompl p q.1)
  have : ∀ q : p.primesOver S, IsScalarTower S (S ⊗[R] Rp) (Sq q) := fun q =>
    IsLocalization.localization_isScalarTower_of_submonoid_le (R := S) (S := S ⊗[R] Rp)
      (T := Sq q) (Algebra.algebraMapSubmonoid S p.primeCompl) q.1.primeCompl
      (algebraMapSubmonoid_le_primeCompl p q.1)
  exact nonempty_algEquiv_pi_of_bijective_of_bijective_quotient p Rp Sq
    (fun n => bijective_algebraMap_pi_quotient_pow p Rp Sq n)

/-- Let `R` be a Noetherian ring, `S` a finite `R`-algebra, `p` a prime of `R`, `Rₚ` the local ring
of `R` at `p` and `S_q` the local ring of `S` at each prime `q` lying over `p`. Then
`S ⊗[R] Rₚ^∧` is, as an `S`-algebra, the product of the completions of the `S_q` at their maximal
ideals. -/
public theorem solution
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Module.Finite R S] (p : Ideal R) [p.IsPrime]
    (Rp : Type*) [CommRing Rp] [Algebra R Rp] [IsLocalization.AtPrime Rp p] [IsLocalRing Rp]
    (Sq : p.primesOver S → Type*) [∀ q, CommRing (Sq q)] [∀ q, Algebra S (Sq q)]
    [∀ q, IsLocalization.AtPrime (Sq q) q.1] [∀ q, IsLocalRing (Sq q)] :
    Nonempty (S ⊗[R] AdicCompletion (maximalIdeal Rp) Rp ≃ₐ[S]
      ∀ q, AdicCompletion (maximalIdeal (Sq q)) (Sq q)) := by
  obtain ⟨e₁⟩ := nonempty_algEquiv_tensor_tensor (S := S) p Rp
  exact (nonempty_algEquiv_pi_of_tensor p Rp Sq).map e₁.trans

end Stacks.AdicCompletion.PrimesOverProduct

end

@[expose] public section

open TensorProduct IsLocalRing

/-- Let `R` be a Noetherian ring, `S` a finite `R`-algebra and `p` a prime of `R`. Let `Rₚ` be the
local ring of `R` at `p` and, for each of the (finitely many) primes `q` of `S` lying over `p`, let
`S_q` be the local ring of `S` at `q`. Then the base change of `S` along the completion `Rₚ^∧` of
`Rₚ` at its maximal ideal is, as an `S`-algebra, the product of the completions `S_q^∧` of the
`S_q` at their maximal ideals: `Rₚ^∧ ⊗[R] S = S_{q₁}^∧ × ⋯ × S_{q_m}^∧`. -/
@[stacks 07N9 "The source's middle term `(S_p)^∧` is Mathlib's \
`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian` over `Rₚ`; the two outer terms are \
identified here. See the module docstring."]
public theorem AdicCompletion.nonempty_algEquiv_pi_primesOver
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Module.Finite R S] (p : Ideal R) [p.IsPrime]
    (Rp : Type*) [CommRing Rp] [Algebra R Rp] [IsLocalization.AtPrime Rp p] [IsLocalRing Rp]
    (Sq : p.primesOver S → Type*) [∀ q, CommRing (Sq q)] [∀ q, Algebra S (Sq q)]
    [∀ q, IsLocalization.AtPrime (Sq q) q.1] [∀ q, IsLocalRing (Sq q)] :
    Nonempty (S ⊗[R] AdicCompletion (maximalIdeal Rp) Rp ≃ₐ[S]
      ∀ q, AdicCompletion (maximalIdeal (Sq q)) (Sq q)) :=
  Stacks.AdicCompletion.PrimesOverProduct.solution p Rp Sq

end
