module

public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import StacksFrontier.RingTheory.CompleteIntersection.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# The universal factorization map is a relative global complete intersection

Let `R` be a ring and `n = m + k`. The universal factorization map
`φ : R[a_0, …, a_{n-1}] → S = R[b_0, …, b_{m-1}] ⊗_R R[c_0, …, c_{k-1}]` is the `R`-algebra map
for which the free monic polynomial of degree `n` factors as
`x^n + a_{n-1} x^{n-1} + ⋯ + a_0 = g h` over `S`, with `g = x^m + b_{m-1} x^{m-1} + ⋯ + b_0` and
`h = x^k + c_{k-1} x^{k-1} + ⋯ + c_0` (`MvPolynomial.universalFactorizationMap`). Its canonical
presentation (`MvPolynomial.universalFactorizationMapPresentation`) has the `m + k` generators
`b_i, c_j` and the `n` relations `a_l = a_l(b_i, c_j)`.

Let `R[a] → K` be a ring map into a field, with `a_l ↦ α_l`, and let `L` be a `K`-algebra. A
`K`-algebra map `K ⊗_{R[a]} S → L` is the same thing as a factorization
`x^n + α_{n-1} x^{n-1} + ⋯ + α_0 = g h` over `L` into monic polynomials of degrees `m` and `k`.
Every fibre ring `K ⊗_{R[a]} S` has finitely many prime ideals and, when nonzero, Krull dimension
`0`; a polynomial over a field has only finitely many factorizations into monic polynomials of
given degrees; and the canonical presentation is a relative global complete intersection.

## Main definitions

* `MvPolynomial.universalFactorizationMapBaseChangeAlgHomEquiv`: `K`-algebra maps from the fibre
  ring `K ⊗_{R[a]} S` to a `K`-algebra `L` are factorizations over `L` of the image of the free
  monic polynomial.

## Main results

* `Polynomial.finite_monicDegreeEq_mul_eq`: over a field a polynomial has finitely many
  factorizations into monic polynomials of given degrees.
* `MvPolynomial.isIntegral_universalFactorizationMap`: `S` is integral over `R[a]`.
* `MvPolynomial.finite_primeSpectrum_tensorProduct_universalFactorizationMap`: every fibre of
  `φ` has finitely many points.
* `MvPolynomial.ringKrullDim_tensorProduct_universalFactorizationMap`: every nonempty fibre of `φ`
  has dimension `0`.
* `MvPolynomial.universalFactorizationMapPresentation_isRelativeGlobalCompleteIntersection`: the
  canonical presentation of `φ` is a relative global complete intersection.
* `MvPolynomial.isRelativeGlobalCompleteIntersection_universalFactorizationMap`: `φ` is a relative
  global complete intersection.

## References

* [Stacks Project, Tag 00SQ](https://stacks.math.columbia.edu/tag/00SQ)
-/

@[expose] public section

open scoped TensorProduct

open Polynomial

namespace MvPolynomial

variable (R : Type*) [CommRing R] (n m k : ℕ) (hn : n = m + k)

add_to_stacks 00SQ "the source's `S` generated over `R` by the `n + m` elements `b_i, c_j`, with the
`n + m` equations `a_k = a_k(b_i, c_j)`: a presentation with variables `Fin m ⊕ Fin k` and relations
`Fin n`, over any base ring, the total degree being `n = m + k`"
  MvPolynomial.universalFactorizationMapPresentation

add_to_stacks 00SQ "the source's last paragraph: `R → S` is a finite ring map, over any base ring,
the total degree being `n = m + k`"
  MvPolynomial.finite_universalFactorizationMap

/-- `K`-algebra maps from the fibre ring `K ⊗_{R[a]} S` of the universal factorization map
`φ : R[a] → S` to a `K`-algebra `L` correspond to factorizations over `L` of the image
`x^n + α_{n-1} x^{n-1} + ⋯ + α_0` of the free monic polynomial into monic polynomials of degrees
`m` and `k`. The factorization attached to `f` consists of the images under `f` of the two factors
of the free monic polynomial over `S`. -/
@[stacks 00SQ "the source's `k`-algebra maps `S_k → K` are tuples `β, γ` with
`x^{n+m} + α_1 x^{n+m-1} + … = (x^n + β_1 x^{n-1} + …)(x^m + γ_1 x^{m-1} + …)` in `K`; here for any
`K`-algebra `L` over any base ring, the tuples being the monic factors of degrees `m` and `k`, the
total degree being `n = m + k`"]
noncomputable def universalFactorizationMapBaseChangeAlgHomEquiv (K L : Type*) [CommRing K]
    [CommRing L] [Algebra (MvPolynomial (Fin n) R) K] [Algebra K L]
    [Algebra (MvPolynomial (Fin n) R) L] [IsScalarTower (MvPolynomial (Fin n) R) K L] :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    (K ⊗[MvPolynomial (Fin n) R] (MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R) →ₐ[K] L) ≃
      {q : MonicDegreeEq L m × MonicDegreeEq L k //
        q.1.1 * q.2.1 = (freeMonic R n).map (algebraMap (MvPolynomial (Fin n) R) L)} :=
  letI := (universalFactorizationMap R n m k hn).toAlgebra
  letI : Algebra R L := ((algebraMap (MvPolynomial (Fin n) R) L).comp (algebraMap R _)).toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin n) R) L := .of_algebraMap_eq' rfl
  (AlgHom.liftEquiv _ K _ L).symm.trans <|
    ({ toFun g := ⟨g.restrictScalars R, AlgHom.ext fun x ↦ g.commutes x⟩
       invFun f := { f.1 with commutes' := fun x ↦ congr($(f.2) x) }
       left_inv _ := rfl
       right_inv _ := rfl } :
      ((MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R) →ₐ[MvPolynomial (Fin n) R] L) ≃
        {f // AlgHom.comp f (universalFactorizationMap R n m k hn) =
          IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R) L}).trans <|
    (Equiv.subtypeEquivRight fun f ↦ by rw [Equiv.symm_apply_apply]).trans <|
    (universalFactorizationMapLiftEquiv R L n m k hn
      (mapEquivMonic R L n (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R) L))).trans <|
    Equiv.subtypeEquivRight fun _ ↦ Iff.rfl

/-- The first factor of the factorization attached to a `K`-algebra map `f : K ⊗_{R[a]} S → L` is
the image under `f` of the first factor `x^m + b_{m-1} x^{m-1} + ⋯ + b_0` of the free monic
polynomial over `S`. -/
theorem coe_fst_universalFactorizationMapBaseChangeAlgHomEquiv (K L : Type*) [CommRing K]
    [CommRing L] [Algebra (MvPolynomial (Fin n) R) K] [Algebra K L]
    [Algebra (MvPolynomial (Fin n) R) L] [IsScalarTower (MvPolynomial (Fin n) R) K L] :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    ∀ f : K ⊗[MvPolynomial (Fin n) R] (MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R) →ₐ[K] L,
      ((universalFactorizationMapBaseChangeAlgHomEquiv R n m k hn K L f).1.1 : L[X]) =
        ((freeMonic R m).map Algebra.TensorProduct.includeLeftRingHom).map
          (f.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) :=
  fun _ ↦ (Polynomial.map_map _ _ _).symm

/-- The second factor of the factorization attached to a `K`-algebra map `f : K ⊗_{R[a]} S → L` is
the image under `f` of the second factor `x^k + c_{k-1} x^{k-1} + ⋯ + c_0` of the free monic
polynomial over `S`. -/
theorem coe_snd_universalFactorizationMapBaseChangeAlgHomEquiv (K L : Type*) [CommRing K]
    [CommRing L] [Algebra (MvPolynomial (Fin n) R) K] [Algebra K L]
    [Algebra (MvPolynomial (Fin n) R) L] [IsScalarTower (MvPolynomial (Fin n) R) K L] :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    ∀ f : K ⊗[MvPolynomial (Fin n) R] (MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R) →ₐ[K] L,
      ((universalFactorizationMapBaseChangeAlgHomEquiv R n m k hn K L f).1.2 : L[X]) =
        ((freeMonic R k).map Algebra.TensorProduct.includeRight.toRingHom).map
          (f.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) :=
  fun _ ↦ (Polynomial.map_map _ _ _).symm

end MvPolynomial

namespace Polynomial

/-- Over a field `L`, a polynomial has only finitely many factorizations into monic polynomials of
given degrees `m` and `k`. -/
@[stacks 00SQ "the source's finiteness of the set of tuples `β, γ` in a field `K` with
`x^{n+m} + α_1 x^{n+m-1} + … = (x^n + β_1 x^{n-1} + …)(x^m + γ_1 x^{m-1} + …)`; here for any
polynomial over any field, with factor degrees `m` and `k`"]
theorem finite_monicDegreeEq_mul_eq (L : Type*) [Field L] (m k : ℕ) (p : L[X]) :
    Finite {q : MonicDegreeEq L m × MonicDegreeEq L k // q.1.1 * q.2.1 = p} := by
  by_cases hp : p.coeff (m + k) = 1 ∧ ∀ i > m + k, p.coeff i = 0
  · obtain ⟨f, hf⟩ := (MvPolynomial.mapEquivMonic L L (m + k)).surjective ⟨p, hp⟩
    let := (MvPolynomial.universalFactorizationMap L (m + k) m k rfl).toAlgebra
    have : Module.Finite (MvPolynomial (Fin (m + k)) L)
        (MvPolynomial (Fin m) L ⊗[L] MvPolynomial (Fin k) L) :=
      MvPolynomial.finite_universalFactorizationMap L (m + k) m k rfl
    let := f.toRingHom.toAlgebra
    have hp' : (freeMonic L (m + k)).map (algebraMap (MvPolynomial (Fin (m + k)) L) L) = p :=
      congrArg Subtype.val hf
    rw [← hp']
    exact .of_equiv _
      (MvPolynomial.universalFactorizationMapBaseChangeAlgHomEquiv L (m + k) m k rfl L L)
  · refine @Finite.of_subsingleton _ ⟨fun q _ ↦ (hp ?_).elim⟩
    rw [← q.2]
    exact (MonicDegreeEq.mk _ (q.1.1.monic.mul q.1.2.monic) (by
      rw [q.1.1.monic.natDegree_mul q.1.2.monic, MonicDegreeEq.natDegree,
        MonicDegreeEq.natDegree])).2

end Polynomial

namespace MvPolynomial

variable (R : Type*) [CommRing R] (n m k : ℕ) (hn : n = m + k)

/-- Every element of `S` is integral over `R[a]` under the universal factorization map. -/
@[stacks 00SQ "the source's last paragraph: each of `b_i, c_j` is integral over `R`; here every
element of `S`, over any base ring, the total degree being `n = m + k`"]
theorem isIntegral_universalFactorizationMap :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    Algebra.IsIntegral (MvPolynomial (Fin n) R)
      (MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R) := by
  let := (universalFactorizationMap R n m k hn).toAlgebra
  have : Module.Finite (MvPolynomial (Fin n) R)
      (MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R) :=
    finite_universalFactorizationMap R n m k hn
  infer_instance

/-- Every fibre `K ⊗_{R[a]} S` of the universal factorization map over a field `K` is Artinian. -/
private theorem isArtinianRing_tensorProduct_universalFactorizationMap (K : Type*) [Field K]
    [Algebra (MvPolynomial (Fin n) R) K] :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    IsArtinianRing
      (K ⊗[MvPolynomial (Fin n) R] (MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R)) := by
  let := (universalFactorizationMap R n m k hn).toAlgebra
  have : Module.Finite (MvPolynomial (Fin n) R)
      (MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R) :=
    finite_universalFactorizationMap R n m k hn
  exact .of_finite K _

/-- Every fibre `K ⊗_{R[a]} S` of the universal factorization map `R[a] → S` over a field `K` has
finitely many points. -/
@[stacks 00SQ "the source's statement that all fibres have finitely many closed points; here all
points, over any base ring, the total degree being `n = m + k`"]
theorem finite_primeSpectrum_tensorProduct_universalFactorizationMap (K : Type*) [Field K]
    [Algebra (MvPolynomial (Fin n) R) K] :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    Finite (PrimeSpectrum
      (K ⊗[MvPolynomial (Fin n) R] (MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R))) := by
  let := (universalFactorizationMap R n m k hn).toAlgebra
  have := isArtinianRing_tensorProduct_universalFactorizationMap R n m k hn K
  infer_instance

/-- Every nonempty fibre `K ⊗_{R[a]} S` of the universal factorization map `R[a] → S` over a field
`K` has dimension `0`. -/
@[stacks 00SQ "the source's statement that all fibres have dimension `0`, over any base ring, the
total degree being `n = m + k`; the fibre over a prime `p` is the case `K = κ(p)`"]
theorem ringKrullDim_tensorProduct_universalFactorizationMap (K : Type*) [Field K]
    [Algebra (MvPolynomial (Fin n) R) K] :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    Nontrivial
        (K ⊗[MvPolynomial (Fin n) R] (MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R)) →
      ringKrullDim
        (K ⊗[MvPolynomial (Fin n) R] (MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R)) = 0 := by
  let := (universalFactorizationMap R n m k hn).toAlgebra
  intro _
  have := isArtinianRing_tensorProduct_universalFactorizationMap R n m k hn K
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance

/-- The canonical presentation `S = R[a][b, c]/(a_l - a_l(b, c))` of the universal factorization
map, with `m + k` variables and `n = m + k` relations, is a relative global complete
intersection. -/
@[stacks 00SQ "the source's `S` is a relative global complete intersection over `R`, for the
presentation by the `b_i, c_j` and the equations `a_k = a_k(b_i, c_j)`, over any base ring, the
total degree being `n = m + k`"]
theorem universalFactorizationMapPresentation_isRelativeGlobalCompleteIntersection :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    Algebra.Presentation.IsRelativeGlobalCompleteIntersection
      (universalFactorizationMapPresentation R n m k hn).toPresentation := by
  let := (universalFactorizationMap R n m k hn).toAlgebra
  refine ⟨fun p _ hp ↦ ?_⟩
  rw [ringKrullDim_tensorProduct_universalFactorizationMap R n m k hn p.ResidueField hp]
  simp [hn]

/-- The universal factorization map `R[a_0, …, a_{n-1}] → R[b] ⊗_R R[c]` is a relative global
complete intersection. -/
@[stacks 00SQ "the source's `R → S` is a relative global complete intersection, as a property of
the ring map, over any base ring, the total degree being `n = m + k`"]
theorem isRelativeGlobalCompleteIntersection_universalFactorizationMap :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    Algebra.IsRelativeGlobalCompleteIntersection (MvPolynomial (Fin n) R)
      (MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R) := by
  let := (universalFactorizationMap R n m k hn).toAlgebra
  have := universalFactorizationMapPresentation_isRelativeGlobalCompleteIntersection R n m k hn
  refine ⟨m + k, n, (universalFactorizationMapPresentation R n m k hn).toPresentation.reindex
    finSumFinEquiv.symm (.refl _), ⟨fun p _ hp ↦ ?_⟩⟩
  simpa [hn] using this.ringKrullDim_fiber_add_card_eq_card p hp

end MvPolynomial

end
