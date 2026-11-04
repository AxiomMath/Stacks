module

public import Mathlib.RingTheory.Unramified.LocalStructure
public import StacksFrontier.RingTheory.GeometricallyNormal.TFAE

import StacksCore.Tactic.StacksAttribute

/-!
# A smooth algebra over a normal ring is normal

Proof of `Algebra.isNormalRing_of_smooth` (Stacks 033C): if `R → S` is a smooth ring map and `R`
is a normal ring, then `S` is a normal ring.

Normality is local on `S`, and locally on `S` a smooth algebra is standard étale over a polynomial
ring: every prime `q` of `S` has an `f ∉ q` with `S_f` standard étale over `R[x₁, …, xₙ]`
(`Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial`). The polynomial ring is normal
(Lemma 00H1, `isNormalRing_mvPolynomial`), an étale algebra over a normal ring is normal
(`IsNormalRing.of_etale`), and `S_q` is a localization of `S_f`.

## Main results

* `IsNormalRing.of_forall_exists_away`: normality of `S` is detected on basic opens around each
  prime.
* `Algebra.isNormalRing_of_smooth`: a smooth algebra over a normal ring is normal.

## Implementation notes

The ring map is an `Algebra R S` instance and its smoothness is `Algebra.Smooth R S`, as for the
reduced analogue `Algebra.isReduced_of_smooth` (Stacks 033B). Normality is the library's
`IsNormalRing` (Definition 00GV): every localization at a prime is an integrally closed domain, so
a normal ring need not be a domain.

## References

* [Stacks Project, Tag 033C](https://stacks.math.columbia.edu/tag/033C)
-/

@[expose] public section

/-- Normality is local on the spectrum: if every prime `q` of `S` has an `f ∉ q` with `S_f`
normal, then `S` is normal, the localization `S_q` being a localization of `S_f`. -/
theorem IsNormalRing.of_forall_exists_away {S : Type*} [CommRing S]
    (H : ∀ (q : Ideal S) [q.IsPrime], ∃ f ∉ q, IsNormalRing (Localization.Away f)) :
    IsNormalRing S := by
  intro q hq
  obtain ⟨f, hf, hT⟩ := H q
  have hle : Submonoid.powers f ≤ q.primeCompl := Submonoid.powers_le.mpr hf
  let _ : Algebra (Localization.Away f) (Localization.AtPrime q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _ q.primeCompl hle
  have : IsScalarTower S (Localization.Away f) (Localization.AtPrime q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ q.primeCompl hle
  have : IsLocalization (q.primeCompl.map (algebraMap S (Localization.Away f)))
      (Localization.AtPrime q) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ _ q.primeCompl hle
  exact (hT.isLocalization (q.primeCompl.map (algebraMap S (Localization.Away f)))
    (Localization.AtPrime q)).of_isLocalRing

/-- **Stacks 033C.** A smooth algebra over a normal ring is a normal ring. -/
@[stacks 033C, sga "1 II 3.1" "normal, O_y ⇒ O_x"]
theorem Algebra.isNormalRing_of_smooth (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] (hR : IsNormalRing R) : IsNormalRing S := by
  refine IsNormalRing.of_forall_exists_away fun q _ ↦ ?_
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R)
    (p := q)
  exact ⟨f, hf, IsNormalRing.of_etale (R := MvPolynomial (Fin n) R)
    (isNormalRing_mvPolynomial (Fin n) hR)⟩

open scoped TensorProduct in
/-- The base change of a normal ring `N` to a localization of a smooth `A`-algebra is normal:
`N ⊗[A] C` is smooth over `N`, hence normal by `Algebra.isNormalRing_of_smooth`, and `N ⊗[A] B` is
a localization of it. -/
theorem Algebra.isNormalRing_tensorProduct_of_smooth_of_isLocalization (A N C B : Type*)
    [CommRing A] [CommRing N] [CommRing C] [CommRing B] [Algebra A N] [Algebra A C] [Algebra A B]
    [Algebra C B] [IsScalarTower A C B] [Algebra.Smooth A C] (hN : IsNormalRing N)
    (S : Submonoid C) [IsLocalization S B] : IsNormalRing (N ⊗[A] B) := by
  have : Algebra.Smooth N (N ⊗[A] C) := Algebra.Smooth.baseChange A C N
  have hNC : IsNormalRing (N ⊗[A] C) := Algebra.isNormalRing_of_smooth N (N ⊗[A] C) hN
  let F : (N ⊗[A] C) →ₐ[A] (N ⊗[A] B) :=
    Algebra.TensorProduct.map (AlgHom.id A N) (IsScalarTower.toAlgHom A C B)
  let _ : Algebra (N ⊗[A] C) (N ⊗[A] B) := F.toRingHom.toAlgebra
  have : IsScalarTower N (N ⊗[A] C) (N ⊗[A] B) :=
    IsScalarTower.of_algebraMap_eq fun n ↦ by simp [RingHom.algebraMap_toAlgebra, F]
  have : IsLocalization (S.map (Algebra.TensorProduct.includeRight (R := A) (A := N)))
      (N ⊗[A] B) :=
    IsLocalization.tensorProduct_tensorProduct_right A N S B
      (by ext c; simp [RingHom.algebraMap_toAlgebra, F])
  exact hNC.isLocalization (S.map (Algebra.TensorProduct.includeRight (R := A) (A := N)))
    (N ⊗[A] B)
