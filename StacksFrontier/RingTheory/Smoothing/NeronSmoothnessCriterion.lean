module

public import Mathlib.RingTheory.Kaehler.TensorProduct
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Kaehler.BaseChange
public import StacksFrontier.RingTheory.Kaehler.Basic
public import StacksFrontier.RingTheory.Kaehler.Defs
public import StacksFrontier.RingTheory.RelativeDimension.Basic
public import StacksFrontier.RingTheory.RelativeDimension.Semicontinuity
public import StacksFrontier.RingTheory.Smooth.LocusBaseChange
public import StacksFrontier.RingTheory.Smooth.RegularLocalRing
public import StacksFrontier.RingTheory.Smooth.SmoothAt
public import StacksFrontier.RingTheory.Smoothing.NeronLocalParameters

/-!
# Smoothness of a Néron chart detected by the conormal sequence

Fix an extension `R → Λ` of discrete valuation rings of ramification index one together with a
factorization `R → A → Λ` in which `A` is flat and of finite type over `R`, and write
`𝔮 = Ker(A → Λ)` and `𝔭 = (A → Λ)^{-1}(𝔪_Λ)`. Suppose `A` is presented as a quotient of an
`R`-algebra `B` which is smooth at the preimage of `𝔭`, and suppose `A` is already smooth over
`R` at the generic point `𝔮`. If the cokernel of the conormal map

`I/I² ⊗_A Λ → Ω_{B/R} ⊗_B Λ`

is a free `Λ`-module, then `A` is smooth over `R` at `𝔭` as well.

The proof compares relative dimensions. Freeness of the cokernel identifies the rank of
`Ω_{A/R} ⊗_A Λ` with the relative dimension `d` at the generic point `𝔮`; semicontinuity of the
relative dimension bounds the relative dimension at `𝔭` below by `d`; and the fibre of `A` over
the closed point of `R` is then smooth at `𝔭` by the dimension criterion.

## Main results

* `Stacks.Smoothing.NeronSituation.isPrime_kernelIdeal`: the ideal `𝔮` is prime.
* `Stacks.Smoothing.smoothAt_of_conormal_cokernel_free`: freeness of the scalar-extended
  conormal cokernel propagates smoothness from `𝔮` to `𝔭`.

## Implementation notes

The cokernel is the quotient of `Λ ⊗_A (A ⊗_B Ω_{B/R})` by the range of the scalar extension of
`ConormalSeq.conormalMap`; the conormal map's source is the `B`-module `I/I²` provided by
`ConormalSeq.cotangentModule`.

Smoothness at a prime is `Algebra.SmoothAt`, the local notion of Definition 00TB: there is an
element outside the prime whose principal localization is smooth.

Smoothness of `B` over `R` at the preimage of `𝔭` is part of the hypotheses, but the dimension
argument below does not need it: freeness of the cokernel already pins the rank of
`Ω_{A/R} ⊗_A Λ`. The hypothesis is retained so that the statement is the one of the source.

## References

* [Stacks Project, Tag 0BJ5](https://stacks.math.columbia.edu/tag/0BJ5)
-/

@[expose] public section

namespace Stacks.Smoothing

open scoped TensorProduct
open TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The kernel ideal `𝔮 = Ker(A → Λ)` is prime, since `Λ` is a domain. -/
instance NeronSituation.isPrime_kernelIdeal (S : NeronSituation) : S.kernelIdeal.IsPrime :=
  RingHom.ker_isPrime (algebraMap S.A S.Λ)

/-- The conormal sequence of a surjection `B → A`, extended to `Λ`, identifies the cokernel of
the conormal map with the base change of `Ω_{A/R}`. -/
private noncomputable def conormalCokernelEquivDifferentials
    (R A Λ B : Type*) [CommRing R] [CommRing A] [CommRing Λ] [CommRing B]
    [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A]
    [Algebra A Λ] (hsurj : Function.Surjective (algebraMap B A)) :
    let _ := ConormalSeq.cotangentModule hsurj
    ((Λ ⊗[A] (A ⊗[B] Ω[B⁄R])) ⧸
      LinearMap.range (LinearMap.baseChange Λ (ConormalSeq.conormalMap R hsurj))) ≃ₗ[Λ]
      (Λ ⊗[A] Ω[A⁄R]) := by
  let _ := ConormalSeq.cotangentModule hsurj
  let f := ConormalSeq.conormalMap R hsurj
  let g := KaehlerDifferential.mapBaseChange R B A
  have hs := ConormalSeq.conormal_exact_sequence R B A hsurj
  have hbc : Function.Exact (LinearMap.baseChange Λ f) (LinearMap.baseChange Λ g) := by
    rw [LinearMap.baseChange_eq_lTensor, LinearMap.baseChange_eq_lTensor]
    exact lTensor_exact Λ (LinearMap.exact_iff.mpr hs.1.symm) hs.2
  exact (Submodule.quotEquivOfEq _ _ hbc.linearMap_ker_eq.symm).trans
    ((LinearMap.baseChange Λ g).quotKerEquivOfSurjective (LinearMap.baseChange_surjective Λ hs.2))

private lemma maximalIdealPreimage_under (S : NeronSituation) :
    S.maximalIdealPreimage.under S.R = IsLocalRing.maximalIdeal S.R := by
  have _ : IsLocalHom (algebraMap S.R S.Λ) := S.extension.2
  change ((IsLocalRing.maximalIdeal S.Λ).comap (algebraMap S.A S.Λ)).comap
      (algebraMap S.R S.A) = _
  rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq S.R S.A S.Λ]
  exact IsLocalRing.maximalIdeal_comap (algebraMap S.R S.Λ)

private lemma kernelIdeal_under (S : NeronSituation) : S.kernelIdeal.under S.R = ⊥ := by
  change (RingHom.ker (algebraMap S.A S.Λ)).comap (algebraMap S.R S.A) = ⊥
  rw [RingHom.comap_ker, ← IsScalarTower.algebraMap_eq S.R S.A S.Λ]
  exact (RingHom.injective_iff_ker_eq_bot _).mp S.extension.1

private lemma kernelIdeal_le_maximalIdealPreimage (S : NeronSituation) :
    S.kernelIdeal ≤ S.maximalIdealPreimage := fun a ha => by
  change algebraMap S.A S.Λ a ∈ IsLocalRing.maximalIdeal S.Λ
  change algebraMap S.A S.Λ a = 0 at ha
  simp [ha]

/-- Relative differentials of a base change have the same rank over a residue field as the
differentials they come from. -/
private lemma finrank_baseChanged_differentials_eq (R A k S F : Type*)
    [CommRing R] [CommRing A] [Algebra R A] [CommRing k] [CommRing S] [Algebra R k]
    [Algebra A S] [Algebra k S] [Algebra R S] [IsScalarTower R A S]
    [IsScalarTower R k S] [Algebra.IsPushout R k A S] [Field F]
    [Algebra S F] [Algebra A F] [IsScalarTower A S F] :
    Module.finrank F (F ⊗[S] Ω[S⁄k]) = Module.finrank F (F ⊗[A] Ω[A⁄R]) := by
  let e : F ⊗[S] Ω[S⁄k] ≃ₗ[F] F ⊗[A] Ω[A⁄R] :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl F F)
      (KaehlerDifferential.tensorKaehlerEquiv R k A S).symm).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A S F F Ω[A⁄R])
  exact e.finrank_eq

/-- A free base change to an intermediate ring has the same rank as a base change to any residue
field inside a common field extension. -/
private lemma finrank_free_scalar_extension_eq (A Λ L κ M : Type*) [CommRing A]
    [CommRing Λ] [Field L] [Field κ] [AddCommGroup M] [Module A M]
    [Algebra A Λ] [Algebra A κ] [Algebra A L] [Algebra Λ L] [Algebra κ L]
    [IsScalarTower A Λ L] [IsScalarTower A κ L]
    [StrongRankCondition Λ]
    [Module.Free Λ (Λ ⊗[A] M)] :
    Module.finrank Λ (Λ ⊗[A] M) = Module.finrank κ (κ ⊗[A] M) := by
  calc
    Module.finrank Λ (Λ ⊗[A] M) = Module.finrank L (L ⊗[Λ] (Λ ⊗[A] M)) :=
      (Module.finrank_baseChange (R := L) (S := Λ) (M' := Λ ⊗[A] M)).symm
    _ = Module.finrank L (L ⊗[A] M) :=
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A Λ L L M).finrank_eq
    _ = Module.finrank L (L ⊗[κ] (κ ⊗[A] M)) :=
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A κ L L M).finrank_eq.symm
    _ = Module.finrank κ (κ ⊗[A] M) := Module.finrank_baseChange

/-- Base changing to the residue fields of primes `P` of `B` over `p` of `A` gives equal ranks. -/
private lemma finrank_residueField_eq_of_comap_eq {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (M : Type*) [AddCommGroup M] [Module A M] (p : Ideal A) [p.IsPrime]
    (P : Ideal B) [P.IsPrime] (hP : P.comap (algebraMap A B) = p) :
    Module.finrank p.ResidueField (p.ResidueField ⊗[A] M) =
      Module.finrank P.ResidueField (P.ResidueField ⊗[A] M) := by
  let f := Ideal.ResidueField.mapₐ p P (Algebra.ofId A B) hP.symm
  let _ : Algebra p.ResidueField P.ResidueField := f.toRingHom.toAlgebra
  have _ : IsScalarTower A p.ResidueField P.ResidueField :=
    .of_algebraMap_eq fun a => (f.commutes a).symm
  exact finrank_free_scalar_extension_eq A p.ResidueField P.ResidueField P.ResidueField M

private lemma exists_nat_le_of_lt_nat {x : WithBot ℕ∞} {d : ℕ}
    (h0 : 0 ≤ x) (h : x < (d : WithBot ℕ∞)) :
    ∃ n < d, x ≤ (n : WithBot ℕ∞) := by
  cases x with
  | bot => simp at h0
  | coe x =>
      cases x with
      | top => simp at h
      | coe n => exact ⟨n, by exact_mod_cast h, le_rfl⟩

private alias zero_le_withBotENat_of_ne_bot :=
  Stacks.RelativeDimension.Semicontinuity.zero_le_of_ne_bot

/-- The relative dimension at a prime is not `⊥` once the fibre has a prime over it. -/
private theorem zero_le_relativeDimensionAt {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (q : Ideal A) [q.IsPrime] (p : Ideal R) [p.IsPrime] (hp : q.under R = p)
    (Q : Ideal (p.Fiber A)) [Q.IsPrime]
    (hQ : Q.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] p.Fiber A) = q) :
    0 ≤ Algebra.relativeDimensionAt R q := by
  rw [Algebra.relativeDimensionAt_eq_localKrullDim q p hp Q hQ, TopologicalSpace.localKrullDim]
  refine le_iInf fun U ↦ le_iInf fun _ ↦ le_iInf fun hQU ↦ zero_le_withBotENat_of_ne_bot ?_
  rw [Ne, topologicalKrullDim_eq_bot_iff_isEmpty]
  exact fun hempty ↦ hempty.false ⟨⟨Q, ‹_›⟩, hQU⟩

/-- Upper semicontinuity of the relative dimension: it can only grow along a specialization
`q ≤ p` of primes of a finite type algebra. -/
private theorem relativeDimensionAt_le_of_le {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] {q p : Ideal A} [q.IsPrime] [p.IsPrime] (hqp : q ≤ p)
    (h0 : 0 ≤ Algebra.relativeDimensionAt R p) {d : ℕ}
    (hq : Algebra.relativeDimensionAt R q = (d : WithBot ℕ∞)) :
    (d : WithBot ℕ∞) ≤ Algebra.relativeDimensionAt R p := by
  by_contra hnot
  obtain ⟨n, hnd, hpn⟩ := exists_nat_le_of_lt_nat h0 (lt_of_not_ge hnot)
  let U := {x : PrimeSpectrum A | Algebra.relativeDimensionAt R x.asIdeal ≤ (n : WithBot ℕ∞)}
  have hU : IsOpen U := by
    simpa [U] using Algebra.isOpen_setOf_relativeDimensionAt_le (R := R) (S := A) n
  have hqpSpec : (⟨q, inferInstance⟩ : PrimeSpectrum A) ≤ ⟨p, inferInstance⟩ := hqp
  have hqn : Algebra.relativeDimensionAt R q ≤ (n : WithBot ℕ∞) :=
    (specializes_iff_forall_open.mp (specializes_iff_mem_closure.mpr
      ((PrimeSpectrum.le_iff_mem_closure _ _).mp hqpSpec))) U hU hpn
  rw [hq] at hqn
  exact Nat.not_le_of_gt hnd (by exact_mod_cast hqn)

/-- At a prime of the generic fibre at which `A` is smooth over `R`, the relative dimension is the
rank of `Ω_{A/R}` at a prime of the generic fibre ring lying over it. -/
private theorem relativeDimensionAt_eq_finrank_of_isSmoothAt {R A : Type*} [CommRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A]
    [Module.Flat R (⊥ : Ideal R).ResidueField] (q : Ideal A) [q.IsPrime] (hq0 : q.under R = ⊥)
    (hA : Algebra.IsSmoothAt R q) (Q : Ideal ((⊥ : Ideal R).Fiber A)) [Q.IsPrime]
    (hQ : Q.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] (⊥ : Ideal R).Fiber A) = q) :
    Algebra.relativeDimensionAt R q =
      (Module.finrank Q.ResidueField (Q.ResidueField ⊗[A] Ω[A⁄R]) : WithBot ℕ∞) := by
  let k := (⊥ : Ideal R).ResidueField
  let T := (⊥ : Ideal R).Fiber A
  have _ : Algebra.IsPushout R A k T :=
    Algebra.IsPushout.symm (show Algebra.IsPushout R k A T from inferInstance)
  have hftT : Algebra.FiniteType k T := Algebra.FiniteType.baseChange k
  have hQsmooth : Algebra.IsSmoothAt k Q := by
    change (⟨Q, ‹_›⟩ : PrimeSpectrum T) ∈ Algebra.smoothLocus k T
    rw [← Algebra.smoothLocus_comap_of_isPushout R A k T]
    change PrimeSpectrum.comap (algebraMap A T) ⟨Q, ‹_›⟩ ∈ Algebra.smoothLocus R A
    rw [show PrimeSpectrum.comap (algebraMap A T) ⟨Q, ‹_›⟩ = ⟨q, inferInstance⟩ from
      PrimeSpectrum.ext hQ]
    exact hA
  have hdimQ' := (Algebra.isSmoothAt_tfae_localKrullDim_and_isRegularLocalRing
    (k := k) (S := T) ⟨Q, ‹_›⟩ (Localization.AtPrime Q)).1.out 1 3 |>.mp hQsmooth
  rw [Algebra.relativeDimensionAt_eq_localKrullDim q ⊥ hq0 Q hQ, ← hdimQ']
  change (Module.finrank Q.ResidueField (Q.ResidueField ⊗[T] Ω[T⁄k]) : WithBot ℕ∞) = _
  exact_mod_cast finrank_baseChanged_differentials_eq R A k T Q.ResidueField

/-- A free base change `Λ ⊗_A M` has the rank of the base change of `M` to the residue field of
any prime of the generic fibre ring over `𝔮 = Ker(A → Λ)`. -/
private theorem finrank_free_eq_finrank_residueField_of_comap_eq_kernelIdeal (S : NeronSituation)
    (M : Type*) [AddCommGroup M] [Module S.A M] [Module.Free S.Λ (S.Λ ⊗[S.A] M)]
    (Q : Ideal ((⊥ : Ideal S.R).Fiber S.A)) [Q.IsPrime]
    (hQ : Q.comap (Algebra.TensorProduct.includeRight : S.A →ₐ[S.R] (⊥ : Ideal S.R).Fiber S.A) =
      S.kernelIdeal) :
    Module.finrank S.Λ (S.Λ ⊗[S.A] M) =
      Module.finrank Q.ResidueField (Q.ResidueField ⊗[S.A] M) := by
  let q := S.kernelIdeal
  let T := (⊥ : Ideal S.R).Fiber S.A
  let F := Q.ResidueField
  let L := FractionRing S.Λ
  let fA : S.A →ₐ[S.R] L := IsScalarTower.toAlgHom S.R S.A L
  have hkerA : RingHom.ker fA.toRingHom = q := by
    ext a
    change (algebraMap S.Λ L (algebraMap S.A S.Λ a) = 0) ↔ (algebraMap S.A S.Λ a = 0)
    exact map_eq_zero_iff _ (IsFractionRing.injective S.Λ L)
  have hunitA : q.primeCompl ≤ (IsUnit.submonoid L).comap fA.toRingHom := fun a ha =>
    isUnit_iff_ne_zero.mpr fun hzero => ha (by rw [← hkerA]; exact RingHom.mem_ker.mpr hzero)
  let fResid := Ideal.ResidueField.liftₐ q fA hkerA.ge hunitA
  let _ : Algebra q.ResidueField L := fResid.toRingHom.toAlgebra
  have _ : IsScalarTower S.A q.ResidueField L :=
    IsScalarTower.of_algebraMap_eq (R := S.A) (S := q.ResidueField) (A := L) fun a =>
      (Ideal.ResidueField.liftₐ_algebraMap q fA hkerA.ge hunitA a).symm
  exact (finrank_free_scalar_extension_eq S.A S.Λ L q.ResidueField M).trans
    (finrank_residueField_eq_of_comap_eq M q Q hQ)

/-- If `Ω_{A/R} ⊗_A Λ` is free, its rank is the rank of the differentials of the closed fibre at
any prime of the closed fibre ring over `𝔭 = (A → Λ)^{-1}(𝔪_Λ)`. -/
private theorem finrank_fiber_differentials_eq_finrank_free (S : NeronSituation)
    [Module.Free S.Λ (S.Λ ⊗[S.A] Ω[S.A⁄S.R])]
    (Qp : Ideal ((IsLocalRing.maximalIdeal S.R).Fiber S.A)) [Qp.IsPrime]
    (hQp : Qp.comap (Algebra.TensorProduct.includeRight :
      S.A →ₐ[S.R] (IsLocalRing.maximalIdeal S.R).Fiber S.A) = S.maximalIdealPreimage) :
    Module.finrank Qp.ResidueField (Qp.ResidueField ⊗[(IsLocalRing.maximalIdeal S.R).Fiber S.A]
      Ω[(IsLocalRing.maximalIdeal S.R).Fiber S.A⁄(IsLocalRing.maximalIdeal S.R).ResidueField]) =
      Module.finrank S.Λ (S.Λ ⊗[S.A] Ω[S.A⁄S.R]) := by
  let p := S.maximalIdealPreimage
  let r := IsLocalRing.maximalIdeal S.R
  let kΛ := (IsLocalRing.maximalIdeal S.Λ).ResidueField
  have _ : IsLocalHom (algebraMap S.R S.Λ) := S.extension.2
  exact (finrank_baseChanged_differentials_eq S.R S.A r.ResidueField (r.Fiber S.A)
    Qp.ResidueField).trans
    ((finrank_residueField_eq_of_comap_eq Ω[S.A⁄S.R] p Qp hQp).symm.trans
      ((finrank_residueField_eq_of_comap_eq Ω[S.A⁄S.R] p (IsLocalRing.maximalIdeal S.Λ) rfl).trans
        (finrank_free_scalar_extension_eq S.A S.Λ kΛ kΛ Ω[S.A⁄S.R]).symm))

/-- **Stacks 0BJ5.** In a Néron situation, suppose `A` is smooth over `R` at the generic point
`𝔮 = Ker(A → Λ)`, suppose `A` is a quotient of an `R`-algebra `B` which is smooth over `R` at the
preimage of `𝔭`, and suppose the cokernel of the conormal map `I/I² ⊗_A Λ → Ω_{B/R} ⊗_B Λ` is a
free `Λ`-module. Then `A` is smooth over `R` at `𝔭` too. -/
@[stacks 0BJ5]
theorem smoothAt_of_conormal_cokernel_free
    (S : NeronSituation)
    (B : Type*) [CommRing B] [Algebra S.R B] [Algebra B S.A]
    [IsScalarTower S.R B S.A]
    (hsurj : Function.Surjective (algebraMap B S.A))
    (hA : Algebra.SmoothAt S.R S.A S.kernelIdeal)
    (_hB : Algebra.SmoothAt S.R B (Ideal.comap (algebraMap B S.A) S.maximalIdealPreimage))
    (hfree : let _ := ConormalSeq.cotangentModule hsurj
      Module.Free S.Λ
        ((S.Λ ⊗[S.A] (S.A ⊗[B] Ω[B⁄S.R])) ⧸
          LinearMap.range
            (LinearMap.baseChange S.Λ (ConormalSeq.conormalMap S.R hsurj)))) :
    Algebra.SmoothAt S.R S.A S.maximalIdealPreimage := by
  let _ := ConormalSeq.cotangentModule hsurj
  let q := S.kernelIdeal
  let p := S.maximalIdealPreimage
  let r := IsLocalRing.maximalIdeal S.R
  have _ : IsPrincipalIdealRing S.R := IsDiscreteValuationRing.toIsPrincipalIdealRing
  have _ : Algebra.FinitePresentation S.R S.A :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hq0 : q.under S.R = ⊥ := kernelIdeal_under S
  have hpr : p.under S.R = r := maximalIdealPreimage_under S
  obtain ⟨Q, hQprime, hQcomap⟩ := Ideal.Fiber.exists_comap_includeRight_eq q ⊥ hq0
  obtain ⟨Qp, hQpPrime, hQpComap⟩ := Ideal.Fiber.exists_comap_includeRight_eq p r hpr
  have _ : Module.Free S.Λ
      ((S.Λ ⊗[S.A] (S.A ⊗[B] Ω[B⁄S.R])) ⧸
        LinearMap.range (LinearMap.baseChange S.Λ (ConormalSeq.conormalMap S.R hsurj))) := hfree
  have hfreeΩ : Module.Free S.Λ (S.Λ ⊗[S.A] Ω[S.A⁄S.R]) :=
    Module.Free.of_equiv (conormalCokernelEquivDifferentials S.R S.A S.Λ B hsurj)
  have hrelq : Algebra.relativeDimensionAt S.R q =
      (Module.finrank S.Λ (S.Λ ⊗[S.A] Ω[S.A⁄S.R]) : WithBot ℕ∞) := by
    rw [relativeDimensionAt_eq_finrank_of_isSmoothAt q hq0
      (Algebra.isSmoothAt_of_smoothAt S.R S.A hA) Q hQcomap,
      finrank_free_eq_finrank_residueField_of_comap_eq_kernelIdeal S _ Q hQcomap]
  have hrelp := relativeDimensionAt_le_of_le (kernelIdeal_le_maximalIdealPreimage S)
    (zero_le_relativeDimensionAt p r hpr Qp hQpComap) hrelq
  have hfiberSmooth : Algebra.IsSmoothAt r.ResidueField Qp :=
    (Algebra.isSmoothAt_tfae_localKrullDim_and_isRegularLocalRing (k := r.ResidueField)
      (S := r.Fiber S.A) ⟨Qp, hQpPrime⟩ (Localization.AtPrime Qp)).1.out 1 2 |>.mpr (by
        rwa [finrank_fiber_differentials_eq_finrank_free S Qp hQpComap,
          ← Algebra.relativeDimensionAt_eq_localKrullDim p r hpr Qp hQpComap])
  have hfpAway : ∃ g ∉ p, Algebra.FinitePresentation S.R (Localization.Away g) := by
    refine ⟨1, fun h =>
      S.isPrime_maximalIdealPreimage.ne_top (Ideal.eq_top_of_isUnit_mem p h isUnit_one), ?_⟩
    have _ : Algebra.FinitePresentation S.A (Localization.Away (1 : S.A)) :=
      IsLocalization.Away.finitePresentation (1 : S.A)
    exact Algebra.FinitePresentation.trans S.R S.A (Localization.Away (1 : S.A))
  exact Algebra.exists_notMem_smooth_of_isSmoothAt_fiber (p := r) (Q := Qp) (q := p)
    hQpComap hfpAway

end Stacks.Smoothing

end
