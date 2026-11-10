module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ConnectednessApplication
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsAssociatedPointInduction
import all StacksFrontier.AlgebraicGeometry.FormalGeometry.ConnectednessApplication

/-!
# The formal locus is connected: Stacks 0EG5

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let `U = Spec(A) ∖ V(𝔞)` and let
`T = V(I) ∖ V(𝔞)`. Stacks 0EG5 says that `T` is empty or connected as soon as `A` is `I`-adically
complete with a dualizing complex, `dim((A/𝔭)_𝔮) > cd(A, I) + 1` for every minimal prime `𝔭`
not in `V(I)` and every `𝔮 ∈ V(𝔭) ∩ V(𝔞)`, and every nonempty open of `Spec(A)` containing `T`
is connected. This file proves it.

## Main results

* `Stacks.Algebraization.eq_empty_or_isConnected_zeroLocus_sdiff_of_isDualizingComplex` —
  **Stacks 0EG5**.

## The proof

The source replaces `A` by its reduction and applies Stacks 0EG2
(`Stacks.Algebraization.isIso_comparisonMap_of_associatedPointsClosureDimensionBound`) to the
structure sheaf of `U`. On a reduced ring the associated points of that structure sheaf are
minimal primes, so the dimension hypothesis at the minimal primes is condition (2) of Stacks
0EG2. The comparison map being an isomorphism, a disconnection of `T` gives a nontrivial
idempotent among the formal sections of `𝒪_U` along `T`, hence a nonconstant idempotent function
on a neighbourhood of `T`, hence a disconnection of a neighbourhood of `T`.

The idempotent argument, the transport of the hypotheses to the reduction and the identification
of the associated points are the lemmas of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/ConnectednessApplication.lean`, used here as they
stand.

## References

* [Stacks Project, Tag 0EG5](https://stacks.math.columbia.edu/tag/0EG5)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance 2000] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.Ample (unitModule)

open Stacks.LocalCohomology

/-- **Stacks 0EG2 for the structure sheaf of a reduced ring.** For a reduced Noetherian ring the
dimension hypothesis of Stacks 0EG5 at the minimal primes is condition (2) of Stacks 0EG2 for the
structure sheaf of `U = Spec(A) ∖ V(𝔞)`, whose associated points are minimal primes, so its
comparison map is an isomorphism. -/
private lemma isIso_comparisonMap_unitModule_of_isReduced (A : Type u) [CommRing A]
    [IsNoetherianRing A] [_root_.IsReduced A] (I a : Ideal A) (hIa : I ≤ a) [IsAdicComplete I A]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : Dualizing.IsDualizingComplex K)
    (hdim : ∀ p q : PrimeSpectrum A, p.asIdeal ∈ minimalPrimes A → ¬ I ≤ p.asIdeal →
      p.asIdeal ≤ q.asIdeal → a ≤ q.asIdeal →
      ((cohomologicalDimension A I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
        krullDimToEInt (closureLocalDimension A p q)) :
    IsIso (comparisonMap A I a (unitModule (complementZeroLocus A a : Scheme))) :=
  isIso_comparisonMap_of_associatedPointsClosureDimensionBound I a hIa inferInstance ⟨K, hK⟩ _
    fun x hx hxI _ z hxz haz =>
      hdim x.1 z (mem_minimalPrimes_of_mem_associatedPoints_unitModule A a x hx) hxI hxz haz

/-- **Stacks Project, Tag 0EG5.** Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`. Assume

1. `A` is `I`-adically complete and has a dualizing complex,
2. if `𝔭` is a minimal prime of `A` not contained in `V(I)` and `𝔮 ∈ V(𝔭) ∩ V(𝔞)`, then
   `dim((A/𝔭)_𝔮) > cd(A, I) + 1`, and
3. every nonempty open `V ⊆ Spec(A)` containing `V(I) ∖ V(𝔞)` is connected.

Then `V(I) ∖ V(𝔞)` is either empty or connected.

The proof replaces `A` by its reduction, where the inequality in (2) holds at every associated
point of the structure sheaf of `U = Spec(A) ∖ V(𝔞)`, and applies Stacks 0EG2 to that structure
sheaf. A disconnection of `V(I) ∖ V(𝔞)` is turned into a compatible family of sections of
`𝒪_U / Iⁿ 𝒪_U` which is `1` on one piece and `0` on the other, the nontrivial idempotent of the
source; Stacks 0EG2 realizes it as a function on an open neighbourhood `V` of `V(I) ∖ V(𝔞)`
whose germs along that locus take the two values `1` and `0`, and the two opens where they are
attained disconnect a neighbourhood of `V(I) ∖ V(𝔞)`, contradicting (3). -/
@[stacks 0EG5]
public theorem eq_empty_or_isConnected_zeroLocus_sdiff_of_isDualizingComplex (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I a : Ideal A) (hIa : I ≤ a) [IsAdicComplete I A]
    (hdualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K)
    (hdim : ∀ p q : PrimeSpectrum A, p.asIdeal ∈ minimalPrimes A → ¬ I ≤ p.asIdeal →
      p.asIdeal ≤ q.asIdeal → a ≤ q.asIdeal →
      ((cohomologicalDimension A I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
        krullDimToEInt (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
          p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))))
    (hconn : ∀ V : Set (PrimeSpectrum A), IsOpen V → V.Nonempty →
      PrimeSpectrum.zeroLocus (I : Set A) \ PrimeSpectrum.zeroLocus (a : Set A) ⊆ V →
      _root_.IsConnected V) :
    PrimeSpectrum.zeroLocus (I : Set A) \ PrimeSpectrum.zeroLocus (a : Set A) = ∅ ∨
      _root_.IsConnected
        (PrimeSpectrum.zeroLocus (I : Set A) \ PrimeSpectrum.zeroLocus (a : Set A)) := by
  classical
  obtain ⟨K, hK⟩ := hdualizing
  let B := A ⧸ nilradical A
  let φ : A →+* B := Ideal.Quotient.mk (nilradical A)
  have hφ : (algebraMap A B) = φ := rfl
  have hbij := PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical
    (show nilradical A ≤ nilradical A from le_rfl)
  let H : PrimeSpectrum B ≃ₜ PrimeSpectrum A :=
    (PrimeSpectrum.isClosedEmbedding_comap_of_surjective B φ
      Ideal.Quotient.mk_surjective).isEmbedding.toHomeomorphOfSurjective hbij.surjective
  let e : PrimeSpectrum B ≃o PrimeSpectrum A :=
    { toEquiv := Equiv.ofBijective (PrimeSpectrum.comap φ) hbij
      map_rel_iff' := fun {r s} =>
        Ideal.comap_le_comap_iff_of_surjective _ Ideal.Quotient.mk_surjective _ _ }
  have he : ∀ r : PrimeSpectrum B, (e r).asIdeal = r.asIdeal.comap φ := fun _ => rfl
  have hmem : ∀ p : PrimeSpectrum B,
      p ∈ PrimeSpectrum.zeroLocus ((I.map φ : Ideal B) : Set B) \
          PrimeSpectrum.zeroLocus ((a.map φ : Ideal B) : Set B) ↔
        H p ∈ PrimeSpectrum.zeroLocus (I : Set A) \
          PrimeSpectrum.zeroLocus (a : Set A) := by
    intro p
    change (I.map φ ≤ p.asIdeal ∧ ¬ a.map φ ≤ p.asIdeal) ↔
      (I ≤ p.asIdeal.comap φ ∧ ¬ a ≤ p.asIdeal.comap φ)
    simp only [Ideal.map_le_iff_le_comap]
  have himage : H '' (PrimeSpectrum.zeroLocus ((I.map φ : Ideal B) : Set B) \
      PrimeSpectrum.zeroLocus ((a.map φ : Ideal B) : Set B)) =
      PrimeSpectrum.zeroLocus (I : Set A) \ PrimeSpectrum.zeroLocus (a : Set A) := by
    ext p
    obtain ⟨q, rfl⟩ := H.surjective p
    rw [H.injective.mem_set_image]
    exact hmem q
  have hconn' : ∀ V : Set (PrimeSpectrum B), IsOpen V → V.Nonempty →
      PrimeSpectrum.zeroLocus ((I.map φ : Ideal B) : Set B) \
        PrimeSpectrum.zeroLocus ((a.map φ : Ideal B) : Set B) ⊆ V → _root_.IsConnected V := by
    intro V hV hne hsub
    refine H.isConnected_image.mp (hconn (H '' V) (H.isOpenMap _ hV) (hne.image H) ?_)
    rw [← himage]
    exact Set.image_mono hsub
  have hdim' : ∀ p q : PrimeSpectrum B, p.asIdeal ∈ minimalPrimes B → ¬ I.map φ ≤ p.asIdeal →
      p.asIdeal ≤ q.asIdeal → a.map φ ≤ q.asIdeal →
      ((cohomologicalDimension B (I.map φ) (I.fg_of_isNoetherianRing.map φ) + 1 : ℤ) : EInt) <
        krullDimToEInt (closureLocalDimension B p q) := by
    intro p q hp hpI hpq haq
    have hpA : (e p).asIdeal ∈ minimalPrimes A := by
      refine PrimeSpectrum.isMin_iff.mp fun r hr => ?_
      have hrp : e.symm r ≤ p := by
        simpa only [e.symm_apply_apply] using e.symm.monotone hr
      simpa only [e.apply_symm_apply] using e.monotone (PrimeSpectrum.isMin_iff.mpr hp hrp)
    have hd := hdim (e p) (e q) hpA (fun h => hpI (Ideal.map_le_iff_le_comap.mpr h))
      (e.monotone hpq) (Ideal.map_le_iff_le_comap.mp haq)
    rw [← closureLocalDimension_eq_ringKrullDim_localizedQuotient (e p) (e q)] at hd
    calc ((cohomologicalDimension B (I.map φ) (I.fg_of_isNoetherianRing.map φ) + 1 : ℤ) : EInt)
        ≤ ((cohomologicalDimension A I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) := by
          have := cohomologicalDimension_map_le φ I I.fg_of_isNoetherianRing
          simp only [WithBotTop.coe, Function.comp_apply, WithBot.coe_le_coe,
            WithTop.coe_le_coe]
          omega
      _ < krullDimToEInt (closureLocalDimension A (e p) (e q)) := hd
      _ = krullDimToEInt (closureLocalDimension B p q) := by
          rw [closureLocalDimension_quotientMk e he p q]
  have _ : _root_.IsReduced B :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical ⊥)
  have _ : IsAdicComplete (I.map φ) B := hφ ▸ isAdicComplete_quotient_nilradical A I
  obtain ⟨L, hL⟩ := exists_isDualizingComplex_quotient_nilradical A K hK
  have _ : IsIso (comparisonMap B (I.map φ) (a.map φ)
      (unitModule (complementZeroLocus B (a.map φ) : Scheme))) :=
    isIso_comparisonMap_unitModule_of_isReduced B (I.map φ) (a.map φ) (Ideal.map_mono hIa) L hL
      hdim'
  have hpreA := (isPreconnected_zeroLocus_sdiff_of_isIso B (I.map φ) (a.map φ) hconn').image H
    H.continuous.continuousOn
  rw [himage] at hpreA
  exact (Set.eq_empty_or_nonempty _).imp_right fun hne => ⟨hne, hpreA⟩

end Stacks.Algebraization

end
