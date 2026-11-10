module

public import Mathlib.RingTheory.Extension.Cotangent.Basis
public import Mathlib.RingTheory.Smooth.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.FinitePresentation.ColimitsII
public import StacksFrontier.RingTheory.CompleteIntersection.AtPrime
public import StacksFrontier.RingTheory.CompleteIntersection.Relative
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Criteria
public import StacksFrontier.RingTheory.Smooth.Syntomic
public import StacksFrontier.RingTheory.Smoothing.ImprovingPresentations
public import StacksFrontier.RingTheory.Syntomic.Basic
public import StacksFrontier.RingTheory.Syntomic.SyntomicAt
public import StacksFrontier.RingTheory.Syntomic.Morphisms

/-!
# Syntomic algebras admit smooth global complete intersection enlargements

For a syntomic ring map `R → A` there is a smooth `A`-algebra `C` with a retraction onto `A`
which is a *relative global complete intersection* over `R`: it is cut out of a polynomial ring
over `R` by finitely many equations, is flat over `R`, and all of its fibres have dimension
`n - c`, where `n` is the number of variables and `c` the number of equations.

## Main results

* `Stacks.Smoothing.exists_smooth_retract_isRelativeGlobalCompleteIntersection`: the smooth
  retract, its flatness over `R`, and its relative global complete intersection presentation.

## Implementation notes

The enlargement is the one of Stacks 07CE, instantiated at `a = 1`: a syntomic map is in
particular a local complete intersection, so the first of the two improvements there applies and
makes `C_1 = C` smooth over `A` with a presentation whose conormal module is free. Freeness of the
conormal module is what upgrades the presentation to a relative global complete intersection: the
rank of the conormal module and the number of variables are compared fibrewise against a local
relative global complete intersection presentation obtained from flatness, which bounds the
relative dimension at every prime by the difference.

The retraction is recorded as a ring homomorphism whose composite with the structure map `A → C`
is the identity, and the scalar compatibility as `IsScalarTower R A C`.

## References

* [Stacks Project, Tag 07CG](https://stacks.math.columbia.edu/tag/07CG)
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Stacks.Smoothing

/-- A syntomic `R`-algebra `S` with a presentation by finitely many polynomial variables whose
conormal module is free is a relative global complete intersection over `R`. -/
public theorem syntomic_freeConormal_isRelativeGlobalCompleteIntersection
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.Syntomic R S]
    (hFree : HasFreeConormalPresentation R S) :
    Algebra.IsRelativeGlobalCompleteIntersection R S := by
  classical
  obtain ⟨n, P₀, hfree⟩ := hFree
  let : Module.Free S P₀.toExtension.Cotangent := hfree
  have hfinite : Module.Finite S P₀.toExtension.Cotangent :=
    Algebra.Extension.Cotangent.finite P₀.fg_ker_of_finitePresentation
  obtain ⟨P, _, _, _⟩ := Algebra.Generators.exists_presentation_of_free_cotangent P₀
  refine Algebra.IsRelativeGlobalCompleteIntersection.of_presentation P (hP := ?_)
  by_cases hS : Subsingleton S
  · refine ⟨fun p _ hnt => ?_⟩
    have : Subsingleton (p.Fiber S) := inferInstance
    exfalso
    exact (not_subsingleton_iff_nontrivial.mpr hnt) inferInstance
  · let : Nontrivial S := not_subsingleton_iff_nontrivial.mp hS
    let r := Module.finrank S P₀.toExtension.Cotangent
    let b₀ : Module.Basis (Fin r) S P₀.toExtension.Cotangent := Module.finBasis S _
    obtain ⟨P, _, _, _⟩ := Algebra.Generators.exists_presentation_of_free_cotangent P₀
    have hdim (q : Ideal S) [q.IsPrime] :
        Algebra.relativeDimensionAt R q + Nat.card (Unit ⊕ Fin r) ≤
          Nat.card (Unit ⊕ Fin n) := by
      let hflatci := Algebra.Syntomic.flat_localization_and_isCompleteIntersection_fiber
        (R := R) (S := S) q
      let : Module.Flat R (Localization.AtPrime q) := hflatci.1
      obtain ⟨g, hg, hlocal⟩ :=
        Algebra.exists_notMem_isRelativeGlobalCompleteIntersection_of_flat
          (R := R) (S := S) q hflatci.2
      let T := Localization.Away g
      have hdisj : Disjoint (Submonoid.powers g : Set S) q :=
        (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hg
      let qT : Ideal T := q.map (algebraMap S T)
      have hqT : qT.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
        (Submonoid.powers g) T q ‹q.IsPrime› hdisj
      let : qT.IsPrime := hqT
      have hcomap : qT.comap (algebraMap S T) = q :=
        IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) T
          ‹q.IsPrime› hdisj
      have hrel : Algebra.relativeDimensionAt R q = Algebra.relativeDimensionAt R qT :=
        (Algebra.relativeDimensionAt_congr hcomap).symm.trans
          (Algebra.relativeDimensionAt_comap_eq (R := R) g T qT)
      let : Algebra.IsRelativeGlobalCompleteIntersection R T := hlocal
      obtain ⟨m, t, Q, hQ⟩ := hlocal.out
      let : Q.IsRelativeGlobalCompleteIntersection := hQ
      obtain ⟨bQ, _⟩ := Q.exists_basis_cotangent_relation
      let K := qT.ResidueField
      let bT : Module.Basis (Fin r) T (T ⊗[S] P₀.toExtension.Cotangent) := b₀.baseChange T
      let bK : Module.Basis (Fin r) K
          (K ⊗[T] (T ⊗[S] P₀.toExtension.Cotangent)) := bT.baseChange K
      let bQK : Module.Basis (Fin t) K (K ⊗[T] Q.toGenerators.toExtension.Cotangent) :=
        bQ.baseChange K
      let : Module.Finite K
          (K ⊗[T] (T ⊗[S] P₀.toExtension.Cotangent)) := Module.Finite.of_basis bK
      let : Module.Finite K (K ⊗[T] Q.toGenerators.toExtension.Cotangent) :=
        Module.Finite.of_basis bQK
      have hrankP : Module.finrank K
          (K ⊗[T] (T ⊗[S] P₀.toExtension.Cotangent)) = r := by
        rw [Module.finrank_eq_card_basis bK]
        simp
      have hrankQ : Module.finrank K (K ⊗[T] Q.toGenerators.toExtension.Cotangent) = t := by
        rw [Module.finrank_eq_card_basis bQK]
        simp
      obtain ⟨e⟩ :=
        Algebra.Generators.nonempty_cotangent_baseChange_prod_linearEquiv_of_isLocalizationAway
          (T := T) g P₀ Q.toGenerators
      have hcounts := finrank_add_eq_of_prodPi_linearEquiv K e
      rw [hrankP, hrankQ] at hcounts
      have hnt : Nontrivial ((qT.under R).Fiber T) :=
        PrimeSpectrum.nonempty_iff_nontrivial.1
          ⟨PrimeSpectrum.primesOverOrderIsoFiber R T (qT.under R)
            ⟨qT, ⟨hqT, ⟨rfl⟩⟩⟩⟩
      have hdimFiber := hQ.ringKrullDim_fiber_add_card_eq_card (qT.under R) hnt
      have hlocaldim : Algebra.relativeDimensionAt R qT + (t : WithBot ℕ∞) ≤ m := by
        calc
          Algebra.relativeDimensionAt R qT + (t : WithBot ℕ∞) ≤
              ringKrullDim ((qT.under R).Fiber T) + (t : WithBot ℕ∞) := by
                gcongr
                exact Algebra.relativeDimensionAt_le_ringKrullDim_fiber qT
          _ = (m : WithBot ℕ∞) := by
            simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hdimFiber
      have hcard : Nat.card (Unit ⊕ Fin r) + m = t + Nat.card (Unit ⊕ Fin n) := by
        simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_unit,
          Fintype.card_fin]
        omega
      have hdimT : Algebra.relativeDimensionAt R qT +
          (Nat.card (Unit ⊕ Fin r) : WithBot ℕ∞) ≤ Nat.card (Unit ⊕ Fin n) := by
        have hdimNat : Algebra.relativeDimensionAt R qT ≤ (m - t : ℕ) :=
          WithBot.le_natCast_sub_of_add_le hlocaldim
        have htm' : (t : WithBot ℕ∞) ≤ m := by
          simpa using (add_le_add_left (Algebra.zero_le_relativeDimensionAt R qT)
            (t : WithBot ℕ∞)).trans hlocaldim
        have htm : t ≤ m := by exact_mod_cast htm'
        have hbound : m - t + Nat.card (Unit ⊕ Fin r) ≤ Nat.card (Unit ⊕ Fin n) := by
          omega
        calc
          Algebra.relativeDimensionAt R qT + (Nat.card (Unit ⊕ Fin r) : WithBot ℕ∞) ≤
              (m - t : ℕ) + Nat.card (Unit ⊕ Fin r) :=
            add_le_add_left hdimNat _
          _ ≤ Nat.card (Unit ⊕ Fin n) := by exact_mod_cast hbound
      simpa [hrel] using hdimT
    let Pfin : Algebra.Presentation R S (Fin (Nat.card (Unit ⊕ Fin n)))
        (Fin (Nat.card (Unit ⊕ Fin r))) :=
      P.reindex (Finite.equivFin (Unit ⊕ Fin n)).symm
        (Finite.equivFin (Unit ⊕ Fin r)).symm
    have hPfin : Pfin.IsRelativeGlobalCompleteIntersection :=
      Algebra.Presentation.isRelativeGlobalCompleteIntersection_of_relativeDimensionAt_add_le
        Pfin hdim
    refine ⟨fun p _ hnt => ?_⟩
    simpa [Pfin] using hPfin.ringKrullDim_fiber_add_card_eq_card p hnt

/-- **Stacks 07CG.** A syntomic `R`-algebra `A` admits a smooth `A`-algebra `C` with a retraction
`C → A`, flat over `R` and a relative global complete intersection over `R`: so `C` is cut out of
a polynomial ring by `c` equations, flat over `R`, with all fibres of dimension `n - c`. -/
@[stacks 07CG]
theorem exists_smooth_retract_isRelativeGlobalCompleteIntersection
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.Syntomic R A] :
    ∃ (C : Type v) (hC : CommRing C) (hRC : Algebra R C) (hAC : Algebra A C)
      (hTower : IsScalarTower R A C),
      let : CommRing C := hC
      let : Algebra R C := hRC
      let : Algebra A C := hAC
      let : IsScalarTower R A C := hTower
      Algebra.Smooth A C ∧
        Module.Flat R C ∧
          ∃ ρ : C →+* A,
          ρ.comp (algebraMap A C) = RingHom.id A ∧
            Algebra.IsRelativeGlobalCompleteIntersection R C := by
  rcases exists_finiteType_retraction_improving_presentation R A with
    ⟨C, hC, hRC, hAC, hTower, hType, ρ, _, _, _, _, _, _, hρ, hImproved⟩
  let : CommRing C := hC
  let : Algebra R C := hRC
  let : Algebra A C := hAC
  let : IsScalarTower R A C := hTower
  let : Algebra.FiniteType A C := hType
  let C₁ := Localization.Away (algebraMap A C (1 : A))
  let R₁ := Localization.Away (1 : A)
  let : Algebra R₁ C₁ :=
    (Localization.awayMap (algebraMap A C) (1 : A)).toAlgebra
  let : IsScalarTower A R₁ C₁ :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := R₁) (A := C₁) (by
      intro a
      have hmap :
          (Localization.awayMap (algebraMap A C) (1 : A)).comp (algebraMap A R₁) =
            (algebraMap C C₁).comp (algebraMap A C) :=
        IsLocalization.map_comp (by
          rintro x ⟨n, rfl⟩
          exact ⟨n, by simp⟩)
      rw [IsScalarTower.algebraMap_eq A C C₁]
      change ((algebraMap C C₁).comp (algebraMap A C)) a =
        ((Localization.awayMap (algebraMap A C) (1 : A)).comp (algebraMap A R₁)) a
      exact (DFunLike.congr_fun hmap a).symm)
  have hAtOne := hImproved.1 1 (by
    let : Algebra.Smooth A (Localization.Away (1 : A)) :=
      Algebra.Smooth.of_isLocalization_Away 1
    have : Algebra.Syntomic A (Localization.Away (1 : A)) := Algebra.Smooth.syntomic A _
    exact (RingHom.syntomic_iff_flat_and_isLocalCompleteIntersection
      (algebraMap R (Localization.Away (1 : A)))).mp (by
        simpa +instances only [toAlgebra_algebraMap] using
          (Algebra.Syntomic.comp R A (Localization.Away (1 : A)))) |>.2)
  let : IsLocalization.Away (1 : C) C₁ := by
    convert (inferInstance : IsLocalization.Away (algebraMap A C (1 : A)) C₁) using 1
    simp
  have hSmooth₁ : Algebra.Smooth A C₁ := by
    have hR₁ : Algebra.Smooth A R₁ :=
      Algebra.Smooth.of_equiv (IsLocalization.atOne A R₁)
    let : Algebra.Smooth R₁ C₁ := hAtOne.1
    exact Algebra.Smooth.comp A R₁ C₁
  let : Algebra.Smooth A C₁ := hSmooth₁
  have hSmooth : Algebra.Smooth A C :=
    Algebra.Smooth.of_equiv ((IsLocalization.atOne C C₁).restrictScalars A).symm
  let : Algebra.Syntomic A C := Algebra.Smooth.syntomic A C
  have hSyntomic : Algebra.Syntomic R C := Algebra.Syntomic.comp R A C
  have hSyntomic₁ : Algebra.Syntomic R C₁ := by
    have : Algebra.Syntomic C C₁ := Algebra.Smooth.syntomic C C₁
    exact Algebra.Syntomic.comp R C C₁
  let : Algebra.Syntomic R C₁ := hSyntomic₁
  have hGci₁ : Algebra.IsRelativeGlobalCompleteIntersection R C₁ :=
    syntomic_freeConormal_isRelativeGlobalCompleteIntersection hAtOne.2
  have hGci : Algebra.IsRelativeGlobalCompleteIntersection R C :=
    let : Algebra.IsRelativeGlobalCompleteIntersection R C₁ := hGci₁
    Algebra.IsRelativeGlobalCompleteIntersection.of_algEquiv
      ((IsLocalization.atOne C C₁).restrictScalars R).symm
  refine ⟨C, hC, hRC, hAC, hTower, hSmooth, hSyntomic.flat, ρ.toRingHom, ?_, hGci⟩
  change (ρ.comp (IsScalarTower.toAlgHom R A C)).toRingHom = _
  exact congrArg AlgHom.toRingHom hρ

end Stacks.Smoothing

end
