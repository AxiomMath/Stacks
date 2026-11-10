module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.FinitePresentation.ColimitsII
public import StacksFrontier.RingTheory.CompleteIntersection.AtPrime
public import StacksFrontier.RingTheory.CompleteIntersection.Relative
public import StacksFrontier.RingTheory.CompleteIntersection.RelativeConormal
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Criteria
public import StacksFrontier.RingTheory.Different.Formula.SquarePresentation
public import StacksFrontier.RingTheory.Etale.LiftSmoothMap
public import StacksFrontier.RingTheory.Flat.RegularSequenceOverBase
public import StacksFrontier.RingTheory.Koszul.FlatQuotient
public import StacksFrontier.RingTheory.RingHom.FinitePresentation
public import StacksFrontier.RingTheory.Smooth.SmoothAt
public import StacksFrontier.RingTheory.Smooth.SymmetricAlgebra
public import StacksFrontier.RingTheory.Smooth.Syntomic
public import StacksFrontier.RingTheory.Smoothing.ImprovingPresentations
public import StacksFrontier.RingTheory.Smoothing.SyntomicCompleteIntersectionExtension
public import StacksFrontier.RingTheory.Syntomic.BaseChange
public import StacksFrontier.RingTheory.Syntomic.Defs
public import StacksFrontier.RingTheory.Syntomic.SyntomicAt
public import StacksFrontier.RingTheory.UniversalHomeomorphism.Examples
public import StacksFrontier.RingTheory.Syntomic.Morphisms
public import StacksFrontier.RingTheory.Smoothing.LiftingAlongSurjections.SyntomicLift

/-!
# Lifting smooth algebras along a surjection

A smooth algebra over a quotient `R₀` of `R` is syntomic, so it has a syntomic lift `A`; the fibres
of `A` over primes containing the kernel are base changes of the smooth special fibre, so `A` is
smooth near `V(IA)`, and inverting one element of the smooth locus congruent to `1` modulo `IA`
gives a smooth lift with unchanged special fibre.

## Main results

* `Stacks.Smoothing.exists_smooth_lift_of_surjective`: a smooth algebra over a quotient of the
  base lifts to a smooth algebra over the base with the given special fibre.

## References

* [Stacks Project, Proposition 16.10.4, Tag 07M8](https://stacks.math.columbia.edu/tag/07M8)
-/

@[expose] public section

open scoped TensorProduct

open RingTheory.Sequence

namespace Stacks.Smoothing

open Koszul

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

universe u v w

/-- If the special fibre of `A` is the smooth `R₀`-algebra `A₀`, then the fibre of `A` over a
prime of `R` containing the kernel `I` is a base change of `A₀`, hence formally smooth over the
residue field. -/
private lemma formallySmooth_specialFiber
    {R R₀ A₀ A : Type*} [CommRing R] [CommRing R₀] [CommRing A₀] [CommRing A]
    [Algebra R R₀] [Algebra R₀ A₀] [Algebra R A]
    (I : Ideal R) (hI : I = RingHom.ker (algebraMap R R₀))
    (hsurj : Function.Surjective (algebraMap R R₀))
    (h₀ : Algebra.Smooth R₀ A₀)
    (e : A₀ ≃+* A ⧸ Ideal.map (algebraMap R A) I)
    (he : ∀ r : R, e (algebraMap R₀ A₀ (algebraMap R R₀ r)) =
      Ideal.Quotient.mk _ (algebraMap R A r))
    (p : Ideal R) [p.IsPrime] (hp : I ≤ p) :
    Algebra.FormallySmooth p.ResidueField (p.Fiber A) := by
  let k := p.ResidueField
  have hker : RingHom.ker (algebraMap R R₀) ≤ RingHom.ker (algebraMap R k) := by
    rw [Ideal.ker_algebraMap_residueField]
    exact (hI ▸ hp)
  let f : R₀ →+* k := (algebraMap R R₀).liftOfSurjective hsurj
    ⟨algebraMap R k, hker⟩
  let : Algebra R₀ k := f.toAlgebra
  let : IsScalarTower R R₀ k := .of_algebraMap_eq' (by
    ext r
    exact (RingHom.liftOfSurjective_comp_apply (algebraMap R R₀) hsurj
      ⟨algebraMap R k, hker⟩ r).symm)
  let : Algebra R A₀ := Algebra.compHom A₀ (algebraMap R R₀)
  let : IsScalarTower R R₀ A₀ := .of_algebraMap_eq' (by ext r; rfl)
  let : Algebra.Smooth R₀ A₀ := h₀
  let qA := Ideal.map (algebraMap R A) I
  let eR : A₀ ≃ₐ[R] A ⧸ qA :=
    { toRingEquiv := e
      commutes' := he }
  let B : Type _ := TensorProduct R A k
  let : Algebra k B := Algebra.TensorProduct.rightAlgebra
  let : Algebra k ((A ⧸ qA) ⊗[R] k) := Algebra.TensorProduct.rightAlgebra
  let J := Ideal.map (algebraMap A B) qA
  have hJ : J = ⊥ := by
    apply (Ideal.map_eq_bot_iff_le_ker (algebraMap A B)).2
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    have hrp : r ∈ p := hp hr
    have hz : algebraMap R k r = 0 :=
      RingHom.mem_ker.1 (by rwa [Ideal.ker_algebraMap_residueField])
    change algebraMap A B (algebraMap R A r) = 0
    rw [← IsScalarTower.algebraMap_apply R A B]
    change (algebraMap R A r) ⊗ₜ[R] (1 : k) = 0
    rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
    simp [hz]
  let eQT := Algebra.TensorProduct.quotientTensorEquiv (R := R) A k A qA
  let eQTk : (A ⧸ qA) ⊗[R] k ≃ₐ[k] B ⧸ J :=
    AlgEquiv.ofRingEquiv (R := k) (f := eQT.toRingEquiv) (by
      intro x
      calc
        eQT (algebraMap k ((A ⧸ qA) ⊗[R] k) x) = eQT ((1 : A ⧸ qA) ⊗ₜ[R] x) := by
          rw [Algebra.TensorProduct.algebraMap_eq_includeRight]
          rfl
        _ = Ideal.Quotient.mk J ((1 : A) ⊗ₜ[R] x) := by
          simpa [eQT, J, qA] using
            (Algebra.TensorProduct.quotientTensorEquiv_apply_tmul (R := R) A k A qA (1 : A) x)
        _ = algebraMap k (B ⧸ J) x := by
          rw [IsScalarTower.algebraMap_apply k B (B ⧸ J)]
          rw [Algebra.TensorProduct.algebraMap_eq_includeRight]
          rfl)
  let eQ : (A ⧸ qA) ⊗[R] k ≃ₐ[k] B :=
    eQTk.trans ((Ideal.quotientEquivAlgOfEq k hJ).trans (AlgEquiv.quotientBot k B))
  let commKA : p.Fiber A ≃ₐ[k] B :=
    Algebra.TensorProduct.commRight R k A
  let commAK : (A ⧸ qA) ⊗[R] k ≃ₐ[k] k ⊗[R] (A ⧸ qA) :=
    (Algebra.TensorProduct.commRight R k (A ⧸ qA)).symm
  let : TensorProduct.CompatibleSMul R R₀ k A₀ := ⟨fun s x y => by
    obtain ⟨r, hr⟩ := hsurj s
    rw [← hr, IsScalarTower.algebraMap_smul (A := R₀) (M := k) r x,
      IsScalarTower.algebraMap_smul (A := R₀) (M := A₀) r y]
    exact TensorProduct.smul_tmul r x y⟩
  let eBase : k ⊗[R] A₀ ≃ₐ[k] k ⊗[R₀] A₀ :=
    (Algebra.TensorProduct.equivOfCompatibleSMul R R₀ k k A₀).symm
  let eFiber : p.Fiber A ≃ₐ[k] k ⊗[R₀] A₀ :=
    commKA.trans (eQ.symm.trans <| commAK.trans <|
      (Algebra.TensorProduct.congr (AlgEquiv.refl : k ≃ₐ[k] k) eR.symm).trans eBase)
  exact Algebra.FormallySmooth.of_equiv eFiber.symm

/-- A smooth algebra over a quotient of the base is the special fibre of a smooth algebra over the
base: if `R → R₀` is surjective with kernel `I` and `R₀ → A₀` is smooth, there is a smooth
`R`-algebra `A` together with a ring equivalence `A₀ ≃ A/IA` compatible with the maps from `R`. -/
@[stacks 07M8 "smooth lift"]
theorem exists_smooth_lift_of_surjective
    (R : Type u) (R₀ : Type v) (A₀ : Type w) [CommRing R] [CommRing R₀] [CommRing A₀]
    [Algebra R R₀] [Algebra R₀ A₀]
    (hR : Function.Surjective (algebraMap R R₀))
    (hA₀ : Algebra.Smooth R₀ A₀) :
    ∃ (A : Type (max u w)) (_ : CommRing A) (a : Algebra R A),
      letI := a
      Algebra.Smooth R A ∧
        ∃ e : A₀ ≃+* A ⧸ Ideal.map (algebraMap R A)
          (RingHom.ker (algebraMap R R₀)),
          ∀ r : R, e (algebraMap R₀ A₀ (algebraMap R R₀ r)) =
            Ideal.Quotient.mk _ (algebraMap R A r) := by
  obtain ⟨I, hI⟩ : ∃ I : Ideal R, I = RingHom.ker (algebraMap R R₀) := ⟨_, rfl⟩
  rw [← hI]
  let : Algebra.Smooth R₀ A₀ := hA₀
  let : Algebra.Syntomic R₀ A₀ := (Algebra.Smooth.exists_span_eq_top_isStandardSmooth_and_syntomic
    R₀ A₀).2
  obtain ⟨A, hA, a, hSyn⟩ :=
    exists_syntomic_lift_of_surjective R R₀ A₀ hR inferInstance
  let : CommRing A := hA
  let : Algebra R A := a
  let : Algebra.Syntomic R A := hSyn.1
  rcases hSyn.2 with ⟨e, he⟩
  have heq : Ideal.map (algebraMap R A) I =
      Ideal.map (algebraMap R A) (RingHom.ker (algebraMap R R₀)) := by rw [hI]
  let eI : A ⧸ Ideal.map (algebraMap R A) I ≃+* A₀ :=
    (Ideal.quotientEquivAlgOfEq A heq).toRingEquiv.trans e.symm
  have heI : ∀ r : R,
      eI.symm (algebraMap R₀ A₀ (algebraMap R R₀ r)) =
        Ideal.Quotient.mk (Ideal.map (algebraMap R A) I) (algebraMap R A r) := by
    intro r
    change (Ideal.quotientEquivAlgOfEq A heq).symm
      (e (algebraMap R₀ A₀ (algebraMap R R₀ r))) = _
    rw [he r, ← Ideal.quotientEquivAlgOfEq_mk A heq (algebraMap R A r)]
    exact (Ideal.quotientEquivAlgOfEq A heq).symm_apply_apply _
  let K := Ideal.map (algebraMap R A) I
  let G : Set A := {g | Algebra.Smooth R (Localization.Away g)}
  let J := Ideal.span G
  have hsum : K ⊔ J = ⊤ := by
    by_contra hneTop
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (K ⊔ J) hneTop
    let : m.IsPrime := hm.isPrime
    have hKm : K ≤ m := le_trans le_sup_left hle
    have hmSmooth : Algebra.IsSmoothAt R m := by
      let p := m.comap (algebraMap R A)
      let : p.IsPrime := inferInstance
      have hp : I ≤ p := fun r hr => hKm (Ideal.mem_map_of_mem (algebraMap R A) hr)
      let : m.LiesOver p := ⟨rfl⟩
      let : Algebra.FormallySmooth p.ResidueField (p.Fiber A) :=
        formallySmooth_specialFiber I hI hR hA₀ eI.symm heI p hp
      exact Algebra.IsSmoothAt.of_formallySmooth_fiber p m
    obtain ⟨g, hgm, hgs⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R m
    have : g ∈ J := Ideal.subset_span hgs
    exact hgm (hle (Ideal.mem_sup_right this))
  have hone : (1 : A) ∈ K ⊔ J := by rw [hsum]; simp
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hone
  let φ : A →+* A₀ := eI.toRingHom.comp (Ideal.Quotient.mk K)
  have hkerφ : RingHom.ker φ = K := by
    simpa [φ] using RingHom.ker_equiv_comp (Ideal.Quotient.mk K) eI
  have hφy : φ y = 1 := by
    have hx0 : φ x = 0 := RingHom.mem_ker.mp (by simpa [hkerφ] using hx)
    simpa [map_add, hx0] using congrArg φ hxy
  let Af := Localization.Away y
  have hT : Submonoid.map φ (Submonoid.powers y) = Submonoid.powers (1 : A₀) := by
    rw [Submonoid.map_powers, hφy]
  let : IsLocalization (Submonoid.powers (1 : A₀)) A₀ :=
    IsLocalization.of_le_isUnit (by
      intro z hz
      have hz' : z = 1 := by simpa using hz
      subst z
      exact isUnit_one)
  let ψ : Af →+* A₀ := IsLocalization.map A₀ φ
    (hT.symm ▸ Submonoid.le_comap_map (Submonoid.powers y))
  have hsurjφ : Function.Surjective φ :=
    eI.surjective.comp Ideal.Quotient.mk_surjective
  have hsurjψ : Function.Surjective ψ := by
    intro z
    obtain ⟨x, hx⟩ := hsurjφ z
    refine ⟨algebraMap A Af x, ?_⟩
    rwa [IsLocalization.map_eq]
  have hkerψ : RingHom.ker ψ = Ideal.map (algebraMap A Af) K := by
    rw [IsLocalization.ker_map A₀ φ hT, hkerφ]
  have hKloc : Ideal.map (algebraMap A Af) K = Ideal.map (algebraMap R Af) I := by
    simp [K, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  let eAf : Af ⧸ Ideal.map (algebraMap R Af) I ≃+* A₀ :=
    (Ideal.quotEquivOfEq hKloc.symm).trans <|
      (Ideal.quotEquivOfEq hkerψ.symm).trans <|
        RingHom.quotientKerEquivOfSurjective hsurjψ
  have hD : (↑(PrimeSpectrum.basicOpen y) : Set (PrimeSpectrum A)) ⊆
      Algebra.smoothLocus R A := by
    intro z hz
    have hyz : y ∉ z.asIdeal := (PrimeSpectrum.mem_basicOpen y z).mp hz
    have hex : ∃ g ∈ G, g ∉ z.asIdeal := by
      by_contra h
      push Not at h
      exact hyz (Ideal.span_le.mpr (fun g hg => h g hg) hy)
    obtain ⟨g, hg, hgz⟩ := hex
    exact (Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hg)
      ((PrimeSpectrum.mem_basicOpen g z).mpr hgz)
  have heAf : ∀ r : R, eAf.symm (algebraMap R₀ A₀ (algebraMap R R₀ r)) =
      Ideal.Quotient.mk (Ideal.map (algebraMap R Af) I) (algebraMap R Af r) := by
    refine fun r => eAf.symm_apply_eq.mpr ?_
    have hmk : eAf (Ideal.Quotient.mk (Ideal.map (algebraMap R Af) I) (algebraMap R Af r)) =
        ψ (algebraMap R Af r) := by
      change (RingHom.quotientKerEquivOfSurjective hsurjψ)
        (Ideal.quotEquivOfEq hkerψ.symm
          (Ideal.quotEquivOfEq hKloc.symm
            (Ideal.Quotient.mk (Ideal.map (algebraMap R Af) I) (algebraMap R Af r)))) = _
      rw [Ideal.quotEquivOfEq_mk, Ideal.quotEquivOfEq_mk]
      exact RingHom.quotientKerEquivOfSurjective_apply_mk hsurjψ _
    rw [hmk, IsScalarTower.algebraMap_apply R A Af, IsLocalization.map_eq]
    exact (eI.apply_symm_apply _).symm.trans (congrArg eI (heI r))
  exact ⟨Af, inferInstance, inferInstance,
    Algebra.basicOpen_subset_smoothLocus_iff_smooth.mp hD, eAf.symm, heAf⟩

end Stacks.Smoothing

end
