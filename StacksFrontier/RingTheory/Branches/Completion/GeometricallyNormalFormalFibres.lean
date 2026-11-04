module

public import Mathlib.CategoryTheory.Presentable.Directed
public import Mathlib.Data.Finset.Card
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.QuasiFinite.Weakly
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Smooth.AdicCompletion
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Unramified.LocalStructure
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.RingTheory.Nilpotent.Ideal
import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.MinimalPrimesDirectLimit
public import StacksFrontier.RingTheory.AdicCompletion.Algebraization
public import StacksFrontier.RingTheory.AdicCompletion.FiniteAlgebra
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Branches.Defs
public import StacksFrontier.RingTheory.Branches.Henselization
public import StacksFrontier.RingTheory.Branches.MinimalPrimes
import StacksFrontier.RingTheory.Catenary.Formal
public import StacksFrontier.RingTheory.Etale.Basic
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import StacksFrontier.RingTheory.Flat.NormalFibres
public import StacksFrontier.RingTheory.GeometricallyNormal.Defs
public import StacksFrontier.RingTheory.GeometricallyNormal.TFAE
public import StacksFrontier.RingTheory.GeometricallyNormal.TensorProduct
public import StacksFrontier.RingTheory.GeometricallyReduced.TensorProduct
public import StacksFrontier.RingTheory.Henselian.Henselization.Basic
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.Henselian.HenselizationUniversalProperty
public import StacksFrontier.RingTheory.Henselian.IntegralDomain
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.BaseChange
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.Existence
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.Nagata.AnalyticallyUnramified
public import StacksFrontier.RingTheory.Nagata.Defs
public import StacksFrontier.RingTheory.Nagata.IntegralClosure
public import StacksFrontier.RingTheory.Smooth.Normal
public import StacksFrontier.RingTheory.WeaklyEtale.Descent
public import StacksFrontier.RingTheory.WeaklyEtale.Flat

@[expose] public section

/-!
# Completion of a local ring with geometrically normal formal fibres

Let `A` be a Noetherian local ring with completion `Â`. If every formal fibre of `A` is
geometrically normal over the residue field of the corresponding prime, then `A` is a Nagata
ring and completion changes neither the number of branches nor the number of geometric branches
of `A`.

## Main results

* `isReduced_tensor_completion_iff`: for a finite `A`-algebra `S`, the ring `S ⊗[A] Â` is reduced
  if and only if the localization of `S` at every maximal ideal is analytically unramified.
* `isNagataRing_and_numberOfBranches_and_numberOfGeometricBranches_eq_adicCompletion`: geometric
  normality of all formal fibres implies that `A` is Nagata and that the ordinary and geometric
  branch counts of `A` agree with those of `Â`.

## Implementation notes

The completion of `A` is `AdicCompletion (IsLocalRing.maximalIdeal A) A` and the formal fibre at a
prime `q` is `q.Fiber (AdicCompletion (IsLocalRing.maximalIdeal A) A)`, the base change of the
completion to the residue field at `q`. Branch counts are `numberOfBranches` and
`numberOfGeometricBranches`, and the statements take arbitrary models of the henselizations and
strict henselizations of both `A` and `Â`.

## References

* [A. Beddani, Theorem 2.3][Beddani]
* [The Stacks Project, Tag 0C2E](https://stacks.math.columbia.edu/tag/0C2E)
-/

universe u v w x y

open Topology
open IsLocalRing
open scoped TensorProduct

/-- For a finite algebra `S` over a Noetherian local ring `A`, the ring `S ⊗[A] Â` is reduced if
and only if the localization of `S` at every maximal ideal is analytically unramified. -/
public lemma isReduced_tensor_completion_iff
    {A : Type u} {S : Type v} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing S] [Algebra A S] [Module.Finite A S] :
    IsReduced (S ⊗[A] AdicCompletion (maximalIdeal A) A) ↔
      ∀ (q : Ideal S) [q.IsMaximal], IsAnalyticallyUnramified (Localization.AtPrime q) := by
  let : IsLocalization.AtPrime A (maximalIdeal A) :=
    IsLocalization.of_le_isUnit fun a ha => (notMem_maximalIdeal (R := A)).mp ha
  obtain ⟨e⟩ := AdicCompletion.nonempty_algEquiv_pi_primesOver (S := S)
    (maximalIdeal A) A (fun q => Localization.AtPrime q.1)
  constructor
  · intro h q hq
    let q' : (maximalIdeal A).primesOver S := ⟨q, inferInstance, by
      rw [Ideal.liesOver_iff]
      exact (eq_maximalIdeal (inferInstance : (q.under A).IsMaximal)).symm⟩
    have : IsReduced (∀ q : (maximalIdeal A).primesOver S,
        AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1)) :=
      isReduced_of_injective e.symm e.symm.injective
    exact isReduced_pi_component (R := fun q : (maximalIdeal A).primesOver S =>
      AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1)) q'
  · intro h
    have : ∀ q : (maximalIdeal A).primesOver S,
        IsReduced (AdicCompletion (maximalIdeal (Localization.AtPrime q.1))
          (Localization.AtPrime q.1)) := fun q => h q.1
    exact isReduced_of_injective e e.injective

/-- If every formal fibre of a Noetherian local ring `A` is geometrically reduced, then
`S ⊗[A] Â` is reduced for every finite `A`-algebra `S` that is a domain. -/
public lemma isReduced_tensor_completion_of_formalFibers
    {A : Type u} {S : Type v} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing S] [IsDomain S] [Algebra A S] [Module.Finite A S]
    (hA : ∀ q : PrimeSpectrum A,
      Algebra.IsGeometricallyReduced q.asIdeal.ResidueField
        (q.asIdeal.Fiber (AdicCompletion (maximalIdeal A) A))) :
    IsReduced (S ⊗[A] AdicCompletion (maximalIdeal A) A) := by
  let q : Ideal S := ⊥
  let p := q.under A
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : Module.Finite p.ResidueField q.ResidueField :=
    Algebra.WeaklyQuasiFiniteAt.finite_residueField p q
  have : Algebra.IsGeometricallyReduced p.ResidueField
      (p.Fiber (AdicCompletion (maximalIdeal A) A)) := hA ⟨p, inferInstance⟩
  have : IsReduced (q.ResidueField ⊗[p.ResidueField]
      (p.Fiber (AdicCompletion (maximalIdeal A) A))) := inferInstance
  have : IsReduced (q.ResidueField ⊗[A] AdicCompletion (maximalIdeal A) A) :=
    let e := Algebra.TensorProduct.cancelBaseChange A p.ResidueField q.ResidueField
      q.ResidueField (AdicCompletion (maximalIdeal A) A)
    isReduced_of_injective e.symm e.symm.injective
  have : Module.Flat A (AdicCompletion (maximalIdeal A) A) :=
    AdicCompletion.flat_of_isNoetherian _
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S q.ResidueField) (AlgHom.id A _))
    (Module.Flat.rTensor_preserves_injective_linearMap _
      (IsFractionRing.injective S q.ResidueField))

/-- A Noetherian local ring whose formal fibres are geometrically reduced is a Nagata ring. -/
@[ega "IV 7.6.4" "Implication a″ ⇒ b"]
private theorem isNagataRing_of_geometricallyReduced_formalFibers
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : ∀ q : PrimeSpectrum A,
      Algebra.IsGeometricallyReduced q.asIdeal.ResidueField
        (q.asIdeal.Fiber (AdicCompletion (maximalIdeal A) A))) :
    IsNagataRing A := by
  refine ((isNagataRing_tfae_isAnalyticallyUnramified.{u, u, u} (R := A)).out 1 2).mpr ?_
  intro S _ _ _ _ q _
  exact isReduced_tensor_completion_iff.mp
    (isReduced_tensor_completion_of_formalFibers hA) q


open CategoryTheory CategoryTheory.Limits

/-- Geometrically normal fibres remain normal after arbitrary base change. -/
private theorem isNormalRing_fiber_tensorProduct
    (R B C : Type u) [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C]
    (hf : ∀ p : PrimeSpectrum R,
      Algebra.IsGeometricallyNormal p.asIdeal.ResidueField (p.asIdeal.Fiber B))
    (q : Ideal C) [q.IsPrime] : IsNormalRing (q.Fiber (C ⊗[R] B)) := by
  let p : PrimeSpectrum R := ⟨q.comap (algebraMap R C), inferInstance⟩
  let K := q.ResidueField
  let : Algebra p.asIdeal.ResidueField K :=
    (Ideal.ResidueField.map p.asIdeal q (algebraMap R C) rfl).toAlgebra
  let : IsScalarTower R p.asIdeal.ResidueField K :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (Ideal.ResidueField.map_algebraMap p.asIdeal q (algebraMap R C) rfl r).symm
  let e := (Algebra.TensorProduct.cancelBaseChange R C K K B).toRingEquiv.trans
    (Algebra.TensorProduct.cancelBaseChange R p.asIdeal.ResidueField K K B).symm.toRingEquiv
  exact IsNormalRing.congr e.symm ((hf p).isNormalRing_tensorProduct K)

/-- Normality ascends under base change by a flat map with geometrically normal fibres. -/
private theorem isNormalRing_tensorProduct_of_geometricallyNormal_fibers
    (R B C : Type u) [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] [Module.Flat R B]
    [IsNoetherianRing C] [IsNoetherianRing (C ⊗[R] B)]
    (hC : IsNormalRing C)
    (hf : ∀ p : PrimeSpectrum R,
      Algebra.IsGeometricallyNormal p.asIdeal.ResidueField (p.asIdeal.Fiber B)) :
    IsNormalRing (C ⊗[R] B) :=
  isNormalRing_of_flat_of_isNormalRing_fiber hC (isNormalRing_fiber_tensorProduct R B C hf)

/-- The normalization of the reduction of a Nagata ring is finite. -/
private theorem finite_integralClosure_fractionRing_reduction
    (R : Type u) [CommRing R] (hR : IsNagataRing R) :
    Module.Finite R (integralClosure R (FractionRing (R ⧸ nilradical R))) := by
  let : IsNoetherianRing R := hR.1
  let : IsReduced (R ⧸ nilradical R) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
  exact IsIntegralClosure.finite_of_essFiniteType_of_isReduced
    (S := FractionRing (R ⧸ nilradical R)) hR.2

/-- Mutually unique incidence identifies two sets. -/
private theorem encard_eq_of_unique_relation {α : Type u} {β : Type v}
    (s : Set α) (t : Set β) (r : α → β → Prop)
    (hs : ∀ a ∈ s, ∃! b, b ∈ t ∧ r a b)
    (ht : ∀ b ∈ t, ∃! a, a ∈ s ∧ r a b) : s.encard = t.encard := by
  classical
  choose f hf using fun a : s => (hs a.1 a.2).exists
  let F : s → t := fun a => ⟨f a, (hf a).1⟩
  apply ENat.card_congr (Equiv.ofBijective F ?_)
  constructor
  · intro a b hab
    apply Subtype.ext
    have he := congrArg Subtype.val hab
    obtain ⟨c, hc, hcu⟩ := ht (f a) (hf a).1
    exact (hcu a.1 ⟨a.2, (hf a).2⟩).trans
      (hcu b.1 ⟨b.2, by change f a = f b at he; simpa only [he] using (hf b).2⟩).symm
  · intro b
    obtain ⟨a, ha, _⟩ := ht b.1 b.2
    refine ⟨⟨a, ha.1⟩, Subtype.ext ?_⟩
    obtain ⟨c, hc, hcu⟩ := hs a ha.1
    exact (hcu _ (hf ⟨a, ha.1⟩)).trans (hcu b.1 ⟨b.2, ha.2⟩).symm

/-- In a normal integral algebra over a henselian local ring, minimal and maximal primes
are in bijection by containment. -/
private theorem encard_minimalPrimes_eq_maximalIdeals
    (R : Type u) (B : Type v) [CommRing R] [HenselianLocalRing R]
    [CommRing B] [Algebra R B] [Algebra.IsIntegral R B] (hB : IsNormalRing B) :
    (minimalPrimes B).encard = {m : Ideal B | m.IsMaximal}.encard := by
  exact encard_eq_of_unique_relation _ _ (fun q m => q ≤ m)
    (fun q hq ↦ existsUnique_maximal_of_integral_henselian R B q hq.isPrime)
    (existsUnique_minimalPrime_le_of_isNormalRing B hB)

private theorem encard_eq_of_bijOn {α : Type u} {β : Type v}
    {s : Set α} {t : Set β} {f : α → β} (h : Set.BijOn f s t) :
    s.encard = t.encard :=
  Set.encard_congr (h.equiv f)

private theorem encard_maximalIdeals_congr {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (e : R ≃+* S) :
    {p : Ideal R | p.IsMaximal}.encard = {q : Ideal S | q.IsMaximal}.encard := by
  symm
  apply encard_eq_of_bijOn (f := Ideal.comap e.toRingHom)
  refine ⟨?_, (Ideal.comap_injective_of_surjective _ e.surjective).injOn, ?_⟩
  · intro q hq
    let : q.IsMaximal := hq
    exact Ideal.comap_isMaximal_of_surjective _ e.surjective
  · intro p hp
    let : p.IsMaximal := hp
    refine ⟨p.comap e.symm.toRingHom,
      Ideal.comap_isMaximal_of_surjective _ e.symm.surjective, ?_⟩
    rw [Ideal.comap_comap]
    convert Ideal.comap_id p using 2
    ext x
    exact e.symm_apply_apply x

private theorem residueFieldMap_bijective_residue (R : Type u)
    [CommRing R] [IsLocalRing R] :
    Function.Bijective (ResidueField.map (residue R)) := by
  refine ⟨RingHom.injective _, ?_⟩
  intro x
  obtain ⟨y, rfl⟩ := residue_surjective x
  obtain ⟨r, rfl⟩ := residue_surjective y
  exact ⟨residue R r, ResidueField.map_residue _ r⟩

/-- Base change of `B ⊗[R] N` along `B → C` is the base change of `N` along `R → C`. -/
private noncomputable def tensorTensorRingEquiv
    (R B C N : Type*) [CommRing R] [CommRing B] [CommRing C] [CommRing N]
    [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C] [Algebra R N] :
    (B ⊗[R] N) ⊗[B] C ≃+* N ⊗[R] C :=
  (Algebra.TensorProduct.comm B (B ⊗[R] N) C).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange R B C C N).toRingEquiv.trans
      (Algebra.TensorProduct.comm R C N).toRingEquiv)

/-- Maximal ideals of an integral algebra over a local ring can be counted in the closed fibre. -/
private theorem encard_maximalIdeals_eq_closedFiber
    (R : Type u) (C : Type v) (N : Type w)
    [CommRing R] [CommRing C] [IsLocalRing C] [CommRing N]
    [Algebra R C] [Algebra R N] [Algebra.IsIntegral R N] :
    {p : Ideal (N ⊗[R] C) | p.IsMaximal}.encard =
      {q : Ideal (N ⊗[R] ResidueField C) | q.IsMaximal}.encard := by
  let : Algebra C (C ⊗[R] N) := inferInstance
  let : Algebra.IsIntegral C (C ⊗[R] N) := Algebra.IsIntegral.tensorProduct R C N
  let : IsLocalHom (algebraMap C (ResidueField C)) := by
    rw [ResidueField.algebraMap_eq]
    infer_instance
  have h := encard_eq_of_bijOn
    (bijOn_maximalIdeals_tensorProduct C (ResidueField C) (C ⊗[R] N)
      (by simpa only [ResidueField.algebraMap_eq] using residueFieldMap_bijective_residue C))
  exact (encard_maximalIdeals_congr (Algebra.TensorProduct.comm R N C).toRingEquiv).trans
    (h.symm.trans (encard_maximalIdeals_congr (tensorTensorRingEquiv R C _ N)))

/-- Branches are counted by the closed fibre of a normal base change of the normalization. -/
private theorem encard_minimalPrimes_eq_normalization_closedFiber
    (R C : Type u) [CommRing R] [CommRing C] [HenselianLocalRing C]
    [Algebra R C] [Module.Flat R C]
    (hN : IsNormalRing (integralClosure R (FractionRing (R ⧸ nilradical R)) ⊗[R] C)) :
    (minimalPrimes C).encard =
      {q : Ideal (integralClosure R (FractionRing (R ⧸ nilradical R)) ⊗[R]
        ResidueField C) | q.IsMaximal}.encard := by
  let N := integralClosure R (FractionRing (R ⧸ nilradical R))
  let : Algebra C (N ⊗[R] C) := Algebra.TensorProduct.rightAlgebra
  let : Algebra.IsIntegral C (N ⊗[R] C) := integral_tensorProduct_right R N C
  exact (encard_eq_of_bijOn
    (bijOn_minimalPrimes_integralClosure_tensorProduct R C)).symm.trans
      ((encard_minimalPrimes_eq_maximalIdeals C (N ⊗[R] C) hN).trans
        (encard_maximalIdeals_eq_closedFiber R C N))

/-- A residue-field equivalence compares the branch counts of normal base changes. -/
private theorem encard_minimalPrimes_eq_of_normalization_of_residueFieldEquiv
    (R C D : Type u) [CommRing R] [CommRing C] [CommRing D]
    [HenselianLocalRing C] [HenselianLocalRing D]
    [Algebra R C] [Algebra R D] [Module.Flat R C] [Module.Flat R D]
    (hC : IsNormalRing (integralClosure R (FractionRing (R ⧸ nilradical R)) ⊗[R] C))
    (hD : IsNormalRing (integralClosure R (FractionRing (R ⧸ nilradical R)) ⊗[R] D))
    (e : ResidueField C ≃ₐ[R] ResidueField D) :
    (minimalPrimes C).encard = (minimalPrimes D).encard := by
  rw [encard_minimalPrimes_eq_normalization_closedFiber R C hC,
    encard_minimalPrimes_eq_normalization_closedFiber R D hD]
  let N := integralClosure R (FractionRing (R ⧸ nilradical R))
  exact encard_maximalIdeals_congr (R := N ⊗[R] ResidueField C)
    (S := N ⊗[R] ResidueField D)
    (Algebra.TensorProduct.congr (AlgEquiv.refl : N ≃ₐ[R] N) e).toRingEquiv

/-- Normality is preserved by a henselization after arbitrary base change. -/
@[ega "IV 18.6.9" "(i), special case"]
private theorem isNormalRing_tensorProduct_henselization
    (R N C : Type u) [CommRing R] [IsLocalRing R] [CommRing N] [Algebra R N]
    [CommRing C] [IsLocalRing C] [Algebra R C]
    (L : Type v) [Field L] [Algebra (ResidueField R) L] [IsHenselization R L C]
    (hN : IsNormalRing N) : IsNormalRing (N ⊗[R] C) :=
  isNormalRing_tensorProduct_of_ind_etale N hN
    (IsHenselization.ind_etale_of_universe_le.{u, v, u} (R := R) (L := L) (Rh := C))

/-- Normality of a base change followed by a henselization. -/
@[ega "IV 18.6.9" "(i), special case"]
private theorem isNormalRing_tensorProduct_henselization_tower
    (R B N C : Type u) [CommRing R] [CommRing B] [IsLocalRing B]
    [CommRing N] [CommRing C] [IsLocalRing C]
    [Algebra R B] [Algebra R N] [Algebra B C] [Algebra R C] [IsScalarTower R B C]
    (L : Type v) [Field L] [Algebra (ResidueField B) L] [IsHenselization B L C]
    (hN : IsNormalRing (N ⊗[R] B)) : IsNormalRing (N ⊗[R] C) :=
  IsNormalRing.congr (tensorTensorRingEquiv R B C N)
    (isNormalRing_tensorProduct_henselization B (B ⊗[R] N) C L
      (IsNormalRing.congr (Algebra.TensorProduct.comm R N B).toRingEquiv hN))

/-- The normalization stays normal after completion. -/
private theorem isNormalRing_normalization_tensorProduct_completion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : IsNagataRing A)
    (hf : ∀ p : PrimeSpectrum A, Algebra.IsGeometricallyNormal p.asIdeal.ResidueField
      (p.asIdeal.Fiber (AdicCompletion (maximalIdeal A) A))) :
    IsNormalRing (integralClosure A (FractionRing (A ⧸ nilradical A)) ⊗[A]
      AdicCompletion (maximalIdeal A) A) := by
  let N := integralClosure A (FractionRing (A ⧸ nilradical A))
  let B := AdicCompletion (maximalIdeal A) A
  let : Module.Finite A N := finite_integralClosure_fractionRing_reduction A hA
  let : IsNoetherianRing N := IsNoetherianRing.of_finite A N
  let : IsNoetherianRing (B ⊗[A] N) := Algebra.FiniteType.isNoetherianRing B _
  let : IsNoetherianRing (N ⊗[A] B) :=
    isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm A B N).toRingEquiv
  exact isNormalRing_tensorProduct_of_geometricallyNormal_fibers A B N
    (isNormalRing_integralClosure_fractionRing_reduction A
      (minimalPrimes.finite_of_isNoetherianRing A)) hf

private noncomputable def residueFieldAlgEquiv_henselization
    (R C : Type u) [CommRing R] [IsLocalRing R] [CommRing C] [IsLocalRing C]
    [Algebra R C] [IsHenselization R (ResidueField R) C] :
    ResidueField R ≃ₐ[R] ResidueField C := by
  let h := IsHenselization.exists_residueFieldEquiv
    (R := R) (L := ResidueField R) (Rh := C)
  refine { h.choose with commutes' := fun r => ?_ }
  rw [IsScalarTower.algebraMap_apply R C (ResidueField C)]
  exact h.choose_spec r

noncomputable def residueFieldAlgEquiv_completion
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    ResidueField R ≃ₐ[R] ResidueField (AdicCompletion (maximalIdeal R) R) :=
  { RingEquiv.ofBijective (ResidueField.map
      (algebraMap R (AdicCompletion (maximalIdeal R) R)))
      (AdicCompletion.residueField_map_bijective R) with
    commutes' := fun r => ResidueField.map_residue _ r }

/-- Compatible residue fields of strict henselizations are isomorphic over the original ring. -/
private theorem nonempty_residueFieldAlgEquiv_strictHenselizations
    (R B C D : Type u) [CommRing R] [IsLocalRing R] [CommRing B] [IsLocalRing B]
    [Algebra R B] [CommRing C] [IsLocalRing C] [Algebra R C]
    [CommRing D] [IsLocalRing D] [Algebra B D] [Algebra R D] [IsScalarTower R B D]
    (L : Type v) [Field L] [Algebra (ResidueField R) L] [IsSepClosure (ResidueField R) L]
    (M : Type w) [Field M] [Algebra (ResidueField B) M] [IsSepClosure (ResidueField B) M]
    [IsHenselization R L C] [IsHenselization B M D]
    (e : ResidueField R ≃ₐ[R] ResidueField B) :
    Nonempty (ResidueField C ≃ₐ[R] ResidueField D) := by
  let : Algebra (ResidueField R) (ResidueField B) := e.toRingHom.toAlgebra
  let eBase : ResidueField R ≃ₐ[ResidueField R] ResidueField B :=
    { e.toRingEquiv with commutes' := fun _ => rfl }
  let : Algebra.IsSeparable (ResidueField R) (ResidueField B) :=
    AlgEquiv.Algebra.isSeparable eBase
  let : Algebra (ResidueField R) M :=
    ((algebraMap (ResidueField B) M).comp e.toRingHom).toAlgebra
  let : IsScalarTower (ResidueField R) (ResidueField B) M :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsSepClosure (ResidueField R) M :=
    ⟨IsSepClosure.sep_closed (ResidueField B),
      Algebra.IsSeparable.trans (ResidueField R) (ResidueField B) M⟩
  let E := IsSepClosure.equiv (ResidueField R) L M
  obtain ⟨eC, heC⟩ := IsHenselization.exists_residueFieldEquiv (R := R) (L := L) (Rh := C)
  obtain ⟨eD, heD⟩ := IsHenselization.exists_residueFieldEquiv (R := B) (L := M) (Rh := D)
  refine ⟨{ eC.symm.trans (E.toRingEquiv.trans eD) with commutes' := ?_ }⟩
  intro r
  show eD (E (eC.symm (residue C (algebraMap R C r)))) =
    residue D (algebraMap R D r)
  rw [← heC r, eC.symm_apply_apply, E.commutes]
  show eD (algebraMap (ResidueField B) M (e (residue R r))) = _
  rw [show e (residue R r) = residue B (algebraMap R B r) from e.commutes r,
    heD, ← IsScalarTower.algebraMap_apply R B D]

@[ega "IV 5.13.5"]
private theorem isReduced_of_isNormalRing (R : Type*) [CommRing R]
    (hR : IsNormalRing R) : IsReduced R := by
  apply isReduced_ofLocalizationMaximal
  intro J hJ
  let : J.IsPrime := hJ.isPrime
  let : IsDomain (Localization.AtPrime J) := (hR J).1
  exact isReduced_of_noZeroDivisors

/-- A Noetherian local ring whose formal fibres are geometrically normal is Nagata, and its
ordinary and geometric branch counts agree with those of its completion. -/
@[stacks 0C2E, ega "IV 7.6.1" "A' finite over A", ega "IV 7.8.3" "(vi) local case"]
theorem isNagataRing_and_numberOfBranches_and_numberOfGeometricBranches_eq_adicCompletion
    (A Ah AhatH Ash AhatSh : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsHenselization A (ResidueField A) Ah]
    [CommRing AhatH] [IsLocalRing AhatH]
    [Algebra (AdicCompletion (maximalIdeal A) A) AhatH]
    [IsHenselization (AdicCompletion (maximalIdeal A) A)
      (ResidueField (AdicCompletion (maximalIdeal A) A)) AhatH]
    (ksep : Type v) [Field ksep] [Algebra (ResidueField A) ksep]
    [IsSepClosure (ResidueField A) ksep]
    [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash] [IsHenselization A ksep Ash]
    (khatsep : Type w) [Field khatsep]
    [Algebra (ResidueField (AdicCompletion (maximalIdeal A) A)) khatsep]
    [IsSepClosure (ResidueField (AdicCompletion (maximalIdeal A) A)) khatsep]
    [CommRing AhatSh] [IsLocalRing AhatSh]
    [Algebra (AdicCompletion (maximalIdeal A) A) AhatSh]
    [IsHenselization (AdicCompletion (maximalIdeal A) A) khatsep AhatSh]
    (hformal : ∀ q : PrimeSpectrum A,
      Algebra.IsGeometricallyNormal q.asIdeal.ResidueField
        (q.asIdeal.Fiber (AdicCompletion (maximalIdeal A) A))) :
    IsNagataRing A ∧
      numberOfBranches A Ah =
        numberOfBranches (AdicCompletion (maximalIdeal A) A) AhatH ∧
      numberOfGeometricBranches A ksep Ash =
        numberOfGeometricBranches
          (AdicCompletion (maximalIdeal A) A) khatsep AhatSh := by
  have hNagata : IsNagataRing A :=
    isNagataRing_of_geometricallyReduced_formalFibers A fun q => by
      rw [Algebra.isGeometricallyReduced_field_iff]
      exact isReduced_of_isNormalRing _
        ((hformal q).isNormalRing_tensorProduct (AlgebraicClosure q.asIdeal.ResidueField))
  let B := AdicCompletion (maximalIdeal A) A
  let N := integralClosure A (FractionRing (A ⧸ nilradical A))
  let : Algebra A AhatH := ((algebraMap B AhatH).comp (algebraMap A B)).toAlgebra
  let : IsScalarTower A B AhatH := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A AhatSh := ((algebraMap B AhatSh).comp (algebraMap A B)).toAlgebra
  let : IsScalarTower A B AhatSh := IsScalarTower.of_algebraMap_eq' rfl
  let : HenselianLocalRing Ah := IsHenselization.henselian (R := A) (L := ResidueField A)
  let : HenselianLocalRing Ash := IsHenselization.henselian (R := A) (L := ksep)
  let : HenselianLocalRing AhatH := IsHenselization.henselian (R := B) (L := ResidueField B)
  let : HenselianLocalRing AhatSh := IsHenselization.henselian (R := B) (L := khatsep)
  let : Module.Flat A Ah := flat_of_isHenselization (L := ResidueField A)
  let : Module.Flat A Ash := flat_of_isHenselization (L := ksep)
  let : Module.Flat B AhatH := flat_of_isHenselization (L := ResidueField B)
  let : Module.Flat B AhatSh := flat_of_isHenselization (L := khatsep)
  let : Module.Flat A AhatH := Module.Flat.trans A B AhatH
  let : Module.Flat A AhatSh := Module.Flat.trans A B AhatSh
  have hN : IsNormalRing N := isNormalRing_integralClosure_fractionRing_reduction A
    (minimalPrimes.finite_of_isNoetherianRing A)
  have hNB : IsNormalRing (N ⊗[A] B) :=
    isNormalRing_normalization_tensorProduct_completion A hNagata hformal
  let eB := residueFieldAlgEquiv_completion A
  refine ⟨hNagata, ?_, ?_⟩
  · exact encard_minimalPrimes_eq_of_normalization_of_residueFieldEquiv A Ah AhatH
      (isNormalRing_tensorProduct_henselization A N Ah (ResidueField A) hN)
      (isNormalRing_tensorProduct_henselization_tower A B N AhatH (ResidueField B) hNB)
      ((residueFieldAlgEquiv_henselization A Ah).symm.trans
        (eB.trans ((residueFieldAlgEquiv_henselization B AhatH).restrictScalars A)))
  · obtain ⟨e⟩ := nonempty_residueFieldAlgEquiv_strictHenselizations
      A B Ash AhatSh ksep khatsep eB
    exact encard_minimalPrimes_eq_of_normalization_of_residueFieldEquiv A Ash AhatSh
      (isNormalRing_tensorProduct_henselization A N Ash ksep hN)
      (isNormalRing_tensorProduct_henselization_tower A B N AhatSh khatsep hNB) e

end
