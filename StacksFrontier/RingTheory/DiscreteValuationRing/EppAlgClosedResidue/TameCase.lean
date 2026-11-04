module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.NumberTheory.Cyclotomic.OneAddPow
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar
public import StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier
public import StacksFrontier.RingTheory.DiscreteValuationRing.BaseChangeClosure
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSolution
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppMixedReentry
public import StacksFrontier.RingTheory.DiscreteValuationRing.ExtensionLevel
public import StacksFrontier.RingTheory.DiscreteValuationRing.FormallySmoothExtension
public import StacksFrontier.RingTheory.DiscreteValuationRing.Galois
public import StacksFrontier.RingTheory.DiscreteValuationRing.Inertia
public import StacksFrontier.RingTheory.DiscreteValuationRing.IntegralClosureBaseChangeConstruction
public import StacksFrontier.RingTheory.DiscreteValuationRing.Kummer
public import StacksFrontier.RingTheory.DiscreteValuationRing.PurelyInseparable
public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationIndex
public import StacksFrontier.RingTheory.DiscreteValuationRing.ReducedTensorTower
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution
public import StacksFrontier.RingTheory.DiscreteValuationRing.Unramified
public import StacksFrontier.RingTheory.DiscreteValuationRing.WeakSolution
public import StacksFrontier.RingTheory.FormallySmooth.Topological
public import StacksFrontier.RingTheory.Nagata.CompleteLocalRing
public import StacksFrontier.RingTheory.IntegralClosure.Pi
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.CompleteIntegralClosure
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.SolvableInertia

open Stacks.DegreePExtensionLevel
open Stacks.DiscreteValuationRing.EppLevelInduction

/-!
# Eliminating ramification: factors of base changes and the tame case

Products of base changes and the ramification indices of their factors, weak solutions from adic
formal smoothness and from a perfect residue field, the tame and residue-characteristic-zero case,
and algebraic closedness of the residue fields of finite extensions.

Part of `StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue`;
see there for the overview and references.
-/

@[expose] public section

universe uA uB uC uK uL uM

namespace IsDiscreteValuationRing

open scoped TensorProduct

universe uK₁

attribute [local instance]
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingA₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraKL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraLL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraBL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraAA₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraA₁K₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraBB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraB₁L₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraAB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraA₁B₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerKLL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerBLL₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerAA₁K₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerBB₁L₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerABB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerAA₁B₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isIntegralClosureA₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isIntegralClosureB₁

attribute [local instance]
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraK₁L₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.isScalarTowerKK₁L₁

universe uF uD₁ uD₂ uD₃

/-- Projection onto a product component is flat, as a localization at an idempotent. -/
private theorem flat_pi_eval (ι : Type*) (S : ι → Type*) [∀ i, CommRing (S i)] (i : ι) :
    letI : Algebra (∀ i, S i) (S i) := (Pi.evalRingHom S i).toAlgebra
    Module.Flat (∀ i, S i) (S i) := by
  classical
  let : Algebra (∀ i, S i) (S i) := (Pi.evalRingHom S i).toAlgebra
  let : IsLocalization.Away (Pi.single i 1 : ∀ i, S i) (S i) := by
    apply IsLocalization.away_of_isIdempotentElem
    · simp [IsIdempotentElem, ← Pi.single_mul_left]
    · exact RingHom.ker_evalRingHom S i
    · exact (Pi.evalRingHom S i).surjective
  exact IsLocalization.flat (S i) (Submonoid.powers (Pi.single i 1))

/-- A field-factor decomposition induces the canonical product decomposition of the
upper integral closure in a base-change package. -/
@[ega "II 6.3.6" "special case"]
private noncomputable def integralClosureBaseChangePiEquiv
    (A B K L K₁ : Type*)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁]
    (D : IsDiscreteValuationRing.IntegralClosureBaseChange A B K L K₁)
    {ι : Type*} [Finite ι] (E : ι → Type*) [∀ i, CommRing (E i)]
    [∀ i, Algebra L (E i)] [∀ i, Algebra B (E i)] [∀ i, IsScalarTower B L (E i)]
    (e : D.L₁ ≃ₐ[L] ∀ i, E i) :
    D.B₁ ≃ₐ[B] ∀ i, integralClosure B (E i) :=
  (IsIntegralClosure.equiv B D.B₁ D.L₁ (integralClosure B D.L₁)).trans
    ((e.restrictScalars B).mapIntegralClosure.trans (integralClosurePiEquiv B E))

/-- The product decomposition of integral closures commutes with the field embeddings. -/
private lemma integralClosureBaseChangePiEquiv_apply
    (A B K L K₁ : Type*)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁]
    (D : IsDiscreteValuationRing.IntegralClosureBaseChange A B K L K₁)
    {ι : Type*} [Finite ι] (E : ι → Type*) [∀ i, CommRing (E i)]
    [∀ i, Algebra L (E i)] [∀ i, Algebra B (E i)] [∀ i, IsScalarTower B L (E i)]
    (e : D.L₁ ≃ₐ[L] ∀ i, E i) (x : D.B₁) (i : ι) :
    (integralClosureBaseChangePiEquiv A B K L K₁ D E e x i : E i) =
      e (algebraMap D.B₁ D.L₁ x) i := by
  change e ((IsIntegralClosure.equiv B D.B₁ D.L₁ (integralClosure B D.L₁) x :
    integralClosure B D.L₁) : D.L₁) i = _
  rw [show ((IsIntegralClosure.equiv B D.B₁ D.L₁ (integralClosure B D.L₁) x :
    integralClosure B D.L₁) : D.L₁) = algebraMap D.B₁ D.L₁ x from
    IsIntegralClosure.algebraMap_equiv B D.B₁ D.L₁ (integralClosure B D.L₁) x]

/-- The factor maps agree with the map from the new base integral closure. -/
private lemma integralClosureBaseChangePiEquiv_base
    (A B K L K₁ : Type*)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁]
    (D : IsDiscreteValuationRing.IntegralClosureBaseChange A B K L K₁)
    {ι : Type*} [Finite ι] (E : ι → Type*) [∀ i, CommRing (E i)]
    [∀ i, Algebra L (E i)] [∀ i, Algebra B (E i)] [∀ i, IsScalarTower B L (E i)]
    [∀ i, Algebra A (E i)] [∀ i, Algebra K₁ (E i)]
    [∀ i, IsScalarTower A B (E i)] [∀ i, IsScalarTower A K₁ (E i)]
    (e : D.L₁ ≃ₐ[L] ∀ i, E i)
    (he : ∀ i x, e (algebraMap K₁ D.L₁ x) i = algebraMap K₁ (E i) x)
    (x : D.A₁) (i : ι) :
    integralClosureBaseChangePiEquiv A B K L K₁ D E e
        (algebraMap D.A₁ D.B₁ x) i =
      mapIntegralClosureOfTower A B K₁ (E i)
        (IsIntegralClosure.equiv A D.A₁ K₁ (integralClosure A K₁) x) := by
  apply Subtype.ext
  rw [integralClosureBaseChangePiEquiv_apply, D.ringSquare, he,
    mapIntegralClosureOfTower_apply]
  congr 1
  exact (IsIntegralClosure.algebraMap_equiv A D.A₁ K₁ (integralClosure A K₁) x).symm
/-- Ramification indices are unchanged by a surjective change of the base ring. -/
private theorem ramificationIdx_eq_of_surjective_base
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (hRS : Function.Surjective (algebraMap R S)) (q : Ideal T) [q.IsPrime] :
    q.ramificationIdx R = q.ramificationIdx S := by
  have hunder : q.under R = (q.under S).comap (algebraMap R S) := by
    rw [Ideal.under, Ideal.under, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  rw [Ideal.ramificationIdx_def, Ideal.ramificationIdx_def,
    IsScalarTower.algebraMap_eq R S (Localization.AtPrime q), ← Ideal.map_map,
    hunder, Ideal.map_comap_of_surjective _ hRS]

/-- A flat quotient does not change ramification at the primes it retains. -/
private theorem ramificationIdx_comap_of_surjective_of_flat
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.Flat S T] (hST : Function.Surjective (algebraMap S T))
    (q : Ideal T) [q.IsPrime] :
    (q.under S).ramificationIdx R = q.ramificationIdx R := by
  have hidx : q.ramificationIdx S = 1 := ramificationIdx_eq_one_of_map_under_eq S T q
    (Ideal.map_comap_of_surjective _ hST q)
  simpa only [hidx, mul_one] using
    (Ideal.ramificationIdx_tower (R := R) (q.under S) q).symm

/-- Ramification indices on a finite product can be computed in each component. -/
private theorem ramificationIdx_comap_pi_eval
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type*} (T : ι → Type*) [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)]
    (e : S ≃ₐ[R] ∀ i, T i) (i : ι) (q : Ideal (T i)) [q.IsPrime] :
    (q.comap ((Pi.evalAlgHom R T i).comp e.toAlgHom).toRingHom).ramificationIdx R =
      q.ramificationIdx R := by
  let f := (Pi.evalAlgHom R T i).comp e.toAlgHom
  let : Algebra S (T i) := f.toAlgebra
  let : IsScalarTower R S (T i) := IsScalarTower.of_algHom f
  let : Module.Flat S (T i) :=
    (RingHom.Flat.of_bijective e.bijective).comp (flat_pi_eval ι T i)
  exact ramificationIdx_comap_of_surjective_of_flat R S (T i)
    ((Pi.evalRingHom T i).surjective.comp e.surjective) q

/-- A maximal ideal in a finite product is the inverse image of a maximal ideal
of one factor, also after presenting the product by an algebra equivalence. -/
private theorem exists_maximal_comap_pi_eval
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type*} [Finite ι] (T : ι → Type*)
    [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)]
    (e : S ≃ₐ[R] ∀ i, T i) (p : Ideal S) (hp : p.IsMaximal) :
    ∃ (i : ι) (q : Ideal (T i)), q.IsMaximal ∧
      q.comap ((Pi.evalAlgHom R T i).comp e.toAlgHom).toRingHom = p := by
  let : p.IsMaximal := hp
  let p' := p.comap e.symm.toRingHom
  have hp' : p'.IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq ⟨p', hp'.isPrime⟩
  have hq' : q.asIdeal.comap (Pi.evalRingHom T i) = p' :=
    congrArg PrimeSpectrum.asIdeal hq
  have hqm : q.asIdeal.IsMaximal := by
    have h := Ideal.map_eq_top_or_isMaximal_of_surjective (Pi.evalRingHom T i)
      (Pi.evalRingHom T i).surjective (hq'.symm ▸ hp')
    rw [Ideal.map_comap_of_surjective _ (Pi.evalRingHom T i).surjective] at h
    exact h.resolve_left q.2.ne_top
  refine ⟨i, q.asIdeal, hqm, ?_⟩
  change (q.asIdeal.comap (Pi.evalRingHom T i)).comap e.toRingHom = p
  rw [hq']
  ext x
  change e.symm (e x) ∈ p ↔ x ∈ p
  rw [AlgEquiv.symm_apply_apply]

/-- Ramification index one can be checked on all components of a finite product. -/
private theorem forall_ramificationIdx_eq_one_iff_pi
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type*} [Finite ι] (T : ι → Type*)
    [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)]
    (e : S ≃ₐ[R] ∀ i, T i) :
    (∀ p : Ideal S, p.IsMaximal → p.ramificationIdx R = 1) ↔
      ∀ (i : ι) (q : Ideal (T i)), q.IsMaximal → q.ramificationIdx R = 1 := by
  constructor
  · intro h i q hq
    let : q.IsMaximal := hq
    have hsurj := (Pi.evalRingHom T i).surjective.comp e.surjective
    have hq' : (q.comap ((Pi.evalAlgHom R T i).comp e.toAlgHom).toRingHom).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ hsurj
    have hi := h _ hq'
    rwa [ramificationIdx_comap_pi_eval R S T e i q] at hi
  · intro h p hp
    obtain ⟨i, q, hq, rfl⟩ := exists_maximal_comap_pi_eval R S T e p hp
    let : q.IsMaximal := hq
    exact (ramificationIdx_comap_pi_eval R S T e i q).trans (h i q hq)

/-- Weak solutions are the same as ramification index one on the integral closures of all
field factors. -/
private theorem isWeakSolution_iff_forall_factor
    (A B K L K₁ : Type*)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁]
    (D : IsDiscreteValuationRing.IntegralClosureBaseChange A B K L K₁)
    {ι : Type*} [Finite ι] (E : ι → Type*) [∀ i, CommRing (E i)]
    [∀ i, Algebra L (E i)] [∀ i, Algebra B (E i)] [∀ i, IsScalarTower B L (E i)]
    [∀ i, Algebra A (E i)] [∀ i, Algebra K₁ (E i)]
    [∀ i, IsScalarTower A B (E i)] [∀ i, IsScalarTower A K₁ (E i)]
    (e : D.L₁ ≃ₐ[L] ∀ i, E i)
    (he : ∀ i x, e (algebraMap K₁ D.L₁ x) i = algebraMap K₁ (E i) x) :
    D.IsWeakSolution ↔ ∀ i,
      letI : Algebra (integralClosure A K₁) (integralClosure B (E i)) :=
        (mapIntegralClosureOfTower A B K₁ (E i)).toRingHom.toAlgebra
      ∀ q : Ideal (integralClosure B (E i)), q.IsMaximal →
        q.ramificationIdx (integralClosure A K₁) = 1 := by
  let A₁ := integralClosure A K₁
  let T : ι → Type _ := fun i => integralClosure B (E i)
  let eA := IsIntegralClosure.equiv A D.A₁ K₁ A₁
  let eB := integralClosureBaseChangePiEquiv A B K L K₁ D E e
  let f := fun i => mapIntegralClosureOfTower A B K₁ (E i)
  let : ∀ i, Algebra A₁ (T i) := fun i => (f i).toRingHom.toAlgebra
  let : Algebra D.A₁ A₁ := eA.toRingHom.toAlgebra
  let : ∀ i, Algebra D.A₁ (T i) := fun i =>
    ((f i).toRingHom.comp eA.toRingHom).toAlgebra
  let : ∀ i, IsScalarTower D.A₁ A₁ (T i) := fun i =>
    IsScalarTower.of_algebraMap_eq' rfl
  let g : D.B₁ ≃ₐ[D.A₁] ∀ i, T i :=
    { __ := eB.toRingEquiv
      commutes' x := funext fun j =>
        integralClosureBaseChangePiEquiv_base A B K L K₁ D E e he x j }
  refine (forall_ramificationIdx_eq_one_iff_pi D.A₁ D.B₁ T g).trans (forall_congr' fun i => ?_)
  refine forall_congr' fun q => imp_congr_right fun hq => ?_
  let : q.IsMaximal := hq
  rw [ramificationIdx_eq_of_surjective_base D.A₁ A₁ (T i) eA.surjective q]

/-- A weak solution induces ramification index one on every field factor, with the
canonical map from the new base integral closure.

This is the half of the factor correspondence that goes *from* a package *to* the factors;
`isWeakSolution_of_forall_factorSolutions` goes the other way. -/
theorem isWeakSolution_factor
    (A B K L K₁ : Type*)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁]
    (D : IsDiscreteValuationRing.IntegralClosureBaseChange A B K L K₁)
    {ι : Type*} [Finite ι] (E : ι → Type*) [∀ i, CommRing (E i)]
    [∀ i, Algebra L (E i)] [∀ i, Algebra B (E i)] [∀ i, IsScalarTower B L (E i)]
    [∀ i, Algebra A (E i)] [∀ i, Algebra K₁ (E i)]
    [∀ i, IsScalarTower A B (E i)] [∀ i, IsScalarTower A K₁ (E i)]
    (e : D.L₁ ≃ₐ[L] ∀ i, E i)
    (he : ∀ i x, e (algebraMap K₁ D.L₁ x) i = algebraMap K₁ (E i) x)
    (hD : D.IsWeakSolution) (i : ι)
    (q : Ideal (integralClosure B (E i))) (hq : q.IsMaximal) :
    letI : Algebra (integralClosure A K₁) (integralClosure B (E i)) :=
      (mapIntegralClosureOfTower A B K₁ (E i)).toRingHom.toAlgebra
    q.ramificationIdx (integralClosure A K₁) = 1 := by
  exact (isWeakSolution_iff_forall_factor A B K L K₁ D E e he).mp hD i q hq


/-- Weak solutions assemble from the canonical integral closures of all field factors. -/
theorem isWeakSolution_of_factors
    (A B K L K₁ : Type*)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁]
    (D : IsDiscreteValuationRing.IntegralClosureBaseChange A B K L K₁)
    {ι : Type*} [Finite ι] (E : ι → Type*) [∀ i, CommRing (E i)]
    [∀ i, Algebra L (E i)] [∀ i, Algebra B (E i)] [∀ i, IsScalarTower B L (E i)]
    [∀ i, Algebra A (E i)] [∀ i, Algebra K₁ (E i)]
    [∀ i, IsScalarTower A B (E i)] [∀ i, IsScalarTower A K₁ (E i)]
    (e : D.L₁ ≃ₐ[L] ∀ i, E i)
    (he : ∀ i x, e (algebraMap K₁ D.L₁ x) i = algebraMap K₁ (E i) x)
    (hE : ∀ (i : ι),
      letI : Algebra (integralClosure A K₁) (integralClosure B (E i)) :=
        (mapIntegralClosureOfTower A B K₁ (E i)).toRingHom.toAlgebra
      ∀ q : Ideal (integralClosure B (E i)), q.IsMaximal →
        q.ramificationIdx (integralClosure A K₁) = 1) : D.IsWeakSolution := by
  exact (isWeakSolution_iff_forall_factor A B K L K₁ D E e he).mpr hE

universe u v

/-- Over a perfect residue field, weak unramifiedness of DVRs is adic formal smoothness. -/
private theorem formallySmooth_of_isWeaklyUnramified
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [IsDiscreteValuationRing.IsExtension A B]
    [PerfectField (IsLocalRing.ResidueField A)]
    (h : IsDiscreteValuationRing.IsWeaklyUnramified A B) :
    RingHom.FormallySmoothNAdic.{max u v} (algebraMap A B) (IsLocalRing.maximalIdeal B) :=
  (IsDiscreteValuationRing.formallySmooth_iff_weaklyUnramified_and_isSeparableExtension
    A B).mpr ⟨h, Algebra.isSeparableExtension_of_perfectField _ _⟩

/-- A map of localized DVRs of ramification index one computes the original prime's index. -/
private theorem ramificationIdx_eq_one_of_localized_map
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal S) [q.IsPrime]
    (φ : Localization.AtPrime (q.under R) →+* Localization.AtPrime q)
    (hφ : ∀ x : R, φ (algebraMap R _ x) = algebraMap S _ (algebraMap R S x))
    (hmax : (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R))).map φ =
      IsLocalRing.maximalIdeal (Localization.AtPrime q)) : q.ramificationIdx R = 1 := by
  have hcomp : algebraMap R (Localization.AtPrime q) =
      φ.comp (algebraMap R (Localization.AtPrime (q.under R))) :=
    RingHom.ext fun x => (hφ x).symm
  rw [Ideal.ramificationIdx_def, hcomp, ← Ideal.map_map,
    Localization.AtPrime.map_eq_maximalIdeal, hmax,
    ENat.toNat_eq_iff_eq_natCast, Nat.cast_one, Module.length_eq_one_iff,
    isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def]
  exact IsLocalRing.maximalIdeal.isMaximal _

/-- Adic formal smoothness of a localization map forces ramification index one
at the corresponding prime. -/
private theorem ramificationIdx_eq_one_of_formallySmooth_localizations
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal S) [q.IsPrime]
    [IsDomain (Localization.AtPrime (q.under R))]
    [IsDiscreteValuationRing (Localization.AtPrime (q.under R))]
    [IsDomain (Localization.AtPrime q)] [IsDiscreteValuationRing (Localization.AtPrime q)]
    (φ : Localization.AtPrime (q.under R) →+* Localization.AtPrime q)
    (hinj : Function.Injective φ) (hlocal : IsLocalHom φ)
    (hφ : ∀ x : R, φ (algebraMap R _ x) = algebraMap S _ (algebraMap R S x))
    (hformal : RingHom.FormallySmoothNAdic.{max u v} φ
      (IsLocalRing.maximalIdeal (Localization.AtPrime q))) : q.ramificationIdx R = 1 := by
  let Rp := Localization.AtPrime (q.under R)
  let Sq := Localization.AtPrime q
  let : Algebra Rp Sq := φ.toAlgebra
  let : FaithfulSMul Rp Sq := (faithfulSMul_iff_algebraMap_injective Rp Sq).mpr hinj
  let : IsLocalHom (algebraMap Rp Sq) := hlocal
  let : IsDiscreteValuationRing.IsExtension Rp Sq := ⟨⟩
  have hw := (IsDiscreteValuationRing.formallySmooth_iff_weaklyUnramified_and_isSeparableExtension
    Rp Sq).mp hformal |>.1
  have hm := (IsDiscreteValuationRing.ramificationIndex_characterization Rp Sq).2.1
  rw [show IsDiscreteValuationRing.ramificationIndex Rp Sq = 1 from hw, pow_one] at hm
  exact ramificationIdx_eq_one_of_localized_map R S q φ hφ hm

universe uL₁ uA₁ uB₁

/-- **The base-change package of an adically formally smooth extension is a weak solution.**

Tag 09EQ propagates adic formal smoothness of `A → B` to the localizations of the base-changed
integral closures, and Tag 09E7 read backwards turns formal smoothness of a local extension of
discrete valuation rings into ramification index one — which is the definition of a weak solution
(Tag 09EN(1)).  So for a formally smooth `A → B`, *every* finite `K₁ / K` is a weak solution, along
any presentation of the base change.

This is 09EQ in bundled form, and the translation is free: 09EQ takes its base-change data
unbundled, as three `AlgEquiv`s and four compatibility conditions, while
`IntegralClosureBaseChange` carries the same data as a package whose `A₁` and `B₁` are integral
closures by their own `IsIntegralClosure` fields.  So the equivalences are
`IsIntegralClosure.equiv` and `D.eL₁`; the conditions are `IsIntegralClosure.algebraMap_equiv`, the
two scalar towers through `L₁`, and the package's own `eL₁_left`, `eL₁_right` and `ringSquare`. -/
theorem IntegralClosureBaseChange.isWeakSolution_of_formallySmoothNAdic
    {A : Type uA} {B : Type uB} {K : Type uK} {L : Type uL} {K₁ : Type uK₁}
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁]
    (D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁}
      A B K L K₁)
    (hformal : RingHom.FormallySmoothNAdic.{max uA uB} (algebraMap A B)
      (IsLocalRing.maximalIdeal B)) :
    D.IsWeakSolution := by
  let eA := IsIntegralClosure.equiv A D.A₁ K₁ (integralClosure A K₁)
  let eB := IsIntegralClosure.equiv B D.B₁ D.L₁ (integralClosure B D.L₁)
  have h :=
    IsDiscreteValuationRing.formallySmooth_localizations_after_finite_fraction_field_extension
    A B K L K₁ D.L₁ D.A₁ D.B₁ D.eL₁ eA eB D.eL₁_left D.eL₁_right
    (fun x => IsIntegralClosure.algebraMap_equiv B D.B₁ D.L₁ (integralClosure B D.L₁) x)
    (fun x => by rw [← IsScalarTower.algebraMap_apply K L D.L₁,
      ← IsScalarTower.algebraMap_apply K K₁ D.L₁])
    (fun x => by
      rw [show (eA x : K₁) = algebraMap D.A₁ K₁ x from
        IsIntegralClosure.algebraMap_equiv A D.A₁ K₁ (integralClosure A K₁) x]
      exact D.ringSquare x)
    hformal
  intro q hq
  obtain ⟨hp, hqp, hpp, ⟨hPdom, hPdvr⟩, ⟨hQdom, hQdvr⟩, φ, hφinj, hφlocal, hφ, hformal⟩ :=
    h.2.2 q hq
  let := hqp
  let := hpp
  let := hPdom
  let := hQdom
  let := hPdvr
  let := hQdvr
  exact ramificationIdx_eq_one_of_formallySmooth_localizations D.A₁ D.B₁ q φ hφinj hφlocal hφ
    hformal

/-- Any finite base extension preserves weak unramifiedness when the original
residue field is perfect.

This is the *perfect* setting's replacement for `isWeakSolution_of_finite_extension` below,
which needs `IsAlgClosed`. Note how little it asks: no completeness on either ring, no
`CharP`, no residue condition — only finiteness of `K₁ / K` and perfectness of `κ_A`. That is the
boundary of the difficulty, because what fails over a merely perfect residue field is moving a
*genuinely ramified* weak solution along an enlargement of the base, not moving an already weakly
unramified one.

The proof is a three-line corollary of
`IntegralClosureBaseChange.isWeakSolution_of_formallySmoothNAdic`. -/
theorem isWeakSolution_of_isWeaklyUnramified_of_perfect_residueField
    (A B K L K₁ : Type*)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁] [PerfectField (IsLocalRing.ResidueField A)]
    (D : IsDiscreteValuationRing.IntegralClosureBaseChange A B K L K₁)
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B) : D.IsWeakSolution :=
  D.isWeakSolution_of_formallySmoothNAdic (formallySmooth_of_isWeaklyUnramified A B hweak)

/-- Finitely many finite field extensions embed over the base into one finite
extension in the universe of the base field. -/
theorem exists_finite_extension_nonempty_algHom
    (K : Type u) [Field K] {ι : Type v} [Finite ι]
    (E : ι → Type uF) [∀ i, Field (E i)] [∀ i, Algebra K (E i)]
    [∀ i, Module.Finite K (E i)] :
    ∃ (F : Type u) (_ : Field F) (_ : Algebra K F) (_ : Module.Finite K F),
      ∀ i, Nonempty (E i →ₐ[K] F) := by
  let f (i : ι) : E i →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let F : IntermediateField K (AlgebraicClosure K) := ⨆ i, (f i).fieldRange
  let : ∀ i, Module.Finite K (f i).fieldRange := fun i =>
    Module.Finite.equiv (AlgEquiv.ofInjectiveField (f i)).toLinearEquiv
  let : Module.Finite K F := inferInstance
  refine ⟨F, inferInstance, inferInstance, inferInstance, fun i => ?_⟩
  exact ⟨(f i).codRestrict F.toSubalgebra fun x =>
    (le_iSup (fun i => (f i).fieldRange) i) ⟨x, rfl⟩⟩

/-- An algebra equivalence preserves ramification indices at corresponding primes. -/
private theorem ramificationIdx_comap_algEquiv
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (e : S ≃ₐ[R] T) (q : Ideal T) [q.IsPrime] :
    (q.comap e.toRingHom).ramificationIdx R = q.ramificationIdx R := by
  let : Algebra S T := e.toRingHom.toAlgebra
  let : IsScalarTower R S T := IsScalarTower.of_algHom e.toAlgHom
  let : Module.Flat S T := RingHom.Flat.of_bijective e.bijective
  exact ramificationIdx_comap_of_surjective_of_flat R S T e.surjective q

/-- Simultaneous compatible equivalences of the base and target preserve the
condition that all maximal ideals have ramification index one. -/
theorem forall_ramificationIdx_eq_one_of_equiv
    (R S R' S' : Type*) [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R' S']
    (eR : R ≃+* R') (eS : S ≃+* S')
    (he : ∀ x : R, eS (algebraMap R S x) = algebraMap R' S' (eR x))
    (h : ∀ q : Ideal S, q.IsMaximal → q.ramificationIdx R = 1) :
    ∀ q : Ideal S', q.IsMaximal → q.ramificationIdx R' = 1 := by
  let : Algebra R R' := eR.toRingHom.toAlgebra
  let : Algebra R S' := ((algebraMap R' S').comp eR.toRingHom).toAlgebra
  let : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq' rfl
  let e : S ≃ₐ[R] S' := { __ := eS, commutes' := he }
  intro q hq
  let : q.IsMaximal := hq
  have h' := h (q.comap e.toRingHom)
    (Ideal.comap_isMaximal_of_surjective _ e.surjective)
  rw [ramificationIdx_comap_algEquiv R S S' e q] at h'
  exact (ramificationIdx_eq_of_surjective_base R R' S' eR.surjective q).symm.trans h'

/-- **Abhyankar's lemma against a prescribed extension.**

For a tamely ramified extension of complete discrete valuation rings, *any* finite `K₁ / K` whose
local ramification index is divisible by `e(B/A)` is already a weak solution — the extension does
not have to be the Kummer one built by adjoining a root of a uniformizer.

This is the shape a transport argument cannot provide.
`isWeakSolution_of_finite_extension` moves a weak solution to a larger base field but pays
completeness and an algebraically closed residue field for it, and
`IsWeakSolution.of_finiteEtale_square` moves one for free but only along an étale square, which a
totally ramified endgame extension never is.  Here nothing is moved: the weak-solution property is
*re-derived* over whatever `K₁` is prescribed, which is what lets several extensions be solved
over one common overfield chosen in advance.

The content is Abhyankar's lemma `formallySmooth_localizations_of_ramificationIndex_dvd` together
with the identification of formal smoothness at each local factor with ramification index one;
`exists_finite_extension_isWeakSolution_of_tame` is the special case in which `K₁` is chosen to be
`K(π^{1/e})`, where the divisibility is an equality. -/
theorem isWeakSolution_of_tame_of_ramificationIndex_dvd
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (K₁ : Type uK)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [Algebra A K₁] [IsScalarTower A K K₁] [Module.Finite K K₁]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (htame : ringChar (IsLocalRing.ResidueField A) = 0 ∨
      Nat.Coprime (ringChar (IsLocalRing.ResidueField A))
          (IsDiscreteValuationRing.ramificationIndex A B) ∧
        Algebra.IsSeparableExtension (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField B))
    (D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uB, uK, uL, uK,
      max uL uK, uK, max uL uK} A B K L K₁)
    (hdvd : ∀ p : Ideal (integralClosure A K₁), p.IsMaximal →
      IsDiscreteValuationRing.ramificationIndex A B ∣ p.ramificationIdx A) :
    D.IsWeakSolution := by
  classical
  let n := IsDiscreteValuationRing.ramificationIndex A B
  obtain ⟨hA₁, hAA₁, hAfin, hAc, hAf⟩ := integralClosure_isCompleteDVR A K K₁
  let A₁ := integralClosure A K₁
  let := hA₁
  let := hAA₁
  obtain ⟨r, E, hE, hKE, hLE, hK₁E, hBE, hKLE, hKK₁E, hfin, e0,
    hr, hleft, hright, hbase, hcases⟩ :=
    IsDiscreteValuationRing.formallySmooth_localizations_of_ramificationIndex_dvd.{uA,uB,uK,uL,uK,
      max uA uB uK uL} A B K L K₁ htame
  let := hE
  let := hKE
  let := hLE
  let := hK₁E
  let := hBE
  let := hKLE
  let := hKK₁E
  let := hfin
  let : ∀ i, IsScalarTower B L (E i) := fun i => IsScalarTower.of_algebraMap_eq (hbase i)
  let : ∀ i, Algebra A (E i) := fun i =>
    ((algebraMap B (E i)).comp (algebraMap A B)).toAlgebra
  let : ∀ i, IsScalarTower A B (E i) := fun i => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, IsScalarTower A K₁ (E i) := fun i => IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap B (E i) (algebraMap A B a) =
      algebraMap K₁ (E i) (algebraMap A K₁ a)
    rw [hbase, ← IsScalarTower.algebraMap_apply A B L,
      IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A K K₁,
      ← IsScalarTower.algebraMap_apply K L (E i),
      ← IsScalarTower.algebraMap_apply K K₁ (E i)]
  let e : D.L₁ ≃ₐ[L] ∀ i, E i :=
    { __ := (D.eL₁.trans e0).toRingEquiv
      commutes' x := funext fun i => by
        change e0 (D.eL₁ (algebraMap L D.L₁ x)) i = algebraMap L (E i) x
        rw [D.eL₁_left]
        exact hleft i x }
  have he : ∀ i x, e (algebraMap K₁ D.L₁ x) i = algebraMap K₁ (E i) x := by
    intro i x
    change e0 (D.eL₁ (algebraMap K₁ D.L₁ x)) i = _
    rw [D.eL₁_right]
    exact hright i x
  apply isWeakSolution_of_factors A B K L K₁ D E e he
  intro i q hq
  let B₁ := integralClosure B (E i)
  let f := mapIntegralClosureOfTower A B K₁ (E i)
  let : Algebra A₁ B₁ := f.toRingHom.toAlgebra
  obtain ⟨hA₁', hB₁, hExt, _, _, _, _⟩ :=
    integralClosure_factor_isExtension A B K L K₁ (E i)
  let := hB₁
  let := hExt
  have hqbase : q.under A₁ = IsLocalRing.maximalIdeal A₁ := by
    rw [IsLocalRing.eq_maximalIdeal hq]
    exact IsLocalRing.maximalIdeal_comap (algebraMap A₁ B₁)
  have hqmax : (q.under A₁).IsMaximal := by rw [hqbase]; infer_instance
  obtain ⟨f0, hf0, _, hlocal⟩ := hcases i
  have hf0eq : f0 = f.toRingHom := by
    ext x
    exact hf0 x
  subst f0
  obtain ⟨hqp, hpp, ⟨hPdom, hPdvr⟩, ⟨hQdom, hQdvr⟩,
    φ, hinj, hloc, hφ, hformal⟩ :=
    hlocal (q.under A₁) hqmax (hdvd (q.under A₁) hqmax) q hq rfl
  let := hqp
  let := hpp
  let := hPdom
  let := hQdom
  let := hPdvr
  let := hQdvr
  exact ramificationIdx_eq_one_of_formallySmooth_localizations A₁ B₁ q φ hinj hloc hφ hformal

/-- A tame extension of complete DVRs admits a weak solution obtained by adjoining
an appropriate root of a uniformizer. -/
theorem exists_finite_extension_isWeakSolution_of_tame
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (htame : ringChar (IsLocalRing.ResidueField A) = 0 ∨
      Nat.Coprime (ringChar (IsLocalRing.ResidueField A))
          (IsDiscreteValuationRing.ramificationIndex A B) ∧
        Algebra.IsSeparableExtension (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField B)) :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁) (_ : Algebra.IsSeparable K K₁),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA,uB,uK,uL,uK,
          max uL uK,uK,max uL uK} A B K L K₁, D.IsWeakSolution := by
  classical
  let n := IsDiscreteValuationRing.ramificationIndex A B
  by_cases hn1 : n = 1
  · obtain ⟨D⟩ := nonempty_integralClosureBaseChange A B K L K
    exact ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, D, isWeakSolution_self A B K L D hn1⟩
  have hn : 2 ≤ n := by
    have := (IsDiscreteValuationRing.ramificationIndex_characterization A B).1
    change 1 ≤ n at this
    omega
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  let : Fact (Irreducible (Stacks.KummerExtension.kummerPoly K π n)) :=
    ⟨Stacks.KummerExtension.kummerPoly_irreducible K π n (by omega) hπ⟩
  let K₁ := Stacks.KummerExtension.K1 K π n
  let : Field K₁ := inferInstance
  let : IsScalarTower A K K₁ := inferInstance
  let : Module.Finite K K₁ := Module.finite_of_finrank_pos
    (by rw [Stacks.KummerExtension.finrank_K1 K π n hn hπ]; omega)
  obtain ⟨hA₁, hAA₁, hAfin, hAc, hAf⟩ := integralClosure_isCompleteDVR A K K₁
  let A₁ := integralClosure A K₁
  let := hA₁
  let := hAA₁
  obtain ⟨m, hmmax, hmlo, _, hmidx⟩ := Stacks.KummerExtension.exists_ramificationIdx_eq K π n hn hπ
  let : m.IsMaximal := hmmax
  let : m.LiesOver (IsLocalRing.maximalIdeal A) := hmlo
  have hmidx' : m.ramificationIdx A = n := by
    rwa [← Ideal.ramificationIdx'_eq_ramificationIdx
      (IsLocalRing.maximalIdeal A) m (IsDiscreteValuationRing.not_a_field A)]
  have hidx : (IsLocalRing.maximalIdeal A₁).ramificationIdx A = n := by
    rwa [IsLocalRing.eq_maximalIdeal hmmax] at hmidx'
  -- `n` is prime to the residue characteristic, so `x ^ n - π` is separable and `K₁ / K` is too.
  have hcop : ringChar (IsLocalRing.ResidueField A) = 0 ∨
      Nat.Coprime (ringChar (IsLocalRing.ResidueField A)) n := htame.imp id And.left
  let : Algebra.IsSeparable K K₁ := Stacks.KummerExtension.isSeparable_K1 K π n hn hπ hcop
  obtain ⟨D⟩ := nonempty_integralClosureBaseChange A B K L K₁
  exact ⟨K₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, D,
    isWeakSolution_of_tame_of_ramificationIndex_dvd A B K L K₁ htame D
      (fun q hq => by rw [IsLocalRing.eq_maximalIdeal hq, hidx])⟩

/-- **Epp's theorem (Stacks Tag 09F9) in the residue-characteristic-zero and tame cases.**

For an extension `A → B` of complete discrete valuation rings, a finite weak solution exists as
soon as either

* the residue characteristic is `0`, or
* the residue characteristic is coprime to the ramification index `e(B/A)` and the residue
  extension `κ_B / κ_A` is separable — that is, `B / A` is *tamely* ramified.

This is a genuine part of Tag 09F9 and it depends on **neither** Tag 09ET nor Tag 09F8. That
matters here for a specific reason: Tag 09ET's literal statement is false (a counterexample
refutes it), and the published proof of 09F9 reduces to
separably closed residue fields by invoking exactly the clause of 09ET that the counterexample
kills. The two cases below sit outside that reduction entirely, so they are unaffected.

This does not cover the substance of 09F9, the *wild* case — residue characteristic `p` dividing
the ramification index — which is what Epp's argument is for.

The extension `K₁ / K` produced here is *separable*, which is why the conclusion carries
`Algebra.IsSeparable K K₁`: in the unramified case `K₁ = K`, and otherwise `K₁ = K(π^{1/n})` with
`n = e(B/A)` prime to the residue characteristic, so `x ^ n - π` is separable
(`Stacks.KummerExtension.isSeparable_K1`). Separability is not needed for the weak-solution
property itself, but the completion descent of Tag 09EJ asks for it of the solution it is handed
upstairs.

The content is entirely that of the private `exists_finite_extension_isWeakSolution_of_tame`
above. -/
alias exists_finite_extension_isWeakSolution_of_tame_or_charZero :=
  exists_finite_extension_isWeakSolution_of_tame

/-- Integral closure is unchanged when the base is replaced by an integral algebra. -/
private noncomputable def integralClosureTowerEquiv
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.IsIntegral R S] :
    integralClosure S T ≃ₐ[R] integralClosure R T :=
  { toFun x := ⟨x.1, isIntegral_trans x.1 x.2⟩
    invFun x := ⟨x.1, x.2.tower_top⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_mul' _ _ := rfl
    commutes' _ := rfl }

private lemma integralClosureTowerEquiv_apply
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.IsIntegral R S] (x : integralClosure S T) :
    (integralClosureTowerEquiv R S T x : T) = (x : T) := rfl

/-- Algebraic closedness transports along an equivalence between arbitrary universes. -/
private theorem isAlgClosed_of_ringEquiv
    (k k' : Type*) [Field k] [Field k'] [IsAlgClosed k] (e : k ≃+* k') :
    IsAlgClosed k' := by
  apply IsAlgClosed.of_exists_root
  intro p hmonic hp
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (p.map e.symm.toRingHom)
    (by rw [Polynomial.degree_map]; exact ne_of_gt (Polynomial.degree_pos_of_irreducible hp))
  refine ⟨e x, e.symm.injective ?_⟩
  rw [Polynomial.IsRoot] at hx
  rw [map_zero, ← hx]
  clear hx hp hmonic
  induction p using Polynomial.induction_on <;> simp_all

theorem isAlgClosed_residueField_of_finite
    (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Finite R S]
    [IsAlgClosed (IsLocalRing.ResidueField R)] :
    IsAlgClosed (IsLocalRing.ResidueField S) :=
  isAlgClosed_of_ringEquiv (IsLocalRing.ResidueField R) _ (RingEquiv.ofBijective
    (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
    (IsAlgClosed.ringHom_bijective_of_isIntegral _ (algebraMap_isIntegral_iff.mpr inferInstance)))


/-- A weakly unramified square between presentations of integral closures gives
ramification index one on the canonical integral closures. -/
theorem forall_ramificationIdx_eq_one_integralClosure
    (R S K L C D : Type*)
    [CommRing R] [CommRing S] [CommRing K] [CommRing L] [CommRing C] [CommRing D]
    [Algebra R S] [Algebra R K] [Algebra S L] [Algebra R L] [Algebra K L]
    [IsScalarTower R S L] [IsScalarTower R K L]
    [Algebra R C] [Algebra C K] [IsScalarTower R C K] [IsIntegralClosure C R K]
    [Algebra S D] [Algebra D L] [IsScalarTower S D L] [IsIntegralClosure D S L]
    [Algebra C D]
    (hsquare : ∀ x : C, algebraMap D L (algebraMap C D x) =
      algebraMap K L (algebraMap C K x))
    (h : ∀ q : Ideal D, q.IsMaximal → q.ramificationIdx C = 1) :
    letI : Algebra (integralClosure R K) (integralClosure S L) :=
      (mapIntegralClosureOfTower R S K L).toRingHom.toAlgebra
    ∀ q : Ideal (integralClosure S L), q.IsMaximal →
      q.ramificationIdx (integralClosure R K) = 1 := by
  let : Algebra (integralClosure R K) (integralClosure S L) :=
    (mapIntegralClosureOfTower R S K L).toRingHom.toAlgebra
  let eC := IsIntegralClosure.equiv R C K (integralClosure R K)
  let eD := IsIntegralClosure.equiv S D L (integralClosure S L)
  apply forall_ramificationIdx_eq_one_of_equiv C D
    (integralClosure R K) (integralClosure S L) eC.toRingEquiv eD.toRingEquiv _ h
  intro x
  apply Subtype.ext
  change algebraMap (integralClosure S L) L (eD (algebraMap C D x)) =
    (mapIntegralClosureOfTower R S K L (eC x) : L)
  rw [mapIntegralClosureOfTower_apply, IsIntegralClosure.algebraMap_equiv,
    hsquare, ← IsIntegralClosure.algebraMap_equiv R C K (integralClosure R K) x]
  rfl

end IsDiscreteValuationRing
