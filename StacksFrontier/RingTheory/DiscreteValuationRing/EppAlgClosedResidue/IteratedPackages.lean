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
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.TameCase
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.PurelyInseparableCase

open Stacks.DegreePExtensionLevel
open Stacks.DiscreteValuationRing.EppLevelInduction

/-!
# Eliminating ramification: iterated packages and perfect residue fields

Iterated base-change packages, perfect residue fields, solutions on factors, transport along
equivalences and along universe lifts.

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

universe u v

universe uL₁ uA₁ uB₁

/-- The reduced compositum, decomposed into its field factors **over the new base `K₁`**.

The two equivalences supplied as input see the decomposition over different bases: `e₀` identifies
an abstract `T` with the reduction of `L ⊗[K] K₁` over `K`, and `e` decomposes `T` into factors
over `L`.  Neither is `K₁`-linear, and it is `K₁`-linearity that a statement about the *new base*
needs. Composing them and checking `commutes'` on the right tensor factor is what produces it. -/
noncomputable def reducedTensorFactorsEquiv
    (K L K₁ T : Type*) [CommRing K] [CommRing L] [CommRing K₁] [CommRing T]
    [Algebra K L] [Algebra K K₁] [Algebra K T] [Algebra L T] [Algebra K₁ T]
    {ι : Type*} (E : ι → Type*) [∀ i, CommRing (E i)] [∀ i, Algebra L (E i)]
    [∀ i, Algebra K₁ (E i)]
    (e₀ : T ≃ₐ[K] ReducedTensorTower.Reduction (L ⊗[K] K₁))
    (e : T ≃ₐ[L] ∀ i, E i)
    (h₀ : ∀ x : K₁, e₀ (algebraMap K₁ T x) =
      Ideal.Quotient.mk _ ((1 : L) ⊗ₜ[K] x))
    (he : ∀ i x, e (algebraMap K₁ T x) i = algebraMap K₁ (E i) x) :
    letI : Algebra K₁ (L ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra K₁ (ReducedTensorTower.Reduction (L ⊗[K] K₁)) :=
      Ideal.Quotient.algebra K₁
    ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K₁] ∀ i, E i := by
  letI : Algebra K₁ (L ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra K₁ (ReducedTensorTower.Reduction (L ⊗[K] K₁)) :=
    Ideal.Quotient.algebra K₁
  refine { __ := e₀.symm.toRingEquiv.trans e.toRingEquiv, commutes' := ?_ }
  intro x
  ext i
  change e (e₀.symm (Ideal.Quotient.mk _ ((1 : L) ⊗ₜ[K] x))) i = _
  rw [← h₀, AlgEquiv.symm_apply_apply]
  exact he i x

/-- `reducedTensorFactorsEquiv` sends the left tensor factor to the structural map from `L`.

The definition's own `commutes'` field records only what it does on `K₁`, so this is the other
half of its characterisation: it shows that the decomposition is compatible with the original one
over `L`. -/
lemma reducedTensorFactorsEquiv_left
    (K L K₁ T : Type*) [CommRing K] [CommRing L] [CommRing K₁] [CommRing T]
    [Algebra K L] [Algebra K K₁] [Algebra K T] [Algebra L T] [Algebra K₁ T]
    {ι : Type*} (E : ι → Type*) [∀ i, CommRing (E i)] [∀ i, Algebra L (E i)]
    [∀ i, Algebra K₁ (E i)]
    (e₀ : T ≃ₐ[K] ReducedTensorTower.Reduction (L ⊗[K] K₁))
    (e : T ≃ₐ[L] ∀ i, E i)
    (h₀ : ∀ x : K₁, e₀ (algebraMap K₁ T x) =
      Ideal.Quotient.mk _ ((1 : L) ⊗ₜ[K] x))
    (he : ∀ i x, e (algebraMap K₁ T x) i = algebraMap K₁ (E i) x)
    (hleft : ∀ x : L, e₀ (algebraMap L T x) =
      Ideal.Quotient.mk _ (x ⊗ₜ[K] (1 : K₁))) (x : L) (i : ι) :
    reducedTensorFactorsEquiv K L K₁ T E e₀ e h₀ he
      (Ideal.Quotient.mk _ (x ⊗ₜ[K] (1 : K₁))) i = algebraMap L (E i) x := by
  change e (e₀.symm (Ideal.Quotient.mk _ (x ⊗ₜ[K] (1 : K₁)))) i = _
  rw [← hleft, AlgEquiv.symm_apply_apply, e.commutes]
  rfl


/-- The intersection-of-Frobenius-powers condition ascends through a finite square
of local rings with algebraically closed bottom residue field. -/
theorem residueField_forall_exists_pow_iff_of_finite_square
    (A B R S : Type*) [CommRing A] [CommRing B] [CommRing R] [CommRing S]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing R] [IsLocalRing S]
    [Algebra A B] [Algebra A R] [Algebra A S] [Algebra B S] [Algebra R S]
    [IsScalarTower A B S] [IsScalarTower A R S]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A R)]
    [IsLocalHom (algebraMap A S)] [IsLocalHom (algebraMap B S)]
    [IsLocalHom (algebraMap R S)] [Module.Finite A R] [Module.Finite B S]
    [IsAlgClosed (IsLocalRing.ResidueField A)]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    (hB : ∀ x : IsLocalRing.ResidueField B,
      (∃ a : IsLocalRing.ResidueField A,
        algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) a = x) ↔
        ∀ n : ℕ, 1 ≤ n → ∃ y : IsLocalRing.ResidueField B, y ^ (p ^ n) = x)
    (x : IsLocalRing.ResidueField S) :
    (∃ a : IsLocalRing.ResidueField R,
      algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) a = x) ↔
      ∀ n : ℕ, 1 ≤ n → ∃ y : IsLocalRing.ResidueField S, y ^ (p ^ n) = x := by
  rw [← residueField_forall_exists_pow_iff_of_finite A B S p hB x]
  have hsurj := (IsAlgClosed.ringHom_bijective_of_isIntegral
    (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField R))
    (algebraMap_isIntegral_iff.mpr inferInstance)).surjective
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨a, rfl⟩ := hsurj r
    exact ⟨a, by rwa [← IsScalarTower.algebraMap_apply (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)] at hr⟩
  · rintro ⟨a, ha⟩
    exact ⟨algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField R) a,
      by rwa [← IsScalarTower.algebraMap_apply (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)]⟩


/-- Weak solutions for all integral field factors of a first base change compose
to a weak solution for the original extension. -/
theorem isWeakSolution_of_iterated_packages
    (A B K L K₁ K₂ R : Type*)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁] [Field K₂]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra K K₂] [Algebra K₁ K₂]
    [Algebra A K₂] [IsScalarTower K K₁ K₂]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₂]
    [Module.Finite K K₂] [Module.Finite K₁ K₂]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra A R] [Algebra.IsIntegral A R]
    [Algebra R K₁] [IsFractionRing R K₁] [Algebra R K₂] [IsScalarTower R K₁ K₂]
    (D₂ : IsDiscreteValuationRing.IntegralClosureBaseChange A B K L K₂)
    {ι : Type*} [Finite ι] (E S : ι → Type*)
    [∀ i, Field (E i)] [∀ i, CommRing (S i)] [∀ i, IsDomain (S i)]
    [∀ i, IsDiscreteValuationRing (S i)]
    [∀ i, Algebra K (E i)] [∀ i, Algebra K₁ (E i)] [∀ i, Algebra L (E i)]
    [∀ i, IsScalarTower K K₁ (E i)]
    [∀ i, Algebra R (S i)] [∀ i, IsDiscreteValuationRing.IsExtension R (S i)]
    [∀ i, Algebra B (S i)] [∀ i, Algebra.IsIntegral B (S i)]
    [∀ i, Algebra R (E i)] [∀ i, Algebra (S i) (E i)]
    [∀ i, IsFractionRing (S i) (E i)]
    [∀ i, IsScalarTower R (S i) (E i)] [∀ i, IsScalarTower R K₁ (E i)]
    (hA : ∀ a : A, algebraMap A K₂ a = algebraMap R K₂ (algebraMap A R a))
    (hB : ∀ i b, algebraMap L (E i) (algebraMap B L b) =
      algebraMap (S i) (E i) (algebraMap B (S i) b))
    (hsquare : ∀ i a, algebraMap B (S i) (algebraMap A B a) =
      algebraMap R (S i) (algebraMap A R a))
    (D : ∀ i, IsDiscreteValuationRing.IntegralClosureBaseChange R (S i) K₁ (E i) K₂)
    (hD : ∀ i, (D i).IsWeakSolution) :
    letI : Algebra K₁ (L ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra K₁ (ReducedTensorTower.Reduction (L ⊗[K] K₁)) :=
      Ideal.Quotient.algebra K₁
    ∀ e : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K₁] ∀ i, E i,
      (∀ i x, e (Ideal.Quotient.mk _ (x ⊗ₜ[K] (1 : K₁))) i = algebraMap L (E i) x) →
      D₂.IsWeakSolution := by
  let : Algebra K₁ (L ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
  let : Algebra K₁ (ReducedTensorTower.Reduction (L ⊗[K] K₁)) :=
    Ideal.Quotient.algebra K₁
  intro e he
  let F := fun i => (D i).L₁
  let : ∀ i, Algebra L (F i) := fun i =>
    ((algebraMap (E i) (F i)).comp (algebraMap L (E i))).toAlgebra
  let : ∀ i, IsScalarTower L (E i) (F i) := fun i => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, Algebra B (F i) := fun i =>
    ((algebraMap (S i) (F i)).comp (algebraMap B (S i))).toAlgebra
  let : ∀ i, Algebra A (F i) := fun i =>
    ((algebraMap B (F i)).comp (algebraMap A B)).toAlgebra
  let : ∀ i, IsScalarTower A B (F i) := fun i => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, IsScalarTower B L (F i) := fun i =>
    IsScalarTower.of_algebraMap_eq fun b => by
      change algebraMap (S i) (F i) (algebraMap B (S i) b) =
        algebraMap (E i) (F i) (algebraMap L (E i) (algebraMap B L b))
      rw [hB, IsScalarTower.algebraMap_apply (S i) (E i) (F i)]
  let : ∀ i, IsScalarTower A K₂ (F i) := fun i =>
    IsScalarTower.of_algebraMap_eq fun a => by
      change algebraMap (S i) (F i) (algebraMap B (S i) (algebraMap A B a)) = _
      rw [hsquare, IsScalarTower.algebraMap_apply (S i) (E i) (F i),
        ← IsScalarTower.algebraMap_apply R (S i) (E i),
        IsScalarTower.algebraMap_apply R K₁ (E i),
        ← IsScalarTower.algebraMap_apply K₁ (E i) (F i),
        IsScalarTower.algebraMap_apply K₁ K₂ (F i),
        ← IsScalarTower.algebraMap_apply R K₁ K₂, ← hA]
  apply isWeakSolution_of_iterated_factors A B K L K₁ K₂ D₂ E F
    (fun i => (D i).eL₁) (fun i => (D i).eL₁_left) (fun i => (D i).eL₁_right) e he
  intro i
  exact isWeakSolution_integral_base_change R (S i) K₁ (E i) K₂ (D i) A B
    hA (fun _ => rfl) (hD i)


/-- **A perfect residue field survives a finite local extension.**

The residue extension induced by a module-finite local algebra is algebraic.  An algebraic
extension of a perfect field is perfect.  This elementary ascent is the reason weak solutions can
be amalgamated over a complete DVR whose residue field is merely perfect, rather than algebraically
closed. -/
theorem perfectField_residueField_of_finite
    (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [Module.Finite R S]
    [PerfectField (IsLocalRing.ResidueField R)] :
    PerfectField (IsLocalRing.ResidueField S) := by
  let : Algebra.IsIntegral (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    inferInstance
  exact Algebra.IsAlgebraic.perfectField (IsLocalRing.ResidueField R)

/-- **A weak solution remains one after a prescribed further finite extension when the
intermediate base has perfect residue field.**

The relevant intermediate base is `integralClosure A K₁`.  Decompose the first compositum into
field factors.  The hypothesis that `D₁` is a weak solution says that every resulting extension of
that intermediate base is weakly unramified; perfectness then makes *every* finite base change from
`K₁` to `K₂` a weak solution for each factor.  The iterated-package composition reassembles those
factorwise statements into `D₂.IsWeakSolution`.

Unlike `isWeakSolution_of_finite_extension` below, this statement does not require the original
residue field to be algebraically closed.  In particular it applies after the totally ramified
orbit extension in the equal-characteristic branch of Epp's theorem: total ramification preserves
the original perfect residue field, and a subsequent shared Artin--Schreier extension can therefore
split all constant classes without destroying the already solved wild members. -/
theorem isWeakSolution_of_finite_extension_of_perfect_integralClosure_residue
    (A B K L K₁ K₂ : Type*)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁] [Field K₂]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra K K₂] [Algebra K₁ K₂]
    [Algebra A K₁] [Algebra A K₂]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [IsScalarTower A K K₂] [IsScalarTower K K₁ K₂]
    [Module.Finite K K₁] [Module.Finite K K₂]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [PerfectField (IsLocalRing.ResidueField A)]
    (D₁ : IsDiscreteValuationRing.IntegralClosureBaseChange A B K L K₁)
    (D₂ : IsDiscreteValuationRing.IntegralClosureBaseChange A B K L K₂)
    (hD₁ : D₁.IsWeakSolution) : D₂.IsWeakSolution := by
  classical
  let : Module.Finite K₁ K₂ := Module.Finite.of_restrictScalars_finite K K₁ K₂
  obtain ⟨n, E, hE, hLE, hKE, hBE, hAE, hBLE, hABE, hAKE, hfinE, hn, e, he⟩ :=
    finiteFieldFactors_compatible A B K L K₁ D₁
  let := hE
  let := hLE
  let := hKE
  let := hBE
  let := hAE
  let := hBLE
  let := hABE
  let := hAKE
  let := hfinE
  let R : Type _ := integralClosure A K₁
  let S : Fin n → Type _ := fun i => integralClosure B (E i)
  obtain ⟨hR, hAR, hfinR, hcompR, hfracR⟩ := integralClosure_isCompleteDVR A K K₁
  let := hR
  let := hAR
  let := hfinR
  let := hcompR
  let := hfracR
  let : PerfectField (IsLocalRing.ResidueField R) :=
    perfectField_residueField_of_finite A R
  have hS := fun i => integralClosure_isCompleteDVR B L (E i)
  choose hS hBS hfinS hcompS hfracS using hS
  let := hS
  let := hBS
  let := hfinS
  let := hcompS
  let := hfracS
  let : ∀ i, Algebra R (S i) := fun i =>
    (mapIntegralClosureOfTower A B K₁ (E i)).toRingHom.toAlgebra
  let : ∀ i, Algebra R (E i) := fun i =>
    ((algebraMap K₁ (E i)).comp (algebraMap R K₁)).toAlgebra
  let : ∀ i, @IsScalarTower R K₁ (E i)
      (inferInstance : Algebra R K₁).toSMul (inferInstance : Algebra K₁ (E i)).toSMul
      (inferInstance : Algebra R (E i)).toSMul := fun i =>
    IsScalarTower.of_algebraMap_eq' (R := R) (S := K₁) (A := E i) rfl
  let : ∀ i, @IsScalarTower R (S i) (E i)
      (inferInstance : Algebra R (S i)).toSMul (inferInstance : Algebra (S i) (E i)).toSMul
      (inferInstance : Algebra R (E i)).toSMul := fun i =>
    IsScalarTower.of_algebraMap_eq (R := R) (S := S i) (A := E i) fun r =>
      (mapIntegralClosureOfTower_apply A B K₁ (E i) r).symm
  let : Algebra R K₂ := ((algebraMap K₁ K₂).comp (algebraMap R K₁)).toAlgebra
  let : @IsScalarTower R K₁ K₂
      (inferInstance : Algebra R K₁).toSMul (inferInstance : Algebra K₁ K₂).toSMul
      (inferInstance : Algebra R K₂).toSMul :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := K₁) (A := K₂) rfl
  let : ∀ i, IsDiscreteValuationRing.IsExtension R (S i) := fun i =>
    (integralClosure_factor_isExtension A B K L K₁ (E i)).choose_spec.choose_spec.1
  have hweak (i : Fin n) : IsDiscreteValuationRing.IsWeaklyUnramified R (S i) :=
    (isWeaklyUnramified_iff_ramificationIdx_eq_one R (S i)).mpr
      (isWeakSolution_factor A B K L K₁ D₁ E e he hD₁ i
        (IsLocalRing.maximalIdeal (S i)) (IsLocalRing.maximalIdeal.isMaximal _))
  let D (i : Fin n) := Classical.choice (nonempty_integralClosureBaseChange R (S i) K₁ (E i) K₂)
  have hD (i : Fin n) : (D i).IsWeakSolution :=
    isWeakSolution_of_isWeaklyUnramified_of_perfect_residueField R (S i) K₁ (E i) K₂
      (D i) (hweak i)
  let : ∀ i, Algebra K (E i) := fun i =>
    ((algebraMap K₁ (E i)).comp (algebraMap K K₁)).toAlgebra
  let : ∀ i, IsScalarTower K K₁ (E i) := fun i => IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A K₁ K₂ := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A K K₂, IsScalarTower.algebraMap_apply A K K₁,
      ← IsScalarTower.algebraMap_apply K K₁ K₂]
  let e' := reducedTensorFactorsEquiv K L K₁ D₁.L₁ E D₁.eL₁ e D₁.eL₁_right he
  apply isWeakSolution_of_iterated_packages A B K L K₁ K₂ R D₂ E S
    ?_ ?_ ?_ D hD e' (fun i x => reducedTensorFactorsEquiv_left K L K₁ D₁.L₁ E
      D₁.eL₁ e D₁.eL₁_right he D₁.eL₁_left x i)
  · intro a
    change algebraMap A K₂ a = algebraMap K₁ K₂ (algebraMap A K₁ a)
    exact IsScalarTower.algebraMap_apply A K₁ K₂ a
  · intro i b
    rw [← IsScalarTower.algebraMap_apply B L (E i),
      ← IsScalarTower.algebraMap_apply B (S i) (E i)]
  · intro i a
    apply Subtype.ext
    change algebraMap B (E i) (algebraMap A B a) =
      ((mapIntegralClosureOfTower A B K₁ (E i)) (algebraMap A R a) : E i)
    rw [mapIntegralClosureOfTower_apply]
    change algebraMap B (E i) (algebraMap A B a) =
      algebraMap K₁ (E i) (algebraMap A K₁ a)
    rw [← IsScalarTower.algebraMap_apply A B (E i),
      ← IsScalarTower.algebraMap_apply A K₁ (E i)]

/-- Weak solutions over a complete DVR with algebraically closed residue field remain weak
solutions after any further finite extension of the base field. -/
theorem isWeakSolution_of_finite_extension
    (A B K L K₁ K₂ : Type*)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁] [Field K₂]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra K K₂] [Algebra K₁ K₂]
    [Algebra A K₁] [Algebra A K₂]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [IsScalarTower A K K₂] [IsScalarTower K K₁ K₂]
    [Module.Finite K K₁] [Module.Finite K K₂]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [IsAlgClosed (IsLocalRing.ResidueField A)]
    (D₁ : IsDiscreteValuationRing.IntegralClosureBaseChange A B K L K₁)
    (D₂ : IsDiscreteValuationRing.IntegralClosureBaseChange A B K L K₂)
    (hD₁ : D₁.IsWeakSolution) : D₂.IsWeakSolution :=
  isWeakSolution_of_finite_extension_of_perfect_integralClosure_residue
    A B K L K₁ K₂ D₁ D₂ hD₁

/-- Over a complete DVR with perfect residue field, finitely many weak solutions admit a common
finite base extension which is simultaneously a weak solution for every original extension. -/
theorem exists_finite_extension_forall_isWeakSolution_of_perfect_residueField
    (A : Type uA) (K : Type uK) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [PerfectField (IsLocalRing.ResidueField A)]
    {ι : Type v} [Finite ι] (B : ι → Type uB) (L : ι → Type uL) (E : ι → Type uF)
    [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)]
    [∀ i, IsDiscreteValuationRing (B i)] [∀ i, Field (L i)] [∀ i, Field (E i)]
    [∀ i, Algebra A (B i)] [∀ i, Algebra A (L i)] [∀ i, Algebra (B i) (L i)]
    [∀ i, Algebra K (L i)] [∀ i, Algebra K (E i)] [∀ i, Algebra A (E i)]
    [∀ i, IsDiscreteValuationRing.IsExtension A (B i)] [∀ i, IsFractionRing (B i) (L i)]
    [∀ i, IsScalarTower A (B i) (L i)] [∀ i, IsScalarTower A K (L i)]
    [∀ i, IsScalarTower A K (E i)] [∀ i, Module.Finite K (E i)]
    [∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (B i)) (B i)]
    (D : ∀ i, IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uB, uK, uL, uF, uD₁, uD₂, uD₃}
      A (B i) K (L i) (E i)) (hD : ∀ i, (D i).IsWeakSolution) :
    ∃ (F : Type uK) (_ : Field F) (_ : Algebra K F) (_ : Algebra A F)
      (_ : IsScalarTower A K F) (_ : Module.Finite K F),
      ∀ i, ∃ D' : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA,uB,uK,uL,uK,
        max uL uK,uK,max uL uK} A (B i) K (L i) F, D'.IsWeakSolution := by
  classical
  obtain ⟨F, hF, hKF, hfinF, hEF⟩ := exists_finite_extension_nonempty_algHom K E
  let := hF
  let := hKF
  let := hfinF
  let : Algebra A F := ((algebraMap K F).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K F := IsScalarTower.of_algebraMap_eq' rfl
  refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro i
  let f := Classical.choice (hEF i)
  let : Algebra (E i) F := f.toRingHom.toAlgebra
  let : IsScalarTower K (E i) F := IsScalarTower.of_algHom f
  let R : Type _ := integralClosure A (E i)
  obtain ⟨hR, hAR, hfinR, hcompR, hfracR⟩ := integralClosure_isCompleteDVR A K (E i)
  let := hR
  let := hAR
  let := hfinR
  let := hcompR
  let := hfracR
  let : PerfectField (IsLocalRing.ResidueField R) :=
    perfectField_residueField_of_finite A R
  obtain ⟨D'⟩ := nonempty_integralClosureBaseChange A (B i) K (L i) F
  exact ⟨D', isWeakSolution_of_finite_extension_of_perfect_integralClosure_residue
    A (B i) K (L i) (E i) F (D i) D' (hD i)⟩

/-- Finitely many weak solutions admit a common finite base extension which is simultaneously a
weak solution for every original extension.  This compatibility wrapper retains the historical
algebraically-closed-residue interface; the proof only uses perfectness. -/
theorem exists_finite_extension_forall_isWeakSolution
    (A : Type uA) (K : Type uK) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAlgClosed (IsLocalRing.ResidueField A)]
    {ι : Type v} [Finite ι] (B : ι → Type uB) (L : ι → Type uL) (E : ι → Type uF)
    [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)]
    [∀ i, IsDiscreteValuationRing (B i)] [∀ i, Field (L i)] [∀ i, Field (E i)]
    [∀ i, Algebra A (B i)] [∀ i, Algebra A (L i)] [∀ i, Algebra (B i) (L i)]
    [∀ i, Algebra K (L i)] [∀ i, Algebra K (E i)] [∀ i, Algebra A (E i)]
    [∀ i, IsDiscreteValuationRing.IsExtension A (B i)] [∀ i, IsFractionRing (B i) (L i)]
    [∀ i, IsScalarTower A (B i) (L i)] [∀ i, IsScalarTower A K (L i)]
    [∀ i, IsScalarTower A K (E i)] [∀ i, Module.Finite K (E i)]
    [∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (B i)) (B i)]
    (D : ∀ i, IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uB, uK, uL, uF, uD₁, uD₂, uD₃}
      A (B i) K (L i) (E i)) (hD : ∀ i, (D i).IsWeakSolution) :
    ∃ (F : Type uK) (_ : Field F) (_ : Algebra K F) (_ : Algebra A F)
      (_ : IsScalarTower A K F) (_ : Module.Finite K F),
      ∀ i, ∃ D' : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA,uB,uK,uL,uK,
        max uL uK,uK,max uL uK} A (B i) K (L i) F, D'.IsWeakSolution := by
  let : PerfectField (IsLocalRing.ResidueField A) := inferInstance
  exact exists_finite_extension_forall_isWeakSolution_of_perfect_residueField
    A K B L E D hD

/-- If every integral field factor after a finite base change admits a weak solution, one further
finite extension solves the original extension.  Perfectness of the intermediate residue field is
enough: it is used only to amalgamate the finitely many factorwise weak solutions. -/
theorem exists_finite_extension_isWeakSolution_of_factor_solutions
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (K₁ : Type uF)
    (R : Type uC)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Module.Finite K K₁]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra A R] [Algebra.IsIntegral A R]
    [Algebra R K₁] [IsFractionRing R K₁]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [PerfectField (IsLocalRing.ResidueField R)]
    {ι : Type v} [Finite ι] (E : ι → Type uD₁) (S : ι → Type uD₂)
    [∀ i, Field (E i)] [∀ i, CommRing (S i)] [∀ i, IsDomain (S i)]
    [∀ i, IsDiscreteValuationRing (S i)]
    [∀ i, Algebra K (E i)] [∀ i, Algebra K₁ (E i)] [∀ i, Algebra L (E i)]
    [∀ i, IsScalarTower K K₁ (E i)]
    [∀ i, Algebra R (S i)] [∀ i, IsDiscreteValuationRing.IsExtension R (S i)]
    [∀ i, Algebra B (S i)] [∀ i, Algebra.IsIntegral B (S i)]
    [∀ i, Algebra R (E i)] [∀ i, Algebra (S i) (E i)]
    [∀ i, IsFractionRing (S i) (E i)]
    [∀ i, IsScalarTower R (S i) (E i)] [∀ i, IsScalarTower R K₁ (E i)]
    [∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (S i)) (S i)]
    (hA : ∀ a : A, algebraMap K K₁ (algebraMap A K a) =
      algebraMap R K₁ (algebraMap A R a))
    (hB : ∀ i b, algebraMap L (E i) (algebraMap B L b) =
      algebraMap (S i) (E i) (algebraMap B (S i) b))
    (hsquare : ∀ i a, algebraMap B (S i) (algebraMap A B a) =
      algebraMap R (S i) (algebraMap A R a))
    (hsol : ∀ i, ∃ (F : Type uF) (_ : Field F) (_ : Algebra K₁ F) (_ : Algebra R F)
      (_ : IsScalarTower R K₁ F) (_ : Module.Finite K₁ F),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uC,uD₂,uF,uD₁,uF,
        max uD₁ uF,uF,max uD₁ uF} R (S i) K₁ (E i) F, D.IsWeakSolution) :
    letI : Algebra K₁ (L ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra K₁ (ReducedTensorTower.Reduction (L ⊗[K] K₁)) :=
      Ideal.Quotient.algebra K₁
    ∀ e : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K₁] ∀ i, E i,
      (∀ i x, e (Ideal.Quotient.mk _ (x ⊗ₜ[K] (1 : K₁))) i = algebraMap L (E i) x) →
      ∃ (F : Type uF) (_ : Field F) (_ : Algebra K F) (_ : Algebra A F)
        (_ : IsScalarTower A K F) (_ : Module.Finite K F),
        ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA,uB,uK,uL,uF,
          max uL uF,uF,max uL uF} A B K L F, D.IsWeakSolution := by
  classical
  let : Algebra K₁ (L ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
  let : Algebra K₁ (ReducedTensorTower.Reduction (L ⊗[K] K₁)) :=
    Ideal.Quotient.algebra K₁
  intro e he
  choose F hF hKF hRF htower hfin D hD using hsol
  let := hF
  let := hKF
  let := hRF
  let := htower
  let := hfin
  obtain ⟨T, hT, hKT, hRT, hRKT, hfinT, hsolT⟩ :=
    exists_finite_extension_forall_isWeakSolution_of_perfect_residueField R K₁ S E F D hD
  let := hT
  let := hKT
  let := hRT
  let := hRKT
  let := hfinT
  let : Algebra K T := ((algebraMap K₁ T).comp (algebraMap K K₁)).toAlgebra
  let : IsScalarTower K K₁ T := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A T := ((algebraMap K T).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K T := IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite K T := Module.Finite.trans (R := K) K₁ T
  obtain ⟨D'⟩ := nonempty_integralClosureBaseChange A B K L T
  refine ⟨T, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, D', ?_⟩
  choose DT hDT using hsolT
  apply isWeakSolution_of_iterated_packages A B K L K₁ T R D' E S
    ?_ hB hsquare DT hDT e he
  intro a
  change algebraMap K₁ T (algebraMap K K₁ (algebraMap A K a)) = _
  rw [hA, ← IsScalarTower.algebraMap_apply R K₁ T]



/-- A weak solution over integral presentations of the two DVRs yields a
canonical weak-solution package for the original DVRs. -/
theorem exists_isWeakSolution_of_integral_ring_extension
    (A : Type uA) (B : Type uB) (R : Type uC) (S : Type uM)
    (K : Type uK) (L : Type uL) (E : Type uF)
    [CommRing A] [CommRing B] [CommRing R] [CommRing S]
    [IsDomain A] [IsDomain B] [IsDomain R] [IsDomain S]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing S]
    [Field K] [Field L] [Field E]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra R S] [Algebra R K] [Algebra R L] [Algebra S L]
    [Algebra K L] [Algebra K E] [Algebra A E] [Algebra R E]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K E]
    [IsScalarTower R S L] [IsScalarTower R K L] [IsScalarTower R K E]
    [IsDiscreteValuationRing.IsExtension A B] [IsDiscreteValuationRing.IsExtension R S]
    [IsFractionRing A K] [IsFractionRing B L]
    [IsFractionRing R K] [IsFractionRing S L] [Module.Finite K E]
    [Algebra A R] [Algebra B S] [Algebra.IsIntegral A R] [Algebra.IsIntegral B S]
    (hA : ∀ a, algebraMap A E a = algebraMap R E (algebraMap A R a))
    (hB : ∀ b, algebraMap B L b = algebraMap S L (algebraMap B S b))
    (D : IsDiscreteValuationRing.IntegralClosureBaseChange R S K L E) (hD : D.IsWeakSolution) :
    ∃ D' : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA,uB,uK,uL,uF,
      max uL uF,uF,max uL uF} A B K L E, D'.IsWeakSolution
    := by
  let : Algebra B D.L₁ := ((algebraMap L D.L₁).comp (algebraMap B L)).toAlgebra
  let : IsScalarTower B L D.L₁ := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A D.L₁ := ((algebraMap B D.L₁).comp (algebraMap A B)).toAlgebra
  let : IsScalarTower A B D.L₁ := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A E D.L₁ := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap L D.L₁ (algebraMap B L (algebraMap A B a)) = _
    rw [← IsScalarTower.algebraMap_apply A B L,
      IsScalarTower.algebraMap_apply A K L,
      ← IsScalarTower.algebraMap_apply K L D.L₁,
      IsScalarTower.algebraMap_apply K E D.L₁,
      ← IsScalarTower.algebraMap_apply A K E]
  have hindices := isWeakSolution_integral_base_change R S K L E D A B hA
    (fun b => by
      change algebraMap L D.L₁ (algebraMap B L b) = _
      rw [hB, ← IsScalarTower.algebraMap_apply S L D.L₁]) hD
  obtain ⟨D'⟩ := nonempty_integralClosureBaseChange A B K L E
  let e : D'.L₁ ≃ₐ[L] D.L₁ :=
    { __ := (D'.eL₁.trans D.eL₁.symm).toRingEquiv
      commutes' x := D.eL₁.symm_apply_eq.mpr ((D'.eL₁_left x).trans (D.eL₁_left x).symm) }
  exact ⟨D', (isWeakSolution_iff_of_reducedCompositum_equiv A B K L E D.L₁ D' e
    fun x => D.eL₁.symm_apply_eq.mpr ((D'.eL₁_right x).trans (D.eL₁_right x).symm)).mpr hindices⟩


/-- Compatible ring equivalences preserve extensions of DVRs. -/
theorem isExtension_of_equiv
    (A B R S : Type*) [CommRing A] [CommRing B] [CommRing R] [CommRing S]
    [IsDomain A] [IsDomain B] [IsDomain R] [IsDomain S]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing S]
    [Algebra A B] [Algebra R S] [IsDiscreteValuationRing.IsExtension A B]
    (eA : A ≃+* R) (eB : B ≃+* S)
    (he : ∀ a, eB (algebraMap A B a) = algebraMap R S (eA a)) :
    IsDiscreteValuationRing.IsExtension R S
    := by
  have hmap : algebraMap R S =
      eB.toRingHom.comp ((algebraMap A B).comp eA.symm.toRingHom) := by
    ext x
    simpa using (he (eA.symm x)).symm
  let : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr (by
    rw [hmap]
    exact eB.injective.comp ((FaithfulSMul.algebraMap_injective A B).comp eA.symm.injective))
  let : IsLocalHom eB.toRingHom := IsLocalHom.of_surjective _ eB.surjective
  let : IsLocalHom eA.symm.toRingHom := IsLocalHom.of_surjective _ eA.symm.surjective
  let : IsLocalHom (algebraMap R S) := by rw [hmap]; infer_instance
  exact ⟨⟩

/-- Compatible ring equivalences preserve weak unramifiedness of DVRs. -/
theorem isWeaklyUnramified_of_equiv
    (A B R S : Type*) [CommRing A] [CommRing B] [CommRing R] [CommRing S]
    [IsDomain A] [IsDomain B] [IsDomain R] [IsDomain S]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing S]
    [Algebra A B] [Algebra R S]
    [IsDiscreteValuationRing.IsExtension A B] [IsDiscreteValuationRing.IsExtension R S]
    (eA : A ≃+* R) (eB : B ≃+* S)
    (he : ∀ a, eB (algebraMap A B a) = algebraMap R S (eA a))
    (h : IsDiscreteValuationRing.IsWeaklyUnramified A B) :
    IsDiscreteValuationRing.IsWeaklyUnramified R S :=
  (isWeaklyUnramified_iff_ramificationIdx_eq_one R S).mpr
    (forall_ramificationIdx_eq_one_of_equiv A B R S eA eB he
      (fun q hq => by
        rw [IsLocalRing.eq_maximalIdeal hq]
        exact (isWeaklyUnramified_iff_ramificationIdx_eq_one A B).mp h)
      (IsLocalRing.maximalIdeal S) (IsLocalRing.maximalIdeal.isMaximal S))

section UniverseTransport

universe w t

attribute [local instance] ULift.algebra'

private noncomputable def reducedTensorProductULiftLeftEquiv
    (K : Type u) (L : Type v) (E : Type w)
    [CommRing K] [CommRing L] [CommRing E]
    [Algebra K L] [Algebra K E] :
    ReducedTensorTower.Reduction (ULift.{t} L ⊗[ULift.{t} K] E) ≃ₐ[K]
      ReducedTensorTower.Reduction (L ⊗[K] E) := by
  let : TensorProduct.CompatibleSMul K (ULift.{t} K) (ULift.{t} L) E :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective _ _ fun x => ⟨x.down, rfl⟩
  exact ReducedTensorTower.reductionEquiv
    ((Algebra.TensorProduct.equivOfCompatibleSMul K (ULift.{t} K) K (ULift.{t} L) E).trans
      (Algebra.TensorProduct.congr ULift.algEquiv (AlgEquiv.refl : E ≃ₐ[K] E)))

private lemma reducedTensorProductULiftLeftEquiv_tmul
    (K : Type u) (L : Type v) (E : Type w)
    [CommRing K] [CommRing L] [CommRing E]
    [Algebra K L] [Algebra K E] (l : L) (e : E) :
    reducedTensorProductULiftLeftEquiv K L E
      (Ideal.Quotient.mk _ ((ULift.up l : ULift.{t} L) ⊗ₜ[ULift.{t} K] e)) =
      Ideal.Quotient.mk _ (l ⊗ₜ[K] e) := by
  rfl



/-- Replacing fraction fields by their canonical universe lifts does not change
whether a finite base extension is a weak solution. -/
theorem exists_isWeakSolution_of_ulift_fraction_fields
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (E : Type uF)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field E]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K E] [Algebra A E]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K E]
    [Module.Finite K E] :
    letI : IsFractionRing A (ULift.{t} K) :=
      IsFractionRing.of_algEquiv (ULift.algEquiv (R := A) (A := K)).symm
    letI : IsFractionRing B (ULift.{t} L) :=
      IsFractionRing.of_algEquiv (ULift.algEquiv (R := B) (A := L)).symm
    letI : IsScalarTower A (ULift.{t} K) (ULift.{t} L) :=
      IsScalarTower.of_algebraMap_eq fun a =>
        congrArg ULift.up (IsScalarTower.algebraMap_apply A K L a)
    letI : IsScalarTower A (ULift.{t} K) E :=
      IsScalarTower.of_algebraMap_eq fun a => IsScalarTower.algebraMap_apply A K E a
    letI : Module.Finite (ULift.{t} K) E :=
      Module.Finite.of_restrictScalars_finite K (ULift.{t} K) E
    ∀ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA,uB,max uK t,max uL t,uF,uD₁,uD₂,uD₃}
        A B (ULift.{t} K) (ULift.{t} L) E,
      D.IsWeakSolution →
      ∃ D' : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA,uB,uK,uL,uF,uD₁,uD₂,uD₃}
        A B K L E, D'.IsWeakSolution
    := by
  let : IsFractionRing A (ULift.{t} K) :=
    IsFractionRing.of_algEquiv (ULift.algEquiv (R := A) (A := K)).symm
  let : IsFractionRing B (ULift.{t} L) :=
    IsFractionRing.of_algEquiv (ULift.algEquiv (R := B) (A := L)).symm
  let : IsScalarTower A (ULift.{t} K) (ULift.{t} L) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      congrArg ULift.up (IsScalarTower.algebraMap_apply A K L a)
  let : IsScalarTower A (ULift.{t} K) E :=
    IsScalarTower.of_algebraMap_eq fun a => IsScalarTower.algebraMap_apply A K E a
  let : Module.Finite (ULift.{t} K) E :=
    Module.Finite.of_restrictScalars_finite K (ULift.{t} K) E
  intro D hD
  let : Algebra (ULift.{t} K) D.L₁ := D.algebraKL₁
  let : Algebra (ULift.{t} L) D.L₁ := D.algebraLL₁
  let : Algebra K D.L₁ :=
    ((algebraMap (ULift.{t} K) D.L₁).comp (algebraMap K (ULift.{t} K))).toAlgebra
  let : Algebra L D.L₁ :=
    ((algebraMap (ULift.{t} L) D.L₁).comp (algebraMap L (ULift.{t} L))).toAlgebra
  let : @IsScalarTower K (ULift.{t} K) D.L₁
      (inferInstance : Algebra K (ULift.{t} K)).toSMul
      (inferInstance : Algebra (ULift.{t} K) D.L₁).toSMul
      (inferInstance : Algebra K D.L₁).toSMul :=
    IsScalarTower.of_algebraMap_eq' (R := K) (S := ULift.{t} K) (A := D.L₁) rfl
  let : IsScalarTower K L D.L₁ := IsScalarTower.of_algebraMap_eq fun x =>
    IsScalarTower.algebraMap_apply (ULift.{t} K) (ULift.{t} L) D.L₁ (ULift.up x)
  let : IsScalarTower K E D.L₁ := IsScalarTower.of_algebraMap_eq fun x =>
    IsScalarTower.algebraMap_apply (ULift.{t} K) E D.L₁ (ULift.up x)
  let : IsScalarTower B L D.L₁ := IsScalarTower.of_algebraMap_eq fun x =>
    IsScalarTower.algebraMap_apply B (ULift.{t} L) D.L₁ x
  let e := (D.eL₁.restrictScalars K).trans (reducedTensorProductULiftLeftEquiv K L E)
  let D' : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA,uB,uK,uL,uF,uD₁,uD₂,uD₃}
      A B K L E :=
    { L₁ := D.L₁
      A₁ := D.A₁
      B₁ := D.B₁
      eL₁ := e
      eL₁_left := fun x => by
        change reducedTensorProductULiftLeftEquiv K L E
          (D.eL₁ (algebraMap (ULift.{t} L) D.L₁ (ULift.up x))) = _
        rw [D.eL₁_left]
        exact reducedTensorProductULiftLeftEquiv_tmul K L E x 1
      eL₁_right := fun x => by
        change reducedTensorProductULiftLeftEquiv K L E (D.eL₁ (algebraMap E D.L₁ x)) = _
        rw [D.eL₁_right]
        exact reducedTensorProductULiftLeftEquiv_tmul K L E 1 x
      ringSquare := D.ringSquare }
  exact ⟨D', hD⟩

end UniverseTransport

end IsDiscreteValuationRing
