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

open Stacks.DegreePExtensionLevel
open Stacks.DiscreteValuationRing.EppLevelInduction

/-!
# Eliminating ramification: the totally ramified and purely inseparable cases

Reductions of tensor products by the nilradical, the totally ramified case, the purely
inseparable case, and weak solutions along iterated factors.

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

private def tensorProductBaseChangeRightAssoc
    (R S T U : Type*) [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra R U] :
    letI : Algebra S (U ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
    ((U ⊗[R] S) ⊗[S] T) ≃ₐ[R] U ⊗[R] T := by
  let : Algebra S (U ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  let e : (U ⊗[R] S) ≃ₐ[S] S ⊗[R] U :=
    { Algebra.TensorProduct.comm R U S with
      commutes' := fun s => by
        change (Algebra.TensorProduct.comm R U S) (1 ⊗ₜ[R] s) = s ⊗ₜ[R] 1
        rfl }
  exact (((Algebra.TensorProduct.comm S (U ⊗[R] S) T).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[S] T) e)).trans
      (Algebra.TensorProduct.cancelBaseChange R S S T U)).restrictScalars R |>.trans
        (Algebra.TensorProduct.comm R T U)

private lemma tensorProductBaseChangeRightAssoc_tmul
    (R S T U : Type*) [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra R U] (u : U) (s : S) (t : T) :
    letI : Algebra S (U ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
    tensorProductBaseChangeRightAssoc R S T U ((u ⊗ₜ[R] s) ⊗ₜ[S] t) =
      u ⊗ₜ[R] (algebraMap S T s * t) := by
  simp [tensorProductBaseChangeRightAssoc, Algebra.smul_def]

/-- Quotienting by a nil ideal sends the nilradical onto the nilradical. -/
private theorem map_nilradical_quotient
    (A : Type*) [CommRing A] (I : Ideal A) (hI : I ≤ nilradical A) :
    (nilradical A).map (Ideal.Quotient.mk I) = nilradical (A ⧸ I) := by
  have hrad : I.radical = nilradical A :=
    le_antisymm (Ideal.radical_le_radical_iff.mpr hI) (Ideal.radical_mono bot_le)
  rw [← hrad, Ideal.map_radical_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]), Ideal.map_quotient_self]
  rfl

/-- Reduction is unaffected by first quotienting by a nil ideal. -/
private noncomputable def reductionQuotientEquiv
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal A) (hI : I ≤ nilradical A) :
    ReducedTensorTower.Reduction (A ⧸ I) ≃ₐ[R] ReducedTensorTower.Reduction A :=
  (Ideal.quotientEquivAlgOfEq R (map_nilradical_quotient A I hI).symm).trans
    (DoubleQuot.quotQuotEquivQuotOfLEₐ R hI)

private lemma reductionQuotientEquiv_mk
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal A) (hI : I ≤ nilradical A) (x : A) :
    reductionQuotientEquiv R A I hI (Ideal.Quotient.mk _ (Ideal.Quotient.mk I x)) =
      Ideal.Quotient.mk _ x := rfl

/-- Reducing one tensor factor does not alter the reduction of the tensor product. -/
private noncomputable def reductionTensorEquiv
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    ReducedTensorTower.Reduction ((ReducedTensorTower.Reduction A) ⊗[R] B) ≃ₐ[R]
      ReducedTensorTower.Reduction (A ⊗[R] B) :=
  (ReducedTensorTower.reductionEquiv
    (Algebra.TensorProduct.quotientTensorEquiv R B A (nilradical A))).trans
    (reductionQuotientEquiv R (A ⊗[R] B) _
      (Ideal.map_le_iff_le_comap.mpr fun _ hx =>
        mem_nilradical.mpr ((mem_nilradical.mp hx).map (algebraMap A (A ⊗[R] B)))))

private lemma reductionTensorEquiv_tmul
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (a : A) (b : B) :
    reductionTensorEquiv R A B
        (Ideal.Quotient.mk _ ((Ideal.Quotient.mk _ a) ⊗ₜ[R] b)) =
      Ideal.Quotient.mk _ (a ⊗ₜ[R] b) := by
  simp only [reductionTensorEquiv, AlgEquiv.trans_apply,
    ReducedTensorTower.reductionEquiv_mk,
    Algebra.TensorProduct.quotientTensorEquiv_apply_tmul, reductionQuotientEquiv_mk]
/-- The reduced compositum formed in two finite base changes agrees with the one
formed in their composite base extension. -/
private noncomputable def reducedTensorBaseChangeRightAssoc
    (R S T U : Type*) [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra R U] :
    letI : Algebra S (U ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra S (ReducedTensorTower.Reduction (U ⊗[R] S)) := Ideal.Quotient.algebra S
    ReducedTensorTower.Reduction ((ReducedTensorTower.Reduction (U ⊗[R] S)) ⊗[S] T) ≃ₐ[R]
      ReducedTensorTower.Reduction (U ⊗[R] T) := by
  letI : Algebra S (U ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra S (ReducedTensorTower.Reduction (U ⊗[R] S)) := Ideal.Quotient.algebra S
  exact ((reductionTensorEquiv S (U ⊗[R] S) T).restrictScalars R).trans
    (ReducedTensorTower.reductionEquiv (tensorProductBaseChangeRightAssoc R S T U))

private lemma reducedTensorBaseChangeRightAssoc_tmul
    (R S T U : Type*) [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra R U] (u : U) (s : S) (t : T) :
    letI : Algebra S (U ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra S (ReducedTensorTower.Reduction (U ⊗[R] S)) := Ideal.Quotient.algebra S
    reducedTensorBaseChangeRightAssoc R S T U
      (Ideal.Quotient.mk _ ((Ideal.Quotient.mk _ (u ⊗ₜ[R] s)) ⊗ₜ[S] t)) =
        Ideal.Quotient.mk _ (u ⊗ₜ[R] (algebraMap S T s * t)) := by
  simp only [reducedTensorBaseChangeRightAssoc, AlgEquiv.trans_apply,
    AlgEquiv.coe_restrictScalars, reductionTensorEquiv_tmul,
    ReducedTensorTower.reductionEquiv_mk, tensorProductBaseChangeRightAssoc_tmul]


/-- Reduction commutes with finite products of commutative algebras. -/
private noncomputable def reductionPiEquiv
    (R : Type*) [CommRing R] {ι : Type*} [Finite ι]
    (A : ι → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] :
    ReducedTensorTower.Reduction (∀ i, A i) ≃ₐ[R] ∀ i, ReducedTensorTower.Reduction (A i) := by
  let f : (∀ i, A i) →ₐ[R] ∀ i, ReducedTensorTower.Reduction (A i) :=
    AlgHom.pi fun i => (Ideal.Quotient.mkₐ R _).comp (Pi.evalAlgHom R A i)
  let g := Ideal.Quotient.liftₐ (nilradical (∀ i, A i)) f (by
    intro x hx
    ext i
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (mem_nilradical.mpr ((isNilpotent_pi_iff x).mp (mem_nilradical.mp hx) i)))
  refine AlgEquiv.ofBijective g ⟨?_, ?_⟩
  · intro x y h
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    apply Ideal.Quotient.eq.mpr
    rw [mem_nilradical, isNilpotent_pi_iff]
    intro i
    exact mem_nilradical.mp (Ideal.Quotient.eq.mp (congrFun h i))
  · intro y
    choose x hx using fun i => Ideal.Quotient.mk_surjective (y i)
    exact ⟨Ideal.Quotient.mk _ x, funext hx⟩

private lemma reductionPiEquiv_mk
    (R : Type*) [CommRing R] {ι : Type*} [Finite ι]
    (A : ι → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    (x : ∀ i, A i) (i : ι) :
    reductionPiEquiv R A (Ideal.Quotient.mk _ x) i = Ideal.Quotient.mk _ (x i) := rfl

/-- Tensoring a finite product and then reducing can be computed factor by factor. -/
private noncomputable def reducedTensorPiEquiv
    (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
    {ι : Type*} [Finite ι] (A : ι → Type*)
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] :
    ReducedTensorTower.Reduction ((∀ i, A i) ⊗[R] B) ≃ₐ[R]
      ∀ i, ReducedTensorTower.Reduction (A i ⊗[R] B) := by
  classical
  letI := Fintype.ofFinite ι
  let e : ((∀ i, A i) ⊗[R] B) ≃ₐ[R] ∀ i, A i ⊗[R] B :=
    ((Algebra.TensorProduct.comm R (∀ i, A i) B).trans
      (Algebra.TensorProduct.piRight R R B A)).trans
      (AlgEquiv.piCongrRight fun i => Algebra.TensorProduct.comm R B (A i))
  exact (ReducedTensorTower.reductionEquiv e).trans
    (reductionPiEquiv R (fun i => A i ⊗[R] B))

private lemma reducedTensorPiEquiv_tmul
    (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
    {ι : Type*} [Finite ι] (A : ι → Type*)
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    (x : ∀ i, A i) (b : B) (i : ι) :
    reducedTensorPiEquiv R B A (Ideal.Quotient.mk _ (x ⊗ₜ[R] b)) i =
      Ideal.Quotient.mk _ (x i ⊗ₜ[R] b) := by
  classical
  simp [reducedTensorPiEquiv, ReducedTensorTower.reductionEquiv_mk,
    reductionPiEquiv_mk, Algebra.TensorProduct.piRight_tmul]


/-- After a finite product decomposition of the first reduced base change, the
composite reduced base change is the product of the reduced base changes of its factors. -/
private noncomputable def reducedTensorBaseChangePiEquiv
    (R S T U : Type*) [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] [Algebra R U]
    {ι : Type*} [Finite ι] (E : ι → Type*) [∀ i, CommRing (E i)]
    [∀ i, Algebra S (E i)] [∀ i, Algebra R (E i)] [∀ i, IsScalarTower R S (E i)] :
    letI : Algebra S (U ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra S (ReducedTensorTower.Reduction (U ⊗[R] S)) := Ideal.Quotient.algebra S
    (ReducedTensorTower.Reduction (U ⊗[R] S) ≃ₐ[S] ∀ i, E i) →
      ReducedTensorTower.Reduction (U ⊗[R] T) ≃ₐ[R]
        ∀ i, ReducedTensorTower.Reduction (E i ⊗[S] T) := by
  letI : Algebra S (U ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra S (ReducedTensorTower.Reduction (U ⊗[R] S)) := Ideal.Quotient.algebra S
  intro e
  exact (reducedTensorBaseChangeRightAssoc R S T U).symm.trans
    (((ReducedTensorTower.reductionEquiv
      (Algebra.TensorProduct.congr e (AlgEquiv.refl : T ≃ₐ[S] T))).trans
        (reducedTensorPiEquiv S T E)).restrictScalars R)

private lemma reducedTensorBaseChangePiEquiv_tmul
    (R S T U : Type*) [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] [Algebra R U]
    {ι : Type*} [Finite ι] (E : ι → Type*) [∀ i, CommRing (E i)]
    [∀ i, Algebra S (E i)] [∀ i, Algebra R (E i)] [∀ i, IsScalarTower R S (E i)] :
    letI : Algebra S (U ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra S (ReducedTensorTower.Reduction (U ⊗[R] S)) := Ideal.Quotient.algebra S
    ∀ (e : ReducedTensorTower.Reduction (U ⊗[R] S) ≃ₐ[S] ∀ i, E i)
      (u : U) (t : T) (i : ι),
      reducedTensorBaseChangePiEquiv R S T U E e (Ideal.Quotient.mk _ (u ⊗ₜ[R] t)) i =
        Ideal.Quotient.mk _ ((e (Ideal.Quotient.mk _ (u ⊗ₜ[R] (1 : S))) i) ⊗ₜ[S] t) := by
  let : Algebra S (U ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  let : Algebra S (ReducedTensorTower.Reduction (U ⊗[R] S)) := Ideal.Quotient.algebra S
  intro e u t i
  have h := reducedTensorBaseChangeRightAssoc_tmul R S T U u 1 t
  simp only [map_one, one_mul] at h
  rw [← h]
  simp only [reducedTensorBaseChangePiEquiv, AlgEquiv.trans_apply,
    AlgEquiv.symm_apply_apply, AlgEquiv.coe_restrictScalars,
    ReducedTensorTower.reductionEquiv_mk, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom, AlgEquiv.refl_toAlgHom,
    AlgHom.id_apply, reducedTensorPiEquiv_tmul]



/-- The weak-solution condition is invariant under a compatible presentation of
the reduced compositum. -/
theorem isWeakSolution_iff_of_reducedCompositum_equiv
    (A B K L K₁ F : Type*)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁] [CommRing F]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁]
    [Algebra L F] [Algebra B F] [Algebra A F] [Algebra K₁ F]
    [IsScalarTower B L F] [IsScalarTower A B F] [IsScalarTower A K₁ F]
    (D : IsDiscreteValuationRing.IntegralClosureBaseChange A B K L K₁)
    (e : D.L₁ ≃ₐ[L] F)
    (he : ∀ x : K₁, e (algebraMap K₁ D.L₁ x) = algebraMap K₁ F x) :
    letI : Algebra (integralClosure A K₁) (integralClosure B F) :=
      (mapIntegralClosureOfTower A B K₁ F).toRingHom.toAlgebra
    D.IsWeakSolution ↔ ∀ q : Ideal (integralClosure B F), q.IsMaximal →
      q.ramificationIdx (integralClosure A K₁) = 1 := by
  let A₁ := integralClosure A K₁
  let B₁ := integralClosure B F
  let : Algebra A₁ B₁ := (mapIntegralClosureOfTower A B K₁ F).toRingHom.toAlgebra
  let eA := IsIntegralClosure.equiv A D.A₁ K₁ A₁
  let eB : D.B₁ ≃ₐ[B] B₁ :=
    (IsIntegralClosure.equiv B D.B₁ D.L₁ (integralClosure B D.L₁)).trans
      (e.restrictScalars B).mapIntegralClosure
  have heB (x : D.B₁) : (eB x : F) = e (algebraMap D.B₁ D.L₁ x) := by
    change e (algebraMap (integralClosure B D.L₁) D.L₁
      (IsIntegralClosure.equiv B D.B₁ D.L₁ (integralClosure B D.L₁) x)) = _
    rw [IsIntegralClosure.algebraMap_equiv]
  have hsquare (x : D.A₁) :
      eB (algebraMap D.A₁ D.B₁ x) = algebraMap A₁ B₁ (eA x) := by
    apply Subtype.ext
    change (eB (algebraMap D.A₁ D.B₁ x) : F) =
      (mapIntegralClosureOfTower A B K₁ F (eA x) : F)
    rw [heB, D.ringSquare, he, mapIntegralClosureOfTower_apply]
    rw [show (eA x : K₁) = algebraMap D.A₁ K₁ x from
      IsIntegralClosure.algebraMap_equiv A D.A₁ K₁ A₁ x]
  constructor
  · exact forall_ramificationIdx_eq_one_of_equiv D.A₁ D.B₁ A₁ B₁
      eA.toRingEquiv eB.toRingEquiv hsquare
  · apply forall_ramificationIdx_eq_one_of_equiv A₁ B₁ D.A₁ D.B₁
      eA.symm.toRingEquiv eB.symm.toRingEquiv
    intro x
    apply eB.injective
    change eB (eB.symm (algebraMap A₁ B₁ x)) =
      eB (algebraMap D.A₁ D.B₁ (eA.symm x))
    rw [AlgEquiv.apply_symm_apply, hsquare, AlgEquiv.apply_symm_apply]


/-- Equality of the extended maximal ideal with the maximal ideal upstairs
implies ramification index one at every maximal ideal. -/
theorem forall_ramificationIdx_eq_one_of_map_maximalIdeal
    (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S]
    (h : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal S) :
    ∀ q : Ideal S, q.IsMaximal → q.ramificationIdx R = 1 := by
  intro q hq
  let : q.IsMaximal := hq
  have heq : q = IsLocalRing.maximalIdeal S := IsLocalRing.eq_maximalIdeal hq
  apply ramificationIdx_eq_one_of_map_under_eq R S q
  have hu : q.under R = IsLocalRing.maximalIdeal R := by
    apply (Ideal.IsMaximal.eq_of_le (IsLocalRing.maximalIdeal.isMaximal R)
      (Ideal.comap_ne_top _ hq.ne_top) ?_).symm
    exact Ideal.map_le_iff_le_comap.mp (by rw [h, heq])
  rw [hu, h, heq]


/-- If the tensor product is a field, a compatible weakly unramified map between
its integral closures is a weak solution in the reduced-compositum formulation. -/
private theorem isWeakSolution_of_isField_tensorProduct
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
    (hfield : IsField (L ⊗[K] K₁))
    (f : integralClosure A K₁ →+* integralClosure B (L ⊗[K] K₁))
    (hf : ∀ x : integralClosure A K₁,
      (f x : L ⊗[K] K₁) = Algebra.TensorProduct.includeRight (x : K₁))
    (hmax : ∀ q : Ideal (integralClosure B (L ⊗[K] K₁)), q.IsMaximal →
      letI : Algebra (integralClosure A K₁) (integralClosure B (L ⊗[K] K₁)) := f.toAlgebra
      q.ramificationIdx (integralClosure A K₁) = 1) : D.IsWeakSolution := by
  let T := L ⊗[K] K₁
  let : Field T := hfield.toField
  let : Algebra K₁ T := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower A K₁ T := IsScalarTower.of_algebraMap_eq fun x => by
    change (Algebra.TensorProduct.includeLeft : L →ₐ[K] T) (algebraMap A L x) =
      (Algebra.TensorProduct.includeRight : K₁ →ₐ[K] T) (algebraMap A K₁ x)
    rw [IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A K K₁,
      AlgHom.commutes, AlgHom.commutes]
  let e0 : (T ⧸ nilradical T) ≃ₐ[K] T :=
    (Ideal.quotientEquivAlgOfEq K (nilradical_eq_zero T)).trans (AlgEquiv.quotientBot K T)
  let e : D.L₁ ≃ₐ[L] T :=
    { __ := (D.eL₁.trans e0).toRingEquiv
      commutes' x := by
        change e0 (D.eL₁ (algebraMap L D.L₁ x)) = algebraMap L T x
        rw [D.eL₁_left]
        rfl }
  apply (isWeakSolution_iff_of_reducedCompositum_equiv A B K L K₁ T D e ?_).mpr
  · have hf' : f = (mapIntegralClosureOfTower A B K₁ T).toRingHom := by
      ext x
      exact hf x
    subst f
    exact hmax
  · intro x
    change e0 (D.eL₁ (algebraMap K₁ D.L₁ x)) = algebraMap K₁ T x
    rw [D.eL₁_right]
    rfl

/-- A weakly unramified extension of DVRs extends the maximal ideal to the maximal ideal. -/
private theorem map_maximalIdeal_eq_of_isWeaklyUnramified
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B]
    [IsDiscreteValuationRing.IsExtension A B]
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B) :
    Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal B := by
  simpa only [show IsDiscreteValuationRing.ramificationIndex A B = 1 from hweak, pow_one] using
    (IsDiscreteValuationRing.ramificationIndex_characterization A B).2.1

/-- A totally ramified finite separable base extension preserves a weakly unramified DVR
extension, packaged in the reduced-compositum formulation of a weak solution.

This is the package-level form of Tag 09ER for one field factor.  In particular it needs no
completeness or algebraic-closedness hypothesis on the residue field: total ramification is the
input that makes the tensor product a field and preserves ramification index one. -/
theorem exists_isWeakSolution_of_isWeaklyUnramified_of_totallyRamified
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (K₁ : Type uK₁)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁]
    [Algebra A B] [IsDiscreteValuationRing.IsExtension A B]
    [Algebra A K] [Algebra B L] [Algebra A L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsFractionRing A K] [IsFractionRing B L]
    [Algebra K K₁] [Algebra A K₁] [IsScalarTower A K K₁]
    [FiniteDimensional K K₁] [Algebra.IsSeparable K K₁]
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B)
    (htot : IsDiscreteValuationRing.IsTotallyRamifiedWithRespectTo A K K₁) :
    ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁,
        max uL uK₁, uK₁, max uL uK₁} A B K L K₁, D.IsWeakSolution := by
  have hmap := map_maximalIdeal_eq_of_isWeaklyUnramified A B hweak
  obtain ⟨hL₁, hA₁, hBdom, hB₁, -, -, hCdom, hC₁, hfrac, e, hsquare, -, hmax⟩ :=
    IsDiscreteValuationRing.isField_tensorProduct_and_isDVR_baseChange_of_totallyRamified
      A B K L K₁ hmap htot
  let : Field (L ⊗[K] K₁) := hL₁.toField
  let : IsDiscreteValuationRing (integralClosure A K₁) := hA₁
  let : IsDomain (B ⊗[A] integralClosure A K₁) := hBdom
  let : IsDiscreteValuationRing (B ⊗[A] integralClosure A K₁) := hB₁
  let : IsDomain (integralClosure B (L ⊗[K] K₁)) := hCdom
  let : IsDiscreteValuationRing (integralClosure B (L ⊗[K] K₁)) := hC₁
  let : IsFractionRing (integralClosure B (L ⊗[K] K₁)) (L ⊗[K] K₁) := hfrac
  let f : integralClosure A K₁ →+* integralClosure B (L ⊗[K] K₁) :=
    e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom
  obtain ⟨D⟩ := nonempty_integralClosureBaseChange A B K L K₁
  refine ⟨D, isWeakSolution_of_isField_tensorProduct A B K L K₁ D hL₁ f hsquare ?_⟩
  let : Algebra (integralClosure A K₁) (integralClosure B (L ⊗[K] K₁)) := f.toAlgebra
  exact forall_ramificationIdx_eq_one_of_map_maximalIdeal
    (integralClosure A K₁) (integralClosure B (L ⊗[K] K₁)) hmax

/-- A purely inseparable field extension embedded in a reduced algebra disappears
when its tensor product is reduced. -/
private noncomputable def reducedTensorEquivOfIsPurelyInseparable
    (K E R : Type*) [Field K] [Field E] [CommRing R] [IsReduced R]
    [Algebra K E] [Algebra K R] [IsPurelyInseparable K E]
    (f : E →ₐ[K] R) :
    ReducedTensorTower.Reduction (R ⊗[K] E) ≃ₐ[K] R := by
  let g : R ⊗[K] E →ₐ[K] R := Algebra.TensorProduct.lift (AlgHom.id K R) f
    (fun _ _ => Commute.all _ _)
  have hg (r : R) : g (algebraMap R (R ⊗[K] E) r) = r := by
    change g (r ⊗ₜ[K] 1) = r
    simp [g]
  let h : ReducedTensorTower.Reduction (R ⊗[K] E) →ₐ[K] R :=
    Ideal.Quotient.liftₐ _ g (fun x hx =>
      (mem_nilradical.mp hx).map g |>.eq_zero)
  refine AlgEquiv.ofBijective h ⟨?_, ?_⟩
  · apply (injective_iff_map_eq_zero h).mpr
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change g x = 0 at hx
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    obtain ⟨n, _, r, hr⟩ := IsPurelyInseparable.exists_pow_mem_range_tensorProduct x
    have hr0 : r = 0 := by
      have ht := congrArg g hr
      rwa [hg, map_pow, hx, zero_pow (by omega)] at ht
    rw [hr0, map_zero] at hr
    exact mem_nilradical.mpr ⟨n, hr.symm⟩
  · intro r
    exact ⟨Ideal.Quotient.mk _ (algebraMap R (R ⊗[K] E) r), hg r⟩

private lemma reducedTensorEquivOfIsPurelyInseparable_tmul
    (K E R : Type*) [Field K] [Field E] [CommRing R] [IsReduced R]
    [Algebra K E] [Algebra K R] [IsPurelyInseparable K E]
    (f : E →ₐ[K] R) (r : R) (e : E) :
    reducedTensorEquivOfIsPurelyInseparable K E R f
      (Ideal.Quotient.mk _ (r ⊗ₜ[K] e)) = r * f e :=
  rfl


private theorem isPurelyInseparable_of_adjoin_eq_top_of_pow_mem
    (K E : Type*) [Field K] [Field E] [Algebra K E]
    (p : ℕ) [ExpChar K p] (x : E)
    (hgen : Algebra.adjoin K {x} = ⊤)
    (hx : ∃ n : ℕ, x ^ p ^ n ∈ (algebraMap K E).range) :
    IsPurelyInseparable K E := by
  let : ExpChar E p := expChar_of_injective_ringHom (algebraMap K E).injective p
  let S := Subalgebra.perfectClosure K E p
  have hS : S = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hx)
  exact (isPurelyInseparable_iff_pow_mem K p).mpr fun y =>
    Subalgebra.mem_perfectClosure_iff.mp (show y ∈ S by simp [hS])

private theorem isPurelyInseparable_adjoinRoot_X_pow_sub_C
    (K : Type*) [Field K] (p : ℕ) [ExpChar K p] (a : K)
    [Fact (Irreducible (Polynomial.X ^ p - Polynomial.C a))] :
    IsPurelyInseparable K (AdjoinRoot (Polynomial.X ^ p - Polynomial.C a)) := by
  apply isPurelyInseparable_of_adjoin_eq_top_of_pow_mem K _ p
    (AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C a)) AdjoinRoot.adjoinRoot_eq_top
  refine ⟨1, a, ?_⟩
  have h := AdjoinRoot.eval₂_root (Polynomial.X ^ p - Polynomial.C a)
  simpa using (sub_eq_zero.mp (by simpa using h)).symm

private theorem isWeaklyUnramified_of_ramificationIndex_le
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [IsDomain R] [IsDomain S] [IsDomain T]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing S] [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [IsDiscreteValuationRing.IsExtension R S] [IsDiscreteValuationRing.IsExtension S T]
    [IsDiscreteValuationRing.IsExtension R T]
    (h : IsDiscreteValuationRing.ramificationIndex R T ≤
      IsDiscreteValuationRing.ramificationIndex R S) :
    IsDiscreteValuationRing.IsWeaklyUnramified S T := by
  have hRS := (IsDiscreteValuationRing.ramificationIndex_characterization R S).1
  have hST := (IsDiscreteValuationRing.ramificationIndex_characterization S T).1
  have hmul := Ideal.ramificationIdx_tower (R := R)
    (IsLocalRing.maximalIdeal S) (IsLocalRing.maximalIdeal T)
  rw [← ramificationIndex_eq_ramificationIdx R T,
    ← ramificationIndex_eq_ramificationIdx R S,
    ← ramificationIndex_eq_ramificationIdx S T] at hmul
  change IsDiscreteValuationRing.ramificationIndex S T = 1
  nlinarith


/-- In residue characteristic `p`, a `p`th root of a base uniformizer eliminates
ramification when the original ramification index is at most `p`. -/
private theorem exists_finite_extension_isWeakSolution_of_uniformizer_root
    (A : Type uA) (C : Type uC) (K : Type uK) (M : Type uM)
    [CommRing A] [CommRing C] [IsDomain A] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing C]
    [Field K] [Field M]
    [Algebra A C] [Algebra A K] [Algebra A M] [Algebra C M] [Algebra K M]
    [IsDiscreteValuationRing.IsExtension A C] [IsFractionRing A K] [IsFractionRing C M]
    [IsScalarTower A C M] [IsScalarTower A K M]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : A) (hπ : Irreducible π) (x : C) (hx : x ^ p = algebraMap A C π)
    (hbound : IsDiscreteValuationRing.ramificationIndex A C ≤ p) :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA,uC,uK,uM,uK,
          max uM uK,uK,max uM uK} A C K M K₁, D.IsWeakSolution := by
  classical
  have hp : p.Prime := Fact.out
  let : Fact (Irreducible (Stacks.KummerExtension.kummerPoly K π p)) :=
    ⟨Stacks.KummerExtension.kummerPoly_irreducible K π p hp.pos hπ⟩
  let K₁ := Stacks.KummerExtension.K1 K π p
  let : Module.Finite K K₁ := Module.finite_of_finrank_pos
    (by rw [Stacks.KummerExtension.finrank_K1 K π p hp.two_le hπ]; exact hp.pos)
  have hroot : Polynomial.eval₂ (algebraMap K M) (algebraMap C M x)
      (Stacks.KummerExtension.kummerPoly K π p) = 0 := by
    simp only [Stacks.KummerExtension.kummerPoly, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
      Polynomial.eval₂_C, ← map_pow, hx, ← IsScalarTower.algebraMap_apply A C M,
      ← IsScalarTower.algebraMap_apply A K M, sub_self]
  let f : K₁ →ₐ[K] M := AdjoinRoot.liftAlgHom _ (Algebra.ofId K M) _ hroot
  let : Algebra K₁ M := f.toRingHom.toAlgebra
  let : IsScalarTower K K₁ M := IsScalarTower.of_algHom f
  let : IsScalarTower A K₁ M := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A K M, IsScalarTower.algebraMap_apply A K K₁,
      ← IsScalarTower.algebraMap_apply K K₁ M]
  let : Fact (Irreducible (Polynomial.X ^ p - Polynomial.C (algebraMap A K π))) :=
    ⟨by simpa [Stacks.KummerExtension.kummerPoly] using
      (Stacks.KummerExtension.kummerPoly_irreducible K π p hp.pos hπ)⟩
  let : IsPurelyInseparable K K₁ := isPurelyInseparable_adjoinRoot_X_pow_sub_C K p
    (algebraMap A K π)
  obtain ⟨hA₁, hAA₁, hAfin, hAc, hAf⟩ := integralClosure_isCompleteDVR A K K₁
  let A₁ := integralClosure A K₁
  let := hA₁
  let := hAA₁
  let eC := IsIntegralClosure.equiv C C M (integralClosure C M)
  let fA : A₁ →+* C := eC.symm.toRingHom.comp
    (mapIntegralClosureOfTower A C K₁ M).toRingHom
  have hfA (a : A₁) : algebraMap C M (fA a) = algebraMap K₁ M (a : K₁) :=
    IsIntegralClosure.algebraMap_equiv C (integralClosure C M) M C
      (mapIntegralClosureOfTower A C K₁ M a)
  let : Algebra A₁ C := fA.toAlgebra
  let : IsScalarTower A A₁ C := IsScalarTower.of_algebraMap_eq fun a => by
    apply IsFractionRing.injective C M
    change algebraMap C M (algebraMap A C a) = algebraMap C M (fA (algebraMap A A₁ a))
    rw [hfA, ← IsScalarTower.algebraMap_apply A C M]
    exact (IsScalarTower.algebraMap_apply A K₁ M a)
  let : FaithfulSMul A₁ C := (faithfulSMul_iff_algebraMap_injective A₁ C).mpr (by
    intro a b h
    apply Subtype.ext
    apply (algebraMap K₁ M).injective
    change fA a = fA b at h
    simpa only [hfA] using congrArg (algebraMap C M) h)
  let : IsLocalHom (algebraMap A₁ C) := isLocalHom_of_isIntegral_tower A A₁ C
  let : IsDiscreteValuationRing.IsExtension A₁ C := ⟨⟩
  obtain ⟨m, hmmax, hmlo, _, hmidx⟩ := Stacks.KummerExtension.exists_ramificationIdx_eq K π p
    hp.two_le hπ
  let : m.IsMaximal := hmmax
  let : m.LiesOver (IsLocalRing.maximalIdeal A) := hmlo
  have hidx : IsDiscreteValuationRing.ramificationIndex A A₁ = p := by
    rw [ramificationIndex_eq_ramificationIdx A A₁,
      ← IsLocalRing.eq_maximalIdeal hmmax,
      ← Ideal.ramificationIdx'_eq_ramificationIdx
        (IsLocalRing.maximalIdeal A) m (IsDiscreteValuationRing.not_a_field A)]
    exact hmidx
  have hweak : IsDiscreteValuationRing.IsWeaklyUnramified A₁ C :=
    isWeaklyUnramified_of_ramificationIndex_le A A₁ C (by rwa [hidx])
  obtain ⟨D⟩ := nonempty_integralClosureBaseChange A C K M K₁
  refine ⟨K₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, D, ?_⟩
  let e0 := reducedTensorEquivOfIsPurelyInseparable K K₁ M f
  let e : D.L₁ ≃ₐ[M] M :=
    { __ := (D.eL₁.trans e0).toRingEquiv
      commutes' y := by
        change e0 (D.eL₁ (algebraMap M D.L₁ y)) = y
        rw [D.eL₁_left]
        change e0 (Ideal.Quotient.mk _ (y ⊗ₜ[K] (1 : K₁))) = y
        rw [reducedTensorEquivOfIsPurelyInseparable_tmul, map_one, mul_one] }
  apply (isWeakSolution_iff_of_reducedCompositum_equiv A C K M K₁ M D e ?_).mpr
  · apply forall_ramificationIdx_eq_one_integralClosure A C K₁ M A₁ C hfA
    apply forall_ramificationIdx_eq_one_of_map_maximalIdeal A₁ C
    exact map_maximalIdeal_eq_of_isWeaklyUnramified A₁ C hweak
  · intro y
    change e0 (D.eL₁ (algebraMap K₁ D.L₁ y)) = algebraMap K₁ M y
    rw [D.eL₁_right]
    change e0 (Ideal.Quotient.mk _ ((1 : M) ⊗ₜ[K] y)) = f y
    rw [reducedTensorEquivOfIsPurelyInseparable_tmul, one_mul]


/-- A purely inseparable prime-degree step over a complete weakly unramified
DVR tower has a finite weak solution. -/
theorem exists_finite_extension_isWeakSolution_of_isPurelyInseparable
    (A B C K L M : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsDiscreteValuationRing.IsExtension A B] [IsDiscreteValuationRing.IsExtension B C]
    [IsDiscreteValuationRing.IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Module.Finite L M] [IsPurelyInseparable L M]
    (p : ℕ) [Fact p.Prime] (hdegree : Module.finrank L M = p)
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B) :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{u,u,u,u,u,u,u,u}
          A C K M K₁, D.IsWeakSolution := by
  have hp : p.Prime := Fact.out
  let : CharP L p := charP_of_finrank_eq_prime L M hp hdegree
  let : CharP K p := (algebraMap K L).charP (algebraMap K L).injective p
  let : IsScalarTower A B M := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A C M, IsScalarTower.algebraMap_apply A B C,
      ← IsScalarTower.algebraMap_apply B C M]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hmap := map_maximalIdeal_eq_of_isWeaklyUnramified A B hweak
  obtain h | ⟨x, hx, _⟩ | h :=
    IsDiscreteValuationRing.weaklyUnramified_or_adjoin_root_or_after_totallyRamified_baseChange
      A B C K L M p hdegree π hπ IsNagataRing.of_isPrecomplete_maximalIdeal hmap
  · obtain ⟨D⟩ := nonempty_integralClosureBaseChange A C K M K
    refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      D, isWeakSolution_self A C K M D ?_⟩
    exact (isWeaklyUnramified_iff_ramificationIdx_eq_one A C).mpr
      (forall_ramificationIdx_eq_one_of_map_maximalIdeal A C h _ inferInstance)
  · apply exists_finite_extension_isWeakSolution_of_uniformizer_root A C K M p π hπ x hx
    obtain ⟨hres, hbound⟩ :=
      IsDiscreteValuationRing.residueField_finite_and_ramificationIdx_mul_residueDegree_le_finrank
        B C L M
    let := hres
    have hpos : 0 < Module.finrank (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField C) :=
      Module.finrank_pos
    have hmul := Ideal.ramificationIdx_tower (R := A)
      (IsLocalRing.maximalIdeal B) (IsLocalRing.maximalIdeal C)
    rw [← ramificationIndex_eq_ramificationIdx A C,
      ← ramificationIndex_eq_ramificationIdx A B] at hmul
    rw [show IsDiscreteValuationRing.ramificationIndex A B = 1 from hweak, one_mul] at hmul
    rw [hmul, hdegree] at *
    nlinarith
  · obtain ⟨K₁, hK₁, hKK₁, hAK₁, hAKK₁, hfin, hsep, hdeg, htot,
      hL₁, hM₁, hA₁, hBdom, hB₁, hCdom, hC₁,
      g, f, f', hf, hf', hgL, hgK, hfK, hf'g, hmB, hmC⟩ := h
    let := hK₁
    let := hKK₁
    let := hAK₁
    let := hAKK₁
    let := hfin
    let := hA₁
    let := hBdom
    let := hB₁
    let := hCdom
    let := hC₁
    obtain ⟨D⟩ := nonempty_integralClosureBaseChange A C K M K₁
    refine ⟨K₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, D, ?_⟩
    apply isWeakSolution_of_isField_tensorProduct A C K M K₁ D hM₁ (f'.comp f)
    · intro a
      rw [RingHom.comp_apply, hf'g, hfK, hgK]
    · let : Algebra (integralClosure A K₁) (integralClosure C (M ⊗[K] K₁)) :=
        (f'.comp f).toAlgebra
      apply forall_ramificationIdx_eq_one_of_map_maximalIdeal
        (integralClosure A K₁) (integralClosure C (M ⊗[K] K₁))
      change Ideal.map (f'.comp f) _ = _
      rw [← Ideal.map_map, hmB, hmC]



private theorem isIntegralClosure_of_isIntegral
    (R S T U : Type*) [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra R U] [Algebra S U] [Algebra T U]
    [IsScalarTower R S U] [Algebra.IsIntegral R S] [IsIntegralClosure T S U] :
    IsIntegralClosure T R U := by
  refine ⟨IsIntegralClosure.algebraMap_injective T S U, ?_⟩
  intro x
  rw [← IsIntegralClosure.isIntegral_iff (A := T) (R := S)]
  exact ⟨IsIntegral.tower_top, isIntegral_trans x⟩

/-- A weak solution over integral extensions of the original rings has the same
ramification condition when its closures are formed over the original rings. -/
theorem isWeakSolution_integral_base_change
    (R S K L K₂ : Type*)
    [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing S]
    [Field K] [Field L] [Field K₂]
    [Algebra R S] [Algebra R K] [Algebra R L] [Algebra S L]
    [Algebra K L] [Algebra K K₂] [Algebra R K₂]
    [IsDiscreteValuationRing.IsExtension R S] [IsFractionRing R K] [IsFractionRing S L]
    [IsScalarTower R S L] [IsScalarTower R K L] [IsScalarTower R K K₂]
    [Module.Finite K K₂]
    (D : IsDiscreteValuationRing.IntegralClosureBaseChange R S K L K₂)
    (A B : Type*) [CommRing A] [CommRing B]
    [Algebra A B] [Algebra A R] [Algebra B S]
    [Algebra.IsIntegral A R] [Algebra.IsIntegral B S]
    [Algebra A K₂] [Algebra B D.L₁] [Algebra A D.L₁]
    [IsScalarTower A B D.L₁] [IsScalarTower A K₂ D.L₁]
    (hA : ∀ a : A, algebraMap A K₂ a = algebraMap R K₂ (algebraMap A R a))
    (hB : ∀ b : B, algebraMap B D.L₁ b = algebraMap S D.L₁ (algebraMap B S b))
    (hD : D.IsWeakSolution) :
    letI : Algebra (integralClosure A K₂) (integralClosure B D.L₁) :=
      (mapIntegralClosureOfTower A B K₂ D.L₁).toRingHom.toAlgebra
    ∀ q : Ideal (integralClosure B D.L₁), q.IsMaximal →
      q.ramificationIdx (integralClosure A K₂) = 1 := by
  let : Algebra A D.A₁ := ((algebraMap R D.A₁).comp (algebraMap A R)).toAlgebra
  let : Algebra B D.B₁ := ((algebraMap S D.B₁).comp (algebraMap B S)).toAlgebra
  let : IsScalarTower A R K₂ := IsScalarTower.of_algebraMap_eq hA
  let : IsScalarTower B S D.L₁ := IsScalarTower.of_algebraMap_eq hB
  let : IsScalarTower A D.A₁ K₂ := IsScalarTower.of_algebraMap_eq fun a => by
    rw [hA, IsScalarTower.algebraMap_apply R D.A₁ K₂]
    rfl
  let : IsScalarTower B D.B₁ D.L₁ := IsScalarTower.of_algebraMap_eq fun b => by
    rw [hB, IsScalarTower.algebraMap_apply S D.B₁ D.L₁]
    rfl
  let : IsIntegralClosure D.A₁ A K₂ := isIntegralClosure_of_isIntegral A R D.A₁ K₂
  let : IsIntegralClosure D.B₁ B D.L₁ := isIntegralClosure_of_isIntegral B S D.B₁ D.L₁
  exact forall_ramificationIdx_eq_one_integralClosure A B K₂ D.L₁ D.A₁ D.B₁ D.ringSquare hD


/-- Compatible reduced base changes on every factor of the first base change
assemble to a weak solution for the composite extension. -/
theorem isWeakSolution_of_iterated_factors
    (A B K L K₁ K₂ : Type*)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁] [Field K₂]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra K K₂] [Algebra K₁ K₂]
    [Algebra A K₂] [IsScalarTower K K₁ K₂]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₂]
    [Module.Finite K K₂]
    (D : IsDiscreteValuationRing.IntegralClosureBaseChange A B K L K₂)
    {ι : Type*} [Finite ι] (E F : ι → Type*)
    [∀ i, CommRing (E i)] [∀ i, CommRing (F i)]
    [∀ i, Algebra K (E i)] [∀ i, Algebra K₁ (E i)] [∀ i, Algebra L (E i)]
    [∀ i, IsScalarTower K K₁ (E i)]
    [∀ i, Algebra K₁ (F i)] [∀ i, Algebra (E i) (F i)]
    [∀ i, IsScalarTower K₁ (E i) (F i)]
    [∀ i, Algebra L (F i)] [∀ i, IsScalarTower L (E i) (F i)]
    [∀ i, Algebra A (F i)] [∀ i, Algebra B (F i)] [∀ i, Algebra K₂ (F i)]
    [∀ i, IsScalarTower B L (F i)] [∀ i, IsScalarTower A B (F i)]
    [∀ i, IsScalarTower A K₂ (F i)]
    (eF : ∀ i, F i ≃ₐ[K₁] ReducedTensorTower.Reduction (E i ⊗[K₁] K₂))
    (hFleft : ∀ i x, eF i (algebraMap (E i) (F i) x) =
      Ideal.Quotient.mk _ (x ⊗ₜ[K₁] (1 : K₂)))
    (hFright : ∀ i x, eF i (algebraMap K₂ (F i) x) =
      Ideal.Quotient.mk _ ((1 : E i) ⊗ₜ[K₁] x)) :
    letI : Algebra K₁ (L ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra K₁ (ReducedTensorTower.Reduction (L ⊗[K] K₁)) := Ideal.Quotient.algebra K₁
    ∀ (e : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K₁] ∀ i, E i)
      (_ : ∀ i x, e (Ideal.Quotient.mk _ (x ⊗ₜ[K] (1 : K₁))) i = algebraMap L (E i) x),
      (∀ i, letI : Algebra (integralClosure A K₂) (integralClosure B (F i)) :=
        (mapIntegralClosureOfTower A B K₂ (F i)).toRingHom.toAlgebra
        ∀ q : Ideal (integralClosure B (F i)), q.IsMaximal →
          q.ramificationIdx (integralClosure A K₂) = 1) → D.IsWeakSolution := by
  let : Algebra K₁ (L ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
  let : Algebra K₁ (ReducedTensorTower.Reduction (L ⊗[K] K₁)) := Ideal.Quotient.algebra K₁
  intro e he hF
  let : ∀ i, Algebra K (F i) := fun i =>
    ((algebraMap K₁ (F i)).comp (algebraMap K K₁)).toAlgebra
  let : ∀ i, IsScalarTower K K₁ (F i) := fun i => IsScalarTower.of_algebraMap_eq' rfl
  let e0 := reducedTensorBaseChangePiEquiv K K₁ K₂ L E e
  let e1 := AlgEquiv.piCongrRight fun i => (eF i).symm.restrictScalars K
  let e2 : D.L₁ ≃ₐ[L] ∀ i, F i :=
    { __ := ((D.eL₁.trans e0).trans e1).toRingEquiv
      commutes' x := by
        ext i
        change (eF i).symm (e0 (D.eL₁ (algebraMap L D.L₁ x)) i) = algebraMap L (F i) x
        rw [D.eL₁_left]
        change (eF i).symm (e0 (Ideal.Quotient.mk _ (x ⊗ₜ[K] (1 : K₂))) i) = _
        rw [reducedTensorBaseChangePiEquiv_tmul, he,
          ← hFleft, AlgEquiv.symm_apply_apply, ← IsScalarTower.algebraMap_apply L (E i) (F i)] }
  apply isWeakSolution_of_factors A B K L K₂ D F e2 ?_ hF
  intro i x
  change (eF i).symm (e0 (D.eL₁ (algebraMap K₂ D.L₁ x)) i) = algebraMap K₂ (F i) x
  rw [D.eL₁_right]
  change (eF i).symm (e0 (Ideal.Quotient.mk _ ((1 : L) ⊗ₜ[K] x)) i) = _
  rw [reducedTensorBaseChangePiEquiv_tmul, he, map_one,
    ← hFright, AlgEquiv.symm_apply_apply]

end IsDiscreteValuationRing
