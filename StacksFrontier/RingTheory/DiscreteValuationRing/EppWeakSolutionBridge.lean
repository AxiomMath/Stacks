module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppRamificationTransport
public import StacksFrontier.RingTheory.Ideal.NilradicalQuotient
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution

/-!
# Transporting weak solutions across isomorphisms of base-change data

Let `D` and `D'` be two base-change packages
(`IsDiscreteValuationRing.IntegralClosureBaseChange`). If their recorded base rings and upper rings
are identified by ring isomorphisms `eA : D.A₁ ≃+* D'.A₁` and `eB : D.B₁ ≃+* D'.B₁` commuting with
the structure maps, then `D` is a weak solution if and only if `D'` is. This applies in particular
when both packages are base changes along one field `K₂`, the first of the tower obtained from the
second by a base change along `K₁ / K` (Stacks Tag 09F9): then `(M ⊗[K] K₁) ⊗[K₁] K₂ ≅ M ⊗[K] K₂`,
and the integral closures of `A₁` and of `A` in `K₂` agree since `A₁` is integral over `A`.

## Main definitions

* `Stacks.DiscreteValuationRing.EppLevelInduction.reductionRingEquiv`: the isomorphism of
  reductions `X ⧸ nilradical X ≃+* Y ⧸ nilradical Y` induced by a ring isomorphism `X ≃+* Y`.
* `Stacks.DiscreteValuationRing.EppLevelInduction.integralClosureRingEquivOfAlgEquiv`: the ring
  isomorphism of integral closures induced by an algebra isomorphism of the ambient rings.
* `Stacks.DiscreteValuationRing.EppLevelInduction.ringEquivOfIsIntegralClosureTower`: the
  isomorphism of two integral closures in one ring over bases one of which is integral over the
  other.
* `Stacks.DiscreteValuationRing.EppLevelInduction.compositumRingEquiv`: the isomorphism of the
  recorded composita of two packages induced by an isomorphism `M₁ ⊗[K₁] K₂ ≃+* M ⊗[K] K₂`.

## Main results

* `Stacks.DiscreteValuationRing.EppLevelInduction.nonempty_algEquiv_tensorCancel` and
  `Stacks.DiscreteValuationRing.EppLevelInduction.exists_ringEquiv_tensorCancel_includeRight`:
  `(M ⊗[K] K₁) ⊗[K₁] K₂ ≅ M ⊗[K] K₂`.
* `Stacks.DiscreteValuationRing.EppLevelInduction.rightAlgebra_eq_includeRight_toAlgebra`: the
  two algebra structures on `A ⊗[R] B` over the right factor are equal.
* `Stacks.DiscreteValuationRing.EppLevelInduction.isWeakSolution_of_ringEquiv_square` and
  `Stacks.DiscreteValuationRing.EppLevelInduction.isWeakSolution_iff_ringEquiv_square`:
  `IsWeakSolution` transports across a commuting square of ring isomorphisms of the two
  packages' base and upper rings.
* `Stacks.DiscreteValuationRing.EppLevelInduction.isIntegralClosure_tower_bot`: an integral
  closure over `S` is one over `R` when `S` is integral over `R`.
* `Stacks.DiscreteValuationRing.EppLevelInduction.isWeakSolution_of_fractionFieldRingEquiv` and
  `Stacks.DiscreteValuationRing.EppLevelInduction.isWeakSolution_of_tensorCancel`: the transport
  for two packages over one field `K₂`, with the compatibilities stated in `K₂` and in the
  composita.

## References

* [The Stacks Project, Tag 09EN](https://stacks.math.columbia.edu/tag/09EN)
* [The Stacks Project, Tag 09F5](https://stacks.math.columbia.edu/tag/09F5)
* [The Stacks Project, Tag 09F9](https://stacks.math.columbia.edu/tag/09F9)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.DiscreteValuationRing.EppLevelInduction

/-! ### The base-change cancellation -/

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- Base change composes: `(M ⊗[K] K₁) ⊗[K₁] K₂ ≃ₐ[K₂] M ⊗[K] K₂`, for the algebra structures
over the right factors. -/
theorem nonempty_algEquiv_tensorCancel
    (K K₁ K₂ M : Type*) [CommRing K] [CommRing K₁] [CommRing K₂] [CommRing M]
    [Algebra K K₁] [Algebra K₁ K₂] [Algebra K K₂] [IsScalarTower K K₁ K₂] [Algebra K M] :
    Nonempty (((M ⊗[K] K₁) ⊗[K₁] K₂) ≃ₐ[K₂] (M ⊗[K] K₂)) :=
  ⟨(Algebra.TensorProduct.commRight K₁ K₂ (M ⊗[K] K₁)).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : K₂ ≃ₐ[K₂] K₂)
        (Algebra.TensorProduct.commRight K K₁ M).symm).trans
      ((Algebra.TensorProduct.cancelBaseChange K K₁ K₂ K₂ M).trans
        (Algebra.TensorProduct.commRight K K₂ M)))⟩

/-- The algebra structure `Algebra.TensorProduct.rightAlgebra` on `A ⊗[R] B` over the right factor
is `Algebra.TensorProduct.includeRight.toRingHom.toAlgebra`. -/
theorem rightAlgebra_eq_includeRight_toAlgebra
    (R A B : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A]
    [CommSemiring B] [Algebra R B] :
    Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := B)
      = (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom.toAlgebra :=
  rfl

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- There is a ring isomorphism `c : (M ⊗[K] K₁) ⊗[K₁] K₂ ≃+* M ⊗[K] K₂` fixing
`Algebra.TensorProduct.includeRight` on `K₂` and sending `(x ⊗ₜ 1) ⊗ₜ 1` to `x ⊗ₜ 1` for
`x : M`. -/
theorem exists_ringEquiv_tensorCancel_includeRight
    (K K₁ K₂ M : Type*) [CommRing K] [CommRing K₁] [CommRing K₂] [CommRing M]
    [Algebra K K₁] [Algebra K₁ K₂] [Algebra K K₂] [IsScalarTower K K₁ K₂] [Algebra K M] :
    ∃ c : ((M ⊗[K] K₁) ⊗[K₁] K₂) ≃+* (M ⊗[K] K₂),
      (∀ x : K₂, c (Algebra.TensorProduct.includeRight x)
        = Algebra.TensorProduct.includeRight x) ∧
      ∀ x : M, c ((x ⊗ₜ[K] (1 : K₁)) ⊗ₜ[K₁] (1 : K₂)) = x ⊗ₜ[K] (1 : K₂) := by
  let c₀ : ((M ⊗[K] K₁) ⊗[K₁] K₂) ≃ₐ[K₂] (M ⊗[K] K₂) :=
    (Algebra.TensorProduct.commRight K₁ K₂ (M ⊗[K] K₁)).symm.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : K₂ ≃ₐ[K₂] K₂)
          (Algebra.TensorProduct.commRight K K₁ M).symm).trans
        ((Algebra.TensorProduct.cancelBaseChange K K₁ K₂ K₂ M).trans
          (Algebra.TensorProduct.commRight K K₂ M)))
  refine ⟨c₀.toRingEquiv, fun x => ?_, fun x => ?_⟩
  · have h1 : (Algebra.TensorProduct.includeRight (R := K₁) (A := M ⊗[K] K₁) (B := K₂) x)
        = algebraMap K₂ ((M ⊗[K] K₁) ⊗[K₁] K₂) x := rfl
    have h2 : (Algebra.TensorProduct.includeRight (R := K) (A := M) (B := K₂) x)
        = algebraMap K₂ (M ⊗[K] K₂) x := rfl
    show c₀ _ = _
    rw [h1, h2, c₀.commutes]
  · show c₀ _ = _
    have hs₁ : (Algebra.TensorProduct.commRight K₁ K₂ (M ⊗[K] K₁)).symm
        ((x ⊗ₜ[K] (1 : K₁)) ⊗ₜ[K₁] (1 : K₂)) = (1 : K₂) ⊗ₜ[K₁] (x ⊗ₜ[K] (1 : K₁)) :=
      (AlgEquiv.symm_apply_eq _).mpr rfl
    have hs₂ : (Algebra.TensorProduct.commRight K K₁ M).symm (x ⊗ₜ[K] (1 : K₁))
        = (1 : K₁) ⊗ₜ[K] x := (AlgEquiv.symm_apply_eq _).mpr rfl
    simp only [c₀, AlgEquiv.trans_apply, hs₁, Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.map_tmul]
    simp [hs₂]

open IsDiscreteValuationRing

universe uA uB uK uL uK₁ w₁ w₂ w₃ vA vB vK vL vK₁ x₁ x₂ x₃

section Bridge

variable {A : Type uA} {B : Type uB} {K : Type uK} {L : Type uL} {K₁ : Type uK₁}
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁]
    {A' : Type vA} {B' : Type vB} {K' : Type vK} {L' : Type vL} {K₁' : Type vK₁}
    [CommRing A'] [CommRing B'] [Field K'] [Field L'] [Field K₁']
    [IsDomain A'] [IsDomain B'] [IsDiscreteValuationRing A'] [IsDiscreteValuationRing B']
    [Algebra A' B'] [Algebra A' K'] [Algebra A' L'] [Algebra B' L']
    [Algebra K' L'] [Algebra K' K₁'] [Algebra A' K₁']
    [IsExtension A' B'] [IsFractionRing A' K'] [IsFractionRing B' L']
    [IsScalarTower A' B' L'] [IsScalarTower A' K' L'] [IsScalarTower A' K' K₁']
    [Module.Finite K' K₁']

/-- If ring isomorphisms `eA : D.A₁ ≃+* D'.A₁` and `eB : D.B₁ ≃+* D'.B₁` commute with the structure
maps, then `D'` is a weak solution whenever `D` is. -/
theorem isWeakSolution_of_ringEquiv_square
    (D : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, w₁, w₂, w₃} A B K L K₁)
    (D' : IntegralClosureBaseChange.{vA, vB, vK, vL, vK₁, x₁, x₂, x₃} A' B' K' L' K₁') :
    letI := D.commRingA₁
    letI := D.commRingB₁
    letI := D.algebraA₁B₁
    letI := D'.commRingA₁
    letI := D'.commRingB₁
    letI := D'.algebraA₁B₁
    ∀ (eA : D.A₁ ≃+* D'.A₁) (eB : D.B₁ ≃+* D'.B₁),
      (∀ x : D.A₁, algebraMap D'.A₁ D'.B₁ (eA x) = eB (algebraMap D.A₁ D.B₁ x)) →
        D.IsWeakSolution → D'.IsWeakSolution := by
  let := D.commRingA₁
  let := D.commRingB₁
  let := D.algebraA₁B₁
  let := D'.commRingA₁
  let := D'.commRingB₁
  let := D'.algebraA₁B₁
  intro eA eB hsq h q' hq'
  have hmax : (q'.comap (eB : D.B₁ →+* D'.B₁)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (eB : D.B₁ →+* D'.B₁) eB.surjective
  have htr := ramificationIdx_map eA eB hsq (q'.comap (eB : D.B₁ →+* D'.B₁))
  rw [Ideal.map_comap_of_surjective (eB : D.B₁ →+* D'.B₁) eB.surjective q'] at htr
  rw [← htr]
  exact h _ hmax

/-- If ring isomorphisms `eA : D.A₁ ≃+* D'.A₁` and `eB : D.B₁ ≃+* D'.B₁` commute with the structure
maps, then `D` is a weak solution if and only if `D'` is. -/
theorem isWeakSolution_iff_ringEquiv_square
    (D : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, w₁, w₂, w₃} A B K L K₁)
    (D' : IntegralClosureBaseChange.{vA, vB, vK, vL, vK₁, x₁, x₂, x₃} A' B' K' L' K₁') :
    letI := D.commRingA₁
    letI := D.commRingB₁
    letI := D.algebraA₁B₁
    letI := D'.commRingA₁
    letI := D'.commRingB₁
    letI := D'.algebraA₁B₁
    ∀ (eA : D.A₁ ≃+* D'.A₁) (eB : D.B₁ ≃+* D'.B₁),
      (∀ x : D.A₁, algebraMap D'.A₁ D'.B₁ (eA x) = eB (algebraMap D.A₁ D.B₁ x)) →
        (D.IsWeakSolution ↔ D'.IsWeakSolution) := by
  let := D.commRingA₁
  let := D.commRingB₁
  let := D.algebraA₁B₁
  let := D'.commRingA₁
  let := D'.commRingB₁
  let := D'.algebraA₁B₁
  intro eA eB hsq
  refine ⟨isWeakSolution_of_ringEquiv_square D D' eA eB hsq, ?_⟩
  refine isWeakSolution_of_ringEquiv_square D' D eA.symm eB.symm fun y => ?_
  have hx := hsq (eA.symm y)
  rw [eA.apply_symm_apply] at hx
  rw [hx, eB.symm_apply_apply]

end Bridge

/-! ### Building the bridge's isomorphisms from a base-change step -/

/-- A ring isomorphism carries the nilradical to the nilradical. -/
theorem map_nilradical (X Y : Type*) [CommRing X] [CommRing Y] (e : X ≃+* Y) :
    (nilradical X).map (e : X →+* Y) = nilradical Y :=
  Ideal.map_nilradical e

/-- The isomorphism of reductions `X ⧸ nilradical X ≃+* Y ⧸ nilradical Y` induced by a ring
isomorphism `e : X ≃+* Y`. -/
noncomputable def reductionRingEquiv (X Y : Type*) [CommRing X] [CommRing Y] (e : X ≃+* Y) :
    (X ⧸ nilradical X) ≃+* (Y ⧸ nilradical Y) :=
  e.quotientNilradical

/-- The ring isomorphism `integralClosure C X ≃+* integralClosure C Y` induced by an isomorphism
of `C`-algebras `e : X ≃ₐ[C] Y`. -/
noncomputable def integralClosureRingEquivOfAlgEquiv
    (C X Y : Type*) [CommRing C] [CommRing X] [CommRing Y]
    [Algebra C X] [Algebra C Y] (e : X ≃ₐ[C] Y) :
    integralClosure C X ≃+* integralClosure C Y :=
  ((e.subalgebraMap (integralClosure C X)).trans
    (Subalgebra.equivOfEq _ _ (integralClosure_map_algEquiv e))).toRingEquiv

/-- `reductionRingEquiv X Y e` sends the class of `x` to the class of `e x`. -/
theorem reductionRingEquiv_mk (X Y : Type*) [CommRing X] [CommRing Y] (e : X ≃+* Y) (x : X) :
    reductionRingEquiv X Y e (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (e x) := rfl

/-- If `e : X ≃+* Y` commutes with the algebra maps from `Z`, then so does
`reductionRingEquiv X Y e` on classes. -/
theorem reductionRingEquiv_algebraMap (Z X Y : Type*) [CommRing Z] [CommRing X] [CommRing Y]
    [Algebra Z X] [Algebra Z Y] (e : X ≃+* Y)
    (hz : ∀ z : Z, e (algebraMap Z X z) = algebraMap Z Y z) (z : Z) :
    reductionRingEquiv X Y e (Ideal.Quotient.mk _ (algebraMap Z X z))
      = Ideal.Quotient.mk _ (algebraMap Z Y z) := by
  rw [reductionRingEquiv_mk, hz]

/-! ### The base ring: two integral closures in one field -/

/-- If `X` is the integral closure of `S` in `T` and `S` is integral over `R`, then `X` is the
integral closure of `R` in `T`. -/
theorem isIntegralClosure_tower_bot
    (R S T X : Type*) [CommRing R] [CommRing S] [CommRing T] [CommRing X]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra S X] [Algebra R X] [Algebra X T] [IsScalarTower R S X]
    [Algebra.IsIntegral R S] [IsIntegralClosure X S T] :
    IsIntegralClosure X R T where
  algebraMap_injective := IsIntegralClosure.algebraMap_injective X S T
  isIntegral_iff {x} := by
    refine ⟨fun h => (IsIntegralClosure.isIntegral_iff (A := X) (R := S)).mp h.tower_top, ?_⟩
    rintro ⟨y, rfl⟩
    exact isIntegral_trans (R := R) (A := S) _
      ((IsIntegralClosure.isIntegral_iff (A := X) (R := S)).mpr ⟨y, rfl⟩)

/-- The ring isomorphism between `X`, the integral closure of `S` in `T`, and `Y`, the integral
closure of `R` in `T`, when `S` is integral over `R`. -/
noncomputable def ringEquivOfIsIntegralClosureTower
    (R S T X Y : Type*) [CommRing R] [CommRing S] [CommRing T] [CommRing X] [CommRing Y]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra S X] [Algebra R X] [Algebra X T] [IsScalarTower R S X] [IsScalarTower R X T]
    [Algebra R Y] [Algebra Y T] [IsScalarTower R Y T]
    [Algebra.IsIntegral R S] [IsIntegralClosure X S T] [IsIntegralClosure Y R T] :
    X ≃+* Y :=
  let := isIntegralClosure_tower_bot R S T X
  (IsIntegralClosure.equiv R X T Y).toRingEquiv

/-- `ringEquivOfIsIntegralClosureTower` commutes with the maps into `T`. -/
theorem algebraMap_ringEquivOfIsIntegralClosureTower
    (R S T X Y : Type*) [CommRing R] [CommRing S] [CommRing T] [CommRing X] [CommRing Y]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra S X] [Algebra R X] [Algebra X T] [IsScalarTower R S X] [IsScalarTower R X T]
    [Algebra R Y] [Algebra Y T] [IsScalarTower R Y T]
    [Algebra.IsIntegral R S] [IsIntegralClosure X S T] [IsIntegralClosure Y R T] (x : X) :
    algebraMap Y T (ringEquivOfIsIntegralClosureTower R S T X Y x) = algebraMap X T x :=
  let := isIntegralClosure_tower_bot R S T X
  IsIntegralClosure.algebraMap_equiv R X T Y x

/-! ### The connector -/

section Connector

universe nA nC nK nM nT n₁ n₂ n₃ mA mC mK mM m₁ m₂ m₃

variable {A₁ : Type nA} {C₁ : Type nC} {K₁ : Type nK} {M₁ : Type nM} {K₂ : Type nT}
    [CommRing A₁] [CommRing C₁] [Field K₁] [Field M₁] [Field K₂]
    [IsDomain A₁] [IsDomain C₁] [IsDiscreteValuationRing A₁] [IsDiscreteValuationRing C₁]
    [Algebra A₁ C₁] [Algebra A₁ K₁] [Algebra A₁ M₁] [Algebra C₁ M₁]
    [Algebra K₁ M₁] [Algebra K₁ K₂] [Algebra A₁ K₂]
    [IsExtension A₁ C₁] [IsFractionRing A₁ K₁] [IsFractionRing C₁ M₁]
    [IsScalarTower A₁ C₁ M₁] [IsScalarTower A₁ K₁ M₁] [IsScalarTower A₁ K₁ K₂]
    [Module.Finite K₁ K₂]
    {A : Type mA} {C : Type mC} {K : Type mK} {M : Type mM}
    [CommRing A] [CommRing C] [Field K] [Field M]
    [IsDomain A] [IsDomain C] [IsDiscreteValuationRing A] [IsDiscreteValuationRing C]
    [Algebra A C] [Algebra A K] [Algebra A M] [Algebra C M]
    [Algebra K M] [Algebra K K₂] [Algebra A K₂]
    [IsExtension A C] [IsFractionRing A K] [IsFractionRing C M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower A K K₂]
    [Module.Finite K K₂]

/-- Let `D` and `D'` be base-change packages along the same field `K₂`, over the towers
`(A₁, C₁, K₁, M₁)` and `(A, C, K, M)`. Suppose given ring isomorphisms `eA : D.A₁ ≃+* D'.A₁`,
`eB : D.B₁ ≃+* D'.B₁` and `eL : D.L₁ ≃+* D'.L₁` such that `eA` commutes with the maps into `K₂`,
`eL` with the maps out of `K₂`, and `eB` and `eL` with the maps `B₁ → L₁`. Then `D'` is a weak
solution whenever `D` is. -/
theorem isWeakSolution_of_fractionFieldRingEquiv
    (D : IntegralClosureBaseChange.{nA, nC, nK, nM, nT, n₁, n₂, n₃} A₁ C₁ K₁ M₁ K₂)
    (D' : IntegralClosureBaseChange.{mA, mC, mK, mM, nT, m₁, m₂, m₃} A C K M K₂) :
    letI := D.commRingA₁
    letI := D.commRingB₁
    letI := D.commRingL₁
    letI := D.algebraA₁B₁
    letI := D.algebraA₁K₁
    letI := D.algebraB₁L₁
    letI := D.algebraK₁L₁
    letI := D'.commRingA₁
    letI := D'.commRingB₁
    letI := D'.commRingL₁
    letI := D'.algebraA₁B₁
    letI := D'.algebraA₁K₁
    letI := D'.algebraB₁L₁
    letI := D'.algebraK₁L₁
    letI := D'.algebraBB₁
    letI := D'.isIntegralClosureB₁
    ∀ (eA : D.A₁ ≃+* D'.A₁)
      (_ : ∀ x : D.A₁, algebraMap D'.A₁ K₂ (eA x) = algebraMap D.A₁ K₂ x)
      (eB : D.B₁ ≃+* D'.B₁) (eL : D.L₁ ≃+* D'.L₁)
      (_ : ∀ x : K₂, eL (algebraMap K₂ D.L₁ x) = algebraMap K₂ D'.L₁ x)
      (_ : ∀ y : D.B₁, algebraMap D'.B₁ D'.L₁ (eB y) = eL (algebraMap D.B₁ D.L₁ y)),
        D.IsWeakSolution → D'.IsWeakSolution := by
  let := D.commRingA₁
  let := D.commRingB₁
  let := D.commRingL₁
  let := D.algebraA₁B₁
  let := D.algebraA₁K₁
  let := D.algebraB₁L₁
  let := D.algebraK₁L₁
  let := D'.commRingA₁
  let := D'.commRingB₁
  let := D'.commRingL₁
  let := D'.algebraA₁B₁
  let := D'.algebraA₁K₁
  let := D'.algebraB₁L₁
  let := D'.algebraK₁L₁
  let := D'.algebraBB₁
  let := D'.isIntegralClosureB₁
  intro eA hA eB eL hL hB
  refine isWeakSolution_of_ringEquiv_square D D' eA eB fun x => ?_
  have hinj : Function.Injective (algebraMap D'.B₁ D'.L₁) :=
    D'.isIntegralClosureB₁.algebraMap_injective
  apply hinj
  rw [D'.ringSquare (eA x), hA x, hB (algebraMap D.A₁ D.B₁ x), D.ringSquare x, hL]

/-! ### The connector, taking the cancellation directly -/

/-- The isomorphism `D.L₁ ≃+* D'.L₁` of the recorded composita induced by a ring isomorphism
`c : M₁ ⊗[K₁] K₂ ≃+* M ⊗[K] K₂`: `D.eL₁`, then the reduction of `c`, then `D'.eL₁.symm`. -/
noncomputable def compositumRingEquiv
    (D : IntegralClosureBaseChange.{nA, nC, nK, nM, nT, n₁, n₂, n₃} A₁ C₁ K₁ M₁ K₂)
    (D' : IntegralClosureBaseChange.{mA, mC, mK, mM, nT, m₁, m₂, m₃} A C K M K₂)
    (c : (M₁ ⊗[K₁] K₂) ≃+* (M ⊗[K] K₂)) :
    letI := D.commRingL₁
    letI := D'.commRingL₁
    D.L₁ ≃+* D'.L₁ :=
  let := D.commRingL₁
  let := D'.commRingL₁
  let := D.algebraKL₁
  let := D'.algebraKL₁
  D.eL₁.toRingEquiv.trans ((reductionRingEquiv _ _ c).trans D'.eL₁.toRingEquiv.symm)

/-- If `c` fixes `Algebra.TensorProduct.includeRight` on `K₂`, then `compositumRingEquiv D D' c`
commutes with the maps out of `K₂`. -/
theorem compositumRingEquiv_algebraMap
    (D : IntegralClosureBaseChange.{nA, nC, nK, nM, nT, n₁, n₂, n₃} A₁ C₁ K₁ M₁ K₂)
    (D' : IntegralClosureBaseChange.{mA, mC, mK, mM, nT, m₁, m₂, m₃} A C K M K₂)
    (c : (M₁ ⊗[K₁] K₂) ≃+* (M ⊗[K] K₂))
    (hc : ∀ x : K₂, c (Algebra.TensorProduct.includeRight x)
      = Algebra.TensorProduct.includeRight x) (x : K₂) :
    letI := D.commRingL₁
    letI := D'.commRingL₁
    letI := D.algebraK₁L₁
    letI := D'.algebraK₁L₁
    compositumRingEquiv D D' c (algebraMap K₂ D.L₁ x) = algebraMap K₂ D'.L₁ x := by
  let := D.commRingL₁
  let := D'.commRingL₁
  let := D.algebraK₁L₁
  let := D'.algebraK₁L₁
  let := D.algebraKL₁
  let := D'.algebraKL₁
  show D'.eL₁.toRingEquiv.symm (reductionRingEquiv _ _ c (D.eL₁ (algebraMap K₂ D.L₁ x))) = _
  rw [D.eL₁_right x, reductionRingEquiv_mk, hc x, ← D'.eL₁_right x]
  exact D'.eL₁.toRingEquiv.symm_apply_apply _

/-- Let `D` and `D'` be base-change packages along the same field `K₂`, and let
`c : M₁ ⊗[K₁] K₂ ≃+* M ⊗[K] K₂` fix `Algebra.TensorProduct.includeRight` on `K₂`. Suppose given
ring isomorphisms `eA : D.A₁ ≃+* D'.A₁`, commuting with the maps into `K₂`, and
`eB : D.B₁ ≃+* D'.B₁`, commuting through `compositumRingEquiv D D' c` with the maps `B₁ → L₁`.
Then `D'` is a weak solution whenever `D` is. -/
theorem isWeakSolution_of_tensorCancel
    (D : IntegralClosureBaseChange.{nA, nC, nK, nM, nT, n₁, n₂, n₃} A₁ C₁ K₁ M₁ K₂)
    (D' : IntegralClosureBaseChange.{mA, mC, mK, mM, nT, m₁, m₂, m₃} A C K M K₂)
    (c : (M₁ ⊗[K₁] K₂) ≃+* (M ⊗[K] K₂))
    (hc : ∀ x : K₂, c (Algebra.TensorProduct.includeRight x)
      = Algebra.TensorProduct.includeRight x) :
    letI := D.commRingA₁
    letI := D.commRingB₁
    letI := D.commRingL₁
    letI := D.algebraA₁B₁
    letI := D.algebraA₁K₁
    letI := D.algebraB₁L₁
    letI := D.algebraK₁L₁
    letI := D'.commRingA₁
    letI := D'.commRingB₁
    letI := D'.commRingL₁
    letI := D'.algebraA₁B₁
    letI := D'.algebraA₁K₁
    letI := D'.algebraB₁L₁
    letI := D'.algebraK₁L₁
    letI := D'.algebraBB₁
    letI := D'.isIntegralClosureB₁
    ∀ (eA : D.A₁ ≃+* D'.A₁)
      (_ : ∀ x : D.A₁, algebraMap D'.A₁ K₂ (eA x) = algebraMap D.A₁ K₂ x)
      (eB : D.B₁ ≃+* D'.B₁)
      (_ : ∀ y : D.B₁, algebraMap D'.B₁ D'.L₁ (eB y)
        = compositumRingEquiv D D' c (algebraMap D.B₁ D.L₁ y)),
        D.IsWeakSolution → D'.IsWeakSolution := by
  intro eA hA eB hB
  exact isWeakSolution_of_fractionFieldRingEquiv D D' eA hA eB (compositumRingEquiv D D' c)
    (compositumRingEquiv_algebraMap D D' c hc) hB

end Connector

end Stacks.DiscreteValuationRing.EppLevelInduction

end
