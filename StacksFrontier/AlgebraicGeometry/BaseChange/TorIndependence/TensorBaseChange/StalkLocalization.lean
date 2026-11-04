module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.StalkComplexCriterion
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalkCartesian
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorOnModels

/-!
# The local ring of a fibre product is a localization

For a cartesian square of schemes and a point `x'` of `X' = X ×_S S'`, the local ring
`𝒪_{X',x'}` is a localization of `𝒪_{X,x} ⊗_{𝒪_{S,s}} 𝒪_{S',s'}`, as an algebra through the ring
map of Stacks 0DJ7.

## Main results

* `AlgebraicGeometry.exists_isLocalization_stalk`: the local ring `𝒪_{X',x'}` is a localization
  of `𝒪_{X,x} ⊗_{𝒪_{S,s}} 𝒪_{S',s'}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable {X X' : Scheme.{u}} (g' : X' ⟶ X)

/-- The component at a complex `P` of the derived pullback natural transformation along `g'` is
the pullback comparison map `pullbackComparisonOnComplex g' P`. -/
theorem derivedPullbackNatTrans_app_eq (P : CochainComplex X.Modules ℤ) :
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans g'.toLRSHom.toShHom).app P =
      pullbackComparisonOnComplex g' P := rfl

end AlgebraicGeometry

namespace AlgebraicGeometry

open RingTheory.TorIndependence

/-- A ring map `A ⊗[R] R' →+* A'` whose restrictions to `A` and to `R'` are the algebra maps
equals `baseChangeTensorRingMap`. -/
theorem baseChangeTensorRingMap_eq_of_comp {R A R' A' : Type u}
    [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
    [IsScalarTower R A A'] [IsScalarTower R R' A'] (φ : A ⊗[R] R' →+* A')
    (hl : φ.comp Algebra.TensorProduct.includeLeftRingHom = algebraMap A A')
    (hr : φ.comp Algebra.TensorProduct.includeRight.toRingHom = algebraMap R' A') :
    φ = baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A') := by
  refine RingHom.ext fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add s t hs ht => rw [map_add, map_add, hs, ht]
  | tmul a r =>
    have ht : a ⊗ₜ[R] r = Algebra.TensorProduct.includeLeftRingHom a *
        Algebra.TensorProduct.includeRight.toRingHom r := by
      show a ⊗ₜ[R] r = (a ⊗ₜ[R] 1) * (1 ⊗ₜ[R] r)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [ht, map_mul, ← RingHom.comp_apply, ← RingHom.comp_apply φ, hl, hr, ← ht,
      baseChangeTensorRingMap_tmul]

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **The local ring of a fibre product is a localization of the tensor product of the local
rings**, for the ring map of the square along which the map of Stacks 0DJ7 is linear. -/
theorem exists_isLocalization_stalk (hpb : IsPullback g' f' f g) (x' : X') :
    letI : Algebra (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x')) :=
      ((f.stalkMap (g' x')).hom).toAlgebra
    letI : Algebra (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x')) :=
      (baseStalkMap f g f' g' hpb.w x').toAlgebra
    letI : Algebra (S.presheaf.stalk (f (g' x'))) (X'.presheaf.stalk x') :=
      (((g'.stalkMap x').hom).comp ((f.stalkMap (g' x')).hom)).toAlgebra
    letI : Algebra (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') :=
      ((g'.stalkMap x').hom).toAlgebra
    letI : Algebra (S'.presheaf.stalk (f' x')) (X'.presheaf.stalk x') :=
      ((f'.stalkMap x').hom).toAlgebra
    letI : IsScalarTower (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x'))
        (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x'))
        (X'.presheaf.stalk x') :=
      IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' hpb.w x')
    letI := (baseChangeTensorRingMap (R := S.presheaf.stalk (f (g' x')))
      (A := X.presheaf.stalk (g' x')) (R' := S'.presheaf.stalk (f' x'))
      (A' := X'.presheaf.stalk x')).toAlgebra
    ∃ M : Submonoid (X.presheaf.stalk (g' x') ⊗[S.presheaf.stalk (f (g' x'))]
      S'.presheaf.stalk (f' x')), IsLocalization M (X'.presheaf.stalk x') := by
  have key : ∀ (b : S.presheaf.stalk (f (g' x')) →+* S'.presheaf.stalk (f' x')),
      b = (eqToHom (congrArg (fun z => S.presheaf.stalk z)
        (congrArg (fun k : X' ⟶ S => k.base x') hpb.w)) ≫ g.stalkMap (f'.base x')).hom →
      let : Algebra (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x')) :=
        ((f.stalkMap (g' x')).hom).toAlgebra
      let : Algebra (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x')) := b.toAlgebra
      ∃ φ : X.presheaf.stalk (g' x') ⊗[S.presheaf.stalk (f (g' x'))] S'.presheaf.stalk (f' x')
          →+* X'.presheaf.stalk x',
        φ.comp Algebra.TensorProduct.includeLeftRingHom = (g'.stalkMap x').hom ∧
        φ.comp Algebra.TensorProduct.includeRight.toRingHom = (f'.stalkMap x').hom ∧
        let := φ.toAlgebra
        ∃ M : Submonoid (X.presheaf.stalk (g' x') ⊗[S.presheaf.stalk (f (g' x'))]
          S'.presheaf.stalk (f' x')), IsLocalization M (X'.presheaf.stalk x') := by
    intro b hb
    subst hb
    exact BaseChangeStalk.cartesian_stalk_isLocalization g' f' f g hpb x'
  obtain ⟨φ, hl, hr, M, hM⟩ := key (baseStalkMap f g f' g' hpb.w x') (by
    rw [baseStalkMap, stalkCongr_of_eq]
    exact congrArg (fun k : X' ⟶ S => k x') hpb.w)
  let : Algebra (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x')) :=
    ((f.stalkMap (g' x')).hom).toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x')) :=
    (baseStalkMap f g f' g' hpb.w x').toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' x'))) (X'.presheaf.stalk x') :=
    (((g'.stalkMap x').hom).comp ((f.stalkMap (g' x')).hom)).toAlgebra
  let : Algebra (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') :=
    ((g'.stalkMap x').hom).toAlgebra
  let : Algebra (S'.presheaf.stalk (f' x')) (X'.presheaf.stalk x') :=
    ((f'.stalkMap x').hom).toAlgebra
  let : IsScalarTower (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x'))
      (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x'))
      (X'.presheaf.stalk x') :=
    IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' hpb.w x')
  refine ⟨M, ?_⟩
  have hφ := baseChangeTensorRingMap_eq_of_comp (R := S.presheaf.stalk (f (g' x')))
    (A := X.presheaf.stalk (g' x')) (R' := S'.presheaf.stalk (f' x'))
    (A' := X'.presheaf.stalk x') φ hl hr
  subst hφ
  exact hM

end AlgebraicGeometry
