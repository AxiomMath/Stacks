module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.StalkIntegralClosureLocalization
public import StacksFrontier.RingTheory.TensorProduct.ReducedFractionRing

/-!
# The integral closure of a base change in the reduction of its fraction ring

Let `A` be a domain with fraction field `K`, let `B` be a finite flat `A`-algebra whose
localization at the nonzero elements of `A` is `L`, and let `O` be a domain over `A` with
fraction field `F`. The total ring of fractions of the reduction of `O ⊗[A] B` is the reduction
of `F ⊗[K] L`, so **the integral closure of `O ⊗[A] B` in the total ring of fractions of its own
reduction is the integral closure of `O` in the reduction of `F ⊗[K] L`.**

## Main definitions

* `integralClosureTensorProductAlgebra`: the `O ⊗[A] B`-algebra structure on the integral
  closure of `O` in the reduction of `F ⊗[K] L`, given by the structure map of `O ⊗[A] B`.

## Main results

* `isScalarTower_tensorProductFractionRing`: the map `O → F ⊗[K] L` factors through `O ⊗[A] B`.
* `nonempty_algEquiv_integralClosure_fractionRing_tensorProduct`: the integral closure of
  `O ⊗[A] B` in the total ring of fractions of the reduction of `O ⊗[A] B` is the integral
  closure of `O` in the reduction of `F ⊗[K] L`.

## References

* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (A O K F B L : Type*) [CommRing A] [CommRing O] [CommRing K] [CommRing F] [CommRing B]
  [CommRing L] [Algebra A O] [Algebra A K] [Algebra A F] [Algebra A B] [Algebra A L]
  [Algebra K F] [Algebra K L] [Algebra O F] [Algebra B L]
  [IsScalarTower A O F] [IsScalarTower A K F] [IsScalarTower A B L] [IsScalarTower A K L]

/-- The structure map `O → F ⊗[K] L` factors through `O ⊗[A] B`: an element `o` of `O` has the
same image `(algebraMap O F o) ⊗ₜ 1` whether it is sent to `F ⊗[K] L` directly or through
`O ⊗[A] B`. -/
theorem isScalarTower_tensorProductFractionRing :
    letI := tensorProductFractionRingAlgebra A O K F B L
    IsScalarTower O (O ⊗[A] B) (F ⊗[K] L) := by
  let _ := tensorProductFractionRingAlgebra A O K F B L
  exact IsScalarTower.of_algebraMap_eq fun o ↦ by
    change _ = (Algebra.TensorProduct.lift _ _ _).toRingHom _
    simp [Algebra.TensorProduct.algebraMap_apply]

/-- For `B` a finite `A`-algebra, the `O ⊗[A] B`-algebra structure on the integral closure of `O`
in the reduction of `F ⊗[K] L` given by the structure map of `O ⊗[A] B`. -/
@[instance_reducible]
def integralClosureTensorProductAlgebra [Module.Finite A B] :
    letI := tensorProductFractionRingAlgebra A O K F B L
    Algebra (O ⊗[A] B) ↥(integralClosure O ((F ⊗[K] L) ⧸ nilradical (F ⊗[K] L))) :=
  letI := tensorProductFractionRingAlgebra A O K F B L
  haveI := isScalarTower_tensorProductFractionRing A O K F B L
  haveI : Module.Finite O (O ⊗[A] B) := Module.Finite.base_change A O B
  haveI : Algebra.IsIntegral O (O ⊗[A] B) := Algebra.IsIntegral.of_finite O (O ⊗[A] B)
  ((IsScalarTower.toAlgHom O (O ⊗[A] B) ((F ⊗[K] L) ⧸ nilradical (F ⊗[K] L))).codRestrict
    (integralClosure O ((F ⊗[K] L) ⧸ nilradical (F ⊗[K] L)))
    fun r ↦ (Algebra.IsIntegral.isIntegral r).map _).toRingHom.toAlgebra

/-- **The integral closure of a base change in the reduction of its fraction ring.** For `A` a
domain with fraction field `K`, `B` a finite flat `A`-algebra with `L` its localization at the
nonzero elements of `A`, and `O` a domain over `A` with fraction field `F`, the integral closure
of `O ⊗[A] B` in the total ring of fractions of the reduction of `O ⊗[A] B` is the integral
closure of `O` in the reduction of `F ⊗[K] L`. -/
theorem nonempty_algEquiv_integralClosure_fractionRing_tensorProduct [IsArtinianRing F]
    [IsDomain O] [Module.Flat A B] [Module.Finite A B] [Module.Finite K L]
    [IsLocalization (nonZeroDivisors A) K]
    [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L]
    [IsLocalization (nonZeroDivisors O) F] :
    letI := tensorProductFractionRingAlgebra A O K F B L
    letI := integralClosureTensorProductAlgebra A O K F B L
    Nonempty (↥(integralClosure (O ⊗[A] B)
        (FractionRing ((O ⊗[A] B) ⧸ nilradical (O ⊗[A] B)))) ≃ₐ[O ⊗[A] B]
      ↥(integralClosure O ((F ⊗[K] L) ⧸ nilradical (F ⊗[K] L)))) := by
  let _ := tensorProductFractionRingAlgebra A O K F B L
  let _ := integralClosureTensorProductAlgebra A O K F B L
  let _ := nilradicalQuotientAlgebra (O ⊗[A] B) (F ⊗[K] L)
  have _ := isFractionRing_nilradicalQuotient_tensorProduct A O K F B L
  have _ := isScalarTower_tensorProductFractionRing A O K F B L
  have _ : IsScalarTower (O ⊗[A] B) ((O ⊗[A] B) ⧸ nilradical (O ⊗[A] B))
      ((F ⊗[K] L) ⧸ nilradical (F ⊗[K] L)) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let e : FractionRing ((O ⊗[A] B) ⧸ nilradical (O ⊗[A] B)) ≃ₐ[O ⊗[A] B]
      ((F ⊗[K] L) ⧸ nilradical (F ⊗[K] L)) :=
    AlgEquiv.ofRingEquiv (f := (IsLocalization.algEquiv
      (nonZeroDivisors ((O ⊗[A] B) ⧸ nilradical (O ⊗[A] B)))
      (FractionRing ((O ⊗[A] B) ⧸ nilradical (O ⊗[A] B)))
      ((F ⊗[K] L) ⧸ nilradical (F ⊗[K] L))).toRingEquiv) fun r ↦ by
      rw [IsScalarTower.algebraMap_apply (O ⊗[A] B) ((O ⊗[A] B) ⧸ nilradical (O ⊗[A] B))
        (FractionRing ((O ⊗[A] B) ⧸ nilradical (O ⊗[A] B)))]
      exact (IsLocalization.algEquiv _ _ _).commutes _ |>.trans
        (IsScalarTower.algebraMap_apply (O ⊗[A] B) ((O ⊗[A] B) ⧸ nilradical (O ⊗[A] B))
          ((F ⊗[K] L) ⧸ nilradical (F ⊗[K] L)) r).symm
  have hmem (x : (F ⊗[K] L) ⧸ nilradical (F ⊗[K] L)) :
      x ∈ integralClosure (O ⊗[A] B) ((F ⊗[K] L) ⧸ nilradical (F ⊗[K] L)) ↔
      x ∈ integralClosure O ((F ⊗[K] L) ⧸ nilradical (F ⊗[K] L)) := by
    rw [integralClosure_eq_restrictScalars_of_isIntegral O (O ⊗[A] B)
      ((F ⊗[K] L) ⧸ nilradical (F ⊗[K] L)), Subalgebra.mem_restrictScalars]
  exact ⟨e.mapIntegralClosure.trans
    { toFun := fun x ↦ ⟨x.1, (hmem x.1).mp x.2⟩
      invFun := fun x ↦ ⟨x.1, (hmem x.1).mpr x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }⟩

end
