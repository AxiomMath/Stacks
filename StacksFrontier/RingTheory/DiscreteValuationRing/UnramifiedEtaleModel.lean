module

public import StacksFrontier.RingTheory.DiscreteValuationRing.UnramifiedIffEtaleIntegralClosure

/-!
# Étale models of algebras unramified over a discrete valuation ring

Let `R` be a discrete valuation ring with fraction field `K` and let `C` be a finite étale
`K`-algebra. If every field quotient of `C` is unramified with respect to `R` in the sense of
[Stacks, Tag 09E9], then `C` has a finite étale model over `R`: a finite étale `R`-algebra `B`
with `K ⊗_R B ≅ C`. The model is the product of the integral closures of `R` in the field factors
of `C`.

## Main results

* `IsDiscreteValuationRing.exists_finite_etale_model_of_isUnramifiedWithRespectTo`: the model.

## Implementation notes

The hypothesis is stated for every field `L` receiving a surjection `C →ₐ[K] L`, so that it can be
supplied for whichever presentation of the field factors (as quotients by maximal ideals, or as
residue fields of the points of `Spec C`) the caller has at hand. The model is formed from the
decomposition of `C` into separable field extensions of `K`,
`Algebra.FormallyEtale.iff_exists_algEquiv_prod`, and each integral closure is étale by
`IsDiscreteValuationRing.isUnramifiedWithRespectTo_iff_etale_integralClosure`.

## References

* [Stacks Project, Tag 09E9](https://stacks.math.columbia.edu/tag/09E9)
* [Stacks Project, Tag 0H2W](https://stacks.math.columbia.edu/tag/0H2W)
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace IsDiscreteValuationRing

/-- **A finite étale algebra unramified over a discrete valuation ring has a finite étale
model.** Let `R` be a discrete valuation ring with fraction field `K` and `C` a finite étale
`K`-algebra all of whose field quotients are unramified with respect to `R`. Then there is a
finite étale `R`-algebra `B` with `K ⊗_R B ≅ C` as `K`-algebras. -/
theorem exists_finite_etale_model_of_isUnramifiedWithRespectTo
    (R : Type u) (K : Type v) (C : Type v)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing C] [Algebra K C] [Algebra.Etale K C]
    (h : ∀ (L : Type v) [Field L] [Algebra K L] [Module.Finite K L] [Algebra.IsSeparable K L]
      [Algebra R L] [IsScalarTower R K L],
      (∃ φ : C →ₐ[K] L, Function.Surjective φ) → IsUnramifiedWithRespectTo R K L) :
    ∃ (B : Type v) (_ : CommRing B) (_ : Algebra R B),
      Algebra.Etale R B ∧ Module.Finite R B ∧ Nonempty (K ⊗[R] B ≃ₐ[K] C) := by
  classical
  obtain ⟨I, hI, Ai, hfield, halg, e, hsep⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod K C).mp inferInstance
  let := Fintype.ofFinite I
  have : Module.Finite K C := Algebra.FormallyUnramified.finite_of_free K C
  let π (i : I) : C →ₐ[K] Ai i := (Pi.evalAlgHom K Ai i).comp e.toAlgHom
  have hπ (i : I) : Function.Surjective (π i) :=
    (Function.surjective_eval i).comp e.surjective
  have hfin (i : I) : Module.Finite K (Ai i) := Module.Finite.of_surjective (π i).toLinearMap (hπ i)
  let (i : I) : Algebra R (Ai i) := ((algebraMap K (Ai i)).comp (algebraMap R K)).toAlgebra
  have htow (i : I) : IsScalarTower R K (Ai i) := IsScalarTower.of_algebraMap_eq' rfl
  have het (i : I) : Algebra.Etale R (integralClosure R (Ai i)) :=
    (isUnramifiedWithRespectTo_iff_etale_integralClosure R K (Ai i) _).mp (h (Ai i) ⟨π i, hπ i⟩)
  have hfinB (i : I) : Module.Finite R (integralClosure R (Ai i)) :=
    IsIntegralClosure.finite R K (Ai i) (integralClosure R (Ai i))
  have hpush (i : I) : Algebra.IsPushout R K (integralClosure R (Ai i)) (Ai i) := by
    have : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R (Ai i))
        (nonZeroDivisors R)) (Ai i) :=
      IsIntegralClosure.isLocalization R K (Ai i) (integralClosure R (Ai i))
    exact (Algebra.IsPushout.comm R (integralClosure R (Ai i)) K (Ai i)).mp
      (Algebra.isPushout_of_isLocalization (nonZeroDivisors R) K (integralClosure R (Ai i)) (Ai i))
  exact ⟨∀ i, integralClosure R (Ai i), inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨(Algebra.TensorProduct.piRight R K K fun i ↦ integralClosure R (Ai i)).trans
      ((AlgEquiv.piCongrRight fun i ↦
        Algebra.IsPushout.equiv R K (integralClosure R (Ai i)) (Ai i)).trans e.symm)⟩⟩

/-- **Unramifiedness is invariant under isomorphism of the discrete valuation ring.** If
`σ : A ≃+* A'` is compatible with the maps of `A` and `A'` to a fraction field `K`, then a finite
separable extension of `K` is unramified with respect to `A` exactly when it is unramified with
respect to `A'`; here one direction is stated. -/
theorem IsUnramifiedWithRespectTo.of_ringEquiv
    {A A' K L : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A']
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra A' K]
    [IsFractionRing A' K] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra A L] [IsScalarTower A K L] [Algebra A' L] [IsScalarTower A' K L]
    (σ : A ≃+* A') (hσ : ∀ a, algebraMap A' K (σ a) = algebraMap A K a)
    (h : IsUnramifiedWithRespectTo A K L) : IsUnramifiedWithRespectTo A' K L := by
  have hL (a : A) : algebraMap A' L (σ a) = algebraMap A L a := by
    rw [IsScalarTower.algebraMap_apply A' K L, hσ, ← IsScalarTower.algebraMap_apply]
  have hL' (a : A') : algebraMap A L (σ.symm a) = algebraMap A' L a := by
    rw [← hL, RingEquiv.apply_symm_apply]
  have hint (x : L) : IsIntegral A x ↔ IsIntegral A' x :=
    ⟨fun h ↦ h.map_of_comp_eq σ.toRingHom (RingHom.id L) (RingHom.ext hL),
      fun h ↦ h.map_of_comp_eq σ.symm.toRingHom (RingHom.id L) (RingHom.ext hL')⟩
  apply (isUnramifiedWithRespectTo_iff_etale_integralClosure A' K L (integralClosure A' L)).mpr
  let ι : integralClosure A L ≃+* integralClosure A' L :=
    { toFun x := ⟨x.1, (hint x.1).mp x.2⟩
      invFun x := ⟨x.1, (hint x.1).mpr x.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl
      map_add' _ _ := rfl }
  have hcomp : algebraMap A' (integralClosure A' L) =
      (ι.toRingHom.comp (algebraMap A (integralClosure A L))).comp σ.symm.toRingHom := by
    ext a
    exact (hL' a).symm
  refine RingHom.etale_algebraMap.mp ?_
  rw [hcomp]
  exact RingHom.Etale.respectsIso.2 _ σ.symm
    (RingHom.Etale.respectsIso.1 (algebraMap A (integralClosure A L)) ι
      (RingHom.etale_algebraMap.mpr
        ((isUnramifiedWithRespectTo_iff_etale_integralClosure A K L _).mp h)))

end IsDiscreteValuationRing
