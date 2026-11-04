module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ProperCurveFibreDualityMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.EtaleModuleDerivedStalkDetection
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.SmashPowerSymmetricPower
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective

/-!
# Relative Poincaré duality for a smooth projective curve, from its geometric fibres

Let `k` be an algebraically closed field, `ℓ` a prime invertible in `k`, `S` affine and smooth
over `k`, and `f : X ⟶ S` smooth projective of relative dimension one with geometrically
irreducible fibres. Relative Poincaré duality for `f`
(`Stacks.EtaleCohomology.ProperCurveRelativeDualityInput`, part of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) is reduced here to the compatibility of the
duality map with restriction to the geometric fibres.

For a top-degree trace `t : Rf_* E ⟶ Λ[-2]`, `E = f⁻¹Λ[0]`, the duality map
`D_t : Rf_* E ⟶ RHom(Rf_* E, Λ[-2])` (`Stacks.EtaleCohomology.curveDualityMap` with the canonical
multiplication `Stacks.EtaleCohomology.curveDualityMultiplication`) is an isomorphism as soon as
its derived stalk at every geometric point `x̄ : Spec Ω ⟶ S` is
(`Stacks.EtaleCohomology.isIso_of_forall_isIso_etaleModuleDerivedStalk`). The fibre
`f' : X_{x̄} ⟶ Spec Ω` is a smooth proper curve over an algebraically closed field, and there the
duality map is an isomorphism for every invertible multiplication and every top-degree trace
(`Stacks.EtaleCohomology.isIso_curveDualityMap_fibre`). What connects the two is
`Stacks.EtaleCohomology.CurveDualityStalkComparison`: the derived stalk of `D_t` at `x̄` is
invertible once the duality map `D_{w', t'}` of the fibre is, for some invertible multiplication
`w'` and top-degree trace `t'` of the fibre (proper base change for `Rf_*`, and the compatibility
of `RHom` and of the cup product with the inverse image along `x̄`). An invertible duality map
gives relative duality on the unbounded derived category
(`Stacks.EtaleCohomology.isBijectiveAt_of_isIso_curveDualityMap`), and from there on `D⁺`
(`Stacks.EtaleCohomology.isBijectiveAt_plus_of_forall_isBijectiveAt`).

## Main definitions and results

* `Stacks.EtaleCohomology.CurveDualityStalkComparison`.
* `Stacks.EtaleCohomology.isIso_curveDualityMap_of_curveDualityStalkComparison`.
* `Stacks.EtaleCohomology.properCurveRelativeDualityInput_of_curveDualityStalkComparison`.

The derived categories are those of the standard model `HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

open Stacks.EtaleCohomology.ExtensionTorsor Stacks.RelativeDuality

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **The duality map of a relative curve is compatible with restriction to the geometric
fibres**: in the setting of `Stacks.EtaleCohomology.ProperCurveRelativeDualityInput`, for every
top-degree trace `t : Rf_* E ⟶ Λ[-2]` and every geometric point `x̄ : Spec Ω ⟶ S`, with fibre
`f' : X ×_S Spec Ω ⟶ Spec Ω`, there are an invertible multiplication `w'` and a top-degree trace
`t'` of the fibre such that the derived stalk at `x̄` of the duality map `D_t` of `f` is invertible
whenever the duality map `D_{w', t'}` of `f'` is. -/
def CurveDualityStalkComparison : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k], IsUnit (ℓ : k) →
    ∀ (S X : Scheme.{u}) (q : S ⟶ Spec (.of k)) (e : ℕ) [SmoothOfRelativeDimension e q]
      [IsAffine S] (f : X ⟶ S) [SmoothOfRelativeDimension 1 f] [GeometricallyIrreducible f],
      IsProjectiveMorphism f →
      ∀ t : ShiftedHom (curveDualityComplex ℓ f)
          ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2),
        IsIso ((DerivedCategory.homologyFunctor _ 2).map t) →
        ∀ x : GeometricPoint S,
          ∃ (w' : ((etaleDerivedTensor.{u, 0} (ZMod ℓ) (pullback f x.hom)).obj
                (curveDualityUnit ℓ (pullback.snd f x.hom))).obj
                (curveDualityUnit ℓ (pullback.snd f x.hom)) ⟶
              curveDualityUnit ℓ (pullback.snd f x.hom)) (_ : IsIso w')
            (t' : ShiftedHom (curveDualityComplex ℓ (pullback.snd f x.hom))
              ((DerivedCategory.singleFunctor _ 0).obj
                (unitSheaf (X := Spec (.of x.residueField)) ℓ)) (-2)),
            IsIso ((DerivedCategory.homologyFunctor _ 2).map t') ∧
              (IsIso (curveDualityMap ℓ (pullback.snd f x.hom) w' t') →
                IsIso ((smallEtaleDerivedStalkAb x.hom).map
                  ((etaleModuleUnderlyingAbelian S (ZMod ℓ)).mapDerivedCategory.map
                    (curveDualityMap ℓ f (curveDualityMultiplication ℓ f) t))))

omit [Fact ℓ.Prime] in
/-- `ℓ` invertible in `k` stays invertible in any field over `k`. -/
lemma isUnit_natCast_of_spec_hom {k Ω : Type u} [Field k] [Field Ω]
    (g : Spec (.of Ω) ⟶ Spec (.of k)) (hℓ : IsUnit (ℓ : k)) : IsUnit (ℓ : Ω) := by
  simpa using hℓ.map (Spec.preimage g).hom

/-- **The duality map is invertible**, granted its compatibility with the geometric fibres: the
derived stalk at a geometric point is controlled by the duality map of the fibre, a smooth proper
curve over an algebraically closed field, where it is invertible. -/
theorem isIso_curveDualityMap_of_curveDualityStalkComparison
    (hC : CurveDualityStalkComparison.{u} ℓ) (k : Type u) [Field k] [IsAlgClosed k]
    (hℓ : IsUnit (ℓ : k)) (S X : Scheme.{u}) (q : S ⟶ Spec (.of k)) (e : ℕ)
    [SmoothOfRelativeDimension e q] [IsAffine S] (f : X ⟶ S) [SmoothOfRelativeDimension 1 f]
    [GeometricallyIrreducible f] (hf : IsProjectiveMorphism f)
    (t : ShiftedHom (curveDualityComplex ℓ f)
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2))
    (ht : IsIso ((DerivedCategory.homologyFunctor _ 2).map t)) :
    IsIso (curveDualityMap ℓ f (curveDualityMultiplication ℓ f) t) := by
  refine isIso_of_forall_isIso_etaleModuleDerivedStalk _ fun x => ?_
  obtain ⟨w', hw', t', ht', himp⟩ := hC k hℓ S X q e f hf t ht x
  refine himp ?_
  have := isProper_of_isProjectiveMorphism f hf
  have : SmoothOfRelativeDimension 1 (pullback.snd f x.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback f x.hom) inferInstance
  have : Smooth (pullback.snd f x.hom) := SmoothOfRelativeDimension.smooth 1 _
  have : IsCurve x.residueField (pullback.snd f x.hom) :=
    Stacks.Chow.isCurve_of_smoothOfRelativeDimension_one _
  exact isIso_curveDualityMap_fibre (pullback.snd f x.hom)
    (isUnit_natCast_of_spec_hom ℓ (x.hom ≫ q) hℓ) w' t' ht'

/-- **Relative Poincaré duality for a smooth projective curve**
(`Stacks.EtaleCohomology.ProperCurveRelativeDualityInput`), granted the compatibility of the
duality map with the geometric fibres. -/
theorem properCurveRelativeDualityInput_of_curveDualityStalkComparison
    (hC : CurveDualityStalkComparison.{u} ℓ) (k : Type u) [Field k] [IsAlgClosed k] :
    ProperCurveRelativeDualityInput ℓ k := by
  intro hℓ S X q e _ _ f _ _ hf t ht
  refine isBijectiveAt_plus_of_forall_isBijectiveAt ℓ f (fun τ hτ => ?_) t ht
  have := isIso_curveDualityMap_of_curveDualityStalkComparison ℓ hC k hℓ S X q e f hf τ hτ
  exact isBijectiveAt_of_isIso_curveDualityMap ℓ f τ

end Stacks.EtaleCohomology

end
