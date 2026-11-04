module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveDualityMapBaseChange
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.GeometricPointConservativity

/-!
# The duality map of a relative curve is checked on geometric fibres

Let `f : X ⟶ S` be proper and `ℓ ≥ 1`. For a multiplication `m : E ⊗^L E ⟶ E` and a trace
`t : K ⟶ Λ_S[-2]`, the duality map `D_{m,t}` (`Stacks.EtaleCohomology.curveDualityMap`) is an
isomorphism as soon as, at every geometric point `x` of `S`, the comparison
`x⁻¹ RHom(K, Λ_S[-2]) ⟶ RHom(x⁻¹K, x⁻¹Λ_S[-2])` of [Stacks, Tag 08JF] is invertible and the duality
map of the geometric fibre `f_x : X ×_S x ⟶ x`, for the multiplication and trace induced by `m`
and `t`, is invertible (`isIso_curveDualityMap_of_forall_geometricFibre`).

This is the reduction to geometric fibres in the proof of [Stacks, Tag 03VH]: inverse images to
geometric points detect isomorphisms
(`Stacks.EtaleCohomology.isIso_of_forall_isIso_etaleModuleDerivedInverseImage_map`), and the
inverse image of `D_{m,t}` is the fibre duality map up to isomorphisms
(`Stacks.EtaleCohomology.isIso_etaleModuleDerivedInverseImage_map_curveDualityMap`).

## Main results

* `Stacks.EtaleCohomology.isIso_curveDualityMap_of_forall_geometricFibre`.

## References

* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

open Stacks.EtaleCohomology.ExtensionTorsor

/-- **The duality map of a proper morphism is checked on geometric fibres.** If at every
geometric point `x` of `S` the comparison of [Stacks, Tag 08JF] at `(K, Λ_S[-2])` is invertible
and the duality map of the geometric fibre `pullback.snd f x.hom`, for the induced multiplication
and trace, is invertible, then `D_{m,t}` is invertible. -/
theorem isIso_curveDualityMap_of_forall_geometricFibre (ℓ : ℕ) [NeZero ℓ] {S X : Scheme.{u}}
    (f : X ⟶ S) [IsProper f]
    (m : ((etaleDerivedTensor.{u, 0} (ZMod ℓ) X).obj (curveDualityUnit ℓ f)).obj
      (curveDualityUnit ℓ f) ⟶ curveDualityUnit ℓ f)
    (t : ShiftedHom (curveDualityComplex ℓ f)
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2))
    (hc : ∀ x : GeometricPoint S, IsIso (etaleDerivedInverseImageHomComparison.{u, 0} (ZMod ℓ)
      x.hom (curveDualityComplex ℓ f)
        (((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ))⟦(-2 : ℤ)⟧)))
    (hD : ∀ x : GeometricPoint S, IsIso (curveDualityMap ℓ (pullback.snd f x.hom)
      (curveDualityBaseChangeMultiplication ℓ f x.hom (pullback.snd f x.hom) (pullback.fst f x.hom)
        (IsPullback.of_hasPullback f x.hom).w m)
      (curveDualityBaseChangeTrace ℓ f x.hom (pullback.snd f x.hom) (pullback.fst f x.hom)
        (IsPullback.of_hasPullback f x.hom) t))) :
    IsIso (curveDualityMap ℓ f m t) :=
  isIso_of_forall_isIso_etaleModuleDerivedInverseImage_map (ZMod ℓ) _ fun x =>
    isIso_etaleModuleDerivedInverseImage_map_curveDualityMap ℓ f x.hom (pullback.snd f x.hom)
      (pullback.fst f x.hom) (IsPullback.of_hasPullback f x.hom) m t (hc x) (hD x)

end Stacks.EtaleCohomology

end
