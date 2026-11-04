module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveDualityCupBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.EtaleDerivedHomInverseImage

/-!
# The duality map of a relative curve, carried to a base change

Let `f : X ⟶ S` be proper, `Λ = ℤ/ℓ` with `ℓ ≥ 1`, and let `(g, g', f')` complete `f` to a
cartesian square. For a multiplication `m : E ⊗^L E ⟶ E` and a trace `t : K ⟶ Λ_S[-2]`, write
`D = D_{m,t} : K ⟶ RHom(K, Λ_S[-2])` for the duality map (`Stacks.EtaleCohomology.curveDualityMap`)
and `D' = D_{m',t'}` for the duality map of the base change built from the induced multiplication
and trace (`curveDualityBaseChangeMultiplication`, `curveDualityBaseChangeTrace`). This file shows

`g⁻¹(D) ≫ c ≫ RHom(g⁻¹K, ψ) = κ ≫ D' ≫ RHom(κ, Λ_{S'}[-2])`

(`etaleModuleDerivedInverseImage_map_curveDualityMap_comp`), where `c` is the comparison
`g⁻¹ RHom(K, M) ⟶ RHom(g⁻¹K, g⁻¹M)` of [Stacks, Tag 08JF]
(`etaleDerivedInverseImageHomComparison`), `κ : g⁻¹K ≅ K'` is proper base change and
`ψ : g⁻¹(Λ_S[-2]) ≅ Λ_{S'}[-2]`. Consequently, if `c` is invertible at `(K, Λ_S[-2])` and `D'` is
invertible, so is `g⁻¹(D)` (`isIso_etaleModuleDerivedInverseImage_map_curveDualityMap`).

The proof: `g⁻¹(D) ≫ c` is the adjoint of `g⁻¹` of the pairing read through [Stacks, Tag 07A4]
(`etaleDerivedInverseImage_map_homEquiv_symm_comp_homComparison`), that pairing is the pairing of
the base change up to `κ` and `ψ` (`curveDualityPairing_baseChange`), and adjoints of pairings that
agree up to isomorphisms of the arguments and of the target agree up to the same isomorphisms, by
the naturality of the tensor–internal-Hom bijection in its three variables ([Stacks, Tag 08J9]).

## Main results

* `Stacks.EtaleCohomology.etaleModuleDerivedInverseImage_map_curveDualityMap_comp`.
* `Stacks.EtaleCohomology.isIso_etaleModuleDerivedInverseImage_map_curveDualityMap`.

## References

* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.Prod

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

open Stacks.EtaleCohomology.ExtensionTorsor

variable (ℓ : ℕ) [NeZero ℓ] {S X S' X' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S')
  (g' : X' ⟶ X) [IsProper f] (sq : IsPullback g' f' f g)

/-- **The duality map is carried to the duality map of the base change.** With `c` the
comparison of [Stacks, Tag 08JF], `κ : g⁻¹K ≅ K'` and `ψ : g⁻¹(Λ_S[-2]) ≅ Λ_{S'}[-2]`,
`g⁻¹(D_{m,t}) ≫ c ≫ RHom(g⁻¹K, ψ) = κ ≫ D_{m',t'} ≫ RHom(κ, Λ_{S'}[-2])`. -/
theorem etaleModuleDerivedInverseImage_map_curveDualityMap_comp
    (m : ((etaleDerivedTensor.{u, 0} (ZMod ℓ) X).obj (curveDualityUnit ℓ f)).obj
      (curveDualityUnit ℓ f) ⟶ curveDualityUnit ℓ f)
    (t : ShiftedHom (curveDualityComplex ℓ f)
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2)) :
    (etaleModuleDerivedInverseImage.{u, 0} (ZMod ℓ) g).map (curveDualityMap ℓ f m t) ≫
        etaleDerivedInverseImageHomComparison.{u, 0} (ZMod ℓ) g (curveDualityComplex ℓ f)
          (((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ))⟦(-2 : ℤ)⟧) ≫
        (((etaleDerivedHom.{u, 0} (ZMod ℓ) S').obj
          (op ((etaleModuleDerivedInverseImage.{u, 0} (ZMod ℓ) g).obj
            (curveDualityComplex ℓ f)))).map
          (curveDualityShiftedUnitInverseImageIso ℓ g (-2)).hom) =
      (curveDualityComplexBaseChangeIso ℓ f g f' g' sq).hom ≫
        curveDualityMap ℓ f' (curveDualityBaseChangeMultiplication ℓ f g f' g' sq.w m)
          (curveDualityBaseChangeTrace ℓ f g f' g' sq t) ≫
        ((etaleDerivedHom.{u, 0} (ZMod ℓ) S').map
          (curveDualityComplexBaseChangeIso ℓ f g f' g' sq).hom.op).app
          (((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S') ℓ))⟦(-2 : ℤ)⟧) := by
  have hP := curveDualityPairing_baseChange ℓ f g f' g' sq m t
  have hQ : (((etaleDerivedInverseImageTensorIso.{u, 0} (ZMod ℓ) g).inv.app
        (curveDualityComplex ℓ f, curveDualityComplex ℓ f) :
        ((etaleDerivedTensor.{u, 0} (ZMod ℓ) S').obj
          ((etaleModuleDerivedInverseImage.{u, 0} (ZMod ℓ) g).obj (curveDualityComplex ℓ f))).obj
          ((etaleModuleDerivedInverseImage.{u, 0} (ZMod ℓ) g).obj (curveDualityComplex ℓ f)) ⟶
        (etaleModuleDerivedInverseImage.{u, 0} (ZMod ℓ) g).obj
          (((etaleDerivedTensor.{u, 0} (ZMod ℓ) S).obj (curveDualityComplex ℓ f)).obj
            (curveDualityComplex ℓ f))) ≫
      (etaleModuleDerivedInverseImage.{u, 0} (ZMod ℓ) g).map
        ((etaleDerivedTensorBraidingIso.{u, 0} (ZMod ℓ) S _ _).inv ≫ curveDualityCup ℓ f ≫
          (etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).map m ≫ t)) ≫
        (curveDualityShiftedUnitInverseImageIso ℓ g (-2)).hom =
      (Functor.uncurry.obj (etaleDerivedTensor.{u, 0} (ZMod ℓ) S')).map
          ((curveDualityComplexBaseChangeIso ℓ f g f' g' sq).hom ×ₘ
            (curveDualityComplexBaseChangeIso ℓ f g f' g' sq).hom) ≫
        ((etaleDerivedTensorBraidingIso.{u, 0} (ZMod ℓ) S' _ _).inv ≫ curveDualityCup ℓ f' ≫
          (etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f').map
              (curveDualityBaseChangeMultiplication ℓ f g f' g' sq.w m) ≫
            curveDualityBaseChangeTrace ℓ f g f' g' sq t) := by
    rw [Category.assoc, ← hP, Iso.inv_hom_id_app_assoc]
  rw [curveDualityMap, curveDualityMap,
    reassoc_of% (etaleDerivedInverseImage_map_homEquiv_symm_comp_homComparison (ZMod ℓ) g _)]
  simp only [Functor.prod_obj]
  apply ((etaleTensorHomAdjunction.{u, 0} (ZMod ℓ) S').homEquiv _ _ _).injective
  rw [(etaleTensorHomAdjunction.{u, 0} (ZMod ℓ) S').homEquiv_naturality_target,
    Equiv.apply_symm_apply,
    (etaleTensorHomAdjunction.{u, 0} (ZMod ℓ) S').homEquiv_naturality_source,
    (etaleTensorHomAdjunction.{u, 0} (ZMod ℓ) S').homEquiv_naturality_middle,
    Equiv.apply_symm_apply, hQ]
  simp only [Functor.uncurry_obj_map, Category.assoc]

/-- **Invertibility of the duality map descends along the base change**: if the comparison `c`
of [Stacks, Tag 08JF] is invertible at `(K, Λ_S[-2])` and the duality map `D_{m',t'}` of the base
change is invertible, then `g⁻¹(D_{m,t})` is invertible. -/
theorem isIso_etaleModuleDerivedInverseImage_map_curveDualityMap
    (m : ((etaleDerivedTensor.{u, 0} (ZMod ℓ) X).obj (curveDualityUnit ℓ f)).obj
      (curveDualityUnit ℓ f) ⟶ curveDualityUnit ℓ f)
    (t : ShiftedHom (curveDualityComplex ℓ f)
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2))
    (hc : IsIso (etaleDerivedInverseImageHomComparison.{u, 0} (ZMod ℓ) g (curveDualityComplex ℓ f)
      (((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ))⟦(-2 : ℤ)⟧)))
    (hD : IsIso (curveDualityMap ℓ f' (curveDualityBaseChangeMultiplication ℓ f g f' g' sq.w m)
      (curveDualityBaseChangeTrace ℓ f g f' g' sq t))) :
    IsIso ((etaleModuleDerivedInverseImage.{u, 0} (ZMod ℓ) g).map (curveDualityMap ℓ f m t)) := by
  have h := etaleModuleDerivedInverseImage_map_curveDualityMap_comp ℓ f g f' g' sq m t
  have : IsIso ((curveDualityComplexBaseChangeIso ℓ f g f' g' sq).hom ≫
      curveDualityMap ℓ f' (curveDualityBaseChangeMultiplication ℓ f g f' g' sq.w m)
        (curveDualityBaseChangeTrace ℓ f g f' g' sq t) ≫
      ((etaleDerivedHom.{u, 0} (ZMod ℓ) S').map
        (curveDualityComplexBaseChangeIso ℓ f g f' g' sq).hom.op).app
        (((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S') ℓ))⟦(-2 : ℤ)⟧)) :=
    inferInstance
  rw [← h] at this
  exact IsIso.of_isIso_comp_right _
    (etaleDerivedInverseImageHomComparison.{u, 0} (ZMod ℓ) g (curveDualityComplex ℓ f)
      (((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ))⟦(-2 : ℤ)⟧) ≫
      (((etaleDerivedHom.{u, 0} (ZMod ℓ) S').obj
        (op ((etaleModuleDerivedInverseImage.{u, 0} (ZMod ℓ) g).obj
          (curveDualityComplex ℓ f)))).map (curveDualityShiftedUnitInverseImageIso ℓ g (-2)).hom))

end Stacks.EtaleCohomology

end
