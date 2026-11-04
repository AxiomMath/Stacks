module

public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp

/-!
# The comparison of derived extension of scalars, transported along an equality of ring maps

For a homomorphism `ψ : A →+* C` of commutative rings,
`CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.comparison` compares derived
extension of scalars along `ψ` with the degreewise one followed by localization. This file states
the comparison with its target spelled as that composite, and its compatibility with equalities of
ring maps and with composites of ring maps.

## Main definitions

* `CochainComplex.DerivedExtensionScalars.extendScalarsComparison`: the comparison, with its
  target spelled as degreewise extension of scalars followed by the localization functor.

## Main results

* `CochainComplex.DerivedExtensionScalars.extendScalarsComparison_congr`: the renaming of derived
  extension of scalars along an equality of ring maps is compatible with the comparison and with
  the renaming of degreewise extension of scalars.
* `CochainComplex.DerivedExtensionScalars.extendScalarsComparison_comp`: the comparison is
  compatible with the scalar-tower isomorphisms of a composite of ring maps ([Stacks, Tag 06Y5]).

## References

* [Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u wA wC

namespace CochainComplex.DerivedExtensionScalars

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [HasDerivedCategory.{wA} (ModuleCat.{u} A)] [HasDerivedCategory.{wC} (ModuleCat.{u} C)]

/-- The comparison from derived extension of scalars along `ψ` to degreewise extension of scalars
followed by the localization functor. -/
def extendScalarsComparison (ψ : A →+* C) [(ModuleCat.extendScalars.{u, u, u} ψ).Additive] :
    DerivedCategory.Q ⋙ (totalDerivedExtensionScalars.{u, u, u} ψ).functor ⟶
      (ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  (totalDerivedExtensionScalars.{u, u, u} ψ).comparison

/-- `extendScalarsComparison ψ` is the comparison of `totalDerivedExtensionScalars ψ`. -/
theorem extendScalarsComparison_eq (ψ : A →+* C)
    [(ModuleCat.extendScalars.{u, u, u} ψ).Additive] :
    extendScalarsComparison.{u, wA, wC} ψ =
      (totalDerivedExtensionScalars.{u, u, u} ψ).comparison :=
  rfl

/-- For `e : ψ₁ = ψ₂`, the renaming of derived extension of scalars along `e` followed by the
comparison of `ψ₂` is the comparison of `ψ₁` followed by the degreewise renaming. -/
theorem extendScalarsComparison_congr {ψ₁ ψ₂ : A →+* C}
    [(ModuleCat.extendScalars.{u, u, u} ψ₁).Additive]
    [(ModuleCat.extendScalars.{u, u, u} ψ₂).Additive] (e : ψ₁ = ψ₂)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    (extendScalarsComparison.{u, wA, wC} ψ₁).app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (eqToHom (congrArg ModuleCat.extendScalars.{u, u, u} e))
          (ComplexShape.up ℤ)).app P) =
      (eqToIso (congrArg (fun ψ => (totalDerivedExtensionScalars.{u, u, u} ψ).functor)
            e)).hom.app (DerivedCategory.Q.obj P) ≫
        (extendScalarsComparison.{u, wA, wC} ψ₂).app P := by
  subst e
  simp

variable [HasDerivedCategory.{wA} (ModuleCat.{u} B)]

/-- [Stacks, Tag 06Y5] for the comparisons: derived extension of scalars along `ψ` applied to the
comparison of `φ`, followed by the comparison of `ψ` and the inverse of the degreewise scalar-tower
isomorphism `ModuleCat.extendScalarsComp φ ψ`, is the derived scalar-tower isomorphism followed by
the comparison of `ψ.comp φ`. -/
theorem extendScalarsComparison_comp (φ : A →+* B) (ψ : B →+* C)
    [(ModuleCat.extendScalars.{u, u, u} φ).Additive]
    [(ModuleCat.extendScalars.{u, u, u} ψ).Additive]
    [(ModuleCat.extendScalars.{u, u, u} (ψ.comp φ)).Additive]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    (totalDerivedExtensionScalars.{u, u, u} ψ).functor.map
          ((extendScalarsComparison.{u, wA, wA} φ).app P) ≫
        (extendScalarsComparison.{u, wA, wC} ψ).app
          (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (ModuleCat.extendScalarsComp.{u, u} φ ψ).inv (ComplexShape.up ℤ)).app P) =
      (totalDerivedExtensionScalarsComp.{u, u} φ ψ).hom.app (DerivedCategory.Q.obj P) ≫
        (extendScalarsComparison.{u, wA, wC} (ψ.comp φ)).app P :=
  totalDerivedExtensionScalarsComp_comparison.{u, u} φ ψ P

end CochainComplex.DerivedExtensionScalars

end
