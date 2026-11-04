module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeIdentification

/-!
# The keystone with [stacks 0E1W] on its canonical side

`Dualizing.unit_comp_homEquiv_symm_iff` says that a morphism `g : F X ⊗ᴸ_A F Y ⟶ F (X ⊗ᴸ_R Y)` is
the lax monoidal structure map of derived base change exactly when

`η_X ≫ (transpose of g)|_R = (transpose of η_{X ⊗ᴸ_R Y}) ≫ 0E1W_{Y, F (X ⊗ᴸ_R Y)}`,

with `η` the unit of [stacks 0GMT] and `0E1W` the change-of-rings isomorphism for derived Hom.
The component of [stacks 0E1W] is an isomorphism, so it may be moved to the other side: the
keystone becomes

`(η_X ≫ (transpose of g)|_R) ≫ 0E1W⁻¹_{Y, F (X ⊗ᴸ_R Y)} = transpose of η_{X ⊗ᴸ_R Y}`,

in which [stacks 0E1W] occurs only through its **inverse**. That is its canonical side: by
`Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_inv_eq_monoidalIso`, the inverse
of the representative model comparison is the [stacks 0A63] transpose of the degreewise
monoidality isomorphism, with nothing inverted, whereas its hom direction, valued by
`Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_hom_eq_monoidalIso`, carries an
inverted transpose. The [stacks 068I] candidate, valued by
`Dualizing.tensorBaseChangeMor_comp_eq_q_obj`, inverts nothing either.

Neither the keystone nor `Dualizing.TensorComparisonCompatibility` is proved here, and no tag
loses its conditional caveat.

## Main results

* `Dualizing.eq_derivedTensorBaseChange_iff_natIso_inv` — a morphism is the lax monoidal
  structure map exactly when the transposed equation holds with the **inverse** component of
  [stacks 0E1W].
* `Dualizing.tensorBaseChangeMor_eq_iff_natIso_inv` — the same at the [stacks 068I] candidate,
  i.e. the keystone itself.

## Implementation notes

The equation is restated in full rather than abbreviated, so that the equivalence is at exactly
the proposition `Dualizing.unit_comp_homEquiv_symm_iff` states.

No `@[stacks]` attribute is placed here: the obligation is still open, so nothing in this file
covers a tag.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars
open CochainComplex.DerivedTensor

attribute [local instance] HasDerivedCategory.standard

universe uR uA uM

namespace Dualizing

attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [hF : F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

include hF in
/-- **A morphism is the lax monoidal structure map of derived base change exactly when the
transposed equation holds with the inverse component of [stacks 0E1W].**

This is `Dualizing.unit_comp_homEquiv_symm_iff` with the component of [stacks 0E1W] moved across
the equation, so that the right-hand side is the bare transpose of the unit of [stacks 0GMT] at
`X ⊗ᴸ_R Y`. -/
theorem eq_derivedTensorBaseChange_iff_natIso_inv
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R))
    (g : (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj
        (F.obj X, F.obj Y) ⟶
      F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
        (X, Y))) :
    g = derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y ↔
      ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X ≫
            (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
              (((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                  max uR uA uM + 1} A).homEquiv (F.obj X) (F.obj Y)
                  (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                    max uR uA uM + 1} R).tensor.obj (X, Y)))).symm g)) ≫
          (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
              comparison).inv.app
            (Opposite.op Y, F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
              max uR uA uM + 1} R).tensor.obj (X, Y))) =
        ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv X Y
            ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
              (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                max uR uA uM + 1} R).tensor.obj (X, Y))))).symm
          ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
            ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
              max uR uA uM + 1} R).tensor.obj (X, Y))) := by
  rw [← unit_comp_homEquiv_symm_iff.{uR, uA, uM} f F comparison X Y g]
  exact (Iso.comp_inv_eq
    ((Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
      comparison).app (Opposite.op Y, F.obj
        ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
          max uR uA uM + 1} R).tensor.obj (X, Y))))).symm

variable (D : TotalDerivedExtensionScalars.{uR, max uR uA uM, uA, max uR uA uM + 1,
  max uR uA uM + 1} f)

include hF in
/-- **The keystone with [stacks 0E1W] on its canonical side.**  The [stacks 068I] morphism
`Dualizing.tensorBaseChangeMor` is the lax monoidal structure map of derived base change exactly
when its transpose over [stacks 0GMT], followed by the **inverse** component of [stacks 0E1W], is
the transpose of the unit of [stacks 0GMT] at `X ⊗ᴸ_R Y`.

This is `Dualizing.eq_derivedTensorBaseChange_iff_natIso_inv` at the [stacks 068I] candidate,
the same equation as `Dualizing.tensorBaseChangeMor_eq_iff` with [stacks 0E1W] moved across. -/
theorem tensorBaseChangeMor_eq_iff_natIso_inv
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y =
        derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y ↔
      ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X ≫
            (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
              (((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                  max uR uA uM + 1} A).homEquiv (F.obj X) (F.obj Y)
                  (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                    max uR uA uM + 1} R).tensor.obj (X, Y)))).symm
                (tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y))) ≫
          (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
              comparison).inv.app
            (Opposite.op Y, F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
              max uR uA uM + 1} R).tensor.obj (X, Y))) =
        ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv X Y
            ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
              (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                max uR uA uM + 1} R).tensor.obj (X, Y))))).symm
          ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
            ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
              max uR uA uM + 1} R).tensor.obj (X, Y))) :=
  eq_derivedTensorBaseChange_iff_natIso_inv.{uR, uA, uM} f F comparison X Y
    (tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y)

end Dualizing

end
