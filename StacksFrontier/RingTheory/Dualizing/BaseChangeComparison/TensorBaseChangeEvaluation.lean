module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorMateFormula
import StacksFrontier.RingTheory.Dualizing.RelativeBiduality

/-!
# The lax structure map of derived base change without an existential

`Dualizing.derivedTensorBaseChange_eq_model` states that the lax monoidal structure map `μ` of
derived base change is, at arbitrary arguments, the localization of a map of complexes — but only
*existentially*: it produces a chain map `h` without saying which one, and a consumer that needs
`μ` itself therefore learns nothing it can compute with.

The existential is avoidable.  `Dualizing.derivedTensorBaseChange_eq` writes `μ` as the adjoint
transpose, under the tensor–Hom adjunction of [stacks 0A63] over `A`, of the coevaluation of
[stacks 0A63] over `R` followed by the derived-Hom base-change morphism of [stacks 0E1X]; and
`Dualizing.homEquiv_eq_tensorMap_comp_evaluation` writes *every* adjoint transpose under that
adjunction as the morphism tensored with an identity, followed by the canonical evaluation.
Composing the two leaves `μ` as a composite of three named morphisms, with no existential, no
chosen model and no resolution:

`μ = (F(coev) ⊗ 1) ≫ (0E1X ⊗ 1) ≫ ev`.

Since
`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_eq_of_models_Q` pins the middle factor,
the chain map `h` of `Dualizing.derivedTensorBaseChange_eq_model` is not needed at all.

## Main results

* `Dualizing.derivedTensorBaseChange_eq_evaluation` — `μ` is the transposed morphism tensored
  with the identity, followed by evaluation.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
-/

@[expose] public noncomputable section

open CategoryTheory StacksDraft.DerivedHom

namespace Dualizing

universe uR uA uM

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

/-- **The lax monoidal structure map of derived base change, with no existential.** `μ` at
arbitrary objects `X` and `Y` is `F` applied to the coevaluation of [stacks 0A63] over `R`,
followed by the derived-Hom base-change morphism of [stacks 0E1X] at `(Y, X ⊗ᴸ_R Y)`, the whole
tensored with the identity of `F Y`, followed by the canonical evaluation of [stacks 0A63] over
`A`.

This is `Dualizing.derivedTensorBaseChange_eq` followed by
`Dualizing.homEquiv_eq_tensorMap_comp_evaluation`.  In particular the chain map produced
existentially by `Dualizing.derivedTensorBaseChange_eq_model` is not needed: every factor here is
a named morphism, and the middle one is pinned by
`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_eq_of_models_Q`. -/
theorem derivedTensorBaseChange_eq_evaluation
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y =
      (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.map
          (show (F.obj X, F.obj Y) ⟶
              ((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                    max uR uA uM + 1} A).hom.obj
                  (Opposite.op (F.obj Y),
                    F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                      max uR uA uM + 1} R).tensor.obj (X, Y))),
                F.obj Y) from
            (F.map ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                  max uR uA uM + 1} R).tensorHomUnit X Y) ≫
                Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uA, uM} f F
                  comparison Y
                  ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                    max uR uA uM + 1} R).tensor.obj (X, Y)),
              𝟙 (F.obj Y))) ≫
        (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).evaluation
          (F.obj Y)
          (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
            max uR uA uM + 1} R).tensor.obj (X, Y))) := by
  rw [derivedTensorBaseChange_eq.{uR, uA, uM} f F comparison X Y,
    homEquiv_eq_tensorMap_comp_evaluation]

end Dualizing

end
