module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeBridge

/-!
# The lax monoidal structure of derived restriction of scalars

Let `f : R → A` be a homomorphism of commutative rings, `F` a model of derived extension of
scalars along `f`, and `U = Res_f` derived restriction of scalars. Extension of scalars is strong
monoidal, so its right adjoint `U` is lax monoidal; on cochain complexes the structure map is
`CochainComplex.ExtendScalars.restrictScalarsLaxTensor`. On derived categories, in the tensor
vocabulary of [stacks 0A63], the structure map is the transpose of the inverse of the
change-of-rings isomorphism of [stacks 0E1W].

Two maps are constructed, the second being the first with the unit of [stacks 0GMT] whiskered into
the second variable:

* `Dualizing.restrictScalarsDerivedProjection` -- the projection-formula map
  `U W ⊗ᴸ_R Y ⟶ U (W ⊗ᴸ_A F Y)`, the transpose of
  `U W ⟶ U RHom_A(F Y, W ⊗ᴸ_A F Y) ⟶ RHom_R(Y, U (W ⊗ᴸ_A F Y))`;
* `Dualizing.restrictScalarsDerivedLaxTensor` -- the lax monoidal structure map
  `U W ⊗ᴸ_R U W' ⟶ U (W ⊗ᴸ_A W')`, the same with the contravariant slot moved from `F (U W')` to
  `W'` along the counit.

`Dualizing.derivedTensorBaseChange` is the lax monoidal structure map `μ` of derived base change,
and `Dualizing.tensorBaseChangeMor` is the candidate `μ'` of [stacks 068I].
`Dualizing.eq_derivedTensorBaseChange_iff_unit_monoidal` says that `μ' = μ` **if and only if**

`(η_X ⊗ᴸ η_Y) ≫ lax_{F X, F Y} ≫ U μ' = η_{X ⊗ᴸ Y}`,

i.e. if and only if the unit of [stacks 0GMT] is monoidal for `μ'` and the lax structure of
restriction of scalars. Both sides are morphisms `X ⊗ᴸ_R Y ⟶ U (F (X ⊗ᴸ_R Y))`, and at a pair of
K-flat complexes the equation is the degreewise identity
`k ⊗ l ↦ (1 ⊗ k) ⊗ (1 ⊗ l) ↦ 1 ⊗ (k ⊗ l)`; its chain-level counterpart is
`CochainComplex.ExtendScalars.unit_tensorHom_comp_restrictScalarsLaxTensor`.

## Main definitions

* `Dualizing.restrictScalarsDerivedProjection` -- the projection-formula map
  `U W ⊗ᴸ_R Y ⟶ U (W ⊗ᴸ_A F Y)`.
* `Dualizing.restrictScalarsDerivedEvaluation` -- the restricted evaluation
  `U RHom_A(F Y, Z) ⊗ᴸ_R Y ⟶ U Z`, the transpose of the inverse component of [stacks 0E1W].
* `Dualizing.restrictScalarsDerivedLaxTensor` -- the lax monoidal structure map
  `U W ⊗ᴸ_R U W' ⟶ U (W ⊗ᴸ_A W')` of derived restriction of scalars.

## Main results

* `Dualizing.homEquiv_symm_restrictScalarsDerivedProjection`,
  `Dualizing.homEquiv_symm_restrictScalarsDerivedLaxTensor` -- the transposes of the two maps.
* `Dualizing.homEquiv_restrictScalars_map_comp_derivedHomRestrictScalarsNatIso_inv` -- the
  transpose over `R` of a restricted morphism followed by the inverse of [stacks 0E1W] is the
  projection map followed by the restriction of the transpose over `A`.
* `Dualizing.restrictScalarsDerivedProjection_eq` -- the projection map is the lax structure map
  with the unit of [stacks 0GMT] whiskered into the second variable.
* `Dualizing.restrictScalarsDerivedProjection_eq_evaluation` -- the projection map is the
  restricted evaluation with the restricted coevaluation of [stacks 0A63] whiskered into the first
  variable.
* `Dualizing.homEquiv_symm_restrictScalarsDerivedEvaluation` -- the transpose of the restricted
  evaluation is the inverse component of [stacks 0E1W].
* `Dualizing.eq_derivedTensorBaseChange_iff_unit_monoidal` -- a morphism is the lax monoidal
  structure map of derived base change if and only if the unit of [stacks 0GMT] is monoidal for it.
* `Dualizing.tensorBaseChangeMor_eq_iff_unit_monoidal` -- the same for the candidate of
  [stacks 068I].

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars
open scoped ChangeOfRings

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
  [F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

/-- Naturality of the inverse of [stacks 0E1W], for the pair of morphisms `((F a).op, b)`. -/
private theorem map_hom_map_comp_derivedHomRestrictScalarsNatIso_inv_app
    {Y Y' : DerivedCategory (ModuleCat.{max uR uA uM} R)}
    {Z Z' : DerivedCategory (ModuleCat.{max uR uA uM} A)} (a : Y ⟶ Y') (b : Z ⟶ Z') :
    (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
        ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).hom.map
          (((F.map a).op, b) :
            (Opposite.op (F.obj Y'), Z) ⟶ (Opposite.op (F.obj Y), Z'))) ≫
      (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
        comparison).inv.app (Opposite.op Y, Z') =
    (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
        comparison).inv.app (Opposite.op Y', Z) ≫
      (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).hom.map
        ((a.op, (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map b) :
          (Opposite.op Y', (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj Z) ⟶
            (Opposite.op Y,
              (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj Z')) :=
  (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
    comparison).inv.naturality ((a.op, b) : (Opposite.op Y', Z) ⟶ (Opposite.op Y, Z'))

/-- **The projection-formula map of derived restriction of scalars**:
`U W ⊗ᴸ_R Y ⟶ U (W ⊗ᴸ_A F Y)`, for `U` derived restriction of scalars along `f : R → A` and `F` a
model of derived extension of scalars.

It is the transpose over `R`, under the tensor--Hom adjunction of [stacks 0A63], of the
coevaluation `W ⟶ RHom_A(F Y, W ⊗ᴸ_A F Y)` of [stacks 0A63] over `A`, restricted along `f` and
followed by the inverse of the change-of-rings isomorphism of [stacks 0E1W] at `(Y, W ⊗ᴸ_A F Y)`.

This is `Dualizing.restrictScalarsDerivedLaxTensor` with the unit of [stacks 0GMT] whiskered into
the second variable; see `Dualizing.restrictScalarsDerivedProjection_eq`. -/
noncomputable def restrictScalarsDerivedProjection
    (W : DerivedCategory (ModuleCat.{max uR uA uM} A))
    (Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
        ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj W, Y) ⟶
      (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
        ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj
          (W, F.obj Y)) :=
  (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv
      ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj W) Y
      ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
        ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj
          (W, F.obj Y)))
    ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
        ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensorHomUnit
          W (F.obj Y)) ≫
      (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
          comparison).inv.app
        (Opposite.op Y,
          (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj
            (W, F.obj Y)))

/-- **The restricted evaluation of [stacks 0E1W]**:
`U RHom_A(F Y, Z) ⊗ᴸ_R Y ⟶ U Z`, the transpose over `R` of the inverse component of the
change-of-rings isomorphism of [stacks 0E1W] at `(Y, Z)`. It is the counit of the restriction of
scalars of an internal Hom. -/
noncomputable def restrictScalarsDerivedEvaluation
    (Y : DerivedCategory (ModuleCat.{max uR uA uM} R))
    (Z : DerivedCategory (ModuleCat.{max uR uA uM} A)) :
    (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
        ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
          ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).hom.obj
            (Opposite.op (F.obj Y), Z)), Y) ⟶
      (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj Z :=
  (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv
      ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
        ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).hom.obj
          (Opposite.op (F.obj Y), Z))) Y
      ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj Z)
    ((Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
      comparison).inv.app (Opposite.op Y, Z))

/-- The defining transpose of `Dualizing.restrictScalarsDerivedEvaluation`: it is the inverse
component of the change-of-rings isomorphism of [stacks 0E1W]. -/
theorem homEquiv_symm_restrictScalarsDerivedEvaluation
    (Y : DerivedCategory (ModuleCat.{max uR uA uM} R))
    (Z : DerivedCategory (ModuleCat.{max uR uA uM} A)) :
    ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv
          ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
            ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).hom.obj
              (Opposite.op (F.obj Y), Z))) Y
          ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj Z)).symm
        (restrictScalarsDerivedEvaluation.{uR, uA, uM} f F comparison Y Z) =
      (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
        comparison).inv.app (Opposite.op Y, Z) :=
  ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv
    ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
      ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).hom.obj
        (Opposite.op (F.obj Y), Z))) Y
    ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj Z)).symm_apply_apply _

/-- **The projection-formula map through the restricted evaluation of [stacks 0E1W].**  Tensoring
the restricted coevaluation of [stacks 0A63] over `A` into the first variable and following with
`Dualizing.restrictScalarsDerivedEvaluation` gives
`Dualizing.restrictScalarsDerivedProjection`. -/
theorem restrictScalarsDerivedProjection_eq_evaluation
    (W : DerivedCategory (ModuleCat.{max uR uA uM} A))
    (Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    restrictScalarsDerivedProjection.{uR, uA, uM} f F comparison W Y =
      (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.map
          (((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
                ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensorHomUnit
                  W (F.obj Y)), 𝟙 Y) :
            (((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj W, Y) :
                DerivedCategory (ModuleCat.{max uR uA uM} R) ×
                  DerivedCategory (ModuleCat.{max uR uA uM} R)) ⟶
              ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
                  ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).hom.obj
                    (Opposite.op (F.obj Y),
                      (derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                        max uR uA uM + 1} A).tensor.obj (W, F.obj Y))), Y)) ≫
        restrictScalarsDerivedEvaluation.{uR, uA, uM} f F comparison Y
          ((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
            max uR uA uM + 1} A).tensor.obj (W, F.obj Y)) :=
  (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv_naturality_left
    ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
      ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensorHomUnit
        W (F.obj Y))) _

/-- **Transposes through the inverse of [stacks 0E1W].** For a morphism
`ν : W ⟶ RHom_A(F Y, Z)` over `A`, the transpose over `R` of its restriction followed by the
inverse of the change-of-rings isomorphism of [stacks 0E1W] is the projection-formula map followed
by the restriction of the transpose of `ν` over `A`.

Equivalently: the projection-formula map is the universal such transpose, and every value of the
inverse of [stacks 0E1W] factors through it. -/
theorem homEquiv_restrictScalars_map_comp_derivedHomRestrictScalarsNatIso_inv
    (W Z : DerivedCategory (ModuleCat.{max uR uA uM} A))
    (Y : DerivedCategory (ModuleCat.{max uR uA uM} R))
    (nu : W ⟶ (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).hom.obj
      (Opposite.op (F.obj Y), Z)) :
    (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv
        ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj W) Y
        ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj Z)
        ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map nu ≫
          (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
            comparison).inv.app (Opposite.op Y, Z)) =
      restrictScalarsDerivedProjection.{uR, uA, uM} f F comparison W Y ≫
        (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
          ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).homEquiv
            W (F.obj Y) Z nu) := by
  have hnu : nu =
      (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensorHomUnit
          W (F.obj Y) ≫
        (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).hom.map
          ((𝟙 (Opposite.op (F.obj Y)),
              (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).homEquiv
                W (F.obj Y) Z nu) :
            (Opposite.op (F.obj Y),
                (derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                  max uR uA uM + 1} A).tensor.obj (W, F.obj Y)) ⟶
              (Opposite.op (F.obj Y), Z)) :=
    ((DerivedHomAdjunction.tensorHomUnit_comp_hom_map
        (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A) W (F.obj Y) Z
        ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).homEquiv
          W (F.obj Y) Z nu)).trans
      (((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
        max uR uA uM + 1} A).homEquiv W (F.obj Y) Z).symm_apply_apply nu)).symm
  have h := map_hom_map_comp_derivedHomRestrictScalarsNatIso_inv_app.{uR, uA, uM} f F comparison
    (𝟙 Y) ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).homEquiv
      W (F.obj Y) Z nu)
  simp only [CategoryTheory.Functor.map_id, op_id] at h
  refine (congrArg _ ?_).trans
    ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv_naturality_right
      _ _)
  conv_lhs => rw [hnu, Functor.map_comp]
  erw [Category.assoc, h]
  exact (Category.assoc _ _ _).symm

/-- **The characterizing equation of `Dualizing.derivedTensorBaseChange`, transposed.**  The
equation of `Dualizing.unit_comp_homEquiv_symm_derivedTensorBaseChange` -- the double transpose of
a morphism `g` is the transpose of the unit of [stacks 0GMT] followed by the change-of-rings
isomorphism of [stacks 0E1W] -- holds if and only if the unit of [stacks 0GMT] at `X`, tensored
with `Y`, followed by the projection-formula map and the restriction of `g`, is the unit at
`X ⊗ᴸ_R Y`. -/
theorem unit_comp_homEquiv_symm_eq_iff_unit_comp_restrictScalarsDerivedProjection
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R))
    (g : (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj
        (F.obj X, F.obj Y) ⟶
      F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
        (X, Y))) :
    ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X ≫
          (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
            (((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).homEquiv
                (F.obj X) (F.obj Y)
                (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                  max uR uA uM + 1} R).tensor.obj (X, Y)))).symm g) =
        ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv X Y
              ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
                (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                  max uR uA uM + 1} R).tensor.obj (X, Y))))).symm
            ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
              ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                max uR uA uM + 1} R).tensor.obj (X, Y))) ≫
          (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
              comparison).hom.app
            (Opposite.op Y, F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
              max uR uA uM + 1} R).tensor.obj (X, Y)))) ↔
      (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.map
            (((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X, 𝟙 Y) :
              ((X, Y) : DerivedCategory (ModuleCat.{max uR uA uM} R) ×
                  DerivedCategory (ModuleCat.{max uR uA uM} R)) ⟶
                ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj (F.obj X),
                  Y)) ≫
          restrictScalarsDerivedProjection.{uR, uA, uM} f F comparison (F.obj X) Y ≫
            (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map g =
        (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
          ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
            max uR uA uM + 1} R).tensor.obj (X, Y)) := by
  have hcalc : (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv X Y
        ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
          (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
            max uR uA uM + 1} R).tensor.obj (X, Y))))
        (((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X ≫
              (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
                (((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).homEquiv
                    (F.obj X) (F.obj Y)
                    (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                      max uR uA uM + 1} R).tensor.obj (X, Y)))).symm g)) ≫
          (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
              comparison).inv.app
            (Opposite.op Y, F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
              max uR uA uM + 1} R).tensor.obj (X, Y)))) =
      (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.map
            (((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X, 𝟙 Y) :
              ((X, Y) : DerivedCategory (ModuleCat.{max uR uA uM} R) ×
                  DerivedCategory (ModuleCat.{max uR uA uM} R)) ⟶
                ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj (F.obj X),
                  Y)) ≫
          restrictScalarsDerivedProjection.{uR, uA, uM} f F comparison (F.obj X) Y ≫
            (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map g := by
    refine Eq.trans (congrArg
      ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv X Y
        ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
          (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
            max uR uA uM + 1} R).tensor.obj (X, Y))))) (Category.assoc _ _ _)) ?_
    refine Eq.trans ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
      max uR uA uM + 1} R).homEquiv_naturality_left
        ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X) _) ?_
    refine congrArg (fun z =>
      (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.map
          (((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X, 𝟙 Y) :
            ((X, Y) : DerivedCategory (ModuleCat.{max uR uA uM} R) ×
                DerivedCategory (ModuleCat.{max uR uA uM} R)) ⟶
              ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj (F.obj X),
                Y)) ≫ z) ?_
    refine Eq.trans (homEquiv_restrictScalars_map_comp_derivedHomRestrictScalarsNatIso_inv.{uR,
      uA, uM} f F comparison (F.obj X)
      (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
        max uR uA uM + 1} R).tensor.obj (X, Y))) Y _) ?_
    exact congrArg (fun z =>
      restrictScalarsDerivedProjection.{uR, uA, uM} f F comparison (F.obj X) Y ≫
        (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map z)
      (((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).homEquiv (F.obj X)
        (F.obj Y) (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
          max uR uA uM + 1} R).tensor.obj (X, Y)))).apply_symm_apply g)
  have hb : (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv X Y
        ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
          (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
            max uR uA uM + 1} R).tensor.obj (X, Y))))
        (((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv X Y
            ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
              (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
                max uR uA uM + 1} R).tensor.obj (X, Y))))).symm
          ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
            ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
              max uR uA uM + 1} R).tensor.obj (X, Y)))) =
      (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
        ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
          max uR uA uM + 1} R).tensor.obj (X, Y)) :=
    ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv X Y
      ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
        (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
          max uR uA uM + 1} R).tensor.obj (X, Y))))).apply_symm_apply _
  refine Iff.trans (Iso.comp_inv_eq
    ((Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
      comparison).app (Opposite.op Y,
        F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
          max uR uA uM + 1} R).tensor.obj (X, Y))))).symm ?_
  refine Iff.trans (Function.Injective.eq_iff
    ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv X Y
      ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
        (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
          max uR uA uM + 1} R).tensor.obj (X, Y))))).injective).symm ?_
  exact Eq.congr hcalc hb

/-- **A morphism is the lax monoidal structure map of derived base change if and only if the unit
of [stacks 0GMT] is monoidal for it**, in the half-whiskered form. -/
theorem eq_derivedTensorBaseChange_iff_unit_comp_restrictScalarsDerivedProjection
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R))
    (g : (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj
        (F.obj X, F.obj Y) ⟶
      F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
        (X, Y))) :
    g = derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y ↔
      (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.map
            (((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X, 𝟙 Y) :
              ((X, Y) : DerivedCategory (ModuleCat.{max uR uA uM} R) ×
                  DerivedCategory (ModuleCat.{max uR uA uM} R)) ⟶
                ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj (F.obj X),
                  Y)) ≫
          restrictScalarsDerivedProjection.{uR, uA, uM} f F comparison (F.obj X) Y ≫
            (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map g =
        (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
          ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
            max uR uA uM + 1} R).tensor.obj (X, Y)) := by
  refine Iff.intro (fun h => ?_) (fun h =>
    eq_derivedTensorBaseChange_of_unit.{uR, uA, uM} f F comparison X Y g
      ((unit_comp_homEquiv_symm_eq_iff_unit_comp_restrictScalarsDerivedProjection.{uR, uA, uM}
        f F comparison X Y g).mpr h))
  subst h
  exact (unit_comp_homEquiv_symm_eq_iff_unit_comp_restrictScalarsDerivedProjection.{uR, uA, uM}
      f F comparison X Y _).mp
    (unit_comp_homEquiv_symm_derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y)

/-- **The lax monoidal structure map of derived restriction of scalars**:
`U W ⊗ᴸ_R U W' ⟶ U (W ⊗ᴸ_A W')`, in the tensor vocabulary of [stacks 0A63].

Derived extension of scalars is left adjoint to `U` by [stacks 0GMT] and is strong monoidal, so
`U` is lax monoidal. The structure map is defined from the change-of-rings isomorphism of
[stacks 0E1W]: it is the transpose over `R` of the coevaluation `W ⟶ RHom_A(W', W ⊗ᴸ_A W')` of
[stacks 0A63] over `A`, pushed along the counit of [stacks 0GMT] into the contravariant slot
`F (U W')`, restricted along `f`, and followed by the inverse of [stacks 0E1W] at
`(U W', W ⊗ᴸ_A W')`.

The chain-level counterpart is `CochainComplex.ExtendScalars.restrictScalarsLaxTensor`. -/
noncomputable def restrictScalarsDerivedLaxTensor
    (W W' : DerivedCategory (ModuleCat.{max uR uA uM} A)) :
    (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
        ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj W,
          (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj W') ⟶
      (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
        ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj
          (W, W')) :=
  (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv
      ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj W)
      ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj W')
      ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
        ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj (W, W')))
    ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
        ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensorHomUnit
            W W' ≫
          (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).hom.map
            ((((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).counit.app W').op,
                𝟙 ((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                  max uR uA uM + 1} A).tensor.obj (W, W'))) :
              (Opposite.op W',
                  (derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                    max uR uA uM + 1} A).tensor.obj (W, W')) ⟶
                (Opposite.op (F.obj ((ModuleCat.restrictScalars.{max uR uA uM}
                      f).mapDerivedCategory.obj W')),
                  (derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                    max uR uA uM + 1} A).tensor.obj (W, W')))) ≫
      (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
          comparison).inv.app
        (Opposite.op ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj W'),
          (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj (W, W')))

/-- **The projection-formula map is the lax structure map with the unit whiskered in.**
Tensoring the unit of [stacks 0GMT] at `Y` into the second variable and following with
`Dualizing.restrictScalarsDerivedLaxTensor` at `(W, F Y)` gives
`Dualizing.restrictScalarsDerivedProjection` at `(W, Y)`. -/
theorem restrictScalarsDerivedProjection_eq
    (W : DerivedCategory (ModuleCat.{max uR uA uM} A))
    (Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    restrictScalarsDerivedProjection.{uR, uA, uM} f F comparison W Y =
      (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.map
          ((𝟙 ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj W),
              (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app Y) :
            (((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj W, Y) :
                DerivedCategory (ModuleCat.{max uR uA uM} R) ×
                  DerivedCategory (ModuleCat.{max uR uA uM} R)) ⟶
              ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj W,
                (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
                  (F.obj Y))) ≫
        restrictScalarsDerivedLaxTensor.{uR, uA, uM} f F comparison W (F.obj Y) := by
  have h := map_hom_map_comp_derivedHomRestrictScalarsNatIso_inv_app.{uR, uA, uM} f F comparison
    ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app Y)
    (𝟙 ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj
      (W, F.obj Y)))
  simp only [CategoryTheory.Functor.map_id, Functor.id_obj, Functor.comp_obj] at h
  have key : (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
        ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensorHomUnit
            W (F.obj Y) ≫
          (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).hom.map
            ((((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).counit.app
                    (F.obj Y)).op,
                𝟙 ((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                  max uR uA uM + 1} A).tensor.obj (W, F.obj Y))) :
              (Opposite.op (F.obj Y),
                  (derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                    max uR uA uM + 1} A).tensor.obj (W, F.obj Y)) ⟶
                (Opposite.op (F.obj ((ModuleCat.restrictScalars.{max uR uA uM}
                      f).mapDerivedCategory.obj (F.obj Y))),
                  (derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                    max uR uA uM + 1} A).tensor.obj (W, F.obj Y)))) ≫
        (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
          ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).hom.map
            (((F.map ((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
                    Y)).op,
                𝟙 ((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                  max uR uA uM + 1} A).tensor.obj (W, F.obj Y))))) =
      (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
        ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensorHomUnit
          W (F.obj Y)) := by
    rw [← Functor.map_comp, Category.assoc, ← Functor.map_comp]
    simp [prod_comp, ← op_comp]
  unfold restrictScalarsDerivedProjection restrictScalarsDerivedLaxTensor
  refine Eq.trans ?_ ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
    max uR uA uM + 1} R).homEquiv_dinaturality _ _)
  congr 1
  rw [← key]
  exact ((Category.assoc _ _ _).trans (congrArg _ h)).trans (Category.assoc _ _ _).symm

/-- **Base change is characterized by monoidality of the unit of [stacks 0GMT].**

A morphism `g : F X ⊗ᴸ_A F Y ⟶ F (X ⊗ᴸ_R Y)` is the lax monoidal structure map
`Dualizing.derivedTensorBaseChange` of derived base change **if and only if**

`(η_X ⊗ᴸ η_Y) ≫ lax_{F X, F Y} ≫ U g = η_{X ⊗ᴸ_R Y}`,

where `η` is the unit of [stacks 0GMT], `lax` is
`Dualizing.restrictScalarsDerivedLaxTensor` and `U` is derived restriction of scalars.  Both sides
are morphisms `X ⊗ᴸ_R Y ⟶ U (F (X ⊗ᴸ_R Y))`. -/
theorem eq_derivedTensorBaseChange_iff_unit_monoidal
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R))
    (g : (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj
        (F.obj X, F.obj Y) ⟶
      F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
        (X, Y))) :
    g = derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y ↔
      (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.map
            (((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X,
                (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app Y) :
              ((X, Y) : DerivedCategory (ModuleCat.{max uR uA uM} R) ×
                  DerivedCategory (ModuleCat.{max uR uA uM} R)) ⟶
                ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj (F.obj X),
                  (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
                    (F.obj Y))) ≫
          restrictScalarsDerivedLaxTensor.{uR, uA, uM} f F comparison (F.obj X) (F.obj Y) ≫
            (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map g =
        (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
          ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
            max uR uA uM + 1} R).tensor.obj (X, Y)) := by
  have hpair : (((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X,
            𝟙 Y) :
          ((X, Y) : DerivedCategory (ModuleCat.{max uR uA uM} R) ×
              DerivedCategory (ModuleCat.{max uR uA uM} R)) ⟶
            ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj (F.obj X), Y)) ≫
        ((𝟙 ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj (F.obj X)),
            (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app Y) :
          ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj (F.obj X), Y) ⟶
            ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj (F.obj X),
              (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj (F.obj Y))) =
      (((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X,
          (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app Y) :
        ((X, Y) : DerivedCategory (ModuleCat.{max uR uA uM} R) ×
            DerivedCategory (ModuleCat.{max uR uA uM} R)) ⟶
          ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj (F.obj X),
            (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj (F.obj Y))) :=
    CategoryTheory.Prod.hom_ext (Category.comp_id _) (Category.id_comp _)
  have hsplit : (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.map
        (((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X,
            (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app Y) :
          ((X, Y) : DerivedCategory (ModuleCat.{max uR uA uM} R) ×
              DerivedCategory (ModuleCat.{max uR uA uM} R)) ⟶
            ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj (F.obj X),
              (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj (F.obj Y))) =
      (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.map
          (((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X, 𝟙 Y) :
            ((X, Y) : DerivedCategory (ModuleCat.{max uR uA uM} R) ×
                DerivedCategory (ModuleCat.{max uR uA uM} R)) ⟶
              ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj (F.obj X),
                Y)) ≫
        (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.map
          ((𝟙 ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj (F.obj X)),
              (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app Y) :
            (((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj (F.obj X), Y) :
                DerivedCategory (ModuleCat.{max uR uA uM} R) ×
                  DerivedCategory (ModuleCat.{max uR uA uM} R)) ⟶
              ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj (F.obj X),
                (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
                  (F.obj Y))) :=
    (congrArg (derivedHomAdjunctionOverRing.{uR, max uR uA uM,
      max uR uA uM + 1} R).tensor.map hpair).symm.trans
      (CategoryTheory.Functor.map_comp _ _ _)
  have hmv : (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.map
            (((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X,
                (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app Y) :
              ((X, Y) : DerivedCategory (ModuleCat.{max uR uA uM} R) ×
                  DerivedCategory (ModuleCat.{max uR uA uM} R)) ⟶
                ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj (F.obj X),
                  (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
                    (F.obj Y))) ≫
          restrictScalarsDerivedLaxTensor.{uR, uA, uM} f F comparison (F.obj X) (F.obj Y) ≫
            (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map g =
      (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.map
            (((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X, 𝟙 Y) :
              ((X, Y) : DerivedCategory (ModuleCat.{max uR uA uM} R) ×
                  DerivedCategory (ModuleCat.{max uR uA uM} R)) ⟶
                ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj (F.obj X),
                  Y)) ≫
          restrictScalarsDerivedProjection.{uR, uA, uM} f F comparison (F.obj X) Y ≫
            (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map g := by
    refine Eq.trans (congrArg (fun z => z ≫
      restrictScalarsDerivedLaxTensor.{uR, uA, uM} f F comparison (F.obj X) (F.obj Y) ≫
        (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map g) hsplit) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine congrArg (fun z =>
      (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.map
          (((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X, 𝟙 Y) :
            ((X, Y) : DerivedCategory (ModuleCat.{max uR uA uM} R) ×
                DerivedCategory (ModuleCat.{max uR uA uM} R)) ⟶
              ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj (F.obj X),
                Y)) ≫ z) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact congrArg (fun z => z ≫
      (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map g)
      (restrictScalarsDerivedProjection_eq.{uR, uA, uM} f F comparison (F.obj X) Y).symm
  exact Iff.trans
    (eq_derivedTensorBaseChange_iff_unit_comp_restrictScalarsDerivedProjection.{uR, uA, uM}
      f F comparison X Y g) (Eq.congr hmv.symm rfl)

/-- The defining transpose of `Dualizing.restrictScalarsDerivedProjection`: restricted
coevaluation followed by the inverse of the change-of-rings isomorphism of [stacks 0E1W]. -/
theorem homEquiv_symm_restrictScalarsDerivedProjection
    (W : DerivedCategory (ModuleCat.{max uR uA uM} A))
    (Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv
          ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj W) Y
          ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
            ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj
              (W, F.obj Y)))).symm
        (restrictScalarsDerivedProjection.{uR, uA, uM} f F comparison W Y) =
      (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
          ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensorHomUnit
            W (F.obj Y)) ≫
        (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
            comparison).inv.app
          (Opposite.op Y,
            (derivedHomAdjunctionOverRing.{uA, max uR uA uM,
              max uR uA uM + 1} A).tensor.obj (W, F.obj Y)) :=
  ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv
    ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj W) Y
    ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
      ((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
        max uR uA uM + 1} A).tensor.obj (W, F.obj Y)))).symm_apply_apply _

/-- The defining transpose of `Dualizing.restrictScalarsDerivedLaxTensor`: restricted
coevaluation, pushed along the counit of [stacks 0GMT] into the contravariant slot, followed by
the inverse of the change-of-rings isomorphism of [stacks 0E1W]. -/
theorem homEquiv_symm_restrictScalarsDerivedLaxTensor
    (W W' : DerivedCategory (ModuleCat.{max uR uA uM} A)) :
    ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv
          ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj W)
          ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj W')
          ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
            ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj
              (W, W')))).symm
        (restrictScalarsDerivedLaxTensor.{uR, uA, uM} f F comparison W W') =
      (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
          ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensorHomUnit
              W W' ≫
            (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).hom.map
              ((((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).counit.app W').op,
                  𝟙 ((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                    max uR uA uM + 1} A).tensor.obj (W, W'))) :
                (Opposite.op W',
                    (derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                      max uR uA uM + 1} A).tensor.obj (W, W')) ⟶
                  (Opposite.op (F.obj ((ModuleCat.restrictScalars.{max uR uA uM}
                        f).mapDerivedCategory.obj W')),
                    (derivedHomAdjunctionOverRing.{uA, max uR uA uM,
                      max uR uA uM + 1} A).tensor.obj (W, W')))) ≫
        (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
            comparison).inv.app
          (Opposite.op ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj W'),
            (derivedHomAdjunctionOverRing.{uA, max uR uA uM,
              max uR uA uM + 1} A).tensor.obj (W, W')) :=
  ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).homEquiv
    ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj W)
    ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj W')
    ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
      ((derivedHomAdjunctionOverRing.{uA, max uR uA uM,
        max uR uA uM + 1} A).tensor.obj (W, W')))).symm_apply_apply _

/-- **The [stacks 068I] identification is the monoidality of the unit of [stacks 0GMT].**  The
candidate `Dualizing.tensorBaseChangeMor` supplied by [stacks 068I] agrees with the lax monoidal
structure map `Dualizing.derivedTensorBaseChange` of derived base change if and only if the unit
of [stacks 0GMT] is monoidal for it and for the lax structure of restriction of scalars. -/
theorem tensorBaseChangeMor_eq_iff_unit_monoidal
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{uR,
      max uR uA uM, uA, max uR uA uM + 1, max uR uA uM + 1} f)
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y =
        derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y ↔
      (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.map
            (((derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app X,
                (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app Y) :
              ((X, Y) : DerivedCategory (ModuleCat.{max uR uA uM} R) ×
                  DerivedCategory (ModuleCat.{max uR uA uM} R)) ⟶
                ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj (F.obj X),
                  (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
                    (F.obj Y))) ≫
          restrictScalarsDerivedLaxTensor.{uR, uA, uM} f F comparison (F.obj X) (F.obj Y) ≫
            (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
              (tensorBaseChangeMor.{uR, uA, uM} f F comparison D X Y) =
        (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app
          ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
            max uR uA uM + 1} R).tensor.obj (X, Y)) :=
  eq_derivedTensorBaseChange_iff_unit_monoidal.{uR, uA, uM} f F comparison X Y _

end Dualizing

end
