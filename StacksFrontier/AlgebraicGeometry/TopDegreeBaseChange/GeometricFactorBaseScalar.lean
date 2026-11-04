module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsGeometricFactor

/-!
# A base scalar on the fixed factor of `N ↦ F ⊗ (f')^* Ñ`

Let `R` be a commutative ring, `W` an `R`-scheme with structure morphism `f'` and `F` a sheaf of
`𝒪_W`-modules. The geometric factor
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.geometricFactorFormula`, `N ↦ F ⊗_{𝒪_W} (f')^* Ñ`,
is `R`-linear in the variable factor `(f')^* Ñ`: it carries `r • 𝟙 N` to `r • 𝟙`.

This file proves the corresponding statement for the fixed factor: the transformation
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.tensorFactorMap` induced by `r • 𝟙 F` is again
multiplication by `r`. Both slots of the tensor product therefore carry the same base scalar.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.tensorFactorMap_smul_id_app`: tensoring
  `r • 𝟙 F` with the identity of the variable factor is tensoring the identity of `F` with
  `r • 𝟙`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.tensorFactorMap_smul_id_app_eq_smul_id`: a base
  scalar on the fixed factor of `F ⊗ -` is that scalar on the tensor product.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.geometricFactorFormulaMap_smul_id_app`: a base
  scalar on the fixed factor of the geometric factor is that scalar on its values.

## Implementation notes

The tensor product of sheaves of modules is the sheafification of the tensor product of the
underlying presheaves, and both sides of the first statement are the sheafification of a morphism
of presheaves of modules; these agree on pure tensors of local sections, where
`(r • x) ⊗ y = r • (x ⊗ y) = x ⊗ (r • y)`. The monoidal structure on presheaves of modules is a
local instance.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0GA8](https://stacks.math.columbia.edu/tag/0GA8)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

variable (R : Type u) [CommRing R] (W : Over (Spec (CommRingCat.of R)))

/-- A base scalar may be moved from the fixed factor of `F ⊗ -` to the variable one:
`(r • 𝟙 F) ⊗ 𝟙 M = 𝟙 F ⊗ (r • 𝟙 M)`. -/
theorem tensorFactorMap_smul_id_app (F : W.left.Modules) (r : R) (M : W.left.Modules) :
    letI := modulesLinear R W
    (tensorFactorMap R W (r • 𝟙 F)).app M = (tensorFactor R W F).map (r • 𝟙 M) := by
  let := modulesLinear R W
  let : MonoidalCategory (PresheafOfModules.{u} W.left.ringCatSheaf.obj) :=
    Stacks.SheafOfModules.monoidalCategoryPresheafOfModules W.left.presheaf
      (AlgebraicGeometry.ringSheafCond W.left)
  have h :
      (((PresheafOfModules.tensorBifunctor.{_, _, u, u, u} W.left.presheaf).map
            ((SheafOfModules.forget W.left.ringCatSheaf).map (r • 𝟙 F))).app
          ((SheafOfModules.forget W.left.ringCatSheaf).obj M)) =
        ((PresheafOfModules.tensorBifunctor.{_, _, u, u, u} W.left.presheaf).obj F.val).map
          ((SheafOfModules.forget W.left.ringCatSheaf).map (r • 𝟙 M)) := by
    refine PresheafOfModules.hom_ext fun U => ?_
    let : CommRing (W.left.ringCatSheaf.obj.obj U) :=
      inferInstanceAs (CommRing (W.left.presheaf.obj U))
    refine ModuleCat.MonoidalCategory.tensor_ext fun x y => ?_
    exact (Stacks.RingedSpace.map_smul_tmul LinearMap.id
        ((baseRingToSections R W U r : W.left.presheaf.obj U)) x y).trans
      (Stacks.RingedSpace.map_tmul_smul LinearMap.id
        ((baseRingToSections R W U r : W.left.presheaf.obj U)) x y).symm
  exact congrArg
    (Stacks.SheafOfModules.TensorSheafification.sheafify W.left.presheaf
      (AlgebraicGeometry.ringSheafCond W.left)).map h

/-- A base scalar on the fixed factor of `F ⊗ -` is that scalar on the tensor product:
`(r • 𝟙 F) ⊗ 𝟙 M = r • 𝟙 (F ⊗ M)`. -/
theorem tensorFactorMap_smul_id_app_eq_smul_id (F : W.left.Modules) (r : R)
    (M : W.left.Modules) :
    letI := modulesLinear R W
    (tensorFactorMap R W (r • 𝟙 F)).app M = r • 𝟙 ((tensorFactor R W F).obj M) :=
  let := modulesLinear R W
  (tensorFactorMap_smul_id_app R W F r M).trans
    ((Functor.linear_iff R (tensorFactor R W F)).1 (tensorLeft_linear R W F) M r)

/-- A base scalar on the fixed factor of the geometric factor `N ↦ F ⊗ (f')^* Ñ` is that scalar
on its values. -/
theorem geometricFactorFormulaMap_smul_id_app (F : W.left.Modules) (r : R)
    (N : ModuleCat.{u} R) :
    letI := modulesLinear R W
    (geometricFactorFormulaMap R W (r • 𝟙 F)).app N =
      r • 𝟙 ((geometricFactorFormula R W F).obj N) :=
  tensorFactorMap_smul_id_app_eq_smul_id R W F r _

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
