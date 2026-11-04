module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.IntegralSchemes
public import StacksFrontier.RingTheory.TranscendenceDegree.FractionRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The function field extension of a dominant morphism of integral schemes

A dominant morphism `f : X ⟶ Y` of integral schemes carries the generic point of `X` to the
generic point of `Y`, so its stalk map at the generic point is a map of function fields
`R(Y) → R(X)`. That extension of fields is the extension of fraction fields of the extension of
section rings `Γ(Y, U) → Γ(X, V)` over any pair of affine opens with `V ⊆ f⁻¹(U)`, and therefore
has the same transcendence degree. This is the identification by which the field-level
transcendence degree `trdeg_{R(Y)} R(X)` appearing in the dimension formula (Stacks 02JU) is
computed by the ring-level `trdeg_{Γ(Y,U)} Γ(X,V)` appearing in its algebra counterpart
(Stacks 02IJ).

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.functionFieldMap`: the map `R(Y) → R(X)`.

## Main results

* `AlgebraicGeometry.genericPoint_eq_of_isDominant`: a dominant morphism of integral schemes
  carries the generic point to the generic point.
* `AlgebraicGeometry.Scheme.Hom.functionFieldMap_germToFunctionField`: compatibility of
  `functionFieldMap` with the maps from section rings into the function fields.
* `AlgebraicGeometry.trdeg_functionField_eq_trdeg_appLE`: the function field extension has the
  same transcendence degree as the extension of section rings over a pair of affine opens.

## Implementation notes

That the generic point is preserved is the second of the equivalent conditions in
`AlgebraicGeometry.tfae_isDominant_of_isIntegral` (Stacks 0CC1), whose fourth condition
—injectivity of `appLE` on every pair of nonempty affine opens— is the `FaithfulSMul` hypothesis
of `Algebra.trdeg_eq_of_isFractionRing`.

`functionFieldMap` is the stalk map at the generic point of `X`, precomposed with the
comparison of the stalks of `Y` at `f (genericPoint X)` and at `genericPoint Y`. That comparison
is written as `TopCat.Presheaf.stalkSpecializes` rather than a cast along the equality of the two
points, because `TopCat.Presheaf.germ_stalkSpecializes` is then available to compute it.

## References

* [Stacks Project, Tag 0CC1](https://stacks.math.columbia.edu/tag/0CC1)
* [Stacks Project, Tag 02JU](https://stacks.math.columbia.edu/tag/02JU)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- A dominant morphism of integral schemes carries the generic point to the generic point. -/
lemma genericPoint_eq_of_isDominant (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    f (genericPoint X) = genericPoint Y :=
  (tfae_isDominant_of_isIntegral f).out 1 2 |>.mp ‹IsDominant f›

/-- The image of the generic point of `X` under a dominant morphism of integral schemes
specializes to the generic point of `Y` — indeed equals it. -/
lemma specializes_genericPoint_of_isDominant (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsDominant f] : f (genericPoint X) ⤳ genericPoint Y := by
  rw [genericPoint_eq_of_isDominant f]

/-- The map `R(Y) → R(X)` on function fields induced by a dominant morphism of integral
schemes. -/
@[ega "I 8.2.7", ega "II 6.3.9", ega "II 6.4.9" "partial"]
noncomputable def Scheme.Hom.functionFieldMap (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsDominant f] : Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes (specializes_genericPoint_of_isDominant f) ≫
    f.stalkMap (genericPoint X)

/-- `functionFieldMap` computes on germs at the generic point. -/
@[reassoc]
lemma Scheme.Hom.germ_functionFieldMap (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsDominant f] {U : Y.Opens} {V : X.Opens} (hVU : V ≤ f ⁻¹ᵁ U)
    (hU : genericPoint Y ∈ U) (hV : genericPoint X ∈ V) :
    Y.presheaf.germ U (genericPoint Y) hU ≫ f.functionFieldMap =
      f.appLE U V hVU ≫ X.presheaf.germ V (genericPoint X) hV := by
  rw [Scheme.Hom.functionFieldMap, ← Category.assoc, Y.presheaf.germ_stalkSpecializes,
    f.germ_stalkMap, Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res]

/-- `functionFieldMap` is compatible with the maps from section rings into the function
fields. -/
lemma Scheme.Hom.functionFieldMap_germToFunctionField (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsDominant f] {U : Y.Opens} {V : X.Opens} (hVU : V ≤ f ⁻¹ᵁ U) [Nonempty U] [Nonempty V]
    (a : Γ(Y, U)) :
    f.functionFieldMap (Y.germToFunctionField U a) =
      X.germToFunctionField V (f.appLE U V hVU a) :=
  congr($(f.germ_functionFieldMap hVU _ _) a)

/-- The function field extension of a dominant morphism of integral schemes has the same
transcendence degree as the extension of section rings over any pair of affine opens
`V ⊆ f⁻¹(U)`. -/
theorem trdeg_functionField_eq_trdeg_appLE (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsDominant f] {U : Y.Opens} {V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) [Nonempty U] [Nonempty V] :
    letI : Algebra Y.functionField X.functionField := f.functionFieldMap.hom.toAlgebra
    letI : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
    Algebra.trdeg Y.functionField X.functionField = Algebra.trdeg Γ(Y, U) Γ(X, V) := by
  let : Algebra Y.functionField X.functionField := f.functionFieldMap.hom.toAlgebra
  let : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
  let : Algebra Γ(Y, U) X.functionField :=
    (f.appLE U V hVU ≫ X.germToFunctionField V).hom.toAlgebra
  have : IsScalarTower Γ(Y, U) Γ(X, V) X.functionField := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, U) Y.functionField X.functionField :=
    .of_algebraMap_eq fun a => (f.functionFieldMap_germToFunctionField hVU a).symm
  have := functionField_isFractionRing_of_isAffineOpen Y U hU
  have := functionField_isFractionRing_of_isAffineOpen X V hV
  have := IsIntegral.component_integral (X := Y) U
  have := IsIntegral.component_integral (X := X) V
  have hinj := ((tfae_isDominant_of_isIntegral f).out 1 4).mp ‹IsDominant f›
  have : FaithfulSMul Γ(Y, U) Γ(X, V) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (hinj ⟨V, hV⟩ ⟨U, hU⟩ inferInstance inferInstance hVU)
  exact Algebra.trdeg_eq_of_isFractionRing

end AlgebraicGeometry

end
