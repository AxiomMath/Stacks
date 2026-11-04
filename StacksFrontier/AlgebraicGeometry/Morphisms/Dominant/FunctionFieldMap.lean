module

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.IntegralSchemes
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The extension of function fields induced by a dominant morphism of integral schemes

An integral scheme has a generic point, and its function field is the local ring there. A
dominant morphism `f : X ⟶ S` of integral schemes carries the generic point of `X` to the
generic point of `S` ([Stacks, Tag 0CC1]), so the stalk map of `f` at the generic point of `X`
is a map `R(S) → R(X)` once transported along that identification. That map is
`AlgebraicGeometry.dominantFunctionFieldMap`, the subject of [Stacks, Tag 02JU].

## Main definitions

* `AlgebraicGeometry.dominantFunctionFieldMap`: the map `R(S) → R(X)` on function fields
  induced by a dominant morphism of integral schemes.

## Main results

* `AlgebraicGeometry.appLE_germToFunctionField_commutes`: **the square comparing the map on
  sections with the map on function fields commutes.** For opens `V ≤ f ⁻¹ᵁ U` meeting the
  generic points, the germ at the generic point of the restriction of a function along `f` is
  the image under `dominantFunctionFieldMap f` of its germ at the generic point of the target.

## Implementation notes

The definition transports a stalk map along an equality of its base point, so every statement
about it has to move a `▸` past a germ; that is the content of the private
`stalkMap_germ_transport`, which is proved by `cases` on the equality.

This file exists so that `appLE_germToFunctionField_commutes` is available outside
`StacksFrontier/AlgebraicGeometry/Morphisms/FiniteType/DimensionFormula.lean`, where it was first
proved as a private step of the dimension formula. The square is the only bridge between the
map on sections of a morphism and the map it induces on function fields, so anything that has
to compute a function-field map from a chart needs it: it is what
`StacksFrontier/AlgebraicGeometry/Curves/InseparableGenusChangeProjectionEmbedding.lean` uses to
read the coordinate projection of [Stacks, Tag 0CD1] on the sections of a chart.

## References

* [Stacks Project, Tag 02JU](https://stacks.math.columbia.edu/tag/02JU)
* [Stacks Project, Tag 0CC1](https://stacks.math.columbia.edu/tag/0CC1)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The extension of function fields induced by a dominant morphism of integral schemes: the
stalk map at the generic point of the source, transported along the identification of its image
with the generic point of the target. -/
@[ega "II 6.3.9", ega "II 6.4.9" "partial"]
noncomputable def dominantFunctionFieldMap {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIntegral X] [IsIntegral S] [IsDominant f] :
    S.functionField →+* X.functionField := by
  let hgen : f (genericPoint X) = genericPoint S :=
    ((tfae_isDominant_of_isIntegral f).out 1 2).mp (inferInstance : IsDominant f)
  exact (hgen ▸ f.stalkMap (genericPoint X)).hom

/-- Transporting a stalk map along an equality of its base point commutes with taking germs. -/
private theorem stalkMap_germ_transport
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (U : S.Opens)
    {z : S} (h : f x = z) (hz : z ∈ U) (a : Γ(S, U)) :
    (h ▸ f.stalkMap x) (S.presheaf.germ U z hz a) =
      f.stalkMap x (S.presheaf.germ U (f x) (h.symm ▸ hz) a) := by
  cases h
  rfl

/-- **For a dominant morphism of integral schemes, the square relating the map on sections over
`V ≤ f ⁻¹ U` to the map on function fields commutes.** -/
theorem appLE_germToFunctionField_commutes
    {X S : Scheme.{u}} (f : X ⟶ S) [IsIntegral X] [IsIntegral S] [IsDominant f]
    (x : X) (U : S.Opens) [Nonempty U] (hx : f x ∈ U)
    (V : X.Opens) [Nonempty V] (hy : x ∈ V)
    (hVU : V ≤ f ⁻¹ᵁ U) :
    RingHom.comp (X.germToFunctionField V).hom (f.appLE U V hVU).hom =
      RingHom.comp (dominantFunctionFieldMap f) (S.germToFunctionField U).hom := by
  have hηS : f (genericPoint X) = genericPoint S :=
    ((tfae_isDominant_of_isIntegral f).out 1 2).mp (inferInstance : IsDominant f)
  have hηV : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.2).mpr (by simpa using ⟨x, hy⟩)
  have hηU : genericPoint S ∈ U :=
    ((genericPoint_spec S).mem_open_set_iff U.2).mpr (by simpa using ⟨f x, hx⟩)
  ext a
  dsimp [Scheme.germToFunctionField, dominantFunctionFieldMap]
  simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply, X.presheaf.germ_res_apply]
  rw [← Scheme.Hom.germ_stalkMap_apply (f := f) U (genericPoint X) (hηS.symm ▸ hηU)]
  exact (stalkMap_germ_transport f (genericPoint X) U hηS hηU a).symm

/-- **The map on function fields, read on a section over an open containing the generic point.**
The germ at the generic point of the pullback of a function along a dominant morphism is the
image of its germ under `dominantFunctionFieldMap`. -/
theorem dominantFunctionFieldMap_germToFunctionField_of_mem
    {X S : Scheme.{u}} (f : X ⟶ S) [IsIntegral X] [IsIntegral S] [IsDominant f]
    (x : X) (U : S.Opens) [Nonempty U] (hx : f x ∈ U)
    (V : X.Opens) [Nonempty V] (hy : x ∈ V)
    (hVU : V ≤ f ⁻¹ᵁ U) (s : Γ(S, U)) :
    dominantFunctionFieldMap f ((S.germToFunctionField U).hom s) =
      (X.germToFunctionField V).hom ((f.appLE U V hVU).hom s) :=
  (RingHom.congr_fun (appLE_germToFunctionField_commutes f x U hx V hy hVU) s).symm

end AlgebraicGeometry

end
