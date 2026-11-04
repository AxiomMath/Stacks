module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.SpecTotalFractionRing

/-!
# The total ring of fractions of an affine integral scheme and its function field

For `T` an integral affine scheme with a point `t`, the total ring of fractions
`Q(Γ(T, 𝒪_T))` maps to the function field `R(T)`: the germ at `t` carries nonzerodivisors of
`Γ(T, 𝒪_T)` to nonzerodivisors of `𝒪_{T, t}`, and `R(T)` is the total ring of fractions of
`𝒪_{T, t}`, so the nonzerodivisors of `Γ(T, 𝒪_T)` become invertible in `R(T)`.

Also recorded here: the coheight of a point of an open subscheme is its coheight in the ambient
scheme, which is the statement that codimension is computed in any open neighbourhood.

## Main definitions

* `AlgebraicGeometry.Scheme.totalFractionRingToFunctionField` is the map
  `Q(Γ(T, 𝒪_T)) → R(T)`.

## Main results

* `AlgebraicGeometry.Scheme.totalFractionRingToFunctionField_algebraMap`: on a global section
  the map is the germ followed by the structure map of `R(T)`.
* `AlgebraicGeometry.Scheme.coheight_opens`: the coheight of a point of an open subscheme is
  its coheight in the ambient scheme.

## References

* [Stacks Project, Tag 01RV](https://stacks.math.columbia.edu/tag/01RV)
* [Stacks Project, Tag 02RJ](https://stacks.math.columbia.edu/tag/02RJ)
-/

@[expose] public section

open CategoryTheory Order
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry

/-- The coheight of a point of an open subscheme is its coheight in the ambient scheme. -/
theorem Scheme.coheight_opens {T : Scheme.{u}} (W : T.Opens) (w : W.toScheme) :
    coheight (W.ι.base w) = coheight w :=
  Topology.IsOpenEmbedding.coheight_eq (x := w) W.ι.base W.ι.isOpenEmbedding

/-- The map from the total ring of fractions of the global sections of an integral affine scheme
to its function field: the germ at a point carries nonzerodivisors of the global sections to
nonzerodivisors of the local ring there, which become invertible in the function field. -/
noncomputable def Scheme.totalFractionRingToFunctionField (T : Scheme.{u}) [IsAffine T]
    [AlgebraicGeometry.IsIntegral T] (t : T) :
    FractionRing Γ(T, ⊤) →+* ↥T.functionField :=
  IsLocalization.lift (M := (Γ(T, ⊤))⁰)
    (g := (algebraMap ↥(T.presheaf.stalk t) ↥T.functionField).comp
      (T.presheaf.germ ⊤ t trivial).hom)
    (fun y => IsLocalization.map_units (M := (↥(T.presheaf.stalk t))⁰) ↥T.functionField
      ⟨(T.presheaf.germ ⊤ t trivial) (y : Γ(T, ⊤)),
        T.nonZeroDivisors_le_comap_germ_top t y.2⟩)

/-- On the image of a global section `a`, `Scheme.totalFractionRingToFunctionField` is the germ
of `a` at `t` followed by the algebra map from the stalk at `t` to the function field. -/
@[simp]
theorem Scheme.totalFractionRingToFunctionField_algebraMap (T : Scheme.{u}) [IsAffine T]
    [AlgebraicGeometry.IsIntegral T] (t : T) (a : Γ(T, ⊤)) :
    T.totalFractionRingToFunctionField t
        (algebraMap Γ(T, ⊤) (FractionRing Γ(T, ⊤)) a) =
      algebraMap ↥(T.presheaf.stalk t) ↥T.functionField
        ((T.presheaf.germ ⊤ t trivial) a) :=
  IsLocalization.lift_eq _ a

end AlgebraicGeometry

end
