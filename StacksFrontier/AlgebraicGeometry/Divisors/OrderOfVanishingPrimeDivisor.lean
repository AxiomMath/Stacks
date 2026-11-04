module

public import StacksFrontier.AlgebraicGeometry.Divisors.OrderOfVanishingInvertible
public import StacksFrontier.AlgebraicGeometry.Divisors.PrimeDivisor
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic

/-!
# The order of vanishing along a prime divisor

Let `X` be a locally Noetherian integral scheme, let `L` be an invertible sheaf of
`𝒪_X`-modules and let `Z` be a prime divisor of `X`, with generic point `ξ`. A global section `t`
of the constant generic-stalk module sheaf of `L` has a coordinate in the function field with
respect to some generator of `L_ξ`, and the order of that coordinate is the same integer for
every generator. Invertibility is `AlgebraicGeometry.SheafOfModules.IsInvertible`.

## Main definitions

* `AlgebraicGeometry.orderOfVanishingDataAtPrimeDivisor`: a choice of the quasi-coherence of `L`
  together with that integer and its characterization.
* `AlgebraicGeometry.orderOfVanishingAtPrimeDivisor`: the order of vanishing of `t` along `Z`.

## Main results

* `AlgebraicGeometry.nonempty_orderOfVanishingData_primeDivisor`: `t` has a coordinate with
  respect to some generator of `L` at the generic point of `Z`, and one integer is the order of
  that coordinate for every generator; packaged with the quasi-coherence of `L`.

## Implementation notes

The section of `L` whose order is measured enters as the global section `t` of
`AlgebraicGeometry.constantGenericStalkModuleSheaf` that Tag 01X5 part (2) attaches to a
meromorphic section of `L`, through `AlgebraicGeometry.meromorphicSectionSheafIsoConstant`.

## References

* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 0BE2](https://stacks.math.columbia.edu/tag/0BE2)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace AlgebraicGeometry

/-- Let `X` be a locally Noetherian integral scheme, `L` an invertible sheaf of `𝒪_X`-modules
and `Z` a prime divisor of `X`, with generic point `ξ`. Then `t` has a coordinate in the function
field with respect to some generator of `L_ξ`, and the order of that coordinate is one and the
same integer for every generator of `L_ξ`; packaged with the quasi-coherence of `L`. -/
theorem nonempty_orderOfVanishingData_primeDivisor
    (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (Z : PrimeDivisor X)
    (t : (constantGenericStalkModuleSheaf X L).val.obj (op ⊤)) :
    Nonempty { q : PSigma (fun _ : L.IsQuasicoherent => ℤ) //
      letI : L.IsQuasicoherent := q.1
      let ξ := Z.genericPoint
      let R := X.presheaf.stalk ξ
      let K := X.functionField
      letI : Module R (L.presheaf.stalk ξ) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) L.val ξ
      letI : Module K (L.presheaf.stalk (genericPoint X)) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) L.val (genericPoint X)
      let isCoordinate := fun (m : L.presheaf.stalk ξ) (a : K) =>
        t = constantGenericStalkModuleSection X L ⊤
          (a • (L.presheaf.stalkSpecializes
            ((genericPoint_spec X).specializes trivial)) m)
      (∃ m : L.presheaf.stalk ξ,
        (Submodule.span R {m} = ⊤) ∧ (∃ a : K, isCoordinate m a)) ∧
      (∀ (m : L.presheaf.stalk ξ)
        (_ : Submodule.span R {m} = ⊤) (a : K),
        isCoordinate m a → q.2 = X.ord a ξ) } := by
  have : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ L).2 ‹_›
  exact nonempty_orderOfVanishingData_of_isInvertible X L Z.genericPoint
    Z.codimension_closureSingleton_genericPoint t

/-- A choice of the data provided by
`AlgebraicGeometry.nonempty_orderOfVanishingData_primeDivisor`: the quasi-coherence of `L`, the
integer, and its characterization as the order of the coordinate of `t` with respect to any
generator of `L` at the generic point of `Z`. -/
def orderOfVanishingDataAtPrimeDivisor
    (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (Z : PrimeDivisor X)
    (t : (constantGenericStalkModuleSheaf X L).val.obj (op ⊤)) :
    { q : PSigma (fun _ : L.IsQuasicoherent => ℤ) //
      letI : L.IsQuasicoherent := q.1
      let ξ := Z.genericPoint
      let R := X.presheaf.stalk ξ
      let K := X.functionField
      letI : Module R (L.presheaf.stalk ξ) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) L.val ξ
      letI : Module K (L.presheaf.stalk (genericPoint X)) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) L.val (genericPoint X)
      let isCoordinate := fun (m : L.presheaf.stalk ξ) (a : K) =>
        t = constantGenericStalkModuleSection X L ⊤
          (a • (L.presheaf.stalkSpecializes
            ((genericPoint_spec X).specializes trivial)) m)
      (∃ m : L.presheaf.stalk ξ,
        (Submodule.span R {m} = ⊤) ∧ (∃ a : K, isCoordinate m a)) ∧
      (∀ (m : L.presheaf.stalk ξ)
        (_ : Submodule.span R {m} = ⊤) (a : K),
        isCoordinate m a → q.2 = X.ord a ξ) } :=
  Classical.choice (nonempty_orderOfVanishingData_primeDivisor X L Z t)

/-- The order of vanishing of `t` along `Z`: the integer component of
`AlgebraicGeometry.orderOfVanishingDataAtPrimeDivisor`, the order of the coordinate of `t` with
respect to any generator of `L` at the generic point of `Z`. -/
def orderOfVanishingAtPrimeDivisor
    (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (Z : PrimeDivisor X)
    (t : (constantGenericStalkModuleSheaf X L).val.obj (op ⊤)) : ℤ :=
  (orderOfVanishingDataAtPrimeDivisor X L Z t).val.2

end AlgebraicGeometry

end
