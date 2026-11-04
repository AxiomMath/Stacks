module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGrc1H01
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStructureSheafPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsGeometric

/-!
# `Curves^{grc,1} ⊂ Curves^{h0,1}`, unconditionally

A family of curves `f : X → S` whose geometric fibres are reduced, connected and of dimension
`1` has `f_*𝒪_X = 𝒪_S`, and this holds after arbitrary base change. This is the inclusion
`Curves^{grc,1} ⊂ Curves^{h0,1}` on the level of the defining properties of the two substacks.

## Main results

* `AlgebraicGeometry.Space.bijective_algebraMap_globalFunctions_of_isGeometricallyConnected`:
  for a proper, geometrically reduced and geometrically connected algebraic space `X` over a
  field `k`, the algebra map `k → H⁰(X, 𝒪_X)` is bijective.
* `AlgebraicGeometry.CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_isGrc1CurveFamily`:
  `f_*𝒪_X = 𝒪_S` universally for a family in `Curves^{grc,1}`.
* `AlgebraicGeometry.isGrc1CurveFamily_le_isH01CurveFamily`: the inclusion of the defining
  properties of `Curves^{grc,1}` and `Curves^{h0,1}`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- A proper algebraic space `X` over a field `k` which is geometrically reduced and
geometrically connected has `k = H⁰(X, 𝒪_X)`: the algebra map `k → H⁰(X, 𝒪_X)` is bijective. -/
theorem Space.bijective_algebraMap_globalFunctions_of_isGeometricallyConnected
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk)))) (hf : Space.IsProper B (Spec (.of k)) hk f)
    (hgr : Space.IsGeometricallyReduced k B hk X hX)
    (hconn : Space.IsGeometricallyConnected B k hk X) :
    Function.Bijective (algebraMap k (Space.globalFunctions B (Spec (.of k)) hk X)) :=
  Space.bijective_baseToGlobalFunctions_of_isGeometricallyConnected k B hk X hX f hf hgr hconn

/-- **`f_*𝒪_X = 𝒪_S` universally on `Curves^{grc,1}`.** For a family of curves `f : X → S` whose
geometric fibres are reduced, connected and of dimension `1`, pullback of global regular
functions along `X ×_S Y → Y` is bijective for every algebraic space `Y` over `S`. -/
theorem CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_isGrc1CurveFamily
    {X : CurveFamily B hZ} (hX : IsGrc1CurveFamily B hZ X) :
    HasUniversallyBijectiveGlobalFunctions B hZ X :=
  (isGrc1CurveFamily_le_isH01CurveFamily_of_structureSharp
    Space.bijective_algebraMap_globalFunctions_of_isGeometricallyConnected
    (Space.isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre B integerBase hZ)
    X hX).1

/-- **The inclusion `Curves^{grc,1} ⊂ Curves^{h0,1}` of defining properties.** A family of curves
whose geometric fibres are reduced, connected and of dimension `1` has `f_*𝒪_X = 𝒪_S`, this
holding after arbitrary base change, and fibres of dimension `1`. -/
theorem isGrc1CurveFamily_le_isH01CurveFamily : IsGrc1CurveFamily B hZ ≤ IsH01CurveFamily B hZ :=
  fun _ hX => ⟨CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_isGrc1CurveFamily hX, hX.2.2⟩

end AlgebraicGeometry

end
