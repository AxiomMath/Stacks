module

public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpaceExt
public import StacksFrontier.Deformation.SquareZero.ExtBaseChange

/-!
# `Ext` out of the truncation `τ_{≥ -1} L_{X/S}`

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces and `𝒢` an `𝒪_X`-module.  The
cotangent complex `L_{X/S}` of **Stacks 08UU** lives in cohomological degrees `≤ 0`, and
`Ext^i_{𝒪_X}(L_{X/S}, 𝒢) = Hom_{D(𝒪_X)}(L_{X/S}, 𝒢[0]⟦i⟧)` with `𝒢[0]⟦i⟧` in degrees `≥ -i`.
Hence for `i ≤ 1` the coefficient object lies in degrees `≥ -1`, and precomposition with the
truncation projection `L_{X/S} ⟶ τ_{≥ -1}L_{X/S}` is bijective on `Ext^i`.

This is the transport that the proof of **Stacks 08UZ** performs in its clauses (1) and (2): it
reads `Ext^2` and `Ext^1` out of `NL_{X/S}` as `Ext^2` and `Ext^1` out of `L_{X/S}` along the
identification `NL_{X/S} = τ_{≥ -1}L_{X/S}` of **Stacks 08UW**.  Only the truncation half of
that transport is here; it does not mention the naive cotangent complex and does not depend on
Stacks 08UW.  **Nothing below claims any part of Stacks 08UZ.**

## Main definitions

* `Stacks.Sheaves.RingedSpaceCotangent.truncCotangentComplexDerived`: the truncation
  `τ_{≥ -1}L_{X/S}` in `D(𝒪_X)`.
* `Stacks.Sheaves.RingedSpaceCotangent.truncCotangentExt`:
  `Ext^i_{𝒪_X}(τ_{≥ -1}L_{X/S}, 𝒢)`.
* `Stacks.Sheaves.RingedSpaceCotangent.extTruncGECotangentAddEquiv`: for `i ≤ 1`, the additive
  isomorphism `Ext^i_{𝒪_X}(τ_{≥ -1}L_{X/S}, 𝒢) ≃+ Ext^i_{𝒪_X}(L_{X/S}, 𝒢)` given by
  precomposition with the truncation projection.

## Main results

* `Stacks.Sheaves.RingedSpaceCotangent.isGE_singleShift`: `𝒢[0]⟦i⟧` lies in cohomological
  degrees `≥ -1` for `i ≤ 1`.
* `Stacks.Sheaves.RingedSpaceCotangent.extTruncGECotangentAddEquiv_apply`: the isomorphism is
  precomposition with the truncation projection.
* `Stacks.Sheaves.RingedSpaceCotangent.bijective_comp_truncGEpi`: **restriction along
  `L_{X/S} ⟶ τ_{≥ -1}L_{X/S}` is bijective on `Ext^i` for every `i ≤ 1`.**

## Implementation notes

The content is `Stacks.Deformation.truncGEHomAddEquiv`, which for a t-structure identifies the
morphisms out of a truncation `τ_{≥ n}X` into an object lying in degrees `≥ n` with the
morphisms out of `X`; `DerivedCategory.Ext X Y i` is by definition `X ⟶ Y⟦i⟧`, so that lemma
applies to `Ext` directly at `n = -1`, `X = L_{X/S}` and `Y = 𝒢[0]⟦i⟧`.  The only thing to
supply is the instance placing `𝒢[0]⟦i⟧` in degrees `≥ -1`, which is
`CategoryTheory.Triangulated.TStructure.isGE_shift` followed by
`CategoryTheory.Triangulated.TStructure.isGE_of_ge`, and it is this step that needs `i ≤ 1`.

The model of the derived category is `HasDerivedCategory.standard` as a local instance, as in
`StacksFrontier/Cotangent/SheavesOfRings/RingedSpaceExt.lean`.

### Correction to the implementation notes of `RingedSpaceExt.lean`

The "Towards Tag 08UZ" section of
`StacksFrontier/Cotangent/SheavesOfRings/RingedSpaceExt.lean` said that the degree `1` transport
needs, besides Stacks 08UW itself, that restriction along `L_{X/S} ⟶ τ_{≥ -1}L_{X/S}` is
bijective on `Ext^i` for `i ≤ 1`, and that neither was in this library.  The second of those two
is `Stacks.Sheaves.RingedSpaceCotangent.bijective_comp_truncGEpi` below, and
`Stacks.Deformation.truncGEHomAddEquiv`, which supplies it, was already in the library.

## References

* [Stacks Project, Tag 08UU](https://stacks.math.columbia.edu/tag/08UU), `L_{X/S}`
* [Stacks Project, Tag 08UW](https://stacks.math.columbia.edu/tag/08UW),
  `NL_{X/S} = τ_{≥ -1}L_{X/S}`
* [Stacks Project, Tag 08UZ](https://stacks.math.columbia.edu/tag/08UZ), the deformation theory
  this feeds
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Sheaves.RingedSpaceCotangent

attribute [local instance] HasDerivedCategory.standard

variable {X S : RingedSpace.{u, u}} (f : X ⟶ S)
  (G : SheafOfModules.{u} (structureSheafRing X))

/-- The truncation `τ_{≥ -1}L_{X/S}` of the cotangent complex of a morphism of ringed spaces,
in the derived category of `𝒪_X`-modules. -/
noncomputable abbrev truncCotangentComplexDerived :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) :=
  (DerivedCategory.TStructure.t.truncGE (-1)).obj (cotangentComplexDerived.{u, u + 1} f)

/-- The extension group `Ext^i_{𝒪_X}(τ_{≥ -1}L_{X/S}, 𝒢)`. -/
noncomputable abbrev truncCotangentExt (i : ℤ) : Type _ :=
  DerivedCategory.Ext (truncCotangentComplexDerived f)
    ((DerivedCategory.singleFunctor _ 0).obj G) i

/-- The complex `𝒢[0]⟦i⟧`, which computes `Ext^i` out of any object, lies in cohomological
degrees `≥ -1` as soon as `i ≤ 1`. -/
theorem isGE_singleShift {i : ℤ} (hi : i ≤ 1) :
    DerivedCategory.TStructure.t.IsGE
      (((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj G)⟦i⟧)
      (-1) :=
  let := DerivedCategory.TStructure.t.isGE_shift
    ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj G)
    0 i (-i) (by omega)
  DerivedCategory.TStructure.t.isGE_of_ge _ (-1) (-i) (by omega)

/-- **Restriction along `L_{X/S} ⟶ τ_{≥ -1}L_{X/S}` identifies the two `Ext^i` in degrees
`i ≤ 1`.**  The coefficient object `𝒢[0]⟦i⟧` then lies in cohomological degrees `≥ -1`, so
morphisms out of the truncation into it are the morphisms out of `L_{X/S}`. -/
noncomputable def extTruncGECotangentAddEquiv {i : ℤ} (hi : i ≤ 1) :
    truncCotangentExt f G i ≃+ cotangentExt f G i :=
  letI := isGE_singleShift G hi
  Stacks.Deformation.truncGEHomAddEquiv DerivedCategory.TStructure.t (-1)
    (cotangentComplexDerived.{u, u + 1} f)
    (((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj G)⟦i⟧)

/-- The identification is precomposition with the truncation projection
`L_{X/S} ⟶ τ_{≥ -1}L_{X/S}`. -/
theorem extTruncGECotangentAddEquiv_apply {i : ℤ} (hi : i ≤ 1) (ξ : truncCotangentExt f G i) :
    extTruncGECotangentAddEquiv f G hi ξ =
      (DerivedCategory.TStructure.t.truncGEπ (-1)).app
        (cotangentComplexDerived.{u, u + 1} f) ≫ ξ :=
  rfl

/-- **Restriction along `L_{X/S} ⟶ τ_{≥ -1}L_{X/S}` is bijective on `Ext^i` for `i ≤ 1`.**  This
is the transport that clauses (1) and (2) of Stacks 08UZ perform on `Ext^2` and `Ext^1`, read on
the truncation side only. -/
theorem bijective_comp_truncGEpi {i : ℤ} (hi : i ≤ 1) :
    Function.Bijective (fun ξ : truncCotangentExt f G i =>
      ((DerivedCategory.TStructure.t.truncGEπ (-1)).app
        (cotangentComplexDerived.{u, u + 1} f) ≫ ξ : cotangentExt f G i)) :=
  (extTruncGECotangentAddEquiv f G hi).bijective

end Stacks.Sheaves.RingedSpaceCotangent

end
