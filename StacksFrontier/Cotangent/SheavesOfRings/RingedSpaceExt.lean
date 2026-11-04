module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.CategoryTheory.Preadditive.CompAddCompAssoc
public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpace

/-!
# `Ext` out of the cotangent complex of a morphism of ringed spaces

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces and `𝒢` an `𝒪_X`-module. The
cotangent complex `L_{X/S}` of **Stacks 08UU** is a complex of sheaves of `𝒪_X`-modules
concentrated in cohomological degrees `≤ 0`, so the groups

`Ext^i_{𝒪_X}(L_{X/S}, 𝒢) = Hom_{D(𝒪_X)}(L_{X/S}, 𝒢[i])`

vanish for `i < 0` and are computed by `H⁰` for `i = 0`. This file records that, together with
the resulting additive identification

`Ext⁰_{𝒪_X}(L_{X/S}, 𝒢) ≃+ Hom_{𝒪_X}(Ω_{X/S}, 𝒢)`

obtained from `H⁰(L_{X/S}) ≅ Ω_{X/S}` (**Stacks 08UV**).

This is the coefficient group in which the deformation theory of
`StacksFrontier/Deformation/RingedSpaceThickening/` is phrased on the full cotangent complex
rather than on the naive one; see "Towards Tag 08UZ" below for what is still missing there.

## Main definitions

* `Stacks.Sheaves.RingedSpaceCotangent.cotangentExt`: `Ext^i_{𝒪_X}(L_{X/S}, 𝒢)`.
* `Stacks.Sheaves.RingedSpaceCotangent.homologyZeroCotangentIso`: `H⁰` of `L_{X/S}` read in the
  derived category is `Ω_{X/S}`.
* `Stacks.Sheaves.RingedSpaceCotangent.extZeroCotangentHom`: the map
  `Ext⁰_{𝒪_X}(L_{X/S}, 𝒢) →+ Hom_{𝒪_X}(Ω_{X/S}, 𝒢)` given by taking `H⁰`.
* `Stacks.Sheaves.RingedSpaceCotangent.extZeroCotangentAddEquiv`: the same map, as an
  isomorphism of additive groups.

## Main results

* `Stacks.Sheaves.RingedSpaceCotangent.cotangentComplex_isStrictlyLE_zero` and
  `Stacks.Sheaves.RingedSpaceCotangent.cotangentComplexDerived_isLE_zero`: `L_{X/S}` lives in
  cohomological degrees `≤ 0`.
* `Stacks.Sheaves.RingedSpaceCotangent.extZeroCotangentHom_bijective`: taking `H⁰` is bijective
  on `Ext⁰_{𝒪_X}(L_{X/S}, 𝒢)`.
* `Stacks.Sheaves.RingedSpaceCotangent.cotangentExt_eq_zero_of_neg`:
  `Ext^i_{𝒪_X}(L_{X/S}, 𝒢) = 0` for `i < 0`.

## Towards Tag 08UZ

**Stacks 08UZ** describes the solutions of the deformation problem of **Stacks 08UY** by
`Ext^i_{𝒪_X}(L_{X/S}, 𝒢)` for `i = 2, 1, 0`, and its proof transports **Stacks 0GQ3**,
**Stacks 08UC** and **Stacks 08U8** from the naive cotangent complex `NL_{X/S}` to `L_{X/S}`
along the identification `NL_{X/S} = τ_{≥-1}L_{X/S}` of **Stacks 08UW**. In degree `0` that
transport is exactly `extZeroCotangentAddEquiv` below, since
`Ext⁰(NL_{X/S}, 𝒢) = Hom(Ω_{X/S}, 𝒢)` as well. In degree `1` it needs, besides
**Stacks 08UW** itself, that restriction along `L_{X/S} ⟶ τ_{≥-1}L_{X/S}` is bijective on
`Ext^i` for `i ≤ 1`. That second piece is
`Stacks.Sheaves.RingedSpaceCotangent.bijective_comp_truncGEpi` in
`StacksFrontier/Cotangent/SheavesOfRings/RingedSpaceExtTruncation.lean`, deduced from
`Stacks.Deformation.truncGEHomAddEquiv`; it is a statement about the t-structure alone and never
mentions the naive cotangent complex. Of **Stacks 08UW** itself the degree-zero clause is
`Stacks.Sheaves.RingedSpaceCotangent.isIso_homologyMap_naiveComparison_zero`, while the degree
`-1` clause has no formalization at any level of this library. **Nothing below claims any part
of Stacks 08UZ.** Clause (3) of that tag is proved in
`StacksFrontier/Deformation/RingedSpaceThickening/SolutionAutomorphisms.lean`, which consumes
`extZeroCotangentAddEquiv` for exactly the degree `0` transport described here.

## Implementation notes

`Ext` is `CategoryTheory.DerivedCategory.Ext`, i.e. `ShiftedHom` in the derived category, as in
`StacksFrontier/Algebra/Homology/DerivedCategory/Ext/Basic.lean`, and the model of the derived
category is `HasDerivedCategory.standard`, a local instance as in
`StacksFrontier/Deformation/RingedSpaceThickening/DerivedLiftingObstruction.lean`. The coefficient
module `𝒢` enters as `(DerivedCategory.singleFunctor _ 0).obj 𝒢`, the complex concentrated in
degree `0`.

`Ext⁰` is computed from `H⁰` by
`DerivedCategory.bijective_homologyFunctor_shiftMap_of_isLE_of_isGE` (**Stacks 06XS**) with
`a = b = n = a' = 0`; the same lemma with `n < 0` gives the vanishing in negative degrees,
because then the target `Hom_{𝒪_X}(H⁰(L_{X/S}), H^n(𝒢[0]))` is a group with one element.

The additive structure is handled as in
`StacksFrontier/Deformation/RingThickening/CotangentAutomorphisms.lean`, which does the same thing
for the cotangent complex of a ring map: the map on `H⁰` is packaged as an `AddMonoidHom` by
`AddMonoidHom.mk'`, its bijectivity is proved separately, and the two are combined by
`AddEquiv.ofBijective`. The additivity of `Functor.shiftMap` is unfolded here rather than
imported from that module, which is about rings and would be a strange dependency; it is one
`rw` through the definition of `Functor.shiftMap`.

The ring sheaf is written `structureSheafRing X` in full, as in
`StacksFrontier/Cotangent/SheavesOfRings/RingedSpace.lean`: inside this namespace the short name
is ambiguous.

## References

* [Stacks Project, Tag 08UU](https://stacks.math.columbia.edu/tag/08UU), `L_{X/S}`
* [Stacks Project, Tag 08UV](https://stacks.math.columbia.edu/tag/08UV),
  `H⁰(L_{X/S}) = Ω_{X/S}`
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS), `Ext` between
  complexes with disjoint homology ranges
* [Stacks Project, Tag 08UZ](https://stacks.math.columbia.edu/tag/08UZ), the deformation theory
  this feeds
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Sheaves.RingedSpaceDifferentials (moduleOfDifferentials)

universe u

namespace Stacks.Sheaves.RingedSpaceCotangent

attribute [local instance] HasDerivedCategory.standard

variable {X S : RingedSpace.{u, u}}

/-! ### `L_{X/S}` lives in cohomological degrees `≤ 0` -/

/-- The terms of the cotangent complex `L_{X/S}` of a morphism of ringed spaces vanish in
positive cohomological degrees, so `L_{X/S}` is strictly `≤ 0`. -/
instance cotangentComplex_isStrictlyLE_zero (f : X ⟶ S) :
    (cotangentComplex f).IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  exact fun i hi => cotangentComplex_isZero_pos f i hi

/-- `L_{X/S}`, as an object of the derived category of `𝒪_X`-modules, lives in cohomological
degrees `≤ 0`. -/
instance cotangentComplexDerived_isLE_zero (f : X ⟶ S) :
    (cotangentComplexDerived.{u, u + 1} f).IsLE 0 :=
  inferInstance

/-! ### `Ext` out of `L_{X/S}` -/

section Ext

variable (f : X ⟶ S) (G : SheafOfModules.{u} (structureSheafRing X))

/-- The extension group `Ext^i_{𝒪_X}(L_{X/S}, 𝒢) = Hom_{D(𝒪_X)}(L_{X/S}, 𝒢[i])` of the
cotangent complex of a morphism of ringed spaces `f : X ⟶ S` (**Stacks 08UU**) by an
`𝒪_X`-module `𝒢`. -/
noncomputable abbrev cotangentExt (i : ℤ) : Type _ :=
  DerivedCategory.Ext (cotangentComplexDerived.{u, u + 1} f)
    ((DerivedCategory.singleFunctor _ 0).obj G) i

/-- `H⁰` of the cotangent complex `L_{X/S}` of a morphism of ringed spaces, read in the derived
category, is the sheaf of relative differentials `Ω_{X/S}`: the comparison of the homology of
the derived object with the homology of the complex, followed by the identification of
**Stacks 08UV**. -/
noncomputable def homologyZeroCotangentIso :
    (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing X)) 0).obj
        (cotangentComplexDerived.{u, u + 1} f) ≅
      moduleOfDifferentials f :=
  (DerivedCategory.homologyFunctorFactors
        (SheafOfModules.{u} (structureSheafRing X)) 0).app
      (cotangentComplex f) ≪≫
    cotangentComplex_homologyZeroIso f

/-- `H⁰` of `𝒢[0]` is `𝒢`. -/
noncomputable def singleHomologyZeroIso :
    (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing X)) 0).obj
        ((DerivedCategory.singleFunctor _ 0).obj G) ≅ G :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (SheafOfModules.{u} (structureSheafRing X)) 0).app G

/-- Taking `H⁰` sends a class in `Ext⁰_{𝒪_X}(L_{X/S}, 𝒢)` to a map `Ω_{X/S} ⟶ 𝒢`, read through
`H⁰(L_{X/S}) ≅ Ω_{X/S}` (**Stacks 08UV**) and `H⁰(𝒢[0]) ≅ 𝒢`. It is additive. -/
noncomputable def extZeroCotangentHom :
    cotangentExt f G 0 →+ (moduleOfDifferentials f ⟶ G) :=
  AddMonoidHom.mk'
    (fun ξ => (homologyZeroCotangentIso f).inv ≫
      ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (structureSheafRing X)) 0).shiftMap
          ξ 0 0 (by omega) :
        (DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (structureSheafRing X)) 0).obj
            (cotangentComplexDerived.{u, u + 1} f) ⟶
          (DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (structureSheafRing X)) 0).obj
            ((DerivedCategory.singleFunctor _ 0).obj G)) ≫
      (singleHomologyZeroIso G).hom)
    fun a b => by
      have hadd : (DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (structureSheafRing X)) 0).shiftMap
            (a + b) 0 0 (by omega) =
          (DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (structureSheafRing X)) 0).shiftMap
            a 0 0 (by omega) +
          (DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (structureSheafRing X)) 0).shiftMap
            b 0 0 (by omega) := by
        rw [Functor.shiftMap, Functor.map_add, Preadditive.add_comp]
        rfl
      rw [hadd]
      exact Preadditive.comp_add_comp_assoc _ _ _ _

/-- `extZeroCotangentHom` is the map on `H⁰`, conjugated by `H⁰(L_{X/S}) ≅ Ω_{X/S}` and
`H⁰(𝒢[0]) ≅ 𝒢`. -/
theorem extZeroCotangentHom_apply (ξ : cotangentExt f G 0) :
    extZeroCotangentHom f G ξ =
      (homologyZeroCotangentIso f).inv ≫
        (DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (structureSheafRing X)) 0).shiftMap
          ξ 0 0 (by omega) ≫
        (singleHomologyZeroIso G).hom :=
  rfl

/-- `L_{X/S}` lives in degrees `≤ 0` and `𝒢[0]` in degrees `≥ 0`, so taking `H⁰` is bijective
on `Ext⁰`. This is **Stacks 06XS** in the case at hand. -/
theorem extZeroCotangentHom_bijective : Function.Bijective (extZeroCotangentHom f G) :=
  (Iso.homCongr (homologyZeroCotangentIso f) (singleHomologyZeroIso G)).bijective.comp
    (DerivedCategory.bijective_homologyFunctor_shiftMap_of_isLE_of_isGE
      (cotangentComplexDerived.{u, u + 1} f) ((DerivedCategory.singleFunctor _ 0).obj G)
      0 0 0 0 (by omega) (by omega))

/-- Taking `H⁰` identifies `Ext⁰_{𝒪_X}(L_{X/S}, 𝒢)` with `Hom_{𝒪_X}(Ω_{X/S}, 𝒢)` as additive
groups: an `Ext⁰`-class `L_{X/S} ⟶ 𝒢[0]` is determined by, and determines, the map
`Ω_{X/S} ⟶ 𝒢` it induces on `H⁰`.

In the deformation theory of first order thickenings of ringed spaces this is the degree `0`
case of the identification `Ext^i(L_{X/S}, 𝒢) = Ext^i(NL_{X/S}, 𝒢)` by which **Stacks 08UZ**
transports **Stacks 08U8** and **Stacks 08UC**; see the module documentation. -/
noncomputable def extZeroCotangentAddEquiv :
    cotangentExt f G 0 ≃+ (moduleOfDifferentials f ⟶ G) :=
  AddEquiv.ofBijective (extZeroCotangentHom f G) (extZeroCotangentHom_bijective f G)

/-- `extZeroCotangentAddEquiv` sends an `Ext⁰`-class to the map it induces on `H⁰`. -/
@[simp]
theorem extZeroCotangentAddEquiv_apply (ξ : cotangentExt f G 0) :
    extZeroCotangentAddEquiv f G ξ = extZeroCotangentHom f G ξ :=
  rfl

/-- `Ext^i_{𝒪_X}(L_{X/S}, 𝒢)` vanishes in negative degrees: `L_{X/S}` lives in degrees `≤ 0`
and `𝒢[0]` in degrees `≥ 0`, so taking `H⁰` is a bijection onto
`Hom_{𝒪_X}(H⁰(L_{X/S}), H^i(𝒢[0]))`, whose target is a zero object. -/
theorem cotangentExt_eq_zero_of_neg {i : ℤ} (hi : i < 0) (ξ : cotangentExt f G i) : ξ = 0 := by
  have hzero : IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X)) i).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X)) 0).obj G)) :=
    DerivedCategory.isZero_of_isGE _ 0 i hi
  refine (DerivedCategory.bijective_homologyFunctor_shiftMap_of_isLE_of_isGE
    (cotangentComplexDerived.{u, u + 1} f)
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing X)) 0).obj G)
    0 0 i i (by omega) (by omega)).1 ?_
  exact hzero.eq_of_tgt _ _

end Ext

end Stacks.Sheaves.RingedSpaceCotangent

end
