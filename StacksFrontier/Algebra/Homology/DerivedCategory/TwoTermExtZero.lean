module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.CategoryTheory.Preadditive.CompAddCompAssoc
public import StacksFrontier.Homology.DoubleExtend
public import StacksFrontier.Homology.DoubleHomology

/-!
# `Ext` out of a complex concentrated in the two degrees `-1` and `0`

Let `𝒜` be an abelian category with a derived category and let `f : X₀ ⟶ X₁` be a morphism of
`𝒜`.  Mathlib's `HomologicalComplex.double f h` is the cochain complex with `X₀` in degree `-1`,
`X₁` in degree `0`, `f` as its only differential and zero elsewhere.  Such a complex lives in
cohomological degrees `≤ 0`, so for every object `G` of `𝒜` the groups

`Ext^i_𝒜(double f, G) = Hom_{D(𝒜)}(double f, G[i])`

vanish for `i < 0` and are computed by `H⁰` for `i = 0`.  Since `H⁰(double f) = coker f`
(`HomologicalComplex.doubleHomologyIsoCokernel`) this gives an identification

`Ext⁰_𝒜(double f, G) ≃+ Hom_𝒜(coker f, G)`.

## Main definitions

* `StacksDraft.TwoTermExt.twoTermComplex`: the complex `double f`, in the cochain indexing of
  `ℤ` with the differential from degree `-1` to degree `0`.
* `StacksDraft.TwoTermExt.twoTermExt`: `Ext^i_𝒜(double f, G)`.
* `StacksDraft.TwoTermExt.homologyZeroTwoTermIso`: `H⁰` of `double f`, read in the derived
  category, is `coker f`.
* `StacksDraft.TwoTermExt.twoTermExtZeroHom`: the map
  `Ext⁰_𝒜(double f, G) →+ Hom_𝒜(coker f, G)` given by taking `H⁰`, and
  `StacksDraft.TwoTermExt.twoTermExtZeroAddEquiv`: the same map, as an isomorphism of additive
  groups.
* `StacksDraft.TwoTermExt.precompAddEquiv`: precomposition with an isomorphism, as an
  isomorphism of the two additive groups of morphisms into a fixed object.

## Main results

* `StacksDraft.TwoTermExt.isStrictlyLE_twoTermComplex`: `double f` lives in cohomological
  degrees `≤ 0`.
* `StacksDraft.TwoTermExt.twoTermExtZeroHom_bijective`: taking `H⁰` is bijective on
  `Ext⁰_𝒜(double f, G)`.
* `StacksDraft.TwoTermExt.twoTermExt_eq_zero_of_neg`: `Ext^i_𝒜(double f, G) = 0` for `i < 0`.

## Implementation notes

`Ext` is `CategoryTheory.DerivedCategory.Ext`, i.e. `ShiftedHom` in the derived category, as in
`StacksFrontier/Algebra/Homology/DerivedCategory/Ext/Basic.lean`; the coefficient object `G` enters
as `(DerivedCategory.singleFunctor _ 0).obj G`, the complex concentrated in degree `0`.  The
model of the derived category is left as a hypothesis rather than fixed, so that a consumer may
use its own.

`Ext⁰` is computed from `H⁰` by
`DerivedCategory.bijective_homologyFunctor_shiftMap_of_isLE_of_isGE` (**Stacks 06XS**) with
`a = b = n = a' = 0`; the same lemma with `n < 0` gives the vanishing in negative degrees,
because then the target `Hom_𝒜(H⁰(double f), H^n(G[0]))` is a group with one element.  The
additive structure is handled as in
`StacksFrontier/Cotangent/SheavesOfRings/RingedSpaceExt.lean`, which does the same thing for the
cotangent complex of a morphism of ringed spaces: the map on `H⁰` is packaged as an
`AddMonoidHom` by `AddMonoidHom.mk'`, its bijectivity is proved separately, and the two are
combined by `AddEquiv.ofBijective`.

Nothing here carries a `stacks` attribute: these are general facts about a complex
concentrated in two adjacent degrees, and no tag of the source states them.  They are an
*input* to the deformation theory of [Stacks, Tag 08U8], whose acting group
`Hom(H⁰(NL(α)), 𝒢)` the source also writes as `Ext⁰(NL(α), 𝒢)`; the naive cotangent complex
`NL(α)` of a polynomial presentation is a `HomologicalComplex.double` by construction, and that
instance is set up in
`StacksFrontier/Deformation/RingedSpaceThickening/NaiveCotangentTwoTermOfDouble.lean`.

## References

* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS), `Ext` between complexes
  with disjoint homology ranges
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u t

namespace StacksDraft.TwoTermExt

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ### Precomposition as an isomorphism of additive groups -/

/-- Precomposition with an isomorphism `e : P ≅ Q`, as an isomorphism of additive groups
`(Q ⟶ G) ≃+ (P ⟶ G)`. -/
@[simps] def precompAddEquiv {P Q : C} (e : P ≅ Q) (G : C) : (Q ⟶ G) ≃+ (P ⟶ G) where
  toFun g := e.hom ≫ g
  invFun g := e.inv ≫ g
  left_inv g := e.inv_hom_id_assoc g
  right_inv g := e.hom_inv_id_assoc g
  map_add' g h := Preadditive.comp_add _ _ _ e.hom g h

/-! ### The complex concentrated in degrees `-1` and `0` -/

variable {X₀ X₁ : C} (f : X₀ ⟶ X₁)

/-- The cochain complex with `X₀` in degree `-1`, `X₁` in degree `0` and `f` as its only
differential. -/
noncomputable abbrev twoTermComplex : CochainComplex C ℤ :=
  HomologicalComplex.double f ComplexShape.upIntRelNegOneZero

/-- A complex concentrated in degrees `-1` and `0` has no terms in positive degrees, so it is
strictly `≤ 0`. -/
instance isStrictlyLE_twoTermComplex : CochainComplex.IsStrictlyLE (twoTermComplex f) 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact HomologicalComplex.isZero_double_X f ComplexShape.upIntRelNegOneZero i
    (by omega) (by omega)

variable [HasDerivedCategory.{t} C]

/-- `double f` regarded as an object of the derived category of `𝒜`. -/
noncomputable abbrev twoTermDerived : DerivedCategory C :=
  DerivedCategory.Q.obj (twoTermComplex f)

/-- `double f` lives in cohomological degrees `≤ 0` as an object of the derived category. -/
instance isLE_twoTermDerived : (twoTermDerived.{v, u, t} f).IsLE 0 := inferInstance

variable (G : C)

/-- The extension group `Ext^i_𝒜(double f, G) = Hom_{D(𝒜)}(double f, G[i])` of a complex
concentrated in degrees `-1` and `0` by an object `G`. -/
noncomputable abbrev twoTermExt (i : ℤ) : Type _ :=
  DerivedCategory.Ext (twoTermDerived.{v, u, t} f)
    ((DerivedCategory.singleFunctor C 0).obj G) i

/-- `H⁰` of `double f`, read in the derived category, is the cokernel of `f`: the comparison of
the homology of the derived object with the homology of the complex, followed by
`HomologicalComplex.doubleHomologyIsoCokernel`. -/
noncomputable def homologyZeroTwoTermIso :
    (DerivedCategory.homologyFunctor C 0).obj (twoTermDerived.{v, u, t} f) ≅ cokernel f :=
  (DerivedCategory.homologyFunctorFactors C 0).app (twoTermComplex f) ≪≫
    HomologicalComplex.doubleHomologyIsoCokernel f ComplexShape.upIntRelNegOneZero (by omega)

/-- `H⁰` of `G[0]` is `G`. -/
noncomputable def singleHomologyZeroIso :
    (DerivedCategory.homologyFunctor C 0).obj ((DerivedCategory.singleFunctor C 0).obj G) ≅ G :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app G

/-- Taking `H⁰` sends a class in `Ext⁰_𝒜(double f, G)` to a map `coker f ⟶ G`, read through
`H⁰(double f) ≅ coker f` and `H⁰(G[0]) ≅ G`.  It is additive. -/
noncomputable def twoTermExtZeroHom :
    twoTermExt.{v, u, t} f G 0 →+ (cokernel f ⟶ G) :=
  AddMonoidHom.mk'
    (fun ξ => (homologyZeroTwoTermIso.{v, u, t} f).inv ≫
      ((DerivedCategory.homologyFunctor C 0).shiftMap ξ 0 0 (by omega)) ≫
      (singleHomologyZeroIso.{v, u, t} G).hom)
    fun a b => by
      have hadd : (DerivedCategory.homologyFunctor C 0).shiftMap (a + b) 0 0 (by omega) =
          (DerivedCategory.homologyFunctor C 0).shiftMap a 0 0 (by omega) +
          (DerivedCategory.homologyFunctor C 0).shiftMap b 0 0 (by omega) := by
        rw [Functor.shiftMap, Functor.map_add, Preadditive.add_comp]
        rfl
      rw [hadd]
      exact Preadditive.comp_add_comp_assoc _ _ _ _

/-- `twoTermExtZeroHom` is the map on `H⁰`, conjugated by `H⁰(double f) ≅ coker f` and
`H⁰(G[0]) ≅ G`. -/
theorem twoTermExtZeroHom_apply (ξ : twoTermExt.{v, u, t} f G 0) :
    twoTermExtZeroHom.{v, u, t} f G ξ =
      (homologyZeroTwoTermIso.{v, u, t} f).inv ≫
        (DerivedCategory.homologyFunctor C 0).shiftMap ξ 0 0 (by omega) ≫
        (singleHomologyZeroIso.{v, u, t} G).hom :=
  rfl

/-- `double f` lives in degrees `≤ 0` and `G[0]` in degrees `≥ 0`, so taking `H⁰` is bijective
on `Ext⁰`.  This is **Stacks 06XS** in the case at hand. -/
theorem twoTermExtZeroHom_bijective :
    Function.Bijective (twoTermExtZeroHom.{v, u, t} f G) :=
  (Iso.homCongr (homologyZeroTwoTermIso.{v, u, t} f)
      (singleHomologyZeroIso.{v, u, t} G)).bijective.comp
    (DerivedCategory.bijective_homologyFunctor_shiftMap_of_isLE_of_isGE
      (twoTermDerived.{v, u, t} f) ((DerivedCategory.singleFunctor C 0).obj G)
      0 0 0 0 (by omega) (by omega))

/-- Taking `H⁰` identifies `Ext⁰_𝒜(double f, G)` with `Hom_𝒜(coker f, G)` as additive groups:
an `Ext⁰`-class `double f ⟶ G[0]` is determined by, and determines, the map `coker f ⟶ G` it
induces on `H⁰`. -/
noncomputable def twoTermExtZeroAddEquiv :
    twoTermExt.{v, u, t} f G 0 ≃+ (cokernel f ⟶ G) :=
  AddEquiv.ofBijective _ (twoTermExtZeroHom_bijective.{v, u, t} f G)

/-- `twoTermExtZeroAddEquiv` sends `ξ` to `twoTermExtZeroHom f G ξ`. -/
@[simp] theorem twoTermExtZeroAddEquiv_apply (ξ : twoTermExt.{v, u, t} f G 0) :
    twoTermExtZeroAddEquiv.{v, u, t} f G ξ = twoTermExtZeroHom.{v, u, t} f G ξ :=
  rfl

/-- `Ext^i_𝒜(double f, G)` vanishes in negative degrees: `double f` lives in degrees `≤ 0` and
`G[0]` in degrees `≥ 0`, so taking `H⁰` is a bijection onto
`Hom_𝒜(H⁰(double f), H^i(G[0]))`, whose target is a zero object. -/
theorem twoTermExt_eq_zero_of_neg {i : ℤ} (hi : i < 0) (ξ : twoTermExt.{v, u, t} f G i) :
    ξ = 0 := by
  have hzero : IsZero ((DerivedCategory.homologyFunctor C i).obj
      ((DerivedCategory.singleFunctor C 0).obj G)) :=
    DerivedCategory.isZero_of_isGE _ 0 i hi
  refine (DerivedCategory.bijective_homologyFunctor_shiftMap_of_isLE_of_isGE
    (twoTermDerived.{v, u, t} f) ((DerivedCategory.singleFunctor C 0).obj G)
    0 0 i i (by omega) (by omega)).1 ?_
  exact hzero.eq_of_tgt _ _

end StacksDraft.TwoTermExt

end
