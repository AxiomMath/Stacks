module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.MappingConeTwoTermHomology
public import StacksFrontier.CategoryTheory.Preadditive.CompAddCompAssoc

/-!
# `Ext` out of an object of the derived category living in degrees `≤ 0`

Let `𝒜` be an abelian category with a derived category and let `Z` be an object of `D(𝒜)` with
`H^i(Z) = 0` for `i > 0`.  For every object `G` of `𝒜` the groups

`Ext^i_𝒜(Z, G) = Hom_{D(𝒜)}(Z, G[i])`

vanish for `i < 0` and are computed by `H⁰` for `i = 0`: taking `H⁰` is a bijection

`Ext⁰_𝒜(Z, G) ≃+ Hom_𝒜(H⁰(Z), G)`.

Both statements are **Stacks 06XS** for a pair of objects whose homology ranges are disjoint,
read at `Z` and at the object `G[0]` concentrated in degree `0`, which lives in degrees `≥ 0`.

## Main definitions

* `StacksDraft.ExtZero.derivedHomologyZeroIsoCokernel`: for a cochain complex vanishing in
  degree `1`, `H⁰` read in the derived category is the cokernel of the differential
  `X^{-1} ⟶ X⁰`.  This is `CochainComplex.homologyZeroIsoCokernel` read through
  `DerivedCategory.homologyFunctorFactors`.
* `StacksDraft.ExtZero.singleHomologyZeroIso`: `H⁰(G[0]) ≅ G`.
* `StacksDraft.ExtZero.extZeroHom`: the map `Ext⁰_𝒜(Z, G) →+ Hom_𝒜(W, G)` given by taking
  `H⁰`, read through a chosen identification `e : H⁰(Z) ≅ W`, and
  `StacksDraft.ExtZero.extZeroAddEquiv`: the same map, as an isomorphism of additive groups.

## Main results

* `StacksDraft.ExtZero.extZeroHom_bijective`: taking `H⁰` is bijective on `Ext⁰_𝒜(Z, G)`.
* `StacksDraft.ExtZero.extZeroHom_comp_left` and
  `StacksDraft.ExtZero.extZeroAddEquiv_comp_left`: the identification is natural in the source —
  precomposing an `Ext⁰`-class with a morphism `u : Z' ⟶ Z` precomposes the homomorphism it
  induces with any morphism of `𝒜` compatible with `H⁰(u)` under the two chosen identifications.
* `StacksDraft.ExtZero.ext_eq_zero_of_neg`: `Ext^i_𝒜(Z, G) = 0` for `i < 0`.

## Implementation notes

`Ext` is `CategoryTheory.DerivedCategory.Ext`, i.e. `ShiftedHom` in the derived category, as in
`StacksFrontier/Algebra/Homology/DerivedCategory/Ext/Basic.lean`; the coefficient object `G` enters
as `(DerivedCategory.singleFunctor _ 0).obj G`, the complex concentrated in degree `0`.  The
model of the derived category is left as a hypothesis rather than fixed.

The target of `extZeroHom` is `Hom_𝒜(W, G)` for an object `W` identified with `H⁰(Z)` rather
than `Hom_𝒜(H⁰(Z), G)` itself, so that the map is literally the conjugate
`e.inv ≫ H⁰(ξ) ≫ (H⁰(G[0]) ≅ G).hom` of the map on `H⁰`.

## References

* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS), `Ext` between complexes
  with disjoint homology ranges
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u t

namespace StacksDraft.ExtZero

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{t} C]

/-! ### `H⁰` of a complex vanishing in degree `1` -/

/-- **`H⁰` of a complex vanishing in degree `1`, read in the derived category, is the cokernel
of its differential into degree `0`.**  This is `CochainComplex.homologyZeroIsoCokernel`
composed with the comparison of the homology of the object of the derived category with the
homology of the complex. -/
noncomputable def derivedHomologyZeroIsoCokernel (M : CochainComplex C ℤ)
    (hM : IsZero (M.X 1)) :
    (DerivedCategory.homologyFunctor C 0).obj (DerivedCategory.Q.obj M) ≅
      cokernel (M.d (-1) 0) :=
  (DerivedCategory.homologyFunctorFactors C 0).app M ≪≫ M.homologyZeroIsoCokernel hM

/-! ### `Ext` out of an object living in degrees `≤ 0` -/

/-- `H⁰` of `G[0]` is `G`. -/
noncomputable def singleHomologyZeroIso (G : C) :
    (DerivedCategory.homologyFunctor C 0).obj ((DerivedCategory.singleFunctor C 0).obj G) ≅ G :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app G

variable (Z : DerivedCategory C) [Z.IsLE 0] {W : C}
  (e : (DerivedCategory.homologyFunctor C 0).obj Z ≅ W) (G : C)

/-- Taking `H⁰` sends a class in `Ext⁰_𝒜(Z, G)` to a map `W ⟶ G`, read through the chosen
identification `e : H⁰(Z) ≅ W` and through `H⁰(G[0]) ≅ G`.  It is additive. -/
noncomputable def extZeroHom :
    DerivedCategory.Ext Z ((DerivedCategory.singleFunctor C 0).obj G) 0 →+ (W ⟶ G) :=
  AddMonoidHom.mk'
    (fun ξ => e.inv ≫ ((DerivedCategory.homologyFunctor C 0).shiftMap ξ 0 0 (by omega)) ≫
      (singleHomologyZeroIso G).hom)
    fun a b => by
      have hadd : (DerivedCategory.homologyFunctor C 0).shiftMap (a + b) 0 0 (by omega) =
          (DerivedCategory.homologyFunctor C 0).shiftMap a 0 0 (by omega) +
          (DerivedCategory.homologyFunctor C 0).shiftMap b 0 0 (by omega) := by
        rw [Functor.shiftMap, Functor.map_add, Preadditive.add_comp]
        rfl
      rw [hadd]
      exact Preadditive.comp_add_comp_assoc _ _ _ _

omit [Z.IsLE 0] in
/-- `extZeroHom` is the map on `H⁰`, conjugated by `e : H⁰(Z) ≅ W` and `H⁰(G[0]) ≅ G`. -/
theorem extZeroHom_apply
    (ξ : DerivedCategory.Ext Z ((DerivedCategory.singleFunctor C 0).obj G) 0) :
    extZeroHom Z e G ξ =
      e.inv ≫ (DerivedCategory.homologyFunctor C 0).shiftMap ξ 0 0 (by omega) ≫
        (singleHomologyZeroIso G).hom :=
  rfl

/-- `Z` lives in degrees `≤ 0` and `G[0]` in degrees `≥ 0`, so taking `H⁰` is bijective on
`Ext⁰`.  This is **Stacks 06XS** in the case at hand. -/
theorem extZeroHom_bijective : Function.Bijective (extZeroHom Z e G) :=
  (Iso.homCongr e (singleHomologyZeroIso G)).bijective.comp
    (DerivedCategory.bijective_homologyFunctor_shiftMap_of_isLE_of_isGE
      Z ((DerivedCategory.singleFunctor C 0).obj G) 0 0 0 0 (by omega) (by omega))

/-- Taking `H⁰` identifies `Ext⁰_𝒜(Z, G)` with `Hom_𝒜(W, G)` as additive groups, through
`e : H⁰(Z) ≅ W`: an `Ext⁰`-class `Z ⟶ G[0]` out of an object living in degrees `≤ 0` is determined
by, and determines, the map it induces on `H⁰`. -/
noncomputable def extZeroAddEquiv :
    DerivedCategory.Ext Z ((DerivedCategory.singleFunctor C 0).obj G) 0 ≃+ (W ⟶ G) :=
  AddEquiv.ofBijective _ (extZeroHom_bijective Z e G)

/-- `extZeroAddEquiv` sends a class `ξ` to `extZeroHom Z e G ξ`. -/
@[simp] theorem extZeroAddEquiv_apply
    (ξ : DerivedCategory.Ext Z ((DerivedCategory.singleFunctor C 0).obj G) 0) :
    extZeroAddEquiv Z e G ξ = extZeroHom Z e G ξ :=
  rfl

omit [Z.IsLE 0] in
/-- **`extZeroHom` is natural in the source.**  Let `u : Z' ⟶ Z` be a morphism between two
objects living in degrees `≤ 0` and let `w : W' ⟶ W` be a morphism of `𝒜` compatible with `H⁰(u)`
under the two chosen identifications `e'` and `e` of the `H⁰`s.  Then precomposing an
`Ext⁰`-class with `u` precomposes the homomorphism it induces with `w`. -/
theorem extZeroHom_comp_left {Z' : DerivedCategory C} [Z'.IsLE 0] {W' : C}
    (e' : (DerivedCategory.homologyFunctor C 0).obj Z' ≅ W') (u : Z' ⟶ Z) (w : W' ⟶ W)
    (hw : (DerivedCategory.homologyFunctor C 0).map u ≫ e.hom = e'.hom ≫ w)
    (ξ : DerivedCategory.Ext Z ((DerivedCategory.singleFunctor C 0).obj G) 0) :
    extZeroHom Z' e' G (u ≫ ξ) = w ≫ extZeroHom Z e G ξ := by
  have hshift : (DerivedCategory.homologyFunctor C 0).shiftMap (u ≫ ξ) 0 0 (by omega) =
      (DerivedCategory.homologyFunctor C 0).map u ≫
        (DerivedCategory.homologyFunctor C 0).shiftMap ξ 0 0 (by omega) :=
    Functor.shiftMap_comp' _ u ξ 0 0 (by omega)
  have hinv : e'.inv ≫ (DerivedCategory.homologyFunctor C 0).map u = w ≫ e.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hw, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h1 : (DerivedCategory.homologyFunctor C 0).shiftMap (u ≫ ξ) 0 0 (by omega) ≫
        (singleHomologyZeroIso G).hom =
      (DerivedCategory.homologyFunctor C 0).map u ≫
        ((DerivedCategory.homologyFunctor C 0).shiftMap ξ 0 0 (by omega) ≫
          (singleHomologyZeroIso G).hom) :=
    (congrArg (fun k => k ≫ (singleHomologyZeroIso G).hom) hshift).trans
      (Category.assoc _ _ _)
  calc extZeroHom Z' e' G (u ≫ ξ)
      = e'.inv ≫ ((DerivedCategory.homologyFunctor C 0).shiftMap (u ≫ ξ) 0 0 (by omega) ≫
          (singleHomologyZeroIso G).hom) := extZeroHom_apply Z' e' G (u ≫ ξ)
    _ = e'.inv ≫ ((DerivedCategory.homologyFunctor C 0).map u ≫
          ((DerivedCategory.homologyFunctor C 0).shiftMap ξ 0 0 (by omega) ≫
            (singleHomologyZeroIso G).hom)) := congrArg (fun k => e'.inv ≫ k) h1
    _ = (e'.inv ≫ (DerivedCategory.homologyFunctor C 0).map u) ≫
          ((DerivedCategory.homologyFunctor C 0).shiftMap ξ 0 0 (by omega) ≫
            (singleHomologyZeroIso G).hom) := (Category.assoc _ _ _).symm
    _ = (w ≫ e.inv) ≫ ((DerivedCategory.homologyFunctor C 0).shiftMap ξ 0 0 (by omega) ≫
          (singleHomologyZeroIso G).hom) :=
      congrArg (fun k => k ≫ ((DerivedCategory.homologyFunctor C 0).shiftMap ξ 0 0 (by omega) ≫
        (singleHomologyZeroIso G).hom)) hinv
    _ = w ≫ extZeroHom Z e G ξ := Category.assoc _ _ _

/-- `extZeroHom_comp_left` for the additive isomorphism. -/
theorem extZeroAddEquiv_comp_left {Z' : DerivedCategory C} [Z'.IsLE 0] {W' : C}
    (e' : (DerivedCategory.homologyFunctor C 0).obj Z' ≅ W') (u : Z' ⟶ Z) (w : W' ⟶ W)
    (hw : (DerivedCategory.homologyFunctor C 0).map u ≫ e.hom = e'.hom ≫ w)
    (ξ : DerivedCategory.Ext Z ((DerivedCategory.singleFunctor C 0).obj G) 0) :
    extZeroAddEquiv Z' e' G (u ≫ ξ) = w ≫ extZeroAddEquiv Z e G ξ :=
  extZeroHom_comp_left Z e G e' u w hw ξ

/-- `Ext^i_𝒜(Z, G)` vanishes in negative degrees. -/
theorem ext_eq_zero_of_neg {i : ℤ} (hi : i < 0)
    (ξ : DerivedCategory.Ext Z ((DerivedCategory.singleFunctor C 0).obj G) i) : ξ = 0 := by
  have hzero : IsZero ((DerivedCategory.homologyFunctor C i).obj
      ((DerivedCategory.singleFunctor C 0).obj G)) :=
    DerivedCategory.isZero_of_isGE _ 0 i hi
  refine (DerivedCategory.bijective_homologyFunctor_shiftMap_of_isLE_of_isGE
    Z ((DerivedCategory.singleFunctor C 0).obj G) 0 0 i i (by omega) (by omega)).1 ?_
  exact hzero.eq_of_tgt _ _

end StacksDraft.ExtZero

end
