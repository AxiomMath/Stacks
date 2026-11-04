module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryEquivalence

/-!
# Ext groups are carried along by an equivalence

An equivalence of abelian categories `F : 𝒜 ⥤ ℬ` identifies the extension groups of `𝒜` with
those of `ℬ`: it acts degreewise on cochain complexes, hence on derived categories, and that
action is again an equivalence, so it is bijective on the Hom groups which *are* the Ext groups.

The construction is in three layers, each stated at the weakest hypotheses it needs.

1. For a category with a shift by `ℤ`, an equivalence commuting with the shift identifies the
   groups `ShiftedHom X Y n = (X ⟶ Y⟦n⟧)`. No abelian structure and no derived category appear
   here: this is the whole of what "an equivalence of categories" gives, and it applies verbatim
   to `DerivedCategory.Ext`, which is an abbreviation for `ShiftedHom`.
2. For an equivalence of abelian categories, the induced functor on the derived categories is an
   equivalence commuting with the shift, so layer 1 applies to it and identifies
   `Ext^n` of objects of the derived category.
3. For objects of the abelian categories themselves, placed in degree zero, the comparison
   `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` moves the degreewise action past the
   degree-zero inclusion, which turns layer 2 into `Ext^n_𝒜(A, B) = Ext^n_ℬ(F A, F B)`.

## Main definitions

* `CategoryTheory.ShiftedHom.mapAddEquiv`: layer 1, the identification
  `(X ⟶ Y⟦n⟧) = (F X ⟶ (F Y)⟦n⟧)` given by an equivalence `F` commuting with the shift.
* `CategoryTheory.ShiftedHom.congrAddEquiv`: the same groups along isomorphisms of the two
  arguments.
* `CategoryTheory.DerivedCategory.Ext.mapAddEquiv`: layer 2,
  `Ext^n(K, K') = Ext^n(F K, F K')` in the derived categories.
* `CategoryTheory.Abelian.zExt.mapAddEquiv`: layer 3,
  `Ext^n_𝒜(A, B) = Ext^n_ℬ(F A, F B)` for objects placed in degree zero.
* `CategoryTheory.Abelian.zExt.congrAddEquiv`: the degree-zero Ext groups along isomorphisms of
  the two arguments.

## Main results

* `CategoryTheory.Functor.additive_of_isEquivalence`: an equivalence between preadditive
  categories with binary products is additive. This removes the additivity hypothesis from the
  statements above at every call site where the functor is known to be an equivalence, which is
  the only case they are about.

## Implementation notes

**Why additivity is proved rather than assumed.** `CategoryTheory.Functor.mapDerivedCategory`
is defined only for an additive exact functor, so `[F.Additive]` has to be *available* for the
statements of layers 2 and 3 to elaborate at all, and it therefore stays in their binder lists.
It is not an extra assumption on the caller: an equivalence is full, hence preserves zero
morphisms, and preserves binary products, hence preserves binary biproducts, hence is additive —
which is `Functor.additive_of_isEquivalence`. Exactness is likewise automatic, an equivalence
preserving all limits and colimits.

**The additive structure is the only structure transported.** Layer 1 is built from
`CategoryTheory.Functor.FullyFaithful.homEquiv` and the functor's chosen commutation with the
shift, so it is `AddEquiv` and not `LinearEquiv`: the `R`-linear version for a functor which is
`R`-linear is `Dualizing.equivalenceShiftedHomLinearEquiv` in
`StacksFrontier/RingTheory/Dualizing/Complexes/InvertibleImage.lean`, and nothing here supersedes
it. The two are the same map when both apply.

**Two models of the derived category.** The statements carry a free `[HasDerivedCategory 𝒜]`
instance binder rather than fixing `HasDerivedCategory.standard`, so a caller which has already
chosen a model uses these at that model with no bridge. The two categories may use different
models; the universes are independent.

Which model a caller has is decided by instance *priority*, not by which attribute line a file
carries, and the two candidates in this library are not symmetric. For `X.Modules` on a scheme,
plain instance search resolves `HasDerivedCategory X.Modules` to the *locally small* global
instance `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, and an unprioritised file-level
`attribute [local instance] HasDerivedCategory.standard` does not displace it — only
`attribute [local instance 10000] HasDerivedCategory.standard` does. (This can be checked both ways, by
`inferInstance` being `rfl`-equal to each of the two in turn; the same observation is recorded in
the module documentation of
`StacksFrontier/AlgebraicGeometry/Cohomology/QuasicoherentAmplitude.lean`.) The free binder is what
makes the choice irrelevant here.

## References

* [Stacks Project, Tag 06XQ](https://stacks.math.columbia.edu/tag/06XQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

/-! ### Additivity of an equivalence -/

/-- **An equivalence between preadditive categories with binary products is additive.** It is
full, so it preserves zero morphisms, and it preserves binary products, so it preserves binary
biproducts; a functor preserving binary biproducts is additive. -/
theorem Functor.additive_of_isEquivalence {A : Type*} [Category* A] {B : Type*} [Category* B]
    [Preadditive A] [Preadditive B] [HasBinaryProducts A] (F : A ⥤ B) [F.IsEquivalence] :
    F.Additive :=
  let : PreservesLimitsOfShape (Discrete WalkingPair) F :=
    (Adjunction.isEquivalencePreservesLimits.{0, 0} F).preservesLimitsOfShape
  F.additive_of_preserves_binary_products

/-! ### Shifted Hom groups along an equivalence -/

namespace ShiftedHom

/-- **An equivalence commuting with the shift identifies the shifted Hom groups**:
`(X ⟶ Y⟦n⟧) = (F X ⟶ (F Y)⟦n⟧)`. The map is `CategoryTheory.ShiftedHom.map`, the functor
followed by its chosen commutation with the shift; it is bijective because `F` is fully faithful
and the commutation is an isomorphism, and additive because `F` is.

For `X`, `Y` in a derived category this is the identification of `Ext^n` groups induced by an
equivalence, `CategoryTheory.DerivedCategory.Ext.mapAddEquiv`. -/
def mapAddEquiv {A : Type*} [Category* A] {B : Type*} [Category* B]
    [Preadditive A] [Preadditive B] [HasShift A ℤ] [HasShift B ℤ]
    (F : A ⥤ B) [F.IsEquivalence] [F.CommShift ℤ] [F.Additive] (X Y : A) (n : ℤ) :
    ShiftedHom X Y n ≃+ ShiftedHom (F.obj X) (F.obj Y) n where
  toEquiv := (Functor.FullyFaithful.ofFullyFaithful F).homEquiv.trans
    ((F.commShiftIso n).app Y).homToEquiv
  map_add' x y := by
    simp [Functor.FullyFaithful.homEquiv_apply, Functor.map_add, Iso.homToEquiv]

/-- The identification `mapAddEquiv F X Y n` sends a shifted morphism `x` to `x.map F`. -/
@[simp]
theorem mapAddEquiv_apply {A : Type*} [Category* A] {B : Type*} [Category* B]
    [Preadditive A] [Preadditive B] [HasShift A ℤ] [HasShift B ℤ]
    (F : A ⥤ B) [F.IsEquivalence] [F.CommShift ℤ] [F.Additive] (X Y : A) (n : ℤ)
    (x : ShiftedHom X Y n) :
    mapAddEquiv F X Y n x = x.map F := rfl

/-- **Isomorphisms of the two arguments identify the shifted Hom groups.** -/
def congrAddEquiv {A : Type*} [Category* A] [Preadditive A] [HasShift A ℤ]
    {X X' Y Y' : A} (i : X ≅ X') (j : Y ≅ Y') (n : ℤ) :
    ShiftedHom X Y n ≃+ ShiftedHom X' Y' n where
  toEquiv := Iso.homCongr i ((shiftFunctor A n).mapIso j)
  map_add' x y := by simp [Iso.homCongr]

end ShiftedHom

/-! ### Ext groups along an equivalence of abelian categories -/

namespace DerivedCategory.Ext

/-- **An equivalence of abelian categories identifies the `Ext` groups of their derived
categories**: `Ext^n(K, K') = Ext^n(F K, F K')`, where `F` acts on the derived categories
degreewise through `CategoryTheory.Functor.mapDerivedCategory`.

The degreewise action is an equivalence
(`Stacks.Injectives.mapDerivedCategory_isEquivalence`) and commutes with the shift, so this is
`CategoryTheory.ShiftedHom.mapAddEquiv` applied to it. The hypothesis `[F.Additive]` is needed
only for `F.mapDerivedCategory` to be defined, and follows from `[F.IsEquivalence]` by
`CategoryTheory.Functor.additive_of_isEquivalence`. -/
def mapAddEquiv {A : Type*} [Category* A] {B : Type*} [Category* B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [F.IsEquivalence] (K K' : DerivedCategory A) (n : ℤ) :
    DerivedCategory.Ext K K' n ≃+
      DerivedCategory.Ext (F.mapDerivedCategory.obj K) (F.mapDerivedCategory.obj K') n :=
  letI := Stacks.Injectives.mapDerivedCategory_isEquivalence F
  ShiftedHom.mapAddEquiv F.mapDerivedCategory K K' n

end DerivedCategory.Ext

namespace Abelian.zExt

/-- **Isomorphisms of the two arguments identify the `Ext` groups of objects placed in degree
zero.** -/
def congrAddEquiv {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {X X' Y Y' : A} (i : X ≅ X') (j : Y ≅ Y') (n : ℤ) :
    Abelian.zExt X Y n ≃+ Abelian.zExt X' Y' n :=
  ShiftedHom.congrAddEquiv ((DerivedCategory.singleFunctor A 0).mapIso i)
    ((DerivedCategory.singleFunctor A 0).mapIso j) n

/-- **An equivalence of abelian categories identifies their `Ext` groups**:
`Ext^n_𝒜(X, Y) = Ext^n_ℬ(F X, F Y)`, for `X` and `Y` objects of `𝒜` placed in degree zero.

This is `CategoryTheory.DerivedCategory.Ext.mapAddEquiv` at the degree-zero objects, composed
with the comparison `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` which identifies the
degreewise action of `F` on the complex concentrated in degree zero with the complex
concentrated in degree zero of the image. -/
def mapAddEquiv {A : Type*} [Category* A] {B : Type*} [Category* B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [F.IsEquivalence] (X Y : A) (n : ℤ) :
    Abelian.zExt X Y n ≃+ Abelian.zExt (F.obj X) (F.obj Y) n :=
  (DerivedCategory.Ext.mapAddEquiv F _ _ n).trans
    (ShiftedHom.congrAddEquiv ((F.mapDerivedCategorySingleFunctor 0).app X)
      ((F.mapDerivedCategorySingleFunctor 0).app Y) n)

end Abelian.zExt

end CategoryTheory

end
