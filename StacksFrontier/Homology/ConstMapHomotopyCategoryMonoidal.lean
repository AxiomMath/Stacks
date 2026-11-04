module

public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import StacksFrontier.Homology.ConstMapHomologicalComplexKFlat
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatLocalization

/-!
# Constant diagrams are monoidal on homotopy categories, and the colimit is oplax monoidal there

Let `J` be a category and `D` a monoidal abelian category whose tensor product commutes with the
coproducts occurring in a total complex, so that `CochainComplex D ℤ` and
`CochainComplex (J ⥤ D) ℤ` both carry the total tensor product and both homotopy categories
carry the monoidal structure `CochainComplex.KFlatMonoidal.homotopyMonoidal` obtained by
localizing it at the homotopy equivalences.  This file descends the complex-level statements of
`StacksFrontier.Homology.ConstMapHomologicalComplexMonoidal` through that localization:

  `(Functor.const J).mapHomotopyCategory (ComplexShape.up ℤ) :
      K(D) ⥤ K(J ⥤ D)`

is monoidal, and its left adjoint `colim.mapHomotopyCategory (ComplexShape.up ℤ)` is oplax
monoidal.  The latter is the canonical comparison morphism
`colim (K₁ ⊗ K₂) ⟶ colim K₁ ⊗ colim K₂` in the homotopy category; no hypothesis making it
invertible is assumed, and none is claimed.

This is one localization closer to Stacks 08QC than the complex-level statement, and it is as
far as that chain can currently be pushed.  The remaining step is the K-flat localization
`CochainComplex.KFlatBifunctor.kFlatQ` through which
`CochainComplex.KFlatMonoidal.derivedMonoidal` builds the derived tensor product.  Of its two
inputs this file and
`StacksFrontier.Homology.ConstMapHomologicalComplexKFlat` supply one — `Functor.const J` carries
K-flat objects to K-flat objects, recorded here as
`CochainComplex.KFlatBifunctor.kFlatObjects_constMapHomotopyCategory` — and the other is
unavailable: `CochainComplex.KFlatMonoidal.derivedMonoidal` needs every complex of
`CochainComplex (J ⥤ D) ℤ` to admit a K-flat resolution, and no such existence statement holds
for a functor category in this repository.  See the implementation notes.

## Main definitions

* `CategoryTheory.Functor.constMapHomotopyCategoryMonoidal`: **constant diagrams form a monoidal
  functor on homotopy categories.**
* `CategoryTheory.Limits.colimMapHomotopyCategoryAdjunction`: the adjunction
  `colim.mapHomotopyCategory c ⊣ (Functor.const J).mapHomotopyCategory c`.
* `CategoryTheory.Limits.colimMapHomotopyCategoryOplaxMonoidal`: **the colimit functor is oplax
  monoidal on homotopy categories.**

## Main results

* `CochainComplex.KFlatBifunctor.kFlatObjects_constMapHomotopyCategory`: **constant diagrams
  carry K-flat objects of `K(D)` to K-flat objects of `K(J ⥤ D)`.**

## Implementation notes

The monoidal structure on `K(D)` is `CochainComplex.KFlatMonoidal.homotopyMonoidal`, which is by
definition the monoidal structure of `CategoryTheory.LocalizedMonoidal` on the type synonym
`CochainComplex.KFlatMonoidal.HomotopyLocalized`.  Because the two are the same term rather than
merely isomorphic structures, the descent needs no comparison between spellings: it is
`CategoryTheory.Localization.Monoidal.functorMonoidalOfComp` applied once, with the lifting
isomorphism supplied by Mathlib's `Functor.mapHomotopyCategoryFactors`, and the result is then
read at the plain `HomotopyCategory` spelling directly.  This is why the file is short, and it
is in contrast to
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionMonoidal`, where the target
monoidal structure is a *different*, strict one and the identity functor between the two
spellings has to be made monoidal in both directions.

Neither `homotopyMonoidal` nor the two monoidal functor structures below is declared an
instance, following `CochainComplex.KFlatMonoidal`: all are seated by `letI` where they are
used, so that no diamond is introduced for categories already carrying a monoidal structure.

The derived statement is blocked on exactly one input.  Running
`CategoryTheory.Localization.Monoidal.functorMonoidalOfComp` a second time, at
`CochainComplex.KFlatBifunctor.kFlatQ`, needs the monoidal structure of
`CochainComplex.KFlatMonoidal.derivedMonoidal` on `D(J ⥤ D)`, and that construction takes as a
hypothesis

  `∀ G : CochainComplex (J ⥤ D) ℤ, ∃ P f, KFlat (curriedTensor (J ⥤ D)) P ∧ QuasiIso f`.

No declaration in this repository proves that for a functor category.  Every K-flat resolution
theorem available is specialized either to `CochainComplex (ModuleCat R) ℤ`
(`CochainComplex.KFlat.exists_kFlat_resolution`, Tag 06Y4) or to complexes of sheaves of modules
on a ringed site (`Stacks.SheafOfModules.exists_kFlat_quasiIso`, Tag 06YS), and there is no
transport of K-flat-resolution existence along an equivalence of categories, so neither can be
moved to a diagram category.  Nothing about derived categories is therefore claimed here or in
`StacksFrontier.Homology.ConstMapHomologicalComplexKFlat`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory
open CochainComplex.KFlatMonoidal

universe v₁ u₁ v₂ u₂

namespace CategoryTheory

variable {J : Type u₁} [Category.{v₁} J] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCoproducts.{0} D] [HasColimitsOfSize.{0, 0} D] [HasInitial D]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [∀ X : D, PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorRight X)]

/-- `(Functor.const J).mapHomotopyCategory (ComplexShape.up ℤ)`, retyped between the type
synonyms on which the localized monoidal structures of the two homotopy categories live.  It is
the same functor; only the spelling of its source and target differs. -/
abbrev Functor.constMapHomotopyCategoryLocalized :
    HomotopyLocalized D ⥤ HomotopyLocalized (J ⥤ D) :=
  (Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategory (ComplexShape.up ℤ)

/-- The lifting of `(Functor.const J).mapHomotopyCategory c` along the homotopy localization: it
is Mathlib's `Functor.mapHomotopyCategoryFactors`, read at the type-synonym spelling of the
localized monoidal structure. -/
@[instance_reducible]
def Functor.constMapHomotopyCategoryLifting :
    Localization.Lifting
      (Localization.Monoidal.toMonoidalCategory (HomotopyCategory.quotient D (ComplexShape.up ℤ))
        (HomologicalComplex.homotopyEquivalences D (ComplexShape.up ℤ))
        (Iso.refl (homotopyUnit D)))
      (HomologicalComplex.homotopyEquivalences D (ComplexShape.up ℤ))
      ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        Localization.Monoidal.toMonoidalCategory
          (HomotopyCategory.quotient (J ⥤ D) (ComplexShape.up ℤ))
          (HomologicalComplex.homotopyEquivalences (J ⥤ D) (ComplexShape.up ℤ))
          (Iso.refl (homotopyUnit (J ⥤ D))))
      (Functor.constMapHomotopyCategoryLocalized (J := J) (D := D)) :=
  ⟨(Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategoryFactors (ComplexShape.up ℤ)⟩

/-- **Constant diagrams form a monoidal functor on homotopy categories**

`(Functor.const J).mapHomotopyCategory (ComplexShape.up ℤ) : K(D) ⥤ K(J ⥤ D)`

for the monoidal structure `CochainComplex.KFlatMonoidal.homotopyMonoidal` on each side.

This is `CategoryTheory.Localization.Monoidal.functorMonoidalOfComp` applied to the homotopy
localization: the functor lifts, by `Functor.mapHomotopyCategoryFactors`, to the composite of
the monoidal functor `CategoryTheory.Functor.constMapHomologicalComplexMonoidal` with the
monoidal localization functor. -/
@[instance_reducible]
def Functor.constMapHomotopyCategoryLocalizedMonoidal :
    (Functor.constMapHomotopyCategoryLocalized (J := J) (D := D)).Monoidal :=
  letI := Functor.constMapHomologicalComplexMonoidal (J := J) (D := D)
    (c := ComplexShape.up ℤ)
  letI := Functor.constMapHomotopyCategoryLifting (J := J) (D := D)
  Localization.Monoidal.functorMonoidalOfComp
    (Localization.Monoidal.toMonoidalCategory (HomotopyCategory.quotient D (ComplexShape.up ℤ))
      (HomologicalComplex.homotopyEquivalences D (ComplexShape.up ℤ))
      (Iso.refl (homotopyUnit D)))
    (HomologicalComplex.homotopyEquivalences D (ComplexShape.up ℤ))
    (Functor.constMapHomotopyCategoryLocalized (J := J) (D := D))
    ((Functor.const J : D ⥤ (J ⥤ D)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      Localization.Monoidal.toMonoidalCategory
        (HomotopyCategory.quotient (J ⥤ D) (ComplexShape.up ℤ))
        (HomologicalComplex.homotopyEquivalences (J ⥤ D) (ComplexShape.up ℤ))
        (Iso.refl (homotopyUnit (J ⥤ D))))

/-- `CategoryTheory.Functor.constMapHomotopyCategoryLocalizedMonoidal` read at the plain
`HomotopyCategory` spelling, with `CochainComplex.KFlatMonoidal.homotopyMonoidal` seated on each
side.  The two are the same term: `homotopyMonoidal` is by definition the monoidal structure
carried by `CochainComplex.KFlatMonoidal.HomotopyLocalized`. -/
@[instance_reducible]
def Functor.constMapHomotopyCategoryMonoidal :
    letI := homotopyMonoidal D
    letI := homotopyMonoidal (J ⥤ D)
    ((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategory (ComplexShape.up ℤ)).Monoidal :=
  Functor.constMapHomotopyCategoryLocalizedMonoidal

section Colim

variable [HasColimitsOfShape J D]

/-- The adjunction `colim.mapHomotopyCategory c ⊣ (Functor.const J).mapHomotopyCategory c`,
obtained from `CategoryTheory.Limits.colimConstAdj` by
`CategoryTheory.Adjunction.mapHomotopyCategoryAdjunction`. -/
def Limits.colimMapHomotopyCategoryAdjunction :
    (colim (J := J) (C := D)).mapHomotopyCategory (ComplexShape.up ℤ) ⊣
      (Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategory (ComplexShape.up ℤ) :=
  Adjunction.mapHomotopyCategoryAdjunction (colimConstAdj (J := J) (C := D)) (ComplexShape.up ℤ)

/-- **The colimit functor is oplax monoidal on homotopy categories**: there is a canonical
comparison morphism

`colim (K₁ ⊗ K₂) ⟶ colim K₁ ⊗ colim K₂`

in `K(D)`, natural and compatible with the associator and the unitors, for the monoidal
structure `CochainComplex.KFlatMonoidal.homotopyMonoidal` on each side.

It is the mate of the identity under
`CategoryTheory.Limits.colimMapHomotopyCategoryAdjunction`, whose right adjoint is monoidal by
`CategoryTheory.Functor.constMapHomotopyCategoryMonoidal`.  No hypothesis making the comparison
invertible is assumed, and the functor is not claimed to be strong monoidal. -/
@[instance_reducible]
def Limits.colimMapHomotopyCategoryOplaxMonoidal :
    letI := homotopyMonoidal D
    letI := homotopyMonoidal (J ⥤ D)
    (((colim (J := J) (C := D)).mapHomotopyCategory (ComplexShape.up ℤ))).OplaxMonoidal :=
  letI := homotopyMonoidal D
  letI := homotopyMonoidal (J ⥤ D)
  letI := Functor.constMapHomotopyCategoryMonoidal (J := J) (D := D)
  (Limits.colimMapHomotopyCategoryAdjunction (J := J) (D := D)).leftAdjointOplaxMonoidal

end Colim

end CategoryTheory

/-! ### K-flat objects of the homotopy category -/

namespace CochainComplex.KFlatBifunctor

variable {J : Type u₁} [Category.{v₁} J] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCoproducts.{0} D] [HasColimitsOfSize.{0, 0} D] [HasInitial D]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [∀ X : D, PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorRight X)]

omit [HasColimitsOfSize.{0, 0} D] in
/-- **Constant diagrams carry K-flat objects of `K(D)` to K-flat objects of `K(J ⥤ D)`.**
K-flatness of an object of a homotopy category is K-flatness of the underlying complex, and
`(Functor.const J).mapHomotopyCategory c` acts on underlying complexes as
`(Functor.const J).mapHomologicalComplex c`, so this is
`CochainComplex.KFlatBifunctor.kFlat_constMapHomologicalComplex`.

This is one of the two inputs needed to descend
`CategoryTheory.Functor.constMapHomotopyCategoryMonoidal` through the K-flat localization
`CochainComplex.KFlatBifunctor.kFlatQ`; the other, the existence of K-flat resolutions in
`CochainComplex (J ⥤ D) ℤ`, is not available. -/
theorem kFlatObjects_constMapHomotopyCategory (X : HomotopyCategory D (ComplexShape.up ℤ))
    (hX : kFlatObjects (curriedTensor D) X) :
    kFlatObjects (curriedTensor (J ⥤ D))
      (((Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategory (ComplexShape.up ℤ)).obj X) :=
  kFlat_constMapHomologicalComplex X.as hX

end CochainComplex.KFlatBifunctor

end
