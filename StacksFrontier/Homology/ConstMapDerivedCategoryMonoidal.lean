module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.EvaluationToDerivedColimit
public import StacksFrontier.Homology.ConstMapHomotopyCategoryMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedMonoidalStructure

/-!
# Constant diagrams are monoidal on derived categories, and derived lower shriek is oplax monoidal

Let `J` be a category and `D` a monoidal abelian category whose tensor product commutes with the
coproducts occurring in a total complex, so that `CochainComplex D ℤ` and
`CochainComplex (J ⥤ D) ℤ` both carry the total tensor product.  Assume moreover that every
cochain complex over `D`, and every cochain complex over `J ⥤ D`, receives a quasi-isomorphism
from a K-flat one, so that `CochainComplex.KFlatMonoidal.derivedMonoidal` equips `D(D)` and
`D(J ⥤ D)` with the derived tensor product.  This file proves that

  `(Functor.const J).mapDerivedCategory : D(D) ⥤ D(J ⥤ D)`

is a **monoidal** functor for those two derived tensor products, and deduces that any left
adjoint of it is **oplax** monoidal.  Applied to the adjunction
`Stacks.CategoryHomology.totalDerivedColimitAdjunction`, whose right adjoint is exactly
`(Functor.const Cᵒᵖ).mapDerivedCategory`, this produces the canonical comparison morphism

  `Lπ_!(K₁ ⊗^L K₂) ⟶ Lπ_!(K₁) ⊗^L Lπ_!(K₂)`

for the derived lower shriek `Lπ_! = Stacks.CategoryHomology.totalDerivedColimit` of the
projection of a chaotic site to a point (Stacks 08PF).

That comparison is the first half of Stacks 08QC.  Only the first half: **it is not proved to be
an isomorphism, and nothing here assumes or uses the resolution hypothesis of Stacks 08Q9 under
which the source asserts that it is.**  See the implementation notes.

## Main definitions

* `CategoryTheory.Functor.constKFlatLift`: constant diagrams, restricted to the K-flat objects
  of the homotopy categories, with its monoidal structure
  `CategoryTheory.Functor.constKFlatLiftMonoidal`.
* `CategoryTheory.Functor.constMapDerivedCategoryMonoidal`: **constant diagrams form a monoidal
  functor on derived categories**, for the derived tensor product on each side.
* `CategoryTheory.Functor.oplaxMonoidal_of_adjunction_constMapDerivedCategory`: **a left adjoint
  of `(Functor.const J).mapDerivedCategory` is oplax monoidal.**
* `Stacks.CategoryHomology.totalDerivedColimitOplaxMonoidal`: **derived lower shriek on a chaotic
  site is oplax monoidal**, and
  `Stacks.CategoryHomology.totalDerivedColimitTensorComparison`, its comparison morphism
  `Lπ_!(K₁ ⊗^L K₂) ⟶ Lπ_!(K₁) ⊗^L Lπ_!(K₂)`.

## Main results

The file contains no result beyond the structures above; each of them is obtained by instantiating
a general construction, and the content is the instantiation.

## Implementation notes

The descent is one application of `CategoryTheory.Localization.Monoidal.functorMonoidalOfComp` at
the K-flat localization `CochainComplex.KFlatBifunctor.kFlatQ`, mirroring the application at the
homotopy localization in `StacksFrontier.Homology.ConstMapHomotopyCategoryMonoidal`.  Its two inputs
are the monoidal structure of `CategoryTheory.Functor.constMapHomotopyCategoryMonoidal`, cut down
to the K-flat objects by `CochainComplex.KFlatBifunctor.kFlatObjects_constMapHomotopyCategory` and
`CategoryTheory.ObjectProperty.liftMonoidal`, and the lifting isomorphism, which is Mathlib's
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` whiskered by the inclusion of the K-flat
objects.  Since `CochainComplex.KFlatMonoidal.derivedMonoidal` is by definition the monoidal
structure of `CategoryTheory.LocalizedMonoidal` on the type synonym
`CochainComplex.KFlatMonoidal.DerivedLocalized`, the result is then read at the plain
`DerivedCategory` spelling without any comparison between spellings.

Neither `derivedMonoidal` nor any of the monoidal functor structures below is declared an
instance, following `CochainComplex.KFlatMonoidal`: all are seated by `letI` where they are used,
so that no diamond is introduced for categories already carrying a monoidal structure.

**What is proved and what is not.**  What is proved is the existence of the canonical oplax
monoidal structure, hence of the comparison morphism, and nothing about it being invertible.  The
comparison is canonical in the precise sense that it is the mate of the lax monoidal structure of
the right adjoint under the adjunction: it is
`CategoryTheory.Adjunction.leftAdjointOplaxMonoidal` applied to
`Stacks.CategoryHomology.totalDerivedColimitAdjunction` and to
`CategoryTheory.Functor.constMapDerivedCategoryMonoidal`.  It is *not* an ad hoc morphism and it
is not an unspecified isomorphism.  Correspondingly, no `@[stacks 08QC]` attribute is attached
anywhere in this file: Stacks 08QC asserts that this comparison is an isomorphism, and that
assertion -- the whole mathematical content of the tag, which is where the cosimplicial resolution
of Stacks 08Q9 enters -- is untouched here.  The invertibility statement also needs no hypothesis
on a cosimplicial object for the comparison to exist, which is why the two halves are kept apart:
every hypothesis of this file is about K-flatness, and none is about a resolution of the site.

**The hypotheses carried.**  `hresD` and `hresJD` (and `hresE`, `hresCE` in the chaotic-site
section) assert the existence of K-flat resolutions; they are exactly the hypothesis of
`CochainComplex.KFlatMonoidal.derivedMonoidal`, without which neither derived category has a
tensor product and the statement cannot be written at all.  For complexes of modules over a ring
the first is `CochainComplex.KFlat.exists_kFlat_resolution` (Stacks 06Y4); for a functor category
no such statement exists in this repository -- every K-flat resolution theorem available is
specialized either to `CochainComplex (ModuleCat R) ℤ` or to complexes of sheaves of modules on a
ringed site (`Stacks.SheafOfModules.exists_kFlat_quasiIso`, Stacks 06YS), and there is no
transport of K-flat-resolution existence along an equivalence of categories.  So the
functor-category hypothesis is carried rather than discharged.

## References

* [Stacks Project, Tag 08QC](https://stacks.math.columbia.edu/tag/08QC)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory
open CochainComplex.KFlatMonoidal CochainComplex.KFlatBifunctor

universe w w' v₁ u₁ v₂ u₂

namespace CategoryTheory

attribute [local instance] homotopyMonoidal homotopyBraided

variable {J : Type u₁} [Category.{v₁} J] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCoproducts.{0} D] [HasColimitsOfSize.{0, 0} D] [HasInitial D]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [∀ X : D, PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorLeft X)]
  [∀ X : D, PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorRight X)]

/-! ### Constant diagrams on the K-flat objects of the homotopy categories -/

/-- `(Functor.const J).mapHomotopyCategory (ComplexShape.up ℤ)`, restricted to the K-flat objects
of the two homotopy categories.  The restriction is legitimate because a constant diagram at a
K-flat complex is K-flat, which is
`CochainComplex.KFlatBifunctor.kFlatObjects_constMapHomotopyCategory`. -/
def Functor.constKFlatLift :
    (kFlatObjects (curriedTensor D)).FullSubcategory ⥤
      (kFlatObjects (curriedTensor (J ⥤ D))).FullSubcategory :=
  (kFlatObjects (curriedTensor (J ⥤ D))).lift
    ((kFlatObjects (curriedTensor D)).ι ⋙
      (Functor.const J : D ⥤ (J ⥤ D)).mapHomotopyCategory (ComplexShape.up ℤ))
    (fun X => kFlatObjects_constMapHomotopyCategory X.obj X.property)

/-- **`Functor.constKFlatLift` is a monoidal functor** between the full monoidal subcategories of
K-flat objects.  The K-flat objects are a full monoidal subcategory on each side
(`CochainComplex.KFlatMonoidal.kFlatObjects_isMonoidal`), and a monoidal functor landing in a
full monoidal subcategory is monoidal into it, so this is
`CategoryTheory.ObjectProperty.liftMonoidal` applied to
`CategoryTheory.Functor.constMapHomotopyCategoryMonoidal`. -/
@[instance_reducible]
def Functor.constKFlatLiftMonoidal :
    letI := homotopyMonoidal D
    letI := homotopyMonoidal (J ⥤ D)
    (Functor.constKFlatLift (J := J) (D := D)).Monoidal :=
  letI := homotopyMonoidal D
  letI := homotopyMonoidal (J ⥤ D)
  letI := Functor.constMapHomotopyCategoryMonoidal (J := J) (D := D)
  ObjectProperty.liftMonoidal _ _ _

/-! ### The descent to the derived categories -/

section Derived

variable [BraidedCategory (CochainComplex D ℤ)] [BraidedCategory (CochainComplex (J ⥤ D) ℤ)]
  [HasDerivedCategory.{w} D] [HasDerivedCategory.{w'} (J ⥤ D)]
  (hresD : ∀ G : CochainComplex D ℤ, ∃ (P : CochainComplex D ℤ) (f : P ⟶ G),
    KFlat (curriedTensor D) P ∧ QuasiIso f)
  (hresJD : ∀ G : CochainComplex (J ⥤ D) ℤ, ∃ (P : CochainComplex (J ⥤ D) ℤ) (f : P ⟶ G),
    KFlat (curriedTensor (J ⥤ D)) P ∧ QuasiIso f)

/-- `(Functor.const J).mapDerivedCategory`, retyped between the type synonyms on which the
localized monoidal structures of the two derived categories live.  It is the same functor; only
the spelling of its source and target differs. -/
abbrev Functor.constMapDerivedCategoryLocalized :
    DerivedLocalized D hresD ⥤ DerivedLocalized (J ⥤ D) hresJD :=
  (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory

/-- The lifting of `(Functor.const J).mapDerivedCategory` along the K-flat localization: it is
Mathlib's `CategoryTheory.Functor.mapDerivedCategoryFactorsh`, whiskered by the inclusion of the
K-flat objects of `K(D)` and read at the type-synonym spelling of the localized monoidal
structure. -/
@[instance_reducible]
def Functor.constMapDerivedCategoryLifting :
    letI := kFlatQ_isLocalization (curriedTensor D) hresD
    letI := kFlatQ_isLocalization (curriedTensor (J ⥤ D)) hresJD
    Localization.Lifting
      (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor D))
        (kFlatQuasiIso (curriedTensor D))
        (Iso.refl ((kFlatQ (curriedTensor D)).obj (𝟙_ _))))
      (kFlatQuasiIso (curriedTensor D))
      (Functor.constKFlatLift (J := J) (D := D) ⋙
        Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor (J ⥤ D)))
          (kFlatQuasiIso (curriedTensor (J ⥤ D)))
          (Iso.refl ((kFlatQ (curriedTensor (J ⥤ D))).obj (𝟙_ _))))
      (Functor.constMapDerivedCategoryLocalized hresD hresJD) :=
  ⟨isoWhiskerLeft (kFlatObjects (curriedTensor D)).ι
    ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategoryFactorsh)⟩

/-- **Constant diagrams form a monoidal functor on derived categories**, stated at the type
synonyms carrying the localized monoidal structures.  This is
`CategoryTheory.Localization.Monoidal.functorMonoidalOfComp` applied to the K-flat localization:
the functor lifts, by `CategoryTheory.Functor.constMapDerivedCategoryLifting`, to the composite of
the monoidal functor `CategoryTheory.Functor.constKFlatLiftMonoidal` with the monoidal
localization functor. -/
@[instance_reducible]
def Functor.constMapDerivedCategoryLocalizedMonoidal :
    (Functor.constMapDerivedCategoryLocalized hresD hresJD).Monoidal :=
  letI := kFlatQ_isLocalization (curriedTensor D) hresD
  letI := kFlatQ_isLocalization (curriedTensor (J ⥤ D)) hresJD
  letI := Functor.constKFlatLiftMonoidal (J := J) (D := D)
  letI := Functor.constMapDerivedCategoryLifting hresD hresJD
  Localization.Monoidal.functorMonoidalOfComp
    (Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor D))
      (kFlatQuasiIso (curriedTensor D))
      (Iso.refl ((kFlatQ (curriedTensor D)).obj (𝟙_ _))))
    (kFlatQuasiIso (curriedTensor D))
    (Functor.constMapDerivedCategoryLocalized hresD hresJD)
    (Functor.constKFlatLift (J := J) (D := D) ⋙
      Localization.Monoidal.toMonoidalCategory (kFlatQ (curriedTensor (J ⥤ D)))
        (kFlatQuasiIso (curriedTensor (J ⥤ D)))
        (Iso.refl ((kFlatQ (curriedTensor (J ⥤ D))).obj (𝟙_ _))))

/-- **Constant diagrams form a monoidal functor on derived categories**

`(Functor.const J).mapDerivedCategory : D(D) ⥤ D(J ⥤ D)`

for the derived tensor product `CochainComplex.KFlatMonoidal.derivedMonoidal` on each side.
This is `CategoryTheory.Functor.constMapDerivedCategoryLocalizedMonoidal` read at the plain
`DerivedCategory` spelling: the two are the same term, `derivedMonoidal` being by definition the
monoidal structure carried by `CochainComplex.KFlatMonoidal.DerivedLocalized`.

For the projection of a chaotic site to a point this is the statement that `π^{-1}` is strong
monoidal on derived categories. -/
@[instance_reducible]
def Functor.constMapDerivedCategoryMonoidal :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    ((Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory).Monoidal :=
  Functor.constMapDerivedCategoryLocalizedMonoidal hresD hresJD

/-- **A left adjoint of `(Functor.const J).mapDerivedCategory` is oplax monoidal**: there is a
canonical comparison morphism

`L (K₁ ⊗^L K₂) ⟶ L K₁ ⊗^L L K₂`

in `D(D)`, natural and compatible with the associator and the unitors, for the derived tensor
product on each side.

It is the mate of the identity under `adj`, whose right adjoint is monoidal by
`CategoryTheory.Functor.constMapDerivedCategoryMonoidal`, so it is
`CategoryTheory.Adjunction.leftAdjointOplaxMonoidal`.  No hypothesis making the comparison
invertible is assumed, and `L` is not claimed to be strong monoidal. -/
@[instance_reducible]
def Functor.oplaxMonoidal_of_adjunction_constMapDerivedCategory
    {L : DerivedCategory (J ⥤ D) ⥤ DerivedCategory D}
    (adj : L ⊣ (Functor.const J : D ⥤ (J ⥤ D)).mapDerivedCategory) :
    letI := derivedMonoidal D hresD
    letI := derivedMonoidal (J ⥤ D) hresJD
    L.OplaxMonoidal :=
  letI := derivedMonoidal D hresD
  letI := derivedMonoidal (J ⥤ D) hresJD
  letI := Functor.constMapDerivedCategoryMonoidal hresD hresJD
  adj.leftAdjointOplaxMonoidal

end Derived

end CategoryTheory

/-! ### Derived lower shriek on a chaotic site -/

namespace Stacks.CategoryHomology

attribute [local instance] HasDerivedCategory.standard

universe v u

variable (C : Type u) [SmallCategory C] (E : Type v) [Category.{v} E] [Abelian E]
  [MonoidalCategory E] [MonoidalPreadditive E]
  [HasCoproducts.{0} E] [HasColimitsOfSize.{0, 0} E] [HasInitial E]
  [∀ X : E, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : E, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [∀ X : E, PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorLeft X)]
  [∀ X : E, PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorRight X)]
  [BraidedCategory (CochainComplex E ℤ)] [BraidedCategory (CochainComplex (Cᵒᵖ ⥤ E) ℤ)]
  [EnoughProjectives (Cᵒᵖ ⥤ E)] [HasColimitsOfShape ℕ E] [HasExactColimitsOfShape ℕ E]
  [HasColimitsOfShape Cᵒᵖ E]
  (hresE : ∀ G : CochainComplex E ℤ, ∃ (P : CochainComplex E ℤ) (f : P ⟶ G),
    KFlat (curriedTensor E) P ∧ QuasiIso f)
  (hresCE : ∀ G : CochainComplex (Cᵒᵖ ⥤ E) ℤ, ∃ (P : CochainComplex (Cᵒᵖ ⥤ E) ℤ) (f : P ⟶ G),
    KFlat (curriedTensor (Cᵒᵖ ⥤ E)) P ∧ QuasiIso f)

/-- **Derived lower shriek on a chaotic site is oplax monoidal.**  The total left derived functor
of the colimit over `Cᵒᵖ` is left adjoint to the degreewise derived constant diagram
(`Stacks.CategoryHomology.totalDerivedColimitAdjunction`), and that right adjoint is monoidal for
the derived tensor products by
`CategoryTheory.Functor.constMapDerivedCategoryMonoidal`; so `Lπ_!` carries the canonical oplax
monoidal structure, whose comparison morphism is
`Stacks.CategoryHomology.totalDerivedColimitTensorComparison`.

This is the comparison morphism of Stacks 08QC and nothing more: it is not proved to be an
isomorphism, and the cosimplicial resolution hypothesis of Stacks 08Q9, under which the source
asserts that it is, is neither assumed nor used. -/
@[instance_reducible]
def totalDerivedColimitOplaxMonoidal :
    letI := CochainComplex.KFlatMonoidal.derivedMonoidal E hresE
    letI := CochainComplex.KFlatMonoidal.derivedMonoidal (Cᵒᵖ ⥤ E) hresCE
    (totalDerivedColimit C E).OplaxMonoidal :=
  CategoryTheory.Functor.oplaxMonoidal_of_adjunction_constMapDerivedCategory hresE hresCE
    (totalDerivedColimitAdjunction C E)

/-- **The canonical comparison morphism of Stacks 08QC**

`Lπ_!(K₁ ⊗^L K₂) ⟶ Lπ_!(K₁) ⊗^L Lπ_!(K₂)`

in `D(E)`, for `K₁, K₂` in `D(Cᵒᵖ ⥤ E)`.  It is the tensorator of
`Stacks.CategoryHomology.totalDerivedColimitOplaxMonoidal`, hence the mate of the identity under
the adjunction `Lπ_! ⊣ π^{-1}` of
`Stacks.CategoryHomology.totalDerivedColimitAdjunction`: the canonical map, not a choice.

**It is not proved to be an isomorphism here**, which is the assertion of Stacks 08QC; that
assertion is what the cosimplicial resolution of Stacks 08Q9 is for, and no such resolution
appears in this file. -/
def totalDerivedColimitTensorComparison (K₁ K₂ : DerivedCategory (Cᵒᵖ ⥤ E)) :
    letI := CochainComplex.KFlatMonoidal.derivedMonoidal E hresE
    letI := CochainComplex.KFlatMonoidal.derivedMonoidal (Cᵒᵖ ⥤ E) hresCE
    (totalDerivedColimit C E).obj (MonoidalCategoryStruct.tensorObj K₁ K₂) ⟶
      MonoidalCategoryStruct.tensorObj ((totalDerivedColimit C E).obj K₁)
        ((totalDerivedColimit C E).obj K₂) :=
  letI := CochainComplex.KFlatMonoidal.derivedMonoidal E hresE
  letI := CochainComplex.KFlatMonoidal.derivedMonoidal (Cᵒᵖ ⥤ E) hresCE
  letI := totalDerivedColimitOplaxMonoidal C E hresE hresCE
  CategoryTheory.Functor.OplaxMonoidal.δ (totalDerivedColimit C E) K₁ K₂

end Stacks.CategoryHomology

end
