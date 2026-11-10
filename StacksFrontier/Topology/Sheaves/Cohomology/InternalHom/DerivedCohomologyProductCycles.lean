module

public import StacksFrontier.Homology.Injectives.KInjective.RealizeDerivedIso
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.HomComplexCohomologyProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.HomComplexCompositionOnExtSheaves

/-!
# The cohomology product of a derived tensor product is the product induced by tensoring cocycles

Let `(X, O_X)` be a ringed space. There are two composition products on the cohomology sheaves of
internal Homs of complexes of `O_X`-modules, and nothing identified them.

* `Stacks.SheafOfModules.sheafExtProduct` is built in the derived category: the cohomology product
  of a derived tensor product, `Stacks.SheafOfModules.derivedCohomologyTensorProduct`, formed on
  the chosen K-flat representatives, followed by the derived composition morphism of Stacks 0A8V.
* `Stacks.SheafOfModules.homologyComposition`, with its form on local sections
  `Stacks.SheafOfModules.homologyMul`, is built at the level of complexes: the product induced by
  tensoring cocycles followed by the composition morphism of internal Hom complexes of Stacks
  0A91.

The composition morphisms were already matched, by
`Stacks.SheafOfModules.strictlyPerfectHomComparison_derivedSheafExtComposition`. What was not
matched is the other factor, and this file matches it.

## Main definitions

* `Stacks.SheafOfModules.kFlatRepresentativeComparison`: the morphism of complexes realizing the
  identification of a K-injective complex with its chosen K-flat representative.

## Main results

* `Stacks.SheafOfModules.toTensor_derivedCohomologyTensorProduct`: **the cohomology product of a
  derived tensor product, carried to the ordinary total tensor complex, is the product induced by
  tensoring cocycles.**
* `Stacks.SheafOfModules.homComplexDerivedComposition_derivedCohomologyTensorProduct` and
  `Stacks.SheafOfModules.homologyComposition_eq_derived`: **the derived composition product on
  the cohomology sheaves of internal Homs is the cycle-level composition pairing**, in the two
  directions in which a consumer uses it.
* `Stacks.SheafOfModules.toTensor_derivedCohomologyTensorProduct_of_isKInjective` and
  `Stacks.SheafOfModules.homologyComposition_eq_derived_of_isKInjective`: the same statements with
  the realization hypotheses discharged.

## Implementation notes

**Why a realization hypothesis is needed and what discharges it.**
`Stacks.SheafOfModules.derivedCohomologyTensorProduct` is formed on
`Stacks.SheafOfModules.kFlatRepresentative`, a chosen K-flat complex related to the given object
of `D(O_X)` by an isomorphism of the derived category and by nothing else; the implementation
notes of `StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCohomologyProduct` record
that no coherence across choices of model is asserted. The cycle-level product, on the other hand,
is a construction on complexes. What joins them is that the canonical map from a derived tensor
product to the ordinary total tensor product is determined by its value on K-flat complexes
together with naturality
(`Stacks.SheafOfModules.DerivedTensorProduct.toTensor_eq_of_resolutions`), and that determination
consumes a K-flat *resolution* — a morphism of complexes out of a K-flat complex — not merely an
identification in the derived category. The hypothesis below is exactly such a morphism for the
chosen representative, and it exists whenever the target is K-injective
(`CochainComplex.realizeDerivedIso`), which is the case the composition product is used in.

**Why the identification is stated after the canonical map and not before.** For arbitrary
complexes `P` and `Q` the derived tensor product of their classes is not the class of their total
tensor complex — that is the content of K-flatness — so the two products do not have the same
target and no identification of them alone can be stated. They are compared after the canonical
map, which is the only morphism between the two targets that exists in general; and the derived
composition morphism factors through that very map, so the composition products *are* compared
with no residue.

**Associativity.** The implementation notes of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.HomComplexCohomologyProduct` and of
`...InternalHom.ExtAlgebraFromKInjective` record that the derived composition product is unusable
for an associativity statement, the derived associator on K-flat representatives of Tag 0FPT being
unavailable. That is about a direct proof: with the identification below, associativity of the
derived product in the K-injective case follows from
`Stacks.SheafOfModules.homologyMul_assoc`, which is proved on local sections and uses no
associator.

**One rewriting hazard.** The inverse of a tensor product of two isomorphisms is itself a
composite — of a whiskering with a whiskering — so an unrestricted `Category.assoc` rewrite
reassociates inside it. Every associativity rewrite below pins its first factor.

## References

* [Stacks Project, Tag 0A8V](https://stacks.math.columbia.edu/tag/0A8V)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Category Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

attribute [local instance_reducible] CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive monoidalSpace' symmetricSpace'
  monoidalPreadditiveSpace' monoidalClosedSpace' preservesColimitTensorRightSpace'
  preservesFiniteColimitsTensorRight' preservesFiniteColimitsTensorLeft'

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The chosen K-flat representative computes the cohomology sheaves of a complex it is
compared with by a chain map.** If `w` is a morphism of complexes whose class is the
identification `Stacks.SheafOfModules.kFlatRepresentativeIso`, then the identification of the
cohomology sheaf of an object of `D(O_X)` with that of its chosen K-flat representative, read
through the factorisation of the derived homology functor, is the map `w` induces on cohomology.

This is naturality of `CategoryTheory.DerivedCategory.homologyFunctorFactors` at `w`, and it is
what lets a statement about the chosen representative be read on the complex itself. -/
theorem homologyKFlatRepresentativeIso_hom_homologyFunctorFactors
    (P : CochainComplex (StructureSheafModules Rc) ℤ)
    (w : kFlatRepresentative Rc (DerivedCategory.Q.obj P) ⟶ P)
    (hw : DerivedCategory.Q.map w =
      (kFlatRepresentativeIso Rc (DerivedCategory.Q.obj P)).hom) (i : ℤ) :
    (homologyKFlatRepresentativeIso Rc (DerivedCategory.Q.obj P) i).hom ≫
        ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) i).app P).hom =
      HomologicalComplex.homologyMap w i := by
  have h1 : (homologyKFlatRepresentativeIso Rc (DerivedCategory.Q.obj P) i).hom =
      ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) i).app
          (kFlatRepresentative Rc (DerivedCategory.Q.obj P))).inv ≫
        (DerivedCategory.homologyFunctor (StructureSheafModules Rc) i).map
          (kFlatRepresentativeIso Rc (DerivedCategory.Q.obj P)).hom := rfl
  have hnat := DerivedCategory.homologyFunctorFactors_hom_naturality w i
  rw (transparency := .default) [h1, ← hw, Category.assoc, hnat, Iso.inv_hom_id_assoc]


section Realize

variable (P : CochainComplex (StructureSheafModules Rc) ℤ) [P.IsKInjective]

/-- **The morphism of complexes realizing the identification of a K-injective complex with its
chosen K-flat representative.** Every isomorphism of the derived category whose target is the
class of a K-injective complex is the class of a morphism of complexes
(`CochainComplex.realizeDerivedIso`), and this is that morphism for
`Stacks.SheafOfModules.kFlatRepresentativeIso`. -/
def kFlatRepresentativeComparison :
    kFlatRepresentative Rc (DerivedCategory.Q.obj P) ⟶ P :=
  CochainComplex.realizeDerivedIso _ _ (kFlatRepresentativeIso Rc (DerivedCategory.Q.obj P))

/-- **The realization does realize the identification.** -/
theorem Q_map_kFlatRepresentativeComparison :
    DerivedCategory.Q.map (kFlatRepresentativeComparison Rc P) =
      (kFlatRepresentativeIso Rc (DerivedCategory.Q.obj P)).hom :=
  CochainComplex.Q_map_realizeDerivedIso _ _ _

end Realize

section Cycles

variable (P Q : CochainComplex (StructureSheafModules Rc) ℤ)
  (w : kFlatRepresentative Rc (DerivedCategory.Q.obj P) ⟶ P)
  (hw : DerivedCategory.Q.map w = (kFlatRepresentativeIso Rc (DerivedCategory.Q.obj P)).hom)
  (v : kFlatRepresentative Rc (DerivedCategory.Q.obj Q) ⟶ Q)
  (hv : DerivedCategory.Q.map v = (kFlatRepresentativeIso Rc (DerivedCategory.Q.obj Q)).hom)

include hw hv in
/-- **The comparison identifying a derived tensor product with the total tensor complex of the
chosen K-flat representatives, followed by the total tensor of two chain maps realizing those
representatives, is the canonical map to the ordinary total tensor product.**

The canonical map is pinned by its value on K-flat complexes together with naturality
(`Stacks.SheafOfModules.DerivedTensorProduct.toTensor_comp_augmentations`), and `w` and `v`
exhibit the chosen representatives as K-flat resolutions of `P` and `Q`. -/
theorem derivedTensorKFlatRepresentativeIso_hom_mapBifunctorMap :
    (derivedTensorKFlatRepresentativeIso Rc (DerivedCategory.Q.obj P)
          (DerivedCategory.Q.obj Q)).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap w v
          (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)) =
      (canonicalDerivedTensorProduct (ringedSite Rc)).toTensor P Q := by
  have haug := (canonicalDerivedTensorProduct (ringedSite Rc)).toTensor_comp_augmentations
    w v (isKFlat_kFlatRepresentative Rc (DerivedCategory.Q.obj P))
    (isKFlat_kFlatRepresentative Rc (DerivedCategory.Q.obj Q))
  have h1 : (kFlatRepresentativeIso Rc (DerivedCategory.Q.obj P)).inv ≫
      DerivedCategory.Q.map w = 𝟙 _ := by rw [hw]; exact Iso.inv_hom_id _
  have h2 : (kFlatRepresentativeIso Rc (DerivedCategory.Q.obj Q)).inv ≫
      DerivedCategory.Q.map v = 𝟙 _ := by rw [hv]; exact Iso.inv_hom_id _
  have hdtm : derivedTensorMap Rc
        (kFlatRepresentativeIso Rc (DerivedCategory.Q.obj P)).inv
        (kFlatRepresentativeIso Rc (DerivedCategory.Q.obj Q)).inv ≫
      derivedTensorMap Rc (DerivedCategory.Q.map w) (DerivedCategory.Q.map v) = 𝟙 _ := by
    rw [RingedSite.derivedTensorMap_comp, h1, h2, RingedSite.derivedTensorMap_id]
  have hhom : (derivedTensorKFlatRepresentativeIso Rc (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj Q)).hom =
      derivedTensorMap Rc (kFlatRepresentativeIso Rc (DerivedCategory.Q.obj P)).inv
          (kFlatRepresentativeIso Rc (DerivedCategory.Q.obj Q)).inv ≫
        ((canonicalDerivedTensorProduct (ringedSite Rc)).comparison
          (kFlatRepresentative Rc (DerivedCategory.Q.obj P))
          (kFlatRepresentative Rc (DerivedCategory.Q.obj Q))
          (isKFlat_kFlatRepresentative Rc (DerivedCategory.Q.obj P))
          (isKFlat_kFlatRepresentative Rc (DerivedCategory.Q.obj Q))).hom :=
    (Category.assoc _ _ _).symm
  have haugE : derivedTensorMap Rc (DerivedCategory.Q.map w) (DerivedCategory.Q.map v) ≫
      (canonicalDerivedTensorProduct (ringedSite Rc)).toTensor P Q =
      ((canonicalDerivedTensorProduct (ringedSite Rc)).comparison
          (kFlatRepresentative Rc (DerivedCategory.Q.obj P))
          (kFlatRepresentative Rc (DerivedCategory.Q.obj Q))
          (isKFlat_kFlatRepresentative Rc (DerivedCategory.Q.obj P))
          (isKFlat_kFlatRepresentative Rc (DerivedCategory.Q.obj Q))).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap w v
          (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)) :=
    (Category.assoc _ _ _).trans haug
  rw (transparency := .default) [hhom, Category.assoc, ← haugE, ← Category.assoc, hdtm,
    Category.id_comp]


/-! ### An elementary factorisation in a category

The lemma below is pure category theory, and it is stated separately for a reason of elaboration
and not of taste. In the development here the ambient category is `D(O_X)` for `O_X` a sheaf of
rings on a space, whose objects are spelled through
`Stacks.SheafOfModules.StructureSheafModules`, and the total tensor complex is spelled
`HomologicalComplex.mapBifunctor` at `Stacks.SheafOfModules.Tensor.sheafTensor` on the side the
derived comparison is stated at and `HomologicalComplex.tensorObj` on the side the cycle-level
product is stated at. The type-correctness check `rw` performs does not see through either
spelling, and `rw (transparency := .default)` crosses them only by unfolding the chosen K-flat
representatives, their identifications and the direct sums of the total complex, which
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/Bifunctor.lean` records as
unaffordable at the default elaboration limits. Stated for an abstract category the same
rewriting is free of all of that, and the result is applied with `exact`, which is up to
definitional unfolding and so crosses each spelling once.

This is the device
`StacksFrontier/Topology/Sheaves/Cohomology/InternalHom/DerivedCohomologyProductNaturality.lean`
uses, for the same reason. -/

section Factorisation

variable {C : Type*} [Category C]

/-- **A three-factor composite collapses when its first factor is an isomorphism's inverse and
the other two compose through that isomorphism's forward map.** Given `g = e.inv ≫ a`,
`a ≫ x = m` and `m ≫ y = e.hom ≫ z`, the composite `g ≫ x ≫ y` is `z`. -/
theorem comp_comp_eq_of_inv_factor {V W A₁ A₂ A₃ : C} (e : V ≅ W) {g : W ⟶ A₁} {a : V ⟶ A₁}
    {x : A₁ ⟶ A₂} {m : V ⟶ A₂} {y : A₂ ⟶ A₃} {z : W ⟶ A₃} (h₁ : g = e.inv ≫ a)
    (h₂ : a ≫ x = m) (h₃ : m ≫ y = e.hom ≫ z) :
    g ≫ x ≫ y = z := by
  rw [h₁, Category.assoc, ← Category.assoc a, h₂, h₃, Iso.inv_hom_id_assoc]

end Factorisation

include hw hv in
/-- **The cohomology sheaf of a derived tensor product, read on the total tensor complex of the
chosen K-flat representatives and then carried to the total tensor complex of `P` and `Q`, is
the map that the total tensor of `w` and `v` induces on cohomology.** -/
theorem homologyDerivedTensorKFlatIso_inv_toTensor (n : ℤ) :
    (homologyDerivedTensorKFlatIso Rc (DerivedCategory.Q.obj P)
          (DerivedCategory.Q.obj Q) n).inv ≫
        (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map
          ((canonicalDerivedTensorProduct (ringedSite Rc)).toTensor P Q) ≫
        ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) n).app
          (HomologicalComplex.tensorObj P Q)).hom =
      HomologicalComplex.homologyMap (HomologicalComplex.mapBifunctorMap
        (C₁ := SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))
        (C₂ := SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))
        (D := SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) w v
        (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)) n := by
  have hinv : (homologyDerivedTensorKFlatIso Rc (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj Q) n).inv =
      ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) n).app
        (HomologicalComplex.tensorObj (kFlatRepresentative Rc (DerivedCategory.Q.obj P))
          (kFlatRepresentative Rc (DerivedCategory.Q.obj Q)))).inv ≫
      (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map
        (derivedTensorKFlatRepresentativeIso Rc (DerivedCategory.Q.obj P)
          (DerivedCategory.Q.obj Q)).inv := rfl
  have hcomp : (derivedTensorKFlatRepresentativeIso Rc (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj Q)).inv ≫
      (canonicalDerivedTensorProduct (ringedSite Rc)).toTensor P Q =
      DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
        (C₁ := SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))
        (C₂ := SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))
        (D := SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) w v
        (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)) :=
    Iso.inv_comp_eq _ |>.2
      (derivedTensorKFlatRepresentativeIso_hom_mapBifunctorMap Rc P Q w hw v hv).symm
  have hmap : (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map
        (derivedTensorKFlatRepresentativeIso Rc (DerivedCategory.Q.obj P)
          (DerivedCategory.Q.obj Q)).inv ≫
      (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map
        ((canonicalDerivedTensorProduct (ringedSite Rc)).toTensor P Q) =
      (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map
        (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          (C₁ := SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))
          (C₂ := SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))
          (D := SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) w v
          (Tensor.sheafTensor Rc) (ComplexShape.up ℤ))) := by
    rw [← Functor.map_comp]
    exact congrArg _ hcomp
  have hnat := DerivedCategory.homologyFunctorFactors_hom_naturality
    (HomologicalComplex.mapBifunctorMap
      (C₁ := SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))
      (C₂ := SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))
      (D := SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) w v
      (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)) n
  exact comp_comp_eq_of_inv_factor _ hinv hmap hnat


/-- **The cohomology product of a total tensor complex is natural in both variables**, at the
spelling of the total tensor product in which the derived comparison is stated. This is
`CochainComplex.tensorHomology_naturality`; the two spellings of the induced morphism,
`HomologicalComplex.tensorHom` and `HomologicalComplex.mapBifunctorMap` at the sheaf tensor
product, are the same morphism. -/
theorem tensorComplexHomology_naturality {P₁ P₂ Q₁ Q₂ : CochainComplex (StructureSheafModules Rc) ℤ}
    (f : P₁ ⟶ P₂) (g : Q₁ ⟶ Q₂) (i j : ℤ) :
    tensorComplexHomology Rc P₁ Q₁ i j ≫
        HomologicalComplex.homologyMap (HomologicalComplex.mapBifunctorMap
          (C₁ := SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))
          (C₂ := SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))
          (D := SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) f g
          (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)) (i + j) =
      (HomologicalComplex.homologyMap f i ⊗ₘ HomologicalComplex.homologyMap g j) ≫
        tensorComplexHomology Rc P₂ Q₂ i j :=
  CochainComplex.tensorHomology_naturality P₁ Q₁ f g i j

include hw hv in
/-- **The cohomology product of a derived tensor product is the product induced by tensoring
cocycles.** For complexes `P` and `Q` of `O_X`-modules, the pairing

`Hⁱ(P) ⊗_{O_X} Hʲ(Q) ⟶ Hⁱ⁺ʲ(P ⊗_{O_X} Q)`

obtained from `Stacks.SheafOfModules.derivedCohomologyTensorProduct` by the canonical map from
the derived tensor product to the ordinary total tensor product is
`Stacks.SheafOfModules.tensorComplexHomology`, the product induced by tensoring cocycles.

This is the identification that separates the derived composition product on Ext sheaves from
the cycle-level composition pairing. The hypotheses are morphisms of complexes `w` and `v`
realizing the two identifications `Stacks.SheafOfModules.kFlatRepresentativeIso`; they are what
exhibits the chosen representatives as K-flat resolutions of `P` and of `Q`, and they are
supplied by `Stacks.SheafOfModules.kFlatRepresentativeComparison` whenever `P` and `Q` are
K-injective. -/
theorem toTensor_derivedCohomologyTensorProduct (i j : ℤ) :
    derivedCohomologyTensorProduct Rc (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) i j ≫
        (DerivedCategory.homologyFunctor (StructureSheafModules Rc) (i + j)).map
          ((canonicalDerivedTensorProduct (ringedSite Rc)).toTensor P Q) ≫
        ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) (i + j)).app
          (HomologicalComplex.tensorObj P Q)).hom =
      (((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) i).app P).hom ⊗ₘ
          ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) j).app Q).hom) ≫
        tensorComplexHomology Rc P Q i j := by
  have hdef : derivedCohomologyTensorProduct Rc (DerivedCategory.Q.obj P)
      (DerivedCategory.Q.obj Q) i j =
      (@tensorIso _ _ (monoidalSpace' Rc) _ _ _ _
            (homologyKFlatRepresentativeIso Rc (DerivedCategory.Q.obj P) i)
            (homologyKFlatRepresentativeIso Rc (DerivedCategory.Q.obj Q) j)).inv ≫
        tensorComplexHomology Rc (kFlatRepresentative Rc (DerivedCategory.Q.obj P))
            (kFlatRepresentative Rc (DerivedCategory.Q.obj Q)) i j ≫
          (homologyDerivedTensorKFlatIso Rc (DerivedCategory.Q.obj P)
            (DerivedCategory.Q.obj Q) (i + j)).inv := rfl
  rw (transparency := .default) [hdef,
    Category.assoc (f := (@tensorIso _ _ (monoidalSpace' Rc) _ _ _ _
      (homologyKFlatRepresentativeIso Rc (DerivedCategory.Q.obj P) i)
      (homologyKFlatRepresentativeIso Rc (DerivedCategory.Q.obj Q) j)).inv),
    Category.assoc (f := tensorComplexHomology Rc
      (kFlatRepresentative Rc (DerivedCategory.Q.obj P))
      (kFlatRepresentative Rc (DerivedCategory.Q.obj Q)) i j),
    homologyDerivedTensorKFlatIso_inv_toTensor Rc P Q w hw v hv,
    tensorComplexHomology_naturality Rc w v i j,
    ← homologyKFlatRepresentativeIso_hom_homologyFunctorFactors Rc P w hw i,
    ← homologyKFlatRepresentativeIso_hom_homologyFunctorFactors Rc Q v hv j,
    ← MonoidalCategory.tensorHom_comp_tensorHom,
    Category.assoc (f := @MonoidalCategoryStruct.tensorHom _ _
      (monoidalSpace' Rc).toMonoidalCategoryStruct _ _ _ _
      (homologyKFlatRepresentativeIso Rc (DerivedCategory.Q.obj P) i).hom
      (homologyKFlatRepresentativeIso Rc (DerivedCategory.Q.obj Q) j).hom),
    show @MonoidalCategoryStruct.tensorHom _ _
        (monoidalSpace' Rc).toMonoidalCategoryStruct _ _ _ _
        (homologyKFlatRepresentativeIso Rc (DerivedCategory.Q.obj P) i).hom
        (homologyKFlatRepresentativeIso Rc (DerivedCategory.Q.obj Q) j).hom =
      (@tensorIso _ _ (monoidalSpace' Rc) _ _ _ _
        (homologyKFlatRepresentativeIso Rc (DerivedCategory.Q.obj P) i)
        (homologyKFlatRepresentativeIso Rc (DerivedCategory.Q.obj Q) j)).hom from rfl,
    Iso.inv_hom_id_assoc]
  rfl


end Cycles

section Composition

variable (K L M : CochainComplex (StructureSheafModules Rc) ℤ)
  (wLM : kFlatRepresentative Rc
      (DerivedCategory.Q.obj (RingedSite.sheafHomComplex (ringedSite Rc) L M).obj) ⟶
    (RingedSite.sheafHomComplex (ringedSite Rc) L M).obj)
  (hwLM : DerivedCategory.Q.map wLM =
    (kFlatRepresentativeIso Rc
      (DerivedCategory.Q.obj (RingedSite.sheafHomComplex (ringedSite Rc) L M).obj)).hom)
  (vKL : kFlatRepresentative Rc
      (DerivedCategory.Q.obj (RingedSite.sheafHomComplex (ringedSite Rc) K L).obj) ⟶
    (RingedSite.sheafHomComplex (ringedSite Rc) K L).obj)
  (hvKL : DerivedCategory.Q.map vKL =
    (kFlatRepresentativeIso Rc
      (DerivedCategory.Q.obj (RingedSite.sheafHomComplex (ringedSite Rc) K L).obj)).hom)

include hwLM hvKL in
/-- **The composition product on the cohomology sheaves of derived internal Homs is the
cycle-level composition pairing.** The derived composition morphism of internal Hom complexes,
read on cohomology sheaves after the cohomology product of the derived tensor product, is
`Stacks.SheafOfModules.homologyComposition`:

`Hⁱ(SheafHom(L, M)) ⊗_{O_X} Hʲ(SheafHom(K, L)) ⟶ Hⁱ⁺ʲ(SheafHom(K, M))`.

The derived composition morphism of `AlgebraicGeometry.RingedSite.homComplexDerivedComposition`
is the canonical map to the ordinary total tensor product followed by the composition morphism
of internal Hom complexes of Stacks 0A91, so the identification of the two pairings is
`Stacks.SheafOfModules.toTensor_derivedCohomologyTensorProduct` composed with the map that the
composition morphism induces on cohomology. -/
theorem homComplexDerivedComposition_derivedCohomologyTensorProduct (i j : ℤ) :
    derivedCohomologyTensorProduct Rc
          (DerivedCategory.Q.obj (RingedSite.sheafHomComplex (ringedSite Rc) L M).obj)
          (DerivedCategory.Q.obj (RingedSite.sheafHomComplex (ringedSite Rc) K L).obj) i j ≫
        (DerivedCategory.homologyFunctor (StructureSheafModules Rc) (i + j)).map
          (RingedSite.homComplexDerivedComposition (ringedSite Rc)
            (canonicalDerivedTensorProduct (ringedSite Rc)) K L M) ≫
        ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) (i + j)).app
          (RingedSite.sheafHomComplex (ringedSite Rc) K M).obj).hom =
      (((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) i).app
            (RingedSite.sheafHomComplex (ringedSite Rc) L M).obj).hom ⊗ₘ
          ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) j).app
            (RingedSite.sheafHomComplex (ringedSite Rc) K L).obj).hom) ≫
        homologyComposition Rc K L M i j := by
  have hdc : RingedSite.homComplexDerivedComposition (ringedSite Rc)
      (canonicalDerivedTensorProduct (ringedSite Rc)) K L M =
      (canonicalDerivedTensorProduct (ringedSite Rc)).toTensor
          (RingedSite.sheafHomComplex (ringedSite Rc) L M).obj
          (RingedSite.sheafHomComplex (ringedSite Rc) K L).obj ≫
        DerivedCategory.Q.map (compositionTotalMap Rc K L M) := rfl
  have hnat := DerivedCategory.homologyFunctorFactors_hom_naturality
    (compositionTotalMap Rc K L M) (i + j)
  rw (transparency := .default) [hdc, Functor.map_comp,
    Category.assoc (f := (DerivedCategory.homologyFunctor (StructureSheafModules Rc) (i + j)).map
      ((canonicalDerivedTensorProduct (ringedSite Rc)).toTensor
        (RingedSite.sheafHomComplex (ringedSite Rc) L M).obj
        (RingedSite.sheafHomComplex (ringedSite Rc) K L).obj)),
    hnat, reassoc_of% toTensor_derivedCohomologyTensorProduct Rc
      (RingedSite.sheafHomComplex (ringedSite Rc) L M).obj
      (RingedSite.sheafHomComplex (ringedSite Rc) K L).obj wLM hwLM vKL hvKL i j]
  rfl


include hwLM hvKL in
/-- **The cycle-level composition pairing, solved for.** The same identification as
`Stacks.SheafOfModules.homComplexDerivedComposition_derivedCohomologyTensorProduct`, written as
a formula for `Stacks.SheafOfModules.homologyComposition` in terms of the derived composition
product. -/
theorem homologyComposition_eq_derived (i j : ℤ) :
    homologyComposition Rc K L M i j =
      (((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) i).app
            (RingedSite.sheafHomComplex (ringedSite Rc) L M).obj) ⊗ᵢ
          ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) j).app
            (RingedSite.sheafHomComplex (ringedSite Rc) K L).obj)).inv ≫
        (derivedCohomologyTensorProduct Rc
            (DerivedCategory.Q.obj (RingedSite.sheafHomComplex (ringedSite Rc) L M).obj)
            (DerivedCategory.Q.obj (RingedSite.sheafHomComplex (ringedSite Rc) K L).obj) i j ≫
          (DerivedCategory.homologyFunctor (StructureSheafModules Rc) (i + j)).map
              (RingedSite.homComplexDerivedComposition (ringedSite Rc)
                (canonicalDerivedTensorProduct (ringedSite Rc)) K L M) ≫
            ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) (i + j)).app
              (RingedSite.sheafHomComplex (ringedSite Rc) K M).obj).hom) := by
  rw (transparency := .default)
    [homComplexDerivedComposition_derivedCohomologyTensorProduct Rc K L M wLM hwLM vKL hvKL i j,
      show (((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) i).app
            (RingedSite.sheafHomComplex (ringedSite Rc) L M).obj).hom ⊗ₘ
          ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) j).app
            (RingedSite.sheafHomComplex (ringedSite Rc) K L).obj).hom) =
        (((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) i).app
            (RingedSite.sheafHomComplex (ringedSite Rc) L M).obj) ⊗ᵢ
          ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) j).app
            (RingedSite.sheafHomComplex (ringedSite Rc) K L).obj)).hom from rfl,
      Iso.inv_hom_id_assoc]

/-- **The bilinear pairing on local sections is the composition pairing read through the unit of
the sheafification adjunction.** This is the definition of
`Stacks.SheafOfModules.homologyMul`, recorded so that the identification of
`Stacks.SheafOfModules.homologyComposition` with the derived composition product is an
identification of `homologyMul` with it. -/
theorem homologyMul_eq_toBilinear (i j : ℤ) :
    homologyMul Rc K L M i j =
      PresheafOfModules.toBilinear
        (((PresheafOfModules.sheafificationAdjunction
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O).obj)).unit.app
            (((RingedSite.sheafHomComplex (ringedSite Rc) L M).obj.homology i).val ⊗
              ((RingedSite.sheafHomComplex (ringedSite Rc) K L).obj.homology j).val)) ≫
          (homologyComposition Rc K L M i j).val) := rfl

end Composition

section KInjective

variable (P Q : CochainComplex (StructureSheafModules Rc) ℤ) [P.IsKInjective] [Q.IsKInjective]

/-- **The cohomology product of a derived tensor product of two K-injective complexes is the
product induced by tensoring cocycles**, with no hypothesis beyond K-injectivity:
`Stacks.SheafOfModules.toTensor_derivedCohomologyTensorProduct` with its realization hypotheses
discharged by `Stacks.SheafOfModules.kFlatRepresentativeComparison`. -/
theorem toTensor_derivedCohomologyTensorProduct_of_isKInjective (i j : ℤ) :
    derivedCohomologyTensorProduct Rc (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) i j ≫
        (DerivedCategory.homologyFunctor (StructureSheafModules Rc) (i + j)).map
          ((canonicalDerivedTensorProduct (ringedSite Rc)).toTensor P Q) ≫
        ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) (i + j)).app
          (HomologicalComplex.tensorObj P Q)).hom =
      (((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) i).app P).hom ⊗ₘ
          ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) j).app Q).hom) ≫
        tensorComplexHomology Rc P Q i j :=
  toTensor_derivedCohomologyTensorProduct Rc P Q
    (kFlatRepresentativeComparison Rc P) (Q_map_kFlatRepresentativeComparison Rc P)
    (kFlatRepresentativeComparison Rc Q) (Q_map_kFlatRepresentativeComparison Rc Q) i j

end KInjective

section CompositionKInjective

variable (K L M : CochainComplex (StructureSheafModules Rc) ℤ)
      [(RingedSite.sheafHomComplex (ringedSite Rc) L M).obj.IsKInjective]
      [(RingedSite.sheafHomComplex (ringedSite Rc) K L).obj.IsKInjective]

/-- **The derived composition product on the cohomology sheaves of internal Homs is the
cycle-level composition pairing**, with no hypothesis beyond K-injectivity of the two internal
Hom complexes the pairing is formed on. By
`Stacks.SheafOfModules.isKInjective_sheafHomComplex_of_isKFlat` that holds whenever `M` is
K-injective and `L` is K-flat, and whenever `L` is K-injective and `K` is K-flat. -/
theorem homologyComposition_eq_derived_of_isKInjective (i j : ℤ) :
    homologyComposition Rc K L M i j =
      (((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) i).app
            (RingedSite.sheafHomComplex (ringedSite Rc) L M).obj) ⊗ᵢ
          ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) j).app
            (RingedSite.sheafHomComplex (ringedSite Rc) K L).obj)).inv ≫
        (derivedCohomologyTensorProduct Rc
            (DerivedCategory.Q.obj (RingedSite.sheafHomComplex (ringedSite Rc) L M).obj)
            (DerivedCategory.Q.obj (RingedSite.sheafHomComplex (ringedSite Rc) K L).obj) i j ≫
          (DerivedCategory.homologyFunctor (StructureSheafModules Rc) (i + j)).map
              (RingedSite.homComplexDerivedComposition (ringedSite Rc)
                (canonicalDerivedTensorProduct (ringedSite Rc)) K L M) ≫
            ((DerivedCategory.homologyFunctorFactors (StructureSheafModules Rc) (i + j)).app
              (RingedSite.sheafHomComplex (ringedSite Rc) K M).obj).hom) :=
  homologyComposition_eq_derived Rc K L M
    (kFlatRepresentativeComparison Rc (RingedSite.sheafHomComplex (ringedSite Rc) L M).obj)
    (Q_map_kFlatRepresentativeComparison Rc (RingedSite.sheafHomComplex (ringedSite Rc) L M).obj)
    (kFlatRepresentativeComparison Rc (RingedSite.sheafHomComplex (ringedSite Rc) K L).obj)
    (Q_map_kFlatRepresentativeComparison Rc (RingedSite.sheafHomComplex (ringedSite Rc) K L).obj)
      i j

end CompositionKInjective

end Stacks.SheafOfModules

end
