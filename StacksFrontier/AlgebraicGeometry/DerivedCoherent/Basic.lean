module

public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardClosedImmersion
public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.SerreClass
public import StacksFrontier.Homology.Injectives.Ext.SpectralSequenceOfFilteredComplex
public import StacksCore.Tactic.StacksAttribute

/-!
# Bounded above coherent complexes and quasi-coherent cohomology

Let `X` be a Noetherian scheme. The inclusion of the coherent `𝒪_X`-modules into the
quasi-coherent ones is exact, so it induces a functor on derived categories; restricted to the
bounded above complexes it lands in the full subcategory `D⁻_Coh(QCoh(𝒪_X))` of the bounded
above derived category of quasi-coherent modules whose objects have coherent cohomology in
every degree. This file constructs that functor and proves it is an equivalence
    `D⁻(Coh(𝒪_X)) ⥤ D⁻_Coh(QCoh(𝒪_X))`.

The proof is the Serre-subcategory criterion of [Stacks, Tag 0FCL]: the coherent modules are a
Serre class in `QCoh(𝒪_X)` with enough subobjects, so the derived functor of the inclusion is
full, faithful, and has essential image the bounded above complexes with coherent cohomology.
The criterion is stated for the full subcategory of `QCoh(𝒪_X)` cut out by coherence, which is
equivalent — indeed isomorphic — to `Coh(𝒪_X)`, so the comparison is transported along the
equivalence of derived categories that this induces.

## Main definitions

* `AlgebraicGeometry.coherentToQuasicoherentDerivedMinus` is the canonical functor
  `D⁻(Coh(𝒪_X)) ⥤ D⁻_Coh(QCoh(𝒪_X))`; it is the derived functor of the inclusion
  `Coh(𝒪_X) ⥤ QCoh(𝒪_X)`, which is what
  `AlgebraicGeometry.coherentToQuasicoherentDerivedMinus_comp_ι` records.
* `AlgebraicGeometry.coherentToQuasicoherentDerivedMinusEquivalence` packages the main result
  as an equivalence of categories.

## Main results

* `AlgebraicGeometry.coherentToQuasicoherentDerivedMinus_isEquivalence`: the canonical functor
  is an equivalence. This is the assertion of [Stacks, Tag 0FDA].
* `AlgebraicGeometry.coherentToQuasicoherentDerivedMinusEquivalence_functor`: the forward
  functor of the equivalence is the canonical one.

## Implementation notes

The statement is about *the* functor induced by the inclusion, not about the existence of some
equivalence: `coherentToQuasicoherentDerivedMinus` is a definition, the exactness and
additivity of the inclusion are instances rather than hypotheses, and the identification with
the derived functor of the inclusion is an equality of functors, proved by `rfl` because the
functor is literally the corestriction of that composite.

`HasDerivedCategory.standard` is installed as a local instance, so the derived categories here
are the standard models; nothing depends on the choice.

## References

* [Stacks Project, Tag 0FCL](https://stacks.math.columbia.edu/tag/0FCL)
* [Stacks Project, Tag 0FDA](https://stacks.math.columbia.edu/tag/0FDA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable (X : Scheme.{u})

/-- The inclusion `Coh(𝒪_X) ⥤ QCoh(𝒪_X)` of the coherent modules into the quasi-coherent
ones, viewed as a functor to the full subcategory of `QCoh(𝒪_X)` which coherence cuts out.
It is an isomorphism of categories on the nose: both sides are the coherent `𝒪_X`-modules with
all `𝒪_X`-module morphisms between them. -/
def coherentToSerreSubcategory :
    SheafOfModules.CoherentModules X.ringCatSheaf ⥤ (coherentInQuasicoherent X).FullSubcategory :=
  (coherentInQuasicoherent X).lift (coherentToQuasicoherent X) fun M => M.property

/-- `coherentToSerreSubcategory` is full: a morphism of the subcategory of `QCoh(𝒪_X)` is a
morphism of `𝒪_X`-modules between coherent modules. -/
instance full_coherentToSerreSubcategory : (coherentToSerreSubcategory X).Full where
  map_surjective f := ⟨ObjectProperty.homMk f.hom.hom, ObjectProperty.hom_ext _ rfl⟩

/-- `coherentToSerreSubcategory` is faithful: it does not change the underlying morphism of
`𝒪_X`-modules. -/
instance faithful_coherentToSerreSubcategory : (coherentToSerreSubcategory X).Faithful where
  map_injective h := ObjectProperty.hom_ext _ (congrArg (fun q => q.hom.hom) h)

/-- `coherentToSerreSubcategory` is essentially surjective: a coherent object of `QCoh(𝒪_X)` is
a coherent `𝒪_X`-module. -/
instance essSurj_coherentToSerreSubcategory : (coherentToSerreSubcategory X).EssSurj where
  mem_essImage Y := ⟨⟨Y.obj.obj, Y.property⟩, ⟨ObjectProperty.isoMk
    (coherentInQuasicoherent X) (ObjectProperty.isoMk
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) (Iso.refl Y.obj.obj))⟩⟩

/-- `coherentToSerreSubcategory` is an equivalence of categories. -/
instance isEquivalence_coherentToSerreSubcategory :
    (coherentToSerreSubcategory X).IsEquivalence := {}

/-- The equivalence between `Coh(𝒪_X)` and the full subcategory of `QCoh(𝒪_X)` of coherent
objects, given by `AlgebraicGeometry.coherentToSerreSubcategory`. -/
def coherentToSerreSubcategoryEquivalence [IsLocallyNoetherian X] :
    SheafOfModules.CoherentModules X.ringCatSheaf ≌ (coherentInQuasicoherent X).FullSubcategory :=
  (coherentToSerreSubcategory X).asEquivalence

/-- An equivalence of abelian categories preserving the zero morphisms is additive. -/
instance additive_coherentToSerreSubcategoryEquivalence [IsLocallyNoetherian X] :
    (coherentToSerreSubcategoryEquivalence X).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The functor `D(Coh(𝒪_X)) ⥤ D(Coh ⊆ QCoh(𝒪_X))` induced on derived categories by
`AlgebraicGeometry.coherentToSerreSubcategory`. -/
def coherentDerivedToSerre [IsLocallyNoetherian X] :
    DerivedCategory (SheafOfModules.CoherentModules X.ringCatSheaf) ⥤
      DerivedCategory (coherentInQuasicoherent X).FullSubcategory :=
  (coherentToSerreSubcategoryEquivalence X).functor.mapDerivedCategory

/-- An additive equivalence of abelian categories induces an equivalence of their derived
categories. -/
instance isEquivalence_coherentDerivedToSerre [IsLocallyNoetherian X] :
    (coherentDerivedToSerre X).IsEquivalence :=
  Stacks.Injectives.mapDerivedCategory_isEquivalence _

/-- `coherentDerivedToSerre` both preserves and reflects the objects of the derived category
which are `≤ n`, being induced by an exact equivalence. -/
lemma isLE_coherentDerivedToSerre_obj_iff [IsLocallyNoetherian X]
    (K : DerivedCategory (SheafOfModules.CoherentModules X.ringCatSheaf)) (n : ℤ) :
    ((coherentDerivedToSerre X).obj K).IsLE n ↔ K.IsLE n :=
  Functor.isLE_mapDerivedCategory_obj_iff (coherentToSerreSubcategoryEquivalence X) K n

/-- The bounded above objects of `D(Coh ⊆ QCoh(𝒪_X))` pull back along
`coherentDerivedToSerre` exactly to the bounded above objects of `D(Coh(𝒪_X))`. -/
lemma inverseImage_minus_coherentDerivedToSerre [IsLocallyNoetherian X] :
    (DerivedCategory.TStructure.t
        (C := (coherentInQuasicoherent X).FullSubcategory)).minus.inverseImage
      (coherentDerivedToSerre X) =
      (DerivedCategory.TStructure.t
        (C := SheafOfModules.CoherentModules X.ringCatSheaf)).minus := by
  ext K
  exact exists_congr fun n => isLE_coherentDerivedToSerre_obj_iff X K n

/-- The equivalence `D⁻(Coh(𝒪_X)) ≌ D⁻(Coh ⊆ QCoh(𝒪_X))` of bounded above derived categories
induced by `AlgebraicGeometry.coherentToSerreSubcategory`. -/
def coherentDerivedMinusToSerre [IsLocallyNoetherian X] :
    DerivedCategory.Minus (SheafOfModules.CoherentModules X.ringCatSheaf) ≌
      DerivedCategory.Minus (coherentInQuasicoherent X).FullSubcategory :=
  Equivalence.congrFullSubcategory (coherentDerivedToSerre X).asEquivalence
    (inverseImage_minus_coherentDerivedToSerre X)

/-- `coherentDerivedMinusToSerre` is the restriction of `coherentDerivedToSerre` to the
bounded above subcategories: composing it with the inclusion of `D⁻` into `D` gives the
inclusion followed by `coherentDerivedToSerre`. -/
lemma coherentDerivedMinusToSerre_comp_ι [IsLocallyNoetherian X] :
    (coherentDerivedMinusToSerre X).functor ⋙ DerivedCategory.Minus.ι =
      DerivedCategory.Minus.ι ⋙ coherentDerivedToSerre X := rfl

/-- The inclusion of the coherent objects of `QCoh(𝒪_X)` into `QCoh(𝒪_X)` is left exact, being
the inclusion of a Serre subcategory. -/
instance preservesFiniteLimits_coherentInQuasicoherentι [IsLocallyNoetherian X] :
    PreservesFiniteLimits (coherentInQuasicoherent X).ι :=
  ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass _

/-- The inclusion of the coherent objects of `QCoh(𝒪_X)` into `QCoh(𝒪_X)` is right exact,
being the inclusion of a Serre subcategory. -/
instance preservesFiniteColimits_coherentInQuasicoherentι [IsLocallyNoetherian X] :
    PreservesFiniteColimits (coherentInQuasicoherent X).ι :=
  ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _

/-- The inclusion of the coherent objects of `QCoh(𝒪_X)` into `QCoh(𝒪_X)` is additive. -/
instance additive_coherentInQuasicoherentι [IsLocallyNoetherian X] :
    (coherentInQuasicoherent X).ι.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The composite `D⁻(Coh(𝒪_X)) ⥤ D(QCoh(𝒪_X))` of the inclusion of the bounded above
complexes with the derived functor of the inclusion `Coh(𝒪_X) ⥤ QCoh(𝒪_X)`. This is the
functor of [Stacks, Tag 0FDA], before its target is cut down to the complexes with coherent
cohomology. -/
def coherentDerivedMinusInclusion [IsLocallyNoetherian X] :
    DerivedCategory.Minus (SheafOfModules.CoherentModules X.ringCatSheaf) ⥤
      DerivedCategory (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  DerivedCategory.Minus.ι ⋙ (coherentToQuasicoherent X).mapDerivedCategory

/-- `coherentDerivedMinusInclusion` factors through the equivalence
`D⁻(Coh(𝒪_X)) ≌ D⁻(Coh ⊆ QCoh(𝒪_X))`: composing that equivalence with the derived functor of
the inclusion of the Serre subcategory gives it back, because `D(-)` is compatible with
composition of exact functors. -/
def coherentDerivedMinusComparisonIso [IsLocallyNoetherian X] :
    (coherentDerivedMinusToSerre X).functor ⋙
        (DerivedCategory.Minus.ι ⋙ (coherentInQuasicoherent X).ι.mapDerivedCategory) ≅
      coherentDerivedMinusInclusion X :=
  Functor.isoWhiskerLeft DerivedCategory.Minus.ι
    (Functor.mapDerivedCategoryCompIso
      (F := (coherentToSerreSubcategoryEquivalence X).functor)
      (G := (coherentInQuasicoherent X).ι) (H := coherentToQuasicoherent X) (Iso.refl _))

/-- **Stacks Project, Tag 0FCL.** `coherentDerivedMinusInclusion` is full: the corresponding
functor out of `D⁻(Coh ⊆ QCoh(𝒪_X))` is, and the two differ by an equivalence. -/
instance full_coherentDerivedMinusInclusion [IsNoetherian X] :
    (coherentDerivedMinusInclusion X).Full :=
  have := (ObjectProperty.full_faithful_essImage_minus_mapDerivedCategory
    (coherentInQuasicoherent X) (exists_coherent_epi_comp X)).1
  Functor.Full.of_iso (coherentDerivedMinusComparisonIso X)

/-- **Stacks Project, Tag 0FCL.** `coherentDerivedMinusInclusion` is faithful: the
corresponding functor out of `D⁻(Coh ⊆ QCoh(𝒪_X))` is, and the two differ by an
equivalence. -/
instance faithful_coherentDerivedMinusInclusion [IsNoetherian X] :
    (coherentDerivedMinusInclusion X).Faithful :=
  have := (ObjectProperty.full_faithful_essImage_minus_mapDerivedCategory
    (coherentInQuasicoherent X) (exists_coherent_epi_comp X)).2.1
  Functor.Faithful.of_iso (coherentDerivedMinusComparisonIso X)

/-- **Stacks Project, Tag 0FCL.** The essential image of `coherentDerivedMinusInclusion`
consists exactly of the objects of `D(QCoh(𝒪_X))` which are bounded above and have coherent
cohomology in every degree. -/
lemma essImage_coherentDerivedMinusInclusion [IsNoetherian X]
    (Y : DerivedCategory (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (coherentDerivedMinusInclusion X).essImage Y ↔
      ((∃ n : ℤ, Y.IsLE n) ∧ ∀ i : ℤ, coherentInQuasicoherent X
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory i).obj Y)) := by
  rw [← (ObjectProperty.full_faithful_essImage_minus_mapDerivedCategory
    (coherentInQuasicoherent X) (exists_coherent_epi_comp X)).2.2 Y]
  constructor
  · rintro ⟨A, ⟨eA⟩⟩
    exact ⟨(coherentDerivedMinusToSerre X).functor.obj A,
      ⟨(coherentDerivedMinusComparisonIso X).app A ≪≫ eA⟩⟩
  · rintro ⟨B, ⟨eB⟩⟩
    refine ⟨(coherentDerivedMinusToSerre X).inverse.obj B, ⟨?_⟩⟩
    refine ((coherentDerivedMinusComparisonIso X).app _).symm ≪≫ ?_
    exact (DerivedCategory.Minus.ι ⋙
      (coherentInQuasicoherent X).ι.mapDerivedCategory).mapIso
        ((coherentDerivedMinusToSerre X).counitIso.app B) ≪≫ eB

/-- The derived inclusion of a bounded above complex of coherent modules is bounded above and
has coherent cohomology, so `coherentDerivedMinusInclusion` lands in `D⁻_Coh(QCoh(𝒪_X))`. -/
lemma derivedCategoryBMinus_coherentDerivedMinusInclusion_obj [IsNoetherian X]
    (K : DerivedCategory.Minus (SheafOfModules.CoherentModules X.ringCatSheaf)) :
    DerivedCategoryB.derivedCategoryBMinus (coherentInQuasicoherent X)
      ((coherentDerivedMinusInclusion X).obj K) :=
  have hK := (essImage_coherentDerivedMinusInclusion X _).mp ⟨K, ⟨Iso.refl _⟩⟩
  ⟨(DerivedCategoryB.isBoundedAbove_iff_exists_isLE _).2 hK.1, hK.2⟩

/-- **Stacks Project, Tag 0FDA.** The canonical functor
`D⁻(Coh(𝒪_X)) ⥤ D⁻_Coh(QCoh(𝒪_X))` on a Noetherian scheme: the derived functor of the
inclusion `Coh(𝒪_X) ⥤ QCoh(𝒪_X)`, restricted to the bounded above complexes and corestricted
to the bounded above complexes with coherent cohomology, where it lands. -/
@[stacks 0FDA]
def coherentToQuasicoherentDerivedMinus [IsNoetherian X] :
    DerivedCategory.Minus (SheafOfModules.CoherentModules X.ringCatSheaf) ⥤
      (DerivedCategoryB.derivedCategoryBMinus (coherentInQuasicoherent X)).FullSubcategory :=
  (DerivedCategoryB.derivedCategoryBMinus (coherentInQuasicoherent X)).lift
    (coherentDerivedMinusInclusion X) (derivedCategoryBMinus_coherentDerivedMinusInclusion_obj X)

/-- The functor of [Stacks, Tag 0FDA] *is* the derived functor of the inclusion
`Coh(𝒪_X) ⥤ QCoh(𝒪_X)`: forgetting the boundedness and coherence conditions on its target
returns the inclusion of the bounded above complexes followed by that derived functor. -/
theorem coherentToQuasicoherentDerivedMinus_comp_ι [IsNoetherian X] :
    coherentToQuasicoherentDerivedMinus X ⋙
        (DerivedCategoryB.derivedCategoryBMinus (coherentInQuasicoherent X)).ι =
      DerivedCategory.Minus.ι ⋙ (coherentToQuasicoherent X).mapDerivedCategory := rfl

/-- The functor of [Stacks, Tag 0FDA] is full, because it is so after composing with the fully
faithful inclusion of `D⁻_Coh(QCoh(𝒪_X))` into `D(QCoh(𝒪_X))`. -/
instance full_coherentToQuasicoherentDerivedMinus [IsNoetherian X] :
    (coherentToQuasicoherentDerivedMinus X).Full where
  map_surjective f := by
    obtain ⟨g, hg⟩ := (coherentDerivedMinusInclusion X).map_surjective f.hom
    exact ⟨g, ObjectProperty.hom_ext _ hg⟩

/-- The functor of [Stacks, Tag 0FDA] is faithful, because it is so after composing with the
inclusion of `D⁻_Coh(QCoh(𝒪_X))` into `D(QCoh(𝒪_X))`. -/
instance faithful_coherentToQuasicoherentDerivedMinus [IsNoetherian X] :
    (coherentToQuasicoherentDerivedMinus X).Faithful where
  map_injective h := (coherentDerivedMinusInclusion X).map_injective
    (congrArg (fun q => q.hom) h)

/-- The functor of [Stacks, Tag 0FDA] is essentially surjective: a bounded above complex of
quasi-coherent modules with coherent cohomology lies in the essential image of the derived
inclusion by [Stacks, Tag 0FCL]. -/
instance essSurj_coherentToQuasicoherentDerivedMinus [IsNoetherian X] :
    (coherentToQuasicoherentDerivedMinus X).EssSurj where
  mem_essImage K := by
    obtain ⟨Y, ⟨e⟩⟩ := (essImage_coherentDerivedMinusInclusion X K.obj).mpr
      ⟨(DerivedCategoryB.isBoundedAbove_iff_exists_isLE K.obj).1 K.property.1, K.property.2⟩
    exact ⟨Y, ⟨ObjectProperty.isoMk _ e⟩⟩

/-- **Stacks Project, Tag 0FDA.** On a Noetherian scheme the canonical functor
`D⁻(Coh(𝒪_X)) ⥤ D⁻_Coh(QCoh(𝒪_X))` is an equivalence: the bounded above derived category of
coherent modules is the full subcategory of the bounded above derived category of
quasi-coherent modules whose objects have coherent cohomology. -/
@[stacks 0FDA, sga "6 II 2.2.2"]
instance coherentToQuasicoherentDerivedMinus_isEquivalence [IsNoetherian X] :
    (coherentToQuasicoherentDerivedMinus X).IsEquivalence := {}

/-- **Stacks Project, Tag 0FDA**, as an equivalence of categories:
`D⁻(Coh(𝒪_X)) ≌ D⁻_Coh(QCoh(𝒪_X))` on a Noetherian scheme. Its functor is the canonical one,
by `AlgebraicGeometry.coherentToQuasicoherentDerivedMinusEquivalence_functor`. -/
def coherentToQuasicoherentDerivedMinusEquivalence [IsNoetherian X] :
    DerivedCategory.Minus (SheafOfModules.CoherentModules X.ringCatSheaf) ≌
      (DerivedCategoryB.derivedCategoryBMinus (coherentInQuasicoherent X)).FullSubcategory :=
  (coherentToQuasicoherentDerivedMinus X).asEquivalence

/-- The equivalence of [Stacks, Tag 0FDA] is an equivalence *of the canonical functor*: its
forward direction is `AlgebraicGeometry.coherentToQuasicoherentDerivedMinus`. -/
theorem coherentToQuasicoherentDerivedMinusEquivalence_functor [IsNoetherian X] :
    (coherentToQuasicoherentDerivedMinusEquivalence X).functor =
      coherentToQuasicoherentDerivedMinus X := rfl

end AlgebraicGeometry

end
