module

public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.NoetherianExtension.Equivalence
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksCore.Tactic.StacksAttribute

/-!
# The derived category of coherent modules on a Noetherian scheme

Let `X` be a Noetherian scheme. The inclusion `Coh(𝒪_X) ⥤ Mod(𝒪_X)` of the coherent
`𝒪_X`-modules into all `𝒪_X`-modules is exact, so it induces a functor on derived categories.
Restricted to the bounded above complexes it lands in `D⁻_Coh(𝒪_X)`, the complexes of
`𝒪_X`-modules which are cohomologically bounded above and have coherent cohomology in every
degree, and restricted to the bounded complexes it lands in `D^b_Coh(𝒪_X)`. This file proves
that both restrictions are equivalences,
    `D⁻(Coh(𝒪_X)) ≌ D⁻_Coh(𝒪_X)` and `D^b(Coh(𝒪_X)) ≌ D^b_Coh(𝒪_X)`.

The proof is the one of the source. The inclusion factors through the quasi-coherent modules,
`Coh(𝒪_X) ⥤ QCoh(𝒪_X) ⥤ Mod(𝒪_X)`, and each of the two induced comparisons is known:
[Stacks, Tag 0FDA] says `D⁻(Coh(𝒪_X)) ⥤ D⁻_Coh(QCoh(𝒪_X))` is an equivalence, and
[Stacks, Tag 09T4] says the comparison `D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of [Stacks, Tag 06VT] is
an equivalence on a Noetherian scheme. The second is what identifies the two readings of
"coherent cohomology": a complex of quasi-coherent modules has coherent cohomology as a complex
of quasi-coherent modules exactly when its image has coherent cohomology as a complex of
`𝒪_X`-modules, because the inclusion `QCoh(𝒪_X) ⥤ Mod(𝒪_X)` does not change the underlying
module. The detour through `QCoh(𝒪_X)` cannot be avoided: coherence is *not* a Serre
subcategory condition in `Mod(𝒪_X)`, since a non-quasi-coherent submodule of `𝒪_X` need not be
coherent, and the criterion of [Stacks, Tag 0FCL] which [Stacks, Tag 0FDA] rests on is applied
inside `QCoh(𝒪_X)`.

The bounded case is the bounded above case restricted further: `D^b(Coh(𝒪_X))` is the full
subcategory of `D⁻(Coh(𝒪_X))` of the objects which are also bounded below, `D^b_Coh(𝒪_X)` is
the corresponding subcategory of `D⁻_Coh(𝒪_X)`, and the equivalence matches the two conditions
because it matches the cohomology.

## Main definitions

* `AlgebraicGeometry.coherentInModules` is coherence, read as a property of objects of
  `Mod(𝒪_X)`.
* `AlgebraicGeometry.coherentToModulesDerivedMinus` is the canonical functor
  `D⁻(Coh(𝒪_X)) ⥤ D⁻_Coh(𝒪_X)`, and
  `AlgebraicGeometry.coherentToModulesDerivedBounded` the canonical functor
  `D^b(Coh(𝒪_X)) ⥤ D^b_Coh(𝒪_X)`; both are derived functors of the inclusion
  `Coh(𝒪_X) ⥤ Mod(𝒪_X)`, as
  `AlgebraicGeometry.coherentToModulesDerivedMinus_comp_ι` and
  `AlgebraicGeometry.coherentToModulesDerivedBounded_comp_ι` record.

## Main results

* `AlgebraicGeometry.coherentToModulesDerivedMinus_isEquivalence` and
  `AlgebraicGeometry.coherentToModulesDerivedBounded_isEquivalence`:
  **[Stacks, Tag 0FDB]**, the two functors are equivalences.
* `AlgebraicGeometry.coherentToModulesDerivedMinusEquivalence` and
  `AlgebraicGeometry.coherentToModulesDerivedBoundedEquivalence` package them as equivalences
  of categories, with the canonical functors as their forward directions.

## Implementation notes

`Mod(𝒪_X)` is spelled `SheafOfModules X.ringCatSheaf`, the spelling [Stacks, Tag 06VT],
[Stacks, Tag 09T4] and [Stacks, Tag 0FDA] are stated at, rather than the definitionally equal
`AlgebraicGeometry.Scheme.Modules X`, which is a `def` and through which the `Abelian` instance
of the full subcategory of coherent objects is not found.

`CategoryTheory.HasDerivedCategory.standard` is installed as a local instance of raised
priority, as in the file proving [Stacks, Tag 09T4]: that is the model both inputs are stated
at, and the import closure carries locally small models at universe `u` as global instances, so
without the raised priority instance search has two models to choose between. Every
identification below goes through the universal property of the localization or through a
functor isomorphism; no two `HasDerivedCategory` terms are ever compared.

The three general lemmas in `CategoryTheory.Functor` and `DerivedCategoryB` are stated for a
*faithful* exact additive functor. `CategoryTheory.Functor.isLE_mapDerivedCategory_obj_iff`
already does the corresponding job for an exact additive *equivalence*; the inclusion
`Coh(𝒪_X) ⥤ Mod(𝒪_X)` is not one, so the general forms are added alongside and that lemma's
statement is untouched.

## References

* [Stacks Project, Tag 0FDB](https://stacks.math.columbia.edu/tag/0FDB)
* [Stacks Project, Tag 0FDA](https://stacks.math.columbia.edu/tag/0FDA)
* [Stacks Project, Tag 0FCL](https://stacks.math.columbia.edu/tag/0FCL)
* [Stacks Project, Tag 09T4](https://stacks.math.columbia.edu/tag/09T4)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.QuasicoherentDerived

universe v₁ v₂ u₁ u₂ w₁ w₂ u

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]

/-- **A faithful exact functor neither creates nor destroys vanishing of cohomology.** For an
exact additive faithful `F : C ⥤ D`, the complex `F(K)` has vanishing `n`-th cohomology exactly
when `K` does, because `Hⁿ(F K) ≅ F(Hⁿ K)` and a faithful additive functor reflects zero
objects. -/
lemma isZero_homologyFunctor_obj_mapDerivedCategory_obj_iff (F : C ⥤ D) [F.Additive]
    [F.Faithful] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory C) (n : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor D n).obj (F.mapDerivedCategory.obj K)) ↔
      IsZero ((DerivedCategory.homologyFunctor C n).obj K) := by
  refine ⟨fun h => ?_, fun h =>
    (F.map_isZero h).of_iso ((F.mapDerivedCategoryHomologyIso n).app K)⟩
  refine (IsZero.iff_id_eq_zero _).2 (F.map_injective ?_)
  simpa using (IsZero.iff_id_eq_zero _).mp
    (h.of_iso ((F.mapDerivedCategoryHomologyIso n).app K).symm)

end CategoryTheory.Functor

namespace DerivedCategoryB

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]

/-- A faithful exact additive functor both preserves and reflects cohomological boundedness
above. -/
lemma isBoundedAbove_mapDerivedCategory_obj_iff (F : C ⥤ D) [F.Additive] [F.Faithful]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (K : DerivedCategory C) :
    IsBoundedAbove (F.mapDerivedCategory.obj K) ↔ IsBoundedAbove K :=
  exists_congr fun _ => forall₂_congr fun i _ =>
    F.isZero_homologyFunctor_obj_mapDerivedCategory_obj_iff K i

/-- A faithful exact additive functor both preserves and reflects cohomological boundedness
below. -/
lemma isBoundedBelow_mapDerivedCategory_obj_iff (F : C ⥤ D) [F.Additive] [F.Faithful]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (K : DerivedCategory C) :
    IsBoundedBelow (F.mapDerivedCategory.obj K) ↔ IsBoundedBelow K :=
  exists_congr fun _ => forall₂_congr fun i _ =>
    F.isZero_homologyFunctor_obj_mapDerivedCategory_obj_iff K i

end DerivedCategoryB

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : Scheme.{u})

/-! ### The inclusion of the coherent modules into all modules -/

/-- Coherence, read as a property of objects of the category `Mod(𝒪_X)` of all `𝒪_X`-modules.
The full subcategory it cuts out is `Coh(𝒪_X)`, i.e.
`AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf`. -/
abbrev coherentInModules : ObjectProperty (SheafOfModules.{u} X.ringCatSheaf) :=
  fun M => M.IsCoherent

/-- The inclusion `Coh(𝒪_X) ⥤ Mod(𝒪_X)` is the inclusion `Coh(𝒪_X) ⥤ QCoh(𝒪_X)` of
[Stacks, Tag 02MP] followed by the inclusion of the quasi-coherent modules: all three functors
leave the underlying `𝒪_X`-module and the morphisms between them alone. -/
theorem coherentInModules_ι :
    (coherentInModules X).ι =
      coherentToQuasicoherent X ⋙ (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι := rfl

/-- The derived functor of the inclusion `Coh(𝒪_X) ⥤ Mod(𝒪_X)` is the derived functor of
`Coh(𝒪_X) ⥤ QCoh(𝒪_X)` followed by the derived functor of `QCoh(𝒪_X) ⥤ Mod(𝒪_X)`, because
`D(-)` is compatible with composition of exact functors. -/
def coherentDerivedToModulesIso [IsLocallyNoetherian X] :
    (coherentToQuasicoherent X).mapDerivedCategory ⋙
        (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory ≅
      (coherentInModules X).ι.mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso (Iso.refl _)

/-- A complex of coherent `𝒪_X`-modules has coherent cohomology sheaves: the inclusion
`Coh(𝒪_X) ⥤ Mod(𝒪_X)` is exact, so it commutes with cohomology. -/
lemma derivedCategoryB_coherentInModules_obj
    (K : DerivedCategory (SheafOfModules.CoherentModules X.ringCatSheaf)) :
    DerivedCategoryB.derivedCategoryB (coherentInModules X)
      ((coherentInModules X).ι.mapDerivedCategory.obj K) := fun n =>
  (coherentInModules X).prop_of_iso
    (((coherentInModules X).ι.mapDerivedCategoryHomologyIso n).app K).symm
    ((DerivedCategory.homologyFunctor _ n).obj K).2

/-! ### The derived inclusion of the quasi-coherent modules on a Noetherian scheme -/

/-- **[Stacks, Tag 09T4].** On a Noetherian scheme the derived functor of the inclusion
`QCoh(𝒪_X) ⥤ Mod(𝒪_X)` is full: it is the comparison functor of [Stacks, Tag 06VT], which is
then an equivalence, followed by the fully faithful inclusion of `D_QCoh(𝒪_X)`. -/
instance full_quasicoherentι_mapDerivedCategory [IsNoetherian X] :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory.Full :=
  letI := Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_isNoetherian X
  Functor.Full.of_iso (derivedQuasicoherentComparisonCompι.{u + 1} X)

/-- **[Stacks, Tag 09T4].** On a Noetherian scheme the derived functor of the inclusion
`QCoh(𝒪_X) ⥤ Mod(𝒪_X)` is faithful, for the same reason as
`AlgebraicGeometry.full_quasicoherentι_mapDerivedCategory`. -/
instance faithful_quasicoherentι_mapDerivedCategory [IsNoetherian X] :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory.Faithful :=
  letI := Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_isNoetherian X
  Functor.Faithful.of_iso (derivedQuasicoherentComparisonCompι.{u + 1} X)

/-- The functor `D⁻(Coh(𝒪_X)) ⥤ D(𝒪_X)` underlying [Stacks, Tag 0FDB] is the functor of
[Stacks, Tag 0FDA], before its target is cut down, followed by the derived inclusion of the
quasi-coherent modules. -/
def coherentDerivedMinusToModulesIso [IsLocallyNoetherian X] :
    coherentDerivedMinusInclusion X ⋙
        (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory ≅
      DerivedCategory.Minus.ι ⋙ (coherentInModules X).ι.mapDerivedCategory :=
  Functor.isoWhiskerLeft DerivedCategory.Minus.ι (coherentDerivedToModulesIso X)

/-- **Stacks Project, Tags 0FCL and 09T4.** The derived inclusion of the bounded above complexes
of coherent modules into `D(𝒪_X)` is full: it is the fully faithful functor of
[Stacks, Tag 0FDA] followed by the derived inclusion of the quasi-coherent modules, which is
fully faithful by [Stacks, Tag 09T4]. -/
instance full_minusι_comp_coherentInModulesι [IsNoetherian X] :
    (DerivedCategory.Minus.ι (C := SheafOfModules.CoherentModules X.ringCatSheaf) ⋙
      (coherentInModules X).ι.mapDerivedCategory).Full :=
  Functor.Full.of_iso (coherentDerivedMinusToModulesIso X)

/-- **Stacks Project, Tags 0FCL and 09T4.** The derived inclusion of the bounded above complexes
of coherent modules into `D(𝒪_X)` is faithful, for the same reason as
`AlgebraicGeometry.full_minusι_comp_coherentInModulesι`. -/
instance faithful_minusι_comp_coherentInModulesι [IsNoetherian X] :
    (DerivedCategory.Minus.ι (C := SheafOfModules.CoherentModules X.ringCatSheaf) ⋙
      (coherentInModules X).ι.mapDerivedCategory).Faithful :=
  Functor.Faithful.of_iso (coherentDerivedMinusToModulesIso X)

/-! ### The bounded above case -/

/-- **Stacks Project, Tag 0FDB.** The canonical functor `D⁻(Coh(𝒪_X)) ⥤ D⁻_Coh(𝒪_X)`: the
derived functor of the inclusion `Coh(𝒪_X) ⥤ Mod(𝒪_X)`, restricted to the bounded above
complexes and corestricted to the complexes of `𝒪_X`-modules which are bounded above with
coherent cohomology, where it lands. -/
def coherentToModulesDerivedMinus :
    DerivedCategory.Minus (SheafOfModules.CoherentModules X.ringCatSheaf) ⥤
      (DerivedCategoryB.derivedCategoryBMinus (coherentInModules X)).FullSubcategory :=
  (DerivedCategoryB.derivedCategoryBMinus (coherentInModules X)).lift
    (DerivedCategory.Minus.ι ⋙ (coherentInModules X).ι.mapDerivedCategory)
    fun K => ⟨(DerivedCategoryB.isBoundedAbove_mapDerivedCategory_obj_iff _ K.obj).2
        ((DerivedCategoryB.isBoundedAbove_iff_exists_isLE K.obj).2 K.property),
      derivedCategoryB_coherentInModules_obj X K.obj⟩

/-- The functor of [Stacks, Tag 0FDB] *is* the derived functor of the inclusion
`Coh(𝒪_X) ⥤ Mod(𝒪_X)`: forgetting the boundedness and coherence conditions on its target
returns the inclusion of the bounded above complexes followed by that derived functor. -/
theorem coherentToModulesDerivedMinus_comp_ι :
    coherentToModulesDerivedMinus X ⋙
        (DerivedCategoryB.derivedCategoryBMinus (coherentInModules X)).ι =
      DerivedCategory.Minus.ι ⋙ (coherentInModules X).ι.mapDerivedCategory := rfl

/-- The functor of [Stacks, Tag 0FDB] is full, because it is so after composing with the fully
faithful inclusion of `D⁻_Coh(𝒪_X)` into `D(𝒪_X)`. -/
instance full_coherentToModulesDerivedMinus [IsNoetherian X] :
    (coherentToModulesDerivedMinus X).Full where
  map_surjective f := by
    obtain ⟨g, hg⟩ := (DerivedCategory.Minus.ι
      (C := SheafOfModules.CoherentModules X.ringCatSheaf) ⋙
        (coherentInModules X).ι.mapDerivedCategory).map_surjective f.hom
    exact ⟨g, ObjectProperty.hom_ext _ hg⟩

/-- The functor of [Stacks, Tag 0FDB] is faithful, because it is so after composing with the
inclusion of `D⁻_Coh(𝒪_X)` into `D(𝒪_X)`. -/
instance faithful_coherentToModulesDerivedMinus [IsNoetherian X] :
    (coherentToModulesDerivedMinus X).Faithful where
  map_injective h := (DerivedCategory.Minus.ι
    (C := SheafOfModules.CoherentModules X.ringCatSheaf) ⋙
      (coherentInModules X).ι.mapDerivedCategory).map_injective (congrArg (fun q => q.hom) h)

/-- **The essential surjectivity of the functor of [Stacks, Tag 0FDB], as the source proves
it.** Let `K` be a bounded above complex of `𝒪_X`-modules with coherent cohomology. Coherent
modules are quasi-coherent, so `K` lies in `D_QCoh(𝒪_X)`, and by [Stacks, Tag 09T4] it is the
image of a complex `L` of quasi-coherent modules. The inclusion `QCoh(𝒪_X) ⥤ Mod(𝒪_X)` is
exact and does not change the underlying module, so `L` is itself bounded above with coherent
cohomology; by [Stacks, Tag 0FDA] it is in turn the image of a bounded above complex of
coherent modules. -/
instance essSurj_coherentToModulesDerivedMinus [IsNoetherian X] :
    (coherentToModulesDerivedMinus X).EssSurj where
  mem_essImage K := by
    have := Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_isNoetherian X
    have hQ : DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf) K.obj := fun n =>
      have : ((DerivedCategory.homologyFunctor _ n).obj K.obj).IsCoherent := K.property.2 n
      isQuasicoherent_of_isCoherent _
    set L := (derivedQuasicoherentComparison.{u + 1} X).objPreimage ⟨K.obj, hQ⟩
    have e₀ : (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory.obj L ≅
        K.obj :=
      ((derivedQuasicoherentComparisonCompι.{u + 1} X).app L).symm ≪≫
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.mapIso
            ((derivedQuasicoherentComparison.{u + 1} X).objObjPreimageIso ⟨K.obj, hQ⟩)
    have hLmem : DerivedCategoryB.derivedCategoryBMinus (coherentInQuasicoherent X) L := by
      refine ⟨(DerivedCategoryB.isBoundedAbove_mapDerivedCategory_obj_iff _ L).1
        (DerivedCategoryB.isBoundedAbove_of_iso e₀.symm K.property.1), fun n => ?_⟩
      exact (coherentInModules X).prop_of_iso
        (((DerivedCategory.homologyFunctor _ n).mapIso e₀).symm ≪≫
          ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategoryHomologyIso n).app L)
        (K.property.2 n)
    set Y := (coherentToQuasicoherentDerivedMinus X).objPreimage ⟨L, hLmem⟩
    refine ⟨Y, ⟨ObjectProperty.isoMk _ (?_ : _ ≅ K.obj)⟩⟩
    refine ((coherentDerivedMinusToModulesIso X).app Y).symm ≪≫ ?_
    refine (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapDerivedCategory.mapIso ?_ ≪≫ e₀
    exact (DerivedCategoryB.derivedCategoryBMinus (coherentInQuasicoherent X)).ι.mapIso
      ((coherentToQuasicoherentDerivedMinus X).objObjPreimageIso ⟨L, hLmem⟩)

/-- **Stacks Project, Tag 0FDB.** On a Noetherian scheme the canonical functor
`D⁻(Coh(𝒪_X)) ⥤ D⁻_Coh(𝒪_X)` is an equivalence: the bounded above derived category of the
coherent `𝒪_X`-modules is the full subcategory of `D(𝒪_X)` of the complexes which are
cohomologically bounded above with coherent cohomology sheaves. -/
@[stacks 0FDB "bounded above", sga "6 II 2.2.2.1" "more general"]
instance coherentToModulesDerivedMinus_isEquivalence [IsNoetherian X] :
    (coherentToModulesDerivedMinus X).IsEquivalence := {}

/-- **Stacks Project, Tag 0FDB**, the bounded above case as an equivalence of categories:
`D⁻(Coh(𝒪_X)) ≌ D⁻_Coh(𝒪_X)` on a Noetherian scheme. Its forward functor is the canonical one,
by `AlgebraicGeometry.coherentToModulesDerivedMinusEquivalence_functor`. -/
def coherentToModulesDerivedMinusEquivalence [IsNoetherian X] :
    DerivedCategory.Minus (SheafOfModules.CoherentModules X.ringCatSheaf) ≌
      (DerivedCategoryB.derivedCategoryBMinus (coherentInModules X)).FullSubcategory :=
  (coherentToModulesDerivedMinus X).asEquivalence

/-- The bounded above equivalence of [Stacks, Tag 0FDB] is an equivalence *of the canonical
functor*: its forward direction is
`AlgebraicGeometry.coherentToModulesDerivedMinus`. -/
theorem coherentToModulesDerivedMinusEquivalence_functor [IsNoetherian X] :
    (coherentToModulesDerivedMinusEquivalence X).functor =
      coherentToModulesDerivedMinus X := rfl

/-! ### The bounded case -/

/-- A bounded object of `D(Coh(𝒪_X))` is bounded above. -/
theorem coherentBounded_le_minus :
    (DerivedCategory.TStructure.t
        (C := SheafOfModules.CoherentModules X.ringCatSheaf)).bounded ≤
      (DerivedCategory.TStructure.t
        (C := SheafOfModules.CoherentModules X.ringCatSheaf)).minus :=
  fun _ hK => hK.2

/-- **Stacks Project, Tags 0FCL and 09T4.** The derived inclusion of the bounded complexes of
coherent modules into `D(𝒪_X)` is full: it is the inclusion `D^b(Coh(𝒪_X)) ⥤ D⁻(Coh(𝒪_X))`
followed by the fully faithful derived inclusion of the bounded above complexes. -/
instance full_boundedι_comp_coherentInModulesι [IsNoetherian X] :
    (DerivedCategory.Bounded.ι (C := SheafOfModules.CoherentModules X.ringCatSheaf) ⋙
      (coherentInModules X).ι.mapDerivedCategory).Full :=
  inferInstanceAs (ObjectProperty.ιOfLE (coherentBounded_le_minus X) ⋙
    (DerivedCategory.Minus.ι ⋙ (coherentInModules X).ι.mapDerivedCategory)).Full

/-- **Stacks Project, Tags 0FCL and 09T4.** The derived inclusion of the bounded complexes of
coherent modules into `D(𝒪_X)` is faithful, for the same reason as
`AlgebraicGeometry.full_boundedι_comp_coherentInModulesι`. -/
instance faithful_boundedι_comp_coherentInModulesι [IsNoetherian X] :
    (DerivedCategory.Bounded.ι (C := SheafOfModules.CoherentModules X.ringCatSheaf) ⋙
      (coherentInModules X).ι.mapDerivedCategory).Faithful :=
  inferInstanceAs (ObjectProperty.ιOfLE (coherentBounded_le_minus X) ⋙
    (DerivedCategory.Minus.ι ⋙ (coherentInModules X).ι.mapDerivedCategory)).Faithful

/-- **Stacks Project, Tag 0FDB.** The canonical functor `D^b(Coh(𝒪_X)) ⥤ D^b_Coh(𝒪_X)`: the
derived functor of the inclusion `Coh(𝒪_X) ⥤ Mod(𝒪_X)`, restricted to the bounded complexes
and corestricted to the complexes of `𝒪_X`-modules which are bounded with coherent cohomology,
where it lands. -/
def coherentToModulesDerivedBounded :
    DerivedCategory.Bounded (SheafOfModules.CoherentModules X.ringCatSheaf) ⥤
      (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).FullSubcategory :=
  (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).lift
    (DerivedCategory.Bounded.ι ⋙ (coherentInModules X).ι.mapDerivedCategory)
    fun K => ⟨⟨(DerivedCategoryB.isBoundedBelow_mapDerivedCategory_obj_iff _ K.obj).2
          ((DerivedCategoryB.isBoundedBelow_iff_exists_isGE K.obj).2 K.property.1),
        (DerivedCategoryB.isBoundedAbove_mapDerivedCategory_obj_iff _ K.obj).2
          ((DerivedCategoryB.isBoundedAbove_iff_exists_isLE K.obj).2 K.property.2)⟩,
      derivedCategoryB_coherentInModules_obj X K.obj⟩

/-- The bounded functor of [Stacks, Tag 0FDB] *is* the derived functor of the inclusion
`Coh(𝒪_X) ⥤ Mod(𝒪_X)`: forgetting the boundedness and coherence conditions on its target
returns the inclusion of the bounded complexes followed by that derived functor. -/
theorem coherentToModulesDerivedBounded_comp_ι :
    coherentToModulesDerivedBounded X ⋙
        (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).ι =
      DerivedCategory.Bounded.ι ⋙ (coherentInModules X).ι.mapDerivedCategory := rfl

/-- The bounded functor of [Stacks, Tag 0FDB] is full, because it is so after composing with
the fully faithful inclusion of `D^b_Coh(𝒪_X)` into `D(𝒪_X)`. -/
instance full_coherentToModulesDerivedBounded [IsNoetherian X] :
    (coherentToModulesDerivedBounded X).Full where
  map_surjective f := by
    obtain ⟨g, hg⟩ := (DerivedCategory.Bounded.ι
      (C := SheafOfModules.CoherentModules X.ringCatSheaf) ⋙
        (coherentInModules X).ι.mapDerivedCategory).map_surjective f.hom
    exact ⟨g, ObjectProperty.hom_ext _ hg⟩

/-- The bounded functor of [Stacks, Tag 0FDB] is faithful, because it is so after composing
with the inclusion of `D^b_Coh(𝒪_X)` into `D(𝒪_X)`. -/
instance faithful_coherentToModulesDerivedBounded [IsNoetherian X] :
    (coherentToModulesDerivedBounded X).Faithful where
  map_injective h := (DerivedCategory.Bounded.ι
    (C := SheafOfModules.CoherentModules X.ringCatSheaf) ⋙
      (coherentInModules X).ι.mapDerivedCategory).map_injective (congrArg (fun q => q.hom) h)

/-- **The bounded case follows from the bounded above case**, as in the source: a bounded
complex of `𝒪_X`-modules with coherent cohomology is in particular bounded above, so it is the
image of a bounded above complex of coherent modules, and that complex is bounded below too
because the inclusion `Coh(𝒪_X) ⥤ Mod(𝒪_X)` is exact and faithful, hence reflects vanishing of
cohomology. -/
instance essSurj_coherentToModulesDerivedBounded [IsNoetherian X] :
    (coherentToModulesDerivedBounded X).EssSurj where
  mem_essImage K := by
    set Km : (DerivedCategoryB.derivedCategoryBMinus (coherentInModules X)).FullSubcategory :=
      ⟨K.obj, K.property.1.2, K.property.2⟩
    set Y := (coherentToModulesDerivedMinus X).objPreimage Km
    have e : (coherentInModules X).ι.mapDerivedCategory.obj Y.obj ≅ K.obj :=
      (DerivedCategoryB.derivedCategoryBMinus (coherentInModules X)).ι.mapIso
        ((coherentToModulesDerivedMinus X).objObjPreimageIso Km)
    have hb : DerivedCategoryB.IsBoundedBelow Y.obj :=
      (DerivedCategoryB.isBoundedBelow_mapDerivedCategory_obj_iff _ Y.obj).1
        (DerivedCategoryB.isBoundedBelow_of_iso e.symm K.property.1.1)
    exact ⟨⟨Y.obj, (DerivedCategoryB.isBoundedBelow_iff_exists_isGE Y.obj).1 hb, Y.property⟩,
      ⟨ObjectProperty.isoMk _ e⟩⟩

/-- **Stacks Project, Tag 0FDB.** On a Noetherian scheme the canonical functor
`D^b(Coh(𝒪_X)) ⥤ D^b_Coh(𝒪_X)` is an equivalence: the bounded derived category of the coherent
`𝒪_X`-modules is the full subcategory of `D(𝒪_X)` of the complexes which are cohomologically
bounded with coherent cohomology sheaves. -/
@[stacks 0FDB "bounded", sga "6 II 2.2.2.1"]
instance coherentToModulesDerivedBounded_isEquivalence [IsNoetherian X] :
    (coherentToModulesDerivedBounded X).IsEquivalence := {}

/-- **Stacks Project, Tag 0FDB**, the bounded case as an equivalence of categories:
`D^b(Coh(𝒪_X)) ≌ D^b_Coh(𝒪_X)` on a Noetherian scheme. Its forward functor is the canonical
one, by `AlgebraicGeometry.coherentToModulesDerivedBoundedEquivalence_functor`. -/
def coherentToModulesDerivedBoundedEquivalence [IsNoetherian X] :
    DerivedCategory.Bounded (SheafOfModules.CoherentModules X.ringCatSheaf) ≌
      (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).FullSubcategory :=
  (coherentToModulesDerivedBounded X).asEquivalence

/-- The bounded equivalence of [Stacks, Tag 0FDB] is an equivalence *of the canonical functor*:
its forward direction is `AlgebraicGeometry.coherentToModulesDerivedBounded`. -/
theorem coherentToModulesDerivedBoundedEquivalence_functor [IsNoetherian X] :
    (coherentToModulesDerivedBoundedEquivalence X).functor =
      coherentToModulesDerivedBounded X := rfl

end AlgebraicGeometry

end
