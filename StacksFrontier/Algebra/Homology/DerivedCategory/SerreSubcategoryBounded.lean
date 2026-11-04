module

public import Mathlib.CategoryTheory.Localization.Equivalence
public import Mathlib.CategoryTheory.Triangulated.LocalizingSubcategory
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedSerreInducedTStructure
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The bounded versions of `D(𝒜)/D_ℬ(𝒜) = D(𝒜/ℬ)`

Let `𝒜` be an abelian category, `ℬ ⊆ 𝒜` a Serre subcategory and `v : 𝒜 ⥤ 𝒜/ℬ` the quotient
functor, and assume `v` has a fully faithful left adjoint `u`. [Stacks, Tag 06XM] states that
`D(𝒜)/D_ℬ(𝒜) = D(𝒜/ℬ)` *and similarly for the bounded versions*. The unbounded statement is
`SerreClassLocalization.isLocalization_mapDerivedCategory_of_leftAdjoint` (in the namespace
`CategoryTheory.ObjectProperty`); this file proves the three bounded ones:

  `D⁺(𝒜)/D⁺_ℬ(𝒜) = D⁺(𝒜/ℬ)`, `D⁻(𝒜)/D⁻_ℬ(𝒜) = D⁻(𝒜/ℬ)`, `Dᵇ(𝒜)/Dᵇ_ℬ(𝒜) = Dᵇ(𝒜/ℬ)`.

Each says that the action of `v` on the bounded derived category (`DerivedCategory.Plus`,
`DerivedCategory.Minus`, `DerivedCategory.Bounded` of Mathlib, the full subcategories of `D(𝒜)`
of the objects with bounded below, above, or both, cohomology) is a localization functor for
the morphisms whose cone has all its cohomology objects in `ℬ`: the Verdier quotient of the
bounded derived category by its triangulated subcategory `D^?_ℬ(𝒜)`.

## Main definitions

* `CategoryTheory.Functor.mapDerivedCategoryMinus`,
  `CategoryTheory.Functor.mapDerivedCategoryBounded`: the action of an exact functor on the
  bounded above and on the bounded derived categories, next to the repository's
  `CategoryTheory.Functor.mapDerivedCategoryPlus`.

## Main results

* `DerivedCategoryB.isVerdierRightLocalizing_plus` and
  `DerivedCategoryB.isVerdierLeftLocalizing_minus`: for a weak Serre subcategory `ℬ`, `D⁺(𝒜)` is
  right `D_ℬ(𝒜)`-localizing and `D⁻(𝒜)` is left `D_ℬ(𝒜)`-localizing in the sense of Verdier.
* `SerreClassLocalization.isLocalization_mapDerivedCategoryPlus_of_leftAdjoint`,
  `..._mapDerivedCategoryMinus_of_leftAdjoint` and `..._mapDerivedCategoryBounded_of_leftAdjoint`
  (in the namespace `CategoryTheory.ObjectProperty`): the three bounded versions of
  [Stacks, Tag 06XM].

## Implementation notes

The bounded statements are deduced from the unbounded one; the source says only "similarly". A
triangulated subcategory `𝒜'` of `D(𝒜)` which is right or left localizing for `D_ℬ(𝒜)` in the
sense of Verdier has `𝒜'/(𝒜' ∩ D_ℬ(𝒜)) ⥤ D(𝒜)/D_ℬ(𝒜)` fully faithful
(`Mathlib.CategoryTheory.Triangulated.LocalizingSubcategory`), so as soon as the restricted
functor `𝒜' ⥤ D^?(𝒜/ℬ)` is essentially surjective it is a localization, by
`CategoryTheory.LocalizerMorphism.isLocalization_of_isLocalizedFullyFaithful`.

* The localizing conditions are the truncations: a morphism `X ⟶ Y` with `X ∈ D_ℬ(𝒜)` and
  `Y ≥ n` factors through `τ^{≥n}X`, which lies in `D⁺(𝒜) ∩ D_ℬ(𝒜)`; dually a morphism
  `X ⟶ Y` with `X ≤ n` and `Y ∈ D_ℬ(𝒜)` factors through `τ^{≤n}Y`.
* The bounded derived category is not right or left localizing inside `D(𝒜)` by a single
  truncation, so it is treated inside `D⁺(𝒜)`: there it is the bounded above part, which is left
  localizing for `D⁺_ℬ(𝒜)` by the same `τ^{≤n}` argument, `τ^{≤n}` preserving boundedness below.
  The result is transported along the identification of `Dᵇ(𝒜)` with that full subcategory of
  `D⁺(𝒜)`.
* Essential surjectivity uses `u`: an object of `D^?(𝒜/ℬ)` is represented by a complex `K`
  which is strictly bounded in the same way, `u` applied termwise to `K` is again strictly
  bounded, and `v u ≅ 𝟭` identifies its image with `K`.

## References

* [Stacks project, Tag 06XM](https://stacks.math.columbia.edu/tag/06XM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated

universe w w' v v' u u'

/-! ### Exact functors on the bounded above and bounded derived categories -/

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The action of an exact functor on the bounded above derived category: the restriction of
its action on the unbounded derived category, which preserves boundedness above. -/
def mapDerivedCategoryMinus : DerivedCategory.Minus C ⥤ DerivedCategory.Minus D :=
  DerivedCategory.TStructure.t.minus.lift (DerivedCategory.Minus.ι ⋙ F.mapDerivedCategory)
    (fun X ↦ by
      obtain ⟨n, hn⟩ := X.property
      have : X.obj.IsLE n := hn
      exact ⟨n, Stacks.Homology.isLE_mapDerivedCategory_obj F X.obj n⟩)

/-- The action of an exact functor on the bounded derived category: the restriction of its
action on the unbounded derived category, which preserves boundedness on both sides. -/
def mapDerivedCategoryBounded : DerivedCategory.Bounded C ⥤ DerivedCategory.Bounded D :=
  DerivedCategory.TStructure.t.bounded.lift (DerivedCategory.Bounded.ι ⋙ F.mapDerivedCategory)
    (fun X ↦ by
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := X.property
      have : X.obj.IsLE b := hb
      exact ⟨⟨a, F.isGE_obj_mapDerivedCategory X.obj a ha⟩,
        ⟨b, Stacks.Homology.isLE_mapDerivedCategory_obj F X.obj b⟩⟩)

end CategoryTheory.Functor

/-! ### The bounded derived categories are localizing for `D_ℬ(𝒜)` -/

namespace DerivedCategoryB

open DerivedCategory ObjectProperty WeakSerre

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  (B : ObjectProperty A) [B.IsWeakSerreClass]

/-- `D⁺(𝒜)` is right `D_ℬ(𝒜)`-localizing: a morphism `X ⟶ Y` with `X ∈ D_ℬ(𝒜)` and `Y ≥ n`
factors through `τ^{≥n}X ∈ D⁺(𝒜) ∩ D_ℬ(𝒜)`. -/
instance isVerdierRightLocalizing_plus :
    (TStructure.t : TStructure (DerivedCategory A)).plus.IsVerdierRightLocalizing
      (derivedCategoryB B) where
  fac {X Y} f hX hY := by
    obtain ⟨n, hn⟩ := hY
    have := hn
    exact ⟨(TStructure.t.truncGE n).obj X, (TStructure.t.truncGEπ n).app X,
      TStructure.t.descTruncGE f n, ⟨n, inferInstance⟩,
      derivedCategoryB_truncGE_obj B (isWeakSerre_of_isWeakSerreClass B) n X hX,
      TStructure.t.π_descTruncGE f n⟩

/-- `D⁻(𝒜)` is left `D_ℬ(𝒜)`-localizing: a morphism `X ⟶ Y` with `X ≤ n` and `Y ∈ D_ℬ(𝒜)`
factors through `τ^{≤n}Y ∈ D⁻(𝒜) ∩ D_ℬ(𝒜)`. -/
instance isVerdierLeftLocalizing_minus :
    (TStructure.t : TStructure (DerivedCategory A)).minus.IsVerdierLeftLocalizing
      (derivedCategoryB B) where
  fac {X Y} f hX hY := by
    obtain ⟨n, hn⟩ := hX
    have := hn
    exact ⟨(TStructure.t.truncLE n).obj Y, TStructure.t.liftTruncLE f n,
      (TStructure.t.truncLEι n).app Y, ⟨n, inferInstance⟩,
      derivedCategoryB_truncLT_obj B (isWeakSerre_of_isWeakSerreClass B) (n + 1) Y hY,
      TStructure.t.liftTruncLE_ι f n⟩

/-- Inside `D⁺(𝒜)`, the bounded above objects are left `D⁺_ℬ(𝒜)`-localizing: a morphism
`X ⟶ Y` of `D⁺(𝒜)` with `X ≤ n` and `Y ∈ D_ℬ(𝒜)` factors through `τ^{≤n}Y`, which is still
bounded below. -/
instance isVerdierLeftLocalizing_minus_inverseImage_plus :
    ((TStructure.t : TStructure (DerivedCategory A)).minus.inverseImage
      (Plus.ι (C := A))).IsVerdierLeftLocalizing ((derivedCategoryB B).inverseImage Plus.ι) where
  fac {X Y} f hX hY := by
    obtain ⟨n, hn⟩ := hX
    obtain ⟨m, hm⟩ := Y.property
    have : TStructure.t.IsLE X.obj n := hn
    have := hm
    let Z : Plus A := ⟨(TStructure.t.truncLE n).obj Y.obj, ⟨m, inferInstance⟩⟩
    exact ⟨Z, ObjectProperty.homMk (TStructure.t.liftTruncLE f.hom n),
      ObjectProperty.homMk ((TStructure.t.truncLEι n).app Y.obj),
      ⟨n, (inferInstance : TStructure.t.IsLE ((TStructure.t.truncLE n).obj Y.obj) n)⟩,
      derivedCategoryB_truncLT_obj B (isWeakSerre_of_isWeakSerreClass B) (n + 1) Y.obj hY,
      ObjectProperty.hom_ext _ (TStructure.t.liftTruncLE_ι f.hom n)⟩

end DerivedCategoryB

/-! ### The bounded versions of [Stacks, Tag 06XM] -/

namespace CategoryTheory.ObjectProperty.SerreClassLocalization

open DerivedCategory DerivedCategoryB

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  {u : D ⥤ C} [u.Full] [u.Faithful] (adj : u ⊣ L)

include adj in
/-- `v u ≅ 𝟭` read on the derived category: the image under `D(v)` of `u` applied termwise to a
complex `K` of `𝒜/ℬ` is `K`. -/
private noncomputable def mapDerivedCategoryObjQIso (K : CochainComplex D ℤ) :
    L.mapDerivedCategory.obj (Q.obj ((u.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≅
      Q.obj K :=
  have : u.Additive := adj.left_adjoint_additive
  L.mapDerivedCategoryFactors.app _ ≪≫ Q.mapIso
    ((NatIso.mapHomologicalComplex (asIso adj.unit) (ComplexShape.up ℤ)).symm.app K ≪≫
      (Functor.mapHomologicalComplexIdIso D (ComplexShape.up ℤ)).app K)

omit [HasDerivedCategory C] [HasDerivedCategory D] [PreservesFiniteLimits L]
  [PreservesFiniteColimits L] in
include adj in
private lemma isStrictlyGE_mapHomologicalComplex (K : CochainComplex D ℤ) (n : ℤ)
    [K.IsStrictlyGE n] :
    CochainComplex.IsStrictlyGE ((u.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n :=
  have : u.Additive := adj.left_adjoint_additive
  (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff K u n).2 inferInstance

omit [HasDerivedCategory C] [HasDerivedCategory D] [PreservesFiniteLimits L]
  [PreservesFiniteColimits L] in
include adj in
private lemma isStrictlyLE_mapHomologicalComplex (K : CochainComplex D ℤ) (n : ℤ)
    [K.IsStrictlyLE n] :
    CochainComplex.IsStrictlyLE ((u.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n :=
  have : u.Additive := adj.left_adjoint_additive
  (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff K u n).2 inferInstance

include adj in
private lemma essSurj_mapDerivedCategoryPlus : L.mapDerivedCategoryPlus.EssSurj where
  mem_essImage Y := by
    obtain ⟨n, hn⟩ := Y.property
    have := hn
    obtain ⟨K, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE Y.obj n
    have := isStrictlyGE_mapHomologicalComplex L adj K n
    exact ⟨⟨Q.obj ((u.mapHomologicalComplex (ComplexShape.up ℤ)).obj K), ⟨n, inferInstance⟩⟩,
      ⟨ObjectProperty.isoMk _ (mapDerivedCategoryObjQIso L adj K ≪≫ e.symm)⟩⟩

include adj in
private lemma essSurj_mapDerivedCategoryMinus : L.mapDerivedCategoryMinus.EssSurj where
  mem_essImage Y := by
    obtain ⟨n, hn⟩ := Y.property
    have := hn
    obtain ⟨K, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE Y.obj n
    have := isStrictlyLE_mapHomologicalComplex L adj K n
    exact ⟨⟨Q.obj ((u.mapHomologicalComplex (ComplexShape.up ℤ)).obj K), ⟨n, inferInstance⟩⟩,
      ⟨ObjectProperty.isoMk _ (mapDerivedCategoryObjQIso L adj K ≪≫ e.symm)⟩⟩

variable (P : ObjectProperty C) [P.IsSerreClass] [L.IsLocalization P.isoModSerre]

include adj in
/-- `D(v)` is a localization at the morphisms with cone in `D_ℬ(𝒜) = derivedCategoryB P`, which is
a triangulated subcategory closed under isomorphisms, [Stacks, Tag 06UQ]. -/
@[sga "6 IV 1.6" "special case"]
private lemma isLocalization_isTriangulated_derivedCategoryB :
    L.mapDerivedCategory.IsLocalization (derivedCategoryB P).trW ∧
      (derivedCategoryB P).IsTriangulated ∧ (derivedCategoryB P).IsClosedUnderIsomorphisms :=
  ⟨isLocalization_mapDerivedCategory_of_leftAdjoint L P adj,
    derivedCategoryB_isTriangulated P (WeakSerre.isWeakSerre_of_isWeakSerreClass P),
    derivedCategoryB_isClosedUnderIsomorphisms P (WeakSerre.isWeakSerre_of_isWeakSerreClass P)⟩

include adj in
/-- **[Stacks, Tag 06XM], bounded below version.** In the situation of
`isLocalization_mapDerivedCategory_of_leftAdjoint` — `L : 𝒜 ⥤ 𝒜/ℬ` the quotient by a Serre
subcategory `ℬ = P`, with a fully faithful left adjoint `u` — the induced functor
`D⁺(𝒜) ⥤ D⁺(𝒜/ℬ)` is a localization functor for the morphisms of `D⁺(𝒜)` whose cone lies in
`D⁺_ℬ(𝒜)`, i.e. `D⁺(𝒜)/D⁺_ℬ(𝒜) = D⁺(𝒜/ℬ)`. -/
@[stacks 06XM "bounded below version"]
public theorem isLocalization_mapDerivedCategoryPlus_of_leftAdjoint :
    L.mapDerivedCategoryPlus.IsLocalization
      ((derivedCategoryB P).inverseImage (Plus.ι (C := C))).trW := by
  obtain ⟨_, _, _⟩ := isLocalization_isTriangulated_derivedCategoryB L adj P
  have := essSurj_mapDerivedCategoryPlus L adj
  exact (TStructure.t.plus.triangulatedLocalizerMorphism
    (derivedCategoryB P)).isLocalization_of_isLocalizedFullyFaithful
      (L₂ := L.mapDerivedCategory) (F := Plus.ι) (Iso.refl _)

include adj in
/-- **[Stacks, Tag 06XM], bounded above version.** `D⁻(𝒜)/D⁻_ℬ(𝒜) = D⁻(𝒜/ℬ)`: the induced
functor `D⁻(𝒜) ⥤ D⁻(𝒜/ℬ)` is a localization functor for the morphisms of `D⁻(𝒜)` whose cone
lies in `D⁻_ℬ(𝒜)`. -/
@[stacks 06XM "bounded above version"]
public theorem isLocalization_mapDerivedCategoryMinus_of_leftAdjoint :
    L.mapDerivedCategoryMinus.IsLocalization
      ((derivedCategoryB P).inverseImage (Minus.ι (C := C))).trW := by
  obtain ⟨_, _, _⟩ := isLocalization_isTriangulated_derivedCategoryB L adj P
  have := essSurj_mapDerivedCategoryMinus L adj
  exact (TStructure.t.minus.triangulatedLocalizerMorphism
    (derivedCategoryB P)).isLocalization_of_isLocalizedFullyFaithful
      (L₂ := L.mapDerivedCategory) (F := Minus.ι) (Iso.refl _)

/-! #### The bounded version, through the bounded above part of `D⁺` -/

variable (C) in
/-- The bounded above objects of `D⁺(𝒜)`. -/
private abbrev minusPlus : ObjectProperty (Plus C) :=
  (TStructure.t : TStructure (DerivedCategory C)).minus.inverseImage (Plus.ι (C := C))

variable (C) in
/-- `Dᵇ(𝒜)` is the full subcategory of bounded above objects of `D⁺(𝒜)`. -/
private noncomputable def boundedEquivalence : (minusPlus C).FullSubcategory ≌ Bounded C where
  functor := TStructure.t.bounded.lift ((minusPlus C).ι ⋙ Plus.ι)
    (fun X ↦ ⟨X.obj.property, X.property⟩)
  inverse := (minusPlus C).lift (TStructure.t.plus.lift Bounded.ι (fun Y ↦ Y.property.1))
    (fun Y ↦ Y.property.2)
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- The action of `v` on the bounded above part of `D⁺`. -/
private noncomputable def mapMinusPlus :
    (minusPlus C).FullSubcategory ⥤ (minusPlus D).FullSubcategory :=
  (minusPlus D).lift ((minusPlus C).ι ⋙ L.mapDerivedCategoryPlus) (fun X ↦ by
    obtain ⟨n, hn⟩ := X.property
    have : X.obj.obj.IsLE n := hn
    exact ⟨n, Stacks.Homology.isLE_mapDerivedCategory_obj L X.obj.obj n⟩)

include adj in
private lemma essSurj_mapMinusPlus : (mapMinusPlus L).EssSurj where
  mem_essImage Y := by
    obtain ⟨a, ha⟩ := Y.obj.property
    obtain ⟨b, hb⟩ := Y.property
    have : Y.obj.obj.IsGE a := ha
    have : Y.obj.obj.IsLE b := hb
    obtain ⟨K, _, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE Y.obj.obj a b
    have := isStrictlyGE_mapHomologicalComplex L adj K a
    have := isStrictlyLE_mapHomologicalComplex L adj K b
    exact ⟨⟨⟨Q.obj ((u.mapHomologicalComplex (ComplexShape.up ℤ)).obj K), ⟨a, inferInstance⟩⟩,
      ⟨b, (inferInstance : (Q.obj ((u.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).IsLE b)⟩⟩,
      ⟨ObjectProperty.isoMk _ (ObjectProperty.isoMk _
        (mapDerivedCategoryObjQIso L adj K ≪≫ e.symm))⟩⟩

include adj in
/-- **[Stacks, Tag 06XM], bounded version.** `Dᵇ(𝒜)/Dᵇ_ℬ(𝒜) = Dᵇ(𝒜/ℬ)`: the induced functor
`Dᵇ(𝒜) ⥤ Dᵇ(𝒜/ℬ)` is a localization functor for the morphisms of `Dᵇ(𝒜)` whose cone lies in
`Dᵇ_ℬ(𝒜)`. -/
@[stacks 06XM "bounded version"]
public theorem isLocalization_mapDerivedCategoryBounded_of_leftAdjoint :
    L.mapDerivedCategoryBounded.IsLocalization
      ((derivedCategoryB P).inverseImage (Bounded.ι (C := C))).trW := by
  obtain ⟨_, _, _⟩ := isLocalization_isTriangulated_derivedCategoryB L adj P
  have := isLocalization_mapDerivedCategoryPlus_of_leftAdjoint L adj P
  have := essSurj_mapMinusPlus L adj
  have h₁ := ((minusPlus C).triangulatedLocalizerMorphism
    ((derivedCategoryB P).inverseImage Plus.ι)).isLocalization_of_isLocalizedFullyFaithful
      (L₂ := L.mapDerivedCategoryPlus) (L₁ := mapMinusPlus L) (F := (minusPlus D).ι) (Iso.refl _)
  have h₂ := Functor.IsLocalization.of_equivalence_target (mapMinusPlus L)
    ((((derivedCategoryB P).inverseImage Plus.ι).inverseImage (minusPlus C).ι).trW)
    (mapMinusPlus L ⋙ (boundedEquivalence D).functor) (boundedEquivalence D) (Iso.refl _)
  refine Functor.IsLocalization.of_equivalence_source
    (mapMinusPlus L ⋙ (boundedEquivalence D).functor)
    ((((derivedCategoryB P).inverseImage Plus.ι).inverseImage (minusPlus C).ι).trW) _ _
    (boundedEquivalence C) ?_ ?_ (Iso.refl _)
  · intro X Y f hf
    refine MorphismProperty.le_isoClosure _ _ ?_
    rw [trW_inverseImage_ι_iff] at hf
    have hf' : ((TStructure.t.minus ⊓ derivedCategoryB P).inverseImage Plus.ι).trW f.hom := hf
    rw [trW_inverseImage_ι_iff] at hf'
    exact (trW_inverseImage_ι_iff _ _ _).2
      (trW_monotone (fun Z h ↦ ⟨⟨h.1, h.2.1⟩, h.2.2⟩) _ hf')
  · intro X Y f hf
    rw [trW_inverseImage_ι_iff] at hf
    have : IsIso (L.mapDerivedCategory.map f.hom) :=
      Localization.inverts _ (derivedCategoryB P).trW _ (trW_monotone (fun _ h ↦ h.2) _ hf)
    have : IsIso (Bounded.ι.map (L.mapDerivedCategoryBounded.map f)) := this
    exact isIso_of_fully_faithful Bounded.ι _

end CategoryTheory.ObjectProperty.SerreClassLocalization
