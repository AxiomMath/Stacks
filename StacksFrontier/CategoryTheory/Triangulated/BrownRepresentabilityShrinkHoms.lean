module

public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Localization.Triangulated
public import StacksFrontier.CategoryTheory.Triangulated.BrownRepresentability
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
public import StacksFrontier.CategoryTheory.Triangulated.Generators

/-!
# Brown representability for locally small triangulated categories

Brown representability (`exists_isTriangulated_rightAdjoint_of_compactlyGenerated`) asks for
`HasCoproducts.{v}` on a category whose morphisms live in `Type v`. That hypothesis fails for the
categories one actually wants to apply it to: `HasDerivedCategory.standard` places the morphisms of
a derived category one universe *above* its objects, so coproducts indexed by the morphism universe
do not exist, and no amount of rephrasing produces them.

This file removes the obstruction. If `C` is merely `LocallySmall.{u}` — its `Hom` types are
*equivalent to* types in `Type u`, which is what derived categories satisfy — then
`CategoryTheory.ShrinkHoms C` is a genuinely `Type u`-enriched category equivalent to `C`, and
`HasCoproducts.{u} C` transports to it. The triangulated structure transports as well, because
`ShrinkHoms.equivalence` is a localization of `C` at `MorphismProperty.isomorphisms C` and the
isomorphisms have a left calculus of fractions compatible with the triangulation. Brown
representability applies to the shrunk functor, and the resulting adjunction is transported back
along `Functor.isLeftAdjoint_comp_iff_left` and `Functor.isLeftAdjoint_comp_iff_right`.

The payoff is `isLeftAdjoint_of_compact_generator`: an exact, coproduct-preserving functor out of a
triangulated category with a compact weak generator has a right adjoint, assuming only
`LocallySmall.{u}` and `HasCoproducts.{u}` at the *object* universe.
`isLeftAdjoint_lift_of_compact_generator` is the version for a functor restricted to triangulated
full subcategories, which is the shape in which derived-category applications arise.

## Main results

* `CategoryTheory.Pretriangulated.isLeftAdjoint_of_compact_generator` — an exact,
  coproduct-preserving functor out of a locally small triangulated category with a compact weak
  generator is a left adjoint.
* `CategoryTheory.Pretriangulated.isLeftAdjoint_lift_of_compact_generator` — the same for the lift
  of a functor to triangulated full subcategories of the source and target.
* `CategoryTheory.Pretriangulated.preservesCoproducts_preadditiveCoyoneda_of_isCompactObject` —
  compactness of `K`, read as preservation of coproducts by `Hom(K, -)`.
* `CategoryTheory.Pretriangulated.isomorphisms_hasLeftCalculusOfFractions` and
  `CategoryTheory.Pretriangulated.isomorphisms_isCompatibleWithTriangulation` — the isomorphisms
  form a left calculus of fractions compatible with the triangulation, which is what makes an
  equivalence a triangulated localization.
* `CategoryTheory.Pretriangulated.isWeakTriangulatedGenerator_obj_of_equivalence` — a weak
  generator is carried to a weak generator by an equivalence commuting with the shift.

## References

* [Stacks Project, Tag 0A8G](https://stacks.math.columbia.edu/tag/0A8G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty
open Opposite
open scoped ZeroObject

universe u₁ u₂ u₃ v₁ v₂

namespace CategoryTheory.Pretriangulated

/-- The isomorphisms of any category have a left calculus of fractions: a left fraction with
invertible denominator `s` is equivalent to the honest morphism `s⁻¹ ≫ f`, and two morphisms
agreeing after precomposition with an isomorphism already agree. -/
theorem isomorphisms_hasLeftCalculusOfFractions
    (C : Type u₁) [Category.{v₁} C] :
    (MorphismProperty.isomorphisms C).HasLeftCalculusOfFractions := by
  constructor
  · intro X Y fraction
    have : IsIso fraction.s := fraction.hs
    exact ⟨MorphismProperty.LeftFraction.mk (inv fraction.s ≫ fraction.f)
      (𝟙 Y) inferInstance, by simp⟩
  · intro X' X Y first second denominator hdenominator equality
    have : IsIso denominator := hdenominator
    exact ⟨Y, 𝟙 Y, inferInstance, by simpa using (cancel_epi denominator).1 equality⟩

/-- The isomorphisms of a category with a shift are stable under the shift: a shift functor is an
equivalence, so it both preserves and reflects isomorphisms. -/
theorem isomorphisms_isCompatibleWithShift (C : Type u₁) [Category.{v₁} C]
    [HasShift C ℤ] :
    (MorphismProperty.isomorphisms C).IsCompatibleWithShift ℤ := by
  constructor
  intro n
  ext X Y morphism
  change IsIso ((shiftFunctor C n).map morphism) ↔ IsIso morphism
  constructor
  · intro h
    have := h
    exact isIso_of_reflects_iso morphism (shiftFunctor C n)
  · intro h
    have := h
    infer_instance

/-- The isomorphisms of a pretriangulated category are compatible with the triangulation: axiom
TR3 completes a commuting square between distinguished triangles, and the third component of the
resulting morphism is an isomorphism as soon as the first two are. -/
theorem isomorphisms_isCompatibleWithTriangulation
    (C : Type u₁) [Category.{v₁} C] [HasShift C ℤ] [Preadditive C]
    [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] :
    (MorphismProperty.isomorphisms C).IsCompatibleWithTriangulation := by
  let := isomorphisms_isCompatibleWithShift C
  constructor
  intro first second hfirst hsecond firstMap secondMap hfirstMap hsecondMap equality
  let morphism := completeDistinguishedTriangleMorphism first second hfirst hsecond
    firstMap secondMap equality
  exact ⟨morphism.hom₃, isIso₃_of_isIso₁₂ morphism hfirst hsecond hfirstMap hsecondMap,
    morphism.comm₂, morphism.comm₃⟩

/-- An equivalence commuting with the shift carries a weak triangulated generator to a weak
triangulated generator. Fullness and faithfulness turn the vanishing condition on `C` for the
preimage of an object into the vanishing condition on `D` for the object itself. -/
theorem isWeakTriangulatedGenerator_obj_of_equivalence
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasShift C ℤ] [HasShift D ℤ]
    (equivalence : C ≌ D) [equivalence.functor.CommShift ℤ]
    [equivalence.functor.PreservesZeroMorphisms] (generator : C)
    (hgenerator : (ObjectProperty.singleton generator).IsWeakTriangulatedGenerator) :
    (ObjectProperty.singleton (equivalence.functor.obj generator)).IsWeakTriangulatedGenerator := by
  intro target htarget
  have horthogonal : ((ObjectProperty.singleton generator).shiftClosure ℤ).rightOrthogonal
      (equivalence.inverse.obj target) := by
    intro source morphism hsource
    obtain ⟨object, shift, iso, hobject⟩ :=
      (ObjectProperty.prop_shiftClosure_iff (ObjectProperty.singleton generator) source).1 hsource
    have equality : object = generator :=
      (ObjectProperty.singleton_iff generator object).1 hobject |>.symm
    subst object
    have hsource' : (ObjectProperty.singleton (equivalence.functor.obj generator)).shiftClosure ℤ
        (equivalence.functor.obj source) :=
      (ObjectProperty.prop_shiftClosure_iff _ _).2
        ⟨equivalence.functor.obj generator, shift, equivalence.functor.mapIso iso ≪≫
          (equivalence.functor.commShiftIso shift).app generator, by simp⟩
    apply equivalence.functor.map_injective
    exact (cancel_mono (equivalence.counitIso.hom.app target)).1 (by simpa using
      (htarget (equivalence.functor.map morphism ≫ equivalence.counitIso.hom.app target) hsource'))
  exact IsZero.of_iso (Functor.map_isZero equivalence.functor (hgenerator _ horthogonal))
    (equivalence.counitIso.app target).symm

/-- An element of the vertex of a colimit cocone of abelian groups lies in a subgroup as soon as
the image of every leg does: the corestrictions of the legs to the subgroup form a cocone, and the
induced map followed by the inclusion is the identity. -/
theorem mem_addSubgroup_of_isColimit {J : Type u₁} [Category.{v₁} J]
    {diagram : J ⥤ AddCommGrpCat.{v₂}} {cocone : Cocone diagram}
    (hcocone : IsColimit cocone) (subgroup : AddSubgroup cocone.pt)
    (hsubgroup : ∀ (index : J) (element : diagram.obj index),
      ConcreteCategory.hom (cocone.ι.app index) element ∈ subgroup)
    (element : cocone.pt) : element ∈ subgroup := by
  let restricted : Cocone diagram := Cocone.mk (AddCommGrpCat.of subgroup)
    { app := fun index => AddCommGrpCat.ofHom
        ((ConcreteCategory.hom (cocone.ι.app index)).codRestrict subgroup (hsubgroup index))
      naturality := by
        intro first second morphism
        ext element
        apply Subtype.ext
        exact ConcreteCategory.congr_hom (cocone.ι.naturality morphism) element }
  have equality : hcocone.desc restricted ≫ AddCommGrpCat.ofHom subgroup.subtype =
      AddCommGrpCat.ofHom (AddMonoidHom.id cocone.pt) := by
    refine hcocone.hom_ext fun index => ?_
    rw [← Category.assoc, hcocone.fac restricted index]
    ext element
    rfl
  have helement := ConcreteCategory.congr_hom equality element
  simp only [ConcreteCategory.comp_apply, AddCommGrpCat.hom_ofHom,
    AddMonoidHom.id_apply] at helement
  exact helement ▸ (ConcreteCategory.hom (hcocone.desc restricted) element).2

/-- For a compact object `generator` and a family `family : I → C` indexed by the universe of the
coproducts, the comparison morphism `⨁ Hom(generator, family i) ⟶ Hom(generator, ∐ family)` is an
isomorphism in `AddCommGrpCat`: this is the bijectivity in the definition of compactness, read as
an isomorphism of abelian groups. -/
theorem isIso_sigmaComparison_preadditiveCoyoneda
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasCoproducts.{v₁} C]
    (generator : C) [IsCompactObject.{v₁} generator] {I : Type v₁} (family : I → C) :
    IsIso (sigmaComparison (preadditiveCoyoneda.obj (op generator)) family) := by
  have := preservesColimitsOfShape_discrete_of_isCompactObject generator I
  infer_instance

/-- **Compactness as preservation of coproducts.** For a compact object `generator` of a
preadditive category with coproducts indexed by `Type v₁`, the additive corepresentable functor
`Hom(generator, -) = preadditiveCoyoneda.obj (op generator)` preserves coproducts indexed by any
`I : Type v₁`. This is the form in which compactness enters Brown representability. -/
theorem preservesCoproducts_preadditiveCoyoneda_of_isCompactObject
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasCoproducts.{v₁} C]
    (generator : C) [IsCompactObject.{v₁} generator] (I : Type v₁) :
    PreservesColimitsOfShape (Discrete I) (preadditiveCoyoneda.obj (op generator)) :=
  preservesColimitsOfShape_discrete_of_isCompactObject generator I

/-- A localization functor which is additive and commutes with the shift has additive shift
functors on its target. -/
private theorem shiftFunctor_additive_of_isLocalization
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Preadditive C]
    [Preadditive D] [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [W.HasLeftCalculusOfFractions] [L.CommShift ℤ] [L.Additive] (n : ℤ) :
    (shiftFunctor D n).Additive := by
  rw [Localization.functor_additive_iff L W]
  exact Functor.additive_of_iso (L.commShiftIso n)

/-- **Brown representability without smallness of the morphism types.** Let `C` be a triangulated
category which is `LocallySmall.{u₃}` and has `Type u₃`-indexed coproducts, and let
`functor : C ⥤ D` be exact and coproduct-preserving into a pretriangulated, locally small `D`. If
`C` has a compact object which is a weak triangulated generator, then `functor` is a left adjoint.

The proof runs Brown representability
(`exists_isTriangulated_rightAdjoint_of_compactlyGenerated`) not on `functor` but on
`ShrinkHoms.equivalence.inverse ⋙ functor ⋙ ShrinkHoms.equivalence.functor`, whose source and
target are genuinely `Type u₃`-enriched; the triangulated structure transports because
`ShrinkHoms.equivalence.functor` is a localization at the isomorphisms, which have a left calculus
of fractions compatible with the triangulation. The adjunction is then transported back along
`Functor.isLeftAdjoint_comp_iff_left` and `Functor.isLeftAdjoint_comp_iff_right`.

This is what makes the result usable for derived categories: `HasDerivedCategory.standard` places
morphisms a universe above objects, so `HasCoproducts` at the morphism universe is false, whereas
`LocallySmall.{u₃}` and `HasCoproducts.{u₃}` both hold. -/
theorem isLeftAdjoint_of_compact_generator
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [LocallySmall.{u₃} C] [LocallySmall.{u₃} D]
    [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
    [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D] [IsTriangulated C] [HasCoproducts.{u₃} C]
    (functor : C ⥤ D) (functorShift : functor.CommShift ℤ)
    (functorTriangulated : @Functor.IsTriangulated _ _ _ _ _ _ functor functorShift
      _ _ _ _ _ _ _ _)
    [∀ I : Type u₃, PreservesColimitsOfShape (Discrete I) functor]
    (generator : C) [IsCompactObject.{u₃} generator]
    (hgenerator : (ObjectProperty.singleton generator).IsWeakTriangulatedGenerator) :
    functor.IsLeftAdjoint := by
  let : functor.CommShift ℤ := functorShift
  let : functor.IsTriangulated := functorTriangulated
  let sourceEquivalence := ShrinkHoms.equivalence.{u₃} C
  let targetEquivalence := ShrinkHoms.equivalence.{u₃} D
  let sourceProperty := MorphismProperty.isomorphisms C
  let targetProperty := MorphismProperty.isomorphisms D
  let := isomorphisms_hasLeftCalculusOfFractions C
  let := isomorphisms_hasLeftCalculusOfFractions D
  let := isomorphisms_isCompatibleWithTriangulation C
  let := isomorphisms_isCompatibleWithTriangulation D
  let := Functor.IsLocalization.of_isEquivalence sourceEquivalence.functor sourceProperty le_rfl
  let := Functor.IsLocalization.of_isEquivalence targetEquivalence.functor targetProperty le_rfl
  let := HasShift.localized sourceEquivalence.functor sourceProperty ℤ
  let := HasShift.localized targetEquivalence.functor targetProperty ℤ
  let := Functor.CommShift.localized sourceEquivalence.functor sourceProperty ℤ
  let := Functor.CommShift.localized targetEquivalence.functor targetProperty ℤ
  let : sourceEquivalence.functor.Additive := ShrinkHoms.instAdditiveFunctor C
  let : targetEquivalence.functor.Additive := ShrinkHoms.instAdditiveFunctor D
  let : HasZeroObject (ShrinkHoms C) := sourceEquivalence.functor.hasZeroObject_of_additive
  let : HasZeroObject (ShrinkHoms D) := targetEquivalence.functor.hasZeroObject_of_additive
  let : ∀ n : ℤ, (shiftFunctor (ShrinkHoms C) n).Additive :=
    shiftFunctor_additive_of_isLocalization sourceEquivalence.functor sourceProperty
  let : ∀ n : ℤ, (shiftFunctor (ShrinkHoms D) n).Additive :=
    shiftFunctor_additive_of_isLocalization targetEquivalence.functor targetProperty
  let := Triangulated.Localization.pretriangulated sourceEquivalence.functor sourceProperty
  let := Triangulated.Localization.pretriangulated targetEquivalence.functor targetProperty
  let : sourceEquivalence.functor.IsTriangulated :=
    Triangulated.Localization.isTriangulated_functor sourceEquivalence.functor sourceProperty
  let : targetEquivalence.functor.IsTriangulated :=
    Triangulated.Localization.isTriangulated_functor targetEquivalence.functor targetProperty
  let : IsTriangulated (ShrinkHoms C) :=
    Triangulated.Localization.isTriangulated sourceEquivalence.functor sourceProperty
  let := sourceEquivalence.commShiftInverse ℤ
  let := sourceEquivalence.commShift_of_functor ℤ
  let : sourceEquivalence.inverse.IsTriangulated :=
    sourceEquivalence.toAdjunction.isTriangulated_rightAdjoint
  let : HasCoproducts.{u₃} (ShrinkHoms C) :=
    fun I => Adjunction.hasColimitsOfShape_of_equivalence sourceEquivalence.inverse
  let shrunkFunctor := sourceEquivalence.inverse ⋙ functor ⋙ targetEquivalence.functor
  let shrunkGenerator := sourceEquivalence.functor.obj generator
  let : shrunkFunctor.CommShift ℤ := by
    dsimp [shrunkFunctor]
    infer_instance
  let : shrunkFunctor.IsTriangulated := by
    dsimp [shrunkFunctor]
    infer_instance
  let : ∀ I : Type u₃, PreservesColimitsOfShape (Discrete I) shrunkFunctor := fun I => by
    dsimp [shrunkFunctor]
    infer_instance
  let : IsCompactObject.{u₃} shrunkGenerator :=
    (isCompactObject_iff_isCompactObject_obj sourceEquivalence.functor generator).1 inferInstance
  have hshrunkGenerator := isWeakTriangulatedGenerator_obj_of_equivalence sourceEquivalence
    generator hgenerator
  let family : PUnit.{u₃ + 1} → ShrinkHoms C := fun _ => shrunkGenerator
  let : ∀ (index : PUnit.{u₃ + 1}) (I : Type u₃),
      PreservesColimitsOfShape (Discrete I) (preadditiveCoyoneda.obj (op (family index))) :=
    fun _ I => preservesCoproducts_preadditiveCoyoneda_of_isCompactObject shrunkGenerator I
  have hfamily : ObjectProperty.ofObj family = ObjectProperty.singleton shrunkGenerator := by
    ext object
    simp only [ObjectProperty.ofObj_iff]
    simp [family]
  obtain ⟨rightAdjoint, adjunction, _, _⟩ :=
    @exists_isTriangulated_rightAdjoint_of_compactlyGenerated
      (ShrinkHoms C) (ShrinkHoms D) inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      shrunkFunctor inferInstance inferInstance inferInstance (PUnit.{u₃ + 1}) family
      (fun index I => preservesCoproducts_preadditiveCoyoneda_of_isCompactObject shrunkGenerator I)
      (by rw [hfamily]; exact hshrunkGenerator)
  exact (Functor.isLeftAdjoint_comp_iff_left functor targetEquivalence.functor).1
    ((Functor.isLeftAdjoint_comp_iff_right sourceEquivalence.inverse
      (functor ⋙ targetEquivalence.functor)).1 adjunction.isLeftAdjoint)

/-- The restricted form of `isLeftAdjoint_of_compact_generator`: if an exact functor
`functor : C ⥤ D` carries a triangulated full subcategory `sourceProperty` of `C` into a
triangulated full subcategory `targetProperty` of `D`, and the lift preserves coproducts, then the
lift is a left adjoint as soon as `sourceProperty.FullSubcategory` is locally small, has
coproducts, and has a compact weak generator.

This is the shape in which the result is used for derived categories: the ambient categories are
not locally small at the morphism universe, but the subcategory of interest is. -/
theorem isLeftAdjoint_lift_of_compact_generator
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
    [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D] [IsTriangulated C]
    (sourceProperty : ObjectProperty C) (targetProperty : ObjectProperty D)
    [sourceProperty.IsTriangulated] [targetProperty.IsTriangulated]
    [sourceProperty.IsClosedUnderIsomorphisms] [targetProperty.IsClosedUnderIsomorphisms]
    [LocallySmall.{u₃} sourceProperty.FullSubcategory]
    [LocallySmall.{u₃} targetProperty.FullSubcategory]
    [HasCoproducts.{u₃} sourceProperty.FullSubcategory]
    (functor : C ⥤ D) (functorShift : functor.CommShift ℤ)
    (functorTriangulated : @Functor.IsTriangulated _ _ _ _ _ _ functor functorShift
      _ _ _ _ _ _ _ _)
    (hfunctor : ∀ object : sourceProperty.FullSubcategory,
      targetProperty (functor.obj object.obj))
    [∀ I : Type u₃, PreservesColimitsOfShape (Discrete I)
      (targetProperty.lift (sourceProperty.ι ⋙ functor) hfunctor)]
    (generator : sourceProperty.FullSubcategory) [IsCompactObject.{u₃} generator]
    (hgenerator : (ObjectProperty.singleton generator).IsWeakTriangulatedGenerator) :
    (targetProperty.lift (sourceProperty.ι ⋙ functor) hfunctor).IsLeftAdjoint := by
  let : functor.CommShift ℤ := functorShift
  let : functor.IsTriangulated := functorTriangulated
  let restricted := targetProperty.lift (sourceProperty.ι ⋙ functor) hfunctor
  let inclusionIso := targetProperty.liftCompιIso (sourceProperty.ι ⋙ functor) hfunctor
  let : (sourceProperty.ι ⋙ functor).CommShift ℤ := inferInstance
  let : restricted.CommShift ℤ := Functor.CommShift.ofComp inclusionIso ℤ
  let : NatTrans.CommShift inclusionIso.hom ℤ :=
    Functor.CommShift.ofComp_compatibility inclusionIso ℤ
  let : restricted.IsTriangulated :=
    (Functor.isTriangulated_iff_comp_right inclusionIso).2 inferInstance
  exact isLeftAdjoint_of_compact_generator restricted inferInstance inferInstance
    generator hgenerator

end CategoryTheory.Pretriangulated

end
