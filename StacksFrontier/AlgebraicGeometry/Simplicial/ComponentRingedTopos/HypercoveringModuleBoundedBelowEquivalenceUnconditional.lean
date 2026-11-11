module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.AugmentationModuleDescent
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ComponentTransitionComparison
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringModuleBoundedBelowEquivalence
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringModuleCohomologicalDescentUnconditional
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianWeakSerreModules

/-!
# `La^*` is an equivalence `D⁺(O_C) ≌ D⁺_𝒜(O)` for a hypercovering, unconditionally

Let `C` be a site with equalizers and fibre products, let `O_C` be a sheaf of commutative rings
on it, let `K` be a hypercovering of `C` and let `a : (Sh((C/K)_total), O) ⟶ (Sh(C), O_C)` be the
ringed augmentation of Stacks 0D9W, with `O = a⁻¹O_C`. Let `𝒜 ⊂ Mod(O)` be the cartesian
`O`-modules. Stacks 0DA2 asserts that `𝒜` is a weak Serre subcategory and that

`La^* : D⁺(O_C) ⟶ D⁺_𝒜(O)`

is an equivalence of categories with quasi-inverse `R a_*`.

The equivalence is
`Stacks.CategoryTheory.Hypercovering.derivedPullbackEquivalenceOfHypercovering`, built from three
inputs `hunit`, `hacyclic` and `hsurj`. This file proves all three for every hypercovering and
proves the weak Serre property of `𝒜`, so the statement holds with nothing beyond the hypotheses
of the source:

* `hunit`, the module form of Stacks 0D8E (`M = a_*a^*M`), is
  `CategoryTheory.SimplicialSemiRepresentable`
  `.isIso_pullbackAdjPushforwardModules_unit_of_hypercoveringOfTerminal`;
* `hacyclic`, that `a^*` of a K-injective complex computes `R a_*`, is
  `CategoryTheory.SimplicialSemiRepresentable`
  `.pullbackComputesDerivedPushforward_of_hypercoveringOfTerminal`;
* `hsurj`, the essential-surjectivity clause of Stacks 0D9Z, is
  `Stacks.CategoryTheory.Hypercovering.essImage_pullbackModules_of_hypercoveringCartesianModules`,
  from `CategoryTheory.SimplicialSiteSituation.RingedAugmentation`
  `.essImage_pullbackModules_of_isCartesianModule` and Stacks 0D8E (1) on sheaves of sets;
* the weak Serre property, Stacks 0D7J (2) as the source applies it through Stacks 0D9W, is
  `Stacks.CategoryTheory.Hypercovering.isWeakSerreClass_hypercoveringCartesianModules`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.isModuleFiberTransitionIso_iff_isCartesianModule`: the
  two spellings of the cartesian condition on sheaves of modules (Stacks 07TF (2)), through the
  component 2-morphism and through the transition of Stacks 09WF, agree.
* `CategoryTheory.SimplicialSiteSituation.isModuleFiberTransitionIso_isWeakSerreClass`: over a
  cartesian structure sheaf the cartesian modules form a weak Serre subcategory. The structure
  maps of the transition morphisms are then invertible, so the pullbacks along the face
  transitions are exact and Stacks 0D7J (2) applies.
* `Stacks.CategoryTheory.Hypercovering.derivedPullbackEquivalenceOfHypercoveringOfTerminal`: the
  equivalence `D⁺(O_C) ≌ D⁺_𝒜(O)`, with no hypothesis.
* `Stacks.CategoryTheory.Hypercovering.exists_derivedPullbackEquivalence_hypercoveringOfTerminal`:
  **Stacks 0DA2**.

## Implementation notes

**Why `hsurj` goes through sheaves of sets.** The library's Stacks 0D9Z essential-image lemma
`RingedAugmentation.essImage_pullbackModules` is stated at the spelling
`situation J.toGrothendieck H.toSimplicialObject` of the simplicial site, while the equivalence
consumes the spelling `hypercoveringSituation J H`. The two are equal by unfolding a definition,
but elaborating the conversion at the level of sheaves of modules does not terminate within the
recursion limit, because the module categories carry the total topology inside their ring sheaf.
The conversion is therefore made at the level of sheaves of sets, where it is immediate, and the
module statement is then obtained from the general
`RingedAugmentation.essImage_pullbackModules_of_isCartesianModule`, which is stated for an
arbitrary simplicial site and so is applied directly at `hypercoveringSituation J H`.

**The derived categories** are those of the base construction, which is built over the
`HasDerivedCategory.standard` model; this file introduces no derived category of its own.

## References

* [Stacks Project, Tag 0DA2](https://stacks.math.columbia.edu/tag/0DA2)
* [Stacks Project, Tag 0DA0](https://stacks.math.columbia.edu/tag/0DA0)
* [Stacks Project, Tag 0D9Z](https://stacks.math.columbia.edu/tag/0D9Z)
* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
* [Stacks Project, Tag 0D8E](https://stacks.math.columbia.edu/tag/0D8E)
* [Stacks Project, Tag 0D7J](https://stacks.math.columbia.edu/tag/0D7J)
* [Stacks Project, Tag 0D7U](https://stacks.math.columbia.edu/tag/0D7U)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- **The two spellings of the cartesian condition of Stacks 07TF (2) agree.** A sheaf of
`O`-modules on the total site has invertible transitions through the component 2-morphism
(`IsModuleFiberTransitionIso`) if and only if it has invertible transitions of Stacks 09WF
(`IsCartesianModule`): the two transitions differ by the identifications of the two
presentations of restriction to a component, by
`CategoryTheory.SimplicialSiteSituation.moduleFiberTransition_comp_restrictionIso`. -/
theorem isModuleFiberTransitionIso_iff_isCartesianModule
    (M : SheafOfModules.{u} (S.totalRingSheaf O)) :
    S.IsModuleFiberTransitionIso O M ↔ IsCartesianModule S O M := by
  refine ⟨fun h m n φ ↦ ?_, fun h m n φ ↦ ?_⟩
  · have := h φ
    exact S.isIso_fiberTransitionModules_of_isIso_moduleFiberTransition O φ M
      (S.moduleFiberTransition_comp_restrictionIso O φ M)
  · let e₁ := (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.mapIso
      ((S.componentPullbackModulesRestrictionIso O m).app M).symm
    let e₂ := (S.componentPullbackModulesRestrictionIso O n).app M
    have hc : e₁.hom ≫ (S.moduleFiberTransition O φ).app M ≫ e₂.hom =
        S.fiberTransitionModules O φ M :=
      S.moduleFiberTransition_comp_restrictionIso O φ M
    have h₁ : IsIso (e₁.hom ≫ (S.moduleFiberTransition O φ).app M ≫ e₂.hom) := hc ▸ h φ
    exact (isIso_comp_right_iff _ e₂.hom).1 ((isIso_comp_left_iff e₁.hom _).1 h₁)

/-- The two spellings of the cartesian condition on sheaves of modules are the same class. -/
theorem isModuleFiberTransitionIso_eq_isCartesianModule :
    S.IsModuleFiberTransitionIso O = IsCartesianModule S O :=
  funext fun M ↦ propext (S.isModuleFiberTransitionIso_iff_isCartesianModule O M)

attribute [local instance] hasSheafifyTotalModule wEqualsLocallyBijectiveTotalModule
  hasSheafifyComponentModule wEqualsLocallyBijectiveComponentModule

/-- **Over a cartesian structure sheaf, the cartesian modules form a weak Serre subcategory of
`Mod(O)`.** If the underlying sheaf of sets of `O` is cartesian, the structure maps of the
transition morphisms of ringed topoi are invertible
(`CategoryTheory.SimplicialSiteSituation.isIso_transitionRingedToposHom_fSharpInverseImage`), so
pullback of modules along each face transition is left exact, which is the hypothesis in which
this library's Stacks 0D7J (2), `isCartesianModule_isWeakSerreClass`, takes the flatness of the
faces. -/
theorem isModuleFiberTransitionIso_isWeakSerreClass
    (hO : S.IsCartesianSheaf ((sheafCompose S.totalTopology (forget CommRingCat.{u})).obj O)) :
    ObjectProperty.IsWeakSerreClass (S.IsModuleFiberTransitionIso O) := by
  rw [S.isModuleFiberTransitionIso_eq_isCartesianModule O]
  refine S.isCartesianModule_isWeakSerreClass O fun k i ↦ ?_
  have := S.isIso_transitionRingedToposHom_fSharpInverseImage O hO (SimplexCategory.δ i)
  exact RingedToposHom.pullbackModules_preservesFiniteLimits_of_isIso_fSharp
    (S.transitionRingedToposHom O (SimplexCategory.δ i))

end CategoryTheory.SimplicialSiteSituation

namespace Stacks.CategoryTheory.Hypercovering

open CategoryTheory.SimplicialSiteSituation CategoryTheory.SimplicialSemiRepresentable

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (J : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u} J) (OC : Sheaf J.toGrothendieck CommRingCat.{u})

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyComponent

attribute [local instance] isClosedUnderIsomorphisms_hypercoveringCartesianModules

/-- **The cartesian `O`-modules on the total site of a hypercovering form a weak Serre
subcategory of `Mod(O)`**, the observation with which the proof of Stacks 0DA2 opens: Stacks
0D7J (2), whose hypothesis holds because `O = a⁻¹O_C` is cartesian (Stacks 0D9W). -/
theorem isWeakSerreClass_hypercoveringCartesianModules :
    (hypercoveringCartesianModules J H OC).IsWeakSerreClass :=
  (hypercoveringSituation J H).isModuleFiberTransitionIso_isWeakSerreClass _
    (RingedAugmentation.isCartesianSheaf_underlyingO (hypercoveringRingedAugmentation J H OC))

/-- **Stacks 0D8E (1), essential image, at the spelling `hypercoveringSituation J H`**: every
cartesian sheaf of sets on the total site of a hypercovering is an inverse image `a⁻¹F`. -/
theorem essImage_hypercoveringTotalInverseImage_of_isCartesianSheaf :
    ∀ E : Sheaf (hypercoveringSituation J H).totalTopology (Type u),
      (hypercoveringSituation J H).IsCartesianSheaf E →
      (Augmentation.totalMorphismOfTopoi (hypercoveringSituation J H) (Cat.of C) J.toGrothendieck
        (hypercoveringAugmentation J H)).inverseImage.essImage E :=
  essImage_situationTotalInverseImage_of_isCartesianSheaf J H

/-- **Stacks 0D8E (1), fullness, at the spelling `hypercoveringSituation J H`**: the inverse
image `a⁻¹` of sheaves of sets along the augmentation of a hypercovering is full. -/
theorem full_hypercoveringTotalInverseImage :
    (Augmentation.totalMorphismOfTopoi (hypercoveringSituation J H) (Cat.of C)
      J.toGrothendieck (hypercoveringAugmentation J H)).inverseImage.Full :=
  full_situationTotalInverseImage J H

/-- **Stacks 0D8E (1), faithfulness, at the spelling `hypercoveringSituation J H`**: the inverse
image `a⁻¹` of sheaves of sets along the augmentation of a hypercovering is faithful. -/
theorem faithful_hypercoveringTotalInverseImage :
    (Augmentation.totalMorphismOfTopoi (hypercoveringSituation J H) (Cat.of C)
      J.toGrothendieck (hypercoveringAugmentation J H)).inverseImage.Faithful :=
  faithful_situationTotalInverseImage J H

/-- **Stacks 0D9Z, essential surjectivity onto the cartesian `O`-modules**, in the form in which
`derivedPullbackEquivalenceOfHypercovering` takes it as `hsurj`: every cartesian sheaf of
`O`-modules on the total site of a hypercovering is a pullback `a^*M`. Its underlying sheaf of sets
is cartesian, hence an inverse image by Stacks 0D8E (1), and a sheaf of modules whose underlying
sheaf of sets is an inverse image is a pullback. -/
theorem essImage_pullbackModules_of_hypercoveringCartesianModules :
    ∀ M, hypercoveringCartesianModules J H OC M →
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := (hypercoveringSituation J H).totalRingedTopos
          (hypercoveringRingedAugmentation J H OC).O)
        (Y := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos)
        (hypercoveringRingedAugmentation J H OC).totalRingedHom.toModulesHom).essImage M :=
  fun _ hM ↦ RingedAugmentation.essImage_pullbackModules_of_isCartesianModule
    (hypercoveringRingedAugmentation J H OC) (full_hypercoveringTotalInverseImage J H)
    (faithful_hypercoveringTotalInverseImage J H)
    (essImage_hypercoveringTotalInverseImage_of_isCartesianSheaf J H) hM

/-- **The equivalence `La^* : D⁺(O_C) ≌ D⁺_𝒜(O)` of Stacks 0DA2, with no hypothesis.** It is
`derivedPullbackEquivalenceOfHypercovering` with its three inputs proved: `hunit` (Stacks 0D8E in
its module form), `hacyclic` (`a^*` of a K-injective complex computes `R a_*`) and `hsurj`
(Stacks 0D9Z). Its functor is the restriction of `La^*` and its inverse the restriction of
`R a_*`, on the nose. -/
def derivedPullbackEquivalenceOfHypercoveringOfTerminal :
    (AlgebraicGeometry.RingedToposHom.derivedPlusTarget
        (Y := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos)).FullSubcategory ≌
      (AlgebraicGeometry.RingedToposHom.derivedPlusProperty
        (hypercoveringCartesianModules J H OC)).FullSubcategory :=
  derivedPullbackEquivalenceOfHypercovering J H OC
    (isIso_pullbackAdjPushforwardModules_unit_of_hypercoveringOfTerminal J H OC)
    (pullbackComputesDerivedPushforward_of_hypercoveringOfTerminal J H OC)
    (essImage_pullbackModules_of_hypercoveringCartesianModules J H OC)

/-- **Stacks 0DA2.** Let `C` be a site with equalizers and fibre products, let `O_C` be a sheaf
of commutative rings on it and let `K` be a hypercovering of `C`; let
`a : (Sh((C/K)_total), O) ⟶ (Sh(C), O_C)` be the ringed augmentation of Stacks 0D9W, so
`O = a⁻¹O_C`. Then the cartesian `O`-modules `𝒜 ⊂ Mod(O)` form a weak Serre subcategory, and the
functor `La^*` defines an equivalence

`D⁺(O_C) ⟶ D⁺_𝒜(O)`

with quasi-inverse `R a_*`: there is an equivalence of categories whose functor is the restriction
of the derived pullback `La^*` to the bounded below subcategories and whose inverse is the
restriction of the derived direct image `R a_*`. Here `D⁺(O_C)` is the full subcategory of
bounded below objects of `D(O_C)`, and `D⁺_𝒜(O)` that of bounded below objects of `D(O)` all of
whose cohomology modules are cartesian. Nothing is assumed beyond the hypotheses of the source. -/
@[stacks 0DA2 "cartesian O-modules are weak Serre; La^* : D⁺(O_C) ≌ D⁺_𝒜(O), inverse Ra_*"]
theorem exists_derivedPullbackEquivalence_hypercoveringOfTerminal :
    (hypercoveringCartesianModules J H OC).IsWeakSerreClass ∧
      ∃ e : (AlgebraicGeometry.RingedToposHom.derivedPlusTarget
          (Y := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos)).FullSubcategory ≌
        (AlgebraicGeometry.RingedToposHom.derivedPlusProperty
          (hypercoveringCartesianModules J H OC)).FullSubcategory,
        e.functor = AlgebraicGeometry.RingedToposHom.derivedPullbackPlus
          (X := (hypercoveringSituation J H).totalRingedTopos
            (hypercoveringRingedAugmentation J H OC).O)
          (Y := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos)
          (hypercoveringRingedAugmentation J H OC).totalRingedHom
          (hypercoveringCartesianModules J H OC)
          (isCartesianModule_pullbackModules_hypercovering J H OC) ∧
        e.inverse = AlgebraicGeometry.RingedToposHom.derivedPushforwardPlus
          (X := (hypercoveringSituation J H).totalRingedTopos
            (hypercoveringRingedAugmentation J H OC).O)
          (Y := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos)
          (hypercoveringRingedAugmentation J H OC).totalRingedHom
          (hypercoveringCartesianModules J H OC) :=
  ⟨isWeakSerreClass_hypercoveringCartesianModules J H OC,
    derivedPullbackEquivalenceOfHypercoveringOfTerminal J H OC, rfl, rfl⟩

end Stacks.CategoryTheory.Hypercovering

end
