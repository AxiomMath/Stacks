module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringModuleBoundedBelowEquivalence
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringModuleBoundedBelowEquivalenceUnconditional
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringObjectModuleDerivedSections

/-!
# `La^*` as an equivalence `D⁺(O_X) ≌ D⁺_𝒜(O)` for a hypercovering of `X` by a simplicial object

Let `C` be a site with fibre products, given by a pretopology `P`, let `X` be an object of `C`,
let `O_C` be a sheaf of commutative rings on `C` and let `a : U ⟶ X` be a hypercovering of `X` in
`C` by a simplicial object `U` of `C` (Stacks, Section 85.21). With `O_X = O_C|_{C/X}`,
`O = a⁻¹O_X` on the total site `(C/U)_total`, `a : (Sh((C/U)_total), O) ⟶ (Sh(C/X), O_X)` the
ringed augmentation of Stacks 0D9X and `𝒜 ⊂ Mod(O)` the weak Serre subcategory of cartesian
`O`-modules, **Stacks 0DAE** asserts that `La^*` defines an equivalence

`D⁺(O_X) ⟶ D⁺_𝒜(O)`

with quasi-inverse `R a_*`.

The source proves it as a special case of Stacks 0DA7, which is Stacks 0DA2 for the site `C/X`.
Both steps are carried out here, with no hypothesis beyond the source's:

* for an arbitrary hypercovering `K` of `X` (Stacks 01G5) the cartesian `O`-modules form a weak
  Serre subcategory, because `O = a⁻¹O_X` is a cartesian sheaf of rings
  (`RingedAugmentation.isCartesianSheaf_underlyingO`), so the face transitions have invertible
  structure maps and the library's Stacks 0D7J (2) applies
  (`SimplicialSiteSituation.isModuleFiberTransitionIso_isWeakSerreClass`);
* the derived adjunction `La^* ⊣ R a_*` restricts to an equivalence `D⁺(O_X) ≌ D⁺_𝒜(O)`
  (`RingedToposHom.derivedPullbackEquivalenceOfProperty`, the argument of Stacks 0D7U): the unit
  is invertible on all of `D(O_X)` by Stacks 0DA5, through its two unconditional inputs
  `isIso_pullbackAdjPushforwardModules_unit_over` and
  `pullbackComputesDerivedPushforward_of_isHypercovering`, and the counit is invertible on
  `D⁺_𝒜(O)` because every cartesian `O`-module is a pullback `a^*M`, which is the essential
  surjectivity clause of Stacks 0DA4 (`essImage_pullbackModules_over`);
* a hypercovering `a : U ⟶ X` in `C` is the same as a hypercovering of `X` by the
  semi-representable objects `n ↦ {U_n ⟶ X}` (Stacks 0GM9,
  `IsHypercoveringAugmentation.isHypercovering`).

## Main definitions

* `SimplicialSemiRepresentable.derivedPullbackEquivalenceOfIsHypercovering`:
  the equivalence `D⁺(O_X) ≌ D⁺_𝒜(O)` for a hypercovering `K` of `X`, the content of
  Stacks 0DA7.
* `SimplicialSemiRepresentable.derivedPullbackEquivalenceOfIsHypercoveringAugmentation`:
  the same for a hypercovering of `X` in `C` by a simplicial object.

## Main results

* `SimplicialSemiRepresentable.isWeakSerreClass_isModuleFiberTransitionIso_over`:
  the cartesian `O`-modules form a weak Serre subcategory of `Mod(O)`.
* `SimplicialSemiRepresentable.exists_derivedPullbackEquivalence_isHypercoveringAugmentation`:
  the cartesian `O`-modules form a weak Serre subcategory `𝒜`, and `La^*` is an equivalence
  `D⁺(O_X) ≌ D⁺_𝒜(O)` with quasi-inverse `R a_*`.

## Implementation notes

The module category of the total ringed topos has two spellings, through the ring sheaf of the
total *ringed topos* (`totalTopos`) and through that of the total *topology*, equal only after
unfolding `totalRingedTopos`. The class of cartesian modules is therefore stated once, in the
second spelling, its closure under isomorphism is supplied as a local instance in the first, and
the equations identifying the two functors of the equivalence with `La^*` and `R a_*` are
proved at the level of an abstract morphism of ringed topoi and transported by matching
reducible and instance transparency: checking them at default transparency unfolds the derived
direct image.

`D⁺(O_X)` is `DerivedCategoryB.derivedCategoryBPlus ⊤`, the bounded below objects of `D(O_X)`,
and `D⁺_𝒜(O)` is `DerivedCategoryB.derivedCategoryBPlus 𝒜`, the bounded below objects of `D(O)`
all of whose cohomology modules lie in `𝒜`, as in the library's Stacks 0DA2 and 0DA9.

## References

* [Stacks Project, Tag 0DAE](https://stacks.math.columbia.edu/tag/0DAE)
* [Stacks Project, Tag 0DA7](https://stacks.math.columbia.edu/tag/0DA7)
* [Stacks Project, Tag 0DA2](https://stacks.math.columbia.edu/tag/0DA2)
* [Stacks Project, Tag 0DA4](https://stacks.math.columbia.edu/tag/0DA4)
* [Stacks Project, Tag 0DA5](https://stacks.math.columbia.edu/tag/0DA5)
* [Stacks Project, Tag 0D7J](https://stacks.math.columbia.edu/tag/0D7J)
* [Stacks Project, Tag 0D7U](https://stacks.math.columbia.edu/tag/0D7U)
* [Stacks Project, Tag 0D9X](https://stacks.math.columbia.edu/tag/0D9X)
* [Stacks Project, Tag 0GM9](https://stacks.math.columbia.edu/tag/0GM9)
* [Stacks Project, Section 85.21 (Tag 09X8)](https://stacks.math.columbia.edu/tag/09X8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicGeometry
open Stacks.CategoryTheory.Hypercovering

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedToposHom

section ExactPullback

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [HasSheafify Y.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposHom X Y) [IsIso f.fSharpInverseImage]
  (P : ObjectProperty (SheafOfModules.{u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)))
  [P.IsClosedUnderIsomorphisms]

/-- The forward functor of `derivedPullbackEquivalenceOfProperty`, followed by the inclusion of
`D⁺_𝒫(O_C)`, is `La^*` on `D⁺(O_D)`. -/
theorem derivedPullbackEquivalenceOfProperty_functor_comp_ι
    (hP : ∀ N, P ((f.toModulesHom.pullbackModules).obj N))
    (hunitPlus : derivedPlusTarget (Y := Y) ≤ (derivedAdjunctionOfIsIsoFSharp f).unitIsIso)
    (hcounitPlus : derivedPlusProperty P ≤ (derivedAdjunctionOfIsIsoFSharp f).counitIsIso) :
    (derivedPullbackEquivalenceOfProperty f P hP hunitPlus hcounitPlus).functor ⋙
        (derivedPlusProperty P).ι =
      (derivedPlusTarget (Y := Y)).ι ⋙ (leftDerivedPullbackOfIsIsoFSharp f).functor :=
  rfl

/-- The quasi-inverse of `derivedPullbackEquivalenceOfProperty`, followed by the inclusion of
`D⁺(O_D)`, is `R f_*` on `D⁺_𝒫(O_C)`. -/
theorem derivedPullbackEquivalenceOfProperty_inverse_comp_ι
    (hP : ∀ N, P ((f.toModulesHom.pullbackModules).obj N))
    (hunitPlus : derivedPlusTarget (Y := Y) ≤ (derivedAdjunctionOfIsIsoFSharp f).unitIsIso)
    (hcounitPlus : derivedPlusProperty P ≤ (derivedAdjunctionOfIsIsoFSharp f).counitIsIso) :
    (derivedPullbackEquivalenceOfProperty f P hP hunitPlus hcounitPlus).inverse ⋙
        (derivedPlusTarget (Y := Y)).ι =
      (derivedPlusProperty P).ι ⋙
        Stacks.Cohomology.DerivedPushforward.derivedPushforward (X := X) (Y := Y) f :=
  rfl

end ExactPullback

end AlgebraicGeometry.RingedToposHom

namespace CategoryTheory.SimplicialSemiRepresentable

open CategoryTheory.SimplicialSiteSituation SemiRepresentable

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyComponent

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (K : SimplicialObject (FormalCoproduct.{u} (Over X)))
  (OC : Sheaf P.toGrothendieck CommRingCat.{u})

/-- **The cartesian `O`-modules form a weak Serre subcategory of `Mod(O)`**, for the structure
sheaf `O = a⁻¹O_X` of the total site of any simplicial semi-representable object `K` of `C/X`.
The structure sheaf is cartesian, being pulled back along the augmentation, which is the
hypothesis under which `SimplicialSiteSituation.isModuleFiberTransitionIso_isWeakSerreClass`
(Stacks 0D7J (2)) applies. -/
theorem isWeakSerreClass_isModuleFiberTransitionIso_over :
    ObjectProperty.IsWeakSerreClass
      ((situation (P.toGrothendieck.over X) K).IsModuleFiberTransitionIso
        (hypercoveringObjectRingedAugmentation P K OC).O) :=
  (situation (P.toGrothendieck.over X) K).isModuleFiberTransitionIso_isWeakSerreClass
    (hypercoveringObjectRingedAugmentation P K OC).O
    (RingedAugmentation.isCartesianSheaf_underlyingO
      (A := hypercoveringObjectRingedAugmentation P K OC))

/-- **Stacks 0D7H (3) for the ringed augmentation of a hypercovering of `X`**: every pullback
`a^*N` of a sheaf of `O_X`-modules is a cartesian `O`-module. -/
theorem isCartesianModule_pullbackModules_over
    (N : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (sliceTopos P K OC).J)) (sliceTopos P K OC).O)) :
    (situation (P.toGrothendieck.over X) K).IsModuleFiberTransitionIso
      (hypercoveringObjectRingedAugmentation P K OC).O
      ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := totalTopos P K OC) (Y := sliceTopos P K OC)
        (augmentationHom P K OC).toModulesHom).obj N) :=
  RingedAugmentation.isCartesianModule_pullbackModules
    (hypercoveringObjectRingedAugmentation P K OC) N

/-- The cartesian `O`-modules are closed under isomorphism, in the spelling of the module
category of the total ringed topos in which the equivalence consumes the class. -/
local instance isClosedUnderIsomorphisms_isModuleFiberTransitionIso_totalTopos :
    ObjectProperty.IsClosedUnderIsomorphisms
      (C := SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (J := (totalTopos P K OC).J)) (totalTopos P K OC).O))
      ((situation (P.toGrothendieck.over X) K).IsModuleFiberTransitionIso
        (hypercoveringObjectRingedAugmentation P K OC).O) where
  of_iso e h := isCartesianModule_of_iso (situation (P.toGrothendieck.over X) K)
    (hypercoveringObjectRingedAugmentation P K OC).O e h

/-- **The derived unit `E ⟶ R a_*La^*E` is invertible** for every `E` of `D(O_X)`, which is
Stacks 0DA5 through its two unconditional inputs. -/
theorem isIso_derivedAdjunction_unit_app_of_isHypercovering (hK : IsHypercovering P K) :
    ∀ M, IsIso ((RingedToposHom.derivedAdjunctionOfIsIsoFSharp
      (augmentationHom P K OC)).unit.app M) :=
  have := RingedToposHom.isIso_derivedPullbackPushforwardUnit (augmentationHom P K OC)
    (isIso_pullbackAdjPushforwardModules_unit_over P K OC hK)
    (pullbackComputesDerivedPushforward_of_isHypercovering P K OC hK)
  fun _ ↦ inferInstance

/-- **The unit is invertible on `D⁺(O_X)`** (Stacks 0DA5, here on all of `D(O_X)`). -/
theorem derivedPlusTarget_le_unitIsIso_of_isHypercovering (hK : IsHypercovering P K) :
    RingedToposHom.derivedPlusTarget (Y := sliceTopos P K OC) ≤
      (RingedToposHom.derivedAdjunctionOfIsIsoFSharp (X := totalTopos P K OC)
        (Y := sliceTopos P K OC) (augmentationHom P K OC)).unitIsIso :=
  fun M _ ↦ isIso_derivedAdjunction_unit_app_of_isHypercovering P K OC hK M

/-- **The counit is invertible on `D⁺_𝒜(O)`**: every cartesian `O`-module is `a^*` of an
`O_X`-module (Stacks 0DA4), and the dévissage of Stacks 0D7S propagates this along the
truncation triangles. -/
theorem derivedPlusProperty_le_counitIsIso_of_isHypercovering (hK : IsHypercovering P K) :
    RingedToposHom.derivedPlusProperty (X := totalTopos P K OC)
        ((situation (P.toGrothendieck.over X) K).IsModuleFiberTransitionIso
          (hypercoveringObjectRingedAugmentation P K OC).O) ≤
      (RingedToposHom.derivedAdjunctionOfIsIsoFSharp (X := totalTopos P K OC)
        (Y := sliceTopos P K OC) (augmentationHom P K OC)).counitIsIso :=
  fun M hM ↦ RingedToposHom.isIso_derivedCounit_app_of_property (augmentationHom P K OC)
    ((situation (P.toGrothendieck.over X) K).IsModuleFiberTransitionIso
      (hypercoveringObjectRingedAugmentation P K OC).O)
    (isIso_derivedAdjunction_unit_app_of_isHypercovering P K OC hK)
    (fun _ hF ↦ essImage_pullbackModules_over P K OC hK hF) M hM

/-- **`La^*` is an equivalence `D⁺(O_X) ≌ D⁺_𝒜(O)` with quasi-inverse `R a_*`**, for a
hypercovering `K` of `X`: the equivalence of Stacks 0DA7, with no hypothesis beyond `hK`. -/
def derivedPullbackEquivalenceOfIsHypercovering (hK : IsHypercovering P K) :
    (RingedToposHom.derivedPlusTarget (Y := sliceTopos P K OC)).FullSubcategory ≌
      (RingedToposHom.derivedPlusProperty (X := totalTopos P K OC)
        ((situation (P.toGrothendieck.over X) K).IsModuleFiberTransitionIso
        (hypercoveringObjectRingedAugmentation P K OC).O)).FullSubcategory :=
  RingedToposHom.derivedPullbackEquivalenceOfProperty (X := totalTopos P K OC)
    (Y := sliceTopos P K OC) (augmentationHom P K OC)
    ((situation (P.toGrothendieck.over X) K).IsModuleFiberTransitionIso
        (hypercoveringObjectRingedAugmentation P K OC).O)
    (isCartesianModule_pullbackModules_over P K OC)
    (derivedPlusTarget_le_unitIsIso_of_isHypercovering P K OC hK)
    (derivedPlusProperty_le_counitIsIso_of_isHypercovering P K OC hK)

/-- The forward functor of `derivedPullbackEquivalenceOfIsHypercovering` is `La^*`: followed by
the inclusion of `D⁺_𝒜(O)` it is `La^*` on `D⁺(O_X)`. -/
theorem derivedPullbackEquivalenceOfIsHypercovering_functor (hK : IsHypercovering P K) :
    (derivedPullbackEquivalenceOfIsHypercovering P K OC hK).functor ⋙
        (RingedToposHom.derivedPlusProperty (X := totalTopos P K OC)
          ((situation (P.toGrothendieck.over X) K).IsModuleFiberTransitionIso
            (hypercoveringObjectRingedAugmentation P K OC).O)).ι =
      (RingedToposHom.derivedPlusTarget (Y := sliceTopos P K OC)).ι ⋙
        (RingedToposHom.leftDerivedPullbackOfIsIsoFSharp (X := totalTopos P K OC)
          (Y := sliceTopos P K OC) (augmentationHom P K OC)).functor :=
  by
  unfold derivedPullbackEquivalenceOfIsHypercovering
  have h := RingedToposHom.derivedPullbackEquivalenceOfProperty_functor_comp_ι
    (augmentationHom P K OC)
    ((situation (P.toGrothendieck.over X) K).IsModuleFiberTransitionIso
      (hypercoveringObjectRingedAugmentation P K OC).O)
    (isCartesianModule_pullbackModules_over P K OC)
    (derivedPlusTarget_le_unitIsIso_of_isHypercovering P K OC hK)
    (derivedPlusProperty_le_counitIsIso_of_isHypercovering P K OC hK)
  with_reducible_and_instances exact h

/-- The quasi-inverse of `derivedPullbackEquivalenceOfIsHypercovering` is `R a_*`: followed by
the inclusion of `D⁺(O_X)` it is `R a_*` on `D⁺_𝒜(O)`. -/
theorem derivedPullbackEquivalenceOfIsHypercovering_inverse (hK : IsHypercovering P K) :
    (derivedPullbackEquivalenceOfIsHypercovering P K OC hK).inverse ⋙
        (RingedToposHom.derivedPlusTarget (Y := sliceTopos P K OC)).ι =
      (RingedToposHom.derivedPlusProperty (X := totalTopos P K OC)
          ((situation (P.toGrothendieck.over X) K).IsModuleFiberTransitionIso
            (hypercoveringObjectRingedAugmentation P K OC).O)).ι ⋙
        Stacks.Cohomology.DerivedPushforward.derivedPushforward (X := totalTopos P K OC)
          (Y := sliceTopos P K OC) (augmentationHom P K OC) :=
  by
  unfold derivedPullbackEquivalenceOfIsHypercovering
  have h := RingedToposHom.derivedPullbackEquivalenceOfProperty_inverse_comp_ι
    (augmentationHom P K OC)
    ((situation (P.toGrothendieck.over X) K).IsModuleFiberTransitionIso
      (hypercoveringObjectRingedAugmentation P K OC).O)
    (isCartesianModule_pullbackModules_over P K OC)
    (derivedPlusTarget_le_unitIsIso_of_isHypercovering P K OC hK)
    (derivedPlusProperty_le_counitIsIso_of_isHypercovering P K OC hK)
  with_reducible_and_instances exact h

section SimplicialObject

variable (U : SimplicialObject C) (a : U ⟶ (SimplicialObject.const C).obj X)

/-- The equivalence `La^* : D⁺(O_X) ≌ D⁺_𝒜(O)` for a hypercovering `a : U ⟶ X` of `X` in `C` by a
simplicial object: `derivedPullbackEquivalenceOfIsHypercovering` at the hypercovering of `X` by
the semi-representable objects `n ↦ {U_n ⟶ X}` that `a` determines (Stacks 0GM9). -/
def derivedPullbackEquivalenceOfIsHypercoveringAugmentation
    (h : IsHypercoveringAugmentation P U a) :
    (RingedToposHom.derivedPlusTarget
          (Y := sliceTopos P (associatedSimplicialObject.{u} U a) OC)).FullSubcategory ≌
      (RingedToposHom.derivedPlusProperty
          (X := totalTopos P (associatedSimplicialObject.{u} U a) OC)
          ((situation (P.toGrothendieck.over X)
          (associatedSimplicialObject.{u} U a)).IsModuleFiberTransitionIso
          (hypercoveringObjectRingedAugmentation P
            (associatedSimplicialObject.{u} U a) OC).O)).FullSubcategory :=
  derivedPullbackEquivalenceOfIsHypercovering P (associatedSimplicialObject.{u} U a) OC
    (h.isHypercovering P U a)

/-- The forward functor of `derivedPullbackEquivalenceOfIsHypercoveringAugmentation` is `La^*`:
followed by the inclusion of `D⁺_𝒜(O)` it is `La^*` on `D⁺(O_X)`. -/
theorem derivedPullbackEquivalenceOfIsHypercoveringAugmentation_functor
    (h : IsHypercoveringAugmentation P U a) :
    (derivedPullbackEquivalenceOfIsHypercoveringAugmentation P OC U a h).functor ⋙
        (RingedToposHom.derivedPlusProperty
          (X := totalTopos P (associatedSimplicialObject.{u} U a) OC)
          ((situation (P.toGrothendieck.over X)
          (associatedSimplicialObject.{u} U a)).IsModuleFiberTransitionIso
          (hypercoveringObjectRingedAugmentation P (associatedSimplicialObject.{u} U a) OC).O)).ι =
      (RingedToposHom.derivedPlusTarget
          (Y := sliceTopos P (associatedSimplicialObject.{u} U a) OC)).ι ⋙
        (RingedToposHom.leftDerivedPullbackOfIsIsoFSharp
          (X := totalTopos P (associatedSimplicialObject.{u} U a) OC)
          (Y := sliceTopos P (associatedSimplicialObject.{u} U a) OC)
          (augmentationHom P (associatedSimplicialObject.{u} U a) OC)).functor :=
  derivedPullbackEquivalenceOfIsHypercovering_functor P _ OC (h.isHypercovering P U a)

/-- The quasi-inverse of `derivedPullbackEquivalenceOfIsHypercoveringAugmentation` is `R a_*`:
followed by the inclusion of `D⁺(O_X)` it is `R a_*` on `D⁺_𝒜(O)`. -/
theorem derivedPullbackEquivalenceOfIsHypercoveringAugmentation_inverse
    (h : IsHypercoveringAugmentation P U a) :
    (derivedPullbackEquivalenceOfIsHypercoveringAugmentation P OC U a h).inverse ⋙
        (RingedToposHom.derivedPlusTarget
          (Y := sliceTopos P (associatedSimplicialObject.{u} U a) OC)).ι =
      (RingedToposHom.derivedPlusProperty
          (X := totalTopos P (associatedSimplicialObject.{u} U a) OC)
          ((situation (P.toGrothendieck.over X)
          (associatedSimplicialObject.{u} U a)).IsModuleFiberTransitionIso
          (hypercoveringObjectRingedAugmentation P (associatedSimplicialObject.{u} U a) OC).O)).ι ⋙
        Stacks.Cohomology.DerivedPushforward.derivedPushforward
          (X := totalTopos P (associatedSimplicialObject.{u} U a) OC)
          (Y := sliceTopos P (associatedSimplicialObject.{u} U a) OC)
          (augmentationHom P (associatedSimplicialObject.{u} U a) OC) :=
  derivedPullbackEquivalenceOfIsHypercovering_inverse P _ OC (h.isHypercovering P U a)

/-- Let `C` be a site with fibre products, given by a pretopology `P`, let `X` be an object of
`C`, let `O_C` be a sheaf of commutative rings on `C` and let `a : U ⟶ X` be a hypercovering of
`X` in `C` by a simplicial object `U` of `C` (`IsHypercoveringAugmentation`). Let
`O_X = O_C|_{C/X}`, let `O = a⁻¹O_X` on the total site `(C/U)_total` and let
`a : (Sh((C/U)_total), O) ⟶ (Sh(C/X), O_X)` be the ringed augmentation of Stacks 0D9X. Then

* the cartesian `O`-modules form a weak Serre subcategory `𝒜 ⊂ Mod(O)`, and
* the functor `La^*` defines an equivalence `D⁺(O_X) ⟶ D⁺_𝒜(O)` with quasi-inverse `R a_*`:
  there is an equivalence of categories whose functor, followed by the inclusion of `D⁺_𝒜(O)`, is
  `La^*` on `D⁺(O_X)`, and whose inverse, followed by the inclusion of `D⁺(O_X)`, is `R a_*` on
  `D⁺_𝒜(O)`.

Here `D⁺(O_X)` is the full subcategory of bounded below objects of `D(O_X)`, and `D⁺_𝒜(O)` that of
bounded below objects of `D(O)` all of whose cohomology modules are cartesian. The equivalence is
`derivedPullbackEquivalenceOfIsHypercoveringAugmentation`. -/
@[stacks 0DAE]
theorem exists_derivedPullbackEquivalence_isHypercoveringAugmentation
    (h : IsHypercoveringAugmentation P U a) :
    ObjectProperty.IsWeakSerreClass
        ((situation (P.toGrothendieck.over X)
          (associatedSimplicialObject.{u} U a)).IsModuleFiberTransitionIso
          (hypercoveringObjectRingedAugmentation P (associatedSimplicialObject.{u} U a) OC).O) ∧
      ∃ e : (RingedToposHom.derivedPlusTarget
          (Y := sliceTopos P (associatedSimplicialObject.{u} U a) OC)).FullSubcategory ≌
          (RingedToposHom.derivedPlusProperty
          (X := totalTopos P (associatedSimplicialObject.{u} U a) OC)
          ((situation (P.toGrothendieck.over X)
          (associatedSimplicialObject.{u} U a)).IsModuleFiberTransitionIso
          (hypercoveringObjectRingedAugmentation P
            (associatedSimplicialObject.{u} U a) OC).O)).FullSubcategory,
        e.functor ⋙ (RingedToposHom.derivedPlusProperty
          (X := totalTopos P (associatedSimplicialObject.{u} U a) OC)
          ((situation (P.toGrothendieck.over X)
          (associatedSimplicialObject.{u} U a)).IsModuleFiberTransitionIso
          (hypercoveringObjectRingedAugmentation P (associatedSimplicialObject.{u} U a) OC).O)).ι =
          (RingedToposHom.derivedPlusTarget
          (Y := sliceTopos P (associatedSimplicialObject.{u} U a) OC)).ι ⋙
            (RingedToposHom.leftDerivedPullbackOfIsIsoFSharp
          (X := totalTopos P (associatedSimplicialObject.{u} U a) OC)
          (Y := sliceTopos P (associatedSimplicialObject.{u} U a) OC)
          (augmentationHom P (associatedSimplicialObject.{u} U a) OC)).functor ∧
        e.inverse ⋙ (RingedToposHom.derivedPlusTarget
          (Y := sliceTopos P (associatedSimplicialObject.{u} U a) OC)).ι =
          (RingedToposHom.derivedPlusProperty
          (X := totalTopos P (associatedSimplicialObject.{u} U a) OC)
          ((situation (P.toGrothendieck.over X)
          (associatedSimplicialObject.{u} U a)).IsModuleFiberTransitionIso
          (hypercoveringObjectRingedAugmentation P (associatedSimplicialObject.{u} U a) OC).O)).ι ⋙
            Stacks.Cohomology.DerivedPushforward.derivedPushforward
          (X := totalTopos P (associatedSimplicialObject.{u} U a) OC)
          (Y := sliceTopos P (associatedSimplicialObject.{u} U a) OC)
          (augmentationHom P (associatedSimplicialObject.{u} U a) OC) :=
  ⟨isWeakSerreClass_isModuleFiberTransitionIso_over P (associatedSimplicialObject.{u} U a) OC,
    derivedPullbackEquivalenceOfIsHypercoveringAugmentation P OC U a h,
    derivedPullbackEquivalenceOfIsHypercoveringAugmentation_functor P OC U a h,
    derivedPullbackEquivalenceOfIsHypercoveringAugmentation_inverse P OC U a h⟩

end SimplicialObject

end CategoryTheory.SimplicialSemiRepresentable

end
