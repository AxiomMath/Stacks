module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringObjectModuleDescent
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.FromSimplicialObject

/-!
# Descent of sheaves of modules along a hypercovering by a simplicial object of the site

Let `C` be a site with fibre products, let `O_C` be a sheaf of commutative rings on it, let `X`
be an object of `C` and set `O_X = O_C|_{C/X}`. Let `U` be a simplicial object of `C` augmented
to `X` which is a hypercovering of `X` in the sense of Stacks, Section 85.21: the augmentation
`U_0 ⟶ X`, the canonical map `U_1 ⟶ U_0 ×_X U_0`, and every higher matching map
`U_{n+1} ⟶ (cosk_n sk_n U)_{n+1}` — the last two formed in `C/X` — generate covering presieves.

Reading each term of `U` as a one-summand family of objects over `X` turns `U ⟶ X` into a
simplicial semi-representable object `associatedSimplicialObject U a` of `SR(C, X)`, and
Stacks 0GM9 identifies the three conditions above with its being a hypercovering of `X` in the
sense of Stacks 01G5. So the total site `(C/U)_total`, the pulled-back structure sheaf
`O = a⁻¹O_X` and the morphism of ringed topoi
`a : (Sh((C/U)_total), O) ⟶ (Sh(C/X), O_X)` of Stacks 0D9X are those of that semi-representable
object, and every assertion about `a` for a hypercovering of an object specializes.

Stacks 0DAB asserts that `a^* : Mod(O_X) ⟶ Mod(O)` is fully faithful with essential image the
cartesian `O`-modules, with `a_*` as quasi-inverse; its proof in the source is that this is a
special case of Stacks 0DA4. This file carries out that specialization, from the results of
Stacks 0DA4 in
`StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringObjectModuleDescent`:
`a^*` is faithful and full, its essential image is exactly the cartesian `O`-modules, and the unit
and the counit of `a^* ⊣ a_*` are isomorphisms, the counit at every cartesian `O`-module, so that
`a_*` is a quasi-inverse.

## Main definitions

There are no new definitions: the ringed augmentation is the one of Stacks 0D9X attached by
`CategoryTheory.SimplicialSemiRepresentable.hypercoveringObjectRingedAugmentation` to the
associated simplicial semi-representable object.

## Main results

In the namespace `CategoryTheory.SimplicialSemiRepresentable`, all for **Stacks 0DAB**:

* `faithful_pullbackModules_simplicialObject`: faithfulness of `a^*` on sheaves of modules.
* `isCartesianModule_of_mem_essImage_simplicialObject`: the inclusion of the essential image of
  `a^*` in the cartesian `O`-modules.
* `full_pullbackModules_simplicialObject` and `fullyFaithfulPullbackModulesSimplicialObject`:
  fullness and full faithfulness of `a^*`.
* `essImage_pullbackModules_simplicialObject` and
  `mem_essImage_pullbackModules_iff_isCartesianModule_simplicialObject`: the essential image of
  `a^*` is exactly the cartesian `O`-modules.
* `isIso_pullbackAdjPushforwardModules_unit_simplicialObject` and
  `isIso_pullbackAdjPushforwardModules_counit_app_simplicialObject`: `a_*` is a quasi-inverse.

## Implementation notes

The hypotheses are the three covering conditions of Section 85.21 written out, which is the form
in which `Stacks.CategoryTheory.Hypercovering.isHypercovering_associatedSimplicialObject_iff` of
Stacks 0GM9 states the hypercovering condition on the associated semi-representable object; no
separate predicate on augmented simplicial objects is introduced, that identification being the
development's rendering of the Section 85.21 definition. The inclusion of the essential image in
the cartesian modules needs none of the three, exactly as its Stacks 0DA4 source needs no
condition on the hypercovering, and is stated without them.

The ringed augmentation is written out rather than abbreviated at the simplicial object: an
abbreviation for it interposes a further layer of unfolding between the statement of the
essential-image inclusion and the sheafification instances its type needs, and elaborating that
type then exceeds the recursion depth.

Sheaves of modules are formed at the site universe. The three sheafification instances this
needs are the ones stated for an arbitrary simplicial-site situation in
`StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringObjectModuleDescent`;
being attached there as local instances they are not visible here, and are re-attached below.

## References

* [Stacks Project, Tag 0DAB](https://stacks.math.columbia.edu/tag/0DAB)
* [Stacks Project, Tag 0DA4](https://stacks.math.columbia.edu/tag/0DA4)
* [Stacks Project, Tag 0D9X](https://stacks.math.columbia.edu/tag/0D9X)
* [Stacks Project, Tag 0D9Z](https://stacks.math.columbia.edu/tag/0D9Z)
* [Stacks Project, Tag 0GM9](https://stacks.math.columbia.edu/tag/0GM9)
* [Stacks Project, Tag 01G5](https://stacks.math.columbia.edu/tag/01G5)
* [Stacks Project, Section 85.21 (Tag 09X8)](https://stacks.math.columbia.edu/tag/09X8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicGeometry
open Stacks.CategoryTheory.Hypercovering

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyComponent

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (U : SimplicialObject C) (a : U ⟶ (SimplicialObject.const C).obj X)
  (OC : Sheaf P.toGrothendieck CommRingCat.{u})

/-- **Stacks 0DAB, the faithfulness half.** Let `C` be a site with fibre products, `X` an object
of it, `O_C` a sheaf of commutative rings on `C`, and `U` a simplicial object of `C` augmented
to `X` which is a hypercovering of `X` in the sense of Stacks, Section 85.21: the degree-zero
augmentation, the canonical map `U_1 ⟶ U_0 ×_X U_0`, and every higher matching map generate
covering presieves. With `O_X = O_C|_{C/X}` and `O = a⁻¹O_X`, the pullback
`a^* : Mod(O_X) ⥤ Mod(O)` of sheaves of modules along the augmentation of the total site of `U`
over `C/X` is faithful.

This is Stacks 0DA4 for the associated simplicial semi-representable object of Stacks 0GM9,
whose hypercovering condition is exactly the three hypotheses. -/
@[stacks 0DAB "a^* on sheaves of modules is faithful, for a hypercovering of X by a simplicial \
object of the site. The essential-image inclusion is \
`isCartesianModule_of_mem_essImage_simplicialObject`; fullness of a^*, and essential \
surjectivity onto the cartesian O-modules making a_* a quasi-inverse, are not proved"]
theorem faithful_pullbackModules_simplicialObject
    (h₀ : Presieve.singleton (a.app (op ⦋0⦌)) ∈ P X)
    (h₁ : Presieve.singleton (oneSimplexToFiberProduct U a) ∈
      P (pullback (a.app (op ⦋0⦌)) (a.app (op ⦋0⦌))))
    (hmatch : ∀ n : ℕ, 1 ≤ n → Presieve.singleton (matchingMap U a n) ∈
      P ((((SimplicialObject.cosk n).obj (Over.lift U a)).obj (op ⦋n + 1⦌)).left)) :
    (hypercoveringObjectRingedAugmentation P (associatedSimplicialObject.{u} U a)
      OC).totalRingedHom.toModulesHom.pullbackModules.Faithful :=
  faithful_pullbackModules_over P (associatedSimplicialObject.{u} U a) OC
    ((isHypercovering_associatedSimplicialObject_iff U a P).mpr ⟨h₀, h₁, hmatch⟩)

/-- **Stacks 0DAB, the inclusion of the essential image in the cartesian modules.** In the
situation above, every sheaf of `O`-modules on the total site of a simplicial object of `C`
augmented to `X` which is isomorphic to a pullback `a^*F` is a cartesian `O`-module.

This is Stacks 0DA4 for the associated simplicial semi-representable object of Stacks 0GM9, and
uses no condition on `U`. -/
@[stacks 0DAB "the essential image of a^* consists of cartesian O-modules, for a hypercovering \
of X by a simplicial object of the site. Faithfulness of a^* is \
`faithful_pullbackModules_simplicialObject`; fullness of a^*, and essential surjectivity onto \
the cartesian O-modules making a_* a quasi-inverse, are not proved"]
theorem isCartesianModule_of_mem_essImage_simplicialObject
    {F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (situation (P.toGrothendieck.over X)
        (associatedSimplicialObject.{u} U a)).totalTopology))
      (hypercoveringObjectRingedAugmentation P (associatedSimplicialObject.{u} U a) OC).O)}
    (hF : (hypercoveringObjectRingedAugmentation P (associatedSimplicialObject.{u} U a)
      OC).totalRingedHom.toModulesHom.pullbackModules.essImage F) :
    (situation (P.toGrothendieck.over X)
      (associatedSimplicialObject.{u} U a)).IsModuleFiberTransitionIso
        (hypercoveringObjectRingedAugmentation P (associatedSimplicialObject.{u} U a) OC).O F :=
  isCartesianModule_of_mem_essImage_over P (associatedSimplicialObject.{u} U a) OC hF

/-- **Stacks 0DAB, the fullness half.** In the situation above, the pullback
`a^* : Mod(O_X) ⥤ Mod(O)` of sheaves of modules is full.

This is Stacks 0DA4 for the associated simplicial semi-representable object of Stacks 0GM9,
whose hypercovering condition is exactly the three hypotheses. -/
@[stacks 0DAB "a^* on sheaves of modules is full, for a hypercovering of X by a simplicial \
object of the site"]
theorem full_pullbackModules_simplicialObject
    (h₀ : Presieve.singleton (a.app (op ⦋0⦌)) ∈ P X)
    (h₁ : Presieve.singleton (oneSimplexToFiberProduct U a) ∈
      P (pullback (a.app (op ⦋0⦌)) (a.app (op ⦋0⦌))))
    (hmatch : ∀ n : ℕ, 1 ≤ n → Presieve.singleton (matchingMap U a n) ∈
      P ((((SimplicialObject.cosk n).obj (Over.lift U a)).obj (op ⦋n + 1⦌)).left)) :
    (hypercoveringObjectRingedAugmentation P (associatedSimplicialObject.{u} U a)
      OC).totalRingedHom.toModulesHom.pullbackModules.Full :=
  full_pullbackModules_over P (associatedSimplicialObject.{u} U a) OC
    ((isHypercovering_associatedSimplicialObject_iff U a P).mpr ⟨h₀, h₁, hmatch⟩)

/-- **Stacks 0DAB, full faithfulness of `a^*` on sheaves of modules.** -/
@[stacks 0DAB "a^* on sheaves of modules is fully faithful, for a hypercovering of X by a \
simplicial object of the site"]
def fullyFaithfulPullbackModulesSimplicialObject
    (h₀ : Presieve.singleton (a.app (op ⦋0⦌)) ∈ P X)
    (h₁ : Presieve.singleton (oneSimplexToFiberProduct U a) ∈
      P (pullback (a.app (op ⦋0⦌)) (a.app (op ⦋0⦌))))
    (hmatch : ∀ n : ℕ, 1 ≤ n → Presieve.singleton (matchingMap U a n) ∈
      P ((((SimplicialObject.cosk n).obj (Over.lift U a)).obj (op ⦋n + 1⦌)).left)) :
    (hypercoveringObjectRingedAugmentation P (associatedSimplicialObject.{u} U a)
      OC).totalRingedHom.toModulesHom.pullbackModules.FullyFaithful :=
  fullyFaithfulPullbackModulesOver P (associatedSimplicialObject.{u} U a) OC
    ((isHypercovering_associatedSimplicialObject_iff U a P).mpr ⟨h₀, h₁, hmatch⟩)

/-- **Stacks 0DAB, essential surjectivity onto the cartesian `O`-modules.** In the situation
above, every cartesian sheaf of `O`-modules on the total site is a pullback `a^*M`.

This is Stacks 0DA4 for the associated simplicial semi-representable object of Stacks 0GM9. -/
@[stacks 0DAB "every cartesian O-module is an a^*M, for a hypercovering of X by a simplicial \
object of the site"]
theorem essImage_pullbackModules_simplicialObject
    (h₀ : Presieve.singleton (a.app (op ⦋0⦌)) ∈ P X)
    (h₁ : Presieve.singleton (oneSimplexToFiberProduct U a) ∈
      P (pullback (a.app (op ⦋0⦌)) (a.app (op ⦋0⦌))))
    (hmatch : ∀ n : ℕ, 1 ≤ n → Presieve.singleton (matchingMap U a n) ∈
      P ((((SimplicialObject.cosk n).obj (Over.lift U a)).obj (op ⦋n + 1⦌)).left))
    {F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (situation (P.toGrothendieck.over X)
        (associatedSimplicialObject.{u} U a)).totalTopology)
      (hypercoveringObjectRingedAugmentation P (associatedSimplicialObject.{u} U a) OC).O))}
    (hF : (situation (P.toGrothendieck.over X)
      (associatedSimplicialObject.{u} U a)).IsModuleFiberTransitionIso
        (hypercoveringObjectRingedAugmentation P (associatedSimplicialObject.{u} U a) OC).O F) :
    (hypercoveringObjectRingedAugmentation P (associatedSimplicialObject.{u} U a)
      OC).totalRingedHom.toModulesHom.pullbackModules.essImage F :=
  essImage_pullbackModules_over P (associatedSimplicialObject.{u} U a) OC
    ((isHypercovering_associatedSimplicialObject_iff U a P).mpr ⟨h₀, h₁, hmatch⟩) hF

/-- **Stacks 0DAB, the essential image of `a^*` is exactly the cartesian `O`-modules.** One
inclusion is `isCartesianModule_of_mem_essImage_simplicialObject`, the other is
`essImage_pullbackModules_simplicialObject`. -/
@[stacks 0DAB "the essential image of a^* on sheaves of modules is exactly the cartesian \
O-modules, for a hypercovering of X by a simplicial object of the site"]
theorem mem_essImage_pullbackModules_iff_isCartesianModule_simplicialObject
    (h₀ : Presieve.singleton (a.app (op ⦋0⦌)) ∈ P X)
    (h₁ : Presieve.singleton (oneSimplexToFiberProduct U a) ∈
      P (pullback (a.app (op ⦋0⦌)) (a.app (op ⦋0⦌))))
    (hmatch : ∀ n : ℕ, 1 ≤ n → Presieve.singleton (matchingMap U a n) ∈
      P ((((SimplicialObject.cosk n).obj (Over.lift U a)).obj (op ⦋n + 1⦌)).left))
    (F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (situation (P.toGrothendieck.over X)
        (associatedSimplicialObject.{u} U a)).totalTopology)
      (hypercoveringObjectRingedAugmentation P (associatedSimplicialObject.{u} U a) OC).O))) :
    (hypercoveringObjectRingedAugmentation P (associatedSimplicialObject.{u} U a)
        OC).totalRingedHom.toModulesHom.pullbackModules.essImage F ↔
      (situation (P.toGrothendieck.over X)
        (associatedSimplicialObject.{u} U a)).IsModuleFiberTransitionIso
          (hypercoveringObjectRingedAugmentation P (associatedSimplicialObject.{u} U a) OC).O F :=
  mem_essImage_pullbackModules_iff_isCartesianModule_over P
    (associatedSimplicialObject.{u} U a) OC
    ((isHypercovering_associatedSimplicialObject_iff U a P).mpr ⟨h₀, h₁, hmatch⟩) F

/-- **Stacks 0DAB, `a_*` is a quasi-inverse on `Mod(O_X)`.** The unit `M ⟶ a_*a^*M` of the
adjunction of Stacks 03D7 is an isomorphism for every sheaf of `O_X`-modules. -/
@[stacks 0DAB "M = a_* a^* M on sheaves of modules, for a hypercovering of X by a simplicial \
object of the site"]
theorem isIso_pullbackAdjPushforwardModules_unit_simplicialObject
    (h₀ : Presieve.singleton (a.app (op ⦋0⦌)) ∈ P X)
    (h₁ : Presieve.singleton (oneSimplexToFiberProduct U a) ∈
      P (pullback (a.app (op ⦋0⦌)) (a.app (op ⦋0⦌))))
    (hmatch : ∀ n : ℕ, 1 ≤ n → Presieve.singleton (matchingMap U a n) ∈
      P ((((SimplicialObject.cosk n).obj (Over.lift U a)).obj (op ⦋n + 1⦌)).left)) :
    IsIso (AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules
      (hypercoveringObjectRingedAugmentation P (associatedSimplicialObject.{u} U a)
        OC).totalRingedHom).unit :=
  isIso_pullbackAdjPushforwardModules_unit_over P (associatedSimplicialObject.{u} U a) OC
    ((isHypercovering_associatedSimplicialObject_iff U a P).mpr ⟨h₀, h₁, hmatch⟩)

/-- **Stacks 0DAB, `a_*` is a quasi-inverse on the cartesian `O`-modules.** The counit
`a^*a_*F ⟶ F` of the adjunction of Stacks 03D7 is an isomorphism at every cartesian sheaf of
`O`-modules. -/
@[stacks 0DAB "a^* a_* F = F for a cartesian O-module F, for a hypercovering of X by a \
simplicial object of the site"]
theorem isIso_pullbackAdjPushforwardModules_counit_app_simplicialObject
    (h₀ : Presieve.singleton (a.app (op ⦋0⦌)) ∈ P X)
    (h₁ : Presieve.singleton (oneSimplexToFiberProduct U a) ∈
      P (pullback (a.app (op ⦋0⦌)) (a.app (op ⦋0⦌))))
    (hmatch : ∀ n : ℕ, 1 ≤ n → Presieve.singleton (matchingMap U a n) ∈
      P ((((SimplicialObject.cosk n).obj (Over.lift U a)).obj (op ⦋n + 1⦌)).left))
    {F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (situation (P.toGrothendieck.over X)
        (associatedSimplicialObject.{u} U a)).totalTopology)
      (hypercoveringObjectRingedAugmentation P (associatedSimplicialObject.{u} U a) OC).O))}
    (hF : (situation (P.toGrothendieck.over X)
      (associatedSimplicialObject.{u} U a)).IsModuleFiberTransitionIso
        (hypercoveringObjectRingedAugmentation P (associatedSimplicialObject.{u} U a) OC).O F) :
    IsIso ((AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules
      (hypercoveringObjectRingedAugmentation P (associatedSimplicialObject.{u} U a)
        OC).totalRingedHom).counit.app F) :=
  isIso_pullbackAdjPushforwardModules_counit_app_over P
    (associatedSimplicialObject.{u} U a) OC
    ((isHypercovering_associatedSimplicialObject_iff U a P).mpr ⟨h₀, h₁, hmatch⟩) hF

end CategoryTheory.SimplicialSemiRepresentable

end
