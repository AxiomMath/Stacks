module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.RightDerivedSectionsEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.InjectiveModuleSheafAcyclicityAtMorphismUniverse
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleSpacePullback.AcyclicCollapse
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 03FD over an object of a site whose objects need not be small

Let `(𝒞, J)` be a site with `𝒞 : Type u` and `Category.{v} 𝒞`, let `𝒪` be a sheaf of rings on it
and let `U` be an object of `𝒞`. Sections over `U` of a sheaf of `𝒪`-modules can be derived in
two places: in the category of sheaves of `𝒪`-modules, and in the category of abelian sheaves
after forgetting the module structure. [Stacks, Tag 03FD] says the two agree. This file proves
that **as an isomorphism**, with the universe `u` of the objects of the site unconstrained, and
identifies the result with Mathlib's `CategoryTheory.Sheaf.H'`.

`ModuleSheafCohomology.sectionsComparisonIso` is the same isomorphism for a site whose objects
form a small type, and `Stacks.Cohomology.ObjectSections.subsingleton_rightDerived_evaluation`
is the one-way transport of *vanishing* that was all this site shape had. Neither covers the
small étale site of a scheme, whose objects live in `Type (u + 1)` while its morphisms, its
structure rings and its modules live in `Type u`; this file does.

## Main results

* `Stacks.Cohomology.ObjectSections.rightDerivedSectionsToSheafIso`: **[Stacks, Tag 03FD] over an
  object of the site, as an isomorphism of functors** — deriving sections over `U` of a sheaf of
  modules and forgetting agrees, in every degree, with forgetting first and deriving sections
  over `U` of abelian sheaves. Natural in the module sheaf, by being an isomorphism of functors.
* `Stacks.Cohomology.ObjectSections.toRightDerivedZero_comp_rightDerivedSectionsToSheafIso`: the
  comparison is normalised in degree zero, intertwining the two canonical maps to the zeroth
  right derived functors. It is therefore not an arbitrary choice.
* `Stacks.Cohomology.ObjectSections.rightDerivedSectionsIsoSheafCohomology`: the composite with
  the abelian identification, so that derived module sections over `U` *are* `Sheaf.H'` of the
  underlying abelian sheaf.
* `Stacks.Cohomology.ObjectSections.rightDerivedSectionsIsoSheafCohomologyOfEssentiallySmall`:
  the same on an essentially small site, where the homological hypotheses on abelian sheaves
  are automatic.

## Implementation notes

**Why the small-site proof does not generalise.** `ModuleSheafCohomology.sectionsComparisonIso`
is `ModuleSheafCohomology.comparisonIso`, whose input is a corepresentation `G ≅
preadditiveCoyoneda.obj (op X)` of the sections functor. The values of `preadditiveCoyoneda` lie
in the universe of the *morphisms* of the sheaf category, which is `max u v`, while the sections
functor lands in the coefficients `AddCommGrpCat.{v}`; demanding that the two agree forces
`u ≤ v`. On the small étale site that asks for `u + 1 ≤ u`. This is the same obstruction that
`Stacks.Cohomology.FreeYonedaUnivLE` removes on the abelian side, and no amount of rewriting of
the `Ext`-theoretic route to the comparison removes it, because the corepresenting object is an
abelian sheaf whose sections are indexed by the morphisms of the site.

**The route taken instead.** The `δ`-functor argument of the source needs no `Ext` at all. Both
`Rⁿ(toSheaf ⋙ Γ(U, -))` and `toSheaf ⋙ RⁿΓ(U, -)` are cohomological `δ`-functors on sheaves of
modules, and both are *universal* ([Stacks, Tag 010T]): the first because right derived functors
vanish on injectives, the second because the underlying abelian sheaf of an injective sheaf of
modules is acyclic for sections over `U`. So [Stacks, Tag 010U] extends the canonical degree-zero
identification to an isomorphism of `δ`-functors, uniquely. That is
`Stacks.Cohomology.DeltaAcyclicCollapse.collapseDeltaIso`, whose three categories carry
independent universes, and the comparison here is its degreewise component.

The acyclicity it is fed is
`Stacks.Cohomology.InjectiveModuleSheafAcyclicity.\
isZero_rightDerived_sections_toSheaf_succAtMorphismUniverse`,
read as right acyclicity through [Stacks, Tag 015C]
(`Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived`). That statement is the torsion-free
dévissage of [Stacks, Tag 03FD] at a coefficient universe free of the objects of the site, which
is exactly what this site shape needs. Nothing is restated here: no new acyclicity lemma, and in
particular no second copy of the dévissage.

**The derived category.** `Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives` is
built from the `ℤ`-indexed `Functor.rightDerivedPlus`, so it needs a derived category; the
standard one is declared a local instance. The *statements* below mention only
`CategoryTheory.Functor.rightDerived`, Mathlib's `ℕ`-indexed right derived functors, which do
not, so no `HasDerivedCategory` hypothesis appears in them.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T)
* [Stacks Project, Tag 010U](https://stacks.math.columbia.edu/tag/010U)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.ObjectSections

universe v u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/- The priority raise on `SheafOfModules.instAbelian` is the one documented in
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleHigherPushforwardEtaleBaseChange.lean`: with the
module-universe-`max u v r w` instances in the import closure, instance search for `Abelian` on
the modules at the morphism universe of the site commits to them and then fails on the universe
constraint. It is `local`, so no global instance is declared. -/
attribute [local instance 5000] SheafOfModules.instAbelian

section Comparison

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] [EnoughInjectives (Sheaf J AddCommGrpCat.{v})]
  (R : Sheaf J RingCat.{v}) [EnoughInjectives (SheafOfModules.{v} R)] (U : C)

/-- **[Stacks, Tag 03FD] over an object of the site, as an isomorphism of functors.** Deriving
sections over `U` of a sheaf of `𝒪`-modules and then forgetting the module structure agrees, in
every degree, with forgetting first and deriving sections over `U` of abelian sheaves.

Being an isomorphism of functors, this is natural in the module sheaf. The universe of the
objects of the site is unconstrained, so this applies to the small étale site of a scheme, which
`ModuleSheafCohomology.sectionsComparisonIso` does not.

Both sides are universal `δ`-functors — the second by the acyclicity of the underlying abelian
sheaf of an injective sheaf of modules — so [Stacks, Tag 010U] determines the comparison from its
degree-zero component, which is the canonical one
(`toRightDerivedZero_comp_rightDerivedSectionsToSheafIso`). -/
@[ega "0 12.1.1" "partial", sga "4 V 3.5"]
def rightDerivedSectionsToSheafIso (n : ℕ) :
    (SheafOfModules.toSheaf.{v} R ⋙
        (sheafSections J AddCommGrpCat.{v}).obj (op U)).rightDerived n ≅
      SheafOfModules.toSheaf.{v} R ⋙
        ((sheafSections J AddCommGrpCat.{v}).obj (op U)).rightDerived n :=
  have := toSheaf_preservesFiniteColimits J R
  have : PreservesFiniteLimits ((sheafSections J AddCommGrpCat.{v}).obj (op U)) :=
    preservesFiniteLimits_of_natIso (sheafSectionsNatIsoEvaluation J AddCommGrpCat.{v}).symm
  have hac : ∀ I : SheafOfModules.{v} R, Injective I →
      ((sheafSections J AddCommGrpCat.{v}).obj (op U)).rightAcyclic
        ((SheafOfModules.toSheaf.{v} R).obj I) := fun I hI =>
    have := hI
    (Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived _ _).2 (fun p hp => by
      obtain ⟨q, rfl⟩ : ∃ q : ℕ, p = q + 1 := ⟨p - 1, by omega⟩
      open InjectiveModuleSheafAcyclicity in
      exact isZero_rightDerived_sections_toSheaf_succAtMorphismUniverse.{v} J R I U q)
  let e := DeltaAcyclicCollapse.collapseDeltaIso (SheafOfModules.toSheaf.{v} R)
    ((sheafSections J AddCommGrpCat.{v}).obj (op U)) hac
  { hom := e.hom.app n
    inv := e.inv.app n
    hom_inv_id := congrArg (fun η => η.app n) e.hom_inv_id
    inv_hom_id := congrArg (fun η => η.app n) e.inv_hom_id }

/-- **The degree-zero normalisation of [Stacks, Tag 03FD] over an object of the site.** The
comparison intertwines the two canonical maps to the zeroth right derived functors, both of which
are the identity of `toSheaf ⋙ Γ(U, -)` by left exactness. So the comparison is not an arbitrary
choice: this equation pins it, by [Stacks, Tag 010U]. -/
theorem toRightDerivedZero_comp_rightDerivedSectionsToSheafIso :
    (SheafOfModules.toSheaf.{v} R ⋙
          (sheafSections J AddCommGrpCat.{v}).obj (op U)).toRightDerivedZero ≫
        (rightDerivedSectionsToSheafIso J R U 0).hom =
      Functor.whiskerLeft (SheafOfModules.toSheaf.{v} R)
        ((sheafSections J AddCommGrpCat.{v}).obj (op U)).toRightDerivedZero := by
  have := toSheaf_preservesFiniteColimits J R
  have : PreservesFiniteLimits ((sheafSections J AddCommGrpCat.{v}).obj (op U)) :=
    preservesFiniteLimits_of_natIso (sheafSectionsNatIsoEvaluation J AddCommGrpCat.{v}).symm
  change _ ≫ (DeltaAcyclicCollapse.collapseDeltaIso _ _ _).hom.app 0 = _
  rw [DeltaAcyclicCollapse.collapseDeltaIso_hom_app_zero]
  simp [DeltaAcyclicCollapse.collapseZeroIso]

/-- **Derived module sections over an object of the site are the sheaf cohomology of the
underlying abelian sheaf.** The `n`-th right derived functor of sections over `U` on sheaves of
`𝒪`-modules, forgotten to abelian groups, is `Hⁿ(U, 𝓕_ab)` in the spelling
`CategoryTheory.Sheaf.H'`.

This is `rightDerivedSectionsToSheafIso` composed with
`Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections`, the purely abelian
identification of `Sheaf.H'` with right derived sections on a site whose objects need not be
small. The second factor is a choice, so no normalisation in degree zero is claimed here; for
that, use `toRightDerivedZero_comp_rightDerivedSectionsToSheafIso`. -/
@[sga "4 V 3.5" "partial"]
def rightDerivedSectionsIsoSheafCohomology (n : ℕ) (F : SheafOfModules.{v} R) :
    ((SheafOfModules.toSheaf.{v} R ⋙
        (sheafSections J AddCommGrpCat.{v}).obj (op U)).rightDerived n).obj F ≅
      Sheaf.H'.{v} ((SheafOfModules.toSheaf.{v} R).obj F) n U :=
  (rightDerivedSectionsToSheafIso J R U n).app F ≪≫
    (Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections.{v} J
      ((SheafOfModules.toSheaf.{v} R).obj F) n U).symm

end Comparison

section EssentiallySmall

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  (R : Sheaf J RingCat.{v}) [EnoughInjectives (SheafOfModules.{v} R)] (U : C)

attribute [local instance] Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite
  Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite

/-- **[Stacks, Tag 03FD] over an object of an essentially small site, as an isomorphism of
functors.** This is `rightDerivedSectionsToSheafIso` with the two homological hypotheses on
abelian sheaves discharged: on an essentially small site they form a Grothendieck abelian
category, so they have enough injectives and their `Ext`-groups lie in the morphism universe of
the site.

The small étale site of a scheme is of this kind — its objects live one universe above its
morphisms, so it is `EssentiallySmall` and never a `CategoryTheory.SmallCategory`. -/
@[sga "4 V 2.1.2" "H^q(X, special case"]
def rightDerivedSectionsToSheafIsoOfEssentiallySmall (n : ℕ) :
    (SheafOfModules.toSheaf.{v} R ⋙
        (sheafSections J AddCommGrpCat.{v}).obj (op U)).rightDerived n ≅
      SheafOfModules.toSheaf.{v} R ⋙
        ((sheafSections J AddCommGrpCat.{v}).obj (op U)).rightDerived n :=
  rightDerivedSectionsToSheafIso J R U n

/-- The degree-zero normalisation of `rightDerivedSectionsToSheafIsoOfEssentiallySmall`. -/
theorem toRightDerivedZero_comp_rightDerivedSectionsToSheafIsoOfEssentiallySmall :
    (SheafOfModules.toSheaf.{v} R ⋙
          (sheafSections J AddCommGrpCat.{v}).obj (op U)).toRightDerivedZero ≫
        (rightDerivedSectionsToSheafIsoOfEssentiallySmall J R U 0).hom =
      Functor.whiskerLeft (SheafOfModules.toSheaf.{v} R)
        ((sheafSections J AddCommGrpCat.{v}).obj (op U)).toRightDerivedZero :=
  toRightDerivedZero_comp_rightDerivedSectionsToSheafIso J R U

/-- **Derived module sections over an object of an essentially small site are the sheaf
cohomology of the underlying abelian sheaf.** This is the join the étale half of
[Stacks, Tag 071N] needs: the left-hand side is what [Stacks, Tag 072W] at a morphism of small
étale ringed sites produces, and the right-hand side is the abelian coefficients at which the
cohomology of the structure sheaf of an affine object is computed. -/
def rightDerivedSectionsIsoSheafCohomologyOfEssentiallySmall (n : ℕ) (F : SheafOfModules.{v} R) :
    ((SheafOfModules.toSheaf.{v} R ⋙
        (sheafSections J AddCommGrpCat.{v}).obj (op U)).rightDerived n).obj F ≅
      Sheaf.H'.{v} ((SheafOfModules.toSheaf.{v} R).obj F) n U :=
  rightDerivedSectionsIsoSheafCohomology J R U n F

end EssentiallySmall

end Stacks.Cohomology.ObjectSections

end
