module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.PostcomposedTotalRightDerived
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringModuleCohomologicalDescentUnconditional
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringModuleDerivedGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsAndPushforward
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringSituationGlobalSections

/-!
# Derived global sections of modules along a hypercovering of a site

Let `C` be a site with equalizers and fibre products, let `O_C` be a sheaf of commutative rings
on it, let `K` be a hypercovering of `C` and let `a : (Sh((C/K)_total), O) ⟶ (Sh(C), O_C)` be
the ringed augmentation of Stacks 0D9W, with `O = a⁻¹O_C`. **Stacks 0DA1** asserts a canonical
isomorphism

`RΓ(C, E) = RΓ((C/K)_total, La^*E)`

for `E` in the unbounded derived category `D(O_C)`. The source deduces it from Stacks 0DA0, that
`E ⟶ Ra_*La^*E` is an isomorphism, and the factorisation
`RΓ((C/K)_total, -) = RΓ(C, -) ∘ Ra_*` of Stacks 08J6 or Stacks 0D6H. Both are carried out here,
and nothing is assumed beyond the hypercovering conditions on `K`:

* `RΓ(C, -)` is the total right derived functor of global sections with values in
  `D(Γ(C, O_C))`, and `RΓ((C/K)_total, -)` that of global sections with values in
  `D(Γ((C/K)_total, O))`. The two sides are modules over different rings; the right hand side is
  read in `D(Γ(C, O_C))` through restriction of scalars along the ring map
  `Γ(C, O_C) ⟶ Γ((C/K)_total, O)` induced by `a`, as Stacks 0D6H reads `RΓ(C, -)` in
  `D(Γ(O_D))`.
* `E ⟶ Ra_*La^*E` is invertible: Stacks 0DA0, in the namespace
  `CategoryTheory.SimplicialSemiRepresentable`, as
  `isIso_derivedPullbackPushforwardUnit_of_hypercoveringOfTerminal`.
* `RΓ(C, Ra_*F) = RΓ((C/K)_total, F)` is the derived half of Stacks 08J6, proved for any morphism
  of ringed topoi with invertible structure map from the underived identity
  `Γ(C, a_*F) = Γ((C/K)_total, F)` of `Γ(C, O_C)`-modules
  (`Stacks.Cohomology.SiteModules.globalSectionsPushforwardIso`) and the preservation of
  K-injective complexes by `a_*`
  (`AlgebraicGeometry.RingedToposHom.isKInjective_pushforwardModules`), together with the exactness
  of restriction of scalars.

The isomorphism is one of functors on all of `D(O_C)`, and its forward map at `E` is `RΓ(C, -)`
of the derived unit `E ⟶ Ra_*La^*E` followed by the factorisation of Stacks 08J6
(`derivedLinearGlobalSectionsPullbackIsoOfHypercovering_hom_app`).

## Main definitions

* `AlgebraicGeometry.RingedTopos.derivedLinearGlobalSections`: `RΓ(Z, -) : D(O_Z) ⥤ D(Γ(O_Z))`.
* `AlgebraicGeometry.RingedToposHom.pushforwardModulesLinearGlobalSectionsIso`: the underived
  identity `Γ(D, f_*F) = Γ(C, F)` of `Γ(O_D)`-modules.
* `AlgebraicGeometry.RingedToposHom.derivedLinearGlobalSectionsPushforwardIso`: the derived half
  of Stacks 08J6 in `D(Γ(O_D))`, for a morphism of ringed topoi with invertible structure map.
* `AlgebraicGeometry.RingedToposHom.derivedLinearGlobalSectionsPullbackIso`:
  `RΓ(D, E) = RΓ(C, Lf^*E)` in `D(Γ(O_D))` once `E ⟶ Rf_*Lf^*E` is invertible.
* `Stacks.CategoryTheory.Hypercovering.derivedLinearGlobalSectionsPullbackIsoOfHypercovering`:
  **Stacks 0DA1**, under exactly the source's hypotheses. It and its `_hom_app` are the
  declarations registered for the tag.
* `Stacks.CategoryTheory.Hypercovering.derivedGlobalSectionsPullbackIsoOfHypercoveringOfTerminal`:
  the same isomorphism read in `D(Ab)`, the module structure of global sections forgotten. It is
  the declaration `derivedGlobalSectionsPullbackIsoOfHypercovering` of
  `HypercoveringModuleDerivedGlobalSections.lean` with its three hypothesis arguments supplied by
  theorems: the module form of Stacks 0D8E, the `Ra_*`-acyclicity of `a^*` of a K-injective
  complex, and the underived identity `Γ(C, a_*F) = Γ((C/K)_total, F)`
  (`pushforwardModulesGlobalSectionsIsoOfHypercovering`).

## References

* [Stacks Project, Tag 0DA1](https://stacks.math.columbia.edu/tag/0DA1)
* [Stacks Project, Tag 0DA0](https://stacks.math.columbia.edu/tag/0DA0)
* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
* [Stacks Project, Tag 0D9W](https://stacks.math.columbia.edu/tag/0D9W)
* [Stacks Project, Tag 093Y](https://stacks.math.columbia.edu/tag/093Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward Stacks.Cohomology.SiteModules

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedTopos

variable (Z : RingedTopos.{u, u, u}) [Z.J.HasSheafCompose (forget RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- `RΓ(Z, -) : D(O_Z) ⥤ D(Γ(O_Z))`: the total right derived functor, on the unbounded derived
category, of global sections of sheaves of modules on a ringed topos, taken as modules over the
ring `Γ(O_Z)` of global sections of the structure sheaf (Stacks 071H). -/
abbrev derivedLinearGlobalSections :
    DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J)) Z.O)) ⥤
      DerivedCategory (ModuleCat.{u} (GlobalSectionRing
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J)) Z.O))) :=
  Stacks.DerivedFunctor.totalRightDerived
    (globalSectionsFunctor.{u, u, u, u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J)) Z.O))

end AlgebraicGeometry.RingedTopos

namespace AlgebraicGeometry.RingedToposHom

section

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

/-- **The underived identity behind Stacks 08J6, as modules:** `Γ(D, f_*F) = Γ(C, F)` as
`Γ(O_D)`-modules, naturally in the `O_C`-module `F`, the right hand side read through restriction
of scalars along the ring map `Γ(O_D) ⟶ Γ(O_C)` induced by `f`. This is
`Stacks.Cohomology.SiteModules.globalSectionsPushforwardIso` for the four-field form of `f`,
transported along `AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso`. -/
def pushforwardModulesLinearGlobalSectionsIso :
    pushforwardModules f ⋙
        globalSectionsFunctor.{u, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) ≅
      globalSectionsFunctor.{u, u, u, u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
        ModuleCat.restrictScalars.{u} (globalSectionsRingHom f.toModulesHom) :=
  Functor.isoWhiskerRight f.toModulesPushforwardIso.symm _ ≪≫
    globalSectionsPushforwardIso f.toModulesHom

/-- **The derived half of Stacks 08J6, as modules:** for a morphism of ringed topoi with
invertible structure map, `RΓ(D, -) ∘ Rf_* = RΓ(C, -)` as functors `D(O_C) ⥤ D(Γ(O_D))`, the
right hand side read through restriction of scalars along `Γ(O_D) ⟶ Γ(O_C)`.

Both sides are derived from the same functor `Γ(D, f_*-)` on the unbounded homotopy category,
by `pushforwardModulesLinearGlobalSectionsIso`; the left hand side is a right derived functor of
it because `f_*` preserves K-injective complexes (`isKInjective_pushforwardModules`, Stacks
093Y), and restriction of scalars, being exact, commutes with total right derivation. -/
def derivedLinearGlobalSectionsPushforwardIso :
    derivedPushforward (X := X) (Y := Y) f ⋙ RingedTopos.derivedLinearGlobalSections Y ≅
      RingedTopos.derivedLinearGlobalSections X ⋙
        (ModuleCat.restrictScalars.{u} (globalSectionsRingHom f.toModulesHom)).mapDerivedCategory :=
  Stacks.Cohomology.LerayUnbounded.derivedCompIso _ _ _
      (pushforwardModulesLinearGlobalSectionsIso f) (isKInjective_pushforwardModules f) ≪≫
    (Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso _ _).symm

/-- **`RΓ(D, E) = RΓ(C, Lf^*E)` in `D(Γ(O_D))`**, for a morphism of ringed topoi with invertible
structure map at which the canonical map `E ⟶ Rf_*Lf^*E` is an isomorphism for every `E`: that
map, followed by `derivedLinearGlobalSectionsPushforwardIso`. -/
def derivedLinearGlobalSectionsPullbackIso (h : IsIso (derivedPullbackPushforwardUnit f)) :
    RingedTopos.derivedLinearGlobalSections Y ≅
      (leftDerivedPullbackOfIsIsoFSharp f).functor ⋙ RingedTopos.derivedLinearGlobalSections X ⋙
        (ModuleCat.restrictScalars.{u} (globalSectionsRingHom f.toModulesHom)).mapDerivedCategory :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (@asIso _ _ _ _ (derivedPullbackPushforwardUnit f) h)
      (RingedTopos.derivedLinearGlobalSections Y) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (leftDerivedPullbackOfIsIsoFSharp f).functor
      (derivedLinearGlobalSectionsPushforwardIso f)

/-- The forward map of `derivedLinearGlobalSectionsPullbackIso` at `E` is `RΓ(D, -)` of the
canonical map `E ⟶ Rf_*Lf^*E`, followed by the factorisation of Stacks 08J6. -/
theorem derivedLinearGlobalSectionsPullbackIso_hom_app
    (h : IsIso (derivedPullbackPushforwardUnit f))
    (E : DerivedCategory (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))) :
    (derivedLinearGlobalSectionsPullbackIso f h).hom.app E =
      (RingedTopos.derivedLinearGlobalSections Y).map
          ((derivedPullbackPushforwardUnit f).app E) ≫
        (derivedLinearGlobalSectionsPushforwardIso f).hom.app
          ((leftDerivedPullbackOfIsIsoFSharp f).functor.obj E) := by
  simp only [derivedLinearGlobalSectionsPullbackIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.associator_hom_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, asIso_hom, Category.id_comp]

end

end AlgebraicGeometry.RingedToposHom

namespace Stacks.CategoryTheory.Hypercovering

open CategoryTheory.SimplicialSiteSituation CategoryTheory.SimplicialSemiRepresentable

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyComponent

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (J : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u} J) (OC : Sheaf J.toGrothendieck CommRingCat.{u})

/-- **Stacks 0DA1.** Let `C` be a site with equalizers and fibre products, let `O_C` be a sheaf of
commutative rings on it and let `K` be a hypercovering of `C`. With `O = a⁻¹O_C` on the total
site and `a : (Sh((C/K)_total), O) ⟶ (Sh(C), O_C)` the ringed augmentation of Stacks 0D9W, there
is a canonical isomorphism

`RΓ(C, E) = RΓ((C/K)_total, La^*E)`

naturally in `E` in the unbounded derived category `D(O_C)`. Here `RΓ(C, -)` takes values in
`D(Γ(C, O_C))`, and the right hand side, which lives in `D(Γ((C/K)_total, O))`, is read in
`D(Γ(C, O_C))` through restriction of scalars along the ring map `Γ(C, O_C) ⟶ Γ((C/K)_total, O)`
induced by `a`. Nothing is assumed beyond the hypercovering conditions on `K`. The forward map is
pinned to the canonical one by `derivedLinearGlobalSectionsPullbackIsoOfHypercovering_hom_app`.

This is the complete statement of the tag, and it supersedes the conditional
`derivedGlobalSectionsPullbackIsoOfHypercovering` of `HypercoveringModuleDerivedGlobalSections`,
which no longer carries the tag: that isomorphism is read only in `D(Ab)` and takes as
hypotheses `hunit` (the module form of Stacks 0D8E), `hacyclic` (`a^*` of a K-injective complex
computes `Ra_*`) and `hΓ` (the underived identity `Γ(C, a_*F) = Γ((C/K)_total, F)`). All three
are theorems, and `derivedGlobalSectionsPullbackIsoOfHypercoveringOfTerminal` below is that
isomorphism with them supplied. -/
@[stacks 0DA1]
def derivedLinearGlobalSectionsPullbackIsoOfHypercovering :
    RingedTopos.derivedLinearGlobalSections
        (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos ≅
      (RingedToposHom.leftDerivedPullbackOfIsIsoFSharp
          (X := (hypercoveringSituation J H).totalRingedTopos
            (hypercoveringRingedAugmentation J H OC).O)
          (Y := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos)
          (hypercoveringRingedAugmentation J H OC).totalRingedHom).functor ⋙
        RingedTopos.derivedLinearGlobalSections
          ((hypercoveringSituation J H).totalRingedTopos
            (hypercoveringRingedAugmentation J H OC).O) ⋙
        (ModuleCat.restrictScalars.{u} (globalSectionsRingHom
          (X := (hypercoveringSituation J H).totalRingedTopos
            (hypercoveringRingedAugmentation J H OC).O)
          (Y := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos)
          (hypercoveringRingedAugmentation J H OC).totalRingedHom.toModulesHom)).mapDerivedCategory
    :=
  RingedToposHom.derivedLinearGlobalSectionsPullbackIso
    (hypercoveringRingedAugmentation J H OC).totalRingedHom
    (isIso_derivedPullbackPushforwardUnit_of_hypercoveringOfTerminal J H OC)

/-- **Stacks 0DA1, the isomorphism is the canonical one.** At every `E` of `D(O_C)` its forward
map is `RΓ(C, -)` of the derived unit `E ⟶ Ra_*La^*E` of the ringed augmentation, followed by the
factorisation `RΓ(C, Ra_*-) = RΓ((C/K)_total, -)` of Stacks 08J6. -/
@[stacks 0DA1 "the forward map of the isomorphism is the canonical one: RΓ(C, -) of the derived \
unit E ⟶ Ra_*La^*E, followed by the factorisation of Tag 08J6"]
theorem derivedLinearGlobalSectionsPullbackIsoOfHypercovering_hom_app
    (E : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (J := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos.J))
      (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos.O))) :
    (derivedLinearGlobalSectionsPullbackIsoOfHypercovering J H OC).hom.app E =
      (RingedTopos.derivedLinearGlobalSections
          (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos).map
          ((RingedToposHom.derivedPullbackPushforwardUnit
            (hypercoveringRingedAugmentation J H OC).totalRingedHom).app E) ≫
        (RingedToposHom.derivedLinearGlobalSectionsPushforwardIso
          (hypercoveringRingedAugmentation J H OC).totalRingedHom).hom.app
          ((RingedToposHom.leftDerivedPullbackOfIsIsoFSharp
            (X := (hypercoveringSituation J H).totalRingedTopos
              (hypercoveringRingedAugmentation J H OC).O)
            (Y := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos)
            (hypercoveringRingedAugmentation J H OC).totalRingedHom).functor.obj E) :=
  RingedToposHom.derivedLinearGlobalSectionsPullbackIso_hom_app _ _ E

/-- **The underived identity `Γ(C, a_*F) = Γ((C/K)_total, F)` on sheaves of modules, read in
abelian groups**, for the ringed augmentation of a hypercovering: the underlying abelian sheaf of
`a_*F` is the abelian direct image of that of `F`
(`inverseImageRingedAugmentationPushforwardToSheafIso`), and global sections of an abelian direct
image along the augmentation are global sections on the total site
(`CategoryTheory.SimplicialSemiRepresentable.abelianTotalPushforwardGammaIso`). This is the `hΓ`
of `derivedGlobalSectionsPullbackIsoOfHypercovering`. -/
def pushforwardModulesGlobalSectionsIsoOfHypercovering :
    AlgebraicGeometry.RingedToposHom.pushforwardModules
          (X := (hypercoveringSituation J H).totalRingedTopos
            (hypercoveringRingedAugmentation J H OC).O)
          (Y := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos)
          (hypercoveringRingedAugmentation J H OC).totalRingedHom ⋙
        AlgebraicGeometry.RingedTopos.moduleGlobalSections
          (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos ≅
      AlgebraicGeometry.RingedTopos.moduleGlobalSections
        ((hypercoveringSituation J H).totalRingedTopos
          (hypercoveringRingedAugmentation J H OC).O) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (inverseImageRingedAugmentationPushforwardToSheafIso (hypercoveringSituation J H)
        (Cat.of C) J.toGrothendieck (hypercoveringAugmentation J H) OC)
      (Sheaf.Γ J.toGrothendieck AddCommGrpCat.{u}) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (abelianTotalPushforwardGammaIso J.toGrothendieck H.toSimplicialObject)

/-- **Stacks 0DA1 read in `D(Ab)`**: `RΓ(C, E) = RΓ((C/K)_total, La^*E)` with the module
structure of global sections forgotten. This is
`derivedGlobalSectionsPullbackIsoOfHypercovering` with its three hypotheses proved:
`isIso_pullbackAdjPushforwardModules_unit_of_hypercoveringOfTerminal` (the module form of
Stacks 0D8E), `pullbackComputesDerivedPushforward_of_hypercoveringOfTerminal` and
`pushforwardModulesGlobalSectionsIsoOfHypercovering`. The statement of record, in
`D(Γ(C, O_C))`, is `derivedLinearGlobalSectionsPullbackIsoOfHypercovering`. -/
def derivedGlobalSectionsPullbackIsoOfHypercoveringOfTerminal :
    AlgebraicGeometry.RingedTopos.derivedModuleGlobalSections
        (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos ≅
      (AlgebraicGeometry.RingedToposHom.leftDerivedPullbackOfIsIsoFSharp
          (X := (hypercoveringSituation J H).totalRingedTopos
            (hypercoveringRingedAugmentation J H OC).O)
          (Y := (hypercoveringRingedAugmentation J H OC).augmentationRingedTopos)
          (hypercoveringRingedAugmentation J H OC).totalRingedHom).functor ⋙
        AlgebraicGeometry.RingedTopos.derivedModuleGlobalSections
          ((hypercoveringSituation J H).totalRingedTopos
            (hypercoveringRingedAugmentation J H OC).O) :=
  derivedGlobalSectionsPullbackIsoOfHypercovering J H OC
    (isIso_pullbackAdjPushforwardModules_unit_of_hypercoveringOfTerminal J H OC)
    (pullbackComputesDerivedPushforward_of_hypercoveringOfTerminal J H OC)
    (pushforwardModulesGlobalSectionsIsoOfHypercovering J H OC)

end Stacks.CategoryTheory.Hypercovering

end
