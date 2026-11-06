module

public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.HigherDirectImages

/-!
# Higher direct images of bounded below complexes of modules and of abelian sheaves

Let `f : X ⟶ Y` be a morphism of ringed spaces.  Write `E` for the pushforward of sheaves of
modules along `f`, `S` and `T` for the forgetful functors from sheaves of modules on `Y`
respectively on `X` to sheaves of abelian groups, and `A` for the pushforward of abelian
sheaves along `f`.  This file proves the bounded below form of Stacks 01F1 part (2): the two
composites of bounded below right derived functors `RE ∘ RS` and `RT ∘ RA` of functors
`D⁺(Mod(𝒪_X)) ⥤ D⁺(Ab(Y))` are canonically isomorphic, and the isomorphism is the one
intertwining the two comparison transformations of Stacks 05T2.

## Main results

* `isRightDerivedFunctor_comp_of_rightAcyclic_obj_injective`: for additive functors `F` and
  `G` out of categories with enough injectives, the composite `RF ∘ RG` *is* the right derived
  functor of `G ∘ F`, with the comparison transformation of Stacks 05T2 as its unit, as soon as
  `F` carries injective objects to `G`-acyclic ones.
* `rightDerivedFunctorPlus_modulePushforward_forget_iso` is Stacks 01F1 part (2) for bounded
  below complexes, and `rightDerivedFunctorPlus_modulePushforward_forget_iso_unit` says that
  it is the canonical comparison.

## Implementation notes

The construction is pure uniqueness of right derived functors.  The two composites
`E ⋙ S` and `T ⋙ A` are definitionally the same functor `Mod(𝒪_X) ⥤ Ab(Y)`, by
`modulePushforwardCompToSheafIso`; so `modulePushforwardDerivedUnit f` and
`abelianPushforwardDerivedUnit f` are two transformations out of *the same* functor
`K⁺(Mod(𝒪_X)) ⥤ D⁺(Ab(Y))`, and the content of the statement is that each of them exhibits
its target as a right derived functor along `DerivedCategory.Plus.Qh`.  Then
`Functor.rightDerivedNatIso` applied to the identity isomorphism produces the comparison and
`Functor.rightDerivedNatTrans_fac` is exactly the unit equation.

That both units exhibit right derived functors is one instance of Stacks 015M,
`Functor.isIso_iff_rightAcyclic_obj_injective`: the canonical map
`R(G ∘ F) ⟶ RG ∘ RF` is invertible precisely when `F` sends injective objects to `G`-acyclic
ones, and an invertible map out of a right derived functor transports the universal property.
This is `isRightDerivedFunctor_comp_of_rightAcyclic_obj_injective`.  Its hypothesis is
`rightAcyclic_abelianPushforward_toSheaf_obj_of_injective` for the pair `(T, A)`, and is free
for the pair `(E, S)` because `S` is exact, so the unit of `RS` is invertible everywhere by
`Stacks.Cohomology.HigherDirectImage.isIso_rightDerivedFunctorPlusUnit`.

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.ModulePushforwardComparison

-- As in `StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors`:
-- everything below mentions `Functor.rightDerivedFunctorPlus`, whose pointwise existence
-- instance search would otherwise try to establish by proving termwise injectivity of an
-- unknown complex, so the cheap instance coming from `EnoughInjectives` is given precedence.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### The composite of two bounded below right derived functors -/

section Composite

variable {C : Type*} {D : Type*} {E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

/-- **The composite of the bounded below right derived functors is a right derived functor of
the composite.**  If `F` carries the injective objects of `𝒜` to objects right acyclic for `G`
then `RG ∘ RF`, together with the comparison transformation of Stacks 05T2 assembled from the
units of `RG` and of `RF`, is a right derived functor of `G ∘ F` along the localization
`Qh : K⁺(𝒜) ⥤ D⁺(𝒜)`.

Stacks 015M (`Functor.isIso_iff_rightAcyclic_obj_injective`) says that the canonical map from
`R(G ∘ F)` factoring the comparison transformation is invertible under exactly that hypothesis,
and `Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc` turns invertibility of that map
into the universal property for the comparison transformation itself. -/
theorem isRightDerivedFunctor_comp_of_rightAcyclic_obj_injective (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [EnoughInjectives C] [EnoughInjectives D]
    (h : ∀ I : C, Injective I → G.rightAcyclic (F.obj I)) :
    (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (Functor.whiskerRight
          (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv
          DerivedCategory.Plus.Qh ≫
        Functor.whiskerLeft F.mapHomotopyCategoryPlus G.rightDerivedFunctorPlusUnith ≫
        Functor.whiskerRight F.rightDerivedFunctorPlusUnith G.rightDerivedFunctorPlus)
      (HomotopyCategory.Plus.quasiIso C) :=
  (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
      (F ⋙ G).rightDerivedFunctorPlus (F ⋙ G).rightDerivedFunctorPlusUnith
      (HomotopyCategory.Plus.quasiIso C) _ _).2
    ((Functor.isIso_iff_rightAcyclic_obj_injective F G _
      (Functor.rightDerived_fac _ _ _ _ _)).2 h)

end Composite

/-! ### Stacks 01F1, part (2), for bounded below complexes -/

section HigherDirectImage

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

attribute [local instance] HasDerivedCategory.standard

/-- The unit from ordinary module pushforward followed by forgetting to the composite of
the corresponding bounded-below right derived functors. -/
noncomputable def modulePushforwardDerivedUnit :
    (modulePushforward f ⋙ SheafOfModules.toSheaf (structureSheafRing Y)).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ (modulePushforward f).rightDerivedFunctorPlus ⋙
        (SheafOfModules.toSheaf (structureSheafRing Y)).rightDerivedFunctorPlus :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryPlusCompIso
        (Iso.refl (modulePushforward f ⋙
          SheafOfModules.toSheaf (structureSheafRing Y)))).inv DerivedCategory.Plus.Qh ≫
    Functor.whiskerLeft (modulePushforward f).mapHomotopyCategoryPlus
      (SheafOfModules.toSheaf (structureSheafRing Y)).rightDerivedFunctorPlusUnith ≫
    Functor.whiskerRight (modulePushforward f).rightDerivedFunctorPlusUnith
      (SheafOfModules.toSheaf (structureSheafRing Y)).rightDerivedFunctorPlus

/-- The unit from ordinary pushforward after forgetting to abelian sheaves to the composite
of the corresponding bounded-below right derived functors. -/
noncomputable def abelianPushforwardDerivedUnit :
    (SheafOfModules.toSheaf (structureSheafRing X) ⋙
      (opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology Y.carrier)
        (Opens.grothendieckTopology X.carrier)).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙
        (SheafOfModules.toSheaf (structureSheafRing X)).rightDerivedFunctorPlus ⋙
        ((opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
          (Opens.grothendieckTopology Y.carrier)
          (Opens.grothendieckTopology X.carrier)).rightDerivedFunctorPlus :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryPlusCompIso
        (Iso.refl (SheafOfModules.toSheaf (structureSheafRing X) ⋙
          (opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
            (Opens.grothendieckTopology Y.carrier)
            (Opens.grothendieckTopology X.carrier)))).inv DerivedCategory.Plus.Qh ≫
    Functor.whiskerLeft (SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategoryPlus
      ((opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology Y.carrier)
        (Opens.grothendieckTopology X.carrier)).rightDerivedFunctorPlusUnith ≫
    Functor.whiskerRight
      (SheafOfModules.toSheaf (structureSheafRing X)).rightDerivedFunctorPlusUnith
      ((opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology Y.carrier)
        (Opens.grothendieckTopology X.carrier)).rightDerivedFunctorPlus

/-- **The module side is a right derived functor.**  Deriving the module pushforward and then
deriving the forgetful functor is a right derived functor of the composite, with
`modulePushforwardDerivedUnit` as its unit.  The acyclicity hypothesis is free here: the
forgetful functor to abelian sheaves is exact, so the unit of its bounded below right derived
functor is invertible at every bounded below complex, in particular at every single complex. -/
instance isRightDerivedFunctor_modulePushforwardDerivedUnit :
    ((modulePushforward f).rightDerivedFunctorPlus ⋙
      (SheafOfModules.toSheaf (structureSheafRing Y)).rightDerivedFunctorPlus).IsRightDerivedFunctor
      (modulePushforwardDerivedUnit f)
      (HomotopyCategory.Plus.quasiIso (SheafOfModules.{u} (structureSheafRing X))) :=
  isRightDerivedFunctor_comp_of_rightAcyclic_obj_injective _ _ fun _ _ =>
    have hinv :
        (HomotopyCategory.Plus.quasiIso (SheafOfModules.{u} (structureSheafRing Y))).IsInvertedBy
        ((SheafOfModules.toSheaf (structureSheafRing Y)).mapHomotopyCategoryPlus ⋙
          DerivedCategory.Plus.Qh) := fun _ _ φ hφ =>
      Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso _) _
        (Stacks.Cohomology.HigherDirectImage.quasiIso_mapHomotopyCategoryPlus_map
          (SheafOfModules.toSheaf (structureSheafRing Y)) φ hφ)
    by
      unfold Functor.rightAcyclic
      refine @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ ?_ _
      exact Functor.isIso_of_isRightDerivedFunctor_of_inverts _ _ hinv

/-- **The abelian side is a right derived functor.**  Deriving the forgetful functor and then
deriving the abelian pushforward is a right derived functor of the composite, with
`abelianPushforwardDerivedUnit` as its unit.  The acyclicity hypothesis is
`rightAcyclic_abelianPushforward_toSheaf_obj_of_injective`. -/
instance isRightDerivedFunctor_abelianPushforwardDerivedUnit :
    ((SheafOfModules.toSheaf (structureSheafRing X)).rightDerivedFunctorPlus ⋙
        ((opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
          (Opens.grothendieckTopology Y.carrier)
          (Opens.grothendieckTopology X.carrier)).rightDerivedFunctorPlus).IsRightDerivedFunctor
      (abelianPushforwardDerivedUnit f)
      (HomotopyCategory.Plus.quasiIso (SheafOfModules.{u} (structureSheafRing X))) :=
  isRightDerivedFunctor_comp_of_rightAcyclic_obj_injective _ _
    fun M hM => rightAcyclic_abelianPushforward_toSheaf_obj_of_injective f M hM

/-- The comparison between module and abelian-sheaf higher direct images is valid for
bounded below complexes and is natural in the complex. -/
@[stacks 01F1 "bounded below complexes, part (2)"]
noncomputable def rightDerivedFunctorPlus_modulePushforward_forget_iso :
    (modulePushforward f).rightDerivedFunctorPlus ⋙
        (SheafOfModules.toSheaf (structureSheafRing Y)).rightDerivedFunctorPlus ≅
      (SheafOfModules.toSheaf (structureSheafRing X)).rightDerivedFunctorPlus ⋙
        ((opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
          (Opens.grothendieckTopology Y.carrier)
          (Opens.grothendieckTopology X.carrier)).rightDerivedFunctorPlus :=
  Functor.rightDerivedNatIso _ _ (modulePushforwardDerivedUnit f)
    (abelianPushforwardDerivedUnit f)
    (HomotopyCategory.Plus.quasiIso (SheafOfModules.{u} (structureSheafRing X))) (Iso.refl _)

/-- The bounded-below higher-direct-image comparison is the canonical one: it intertwines
the units from ordinary pushforward. -/
@[stacks 01F1 "bounded below complexes, part (2), canonical comparison"]
theorem rightDerivedFunctorPlus_modulePushforward_forget_iso_unit :
    modulePushforwardDerivedUnit f ≫
        Functor.whiskerLeft DerivedCategory.Plus.Qh
          (rightDerivedFunctorPlus_modulePushforward_forget_iso f).hom =
      abelianPushforwardDerivedUnit f :=
  (Functor.rightDerivedNatTrans_fac _ _ (modulePushforwardDerivedUnit f)
      (abelianPushforwardDerivedUnit f)
      (HomotopyCategory.Plus.quasiIso (SheafOfModules.{u} (structureSheafRing X)))
      (Iso.refl _).hom).trans (Category.id_comp _)

end HigherDirectImage

end Stacks.Cohomology.ModulePushforwardComparison

end
