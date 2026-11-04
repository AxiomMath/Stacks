module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkMateComp
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalkNatTrans
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsCompGeneral
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional

/-!
# The derived stalk of an iterated derived pullback, at an arbitrary model

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of schemes and `x` a point of `X`.
`StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalkComposition` builds the
two-step derived stalk computation of `Lg^* ⋙ Lf^*` from the derived stalk formula of Stacks 0098
and reduces its coherence with the composition formula of Tag 0D5S to one equation at K-flat
complexes. Every statement there is elaborated under
`attribute [local instance] HasDerivedCategory.standard`: the standard model of each derived
category involved is part of its type.

The derived stalk formula itself, `AlgebraicGeometry.derivedPullbackStalkIso`, and the derived
stalk functor are stated at an arbitrary model. This file builds the two-step computation and
proves the reduction at an arbitrary choice of the six models involved -- the derived categories
of `𝒪_X`-, `𝒪_Y`- and `𝒪_Z`-modules and of modules over the three local rings -- with those
binders written in the binder list of every declaration. The consumer that needs this generality
is the chart comparison of Stacks 0DJ8, which computes derived stalks at the locally small model
of `StacksFrontier.Homology.DerivedCategory.LocallySmall` (the global instances), not at
`HasDerivedCategory.standard`.

The constructions and proofs are those of the base modules, elaborated against the quantified
instances.

## Main definitions

* `AlgebraicGeometry.derivedStalkExtensionCompIsoGeneral`: derived extension of scalars along the
  germ map of `g` at `f x`, then along the germ map of `f` at `x`, is derived extension of
  scalars along the germ map of `f ≫ g` at `x`.
* `AlgebraicGeometry.derivedPullbackStalkCompIsoGeneral`: the two-step derived stalk computation
  `Lg^* ⋙ Lf^* ⋙ (−)_x ≅ (−)_{g (f x)} ⋙ (𝒪_{X,x} ⊗ᴸ −)`.

## Main results

* `AlgebraicGeometry.derivedPullbackStalkIso_comp_of_kFlat_general`,
  `AlgebraicGeometry.derivedPullbackStalkCompIsoGeneral_hom_eq_of_kFlat` and
  `AlgebraicGeometry.derivedPullbackStalkCompIsoGeneral_eq_of_kFlat`: the coherence, reduced to
  one equation at K-flat complexes. The equation is proved at every complex in
  `StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalkCompositionCoherence`.
* `AlgebraicGeometry.derivedStalkExtensionCompIsoGeneral_hom_app_comp_comparison`: the merged
  extension-of-scalars tail of the two-step computation, against the comparison of derived with
  degreewise extension of scalars.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry RingedSpaceModuleAdjunction
open CochainComplex.DerivedExtensionScalars
open Stacks.DerivedPullback.Composition
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open StacksDraft.DerivedExtensionScalarsComp

universe u w

namespace AlgebraicGeometry

attribute [local instance] hasDerivedCategory_ringedSpaceModules

/-- A model for the derived category of modules over the local ring of `Z` at `g (f x)` is one
for the local ring at `(f ≫ g) x`: the two points are definitionally equal, but not reducibly so,
so instance search does not pass between the two spellings on its own, and a statement mentioning
both would otherwise carry two unrelated instance arguments for one and the same category. -/
local instance hasDerivedCategory_stalk_comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {x : X} [h : HasDerivedCategory.{w} (ModuleCat.{u} (Z.presheaf.stalk (g (f x))))] :
    HasDerivedCategory.{w} (ModuleCat.{u} (Z.presheaf.stalk ((f ≫ g) x))) := h

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)

/-- **Derived extension of scalars along the germ maps composes.**  Extending scalars along the
germ map of `g` at `f x` and then along the germ map of `f` at `x` is extending scalars along the
germ map of `f ≫ g` at `x`.

This is `StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIsoGeneral` at the two
germ maps, transported along `Stacks.ModuleSkyscraper.stalkMap_hom_comp`. -/
def derivedStalkExtensionCompIsoGeneral
    [HasDerivedCategory.{w} (ModuleCat.{u} (X.presheaf.stalk x))]
    [HasDerivedCategory.{w} (ModuleCat.{u} (Y.presheaf.stalk (f x)))]
    [HasDerivedCategory.{w} (ModuleCat.{u} (Z.presheaf.stalk (g (f x))))] :
    (totalDerivedExtensionScalars.{u, u, u} (g.stalkMap (f x)).hom).functor ⋙
        (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap x).hom).functor ≅
      (totalDerivedExtensionScalars.{u, u, u} ((f ≫ g).stalkMap x).hom).functor :=
  derivedExtensionScalarsCompIsoGeneral (g.stalkMap (f x)).hom (f.stalkMap x).hom ≪≫
    eqToIso (congrArg (fun φ => (totalDerivedExtensionScalars.{u, u, u} φ).functor)
      (Stacks.ModuleSkyscraper.stalkMap_hom_comp f g x).symm)

/-- **The two-step derived stalk computation of an iterated derived pullback.**  The derived stalk
at `x` of `Lg^*` followed by `Lf^*` is the derived stalk at `g (f x)`, extended along the germ map
of `f ≫ g` at `x`.

The three steps are `AlgebraicGeometry.derivedPullbackStalkIso` for `f` at `x`, the same for `g`
at `f x`, and `derivedStalkExtensionCompIsoGeneral` to merge the two extensions of scalars. -/
def derivedPullbackStalkCompIsoGeneral
    [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]
    [HasDerivedCategory.{w} Z.Modules]
    [HasDerivedCategory.{w} (ModuleCat.{u} (X.presheaf.stalk x))]
    [HasDerivedCategory.{w} (ModuleCat.{u} (Y.presheaf.stalk (f x)))]
    [HasDerivedCategory.{w} (ModuleCat.{u} (Z.presheaf.stalk (g (f x))))] :
    derivedPullback g.toLRSHom.toShHom ⋙ derivedPullback f.toLRSHom.toShHom ⋙
        derivedStalkFunctor x ≅
      derivedStalkFunctor (g (f x)) ⋙
        (totalDerivedExtensionScalars.{u, u, u} ((f ≫ g).stalkMap x).hom).functor :=
  Functor.isoWhiskerLeft _ (derivedPullbackStalkIso f x) ≪≫
    Functor.isoWhiskerRight (derivedPullbackStalkIso g (f x))
      (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap x).hom).functor ≪≫
    Functor.isoWhiskerLeft _ (derivedStalkExtensionCompIsoGeneral f g x)

/-- **The coherence of the derived stalk formula with the composition formula of Tag 0D5S,
reduced to one equation on the K-flat class.**

Suppose that at every K-flat complex `P` of `𝒪_Z`-modules the two-step stalk computation
`derivedPullbackStalkCompIsoGeneral`, read backwards along the Tag 0D5S composition isomorphism and
composed with the comparison of derived against degreewise extension of scalars along the germ
map of `f ≫ g`, is the comparison of the derived pullback along `f ≫ g` followed by the underived
stalk formula of Stacks 0098 — that is, that it satisfies the equation which characterizes
`AlgebraicGeometry.derivedPullbackStalkIso` for `f ≫ g`.  Then the two stalk computations agree
as isomorphisms of functors on the whole unbounded derived category.

The hypothesis is a statement about degreewise data; see the implementation notes. -/
theorem derivedPullbackStalkIso_comp_of_kFlat_general
    [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]
    [HasDerivedCategory.{w} Z.Modules]
    [HasDerivedCategory.{w} (ModuleCat.{u} (X.presheaf.stalk x))]
    [HasDerivedCategory.{w} (ModuleCat.{u} (Y.presheaf.stalk (f x)))]
    [HasDerivedCategory.{w} (ModuleCat.{u} (Z.presheaf.stalk (g (f x))))]
    (hcomp : ∀ P : CochainComplex Z.Modules ℤ,
      Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Z.toSheafedSpace P →
      (derivedStalkFunctor x).map
            ((derivedPullbackCompIsoCanonical f.toLRSHom.toShHom
              g.toLRSHom.toShHom).inv.app (DerivedCategory.Q.obj P)) ≫
          (derivedPullbackStalkCompIsoGeneral f g x).hom.app (DerivedCategory.Q.obj P) ≫
          (totalDerivedExtensionScalars.{u, u, u} ((f ≫ g).stalkMap x).hom).functor.map
            ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
              ((f ≫ g) x)).mapDerivedCategoryFactors.hom.app P) ≫
          (totalDerivedExtensionScalars.{u, u, u} ((f ≫ g).stalkMap x).hom).comparison.app
            (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
              ((f ≫ g) x)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
        (derivedStalkFunctor x).map (pullbackComparisonOnComplex (f ≫ g) P) ≫
          (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategoryFactors.hom.app
            (((Scheme.Modules.pullback (f ≫ g)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex
              (Stacks.ModuleSkyscraper.pullbackStalkIso (f ≫ g) x).symm
              (ComplexShape.up ℤ)).hom.app P)) :
    (Functor.isoWhiskerRight
          (derivedPullbackCompIsoCanonical f.toLRSHom.toShHom g.toLRSHom.toShHom)
          (derivedStalkFunctor x)).inv ≫ (derivedPullbackStalkCompIsoGeneral f g x).hom =
      (derivedPullbackStalkIso (f ≫ g) x).hom :=
  derivedPullbackStalkIso_hom_eq_of_kFlat_of_iso (f ≫ g) x _ _ hcomp

/-- **The coherence, as an equality of isomorphisms.**  Under the hypothesis of
`derivedPullbackStalkIso_comp_of_kFlat_general`, the two-step derived stalk computation of an
iterated derived pullback is the Tag 0D5S composition isomorphism followed by the one-step
computation.

This is the form a consumer reasoning about the derived base change map of Stacks 08HY applies:
the composition isomorphism appears there in the adjoint description of the map, and this says
what the derived stalk does to it. -/
theorem derivedPullbackStalkCompIsoGeneral_hom_eq_of_kFlat
    [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]
    [HasDerivedCategory.{w} Z.Modules]
    [HasDerivedCategory.{w} (ModuleCat.{u} (X.presheaf.stalk x))]
    [HasDerivedCategory.{w} (ModuleCat.{u} (Y.presheaf.stalk (f x)))]
    [HasDerivedCategory.{w} (ModuleCat.{u} (Z.presheaf.stalk (g (f x))))]
    (hcomp : ∀ P : CochainComplex Z.Modules ℤ,
      Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Z.toSheafedSpace P →
      (derivedStalkFunctor x).map
            ((derivedPullbackCompIsoCanonical f.toLRSHom.toShHom
              g.toLRSHom.toShHom).inv.app (DerivedCategory.Q.obj P)) ≫
          (derivedPullbackStalkCompIsoGeneral f g x).hom.app (DerivedCategory.Q.obj P) ≫
          (totalDerivedExtensionScalars.{u, u, u} ((f ≫ g).stalkMap x).hom).functor.map
            ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
              ((f ≫ g) x)).mapDerivedCategoryFactors.hom.app P) ≫
          (totalDerivedExtensionScalars.{u, u, u} ((f ≫ g).stalkMap x).hom).comparison.app
            (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
              ((f ≫ g) x)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
        (derivedStalkFunctor x).map (pullbackComparisonOnComplex (f ≫ g) P) ≫
          (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategoryFactors.hom.app
            (((Scheme.Modules.pullback (f ≫ g)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex
              (Stacks.ModuleSkyscraper.pullbackStalkIso (f ≫ g) x).symm
              (ComplexShape.up ℤ)).hom.app P)) :
    (derivedPullbackStalkCompIsoGeneral f g x).hom =
      (Functor.isoWhiskerRight
          (derivedPullbackCompIsoCanonical f.toLRSHom.toShHom g.toLRSHom.toShHom)
          (derivedStalkFunctor x)).hom ≫ (derivedPullbackStalkIso (f ≫ g) x).hom :=
  (Iso.inv_comp_eq _).1 (derivedPullbackStalkIso_comp_of_kFlat_general f g x hcomp)

/-- **The coherence, as an isomorphism of isomorphisms.**  Under the same hypothesis the two-step
derived stalk computation *is* the Tag 0D5S composition isomorphism composed with the one-step
computation, as isomorphisms of functors. -/
theorem derivedPullbackStalkCompIsoGeneral_eq_of_kFlat
    [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]
    [HasDerivedCategory.{w} Z.Modules]
    [HasDerivedCategory.{w} (ModuleCat.{u} (X.presheaf.stalk x))]
    [HasDerivedCategory.{w} (ModuleCat.{u} (Y.presheaf.stalk (f x)))]
    [HasDerivedCategory.{w} (ModuleCat.{u} (Z.presheaf.stalk (g (f x))))]
    (hcomp : ∀ P : CochainComplex Z.Modules ℤ,
      Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Z.toSheafedSpace P →
      (derivedStalkFunctor x).map
            ((derivedPullbackCompIsoCanonical f.toLRSHom.toShHom
              g.toLRSHom.toShHom).inv.app (DerivedCategory.Q.obj P)) ≫
          (derivedPullbackStalkCompIsoGeneral f g x).hom.app (DerivedCategory.Q.obj P) ≫
          (totalDerivedExtensionScalars.{u, u, u} ((f ≫ g).stalkMap x).hom).functor.map
            ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
              ((f ≫ g) x)).mapDerivedCategoryFactors.hom.app P) ≫
          (totalDerivedExtensionScalars.{u, u, u} ((f ≫ g).stalkMap x).hom).comparison.app
            (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
              ((f ≫ g) x)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
        (derivedStalkFunctor x).map (pullbackComparisonOnComplex (f ≫ g) P) ≫
          (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategoryFactors.hom.app
            (((Scheme.Modules.pullback (f ≫ g)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex
              (Stacks.ModuleSkyscraper.pullbackStalkIso (f ≫ g) x).symm
              (ComplexShape.up ℤ)).hom.app P)) :
    derivedPullbackStalkCompIsoGeneral f g x =
      Functor.isoWhiskerRight
          (derivedPullbackCompIsoCanonical f.toLRSHom.toShHom g.toLRSHom.toShHom)
          (derivedStalkFunctor x) ≪≫ derivedPullbackStalkIso (f ≫ g) x :=
  Iso.ext (derivedPullbackStalkCompIsoGeneral_hom_eq_of_kFlat f g x hcomp)

/-- **The merged extension-of-scalars tail of the iterated derived stalk.**  At a cochain complex
`C` of `𝒪_{Z, g (f x)}`-modules, the merge `derivedStalkExtensionCompIsoGeneral` of the two derived
extensions of scalars along the germ maps, followed by the comparison of derived with degreewise
extension of scalars along the germ map of `f ≫ g`, is the comparison for `g` at `f x`, then the
comparison for `f` at `x`, then the degreewise merge `extensionScalarsComplexCompIsoGeneral`. -/
theorem derivedStalkExtensionCompIsoGeneral_hom_app_comp_comparison
    [HasDerivedCategory.{w} (ModuleCat.{u} (X.presheaf.stalk x))]
    [HasDerivedCategory.{w} (ModuleCat.{u} (Y.presheaf.stalk (f x)))]
    [HasDerivedCategory.{w} (ModuleCat.{u} (Z.presheaf.stalk (g (f x))))]
    (C : CochainComplex (ModuleCat.{u} (ToType (Z.presheaf.stalk (g (f x))))) ℤ) :
    (derivedStalkExtensionCompIsoGeneral f g x).hom.app (DerivedCategory.Q.obj C) ≫
        (totalDerivedExtensionScalars.{u, u, u} ((f ≫ g).stalkMap x).hom).comparison.app C =
      (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap x).hom).functor.map
          ((totalDerivedExtensionScalars.{u, u, u} (g.stalkMap (f x)).hom).comparison.app C) ≫
        (totalDerivedExtensionScalars.{u, u, u} (f.stalkMap x).hom).comparison.app
          (((ModuleCat.extendScalars (g.stalkMap (f x)).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C) ≫
        (StacksDraft.DerivedExtensionScalarsComp.extensionScalarsComplexCompIsoGeneral
          (g.stalkMap (f x)).hom (f.stalkMap x).hom).hom.app C ≫
        eqToHom (congrArg (fun ψ => (extensionOfScalarsComplex.{u, u, u} ψ).obj C)
          (Stacks.ModuleSkyscraper.stalkMap_hom_comp f g x).symm) :=
  derivedExtensionScalarsCompIsoGeneral_eqToIso_comp_comparison
    _ _ _ (Stacks.ModuleSkyscraper.stalkMap_hom_comp f g x) C

end AlgebraicGeometry

end
