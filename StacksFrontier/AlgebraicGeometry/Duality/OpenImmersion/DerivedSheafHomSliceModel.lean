module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardClosedImmersion
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedRestrictionToOpens

/-!
# Restriction of the derived internal Hom to an open subscheme, in Mathlib's idiom

Let `X` be a scheme and `U ⊆ X` an open subscheme. [Stacks, Tag 08DL] says that the derived
internal Hom commutes with restriction to `U`, and the library carries that statement for the
*slice site* `Opens X / U`: `Stacks.SheafOfModules.derivedSheafHomRestrictionIso` identifies

`RSheafHom_{𝒪_X}(K, L)|_U ≅ RSheafHom_{𝒪_U}(K|_U, L|_U)`

where `(-)|_U` is `Stacks.SheafOfModules.derivedRestrict`, the functor induced on derived
categories by `SheafOfModules.overFunctor`, and `𝒪_U`-modules are modelled as modules over
`X.ringCatSheaf.over U`.

A consumer who wants to pass from `X` to the *open subscheme* `U.toScheme` — to recognize `U` as
`Spec Γ(X, U)` when `U` is affine, say — works instead with Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι`, whose target is `U.toScheme.Modules`.
This file supplies the missing comparison between the two models on derived categories, and
rereads the slice-site comparison of Stacks 08DL through it.

At the level of abelian categories the comparison is Mathlib's
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`: restriction to the slice site followed by
the equivalence `AlgebraicGeometry.Scheme.Modules.overEquiv` between the slice-site model and
the open-subscheme model is restriction along `U.ι`. All three functors are exact, so that
isomorphism is carried to derived categories by
`CategoryTheory.Functor.mapDerivedCategoryCompIso`.

## Main definitions

* `Stacks.SheafOfModules.derivedOverFunctorEquiv`: **the model comparison on derived
  categories.** Derived restriction to the slice site over `U`, followed by the equivalence
  between the slice-site and open-subscheme models of `𝒪_U`-modules, is the derived restriction
  along the open immersion `U.ι`.
* `Stacks.SheafOfModules.derivedSheafHomSchemeRestriction`: the comparison of Stacks 08DL with
  its left-hand side read in the open-subscheme model, i.e. the restriction along `U.ι` of
  `RSheafHom_{𝒪_X}(K, L)`.

## Main results

* `Stacks.SheafOfModules.derivedSheafHomSchemeRestriction_natural_left` and
  `Stacks.SheafOfModules.derivedSheafHomSchemeRestriction_natural_right`: the reread comparison
  is natural in each of the two variables, since both of the isomorphisms it is composed of are.

## What is not proved

This is a change of model for the *restriction functor*, not for the derived internal Hom. The
right-hand side of `derivedSheafHomSchemeRestriction` is still the derived internal Hom of the
slice site `Opens X / U`, carried into the open-subscheme model by the equivalence `overEquiv`;
it is *not* `Stacks.SheafOfModules.derivedSheafHom U.toScheme.sheaf` applied to the restricted
arguments. Identifying the two needs the derived internal Hom to be invariant under the
equivalence of ringed sites underlying `overEquiv`.

**The abelian-level half of that is available.** It is a transport of
`AlgebraicGeometry.RingedSite.internalHomSheaf` along an arbitrary equivalence of ringed sites,
generalizing `Stacks.SheafOfModules.InternalHom.internalHomOverIso` ([Stacks, Tag 0E8H]) from
restriction to a slice site; it is
`Stacks.SheafOfModules.InternalHom.siteEquivInternalHomIso`, whose hypotheses are exactly the
data of `SheafOfModules.pushforwardPushforwardEquivalence` — which `overEquiv` is — with
`Stacks.SheafOfModules.InternalHom.siteEquivInternalHomIsoOfIso` the form taking only an
invertible structure map, and `Stacks.SheafOfModules.InternalHom.siteEquivInternalHomIso_hom_app`
pinning it on sections. What is still missing is the derived-level statement, which would follow
the pattern of `AlgebraicGeometry.RingedSite.derivedHomRestriction`. Until that exists, nothing
here states Stacks 08DL for the derived internal Hom of the scheme `U.toScheme`, and nothing
here carries a `@[stacks]` attribute.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def`, not an `abbrev`, while
`Stacks.SheafOfModules.StructureSheafModules Rc` and `SheafOfModules X.ringCatSheaf` are
`abbrev`s. The three spellings of the category of `𝒪_X`-modules are therefore definitionally but
not reducibly equal, so instance synthesis for a functor written in one spelling fails while the
other is in force. Every exactness instance of `derivedOverFunctorEquiv` is consequently
supplied as a term, as in
`AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor`.

`X.ringCatSheaf` and `Stacks.SheafOfModules.structureSheaf X.sheaf` are the same term — both are
`(sheafCompose _ (forget₂ CommRingCat RingCat)).obj X.sheaf` — so the statements of
`StacksFrontier/Topology/Sheaves/Cohomology/InternalHom/DerivedRestrictionToOpens.lean` apply to a
scheme's structure sheaf with no comparison layer.

## References

* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

namespace Stacks.SheafOfModules

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}} (U : X.Opens)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [HasSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}]
  [PreservesFiniteLimits (SheafOfModules.overFunctor.{u} X.ringCatSheaf U)]
  [PreservesFiniteColimits (SheafOfModules.overFunctor.{u} X.ringCatSheaf U)]

/-- Passing from the slice-site model of `𝒪_U`-modules to the open-subscheme model is additive:
it is a pushforward of sheaves of modules, so it is the identity on the underlying maps of
sheaves.

Named rather than synthesized because `AlgebraicGeometry.Scheme.Modules` is a semireducible
`def`: the instance for `TopologicalSpace.Opens.sheafOfModulesEquivOver` is stated at the
`SheafOfModules` spelling of the target category, which synthesis will not unfold to. -/
instance overEquivFunctorAdditive : ((Scheme.Modules.overEquiv U).functor).Additive :=
  inferInstanceAs (U.sheafOfModulesEquivOver X.ringCatSheaf).functor.Additive

/-- **The two models of derived restriction to an open subscheme agree.** Restriction of
`𝒪_X`-modules to the slice site `Opens X / U`, induced on derived categories and read through
the equivalence `AlgebraicGeometry.Scheme.Modules.overEquiv` between the slice-site model of
`𝒪_U`-modules and the open-subscheme model, is the functor induced on derived categories by
Mathlib's restriction along the open immersion `U.ι`.

Restriction to the slice site and the equivalence are both exact, so each of the three functors
induces a functor on unbounded derived categories, and
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv` — the same statement for the underlying
abelian categories — is carried across by the universal property of the localization. -/
def derivedOverFunctorEquiv :
    (SheafOfModules.overFunctor.{u} X.ringCatSheaf U).mapDerivedCategory ⋙
        ((Scheme.Modules.overEquiv U).functor).mapDerivedCategory ≅
      (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory :=
  @Functor.mapDerivedCategoryCompIso _ _ _ _ _ _ _ _ _ _ _ _ _
    (SheafOfModules.overFunctor_additive.{u, u, u, u} X.ringCatSheaf U)
    (inferInstanceAs
      (PreservesFiniteLimits (SheafOfModules.overFunctor.{u} X.ringCatSheaf U)))
    (inferInstanceAs
      (PreservesFiniteColimits (SheafOfModules.overFunctor.{u} X.ringCatSheaf U)))
    _ (overEquivFunctorAdditive U)
    (inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.overEquiv U).functor))
    (inferInstanceAs (PreservesFiniteColimits (Scheme.Modules.overEquiv U).functor))
    _ (Scheme.Modules.restrictFunctor_additive U.ι)
    (inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.restrictFunctor U.ι)))
    (inferInstanceAs (PreservesFiniteColimits (Scheme.Modules.restrictFunctor U.ι)))
    (Scheme.Modules.overFunctorEquiv U)

/-- The comparison of [Stacks, Tag 08DL] with its left-hand side in the open-subscheme model:
the restriction along the open immersion `U.ι` of `RSheafHom_{𝒪_X}(K, L)` is the derived
internal Hom of the slice site over `U` of the restrictions, read in the open-subscheme model.

It is the composite of the model comparison `derivedOverFunctorEquiv` with the slice-site
comparison `Stacks.SheafOfModules.derivedSheafHomRestrictionIso`, so it is canonical; its
naturality in each variable is `derivedSheafHomSchemeRestriction_natural_left` and
`derivedSheafHomSchemeRestriction_natural_right`.

The right-hand side is *not* the derived internal Hom of the scheme `U.toScheme`: see the
module documentation. -/
def derivedSheafHomSchemeRestriction
    (K L : DerivedCategory (StructureSheafModules X.sheaf)) :
    (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
        (((RingedSite.derivedSheafHomBifunctor (ringedSite X.sheaf)).obj (op K)).obj L) ≅
      ((Scheme.Modules.overEquiv U).functor).mapDerivedCategory.obj
        (((RingedSite.derivedSheafHomBifunctor ((ringedSite X.sheaf).over U)).obj
            (op ((derivedRestrict X.sheaf U).obj K))).obj
          ((derivedRestrict X.sheaf U).obj L)) :=
  ((derivedOverFunctorEquiv U).app _).symm ≪≫
    ((Scheme.Modules.overEquiv U).functor).mapDerivedCategory.mapIso
      (derivedSheafHomRestrictionIso X.sheaf U K L)

/-- Naturality of a comparison of the form `derivedOverFunctorEquiv.symm ≪≫ F.mapIso ψ` follows
from the naturality of the slice-site isomorphisms `ψ`. -/
private theorem restrictFunctor_map_comp_symm_trans_mapIso_hom
    {A B : DerivedCategory (StructureSheafModules X.sheaf)}
    {P Q : DerivedCategory (SheafOfModules.{u} (X.ringCatSheaf.over U))}
    (ψA : (derivedRestrict X.sheaf U).obj A ≅ P) (ψB : (derivedRestrict X.sheaf U).obj B ≅ Q)
    (a : A ⟶ B) (p : P ⟶ Q)
    (h : (derivedRestrict X.sheaf U).map a ≫ ψB.hom = ψA.hom ≫ p) :
    (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.map a ≫
        (((derivedOverFunctorEquiv U).app B).symm ≪≫
          ((Scheme.Modules.overEquiv U).functor).mapDerivedCategory.mapIso ψB).hom =
      (((derivedOverFunctorEquiv U).app A).symm ≪≫
          ((Scheme.Modules.overEquiv U).functor).mapDerivedCategory.mapIso ψA).hom ≫
        ((Scheme.Modules.overEquiv U).functor).mapDerivedCategory.map p := by
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  refine ((reassoc_of% (derivedOverFunctorEquiv U).inv.naturality a) _).trans ?_
  rw [← Functor.map_comp, h, Functor.map_comp, Category.assoc]
  rfl

/-- The reread comparison is natural in the contravariant variable: restricting along `U.ι` the
map `RSheafHom(K, L) ⟶ RSheafHom(K', L)` induced by `f : K' ⟶ K` gives the map induced by the
restriction of `f` to the slice site over `U`. -/
theorem derivedSheafHomSchemeRestriction_natural_left
    {K K' L : DerivedCategory (StructureSheafModules X.sheaf)} (f : K' ⟶ K) :
    (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.map
        (((RingedSite.derivedSheafHomBifunctor (ringedSite X.sheaf)).map f.op).app L) ≫
        (derivedSheafHomSchemeRestriction U K' L).hom =
      (derivedSheafHomSchemeRestriction U K L).hom ≫
        ((Scheme.Modules.overEquiv U).functor).mapDerivedCategory.map
          (((RingedSite.derivedSheafHomBifunctor ((ringedSite X.sheaf).over U)).map
              ((derivedRestrict X.sheaf U).map f).op).app
            ((derivedRestrict X.sheaf U).obj L)) :=
  restrictFunctor_map_comp_symm_trans_mapIso_hom U _ _ _ _
    (derivedSheafHomRestrictionIso_natural_left X.sheaf U (L := L) f)

/-- The reread comparison is natural in the covariant variable: restricting along `U.ι` the map
`RSheafHom(K, L) ⟶ RSheafHom(K, L')` induced by `g : L ⟶ L'` gives the map induced by the
restriction of `g` to the slice site over `U`. -/
theorem derivedSheafHomSchemeRestriction_natural_right
    {K L L' : DerivedCategory (StructureSheafModules X.sheaf)} (g : L ⟶ L') :
    (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.map
        (((RingedSite.derivedSheafHomBifunctor (ringedSite X.sheaf)).obj (op K)).map g) ≫
        (derivedSheafHomSchemeRestriction U K L').hom =
      (derivedSheafHomSchemeRestriction U K L).hom ≫
        ((Scheme.Modules.overEquiv U).functor).mapDerivedCategory.map
          (((RingedSite.derivedSheafHomBifunctor ((ringedSite X.sheaf).over U)).obj
              (op ((derivedRestrict X.sheaf U).obj K))).map
            ((derivedRestrict X.sheaf U).map g)) :=
  restrictFunctor_map_comp_symm_trans_mapIso_hom U _ _ _ _
    (derivedSheafHomRestrictionIso_natural_right X.sheaf U (K := K) g)

end Stacks.SheafOfModules

end
