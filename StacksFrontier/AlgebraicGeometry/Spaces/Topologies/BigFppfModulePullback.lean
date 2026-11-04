module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfEtaleRingedComparison

/-!
# Inverse images of sheaves of modules for the fppf-to-étale comparisons of an algebraic space

Let `T` be a big fppf site of algebraic spaces over `S` and `E` a big étale site of algebraic
spaces over the same big fppf site of schemes. For an algebraic space `X` of `T` the comparison
morphisms of ringed sites `π_X`, `ε_X` and `a_X = π_X ∘ ε_X` have direct images on sheaves of
`𝒪`-modules; this file supplies their left adjoints `π_X^*`, `ε_X^*` and `a_X^*`, together with
the canonical identification `ε_X^* ∘ π_X^* ≅ a_X^*` and the two comparison maps
`π_X^*𝓕 ⟶ ε_{X,*}(a_X^*𝓕)` and `𝓕 ⟶ a_{X,*}(a_X^*𝓕)`.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.restrictModulesPullback` and
  `AlgebraicGeometry.BigEtaleSpaceSite.restrictModulesAdjunction`: the inverse image `π_X^*` of
  sheaves of modules from the small étale site of `X` to its big étale site, and its adjunction
  with `π_{X,*}`.
* `AlgebraicGeometry.BigFppfSpaceSite.fppfToBigEtaleModulePullback` and
  `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtaleModulePullback`: the inverse images
  `ε_X^*` and `a_X^*` of sheaves of modules, with their adjunctions
  `AlgebraicGeometry.BigFppfSpaceSite.fppfToBigEtaleModuleAdjunction` and
  `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtaleModuleAdjunction`.
* `AlgebraicGeometry.BigFppfSpaceSite.modulePullbackCompIso`: the factorization
  `ε_X^* ∘ π_X^* ≅ a_X^*` of inverse images on sheaves of modules.
* `AlgebraicGeometry.BigFppfSpaceSite.bigEtaleFppfComparison` and
  `AlgebraicGeometry.BigFppfSpaceSite.smallEtaleFppfComparison`: the two comparison maps
  `π_X^*𝓕 ⟶ ε_{X,*}(a_X^*𝓕)` and `𝓕 ⟶ a_{X,*}(a_X^*𝓕)`.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtaleSharp_comp_eq`: the structure map of
  `a_X` is the structure map of `π_X` followed by the direct image of that of `ε_X`.

## Implementation notes

The module universe is the universe `u + 1` of the sections of the structure sheaves and of the
objects and morphisms of the three sites. That is forced by the construction of the left
adjoint, which resolves a presheaf of modules into free modules on representables: a
representable presheaf on a category of objects in `Type w` is `w`-small only when its
morphisms live in `Type w` as well. All three sites here are categories of algebraic spaces
over `S`, whose objects, morphisms and global regular functions all lie in `Type (u + 1)`, so
the condition holds and the generic adjunction
`Stacks.Sheaves.ModuleAdjunction.pullbackPushforwardAdjunction` applies with nothing further to
check; the two sheafification hypotheses it carries, that abelian presheaves on the big fppf
site of `X` have a sheafification whose local isomorphisms are the locally bijective maps, are
found by instance search, the site being small in the universe of the sections.

The factorization `ε_X^* ∘ π_X^* ≅ a_X^*` is obtained from uniqueness of left adjoints: the
composite of the two adjunctions is an adjunction with `ε_{X,*} ∘ π_{X,*}`, which is the direct
image along the composite structure map by `fppfToSmallEtaleSharp_comp_eq`, hence is `a_{X,*}`.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 0DF9](https://stacks.math.columbia.edu/tag/0DF9)
* [Stacks Project, Tag 0DGP](https://stacks.math.columbia.edu/tag/0DGP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace BigEtaleSpaceSite

variable {S : Scheme.{u}} (E : BigEtaleSpaceSite S)

/-- The inverse image `π_X^*` of sheaves of `𝒪`-modules along the comparison morphism `π_X`,
from the small étale site of `X` to its big étale site: the left adjoint of restriction. -/
abbrev restrictModulesPullback (X : E.Spaces) :
    SpacesEtaleModules.{u, u + 1} E X ⥤ BigEtaleModules.{u, u + 1} E X :=
  SheafOfModules.pullback.{u + 1} (E.restrictSharp X)

/-- The inverse image of sheaves of `𝒪`-modules along `π_X` is left adjoint to restriction to
the small étale site of `X`. -/
def restrictModulesAdjunction (X : E.Spaces) :
    restrictModulesPullback E X ⊣ restrictModules.{u, u + 1} E X :=
  Stacks.Sheaves.ModuleAdjunction.pullbackPushforwardAdjunction.{u + 1} (E.restrictSharp X)

end BigEtaleSpaceSite

namespace BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : T.schemeSite = E.fppfSite)

/-! ### The two inverse images on sheaves of modules -/

/-- The inverse image `ε_X^*` of sheaves of `𝒪`-modules along the change-of-topology morphism
`ε_X`, from the big étale site of `X` to its big fppf site. -/
abbrev fppfToBigEtaleModulePullback (X : T.Spaces) :
    E.BigEtaleModules.{u, u + 1} (etaleSpace T E h X) ⥤ BigFppfModules.{u, u + 1} T X :=
  SheafOfModules.pullback.{u + 1} (fppfToBigEtaleSharp T E h X)

/-- The inverse image `a_X^*` of sheaves of `𝒪`-modules along `a_X`, from the small étale site
of `X` to its big fppf site. -/
abbrev fppfToSmallEtaleModulePullback (X : T.Spaces) :
    E.SpacesEtaleModules.{u, u + 1} (etaleSpace T E h X) ⥤ BigFppfModules.{u, u + 1} T X :=
  SheafOfModules.pullback.{u + 1} (fppfToSmallEtaleSharp T E h X)

/-- The inverse image along `ε_X` is left adjoint to the direct image `ε_{X,*}` on sheaves of
`𝒪`-modules. -/
def fppfToBigEtaleModuleAdjunction (X : T.Spaces) :
    fppfToBigEtaleModulePullback T E h X ⊣
      fppfToBigEtaleModulePushforward.{u, u + 1} T E h X :=
  Stacks.Sheaves.ModuleAdjunction.pullbackPushforwardAdjunction.{u + 1}
    (fppfToBigEtaleSharp T E h X)

/-- The inverse image along `a_X` is left adjoint to the direct image `a_{X,*}` on sheaves of
`𝒪`-modules. -/
def fppfToSmallEtaleModuleAdjunction (X : T.Spaces) :
    fppfToSmallEtaleModulePullback T E h X ⊣
      fppfToSmallEtaleModulePushforward.{u, u + 1} T E h X :=
  Stacks.Sheaves.ModuleAdjunction.pullbackPushforwardAdjunction.{u + 1}
    (fppfToSmallEtaleSharp T E h X)

/-! ### The factorization of the inverse images -/

/-- The structure map of `a_X` is the structure map of `π_X` followed by the direct image along
`π_X` of the structure map of `ε_X`, the canonical comparison of the two composite direct
images being the identity. -/
theorem fppfToSmallEtaleSharp_comp_eq (X : T.Spaces) :
    E.restrictSharp (etaleSpace T E h X) ≫
        ((Space.SpacesEtale.inclusion E.fppfSite S E.fppf_mem
            (etaleSpace T E h X)).sheafPushforwardContinuous RingCat.{u + 1}
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h X))
          (E.bigEtaleTopology (etaleSpace T E h X))).map (fppfToBigEtaleSharp T E h X) =
      fppfToSmallEtaleSharp T E h X := by
  cases E with
  | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
      eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
    cases h
    exact Category.id_comp _

/-- The composite of the direct images along `ε_X` and `π_X` is the direct image along `a_X` on
sheaves of `𝒪`-modules, matching the factorization `a_X = π_X ∘ ε_X`. -/
def modulePushforwardCompIso (X : T.Spaces) :
    fppfToBigEtaleModulePushforward.{u, u + 1} T E h X ⋙
        E.restrictModules.{u, u + 1} (etaleSpace T E h X) ≅
      fppfToSmallEtaleModulePushforward.{u, u + 1} T E h X :=
  SheafOfModules.pushforwardComp.{u + 1} (E.restrictSharp (etaleSpace T E h X))
      (fppfToBigEtaleSharp T E h X) ≪≫
    SheafOfModules.pushforwardCongr.{u + 1} (fppfToSmallEtaleSharp_comp_eq T E h X)

/-- The inverse image along `a_X` is the inverse image along `π_X` followed by the inverse image
along `ε_X`: both are left adjoint to the direct image along `a_X`. -/
def modulePullbackCompIso (X : T.Spaces) :
    E.restrictModulesPullback (etaleSpace T E h X) ⋙ fppfToBigEtaleModulePullback T E h X ≅
      fppfToSmallEtaleModulePullback T E h X :=
  Adjunction.leftAdjointUniq
    (((E.restrictModulesAdjunction (etaleSpace T E h X)).comp
      (fppfToBigEtaleModuleAdjunction T E h X)).ofNatIsoRight (modulePushforwardCompIso T E h X))
    (fppfToSmallEtaleModuleAdjunction T E h X)

/-! ### The two comparison maps -/

/-- The comparison map `𝓕 ⟶ a_{X,*}(a_X^*𝓕)` of a sheaf of `𝒪_X`-modules on the small étale
site of `X`: the unit of the adjunction between the inverse and the direct image along `a_X`. -/
def smallEtaleFppfComparison (X : T.Spaces)
    (M : E.SpacesEtaleModules.{u, u + 1} (etaleSpace T E h X)) :
    M ⟶ (fppfToSmallEtaleModulePushforward.{u, u + 1} T E h X).obj
      ((fppfToSmallEtaleModulePullback T E h X).obj M) :=
  (fppfToSmallEtaleModuleAdjunction T E h X).unit.app M

/-- The comparison map `π_X^*𝓕 ⟶ ε_{X,*}(a_X^*𝓕)` of a sheaf of `𝒪_X`-modules on the small
étale site of `X`: the unit of the adjunction along `ε_X` at `π_X^*𝓕`, followed by the direct
image along `ε_X` of the factorization `ε_X^*(π_X^*𝓕) ≅ a_X^*𝓕`. -/
def bigEtaleFppfComparison (X : T.Spaces)
    (M : E.SpacesEtaleModules.{u, u + 1} (etaleSpace T E h X)) :
    (E.restrictModulesPullback (etaleSpace T E h X)).obj M ⟶
      (fppfToBigEtaleModulePushforward.{u, u + 1} T E h X).obj
        ((fppfToSmallEtaleModulePullback T E h X).obj M) :=
  (fppfToBigEtaleModuleAdjunction T E h X).unit.app
      ((E.restrictModulesPullback (etaleSpace T E h X)).obj M) ≫
    (fppfToBigEtaleModulePushforward.{u, u + 1} T E h X).map
      ((modulePullbackCompIso T E h X).hom.app M)

/-- The two comparison maps determine one another: the first is the mate of the second under the
adjunction between the inverse and the direct image along `π_X`, read through the factorization
`a_{X,*} ≅ π_{X,*} ∘ ε_{X,*}` of the direct images. -/
theorem homEquiv_bigEtaleFppfComparison (X : T.Spaces)
    (M : E.SpacesEtaleModules.{u, u + 1} (etaleSpace T E h X)) :
    (E.restrictModulesAdjunction (etaleSpace T E h X)).homEquiv _ _
        (bigEtaleFppfComparison T E h X M) =
      smallEtaleFppfComparison T E h X M ≫
        (modulePushforwardCompIso T E h X).inv.app
          ((fppfToSmallEtaleModulePullback T E h X).obj M) := by
  have key := Adjunction.unit_leftAdjointUniq_hom_app
    (((E.restrictModulesAdjunction (etaleSpace T E h X)).comp
        (fppfToBigEtaleModuleAdjunction T E h X)).ofNatIsoRight
      (modulePushforwardCompIso T E h X))
    (fppfToSmallEtaleModuleAdjunction T E h X) M
  dsimp only [smallEtaleFppfComparison, bigEtaleFppfComparison]
  rw [← key, Adjunction.homEquiv_unit]
  simp [Adjunction.comp_unit_app, modulePullbackCompIso, ← Functor.map_comp]

end BigFppfSpaceSite

end AlgebraicGeometry

end
