module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfRingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtalePushforwardModules

/-!
# The fppf-to-étale comparisons of an algebraic space as morphisms of ringed sites

Let `T` be a big fppf site of algebraic spaces over `S` and `E` a big étale site of algebraic
spaces over the same big fppf site of schemes. For an algebraic space `X` of `T` the
change-of-topology morphism `ε_X` to the big étale topos of `X` and the morphism
`a_X = π_X ∘ ε_X` to the small étale topos are morphisms of sites whose source and target both
carry the sheaf of global regular functions. Their structure maps are the identity, because the
sections of all three structure sheaves over an algebraic space are its own global regular
functions, so both comparisons are morphisms of ringed sites and induce direct images on
sheaves of modules.

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceSite.fppfToBigEtaleSharp` and
  `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtaleSharp`: the structure maps of `ε_X` and
  of `a_X`.
* `AlgebraicGeometry.BigFppfSpaceSite.fppfToBigEtaleRingedHom` and
  `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtaleRingedHom`: `ε_X` and `a_X` as morphisms
  of ringed sites.
* `AlgebraicGeometry.BigFppfSpaceSite.fppfToBigEtaleModulePushforward` and
  `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtaleModulePushforward`: the direct images
  `ε_{X,*}` and `a_{X,*}` on sheaves of `𝒪`-modules.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtale_isContinuous`: the composite of the
  inclusion of the small étale site with the change-of-topology functor is continuous for the
  small étale and the big fppf topologies.
* `AlgebraicGeometry.BigFppfSpaceSite.fppfToSmallEtaleSharp_eq`: the structure map of `a_X` is
  the composite of those of `π_X` and `ε_X`, so the factorization `a_X = π_X ∘ ε_X` holds on
  structure sheaves as well as on sites.

## Implementation notes

The two sites describe the same category of algebraic spaces exactly when the fppf scheme site
of `E` is the scheme site of `T`, which is the hypothesis `h` carried throughout.

Direct images of sheaves of modules are taken along a continuous functor of sites together with
a map of structure sheaves, so `a_{X,*}` is a direct image along the composite functor rather
than a composite of two direct images.

## References

* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 0DF9](https://stacks.math.columbia.edu/tag/0DF9)
* [Stacks Project, Tag 0DGI](https://stacks.math.columbia.edu/tag/0DGI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : T.schemeSite = E.fppfSite)

/-! ### Continuity of the two comparison functors -/

/-- The composite of the inclusion of the small étale site of `X` with the identity-on-spaces
change-of-topology functor is continuous from the small étale topology of `X` to its big fppf
topology. -/
instance fppfToSmallEtale_isContinuous (X : T.Spaces) :
    ((Space.SpacesEtale.inclusion E.fppfSite S E.fppf_mem (etaleSpace T E h X)) ⋙
        (Over.postEquiv (canonicalSpaceEquivalence T E h).1 (X := X)).inverse).IsContinuous
      (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h X))
      (BigFppfSpaceOver.topology T X) :=
  Functor.isContinuous_comp
    (Space.SpacesEtale.inclusion E.fppfSite S E.fppf_mem (etaleSpace T E h X))
    ((Over.postEquiv (canonicalSpaceEquivalence T E h).1 (X := X)).inverse)
    (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h X))
    (E.bigEtaleTopology (etaleSpace T E h X))
    (BigFppfSpaceOver.topology T X)

/-! ### The two structure maps -/

/-- The structure map of the change-of-topology morphism `ε_X`: the sections of the direct
image of the big fppf structure sheaf over an algebraic space over `X` are its own global
regular functions, so the structure map is the identity. -/
def fppfToBigEtaleSharp (X : T.Spaces) :
    E.bigEtaleRingSheaf (etaleSpace T E h X) ⟶
      (((Over.postEquiv (canonicalSpaceEquivalence T E h).1
          (X := X)).inverse).sheafPushforwardContinuous RingCat.{u + 1}
        (E.bigEtaleTopology (etaleSpace T E h X))
        (BigFppfSpaceOver.topology T X)).obj (bigFppfRingSheaf T X) := by
  cases E
  cases h
  exact 𝟙 _

/-- The structure map of the morphism `a_X` to the small étale topos: the sections of the
direct image of the big fppf structure sheaf over an algebraic space étale over `X` are its own
global regular functions, so the structure map is the identity. -/
def fppfToSmallEtaleSharp (X : T.Spaces) :
    E.spacesEtaleRingSheaf (etaleSpace T E h X) ⟶
      (((Space.SpacesEtale.inclusion E.fppfSite S E.fppf_mem (etaleSpace T E h X)) ⋙
          (Over.postEquiv (canonicalSpaceEquivalence T E h).1
            (X := X)).inverse).sheafPushforwardContinuous RingCat.{u + 1}
        (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h X))
        (BigFppfSpaceOver.topology T X)).obj (bigFppfRingSheaf T X) := by
  cases E
  cases h
  exact 𝟙 _

/-- The structure map of `a_X` is the composite of the structure map of `π_X` with the direct
image of the structure map of `ε_X`: the factorization `a_X = π_X ∘ ε_X` holds on structure
sheaves. -/
theorem fppfToSmallEtaleSharp_eq (X : T.Spaces) :
    fppfToSmallEtaleSharp T E h X =
      E.restrictSharp (etaleSpace T E h X) ≫
        ((Space.SpacesEtale.inclusion E.fppfSite S E.fppf_mem
            (etaleSpace T E h X)).sheafPushforwardContinuous RingCat.{u + 1}
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h X))
          (E.bigEtaleTopology (etaleSpace T E h X))).map (fppfToBigEtaleSharp T E h X) ≫
        (Functor.sheafPushforwardContinuousComp
          (Space.SpacesEtale.inclusion E.fppfSite S E.fppf_mem (etaleSpace T E h X))
          ((Over.postEquiv (canonicalSpaceEquivalence T E h).1 (X := X)).inverse)
          RingCat.{u + 1}
          (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h X))
          (E.bigEtaleTopology (etaleSpace T E h X))
          (BigFppfSpaceOver.topology T X)).hom.app (bigFppfRingSheaf T X) := by
  cases E
  cases h
  exact (Category.id_comp _).symm

/-! ### The two morphisms of ringed sites -/

/-- The change-of-topology morphism `ε_X` from the big fppf site of `X` to its big étale site,
as a morphism of ringed sites. -/
def fppfToBigEtaleRingedHom (X : T.Spaces) :
    RingedSite.Hom (bigFppfRingedSite T X) (E.bigEtaleRingedSite (etaleSpace T E h X)) where
  u := (Over.postEquiv (canonicalSpaceEquivalence T E h).1 (X := X)).inverse
  isMorphismOfSites :=
    Functor.isMorphismOfSites_of_representablyFlat
      ((Over.postEquiv (canonicalSpaceEquivalence T E h).1 (X := X)).inverse)
      (E.bigEtaleTopology (etaleSpace T E h X)) (BigFppfSpaceOver.topology T X)
  fsharp := by
    cases E
    cases h
    exact 𝟙 _

/-- The morphism `a_X` from the big fppf site of `X` to its small étale site, as a morphism of
ringed sites. Its underlying functor is the composite of the inclusion of the small étale site
with the change-of-topology functor, matching the factorization `a_X = π_X ∘ ε_X`. -/
def fppfToSmallEtaleRingedHom (X : T.Spaces) :
    RingedSite.Hom (bigFppfRingedSite T X)
      (Space.spacesEtaleRingedSite E.fppfSite S E.fppf_mem (etaleSpace T E h X)) where
  u := (Space.SpacesEtale.inclusion E.fppfSite S E.fppf_mem (etaleSpace T E h X)) ⋙
    (Over.postEquiv (canonicalSpaceEquivalence T E h).1 (X := X)).inverse
  isMorphismOfSites :=
    (E.inclusion_isMorphismOfSites (etaleSpace T E h X)).comp
      (Functor.isMorphismOfSites_of_representablyFlat
        ((Over.postEquiv (canonicalSpaceEquivalence T E h).1 (X := X)).inverse)
        (E.bigEtaleTopology (etaleSpace T E h X)) (BigFppfSpaceOver.topology T X))
  fsharp := by
    cases E
    cases h
    exact 𝟙 _

/-! ### The direct images on sheaves of modules -/

/-- The direct image `ε_{X,*}` of sheaves of `𝒪`-modules from the big fppf site of `X` to its
big étale site. -/
abbrev fppfToBigEtaleModulePushforward (X : T.Spaces) :
    BigFppfModules.{u, m} T X ⥤ E.BigEtaleModules.{u, m} (etaleSpace T E h X) :=
  SheafOfModules.pushforward.{m} (fppfToBigEtaleSharp T E h X)

/-- The direct image `a_{X,*}` of sheaves of `𝒪`-modules from the big fppf site of `X` to its
small étale site. -/
abbrev fppfToSmallEtaleModulePushforward (X : T.Spaces) :
    BigFppfModules.{u, m} T X ⥤ E.SpacesEtaleModules.{u, m} (etaleSpace T E h X) :=
  SheafOfModules.pushforward.{m} (fppfToSmallEtaleSharp T E h X)

end AlgebraicGeometry.BigFppfSpaceSite

end
