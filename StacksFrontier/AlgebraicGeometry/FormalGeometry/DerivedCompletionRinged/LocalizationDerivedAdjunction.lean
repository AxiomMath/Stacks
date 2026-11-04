module

public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.PullbackToposSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdjunctionForRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Existence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardComp
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedSectionsCanonicalMaps
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.LocalizationCompletionFiniteType

/-!
# Restriction to a slice is left adjoint to the derived direct image of the localization

Let `(𝒞, 𝒪)` be a ringed site, `U` an object of `𝒞` and `j : (𝒞/U, 𝒪_U) ⟶ (𝒞, 𝒪)` the localization
morphism ([Stacks, Tag 03DH], as the two-field morphism of ringed topoi
`AlgebraicGeometry.RingedSite.localizationRingedToposHom`). Its pullback of sheaves of modules is
restriction to the slice ([Stacks, Tag 04IX]), which is exact; so restriction induces a functor
`D(𝒪) ⥤ D(𝒪_U)` which is left adjoint to the unbounded derived direct image `Rj_*`
([Stacks, Tag 07A6] for `j`).

## Main definitions

* `AlgebraicGeometry.RingedSite.localizationDerivedPushforward`: `Rj_*`.
* `AlgebraicGeometry.RingedSite.localizationPullbackDerivedAdjunction`: the adjunction with the
  pullback of sheaves of modules along `j` on the left.
* `AlgebraicGeometry.RingedSite.overFunctorDerivedAdjunction`: **the adjunction
  `(-)|_U ⊣ Rj_*` on derived categories.**

## Implementation notes

The adjunction is derived from the underived `j^* ⊣ j_*` by
`Stacks.Cohomology.SupportedComplexes.derivedAdjunctionOfExactLeftAdjoint`, which needs only that
the left adjoint is exact and that complexes of `𝒪_U`-modules have K-injective resolutions. It is
built with the pullback along `j` on the left and then transported along
`AlgebraicGeometry.RingedSite.localizationPullbackToposIsoRestriction`, because the categories of
sheaves of modules involved have two spellings (through the ringed topos and through the ringed
site) that instance search does not identify.

## References

* [Stacks Project, Tag 03DH](https://stacks.math.columbia.edu/tag/03DH)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.DerivedCategoryComparisons

/-- An adjunction out of the functor an exact functor induces on derived categories transports
along an isomorphism of exact functors. The exactness of the second functor is taken as
explicit arguments, so that the lemma applies across two spellings of a category. -/
def adjunctionOfNatIsoLeft {C₁ C₂ : Type*} [Category C₁] [Abelian C₁] [HasDerivedCategory C₁]
    [Category C₂] [Abelian C₂] [HasDerivedCategory C₂] (F G : C₁ ⥤ C₂) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (e : F ≅ G) (hA : G.Additive)
    (hL : PreservesFiniteLimits G) (hC : PreservesFiniteColimits G)
    {R : DerivedCategory C₂ ⥤ DerivedCategory C₁} (adj : F.mapDerivedCategory ⊣ R) :
    G.mapDerivedCategory ⊣ R :=
  adj.ofNatIsoLeft (mapDerivedCategoryIsoOfNatIso F G e)

end Stacks.DerivedCategoryComparisons

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] overFunctor_preservesFiniteLimits overFunctor_preservesFiniteColimits
  additive_overFunctor

variable (X : RingedSite.{u, u, u}) (U : X.C)

/-- Restriction to the slice is left adjoint to the direct image along the localization
morphism. -/
def overFunctorAdjPushforwardModules :
    SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U ⊣
      RingedToposHom.pushforwardModules (X := ringedTopos (X.over U)) (Y := ringedTopos X)
        (X.localizationRingedToposHom U) :=
  (RingedToposHom.pullbackAdjPushforwardModules (X := ringedTopos (X.over U))
      (Y := ringedTopos X) (X.localizationRingedToposHom U)).ofNatIsoLeft
    (X.localizationPullbackToposIsoRestriction U)

/-- The derived direct image `Rj_*` along the localization morphism `j` at `U`. -/
abbrev localizationDerivedPushforward :=
  Stacks.Cohomology.DerivedPushforward.derivedPushforward (X := ringedTopos (X.over U))
    (Y := ringedTopos X) (X.localizationRingedToposHom U)

/-- The pullback of sheaves of modules along the localization morphism preserves finite limits:
it is restriction to the slice. -/
instance preservesFiniteLimits_localizationPullbackModules :
    PreservesFiniteLimits (X.localizationRingedToposHom U).toModulesHom.pullbackModules :=
  @preservesFiniteLimits_of_natIso _ _ _ _ _ _ (X.localizationPullbackToposIsoRestriction U).symm
    (Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits U)

/-- The pullback of sheaves of modules along the localization morphism preserves finite
colimits: it is restriction to the slice. -/
instance preservesFiniteColimits_localizationPullbackModules :
    PreservesFiniteColimits (X.localizationRingedToposHom U).toModulesHom.pullbackModules :=
  @preservesFiniteColimits_of_natIso _ _ _ _ _ _ (X.localizationPullbackToposIsoRestriction U).symm
    (Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits U)

/-- The direct image of sheaves of modules along the localization morphism is additive. -/
instance additive_localizationPushforwardModules :
    (RingedToposHom.pushforwardModules (X := ringedTopos (X.over U)) (Y := ringedTopos X)
      (X.localizationRingedToposHom U)).Additive :=
  RingedToposHom.pushforwardModules_additive (X := ringedTopos (X.over U)) (Y := ringedTopos X)
    (X.localizationRingedToposHom U)

/-- The pullback of sheaves of modules along the localization morphism is additive. -/
instance additive_localizationPullbackModules :
    (X.localizationRingedToposHom U).toModulesHom.pullbackModules.Additive :=
  (RingedToposHom.pullbackAdjPushforwardModules (X := ringedTopos (X.over U))
    (Y := ringedTopos X) (X.localizationRingedToposHom U)).left_adjoint_additive

/-- **Stacks 07A6 for the localization morphism, with `Lj^*` the derived pullback of an exact
functor**: the pullback along `j` induces on derived categories a left adjoint of `Rj_*`. -/
def localizationPullbackDerivedAdjunction :
    (X.localizationRingedToposHom U).toModulesHom.pullbackModules.mapDerivedCategory ⊣
      localizationDerivedPushforward X U :=
  Stacks.Cohomology.SupportedComplexes.derivedAdjunctionOfExactLeftAdjoint
    (RingedToposHom.pullbackAdjPushforwardModules (X := ringedTopos (X.over U))
      (Y := ringedTopos X) (X.localizationRingedToposHom U))
    (localizationDerivedPushforward X U)
    ((Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy (X := ringedTopos (X.over U))
      (Y := ringedTopos X) (X.localizationRingedToposHom U)).totalRightDerivedUnit
        DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.exists_quasiIso_isKInjective
      (ringedTopos.{u, u, u} (X.over U)))

/-- **Restriction to the slice is left adjoint to `Rj_*` on derived categories**, `j` the
localization morphism: `localizationPullbackDerivedAdjunction` with the derived pullback `Lj^*`
replaced by the functor that restriction, to which the pullback is isomorphic, induces. -/
def overFunctorDerivedAdjunction :
    (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory ⊣
      localizationDerivedPushforward X U :=
  Stacks.DerivedCategoryComparisons.adjunctionOfNatIsoLeft _ _
    (X.localizationPullbackToposIsoRestriction U) ⟨rfl⟩
    (Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits U)
    (Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits U)
    (localizationPullbackDerivedAdjunction X U)

end AlgebraicGeometry.RingedSite
