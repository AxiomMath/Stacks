module

public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigToSmallEtale
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Adjunction
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactness

/-!
# Restriction to a small étale site preserves injectivity and K-injectivity (Stacks 0DG8)

Let `T` be a big étale site of algebraic spaces over a scheme `S` and let `X` be one of its
objects. An injective abelian sheaf on the big étale site of `X`, and likewise a K-injective
complex of abelian sheaves, stays injective resp. K-injective after restriction to the
spaces-étale site of `X`, and more generally after restriction along a morphism `f : Y ⟶ X`
of `T`, which is the inverse image of the morphism of topoi `i_f` of Tag 0DF2.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.injective_spacesEtaleRestriction` — part (1)(b) of
  the source: restriction to the spaces-étale site of `X` preserves injective abelian
  sheaves.
* `AlgebraicGeometry.BigEtaleSpaceSite.injective_spacesEtaleRestrictionAlong` — part (1)(a):
  the same for restriction along a morphism `f : Y ⟶ X`.
* `AlgebraicGeometry.BigEtaleSpaceSite.isKInjective_spacesEtaleRestriction` — part (2)(b) of
  the source: restriction to the spaces-étale site of `X` preserves K-injectivity.
* `AlgebraicGeometry.BigEtaleSpaceSite.isKInjective_spacesEtaleRestrictionAlong` — part
  (2)(a): the same for restriction along a morphism `f : Y ⟶ X`.

## Implementation notes

All four are the same adjoint criterion. Restriction is right adjoint to lower shriek, and
lower shriek on abelian sheaves is exact; an exact left adjoint makes its right adjoint
preserve injective objects, which for the injective halves is
`preservesInjectiveObjects_of_isExact` — the Lean form of Homology, Lemma 015Z, the lemma
the source itself cites — and for the K-injective halves is
`CochainComplex.isKInjective_mapHomologicalComplex_of_exact`. Lower shriek is exact by
`Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits` and
`Stacks.Sites.LowerShriek.gShriek_preservesFiniteColimits` (Tag 04BH). Nothing about that
exactness is redone here; the hypotheses it needs — fibre products and equalizers of the small
site, preserved by the inclusion — are the instances of Tag 0DF3 and Tag 0DF2. Both Tag 04BH
results carry `instance`, so in the injective halves they are reached by synthesis and need
no universe list; the K-injective halves apply them explicitly.

The two restriction functors are written as Mathlib's `sheafPushforwardContinuous`, with no
abelian restriction functor coined: the source's `i_f^{-1}` is restriction along the inclusion
functor of Tag 0DF2 and `\pi_{X,*}` is restriction along the inclusion of the spaces-étale
site, which Tag 0DF3 identifies with the `f = 𝟙 X` case of the former.

Preservation of fibre products and equalizers by the inclusion functor of Tag 0DF2 is
re-derived here in one line each from the public instances of the spaces-étale site and of
`CategoryTheory.Over.map`; the corresponding instances of
`StacksFrontier/AlgebraicGeometry/Spaces/Topologies/SmallToBigEtale.lean` are private there and
promoting them would mean editing a tagged module for no saving.

Sheafification of abelian sheaves on these sites needs no hypothesis: every slice of the big
étale site is essentially small, so `CategoryTheory.hasSheafifyEssentiallySmallSite` applies
and the instance is found by synthesis. That instance is what fixes the universe of sections
to `u + 1`, the universe in which the sites themselves live: at a strictly larger universe of
sections `CategoryTheory.hasSheafifyEssentiallySmallSite` is unavailable, because the small
model's own sheafification instance is universe-matched, so none of the four results can be
stated with an independent universe of sections.

The module remark of the source — that the corresponding statements for sheaves of modules do
not hold — is proved over `Spec ℤ` in
`StacksFrontier/AlgebraicGeometry/Spaces/Topologies/BigSmallEtaleModuleRestrictionInjective.lean`,
by `AlgebraicGeometry.BigEtaleSpaceSite.exists_injective_not_injective_restrictModules` and its
three companions.

## References

* [Stacks Project, Tag 0DG8](https://stacks.math.columbia.edu/tag/0DG8)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 04BH](https://stacks.math.columbia.edu/tag/04BH)
* [Stacks Project, Tag 0DF2](https://stacks.math.columbia.edu/tag/0DF2)
* [Stacks Project, Tag 0DF3](https://stacks.math.columbia.edu/tag/0DF3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

/-- Composing an étale object over `Y` with `f : Y ⟶ X` preserves fibre products. -/
private instance inclusionFunctor_preservesPullbacks' {X Y : T.Spaces} (f : Y ⟶ X) :
    PreservesLimitsOfShape WalkingCospan (inclusionFunctor T f) :=
  comp_preservesLimitsOfShape
    (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Y) (Over.map f)

/-- Composing an étale object over `Y` with `f : Y ⟶ X` preserves equalizers. -/
private noncomputable instance inclusionFunctor_preservesEqualizers' {X Y : T.Spaces}
    (f : Y ⟶ X) :
    PreservesLimitsOfShape WalkingParallelPair (inclusionFunctor T f) :=
  comp_preservesLimitsOfShape
    (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem Y) (Over.map f)

/-- **Stacks Project, Tag 0DG8, part (1)(b).** Restriction of an injective abelian sheaf
from the big étale site of `X` to the spaces-étale site of `X` is injective. -/
@[stacks 0DG8 "injective_restriction"]
theorem injective_spacesEtaleRestriction (X : T.Spaces)
    (I : Sheaf (T.bigEtaleTopology X) Ab.{u + 1}) [Injective I] :
    Injective
      (((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X).sheafPushforwardContinuous
        Ab.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
        (T.bigEtaleTopology X)).obj I) :=
  let G := Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X
  let J := Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X
  let K := T.bigEtaleTopology X
  let L := Functor.sheafPullbackConstruction.sheafPullback G Ab.{u + 1} J K
  let R := G.sheafPushforwardContinuous Ab.{u + 1} J K
  let adj : L ⊣ R :=
    Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G Ab.{u + 1} J K
  let : R.Additive := Functor.additive_of_preserves_binary_products _
  let : L.Additive := Functor.additive_of_preserves_binary_products _
  let : R.PreservesInjectiveObjects :=
    preservesInjectiveObjects_of_isExact R L adj ⟨inferInstance, inferInstance⟩
  Functor.injective_obj_of_injective R inferInstance

/-- **Stacks Project, Tag 0DG8, part (1)(a).** Restriction of an injective abelian sheaf
from the big étale site of `X` to the spaces-étale site of `Y` along a morphism
`f : Y ⟶ X` — the inverse image of `i_f` — is injective. -/
@[stacks 0DG8 "injective_pullback"]
theorem injective_spacesEtaleRestrictionAlong {X Y : T.Spaces} (f : Y ⟶ X)
    (I : Sheaf (T.bigEtaleTopology X) Ab.{u + 1}) [Injective I] :
    Injective
      (((inclusionFunctor T f).sheafPushforwardContinuous Ab.{u + 1}
        (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
        (T.bigEtaleTopology X)).obj I) :=
  let G := inclusionFunctor T f
  let J := Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y
  let K := T.bigEtaleTopology X
  let L := Functor.sheafPullbackConstruction.sheafPullback G Ab.{u + 1} J K
  let R := G.sheafPushforwardContinuous Ab.{u + 1} J K
  let adj : L ⊣ R :=
    Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G Ab.{u + 1} J K
  let : R.Additive := Functor.additive_of_preserves_binary_products _
  let : L.Additive := Functor.additive_of_preserves_binary_products _
  let : R.PreservesInjectiveObjects :=
    preservesInjectiveObjects_of_isExact R L adj ⟨inferInstance, inferInstance⟩
  Functor.injective_obj_of_injective R inferInstance

/-- **Stacks Project, Tag 0DG8, part (2)(b).** Restriction of a K-injective complex of
abelian sheaves from the big étale site of `X` to the spaces-étale site of `X` is
K-injective. -/
@[stacks 0DG8 "kinjective_restriction"]
theorem isKInjective_spacesEtaleRestriction (X : T.Spaces)
    (I : CochainComplex (Sheaf (T.bigEtaleTopology X) Ab.{u + 1}) ℤ)
    (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      ((((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X).sheafPushforwardContinuous
        Ab.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
        (T.bigEtaleTopology X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  let G := Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X
  let J := Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X
  let K := T.bigEtaleTopology X
  let L := Functor.sheafPullbackConstruction.sheafPullback G Ab.{u + 1} J K
  let : PreservesFiniteLimits L :=
    Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits.{u + 1, u + 1, u + 1, u + 1, u + 1}
      G J K
  let : PreservesFiniteColimits L :=
    Stacks.Sites.LowerShriek.gShriek_preservesFiniteColimits AddCommGrpCat.{u + 1} G J K
  let : (G.sheafPushforwardContinuous Ab.{u + 1} J K).Additive :=
    Functor.additive_of_preserves_binary_products _
  let : L.Additive := Functor.additive_of_preserves_binary_products _
  let := hI
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact
    (G.sheafPushforwardContinuous Ab.{u + 1} J K) L
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G Ab.{u + 1} J K) I

/-- **Stacks Project, Tag 0DG8, part (2)(a).** Restriction of a K-injective complex of
abelian sheaves from the big étale site of `X` to the spaces-étale site of `Y` along a
morphism `f : Y ⟶ X` — the inverse image of `i_f` — is K-injective. -/
@[stacks 0DG8 "kinjective_pullback"]
theorem isKInjective_spacesEtaleRestrictionAlong {X Y : T.Spaces} (f : Y ⟶ X)
    (I : CochainComplex (Sheaf (T.bigEtaleTopology X) Ab.{u + 1}) ℤ)
    (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      ((((inclusionFunctor T f).sheafPushforwardContinuous Ab.{u + 1}
        (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
        (T.bigEtaleTopology X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  let G := inclusionFunctor T f
  let J := Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y
  let K := T.bigEtaleTopology X
  let L := Functor.sheafPullbackConstruction.sheafPullback G Ab.{u + 1} J K
  let : PreservesFiniteLimits L :=
    Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits.{u + 1, u + 1, u + 1, u + 1, u + 1}
      G J K
  let : PreservesFiniteColimits L :=
    Stacks.Sites.LowerShriek.gShriek_preservesFiniteColimits AddCommGrpCat.{u + 1} G J K
  let : (G.sheafPushforwardContinuous Ab.{u + 1} J K).Additive :=
    Functor.additive_of_preserves_binary_products _
  let : L.Additive := Functor.additive_of_preserves_binary_products _
  let := hI
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact
    (G.sheafPushforwardContinuous Ab.{u + 1} J K) L
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G Ab.{u + 1} J K) I

end AlgebraicGeometry.BigEtaleSpaceSite

end
