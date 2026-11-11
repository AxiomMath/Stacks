module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.Injective.Basic
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigToSmallEtale
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Adjunction
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactness

/-!
# Restricting abelian sheaves from a big étale site of algebraic spaces (Stacks 0DG8)

Let `T` be a big étale site of algebraic spaces over a scheme `S` and `f : Y ⟶ X` a morphism of
its objects. Restriction of abelian sheaves from the big étale site of `X` to the spaces-étale
site of `Y` — the inverse image of the morphism of topoi `i_f` of Tag 0DF2 — preserves
injective objects, and on complexes it preserves K-injectivity. The same holds for restriction
to the spaces-étale site of `X` itself, which Tag 0DF3 identifies with the inverse image of
`i_X` and with the direct image of `π_X`.

The analogous statements for sheaves of modules are false, as the source records; the
counterexamples over `Spec ℤ` are
`AlgebraicGeometry.BigEtaleSpaceSite.exists_injective_not_injective_restrictModules` and its
three companions in
`StacksFrontier/AlgebraicGeometry/Spaces/Topologies/BigSmallEtaleModuleRestrictionInjective.lean`.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.smallEtaleRestriction` is restriction of abelian sheaves
  along the inclusion functor of Tag 0DF2, that is, the inverse image of `i_f`.
* `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallEtaleRestriction` is restriction along the
  inclusion of the spaces-étale site of `X` into the big étale site of `X`, and
  `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallEtaleRestrictionComplex` applies it
  degreewise.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.injective_smallEtaleRestriction` and
  `AlgebraicGeometry.BigEtaleSpaceSite.injective_bigToSmallEtaleRestriction`: **Stacks 0DG8**,
  part (1).
* `AlgebraicGeometry.BigEtaleSpaceSite.isKInjective_smallEtaleRestriction` and
  `AlgebraicGeometry.BigEtaleSpaceSite.isKInjective_bigToSmallEtaleRestriction`:
  **Stacks 0DG8**, part (2).

## Implementation notes

Both halves of the statement come from exactness of the left adjoint of restriction, the lower
shriek functor of the relevant continuous functor of sites: that is
`Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits` together with
`Stacks.Sites.LowerShriek.gShriek_preservesFiniteColimits`, so no Kan extension is recomputed
here. Injectives are then preserved by
`CategoryTheory.preservesInjectiveObjects_of_isExact` and K-injectivity by
`CochainComplex.isKInjective_mapHomologicalComplex_of_exact`.

The finite limits of the spaces-étale site and their preservation by the inclusion are the
instances supplied with Tag 0DF3, and the big étale site of `X` is the slice category `Over X`,
so the fibre products and equalizers the exactness statement needs are already available to
instance search. Continuity of the inclusion of the spaces-étale site of `X` is the
morphism-of-sites statement of Tag 0DF3, available as the instance
`AlgebraicGeometry.BigEtaleSpaceSite.spacesEtaleInclusion_isContinuous`. Sheafification of
abelian groups needs no hypothesis: every site here is essentially small, so
`CategoryTheory.hasSheafifyEssentiallySmallSite` applies.

The morphism `f` is not required to be étale; only objects of the big étale site enter.

## References

* [Stacks Project, Tag 0DG8](https://stacks.math.columbia.edu/tag/0DG8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

/-! ### Restriction along the inclusion functors -/

/-- **Stacks 0DG8.** Restriction of abelian sheaves from the big étale site of `X` to the
spaces-étale site of `Y`: the inverse image of the morphism of topoi `i_f` of Tag 0DF2. -/
noncomputable abbrev smallEtaleRestriction {X Y : T.Spaces} (f : Y ⟶ X) :
    Sheaf (T.bigEtaleTopology X) Ab.{u + 1} ⥤
      Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1} :=
  (inclusionFunctor T f).sheafPushforwardContinuous Ab.{u + 1}
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (T.bigEtaleTopology X)

/-- **Stacks 0DG8.** Restriction of abelian sheaves from the big étale site of `X` to the
spaces-étale site of `X`, identified in Tag 0DF3 both with the inverse image of `i_X` and with
the direct image of `π_X`. -/
noncomputable abbrev bigToSmallEtaleRestriction (X : T.Spaces) :
    Sheaf (T.bigEtaleTopology X) Ab.{u + 1} ⥤
      Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1} :=
  (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X).sheafPushforwardContinuous
    Ab.{u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
    (T.bigEtaleTopology X)

/-- Restriction along `i_f` is additive, being a restriction of presheaves. -/
instance smallEtaleRestriction_additive {X Y : T.Spaces} (f : Y ⟶ X) :
    (smallEtaleRestriction T f).Additive := ⟨rfl⟩

/-- Restriction to the spaces-étale site of `X` is additive, being a restriction of
presheaves. -/
instance bigToSmallEtaleRestriction_additive (X : T.Spaces) :
    (bigToSmallEtaleRestriction T X).Additive := ⟨rfl⟩

/-- **Stacks 0DG8.** Degreewise restriction of complexes of abelian sheaves from the big étale
site of `X` to the spaces-étale site of `X`. -/
noncomputable def bigToSmallEtaleRestrictionComplex (X : T.Spaces) :
    CochainComplex (Sheaf (T.bigEtaleTopology X) Ab.{u + 1}) ℤ ⥤
      CochainComplex
        (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1}) ℤ :=
  (bigToSmallEtaleRestriction T X).mapHomologicalComplex (ComplexShape.up ℤ)

/-! ### Exactness of lower shriek -/

section Exactness

variable {X Y : T.Spaces} (f : Y ⟶ X)

/-- Lower shriek for the inclusion of the spaces-étale site of `Y` into the big étale site of
`X` preserves finite limits. -/
private noncomputable instance lowerShriekAb_preservesFiniteLimits :
    PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (inclusionFunctor T f) Ab.{u + 1}
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (T.bigEtaleTopology X)) :=
  Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits.{u + 1, u + 1, u + 1, u + 1, u + 1}
    (inclusionFunctor T f) (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
    (T.bigEtaleTopology X)

/-- Lower shriek for the inclusion of the spaces-étale site of `Y` into the big étale site of
`X` preserves finite colimits. -/
private noncomputable instance lowerShriekAb_preservesFiniteColimits :
    PreservesFiniteColimits (Functor.sheafPullbackConstruction.sheafPullback
      (inclusionFunctor T f) Ab.{u + 1}
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (T.bigEtaleTopology X)) :=
  Stacks.Sites.LowerShriek.gShriek_preservesFiniteColimits AddCommGrpCat.{u + 1}
    (inclusionFunctor T f) (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
    (T.bigEtaleTopology X)

end Exactness

section ExactnessId

variable (X : T.Spaces)

/-- Lower shriek for the inclusion of the spaces-étale site of `X` into the big étale site of
`X` preserves finite limits. -/
private noncomputable instance lowerShriekAbId_preservesFiniteLimits :
    PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X) Ab.{u + 1}
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (T.bigEtaleTopology X)) :=
  Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits.{u + 1, u + 1, u + 1, u + 1, u + 1}
    (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X)
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (T.bigEtaleTopology X)

/-- Lower shriek for the inclusion of the spaces-étale site of `X` into the big étale site of
`X` preserves finite colimits. -/
private noncomputable instance lowerShriekAbId_preservesFiniteColimits :
    PreservesFiniteColimits (Functor.sheafPullbackConstruction.sheafPullback
      (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X) Ab.{u + 1}
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (T.bigEtaleTopology X)) :=
  Stacks.Sites.LowerShriek.gShriek_preservesFiniteColimits AddCommGrpCat.{u + 1}
    (Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X)
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (T.bigEtaleTopology X)

end ExactnessId

/-! ### Injectives and K-injective complexes -/

/-- **Stacks 0DG8, part (1).** The inverse image along `i_f` of an injective abelian sheaf on
the big étale site of `X` is an injective abelian sheaf on the spaces-étale site of `Y`. -/
@[stacks 0DG8 "part (1), injectives restrict along i_f"]
theorem injective_smallEtaleRestriction {X Y : T.Spaces} (f : Y ⟶ X)
    (I : Sheaf (T.bigEtaleTopology X) Ab.{u + 1}) [Injective I] :
    Injective ((smallEtaleRestriction T f).obj I) := by
  let J := Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y
  let K := T.bigEtaleTopology X
  let v := inclusionFunctor T f
  let R := v.sheafPushforwardContinuous Ab.{u + 1} J K
  let L := Functor.sheafPullbackConstruction.sheafPullback v Ab.{u + 1} J K
  let adj : L ⊣ R :=
    Functor.sheafPullbackConstruction.sheafAdjunctionContinuous v Ab.{u + 1} J K
  have : R.Additive := Functor.additive_of_preserves_binary_products _
  have : L.Additive := Functor.additive_of_preserves_binary_products _
  have : R.PreservesInjectiveObjects :=
    preservesInjectiveObjects_of_isExact R L adj ⟨inferInstance, inferInstance⟩
  exact Functor.injective_obj_of_injective R inferInstance

/-- **Stacks 0DG8, part (1).** The restriction to the spaces-étale site of `X` of an injective
abelian sheaf on the big étale site of `X` is injective. -/
@[stacks 0DG8 "part (1), injectives restrict to the small site"]
theorem injective_bigToSmallEtaleRestriction (X : T.Spaces)
    (I : Sheaf (T.bigEtaleTopology X) Ab.{u + 1}) [Injective I] :
    Injective ((bigToSmallEtaleRestriction T X).obj I) := by
  let J := Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X
  let K := T.bigEtaleTopology X
  let v := Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X
  let R := v.sheafPushforwardContinuous Ab.{u + 1} J K
  let L := Functor.sheafPullbackConstruction.sheafPullback v Ab.{u + 1} J K
  let adj : L ⊣ R :=
    Functor.sheafPullbackConstruction.sheafAdjunctionContinuous v Ab.{u + 1} J K
  have : R.Additive := Functor.additive_of_preserves_binary_products _
  have : L.Additive := Functor.additive_of_preserves_binary_products _
  have : R.PreservesInjectiveObjects :=
    preservesInjectiveObjects_of_isExact R L adj ⟨inferInstance, inferInstance⟩
  exact Functor.injective_obj_of_injective R inferInstance

/-- **Stacks 0DG8, part (2).** The inverse image along `i_f` of a K-injective complex of
abelian sheaves on the big étale site of `X` is a K-injective complex on the spaces-étale site
of `Y`. -/
@[stacks 0DG8 "part (2), K-injectivity restricts along i_f"]
theorem isKInjective_smallEtaleRestriction {X Y : T.Spaces} (f : Y ⟶ X)
    (I : CochainComplex (Sheaf (T.bigEtaleTopology X) Ab.{u + 1}) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((smallEtaleRestriction T f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  let J := Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y
  let K := T.bigEtaleTopology X
  let v := inclusionFunctor T f
  let R := v.sheafPushforwardContinuous Ab.{u + 1} J K
  let L := Functor.sheafPullbackConstruction.sheafPullback v Ab.{u + 1} J K
  let adj : L ⊣ R :=
    Functor.sheafPullbackConstruction.sheafAdjunctionContinuous v Ab.{u + 1} J K
  have : R.Additive := Functor.additive_of_preserves_binary_products _
  have : L.Additive := Functor.additive_of_preserves_binary_products _
  exact CochainComplex.isKInjective_mapHomologicalComplex_of_exact R L adj I

/-- **Stacks 0DG8, part (2).** The restriction to the spaces-étale site of `X` of a K-injective
complex of abelian sheaves on the big étale site of `X` is K-injective. -/
@[stacks 0DG8 "part (2), K-injectivity restricts to the small site"]
theorem isKInjective_bigToSmallEtaleRestriction (X : T.Spaces)
    (I : CochainComplex (Sheaf (T.bigEtaleTopology X) Ab.{u + 1}) ℤ) [I.IsKInjective] :
    ((bigToSmallEtaleRestrictionComplex T X).obj I).IsKInjective := by
  let J := Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X
  let K := T.bigEtaleTopology X
  let v := Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem X
  let R := v.sheafPushforwardContinuous Ab.{u + 1} J K
  let L := Functor.sheafPullbackConstruction.sheafPullback v Ab.{u + 1} J K
  let adj : L ⊣ R :=
    Functor.sheafPullbackConstruction.sheafAdjunctionContinuous v Ab.{u + 1} J K
  have : R.Additive := Functor.additive_of_preserves_binary_products _
  have : L.Additive := Functor.additive_of_preserves_binary_products _
  exact CochainComplex.isKInjective_mapHomologicalComplex_of_exact R L adj I

end AlgebraicGeometry.BigEtaleSpaceSite

end
