module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZeroComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Adjunction
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite

/-!
# Extension by zero on the two presentations of the small étale site

Let `B` be a big étale site, `S` a scheme contained in it and `U` an object of the small étale
site of Stacks 021B of `S`, with structure morphism `j : U ⟶ S`. Extension by zero along `j` is
available on both presentations of the small étale site: on the site of Stacks 021B as the left
adjoint of restriction along `AlgebraicGeometry.smallEtalePostcompose`, and on Mathlib's
`AlgebraicGeometry.Scheme.smallEtaleTopology` as the left adjoint of restriction along
`AlgebraicGeometry.Scheme.Etale.smallEtaleCompose j`. This file identifies the two through the
equivalence `AlgebraicGeometry.SmallEtale.sheafEquiv` of their sheaf categories.

## Main definitions

* `AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardPostcomposeIso` — the two restrictions
  agree, since the two composition functors of sites agree after embedding the site of
  Stacks 021B in Mathlib's (`AlgebraicGeometry.SmallEtale.toEtaleSiteCompSmallEtaleComposeIso`).
* `AlgebraicGeometry.SmallEtale.toEtaleSiteExtensionByZeroIso` — hence, for arbitrary chosen
  left adjoints, the two extensions by zero agree.
* `AlgebraicGeometry.SmallEtale.sheafEquivExtensionByZeroIso` — the same with the equivalences
  of sheaf categories `AlgebraicGeometry.SmallEtale.sheafEquiv`.

## Implementation notes

This is `AlgebraicGeometry.SmallEtale.toEtaleSitePullbackBaseChangeIso` with composition in place
of base change: the comparison of sites holds objectwise by definition, both composites sending
a scheme `V` étale over `U` to `V` with structure morphism `V ⟶ U ⟶ S`, and the rest is the
passage to direct images and then to their left adjoints.

## References

* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 0GK1](https://stacks.math.columbia.edu/tag/0GK1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v' u'

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : SmallEtale B S hS)

/-- **Composition with `U ⟶ S` is continuous for Mathlib's presentation of the small étale
site**, in the spelling in which `U` is presented as an object of a big étale site and the target
is `S.Etale`: instance search does not pass between the two definitionally equal spellings of the
source scheme, nor to the spelling of
`AlgebraicGeometry.SmallEtale.isContinuous_smallEtaleCompose_inclusion_map_obj_hom`, whose target
is the étale site of `B.inclusion.obj (B.obj S hS)`. -/
instance isContinuous_smallEtaleCompose_inclusionMap :
    (Scheme.Etale.smallEtaleCompose (B.inclusion.map U.obj.hom)).IsContinuous
      U.obj.left.1.smallEtaleTopology S.smallEtaleTopology :=
  Scheme.Etale.smallEtaleCompose_isContinuous _

variable (A : Type u') [Category.{v'} A]

/-- **The two presentations of the small étale site have the same restriction to `U`.**
Restriction from `S` to `U` on Mathlib's site followed by restriction along the embedding of the
site of Stacks 021B of `U` is restriction along the embedding for `S` followed by restriction to
`U` on the site of Stacks 021B. -/
def toEtaleSitePushforwardPostcomposeIso :
    (Scheme.Etale.smallEtaleCompose (B.inclusion.map U.obj.hom)).sheafPushforwardContinuous A
          U.obj.left.1.smallEtaleTopology S.smallEtaleTopology ⋙
        (toEtaleSite B U.obj.left.1 U.obj.left.property).sheafPushforwardContinuous A
          (topology B U.obj.left.1 U.obj.left.property) U.obj.left.1.smallEtaleTopology ≅
      (toEtaleSite B S hS).sheafPushforwardContinuous A (topology B S hS) S.smallEtaleTopology ⋙
        (smallEtalePostcompose B S hS U).sheafPushforwardContinuous A
          (topology B U.obj.left.1 U.obj.left.property) (topology B S hS) := by
  haveI := isContinuous_smallEtaleCompose_inclusionMap B S hS U
  have hc1 : (toEtaleSite B U.obj.left.1 U.obj.left.property ⋙
      Scheme.Etale.smallEtaleCompose (B.inclusion.map U.obj.hom)).IsContinuous
      (topology B U.obj.left.1 U.obj.left.property) S.smallEtaleTopology :=
    Functor.isContinuous_comp _ _ _ U.obj.left.1.smallEtaleTopology _
  have hc2 : (smallEtalePostcompose B S hS U ⋙ toEtaleSite B S hS).IsContinuous
      (topology B U.obj.left.1 U.obj.left.property) S.smallEtaleTopology :=
    Functor.isContinuous_comp _ _ _ (topology B S hS) _
  exact Functor.sheafPushforwardContinuousComp'
      (F := toEtaleSite B U.obj.left.1 U.obj.left.property)
      (G := Scheme.Etale.smallEtaleCompose (B.inclusion.map U.obj.hom)) (Iso.refl _) _ _ _ _ ≪≫
    Functor.sheafPushforwardContinuousIso (toEtaleSiteCompSmallEtaleComposeIso B S hS U) _ _ _ ≪≫
      (Functor.sheafPushforwardContinuousComp' (F := smallEtalePostcompose B S hS U)
        (G := toEtaleSite B S hS) (Iso.refl _) _ _ _ _).symm

section ExtensionByZero

variable
  {LM : Sheaf U.obj.left.1.smallEtaleTopology A ⥤ Sheaf S.smallEtaleTopology A}
  {LB : Sheaf (topology B U.obj.left.1 U.obj.left.property) A ⥤ Sheaf (topology B S hS) A}
  {EU : Sheaf (topology B U.obj.left.1 U.obj.left.property) A ⥤
    Sheaf U.obj.left.1.smallEtaleTopology A}
  {ES : Sheaf (topology B S hS) A ⥤ Sheaf S.smallEtaleTopology A}
  (adjM : LM ⊣
    (Scheme.Etale.smallEtaleCompose (B.inclusion.map U.obj.hom)).sheafPushforwardContinuous A
      U.obj.left.1.smallEtaleTopology S.smallEtaleTopology)
  (adjB : LB ⊣ (smallEtalePostcompose B S hS U).sheafPushforwardContinuous A
      (topology B U.obj.left.1 U.obj.left.property) (topology B S hS))
  (adjU : EU ⊣ (toEtaleSite B U.obj.left.1 U.obj.left.property).sheafPushforwardContinuous A
      (topology B U.obj.left.1 U.obj.left.property) U.obj.left.1.smallEtaleTopology)
  (adjS : ES ⊣ (toEtaleSite B S hS).sheafPushforwardContinuous A (topology B S hS)
      S.smallEtaleTopology)

/-- **The two presentations of the small étale site have the same extension by zero.** The
left adjoint of restriction along the embedding for `U`, followed by extension by zero on
Mathlib's site, is extension by zero on the site of Stacks 021B followed by the left adjoint of
restriction along the embedding for `S`; the left adjoints may be any chosen ones. -/
def toEtaleSiteExtensionByZeroIso : EU ⋙ LM ≅ LB ⋙ ES :=
  Adjunction.leftAdjointUniq
    ((adjU.comp adjM).ofNatIsoRight (toEtaleSitePushforwardPostcomposeIso B S hS U A))
    (adjB.comp adjS)

end ExtensionByZero

/-- **The equivalence of the sheaves of the two presentations of the small étale site commutes
with extension by zero**, for any chosen left adjoints of the two restrictions to `U`. -/
def sheafEquivExtensionByZeroIso [HasLimitsOfSize.{u, u} A]
    {LM : Sheaf U.obj.left.1.smallEtaleTopology A ⥤ Sheaf S.smallEtaleTopology A}
    {LB : Sheaf (topology B U.obj.left.1 U.obj.left.property) A ⥤ Sheaf (topology B S hS) A}
    (adjM : LM ⊣
      (Scheme.Etale.smallEtaleCompose (B.inclusion.map U.obj.hom)).sheafPushforwardContinuous
        A U.obj.left.1.smallEtaleTopology S.smallEtaleTopology)
    (adjB : LB ⊣ (smallEtalePostcompose B S hS U).sheafPushforwardContinuous A
      (topology B U.obj.left.1 U.obj.left.property) (topology B S hS)) :
    (sheafEquiv B U.obj.left.1 U.obj.left.property A).functor ⋙ LM ≅
      LB ⋙ (sheafEquiv B S hS A).functor :=
  toEtaleSiteExtensionByZeroIso B S hS U A adjM adjB
    (sheafEquiv B U.obj.left.1 U.obj.left.property A).toAdjunction
    (sheafEquiv B S hS A).toAdjunction

end AlgebraicGeometry.SmallEtale
