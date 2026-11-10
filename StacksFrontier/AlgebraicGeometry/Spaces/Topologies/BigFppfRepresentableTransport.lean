module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigToSmallEtaleFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.HigherDirectImages

/-!
# Schemes over a scheme-valued point of an algebraic space

Let `B` be a big fppf site, `S` a scheme of `B` and `X` an algebraic space over `S`. A morphism
`s : h_A ⟶ X` from the algebraic space represented by a scheme `A` over `S` gives a functor

`Ψ_s : (Sch/A) ⥤ (Spaces/X)`, `(W → A) ↦ (h_W → h_A → X)`,

from the big category of schemes over `A` to the slice of algebraic spaces over `X`. For the fppf
topologies `Ψ_s` is continuous and cocontinuous, and restriction of abelian sheaves along it is
exact and preserves injective objects; for the étale topologies it preserves covering sieves.

## Main definitions

* `AlgebraicGeometry.Space.schemeSliceToSpaceSlice`: the functor `Ψ_s`.

## Main results

* `AlgebraicGeometry.Space.schemeSliceToSpaceSlice_isContinuous` and
  `AlgebraicGeometry.Space.schemeSliceToSpaceSlice_isCocontinuous`: `Ψ_s` is continuous and
  cocontinuous for the fppf topologies.
* `AlgebraicGeometry.Space.schemeSliceToSpaceSliceEtale_coverPreserving`: `Ψ_s` preserves covering
  sieves for the étale topologies.

## References

* [Stacks Project, Tag 0DFV](https://stacks.math.columbia.edu/tag/0DFV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X : AlgebraicSpaces B S hS}
  (A : BigFppfOver B S hS) (s : (schemeSpaceFunctor B S hS).obj A ⟶ X)

/-- The functor `Ψ_s : (Sch/A) ⥤ (Spaces/X)` attached to a morphism `s : h_A ⟶ X` from the
algebraic space represented by a scheme `A` over `S`: a scheme `W` over `A` goes to the
algebraic space `h_W`, over `X` through `h_W ⟶ h_A ⟶ X`. -/
abbrev schemeSliceToSpaceSlice : Over A.left ⥤ Over X :=
  (Over.iteratedSliceEquiv A).inverse ⋙ Over.post (schemeSpaceFunctor B S hS) ⋙ Over.map s

section Fppf

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) {X : T.Spaces} (A : T.Schemes)
  (s : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj A ⟶ X)

/-- The inclusion of schemes over `S` into algebraic spaces over `S` is a dense subsite for the
fppf topologies. -/
instance schemeSpaceFunctor_isDenseSubsite :
    (schemeSpaceFunctor T.schemeSite S T.scheme_mem).IsDenseSubsite
      (BigFppfOver.topology T.schemeSite S T.scheme_mem) T.topology :=
  (fppfSchemeToSpace_isSpecialCocontinuous T).2

/-- The inclusion of schemes over `S` into algebraic spaces over `S` is cocontinuous for the fppf
topologies. -/
instance schemeSpaceFunctor_isCocontinuous :
    (schemeSpaceFunctor T.schemeSite S T.scheme_mem).IsCocontinuous
      (BigFppfOver.topology T.schemeSite S T.scheme_mem) T.topology :=
  (fppfSchemeToSpace_isSpecialCocontinuous T).1

/-- The inclusion of schemes over `A` into algebraic spaces over `h_A` is a dense subsite for the
fppf topologies. -/
instance overPost_schemeSpaceFunctor_isDenseSubsite :
    (Over.post (X := A) (schemeSpaceFunctor T.schemeSite S T.scheme_mem)).IsDenseSubsite
      ((BigFppfOver.topology T.schemeSite S T.scheme_mem).over A)
      (T.topology.over ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj A)) :=
  Stacks.Sites.overPost_isDenseSubsite (J := BigFppfOver.topology T.schemeSite S
    T.scheme_mem) (K := T.topology) (schemeSpaceFunctor T.schemeSite S T.scheme_mem) A

/-- **`Ψ_s` is continuous for the fppf topologies.** -/
instance schemeSliceToSpaceSlice_isContinuous :
    (schemeSliceToSpaceSlice T.schemeSite S T.scheme_mem A s).IsContinuous
      (T.schemeSite.topology.over A.left) (T.topology.over X) := by
  have : (Over.post (X := A) (schemeSpaceFunctor T.schemeSite S T.scheme_mem) ⋙
      Over.map s).IsContinuous ((BigFppfOver.topology T.schemeSite S T.scheme_mem).over A)
      (T.topology.over X) :=
    Functor.isContinuous_comp _ _ _
      (T.topology.over ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj A)) _
  exact Functor.isContinuous_comp _ _ _
    ((BigFppfOver.topology T.schemeSite S T.scheme_mem).over A) _

/-- **`Ψ_s` is cocontinuous for the fppf topologies.** -/
instance schemeSliceToSpaceSlice_isCocontinuous :
    (schemeSliceToSpaceSlice T.schemeSite S T.scheme_mem A s).IsCocontinuous
      (T.schemeSite.topology.over A.left) (T.topology.over X) := by
  have : (Over.post (X := A) (schemeSpaceFunctor T.schemeSite S T.scheme_mem) ⋙
      Over.map s).IsCocontinuous ((BigFppfOver.topology T.schemeSite S T.scheme_mem).over A)
      (T.topology.over X) :=
    CategoryTheory.isCocontinuous_comp _ _ _
      (T.topology.over ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj A))
  exact CategoryTheory.isCocontinuous_comp _ _ _
    ((BigFppfOver.topology T.schemeSite S T.scheme_mem).over A)

/-! ### Restriction of abelian sheaves along `Ψ_s` -/

/-- A functor isomorphic to one preserving injective objects preserves injective objects. -/
private theorem preservesInjectiveObjects_of_iso {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ]
    {F G : 𝒜 ⥤ ℬ} (e : F ≅ G) [F.PreservesInjectiveObjects] : G.PreservesInjectiveObjects where
  injective_obj {X} _ := Injective.of_iso (e.app X) inferInstance

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) {X : T.Spaces} (A : T.Schemes)
  (s : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj A ⟶ X)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for discrete limits of presheaves on the big fppf site exceeds the default
-- budget
/-- Discrete limits of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_bigFppfRepresentableTransport
    (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver T.schemeSite S T.scheme_mem)ᵒᵖ ⥤ Type u) :=
  inferInstance

/-- Restriction of abelian sheaves along `Ψ_s`, from the big fppf site of `X` to the big fppf
site of the scheme `A`. -/
abbrev schemeSliceRestriction :
    Sheaf (T.topology.over X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (T.schemeSite.topology.over A.left) AddCommGrpCat.{u + 1} :=
  (schemeSliceToSpaceSlice T.schemeSite S T.scheme_mem A s).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (T.schemeSite.topology.over A.left) (T.topology.over X)

/-- Restriction of abelian sheaves along `Over.post` of the inclusion of schemes into algebraic
spaces, followed by restriction along the inverse of the iterated slice equivalence
`(Sch/S)/A ≌ Sch/A`. -/
private abbrev schemeSliceDenseRestriction :
    Sheaf (T.topology.over ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj A))
        AddCommGrpCat.{u + 1} ⥤
      Sheaf (T.schemeSite.topology.over A.left) AddCommGrpCat.{u + 1} :=
  (Over.post (X := A) (schemeSpaceFunctor T.schemeSite S T.scheme_mem)).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} ((BigFppfOver.topology T.schemeSite S T.scheme_mem).over A)
      (T.topology.over ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj A)) ⋙
    (Over.iteratedSliceEquiv A).inverse.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (T.schemeSite.topology.over A.left)
      ((BigFppfOver.topology T.schemeSite S T.scheme_mem).over A)

private instance schemeSliceDenseRestriction_isEquivalence :
    (schemeSliceDenseRestriction T A).IsEquivalence :=
  inferInstanceAs ((Over.post (X := A) (schemeSpaceFunctor T.schemeSite S
    T.scheme_mem)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      ((BigFppfOver.topology T.schemeSite S T.scheme_mem).over A)
      (T.topology.over ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj A)) ⋙
    (Over.iteratedSliceEquiv A).inverse.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (T.schemeSite.topology.over A.left)
      ((BigFppfOver.topology T.schemeSite S T.scheme_mem).over A)).IsEquivalence

/-- Restriction along `Ψ_s` is restriction along composition with `s` followed by an
equivalence. -/
private theorem schemeSliceRestriction_eq :
    schemeSliceRestriction T A s =
      T.topology.overMapPullback AddCommGrpCat.{u + 1} s ⋙ schemeSliceDenseRestriction T A :=
  rfl

/-- Restriction of abelian sheaves along `Ψ_s` preserves finite limits. -/
instance schemeSliceRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (schemeSliceRestriction T A s) := by
  rw [schemeSliceRestriction_eq]
  exact comp_preservesFiniteLimits _ _

/-- Restriction of abelian sheaves along `Ψ_s` preserves finite colimits. -/
instance schemeSliceRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (schemeSliceRestriction T A s) := by
  rw [schemeSliceRestriction_eq]
  exact comp_preservesFiniteColimits _ _

/-- Restriction of abelian sheaves along `Ψ_s` preserves injective objects. -/
instance schemeSliceRestriction_preservesInjectiveObjects :
    (schemeSliceRestriction T A s).PreservesInjectiveObjects := by
  rw [schemeSliceRestriction_eq]
  have : (T.topology.overMapPullback AddCommGrpCat.{u + 1} s).PreservesInjectiveObjects :=
    Stacks.Cohomology.Localization.overPullback_preservesInjectiveObjects T.topology s
  infer_instance

/-- Restriction of abelian sheaves along `Ψ_s` is additive. -/
instance schemeSliceRestriction_additive : (schemeSliceRestriction T A s).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Restriction of abelian sheaves along `Ψ_s` preserves homology. -/
instance schemeSliceRestriction_preservesHomology :
    (schemeSliceRestriction T A s).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- **For `X = h_A` and `s = 𝟙`, restriction of sheaves of sets along `Ψ_s` is an equivalence**:
the big fppf topos of the scheme `A` is the big fppf topos of the algebraic space `h_A`
(Stacks 0DFV, localized at `A`). -/
instance schemeSliceToSpaceSlice_id_isEquivalence :
    ((schemeSliceToSpaceSlice T.schemeSite S T.scheme_mem A (𝟙 _)).sheafPushforwardContinuous
      (Type (u + 1)) (T.schemeSite.topology.over A.left)
      (T.topology.over
        ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj A))).IsEquivalence := by
  have e : T.topology.overMapPullback (Type (u + 1))
      (𝟙 ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj A)) ≅ 𝟭 _ :=
    T.topology.overMapPullbackId (Type (u + 1)) _
  have : (T.topology.overMapPullback (Type (u + 1))
      (𝟙 ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj A))).IsEquivalence :=
    Functor.isEquivalence_of_iso e.symm
  exact inferInstanceAs (T.topology.overMapPullback (Type (u + 1)) (𝟙 _) ⋙
    ((Over.post (X := A) (schemeSpaceFunctor T.schemeSite S
      T.scheme_mem)).sheafPushforwardContinuous (Type (u + 1))
      ((BigFppfOver.topology T.schemeSite S T.scheme_mem).over A)
      (T.topology.over ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj A)) ⋙
    (Over.iteratedSliceEquiv A).inverse.sheafPushforwardContinuous (Type (u + 1))
      (T.schemeSite.topology.over A.left)
      ((BigFppfOver.topology T.schemeSite S T.scheme_mem).over A))).IsEquivalence

end Fppf

section Etale

variable {S : Scheme.{u}} (E : BigEtaleSpaceSite S) {X : E.Spaces}
  (A : BigEtaleOver (associatedBigEtaleSite E.fppfSite) S E.fppf_mem)
  (s : (BigEtaleSpaceSite.schemeInclusion E).obj A ⟶ X)

/-- The functor `Ψ_s` for the big étale site: schemes over `A`, with the big étale topology of the
scheme `A`, mapped to algebraic spaces over `X` through `s`. As a functor it is
`AlgebraicGeometry.Space.schemeSliceToSpaceSlice`. -/
abbrev schemeSliceToSpaceSliceEtale :
    BigEtaleOver (associatedBigEtaleSite E.fppfSite) A.left.obj A.left.property ⥤ Over X :=
  BigEtaleSpaceSite.overSchemeInclusion E A ⋙ Over.map s

/-- **`Ψ_s` preserves covering sieves for the étale topologies.** -/
theorem schemeSliceToSpaceSliceEtale_coverPreserving :
    CoverPreserving
      (BigEtaleOver.topology (associatedBigEtaleSite E.fppfSite) A.left.obj A.left.property)
      (E.bigEtaleTopology X) (schemeSliceToSpaceSliceEtale E A s) := by
  have h₂ := Stacks.Sites.overPost_isDenseSubsite
    (J := BigEtaleOver.topology (associatedBigEtaleSite E.fppfSite) S E.fppf_mem)
    (K := E.topology) (BigEtaleSpaceSite.schemeInclusion E) A
  have h₁ : CoverPreserving
      (BigEtaleOver.topology (associatedBigEtaleSite E.fppfSite) A.left.obj A.left.property)
      ((BigEtaleOver.topology (associatedBigEtaleSite E.fppfSite) S E.fppf_mem).over A)
      (Over.iteratedSliceEquiv A).inverse := by
    rw [bigEtaleOver_topology_eq, bigEtaleOver_topology_eq]
    exact Functor.IsDenseSubsite.coverPreserving
      ((associatedBigEtaleSite E.fppfSite).topology.over A.left)
      (((associatedBigEtaleSite E.fppfSite).topology.over _).over A) _
  exact CoverPreserving.comp (hF := CoverPreserving.comp (hF := h₁)
      (hG := Functor.IsDenseSubsite.coverPreserving _
        (E.bigEtaleTopology ((BigEtaleSpaceSite.schemeInclusion E).obj A))
        (Over.post (X := A) (BigEtaleSpaceSite.schemeInclusion E))))
    (hG := GrothendieckTopology.over_map_coverPreserving E.topology s)

/-- `Ψ_s` is continuous for the étale topologies. -/
instance schemeSliceToSpaceSliceEtale_isContinuous :
    (schemeSliceToSpaceSliceEtale E A s).IsContinuous
      (BigEtaleOver.topology (associatedBigEtaleSite E.fppfSite) A.left.obj A.left.property)
      (E.bigEtaleTopology X) :=
  Functor.isContinuous_comp _ _ _
    (E.bigEtaleTopology ((BigEtaleSpaceSite.schemeInclusion E).obj A)) _

/-- **`π_X⁻¹` restricted along `Ψ_s` is the scheme `π_A⁻¹` of the restriction of the sheaf.**
For a sheaf `F` on the spaces-étale site of `X`, the restriction of `π_X⁻¹F` along `Ψ_s` to the
big étale site of the scheme `A` is `π_A⁻¹` of the sheaf on the small étale site of `A` obtained
from `s_small⁻¹F`, naturally in `F`. -/
def schemeSliceToSpaceSliceEtale_bigToSmall_inverseImageIso :
    (E.bigToSmallEtaleMorphism X).inverseImage ⋙
        (schemeSliceToSpaceSliceEtale E A s).sheafPushforwardContinuous (Type (u + 1))
          (BigEtaleOver.topology (associatedBigEtaleSite E.fppfSite) A.left.obj A.left.property)
          (E.bigEtaleTopology X) ≅
      (E.smallEtaleMorphism s).inverseImage ⋙
        (representedSpacesEtaleSheafEquiv E.fppfSite S E.fppf_mem A).functor ⋙
        (bigEtaleToSmallEtaleMorphism (associatedBigEtaleSite E.fppfSite) A.left.obj
          A.left.property).inverseImage :=
  Functor.isoWhiskerRight (E.bigEtaleMorphism_inverseImageIso s)
      ((BigEtaleSpaceSite.overSchemeInclusion E A).sheafPushforwardContinuous (Type (u + 1))
        (BigEtaleOver.topology (associatedBigEtaleSite E.fppfSite) A.left.obj A.left.property)
        (E.bigEtaleTopology ((BigEtaleSpaceSite.schemeInclusion E).obj A))) ≪≫
    Functor.isoWhiskerLeft (E.smallEtaleMorphism s).inverseImage
      (Functor.isoWhiskerRight (BigEtaleSpaceSite.chartProjectionInverseImageIso E A).symm
          ((BigEtaleSpaceSite.overSchemeInclusion E A).sheafPushforwardContinuous (Type (u + 1))
            (BigEtaleOver.topology (associatedBigEtaleSite E.fppfSite) A.left.obj
              A.left.property)
            (E.bigEtaleTopology ((BigEtaleSpaceSite.schemeInclusion E).obj A))) ≪≫
        Functor.isoWhiskerLeft (representedSpacesEtaleSheafEquiv E.fppfSite S E.fppf_mem A).functor
          (BigEtaleSpaceSite.schemeProjectionInverseImageIso E A).symm)

end Etale

end AlgebraicGeometry.Space

end
