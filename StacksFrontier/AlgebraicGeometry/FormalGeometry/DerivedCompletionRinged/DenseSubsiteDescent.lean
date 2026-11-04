module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.PushforwardConverse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackLowerShriek
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.DenseSubsiteMorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsite
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleRlimTensorLimit
import StacksCore.Tactic.StacksAttribute

/-!
# Derived completeness descends from a dense subsite

Let `A` and `Z` be ringed sites, let `v : A.C ⥤ Z.C` exhibit `A.C` as a dense subsite of `Z.C`
and let `α : 𝒪_A ⟶ v_*𝒪_Z` be an *invertible* structure map. Then `v` is a morphism of sites
([Stacks, Tag 00X6], because the inverse image is the inverse of an equivalence of topoi by
[Stacks, Tag 03A0]), so `(v, α)` is a morphism of ringed sites `Z ⟶ A`, and its direct image of
sheaves of modules is an equivalence: restriction of sections along a dense subsite is an
equivalence by the Comparison Lemma, and restriction of scalars along an isomorphism is one too.

This file reads the converse of [Stacks, Tag 099J] for such a morphism: the Milnor condition for
`R(v, α)_* L` on `A` forces the Milnor condition for `L` on `Z`. The condition is checked at an
object `W` of `Z.C` by covering `W` with arrows that factor through the image of `v`
(cover-density) and using the locality of the condition ([Stacks, Tag 0998]); at an object `v(U)`
it is the conservativity of the derived direct image on the slice.

## Main definitions

* `AlgebraicGeometry.RingedSite.denseRestrictHom`: `(v, α)`, as a morphism of ringed sites.

## Main results

* `AlgebraicGeometry.RingedSite.localizedPushforward_denseRestrictHom`: the direct image along
  the localization of `(v, α)` at `U` is restriction of sections along `Over.post v` followed by
  restriction of scalars — on the nose.
* `AlgebraicGeometry.RingedSite.reflectsIsomorphisms_derivedLocalizedPushforward`: the derived
  direct image along that localization reflects isomorphisms.
* `AlgebraicGeometry.RingedSite.isDerivedCompleteAtSection_of_denseRestrict`: **the Milnor
  condition descends from a dense subsite.**

## Implementation notes

The structure sheaf of a localized ringed site and the restriction to a slice of the structure
sheaf are the same sheaf of rings by definition but not after the reductions instance search
performs. The statements about derived functors below are therefore written at the *localized*
spelling, which is the one the derived direct image of a morphism of ringed topoi is declared at,
while `Stacks.Cohomology.Localization.localizedPushforward` is written at the restriction
spelling; `denseRestrictLocalized` and `denseRestrictLocalizedPushforward` name the localized
spellings so that the two do not have to be mixed inside one statement.

## References

* [Stacks Project, Tag 099J](https://stacks.math.columbia.edu/tag/099J)
* [Stacks Project, Tag 0998](https://stacks.math.columbia.edu/tag/0998)
* [Stacks Project, Tag 03A0](https://stacks.math.columbia.edu/tag/03A0)
* [Stacks Project, Tag 00X6](https://stacks.math.columbia.edu/tag/00X6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.Localization

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable (A Z : RingedSite.{u, u, u}) (v : A.C ⥤ Z.C) [v.IsDenseSubsite A.J Z.J]
  (α : A.O ⟶ (v.sheafPushforwardContinuous CommRingCat.{u} A.J Z.J).obj Z.O)

/-- The underlying functor of a dense subsite inclusion is a morphism of sites: its inverse image
is the inverse of an equivalence of topoi, hence exact. -/
theorem isMorphismOfSites_of_isDenseSubsite : v.IsMorphismOfSites A.J Z.J :=
  (IsMorphismOfSites.ofIsDenseSubsite.{u} v).toSmallIsMorphismOfSites

/-- **Restriction to a dense subsite, as a morphism of ringed sites.** The underlying functor is
the dense subsite inclusion `v`, which is a morphism of sites, and the structure map is the given
`α : 𝒪_A ⟶ v_*𝒪_Z`. -/
def denseRestrictHom : RingedSite.Hom Z A where
  u := v
  isMorphismOfSites := isMorphismOfSites_of_isDenseSubsite A Z v
  fsharp := α

/-- The underlying functor of `denseRestrictHom A Z v α` is `v`. -/
@[simp]
theorem denseRestrictHom_u : (denseRestrictHom A Z v α).u = v := rfl

/-- The structure map of `denseRestrictHom A Z v α` is `α`. -/
@[simp]
theorem denseRestrictHom_fsharp : (denseRestrictHom A Z v α).fsharp = α := rfl

attribute [local instance] isContinuous_localized

/-- A slice of a dense subsite inclusion is again one ([Stacks, Tag 03A0] localized), in the
shape instance search keys on. -/
local instance overPostIsDenseSubsite (U : A.C) :
    (Over.post (X := U) v).IsDenseSubsite (A.J.over U) (Z.J.over (v.obj U)) :=
  Stacks.Sites.overPost_isDenseSubsite (J := A.J) (K := Z.J) v U

/-- **The direct image along the localization of `(v, α)` at an object is restriction of sections
along the slice of the dense subsite, followed by restriction of scalars.** The two are the same
functor on the nose: the direct image of sheaves of modules along a continuous functor *is*
restriction of sections followed by restriction of scalars, and the restriction to the slice at
`U` of the restriction along `v` of a sheaf of rings is the restriction along `Over.post v` of
its restriction to the slice at `v(U)`. -/
theorem localizedPushforward_denseRestrictHom (U : A.C) :
    Stacks.Cohomology.Localization.localizedPushforward (denseRestrictHom A Z v α) U =
      Stacks.DenseSubsiteModules.moduleRestriction (A.J.over U) (Z.J.over (v.obj U))
          (Over.post (X := U) v) ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over (v.obj U)) ⋙
        SheafOfModules.restrictScalars.{u}
          ((denseRestrictHom A Z v α).localized U).toRingedToposSiteHom.fSharpRing :=
  rfl

/-- **The direct image along `(v, α)` is restriction of sections along the dense subsite,
followed by restriction of scalars** — `localizedPushforward_denseRestrictHom` before
localization, and for the same reason. -/
theorem pushforwardTopos_denseRestrictHom :
    (denseRestrictHom A Z v α).toRingedToposSiteHom.pushforwardTopos =
      Stacks.DenseSubsiteModules.moduleRestriction A.J Z.J v
          (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) ⋙
        SheafOfModules.restrictScalars.{u}
          (denseRestrictHom A Z v α).toRingedToposSiteHom.fSharpRing :=
  rfl

variable [hfs : IsIso (denseRestrictHom A Z v α).toRingedToposSiteHom.fSharpRing]

include hfs in
/-- The structure map of the localization of a morphism of ringed sites is invertible as soon as
the structure map itself is: it is its image under restriction to a slice. -/
local instance isIso_fSharpRing_localized (U : A.C) :
    IsIso ((denseRestrictHom A Z v α).localized U).toRingedToposSiteHom.fSharpRing := by
  rw [fSharpRing_localized]
  exact Functor.map_isIso _ _

/-- **The direct image along `(v, α)` is an equivalence.** Restriction of sections along a dense
subsite is an equivalence by the Comparison Lemma for sheaves of abelian groups, transported to
sheaves of modules; and restriction of scalars along an invertible structure map is an
equivalence. -/
instance isEquivalence_pushforwardTopos :
    (denseRestrictHom A Z v α).toRingedToposSiteHom.pushforwardTopos.IsEquivalence := by
  have hF : (Stacks.DenseSubsiteModules.moduleRestriction A.J Z.J v
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).IsEquivalence :=
    inferInstance
  have hG : (SheafOfModules.restrictScalars.{u}
      (denseRestrictHom A Z v α).toRingedToposSiteHom.fSharpRing).IsEquivalence := inferInstance
  exact @Functor.isEquivalence_trans _ _ _ _ _ _ _ _ hF hG

/-- Additivity of the direct image along `(v, α)`, at the universes of a morphism of ringed
sites. -/
local instance additive_denseRestrictHom_pushforwardTopos :
    (denseRestrictHom A Z v α).toRingedToposSiteHom.pushforwardTopos.Additive :=
  RingedToposSiteHom.pushforwardTopos_additive.{u} _

/-- An equivalence is exact. -/
local instance preservesFiniteLimits_pushforwardTopos :
    PreservesFiniteLimits (denseRestrictHom A Z v α).toRingedToposSiteHom.pushforwardTopos :=
  inferInstance

/-- An equivalence is exact. -/
local instance preservesFiniteColimits_pushforwardTopos :
    PreservesFiniteColimits (denseRestrictHom A Z v α).toRingedToposSiteHom.pushforwardTopos :=
  inferInstance

/-- **The derived direct image along `(v, α)` is the functor that the direct image induces on
derived categories.** The direct image is an equivalence, hence exact, so it needs no derivation
and the two are right derived functors of the same functor on the homotopy category. -/
def derivedPushforwardDenseRestrictIso :
    (denseRestrictHom A Z v α).toRingedToposSiteHom.pushforwardTopos.mapDerivedCategory ≅
      derivedPushforward.{u} (denseRestrictHom A Z v α).toRingedToposSiteHom := by
  have inst : ((denseRestrictHom A Z v α).toRingedToposSiteHom.pushforwardTopos
      ).mapDerivedCategory.IsRightDerivedFunctor
      ((denseRestrictHom A Z v α).toRingedToposSiteHom.pushforwardTopos
        ).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Z).O))
        (ComplexShape.up ℤ)) :=
    CategoryTheory.Functor.isRightDerivedFunctor_of_inverts _ _
      ((denseRestrictHom A Z v α).toRingedToposSiteHom.pushforwardTopos
        ).mapDerivedCategoryFactorsh
  exact CategoryTheory.Functor.rightDerivedUnique
    (denseRestrictHom A Z v α).toRingedToposSiteHom.pushforwardTopos.mapDerivedCategory
    (derivedPushforward.{u} (denseRestrictHom A Z v α).toRingedToposSiteHom)
    ((denseRestrictHom A Z v α).toRingedToposSiteHom.pushforwardTopos
      ).mapDerivedCategoryFactorsh.inv
    (derivedPushforwardUnit.{u} (denseRestrictHom A Z v α).toRingedToposSiteHom)
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Z).O))
      (ComplexShape.up ℤ))

/-- **The derived direct image along `(v, α)` is an equivalence of derived categories.** -/
local instance isEquivalence_derivedPushforwardDenseRestrict :
    (derivedPushforward.{u} (denseRestrictHom A Z v α).toRingedToposSiteHom).IsEquivalence := by
  have hmap : ((denseRestrictHom A Z v α).toRingedToposSiteHom.pushforwardTopos
      ).mapDerivedCategory.IsEquivalence :=
    Stacks.Injectives.mapDerivedCategory_isEquivalence _
  exact Functor.isEquivalence_of_iso (derivedPushforwardDenseRestrictIso A Z v α)

/-- **The direct image along the localization of `(v, α)` at an object is an equivalence.**
Restriction of sections along the slice of a dense subsite is an equivalence by the Comparison
Lemma for sheaves of abelian groups, transported to sheaves of modules; and restriction of
scalars along an invertible structure map is an equivalence. -/
local instance isEquivalence_localizedPushforward (U : A.C) :
    (Stacks.Cohomology.Localization.localizedPushforward
      (denseRestrictHom A Z v α) U).IsEquivalence := by
  have hF : (Stacks.DenseSubsiteModules.moduleRestriction (A.J.over U) (Z.J.over (v.obj U))
      (Over.post (X := U) v)
      ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over (v.obj U))).IsEquivalence :=
    inferInstance
  have hG : (SheafOfModules.restrictScalars.{u}
      ((denseRestrictHom A Z v α).localized U).toRingedToposSiteHom.fSharpRing).IsEquivalence :=
    inferInstance
  exact @Functor.isEquivalence_trans _ _ _ _ _ _ _ _ hF hG

/-- An equivalence is exact. -/
local instance preservesFiniteLimits_localizedPushforward (U : A.C) :
    PreservesFiniteLimits (Stacks.Cohomology.Localization.localizedPushforward
      (denseRestrictHom A Z v α) U) := inferInstance

/-- An equivalence is exact. -/
local instance preservesFiniteColimits_localizedPushforward (U : A.C) :
    PreservesFiniteColimits (Stacks.Cohomology.Localization.localizedPushforward
      (denseRestrictHom A Z v α) U) := inferInstance

/-- An equivalence reflects isomorphisms. -/
local instance reflectsIsomorphisms_localizedPushforward (U : A.C) :
    (Stacks.Cohomology.Localization.localizedPushforward
      (denseRestrictHom A Z v α) U).ReflectsIsomorphisms := inferInstance

/-- The morphism of ringed sites `(v, α)`, localized at an object `U`, read as a morphism of
ringed topoi presented by a continuous functor of the underlying sites. The derived statements
below are written at this spelling of the localized structure sheaves. -/
abbrev denseRestrictLocalized (U : A.C) :=
  ((denseRestrictHom A Z v α).localized U).toRingedToposSiteHom

/-- The direct image of sheaves of modules along the localized morphism, in the localized
spelling of the structure sheaves. -/
abbrev denseRestrictLocalizedPushforward (U : A.C) :=
  (denseRestrictLocalized A Z v α U).pushforwardTopos

/-- Additivity of the localized direct image, in the localized spelling. -/
local instance additive_denseRestrictLocalized (U : A.C) :
    (denseRestrictLocalizedPushforward A Z v α U).Additive :=
  RingedToposSiteHom.pushforwardTopos_additive.{u} _

/-- Exactness of the localized direct image, in the localized spelling. -/
local instance preservesFiniteLimits_denseRestrictLocalized (U : A.C) :
    PreservesFiniteLimits (denseRestrictLocalizedPushforward A Z v α U) :=
  inferInstanceAs (PreservesFiniteLimits
    (Stacks.Cohomology.Localization.localizedPushforward (denseRestrictHom A Z v α) U))

/-- Exactness of the localized direct image, in the localized spelling. -/
local instance preservesFiniteColimits_denseRestrictLocalized (U : A.C) :
    PreservesFiniteColimits (denseRestrictLocalizedPushforward A Z v α U) :=
  inferInstanceAs (PreservesFiniteColimits
    (Stacks.Cohomology.Localization.localizedPushforward (denseRestrictHom A Z v α) U))

/-- Conservativity of the localized direct image, in the localized spelling. -/
local instance reflectsIsomorphisms_denseRestrictLocalized (U : A.C) :
    (denseRestrictLocalizedPushforward A Z v α U).ReflectsIsomorphisms :=
  inferInstanceAs (Stacks.Cohomology.Localization.localizedPushforward
    (denseRestrictHom A Z v α) U).ReflectsIsomorphisms

/-- **The derived direct image along the localization of `(v, α)` is the functor that the direct
image induces on derived categories.** The direct image is an equivalence, hence exact, so it
needs no derivation and the two are right derived functors of the same functor on the homotopy
category. -/
def derivedLocalizedPushforwardDenseRestrictIso (U : A.C) :
    (denseRestrictLocalizedPushforward A Z v α U).mapDerivedCategory ≅
      derivedPushforward.{u} (denseRestrictLocalized A Z v α U) := by
  have inst :
      (denseRestrictLocalizedPushforward A Z v α U).mapDerivedCategory.IsRightDerivedFunctor
      (denseRestrictLocalizedPushforward A Z v α U).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (Z.over ((denseRestrictHom A Z v α).u.obj U)).ringedTopos.O)))
        (ComplexShape.up ℤ)) :=
    CategoryTheory.Functor.isRightDerivedFunctor_of_inverts _ _
      (denseRestrictLocalizedPushforward A Z v α U).mapDerivedCategoryFactorsh
  exact CategoryTheory.Functor.rightDerivedUnique
    (denseRestrictLocalizedPushforward A Z v α U).mapDerivedCategory
    (derivedPushforward.{u} (denseRestrictLocalized A Z v α U))
    (denseRestrictLocalizedPushforward A Z v α U).mapDerivedCategoryFactorsh.inv
    (derivedPushforwardUnit.{u} (denseRestrictLocalized A Z v α U))
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Z.over ((denseRestrictHom A Z v α).u.obj U)).ringedTopos.O)))
      (ComplexShape.up ℤ))

/-- **The derived direct image along the localization of `(v, α)` reflects isomorphisms.** It is
the functor an equivalence induces on derived categories, and an exact functor reflecting
isomorphisms reflects them degreewise on cohomology, hence on derived categories. -/
theorem reflectsIsomorphisms_derivedLocalizedPushforward (U : A.C) :
    (Stacks.Cohomology.Localization.derivedLocalizedPushforward
      (denseRestrictHom A Z v α) U).ReflectsIsomorphisms := by
  have h : (derivedPushforward.{u}
      (denseRestrictLocalized A Z v α U)).ReflectsIsomorphisms := by
    constructor
    intro M N φ hφ
    have h₁ : IsIso ((denseRestrictLocalizedPushforward A Z v α U).mapDerivedCategory.map φ) :=
      (NatIso.isIso_map_iff
        (derivedLocalizedPushforwardDenseRestrictIso A Z v α U) φ).mpr hφ
    exact isIso_of_reflects_iso φ
      (denseRestrictLocalizedPushforward A Z v α U).mapDerivedCategory
  exact h

/-- **The Milnor condition descends from a dense subsite, at an object of the subsite.** The
derived direct image along `(v, α)` reflects isomorphisms on the slice at `U`, so the Milnor
condition for `R(v, α)_*L` at a section `t` over `U` forces it for `L` at `α(t)` over `v(U)`. -/
theorem isDerivedCompleteAtSection_of_denseRestrict_image (U : A.C)
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
    (t : (Stacks.SheafOfModules.Tensor.ringSheaf A.O).obj.obj (op U))
    (h : IsDerivedCompleteAtSection A
      ((derivedPushforward.{u} (denseRestrictHom A Z v α).toRingedToposSiteHom).obj L) U t) :
    IsDerivedCompleteAtSection Z L (v.obj U) (fSharpSection (denseRestrictHom A Z v α) U t) :=
  isDerivedCompleteAtSection_of_derivedPushforward (denseRestrictHom A Z v α) U
    (reflectsIsomorphisms_derivedLocalizedPushforward A Z v α U) L t h

/-- **The Milnor condition descends from a dense subsite.** The sieve of arrows into `W` that
factor through the image of `v` is covering, by cover-density, so by the locality of the Milnor
condition ([Stacks, Tag 0998], as
`AlgebraicGeometry.RingedSite.IsDerivedCompleteAtSection.of_sieve`) it is enough to check the
condition at the members of that sieve; each factors through some `v(U)`, where
`isDerivedCompleteAtSection_of_denseRestrict_image` applies, and the condition is stable under
further restriction. -/
theorem isDerivedCompleteAtSection_of_denseRestrict (W : Z.C)
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
    (s : (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj.obj (op W))
    (h : ∀ (U : A.C) (a : v.obj U ⟶ W)
        (t : (Stacks.SheafOfModules.Tensor.ringSheaf A.O).obj.obj (op U)),
      fSharpSection (denseRestrictHom A Z v α) U t =
          (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj.map a.op s →
        IsDerivedCompleteAtSection A
          ((derivedPushforward.{u} (denseRestrictHom A Z v α).toRingedToposSiteHom).obj L) U t) :
    IsDerivedCompleteAtSection Z L W s := by
  refine IsDerivedCompleteAtSection.of_sieve Z L s (Sieve.coverByImage v W)
    ((Functor.IsDenseSubsite.isCoverDense A.J Z.J v).is_cover W) ?_
  rintro V a ⟨⟨O, lift, map, fac⟩⟩
  obtain ⟨t, ht⟩ : ∃ t : (Stacks.SheafOfModules.Tensor.ringSheaf A.O).obj.obj (op O),
      fSharpSection (denseRestrictHom A Z v α) O t =
        (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj.map map.op s := by
    have hiso : IsIso
        ((denseRestrictHom A Z v α).toRingedToposSiteHom.fSharpRing.hom.app (op O)) :=
      Functor.map_isIso (sheafToPresheaf A.J RingCat.{u} ⋙
        (evaluation A.Cᵒᵖ RingCat.{u}).obj (op O))
        (denseRestrictHom A Z v α).toRingedToposSiteHom.fSharpRing
    exact ⟨inv ((denseRestrictHom A Z v α).toRingedToposSiteHom.fSharpRing.hom.app (op O))
      ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj.map map.op s), IsIso.inv_hom_id_apply _ _⟩
  have hO := isDerivedCompleteAtSection_of_denseRestrict_image A Z v α O L t (h O map t ht)
  rw [ht] at hO
  have hV := IsDerivedCompleteAtSection.restrict Z L lift _ hO
  have hmap : (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj.map lift.op
      ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj.map map.op s) =
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj.map a.op s := by
    rw [← fac, op_comp, (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj.map_comp,
      RingCat.comp_apply]
  exact hmap ▸ hV

section SliceInstances

open scoped IsMulCommutative

attribute [local instance] isMulCommutative_over overCatCenterLinear
  overFunctor_preservesFiniteLimits overFunctor_preservesFiniteColimits
  hasProductsOfShape_nat_derivedCategory_over

/-- The Milnor condition at a section depends only on the isomorphism class of the complex:
restriction to a slice is a functor, so an isomorphism of complexes becomes an isomorphism of
their restrictions, along which `isDerivedCompleteAt_iff_of_iso` transports the condition. -/
theorem isDerivedCompleteAtSection_of_iso (Y : RingedSite.{u, u, u})
    {K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    (ε : K ≅ L) (U : Y.C)
    (t : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (op U))
    (h : IsDerivedCompleteAtSection Y K U t) :
    IsDerivedCompleteAtSection Y L U t :=
  (isDerivedCompleteAt_iff_of_iso
    ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      U).mapDerivedCategory.mapIso ε) _).mp h

end SliceInstances

/-- **The Milnor condition ascends to a dense subsite.** The derived direct image along `(v, α)`
is an equivalence, so every complex `K` on `A` is the image of one on `Z`; the statement is made
for an arbitrary `L` together with an isomorphism `R(v, α)_*L ≅ K`, which is what the
`isEquivalence_derivedPushforwardDenseRestrict` instance produces.

This is `isDerivedCompleteAtSection_of_denseRestrict` with the hypothesis read on `K` rather
than on `R(v, α)_*L`. -/
theorem isDerivedCompleteAtSection_of_derivedPushforward_iso
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf A.O)))
    (ε : (derivedPushforward.{u} (denseRestrictHom A Z v α).toRingedToposSiteHom).obj L ≅ K)
    (W : Z.C) (s : (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj.obj (op W))
    (h : ∀ (U : A.C) (a : v.obj U ⟶ W)
        (t : (Stacks.SheafOfModules.Tensor.ringSheaf A.O).obj.obj (op U)),
      fSharpSection (denseRestrictHom A Z v α) U t =
          (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj.map a.op s →
        IsDerivedCompleteAtSection A K U t) :
    IsDerivedCompleteAtSection Z L W s :=
  isDerivedCompleteAtSection_of_denseRestrict A Z v α W L s
    fun U a t ht => isDerivedCompleteAtSection_of_iso A ε.symm U t (h U a t ht)

end AlgebraicGeometry.RingedSite

end
