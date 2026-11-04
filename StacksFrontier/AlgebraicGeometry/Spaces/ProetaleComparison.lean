module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksCore.Tactic.StacksAttribute

/-!
# The small étale and small pro-étale sites of a scheme, and the functors between them

The small étale site of a scheme sits inside its small pro-étale site: an étale morphism is
weakly étale, so an étale `X`-scheme is a pro-étale object of `X`.  The small pro-étale site
also moves along a morphism of schemes, by base change.  This file constructs those two
functors, shows that both are continuous, and provides the sheafification and
homological-algebra instances in which the comparison of étale and pro-étale sheaf categories
is phrased.

Both sites are Mathlib's: `AlgebraicGeometry.Scheme.Etale` with
`AlgebraicGeometry.Scheme.smallEtaleTopology`, and `AlgebraicGeometry.Scheme.ProEt` with
`AlgebraicGeometry.Scheme.ProEt.topology`.

## Main definitions

* `AlgebraicGeometry.Scheme.etaleToProetale` is the inclusion of the small étale category of a
  scheme into its small pro-étale category.
* `AlgebraicGeometry.Scheme.proetaleBaseChange` is base change along a morphism of schemes on
  small pro-étale categories.
* `AlgebraicGeometry.Scheme.etaleInverseImage` and
  `AlgebraicGeometry.Scheme.etaleDirectImage` are inverse and direct image of sheaves of
  modules along the inclusion of sites.
* `AlgebraicGeometry.Scheme.etaleModuleImage` is the essential image of inverse image, the
  class of pro-étale module sheaves coming from the étale site.

## Main results

* `AlgebraicGeometry.Scheme.etaleToProetale_isContinuous` and
  `AlgebraicGeometry.Scheme.proetaleBaseChange_isContinuous`: both functors are continuous
  functors of sites, so restriction along each of them carries sheaves to sheaves and each has
  an inverse image left adjoint to that restriction.
* `AlgebraicGeometry.Scheme.smallEtaleTopology_eq_restrictedTopology` and
  `AlgebraicGeometry.Scheme.ProEt.topology_eq_restrictedTopology`: both small topologies are
  the topology restricted along the forgetful functor to `S`-schemes from the corresponding
  big topology localized at the base.
* `AlgebraicGeometry.hasSheafify_moduleCat`: module-valued presheaves on any site have a
  sheafification once the module universe dominates the universes of the site and of the
  coefficient ring.
* `AlgebraicGeometry.Scheme.comparisonSheafification_exists`: that result for the two small
  sites at once.
* `AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives` and
  `AlgebraicGeometry.Scheme.proetaleSheaves_enoughInjectives`: both sheaf categories have
  enough injectives, so the two derived categories and the derived functors between them
  exist.

## Implementation notes

Both continuous functors are instances of one argument, isolated as
`CategoryTheory.isContinuous_of_restrictedTopology`: a functor `u : C ⥤ D` between sites
carrying topologies restricted along `gC : C ⥤ E` and `gD : D ⥤ F` is continuous as soon as it
is representably flat and `u ⋙ gD = gC ⋙ v` for a cover-preserving `v : E ⥤ F`.  In both
applications `gC` and `gD` are the forgetful functors of the small sites, the identity
`u ⋙ gD = gC ⋙ v` holds by `rfl`, and `v` is the identity of `Over X` (for the inclusion,
where the content is that the big étale topology is coarser than the big pro-étale one) or
`CategoryTheory.Over.pullback` (for pro-étale base change, where cover preservation is
Mathlib's `CategoryTheory.GrothendieckTopology.coverPreserving_overPullback`).  So no cover of
a small site is ever manipulated directly.

The coefficient ring of the module categories has a universe `r` of its own, independent of
the universe `u` of the scheme, and the module sections live in `max (u + 1) w r` for an
arbitrary `w`: the small étale and small pro-étale categories have their objects in
`Type (u + 1)` and their morphisms in `Type u`, so `max (u + 1) w r` is the general module
universe in which both sites are essentially small.  That is exactly the hypothesis under
which `AlgebraicGeometry.hasSheafify_moduleCat` and the Grothendieck-category argument for
enough injectives apply.

## References

* [Stacks Project, Tag 099S](https://stacks.math.columbia.edu/tag/099S)
* [Stacks Project, Tag 09B1](https://stacks.math.columbia.edu/tag/09B1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MorphismProperty

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ u w r

namespace CategoryTheory

/-! ### Continuity of a functor between restricted topologies -/

/-- A functor `u : C ⥤ D` between sites whose topologies are restricted along `gC : C ⥤ E`
and `gD : D ⥤ F` is continuous as soon as it is representably flat and factors as
`u ⋙ gD = gC ⋙ v` through a cover-preserving functor `v : E ⥤ F`. -/
public theorem isContinuous_of_restrictedTopology
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] {F : Type u₄} [Category.{v₄} F]
    {u : C ⥤ D} {gC : C ⥤ E} {gD : D ⥤ F} {v : E ⥤ F}
    {J : GrothendieckTopology E} {K : GrothendieckTopology F}
    [gC.LocallyCoverDense J] [gC.IsLocallyFull J] [gC.IsLocallyFaithful J]
    [gD.LocallyCoverDense K] [gD.IsLocallyFull K] [gD.IsLocallyFaithful K]
    [RepresentablyFlat u]
    (hcomp : u ⋙ gD = gC ⋙ v) (hv : CoverPreserving J K v) :
    u.IsContinuous (gC.restrictedTopology J) (gD.restrictedTopology K) := by
  rw [Functor.isContinuous_iff_coverPreserving]
  have h : CoverPreserving (gC.restrictedTopology J) K (u ⋙ gD) := by
    rw [hcomp]
    exact CoverPreserving.comp _ _ (gC.coverPreserving_restrictedTopology J) hv
  refine ⟨fun {W R} hR => ?_⟩
  rw [Functor.mem_restrictedTopology_iff, ← Sieve.functorPushforward_comp]
  exact h.cover_preserve hR

/-- The identity functor is cover preserving from a coarser to a finer topology. -/
public theorem coverPreserving_id_of_le {C : Type u₁} [Category.{v₁} C]
    {J K : GrothendieckTopology C} (h : J ≤ K) : CoverPreserving J K (𝟭 C) :=
  ⟨fun hS => by simpa using h _ hS⟩

/-- Localizing a topology at an object is monotone. -/
public theorem GrothendieckTopology.over_mono {C : Type u₁} [Category.{v₁} C]
    {J K : GrothendieckTopology C} (h : J ≤ K) (X : C) : J.over X ≤ K.over X :=
  fun _ _ hS => h _ hS

end CategoryTheory

namespace AlgebraicGeometry

/-! ### The two small topologies as restricted topologies -/

/-- The small étale topology is the topology restricted along the forgetful functor to
`X`-schemes from the big étale topology localized at `X`. -/
public theorem Scheme.smallEtaleTopology_eq_restrictedTopology (X : Scheme.{u}) :
    X.smallEtaleTopology =
      (Scheme.Etale.forget X).restrictedTopology (Scheme.etaleTopology.over X) := rfl

/-- The forgetful functor from the small étale category to `X`-schemes is locally cover dense
for the big étale topology localized at `X`. -/
public instance Scheme.Etale.forget_locallyCoverDense (X : Scheme.{u}) :
    (Scheme.Etale.forget X).LocallyCoverDense (Scheme.etaleTopology.over X) := by
  have : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.IsStableUnderComposition (@Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  exact Scheme.locallyCoverDense_of_le X (le_refl (@Etale : MorphismProperty Scheme.{u}))

/-- The small pro-étale topology is the topology restricted along the forgetful functor to
`S`-schemes from the big pro-étale topology localized at `S`. -/
public theorem Scheme.ProEt.topology_eq_restrictedTopology (S : Scheme.{u}) :
    Scheme.ProEt.topology S =
      (Scheme.ProEt.forget S).restrictedTopology (Scheme.proetaleTopology.over S) := by
  have : MorphismProperty.IsStableUnderComposition
      (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  exact MorphismProperty.toGrothendieck_comap_forget_eq_restrictedTopology
    Scheme.proetalePrecoverage Scheme.proetalePrecoverage_le_precoverage_weaklyEtale

/-! ### The inclusion of the small étale site into the small pro-étale site -/

/-- The inclusion of the étale objects among the weakly étale objects over a scheme, that is,
of the small étale category into the small pro-étale category. -/
public abbrev Scheme.etaleToProetale (S : Scheme.{u}) : S.Etale ⥤ S.ProEt :=
  MorphismProperty.Over.changeProp S
    (etale_le_weaklyEtale : (@Etale : MorphismProperty Scheme.{u}) ≤ @WeaklyEtale)
    (le_refl ⊤)

/-- Including the small étale category into the small pro-étale category and then forgetting
to `S`-schemes is forgetting from the small étale category. -/
public theorem Scheme.etaleToProetale_comp_forget (S : Scheme.{u}) :
    S.etaleToProetale ⋙ Scheme.ProEt.forget S = Scheme.Etale.forget S := rfl

/-- The inclusion of the small étale category into the small pro-étale category preserves
finite limits: it does so after composing with the fully faithful forgetful functor to
`S`-schemes, which therefore reflects them. -/
public instance Scheme.preservesFiniteLimits_etaleToProetale (S : Scheme.{u}) :
    PreservesFiniteLimits S.etaleToProetale := by
  have : PreservesFiniteLimits (S.etaleToProetale ⋙ Scheme.ProEt.forget S) :=
    inferInstanceAs (PreservesFiniteLimits (Scheme.Etale.forget S))
  exact ⟨fun _ _ _ => preservesLimitsOfShape_of_reflects_of_preserves
    S.etaleToProetale (Scheme.ProEt.forget S)⟩

/-- The inclusion of étale objects into pro-étale objects preserves sheaves under
restriction. -/
public theorem Scheme.etaleToProetale_isContinuous (X : Scheme.{u}) :
    X.etaleToProetale.IsContinuous X.smallEtaleTopology (Scheme.ProEt.topology X) := by
  have : RepresentablyFlat X.etaleToProetale := flat_of_preservesFiniteLimits _
  rw [Scheme.ProEt.topology_eq_restrictedTopology,
    Scheme.smallEtaleTopology_eq_restrictedTopology]
  exact isContinuous_of_restrictedTopology (v := 𝟭 _) rfl
    (coverPreserving_id_of_le
      (GrothendieckTopology.over_mono Scheme.etaleTopology_le_proetaleTopology X))

attribute [instance] Scheme.etaleToProetale_isContinuous

/-! ### Base change on the small pro-étale site -/

/-- Base change along a morphism of schemes, as a functor between the corresponding small
pro-étale categories. -/
public def Scheme.proetaleBaseChange {Z X : Scheme.{u}} (i : Z ⟶ X) :
    X.ProEt ⥤ Z.ProEt := by
  letI : MorphismProperty.HasPullbacksAlong
      (@WeaklyEtale : MorphismProperty Scheme.{u}) i := ⟨fun _ _ ↦ inferInstance⟩
  letI : MorphismProperty.IsStableUnderBaseChangeAlong
      (@WeaklyEtale : MorphismProperty Scheme.{u}) i :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  exact MorphismProperty.Over.pullback
    (@WeaklyEtale : MorphismProperty Scheme.{u}) ⊤ i

/-- Small pro-étale base change preserves finite limits. -/
public instance Scheme.preservesFiniteLimits_proetaleBaseChange {Z X : Scheme.{u}}
    (i : Z ⟶ X) : PreservesFiniteLimits (Scheme.proetaleBaseChange i) := by
  have : PreservesFiniteLimits (Scheme.proetaleBaseChange i ⋙ Scheme.ProEt.forget Z) :=
    inferInstanceAs (PreservesFiniteLimits (Scheme.ProEt.forget X ⋙ Over.pullback i))
  exact ⟨fun _ _ _ => preservesLimitsOfShape_of_reflects_of_preserves
    (Scheme.proetaleBaseChange i) (Scheme.ProEt.forget Z)⟩

/-- Base change is continuous for the small pro-étale sites. -/
public instance Scheme.proetaleBaseChange_isContinuous {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (Scheme.proetaleBaseChange i).IsContinuous
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z) := by
  have : RepresentablyFlat (Scheme.proetaleBaseChange i) :=
    flat_of_preservesFiniteLimits _
  rw [Scheme.ProEt.topology_eq_restrictedTopology X,
    Scheme.ProEt.topology_eq_restrictedTopology Z]
  exact isContinuous_of_restrictedTopology (v := Over.pullback i) rfl
    (GrothendieckTopology.coverPreserving_overPullback Scheme.proetaleTopology i)

/-! ### Sheafification of module-valued presheaves -/

/-- Sheafification of presheaves of modules exists on any site, with the coefficient ring and
the module sections in universes independent of the site. -/
public instance hasSheafify_moduleCat {C : Type u₁} [Category.{v₁} C]
    (J : GrothendieckTopology C) (R : Type r) [Ring R] :
    HasSheafify J (ModuleCat.{max u₁ v₁ w r} R) := by
  let : PreservesColimitsOfSize.{max u₁ v₁ w r, max u₁ v₁ w r}
      (forget₂ (ModuleCat.{max u₁ v₁ w r} R) AddCommGrpCat.{max u₁ v₁ w r}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max u₁ v₁ w r, r, max u₁ v₁ w r,
      max u₁ v₁ w r} R
  let : PreservesFilteredColimits (forget (ModuleCat.{max u₁ v₁ w r} R)) :=
    comp_preservesFilteredColimits.{max u₁ v₁ w r, max u₁ v₁ w r}
      (forget₂ (ModuleCat.{max u₁ v₁ w r} R) AddCommGrpCat.{max u₁ v₁ w r})
      (forget AddCommGrpCat.{max u₁ v₁ w r})
  let : PreservesFilteredColimitsOfSize.{max u₁ v₁, max u₁ v₁}
      (forget (ModuleCat.{max u₁ v₁ w r} R)) :=
    preservesFilteredColimitsOfSize_shrink.{max u₁ v₁, max u₁ v₁ w r, max u₁ v₁,
      max u₁ v₁ w r} _
  infer_instance

/-- Sheafification exists for module-valued presheaves on the two small sites. -/
public theorem Scheme.comparisonSheafification_exists (X : Scheme.{u})
    (Λ : Type r) [Ring Λ] :
    HasSheafify X.smallEtaleTopology (ModuleCat.{max (u + 1) w r} Λ) ∧
      HasSheafify (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w r} Λ) :=
  ⟨hasSheafify_moduleCat.{u + 1, u, w, r} _ _, hasSheafify_moduleCat.{u + 1, u, w, r} _ _⟩

/-! ### Inverse and direct image of sheaves of modules -/

variable (X : Scheme.{u}) (Λ : Type r) [Ring Λ]
  [HasSheafify X.smallEtaleTopology (ModuleCat.{max (u + 1) w r} Λ)]
  [HasSheafify (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w r} Λ)]

/-- Inverse image of sheaves of `Λ`-modules along the étale-to-pro-étale site morphism. -/
public abbrev Scheme.etaleInverseImage :=
  Functor.sheafPullbackConstruction.sheafPullback
    X.etaleToProetale (ModuleCat.{max (u + 1) w r} Λ)
    X.smallEtaleTopology (Scheme.ProEt.topology X)

/-- The class of pro-étale module sheaves obtained from étale module sheaves. -/
public abbrev Scheme.etaleModuleImage :
    ObjectProperty (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w r} Λ)) :=
  (Scheme.etaleInverseImage.{u, w, r} X Λ).essImage

/-- Direct image of module sheaves along the étale-to-pro-étale site morphism. -/
public abbrev Scheme.etaleDirectImage :=
  X.etaleToProetale.sheafPushforwardContinuous
    (ModuleCat.{max (u + 1) w r} Λ)
    X.smallEtaleTopology (Scheme.ProEt.topology X)

/-! ### Enough injectives and additivity -/

/-- The module category remains Grothendieck when its carrier universe is larger than the
coefficient-ring universe. -/
private theorem moduleCat_isGrothendieckAbelian (Λ : Type r) [Ring Λ] :
    IsGrothendieckAbelian.{max w r} (ModuleCat.{max w r} Λ) := by
  let : AB5 (ModuleCat.{max w r} Λ) :=
    { ofShape J _ _ :=
        HasExactColimitsOfShape.domain_of_functor J
          (forget₂ (ModuleCat.{max w r} Λ) AddCommGrpCat) }
  exact {}

/-- Module sheaves on the small étale site have enough injectives. -/
public instance Scheme.etaleSheaves_enoughInjectives (X : Scheme.{u})
    (Λ : Type r) [Ring Λ]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{max (u + 1) w r} Λ)] :
    EnoughInjectives
      (Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) w r} Λ)) := by
  let : IsGrothendieckAbelian.{max (u + 1) w r}
      (ModuleCat.{max (u + 1) w r} Λ) :=
    moduleCat_isGrothendieckAbelian.{max (u + 1) w, r} Λ
  let : EssentiallySmall.{max (u + 1) w r} X.Etale := inferInstance
  let e := equivSmallModel.{max (u + 1) w r} X.Etale
  let : HasSheafify (e.inverse.inducedTopology X.smallEtaleTopology)
      (ModuleCat.{max (u + 1) w r} Λ) := by
    let : e.symm.inverse.IsDenseSubsite X.smallEtaleTopology
        (e.inverse.inducedTopology X.smallEtaleTopology) :=
      inferInstanceAs (e.functor.IsDenseSubsite X.smallEtaleTopology
        (e.inverse.inducedTopology X.smallEtaleTopology))
    exact e.symm.hasSheafify _ X.smallEtaleTopology _
  let : IsGrothendieckAbelian.{max (u + 1) w r}
      (Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) w r} Λ)) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _
  exact IsGrothendieckAbelian.enoughInjectives

/-- Module sheaves on the small pro-étale site have enough injectives. -/
public instance Scheme.proetaleSheaves_enoughInjectives (X : Scheme.{u})
    (Λ : Type r) [Ring Λ]
    [HasSheafify (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w r} Λ)] :
    EnoughInjectives
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w r} Λ)) := by
  let : IsGrothendieckAbelian.{max (u + 1) w r}
      (ModuleCat.{max (u + 1) w r} Λ) :=
    moduleCat_isGrothendieckAbelian.{max (u + 1) w, r} Λ
  let : EssentiallySmall.{max (u + 1) w r} X.ProEt := inferInstance
  let e := equivSmallModel.{max (u + 1) w r} X.ProEt
  let : HasSheafify (e.inverse.inducedTopology (Scheme.ProEt.topology X))
      (ModuleCat.{max (u + 1) w r} Λ) := by
    let : e.symm.inverse.IsDenseSubsite (Scheme.ProEt.topology X)
        (e.inverse.inducedTopology (Scheme.ProEt.topology X)) :=
      inferInstanceAs (e.functor.IsDenseSubsite (Scheme.ProEt.topology X)
        (e.inverse.inducedTopology (Scheme.ProEt.topology X)))
    exact e.symm.hasSheafify _ (Scheme.ProEt.topology X) _
  let : IsGrothendieckAbelian.{max (u + 1) w r}
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w r} Λ)) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _
  exact IsGrothendieckAbelian.enoughInjectives

/-- Restriction of module sheaves along the étale inclusion is additive. -/
public instance Scheme.etaleDirectImage_additive :
    (Scheme.etaleDirectImage.{u, w, r} X Λ).Additive where
  map_add := rfl

/-- Inverse image of module sheaves along the étale inclusion is additive. -/
public instance Scheme.etaleInverseImage_additive :
    (Scheme.etaleInverseImage.{u, w, r} X Λ).Additive := by
  let := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    X.etaleToProetale (ModuleCat.{max (u + 1) w r} Λ)
    X.smallEtaleTopology (Scheme.ProEt.topology X)).isLeftAdjoint
  let : PreservesBinaryBiproducts (Scheme.etaleInverseImage.{u, w, r} X Λ) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

end AlgebraicGeometry

end
