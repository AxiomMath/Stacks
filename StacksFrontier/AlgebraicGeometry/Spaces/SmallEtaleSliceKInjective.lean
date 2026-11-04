module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EvaluationConservative
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPseudoCoherentTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionKInjectiveEssentiallySmall
import StacksCore.Tactic.StacksAttribute

/-!
# Restriction to a slice of the small étale site of an algebraic space, and K-injectives

Let `F` be an algebraic space over a scheme `S` and let `U` be an object of its small étale
site.  Restriction of `𝒪_F`-modules to the slice over `U` is `SheafOfModules.overFunctor`, and
its left adjoint is extension by zero, which is exact (Stacks 03DJ).  So by the adjoint
criterion for K-injectivity (Stacks 08BJ) the restriction carries K-injective complexes to
K-injective complexes — Stacks 08FI — and therefore, by Stacks 0D6G, the degreewise image under
it of a K-injective complex computes the right derived functor of *any* additive functor out of
the modules on the slice.

That last statement is
`Stacks.Cohomology.LerayUnbounded.ComputesSecond (overFunctor 𝒪_F U) G`, the hypothesis of
`Stacks.Cohomology.LerayUnbounded.derivedCompIsoOfComputes`, and it is what makes derived
sections cross the slice: taken at `G = Γ(Over.mk (𝟙 U), -)`, the evaluation at the final object
of the slice, it gives `RΓ(⊤, -) ∘ R(overFunctor) ≅ RΓ(U, -)`, the underived form of which is
the equality `AlgebraicGeometry.RingedSite.overEvaluationIso`.

## What is new here, and why the collapsed statements do not apply

Stacks 08FI is proved twice in the library.  `Stacks.Cohomology.Localization.isKInjective_over` is
stated for `{C : Type u}` with `[Category.{u} C]`, which the small étale site of an algebraic
space — an `AlgebraicGeometry.RingedSite.{u + 1, u, u}` — does not satisfy, its objects lying
one universe above its morphisms.
`Stacks.Cohomology.Localization.isKInjective_over_of_essentiallySmall` removes exactly that
restriction under essential smallness, which the small étale site has; what it still asks for is
the sheafification data and the essential smallness *at the reduced spellings* of the site,
whereas a goal about `smallEtaleRingedSite` presents them through the projections `.C` and `.J`
of a structure instance, which instance search does not invert.  This file supplies those as
local instances and reads off the two conclusions.

The one input that genuinely was not available anywhere is Grothendieck abelianness of the
modules on the *slice* at the module universe: `ComputesSecond` carries it as an instance binder
on both of its categories, and the implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDerivedSectionsOverObject.lean`
record it as unavailable at independent site universes.  It is available here, and by the same
route as for the site itself: a slice of an essentially `u`-small category is essentially
`u`-small (`Stacks.essentiallySmall_over`), the slice topology has sheafification and local
bijectivity of its weak equivalences by
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify_over` and
`AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective_over`, and
`SheafOfModules.isGrothendieckAbelian_of_essentiallySmall` concludes.  Nothing is carried as a
new binder on a shared declaration.

## Main results

* `AlgebraicGeometry.Space.isKInjective_overFunctor`: **Stacks 08FI at the small étale ringed
  site of an algebraic space** — restriction to the slice over an object carries a K-injective
  complex of `𝒪_F`-modules to a K-injective complex.
* `AlgebraicGeometry.Space.computesSecond_overFunctor`: consequently that restriction satisfies
  `Stacks.Cohomology.LerayUnbounded.ComputesSecond` against every additive functor out of the
  modules on the slice.
* `AlgebraicGeometry.Space.computesSecond_overFunctor_evaluation`: the same at the evaluation
  of a sheaf of modules on the slice at the slice's final object `Over.mk (𝟙 U)`, and at
  `CategoryTheory.HasDerivedCategory.standard`, which is the pin the pseudo-coherence
  development of an algebraic space uses.

The localized sheaf of rings is written `𝒪_F.over U` and not `(𝒪_F|_U)` — that is,
`(smallEtaleRingedSite B S hS F hF).ringSheaf.over U` and not
`((smallEtaleRingedSite B S hS F hF).over U).ringSheaf` — throughout the statements about
restriction.  The two are definitionally equal, restriction along `Over.forget U` commuting with
the forgetful functor from commutative rings to rings, but the first is the spelling of the
codomain of `SheafOfModules.overFunctor` and of `AlgebraicGeometry.RingedSite.overEvaluationIso`,
and instance search does not invert the projections of a ringed site, so a statement at the
second spelling leaves the instances of `ComputesSecond` unsynthesizable.

## Implementation notes

The two Grothendieck-abelianness facts about the modules on a slice are global instances; the
essential smallness, sheafification and local-bijectivity facts are `local instance`s and not
instances.  For the sheafification data that is the usual reason — they exist already at the
reduced spelling, and only the projection spelling is new.  For `EssentiallySmall` at
`(smallEtaleRingedSite B S hS F hF).C` it is a recorded hazard:
`AlgebraicGeometry.Space.isGrothendieckAbelian_modules` says that such an instance breaks existing
lemmas which unify against the reduced spelling.

None of the three results is an `instance`.  `Stacks.Cohomology.LerayUnbounded.ComputesSecond`
is an `abbrev` for a universally quantified proposition and not a class, so it cannot be one;
and `isKInjective_overFunctor` follows the choice made for
`Stacks.Cohomology.Localization.isKInjective_over_of_essentiallySmall`, whose hypotheses would
otherwise be tried at every site in the development.

No `@[stacks]` attribute.  Stacks 08FI is carried by
`Stacks.Cohomology.Localization.isKInjective_over`, which states it in the generality the tag
has; these are its instance at one site, with the hypotheses discharged.

## References

* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
* [Stacks Project, Tag 0D6G](https://stacks.math.columbia.edu/tag/0D6G)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

-- `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is removed as an instance for this file,
-- for the reason recorded in the implementation notes of
-- `StacksFrontier/AlgebraicGeometry/Spaces/ChartPseudoCoherentTransport.lean`: it answers
-- `Abelian (SheafOfModules …)` with the module universe left as the join of the universes of the
-- site, the rings and a free one, and a search reaching it first ends in a universe constraint
-- with no solution rather than in a recoverable failure.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

-- `Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck` is removed for the same reason, one
-- class up: it answers `IsGrothendieckAbelian (SheafOfModules …)` with the module universe fixed
-- to the join `max u v r w` of the universes of the site, the rings and a free one.  The size
-- parameter of the `IsGrothendieckAbelian` binders of
-- `Stacks.Cohomology.LerayUnbounded.ComputesSecond` is a metavariable at the statement below, so
-- a search reaching this instance first ends in `u + 1 =?= max (u + 1) ?w`, a universe
-- constraint with no solution, rather than in a recoverable failure.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

universe w v₁ u₁ u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### The site data at the projection spellings -/

-- The sheafification data of the slices of a ringed site, at the `(X.over U).J` spelling of the
-- localized topology; these are the `local instance`s of
-- `StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/LocalNature.lean`, re-enabled here
-- exactly as `StacksFrontier/AlgebraicGeometry/Spaces/ChartPseudoCoherentTransport.lean` re-enables
-- them.  They are what the abelian structure of the modules on a slice is synthesized from.
attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

-- The small étale site of an algebraic space is essentially small at the universe of the
-- schemes, at the `AlgebraicGeometry.RingedSite.C` spelling of its underlying category:
-- `AlgebraicGeometry.Space.smallEtaleRingedSite_essentiallySmall`.  It is deliberately not a
-- global instance: see the implementation notes.
attribute [local instance] smallEtaleRingedSite_essentiallySmall

/-- Sheafification of presheaves of abelian groups exists on the small étale site of an
algebraic space, at the `AlgebraicGeometry.RingedSite.J` spelling of its topology. -/
local instance hasSheafifyAddCommGrp_smallEtaleRingedSite :
    HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{u} := by
  change HasSheafify (SmallEtale.topology B S hS F) AddCommGrpCat.{u}
  infer_instance

/-- On the small étale site of an algebraic space the local equivalences of presheaves of
abelian groups are exactly the locally bijective morphisms, at the
`AlgebraicGeometry.RingedSite.J` spelling of the topology. -/
local instance wEqualsLocallyBijectiveAddCommGrp_smallEtaleRingedSite :
    (smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{u} := by
  change (SmallEtale.topology B S hS F).WEqualsLocallyBijective AddCommGrpCat.{u}
  infer_instance

/-- **The `𝒪_F`-modules on the small étale ringed site of an algebraic space form a Grothendieck
abelian category at the universe of the structure rings.**

This is `AlgebraicGeometry.Space.isGrothendieckAbelian_modules`, which is a theorem rather than
an instance for the reason recorded there; it is the instance that
`Stacks.Cohomology.LerayUnbounded.ComputesSecond` carries on its source category. -/
local instance isGrothendieckAbelian_smallEtaleRingedSite :
    IsGrothendieckAbelian.{u}
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) :=
  isGrothendieckAbelian_modules B S hS F hF

variable (U : (smallEtaleRingedSite B S hS F hF).C)

/-- A slice of the small étale site of an algebraic space is essentially small at the universe
of the schemes: it is `Stacks.essentiallySmall_over` at the site, which is essentially small
itself. -/
local instance essentiallySmall_smallEtaleRingedSite_over :
    EssentiallySmall.{u} ((smallEtaleRingedSite B S hS F hF).over U).C :=
  Stacks.essentiallySmall_over.{u} (C := SmallEtale B S hS F) U

/-- **The `𝒪_F|_U`-modules on a slice of the small étale ringed site of an algebraic space form
a Grothendieck abelian category at the universe of the structure rings.**

This is `SheafOfModules.isGrothendieckAbelian_of_essentiallySmall` at the slice: the slice is
essentially `u`-small, and its topology has sheafification and local bijectivity of its weak
equivalences by `AlgebraicGeometry.Space.smallEtaleRingedSite_hasSheafify_over` and
`AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective_over`.  It is the instance
that `Stacks.Cohomology.LerayUnbounded.ComputesSecond` carries on its middle category, and the
one the implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDerivedSectionsOverObject.lean`
record as unavailable at independent site universes in general. -/
public instance isGrothendieckAbelian_smallEtaleRingedSite_over :
    IsGrothendieckAbelian.{u}
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS F hF).over U).O)) :=
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _

/-- The previous instance at the other spelling of the localized sheaf of rings.

The codomain of `SheafOfModules.overFunctor R U` is the modules over `R.over U`, so a goal about
restriction to the slice presents the localized sheaf of rings as
`(smallEtaleRingedSite B S hS F hF).ringSheaf.over U` and not as
`((smallEtaleRingedSite B S hS F hF).over U).ringSheaf`.  The two are definitionally equal —
restricting along `Over.forget U` commutes with forgetting from commutative rings to rings — but
instance search does not invert the projections of a ringed site, so both spellings are
needed.

Like its companion this is a global instance: it can fire only at a goal mentioning
`AlgebraicGeometry.Space.smallEtaleRingedSite`, `CategoryTheory.IsGrothendieckAbelian` is a
`Prop` so it cannot diamond, and it takes no instance argument of its own class so it cannot
loop — the same reasons recorded for
`AlgebraicGeometry.smallEtaleRingedSite_isGrothendieckAbelian`. -/
public instance isGrothendieckAbelian_ringSheaf_over :
    IsGrothendieckAbelian.{u}
      (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over U)) :=
  isGrothendieckAbelian_smallEtaleRingedSite_over B S hS F hF U

/-! ### Stacks 08FI at the small étale site of an algebraic space -/

/-- **Stacks 08FI at the small étale ringed site of an algebraic space.**  Restriction of
`𝒪_F`-modules to the slice over an object `U` carries a K-injective complex to a K-injective
complex.

The left adjoint of the restriction is extension by zero, which is exact (Stacks 03DJ), so this
is the adjoint criterion for K-injectivity, Stacks 08BJ.  Concretely it is
`Stacks.Cohomology.Localization.isKInjective_over_of_essentiallySmall` — the form of Stacks 08FI
whose site may have its objects above its morphisms — with its hypotheses discharged at the
projection spellings of the ringed site. -/
theorem isKInjective_overFunctor
    (I : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) ℤ)
    (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      (((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) U
        ).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  have := hI
  Stacks.Cohomology.Localization.isKInjective_over_of_essentiallySmall
    (smallEtaleRingedSite B S hS F hF).J
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) U I

/-! ### The `ComputesSecond` hypothesis across the slice -/

section Computes

variable [HasDerivedCategory.{w}
    (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))]
  [HasDerivedCategory.{w}
    (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over U))]

omit [HasDerivedCategory.{w}
    (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))] in
/-- **Restriction to a slice computes the second functor of any composite.**  For every additive
functor `G` out of the `𝒪_F|_U`-modules on the slice, the comparison `G J ⟶ RG J` is invertible
at `J` the degreewise restriction of any K-injective complex of `𝒪_F`-modules.

This is `Stacks.Cohomology.LerayUnbounded.ComputesSecond` for `SheafOfModules.overFunctor` and
`G`, discharged from `AlgebraicGeometry.Space.isKInjective_overFunctor`: the comparison of a
right derived functor is invertible on a K-injective complex, and the restriction of a
K-injective complex is one.  It is the hypothesis under which
`Stacks.Cohomology.LerayUnbounded.derivedCompIsoOfComputes` gives
`RG ∘ R(overFunctor) ≅ R(G ∘ overFunctor)`. -/
theorem computesSecond_overFunctor {D : Type u₁} [Category.{v₁} D] [Abelian D]
    [HasDerivedCategory.{w} D]
    (G : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over U) ⥤ D)
    [G.Additive] :
    Stacks.Cohomology.LerayUnbounded.ComputesSecond
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) U) G :=
  Stacks.Cohomology.LerayUnbounded.computesSecond_of_isKInjective _ _
    (isKInjective_overFunctor B S hS F hF U)

end Computes

section Standard

/-- The standard derived category of the `𝒪_F`-modules on the small étale ringed site of an
algebraic space, named explicitly because instance synthesis cannot produce
`CategoryTheory.HasDerivedCategory.standard` at a goal whose universe is already fixed: it would
have to solve `max ?u_obj ?u_hom =?= u + 1` with both sides metavariables. -/
local instance hasDerivedCategory_modules :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) :=
  HasDerivedCategory.standard _

/-- The standard derived category of the `𝒪_F|_U`-modules on a slice, named explicitly for the
reason recorded at `hasDerivedCategory_modules`. -/
local instance hasDerivedCategory_modules_over :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over U)) :=
  HasDerivedCategory.standard _

/-- The standard derived category of the modules of sections of the localized structure sheaf
over the final object of the slice, named explicitly for the reason recorded at
`hasDerivedCategory_modules`. -/
local instance hasDerivedCategory_sections :
    HasDerivedCategory.{u + 1}
      (ModuleCat.{u}
        (((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O).over U).obj.obj (op (Over.mk (𝟙 U))))) :=
  HasDerivedCategory.standard _

/-- **Restriction to the slice over `U` computes `RΓ(⊤, -)` on the slice.**  The comparison of
the right derived functor of evaluation at the final object `Over.mk (𝟙 U)` of the slice is
invertible at the degreewise restriction of every K-injective complex of `𝒪_F`-modules.

This is `AlgebraicGeometry.Space.computesSecond_overFunctor` at
`G = SheafOfModules.evaluation (𝒪_F|_U) (op (Over.mk (𝟙 U)))`, whose additivity is
`Stacks.SheafOfModulesEvaluation.evaluation_additive`, and at
`CategoryTheory.HasDerivedCategory.standard`, which is the derived-category pin that the
relative pseudo-coherence development of an algebraic space uses.  Composed with the equality of
underived functors `AlgebraicGeometry.RingedSite.overEvaluationIso` it is what carries derived
sections over `U` across the slice. -/
theorem computesSecond_overFunctor_evaluation :
    Stacks.Cohomology.LerayUnbounded.ComputesSecond
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) U)
      (SheafOfModules.evaluation.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over U)
        (op (Over.mk (𝟙 U)))) :=
  computesSecond_overFunctor B S hS F hF U _

end Standard

end AlgebraicGeometry.Space

end
