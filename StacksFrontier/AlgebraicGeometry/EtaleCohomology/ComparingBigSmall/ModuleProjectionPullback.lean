module

public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageFullyFaithful
public import StacksFrontier.Algebra.Homology.HomotopyCategory.AdjunctionComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ModuleCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.ExactAbelianLowerShriek

/-!
# `π_S^*` and `Lπ_S^*` on sheaves of `𝒪`-modules, and Stacks 0DDH part (2)

Let `B` be a big étale site and let `S` be an object of it.  This file builds the pullback
`π_S^*` of sheaves of `𝒪`-modules along the projection `π_S` from the big étale topos over `S`
to the small étale topos of `S`, its left derived functor `Lπ_S^*`, and the clause of
Stacks 0DDH computing big-site cohomology of a derived module pullback.

## Main definitions

* `AlgebraicGeometry.smallEtaleModuleProjectionPullback` — `π_S^*` on sheaves of `𝒪`-modules.
* `AlgebraicGeometry.derivedSmallEtaleModuleProjectionPullback` — `Lπ_S^*`.

## Main results

* `AlgebraicGeometry.smallEtaleModuleProjectionAdjunction` — `π_S^* ⊣ π_{S,*}`.
* `AlgebraicGeometry.smallEtaleModuleProjectionUnitIso` — `π_{S,*}π_S^* ≅ 𝟭`.
* `AlgebraicGeometry.derivedSmallEtaleModuleProjectionUnitIso` — `π_{S,*}Lπ_S^* ≅ 𝟭` on the
  unbounded derived categories.
* `AlgebraicGeometry.bigSmallEtaleModuleProjectionPullbackCohomologyIsoSelf` — Stacks 0DDH,
  part (2), on underlying abelian complexes: `H^n_étale(S, Lπ_S^*K) = H^n(S_étale, K)`.

## The spelling of `π_S`

`π_{S,*}` is restriction along the inclusion of the small étale site of `S` into the big étale
site over `S`.  Everything below is written along
`AlgebraicGeometry.smallEtaleToBigEtaleFunctor B S S (𝟙 S)`, the functor `U/S ↦ U/S` of Stacks
021F at the identity morphism, rather than along `AlgebraicGeometry.SmallEtale.inclusion`
directly.  The two functors are *equal*, by
`AlgebraicGeometry.smallEtaleToBigEtaleFunctor_id_eq`, so this is a spelling and not a change of
statement; the reason for it is that the continuity and cocontinuity of the Stacks 021F functor
are global instances (`AlgebraicGeometry.smallEtaleToBigEtaleFunctor_isContinuous` and
`AlgebraicGeometry.smallEtaleToBigEtaleFunctor_isCocontinuous`) whereas for the inclusion they
are theorems, and that in this spelling `π_{S,*}` on modules *is*
`AlgebraicGeometry.smallEtaleModuleRestriction B S S (𝟙 S)`, the functor `i_f^*` that
Stacks 0DDH part (6) is stated with, so part (6) applies with no transport at all.

## Why `π_S^*` is a genuine left derived functor

`π_S^*` is the module lower shriek of Stacks 0797 along the small étale inclusion, i.e. the
*left* adjoint of restriction, and the inclusion's structure map is the identity
(`AlgebraicGeometry.smallEtalePiStructureSharp_eq_id`).  It is nevertheless neither left exact
(`Stacks.SheafOfModules.lowerShriek_not_preservesFiniteLimits`) nor compatible with forgetting
the module structure (`Stacks.SheafOfModules.lowerShriekForget_not_isomorphic`, whose
counterexample functor is fully faithful, final, continuous and cocontinuous with the identity
structure map — the shape of the small étale inclusion).  So `Lπ_S^*` is a genuine left derived
functor and the underlying abelian complex of `Lπ_S^*K` is *not* `π_S^{-1}` of the underlying
abelian complex of `K`: part (2) does not follow from the abelian part (1).

## `Lπ_S^*` exists and is absolute

The left derived functor `Lπ_S^*` exists on the whole unbounded derived category — the existence
half of Stacks 07AC for the small étale inclusion — and it is *absolute*: followed by any functor
out of the derived category of the big étale site, in particular by the exact `π_{S,*}`, it is
still a left derived functor.  These are the instances
`AlgebraicGeometry.hasPointwiseLeftDerivedFunctor_smallEtaleModuleProjectionPullback` and
`AlgebraicGeometry.isLeftDerivedFunctor_derivedSmallEtaleModuleProjectionPullback_comp`, read off
`Stacks.Cohomology.ExactAbelianLowerShriek.hasPointwiseLeftDerivedFunctor` and
`Stacks.Cohomology.ExactAbelianLowerShriek.isLeftDerivedFunctor_comp`.  The input those need is
that `π_{S,*}` on modules lies over the abelian `π_{S,*}`, whose left adjoint `π_S^{-1}` is exact
(Stacks 0DDI, here `AlgebraicGeometry.smallEtaleAbelianProjectionPullback_preservesFiniteLimits`):
then `Ext^p(𝒪 ⊗ X, π_{S,*}I) = Ext^p(X, π_{S,*}I_ab) = Ext^p(π_S^{-1}X, I_ab) = 0` for an
injective module `I`, `p > 0` and `X` sectionwise torsion-free, which is the acyclicity input
of Stacks 0794.  The derived section functors `RΓ(S, -)` of the big étale site and
`RΓ(S_étale, -)` of the small one exist by the K-injective resolutions of the two Grothendieck
abelian categories of abelian sheaves (`AlgebraicGeometry.hasRightDerivedFunctor_bigEtaleSections`
and `AlgebraicGeometry.hasRightDerivedFunctor_smallEtaleGlobalSections`).  So part (2) is stated
with no hypothesis.

## Where part (4) is

Part (4) of Stacks 0DDH, `H^n_étale(T, Lπ_S^*K) = H^n(T_étale, Lf_{small}^*K)` for a morphism
`f : T ⟶ S`, is not here but in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ComparingBigSmall/DerivedModulePullback.lean`, on
`AlgebraicGeometry.bigSmallEtaleModuleProjectionPullbackCohomologyIso`.  Part (2) is the case
`f = 𝟙` and is proved above directly from part (6) rather than, as the source does it, as a
special case of part (4); what part (4) adds is the identity `Lf_{small}^* = i_f^* ∘ Lπ_S^*`
(`AlgebraicGeometry.derivedSmallEtaleModulePullbackIso`), and with it the functor `f_{small}^*`
on sheaves of `𝒪`-modules at this file's module universe
(`AlgebraicGeometry.smallEtaleModulePullbackLarge`, built in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ComparingBigSmall/ModulePullback.lean`).

`f_{small}^*` is a genuine change of rings — `f_{small}^♯` is not the identity, unlike `π_S^♯`
and `i_f^♯` — so it is not a module lower shriek and the construction above does not produce it.
The library also has it as `AlgebraicGeometry.smallEtalePullbackModules`, but only at
`SheafOfModules.{u}`: that functor is
`AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesGeneral`, which is
`AlgebraicGeometry.RingedToposSiteHom.pullbackToposGeneral`, and both are stated at a
`AlgebraicGeometry.RingedTopos.{v, u, w}` whose structure sheaf is valued in `CommRingCat.{w}`
and whose sheaves of modules are `SheafOfModules.{w}` — one universe for the structure rings and
the module sections together.  For the small étale site of a scheme the structure rings are in
`Type u`, so that route gives `f_{small}^*` only at `SheafOfModules.{u}`, whereas part (6),
`π_S^*` and `Lπ_S^*` live at `SheafOfModules.{u + 1}`.  The obstruction was the universe
generality of those wrappers and not a missing mathematical input: Mathlib's
`SheafOfModules.pullback` is polymorphic in the module universe independently of the universe of
the structure rings, so `f_{small}^*` at `SheafOfModules.{u + 1}` is constructed from
`f_{small}^♯` directly.

The module-level form of the Stacks 0759 square for schemes that part (4) also needs is
`AlgebraicGeometry.smallEtaleRestrictionPushforwardModules_eq`, with its mate
`AlgebraicGeometry.smallEtaleModulePullbackProjectionIso`; the abelian/arbitrary-coefficient
form is `AlgebraicGeometry.smallEtaleRestrictionPushforwardIso`, and the algebraic-spaces module
form is `AlgebraicGeometry.BigEtaleSpaceSite.bigSmallEtale_restrictPushforwardModulesIso` with
its derived companion `derivedBigSmallEtaleModulePushforwardIso`.  The factorization
`i_f^* ≅ π_{T,*} ∘ f_{big}^*` on modules is
`AlgebraicGeometry.smallEtaleModuleRestrictionFactorIso`, and `f_{big}^*` and `f_{big!}` on
modules of the big étale sites are `AlgebraicGeometry.bigEtaleInverseImageModules` and
`AlgebraicGeometry.bigEtaleLowerShriekModules`.

## Cohomology of a module complex

Part (2) is proved here on underlying complexes of abelian sheaves: both sides are `RΓ` of the
image of the coefficient object under `SheafOfModules.toSheaf`. The statement with `RΓ` taken in
the derived category of modules, as in the source, is
`AlgebraicGeometry.bigSmallEtaleModuleProjectionPullbackSectionsCohomologyIsoSelf` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ComparingBigSmall/ModuleSectionsCohomology.lean`,
deduced from this one by Stacks 0D6J.

## References

* [Stacks Project, Tag 0DDH](https://stacks.math.columbia.edu/tag/0DDH)
* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
* [Stacks Project, Tag 021F](https://stacks.math.columbia.edu/tag/021F)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : B.Scheme)

/-- **The Stacks 021F functor at the identity is the small étale inclusion.**  Sending `U/S` to
`U/S` along the identity of `S` is the inclusion of the small étale site of `S` into the big
étale site over `S`.

This is the standalone form of a step that occurs inside the proof of
`AlgebraicGeometry.smallEtaleInclusion_isCocontinuous`; it is what justifies reading every
functor in this file as being attached to the projection `π_S`. -/
public theorem smallEtaleToBigEtaleFunctor_id_eq :
    smallEtaleToBigEtaleFunctor B S S (𝟙 S) = SmallEtale.inclusion B S.obj S.property := by
  dsimp [smallEtaleToBigEtaleFunctor]
  rw [Over.mapId_eq]
  rfl

/-- The Stacks 021F functor at the identity is full, being the small étale inclusion. -/
public instance smallEtaleToBigEtaleFunctor_id_full :
    (smallEtaleToBigEtaleFunctor B S S (𝟙 S)).Full := by
  rw [smallEtaleToBigEtaleFunctor_id_eq]
  infer_instance

/-- The Stacks 021F functor at the identity is faithful, being the small étale inclusion. -/
public instance smallEtaleToBigEtaleFunctor_id_faithful :
    (smallEtaleToBigEtaleFunctor B S S (𝟙 S)).Faithful := by
  rw [smallEtaleToBigEtaleFunctor_id_eq]
  infer_instance

section Underived

/-- **`π_S^*` on sheaves of `𝒪`-modules**, the module lower shriek of Stacks 0797 along the
inclusion of the small étale site of `S` into the big étale site over `S`: a sheaf of
`𝒪_{S_étale}`-modules is pushed forward as a presheaf of modules and the result is sheafified.

It is the left adjoint of `π_{S,*}`, which on modules is restriction along the inclusion with no
change of rings, because `π_S^♯` is the identity
(`AlgebraicGeometry.smallEtalePiStructureSharp_eq_id`). -/
public abbrev smallEtaleModuleProjectionPullback :
    SheafOfModules.{u + 1} (SmallEtale.structureSheaf B S.obj S.property) ⥤
      SheafOfModules.{u + 1} (BigEtaleOver.structureSheaf B S.obj S.property) :=
  Stacks.SheafOfModules.lowerShriek.{u + 1}
    (SmallEtale.topology B S.obj S.property)
    (BigEtaleOver.topology B S.obj S.property)
    (smallEtaleToBigEtaleFunctor B S S (𝟙 S))
    (BigEtaleOver.structureSheaf B S.obj S.property)

/-- **Stacks 0797 at the small étale inclusion.** `π_S^*` is left adjoint to `π_{S,*}`, which is
`AlgebraicGeometry.smallEtaleModuleRestriction B S S (𝟙 S)`. -/
@[stacks 0797 "the adjunction at the inclusion of the small étale site of a scheme into its big \
étale site, at the module universe of Stacks 0DDH part (6)"]
public def smallEtaleModuleProjectionAdjunction :
    smallEtaleModuleProjectionPullback B S ⊣ smallEtaleModuleRestriction B S S (𝟙 S) :=
  Stacks.SheafOfModules.lowerShriekAdjunction.{u + 1}
    (SmallEtale.topology B S.obj S.property)
    (BigEtaleOver.topology B S.obj S.property)
    (smallEtaleToBigEtaleFunctor B S S (𝟙 S))
    (BigEtaleOver.structureSheaf B S.obj S.property)

/-- The unit of `π_S^* ⊣ π_{S,*}` is an isomorphism: the small étale inclusion is fully faithful,
continuous and cocontinuous, and the structure map of `π_S` is the identity, which is exactly the
situation of `SheafOfModules.isIso_unit_of_isIso_coefficient`.  The module universe of that
lemma is `max uC vD w` for the two universes `uC`, `vD` of the sites, so the universe of the
module sections has to be pinned explicitly for it to come out as `u + 1`: the explicit levels
are, in order, the universe of the structure rings, of the module sections, of the morphisms of
the small and of the big site, and of the objects of the small and of the big site. -/
public instance isIso_smallEtaleModuleProjectionAdjunction_unit :
    IsIso (smallEtaleModuleProjectionAdjunction B S).unit :=
  SheafOfModules.isIso_unit_of_isIso_coefficient.{u, u + 1, u, u, u + 1, u + 1}
    (smallEtaleToBigEtaleFunctor B S S (𝟙 S))
    (SmallEtale.topology B S.obj S.property)
    (BigEtaleOver.topology B S.obj S.property)
    (BigEtaleOver.structureSheaf B S.obj S.property)
    (𝟙 _) (smallEtaleModuleProjectionAdjunction B S)

/-- **`π_{S,*}π_S^* = 𝟭` on sheaves of `𝒪`-modules.** Pulling a sheaf of `𝒪_{S_étale}`-modules
back to the big étale site over `S` and restricting it again returns it, naturally. -/
public def smallEtaleModuleProjectionUnitIso :
    smallEtaleModuleProjectionPullback B S ⋙ smallEtaleModuleRestriction B S S (𝟙 S) ≅
      𝟭 (SheafOfModules.{u + 1} (SmallEtale.structureSheaf B S.obj S.property)) :=
  (asIso (smallEtaleModuleProjectionAdjunction B S).unit).symm

/-- `π_S^*` preserves finite colimits, being a left adjoint. -/
public instance smallEtaleModuleProjectionPullback_preservesFiniteColimits :
    PreservesFiniteColimits (smallEtaleModuleProjectionPullback B S) :=
  ((smallEtaleModuleProjectionAdjunction B S).leftAdjoint_preservesColimits.{u + 1,
    u + 1}).preservesFiniteColimits

/-- `π_S^*` is additive: it preserves finite colimits, hence binary biproducts. -/
public instance smallEtaleModuleProjectionPullback_additive :
    (smallEtaleModuleProjectionPullback B S).Additive :=
  have : PreservesBinaryBiproducts (smallEtaleModuleProjectionPullback B S) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

end Underived

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- The quasi-isomorphisms of the unbounded homotopy category of sheaves of
`𝒪_{S_étale}`-modules, the class at which `Lπ_S^*` is taken. -/
public abbrev smallEtaleModuleQuasiIso :
    MorphismProperty
      (HomotopyCategory (SheafOfModules.{u + 1} (SmallEtale.structureSheaf B S.obj S.property))
        (ComplexShape.up ℤ)) :=
  HomotopyCategory.quasiIso
    (SheafOfModules.{u + 1} (SmallEtale.structureSheaf B S.obj S.property)) (ComplexShape.up ℤ)

/-- **`π_S^{-1}` on abelian sheaves, as the left adjoint of restriction along the Stacks 021F
functor at the identity.**  This is the inverse image of the projection `π_S` at abelian
coefficients, spelled along `AlgebraicGeometry.smallEtaleToBigEtaleFunctor B S S (𝟙 S)` so that
it is left adjoint to `AlgebraicGeometry.smallEtaleRestriction B S S (𝟙 S)` on the nose. -/
abbrev smallEtaleAbelianProjectionPullback :
    Sheaf (SmallEtale.topology B S.obj S.property) Ab.{u + 1} ⥤
      Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1} :=
  (smallEtaleToBigEtaleFunctor B S S (𝟙 S)).sheafPullback Ab.{u + 1}
    (SmallEtale.topology B S.obj S.property) (BigEtaleOver.topology B S.obj S.property)

/-- **`π_S^{-1}` is exact on abelian sheaves** (Stacks 0DDI): the small étale inclusion is
representably flat, the small étale site having finite limits which the inclusion preserves, and
lower shriek of abelian sheaves along a representably flat continuous functor is left exact. -/
instance smallEtaleAbelianProjectionPullback_preservesFiniteLimits :
    PreservesFiniteLimits (smallEtaleAbelianProjectionPullback B S) := by
  have : RepresentablyFlat (smallEtaleToBigEtaleFunctor B S S (𝟙 S)) := by
    rw [smallEtaleToBigEtaleFunctor_id_eq]
    have : PreservesLimitsOfShape (Discrete PEmpty.{1})
        (SmallEtale.inclusion B S.obj S.property) :=
      preservesLimitsOfShape_pempty_of_preservesTerminal _
    have : PreservesFiniteLimits (SmallEtale.inclusion B S.obj S.property) :=
      preservesFiniteLimits_of_preservesTerminal_and_pullbacks _
    exact flat_of_preservesFiniteLimits _
  exact Stacks.Sites.LowerShriek.preservesFiniteLimits_sheafPullback_of_representablyFlat.{u + 1}
    (smallEtaleToBigEtaleFunctor B S S (𝟙 S)) _ _

/-- **Stacks 07AC, existence, for the small étale inclusion: `Lπ_S^*` exists.**  The left derived
functor of `π_S^*` on unbounded complexes of sheaves of `𝒪`-modules is defined on the whole
derived category.  This is
`Stacks.Cohomology.ExactAbelianLowerShriek.hasPointwiseLeftDerivedFunctor`: `π_{S,*}` lies over
the abelian restriction `i_S^{-1}`, whose left adjoint `π_S^{-1}` is exact
(`AlgebraicGeometry.smallEtaleAbelianProjectionPullback_preservesFiniteLimits`). -/
public instance hasPointwiseLeftDerivedFunctor_smallEtaleModuleProjectionPullback :
    ((smallEtaleModuleProjectionPullback B S).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor (smallEtaleModuleQuasiIso B S) := by
  have : HasExactColimitsOfShape ℕ (SheafOfModules.{u + 1}
      (BigEtaleOver.structureSheaf B S.obj S.property)) := by
    have : AB5OfSize.{0, 0} (SheafOfModules.{u + 1}
        (BigEtaleOver.structureSheaf B S.obj S.property)) := AB5OfSize_shrink _
    exact AB5OfSize.ofShape ℕ
  have : PreservesColimitsOfShape ℕ (smallEtaleModuleProjectionPullback B S) :=
    ((smallEtaleModuleProjectionAdjunction B S).leftAdjoint_preservesColimits.{0,
      0}).preservesColimitsOfShape
  exact Stacks.Cohomology.ExactAbelianLowerShriek.hasPointwiseLeftDerivedFunctor.{u, u, u, u + 1}
    (smallEtaleModuleProjectionAdjunction B S) (smallEtaleRestriction B S S (𝟙 S))
    (Iso.refl _)
    ((smallEtaleToBigEtaleFunctor B S S (𝟙 S)).sheafAdjunctionContinuous Ab.{u + 1}
      (SmallEtale.topology B S.obj S.property) (BigEtaleOver.topology B S.obj S.property))
    (smallEtaleModuleProjectionPullback B S) (𝟭 _) (Functor.rightUnitor _).symm

/-- **`Lπ_S^*`**, the unbounded left derived functor of `π_S^*` on sheaves of `𝒪`-modules. -/
public abbrev derivedSmallEtaleModuleProjectionPullback :
    DerivedCategory (SheafOfModules.{u + 1} (SmallEtale.structureSheaf B S.obj S.property)) ⥤
      DerivedCategory (SheafOfModules.{u + 1}
        (BigEtaleOver.structureSheaf B S.obj S.property)) :=
  ((smallEtaleModuleProjectionPullback B S).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerived DerivedCategory.Qh (smallEtaleModuleQuasiIso B S)

/-- The counit exhibiting `Lπ_S^*` as a left derived functor of degreewise `π_S^*`. -/
public abbrev derivedSmallEtaleModuleProjectionPullbackCounit :
    DerivedCategory.Qh ⋙ derivedSmallEtaleModuleProjectionPullback B S ⟶
      (smallEtaleModuleProjectionPullback B S).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh :=
  ((smallEtaleModuleProjectionPullback B S).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerivedCounit DerivedCategory.Qh (smallEtaleModuleQuasiIso B S)

/-- **`Lπ_S^*` is absolute**: followed by any functor `G'` out of the derived category of the big
étale site, it is still a left derived functor, of the degreewise `π_S^*` followed by `G'`.  This
is `Stacks.Cohomology.ExactAbelianLowerShriek.isLeftDerivedFunctor_comp`: `Lπ_S^*` is computed by
resolutions by objects that are `Ext`-acyclic for `π_S^* ⊣ π_{S,*}`. -/
public instance isLeftDerivedFunctor_derivedSmallEtaleModuleProjectionPullback_comp
    {E : Type*} [Category E]
    (G' : DerivedCategory (SheafOfModules.{u + 1}
      (BigEtaleOver.structureSheaf B S.obj S.property)) ⥤ E) :
    (derivedSmallEtaleModuleProjectionPullback B S ⋙ G').IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh (derivedSmallEtaleModuleProjectionPullback B S)
          G').inv ≫
        Functor.whiskerRight (derivedSmallEtaleModuleProjectionPullbackCounit B S) G')
      (smallEtaleModuleQuasiIso B S) := by
  have : HasExactColimitsOfShape ℕ (SheafOfModules.{u + 1}
      (BigEtaleOver.structureSheaf B S.obj S.property)) := by
    have : AB5OfSize.{0, 0} (SheafOfModules.{u + 1}
        (BigEtaleOver.structureSheaf B S.obj S.property)) := AB5OfSize_shrink _
    exact AB5OfSize.ofShape ℕ
  have : PreservesColimitsOfShape ℕ (smallEtaleModuleProjectionPullback B S) :=
    ((smallEtaleModuleProjectionAdjunction B S).leftAdjoint_preservesColimits.{0,
      0}).preservesColimitsOfShape
  exact Stacks.Cohomology.ExactAbelianLowerShriek.isLeftDerivedFunctor_comp.{u, u, u, u + 1}
    (smallEtaleModuleProjectionAdjunction B S) (smallEtaleRestriction B S S (𝟙 S))
    (Iso.refl _)
    ((smallEtaleToBigEtaleFunctor B S S (𝟙 S)).sheafAdjunctionContinuous Ab.{u + 1}
      (SmallEtale.topology B S.obj S.property) (BigEtaleOver.topology B S.obj S.property))
    (smallEtaleModuleProjectionPullback B S) (𝟭 _) (Functor.rightUnitor _).symm _ _ G'

/-- **`π_{S,*}Lπ_S^* ≅ 𝟭` on the unbounded derived categories.** `π_{S,*}` is exact, so the
functor it induces on derived categories is its own derived functor; the composite
`Lπ_S^* ⋙ π_{S,*}` is then a left derived functor of the degreewise `π_{S,*}π_S^*`, which is the
identity by `AlgebraicGeometry.smallEtaleModuleProjectionUnitIso`, and so is the identity functor
of the derived category.  Uniqueness of left derived functors identifies the two.

The absoluteness of `Lπ_S^*`, that it stays a left derived functor after composition with the
exact `π_{S,*}`, is
`AlgebraicGeometry.isLeftDerivedFunctor_derivedSmallEtaleModuleProjectionPullback_comp`. -/
public def derivedSmallEtaleModuleProjectionUnitIso :
    derivedSmallEtaleModuleProjectionPullback B S ⋙
        (smallEtaleModuleRestriction B S S (𝟙 S)).mapDerivedCategory ≅
      𝟭 (DerivedCategory (SheafOfModules.{u + 1}
        (SmallEtale.structureSheaf B S.obj S.property))) := by
  have hPR : (smallEtaleModuleProjectionPullback B S).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      (smallEtaleModuleRestriction B S S (𝟙 S)).mapHomotopyCategory (ComplexShape.up ℤ) ≅
        𝟭 (HomotopyCategory
          (SheafOfModules.{u + 1} (SmallEtale.structureSheaf B S.obj S.property))
          (ComplexShape.up ℤ)) :=
    Functor.mapHomotopyCategoryCompIso (smallEtaleModuleProjectionUnitIso B S)
        (ComplexShape.up ℤ) ≪≫
      Functor.mapHomotopyCategoryIdIso _ (ComplexShape.up ℤ)
  have θ : ((smallEtaleModuleProjectionPullback B S).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) ⋙
      (smallEtaleModuleRestriction B S S (𝟙 S)).mapDerivedCategory ≅
        DerivedCategory.Qh :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (smallEtaleModuleRestriction B S S (𝟙 S)).mapDerivedCategoryFactorsh ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight hPR DerivedCategory.Qh ≪≫
      Functor.leftUnitor _
  have η : DerivedCategory.Qh ⋙
      𝟭 (DerivedCategory (SheafOfModules.{u + 1}
        (SmallEtale.structureSheaf B S.obj S.property))) ≅
      ((smallEtaleModuleProjectionPullback B S).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) ⋙
          (smallEtaleModuleRestriction B S S (𝟙 S)).mapDerivedCategory :=
    Functor.rightUnitor _ ≪≫ θ.symm
  have : (𝟭 (DerivedCategory (SheafOfModules.{u + 1}
      (SmallEtale.structureSheaf B S.obj S.property)))).IsLeftDerivedFunctor η.hom
        (smallEtaleModuleQuasiIso B S) :=
    Functor.isLeftDerivedFunctor_of_inverts (smallEtaleModuleQuasiIso B S) _ η
  exact Functor.leftDerivedUnique
    (LF := derivedSmallEtaleModuleProjectionPullback B S ⋙
      (smallEtaleModuleRestriction B S S (𝟙 S)).mapDerivedCategory)
    (LF' := 𝟭 (DerivedCategory (SheafOfModules.{u + 1}
      (SmallEtale.structureSheaf B S.obj S.property))))
    (α := (Functor.associator DerivedCategory.Qh
        (derivedSmallEtaleModuleProjectionPullback B S)
        (smallEtaleModuleRestriction B S S (𝟙 S)).mapDerivedCategory).inv ≫
      Functor.whiskerRight (derivedSmallEtaleModuleProjectionPullbackCounit B S)
        (smallEtaleModuleRestriction B S S (𝟙 S)).mapDerivedCategory)
    (α'₂ := η.hom) (W := smallEtaleModuleQuasiIso B S)

/-- **Stacks 0DDH, part (2), on underlying abelian complexes.** Let `S` be an object of a big
étale site and let `K` be an
unbounded complex of sheaves of `𝒪_{S_étale}`-modules.  Cohomology on the big étale site of `S`
of the derived pullback `Lπ_S^*K` agrees with cohomology of `K` on the small étale site of `S`,
naturally in `K`:
`H^n_étale(S, Lπ_S^*K) = H^n(S_étale, K)`.

Both sides are `RΓ` of abelian sheaves applied after `SheafOfModules.toSheaf`; the statement with
`RΓ` taken in `D(𝒪)`, as in the source, is
`AlgebraicGeometry.bigSmallEtaleModuleProjectionPullbackSectionsCohomologyIsoSelf`.

The proof is part (6), `AlgebraicGeometry.bigSmallEtaleModuleCohomologyIso`, at the identity
morphism of `S`, where `i_f^*` is `π_{S,*}`, followed by
`AlgebraicGeometry.derivedSmallEtaleModuleProjectionUnitIso`. -/
public def bigSmallEtaleModuleProjectionPullbackCohomologyIsoSelf :
    derivedSmallEtaleModuleProjectionPullback B S ⋙
        ((SheafOfModules.toSheaf.{u + 1}
            (BigEtaleOver.structureSheaf B S.obj S.property)).mapDerivedCategory ⋙
          (((bigEtaleSections B S S (𝟙 S)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
              (HomotopyCategory.quasiIso
                (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1})
                (ComplexShape.up ℤ)))) ≅
      (SheafOfModules.toSheaf.{u + 1}
          (SmallEtale.structureSheaf B S.obj S.property)).mapDerivedCategory ⋙
        (((Sheaf.Γ (SmallEtale.topology B S.obj S.property) Ab.{u + 1}).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
            (HomotopyCategory.quasiIso
              (Sheaf (SmallEtale.topology B S.obj S.property) Ab.{u + 1})
              (ComplexShape.up ℤ))) :=
  Functor.isoWhiskerLeft _ (bigSmallEtaleModuleCohomologyIso B S S (𝟙 S)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedSmallEtaleModuleProjectionUnitIso B S) _ ≪≫
    Functor.leftUnitor _

end Derived

end AlgebraicGeometry

end
