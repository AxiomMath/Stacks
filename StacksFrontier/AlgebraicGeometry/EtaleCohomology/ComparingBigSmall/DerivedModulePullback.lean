module

public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ModuleProjectionPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ModulePullback

/-!
# `Lf_small^* = i_f^* ∘ Lπ_S^*` on sheaves of `𝒪`-modules, and Stacks 0DDH part (4)

Let `B` be a big étale site and let `f : T ⟶ S` be a morphism of its objects.  This file proves
the identity `Lf_small^* ≅ i_f^* ∘ Lπ_S^*` of functors on the unbounded derived categories of
sheaves of `𝒪`-modules, at the module universe `u + 1` of the étale cohomology comparisons of
Stacks 0DDH, and deduces from it and part (6) the remaining clause of that tag:

Stacks 0DDH, part (4), on underlying abelian complexes:
`H^n_étale(T, Lπ_S^*K) = H^n(T_étale, Lf_small^*K)`.

## Main definitions

* `AlgebraicGeometry.derivedSmallEtaleModulePullback` — `Lf_small^*`, the unbounded left derived
  functor of `f_small^*` on sheaves of `𝒪`-modules.

## Main results

* `AlgebraicGeometry.smallEtaleModuleProjectionPullbackRestrictionIso` — the underived identity
  `π_S^* ⋙ i_f^* ≅ f_small^*`.
* `AlgebraicGeometry.derivedSmallEtaleModulePullbackIso` — its derived form,
  `Lπ_S^* ⋙ i_f^* ≅ Lf_small^*`.
* `AlgebraicGeometry.bigSmallEtaleModuleProjectionPullbackCohomologyIso` — Stacks 0DDH,
  part (4), on underlying abelian complexes.

## The underived identity, in four steps

`i_f^*` is restriction along `AlgebraicGeometry.smallEtaleToBigEtaleFunctor B T S f`, which *is*
`SmallEtale.inclusion B T.obj T.property ⋙ Over.map f`, so it factors as `f_big^* ⋙ π_{T,*}` by
`SheafOfModules.pushforwardComp` together with a `SheafOfModules.pushforwardCongr` for
`𝟙 ≫ map 𝟙 = 𝟙`; this is
`AlgebraicGeometry.smallEtaleModuleRestrictionFactorIso`.  The mate of the module form of
Stacks 0759, `AlgebraicGeometry.smallEtaleModulePullbackProjectionIso`, then turns
`π_S^* ⋙ f_big^*` into `f_small^* ⋙ π_T^*`, and `π_{T,*}π_T^* ≅ 𝟭` leaves `f_small^*`.

The two spellings of the small étale projection have to be crossed to put those steps together.
`AlgebraicGeometry.smallEtaleModuleProjectionPullback` and
`AlgebraicGeometry.smallEtaleModuleProjectionUnitIso` are written along
`AlgebraicGeometry.smallEtaleToBigEtaleFunctor B X X (𝟙 X)`, the Stacks 021F functor at the
identity, whereas the Stacks 0759 mate is written along
`AlgebraicGeometry.SmallEtale.inclusion`.  The two functors are *equal*, by
`AlgebraicGeometry.smallEtaleToBigEtaleFunctor_id_eq`, and
`AlgebraicGeometry.smallEtaleModuleInclusionInverseImage_eq` transports `π_{X,*}` across that
equality with `Stacks.SheafOfModules.pushforward_eqToHom_eq`, whose `eqToHom` is the identity
here because both inverse-image rings are `rfl`-equal to `AlgebraicGeometry.SmallEtale`'s own
structure sheaf (`AlgebraicGeometry.smallEtaleModuleInverseImageRing_eq`).  Uniqueness of left
adjoints then crosses `π_X^*` itself.

## The derived identity

`Lf_small^*` is the unbounded left derived functor of degreewise `f_small^*`, and
`Lπ_S^* ⋙ i_f^*` is a left derived functor of degreewise `π_S^* ⋙ i_f^*` because `i_f^*` is
exact (`AlgebraicGeometry.smallEtaleModuleRestriction_preservesFiniteLimits` and
`AlgebraicGeometry.smallEtaleModuleRestriction_preservesFiniteColimits`).  The underived
identity above identifies the two degreewise functors, and uniqueness of left derived functors
identifies the two derived ones.  This is the proof of
`AlgebraicGeometry.derivedSmallEtaleModuleProjectionUnitIso` with `i_f^*` in place of `π_{S,*}`.

## Why `f_small^*` is not exact, and why part (4) is not the abelian part (3)

`f_small^*` is only *right* exact: a module pullback is the abelian inverse image followed by
base change along the structure map, which is exact only under flatness; what is available is
`AlgebraicGeometry.smallEtaleModulePullback_preservesFiniteColimits`.  So `Lf_small^*` is a
genuine left derived functor, and as for part (2) no reduction to the abelian comparison is
possible: `Stacks.SheafOfModules.lowerShriekForget_not_isomorphic` and
`Stacks.SheafOfModules.lowerShriek_not_preservesFiniteLimits` rule it out, the latter's
counterexample functor being full, faithful, final and covering the terminal object — the shape
of the small étale inclusion.

## The derived functors involved, and the convention on `H^n`

Every derived functor in part (4) exists, and nothing is assumed of them.  `Lπ_S^*` exists and
is absolute (`AlgebraicGeometry.hasPointwiseLeftDerivedFunctor_smallEtaleModuleProjectionPullback`
and `AlgebraicGeometry.isLeftDerivedFunctor_derivedSmallEtaleModuleProjectionPullback_comp`), so
in particular `Lπ_S^* ⋙ i_f^*` is a left derived functor of `π_S^* ⋙ i_f^*`.  `Lf_small^*`
exists by `AlgebraicGeometry.hasPointwiseLeftDerivedFunctor_smallEtaleModulePullbackLarge`:
`f_small^*` is `π_S^*` followed by the exact `i_f^*`, so the class of objects with which
`Lπ_S^*` is constructed by the criterion of Stacks 0794 serves for `f_small^*` as well.  The two
derived section functors exist by the K-injective resolutions of the two Grothendieck abelian
categories of abelian sheaves, and the derived functor of the exact `i_f^{-1}` is the functor it
induces on derived categories (`AlgebraicGeometry.hasRightDerivedFunctor_smallEtaleRestriction`).

Part (4) is proved here on underlying complexes of abelian sheaves: both sides are `RΓ` of the
image of the coefficient object under `SheafOfModules.toSheaf`. The statement with `RΓ` taken in
the derived categories of modules, as in the source, is
`AlgebraicGeometry.bigSmallEtaleModuleProjectionPullbackSectionsCohomologyIso` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ComparingBigSmall/ModuleSectionsCohomology.lean`,
deduced from this one by Stacks 0D6J.

## References

* [Stacks Project, Tag 0DDH](https://stacks.math.columbia.edu/tag/0DDH)
* [Stacks Project, Tag 0759](https://stacks.math.columbia.edu/tag/0759)
* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
* [Stacks Project, Tag 021F](https://stacks.math.columbia.edu/tag/021F)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)

section Crossing

attribute [local instance] smallEtaleInclusion_isCocontinuous

variable (X : B.Scheme)

/-- **`π_{X,*}` is the same functor in the two spellings of the small étale projection.**
Restriction of sheaves of `𝒪`-modules along `AlgebraicGeometry.SmallEtale.inclusion` is
restriction along `AlgebraicGeometry.smallEtaleToBigEtaleFunctor B X X (𝟙 X)`, the Stacks 021F
functor at the identity.

The two site functors are equal by
`AlgebraicGeometry.smallEtaleToBigEtaleFunctor_id_eq`, so this is
`Stacks.SheafOfModules.pushforward_eqToHom_eq`; the `eqToHom` it inserts is the identity because
both inverse-image rings are `rfl`-equal to the structure sheaf of the small étale site of `X`
(`AlgebraicGeometry.smallEtaleModuleInverseImageRing_eq`). -/
public theorem smallEtaleModuleInclusionInverseImage_eq :
    Stacks.SheafOfModules.inverseImage.{u + 1}
        (SmallEtale.topology B X.obj X.property)
        (BigEtaleOver.topology B X.obj X.property)
        (SmallEtale.inclusion B X.obj X.property)
        (BigEtaleOver.structureSheaf B X.obj X.property) =
      smallEtaleModuleRestriction B X X (𝟙 X) := by
  change SheafOfModules.pushforward.{u + 1}
      (F := SmallEtale.inclusion B X.obj X.property)
      (Stacks.SheafOfModules.structureMap
        (SmallEtale.topology B X.obj X.property)
        (BigEtaleOver.topology B X.obj X.property)
        (SmallEtale.inclusion B X.obj X.property)
        (BigEtaleOver.structureSheaf B X.obj X.property)) = _
  refine Eq.trans ?_
    (Stacks.SheafOfModules.pushforward_eqToHom_eq
      (SmallEtale.topology B X.obj X.property)
      (BigEtaleOver.topology B X.obj X.property)
      (smallEtaleToBigEtaleFunctor_id_eq B X) _ rfl)
  erw [Category.comp_id]
  rfl

/-- **`π_X^*` is the same functor in the two spellings of the small étale projection.**
`AlgebraicGeometry.smallEtaleModuleProjectionPullback`, the module lower shriek of Stacks 0797
along the Stacks 021F functor at the identity, is the module lower shriek along
`AlgebraicGeometry.SmallEtale.inclusion`.

Two left adjoints of one functor are canonically isomorphic, the two right adjoints being equal
by `AlgebraicGeometry.smallEtaleModuleInclusionInverseImage_eq`. -/
public def smallEtaleModuleInclusionProjectionPullbackIso :
    smallEtaleModuleProjectionPullback B X ≅
      Stacks.SheafOfModules.lowerShriek.{u + 1}
        (SmallEtale.topology B X.obj X.property)
        (BigEtaleOver.topology B X.obj X.property)
        (SmallEtale.inclusion B X.obj X.property)
        (BigEtaleOver.structureSheaf B X.obj X.property) :=
  Adjunction.leftAdjointUniq
    ((smallEtaleModuleProjectionAdjunction B X).ofNatIsoRight
      (eqToIso (smallEtaleModuleInclusionInverseImage_eq B X).symm))
    (Stacks.SheafOfModules.lowerShriekAdjunction.{u + 1}
      (SmallEtale.topology B X.obj X.property)
      (BigEtaleOver.topology B X.obj X.property)
      (SmallEtale.inclusion B X.obj X.property)
      (BigEtaleOver.structureSheaf B X.obj X.property))

/-- **`π_{X,*}π_X^* ≅ 𝟭` at the inclusion spelling.**  This is
`AlgebraicGeometry.smallEtaleModuleProjectionUnitIso` read through the two crossings of
`AlgebraicGeometry.smallEtaleModuleInclusionProjectionPullbackIso` and
`AlgebraicGeometry.smallEtaleModuleInclusionInverseImage_eq`. -/
public def smallEtaleModuleInclusionProjectionUnitIso :
    Stacks.SheafOfModules.lowerShriek.{u + 1}
          (SmallEtale.topology B X.obj X.property)
          (BigEtaleOver.topology B X.obj X.property)
          (SmallEtale.inclusion B X.obj X.property)
          (BigEtaleOver.structureSheaf B X.obj X.property) ⋙
        Stacks.SheafOfModules.inverseImage.{u + 1}
          (SmallEtale.topology B X.obj X.property)
          (BigEtaleOver.topology B X.obj X.property)
          (SmallEtale.inclusion B X.obj X.property)
          (BigEtaleOver.structureSheaf B X.obj X.property) ≅
      𝟭 (SheafOfModules.{u + 1} (SmallEtale.structureSheaf B X.obj X.property)) :=
  Functor.isoWhiskerRight (smallEtaleModuleInclusionProjectionPullbackIso B X).symm _ ≪≫
    Functor.isoWhiskerLeft _ (eqToIso (smallEtaleModuleInclusionInverseImage_eq B X)) ≪≫
    smallEtaleModuleProjectionUnitIso B X

end Crossing

section Underived

attribute [local instance] smallEtaleInclusion_isCocontinuous

/-- **`i_f^* ≅ f_big^* ⋙ π_{T,*}` on sheaves of `𝒪`-modules.**  Restriction along the
Stacks 021F functor `V/T ↦ V/S` is restriction along postcomposition with `f` followed by
restriction to the small étale site of `T`.

The Stacks 021F functor *is* `SmallEtale.inclusion B T.obj T.property ⋙ Over.map f`, all three
functors are direct images of sheaves of modules with the identity structure map, and
`SheafOfModules.pushforwardComp` composes two such; the structure map of the composite is
`𝟙 ≫ map 𝟙`, which `SheafOfModules.pushforwardCongr` identifies with `𝟙`. -/
public def smallEtaleModuleRestrictionFactorIso :
    bigEtaleInverseImageModules B T S f ⋙
        Stacks.SheafOfModules.inverseImage.{u + 1}
          (SmallEtale.topology B T.obj T.property)
          (BigEtaleOver.topology B T.obj T.property)
          (SmallEtale.inclusion B T.obj T.property)
          (BigEtaleOver.structureSheaf B T.obj T.property) ≅
      smallEtaleModuleRestriction B T S f :=
  SheafOfModules.pushforwardComp.{u + 1}
      (Stacks.SheafOfModules.structureMap
        (SmallEtale.topology B T.obj T.property)
        (BigEtaleOver.topology B T.obj T.property)
        (SmallEtale.inclusion B T.obj T.property)
        (BigEtaleOver.structureSheaf B T.obj T.property))
      (Stacks.SheafOfModules.structureMap
        (BigEtaleOver.topology B T.obj T.property)
        (BigEtaleOver.topology B S.obj S.property)
        (Over.map f)
        (BigEtaleOver.structureSheaf B S.obj S.property)) ≪≫
    SheafOfModules.pushforwardCongr
      ((Category.id_comp _).trans (CategoryTheory.Functor.map_id _ _))

section Mate

/-- **`π_S^* ⋙ i_f^* ≅ f_small^*` on sheaves of `𝒪`-modules.**  Pulling a sheaf of
`𝒪_{S_étale}`-modules back to the big étale site over `S` and restricting it to the small étale
site of `T` is the small étale pullback along `f`.

The factorization `i_f^* ≅ f_big^* ⋙ π_{T,*}`
(`AlgebraicGeometry.smallEtaleModuleRestrictionFactorIso`) turns the left-hand side into
`π_S^* ⋙ f_big^* ⋙ π_{T,*}`; the mate of the module form of Stacks 0759
(`AlgebraicGeometry.smallEtaleModulePullbackProjectionIso`) turns `π_S^* ⋙ f_big^*` into
`f_small^* ⋙ π_T^*`, after crossing the two spellings of `π_S^*` with
`AlgebraicGeometry.smallEtaleModuleInclusionProjectionPullbackIso`; and
`AlgebraicGeometry.smallEtaleModuleInclusionProjectionUnitIso` cancels `π_{T,*}π_T^*`. -/
public def smallEtaleModuleProjectionPullbackRestrictionIso :
    smallEtaleModuleProjectionPullback B S ⋙ smallEtaleModuleRestriction B T S f ≅
      smallEtaleModulePullbackLarge B T S f :=
  Functor.isoWhiskerLeft _ (smallEtaleModuleRestrictionFactorIso B T S f).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (smallEtaleModuleInclusionProjectionPullbackIso B S) _ ≪≫
        (smallEtaleModulePullbackProjectionIso B T S f).symm) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (smallEtaleModuleInclusionProjectionUnitIso B T) ≪≫
    Functor.rightUnitor _

end Mate

end Underived

section Derived

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits
attribute [local instance] smallEtaleInclusion_isCocontinuous

/-- **`Lf_small^*` exists**: the left derived functor of `f_small^*` on unbounded complexes of
sheaves of `𝒪`-modules is defined on the whole derived category.

`f_small^*` is `π_S^*` followed by the exact `i_f^*`
(`AlgebraicGeometry.smallEtaleModuleProjectionPullbackRestrictionIso`), so the class of objects
that are `Ext`-acyclic for `π_S^* ⊣ π_{S,*}`, with which `Lπ_S^*` is constructed, serves for
`f_small^*` too; this is `Stacks.Cohomology.ExactAbelianLowerShriek.hasPointwiseLeftDerivedFunctor`
applied to `f_small^*` as `F'`. -/
public instance hasPointwiseLeftDerivedFunctor_smallEtaleModulePullbackLarge :
    ((smallEtaleModulePullbackLarge B T S f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor (smallEtaleModuleQuasiIso B S) := by
  have : HasExactColimitsOfShape ℕ (SheafOfModules.{u + 1}
      (SmallEtale.structureSheaf B T.obj T.property)) := by
    have : AB5OfSize.{0, 0} (SheafOfModules.{u + 1}
        (SmallEtale.structureSheaf B T.obj T.property)) := AB5OfSize_shrink _
    exact AB5OfSize.ofShape ℕ
  have : PreservesColimitsOfShape ℕ (smallEtaleModulePullbackLarge B T S f) :=
    ((smallEtaleModulePullbackAdjunction B T S f).leftAdjoint_preservesColimits.{0,
      0}).preservesColimitsOfShape
  exact Stacks.Cohomology.ExactAbelianLowerShriek.hasPointwiseLeftDerivedFunctor.{u, u, u, u + 1}
    (smallEtaleModuleProjectionAdjunction B S) (smallEtaleRestriction B S S (𝟙 S))
    (Iso.refl _)
    ((smallEtaleToBigEtaleFunctor B S S (𝟙 S)).sheafAdjunctionContinuous Ab.{u + 1}
      (SmallEtale.topology B S.obj S.property) (BigEtaleOver.topology B S.obj S.property))
    (smallEtaleModulePullbackLarge B T S f) (smallEtaleModuleRestriction B T S f)
    (smallEtaleModuleProjectionPullbackRestrictionIso B T S f).symm

/-- **`Lf_small^*`**, the unbounded left derived functor of `f_small^*` on sheaves of
`𝒪`-modules.

`f_small^*` is only right exact — a module pullback is the abelian inverse image followed by base
change along the structure map, exact only under flatness — so this is a genuine left derived
functor; see the module docstring. -/
public abbrev derivedSmallEtaleModulePullback :
    DerivedCategory (SheafOfModules.{u + 1} (SmallEtale.structureSheaf B S.obj S.property)) ⥤
      DerivedCategory (SheafOfModules.{u + 1}
        (SmallEtale.structureSheaf B T.obj T.property)) :=
  ((smallEtaleModulePullbackLarge B T S f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerived DerivedCategory.Qh (smallEtaleModuleQuasiIso B S)

/-- The counit exhibiting `Lf_small^*` as a left derived functor of degreewise `f_small^*`. -/
public abbrev derivedSmallEtaleModulePullbackCounit :
    DerivedCategory.Qh ⋙ derivedSmallEtaleModulePullback B T S f ⟶
      (smallEtaleModulePullbackLarge B T S f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh :=
  ((smallEtaleModulePullbackLarge B T S f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerivedCounit DerivedCategory.Qh (smallEtaleModuleQuasiIso B S)

/-- **`Lπ_S^* ⋙ i_f^* ≅ Lf_small^*` on the unbounded derived categories.**  `i_f^*` is exact, so
the functor it induces on derived categories is its own derived functor; the composite
`Lπ_S^* ⋙ i_f^*` is then a left derived functor of the degreewise `π_S^* ⋙ i_f^*`, which is
`f_small^*` by `AlgebraicGeometry.smallEtaleModuleProjectionPullbackRestrictionIso`.  Uniqueness
of left derived functors identifies the two.

The absoluteness of `Lπ_S^*`, that it stays a left derived functor after composition with the
exact `i_f^*`, is
`AlgebraicGeometry.isLeftDerivedFunctor_derivedSmallEtaleModuleProjectionPullback_comp`. -/
public def derivedSmallEtaleModulePullbackIso :
    derivedSmallEtaleModuleProjectionPullback B S ⋙
        (smallEtaleModuleRestriction B T S f).mapDerivedCategory ≅
      derivedSmallEtaleModulePullback B T S f := by
  have hPR : (smallEtaleModuleProjectionPullback B S).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      (smallEtaleModuleRestriction B T S f).mapHomotopyCategory (ComplexShape.up ℤ) ≅
        (smallEtaleModulePullbackLarge B T S f).mapHomotopyCategory (ComplexShape.up ℤ) :=
    Functor.mapHomotopyCategoryCompIso
      (smallEtaleModuleProjectionPullbackRestrictionIso B T S f) (ComplexShape.up ℤ)
  have θ : ((smallEtaleModuleProjectionPullback B S).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) ⋙
      (smallEtaleModuleRestriction B T S f).mapDerivedCategory ≅
        (smallEtaleModulePullbackLarge B T S f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (smallEtaleModuleRestriction B T S f).mapDerivedCategoryFactorsh ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight hPR DerivedCategory.Qh
  exact Functor.leftDerivedNatIso
    (LF' := derivedSmallEtaleModuleProjectionPullback B S ⋙
      (smallEtaleModuleRestriction B T S f).mapDerivedCategory)
    (LF := derivedSmallEtaleModulePullback B T S f)
    (α' := (Functor.associator DerivedCategory.Qh
        (derivedSmallEtaleModuleProjectionPullback B S)
        (smallEtaleModuleRestriction B T S f).mapDerivedCategory).inv ≫
      Functor.whiskerRight (derivedSmallEtaleModuleProjectionPullbackCounit B S)
        (smallEtaleModuleRestriction B T S f).mapDerivedCategory)
    (α := derivedSmallEtaleModulePullbackCounit B T S f)
    (W := smallEtaleModuleQuasiIso B S) θ

/-- **Stacks 0DDH, part (4), on underlying abelian complexes.** Let `f : T ⟶ S` be a morphism
of a big étale site and let `K` be
an unbounded complex of sheaves of `𝒪_{S_étale}`-modules.  Cohomology over the object `T ⟶ S` of
the big étale site of `S` of the derived pullback `Lπ_S^*K` agrees with cohomology on the small
étale site of `T` of the derived small étale pullback `Lf_small^*K`, naturally in `K`:
`H^n_étale(T, Lπ_S^*K) = H^n(T_étale, Lf_small^*K)`.

Both sides are `RΓ` of abelian sheaves applied after `SheafOfModules.toSheaf`; the statement with
`RΓ` taken in `D(𝒪)`, as in the source, is
`AlgebraicGeometry.bigSmallEtaleModuleProjectionPullbackSectionsCohomologyIso`.

The proof is part (6), `AlgebraicGeometry.bigSmallEtaleModuleCohomologyIso`, followed by
`AlgebraicGeometry.derivedSmallEtaleModulePullbackIso`. -/
public def bigSmallEtaleModuleProjectionPullbackCohomologyIso :
    derivedSmallEtaleModuleProjectionPullback B S ⋙
        ((SheafOfModules.toSheaf.{u + 1}
            (BigEtaleOver.structureSheaf B S.obj S.property)).mapDerivedCategory ⋙
          (((bigEtaleSections B T S f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
              (HomotopyCategory.quasiIso
                (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1})
                (ComplexShape.up ℤ)))) ≅
      derivedSmallEtaleModulePullback B T S f ⋙
        ((SheafOfModules.toSheaf.{u + 1}
            (SmallEtale.structureSheaf B T.obj T.property)).mapDerivedCategory ⋙
          (((Sheaf.Γ (SmallEtale.topology B T.obj T.property) Ab.{u + 1}).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
              (HomotopyCategory.quasiIso
                (Sheaf (SmallEtale.topology B T.obj T.property) Ab.{u + 1})
                (ComplexShape.up ℤ)))) :=
  Functor.isoWhiskerLeft _ (bigSmallEtaleModuleCohomologyIso B T S f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedSmallEtaleModulePullbackIso B T S f) _

end Derived

end AlgebraicGeometry

end
