module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.CohomologicalDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.Cohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.DirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.SheafCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactnessFlat
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.SelfExtOnACollectionOfOpens

/-!
# Restricting a pullback from the small étale site: `i_f^{-1}π_S^{-1} = f_{small}^{-1}`

Let `B` be a big étale site and let `f : T ⟶ S` be a morphism of its underlying category. There
are three inverse images in play:

* `π_S^{-1}`, from the small étale site of `S` to the big étale site over `S`, the left adjoint of
  restriction along the small-site inclusion;
* `i_f^{-1}`, from the big étale site over `S` to the small étale site of `T`, which *is*
  restriction along the functor `V/T ↦ V/S`;
* `f_{small}^{-1}`, from the small étale site of `S` to the small étale site of `T`, the left
  adjoint of restriction along small étale base change.

This file proves that the first two compose to the third. It is the shared input for the clauses
of Stacks 0DDH that compute big-site cohomology of a pullback from the small site: combined with
`AlgebraicGeometry.bigSmallEtaleCohomologyIso` it turns `RΓ(T, π_S^{-1}K)` into
`RΓ(T_étale, f_{small}^{-1}K)`.

## Main results

* `AlgebraicGeometry.smallEtaleRestrictionProjectionPullbackIso` — the identity
  `i_f^{-1} ∘ π_S^{-1} ≅ f_{small}^{-1}`, at an arbitrary coefficient category.
* `AlgebraicGeometry.bigEtalePullbackProjectionPullbackIso` — the inverse-image square
  `f_{big}^{-1} ∘ π_S^{-1} ≅ π_T^{-1} ∘ f_{small}^{-1}`, which is the substance of the previous
  result and the mate of the direct-image square
  `AlgebraicGeometry.smallEtaleRestrictionPushforwardIso` of Stacks 0759.
* `AlgebraicGeometry.bigSmallEtaleProjectionPullbackCohomologyIso` — **Stacks 0DDH, part (3)**:
  `H^n_étale(T, π_S^{-1}K) = H^n(T_étale, f_{small}^{-1}K)`.
* `AlgebraicGeometry.bigSmallEtaleProjectionPullbackCohomologyIsoSelf` — **Stacks 0DDH,
  part (1)**: `H^n_étale(S, π_S^{-1}K) = H^n(S_étale, K)`, the case `f = 𝟙`.

Part (5), the comparison for an arbitrary abelian complex on the big site, is
`AlgebraicGeometry.bigSmallEtaleCohomologyIso`. Of the `O`-module clauses of Stacks 0DDH, part
(6) is `AlgebraicGeometry.bigSmallEtaleModuleCohomologyIso` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ComparingBigSmall/ModuleCohomology.lean` and part
(2) is `AlgebraicGeometry.bigSmallEtaleModuleProjectionPullbackCohomologyIsoSelf` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ComparingBigSmall/ModuleProjectionPullback.lean`;
part (4) is `AlgebraicGeometry.bigSmallEtaleModuleProjectionPullbackCohomologyIso` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ComparingBigSmall/DerivedModulePullback.lean`.

## Implementation notes

Every functor involved is either a restriction along a site functor or the left adjoint of one, so
the whole proof is uniqueness of left adjoints applied to the direct-image square of Stacks 0759,
plus two formal steps. The three steps are:

* `i_f^{-1}` is restriction along `SmallEtale.inclusion B T ⋙ Over.map f`, hence the composite of
  restriction along `Over.map f` — that is `f_{big}^{-1}` — with restriction along the inclusion —
  that is `π_{T,*}`. This is Mathlib's
  `CategoryTheory.Functor.sheafPushforwardContinuousComp`, and is the identity map.
* `f_{big}^{-1} ∘ π_S^{-1} ≅ π_T^{-1} ∘ f_{small}^{-1}`: both sides are left adjoints, of
  `π_{T,*} ∘ f_{small,*}` and of `f_{big,*} ∘ π_{S,*}` respectively, and those two agree by Stacks
  0759. The adjunction `f_{big}^{-1} ⊣ f_{big,*}` needed to assemble one of the two composite
  adjunctions is `CategoryTheory.Adjunction.sheafPushforwardContinuous` applied to
  `CategoryTheory.Over.mapPullbackAdj`: restrictions along adjoint site functors are adjoint.
* `π_{T,*} ∘ π_T^{-1} ≅ 𝟭`, the unit of the projection adjunction, which is invertible because the
  small-site inclusion is fully faithful, continuous and cocontinuous
  (`CategoryTheory.Functor.isIso_unit_of_sheafPushforwardContinuous`, Stacks 00XT).

The coefficient category is a parameter: the statement is used at abelian coefficients, but nothing
in the argument is specific to them. The instance hypotheses are exactly the three left adjoints
that have to exist for the three inverse images to be defined, together with the right Kan
extensions defining `π_{T,*}`'s own right adjoint.

## References

* [Stacks Project, Tag 0DDH](https://stacks.math.columbia.edu/tag/0DDH)
* [Stacks Project, Tag 0759](https://stacks.math.columbia.edu/tag/0759)
* [Stacks Project, Tag 021I](https://stacks.math.columbia.edu/tag/021I)
* [Stacks Project, Tag 00XT](https://stacks.math.columbia.edu/tag/00XT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w' u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S) (A : Type w) [Category.{w'} A]

/-- The inclusion of the small étale category of an object of a big étale site into the big étale
category over it is continuous. -/
private instance smallEtaleInclusion_isContinuous_obj (X : B.Scheme) :
    (SmallEtale.inclusion B X.obj X.property).IsContinuous
      (SmallEtale.topology B X.obj X.property)
      (BigEtaleOver.topology B X.obj X.property) :=
  (smallEtaleInclusion_isMorphismOfSites B X.obj X.property).toIsContinuous


section

variable
  [((SmallEtale.inclusion B S.obj S.property).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (BigEtaleOver.topology B S.obj S.property)).IsRightAdjoint]
  [((SmallEtale.inclusion B T.obj T.property).sheafPushforwardContinuous A
      (SmallEtale.topology B T.obj T.property)
      (BigEtaleOver.topology B T.obj T.property)).IsRightAdjoint]
  [((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

/-- **The inverse-image square of Stacks 0759.** Pulling a sheaf on the small étale site of `S`
back to the big étale site over `S` and then restricting along `f` agrees with pulling it back to
the small étale site of `T` and then up to the big étale site over `T`:
`f_{big}^{-1}π_S^{-1} ≅ π_T^{-1}f_{small}^{-1}`.

This is the mate of `AlgebraicGeometry.smallEtaleRestrictionPushforwardIso`: all four functors are
left adjoints of the four restrictions appearing there, and uniqueness of left adjoints transports
the isomorphism. -/
@[stacks 0759 "inverse images"]
public def bigEtalePullbackProjectionPullbackIso :
    (SmallEtale.inclusion B S.obj S.property).sheafPullback A
        (SmallEtale.topology B S.obj S.property)
        (BigEtaleOver.topology B S.obj S.property) ⋙
      (Over.map f).sheafPushforwardContinuous A
        (BigEtaleOver.topology B T.obj T.property)
        (BigEtaleOver.topology B S.obj S.property) ≅
    (smallEtaleBaseChange B f).sheafPullback A
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property) ⋙
      (SmallEtale.inclusion B T.obj T.property).sheafPullback A
        (SmallEtale.topology B T.obj T.property)
        (BigEtaleOver.topology B T.obj T.property) :=
  (conjugateIsoEquiv
    (((smallEtaleBaseChange B f).sheafAdjunctionContinuous A
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).comp
      ((SmallEtale.inclusion B T.obj T.property).sheafAdjunctionContinuous A
        (SmallEtale.topology B T.obj T.property)
        (BigEtaleOver.topology B T.obj T.property)))
    (((SmallEtale.inclusion B S.obj S.property).sheafAdjunctionContinuous A
        (SmallEtale.topology B S.obj S.property)
        (BigEtaleOver.topology B S.obj S.property)).comp
      ((Over.mapPullbackAdj f).sheafPushforwardContinuous
        (BigEtaleOver.topology B T.obj T.property)
        (BigEtaleOver.topology B S.obj S.property)))).symm
    (smallEtaleRestrictionPushforwardIso B T S f A).symm

variable
  [∀ P : (SmallEtale B T.obj T.property)ᵒᵖ ⥤ A,
    (SmallEtale.inclusion B T.obj T.property).op.HasPointwiseRightKanExtension P]

/-- **`i_f^{-1}π_S^{-1} = f_{small}^{-1}`.** Pulling a sheaf back from the small étale site of `S`
to the big étale site over `S` and then restricting it to the small étale site of `T` along `f`
is pulling it back along `f_{small}` directly.

This is the identity the clauses of Stacks 0DDH about `π_S^{-1}` reduce to: it converts the
comparison of big-site cohomology over `T` with small-site cohomology of `i_f^{-1}` into a
statement about `f_{small}^{-1}`. -/
@[stacks 021I "small-site factorization, inverse images"]
public def smallEtaleRestrictionProjectionPullbackIso :
    (SmallEtale.inclusion B S.obj S.property).sheafPullback A
        (SmallEtale.topology B S.obj S.property)
        (BigEtaleOver.topology B S.obj S.property) ⋙
      (smallEtaleToBigEtaleFunctor B T S f).sheafPushforwardContinuous A
        (SmallEtale.topology B T.obj T.property)
        (BigEtaleOver.topology B S.obj S.property) ≅
    (smallEtaleBaseChange B f).sheafPullback A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property) := by
  have : (SmallEtale.inclusion B T.obj T.property).IsCocontinuous
      (SmallEtale.topology B T.obj T.property)
      (BigEtaleOver.topology B T.obj T.property) :=
    smallEtaleInclusion_isCocontinuous B T.obj T.property
  haveI : IsIso ((SmallEtale.inclusion B T.obj T.property).sheafAdjunctionContinuous A
      (SmallEtale.topology B T.obj T.property)
      (BigEtaleOver.topology B T.obj T.property)).unit :=
    Functor.isIso_unit_of_sheafPushforwardContinuous
      (SmallEtale.inclusion B T.obj T.property) A
      (SmallEtale.topology B T.obj T.property)
      (BigEtaleOver.topology B T.obj T.property)
      ((SmallEtale.inclusion B T.obj T.property).sheafAdjunctionContinuous A
        (SmallEtale.topology B T.obj T.property)
        (BigEtaleOver.topology B T.obj T.property))
  exact Functor.isoWhiskerLeft _
      ((SmallEtale.inclusion B T.obj T.property).sheafPushforwardContinuousComp (Over.map f) A
        (SmallEtale.topology B T.obj T.property)
        (BigEtaleOver.topology B T.obj T.property)
        (BigEtaleOver.topology B S.obj S.property)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (bigEtalePullbackProjectionPullbackIso B T S f A) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (asIso ((SmallEtale.inclusion B T.obj T.property
      ).sheafAdjunctionContinuous A (SmallEtale.topology B T.obj T.property)
      (BigEtaleOver.topology B T.obj T.property)).unit).symm ≪≫
    Functor.rightUnitor _

end

/-! ### Abelian coefficients, and the derived comparison of Stacks 0DDH (3) -/

section Abelian

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts
attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-- `i_f^{-1}` preserves finite limits: being restriction along a continuous functor, it is a
right adjoint. -/
public instance smallEtaleRestrictionAlong_preservesFiniteLimits :
    PreservesFiniteLimits (smallEtaleRestriction B T S f) := by
  have := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smallEtaleToBigEtaleFunctor B T S f) Ab.{u + 1}
    (SmallEtale.topology B T.obj T.property)
    (BigEtaleOver.topology B S.obj S.property)).isRightAdjoint
  infer_instance

/-- `i_f^{-1}` preserves finite colimits: the functor presenting `i_f` is cocontinuous as well as
continuous, so restriction along it is also a sheaf pullback, hence a left adjoint. -/
public instance smallEtaleRestrictionAlong_preservesFiniteColimits :
    PreservesFiniteColimits (smallEtaleRestriction B T S f) := by
  have adj := (smallEtaleToBigEtaleFunctor B T S f).sheafAdjunctionPullbackCocontinuous
    Ab.{u + 1} (SmallEtale.topology B T.obj T.property)
    (BigEtaleOver.topology B S.obj S.property)
  have : PreservesFiniteColimits
      ((smallEtaleToBigEtaleFunctor B T S f).sheafPullbackCocontinuous Ab.{u + 1}
        (SmallEtale.topology B T.obj T.property)
        (BigEtaleOver.topology B S.obj S.property)) :=
    (adj.leftAdjoint_preservesColimits.{u + 1, u + 1}).preservesFiniteColimits
  exact preservesFiniteColimits_of_natIso
    ((smallEtaleToBigEtaleFunctor B T S f
        ).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
      Ab.{u + 1} (SmallEtale.topology B T.obj T.property)
      (BigEtaleOver.topology B S.obj S.property))

/-- **The derived functor of `i_f^{-1}` exists, and is the functor `i_f^{-1}` induces on the
unbounded derived categories.**  `i_f^{-1}` is exact
(`AlgebraicGeometry.smallEtaleRestrictionAlong_preservesFiniteLimits` and
`AlgebraicGeometry.smallEtaleRestrictionAlong_preservesFiniteColimits`), so the canonical
factorization `CategoryTheory.Functor.mapDerivedCategoryFactorsh` is an isomorphism and already
exhibits the induced functor as a right derived functor of the degreewise one; abelian sheaves on
the big étale site over `S` are a Grothendieck abelian category
(`AlgebraicGeometry.bigEtaleSheaf_isGrothendieckAbelian`), which is what makes
`DerivedCategory.Qh` a localization at the quasi-isomorphisms.

This is the same argument as
`Stacks.Cohomology.DerivedLowerShriek.isRightDerivedFunctor_derivedRestriction` for restriction
of sheaves of modules.  Its point here is that the existence of the derived functor of `i_f^{-1}`
is *not* an extra assumption on the site, so the clauses of Stacks 0DDH below do not carry it. -/
public instance hasRightDerivedFunctor_smallEtaleRestriction :
    ((smallEtaleRestriction B T S f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso
          (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1})
          (ComplexShape.up ℤ)) := by
  let : IsGrothendieckAbelian.{u + 1, u + 1, u + 2}
      (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1}) :=
    bigEtaleSheaf_isGrothendieckAbelian B S
  have e : DerivedCategory.Qh ⋙ (smallEtaleRestriction B T S f).mapDerivedCategory ≅
      (smallEtaleRestriction B T S f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh :=
    (smallEtaleRestriction B T S f).mapDerivedCategoryFactorsh
  have : (smallEtaleRestriction B T S f).mapDerivedCategory.IsRightDerivedFunctor e.inv
      (HomotopyCategory.quasiIso
        (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1})
        (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts
      (HomotopyCategory.quasiIso
        (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1})
        (ComplexShape.up ℤ)) _ e
  exact Functor.HasRightDerivedFunctor.mk'
    (L := DerivedCategory.Qh
      (C := Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1}))
    (RF := (smallEtaleRestriction B T S f).mapDerivedCategory) (α := e.inv)

/-- `π_S^{-1}` preserves finite limits, by exactness of the inverse image of the projection
(Stacks 0DDI). -/
public instance projectionPullback_preservesFiniteLimits :
    PreservesFiniteLimits (projectionPullback.{u, u + 1} B S.obj S.property) :=
  (projectionPullback_exact.{u, u + 1} B S.obj S.property).1

/-- `π_S^{-1}` preserves finite colimits, by exactness of the inverse image of the projection
(Stacks 0DDI). -/
public instance projectionPullback_preservesFiniteColimits :
    PreservesFiniteColimits (projectionPullback.{u, u + 1} B S.obj S.property) :=
  (projectionPullback_exact.{u, u + 1} B S.obj S.property).2

/-- `π_S^{-1}` is additive, being exact. -/
public instance projectionPullback_additive :
    (projectionPullback.{u, u + 1} B S.obj S.property).Additive :=
  (projectionPullback.{u, u + 1} B S.obj S.property).additive_of_preservesBinaryBiproducts

/-- The inverse image of abelian sheaves along `f_{small}`, that is `f_{small}^{-1}` at abelian
coefficients. -/
public abbrev smallEtaleAbelianInverseImage :
    Sheaf (SmallEtale.topology B S.obj S.property) Ab.{u + 1} ⥤
      Sheaf (SmallEtale.topology B T.obj T.property) Ab.{u + 1} :=
  (smallEtaleBaseChange B f).sheafPullback Ab.{u + 1}
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)

/-- `f_{small}^{-1}` preserves finite limits: small étale base change is representably flat, and
lower shriek on abelian sheaves along a representably flat continuous functor is left exact. -/
@[sga "5 VI 2.1" "left exactness of f*"]
public instance smallEtaleAbelianInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (smallEtaleAbelianInverseImage B T S f) :=
  Stacks.Sites.LowerShriek.preservesFiniteLimits_sheafPullback_of_representablyFlat.{u + 1}
    (smallEtaleBaseChange B f) (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)

/-- `f_{small}^{-1}` preserves finite colimits, being a left adjoint. -/
public instance smallEtaleAbelianInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits (smallEtaleAbelianInverseImage B T S f) :=
  ((((smallEtaleBaseChange B f).sheafAdjunctionContinuous Ab.{u + 1}
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)).leftAdjoint_preservesColimits.{u + 1,
      u + 1})).preservesFiniteColimits

/-- `f_{small}^{-1}` is additive, being exact. -/
public instance smallEtaleAbelianInverseImage_additive :
    (smallEtaleAbelianInverseImage B T S f).Additive :=
  (smallEtaleAbelianInverseImage B T S f).additive_of_preservesBinaryBiproducts

/-- **Stacks 0DDH, part (3).** Let `f : T ⟶ S` be a morphism of a big étale site and let `K` be
an unbounded complex of abelian sheaves on the small étale site of `S`. Cohomology over the
object `T ⟶ S` of the big étale site of `S` of the pullback `π_S^{-1}K` agrees with cohomology
on the small étale site of `T` of `f_{small}^{-1}K`, naturally in `K`:
`H^n_étale(T, π_S^{-1}K) = H^n(T_étale, f_{small}^{-1}K)`.

Both `π_S^{-1}` and `f_{small}^{-1}` are exact, so no derived functor of them intervenes: the
statement is between the two unbounded derived section functors precomposed with the functors the
two pullbacks induce on derived categories.

The proof is part (5), `AlgebraicGeometry.bigSmallEtaleCohomologyIso`, followed by
`AlgebraicGeometry.smallEtaleRestrictionProjectionPullbackIso`: the derived functor of the exact
`i_f^{-1}` is the functor it induces on derived categories, and composing that with `π_S^{-1}`'s
gives the one induced by `f_{small}^{-1}`. -/
@[stacks 0DDH "part (3)"]
public def bigSmallEtaleProjectionPullbackCohomologyIso :
    (projectionPullback.{u, u + 1} B S.obj S.property).mapDerivedCategory ⋙
      (((bigEtaleSections B T S f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1})
            (ComplexShape.up ℤ))) ≅
    (smallEtaleAbelianInverseImage B T S f).mapDerivedCategory ⋙
      (((Sheaf.Γ (SmallEtale.topology B T.obj T.property) Ab.{u + 1}).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (Sheaf (SmallEtale.topology B T.obj T.property) Ab.{u + 1})
            (ComplexShape.up ℤ))) := by
  let : IsGrothendieckAbelian.{u + 1, u + 1, u + 2}
      (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1}) :=
    bigEtaleSheaf_isGrothendieckAbelian B S
  let : IsGrothendieckAbelian.{u + 1, u + 1, u + 2}
      (Sheaf (SmallEtale.topology B T.obj T.property) Ab.{u + 1}) :=
    smallEtaleSheaf_isGrothendieckAbelian B T
  have hR : ((smallEtaleRestriction B T S f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1})
            (ComplexShape.up ℤ)) ≅
      (smallEtaleRestriction B T S f).mapDerivedCategory :=
    Functor.rightDerivedUnique _ _
      (((smallEtaleRestriction B T S f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1})
            (ComplexShape.up ℤ)))
      (smallEtaleRestriction B T S f).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso
        (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1})
        (ComplexShape.up ℤ))
  exact Functor.isoWhiskerLeft _ (bigSmallEtaleCohomologyIso B T S f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft _ hR ≪≫
        (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).symm ≪≫
        Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
          (smallEtaleRestrictionProjectionPullbackIso B T S f Ab.{u + 1})) _

/-- **Stacks 0DDH, part (1).** For an unbounded complex `K` of abelian sheaves on the small étale
site of `S`, cohomology of the pullback `π_S^{-1}K` on the big étale site of `S` agrees with
cohomology of `K` on the small étale site of `S`, naturally in `K`:
`H^n_étale(S, π_S^{-1}K) = H^n(S_étale, K)`.

This is part (3) at the identity morphism of `S`, where `f_{small}^{-1}` is the identity functor
by `AlgebraicGeometry.smallEtaleSheafPullbackIdIso` (Stacks 021J). -/
@[stacks 0DDH "part (1)"]
public def bigSmallEtaleProjectionPullbackCohomologyIsoSelf :
    (projectionPullback.{u, u + 1} B S.obj S.property).mapDerivedCategory ⋙
      (((bigEtaleSections B S S (𝟙 S)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1})
            (ComplexShape.up ℤ))) ≅
    (((Sheaf.Γ (SmallEtale.topology B S.obj S.property) Ab.{u + 1}).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (Sheaf (SmallEtale.topology B S.obj S.property) Ab.{u + 1})
          (ComplexShape.up ℤ))) :=
  bigSmallEtaleProjectionPullbackCohomologyIso B S S (𝟙 S) ≪≫
    Functor.isoWhiskerRight
      (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso
        (smallEtaleAbelianInverseImage B S S (𝟙 S))
        (𝟭 (Sheaf (SmallEtale.topology B S.obj S.property) Ab.{u + 1}))
        (smallEtaleSheafPullbackIdIso B S Ab.{u + 1}) ≪≫
        Stacks.Homology.mapDerivedCategoryIdIso) _ ≪≫
    Functor.leftUnitor _

/-- **Stacks 0DDH, part (5).** Let `f : T ⟶ S` be a morphism of a big étale site and let `M` be
an unbounded complex of abelian sheaves on the big étale site over `S`. Cohomology over the
object `T ⟶ S` of the big étale site of `S` agrees with cohomology on the small étale site of
`T` of the restriction `i_f^{-1}M`, naturally in `M`:
`H^n_étale(T, M) = H^n(T_étale, i_f^{-1}M)`.

This is `AlgebraicGeometry.bigSmallEtaleCohomologyIso` with nothing assumed: the three derived
functors in the statement exist, the derived functor of the exact `i_f^{-1}` by
`AlgebraicGeometry.hasRightDerivedFunctor_smallEtaleRestriction`, and the derived sections
functors `RΓ(T → S, -)` and `RΓ(T_étale, -)` by
`AlgebraicGeometry.hasRightDerivedFunctor_bigEtaleSections` and
`AlgebraicGeometry.hasRightDerivedFunctor_smallEtaleGlobalSections`, from the K-injective
resolutions of the two Grothendieck abelian categories of sheaves. -/
@[stacks 0DDH "part (5)"]
public def bigSmallEtaleDerivedSectionsIso :
    (((bigEtaleSections B T S f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1})
          (ComplexShape.up ℤ))) ≅
    ((((smallEtaleRestriction B T S f).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1})
          (ComplexShape.up ℤ))) ⋙
    (((Sheaf.Γ (SmallEtale.topology B T.obj T.property) Ab.{u + 1}).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (Sheaf (SmallEtale.topology B T.obj T.property) Ab.{u + 1})
          (ComplexShape.up ℤ)))) :=
  bigSmallEtaleCohomologyIso B T S f

end Abelian

end AlgebraicGeometry
