module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.Algebra.Homology.DerivedFunctorLongExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedImmersionSupportedDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupportShortExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.HigherDirectImage
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef
public import StacksFrontier.Homology.CompositeCollapse
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The identifications behind the long exact sequence of cohomology with support

Let `i : Z ⟶ X` be a closed immersion of schemes and `j : U ⟶ X` the inclusion of the open
complement.  The long exact sequence of [Stacks, Tag 0A45] is the long exact sequence of right
derived functors of the short complex of endofunctors of `X_étale`

`i_*ℋ_Z ⟶ 𝟭 ⟶ j_*(-|_U)`

of `AlgebraicGeometry.supportedSectionsShortComplex`, which is short exact at every injective
abelian sheaf by `AlgebraicGeometry.supportedSectionsShortComplex_shortExact_of_injective`.
This file proves the left exactness of `ℋ_Z` and `i_*ℋ_Z`, identifies the three derived functors
in degree zero with the functors themselves, and identifies the right derived functors of the
two composites:

* `R^n(i_* ∘ ℋ_Z) ≅ i_* ∘ R^n ℋ_Z`, because `i_*` is exact;
* `R^n(j_* ∘ j^{-1}) ≅ (R^n j_*) ∘ j^{-1}`, because `j^{-1}` is exact and preserves injectives.

## Main results

* `AlgebraicGeometry.supportedSections_preservesFiniteLimits` and
  `AlgebraicGeometry.supportedSectionsPushforward_preservesFiniteLimits` — `ℋ_Z` and `i_*ℋ_Z`
  are left exact.
* `CategoryTheory.isZero_rightDerived_id_obj` — the higher right derived functors of the
  identity functor vanish.
* `CategoryTheory.rightDerived_zero_comp_rightDerivedZeroIsoSelf` — the degree-zero right
  derived functor of a natural transformation of left exact functors is the transformation
  itself, under `CategoryTheory.Functor.rightDerivedZeroIsoSelf`.
* `AlgebraicGeometry.supportedSectionsPushforwardRightDerivedIso` and
  `AlgebraicGeometry.complementRestrictPushRightDerivedIso` — the two identifications above.
* `AlgebraicGeometry.exists_longExact_supportedSections` — the long exact sequence of right
  derived functors of the short complex of endofunctors.

## References

* [Stacks Project, Tag 0A45](https://stacks.math.columbia.edu/tag/0A45)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u u₁ u₂

namespace CategoryTheory

variable {A : Type*} [Category* A] [Abelian A] [HasInjectiveResolutions A]
  {A' : Type u₁} [Category.{v} A'] [Abelian A'] [HasInjectiveResolutions A']

/-- **The higher right derived functors of the identity functor vanish**: `R^(n+1) 𝟭 = 0`. -/
public theorem isZero_rightDerived_id_obj (F : A) (n : ℕ) :
    IsZero (((𝟭 A).rightDerived (n + 1)).obj F) :=
  Functor.isZero_rightDerived_of_exact (𝟭 A) F (n + 1) n.succ_pos

variable {Bc : Type u₂} [Category.{v} Bc] [Abelian Bc]

/-- **The degree-zero right derived functor of a natural transformation of left exact functors
is the transformation itself.**  For additive left exact `T S : A' ⥤ Bc` and `τ : T ⟶ S`, the
isomorphisms `CategoryTheory.Functor.rightDerivedZeroIsoSelf` carry
`NatTrans.rightDerived τ 0` to `τ`. -/
public theorem rightDerived_zero_comp_rightDerivedZeroIsoSelf {T S : A' ⥤ Bc} [T.Additive]
    [S.Additive] [PreservesFiniteLimits T] [PreservesFiniteLimits S] (τ : T ⟶ S) :
    NatTrans.rightDerived τ 0 ≫ S.rightDerivedZeroIsoSelf.hom =
      T.rightDerivedZeroIsoSelf.hom ≫ τ := by
  rw [← cancel_epi T.toRightDerivedZero, ← Category.assoc,
    ← ModuleSheafCohomology.toRightDerivedZero_naturality_functor τ]
  simp

end CategoryTheory

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {Z X : B.Scheme} (i : Z ⟶ X)
  [IsClosedImmersion (B.inclusion.map i)]

/-! ### Left exactness of the two composites -/

/-- **`ℋ_Z` is left exact.** -/
@[sga "4 V 6.3" "special case"]
public instance supportedSections_preservesFiniteLimits :
    PreservesFiniteLimits (supportedSections B i) :=
  haveI : PreservesLimitsOfSize.{0, 0} (supportedSections B i) :=
    (supportedSectionsAdjunction B i).rightAdjoint_preservesLimits
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- **`F ↦ i_*ℋ_Z(F)` is left exact.** -/
@[sga "4 V 6.3" "special case"]
public instance supportedSectionsPushforward_preservesFiniteLimits :
    PreservesFiniteLimits (supportedSectionsPushforward B i) :=
  haveI : PreservesLimitsOfSize.{0, 0}
      ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B Z.obj Z.property)) :=
    ((smallEtaleBaseChange B i).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B Z.obj Z.property)).rightAdjoint_preservesLimits
  haveI : PreservesFiniteLimits
      ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B Z.obj Z.property)) :=
    PreservesLimitsOfSize.preservesFiniteLimits _
  comp_preservesFiniteLimits _ _

/-! ### The degree-zero identifications -/

/-- **`R⁰(i_*ℋ_Z) ≅ i_*ℋ_Z`**, the functor being left exact. -/
public abbrev supportedSectionsPushforwardRightDerivedZeroIso :
    (supportedSectionsPushforward B i).rightDerived 0 ≅ supportedSectionsPushforward B i :=
  (supportedSectionsPushforward B i).rightDerivedZeroIsoSelf

/-- **`R⁰(j_*(-|_U)) ≅ j_*(-|_U)`**, the functor being left exact. -/
public abbrev complementRestrictPushRightDerivedZeroIso :
    (complementRestrictPush B i).rightDerived 0 ≅ complementRestrictPush B i :=
  (complementRestrictPush B i).rightDerivedZeroIsoSelf

/-- **In degree zero the derived map `R⁰(i_*ℋ_Z) ⟶ R⁰𝟭` is the canonical map
`i_*ℋ_Z(F) ⟶ F`.** -/
public theorem rightDerived_supportedSectionsPushforwardInclusion_zero :
    NatTrans.rightDerived (supportedSectionsPushforwardInclusion B i) 0 ≫
        (𝟭 (SmallEtaleAbelianSheaf B X)).rightDerivedZeroIsoSelf.hom =
      (supportedSectionsPushforward B i).rightDerivedZeroIsoSelf.hom ≫
        supportedSectionsPushforwardInclusion B i :=
  rightDerived_zero_comp_rightDerivedZeroIsoSelf (supportedSectionsPushforwardInclusion B i)

/-- **In degree zero the derived map `R⁰𝟭 ⟶ R⁰(j_*(-|_U))` is the restriction map
`F ⟶ j_*(F|_U)`.** -/
public theorem rightDerived_complementRestriction_zero :
    NatTrans.rightDerived (complementRestriction B i) 0 ≫
        (complementRestrictPush B i).rightDerivedZeroIsoSelf.hom =
      (𝟭 (SmallEtaleAbelianSheaf B X)).rightDerivedZeroIsoSelf.hom ≫
        complementRestriction B i :=
  rightDerived_zero_comp_rightDerivedZeroIsoSelf (complementRestriction B i)

/-! ### `i_*` passes through the derived functor of `ℋ_Z` -/

/-- Direct image of abelian sheaves along a closed immersion preserves homology. -/
public instance smallEtalePushforward_preservesHomology_ab :
    ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B Z.obj Z.property)).PreservesHomology :=
  haveI := (exactFunctor_iff _).1 (smallEtalePushforward_exact_ab B i)
  haveI : PreservesFiniteLimits
      ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B Z.obj Z.property)) := ‹_ ∧ _›.1
  haveI : PreservesFiniteColimits
      ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B Z.obj Z.property)) := ‹_ ∧ _›.2
  Functor.preservesHomologyOfExact _

/-- **`R^n(i_* ∘ ℋ_Z) ≅ i_* ∘ R^n ℋ_Z`.** -/
public def supportedSectionsPushforwardRightDerivedIso (n : ℕ) :
    (supportedSectionsPushforward B i).rightDerived n ≅
      (supportedSections B i).rightDerived n ⋙
        (smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B Z.obj Z.property) :=
  Functor.rightDerivedCompIso (supportedSections B i)
    ((smallEtaleBaseChange B i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B Z.obj Z.property)) n

/-! ### The derived functor of `j_*(-|_U)` is `R^n j_*` after restriction -/

/-- Every abelian sheaf on `X_étale` is acyclic for restriction to the open complement. -/
public theorem acyclic_complementPullback (F : SmallEtaleAbelianSheaf B X) :
    Stacks.RightDerivedComp.acyclic
      (SmallEtale.openRestriction.{u, u + 1} B (closedComplementInclusion B i)) F :=
  fun n hn => Functor.isZero_rightDerived_of_exact _ F n hn

/-- **`R^n(j_* ∘ j^{-1}) ≅ (R^n j_*) ∘ j^{-1}`.** -/
public def complementRestrictPushRightDerivedIso (n : ℕ) :
    (complementRestrictPush B i).rightDerived n ≅
      SmallEtale.openRestriction.{u, u + 1} B (closedComplementInclusion B i) ⋙
        (Stacks.HigherDirectImage.pushforward.{u, u + 1} B
          (closedComplementInclusion B i)).rightDerived n :=
  haveI := preservesInjectiveObjects_complementPullback B i
  NatIso.ofComponents
    (fun F => Stacks.RightDerivedComp.objIso
      (SmallEtale.openRestriction.{u, u + 1} B (closedComplementInclusion B i))
      (injectiveResolution F) (acyclic_complementPullback B i F)
      (Stacks.HigherDirectImage.pushforward.{u, u + 1} B (closedComplementInclusion B i)) n)
    fun {F F'} g => Stacks.RightDerivedComp.objIso_hom_naturality _ _ n
      (acyclic_complementPullback B i F) (acyclic_complementPullback B i F') g

/-! ### The long exact sequence -/

/-- **The long exact sequence of right derived functors of the short complex of endofunctors
`i_*ℋ_Z ⟶ 𝟭 ⟶ j_*(-|_U)`** of abelian sheaves on `X_étale` ([Stacks, Tag 0A45]): there is a
connecting natural transformation `R^n(j_*(-|_U)) ⟶ R^(n+1)(i_*ℋ_Z)` for which the sequence

`0 ⟶ R⁰(i_*ℋ_Z) ⟶ R⁰𝟭 ⟶ R⁰(j_*(-|_U)) ⟶ R¹(i_*ℋ_Z) ⟶ R¹𝟭 ⟶ ⋯`

is exact at every abelian sheaf. -/
@[sga "4 VIII 6.5" "partial"]
public theorem exists_longExact_supportedSections :
    ∃ delta : ∀ n : ℕ, (complementRestrictPush B i).rightDerived n ⟶
        (supportedSectionsPushforward B i).rightDerived (n + 1),
      (∀ F : SmallEtaleAbelianSheaf B X,
          Mono ((NatTrans.rightDerived (supportedSectionsPushforwardInclusion B i) 0).app F)) ∧
        ∀ (n : ℕ) (F : SmallEtaleAbelianSheaf B X), (ComposableArrows.mk₅
          ((NatTrans.rightDerived (supportedSectionsPushforwardInclusion B i) n).app F)
          ((NatTrans.rightDerived (complementRestriction B i) n).app F)
          ((delta n).app F)
          ((NatTrans.rightDerived (supportedSectionsPushforwardInclusion B i) (n + 1)).app F)
          ((NatTrans.rightDerived (complementRestriction B i) (n + 1)).app F)).Exact :=
  longExact_rightDerived_of_shortExact_on_injectives
    (supportedSectionsPushforwardInclusion B i) (complementRestriction B i)
    (supportedSectionsPushforwardInclusion_comp_complementRestriction B i)
    fun I hI => have := hI; supportedSectionsShortComplex_shortExact_of_injective B i I

end AlgebraicGeometry

end
