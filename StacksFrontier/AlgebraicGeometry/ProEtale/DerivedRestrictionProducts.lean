module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackUnivLE
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.WeaklyContractibleProducts
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleComplexes
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSections
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.ProetaleTestingFamily
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.Slice
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.SliceTestingFamily

/-!
# Countable products in `D(X_proét, Λ)` and restriction to an object of `X_proét`

Let `X` be a scheme and `Λ` a ring. Every object of `X_proét` is covered by weakly contractible
objects, so countable products of sheaves of modules over the constant coefficient ring sheaf
`\underline{Λ}` are exact (Stacks 0947 (4)), on `X_proét` and on each slice `X_proét/V`. Hence
countable products in `D(X_proét, Λ)` are computed termwise, and restriction to an object `V` of
`X_proét`, which is exact and commutes with products of sheaves, commutes with countable products
in the derived categories. In particular it carries derived limits `R lim Kₙ` to derived limits
(`NoetherianAdicCompletion.IsDerivedLimitWithProjections.map`).

## Main results

* `AlgebraicGeometry.ProEtale.hasExactLimitsOfShape_discrete_nat_modules`: countable products
  of sheaves of `\underline{Λ}`-modules on `X_proét` are exact.
* `AlgebraicGeometry.ProEtale.hasExactLimitsOfShape_discrete_nat_modules_over`: the same on the
  slice site over an object of `X_proét`.
* `AlgebraicGeometry.ProEtale.preservesLimitsOfShape_overRestrictionDerived`: restriction
  `D(X_proét, Λ) → D(X_proét/V, \underline{Λ}|_V)` preserves countable products.

## References

* [Stacks Project, Tag 0947](https://stacks.math.columbia.edu/tag/0947)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u r w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

-- The universe-polymorphic instance `hasSheafify_proetale_addCommGrpCat` asks instance search to
-- solve `max (u + 1) ?v` against the value universe `max (u + 1) r w` of the modules here, which
-- the universe unifier cannot do; the sheafification it would supply is found without it.
attribute [-instance] AlgebraicGeometry.ProEtale.hasSheafify_proetale_addCommGrpCat

variable (X : Scheme.{u}) (Λ : Type r) [CommRing Λ]

/-- Countable products of sheaves of modules over the constant coefficient ring sheaf on
`X_proét` are exact (Stacks 0947 (4)). -/
instance hasExactLimitsOfShape_discrete_nat_modules :
    HasExactLimitsOfShape (Discrete ℕ) (RingedSite.Modules.{u + 1, u, max (u + 1) r w}
      (constantCoefficientRingedSite.{u, r, w} X Λ)) :=
  let h := Scheme.ProEt.testingFamily.{max (u + 1) r w} X
  Stacks.SheafOfModules.WeaklyContractible.hasExactLimitsOfShape_discrete_nat.{max (u + 1) r w}
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (constantCoefficientRingedSite.{u, r, w} X Λ).O))
    h.B h.hasEnoughObjects fun _ hU _ _ φ hφ => h.surjective_app hU φ hφ

/-- Countable products of sheaves of modules over the restriction of the constant coefficient
ring sheaf to an object of `X_proét` are exact (Stacks 0947 (4)). -/
instance hasExactLimitsOfShape_discrete_nat_modules_over (V : X.ProEt) :
    HasExactLimitsOfShape (Discrete ℕ) (SheafOfModules.{max (u + 1) r w}
      (((Stacks.SheafOfModules.Tensor.ringSheaf
        (constantCoefficientRingedSite.{u, r, w} X Λ).O)).over V)) :=
  let h := Stacks.WeaklyContractible.SliceTestingFamily.over _
    (Scheme.ProEt.testingFamily.{max (u + 1) r w} X) V
  Stacks.SheafOfModules.WeaklyContractible.hasExactLimitsOfShape_discrete_nat.{max (u + 1) r w}
    (R := ((Stacks.SheafOfModules.Tensor.ringSheaf
      (constantCoefficientRingedSite.{u, r, w} X Λ).O)).over V)
    h.B h.hasEnoughObjects fun _ hU _ _ φ hφ => h.surjective_app hU φ hφ

/-- **Restriction to an object of `X_proét` commutes with countable products in the derived
categories.** The restriction of sheaves of modules to the slice site over `V` is exact and
commutes with products, and countable products are exact on both sites, so they are computed
termwise in both derived categories. -/
theorem preservesLimitsOfShape_overRestrictionDerived (V : X.ProEt) :
    PreservesLimitsOfShape (Discrete ℕ) (overRestrictionDerived.{u, r, w} X Λ V) := by
  let : PreservesFiniteLimits (SheafOfModules.overFunctor.{max (u + 1) r w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (constantCoefficientRingedSite.{u, r, w} X Λ).O)) V) :=
    SheafOfModules.preservesFiniteLimits_pushforward _
  let : PreservesFiniteColimits (SheafOfModules.overFunctor.{max (u + 1) r w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (constantCoefficientRingedSite.{u, r, w} X Λ).O)) V) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits.{u + 1, u,
      max (u + 1) r w} V
  let R := (Stacks.SheafOfModules.Tensor.ringSheaf (constantCoefficientRingedSite.{u, r, w} X Λ).O)
  have h1 : PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.forget.{max (u + 1) r w} R) :=
    inferInstance
  have : Small.{max (u + 1) r w} (Over V) := small_lift.{u + 1, max r w} _
  have : LocallySmall.{max (u + 1) r w} (Over V) := locallySmall_max.{max (u + 1) r w, u}
  have : LocallySmall.{max (u + 1) r w} X.ProEt := locallySmall_max.{max (u + 1) r w, u}
  have h2 : (PresheafOfModules.pushforward.{max (u + 1) r w} (F := (Over.forget V))
        ((sheafToPresheaf _ _).map (𝟙 (R.over V)))).IsRightAdjoint :=
    PresheafOfModules.isRightAdjoint_pushforward_of_univLE.{max (u + 1) r w} _
  have : PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.overFunctor.{max (u + 1) r w} R V ⋙
      SheafOfModules.forget _) :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.forget R ⋙
      PresheafOfModules.pushforward.{max (u + 1) r w} (F := (Over.forget V))
        ((sheafToPresheaf _ _).map (𝟙 (R.over V)))))
  have : PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.overFunctor.{max (u + 1) r w} R V) :=
    preservesLimitsOfShape_of_reflects_of_preserves _ (SheafOfModules.forget _)
  exact CategoryTheory.Functor.preservesProducts_mapDerivedCategory ℕ _

end AlgebraicGeometry.ProEtale
