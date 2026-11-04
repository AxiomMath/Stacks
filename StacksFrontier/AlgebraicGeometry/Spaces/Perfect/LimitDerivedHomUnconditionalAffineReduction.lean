module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtensionByZeroBaseChangeIsoLimitSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomUnconditionalPullbackData
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitSystemColimEtaleInduction

/-!
# Stacks 09RI reduced to the colimit statement over an affine base

In Situation 09RH let `E₀` and `K₀` be objects of `D(𝒪_{X₀})`.  The dévissage of Stacks 09RI is
closed in `StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitSystemColimEtaleInduction.lean`:
`AlgebraicGeometry.Space.DescentSituation.isColim_of_affine` derives the conclusion of the tag
from the predicate `AlgebraicGeometry.Space.DescentSituation.ExtendRestrictIsColim` at every
étale `u : U ⟶ X₀` with `U` affine, that is from the colimit statement for `u_!(u^*E₀)` at every
shift.  The reduction of *that* to a statement over `U` is closed in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ExtensionByZeroBaseChangeIsoLimitSystem.lean`:
`AlgebraicGeometry.Space.DescentSituation.isColim_lowerShriek_of_baseChangeSystem` derives the
colimit statement for `(u_!A, K₀)` on the system of `X₀` from the colimit statement for
`(A, Lu^*K₀)` on the base-changed system of the fibre products `U_i = X_i ×_{X₀} U` over `U`.

The two did not meet: the first is stated for the pullback-pseudofunctor datum
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`, the second for
`AlgebraicGeometry.Space.canonicalPullbackData`, and the identification of their composition
comparisons was open.  It is now
`AlgebraicGeometry.Space.isColim_canonicalPullbackData_iff`, and this file joins the two halves.

What results is **Stacks 09RI reduced to its affine case over an affine base**: the conclusion of
the tag, for the given `E₀` and `K₀`, from the single hypothesis that for every étale
`u : U ⟶ X₀` with `U` affine and every `n` the map

`colim_{i ≥ 0} Hom_{D(𝒪_{U_i})}(Lf_i'^*((u^*E₀)⟦n⟧), Lf_i'^*(Lu^*K₀)) ⟶`
`  Hom_{D(𝒪_{X ×_{X₀} U})}(…)`

is bijective, `U_i = X_i ×_{X₀} U`.  That is the leaf of the source's induction, at the point
where the source invokes the scheme-level Stacks 09RE through the comparison of the small étale
and the Zariski site.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.extendRestrictIsColim_of_baseChangeSystem`: the
  predicate of the dévissage at `u`, from the colimit statement on the base-changed system
  over `U`.
* `AlgebraicGeometry.Space.DescentSituation.isColim_of_affineBaseChange` and
  `isHomColimit_canonicalDerivedPullbackSystem_of_affineBaseChange`: **the conclusion of
  Stacks 09RI from the colimit statement over the affine objects étale over `X₀`**, in the two
  equivalent forms.

## The hypothesis carried, and why it is not a weakening

`hleaf` is the affine case of the source's own proof, which this library does not have: Stacks
09RE is proved (`AlgebraicGeometry.DescentSituation.isHomColimit`) for *schemes*, and carrying it
across the equivalence of Stacks 071Q to the small étale site of the affine `U` — together with
the dictionary of Stacks 08HE, 08HF and 08HG, all three of which are now available in both
directions — is not done anywhere in the tree.  No `@[stacks 09RI]` attribute is placed below:
the statements here are conditional, and the tag belongs only on an unconditional one.

Nothing else is assumed.  No universe restriction is incurred here; both of the tag's live in the
affine case, as the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitSystemColimEtaleInduction.lean` records.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Lemma 36.29.2 (Tag 09RE)](https://stacks.math.columbia.edu/tag/09RE)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe v u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits etaleModuleLowerShriek_additive
  preservesFiniteLimits_etaleModuleLowerShriek preservesFiniteColimits_etaleModuleLowerShriek

namespace DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  {D : DescentSituation B S hS hZ I} {U : AlgebraicSpaces B S hS}

/-- **The predicate of the dévissage of Stacks 09RI at an étale `u : U ⟶ X₀`, from the colimit
statement on the base-changed system over `U`.**

For each shift `n` the colimit statement for `(u^*E₀)⟦n⟧` against `Lu^*K₀` on the system of the
fibre products `U_i = X_i ×_{X₀} U` gives, by
`AlgebraicGeometry.Space.DescentSituation.isColim_lowerShriek_of_baseChangeSystem`, the colimit
statement for `u_!((u^*E₀)⟦n⟧)` against `K₀` on the system of `X₀`; and `u_!` commutes with the
shift, so that object is `(u_!(u^*E₀))⟦n⟧`. -/
theorem extendRestrictIsColim_of_baseChangeSystem (E₀ K₀ : derivedModules B S hS (D.stage D.base))
    (u : U ⟶ D.stage D.base) (hu : IsEtale B S hS u.hom)
    (hU : ∀ n : ℤ, (baseChangeSystem u).IsColim (smallEtaleDerivedPullbackData B S hS)
      (((etaleModulePullback.{u, u} B S hS u hu).mapDerivedCategory.obj E₀)⟦n⟧)
      ((smallEtaleDerivedModulePullback B S hS u).obj K₀)) :
    D.ExtendRestrictIsColim E₀ K₀ u hu := by
  intro n
  refine PullbackData.LimitSystem.IsColim.of_iso_fst
    (smallEtaleDerivedPullbackData_isCoherent B S hS)
    ((((etaleModuleLowerShriek B S hS u hu).mapDerivedCategory.commShiftIso n).app
        ((etaleModulePullback.{u, u} B S hS u hu).mapDerivedCategory.obj E₀)) ≪≫
      (shiftFunctor (derivedModules B S hS (D.stage D.base)) n).mapIso
        ((Dualizing.mapDerivedCategoryComp (etaleModulePullback.{u, u} B S hS u hu)
          (etaleModuleLowerShriek B S hS u hu)).app E₀).symm)
    ((isColim_canonicalPullbackData_iff D.limitSystem _ K₀).1 ?_)
  exact isColim_lowerShriek_of_baseChangeSystem u hu _ K₀
    ((isColim_canonicalPullbackData_iff (baseChangeSystem u) _ _).2 (hU n))

/-- **Stacks 09RI, reduced to the colimit statement over the affine objects étale over `X₀`.**
In Situation 09RH, if for every étale `u : U ⟶ X₀` with `U` affine and every shift `n` the map

`colim_{i ≥ 0} Hom_{D(𝒪_{U_i})}(Lf_i'^*((u^*E₀)⟦n⟧), Lf_i'^*(Lu^*K₀)) ⟶`
`  Hom_{D(𝒪_{X ×_{X₀} U})}(…)`

is bijective, where `U_i = X_i ×_{X₀} U`, then

`colim_{i ≥ 0} Hom_{D(𝒪_{X_i})}(Lf_{i0}^*E₀, Lf_{i0}^*K₀) ⟶ Hom_{D(𝒪_X)}(Lf_0^*E₀, Lf_0^*K₀)`

is bijective. -/
theorem isColim_of_affineBaseChange (E₀ K₀ : derivedModules B S hS (D.stage D.base))
    (hleaf : ∀ {V : AlgebraicSpaces B S hS} (u : V ⟶ D.stage D.base)
      (hu : IsEtale B S hS u.hom), IsAffineSpace B S hS V.1 → ∀ n : ℤ,
        (baseChangeSystem u).IsColim (smallEtaleDerivedPullbackData B S hS)
          (((etaleModulePullback.{u, u} B S hS u hu).mapDerivedCategory.obj E₀)⟦n⟧)
          ((smallEtaleDerivedModulePullback B S hS u).obj K₀)) :
    D.limitSystem.IsColim (smallEtaleDerivedPullbackData B S hS) E₀ K₀ :=
  isColim_of_affine E₀ K₀ fun u hu hV ↦
    extendRestrictIsColim_of_baseChangeSystem E₀ K₀ u hu (hleaf u hu hV)

/-- **The conclusion of Stacks 09RI for the canonical system of derived pullbacks, reduced to
the colimit statement over the affine objects étale over `X₀`.** -/
theorem isHomColimit_canonicalDerivedPullbackSystem_of_affineBaseChange
    (E₀ K₀ : derivedModules B S hS (D.stage D.base))
    (hleaf : ∀ {V : AlgebraicSpaces B S hS} (u : V ⟶ D.stage D.base)
      (hu : IsEtale B S hS u.hom), IsAffineSpace B S hS V.1 → ∀ n : ℤ,
        (baseChangeSystem u).IsColim (smallEtaleDerivedPullbackData B S hS)
          (((etaleModulePullback.{u, u} B S hS u hu).mapDerivedCategory.obj E₀)⟦n⟧)
          ((smallEtaleDerivedModulePullback B S hS u).obj K₀)) :
    IsHomColimit D.canonicalDerivedPullbackSystem E₀ K₀ :=
  (isHomColimit_canonicalDerivedPullbackSystem_iff D E₀ K₀).2
    (isColim_of_affineBaseChange E₀ K₀ hleaf)

end DescentSituation

end AlgebraicGeometry.Space

end
