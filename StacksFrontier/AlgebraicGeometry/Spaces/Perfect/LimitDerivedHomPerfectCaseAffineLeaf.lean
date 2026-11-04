module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomUnconditionalAffineReduction
public import StacksFrontier.CategoryTheory.PullbackData.LimitDerivedHomPerfectCaseSummand

/-!
# The affine leaf of Stacks 09RI, as a dévissage-ready predicate in its first argument

The dévissage of Stacks 09RI is closed:
`AlgebraicGeometry.Space.DescentSituation.isColim_of_affineBaseChange` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitDerivedHomUnconditionalAffineReduction.lean`
derives the conclusion of the tag from the colimit statement on the base-changed system
`U_i = X_i ×_{X₀} U` over the affine objects `u : U ⟶ X₀` of the small étale site, for the first
argument `Lu^*E₀` and *every* shift of it.

That hypothesis is literally
`CategoryTheory.PullbackData.LimitSystem.ShiftedIsColim` — the predicate whose closure
properties are proved in
`StacksFrontier/CategoryTheory/PullbackData/LimitSystemColimShift.lean` (isomorphism, shift, the
three vertices of a distinguished triangle, binary biproducts) and in
`StacksFrontier/CategoryTheory/PullbackData/LimitDerivedHomPerfectCaseSummand.lean` (direct
summands).  Reading it that way is what lets those closure lemmas be applied to the leaf
without unfolding anything, and that is all this file does: it restates the reduction with its
hypothesis spelled as `ShiftedIsColim`, and records the two consequences a dévissage of a
perfect `Lu^*E₀` immediately wants — that the leaf statement descends to a direct summand of an
object that satisfies it, and to a summand presented by an isomorphism `A ⊞ A' ≅ C`.

## What the dévissage still lacks

With these the class of first arguments satisfying the leaf statement is closed under
isomorphism, shift, extensions in a distinguished triangle, finite biproducts and direct
summands — every operation a dévissage of a perfect object over an affine base performs on it.
What is missing is the **base case**: the leaf statement for the structure sheaf `𝒪_U` itself,
that is, the bijectivity of
`colim_i Hom_{D(𝒪_{U_i})}(𝒪_{U_i}, (Lu^*K₀)_i⟦n⟧) ⟶ Hom_{D(𝒪_{U})}(𝒪_U, (Lu^*K₀)⟦n⟧)`
for `K₀` in `D_QCoh(𝒪_{X₀})` and `U`, the `U_i` and their limit all affine (which they are, by
`AlgebraicGeometry.Space.DescentSituation.isAffineSpace_baseChangeStage` and
`isAffineSpace_baseChangeLimit`).  That is the geometric input of the source, and it is where
the tag's two universe restrictions live; nothing in this file supplies it.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.isColim_of_shiftedIsColim_affineBaseChange`: the
  reduction of Stacks 09RI to the affine leaf, with the leaf hypothesis read as
  `CategoryTheory.PullbackData.LimitSystem.ShiftedIsColim`.
* `AlgebraicGeometry.Space.DescentSituation.shiftedIsColim_baseChangeSystem_of_retract` and
  `shiftedIsColim_baseChangeSystem_of_biprod_iso`: the leaf statement passes to a direct summand
  of its first argument.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
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

/-- **Stacks 09RI, reduced to the affine leaf, with the leaf hypothesis read as
`CategoryTheory.PullbackData.LimitSystem.ShiftedIsColim`.**

This is `AlgebraicGeometry.Space.DescentSituation.isColim_of_affineBaseChange` verbatim: the
hypothesis there is `∀ n : ℤ, _.IsColim _ (X⟦n⟧) Y`, which is the definition of
`ShiftedIsColim`.  Stating it this way is what makes the closure lemmas of
`CategoryTheory.PullbackData.LimitSystem.ShiftedIsColim` — `of_iso`, `shift`, `obj₁`, `obj₂`,
`obj₃`, `biprod`, `of_retract` — apply to the leaf as they stand. -/
theorem isColim_of_shiftedIsColim_affineBaseChange
    (E₀ K₀ : derivedModules B S hS (D.stage D.base))
    (hleaf : ∀ {V : AlgebraicSpaces B S hS} (u : V ⟶ D.stage D.base)
      (hu : IsEtale B S hS u.hom), IsAffineSpace B S hS V.1 →
        PullbackData.LimitSystem.ShiftedIsColim (baseChangeSystem u)
          (smallEtaleDerivedPullbackData B S hS)
          ((etaleModulePullback.{u, u} B S hS u hu).mapDerivedCategory.obj E₀)
          ((smallEtaleDerivedModulePullback B S hS u).obj K₀)) :
    D.limitSystem.IsColim (smallEtaleDerivedPullbackData B S hS) E₀ K₀ :=
  isColim_of_affineBaseChange E₀ K₀ fun u hu hV ↦ hleaf u hu hV

/-- **The leaf statement of Stacks 09RI passes to a direct summand of its first argument.**  If
`A` is a retract of `C` and the colimit statement on the base-changed system holds at every
shift for `C`, it holds at every shift for `A`.

Over an affine base this is the step a dévissage of a perfect object cannot do without: there a
finite projective module is a summand of a finite free one and not in general free, so the
closure of the class of first arguments under finite biproducts
(`CategoryTheory.PullbackData.LimitSystem.ShiftedIsColim.biprod`) does not reach it. -/
theorem shiftedIsColim_baseChangeSystem_of_retract (u : U ⟶ D.stage D.base)
    {A C K : derivedModules B S hS U} (h : Retract A C)
    (hC : PullbackData.LimitSystem.ShiftedIsColim (baseChangeSystem u)
      (smallEtaleDerivedPullbackData B S hS) C K) :
    PullbackData.LimitSystem.ShiftedIsColim (baseChangeSystem u)
      (smallEtaleDerivedPullbackData B S hS) A K :=
  hC.of_retract (smallEtaleDerivedPullbackData_isCoherent B S hS) h

/-- **The leaf statement of Stacks 09RI passes to a summand presented by an isomorphism
`A ⊞ A' ≅ C`**, the form in which a dévissage over an affine base meets it. -/
theorem shiftedIsColim_baseChangeSystem_of_biprod_iso (u : U ⟶ D.stage D.base)
    {A A' C K : derivedModules B S hS U} (e : A ⊞ A' ≅ C)
    (hC : PullbackData.LimitSystem.ShiftedIsColim (baseChangeSystem u)
      (smallEtaleDerivedPullbackData B S hS) C K) :
    PullbackData.LimitSystem.ShiftedIsColim (baseChangeSystem u)
      (smallEtaleDerivedPullbackData B S hS) A K :=
  PullbackData.LimitSystem.ShiftedIsColim.of_biprod_iso
    (smallEtaleDerivedPullbackData_isCoherent B S hS) e hC

end DescentSituation

end AlgebraicGeometry.Space

end
