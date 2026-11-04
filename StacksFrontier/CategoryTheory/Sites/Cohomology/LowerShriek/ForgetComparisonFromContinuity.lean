module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.AbelianAcyclicityFromContinuity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedForgetComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.ModuleDerivedLowerShriek
import StacksCore.Tactic.StacksAttribute

/-!
# The comparison of the two derived lower shrieks, for a continuous functor of sites

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites, let `g : Sh(C) ⟶ Sh(D)` be the
corresponding morphism of topoi, let `O_D` be a sheaf of rings on `D` and set `O_C = g^{-1}O_D`.
The warning of Stacks 07AE says that the square

```
D(Mod(O_C)) --Lg_!--> D(Mod(O_D))
    |                     |
  forget                forget
    v                     v
  D(Ab(C)) --Lg_!^{Ab}--> D(Ab(D))
```

does not commute, and that all one gets is a canonical natural transformation
`Lg_!^{Ab} ∘ forget ⟶ forget ∘ Lg_!`.

`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/ForgetComparison.lean` constructs that
transformation and characterises it uniquely, but under the acyclicity statement of Stacks 0794
for lower shriek of modules and under the existence of `Lg_!^{Ab}`. This file discharges both,
for a functor of sites continuous in the sense of Sites, Definition 00WV, and so carries the
tag. The two inputs are
`Stacks.Cohomology.DerivedLowerShriek.lowerShriekModules_acyclic` of
`ModuleDerivedLowerShriek.lean` and
`Stacks.Cohomology.DerivedLowerShriek.hasPointwiseLeftDerivedAbelianLowerShriek_of_continuous`
of `AbelianAcyclicityFromContinuity.lean`; both are that same acyclicity statement, for the
structure sheaf `O_D` and for the constant sheaf of integers respectively, and both are proved
there from Stacks 0D6X, hence from the covering-pullback clause
`Stacks.Sites.PreservesCoveringPullbacks` of continuity.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.existsUnique_derivedForgetComparison_of_continuous`:
  **Stacks 07AE**, the comparison transformation `Lg_!^{Ab} ∘ forget ⟶ forget ∘ Lg_!`, for a
  continuous and cocontinuous functor of sites.

## Implementation notes

This is a separate module rather than a section of `ForgetComparison.lean` because that file
states its declarations with the object and morphism universes of the two sites and the universe
of the module sections mutually free, while the instances of `AbelianDerivedExistence.lean` —
among them the additivity of lower shriek on abelian sheaves — are stated with the coefficient
universe containing the morphism universe of the source. Importing them into `ForgetComparison`
leaves the search for `Functor.Additive (lowerShriekAbelian J K f)` there stuck on a universe
constraint.

The two sites are small and their objects, morphisms and the module sections lie in one universe,
and the sheaf of rings is commutative, which is the setting of Stacks 07AC
(`Stacks.Cohomology.DerivedLowerShriek.derivedLowerShriek_spec`) and the setting in which the
acyclicity statement is available. The left adjoints of restriction of modules along `u` and
along the slice projections come from `AdjointExistence.lean`; the one for the slices has to be
named, instance search for it timing out.

## References

* [Stacks Project, Tag 07AE](https://stacks.math.columbia.edu/tag/07AE)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
* [Stacks Project, Tag 00WV](https://stacks.math.columbia.edu/tag/00WV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Cohomology.DerivedLowerShriek

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (f : C ⥤ D)
  [f.IsContinuous J K] [f.IsCocontinuous J K]
  [Stacks.Sites.PreservesCoveringPullbacks J f] (O : Sheaf K CommRingCat.{u})

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks Project, Tag 07AE.** Let `u : C ⥤ D` be a continuous and cocontinuous functor of
sites, let `g : Sh(C) ⟶ Sh(D)` be the corresponding morphism of topoi, let `O_D` be a sheaf of
rings on `D` and set `O_C = g^{-1}O_D`. There is exactly one natural transformation

`Lg_!^{Ab} ∘ forget ⟶ forget ∘ Lg_!`

compatible with the counits exhibiting the two functors as left derived functors and with the
comparison `g_!^{Ab} ∘ forget ⟶ forget ∘ g_!` of Stacks 0798.

That is all the warning allows: the undifferentiated functors already need not agree, which is
`Stacks.SheafOfModules.lowerShriekForget_not_isomorphic`, and the square commutes exactly when
the canonical maps `Lg_!^{Ab} j_{U!}O_U ⟶ j_{u(U)!}O_{u(U)}` are isomorphisms, which they need
not be. Uniqueness is what makes this *the* comparison of the warning rather than some
transformation between the two composites: a left derived functor is a right Kan extension along
the localization, so a transformation into `Lg_! ⋙ forget` is the same thing as one out of
`Q_h ⋙ (forget ⋙ Lg_!^{Ab})` into degreewise `g_! ⋙ forget` followed by `Q_h`, and the lift is
unique.

This is `existsUnique_derivedForgetComparison_of_acyclic` with its inputs discharged; see the
module docstring. The hypotheses are exactly those of Stacks 07AC: `[f.IsContinuous J K]` and
`[Stacks.Sites.PreservesCoveringPullbacks J f]` together are continuity of `u` in the sense of
Stacks 00WV, `[f.IsCocontinuous J K]` is cocontinuity, and `O` is the sheaf of rings `O_D`. The
acyclicity statement of Stacks 0794 that the conditional form takes as `hFP`, the left adjoints
`g_!` and `g_!^{Ab}` of restriction, and the existence of both derived functors are all found by
instance search from the instances proved in `ModuleDerivedLowerShriek.lean`,
`AbelianAcyclicityFromContinuity.lean` and `AdjointExistence.lean`; the transformation itself is
`derivedForgetComparison`. -/
@[stacks 07AE "the comparison transformation `Lg_!^{Ab} ∘ forget ⟶ forget ∘ Lg_!`, with no \
hypothesis beyond those of Stacks 07AC: continuity of u (Stacks 00WV) is `Functor.IsContinuous` \
with `Stacks.Sites.PreservesCoveringPullbacks`; the existence of `g_!`, `g_!^{Ab}`, `Lg_!` and \
`Lg_!^{Ab}` is proved, not assumed; the sites are small and the ring sheaf commutative, as in \
Stacks 07AC"]
theorem existsUnique_derivedForgetComparison_of_continuous :
    ∃! t : (forgetSourceModules J K f
          (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).mapDerivedCategory ⋙
        derivedLowerShriekAbelian J K f ⟶
      derivedLowerShriek J K f (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O) ⋙
        (forgetTargetModules K
          (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).mapDerivedCategory,
      Functor.whiskerLeft DerivedCategory.Qh t ≫
          derivedLowerShriekForgetCounit J K f
            (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O) =
        derivedForgetComparisonCounit J K f
          (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O) := by
  have : ∀ V : C, Functor.IsRightAdjoint
      (_root_.SheafOfModules.pushforward.{u} (F := Over.forget V)
        (𝟙 ((inverseImageRing J K f
          (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).over V))) :=
    fun V => Stacks.Sites.ExtensionByZero.sheafRestrictionIsRightAdjoint_of_univLE.{u}
      J (inverseImageRing J K f (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) V
  exact existsUnique_derivedForgetComparison_of_acyclic J K f _
    (lowerShriekModules_acyclic J K f O)

end Stacks.Cohomology.DerivedLowerShriek

end
