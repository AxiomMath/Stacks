module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.ModuleHigherVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedLimitOfTruncations
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.RightDerivedSectionsEssentiallySmall

/-!
# The affine acyclicity carried by Stacks 08IY, reduced to abelian sheaf cohomology

`AlgebraicGeometry.Stack.HasAffineAcyclicLqcFbcModules` is the vanishing

`R^i Γ(x, ℱ) = 0` for `i > 0`, `ℱ` in `LQCoh^fbc(𝒪_𝒳)` and `x` an object of `𝒳_fppf` lying over
an affine scheme,

carried as an explicit hypothesis by the statements of **Stacks 08IY**, **Stacks 08IZ** and
**Stacks 075R** in this repository.  There `R^i Γ(x, -)` is the `i`-th right derived functor of
`CategoryTheory.SheafOfModules.evaluation` at `x`, so the vanishing is a statement about
*module-valued* cohomology, whereas each of the four results the source cites for it —
**Stacks 075F**, **Stacks 0756**, **Stacks 03DW** and **Stacks 01XB** — is a statement about
*abelian sheaf* cohomology.

This file performs that one change of level.  Given the vanishing of
`CategoryTheory.Sheaf.H'` on the underlying abelian sheaf of every module in `LQCoh^fbc(𝒪_𝒳)`
over every object lying over an affine scheme, the carried hypothesis follows.  So the hypothesis
`hvan` of `AlgebraicGeometry.Stack.exists_isDerivedLimit_truncGETower_of_lqcFbc` is equivalent
to — in fact weaker than — an abelian-sheaf statement, and the four cited results can be aimed
at it directly, with no module-level comparison left to construct.

## Main results

* `AlgebraicGeometry.Stack.hasAffineAcyclicLqcFbcModules_of_isZero_sheafCohomology`: the change
  of level.  The module-valued affine acyclicity follows from the abelian-sheaf one.
* `AlgebraicGeometry.Stack.exists_isDerivedLimit_truncGETower_of_isZero_sheafCohomology`:
  **Stacks 08IY** with its carried hypothesis replaced by the abelian-sheaf vanishing.
* `AlgebraicGeometry.Stack.enoughInjectives_fppfSiteSheaf_of_essentiallySmall`: one of the
  instance hypotheses below is satisfiable on an essentially small site, which the fppf site of
  a category fibred in groupoids over an essentially small site is.  The remaining five are
  exhibited at the same data in
  `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/AffineAcyclicityHypothesesInhabited.lean`,
  so that the reduction below is not a statement about an empty class.

## What this does and does not settle

The abelian-sheaf vanishing is not proved in this file.  For an essentially small category
fibred in groupoids it is proved, by the Čech argument of
`AlgebraicGeometry.Stack.isZero_sheafCohomology_of_isLocallyQuasicoherent`, and the
module-valued vanishing follows as `AlgebraicGeometry.Stack.hasAffineAcyclicLqcFbcModules`; the
resulting statement of Stacks 08IY is
`AlgebraicGeometry.Stack.exists_isDerivedLimit_truncGETower_of_lqcFbc_algebraicStack`.
What this file records is that at the hom universe of the site of schemes no comparison between
module-valued and abelian-sheaf cohomology over an object remains to be built, because
`Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_evaluation_of_isZero_H'`
already provides it at a site whose objects may live above its morphisms.

## Implementation notes

The hom universe of the site is the module universe `u`.  That is what the comparison
`Stacks.Cohomology.ObjectSections.subsingleton_rightDerived_evaluation` requires: it corepresents
sections over an object by an object of `Mod(𝒪_𝒳)` whose `Ext`-groups are computed in
`CategoryTheory.Abelian.Ext` at the morphism universe of the sheaf category, and the ring and
module sections must both sit in the hom universe of the site for that corepresentation to
typecheck.  The configuration is the one of
`AlgebraicGeometry.BigFppfOver`, whose objects lie in `Type (u + 1)` and whose morphisms lie in
`Type u`, which is also that of an object of `AlgebraicGeometry.Stack.AlgebraicStacks`.  It is not
the configuration of `AlgebraicGeometry.Stack.exists_isDerivedLimit_truncGETower_of_lqcFbc'`,
whose site has its morphisms in `Type (u + 1)`, so this reduction does not apply there.

The `Ext` universe is `max v u`, the morphism universe of the sheaf category on a site with
objects in `Type v` and coefficients in `AddCommGrpCat.{u}`.  That is the universe at which
`CategoryTheory.Sheaf.H'` is taken; the choice is immaterial by
`Stacks.Cohomology.ModuleDirectImageOnACover.isZero_sheafCohomology_chgUniv`, and the variant of
the comparison stated there is what a consumer supplying a vanishing at another `Ext` universe
should use.

`Stacks.Cohomology.AcyclicCover.evaluation_additive` is a local instance because the statement of
the carried predicate mentions the right derived functors of
`CategoryTheory.SheafOfModules.evaluation`, which needs its additivity in scope.

## References

* [Stacks Project, Tag 08IY](https://stacks.math.columbia.edu/tag/08IY)
* [Stacks Project, Tag 075F](https://stacks.math.columbia.edu/tag/075F)
* [Stacks Project, Tag 0756](https://stacks.math.columbia.edu/tag/0756)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Opposite

universe u v

namespace AlgebraicGeometry.Stack

attribute [local instance] Stacks.Cohomology.AcyclicCover.evaluation_additive
attribute [local instance] HasDerivedCategory.standard

section Reduction

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)
  [HasSheafify (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u}]

/-- **The sheaf-side instance hypothesis of this file is satisfiable.** Abelian sheaves on the
fppf site of a category fibred in groupoids have enough injectives, at the coefficient universe
`u` of the schemes, as soon as that site is essentially small at `u`: they then form a
Grothendieck abelian category.

This is `Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite`, recorded so
that the hypotheses carried below are visibly inhabited and not an empty class. -/
theorem enoughInjectives_fppfSiteSheaf_of_essentiallySmall [EssentiallySmall.{u} 𝒳] :
    EnoughInjectives
      (Sheaf (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u}) :=
  Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite _

variable
  [(BigFppfOver.associatedTopology B S hS p .fppf).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (fppfSiteModules B S hS p hp)]
  [HasExt.{max v u}
    (Sheaf (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u})]
  [EnoughInjectives
    (Sheaf (BigFppfOver.associatedTopology B S hS p .fppf) AddCommGrpCat.{u})]
  [HasExt.{max v u} (fppfSiteModules B S hS p hp)]

/-- **The affine acyclicity carried by Stacks 08IY follows from its abelian-sheaf form.** If the
cohomology of the underlying abelian sheaf of every module in `LQCoh^fbc(𝒪_𝒳)` vanishes in every
positive degree over every object of `𝒳_fppf` lying over an affine scheme, then so does the
module-valued cohomology, which is
`AlgebraicGeometry.Stack.HasAffineAcyclicLqcFbcModules`.

The two spellings of cohomology over an object are compared by
`Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_evaluation_of_isZero_H'`, which
corepresents module-valued sections over an object and so needs no smallness of the site — only
that its morphisms and the module sections share a universe.  A positive degree is written as a
successor, which is the form that comparison takes. -/
theorem hasAffineAcyclicLqcFbcModules_of_isZero_sheafCohomology
    (hab : ∀ F : fppfSiteModules B S hS p hp,
      IsLocallyQuasicoherentWithFlatBaseChange B E h S hS p hp F.val →
      ∀ x : 𝒳, IsAffineOver B S hS (p.obj x) → ∀ i : ℕ, 0 < i →
        IsZero (Sheaf.H'.{max v u}
          ((SheafOfModules.toSheaf (fppfSiteRingSheaf B S hS p hp)).obj F) i x)) :
    HasAffineAcyclicLqcFbcModules B E h S hS p hp := by
  intro F hF x hx i hi
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = j + 1 := ⟨i - 1, (Nat.succ_pred_eq_of_pos hi).symm⟩
  exact Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_evaluation_of_isZero_H'
    (BigFppfOver.associatedTopology B S hS p .fppf) (fppfSiteRingSheaf B S hS p hp) x j F
    (hab F hF x hx (j + 1) (Nat.succ_pos j))

/-- **Stacks 08IY for a category fibred in groupoids, with the carried hypothesis moved to the
abelian-sheaf level.** An object `K` of `D(𝒪_𝒳)` whose cohomology sheaves are locally
quasi-coherent with the flat base change property is a derived limit of the tower of its
canonical truncations from below, provided the cohomology of the underlying abelian sheaves of
the modules in `LQCoh^fbc(𝒪_𝒳)` vanishes in positive degrees over the objects lying over affine
schemes.

This is `AlgebraicGeometry.Stack.exists_isDerivedLimit_truncGETower_of_lqcFbc` with `hvan`
supplied by `hasAffineAcyclicLqcFbcModules_of_isZero_sheafCohomology`.  The covering class is
still carried as `hB`; on an essentially small site it is discharged by
`AlgebraicGeometry.Stack.hasEnoughObjects_isAffineOver_of_essentiallySmall`. -/
theorem exists_isDerivedLimit_truncGETower_of_isZero_sheafCohomology
    (K : DerivedCategory (fppfSiteModules B S hS p hp))
    (hK : ∀ i : ℤ, IsLocallyQuasicoherentWithFlatBaseChange B E h S hS p hp
      ((DerivedCategory.homologyFunctor (fppfSiteModules B S hS p hp) i).obj K).val)
    (hB : (BigFppfOver.associatedTopology B S hS p .fppf).HasEnoughObjects
      (fun x => IsAffineOver B S hS (p.obj x)))
    (hab : ∀ F : fppfSiteModules B S hS p hp,
      IsLocallyQuasicoherentWithFlatBaseChange B E h S hS p hp F.val →
      ∀ x : 𝒳, IsAffineOver B S hS (p.obj x) → ∀ i : ℕ, 0 < i →
        IsZero (Sheaf.H'.{max v u}
          ((SheafOfModules.toSheaf (fppfSiteRingSheaf B S hS p hp)).obj F) i x)) :
    ∃ _ : HasProduct fun n : ℕ ↦ (fppfTruncGETower B S hS p hp K).obj ⟨n⟩,
      IsDerivedLimit (fppfTruncGETower B S hS p hp K) K :=
  exists_isDerivedLimit_truncGETower_of_lqcFbc B E h S hS p hp K hK hB
    (hasAffineAcyclicLqcFbcModules_of_isZero_sheafCohomology B E h S hS p hp hab)

end Reduction

end AlgebraicGeometry.Stack

end
