module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedColimit
public import StacksCore.Tactic.StacksAttribute

/-!
# Colimits of good differential graded modules, with nothing assumed of the base change

Let `(C, O)` be a ringed site and let `A` be a sheaf of differential graded `O`-algebras on it.
An arbitrary direct sum of good right differential graded `A`-modules is good, and a filtered
colimit of good right differential graded `A`-modules is good.

The notion of goodness used here is
`SheafOfModules.DifferentialGradedModule.IsGoodSiteBaseChange`: conditions (1) and (2) of the
source, and condition (3) quantified over the base changes along a morphism of ringed *sites*,
that is those whose functor of sites is continuous.

**That is not Tag 0FSA, and the statements of this file do not carry Tag 0FSD.** The source reads
condition (3) over morphisms of ringed *topoi*; the definition that does so is
`SheafOfModules.IsGoodToposBaseChange`, which carries Tag 0FSA, and Tag 0FSD at that reading is
`SheafOfModules.isGoodToposBaseChange_of_isColimitCofan` and
`isGoodToposBaseChange_of_isColimit_isFiltered` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GoodDifferentialGradedToposDirectSum.lean`. The
statements below are the same two colimit arguments run at this file's auxiliary variant, kept
for the consumers stated against it.

Nothing is assumed of the pullback itself. The argument needs the pullback to commute with the
colimit, and along a morphism of ringed sites it does: the pullback is the left adjoint of the
direct image, so it preserves every colimit. This is
`SheafOfModules.DifferentialGradedModule.PullbackData.isColimit_functor_mapCocone` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPullbackColimits.lean`, and it is
what replaces the colimit-preservation hypothesis carried by
`SheafOfModules.DifferentialGradedModule.IsGoodCocontinuousBaseChange`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.IsGoodSiteBaseChange`: a good right differential
  graded module, with condition (3) read over the base changes along a morphism of ringed sites.

## Main results

* `SheafOfModules.DifferentialGradedModule.isGoodSiteBaseChange_of_isColimitCofan` and
  `isGoodSiteBaseChange_of_isColimit_isFiltered`: **an arbitrary direct sum of good right
  differential graded modules is good, and a filtered colimit of good right differential graded
  modules is good**, with no condition on the base changes beyond their being morphisms of
  ringed sites.
* `SheafOfModules.DifferentialGradedModule.IsGoodCocontinuousBaseChange.isGoodSiteBaseChange`:
  **the colimit-preservation hypothesis of `IsGoodCocontinuousBaseChange` is discharged, not
  assumed**, at every base change along a morphism of ringed sites.
* `SheafOfModules.DifferentialGradedModule.IsGood.isGoodSiteBaseChange`: condition (3) of
  `IsGood` concludes for every pullback datum, so in particular for those along a morphism of
  ringed sites.

## Implementation notes

The predicate is a third reading of goodness beside `IsGood` and
`IsGoodCocontinuousBaseChange`, and the three differ only in which base changes condition (3)
ranges over: every functor `u` between the two sites, those whose pullback preserves colimits,
and those whose `u` is continuous. The third is the one for which the lemma of this file holds
with no side condition, because continuity of `u` is exactly what makes the direct image exist
and hence the pullback a left adjoint. Conditions (1) and (2) are the same three times over, and
are shared verbatim with the two existing predicates, so the colimit statements of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GoodDifferentialGradedColimit.lean` serve all
three.

Continuity of `u` does not tie the universes of the two ringed sites together, for the reason
recorded in `DifferentialGradedPullbackColimits.lean`. What does tie the two module universes
together is the adjunction, whose two categories of modules have the same section universe; so
the colimit statements, which use it, fix the module universe of the second ringed site to be
that of the first, as the corresponding statements for `IsGoodCocontinuousBaseChange` already do
for the reason recorded there.

Exactness of the colimits is needed at the second ringed site as well as at the first, and that
site is quantified over inside the predicate, so the hypothesis cannot be imposed on it; for a
discrete index category it is AB4 and for a filtered one AB5, and both hold at every site.

## References

* [Stacks Project, Tag 0FSD](https://stacks.math.columbia.edu/tag/0FSD)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 03CR](https://stacks.math.columbia.edu/tag/03CR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t m v u m₁ v₁ u₁

namespace SheafOfModules

/-- Coproducts of sheaves of modules, indexed in the module universe. Instance search times out
looking for them through the `Discrete` shape, so they are taken from `HasColimitsOfSize`. -/
local instance (priority := high) hasColimitsOfShape_discrete_GoodDifferentialGradedSiteColimit {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    (R : Sheaf J RingCat.{t}) (K : Type m) :
    HasColimitsOfShape (Discrete K) (SheafOfModules.{m} R) :=
  (inferInstance : HasColimitsOfSize.{m, m} (SheafOfModules.{m} R)).has_colimits_of_shape _

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {Osharp : Sheaf J CommRingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}

/-- An auxiliary variant of goodness: a right differential graded `A`-module is flat as a graded
module, K-flat, and stays so after every base change along a morphism of ringed sites, that is
along a continuous functor of the underlying sites, every differential graded algebra on the
target and every homomorphism of differential graded algebras.

Tag 0FSA itself is `SheafOfModules.IsGoodToposBaseChange` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeDifferentialGradedModuleToposPullback.lean`,
whose condition (3) runs over morphisms of ringed topoi. The two are incomparable in both
directions: not every morphism of topoi comes from a functor of the two given sites — only from
a functor of a site equivalent to the target (Tag 03CR) — so this definition is silent where the
tag speaks; and where both speak, this one takes a `PullbackData` as given while the tag asserts
that a pullback exists, so neither clause implies the other. -/
def IsGoodSiteBaseChange (P : DifferentialGradedModule.{t, m, m} A) : Prop :=
  RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded P) ∧
    RelativeTensor.IsKFlat P ∧
      ∀ {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
        [J₁.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
        [J₁.WEqualsLocallyBijective AddCommGrpCat.{m₁}] [HasSheafify J₁ AddCommGrpCat.{m₁}]
        {Osharp₁ : Sheaf J₁ CommRingCat.{t}} (u : C ⥤ C₁) [u.IsContinuous J J₁]
        (σ : (toRingCat J Osharp).obj ⟶ u.op ⋙ (toRingCat J₁ Osharp₁).obj)
        (A₁ : DifferentialGradedAlgebra.{t, m₁} (toRingCat J₁ Osharp₁))
        (φ : DifferentialGradedAlgebra.SemilinearHom u σ A A₁)
        (PD : PullbackData.{t, m₁, m₁, v₁, u₁, m, m, v, u} φ),
        RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded (PD.obj P)) ∧
          RelativeTensor.IsKFlat (PD.obj P)

namespace IsGoodSiteBaseChange

variable {P : DifferentialGradedModule.{t, m, m} A}

/-- The underlying graded module of a good differential graded module is flat. -/
theorem isGradedFlat (hP : IsGoodSiteBaseChange.{t, m, v, u, m₁, v₁, u₁} P) :
    RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded P) :=
  hP.1

/-- A good differential graded module is K-flat. -/
theorem isKFlat (hP : IsGoodSiteBaseChange.{t, m, v, u, m₁, v₁, u₁} P) :
    RelativeTensor.IsKFlat P :=
  hP.2.1

/-- Flatness and K-flatness of a good differential graded module persist after a base change
along a morphism of ringed sites. -/
theorem baseChange (hP : IsGoodSiteBaseChange.{t, m, v, u, m₁, v₁, u₁} P)
    {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
    [J₁.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
    [J₁.WEqualsLocallyBijective AddCommGrpCat.{m₁}] [HasSheafify J₁ AddCommGrpCat.{m₁}]
    {Osharp₁ : Sheaf J₁ CommRingCat.{t}} (u : C ⥤ C₁) [u.IsContinuous J J₁]
    (σ : (toRingCat J Osharp).obj ⟶ u.op ⋙ (toRingCat J₁ Osharp₁).obj)
    (A₁ : DifferentialGradedAlgebra.{t, m₁} (toRingCat J₁ Osharp₁))
    (φ : DifferentialGradedAlgebra.SemilinearHom u σ A A₁)
    (PD : PullbackData.{t, m₁, m₁, v₁, u₁, m, m, v, u} φ) :
    RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded (PD.obj P)) ∧
      RelativeTensor.IsKFlat (PD.obj P) :=
  hP.2.2 u σ A₁ φ PD

end IsGoodSiteBaseChange

/-- Condition (3) of `IsGood` concludes for every pullback datum, so it concludes in particular
for the pullback data along a morphism of ringed sites. -/
theorem IsGood.isGoodSiteBaseChange {P : DifferentialGradedModule.{t, m, m} A}
    (hP : IsGood.{t, m, v, u, m₁, v₁, u₁} P) :
    IsGoodSiteBaseChange.{t, m, v, u, m₁, v₁, u₁} P := by
  refine ⟨hP.isGradedFlat, hP.isKFlat, ?_⟩
  intro C₁ _ J₁ _ _ _ Osharp₁ u _ σ A₁ φ PD
  exact hP.baseChange u σ A₁ φ PD

/-- **The colimit-preservation hypothesis of `IsGoodCocontinuousBaseChange` is discharged at
every base change along a morphism of ringed sites**: there the pullback is the left adjoint of
the direct image, so it preserves colimits and the hypothesis is met rather than assumed. -/
theorem IsGoodCocontinuousBaseChange.isGoodSiteBaseChange
    {P : DifferentialGradedModule.{t, m, m} A}
    (hP : IsGoodCocontinuousBaseChange.{t, m, v, u, m, v₁, u₁} P) :
    IsGoodSiteBaseChange.{t, m, v, u, m, v₁, u₁} P := by
  refine ⟨hP.isGradedFlat, hP.isKFlat, ?_⟩
  intro C₁ _ J₁ _ _ _ Osharp₁ u _ σ A₁ φ PD
  exact hP.baseChange u σ A₁ φ PD PD.preservesColimitsOfSize_functor

/-- **An arbitrary direct sum of good right differential graded modules is good.**

Conditions (1) and (2) for the direct sum are the colimit statements of
`GoodDifferentialGradedColimit.lean`, applied to the coproduct cocone. For condition (3), the
pullback along a morphism of ringed sites preserves colimits because it is a left adjoint, so
the pullbacks of the summands form a coproduct cocone with the pullback of the direct sum as its
point; the summands' own condition (3) says that those pullbacks are flat and K-flat, and the
colimit statements apply again, at the second ringed site.

Goodness is this file's auxiliary `IsGoodSiteBaseChange`, so this is not Tag 0FSD; that tag is
registered on the same statement at `SheafOfModules.IsGoodToposBaseChange` in
`GoodDifferentialGradedToposDirectSum.lean`. -/
theorem isGoodSiteBaseChange_of_isColimitCofan {ι : Type m}
    {P : ι → DifferentialGradedModule.{t, m, m} A} {c : Cofan P} (hc : IsColimit c)
    (hP : ∀ i, IsGoodSiteBaseChange.{t, m, v, u, m, v₁, u₁} (P i)) :
    IsGoodSiteBaseChange.{t, m, v, u, m, v₁, u₁} c.pt := by
  have := ab4OfSize.{t, m} (toRingCat J Osharp)
  have h₁ := isGradedFlat_and_isKFlat_of_isColimit hc
    fun i ↦ ⟨(hP i.as).isGradedFlat, (hP i.as).isKFlat⟩
  refine ⟨h₁.1, h₁.2, ?_⟩
  intro C₁ _ J₁ _ _ _ Osharp₁ u _ σ A₁ φ PD
  have := ab4OfSize.{t, m} (toRingCat J₁ Osharp₁)
  exact isGradedFlat_and_isKFlat_of_isColimit (c := PD.functor.mapCocone c)
    (PD.isColimit_functor_mapCocone hc) fun i ↦ (hP i.as).baseChange u σ A₁ φ PD

/-- **A filtered colimit of good right differential graded modules is good.** The argument is
that of `isGoodSiteBaseChange_of_isColimitCofan`, with AB5 in place of AB4. Goodness is this
file's auxiliary `IsGoodSiteBaseChange`, so this is not Tag 0FSD; that tag is registered on the
same statement at `SheafOfModules.IsGoodToposBaseChange` in
`GoodDifferentialGradedToposDirectSum.lean`. -/
theorem isGoodSiteBaseChange_of_isColimit_isFiltered {D : Type m} [SmallCategory D]
    [IsFiltered D] {K : D ⥤ DifferentialGradedModule.{t, m, m} A} {c : Cocone K}
    (hc : IsColimit c) (hK : ∀ d : D, IsGoodSiteBaseChange.{t, m, v, u, m, v₁, u₁} (K.obj d)) :
    IsGoodSiteBaseChange.{t, m, v, u, m, v₁, u₁} c.pt := by
  have h₁ := isGradedFlat_and_isKFlat_of_isColimit hc
    fun d ↦ ⟨(hK d).isGradedFlat, (hK d).isKFlat⟩
  refine ⟨h₁.1, h₁.2, ?_⟩
  intro C₁ _ J₁ _ _ _ Osharp₁ u _ σ A₁ φ PD
  exact isGradedFlat_and_isKFlat_of_isColimit (c := PD.functor.mapCocone c)
    (PD.isColimit_functor_mapCocone hc) fun d ↦ (hK d).baseChange u σ A₁ φ PD

end DifferentialGradedModule

end SheafOfModules
