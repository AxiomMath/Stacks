module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.AbelianSheafification
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposOfAFibredCategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.AbelianDerivedExistence

/-!
# Lower shriek on abelian sheaves for the projection of a fibred category

Let `(D, O_D)` be a ringed site, let `p : C ⥤ D` be a fibred category over its underlying site,
and give `C` the topology it inherits from `D`, as in the standing data of Stacks 08P8. The
projection is continuous and cocontinuous for those topologies, so the induced morphism of topoi
`π : Sh(C) ⟶ Sh(D)` has inverse image `π⁻¹ = p_s`, restriction along `p`. On abelian sheaves that
restriction has a left adjoint `π_!`, the lower shriek of the situation, and `π_!` has an
unbounded left derived functor `Lπ_! : D(Ab(C)) ⥤ D(Ab(D))` as soon as the acyclicity statement
of Stacks 07AC holds for it.

This file constructs both in the situation of Stacks 08P8, together with the family of functors
`F ↦ H^{-n}(Lπ_! F)` which is the left-hand side of Stacks 08PJ.

## Main definitions

* `Stacks.Sites.FibredCategory.FibredCategorySituation.abelianInverseImage`: `π⁻¹ : Ab(D) ⥤
  Ab(C)`, restriction of abelian sheaves along the projection.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.abelianLowerShriek`: `π_! : Ab(C) ⥤
  Ab(D)`, the chosen left adjoint of `π⁻¹`, with its adjunction
  `abelianLowerShriekAdjunction`.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.AbelianLowerShriekAcyclic`: the acyclicity
  statement of Stacks 07AC for `π_!`.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.derivedAbelianLowerShriek`: `Lπ_!`, the
  unbounded left derived functor of `π_!`, with its adjunction
  `derivedAbelianLowerShriekAdjunction` to derived restriction
  `derivedAbelianInverseImage`.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.derivedAbelianLowerShriekHomology`:
  `F ↦ H^{-n}(Lπ_! F)`, the family of functors appearing in Stacks 08PJ.

## Main results

* `Stacks.Sites.FibredCategory.FibredCategorySituation.abelianInverseImage_isRightAdjoint`:
  restriction of abelian sheaves along the projection admits a left adjoint.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.abelianLowerShriek_additive` and
  `abelianLowerShriek_preservesFiniteColimits`: `π_!` is additive and right exact.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.abelianLowerShriekIsoConstruction`:
  the chosen left adjoint agrees with the left Kan extension followed by sheafification, the
  functor whose fibrewise-colimit description is Stacks 08PE.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.hasPointwiseLeftDerivedAbelianLowerShriek`:
  the acyclicity statement of Stacks 07AC produces the pointwise left derived functor of `π_!`.

## Implementation notes

The sections are taken in `AddCommGrpCat.{max w uD vD uC vC}`, the universe in which Stacks 08P8
forms the morphism of topoi and in which Stacks 08PE states the lower shriek. The generic
constructions of
`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/AbelianDerivedExistence.lean` are stated
with coefficients `AddCommGrpCat.{max v₁ w'}`, and are applied here with `w' := max w uD vD uC`
and explicit universes: Lean's level unifier does not solve `max vC ?w' =?= max w uD vD uC vC`,
so the instances below are given by name.

The acyclicity statement of Stacks 07AC for `π_!` is the proposition `AbelianLowerShriekAcyclic`;
`derivedAbelianLowerShriek` and the declarations after it take the resulting pointwise left
derived functor as an instance hypothesis, which `hasPointwiseLeftDerivedAbelianLowerShriek`
derives from `AbelianLowerShriekAcyclic`.

`Functor.sheafPullback` is a chosen left adjoint and
`Functor.sheafPullbackConstruction.sheafPullback` is the left Kan extension followed by
sheafification; `abelianLowerShriekIsoConstruction` compares the two.

## References

* [Stacks Project, Tag 08P8](https://stacks.math.columbia.edu/tag/08P8)
* [Stacks Project, Tag 08PE](https://stacks.math.columbia.edu/tag/08PE)
* [Stacks Project, Tag 08PJ](https://stacks.math.columbia.edu/tag/08PJ)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 06NW](https://stacks.math.columbia.edu/tag/06NW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sites.FibredCategory

universe uD vD uC vC w u₁ v₁ t

namespace FibredCategorySituation

variable (s : FibredCategorySituation.{uD, vD, uC, vC, w})

/-- Abelian sheaves for the inherited topology on the total category can be sheafified in the
universe in which the morphism of topoi `π` is formed. -/
instance hasSheafifyTopology :
    HasSheafify s.topology AddCommGrpCat.{max w uD vD uC vC} :=
  hasSheafify_addCommGrpCat.{uC, vC, max w uD vD uC vC} s.topology

/-- Abelian sheaves on the base site can be sheafified in the universe in which the morphism of
topoi `π` is formed. -/
instance hasSheafifyBaseTopology :
    HasSheafify s.base.J AddCommGrpCat.{max w uD vD uC vC} :=
  hasSheafify_addCommGrpCat.{uD, vD, max w uD vD uC vC} s.base.J

/-- Abelian sheaves on the base site form a Grothendieck abelian category. -/
instance isGrothendieckAbelian_baseSheaves :
    IsGrothendieckAbelian.{max w uD vD uC vC}
      (Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}) :=
  isGrothendieckAbelian_sheaf_addCommGrpCat.{uD, vD, max w uD vD uC vC} s.base.J

/-- The total category is small in the universe of the sections. -/
instance small_C : Small.{max w uD vD uC vC} s.C :=
  small_max.{max w uD vD vC, uC} _

/-- `π⁻¹ : Ab(D) ⥤ Ab(C)`, the inverse image of abelian sheaves along the morphism of topoi
induced by the projection: restriction along `p`, which is a sheaf for the inherited topology
because `p` is continuous. -/
abbrev abelianInverseImage :
    Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC} ⥤
      Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC} :=
  s.p.sheafPushforwardContinuous AddCommGrpCat.{max w uD vD uC vC} s.topology s.base.J

/-- The inverse image of abelian sheaves along `π` admits a left adjoint `π_!`. -/
instance abelianInverseImage_isRightAdjoint : s.abelianInverseImage.IsRightAdjoint :=
  inferInstance

/-- `π_! : Ab(C) ⥤ Ab(D)`, the lower-shriek functor on abelian sheaves for the projection of the
fibred category: the chosen left adjoint of `π⁻¹`. -/
abbrev abelianLowerShriek :
    Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC} ⥤
      Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC} :=
  s.p.sheafPullback AddCommGrpCat.{max w uD vD uC vC} s.topology s.base.J

/-- The adjunction `π_! ⊣ π⁻¹` on abelian sheaves. -/
abbrev abelianLowerShriekAdjunction : s.abelianLowerShriek ⊣ s.abelianInverseImage :=
  s.p.sheafAdjunctionContinuous AddCommGrpCat.{max w uD vD uC vC} s.topology s.base.J

/-- `π_!` is additive. -/
instance abelianLowerShriek_additive : s.abelianLowerShriek.Additive :=
  Stacks.Cohomology.DerivedLowerShriek.additive_abelianLowerShriek.{max w uD vD uC,
    vC, uC, vD, uD} s.topology s.base.J s.p

/-- `π_!` preserves finite colimits. -/
instance abelianLowerShriek_preservesFiniteColimits :
    PreservesFiniteColimits s.abelianLowerShriek :=
  Stacks.Cohomology.DerivedLowerShriek.preservesFiniteColimits_abelianLowerShriek.{max w uD vD uC,
    vC, uC, vD, uD} s.topology s.base.J s.p

/-- The chosen left adjoint `π_!` agrees with the left Kan extension along `p.op` followed by
sheafification, the functor whose value at an abelian sheaf is the sheaf associated to the
presheaf of fibrewise colimits of Stacks 08PE. -/
abbrev abelianLowerShriekIsoConstruction :
    s.abelianLowerShriek ≅ Functor.sheafPullbackConstruction.sheafPullback s.p
      AddCommGrpCat.{max w uD vD uC vC} s.topology s.base.J :=
  Functor.sheafPullbackConstruction.sheafPullbackIso s.p
    AddCommGrpCat.{max w uD vD uC vC} s.topology s.base.J

/-- `π_!` applied degreewise to unbounded complexes of abelian sheaves, read on the homotopy
categories. -/
abbrev abelianLowerShriekOnHomotopy :
    HomotopyCategory (Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC}) (ComplexShape.up ℤ) ⥤
      HomotopyCategory (Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}) (ComplexShape.up ℤ) :=
  Stacks.Cohomology.DerivedLowerShriek.abelianLowerShriekOnHomotopy.{max w uD vD uC,
    vC, uC, vD, uD} s.topology s.base.J s.p

/-- The acyclicity statement of Stacks 07AC for `π_!`: the lower-shriek functor of the
situation carries a bounded above acyclic complex whose terms are direct sums of the free abelian
sheaves `j_{U!} ℤ_U` on objects of the total category to an acyclic complex. -/
abbrev AbelianLowerShriekAcyclic : Prop :=
  Stacks.Cohomology.DerivedLowerShriek.AbelianLowerShriekAcyclic.{max w uD vD uC,
    vC, uC, vD, uD} s.topology s.base.J s.p

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- Under the acyclicity statement of Stacks 07AC, degreewise `π_!` has a pointwise left derived
functor on the unbounded homotopy category. -/
theorem hasPointwiseLeftDerivedAbelianLowerShriek (h : s.AbelianLowerShriekAcyclic) :
    (s.abelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC})
        (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.DerivedLowerShriek.hasPointwiseLeftDerivedAbelianLowerShriek_of_acyclic.{max w
    uD vD uC, vC, uC, vD, uD} s.topology s.base.J s.p h

variable [(s.abelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
  (HomotopyCategory.quasiIso (Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC})
    (ComplexShape.up ℤ))]

/-- `Lπ_! : D(Ab(C)) ⥤ D(Ab(D))`, the unbounded left derived functor of the lower-shriek functor
of the situation. -/
abbrev derivedAbelianLowerShriek :
    DerivedCategory (Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC}) ⥤
      DerivedCategory (Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}) :=
  Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriek.{max w uD vD uC,
    vC, uC, vD, uD} s.topology s.base.J s.p

/-- `π⁻¹ : D(Ab(D)) ⥤ D(Ab(C))` on the unbounded derived categories, induced degreewise by the
exact functor `π⁻¹` on abelian sheaves. -/
abbrev derivedAbelianInverseImage :
    DerivedCategory (Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}) ⥤
      DerivedCategory (Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC}) :=
  Stacks.Cohomology.DerivedLowerShriek.derivedAbelianRestriction.{max w uD vD uC,
    vC, uC, vD, uD} s.topology s.base.J s.p

open Stacks.Cohomology.DerivedLowerShriek in
/-- Under the acyclicity statement of Stacks 07AC, `Lπ_!` is left adjoint to derived
restriction. -/
def derivedAbelianLowerShriekAdjunction (h : s.AbelianLowerShriekAcyclic) :
    s.derivedAbelianLowerShriek ⊣ s.derivedAbelianInverseImage :=
  have :=
    isLeftDerivedFunctor_abelianLowerShriek_comp_of_acyclic.{max w uD vD uC, vC, uC, vD, uD}
      s.topology s.base.J s.p h DerivedCategory.Qh s.derivedAbelianLowerShriek
      (derivedAbelianLowerShriekComparison.{max w uD vD uC, vC, uC, vD, uD}
        s.topology s.base.J s.p)
      s.derivedAbelianInverseImage
  Stacks.Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekAdjunction.{max w uD vD uC,
    vC, uC, vD, uD} s.topology s.base.J s.p

/-- `F ↦ H^{-n}(Lπ_! F)`, the homology of the left derived lower shriek of an abelian sheaf placed
in degree zero: the left-hand side of Stacks 08PJ. -/
abbrev derivedAbelianLowerShriekHomology (n : ℕ) :
    Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC} ⥤
      Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC} :=
  DerivedCategory.singleFunctor (Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC}) 0 ⋙
    s.derivedAbelianLowerShriek ⋙
      DerivedCategory.homologyFunctor
        (Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}) (-(n : ℤ))

end Derived

end FibredCategorySituation

end Stacks.Sites.FibredCategory

end
