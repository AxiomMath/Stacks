module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriek

/-!
# Derived lower shriek on a chaotic site commutes with colimits

Let `C` be a small category with the chaotic topology, so that lower shriek along the morphism
to the point is the colimit over `Cᵒᵖ` (Stacks 08PF) and its total left derived functor is
`Stacks.CategoryHomology.totalDerivedColimit` (Stacks 08Q6). Derived Categories, Proposition
13.29.2 says that `Lπ_!` commutes with direct sums and with countable filtered colimits; here
that is immediate, because `Lπ_!` is a left adjoint — the derived adjunction `Lπ_! ⊣ π^{-1}` is
`Stacks.CategoryHomology.totalDerivedColimitAdjunction`, and it is unconditional.

This file records that consequence as instances, for `Lπ_!` on diagrams and for `Lπ_!` with
coefficients in a sheaf of rings (Stacks 09CZ,
`Stacks.ChaoticSite.derivedColimitWithCoefficients`). It is the input to the dévissage step of
[Stacks, Tag 08RX], which reduces a statement about an arbitrary object of `D(O)` to the
generators `j_{U!}O_U` by writing it as a colimit of bounded above complexes whose terms are
direct sums of generators.

## Main results

* `Stacks.CategoryHomology.totalDerivedColimit_preservesColimitsOfSize` and
  `Stacks.CategoryHomology.totalDerivedColimit_preservesColimitsOfShape_discrete`: `Lπ_!` on
  `D(Cᵒᵖ ⥤ D)` preserves all colimits that exist, in particular all direct sums.
* `Stacks.ChaoticSite.derivedColimitWithCoefficients_preservesColimitsOfSize` and
  `Stacks.ChaoticSite.derivedColimitWithCoefficients_preservesColimitsOfShape_discrete`: the
  same for `Lπ_! : D(O) ⥤ D(B)` of Stacks 09CZ.

## Implementation notes

`CategoryTheory.Adjunction.leftAdjoint_preservesColimits` is universe polymorphic in the shape
of the colimit, so the statements below are too; the discrete case is spelled out separately
because the dévissage uses it at an index type whose universe is not that of the site.

## References

* [Stacks Project, Tag 08Q6](https://stacks.math.columbia.edu/tag/08Q6)
* [Stacks Project, Tag 09CZ](https://stacks.math.columbia.edu/tag/09CZ)
* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w' w uD vD u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.CategoryHomology

variable (C : Type u) [SmallCategory C] (D : Type uD) [Category.{vD} D] [Abelian D]
  [EnoughProjectives (Cᵒᵖ ⥤ D)] [HasColimitsOfShape ℕ D] [HasExactColimitsOfShape ℕ D]
  [HasColimitsOfShape Cᵒᵖ D]

/-- **Derived lower shriek on a chaotic site preserves colimits**, being a left adjoint: the
derived adjunction `Lπ_! ⊣ π^{-1}` is `totalDerivedColimitAdjunction`. This is the form of
Derived Categories, Proposition 13.29.2 used in [Stacks, Tag 08RX]. -/
instance totalDerivedColimit_preservesColimitsOfSize :
    PreservesColimitsOfSize.{w', w} (totalDerivedColimit C D) :=
  (totalDerivedColimitAdjunction C D).leftAdjoint_preservesColimits

/-- **Derived lower shriek on a chaotic site commutes with direct sums.** -/
instance totalDerivedColimit_preservesColimitsOfShape_discrete (ι : Type w) :
    PreservesColimitsOfShape (Discrete ι) (totalDerivedColimit C D) :=
  inferInstance

end Stacks.CategoryHomology

namespace Stacks.ChaoticSite

open Stacks.CategoryHomology

variable {C : Type u} [SmallCategory C] (B : Type u) [Ring B] (O : Cᵒᵖ ⥤ RingCat.{u})
  (φ : O ⟶ (Functor.const Cᵒᵖ).obj (RingCat.of B))

/-- **Derived lower shriek with coefficients preserves colimits.** The functor `Lπ_!` of
[Stacks, Tag 09CZ] is a composite of two left adjoints, so it is one. -/
instance derivedColimitWithCoefficients_preservesColimitsOfSize :
    PreservesColimitsOfSize.{w', w} (derivedColimitWithCoefficients B O φ) :=
  (derivedColimitWithCoefficientsAdjunction B O φ).leftAdjoint_preservesColimits

/-- **Derived lower shriek with coefficients commutes with direct sums.** -/
instance derivedColimitWithCoefficients_preservesColimitsOfShape_discrete (ι : Type w) :
    PreservesColimitsOfShape (Discrete ι) (derivedColimitWithCoefficients B O φ) :=
  inferInstance

end Stacks.ChaoticSite

end
