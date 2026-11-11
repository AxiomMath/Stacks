module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.PontryaginDualEquivalence
public import StacksFrontier.CategoryTheory.Abelian.DerivedFunctorDualityPlus

/-!
# Homology of a topological group with coefficients in compact modules

Let `G` be a topological group. The category of compact `G`-modules is anti-equivalent to the
category of discrete `G`-modules (`Stacks.GroupHomology.compactDualEquivalence`), which is abelian
with enough injectives. Hence compact `G`-modules form an abelian category with enough
projectives, and the homology of `G` is defined, as in [Stacks, Tag 03VI], by
`H_i(G, M) = L_i H₀(G, M)`, the left derived functors of the coinvariants `M ↦ M_G`. For a normal
subgroup `N` of a topological group `Γ`, the left derived functors of `H₀(N, -)` take compact
`Γ`-modules to compact `Γ ⧸ N`-modules.

## Main definitions

* `Stacks.GroupHomology.compactGModuleAbelian`: compact `G`-modules form an abelian category.
* `Stacks.GroupHomology.compactGModuleEnoughProjectives`: compact `G`-modules have enough
  projectives.
* `Stacks.GroupHomology.groupHomologyFunctor G i`: `H_i(G, -) = L_i H₀(G, -)` from compact
  `G`-modules to compact abelian groups.
* `Stacks.GroupHomology.normalCoinvariantsLeftDerived N i`: `L_i H₀(N, -)` from compact
  `Γ`-modules to compact `Γ ⧸ N`-modules.
* `Stacks.GroupHomology.derivedCoinvariantsFunctor G` and
  `Stacks.GroupHomology.derivedNormalCoinvariantsFunctor N`: the derived functors `LH₀(G, -)`
  and `LH₀(N, -)` on bounded above complexes, through the opposite categories.

## Implementation notes

The left derived functor `LH₀(G, -) : D⁻(Mod^cpt_G) ⥤ D⁻(Ab^cpt)` is expressed as the right
derived functor `D⁺((Mod^cpt_G)ᵒᵖ) ⥤ D⁺((Ab^cpt)ᵒᵖ)` of the opposite functor
(`CategoryTheory.Functor.leftDerivedFunctorMinusOfOp`), since `D⁺(Cᵒᵖ)` is `D⁻(C)ᵒᵖ`. Its
cohomology on an object placed in degree `0` is the opposite of `H_i(G, -)`
(`CategoryTheory.Functor.leftDerivedFunctorMinusOfOpHomologyIso`).

Enough projectives needs the universe of the modules to contain that of the group, as enough
injectives does for discrete modules, so the derived functors are stated at module universe
`max u v`.

## References

* [Stacks Project, Tag 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.GroupCohomology

universe u v

namespace Stacks.GroupHomology

section Category

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Compact `G`-modules form an abelian category**, being anti-equivalent to the abelian
category of discrete `G`-modules. -/
instance compactGModuleAbelian : Abelian (CompactGModule.{u, v} G) :=
  (compactDualEquivalence.{u, v} G).abelianOfAntiEquivalence

/-- **Compact `G`-modules have enough projectives**: the anti-equivalence with discrete
`G`-modules takes injectives to projectives, and discrete `G`-modules have enough injectives. -/
@[stacks 03VI "compact G-modules have enough projectives"]
instance compactGModuleEnoughProjectives : EnoughProjectives (CompactGModule.{u, max u v} G) :=
  (compactDualEquivalence.{u, max u v} G).enoughProjectives_of_antiEquivalence

end Category

section Homology

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The homology of `G` with coefficients in compact modules**: `H_i(G, -) = L_i H₀(G, -)`,
the `i`-th left derived functor of the coinvariants `M ↦ M_G` from compact `G`-modules to compact
abelian groups. -/
@[stacks 03VI "H_i(G, M) = L_i H₀(G, M), the left derived functors of coinvariants on compact \
G-modules"]
abbrev groupHomologyFunctor (i : ℕ) :
    CompactGModule.{u, max u v} G ⥤ CompactAddCommGrp.{max u v} :=
  (compactCoinvariantsFunctor.{u, max u v} G).leftDerived i

/-- The homology group `H_i(G, M)` of a compact `G`-module, a compact abelian group. -/
abbrev groupHomology (i : ℕ) (M : CompactGModule.{u, max u v} G) : CompactAddCommGrp.{max u v} :=
  (groupHomologyFunctor.{u, v} G i).obj M

/-- **The derived version `LH₀(G, -)`** of the coinvariants on compact `G`-modules, on bounded
above complexes, written through the opposite categories as a functor
`D⁺((Mod^cpt_G)ᵒᵖ) ⥤ D⁺((Ab^cpt)ᵒᵖ)`, that is `D⁻(Mod^cpt_G)ᵒᵖ ⥤ D⁻(Ab^cpt)ᵒᵖ`. -/
@[stacks 03VI "the derived version LH₀(G, -)"]
abbrev derivedCoinvariantsFunctor [HasDerivedCategory (CompactGModule.{u, max u v} G)ᵒᵖ]
    [HasDerivedCategory CompactAddCommGrp.{max u v}ᵒᵖ] :
    DerivedCategory.Plus (CompactGModule.{u, max u v} G)ᵒᵖ ⥤
      DerivedCategory.Plus CompactAddCommGrp.{max u v}ᵒᵖ :=
  (compactCoinvariantsFunctor.{u, max u v} G).leftDerivedFunctorMinusOfOp

end Homology

section Normal

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (N : Subgroup Γ)
  [N.Normal]

/-- The `i`-th left derived functor `L_i H₀(N, -)` of the coinvariants under a normal subgroup,
from compact `Γ`-modules to compact `Γ ⧸ N`-modules. -/
abbrev normalCoinvariantsLeftDerived (i : ℕ) :
    CompactGModule.{u, max u v} Γ ⥤ CompactGModule.{u, max u v} (Γ ⧸ N) :=
  (normalCoinvariantsFunctor.{u, max u v} N).leftDerived i

/-- **The derived functor `LH₀(N, -)`** of the coinvariants under a normal subgroup `N`, from
bounded above complexes of compact `Γ`-modules to bounded above complexes of compact
`Γ ⧸ N`-modules, written through the opposite categories. -/
@[stacks 03VI "LH₀(N, -) of the coinvariants under a normal subgroup"]
abbrev derivedNormalCoinvariantsFunctor [HasDerivedCategory (CompactGModule.{u, max u v} Γ)ᵒᵖ]
    [HasDerivedCategory (CompactGModule.{u, max u v} (Γ ⧸ N))ᵒᵖ] :
    DerivedCategory.Plus (CompactGModule.{u, max u v} Γ)ᵒᵖ ⥤
      DerivedCategory.Plus (CompactGModule.{u, max u v} (Γ ⧸ N))ᵒᵖ :=
  (normalCoinvariantsFunctor.{u, max u v} N).leftDerivedFunctorMinusOfOp

end Normal

end Stacks.GroupHomology
