module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorComparisonEquivalence
import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverBased
import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverCompare
import StacksFrontier.CategoryTheory.Sites.Stack.Transport.EffectiveDescent

/-!
# Effectivity of descent for `G`-torsors and algebraicity of torsor total spaces

Let `p : G-Torsors ⥤ (Sch/S)_fppf` be the projection of the category of `G`-torsors. Granted
effectivity of descent for `𝒢/ℬ`-torsor sheaves (condition (3) of Stacks 04UM, the hypothesis
`htarget`), effectivity of descent for `p` (condition (3) of Stacks 02ZI) is equivalent to every
`𝒢/ℬ`-torsor sheaf having an algebraic space as total space, and to the comparison functor
`G-Torsors ⥤ 𝒢/ℬ-Torsors` being an equivalence over the big fppf site (the conclusion of
Stacks 04UT).

## Main results

* `AlgebraicGeometry.Space.FppfTorsors.hasEffectiveDescent_projection_of_isAlgebraicSpace_total`:
  granted `htarget`, algebraicity of the total space of every `𝒢/ℬ`-torsor sheaf implies
  effectivity of descent for `p`.
* `AlgebraicGeometry.Space.FppfTorsors.hasEffectiveDescent_projection_iff`: granted `htarget`,
  effectivity of descent for `p` is equivalent to that algebraicity.
* `AlgebraicGeometry.Space.FppfTorsors.nonempty_isEquivalenceOver_iff_hasEffectiveDescent`:
  granted `htarget`, the comparison functor is an equivalence over the site if and only if
  descent for `p` is effective.

## References

* [Stacks Project, Tag 04UT](https://stacks.math.columbia.edu/tag/04UT)
* [Stacks Project, Tag 04UM](https://stacks.math.columbia.edu/tag/04UM)
* [Stacks Project, Tag 04U1](https://stacks.math.columbia.edu/tag/04U1)
* [Stacks Project, Tag 04US](https://stacks.math.columbia.edu/tag/04US)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} {hB : IsAlgebraicSpace 𝒞 S hS B}
  {G : GroupAlgebraicSpace 𝒞 S hS B hB}

namespace FppfTorsors

/-- If every descent datum of `𝒢/ℬ`-torsor sheaves along a covering sieve of the big fppf site
of `S` is effective (`htarget`, condition (3) of Stacks 04UM) and every `𝒢/ℬ`-torsor sheaf has an
algebraic space as total space (`halg`), then descent for `G-Torsors` is effective. -/
theorem hasEffectiveDescent_projection_of_isAlgebraicSpace_total
    (hB : IsAlgebraicSpace 𝒞 S hS B) (G : GroupAlgebraicSpace 𝒞 S hS B hB)
    (htarget : letI : (SheafTorsors.projection G.obj).IsFibered :=
        (SheafTorsors.projection_isFiberedInGroupoids G.obj).isFibered
      Functor.HasEffectiveDescent (SheafTorsors.projection G.obj)
        (BigFppfOver.topology 𝒞 S hS))
    (halg : ∀ T : SheafTorsors G.obj, IsAlgebraicSpace 𝒞 S hS T.total.left) :
    letI : (projection hB G).IsFibered :=
      (projection_isFiberedInGroupoids (hB := hB) (G := G)).isFibered
    Functor.HasEffectiveDescent (projection hB G) (BigFppfOver.topology 𝒞 S hS) := by
  let : (projection hB G).IsFibered :=
    (projection_isFiberedInGroupoids (hB := hB) (G := G)).isFibered
  let : (SheafTorsors.projection G.obj).IsFibered :=
    (SheafTorsors.projection_isFiberedInGroupoids G.obj).isFibered
  let : (BasedCategory.ofFunctor (projection hB G)).p.IsFibered :=
    (projection_isFiberedInGroupoids (hB := hB) (G := G)).isFibered
  let : (BasedCategory.ofFunctor (SheafTorsors.projection G.obj)).p.IsFibered :=
    (SheafTorsors.projection_isFiberedInGroupoids G.obj).isFibered
  exact (StacksRepresentableCFG.EquivalenceOver.toBasedEquivalence
      (𝒳 := BasedCategory.ofFunctor (projection hB G))
      (𝒴 := BasedCategory.ofFunctor (SheafTorsors.projection G.obj))
      (StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
        (comparison_comp_projection hB G)
        (isEquivalenceOverComparisonOfAlgebraic hB G halg))).symm.hasEffectiveDescent
    (BigFppfOver.topology 𝒞 S hS) htarget

/-- Granted effectivity of descent for `𝒢/ℬ`-torsor sheaves (`htarget`, condition (3) of
Stacks 04UM), descent for `G-Torsors` is effective if and only if every `𝒢/ℬ`-torsor sheaf has an
algebraic space as total space. -/
theorem hasEffectiveDescent_projection_iff (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G : GroupAlgebraicSpace 𝒞 S hS B hB)
    (htarget : letI : (SheafTorsors.projection G.obj).IsFibered :=
        (SheafTorsors.projection_isFiberedInGroupoids G.obj).isFibered
      Functor.HasEffectiveDescent (SheafTorsors.projection G.obj)
        (BigFppfOver.topology 𝒞 S hS)) :
    letI : (projection hB G).IsFibered :=
      (projection_isFiberedInGroupoids (hB := hB) (G := G)).isFibered
    (Functor.HasEffectiveDescent (projection hB G) (BigFppfOver.topology 𝒞 S hS) ↔
      ∀ T : SheafTorsors G.obj, IsAlgebraicSpace 𝒞 S hS T.total.left) :=
  ⟨fun hdesc => isAlgebraicSpace_total_of_hasEffectiveDescent hB G hdesc,
    hasEffectiveDescent_projection_of_isAlgebraicSpace_total hB G htarget⟩

/-- Granted effectivity of descent for `𝒢/ℬ`-torsor sheaves (`htarget`, condition (3) of
Stacks 04UM), the comparison functor `G-Torsors ⥤ 𝒢/ℬ-Torsors` is an equivalence over the big
fppf site of `S` if and only if descent for `G-Torsors` is effective. -/
theorem nonempty_isEquivalenceOver_iff_hasEffectiveDescent
    (hB : IsAlgebraicSpace 𝒞 S hS B) (G : GroupAlgebraicSpace 𝒞 S hS B hB)
    (htarget : letI : (SheafTorsors.projection G.obj).IsFibered :=
        (SheafTorsors.projection_isFiberedInGroupoids G.obj).isFibered
      Functor.HasEffectiveDescent (SheafTorsors.projection G.obj)
        (BigFppfOver.topology 𝒞 S hS)) :
    letI : (projection hB G).IsFibered :=
      (projection_isFiberedInGroupoids (hB := hB) (G := G)).isFibered
    (Nonempty (Functor.IsEquivalenceOver (projection hB G) (SheafTorsors.projection G.obj)
        (comparison hB G)) ↔
      Functor.HasEffectiveDescent (projection hB G) (BigFppfOver.topology 𝒞 S hS)) :=
  (nonempty_isEquivalenceOver_comparison_iff_isAlgebraicSpace_total hB G).trans
    (hasEffectiveDescent_projection_iff hB G htarget).symm

end FppfTorsors

end AlgebraicGeometry.Space

end
