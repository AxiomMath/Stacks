module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.FiniteCoverDescent

/-!
# The category `ℋ_d` of degree-`d` finite locally free covers is a stack in groupoids

Let `S` be a scheme contained in a big fppf site `B` and let `d` be a natural number. This file
assembles the three conditions of Stacks 02ZI for the category `ℋ_d` of degree-`d` finite locally
free covers of `AlgebraicGeometry.Stack.finiteCoverCategory` over the big fppf site of `S` into a
term of `CategoryTheory.Functor.IsStackInGroupoids`.

## Main results

* `AlgebraicGeometry.Stack.isStackInGroupoids_finiteCoverProjection`: the category `ℋ_d` of
  degree-`d` finite locally free covers is a stack in groupoids over the big fppf site of `S`.
* `AlgebraicGeometry.Stack.finiteCoverStack`: `ℋ_d` as a bundled stack in groupoids over that
  site.

## References

* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
* [Stacks Project, Tag 05WB](https://stacks.math.columbia.edu/tag/05WB)
* [Stacks Project, Tag 05WC](https://stacks.math.columbia.edu/tag/05WC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}

/-- **The category `ℋ_d` of degree-`d` finite locally free covers is a stack in groupoids over
the big fppf site of `S`.** -/
@[stacks 05WB "The category `ℋ_d` of degree-`d` finite locally free covers, i.e. the case
`𝒳 = 𝒴 = S` of the source's `ℋ_d(𝒳/𝒴)`, is a stack in groupoids over the big fppf site of `S`.
All three conditions of Stacks 02ZI are discharged: condition (1) is
`AlgebraicGeometry.Stack.isFiberedInGroupoids_finiteCoverProjection`, condition (2) is
`AlgebraicGeometry.Stack.isom_isSheaf_finiteCoverProjection`, and condition (3), effectivity of
descent data, is `AlgebraicGeometry.Stack.descentDatum_isEffective_finiteCoverProjection`.",
  sga "3 IV 4.5.13" "special case"]
theorem isStackInGroupoids_finiteCoverProjection :
    (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsStackInGroupoids.{w}
      (BigFppfOver.topology B S hS) :=
  ⟨isFiberedInGroupoids_finiteCoverProjection, isom_isSheaf_finiteCoverProjection,
    descentDatum_isEffective_finiteCoverProjection⟩

/-- The category `ℋ_d` of degree-`d` finite locally free covers as a bundled stack in groupoids
over the big fppf site of `S`. -/
def finiteCoverStack (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (d : ℕ) :
    StackInGroupoids.{w, u, u, u + 1, u + 1} (BigFppfOver B S hS)
      (BigFppfOver.topology B S hS) where
  toBasedCategory := finiteCoverCategory (B := B) (S := S) (hS := hS) (d := d)
  isStackInGroupoids := isStackInGroupoids_finiteCoverProjection

end AlgebraicGeometry.Stack

end
