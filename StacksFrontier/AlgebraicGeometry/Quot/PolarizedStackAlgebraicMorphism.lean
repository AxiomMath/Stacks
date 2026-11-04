module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesForget
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.StackOfSpacesStack
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicMorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical
public import StacksFrontier.CategoryTheory.Sites.Localization.StacksOverSlice
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge

/-!
# The forgetful 1-morphism `Polarized ⟶ Spaces'_{fp, flat, proper}`

Stacks 0D41 says that the forgetful functor (0D3Y)

```text
  Polarized ⟶ Spaces'_{fp, flat, proper},   (X ⟶ S, ℒ) ↦ (X ⟶ S)
```

is a 1-morphism of stacks in groupoids over `Sch_fppf` which is algebraic in the sense of
Stacks 06CF. The notion of Stacks 06CF in this library,
`AlgebraicGeometry.Stack.IsAlgebraicMorphism`, takes a 1-morphism between two
`CategoryTheory.StackInGroupoids` over the big fppf site of a base scheme. The absolute site
`Sch_fppf` is the big fppf site of the terminal scheme `AlgebraicGeometry.integerBase`, and this
file presents both sides as stacks in groupoids over that site.

* `Spaces'_{fp, flat, proper}` is a stack in groupoids over the big fppf site of any scheme by
  Stacks 0D1G, `AlgebraicGeometry.cartesianProperFlatProjection_isStackInGroupoids`.
* `Polarized` is read over the big fppf site of the terminal scheme through the forgetful functor
  followed by the projection of `Spaces'_{fp, flat, proper}`,
  `AlgebraicGeometry.polarizedIntegerProjection`, so that the forgetful functor lies over that
  site on the nose. It is fibred in groupoids by Stacks 0D3Z, and it is a stack over the slice
  once it is a stack over the site itself (Construction B of Stacks 04WV,
  `CategoryTheory.Over.isStack_of_comp_forget`). That the polarized families form a stack over
  the site is the second assertion of Stacks 0D40, a hypothesis of
  `AlgebraicGeometry.polarizedStackInGroupoids`.
* The forgetful functor of Stacks 0D3Y, `AlgebraicGeometry.forgetPolarization`, is a functor
  over the big fppf site of the terminal scheme between the two, on the nose.

## Main definitions

* `AlgebraicGeometry.properFlatSpacesStackInGroupoids`: `Spaces'_{fp, flat, proper}` as a stack
  in groupoids.
* `AlgebraicGeometry.polarizedIntegerProjection`: the projection of `Polarized` to the big fppf
  site of the terminal scheme.
* `AlgebraicGeometry.polarizedStackInGroupoids`: `Polarized` as a stack in groupoids over
  the big fppf site of the terminal scheme, given the second assertion of Stacks 0D40.
* `AlgebraicGeometry.forgetPolarizationBased`: the forgetful functor of Stacks 0D3Y as a
  1-morphism of categories over the big fppf site of the terminal scheme.

## Main results

* `AlgebraicGeometry.polarizedIntegerProjection_isFiberedInGroupoids`: that projection is fibred
  in groupoids.
* `AlgebraicGeometry.polarizedIntegerProjection_isStack`: that projection is a stack, given the
  second assertion of Stacks 0D40.

## References

* [Stacks Project, Tag 0D41](https://stacks.math.columbia.edu/tag/0D41)
* [Stacks Project, Tag 0D3Y](https://stacks.math.columbia.edu/tag/0D3Y)
* [Stacks Project, Tag 0D40](https://stacks.math.columbia.edu/tag/0D40)
* [Stacks Project, Tag 0D1G](https://stacks.math.columbia.edu/tag/0D1G)
* [Stacks Project, Tag 04WV](https://stacks.math.columbia.edu/tag/04WV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry

/-! ### `Spaces'_{fp, flat, proper}` as a stack in groupoids -/

section ProperFlat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `Spaces'_{fp, flat, proper}` over the big fppf site of `S`, as a stack in groupoids
(Stacks 0D1G). -/
def properFlatSpacesStackInGroupoids :
    StackInGroupoids.{w} (BigFppfOver B S hS) (BigFppfOver.topology B S hS) where
  toBasedCategory := BasedCategory.ofFunctor (cartesianProperFlatProjection B S hS)
  isStackInGroupoids := cartesianProperFlatProjection_isStackInGroupoids B S hS

end ProperFlat

/-! ### `Polarized` over the big fppf site of the terminal scheme -/

section Polarized

variable (B : BigFppfSite.{u})

/-- `Polarized` over the big fppf site of the terminal scheme: a polarized family is sent to its
base scheme with its unique morphism to the terminal scheme, which is the base of the family of
algebraic spaces it polarizes. -/
abbrev polarizedIntegerProjection :
    PolarizedFamily B ⥤ BigFppfOver B integerBase B.contains_integerBase :=
  forgetPolarization B ⋙ cartesianProperFlatProjection B integerBase B.contains_integerBase

/-- The projection of `Polarized` to the big fppf site of the terminal scheme is fibred in
groupoids (Stacks 0D3Z, read over the slice at the terminal scheme, Stacks 02XT). -/
theorem polarizedIntegerProjection_isFiberedInGroupoids :
    (polarizedIntegerProjection B).IsFiberedInGroupoids :=
  Functor.IsFiberedInGroupoids.of_comp_over _ (polarizedProjection B) _ rfl
    polarizedProjection_isFiberedInGroupoids_unconditional

/-- If the polarized families form a stack over the big fppf site (the second assertion of
Stacks 0D40), they form a stack over the big fppf site of the terminal scheme (Construction B of
Stacks 04WV). -/
theorem polarizedIntegerProjection_isStack (h : (polarizedProjection B).IsStack B.topology) :
    (polarizedIntegerProjection B).IsStack
      (BigFppfOver.topology B integerBase B.contains_integerBase) :=
  Over.isStack_of_comp_forget _
    ((isSheaf_iff_isSheaf_of_type B.topology _).2
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)) h

/-- `Polarized` as a stack in groupoids over the big fppf site of the terminal scheme, from the
second assertion `h` of Stacks 0D40. -/
def polarizedStackInGroupoids (h : (polarizedProjection B).IsStack B.topology) :
    StackInGroupoids.{w} (BigFppfOver B integerBase B.contains_integerBase)
      (BigFppfOver.topology B integerBase B.contains_integerBase) where
  toBasedCategory := BasedCategory.ofFunctor (polarizedIntegerProjection B)
  isStackInGroupoids := (polarizedIntegerProjection_isStack B h).isStackInGroupoids
    (polarizedIntegerProjection_isFiberedInGroupoids B)

/-- **The forgetful functor of Stacks 0D3Y as a 1-morphism** from `Polarized` to
`Spaces'_{fp, flat, proper}`, both read over the big fppf site of the terminal scheme. -/
def forgetPolarizationBased :
    BasedCategory.ofFunctor (polarizedIntegerProjection B) ⥤ᵇ
      BasedCategory.ofFunctor
        (cartesianProperFlatProjection B integerBase B.contains_integerBase) where
  toFunctor := forgetPolarization B
  w := rfl

end Polarized

end AlgebraicGeometry

end
