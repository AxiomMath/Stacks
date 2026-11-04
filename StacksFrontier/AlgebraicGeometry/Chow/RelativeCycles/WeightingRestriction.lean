module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Weighting
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FlatLength

/-!
# The weighting of a family of zero-cycles restricted to an open subscheme

Restricting a family of `0`-cycles on the fibres of `f : X ⟶ S` along an open immersion
`j : U ⟶ X` restricts the function `w_α` accordingly: `w_{α|_U} = w_α ∘ j`. The coefficients
agree because the restriction of a fibrewise cycle is read at the image point, and the
inseparable degrees agree because an open immersion is étale, so the square
`j ≫ f = (j ≫ f) ≫ 𝟙` is an étale base-change square.

## Main results

* `Stacks.Chow.relativeCycleWeight_fiberCycleRestrict` — the displayed identity.

## References

* [Stacks Project, Tag 0H5P](https://stacks.math.columbia.edu/tag/0H5P)
* [Stacks Project, Tag 0H51](https://stacks.math.columbia.edu/tag/0H51)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- The point of the fibre of `U/S` attached to a point of `U` maps to the point of the fibre of
`X/S` attached to its image under an open immersion `j : U ⟶ X` over `S`. -/
theorem fiberRestrict_asFiber {X S U : Scheme.{u}} (f : X ⟶ S) (j : U ⟶ X)
    [IsOpenImmersion j] (x : U) :
    fiberRestrict f (j ≫ f) j rfl ((j ≫ f) x) ((j ≫ f).asFiber x) = f.asFiber (j x) := by
  refine (f.fiberι ((j ≫ f) x)).isEmbedding.injective ?_
  have hmap := congrArg (fun m : (j ≫ f).fiber ((j ≫ f) x) ⟶ X => m ((j ≫ f).asFiber x))
    (fiberRestrict_fiberι f (j ≫ f) j rfl ((j ≫ f) x))
  change f.fiberι ((j ≫ f) x) (fiberRestrict f (j ≫ f) j rfl ((j ≫ f) x) ((j ≫ f).asFiber x)) =
    j ((j ≫ f).fiberι ((j ≫ f) x) ((j ≫ f).asFiber x)) at hmap
  rw [hmap, Scheme.Hom.fiberι_asFiber]
  exact (f.fiberι_asFiber (j x)).symm

/-- **Stacks Project, Tag 0H5P.** The function `w_α` attached to the restriction of a family of
`0`-cycles along an open immersion of the source is the restriction of `w_α`. -/
theorem relativeCycleWeight_fiberCycleRestrict {X S U : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] (j : U ⟶ X) [IsOpenImmersion j]
    (α : FamilyOfCycles f 0) (x : U) :
    relativeCycleWeight (j ≫ f)
        (fun s ↦ fiberCycleRestrict f (j ≫ f) j rfl s 0 (α s)) x =
      relativeCycleWeight f α (j x) := by
  have hdeg := (AlgebraicGeometry.finInsepDegree_residueField_eq_of_etale_square f j (j ≫ f)
    (𝟙 S) (by simp) x).symm
  rw [relativeCycleWeight_apply, relativeCycleWeight_apply, fiberCycleRestrict_apply,
    fiberRestrict_asFiber f j x]
  exact congrArg _ (congrArg _ hdeg)

end Stacks.Chow

end
