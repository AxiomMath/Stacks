module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleEquivalence
public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierDerivedSheafHom
public import StacksFrontier.CategoryTheory.Monoidal.UnitEndomorphismCentral

/-!
# `Hom_{𝒪_X}(i_* 𝒩, 𝒪_X(D)) = 0` for an effective Cartier divisor

Let `X` be a scheme and `D ⊆ X` an effective Cartier divisor with closed immersion `i : D ⟶ X`,
invertible sheaf `𝒪_X(D)` and normal sheaf `𝒩 = i^* 𝒪_X(D)`. This file proves that there is no
nonzero morphism of `𝒪_X`-modules

`i_* 𝒩 ⟶ 𝒪_X(D)`,

which is one of the three inputs of
`Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport_of_dualTriangleFirstMap`,
the triangulated comparison of [Stacks, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B).

## The argument

The normal short exact sequence `0 ⟶ 𝒪_X ⟶ 𝒪_X(D) ⟶ i_* 𝒩 ⟶ 0`
(`Stacks.Divisors.normalShortComplex_shortExact`) has its second map epimorphic and its first
monomorphic, and the composite vanishes. So a morphism `w : i_* 𝒩 ⟶ 𝒪_X(D)` is zero as soon as
`g ≫ w` is, and `g ≫ w` is an endomorphism `k` of `𝒪_X(D)` with `f ≫ k = 0`, where `f` is
multiplication by the canonical section `1_D`.

That is exactly the hypothesis of
`CategoryTheory.MonoidalCategory.eq_zero_of_mono_unit_comp_eq_zero`: `𝒪_X(D)` is invertible, so
every endomorphism of it is multiplication by a global function, by the centrality of the
endomorphisms of the tensor unit; `f` is a monomorphism out of the tensor unit, so that function
is zero, so `k` is.

## Main results

* `Stacks.Divisors.hom_normalQuotient_divisorSheaf_eq_zero`: **`Hom_{𝒪_X}(i_* 𝒩, 𝒪_X(D)) = 0`.**

## Implementation notes

The monoidal structure used is `Stacks.SheafOfModules.monoidalCategory`, at the index
`(X.presheaf, (structureSheafRing X.toRingedSpace).property)` — the one
`Stacks.Divisors.isTensorInvertible_invertibleSheaf` is stated at, so that the tensor inverse of
`𝒪_X(D)` is obtained from it by `Stacks.SheafOfModules.hasInverse_of_isInvertible` with no
transport. Its tensor unit is `SheafOfModules.unit` on the nose
(`Stacks.SheafOfModules.tensorUnit_eq`), hence equal to the first term
`Stacks.Divisors.structureModule` of the normal sequence.

`Stacks.Divisors.divisorSheafHasInverse` ascribes its object to that spelling of the category of
modules of `X`; without the ascription the `MonoidalCategory` instance is not found. For the same
reason the vanishing of the composite of the normal sequence is read off in term style, with
`Category.assoc` and `congrArg`: the `rw` form of the same step reports the target as not
type-correct at `implicit` transparency, `divisorSheaf D` being spelled over `X.Modules` while
the tensor unit of the monoidal structure is spelled over
`SheafOfModules (TensorSheafification.structureSheaf X.presheaf _)`.

## References

* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

universe u

namespace Stacks.Divisors

attribute [local instance] Stacks.SheafOfModules.monoidalCategory

variable {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]

/-- **A two-sided tensor inverse of `𝒪_X(D)`**, for an effective Cartier divisor `D`: the sheaf
`𝒪_X(D)` is invertible (`Stacks.Divisors.isTensorInvertible_invertibleSheaf`), and an invertible
sheaf of modules has a two-sided tensor inverse by [Stacks, Tag 0FFN].

The object is ascribed to the spelling of the category of modules of `X` that the monoidal
structure `Stacks.SheafOfModules.monoidalCategory` is indexed by; instance search does not find
the monoidal structure at the `X.Modules` spelling. -/
def divisorSheafHasInverse :
    MonoidalCategory.HasInverse
      (C := SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        X.presheaf (structureSheafRing X.toRingedSpace).property))
      (divisorSheaf D) :=
  haveI := isTensorInvertible_invertibleSheaf D
  Stacks.SheafOfModules.hasInverse_of_isInvertible X.presheaf
    (structureSheafRing X.toRingedSpace).property (invertibleSheaf' D)

/-- **`Hom_{𝒪_X}(i_* 𝒩, 𝒪_X(D)) = 0`** for an effective Cartier divisor `D`, where
`𝒩 = i^* 𝒪_X(D)` is its normal sheaf: every morphism of `𝒪_X`-modules from the third term of the
normal short exact sequence to `𝒪_X(D)` vanishes.

This is one of the three inputs of
`Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport_of_dualTriangleFirstMap`.

Composing with the epimorphism `g : 𝒪_X(D) ⟶ i_* 𝒩` of the normal sequence turns the assertion
into the vanishing of an endomorphism of `𝒪_X(D)` killed by multiplication by the canonical
section `1_D`, which is a monomorphism out of the tensor unit; that vanishing is
`CategoryTheory.MonoidalCategory.eq_zero_of_mono_unit_comp_eq_zero` at the tensor inverse
`Stacks.Divisors.divisorSheafHasInverse`. -/
theorem hom_normalQuotient_divisorSheaf_eq_zero
    (w : (normalShortComplex D).X₃ ⟶ divisorSheaf D) : w = 0 := by
  have : Epi (normalShortComplex D).g := (normalShortComplex_shortExact D).epi_g
  have hk : (normalShortComplex D).g ≫ w = 0 := by
    refine MonoidalCategory.eq_zero_of_mono_unit_comp_eq_zero (divisorSheafHasInverse D)
      (f := (normalShortComplex D).f) (normalShortComplex_shortExact D).mono_f ?_
    exact ((Category.assoc (normalShortComplex D).f (normalShortComplex D).g w).symm.trans
      (congrArg (fun t => t ≫ w) (normalShortComplex D).zero)).trans zero_comp
  exact (cancel_epi (normalShortComplex D).g).mp (hk.trans (comp_zero).symm)

end Stacks.Divisors

end
