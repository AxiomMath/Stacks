module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedDirectSum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubspaceReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRestrictedData
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheaf

/-!
# The difference of two lifts into an undeformed target

Let `Z ⊂ X` be a first order thickening of algebraic spaces over a scheme `S` and let
`c, c' : X ⟶ W` be two morphisms whose restrictions to `Z` agree.  To read their difference as
an `𝒪_Z`-linear map out of the pulled back differentials one has to know hypothesis (2) of
[Stacks Project, Tag 0618]: that the two comorphisms agree on the sections killed by the
reduction of the closed subspace `W₀ ⊆ W` through which the common restriction factors.
`AlgebraicGeometry.Space.restrictedLiftDifferenceData` carries it as the hypothesis `hker`.

This file discharges that hypothesis **when the target is not deformed**, that is when
`W₀ = W`.  Then the kernel of the reduction is the conormal module `𝒞_{W/W}`, which vanishes —
Remark [Stacks Project, Tag 061D], `AlgebraicGeometry.Space.isZero_conormalModule_top` — so the
kernel has no nonzero sections at all and the agreement is vacuous.  This is the case the sheaf
of lifts of [Stacks Project, Tag 061A] is formed in, and the case Remark
[Stacks Project, Tag 061D] singles out by saying that the map `A` of the general lifting problem
is always zero.

## Main results

* `AlgebraicGeometry.Space.eq_zero_of_app_structureSharpRingInverseImage_top`: a section of
  `j^{-1}𝒪_W` killed by `j^♯` is zero when `j` is the inclusion of the top closed subspace.
* `AlgebraicGeometry.Space.restrictedSharpThroughThickening_app_eq_of_top`: **hypothesis (2) of
  [Stacks Project, Tag 0618] for an undeformed target**, in the shape
  `AlgebraicGeometry.Space.restrictedLiftDifferenceData` consumes it.

## Implementation notes

The vanishing of the kernel is read through
`AlgebraicGeometry.Space.exists_conormalInverseImageι_eq`, which needs the inclusion of the top
subspace to be a first order thickening; that is
`AlgebraicGeometry.Space.isNthOrderThickening_top` at `n = 1`.  No hypothesis on `W` is used
beyond its being an algebraic space, and no hypothesis relating `c` and `c'` beyond the two
restriction identities the datum already asks for: the conclusion is an identity between the
two comorphisms at a section which is itself zero.

The statement is not a specialisation of
`AlgebraicGeometry.Space.restrictedSharpThroughThickening_app_eq_of_mem_span`, which asks for a
generating family of the kernel over a covering sieve on which the two comorphisms agree.  Here
the kernel is zero, so no family is produced and no covering sieve is used.

## References

* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618), whose hypothesis (2)
  this is.
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D), the remark that the
  map `A` vanishes when the target is not deformed.
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN), the conormal module.
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK), thickenings.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A section of `j^{-1}𝒪_W` killed by `j^♯` vanishes when `W₀ = W`.**  The kernel of the
reduction of a first order thickening is the conormal module, by
`AlgebraicGeometry.Space.exists_conormalInverseImageι_eq`; the top closed subspace is a first
order thickening, by `AlgebraicGeometry.Space.isNthOrderThickening_top`, and its conormal
module vanishes, by `AlgebraicGeometry.Space.isZero_conormalModule_top`. -/
theorem eq_zero_of_app_structureSharpRingInverseImage_top (W : AlgebraicSpaces B S hS)
    (V : (SmallEtale B S hS
      (⟨(⊤ : Subfunctor W.1).toFunctor, (isClosedSubspace_top B S hS W).1⟩ :
        AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : (structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS W ⟨⊤, isClosedSubspace_top B S hS W⟩)).obj.obj V)
    (hx : (structureSharpRingInverseImage B S hS
      (subspaceInclusion B S hS W ⟨⊤, isClosedSubspace_top B S hS W⟩)).hom.app V x = 0) :
    x = 0 := by
  obtain ⟨m, hm⟩ := exists_conormalInverseImageι_eq B S hS
    ⟨⊤, isClosedSubspace_top B S hS W⟩ (isNthOrderThickening_top B S hS 1 W) V x hx
  have hz := Functor.map_isZero
    (SheafOfModules.restrictScalars (structureSharpRingInverseImage B S hS
      (subspaceInclusion B S hS W ⟨⊤, isClosedSubspace_top B S hS W⟩)))
    (isZero_conormalModule_top B S hS W)
  have hm0 : m = 0 := (Stacks.subsingleton_of_isZero hz V).elim m 0
  rw [← hm, hm0, map_zero]
  rfl

/-- **Hypothesis (2) of [Stacks Project, Tag 0618] for an undeformed target.**  For two
morphisms `c, c' : X ⟶ W` whose restrictions to the thickening `Z ⊂ X` are both `e₀` read
through the inclusion of the *top* closed subspace of `W`, the two transported comorphisms
agree on every section killed by the reduction: there are no such sections but zero, by
`AlgebraicGeometry.Space.eq_zero_of_app_structureSharpRingInverseImage_top`.

This is the hypothesis `hker` of
`AlgebraicGeometry.Space.restrictedLiftDifferenceData`, discharged in the case of
Remark [Stacks Project, Tag 061D]: the target of the lifting problem is not deformed, so the
map `A` out of the conormal module `𝒞_{W/W}` is zero. -/
theorem restrictedSharpThroughThickening_app_eq_of_top {X W : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS X.1)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨(⊤ : Subfunctor W.1).toFunctor, (isClosedSubspace_top B S hS W).1⟩ :
        AlgebraicSpaces B S hS))
    (c c' : X ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c =
      e₀ ≫ subspaceInclusion B S hS W ⟨⊤, isClosedSubspace_top B S hS W⟩)
    (h' : subspaceInclusion B S hS X Z ≫ c' =
      e₀ ≫ subspaceInclusion B S hS W ⟨⊤, isClosedSubspace_top B S hS W⟩)
    (V : (SmallEtale B S hS
      (⟨(⊤ : Subfunctor W.1).toFunctor, (isClosedSubspace_top B S hS W).1⟩ :
        AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : (structureRingSheafInverseImage B S hS
      (subspaceInclusion B S hS W ⟨⊤, isClosedSubspace_top B S hS W⟩)).obj.obj V)
    (hx : (structureSharpRingInverseImage B S hS
      (subspaceInclusion B S hS W ⟨⊤, isClosedSubspace_top B S hS W⟩)).hom.app V x = 0) :
    (restrictedSharpThroughThickening B S hS Z
        ⟨⊤, isClosedSubspace_top B S hS W⟩ c e₀ h).hom.app V x =
      (restrictedSharpThroughThickening B S hS Z
        ⟨⊤, isClosedSubspace_top B S hS W⟩ c' e₀ h').hom.app V x := by
  rw [eq_zero_of_app_structureSharpRingInverseImage_top B S hS W V x hx, map_zero, map_zero]

end AlgebraicGeometry.Space

end
