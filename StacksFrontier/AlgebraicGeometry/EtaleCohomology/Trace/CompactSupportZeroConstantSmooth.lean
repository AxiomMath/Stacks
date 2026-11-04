module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportZeroConstant

/-!
# `H⁰_c` of a constant sheaf on an affine scheme compactified by a smooth proper curve

Let `X` be affine, separated of finite type over a finite field `k`, with a compactification
`j : X ⟶ X̄` such that `X̄` is smooth of relative dimension one over `k` (and proper), and let `k̄`
be an algebraically closed extension of `k`. Then `H⁰_c(X_k̄, M) = 0` for every constant sheaf `M`:
no nonempty clopen subset of `X̄_k̄` lies in the affine `X_k̄`
(`AlgebraicGeometry.eq_empty_of_isClopen_of_subset_range_of_isAffine`), so
`Stacks.EtaleCohomology.isZero_compactSupportFrobeniusCohomologyGroup_zero_constant` applies.
This generalizes
`Stacks.EtaleCohomology.isZero_compactSupportFrobeniusCohomologyGroup_zero_constant_of_isAffine`
from the compactification of a finite étale cover to any such compactification, as needed for
the non-projective assertion of [Tag 03VL](https://stacks.math.columbia.edu/tag/03VL) on an open
of a cover.

## Main results

* `Stacks.EtaleCohomology.isZero_compactSupportFrobeniusCohomologyGroup_zero_constant_of_smooth`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Constant

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
  [SmoothOfRelativeDimension 1 j.toBase] [IsAffine X] (kbar : Type u) [Field kbar]
  [IsAlgClosed kbar] [Algebra k kbar] (Λ : Type) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)

omit [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [IsAlgClosed kbar] in
/-- **`H⁰_c(X_k̄, M) = 0` for a constant sheaf on an affine `X` with a compactification by a
proper smooth curve over `k`**: no nonempty clopen subset of `X̄_k̄` lies in the affine `X_k̄`. -/
theorem isZero_compactSupportFrobeniusCohomologyGroup_zero_constant_of_smooth :
    IsZero (compactSupportFrobeniusCohomologyGroup.{u, 0} Λ f j kbar
      ⟨(CochainComplex.singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M),
        CochainComplex.plus_singleFunctor_obj _⟩ 0) := by
  refine isZero_compactSupportFrobeniusCohomologyGroup_zero_constant f j kbar Λ M
    fun Z hZ hne => ?_
  have : SmoothOfRelativeDimension 1 (pullback.snd j.toBase (specAlgebraMap k kbar)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback _ _) (inferInstanceAs (SmoothOfRelativeDimension 1 j.toBase))
  by_contra hcon
  push Not at hcon
  have hsub : Z ⊆ Set.range (compactificationFieldBaseChangeImmersion f j kbar) :=
    fun y hy => hcon y hy
  exact hne.ne_empty (eq_empty_of_isClopen_of_subset_range_of_isAffine
    (pullback.snd j.toBase (specAlgebraMap k kbar))
    (compactificationFieldBaseChangeImmersion f j kbar) Z hZ hsub)

end Constant

end Stacks.EtaleCohomology

end
