module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineBundleDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineBundleReduced
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.BranchCover

/-!
# The branches over an integral closed subscheme of `D` are integral of δ-dimension one more

In the situation of [Stacks, Tag 0F97] let `W ⊆ Y` be an *integral* closed subscheme contained in
the divisor `D`, that is `zeroIdeal Y L₁ L₂ s ≤ W`. The case `W ⊆ D` of [Stacks, Tag 0F98] needs
each of the two branches `Wᵢ` of the base-changed diagram to be an integral closed subscheme of
`p^{-1}(W)` of δ-dimension one more than `W`, so that the union
`Stacks.Chow.TensorZeroScheme.Decomposition.inf_eq_bot_of_zeroIdeal_le` can be read as the
cycle identity `[p^{-1}W] = [W₁] + [W₂]`.

This file supplies the integrality and the δ-dimension. Clause (4) of the diagram presents
each branch as the total space of
`Stacks.Chow.TensorZeroScheme.branchSituation`, a line bundle over the base-changed divisor; and
that divisor is the whole of `W` because `s` restricts to zero on `W`
(`Stacks.Chow.TensorZeroScheme.zeroIdeal_pullbackTensorSection_subschemeι_eq_bot`). So the base of
the branch bundle is integral, and then
`Stacks.LineBundle.Situation.isIntegral_totalSpace` and
`Stacks.LineBundle.Situation.schemeDeltaDimension_totalSpaceToBase_comp` apply directly.

`IrreducibleSpace` alone is what `Stacks.Chow.schemeDeltaDimension_eq_add_of_flat` consumes, so
it is recorded separately; the full `AlgebraicGeometry.IsIntegral` is what step 2 of the case
`W ⊆ D` of [Stacks, Tag 0F98] needs in order to read a branch as a prime cycle through
`Stacks.Chow.extendCycleGroup_cycleAssociatedToClosedSubscheme`. Reducedness of the branch is not
visible from irreducibility: it comes from reducedness of the base through
`Stacks.Chow.isReduced_of_isAffineSpaceBundle`.

Because a branch is presented by an *isomorphism* onto the total space of the bundle — clause (4)
is the field `Stacks.Chow.TensorZeroScheme.Decomposition.branch₁` and its base-changed form is
`Stacks.Chow.TensorZeroScheme.BranchTransport.bcBranchIso` — the integrality is also stated for
an arbitrary scheme carrying such an isomorphism, which is what the consumers have in hand.

## Main results

* `Stacks.Chow.TensorZeroScheme.isIntegral_zeroIdeal_pullbackTensorSection_subscheme_of_le`:
  **the divisor of the base-changed diagram over an integral closed subscheme of `D` is
  integral**, being the whole of that subscheme.
* `Stacks.Chow.TensorZeroScheme.isIntegral_branchSituation_X_of_le`: the same, read as
  integrality of the base of the line bundle presenting a branch.
* `Stacks.Chow.TensorZeroScheme.irreducibleSpace_branchSituation_totalSpace_of_le`: **a branch of
  the base-changed diagram over an integral closed subscheme of `D` is irreducible.**
* `Stacks.Chow.TensorZeroScheme.isIntegral_branchSituation_totalSpace_of_le`: **such a branch is
  integral**, which is what reads it as a prime cycle.
* `Stacks.Chow.TensorZeroScheme.isIntegral_of_iso_branchSituation_totalSpace_of_le`: the same for
  any scheme identified with the branch, which is the form clause (4) of [Stacks, Tag 0F97]
  delivers.
* `Stacks.Chow.TensorZeroScheme.Decomposition.isIntegral_D₁_subscheme_of_zeroIdeal_le`,
  `Stacks.Chow.TensorZeroScheme.Decomposition.isIntegral_D₂_subscheme_of_zeroIdeal_le`: **the two
  branches of a decomposition over an integral closed subscheme of `D` are integral closed
  subschemes of its total space.**
* `Stacks.Chow.TensorZeroScheme.schemeDeltaDimension_branchSituation_of_le`: **such a branch has
  δ-dimension one more than the subscheme it lies over.**

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.PullbackTensorIso (pullbackTensorSection)

universe u

namespace Stacks.Chow.TensorZeroScheme

variable {Y : Scheme.{u}} (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)) (W : Y.IdealSheafData)

include h₁ h₂ in
/-- **The divisor of the base-changed diagram over an integral closed subscheme of `D` is
integral.** It is the whole subscheme, and the closed immersion of the trivial ideal sheaf is an
isomorphism. -/
theorem isIntegral_zeroIdeal_pullbackTensorSection_subscheme_of_le
    (hW : zeroIdeal Y L₁ L₂ s ≤ W) [IsIntegral W.subscheme] :
    IsIntegral (zeroIdeal W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)).subscheme := by
  rw [zeroIdeal_pullbackTensorSection_subschemeι_eq_bot L₁ L₂ s W hW]
  have : IsIso (⊥ : W.subscheme.IdealSheafData).subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot _).2 rfl
  exact IsIntegral.of_isIso (CategoryTheory.inv (⊥ : W.subscheme.IdealSheafData).subschemeι)

variable (N : W.subscheme.Modules)
  [hN : AlgebraicGeometry.SheafOfModules.IsInvertible W.subscheme.sheaf.obj
    W.subscheme.ringCatSheaf.property N]

include h₁ h₂ hN in
/-- The base of the line bundle presenting a branch of the base-changed diagram over an integral
closed subscheme of `D` is integral. This is
`Stacks.Chow.TensorZeroScheme.isIntegral_zeroIdeal_pullbackTensorSection_subscheme_of_le` at the
spelling `Stacks.Chow.TensorZeroScheme.branchSituation_X`, which is where the line-bundle results
read their base. -/
theorem isIntegral_branchSituation_X_of_le (hW : zeroIdeal Y L₁ L₂ s ≤ W)
    [IsIntegral W.subscheme] :
    IsIntegral (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s) N).X :=
  isIntegral_zeroIdeal_pullbackTensorSection_subscheme_of_le L₁ L₂ s W hW

include h₁ h₂ hN in
/-- **A branch of the base-changed diagram over an integral closed subscheme of `D` is
irreducible**, being the total space of a line bundle over an integral base. -/
theorem irreducibleSpace_branchSituation_totalSpace_of_le (hW : zeroIdeal Y L₁ L₂ s ≤ W)
    [IsIntegral W.subscheme] :
    IrreducibleSpace (branchSituation W.subscheme
      ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s) N).totalSpace :=
  have := isIntegral_branchSituation_X_of_le L₁ L₂ s W N hW
  Stacks.LineBundle.Situation.irreducibleSpace_totalSpace _

include h₁ h₂ hN in
/-- **A branch of the base-changed diagram over an integral closed subscheme of `D` is
integral**, being the total space of a line bundle over an integral base. This is what step 2 of
the case `W ⊆ D` of [Stacks, Tag 0F98] needs in order to read the branch as a prime cycle:
irreducibility alone does not suffice, and the reducedness comes from reducedness of the base. -/
theorem isIntegral_branchSituation_totalSpace_of_le (hW : zeroIdeal Y L₁ L₂ s ≤ W)
    [IsIntegral W.subscheme] :
    IsIntegral (branchSituation W.subscheme
      ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s) N).totalSpace :=
  have := isIntegral_branchSituation_X_of_le L₁ L₂ s W N hW
  Stacks.LineBundle.Situation.isIntegral_totalSpace _

include h₁ h₂ hN in
/-- **A scheme identified with a branch of the base-changed diagram over an integral closed
subscheme of `D` is integral.** Clause (4) of [Stacks, Tag 0F97] presents a branch only up to
isomorphism — as the field `Stacks.Chow.TensorZeroScheme.Decomposition.branch₁`, or after base
change as `Stacks.Chow.TensorZeroScheme.BranchTransport.bcBranchIso` — so this is the form in
which the branches of the dévissage are integral. -/
theorem isIntegral_of_iso_branchSituation_totalSpace_of_le (hW : zeroIdeal Y L₁ L₂ s ≤ W)
    [IsIntegral W.subscheme] {Z : Scheme.{u}}
    (e : Z ≅ (branchSituation W.subscheme
      ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s) N).totalSpace) :
    IsIntegral Z :=
  have := isIntegral_branchSituation_totalSpace_of_le L₁ L₂ s W N hW
  IsIntegral.of_isIso e.inv

include h₁ h₂ in
/-- **The first branch of a decomposition over an integral closed subscheme of `D` is an integral
closed subscheme of its total space.** This is the cycle `[W₁]` of the case `W ⊆ D` of
[Stacks, Tag 0F98]. -/
theorem Decomposition.isIntegral_D₁_subscheme_of_zeroIdeal_le (hW : zeroIdeal Y L₁ L₂ s ≤ W)
    [IsIntegral W.subscheme]
    (R : Decomposition W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)) :
    IsIntegral R.D₁.subscheme :=
  isIntegral_of_iso_branchSituation_totalSpace_of_le L₁ L₂ s W _ hW R.branch₁

include h₁ h₂ in
/-- **The second branch of a decomposition over an integral closed subscheme of `D` is an integral
closed subscheme of its total space.** This is the cycle `[W₂]` of the case `W ⊆ D` of
[Stacks, Tag 0F98]. -/
theorem Decomposition.isIntegral_D₂_subscheme_of_zeroIdeal_le (hW : zeroIdeal Y L₁ L₂ s ≤ W)
    [IsIntegral W.subscheme]
    (R : Decomposition W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)) :
    IsIntegral R.D₂.subscheme :=
  isIntegral_of_iso_branchSituation_totalSpace_of_le L₁ L₂ s W _ hW R.branch₂

include h₁ h₂ hN in
/-- **A branch of the base-changed diagram over an integral closed subscheme of `D` of
δ-dimension `n` has δ-dimension `n + 1`.** This is the value the dévissage of
[Stacks, Tag 0F98] reads off each of `W₁` and `W₂`: with `W` of δ-dimension `k + 1` the branches
have `k + 2`, which is one more than the intersection `W₁ ∩ W₂ ≅ W`, so the fundamental cycle of
the union splits as the sum of the two. -/
theorem schemeDeltaDimension_branchSituation_of_le (C : Stacks.Chow.ChowSituation.{u})
    (sD : (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s) N).X ⟶ C.S)
    [LocallyOfFiniteType sD] (hW : zeroIdeal Y L₁ L₂ s ≤ W) [IsIntegral W.subscheme] {n : ℤ}
    (hn : Stacks.Chow.schemeDeltaDimension C sD = (n : EInt)) :
    Stacks.Chow.schemeDeltaDimension C
        ((branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)
          (pullbackTensorSection W.subschemeι L₁ L₂ s) N).totalSpaceToBase ≫ sD) =
      ((n + 1 : ℤ) : EInt) :=
  have := isIntegral_branchSituation_X_of_le L₁ L₂ s W N hW
  Stacks.LineBundle.Situation.schemeDeltaDimension_totalSpaceToBase_comp C _ sD hn

end Stacks.Chow.TensorZeroScheme

end
