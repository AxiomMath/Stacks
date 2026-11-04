module

public import StacksFrontier.AlgebraicGeometry.QuasiAffineFiniteNonvanishing.Basic

/-!
# Stacks Tag 0F20 needs no affineness input

The route to Stacks Tag 0F20 in
`StacksFrontier/AlgebraicGeometry/QuasiAffineFiniteNonvanishing/Basic.lean` reduces the statement to
**two** hypotheses: pointwise global generation of `L`, and a consequence of Stacks Tag 01PV
(`U ⊓ X_s` is affine for every affine open `U`), carried there as
`Stacks.QuasiAffineFiniteNonvanishing.IsAffineNonvanishingOfLe`. This file removes the second
one. Tag 01PV is not needed for Tag 0F20.

The reason is a one-line change in where prime avoidance is applied. That route picks `g` with
`E ⊆ X_g ≤ W` and then has to prove `X_{g s} = X_g ⊓ X_s` affine from the ambient affine `X_g`,
which is Tag 01PV. Applying avoidance inside `W ⊓ X_s` instead -- an open which still contains
`E`, because `E ⊆ X_s` is the standing hypothesis -- gives `X_g ≤ X_s`, whence
`X_{g s} = X_g ⊓ X_s` is `X_g` *itself*, already affine because that is what avoidance produces.
Nothing about affineness of nonvanishing loci is used, and the section produced is the same
`g • s`.

## Main results

* `Stacks.QuasiAffineGlobalGeneration.nonvanishingOpen_smul_of_le`: if `X_g ≤ X_s` then `X_{g s} =
X_g`.
* `Stacks.QuasiAffineGlobalGeneration.exists_affine_nonvanishingOpen_of_nonvanishing`: Stacks Tag
  0F20's conclusion from a single global section not vanishing on `E`, with no further hypothesis.

## References

* [Stacks Project, Tag 0F20](https://stacks.math.columbia.edu/tag/0F20)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)

## What is not done

No `stacks` attribute is attached here: the hypothesis `E ⊆ X_{s₀}` is discharged in
`StacksFrontier/AlgebraicGeometry/QuasiAffineGlobalGeneration/Basic.lean`, which is where the label
sits.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.Ample Stacks.ModuleStalk Stacks.NonvanishingOpen

universe u

namespace Stacks.QuasiAffineGlobalGeneration

variable {X : Scheme.{u}}

/-- **Scaling by a function that vanishes nowhere on `X_s` cuts `X_s` down to its basic open.**
If `X_g ≤ X_s` then `X_{g s} = X_g ⊓ X_s = X_g`. -/
theorem nonvanishingOpen_smul_of_le (L : X.Modules) [IsInvertibleModule X L] (g : Γ(X, ⊤))
    (s : Γ(L, ⊤)) (hg : X.basicOpen g ≤ nonvanishingOpen X L s) :
    nonvanishingOpen X L (g • s) = X.basicOpen g := by
  refine Opens.ext ?_
  rw [coe_nonvanishingOpen, nonvanishingLocus_smul]
  exact Set.inter_eq_self_of_subset_left fun x hx => hg hx

/-- **Stacks Tag 0F20 from one nonvanishing section, with no second input.** Given a global
section `s₀` of the invertible `L` not vanishing anywhere on the finite set `E ⊆ W`, prime
avoidance inside `W ⊓ X_{s₀}` produces `g` with `X_g` affine and `E ⊆ X_g ≤ W ⊓ X_{s₀}`; then
`X_{g s₀} = X_g`, so it is affine, contains `E` and lies in `W`.

Stacks Tag 01PV, which the source and the earlier route in
`F3/QuasiAffineFiniteNonvanishing/` both use at this point, is not needed. -/
theorem exists_affine_nonvanishingOpen_of_nonvanishing [X.IsQuasiAffine] (L : X.Modules)
    [IsInvertibleModule X L] {E : Set X} (hE : E.Finite) (W : X.Opens)
    (hEW : E ⊆ (W : Set X)) {s₀ : Γ(L, ⊤)} (hs₀ : E ⊆ nonvanishingLocus L s₀) :
    ∃ s : Γ(L, ⊤), IsAffineOpen (nonvanishingOpen X L s) ∧
      E ⊆ (nonvanishingOpen X L s : Set X) ∧ nonvanishingOpen X L s ≤ W := by
  obtain ⟨g, haff, hEg, hgW⟩ :=
    Stacks.AmpleCluster.exists_affine_basicOpen_of_finite_of_isQuasiAffine hE
      (W ⊓ nonvanishingOpen X L s₀) fun x hx => ⟨hEW hx, hs₀ hx⟩
  have key : nonvanishingOpen X L (g • s₀) = X.basicOpen g :=
    nonvanishingOpen_smul_of_le L g s₀ (hgW.trans inf_le_right)
  exact ⟨g • s₀, key ▸ haff, key ▸ hEg, key ▸ hgW.trans inf_le_left⟩

end Stacks.QuasiAffineGlobalGeneration

end
