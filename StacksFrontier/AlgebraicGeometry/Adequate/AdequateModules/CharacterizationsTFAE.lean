module

public import Mathlib.Tactic.TFAE
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedKernelConverse

/-!
# Tag 06VK: the five characterisations of an adequate module, as one statement

[Stacks, Tag 06VK] is the assertion that five conditions on an `𝒪`-module `𝓕` on the big
`τ`-site over a scheme `S` are equivalent:

1. `𝓕` is adequate;
2. there is an affine open covering `S = ⋃ Sᵢ` and maps `𝓖ᵢ ⟶ 𝓗ᵢ` of quasi-coherent
   `𝒪_{Sᵢ}`-modules with `𝓕|_(Sch/Sᵢ)_τ = Ker(𝓖ᵢᵃ ⟶ 𝓗ᵢᵃ)`;
3. the same with an arbitrary `τ`-covering `{Sᵢ → S}` in place of the affine open covering;
4. there is a `τ`-covering `{fᵢ : Sᵢ → S}` with every pullback `fᵢ^*𝓕` adequate;
5. for every affine scheme `U` over `S` the restriction `𝓕|_(Sch/U)_τ` is the kernel of a map
   `𝓖ᵃ ⟶ 𝓗ᵃ` of quasi-coherent `𝒪_U`-modules.

The four conditions other than adequacy are the predicates
`Stacks.Adequate.HasAffineOpenAssociatedKernelCover`,
`Stacks.Adequate.HasCoveringAssociatedKernel`, `Stacks.Adequate.HasAdequatePullbackCover` and
`Stacks.Adequate.HasAssociatedKernelOnEveryAffine` of
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/Characterizations.lean`, and the
pairwise equivalences of each of them with adequacy are proved there and in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AssociatedKernelConverse.lean`. What
this module adds is the single statement that the tag actually makes: the one proposition that
all five are equivalent, rather than four separate propositions each relating one of them to
the first.

## Main results

* `Stacks.Adequate.isAdequate_tfae` — **[Stacks, Tag 06VK] in full**: the five conditions, in
  the source's order, are equivalent. Every edge of the equivalence is unconditional, so the
  statement carries no hypothesis beyond the big site `B` over `S` and the `𝒪`-module `𝓕` on
  it.

## Implementation notes

The list is given in the source's order, so that `(Stacks.Adequate.isAdequate_tfae B F).out i j`
is the implication from the source's condition `i + 1` to its condition `j + 1`.

The four spokes `(1) ↔ (2)`, `(1) ↔ (3)`, `(1) ↔ (4)` and `(1) ↔ (5)` already determine the
whole equivalence, and `tfae_finish` closes the remaining edges from them; no new mathematical
input is needed here and none is supplied.

Conditions (2), (3) and (5) are phrased with `Stacks.Adequate.IsAssociatedKernelOnPullback`,
which bundles `Stacks.Adequate.AffineAssociatedSections` for the site over each member of the
covering along with the kernel presentation. That conjunct is discharged unconditionally by the
theorem `Stacks.Adequate.affineAssociatedSections`, so it does not weaken the equivalence: it
is supplied, not assumed. See the implementation notes of
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/Characterizations.lean`.

## References

* [Stacks Project, Tag 06VK](https://stacks.math.columbia.edu/tag/06VK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)

/-- **[Stacks, Tag 06VK].** For an `𝒪`-module `𝓕` on the big `τ`-site over a scheme `S` the
following five conditions are equivalent, in the source's order:

1. `𝓕` is adequate;
2. there is an affine open covering `S = ⋃ Sᵢ` and, for each `i`, a map `𝓖ᵢ ⟶ 𝓗ᵢ` of
   quasi-coherent `𝒪_{Sᵢ}`-modules presenting `𝓕|_(Sch/Sᵢ)_τ` as the kernel of
   `𝓖ᵢᵃ ⟶ 𝓗ᵢᵃ`;
3. the same over a `τ`-covering `{Sᵢ → S}` of `S` rather than an affine open covering;
4. there is a `τ`-covering `{fᵢ : Sᵢ → S}` of `S` with every pullback `fᵢ^*𝓕` adequate;
5. for every affine scheme `Spec A` of the site over `S` the restriction `𝓕|_(Sch/Spec A)_τ` is
   the kernel of a map `𝓖ᵃ ⟶ 𝓗ᵃ` of associated modules of quasi-coherent
   `𝒪_{Spec A}`-modules.

The statement is unconditional: each of the four equivalences with condition (1) holds with no
hypotheses, and `tfae_finish` assembles the remaining edges. -/
@[stacks 06VK "the whole tag as one statement: all five conditions on an 𝒪-module on the big
τ-site over a scheme are equivalent, listed in the source's order and with no hypotheses"]
public theorem isAdequate_tfae (F : SheafOfModules.{u} B.structureSheaf) :
    [IsAdequate B F,
      HasAffineOpenAssociatedKernelCover B F,
      HasCoveringAssociatedKernel B F,
      HasAdequatePullbackCover B F,
      HasAssociatedKernelOnEveryAffine B F].TFAE := by
  tfae_have 1 ↔ 2 := isAdequate_iff_hasAffineOpenAssociatedKernelCover B F
  tfae_have 1 ↔ 3 := isAdequate_iff_hasCoveringAssociatedKernel B F
  tfae_have 1 ↔ 4 := isAdequate_iff_hasAdequatePullbackCover B F
  tfae_have 1 ↔ 5 := isAdequate_iff_hasAssociatedKernelOnEveryAffine B F
  tfae_finish

end Stacks.Adequate

end
