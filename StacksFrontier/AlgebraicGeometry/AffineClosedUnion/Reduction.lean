module

public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.CardForm
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningAffine

/-!
# A scheme covered by finitely many affine closed subschemes, without reducedness

[Stacks, Tag 09NL](https://stacks.math.columbia.edu/tag/09NL) states that a scheme which is set
theoretically the union of finitely many affine closed subschemes is affine, with *no* hypothesis
on the ambient scheme. `StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Finite` and
`StacksFrontier.AlgebraicGeometry.AffineClosedUnion.CardForm` prove the case of a reduced ambient
scheme. This file removes the reducedness hypothesis from everything in the tag except one
statement about global sections, which is carried as an explicit hypothesis.

The reduction is this. Reducedness is used in the reduced case only at the very last step: the
intersection `⨅ i, (f i).ker.radical` of the radicals of the kernel ideal sheaves is a radical
ideal sheaf whose support is all of `X`, and on a reduced scheme such an ideal sheaf is `⊥`, so
its closed subscheme — which is affine by
`Stacks.AffineClosedUnion.isAffine_subscheme_finsetInf`, a statement that never mentions
reducedness — is the whole of `X`. On an arbitrary scheme the same ideal sheaf is instead the
nilradical `AlgebraicGeometry.Scheme.nilradical`, by
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_support`: a radical ideal sheaf is the
vanishing ideal sheaf of its support. So the conclusion that survives unconditionally is that
the *reduced induced closed subscheme* `X.nilradical.subscheme` is affine, and `X` is a
thickening of it.

What is then missing for the tag is exactly [Stacks, Tag 06AD] — a thickening of an affine
scheme is affine — for that one thickening, and by
`Stacks.Thickenings.IsThickening.isAffine_iff_surjective_appTop` that is exactly the
surjectivity of `X.nilradical.subschemeι.appTop`, the statement that every global function on
the reduced induced subscheme is the restriction of a global function on `X`. That surjectivity
is the vanishing of a first cohomology group; the source deduces it from [Stacks, Tag 05YU]
(a scheme admitting a surjective universally closed morphism from an affine scheme is affine),
which is not available in this repository. It is therefore carried as the hypothesis `hlift` of
the two tagged statements below, and nothing else is assumed.

## Main results

* `Stacks.AffineClosedUnion.isAffine_nilradical_subscheme_of_isClosedImmersion_iUnion`:
  **unconditionally**, for a scheme set theoretically covered by finitely many affine closed
  subschemes the reduced induced closed subscheme `X.nilradical.subscheme` is affine. No
  reducedness, and no hypothesis on global sections.
* `Stacks.AffineClosedUnion.isThickening_subschemeι_nilradical`: a scheme is a thickening of its
  reduced induced closed subscheme.
* `Stacks.AffineClosedUnion.isAffine_of_isClosedImmersion_iUnion_of_surjective_appTop` and
  `Stacks.AffineClosedUnion.isAffine_of_surjective_sigmaDesc_of_surjective_appTop`:
  [Stacks, Tag 09NL] in the two spellings of the covering hypothesis, with the lifting of global
  sections along `X.nilradical.subschemeι` as an explicit hypothesis.

## Implementation notes

The hypothesis `hlift` is about the single morphism `X.nilradical.subschemeι` determined by `X`
alone; it mentions neither the family `f` nor the index type. Given the covering hypothesis it
is equivalent to the conclusion, by
`Stacks.Thickenings.IsThickening.isAffine_iff_surjective_appTop`, but it is not the conclusion:
the content proved here is that the reduced induced subscheme is affine, which is what turns a
surjectivity of one ring map into affineness of `X`.

## References

* [Stacks Project, Tag 05YU](https://stacks.math.columbia.edu/tag/05YU)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 09NL](https://stacks.math.columbia.edu/tag/09NL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData

universe u v

namespace Stacks.AffineClosedUnion

variable {X : Scheme.{u}}

/-- **The reduced induced closed subscheme of a scheme covered by finitely many affine closed
subschemes is affine.** This is the whole of [Stacks, Tag 09NL] except for the passage from the
reduced induced subscheme to the scheme itself, and it needs no hypothesis on `X`.

The intersection `⨅ i, (f i).ker.radical` is a radical ideal sheaf whose support is all of `X`,
hence is the vanishing ideal sheaf of `⊤`, which is the nilradical; and its closed subscheme is
affine by `Stacks.AffineClosedUnion.isAffine_subscheme_finsetInf`. -/
theorem isAffine_nilradical_subscheme_of_isClosedImmersion_iUnion {ι : Type*} [Finite ι]
    {Z : ι → Scheme.{u}} (f : ∀ i, Z i ⟶ X) [∀ i, IsClosedImmersion (f i)]
    [∀ i, IsAffine (Z i)] (hcov : ⋃ i, Set.range (f i).base = Set.univ) :
    IsAffine X.nilradical.subscheme := by
  classical
  cases nonempty_fintype ι
  have hrad : ∀ i, ((f i).ker.radical).radical = (f i).ker.radical := fun i ↦ radical_radical _
  have haff : ∀ i, IsAffine ((f i).ker.radical).subscheme := fun i ↦ by
    have := isAffine_ker_subscheme (f i)
    exact isAffine_of_isAffineHom (inclusion (le_radical (f i).ker))
  have hsupp : (Finset.univ.inf fun i ↦ (f i).ker.radical).support = ⊤ := by
    rw [support_finsetInf]
    refine le_antisymm le_top ?_
    rw [← SetLike.coe_subset_coe]
    intro x _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov ▸ Set.mem_univ x)
    have hxi : x ∈ ((f i).ker.radical).support := by
      rw [support_radical]
      exact (support_ker_eq_range (f i)).ge hi
    exact Finset.le_sup (f := fun i ↦ ((f i).ker.radical).support) (Finset.mem_univ i) hxi
  have hJ : (Finset.univ.inf fun i ↦ (f i).ker.radical) = X.nilradical := by
    rw [← radical_finsetInf (fun i ↦ (f i).ker.radical) hrad Finset.univ, ← vanishingIdeal_support,
      hsupp, vanishingIdeal_top]
  have hA := isAffine_subscheme_finsetInf (fun i ↦ (f i).ker.radical) hrad haff Finset.univ
  rwa [hJ] at hA

/-- **A scheme is a thickening of its reduced induced closed subscheme.** The inclusion of the
closed subscheme cut out by the nilradical is a closed immersion, and it is surjective because
the support of the nilradical is everything. -/
theorem isThickening_subschemeι_nilradical (X : Scheme.{u}) :
    Stacks.Thickenings.IsThickening X.nilradical.subschemeι := by
  refine ⟨inferInstance, Set.range_eq_univ.mp ?_⟩
  rw [range_subschemeι, Scheme.support_nilradical]
  exact TopologicalSpace.Closeds.coe_top

/-- **[Stacks, Tag 09NL], granted that global functions lift to the ambient scheme.** A scheme
which is set theoretically the union of finitely many affine closed subschemes is affine,
provided every global function on its reduced induced closed subscheme is the restriction of a
global function on it.

The hypothesis `hlift` is the only thing assumed, it concerns the single morphism
`X.nilradical.subschemeι`, and it is the cohomological content of [Stacks, Tag 06AD] for that
thickening: see the module docstring. Everything else — that the reduced induced closed
subscheme is affine — is
`Stacks.AffineClosedUnion.isAffine_nilradical_subscheme_of_isClosedImmersion_iUnion`. -/
@[stacks 09NL]
theorem isAffine_of_isClosedImmersion_iUnion_of_surjective_appTop {ι : Type*} [Finite ι]
    {Z : ι → Scheme.{u}} (f : ∀ i, Z i ⟶ X) [∀ i, IsClosedImmersion (f i)]
    [∀ i, IsAffine (Z i)] (hcov : ⋃ i, Set.range (f i).base = Set.univ)
    (hlift : Function.Surjective X.nilradical.subschemeι.appTop.hom) : IsAffine X :=
  haveI := isAffine_nilradical_subscheme_of_isClosedImmersion_iUnion f hcov
  Stacks.Thickenings.isAffine_of_isThickening_of_surjective_appTop
    (isThickening_subschemeι_nilradical X) hlift

/-- **[Stacks, Tag 09NL] in the tag's own vocabulary, granted that global functions lift to the
ambient scheme.** The covering hypothesis is surjectivity of the morphism from the coproduct, as
in the tag; it is the same hypothesis by
`Stacks.AffineClosedUnion.surjective_sigmaDesc_iff`.

The hypothesis `hlift` is as in
`Stacks.AffineClosedUnion.isAffine_of_isClosedImmersion_iUnion_of_surjective_appTop`. -/
@[stacks 09NL]
theorem isAffine_of_surjective_sigmaDesc_of_surjective_appTop {ι : Type v} [Finite ι]
    {Z : ι → Scheme.{u}} (f : ∀ i, Z i ⟶ X) [∀ i, IsAffine (Z i)]
    [∀ i, IsClosedImmersion (f i)] [hsurj : Surjective (Sigma.desc f)]
    (hlift : Function.Surjective X.nilradical.subschemeι.appTop.hom) : IsAffine X :=
  haveI : Small.{u} ι := inferInstance
  isAffine_of_isClosedImmersion_iUnion_of_surjective_appTop f
    ((surjective_sigmaDesc_iff f).mp hsurj) hlift

end Stacks.AffineClosedUnion

end
