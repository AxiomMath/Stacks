module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowTruncation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.AbelianHypercohomology

/-!
# Hypercohomology only sees a bounded below complex through a range of degrees

Let `C` be a small category, `J` a Grothendieck topology on `C` and `U` an object of `C`. A
morphism `f : K ⟶ L` of bounded below complexes of abelian sheaves which is invertible on the
cohomology sheaves `H^i` for all `i ≤ n + 1` is invertible on hypercohomology
`H^i(U, -)` for all `i ≤ n`.

This is the step of the proof of [Stacks, Tag 0EZB] which converts a statement about cohomology
*sheaves* into a statement about hypercohomology *groups*, and it is the only step of that proof
which is pure homological algebra: the source argues through a spectral sequence, but the
statement is simply that the cone of `f` is bounded below by `n + 1`
(`DerivedCategory.Plus.isGE_three_of_isIso_homologyMap_mor₁`), that derived sections move
cohomology to the right (`Stacks.Cohomology.isZero_hypercohomology_of_isGE`), and that
hypercohomology has a long exact sequence
(`Stacks.Cohomology.epi_hypercohomology_map_mor₁_iff` and
`Stacks.Cohomology.mono_hypercohomology_map_mor₁_iff`).

Note the degree `n + 1` in the hypothesis: hypercohomology in degree `n` sees the cone of `f` in
degrees `n - 1` and `n`, so what must vanish is `H^i` of the cone for `i ≤ n`, and vanishing of
the cone in degree `n` needs invertibility of `f` on `H^{n + 1}` as well. This matches the
source, which concludes that `L ⟶ Rε_{X, *}ε_X^{-1}L` is an isomorphism "in degrees
`≤ n`" from vanishing of the relevant spectral sequence terms in the whole range `p + q ≤ n`.

## Main results

* `Stacks.Cohomology.isIso_hypercohomologyFunctor_map_of_isIso_homologyFunctor_map`: the
  statement above.
* `Stacks.Cohomology.isIso_hypercohomologyFunctor_map_of_isIso_of_mono_homologyFunctor_map`: the
  weaker hypothesis that is actually available — invertible on `H^i` for `i ≤ n` and merely
  *monomorphic* on `H^{n + 1}`. For the change-of-topology comparison
  `L' ⟶ Rε_{X, *}ε_X^{-1}L'` invertibility in the top degree is false, because `H^{n + 1}` of
  the target receives `R^{n + 1}ε_{X, *}(ε_X^{-1}H^0(L'))`; injectivity there is all the
  vanishing argument uses.

## References

* [Stacks Project, Tag 0EZB](https://stacks.math.columbia.edu/tag/0EZB)
* [Stacks Project, Tag 015A](https://stacks.math.columbia.edu/tag/015A)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace Stacks.Cohomology

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)

/-- If the cone of `f` is bounded below by `n + 1`, then `f` is invertible on hypercohomology
over `U` in degrees `≤ n`. -/
private theorem isIso_hypercohomologyFunctor_map_of_isGE_cone
    {K L M : DerivedCategory.Plus (Sheaf J Ab.{max u v})} (f : K ⟶ L) {g : L ⟶ M}
    {h : M ⟶ K⟦(1 : ℤ)⟧} (hT : Triangle.mk f g h ∈ distTriang _) (n : ℤ) (i : ℤ) (hi : i ≤ n)
    [M.IsGE (n + 1)] :
    IsIso ((hypercohomologyFunctor J U i).map f) := by
  have hepi : Epi ((hypercohomologyFunctor J U i).map f) := by
    rw [← Triangle.mk_mor₁ f g h, epi_hypercohomology_map_mor₁_iff J U _ hT i]
    exact (isZero_hypercohomology_of_isGE J U M (n + 1) i (by omega)).eq_zero_of_tgt _
  have hmono : Mono ((hypercohomologyFunctor J U i).map f) := by
    rw [← Triangle.mk_mor₁ f g h, mono_hypercohomology_map_mor₁_iff J U _ hT (i - 1) i (by omega)]
    exact (isZero_hypercohomology_of_isGE J U M (n + 1) (i - 1)
      (by omega)).eq_zero_of_src _
  exact isIso_of_mono_of_epi _

/-- **A morphism of bounded below complexes of abelian sheaves which is invertible on the
cohomology sheaves in degrees `≤ n + 1` is invertible on hypercohomology over `U` in degrees
`≤ n`**, [Stacks, Tag 0EZB].

The cone of such a morphism has no cohomology in degrees `≤ n`, hence no hypercohomology over
`U` in those degrees either, and the long exact sequence of hypercohomology then makes the
morphism both epi and mono in every degree `≤ n`. -/
theorem isIso_hypercohomologyFunctor_map_of_isIso_homologyFunctor_map
    {K L : DerivedCategory.Plus (Sheaf J Ab.{max u v})} (f : K ⟶ L) (n : ℤ)
    (hf : ∀ i : ℤ, i ≤ n + 1 →
      IsIso ((DerivedCategory.Plus.homologyFunctor (Sheaf J Ab.{max u v}) i).map f))
    (i : ℤ) (hi : i ≤ n) :
    IsIso ((hypercohomologyFunctor J U i).map f) := by
  obtain ⟨M, g, h, hT⟩ := distinguished_cocone_triangle f
  have : M.IsGE (n + 1) :=
    DerivedCategory.Plus.isGE_three_of_isIso_homologyMap_mor₁ _ hT n hf
  exact isIso_hypercohomologyFunctor_map_of_isGE_cone J U f hT n i hi

/-- **A morphism of bounded below complexes of abelian sheaves which is invertible on the
cohomology sheaves in degrees `≤ n` and monomorphic in degree `n + 1` is invertible on
hypercohomology over `U` in degrees `≤ n`**, [Stacks, Tag 0EZB].

This is the form in which the step is used, and it is strictly weaker than
`isIso_hypercohomologyFunctor_map_of_isIso_homologyFunctor_map`: for the change-of-topology
comparison `L' ⟶ Rε_{X,*}ε_X^{-1}L'` the top degree `n + 1` of the cohomology sheaves of the
target receives `R^{n+1}ε_{X,*}(ε_X^{-1}H^0(L'))`, so the comparison is *not* invertible there,
only injective. Injectivity in degree `n + 1` is all the vanishing argument needs: the cone of
the morphism is still bounded below by `n + 1`
(`DerivedCategory.Plus.isGE_three_of_epi_of_mono_homologyMap_mor₁`), hence has no
hypercohomology over `U` in degrees `≤ n`. -/
theorem isIso_hypercohomologyFunctor_map_of_isIso_of_mono_homologyFunctor_map
    {K L : DerivedCategory.Plus (Sheaf J Ab.{max u v})} (f : K ⟶ L) (n : ℤ)
    (hf : ∀ i : ℤ, i ≤ n →
      IsIso ((DerivedCategory.Plus.homologyFunctor (Sheaf J Ab.{max u v}) i).map f))
    (hf' : Mono ((DerivedCategory.Plus.homologyFunctor (Sheaf J Ab.{max u v}) (n + 1)).map f))
    (i : ℤ) (hi : i ≤ n) :
    IsIso ((hypercohomologyFunctor J U i).map f) := by
  obtain ⟨M, g, h, hT⟩ := distinguished_cocone_triangle f
  have hepiH : ∀ j : ℤ, j ≤ n →
      Epi ((DerivedCategory.Plus.homologyFunctor (Sheaf J Ab.{max u v}) j).map f) := by
    intro j hj
    have := hf j hj
    infer_instance
  have hmonoH : ∀ j : ℤ, j ≤ n + 1 →
      Mono ((DerivedCategory.Plus.homologyFunctor (Sheaf J Ab.{max u v}) j).map f) := by
    intro j hj
    rcases eq_or_lt_of_le hj with rfl | hj'
    · exact hf'
    · have := hf j (by omega)
      infer_instance
  have : M.IsGE (n + 1) :=
    DerivedCategory.Plus.isGE_three_of_epi_of_mono_homologyMap_mor₁ _ hT n hepiH hmonoH
  exact isIso_hypercohomologyFunctor_map_of_isGE_cone J U f hT n i hi

end Stacks.Cohomology
