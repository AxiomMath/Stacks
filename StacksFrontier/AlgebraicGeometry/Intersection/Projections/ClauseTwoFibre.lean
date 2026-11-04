module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.EndProjectionFinite
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.LineThroughIdentityDomain

/-!
# Clause (2) of Tag 0B1S as the dimension of one closed subset of `X`

Clause (2) of Tag 0B1S asks that `r_g(X)` meet `Y` properly, which by
`AlgebraicGeometry.ProjectiveSpaceOfModule.IsGoodEndomorphism` is the inequality

`dim (r_g(X) ∩ Y) + dim 𝐏(V) ≤ dim r_g(X) + dim Y`.

The source gets at that inequality through the incidence correspondence
`T = {(x, y, [g]) : x ∈ X, y ∈ Y, r_g(x) = y}`, whose fibre over a class `[g]` is the set of
pairs `(x, r_g(x))` with `x ∈ X` and `r_g(x) ∈ Y` — that is, a copy of

`F(g) = X ∩ r_g⁻¹(Y)`,

the part of `X` that `r_g` carries into `Y`. This file builds `F(g)` and proves that its
dimension is the one clause (2) is about: `F(g)` is a closed subset of `U(g)` whose translate is
exactly `r_g(X) ∩ Y`, and the translate of a closed subset of `U(g)` has the dimension of the
subset, because `r_g` is finite there
(`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_endProjectionImage_eq`). The
same finiteness turns `dim r_g(X)` into `dim X`, so clause (2) becomes a comparison between
`dim F(g)` and the three *fixed* numbers `dim X`, `dim Y` and `dim 𝐏(V)`:

`AlgebraicGeometry.ProjectiveSpaceOfModule.isGoodEndomorphism_iff_topologicalKrullDim_fibre_le`.

That equivalence holds for **every** endomorphism whose domain of definition contains `X`,
singular ones included, and asks no irreducibility of `X`: both are consequences of the
finiteness of `r_g` on a closed subset of `U(g)`, which holds for an arbitrary `g`. It is
therefore not where the determinant enters Tag 0B1S — the split of the bad locus along
`det g = 0` in
`ProjectiveSpaceOfModule.exists_isOpen_closedPoint_line_isGood_of_clauseTwo_split`
is a split of the *codimension* bound and not of the badness criterion.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.endProjectionFibre`: the subset `F(g) = X ∩ r_g⁻¹(Y)`
  of `𝐏(V)`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_endProjectionFibre`: `F(g)` is closed.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.endProjectionImage_endProjectionFibre`: its
  translate is `r_g(X) ∩ Y`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_endProjectionFibre`:
  `dim F(g) = dim (r_g(X) ∩ Y)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_endProjectionFibre_linearFunctionalPoint_iff`:
  on closed points, `[f] ∈ F(g)` says `[f] ∈ X` and `[f ∘ g] ∈ Y` — the condition cutting out the
  fibre of the incidence correspondence, as
  `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_transitionLocus_iff_of_linearFunctionalPoint`
  reads it there.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isGoodEndomorphism_iff_topologicalKrullDim_fibre_le`:
  clause (2) as a bound on `dim F(g)`.

## Implementation notes

`F(g)` is written `X ∩ ι(r_g⁻¹(Y))` rather than as a subset of `U(g)`, so that it can be fed to
the dimension lemmas, which take subsets of `𝐏(V)`. Its closedness is not the closedness of a
preimage: `ι(r_g⁻¹(Y))` is only locally closed in `𝐏(V)`. What is used instead is that `X` lies
in `U(g)`, on which `ι` is a bijection, so inside `X` the complement of `F(g)` is
`ι(r_g⁻¹(Yᶜ))`, which is *open* in `𝐏(V)`; `F(g)` is then `X` minus an open set.

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0B2W](https://stacks.math.columbia.edu/tag/0B2W)
* [Stacks Project, Tag 0AZQ](https://stacks.math.columbia.edu/tag/0AZQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- **The part of `X` that `r_g` carries into `Y`:** the subset `F(g) = X ∩ r_g⁻¹(Y)` of `𝐏(V)`,
formed by taking the preimage of `Y` inside the domain of definition `U(g)` and reading it back in
`𝐏(V)`. For `X ⊆ U(g)` this is the fibre of the incidence correspondence of Tag 0B1S over the
class `[g]`, read through the projection to the first factor. -/
public def endProjectionFibre (g : V →ₗ[k] V) (X Y : Set (projectiveSpaceOfModule k V)) :
    Set (projectiveSpaceOfModule k V) :=
  X ∩ (endDomain k V g).ι.base '' ((endProjection k V g).base ⁻¹' Y)

/-- `F(g) = X ∩ r_g⁻¹(Y)` is contained in `X`. -/
public theorem endProjectionFibre_subset (g : V →ₗ[k] V)
    (X Y : Set (projectiveSpaceOfModule k V)) : endProjectionFibre k V g X Y ⊆ X :=
  Set.inter_subset_left

/-- A point of the domain of definition `U(g)` is the image of a point of `U(g)`. -/
private theorem exists_ι_base_eq_of_mem_endDomain (g : V →ₗ[k] V)
    {x : projectiveSpaceOfModule k V}
    (hx : x ∈ (endDomain k V g : Set (projectiveSpaceOfModule k V))) :
    ∃ y, (endDomain k V g).ι.base y = x := by
  rwa [← Set.mem_range, Scheme.Opens.range_ι]

/-- **`F(g)` is closed.** Inside `X`, which lies in `U(g)`, the complement of `F(g)` is the image
of `r_g⁻¹(Yᶜ)`, an open subset of `U(g)` whose image in `𝐏(V)` is open; so `F(g)` is `X` with an
open set removed. -/
public theorem isClosed_endProjectionFibre (g : V →ₗ[k] V)
    {X Y : Set (projectiveSpaceOfModule k V)} (hXc : IsClosed X) (hYc : IsClosed Y)
    (hdom : X ⊆ (endDomain k V g : Set (projectiveSpaceOfModule k V))) :
    IsClosed (endProjectionFibre k V g X Y) := by
  have hopen : IsOpen ((endDomain k V g).ι.base ''
      ((endProjection k V g).base ⁻¹' Yᶜ)) :=
    (endDomain k V g).ι.isOpenEmbedding.isOpenMap _
      (hYc.isOpen_compl.preimage (by fun_prop))
  have hset : endProjectionFibre k V g X Y =
      X ∩ ((endDomain k V g).ι.base '' ((endProjection k V g).base ⁻¹' Yᶜ))ᶜ := by
    refine Set.ext fun x => and_congr_right fun hx => ?_
    obtain ⟨y, rfl⟩ := exists_ι_base_eq_of_mem_endDomain k V g (hdom hx)
    rw [(endDomain k V g).ι.isOpenEmbedding.injective.mem_set_image, Set.mem_compl_iff,
      (endDomain k V g).ι.isOpenEmbedding.injective.mem_set_image]
    simp
  rw [hset]
  exact hXc.inter hopen.isClosed_compl

/-- **The translate of `F(g)` is `r_g(X) ∩ Y`.** The preimage in `U(g)` of `F(g)` is the
intersection of the preimage of `X` with `r_g⁻¹(Y)`, and the image of such an intersection is the
image of the first factor intersected with `Y`. -/
public theorem endProjectionImage_endProjectionFibre (g : V →ₗ[k] V)
    (X Y : Set (projectiveSpaceOfModule k V)) :
    endProjectionImage k V g (endProjectionFibre k V g X Y) =
      endProjectionImage k V g X ∩ Y := by
  have hpre : (endDomain k V g).ι.base ⁻¹' endProjectionFibre k V g X Y =
      ((endDomain k V g).ι.base ⁻¹' X) ∩ ((endProjection k V g).base ⁻¹' Y) := by
    rw [endProjectionFibre, Set.preimage_inter,
      Set.preimage_image_eq _ (endDomain k V g).ι.isOpenEmbedding.injective]
  rw [endProjectionImage, hpre, Set.image_inter_preimage, endProjectionImage]

/-- **`F(g)` has the dimension clause (2) is about:** `dim F(g) = dim (r_g(X) ∩ Y)`. This is the
finiteness of `r_g` on a closed subset of `U(g)`, applied to `F(g)` — which is why the
non-irreducible case of
`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_endProjectionImage_eq` is needed:
`X ∩ r_g⁻¹(Y)` has no reason to be irreducible even when `X` and `Y` are. -/
public theorem topologicalKrullDim_endProjectionFibre [IsAlgClosed k] [FiniteDimensional k V]
    [Nontrivial V] (g : V →ₗ[k] V) {X Y : Set (projectiveSpaceOfModule k V)}
    (hXc : IsClosed X) (hYc : IsClosed Y)
    (hdom : X ⊆ (endDomain k V g : Set (projectiveSpaceOfModule k V))) :
    topologicalKrullDim ↥(endProjectionFibre k V g X Y) =
      topologicalKrullDim ↥(endProjectionImage k V g X ∩ Y) := by
  rw [← endProjectionImage_endProjectionFibre k V g X Y]
  exact (topologicalKrullDim_endProjectionImage_eq k V g
    (isClosed_endProjectionFibre k V g hXc hYc hdom)
    ((endProjectionFibre_subset k V g X Y).trans hdom)).symm

/-- **`F(g)` on closed points:** the point cut out by a nonzero functional `f` lies in `F(g)`
exactly when it lies in `X` and the point cut out by `f ∘ g` lies in `Y`. This is the condition
cutting out the fibre of the incidence correspondence of Tag 0B1S over `[g]`, as
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_transitionLocus_iff_of_linearFunctionalPoint`
reads it there: `f ∘ g ∈ k ∙ f'` for a nonzero `f'` cutting out a point of `Y`. -/
public theorem mem_endProjectionFibre_linearFunctionalPoint_iff [IsAlgClosed k]
    [FiniteDimensional k V] [Nontrivial V] (g : V →ₗ[k] V)
    (X Y : Set (projectiveSpaceOfModule k V)) {f : Module.Dual k V} (hf : f ≠ 0)
    (hfg : f ∘ₗ g ≠ 0) :
    linearFunctionalPoint k V f hf ∈ endProjectionFibre k V g X Y ↔
      linearFunctionalPoint k V f hf ∈ X ∧
        linearFunctionalPoint k V (f ∘ₗ g) hfg ∈ Y := by
  obtain ⟨y, hy⟩ := exists_ι_base_eq_of_mem_endDomain k V g (x := linearFunctionalPoint k V f hf)
    (by
      by_contra hcon
      exact hfg ((notMem_endDomain_linearFunctionalPoint_iff k V f hf g).mp hcon))
  have hval : endProjection k V g y = linearFunctionalPoint k V (f ∘ₗ g) hfg :=
    endProjection_eq_linearFunctionalPoint k V g y f hf hfg hy
  refine and_congr_right fun _ => ?_
  rw [← hy, (endDomain k V g).ι.isOpenEmbedding.injective.mem_set_image, Set.mem_preimage, hval]

/-- **Clause (2) of Tag 0B1S as a bound on `dim F(g)`.** For an endomorphism whose domain of
definition contains the closed subset `X`, goodness for the pair `X, Y` is the single inequality

`dim F(g) + dim 𝐏(V) ≤ dim X + dim Y`,

with `F(g) = X ∩ r_g⁻¹(Y)`. Both replacements — `dim (r_g(X) ∩ Y)` by `dim F(g)` and `dim r_g(X)`
by `dim X` — are the finiteness of `r_g` on a closed subset of `U(g)`, so the equivalence needs
neither invertibility of `g` nor irreducibility of `X`. -/
public theorem isGoodEndomorphism_iff_topologicalKrullDim_fibre_le [IsAlgClosed k]
    [FiniteDimensional k V] [Nontrivial V] (g : V →ₗ[k] V)
    {X Y : Set (projectiveSpaceOfModule k V)} (hXc : IsClosed X) (hYc : IsClosed Y)
    (hdom : X ⊆ (endDomain k V g : Set (projectiveSpaceOfModule k V))) :
    IsGoodEndomorphism k V X Y g ↔
      topologicalKrullDim ↥(endProjectionFibre k V g X Y) +
          topologicalKrullDim (projectiveSpaceOfModule k V) ≤
        topologicalKrullDim ↥X + topologicalKrullDim ↥Y := by
  rw [IsGoodEndomorphism, and_iff_right hdom,
    topologicalKrullDim_endProjectionFibre k V g hXc hYc hdom,
    topologicalKrullDim_endProjectionImage_eq k V g hXc hdom]

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
