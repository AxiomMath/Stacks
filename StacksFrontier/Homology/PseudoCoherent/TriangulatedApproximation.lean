module

public import StacksFrontier.Homology.PseudoCoherent.Basic

/-!
# Pseudo-coherence of an image under a triangulated functor, from approximations

Let `R` be a ring and let `G : 𝒟 ⥤ D(R)` be a triangulated functor out of a pretriangulated
category. Suppose an object `E` of `𝒟` can, in every degree, be approximated: for each integer
`m` there is a distinguished triangle `P ⟶ E ⟶ C ⟶ P⟦1⟧` whose first vertex has
pseudo-coherent image `G(P)` and whose third vertex has image `G(C)` with vanishing cohomology
in all degrees at least `m - 1`. Then `G(E)` is pseudo-coherent.

This is the mechanism by which pseudo-coherence of a derived image is propagated from a class
of objects that approximates `E` to `E` itself. Its intended consumer is
[Stacks, Tag 0CSH], where `𝒟 = D(𝒪_X)` for a quasi-compact quasi-separated scheme `X` over
`R`, `G` is `RΓ(X, - ⊗^L_{𝒪_X} K)` for a bounded-above `K` with quasi-coherent cohomology, and
the approximating `P` are the perfect complexes supplied by the approximation theorem; see the
implementation notes.

## Main results

* `StacksDraft.PseudoCoherence.isPseudoCoherentFrom_obj₂_of_distTriang`: in a distinguished
  triangle of `D(R)` whose first vertex is pseudo-coherent and whose third vertex has vanishing
  cohomology in all degrees at least `m - 1`, the second vertex is `m`-pseudo-coherent.
* `StacksDraft.PseudoCoherence.isPseudoCoherent_of_forall_approximation`: the conclusion above,
  for a triangulated functor and an object approximated in every degree.

## Implementation notes

Pseudo-coherence is `m`-pseudo-coherence in every degree `m`
(`StacksDraft.PseudoCoherence.pseudoCoherent_iff_all`), so the whole argument happens one degree
at a time. In a single degree the two inputs are the triangle statement of [Stacks, Tag 064R]
part (2), `PseudoCoherence.isPseudoCoherent_of_distinguished_two`, and the observation that an
object with no cohomology from degree `m - 1` upwards is `(m - 1)`-pseudo-coherent, approximated
by the zero complex, hence `m`-pseudo-coherent. The `m - 1` rather than `m` is what the intended
consumer produces: there the vanishing comes from a cohomological-dimension bound applied to a
cone whose cohomology sheaves vanish from a degree computed to be one lower.

The hypothesis is phrased as an existential over the three vertices and the three maps of the
triangle rather than over a `CategoryTheory.Pretriangulated.Triangle` with an equation pinning
its second vertex to `E`, so that `G.mapTriangle` applied to it has `G.obj E` as its second
vertex definitionally and no transport is needed.

Nothing here is specific to a model of the derived category of `𝒟`: `𝒟` is an arbitrary
pretriangulated category and only `D(R)` is a derived category.

**What this is not.** It is not [Stacks, Tag 0CSH]. That tag additionally needs, on the
geometric side, the approximation theorem [Stacks, Tag 08ES], a cohomological-dimension bound for
`RΓ(X, -)` and the stability of quasi-coherent cohomology under the derived tensor product,
[Stacks, Tag 08DX]; it is assembled from those in
`AlgebraicGeometry.isPseudoCoherent_derivedGlobalSectionsOver_tensor_of_isPseudoCoherent`. No
`@[stacks]` attribute is placed below: the statements here are about an abstract triangulated
functor.

## References

* [Stacks Project, Tag 064R](https://stacks.math.columbia.edu/tag/064R)
* [Stacks Project, Tag 064Q](https://stacks.math.columbia.edu/tag/064Q)
* [Stacks Project, Tag 0CSH](https://stacks.math.columbia.edu/tag/0CSH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace StacksDraft.PseudoCoherence

attribute [local instance] HasDerivedCategory.standard

universe u v w t

variable {R : Type u} [Ring R]

/-- **A distinguished triangle with pseudo-coherent first vertex and cohomologically small third
vertex has `m`-pseudo-coherent second vertex.** If `T₁ ⟶ T₂ ⟶ T₃ ⟶ T₁⟦1⟧` is distinguished in
`D(R)`, if `T₁` is pseudo-coherent, and if `T₃` has vanishing cohomology in every degree at
least `m - 1`, then `T₂` is `m`-pseudo-coherent.

The first vertex is `m`-pseudo-coherent because pseudo-coherence is `m`-pseudo-coherence in
every degree; the third is `(m - 1)`-pseudo-coherent by its vanishing, hence `m`-pseudo-coherent
because `m`-pseudo-coherence weakens as `m` grows. Part (2) of [Stacks, Tag 064R] concludes. -/
theorem isPseudoCoherentFrom_obj₂_of_distTriang (m : ℤ)
    (T : Triangle (DerivedCategory (ModuleCat.{v} R)))
    (hT : T ∈ distinguishedTriangles)
    (h₁ : IsPseudoCoherent T.obj₁)
    (h₃ : ∀ i : ℤ, m - 1 ≤ i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj T.obj₃)) :
    IsPseudoCoherentFrom T.obj₂ m :=
  _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_two m T hT
    ((pseudoCoherent_iff_all T.obj₁).1 h₁ m)
    ((isPseudoCoherentFrom_of_homology_isZero T.obj₃ (m - 1) h₃).mono (n := m) (by omega))

/-- **Pseudo-coherence of `G(E)` from approximations of `E` in every degree.** Let `G : 𝒟 ⥤ D(R)`
be a triangulated functor out of a pretriangulated category and let `E` be an object of `𝒟`.
Suppose that for every integer `m` there is a distinguished triangle `P ⟶ E ⟶ C ⟶ P⟦1⟧` in `𝒟`
such that `G(P)` is pseudo-coherent and `G(C)` has vanishing cohomology in every degree at
least `m - 1`. Then `G(E)` is pseudo-coherent.

A triangulated functor carries the triangle of degree `m` to a distinguished triangle of `D(R)`
whose second vertex is `G(E)`, which is therefore `m`-pseudo-coherent; being so in every degree
is pseudo-coherence. -/
theorem isPseudoCoherent_of_forall_approximation
    {D : Type w} [Category.{t} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (G : D ⥤ DerivedCategory (ModuleCat.{v} R)) [G.CommShift ℤ] [G.IsTriangulated] (E : D)
    (happrox : ∀ m : ℤ, ∃ (P C : D) (a : P ⟶ E) (b : E ⟶ C) (c : C ⟶ P⟦(1 : ℤ)⟧),
      Triangle.mk a b c ∈ distTriang D ∧ IsPseudoCoherent (G.obj P) ∧
        ∀ i : ℤ, m - 1 ≤ i →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj (G.obj C))) :
    IsPseudoCoherent (G.obj E) := by
  refine (pseudoCoherent_iff_all (G.obj E)).2 fun m => ?_
  obtain ⟨P, C, a, b, c, hT, hP, hC⟩ := happrox m
  exact isPseudoCoherentFrom_obj₂_of_distTriang m (G.mapTriangle.obj (Triangle.mk a b c))
    (G.map_distinguished _ hT) hP hC

end StacksDraft.PseudoCoherence

end
