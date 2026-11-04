module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedAbove
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedApproximation
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedBelowApproximation
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.LocalNullHomotopyOverSlices

/-!
# Strictly perfect approximations with no terms above a degree

Let `X` be a ringed space and let `A` be an `m`-pseudo-coherent complex of `𝒪_X`-modules whose
cohomology vanishes in every degree above some `r ≥ m`. Near every point of `X` the complex `A`
then admits a strictly perfect approximation in degrees `≥ m` which has no terms above degree
`r` at all. The approximation supplied by `m`-pseudo-coherence is an isomorphism on cohomology
above `m`, hence above `r`, so the approximating strictly perfect complex `P₀` has no cohomology
above `r` either and may be replaced by its canonical truncation `τ^{≤r}P₀`; the only thing that
is not formal is that the degree-`r` cycles of `P₀` are again a direct summand of a finite free
module, and that holds after shrinking the neighbourhood once more.

This is the ringed-space half of Stacks 20.46.9, and it is the step "we may assume `P` has no
terms above `r`" that Stacks performs inside the proofs of 08CD (two-out-of-three for
pseudo-coherence in a distinguished triangle) and 08DN (finite-typeness of the top cohomology
sheaf).

## Main results

* `AlgebraicGeometry.RingedSpace.exists_isDirectSummandOfFiniteFree_cycles`: near every point,
  the degree-`r` cycles of a strictly perfect complex with no cohomology above `r` become a
  direct summand of a finite free module after restriction.
* `AlgebraicGeometry.RingedSpace.exists_approximation_isZero_X_above`: the approximation of an
  `m`-pseudo-coherent complex near a point can be taken with no terms above degree `r`, provided
  the complex has no cohomology above `r ≥ m`.

## Implementation notes

The degree-`r` cycles are the one non-formal input of the purely homological truncation lemma
`StrictlyPerfect.exists_isStrictlyPerfect_boundedAbove_of_approximation`, and they are produced
from a *local null homotopy of the tail inclusion*. The stupid truncation `σ^{≥r+1}P₀` is a
subcomplex of `P₀` because the differential raises degrees, it is strictly perfect, it vanishes
below `r + 1`, and `P₀` has no cohomology in degrees `≥ r + 1`; so Stacks 08C7 makes the
inclusion `σ^{≥r+1}P₀ ⟶ P₀` null homotopic over some neighbourhood `V`. That inclusion is an
isomorphism in every degree `≥ r + 1`, in particular in the two degrees `r + 1` and `r + 2`, and
a null homotopy of a map which is an isomorphism in two consecutive degrees splits
`P₀^{r} ⟶ Z^{r+1}(P₀)`, exhibiting `Z^{r}(P₀|_V)` as a retract of `P₀^{r}|_V`
(`AlgebraicGeometry.RingedSpace.isDirectSummandOfFiniteFree_cycles_of_tailHomotopy`).

Consequently the open set shrinks twice: once for the approximation provided by
`m`-pseudo-coherence, and once more for the null homotopy. The truncation is therefore carried
out over an open subspace `V` of the open subspace `U` of `X`, and
`AlgebraicGeometry.RingedSpace.exists_strictlyPerfect_approximation_of_nested` identifies modules
on `(X|_U)|_V` with modules on `X|_W` for `W` the image of `V` in `X`, which brings the
conclusion back to a single open set of `X`. The point `x` lies in `W` because it lies in `U` and
its corresponding point of `X|_U` lies in `V`.

## References

* [Stacks Project, Tag 08CC](https://stacks.math.columbia.edu/tag/08CC)
* [Stacks Project, Tag 08C7](https://stacks.math.columbia.edu/tag/08C7)
* [Stacks Project, Tag 08DN](https://stacks.math.columbia.edu/tag/08DN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace

universe u

variable {X : RingedSpace.{u, u}}

/-- **Near every point, the degree-`r` cycles of a strictly perfect complex with no cohomology
above `r` are a direct summand of a finite free module after restriction.**

The stupid truncation `σ^{≥r+1}P` is a subcomplex of `P`, is strictly perfect and vanishes below
`r + 1`, while `P` has no cohomology in degrees `≥ r + 1`; so Stacks 08C7 makes the inclusion
`σ^{≥r+1}P ⟶ P` null homotopic over some neighbourhood `V` of the given point. The inclusion is
an isomorphism in the degrees `r + 1` and `r + 2`, and a null homotopy of such a map splits the
map from `P^{r}` to the degree-`(r+1)` cycles, which makes the degree-`r` cycles a retract of
`P^{r}`.

This discharges the hypothesis `hcyc` of
`StrictlyPerfect.exists_isStrictlyPerfect_boundedAbove_of_approximation`. -/
theorem exists_isDirectSummandOfFiniteFree_cycles
    (P : CochainComplex (OXMod.{u, u} X) ℤ) (hP : IsStrictlyPerfect P) (r : ℤ)
    (hvan : ∀ i : ℤ, r < i → IsZero (P.homology i)) (x : X.carrier) :
    ∃ V : Opens X.carrier, x ∈ V ∧
      IsDirectSummandOfFiniteFree ((restrictComplex P V).cycles r) := by
  obtain ⟨V, hxV, hhom⟩ := exists_local_homotopy_zero_of_isZero_homology
    (P.ιStupidTrunc (ComplexShape.embeddingUpIntGE (r + 1))) (r + 1)
    (isStrictlyPerfect_stupidTrunc P hP _)
    (fun i hi => P.isZero_X_stupidTrunc_embeddingUpIntGE (r + 1) i hi)
    (fun i hi => hvan i (by omega)) x
  obtain ⟨H⟩ := nonempty_homotopy_zero_restrictModules V _ hhom
  refine ⟨V, hxV, ?_⟩
  have h : ∀ n : ℤ, r + 1 ≤ n → IsIso ((((restrictModules X V).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (P.ιStupidTrunc (ComplexShape.embeddingUpIntGE (r + 1)))).f n) := by
    intro n hn
    have := P.isIso_ιStupidTrunc_embeddingUpIntGE_f (r + 1) n hn
    exact inferInstanceAs (IsIso ((restrictModules X V).map
      ((P.ιStupidTrunc (ComplexShape.embeddingUpIntGE (r + 1))).f n)))
  have key := isDirectSummandOfFiniteFree_cycles_of_tailHomotopy
    (restrictComplex P V) (isStrictlyPerfect_restrictComplex hP V) (r + 1)
    (restrictComplex (P.stupidTrunc (ComplexShape.embeddingUpIntGE (r + 1))) V)
    (((restrictModules X V).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (P.ιStupidTrunc (ComplexShape.embeddingUpIntGE (r + 1)))) (h _ le_rfl) (h _ (by omega)) H
  simpa using key

/-- **A local strictly perfect approximation can be taken with no terms above a degree where the
cohomology already vanishes.** -/
theorem exists_approximation_isZero_X_above
    (A : CochainComplex (OXMod.{u, u} X) ℤ) (m r : ℤ) (hmr : m ≤ r)
    (hA : IsPseudoCoherentComplexFrom A m)
    (hvanish : ∀ i : ℤ, r < i → IsZero (A.homology i)) (x : X.carrier) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ,
        StrictlyPerfect.IsStrictlyPerfect P ∧ (∀ i : ℤ, r < i → IsZero (P.X i)) ∧
        ∃ α : P ⟶ restrictComplex A U,
          (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
          Epi (HomologicalComplex.homologyMap α m) := by
  obtain ⟨U, hxU, P₀, hP₀, α₀, hiso₀, hepi₀⟩ := hA x
  have hresA : ∀ i : ℤ, r < i → IsZero ((restrictComplex A U).homology i) :=
    fun i hi => isZero_restrictComplex_homology A U i (hvanish i hi)
  have hP₀van : ∀ i : ℤ, r < i → IsZero (P₀.homology i) := by
    intro i hi
    have : IsIso (HomologicalComplex.homologyMap α₀ i) := hiso₀ i (lt_of_le_of_lt hmr hi)
    exact (hresA i hi).of_iso (asIso (HomologicalComplex.homologyMap α₀ i))
  obtain ⟨V, hxV, hcyc⟩ :=
    exists_isDirectSummandOfFiniteFree_cycles P₀ hP₀ r hP₀van ⟨x, hxU⟩
  have := restrictModules_preservesFiniteLimits (X.restrict U.isOpenEmbedding) V
  have := restrictModules_preservesFiniteColimits (X.restrict U.isOpenEmbedding) V
  obtain ⟨Q, hQ, hQtop, β, hβiso, hβepi⟩ :=
    StrictlyPerfect.exists_isStrictlyPerfect_boundedAbove_of_approximation
      (isStrictlyPerfect_restrictComplex hP₀ V) m r hmr
      (fun i hi => isZero_restrictComplex_homology (restrictComplex A U) V i (hresA i hi))
      (((restrictModules (X.restrict U.isOpenEmbedding) V).mapHomologicalComplex
        (ComplexShape.up ℤ)).map α₀)
      (fun j hj => isIso_homologyMap_map _ α₀ j (hiso₀ j hj))
      (epi_homologyMap_map _ α₀ m hepi₀) hcyc
  obtain ⟨P, hP, hPtop, α, hαiso, hαepi⟩ :=
    exists_strictlyPerfect_approximation_of_nested U V A m r Q hQ hQtop β hβiso hβepi
  exact ⟨U.isOpenEmbedding.functor.obj V, ⟨⟨x, hxU⟩, hxV, rfl⟩, P, hP, hPtop, α, hαiso, hαepi⟩

end AlgebraicGeometry.RingedSpace

end

