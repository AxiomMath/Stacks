module

public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFrom.Affine
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBoundedBelow

/-!
# Local boundedness below becomes global on a quasi-compact space

An object `E` of `D(𝒪_X)` on a ringed space is *locally bounded below* when every point of `X`
has an open neighbourhood `U` and an integer `N` with `H^i(E)|_U = 0` for all `i < N`
(`AlgebraicGeometry.RingedSpace.IsLocallyBoundedBelow`). On a quasi-compact space the local
bounds can be replaced by a single global one: finitely many of the neighbourhoods already cover
`X`, the minimum of the finitely many integers attached to them is a bound valid everywhere, and
a sheaf of modules whose restrictions to the members of an open covering vanish is zero.

The consequence recorded here is the one the derived direct image needs. An `S`-perfect object
in the sense of Stacks 0DI0 is locally bounded below, by
`AlgebraicGeometry.isLocallyBoundedBelow_of_isPerfectRelativeTo`; so on a quasi-compact `X` it is
bounded below, which is the clause `E.IsGE a` that the finiteness results for `Rf_*` ask of their
source complex.

## Main results

* `AlgebraicGeometry.RingedSpace.exists_isGE_of_isLocallyBoundedBelow`: on a quasi-compact ringed
  space a locally bounded below object of `D(𝒪_X)` is bounded below.
* `AlgebraicGeometry.exists_isGE_of_isPerfectRelativeTo`: an `S`-perfect object of `D(𝒪_X)` is
  bounded below when `X` is quasi-compact.

## Implementation notes

The minimum of the finitely many local bounds is taken with `Finset.inf'`, which needs the finite
subcover to be nonempty; the degenerate case is kept by taking `0` there, and the resulting bound
is still correct because the index type of the covering is then empty, so the vanishing statement
to be proved is reached from an empty family — which forces `X` itself to be empty, and
`AlgebraicGeometry.RingedSpace.isZero_of_restrictModules` applied to an empty covering of an empty
space concludes.

Boundedness below is `CategoryTheory.Triangulated.TStructure.IsGE` for the canonical t-structure,
read through `CategoryTheory.DerivedCategory.isGE_iff` as vanishing of the cohomology sheaves in
all low degrees; that is the form in which the finiteness results for `Rf_*` consume it.

## References

* [Stacks Project, Lemma 36.35.13 (Tag 0GEH)](https://stacks.math.columbia.edu/tag/0GEH)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe d d' u

namespace AlgebraicGeometry

namespace RingedSpace

/-- **On a quasi-compact ringed space a locally bounded below object is bounded below.** If every
point of `X` has a neighbourhood on which the cohomology sheaves of `E` vanish in all
sufficiently low degrees, and `X` is quasi-compact, then there is one degree below which all of
them vanish.

Finitely many of the neighbourhoods cover `X`; the minimum of the finitely many associated bounds
works globally, because a sheaf of modules whose restrictions to the members of an open covering
all vanish is zero. -/
public theorem exists_isGE_of_isLocallyBoundedBelow (X : RingedSpace.{u, u})
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] [CompactSpace X.carrier]
    (E : DerivedCategory (OXMod.{u, u} X)) (hE : IsLocallyBoundedBelow X E) :
    ∃ N : ℤ, E.IsGE N := by
  classical
  choose U hxU N hN using hE
  obtain ⟨t, ht⟩ := (isCompact_univ (X := X.carrier)).elim_finite_subcover
    (fun x : X.carrier => (U x : Set X.carrier)) (fun x => (U x).isOpen)
    fun x _ => Set.mem_iUnion.2 ⟨x, hxU x⟩
  refine ⟨if h : t.Nonempty then t.inf' h N else 0, (DerivedCategory.isGE_iff E _).2 ?_⟩
  have hle : ∀ x ∈ t, (if h : t.Nonempty then t.inf' h N else 0) ≤ N x := by
    intro x hx
    rw [dite_eq_left ⟨x, hx⟩]
    exact Finset.inf'_le _ hx
  intro i hi
  refine isZero_of_restrictModules X _ (fun x : {x // x ∈ t} => U x.1) (fun x => ?_) fun x => ?_
  · obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨⟨y, hy⟩, hxy⟩
  · exact hN x.1 i (lt_of_lt_of_le hi (hle x.1 x.2))

end RingedSpace

/-- **An `S`-perfect object on a quasi-compact scheme is bounded below.** Relative perfectness in
the sense of Stacks 0DI0 asks for finite Tor dimension over `f⁻¹𝒪_S` on the members of an open
covering, which bounds the cohomology of `E` below on each of them; quasi-compactness of `X` then
makes one of those bounds work everywhere.

The derived tensor product on the inverse-image ringed space is a family of certificates, one on
each open subspace, pinned by the hypothesis `hD` that its underived tensor product is the
genuine `- ⊗_{f⁻¹𝒪_S} -` of Stacks 06YU; without that pinning the Tor clause of relative
perfectness carries no information about the cohomology of `E`. -/
public theorem exists_isGE_of_isPerfectRelativeTo {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [CompactSpace X]
    [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)]
    [HasDerivedCategory.{d'} (OXMod.{u, u} (RingedSpace.inverseImage S.toRingedSpace f.base))]
    [∀ U : Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      HasDerivedCategory.{d'}
        (OXMod.{u, u} ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict
          U.isOpenEmbedding))]
    (D : ∀ U : Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{d', u}
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding))
    (hD : ∀ U : Opens (RingedSpace.inverseImage S.toRingedSpace f.base).carrier,
      (D U).tensor = Stacks.SheafOfModules.Tensor.sheafTensor
        ((RingedSpace.inverseImage S.toRingedSpace f.base).restrict U.isOpenEmbedding).sheaf)
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : f.IsPerfectRelativeTo D E) :
    ∃ N : ℤ, E.IsGE N :=
  RingedSpace.exists_isGE_of_isLocallyBoundedBelow X.toRingedSpace E
    (isLocallyBoundedBelow_of_isPerfectRelativeTo f D hD E hE)

end AlgebraicGeometry

end
