module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LocalPerfectness

/-!
# Perfectness of a derived object from perfectness on a covering by opens

Let `X` be a ringed space and `K` an object of `D(𝒪_X)`. If `X` is covered by opens `U i` and
each restriction `K|_{U i}` is perfect, then `K` is perfect. The case of two opens `U ⊔ V = ⊤`
is the one a glueing argument needs: a glued object is perfect as soon as the two objects it was
glued from are.

Both statements are given twice, once for each of the two functors that spell "restriction of a
derived object to an open" in this development:

* the derived functor of the degreewise restriction,
  `AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules`, which is the functor
  perfectness itself (Stacks 08CM) is defined through;
* the derived pullback `Lj_U^*` along the inclusion `j_U` of the open subspace, which is the
  functor the glueing lemma [Stacks, Tag 08DG] is stated in.

## Main results

* `Stacks.Cohomology.PerfectComplexes.isPerfect_of_isPerfect_restrict_cover`
* `Stacks.Cohomology.PerfectComplexes.isPerfect_of_isPerfect_restrict_sup_eq_top`
* `Stacks.Cohomology.PerfectComplexes.isPerfect_of_isPerfect_derivedPullback_cover`
* `Stacks.Cohomology.PerfectComplexes.isPerfect_of_isPerfect_derivedPullback_sup_eq_top`

## Implementation notes

The mathematical content is already carried by
`Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect`, which asks for a
neighbourhood with perfect restriction at *every point* rather than for a covering; a covering
yields such a neighbourhood at each of its points and nothing else is needed. What is added here
is only the shape: a consumer that has produced a covering, or glued along two opens, has the
covering and not the pointwise choice function.

The index type is left in an arbitrary universe, which the pointwise form permits — unlike
`AlgebraicGeometry.RingedSpace.IsPerfectComplex`, whose own covering must be indexed in the
universe of the space.

The two-open case is derived from the covering case over `Bool` rather than proved again, so the
point-chasing happens once.

Two further instantiations need no separate statement. Perfectness over an open `Z` of `X`,
covered by opens of the subspace `X|_Z`, is the statement below at the ringed space
`X.restrict Z.isOpenEmbedding`. And for `X` a scheme, `DerivedCategory X.Modules` is
`DerivedCategory (StrictlyPerfect.OXMod X.toRingedSpace)` and `U.toScheme.toRingedSpace` is
`X.toRingedSpace.restrict U.isOpenEmbedding`, both by `rfl`, so a scheme-level consumer applies
these at `X.toRingedSpace` with no transport. A covering by *general* open immersions of ringed
spaces `j : Y ⟶ X`, which is the literal hypothesis shape of [Stacks, Tag 08DG], is **not**
covered: it would need perfectness to be transported along an isomorphism of ringed spaces, and
the development carries that transport for strict perfection
(`AlgebraicGeometry.RingedSpace.PseudoCoherence.isStrictlyPerfect_moduleEquiv`) but not for
`Stacks.Cohomology.PerfectComplexes.IsPerfectComplex`. The inclusions of open subspaces, which
the statements below do cover, are what an induction over the opens of a fixed `X` produces.

`Stacks.Cohomology.PerfectComplexes.IsPerfect` and `AlgebraicGeometry.RingedSpace.IsPerfect` are
two spellings of Stacks 08CM which are equal by `rfl`; the statements below are in the first, and
a goal phrased in the second is closed by them in term mode.

## No tag registration

Locality of perfectness on the space is not a numbered statement of the source — it is the
sentence "the question is local on `X`" of the proof of [Stacks, Tag 08CQ] — so, as for
`Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect`, no `@[stacks]`
attribute is placed here. Nothing below is a restatement of [Stacks, Tag 08CN], whose hypothesis
is a global representative together with strictly perfect local models and which is registered on
`AlgebraicGeometry.RingedSpace.isPerfect_of_strictlyPerfect_local_models`; the tags whose proofs
consume these statements, [Stacks, Tag 09IM] and [Stacks, Tag 08DG], are treated elsewhere.

## References

* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 08CQ](https://stacks.math.columbia.edu/tag/08CQ)
* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open AlgebraicGeometry.RingedSpace.PseudoCoherence
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.Cohomology.PerfectComplexes

universe u d

variable {X : RingedSpace.{u, u}}

attribute [local instance] HasDerivedCategory.standard

/-! ### Restriction as the derived functor of degreewise restriction -/

/-- **Perfectness on a covering implies perfectness.** If the opens `U i` cover the ringed space
`X` and the restriction of `K` to each of them is perfect, then `K` is perfect.

Each point of `X` lies in some member of the covering, so
`Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect` applies. -/
theorem isPerfect_of_isPerfect_restrict_cover [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (K : DerivedCategory (OXMod.{u, u} X)) {I : Type*} (U : I → Opens X.carrier)
    (hU : (⨆ i, U i) = ⊤)
    (h : ∀ i, IsPerfect ((restrictModules.{u} X (U i)).mapDerivedCategory.obj K)) :
    IsPerfect K := by
  refine Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect K fun x => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, U i by rw [hU]; trivial)
  exact ⟨U i, hi, h i⟩

/-- **Perfectness is detected by a covering by two opens.** If `U ⊔ V = ⊤` and both `K|_U` and
`K|_V` are perfect, then `K` is perfect.

This is the perfectness clause of a glueing along two opens: the object produced by
[Stacks, Tag 08DG] out of perfect objects over `U` and over `V` is perfect. -/
theorem isPerfect_of_isPerfect_restrict_sup_eq_top [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (K : DerivedCategory (OXMod.{u, u} X)) (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (hU : IsPerfect ((restrictModules.{u} X U).mapDerivedCategory.obj K))
    (hV : IsPerfect ((restrictModules.{u} X V).mapDerivedCategory.obj K)) :
    IsPerfect K := by
  refine isPerfect_of_isPerfect_restrict_cover K (fun b : Bool => bif b then U else V) ?_ ?_
  · rw [iSup_bool_eq]
    exact hUV
  · rintro (_ | _)
    · exact hV
    · exact hU

/-! ### Restriction as the derived pullback along the inclusion of an open subspace -/

/-- Perfectness of the derived pullback along an open inclusion gives perfectness of the
degreewise restriction. -/
private theorem isPerfect_restrict_of_isPerfect_derivedPullback
    (K : DerivedCategory (OXMod.{u, u} X)) (U : Opens X.carrier)
    (h : IsPerfect (X := X.restrict U.isOpenEmbedding)
      ((derivedPullback (X.ofRestrict U.isOpenEmbedding)).obj K)) :
    IsPerfect (X := X.restrict U.isOpenEmbedding)
      ((restrictModules.{u} X U).mapDerivedCategory.obj K) :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
    (X := X.restrict U.isOpenEmbedding)
    ((Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackModuleRestrictionIso X U).app K) h

/-- **Perfectness on a covering implies perfectness, for the derived pullback.** The same
statement as `Stacks.Cohomology.PerfectComplexes.isPerfect_of_isPerfect_restrict_cover` with the
restriction of `K` to `U i` taken to be the derived pullback `Lj_{U i}^*K` along the inclusion of
the open subspace — equivalently `Stacks.Cohomology.GlueingComplexes.derivedRestrict`, which is
an abbreviation for that pullback and the functor [Stacks, Tag 08DG] is stated in.

Derived pullback along the inclusion of an open subspace is the derived functor of degreewise
restriction, by
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackModuleRestrictionIso`, and perfectness is
invariant under isomorphism. -/
theorem isPerfect_of_isPerfect_derivedPullback_cover (K : DerivedCategory (OXMod.{u, u} X))
    {I : Type*} (U : I → Opens X.carrier) (hU : (⨆ i, U i) = ⊤)
    (h : ∀ i, IsPerfect (X := X.restrict (U i).isOpenEmbedding)
      ((derivedPullback (X.ofRestrict (U i).isOpenEmbedding)).obj K)) :
    IsPerfect (X := X) K := by
  exact isPerfect_of_isPerfect_restrict_cover K U hU fun i =>
    isPerfect_restrict_of_isPerfect_derivedPullback K (U i) (h i)

/-- **Perfectness is detected by a covering by two opens, for the derived pullback.** If
`U ⊔ V = ⊤` and both `Lj_U^*K` and `Lj_V^*K` are perfect, then `K` is perfect.

This is the form in which the perfectness clause of a glueing along two opens is used, the
glueing lemma [Stacks, Tag 08DG] being stated for the derived pullback. -/
theorem isPerfect_of_isPerfect_derivedPullback_sup_eq_top (K : DerivedCategory (OXMod.{u, u} X))
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (hU : IsPerfect (X := X.restrict U.isOpenEmbedding)
      ((derivedPullback (X.ofRestrict U.isOpenEmbedding)).obj K))
    (hV : IsPerfect (X := X.restrict V.isOpenEmbedding)
      ((derivedPullback (X.ofRestrict V.isOpenEmbedding)).obj K)) :
    IsPerfect (X := X) K := by
  exact isPerfect_of_isPerfect_restrict_sup_eq_top K U V hUV
    (isPerfect_restrict_of_isPerfect_derivedPullback K U hU)
    (isPerfect_restrict_of_isPerfect_derivedPullback K V hV)

end Stacks.Cohomology.PerfectComplexes

end
