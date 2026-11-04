module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.CommonRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Refinements of constructible stratifications

A constructible stratification of an open subscheme `U` of `X` is a finite partition of `U` by
constructible locally closed subschemes. Two such partitions have a common refinement, obtained by
intersecting the strata pairwise, the intersection being realized by the fibre product of the two
immersions; and a finite family of partitions has a common refinement, obtained by iterating.

This is the combinatorial input to the closure properties of constructible sheaves: a finite
diagram of constructible sheaves is trivialized stratum by stratum only after the finitely many
stratifications produced by its objects have been replaced by one that refines them all.

## Main definitions

* `AlgebraicGeometry.ConstructibleStratification.FactorsThroughStrata` — one stratification
  refines another when each of its strata factors through a stratum of the other.
* `AlgebraicGeometry.ConstructibleStratification.refineFinite` — a common refinement of a finite
  family of stratifications.
* `AlgebraicGeometry.ConstructibleStratification.single` — the one-stratum stratification of `U`
  by itself.

## Main results

* `AlgebraicGeometry.ConstructibleStratification.inf_factorsThroughStrata_left` and
  `…_right` — the common refinement refines both of its arguments, in the sense of
  `AlgebraicGeometry.ConstructibleStratification.FactorsThroughStrata`.
* `AlgebraicGeometry.ConstructibleStratification.refineFinite_refines` — a common refinement of a
  finite family refines every member.

## Implementation notes

The pairwise intersection of two stratifications is
`AlgebraicGeometry.ConstructibleStratification.inf` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.CommonRefinement`, not a second
construction here; this module only reads its refinement property off in the
`FactorsThroughStrata` form the iteration below consumes.
`AlgebraicGeometry.range_comp_eq_inter_of_isPullback`, which computes the image of a fibre
product and is the reason such a pairwise intersection is again an immersion with
constructible, pairwise disjoint and covering image, stays here as a general lemma about
schemes.

The common refinement of a finite family is defined by recursion on a list of indices rather than
by a `Finset.fold`, because the carrier of a stratification is data and not a subsingleton: the
recursion produces one stratification, and the refinement property is proved by induction over the
same list.

## References

* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- The image of a fibre product of schemes, along either projection followed by the
corresponding morphism, is the intersection of the two images. -/
public theorem range_comp_eq_inter_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) :
    Set.range (fst ≫ f).base = Set.range f.base ∩ Set.range g.base := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨⟨fst.base p, rfl⟩, ⟨snd.base p, ?_⟩⟩
    simpa only [Scheme.Hom.comp_base, TopCat.comp_app] using
      (congrArg (fun q : P ⟶ Z => q.base p) h.w).symm
  · rintro ⟨⟨x, rfl⟩, ⟨y, hxy⟩⟩
    obtain ⟨p, hp, -⟩ := Scheme.exists_preimage_of_isPullback h x y hxy.symm
    exact ⟨p, by simp [Scheme.Hom.comp_base, hp]⟩

namespace ConstructibleStratification

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {U : X.obj.Opens}

/-- A stratification `r` refines a stratification `s` when every stratum of `r` factors through
some stratum of `s` over `X`. -/
public def FactorsThroughStrata (r s : ConstructibleStratification B X U) : Prop :=
  ∀ k, ∃ l, ∃ f : r.piece k ⟶ s.piece l, f ≫ s.inclusion l = r.inclusion k

/-- Refinement is transitive. -/
public theorem FactorsThroughStrata.trans {r s t : ConstructibleStratification B X U}
    (hrs : FactorsThroughStrata r s) (hst : FactorsThroughStrata s t) :
    FactorsThroughStrata r t := by
  intro k
  obtain ⟨l, f, hf⟩ := hrs k
  obtain ⟨m, g, hg⟩ := hst l
  exact ⟨m, f ≫ g, by rw [Category.assoc, hg, hf]⟩

section CommonRefinement

variable (s t : ConstructibleStratification B X U)

-- NO SECOND COMMON REFINEMENT HERE. This section used to build one from scratch --
-- `leftIndex`, `rightIndex`, `refinementPiece`, `refinementInclusion`,
-- `isPullback_refinement`, `range_refinementInclusion` and `commonRefinement` -- duplicating
-- `AlgebraicGeometry.ConstructibleStratification.inf` and its helpers `interPiece`,
-- `interFst`, `interSnd`, `interInclusion`, `range_interInclusion` of
-- `StacksFrontier/AlgebraicGeometry/EtaleCohomology/Constructible/CommonRefinement.lean`.
-- Both are the stratification whose strata are the pairwise fibre products, with the same
-- `n := s.n * t.n` and the same field proofs; they differed only in where the fibre product
-- was taken (`inf` takes it in `Scheme` and repackages with a size proof, this one took it
-- in `B.Scheme`), which is why the merge needed these two bridging lemmas rather than a
-- rename. `inf` is the survivor: it has the smaller import closure and the consumers.

/-- The common refinement of two stratifications refines the first. -/
public theorem inf_factorsThroughStrata_left : FactorsThroughStrata (s.inf t) s :=
  fun k =>
    let ⟨i, a, _, h⟩ := inf_factorsThrough_fst s t k
    ⟨i, a, h⟩

/-- The common refinement of two stratifications refines the second. -/
public theorem inf_factorsThroughStrata_right : FactorsThroughStrata (s.inf t) t :=
  fun k =>
    let ⟨j, b, _, h⟩ := inf_factorsThrough_snd s t k
    ⟨j, b, h⟩

end CommonRefinement

section Finite

variable {I : Type*} (S : I → ConstructibleStratification B X U)

/-- The common refinement of the stratifications indexed by a list, taken into an accumulator. -/
public def refineList : List I → ConstructibleStratification B X U →
    ConstructibleStratification B X U
  | [], acc => acc
  | i :: is, acc => (S i).inf (refineList is acc)

/-- The common refinement along a list refines the stratification at each index on the list. -/
public theorem refineList_refines :
    ∀ (is : List I) (acc : ConstructibleStratification B X U) (i : I), i ∈ is →
      FactorsThroughStrata (refineList S is acc) (S i) := by
  intro is
  induction is with
  | nil => simp
  | cons j js ih =>
      intro acc i hi
      obtain rfl | hi := List.mem_cons.mp hi
      · exact inf_factorsThroughStrata_left (S i) (refineList S js acc)
      · exact FactorsThroughStrata.trans
          (inf_factorsThroughStrata_right (S j) (refineList S js acc)) (ih acc i hi)

variable [Fintype I]

/-- **A common refinement of a finite family of stratifications**, refining in addition a given
stratification used as the starting point. -/
public def refineFinite (acc : ConstructibleStratification B X U) :
    ConstructibleStratification B X U :=
  refineList S Finset.univ.toList acc

/-- The common refinement of a finite family refines every member of the family. -/
public theorem refineFinite_refines (acc : ConstructibleStratification B X U) (i : I) :
    FactorsThroughStrata (refineFinite S acc) (S i) :=
  refineList_refines S Finset.univ.toList acc i (Finset.mem_toList.mpr (Finset.mem_univ i))

end Finite

/-- **The one-stratum stratification.** An open subscheme of `X` is an immersed, constructible
stratum of itself, so it carries a stratification with a single piece. -/
public def single (B : BigEtaleSite.{u}) (X : B.Scheme) (U : X.obj.Opens) :
    ConstructibleStratification B X U :=
  let Z : B.Scheme :=
    ⟨U.toScheme, lt_of_le_of_lt (Scheme.size_coe_opens_le X.obj U) X.property⟩
  let j : Z ⟶ X := B.inclusion.preimage U.ι
  have hj : B.inclusion.map j = U.ι := B.inclusion.map_preimage _
  { n := 1
    piece := fun _ => Z
    inclusion := fun _ => j
    isImmersion := fun _ => by rw [hj]; infer_instance
    contained := fun _ => by rw [hj, Scheme.Opens.range_ι]
    constructible := fun _ => by
      rw [hj, Set.preimage_range]
      exact Topology.IsConstructible.univ
    pairwise_disjoint := fun _ _ h => (h (Subsingleton.elim _ _)).elim
    covers := by
      ext x
      simp only [Set.mem_iUnion]
      rw [hj, Scheme.Opens.range_ι]
      simp }

end ConstructibleStratification

end AlgebraicGeometry

end
