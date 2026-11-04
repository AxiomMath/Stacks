module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DirectedComapNhds
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.PointTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.Reduced
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace

/-!
# The closure of a point of an inverse limit of algebraic spaces

Let `X = limit D` be the limit of a cofiltered inverse system `D` of algebraic spaces over a
scheme `S` with affine transition morphisms, as in Stacks 07SF, and let `x` be a point of `X`
with images `x i` in the stages. The closure of `x` is the inverse limit of the closures of the
`x i`, both as sets and as algebraic spaces: as a subset of `|X|` it is the intersection of the
preimages of those closures, and with the reduced induced structures of Stacks 047X it is the
limit of the reduced closures of the `x i`.

## Main results

* `AlgebraicGeometry.Space.closure_singleton_limit`: the closure of `x` is the intersection
  of the preimages of the closures of the `x i`.
* `AlgebraicGeometry.Space.existsUnique_point_closure_limit`: a compatible family of points
  of the closures of the `x i` comes from a unique point, which lies in the closure of `x`.
* `AlgebraicGeometry.Space.exists_iso_limit_reducedClosure`: the reduced induced structure on
  the closure of `x` is the limit of the reduced induced structures on the closures of the
  `x i`.
* `AlgebraicGeometry.Space.closure_singleton_limit_of_mono`,
  `AlgebraicGeometry.Space.existsUnique_point_closure_limit_of_monoBoundedBy` and
  `AlgebraicGeometry.Space.exists_iso_limit_reducedClosure_of_mono`: the same three
  conclusions from the cofinality-free cardinality hypothesis, at the cost of monomorphic
  transition morphisms. For the third this has to survive the passage to the derived diagram
  of reduced closures, and it does: a reduced closed subspace inclusion is a monomorphism, so
  the derived transition morphisms are monomorphisms again.

## Implementation notes

The inclusion of the closure of `x` in each preimage is continuity of the limit projections
on points, clause (2) of Stacks 03BX. The reverse inclusion is the assertion that a point `y`
outside the closure of `x` is separated from `x` already at some stage, and that is read off
from Stacks 086V: the point topology of the limit is the infimum of the topologies induced by
the projections, so the neighbourhood filter at `y` is the infimum of the filters pulled back
from the stages, and cofilteredness of the index category makes that family of filters
downward directed, so a neighbourhood of `y` in the limit contains the preimage of a
neighbourhood of `y i` at a single stage `i`. This is the role played in the source by
Topology, Lemma 0A2P, which writes an open of a limit as a union of preimages of opens of the
stages.

Neither inclusion uses decency; decency enters only through Stacks 0CUJ, which turns the
set-level equality into the statement about compatible families of points.

The reduced closures of the `x i` form an inverse system because a morphism of algebraic
spaces carries the reduced closure of a point into the reduced closure of its image, by
Stacks 03JJ: a morphism out of a reduced algebraic space factors through a closed subspace as
soon as its image on points lies there. The transition morphisms of that system are affine,
being affine after composition with a closed immersion, so the system has a limit which is an
algebraic space by Stacks 07SF and is reduced by Stacks 0CUI. The set-level assertion then
produces the two factorizations which identify that limit with the reduced closure of `x`:
the points of the reduced closure of `x` lie in each closure of an `x i`, and the points of
the limit lie in every preimage of one, hence in the closure of `x`. Both composites are
identities because the inclusions of closed subspaces are monomorphisms; this is where the
source instead invokes Stacks 0CUH and the uniqueness of the reduced induced structure.

## References

* [Stacks Project, Tag 0CUK](https://stacks.math.columbia.edu/tag/0CUK)
* [Stacks Project, Tag 0CUJ](https://stacks.math.columbia.edu/tag/0CUJ)
* [Stacks Project, Tag 0CUI](https://stacks.math.columbia.edu/tag/0CUI)
* [Stacks Project, Tag 086V](https://stacks.math.columbia.edu/tag/086V)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 0A2P](https://stacks.math.columbia.edu/tag/0A2P)
* [Stacks Project, Tag 047X](https://stacks.math.columbia.edu/tag/047X)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Stage neighbourhoods in an inverse-limit topology -/

/-- For the infimum of the topologies induced by a family of maps `p i : X → Y i`, whose pulled
back neighbourhood filters at a point `x` are downward directed, the preimages of the open sets
of the `Y i` form a neighbourhood basis at `x`. -/
private theorem exists_stage_nbhd_of_eq_iInf {ι : Type*} [Nonempty ι] {X : Type*}
    {Y : ι → Type*} (t : ∀ i, TopologicalSpace (Y i)) (p : ∀ i, X → Y i)
    [tX : TopologicalSpace X] (htX : tX = ⨅ i, TopologicalSpace.induced (p i) (t i)) (x : X)
    (hdir : Directed (· ≥ ·) fun i ↦ Filter.comap (p i) (@nhds _ (t i) (p i x)))
    {W : Set X} (hW : IsOpen W) (hx : x ∈ W) :
    ∃ (i : ι) (V : Set (Y i)), @IsOpen _ (t i) V ∧ p i x ∈ V ∧ p i ⁻¹' V ⊆ W := by
  have hmem : W ∈ nhds x := hW.mem_nhds hx
  rw [htX] at hmem
  simp only [nhds_iInf, nhds_induced] at hmem
  obtain ⟨i, hi⟩ := (Filter.mem_iInf_of_directed hdir W).1 hmem
  obtain ⟨V, hV, hVW⟩ := Filter.mem_comap.1 hi
  obtain ⟨V', hV'V, hV'open, hxV'⟩ := mem_nhds_iff.1 hV
  exact ⟨i, V', hV'open, hxV', fun y hy ↦ hVW (hV'V hy)⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-! ### The closure of a point of the limit -/

/-- **Stacks 0CUK, as sets**, from the topological statement of Stacks 086V. This is the
common core of the two forms below: the only use either makes of its cardinality hypotheses
is to know that the point topology of the limit is the inverse-limit topology. -/
theorem closure_singleton_limit_of_pointTopology
    (htop : pointTopology B S hS (limit D) =
      ⨅ i : I, TopologicalSpace.induced (pointsMap B S hS (limit D) (limit.π D i))
        (pointTopology B S hS (D.obj i)))
    (x : points B S hS (limit D)) :
    closure {x} = ⋂ i : I, pointsMap B S hS (limit D) (limit.π D i) ⁻¹'
      closure {pointsMap B S hS (limit D) (limit.π D i) x} := by
  have _ := IsCofiltered.nonempty (C := I)
  refine Set.Subset.antisymm (Set.subset_iInter fun i ↦ closure_minimal
    (Set.singleton_subset_iff.2 (subset_closure rfl))
    (isClosed_closure.preimage (continuous_pointsMap B S hS (limit.π D i)))) ?_
  intro y hy
  by_contra hynot
  obtain ⟨i, V, hV, hyV, hsub⟩ := exists_stage_nbhd_of_eq_iInf
    (fun i : I ↦ pointTopology B S hS (D.obj i))
    (fun i : I ↦ pointsMap B S hS (limit D) (limit.π D i))
    htop y
    (directedGE_comap_nhds_limitπ B S hS D y)
    isClosed_closure.isOpen_compl hynot
  obtain ⟨z, hzV, hz⟩ := mem_closure_iff.1 (Set.mem_iInter.1 hy i) V hV hyV
  have hxV : pointsMap B S hS (limit D) (limit.π D i) x ∈ V := by
    rw [← Set.mem_singleton_iff.1 hz]
    exact hzV
  exact hsub hxV (subset_closure rfl)

/-- **Stacks 0CUK, as sets.** Let `x` be a point of the limit `X` of a cofiltered inverse
system of algebraic spaces over `S` with affine transition morphisms, with images `x i` in the
stages. The closure of `x` in `|X|` is the intersection of the preimages of the closures of
the `x i`, that is, the inverse limit of those closures. -/
@[stacks 0CUK "as sets"]
theorem closure_singleton_limit (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (x : points B S hS (limit D)) :
    closure {x} = ⋂ i : I, pointsMap B S hS (limit D) (limit.π D i) ⁻¹'
      closure {pointsMap B S hS (limit D) (limit.π D i) x} :=
  closure_singleton_limit_of_pointTopology B S hS D
    (pointTopology_limit B S hS D hSize hHomSize hD hAffine) x

/-- **The closure of a point of the limit, with no cofinality hypothesis.** This is
`AlgebraicGeometry.Space.closure_singleton_limit` with the cardinality bound on the index
category traded for a bound by the cutoff itself together with monomorphic transition
morphisms, through `AlgebraicGeometry.Space.pointTopology_limit_of_mono`. The two hypotheses
are incomparable, and `@[stacks 0CUK]` stays on the form carrying the source's own one. -/
theorem closure_singleton_limit_of_mono {ν : Cardinal.{u}} (hSize : #I < B.cutoff)
    (hν : ν < B.cutoff) (hHomSize : ∀ i j : I, #(i ⟶ j) ≤ ν)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hMono : ∀ {i j : I} (f : i ⟶ j), Mono (D.map f))
    (x : points B S hS (limit D)) :
    closure {x} = ⋂ i : I, pointsMap B S hS (limit D) (limit.π D i) ⁻¹'
      closure {pointsMap B S hS (limit D) (limit.π D i) x} :=
  closure_singleton_limit_of_pointTopology B S hS D
    (pointTopology_limit_of_mono B S hS D hSize hν hHomSize hD hAffine hMono) x

/-- **The closure of a point of the limit, for a system with uniformly bounded base changes.**
This is `AlgebraicGeometry.Space.closure_singleton_limit` with the cardinality bound on the
index category traded for a bound by the cutoff itself together with
`AlgebraicGeometry.Space.BaseChangeSizeBounded`, through
`AlgebraicGeometry.Space.pointTopology_limit_of_baseChangeSizeBounded`. -/
theorem closure_singleton_limit_of_baseChangeSizeBounded {ν : Cardinal.{u}}
    (hSize : #I < B.cutoff) (hν : ν < B.cutoff) (hHomSize : ∀ i j : I, #(i ⟶ j) ≤ ν)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hB : BaseChangeSizeBounded B S hS D)
    (x : points B S hS (limit D)) :
    closure {x} = ⋂ i : I, pointsMap B S hS (limit D) (limit.π D i) ⁻¹'
      closure {pointsMap B S hS (limit D) (limit.π D i) x} :=
  closure_singleton_limit_of_pointTopology B S hS D
    (pointTopology_limit_of_baseChangeSizeBounded B S hS D hSize hν hHomSize hD hAffine hB) x

omit [IsCofiltered I] in
/-- **Stacks 0CUK, as sets.** The set-level assertion read through the identification
`|X| = lim |D i|` of Stacks 0CUJ: for a decent system, a family of points `z i` of the stages
which is compatible with the transition morphisms and lies in the closures of the images `x i`
of a point `x` of the limit is the family of images of exactly one point of the limit, and
that point lies in the closure of `x`. -/
theorem existsUnique_point_closure_limit_of_existsUnique_point
    (x : points B S hS (limit D)) (z : ∀ i, points B S hS (D.obj i))
    (hpoint : ∃! y : points B S hS (limit D),
      ∀ i, pointsMap B S hS (limit D) (limit.π D i) y = z i)
    (hclosure : closure {x} = ⋂ i : I, pointsMap B S hS (limit D) (limit.π D i) ⁻¹'
      closure {pointsMap B S hS (limit D) (limit.π D i) x})
    (hzmem : ∀ i, z i ∈ closure {pointsMap B S hS (limit D) (limit.π D i) x}) :
    ∃! y : points B S hS (limit D), y ∈ closure {x} ∧
      ∀ i, pointsMap B S hS (limit D) (limit.π D i) y = z i := by
  obtain ⟨y, hy, huniq⟩ := hpoint
  refine ⟨y, ⟨?_, hy⟩, fun y' hy' ↦ huniq y' hy'.2⟩
  rw [hclosure]
  exact Set.mem_iInter.2 fun i ↦ by rw [Set.mem_preimage, hy i]; exact hzmem i

/-- **Stacks 0CUK, as sets.** The set-level assertion read through the identification
`|X| = lim |D i|` of Stacks 0CUJ, for a compatible family of points. -/
@[stacks 0CUK "as sets, for a compatible family of points"]
theorem existsUnique_point_closure_limit (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hDecent : ∀ i, IsDecentSpace B S hS (D.obj i))
    (x : points B S hS (limit D)) (z : ∀ i, points B S hS (D.obj i))
    (hz : ∀ {i j : I} (f : i ⟶ j), pointsMap B S hS (D.obj i) (D.map f) (z i) = z j)
    (hzmem : ∀ i, z i ∈ closure {pointsMap B S hS (limit D) (limit.π D i) x}) :
    ∃! y : points B S hS (limit D), y ∈ closure {x} ∧
      ∀ i, pointsMap B S hS (limit D) (limit.π D i) y = z i :=
  existsUnique_point_closure_limit_of_existsUnique_point B S hS D x z
    (existsUnique_point_limit B S hS D hSize hHomSize hD hAffine hDecent z hz)
    (closure_singleton_limit B S hS D hSize hHomSize hD hAffine x) hzmem

/-- **The same, with no cofinality hypothesis.** The index category is only asked to have
fewer objects than the site's size cutoff with all its morphism types bounded by one cardinal
`ν` below it, in exchange for monomorphic transition morphisms and for the system being
bounded by one object of the site in the sense of
`AlgebraicGeometry.Space.MonoBoundedBy`, which is what
`AlgebraicGeometry.Space.existsUnique_point_limit_of_monoBoundedBy` consumes. The two
hypotheses are incomparable, and `@[stacks 0CUK]` stays on the form carrying the source's own
one. -/
theorem existsUnique_point_closure_limit_of_monoBoundedBy {ν : Cardinal.{u}}
    (hSize : #I < B.cutoff) (hν : ν < B.cutoff) (hHomSize : ∀ i j : I, #(i ⟶ j) ≤ ν)
    {Z : BigFppfOver B S hS} (hZ : MonoBoundedBy B S hS D Z)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hMono : ∀ {i j : I} (f : i ⟶ j), Mono (D.map f))
    (hDecent : ∀ i, IsDecentSpace B S hS (D.obj i))
    (x : points B S hS (limit D)) (z : ∀ i, points B S hS (D.obj i))
    (hz : ∀ {i j : I} (f : i ⟶ j), pointsMap B S hS (D.obj i) (D.map f) (z i) = z j)
    (hzmem : ∀ i, z i ∈ closure {pointsMap B S hS (limit D) (limit.π D i) x}) :
    ∃! y : points B S hS (limit D), y ∈ closure {x} ∧
      ∀ i, pointsMap B S hS (limit D) (limit.π D i) y = z i :=
  existsUnique_point_closure_limit_of_existsUnique_point B S hS D x z
    (existsUnique_point_limit_of_monoBoundedBy B S hS D hSize hZ hD hDecent z hz)
    (closure_singleton_limit_of_mono B S hS D hSize hν hHomSize hD hAffine hMono x) hzmem

/-! ### The reduced induced structure on the closure of a point -/

omit [IsCofiltered I] in
/-- The image of a point of the limit at a later stage is the image of its image at an earlier
one. -/
private theorem pointsMap_limitπ_map (x : points B S hS (limit D)) {i j : I} (f : i ⟶ j) :
    pointsMap B S hS (D.obj i) (D.map f)
        (pointsMap B S hS (limit D) (limit.π D i) x) =
      pointsMap B S hS (limit D) (limit.π D j) x := by
  rw [← pointsMap_comp_apply, limit.w]

/-- The reduced induced structure on a closed subset is a reduced closed subspace whose points are
exactly that subset. -/
private theorem reducedClosedSubspace_spec {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (T : Set (points B S hS X)) (hT : IsClosed T) :
    IsClosedSubspace B S hS (reducedClosedSubspace B S hS X hX T hT) ∧
      Set.range (pointsMap B S hS (reducedClosedSubspace B S hS X hX T hT).toFunctor
        (reducedClosedSubspace B S hS X hX T hT).ι) = T ∧
      HasEtaleLocalProperty B S hS (reducedClosedSubspace B S hS X hX T hT).toFunctor
        (fun Y : Scheme.{u} ↦ IsReduced Y) :=
  ⟨isClosedSubspace_reducedClosedSubspace B S hS X hX T hT,
    range_pointsMap_ι_reducedClosedSubspace B S hS X hX T hT,
    hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X hX T hT⟩

/-- A morphism of algebraic spaces over `S` carries the reduced induced structure on the
closure of a point into the reduced induced structure on the closure of its image. -/
private theorem exists_lift_reducedClosure {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (x : points B S hS X) (y : points B S hS Y) (hxy : pointsMap B S hS X f x = y) :
    ∃ g : (reducedClosedSubspace B S hS X hX (closure {x}) isClosed_closure).toFunctor ⟶
        (reducedClosedSubspace B S hS Y hY (closure {y}) isClosed_closure).toFunctor,
      g ≫ (reducedClosedSubspace B S hS Y hY (closure {y}) isClosed_closure).ι =
        (reducedClosedSubspace B S hS X hX (closure {x}) isClosed_closure).ι ≫ f := by
  obtain ⟨hXc, hXr, hXred⟩ := reducedClosedSubspace_spec B S hS hX (closure {x}) isClosed_closure
  obtain ⟨hYc, hYr, -⟩ := reducedClosedSubspace_spec B S hS hY (closure {y}) isClosed_closure
  refine (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS hY hXc.1 _ hYc hXred _).2 ?_
  rw [hYr, pointsMap_comp, Set.range_comp, hXr, ← hxy]
  have himg := image_closure_subset_closure_image
    (continuous_pointsMap B S hS f) (s := ({x} : Set (points B S hS X)))
  rwa [Set.image_singleton] at himg

omit [IsCofiltered I] in
/-- **Stacks 0CUK, as algebraic spaces.** Let `x` be a point of the limit `X` of a cofiltered
inverse system of algebraic spaces over `S` with affine transition morphisms. The closure of
`x`, with its reduced induced structure, is the limit of the closures of the images `x i` with
theirs: those closures form an inverse system of algebraic spaces with affine transition
morphisms, its limit is reduced, and the inclusion of the closure of `x` into `X` factors
through an isomorphism onto that limit. -/
theorem exists_iso_limit_reducedClosure_of_limitReduced
    (hLim : IsAlgebraicSpace B S hS (limit D))
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (x : points B S hS (limit D))
    (hclosure : closure {x} = ⋂ i : I, pointsMap B S hS (limit D) (limit.π D i) ⁻¹'
      closure {pointsMap B S hS (limit D) (limit.π D i) x})
    (hderived : ∀ (E : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (η : E ⟶ D),
      (∀ i, IsAlgebraicSpace B S hS (E.obj i)) →
      (∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (E.map f)) →
      (∀ i, Mono (η.app i)) →
      (∀ i, HasEtaleLocalProperty B S hS (E.obj i) (fun Y : Scheme.{u} ↦ IsReduced Y)) →
      IsAlgebraicSpace B S hS (limit E) ∧
        HasEtaleLocalProperty B S hS (limit E) (fun Y : Scheme.{u} ↦ IsReduced Y)) :
    ∃ (E : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (η : E ⟶ D)
      (e : (reducedClosedSubspace B S hS (limit D)
          hLim
          (closure {x}) isClosed_closure).toFunctor ≅ limit E),
      (∀ i : I, ∃ eᵢ : E.obj i ≅ (reducedClosedSubspace B S hS (D.obj i) (hD i)
            (closure {pointsMap B S hS (limit D) (limit.π D i) x}) isClosed_closure).toFunctor,
          eᵢ.hom ≫ (reducedClosedSubspace B S hS (D.obj i) (hD i)
            (closure {pointsMap B S hS (limit D) (limit.π D i) x}) isClosed_closure).ι
            = η.app i) ∧
        (∀ i, IsAlgebraicSpace B S hS (E.obj i)) ∧
        (∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (E.map f)) ∧
        HasEtaleLocalProperty B S hS (limit E) (fun Y : Scheme.{u} ↦ IsReduced Y) ∧
        e.hom ≫ limMap η = (reducedClosedSubspace B S hS (limit D)
          hLim
          (closure {x}) isClosed_closure).ι := by
  classical
  -- the reduced induced structures on the closures of the images of `x`
  let A : ∀ i : I, Subfunctor (D.obj i) := fun i ↦
    reducedClosedSubspace B S hS (D.obj i) (hD i)
      (closure {pointsMap B S hS (limit D) (limit.π D i) x}) isClosed_closure
  have hA := fun i ↦ reducedClosedSubspace_spec B S hS (hD i)
    (closure {pointsMap B S hS (limit D) (limit.π D i) x}) isClosed_closure
  have hAc : ∀ i, IsClosedSubspace B S hS (A i) := fun i ↦ (hA i).1
  have hAr : ∀ i : I, Set.range (pointsMap B S hS (A i).toFunctor (A i).ι) =
      closure {pointsMap B S hS (limit D) (limit.π D i) x} := fun i ↦ (hA i).2.1
  have hAred : ∀ i, HasEtaleLocalProperty B S hS (A i).toFunctor
      (fun Y : Scheme.{u} ↦ IsReduced Y) := fun i ↦ (hA i).2.2
  -- they form an inverse system over `D`
  have hlift : ∀ {i j : I} (f : i ⟶ j), ∃ g : (A i).toFunctor ⟶ (A j).toFunctor,
      g ≫ (A j).ι = (A i).ι ≫ D.map f := fun {i j} f ↦
    exists_lift_reducedClosure B S hS (hD i) (hD j) (D.map f) _ _
      (pointsMap_limitπ_map B S hS D x f)
  have hm : ∀ {i j : I} (f : i ⟶ j),
      Classical.choose (hlift f) ≫ (A j).ι = (A i).ι ≫ D.map f := fun f ↦
    Classical.choose_spec (hlift f)
  let E : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
    { obj := fun i ↦ (A i).toFunctor
      map := fun {i j} f ↦ Classical.choose (hlift f)
      map_id := fun i ↦ by
        refine (cancel_mono (A i).ι).1 ?_
        rw [hm, D.map_id, Category.comp_id, Category.id_comp]
      map_comp := fun {i j k} f g ↦ by
        refine (cancel_mono (A k).ι).1 ?_
        rw [Category.assoc, hm g, reassoc_of% (hm f), hm, D.map_comp] }
  let η : E ⟶ D := { app := fun i ↦ (A i).ι, naturality := fun i j f ↦ hm f }
  have hE : ∀ i, IsAlgebraicSpace B S hS (E.obj i) := fun i ↦ (hAc i).1
  have hηAffine : ∀ i, IsAffineHom B S hS (η.app i) := fun i ↦
    isAffineHom_of_isClosedImmersion B S hS _ (hAc i).2
  have hEAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (E.map f) := by
    intro i j f
    refine isAffineHom_of_isAffineHom_comp_of_isSeparated B S hS (E.map f) (η.app j) ?_
      (isSeparated_of_isClosedImmersion B S hS (η.app j) (hAc j).2)
    rw [show E.map f ≫ η.app j = η.app i ≫ D.map f from hm f]
    exact isAffineHom_comp B S hS _ _ (hηAffine i) (hAffine f)
  have hηMono : ∀ i, Mono (η.app i) := fun i ↦ inferInstanceAs (Mono (A i).ι)
  obtain ⟨hELim, hELimRed⟩ := hderived E η hE hEAffine hηMono hAred
  -- the reduced induced structure on the closure of `x` itself
  let Z : Subfunctor (limit D) :=
    reducedClosedSubspace B S hS (limit D) hLim (closure {x}) isClosed_closure
  obtain ⟨hZc, hZr, hZred⟩ :=
    reducedClosedSubspace_spec B S hS hLim (closure {x}) isClosed_closure
  -- it maps to every stage, by the set-level assertion
  have hγ : ∀ i : I, ∃ g : Z.toFunctor ⟶ E.obj i, g ≫ (A i).ι = Z.ι ≫ limit.π D i := by
    intro i
    refine (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS (hD i) hZc.1
      (A i) (hAc i) hZred _).2 ?_
    rw [hAr i, pointsMap_comp, Set.range_comp, hZr, hclosure]
    rintro z ⟨w, hw, rfl⟩
    exact Set.mem_iInter.1 hw i
  choose γ hγ' using hγ
  let cZ : Cone E :=
    { pt := Z.toFunctor
      π :=
        { app := γ
          naturality := fun i j f ↦ by
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
            refine (cancel_mono (A j).ι).1 ?_
            rw [Category.assoc, hm f, reassoc_of% (hγ' i), limit.w, hγ' j] } }
  let eHom : Z.toFunctor ⟶ limit E := limit.lift E cZ
  have heHom : ∀ i, eHom ≫ limit.π E i = γ i := fun i ↦ limit.lift_π cZ i
  have heIncl : eHom ≫ limMap η = Z.ι := by
    refine limit.hom_ext fun i ↦ ?_
    rw [Category.assoc, limMap_π, ← Category.assoc, heHom]
    exact hγ' i
  -- conversely the limit of the stages maps to the closure of `x`
  obtain ⟨δ, hδfac⟩ : ∃ δ : limit E ⟶ Z.toFunctor, δ ≫ Z.ι = limMap η := by
    refine (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS hLim hELim Z hZc
      hELimRed _).2 ?_
    rw [hZr, hclosure]
    rintro z ⟨q, rfl⟩
    refine Set.mem_iInter.2 fun i ↦ ?_
    have hcomp : pointsMap B S hS (limit D) (limit.π D i)
          (pointsMap B S hS (limit E) (limMap η) q) =
        pointsMap B S hS (E.obj i) (η.app i)
          (pointsMap B S hS (limit E) (limit.π E i) q) := by
      rw [← pointsMap_comp_apply, limMap_π, pointsMap_comp_apply]
    rw [Set.mem_preimage, hcomp, ← hAr i]
    exact ⟨_, rfl⟩
  refine ⟨E, η, { hom := eHom, inv := δ, hom_inv_id := ?_, inv_hom_id := ?_ },
    fun i ↦ ⟨Iso.refl _, Category.id_comp _⟩, hE, hEAffine, hELimRed, heIncl⟩
  · refine (cancel_mono Z.ι).1 ?_
    rw [Category.assoc, hδfac, heIncl, Category.id_comp]
  · refine limit.hom_ext fun i ↦ ?_
    refine (cancel_mono (A i).ι).1 ?_
    simp only [Category.assoc, Category.id_comp, heHom, hγ']
    rw [← Category.assoc, hδfac, limMap_π]

/-- **Stacks 0CUK, as algebraic spaces.** Let `x` be a point of the limit `X` of a cofiltered
inverse system of algebraic spaces over `S` with affine transition morphisms. The closure of
`x`, with its reduced induced structure, is the limit of the closures of the images `x i` with
theirs: those closures form an inverse system of algebraic spaces with affine transition
morphisms, its limit is reduced, and the inclusion of the closure of `x` into `X` factors
through an isomorphism onto that limit. -/
@[stacks 0CUK "as algebraic spaces with the reduced induced structure"]
theorem exists_iso_limit_reducedClosure (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (x : points B S hS (limit D)) :
    ∃ (E : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (η : E ⟶ D)
      (e : (reducedClosedSubspace B S hS (limit D)
          (isAlgebraicSpace_limit B S hS D hSize hHomSize hD hAffine)
          (closure {x}) isClosed_closure).toFunctor ≅ limit E),
      (∀ i : I, ∃ eᵢ : E.obj i ≅ (reducedClosedSubspace B S hS (D.obj i) (hD i)
            (closure {pointsMap B S hS (limit D) (limit.π D i) x}) isClosed_closure).toFunctor,
          eᵢ.hom ≫ (reducedClosedSubspace B S hS (D.obj i) (hD i)
            (closure {pointsMap B S hS (limit D) (limit.π D i) x}) isClosed_closure).ι
            = η.app i) ∧
        (∀ i, IsAlgebraicSpace B S hS (E.obj i)) ∧
        (∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (E.map f)) ∧
        HasEtaleLocalProperty B S hS (limit E) (fun Y : Scheme.{u} ↦ IsReduced Y) ∧
        e.hom ≫ limMap η = (reducedClosedSubspace B S hS (limit D)
          (isAlgebraicSpace_limit B S hS D hSize hHomSize hD hAffine)
          (closure {x}) isClosed_closure).ι :=
  exists_iso_limit_reducedClosure_of_limitReduced B S hS D
    (isAlgebraicSpace_limit B S hS D hSize hHomSize hD hAffine) hD hAffine x
    (closure_singleton_limit B S hS D hSize hHomSize hD hAffine x)
    fun E _ hE hEAffine _ hAred ↦
      ⟨isAlgebraicSpace_limit B S hS E hSize hHomSize hE hEAffine,
        isReduced_limit B S hS E hSize hHomSize hE hEAffine hAred⟩

/-- **The reduced closure of a point of the limit, with no cofinality hypothesis.** The index
category is only asked to have fewer objects than the site's size cutoff with all its morphism
types bounded by one cardinal `ν` below it, in exchange for monomorphic transition morphisms.

The two hypotheses are incomparable, and `@[stacks 0CUK]` stays on the form carrying the
source's own one. -/
theorem exists_iso_limit_reducedClosure_of_mono {ν : Cardinal.{u}} (hSize : #I < B.cutoff)
    (hν : ν < B.cutoff) (hHomSize : ∀ i j : I, #(i ⟶ j) ≤ ν)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hMono : ∀ {i j : I} (f : i ⟶ j), Mono (D.map f))
    (x : points B S hS (limit D)) :
    ∃ (E : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (η : E ⟶ D)
      (e : (reducedClosedSubspace B S hS (limit D)
          (isAlgebraicSpace_limit_of_mono B S hS D hSize hν hHomSize hD hAffine hMono)
          (closure {x}) isClosed_closure).toFunctor ≅ limit E),
      (∀ i : I, ∃ eᵢ : E.obj i ≅ (reducedClosedSubspace B S hS (D.obj i) (hD i)
            (closure {pointsMap B S hS (limit D) (limit.π D i) x}) isClosed_closure).toFunctor,
          eᵢ.hom ≫ (reducedClosedSubspace B S hS (D.obj i) (hD i)
            (closure {pointsMap B S hS (limit D) (limit.π D i) x}) isClosed_closure).ι
            = η.app i) ∧
        (∀ i, IsAlgebraicSpace B S hS (E.obj i)) ∧
        (∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (E.map f)) ∧
        HasEtaleLocalProperty B S hS (limit E) (fun Y : Scheme.{u} ↦ IsReduced Y) ∧
        e.hom ≫ limMap η = (reducedClosedSubspace B S hS (limit D)
          (isAlgebraicSpace_limit_of_mono B S hS D hSize hν hHomSize hD hAffine hMono)
          (closure {x}) isClosed_closure).ι :=
  exists_iso_limit_reducedClosure_of_limitReduced B S hS D
    (isAlgebraicSpace_limit_of_mono B S hS D hSize hν hHomSize hD hAffine hMono) hD hAffine x
    (closure_singleton_limit_of_mono B S hS D hSize hν hHomSize hD hAffine hMono x)
    fun E η hE hEAffine hηMono hAred ↦
      have hEMono : ∀ {i j : I} (f : i ⟶ j), Mono (E.map f) := by
        intro i j f
        have _ := hηMono i
        have _ := hηMono j
        have _ := hMono f
        exact mono_of_mono_fac (η.naturality f)
      ⟨isAlgebraicSpace_limit_of_mono B S hS E hSize hν hHomSize hE hEAffine hEMono,
        isReduced_limit_of_mono B S hS E hSize hν hHomSize hE hEAffine hEMono hAred⟩

end AlgebraicGeometry.Space

end
