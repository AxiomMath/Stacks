module

public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.Defs
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.EndomorphismProjection
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.ProjMapComparison
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.ProjectiveLinearGroup
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.AvoidingLines
public import StacksCore.Tactic.StacksAttribute

/-!
# Moving a closed subvariety off another along a general line of projective transformations

Let `X, Y` be closed subvarieties of `𝐏(V)` which intersect properly, with `X ≠ 𝐏(V)` and
`X ∩ Y ≠ ∅`. A point `[g]` of the parameter space `𝐏 = 𝐏((End V)ᵛ)` is *bad* when some nonzero
representative `g` of its class violates `X ⊆ U(g)` or fails to make `r_g(X)` meet `Y` properly.
The class `[id_V]` of the identity is not bad: its representatives are the unit scalar multiples
of the identity, whose domain of definition is all of `𝐏(V)` and which fix every subset, so
badness at `[id_V]` would contradict the hypothesis on `X` and `Y`. Once the bad locus is known
to be a closed subvariety of codimension at least two, a general line through `[id_V]` misses it
and both clauses hold at every closed point of that line.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.ParameterModule`: the module `(End V)ᵛ` whose
  projective space is the parameter space `𝐏`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.endProjectionImage`: the image `r_g(S)` of a subset
  of `𝐏(V)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.IsGoodEndomorphism`: the two clauses, for a single
  endomorphism.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.identityParameterPoint`: the point `[id_V]` of `𝐏`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.badParameterLocus`: the bad locus `B ⊆ 𝐏`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.endProjection_eq_ι_comp_map`: for invertible `g`
  the morphism `r_g` is the inclusion of `U(g)` followed by the automorphism of `𝐏(V)`
  attached to `g`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.endProjectionImage_of_eq_smul_id`: a unit scalar
  multiple of the identity carries every subset of `𝐏(V)` to itself.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.identityParameterPoint_notMem_badParameterLocus`:
  `[id_V]` is not bad.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_line_isGood`:
  both clauses hold along a general line through `[id_V]`, once the bad locus is known to be an
  irreducible closed subset of codimension at least two.

## Implementation notes

**"For a general line".** The genericity of the source is read exactly as in
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_subset_union_lines_disjoint` (Tag
0B2T): there is a nonempty Zariski open subset `U` of the parameter space such that every closed
point `q ∈ U` lies, together with `[id_V]`, on a line `ℓ ⊆ 𝐏` along which both clauses hold.
A line is a `AlgebraicGeometry.ProjectiveSpaceOfModule.linearSubspace` cut out by a submodule of
corank two, as in that lemma. This is strictly stronger than the existence of one such line and
strictly weaker than the statement for every line, both of which the source's "for a general
line" excludes; the lines it produces sweep out a dense open subset of `𝐏`.

**The bad-locus bound is an input here.** The source proves the two clauses by showing that
the bad locus `B` is closed of dimension at most `dim 𝐏 - 2` and then quoting Tag 0B2T. This file
contains the first and the last of those steps — `[id_V] ∉ B`, which the source leaves to "by
assumption", is proved — and takes the bound on `B` as the hypotheses `hB` and `hcodim`. The bound
itself is proved downstream, from the incidence correspondence
`T = {(x, y, [g]) : x ∈ X, y ∈ Y, r_g(x) = y}` and the analysis of the determinant hypersurface
`𝐏 ∖ PGL(V)`, in
`…ProjectiveSpaceOfModule.exists_isClosed_two_le_codimension_badParameterLocus_subset` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionDominant`, as a closed superset
of the bad locus that need not be irreducible; Tag 0B1S itself is
`…ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_line_subset_endDomain_intersectProperly`
of `StacksFrontier.AlgebraicGeometry.Intersection.Projections.GeneralLineIntersectProperly`.

**Clause (2).** `AlgebraicGeometry.IntersectProperly` (Tag 0AZQ) is a predicate on irreducible
closed subsets, and `r_g(X)` is one — the image of the proper `X` under a morphism over the
ground field — but its closedness and irreducibility,
`AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_endProjectionImage` and
`AlgebraicGeometry.ProjectiveSpaceOfModule.isIrreducible_endProjectionImage`, are proved downstream
of this file. So clause (2) is spelled here as the dimension criterion that defines
`IntersectProperly`, read on the image set;
`AlgebraicGeometry.ProjectiveSpaceOfModule.isGoodEndomorphism_iff_intersectProperly` checks that
the two agree whenever the image is the underlying set of a closed subvariety.

**Representatives.** Goodness is a property of an endomorphism, and the bad locus collects the
points of `𝐏` having a bad representative; the conclusion therefore asserts the clauses for
*every* representative of a point of the line. That `U(g)` and `r_g` depend only on the class
`[g]` is `AlgebraicGeometry.ProjectiveSpaceOfModule.endDomain_smul` and
`AlgebraicGeometry.ProjectiveSpaceOfModule.endProjection_smul_apply`, the latter on closed
points; quantifying over representatives avoids relying on the missing global form.

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0B2T](https://stacks.math.columbia.edu/tag/0B2T)
* [Stacks Project, Tag 0B2U](https://stacks.math.columbia.edu/tag/0B2U)
* [Stacks Project, Tag 0B2W](https://stacks.math.columbia.edu/tag/0B2W)
* [Stacks Project, Tag 0AZQ](https://stacks.math.columbia.edu/tag/0AZQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- The module `(End V)ᵛ` whose projective space is the parameter space `𝐏` of the projective
transformations of `𝐏(V)`: its closed points are the classes of endomorphisms of `V`. -/
public abbrev ParameterModule : Type u := Module.Dual k (V →ₗ[k] V)

/-- The image `r_g(S)` of a subset `S` of `𝐏(V)` under the projective transformation attached to
an endomorphism `g` of `V`, formed inside the domain of definition `U(g)` and read in `𝐏(V)`. -/
public def endProjectionImage (g : V →ₗ[k] V) (S : Set (projectiveSpaceOfModule k V)) :
    Set (projectiveSpaceOfModule k V) :=
  (endProjection k V g).base '' ((endDomain k V g).ι.base ⁻¹' S)

/-- **`r_g` for an invertible `g`.** The projective transformation attached to an invertible
linear map is the inclusion of its domain of definition followed by the automorphism of `𝐏(V)`
that the map induces. -/
public theorem endProjection_eq_ι_comp_map (g : LinearMap.GeneralLinearGroup k V) :
    endProjection k V (g : V →ₗ[k] V) =
      (endDomain k V (g : V →ₗ[k] V)).ι ≫ map k V g := by
  have h := mapDomain_ι_comp_map k V g
  rw [projMapData_hom] at h
  exact h.symm

/-- The invertible linear map given by a unit scalar multiple of the identity. -/
private def unitsSmulId (c : kˣ) : LinearMap.GeneralLinearGroup k V :=
  Units.map (algebraMap k (Module.End k V)).toMonoidHom c

/-- The underlying linear map of `unitsSmulId` is the scalar multiple of the identity. -/
private theorem coe_unitsSmulId (c : kˣ) :
    (unitsSmulId k V c : V →ₗ[k] V) = (c : k) • LinearMap.id := rfl

/-- The domain of definition of a unit scalar multiple of the identity is all of `𝐏(V)`. -/
private theorem endDomain_eq_top_of_eq_smul_id {g : V →ₗ[k] V} {c : kˣ}
    (hg : g = (c : k) • LinearMap.id) : endDomain k V g = ⊤ := by
  rw [← coe_unitsSmulId k V c] at hg
  rw [hg]
  exact mapDomain_eq_top k V (unitsSmulId k V c)

/-- **A unit scalar multiple of the identity acts trivially on subsets.** Its domain of
definition is all of `𝐏(V)` and the morphism it induces is the identity, so it carries every
subset of `𝐏(V)` to itself. -/
public theorem endProjectionImage_of_eq_smul_id {g : V →ₗ[k] V} {c : kˣ}
    (hg : g = (c : k) • LinearMap.id) (S : Set (projectiveSpaceOfModule k V)) :
    endProjectionImage k V g S = S := by
  have hc : (unitsSmulId k V c : V →ₗ[k] V) = g := by rw [coe_unitsSmulId, hg]
  have htop := endDomain_eq_top_of_eq_smul_id k V hg
  have hmap : map k V (unitsSmulId k V c) = 𝟙 _ :=
    map_eq_id_of_eq_smul_id k V (unitsSmulId k V c) c (coe_unitsSmulId k V c)
  have hproj : endProjection k V g = (endDomain k V g).ι := by
    rw [← hc, endProjection_eq_ι_comp_map k V (unitsSmulId k V c), hmap, Category.comp_id]
  rw [endProjectionImage, hproj, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι, htop]
  simp

/-- **The two clauses, for a single endomorphism.** An endomorphism `g` of `V` is *good* for the
pair of subsets `X, Y` of `𝐏(V)` when `X ⊆ U(g)` and `r_g(X)` intersects `Y` properly, the
latter read as the dimension criterion that defines `AlgebraicGeometry.IntersectProperly`. -/
public def IsGoodEndomorphism (X Y : Set (projectiveSpaceOfModule k V)) (g : V →ₗ[k] V) : Prop :=
  X ⊆ (endDomain k V g : Set (projectiveSpaceOfModule k V)) ∧
    topologicalKrullDim ↥(endProjectionImage k V g X ∩ Y) +
        topologicalKrullDim (projectiveSpaceOfModule k V) ≤
      topologicalKrullDim ↥(endProjectionImage k V g X) + topologicalKrullDim ↥Y

/-- **Clause (2) is proper intersection.** When the image `r_g(X)` is the underlying set of a
closed subvariety `W` of `𝐏(V)`, goodness of `g` is exactly `X ⊆ U(g)` together with
`AlgebraicGeometry.IntersectProperly W Y`. -/
public theorem isGoodEndomorphism_iff_intersectProperly
    (X : Set (projectiveSpaceOfModule k V))
    (Y W : IrreducibleCloseds (projectiveSpaceOfModule k V)) (g : V →ₗ[k] V)
    (hW : (W : Set (projectiveSpaceOfModule k V)) = endProjectionImage k V g X) :
    IsGoodEndomorphism k V X (Y : Set (projectiveSpaceOfModule k V)) g ↔
      X ⊆ (endDomain k V g : Set (projectiveSpaceOfModule k V)) ∧ IntersectProperly W Y := by
  unfold IsGoodEndomorphism IntersectProperly
  rw [← hW]

/-- The identity of a nontrivial vector space is a nonzero linear map. -/
public theorem linearMapId_ne_zero [Nontrivial V] : (LinearMap.id : V →ₗ[k] V) ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  intro h
  exact hv (by simpa using LinearMap.congr_fun h v)

variable [IsAlgClosed k] [FiniteDimensional k V]

/-- An endomorphism of `V` **represents** a closed point `p` of the parameter space `𝐏` when it
is nonzero and its projective class is the class of endomorphisms that `p` names. -/
public def RepresentsParameterPoint (p : ClosedPoints k (ParameterModule k V))
    (g : V →ₗ[k] V) : Prop :=
  ∃ hg : g ≠ 0, dualEndClosedPointsEquiv k V p = Projectivization.mk k g hg

/-- The point `[id_V]` of the parameter space `𝐏`: the closed point naming the class of the
identity endomorphism of `V`. -/
public def identityParameterPoint [Nontrivial V] :
    projectiveSpaceOfModule k (ParameterModule k V) :=
  ((dualEndClosedPointsEquiv k V).symm
    (Projectivization.mk k (LinearMap.id : V →ₗ[k] V) (linearMapId_ne_zero k V))).val

/-- `[id_V]` is a closed point of the parameter space. -/
public theorem isClosed_identityParameterPoint [Nontrivial V] :
    IsClosed ({identityParameterPoint k V} :
      Set (projectiveSpaceOfModule k (ParameterModule k V))) :=
  ((dualEndClosedPointsEquiv k V).symm _).property

/-- **The bad locus `B ⊆ 𝐏`:** the set of points of the parameter space having a representative
endomorphism that violates one of the two clauses for the pair `X, Y`. -/
public def badParameterLocus (X Y : Set (projectiveSpaceOfModule k V)) :
    Set (projectiveSpaceOfModule k (ParameterModule k V)) :=
  {q | ∃ (p : ClosedPoints k (ParameterModule k V)) (g : V →ₗ[k] V),
    (p : projectiveSpaceOfModule k (ParameterModule k V)) = q ∧
      RepresentsParameterPoint k V p g ∧ ¬ IsGoodEndomorphism k V X Y g}

/-- Off the bad locus every representative is good. -/
public theorem isGoodEndomorphism_of_notMem_badParameterLocus
    {X Y : Set (projectiveSpaceOfModule k V)} {p : ClosedPoints k (ParameterModule k V)}
    (hp : (p : projectiveSpaceOfModule k (ParameterModule k V)) ∉ badParameterLocus k V X Y)
    {g : V →ₗ[k] V} (hg : RepresentsParameterPoint k V p g) :
    IsGoodEndomorphism k V X Y g := by
  by_contra h
  exact hp ⟨p, g, rfl, hg, h⟩

/-- **`[id_V]` is not bad.** Every representative of the class of the identity is a unit scalar
multiple of the identity, whose domain of definition is all of `𝐏(V)` and which carries `X` to
itself; so both clauses at `[id_V]` reduce to the hypothesis that `X` and `Y` intersect
properly. This is the step the source leaves to "by assumption". -/
public theorem identityParameterPoint_notMem_badParameterLocus [Nontrivial V]
    {X Y : IrreducibleCloseds (projectiveSpaceOfModule k V)} (hXY : IntersectProperly X Y) :
    identityParameterPoint k V ∉
      badParameterLocus k V (X : Set (projectiveSpaceOfModule k V))
        (Y : Set (projectiveSpaceOfModule k V)) := by
  rintro ⟨p, g, hpq, ⟨hg0, hgeq⟩, hbad⟩
  have hp : p = (dualEndClosedPointsEquiv k V).symm
      (Projectivization.mk k (LinearMap.id : V →ₗ[k] V) (linearMapId_ne_zero k V)) :=
    Subtype.ext hpq
  have hmk : Projectivization.mk k g hg0 =
      Projectivization.mk k (LinearMap.id : V →ₗ[k] V) (linearMapId_ne_zero k V) := by
    rw [← hgeq, hp, Equiv.apply_symm_apply]
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff k g (LinearMap.id : V →ₗ[k] V) hg0
    (linearMapId_ne_zero k V)).mp hmk
  have hgc : g = (c : k) • LinearMap.id := by
    rw [← hc, Units.smul_def]
  refine hbad ⟨?_, ?_⟩
  · rw [endDomain_eq_top_of_eq_smul_id k V hgc]
    simp
  · rw [endProjectionImage_of_eq_smul_id k V hgc]
    exact hXY

/-- **The genericity step of Tag 0B1S, for an irreducible bad locus.** With `X, Y` closed
subvarieties of `𝐏(V)` which intersect properly, if the bad locus in the parameter space
`𝐏 = 𝐏((End V)ᵛ)` is an irreducible closed subset `B` of codimension at least two, then for the
line through `[id_V]` and any closed point of a nonempty Zariski open subset of `𝐏`, every
representative `g` of every closed point of that line is good.

This is the last step of the source's proof (Tag 0B2T applied to `B`), with the bound on `B`
supplied by the caller. Tag 0B1S itself, with no hypothesis on the bad locus, is
`…ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_line_subset_endDomain_intersectProperly`
of `StacksFrontier.AlgebraicGeometry.Intersection.Projections.GeneralLineIntersectProperly`. The
hypotheses `X ≠ 𝐏(V)` and `X ∩ Y ≠ ∅` are not used here. -/
public theorem exists_isOpen_forall_closedPoint_line_isGood [Nontrivial V]
    (X Y : IrreducibleCloseds (projectiveSpaceOfModule k V)) (hXY : IntersectProperly X Y)
    (_hXne : (X : Set (projectiveSpaceOfModule k V)) ≠ Set.univ)
    (_hXYne : ((X : Set (projectiveSpaceOfModule k V)) ∩
      (Y : Set (projectiveSpaceOfModule k V))).Nonempty)
    (B : IrreducibleCloseds (projectiveSpaceOfModule k (ParameterModule k V)))
    (hB : (B : Set (projectiveSpaceOfModule k (ParameterModule k V))) =
      badParameterLocus k V (X : Set (projectiveSpaceOfModule k V))
        (Y : Set (projectiveSpaceOfModule k V)))
    (hcodim : (2 : ℕ∞) ≤ codimension B) :
    ∃ U : Set (projectiveSpaceOfModule k (ParameterModule k V)), IsOpen U ∧ U.Nonempty ∧
      ∀ q ∈ U, IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V))) →
        ∃ L : Submodule k (ParameterModule k V),
          Module.finrank k (ParameterModule k V ⧸ L) = 2 ∧
          identityParameterPoint k V ∈ linearSubspace k (ParameterModule k V) L ∧
          q ∈ linearSubspace k (ParameterModule k V) L ∧
          ∀ p : ClosedPoints k (ParameterModule k V),
            (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
              linearSubspace k (ParameterModule k V) L →
            ∀ g : V →ₗ[k] V, RepresentsParameterPoint k V p g →
              IsGoodEndomorphism k V (X : Set (projectiveSpaceOfModule k V))
                (Y : Set (projectiveSpaceOfModule k V)) g := by
  have hnt : Nontrivial (ParameterModule k V) := by
    refine Module.nontrivial_of_finrank_pos (R := k) ?_
    rw [Subspace.dual_finrank_eq, Module.finrank_linearMap]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos
  have hid : identityParameterPoint k V ∉
      (B : Set (projectiveSpaceOfModule k (ParameterModule k V))) := by
    rw [hB]
    exact identityParameterPoint_notMem_badParameterLocus k V hXY
  obtain ⟨U, hUopen, hUne, hU⟩ :=
    exists_isOpen_subset_union_lines_disjoint k (ParameterModule k V) B hcodim
      (identityParameterPoint k V) (isClosed_identityParameterPoint k V) hid
  refine ⟨U, hUopen, hUne, fun q hq hqc => ?_⟩
  obtain ⟨L, hL2, hidL, hqL, hdisj⟩ := hU q hq hqc
  refine ⟨L, hL2, hidL, hqL, fun p hpL g hg => ?_⟩
  refine isGoodEndomorphism_of_notMem_badParameterLocus k V ?_ hg
  rw [← hB]
  exact Set.disjoint_left.mp hdisj hpL

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
