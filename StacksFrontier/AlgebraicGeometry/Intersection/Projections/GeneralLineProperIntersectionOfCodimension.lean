module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.GeneralLineProperIntersection
import all StacksFrontier.AlgebraicGeometry.Intersection.Projections.GeneralLineProperIntersection
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.AvoidingLinesOfClosedSubset

/-!
# A general line of projective transformations, for a bad locus of codimension two

Let `X, Y` be closed subvarieties of `𝐏(V)` with `X ≠ 𝐏(V)`, and let `B` be a closed subset of
the parameter space `𝐏 = 𝐏((End V)ᵛ)` which contains every bad closed point
(`AlgebraicGeometry.ProjectiveSpaceOfModule.badParameterLocus` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.GeneralLineProperIntersection`), avoids
`[id_V]` and has codimension at least two at each of its points. Then for a general line
`ℓ ⊆ 𝐏` through `[id_V]` every representative `g` of every closed point of `ℓ` satisfies
`X ⊆ U(g)` and makes `r_g(X)` intersect `Y` properly.

## Main results

* `…ProjectiveSpaceOfModule.irreducibleSpace_projectiveSpaceOfModule_of_finrank_eq`:
  the projective space of a vector space of dimension `n + 1` is irreducible.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_closedPoint_line_isGood_of_codimension`:
  both clauses hold along a general line through `[id_V]`.

## Implementation notes

## Implementation notes

**"For a general line".** The genericity of the source is read exactly as in
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_subset_union_lines_disjoint` (Tag
0B2T): there is a nonempty Zariski open subset `U` of the parameter space such that every closed
point `q ∈ U` lies, together with `[id_V]`, on a line `ℓ ⊆ 𝐏` along which both clauses hold.
A line is a `AlgebraicGeometry.ProjectiveSpaceOfModule.linearSubspace` cut out by a submodule of
corank two, as in that lemma. This is strictly stronger than the existence of one such line and
strictly weaker than the statement for every line, both of which the source's "for a general
line" excludes; the lines it produces sweep out a dense open subset of `𝐏`.

**What is carried here.** The source proves the two clauses by showing that the bad locus is
contained in a closed subset `B` of dimension at most `dim 𝐏 - 2` avoiding `[id_V]` and then
quoting Tag 0B2T. The closedness, the containment, the dimension bound and `[id_V] ∉ B` are the
hypotheses `hBc`, `hB`, `hcodim` and `hBid` of the statement below: everything the source's
proof does between its first and last steps, namely the incidence variety
`T = {(x, y, [g]) : x ∈ X, y ∈ Y, r_g(x) = y}` over `X × Y` and the analysis of the determinant
hypersurface `𝐏 ∖ PGL(V)`. Those hypotheses are *discharged* in
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_line_isGood` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionDominant`, which is where Tag
0B1S is registered; the statement below is the step of the argument that is independent of how
the bad locus is produced. The source leaves `[id_V] ∉ B` to "by assumption"; it is a hypothesis
here because `B` is only a superset of the bad locus, so goodness at `[id_V]` no longer forces
it. `AlgebraicGeometry.ProjectiveSpaceOfModule.identityParameterPoint_notMem_badParameterLocus`
is what discharges it at each use.

The clause-(1) half of `hB` and `hcodim` — the locus where `X` leaves `U(g)` — is *not* carried
either, in
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_closedPoint_line_isGood_of_clauseTwo`
of `StacksFrontier.AlgebraicGeometry.Intersection.Projections.BadLocusCodimension`, which has the
same conclusion as the statement below and carries only the clause-(2) half. The incidence
variety is not needed for the clause-(1) half: the adjugate of the matrix of a corank-one
endomorphism names its omitted point by forms of degree `dim V - 1`, so substituting that into a
form cutting out `X` already produces the closed subset the genericity of Tag 0B2T consumes.

`badParameterLocus` is a set of *closed* points of `𝐏`, badness being a property of an
endomorphism and the closed points of `𝐏` being the classes of endomorphisms. Asking for that
set itself to be closed would therefore be asking for much more than the source does: a closed
subset of a scheme is the closure of its closed points, and an irreducible closed subset with
two points has a non-closed generic point, so a closed set of closed points in a Noetherian
scheme is finite. The hypothesis is accordingly that `B` is a closed subset *containing* every
bad closed point, that is that `B` contains the Zariski closure of the bad locus.

**`B` is not asked to be irreducible.** Tag 0B2T is about an irreducible closed subset of
codimension at least two, which is what its source statement is about, so asking `B` to be
irreducible would be the direct way to quote it. That extra strength is not harmless: for
a pair of distinct lines of `𝐏²` no irreducible closed `B` whose closed points are exactly the
bad ones has codimension at least two — indeed none exists at all — so a statement carrying that
hypothesis is vacuous there. This is
`AlgebraicGeometry.ProjectiveSpaceOfModule.not_exists_irreducible_badParameterLocus` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.BadLocusReducible`. For `X` and `Y` the
lines cut out by two independent vectors `a` and `b` of a three-dimensional `V` — which intersect
properly, in a point, with `X ≠ 𝐏²` and `X ∩ Y ≠ ∅` — the classes of the endomorphisms `g` with
`g b ∈ k·a` form a *linear* subspace of the parameter space, of codimension two, every closed
point of which is bad: either `X` leaves `U(g)`, or else `r_g(X)` lies inside the line `Y` and
clause (2) fails outright. The class of the rank-one endomorphism `u ↦ ψ(u)·b` with `ψ b = 1` is
bad as well, clause (1) failing at it, and it does not lie on that subspace. An irreducible
closed `B` whose closed points were exactly the bad ones would contain the subspace — the closed
points of a linear subspace are dense in it — and would contain that extra class, hence would
contain the subspace *strictly*; strict inclusion of irreducible closed subsets raises the
codimension, so the subspace would have codimension at least three, against its dimension `6` in
a parameter space of dimension `8`.

The hypothesis carried below is accordingly the pointwise one, `hcodim`, which asks the
codimension bound of the closure of each point of a *closed* `B`:
`∀ x ∈ B, 2 ≤ codimension (closureSingleton x)`. That is what the form of Tag 0B2T for a
reducible closed subset,
`exists_isOpen_subset_union_lines_disjoint_of_forall_codimension_ge_two` of
`StacksFrontier.AlgebraicGeometry.Variety.Projective.AvoidingLines`, consumes, no decomposition
into irreducible components being needed. It is what the clause-(1) half of the bad locus is
produced in:
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isClosed_two_le_codimension_notMem_endDomain`
of `StacksFrontier.AlgebraicGeometry.Intersection.Projections.BadLocusCodimension` bounds the
codimension of the locus where `X` leaves `U(g)` pointwise, and not of an irreducible closure
of it.

**Clause (2).** `AlgebraicGeometry.IntersectProperly` (Tag 0AZQ) is a predicate on irreducible
closed subsets, and `r_g(X)` is one — the image of the proper `X` under a morphism over the
ground field — but the library has closedness of such an image only for the linear projection,
as `AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_image_projection`, and not for `r_g`. So
clause (2) is spelled as the dimension criterion that defines `IntersectProperly`, read on the
image set; `AlgebraicGeometry.ProjectiveSpaceOfModule.isGoodEndomorphism_iff_intersectProperly`
checks that the two agree whenever the image is the underlying set of a closed subvariety.

**Representatives.** Goodness is a property of an endomorphism, and the bad locus collects the
points of `𝐏` having a bad representative; the conclusion therefore asserts the clauses for
*every* representative of a point of the line. That `U(g)` and `r_g` depend only on the class
`[g]` is `AlgebraicGeometry.ProjectiveSpaceOfModule.endDomain_smul` and
`AlgebraicGeometry.ProjectiveSpaceOfModule.endProjection_smul_apply`, the latter on closed
points; quantifying over representatives avoids relying on the missing global form.

The hypotheses `X ∩ Y ≠ ∅` and `IntersectProperly X Y` of the source are recorded and not used:
they enter only the steps that `hB`, `hBid` and `hcodim` stand for — the second of them being
exactly what makes `[id_V]` good, hence what discharges `hBid`. `X ≠ 𝐏(V)` is used, but not for
what the source uses it for: it rules out `dim V = 1`, in which `𝐏(V)` is a point and no line
exists at all.

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0B2T](https://stacks.math.columbia.edu/tag/0B2T)
* [Stacks Project, Tag 0AZQ](https://stacks.math.columbia.edu/tag/0AZQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- **The projective space of a vector space of dimension `n + 1` is irreducible.** A basis
indexed by `Fin (n + 1)` identifies `𝐏(V)` with `Proj k[T₀, …, Tₙ]`, which is irreducible
because its standard opens are irreducible and all contain the zero ideal. Stated from the
dimension rather than from a basis, which is the form every caller in this tree has: each of
them has `dim_k V = n + 1` and builds the basis only to feed it in. -/
public theorem irreducibleSpace_projectiveSpaceOfModule_of_finrank_eq {n : ℕ}
    [FiniteDimensional k V] (hV : Module.finrank k V = n + 1) :
    IrreducibleSpace (projectiveSpaceOfModule k V) :=
  (projectiveSpaceOfModuleIsoProjMvPolynomial
    (Module.finBasisOfFinrankEq k V hV)).hom.homeomorph.irreducibleSpace_iff.mpr inferInstance


variable [IsAlgClosed k] [FiniteDimensional k V]

omit [IsAlgClosed k] in
/-- **An irreducible closed subset of `𝐏(V)` other than all of it forces `dim V ≥ 2`.** Were `V`
a line, `𝐏(V)` would be irreducible of dimension `0`, so such a subset would sit strictly below
the whole space and give a chain of length one. The same bound for an arbitrary nonempty proper
closed subset, read off the closed points of `𝐏(V)` instead, is
`AlgebraicGeometry.ProjectiveSpaceOfModule.two_le_finrank_of_isClosed_ne_univ`, which is not
available here: the closed point it needs inside the subset comes from a module downstream of
this one. -/
private theorem two_le_finrank_of_ne_univ [Nontrivial V]
    (X : IrreducibleCloseds (projectiveSpaceOfModule k V))
    (hXne : (X : Set (projectiveSpaceOfModule k V)) ≠ Set.univ) :
    2 ≤ Module.finrank k V := by
  by_contra hlt
  have h1 : Module.finrank k V = 0 + 1 := by
    have := Module.finrank_pos (R := k) (M := V)
    omega
  have hirr : IrreducibleSpace (projectiveSpaceOfModule k V) :=
    irreducibleSpace_projectiveSpaceOfModule_of_finrank_eq k V h1
  set T : IrreducibleCloseds (projectiveSpaceOfModule k V) :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩
  have hXT : X < T :=
    lt_of_le_of_ne (fun x _ => Set.mem_univ x)
      fun h => hXne (congrArg IrreducibleCloseds.carrier h)
  have hchain : ∃ l : LTSeries (IrreducibleCloseds (projectiveSpaceOfModule k V)),
      l.length = 1 := ⟨(RelSeries.singleton _ X).snoc T hXT, rfl⟩
  have hle : ((1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim (projectiveSpaceOfModule k V) :=
    Order.le_krullDim_iff.2 hchain
  rw [topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq h1] at hle
  exact absurd hle (by decide)

omit [IsAlgClosed k] in
/-- **`dim V ≥ 2` forces `dim (End V)ᵛ ≥ 3`**, the parameter space having dimension
`(dim V)² - 1`. This is what the form of Tag 0B2T for a reducible closed subset asks of the
ambient space. -/
private theorem three_le_finrank_parameterModule (h2 : 2 ≤ Module.finrank k V) :
    3 ≤ Module.finrank k (ParameterModule k V) := by
  have hfr : Module.finrank k (ParameterModule k V) =
      Module.finrank k V * Module.finrank k V := by
    rw [Subspace.dual_finrank_eq, Module.finrank_linearMap]
  rw [hfr]
  calc (3 : ℕ) ≤ 2 * 2 := by norm_num
    _ ≤ _ := Nat.mul_le_mul h2 h2

/-- **Stacks Project, Tag 0B1S.** With `X, Y` closed subvarieties of `𝐏(V)` which intersect
properly, `X ≠ 𝐏(V)` and `X ∩ Y ≠ ∅`, suppose the bad locus in the parameter space
`𝐏 = 𝐏((End V)ᵛ)` is *contained in* a closed subset `B` of `𝐏` which has codimension at least
two at each of its points and does not contain `[id_V]`. Then for a general line `ℓ ⊆ 𝐏` through
`[id_V]` — that is, for a line through `[id_V]` and any closed point of a nonempty Zariski open
subset of `𝐏` — every representative `g` of every closed point of `ℓ` satisfies `X ⊆ U(g)` and
makes `r_g(X)` intersect `Y` properly.

Containment and not equality, together with `[id_V] ∉ B`: that is all the genericity argument
uses, and it is what the clause-(1) and clause-(2) loci of
`…ProjectiveSpaceOfModule.exists_isClosed_two_le_codimension_badParameterLocus_subset`
supply — their union is a superset of the bad locus, the codimension bound being available only
there. With the equality `[id_V] ∉ B` would follow from `[id_V]` being closed and good, so the
hypothesis is stated separately; the proper intersection of `X` and `Y`, which is what makes
`[id_V]` good, is accordingly recorded and not used.

`B` is *not* asked to be irreducible: that strengthening is unsatisfiable for some admissible
pairs, by
`AlgebraicGeometry.ProjectiveSpaceOfModule.not_exists_irreducible_badParameterLocus`. -/
@[stacks 0B1S "both clauses (1) X ⊆ U(g) and (2) g(X) intersects Y properly, along a general \
line through [id_V], in the form that assumes a bound on the bad locus: 'general' is read as in \
Tag 0B2T, namely that there is a nonempty Zariski open subset of the parameter space \
𝐏 = 𝐏((End V)ᵛ) each of whose closed points lies with [id_V] on such a line, and clause (2) \
is the dimension criterion defining Tag 0AZQ read on the image set r_g(X), which agrees with \
IntersectProperly whenever that image is the underlying set of a closed subvariety. The \
bad-locus bound is discharged, and the tag registered for both clauses at the source's own \
hypotheses alone, by \
AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_line_isGood of \
StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionDominant; this form keeps its \
place here, upstream of the incidence-correspondence construction that the discharge needs"]
public theorem exists_isOpen_closedPoint_line_isGood_of_codimension [Nontrivial V]
    (X Y : IrreducibleCloseds (projectiveSpaceOfModule k V)) (_hXY : IntersectProperly X Y)
    (hXne : (X : Set (projectiveSpaceOfModule k V)) ≠ Set.univ)
    (_hXYne : ((X : Set (projectiveSpaceOfModule k V)) ∩
      (Y : Set (projectiveSpaceOfModule k V))).Nonempty)
    (B : Set (projectiveSpaceOfModule k (ParameterModule k V))) (hBc : IsClosed B)
    (hB : ∀ p : ClosedPoints k (ParameterModule k V),
      (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
          badParameterLocus k V (X : Set (projectiveSpaceOfModule k V))
            (Y : Set (projectiveSpaceOfModule k V)) →
        (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈ B)
    (hBid : identityParameterPoint k V ∉ B)
    (hcodim : ∀ x ∈ B, (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x)) :
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
  have h3 := three_le_finrank_parameterModule k V (two_le_finrank_of_ne_univ k V X hXne)
  have hnt : Nontrivial (ParameterModule k V) :=
    Module.nontrivial_of_finrank_pos (R := k) (by omega)
  obtain ⟨U, hUopen, hUne, hU⟩ :=
    exists_isOpen_subset_union_lines_disjoint_of_forall_codimension_ge_two k
      (ParameterModule k V) h3 B hBc hcodim (identityParameterPoint k V)
      (isClosed_identityParameterPoint k V) hBid
  refine ⟨U, hUopen, hUne, fun q hq hqc => ?_⟩
  obtain ⟨L, hL2, hidL, hqL, hdisj⟩ := hU q hq hqc
  refine ⟨L, hL2, hidL, hqL, fun p hpL g hg => ?_⟩
  refine isGoodEndomorphism_of_notMem_badParameterLocus k V ?_ hg
  intro hbad
  exact Set.disjoint_left.mp hdisj hpL (hB p hbad)

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
