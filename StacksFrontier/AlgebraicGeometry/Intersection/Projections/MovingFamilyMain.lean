module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.GeneralLineProperIntersectionOfCodimension
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.GeneralTranslateProper
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.LineThroughIdentityDomain
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyIrreducibleFamily
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyProper
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingLemmaOfCodimension
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionDominant
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.AvoidingLinesOfClosedSubset

/-!
# The Moving Lemma: the family `C'` over a general line of the parameter space

Let `C, X` be closed subvarieties of `𝐏(V)` which intersect properly, with `C ≠ 𝐏(V)`, and let
`T i ⊆ X` be a finite collection of closed subvarieties. There is a family

`C' ⊆ ℓ ×_k 𝐏(V)`

over a line `ℓ ⊆ 𝐏((End V)ᵛ)` through `[id_V]` satisfying the four clauses of the source:

1. `C'` is dominant over `ℓ`;
2. its fibre over `0 = [id_V]` is `C`;
3. it meets the constant family `X × ℓ` properly;
4. its fibre over `∞` meets each `T i` properly.

As in the source there are two constructions, chosen by whether `C` meets `X`. When `C ∩ X = ∅`
nothing is moved and `C'` is the constant family `C × ℓ`
(`AlgebraicGeometry.ProjectiveSpaceOfModule.constantFamily`): each of its fibres is `C`, and
clauses (3) and (4) hold because the intersections in question are empty. When `C` meets `X`,
`ℓ` is a general line and `C'` is the family whose fibre over a point `[g]` of `ℓ` is the
translate `r_g(C)` — constructed in
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilySet` as the image, under the
proper projection forgetting the source point, of the part of the graph of the family of
projective transformations lying over `C`.

## Main results

* `…ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_line_moving_of_intersectProperly`:
  the general-position step, read on the fibres: the four clauses for the translates `r_g(C)`, at
  the hypotheses of Tag 0B1S.
* `…ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_movingFamily_of_inter_eq_empty`:
  the four clauses for the constant family, when `C ∩ X = ∅`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_movingFamily`:
  **the four clauses about the family `C'` over a general line of `𝐏`**, the two constructions
  combined, for a closed `X` and with clause (2) read on sets; it costs the hypothesis
  `C ≠ 𝐏(V)`, its base being a line of `𝐏`. Tag 0B1T itself — `X` not necessarily closed,
  clause (2) scheme theoretically, base an abstract `𝐏^1` — is
  `…ProjectiveSpaceOfModule.exists_movingFamily_of_subvariety_fixed` of
  `StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingLemmaFixedPoints`.

## Implementation notes

The line is the scheme `AlgebraicGeometry.ProjectiveSpaceOfModule.movingLine`, the projective
space of the corank-two quotient `(End V)ᵛ ⧸ L`, embedded in the parameter space by
`AlgebraicGeometry.ProjectiveSpaceOfModule.movingLineι` with image the linear subspace cut out by
`L`; the two distinguished points `0` and `∞` are the points of that scheme lying over
`[id_V]` and over the chosen general point `q`.

A fibre is the preimage under the section
`AlgebraicGeometry.ProjectiveSpaceOfModule.lineSection` at a closed point of the line, which is
the fibre of the projection over that point
(`AlgebraicGeometry.ProjectiveSpaceOfModule.range_lineSection`). For the general-position
construction clauses (2) and (4) are instances of one identity, `σ_λ⁻¹(C') = r_g(C)`, proved in
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyFibre`; for the constant
family all four read off the single identity `σ_λ⁻¹(C × ℓ) = C` of
`AlgebraicGeometry.ProjectiveSpaceOfModule.movingFibre_constantFamily`.

Closed subvarieties are `TopologicalSpace.IrreducibleCloseds`, the project's convention; the
constant family `X × ℓ` and the fibre over `∞` are produced as such, so that
`AlgebraicGeometry.IntersectProperly` applies to them on the nose.

**Clause (2) scheme theoretically.** The clause (2) in the statements here is the equality of the
fibre of `C'` over `0` with `C` as *subsets* of `𝐏(V)`; the source asks for it scheme
theoretically, and
`AlgebraicGeometry.Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme` together with
`AlgebraicGeometry.Scheme.IdealSheafData.support_comap` turns that into the subset equality plus
the reducedness of the scheme-theoretic fibre `(vanishingIdeal C').comap (lineSection … 0)`.

For the constant family that reducedness holds and the scheme-theoretic clause is proved:
`AlgebraicGeometry.ProjectiveSpaceOfModule.comap_vanishingIdeal_lineProductConstant` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyConstantScheme`, the
scheme-theoretic fibre of `X × 𝐏(W)` over every closed point of `𝐏(W)` being the reduced closed
subscheme on `X`, because the reduced structure on the constant family is the preimage of the
reduced structure on `X` — the product `𝐏(W) ×_k X` is a variety over an algebraically closed
field, by Tag 0AZM, hence reduced — and `lineSection` is a section of the projection to `𝐏(V)`,
so the two pullbacks of ideal sheaves compose to the identity.

For the *general-position* family the reducedness holds because the family is an isomorphism
over a neighbourhood of `0 = [id_V]`; that is
`AlgebraicGeometry.ProjectiveSpaceOfModule.comap_vanishingIdeal_lineProductSection_of_translate`
of `StacksFrontier.AlgebraicGeometry.Intersection.Projections.LocalTranslationFamily`, applied in
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingLemmaFixedPoints`.

**The source's own hypotheses, and the one beyond them.** Both families of hypotheses of
`…ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_line_moving_of_codimension` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingLemma` are discharged here, once,
in `…ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_line_moving_of_intersectProperly`.
Nothing about the family `C'` itself is assumed either, and `C ∩ X ≠ ∅` is assumed only by that
general-position step, the family statement splitting into cases instead. `X` is a *closed*
subvariety, which is what the source's "subvariety" means in this chapter: Definition 0AZQ
defines proper intersection for closed subvarieties only, so both the hypothesis and clause (3)
read that way; the chapter itself introduces `W ⊂ X` as "a subvariety" and then calls that same
`W` a closed subvariety; and 0B1T's proof applies Lemma 0B1S, whose subvarieties are closed. The
one hypothesis beyond the source's is `C ≠ 𝐏(V)`, which the *shape of the conclusion* forces
rather than the proof: the line is asked for inside `𝐏 = 𝐏((End V)ᵛ)`, of dimension
`(dim V)^2 - 1`, so at `dim V = 1` there is no line to be had, while `𝐏(V)` is then a single
point whose only closed subvariety is `𝐏(V)` itself.

**The first family**, about the bad locus of `(C, X)`, asks for a closed subset `B ⊆ 𝐏`
containing every bad closed point, having codimension at least two at each of its points and
missing `[id_V]`; it is discharged by
`…ProjectiveSpaceOfModule.exists_isClosed_two_le_codimension_badParameterLocus_subset` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionDominant`, the step of Tag
0B1S's proof which bounds the codimension of the bad locus, applied to the very pair `(C, X)`.
That `B` is a *superset* of the bad locus and not the bad locus itself — its clause-(1) piece
being the adjugate-substitution locus together with the leading-minor locus, which is where the
codimension bound lives — is why the upstream hypothesis is the containment `bad ⊆ B` rather
than an equality on closed points, and why `[id_V] ∉ B` is asked separately instead of being
read off from `[id_V]` being good. `B` is *not* asked to be irreducible: an irreducible `B` of
codimension at least two does not exist for `C` and `X` two distinct lines of `𝐏²`, by
`AlgebraicGeometry.ProjectiveSpaceOfModule.not_exists_irreducible_badParameterLocus` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.BadLocusReducible`, so the pointwise
bound `∀ x ∈ B, 2 ≤ codimension (closureSingleton x)` is what replaces `2 ≤ codimension B`; see
the implementation notes of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.GeneralLineProperIntersection`.

**The second family** asks, for each `i`, for a proper closed subset of `𝐏` containing the bad
locus of `(C, T i)` —
the source's "a general point `∞ = [g] ∈ ℓ` is a general point of `𝐏` and for such a point
`r_g(C) ∩ T` is proper for any closed subvariety `T` of `𝐏(V)`". `MovingLemma` cannot discharge
either family, being upstream of the whole incidence-correspondence construction, but this one
can:
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_nonempty_disjoint_badParameterLocus` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.GeneralTranslateProper` produces, for
*any* two closed subvarieties and with no hypothesis relating them, a nonempty open subset of `𝐏`
missing the bad locus, and the complement of that open subset is the proper closed subset wanted.
Only codimension one is needed of the bad locus of `(C, T i)`, the single point `∞` having to
avoid it rather than a whole line; Tag 0B1S, which gives codimension two, is *not* applicable to
those pairs, its argument using that the pair already intersects properly — which `C` a line, `X`
a plane and `T i` a point of `𝐏³` violates. The intersection `C ∩ T i` is allowed to be empty.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0B2T](https://stacks.math.columbia.edu/tag/0B2T)
* [Stacks Project, Tag 0B2W](https://stacks.math.columbia.edu/tag/0B2W)
* [Stacks Project, Tag 0AZQ](https://stacks.math.columbia.edu/tag/0AZQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

/-- **Disjoint closed subvarieties intersect properly.** Their intersection is empty, so its
dimension is `⊥`, and `⊥` absorbs the ambient dimension on the left of the criterion of Tag
0AZQ. -/
public theorem _root_.AlgebraicGeometry.intersectProperly_of_inter_eq_empty {Y : Scheme.{u}}
    (W Z : IrreducibleCloseds Y) (h : (W : Set Y) ∩ (Z : Set Y) = ∅) :
    IntersectProperly W Z := by
  have hbot : topologicalKrullDim ↥((W : Set Y) ∩ (Z : Set Y)) = ⊥ :=
    (topologicalKrullDim_eq_bot_iff_isEmpty _).mpr (Set.isEmpty_coe_sort.mpr h)
  rw [intersectProperly_iff, hbot, WithBot.bot_add]
  exact bot_le

variable (k V : Type u) [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [Nontrivial V]

omit [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V] in
/-- A point of the parameter space lying on the line comes from a point of the line, and that
point is closed when the given one is. -/
public theorem exists_movingLine_point (L : Submodule k (ParameterModule k V))
    {p : projectiveSpaceOfModule k (ParameterModule k V)}
    (hp : p ∈ linearSubspace k (ParameterModule k V) L)
    (hpc : IsClosed ({p} : Set (projectiveSpaceOfModule k (ParameterModule k V)))) :
    ∃ (lam : movingLine k V L) (_ : IsClosed ({lam} : Set (movingLine k V L))),
      (movingLineι k V L).base lam = p := by
  obtain ⟨lam, hlam⟩ : p ∈ Set.range (movingLineι k V L).base := by
    rw [range_movingLineι]; exact hp
  refine ⟨lam, ?_, hlam⟩
  have hpre : (movingLineι k V L).base ⁻¹' {p} = {lam} := by
    refine Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)
    · rw [Set.mem_singleton_iff]
      refine (movingLineι k V L).isClosedEmbedding.injective ?_
      rw [hlam]
      exact hz
    · rw [Set.mem_singleton_iff] at hz
      rw [Set.mem_preimage, hz, hlam]
      rfl
  rw [← hpre]
  exact hpc.preimage (movingLineι k V L).continuous

omit [Nontrivial V] in
/-- A closed point of the line is a closed point of the parameter space lying on the line, and
the tautological endomorphism it names represents it. -/
public theorem exists_representsParameterPoint_of_movingLine
    (L : Submodule k (ParameterModule k V)) {mu : Module.Dual k (lineSpace k V L)}
    (hmu : mu ≠ 0) :
    ∃ p : ClosedPoints k (ParameterModule k V),
      (p : projectiveSpaceOfModule k (ParameterModule k V)) =
        (movingLineι k V L).base (linearFunctionalPoint k (lineSpace k V L) mu hmu) ∧
      (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
        linearSubspace k (ParameterModule k V) L ∧
      RepresentsParameterPoint k V p (lineEnd k V L mu) := by
  have hcl : IsClosed ({(movingLineι k V L).base
                          (linearFunctionalPoint k (lineSpace k V L) mu hmu)} :
        Set (projectiveSpaceOfModule k (ParameterModule k V))) := by
    have h := (movingLineι k V L).isClosedMap
      ({linearFunctionalPoint k (lineSpace k V L) mu hmu} : Set (movingLine k V L))
      (linearFunctionalPoint_isClosed k (lineSpace k V L) mu hmu)
    rwa [Set.image_singleton] at h
  refine ⟨⟨_, hcl⟩, rfl, ?_, representsParameterPoint_lineEnd k V L hmu ⟨_, hcl⟩ rfl⟩
  rw [← range_movingLineι k V L]
  exact Set.mem_range_self _

/-- **The general-position step of Tag 0B1T, read on the fibres.** Let `C, X` be closed
subvarieties of `𝐏(V)` which intersect properly, with `C ≠ 𝐏(V)` and `C ∩ X ≠ ∅`, and let
`T i ⊆ X` be a finite collection of closed subvarieties. Then for a general line `ℓ ⊆ 𝐏`
through `[id_V]` — that is, for the line through `[id_V]` and any closed point `∞` of a nonempty
Zariski open subset of `𝐏` — the family whose fibre over a point `[g]` of `ℓ` is the translate
`r_g(C)` has nonempty fibres; its fibre over `0 = [id_V]` is `C`; `r_g(C)` meets `X` properly at
every closed point of `ℓ`; and `r_g(C)` meets each `T i` properly at `∞`.

This is
`…ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_line_moving_of_codimension` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingLemma` with both of its families
of bad-locus hypotheses discharged, which that module cannot do and this one can; the
conclusions are identical. The first family is discharged by Tag 0B1S's own codimension bound
`…ProjectiveSpaceOfModule.exists_isClosed_two_le_codimension_badParameterLocus_subset`, applied
to the very pair `(C, X)`, and the second by
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_nonempty_disjoint_badParameterLocus`,
which needs no hypothesis relating `C` to `T i`.

`C ∩ X ≠ ∅` cannot be dropped from *this* statement, which is why Tag 0B1T is registered on
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_movingFamily`
instead: with `C` a closed point `p` of `𝐏²` and `X` a line missing `p`, the two intersect
properly, their intersection being empty, yet `{[g] : g(p) ∈ X}` is a hypersurface of `𝐏`, so
every line of `𝐏` meets it and every line through `[id_V]` carries a closed point `[g]` at
which `r_g(C) ∩ X` is a point where the expected dimension is `-1`. The source does not move `C`
at all in that case, and neither does the family statement. -/
public theorem exists_isOpen_forall_closedPoint_line_moving_of_intersectProperly
    (C X : IrreducibleCloseds (projectiveSpaceOfModule k V)) (hCX : IntersectProperly C X)
    (hCne : (C : Set (projectiveSpaceOfModule k V)) ≠ Set.univ)
    (hCXne : ((C : Set (projectiveSpaceOfModule k V)) ∩
      (X : Set (projectiveSpaceOfModule k V))).Nonempty)
    {ι : Type*} [Finite ι] (T : ι → IrreducibleCloseds (projectiveSpaceOfModule k V))
    (hTX : ∀ i, (T i : Set (projectiveSpaceOfModule k V)) ⊆
      (X : Set (projectiveSpaceOfModule k V))) :
    ∃ U : Set (projectiveSpaceOfModule k (ParameterModule k V)), IsOpen U ∧ U.Nonempty ∧
      ∀ q ∈ U, IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V))) →
        ∃ L : Submodule k (ParameterModule k V),
          Module.finrank k (ParameterModule k V ⧸ L) = 2 ∧
          identityParameterPoint k V ∈ linearSubspace k (ParameterModule k V) L ∧
          q ∈ linearSubspace k (ParameterModule k V) L ∧
          (∀ p : ClosedPoints k (ParameterModule k V),
            (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
              linearSubspace k (ParameterModule k V) L →
            ∀ g : V →ₗ[k] V, RepresentsParameterPoint k V p g →
              (endProjectionImage k V g (C : Set (projectiveSpaceOfModule k V))).Nonempty ∧
                IsGoodEndomorphism k V (C : Set (projectiveSpaceOfModule k V))
                  (X : Set (projectiveSpaceOfModule k V)) g) ∧
          (∀ p : ClosedPoints k (ParameterModule k V),
            (p : projectiveSpaceOfModule k (ParameterModule k V)) =
              identityParameterPoint k V →
            ∀ g : V →ₗ[k] V, RepresentsParameterPoint k V p g →
              endProjectionImage k V g (C : Set (projectiveSpaceOfModule k V)) =
                (C : Set (projectiveSpaceOfModule k V))) ∧
          ∀ p : ClosedPoints k (ParameterModule k V),
            (p : projectiveSpaceOfModule k (ParameterModule k V)) = q →
            ∀ g : V →ₗ[k] V, RepresentsParameterPoint k V p g → ∀ i,
              IsGoodEndomorphism k V (C : Set (projectiveSpaceOfModule k V))
                (T i : Set (projectiveSpaceOfModule k V)) g := by
  -- the first family of hypotheses, discharged: the bad locus of `(C, X)` lies in a closed set
  -- of codimension at least two at each of its points which misses `[id_V]`
  obtain ⟨B, hBc, hB, hcodim, hBid⟩ :=
    exists_isClosed_two_le_codimension_badParameterLocus_subset k V C X hCX hCne hCXne
  -- the second family of hypotheses, discharged: a general class is good for each pair `(C, T i)`
  choose O hOopen hOne hOgood using fun i =>
    exists_isOpen_nonempty_disjoint_badParameterLocus k V C (T i)
  exact exists_isOpen_forall_closedPoint_line_moving_of_codimension k V C X hCX hCne hCXne T hTX
    B hBc hB hBid hcodim
    (fun i => (O i)ᶜ) (fun i => (hOopen i).isClosed_compl)
    (fun i h => by
      obtain ⟨z, hz⟩ := hOne i
      rw [Set.eq_univ_iff_forall] at h
      exact h z hz)
    fun i p hbad hmem => hOgood i p hmem hbad

/-- **Tag 0B1T for disjoint `C` and `X`: the constant family.** When `C ∩ X = ∅` the source does
not move `C` at all, taking for `C'` the constant family `C × 𝐏^1`; here that is
`AlgebraicGeometry.ProjectiveSpaceOfModule.constantFamily` of `C` over a line `ℓ` through
`[id_V]` and the given point `q`. Its fibre over every closed point of `ℓ` is `C`, so it is
dominant over `ℓ` and its fibre over `0` is `C` on the nose; it meets the constant family
`X × ℓ` properly and its fibre over `∞` meets each `T i` properly because in both cases the
intersection is empty, `T i` being contained in `X`.

Proper intersection of `C` with `X` is not assumed: for disjoint subvarieties it is automatic,
by `AlgebraicGeometry.intersectProperly_of_inter_eq_empty`. What is assumed is `C ≠ 𝐏(V)`, and
only to produce the line: `dim V = 1` makes `𝐏((End V)ᵛ)` a single point, which carries no line
at all. -/
public theorem exists_isOpen_forall_closedPoint_movingFamily_of_inter_eq_empty
    (C X : IrreducibleCloseds (projectiveSpaceOfModule k V))
    (hCne : (C : Set (projectiveSpaceOfModule k V)) ≠ Set.univ)
    (hCX0 : (C : Set (projectiveSpaceOfModule k V)) ∩
      (X : Set (projectiveSpaceOfModule k V)) = ∅)
    {ι : Type*} (T : ι → IrreducibleCloseds (projectiveSpaceOfModule k V))
    (hTX : ∀ i, (T i : Set (projectiveSpaceOfModule k V)) ⊆
      (X : Set (projectiveSpaceOfModule k V))) :
    ∃ U : Set (projectiveSpaceOfModule k (ParameterModule k V)), IsOpen U ∧ U.Nonempty ∧
      ∀ q ∈ U, IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V))) →
        ∃ (L : Submodule k (ParameterModule k V))
          (hL : Module.finrank k (lineSpace k V L) = 2),
          haveI : Nontrivial (lineSpace k V L) :=
            Module.nontrivial_of_finrank_pos (R := k) (by rw [hL]; omega)
          ∃ (zero infty : movingLine k V L)
            (hzero : IsClosed ({zero} : Set (movingLine k V L)))
            (hinfty : IsClosed ({infty} : Set (movingLine k V L))),
            (movingLineι k V L).base zero = identityParameterPoint k V ∧
            (movingLineι k V L).base infty = q ∧
            ∃ Cfam : IrreducibleCloseds (movingAmbient k V L),
              closure ((ambLine k V L).base ''
                  (Cfam : Set (movingAmbient k V L))) = Set.univ ∧
              movingFibre k V L zero hzero (Cfam : Set (movingAmbient k V L)) =
                (C : Set (projectiveSpaceOfModule k V)) ∧
              (∃ Xfam : IrreducibleCloseds (movingAmbient k V L),
                (Xfam : Set (movingAmbient k V L)) =
                  constantFamily k V L (X : Set (projectiveSpaceOfModule k V)) ∧
                IntersectProperly Cfam Xfam) ∧
              ∀ i, ∃ F : IrreducibleCloseds (projectiveSpaceOfModule k V),
                (F : Set (projectiveSpaceOfModule k V)) =
                  movingFibre k V L infty hinfty (Cfam : Set (movingAmbient k V L)) ∧
                IntersectProperly F (T i) := by
  have h2V : 2 ≤ Module.finrank k V :=
    two_le_finrank_of_isClosed_ne_univ k V C.isClosed' hCne C.isIrreducible'.nonempty
  have h3P : 3 ≤ Module.finrank k (ParameterModule k V) := by
    rw [finrank_parameterModule]
    calc (3 : ℕ) ≤ 2 * 2 := by omega
      _ ≤ Module.finrank k V * Module.finrank k V := Nat.mul_le_mul h2V h2V
  have : Nontrivial (ParameterModule k V) :=
    Module.nontrivial_of_finrank_pos (R := k) (by omega)
  obtain ⟨U, hUopen, hUne, hU⟩ :=
    exists_isOpen_subset_union_lines_disjoint_of_forall_codimension_ge_two k
      (ParameterModule k V) h3P ∅ isClosed_empty (by simp) (identityParameterPoint k V)
      (isClosed_identityParameterPoint k V) (by simp)
  refine ⟨U, hUopen, hUne, fun q hqU hqc => ?_⟩
  obtain ⟨L, hL2, hidL, hqL, -⟩ := hU q hqU hqc
  have hNT : Nontrivial (lineSpace k V L) :=
    Module.nontrivial_of_finrank_pos (R := k) (by rw [hL2]; omega)
  refine ⟨L, hL2, ?_⟩
  obtain ⟨zero, hzero, hzeroim⟩ := exists_movingLine_point k V L hidL
    (isClosed_identityParameterPoint k V)
  obtain ⟨infty, hinfty, hinftyim⟩ := exists_movingLine_point k V L hqL hqc
  have hCclosed : IsClosed (C : Set (projectiveSpaceOfModule k V)) := C.isClosed'
  have hCirr : IsIrreducible (C : Set (projectiveSpaceOfModule k V)) := C.isIrreducible'
  -- every fibre of the constant family is `C` itself
  have hfib : ∀ (lam : movingLine k V L) (hlam : IsClosed ({lam} : Set (movingLine k V L))),
      movingFibre k V L lam hlam
          (constantFamily k V L (C : Set (projectiveSpaceOfModule k V))) =
        (C : Set (projectiveSpaceOfModule k V)) :=
    fun lam hlam => movingFibre_constantFamily k V L _ lam hlam
  refine ⟨zero, infty, hzero, hinfty, hzeroim, hinftyim,
    ⟨constantFamily k V L (C : Set (projectiveSpaceOfModule k V)),
      isIrreducible_constantFamily k V L _ hCclosed hCirr,
      isClosed_constantFamily k V L _ hCclosed⟩, ?_, hfib zero hzero, ?_, ?_⟩
  · -- clause (1): every closed point of the line has nonempty fibre, so the image is dense
    exact closure_eq_univ_of_closedPoints_subset fun lam hlam =>
      mem_image_ambLine_of_movingFibre_nonempty k V L lam (mem_closedPoints_iff.mp hlam)
        (by
          change (movingFibre k V L lam (mem_closedPoints_iff.mp hlam)
            (constantFamily k V L (C : Set (projectiveSpaceOfModule k V)))).Nonempty
          rw [hfib lam (mem_closedPoints_iff.mp hlam)]
          exact hCirr.nonempty)
  · -- clause (3): the two constant families are disjoint
    refine ⟨⟨constantFamily k V L (X : Set (projectiveSpaceOfModule k V)),
      isIrreducible_constantFamily k V L _ X.isClosed' X.isIrreducible',
      isClosed_constantFamily k V L _ X.isClosed'⟩, rfl,
      intersectProperly_of_inter_eq_empty _ _ ?_⟩
    change constantFamily k V L (C : Set (projectiveSpaceOfModule k V)) ∩
      constantFamily k V L (X : Set (projectiveSpaceOfModule k V)) = ∅
    rw [constantFamily, constantFamily, lineProductConstant, lineProductConstant,
      ← Set.preimage_inter, hCX0, Set.preimage_empty]
  · -- clause (4): the fibre over `∞` is `C`, which misses every `T i`
    intro i
    refine ⟨C, (hfib infty hinfty).symm, intersectProperly_of_inter_eq_empty _ _ ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    exact fun z hz => (Set.eq_empty_iff_forall_notMem.mp hCX0) z ⟨hz.1, hTX i hz.2⟩

/-- **The Moving Lemma with the family over a general line of `𝐏 = 𝐏((End V)ᵛ)`: a statement
stronger than Tag 0B1T.** Let `C` be a closed subvariety of `𝐏(V)` with `C ≠ 𝐏(V)`, let `X` be a
closed subvariety of `𝐏(V)` intersecting `C` properly and let `T i ⊆ X` be a finite collection
of closed subvarieties. Nothing else is assumed: in particular nothing of the pairs `(C, T i)`,
nothing of the bad locus of `(C, X)` in `𝐏`, and not that `C` meets `X`. Then for a general line
`ℓ ⊆ 𝐏` through `[id_V]` — that is, for the line through `[id_V]` and any closed point `∞` of a
nonempty Zariski open subset of `𝐏` — there is a closed subvariety `C'` of `ℓ × 𝐏(V)` such that:
`C'` is dominant over `ℓ`; its fibre over `0 = [id_V]` is `C`; it intersects the constant family
`X × ℓ` properly; and its fibre over `∞` intersects each `T i` properly.

Two cases, as in the source. When `C ∩ X = ∅` the family is the constant one and nothing is
moved,
`…ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_movingFamily_of_inter_eq_empty`;
when `C` meets `X` the general-position construction applies, and it is there that
`IntersectProperly C X` does its work, bounding the codimension of the bad locus of `(C, X)`
through Tag 0B1S.

`X` is a *closed* subvariety here. That is what the source means: Definition 0AZQ, which is what
"intersect properly" abbreviates both in the hypothesis and in clause (3), is stated for closed
subvarieties only; the chapter introduces `W ⊂ X` as "a subvariety" and then says of that very
`W` that it "is a closed subvariety"; and the proof of 0B1T applies Lemma 0B1S, whose hypothesis
is that both subvarieties are closed.

**Why this is stronger than Tag 0B1T, and why `C ≠ 𝐏(V)` comes with the extra strength.** Tag
0B1T puts its family over `𝐏^1`, an abstract projective line; this statement puts it over a
*general line of `𝐏`* through `[id_V]`, which is more information — such a line is a projective
line, so the source's conclusion follows, and that implication is how Tag 0B1T is proved from
this one in
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyProjectiveLine`. The price
is `C ≠ 𝐏(V)`, which the shape of this conclusion forces rather than the proof: a line of `𝐏` is
presented by a submodule `L ⊆ (End V)ᵛ` of corank two, and `dim_k (End V)ᵛ = (dim_k V)^2`, so at
`dim V = 1` there is no such `L` — while the source's hypotheses are satisfiable there, `𝐏(V)`
being irreducible and so `C = X = 𝐏(V)` a pair of closed subvarieties intersecting properly. That
measurement is
`…ProjectiveSpaceOfModule.exists_intersectProperly_and_not_exists_finrank_lineSpace_eq_two`
below, and it is why Tag 0B1T is registered on the abstract-line form and not here. `C = 𝐏(V)` is
exactly the case `dim V = 1` leaves, and it is handled there by the constant family. -/
public theorem exists_isOpen_forall_closedPoint_movingFamily
    (C X : IrreducibleCloseds (projectiveSpaceOfModule k V)) (hCX : IntersectProperly C X)
    (hCne : (C : Set (projectiveSpaceOfModule k V)) ≠ Set.univ)
    {ι : Type*} [Finite ι] (T : ι → IrreducibleCloseds (projectiveSpaceOfModule k V))
    (hTX : ∀ i, (T i : Set (projectiveSpaceOfModule k V)) ⊆
      (X : Set (projectiveSpaceOfModule k V))) :
    ∃ U : Set (projectiveSpaceOfModule k (ParameterModule k V)), IsOpen U ∧ U.Nonempty ∧
      ∀ q ∈ U, IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V))) →
        ∃ (L : Submodule k (ParameterModule k V))
          (hL : Module.finrank k (lineSpace k V L) = 2),
          haveI : Nontrivial (lineSpace k V L) :=
            Module.nontrivial_of_finrank_pos (R := k) (by rw [hL]; omega)
          ∃ (zero infty : movingLine k V L)
            (hzero : IsClosed ({zero} : Set (movingLine k V L)))
            (hinfty : IsClosed ({infty} : Set (movingLine k V L))),
            (movingLineι k V L).base zero = identityParameterPoint k V ∧
            (movingLineι k V L).base infty = q ∧
            ∃ Cfam : IrreducibleCloseds (movingAmbient k V L),
              closure ((ambLine k V L).base ''
                  (Cfam : Set (movingAmbient k V L))) = Set.univ ∧
              movingFibre k V L zero hzero (Cfam : Set (movingAmbient k V L)) =
                (C : Set (projectiveSpaceOfModule k V)) ∧
              (∃ Xfam : IrreducibleCloseds (movingAmbient k V L),
                (Xfam : Set (movingAmbient k V L)) =
                  constantFamily k V L (X : Set (projectiveSpaceOfModule k V)) ∧
                IntersectProperly Cfam Xfam) ∧
              ∀ i, ∃ F : IrreducibleCloseds (projectiveSpaceOfModule k V),
                (F : Set (projectiveSpaceOfModule k V)) =
                  movingFibre k V L infty hinfty (Cfam : Set (movingAmbient k V L)) ∧
                IntersectProperly F (T i) := by
  rcases Set.eq_empty_or_nonempty ((C : Set (projectiveSpaceOfModule k V)) ∩
    (X : Set (projectiveSpaceOfModule k V))) with hCX0 | hCXne
  · -- disjoint `C` and `X`: the constant family
    exact exists_isOpen_forall_closedPoint_movingFamily_of_inter_eq_empty k V C X hCne hCX0 T hTX
  -- the fibrewise form of the four clauses, at these same hypotheses: both families of
  -- bad-locus hypotheses are discharged there
  obtain ⟨U, hUopen, hUne, hU⟩ :=
    exists_isOpen_forall_closedPoint_line_moving_of_intersectProperly k V C X hCX hCne hCXne T hTX
  refine ⟨U, hUopen, hUne, fun q hqU hqc => ?_⟩
  obtain ⟨L, hL2, hidL, hqL, hgood, hid, hTinf⟩ := hU q hqU hqc
  have hNT : Nontrivial (lineSpace k V L) :=
    Module.nontrivial_of_finrank_pos (R := k) (by rw [hL2]; omega)
  refine ⟨L, hL2, ?_⟩
  set b := Module.finBasisOfFinrankEq k (lineSpace k V L) hL2 with hb
  obtain ⟨zero, hzero, hzeroim⟩ := exists_movingLine_point k V L hidL
    (isClosed_identityParameterPoint k V)
  obtain ⟨mu0, hmu0, hzerodef⟩ := exists_eq_linearFunctionalPoint k (lineSpace k V L) zero hzero
  subst hzerodef
  obtain ⟨infty, hinfty, hinftyim⟩ := exists_movingLine_point k V L hqL hqc
  obtain ⟨mu1, hmu1, hinftydef⟩ :=
    exists_eq_linearFunctionalPoint k (lineSpace k V L) infty hinfty
  subst hinftydef
  -- every closed point of the line is good
  have hgoodmu : ∀ (mu : Module.Dual k (lineSpace k V L)), mu ≠ 0 →
      (endProjectionImage k V (lineEnd k V L mu)
          (C : Set (projectiveSpaceOfModule k V))).Nonempty ∧
        IsGoodEndomorphism k V (C : Set (projectiveSpaceOfModule k V))
          (X : Set (projectiveSpaceOfModule k V)) (lineEnd k V L mu) := by
    intro mu hmu
    obtain ⟨p, -, hpL, hprep⟩ := exists_representsParameterPoint_of_movingLine k V L hmu
    exact hgood p hpL (lineEnd k V L mu) hprep
  have hCg : ∀ (mu : Module.Dual k (lineSpace k V L)), mu ≠ 0 →
      (C : Set (projectiveSpaceOfModule k V)) ⊆
        (endDomain k V (lineEnd k V L mu) : Set (projectiveSpaceOfModule k V)) :=
    fun mu hmu => (hgoodmu mu hmu).2.1
  have hCclosed : IsClosed (C : Set (projectiveSpaceOfModule k V)) := C.isClosed'
  have hCirr : IsIrreducible (C : Set (projectiveSpaceOfModule k V)) := C.isIrreducible'
  have hXclosed : IsClosed (X : Set (projectiveSpaceOfModule k V)) := X.isClosed'
  have hXirr : IsIrreducible (X : Set (projectiveSpaceOfModule k V)) := X.isIrreducible'
  have hSclosed := isClosed_movingFamilySet k V L b hCclosed
  have hSirr := isIrreducible_movingFamilySet k V L b hCclosed hCirr hCirr.nonempty hCg
  -- clause (2): the fibre over `0` is `C`
  have hfib0 : movingFibre k V L (linearFunctionalPoint k (lineSpace k V L) mu0 hmu0) hzero
      (movingFamilySet k V L b (C : Set (projectiveSpaceOfModule k V))) =
        (C : Set (projectiveSpaceOfModule k V)) := by
    obtain ⟨p, hpdef, hpL, hprep⟩ := exists_representsParameterPoint_of_movingLine k V L hmu0
    refine (movingFibre_movingFamilySet k V L b hCclosed hmu0 (hCg mu0 hmu0)).trans ?_
    exact hid p (by rw [hpdef]; exact hzeroim) (lineEnd k V L mu0) hprep
  -- clause (1): dominance
  have hdom : closure ((ambLine k V L).base ''
      movingFamilySet k V L b (C : Set (projectiveSpaceOfModule k V))) = Set.univ := by
    refine closure_image_ambLine_movingFamilySet k V L b _ fun lam hlam => ?_
    obtain ⟨mu, hmu, rfl⟩ := exists_eq_linearFunctionalPoint k (lineSpace k V L) lam hlam
    exact movingFibre_movingFamilySet_nonempty k V L b hCclosed hCirr.nonempty hmu (hCg mu hmu)
  refine ⟨linearFunctionalPoint k (lineSpace k V L) mu0 hmu0,
    linearFunctionalPoint k (lineSpace k V L) mu1 hmu1, hzero, hinfty, hzeroim, hinftyim,
    ⟨movingFamilySet k V L b (C : Set (projectiveSpaceOfModule k V)), hSirr, hSclosed⟩,
    hdom, hfib0, ?_, ?_⟩
  · -- clause (3)
    refine ⟨⟨constantFamily k V L (X : Set (projectiveSpaceOfModule k V)),
      isIrreducible_constantFamily k V L _ hXclosed hXirr,
      isClosed_constantFamily k V L _ hXclosed⟩, rfl, ?_⟩
    exact intersectProperly_criterion_movingFamilySet k V L b hCclosed hCirr.nonempty hXclosed
      hXirr.nonempty hL2 hCg (fun mu hmu => (hgoodmu mu hmu).2)
      (linearFunctionalPoint k (lineSpace k V L) mu0 hmu0) hzero hfib0 hSirr hdom
  · -- clause (4)
    intro i
    obtain ⟨p, hpdef, hpL, hprep⟩ := exists_representsParameterPoint_of_movingLine k V L hmu1
    have hinftyeq : movingFibre k V L (linearFunctionalPoint k (lineSpace k V L) mu1 hmu1)
        hinfty (movingFamilySet k V L b (C : Set (projectiveSpaceOfModule k V))) =
          endProjectionImage k V (lineEnd k V L mu1)
            (C : Set (projectiveSpaceOfModule k V)) :=
      movingFibre_movingFamilySet k V L b hCclosed hmu1 (hCg mu1 hmu1)
    have hgoodi := hTinf p (by rw [hpdef]; exact hinftyim) (lineEnd k V L mu1) hprep i
    refine ⟨⟨movingFibre k V L (linearFunctionalPoint k (lineSpace k V L) mu1 hmu1) hinfty
        (movingFamilySet k V L b (C : Set (projectiveSpaceOfModule k V))), ?_,
      isClosed_movingFibre k V L _ hinfty hSclosed⟩, rfl, ?_⟩
    · rw [hinftyeq]
      exact isIrreducible_endProjectionImage k V (lineEnd k V L mu1) (hCg mu1 hmu1) hCirr
    · have h2 := hgoodi.2
      rw [← hinftyeq] at h2
      exact h2

omit [IsAlgClosed k] [Nontrivial V] in
/-- **The hypothesis `C ≠ 𝐏(V)` of
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_movingFamily` is
forced by the shape of its conclusion.** At `dim_k V = 1` the source's hypotheses are
satisfiable: `𝐏(V)` is irreducible, so `C = X = 𝐏(V)` are closed subvarieties which intersect
properly, and the collection of `T i` may be taken empty. The conclusion, however, asks for a
line inside `𝐏 = 𝐏((End V)ᵛ)`, presented as a submodule `L ⊆ (End V)ᵛ` of corank two; and
`dim_k (End V)ᵛ = (dim_k V)^2 = 1`, so no submodule has a quotient of dimension two. The
source's proof is in the same position — it chooses a general line `ℓ ⊂ 𝐏` through `[id_V]`,
which a one-point `𝐏` does not carry — and covers `dim V = 1` only through the constant family
`C × 𝐏^1` over an abstract projective line, which is not a line of `𝐏`. -/
public theorem exists_intersectProperly_and_not_exists_finrank_lineSpace_eq_two
    (h1 : Module.finrank k V = 1) :
    (∃ C X : IrreducibleCloseds (projectiveSpaceOfModule k V), IntersectProperly C X) ∧
      ¬ ∃ L : Submodule k (ParameterModule k V), Module.finrank k (lineSpace k V L) = 2 := by
  have h1' : Module.finrank k V = 0 + 1 := by omega
  have : IrreducibleSpace (projectiveSpaceOfModule k V) :=
    irreducibleSpace_projectiveSpaceOfModule_of_finrank_eq k V h1'
  refine ⟨⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩,
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩, ?_⟩, ?_⟩
  · have hd : topologicalKrullDim ↥(Set.univ : Set (projectiveSpaceOfModule k V)) =
        topologicalKrullDim (projectiveSpaceOfModule k V) :=
      IsHomeomorph.topologicalKrullDim_eq _
        (Homeomorph.Set.univ (projectiveSpaceOfModule k V)).isHomeomorph
    change topologicalKrullDim ↥((Set.univ : Set (projectiveSpaceOfModule k V)) ∩ Set.univ) +
        topologicalKrullDim (projectiveSpaceOfModule k V) ≤
      topologicalKrullDim ↥(Set.univ : Set (projectiveSpaceOfModule k V)) +
        topologicalKrullDim ↥(Set.univ : Set (projectiveSpaceOfModule k V))
    rw [Set.inter_self, hd]
  · rintro ⟨L, hL⟩
    have hP : Module.finrank k (ParameterModule k V) = 1 := by
      rw [finrank_parameterModule, h1, one_mul]
    have hq : Module.finrank k (ParameterModule k V ⧸ L) = 2 := hL
    have hsum := Submodule.finrank_quotient_add_finrank L
    rw [hP, hq] at hsum
    omega

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
