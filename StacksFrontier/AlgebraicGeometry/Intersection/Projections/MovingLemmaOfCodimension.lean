module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.GeneralLineProperIntersectionOfCodimension
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingLemma
import all StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingLemma

/-!
# Moving a subvariety off finitely many subvarieties, for bad loci of codimension two

Let `C, X` be closed subvarieties of `𝐏(V)` which intersect properly and let `T i ⊆ X` be a
finite collection of closed subvarieties. Suppose the bad locus of the pair `(C, X)` is contained
in a closed subset of the parameter space `𝐏 = 𝐏((End V)ᵛ)` which misses `[id_V]` and has
codimension at least two at each of its points, and that for each `i` the bad locus of the pair
`(C, T i)` is contained in a closed subset of `𝐏` other than all of `𝐏`. Then for a general line
`ℓ` through `[id_V]` the four clauses of Tag 0B1T hold on the fibres of the family of translates
`r_g(C)`, as in `StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingLemma`.

## Main results

* `…ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_line_moving_of_codimension`: all
  four clauses of the source along a general line through `[id_V]`, carrying the two families of
  bad-locus hypotheses which this module is upstream of. The form with both discharged is
  `…ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_line_moving_of_intersectProperly`
  of `StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyMain`.

## Implementation notes

**What is proved here, and where the family itself is.** What is proved here is each of the four
clauses read on the fibres, in the form in which the source's own proof establishes them, with
`𝐏^1` realized as the line `ℓ` and the fibre `C'_{[g]}` realized as the translate `r_g(C)`,
which is the set `AlgebraicGeometry.ProjectiveSpaceOfModule.endProjectionImage`:

* clause (1), dominance of `C' → 𝐏^1`, becomes: the fibre over every closed point of `ℓ` is
  nonempty, so every closed point of `ℓ` is in the image of the family;
* clause (2), `C'_0 = C`, becomes: `r_g(C) = C` for every representative `g` of `[id_V]`;
* clause (3), proper intersection of `C'` with `X × 𝐏^1`, becomes: `r_g(C)` meets `X` properly
  for every representative of every closed point of `ℓ`;
* clause (4), proper intersection of `C'_∞` with the `T i`, becomes: `r_g(C)` meets each `T i`
  properly for every representative of the `∞` point of `ℓ`.

The four are asserted together, of one and the same line, by
`…ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_line_moving_of_codimension`; clause
(2) holds of every line through `[id_V]` and is also available on its own as
`AlgebraicGeometry.ProjectiveSpaceOfModule.endProjectionImage_eq_of_represents_identity`.

The family `C'` itself is
`AlgebraicGeometry.ProjectiveSpaceOfModule.movingFamilySet` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilySet`, a closed subvariety of
the product `ℓ ×_k 𝐏(V)` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyProduct`, and the four
clauses about it are
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_movingFamily` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyMain`. The results of this
module are what that one consumes at each closed point of the line: the step between the two is
the fibre-dimension computation the source compresses into "Parts (1) and (2) are clear" and the
two sentences after it.

**"For a general line", "a general point".** Both are read exactly as in Tag 0B2T and Tag 0B1S:
there is a nonempty Zariski open subset `U ⊆ 𝐏` such that every closed point `q ∈ U` is the `∞`
point of a line `ℓ` through `[id_V]` with the stated properties. The lines so produced sweep out
a dense open subset of `𝐏`. A line is a
`AlgebraicGeometry.ProjectiveSpaceOfModule.linearSubspace` cut out by a submodule of corank two,
as in those tags.

**`0` and `∞`.** That the two distinguished points of the line are distinct is not asserted, the
source leaving it implicit in "general". It is not needed to see that the conclusion is not
vacuous: clause (4) holds for every representative of `∞`, so if `∞` were `[id_V]` then clause
(4) would say that `C` already intersects each `T i` properly, which is the one case in which
nothing has to be moved.

**Proper intersection.** As in Tag 0B1S, the conclusion uses
`AlgebraicGeometry.ProjectiveSpaceOfModule.IsGoodEndomorphism`, whose second clause is the
dimension criterion defining `AlgebraicGeometry.IntersectProperly` (Tag 0AZQ) read on the image
set `r_g(C)`; the library has closedness of that image only for the linear projection and not
for `r_g`, so the predicate on irreducible closed subsets cannot be applied to it directly.
`AlgebraicGeometry.ProjectiveSpaceOfModule.isGoodEndomorphism_iff_intersectProperly` checks
that the two readings agree whenever the image is the underlying set of a closed subvariety.

**What is carried.** Two families of hypotheses. First, that the bad locus of the pair `(C, X)`
is *contained in* a closed subset `B ⊆ 𝐏` which has codimension at least two at each of its
points and misses `[id_V]`: this is what the formalization of Tag 0B1S itself carries, and it is
passed through unchanged. `B` is *not* asked to be irreducible, and the pointwise bound
`∀ x ∈ B, 2 ≤ codimension (closureSingleton x)` is what replaces `2 ≤ codimension B`: asking for
an irreducible `B` of codimension at least two is not satisfiable for every admissible pair, no
such subset existing for `C` and `X` two distinct lines of `𝐏²`, by
`AlgebraicGeometry.ProjectiveSpaceOfModule.not_exists_irreducible_badParameterLocus` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.BadLocusReducible`; a statement carrying
that hypothesis would be vacuous for that pair. See the implementation notes of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.GeneralLineProperIntersection`.
Second, that for each `i` the bad locus of the pair `(C, T i)` is *contained in* a closed subset
of `𝐏` other than all of `𝐏`. Containment and not equality in both families: that is what the
proof uses, and the bad locus is not known to be closed — it consists of closed points only, so
asking it to be closed outright would force it to be finite; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.GeneralLineProperIntersection`.
That second family is the source's "a general point `∞ = [g] ∈ ℓ` is a general point of `𝐏` and
for such a point `r_g(C) ∩ T` is proper for any closed subvariety `T` of `𝐏(V)`", whose details
the source omits. **Neither family is an assumption of the Moving Lemma as this project states
it.** The second is discharged, for any two closed subvarieties and with no hypothesis relating
them, by
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_nonempty_forall_isGoodEndomorphism` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.GeneralTranslateProper`, and the first by
`…ProjectiveSpaceOfModule.exists_isClosed_two_le_codimension_badParameterLocus_subset` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionDominant`; the declaration that
consumes both discharges is
`…ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_line_moving_of_intersectProperly` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyMain`, which states these
same four clauses on the fibres at the hypotheses of Tag 0B1S and assumes neither family; the
four clauses about the family `C'` itself, at the source's own hypotheses on `C`, `X` and the
`T i`, are
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_movingFamily_of_subvariety_fixed` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingLemmaFixedPoints`, which is
where Tag 0B1T is registered for them, its base being the source's own `𝐏^1`. They are still
hypotheses *here* for a reason of module order and not of mathematics: this module is upstream
of the whole incidence-correspondence construction — the
product `𝐏(V) ×_k 𝐏(V)` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.CollinearityLocus` is built on top of it
— so neither discharge can be imported at this point. The half of the source's sentence which is
a general fact rather than a claim about the `T i` — that a general point of `ℓ` is a general
point of `𝐏` — is proved here, as the intersection of the open subset of Tag 0B1S with the
complements of the `BT i`, using that `𝐏` is irreducible.

**Closedness of `X`.** The source calls `X` a subvariety, not necessarily closed. It is taken
closed in this module, because Tag 0B1S is formalized for a pair of closed subvarieties. The
whole lemma for a not necessarily closed subvariety `X` and `T i` closed in `X`, with clause (2)
scheme theoretically, is
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_movingFamily_of_subvariety_fixed`
of `StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingLemmaFixedPoints`.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0B2T](https://stacks.math.columbia.edu/tag/0B2T)
* [Stacks Project, Tag 0AZQ](https://stacks.math.columbia.edu/tag/0AZQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

variable [IsAlgClosed k] [FiniteDimensional k V]

/-- **Stacks Project, Tag 0B1T.** Let `C, X` be closed subvarieties of
`𝐏(V)` which intersect properly, with `C ≠ 𝐏(V)` and `C ∩ X ≠ ∅`, and let `T i ⊆ X` be a finite
collection of closed subvarieties. Suppose the bad locus of `(C, X)` in the parameter space
`𝐏 = 𝐏((End V)ᵛ)` is contained in a closed subset `B` which has codimension at least two at each
of its points and does not contain `[id_V]`, and that for each `i` the bad locus of `(C, T i)` is
contained in a closed subset `BT i` other than all of `𝐏`. Then for a
general line `ℓ ⊆ 𝐏` through `[id_V]` — that is, for the line through `[id_V]` and any closed
point `∞` of a nonempty Zariski open subset of `𝐏` — the four clauses of the source hold of the
family whose fibre over a point `[g]` of `ℓ` is the translate `r_g(C)`: that family is dominant
over `ℓ`, because `r_g(C)` is nonempty for every representative `g` of every closed point of
`ℓ`; its fibre over `0 = [id_V]` is `C`; it meets the constant family `X × ℓ` properly, because
`r_g(C)` meets `X` properly at every closed point of `ℓ`; and its fibre over `∞` meets each
`T i` properly.

Both families of hypotheses are carried, this module being upstream of either discharge, which
is why Tag 0B1T is registered not here but on the form over `𝐏^1`
`…ProjectiveSpaceOfModule.exists_movingFamily_of_subvariety_fixed` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingLemmaFixedPoints`, which
states all four clauses about the family itself at the source's hypotheses alone. -/
@[stacks 0B1T "clauses (1), (3) and (4), read on the fibres, in the form that assumes bounds on \
the two bad loci: 𝐏^1 is the source's own line ℓ ⊆ 𝐏 = 𝐏((End V)ᵛ) through [id_V] and the \
fibre C'_[g] is the translate r_g(C), so that (1) 'C' → 𝐏^1 is dominant' is read as 'the fibre \
over every closed point of ℓ is nonempty', (3) as 'r_g(C) intersects X properly for every \
representative g of every closed point of ℓ' and (4) as 'r_g(C) intersects each T i properly \
for every representative g of the ∞ point of ℓ'; clause (2) is \
endProjectionImage_eq_of_represents_identity of this module; 'general' is read as in Tags 0B2T \
and 0B1S, namely that there is a nonempty Zariski open subset of 𝐏 each of whose closed points \
is the ∞ point of such a line; proper intersection is the dimension criterion defining Tag \
0AZQ read on the image set r_g(C), as in Tag 0B1S; X is taken closed in this form, Lemma 0B1S \
being formalized for a pair of closed subvarieties. The two bad-locus bounds are discharged by \
AlgebraicGeometry.ProjectiveSpaceOfModule \
.exists_isOpen_forall_closedPoint_line_moving_of_intersectProperly of \
StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyMain, and the tag is \
registered for all four clauses about the family C' over 𝐏^1 at the source's own hypotheses on \
C, X (not necessarily closed) and the T i, clause (2) scheme theoretically, on \
AlgebraicGeometry.ProjectiveSpaceOfModule.exists_movingFamily_of_subvariety_fixed of \
StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingLemmaFixedPoints; this form \
keeps its place here, upstream of the incidence-correspondence construction that either \
discharge needs"]
public theorem exists_isOpen_forall_closedPoint_line_moving_of_codimension [Nontrivial V]
    (C X : IrreducibleCloseds (projectiveSpaceOfModule k V)) (hCX : IntersectProperly C X)
    (hCne : (C : Set (projectiveSpaceOfModule k V)) ≠ Set.univ)
    (hCXne : ((C : Set (projectiveSpaceOfModule k V)) ∩
      (X : Set (projectiveSpaceOfModule k V))).Nonempty)
    {ι : Type*} [Finite ι] (T : ι → IrreducibleCloseds (projectiveSpaceOfModule k V))
    (_hTX : ∀ i, (T i : Set (projectiveSpaceOfModule k V)) ⊆
      (X : Set (projectiveSpaceOfModule k V)))
    (B : Set (projectiveSpaceOfModule k (ParameterModule k V))) (hBc : IsClosed B)
    (hB : ∀ p : ClosedPoints k (ParameterModule k V),
      (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
          badParameterLocus k V (C : Set (projectiveSpaceOfModule k V))
            (X : Set (projectiveSpaceOfModule k V)) →
        (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈ B)
    (hBid : identityParameterPoint k V ∉ B)
    (hcodim : ∀ x ∈ B, (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (BT : ι → Set (projectiveSpaceOfModule k (ParameterModule k V)))
    (hBT : ∀ i, IsClosed (BT i)) (hBTne : ∀ i, BT i ≠ Set.univ)
    (hBTbad : ∀ (i) (p : ClosedPoints k (ParameterModule k V)),
      (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
          badParameterLocus k V (C : Set (projectiveSpaceOfModule k V))
            (T i : Set (projectiveSpaceOfModule k V)) →
        (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈ BT i) :
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
  have hnt : Nontrivial (ParameterModule k V) := by
    refine Module.nontrivial_of_finrank_pos (R := k) ?_
    rw [Subspace.dual_finrank_eq, Module.finrank_linearMap]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos
  have hirr : IrreducibleSpace (projectiveSpaceOfModule k (ParameterModule k V)) := by
    obtain ⟨n, hn⟩ : ∃ n, Module.finrank k (ParameterModule k V) = n + 1 :=
      ⟨Module.finrank k (ParameterModule k V) - 1, by
        have := Module.finrank_pos (R := k) (M := ParameterModule k V); omega⟩
    exact irreducibleSpace_projectiveSpaceOfModule_of_basis k (ParameterModule k V)
      (Module.finBasisOfFinrankEq k (ParameterModule k V) hn)
  obtain ⟨U, hUopen, hUne, hU⟩ :=
    exists_isOpen_closedPoint_line_isGood_of_codimension k V C X hCX hCne hCXne B hBc hB
      hBid hcodim
  refine ⟨U ∩ ⋂ i, (BT i)ᶜ, ?_, ?_, ?_⟩
  · exact hUopen.inter (isOpen_iInter_of_finite fun i => (hBT i).isOpen_compl)
  · exact nonempty_inter_iInter _ (fun i => (hBT i).isOpen_compl)
      (fun i => Set.nonempty_compl.mpr (hBTne i)) U hUopen hUne
  · rintro q ⟨hqU, hqB⟩ hqc
    obtain ⟨L, hL2, hidL, hqL, hgood⟩ := hU q hqU hqc
    refine ⟨L, hL2, hidL, hqL, fun p hpL g hgrep => ?_,
      fun p hpid g hgrep => endProjectionImage_eq_of_represents_identity k V hpid hgrep _,
      fun p hpq g hgrep i => ?_⟩
    · exact ⟨endProjectionImage_nonempty k V C.isIrreducible'.nonempty
        (hgood p hpL g hgrep).1, hgood p hpL g hgrep⟩
    · refine isGoodEndomorphism_of_notMem_badParameterLocus k V ?_ hgrep
      intro hbad
      exact Set.mem_iInter.mp hqB i (hpq ▸ hBTbad i p hbad)

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
