module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechRefinements.PositiveDegreeSurjectivity

/-!
# The refinement step of [Stacks, Tag 07MC], and why its colimit is not a filtered one

The proof of [Stacks, Tag 07MC] contains one topological step: given a cocycle `α₃` of the
total Čech complex of `𝓕₃^•` for an open covering `𝒰`, "after refining `𝒰` if necessary, we
can find a cochain `α₂` of the total Čech complex of `𝓕₂^•` mapping to `α₃`".  Everything else
in that proof is homological algebra about short exact sequences of cochain complexes, and that
part is already formalized, in `StacksFrontier.Algebra.Homology.CupProductBoundaryClass`.

This file contains two measurements about the remaining step.

## The step itself, in Čech degree

`Stacks.Cohomology.CechRefinement.exists_refinement_cochain_lift` is the step for the Čech
complex of a single sheaf: on a Hausdorff quasi-compact space, a Čech cochain of the last term
of a short exact sequence of abelian sheaves becomes, after a refinement of the covering, the
image of a Čech cochain of the middle term.

It is not new mathematics but a second use of one lemma that is already here.
`Stacks.Cohomology.CechRefinement.exists_refinement_cochain_preimage_int` is the *exactness*
form of the same statement — a cochain of the middle term dying in the last term comes, after a
refinement, from the first term — and applying it to the short complex `𝓕₂ ⟶ 𝓕₃ ⟶ 0`, which is
exact precisely because `𝓕₂ ⟶ 𝓕₃` is an epimorphism, gives the lifting form.  Both rest on
[Stacks, Tag 09UW], `Stacks.exists_cover_closure_subset_and_refines`, which is where the
Hausdorff quasi-compact hypothesis is used: each component of the cochain lifts over *some*
covering of its own iterated intersection, and 09UW produces a *single* refinement of the
covering on whose iterated intersections all of those local lifts are simultaneously defined.

The hypothesis is therefore not an added convenience.  It is the hypothesis under which this
repository proves the Čech-to-sheaf comparison to be an isomorphism at all
(`Stacks.Cohomology.CechRefinement.isIso_colimitToCohomology`, [Stacks, Tag 09V2]), which is
in turn the hypothesis [Stacks, Tag 07MC] makes for itself: "assume Čech cohomology agrees with
cohomology for the sheaves `𝓕ᵢ^p` and `𝓖ⱼ^q`".

## Why the colimit over refinements is not a filtered colimit

The natural way to turn the step above into short exactness of a colimit of total Čech
complexes is to take the colimit over `Stacks.Cohomology.CechRefinement.OpenCoverSet X`, the
category of open coverings and refinements, and to appeal to exactness of filtered colimits.
That route does not exist: **that category is not filtered.**

A morphism of coverings carries a *chosen* refinement function, which is what makes coverings a
category rather than a preorder and what the induced map of Čech complexes depends on.  Two
choices of refinement function are then parallel morphisms, and
`Stacks.Cohomology.CechRefinement.OpenCoverSet.comp_ne_comp_of_forall_index_ne` says they
cannot be equalized as soon as they disagree at every member of the refining covering through
a single point `x`: a further refinement still has a member containing `x`, and that member's
chosen index is a member of the refining covering containing `x`, so the two composites differ
there.  `Stacks.Cohomology.CechRefinement.NotFiltered.not_isFiltered_openCoverSet_int` exhibits
that configuration on `ℤ` with the discrete topology and so refutes
`CategoryTheory.IsFiltered (OpenCoverSet ℤ)`.

Only the `cocone_maps` half of filteredness fails; the `cocone_objs` half holds, and is
`Stacks.Cohomology.CechRefinement.OpenCoverSet.exists_common_refinement`.

This is why `Stacks.Cohomology.CechRefinement.cechDiagram`, the existing colimit over
refinements, is a diagram of Čech cohomology *in a fixed degree* rather than of Čech complexes:
two refinement functions induce maps of Čech complexes that agree only up to homotopy, hence
agree after passing to cohomology, and the diagram of complexes retains the discrepancy.

## Relation to the statement of [Stacks, Tag 07MC] on `X`

`Stacks.Cech.Hypercohomology.cup_boundary` takes the refinement step on cohomology classes
rather than on cochains: the total Čech complexes of a short exact sequence of complexes are
compared with hypercohomology through `Stacks.Cech.Hypercohomology.cechClass`, and a class of
`Hⁿ(X, 𝓕₃^•)` is lifted to a cochain `α₂` with a cocycle `α₁` over `d(α₂)`, on a suitable
covering, from the fact that Čech cohomology computes the cohomology of `𝓕₁^•` and `𝓕₂^•`
(`Stacks.Cech.Hypercohomology.exists_cechLift`).  Refinements then act only on cohomology,
where two refinement functions induce the same map, so no filtered colimit of complexes enters.

## Main results

* `Stacks.Cohomology.CechRefinement.exists_refinement_cochain_lift`: the refinement step of
  [Stacks, Tag 07MC] in Čech degree, on a Hausdorff quasi-compact space.
* `Stacks.Cohomology.CechRefinement.OpenCoverSet.comp_ne_comp_of_forall_index_ne`: two
  refinement functions disagreeing at every member through one point are equalized by no
  further refinement.
* `Stacks.Cohomology.CechRefinement.NotFiltered.not_isFiltered_openCoverSet_int`: the category
  of open coverings of `ℤ` with the discrete topology, and refinements, is not filtered.

## Implementation notes

The counterexample is on `ℤ` with its discrete topology, so that every subset is open and the
covering conditions are decided by `omega`.  Three members of the refining covering are needed
and not two: a member at which the two refinement functions disagree is contained in both
chosen members of the coarser covering, and two such members cannot cover a space on which the
coarser covering has two distinct members.

The two refinement functions are defined by a test on the members of the refining covering
rather than by a case split on a membership proof, because the members of a covering are
recorded as a *set* of opens, so a membership proof is a `Prop` and cannot be eliminated into
the choice of index.  Hence `Classical`.

## References

* [Stacks Project, Tag 07MC](https://stacks.math.columbia.edu/tag/07MC)
* [Stacks Project, Tag 09UW](https://stacks.math.columbia.edu/tag/09UW)
* [Stacks Project, Tag 09V2](https://stacks.math.columbia.edu/tag/09V2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace Stacks.Cohomology.CechRefinement

open OpenCoverSet

/-! ### The refinement step of Tag 07MC, in Čech degree -/

section Lift

variable {X : Type u} [TopologicalSpace X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- **The refinement step in the proof of [Stacks, Tag 07MC]**, for the Čech complex of a single
sheaf.  Let `X` be Hausdorff and quasi-compact and let `S : 𝓕₁ ⟶ 𝓕₂ ⟶ 𝓕₃` be a short exact
sequence of abelian sheaves on `X`.  A Čech cochain of `𝓕₃` for an open covering becomes, after
passing to a refinement of the covering, the image of a Čech cochain of `𝓕₂`.

This is the source's "after refining `𝒰` if necessary, we can find cochains `α₂`, resp. `β₂`
mapping to `α₃`, resp. `β₁`", which at a fixed covering is false: it needs presheaf-level
surjectivity of a sheaf epimorphism over the opens of the covering.

It is `Stacks.Cohomology.CechRefinement.exists_refinement_cochain_preimage_int` — the same
statement in its exactness form — applied to the short complex `𝓕₂ ⟶ 𝓕₃ ⟶ 0`, which is exact
exactly because `S.g` is an epimorphism.  So the Hausdorff quasi-compact hypothesis enters
through [Stacks, Tag 09UW], as it does there. -/
theorem exists_refinement_cochain_lift [T2Space X] [CompactSpace X]
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}))
    (hS : S.ShortExact) (U : OpenCoverSet X) (q : ℤ)
    (c : ((CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
      (hypercover U)).obj S.X₃).X q) :
    ∃ (W : OpenCoverSet X) (f : U ⟶ W)
      (b : ((CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
        (hypercover W)).obj S.X₂).X q),
      ((CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
        (hypercover W)).map S.g).f q b = ((refinementComplexIntNat f).app S.X₃).f q c :=
  exists_refinement_cochain_preimage_int.{v}
    (ShortComplex.mk S.g (0 : S.X₃ ⟶ S.X₃) (by simp))
    ((ShortComplex.exact_iff_epi _ rfl).2 hS.epi_g) U q c
    (by rw [Functor.map_zero]; simp)

end Lift

/-! ### Refinements of open coverings are not equalized -/

namespace OpenCoverSet

/-- **Two refinement functions that disagree at every member through a single point are equalized
by no further refinement.**  If the indices of `f g : U ⟶ V` differ at every member of `V`
containing `x`, then `f ≫ h ≠ g ≫ h` for every refinement `h : V ⟶ W`. This is the
`cocone_maps` condition of a filtered category failing for the category of open coverings: `W`
still has a member containing `x`, its chosen index is a member of `V` containing `x`, and the two
composites differ at it. -/
theorem comp_ne_comp_of_forall_index_ne {X : Type u} [TopologicalSpace X]
    {U V : OpenCoverSet X} (f g : U ⟶ V) (x : X)
    (hx : ∀ v : V.members, x ∈ (v.1 : Opens X) → f.index v ≠ g.index v)
    (W : OpenCoverSet X) (h : V ⟶ W) : f ≫ h ≠ g ≫ h := by
  intro he
  have hxW : x ∈ (⨆ w : W.members, (w.1 : Opens X)) := by
    rw [W.iSup_eq_top]; trivial
  obtain ⟨w, hw⟩ := Opens.mem_iSup.mp hxW
  refine hx (h.index w) (h.le_index w hw) ?_
  have := congrArg (fun k : U ⟶ W ↦ k.index w) he
  simpa using this

end OpenCoverSet

/-! ### A space whose coverings are not a filtered category -/

namespace NotFiltered

/-- The open `{n | n ≤ 1}` of `ℤ`, a member of the coarser covering. -/
def oA : Opens ℤ := ⟨{n : ℤ | n ≤ 1}, isOpen_discrete _⟩

/-- The open `{n | 1 ≤ n}` of `ℤ`, the other member of the coarser covering. -/
def oB : Opens ℤ := ⟨{n : ℤ | 1 ≤ n}, isOpen_discrete _⟩

/-- The open `{n | n ≤ 0}` of `ℤ`, the member of the refining covering that lies only in
`oA`. -/
def oC : Opens ℤ := ⟨{n : ℤ | n ≤ 0}, isOpen_discrete _⟩

/-- The open `{n | 2 ≤ n}` of `ℤ`, the member of the refining covering that lies only in
`oB`. -/
def oD : Opens ℤ := ⟨{n : ℤ | 2 ≤ n}, isOpen_discrete _⟩

/-- The open `{1}` of `ℤ`, the member of the refining covering that lies in both `oA` and `oB`
and is the only one containing `1`.  It is where the two refinement functions disagree. -/
def oE : Opens ℤ := ⟨{n : ℤ | n = 1}, isOpen_discrete _⟩

/-- The coarser covering `{oA, oB}` of `ℤ`. -/
def coarse : OpenCoverSet ℤ where
  members := {oA, oB}
  iSup_eq_top := by
    refine le_antisymm le_top fun x _ ↦ ?_
    rcases le_or_gt x 1 with h | h
    · exact Opens.mem_iSup.mpr ⟨⟨oA, by simp⟩, h⟩
    · exact Opens.mem_iSup.mpr ⟨⟨oB, by simp⟩, show (1:ℤ) ≤ x by omega⟩

/-- The refining covering `{oC, oD, oE}` of `ℤ`. -/
def fine : OpenCoverSet ℤ where
  members := {oC, oD, oE}
  iSup_eq_top := by
    refine le_antisymm le_top fun x _ ↦ ?_
    rcases lt_trichotomy x 1 with h | h | h
    · exact Opens.mem_iSup.mpr ⟨⟨oC, by simp⟩, show x ≤ (0:ℤ) by omega⟩
    · exact Opens.mem_iSup.mpr ⟨⟨oE, by simp⟩, h⟩
    · exact Opens.mem_iSup.mpr ⟨⟨oD, by simp⟩, show (2:ℤ) ≤ x by omega⟩

/-- `oC ⊆ oA`. -/
theorem oC_le_oA : oC ≤ oA := fun n hn ↦ show n ≤ (1:ℤ) by
  have : n ≤ (0:ℤ) := hn; omega

/-- `oE ⊆ oA`. -/
theorem oE_le_oA : oE ≤ oA := fun n hn ↦ show n ≤ (1:ℤ) by
  have : n = (1:ℤ) := hn; omega

/-- `oE ⊆ oB`. -/
theorem oE_le_oB : oE ≤ oB := fun n hn ↦ show (1:ℤ) ≤ n by
  have : n = (1:ℤ) := hn; omega

/-- `oD ⊆ oB`. -/
theorem oD_le_oB : oD ≤ oB := fun n hn ↦ show (1:ℤ) ≤ n by
  have : (2:ℤ) ≤ n := hn; omega

/-- The opens `oA` and `oB` are distinct. -/
theorem oA_ne_oB : oA ≠ oB := fun h ↦ by
  have h0 : (0:ℤ) ∈ oA := show (0:ℤ) ≤ 1 by omega
  rw [h] at h0
  have : (1:ℤ) ≤ (0:ℤ) := h0
  omega

/-- The members of the refining covering, enumerated. -/
theorem mem_fine (v : fine.members) : v.1 = oC ∨ v.1 = oD ∨ v.1 = oE := by
  have := v.2
  simpa [fine] using this

open scoped Classical in
/-- One refinement function: send a member to `oA` when it lies in `oA`, else to `oB`. -/
def firstHom : coarse ⟶ fine where
  index v := if v.1 ≤ oA then ⟨oA, by simp [coarse]⟩ else ⟨oB, by simp [coarse]⟩
  le_index v := by
    by_cases h : v.1 ≤ oA
    · simp [h]
    · rcases mem_fine v with hv | hv | hv
      · exact absurd (hv ▸ oC_le_oA) h
      · simp only [ite_eq_right h]; exact hv ▸ oD_le_oB
      · exact absurd (hv ▸ oE_le_oA) h

open scoped Classical in
/-- The other refinement function: send a member to `oB` when it lies in `oB`, else to `oA`.
It differs from `firstHom` exactly at `oE`, which lies in both. -/
def secondHom : coarse ⟶ fine where
  index v := if v.1 ≤ oB then ⟨oB, by simp [coarse]⟩ else ⟨oA, by simp [coarse]⟩
  le_index v := by
    by_cases h : v.1 ≤ oB
    · simp [h]
    · rcases mem_fine v with hv | hv | hv
      · simp only [ite_eq_right h]; exact hv ▸ oC_le_oA
      · exact absurd (hv ▸ oD_le_oB) h
      · exact absurd (hv ▸ oE_le_oB) h

open scoped Classical in
/-- The two refinement functions disagree at every member of the refining covering that
contains `1`, there being only one such member. -/
theorem index_ne (v : fine.members) (h1 : (1 : ℤ) ∈ (v.1 : Opens ℤ)) :
    firstHom.index v ≠ secondHom.index v := by
  have hv : v.1 = oE := by
    rcases mem_fine v with hv | hv | hv
    · simp [hv, oC] at h1
    · simp [hv, oD] at h1
    · exact hv
  simp [firstHom, secondHom, hv, oE_le_oA, oE_le_oB, oA_ne_oB]

/-- **Non-vacuity of the configuration**: the two refinement functions genuinely differ, at the
member `{1}` of the refining covering.  Without this the hypothesis of
`Stacks.Cohomology.CechRefinement.OpenCoverSet.comp_ne_comp_of_forall_index_ne` could be
satisfied by two equal morphisms and the refutation below would prove nothing. -/
theorem index_ne_oE :
    firstHom.index ⟨oE, by simp [fine]⟩ ≠ secondHom.index ⟨oE, by simp [fine]⟩ :=
  index_ne _ (show (1:ℤ) = 1 from rfl)

/-- **The category of open coverings of a space, with refinements, is not filtered.**  Here for
`ℤ` with the discrete topology: the coverings `{{n | n ≤ 1}, {n | 1 ≤ n}}` and
`{{n | n ≤ 0}, {n | 2 ≤ n}, {1}}` carry two refinement functions that differ at `{1}`, and no
further refinement equalizes them, because every covering has a member containing `1` and `{1}`
is the only member of the finer covering that contains `1`.

So exactness of a colimit of Čech complexes over all coverings cannot be had from exactness of
filtered colimits, and a colimit of complexes over this category has no reason to compute the
colimit of their cohomology.  Only `cocone_maps` fails; `cocone_objs` is
`Stacks.Cohomology.CechRefinement.OpenCoverSet.exists_common_refinement`. -/
theorem not_isFiltered_openCoverSet_int : ¬ IsFiltered (OpenCoverSet ℤ) := by
  intro _
  obtain ⟨W, h, hh⟩ := IsFilteredOrEmpty.cocone_maps firstHom secondHom
  exact OpenCoverSet.comp_ne_comp_of_forall_index_ne firstHom secondHom 1
    (fun v hv ↦ index_ne v hv) W h hh

end NotFiltered

end Stacks.Cohomology.CechRefinement

end
