module

public import Mathlib.Algebra.Category.Grp.Zero
public import StacksCore.Algebra.Homology.TotalComplex
public import StacksFrontier.Topology.Compact.RefineCover
public import StacksFrontier.Topology.Sheaves.Cohomology.CechRefinements.DegreeOneIsomorphism
import StacksCore.Tactic.StacksAttribute

/-!
# Čech cohomology surjects onto sheaf cohomology on a Hausdorff quasi-compact space

Let `X` be a Hausdorff quasi-compact topological space and `F` an abelian sheaf on `X`.  Stacks
09UZ produces the canonical comparison

`Ȟ^n(X, F) = colim_𝒰 Ȟ^n(𝒰, F) ⟶ H^n(X, F)`

from the Čech cohomology of `X`, the colimit over all open coverings of the Čech cohomology of
the covering, to sheaf cohomology.  This file proves the surjectivity half of Stacks 09V2: that
comparison is surjective in every nonnegative degree.  In degree at most one the comparison is
moreover injective, by Stacks 09V1, which is
`Stacks.Cohomology.CechRefinement.isIso_colimitToCohomology_one`.

## The staircase

Fix an injective resolution `F ⟶ J^•` and let `K` be the Čech bicomplex of `J^•` for a covering
`𝒰`, with the resolution degree `p` first and the Čech degree `q` second.  Stacks 03AX computes
sheaf cohomology as the cohomology of the total complex `Tot K`, through the degreewise
augmentation `α : Γ(J^•) ⟶ Tot K`, and the comparison from Čech cohomology is induced by
`β : Č^•(𝒰, F) ⟶ Tot K`, the zeroth column.

A sheaf cohomology class in degree `n` is represented by a global section of `J^n` killed by the
differential of the resolution; its augmentation is a cochain in bidegree `(n, 0)` which both
differentials of the bicomplex kill.  The class is then walked down the staircase

`(n, 0) → (n - 1, 1) → ⋯ → (0, n)`,

one step at a time, by `exists_refinement_column_shift`: a cochain in bidegree `(p + 1, q)` which
both differentials kill is, locally on each iterated intersection of the covering, the image
under the differential of the resolution of a cochain in bidegree `(p, q)`, because `J^•` is
exact in positive degrees; Stacks 09UW — this is where `X` being Hausdorff and quasi-compact is
used — refines the covering so that all those local primitives are defined on the iterated
intersections of a *single* covering, and the total differential of the resulting primitive
exhibits the original cochain as congruent, modulo a boundary of the total complex, to the Čech
differential of the primitive, which sits in bidegree `(p, q + 1)`.

So the covering is refined once per step, `n` times in all — which is why the statement is about
the colimit over all coverings and not about a fixed one.  At the foot of the staircase the
cochain sits in the zeroth column, where left exactness of the Čech complex functor identifies
`F` with `ker(J^0 → J^1)` in every Čech degree, so the cochain comes from `Č^n(𝒰, F)`; it is a
cocycle because its class in the total complex is one, and its image under `H^n(β)` is the given
class.

## Main results

* `Stacks.Cohomology.CechRefinement.exists_cechCohomologyToCohomology_preimage_of_nonneg`:
  Stacks 09V2, surjectivity — every sheaf cohomology class in nonnegative degree comes from the
  Čech cohomology of some open covering.
* `Stacks.Cohomology.CechRefinement.surjective_colimitToCohomology_of_nonneg`: the same
  statement for the comparison out of the colimit of Stacks 09UZ.
* `Stacks.Cohomology.CechRefinement.exists_refinement_cochain_preimage_int`: the refinement
  step, where Stacks 09UW is used — a Čech cochain of the middle term of an exact sequence of
  abelian sheaves which dies in the right-hand term becomes, after passing to a refinement of
  the covering, the image of a Čech cochain of the left-hand term.

## Implementation notes

Stacks 09UW is a statement about intersections of members of a covering of a compact Hausdorff
space, while the Čech complex is built from the iterated fibre products of the covering taken in
the slice category over the whole space.  `cechProductLeft_eq_iInf` identifies the two: a product
in the poset `Opens X` is an infimum, so the fibre product of a tuple of members is their
infimum, and `TopologicalSpace.Opens.coe_iInf` turns a finite infimum of opens into the
intersection of their carriers.

The index type that Stacks 09UW produces for the covering of an iterated intersection is allowed
to be empty, and the refinement it returns may well have tuples whose intersection is empty.
Both are handled by `subsingleton_obj_bot`: an abelian sheaf has no nonzero sections over the
empty open, since the empty sieve covers it, so over such a tuple there is nothing to lift.

The element-level identities about the total complex are stated for a *variable* double complex
(`total_d_ιTotal_apply`, `total_map_ιTotal_apply`, `exists_ιTotal_eq_add_total_d`) and only then
instantiated at the Čech bicomplex.  Stated directly at the Čech bicomplex they are the same
identities, but elaborating them there means unifying against the unfolding of the bicomplex and
is prohibitively slow.

## Why this is untagged

Stacks 09V2 asserts that the comparison `Ȟ^n(X, F) → H^n(X, F)` of Stacks 09UZ is an
**isomorphism** for all `n` — a single assertion.  What is proved here is its **surjectivity**
half, so the covering set of 09V2 is not complete in this file and no `@[stacks 09V2]`
attribute is attached: a tag lands only with its full covering set.  The full isomorphism is
`Stacks.Cohomology.CechRefinement.isIso_colimitToCohomology`, in
`StacksFrontier.Topology.Sheaves.Cohomology.CechRefinements.HausdorffQuasiCompactIsomorphism`,
which carries the tag and reuses the refinement step proved here.

## References


* [Stacks Project, Tag 09V2](https://stacks.math.columbia.edu/tag/09V2)
* [Stacks Project, Tag 09UW](https://stacks.math.columbia.edu/tag/09UW)
* [Stacks Project, Tag 09UZ](https://stacks.math.columbia.edu/tag/09UZ)
* [Stacks Project, Tag 03AX](https://stacks.math.columbia.edu/tag/03AX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe t w v u

namespace Stacks.Cohomology.CechRefinement

open OpenCoverSet

/-! ### Infima of opens and the iterated fibre products of a covering -/

section Opens

variable {X : Type u} [TopologicalSpace X]

/-- The iterated fibre product, over the whole space, of the members of an open covering
indexed by a tuple is their infimum.  This is the identification along which Stacks 09UW, a
statement about intersections of members of a covering, is applied to the Čech complex. -/
private theorem cechProductLeft_eq_iInf {n : ℕ} (U : OpenCoverSet X)
    (k : Fin n → U.members) :
    (∏ᶜ (fun j ↦ Over.mk ((hypercover U).f (k j))) : Over (⊤ : Opens X)).left =
      ⨅ j, (k j).1 := by
  refine le_antisymm (le_iInf fun j ↦
    leOfHom (Pi.π (fun j ↦ Over.mk ((hypercover U).f (k j))) j).left) ?_
  have h : (Over.mk (homOfLE (le_top : (⨅ j, (k j).1) ≤ ⊤)) : Over (⊤ : Opens X)) ⟶
      ∏ᶜ (fun j ↦ Over.mk ((hypercover U).f (k j))) :=
    Pi.lift fun j ↦ Over.homMk (homOfLE (iInf_le (fun j ↦ (k j).1) j))
      (Subsingleton.elim _ _)
  exact leOfHom h.left

/-- An abelian sheaf has no nonzero sections over the empty open: the empty sieve covers the
empty open. -/
private theorem subsingleton_obj_bot
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) :
    Subsingleton (G.obj.obj (op (⊥ : Opens X))) :=
  AddCommGrpCat.subsingleton_of_isZero
    (Sheaf.isTerminalOfBotCover G (⊥ : Opens X)
      ((Opens.mem_grothendieckTopology (U := (⊥ : Opens X)) (S := ⊥)).2 (by simp))).isZero

end Opens

/-! ### Local lifting along an exact sequence of abelian sheaves -/

section LocalLifting

variable {X : Type u} [TopologicalSpace X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- A section of the middle term of an exact sequence of abelian sheaves over an open `W` which
dies in the right-hand term is locally in the image of the left-hand term: there is a family of
opens covering `W` on each of which it lifts.  This is the degree-zero input of Stacks 09V2: the
cochain to be lifted is lifted member by member of the covering before Stacks 09UW is applied. -/
private theorem exists_cover_local_preimage
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}))
    (hS : S.Exact) (W : Opens X) (s : S.X₂.obj.obj (op W))
    (hs : S.g.hom.app (op W) s = 0) :
    ∃ P : Set (Opens X), (⨆ V : P, (V : Opens X)) = W ∧
      ∀ V ∈ P, ∃ (h : V ≤ W) (t : S.X₁.obj.obj (op V)),
        S.f.hom.app (op V) t = S.X₂.obj.map (homOfLE h).op s := by
  classical
  have hR : (ShortComplex.mk S.iCycles S.g S.iCycles_g).Exact :=
    ShortComplex.exact_of_f_is_kernel _ S.cyclesIsKernel
  have he : PreservesFiniteLimits ((sheafSections (Opens.grothendieckTopology X)
      AddCommGrpCat.{max u v}).obj (op W)) := by
    show PreservesFiniteLimits (sheafToPresheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{max u v} ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{max u v}).obj (op W))
    infer_instance
  have hRe := hR.map_of_mono_of_preservesKernel
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj (op W))
    inferInstance inferInstance
  obtain ⟨t, ht⟩ : ∃ t : S.cycles.obj.obj (op W), S.iCycles.hom.app (op W) t = s :=
    (ShortComplex.ab_exact_iff _).mp hRe s hs
  have hepi : Epi S.toCycles := hS.epi_toCycles
  have hls : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) S.toCycles.hom :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max u v} S.toCycles).mpr inferInstance
  refine ⟨{V | ∃ (h : V ≤ W) (t : S.X₁.obj.obj (op V)),
    S.f.hom.app (op V) t = S.X₂.obj.map (homOfLE h).op s}, ?_, fun _ hV ↦ hV⟩
  refine le_antisymm (iSup_le fun V ↦ V.2.1) fun x hx ↦ ?_
  obtain ⟨V, i, ⟨wit, hwit⟩, hxV⟩ := hls.imageSieve_mem t x hx
  have hVW : V ≤ W := leOfHom i
  have hV : ∃ (h : V ≤ W) (t' : S.X₁.obj.obj (op V)),
      S.f.hom.app (op V) t' = S.X₂.obj.map (homOfLE h).op s := by
    refine ⟨hVW, wit, ?_⟩
    have h := congrArg (fun z ↦ S.iCycles.hom.app (op V) z) hwit
    change (S.toCycles.hom.app (op V) ≫ S.iCycles.hom.app (op V)) wit =
      (S.cycles.obj.map i.op ≫ S.iCycles.hom.app (op V)) t at h
    rw [S.iCycles.hom.naturality] at h
    have hcomp : S.toCycles.hom.app (op V) ≫ S.iCycles.hom.app (op V) =
        S.f.hom.app (op V) := congrArg (fun g ↦ g.hom.app (op V)) S.toCycles_i
    rw [hcomp] at h
    change S.f.hom.app (op V) wit = S.X₂.obj.map i.op (S.iCycles.hom.app (op W) t) at h
    rw [ht, Subsingleton.elim i (homOfLE hVW)] at h
    exact h
  exact Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hxV⟩

/-- **Stacks 09V2**, the refinement step.  Let `X` be Hausdorff and quasi-compact and let
`S : F ⟶ G ⟶ H` be an exact sequence of abelian sheaves.  A Čech cochain of `G` for an open
covering whose image in `H` vanishes becomes, after passing to a refinement of the covering, the
image of a Čech cochain of `F`.

Each component of the cochain lifts locally, by `exists_cover_local_preimage`; Stacks 09UW is
what produces a *single* refinement of the covering on whose iterated intersections all those
local lifts are simultaneously defined. -/
private theorem exists_refinement_cochain_preimage [T2Space X] [CompactSpace X]
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}))
    (hS : S.Exact) (U : OpenCoverSet X) (m : ℕ)
    (c : (CechSite.cechComplex (hypercover U) S.X₂.obj).X m)
    (hc : ((CechSite.cechComplexFunctor (hypercover U)).map S.g.hom).f m c = 0) :
    ∃ (W : OpenCoverSet X) (f : U ⟶ W)
      (b : (CechSite.cechComplex (hypercover W) S.X₁.obj).X m),
      ((CechSite.cechComplexFunctor (hypercover W)).map S.f.hom).f m b =
        (refinementCochainMap f S.X₂.obj).f m c := by
  classical
  -- The open attached to a tuple of members of `U`, and the corresponding component of `c`.
  set Wo : (Fin (m + 1) → U.members) → Opens X := fun i ↦
    (∏ᶜ (fun j ↦ Over.mk ((hypercover U).f (i j))) : Over (⊤ : Opens X)).left with hWo
  set ci : ∀ i : Fin (m + 1) → U.members, S.X₂.obj.obj (op (Wo i)) := fun i ↦
    Pi.π (CechSite.cochainFactor (hypercover U) S.X₂.obj m) i c with hci
  have hWoinf : ∀ i, Wo i = ⨅ a, (i a).1 := fun i ↦ cechProductLeft_eq_iInf U i
  -- Each component dies in `H`, hence lifts locally to `F`.
  have hcomp : ∀ i, S.g.hom.app (op (Wo i)) (ci i) = 0 := by
    intro i
    have h := CechSite.cechComplexFunctor_map_f_π_apply.{max u v} (hypercover U) S.g.hom m i c
    rw [hc] at h
    exact h.symm.trans (map_zero _)
  choose P hPsup hPlift using fun i ↦ exists_cover_local_preimage S hS (Wo i) (ci i) (hcomp i)
  -- The data for Stacks 09UW: the covering of `X`, and for each tuple a covering of the
  -- intersection by opens over which the component lifts (plus a redundant empty member, so
  -- that the index type is nonempty).
  have hUcov : ⋃ i : U.members, ((i.1 : Opens X) : Set X) = Set.univ := by
    have h := congrArg (fun V : Opens X ↦ (V : Set X)) U.iSup_eq_top
    rwa [Opens.coe_iSup, Opens.coe_top] at h
  set Wset : ∀ i : Fin (m + 1) → U.members, Option (P i) → Set X := fun _ k ↦
    k.elim ∅ (fun V ↦ ((V.1 : Opens X) : Set X)) with hWset
  have hWsetopen : ∀ i k, IsOpen (Wset i k) := by
    intro i k
    cases k with
    | none => exact isOpen_empty
    | some V => exact (V.1 : Opens X).isOpen
  have hWsetcov : ∀ i, (⋂ a, ((i a).1 : Opens X) : Set X) = ⋃ k, Wset i k := by
    intro i
    have h1 : (⋂ a, (((i a).1 : Opens X) : Set X)) = ((Wo i : Opens X) : Set X) := by
      rw [hWoinf i, Opens.coe_iInf]
    have h2 : ((Wo i : Opens X) : Set X) = ⋃ V : P i, ((V.1 : Opens X) : Set X) := by
      rw [← hPsup i, Opens.coe_iSup]
    refine h1.trans (h2.trans (Set.Subset.antisymm ?_ ?_))
    · exact Set.iUnion_subset fun V ↦ Set.subset_iUnion (fun k ↦ Wset i k) (some V)
    · refine Set.iUnion_subset fun k ↦ ?_
      cases k with
      | none => exact Set.empty_subset _
      | some V => exact Set.subset_iUnion (fun V : P i ↦ ((V.1 : Opens X) : Set X)) V
  obtain ⟨Jt, Vset, αr, hVopen, hVcov, hVclos, hVint⟩ :=
    exists_cover_closure_subset_and_refines (fun i : U.members ↦ ((i.1 : Opens X) : Set X))
      (fun i ↦ (i.1 : Opens X).isOpen) hUcov m Wset hWsetopen hWsetcov
  -- The refinement, as an open covering of `X` and a morphism of coverings.
  set Vo : Jt → Opens X := fun j ↦ ⟨Vset j, hVopen j⟩ with hVo
  have hsup : (⨆ M : Set.range Vo, (M : Opens X)) = ⊤ := by
    refine le_antisymm le_top fun x _ ↦ ?_
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hVcov ▸ Set.mem_univ x)
    exact Opens.mem_iSup.mpr ⟨⟨Vo j, ⟨j, rfl⟩⟩, hj⟩
  set Wc : OpenCoverSet X := ⟨Set.range Vo, hsup⟩ with hWc
  choose jsel hjsel using fun M : Wc.members ↦ Set.mem_range.1 M.2
  have hle : ∀ M : Wc.members, M.1 ≤ (αr (jsel M)).1 := by
    intro M
    refine fun x hx ↦ ?_
    have hx' : x ∈ Vset (jsel M) := by rw [← hjsel M] at hx; exact hx
    exact hVclos (jsel M) (subset_closure hx')
  set fr : U ⟶ Wc := ⟨fun M ↦ αr (jsel M), hle⟩ with hfr
  -- The open attached to a tuple of members of the refinement, and its carrier.
  set Vp : (Fin (m + 1) → Wc.members) → Opens X := fun k ↦
    (∏ᶜ (fun j ↦ Over.mk ((hypercover Wc).f (k j))) : Over (⊤ : Opens X)).left with hVp
  have hVpcar : ∀ k, ((Vp k : Opens X) : Set X) = ⋂ a, Vset (jsel (k a)) := by
    intro k
    have h1 : Vp k = ⨅ a, (k a).1 := cechProductLeft_eq_iInf Wc k
    rw [h1, Opens.coe_iInf]
    exact Set.iInter_congr fun a ↦
      congrArg (fun V : Opens X ↦ (V : Set X)) (hjsel (k a)).symm
  -- For every tuple of the refinement, a lift of the corresponding component of `c`.
  have key : ∀ k : Fin (m + 1) → Wc.members, ∃ bk : S.X₁.obj.obj (op (Vp k)),
      S.f.hom.app (op (Vp k)) bk =
        S.X₂.obj.map (CechSite.cechProductMap (hypercover Wc) (hypercover U)
          (homOver fr) m k).op (ci (fr.index ∘ k)) := by
    intro k
    by_cases hbot : ((Vp k : Opens X) : Set X) = ∅
    · have hsub : Subsingleton (S.X₂.obj.obj (op (Vp k))) := by
        rw [show Vp k = ⊥ from Opens.ext hbot]; exact subsingleton_obj_bot S.X₂
      exact ⟨0, by rw [map_zero]; exact hsub.elim _ _⟩
    · rcases hVint (fun a ↦ jsel (k a)) with hempty | ⟨κ, hκ⟩
      · exact absurd ((hVpcar k).trans hempty) hbot
      cases κ with
      | none => exact absurd (Set.subset_eq_empty ((hVpcar k).le.trans hκ) rfl) hbot
      | some V₀ =>
        obtain ⟨hV₀W, t, ht⟩ := hPlift (fun a ↦ αr (jsel (k a))) V₀.1 V₀.2
        have hVple : Vp k ≤ (V₀.1 : Opens X) := fun x hx ↦ hκ ((hVpcar k) ▸ hx)
        refine ⟨S.X₁.obj.map (homOfLE hVple).op t, ?_⟩
        refine (app_map_op S.f.hom (homOfLE hVple) t).symm.trans ?_
        rw [ht]
        exact map_op_comp_apply_eq S.X₂.obj _ _ _ _
  choose bk hbk using key
  obtain ⟨b, hbπ⟩ : ∃ b : (CechSite.cechComplex (hypercover Wc) S.X₁.obj).X m,
      ∀ k, Pi.π (CechSite.cochainFactor (hypercover Wc) S.X₁.obj m) k b = bk k :=
    ⟨(CechSite.productAddEquiv (CechSite.cochainFactor (hypercover Wc) S.X₁.obj m)).symm bk,
      fun k ↦ congrFun ((CechSite.productAddEquiv
        (CechSite.cochainFactor (hypercover Wc) S.X₁.obj m)).apply_symm_apply bk) k⟩
  refine ⟨Wc, fr, b, ?_⟩
  apply (CechSite.productAddEquiv (CechSite.cochainFactor (hypercover Wc) S.X₂.obj m)).injective
  ext k
  show Pi.π (CechSite.cochainFactor (hypercover Wc) S.X₂.obj m) k
      (((CechSite.cechComplexFunctor (hypercover Wc)).map S.f.hom).f m b) =
    Pi.π (CechSite.cochainFactor (hypercover Wc) S.X₂.obj m) k
      ((refinementCochainMap fr S.X₂.obj).f m c)
  rw [CechSite.cechComplexFunctor_map_f_π_apply.{max u v} (hypercover Wc) S.f.hom m k b, hbπ,
    refinementCochainMap_f_π_apply fr S.X₂.obj m k c]
  exact hbk k

end LocalLifting

/-! ### Passing to the integer grading -/

section IntegerGrading

variable {X : Type u} [TopologicalSpace X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  {U V W : OpenCoverSet X}
  {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}}

/-- The degree of the integer-graded Čech complex at the image of a natural number. -/
private theorem embeddingUpNat_f (m : ℕ) : ComplexShape.embeddingUpNat.f m = (m : ℤ) := rfl

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- In the degree of a natural number, the map of integer-graded Čech complexes induced by a
morphism of abelian sheaves is the corresponding map of natural-number-graded Čech
complexes. -/
private theorem cechComplexIntFunctor_map_f (φ : F ⟶ G) (m : ℕ) :
    ((CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
        (hypercover U)).map φ).f (m : ℤ) =
      (CechSite.cechIntXIsoPre.{v} (hypercover U) F.obj m m (embeddingUpNat_f m)).hom ≫
        ((CechSite.cechComplexFunctor (hypercover U)).map φ.hom).f m ≫
        (CechSite.cechIntXIsoPre.{v} (hypercover U) G.obj m m (embeddingUpNat_f m)).inv :=
  HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (embeddingUpNat_f m)

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- In the degree of a natural number, the refinement map of integer-graded Čech complexes is
the corresponding refinement map of natural-number-graded Čech complexes. -/
private theorem refinementComplexIntNat_app_f (f : U ⟶ V) (m : ℕ) :
    ((refinementComplexIntNat f).app G).f (m : ℤ) =
      (CechSite.cechIntXIsoPre.{v} (hypercover U) G.obj m m (embeddingUpNat_f m)).hom ≫
        (refinementCochainMap f G.obj).f m ≫
        (CechSite.cechIntXIsoPre.{v} (hypercover V) G.obj m m (embeddingUpNat_f m)).inv := by
  rw [refinementComplexIntNat_app]
  exact HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (embeddingUpNat_f m)

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- The identity refinement induces the identity map of integer-graded Čech complexes. -/
theorem refinementComplexIntNat_app_id (U : OpenCoverSet X)
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) :
    (refinementComplexIntNat (𝟙 U)).app G = 𝟙 _ := by
  rw [refinementComplexIntNat_app, refinementCochainMap_id]
  exact HomologicalComplex.extendMap_id _ _

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- The refinement maps of integer-graded Čech complexes compose contravariantly. -/
theorem refinementComplexIntNat_app_comp (f : U ⟶ V) (g : V ⟶ W)
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) :
    (refinementComplexIntNat f).app G ≫ (refinementComplexIntNat g).app G =
      (refinementComplexIntNat (f ≫ g)).app G := by
  have h := congrArg (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max u v}).map
    (refinementCochainMap_comp f g G.obj)
  rw [Functor.map_comp] at h
  rw [refinementComplexIntNat_app, refinementComplexIntNat_app, refinementComplexIntNat_app]
  exact h

/-- **Stacks 09V2**, the refinement step in the integer grading: a cochain of the integer-graded
Čech complex of the middle term of an exact sequence of abelian sheaves which dies in the
right-hand term becomes, after a refinement, the image of a cochain of the left-hand term. -/
theorem exists_refinement_cochain_preimage_int [T2Space X] [CompactSpace X]
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}))
    (hS : S.Exact) (U : OpenCoverSet X) (q : ℤ)
    (c : ((CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
      (hypercover U)).obj S.X₂).X q)
    (hc : ((CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
      (hypercover U)).map S.g).f q c = 0) :
    ∃ (W : OpenCoverSet X) (f : U ⟶ W)
      (b : ((CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
        (hypercover W)).obj S.X₁).X q),
      ((CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
        (hypercover W)).map S.f).f q b = ((refinementComplexIntNat f).app S.X₂).f q c := by
  rcases lt_or_ge q 0 with hq | hq
  · have hzero : Subsingleton (((CechSite.cechComplexIntFunctor.{v}
        (Opens.grothendieckTopology X) (hypercover U)).obj S.X₂).X q) :=
      AddCommGrpCat.subsingleton_of_isZero
        (CechSite.isZero_cechComplexIntFunctorPre_X.{v} (hypercover U) S.X₂.obj q hq)
    exact ⟨U, 𝟙 U, 0, Subsingleton.elim _ _⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℤ) = q := ⟨q.toNat, by omega⟩
  obtain ⟨c', hc'⟩ : ∃ c', (CechSite.cechIntXIsoPre.{v} (hypercover U) S.X₂.obj m m
      (embeddingUpNat_f m)).hom c = c' := ⟨_, rfl⟩
  have hc'0 : ((CechSite.cechComplexFunctor (hypercover U)).map S.g.hom).f m c' = 0 := by
    have h := ConcreteCategory.congr_hom (cechComplexIntFunctor_map_f.{v} (U := U) S.g m) c
    rw [hc] at h
    apply (ConcreteCategory.bijective_of_isIso
      (CechSite.cechIntXIsoPre.{v} (hypercover U) S.X₃.obj m m (embeddingUpNat_f m)).inv).1
    rw [map_zero]
    simp only [ConcreteCategory.comp_apply, hc'] at h
    exact h.symm
  obtain ⟨W, f, b', hb'⟩ := exists_refinement_cochain_preimage S hS U m c' hc'0
  refine ⟨W, f, (CechSite.cechIntXIsoPre.{v} (hypercover W) S.X₁.obj m m
    (embeddingUpNat_f m)).inv b', ?_⟩
  rw [ConcreteCategory.congr_hom (cechComplexIntFunctor_map_f.{v} (U := W) S.f m),
    ConcreteCategory.congr_hom (refinementComplexIntNat_app_f.{v} f (G := S.X₂) m)]
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply, hc', hb']

end IntegerGrading

/-! ### Reading off a summand of a total complex -/

section Total

variable {A : Type w} [Category.{t} A] [Preadditive A]
  (K : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [K.HasTotal (ComplexShape.up ℤ)]

/-- The inclusion of a summand of a total complex is a monomorphism. -/
private theorem mono_ιTotal (p q n : ℤ) (h : p + q = n) :
    Mono (K.ιTotal (ComplexShape.up ℤ) p q n h) :=
  mono_of_mono_fac (ι_totalProjection K p q n h)

end Total

/-! ### Lifting a homology class along a map of complexes -/

section Preimage

/-- A unit of `ℤ` acting on a morphism of abelian groups acts on its values. -/
private theorem units_smul_apply {A B : AddCommGrpCat.{w}} (ε : ℤˣ) (f : A ⟶ B) (x : A) :
    (ε • f) x = (ε : ℤ) • f x := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp

/-- A map of cochain complexes of abelian groups commutes with the differential, on
elements. -/
private theorem hom_f_d_apply {S T : CochainComplex AddCommGrpCat.{w} ℤ} (ψ : S ⟶ T) (i j : ℤ)
    (x : S.X i) : ψ.f j (S.d i j x) = T.d i j (ψ.f i x) := by
  rw [← ConcreteCategory.comp_apply, ← ψ.comm i j, ConcreteCategory.comp_apply]

/-- Two successive differentials of a cochain complex of abelian groups kill every element. -/
private theorem d_d_apply (S : CochainComplex AddCommGrpCat.{w} ℤ) (i j k : ℤ) (x : S.X i) :
    S.d j k (S.d i j x) = 0 := by
  rw [← ConcreteCategory.comp_apply, S.d_comp_d]
  simp

variable (K L : HomologicalComplex₂ AddCommGrpCat.{w} (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]

/-- The differential of a total complex, read on one summand, on elements: it is the first
differential plus the second with the sign of the first degree. -/
private theorem total_d_ιTotal_apply (p q n : ℤ) (h : p + q = n) (b : (K.X p).X q) :
    (K.total (ComplexShape.up ℤ)).d n (n + 1) (K.ιTotal (ComplexShape.up ℤ) p q n h b) =
      K.ιTotal (ComplexShape.up ℤ) (p + 1) q (n + 1)
            (by simp only [ComplexShape.π_def]; omega) ((K.d p (p + 1)).f q b) +
        (p.negOnePow : ℤ) • K.ιTotal (ComplexShape.up ℤ) p (q + 1) (n + 1)
            (by simp only [ComplexShape.π_def]; omega) ((K.X p).d q (q + 1) b) := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex₂.ιTotal_d_up_ℤ]
  simp only [AddCommGrpCat.hom_add, AddMonoidHom.add_apply, ConcreteCategory.comp_apply,
    units_smul_apply]

/-- A map of double complexes, read on one summand of the total complex, on elements. -/
private theorem total_map_ιTotal_apply (φ : K ⟶ L) (p q n : ℤ) (h : p + q = n)
    (x : (K.X p).X q) :
    (HomologicalComplex₂.total.map φ (ComplexShape.up ℤ)).f n
        (K.ιTotal (ComplexShape.up ℤ) p q n h x) =
      L.ιTotal (ComplexShape.up ℤ) p q n h ((φ.f p).f q x) := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex₂.ιTotal_map,
    ConcreteCategory.comp_apply]

/-- **Stacks 09V2**, one step of the staircase, as a statement about an abstract double
complex.  A summand of the total complex in bidegree `(p + 1, q)` which is the image, under the
first differential, of an element in bidegree `(p, q)` whose Čech differential the first
differential kills agrees, up to a boundary of the total complex, with a summand in bidegree
`(p, q + 1)` which both differentials kill. -/
private theorem exists_ιTotal_eq_add_total_d (p q n : ℤ) (h : p + q = n) (b : (K.X p).X q)
    (hb : (K.d p (p + 1)).f (q + 1) ((K.X p).d q (q + 1) b) = 0) :
    ∃ c : (K.X p).X (q + 1), (K.d p (p + 1)).f (q + 1) c = 0 ∧
      (K.X p).d (q + 1) (q + 1 + 1) c = 0 ∧
      K.ιTotal (ComplexShape.up ℤ) (p + 1) q (n + 1)
            (by simp only [ComplexShape.π_def]; omega) ((K.d p (p + 1)).f q b) =
        K.ιTotal (ComplexShape.up ℤ) p (q + 1) (n + 1)
            (by simp only [ComplexShape.π_def]; omega) c +
          (K.total (ComplexShape.up ℤ)).d n (n + 1)
            (K.ιTotal (ComplexShape.up ℤ) p q n h b) := by
  refine ⟨-((p.negOnePow : ℤ) • ((K.X p).d q (q + 1) b)), ?_, ?_, ?_⟩
  · rw [map_neg, map_zsmul, hb, smul_zero, neg_zero]
  · rw [map_neg, map_zsmul, d_d_apply, smul_zero, neg_zero]
  · rw [map_neg, map_zsmul, total_d_ιTotal_apply K p q n h b]
    abel

end Preimage

/-! ### The staircase -/

section Staircase

variable {X : Type u} [TopologicalSpace X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})]
  {G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}}

/-- The Čech bicomplex of an injective resolution of an abelian sheaf, for a given open
covering: resolution degree first, Čech degree second. -/
public abbrev resolutionBicomplex (U : OpenCoverSet X) (J : InjectiveResolution G) :
    HomologicalComplex₂ AddCommGrpCat.{max u v} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  CechSite.cechBicomplex.{v} (Opens.grothendieckTopology X) (hypercover U) J.cochainComplex

/-- The total complex of the Čech bicomplex of an injective resolution. -/
public abbrev resolutionTotal (U : OpenCoverSet X) (J : InjectiveResolution G) :
    CochainComplex AddCommGrpCat.{max u v} ℤ :=
  (resolutionBicomplex U J).total (ComplexShape.up ℤ)

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})] in
/-- The map from the Čech complex of the sheaf to the total Čech complex of an injective
resolution lands, degreewise, in the zeroth column. -/
public theorem cechToTotal_f (U : OpenCoverSet X) (J : InjectiveResolution G) (p : ℤ) :
    (CechSite.cechToTotal.{v} (Opens.grothendieckTopology X) (hypercover U) G J).f p =
      ((CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
        (hypercover U)).map J.inclusionZero).f p ≫
        (resolutionBicomplex U J).ιTotal (ComplexShape.up ℤ) 0 p p (by simp) := rfl

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})] in
/-- The first differential of the Čech bicomplex is the Čech complex of the differential of the
resolution. -/
private theorem resolutionBicomplex_d (U : OpenCoverSet X) (J : InjectiveResolution G)
    (p p' : ℤ) :
    (resolutionBicomplex U J).d p p' =
      (CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X) (hypercover U)).map
        (J.cochainComplex.d p p') :=
  Functor.mapHomologicalComplex_obj_d _ _ _ _ _

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})] in
/-- The augmentation of a global section is a Čech cocycle. -/
private theorem cechAugmentationInt_comp_cech_d (U : OpenCoverSet X)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})
    (s : ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj
      (op (⊤ : Opens X))).obj F) :
    ((CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
          (hypercover U)).obj F).d 0 1
        (CechSite.cechAugmentationInt.{v} (Opens.grothendieckTopology X) (hypercover U) F s)
      = 0 :=
  ConcreteCategory.congr_hom
    (CechSite.cechAugmentationIntPre_comp_d.{v} (hypercover U) F.obj) s

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})] in
/-- The augmentation of a global section killed by the differential of the resolution is killed
by the first differential of the Čech bicomplex. -/
private theorem cechAugmentationInt_comp_resolution_d (U : OpenCoverSet X)
    (J : InjectiveResolution G) (p p' : ℤ)
    (s : ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj
      (op (⊤ : Opens X))).obj (J.cochainComplex.X p))
    (hs : ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj
      (op (⊤ : Opens X))).map (J.cochainComplex.d p p') s = 0) :
    ((CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
          (hypercover U)).map (J.cochainComplex.d p p')).f 0
        (CechSite.cechAugmentationInt.{v} (Opens.grothendieckTopology X) (hypercover U)
          (J.cochainComplex.X p) s) = 0 := by
  rw [← ConcreteCategory.comp_apply, CechSite.cechAugmentationInt_naturality.{v}
    (Opens.grothendieckTopology X) (hypercover U) (J.cochainComplex.d p p'),
    ConcreteCategory.comp_apply, hs, map_zero]

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})] in
/-- The refinement maps of Čech bicomplexes compose contravariantly. -/
private theorem refinementBicomplexMap_f_comp {U V W : OpenCoverSet X} (f : U ⟶ V) (g : V ⟶ W)
    (J : InjectiveResolution G) (p : ℤ) :
    (refinementBicomplexMap f J).f p ≫ (refinementBicomplexMap g J).f p =
      (refinementBicomplexMap (f ≫ g) J).f p :=
  refinementComplexIntNat_app_comp.{v} f g (J.cochainComplex.X p)

omit [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})] in
/-- **Stacks 09V2**, one refinement of the staircase.  A cochain in bidegree `(p + 1, q)` of
the Čech bicomplex of an injective resolution which both differentials kill becomes, after one
refinement of the open covering, congruent modulo a boundary of the total complex to a cochain
in bidegree `(p, q + 1)` which both differentials kill.

The local `d`-exactness of the resolution in positive degrees produces a primitive in bidegree
`(p, q)` over a covering of each iterated intersection, and Stacks 09UW refines the covering so
that all those primitives live on the iterated intersections of a single covering. -/
private theorem exists_refinement_column_shift [T2Space X] [CompactSpace X]
    (J : InjectiveResolution G) (p q n : ℤ) (hp : 0 ≤ p) (hn : p + q = n)
    (U : OpenCoverSet X) (c : ((resolutionBicomplex U J).X (p + 1)).X q)
    (hd : ((resolutionBicomplex U J).d (p + 1) (p + 1 + 1)).f q c = 0)
    (hδ : ((resolutionBicomplex U J).X (p + 1)).d q (q + 1) c = 0) :
    ∃ (V : OpenCoverSet X) (f : U ⟶ V) (c₂ : ((resolutionBicomplex V J).X p).X (q + 1))
      (w : (resolutionTotal V J).X n),
      ((resolutionBicomplex V J).d p (p + 1)).f (q + 1) c₂ = 0 ∧
      ((resolutionBicomplex V J).X p).d (q + 1) (q + 1 + 1) c₂ = 0 ∧
      (resolutionBicomplex V J).ιTotal (ComplexShape.up ℤ) (p + 1) q (n + 1)
            (by simp only [ComplexShape.π_def]; omega)
            (((refinementBicomplexMap f J).f (p + 1)).f q c) =
        (resolutionBicomplex V J).ιTotal (ComplexShape.up ℤ) p (q + 1) (n + 1)
            (by simp only [ComplexShape.π_def]; omega) c₂ +
          (resolutionTotal V J).d n (n + 1) w := by
  have hS : (ShortComplex.mk (J.cochainComplex.d p (p + 1))
      (J.cochainComplex.d (p + 1) (p + 1 + 1))
      (J.cochainComplex.d_comp_d p (p + 1) (p + 1 + 1))).Exact :=
    (J.cochainComplex.exactAt_iff' p (p + 1) (p + 1 + 1) (by simp) (by simp)).mp
      (CochainComplex.exactAt_of_isLE J.cochainComplex 0 (p + 1) (by omega))
  obtain ⟨V, f, b₀, hb₀⟩ := exists_refinement_cochain_preimage_int.{v} _ hS U q c hd
  obtain ⟨b, hb⟩ : ∃ b : ((resolutionBicomplex V J).X p).X q,
      ((resolutionBicomplex V J).d p (p + 1)).f q b =
        ((refinementBicomplexMap f J).f (p + 1)).f q c := ⟨b₀, hb₀⟩
  have hδrefine : ((resolutionBicomplex V J).X (p + 1)).d q (q + 1)
      (((refinementBicomplexMap f J).f (p + 1)).f q c) = 0 := by
    rw [← hom_f_d_apply ((refinementBicomplexMap f J).f (p + 1)) q (q + 1) c, hδ, map_zero]
  have hdδb : ((resolutionBicomplex V J).d p (p + 1)).f (q + 1)
      (((resolutionBicomplex V J).X p).d q (q + 1) b) = 0 := by
    rw [hom_f_d_apply ((resolutionBicomplex V J).d p (p + 1)) q (q + 1) b, hb, hδrefine]
  obtain ⟨c₂, h1, h2, heq⟩ :=
    exists_ιTotal_eq_add_total_d (resolutionBicomplex V J) p q n hn b hdδb
  rw [hb] at heq
  exact ⟨V, f, c₂, _, h1, h2, heq⟩

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})] in
/-- A refinement map of total complexes, read on one summand, on elements. -/
private theorem refinementTotalMap_ιTotal_apply (J : InjectiveResolution G) (p q n : ℤ)
    (hn : p + q = n) {U V : OpenCoverSet X} (f : U ⟶ V)
    (x : ((resolutionBicomplex U J).X p).X q) :
    (refinementTotalMap f J).f n
        ((resolutionBicomplex U J).ιTotal (ComplexShape.up ℤ) p q n hn x) =
      (resolutionBicomplex V J).ιTotal (ComplexShape.up ℤ) p q n hn
        (((refinementBicomplexMap f J).f p).f q x) :=
  total_map_ιTotal_apply (resolutionBicomplex U J) (resolutionBicomplex V J)
    (refinementBicomplexMap f J) p q n hn x

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})] in
/-- Transporting a summand of the total complex along a refinement composes the two
refinements. -/
private theorem refinementTotalMap_ιTotal (J : InjectiveResolution G) (p q n : ℤ)
    (hn : p + q = n) {U V₁ V : OpenCoverSet X} (f₁ : U ⟶ V₁) (f₂ : V₁ ⟶ V)
    (x : ((resolutionBicomplex U J).X p).X q) :
    (refinementTotalMap f₂ J).f n
        ((resolutionBicomplex V₁ J).ιTotal (ComplexShape.up ℤ) p q n hn
          (((refinementBicomplexMap f₁ J).f p).f q x)) =
      (resolutionBicomplex V J).ιTotal (ComplexShape.up ℤ) p q n hn
        (((refinementBicomplexMap (f₁ ≫ f₂) J).f p).f q x) := by
  rw [refinementTotalMap_ιTotal_apply J p q n hn f₂,
    ← refinementBicomplexMap_f_comp f₁ f₂ J p, HomologicalComplex.comp_f,
    ConcreteCategory.comp_apply]

omit [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})] in
/-- **Stacks 09V2**, the staircase.  Let `X` be Hausdorff and quasi-compact, let `J` be an
injective resolution of an abelian sheaf `G` and fix a bidegree `(p, q)` of the Čech bicomplex
of `J`.  A cochain in that bidegree which is killed by both differentials becomes, after `p`
successive refinements of the open covering, the image of a Čech cochain of `G` in total degree
`p + q`, up to a boundary of the total complex.

The induction walks the class down the staircase `(p, q) → (p - 1, q + 1) → ⋯ → (0, p + q)`,
one refinement of the covering at each step by `exists_refinement_column_shift`; at the foot of
the staircase the cochain lies in the zeroth column, where left exactness of the Čech complex
functor identifies it with a cochain of `G = ker(J⁰ → J¹)`. -/
private theorem exists_cechCochain_of_column [T2Space X] [CompactSpace X]
    (J : InjectiveResolution G) :
    ∀ (k : ℕ) (p q n n' : ℤ) (_hp : p = (k : ℤ)) (hpq : p + q = n) (_hn : n' + 1 = n)
      (U : OpenCoverSet X) (c : ((resolutionBicomplex U J).X p).X q),
      ((resolutionBicomplex U J).d p (p + 1)).f q c = 0 →
      ((resolutionBicomplex U J).X p).d q (q + 1) c = 0 →
      ∃ (V : OpenCoverSet X) (f : U ⟶ V)
        (z : ((CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
          (hypercover V)).obj G).X n) (w : (resolutionTotal V J).X n'),
        (CechSite.cechToTotal.{v} (Opens.grothendieckTopology X) (hypercover V) G J).f n z =
          (resolutionBicomplex V J).ιTotal (ComplexShape.up ℤ) p q n hpq
              (((refinementBicomplexMap f J).f p).f q c) +
            (resolutionTotal V J).d n' n w := by
  intro k
  induction k with
  | zero =>
    intro p q n n' hp hpq _ U c hd _
    obtain rfl : p = 0 := by simpa using hp
    obtain rfl : n = q := by omega
    have hC := preservesFiniteLimits_cechIntEval.{v} U n
    have hmono := mono_inclusionZero J
    have he := (inclusionZero_exact J).map_of_mono_of_preservesKernel
      (CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X) (hypercover U) ⋙
        HomologicalComplex.eval AddCommGrpCat.{max u v} (ComplexShape.up ℤ) n)
      inferInstance inferInstance
    obtain ⟨z, hz⟩ := (ShortComplex.ab_exact_iff _).mp he c hd
    refine ⟨U, 𝟙 U, z, 0, ?_⟩
    have hid : ((refinementBicomplexMap (𝟙 U) J).f (0 : ℤ)).f n c = c := by
      have h : (refinementBicomplexMap (𝟙 U) J).f (0 : ℤ) =
          (refinementComplexIntNat (𝟙 U)).app (J.cochainComplex.X 0) := rfl
      rw [h, refinementComplexIntNat_app_id]
      rfl
    rw [hid, map_zero, add_zero, cechToTotal_f]
    exact (ConcreteCategory.comp_apply _ _ z).trans (congrArg _ hz)
  | succ k ih =>
    intro p q n n' hp hpq hn U c hd hδ
    obtain ⟨p₀, rfl⟩ : ∃ p₀, p = p₀ + 1 := ⟨(k : ℤ), by rw [hp]; push_cast; ring⟩
    obtain rfl : n = n' + 1 := hn.symm
    have hp₀ : p₀ = (k : ℤ) := by push_cast at hp; omega
    obtain ⟨V₁, f₁, c₂, w₁, h1, h2, heq⟩ := exists_refinement_column_shift.{v} J p₀ q n'
      (by omega) (by omega) U c hd hδ
    obtain ⟨V, f₂, z, w₂, hz⟩ :=
      ih p₀ (q + 1) (n' + 1) n' hp₀ (by omega) rfl V₁ c₂ h1 h2
    have hstep := congrArg ((refinementTotalMap f₂ J).f (n' + 1)) heq
    rw [map_add, refinementTotalMap_ιTotal J (p₀ + 1) q (n' + 1) (by omega) f₁ f₂,
      refinementTotalMap_ιTotal_apply J p₀ (q + 1) (n' + 1) (by omega) f₂,
      hom_f_d_apply (refinementTotalMap f₂ J) n' (n' + 1)] at hstep
    refine ⟨V, f₁ ≫ f₂, z, w₂ - (refinementTotalMap f₂ J).f n' w₁, ?_⟩
    rw [hz, hstep, map_sub]
    abel

end Staircase

/-! ### Stacks 09V2, surjectivity -/

section Main

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})]

/-- The open covering of a space by the space itself. -/
def topCover (X : Type u) [TopologicalSpace X] : OpenCoverSet X where
  members := {⊤}
  iSup_eq_top := le_antisymm le_top
    (le_iSup (fun V : ({⊤} : Set (Opens X)) ↦ (V : Opens X)) ⟨⊤, rfl⟩)

/-- **Stacks Project, Tag 09V2.** On a Hausdorff quasi-compact space every sheaf cohomology
class in nonnegative degree comes from the Čech cohomology of some open covering.

The class is represented by a global section of the degree-`n` term of an injective resolution
killed by the differential; `exists_cechCochain_of_column` walks that representative down the
staircase of the Čech bicomplex, refining the covering `n` times, and delivers a Čech cochain of
the sheaf whose class in the total complex is the given one. -/
theorem exists_cechCohomologyToCohomology_preimage_of_nonneg
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) (n : ℤ) (hn : 0 ≤ n)
    (y : (CechSite.derivedSectionsFunctor.{max u v} (Opens.grothendieckTopology X)
      (⊤ : Opens X) ⋙ DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u v} n).obj G) :
    ∃ U : OpenCoverSet X, ∃ x, ((CechSite.cechCohomologyToCohomology.{v}
      (Opens.grothendieckTopology X) (hypercover U)
        (hypercover_mem_grothendieckTopology U) n).app G) x = y := by
  classical
  set H := DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} n with hHdef
  set qf := DerivedCategory.homologyFunctorFactors AddCommGrpCat.{max u v} n with hqdef
  set Γ := (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj
    (op (⊤ : Opens X)) with hΓdef
  let J := InjectiveResolution.of G
  let R := (Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj J.cochainComplex
  let ρ := J.toRightDerived Γ
  have hΦ : IsIso (qf.inv.app R ≫ H.map ρ) := by
    have h1 : IsIso (qf.inv.app R) := Iso.isIso_inv (qf.app R)
    have h2 : IsIso (H.map ρ) := inferInstance
    infer_instance
  obtain ⟨t, ht⟩ := (AddCommGrpCat.epi_iff_surjective (R.homologyπ n)).mp inferInstance
    (inv (qf.inv.app R ≫ H.map ρ) y)
  -- The augmentation of the representing section, as a cochain in bidegree `(n, 0)`.
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ((resolutionBicomplex (topCover X) J).X n).X 0,
      CechSite.cechAugmentationInt.{v} (Opens.grothendieckTopology X)
        (hypercover (topCover X)) (J.cochainComplex.X n) (R.iCycles n t) = c₀ := ⟨_, rfl⟩
  have hdt : R.d n (n + 1) (R.iCycles n t) = 0 := by
    rw [← ConcreteCategory.comp_apply, R.iCycles_d n (n + 1)]
    simp
  have hd₀ : ((resolutionBicomplex (topCover X) J).d n (n + 1)).f 0 c₀ = 0 := by
    rw [← hc₀, resolutionBicomplex_d]
    exact cechAugmentationInt_comp_resolution_d.{v} (topCover X) J n (n + 1) _ hdt
  have hδ₀ : ((resolutionBicomplex (topCover X) J).X n).d 0 1 c₀ = 0 := by
    rw [← hc₀]
    exact cechAugmentationInt_comp_cech_d.{v} (topCover X) (J.cochainComplex.X n) _
  -- The staircase.
  obtain ⟨V, fr, z, w, hzw⟩ := exists_cechCochain_of_column.{v} J n.toNat n 0 n (n - 1)
    (by omega) (by omega) (by omega) (topCover X) c₀ hd₀ hδ₀
  -- The augmentation into the total complex, after the refinement.
  have hA : (CechSite.totalAugmentation.{v} (Opens.grothendieckTopology X) (hypercover V)
        (hypercover_mem_grothendieckTopology V) J.cochainComplex).f n (R.iCycles n t) =
      (resolutionBicomplex V J).ιTotal (ComplexShape.up ℤ) n 0 n
          (by simp only [ComplexShape.π_def]; omega)
        (((refinementBicomplexMap fr J).f n).f 0 c₀) := by
    rw [CechSite.totalAugmentation_f.{v} (Opens.grothendieckTopology X) (hypercover V)
      (hypercover_mem_grothendieckTopology V) J.cochainComplex n, ConcreteCategory.comp_apply,
      ← hc₀]
    refine congrArg _ ?_
    rw [← cechAugmentationInt_refinement fr (J.cochainComplex.X n)]
    exact ConcreteCategory.comp_apply _ _ _
  -- Monomorphy of the comparison in degree `n + 1`.
  have hC1 := preservesFiniteLimits_cechIntEval.{v} V (n + 1)
  have hmono := mono_inclusionZero J
  have hfmono : Mono (((CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
      (hypercover V)).map J.inclusionZero).f (n + 1)) :=
    (CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X) (hypercover V) ⋙
      HomologicalComplex.eval AddCommGrpCat.{max u v} (ComplexShape.up ℤ) (n + 1)).map_mono _
  have hιmono : Mono ((resolutionBicomplex V J).ιTotal (ComplexShape.up ℤ) 0 (n + 1) (n + 1)
      (by simp)) := mono_ιTotal (resolutionBicomplex V J) 0 (n + 1) (n + 1) (by omega)
  have hβmono : Mono ((CechSite.cechToTotal.{v} (Opens.grothendieckTopology X)
      (hypercover V) G J).f (n + 1)) := by
    rw [cechToTotal_f]
    exact mono_comp _ _
  obtain ⟨x, hx⟩ := exists_homologyMap_preimage_of_boundary
    (CechSite.totalAugmentation.{v} (Opens.grothendieckTopology X) (hypercover V)
      (hypercover_mem_grothendieckTopology V) J.cochainComplex)
    (CechSite.cechToTotal.{v} (Opens.grothendieckTopology X) (hypercover V) G J) n (n - 1)
    t z (-w) (by rw [hA, hzw, map_neg]; abel)
  -- Transporting the conclusion to the canonical comparison.
  obtain ⟨r⟩ := CechSite.nonempty_cechResolutionComparison.{v}
    (Opens.grothendieckTopology X) (hypercover V)
    (hypercover_mem_grothendieckTopology V) G J
  have hrα : r.α = CechSite.totalAugmentation.{v} (Opens.grothendieckTopology X) (hypercover V)
      (hypercover_mem_grothendieckTopology V) J.cochainComplex :=
    HomologicalComplex.hom_ext _ _ fun m ↦ (r.α_f m).trans
      (CechSite.totalAugmentation_f.{v} (Opens.grothendieckTopology X) (hypercover V)
        (hypercover_mem_grothendieckTopology V) J.cochainComplex m).symm
  have hrβ : r.β = CechSite.cechToTotal.{v} (Opens.grothendieckTopology X)
      (hypercover V) G J :=
    HomologicalComplex.hom_ext _ _ fun m ↦ (r.β_f m).trans (cechToTotal_f V J m).symm
  rw [← hrα, ← hrβ] at hx
  let kk := qf.inv.app ((resolutionBicomplex V J).total (ComplexShape.up ℤ)) ≫
    H.map r.αIso.inv ≫ H.map ρ
  have hcc : ((CechSite.cechCohomologyToCohomology.{v} (Opens.grothendieckTopology X)
        (hypercover V) (hypercover_mem_grothendieckTopology V) n).app G) =
      H.map (DerivedCategory.Q.map r.β) ≫ H.map r.αIso.inv ≫ H.map ρ :=
    (congrArg H.map r.comparison).trans ((H.map_comp _ _).trans
      (congrArg (fun zz ↦ H.map (DerivedCategory.Q.map r.β) ≫ zz) (H.map_comp _ _)))
  have hαk : HomologicalComplex.homologyMap r.α n ≫ kk = qf.inv.app R ≫ H.map ρ := by
    have hid : H.map (DerivedCategory.Q.map r.α) ≫ H.map r.αIso.inv = 𝟙 _ := by
      rw [← H.map_comp, ← r.αIso_hom, Iso.hom_inv_id, H.map_id]
    have h1 : HomologicalComplex.homologyMap r.α n ≫ kk =
        qf.inv.app R ≫ H.map (DerivedCategory.Q.map r.α) ≫ H.map r.αIso.inv ≫ H.map ρ :=
      qf.inv.naturality_assoc r.α _
    rw [h1, ← Category.assoc (H.map (DerivedCategory.Q.map r.α)), hid, Category.id_comp]
  have hβeq : HomologicalComplex.homologyMap r.β n ≫ kk =
      qf.inv.app ((CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
          (hypercover V)).obj G) ≫
        ((CechSite.cechCohomologyToCohomology.{v} (Opens.grothendieckTopology X) (hypercover V)
          (hypercover_mem_grothendieckTopology V) n).app G) := by
    rw [hcc]
    exact qf.inv.naturality_assoc r.β _
  have e1 : ((CechSite.cechCohomologyToCohomology.{v} (Opens.grothendieckTopology X)
        (hypercover V) (hypercover_mem_grothendieckTopology V) n).app G)
      (qf.inv.app ((CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
        (hypercover V)).obj G) x) = (HomologicalComplex.homologyMap r.β n ≫ kk) x := by
    rw [hβeq]
    exact (ConcreteCategory.comp_apply _ _ x).symm
  have e2 : (HomologicalComplex.homologyMap r.β n ≫ kk) x = y := by
    have s1 : (HomologicalComplex.homologyMap r.β n ≫ kk) x =
        kk (HomologicalComplex.homologyMap r.β n x) := ConcreteCategory.comp_apply _ _ x
    have s2 : kk (HomologicalComplex.homologyMap r.β n x) =
        (HomologicalComplex.homologyMap r.α n ≫ kk) (R.homologyπ n t) :=
      (congrArg (fun zz ↦ kk zz) hx).trans (ConcreteCategory.comp_apply _ _ _).symm
    have s3 : (HomologicalComplex.homologyMap r.α n ≫ kk) (R.homologyπ n t) =
        (inv (qf.inv.app R ≫ H.map ρ) ≫ (qf.inv.app R ≫ H.map ρ)) y := by
      rw [hαk]
      refine (congrArg (fun zz ↦ (qf.inv.app R ≫ H.map ρ) zz) ht).trans ?_
      exact (ConcreteCategory.comp_apply _ _ y).symm
    have s4 : (inv (qf.inv.app R ≫ H.map ρ) ≫ (qf.inv.app R ≫ H.map ρ)) y = y := by
      rw [IsIso.inv_hom_id]
      exact CategoryTheory.id_apply y
    exact s1.trans (s2.trans (s3.trans s4))
  exact ⟨V, qf.inv.app ((CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
    (hypercover V)).obj G) x, e1.trans e2⟩

/-- **Stacks Project, Tag 09V2.** On a Hausdorff quasi-compact space the comparison of
Stacks 09UZ from Čech cohomology to sheaf cohomology is surjective in every nonnegative
degree. -/
theorem surjective_colimitToCohomology_of_nonneg
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) (n : ℤ) (hn : 0 ≤ n) :
    Function.Surjective (colimitToCohomology G n) := by
  intro y
  obtain ⟨U, x, hx⟩ := exists_cechCohomologyToCohomology_preimage_of_nonneg.{v} G n hn y
  refine ⟨colimit.ι (cechDiagram G n) U x, ?_⟩
  exact (ConcreteCategory.comp_apply (colimit.ι (cechDiagram G n) U)
      (colimitToCohomology G n) x).symm.trans
    ((ConcreteCategory.congr_hom (ι_colimitToCohomology (G := G) (p := n) U) x).trans hx)

end Main

end Stacks.Cohomology.CechRefinement

end
