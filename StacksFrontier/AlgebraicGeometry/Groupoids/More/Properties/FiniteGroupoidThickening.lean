module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.OverPullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.GroupoidInverse
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteStratificationInvariant
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteStratificationRankSheaf
public import StacksFrontier.AlgebraicGeometry.Thickenings

/-!
# An invariant thickening of a finite groupoid on which the structure maps are free

Let `G` be a groupoid scheme whose source and target maps are finite. Its Fitting
stratification cuts the object scheme into locally closed rank strata, and the source map
becomes finite locally free of rank `r` over the `r`-th stratum. Choosing the strata greedily
— at each step removing the saturation of the closure of what has already been chosen —
produces a disjoint family of invariant opens whose union `W` is invariant, whose saturated
closure is the whole object scheme, and over which a canonical invariant closed thickening
`W' ⊆ W` is finite locally free for both structure maps of the restricted groupoid.

## Main definitions

* `AlgebraicGeometry.layerPiece`: the open chosen at one stage of the greedy construction, and
  `AlgebraicGeometry.layerCovered` the closed set saturated by the stages up to there.
* `AlgebraicGeometry.layerUnionOpen`: the union `W` of the chosen opens, and
  `AlgebraicGeometry.layerUnionCoproductIso` its identification with their coproduct.
* `AlgebraicGeometry.layerThickening` and
  `AlgebraicGeometry.layerThickeningInclusion`: the closed subscheme `W' ⊆ W` and its
  inclusion.

## Main results

* `AlgebraicGeometry.layerPiece_eq_zero` and `AlgebraicGeometry.layerPiece_eq_succ'`: the two
  defining descriptions of the chosen opens.
* `AlgebraicGeometry.layerUnion_invariant`,
  `AlgebraicGeometry.isInvariantMonomorphism_layerThickeningInclusion`,
  `AlgebraicGeometry.saturation_closure_layerUnion_eq_univ` and
  `AlgebraicGeometry.isThickening_layerThickeningInclusion`: the four properties of the pair.
* `AlgebraicGeometry.exists_invariant_thickening_finiteLocallyFree_restriction`: the invariant
  open, its invariant closed thickening, and the finite local freeness of the two structure
  maps of the restriction to that thickening.

## Implementation notes

The greedy choice is recorded by `AlgebraicGeometry.layerState`, a recursion carrying the open
chosen at a stage together with the closed set already saturated. The thickening is built as a
coproduct over the stages: on the stage `n` it is the scheme-theoretic intersection of the
chosen open with the `n`-th Fitting closed subscheme, and that intersection is a thickening of
the open because the open lies inside the `n`-th stratum. Both the invariance of the resulting
monomorphism and the finite local freeness of its source pullback are checked one stage at a
time and assembled with the Zariski locality of the two properties on the target.

Invariance of a monomorphism is `Stacks.Groupoids.IsInvariantMonomorphism`, an equality in the
subobject poset of the arrow scheme; the conclusion of the source speaks of the closed
subscheme of `W`, so the monomorphism in the statement is the composite with the inclusion of
`W`.

## References

* [Stacks Project, Tag 0ABA](https://stacks.math.columbia.edu/tag/0ABA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry

/-- The saturation of a subset of the object scheme: the image under the target map of its
inverse image under the source map. -/
def arrowSaturation {S : Scheme.{u}} (G : GroupoidScheme S)
    (A : Set G.objects.left) : Set G.objects.left :=
  G.target.left.base '' (G.source.left.base ⁻¹' A)

/-- One stage of the greedy choice of strata: an open of the object scheme together with the
closed set that the stages up to here have already saturated. -/
structure LayerState (X : Scheme.{u}) where
  /-- The open chosen at this stage. -/
  piece : X.Opens
  /-- The closed set saturated by the stages up to and including this one. -/
  covered : Set X
  /-- The saturated set is closed. -/
  covered_closed : IsClosed covered

/-- The greedy choice of strata. At stage `0` the open is the complement of the first Fitting
closed subscheme; at stage `n + 1` it is the complement of the union of the `(n + 2)`-nd
Fitting closed subscheme with everything already saturated. -/
noncomputable def layerState {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] :
    ℕ → LayerState G.objects.left := by
  classical
  have hclosedSat : ∀ A : Set G.objects.left, IsClosed A → IsClosed (arrowSaturation G A) :=
    fun A hA ↦ G.target.left.isClosedMap _ (hA.preimage (by fun_prop))
  have hZclosed : ∀ n, IsClosed ((finiteStratification G n).support :
      Set G.objects.left) :=
    fun n ↦ (finiteStratification G n).support.isClosed
  let basePiece : G.objects.left.Opens :=
    ⟨((finiteStratification G 1).support : Set G.objects.left)ᶜ,
      isOpen_compl_iff.mpr (hZclosed 1)⟩
  exact Nat.rec
    ⟨basePiece, arrowSaturation G (closure (basePiece : Set G.objects.left)),
      hclosedSat _ isClosed_closure⟩
    (fun n st ↦
      let p : G.objects.left.Opens :=
        ⟨(((finiteStratification G (n + 2)).support : Set G.objects.left) ∪ st.covered)ᶜ,
          isOpen_compl_iff.mpr ((hZclosed (n + 2)).union st.covered_closed)⟩
      ⟨p, st.covered ∪ arrowSaturation G (closure (p : Set G.objects.left)),
        st.covered_closed.union (hclosedSat _ isClosed_closure)⟩)

/-- Every member of the Fitting stratification has invariant support. -/
theorem mem_support_finiteStratification_iff {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (n : ℕ) (r : G.arrows.left) :
    G.source.left.base r ∈ (finiteStratification G n).support ↔
      G.target.left.base r ∈ (finiteStratification G n).support := by
  have hsupport := congrArg
    (fun I : G.arrows.left.IdealSheafData ↦ (I.support : Set G.arrows.left))
    (finiteStratification_invariant G n)
  rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap] at hsupport
  exact (Set.ext_iff.mp hsupport r).symm

/-- An invariant subset contains the target of an arrow exactly when it contains its source:
the inverse arrow gives the converse implication. -/
theorem mem_invariantSet_source_iff_target {S : Scheme.{u}} (G : GroupoidScheme S)
    {A : Set G.objects.left} (hA : IsInvariantSet G A) (r : G.arrows.left) :
    G.source.left.base r ∈ A ↔ G.target.left.base r ∈ A := by
  refine ⟨hA r, fun ht ↦ ?_⟩
  have hsInv : G.source.left.base (G.inverse.left.base r) = G.target.left.base r := by
    simpa [Scheme.Hom.comp_apply] using
      congrArg (fun f : G.arrows ⟶ G.objects ↦ f.left.base r) G.source_inverse
  have htInv : G.target.left.base (G.inverse.left.base r) = G.source.left.base r := by
    simpa [Scheme.Hom.comp_apply] using
      congrArg (fun f : G.arrows ⟶ G.objects ↦ f.left.base r) G.target_inverse
  exact htInv ▸ hA (G.inverse.left r) (hsInv ▸ ht)

/-- The open chosen at stage `n` of the greedy choice. -/
noncomputable def layerPiece {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (n : ℕ) : G.objects.left.Opens :=
  (layerState G n).piece

/-- The closed set saturated by the stages up to `n`. -/
noncomputable def layerCovered {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (n : ℕ) : Set G.objects.left :=
  (layerState G n).covered

/-- A subset is contained in its own saturation, because the identity arrows have equal source
and target. -/
theorem mem_arrowSaturation_of_mem {S : Scheme.{u}} (G : GroupoidScheme S)
    {A : Set G.objects.left} {x : G.objects.left} (hx : x ∈ A) : x ∈ arrowSaturation G A := by
  refine ⟨G.identity.left.base x, ?_, ?_⟩
  · have hs : G.source.left.base (G.identity.left.base x) = x := by
      simpa [Scheme.Hom.comp_apply] using
        congrArg (fun f : G.objects ⟶ G.objects ↦ f.left.base x) G.source_identity
    simpa [hs] using hx
  · have ht : G.target.left.base (G.identity.left.base x) = x := by
      simpa [Scheme.Hom.comp_apply] using
        congrArg (fun f : G.objects ⟶ G.objects ↦ f.left.base x) G.target_identity
    simp [ht]

/-- The open chosen at stage `0`. -/
theorem layerPiece_eq_zero {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] :
    (layerPiece G 0 : Set G.objects.left) =
      ((finiteStratification G 1).support : Set G.objects.left)ᶜ := by
  simp [layerPiece, layerState]

/-- The open chosen at stage `n + 1`. -/
theorem layerPiece_eq_succ {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (n : ℕ) :
    (layerPiece G (n + 1) : Set G.objects.left) =
      (((finiteStratification G (n + 2)).support : Set G.objects.left) ∪
        layerCovered G n)ᶜ := by
  simp [layerPiece, layerCovered, layerState]

/-- The set saturated after stage `0`. -/
theorem layerCovered_eq_zero {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] :
    layerCovered G 0 =
      arrowSaturation G (closure (layerPiece G 0 : Set G.objects.left)) := by
  simp [layerCovered, layerPiece, layerState]

/-- The set saturated after stage `n + 1`. -/
theorem layerCovered_eq_succ {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (n : ℕ) :
    layerCovered G (n + 1) =
      layerCovered G n ∪
        arrowSaturation G (closure (layerPiece G (n + 1) : Set G.objects.left)) := by
  simp [layerCovered, layerPiece, layerState]

/-- The set saturated after any stage is invariant. -/
theorem layerCovered_invariant {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (n : ℕ) :
    IsInvariantSet G (layerCovered G n) := by
  induction n with
  | zero =>
      rw [layerCovered_eq_zero]
      exact GroupoidScheme.isInvariantSet_target_image_source_preimage G _
  | succ n ih =>
      rw [layerCovered_eq_succ]
      intro r hr
      rcases (Set.mem_union _ _ _).mp hr with h | h
      · exact Or.inl (ih r h)
      · exact Or.inr
          (GroupoidScheme.isInvariantSet_target_image_source_preimage G _ r h)

/-- Each open chosen by the greedy choice is invariant. -/
theorem layerPiece_invariant {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (n : ℕ) :
    IsInvariantOpen G (layerPiece G n) := by
  intro r hr
  change G.source.left.base r ∈ (layerPiece G n : Set G.objects.left) at hr
  change G.target.left.base r ∈ (layerPiece G n : Set G.objects.left)
  by_cases hn : n = 0
  · subst n
    rw [layerPiece_eq_zero] at hr ⊢
    exact fun hmem ↦ hr ((mem_support_finiteStratification_iff G 1 r).mpr hmem)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [layerPiece_eq_succ] at hr ⊢
    have hZ := mem_support_finiteStratification_iff G (k + 2) r
    have hC := mem_invariantSet_source_iff_target G (layerCovered_invariant G k) r
    simp only [Set.mem_compl_iff, Set.mem_union] at hr ⊢
    rintro (hZ' | hC')
    · exact hr (Or.inl (hZ.mpr hZ'))
    · exact hr (Or.inr (hC.mpr hC'))

/-- Every open chosen at or before stage `n` is contained in the set saturated after stage
`n`. -/
theorem layerPiece_mem_covered {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] {i n : ℕ} (hin : i ≤ n) :
    (layerPiece G i : Set G.objects.left) ⊆ layerCovered G n := by
  induction n with
  | zero =>
      obtain rfl : i = 0 := by omega
      rw [layerCovered_eq_zero]
      exact fun x hx ↦ mem_arrowSaturation_of_mem G (subset_closure hx)
  | succ n ih =>
      by_cases hle : i ≤ n
      · exact (ih hle).trans Set.subset_union_left
      · obtain rfl : i = n + 1 := by omega
        rw [layerCovered_eq_succ]
        exact fun x hx ↦ Or.inr (mem_arrowSaturation_of_mem G (subset_closure hx))

/-- The opens chosen at distinct stages are disjoint. -/
theorem layerPiece_pairwise_disjoint {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] {i j : ℕ} (hij : i < j) :
    Disjoint (layerPiece G i : Set G.objects.left)
      (layerPiece G j : Set G.objects.left) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hij)
  have hiC := layerPiece_mem_covered G (show i ≤ k by omega)
  rw [layerPiece_eq_succ]
  exact Set.disjoint_left.mpr fun x hxi hxj ↦ hxj (Or.inr (hiC hxi))

/-- The saturated closure of one chosen open lies in the saturated closure of their union. -/
theorem layerPiece_saturation_subset_union {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (i : ℕ) :
    arrowSaturation G (closure (layerPiece G i : Set G.objects.left)) ⊆
      arrowSaturation G (closure (⋃ n, (layerPiece G n : Set G.objects.left))) :=
  Set.image_mono (Set.preimage_mono (closure_mono
    (Set.subset_iUnion (s := fun n : ℕ ↦ (layerPiece G n : Set G.objects.left)) i)))

/-- Everything saturated by the greedy choice lies in the saturated closure of the union of the
chosen opens. -/
theorem layerCovered_subset_saturation_closure_union {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFinite G.source.left] [IsFinite G.target.left] (n : ℕ) :
    layerCovered G n ⊆
      arrowSaturation G (closure (⋃ k, (layerPiece G k : Set G.objects.left))) := by
  induction n with
  | zero =>
      rw [layerCovered_eq_zero]
      exact layerPiece_saturation_subset_union G 0
  | succ n ih =>
      rw [layerCovered_eq_succ]
      exact Set.union_subset ih (layerPiece_saturation_subset_union G (n + 1))

/-- A point outside the `(n + 1)`-st Fitting closed subscheme has been saturated by stage
`n`. -/
theorem complement_stratum_subset_layerCovered {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (n : ℕ) :
    ((finiteStratification G (n + 1)).support : Set G.objects.left)ᶜ ⊆ layerCovered G n := by
  cases n with
  | zero =>
      rw [layerCovered_eq_zero, layerPiece_eq_zero]
      exact fun x hx ↦ mem_arrowSaturation_of_mem G (subset_closure hx)
  | succ n =>
      rw [layerCovered_eq_succ]
      intro x hx
      by_cases hc : x ∈ layerCovered G n
      · exact Or.inl hc
      · have hp : x ∈ (layerPiece G (n + 1) : Set G.objects.left) := by
          rw [layerPiece_eq_succ]
          simp only [Set.mem_compl_iff, Set.mem_union]
          exact not_or.mpr ⟨hx, hc⟩
        exact Or.inr (mem_arrowSaturation_of_mem G (subset_closure hp))

/-- The union of the opens chosen by the greedy choice. -/
noncomputable def layerUnionOpen {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] : G.objects.left.Opens :=
  ⨆ n : ULift.{u} ℕ, layerPiece G n.down

/-- The underlying set of the union of the chosen opens. -/
theorem layerUnionOpen_coe {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] :
    (layerUnionOpen G : Set G.objects.left) =
      ⋃ n, (layerPiece G n : Set G.objects.left) := by
  ext x
  simp [layerUnionOpen]

/-- The inclusion of the open chosen at stage `n` into their union. -/
noncomputable def layerPieceToUnion {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (n : ℕ) :
    (layerPiece G n).toScheme ⟶ (layerUnionOpen G).toScheme :=
  G.objects.left.homOfLE (le_iSup (fun i : ULift.{u} ℕ ↦ layerPiece G i.down) (ULift.up n))

/-- The inclusion of a chosen open into the union of the chosen opens is an open immersion. -/
instance isOpenImmersion_layerPieceToUnion {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (n : ℕ) :
    IsOpenImmersion (layerPieceToUnion G n) :=
  inferInstanceAs (IsOpenImmersion (G.objects.left.homOfLE
    (le_iSup (fun i : ULift.{u} ℕ ↦ layerPiece G i.down) (ULift.up n))))

/-- The open range of the inclusion of a chosen open into their union. -/
theorem opensRange_layerPieceToUnion {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (n : ℕ) :
    (layerPieceToUnion G n).opensRange = (layerUnionOpen G).ι ⁻¹ᵁ layerPiece G n :=
  Scheme.opensRange_homOfLE _

/-- The inclusions of the chosen opens into their union are compatible with the inclusions into
the object scheme. -/
theorem layerPieceToUnion_comp_ι {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (n : ℕ) :
    layerPieceToUnion G n ≫ (layerUnionOpen G).ι = (layerPiece G n).ι := by
  dsimp [layerPieceToUnion, layerUnionOpen]
  exact Scheme.homOfLE_ι _ _

/-- The chosen opens are disjoint and cover their union, so that union is their coproduct. -/
noncomputable def layerUnionCoproductIso {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] :
    (∐ fun n : ULift.{u} ℕ ↦ (layerPiece G n.down).toScheme) ≅
      (layerUnionOpen G).toScheme := by
  classical
  have hdisj : Pairwise (fun i j : ULift.{u} ℕ ↦
      Disjoint (layerPieceToUnion G i.down).opensRange
        (layerPieceToUnion G j.down).opensRange) := by
    intro i j hij
    rw [opensRange_layerPieceToUnion, opensRange_layerPieceToUnion]
    apply TopologicalSpace.Opens.coe_disjoint.mp
    change Disjoint ((layerUnionOpen G).ι.base ⁻¹' (layerPiece G i.down : Set G.objects.left))
      ((layerUnionOpen G).ι.base ⁻¹' (layerPiece G j.down : Set G.objects.left))
    refine Set.disjoint_left.mpr fun x hxi hxj ↦ ?_
    have hne : i.down ≠ j.down := fun h ↦ hij (by cases i; cases j; cases h; rfl)
    have hpair : Disjoint (layerPiece G i.down : Set G.objects.left)
        (layerPiece G j.down : Set G.objects.left) := by
      rcases lt_or_gt_of_ne hne with hij' | hji
      · exact layerPiece_pairwise_disjoint G hij'
      · exact (layerPiece_pairwise_disjoint G hji).symm
    exact Set.disjoint_left.mp hpair hxi hxj
  have hcov : ⨆ n : ULift.{u} ℕ, (layerPieceToUnion G n.down).opensRange = ⊤ := by
    ext x
    change (x ∈ (⨆ n : ULift.{u} ℕ, (layerPieceToUnion G n.down).opensRange :
        (layerUnionOpen G).toScheme.Opens)) ↔ x ∈ (⊤ : (layerUnionOpen G).toScheme.Opens)
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp x.property
    refine ⟨i, ?_⟩
    rw [opensRange_layerPieceToUnion]
    exact hi
  have hiso : IsIso (Limits.Sigma.desc fun n : ULift.{u} ℕ ↦ layerPieceToUnion G n.down) :=
    (Limits.Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
      (Limits.Cofan.mk (layerUnionOpen G).toScheme
        fun n : ULift.{u} ℕ ↦ layerPieceToUnion G n.down)).mp
      (nonempty_isColimit_cofanMk_of _ hcov hdisj)
  exact asIso (Limits.Sigma.desc fun n : ULift.{u} ℕ ↦ layerPieceToUnion G n.down)

/-- The identification of the union of the chosen opens with their coproduct, read on one
summand. -/
theorem layerUnionCoproductIso_ι {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (n : ULift.{u} ℕ) :
    Limits.Sigma.ι (fun m : ULift.{u} ℕ ↦ (layerPiece G m.down).toScheme) n ≫
        (layerUnionCoproductIso G).hom = layerPieceToUnion G n.down := by
  dsimp [layerUnionCoproductIso]
  exact Limits.Sigma.ι_comp_desc _ _

/-- The union of the chosen opens is invariant. -/
theorem layerUnion_invariant {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] :
    IsInvariantOpen G (layerUnionOpen G) := by
  intro r hr
  change G.source.left.base r ∈ (layerUnionOpen G : Set G.objects.left) at hr
  change G.target.left.base r ∈ (layerUnionOpen G : Set G.objects.left)
  rw [layerUnionOpen_coe] at hr ⊢
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hr
  exact Set.mem_iUnion.mpr ⟨n, layerPiece_invariant G n r hn⟩

/-- The saturated closure of the union of the chosen opens is the whole object scheme. -/
theorem saturation_closure_layerUnion_eq_univ {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] :
    arrowSaturation G (closure (layerUnionOpen G : Set G.objects.left)) = Set.univ := by
  refine Set.eq_univ_iff_forall.mpr fun x ↦ ?_
  obtain ⟨m, hm⟩ := finiteStratification_exhaustive G x
  cases m with
  | zero =>
      refine absurd ?_ hm
      rw [finiteStratification_zero]
      trivial
  | succ n =>
      simpa only [layerUnionOpen_coe] using
        layerCovered_subset_saturation_closure_union G n
          (complement_stratum_subset_layerCovered G n hm)

/-- The saturation of a union is the union of the saturations. -/
theorem arrowSaturation_union {S : Scheme.{u}} (G : GroupoidScheme S)
    (A B : Set G.objects.left) :
    arrowSaturation G (A ∪ B) = arrowSaturation G A ∪ arrowSaturation G B := by
  simp [arrowSaturation, Set.preimage_union, Set.image_union]

/-- The members of the Fitting stratification have decreasing supports. -/
theorem support_finiteStratification_antitone {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] {m n : ℕ} (hmn : m ≤ n) :
    ((finiteStratification G n).support : Set G.objects.left) ⊆
      ((finiteStratification G m).support : Set G.objects.left) := by
  induction hmn with
  | refl => exact subset_rfl
  | @step k _ ih =>
      exact subset_trans
        (Scheme.IdealSheafData.support_antitone (finiteStratification_mono G k)) ih

/-- The set saturated after stage `n` is the saturation of the union of the closures of the
opens chosen at the stages up to `n`. -/
theorem layerCovered_eq_arrowSaturation_biUnion {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (n : ℕ) :
    layerCovered G n =
      arrowSaturation G
        (⋃ r ∈ Set.Iic n, closure (layerPiece G r : Set G.objects.left)) := by
  induction n with
  | zero =>
      rw [layerCovered_eq_zero]
      simp
  | succ n ih =>
      have hIic : (⋃ r ∈ Set.Iic (n + 1), closure (layerPiece G r : Set G.objects.left)) =
          (⋃ r ∈ Set.Iic n, closure (layerPiece G r : Set G.objects.left)) ∪
            closure (layerPiece G (n + 1) : Set G.objects.left) := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_union, exists_prop]
        constructor
        · rintro ⟨r, hr, hx⟩
          rcases Nat.le_succ_iff.mp hr with h | rfl
          · exact Or.inl ⟨r, h, hx⟩
          · exact Or.inr hx
        · rintro (⟨r, hr, hx⟩ | hx)
          · exact ⟨r, hr.trans (Nat.le_succ n), hx⟩
          · exact ⟨n + 1, le_rfl, hx⟩
      rw [layerCovered_eq_succ, ih, hIic, arrowSaturation_union]

/-- The open chosen at stage `n + 1`, in the form the source gives it: the points of the
`(n + 1)`-st Fitting closed subscheme outside the `(n + 2)`-nd one and outside the saturation
of the closures of the opens chosen at the earlier stages. -/
theorem layerPiece_eq_succ' {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (n : ℕ) :
    (layerPiece G (n + 1) : Set G.objects.left) =
      {x | x ∈ (finiteStratification G (n + 1)).support ∧
        x ∉ (finiteStratification G (n + 2)).support ∧
        x ∉ G.target.left.base ''
          (G.source.left.base ⁻¹'
            (⋃ r ∈ Set.Iic n, closure (layerPiece G r : Set G.objects.left)))} := by
  have hcov := layerCovered_eq_arrowSaturation_biUnion G n
  rw [layerPiece_eq_succ]
  ext x
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, not_or]
  rw [hcov]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, h2⟩
    by_contra hnot
    exact h2 (hcov ▸ complement_stratum_subset_layerCovered G n hnot)
  · rintro ⟨-, h1, h2⟩
    exact ⟨h1, h2⟩

/-- The open chosen at stage `n` lies in the `n`-th rank stratum. -/
theorem layerPiece_subset_stratum {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (n : ℕ) :
    (layerPiece G n : Set G.objects.left) ⊆
      ((finiteStratification G n).support : Set G.objects.left) \
        ((finiteStratification G (n + 1)).support : Set G.objects.left) := by
  cases n with
  | zero =>
      rw [layerPiece_eq_zero]
      exact fun x hx ↦ ⟨by simp [finiteStratification_zero], hx⟩
  | succ n =>
      rw [layerPiece_eq_succ]
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_union] at hx
      refine ⟨?_, fun h ↦ hx (Or.inl h)⟩
      by_contra hnot
      exact hx (Or.inr (complement_stratum_subset_layerCovered G n hnot))

/-- The open chosen at stage `n` is covered by an open of the `n`-th Fitting closed subscheme
over which the source map is finite locally free of rank `n + 1`. -/
theorem exists_rank_stratum_layer {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (n : ℕ) :
    ∃ V : (finiteStratification G n).subscheme.Opens,
      (layerPiece G n : Set G.objects.left) ⊆
          Set.range (V.ι ≫ (finiteStratification G n).subschemeι) ∧
        IsFiniteLocallyFreeOfRank
          (pullback.snd G.source.left (V.ι ≫ (finiteStratification G n).subschemeι))
          (n + 1) := by
  obtain ⟨V, hV, hflf⟩ := finiteStratification_rank G (n + 1) (Nat.succ_pos n)
  refine ⟨V, ?_, hflf⟩
  have hV' : Set.range (V.ι ≫ (finiteStratification G n).subschemeι) =
      ((finiteStratification G n).support : Set G.objects.left) \
        ((finiteStratification G (n + 1)).support : Set G.objects.left) := by
    simpa [Nat.add_sub_cancel] using hV
  rw [hV']
  exact layerPiece_subset_stratum G n

/-- The scheme-theoretic intersection of the open chosen at stage `n` with the `n`-th Fitting
closed subscheme is a thickening of that open, because the open lies in the `n`-th stratum. -/
theorem layerFitting_thickening {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (n : ℕ) :
    IsThickening
      (pullback.fst (layerPiece G n).ι (finiteStratification G n).subschemeι) := by
  set j := pullback.fst (layerPiece G n).ι (finiteStratification G n).subschemeι with hj
  refine ⟨inferInstance, fun x ↦ ?_⟩
  change x ∈ Set.range j.base
  rw [hj, Scheme.Pullback.range_fst, Scheme.IdealSheafData.range_subschemeι]
  exact (layerPiece_subset_stratum G n x.property).1

/-- A property stable under isomorphism holds for the base change of `f` along a composite
`h ≫ g` exactly when it holds for the iterated base change along `g` and then `h`. -/
private theorem snd_comp_mem_iff {X Y Z W : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ Y) :
    P (pullback.snd f (h ≫ g)) ↔ P (pullback.snd (pullback.snd f g) h) := by
  rw [← pullbackLeftPullbackSndIso_hom_snd f g h]
  exact (P.cancel_left_of_respectsIso (pullbackLeftPullbackSndIso f g h).hom _).symm

/-- Pulling the source map back along the intersection of the open chosen at stage `n` with the
`n`-th Fitting closed subscheme gives a finite locally free morphism. -/
theorem layerFittingPullback_source_finiteLocallyFree {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFinite G.source.left] [IsFinite G.target.left] (n : ℕ) :
    IsFiniteLocallyFree
      (pullback.snd G.source.left
        (pullback.snd (layerPiece G n).ι (finiteStratification G n).subschemeι ≫
          (finiteStratification G n).subschemeι)) := by
  obtain ⟨V, hpiece, hrank⟩ := exists_rank_stratum_layer G n
  set Iι := (finiteStratification G n).subschemeι with hIι
  set p := pullback.fst (layerPiece G n).ι Iι with hp
  set q := pullback.snd (layerPiece G n).ι Iι with hq
  have hqrange : Set.range q.base ⊆ Set.range V.ι.base := by
    rintro y ⟨x, rfl⟩
    obtain ⟨v, hv⟩ := hpiece (p.base x).property
    refine ⟨v, Iι.isClosedEmbedding.injective ?_⟩
    have hpull := congrArg
      (fun f : pullback (layerPiece G n).ι Iι ⟶ G.objects.left ↦ f.base x)
      (pullback.condition (f := (layerPiece G n).ι) (g := Iι))
    change (layerPiece G n).ι.base (p.base x) = Iι.base (q.base x) at hpull
    change (V.ι ≫ Iι).base v = (layerPiece G n).ι.base (p.base x) at hv
    exact hv.trans hpull
  set qV : pullback (layerPiece G n).ι Iι ⟶ V := IsOpenImmersion.lift V.ι q hqrange with hqV'
  have hqV : qV ≫ V.ι = q := IsOpenImmersion.lift_fac V.ι q hqrange
  have hbase : IsFiniteLocallyFree (pullback.snd G.source.left (V.ι ≫ Iι)) :=
    have : IsFiniteLocallyFreeOfRank (pullback.snd G.source.left (V.ι ≫ Iι)) (n + 1) := hrank
    IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ (n + 1)
  have hfN : IsFiniteLocallyFree
      (pullback.snd (pullback.snd G.source.left (V.ι ≫ Iι)) qV) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback _ qV) hbase
  have hfD : IsFiniteLocallyFree (pullback.snd G.source.left (qV ≫ V.ι ≫ Iι)) :=
    (snd_comp_mem_iff (@IsFiniteLocallyFree : MorphismProperty Scheme.{u}) _ _ _).mpr hfN
  rwa [← Category.assoc, hqV] at hfD

/-- The pullbacks of a subobject along two maps agree exactly when the two base changes of the
monomorphism are equal as subobjects. -/
private theorem subobject_pullback_obj_eq_iff {X Y Z : Scheme.{u}} (g : X ⟶ Z) [Mono g]
    (t s : Y ⟶ Z) :
    (Subobject.pullback t).obj (Subobject.mk g) = (Subobject.pullback s).obj (Subobject.mk g) ↔
      Subobject.mk (pullback.snd g t) = Subobject.mk (pullback.snd g s) := by
  rw [Subobject.pullback_obj_mk (IsPullback.of_hasPullback g t),
    Subobject.pullback_obj_mk (IsPullback.of_hasPullback g s)]

/-- An invariant open has the same two subobject pullbacks along source and target. -/
theorem subobject_pullback_eq_of_isInvariantOpen {S : Scheme.{u}}
    (G : GroupoidScheme S) {V : G.objects.left.Opens} (hV : IsInvariantOpen G V) :
    (Subobject.pullback G.target.left).obj (Subobject.mk V.ι) =
      (Subobject.pullback G.source.left).obj (Subobject.mk V.ι) := by
  have hset : G.target.left.base ⁻¹' (V : Set G.objects.left) =
      G.source.left.base ⁻¹' (V : Set G.objects.left) := by
    ext r
    exact (mem_invariantSet_source_iff_target G hV r).symm
  have hrange : Set.range (pullback.snd V.ι G.target.left).base =
      Set.range (pullback.snd V.ι G.source.left).base := by
    rw [IsOpenImmersion.range_pullbackSnd, IsOpenImmersion.range_pullbackSnd]
    simpa [Scheme.Opens.opensRange_ι] using hset
  rw [subobject_pullback_obj_eq_iff]
  exact Subobject.mk_eq_mk_of_comm _ _ (IsOpenImmersion.isoOfRangeEq _ _ hrange)
    (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange)

/-- Each member of the Fitting stratification has the same two subobject pullbacks along source
and target, because it is an invariant closed subscheme. -/
theorem subobject_pullback_finiteStratification_eq {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFinite G.source.left] [IsFinite G.target.left] (n : ℕ) :
    (Subobject.pullback G.target.left).obj
        (Subobject.mk (finiteStratification G n).subschemeι) =
      (Subobject.pullback G.source.left).obj
        (Subobject.mk (finiteStratification G n).subschemeι) := by
  let F := finiteStratification G n
  have hF : F.comap G.target.left = F.comap G.source.left := finiteStratification_invariant G n
  have hcomap (f : G.arrows.left ⟶ G.objects.left) :
      Subobject.mk (pullback.snd F.subschemeι f) = Subobject.mk (F.comap f).subschemeι := by
    refine Subobject.mk_eq_mk_of_comm _ _
      ((pullbackSymmetry f F.subschemeι).symm ≪≫ (F.comapIso f).symm) ?_
    dsimp
    rw [Category.assoc, Scheme.IdealSheafData.comapIso_inv_subschemeι,
      pullbackSymmetry_inv_comp_fst]
  rw [subobject_pullback_obj_eq_iff, hcomap G.target.left, hcomap G.source.left, hF]

/-- The intersection of the open chosen at stage `n` with the `n`-th Fitting closed subscheme is
an invariant monomorphism into the object scheme: it is the meet of two invariant
subobjects. -/
theorem isInvariantMonomorphism_layerFitting {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (n : ℕ) :
    IsInvariantMonomorphism G
      (pullback.fst (layerPiece G n).ι (finiteStratification G n).subschemeι ≫
        (layerPiece G n).ι) := by
  let U := layerPiece G n
  let F := finiteStratification G n
  let j := pullback.fst U.ι F.subschemeι ≫ U.ι
  have hmeet : Subobject.mk j = Subobject.mk U.ι ⊓ Subobject.mk F.subschemeι := by
    let C := Subobject.mk U.ι
    let D := Subobject.mk F.subschemeι
    let P : Subobject G.objects.left := C ⊓ D
    let a := Subobject.ofLE P C (inf_le_left : C ⊓ D ≤ C) ≫ (Subobject.underlyingIso U.ι).hom
    let b := Subobject.ofLE P D (inf_le_right : C ⊓ D ≤ D) ≫
      (Subobject.underlyingIso F.subschemeι).hom
    have hPull : IsPullback a b U.ι F.subschemeι := by
      refine IsPullback.of_iso (Subobject.inf_isPullback C D)
        (Iso.refl (Subobject.underlying.obj P)) (Subobject.underlyingIso U.ι)
        (Subobject.underlyingIso F.subschemeι) (Iso.refl G.objects.left) ?_ ?_ ?_ ?_
      · change a = 𝟙 (Subobject.underlying.obj P) ≫ a
        simp
      · change b = 𝟙 (Subobject.underlying.obj P) ≫ b
        simp
      · exact (Subobject.underlyingIso_hom_comp_eq_mk U.ι).symm
      · exact (Subobject.underlyingIso_hom_comp_eq_mk F.subschemeι).symm
    have ha : a ≫ U.ι = P.arrow := by
      calc
        a ≫ U.ι = Subobject.ofLE P C (inf_le_left : C ⊓ D ≤ C) ≫
            ((Subobject.underlyingIso U.ι).hom ≫ U.ι) := by
          simp [a, Category.assoc]
        _ = Subobject.ofLE P C (inf_le_left : C ⊓ D ≤ C) ≫ C.arrow := by
          rw [Subobject.underlyingIso_hom_comp_eq_mk]
        _ = P.arrow := Subobject.ofLE_arrow (inf_le_left : C ⊓ D ≤ C)
    have he : hPull.isoPullback.symm.hom ≫ P.arrow = j := by
      calc
        hPull.isoPullback.symm.hom ≫ P.arrow = hPull.isoPullback.symm.hom ≫ a ≫ U.ι := by
          rw [← ha]
        _ = pullback.fst U.ι F.subschemeι ≫ U.ι := by
          dsimp
          rw [← Category.assoc, hPull.isoPullback_inv_fst]
        _ = j := rfl
    simpa [P, C, D] using Subobject.mk_eq_mk_of_comm j P.arrow _ he
  change (Subobject.pullback G.target.left).obj (Subobject.mk j) =
    (Subobject.pullback G.source.left).obj (Subobject.mk j)
  rw [hmeet, Subobject.inf_pullback,
    subobject_pullback_eq_of_isInvariantOpen G (layerPiece_invariant G n),
    subobject_pullback_finiteStratification_eq G n, ← Subobject.inf_pullback]

/-- A property stable under isomorphism holding for the source map of a restriction holds for
its target map: the inverse of the restricted groupoid is an isomorphism exchanging the two. -/
theorem restrictionTarget_mem_of_restrictionSource_mem {S : Scheme.{u}}
    (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects)
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hsrc : P (restrictionSource G g).left) : P (restrictionTarget G g).left := by
  let R := GroupoidScheme.restrict G g
  let H := R.groupoid
  have : IsIso H.inverse.left := groupoidInverse_left_isIso H
  let a := eqToHom (congrArg Over.left R.arrows_eq)
  let b := eqToHom (congrArg Over.left R.objects_eq.symm)
  have : IsIso a := by dsimp [a]; infer_instance
  have : IsIso b := by dsimp [b]; infer_instance
  have hsOver' : H.source.left = a ≫ (restrictionSource G g).left ≫ b := by
    simpa [a, b] using congrArg Over.Hom.left R.source_eq
  have htOver' : H.target.left = a ≫ (restrictionTarget G g).left ≫ b := by
    simpa [a, b] using congrArg Over.Hom.left R.target_eq
  have hs : P H.source.left := by
    rw [hsOver']
    exact (P.cancel_left_of_respectsIso a _).mpr
      ((P.cancel_right_of_respectsIso _ b).mpr hsrc)
  have hcomp : H.inverse.left ≫ H.source.left = H.target.left :=
    congrArg Over.Hom.left H.source_inverse
  have hc := (P.cancel_left_of_respectsIso H.inverse.left H.source.left).mpr hs
  rw [hcomp, htOver'] at hc
  exact (P.cancel_right_of_respectsIso (restrictionTarget G g).left b).mp
    ((P.cancel_left_of_respectsIso a _).mp hc)

/-- For an invariant monomorphism `g`, the source map of the restriction along `g` inherits any
isomorphism-invariant property of the base change of the source map along `g`: invariance makes
the two base changes the same subobject, and the resulting comparison with the fibre product in
`Over S` is a split epimorphism between monomorphisms, hence an isomorphism. -/
theorem restrictionSource_mem_of_isInvariantMonomorphism {S : Scheme.{u}}
    (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects) [Mono g.left]
    (hInv : IsInvariantMonomorphism G g.left) (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hsrc : P (pullback.snd G.source.left g.left)) : P (restrictionSource G g).left := by
  let pTOver := pullback.snd g G.target
  let pSOver := pullback.snd g G.source
  let pS'Over := pullback.fst G.source g
  have : Mono g := Over.mono_of_mono_left g
  have hInvSch : Subobject.mk (pullback.snd g.left G.target.left) =
      Subobject.mk (pullback.snd g.left G.source.left) := by
    exact (subobject_pullback_obj_eq_iff g.left G.target.left G.source.left).mp hInv
  let hpT := overFibreProduct_isPullback g G.target
  let hpS := overFibreProduct_isPullback g G.source
  let eTSsch : pullback g.left G.target.left ≅ pullback g.left G.source.left :=
    Subobject.isoOfMkEqMk (pullback.snd g.left G.target.left)
      (pullback.snd g.left G.source.left) hInvSch
  have heTSsch : eTSsch.hom ≫ pullback.snd g.left G.source.left =
      pullback.snd g.left G.target.left := Subobject.ofMkLEMk_comp hInvSch.le
  let eTSLeft := hpT.isoPullback ≪≫ eTSsch ≪≫ hpS.isoPullback.symm
  have heTSLeft : eTSLeft.hom ≫ pSOver.left = pTOver.left := by
    dsimp [eTSLeft, pSOver, pTOver]
    rw [Category.assoc, Category.assoc, hpS.isoPullback_inv_snd, heTSsch,
      hpT.isoPullback_hom_snd]
  let eTSOver : pullback g G.target ≅ pullback g G.source :=
    Over.isoMk eTSLeft (by
      calc
        eTSLeft.hom ≫ (pullback g G.source).hom =
            eTSLeft.hom ≫ pSOver.left ≫ G.arrows.hom := by cat_disch
        _ = pTOver.left ≫ G.arrows.hom := by rw [← Category.assoc, heTSLeft]
        _ = (pullback g G.target).hom := by cat_disch)
  let eOver := eTSOver ≪≫ (pullbackSymmetry G.source g).symm
  have heTS : eTSOver.hom ≫ pSOver = pTOver := Over.OverMorphism.ext heTSLeft
  have heOver : eOver.hom ≫ pS'Over = pTOver := by
    dsimp [eOver]
    rw [Category.assoc, pullbackSymmetry_inv_comp_fst, heTS]
  let tOver := pullback.snd pTOver pS'Over
  let liftOver : pullback G.source g ⟶ pullback pTOver pS'Over :=
    pullback.lift eOver.inv (𝟙 _) (by
      calc
        eOver.inv ≫ pTOver = eOver.inv ≫ eOver.hom ≫ pS'Over := by rw [heOver]
        _ = 𝟙 _ ≫ pS'Over := by simp)
  have hlift_snd : liftOver ≫ tOver = 𝟙 _ := by
    dsimp [liftOver, tOver]
    exact pullback.lift_snd _ _ _
  have : IsIso tOver :=
    have : IsSplitEpi tOver := IsSplitEpi.mk' ⟨liftOver, hlift_snd⟩
    isIso_of_mono_of_isSplitEpi tOver
  have : IsIso tOver.left := inferInstanceAs (IsIso ((Over.forget S).map tOver))
  let hpSrc := overFibreProduct_isPullback G.source g
  have hSrcOver : P (pullback.snd G.source g).left := by
    rw [← hpSrc.isoPullback_hom_snd]
    exact (P.cancel_left_of_respectsIso hpSrc.isoPullback.hom _).mpr hsrc
  change P (tOver.left ≫ (pullback.snd G.source g).left)
  exact (P.cancel_left_of_respectsIso tOver.left _).mpr hSrcOver

/-- Each coproduct inclusion of a coproduct of schemes is the base change of the corresponding
component of a map of families. -/
theorem sigmaMap_component_pullback {ι : Type u} [Small.{u} ι] (X Y : ι → Scheme.{u})
    (p : ∀ i, X i ⟶ Y i) (i : ι) :
    IsPullback (p i) (Sigma.ι X i) (Sigma.ι Y i) (Limits.Sigma.map p) := by
  apply IsOpenImmersion.isPullback (p i) (Sigma.ι X i) (Sigma.ι Y i) (Limits.Sigma.map p)
  · rw [Limits.Sigma.ι_map]
  · ext x
    obtain ⟨⟨j, xj⟩, hx⟩ := (sigmaMk X).surjective x
    have hx' : (Sigma.ι X j) xj = x := by simpa using hx
    change (Limits.Sigma.map p).base x ∈ Set.range (Sigma.ι Y i).base ↔
      x ∈ Set.range (Sigma.ι X i).base
    rw [← hx']
    have hmap : (Limits.Sigma.map p) ((Sigma.ι X j) xj) = (Sigma.ι Y j) ((p j) xj) := by
      change (Sigma.ι X j ≫ Limits.Sigma.map p) xj = (p j ≫ Sigma.ι Y j) xj
      rw [Limits.Sigma.ι_map]
    change (∃ y, (Sigma.ι Y i).base y =
        (Limits.Sigma.map p).base ((Sigma.ι X j).base xj)) ↔
      ∃ z, (Sigma.ι X i).base z = (Sigma.ι X j).base xj
    rw [hmap]
    constructor
    · rintro ⟨y, hy⟩
      have hp := (sigmaι_eq_iff Y i j y ((p j).base xj)).mp hy
      have hji : j = i := (congrArg Sigma.fst hp).symm
      subst j
      exact ⟨xj, rfl⟩
    · rintro ⟨z, hz⟩
      have hp := (sigmaι_eq_iff X i j z xj).mp hz
      have hji : j = i := (congrArg Sigma.fst hp).symm
      subst j
      have hzj : z = xj := by cases hp; rfl
      subst z
      exact ⟨(p i) xj, rfl⟩

/-- A map of families of schemes whose components all have a Zariski-local property has that
property on the coproduct. -/
theorem sigmaMap_property_of_components {ι : Type u} [Small.{u} ι]
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P] (X Y : ι → Scheme.{u})
    (p : ∀ i, X i ⟶ Y i) (hp : ∀ i, P (p i)) : P (Limits.Sigma.map p) := by
  apply IsZariskiLocalAtTarget.of_openCover (sigmaOpenCover Y)
  intro i
  apply (MorphismProperty.cancel_left_of_respectsIso P
    (sigmaMap_component_pullback X Y p i).flip.isoPullback.hom
    (pullback.snd (Limits.Sigma.map p) (Sigma.ι Y i))).mp
  rw [(sigmaMap_component_pullback X Y p i).flip.isoPullback_hom_snd]
  exact hp i

/-- The part of a base change along a map out of a coproduct lying over one summand. -/
noncomputable def sigmaPullbackComponent {ι : Type u} [Small.{u} ι]
    (X : ι → Scheme.{u}) {Z Y : Scheme.{u}} (j : (∐ X) ⟶ Z) (f : Y ⟶ Z) (i : ι) : Scheme.{u} :=
  pullback (Sigma.ι X i) (pullback.fst j f)

/-- The inclusion of one part of a base change along a map out of a coproduct. -/
noncomputable def sigmaPullbackComponentToPullback {ι : Type u} [Small.{u} ι]
    (X : ι → Scheme.{u}) {Z Y : Scheme.{u}} (j : (∐ X) ⟶ Z) (f : Y ⟶ Z) (i : ι) :
    sigmaPullbackComponent X j f i ⟶ pullback j f :=
  pullback.snd (Sigma.ι X i) (pullback.fst j f)

/-- One part of a base change along a map out of a coproduct is the base change of the
restriction of that map to the corresponding summand. -/
noncomputable def sigmaPullbackComponentIso {ι : Type u} [Small.{u} ι]
    (X : ι → Scheme.{u}) {Z Y : Scheme.{u}} (j : (∐ X) ⟶ Z) (f : Y ⟶ Z) (i : ι) :
    sigmaPullbackComponent X j f i ≅ pullback (Sigma.ι X i ≫ j) f :=
  pullbackRightPullbackFstIso j f (Sigma.ι X i)

/-- The identification of one part of a base change is compatible with the second
projections. -/
theorem sigmaPullbackComponentIso_snd {ι : Type u} [Small.{u} ι] (X : ι → Scheme.{u})
    {Z Y : Scheme.{u}} (j : (∐ X) ⟶ Z) (f : Y ⟶ Z) (i : ι) :
    (sigmaPullbackComponentIso X j f i).hom ≫ pullback.snd (Sigma.ι X i ≫ j) f =
      sigmaPullbackComponentToPullback X j f i ≫ pullback.snd j f :=
  pullbackRightPullbackFstIso_hom_snd j f (Sigma.ι X i)

/-- A base change along a map out of a coproduct is the coproduct of its parts. -/
noncomputable def sigmaPullbackCofanIso {ι : Type u} [Small.{u} ι]
    (X : ι → Scheme.{u}) {Z Y : Scheme.{u}} (j : (∐ X) ⟶ Z) (f : Y ⟶ Z) :
    (∐ fun i ↦ sigmaPullbackComponent X j f i) ≅ pullback j f := by
  classical
  let q := sigmaPullbackComponentToPullback X j f
  have hq' : ∀ i, IsOpenImmersion (q i) := fun i ↦ by
    dsimp [q, sigmaPullbackComponentToPullback, sigmaPullbackComponent]
    infer_instance
  have hcov : ⨆ i, (q i).opensRange = ⊤ := by
    ext x
    change (x ∈ (⨆ i, (q i).opensRange : (pullback j f).Opens)) ↔
      x ∈ (⊤ : (pullback j f).Opens)
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
    obtain ⟨⟨i, xi⟩, hxi⟩ := (sigmaMk X).surjective ((pullback.fst j f).base x)
    refine ⟨i, ?_⟩
    change x ∈ Set.range (pullback.snd (Sigma.ι X i) (pullback.fst j f)).base
    rw [IsOpenImmersion.range_pullbackSnd]
    exact ⟨xi, by simpa using hxi⟩
  have hdisj : Pairwise fun i k ↦ Disjoint (q i).opensRange (q k).opensRange := by
    intro i k hik
    apply TopologicalSpace.Opens.coe_disjoint.mp
    change Disjoint (Set.range (pullback.snd (Sigma.ι X i) (pullback.fst j f)).base)
      (Set.range (pullback.snd (Sigma.ι X k) (pullback.fst j f)).base)
    rw [IsOpenImmersion.range_pullbackSnd, IsOpenImmersion.range_pullbackSnd]
    rintro A hAi hAk x hx
    obtain ⟨xi, hxi⟩ := hAi hx
    obtain ⟨xk, hxk⟩ := hAk hx
    exact absurd (congrArg Sigma.fst
      ((sigmaι_eq_iff X i k xi xk).mp (hxi.trans hxk.symm))) hik
  have hIso : IsIso (Limits.Sigma.desc q) :=
    (Limits.Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
      (Limits.Cofan.mk (pullback j f) q)).mp (nonempty_isColimit_cofanMk_of q hcov hdisj)
  exact asIso (Limits.Sigma.desc q)

/-- The identification of a base change with the coproduct of its parts, read on one summand. -/
theorem sigmaPullbackCofanIso_ι {ι : Type u} [Small.{u} ι] (X : ι → Scheme.{u})
    {Z Y : Scheme.{u}} (j : (∐ X) ⟶ Z) (f : Y ⟶ Z) (i : ι) :
    Sigma.ι (fun i ↦ sigmaPullbackComponent X j f i) i ≫ (sigmaPullbackCofanIso X j f).hom =
      sigmaPullbackComponentToPullback X j f i := by
  dsimp [sigmaPullbackCofanIso]
  exact Limits.Sigma.ι_comp_desc _ _

/-- The identification of a base change with the coproduct of its parts is compatible with the
second projections. -/
theorem sigmaPullbackCofanIso_snd {ι : Type u} [Small.{u} ι] (X : ι → Scheme.{u})
    {Z Y : Scheme.{u}} (j : (∐ X) ⟶ Z) (f : Y ⟶ Z) :
    (sigmaPullbackCofanIso X j f).hom ≫ pullback.snd j f =
      Limits.Sigma.desc fun i ↦ (sigmaPullbackComponentIso X j f i).hom ≫
        pullback.snd (Sigma.ι X i ≫ j) f := by
  refine Limits.Sigma.hom_ext _ _ fun i ↦ ?_
  rw [← Category.assoc, sigmaPullbackCofanIso_ι, Limits.Sigma.ι_comp_desc]
  exact (sigmaPullbackComponentIso_snd X j f i).symm

/-- A monomorphism out of a coproduct has equal subobject pullbacks along two morphisms as soon
as each of its restrictions to a summand has. -/
theorem subobject_pullback_sigma_eq_of_forall {ι : Type u} [Small.{u} ι]
    (X : ι → Scheme.{u}) {Z Y : Scheme.{u}} (j : (∐ X) ⟶ Z) [Mono j] (t s : Y ⟶ Z)
    (h : ∀ i, (Subobject.pullback t).obj (Subobject.mk (Sigma.ι X i ≫ j)) =
      (Subobject.pullback s).obj (Subobject.mk (Sigma.ι X i ≫ j))) :
    (Subobject.pullback t).obj (Subobject.mk j) =
      (Subobject.pullback s).obj (Subobject.mk j) := by
  classical
  let eT := sigmaPullbackCofanIso X j t
  let eS := sigmaPullbackCofanIso X j s
  have hT : eT.hom ≫ pullback.snd j t =
      Limits.Sigma.desc (fun i ↦ (sigmaPullbackComponentIso X j t i).hom ≫
        pullback.snd (Sigma.ι X i ≫ j) t) := sigmaPullbackCofanIso_snd X j t
  have hS : eS.hom ≫ pullback.snd j s =
      Limits.Sigma.desc (fun i ↦ (sigmaPullbackComponentIso X j s i).hom ≫
        pullback.snd (Sigma.ι X i ≫ j) s) := sigmaPullbackCofanIso_snd X j s
  have hi (i : ι) : Subobject.mk (pullback.snd (Sigma.ι X i ≫ j) t) =
      Subobject.mk (pullback.snd (Sigma.ι X i ≫ j) s) := by
    have : Mono (Sigma.ι X i ≫ j) := inferInstance
    exact (subobject_pullback_obj_eq_iff _ t s).mp (h i)
  let ei (i : ι) : sigmaPullbackComponent X j t i ≅ sigmaPullbackComponent X j s i := by
    let ji := Sigma.ι X i ≫ j
    have : Mono ji := by dsimp [ji]; infer_instance
    exact sigmaPullbackComponentIso X j t i ≪≫
      Subobject.isoOfMkEqMk (pullback.snd ji t) (pullback.snd ji s) (hi i) ≪≫
        (sigmaPullbackComponentIso X j s i).symm
  have hei (i : ι) : (ei i).hom ≫
      sigmaPullbackComponentToPullback X j s i ≫ pullback.snd j s =
        sigmaPullbackComponentToPullback X j t i ≫ pullback.snd j t := by
    let ji := Sigma.ι X i ≫ j
    have : Mono ji := by dsimp [ji]; infer_instance
    let e0 := Subobject.isoOfMkEqMk (pullback.snd ji t) (pullback.snd ji s) (hi i)
    have he0 : e0.hom ≫ pullback.snd ji s = pullback.snd ji t :=
      Subobject.ofMkLEMk_comp (hi i).le
    have hinvS : (sigmaPullbackComponentIso X j s i).inv ≫
        sigmaPullbackComponentToPullback X j s i ≫ pullback.snd j s =
          pullback.snd ji s := by
      rw [← sigmaPullbackComponentIso_snd X j s i]
      simp [ji]
    dsimp [ei, e0]
    calc
      (sigmaPullbackComponentIso X j t i).hom ≫ e0.hom ≫
          (sigmaPullbackComponentIso X j s i).inv ≫
            sigmaPullbackComponentToPullback X j s i ≫ pullback.snd j s =
          (sigmaPullbackComponentIso X j t i).hom ≫ e0.hom ≫
            ((sigmaPullbackComponentIso X j s i).inv ≫
              sigmaPullbackComponentToPullback X j s i ≫ pullback.snd j s) := by
        simp
      _ = (sigmaPullbackComponentIso X j t i).hom ≫ e0.hom ≫ pullback.snd ji s := by
        rw [hinvS]
      _ = (sigmaPullbackComponentIso X j t i).hom ≫ pullback.snd ji t := by rw [he0]
      _ = sigmaPullbackComponentToPullback X j t i ≫ pullback.snd j t :=
        sigmaPullbackComponentIso_snd X j t i
  let eSigma := Limits.Sigma.mapIso ei
  let E := eT.symm ≪≫ eSigma ≪≫ eS
  have hdesc : eSigma.hom ≫
      Limits.Sigma.desc (fun i ↦ (sigmaPullbackComponentIso X j s i).hom ≫
        pullback.snd (Sigma.ι X i ≫ j) s) =
      Limits.Sigma.desc (fun i ↦ (sigmaPullbackComponentIso X j t i).hom ≫
        pullback.snd (Sigma.ι X i ≫ j) t) := by
    have hei' (i : ι) : (ei i).hom ≫ (sigmaPullbackComponentIso X j s i).hom ≫
        pullback.snd (Sigma.ι X i ≫ j) s =
          (sigmaPullbackComponentIso X j t i).hom ≫
            pullback.snd (Sigma.ι X i ≫ j) t := by
      calc
        _ = (ei i).hom ≫ sigmaPullbackComponentToPullback X j s i ≫
            pullback.snd j s := by rw [sigmaPullbackComponentIso_snd]
        _ = sigmaPullbackComponentToPullback X j t i ≫ pullback.snd j t := hei i
        _ = _ := by rw [← sigmaPullbackComponentIso_snd]
    refine Limits.Sigma.hom_ext _ _ fun i ↦ ?_
    simpa [eSigma, Category.assoc] using hei' i
  have hfac : E.hom ≫ pullback.snd j s = pullback.snd j t := by
    refine (cancel_epi eT.hom).1 ?_
    calc
      eT.hom ≫ E.hom ≫ pullback.snd j s =
          eSigma.hom ≫ eS.hom ≫ pullback.snd j s := by simp [E]
      _ = eSigma.hom ≫ Limits.Sigma.desc (fun i ↦
          (sigmaPullbackComponentIso X j s i).hom ≫
            pullback.snd (Sigma.ι X i ≫ j) s) := by rw [hS]
      _ = Limits.Sigma.desc (fun i ↦ (sigmaPullbackComponentIso X j t i).hom ≫
          pullback.snd (Sigma.ι X i ≫ j) t) := hdesc
      _ = eT.hom ≫ pullback.snd j t := hT.symm
  rw [subobject_pullback_obj_eq_iff]
  exact Subobject.mk_eq_mk_of_comm (pullback.snd j t) (pullback.snd j s) E hfac

/-- The part of the thickening lying over the open chosen at stage `n`: the scheme-theoretic
intersection of that open with the `n`-th Fitting closed subscheme. -/
noncomputable abbrev layerFittingPiece {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (n : ULift.{u} ℕ) : Scheme.{u} :=
  pullback (layerPiece G n.down).ι (finiteStratification G n.down).subschemeι

/-- The projection of the stage `n` part of the thickening to the open chosen at stage `n`. -/
noncomputable abbrev layerFittingProj {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (n : ULift.{u} ℕ) :
    layerFittingPiece G n ⟶ (layerPiece G n.down).toScheme :=
  pullback.fst (layerPiece G n.down).ι (finiteStratification G n.down).subschemeι

/-- The invariant closed thickening inside the union of the chosen opens: the coproduct, over
the stages, of the scheme-theoretic intersections of the chosen opens with the corresponding
members of the Fitting stratification. -/
noncomputable abbrev layerThickening {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] : Scheme.{u} :=
  ∐ layerFittingPiece G

/-- The canonical closed immersion of the thickening into the union of the chosen opens. -/
noncomputable def layerThickeningInclusion {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] :
    layerThickening G ⟶ (layerUnionOpen G).toScheme :=
  Limits.Sigma.map (layerFittingProj G) ≫ (layerUnionCoproductIso G).hom

/-- The inclusion of the thickening, described on the coproduct of its stages. -/
theorem layerThickeningInclusion_eq_sigmaDesc {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] :
    layerThickeningInclusion G =
      Limits.Sigma.desc fun n ↦ layerFittingProj G n ≫ layerPieceToUnion G n.down := by
  refine Limits.Sigma.hom_ext _ _ fun n ↦ ?_
  rw [Limits.Sigma.ι_comp_desc, layerThickeningInclusion, ← Category.assoc, Limits.Sigma.ι_map,
    Category.assoc, layerUnionCoproductIso_ι]

/-- On the stage `n`, the inclusion of the thickening into the object scheme is the inclusion of
the intersection of the open chosen at stage `n` with the `n`-th Fitting closed subscheme. -/
theorem sigmaι_comp_layerThickeningInclusion_ι {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (n : ULift.{u} ℕ) :
    Limits.Sigma.ι (layerFittingPiece G) n ≫
        layerThickeningInclusion G ≫ (layerUnionOpen G).ι =
      layerFittingProj G n ≫ (layerPiece G n.down).ι := by
  rw [layerThickeningInclusion_eq_sigmaDesc, ← Category.assoc, Limits.Sigma.ι_comp_desc,
    Category.assoc, layerPieceToUnion_comp_ι]

/-- The inclusion of the thickening is a closed immersion. -/
instance isClosedImmersion_layerThickeningInclusion {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] :
    IsClosedImmersion (layerThickeningInclusion G) := by
  have hSigmaClosed : IsClosedImmersion (Limits.Sigma.map (layerFittingProj G)) :=
    sigmaMap_property_of_components (@IsClosedImmersion : MorphismProperty Scheme.{u}) _ _ _
      fun n ↦ (layerFitting_thickening G n.down).1
  rw [layerThickeningInclusion]
  infer_instance

/-- The inclusion of the thickening into the union of the chosen opens is a thickening: it is
surjective because each chosen open lies inside the corresponding rank stratum. -/
theorem isThickening_layerThickeningInclusion {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] :
    IsThickening (layerThickeningInclusion G) := by
  have hSigmaSurj : Surjective (Limits.Sigma.map (layerFittingProj G)) :=
    sigmaMap_property_of_components (@Surjective : MorphismProperty Scheme.{u}) _ _ _
      fun n ↦ ⟨(layerFitting_thickening G n.down).2⟩
  refine ⟨inferInstance, ?_⟩
  rw [layerThickeningInclusion]
  exact (Limits.Sigma.map (layerFittingProj G) ≫ (layerUnionCoproductIso G).hom).surjective

/-- The composite of the inclusion of the thickening with the inclusion of the union of the
chosen opens is a monomorphism. -/
instance mono_layerThickeningInclusion_comp_ι {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] :
    Mono (layerThickeningInclusion G ≫ (layerUnionOpen G).ι) :=
  inferInstance

/-- The thickening is an invariant monomorphism into the object scheme: each of its stages is
the meet of an invariant open with an invariant closed subscheme. -/
theorem isInvariantMonomorphism_layerThickeningInclusion {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFinite G.source.left] [IsFinite G.target.left] :
    IsInvariantMonomorphism G (layerThickeningInclusion G ≫ (layerUnionOpen G).ι) :=
  subobject_pullback_sigma_eq_of_forall (X := layerFittingPiece G)
    (j := layerThickeningInclusion G ≫ (layerUnionOpen G).ι) (t := G.target.left)
    (s := G.source.left) fun n ↦ by
      simpa only [sigmaι_comp_layerThickeningInclusion_ι] using
        isInvariantMonomorphism_layerFitting G n.down

/-- Pulling the source map back along the thickening gives a finite locally free morphism. -/
theorem finiteLocallyFree_pullback_source_layerThickening {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFinite G.source.left] [IsFinite G.target.left] :
    IsFiniteLocallyFree (pullback.snd G.source.left
      (layerThickeningInclusion G ≫ (layerUnionOpen G).ι)) := by
  set j := layerThickeningInclusion G ≫ (layerUnionOpen G).ι with hj
  have hLocalSource (n : ULift.{u} ℕ) :
      IsFiniteLocallyFree
        (pullback.snd G.source.left (Limits.Sigma.ι (layerFittingPiece G) n ≫ j)) := by
    rw [hj, sigmaι_comp_layerThickeningInclusion_ι, pullback.condition]
    exact layerFittingPullback_source_finiteLocallyFree G n.down
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsFiniteLocallyFree)
    (sigmaOpenCover (layerFittingPiece G))
  intro n
  exact (snd_comp_mem_iff (@IsFiniteLocallyFree : MorphismProperty Scheme.{u}) _ _ _).mp
    (hLocalSource n)

/-- **Stacks Project, Tag 0ABA.** A groupoid scheme with finite source and target has an
invariant open subscheme `W` carrying an invariant closed thickening `W'` such that the source
and target maps of the restriction of the groupoid to `W'` are finite locally free, and such
that the saturation of the closure of `W` is the whole object scheme. -/
@[stacks 0ABA]
public theorem exists_invariant_thickening_finiteLocallyFree_restriction {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFinite G.source.left] [IsFinite G.target.left] :
    ∃ (W : G.objects.left.Opens) (W' : Scheme.{u}) (i : W' ⟶ W.toScheme)
      (hmono : Mono (i ≫ W.ι)),
      letI : Mono (i ≫ W.ι) := hmono
      IsInvariantOpen G W ∧
      IsInvariantMonomorphism G (i ≫ W.ι) ∧
      (G.target.left.base ''
        (G.source.left.base ⁻¹' closure (W : Set G.objects.left)) = Set.univ) ∧
      IsThickening i ∧
      (let g : Over.mk (i ≫ W.ι ≫ G.objects.hom) ⟶ G.objects := Over.homMk (i ≫ W.ι)
       IsFiniteLocallyFree (restrictionSource G g).left ∧
       IsFiniteLocallyFree (restrictionTarget G g).left) := by
  let j := layerThickeningInclusion G ≫ (layerUnionOpen G).ι
  let g : Over.mk (j ≫ G.objects.hom) ⟶ G.objects := Over.homMk j
  have hSrc : IsFiniteLocallyFree (restrictionSource G g).left :=
    restrictionSource_mem_of_isInvariantMonomorphism G g
      (isInvariantMonomorphism_layerThickeningInclusion G)
      (@IsFiniteLocallyFree : MorphismProperty Scheme.{u})
      (finiteLocallyFree_pullback_source_layerThickening G)
  refine ⟨layerUnionOpen G, layerThickening G, layerThickeningInclusion G, inferInstance, ?_⟩
  change IsInvariantOpen G (layerUnionOpen G) ∧ IsInvariantMonomorphism G j ∧
    (G.target.left.base '' (G.source.left.base ⁻¹'
      closure (layerUnionOpen G : Set G.objects.left)) = Set.univ) ∧
    IsThickening (layerThickeningInclusion G) ∧
    (IsFiniteLocallyFree (restrictionSource G g).left ∧
      IsFiniteLocallyFree (restrictionTarget G g).left)
  exact ⟨layerUnion_invariant G, isInvariantMonomorphism_layerThickeningInclusion G,
    saturation_closure_layerUnion_eq_univ G, isThickening_layerThickeningInclusion G, hSrc,
    restrictionTarget_mem_of_restrictionSource_mem G g
      (@IsFiniteLocallyFree : MorphismProperty Scheme.{u}) hSrc⟩

end AlgebraicGeometry

end
