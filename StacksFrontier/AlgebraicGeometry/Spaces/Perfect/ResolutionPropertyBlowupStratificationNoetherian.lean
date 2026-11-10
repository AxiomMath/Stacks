module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubspaceReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyBlowupStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalFirstOrderThickening

/-!
# Step 2 of Stacks 0GV6: the filtration of a Noetherian algebraic space

Stacks 0GV6 asserts that a quasi-compact, quasi-separated algebraic space `X` over a scheme `S`
carries a chain of closed subspaces `X ⊇ Z₀ ⊇ Z₁ ⊇ ⋯ ⊇ Z_t = ∅` with each `Z_i → X` of finite
presentation, with `Z₀ ⊆ X` a thickening, and with, for every `i < t`, a
`(Z_i ∖ Z_{i+1})`-admissible blowing up `Z'_i → Z_i` such that `Z'_i` has the resolution
property.  Its proof has two steps: Step 1 reduces to the case of finite presentation over
`Spec ℤ` by absolute Noetherian approximation, and Step 2 treats a Noetherian `X` by induction
inside `|X|`.

**This file is Step 2, and Step 2 only.**  Its main result,
`AlgebraicGeometry.Space.isResolutionBlowupStratified_top_of_isNoetherian`, is the source's
Step 2 statement for statement: for `X` *Noetherian* in the sense of Stacks 03EA
(`AlgebraicGeometry.Space.IsNoetherian`: quasi-compact, quasi-separated and locally
Noetherian), the chain of Stacks 0GV6 exists.  It does **not** claim Stacks 0GV6, and nothing
here carries a tag.

## Two hypotheses are carried, and both are named here

**(1) Stacks 0GV5 is an explicit hypothesis.**  Every statement below that produces a chain
takes the conclusion of Stacks 0GV5 — for a quasi-compact, quasi-separated algebraic space
whose point space has finitely many irreducible components, a dense quasi-compact open `U` and
a `U`-admissible blowing up with the resolution property — as a hypothesis `h0GV5`, universally
quantified over the algebraic space it is applied to (the induction applies it to each stratum,
not only to `X`).  Stacks 0GV5 is **not proved in this library**; it is being proved on a
separate branch, and the hypothesis is written in exactly the shape of that statement so that
these results compose with it unedited once it lands.  The quantified form is the only addition
to the shape: the hypothesis is
`∀ X, IsQuasiCompactSpace … → IsAbsolutelyQuasiSeparated … → (irreducibleComponents …).Finite →
∃ U, …`, which is Stacks 0GV5's own binders with its three hypotheses turned into arrows.

**(2) `X` is Noetherian.**  This is *not* a weakening of Step 2 — it is Step 2's own
hypothesis, the one Step 1 establishes by absolute Noetherian approximation (Stacks 07SU) and
ascent of the resolution property along affine morphisms (Stacks 0GUU).  **Step 1 is not
assembled in this library**, so the unqualified statement of Stacks 0GV6, for a merely
quasi-compact quasi-separated `X`, does not follow from what is here.  What Step 1 still needs
beyond Stacks 07SU and 0GUU is a comparison of a whole stratification and its blowup centres
along the affine morphism `X ⟶ X₀`; the one ingredient of it the library was missing,
"the strict transform of an affine morphism is affine", is now
`AlgebraicGeometry.Space.isAffineHom_strictTransformSpaceToBlowUp` in
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformAffineHom.lean`.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentation_ι_of_isClosedSubspace_of_isLocallyNoetherian`:
  on a locally Noetherian algebraic space every closed subspace is of finite presentation.
  This is what makes the strata of the induction legitimate members of the chain.
* `AlgebraicGeometry.Space.isResolutionBlowupStratified_top_of_isNoetherian`: **Step 2** — a
  Noetherian algebraic space is stratified in the sense of
  `AlgebraicGeometry.Space.IsResolutionBlowupStratified`, given Stacks 0GV5.
* `exists_closedFiltration_admissibleBlowups_resolutionProperty_of_isNoetherian`, in the
  `AlgebraicGeometry.Space` namespace: the same, unpacked into the words of Stacks 0GV6 — a
  thickening `Z₀ ⊆ X`, an empty last member, finite presentation of every `Z_i ⟶ X` and the
  admissible blowups with the resolution property.

## Implementation notes

**The induction is Noetherian induction on `|W|`, not induction on `dim |X|`.**  The source
inducts on the dimension of `|X|`, which for a Noetherian space of finite dimension is
available here — `IsNowhereDense.toNat_unbotD_topologicalKrullDim_lt` of
`StacksFrontier/Topology/Dimension/NowhereDense.lean` is exactly the dimension drop for the
complement of a dense open, since that complement is closed with empty interior.  The
well-founded recursion on `TopologicalSpace.Closeds (points B S hS X.1)` used below is the same
induction with one fewer input: it needs only that `|X|` is a Noetherian space (Stacks 04ZF,
`AlgebraicGeometry.Space.noetherianSpace_of_isQuasiCompact_of_isLocallyNoetherian`) and the
strict inclusion `|Z₁| ⊊ |Z₀|`, and not the finite-dimensionality that the dimension form's
strict inequality needs as a side condition.  The strict inclusion is immediate: the open `U`
of Stacks 0GV5 is dense, hence nonempty as soon as the stratum has a point, and the empty
stratum is the base case.

**The strata live in the ambient `X`.**  As in
`AlgebraicGeometry.Space.IsResolutionBlowupStratified` itself, the chain's members are
subfunctors of `X`, so the induction never transports a subfunctor across a closed immersion.
What *is* transported is the datum of Stacks 0GV5: it is produced on the algebraic space
`⟨W.toFunctor, _⟩` of the stratum, which is exactly the shape
`AlgebraicGeometry.Space.IsResolutionBlowupStratified.prepend` consumes, and only the *point
set* of the open `U` is read in `X`, along the closed embedding
`AlgebraicGeometry.Space.isEmbedding_pointsMap_of_isImmersion` (Stacks 0ABJ).

**`Z₁` is the reduced closed subspace of `X` on `|W| ∖ |U|`.**  The source takes the reduced
induced structure on the complement, and so does this file — but on the complement measured in
`X`, as `AlgebraicGeometry.Space.reducedClosedSubspace` of `X` (Stacks 03IQ), rather than as
`AlgebraicGeometry.Space.openComplementReducedSubspace` of the stratum.  The two agree, and the
`X`-side spelling is the one whose containment in the stratum is a lemma the library already
has: `AlgebraicGeometry.Space.reducedClosedSubspace_mono` followed by
`AlgebraicGeometry.Space.reducedClosedSubspace_le_of_isClosedSubspace`.  The source's final
re-indexing remark, that reducedness of `Z₁` gives `Z₁ = Z_{1,0}`, is not needed: the chain
predicate asks only that its first member be a thickening of the subfunctor it is a chain over,
which `prepend` discharges.

**The module universe is fixed at `{u, u}`**, as in every resolution-property result of
this library and in `AlgebraicGeometry.Space.IsResolutionBlowupStratified`.

## References

* [Stacks Project, Tag 0GV6](https://stacks.math.columbia.edu/tag/0GV6)
* [Stacks Project, Tag 0GV5](https://stacks.math.columbia.edu/tag/0GV5)
* [Stacks Project, Tag 03EA](https://stacks.math.columbia.edu/tag/03EA)
* [Stacks Project, Tag 04ZF](https://stacks.math.columbia.edu/tag/04ZF)
* [Stacks Project, Tag 084Q](https://stacks.math.columbia.edu/tag/084Q)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 0ABJ](https://stacks.math.columbia.edu/tag/0ABJ)
* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
* [Stacks Project, Tag 0GUU](https://stacks.math.columbia.edu/tag/0GUU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Closed subspaces of a locally Noetherian algebraic space -/

/-- **On a locally Noetherian algebraic space every closed subspace is of finite presentation.**
By Stacks 084Q the inclusion of a closed subspace is of finite presentation exactly when the
ideal it cuts out on a surjective étale scheme chart is finitely generated over every affine
open of the chart; local Noetherianity of the chart furnished by Stacks 03E6 makes every such
ideal finitely generated. -/
theorem isFinitePresentation_ι_of_isClosedSubspace_of_isLocallyNoetherian
    (X : AlgebraicSpaces B S hS)
    (hN : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (G : Subfunctor X.1) (hG : IsClosedSubspace B S hS G) :
    IsFinitePresentation B S hS G.ι := by
  obtain ⟨V, a, hasurj, haetale, hVN⟩ := hN
  refine (isFinitePresentation_iff_fg_ker_of_surjectiveEtaleChart B S hS
    (Z := ⟨G.toFunctor, hG.1⟩) (ObjectProperty.homMk G.ι) hG.2 haetale hasurj).2 fun A => ?_
  have := hVN.component_noetherian A
  exact _root_.IsNoetherian.noetherian _

/-! ### Step 2 of the proof of Stacks 0GV6 -/

/-- **Step 2 of the proof of Stacks 0GV6.**  A Noetherian algebraic space over `S` — Stacks
03EA: quasi-compact, quasi-separated and locally Noetherian — carries the chain of Stacks 0GV6,
given the conclusion of Stacks 0GV5.

Two hypotheses are carried, and neither weakens Step 2.  `h0GV5` is the conclusion of Stacks
0GV5, which this library does not prove, written in the shape of that statement and quantified
over the algebraic space it is applied to, because the induction applies it to every stratum.
`hX` is Step 2's own Noetherian hypothesis, which Step 1 of the source's proof establishes for
a general quasi-compact quasi-separated space by absolute Noetherian approximation; Step 1 is
not assembled in this library, so Stacks 0GV6 itself does not follow from this.  See the module
documentation.

The induction is Noetherian induction on the closed point set of the stratum.  Given a closed
subspace `W` of `X` with a point, Stacks 0GV5 on the algebraic space of `W` produces a dense
quasi-compact open `U ⊆ W` and a `U`-admissible blowing up of `W` with the resolution property;
`W₁` is the reduced closed subspace of `X` on `|W| ∖ |U|`, whose point set is strictly smaller
than `|W|` because `U` is dense and `W` has a point, so the induction hypothesis stratifies
`W₁`, and `AlgebraicGeometry.Space.IsResolutionBlowupStratified.prepend` prepends `W`.  A
closed subspace with no points is stratified by the chain of length `0` constant at the reduced
closed subspace of `X` on the empty set. -/
theorem isResolutionBlowupStratified_top_of_isNoetherian
    (h0GV5 : ∀ X : AlgebraicSpaces B S hS, IsQuasiCompactSpace B S hS X.1 →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1 →
      (irreducibleComponents (points B S hS X.1)).Finite →
      ∃ U : OpenSubspaces B S hS X.1, IsQuasiCompactSpace B S hS U.1.toFunctor ∧
        Dense (subspacePointSet B S hS X.1 U.1) ∧
          ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X), IsAdmissibleBlowup B S hS U b ∧
            HasResolutionProperty.{u, u} B S hS X'.1 X'.2)
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS B.contains_terminal X.1) :
    IsResolutionBlowupStratified B S hS X ⊤ := by
  have hNpts : TopologicalSpace.NoetherianSpace (points B S hS X.1) :=
    noetherianSpace_of_isQuasiCompact_of_isLocallyNoetherian B S hS X.1 X.2 hX.1 hX.2.2
  -- every closed subspace of `X` is of finite presentation over `X`
  have hfp : ∀ G : Subfunctor X.1, IsClosedSubspace B S hS G →
      IsFinitePresentation B S hS G.ι := fun G hG =>
    isFinitePresentation_ι_of_isClosedSubspace_of_isLocallyNoetherian B S hS X hX.2.2 G hG
  -- the point set of a closed subspace is a closed subset of `|X|`, homeomorphically
  have hemb : ∀ G : Subfunctor X.1, IsClosedSubspace B S hS G →
      Topology.IsClosedEmbedding (pointsMap B S hS G.toFunctor G.ι) := fun G hG =>
    ⟨isEmbedding_pointsMap_of_isImmersion B S hS X.2 G.ι
        (isImmersion_of_isClosedImmersion B S hS hG.2),
      isClosed_range_pointsMap_of_isClosedImmersion B S hS X.2 G.ι hG.2⟩
  suffices H : ∀ C : TopologicalSpace.Closeds (points B S hS X.1), ∀ W : Subfunctor X.1,
      IsClosedSubspace B S hS W → subspacePointSet B S hS X.1 W = (C : Set _) →
      IsResolutionBlowupStratified B S hS X W by
    exact H ⟨_, (hemb ⊤ (isClosedSubspace_top B S hS X)).isClosed_range⟩ ⊤
      (isClosedSubspace_top B S hS X) rfl
  intro C
  induction C using WellFoundedLT.induction with
  | _ C IH =>
  intro W hW hWC
  by_cases hne : (subspacePointSet B S hS X.1 W).Nonempty
  case neg =>
    -- the base case: a stratum with no points, stratified by the chain of length `0` constant
    -- at the reduced closed subspace of `X` on the empty set
    have hemp : subspacePointSet B S hS X.1 W = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hZcl : IsClosedSubspace B S hS
        (reducedClosedSubspace B S hS X.1 X.2 (∅ : Set (points B S hS X.1)) isClosed_empty) :=
      isClosedSubspace_reducedClosedSubspace B S hS X.1 X.2 _ _
    have hZpts : subspacePointSet B S hS X.1
        (reducedClosedSubspace B S hS X.1 X.2 (∅ : Set (points B S hS X.1)) isClosed_empty) =
          ∅ :=
      range_pointsMap_ι_reducedClosedSubspace B S hS X.1 X.2 _ _
    refine ⟨0, fun _ =>
      reducedClosedSubspace B S hS X.1 X.2 (∅ : Set (points B S hS X.1)) isClosed_empty,
      fun _ => hZcl, fun _ => hfp _ hZcl, fun _ => le_rfl, ?_, by rw [hZpts, hemp], hZpts,
      fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    exact (reducedClosedSubspace_mono B S hS X.2 _ _ isClosed_empty _
      (Set.empty_subset _)).trans
      (reducedClosedSubspace_le_of_isClosedSubspace B S hS X.2 W hW)
  -- the stratum has a point: the datum of Stacks 0GV5 on its algebraic space
  have hWne : Nonempty (points B S hS W.toFunctor) := Set.range_nonempty_iff_nonempty.mp hne
  have hWN : TopologicalSpace.NoetherianSpace (points B S hS W.toFunctor) :=
    (hemb W hW).isInducing.noetherianSpace
  obtain ⟨U, -, hUdense, Y, f, hf, hres⟩ :=
    h0GV5 ⟨W.toFunctor, hW.1⟩
      (isQuasiCompactSpace_of_isClosedImmersion B S hS hX.1 W.ι hW.2)
      (isAbsolutelyQuasiSeparated_of_mono B S hS B.contains_terminal hW.1 W.ι inferInstance
        hX.2.1)
      (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
        (α := points B S hS W.toFunctor))
  -- the point set of `U`, measured in `X`
  have hVeq : Set.range (pointsMap B S hS U.1.toFunctor (U.1.ι ≫ W.ι)) =
      pointsMap B S hS W.toFunctor W.ι '' subspacePointSet B S hS W.toFunctor U.1 := by
    rw [pointsMap_comp, Set.range_comp]
  have hVsub : Set.range (pointsMap B S hS U.1.toFunctor (U.1.ι ≫ W.ι)) ⊆
      subspacePointSet B S hS X.1 W := by
    rw [hVeq]
    exact Set.image_subset_range _ _
  have hUopen : IsOpen (subspacePointSet B S hS W.toFunctor U.1) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS U.1.ι U.2.2
  -- `|W| ∖ |U|` is a closed subset of `|X|`
  have hTclosed : IsClosed (subspacePointSet B S hS X.1 W \
      Set.range (pointsMap B S hS U.1.toFunctor (U.1.ι ≫ W.ι))) := by
    have hTeq : subspacePointSet B S hS X.1 W \
        Set.range (pointsMap B S hS U.1.toFunctor (U.1.ι ≫ W.ι)) =
          pointsMap B S hS W.toFunctor W.ι ''
            (subspacePointSet B S hS W.toFunctor U.1)ᶜ := by
      rw [hVeq, Set.compl_eq_univ_sdiff, Set.image_sdiff (hemb W hW).injective, Set.image_univ]
    rw [hTeq]
    exact (hemb W hW).isClosedMap _ hUopen.isClosed_compl
  -- `W₁`, the reduced closed subspace of `X` on `|W| ∖ |U|`
  have hW₁cl : IsClosedSubspace B S hS
      (reducedClosedSubspace B S hS X.1 X.2 _ hTclosed) :=
    isClosedSubspace_reducedClosedSubspace B S hS X.1 X.2 _ _
  have hW₁pts : subspacePointSet B S hS X.1
      (reducedClosedSubspace B S hS X.1 X.2 _ hTclosed) =
        subspacePointSet B S hS X.1 W \
          Set.range (pointsMap B S hS U.1.toFunctor (U.1.ι ≫ W.ι)) :=
    range_pointsMap_ι_reducedClosedSubspace B S hS X.1 X.2 _ _
  have hW₁W : reducedClosedSubspace B S hS X.1 X.2 _ hTclosed ≤ W :=
    (reducedClosedSubspace_mono B S hS X.2 _ _ hTclosed _ Set.sdiff_subset).trans
      (reducedClosedSubspace_le_of_isClosedSubspace B S hS X.2 W hW)
  -- the point set of `W₁` is strictly smaller than that of `W`, because `U` is dense and
  -- nonempty
  obtain ⟨x, hx⟩ := hUdense.nonempty
  have hlt : (⟨_, hTclosed⟩ : TopologicalSpace.Closeds (points B S hS X.1)) < C := by
    refine lt_of_le_of_ne (SetLike.coe_subset_coe.mp (hWC ▸ Set.sdiff_subset)) fun h => ?_
    have hmem : pointsMap B S hS W.toFunctor W.ι x ∈ (C : Set _) :=
      hWC ▸ hVsub (hVeq ▸ Set.mem_image_of_mem _ hx)
    rw [← h] at hmem
    exact hmem.2 (hVeq ▸ Set.mem_image_of_mem _ hx)
  refine IsResolutionBlowupStratified.prepend hW (hfp W hW) le_rfl rfl hW₁W U ?_ f hf hres
    (IH _ hlt _ hW₁cl hW₁pts)
  rw [hW₁pts, Set.sdiff_sdiff_right_self, Set.inter_eq_self_of_subset_right hVsub]

/-- **The chain of Step 2 of Stacks 0GV6, in the words of the source.**  For a Noetherian
algebraic space `X` over `S` — Stacks 03EA — and given the conclusion of Stacks 0GV5, there are
closed subspaces `Z₀ ⊇ Z₁ ⊇ ⋯ ⊇ Z_t` of `X`, each of finite presentation over `X`, with
`Z₀ ⊆ X` a thickening in the sense of Stacks 05ZK part (1), with `Z_t` the empty algebraic
space, and with a `(Z_i ∖ Z_{i+1})`-admissible blowing up of `Z_i` whose source has the
resolution property for every `i < t`.

This is the conclusion of Stacks 0GV6 under Step 2's Noetherian hypothesis.  Both hypotheses
are carried and neither weakens Step 2: `h0GV5` is the unproved Stacks 0GV5 in exactly its own
shape, and `hX` is Step 2's Noetherian hypothesis, which the unassembled Step 1 of the source's
proof supplies for a general quasi-compact quasi-separated space.  See the module
documentation. -/
theorem exists_closedFiltration_admissibleBlowups_resolutionProperty_of_isNoetherian
    (h0GV5 : ∀ X : AlgebraicSpaces B S hS, IsQuasiCompactSpace B S hS X.1 →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1 →
      (irreducibleComponents (points B S hS X.1)).Finite →
      ∃ U : OpenSubspaces B S hS X.1, IsQuasiCompactSpace B S hS U.1.toFunctor ∧
        Dense (subspacePointSet B S hS X.1 U.1) ∧
          ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X), IsAdmissibleBlowup B S hS U b ∧
            HasResolutionProperty.{u, u} B S hS X'.1 X'.2)
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS B.contains_terminal X.1) :
    ∃ (t : ℕ) (Z : ℕ → Subfunctor X.1) (hZ : ∀ i, IsClosedSubspace B S hS (Z i)),
      (∀ i, IsFinitePresentation B S hS (Z i).ι) ∧
      (∀ i, Z (i + 1) ≤ Z i) ∧
      IsThickening B S hS X (Z 0) ∧
      IsEmpty (points B S hS (Z t).toFunctor) ∧
      ∀ i < t, ∃ (U : OpenSubspaces B S hS (Z i).toFunctor) (Y : AlgebraicSpaces B S hS)
          (f : Y ⟶ (⟨(Z i).toFunctor, (hZ i).1⟩ : AlgebraicSpaces B S hS)),
        Set.range (pointsMap B S hS U.1.toFunctor (U.1.ι ≫ (Z i).ι)) =
            subspacePointSet B S hS X.1 (Z i) \ subspacePointSet B S hS X.1 (Z (i + 1)) ∧
          IsAdmissibleBlowup B S hS U f ∧
          HasResolutionProperty.{u, u} B S hS Y.1 Y.2 :=
  exists_thickening_filtration_of_isResolutionBlowupStratified_top
    (isResolutionBlowupStratified_top_of_isNoetherian B S hS h0GV5 X hX)

end AlgebraicGeometry.Space

end
