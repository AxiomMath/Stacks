module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksCore.Tactic.StacksAttribute

/-!
# Recognizing fpqc coverings

A family of morphisms of schemes is an fpqc covering precisely when its members are flat
and every affine open of the target is a union of images of an almost-everywhere empty
family of quasi-compact opens.  It is enough to exhibit such finite families over the
members of a single affine open covering, and for a quasi-separated target there is a
pointwise neighbourhood criterion.  A flat family is also fpqc as soon as it admits a
standard fpqc refinement after every base change to an affine scheme.  Finally, being an
fpqc covering is itself local on an fpqc covering of the target: a flat family which base
changes to an fpqc covering over every member of some fpqc covering of the target is already
an fpqc covering.

## Main results

* `AlgebraicGeometry.mem_fpqcPrecoverage_iff_affine_finite_support`: a family lies in Mathlib's
  `Scheme.fpqcPrecoverage` if and only if it is flat and every affine open of the target is the
  union of the images of quasi-compact opens, all but finitely many of them empty.
* `AlgebraicGeometry.mem_fpqcPrecoverage_iff_exists_affine_open_cover`: the same with finitely
  many quasi-compact opens over each member of some affine open covering of the target.
* `AlgebraicGeometry.mem_fpqcPrecoverage_iff_pointwise_compact_open_neighborhood`: for a
  quasi-separated target, the same with a neighbourhood of every point in place of an affine
  open.

The forms of these equivalences with the Stacks 022B notion of fpqc covering
(`IsFpqcCoveringFamily`) as condition (1), and the bridge between that notion and
`Scheme.fpqcPrecoverage`, are in `StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.CoveringFamily`.
* `AlgebraicGeometry.presieve₀_mem_fpqcPrecoverage_of_affine_refinements`: the criterion by
  refinements after affine base change.
* `AlgebraicGeometry.ofArrows_mem_fpqcPrecoverage_of_fpqc_locally`: being an fpqc covering is
  local on an fpqc covering of the target.

## References

* [Stacks Project, Tag 03L7](https://stacks.math.columbia.edu/tag/03L7)
* [Stacks Project, Tag 03LB](https://stacks.math.columbia.edu/tag/03LB)
* [Stacks Project, Tag 03L9](https://stacks.math.columbia.edu/tag/03L9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TopologicalSpace

universe u v

namespace AlgebraicGeometry

section Characterization

variable {T : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ T)

/-- A subset of `V` whose preimage under `g` is compact in the subtype `V` has compact
intersection with `V`. -/
private lemma isCompact_inter_preimage_of_isCompact_subtype {Y T : Type*} [TopologicalSpace Y]
    [TopologicalSpace T] (g : Y → T) (V : Set Y) (W : Set T)
    (h : IsCompact ((fun x : V => g x.1) ⁻¹' W)) : IsCompact (V ∩ g ⁻¹' W) := by
  convert h.image continuous_subtype_val using 1
  ext x
  simp [and_comm]

private lemma compact_inter_preimage_of_affine
    {Y : Scheme.{u}} (g : Y ⟶ T) (U : T.Opens) (V : Y.Opens) (W : T.Opens)
    (hU : IsAffineOpen U)
    (hV : IsCompact (V : Set Y)) (hVU : V ≤ g ⁻¹ᵁ U)
    (hW : IsCompact (W : Set T)) (hWU : W ≤ U) :
    IsCompact ((V : Set Y) ∩ g ⁻¹' (W : Set T)) := by
  let r := g.resLE U V hVU
  let W' : U.toScheme.Opens := U.ι ⁻¹ᵁ W
  have hW' : IsCompact (W' : Set U.toScheme) := by
    have himage : (fun x : U.toScheme => x.1) ''
        ((fun x : U.toScheme => x.1) ⁻¹' (W : Set T)) = (W : Set T) := by
      rw [Set.image_preimage_eq_inter_range]
      exact Set.inter_eq_left.mpr fun x hx ↦ ⟨⟨x, hWU hx⟩, rfl⟩
    exact Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr (himage.symm ▸ hW)
  let : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV
  let : IsAffine U.toScheme := hU
  let : QuasiSeparatedSpace U.toScheme := inferInstance
  have hqr : QuasiCompact r := inferInstance
  have hK : IsCompact (r ⁻¹ᵁ W' : Set V.toScheme) :=
    QuasiCompact.isCompact_preimage _ W'.2 hW'
  exact isCompact_inter_preimage_of_isCompact_subtype g V W
    (by
      have : (fun x : V => g x.1) ⁻¹' (W : Set T) = (r ⁻¹ᵁ W' : Set V.toScheme) := by
        ext y
        exact (congrArg (· ∈ W) (Scheme.Hom.coe_resLE_apply (f := g) hVU y)).symm.to_iff
      exact this ▸ hK)

private lemma compact_inter_preimage_of_quasiSeparated
    [QuasiSeparatedSpace T] {Y : Scheme.{u}} (g : Y ⟶ T) (V : Y.Opens)
    (hV : IsCompact (V : Set Y)) (W : T.Opens) (hW : IsCompact (W : Set T)) :
    IsCompact ((V : Set Y) ∩ g ⁻¹' (W : Set T)) := by
  let r := V.ι ≫ g
  let : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV
  have hK : IsCompact (r ⁻¹' (W : Set T)) :=
    QuasiCompact.isCompact_preimage _ W.2 hW
  have hr (y : V.toScheme) : r y = g y.1 := rfl
  exact isCompact_inter_preimage_of_isCompact_subtype g V W hK

/-- Intersecting the opens `V j` with the preimage of `W` cuts the union of their images down
to `W`, provided `W` is contained in that union. -/
private lemma iUnion_image_inf_preimage_eq {ι : Type*} {X : ι → Scheme.{u}} (f : ∀ j, X j ⟶ T)
    (V : ∀ j, (X j).Opens) (W : T.Opens) (h : (W : Set T) ⊆ ⋃ j, f j '' (V j : Set (X j))) :
    ⋃ j, f j '' ((V j ⊓ f j ⁻¹ᵁ W : (X j).Opens) : Set (X j)) = (W : Set T) := by
  simp only [Opens.coe_inf, Scheme.Hom.coe_preimage, Set.image_inter_preimage]
  rw [← Set.iUnion_inter]
  exact Set.inter_eq_right.mpr h

private lemma fpqc_mem_iff_flat_and_compactOpenCovered :
    Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage T ↔
      ((∀ i, Flat (f i)) ∧
        ∀ U : T.Opens, IsAffineOpen U →
          IsCompactOpenCovered (fun i => (f i).base) (U : Set T)) := by
  rw [Scheme.fpqcPrecoverage]
  change (Presieve.ofArrows X f ∈ Scheme.qcPrecoverage T ∧
      Presieve.ofArrows X f ∈ Scheme.precoverage @Flat T) ↔ _
  constructor
  · rintro ⟨hqc, hflat⟩
    have hflat' := (Scheme.ofArrows_mem_precoverage_iff @Flat).mp hflat
    refine ⟨hflat'.2, ?_⟩
    rw [Scheme.qcPrecoverage, Scheme.qcCoverFamily,
      PreZeroHypercoverFamily.mem_precoverage_iff] at hqc
    obtain ⟨E, hE, hEq⟩ := hqc
    intro U hU
    have hE' := (Scheme.quasiCompactCover_iff T E).mp hE
    have hle : E.presieve₀ ≤ Presieve.ofArrows X f := by rw [← hEq]
    have hfac : ∀ j : E.I₀, ∃ i : I, ∃ g : E.X j ⟶ X i, E.f j = g ≫ f i := by
      intro j
      let hmem : Presieve.ofArrows X f (E.f j) := hle _ _ (E.presieve₀_f j)
      let i := hmem.idx
      let g : E.X j ⟶ X i := eqToHom hmem.obj_idx.symm
      refine ⟨i, g, ?_⟩
      simpa [i, g] using hmem.eq_eqToHom_comp_hom_idx
    choose a g hg using hfac
    have hEcov : IsCompactOpenCovered (fun j => (E.f j).base) (U : Set T) :=
      QuasiCompactCover.isCompactOpenCovered_of_isAffineOpen hU
    exact IsCompactOpenCovered.of_comp (g := fun j => (E.f j).base) (a := a)
      (fun j => g j) (fun j => by fun_prop)
      (fun j => by
        funext x
        change (E.f j) x = (f (a j)) ((g j) x)
        exact congrArg (fun q : E.X j ⟶ T => q x) (hg j))
      (fun i => (f i).continuous) U.2 hEcov
  · rintro ⟨hflat, hcov⟩
    let E : PreZeroHypercover.{v} T := ⟨I, X, f⟩
    have hE : QuasiCompactCover E := ⟨fun {U} hU ↦ by simpa [E] using hcov U hU⟩
    have hqc : Presieve.ofArrows X f ∈ Scheme.qcPrecoverage T := by
      change E.presieve₀ ∈ Scheme.qcPrecoverage T
      rw [Scheme.presieve₀_mem_qcPrecoverage_iff]
      exact hE
    have hsurj : ∀ x : T, ∃ i, x ∈ Set.range (f i) := by
      intro x
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      obtain ⟨s, hs, W, hW, hcover⟩ := hcov U hU
      have hxU' : x ∈ ⋃ i, ⋃ hi : i ∈ s, (f i) '' (W i hi : Set (X i)) := by
        rw [hcover]
        exact hxU
      simp only [Set.mem_iUnion, Set.mem_image] at hxU'
      obtain ⟨i, hi, y, hy, hxy⟩ := hxU'
      exact ⟨i, y, hxy⟩
    exact ⟨hqc, (Scheme.ofArrows_mem_precoverage_iff @Flat).mpr ⟨hsurj, hflat⟩⟩

/-- A family lies in Mathlib's `Scheme.fpqcPrecoverage` if and only if
every member is flat and every affine open of the target is the union of the images of
quasi-compact opens in the sources, all but finitely many of which are empty.  The form with
the Stacks 022B notion of fpqc covering is `isFpqcCoveringFamily_iff_affine_finite_support`. -/
public lemma mem_fpqcPrecoverage_iff_affine_finite_support :
    Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage T ↔
      ((∀ i, Flat (f i)) ∧
        (∀ U : T.Opens, IsAffineOpen U →
            ∃ V : ∀ i, (X i).Opens,
              ((∀ i, IsCompact (V i : Set (X i))) ∧
                ({i | V i ≠ ⊥} : Set I).Finite ∧
                ⋃ i, f i '' (V i : Set (X i)) = (U : Set T)))) := by
  rw [fpqc_mem_iff_flat_and_compactOpenCovered]
  constructor
  · rintro ⟨hflat, hcov⟩
    refine ⟨hflat, fun U hU => ?_⟩
    obtain ⟨s, hs, W, hW, hcover⟩ := hcov U hU
    classical
    let V (i : I) : (X i).Opens := if hi : i ∈ s then W i hi else ⊥
    have hVcompact (i : I) : IsCompact (V i : Set (X i)) := by
      dsimp [V]
      split_ifs with hi
      exacts [hW i hi, isCompact_empty]
    have hVfinite : ({i | V i ≠ ⊥} : Set I).Finite :=
      hs.subset fun i hi ↦ by_contra fun hnot ↦ hi (by simp [V, hnot])
    have hEq : (⋃ i, (f i) '' (V i : Set (X i))) =
        ⋃ i, ⋃ hi : i ∈ s, (f i) '' (W i hi : Set (X i)) := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_image]
      constructor
      · rintro ⟨i, y, hy, hxy⟩
        by_cases hi : i ∈ s
        · exact ⟨i, hi, y, by simpa [V, hi] using hy, hxy⟩
        · simp [V, hi] at hy
      · rintro ⟨i, hi, y, hy, hxy⟩
        exact ⟨i, y, by simpa [V, hi] using hy, hxy⟩
    exact ⟨V, hVcompact, hVfinite, hEq.trans hcover⟩
  · rintro ⟨hflat, hU⟩
    refine ⟨hflat, fun U hUaff => ?_⟩
    obtain ⟨V, hV, hs, hcover⟩ := hU U hUaff
    classical
    have hs' : {i | V i ≠ ⊥}.Finite := hs
    let s : Set I := {i | V i ≠ ⊥}
    let : Finite s := hs'.to_subtype
    have hEq : (⋃ j : s, (f j.1) '' (V j.1 : Set (X j.1))) =
        ⋃ i, (f i) '' (V i : Set (X i)) := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_image]
      constructor
      · rintro ⟨j, y, hy, hxy⟩
        exact ⟨j.1, y, hy, hxy⟩
      · rintro ⟨i, y, hy, hxy⟩
        by_cases hi : i ∈ s
        · exact ⟨⟨i, hi⟩, y, hy, hxy⟩
        · have hbot : V i = ⊥ := by simpa [s] using hi
          simp [hbot] at hy
    exact IsCompactOpenCovered.of_finite (fun j : s => j.1) (fun j => V j.1)
      (fun j => hV j.1) (hEq.trans hcover)

/-- A family lies in Mathlib's `Scheme.fpqcPrecoverage` if and only if its
members are flat and some affine open covering of the target is, member by member, the union of
images of finitely many quasi-compact opens in the sources.  The form with the Stacks 022B
notion of fpqc covering is `isFpqcCoveringFamily_iff_exists_affine_open_cover`. -/
public lemma mem_fpqcPrecoverage_iff_exists_affine_open_cover :
    Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage T ↔
      ((∀ i, Flat (f i)) ∧
        ∃ (A : Type u) (U : A → T.Opens),
          ((∀ a, IsAffineOpen (U a)) ∧
            (⋃ a, (U a : Set T)) = Set.univ ∧
            ∀ a, ∃ (n : ℕ) (i : Fin n → I) (V : ∀ j, (X (i j)).Opens),
              ((∀ j, IsCompact (V j : Set (X (i j)))) ∧
                ⋃ j, f (i j) '' (V j : Set (X (i j))) = (U a : Set T)))) := by
  rw [fpqc_mem_iff_flat_and_compactOpenCovered]
  constructor
  · rintro ⟨hflat, hcov⟩
    refine ⟨hflat, T.affineOpens, fun a => a.1, ?_, ?_, ?_⟩
    · exact fun a ↦ a.2
    · refine Set.eq_univ_of_forall fun x ↦ ?_
      obtain ⟨W, hW, hxW, -⟩ :=
        exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : T.Opens) from Set.mem_univ x)
      exact Set.mem_iUnion.mpr ⟨⟨W, hW⟩, hxW⟩
    · intro a
      obtain ⟨n, i, V, hV, hEq⟩ :=
        (hcov a.1 a.2).exists_mem_of_isBasis (fun j => (X j).isBasis_affineOpens)
          (fun j W hW => hW.isCompact)
      exact ⟨n, i, V, fun j => hV j |>.isCompact, hEq⟩
  · rintro ⟨hflat, A, U, hUa, hcover, hfinite⟩
    refine ⟨hflat, fun W hW => ?_⟩
    classical
    choose n i V hV hUa_eq using hfinite
    let J := Σ a : A, {W' : T.Opens // IsAffineOpen W' ∧ W' ≤ W ∧ W' ≤ U a}
    let localOpen (p : J) : T.Opens := p.2.1
    have hJcovers (x : T) (hx : x ∈ W) : ∃ p : J, x ∈ localOpen p := by
      obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hcover x)
      obtain ⟨W', hW', hxW', hW'sub⟩ := exists_isAffineOpen_mem_and_subset
        (show x ∈ W ⊓ U a from ⟨hx, hxa⟩)
      refine ⟨⟨a, ⟨W', hW', hW'sub.trans inf_le_left, hW'sub.trans inf_le_right⟩⟩, hxW'⟩
    have hcoverLocal : (W : Set T) ⊆ ⋃ p : J, (localOpen p : Set T) :=
      fun x hx ↦ Set.mem_iUnion.mpr (hJcovers x hx)
    obtain ⟨s, hsJ, hsFin, hfiniteCover⟩ :=
      hW.isCompact.elim_finite_subcover_image (b := Set.univ)
        (c := fun p => (localOpen p : Set T)) (fun p _ => (localOpen p).2)
        (by simpa using hcoverLocal)
    let : Finite s := hsFin.to_subtype
    have hlocal (p : s) : IsCompactOpenCovered (fun k => (f k).base) (localOpen p.1 : Set T) := by
      rcases p.1 with ⟨a, ⟨W', hW'aff, hWsub, hWa⟩⟩
      have hW'compact : IsCompact (W' : Set T) := hW'aff.isCompact
      let V' (j : Fin (n a)) : (X (i a j)).Opens :=
        V a j ⊓ (f (i a j)) ⁻¹ᵁ W'
      have hV'compact (j : Fin (n a)) : IsCompact (V' j : Set (X (i a j))) := by
        change IsCompact ((V a j : Set (X (i a j))) ∩
          (f (i a j)) ⁻¹' (W' : Set T))
        exact compact_inter_preimage_of_affine (f (i a j)) (U a) (V a j) W'
          (hUa a) (hV a j) (by
            change (V a j : Set (X (i a j))) ⊆ (f (i a j)) ⁻¹' (U a : Set T)
            intro x hx
            have himg : (f (i a j)) '' (V a j : Set (X (i a j))) ⊆ (U a : Set T) := by
              rw [← hUa_eq a]
              exact Set.subset_iUnion_of_subset j Set.Subset.rfl
            exact himg ⟨x, hx, rfl⟩)
          hW'compact hWa
      have hlocalEq :
          ⋃ j, (f (i a j)) '' (V' j : Set (X (i a j))) = (W' : Set T) := by
        exact iUnion_image_inf_preimage_eq (fun j ↦ f (i a j)) (V a) W' (hUa_eq a ▸ hWa)
      exact IsCompactOpenCovered.of_finite (i a) V' hV'compact hlocalEq
    have hWcover : (⋃ p : s, (localOpen p.1 : Set T)) = (W : Set T) := by
      rw [Set.iUnion_subtype]
      exact Set.Subset.antisymm
        (Set.iUnion_subset fun p => Set.iUnion_subset fun hp => p.2.2.2.1)
        hfiniteCover
    exact IsCompactOpenCovered.of_iUnion_eq_of_finite (fun p : s => (localOpen p.1 : Set T))
      hWcover hlocal

/-- If the target is quasi-separated, a family lies in
Mathlib's `Scheme.fpqcPrecoverage` if and only if its members are flat and every point has a
neighborhood which is the union of the images of finitely many quasi-compact opens in the
sources. The neighborhood itself is not required to be open.  The form with the Stacks 022B
notion of fpqc covering is `isFpqcCoveringFamily_iff_pointwise_compact_open_neighborhood`. -/
public lemma mem_fpqcPrecoverage_iff_pointwise_compact_open_neighborhood
    [QuasiSeparatedSpace T] :
    Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage T ↔
      ((∀ i, Flat (f i)) ∧
        ∀ t : T, ∃ (n : ℕ) (i : Fin n → I) (V : ∀ j, (X (i j)).Opens),
          ((∀ j, IsCompact (V j : Set (X (i j)))) ∧
            (⋃ j, f (i j) '' (V j : Set (X (i j)))) ∈ nhds t)) := by
  rw [fpqc_mem_iff_flat_and_compactOpenCovered]
  constructor
  · rintro ⟨hflat, hcov⟩
    refine ⟨hflat, fun t => ?_⟩
    obtain ⟨W, hW, htW, -⟩ :=
      exists_isAffineOpen_mem_and_subset (show t ∈ (⊤ : T.Opens) from Set.mem_univ t)
    obtain ⟨n, i, V, hV, hEq⟩ :=
      (hcov W hW).exists_mem_of_isBasis (fun j => (X j).isBasis_affineOpens)
        (fun j V hV => hV.isCompact)
    refine ⟨n, i, V, fun j => hV j |>.isCompact, ?_⟩
    rw [hEq]
    exact W.2.mem_nhds htW
  · rintro ⟨hflat, hpoint⟩
    refine ⟨hflat, fun U hU => ?_⟩
    exact IsCompactOpenCovered.of_isCompact_of_forall_exists_isCompactOpenCovered
        hU.isCompact (fun x hxU => by
          obtain ⟨n, i, V, hV, hnhds⟩ := hpoint x
          obtain ⟨O, hOS, hO, hxO⟩ := mem_nhds_iff.mp hnhds
          let O' : T.Opens := ⟨O, hO⟩
          obtain ⟨W, hW, hxW, hWO⟩ :=
            exists_isAffineOpen_mem_and_subset
              (show x ∈ O' ⊓ U from ⟨hxO, hxU⟩)
          let V' (j : Fin n) : (X (i j)).Opens := V j ⊓ (f (i j)) ⁻¹ᵁ W
          have hV' (j : Fin n) : IsCompact (V' j : Set (X (i j))) := by
            change IsCompact ((V j : Set (X (i j))) ∩
              (f (i j)) ⁻¹' (W : Set T))
            exact compact_inter_preimage_of_quasiSeparated (f (i j)) (V j) (hV j) W hW.isCompact
          have hEq : ⋃ j, f (i j) '' (V' j : Set (X (i j))) = (W : Set T) := by
            exact iUnion_image_inf_preimage_eq (fun j ↦ f (i j)) V W
              fun y hy => hOS ((hWO hy).1)
          have hWcov : IsCompactOpenCovered (fun i => (f i).base) (W : Set T) :=
            IsCompactOpenCovered.of_finite i V' hV' hEq
          exact ⟨W, hWO.trans inf_le_right, hxW, W.2, hWcov⟩)

end Characterization

section AffineRefinements

/-- A flat family which admits a standard fpqc refinement after every affine base change
is an fpqc covering. -/
@[stacks 03LB, sga "3 IV 6.3.1" "(i) fpqc, sufficiency"]
public lemma presieve₀_mem_fpqcPrecoverage_of_affine_refinements
    {T : Scheme.{u}} (U : PreZeroHypercover.{v} T)
    (hflat : ∀ i, Flat (U.f i))
    (hrefine : ∀ {Z : Scheme.{u}} [IsAffine Z] (h : Z ⟶ T),
      ∃ (V : Z.AffineCover.{0} @Flat), Finite V.I₀ ∧
        Nonempty (V.cover.toPreZeroHypercover.Hom (U.pullback₂ h))) :
    U.presieve₀ ∈ Scheme.fpqcPrecoverage T := by
  classical
  have hqc : QuasiCompactCover U := by
    refine ⟨fun {W} hW ↦ ?_⟩
    have : IsAffine (↑W : Scheme) := hW
    obtain ⟨V, hVfin, ⟨φ⟩⟩ := hrefine W.ι
    let F := V.cover.toPreZeroHypercover
    let a : F.I₀ → U.I₀ := φ.s₀
    let t (j : F.I₀) : F.X j ⟶ U.X (a j) :=
      φ.h₀ j ≫ pullback.fst (U.f (a j)) W.ι
    let family : ∀ i, U.X i → T := fun i ↦ (U.f i).base
    let refined : ∀ j, F.X j → T := fun j ↦ (V.cover.f j ≫ W.ι).base
    have hfactor (j : F.I₀) : t j ≫ U.f (a j) = F.f j ≫ W.ι := by
      have hφ : φ.h₀ j ≫ pullback.snd (U.f (φ.s₀ j)) W.ι = V.cover.f j := by
        simpa [PreZeroHypercover.pullback₂] using φ.w₀ j
      dsimp [t, a]
      calc
        _ = φ.h₀ j ≫ (pullback.fst (U.f (φ.s₀ j)) W.ι ≫ U.f (φ.s₀ j)) :=
          Category.assoc _ _ _
        _ = φ.h₀ j ≫ (pullback.snd (U.f (φ.s₀ j)) W.ι ≫ W.ι) :=
          congrArg (fun k ↦ φ.h₀ j ≫ k) pullback.condition
        _ = _ := (Category.assoc _ _ _).symm.trans (congrArg (fun k ↦ k ≫ W.ι) hφ)
    have hfactor_base (j : F.I₀) :
        refined j = family (a j) ∘ (t j).base := by
      funext x
      simpa [refined, family, Function.comp_apply, Scheme.Hom.comp_base] using
        (congrArg (fun f : F.X j ⟶ T ↦ f.base x) (hfactor j)).symm
    have hcover : (⋃ j, refined j '' (Set.univ : Set (F.X j))) =
        Set.range W.ι.base := by
      ext x
      simp only [Set.image_univ, Set.mem_iUnion, Set.mem_range]
      constructor
      · rintro ⟨j, y, rfl⟩
        exact ⟨V.cover.f j y, by simp [refined, Scheme.Hom.comp_base]⟩
      · rintro ⟨y, rfl⟩
        obtain ⟨z, hz⟩ := V.covers y
        refine ⟨V.idx y, z, ?_⟩
        change W.ι.base ((V.f (V.idx y)).base z) = W.ι.base y
        exact congrArg W.ι.base hz
    let : Finite F.I₀ := hVfin
    have hcovered : IsCompactOpenCovered refined (Set.range W.ι.base) :=
      IsCompactOpenCovered.of_finite (fun j : F.I₀ ↦ j)
        (fun _ ↦ ⟨Set.univ, isOpen_univ⟩) (fun j ↦ by
          change IsCompact (Set.univ : Set (Spec (V.X j)))
          exact isCompact_univ) hcover
    simpa [Scheme.Opens.range_ι] using
      (IsCompactOpenCovered.of_comp (f := family) (U := Set.range W.ι.base)
        (g := refined) (a := a) (t := fun j ↦ (t j).base)
        (fun j ↦ (t j).continuous) hfactor_base (fun i ↦ (U.f i).continuous)
        (IsOpenImmersion.isOpen_range W.ι) hcovered)
  change U.presieve₀ ∈ Scheme.qcPrecoverage T ∧
    U.presieve₀ ∈ Scheme.precoverage (@Flat.{u} : MorphismProperty Scheme.{u}) T
  constructor
  · simpa only [Scheme.presieve₀_mem_qcPrecoverage_iff] using hqc
  · rw [Scheme.presieve₀_mem_precoverage_iff
      (P := (@Flat.{u} : MorphismProperty Scheme.{u}))]
    refine ⟨fun x ↦ ?_, hflat⟩
    obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset
      (U := (⊤ : T.Opens)) (by simp)
    let : QuasiCompactCover U := hqc
    obtain ⟨s, _, O, _, hOeq⟩ := hW.isCompactOpenCovered U
    have hx : x ∈ ⋃ (i : U.I₀) (hi : i ∈ s), (U.f i).base '' (O i hi) := by
      rw [hOeq]; exact hxW
    simp only [Set.mem_iUnion, Set.mem_image] at hx
    obtain ⟨i, hi, y, hy, hxy⟩ := hx
    exact ⟨i, ⟨y, hxy⟩⟩
end AffineRefinements

section Locality

universe w

variable {T : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ T)

private lemma fpqc_mem_iff_qc_and_flat {R : Presieve T} :
    R ∈ Scheme.fpqcPrecoverage T ↔
      R ∈ Scheme.qcPrecoverage T ∧
        R ∈ Scheme.precoverage (@Flat.{u} : MorphismProperty Scheme.{u}) T :=
  Iff.rfl

/-- Being an fpqc covering is local on an fpqc covering of the base. If every
member of a family `f i : X i ⟶ T` is flat and there is an fpqc covering `g j : S j ⟶ T` of the
target such that for every `j` the base-changed family `S j ×[T] X i ⟶ S j` is an fpqc covering
of `S j`, then `f` is an fpqc covering of `T`. -/
@[stacks 03L9]
public lemma ofArrows_mem_fpqcPrecoverage_of_fpqc_locally
    {J : Type w} {S : J → Scheme.{u}} (g : ∀ j, S j ⟶ T)
    (hflat : ∀ i, Flat (f i))
    (hg : Presieve.ofArrows S g ∈ Scheme.fpqcPrecoverage T)
    (hbc : ∀ j, Presieve.ofArrows (fun i ↦ pullback (g j) (f i))
      (fun i ↦ pullback.fst (g j) (f i)) ∈ Scheme.fpqcPrecoverage (S j)) :
    Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage T := by
  rw [fpqc_mem_iff_qc_and_flat] at hg
  have hbcqc : ∀ j, Presieve.ofArrows (fun i ↦ pullback (g j) (f i))
      (fun i ↦ pullback.fst (g j) (f i)) ∈ Scheme.qcPrecoverage (S j) :=
    fun j ↦ (fpqc_mem_iff_qc_and_flat.mp (hbc j)).1
  have hbcsurj : ∀ (j : J) (s : S j), ∃ i, s ∈ Set.range (pullback.fst (g j) (f i)) :=
    fun j ↦ ((Scheme.ofArrows_mem_precoverage_iff _).mp
      (fpqc_mem_iff_qc_and_flat.mp (hbc j)).2).1
  have hEJ : QuasiCompactCover (⟨J, S, g⟩ : PreZeroHypercover.{w} T) :=
    Scheme.presieve₀_mem_qcPrecoverage_iff.mp hg.1
  have hEI : ∀ j : J, QuasiCompactCover (⟨I, fun i ↦ pullback (g j) (f i),
      fun i ↦ pullback.fst (g j) (f i)⟩ : PreZeroHypercover.{v} (S j)) :=
    fun j ↦ Scheme.presieve₀_mem_qcPrecoverage_iff.mp (hbcqc j)
  have hEJ' : QuasiCompactCover (⟨ULift.{v} J, fun j ↦ S j.down, fun j ↦ g j.down⟩ :
      PreZeroHypercover.{max w v} T) :=
    QuasiCompactCover.of_hom (𝒱 := (⟨J, S, g⟩ : PreZeroHypercover.{w} T))
      { s₀ := ULift.up, h₀ := fun _ ↦ 𝟙 _, w₀ := fun _ ↦ Category.id_comp _ }
  have hEI' : ∀ j : ULift.{v} J, QuasiCompactCover
      (⟨ULift.{w} I, fun i ↦ pullback (g j.down) (f i.down),
        fun i ↦ pullback.fst (g j.down) (f i.down)⟩ :
          PreZeroHypercover.{max w v} (S j.down)) := by
    intro j
    have := hEI j.down
    exact QuasiCompactCover.of_hom (𝒱 := (⟨I, fun i ↦ pullback (g j.down) (f i),
      fun i ↦ pullback.fst (g j.down) (f i)⟩ : PreZeroHypercover.{v} (S j.down)))
      { s₀ := ULift.up, h₀ := fun _ ↦ 𝟙 _, w₀ := fun _ ↦ Category.id_comp _ }
  have hbind : QuasiCompactCover
      ((⟨ULift.{v} J, fun j ↦ S j.down, fun j ↦ g j.down⟩ :
            PreZeroHypercover.{max w v} T).bind
        (fun j ↦ ⟨ULift.{w} I, fun i ↦ pullback (g j.down) (f i.down),
          fun i ↦ pullback.fst (g j.down) (f i.down)⟩)) := inferInstance
  have hqc : QuasiCompactCover (⟨I, X, f⟩ : PreZeroHypercover.{v} T) :=
    QuasiCompactCover.of_hom
      (𝒱 := (⟨ULift.{v} J, fun j ↦ S j.down, fun j ↦ g j.down⟩ :
            PreZeroHypercover.{max w v} T).bind
        (fun j ↦ ⟨ULift.{w} I, fun i ↦ pullback (g j.down) (f i.down),
          fun i ↦ pullback.fst (g j.down) (f i.down)⟩))
      { s₀ := fun p ↦ p.2.down
        h₀ := fun p ↦ pullback.snd (g p.1.down) (f p.2.down)
        w₀ := fun _ ↦ pullback.condition.symm }
  refine fpqc_mem_iff_qc_and_flat.mpr
    ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr hqc, ?_⟩
  refine (Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨fun x ↦ ?_, hflat⟩
  obtain ⟨j, s, rfl⟩ := ((Scheme.ofArrows_mem_precoverage_iff _).mp hg.2).1 x
  obtain ⟨i, y, hy⟩ := hbcsurj j s
  refine ⟨i, pullback.snd (g j) (f i) y, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, hy]
end Locality

end AlgebraicGeometry
