module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FlatBaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.FlatPullbackVariety
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.FiniteProjectionFlat
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.FlatPullbackPointCycle
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.MovableCycles
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.ProjectionExcess
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.ProjectiveSpaceMoving

/-!
# The moving lemma on an open subset of the nonsingular locus of a projective variety

Let `X ⊆ 𝐏(V)` be a closed subvariety over an algebraically closed field, let `Y ⊆ X` be an open
subset contained in the nonsingular locus of `X`, let `α` be an `r`-cycle and let `β i` be
finitely many cycles on `Y`. Then `α` is rationally equivalent on `Y` to an `r`-cycle which
intersects every `β i` properly. For `Y = X` nonsingular this is the substance of Tag 0B1U, and
for a general `Y` that of Remark 0B61; the statements for abstract nonsingular projective and
quasi-projective varieties are
`StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.MovingCycles`.

## Proof

By linearity (`Stacks.Chow.isMovableOff_of_forall_pointCycle`) it suffices to move a prime cycle
`[Z]`, `Z ⊆ Y` of dimension `r < n = dim X`, off the finitely many components `T` of the `β i`;
all dimensions are read in `Y`. The proof is by induction on the total *excess*
`∑_T max(0, dim (Z ∩ T) + n - (r + dim T))`, which vanishes exactly when `Z` meets every `T`
properly. The proof of Tag 0B0E produces a finite morphism `π : X ⟶ 𝐏^n`
(`exists_isFinite_excess_clauses_of_le_of_isOpenImmersion`), whose restriction to `Y` is flat by
miracle flatness, `Y` and `𝐏^n` being nonsingular and the restriction dominant and quasi-finite
(`flat_of_locallyQuasiFinite_of_isRegular`). Its flat pullback satisfies

`π^*[π(Z)] = [Z] + ∑ m_j [Z_j]`,

with coefficient one at `Z` because the maximal ideal at the image of the generic point of `Z`
generates the maximal ideal there (`Stacks.Chow.flatPullback_pointCycle_apply_eq_one`), and with
every `Z_j` the trace on `Y` of a closed subvariety of `π^{-1}(π(Z))` of dimension `r` other than
the closure of `Z`, hence of smaller excess
(`exists_isFinite_projection_excess_clauses_of_isOpenImmersion`): the `[Z_j]` are movable by
induction. On the other hand `[π(Z)]` is rationally equivalent on `𝐏^n` to a cycle `γ` whose
components meet every `π(T)` properly
(`exists_rationallyEquivalent_pointCycle_forall_intersectProperly`), so `π^*[π(Z)]` is rationally
equivalent (Tag 02S1) to `π^*γ`, whose components meet every `T` properly because `π` is finite.
Hence `[Z] = π^*[π(Z)] - ∑ m_j [Z_j]` is movable.

This replaces the source's degeneration of the cone `C` over `π(Z)` in `𝐏^N × 𝐏^1` (Tags 0B1T,
0B1M and 0B07) by the flat pullback along `π` and a degeneration of `π(Z)` itself inside `𝐏^n`:
the cycle `C · X` of the source is `π^*[π(Z)]`.

## Main results

* `AlgebraicGeometry.isMovableOff_pointCycle_of_isOpenImmersion`: the prime case.
* `AlgebraicGeometry.isMovableOff_of_isOpenImmersion`: every cycle on `Y`.
* `AlgebraicGeometry.isMovableOff_of_isClosedImmersion`: the case `Y = X`, for a nonsingular
  closed subvariety of `𝐏(V)`.

## References

* [Stacks Project, Tag 0B1U](https://stacks.math.columbia.edu/tag/0B1U)
* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Remark 0B61](https://stacks.math.columbia.edu/tag/0B61)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Chow

universe u

namespace AlgebraicGeometry

/-! ### The excess of a proper intersection -/

/-- The **excess** of an intersection of dimension `D` against an expected dimension `c - n`:
`D + n - c` when the intersection is nonempty, and `0` when it is empty. -/
private def excess (n c : ℕ) (D : WithBot ℕ∞) : ℕ :=
  open Classical in if D = ⊥ then 0 else (WithBot.unbotD 0 D).toNat + n - c

/-- A dimension other than `⊤` is `⊥` or a natural number. -/
private theorem eq_bot_or_exists_natCast {D : WithBot ℕ∞} (hD : D ≠ ⊤) :
    D = ⊥ ∨ ∃ m : ℕ, D = (m : WithBot ℕ∞) := by
  induction D using WithBot.recBotCoe with
  | bot => exact Or.inl rfl
  | coe e =>
    refine Or.inr ?_
    induction e using ENat.recTopCoe with
    | top => exact absurd rfl hD
    | coe m => exact ⟨m, rfl⟩

private theorem excess_natCast (n c m : ℕ) : excess n c (m : WithBot ℕ∞) = m + n - c := by
  unfold excess
  rw [if_neg (by exact_mod_cast WithBot.coe_ne_bot)]
  rfl

private theorem excess_bot (n c : ℕ) : excess n c ⊥ = 0 := by
  simp [excess]

/-- The excess vanishes exactly when the intersection has at most the expected dimension. -/
private theorem excess_eq_zero_iff {n c : ℕ} {D : WithBot ℕ∞} (hD : D ≠ ⊤) :
    excess n c D = 0 ↔ D + (n : WithBot ℕ∞) ≤ (c : WithBot ℕ∞) := by
  rcases eq_bot_or_exists_natCast hD with rfl | ⟨m, rfl⟩
  · simp [excess_bot]
  · rw [excess_natCast]
    constructor
    · intro h; exact_mod_cast (by omega : m + n ≤ c)
    · intro h; have : m + n ≤ c := by exact_mod_cast h
      omega

/-- The excess does not grow under either of the two clauses of the proof of Tag 0B0E. -/
private theorem excess_le_excess {n c : ℕ} {D D' : WithBot ℕ∞} (hD : D ≠ ⊤) (hD' : D' ≠ ⊤)
    (h : D' ≤ D ∨ D' + (n : WithBot ℕ∞) ≤ (c : WithBot ℕ∞)) :
    excess n c D' ≤ excess n c D := by
  rcases h with h | h
  · rcases eq_bot_or_exists_natCast hD' with rfl | ⟨m', rfl⟩
    · rw [excess_bot]; exact Nat.zero_le _
    · rcases eq_bot_or_exists_natCast hD with rfl | ⟨m, rfl⟩
      · exact absurd (le_bot_iff.mp h) (by exact_mod_cast WithBot.coe_ne_bot)
      · have : m' ≤ m := by exact_mod_cast h
        rw [excess_natCast, excess_natCast]
        omega
  · rw [(excess_eq_zero_iff hD').mpr h]; exact Nat.zero_le _

/-- The excess drops strictly with the dimension of an improper intersection. -/
private theorem excess_lt_excess {n c : ℕ} {D D' : WithBot ℕ∞} (hD : D ≠ ⊤) (hD' : D' ≠ ⊤)
    (hns : ¬ D + (n : WithBot ℕ∞) ≤ (c : WithBot ℕ∞)) (h : D' < D) :
    excess n c D' < excess n c D := by
  have hpos : excess n c D ≠ 0 := fun h0 ↦ hns ((excess_eq_zero_iff hD).mp h0)
  rcases eq_bot_or_exists_natCast hD' with rfl | ⟨m', rfl⟩
  · rw [excess_bot]; omega
  · rcases eq_bot_or_exists_natCast hD with rfl | ⟨m, rfl⟩
    · exact absurd h not_lt_bot
    · have hm : m' < m := by exact_mod_cast h
      have hpos' := hpos
      rw [excess_natCast] at hpos' ⊢
      rw [excess_natCast]
      omega

/-! ### The prime case -/

/-- Cycle groups of equal degree carry the same rational equivalences. -/
private theorem cycleGroupCongrDegree_mem_rationalEquivalences (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] {j k : ℤ} (h : j = k)
    {z : CycleGroup C f j} (hz : z ∈ rationalEquivalences C f j) :
    cycleGroupCongrDegree C f h z ∈ rationalEquivalences C f k := by
  subst h
  exact hz

/-- An open subscheme of a scheme contained in its nonsingular locus is regular: its local rings
are those of the ambient scheme. -/
private theorem isRegular_of_isOpenImmersion {X Y : Scheme.{u}} (j₀ : Y ⟶ X) [IsOpenImmersion j₀]
    [IsLocallyNoetherian Y] (hU : Set.range j₀.base ⊆ regularLocus X) : IsRegular Y := by
  have h : IsLocallyNoetherian Y ∧ ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) := by
    refine ⟨inferInstance, fun y ↦ ?_⟩
    have : IsRegularLocalRing (X.presheaf.stalk (j₀.base y)) := hU ⟨y, rfl⟩
    exact IsRegularLocalRing.of_ringEquiv (asIso (j₀.stalkMap y)).commRingCatIsoToRingEquiv
  exact ((isRegular_tfae Y).out 1 2).mpr h

/-- **The moving lemma for a prime cycle on an open subset of the nonsingular locus of a closed
subvariety of `𝐏(V)`.** Let `X ⊆ 𝐏(V)` be a closed subvariety of dimension `n` over an
algebraically closed field, let `j₀ : Y ⟶ X` be an open immersion of a nonempty scheme whose image
lies in the nonsingular locus of `X`, let `β i` be finitely many cycles on `Y` and let `z` be a
point of `Y` of dimension `r`. Then the prime cycle `[z]` is rationally equivalent on `Y` to an
`r`-cycle intersecting every `β i` properly. -/
public theorem isMovableOff_pointCycle_of_isOpenImmersion (k V : Type u) [Field k]
    [IsAlgClosed k] [AddCommGroup V] [Module k V] [FiniteDimensional k V] {N n : ℕ}
    (hV : Module.finrank k V = N + 1) {X : Scheme.{u}} (iX : X ⟶ projectiveSpaceOfModule k V)
    [IsClosedImmersion iX] [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)]
    (hdimX : topologicalKrullDim X = (n : WithBot ℕ∞)) {Y : Scheme.{u}} (j₀ : Y ⟶ X)
    [IsOpenImmersion j₀] (hU : Set.range j₀.base ⊆ regularLocus X)
    (sY : Y ⟶ (fieldChowSituation k).S) [IsVariety k sY]
    (hsY : j₀ ≫ iX ≫ projectiveSpaceOfModuleToSpec k V = sY)
    (hdimY : topologicalKrullDim Y = (n : WithBot ℕ∞))
    {ι : Type*} [Finite ι] (β : ι → AlgebraicCycle Y ℤ) (r : ℕ) (z : Y)
    (hz : relativeDimension (fieldChowSituation k).dimensionFunction sY z = (r : ℤ)) :
    IsMovableOff (fieldChowSituation k) sY (r : ℤ) β
      (pointCycle (fieldChowSituation k) sY (r : ℤ) z hz) := by
  classical
  set sX : X ⟶ (fieldChowSituation k).S := iX ≫ projectiveSpaceOfModuleToSpec k V with hsX
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hYreg : IsRegular Y := isRegular_of_isOpenImmersion j₀ hU
  have hinj : Function.Injective j₀.base := j₀.isOpenEmbedding.injective
  -- closures in `Y` are the traces of closures in `X`
  have hclpre : ∀ y : Y, j₀.base ⁻¹' closure ({j₀.base y} : Set X) = closure ({y} : Set Y) :=
    fun y ↦ by
      rw [j₀.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_singleton]
  have hrelj : ∀ y : Y, relativeDimension (fieldChowSituation k).dimensionFunction sX (j₀.base y) =
      relativeDimension (fieldChowSituation k).dimensionFunction sY y := fun y ↦ by
    rw [← relativeDimension_comp_isOpenImmersion _ j₀ sX y]
    exact congrArg (fun q ↦ relativeDimension (fieldChowSituation k).dimensionFunction q y) hsY
  -- the components of the `β i`
  set S : Set Y := ⋃ i, Function.support (β i : Y → ℤ) with hSdef
  have hSfin : S.Finite :=
    Set.finite_iUnion fun i ↦ TorFormula.finite_support_of_compactSpace (β i)
  set dimN : Y → ℕ := fun y ↦
    (relativeDimension (fieldChowSituation k).dimensionFunction sY y).toNat with hdimNdef
  have hdimN : ∀ y, topologicalKrullDim ↥(closure ({y} : Set Y)) = (dimN y : WithBot ℕ∞) :=
    fun y ↦ topologicalKrullDim_closure_eq_toNat_relativeDimension k sY y
  have hdimNX : ∀ y, topologicalKrullDim ↥(closure ({j₀.base y} : Set X)) =
      (dimN y : WithBot ℕ∞) := fun y ↦ by
    rw [topologicalKrullDim_closure_eq_toNat_relativeDimension k sX (j₀.base y), hrelj]
  have hrel : ∀ x, relativeDimension (fieldChowSituation k).dimensionFunction sY x = (r : ℤ) →
      dimN x = r := fun x hx ↦ by simp [hdimNdef, hx]
  set D : Y → Y → WithBot ℕ∞ := fun x y ↦
    topologicalKrullDim ↥(closure ({x} : Set Y) ∩ closure ({y} : Set Y)) with hDdef
  have hDle : ∀ x y, D x y ≤ (dimN x : WithBot ℕ∞) := fun x y ↦
    (topologicalKrullDim_le_of_subset Set.inter_subset_left).trans (le_of_eq (hdimN x))
  have hDle' : ∀ x y, D x y ≤ (dimN y : WithBot ℕ∞) := fun x y ↦
    (topologicalKrullDim_le_of_subset Set.inter_subset_right).trans (le_of_eq (hdimN y))
  have hDtop : ∀ x y, D x y ≠ ⊤ := fun x y h ↦ by
    have := hDle x y
    rw [h, top_le_iff] at this
    exact absurd this (by
      intro h1; rw [← WithBot.coe_top] at h1
      exact (ENat.coe_ne_top (dimN x)) (by exact_mod_cast h1))
  have hDpre : ∀ x y, D x y = topologicalKrullDim ↥(j₀.base ⁻¹' closure ({j₀.base x} : Set X) ∩
      j₀.base ⁻¹' closure ({j₀.base y} : Set X)) := fun x y ↦ by rw [hclpre, hclpre]
  set μ : Y → ℕ := fun x ↦ ∑ y ∈ hSfin.toFinset, excess n (r + dimN y) (D x y) with hμdef
  -- the components of dimension at least `n` meet everything properly
  have hbig : ∀ x y, dimN x = r → n ≤ dimN y → excess n (r + dimN y) (D x y) = 0 := by
    intro x y hx hy
    rw [excess_eq_zero_iff (hDtop x y)]
    calc D x y + (n : WithBot ℕ∞) ≤ (dimN x : WithBot ℕ∞) + (dimN y : WithBot ℕ∞) :=
          add_le_add (hDle x y) (by exact_mod_cast hy)
      _ = ((r + dimN y : ℕ) : WithBot ℕ∞) := by rw [hx]; push_cast; rfl
  have hyS : ∀ (i : ι) y, y ∈ Function.support (β i : Y → ℤ) → y ∈ S := fun i y hy ↦ by
    rw [hSdef, Set.mem_iUnion]; exact ⟨i, hy⟩
  -- proper intersection of two components, from the dimension inequality
  have hIP : ∀ x y : Y, dimN x = r → excess n (r + dimN y) (D x y) = 0 →
      AlgebraicGeometry.IntersectProperly
        ⟨closure ({x} : Set Y), isIrreducible_singleton.closure, isClosed_closure⟩
        ⟨closure ({y} : Set Y), isIrreducible_singleton.closure, isClosed_closure⟩ := by
    intro x y hx h
    rw [excess_eq_zero_iff (hDtop x y)] at h
    rw [AlgebraicGeometry.intersectProperly_iff]
    show D x y + topologicalKrullDim Y ≤
      topologicalKrullDim ↥(closure ({x} : Set Y)) + topologicalKrullDim ↥(closure ({y} : Set Y))
    rw [hdimY, hdimN x, hdimN y, hx]
    exact_mod_cast h
  -- the target spaces of the projections and their structure
  have hnN : n ≤ N := by
    have hle : topologicalKrullDim X ≤ topologicalKrullDim (projectiveSpaceOfModule k V) :=
      iX.isClosedEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
    rw [hdimX, topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hV] at hle
    exact_mod_cast hle
  -- the induction on the excess
  suffices H : ∀ m : ℕ, ∀ (z : Y)
      (hz : relativeDimension (fieldChowSituation k).dimensionFunction sY z = (r : ℤ)),
      μ z = m → IsMovableOff (fieldChowSituation k) sY (r : ℤ) β
        (pointCycle (fieldChowSituation k) sY (r : ℤ) z hz) from H _ z hz rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro z hz hμ
  have hzr : dimN z = r := hrel z hz
  by_cases hμ0 : μ z = 0
  · -- no excess: `[z]` itself meets every `β i` properly
    refine IsMovableOff.of_intersectProperly fun i ↦ ?_
    refine AlgebraicCycle.intersectProperly_of_forall_closure fun x y hx hy ↦ ?_
    have hxz : x = z := by
      by_contra hne
      exact hx (by rw [pointCycle_apply, if_neg hne])
    subst hxz
    exact hIP x y hzr ((Finset.sum_eq_zero_iff.mp hμ0) y (hSfin.mem_toFinset.mpr (hyS i y hy)))
  -- positive excess: then `r < n`
  have hrn : r < n := by
    by_contra hcon
    replace hcon := not_lt.mp hcon
    refine hμ0 (Finset.sum_eq_zero fun y _ ↦ ?_)
    rw [excess_eq_zero_iff (hDtop z y)]
    calc D z y + (n : WithBot ℕ∞) ≤ (dimN y : WithBot ℕ∞) + (r : WithBot ℕ∞) :=
          add_le_add (hDle' z y) (by exact_mod_cast hcon)
      _ = ((r + dimN y : ℕ) : WithBot ℕ∞) := by push_cast; rw [add_comm]
  -- the components of dimension less than `n`, which the projection has to handle
  set Ty : Set Y := S ∩ {y | dimN y < n} with hTydef
  have : Finite ↥Ty := (hSfin.subset Set.inter_subset_left).to_subtype
  obtain ⟨W, hWrank, π, hfin, hπ, hmax, hcl⟩ :=
    ProjectiveSpaceOfModule.exists_isFinite_excess_clauses_of_le_of_isOpenImmersion k V hV iX
      hdimX hnN hrn j₀ hU z (by rw [hdimNX, hzr])
      (fun y : ↥Ty ↦ closure ({j₀.base y.1} : Set X)) (fun _ ↦ isClosed_closure)
      (d' := fun y ↦ dimN y.1) (fun y ↦ y.2.2) (fun y ↦ le_of_eq (hdimNX y.1))
  have := hfin
  have : Nontrivial ↥W := Module.nontrivial_of_finrank_pos (R := k) (by rw [hWrank]; omega)
  set sP : projectiveSpaceOfModule k ↥W ⟶ (fieldChowSituation k).S :=
    projectiveSpaceOfModuleToSpec k ↥W with hsP
  have : IsReduced (projectiveSpaceOfModule k ↥W) :=
    ProjectiveSpaceOfModule.isReduced_projectiveSpaceOfModule k ↥W
  have : IsVariety k sP := ⟨⟩
  have hπs : π ≫ sP = sX := hπ
  have hdimP : topologicalKrullDim (projectiveSpaceOfModule k ↥W) = (n : WithBot ℕ∞) :=
    topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hWrank
  -- the composite `π_Y : Y ⟶ 𝐏(W)` is flat of relative dimension zero
  set πY : Y ⟶ projectiveSpaceOfModule k ↥W := j₀ ≫ π with hπYdef
  have hπYs : πY ≫ sP = sY := by rw [hπYdef, Category.assoc, hπs, hsX, hsY]
  have : LocallyOfFiniteType πY := locallyOfFiniteType_of_isVariety_comp k sY sP πY hπYs
  have : IsDominant π := by
    have : Surjective π := surjective_of_isFinite_of_topologicalKrullDim_le π
      (by rw [hdimP]; exact (WithBot.coe_lt_coe.mpr (ENat.coe_lt_top n)).ne)
      (by rw [hdimP, hdimX])
    infer_instance
  have : IsDominant j₀ := by
    obtain ⟨y⟩ : Nonempty Y := ⟨z⟩
    exact ⟨(j₀.isOpenEmbedding.isOpenMap.isOpen_range).dense ⟨j₀.base y, y, rfl⟩⟩
  have : Flat πY := flat_of_locallyQuasiFinite_of_isRegular k sP πY hYreg
    (ProjectiveSpaceOfModule.isRegular_projectiveSpaceOfModule k ↥W)
  have hr0 : AlgebraicGeometry.RelativeDimension πY 0 :=
    relativeDimension_of_flat_of_isVariety k sY sP πY hπYs 0 (by rw [hdimY, hdimP]; simp)
  have hrelπ : ∀ x, relativeDimension (fieldChowSituation k).dimensionFunction sP (πY.base x) =
      relativeDimension (fieldChowSituation k).dimensionFunction sY x := fun x ↦ by
    rw [← relativeDimension_eq_of_locallyQuasiFinite k sP πY x, hπYs]
  have hy0 : relativeDimension (fieldChowSituation k).dimensionFunction sP (πY.base z) =
      (r : ℤ) := by rw [hrelπ, hz]
  have h00 : (r : ℤ) + ((0 : ℕ) : ℤ) = (r : ℤ) := by simp
  -- the pullback, read in degree `r`
  set pull : CycleGroup (fieldChowSituation k) sP (r : ℤ) →
      CycleGroup (fieldChowSituation k) sY (r : ℤ) := fun c ↦
    cycleGroupCongrDegree (fieldChowSituation k) sY h00
      (flatPullback (fieldChowSituation k) sY sP πY hπYs 0 hr0 (r : ℤ) c) with hpulldef
  have hpull_apply : ∀ c x, (pull c).1 x = c.1 (πY.base x) *
      flatPullbackWeight (fieldChowSituation k) sY πY ((r : ℤ) + ((0 : ℕ) : ℤ)) x := fun c x ↦ by
    exact flatPullback_apply (fieldChowSituation k) sY sP πY hπYs 0 hr0 (r : ℤ) c x
  have hpull_sub : ∀ c₁ c₂, pull c₁ - pull c₂ =
      cycleGroupCongrDegree (fieldChowSituation k) sY h00
        (flatPullback (fieldChowSituation k) sY sP πY hπYs 0 hr0 (r : ℤ) (c₁ - c₂)) := by
    intro c₁ c₂
    rw [hpulldef, map_sub, map_sub]
  -- images of closed sets under the finite morphism `π`
  have himg : ∀ {A : Set X}, IsClosed A → IsClosed (π.base '' A) ∧
      topologicalKrullDim ↥(π.base '' A) ≤ topologicalKrullDim ↥A := fun {A} hA ↦
    ProjectiveSpaceOfModule.isClosed_image_and_topologicalKrullDim_image_le k π sX sP hπs hA
  -- moving `[π(Z)]` inside `𝐏(W)`
  obtain ⟨γ, hγrat, hγprop⟩ :=
    ProjectiveSpaceOfModule.exists_rationallyEquivalent_pointCycle_forall_intersectProperly k ↥W
      hWrank (πY.base z) hy0 (fun y : ↥Ty ↦ π.base '' closure ({j₀.base y.1} : Set X))
      (fun _ ↦ (himg isClosed_closure).1)
      (fun _ ↦ isIrreducible_singleton.closure.image _ π.continuous.continuousOn)
  set P := pull (pointCycle (fieldChowSituation k) sP (r : ℤ) (πY.base z) hy0) with hPdef
  -- `π^*[π(Z)]` is movable: `π^*γ` meets every `β i` properly
  have hPmov : IsMovableOff (fieldChowSituation k) sY (r : ℤ) β P := by
    refine ⟨pull γ, ?_, fun i ↦ ?_⟩
    · show pull γ - P ∈ rationalEquivalences (fieldChowSituation k) sY (r : ℤ)
      rw [hPdef, hpull_sub]
      exact cycleGroupCongrDegree_mem_rationalEquivalences _ _ h00
        (flatPullbackFactorsThroughRationalEquivalence_general (fieldChowSituation k) sY sP πY
          hπYs 0 hr0 (r : ℤ) _ hγrat)
    · refine AlgebraicCycle.intersectProperly_of_forall_closure fun x y hx hy ↦ ?_
      have hγx : γ.1 (πY.base x) ≠ 0 := by
        rw [hpull_apply] at hx
        exact left_ne_zero_of_mul hx
      have hxr : relativeDimension (fieldChowSituation k).dimensionFunction sY x = (r : ℤ) :=
        (mem_cyclesOfDimension_iff_forall_point _ _ _ _).mp (pull γ).2 x hx
      have hxN : dimN x = r := hrel x hxr
      by_cases hyn : n ≤ dimN y
      · exact hIP x y hxN (hbig x y hxN hyn)
      refine hIP x y hxN ((excess_eq_zero_iff (hDtop x y)).mpr ?_)
      have hm := hγprop (πY.base x) hγx ⟨y, hyS i y hy, not_le.mp hyn⟩
      have hcl₁ : IsClosed (closure ({πY.base x} : Set (projectiveSpaceOfModule k ↥W)) ∩
          π.base '' closure ({j₀.base y} : Set X)) :=
        isClosed_closure.inter (himg isClosed_closure).1
      have hsub : j₀.base '' (closure ({x} : Set Y) ∩ closure ({y} : Set Y)) ⊆
          π.base ⁻¹' (closure ({πY.base x} : Set (projectiveSpaceOfModule k ↥W)) ∩
            π.base '' closure ({j₀.base y} : Set X)) := by
        rintro _ ⟨w, ⟨hwx, hwy⟩, rfl⟩
        refine ⟨?_, ⟨j₀.base w, ?_, rfl⟩⟩
        · have h1 := image_closure_subset_closure_image (f := πY.base) πY.continuous
            (Set.mem_image_of_mem πY.base hwx)
          rwa [Set.image_singleton] at h1
        · rwa [← hclpre] at hwy
      have hle₁ : D x y ≤
          topologicalKrullDim ↥(closure ({πY.base x} : Set (projectiveSpaceOfModule k ↥W)) ∩
            π.base '' closure ({j₀.base y} : Set X)) := by
        show topologicalKrullDim ↥(closure ({x} : Set Y) ∩ closure ({y} : Set Y)) ≤ _
        rw [← topologicalKrullDim_image_eq_of_isEmbedding j₀.isOpenEmbedding.isEmbedding]
        exact (topologicalKrullDim_le_of_subset hsub).trans
          (topologicalKrullDim_preimage_le_of_isIntegralHom π hcl₁)
      have hπx : topologicalKrullDim ↥(closure ({πY.base x} :
          Set (projectiveSpaceOfModule k ↥W))) = (r : WithBot ℕ∞) :=
        topologicalKrullDim_closure_eq_of_relativeDimension_eq k sP (by rw [hrelπ, hxr])
      rw [hπx] at hm
      calc D x y + (n : WithBot ℕ∞)
          ≤ topologicalKrullDim ↥(closure ({πY.base x} : Set (projectiveSpaceOfModule k ↥W)) ∩
              π.base '' closure ({j₀.base y} : Set X)) + (n : WithBot ℕ∞) :=
            add_le_add hle₁ le_rfl
        _ ≤ (r : WithBot ℕ∞) + topologicalKrullDim ↥(π.base '' closure ({j₀.base y} : Set X)) :=
            hm
        _ ≤ (r : WithBot ℕ∞) + (dimN y : WithBot ℕ∞) :=
            add_le_add le_rfl ((himg isClosed_closure).2.trans (hdimNX y).le)
  -- the remainder `π^*[π(Z)] - [Z]` is movable by induction
  set R := P - pointCycle (fieldChowSituation k) sY (r : ℤ) z hz with hRdef
  have hP1 : P.1 z = 1 :=
    flatPullback_pointCycle_apply_eq_one (fieldChowSituation k) sY sP πY hπYs (r : ℤ) hr0 z hz
      hy0 hmax
  have hRmov : IsMovableOff (fieldChowSituation k) sY (r : ℤ) β R := by
    refine isMovableOff_of_forall_pointCycle R fun x hx hRx ↦ ?_
    have hRx' : P.1 x - (if x = z then 1 else 0) ≠ 0 := by
      rwa [← pointCycle_apply (fieldChowSituation k) sY (r : ℤ) z hz x]
    have hxz : x ≠ z := by
      rintro rfl
      exact hRx' (by rw [hP1, if_pos rfl, sub_self])
    have hPx : P.1 x ≠ 0 := by simpa [hxz] using hRx'
    have hπx : πY.base x = πY.base z := by
      rw [hPdef, hpull_apply, pointCycle_apply] at hPx
      by_contra hne
      exact hPx (by rw [if_neg hne, zero_mul])
    have hxN : dimN x = r := hrel x hx
    have hW'sub : closure ({j₀.base x} : Set X) ⊆
        π.base ⁻¹' (π.base '' closure ({j₀.base z} : Set X)) := by
      refine ((himg isClosed_closure).1.preimage π.continuous).closure_subset_iff.mpr ?_
      rw [Set.singleton_subset_iff, Set.mem_preimage]
      rw [show π.base (j₀.base x) = π.base (j₀.base z) from hπx]
      exact Set.mem_image_of_mem _ (subset_closure (Set.mem_singleton _))
    have hW'ne : closure ({j₀.base x} : Set X) ≠ closure ({j₀.base z} : Set X) := fun h ↦
      hxz (hinj (inseparable_iff_closure_eq.mpr h).eq)
    have hclx := hcl (closure ({j₀.base x} : Set X)) isClosed_closure
      isIrreducible_singleton.closure hW'sub (by rw [hdimNX, hxN]) hW'ne
    refine ih (μ x) ?_ x hx rfl
    rw [← hμ]
    -- the excess drops
    obtain ⟨y₀, hy₀S, hy₀ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hμ0
    refine Finset.sum_lt_sum (fun y hyS ↦ ?_) ⟨y₀, hy₀S, ?_⟩
    · by_cases hyn : n ≤ dimN y
      · rw [hbig x y hxN hyn]; exact Nat.zero_le _
      · have hc := (hclx ⟨y, (Set.Finite.mem_toFinset hSfin).mp hyS, not_le.mp hyn⟩).1
        refine excess_le_excess (hDtop z y) (hDtop x y) ?_
        rw [hDpre, hDpre]
        push_cast
        exact hc
    · have hyn : ¬ n ≤ dimN y₀ := fun h ↦ hy₀ne (hbig z y₀ hzr h)
      have hns : ¬ D z y₀ + (n : WithBot ℕ∞) ≤ ((r + dimN y₀ : ℕ) : WithBot ℕ∞) :=
        fun h ↦ hy₀ne ((excess_eq_zero_iff (hDtop z y₀)).mpr h)
      have hc := (hclx ⟨y₀, (Set.Finite.mem_toFinset hSfin).mp hy₀S, not_le.mp hyn⟩).2
        (by rw [hDpre] at hns; push_cast at hns; exact hns)
      refine excess_lt_excess (hDtop z y₀) (hDtop x y₀) hns ?_
      rw [hDpre, hDpre]
      exact hc
  -- `[Z] = π^*[π(Z)] - R`
  have hdec : pointCycle (fieldChowSituation k) sY (r : ℤ) z hz = P - R := by
    rw [hRdef, sub_sub_cancel]
  rw [hdec]
  exact hPmov.sub hRmov

/-! ### The moving lemma -/

/-- **The moving lemma on an open subset of the nonsingular locus of a closed subvariety of
`𝐏(V)`.** Every `r`-cycle on such an open subset is rationally equivalent there to one meeting
finitely many given cycles properly. -/
public theorem isMovableOff_of_isOpenImmersion (k V : Type u) [Field k] [IsAlgClosed k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] {N n : ℕ}
    (hV : Module.finrank k V = N + 1) {X : Scheme.{u}} (iX : X ⟶ projectiveSpaceOfModule k V)
    [IsClosedImmersion iX] [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)]
    (hdimX : topologicalKrullDim X = (n : WithBot ℕ∞)) {Y : Scheme.{u}} (j₀ : Y ⟶ X)
    [IsOpenImmersion j₀] (hU : Set.range j₀.base ⊆ regularLocus X)
    (sY : Y ⟶ (fieldChowSituation k).S) [IsVariety k sY]
    (hsY : j₀ ≫ iX ≫ projectiveSpaceOfModuleToSpec k V = sY)
    (hdimY : topologicalKrullDim Y = (n : WithBot ℕ∞))
    {ι : Type*} [Finite ι] (β : ι → AlgebraicCycle Y ℤ) (r : ℤ)
    (α : CycleGroup (fieldChowSituation k) sY r) :
    IsMovableOff (fieldChowSituation k) sY r β α := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  refine isMovableOff_of_forall_pointCycle α fun x hx _ ↦ ?_
  have hr0 : 0 ≤ r := hx ▸ relativeDimension_nonneg (fieldChowSituation k) (fun _ _ ↦ rfl) _ x
  obtain ⟨r', rfl⟩ : ∃ r' : ℕ, r = (r' : ℤ) := ⟨r.toNat, (Int.toNat_of_nonneg hr0).symm⟩
  exact isMovableOff_pointCycle_of_isOpenImmersion k V hV iX hdimX j₀ hU sY hsY hdimY β r' x hx

/-- An open immersion of a nonsingular scheme lands in the nonsingular locus: it identifies local
rings. -/
public theorem range_subset_regularLocus_of_isRegular {X Y : Scheme.{u}} (j₀ : Y ⟶ X)
    [IsOpenImmersion j₀] (hY : IsRegular Y) : Set.range j₀.base ⊆ regularLocus X := by
  rintro _ ⟨y, rfl⟩
  have hYs : IsLocallyNoetherian Y ∧ ∀ z : Y, IsRegularLocalRing (Y.presheaf.stalk z) :=
    ((isRegular_tfae Y).out 1 2).mp hY
  have := hYs.2 y
  exact IsRegularLocalRing.of_ringEquiv (asIso (j₀.stalkMap y)).commRingCatIsoToRingEquiv.symm

/-- **The moving lemma on a nonsingular closed subvariety of `𝐏(V)`.** Every `r`-cycle on a
nonsingular closed subvariety `X` of the projective space of a finite-dimensional vector space over
an algebraically closed field is rationally equivalent to one meeting finitely many given cycles
properly. This is the case `Y = X` of `isMovableOff_of_isOpenImmersion`. -/
public theorem isMovableOff_of_isClosedImmersion (k V : Type u) [Field k] [IsAlgClosed k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] {N : ℕ}
    (hV : Module.finrank k V = N + 1) {X : Scheme.{u}} (iX : X ⟶ projectiveSpaceOfModule k V)
    [IsClosedImmersion iX] [IsVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)]
    (hXreg : IsRegular X) {ι : Type*} [Finite ι] (β : ι → AlgebraicCycle X ℤ) (r : ℤ)
    (α : CycleGroup (fieldChowSituation k) (iX ≫ projectiveSpaceOfModuleToSpec k V) r) :
    IsMovableOff (fieldChowSituation k) (iX ≫ projectiveSpaceOfModuleToSpec k V) r β α := by
  obtain ⟨n, hn⟩ :=
    exists_topologicalKrullDim_eq_natCast_of_isVariety k (iX ≫ projectiveSpaceOfModuleToSpec k V)
  exact isMovableOff_of_isOpenImmersion k V hV iX hn (𝟙 X)
    (range_subset_regularLocus_of_isRegular _ hXreg) _ (Category.id_comp _) hn β r α

end AlgebraicGeometry

end
