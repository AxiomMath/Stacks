module

public import Mathlib.Topology.Constructible
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeSupport
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.EffectiveSupportClosed
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Relative
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationRestriction
public import StacksFrontier.AlgebraicGeometry.Properties.DiscreteValuation
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.Topology.Specialization.Constructible
public import StacksCore.Tactic.StacksAttribute

/-!
# The locus where two relative cycles have the same fibre cycle

Let `f : X ⟶ S` be locally of finite type and let `α, β` be families of `r`-cycles on the fibres
of `X/S`. Since a family of cycles is a choice of cycle on each fibre, the map `α ↦ α_s` is
additive and the locus `E = {s ∈ S : α_s = β_s}` is the locus where `α - β` vanishes, that is
the complement of the image in `S` of the support of `α - β`.

This file collects the properties of such a vanishing locus: its description as the complement of
an image of a support, its behaviour under base change, under a closed immersion of the source and
under open coverings of the source and of the base, and — for a relative `r`-cycle over a locally
Noetherian base — its stability under specialization and its closedness, which is Lemma 0H5C.

## Main results

* `Stacks.Chow.image_supportOfFamily_eq_setOf_ne_zero` — the image in `S` of the support of a
  family of cycles is the set of points where the family is nonzero.
* `Stacks.Chow.baseChangeFamily_apply_eq_zero_iff`,
  `Stacks.Chow.properPushforwardFamily_apply_eq_zero_iff` — the vanishing locus is unchanged by
  base change (read on the inverse image) and by pushforward along a closed immersion.
* `Stacks.Chow.isClosed_vanishingLocus_of_proper_surjective`,
  `Stacks.Chow.isClosed_vanishingLocus_of_baseOpenCover`,
  `Stacks.Chow.isClosed_vanishingLocus_of_openCover` — closedness of the vanishing locus may be
  tested after a proper surjective base change, on an open covering of the base, and on an open
  covering of the source.
* `Stacks.Chow.stableUnderSpecialization_setOf_fiberCycle_eq` — for relative `r`-cycles the
  locus where two fibre cycles agree is stable under specialization.
* `Stacks.Chow.isClosed_of_stableUnderSpecialization_of_forall_notMem` — on a Noetherian
  quasi-sober space, a subset stable under specialization is closed as soon as every point outside
  it has an open neighbourhood containing none of its specializations in the subset.
* `Stacks.Chow.exists_isOpen_forall_specializes_ne_zero` — a relative `r`-cycle nonzero on the
  fibre over `η` is nonzero on the fibre over every specialization of `η` near `η`.
* `Stacks.Chow.isClosed_setOf_fiberCycle_eq` — Lemma 0H5C.

## Implementation notes

The proof of Lemma 0H5C given here is not the source's, which reduces by Lemma 0H59 to cycles in
the image of the cycle class map and then uses the local structure of morphisms of finite type,
Tag 052E, and Lemma 0H5B. Instead, with `γ = α - β`, the locus `E = {γ_s = 0}` is stable under
specialization by the valuative condition, and a Noetherian induction on the closed subsets of the
base shows that it is closed as soon as every `η ∉ E` has an open neighbourhood `O` with
`O ∩ closure {η}` disjoint from `E`. To find `O`, restrict `±γ` to an open `U ⊆ X` on which
`γ_η = m[ξ]` with `m > 0`; the support of the restricted cycle is then carried along every
specialization of `ξ` (the argument of Tag 0H5W, which needs effectivity of the fibre cycle at
the generizing point only), and by Chevalley's theorem the images of the specializations of `ξ`
fill out `O ∩ closure {η}` for a suitable open `O ∋ η`.

## References

* [Stacks Project, Lemma 0H5C](https://stacks.math.columbia.edu/tag/0H5C)
* [Stacks Project, Definition 0H50](https://stacks.math.columbia.edu/tag/0H50)
* [Stacks Project, Lemma 0H5W](https://stacks.math.columbia.edu/tag/0H5W)
* [Stacks Project, Lemma 054F](https://stacks.math.columbia.edu/tag/054F)
* [Stacks Project, Theorem 054J](https://stacks.math.columbia.edu/tag/054J)
* [Stacks Project, Lemma 0903](https://stacks.math.columbia.edu/tag/0903)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v u

namespace Stacks.Chow

/-! ### The vanishing locus as the complement of an image of a support -/

/-- The image in `S` of the support of a family of `r`-cycles on the fibres of `f` is the set of
points of the base at which the family is nonzero. -/
theorem image_supportOfFamily_eq_setOf_ne_zero {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {r : ℕ} (α : FamilyOfCycles f r) :
    f '' supportOfFamily f α = {s : S | α s ≠ 0} := by
  ext s
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, y, hy, rfl⟩ := (mem_supportOfFamily f α x).mp hx
    have hbase : f (f.fiberι t y) = t := (f.fiberHomeo t y).2
    intro hzero
    rw [show α t = 0 from hbase ▸ hzero] at hy
    exact tsupport_zero.subset hy
  · intro hs
    obtain ⟨y, hy⟩ : (tsupport (α s : AlgebraicCycle (f.fiber s) ℤ)).Nonempty := by
      by_contra hempty
      have hzero := tsupport_eq_empty_iff.mp (Set.not_nonempty_iff_eq_empty.mp hempty)
      exact hs (Subtype.ext (Function.locallyFinsuppWithin.ext fun y => congrFun hzero y))
    exact ⟨f.fiberι s y, (mem_supportOfFamily f α _).mpr ⟨s, y, hy, rfl⟩,
      (f.fiberHomeo s y).2⟩

/-- The vanishing locus of a family of `r`-cycles on the fibres of `f` is the complement of the
image in `S` of its support. -/
theorem setOf_eq_zero_eq_compl_image_supportOfFamily {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {r : ℕ} (α : FamilyOfCycles f r) :
    {s : S | α s = 0} = (f '' supportOfFamily f α)ᶜ := by
  rw [image_supportOfFamily_eq_setOf_ne_zero]
  ext s
  simp

/-- The locus where two families of `r`-cycles on the fibres of `f` agree is the vanishing locus
of their difference: the map sending a family to its cycle on the fibre over `s` is additive. -/
theorem setOf_fiberCycle_eq_eq_setOf_sub_eq_zero {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {r : ℕ} (α β : FamilyOfCycles f r) :
    {s : S | α s = β s} = {s : S | (α - β) s = 0} := by
  ext s
  change _ ↔ α s - β s = 0
  exact sub_eq_zero.symm

/-- If the support of a family of `r`-cycles is open and `f` is an open map, then the vanishing
locus of the family is closed. -/
theorem isClosed_setOf_eq_zero_of_isOpen_supportOfFamily {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (hf : IsOpenMap f.base) {r : ℕ} (α : FamilyOfCycles f r)
    (hα : IsOpen (supportOfFamily f α)) :
    IsClosed {s : S | α s = 0} := by
  rw [setOf_eq_zero_eq_compl_image_supportOfFamily]
  exact (hf _ hα).isClosed_compl

/-! ### The vanishing locus under base change -/

/-- The base change of a family of `r`-cycles along `g : S' ⟶ S` vanishes on the fibre over `t`
exactly when the family vanishes on the fibre over `g t`. -/
theorem baseChangeFamily_apply_eq_zero_iff {X S S' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : S' ⟶ S) (r : ℕ) (α : FamilyOfCycles f r) (t : S') :
    baseChangeFamily f g r α t = 0 ↔ α (g t) = 0 := by
  have hcond : ∀ z : (pullback f g : Scheme.{u}),
      f (pullback.fst f g z) = g (pullback.snd f g z) := fun z => by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun m : (pullback f g : Scheme.{u}) ⟶ S => m z) (pullback.condition (f := f))
  have e₁ : ¬ baseChangeFamily f g r α t = 0 ↔
      t ∈ pullback.snd f g '' supportOfFamily (pullback.snd f g) (baseChangeFamily f g r α) := by
    rw [image_supportOfFamily_eq_setOf_ne_zero]
    exact Iff.rfl
  have e₂ : ¬ α (g t) = 0 ↔ g t ∈ f '' supportOfFamily f α := by
    rw [image_supportOfFamily_eq_setOf_ne_zero]
    exact Iff.rfl
  rw [← not_iff_not, e₁, e₂, supportOfFamily_baseChangeFamily]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨pullback.fst f g z, hz, hcond z⟩
  · rintro ⟨x, hx, hxt⟩
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x t hxt
    exact ⟨z, by simpa only [Set.mem_preimage, hz₁] using hx, hz₂⟩

/-- The vanishing locus of a base change is the inverse image of the vanishing locus. -/
theorem setOf_baseChangeFamily_eq_zero {X S S' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : S' ⟶ S) (r : ℕ) (α : FamilyOfCycles f r) :
    {t : S' | baseChangeFamily f g r α t = 0} = g ⁻¹' {s : S | α s = 0} :=
  Set.ext fun t => baseChangeFamily_apply_eq_zero_iff f g r α t

/-- The vanishing locus of a family of `r`-cycles is closed as soon as the vanishing locus of
its base change along a proper surjective morphism is closed. -/
theorem isClosed_vanishingLocus_of_proper_surjective {X S S' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : S' ⟶ S) [IsProper g] (hg : Function.Surjective g.base)
    (r : ℕ) (α : FamilyOfCycles f r)
    (h : IsClosed {t : S' | baseChangeFamily f g r α t = 0}) :
    IsClosed {s : S | α s = 0} := by
  rw [setOf_baseChangeFamily_eq_zero] at h
  rw [← Set.image_preimage_eq {s : S | α s = 0} hg]
  exact g.isProperMap.isClosedMap _ h

/-- The vanishing locus of a family of `r`-cycles is closed as soon as the vanishing loci of its
base changes along a jointly surjective family of open morphisms of the base are closed. -/
theorem isClosed_vanishingLocus_of_baseOpenCover {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (r : ℕ) (α : FamilyOfCycles f r) {ι : Type v} {V : ι → Scheme.{u}}
    (g : ∀ i, V i ⟶ S) (hopen : ∀ i, IsOpenMap (g i).base)
    (hcover : ⋃ i, Set.range (g i).base = Set.univ)
    (hclosed : ∀ i, IsClosed {t : V i | baseChangeFamily f (g i) r α t = 0}) :
    IsClosed {s : S | α s = 0} := by
  rw [← isOpen_compl_iff]
  have hunion : {s : S | α s = 0}ᶜ = ⋃ i, g i '' (g i ⁻¹' {s : S | α s = 0}ᶜ) := by
    ext s
    refine ⟨fun hs => ?_, ?_⟩
    · obtain ⟨-, ⟨i, rfl⟩, t, ht⟩ := hcover.symm.subset (Set.mem_univ s)
      exact Set.mem_iUnion.mpr ⟨i, ⟨t, by rwa [Set.mem_preimage, ht], ht⟩⟩
    · rintro ⟨-, ⟨i, rfl⟩, t, ht, rfl⟩
      exact ht
  rw [hunion]
  refine isOpen_iUnion fun i => hopen i _ ?_
  rw [Set.preimage_compl, ← setOf_baseChangeFamily_eq_zero]
  exact (hclosed i).isOpen_compl

/-! ### The vanishing locus under a closed immersion of the source -/

/-- Pushing a family of `r`-cycles forward along a closed immersion over the base leaves its
vanishing locus unchanged, pushforward along a closed immersion being injective on each
fibre. -/
theorem properPushforwardFamily_apply_eq_zero_iff {X Y S : Scheme.{u}} (sX : X ⟶ S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ S) [LocallyOfFiniteType sY] (i : X ⟶ Y)
    [IsClosedImmersion i] (hi : i ≫ sY = sX) (r : ℕ) (α : FamilyOfCycles sX r) (s : S) :
    properPushforwardFamily sX sY i hi r α s = 0 ↔ α s = 0 := by
  have hzero : fiberProperPushforward sX sY i hi s r 0 = 0 :=
    properPushforward_zero (fieldChowSituation (S.residueField s))
      (sX.fiberToSpecResidueField s) (sY.fiberToSpecResidueField s)
      (inducedFiberMap sX sY i hi s) (inducedFiberMap_fiberToSpecResidueField sX sY i hi s)
      (r : ℤ)
  rw [properPushforwardFamily_apply]
  exact ⟨fun h => fiberProperPushforward_injective sX sY i hi s r (by rw [h, hzero]),
    fun h => by rw [h, hzero]⟩

/-- The vanishing locus of a family of `r`-cycles is the vanishing locus of its pushforward along
a closed immersion of the source over the base. -/
theorem setOf_properPushforwardFamily_eq_zero {X Y S : Scheme.{u}} (sX : X ⟶ S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ S) [LocallyOfFiniteType sY] (i : X ⟶ Y)
    [IsClosedImmersion i] (hi : i ≫ sY = sX) (r : ℕ) (α : FamilyOfCycles sX r) :
    {s : S | properPushforwardFamily sX sY i hi r α s = 0} = {s : S | α s = 0} :=
  Set.ext fun s => properPushforwardFamily_apply_eq_zero_iff sX sY i hi r α s

/-! ### The vanishing locus under an open covering of the source -/

/-- A family of `r`-cycles vanishes on the fibre over `s` exactly when all of its restrictions
to the members of an open covering of the source do. -/
theorem fiberCycle_eq_zero_iff_forall_fiberCycleRestrict {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {r : ℕ} (α : FamilyOfCycles f r) {ι : Type v} {U : ι → Scheme.{u}}
    (fU : ∀ i, U i ⟶ S) [∀ i, LocallyOfFiniteType (fU i)] (j : ∀ i, U i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (h : ∀ i, j i ≫ f = fU i)
    (hcover : ⋃ i, Set.range (j i).base = Set.univ) (s : S) :
    α s = 0 ↔ ∀ i, fiberCycleRestrict f (fU i) (j i) (h i) s r (α s) = 0 := by
  refine ⟨fun hzero i => by rw [hzero, map_zero], fun hzero => ?_⟩
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x => ?_)
  obtain ⟨-, ⟨i, rfl⟩, u, hu⟩ := hcover.symm.subset (Set.mem_univ (f.fiberι s x))
  have hfu : fU i u = s := by
    have hmap := congrArg (fun m : U i ⟶ S => m u) (h i)
    simp only [Scheme.Hom.comp_apply] at hmap
    rw [← hmap, hu]
    exact (f.fiberHomeo s x).2
  obtain ⟨υ, hυ⟩ := exists_fiberRestrict_eq f (fU i) (j i) (h i) u s hfu x hu.symm
  have hcoeff := fiberCycleRestrict_apply f (fU i) (j i) (h i) s r (α s) υ
  rw [hυ, hzero i] at hcoeff
  exact hcoeff.symm

/-- The vanishing locus of a family of `r`-cycles is closed as soon as the vanishing loci of its
restrictions to the members of an open covering of the source are closed. -/
theorem isClosed_vanishingLocus_of_openCover {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {r : ℕ} (α : FamilyOfCycles f r) {ι : Type v} {U : ι → Scheme.{u}}
    (fU : ∀ i, U i ⟶ S) [∀ i, LocallyOfFiniteType (fU i)] (j : ∀ i, U i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (h : ∀ i, j i ≫ f = fU i)
    (hcover : ⋃ i, Set.range (j i).base = Set.univ)
    (hclosed : ∀ i, IsClosed {s : S | fiberCycleRestrict f (fU i) (j i) (h i) s r (α s) = 0}) :
    IsClosed {s : S | α s = 0} := by
  have hinter : {s : S | α s = 0} =
      ⋂ i, {s : S | fiberCycleRestrict f (fU i) (j i) (h i) s r (α s) = 0} := by
    ext s
    simpa only [Set.mem_ofPred_eq, Set.mem_iInter] using
      fiberCycle_eq_zero_iff_forall_fiberCycleRestrict f α fU j h hcover s
  rw [hinter]
  exact isClosed_iInter hclosed

/-! ### Stability of the vanishing locus under specialization -/

/-- The vanishing locus of a relative `r`-cycle is stable under specialization: the valuative
condition on a discrete valuation ring realizing the specialization carries the vanishing on the
generic fibre to the special fibre. -/
theorem fiberCycle_eq_zero_of_specializes {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] {r : ℕ} {α : FamilyOfCycles f r}
    (hα : IsRelativeCycle f r α) {s' s : S} (hsp : s' ⤳ s) (hzero : α s' = 0) : α s = 0 := by
  obtain ⟨R, _, _, _, g, hη, hs⟩ := AlgebraicGeometry.exists_dvr_morphism_of_specializes S hsp
  have hgen : baseChangeFamily f g r α (genericPoint (Spec (.of R))) = 0 :=
    (baseChangeFamily_apply_eq_zero_iff f g r α _).mpr (by rwa [hη])
  have hcond := hα R g
  rw [hgen, specializationCycle_zero (pullback.snd f g) r] at hcond
  have := (baseChangeFamily_apply_eq_zero_iff f g r α (IsLocalRing.closedPoint R)).mp hcond.symm
  rwa [hs] at this

/-- The vanishing locus of a relative `r`-cycle is stable under specialization. -/
theorem stableUnderSpecialization_setOf_eq_zero {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] {r : ℕ} (α : relativeCycles f r) :
    StableUnderSpecialization {s : S | (α : FamilyOfCycles f r) s = 0} :=
  fun _ _ hsp hzero => fiberCycle_eq_zero_of_specializes f α.2 hsp hzero

/-- The locus where two relative `r`-cycles have the same cycle on the fibre is stable under
specialization. -/
theorem stableUnderSpecialization_setOf_fiberCycle_eq {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] {r : ℕ} (α β : relativeCycles f r) :
    StableUnderSpecialization
      {s : S | (α : FamilyOfCycles f r) s = (β : FamilyOfCycles f r) s} := by
  rw [setOf_fiberCycle_eq_eq_setOf_sub_eq_zero]
  exact stableUnderSpecialization_setOf_eq_zero f (α - β)

/-! ### A closedness criterion on a locally Noetherian space -/

/-- In a Noetherian quasi-sober space, a subset `E` stable under specialization is closed as soon
as every point `η ∉ E` has an open neighbourhood containing no point of `E` that specializes
from `η`.

Noetherian induction on the closed subsets `Y` shows that `E ∩ Y` is closed. If `Y` is reducible
it is the union of two smaller closed subsets. If `Y` is irreducible with generic point `ζ`, then
either `ζ ∈ E`, so `Y ⊆ E` by stability under specialization, or the open neighbourhood `O` of
`ζ` provided by the hypothesis meets `Y` outside `E`, so that `E ∩ Y = E ∩ (Y \ O)` with
`Y \ O` a strictly smaller closed subset. -/
theorem isClosed_of_stableUnderSpecialization_of_forall_notMem {A : Type*} [TopologicalSpace A]
    [NoetherianSpace A] [QuasiSober A] {E : Set A} (hspec : StableUnderSpecialization E)
    (hnbhd : ∀ η ∉ E, ∃ O : Set A, IsOpen O ∧ η ∈ O ∧ ∀ t ∈ O, η ⤳ t → t ∉ E) :
    IsClosed E := by
  suffices h : ∀ Y : Closeds A, IsClosed (E ∩ Y) by simpa using h ⊤
  intro Y
  induction Y using WellFoundedLT.induction with
  | _ Y ih =>
  rcases eq_or_ne Y ⊥ with rfl | h₀
  · simp
  by_cases h₁ : IsPreirreducible (Y : Set A)
  · have hirr : IsIrreducible (Y : Set A) := ⟨Closeds.coe_nonempty.2 h₀, h₁⟩
    have hζ : closure {hirr.genericPoint} = (Y : Set A) := hirr.closure_genericPoint Y.isClosed
    have hmem : ∀ y ∈ (Y : Set A), hirr.genericPoint ⤳ y := fun y hy ↦
      specializes_iff_mem_closure.mpr (hζ.symm ▸ hy)
    by_cases hζE : hirr.genericPoint ∈ E
    · rw [Set.inter_eq_right.mpr fun y hy ↦ hspec (hmem y hy) hζE]
      exact Y.isClosed
    · obtain ⟨O, hO, hζO, hOE⟩ := hnbhd _ hζE
      let Y' : Closeds A := ⟨(Y : Set A) \ O, Y.isClosed.sdiff hO⟩
      have hlt : Y' < Y := by
        refine lt_of_le_of_ne (fun y hy ↦ hy.1) fun h ↦ ?_
        have hY : hirr.genericPoint ∈ (Y' : Set A) := by
          rw [h]
          exact hirr.isGenericPoint_genericPoint Y.isClosed |>.mem
        exact hY.2 hζO
      have heq : E ∩ (Y : Set A) = E ∩ (Y' : Set A) := by
        ext y
        refine ⟨fun ⟨hyE, hyY⟩ ↦ ⟨hyE, hyY, fun hyO ↦ hOE y hyO (hmem y hyY) hyE⟩,
          fun ⟨hyE, hyY, _⟩ ↦ ⟨hyE, hyY⟩⟩
      rw [heq]
      exact ih Y' hlt
  · simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at h₁
    obtain ⟨z₁, z₂, hz₁, hz₂, h, hz₁', hz₂'⟩ := h₁
    lift z₁ to Closeds A using hz₁
    lift z₂ to Closeds A using hz₂
    have heq : E ∩ (Y : Set A) = E ∩ ↑(Y ⊓ z₁) ∪ E ∩ ↑(Y ⊓ z₂) := by
      rw [Closeds.coe_inf, Closeds.coe_inf, ← Set.inter_union_distrib_left,
        ← Set.inter_union_distrib_left, Set.inter_eq_left.mpr h]
    rw [heq]
    exact (ih _ (inf_lt_left.2 hz₁')).union (ih _ (inf_lt_left.2 hz₂'))

/-- In a quasi-sober space every point of which has a Noetherian open neighbourhood, a subset `E`
stable under specialization is closed as soon as every point `η ∉ E` has an open neighbourhood
containing no point of `E` that specializes from `η`. Being closed is a local property, and on a
Noetherian open neighbourhood `isClosed_of_stableUnderSpecialization_of_forall_notMem`
applies. -/
theorem isClosed_of_stableUnderSpecialization_of_forall_notMem_of_isLocallyNoetherianSpace
    {A : Type*} [TopologicalSpace A] [QuasiSober A] (hA : IsLocallyNoetherianSpace A)
    {E : Set A} (hspec : StableUnderSpecialization E)
    (hnbhd : ∀ η ∉ E, ∃ O : Set A, IsOpen O ∧ η ∈ O ∧ ∀ t ∈ O, η ⤳ t → t ∉ E) :
    IsClosed E := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨U, hUopen, hxU, hUnoeth⟩ := hA x
  have hemb : Topology.IsOpenEmbedding ((↑) : U → A) := hUopen.isOpenEmbedding_subtypeVal
  have : QuasiSober U := hemb.quasiSober
  have hclosed : IsClosed (Subtype.val ⁻¹' E : Set U) := by
    refine isClosed_of_stableUnderSpecialization_of_forall_notMem
      (hspec.preimage continuous_subtype_val) fun η hη ↦ ?_
    obtain ⟨O, hO, hηO, hOE⟩ := hnbhd η hη
    exact ⟨Subtype.val ⁻¹' O, hO.preimage continuous_subtype_val, hηO,
      fun t ht hηt ↦ hOE t ht (hηt.map continuous_subtype_val)⟩
  refine mem_nhds_iff.mpr ⟨_, ?_, hemb.isOpenMap _ hclosed.isOpen_compl, ⟨⟨x, hxU⟩, hx, rfl⟩⟩
  rintro _ ⟨⟨y, hy⟩, hy', rfl⟩
  exact hy'

/-- In a Noetherian sober space, a constructible set `C` containing a point `η` contains every
specialization of `η` lying in a suitable open neighbourhood of `η`.

The set `D` of specializations of `η` outside `C` is constructible, and a point in the closure
of a constructible set of a spectral space specializes from a point of that set (Stacks 0903(1));
so `η` is not in the closure of `D`, whose complement is the neighbourhood sought. -/
theorem exists_isOpen_forall_specializes_mem_of_isConstructible {A : Type*}
    [TopologicalSpace A] [NoetherianSpace A] [QuasiSober A] [T0Space A] {C : Set A}
    (hC : Topology.IsConstructible C) {η : A} (hη : η ∈ C) :
    ∃ O : Set A, IsOpen O ∧ η ∈ O ∧ ∀ t ∈ O, η ⤳ t → t ∈ C := by
  have := SpectralSpace.of_noetherianSpace A
  have hcl : Topology.IsConstructible (closure ({η} : Set A)) :=
    Topology.isConstructible_compl.mp
      ((NoetherianSpace.isCompact _).isConstructible isClosed_closure.isOpen_compl)
  have hD : Topology.IsConstructible (closure ({η} : Set A) ∩ Cᶜ) := hcl.inter hC.compl
  refine ⟨(closure (closure ({η} : Set A) ∩ Cᶜ))ᶜ, isClosed_closure.isOpen_compl, fun hηD ↦ ?_,
    fun t ht hηt ↦ ?_⟩
  · obtain ⟨z, hz, hzη⟩ := hD.exists_mem_specializes_of_mem_closure hηD
    have hz' : z = η := (hzη.antisymm (specializes_iff_mem_closure.mpr hz.1)).eq
    exact hz.2 (hz' ▸ hη)
  · by_contra htC
    exact ht (subset_closure ⟨specializes_iff_mem_closure.mp hηt, htC⟩)

/-! ### Images of closures of points -/

/-- Let `f : X ⟶ S` be locally of finite type with `S` locally Noetherian and let `a ∈ X`. Every
specialization of `f a` in a suitable open neighbourhood of `f a` is the image of a
specialization of `a`.

Choose an affine open `V ∋ f a` and an affine open `W ∋ a` mapping into `V`. By Chevalley's
theorem the image in `V` of the closure of `a` in `W` is constructible, and it contains `f a`;
the neighbourhood is then given by
`exists_isOpen_forall_specializes_mem_of_isConstructible`. -/
theorem exists_isOpen_forall_specializes_exists_specializes {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (a : X) :
    ∃ O : Set S, IsOpen O ∧ f a ∈ O ∧ ∀ t ∈ O, f a ⤳ t → ∃ b : X, a ⤳ b ∧ f b = t := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨V, hV, hfaV, -⟩ := (Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
    (show f a ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨W, hW, haW, hWV⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show a ∈ f ⁻¹ᵁ V from hfaV)
  have : IsAffine (V : Scheme.{u}) := hV
  have : IsAffine (W : Scheme.{u}) := hW
  have : IsNoetherian (V : Scheme.{u}) := {}
  have : IsNoetherian (W : Scheme.{u}) := {}
  let g : (W : Scheme.{u}) ⟶ V := f.resLE V W hWV
  have hg : ∀ w, ((Scheme.Opens.ι V) (g w) : S) = f ((Scheme.Opens.ι W) w) := fun w ↦ by
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply]
  let a' : (W : Scheme.{u}) := ⟨a, haW⟩
  let η' : (V : Scheme.{u}) := ⟨f a, hfaV⟩
  have hcl : Topology.IsConstructible (closure ({a'} : Set (W : Scheme.{u}))) :=
    Topology.isConstructible_compl.mp
      ((NoetherianSpace.isCompact _).isConstructible isClosed_closure.isOpen_compl)
  have hC := g.isConstructible_image hcl
  have hη' : η' ∈ g '' closure ({a'} : Set (W : Scheme.{u})) := by
    refine ⟨a', subset_closure rfl, (Scheme.Opens.ι V).isOpenEmbedding.injective ?_⟩
    rw [hg]
    rfl
  obtain ⟨O, hO, hηO, hOC⟩ := exists_isOpen_forall_specializes_mem_of_isConstructible hC hη'
  refine ⟨(Scheme.Opens.ι V) '' O, (Scheme.Opens.ι V).isOpenEmbedding.isOpenMap _ hO,
    ⟨η', hηO, rfl⟩, ?_⟩
  rintro _ ⟨t, ht, rfl⟩ hηt
  have hηt' : η' ⤳ t := (Scheme.Opens.ι V).isOpenEmbedding.isInducing.specializes_iff.mp hηt
  obtain ⟨w, hw, hwt⟩ := hOC t ht hηt'
  refine ⟨(Scheme.Opens.ι W) w,
    (specializes_iff_mem_closure.mpr hw).map (Scheme.Opens.ι W).continuous, ?_⟩
  rw [← hg, hwt]

/-! ### Points outside the equality locus -/

/-- Let `δ` be a relative `r`-cycle on `X/S` and let `a` be a point of its support at which the
fibre cycle `δ_{f a}` is effective. Then `δ` is nonzero on the fibre over every specialization of
`f a` lying in a suitable open neighbourhood of `f a`: such a specialization is the image of a
specialization `b` of `a`, and `b` lies in the support of `δ` by
`Stacks.Chow.mem_supportOfFamily_of_specializes`. -/
theorem exists_isOpen_forall_specializes_ne_zero_of_isEffectiveCycle {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian S] {r : ℕ}
    {δ : FamilyOfCycles f r} (hδ : IsRelativeCycle f r δ) {a : X}
    (heff : IsEffectiveCycle (δ (f a) : AlgebraicCycle (f.fiber (f a)) ℤ))
    (ha : a ∈ supportOfFamily f δ) :
    ∃ O : Set S, IsOpen O ∧ f a ∈ O ∧ ∀ t ∈ O, f a ⤳ t → δ t ≠ 0 := by
  obtain ⟨O, hO, haO, hOt⟩ := exists_isOpen_forall_specializes_exists_specializes f a
  refine ⟨O, hO, haO, fun t ht hat ↦ ?_⟩
  obtain ⟨b, hab, rfl⟩ := hOt t ht hat
  have hb : f b ∈ f '' supportOfFamily f δ :=
    ⟨b, mem_supportOfFamily_of_specializes f r δ hδ hab heff ha, rfl⟩
  rwa [image_supportOfFamily_eq_setOf_ne_zero] at hb

/-- Let `γ` be a relative `r`-cycle on `X/S` with `γ_η ≠ 0`. Then `γ_t ≠ 0` for every
specialization `t` of `η` lying in a suitable open neighbourhood of `η`.

Choose a point `ξ` of the fibre over `η` at which `γ_η` has a nonzero coefficient `m`. The other
points of the support of `γ_η` are generic points of integral closed subschemes of the same
dimension `r`, so none of them specializes to `ξ`; local finiteness of the support then gives an
open `U ⊆ X` through `ξ` on which `γ_η` is `m[ξ]`. The restriction of `±γ` to `U` is a relative
`r`-cycle whose fibre cycle over `η` is effective, and
`exists_isOpen_forall_specializes_ne_zero_of_isEffectiveCycle` applies to it at `ξ`. -/
theorem exists_isOpen_forall_specializes_ne_zero {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] {r : ℕ} {γ : FamilyOfCycles f r}
    (hγ : IsRelativeCycle f r γ) {η : S} (hη : γ η ≠ 0) :
    ∃ O : Set S, IsOpen O ∧ η ∈ O ∧ ∀ t ∈ O, η ⤳ t → γ t ≠ 0 := by
  classical
  set c : AlgebraicCycle (f.fiber η) ℤ := (γ η : AlgebraicCycle (f.fiber η) ℤ) with hc
  obtain ⟨ξ, hξ⟩ : ∃ ξ, c ξ ≠ 0 := by
    by_contra! h
    exact hη (Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ h y))
  -- distinct points of the support do not specialize to one another
  have hdim : ∀ y, c y ≠ 0 → relativeDimension
      (fieldChowSituation ↥(S.residueField η)).dimensionFunction
      (f.fiberToSpecResidueField η) y = (r : ℤ) :=
    (mem_cyclesOfDimension_iff_forall_point _ _ _ _).1 (γ η).2
  have hincomp : ∀ y, c y ≠ 0 → y ≠ ξ → ξ ∉ closure ({y} : Set (f.fiber η)) := by
    intro y hy hne hmem
    obtain ⟨d, hd⟩ := relativeDimension_isDimensionFunction
      (fieldChowSituation ↥(S.residueField η)).isUniversallyCatenary
      (fieldChowSituation ↥(S.residueField η)).dimensionFunction (f.fiberToSpecResidueField η)
    have hlt := d.strictAnti_specializes (specializes_iff_mem_closure.mpr hmem) hne
    rw [hd ξ, hd y, hdim y hy, hdim ξ hξ] at hlt
    exact lt_irrefl _ hlt
  -- an open neighbourhood of `ξ` in the fibre meeting the support only in `ξ`
  obtain ⟨N, hN, hfin⟩ := Function.locallyFinsupp.locallyFiniteSupport c ξ
  set B : Set (f.fiber η) := (N ∩ Function.support c) \ {ξ} with hBdef
  have hB : B.Finite := hfin.sdiff
  set Wf : Set (f.fiber η) := interior N \ ⋃ y ∈ B, closure {y} with hWfdef
  have hWf : IsOpen Wf := isOpen_interior.sdiff (hB.isClosed_biUnion fun _ _ ↦ isClosed_closure)
  have hξW : ξ ∈ Wf := by
    refine ⟨mem_interior_iff_mem_nhds.mpr hN, fun hξB ↦ ?_⟩
    obtain ⟨y, hyB, hξy⟩ := Set.mem_iUnion₂.mp hξB
    exact hincomp y hyB.1.2 hyB.2 hξy
  have hW0 : ∀ y ∈ Wf, y ≠ ξ → c y = 0 := by
    intro y hy hne
    by_contra h
    exact hy.2 (Set.mem_iUnion₂.mpr ⟨y, ⟨⟨interior_subset hy.1, h⟩, hne⟩, subset_closure rfl⟩)
  obtain ⟨O', hO', hO'W⟩ := (f.fiberι η).isEmbedding.isInducing.isOpen_iff.mp hWf
  -- the restriction of `γ` to the corresponding open subscheme of `X`
  let U : X.Opens := ⟨O', hO'⟩
  let fU : (U : Scheme.{u}) ⟶ S := Scheme.Opens.ι U ≫ f
  let γ' : FamilyOfCycles fU r := fun s ↦ fiberCycleRestrict f fU (Scheme.Opens.ι U) rfl s r (γ s)
  have hγ' : IsRelativeCycle fU r γ' := isRelativeCycle_fiberCycleRestrict f fU _ rfl r hγ
  have hxU : f.fiberι η ξ ∈ U := by
    change f.fiberι η ξ ∈ O'
    rw [← Set.mem_preimage, hO'W]
    exact hξW
  let x₀ : (U : Scheme.{u}) := ⟨f.fiberι η ξ, hxU⟩
  have hfx : fU x₀ = η := fiberι_apply_base f η ξ
  have hfib : ∀ υ : fU.fiber η, f.fiberι η (fiberRestrict f fU (Scheme.Opens.ι U) rfl η υ) =
      Scheme.Opens.ι U (fU.fiberι η υ) := fun υ ↦ by
    rw [← Scheme.Hom.comp_apply, fiberRestrict_fiberι, Scheme.Hom.comp_apply]
  obtain ⟨υ, hυ⟩ := exists_fiberRestrict_eq f fU (Scheme.Opens.ι U) rfl x₀ η hfx ξ rfl
  have hυx : fU.fiberι η υ = x₀ := by
    apply (Scheme.Opens.ι U).isOpenEmbedding.injective
    rw [← hfib, hυ]
    rfl
  have hcoef : ∀ υ' : fU.fiber η, fiberRestrict f fU (Scheme.Opens.ι U) rfl η υ' ≠ ξ →
      (γ' η : AlgebraicCycle (fU.fiber η) ℤ) υ' = 0 := by
    intro υ' hne
    rw [fiberCycleRestrict_apply]
    refine hW0 _ ?_ hne
    rw [← hO'W, Set.mem_preimage, hfib]
    exact (fU.fiberι η υ').2
  have hυc : (γ' η : AlgebraicCycle (fU.fiber η) ℤ) υ = c ξ := by
    rw [fiberCycleRestrict_apply, hυ]
  -- `±γ'` is effective over `η`
  obtain ⟨δ, hδ, hδη, hδυ, hδt⟩ : ∃ δ : FamilyOfCycles fU r, IsRelativeCycle fU r δ ∧
      IsEffectiveCycle (δ η : AlgebraicCycle (fU.fiber η) ℤ) ∧
      (δ η : AlgebraicCycle (fU.fiber η) ℤ) υ ≠ 0 ∧ ∀ t, γ t = 0 → δ t = 0 := by
    rcases lt_or_gt_of_ne hξ with hneg | hpos
    · refine ⟨-γ', isRelativeCycle_neg fU r hγ', fun υ' ↦ ?_, ?_, fun t ht ↦ ?_⟩
      · change 0 ≤ -(γ' η : AlgebraicCycle (fU.fiber η) ℤ) υ'
        by_cases h : fiberRestrict f fU (Scheme.Opens.ι U) rfl η υ' = ξ
        · rw [fiberCycleRestrict_apply, h]
          exact (neg_pos.mpr hneg).le
        · rw [hcoef υ' h, neg_zero]
      · change -(γ' η : AlgebraicCycle (fU.fiber η) ℤ) υ ≠ 0
        rw [hυc]
        exact neg_ne_zero.mpr hξ
      · change -(fiberCycleRestrict f fU (Scheme.Opens.ι U) rfl t r (γ t)) = 0
        rw [ht, map_zero, neg_zero]
    · refine ⟨γ', hγ', fun υ' ↦ ?_, ?_, fun t ht ↦ ?_⟩
      · by_cases h : fiberRestrict f fU (Scheme.Opens.ι U) rfl η υ' = ξ
        · rw [fiberCycleRestrict_apply, h]
          exact hpos.le
        · rw [hcoef υ' h]
      · rw [hυc]
        exact hξ
      · change fiberCycleRestrict f fU (Scheme.Opens.ι U) rfl t r (γ t) = 0
        rw [ht, map_zero]
  have heff : ∀ s, s = η → IsEffectiveCycle (δ s : AlgebraicCycle (fU.fiber s) ℤ) := by
    rintro s rfl
    exact hδη
  have hsupp : x₀ ∈ supportOfFamily fU δ :=
    (mem_supportOfFamily fU δ x₀).mpr ⟨η, υ, subset_tsupport _ hδυ, hυx⟩
  obtain ⟨O, hO, hxO, hOt⟩ :=
    exists_isOpen_forall_specializes_ne_zero_of_isEffectiveCycle fU hδ (heff _ hfx) hsupp
  rw [hfx] at hxO hOt
  exact ⟨O, hO, hxO, fun t ht hηt h0 ↦ hOt t ht hηt (hδt t h0)⟩

/-! ### The equality locus is closed -/

/-- **Stacks Project, Lemma 0H5C.** Let `f : X ⟶ S` be a morphism of schemes with `S` locally
Noetherian and `f` locally of finite type, let `r ≥ 0` and let `α, β ∈ z(X/S, r)`. Then the set
`E = {s ∈ S : α_s = β_s}` is closed in `S`.

With `γ = α - β`, the set `E` is the vanishing locus of the relative cycle `γ`. It is stable
under specialization, and every point `η ∉ E` has an open neighbourhood containing no point of
`E` specializing from `η` (`Stacks.Chow.exists_isOpen_forall_specializes_ne_zero`); on a locally
Noetherian space these two properties make `E` closed. -/
@[stacks 0H5C]
theorem isClosed_setOf_fiberCycle_eq {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] {r : ℕ} (α β : relativeCycles f r) :
    IsClosed {s : S | (α : FamilyOfCycles f r) s = (β : FamilyOfCycles f r) s} := by
  rw [setOf_fiberCycle_eq_eq_setOf_sub_eq_zero]
  refine isClosed_of_stableUnderSpecialization_of_forall_notMem_of_isLocallyNoetherianSpace
    (AlgebraicGeometry.isLocallyNoetherianSpace_of_isLocallyNoetherian S)
    (stableUnderSpecialization_setOf_eq_zero f (α - β))
    fun η hη ↦ exists_isOpen_forall_specializes_ne_zero f (α - β).2 hη

end Stacks.Chow

end
