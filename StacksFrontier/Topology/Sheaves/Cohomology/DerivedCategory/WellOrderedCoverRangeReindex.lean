module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingOverAWellOrderedCover
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOverACover

/-!
# Reindexing a well ordered increasing cover by its range

`Stacks.DerivedGlueing.GluesAlongWellOrderedCover.{v}` quantifies over an index type `E` in an
*arbitrary* universe `v`, while the route to it through complexes —
`Stacks.DerivedGlueing.ProducesComplexSystem` and the assembly
`Stacks.DerivedGlueing.exists_glueing_of_complexSystem` — forms a colimit of an `E`-indexed
diagram inside `SheafOfModules.{u}`, so it is stated at `E : Type u`.  An arbitrary monotone
`W : E → Opens X.carrier` is reduced to its range, which is a chain inside
`Opens X.carrier : Type u`.

This file carries that reduction, at the level of an arbitrary complete lattice, where it is a
statement about orders and nothing else.  Given a family `W : E → L` indexed by a well ordered
`E : Type v` and increasing along every pair `β < α`, its range is a subset of `L`, hence a type
in the universe of `L`, and:

* it is linearly ordered by the order of `L` — `Stacks.DerivedGlueing.rangeLinearOrder`;
* it is well ordered — `Stacks.DerivedGlueing.wellFounded_lt_range`;
* reindexed by the least index attaining each value, it satisfies the continuity hypothesis
  `hlimit` of `Stacks.DerivedGlueing.exists_glueing_of_wellOrderedCover` whenever `W` does —
  `Stacks.DerivedGlueing.leastIndex_eq_iSup_of_not_isPred`;
* and it has the same supremum, so it satisfies `hcover` whenever `W` does —
  `Stacks.DerivedGlueing.iSup_apply_leastIndex`.

The reindexing map is `Stacks.DerivedGlueing.leastIndex`, which sends a value of the range to the
least index attaining it.  Reading the reindexed family as `W ∘ leastIndex W` rather than as the
inclusion of the range into `L` is deliberate and is what keeps the reduction usable downstream:
the prescribed objects of [Stacks, Tag 0D6B] live in `OpenDerivedCategory X (W α)`, so defining
the reindexed family as a composite with `W` makes the reindexed objects `K ∘ leastIndex W`
typecheck with no transport at all, while defining it as `Subtype.val` would require carrying
the equality `W (leastIndex W V) = V` through every object and morphism.

## Main definitions

* `Stacks.DerivedGlueing.leastIndex`: the least index at which a family attains a given value of
  its range.
* `Stacks.DerivedGlueing.rangeLinearOrder`: the linear order on the range of an increasing
  family.

## Main results

* `Stacks.DerivedGlueing.apply_leastIndex`, `Stacks.DerivedGlueing.leastIndex_le`: the defining
  properties of the least index.
* `Stacks.DerivedGlueing.leastIndex_strictMono`: the least index is strictly monotone, which is
  what transports both well-foundedness and the increasingness hypothesis.
* `Stacks.DerivedGlueing.wellFounded_lt_range`: the range of an increasing family indexed by a
  well ordered set is well ordered.
* `Stacks.DerivedGlueing.not_isPred_leastIndex`: a value of the range with no immediate
  predecessor *in the range* is attained first at an index with no immediate predecessor in the
  index set.  This is the step that makes the continuity hypothesis transport, and it is the only
  one that is not formal.
* `Stacks.DerivedGlueing.leastIndex_eq_iSup_of_not_isPred`: the continuity hypothesis, reindexed.
* `Stacks.DerivedGlueing.iSup_apply_leastIndex`: the covering hypothesis, reindexed.
* `Stacks.DerivedGlueing.leastIndex_eq_iSup_withTopNatSegments`: a NON-DEGENERATE instance of all
  of the above, machine-checked -- the chain of initial segments of `ℕ` with a top stage
  adjoined, indexed by `ULift (WithTop ℕ) : Type 1` over the lattice `Set ℕ : Type 0`, so the
  index universe is genuinely the larger one.  Its top stage is a *genuine* limit: it is the
  union of the proper stages, it is not `⊥`, and it is not equal to any of them
  (`Stacks.DerivedGlueing.withTopNatSegments_ne_top`,
  `Stacks.DerivedGlueing.withTopNatSegments_ne`).  Without it the continuity result above could
  hold vacuously, or only at `⊥`.

## Use in Tag 0D6B

The reduction of `GluesAlongWellOrderedCover.{v}` to `GluesAlongWellOrderedCover.{u}` is
`Stacks.DerivedGlueing.gluesAlongWellOrderedCover` in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.WellOrderedCoverRecursion`: the
identification produced at the least stage attaining an open is carried to every later stage
attaining the same open by `Stacks.DerivedGlueing.isoOfRestrictionObjIso`, and its compatibility
with the prescribed transitions is checked after restriction across the equality of opens, by
`Stacks.DerivedGlueing.restriction_map_injective_of_antisymm`.

Nothing in this file is tagged: a reindexing of a hypothesis is a step of a proof, not a clause
of the statement of any tag.

## References

* [Stacks Project, Tag 0D6B](https://stacks.math.columbia.edu/tag/0D6B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Set

namespace Stacks.DerivedGlueing

universe u v

section CompleteLattice

variable {L : Type u} [CompleteLattice L] {E : Type v} [LinearOrder E] [WellFoundedLT E]

/-- **The least index at which a family attains a given value of its range.** -/
noncomputable def leastIndex (W : E → L) (V : ↥(Set.range W)) : E :=
  (wellFounded_lt (α := E)).min {β | W β = V.1} V.2

omit [CompleteLattice L] in
/-- The least index attains the value it was chosen for. -/
theorem apply_leastIndex (W : E → L) (V : ↥(Set.range W)) : W (leastIndex W V) = V.1 :=
  (wellFounded_lt (α := E)).min_mem {β | W β = V.1} V.2

omit [CompleteLattice L] in
/-- The least index is least: any index attaining the same value is at least it. -/
theorem leastIndex_le (W : E → L) (V : ↥(Set.range W)) {β : E} (h : W β = V.1) :
    leastIndex W V ≤ β :=
  not_lt.mp ((wellFounded_lt (α := E)).not_lt_min {β | W β = V.1} h)

omit [CompleteLattice L] in
/-- The least index of the value of the family at `α` is at most `α`. -/
theorem leastIndex_self_le (W : E → L) (α : E) :
    leastIndex W ⟨W α, ⟨α, rfl⟩⟩ ≤ α :=
  leastIndex_le W _ rfl

omit [WellFoundedLT E] in
/-- **A family increasing along every strictly ordered pair is monotone.** -/
theorem apply_le_apply_of_le {W : E → L} (hmono : ∀ β α : E, β < α → W β ≤ W α) {γ δ : E}
    (h : γ ≤ δ) : W γ ≤ W δ := by
  rcases eq_or_lt_of_le h with rfl | h
  · exact le_rfl
  · exact hmono _ _ h

/-- **An index strictly below the least index of a value attains a strictly smaller value.**
It attains at most that value because the family is increasing, and not that value because the
least index is least. -/
theorem apply_lt_of_lt_leastIndex {W : E → L} (hmono : ∀ β α : E, β < α → W β ≤ W α)
    (V : ↥(Set.range W)) {γ : E} (hγ : γ < leastIndex W V) : W γ < V.1 := by
  have hle : W γ ≤ V.1 := by
    rw [← apply_leastIndex W V]
    exact hmono γ _ hγ
  exact lt_of_le_of_ne hle fun h => absurd (leastIndex_le W V h) (not_le.mpr hγ)

/-- **An index attaining a value strictly below a given one is strictly below that value's least
index.** -/
theorem lt_leastIndex_of_apply_lt {W : E → L} (hmono : ∀ β α : E, β < α → W β ≤ W α)
    (V : ↥(Set.range W)) {γ : E} (hγ : W γ < V.1) : γ < leastIndex W V := by
  by_contra h
  have hle : V.1 ≤ W γ := by
    rw [← apply_leastIndex W V]
    exact apply_le_apply_of_le hmono (not_lt.mp h)
  exact absurd hle hγ.not_ge

/-- **The least index is strictly monotone on the range.** -/
theorem leastIndex_strictMono {W : E → L} (hmono : ∀ β α : E, β < α → W β ≤ W α)
    {V U : ↥(Set.range W)} (h : V.1 < U.1) : leastIndex W V < leastIndex W U :=
  lt_leastIndex_of_apply_lt hmono U (by rwa [apply_leastIndex W V])

/-- **The range of an increasing family is linearly ordered** by the order of the lattice: two
values of an increasing family are comparable because their indices are. -/
@[instance_reducible]
noncomputable def rangeLinearOrder {W : E → L} (hmono : ∀ β α : E, β < α → W β ≤ W α) :
    LinearOrder ↥(Set.range W) :=
  { (inferInstance : PartialOrder ↥(Set.range W)) with
    le_total := by
      rintro ⟨_, β, rfl⟩ ⟨_, α, rfl⟩
      rcases lt_trichotomy β α with h | rfl | h
      · exact Or.inl (hmono β α h)
      · exact Or.inl le_rfl
      · exact Or.inr (hmono α β h)
    toDecidableLE := Classical.decRel _ }

/-- **The range of an increasing family indexed by a well ordered set is well ordered.** The
least index is a strictly monotone map from the range to the index set, so the order on the range
is a subrelation of the pullback of a well founded one. -/
theorem wellFounded_lt_range {W : E → L} (hmono : ∀ β α : E, β < α → W β ≤ W α) :
    WellFounded ((· < ·) : ↥(Set.range W) → ↥(Set.range W) → Prop) :=
  Subrelation.wf (fun {_ _} h => leastIndex_strictMono hmono (Subtype.coe_lt_coe.mpr h))
    (InvImage.wf (leastIndex W) (wellFounded_lt (α := E)))

/-- **A value of the range with no immediate predecessor in the range is attained first at an
index with no immediate predecessor in the index set.**

This is the one step of the reindexing that is not formal, and it is what makes the continuity
hypothesis of [Stacks, Tag 0D6B] transport to the range.  If the least index `b` of `V` had an
immediate predecessor `δ`, then `W δ` would be an immediate predecessor of `V` in the range: it
is strictly below `V` because `δ < b`, and every value strictly below `V` is attained at some
index strictly below `b`, hence at most `δ`, hence is at most `W δ`. -/
theorem not_isPred_leastIndex {W : E → L} (hmono : ∀ β α : E, β < α → W β ≤ W α)
    {V : ↥(Set.range W)}
    (hV : ¬ ∃ U : ↥(Set.range W), U.1 < V.1 ∧ ∀ T : ↥(Set.range W), T.1 < V.1 → T.1 ≤ U.1) :
    ¬ ∃ δ : E, δ < leastIndex W V ∧ ∀ γ : E, γ < leastIndex W V → γ ≤ δ := by
  rintro ⟨δ, hδb, hδ⟩
  refine hV ⟨⟨W δ, ⟨δ, rfl⟩⟩, apply_lt_of_lt_leastIndex hmono V hδb, ?_⟩
  rintro ⟨_, γ, rfl⟩ hT
  exact apply_le_apply_of_le hmono (hδ γ (lt_leastIndex_of_apply_lt hmono V hT))

/-- **The continuity hypothesis of [Stacks, Tag 0D6B], reindexed by the range.** If the family
is continuous at the stages with no immediate predecessor, then so is its reindexing by the
range: a value with no immediate predecessor in the range is the supremum of the values strictly
below it.

This is the hypothesis `hlimit` of
`Stacks.DerivedGlueing.exists_glueing_of_wellOrderedCover` for the reindexed family.  The proof
is `Stacks.DerivedGlueing.not_isPred_leastIndex` followed by the identification of the two
suprema: an index below the least index of `V` contributes the value it attains, and a value
below `V` is attained at its own least index, which is below that of `V`. -/
theorem leastIndex_eq_iSup_of_not_isPred {W : E → L} (hmono : ∀ β α : E, β < α → W β ≤ W α)
    (hlimit : ∀ α : E, (¬ ∃ β : E, β < α ∧ ∀ γ : E, γ < α → γ ≤ β) →
      W α = ⨆ (β : E) (_ : β < α), W β)
    {V : ↥(Set.range W)}
    (hV : ¬ ∃ U : ↥(Set.range W), U.1 < V.1 ∧ ∀ T : ↥(Set.range W), T.1 < V.1 → T.1 ≤ U.1) :
    W (leastIndex W V) = ⨆ (U : ↥(Set.range W)) (_ : U.1 < V.1), W (leastIndex W U) := by
  rw [hlimit _ (not_isPred_leastIndex hmono hV)]
  refine le_antisymm (iSup₂_le fun γ hγ => ?_) (iSup₂_le fun U hU => ?_)
  · exact le_iSup₂_of_le ⟨W γ, ⟨γ, rfl⟩⟩ (apply_lt_of_lt_leastIndex hmono V hγ)
      (apply_leastIndex W ⟨W γ, ⟨γ, rfl⟩⟩).ge
  · exact le_iSup₂_of_le (leastIndex W U) (leastIndex_strictMono hmono hU) le_rfl

/-- **The covering hypothesis of [Stacks, Tag 0D6B], reindexed by the range.** Reindexing by the
range does not change the supremum of the family, so the reindexed family covers exactly when
the original does.  This is the hypothesis `hcover` of
`Stacks.DerivedGlueing.exists_glueing_of_wellOrderedCover` for the reindexed family. -/
theorem iSup_apply_leastIndex (W : E → L) :
    (⨆ V : ↥(Set.range W), W (leastIndex W V)) = ⨆ α : E, W α :=
  le_antisymm (iSup_le fun V => le_iSup W (leastIndex W V))
    (iSup_le fun α => le_iSup_of_le ⟨W α, ⟨α, rfl⟩⟩ (apply_leastIndex W ⟨W α, ⟨α, rfl⟩⟩).ge)

end CompleteLattice

section Restriction

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-- **A displayed restriction across an equality of opens reflects isomorphisms.** If `U ≤ V`
and `V ≤ U`, so that the two opens are equal, then an isomorphism between the restrictions of
two objects of `D(𝒪_V)` to `U` comes from an isomorphism between the objects themselves.

This is the primitive the reindexing of [Stacks, Tag 0D6B] by the range of its cover needs: the
reindexed stage of `α` is `W (leastIndex W ⟨W α, _⟩)`, which is equal to `W α` but is not the
same term, so an identification produced over the reindexed stage reaches the prescribed object
`K α` only across that equality.  Once the two opens are identified the displayed restriction is
the identity functor, by `Stacks.DerivedGlueing.restrictionSelfIso`. -/
def isoOfRestrictionObjIso (S : LocallyGiven X) {U V : Opens X.carrier}
    (hUV : U ≤ V) (hVU : V ≤ U) {P Q : OpenDerivedCategory X V}
    (e : (S.restriction U V hUV).obj P ≅ (S.restriction U V hUV).obj Q) : P ≅ Q := by
  obtain rfl : U = V := le_antisymm hUV hVU
  exact ((restrictionSelfIso S U hUV).app P).symm ≪≫ e ≪≫ (restrictionSelfIso S U hUV).app Q

/-- **A displayed restriction across an equality of opens is faithful.** The companion of
`Stacks.DerivedGlueing.isoOfRestrictionObjIso`: once the two opens are identified the displayed
restriction is the identity functor, which is faithful by
`Stacks.DerivedGlueing.restrictionSelf_map_injective`. -/
theorem restriction_map_injective_of_antisymm (S : LocallyGiven X) {U V : Opens X.carrier}
    (hUV : U ≤ V) (hVU : V ≤ U) {P Q : OpenDerivedCategory X V} {f g : P ⟶ Q}
    (h : (S.restriction U V hUV).map f = (S.restriction U V hUV).map g) : f = g := by
  obtain rfl : U = V := le_antisymm hUV hVU
  exact restrictionSelf_map_injective S U hUV h

end Restriction

/-! ### A non-degenerate witness, at two different universes

The reindexing above is quantified over a family `W : E → L` with `E` and `L` in unrelated
universes, and its main result speaks about a value of the range with no immediate predecessor
there.  Nothing so far says that such a value exists, or that it is anything other than `⊥` --
which is the shape in which a statement about a limit stage can be true and empty.  This section
supplies a witness in which it is neither.
-/

/-- The witness: `E = ULift (WithTop ℕ)` in `Type 1`, `L = Set ℕ` in `Type 0` -- so the index
universe is genuinely larger than the lattice universe, which is the configuration the
reindexing exists for.  `W` is the chain of initial segments of `ℕ`, with the adjoined top
carrying all of `ℕ`.  It is strictly increasing, it covers, it is continuous at both of its
non-successor stages, and its top stage is a GENUINE LIMIT: `univ` is the union of the `Iio n`
and is not any one of them. -/
def withTopNatSegments : ULift.{1, 0} (WithTop ℕ) → Set ℕ :=
  fun x => WithTop.recTopCoe Set.univ (fun n => Set.Iio n) x.down

/-- At a finite index `n`, `withTopNatSegments` is the initial segment `Set.Iio n`. -/
theorem withTopNatSegments_coe (n : ℕ) : withTopNatSegments ⟨(n : WithTop ℕ)⟩ = Set.Iio n := rfl

/-- At the top index, `withTopNatSegments` is all of `ℕ`. -/
theorem withTopNatSegments_top : withTopNatSegments ⟨⊤⟩ = Set.univ := rfl

/-- `withTopNatSegments` is monotone with respect to the strict order on indices. -/
theorem withTopNatSegments_mono : ∀ β α : ULift.{1, 0} (WithTop ℕ), β < α →
    withTopNatSegments β ≤ withTopNatSegments α := by
  rintro ⟨β⟩ ⟨α⟩ h
  replace h : β < α := h
  induction β using WithTop.recTopCoe with
  | top => exact absurd h (by simp)
  | coe n =>
    induction α using WithTop.recTopCoe with
    | top => exact le_top
    | coe m =>
      show Set.Iio n ⊆ Set.Iio m
      exact Set.Iio_subset_Iio (le_of_lt (by exact_mod_cast h))

/-- The stages of `withTopNatSegments` cover `ℕ`: their supremum is `⊤`. -/
theorem iSup_withTopNatSegments : (⨆ α : ULift.{1, 0} (WithTop ℕ), withTopNatSegments α) = ⊤ :=
  top_le_iff.mp (le_iSup_of_le ⟨⊤⟩ (by rw [withTopNatSegments_top]; exact le_rfl))

/-- The top stage is a genuine limit: it is the union of the stages strictly below it, and it is
not equal to any of them. -/
theorem withTopNatSegments_top_eq_iSup :
    withTopNatSegments ⟨⊤⟩ =
      ⨆ (β : ULift.{1, 0} (WithTop ℕ)) (_ : β < ⟨⊤⟩), withTopNatSegments β := by
  refine le_antisymm (fun k _ => ?_) (iSup₂_le fun β _ => le_top)
  exact Set.mem_iUnion.mpr ⟨⟨(k + 1 : ℕ)⟩, Set.mem_iUnion.mpr
    ⟨WithTop.coe_lt_top _, by rw [withTopNatSegments_coe]; exact Nat.lt_succ_self k⟩⟩

/-- An initial segment `Set.Iio n` of `ℕ` is not any set containing `n`. -/
private theorem Iio_ne_of_mem {n : ℕ} {s : Set ℕ} (h : n ∈ s) : Set.Iio n ≠ s :=
  fun he => lt_irrefl n (show n ∈ Set.Iio n from he ▸ h)

/-- NON-DEGENERACY, part 1: the chain is strictly increasing, so the range is infinite and the
index order has no greatest element below the top -- the degeneracy criterion
`Stacks.DerivedGlueing.eq_top_of_isGreatest` does not apply to the proper part of the chain. -/
theorem withTopNatSegments_ne (n m : ℕ) (h : n < m) :
    withTopNatSegments ⟨(n : WithTop ℕ)⟩ ≠ withTopNatSegments ⟨(m : WithTop ℕ)⟩ := by
  exact Iio_ne_of_mem h

/-- NON-DEGENERACY, part 2: the top stage is a PROPER limit -- it is strictly above every
proper stage, so the range of the chain genuinely has a value with no immediate predecessor
and that value is not `⊥`.  This is what makes
`Stacks.DerivedGlueing.leastIndex_eq_iSup_of_not_isPred` say something at this witness. -/
theorem withTopNatSegments_ne_top (n : ℕ) :
    withTopNatSegments ⟨(n : WithTop ℕ)⟩ ≠ withTopNatSegments ⟨⊤⟩ := by
  exact Iio_ne_of_mem (Set.mem_univ n)

/-- `<` on the `ULift` of the index order is `<` of the underlying elements. -/
theorem withTopNat_up_lt {a b : WithTop ℕ} (h : a < b) :
    (⟨a⟩ : ULift.{1, 0} (WithTop ℕ)) < ⟨b⟩ := h

/-- The continuity hypothesis `hlimit` for the witness.  Its two non-successor stages are the
bottom one, where both sides are `⊥`, and the top one, where it is
`withTopNatSegments_top_eq_iSup`. -/
theorem withTopNatSegments_limit : ∀ α : ULift.{1, 0} (WithTop ℕ),
    (¬ ∃ β : ULift.{1, 0} (WithTop ℕ), β < α ∧
        ∀ γ : ULift.{1, 0} (WithTop ℕ), γ < α → γ ≤ β) →
      withTopNatSegments α =
        ⨆ (β : ULift.{1, 0} (WithTop ℕ)) (_ : β < α), withTopNatSegments β := by
  rintro ⟨α⟩ hα
  induction α using WithTop.recTopCoe with
  | top => exact withTopNatSegments_top_eq_iSup
  | coe n =>
    match n with
    | 0 =>
      have hempty : ∀ β : ULift.{1, 0} (WithTop ℕ),
          ¬ (β < (⟨((0 : ℕ) : WithTop ℕ)⟩ : ULift.{1, 0} (WithTop ℕ))) := by
        rintro ⟨β⟩ hβ
        have hb : β < ((0 : ℕ) : WithTop ℕ) := hβ
        induction β using WithTop.recTopCoe with
        | top => exact absurd hb (by simp)
        | coe k => exact absurd (WithTop.coe_lt_coe.mp hb) (Nat.not_lt_zero k)
      refine le_antisymm ?_ (iSup₂_le fun β hβ => absurd hβ (hempty β))
      exact fun k hk => absurd (hk : k < 0) (Nat.not_lt_zero k)
    | (m + 1) =>
      refine absurd ⟨(⟨(m : WithTop ℕ)⟩ : ULift.{1, 0} (WithTop ℕ)),
        withTopNat_up_lt (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self m)), ?_⟩ hα
      rintro ⟨γ⟩ hγ
      have hg : γ < (((m + 1 : ℕ)) : WithTop ℕ) := hγ
      induction γ using WithTop.recTopCoe with
      | top => exact absurd hg (by simp)
      | coe k =>
        have hk : k < m + 1 := WithTop.coe_lt_coe.mp hg
        exact WithTop.coe_le_coe.mpr (by omega : k ≤ m)

/-- SATISFIABILITY, machine-checked: every binder of
`Stacks.DerivedGlueing.leastIndex_eq_iSup_of_not_isPred` instantiated at the witness, at the
value of the range that is a GENUINE LIMIT -- `Set.univ`, which is not `⊥` and is not any
proper stage.  So the lemma is neither vacuous nor degenerate at this instance. -/
theorem leastIndex_eq_iSup_withTopNatSegments :
    withTopNatSegments (leastIndex withTopNatSegments ⟨Set.univ, ⟨⟨⊤⟩, rfl⟩⟩) =
      ⨆ (U : ↥(Set.range withTopNatSegments))
        (_ : U.1 < (⟨Set.univ, ⟨⟨⊤⟩, rfl⟩⟩ : ↥(Set.range withTopNatSegments)).1),
        withTopNatSegments (leastIndex withTopNatSegments U) := by
  refine leastIndex_eq_iSup_of_not_isPred withTopNatSegments_mono withTopNatSegments_limit ?_
  rintro ⟨⟨U, ⟨x⟩, rfl⟩, hU, hmax⟩
  induction x using WithTop.recTopCoe with
  | top => exact absurd hU (lt_irrefl _)
  | coe n =>
    have hnext : withTopNatSegments ⟨((n + 1 : ℕ) : WithTop ℕ)⟩ <
        (⟨Set.univ, ⟨⟨⊤⟩, rfl⟩⟩ : ↥(Set.range withTopNatSegments)).1 := by
      show Set.Iio (n + 1) < Set.univ
      exact lt_of_le_of_ne le_top (Iio_ne_of_mem (Set.mem_univ _))
    have hle := hmax
      ⟨withTopNatSegments ⟨((n + 1 : ℕ) : WithTop ℕ)⟩, ⟨⟨((n + 1 : ℕ) : WithTop ℕ)⟩, rfl⟩⟩ hnext
    have hmem : n ∈ Set.Iio n := hle (show n < n + 1 by omega)
    exact absurd (hmem : n < n) (Nat.lt_irrefl _)

end Stacks.DerivedGlueing

end
