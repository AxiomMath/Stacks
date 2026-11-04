module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.WellOrderedCoverRangeReindex
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HomVanishingOverASubcollection

/-!
# The datum of Tag 0D6B as a system of locally given derived objects

The datum of [Stacks, Tag 0D6B] — a well ordered increasing cover `W : E → Opens X`, an object
`K α` of `D(𝒪_{W_α})` for each stage and transition isomorphisms `ρ^α_β : K_α|_{W_β} ≅ K_β` for
`β < α` satisfying the cocycle condition — is indexed by the stages, and `α ↦ W α` need not be
injective.  Every statement this development carries about such a datum is instead phrased
through `Stacks.DerivedGlueing.LocallyGiven`, whose prescribed objects are indexed by the
*opens* they live on.  This file reindexes the one into the other.

## The shape of the reindexing, and why the prescribed objects are restrictions

The displayed opens of the reindexed system are the members of the range of `W`, and the index
attached to such a member is the least stage attaining it,
`Stacks.DerivedGlueing.leastIndex`.  The object prescribed on a member `V` cannot be taken to be
`K (leastIndex W V)` on the nose: that object lives over `W (leastIndex W V)`, an open *equal* to
`V` but not the same term.  Rather than transport along that equality it is taken to be the
displayed restriction of `K (leastIndex W V)` from `W (leastIndex W V)` to `V`, which is a
functor applied to an object and so needs no transport at all.

That choice is what makes the transition isomorphisms of the reindexed system uniform.  A
`Stacks.DerivedGlueing.LocallyGiven` prescribes a transition for *every* inclusion `V ≤ U` of
members, the degenerate inclusion `V ≤ V` included, while the datum of the tag supplies `ρ^α_β`
only for `β < α`.  With the prescribed objects taken as restrictions, the degenerate transition
is a comparison of restriction in two steps — `restrictionComp` along `V ≤ V ≤ W (leastIndex W V)`
— and no identification of restriction from an open to itself with the identity is needed.

## Main definitions

* `Stacks.DerivedGlueing.coverIndex`: the stage attached to a member of the range of the cover,
  namely the least one attaining it.
* `Stacks.DerivedGlueing.coverTransferIso`: for `β ≤ α` and an open `V ≤ W β`, the identification
  of the restriction of `K α` to `V` with the restriction of `K β` to `V`.  At `β = α` it is the
  identity and at `β < α` it is the prescribed `ρ^α_β` restricted to `V`.
* `Stacks.DerivedGlueing.coverSystemObj`, `Stacks.DerivedGlueing.coverSystemRho`: the objects and
  transitions of the reindexed system.
* `Stacks.DerivedGlueing.LocallyGiven.ofWellOrderedCover`: the datum of [Stacks, Tag 0D6B] as a
  system of locally given derived objects, displayed on the range of the cover.
* `Stacks.DerivedGlueing.belowStageSystem`: the same datum displayed only on the stages
  strictly below a fixed stage, which is the system the limit stage of the source's recursion
  forms a solution of.
* `Stacks.DerivedGlueing.selfSolutionOverStage`,
  `Stacks.DerivedGlueing.selfSolutionOverBelowStage`: the prescribed object at a stage, as a
  solution over that stage for each of those two systems.  These inhabit the types of solutions
  the uniqueness statements below quantify over, and the second is the solution `(K_α, ρ^α_β)`
  the source compares the colimit of the earlier stages with.

## Main results

* `Stacks.DerivedGlueing.leastIndex_monotone`, `Stacks.DerivedGlueing.coverIndex_monotone`: the
  stage attached to a member is monotone in the member.
* `Stacks.DerivedGlueing.coverTransferIso_trans`: the identifications compose, which is the
  cocycle condition of the datum read at an open below the smallest of three stages.
* `Stacks.DerivedGlueing.coverTransferIso_restrict`: the identifications are compatible with
  restriction to a smaller open, which is their naturality in the open they are read over.
* `Stacks.DerivedGlueing.coverSystemRho_cocycle`: the cocycle condition of the reindexed system.
* `Stacks.DerivedGlueing.subsingleton_shiftedHom_restriction_of_antisymm`: a displayed
  restriction across an equality of opens preserves the vanishing of negative self-Ext.
* `Stacks.DerivedGlueing.subsingleton_shiftedHom_coverSystemObj`: hence so do the objects the
  reindexed system prescribes.
* `Stacks.DerivedGlueing.hasUniqueSolutionOverIso_ofWellOrderedCover`: **the uniqueness clause of
  [Stacks, Tag 0D68] for the reindexed system, with nothing granted** — the stages are a chain, so
  the hypothesis on intersections of Situation 0D67 is automatic by
  `Stacks.DerivedGlueing.inf_eq_sSup_of_totallyOrdered` and
  `Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_covers` applies.  Not even a hypothesis that
  the stages cover `X` is needed, so this holds for the stages below a fixed stage as well.
* `Stacks.DerivedGlueing.exists_unique_solutionOver_iso_of_wellOrderedCover`: **two solutions over
  a stage `W α` are identified by a unique isomorphism of solutions, with nothing granted.**
* `Stacks.DerivedGlueing.exists_unique_solutionOver_iso_below_of_wellOrderedCover`: **the
  uniqueness input of the limit stages of [Stacks, Tag 0D6B], with nothing granted** — the same
  for two solutions of the datum displayed on the stages *strictly below* a limit stage, which is
  the form the source's recursion consumes, where the collection covers only `W α`.  The source
  names that step as the one where the vanishing of the negative Ext groups is used, and cites
  [Stacks, Tag 0D6A] for it.

## Use in Tag 0D6B

The stages of the transfinite recursion of [Stacks, Tag 0D6B] compare two solutions of the datum
displayed on the stages strictly below a stage; that comparison is
`Stacks.DerivedGlueing.exists_iso_of_isCompatibleBelow` in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.WellOrderedCoverRecursion`, through
`Stacks.DerivedGlueing.belowStageSystem`.

One distinction is worth stating precisely, because it is easy to lose.  A solution of the system
displayed on *all* the stages carries an identification over `W α` itself, whereas the limit stage
of the source's recursion compares two solutions of the system displayed on the stages *strictly
below* `α`, the identification over `W α` being the very thing it constructs.  Both forms are
proved here, and the second only because the uniqueness clause carried by
`Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_covers` asks nothing about the collection
covering `X`, only about intersections: the stages below `α` cover `W α` and nothing more.

Nothing here is tagged: a reindexing of a datum is a step of a proof, not a clause of the
statement of any tag.

## References

* [Stacks Project, Tag 0D6B](https://stacks.math.columbia.edu/tag/0D6B)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D6A](https://stacks.math.columbia.edu/tag/0D6A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.DerivedGlueing

universe u v

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-! ### The least index is monotone -/

/-- **The least index of a value of an increasing family is monotone in that value.** For two
values of the range the least index is strictly monotone by
`Stacks.DerivedGlueing.leastIndex_strictMono`, and equal values have equal least indices. -/
theorem leastIndex_monotone {L : Type u} [CompleteLattice L] {E : Type v} [LinearOrder E]
    [WellFoundedLT E] {W : E → L} (hmono : ∀ β α : E, β < α → W β ≤ W α)
    {V U : ↥(Set.range W)} (h : V.1 ≤ U.1) : leastIndex W V ≤ leastIndex W U := by
  rcases eq_or_lt_of_le h with he | hl
  · exact le_of_eq (congrArg (leastIndex W) (Subtype.ext he))
  · exact (leastIndex_strictMono hmono hl).le

/-! ### The stage attached to a member of the range -/

/-- **The stage attached to a member of the range of a family**: the least index attaining it. -/
def coverIndex {L : Type u} [CompleteLattice L] {E : Type v} [LinearOrder E] [WellFoundedLT E]
    (W : E → L) (V : L) (hV : V ∈ Set.range W) : E :=
  leastIndex W ⟨V, hV⟩

/-- The member is contained in the value of the family at the stage attached to it — they are in
fact equal. -/
theorem le_coverIndex_apply {L : Type u} [CompleteLattice L] {E : Type v} [LinearOrder E]
    [WellFoundedLT E] (W : E → L) (V : L) (hV : V ∈ Set.range W) : V ≤ W (coverIndex W V hV) :=
  (apply_leastIndex W ⟨V, hV⟩).ge

/-- The value of the family at the stage attached to a member is contained in it — they are in
fact equal. -/
theorem coverIndex_apply_le {L : Type u} [CompleteLattice L] {E : Type v} [LinearOrder E]
    [WellFoundedLT E] (W : E → L) (V : L) (hV : V ∈ Set.range W) : W (coverIndex W V hV) ≤ V :=
  (apply_leastIndex W ⟨V, hV⟩).le

/-- **The stage attached to a member is monotone in the member.** -/
theorem coverIndex_monotone {L : Type u} [CompleteLattice L] {E : Type v} [LinearOrder E]
    [WellFoundedLT E] (W : E → L) (hmono : ∀ β α : E, β < α → W β ≤ W α) {V U : L}
    (hV : V ∈ Set.range W) (hU : U ∈ Set.range W) (hVU : V ≤ U) :
    coverIndex W V hV ≤ coverIndex W U hU :=
  leastIndex_monotone hmono (V := ⟨V, hV⟩) (U := ⟨U, hU⟩) hVU

/-! ### Negative self-Ext across an equality of opens -/

/-- **A displayed restriction across an equality of opens preserves the vanishing of negative
self-Ext.** If `U ≤ V` and `V ≤ U`, so that the two opens are equal, then the displayed
restriction from `V` to `U` is the identity functor by
`Stacks.DerivedGlueing.restrictionSelfIso`, and the vanishing of the negative self-Ext of an
object is inherited by its restriction.

This is the companion of `Stacks.DerivedGlueing.isoOfRestrictionObjIso` for the hypothesis
`hExt` of [Stacks, Tag 0D68]: the objects prescribed by
`Stacks.DerivedGlueing.LocallyGiven.ofWellOrderedCover` are restrictions of the objects of the
datum across such an equality, so this is what carries that hypothesis across the
reindexing. -/
theorem subsingleton_shiftedHom_restriction_of_antisymm (S : LocallyGiven X)
    {U V : Opens X.carrier} (hUV : U ≤ V) (hVU : V ≤ U) (P : OpenDerivedCategory X V) (i : ℤ)
    (h : Subsingleton (ShiftedHom P P i)) :
    Subsingleton
      (ShiftedHom ((S.restriction U V hUV).obj P) ((S.restriction U V hUV).obj P) i) := by
  obtain rfl : U = V := le_antisymm hUV hVU
  exact subsingleton_shiftedHom_of_iso ((restrictionSelfIso S U hUV).app P)
    ((restrictionSelfIso S U hUV).app P) i h

/-! ### The identifications attached to the datum -/

section Transfer

variable (S : LocallyGiven X) {E : Type v} [LinearOrder E] [WellFoundedLT E]
  (W : E → Opens X.carrier) (hmono : ∀ β α : E, β < α → W β ≤ W α)
  (K : ∀ α : E, OpenDerivedCategory X (W α))
  (rho : ∀ (β α : E) (h : β < α),
    (S.restriction (W β) (W α) (hmono β α h)).obj (K α) ≅ K β)

/-- **The identification of the restrictions of two prescribed objects to an open below the
smaller stage.** For `β ≤ α` and an open `V` contained in `W β`, the displayed restriction of
`K α` to `V` is the displayed restriction of `K β` to `V`: at `β = α` the two are the same object
and at `β < α` the identification is the prescribed `ρ^α_β` restricted to `V`, read through the
comparison of restriction in two steps. -/
def coverTransferIso (V : Opens X.carrier) {β α : E} (hβα : β ≤ α) (hV : V ≤ W β) :
    (S.restriction V (W α) (hV.trans (apply_le_apply_of_le hmono hβα))).obj (K α) ≅
      (S.restriction V (W β) hV).obj (K β) :=
  if h : β = α then eqToIso (by cases h; rfl)
  else
    (S.restrictionComp V (W β) (W α) hV (hmono β α (lt_of_le_of_ne hβα h))).app (K α) ≪≫
      (S.restriction V (W β) hV).mapIso (rho β α (lt_of_le_of_ne hβα h))

omit [WellFoundedLT E] in
/-- At a single stage the identification is the identity. -/
theorem coverTransferIso_self (V : Opens X.carrier) {β : E} (hβ : β ≤ β) (hV : V ≤ W β) :
    (coverTransferIso S W hmono K rho V hβ hV).hom = 𝟙 _ := by
  rw [coverTransferIso, dite_eq_left rfl]
  exact eqToHom_refl ((S.restriction V (W β) hV).obj (K β)) rfl

omit [WellFoundedLT E] in
/-- At a strict pair of stages the identification is the prescribed transition restricted. -/
theorem coverTransferIso_hom_of_lt (V : Opens X.carrier) {β α : E} (hβα : β ≤ α) (hV : V ≤ W β)
    (h : β < α) :
    (coverTransferIso S W hmono K rho V hβα hV).hom =
      (S.restrictionComp V (W β) (W α) hV (hmono β α h)).hom.app (K α) ≫
        (S.restriction V (W β) hV).map (rho β α h).hom := by
  rw [coverTransferIso, dite_eq_right (ne_of_lt h)]
  rfl

omit [WellFoundedLT E] in
/-- **The identifications compose.** For `γ ≤ β ≤ α` and an open `V` contained in `W γ`, the
identification of the restriction of `K α` to `V` with the restriction of `K γ` to `V` factors
through the restriction of `K β` to `V`.

This is the cocycle condition of the datum of [Stacks, Tag 0D6B] read at an open below the
smallest of three stages, and it is what the cocycle condition of
`Stacks.DerivedGlueing.LocallyGiven.ofWellOrderedCover` reduces to.  The degenerate cases are
`Stacks.DerivedGlueing.coverTransferIso_self`; in the strict case the prescribed cocycle
condition is substituted and the two comparisons of restriction are reassociated by the
coherence `Stacks.DerivedGlueing.LocallyGiven.restrictionComp_pentagon`, after the naturality of
the comparison has moved the prescribed transition past it. -/
theorem coverTransferIso_trans
    (hcocycle : ∀ (γ β α : E) (hγβ : γ < β) (hβα : β < α),
      (rho γ α (hγβ.trans hβα)).hom =
        (S.restrictionComp (W γ) (W β) (W α) (hmono γ β hγβ)
            (hmono β α hβα)).hom.app (K α) ≫
          (S.restriction (W γ) (W β) (hmono γ β hγβ)).map (rho β α hβα).hom ≫
            (rho γ β hγβ).hom)
    (V : Opens X.carrier) {γ β α : E} (hγβ : γ ≤ β) (hβα : β ≤ α) (hV : V ≤ W γ) :
    (coverTransferIso S W hmono K rho V (hγβ.trans hβα) hV).hom =
      (coverTransferIso S W hmono K rho V hβα
          (hV.trans (apply_le_apply_of_le hmono hγβ))).hom ≫
        (coverTransferIso S W hmono K rho V hγβ hV).hom := by
  rcases eq_or_lt_of_le hγβ with rfl | hγβ'
  · rw [coverTransferIso_self, Category.comp_id]
  rcases eq_or_lt_of_le hβα with rfl | hβα'
  · rw [coverTransferIso_self, Category.id_comp]
  rw [coverTransferIso_hom_of_lt S W hmono K rho V _ _ (hγβ'.trans hβα'),
    coverTransferIso_hom_of_lt S W hmono K rho V _ _ hβα',
    coverTransferIso_hom_of_lt S W hmono K rho V _ _ hγβ',
    hcocycle γ β α hγβ' hβα']
  simp only [Functor.map_comp, Category.assoc]
  rw [(S.restrictionComp V (W γ) (W β) hV (hmono γ β hγβ')).hom.naturality_assoc
    (rho β α hβα').hom]
  simp only [Functor.comp_map]
  rw [← reassoc_of% S.restrictionComp_pentagon V (W γ) (W β) (W α) hV (hmono γ β hγβ')
    (hmono β α hβα') (K α)]

omit [WellFoundedLT E] in
/-- **The identifications are compatible with restriction to a smaller open.** For `β ≤ α` and
opens `T ≤ V ≤ W β`, the identification at `T` is the identification at `V` restricted from `V`
to `T`, read through the comparisons of restriction in two steps.

This is the naturality of `Stacks.DerivedGlueing.coverTransferIso` in the open it is read over,
and it is what the cocycle condition of
`Stacks.DerivedGlueing.LocallyGiven.ofWellOrderedCover` needs beyond
`Stacks.DerivedGlueing.coverTransferIso_trans`. -/
theorem coverTransferIso_restrict (T V : Opens X.carrier) {β α : E} (hβα : β ≤ α)
    (hTV : T ≤ V) (hV : V ≤ W β) :
    (coverTransferIso S W hmono K rho T hβα (hTV.trans hV)).hom =
      (S.restrictionComp T V (W α) hTV
          (hV.trans (apply_le_apply_of_le hmono hβα))).hom.app (K α) ≫
        (S.restriction T V hTV).map (coverTransferIso S W hmono K rho V hβα hV).hom ≫
          (S.restrictionComp T V (W β) hTV hV).inv.app (K β) := by
  rcases eq_or_lt_of_le hβα with rfl | h
  · rw [coverTransferIso_self, coverTransferIso_self]
    simp
  rw [coverTransferIso_hom_of_lt S W hmono K rho T _ _ h,
    coverTransferIso_hom_of_lt S W hmono K rho V _ _ h]
  simp only [Functor.map_comp, Category.assoc]
  have hnat := (S.restrictionComp T V (W β) hTV hV).hom.naturality (rho β α h).hom
  simp only [Functor.comp_map] at hnat
  rw [← reassoc_of% S.restrictionComp_pentagon T V (W β) (W α) hTV hV (hmono β α h) (K α),
    ← reassoc_of% hnat]
  simp

/-! ### The system carried by the datum -/

/-- **The object the reindexed system prescribes on a member of the range**: the displayed
restriction to that member of the object prescribed at the stage attached to it.  The two opens
are equal, so no content is lost; taking the restriction rather than transporting along that
equality is what keeps the transition isomorphisms of the reindexed system uniform. -/
def coverSystemObj (V : Opens X.carrier) (hV : V ∈ Set.range W) : OpenDerivedCategory X V :=
  (S.restriction V (W (coverIndex W V hV)) (le_coverIndex_apply W V hV)).obj
    (K (coverIndex W V hV))

/-- **The transition isomorphism the reindexed system prescribes for an inclusion of members.**
Compare restriction in two steps and then apply
`Stacks.DerivedGlueing.coverTransferIso` at the two stages attached to the two members. -/
def coverSystemRho (V U : Opens X.carrier) (hVU : V ≤ U) (hU : U ∈ Set.range W)
    (hV : V ∈ Set.range W) :
    (S.restriction V U hVU).obj (coverSystemObj S W K U hU) ≅ coverSystemObj S W K V hV :=
  ((S.restrictionComp V U (W (coverIndex W U hU)) hVU
        (le_coverIndex_apply W U hU)).app (K (coverIndex W U hU))).symm ≪≫
    coverTransferIso S W hmono K rho V (coverIndex_monotone W hmono hV hU hVU)
      (le_coverIndex_apply W V hV)

/-- **The transition isomorphisms of the reindexed system satisfy the cocycle condition.**
The identifications compose by `Stacks.DerivedGlueing.coverTransferIso_trans`, the one read over
the middle member is the one read over the smallest restricted by
`Stacks.DerivedGlueing.coverTransferIso_restrict`, and the three comparisons of restriction in
two steps are reassociated by the coherence
`Stacks.DerivedGlueing.LocallyGiven.restrictionComp_pentagon` along the chain
`T ⊆ V ⊆ U ⊆ W_α` with `α` the stage attached to `U`. -/
theorem coverSystemRho_cocycle
    (hcocycle : ∀ (γ β α : E) (hγβ : γ < β) (hβα : β < α),
      (rho γ α (hγβ.trans hβα)).hom =
        (S.restrictionComp (W γ) (W β) (W α) (hmono γ β hγβ)
            (hmono β α hβα)).hom.app (K α) ≫
          (S.restriction (W γ) (W β) (hmono γ β hγβ)).map (rho β α hβα).hom ≫
            (rho γ β hγβ).hom)
    (T V U : Opens X.carrier) (hTV : T ≤ V) (hVU : V ≤ U) (hU : U ∈ Set.range W)
    (hV : V ∈ Set.range W) (hT : T ∈ Set.range W) :
    (coverSystemRho S W hmono K rho T U (hTV.trans hVU) hU hT).hom =
      (S.restrictionComp T V U hTV hVU).hom.app (coverSystemObj S W K U hU) ≫
        (S.restriction T V hTV).map (coverSystemRho S W hmono K rho V U hVU hU hV).hom ≫
          (coverSystemRho S W hmono K rho T V hTV hV hT).hom := by
  have hp := S.restrictionComp_pentagon T V U (W (coverIndex W U hU)) hTV hVU
    (le_coverIndex_apply W U hU) (K (coverIndex W U hU))
  have key : (S.restrictionComp T U (W (coverIndex W U hU)) (hTV.trans hVU)
          (le_coverIndex_apply W U hU)).inv.app (K (coverIndex W U hU)) ≫
        (S.restrictionComp T V (W (coverIndex W U hU)) hTV
          (hVU.trans (le_coverIndex_apply W U hU))).hom.app (K (coverIndex W U hU)) =
      (S.restrictionComp T V U hTV hVU).hom.app
          ((S.restriction U (W (coverIndex W U hU))
            (le_coverIndex_apply W U hU)).obj (K (coverIndex W U hU))) ≫
        (S.restriction T V hTV).map
          ((S.restrictionComp V U (W (coverIndex W U hU)) hVU
            (le_coverIndex_apply W U hU)).inv.app (K (coverIndex W U hU))) := by
    rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, reassoc_of% hp, ← Functor.map_comp]
    simp
  simp only [coverSystemRho, coverSystemObj, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc]
  rw [coverTransferIso_trans S W hmono K rho hcocycle T
      (coverIndex_monotone W hmono hT hV hTV) (coverIndex_monotone W hmono hV hU hVU)
      (le_coverIndex_apply W T hT),
    coverTransferIso_restrict S W hmono K rho T V
      (coverIndex_monotone W hmono hV hU hVU) hTV (le_coverIndex_apply W V hV)]
  simp only [Category.assoc]
  rw [reassoc_of% key]

end Transfer

/-! ### The datum of Tag 0D6B as a system of locally given derived objects -/

/-- **The datum of [Stacks, Tag 0D6B] as a system of locally given derived objects.** The
displayed opens are the members of the range of the cover, the restriction functors and their
comparisons are those of the ambient system `S`, the object prescribed on a member is
`Stacks.DerivedGlueing.coverSystemObj` and the transitions are
`Stacks.DerivedGlueing.coverSystemRho`.

This is the reindexing the statements of Situation 0D67 need in order to be read against the
datum of the tag, whose objects are indexed by the stages rather than by the opens they live
on. -/
def LocallyGiven.ofWellOrderedCover (S : LocallyGiven X) {E : Type v} [LinearOrder E]
    [WellFoundedLT E] (W : E → Opens X.carrier) (hmono : ∀ β α : E, β < α → W β ≤ W α)
    (K : ∀ α : E, OpenDerivedCategory X (W α))
    (rho : ∀ (β α : E) (h : β < α),
      (S.restriction (W β) (W α) (hmono β α h)).obj (K α) ≅ K β)
    (hcocycle : ∀ (γ β α : E) (hγβ : γ < β) (hβα : β < α),
      (rho γ α (hγβ.trans hβα)).hom =
        (S.restrictionComp (W γ) (W β) (W α) (hmono γ β hγβ)
            (hmono β α hβα)).hom.app (K α) ≫
          (S.restriction (W γ) (W β) (hmono γ β hγβ)).map (rho β α hβα).hom ≫
            (rho γ β hγβ).hom) :
    LocallyGiven X :=
  { S with
    opens := Set.range W
    obj := fun V hV => coverSystemObj S W K V hV
    rho := fun V U hVU hU hV => coverSystemRho S W hmono K rho V U hVU hU hV
    cocycle := fun T V U hTV hVU hU hV hT =>
      coverSystemRho_cocycle S W hmono K rho hcocycle T V U hTV hVU hU hV hT }

/-- The displayed opens of `LocallyGiven.ofWellOrderedCover` are the members of the range of
the cover. -/
@[simp]
theorem LocallyGiven.ofWellOrderedCover_opens (S : LocallyGiven X) {E : Type v} [LinearOrder E]
    [WellFoundedLT E] (W : E → Opens X.carrier) (hmono : ∀ β α : E, β < α → W β ≤ W α)
    (K : ∀ α : E, OpenDerivedCategory X (W α))
    (rho : ∀ (β α : E) (h : β < α),
      (S.restriction (W β) (W α) (hmono β α h)).obj (K α) ≅ K β)
    (hcocycle : ∀ (γ β α : E) (hγβ : γ < β) (hβα : β < α),
      (rho γ α (hγβ.trans hβα)).hom =
        (S.restrictionComp (W γ) (W β) (W α) (hmono γ β hγβ)
            (hmono β α hβα)).hom.app (K α) ≫
          (S.restriction (W γ) (W β) (hmono γ β hγβ)).map (rho β α hβα).hom ≫
            (rho γ β hγβ).hom) :
    (S.ofWellOrderedCover W hmono K rho hcocycle).opens = Set.range W := rfl

/-- The restriction functors of `LocallyGiven.ofWellOrderedCover` are those of the ambient
system. -/
@[simp]
theorem LocallyGiven.ofWellOrderedCover_restriction (S : LocallyGiven X) {E : Type v}
    [LinearOrder E] [WellFoundedLT E] (W : E → Opens X.carrier)
    (hmono : ∀ β α : E, β < α → W β ≤ W α) (K : ∀ α : E, OpenDerivedCategory X (W α))
    (rho : ∀ (β α : E) (h : β < α),
      (S.restriction (W β) (W α) (hmono β α h)).obj (K α) ≅ K β)
    (hcocycle : ∀ (γ β α : E) (hγβ : γ < β) (hβα : β < α),
      (rho γ α (hγβ.trans hβα)).hom =
        (S.restrictionComp (W γ) (W β) (W α) (hmono γ β hγβ)
            (hmono β α hβα)).hom.app (K α) ≫
          (S.restriction (W γ) (W β) (hmono γ β hγβ)).map (rho β α hβα).hom ≫
            (rho γ β hγβ).hom)
    (V U : Opens X.carrier) (hVU : V ≤ U) :
    (S.ofWellOrderedCover W hmono K rho hcocycle).restriction V U hVU =
      S.restriction V U hVU := rfl

/-- The object of `LocallyGiven.ofWellOrderedCover` on a member of the range of the cover is
`Stacks.DerivedGlueing.coverSystemObj`. -/
@[simp]
theorem LocallyGiven.ofWellOrderedCover_obj (S : LocallyGiven X) {E : Type v} [LinearOrder E]
    [WellFoundedLT E] (W : E → Opens X.carrier) (hmono : ∀ β α : E, β < α → W β ≤ W α)
    (K : ∀ α : E, OpenDerivedCategory X (W α))
    (rho : ∀ (β α : E) (h : β < α),
      (S.restriction (W β) (W α) (hmono β α h)).obj (K α) ≅ K β)
    (hcocycle : ∀ (γ β α : E) (hγβ : γ < β) (hβα : β < α),
      (rho γ α (hγβ.trans hβα)).hom =
        (S.restrictionComp (W γ) (W β) (W α) (hmono γ β hγβ)
            (hmono β α hβα)).hom.app (K α) ≫
          (S.restriction (W γ) (W β) (hmono γ β hγβ)).map (rho β α hβα).hom ≫
            (rho γ β hγβ).hom)
    (V : Opens X.carrier) (hV : V ∈ Set.range W) :
    (S.ofWellOrderedCover W hmono K rho hcocycle).obj V hV = coverSystemObj S W K V hV := rfl

/-! ### The uniqueness input of the limit stages of Tag 0D6B -/

section Uniqueness

variable (S : LocallyGiven X) {E : Type v} [LinearOrder E] [WellFoundedLT E]
  (W : E → Opens X.carrier) (hmono : ∀ β α : E, β < α → W β ≤ W α)
  (K : ∀ α : E, OpenDerivedCategory X (W α))
  (rho : ∀ (β α : E) (h : β < α),
    (S.restriction (W β) (W α) (hmono β α h)).obj (K α) ≅ K β)
  (hcocycle : ∀ (γ β α : E) (hγβ : γ < β) (hβα : β < α),
    (rho γ α (hγβ.trans hβα)).hom =
      (S.restrictionComp (W γ) (W β) (W α) (hmono γ β hγβ)
          (hmono β α hβα)).hom.app (K α) ≫
        (S.restriction (W γ) (W β) (hmono γ β hγβ)).map (rho β α hβα).hom ≫
          (rho γ β hγβ).hom)

omit [WellFoundedLT E] in
include hmono in
/-- **The intersection of two stages is the union of the stages contained in it.** The stages of
an increasing cover are totally ordered by inclusion, so this is
`Stacks.DerivedGlueing.inf_eq_sSup_of_totallyOrdered`: the intersection of two of them is the
smaller. -/
theorem inf_eq_sSup_range_of_wellOrderedCover (U : Opens X.carrier) (hU : U ∈ Set.range W)
    (V : Opens X.carrier) (hV : V ∈ Set.range W) :
    U ⊓ V = sSup {T | T ∈ Set.range W ∧ T ≤ U ⊓ V} :=
  inf_eq_sSup_of_totallyOrdered (Set.range W)
    (totallyOrdered_range_of_wellOrderedCover W hmono) U V hU hV

omit [LinearOrder E] [WellFoundedLT E] in
/-- **Each stage is the union of the stages it contains**, being one of them. -/
theorem eq_sSup_range_le_of_wellOrderedCover (α : E) :
    W α = sSup {T | T ∈ Set.range W ∧ T ≤ W α} :=
  le_antisymm (le_sSup ⟨⟨α, rfl⟩, le_rfl⟩) (sSup_le fun _ hT => hT.2)

/-- **The prescribed objects of the reindexed system have no negative self-Ext** as soon as those
of the datum do.  The object prescribed on a member is the restriction of an object of the datum
across an equality of opens, so this is
`Stacks.DerivedGlueing.subsingleton_shiftedHom_restriction_of_antisymm`. -/
theorem subsingleton_shiftedHom_coverSystemObj
    (hExt : ∀ (α : E) (i : ℤ), i < 0 → Subsingleton (ShiftedHom (K α) (K α) i))
    (V : Opens X.carrier) (hV : V ∈ Set.range W) (i : ℤ) (hi : i < 0) :
    Subsingleton (ShiftedHom (coverSystemObj S W K V hV) (coverSystemObj S W K V hV) i) :=
  subsingleton_shiftedHom_restriction_of_antisymm S (le_coverIndex_apply W V hV)
    (coverIndex_apply_le W V hV) (K (coverIndex W V hV)) i (hExt _ i hi)

/-- **The uniqueness clause of [Stacks, Tag 0D68] for the datum of [Stacks, Tag 0D6B], with
nothing granted.** The stages of a well ordered increasing cover of `X` form a chain covering
`X`, so the hypothesis on intersections of Situation 0D67 is automatic and
`Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_covers` applies to the reindexed system. -/
theorem hasUniqueSolutionOverIso_ofWellOrderedCover :
    HasUniqueSolutionOverIso (S.ofWellOrderedCover W hmono K rho hcocycle) :=
  hasUniqueSolutionOverIso_of_covers _ (inf_eq_sSup_range_of_wellOrderedCover W hmono)

/-- **Two solutions over a stage are identified by a unique isomorphism of solutions, with
nothing granted.** Let `W` be a well ordered increasing cover of `X`, let `K α` be an object of
`D(𝒪_{W_α})` without negative self-Ext at each stage and let `ρ^α_β` be transition isomorphisms
satisfying the cocycle condition.  Then two solutions over a stage `W α` of the system this
datum carries are identified by a *unique* isomorphism of solutions.

The solutions here are solutions of the datum displayed on *all* the stages, so an identification
over `W α` itself is part of what each of them carries.  The limit stage of the source's
recursion compares two solutions of the datum displayed on the stages *strictly below* `α`,
because there the identification over `W α` is the thing being constructed; that form is
`Stacks.DerivedGlueing.exists_unique_solutionOver_iso_below_of_wellOrderedCover`. -/
theorem exists_unique_solutionOver_iso_of_wellOrderedCover
    (hExt : ∀ (α : E) (i : ℤ), i < 0 → Subsingleton (ShiftedHom (K α) (K α) i)) (α : E)
    (A B : SolutionOver (S.ofWellOrderedCover W hmono K rho hcocycle) (W α)) :
    ∃! φ : A.obj ≅ B.obj, A.IsCompatibleHom B φ.hom :=
  hasUniqueSolutionOverIso_ofWellOrderedCover S W hmono K rho hcocycle (W α)
    (eq_sSup_range_le_of_wellOrderedCover W α) (inf_eq_sSup_range_of_wellOrderedCover W hmono)
    (fun V hV i hi => subsingleton_shiftedHom_coverSystemObj S W K hExt V hV i hi) A B

/-- **The prescribed object at a stage is a solution over that stage.** A stage is a member of
the displayed collection of the reindexed system, so this is
`Stacks.DerivedGlueing.selfSolutionOver`.

It is what makes `Stacks.DerivedGlueing.exists_unique_solutionOver_iso_of_wellOrderedCover` say
something: the type of solutions it quantifies over is inhabited at every stage, and this is the
very solution the source compares the colimit of the earlier stages with. -/
def selfSolutionOverStage (α : E) :
    SolutionOver (S.ofWellOrderedCover W hmono K rho hcocycle) (W α) :=
  selfSolutionOver _ (W α) ⟨α, rfl⟩

/-! ### The system displayed on the stages strictly below a stage -/

omit [WellFoundedLT E] in
/-- The stages strictly below a stage are members of the range of the cover. -/
theorem image_Iio_subset_range (α : E) : W '' Set.Iio α ⊆ Set.range W :=
  fun _ ⟨β, _, hβ⟩ => ⟨β, hβ⟩

/-- **The datum of [Stacks, Tag 0D6B] displayed only on the stages strictly below a stage.**
This is the system the limit stage of the source's recursion forms a solution of: there the
identification over `W α` itself is the object of the construction, so it cannot be part of the
datum the two solutions are solutions of. -/
def belowStageSystem (α : E) : LocallyGiven X :=
  (S.ofWellOrderedCover W hmono K rho hcocycle).subcollection (W '' Set.Iio α)
    (image_Iio_subset_range W α)

omit [WellFoundedLT E] in
include hmono in
/-- The stages strictly below a stage are totally ordered by inclusion. -/
theorem totallyOrdered_image_Iio (α : E) :
    ∀ U ∈ W '' Set.Iio α, ∀ V ∈ W '' Set.Iio α, U ≤ V ∨ V ≤ U :=
  fun U hU V hV => totallyOrdered_range_of_wellOrderedCover W hmono U
    (image_Iio_subset_range W α hU) V (image_Iio_subset_range W α hV)

omit [WellFoundedLT E] in
include hmono in
/-- **Hypothesis (1) of [Stacks, Tag 0D68] for the stages strictly below a stage**, which is
automatic because they are a chain. -/
theorem inf_eq_sSup_image_Iio (α : E) (U : Opens X.carrier) (hU : U ∈ W '' Set.Iio α)
    (V : Opens X.carrier) (hV : V ∈ W '' Set.Iio α) :
    U ⊓ V = sSup {T | T ∈ W '' Set.Iio α ∧ T ≤ U ⊓ V} :=
  inf_eq_sSup_of_totallyOrdered (W '' Set.Iio α) (totallyOrdered_image_Iio W hmono α) U V hU hV

omit [WellFoundedLT E] in
include hmono in
/-- **A stage with no immediate predecessor is the union of the stages strictly below it that it
contains.** Each of those is contained in it because the cover is increasing, so the condition is
no restriction and this is the hypothesis `hlimit` of [Stacks, Tag 0D6B] read as the covering
condition of Situation 0D67 at that stage. -/
theorem eq_sSup_image_Iio_of_limit (α : E) (hlimit : W α = ⨆ (β : E) (_ : β < α), W β) :
    W α = sSup {T | T ∈ W '' Set.Iio α ∧ T ≤ W α} := by
  refine le_antisymm (hlimit.le.trans ?_) (sSup_le fun T hT => hT.2)
  exact iSup₂_le fun β hβ => le_sSup ⟨⟨β, hβ, rfl⟩, hmono β α hβ⟩

/-- **The uniqueness input of the limit stages of [Stacks, Tag 0D6B], with nothing granted.**
Let `W` be a well ordered increasing cover, let `K α` be an object of `D(𝒪_{W_α})` without
negative self-Ext at each stage and let `ρ^α_β` be transition isomorphisms satisfying the cocycle
condition.  Let `α` be a stage with no immediate predecessor, so that `W α = ⋃_{β < α} W_β`.
Then two solutions over `W α` of the datum displayed on the stages *strictly below* `α` are
identified by a unique isomorphism of solutions.

This is exactly the step the source performs there: the termwise colimit `C^•` of the earlier
stages and the prescribed object `K_α` are both solutions of the system
`({K_β}_{β < α}, {ρ^β_{β'}}_{β' < β < α})` over `W α`, and uniqueness yields the single
isomorphism `σ : K_α → C^•`.  The source cites [Stacks, Tag 0D6A] for it and names it as the
place where the vanishing of the negative Ext groups is used; the vanishing enters here through
`Stacks.DerivedGlueing.subsingleton_shiftedHom_coverSystemObj`.

The stages below `α` cover only `W α` and not `X`, which is why this needs
`Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_covers` to ask nothing about a global
covering — see the section on the global covering hypothesis in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsAtAnOpenFromTheCover`. -/
theorem exists_unique_solutionOver_iso_below_of_wellOrderedCover
    (hExt : ∀ (α : E) (i : ℤ), i < 0 → Subsingleton (ShiftedHom (K α) (K α) i)) (α : E)
    (hlimit : W α = ⨆ (β : E) (_ : β < α), W β)
    (A B : SolutionOver (belowStageSystem S W hmono K rho hcocycle α) (W α)) :
    ∃! φ : A.obj ≅ B.obj, A.IsCompatibleHom B φ.hom :=
  hasUniqueSolutionOverIso_of_covers (belowStageSystem S W hmono K rho hcocycle α)
    (inf_eq_sSup_image_Iio W hmono α) (W α) (eq_sSup_image_Iio_of_limit W hmono α hlimit)
    (inf_eq_sSup_image_Iio W hmono α)
    (fun V hV i hi => subsingleton_shiftedHom_coverSystemObj S W K hExt V
      (image_Iio_subset_range W α hV) i hi) A B

/-- **The prescribed object at a stage is a solution over that stage of the datum displayed on
the stages strictly below it.** Its identifications are the prescribed transitions out of that
stage and their compatibility is the cocycle condition, so this is
`Stacks.DerivedGlueing.selfSolutionOverSubcollection`.

It is what makes `Stacks.DerivedGlueing.exists_unique_solutionOver_iso_below_of_wellOrderedCover`
say something — the type of solutions it quantifies over is inhabited — and it is the solution
`(K_α, ρ^α_β)` that the source compares the colimit of the earlier stages with. -/
def selfSolutionOverBelowStage (α : E) :
    SolutionOver (belowStageSystem S W hmono K rho hcocycle α) (W α) :=
  selfSolutionOverSubcollection (S.ofWellOrderedCover W hmono K rho hcocycle)
    (W '' Set.Iio α) (image_Iio_subset_range W α) (W α) ⟨α, rfl⟩

end Uniqueness

end Stacks.DerivedGlueing

end
