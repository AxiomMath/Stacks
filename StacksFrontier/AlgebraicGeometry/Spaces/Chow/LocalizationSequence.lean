module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenComplement

/-!
# Cycles on a closed subspace and on an open subspace

In the situation of Stacks 0EDT let `X/B` be good, let `i : Y ⟶ X` be a closed immersion over
the base and let `j : U ⟶ X` be an open immersion over the base. Pushforward along `i` carries
a `k`-cycle on `Y` to the `k`-cycle on `X` with the same coefficients on the images of the
integral closed subspaces of `Y` and zero elsewhere; restriction along `j` carries a `k`-cycle
on `X` to the `k`-cycle on `U` whose coefficient at an integral closed subspace of `U` is the
coefficient of the original cycle at the closure of its image.

When the images of `i` and `j` are complementary these are the two outer maps of the sequence
of Stacks 0EP9, and a cycle on `X` restricts to zero on `U` exactly when it is a pushforward
from `Y`. Restriction is moreover surjective, by extending a coefficient family on `U` by zero.

## Main definitions

* `AlgebraicGeometry.Space.cycleGroupClosedPushforward`: pushforward of `k`-cycles along a
  closed immersion over the base.
* `AlgebraicGeometry.Space.cycleGroupRestrict`: restriction of `k`-cycles along an open
  immersion over the base.

## Main results

* `AlgebraicGeometry.Space.cycleGroupRestrict_eq_zero_iff`: **Stacks 0EP9**, exactness at
  `Z_k(X)` — a `k`-cycle restricts to zero on the open complement exactly when it is the
  pushforward of a `k`-cycle on the closed complement.
* `AlgebraicGeometry.Space.cycleGroupRestrict_surjective`: **Stacks 0EP9**, exactness at
  `Z_k(U)` — restriction along an open immersion over the base is surjective on `k`-cycles.
* `AlgebraicGeometry.Space.injective_cycleGroupClosedPushforward`: exactness at `Z_k(Y)`, the
  pushforward being injective.
* `AlgebraicGeometry.Space.locallyFinite_subspacePointSet_closureImage`: a locally finite
  family of integral closed subspaces of the open subspace stays locally finite after taking
  closures in the ambient space.

## Implementation notes

Both maps are described by their effect on coefficient families, through the two maps on
integral closed subspaces of
`StacksFrontier/AlgebraicGeometry/Spaces/Chow/IntegralClosedSubspaceMaps.lean`: pushforward is
`Function.extend` along the injective map which takes the image of a subspace, and restriction
is composition with the map which takes the closure of the image. Each is additive because it
is built coefficientwise, and each lands in the right δ-degree because both maps on subspaces
preserve the δ-dimension.

The three local-finiteness transports are isolated as
`AlgebraicGeometry.Space.locallyFinite_of_isClosedEmbedding_extend`,
`AlgebraicGeometry.Space.locallyFinite_of_continuous_comap` and
`AlgebraicGeometry.Space.locallyFinite_of_isOpenEmbedding_extend`, all purely topological. The
first uses that the map on points of a closed immersion is a closed embedding, so that a point
outside its image has the complement of that image as a neighbourhood meeting nothing in the
family; the second only needs continuity.

The third, used for surjectivity of restriction, needs more: extending a family on `|U|` by the
empty set along an open embedding is *not* locally finite in general, the inverse image of a
neighbourhood of a point outside the open part being too large. Local Noetherianity of `|X|`,
which comes from Stacks 04ZK and Stacks 04ZF for a good algebraic space, supplies a Noetherian
open neighbourhood of that point, whose inverse image is then quasi-compact; the neighbourhood
being open, it meets the closure of the image of a member of the family only if it already meets
that image.

Neither statement below needs `Y` to carry the reduced induced structure, and neither needs `U`
to be the complement of `Y` except through the one hypothesis that the two point sets are
complementary; cycles see only the point sets of the integral closed subspaces involved.

The family form of the third transport,
`AlgebraicGeometry.Space.locallyFinite_subspacePointSet_closureImage`, differs from the use
made of it for surjectivity of restriction only in its index type: there the family is indexed
by the integral closed subspaces of `X` themselves and is extended by the empty set, here by an
arbitrary type, which is the shape in which a rational equivalence presents its subspaces.

### Relation to Stacks 0EQ7

Lemma 0EQ7 states that `CH_k(Y) → CH_k(X) → CH_k(U) → 0` is an exact complex. The exactness of
the corresponding sequence of cycle groups, Tag 0EP9, is the second half of its proof, and
`AlgebraicGeometry.Space.locallyFinite_subspacePointSet_closureImage` is the local-finiteness
step of its first half: the subspaces `W_j ⊆ U` carrying a rational equivalence on `U` are
replaced by their closures `W'_j ⊆ X`, and the resulting family is again locally finite.

## References

* [Stacks Project, Tag 04ZF](https://stacks.math.columbia.edu/tag/04ZF)
* [Stacks Project, Tag 04ZK](https://stacks.math.columbia.edu/tag/04ZK)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0EP9](https://stacks.math.columbia.edu/tag/0EP9)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQ7](https://stacks.math.columbia.edu/tag/0EQ7)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Transports of local finiteness -/

/-- A point of a member of a family which is empty off the range of the reindexing lies in a
member with an index in that range. -/
private theorem exists_eq_of_mem_of_empty {β : Type*} {ι κ : Type*} {e : ι → κ} {g : κ → Set β}
    (hempty : ∀ w : κ, (∀ i, e i ≠ w) → g w = ∅) {w : κ} {p : β} (hp : p ∈ g w) :
    ∃ i, e i = w := by
  by_contra h
  rw [hempty w fun i hi => h ⟨i, hi⟩] at hp
  exact hp

/-- Local finiteness of a family extended by the empty set along a closed embedding: a point
outside the image of the embedding has the complement of that image as a neighbourhood, which
meets no member of the family, and at a point of the image the embedding pulls a neighbourhood
back to a neighbourhood. -/
theorem locallyFinite_of_isClosedEmbedding_extend {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {q : α → β} (hq : Topology.IsClosedEmbedding q) {ι κ : Type*}
    {e : ι → κ} {f : ι → Set α} {g : κ → Set β}
    (hempty : ∀ w : κ, (∀ i, e i ≠ w) → g w = ∅) (hsub : ∀ i, g (e i) ⊆ q '' f i)
    (hf : LocallyFinite f) : LocallyFinite g := by
  intro x
  by_cases hx : x ∈ Set.range q
  · obtain ⟨y, rfl⟩ := hx
    obtain ⟨t, ht, htfin⟩ := hf y
    rw [hq.isInducing.nhds_eq_comap, Filter.mem_comap] at ht
    obtain ⟨V, hV, hVt⟩ := ht
    refine ⟨V, hV, (htfin.image e).subset ?_⟩
    intro w hw
    obtain ⟨p, hpg, hpV⟩ := hw
    obtain ⟨i, rfl⟩ := exists_eq_of_mem_of_empty hempty hpg
    obtain ⟨s, hsf, rfl⟩ := hsub i hpg
    exact ⟨i, ⟨s, hsf, hVt hpV⟩, rfl⟩
  · refine ⟨(Set.range q)ᶜ, hq.isClosed_range.isOpen_compl.mem_nhds hx, ?_⟩
    convert Set.finite_empty
    refine Set.eq_empty_iff_forall_notMem.2 fun w hw => ?_
    obtain ⟨p, hpg, hpc⟩ := hw
    obtain ⟨i, rfl⟩ := exists_eq_of_mem_of_empty hempty hpg
    obtain ⟨s, -, rfl⟩ := hsub i hpg
    exact hpc ⟨s, rfl⟩

/-- Local finiteness pulled back along a continuous map: if each member of the source family has
image inside the corresponding member of a locally finite family, indexed injectively, then the
source family is locally finite. -/
theorem locallyFinite_of_continuous_comap {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {q : α → β} (hq : Continuous q) {ι κ : Type*} {e : ι → κ}
    (hinj : Function.Injective e) {f : ι → Set α} {g : κ → Set β}
    (hsub : ∀ i, q '' f i ⊆ g (e i)) (hg : LocallyFinite g) : LocallyFinite f := by
  intro y
  obtain ⟨V, hV, hVfin⟩ := hg (q y)
  refine ⟨q ⁻¹' V, hq.continuousAt hV, (hVfin.preimage hinj.injOn).subset ?_⟩
  intro i hi
  obtain ⟨p, hpf, hpV⟩ := hi
  exact ⟨q p, hsub i ⟨p, hpf, rfl⟩, hpV⟩

/-- The inverse image of a Noetherian subset under an embedding is quasi-compact: the image of
that inverse image is the intersection of the subset with the range of the embedding, and every
subset of a Noetherian subspace is quasi-compact. -/
@[ega "0 2.2.4" "more general"]
theorem isCompact_preimage_of_noetherianSpace {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {q : α → β} (hq : Topology.IsEmbedding q) {t : Set β}
    (ht : NoetherianSpace t) : IsCompact (q ⁻¹' t) := by
  rw [hq.isCompact_iff, Set.image_preimage_eq_inter_range]
  exact (noetherianSpace_set_iff t).1 ht _ Set.inter_subset_left

/-- Local finiteness of a family extended by the empty set along an open embedding into a locally
Noetherian space, each member of the extended family being contained in the closure of the image
of the corresponding member of a locally finite family.

A Noetherian open neighbourhood of a point of the target pulls back to a quasi-compact subset of
the source, which only finitely many members of the source family meet; and that neighbourhood
being open, it meets the closure of the image of a member only if it already meets that image. -/
theorem locallyFinite_of_isOpenEmbedding_extend {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (hβ : IsLocallyNoetherianSpace β) {q : α → β}
    (hq : Topology.IsOpenEmbedding q) {ι κ : Type*} {e : ι → κ} {f : ι → Set α} {g : κ → Set β}
    (hempty : ∀ w : κ, (∀ i, e i ≠ w) → g w = ∅)
    (hsub : ∀ i, g (e i) ⊆ closure (q '' f i)) (hf : LocallyFinite f) : LocallyFinite g := by
  intro x
  obtain ⟨t, htopen, hxt, htnoeth⟩ := hβ x
  refine ⟨t, htopen.mem_nhds hxt, ((hf.finite_nonempty_inter_compact
    (isCompact_preimage_of_noetherianSpace hq.isEmbedding htnoeth)).image e).subset ?_⟩
  intro w hw
  obtain ⟨p, hpg, hpt⟩ := hw
  obtain ⟨i, rfl⟩ := exists_eq_of_mem_of_empty hempty hpg
  obtain ⟨p', hp't, y, hyf, rfl⟩ := mem_closure_iff.1 (hsub i hpg) t htopen hpt
  exact ⟨i, ⟨y, hyf, hp't⟩, rfl⟩

/-! ### Pushforward along a closed immersion -/

section Pushforward

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- Pushforward of a coefficient family along a closed immersion `i : Y ⟶ X`: the coefficient at
the image of an integral closed subspace of `Y` is its coefficient there, and the coefficient at
an integral closed subspace of `X` not of that form is zero. -/
noncomputable def cycleClosedPushforward (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X) {i : Y ⟶ X}
    (hi : IsClosedImmersion D.site D.base D.base_mem i)
    (β : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) :
    IntegralClosedSubspace D.site D.base D.base_mem X → ℤ :=
  Function.extend
    (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX hY hXdec hi) β 0

variable (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X) {i : Y ⟶ X}
    (hi : IsClosedImmersion D.site D.base D.base_mem i)

/-- The coefficient of a pushforward at the image of an integral closed subspace is the
coefficient there. -/
@[simp]
theorem cycleClosedPushforward_apply_pushforward
    (β : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    cycleClosedPushforward D hX hY hXdec hi β
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX hY hXdec hi Z) = β Z :=
  (IntegralClosedSubspace.injective_pushforward D.site D.base D.base_mem hX hY hXdec
    hi).extend_apply _ _ _

/-- The coefficient of a pushforward vanishes at an integral closed subspace which is not the
image of one of the closed subspace. -/
theorem cycleClosedPushforward_apply_of_forall_ne
    (β : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : ∀ Z, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX hY hXdec hi Z
      ≠ W) :
    cycleClosedPushforward D hX hY hXdec hi β W = 0 :=
  Function.extend_apply' β (0 : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ) W
    (fun h => hW h.choose h.choose_spec)

/-- Pushforward of coefficient families along a closed immersion takes the zero family to the
zero family. -/
@[simp]
theorem cycleClosedPushforward_zero : cycleClosedPushforward D hX hY hXdec hi 0 = 0 := by
  funext W
  by_cases hW : ∃ Z, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX hY hXdec
      hi Z = W
  · obtain ⟨Z, rfl⟩ := hW
    rw [cycleClosedPushforward_apply_pushforward]
    rfl
  · rw [cycleClosedPushforward_apply_of_forall_ne D hX hY hXdec hi 0 W
      fun Z hZ => hW ⟨Z, hZ⟩]
    rfl

/-- Pushforward of coefficient families along a closed immersion is additive. -/
@[simp]
theorem cycleClosedPushforward_add
    (β γ : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ) :
    cycleClosedPushforward D hX hY hXdec hi (β + γ) =
      cycleClosedPushforward D hX hY hXdec hi β + cycleClosedPushforward D hX hY hXdec hi γ := by
  funext W
  by_cases hW : ∃ Z, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX hY hXdec
      hi Z = W
  · obtain ⟨Z, rfl⟩ := hW
    simp only [cycleClosedPushforward_apply_pushforward, Pi.add_apply]
  · simp only [Pi.add_apply,
      cycleClosedPushforward_apply_of_forall_ne D hX hY hXdec hi _ W fun Z hZ => hW ⟨Z, hZ⟩,
      add_zero]

/-- The pushforward of a `k`-cycle along a closed immersion over the base is a `k`-cycle: the
point sets of the images form a locally finite collection because the map on points is a closed
embedding, and the δ-dimension is preserved. -/
theorem cycleClosedPushforward_mem_cyclesOfDimension (sX : X ⟶ D.space)
    (hsX : IsLocallyOfFiniteType D.site D.base D.base_mem sX) (sY : Y ⟶ D.space)
    (hic : i ≫ sX = sY) (k : ℤ)
    {β : IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ}
    (hβ : β ∈ cyclesOfDimension D sY k) :
    cycleClosedPushforward D hX hY hXdec hi β ∈ cyclesOfDimension D sX k := by
  refine ⟨?_, ?_⟩
  · refine locallyFinite_of_isClosedEmbedding_extend
      (isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hX hi)
      (e := IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX hY hXdec hi)
      (fun W hW => ?_) (fun Z => ?_) hβ.1
    · simp [cycleClosedPushforward_apply_of_forall_ne D hX hY hXdec hi β W hW]
    · rw [cycleClosedPushforward_apply_pushforward,
        IntegralClosedSubspace.subspacePointSet_pushforward]
      split_ifs
      · simp
      · exact subset_rfl
  · intro W hW
    by_cases hWe : ∃ Z, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX hY
        hXdec hi Z = W
    swap
    · rw [cycleClosedPushforward_apply_of_forall_ne D hX hY hXdec hi β W
        fun Z hZ => hWe ⟨Z, hZ⟩] at hW
      exact absurd rfl hW
    · obtain ⟨Z, rfl⟩ := hWe
      rw [cycleClosedPushforward_apply_pushforward] at hW
      rw [IntegralClosedSubspace.deltaDimension_pushforward D sX hsX hX hY hXdec hi Z, hic]
      exact hβ.2 Z hW

/-- Pushforward of `k`-cycles along a closed immersion `i : Y ⟶ X` over the base. -/
noncomputable def cycleGroupClosedPushforward (sX : X ⟶ D.space)
    (hsX : IsLocallyOfFiniteType D.site D.base D.base_mem sX) (sY : Y ⟶ D.space)
    (hic : i ≫ sX = sY) (k : ℤ) : CycleGroup D sY k →+ CycleGroup D sX k where
  toFun β := ⟨cycleClosedPushforward D hX hY hXdec hi β.1,
    cycleClosedPushforward_mem_cyclesOfDimension D hX hY hXdec hi sX hsX sY hic k β.2⟩
  map_zero' := Subtype.ext (cycleClosedPushforward_zero D hX hY hXdec hi)
  map_add' β γ := Subtype.ext (cycleClosedPushforward_add D hX hY hXdec hi β.1 γ.1)

/-- Pushforward along a closed immersion is injective on cycles: the map on integral closed
subspaces is injective, and the coefficient at an image is the original coefficient. -/
theorem injective_cycleGroupClosedPushforward (sX : X ⟶ D.space)
    (hsX : IsLocallyOfFiniteType D.site D.base D.base_mem sX) (sY : Y ⟶ D.space)
    (hic : i ≫ sX = sY) (k : ℤ) :
    Function.Injective
      (cycleGroupClosedPushforward D hX hY hXdec hi sX hsX sY hic k) := by
  intro β γ h
  have h' : cycleClosedPushforward D hX hY hXdec hi β.1 =
      cycleClosedPushforward D hX hY hXdec hi γ.1 := congrArg Subtype.val h
  refine Subtype.ext (funext fun Z => ?_)
  rw [← cycleClosedPushforward_apply_pushforward D hX hY hXdec hi β.1 Z,
    ← cycleClosedPushforward_apply_pushforward D hX hY hXdec hi γ.1 Z, h']

end Pushforward

/-! ### Restriction along an open immersion -/

section Restrict

variable (D : BaseSpaceDimensionSituation.{u})
    {X U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- Restriction of `k`-cycles along an open immersion `j : U ⟶ X` over the base: the coefficient
at an integral closed subspace of `U` is the coefficient of the original cycle at the closure of
its image in `X`. -/
noncomputable def cycleGroupRestrict (sX : X ⟶ D.space) (hX : D.IsGood sX) (sU : U ⟶ D.space)
    (hU : D.IsGood sU) {j : U ⟶ X} (hj : IsOpenImmersion D.site D.base D.base_mem j)
    (hjc : j ≫ sX = sU) (k : ℤ) :
    CycleGroup D sX k →+ CycleGroup D sU k where
  toFun α := ⟨fun W => α.1 (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1
      (D.isDecentSpace_of_isGood sX hX) j W), by
    have himm : IsImmersion D.site D.base D.base_mem j :=
      isImmersion_of_isOpenImmersion D.site D.base D.base_mem hj
    have hinj := IntegralClosedSubspace.injective_closureImage D hX.1 hU.1
      (D.isDecentSpace_of_isGood sX hX) himm
    refine ⟨?_, ?_⟩
    · refine locallyFinite_of_continuous_comap
        (continuous_pointsMap D.site D.base D.base_mem j) hinj (fun W => ?_) α.2.1
      rw [IntegralClosedSubspace.subspacePointSet_closureImage]
      split_ifs
      · simp
      · exact subset_closure
    · intro W hW
      rw [← hjc, ← IntegralClosedSubspace.deltaDimension_closureImage D sX hX.2.2 hX.1 hU.1
        (D.isDecentSpace_of_isGood sX hX) himm W]
      exact α.2.2 _ hW⟩
  map_zero' := rfl
  map_add' α γ := rfl

/-- The coefficient of a restriction at an integral closed subspace of the open subspace is the
coefficient of the original cycle at the closure of its image. -/
theorem cycleGroupRestrict_apply (sX : X ⟶ D.space) (hX : D.IsGood sX) (sU : U ⟶ D.space)
    (hU : D.IsGood sU) {j : U ⟶ X} (hj : IsOpenImmersion D.site D.base D.base_mem j)
    (hjc : j ≫ sX = sU) (k : ℤ) (α : CycleGroup D sX k)
    (W : IntegralClosedSubspace D.site D.base D.base_mem U) :
    (cycleGroupRestrict D sX hX sU hU hj hjc k α).1 W =
      α.1 (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1
        (D.isDecentSpace_of_isGood sX hX) j W) :=
  rfl

end Restrict

/-! ### The localization sequence -/

section Localization

/-- An irreducible closed set is the closure of its intersection with any open set it meets: a
nonempty relatively open subset of a preirreducible set is dense in it. -/
@[ega "0 2.1.1" "open-density criterion", ega "0 2.1.6" "density of Z ∩ U in Z"]
theorem closure_inter_open_eq_of_isIrreducible {α : Type*} [TopologicalSpace α] {T O : Set α}
    (hT : IsIrreducible T) (hTc : IsClosed T) (hO : IsOpen O) (hne : (T ∩ O).Nonempty) :
    closure (T ∩ O) = T :=
  Set.Subset.antisymm (hTc.closure_subset_iff.2 Set.inter_subset_left)
    (subset_closure_inter_of_isPreirreducible_of_isOpen hT.2 hO hne)

/-- The inverse image of an irreducible set meeting the image of an open embedding is
irreducible: an open set of the source is the inverse image of an open set of the target, and
intersecting with the open image keeps it open. -/
theorem isIrreducible_preimage_of_isOpenEmbedding {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {q : α → β} (hq : Topology.IsOpenEmbedding q) {T : Set β}
    (hT : IsIrreducible T) (hne : (T ∩ Set.range q).Nonempty) : IsIrreducible (q ⁻¹' T) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨p, hpT, y, rfl⟩ := hne
    exact ⟨y, hpT⟩
  · intro V₁ V₂ hV₁ hV₂ ⟨y₁, hy₁T, hy₁V⟩ ⟨y₂, hy₂T, hy₂V⟩
    obtain ⟨O₁, hO₁, hO₁eq⟩ := hq.isInducing.isOpen_iff.1 hV₁
    obtain ⟨O₂, hO₂, hO₂eq⟩ := hq.isInducing.isOpen_iff.1 hV₂
    obtain ⟨x, hxT, ⟨hxO₁, -⟩, hxO₂, y, rfl⟩ :=
      hT.2 (O₁ ∩ Set.range q) (O₂ ∩ Set.range q) (hO₁.inter hq.isOpen_range)
        (hO₂.inter hq.isOpen_range)
        ⟨q y₁, hy₁T, ⟨by rw [← hO₁eq] at hy₁V; exact hy₁V, y₁, rfl⟩⟩
        ⟨q y₂, hy₂T, ⟨by rw [← hO₂eq] at hy₂V; exact hy₂V, y₂, rfl⟩⟩
    refine ⟨y, hxT, ?_, ?_⟩
    · rw [← hO₁eq]; exact hxO₁
    · rw [← hO₂eq]; exact hxO₂

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The map on points of an open immersion into an algebraic space over `S` is an open
embedding: it is an embedding by Stacks 0ABJ and its image is open. -/
theorem isOpenEmbedding_pointsMap_of_isOpenImmersion
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X) {j : U ⟶ X}
    (hj : IsOpenImmersion D.site D.base D.base_mem j) :
    Topology.IsOpenEmbedding (pointsMap D.site D.base D.base_mem U j) :=
  ⟨isEmbedding_pointsMap_of_isImmersion D.site D.base D.base_mem hX j
      (isImmersion_of_isOpenImmersion D.site D.base D.base_mem hj),
    isOpen_range_pointsMap_of_isOpenImmersion D.site D.base D.base_mem j hj⟩

/-- An integral closed subspace of `X` whose point set meets the image of an open immersion
`j : U ⟶ X` is the closure of the image of an integral closed subspace of `U`, namely of the one
on the inverse image of its point set. -/
theorem IntegralClosedSubspace.exists_closureImage_eq
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hU : IsAlgebraicSpace D.site D.base D.base_mem U)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X)
    (hUdec : IsDecentSpace D.site D.base D.base_mem U) {j : U ⟶ X}
    (hj : IsOpenImmersion D.site D.base D.base_mem j)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : (subspacePointSet D.site D.base D.base_mem X W.subspace ∩
      Set.range (pointsMap D.site D.base D.base_mem U j)).Nonempty) :
    ∃ W' : IntegralClosedSubspace D.site D.base D.base_mem U,
      IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX hXdec j W' = W := by
  have hemb := isOpenEmbedding_pointsMap_of_isOpenImmersion D hX hj
  have hWirr := isIrreducible_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem W
  have hWcl := isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hX W
  have hirr : IsIrreducible (pointsMap D.site D.base D.base_mem U j ⁻¹'
      subspacePointSet D.site D.base D.base_mem X W.subspace) :=
    isIrreducible_preimage_of_isOpenEmbedding hemb hWirr hW
  set T : IrreducibleCloseds (points D.site D.base D.base_mem U) :=
    ⟨pointsMap D.site D.base D.base_mem U j ⁻¹'
        subspacePointSet D.site D.base D.base_mem X W.subspace, hirr,
      hWcl.preimage (continuous_pointsMap D.site D.base D.base_mem j)⟩ with hTdef
  refine ⟨integralClosedSubspaceOfPoints D.site D.base D.base_mem hU hUdec T, ?_⟩
  refine (eq_integralClosedSubspaceOfPoints D.site D.base D.base_mem hX hXdec W _ ?_).symm
  have hpts : subspacePointSet D.site D.base D.base_mem U
      (integralClosedSubspaceOfPoints D.site D.base D.base_mem hU hUdec T).subspace =
      (T : Set (points D.site D.base D.base_mem U)) :=
    subspacePointSet_integralClosedSubspaceOfPoints D.site D.base D.base_mem hU hUdec T
  have hgoal : subspacePointSet D.site D.base D.base_mem X W.subspace =
      closure (pointsMap D.site D.base D.base_mem U j ''
        subspacePointSet D.site D.base D.base_mem U
          (integralClosedSubspaceOfPoints D.site D.base D.base_mem hU hUdec T).subspace) := by
    rw [hpts]
    change subspacePointSet D.site D.base D.base_mem X W.subspace =
      closure (pointsMap D.site D.base D.base_mem U j ''
        (pointsMap D.site D.base D.base_mem U j ⁻¹'
          subspacePointSet D.site D.base D.base_mem X W.subspace))
    rw [Set.image_preimage_eq_inter_range]
    exact (closure_inter_open_eq_of_isIrreducible hWirr hWcl hemb.isOpen_range hW).symm
  exact hgoal

/-- The space of points of a good algebraic space over `D` is locally Noetherian. -/
private theorem isLocallyNoetherianSpace_points_of_isGood (sX : X ⟶ D.space) (hX : D.IsGood sX) :
    IsLocallyNoetherianSpace (points D.site D.base D.base_mem X) :=
  isLocallyNoetherianSpace_of_isLocallyNoetherian D.site D.base D.base_mem X hX.1
    (isLocallyNoetherian_of_isLocallyOfFiniteType D.site D.base D.base_mem hX.1
      D.isAlgebraicSpace sX hX.2.2 D.locallyNoetherian)

/-- **Stacks 0EP9, exactness at the `k`-cycles of the ambient space.** In Situation 0EDT let
`X/B` be good, let `i : Y ⟶ X` be a closed immersion over the base and let `j : U ⟶ X` be an
open immersion over the base whose image is the complement of the image of `i`. A `k`-cycle on
`X` restricts to zero on `U` exactly when it is the pushforward of a `k`-cycle on `Y`. -/
@[stacks 0EP9 "exactness at the k-cycles of the ambient space"]
theorem cycleGroupRestrict_eq_zero_iff (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (sU : U ⟶ D.space) (hU : D.IsGood sU) {i : Y ⟶ X}
    (hi : IsClosedImmersion D.site D.base D.base_mem i) (hic : i ≫ sX = sY) {j : U ⟶ X}
    (hj : IsOpenImmersion D.site D.base D.base_mem j) (hjc : j ≫ sX = sU)
    (hcomplement : Set.range (pointsMap D.site D.base D.base_mem Y i) =
      (Set.range (pointsMap D.site D.base D.base_mem U j))ᶜ) (k : ℤ) (α : CycleGroup D sX k) :
    cycleGroupRestrict D sX hX sU hU hj hjc k α = 0 ↔
      ∃ β : CycleGroup D sY k,
        cycleGroupClosedPushforward D hX.1 hY.1 (D.isDecentSpace_of_isGood sX hX) hi sX hX.2.2
          sY hic k β = α := by
  have hXdec := D.isDecentSpace_of_isGood sX hX
  have hYdec := D.isDecentSpace_of_isGood sY hY
  have hUdec := D.isDecentSpace_of_isGood sU hU
  constructor
  · intro hz
    -- a subspace carrying a nonzero coefficient lies in the closed part
    have hoff : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X, α.1 W ≠ 0 →
        subspacePointSet D.site D.base D.base_mem X W.subspace ⊆
          Set.range (pointsMap D.site D.base D.base_mem Y i) := by
      intro W hW
      by_contra hsub
      obtain ⟨p, hpW, hp⟩ := Set.not_subset.1 hsub
      have hpj : p ∈ Set.range (pointsMap D.site D.base D.base_mem U j) := by
        by_contra hnot
        exact hp (hcomplement ▸ hnot)
      obtain ⟨W', rfl⟩ := IntegralClosedSubspace.exists_closureImage_eq D hX.1 hU.1 hXdec hUdec
        hj W ⟨p, hpW, hpj⟩
      exact hW (congrArg (fun e : CycleGroup D sU k => e.1 W') hz)
    -- every such subspace is the image of one of the closed part
    have hex : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X, α.1 W ≠ 0 →
        ∃ Z, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1 hXdec hi Z
          = W := fun W hW =>
      IntegralClosedSubspace.exists_pushforward_eq D.site D.base D.base_mem hX.1 hY.1 hXdec
        hYdec hi W (hoff W hW)
    have hβmem : (fun Z => α.1 (IntegralClosedSubspace.pushforward D.site D.base D.base_mem
        hX.1 hY.1 hXdec hi Z)) ∈ cyclesOfDimension D sY k := by
      refine ⟨?_, ?_⟩
      · refine locallyFinite_of_continuous_comap
          (continuous_pointsMap D.site D.base D.base_mem i)
          (IntegralClosedSubspace.injective_pushforward D.site D.base D.base_mem hX.1 hY.1
            hXdec hi)
          (e := IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1 hXdec hi)
          (fun Z => ?_) α.2.1
        rw [IntegralClosedSubspace.subspacePointSet_pushforward]
        split_ifs
        · simp
        · exact subset_rfl
      · intro Z hZ
        rw [← hic,
          ← IntegralClosedSubspace.deltaDimension_pushforward D sX hX.2.2 hX.1 hY.1 hXdec hi Z]
        exact α.2.2 _ hZ
    refine ⟨⟨_, hβmem⟩, Subtype.ext (funext fun W => ?_)⟩
    change cycleClosedPushforward D hX.1 hY.1 hXdec hi
      (fun Z => α.1 (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
        hXdec hi Z)) W = α.1 W
    by_cases hW : ∃ Z, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 hY.1
        hXdec hi Z = W
    · obtain ⟨Z, rfl⟩ := hW
      exact cycleClosedPushforward_apply_pushforward D hX.1 hY.1 hXdec hi _ Z
    · rw [cycleClosedPushforward_apply_of_forall_ne D hX.1 hY.1 hXdec hi _ W
        fun Z hZ => hW ⟨Z, hZ⟩]
      by_contra hne
      exact hW (hex W fun h => hne h.symm)
  · rintro ⟨β, rfl⟩
    refine Subtype.ext (funext fun W' => ?_)
    rw [cycleGroupRestrict_apply]
    refine cycleClosedPushforward_apply_of_forall_ne D hX.1 hY.1 hXdec hi _ _ fun Z hZ => ?_
    obtain ⟨p, hp⟩ := (isIrreducible_range_pointsMap_integralClosedSubspace D.site D.base
      D.base_mem W').1
    have hmem : pointsMap D.site D.base D.base_mem U j p ∈
        subspacePointSet D.site D.base D.base_mem X
          (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1 hXdec j W').subspace
        := by
      rw [IntegralClosedSubspace.subspacePointSet_closureImage]
      exact subset_closure ⟨p, hp, rfl⟩
    rw [← hZ, IntegralClosedSubspace.subspacePointSet_pushforward] at hmem
    obtain ⟨y, -, hy⟩ := hmem
    have : pointsMap D.site D.base D.base_mem Y i y ∈
        (Set.range (pointsMap D.site D.base D.base_mem U j))ᶜ := hcomplement ▸ ⟨y, rfl⟩
    exact this ⟨p, hy.symm⟩

/-- **Stacks 0EP9, surjectivity onto the `k`-cycles of the open subspace.** In Situation 0EDT let
`X/B` and `U/B` be good and let `j : U ⟶ X` be an open immersion over the base. Every `k`-cycle
on `U` is the restriction of a `k`-cycle on `X`, namely of the coefficient family extending it by
zero along the map which takes the closure of the image of an integral closed subspace.

That extension is a `k`-cycle: it has the right δ-dimension because taking the closure of the
image preserves it, and its support family is locally finite because `|X|` is locally Noetherian,
the structure morphism being locally of finite type over a locally Noetherian base. -/
@[stacks 0EP9 "surjectivity onto the k-cycles of the open subspace"]
theorem cycleGroupRestrict_surjective (sX : X ⟶ D.space) (hX : D.IsGood sX) (sU : U ⟶ D.space)
    (hU : D.IsGood sU) {j : U ⟶ X} (hj : IsOpenImmersion D.site D.base D.base_mem j)
    (hjc : j ≫ sX = sU) (k : ℤ) :
    Function.Surjective (cycleGroupRestrict D sX hX sU hU hj hjc k) := by
  have hXdec := D.isDecentSpace_of_isGood sX hX
  have himm : IsImmersion D.site D.base D.base_mem j :=
    isImmersion_of_isOpenImmersion D.site D.base D.base_mem hj
  have hinj := IntegralClosedSubspace.injective_closureImage D hX.1 hU.1 hXdec himm
  have hnoeth := isLocallyNoetherianSpace_points_of_isGood D sX hX
  intro β
  have hcoeff : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem U,
      Function.extend (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1 hXdec j)
          β.1 0 (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1 hXdec j W) =
        β.1 W :=
    fun W => hinj.extend_apply β.1 0 W
  have hvanish : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      (∀ W', IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1 hXdec j W' ≠ W) →
        Function.extend
          (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1 hXdec j) β.1 0 W =
          0 :=
    fun W hW => Function.extend_apply' β.1
      (0 : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ) W
      fun h => hW h.choose h.choose_spec
  have hmem : Function.extend
      (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1 hXdec j) β.1 0 ∈
      cyclesOfDimension D sX k := by
    refine ⟨?_, ?_⟩
    · refine locallyFinite_of_isOpenEmbedding_extend hnoeth
        (isOpenEmbedding_pointsMap_of_isOpenImmersion D hX.1 hj)
        (e := IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1 hXdec j)
        (fun W hW => ?_) (fun W => ?_) β.2.1
      · simp [hvanish W hW]
      · simp only [hcoeff W, IntegralClosedSubspace.subspacePointSet_closureImage]
        split_ifs
        · simp
        · exact subset_rfl
    · intro W hW
      by_cases hWe : ∃ W', IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1
          hXdec j W' = W
      · obtain ⟨W', rfl⟩ := hWe
        rw [IntegralClosedSubspace.deltaDimension_closureImage D sX hX.2.2 hX.1 hU.1 hXdec himm
          W', hjc]
        exact β.2.2 W' fun h => hW ((hcoeff W').trans h)
      · rw [hvanish W fun W' h => hWe ⟨W', h⟩] at hW
        exact absurd rfl hW
  exact ⟨⟨_, hmem⟩, Subtype.ext (funext fun W => hcoeff W)⟩

/-- **The lifting step in the proof of Stacks 0EQ7.** In Situation 0EDT let `X/B` be good and
let `j : U ⟶ X` be an open immersion. A family of integral closed subspaces of `U` whose point
sets form a locally finite collection in `|U|` is carried by taking closures of images to a
family of integral closed subspaces of `X` whose point sets form a locally finite collection in
`|X|`.

The source argues this by quasi-compactness: a quasi-compact open `V ⊆ |X|` is Noetherian, so
`V ∩ |U|` is again quasi-compact, and a member of the original family meets it exactly when its
closure meets `V`. Here that argument is
`AlgebraicGeometry.Space.locallyFinite_of_isOpenEmbedding_extend`, applied along the identity
reindexing, local Noetherianity of `|X|` coming from goodness as for surjectivity of
restriction. -/
theorem locallyFinite_subspacePointSet_closureImage (sX : X ⟶ D.space) (hX : D.IsGood sX)
    {j : U ⟶ X} (hj : IsOpenImmersion D.site D.base D.base_mem j) {J : Type*}
    (W : J → IntegralClosedSubspace D.site D.base D.base_mem U)
    (hW : LocallyFinite fun n => subspacePointSet D.site D.base D.base_mem U (W n).subspace) :
    LocallyFinite fun n => subspacePointSet D.site D.base D.base_mem X
      (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hX.1
        (D.isDecentSpace_of_isGood sX hX) j (W n)).subspace := by
  have hnoeth := isLocallyNoetherianSpace_points_of_isGood D sX hX
  exact locallyFinite_of_isOpenEmbedding_extend hnoeth
    (isOpenEmbedding_pointsMap_of_isOpenImmersion D hX.1 hj) (e := id)
    (fun n hn => absurd rfl (hn n))
    (fun n => (IntegralClosedSubspace.subspacePointSet_closureImage D.site D.base D.base_mem
      hX.1 (D.isDecentSpace_of_isGood sX hX) j (W n)).subset) hW

end Localization

end AlgebraicGeometry.Space

end
