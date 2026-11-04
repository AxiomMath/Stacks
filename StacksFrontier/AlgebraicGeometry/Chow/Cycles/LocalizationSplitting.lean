module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Chow.Cycles.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Splitting a locally finite direct sum along an open subset and its closed complement

Stacks 0GUA asserts, for `U ⊆ X` open with reduced closed complement `Y`, a split short exact
sequence relating the three primed direct sums `⨁'_{δ(x) = k + i} K_i^M(κ(x))` taken over the
points of `Y`, of `X` and of `U`. This file proves the part of that assertion that is about the
chain groups alone, for an arbitrary family of abelian groups indexed by an arbitrary set of
points, and therefore uniformly in the degree `i`.

## The setup

`X` is a scheme, `T` is a set of points of `X`, and `G` is a family of abelian groups indexed by
`T`. The locally finite direct sum `locallyFiniteDirectSum X T G` of Stacks 0GU2 is the subgroup
of `∀ x : T, G x` whose members have support meeting every quasi-compact open in a finite set.
A subset `W` of `X` cuts out the subgroup `supportedOn X T G W` of families vanishing at every
point outside `W`.

## What is proved

Truncation to `W` — keep the components at points of `W` and replace the others by zero — is an
idempotent endomorphism of the locally finite direct sum landing in the families supported on
`W`. Truncation to `W` and truncation to the complement of `W` add up to the identity and kill
each other, so the two subgroups of families supported on `W` and on its complement are
complementary: the resulting short exact sequence is split, by truncation, with no hypothesis on
`W` and none on `X`.

The remaining content of the degreewise assertion is that the families supported on an open `U`
are the locally finite direct sum computed inside `U`. One inclusion is formal. The converse is
where a hypothesis enters: a family supported on `U` whose support is finite in every
quasi-compact open *of `U`* is locally finite on `X` as well, because on a locally Noetherian
scheme the intersection of a quasi-compact open with `U` is again a quasi-compact open. That is
`mem_locallyFiniteDirectSum_of_subset_isOpen`, and it is the step that makes restriction to `U`
surjective.

## What is carried

* `isCompact_inter_of_isLocallyNoetherian` and
  `mem_locallyFiniteDirectSum_of_subset_isOpen` carry `[IsLocallyNoetherian X]`. It is not
  removable: without it a quasi-compact open of `X` can meet `U` in an open set that is not
  quasi-compact, and then a family that is locally finite on `U` need not be locally finite on
  `X`. On the schemes of Stacks 0GUA the hypothesis is automatic, since a scheme locally of
  finite type over a locally Noetherian base is locally Noetherian.
* Nothing here carries the existence of the complex of Stacks 0GU9, nor any of its
  differentials: the statements below are about the chain groups and the truncation maps only.
  In particular nothing here asserts Stacks 0GUA, which additionally requires the three
  truncations to be compatible with the two boundary maps of Stacks 0GU9 and then feeds that
  compatibility into the snake lemma.

## Main results

* `AlgebraicGeometry.isCompact_inter_of_isLocallyNoetherian` — on a locally Noetherian scheme
  every subset of a quasi-compact open is quasi-compact.
* `AlgebraicGeometry.locallyFiniteTruncate` — truncation of a locally finite family to a subset
  of `X`, as a homomorphism.
* `AlgebraicGeometry.locallyFiniteTruncate_add_compl` — truncation to `W` plus truncation to the
  complement of `W` is the identity.
* `AlgebraicGeometry.isCompl_supportedOnSubgroup` — the families supported on `W` and those
  supported on its complement are complementary subgroups of the locally finite direct sum.
* `AlgebraicGeometry.mem_locallyFiniteDirectSum_of_subset_isOpen` — a family supported on an
  open `U` and finite on every quasi-compact open contained in `U` is locally finite.

## References

* [Stacks Project, Tag 0GUA](https://stacks.math.columbia.edu/tag/0GUA)
* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
* [Stacks Project, Tag 0GU3](https://stacks.math.columbia.edu/tag/0GU3)
* [Stacks Project, Tag 0GU2](https://stacks.math.columbia.edu/tag/0GU2)
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry

open TopologicalSpace

/-! ### Subsets of quasi-compact opens of a locally Noetherian scheme -/

/-- **On a locally Noetherian scheme every subset of a quasi-compact open is quasi-compact.**
A quasi-compact open `V` is a Noetherian scheme, hence a Noetherian topological space, in which
every subspace is quasi-compact; the image of a quasi-compact subspace of `V` under the
inclusion is the corresponding intersection with `V`. -/
@[ega "I 6.1.2" "more general"]
theorem isCompact_inter_of_isLocallyNoetherian {X : Scheme.{u}} [IsLocallyNoetherian X]
    (V : X.Opens) (hV : IsCompact (V : Set X)) (s : Set X) :
    IsCompact ((V : Set X) ∩ s) := by
  have : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV
  have : IsNoetherian V.toScheme := ⟨⟩
  have hnoeth : NoetherianSpace V.toScheme := inferInstance
  rw [← Subtype.image_preimage_coe]
  exact (hnoeth.isCompact (Subtype.val ⁻¹' s)).image continuous_subtype_val

/-! ### Families supported on a subset -/

variable {X : Scheme.{u}} {T : Set X} (G : T → Type v) [∀ x, AddCommGroup (G x)]

/-- The subgroup of pointwise families vanishing at every point of `T` outside `W`. -/
def supportedOn (X : Scheme.{u}) (T : Set X) (G : T → Type v) [∀ x, AddCommGroup (G x)]
    (W : Set X) : AddSubgroup (∀ x : T, G x) where
  carrier := {a | ∀ x : T, (x : X) ∉ W → a x = 0}
  zero_mem' _ _ := rfl
  add_mem' ha hb x hx := by rw [Pi.add_apply, ha x hx, hb x hx, add_zero]
  neg_mem' ha x hx := by rw [Pi.neg_apply, ha x hx, neg_zero]

/-- A family lies in `supportedOn X T G W` if and only if it vanishes at every point of `T` outside
`W`. -/
@[simp]
theorem mem_supportedOn {W : Set X} {a : ∀ x : T, G x} :
    a ∈ supportedOn X T G W ↔ ∀ x : T, (x : X) ∉ W → a x = 0 := Iff.rfl

/-- A family supported on `W` and also supported on the complement of `W` is zero. -/
theorem eq_zero_of_mem_supportedOn_of_mem_supportedOn_compl {W : Set X} {a : ∀ x : T, G x}
    (ha : a ∈ supportedOn X T G W) (ha' : a ∈ supportedOn X T G Wᶜ) : a = 0 := by
  funext x
  by_cases hx : (x : X) ∈ W
  · exact ha' x (by simpa using hx)
  · exact ha x hx

/-! ### Truncation -/

open Classical in
/-- **Truncation of a locally finite family to a subset of `X`.** The components at points of
`W` are kept and all others are replaced by zero. The support only shrinks, so the result is
again locally finite. -/
noncomputable def locallyFiniteTruncate (W : Set X) :
    locallyFiniteDirectSum X T G →+ locallyFiniteDirectSum X T G where
  toFun a :=
    ⟨fun x => if (x : X) ∈ W then a.1 x else 0, fun V hV =>
      ((a.2 V hV).subset (by
        intro x hx
        refine ⟨hx.1, ?_⟩
        by_cases hxW : (x : X) ∈ W
        · simpa [hxW] using hx.2
        · simp [hxW] at hx))⟩
  map_zero' := by
    refine Subtype.ext (funext fun x => ?_)
    by_cases hxW : (x : X) ∈ W <;> simp [hxW]
  map_add' a b := by
    refine Subtype.ext (funext fun x => ?_)
    by_cases hxW : (x : X) ∈ W <;> simp [hxW]

open Classical in
/-- The component of the truncation to `W` at `x` is the component of `a` at `x` if `x ∈ W`, and
zero otherwise. -/
@[simp]
theorem locallyFiniteTruncate_apply_coe (W : Set X) (a : locallyFiniteDirectSum X T G)
    (x : T) :
    (locallyFiniteTruncate G W a).1 x = if (x : X) ∈ W then a.1 x else 0 := rfl

/-- Truncation to `W` lands in the families supported on `W`. -/
theorem locallyFiniteTruncate_mem_supportedOn (W : Set X)
    (a : locallyFiniteDirectSum X T G) :
    (locallyFiniteTruncate G W a).1 ∈ supportedOn X T G W := by
  classical
  intro x hx
  simp [hx]

/-- **Truncation to `W` and to its complement add up to the identity.** This is the splitting of
the degreewise sequence of Stacks 0GUA. -/
theorem locallyFiniteTruncate_add_compl (W : Set X) (a : locallyFiniteDirectSum X T G) :
    locallyFiniteTruncate G W a + locallyFiniteTruncate G Wᶜ a = a := by
  classical
  refine Subtype.ext (funext fun x => ?_)
  by_cases hxW : (x : X) ∈ W <;> simp [hxW]

/-- A family already supported on `W` is unchanged by truncation to `W`. -/
theorem locallyFiniteTruncate_of_mem_supportedOn (W : Set X)
    (a : locallyFiniteDirectSum X T G) (ha : a.1 ∈ supportedOn X T G W) :
    locallyFiniteTruncate G W a = a := by
  classical
  refine Subtype.ext (funext fun x => ?_)
  by_cases hxW : (x : X) ∈ W
  · simp [hxW]
  · simp [hxW, ha x hxW]

/-- Truncation is idempotent. -/
theorem locallyFiniteTruncate_idem (W : Set X) (a : locallyFiniteDirectSum X T G) :
    locallyFiniteTruncate G W (locallyFiniteTruncate G W a) =
      locallyFiniteTruncate G W a :=
  locallyFiniteTruncate_of_mem_supportedOn G W _
    (locallyFiniteTruncate_mem_supportedOn G W a)

/-! ### The split short exact sequence -/

/-- The families supported on `W`, as a subgroup of the locally finite direct sum. -/
def supportedOnSubgroup (X : Scheme.{u}) (T : Set X) (G : T → Type v)
    [∀ x, AddCommGroup (G x)] (W : Set X) :
    AddSubgroup (locallyFiniteDirectSum X T G) :=
  (supportedOn X T G W).comap (locallyFiniteDirectSum X T G).subtype

/-- An element of the locally finite direct sum lies in `supportedOnSubgroup X T G W` if and only
if its underlying family lies in `supportedOn X T G W`. -/
@[simp]
theorem mem_supportedOnSubgroup {W : Set X} {a : locallyFiniteDirectSum X T G} :
    a ∈ supportedOnSubgroup X T G W ↔ a.1 ∈ supportedOn X T G W := Iff.rfl

/-- **The families supported on `W` and those supported on its complement are complementary
subgroups of the locally finite direct sum.** Equivalently the sequence
`0 → ⨁'_{W} → ⨁'_{X} → ⨁'_{Wᶜ} → 0` is short exact and split, the splitting being truncation.
No hypothesis on `W` or on `X` is needed. -/
theorem isCompl_supportedOnSubgroup (W : Set X) :
    IsCompl (supportedOnSubgroup X T G W) (supportedOnSubgroup X T G Wᶜ) :=
  ⟨disjoint_iff_inf_le.mpr fun _ ha => AddSubgroup.mem_bot.mpr
      (Subtype.ext (eq_zero_of_mem_supportedOn_of_mem_supportedOn_compl G ha.1 ha.2)),
    codisjoint_iff_le_sup.mpr fun a _ => AddSubgroup.mem_sup.mpr
      ⟨locallyFiniteTruncate G W a, locallyFiniteTruncate_mem_supportedOn G W a,
        locallyFiniteTruncate G Wᶜ a, locallyFiniteTruncate_mem_supportedOn G Wᶜ a,
        locallyFiniteTruncate_add_compl G W a⟩⟩

/-! ### Recognising local finiteness on an open subset -/

/-- **A family supported on an open subset `U` and finite on every quasi-compact open contained
in `U` is locally finite on `X`.** For a quasi-compact open `V` of `X` the intersection
`V ∩ U` is again a quasi-compact open, by
`isCompact_inter_of_isLocallyNoetherian`, and the support of the family in `V` is already
contained in `V ∩ U`. This is the step that makes restriction to `U` surjective in the
degreewise sequence of Stacks 0GUA. -/
theorem mem_locallyFiniteDirectSum_of_subset_isOpen [IsLocallyNoetherian X] (U : X.Opens)
    {a : ∀ x : T, G x} (hsupp : a ∈ supportedOn X T G (U : Set X))
    (hfin : ∀ V : X.Opens, IsCompact (V : Set X) → (V : Set X) ⊆ (U : Set X) →
      {x : T | (x : X) ∈ (V : Set X) ∧ a x ≠ 0}.Finite) :
    a ∈ locallyFiniteDirectSum X T G := by
  intro V hV
  have hcompact : IsCompact (((V ⊓ U : X.Opens)) : Set X) :=
    isCompact_inter_of_isLocallyNoetherian V hV (U : Set X)
  have hsub : (((V ⊓ U : X.Opens)) : Set X) ⊆ (U : Set X) := Set.inter_subset_right
  exact (hfin (V ⊓ U) hcompact hsub).subset fun x hx =>
    ⟨⟨hx.1, Classical.byContradiction fun hxU => hx.2 (hsupp x hxU)⟩, hx.2⟩

end AlgebraicGeometry

end
