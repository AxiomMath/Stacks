module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.NoetherianSpace
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The local ring at a point of delta-dimension `k` on a scheme of delta-dimension `k + 1`

Let `C = (S, δ)` be a Chow situation, let `f : X ⟶ C.S` be locally of finite type with
`dim_δ(X) ≤ k + 1`, and let `ξ` be a point of `X` with `δ(ξ) = k`. The dimension function of
[Stacks, Tag 02JW] drops strictly along every proper specialization, so a proper generization
of `ξ` already has delta-dimension `k + 1`, which is the maximum, and therefore has no proper
generization of its own. Hence the coheight of `ξ` — the length of the longest chain of
generizations starting at `ξ`, which by [Stacks, Tag 02IZ] is the Krull dimension of the local
ring `𝒪_{X, ξ}` — is at most one, and is exactly one as soon as `ξ` has a proper generization
at all.

This is the input that makes the length formula of [Stacks, Tag 02QH]
(`Ideal.length_fractionalProduct_quotient_sub_length_denominator_quotient`, stated for a
one-dimensional Noetherian local ring) applicable at `𝒪_{X, ξ}`.

## Main results

* `Stacks.Chow.StalkLocalSituation.relativeDimension_le_of_schemeDeltaDimension_le`: on a
  scheme of delta-dimension at most `n`, *every* point has relative dimension at most `n`, not
  just the generic points of the irreducible components.
* `Stacks.Chow.StalkLocalSituation.coheight_le_one` and
  `Stacks.Chow.StalkLocalSituation.ringKrullDim_stalk_le_one`: the upper bound, which needs
  only `dim_δ(X) ≤ k + 1` and `δ(ξ) = k`.
* `Stacks.Chow.StalkLocalSituation.coheight_eq_one` and
  `Stacks.Chow.StalkLocalSituation.ringKrullDim_stalk_eq_one`: the exact value, for a `ξ` that
  is not maximal for the specialization order.
* `Stacks.Chow.StalkLocalSituation.not_subset_of_mem_irreducibleComponents_of_isNowhereDense`
  and `Stacks.Chow.StalkLocalSituation.not_isMax_of_mem_of_isNowhereDense`: a point of a closed
  nowhere dense subset of a locally Noetherian scheme is never maximal, which is how the
  non-maximality hypothesis is discharged in practice.
* `Stacks.Chow.StalkLocalSituation.ringKrullDim_stalk_eq_one_of_mem_isNowhereDense`: the two
  combined, with purely geometric hypotheses.

## Implementation notes

The order on the points of a scheme is the specialization order of
`TopologicalSpace.specializationOrder`, in which `x ≤ y` means `y ⤳ x`: larger means more
generic, the generic point of an irreducible scheme is the top element, and `Order.coheight`
measures chains of generizations. That is the convention under which
`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight` holds, and `IsMax ξ` says exactly that `ξ`
is the generic point of an irreducible component of `X`.

Non-maximality is a genuine extra hypothesis, not an artefact: on the disjoint union of a
`k`-dimensional and a `(k+1)`-dimensional integral scheme the generic point of the first
component has `δ = k` while its local ring is a field, and the scheme has no embedded points.
What rules this out in [Stacks, Tag 02SW] is that the points contributing to the identity of
its part (4) lie in the closed nowhere dense exceptional subset of [Stacks, Tag 02P2]; that is
the shape in which `ringKrullDim_stalk_eq_one_of_mem_isNowhereDense` takes the hypothesis.

Only the locally Noetherian hypothesis is used for the nowhere-dense statements, through an
affine open neighbourhood, which is a Noetherian space and in which an irreducible component
therefore contains a nonempty open set ([Stacks, Tag 0052 (3)]).

## References

* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 02QH](https://stacks.math.columbia.edu/tag/02QH)
* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 0052](https://stacks.math.columbia.edu/tag/0052)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Topology TopologicalSpace

universe u

namespace Stacks.Chow.StalkLocalSituation

/-! ### The delta-dimension bounds every point, not only the generic ones -/

/-- Every point of a scheme lies on an irreducible component, together with its generic point. -/
private theorem exists_mem_irreducibleComponents_isGenericPoint {X : Scheme.{u}} (y : X) :
    ∃ (W : Set X) (hW : W ∈ irreducibleComponents X),
      y ∈ W ∧ IsGenericPoint hW.1.genericPoint W := by
  obtain ⟨W, hW, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({y} : Set X)) isIrreducible_singleton.closure
  exact ⟨W, hW, hsub (subset_closure rfl),
    hW.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents W hW)⟩

/-- The relative dimension strictly increases along a proper generization `a ≤ b`. -/
private theorem relativeDimension_lt_of_lt (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] {a b : X} (h : a ≤ b) (hne : b ≠ a) :
    relativeDimension C.dimensionFunction f a < relativeDimension C.dimensionFunction f b := by
  obtain ⟨d, hd⟩ :=
    relativeDimension_isDimensionFunction C.isUniversallyCatenary C.dimensionFunction f
  rw [← hd a, ← hd b]
  exact d.strictAnti_specializes h hne

/-- **Every point of a scheme of delta-dimension at most `n` has relative dimension at most
`n`.** The point lies on an irreducible component, whose generic point has relative dimension at
most `n` by the definition of `Stacks.Chow.schemeDeltaDimension` as a supremum, and the
dimension function of [Stacks, Tag 02JW] does not increase along the specialization from that
generic point. -/
theorem relativeDimension_le_of_schemeDeltaDimension_le (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] {n : ℤ}
    (hdim : schemeDeltaDimension C f ≤ (n : EInt)) (y : X) :
    relativeDimension C.dimensionFunction f y ≤ n := by
  obtain ⟨W, hW, hyW, hgen⟩ := exists_mem_irreducibleComponents_isGenericPoint y
  have hWle : relativeDimension C.dimensionFunction f hW.1.genericPoint ≤ n := by
    rw [schemeDeltaDimension_eq_iSup] at hdim
    have hle := WithBotTop.coe_le_coe.mp ((le_iSup
      (fun V : irreducibleComponents X => (deltaDimension C f ⟨(V : Set X), V.2.1,
        isClosed_of_mem_irreducibleComponents (V : Set X) V.2⟩ : EInt))
      (⟨W, hW⟩ : irreducibleComponents X)).trans hdim)
    rwa [deltaDimension_eq_of_isGenericPoint C f _ _ hgen] at hle
  by_cases hy : hW.1.genericPoint = y
  · exact hy ▸ hWle
  · have := relativeDimension_lt_of_lt C f
      (hgen.specializes hyW) hy
    omega

/-! ### The coheight of a point of delta-dimension `k` -/

/-- **A proper generization of a point of delta-dimension `k` on a scheme of delta-dimension at
most `k + 1` is maximal.** Its relative dimension is at least `k + 1` because the dimension
function drops strictly along the specialization, and at most `k + 1` by the bound on the
scheme, so it cannot itself have a proper generization. -/
theorem isMax_of_lt_of_relativeDimension_eq (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt)) {ξ y : X}
    (hξ : relativeDimension C.dimensionFunction f ξ = k) (hy : ξ < y) :
    IsMax y := by
  have hbound : ∀ z : X, relativeDimension C.dimensionFunction f z ≤ k + 1 := fun z =>
    relativeDimension_le_of_schemeDeltaDimension_le C f hdim z
  have hyval : relativeDimension C.dimensionFunction f y = k + 1 := by
    have := relativeDimension_lt_of_lt C f hy.le hy.ne'
    have := hbound y
    omega
  intro z hz
  by_cases hzy : z ≤ y
  · exact hzy
  · have hlt : y < z := lt_iff_le_not_ge.mpr ⟨hz, hzy⟩
    have := relativeDimension_lt_of_lt C f hlt.le hlt.ne'
    have := hbound z
    omega

/-- **The coheight of a point of delta-dimension `k` on a scheme of delta-dimension at most
`k + 1` is at most one.** -/
theorem coheight_le_one (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt)) {ξ : X}
    (hξ : relativeDimension C.dimensionFunction f ξ = k) :
    Order.coheight ξ ≤ 1 := by
  rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, Order.coheight_le_coe_iff]
  intro y hy
  rw [Order.coheight_eq_zero.mpr (isMax_of_lt_of_relativeDimension_eq C f hdim hξ hy)]
  exact Nat.cast_pos.mpr Nat.one_pos

/-- **The Krull dimension of the local ring at a point of delta-dimension `k` on a scheme of
delta-dimension at most `k + 1` is at most one.** -/
theorem ringKrullDim_stalk_le_one (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt)) {ξ : X}
    (hξ : relativeDimension C.dimensionFunction f ξ = k) :
    ringKrullDim (X.presheaf.stalk ξ) ≤ 1 := by
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight]
  exact WithBot.coe_le_coe.mpr (coheight_le_one C f hdim hξ)

/-- **The coheight of a non-maximal point of delta-dimension `k` on a scheme of delta-dimension
at most `k + 1` is exactly one.** -/
theorem coheight_eq_one (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt)) {ξ : X}
    (hξ : relativeDimension C.dimensionFunction f ξ = k) (hmax : ¬ IsMax ξ) :
    Order.coheight ξ = 1 :=
  le_antisymm (coheight_le_one C f hdim hξ)
    (Order.one_le_iff_ne_zero.mpr (Order.coheight_ne_zero.mpr hmax))

/-- **The local ring at a non-maximal point of delta-dimension `k` on a scheme of
delta-dimension at most `k + 1` has Krull dimension one.** This is the hypothesis `dim R = 1`
of the length formula of [Stacks, Tag 02QH]. -/
theorem ringKrullDim_stalk_eq_one (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt)) {ξ : X}
    (hξ : relativeDimension C.dimensionFunction f ξ = k) (hmax : ¬ IsMax ξ) :
    ringKrullDim (X.presheaf.stalk ξ) = 1 := by
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, coheight_eq_one C f hdim hξ hmax]
  rfl

/-! ### Non-maximality from a closed nowhere dense subset -/

/-- **An irreducible component of a locally Noetherian scheme is not contained in a closed
nowhere dense subset.** An affine open neighbourhood of a point of the component is a Noetherian
space, in which the component meets it in an irreducible component, and an irreducible component
of a Noetherian space contains a nonempty open subset ([Stacks, Tag 0052 (3)]); its image is a
nonempty open subset of the ambient scheme inside the nowhere dense set. -/
@[ega "I 7.2.8.1" "parenthetical clause"]
theorem not_subset_of_mem_irreducibleComponents_of_isNowhereDense (X : Scheme.{u})
    [IsLocallyNoetherian X] {Z T : Set X} (hZ : Z ∈ irreducibleComponents X) (hT : IsClosed T)
    (hT' : IsNowhereDense T) : ¬ Z ⊆ T := by
  intro hZT
  obtain ⟨z, hz⟩ := hZ.1.nonempty
  obtain ⟨U, hU, hzU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := z) (U := ⊤) (by trivial)
  have : IsAffine U.toScheme := hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : NoetherianSpace U := noetherianSpace_of_isAffineOpen U hU
  have hZU : Subtype.val ⁻¹' Z ∈ irreducibleComponents U :=
    preimage_mem_irreducibleComponents hZ U.isOpenEmbedding ⟨z, hz, ⟨⟨z, hzU⟩, rfl⟩⟩
  obtain ⟨V, hV, hVne, hVZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hZU
  have hVT : Subtype.val '' V ⊆ T := by
    rintro _ ⟨y, hy, rfl⟩
    exact hZT (hVZ hy)
  have hVi : Subtype.val '' V ⊆ interior T :=
    interior_maximal hVT (U.isOpenEmbedding.isOpenMap _ hV)
  rw [hT.isNowhereDense_iff.mp hT'] at hVi
  exact (hVne.image Subtype.val).ne_empty (Set.eq_empty_of_subset_empty hVi)

/-- **A point of a closed nowhere dense subset of a locally Noetherian scheme is not maximal for
the specialization order**, that is, it is a proper specialization of some point. Were it
maximal, the closure of the point would be an irreducible component contained in the nowhere
dense subset. -/
theorem not_isMax_of_mem_of_isNowhereDense (X : Scheme.{u}) [IsLocallyNoetherian X] {T : Set X}
    (hT : IsClosed T) (hT' : IsNowhereDense T) {ξ : X} (hξ : ξ ∈ T) : ¬ IsMax ξ := by
  intro hmax
  obtain ⟨W, hW, hξW, hgen⟩ := exists_mem_irreducibleComponents_isGenericPoint ξ
  refine not_subset_of_mem_irreducibleComponents_of_isNowhereDense X hW hT hT' ?_
  have hle : ξ ≤ hW.1.genericPoint := hgen.specializes hξW
  have heq : hW.1.genericPoint = ξ := (Specializes.antisymm hle (hmax hle)).eq
  rw [← hgen, heq]
  exact hT.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hξ)

/-- **The local ring at a point of delta-dimension `k` lying in a closed nowhere dense subset of
a scheme of delta-dimension at most `k + 1` has Krull dimension one.** All the hypotheses are
geometric: the bound on the delta-dimension, the value of the dimension function at the point,
and the nowhere dense closed subset containing it. -/
theorem ringKrullDim_stalk_eq_one_of_mem_isNowhereDense (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsLocallyNoetherian X] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt)) {T : Set X} (hT : IsClosed T)
    (hT' : IsNowhereDense T) {ξ : X} (hξT : ξ ∈ T)
    (hξ : relativeDimension C.dimensionFunction f ξ = k) :
    ringKrullDim (X.presheaf.stalk ξ) = 1 :=
  ringKrullDim_stalk_eq_one C f hdim hξ (not_isMax_of_mem_of_isNowhereDense X hT hT' hξT)

end Stacks.Chow.StalkLocalSituation

end
