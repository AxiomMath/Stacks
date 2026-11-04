module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.MilnorChainLocalization
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.PointwiseMilnorBoundary
public import StacksFrontier.AlgebraicGeometry.Chow.StalkDvrMilnorBoundary
public import StacksCore.Tactic.StacksAttribute

/-!
# The arrows of Stacks 0EAY in every degree

Stacks 0EAY displays, for a Noetherian scheme `X` with a dimension function `δ`, the two arrows

`⨁_{δ(x) = j + 1} K^M_{i+1}(κ(x)) ⟶ ⨁_{δ(x) = j} K^M_i(κ(x)) ⟶ ⨁_{δ(x) = j - 1} K^M_{i-1}(κ(x))`,

built out of the tame symbols `∂_A` of the remark. At `i = 1` both arrows are already available:
`Stacks.Chow.pointwiseMilnorBoundary` and `Stacks.Chow.pointwiseDivisorDifferential`. This file
builds the first arrow **in every degree**,

`∂ : ⨁_{δ(x) = j + 1} K^M_{i+1}(κ(x)) ⟶ ⨁_{δ(x) = j} K^M_i(κ(x))`,

out of `Stacks.Chow.dvrMilnorTameSymbol'`, the tame symbol of a discrete valuation ring in every
degree.

## What is assumed, and why

**CONDITIONALLY -- the arrow built here is not an unconditional proof of Stacks 0EAY.** The
registration below carries the extra hypothesis `Stacks.Chow.HasDvrPointClosureStalks`, which the
remark's displayed sentence does not carry; the rest of this section says what that hypothesis is
and why the remark itself gives no way to remove it. The arrows of the display *at `i = 1`* are
unconditional and are registered elsewhere, on `Stacks.Chow.pointwiseMilnorBoundary` and
`Stacks.Chow.pointwiseDivisorDifferential`.

The `(x, x')` component of the arrow is the tame symbol of the local ring `𝒪_{Wₓ, x'}`, where
`Wₓ = closure {x}`. A drop of one in `δ` makes that ring a **one-dimensional Noetherian local
domain**, and no more than that. In degree `i = 1` such a ring is all the tame symbol of Section
42.5 needs, which is why `Stacks.Chow.pointwiseMilnorBoundary` is unconditional. For `i ≥ 2` the
remark constructs `∂_A` only for a **discrete valuation ring**; it extends it to an excellent
local domain of dimension one by a citation to [Kato-Milnor-K], using normalization and norm maps
on `K^M_i`, and says of an arbitrary Noetherian local domain of dimension one only that the
method of Section 42.5 can "presumably" be used.

So this file carries the hypothesis `Stacks.Chow.HasDvrPointClosureStalks`: every local ring
`𝒪_{Wₓ, x'}` that the arrow uses is a discrete valuation ring. **This is a genuine restriction on
`X`, stated plainly and not hidden** — it holds, for instance, when the integral closed
subschemes `Wₓ` are normal at the relevant points, and it fails in general. It is *not* a
stand-in for the cited theorem: no binder here has the Kato extension as its conclusion. Closing
the gap between this hypothesis and the general Noetherian case is exactly the content the remark
defers to [Kato-Milnor-K], and it is not formalized anywhere in this development.

The second arrow of the display is not built here in degree `i ≥ 2` for the same reason: its
`(x, x')` component is again a tame symbol at a one-dimensional local ring, one degree lower.

## How the arrow is built

The construction mirrors `Stacks.Chow.pointwiseMilnorBoundary` exactly, with the degree-two local
boundary `Stacks.Chow.stalkMilnorBoundary` replaced by the all-degree
`Stacks.Chow.stalkDvrMilnorBoundary`, and the degree-one transport `milnorKOneTransport` replaced
by the all-degree `milnorKTransport`. Three things are checked, as there: the local component
exists, the inner sum over the points `x` specializing to `x'` is finite, and the resulting family
of coefficients is locally finite. The last is where the general-degree input is needed, and it
comes from `Stacks.Chow.finite_stalkDvrMilnorBoundary_ne_zero`.

**Nothing here asserts that the composite with a second arrow vanishes.** The remark says the
composition being zero is not clear in general, cites [Kato-Milnor-K] for excellent `X`, and
proves it only for `i = 1` — where it is formalized as
`Stacks.Chow.pointwiseDivisorDifferential_comp_pointwiseMilnorBoundary`.

## Main definitions

* `Stacks.Chow.HasDvrPointClosureStalks` — the hypothesis above.
* `Stacks.Chow.pointClosureDvrMilnorBoundary` — the local component `∂_{𝒪_{Wₓ, x'}}` in every
  degree.
* `Stacks.Chow.milnorChainDvrBoundary` — **the first arrow of the display, in every degree**.

## Main results

* `Stacks.Chow.finite_support_milnorChainDvrBoundaryTerm` — the inner sum is finite.
* `Stacks.Chow.finite_milnorChainDvrBoundaryCoeff_ne_zero` — the family of coefficients is
  locally finite.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
* [Stacks Project, Tag 0GU2](https://stacks.math.columbia.edu/tag/0GU2)
* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]

/-! ### The hypothesis -/

/-- **The hypothesis under which the arrows of Stacks 0EAY exist in degrees above one**: every
one-dimensional local ring the arrow at level `j` uses — the local ring of `closure {x}` at `x'`,
for `x` of `δ`-dimension `j + 1` specializing to `x'` of `δ`-dimension `j` — is a discrete
valuation ring.

A drop of one in `δ` makes those rings one-dimensional Noetherian local domains and no more; the
remark constructs the higher-degree tame symbol only for discrete valuation rings, deferring the
general one-dimensional case to [Kato-Milnor-K]. This is therefore a restriction on `X`, not a
hypothesis standing in for an unproved result. -/
def HasDvrPointClosureStalks (j : ℤ) : Prop :=
  ∀ (x : pointsOfDimension C p (j + 1)) (x' : pointsOfDimension C p j)
    (h : (x.1 : X) ⤳ (x'.1 : X)),
    IsDiscreteValuationRing ↥((integralComponentAt (x.1 : X)).subscheme.presheaf.stalk
      (pointClosurePoint (x.1 : X) (specializes_iff_mem_closure.mp h)))

/-! ### The local component -/

/-- **The local component `∂_{𝒪_{Wₓ, x'}}` of the first arrow of Stacks 0EAY, in every degree.**
For `x ⇝ x'` with `𝒪_{closure {x}, x'}` a discrete valuation ring, the tame symbol of that ring
in degree `i + 1`, read through the identification of its fraction field with `κ(x)` and of its
residue field with `κ(x')`. For `i = 1` this is `Stacks.Chow.pointClosureMilnorBoundary`, which
needs only one-dimensionality. -/
def pointClosureDvrMilnorBoundary (x : X) {x' : X} (h : x' ∈ closure ({x} : Set X))
    (hdvr : IsDiscreteValuationRing ↥((integralComponentAt x).subscheme.presheaf.stalk
      (pointClosurePoint x h))) (i : ℕ) :
    MilnorKTheory ↥(X.residueField x) (i + 1) →+ MilnorKTheory ↥(X.residueField x') i :=
  (milnorKTransport (pointClosureResidueFieldEquiv x h).toRingHom i).comp
    (stalkDvrMilnorBoundary (pointClosureFunctionFieldEquiv x) (pointClosurePoint x h) hdvr i)

/-- The local component is the all-degree boundary of `closure {x}` at `x'` followed by the
transport along the identification of residue fields. -/
theorem pointClosureDvrMilnorBoundary_eq (x : X) {x' : X} (h : x' ∈ closure ({x} : Set X))
    (hdvr : IsDiscreteValuationRing ↥((integralComponentAt x).subscheme.presheaf.stalk
      (pointClosurePoint x h))) (i : ℕ) :
    pointClosureDvrMilnorBoundary x h hdvr i =
      (milnorKTransport (pointClosureResidueFieldEquiv x h).toRingHom i).comp
        (stalkDvrMilnorBoundary (pointClosureFunctionFieldEquiv x) (pointClosurePoint x h)
          hdvr i) := rfl

/-- The local component sends a class killed by the all-degree boundary of `closure {x}` to
zero: it is that boundary followed by a homomorphism. -/
theorem pointClosureDvrMilnorBoundary_eq_zero_of_stalkDvrMilnorBoundary_eq_zero (x : X) {x' : X}
    (h : x' ∈ closure ({x} : Set X))
    (hdvr : IsDiscreteValuationRing ↥((integralComponentAt x).subscheme.presheaf.stalk
      (pointClosurePoint x h))) (i : ℕ)
    (α : MilnorKTheory ↥(X.residueField x) (i + 1))
    (hα : stalkDvrMilnorBoundary (pointClosureFunctionFieldEquiv x) (pointClosurePoint x h)
      hdvr i α = 0) :
    pointClosureDvrMilnorBoundary x h hdvr i α = 0 := by
  rw [pointClosureDvrMilnorBoundary_eq, AddMonoidHom.comp_apply, hα, map_zero]

/-! ### The contribution of a single point -/

open Classical in
/-- The contribution of a point `x` of `δ`-dimension `j + 1` to the coefficient at a point `x'`
of `δ`-dimension `j`: the local component applied to the class of the chain at `x`, and zero when
`x` does not specialize to `x'`. -/
def milnorChainDvrBoundaryTerm (i : ℕ) (j : ℤ) (hdvr : HasDvrPointClosureStalks C p j)
    (ξ : MilnorChainGroup C p (j + 1) (i + 1)) (x : pointsOfDimension C p (j + 1))
    (x' : pointsOfDimension C p j) : MilnorKTheory ↥(X.residueField x'.1) i :=
  if h : (x.1 : X) ⤳ (x'.1 : X) then
    pointClosureDvrMilnorBoundary x.1 (specializes_iff_mem_closure.mp h) (hdvr x x' h) i
      (ξ.1 x)
  else 0

open Classical in
omit [LocallyOfFiniteType p] in
/-- When `x` specializes to `x'`, the contribution of `x` is the local component applied to the
class of the chain at `x`. -/
theorem milnorChainDvrBoundaryTerm_of_specializes (i : ℕ) (j : ℤ)
    (hdvr : HasDvrPointClosureStalks C p j) (ξ : MilnorChainGroup C p (j + 1) (i + 1))
    (x : pointsOfDimension C p (j + 1)) (x' : pointsOfDimension C p j)
    (h : (x.1 : X) ⤳ (x'.1 : X)) :
    milnorChainDvrBoundaryTerm C p i j hdvr ξ x x' =
      pointClosureDvrMilnorBoundary x.1 (specializes_iff_mem_closure.mp h) (hdvr x x' h) i
        (ξ.1 x) := by
  rw [milnorChainDvrBoundaryTerm]
  split
  · rfl
  · rename_i hno
    exact absurd h hno

open Classical in
omit [LocallyOfFiniteType p] in
/-- When `x` does not specialize to `x'`, the contribution of `x` is zero. -/
theorem milnorChainDvrBoundaryTerm_of_not_specializes (i : ℕ) (j : ℤ)
    (hdvr : HasDvrPointClosureStalks C p j) (ξ : MilnorChainGroup C p (j + 1) (i + 1))
    (x : pointsOfDimension C p (j + 1)) (x' : pointsOfDimension C p j)
    (h : ¬(x.1 : X) ⤳ (x'.1 : X)) :
    milnorChainDvrBoundaryTerm C p i j hdvr ξ x x' = 0 := by
  rw [milnorChainDvrBoundaryTerm]
  split
  · rename_i hspec
    exact absurd hspec h
  · rfl

open Classical in
omit [LocallyOfFiniteType p] in
/-- Where the chain vanishes, the point contributes nothing. -/
theorem milnorChainDvrBoundaryTerm_of_eq_zero (i : ℕ) (j : ℤ)
    (hdvr : HasDvrPointClosureStalks C p j) (ξ : MilnorChainGroup C p (j + 1) (i + 1))
    {x : pointsOfDimension C p (j + 1)} (hx : ξ.1 x = 0) (x' : pointsOfDimension C p j) :
    milnorChainDvrBoundaryTerm C p i j hdvr ξ x x' = 0 := by
  rw [milnorChainDvrBoundaryTerm]
  split
  · rw [hx, map_zero]
  · rfl

open Classical in
omit [LocallyOfFiniteType p] in
/-- The contribution of a point is additive in the chain. -/
theorem milnorChainDvrBoundaryTerm_add (i : ℕ) (j : ℤ) (hdvr : HasDvrPointClosureStalks C p j)
    (ξ η : MilnorChainGroup C p (j + 1) (i + 1)) (x : pointsOfDimension C p (j + 1))
    (x' : pointsOfDimension C p j) :
    milnorChainDvrBoundaryTerm C p i j hdvr (ξ + η) x x' =
      milnorChainDvrBoundaryTerm C p i j hdvr ξ x x' +
        milnorChainDvrBoundaryTerm C p i j hdvr η x x' := by
  rw [milnorChainDvrBoundaryTerm, milnorChainDvrBoundaryTerm, milnorChainDvrBoundaryTerm]
  split
  · rw [show (ξ + η).1 x = ξ.1 x + η.1 x from rfl, map_add]
  · rw [add_zero]

omit [LocallyOfFiniteType p] in
/-- **The inner sum is finite.** Only finitely many points of `δ`-dimension `j + 1` contribute to
the coefficient at a fixed `x'`: such a point carries a nonzero class of the chain and
specializes to `x'`, and the closures of the points carrying the chain are locally finite. -/
theorem finite_support_milnorChainDvrBoundaryTerm (i : ℕ) (j : ℤ)
    (hdvr : HasDvrPointClosureStalks C p j) (ξ : MilnorChainGroup C p (j + 1) (i + 1))
    (x' : pointsOfDimension C p j) :
    (Function.support fun x : pointsOfDimension C p (j + 1) ↦
      milnorChainDvrBoundaryTerm C p i j hdvr ξ x x').Finite := by
  obtain ⟨t, ht, hfin⟩ :=
    locallyFinite_closure_milnorChainSupport C p (j + 1) (i + 1) ξ x'.1
  refine (Set.Finite.image
    (fun q : {x : pointsOfDimension C p (j + 1) // ξ.1 x ≠ 0} ↦ q.1) hfin).subset ?_
  intro x hx
  have hax : ξ.1 x ≠ 0 := fun h ↦
    hx (milnorChainDvrBoundaryTerm_of_eq_zero C p i j hdvr ξ h x')
  have hspec : (x.1 : X) ⤳ (x'.1 : X) := by
    by_contra hnot
    exact hx (milnorChainDvrBoundaryTerm_of_not_specializes C p i j hdvr ξ x x' hnot)
  exact ⟨⟨x, hax⟩, ⟨x'.1, specializes_iff_mem_closure.mp hspec, mem_of_mem_nhds ht⟩, rfl⟩

/-! ### The coefficient -/

/-- The coefficient at `x'` of the first arrow of Stacks 0EAY in degree `i + 1`: the locally
finite sum, over the points `x` of `δ`-dimension `j + 1`, of the local tame-symbol boundaries of
the classes of the chain. -/
def milnorChainDvrBoundaryCoeff (i : ℕ) (j : ℤ) (hdvr : HasDvrPointClosureStalks C p j)
    (ξ : MilnorChainGroup C p (j + 1) (i + 1)) (x' : pointsOfDimension C p j) :
    MilnorKTheory ↥(X.residueField x'.1) i :=
  ∑ᶠ x : pointsOfDimension C p (j + 1), milnorChainDvrBoundaryTerm C p i j hdvr ξ x x'

omit [LocallyOfFiniteType p] in
/-- The coefficient is additive in the chain. -/
theorem milnorChainDvrBoundaryCoeff_add (i : ℕ) (j : ℤ) (hdvr : HasDvrPointClosureStalks C p j)
    (ξ η : MilnorChainGroup C p (j + 1) (i + 1)) (x' : pointsOfDimension C p j) :
    milnorChainDvrBoundaryCoeff C p i j hdvr (ξ + η) x' =
      milnorChainDvrBoundaryCoeff C p i j hdvr ξ x' +
        milnorChainDvrBoundaryCoeff C p i j hdvr η x' := by
  rw [milnorChainDvrBoundaryCoeff, milnorChainDvrBoundaryCoeff, milnorChainDvrBoundaryCoeff,
    ← finsum_add_distrib (finite_support_milnorChainDvrBoundaryTerm C p i j hdvr ξ x')
      (finite_support_milnorChainDvrBoundaryTerm C p i j hdvr η x')]
  exact finsum_congr fun x ↦ milnorChainDvrBoundaryTerm_add C p i j hdvr ξ η x x'

omit [LocallyOfFiniteType p] in
/-- The coefficient of the zero chain vanishes. -/
theorem milnorChainDvrBoundaryCoeff_zero (i : ℕ) (j : ℤ)
    (hdvr : HasDvrPointClosureStalks C p j) (x' : pointsOfDimension C p j) :
    milnorChainDvrBoundaryCoeff C p i j hdvr 0 x' = 0 := by
  rw [milnorChainDvrBoundaryCoeff,
    finsum_congr fun x ↦ milnorChainDvrBoundaryTerm_of_eq_zero C p i j hdvr 0 (rfl) x']
  exact finsum_zero

/-! ### Local finiteness -/

/-- **A single point contributes at only finitely many points of a quasi-compact open.** The
intersection of `U` with `closure {x}` is a quasi-compact open of the integral locally Noetherian
scheme `closure {x}`, so `Stacks.Chow.finite_stalkDvrMilnorBoundary_ne_zero` applies there. -/
theorem finite_milnorChainDvrBoundaryTerm_ne_zero (i : ℕ) (j : ℤ)
    (hdvr : HasDvrPointClosureStalks C p j) (ξ : MilnorChainGroup C p (j + 1) (i + 1))
    (x : pointsOfDimension C p (j + 1)) (U : X.Opens) (hU : IsCompact (U : Set X)) :
    {x' : pointsOfDimension C p j | (x'.1 : X) ∈ (U : Set X) ∧
      milnorChainDvrBoundaryTerm C p i j hdvr ξ x x' ≠ 0}.Finite := by
  classical
  let _ : IsLocallyNoetherian (integralComponentAt x.1).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt x.1).subschemeι ≫ p)
  have hVcompact : IsCompact ((((integralComponentAt x.1).subschemeι ⁻¹ᵁ U) :
      Set (integralComponentAt x.1).subscheme) : Set (integralComponentAt x.1).subscheme) :=
    ((integralComponentAt x.1).subschemeι.isClosedEmbedding.isInducing.isCompact_preimage
      (integralComponentAt x.1).subschemeι.isClosedEmbedding.isClosed_range hU)
  have hfin := finite_stalkDvrMilnorBoundary_ne_zero (pointClosureFunctionFieldEquiv x.1)
    ((integralComponentAt x.1).subschemeι ⁻¹ᵁ U) hVcompact i (ξ.1 x)
  refine Set.Finite.of_finite_image (f := fun x' : pointsOfDimension C p j ↦ (x'.1 : X))
    ((hfin.image fun z ↦ ((integralComponentAt x.1).subschemeι z.1 : X)).subset ?_)
    (Set.injOn_of_injective Subtype.val_injective)
  rintro _ ⟨x', ⟨hx'U, hx'ne⟩, rfl⟩
  by_cases hspec : (x.1 : X) ⤳ (x'.1 : X)
  · have hmem : (x'.1 : X) ∈ closure ({(x.1 : X)} : Set X) := specializes_iff_mem_closure.mp hspec
    refine ⟨⟨pointClosurePoint x.1 hmem, hdvr x x' hspec⟩, ⟨?_, ?_⟩,
      subschemeι_pointClosurePoint x.1 hmem⟩
    · show (integralComponentAt x.1).subschemeι (pointClosurePoint x.1 hmem) ∈ (U : Set X)
      rw [subschemeι_pointClosurePoint x.1 hmem]
      exact hx'U
    · intro hzero
      refine hx'ne ?_
      rw [milnorChainDvrBoundaryTerm_of_specializes C p i j hdvr ξ x x' hspec]
      exact pointClosureDvrMilnorBoundary_eq_zero_of_stalkDvrMilnorBoundary_eq_zero x.1 hmem
        (hdvr x x' hspec) i (ξ.1 x) hzero
  · exact absurd (milnorChainDvrBoundaryTerm_of_not_specializes C p i j hdvr ξ x x' hspec) hx'ne

/-- **The family of coefficients is locally finite.** On a quasi-compact open `U` only finitely
many points of `δ`-dimension `j` carry a nonzero coefficient: only the finitely many points `x`
of `U` of `δ`-dimension `j + 1` at which the chain is nonzero can contribute, and each of them
contributes at only finitely many points of `U`. -/
theorem finite_milnorChainDvrBoundaryCoeff_ne_zero (i : ℕ) (j : ℤ)
    (hdvr : HasDvrPointClosureStalks C p j) (ξ : MilnorChainGroup C p (j + 1) (i + 1))
    (U : X.Opens) (hU : IsCompact (U : Set X)) :
    {x' : pointsOfDimension C p j | (x'.1 : X) ∈ (U : Set X) ∧
      milnorChainDvrBoundaryCoeff C p i j hdvr ξ x' ≠ 0}.Finite := by
  classical
  have hF : {x : pointsOfDimension C p (j + 1) | (x.1 : X) ∈ (U : Set X) ∧
      ξ.1 x ≠ 0}.Finite := ξ.2 U hU
  refine (hF.biUnion
    (fun x _ ↦ finite_milnorChainDvrBoundaryTerm_ne_zero C p i j hdvr ξ x U hU)).subset ?_
  rintro x' ⟨hx'U, hx'ne⟩
  have hsupp : ∃ x : pointsOfDimension C p (j + 1),
      milnorChainDvrBoundaryTerm C p i j hdvr ξ x x' ≠ 0 := by
    by_contra hall
    refine hx'ne ?_
    rw [milnorChainDvrBoundaryCoeff,
      finsum_congr fun x ↦ not_not.mp fun hne ↦ hall ⟨x, hne⟩]
    exact finsum_zero
  obtain ⟨x, hx⟩ := hsupp
  have hax : ξ.1 x ≠ 0 := fun h ↦
    hx (milnorChainDvrBoundaryTerm_of_eq_zero C p i j hdvr ξ h x')
  have hspec : (x.1 : X) ⤳ (x'.1 : X) := by
    by_contra hnot
    exact hx (milnorChainDvrBoundaryTerm_of_not_specializes C p i j hdvr ξ x x' hnot)
  have hxU : (x.1 : X) ∈ (U : Set X) := by
    obtain ⟨v, hvU, hv⟩ := mem_closure_iff.mp (specializes_iff_mem_closure.mp hspec)
      (U : Set X) U.2 hx'U
    rw [← Set.mem_singleton_iff.mp hv]
    exact hvU
  exact Set.mem_biUnion (show x ∈ {y : pointsOfDimension C p (j + 1) | (y.1 : X) ∈ (U : Set X) ∧
    ξ.1 y ≠ 0} from ⟨hxU, hax⟩) (show x' ∈ {y' : pointsOfDimension C p j |
      (y'.1 : X) ∈ (U : Set X) ∧
      milnorChainDvrBoundaryTerm C p i j hdvr ξ x y' ≠ 0} from ⟨hx'U, hx⟩)

/-! ### The arrow -/

/-- **The first arrow of the display of Stacks 0EAY at discrete-valuation stalks.** For a
Noetherian scheme `X` with a dimension function `δ`, the homomorphism

`⨁_{δ(x) = j + 1} K^M_{i+1}(κ(x)) ⟶ ⨁_{δ(x) = j} K^M_i(κ(x))`

whose coefficient at `x'` is the sum, over the points `x` of `δ`-dimension `j + 1` specializing
to `x'`, of the tame symbols `∂_{𝒪_{closure {x}, x'}}` of the classes of the chain. Both the
finiteness of that sum and the local finiteness of the resulting family are proved, so the rule
is a well defined additive map.

This is the special case in which every one-dimensional local ring `𝒪_{closure {x}, x'}` the arrow
uses is a discrete valuation ring (`Stacks.Chow.HasDvrPointClosureStalks`). The arrow of the remark
for an arbitrary Noetherian scheme, built from the tame symbol of a one-dimensional Noetherian
local domain by normalization and norm, is `Stacks.Chow.milnorChainBoundary`. At `i = 1` the
arrow of the remark built from the tame symbol of Stacks 02Q1 is
`Stacks.Chow.pointwiseMilnorBoundary`. -/
def milnorChainDvrBoundary (i : ℕ) (j : ℤ) (hdvr : HasDvrPointClosureStalks C p j) :
    MilnorChainGroup C p (j + 1) (i + 1) →+ MilnorChainGroup C p j i where
  toFun ξ := ⟨fun x' ↦ milnorChainDvrBoundaryCoeff C p i j hdvr ξ x', fun U hU ↦
    finite_milnorChainDvrBoundaryCoeff_ne_zero C p i j hdvr ξ U hU⟩
  map_zero' := Subtype.ext (funext fun x' ↦ milnorChainDvrBoundaryCoeff_zero C p i j hdvr x')
  map_add' ξ η := Subtype.ext (funext fun x' ↦
    milnorChainDvrBoundaryCoeff_add C p i j hdvr ξ η x')

/-- The value of the arrow at `x'` is the coefficient at `x'`. -/
@[simp]
theorem milnorChainDvrBoundary_apply (i : ℕ) (j : ℤ) (hdvr : HasDvrPointClosureStalks C p j)
    (ξ : MilnorChainGroup C p (j + 1) (i + 1)) (x' : pointsOfDimension C p j) :
    (milnorChainDvrBoundary C p i j hdvr ξ).1 x' =
      milnorChainDvrBoundaryCoeff C p i j hdvr ξ x' := rfl

end Stacks.Chow

end
