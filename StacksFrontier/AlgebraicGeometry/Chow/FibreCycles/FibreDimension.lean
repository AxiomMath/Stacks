module

public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.StalkDimension
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.MinimalSupport
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The two dimension hypotheses of the local comparison, read off the geometry

The local comparison of multiplicities underlying Stacks Tag 02S5,
`Stacks.Chow.length_quotient_span_sup_eq_sum_minimalPrimes_of_notMem_associatedPrimes`, carries
two hypotheses on Krull dimensions in the local ring `A = 𝒪_{X ×_S 𝐏¹_S, ξ}`: that `A/(t, I)`
has dimension at most zero, and that `A/I` has dimension exactly one, for `I` the stalk of the
ideal sheaf of a closed subscheme `Z` and `t` a local equation of a section.
`StacksFrontier/AlgebraicGeometry/Chow/FibreCycles/StalkDimension.lean` identified both quotients
with local rings of schemes; this file discharges the two resulting bounds from the hypotheses
that Tag 02S5 actually supplies.

The first bound is free at a generic point of the fibre: a generic point of an irreducible
component is maximal in the specialization order, so its coheight — and therefore the Krull
dimension of the local ring there — is zero.

The second is the substantive one. Let `ξ` be a point of `Z` lying over a generic point of the
zero (or infinity) fibre at which the relative dimension of Stacks 02JW equals `k`. The upper
bound `dim 𝒪_{Z,ξ} ≤ 1` comes from the delta-dimension hypothesis of the tag: the relative
dimension strictly increases along strict generalization, and it is capped at `k + 1`, so no
point of `Z` admits a chain of two strict generalizations above `ξ`. The lower bound
`dim 𝒪_{Z,ξ} ≥ 1` says that `ξ` is not the generic point of a component of `Z`, and this is
where the hypothesis on associated points enters: were `ξ` such a generic point it would be an
associated point of `Z`, while `ξ` lies on a section and has relative dimension `k`, so both
alternatives offered for an associated point fail.

## Main results

* `Stacks.Chow.isMax_of_mem_genericPoints` and `Stacks.Chow.mem_genericPoints_of_isMax` — on a
  scheme, being a generic point of an irreducible component is the same as being maximal for
  the specialization order.
* `Stacks.Chow.ringKrullDim_stalk_eq_zero_of_mem_genericPoints` — the local ring of a scheme at
  a generic point of an irreducible component has Krull dimension zero.
* `Stacks.Chow.exists_localEquation_ringKrullDim_quotient_le_zero_zeroFiber` and
  `Stacks.Chow.exists_localEquation_ringKrullDim_quotient_le_zero_infinityFiber` — the first
  dimension hypothesis of the local comparison, at a generic point of the fibre.
* `Stacks.Chow.ringKrullDim_stalk_subscheme_eq_one` and
  `Stacks.Chow.ringKrullDim_quotient_idealStalk_eq_one` — the second dimension hypothesis of
  the local comparison, from the delta-dimension and associated-point hypotheses of Tag 02S5.

## Implementation notes

The specialization preorder on the points of a scheme has `x ≤ y` iff `y ⤳ x`, so `IsMax x`
says that every generalization of `x` is a specialization of it, and `Order.coheight x` is the
codimension of `closure {x}`. The bridge to Krull dimension is Mathlib's
`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`.

The order-theoretic heart of the upper bound is isolated as a statement about an arbitrary
integer-valued function that is strictly monotone for the ambient preorder and bounded above by
`k + 1`; it needs nothing about schemes, and in particular it does not need the second clause of
a `TopologicalSpace.DimensionFunction`. The dimension function of Stacks 02JW enters only
through `Stacks.Chow.deltaDimensionFunction`, whose `strictAnti_specializes` field supplies the
monotonicity, and whose existence is what forces the `LocallyOfFiniteType` hypothesis.

The hypothesis on associated points is taken in the form the tag's statement gives it, as the
disjunction "`ξ` avoids both sections, or the relative dimension at `ξ` drops below `k`",
instantiated at the single point under consideration. Note that the tag's own statement
quantifies that hypothesis over embedded points, which is not enough: for `S = X = Spec k`,
`δ = 0`, `k = 0` and `Z` the origin of `𝐏¹_k`, the subscheme `Z` has no embedded point at all
and the conclusion of the tag fails. Quantifying over associated points is the repair, and it
is exactly what the lower bound here consumes.

## References

* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 05AH](https://stacks.math.columbia.edu/tag/05AH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Generic points of irreducible components and the specialization order -/

/-- A generic point of an irreducible component of a scheme is maximal for the specialization
order: any point of which it is a specialization is equal to it. -/
theorem isMax_of_mem_genericPoints {W : Scheme.{u}} (y : genericPoints W) : IsMax y.1 :=
  fun _ hb ↦ le_of_eq (Topology.eq_of_specializes_isGenericPoint y.2
    (genericPoints.isGenericPoint y) hb)

/-- Conversely, a point of a scheme that is maximal for the specialization order is a generic
point of an irreducible component: its closure is forced to be the whole of the irreducible
component containing it. -/
theorem mem_genericPoints_of_isMax {W : Scheme.{u}} {x : W} (hx : IsMax x) :
    x ∈ genericPoints W := by
  let c : irreducibleComponents W :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  have hbx : (genericPoints.ofComponent c).1 ⤳ x :=
    (genericPoints.isGenericPoint_ofComponent c).specializes mem_irreducibleComponent
  rw [(Specializes.antisymm (hx hbx) hbx).eq]
  exact (genericPoints.ofComponent c).2

/-- The local ring of a scheme at a generic point of an irreducible component has Krull
dimension zero: such a point is maximal for the specialization order, so its coheight
vanishes. -/
@[ega "I 2.4.3" "partial"]
theorem ringKrullDim_stalk_eq_zero_of_mem_genericPoints {W : Scheme.{u}}
    (y : genericPoints W) : ringKrullDim (W.presheaf.stalk y.1) = 0 := by
  rw [ringKrullDim_stalk_eq_coheight, Order.coheight_eq_zero.mpr (isMax_of_mem_genericPoints y)]
  rfl

/-! ### The first dimension hypothesis, at a generic point of the fibre -/

/-- If a family of dimensions contains the Krull dimension of the local ring at a generic point of
an irreducible component, then it contains a value at most zero. -/
private lemma exists_le_zero_of_exists_eq_stalk {W : Scheme.{u}} (y : genericPoints W) {ι : Type*}
    {d : ι → WithBot ℕ∞} (h : ∃ t, d t = ringKrullDim (W.presheaf.stalk y.1)) : ∃ t, d t ≤ 0 :=
  h.imp fun _ ht ↦ by rw [ht, ringKrullDim_stalk_eq_zero_of_mem_genericPoints y]

/-- At a generic point of an irreducible component of the zero fibre, the quotient of the local
ring of `X ×_S 𝐏¹_S` by a local equation of the zero section together with the stalk of the
ideal sheaf of `Z` has Krull dimension at most zero.

This is the hypothesis `hx` of
`Stacks.Chow.length_quotient_span_sup_eq_sum_minimalPrimes_of_notMem_associatedPrimes`, for the
zero section. -/
theorem exists_localEquation_ringKrullDim_quotient_le_zero_zeroFiber
    {X S : Scheme.{u}} (f : X ⟶ S) (Z : (projectiveLineProduct f).IdealSheafData)
    (y : genericPoints (zeroFiber f Z).subscheme) :
    ∃ t : (projectiveLineProduct f).presheaf.stalk
        (zeroSection f ((zeroFiber f Z).subschemeι y.1)),
      ringKrullDim ((projectiveLineProduct f).presheaf.stalk
            (zeroSection f ((zeroFiber f Z).subschemeι y.1)) ⧸
          (Ideal.span {t} ⊔
            IdealSheafData.stalk Z (zeroSection f ((zeroFiber f Z).subschemeι y.1)))) ≤ 0 :=
  exists_le_zero_of_exists_eq_stalk y
    (exists_localEquation_ringKrullDim_quotient_eq_zeroFiber f Z y.1)

/-- At a generic point of an irreducible component of the infinity fibre, the quotient of the
local ring of `X ×_S 𝐏¹_S` by a local equation of the infinity section together with the stalk
of the ideal sheaf of `Z` has Krull dimension at most zero.

This is the hypothesis `hx` of
`Stacks.Chow.length_quotient_span_sup_eq_sum_minimalPrimes_of_notMem_associatedPrimes`, for the
infinity section. -/
theorem exists_localEquation_ringKrullDim_quotient_le_zero_infinityFiber
    {X S : Scheme.{u}} (f : X ⟶ S) (Z : (projectiveLineProduct f).IdealSheafData)
    (y : genericPoints (infinityFiber f Z).subscheme) :
    ∃ t : (projectiveLineProduct f).presheaf.stalk
        (infinitySection f ((infinityFiber f Z).subschemeι y.1)),
      ringKrullDim ((projectiveLineProduct f).presheaf.stalk
            (infinitySection f ((infinityFiber f Z).subschemeι y.1)) ⧸
          (Ideal.span {t} ⊔
            IdealSheafData.stalk Z
              (infinitySection f ((infinityFiber f Z).subschemeι y.1)))) ≤ 0 :=
  exists_le_zero_of_exists_eq_stalk y
    (exists_localEquation_ringKrullDim_quotient_eq_infinityFiber f Z y.1)

/-! ### The second dimension hypothesis -/

/-- The order-theoretic heart of the dimension-one bound. If an integer-valued function on a
preorder is strictly monotone and bounded above by `k + 1`, then a non-maximal element at which
it takes the value `k` has coheight exactly one: every element strictly above it is already
maximal, since the function there is forced to be `k + 1`. -/
private lemma coheight_eq_one_of_strictMono_of_le_of_eq {T : Type*} [Preorder T] {g : T → ℤ}
    (hmono : ∀ ⦃x y : T⦄, x < y → g x < g y) {k : ℤ} (hg : ∀ z : T, g z ≤ k + 1) {ξ : T}
    (hξ : g ξ = k) (hnotmax : ¬ IsMax ξ) :
    Order.coheight ξ = 1 := by
  refine le_antisymm (Order.coheight_le_coe_iff.mpr fun y hy ↦ ?_)
    (Order.one_le_iff_ne_zero.mpr (Order.coheight_ne_zero.mpr hnotmax))
  have hyval : g ξ < g y := hmono hy
  have hymax : IsMax y := by
    intro b hb
    by_contra hcon
    have hlt : g y < g b := hmono (lt_iff_le_not_ge.mpr ⟨hb, hcon⟩)
    have hbound := hg b
    omega
  rw [Order.coheight_eq_zero.mpr hymax]
  exact zero_lt_one

/-- **Stacks 02S5**, the dimension-one hypothesis. Let `Z` be a closed subscheme of
`X ×_S 𝐏¹_S` all of whose points have relative dimension at most `k + 1` over the base, and let
`ξ` be a point of `Z` of relative dimension exactly `k` lying on one of the two distinguished
sections. If the associated points of `Z` either avoid both sections or have relative dimension
strictly below `k`, then the local ring of `Z` at `ξ` has Krull dimension one.

The upper bound uses only the cap `k + 1` and the strict monotonicity of the relative dimension
of Stacks 02JW; the lower bound is the statement that `ξ` is not the generic point of an
irreducible component of `Z`, which is what the hypothesis on associated points provides. -/
theorem ringKrullDim_stalk_subscheme_eq_one (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (Z : (projectiveLineProduct f).IdealSheafData)
    (k : ℤ) {ξ : Z.subscheme}
    (hZ : ∀ ζ : Z.subscheme, relativeDimension C.dimensionFunction
        (Z.subschemeι ≫ pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) ζ ≤ k + 1)
    (hξ : relativeDimension C.dimensionFunction
        (Z.subschemeι ≫ pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) ξ = k)
    (hrange : Z.subschemeι ξ ∈ Set.range (zeroSection f) ∨
      Z.subschemeι ξ ∈ Set.range (infinitySection f))
    (hAssociated : ξ ∈ Stacks.Divisors.schemeAssociatedPoints Z.subscheme →
      ((Z.subschemeι ξ ∉ Set.range (zeroSection f) ∧
          Z.subschemeι ξ ∉ Set.range (infinitySection f)) ∨
        relativeDimension C.dimensionFunction
          (Z.subschemeι ≫ pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) ξ < k)) :
    ringKrullDim (Z.subscheme.presheaf.stalk ξ) = 1 := by
  have hnoeth : IsLocallyNoetherian Z.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian
      (Z.subschemeι ≫ pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f)
  have hnotmax : ¬ IsMax ξ := by
    intro hmax
    have hgen : ξ ∈ genericPoints Z.subscheme := mem_genericPoints_of_isMax hmax
    rcases hAssociated (mem_schemeAssociatedPoints_of_isGenericPoint_irreducibleComponent
        Z.subscheme hgen (genericPoints.isGenericPoint ⟨ξ, hgen⟩)) with ⟨h0, hInf⟩ | hlt
    · exact hrange.elim h0 hInf
    · omega
  have hmono : ∀ ⦃x y : Z.subscheme⦄, x < y →
      relativeDimension C.dimensionFunction
          (Z.subschemeι ≫ pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) x <
        relativeDimension C.dimensionFunction
          (Z.subschemeι ≫ pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) y := by
    intro x y hxy
    have h := (deltaDimensionFunction C
      (Z.subschemeι ≫ pullback.fst f
        (relativeProjectiveLine C.S ↘ C.S) ≫ f)).strictAnti_specializes hxy.le (ne_of_gt hxy)
    rwa [deltaDimensionFunction_apply, deltaDimensionFunction_apply] at h
  rw [ringKrullDim_stalk_eq_coheight,
    coheight_eq_one_of_strictMono_of_le_of_eq hmono hZ hξ hnotmax]
  rfl

/-- **Stacks 02S5**, the dimension-one hypothesis in the form the local comparison uses it: the
quotient of the local ring of `X ×_S 𝐏¹_S` at `Z.subschemeι ξ` by the stalk of the ideal sheaf
of `Z` has Krull dimension one.

This is the hypothesis `hdim` of
`Stacks.Chow.length_quotient_span_sup_eq_sum_minimalPrimes_of_notMem_associatedPrimes`, obtained
from `Stacks.Chow.ringKrullDim_stalk_subscheme_eq_one` by
`Stacks.Chow.ringKrullDim_quotient_idealStalk_eq`. -/
theorem ringKrullDim_quotient_idealStalk_eq_one (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (Z : (projectiveLineProduct f).IdealSheafData)
    (k : ℤ) {ξ : Z.subscheme}
    (hZ : ∀ ζ : Z.subscheme, relativeDimension C.dimensionFunction
        (Z.subschemeι ≫ pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) ζ ≤ k + 1)
    (hξ : relativeDimension C.dimensionFunction
        (Z.subschemeι ≫ pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) ξ = k)
    (hrange : Z.subschemeι ξ ∈ Set.range (zeroSection f) ∨
      Z.subschemeι ξ ∈ Set.range (infinitySection f))
    (hAssociated : ξ ∈ Stacks.Divisors.schemeAssociatedPoints Z.subscheme →
      ((Z.subschemeι ξ ∉ Set.range (zeroSection f) ∧
          Z.subschemeι ξ ∉ Set.range (infinitySection f)) ∨
        relativeDimension C.dimensionFunction
          (Z.subschemeι ≫ pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) ξ < k)) :
    ringKrullDim ((projectiveLineProduct f).presheaf.stalk (Z.subschemeι ξ) ⧸
      IdealSheafData.stalk Z (Z.subschemeι ξ)) = 1 :=
  (ringKrullDim_quotient_idealStalk_eq Z ξ).trans
    (ringKrullDim_stalk_subscheme_eq_one C f Z k hZ hξ hrange hAssociated)

end Stacks.Chow

end
