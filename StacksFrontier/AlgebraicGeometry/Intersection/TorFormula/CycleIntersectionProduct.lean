module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.FlatPullbackVariety
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.Defs
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.IntersectionProductCycle
import StacksCore.Tactic.StacksAttribute

/-!
# The intersection product of two cycles

Let `X` be a nonsingular variety, let `α = ∑ᵢ nᵢ [Wᵢ]` be an `r`-cycle and `β = ∑ⱼ mⱼ [Vⱼ]` an
`s`-cycle on `X` which intersect properly. Section 43.17 of the source defines their intersection
product by bilinearity from the product of two closed subvarieties of Section 43.14:

`α · β = ∑ᵢⱼ nᵢ mⱼ Wᵢ · Vⱼ`,

and writes `α · V` for `α · [V]`. This file constructs that bilinear extension, for an arbitrary
rule `prod` assigning a cycle to a pair of closed subvarieties, and then instantiates `prod` at
the Tor-formula product of Section 43.14.

Closed subvarieties are their generic points, as cycles are, so `prod` is a function of two points
of `X` and the sum is indexed by `X × X`; a pair whose two coefficients are not both nonzero
contributes zero, so the index set is effectively the pairs of components of `α` and `β`. On a
quasi-compact `X` — in particular on a variety — a cycle has finite support, so the sum is the
honest finite double sum of the source.

## Main definitions

* `AlgebraicGeometry.TorFormula.cycleIntersectionProduct` — **Tag 0B08**, the product `α · β`.
* `AlgebraicGeometry.TorFormula.structureSheafAt` — the structure sheaf `𝒪_W` of the reduced
  closure `W` of a point, as a module on the ambient scheme.
* `AlgebraicGeometry.TorFormula.torSubvarietyProductOfBound` — the Section 43.14 product `W · V`
  of the reduced closures of two points, from the delta-dimension bound for that single pair.
* `AlgebraicGeometry.TorFormula.torFormulaSubvarietyProduct` — the Section 43.14 product `W · V`
  of the reduced closures of two points, by the Tor formula.
* `AlgebraicGeometry.TorFormula.torFormulaSubvarietyProductTotal` — the same product read at
  every pair of points, the zero cycle at a pair whose `Tor` sheaves have too big a support.
* `AlgebraicGeometry.TorFormula.torFormulaCycleIntersectionProduct` — **Tag 0B08** for that
  product: the intersection product of two cycles computed by the Tor formula.
* `AlgebraicGeometry.TorFormula.cycleIntersectionProductLeftHom` and
  `AlgebraicGeometry.TorFormula.cycleIntersectionProductRightHom` — the product against a fixed
  cycle in the other variable, as a homomorphism of cycle groups.

## Main results

* `AlgebraicGeometry.TorFormula.cycleIntersectionProduct_eq_sum` — the displayed double sum.
* `AlgebraicGeometry.TorFormula.cycleIntersectionProduct_single_right` — the clause `α · V`.
* `AlgebraicGeometry.TorFormula.cycleIntersectionProduct_single_single` — on two prime cycles the
  product is the product of the two subvarieties.
* `AlgebraicGeometry.TorFormula.cycleIntersectionProduct_add_left` and
  `AlgebraicGeometry.TorFormula.cycleIntersectionProduct_add_right` — bilinearity, from which the
  rest of the linearity family — `cycleIntersectionProduct_zsmul_left`,
  `cycleIntersectionProduct_sum_left`, `cycleIntersectionProduct_finsum_zsmul_left` and their
  right-hand companions — is read off the two homomorphisms above.
* `AlgebraicGeometry.TorFormula.intersectProperly_of_mem_support` — every pair of components
  actually contributing to the sum intersects properly, which is the standing hypothesis of the
  source read off the index set.
* `AlgebraicGeometry.TorFormula.torSupportBound_of_intersectProperly` — over a field the
  delta-dimension bounds that the Tor-formula product needs follow from proper intersection of
  the two components.
* `AlgebraicGeometry.TorFormula.torSupportBound_of_mem_support_of_intersectProperly` — for two
  cycles intersecting properly, every pair of components contributing to `α · β` satisfies those
  bounds.
* `AlgebraicGeometry.TorFormula.torFormulaSubvarietyProductTotal_eq_of_intersectProperly` —
  **Tag 0B08**, the agreement with the source: at every pair of components contributing to
  `α · β` the summand is the alternating sum `∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_X}(𝒪_W, 𝒪_V)]_n` of
  Section 43.14, namely `intersectionProductCycle` of Tag 0AZR.

## Implementation notes

The sum is a `finsum` over `X × X`, which is total whatever the summands do, and
`cycleIntersectionProduct_eq_sum` is what says the value is the finite double sum of the source
rather than an artefact of the convention: it needs the supports of `α` and `β` to be finite,
which `finite_support_of_compactSpace` supplies on a quasi-compact scheme.

The expected dimension `r + s - dim X` is spelled as a natural number `n` together with the
hypothesis `dim W + dim V = dim X + n`; no subtraction of extended dimensions occurs.

### Why the subvariety product is read at every pair of points

The source forms `W · V` only for subvarieties intersecting properly, since only then are the
`Tor` sheaves supported closely enough for `[-]_k` to be a `k`-cycle. Demanding that bound at
every pair of points of `X` at once would be a condition nothing satisfies: at the generic point
of `X` taken twice, `Tor₀(𝒪_X, 𝒪_X) = 𝒪_X` is supported on all of `X`, so the bound fails for
every `k` below the dimension of `X`. `torFormulaSubvarietyProductTotal` therefore reads the
genuine alternating sum at a pair that does satisfy the bound and the zero cycle at a pair that
does not, which makes `torFormulaCycleIntersectionProduct` a plain function of `α` and `β`.

Nothing is lost at the pairs the source sums over. Only pairs of components of `α` and `β`
contribute to the double sum, and when `α` and `β` intersect properly in the sense of Definition
43.13.5 those pairs intersect properly, so they satisfy the bound: that is
`torSupportBound_of_mem_support_of_intersectProperly`, and
`torFormulaSubvarietyProductTotal_eq_of_intersectProperly` turns it into the agreement of every
contributing summand with `intersectionProductCycle` of Tag 0AZR. The value computed here is
therefore the `α · β` of the source rather than an artefact of the convention.

## References

* [Stacks Project, Tag 0B08](https://stacks.math.columbia.edu/tag/0B08)
* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
* [Stacks Project, Tag 0AZQ](https://stacks.math.columbia.edu/tag/0AZQ)
* [Stacks Project, Tag 0AZT](https://stacks.math.columbia.edu/tag/0AZT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.TorFormula

variable {X : Scheme.{u}}

/-! ### The bilinear extension -/

/-- The summand of the intersection product of two cycles indexed by a pair of points: the
product of the two coefficients times the product of the two closed subvarieties. -/
def cycleIntersectionProductSummand (prod : X → X → AlgebraicCycle X ℤ)
    (α β : AlgebraicCycle X ℤ) (q : X × X) : AlgebraicCycle X ℤ :=
  (α q.1 * β q.2) • prod q.1 q.2

/-- **Stacks 0B08: the intersection product of two cycles.** For a rule `prod` assigning a cycle
to a pair of closed subvarieties of `X`, the bilinear extension `α · β = ∑ᵢⱼ nᵢ mⱼ Wᵢ · Vⱼ` of
`prod` to cycles `α = ∑ᵢ nᵢ [Wᵢ]` and `β = ∑ⱼ mⱼ [Vⱼ]`. -/
@[stacks 0B08 "the displayed definition `α · β = ∑ᵢⱼ nᵢ mⱼ Wᵢ · Vⱼ` of the intersection product \
of an `r`-cycle and an `s`-cycle, with no hypotheses, for the product `Wᵢ · Vⱼ` of two closed \
subvarieties of Section 43.14 supplied as the parameter `prod`. Closed subvarieties are their \
generic points, so `prod` is a function of two points and the sum is indexed by `X × X`; the \
pairs that contribute are the pairs of components of `α` and `β`, and \
`cycleIntersectionProduct_eq_sum` identifies the value with the finite double sum displayed by \
the source. The instance of this definition in which `prod` is the Tor-formula product of \
Section 43.14 is `torFormulaCycleIntersectionProduct`."]
def cycleIntersectionProduct (prod : X → X → AlgebraicCycle X ℤ)
    (α β : AlgebraicCycle X ℤ) : AlgebraicCycle X ℤ :=
  ∑ᶠ q : X × X, cycleIntersectionProductSummand prod α β q

/-- Only pairs of components of the two cycles contribute to the intersection product. -/
theorem support_cycleIntersectionProductSummand_subset (prod : X → X → AlgebraicCycle X ℤ)
    (α β : AlgebraicCycle X ℤ) :
    Function.support (cycleIntersectionProductSummand prod α β) ⊆
      Function.support α ×ˢ Function.support β := by
  intro q hq
  refine ⟨?_, ?_⟩ <;> by_contra h <;>
    simp only [Function.notMem_support] at h <;>
    exact hq (by simp [cycleIntersectionProductSummand, h])

/-- If both cycles have finitely many components, the intersection product is a finite sum. -/
theorem hasFiniteSupport_cycleIntersectionProductSummand (prod : X → X → AlgebraicCycle X ℤ)
    {α β : AlgebraicCycle X ℤ} (hα : (Function.support α).Finite)
    (hβ : (Function.support β).Finite) :
    Function.HasFiniteSupport (cycleIntersectionProductSummand prod α β) :=
  (hα.prod hβ).subset (support_cycleIntersectionProductSummand_subset prod α β)

/-- A cycle on a quasi-compact scheme has finitely many components: its support is locally finite
and the whole space is compact. -/
theorem finite_support_of_compactSpace [CompactSpace X] (α : AlgebraicCycle X ℤ) :
    (Function.support α).Finite := by
  have := α.locallyFiniteSupport.finite_inter_support_of_isCompact (isCompact_univ (X := X))
  simpa using this

/-- **The display of Stacks 0B08.** For cycles `α = ∑ᵢ nᵢ [Wᵢ]` and `β = ∑ⱼ mⱼ [Vⱼ]` with
finitely many components, `α · β = ∑ᵢⱼ nᵢ mⱼ Wᵢ · Vⱼ` as a finite double sum. -/
@[stacks 0B08 "the display `α · β = ∑ᵢⱼ nᵢ mⱼ Wᵢ · Vⱼ` as a finite double sum over the \
components of the two cycles, assuming each has finitely many components — which on a \
quasi-compact scheme, in particular on a variety, is automatic by \
`finite_support_of_compactSpace`."]
theorem cycleIntersectionProduct_eq_sum (prod : X → X → AlgebraicCycle X ℤ)
    {α β : AlgebraicCycle X ℤ} (hα : (Function.support α).Finite)
    (hβ : (Function.support β).Finite) :
    cycleIntersectionProduct prod α β =
      ∑ x ∈ hα.toFinset, ∑ y ∈ hβ.toFinset, (α x * β y) • prod x y := by
  rw [cycleIntersectionProduct,
    finsum_eq_sum_of_support_subset _ (s := hα.toFinset ×ˢ hβ.toFinset) ?_, Finset.sum_product]
  · rfl
  · simpa using support_cycleIntersectionProductSummand_subset prod α β

/-- The coefficient of the intersection product at a point is the double sum of the coefficients
of the products of the components. -/
theorem cycleIntersectionProduct_apply (prod : X → X → AlgebraicCycle X ℤ)
    {α β : AlgebraicCycle X ℤ} (hα : (Function.support α).Finite)
    (hβ : (Function.support β).Finite) (z : X) :
    cycleIntersectionProduct prod α β z =
      ∑ x ∈ hα.toFinset, ∑ y ∈ hβ.toFinset, (α x * β y) * prod x y z := by
  rw [cycleIntersectionProduct_eq_sum prod hα hβ]
  simp [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]

/-- The intersection product with the zero cycle is zero. -/
@[simp]
theorem cycleIntersectionProduct_zero_left (prod : X → X → AlgebraicCycle X ℤ)
    (β : AlgebraicCycle X ℤ) : cycleIntersectionProduct prod 0 β = 0 :=
  finsum_eq_zero_of_forall_eq_zero fun _ => by simp [cycleIntersectionProductSummand]

/-- The intersection product with the zero cycle is zero. -/
@[simp]
theorem cycleIntersectionProduct_zero_right (prod : X → X → AlgebraicCycle X ℤ)
    (α : AlgebraicCycle X ℤ) : cycleIntersectionProduct prod α 0 = 0 :=
  finsum_eq_zero_of_forall_eq_zero fun _ => by simp [cycleIntersectionProductSummand]

/-! ### Linearity in one variable

The two primitives are `cycleIntersectionProduct_add_left` and
`cycleIntersectionProduct_add_right`, which carry explicit finiteness hypotheses and so hold on an
arbitrary scheme. On a quasi-compact scheme the finiteness is automatic, so the product against a
fixed cycle in the other variable is an `AddMonoidHom`, and every further form of linearity —
along a `Finset` sum, along a finitely supported weighted sum — is one of that homomorphism's own
`map_` lemmas. -/

/-- If every summand of a product is the sum of the summands of two others, the products add. -/
private theorem cycleIntersectionProduct_eq_add_of_summand_eq
    (prod : X → X → AlgebraicCycle X ℤ) {α β α₁ β₁ α₂ β₂ : AlgebraicCycle X ℤ}
    (h₁ : Function.HasFiniteSupport (cycleIntersectionProductSummand prod α₁ β₁))
    (h₂ : Function.HasFiniteSupport (cycleIntersectionProductSummand prod α₂ β₂))
    (h : ∀ q, cycleIntersectionProductSummand prod α β q =
      cycleIntersectionProductSummand prod α₁ β₁ q +
        cycleIntersectionProductSummand prod α₂ β₂ q) :
    cycleIntersectionProduct prod α β =
      cycleIntersectionProduct prod α₁ β₁ + cycleIntersectionProduct prod α₂ β₂ := by
  rw [cycleIntersectionProduct, cycleIntersectionProduct, cycleIntersectionProduct,
    ← finsum_add_distrib h₁ h₂]
  exact finsum_congr h

/-- If every summand of a product is `n` times the summand of another, the products scale. -/
private theorem cycleIntersectionProduct_eq_zsmul_of_summand_eq
    (prod : X → X → AlgebraicCycle X ℤ) (n : ℤ) {α β α' β' : AlgebraicCycle X ℤ}
    (h' : Function.HasFiniteSupport (cycleIntersectionProductSummand prod α' β'))
    (h : ∀ q, cycleIntersectionProductSummand prod α β q =
      n • cycleIntersectionProductSummand prod α' β' q) :
    cycleIntersectionProduct prod α β = n • cycleIntersectionProduct prod α' β' := by
  rw [cycleIntersectionProduct, cycleIntersectionProduct, smul_finsum' n h']
  exact finsum_congr h

/-- The intersection product is additive in its first argument. -/
theorem cycleIntersectionProduct_add_left (prod : X → X → AlgebraicCycle X ℤ)
    {α₁ α₂ β : AlgebraicCycle X ℤ} (h₁ : (Function.support α₁).Finite)
    (h₂ : (Function.support α₂).Finite) (hβ : (Function.support β).Finite) :
    cycleIntersectionProduct prod (α₁ + α₂) β =
      cycleIntersectionProduct prod α₁ β + cycleIntersectionProduct prod α₂ β :=
  cycleIntersectionProduct_eq_add_of_summand_eq prod
    (hasFiniteSupport_cycleIntersectionProductSummand prod h₁ hβ)
    (hasFiniteSupport_cycleIntersectionProductSummand prod h₂ hβ)
    fun _ => by simp [cycleIntersectionProductSummand, add_mul, add_smul]

/-- The intersection product is additive in its second argument. -/
theorem cycleIntersectionProduct_add_right (prod : X → X → AlgebraicCycle X ℤ)
    {α β₁ β₂ : AlgebraicCycle X ℤ} (hα : (Function.support α).Finite)
    (h₁ : (Function.support β₁).Finite) (h₂ : (Function.support β₂).Finite) :
    cycleIntersectionProduct prod α (β₁ + β₂) =
      cycleIntersectionProduct prod α β₁ + cycleIntersectionProduct prod α β₂ :=
  cycleIntersectionProduct_eq_add_of_summand_eq prod
    (hasFiniteSupport_cycleIntersectionProductSummand prod hα h₁)
    (hasFiniteSupport_cycleIntersectionProductSummand prod hα h₂)
    fun _ => by simp [cycleIntersectionProductSummand, mul_add, add_smul]

/-- The intersection product against a fixed second cycle, as a homomorphism of cycle groups.
Additivity needs each cycle to have finitely many components, which is automatic on a
quasi-compact scheme. -/
def cycleIntersectionProductLeftHom [CompactSpace X]
    (prod : X → X → AlgebraicCycle X ℤ) (β : AlgebraicCycle X ℤ) :
    AlgebraicCycle X ℤ →+ AlgebraicCycle X ℤ :=
  AddMonoidHom.mk' (fun α => cycleIntersectionProduct prod α β) fun α₁ α₂ =>
    cycleIntersectionProduct_add_left prod (finite_support_of_compactSpace α₁)
      (finite_support_of_compactSpace α₂) (finite_support_of_compactSpace β)

/-- The intersection product against a fixed first cycle, as a homomorphism of cycle groups. -/
def cycleIntersectionProductRightHom [CompactSpace X]
    (prod : X → X → AlgebraicCycle X ℤ) (α : AlgebraicCycle X ℤ) :
    AlgebraicCycle X ℤ →+ AlgebraicCycle X ℤ :=
  AddMonoidHom.mk' (cycleIntersectionProduct prod α) fun β₁ β₂ =>
    cycleIntersectionProduct_add_right prod (finite_support_of_compactSpace α)
      (finite_support_of_compactSpace β₁) (finite_support_of_compactSpace β₂)

/-- The intersection product is homogeneous in its first argument. -/
theorem cycleIntersectionProduct_zsmul_left (prod : X → X → AlgebraicCycle X ℤ) (n : ℤ)
    {α β : AlgebraicCycle X ℤ} (hα : (Function.support α).Finite)
    (hβ : (Function.support β).Finite) :
    cycleIntersectionProduct prod (n • α) β = n • cycleIntersectionProduct prod α β :=
  cycleIntersectionProduct_eq_zsmul_of_summand_eq prod n
    (hasFiniteSupport_cycleIntersectionProductSummand prod hα hβ) fun q => by
      simp only [cycleIntersectionProductSummand, Function.locallyFinsuppWithin.coe_zsmul,
        Pi.smul_apply, smul_eq_mul, smul_smul, mul_assoc]

/-- The intersection product is homogeneous in its second argument. -/
theorem cycleIntersectionProduct_zsmul_right (prod : X → X → AlgebraicCycle X ℤ) (n : ℤ)
    {α β : AlgebraicCycle X ℤ} (hα : (Function.support α).Finite)
    (hβ : (Function.support β).Finite) :
    cycleIntersectionProduct prod α (n • β) = n • cycleIntersectionProduct prod α β :=
  cycleIntersectionProduct_eq_zsmul_of_summand_eq prod n
    (hasFiniteSupport_cycleIntersectionProductSummand prod hα hβ) fun q => by
      simp only [cycleIntersectionProductSummand, Function.locallyFinsuppWithin.coe_zsmul,
        Pi.smul_apply, smul_eq_mul, smul_smul, mul_left_comm]

/-- The intersection product distributes over a finite sum in its first argument. On a
quasi-compact scheme every cycle has finitely many components, so no finiteness hypothesis is
needed. -/
theorem cycleIntersectionProduct_sum_left [CompactSpace X]
    (prod : X → X → AlgebraicCycle X ℤ) {ι : Type*} (s : Finset ι)
    (A : ι → AlgebraicCycle X ℤ) (β : AlgebraicCycle X ℤ) :
    cycleIntersectionProduct prod (∑ i ∈ s, A i) β =
      ∑ i ∈ s, cycleIntersectionProduct prod (A i) β :=
  map_sum (cycleIntersectionProductLeftHom prod β) A s

/-- The intersection product distributes over a finite sum in its second argument. -/
theorem cycleIntersectionProduct_sum_right [CompactSpace X]
    (prod : X → X → AlgebraicCycle X ℤ) {ι : Type*} (s : Finset ι)
    (α : AlgebraicCycle X ℤ) (B : ι → AlgebraicCycle X ℤ) :
    cycleIntersectionProduct prod α (∑ i ∈ s, B i) =
      ∑ i ∈ s, cycleIntersectionProduct prod α (B i) :=
  map_sum (cycleIntersectionProductRightHom prod α) B s

/-- **The product of cycles is linear in its first variable along a finitely supported weighted
sum.** This is the bilinearity of `cycleIntersectionProduct` applied to a sum
`∑ᵢ cᵢ • αᵢ` such as the alternating sum `∑ᵢ (-1)ⁱ [Torᵢ(ℱ, 𝒢)]` the Tor formula produces. -/
theorem cycleIntersectionProduct_finsum_zsmul_left [CompactSpace X]
    (prod : X → X → AlgebraicCycle X ℤ) {ι : Type*} (c : ι → ℤ) (α : ι → AlgebraicCycle X ℤ)
    (hα : (Function.support fun i => c i • α i).Finite) (β : AlgebraicCycle X ℤ) :
    cycleIntersectionProduct prod (∑ᶠ i, c i • α i) β =
      ∑ᶠ i, c i • cycleIntersectionProduct prod (α i) β :=
  Eq.trans (AddMonoidHom.map_finsum (cycleIntersectionProductLeftHom prod β) hα)
    (finsum_congr fun i => (cycleIntersectionProductLeftHom prod β).map_zsmul (c i) (α i))

/-- **The product of cycles is linear in its second variable along a finitely supported weighted
sum.** -/
theorem cycleIntersectionProduct_finsum_zsmul_right [CompactSpace X]
    (prod : X → X → AlgebraicCycle X ℤ) (α : AlgebraicCycle X ℤ) {ι : Type*} (c : ι → ℤ)
    (β : ι → AlgebraicCycle X ℤ) (hβ : (Function.support fun i => c i • β i).Finite) :
    cycleIntersectionProduct prod α (∑ᶠ i, c i • β i) =
      ∑ᶠ i, c i • cycleIntersectionProduct prod α (β i) :=
  Eq.trans (AddMonoidHom.map_finsum (cycleIntersectionProductRightHom prod α) hβ)
    (finsum_congr fun i => (cycleIntersectionProductRightHom prod α).map_zsmul (c i) (β i))

/-- **A cycle with finitely many components is the finite sum of its prime cycles.** Each point
carrying a nonzero coefficient contributes that coefficient times the prime cycle of its closure.
On a quasi-compact scheme the finiteness hypothesis is automatic by
`finite_support_of_compactSpace`. -/
theorem cycle_eq_sum_single [DecidableEq X] {α : AlgebraicCycle X ℤ}
    (hα : (Function.support α).Finite) :
    α = ∑ v ∈ hα.toFinset, Function.locallyFinsuppWithin.single v (α v) := by
  refine Function.locallyFinsuppWithin.ext fun z => ?_
  have h1 : (∑ v ∈ hα.toFinset, Function.locallyFinsuppWithin.single v (α v)) z =
      ∑ v ∈ hα.toFinset, (if z = v then α v else 0) := by
    rw [Function.locallyFinsuppWithin.coe_sum]
    simp [Finset.sum_apply]
  rw [h1, Finset.sum_ite_eq]
  by_cases hz : z ∈ hα.toFinset
  · rw [ite_eq_left hz]
  · rw [ite_eq_right hz]
    exact Function.notMem_support.1 fun h => hz (hα.mem_toFinset.2 h)

/-! ### Prime cycles -/

/-- On two prime cycles the intersection product is the product of the two closed subvarieties:
`[W] · [V] = W · V`. -/
@[stacks 0B08 "the one-term case of the display, with NO hypotheses: on the prime cycles \
`α = m [W]` and `β = n [V]` the product is `m n (W · V)`, so the bilinear extension really does \
extend the product of two closed subvarieties of Section 43.14. This is the clause of the \
section that is carried unrestrictedly; the full display needs each cycle to have finitely many \
components (`cycleIntersectionProduct_eq_sum`)."]
theorem cycleIntersectionProduct_single_single [DecidableEq X]
    (prod : X → X → AlgebraicCycle X ℤ) (x y : X) (m n : ℤ) :
    cycleIntersectionProduct prod (Function.locallyFinsuppWithin.single x m)
      (Function.locallyFinsuppWithin.single y n) = (m * n) • prod x y := by
  rw [cycleIntersectionProduct, finsum_eq_single _ (x, y) ?_]
  · simp [cycleIntersectionProductSummand]
  · rintro ⟨a, b⟩ hab
    simp only [cycleIntersectionProductSummand]
    rcases ne_or_eq a x with ha | rfl
    · simp [ha]
    · simp_all [Prod.ext_iff]

/-- **The clause `α · V` of Stacks 0B08.** For `β = [V]` the prime cycle of a closed subvariety,
the intersection product is `α · V = ∑ᵢ nᵢ Wᵢ · V`. -/
@[stacks 0B08 "the final clause of the section: for `β = [V]` the prime cycle of a closed \
subvariety `V`, the product `α · β`, there written `α · V`, is `∑ᵢ nᵢ Wᵢ · V`. Assumes `α` has \
finitely many components."]
theorem cycleIntersectionProduct_single_right [DecidableEq X]
    (prod : X → X → AlgebraicCycle X ℤ) {α : AlgebraicCycle X ℤ}
    (hα : (Function.support α).Finite) (y : X) :
    cycleIntersectionProduct prod α (Function.locallyFinsuppWithin.single y 1) =
      ∑ x ∈ hα.toFinset, α x • prod x y := by
  rw [cycleIntersectionProduct,
    finsum_eq_sum_of_support_subset _ (s := hα.toFinset ×ˢ {y}) ?_, Finset.sum_product]
  · exact Finset.sum_congr rfl fun x _ => by simp [cycleIntersectionProductSummand]
  · intro q hq
    obtain ⟨h1, h2⟩ := support_cycleIntersectionProductSummand_subset prod _ _ hq
    simp only [Function.mem_support, Function.locallyFinsuppWithin.single_apply,
      ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not] at h2
    refine Finset.mem_coe.2 (Finset.mem_product.2 ⟨hα.mem_toFinset.2 h1, ?_⟩)
    simpa using h2

/-- **The clause `W · β` of Stacks 0B08.** For `α = [W]` the prime cycle of a closed subvariety,
the intersection product is `W · β = ∑ⱼ mⱼ W · Vⱼ`. -/
@[stacks 0B08 "the first-variable form of the final clause of the section: for `α = [W]` the \
prime cycle of a closed subvariety `W`, the product `α · β` is `∑ⱼ mⱼ W · Vⱼ`. Assumes `β` has \
finitely many components."]
theorem cycleIntersectionProduct_single_left [DecidableEq X]
    (prod : X → X → AlgebraicCycle X ℤ) {β : AlgebraicCycle X ℤ}
    (hβ : (Function.support β).Finite) (x : X) :
    cycleIntersectionProduct prod (Function.locallyFinsuppWithin.single x 1) β =
      ∑ y ∈ hβ.toFinset, β y • prod x y := by
  rw [cycleIntersectionProduct,
    finsum_eq_sum_of_support_subset _ (s := {x} ×ˢ hβ.toFinset) ?_, Finset.sum_product,
    Finset.sum_singleton]
  · exact Finset.sum_congr rfl fun y _ => by simp [cycleIntersectionProductSummand]
  · intro q hq
    obtain ⟨h1, h2⟩ := support_cycleIntersectionProductSummand_subset prod _ _ hq
    simp only [Function.mem_support, Function.locallyFinsuppWithin.single_apply,
      ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not] at h1
    refine Finset.mem_coe.2 (Finset.mem_product.2 ⟨?_, hβ.mem_toFinset.2 h2⟩)
    simpa using h1

/-- The coefficient at a point of the product `W · β` of a prime cycle with a cycle. -/
theorem cycleIntersectionProduct_single_left_apply [DecidableEq X]
    (prod : X → X → AlgebraicCycle X ℤ) {β : AlgebraicCycle X ℤ}
    (hβ : (Function.support β).Finite) (x z : X) :
    cycleIntersectionProduct prod (Function.locallyFinsuppWithin.single x 1) β z =
      ∑ y ∈ hβ.toFinset, β y * prod x y z := by
  rw [cycleIntersectionProduct_single_left prod hβ x]
  simp [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]

/-! ### The standing hypothesis of proper intersection -/

/-- A point is the generic point of the reduced closure of its singleton. -/
theorem genericPoint_closure_singleton (x : X) :
    (isIrreducible_singleton (x := x)).closure.genericPoint = x :=
  (isGenericPoint_closure.eq
    ((isIrreducible_singleton (x := x)).closure.isGenericPoint_genericPoint
      isClosed_closure)).symm

/-- **The standing hypothesis of Stacks 0B08 read off the index set.** If `α` and `β` intersect
properly then every pair of closed subvarieties actually contributing to `α · β` intersects
properly. -/
theorem intersectProperly_of_mem_support (prod : X → X → AlgebraicCycle X ℤ)
    {α β : AlgebraicCycle X ℤ} (h : AlgebraicCycle.IntersectProperly α β) {q : X × X}
    (hq : q ∈ Function.support (cycleIntersectionProductSummand prod α β)) :
    AlgebraicGeometry.IntersectProperly
      ⟨closure {q.1}, isIrreducible_singleton.closure, isClosed_closure⟩
      ⟨closure {q.2}, isIrreducible_singleton.closure, isClosed_closure⟩ := by
  obtain ⟨h1, h2⟩ := support_cycleIntersectionProductSummand_subset prod α β hq
  exact h _ _ (by rwa [genericPoint_closure_singleton]) (by rwa [genericPoint_closure_singleton])

/-! ### The Tor-formula product of two cycles -/

/-- The structure sheaf `𝒪_W` of the reduced closure `W` of a point, pushed forward to an
`𝒪_X`-module on the ambient scheme. -/
def structureSheafAt (x : X) : X.Modules :=
  (Scheme.Modules.pushforward (Stacks.Chow.integralComponentAt x).subschemeι).obj
    (Stacks.Ample.unitModule _)

/-- On a locally Noetherian scheme, the pushed-forward structure sheaf `structureSheafAt x` of the
reduced closure of a point is coherent. -/
instance isCoherent_structureSheafAt [IsLocallyNoetherian X] (x : X) :
    (structureSheafAt x).IsCoherent :=
  Stacks.Chow.isCoherent_pushforwardStructureSheaf _

/-- The hypothesis under which the Tor-formula product of the reduced closures of two points is a
`k`-cycle: every `Tor` sheaf of their structure sheaves has support of delta-dimension at most
`k`. -/
def TorSupportBound (C : Stacks.Chow.ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian X] (hX : IsRegular X) (k : ℤ) (x y : X) : Prop :=
  ∀ i : ℕ,
    haveI := isCoherent_torSheaf_of_isRegular X hX (structureSheafAt x) (structureSheafAt y)
      (isCoherent_structureSheafAt x) (isCoherent_structureSheafAt y) i
    Stacks.Chow.schemeDeltaDimension C
      ((Stacks.Chow.reducedSupport
        (torSheaf X (structureSheafAt x) (structureSheafAt y) i)).subschemeι ≫ f) ≤
      WithBotTop.coe k

/-- The Section 43.14 product `W · V` of the reduced closures of two points of a regular scheme,
formed from the delta-dimension bound for that one pair: the alternating sum
`∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_X}(𝒪_W, 𝒪_V)]_k` of the cycles of the `Tor` sheaves of their structure
sheaves. -/
def torSubvarietyProductOfBound (C : Stacks.Chow.ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsLocallyNoetherian X] (hX : IsRegular X) (k : ℤ)
    {x y : X} (h : TorSupportBound C f hX k x y) : AlgebraicCycle X ℤ :=
  intersectionProductCycle C f hX (structureSheafAt x) (structureSheafAt y)
    (isCoherent_structureSheafAt x) (isCoherent_structureSheafAt y) k h

/-- The Section 43.14 product `W · V` of the reduced closures of two points of a regular scheme:
the alternating sum `∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_X}(𝒪_W, 𝒪_V)]_k` of the cycles of the `Tor` sheaves of
their structure sheaves. -/
def torFormulaSubvarietyProduct (C : Stacks.Chow.ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsLocallyNoetherian X] (hX : IsRegular X) (k : ℤ)
    (hFk : ∀ x y : X, TorSupportBound C f hX k x y) (x y : X) : AlgebraicCycle X ℤ :=
  intersectionProductCycle C f hX (structureSheafAt x) (structureSheafAt y)
    (isCoherent_structureSheafAt x) (isCoherent_structureSheafAt y) k (hFk x y)

/-- The two spellings of the Section 43.14 product agree: the alternating sum uses exactly the
one delta-dimension bound belonging to the pair of points it is formed at. -/
theorem torFormulaSubvarietyProduct_eq_torSubvarietyProductOfBound
    (C : Stacks.Chow.ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian X] (hX : IsRegular X) (k : ℤ)
    (hFk : ∀ x y : X, TorSupportBound C f hX k x y) (x y : X) :
    torFormulaSubvarietyProduct C f hX k hFk x y =
      torSubvarietyProductOfBound C f hX k (hFk x y) :=
  rfl

/-- The Section 43.14 product `W · V` of the reduced closures of two points, read at every pair:
the alternating sum `∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_X}(𝒪_W, 𝒪_V)]_k` at a pair whose `Tor` sheaves have
supports of delta-dimension at most `k`, and the zero cycle at a pair where they do not. Only
pairs of components of the two cycles contribute to the intersection product of Section 43.17,
and for cycles intersecting properly such a pair always satisfies the bound. -/
def torFormulaSubvarietyProductTotal (C : Stacks.Chow.ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsLocallyNoetherian X] (hX : IsRegular X) (k : ℤ)
    (x y : X) : AlgebraicCycle X ℤ :=
  open Classical in
  if h : TorSupportBound C f hX k x y then torSubvarietyProductOfBound C f hX k h else 0

/-- At a pair of points whose `Tor` sheaves have supports of delta-dimension at most `k`, the
product read there is the alternating sum of Section 43.14. -/
theorem torFormulaSubvarietyProductTotal_eq_of_bound (C : Stacks.Chow.ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsLocallyNoetherian X]
    (hX : IsRegular X) (k : ℤ) {x y : X} (h : TorSupportBound C f hX k x y) :
    torFormulaSubvarietyProductTotal C f hX k x y = torSubvarietyProductOfBound C f hX k h :=
  dite_eq_left h

/-- At a pair of points some `Tor` sheaf of which has too big a support, the product read there
is the zero cycle. -/
theorem torFormulaSubvarietyProductTotal_eq_zero (C : Stacks.Chow.ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsLocallyNoetherian X]
    (hX : IsRegular X) (k : ℤ) {x y : X} (h : ¬ TorSupportBound C f hX k x y) :
    torFormulaSubvarietyProductTotal C f hX k x y = 0 :=
  dite_eq_right h

/-- **Stacks 0B08 for the Tor formula.** The intersection product `α · β = ∑ᵢⱼ nᵢ mⱼ Wᵢ · Vⱼ` of
two cycles on a regular scheme, with `Wᵢ · Vⱼ` the Tor-formula product of Section 43.14. -/
@[stacks 0B08 "the intersection product α · β, total in the Tor-support bound"]
def torFormulaCycleIntersectionProduct (C : Stacks.Chow.ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsLocallyNoetherian X] (hX : IsRegular X) (k : ℤ)
    (α β : AlgebraicCycle X ℤ) : AlgebraicCycle X ℤ :=
  cycleIntersectionProduct (torFormulaSubvarietyProductTotal C f hX k) α β

/-- The Tor-formula intersection product of two cycles with finitely many components is the finite
double sum `∑ᵢⱼ nᵢ mⱼ Wᵢ · Vⱼ`. -/
theorem torFormulaCycleIntersectionProduct_eq_sum (C : Stacks.Chow.ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] [IsLocallyNoetherian X]
    (hX : IsRegular X) (k : ℤ) {α β : AlgebraicCycle X ℤ} (hα : (Function.support α).Finite)
    (hβ : (Function.support β).Finite) :
    torFormulaCycleIntersectionProduct C f hX k α β =
      ∑ x ∈ hα.toFinset, ∑ y ∈ hβ.toFinset,
        (α x * β y) • torFormulaSubvarietyProductTotal C f hX k x y :=
  cycleIntersectionProduct_eq_sum _ hα hβ

/-! ### The bound from proper intersection -/

/-- The structure sheaf of the reduced closure of a point is supported on that closure. -/
theorem supp_structureSheafAt (x : X) :
    SheafOfModules.supp (structureSheafAt x) = closure ({x} : Set X) := by
  rw [structureSheafAt, Stacks.Chow.supp_pushforwardStructureSheaf,
    Scheme.IdealSheafData.range_subschemeι, Stacks.Chow.coe_support_integralComponentAt]

/-- The `Tor` sheaves of the structure sheaves of the reduced closures of two points are
supported on the intersection of those closures. -/
theorem supp_torSheaf_structureSheafAt_subset (x y : X) (i : ℕ) :
    SheafOfModules.supp (torSheaf X (structureSheafAt x) (structureSheafAt y) i) ⊆
      closure ({x} : Set X) ∩ closure ({y} : Set X) := by
  rw [← supp_structureSheafAt x, ← supp_structureSheafAt y]
  exact supp_torSheaf_subset_inter X _ _ i

/-- A bound on the dimension of the intersection of the reduced closures of two points of a
scheme over a field bounds the delta-dimension of the supports of the `Tor` sheaves of their
structure sheaves. -/
theorem torSupportBound_of_topologicalKrullDim_le (k : Type u) [Field k] {X : Scheme.{u}}
    (sX : X ⟶ (Stacks.Chow.fieldChowSituation k).S) [LocallyOfFiniteType sX]
    [IsLocallyNoetherian X] (hX : IsRegular X) (n : ℕ) (x y : X)
    (hxy : topologicalKrullDim (↥(closure ({x} : Set X) ∩ closure ({y} : Set X))) ≤
      (n : WithBot ℕ∞)) :
    TorSupportBound (Stacks.Chow.fieldChowSituation k) sX hX (n : ℤ) x y := by
  intro i
  have := isCoherent_torSheaf_of_isRegular X hX (structureSheafAt x) (structureSheafAt y)
    (isCoherent_structureSheafAt x) (isCoherent_structureSheafAt y) i
  refine Stacks.Chow.schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le k sX _ n ?_
  refine le_trans ?_ hxy
  exact (Topology.IsEmbedding.inclusion
    (supp_torSheaf_structureSheafAt_subset x y i)).isInducing.topologicalKrullDim_le

/-- Two closed subvarieties whose dimensions sum to `dim X + n` and which intersect properly have
intersection of dimension at most `n`.  The hypothesis is the sum of the two dimensions; the
variant `topologicalKrullDim_inter_le_of_intersectProperly` in
`StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.SubvarietyIntersection` takes the two
dimensions separately together with `r + s = n + k`. -/
theorem topologicalKrullDim_inter_le_of_intersectProperly_of_add_eq
    {W V : IrreducibleCloseds X}
    (h : AlgebraicGeometry.IntersectProperly W V) {m n : ℕ}
    (hdimX : topologicalKrullDim X = (m : WithBot ℕ∞))
    (hdim : topologicalKrullDim (W : Set X) + topologicalKrullDim (V : Set X) =
      (m : WithBot ℕ∞) + (n : WithBot ℕ∞)) :
    topologicalKrullDim (↥((W : Set X) ∩ (V : Set X))) ≤ (n : WithBot ℕ∞) := by
  rw [AlgebraicGeometry.intersectProperly_iff, hdimX, hdim] at h
  set a := topologicalKrullDim (↥((W : Set X) ∩ (V : Set X))) with ha
  clear_value a
  rcases eq_or_ne a ⊥ with rfl | hbot
  · simp
  lift a to ℕ∞ using hbot with b
  have h' : b + (m : ℕ∞) ≤ (n : ℕ∞) + (m : ℕ∞) := by
    rw [add_comm ((n : ℕ∞))]
    exact_mod_cast h
  exact_mod_cast (WithTop.add_le_add_iff_right (by exact_mod_cast ENat.natCast_ne_top m)).1 h'

/-- **The hypothesis of Stacks 0B08 discharged.** If the reduced closures of two points of a
regular scheme over a field have dimensions summing to `dim X + n` and intersect properly, the
`Tor` sheaves of their structure sheaves satisfy the delta-dimension bound that makes the
Tor-formula product of Section 43.14 an `n`-cycle. -/
theorem torSupportBound_of_intersectProperly (k : Type u) [Field k] {X : Scheme.{u}}
    (sX : X ⟶ (Stacks.Chow.fieldChowSituation k).S) [LocallyOfFiniteType sX]
    [IsLocallyNoetherian X] (hX : IsRegular X) {m n : ℕ} (x y : X)
    (hdimX : topologicalKrullDim X = (m : WithBot ℕ∞))
    (hdim : topologicalKrullDim (closure ({x} : Set X)) +
      topologicalKrullDim (closure ({y} : Set X)) = (m : WithBot ℕ∞) + (n : WithBot ℕ∞))
    (hprop : AlgebraicGeometry.IntersectProperly
      ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
      ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩) :
    TorSupportBound (Stacks.Chow.fieldChowSituation k) sX hX (n : ℤ) x y :=
  torSupportBound_of_topologicalKrullDim_le k sX hX n x y
    (topologicalKrullDim_inter_le_of_intersectProperly_of_add_eq hprop hdimX hdim)

/-! ### Agreement with the product of the source -/

/-- **The bound at a contributing pair of components.** Let `α` and `β` be cycles on a regular
scheme over a field which intersect properly, with `dim X = m` and with the dimensions of the
closures of any component of `α` and any component of `β` summing to `m + n`. Then every pair of
points contributing to the double sum `∑ᵢⱼ nᵢ mⱼ Wᵢ · Vⱼ` satisfies the delta-dimension bound
that the Tor-formula product of Section 43.14 needs. -/
theorem torSupportBound_of_mem_support_of_intersectProperly (k : Type u) [Field k]
    {X : Scheme.{u}} (sX : X ⟶ (Stacks.Chow.fieldChowSituation k).S) [LocallyOfFiniteType sX]
    [IsLocallyNoetherian X] (hX : IsRegular X) {m n : ℕ} {α β : AlgebraicCycle X ℤ}
    (hαβ : AlgebraicCycle.IntersectProperly α β)
    (hdimX : topologicalKrullDim X = (m : WithBot ℕ∞))
    (hdim : ∀ x ∈ Function.support α, ∀ y ∈ Function.support β,
      topologicalKrullDim (closure ({x} : Set X)) +
        topologicalKrullDim (closure ({y} : Set X)) = (m : WithBot ℕ∞) + (n : WithBot ℕ∞))
    (prod : X → X → AlgebraicCycle X ℤ) {q : X × X}
    (hq : q ∈ Function.support (cycleIntersectionProductSummand prod α β)) :
    TorSupportBound (Stacks.Chow.fieldChowSituation k) sX hX (n : ℤ) q.1 q.2 := by
  obtain ⟨h1, h2⟩ := support_cycleIntersectionProductSummand_subset prod α β hq
  exact torSupportBound_of_intersectProperly k sX hX q.1 q.2 hdimX (hdim _ h1 _ h2)
    (intersectProperly_of_mem_support prod hαβ hq)

/-- **Stacks 0B08: the value computed here is the product of the source.** For cycles `α` and `β`
on a regular scheme over a field which intersect properly, with `dim X = m` and the dimensions of
the components summing to `m + n`, every summand of `α · β` that contributes is the genuine
alternating sum `∑ᵢ (-1)ⁱ [Torᵢ^{𝒪_X}(𝒪_{Wᵢ}, 𝒪_{Vⱼ})]_n` of Section 43.14, the
`intersectionProductCycle` of Tag 0AZR. So the double sum of `torFormulaCycleIntersectionProduct`
is the `α · β` the source displays. -/
@[stacks 0B08 "the summand Wᵢ · Vⱼ at a pair of components, by the Tor formula"]
theorem torFormulaSubvarietyProductTotal_eq_of_intersectProperly (k : Type u) [Field k]
    {X : Scheme.{u}} (sX : X ⟶ (Stacks.Chow.fieldChowSituation k).S) [LocallyOfFiniteType sX]
    [IsLocallyNoetherian X] (hX : IsRegular X) {m n : ℕ} {α β : AlgebraicCycle X ℤ}
    (hαβ : AlgebraicCycle.IntersectProperly α β)
    (hdimX : topologicalKrullDim X = (m : WithBot ℕ∞))
    (hdim : ∀ x ∈ Function.support α, ∀ y ∈ Function.support β,
      topologicalKrullDim (closure ({x} : Set X)) +
        topologicalKrullDim (closure ({y} : Set X)) = (m : WithBot ℕ∞) + (n : WithBot ℕ∞))
    {q : X × X}
    (hq : q ∈ Function.support (cycleIntersectionProductSummand
      (torFormulaSubvarietyProductTotal (Stacks.Chow.fieldChowSituation k) sX hX (n : ℤ)) α β)) :
    torFormulaSubvarietyProductTotal (Stacks.Chow.fieldChowSituation k) sX hX (n : ℤ) q.1 q.2 =
      intersectionProductCycle (Stacks.Chow.fieldChowSituation k) sX hX
        (structureSheafAt q.1) (structureSheafAt q.2) (isCoherent_structureSheafAt q.1)
        (isCoherent_structureSheafAt q.2) (n : ℤ)
        (torSupportBound_of_mem_support_of_intersectProperly k sX hX hαβ hdimX hdim _ hq) :=
  torFormulaSubvarietyProductTotal_eq_of_bound _ _ _ _ _

end AlgebraicGeometry.TorFormula

end
