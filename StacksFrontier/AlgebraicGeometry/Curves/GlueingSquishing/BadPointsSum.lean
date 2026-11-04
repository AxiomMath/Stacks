module

public import Mathlib.Algebra.BigOperators.Finprod
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleRestriction
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.BadPointsAdditivity

/-!
# The measure of [Stacks, Tag 0C1L] as a number, and its strict drop

The induction `Stacks.GlueSquishFactor.isElementaryChain_of_split` is on an `ℕ`-valued measure
`μ`, and the measure the source uses is the *total* length of `f_*𝒪_{X'}/𝒪_X`, i.e. the sum over
the points of `X` of the stalkwise multiplicities. Everything in
`StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.BadPointsAdditivity` is pointwise. **This
file forms the sum and proves that it drops strictly**, at each end of an intermediate
factorization.

## Main definitions

* `Stacks.GlueSquishFactor.sumSheafMultiplicity` — the total multiplicity of a sheaf of modules,
  `∑ᶠ x, m_F(x)`, read in `ℕ`. It is a `finsum`, so it is a *total* function: a module whose
  multiplicity is nonzero at infinitely many points is given total multiplicity `0`, and every
  statement below therefore carries the finiteness of the support that rules this out.
* `Stacks.GlueSquishFactor.measureOver` — **the measure `μ` of [Stacks, Tag 0C1L]**: the total
  multiplicity of `f_*𝒪_{X'}/𝒪_X` for a morphism of schemes over `Spec k`. This is the `μ` that
  `Stacks.GlueSquishFactor.isElementaryChain_of_isAlmostIso` quantifies over.

## Main results

* `Stacks.GlueSquishFactor.sumSheafMultiplicity_eq_finset_sum` — the total multiplicity is a
  `Finset` sum over any finite set carrying the support.
* `Stacks.GlueSquishFactor.sumSheafMultiplicity_lt_of_forall_le` — **the comparison**: if `F` has
  multiplicity at most that of `G` everywhere, strictly less somewhere, and `G` has finite
  support, then the total multiplicity of `F` is strictly below that of `G`. The finiteness
  hypothesis is on `G` alone; the support of `F` is contained in it wherever `F`'s multiplicity
  is nonzero, which is all the sum sees.
* `Stacks.GlueSquishFactor.sumSheafMultiplicity_eq_of_iso` — the total multiplicity is an
  isomorphism invariant, which is what carries the measure across the identification
  `q_*𝒪_{Spec_X(𝒜)} ≅ 𝒜` of [Stacks, Tag 01SA].
* `Stacks.GlueSquishFactor.sumSheafMultiplicity_cokernel_lt_of_mem_supp_right` and
  `...sumSheafMultiplicity_cokernel_lt_of_mem_supp_left` — **the two strict drops of the measure of
  [Stacks, Tag 0C1L]**, in the summed form the induction reads: for a factorization
  `𝒪_X ⟶ 𝒜 ⟶ f_*𝒪_{X'}` of the unit by monomorphisms of `𝒪_X`-modules, the total multiplicity
  of `𝒜/𝒪_X` (respectively of `f_*𝒪_{X'}/𝒜`) is strictly below that of `f_*𝒪_{X'}/𝒪_X` as soon
  as `f_*𝒪_{X'}/𝒜` (respectively `𝒜/𝒪_X`) is nonzero at one point.

## Implementation notes

**Why the support of the smaller quotient needs no hypothesis.** `Stacks.Chow.sheafMultiplicity`
is `ℤ`-valued through `ENat.toNat`, so an *infinite* stalk length is recorded as `0` — which is
why the pointwise statements of
`StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.BadPointsAdditivity` carry a finite-length
hypothesis. For the *sum* this cuts the other way and helps: `finsum` only looks at
`Function.support`, and a point where `F`'s multiplicity is nonzero has `G`'s multiplicity
nonzero too, hence lies in the support of `G`. So one finiteness hypothesis, on the larger
quotient, serves both sums. For `f_*𝒪_{X'}/𝒪_X` it is discharged by
`Stacks.GlueSquishFactor.finite_supp_cokernel_structureUnitHom`.

**What the two drops below do and do not give.** They are the drops of the measure *computed on
`X`*. The induction needs the measure of the lower half `Spec_X(𝒜) ⟶ X` — which is the total
multiplicity of `𝒜/𝒪_X` once `q_*𝒪_{Spec_X(𝒜)}` is identified with `𝒜` by [Stacks, Tag 01SA] —
and the measure of the *upper* half `X' ⟶ Spec_X(𝒜)`, which is a sum over the points of
`Spec_X(𝒜)` and is *not* the total multiplicity of `f_*𝒪_{X'}/𝒜` on the nose. Comparing the two
is the fibre sum, `Stacks.GlueSquishFactor.sum_sheafMultiplicity_le_sheafMultiplicity_pushforward`,
composed with the identification of `q_*` of the upper quotient with `f_*𝒪_{X'}/𝒜` through
`Stacks.AlgebraicGeometry.AffineQcohExactness.preservesColimit_parallelPair_zero`; neither
composition is performed here.

## No stacks attribute

**No `@[stacks]` attribute is attached, and none is earned.** These statements are inputs to the
splitting hypothesis `hsplit` of
`Stacks.GlueSquishFactor.isElementaryChain_of_isAlmostIso`, which is still unproved.

## References

* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.GlueSquishFactor

/-! ### The total multiplicity -/

/-- **The total multiplicity of a sheaf of modules**: the sum over the points of `X` of
`Stacks.Chow.sheafMultiplicity`, read in `ℕ`.

It is a `finsum`, hence total: where the multiplicity is nonzero at infinitely many points the
value is `0`. Every consumer below carries the finiteness hypothesis that excludes this. -/
def sumSheafMultiplicity {X : Scheme.{u}} (F : X.Modules) : ℕ :=
  ∑ᶠ x : X, (Stacks.Chow.sheafMultiplicity F x).toNat

/-- The multiplicity is a nonnegative integer, being a cast of `ENat.toNat` of a length. -/
theorem sheafMultiplicity_nonneg {X : Scheme.{u}} (F : X.Modules) (x : X) :
    0 ≤ Stacks.Chow.sheafMultiplicity F x := by
  rw [Stacks.Chow.sheafMultiplicity]
  exact Int.natCast_nonneg _

/-- A point where the multiplicity of `F` is nonzero lies in the support of `F`. -/
theorem mem_supp_of_toNat_sheafMultiplicity_ne_zero {X : Scheme.{u}} (F : X.Modules) {x : X}
    (hx : (Stacks.Chow.sheafMultiplicity F x).toNat ≠ 0) : x ∈ SheafOfModules.supp F := by
  by_contra hcon
  rw [Stacks.Chow.sheafMultiplicity_eq_zero_of_notMem_supp F hcon] at hx
  exact hx rfl

/-- **The total multiplicity as a `Finset` sum.** Over any finite set of points containing every
point at which the multiplicity is nonzero, the `finsum` is the ordinary sum. -/
theorem sumSheafMultiplicity_eq_finset_sum {X : Scheme.{u}} (F : X.Modules) (s : Finset X)
    (hs : ∀ x : X, (Stacks.Chow.sheafMultiplicity F x).toNat ≠ 0 → x ∈ s) :
    sumSheafMultiplicity F = ∑ x ∈ s, (Stacks.Chow.sheafMultiplicity F x).toNat :=
  finsum_eq_sum_of_support_subset _ fun x hx => by
    simpa using hs x (by simpa using hx)

/-- **The total multiplicity is an isomorphism invariant**, the multiplicity at each point being
one by `Stacks.Chow.sheafMultiplicity_eq_of_iso`. This is what carries the measure across the
identification `q_*𝒪_{Spec_X(𝒜)} ≅ 𝒜` of [Stacks, Tag 01SA]. -/
theorem sumSheafMultiplicity_eq_of_iso {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) :
    sumSheafMultiplicity F = sumSheafMultiplicity G :=
  finsum_congr fun x => congrArg Int.toNat (Stacks.Chow.sheafMultiplicity_eq_of_iso e x)

/-! ### The comparison of two total multiplicities -/

/-- **The strict comparison of total multiplicities.** If the multiplicity of `F` is at most that
of `G` at every point, strictly less at one point, and the support of `G` is finite, then the
total multiplicity of `F` is strictly below that of `G`.

Only `G` is assumed to have finite support: a point where `F`'s multiplicity is nonzero has `G`'s
multiplicity nonzero as well, so both sums are `Finset` sums over the support of `G`, and
`Finset.sum_lt_sum` applies. -/
theorem sumSheafMultiplicity_lt_of_forall_le {X : Scheme.{u}} (F G : X.Modules)
    (hGfin : (SheafOfModules.supp G : Set X).Finite)
    (hle : ∀ x : X, Stacks.Chow.sheafMultiplicity F x ≤ Stacks.Chow.sheafMultiplicity G x)
    {x₀ : X}
    (hlt : Stacks.Chow.sheafMultiplicity F x₀ < Stacks.Chow.sheafMultiplicity G x₀) :
    sumSheafMultiplicity F < sumSheafMultiplicity G := by
  classical
  have hmem : ∀ x : X, (Stacks.Chow.sheafMultiplicity G x).toNat ≠ 0 → x ∈ hGfin.toFinset :=
    fun x hx => hGfin.mem_toFinset.mpr (mem_supp_of_toNat_sheafMultiplicity_ne_zero G hx)
  have hmemF : ∀ x : X, (Stacks.Chow.sheafMultiplicity F x).toNat ≠ 0 → x ∈ hGfin.toFinset :=
    fun x hx => hmem x (by have := Int.toNat_le_toNat (hle x); omega)
  rw [sumSheafMultiplicity_eq_finset_sum F _ hmemF,
    sumSheafMultiplicity_eq_finset_sum G _ hmem]
  have := sheafMultiplicity_nonneg F x₀
  refine Finset.sum_lt_sum (fun i _ => Int.toNat_le_toNat (hle i)) ⟨x₀, hmem x₀ ?_, ?_⟩ <;> omega

/-- A strict pointwise drop of `F` below `G = F + C`, with `G` of finite support, drops the total
multiplicity. -/
private theorem sumSheafMultiplicity_lt_of_add_eq {X : Scheme.{u}} (F C G : X.Modules)
    (hGfin : (SheafOfModules.supp G : Set X).Finite)
    (hadd : ∀ x : X, Stacks.Chow.sheafMultiplicity G x =
      Stacks.Chow.sheafMultiplicity F x + Stacks.Chow.sheafMultiplicity C x)
    {x₀ : X} (hlt : Stacks.Chow.sheafMultiplicity F x₀ < Stacks.Chow.sheafMultiplicity G x₀) :
    sumSheafMultiplicity F < sumSheafMultiplicity G :=
  sumSheafMultiplicity_lt_of_forall_le F G hGfin
    (fun x => by have := sheafMultiplicity_nonneg C x; have := hadd x; omega) hlt

/-! ### The measure of [Stacks, Tag 0C1L] -/

/-- **The measure `μ` of the induction of [Stacks, Tag 0C1L]**: the total multiplicity of
`f_*𝒪_{X'}/𝒪_X`, i.e. the total length of the source's `f_*𝒪_{X'}/𝒪_X`.

This is the `μ` that `Stacks.GlueSquishFactor.isElementaryChain_of_isAlmostIso` quantifies over:
it is a bare `ℕ`-valued function of a morphism of `k`-schemes with no hypotheses, which is what
`Stacks.GlueSquishFactor.isElementaryChain_of_split` takes. -/
def measureOver {k : Type u} [Field k] {Y' Y : Over (Spec (.of k))} (g : Y' ⟶ Y) : ℕ :=
  sumSheafMultiplicity (cokernel (structureUnitHom g.left))

/-- **The strict drop of the measure at the upper end.** With the hypotheses of
`Stacks.GlueSquishFactor.sheafMultiplicity_cokernel_structureUnitHom_add` and one point at which
`f_*𝒪_{X'}/𝒜` does not vanish, the total multiplicity of `𝒜/𝒪_X` is strictly below the measure
of `f`.

The pointwise inequality is additivity together with nonnegativity, the strict inequality at the
one point is
`Stacks.GlueSquishFactor.sheafMultiplicity_cokernel_structureUnitHom_lt_of_mem_supp_right`,
and the finiteness of the support of `f_*𝒪_{X'}/𝒪_X` is
`Stacks.GlueSquishFactor.finite_supp_cokernel_structureUnitHom`. -/
theorem sumSheafMultiplicity_cokernel_lt_of_mem_supp_right {k : Type u} [Field k]
    {X' X : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (hcoh : (cokernel (structureUnitHom f)).IsCoherent) (U : X.Opens) [IsIso (f ∣_ U)]
    (hUfin : Set.Finite ((U : Set X)ᶜ)) {A : X.Modules} (a : unitModule X ⟶ A)
    (b : A ⟶ (AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules)) [Mono a]
    [Mono b] (hab : a ≫ b = structureUnitHom f) {x₀ : X}
    (hb : x₀ ∈ SheafOfModules.supp (cokernel b)) :
    sumSheafMultiplicity (cokernel a) <
      sumSheafMultiplicity (cokernel (structureUnitHom f)) := by
  exact sumSheafMultiplicity_lt_of_add_eq _ (cokernel b) _
    (finite_supp_cokernel_structureUnitHom f U hUfin)
    (sheafMultiplicity_cokernel_structureUnitHom_add f p hcoh U hUfin a b hab)
    (sheafMultiplicity_cokernel_structureUnitHom_lt_of_mem_supp_right f p hcoh U hUfin a b hab hb)

/-- **The strict drop of the measure at the lower end.** With the hypotheses of
`Stacks.GlueSquishFactor.sheafMultiplicity_cokernel_structureUnitHom_add` and one point at which
`𝒜/𝒪_X` does not vanish, the total multiplicity of `f_*𝒪_{X'}/𝒜` is strictly below the measure of
`f`. -/
theorem sumSheafMultiplicity_cokernel_lt_of_mem_supp_left {k : Type u} [Field k]
    {X' X : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (hcoh : (cokernel (structureUnitHom f)).IsCoherent) (U : X.Opens) [IsIso (f ∣_ U)]
    (hUfin : Set.Finite ((U : Set X)ᶜ)) {A : X.Modules} (a : unitModule X ⟶ A)
    (b : A ⟶ (AlgebraSheaf.underlyingModule (pushforwardAlgebra f) : X.Modules)) [Mono a]
    [Mono b] (hab : a ≫ b = structureUnitHom f) {x₀ : X}
    (ha : x₀ ∈ SheafOfModules.supp (cokernel a)) :
    sumSheafMultiplicity (cokernel b) <
      sumSheafMultiplicity (cokernel (structureUnitHom f)) := by
  have hfin0 := isFiniteLength_stalk_cokernel_structureUnitHom f p hcoh U hUfin x₀
  rw [← hab] at hfin0
  exact sumSheafMultiplicity_lt_of_add_eq _ (cokernel a) _
    (finite_supp_cokernel_structureUnitHom f U hUfin)
    (fun x => (sheafMultiplicity_cokernel_structureUnitHom_add f p hcoh U hUfin a b hab x).trans
      (add_comm _ _))
    (sheafMultiplicity_cokernel_lt_of_mem_supp_left (x := x₀) a b hfin0 ha |>.trans_eq
      (congrArg (fun φ => Stacks.Chow.sheafMultiplicity (cokernel φ) x₀) hab))

end Stacks.GlueSquishFactor

end
