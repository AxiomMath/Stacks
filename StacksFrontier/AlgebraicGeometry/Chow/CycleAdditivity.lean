module

public import StacksFrontier.AlgebraicGeometry.Chow.CycleAdditivity.ComponentRuleFinsum
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs

/-!
# Locally finite sums of cycles rationally equivalent to zero

A `k`-cycle `α` is rationally equivalent to zero in the sense of [Stacks, Tag 02RW] when there is
a locally finite family `{W_j}` of integral closed subschemes of delta-dimension `k + 1`, and a
nonzero rational function `g_j` on each, with `α = ∑ᶠ_j (W_j ⟶ X)_* div(g_j)`. This file shows
that a locally finite sum of cycles rationally equivalent to zero is rationally equivalent to
zero, provided the witnessing families of the summands lie in the members of a locally finite
family of subsets of `X`. The combined family is indexed by the sigma type `Σ j, I j` of the index
sets of the individual families.

## Main definitions

* `Stacks.Chow.IsRationallyEquivalentToZeroWithin` — rational equivalence to zero witnessed by a
  family of integral closed subschemes contained in a given subset of `X`.

## Main results

* `Stacks.Chow.finsum_sigma` — a finitely supported `finsum` over a sigma type is the iterated
  `finsum`.
* `Stacks.Chow.rationallyEquivalentToZero_of_sigma_presentation` — a cycle presented as the
  locally finite double sum of the pushforwards of the principal divisors of a `J`-indexed family
  of families of rational functions is rationally equivalent to zero.
* `Stacks.Chow.rationallyEquivalentToZero_finsum` — a locally finite sum of cycles each
  rationally equivalent to zero, with witnesses lying in a locally finite family of sets, is
  rationally equivalent to zero.

## References

* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Topology

universe u

namespace Stacks.Chow

/-! ### Locally finite sums over a sigma type -/

/-- A finitely supported sum over a sigma type is the iterated sum: first over the fibres of the
first projection, then over the base. -/
theorem finsum_sigma {J : Type*} {I : J → Type*} {M : Type*} [AddCommMonoid M]
    (f : ((j : J) × I j) → M) (hf : (Function.support f).Finite) :
    (∑ᶠ s : (j : J) × I j, f s) = ∑ᶠ j : J, ∑ᶠ i : I j, f ⟨j, i⟩ := by
  rw [← finsum_finsum_mem_fiber Sigma.fst f hf]
  refine finsum_congr fun j ↦ ?_
  have hrange : Sigma.fst ⁻¹' {j} = Set.range fun i : I j ↦ (⟨j, i⟩ : (j : J) × I j) := by
    ext s
    refine ⟨fun hs ↦ ?_, fun ⟨i, hi⟩ ↦ hi ▸ rfl⟩
    obtain ⟨j', i⟩ := s
    obtain rfl : j' = j := hs
    exact ⟨i, rfl⟩
  rw [hrange, finsum_mem_range sigma_mk_injective]

/-! ### Rational equivalence with a prescribed carrier -/

/-- A `k`-cycle is rationally equivalent to zero *within* a subset `T` of `X` when the family of
integral closed subschemes witnessing its rational equivalence to zero can be taken inside `T`. -/
def IsRationallyEquivalentToZeroWithin (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (k : ℤ) (α : CycleGroup C p k) (T : Set X) : Prop :=
  ∃ (J : Type u) (W : J → X.IdealSheafData) (hW : ∀ j, IsIntegral (W j).subscheme)
    (_ : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)),
    (LocallyFinite fun j ↦ ((W j).support : Set X)) ∧ (∀ j, ((W j).support : Set X) ⊆ T) ∧
      ∃ g : ∀ j, (rationalFunctions (W j).subscheme)ˣ,
        ∀ x : X, α.1 x = principalDivisorFamilyCoefficient C p W hW g x

/-- The zero cycle is rationally equivalent to zero within any subset, via the empty family. -/
theorem isRationallyEquivalentToZeroWithin_zero (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) (T : Set X) :
    IsRationallyEquivalentToZeroWithin C p k 0 T := by
  refine ⟨PEmpty.{u + 1}, (fun j ↦ nomatch j), (fun j ↦ nomatch j), (fun j ↦ nomatch j),
    (fun _ ↦ ⟨Set.univ, Filter.univ_mem, Set.toFinite _⟩), (fun j ↦ nomatch j),
    (fun j ↦ nomatch j), fun x ↦ ?_⟩
  change (0 : AlgebraicCycle X ℤ) x = _
  simp [principalDivisorFamilyCoefficient, finsum_of_isEmpty]

/-- Enlarging the carrier preserves rational equivalence to zero within it. -/
theorem IsRationallyEquivalentToZeroWithin.mono {C : ChowSituation.{u}} {X : Scheme.{u}}
    {p : X ⟶ C.S} [LocallyOfFiniteType p] {k : ℤ} {α : CycleGroup C p k} {T T' : Set X}
    (h : IsRationallyEquivalentToZeroWithin C p k α T) (hT : T ⊆ T') :
    IsRationallyEquivalentToZeroWithin C p k α T' := by
  obtain ⟨J, W, hW, hDim, hLocal, hsub, g, hg⟩ := h
  exact ⟨J, W, hW, hDim, hLocal, fun j ↦ (hsub j).trans hT, g, hg⟩

/-- A cycle rationally equivalent to zero within a subset is rationally equivalent to zero. -/
theorem IsRationallyEquivalentToZeroWithin.isRationallyEquivalentToZero
    {C : ChowSituation.{u}} {X : Scheme.{u}} {p : X ⟶ C.S} [LocallyOfFiniteType p] {k : ℤ}
    {α : CycleGroup C p k} {T : Set X} (h : IsRationallyEquivalentToZeroWithin C p k α T) :
    IsRationallyEquivalentToZero C p k α := by
  obtain ⟨J, W, hW, hDim, hLocal, -, g, hg⟩ := h
  exact ⟨J, W, hW, hDim, hLocal, g, hg⟩

/-- A cycle is rationally equivalent to zero if and only if it is rationally equivalent to zero
within the whole of `X`. -/
theorem isRationallyEquivalentToZeroWithin_univ_iff (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) (α : CycleGroup C p k) :
    IsRationallyEquivalentToZeroWithin C p k α Set.univ ↔
      IsRationallyEquivalentToZero C p k α := by
  refine ⟨fun h ↦ h.isRationallyEquivalentToZero, fun h ↦ ?_⟩
  obtain ⟨J, W, hW, hDim, hLocal, g, hg⟩ := h
  exact ⟨J, W, hW, hDim, hLocal, fun j ↦ Set.subset_univ _, g, hg⟩

/-! ### The `Sigma`-indexed additivity -/

/-- A cycle whose coefficients are the iterated locally finite sum, over `j : J` and then over
`i : I j`, of the pushforwards of the principal divisors of rational functions on a locally finite
family `{W_{j,i}}` of integral closed subschemes of delta-dimension `k + 1` is rationally
equivalent to zero within any set containing the family. -/
theorem rationallyEquivalentToZeroWithin_of_sigma_presentation (C : ChowSituation.{u})
    {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) {J : Type u} {I : J → Type u}
    (W : ∀ j, I j → X.IdealSheafData) (hW : ∀ j i, IsIntegral (W j i).subscheme)
    (hDim : ∀ j i, schemeDeltaDimension C ((W j i).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (hLocal : LocallyFinite fun s : (j : J) × I j ↦ ((W s.1 s.2).support : Set X))
    (g : ∀ j i, (rationalFunctions (W j i).subscheme)ˣ) (T : Set X)
    (hT : ∀ j i, ((W j i).support : Set X) ⊆ T) {α : CycleGroup C p k}
    (hα : ∀ x : X,
      α.1 x = ∑ᶠ j : J, principalDivisorFamilyCoefficient C p (W j) (hW j) (g j) x) :
    IsRationallyEquivalentToZeroWithin C p k α T := by
  have hsub : ∀ s : (j : J) × I j,
      Function.support (principalDivisorPushforward C p (W s.1 s.2) (hW s.1 s.2) (g s.1 s.2)) ⊆
        ((W s.1 s.2).support : Set X) :=
    fun s ↦ support_principalDivisorPushforward_subset C p (W s.1 s.2) (hW s.1 s.2) (g s.1 s.2)
  have hfin : ∀ x : X, (Function.support fun s : (j : J) × I j ↦
      principalDivisorPushforward C p (W s.1 s.2) (hW s.1 s.2) (g s.1 s.2) x).Finite :=
    fun x ↦ finite_support_of_locallyFinite _ hLocal _ hsub x
  refine ⟨(j : J) × I j, fun s ↦ W s.1 s.2, fun s ↦ hW s.1 s.2, fun s ↦ hDim s.1 s.2, hLocal,
    fun s ↦ hT s.1 s.2, fun s ↦ g s.1 s.2, fun x ↦ ?_⟩
  rw [hα x]
  simp only [principalDivisorFamilyCoefficient]
  exact (finsum_sigma (fun s : (j : J) × I j ↦
    principalDivisorPushforward C p (W s.1 s.2) (hW s.1 s.2) (g s.1 s.2) x) (hfin x)).symm

/-- A cycle whose coefficients are the iterated locally finite sum of the pushforwards of the
principal divisors of a `J`-indexed family of families of rational functions on integral closed
subschemes of delta-dimension `k + 1` is rationally equivalent to zero. -/
theorem rationallyEquivalentToZero_of_sigma_presentation (C : ChowSituation.{u})
    {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) {J : Type u} {I : J → Type u}
    (W : ∀ j, I j → X.IdealSheafData) (hW : ∀ j i, IsIntegral (W j i).subscheme)
    (hDim : ∀ j i, schemeDeltaDimension C ((W j i).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (hLocal : LocallyFinite fun s : (j : J) × I j ↦ ((W s.1 s.2).support : Set X))
    (g : ∀ j i, (rationalFunctions (W j i).subscheme)ˣ) {α : CycleGroup C p k}
    (hα : ∀ x : X,
      α.1 x = ∑ᶠ j : J, principalDivisorFamilyCoefficient C p (W j) (hW j) (g j) x) :
    IsRationallyEquivalentToZero C p k α :=
  (rationallyEquivalentToZeroWithin_of_sigma_presentation C p k W hW hDim hLocal g Set.univ
    (fun _ _ ↦ Set.subset_univ _) hα).isRationallyEquivalentToZero

/-! ### Locally finite sums of cycles rationally equivalent to zero -/

/-- A cycle that is coefficientwise the locally finite sum of cycles `D j`, each rationally
equivalent to zero within a set `E j`, is rationally equivalent to zero within the union of the
`E j`, provided the family `E` is locally finite. -/
theorem rationallyEquivalentToZeroWithin_finsum (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) {J : Type u} (D : J → CycleGroup C p k)
    (E : J → Set X) (hE : LocallyFinite E)
    (hD : ∀ j, IsRationallyEquivalentToZeroWithin C p k (D j) (E j))
    {α : CycleGroup C p k} (hα : ∀ x : X, α.1 x = ∑ᶠ j : J, (D j).1 x) :
    IsRationallyEquivalentToZeroWithin C p k α (⋃ j, E j) := by
  choose I W hW hDim hLocal hsub g hg using hD
  have hsigma : LocallyFinite fun s : (j : J) × I j ↦ ((W s.1 s.2).support : Set X) := by
    intro x
    obtain ⟨t, ht, hAfin⟩ := hE x
    choose t' ht' hfin' using fun j ↦ hLocal j x
    refine ⟨t ∩ ⋂ j ∈ {j : J | (E j ∩ t).Nonempty}, t' j,
      Filter.inter_mem ht ((Filter.biInter_mem hAfin).2 fun j _ ↦ ht' j), ?_⟩
    refine (hAfin.biUnion fun j _ ↦
      (hfin' j).image fun i ↦ (⟨j, i⟩ : (j : J) × I j)).subset ?_
    rintro s ⟨z, hz, hzt⟩
    have hjA : s.1 ∈ {j : J | (E j ∩ t).Nonempty} := ⟨z, hsub s.1 s.2 hz, hzt.1⟩
    exact Set.mem_biUnion hjA ⟨s.2, ⟨z, hz, Set.mem_iInter₂.1 hzt.2 s.1 hjA⟩, rfl⟩
  refine rationallyEquivalentToZeroWithin_of_sigma_presentation C p k W hW hDim hsigma g _
    (fun j i ↦ (hsub j i).trans (Set.subset_iUnion E j)) fun x ↦
      (hα x).trans (finsum_congr fun j ↦ hg j x)

/-- A cycle that is coefficientwise the locally finite sum of cycles each rationally equivalent to
zero within the members of a locally finite family of sets is rationally equivalent to zero. -/
theorem rationallyEquivalentToZero_finsum (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) {J : Type u} (D : J → CycleGroup C p k)
    (E : J → Set X) (hE : LocallyFinite E)
    (hD : ∀ j, IsRationallyEquivalentToZeroWithin C p k (D j) (E j))
    {α : CycleGroup C p k} (hα : ∀ x : X, α.1 x = ∑ᶠ j : J, (D j).1 x) :
    IsRationallyEquivalentToZero C p k α :=
  (rationallyEquivalentToZeroWithin_finsum C p k D E hE hD hα).isRationallyEquivalentToZero

end Stacks.Chow

end
