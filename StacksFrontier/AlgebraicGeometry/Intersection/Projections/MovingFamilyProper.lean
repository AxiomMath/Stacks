module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyConstant
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyFibre
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyDim
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyFibreRange
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilySlice
public import StacksFrontier.Data.ENat.WithBotNatCast

/-!
# Clause (3) of the Moving Lemma: the dimension of `C' ∩ (X × ℓ)`

Clause (3) of Tag 0B1T says that the family `C'` meets the constant family `X × ℓ` properly. The
dimension criterion that defines proper intersection compares `dim (C' ∩ (X × ℓ))` with
`dim C' + dim (X × ℓ) - dim (ℓ × 𝐏(V))`, and all four dimensions are the dimension of a slice
plus one. This file supplies the only one of the four that is not already a product formula: the
upper bound for `dim (C' ∩ (X × ℓ))` in terms of the dimensions of the sets `r_g(C) ∩ X`, the
slices of `C' ∩ (X × ℓ)` over the closed points of the line.

The bound is the slice bound of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilySlice` applied to the
identification of the slices: over a closed point `λ` of the line the slice of `C' ∩ (X × ℓ)` is
`r_g(C) ∩ X`, by the fibre identification of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyFibre` and the fact that the
fibre of the constant family is `X`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_movingFamilySet_inter_le`: if
  every translate `r_g(C)` along the line meets `X` in a set of dimension at most `m`, then
  `C' ∩ (X × ℓ)` has dimension at most `m + 1`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.movingFibre_movingFamilySet_inter_constantFamily`:
  the slice identification itself.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.intersectProperly_criterion_movingFamilySet`:
  **clause (3) of Tag 0B1T**, the dimension criterion for `C'` and `X × ℓ`.

## Implementation notes

The bound is stated with a natural number `m` because that is what the semicontinuity step
`AlgebraicGeometry.fiberDimensionAt_le_of_isClosed_singleton_target` consumes; the caller
produces `m` from the dimension criterion satisfied by the translates.

Every closed point of the line is cut out by a nonzero functional on the corank-two quotient
(`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_eq_linearFunctionalPoint`), so the hypothesis
is quantified over those functionals rather than over the closed points themselves.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
* [Stacks Project, Tag 0AZQ](https://stacks.math.columbia.edu/tag/0AZQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
  (L : Submodule k (ParameterModule k V)) [FiniteDimensional k V]
  [Nontrivial (lineSpace k V L)] [Nontrivial V]

/-- **The slice of `C' ∩ (X × ℓ)` over a closed point of the line is `r_g(C) ∩ X`.** -/
public theorem movingFibre_movingFamilySet_inter_constantFamily {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k (lineSpace k V L)) {C X : Set (projectiveSpaceOfModule k V)}
    (hC : IsClosed C) {mu : Module.Dual k (lineSpace k V L)} (hmu : mu ≠ 0)
    (hCg : C ⊆ (endDomain k V (lineEnd k V L mu) : Set (projectiveSpaceOfModule k V))) :
    movingFibre k V L (linearFunctionalPoint k (lineSpace k V L) mu hmu)
        (linearFunctionalPoint_isClosed k (lineSpace k V L) mu hmu)
        (movingFamilySet k V L b C ∩ constantFamily k V L X) =
      endProjectionImage k V (lineEnd k V L mu) C ∩ X := by
  rw [movingFibre_inter_constantFamily k V L X _ _ (movingFamilySet k V L b C),
    movingFibre_movingFamilySet k V L b hC hmu hCg]

/-- **Clause (3) of Tag 0B1T, the dimension bound.** If every translate of `C` along the line
meets `X` in a set of dimension at most `m`, then `C' ∩ (X × ℓ)` has dimension at most
`m + 1`. -/
public theorem topologicalKrullDim_movingFamilySet_inter_le {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k (lineSpace k V L)) {C X : Set (projectiveSpaceOfModule k V)}
    (hC : IsClosed C) (hX : IsClosed X) (hL : Module.finrank k (lineSpace k V L) = 2)
    (hCg : ∀ (mu : Module.Dual k (lineSpace k V L)), mu ≠ 0 →
      C ⊆ (endDomain k V (lineEnd k V L mu) : Set (projectiveSpaceOfModule k V)))
    {m : ℕ}
    (hm : ∀ (mu : Module.Dual k (lineSpace k V L)), mu ≠ 0 →
      topologicalKrullDim ↥(endProjectionImage k V (lineEnd k V L mu) C ∩ X) ≤
        (m : WithBot ℕ∞)) :
    topologicalKrullDim ↥(movingFamilySet k V L b C ∩ constantFamily k V L X) ≤
      (m : WithBot ℕ∞) + 1 := by
  refine topologicalKrullDim_le_of_slice_le k V L
    ((isClosed_movingFamilySet k V L b hC).inter (isClosed_constantFamily k V L X hX)) hL
    fun lam hlam => ?_
  obtain ⟨mu, hmu, rfl⟩ := exists_eq_linearFunctionalPoint k (lineSpace k V L) lam hlam
  rw [← topologicalKrullDim_movingFibre k V L _ hlam
      (movingFamilySet k V L b C ∩ constantFamily k V L X),
    movingFibre_movingFamilySet_inter_constantFamily k V L b hC hmu (hCg mu hmu)]
  exact hm mu hmu

/-! ### Clause (3) itself -/

/-- An element of `WithBot ℕ∞` which is not `⊥` and is bounded by a natural number is a natural
number. -/
public theorem exists_natCast_of_ne_bot_of_le {a : WithBot ℕ∞} {n : ℕ} (hb : a ≠ ⊥)
    (h : a ≤ (n : WithBot ℕ∞)) : ∃ m : ℕ, a = (m : WithBot ℕ∞) := by
  have ht : a ≠ ⊤ := by
    intro htop
    rw [htop, top_le_iff] at h
    exact absurd h (natCast_ne_top_withBot n)
  cases ha : a with
  | bot => exact absurd ha hb
  | coe e =>
    cases e with
    | top => exact absurd ha ht
    | coe m => exact ⟨m, rfl⟩

/-- The dimension of a nonempty subspace bounded by a natural number is a natural number. -/
private theorem exists_natCast_of_nonempty_of_le {X : Type*} [TopologicalSpace X] {S : Set X}
    {n : ℕ} (hS : S.Nonempty) (h : topologicalKrullDim ↥S ≤ (n : WithBot ℕ∞)) :
    ∃ m : ℕ, topologicalKrullDim ↥S = (m : WithBot ℕ∞) := by
  refine exists_natCast_of_ne_bot_of_le ?_ h
  rw [ne_eq, topologicalKrullDim_eq_bot_iff_isEmpty]
  simp only [not_isEmpty_iff]
  exact ⟨⟨hS.choose, hS.choose_spec⟩⟩

/-- Cancelling a finite summand on the right of an inequality in `WithBot ℕ∞`. -/
public theorem le_natCast_of_add_natCast_le {d : WithBot ℕ∞} {n m : ℕ}
    (h : d + (n : WithBot ℕ∞) ≤ ((m + n : ℕ) : WithBot ℕ∞)) : d ≤ (m : WithBot ℕ∞) := by
  induction d with
  | bot => exact bot_le
  | coe p =>
    rw [show ((n : ℕ) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl,
      ← WithBot.coe_add, show (((m + n : ℕ)) : WithBot ℕ∞) = (((m + n : ℕ) : ℕ∞) :
        WithBot ℕ∞) from rfl, WithBot.coe_le_coe] at h
    rw [show ((m : ℕ) : WithBot ℕ∞) = ((m : ℕ∞) : WithBot ℕ∞) from rfl, WithBot.coe_le_coe]
    have hn : (n : ℕ∞) ≠ ⊤ := by simp
    rw [show (((m + n : ℕ)) : ℕ∞) = (m : ℕ∞) + (n : ℕ∞) by push_cast; rfl] at h
    exact (WithTop.add_le_add_iff_right hn).mp h

/-- **Clause (3) of Tag 0B1T: the family `C'` meets the constant family `X × ℓ` properly.** The
dimension criterion is the slice bound `dim (C' ∩ (X × ℓ)) ≤ m + 1` together with
`dim C + 1 ≤ dim C'`, the product formulas `dim (ℓ × 𝐏(V)) = dim 𝐏(V) + 1` and
`dim (X × ℓ) = dim X + 1`, and the fibrewise criterion, which supplies `m` with
`m + dim 𝐏(V) ≤ dim C + dim X`. -/
public theorem intersectProperly_criterion_movingFamilySet {ι : Type*} [Fintype ι]
    (b : Module.Basis ι k (lineSpace k V L)) {C X : Set (projectiveSpaceOfModule k V)}
    (hC : IsClosed C) (hCne : C.Nonempty) (hX : IsClosed X) (hXne : X.Nonempty)
    (hL : Module.finrank k (lineSpace k V L) = 2)
    (hCg : ∀ mu : Module.Dual k (lineSpace k V L), mu ≠ 0 →
      C ⊆ (endDomain k V (lineEnd k V L mu) : Set (projectiveSpaceOfModule k V)))
    (hgood : ∀ mu : Module.Dual k (lineSpace k V L), mu ≠ 0 →
      IsGoodEndomorphism k V C X (lineEnd k V L mu))
    (lam : movingLine k V L) (hlam : IsClosed ({lam} : Set (movingLine k V L)))
    (hfib : movingFibre k V L lam hlam (movingFamilySet k V L b C) = C)
    (hirr : IsIrreducible (movingFamilySet k V L b C))
    (hdom : closure ((ambLine k V L).base '' movingFamilySet k V L b C) = Set.univ) :
    topologicalKrullDim ↥(movingFamilySet k V L b C ∩ constantFamily k V L X) +
        topologicalKrullDim (movingAmbient k V L) ≤
      topologicalKrullDim ↥(movingFamilySet k V L b C) +
        topologicalKrullDim ↥(constantFamily k V L X) := by
  -- the dimension of `𝐏(V)`, of `C` and of `X`, as natural numbers
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Module.finrank k V = n + 1 :=
    ⟨Module.finrank k V - 1, by have := Module.finrank_pos (R := k) (M := V); omega⟩
  have hN : topologicalKrullDim (projectiveSpaceOfModule k V) = (n : WithBot ℕ∞) :=
    topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hn
  have hfinite : ∀ {S : Set (projectiveSpaceOfModule k V)}, S.Nonempty →
      ∃ m : ℕ, topologicalKrullDim ↥S = (m : WithBot ℕ∞) := fun hSne =>
    exists_natCast_of_nonempty_of_le hSne (hN ▸ topologicalKrullDim_subspace_le _ _)
  obtain ⟨c, hc⟩ := hfinite hCne
  obtain ⟨x, hx⟩ := hfinite hXne
  -- the fibrewise criterion, read as a bound on the slices
  have hslice : ∀ mu : Module.Dual k (lineSpace k V L), mu ≠ 0 →
      topologicalKrullDim ↥(endProjectionImage k V (lineEnd k V L mu) C ∩ X) +
        (n : WithBot ℕ∞) ≤ (c : WithBot ℕ∞) + (x : WithBot ℕ∞) := by
    intro mu hmu
    obtain ⟨-, hdim⟩ := hgood mu hmu
    rw [← hN]
    refine le_trans hdim (add_le_add ?_ (le_of_eq hx))
    exact le_trans (topologicalKrullDim_endProjectionImage_le k V (lineEnd k V L mu) hC
      (hCg mu hmu)) (le_of_eq hc)
  by_cases hempty : (movingFamilySet k V L b C ∩ constantFamily k V L X) = ∅
  · rw [hempty, (topologicalKrullDim_eq_bot_iff_isEmpty _).mpr (by
      simp only [Set.isEmpty_coe_sort]) ]
    exact le_trans (le_of_eq (by simp)) bot_le
  · -- some slice is nonempty, so `n ≤ c + x`
    obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨z', hz', hz'c⟩ := exists_isClosed_singleton_mem ⟨z, hz⟩
      ((isClosed_movingFamilySet k V L b hC).inter (isClosed_constantFamily k V L X hX))
    have hlamz : IsClosed ({(ambLine k V L).base z'} : Set (movingLine k V L)) :=
      isClosed_singleton_image_of_isClosed_singleton (ambLine k V L)
        (movingAmbientToSpec k V L) (movingLineToSpec k V L) rfl z' hz'c
    obtain ⟨mu, hmu, hmudef⟩ := exists_eq_linearFunctionalPoint k (lineSpace k V L)
      ((ambLine k V L).base z') hlamz
    have hzslice : z' ∈ movingFamilySet k V L b C ∩ constantFamily k V L X ∩
        (ambLine k V L).base ⁻¹' {(ambLine k V L).base z'} := ⟨hz', rfl⟩
    have hsne : (endProjectionImage k V (lineEnd k V L mu) C ∩ X).Nonempty := by
      rw [← movingFibre_movingFamilySet_inter_constantFamily k V L b hC hmu (hCg mu hmu)]
      obtain ⟨y, hy⟩ : z' ∈ Set.range (lineSection k V L
          (linearFunctionalPoint k (lineSpace k V L) mu hmu)
          (linearFunctionalPoint_isClosed k (lineSpace k V L) mu hmu)).base := by
        rw [range_lineSection]
        exact hmudef ▸ rfl
      exact ⟨y, by rw [mem_movingFibre_iff, hy]; exact hz'⟩
    have hnle : n ≤ c + x := by
      obtain ⟨d, hd⟩ : ∃ d : ℕ,
          topologicalKrullDim ↥(endProjectionImage k V (lineEnd k V L mu) C ∩ X) =
            (d : WithBot ℕ∞) := by
        exact exists_natCast_of_nonempty_of_le hsne
          (le_trans (topologicalKrullDim_le_of_subset Set.inter_subset_right) (le_of_eq hx))
      have h2 := hslice mu hmu
      rw [hd] at h2
      rw [show ((d : ℕ) : WithBot ℕ∞) + ((n : ℕ) : WithBot ℕ∞) = (((d + n : ℕ)) : WithBot ℕ∞) by
        push_cast; rfl,
        show ((c : ℕ) : WithBot ℕ∞) + ((x : ℕ) : WithBot ℕ∞) = (((c + x : ℕ)) : WithBot ℕ∞) by
        push_cast; rfl, Nat.cast_le] at h2
      omega
    -- the slice bound with `m := c + x - n`
    have hm : ∀ mu : Module.Dual k (lineSpace k V L), mu ≠ 0 →
        topologicalKrullDim ↥(endProjectionImage k V (lineEnd k V L mu) C ∩ X) ≤
          ((c + x - n : ℕ) : WithBot ℕ∞) := by
      intro nu hnu
      refine le_natCast_of_add_natCast_le (n := n) ?_
      rw [show ((c + x - n + n : ℕ)) = c + x by omega]
      rw [show (((c + x : ℕ)) : WithBot ℕ∞) = ((c : ℕ) : WithBot ℕ∞) + ((x : ℕ) : WithBot ℕ∞) by
        push_cast; rfl]
      exact hslice nu hnu
    have hupper := topologicalKrullDim_movingFamilySet_inter_le k V L b hC hX hL hCg hm
    have hlower := topologicalKrullDim_add_one_le_movingFamilySet k V L b lam hlam hfib hirr
      hdom hL
    rw [topologicalKrullDim_movingAmbient_eq k V L hL,
      topologicalKrullDim_constantFamily' k V L X hX hL, hN, hx]
    have harith : (((c + x - n : ℕ)) : WithBot ℕ∞) + 1 + ((n : WithBot ℕ∞) + 1) =
        ((c : ℕ) : WithBot ℕ∞) + 1 + ((((x : ℕ)) : WithBot ℕ∞) + 1) := by
      have h1 : (((c + x - n : ℕ)) : WithBot ℕ∞) + 1 + ((n : WithBot ℕ∞) + 1) =
          (((c + x - n + 1 + n + 1 : ℕ)) : WithBot ℕ∞) := by push_cast; abel
      have h2 : ((c : ℕ) : WithBot ℕ∞) + 1 + ((((x : ℕ)) : WithBot ℕ∞) + 1) =
          (((c + 1 + x + 1 : ℕ)) : WithBot ℕ∞) := by push_cast; abel
      rw [h1, h2, show (c + x - n + 1 + n + 1 : ℕ) = c + 1 + x + 1 by omega]
    calc topologicalKrullDim ↥(movingFamilySet k V L b C ∩ constantFamily k V L X) +
          ((n : WithBot ℕ∞) + 1)
        ≤ (((c + x - n : ℕ)) : WithBot ℕ∞) + 1 + ((n : WithBot ℕ∞) + 1) :=
          add_le_add hupper le_rfl
      _ = ((c : ℕ) : WithBot ℕ∞) + 1 + ((((x : ℕ)) : WithBot ℕ∞) + 1) := harith
      _ ≤ topologicalKrullDim ↥(movingFamilySet k V L b C) +
            ((((x : ℕ)) : WithBot ℕ∞) + 1) := by
          refine add_le_add ?_ le_rfl
          rw [← hc]
          exact hlower

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
