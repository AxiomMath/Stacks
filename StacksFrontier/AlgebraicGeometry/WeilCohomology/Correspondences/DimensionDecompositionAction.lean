module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DimensionDecompositionBasePoint

/-!
# Composition of correspondences of mixed dimension and their action on Chow groups

Let `k` be a field and let `X`, `Y`, `Z` be schemes smooth over `k`, not necessarily
equidimensional. Part (4) of Stacks 0FG0 asserts that composition of correspondences is
compatible with pullback and pushforward of cycles: for `c ∈ Corrʳ(X, Y)` and
`c' ∈ Corrˢ(Y, Z)`,

  `(c' ∘ c)^*(α) = c^*((c')^*(α))`  for `α ∈ CH_m(Z) ⊗ ℚ`,

  `(c' ∘ c)_*(α) = (c')_*(c_*(α))`  for `α ∈ CH^i(X) ⊗ ℚ`.

The source deduces this from parts (1), (2) and (3), and so does this file, for the mixed
correspondences `Stacks.WeilCohomology.Corr`: by (2) a class `α ∈ CH_{-t}(Z) ⊗ ℚ` is a
correspondence `Z ⟶ Spec k` and `γ^*(α)` corresponds to `α ∘ γ`, so the first identity is the
associativity `α ∘ (c' ∘ c) = (α ∘ c') ∘ c` of (1) with `Spec k` as the fourth scheme; by (3) a
class `α ∈ CH^i(X) ⊗ ℚ` is a correspondence `Spec k ⟶ X` and `γ_*(α)` corresponds to `γ ∘ α`,
so the second identity is the associativity with `Spec k` as the first scheme.

## Main definitions

* `Stacks.WeilCohomology.codimChowCongr`: the identification `CH^i(X) ⊗ ℚ ≃ CH^{i'}(X) ⊗ ℚ` for
  `i = i'`.

## Main results

* `Stacks.WeilCohomology.pullback_comp`: `(c' ∘ c)^* = c^* ∘ (c')^*`.
* `Stacks.WeilCohomology.pushforward_comp`: `(c' ∘ c)_* = (c')_* ∘ c_*`.

## Implementation notes

The intersection products are formed with an arbitrary family `Δ` of diagonal classes; the
hypotheses are associativity of equidimensional composition (`Δ.CompositionAssoc`), invariance
under isomorphisms and, for the pushforward, symmetry of the products, which are what (1), (2)
and (3) are proved from.

## References

* [Stacks Project, Tag 0FG0](https://stacks.math.columbia.edu/tag/0FG0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Chow

universe u

namespace Stacks.WeilCohomology

variable (k : Type u) [Field k] {X Y Z : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)
  (sZ : Z ⟶ (fieldChowSituation k).S)
  [Smooth sX] [IsSeparated sX] [Smooth sY] [IsSeparated sY] [Smooth sZ] [IsSeparated sZ]

/-! ### Transport along equalities of degrees -/

omit [IsSeparated sX] [IsSeparated sY] in
/-- Transport of mixed correspondences along `r = r` is the identity. -/
theorem corrCongr_self {r : ℤ} (h : r = r) (c : Corr k sX sY r) : corrCongr k sX sY h c = c := by
  induction c using Corr.induction_on with
  | zero => exact LinearEquiv.map_zero _
  | add a b ha hb => rw [map_add, ha, hb]
  | lof d e x =>
    rw [corrCongr_lof_lof]
    congr 2
    induction x using TensorProduct.inductionOn with
    | tmul q y => rfl
    | add a b ha hb => rw [map_add, ha, hb]

/-- The identification `CH^i(X) ⊗ ℚ ≃ CH^{i'}(X) ⊗ ℚ` for `i = i'`, blockwise the transport of
`Stacks.Chow.chowGroupDegreeEquiv`. -/
def codimChowCongr {i i' : ℤ} (h : i = i') : CodimChow k sX i ≃ₗ[ℚ] CodimChow k sX i' :=
  DirectSum.congrLinearEquiv fun d ↦
    (chowGroupDegreeEquiv (fieldChowSituation k) (partBase sX d)
      (by rw [h])).toIntLinearEquiv.baseChange ℤ ℚ _ _

omit [IsSeparated sX] in
/-- On the summand indexed by `d`, `codimChowCongr` acts as the base change to `ℚ` of the
transport of degrees `Stacks.Chow.chowGroupDegreeEquiv`. -/
@[simp]
theorem codimChowCongr_lof {i i' : ℤ} (h : i = i') (d : ℕ)
    (a : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) (partBase sX d) ((d : ℤ) - i))) :
    codimChowCongr k sX h (DirectSum.lof ℚ ℕ _ d a) =
      DirectSum.lof ℚ ℕ _ d ((chowGroupDegreeEquiv (fieldChowSituation k) (partBase sX d)
        (by rw [h])).toIntLinearEquiv.baseChange ℤ ℚ _ _ a) := by
  simp [codimChowCongr, DirectSum.coe_congrLinearEquiv]
  rfl

omit [IsSeparated sX] in
/-- Transport of degrees commutes with the identification
`CH_{-r}(X) ⊗ ℚ = Corrʳ(X, Spec k)` of Stacks 0FG0 (2). -/
theorem corrCongr_corrToPointEquiv [IsProper sX] {r r' : ℤ} (h : r = r')
    (x : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sX (-r))) :
    corrCongr k sX (𝟙 _) h (corrToPointEquiv k sX r x) =
      corrToPointEquiv k sX r'
        ((chowGroupDegreeEquiv _ sX (by rw [h])).toIntLinearEquiv.baseChange ℤ ℚ _ _ x) := by
  subst h
  rw [corrCongr_self, baseChange_chowGroupDegreeEquiv_self]

omit [IsSeparated sX] in
/-- Transport of degrees commutes with the identification
`CH^r(X) ⊗ ℚ = Corrʳ(Spec k, X)` of Stacks 0FG0 (3). -/
theorem corrCongr_corrFromPointEquiv {r r' : ℤ} (h : r = r') (x : CodimChow k sX r) :
    corrCongr k (𝟙 _) sX h (corrFromPointEquiv k sX r x) =
      corrFromPointEquiv k sX r' (codimChowCongr k sX h x) := by
  subst h
  rw [corrCongr_self]
  congr 1
  induction x using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, ← ha, ← hb]
  | of d a =>
    rw [← DirectSum.lof_eq_of ℚ, codimChowCongr_lof, baseChange_chowGroupDegreeEquiv_self]

variable (Δ : DiagonalClassFamily k)

omit [IsSeparated sX] [IsSeparated sY] in
/-- Pullback by a mixed correspondence commutes with the transport of degrees. -/
theorem pullback_baseChange_chowGroupDegreeEquiv [IsProper sX] [IsProper sY] (r : ℤ) {m m' : ℤ}
    (h : m = m') (c : Corr k sX sY r)
    (β : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sY m)) :
    pullback k sX sY Δ r m' c
        ((chowGroupDegreeEquiv _ sY h).toIntLinearEquiv.baseChange ℤ ℚ _ _ β) =
      (chowGroupDegreeEquiv _ sX (by rw [h])).toIntLinearEquiv.baseChange ℤ ℚ _ _
        (pullback k sX sY Δ r m c β) := by
  subst h
  simp only [baseChange_chowGroupDegreeEquiv_self]

/-! ### Stacks 0FG0 (4) -/

/-- **Stacks 0FG0 (4), pullback**, for smooth proper `X`, `Y`, `Z` over `k` of arbitrary
dimension: for `c ∈ Corrʳ(X, Y)`, `c' ∈ Corrˢ(Y, Z)` and `α ∈ CH_m(Z) ⊗ ℚ`,
`(c' ∘ c)^*(α) = c^*((c')^*(α))`, the degrees `m - (r + s)` and `(m - s) - r` being identified,
for a family of diagonal classes whose equidimensional composition is associative and which is
invariant under isomorphisms. -/
theorem pullback_comp (hassoc : Δ.CompositionAssoc) (hΔ : Δ.IsoInvariant) [IsProper sX]
    [IsProper sY] [IsProper sZ] (r s m : ℤ) (c : Corr k sX sY r) (c' : Corr k sY sZ s)
    (α : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sZ m)) :
    Stacks.WeilCohomology.pullback k sX sZ Δ (r + s) m (comp k sX sY sZ Δ r s c c') α =
      (chowGroupDegreeEquiv _ sX (show m - s - r = m - (r + s) by ring)).toIntLinearEquiv.baseChange
        ℤ ℚ _ _ (Stacks.WeilCohomology.pullback k sX sY Δ r (m - s) c
          (Stacks.WeilCohomology.pullback k sY sZ Δ s m c' α)) := by
  obtain ⟨t, rfl⟩ : ∃ t, m = -t := ⟨-m, (neg_neg m).symm⟩
  have h2' := corrToPointEquiv_pullback k Δ sZ sY hΔ s t c' α
  have h2 := corrToPointEquiv_pullback k Δ sZ sX hΔ (r + s) t (comp k sX sY sZ Δ r s c c') α
  have h2'' := corrToPointEquiv_pullback k Δ sY sX hΔ r (s + t) c
    ((chowGroupDegreeEquiv _ sY (show -t - s = -(s + t) by ring)).toIntLinearEquiv.baseChange
      ℤ ℚ _ _ (Stacks.WeilCohomology.pullback k sY sZ Δ s (-t) c' α))
  have h1 := comp_assoc k sX sY sZ (𝟙 _) Δ hassoc r s t c c' (corrToPointEquiv k sZ t α)
  have e1 : (chowGroupDegreeEquiv (fieldChowSituation k) sX
      (show -t - s - r = -(r + (s + t)) by ring)).toIntLinearEquiv.baseChange ℤ ℚ _ _
        (Stacks.WeilCohomology.pullback k sX sY Δ r (-t - s) c
          (Stacks.WeilCohomology.pullback k sY sZ Δ s (-t) c' α)) =
      (chowGroupDegreeEquiv (fieldChowSituation k) sX
        (show -(s + t) - r = -(r + (s + t)) by ring)).toIntLinearEquiv.baseChange ℤ ℚ _ _
        (Stacks.WeilCohomology.pullback k sX sY Δ r (-(s + t)) c
          ((chowGroupDegreeEquiv _ sY (show -t - s = -(s + t) by ring)).toIntLinearEquiv.baseChange
            ℤ ℚ _ _ (Stacks.WeilCohomology.pullback k sY sZ Δ s (-t) c' α))) := by
    rw [pullback_baseChange_chowGroupDegreeEquiv,
      baseChange_chowGroupDegreeEquiv_baseChange_chowGroupDegreeEquiv]
  apply ((chowGroupDegreeEquiv (fieldChowSituation k) sX
    (show -t - (r + s) = -(r + (s + t)) by ring)).toIntLinearEquiv.baseChange ℤ ℚ _ _).injective
  apply (corrToPointEquiv k sX (r + (s + t))).injective
  rw [baseChange_chowGroupDegreeEquiv_baseChange_chowGroupDegreeEquiv, e1, h2'', h2', ← h1, ← h2,
    corrCongr_corrToPointEquiv, baseChange_chowGroupDegreeEquiv_baseChange_chowGroupDegreeEquiv]

/-- **Stacks 0FG0 (4), pushforward**, for smooth `X`, `Y`, `Z` over `k` of arbitrary dimension,
`X` and `Y` proper: for `c ∈ Corrʳ(X, Y)`, `c' ∈ Corrˢ(Y, Z)` and `α ∈ CH^i(X) ⊗ ℚ`,
`(c' ∘ c)_*(α) = (c')_*(c_*(α))`, the codimensions `i + (r + s)` and `(i + r) + s` being
identified, for a family of diagonal classes whose equidimensional composition is associative and
which is invariant under isomorphisms and symmetric. -/
theorem pushforward_comp (hassoc : Δ.CompositionAssoc) (hΔ : Δ.IsoInvariant)
    (hΔs : Δ.IsSymmetric) [IsProper sX] [IsProper sY] (r s i : ℤ) (c : Corr k sX sY r)
    (c' : Corr k sY sZ s) (α : CodimChow k sX i) :
    pushforward k sX sZ Δ (r + s) i (comp k sX sY sZ Δ r s c c') α =
      codimChowCongr k sZ (add_assoc i r s)
        (pushforward k sY sZ Δ s (i + r) c' (pushforward k sX sY Δ r i c α)) := by
  apply (corrFromPointEquiv k sZ (i + (r + s))).injective
  rw [corrFromPointEquiv_pushforward k Δ sX sZ hΔ hΔs, ← corrCongr_corrFromPointEquiv,
    corrFromPointEquiv_pushforward k Δ sY sZ hΔ hΔs,
    corrFromPointEquiv_pushforward k Δ sX sY hΔ hΔs,
    comp_assoc k (𝟙 _) sX sY sZ Δ hassoc i r s]

end Stacks.WeilCohomology

end
