module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.BasePointComposition

/-!
# Composition of correspondences and their action on Chow groups

Let `k` be a field and let `X`, `Y`, `Z` be smooth schemes over `k` of constant dimensions
`d`, `e`, `f`. Part (4) of Stacks 0FG0 asserts that composition of correspondences is
compatible with pullback and pushforward of cycles: for `c ∈ Corrʳ(X, Y)` and
`c' ∈ Corrˢ(Y, Z)`,

  `(c' ∘ c)^*(α) = c^*((c')^*(α))`  for `α ∈ CH_m(Z) ⊗ ℚ`,

  `(c' ∘ c)_*(α) = (c')_*(c_*(α))`  for `α ∈ CH^i(X) ⊗ ℚ`.

The source deduces this from parts (1), (2) and (3). For the pullback, write `m = -t`; by (2)
the class `α` is a correspondence `Z ⟶ Spec k` of degree `t` and `γ^*(α)` corresponds to the
composition `α ∘ γ` for every correspondence `γ`, so the identity is the associativity
`α ∘ (c' ∘ c) = (α ∘ c') ∘ c` of (1) with `Spec k` as the fourth scheme. For the pushforward,
by (3) the class `α` is a correspondence `Spec k ⟶ X` of degree `i` and `γ_*(α)` corresponds to
`γ ∘ α`, so the identity is the associativity `(c' ∘ c) ∘ α = c' ∘ (c ∘ α)` with `Spec k` as
the first scheme.

## Main results

* `Stacks.WeilCohomology.correspondencePullback_composition`: `(c' ∘ c)^* = c^* ∘ (c')^*`.
* `Stacks.WeilCohomology.correspondencePushforward_composition`: `(c' ∘ c)_* = (c')_* ∘ c_*`.

## Implementation notes

The constructions of `StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Composition`
take a family `Δ` of Gysin classes of diagonals as an argument, and the two statements are
proved for every family which is associative
(`Stacks.WeilCohomology.DiagonalClassFamily.CompositionAssoc`) and invariant under isomorphisms
(`Stacks.WeilCohomology.DiagonalClassFamily.IsoInvariant`), and, for the pushforward, symmetric
(`Stacks.WeilCohomology.DiagonalClassFamily.IsSymmetric`); these are the properties of the
canonical family which the parts (1), (2) and (3) of Stacks 0FG0 use.

The class `c^*((c')^*(α))` lies in degree `(m - s) - r` and `(c' ∘ c)^*(α)` in degree
`m - (r + s)`; similarly `(c')_*(c_*(α))` has codimension `(i + r) + s` and `(c' ∘ c)_*(α)` has
codimension `i + (r + s)`. These are the same integers written two ways, and are compared
through the base change to `ℚ` of `Stacks.Chow.chowGroupDegreeEquiv`.

## References

* [Stacks Project, Tag 0FG0](https://stacks.math.columbia.edu/tag/0FG0)
* [Stacks Project, Section 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

/-! ### Transport of rational Chow classes along equalities of degrees -/

section Transport

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- Transport of rational Chow classes along `k = k` is the identity. -/
theorem baseChange_chowGroupDegreeEquiv_self {n : ℤ} (h : n = n)
    (x : TensorProduct ℤ ℚ (chowGroup C sX n)) :
    (chowGroupDegreeEquiv C sX h).toIntLinearEquiv.baseChange ℤ ℚ _ _ x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul q y => rfl
  | add x y hx hy => rw [map_add, hx, hy]

/-- Two successive transports of rational Chow classes along equalities of degrees compose to
the transport along the composite equality. -/
theorem baseChange_chowGroupDegreeEquiv_baseChange_chowGroupDegreeEquiv {i j l : ℤ}
    (hij : i = j) (hjl : j = l) (x : TensorProduct ℤ ℚ (chowGroup C sX i)) :
    (chowGroupDegreeEquiv C sX hjl).toIntLinearEquiv.baseChange ℤ ℚ _ _
        ((chowGroupDegreeEquiv C sX hij).toIntLinearEquiv.baseChange ℤ ℚ _ _ x) =
      (chowGroupDegreeEquiv C sX (hij.trans hjl)).toIntLinearEquiv.baseChange ℤ ℚ _ _ x := by
  subst hij hjl
  simp only [baseChange_chowGroupDegreeEquiv_self]

end Transport

section Calculus

variable (k : Type u) [Field k] {X Y Z : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)
  (sZ : Z ⟶ (fieldChowSituation k).S)
  [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType sZ]

/-- Transport of degrees commutes with the identification
`CH_{-a}(X) ⊗ ℚ = Corrᵃ(X, Spec k)` of Stacks 0FG0 (2). -/
theorem correspondenceCongr_correspondenceToPointEquiv {a a' : ℤ} (h : a = a')
    (x : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sX (-a))) :
    correspondenceCongr k sX (𝟙 _) h (correspondenceToPointEquiv _ sX a x) =
      correspondenceToPointEquiv _ sX a'
        ((chowGroupDegreeEquiv _ sX (by rw [h])).toIntLinearEquiv.baseChange ℤ ℚ _ _ x) := by
  subst h
  rw [baseChange_chowGroupDegreeEquiv_self]
  exact baseChange_chowGroupDegreeEquiv_self _ _ _ _

/-- Transport of degrees commutes with the identification
`CH^a(X) ⊗ ℚ = Corrᵃ(Spec k, X)` of Stacks 0FG0 (3). -/
theorem correspondenceCongr_correspondenceFromPointEquiv (d : ℤ) {a a' : ℤ} (h : a = a')
    (x : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sX (d - a))) :
    correspondenceCongr k (𝟙 _) sX h (correspondenceFromPointEquiv _ sX d a x) =
      correspondenceFromPointEquiv _ sX d a'
        ((chowGroupDegreeEquiv _ sX (by rw [h])).toIntLinearEquiv.baseChange ℤ ℚ _ _ x) := by
  subst h
  rw [baseChange_chowGroupDegreeEquiv_self]
  exact baseChange_chowGroupDegreeEquiv_self _ _ _ _

variable [Smooth sX] [IsSeparated sX] [Smooth sY] [IsSeparated sY] [Smooth sZ]
    [IsSeparated sZ] (Δ : DiagonalClassFamily k)

omit [IsSeparated sX] [IsSeparated sY] in
/-- Pullback by a correspondence commutes with transport of degrees. -/
theorem correspondencePullback_baseChange_chowGroupDegreeEquiv [IsProper sY] {d e : ℕ}
    (hX : RelativeDimension sX d) (hY : RelativeDimension sY e) (r : ℤ) {m m' : ℤ}
    (h : m = m') (c : Correspondence (fieldChowSituation k) sX sY e r)
    (β : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sY m)) :
    correspondencePullback k sX sY Δ hX hY r m' c
        ((chowGroupDegreeEquiv _ sY h).toIntLinearEquiv.baseChange ℤ ℚ _ _ β) =
      (chowGroupDegreeEquiv _ sX (by rw [h])).toIntLinearEquiv.baseChange ℤ ℚ _ _
        (correspondencePullback k sX sY Δ hX hY r m c β) := by
  subst h
  simp only [baseChange_chowGroupDegreeEquiv_self]

/-- **Stacks 0FG0 (4), pullback.** For an associative and iso-invariant family of diagonal
classes, `c ∈ Corrʳ(X, Y)`, `c' ∈ Corrˢ(Y, Z)` and `α ∈ CH_m(Z) ⊗ ℚ`,
`(c' ∘ c)^*(α) = c^*((c')^*(α))`, the degrees `m - (r + s)` and `(m - s) - r` being identified. -/
theorem correspondencePullback_composition (hassoc : Δ.CompositionAssoc) (hΔ : Δ.IsoInvariant)
    [IsProper sY] [IsProper sZ] {d e f : ℕ} (hX : RelativeDimension sX d)
    (hY : RelativeDimension sY e) (hZ : RelativeDimension sZ f) (r s m : ℤ)
    (c : Correspondence (fieldChowSituation k) sX sY e r)
    (c' : Correspondence (fieldChowSituation k) sY sZ f s)
    (α : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sZ m)) :
    correspondencePullback k sX sZ Δ hX hZ (r + s) m (composition k sX sY sZ Δ hX hY hZ r s c c')
        α =
      (chowGroupDegreeEquiv _ sX (show m - s - r = m - (r + s) by ring)).toIntLinearEquiv.baseChange
        ℤ ℚ _ _ (correspondencePullback k sX sY Δ hX hY r (m - s) c
          (correspondencePullback k sY sZ Δ hY hZ s m c' α)) := by
  obtain ⟨t, rfl⟩ : ∃ t, m = -t := ⟨-m, (neg_neg m).symm⟩
  set E := (chowGroupDegreeEquiv (fieldChowSituation k) sX
    (show -t - (r + s) = -(r + (s + t)) by ring)).toIntLinearEquiv.baseChange ℤ ℚ _ _ with hE
  apply E.injective
  apply (correspondenceToPointEquiv _ sX (r + (s + t))).injective
  have h2 := correspondenceToPointEquiv_correspondencePullback sX sZ hΔ hX hZ (r + s) t
    (composition k sX sY sZ Δ hX hY hZ r s c c') α
  have h2' := correspondenceToPointEquiv_correspondencePullback sY sZ hΔ hY hZ s t c' α
  have h2'' := correspondenceToPointEquiv_correspondencePullback sX sY hΔ hX hY r (s + t) c
    ((chowGroupDegreeEquiv _ sY (show -t - s = -(s + t) by ring)).toIntLinearEquiv.baseChange
      ℤ ℚ _ _ (correspondencePullback k sY sZ Δ hY hZ s (-t) c' α))
  have h1 := hassoc sX sY sZ (𝟙 _) hX hY hZ (relativeDimension_identity _) r s t c c'
    (correspondenceToPointEquiv _ sZ t α)
  rw [← h2, correspondenceCongr_correspondenceToPointEquiv, ← h2', ← h2'',
    baseChange_chowGroupDegreeEquiv_baseChange_chowGroupDegreeEquiv] at h1
  rw [hE, h1, correspondencePullback_baseChange_chowGroupDegreeEquiv,
    baseChange_chowGroupDegreeEquiv_baseChange_chowGroupDegreeEquiv,
    baseChange_chowGroupDegreeEquiv_baseChange_chowGroupDegreeEquiv]

/-- **Stacks 0FG0 (4), pushforward.** For an associative, iso-invariant and symmetric family of
diagonal classes, `c ∈ Corrʳ(X, Y)`, `c' ∈ Corrˢ(Y, Z)` and `α ∈ CH^i(X) ⊗ ℚ`,
`(c' ∘ c)_*(α) = (c')_*(c_*(α))`, the codimensions `i + (r + s)` and `(i + r) + s` being
identified. -/
theorem correspondencePushforward_composition (hassoc : Δ.CompositionAssoc)
    (hΔ : Δ.IsoInvariant) (hΔs : Δ.IsSymmetric) [IsProper sX] [IsProper sY] {d e f : ℕ}
    (hX : RelativeDimension sX d) (hY : RelativeDimension sY e) (hZ : RelativeDimension sZ f)
    (r s i : ℤ) (c : Correspondence (fieldChowSituation k) sX sY e r)
    (c' : Correspondence (fieldChowSituation k) sY sZ f s)
    (α : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sX ((d : ℤ) - i))) :
    correspondencePushforward k sX sZ Δ hX hZ (r + s) i
        (composition k sX sY sZ Δ hX hY hZ r s c c') α =
      (chowGroupDegreeEquiv _ sZ
          (show (f : ℤ) - (i + r + s) = f - (i + (r + s)) by ring)).toIntLinearEquiv.baseChange
        ℤ ℚ _ _ (correspondencePushforward k sY sZ Δ hY hZ s (i + r) c'
          (correspondencePushforward k sX sY Δ hX hY r i c α)) := by
  apply (correspondenceFromPointEquiv _ sZ f (i + (r + s))).injective
  have h3 := correspondenceFromPointEquiv_correspondencePushforward sX sZ hΔ hΔs hX hZ i (r + s)
    (composition k sX sY sZ Δ hX hY hZ r s c c') α
  have h3' := correspondenceFromPointEquiv_correspondencePushforward sX sY hΔ hΔs hX hY i r c α
  have h3'' := correspondenceFromPointEquiv_correspondencePushforward sY sZ hΔ hΔs hY hZ (i + r)
    s c' (correspondencePushforward k sX sY Δ hX hY r i c α)
  have h1 := hassoc (𝟙 _) sX sY sZ (relativeDimension_identity _) hX hY hZ i r s
    (correspondenceFromPointEquiv _ sX d i α) c c'
  rw [← h3', ← h3'', correspondenceCongr_correspondenceFromPointEquiv, ← h3] at h1
  rw [← h1]

end Calculus

end Stacks.WeilCohomology
