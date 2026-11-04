module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# The affine covering number of an open subscheme

For an open subscheme `U` of a scheme `X`, `X.affineCoverNum U` is the least number of affine
opens needed to cover `U`. It is the quantity written `t(U)` in [Stacks, Tag 01XI] and
[Stacks, Tag 071L], and it is finite exactly when `U` is quasi-compact.

Affine opens of the scheme `U` are the same thing as affine opens of `X` contained in `U`, so
taking the affine opens here to be affine opens of the ambient scheme loses nothing.

## Main definitions

* `AlgebraicGeometry.Scheme.affineCoverNum`: the least `n` for which `U` is the union of `n`
  affine opens, or `0` if there is no such `n`.

## Main results

* `AlgebraicGeometry.exists_finite_affineOpen_cover`: a quasi-compact open is a finite union of
  affine opens.
* `AlgebraicGeometry.Scheme.exists_affineCover_affineCoverNum`: a quasi-compact open admits a
  cover by exactly `X.affineCoverNum U` affine opens.
* `AlgebraicGeometry.Scheme.affineCoverNum_le`: any cover of `U` by `n` affine opens bounds
  `X.affineCoverNum U` by `n`.
* `AlgebraicGeometry.Scheme.eq_bot_of_affineCoverNum_eq_zero`: a quasi-compact open whose
  affine covering number is `0` is empty.
* `AlgebraicGeometry.isCompact_finsetInf`: in a quasi-separated scheme a nonempty finite
  intersection of quasi-compact opens is quasi-compact.

## References

* [Stacks Project, Tag 01XI](https://stacks.math.columbia.edu/tag/01XI)
* [Stacks Project, Tag 071L](https://stacks.math.columbia.edu/tag/071L)
-/

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A quasi-compact open of a scheme is a finite union of affine opens.** The affine opens
form a basis of the topology, so every point of `U` has an affine open neighbourhood inside
`U`, and quasi-compactness extracts a finite subfamily. -/
theorem exists_finite_affineOpen_cover {X : Scheme.{u}} (U : X.Opens)
    (hU : IsCompact (U : Set X)) :
    ∃ (n : ℕ) (V : Fin n → X.Opens), (∀ i, IsAffineOpen (V i)) ∧ ⨆ i, V i = U := by
  classical
  have hnbhd : ∀ x : U, ∃ W : X.Opens, IsAffineOpen W ∧ (x : X) ∈ W ∧ W ≤ U := by
    intro x
    obtain ⟨-, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open x.2 U.2
    exact ⟨W, hW, hxW, hWU⟩
  choose W hWaff hxW hWU using hnbhd
  obtain ⟨s, hs⟩ := hU.elim_finite_subcover (fun x : U ↦ (W x : Set X))
    (fun x ↦ (W x).2) fun x hx ↦ Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩
  refine ⟨s.card, fun i ↦ W ((s.equivFin.symm i : U)), fun i ↦ hWaff _, le_antisymm ?_ ?_⟩
  · exact iSup_le fun i ↦ hWU _
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hs hx
    obtain ⟨y, rfl⟩ := hy
    obtain ⟨hy, hxy⟩ := Set.mem_iUnion.mp hxy
    exact le_iSup (fun i ↦ W ((s.equivFin.symm i : U))) (s.equivFin ⟨y, hy⟩) (by simpa using hxy)

/-- **The affine covering number of an open subscheme**, the quantity `t(U)` of
[Stacks, Tag 01XI]: the least number of affine opens needed to cover `U`. It is `0` when `U` is
not a finite union of affine opens, which by `exists_finite_affineOpen_cover` happens only when
`U` fails to be quasi-compact. -/
noncomputable def Scheme.affineCoverNum (X : Scheme.{u}) (U : X.Opens) : ℕ :=
  sInf {n : ℕ | ∃ V : Fin n → X.Opens, (∀ i, IsAffineOpen (V i)) ∧ ⨆ i, V i = U}

/-- A cover of `U` by `n` affine opens bounds the affine covering number of `U` by `n`. -/
theorem Scheme.affineCoverNum_le {X : Scheme.{u}} {U : X.Opens} {n : ℕ} (V : Fin n → X.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hcov : ⨆ i, V i = U) : X.affineCoverNum U ≤ n :=
  Nat.sInf_le ⟨V, hV, hcov⟩

/-- A quasi-compact open admits a cover by exactly `X.affineCoverNum U` affine opens: the
infimum defining the affine covering number is attained. -/
theorem Scheme.exists_affineCover_affineCoverNum {X : Scheme.{u}} (U : X.Opens)
    (hU : IsCompact (U : Set X)) :
    ∃ V : Fin (X.affineCoverNum U) → X.Opens, (∀ i, IsAffineOpen (V i)) ∧ ⨆ i, V i = U := by
  obtain ⟨n, V, hV, hcov⟩ := exists_finite_affineOpen_cover U hU
  have hne : {m : ℕ | ∃ V : Fin m → X.Opens, (∀ i, IsAffineOpen (V i)) ∧ ⨆ i, V i = U}.Nonempty :=
    ⟨n, V, hV, hcov⟩
  exact Nat.sInf_mem hne

/-- A quasi-compact open with affine covering number `0` is empty: the attained cover has no
members. -/
theorem Scheme.eq_bot_of_affineCoverNum_eq_zero {X : Scheme.{u}} (W : X.Opens)
    (hW : IsCompact (W : Set X)) (h : X.affineCoverNum W = 0) : W = ⊥ := by
  have hcover := Scheme.exists_affineCover_affineCoverNum W hW
  rw [h] at hcover
  obtain ⟨V, -, hcov⟩ := hcover
  simpa using hcov.symm

/-- The empty open is covered by no affine opens at all, so its affine covering number is `0`. -/
@[simp]
theorem Scheme.affineCoverNum_bot (X : Scheme.{u}) : X.affineCoverNum ⊥ = 0 :=
  Nat.le_zero.mp (Scheme.affineCoverNum_le (n := 0) (fun i ↦ i.elim0) (fun i ↦ i.elim0) (by simp))

/-- In a quasi-separated scheme a nonempty finite intersection of quasi-compact opens is
quasi-compact. -/
theorem isCompact_finsetInf {X : Scheme.{u}} [QuasiSeparatedSpace X] {ι : Type*}
    (U : ι → X.Opens) (hU : ∀ i, IsCompact (U i : Set X)) {s : Finset ι} (hs : s.Nonempty) :
    IsCompact ((s.inf U : X.Opens) : Set X) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simpa using hU i
  | cons i s hi hs ih =>
      rw [Finset.inf_cons]
      have hsets : ((U i ⊓ s.inf U : X.Opens) : Set X) = (U i : Set X) ∩ (s.inf U : X.Opens) :=
        rfl
      rw [hsets]
      exact (hU i).inter_of_isOpen ih (U i).2 (s.inf U : X.Opens).2

end AlgebraicGeometry
