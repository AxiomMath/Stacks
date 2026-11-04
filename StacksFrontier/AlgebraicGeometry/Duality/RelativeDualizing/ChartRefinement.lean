module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Common basic-open refinements of two affine opens

Two affine opens `V₁` and `V₂` of a scheme `Y` overlap in an open which is in general affine on
neither chart's terms. This file produces, around any point of any prescribed open inside the
overlap, a single open which is simultaneously a principal open of `V₁` and a principal open of
`V₂`, and which sits inside the prescribed open. Such opens therefore form a basis of the overlap
`V₁ ⊓ V₂`, indexed by the pairs of functions presenting them.

The point of the second form is that a comparison of two quasi-coherent sheaves of modules is
usually only available on opens that are principal on *both* charts, while the gluing data such a
comparison feeds wants it on an arbitrary open of the overlap. The basis statement is exactly the
hypothesis of `Stacks.Modules.exists_sectionEquiv_of_basis`, which bridges that gap.

Despite its location this file is pure scheme topology: nothing here mentions duality.

## Main results

* `Stacks.Discriminant.exists_common_basicOpen_le`: given affine opens `V₁ V₂` of `Y`, an open
  `O ≤ V₁ ⊓ V₂` and a point `y ∈ O`, there are `g₁ : Γ(Y, V₁)` and `g₂ : Γ(Y, V₂)` cutting out the
  *same* open, which contains `y` and lies inside `O`.
* `Stacks.Discriminant.common_basicOpen_isBasis`: the same statement packaged as the basis
  property of the family indexed by such pairs, in the shape
  `Stacks.Modules.exists_sectionEquiv_of_basis` consumes.
* `Stacks.Discriminant.exists_basicOpen_eq_of_le`: a principal open of one affine chart which
  lies inside a principal open of a second affine chart is a principal open of that second
  chart. This is the re-presentation step, isolated.
* `Stacks.Discriminant.exists_common_basicOpen_le₃` and
  `Stacks.Discriminant.common_basicOpen_isBasis₃`: the same for three affine opens. A cocycle
  identity for comparisons extended from the two-chart bases has to be checked on a basis of a
  triple intersection, and the two-chart bases of the three pairs are different families, so the
  three-chart refinement is what the check is run on.

## Implementation notes

`AlgebraicGeometry.exists_basicOpen_le_affine_inter` already produces a common presentation
`Y.basicOpen a₁ = Y.basicOpen a₂` of one open around `y`, but with no control over where that open
sits; `AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le` produces an open inside a prescribed
one, but presented on a single chart only. Combining them is a two-step shrink: first get the
common open `Y.basicOpen a₁`, then shrink inside `O ⊓ Y.basicOpen a₁` on the chart `V₁`, giving
`g₁` with `Y.basicOpen g₁ ≤ Y.basicOpen a₂`.

Re-presenting `Y.basicOpen g₁` on the chart `V₂` is then immediate from
`AlgebraicGeometry.IsAffineOpen.basicOpen_basicOpen_is_basicOpen`: restricting `g₁` to
`Y.basicOpen a₂` does not change the open it cuts out, and a principal open of a principal open of
an affine open is a principal open of that affine open. No localization computation is needed here
— that lemma is where it already happened.

## References

* `Mathlib/AlgebraicGeometry/AffineScheme.lean`, for the two existence results combined here and
  for `IsAffineOpen.basicOpen_basicOpen_is_basicOpen`.
* `StacksFrontier/AlgebraicGeometry/Modules/BasisSectionExtension.lean`, for the consumer of the
  basis form.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Discriminant

/-- A principal open of `V₁` inside a principal open `Y.basicOpen a ≤ V₁` of `V₂` is principal
on `V₂`. -/
private theorem exists_basicOpen_eq_of_le_aux {Y : Scheme.{u}} (V₁ V₂ : Y.affineOpens)
    (g : Γ(Y, V₁.1)) (a : Γ(Y, V₂.1)) (ha : Y.basicOpen a ≤ V₁.1)
    (h : Y.basicOpen g ≤ Y.basicOpen a) :
    ∃ g₂ : Γ(Y, V₂.1), Y.basicOpen g₂ = Y.basicOpen g := by
  obtain ⟨g₂, hg₂⟩ := V₂.2.basicOpen_basicOpen_is_basicOpen a (Y.presheaf.map (homOfLE ha).op g)
  exact ⟨g₂, by rw [hg₂, Scheme.basicOpen_res, inf_eq_right.mpr h]⟩

/-- Two affine opens of a scheme admit a common basic-open refinement inside any prescribed open
around any common point: given affine opens `V₁ V₂` of `Y`, an open `O ≤ V₁ ⊓ V₂` and a point
`y ∈ O`, there are `g₁ : Γ(Y, V₁)` and `g₂ : Γ(Y, V₂)` with `Y.basicOpen g₁ = Y.basicOpen g₂`,
`y ∈ Y.basicOpen g₁` and `Y.basicOpen g₁ ≤ O`. -/
public theorem exists_common_basicOpen_le {Y : Scheme.{u}} (V₁ V₂ : Y.affineOpens)
    (O : Y.Opens) (hO : O ≤ V₁.1 ⊓ V₂.1) (y : Y) (hy : y ∈ O) :
    ∃ (g₁ : Γ(Y, V₁.1)) (g₂ : Γ(Y, V₂.1)),
      Y.basicOpen g₁ = Y.basicOpen g₂ ∧ y ∈ Y.basicOpen g₁ ∧ Y.basicOpen g₁ ≤ O := by
  obtain ⟨hy₁, hy₂⟩ := hO hy
  obtain ⟨a₁, a₂, ha, hya⟩ :=
    AlgebraicGeometry.exists_basicOpen_le_affine_inter V₁.2 V₂.2 y ⟨hy₁, hy₂⟩
  obtain ⟨g₁, hg₁le, hyg₁⟩ :=
    V₁.2.exists_basicOpen_le (V := O ⊓ Y.basicOpen a₁) ⟨y, ⟨hy, hya⟩⟩ hy₁
  have hle₂ : Y.basicOpen a₂ ≤ V₁.1 := by rw [← ha]; exact Y.basicOpen_le a₁
  have hsub : Y.basicOpen g₁ ≤ Y.basicOpen a₂ := by
    rw [← ha]; exact hg₁le.trans inf_le_right
  obtain ⟨g₂, hg₂⟩ := exists_basicOpen_eq_of_le_aux V₁ V₂ g₁ a₂ hle₂ hsub
  exact ⟨g₁, g₂, hg₂.symm, hyg₁, hg₁le.trans inf_le_left⟩

/-- The common basic-open refinements of two affine opens form a basis of their intersection,
indexed by the pairs of functions presenting one open on either chart. -/
public theorem common_basicOpen_isBasis {Y : Scheme.{u}} (V₁ V₂ : Y.affineOpens) :
    ∀ O : Y.Opens, O ≤ V₁.1 ⊓ V₂.1 → ∀ y ∈ O,
      ∃ p : {q : Γ(Y, V₁.1) × Γ(Y, V₂.1) // Y.basicOpen q.1 = Y.basicOpen q.2},
        y ∈ Y.basicOpen p.1.1 ∧ Y.basicOpen p.1.1 ≤ O := by
  intro O hO y hy
  obtain ⟨g₁, g₂, he, hyg₁, hg₁le⟩ := exists_common_basicOpen_le V₁ V₂ O hO y hy
  exact ⟨⟨(g₁, g₂), he⟩, hyg₁, hg₁le⟩

/-- **Re-presenting a principal open on a second affine chart.** A principal open of an affine
chart `V₁` which lies inside a principal open `Y.basicOpen a` of a second affine chart `V₂` (with
that principal open inside `V₁`) is itself a principal open of `V₂`. -/
public theorem exists_basicOpen_eq_of_le {Y : Scheme.{u}} (V₁ V₂ : Y.affineOpens)
    (g : Γ(Y, V₁.1)) (a : Γ(Y, V₂.1)) (ha : Y.basicOpen a ≤ V₁.1)
    (h : Y.basicOpen g ≤ Y.basicOpen a) :
    ∃ g₂ : Γ(Y, V₂.1), Y.basicOpen g₂ = Y.basicOpen g :=
  exists_basicOpen_eq_of_le_aux V₁ V₂ g a ha h

/-- **Three affine opens admit a common basic-open refinement.** The three-chart form of
`exists_common_basicOpen_le`: one open, presented as a principal open of each of `V₁`, `V₂` and
`V₃`, containing a prescribed common point and inside a prescribed open of the triple
intersection. -/
public theorem exists_common_basicOpen_le₃ {Y : Scheme.{u}} (V₁ V₂ V₃ : Y.affineOpens)
    (O : Y.Opens) (hO : O ≤ V₁.1 ⊓ V₂.1 ⊓ V₃.1) (y : Y) (hy : y ∈ O) :
    ∃ (g₁ : Γ(Y, V₁.1)) (g₂ : Γ(Y, V₂.1)) (g₃ : Γ(Y, V₃.1)),
      Y.basicOpen g₁ = Y.basicOpen g₂ ∧ Y.basicOpen g₁ = Y.basicOpen g₃ ∧
        y ∈ Y.basicOpen g₁ ∧ Y.basicOpen g₁ ≤ O := by
  obtain ⟨b₁, b₂, hb, hyb, hbO⟩ :=
    exists_common_basicOpen_le V₁ V₂ O (le_trans hO inf_le_left) y hy
  have h3 : Y.basicOpen b₁ ≤ V₁.1 ⊓ V₃.1 :=
    le_inf (Y.basicOpen_le b₁) (hbO.trans (le_trans hO inf_le_right))
  obtain ⟨g₁, g₃, hg, hyg, hgle⟩ :=
    exists_common_basicOpen_le V₁ V₃ (Y.basicOpen b₁) h3 y hyb
  have hb₂le : Y.basicOpen b₂ ≤ V₁.1 := by rw [← hb]; exact Y.basicOpen_le b₁
  have hsub : Y.basicOpen g₁ ≤ Y.basicOpen b₂ := by rw [← hb]; exact hgle
  obtain ⟨g₂, hg₂⟩ := exists_basicOpen_eq_of_le V₁ V₂ g₁ b₂ hb₂le hsub
  exact ⟨g₁, g₂, g₃, hg₂.symm, hg, hyg, hgle.trans hbO⟩

/-- The common basic-open refinements of three affine opens form a basis of their triple
intersection. This is what a cocycle identity for comparisons extended from the two-chart basis
is proved on. -/
public theorem common_basicOpen_isBasis₃ {Y : Scheme.{u}} (V₁ V₂ V₃ : Y.affineOpens) :
    ∀ O : Y.Opens, O ≤ V₁.1 ⊓ V₂.1 ⊓ V₃.1 → ∀ y ∈ O,
      ∃ p : {q : Γ(Y, V₁.1) × Γ(Y, V₂.1) × Γ(Y, V₃.1) //
          Y.basicOpen q.1 = Y.basicOpen q.2.1 ∧ Y.basicOpen q.1 = Y.basicOpen q.2.2},
        y ∈ Y.basicOpen p.1.1 ∧ Y.basicOpen p.1.1 ≤ O := by
  intro O hO y hy
  obtain ⟨g₁, g₂, g₃, he₂, he₃, hyg, hgle⟩ := exists_common_basicOpen_le₃ V₁ V₂ V₃ O hO y hy
  exact ⟨⟨(g₁, g₂, g₃), he₂, he₃⟩, hyg, hgle⟩

end Stacks.Discriminant

end
