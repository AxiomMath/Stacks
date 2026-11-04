module

public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Cocycle

/-!
# An invertible module from a single unit on a two-chart cover

Let `(X, 𝒪_X)` be a ringed space covered by two opens `U₀` and `U₁`. A unit
`u ∈ 𝒪_X(U₀ ∩ U₁)^*` is already a complete gluing datum: there is no third chart, so the cocycle
condition carries no content beyond the group laws, and restricting `u` to the opens inside both
charts produces a `Stacks.SheafOfModules.UnitTransitionCocycle`. Gluing it gives an invertible
sheaf of `𝒪_X`-modules.

This is the shape in which a line bundle on a two-chart cover is written down in practice: `ℙ¹`
glued from two affine lines, and the modules `L_n` of
[Stacks, Tag 0EHE](https://stacks.math.columbia.edu/tag/0EHE), glued from `A_x/t^nA_x` and
`A_y/t^nA_y` along a unit of `A_{xy}/t^nA_{xy}` over the punctured spectrum of `A/t^nA`.

## Main definitions

* `Stacks.SheafOfModules.twoChartFamily`: the two-element family of opens `{U₀, U₁}`, indexed by
  `ULift Bool` so that the index type lives in the universe the gluing data requires.
* `Stacks.SheafOfModules.overlapUnit`: the restriction of the overlap unit to an open contained
  in both charts.
* `Stacks.SheafOfModules.twoChartCocycle`: the unit transition cocycle of a single overlap unit.

## Main results

* `Stacks.SheafOfModules.isInvertible_glue_twoChartCocycle`: the module glued from one unit on
  the overlap of a two-chart cover of the whole space is invertible.
* `Stacks.SheafOfModules.isInvertibleModule_glue_twoChartCocycle`: the same on a scheme, in the
  spelling `Stacks.Ample.IsInvertibleModule` that `Stacks.Coherent.IsInvertibleAdic` asks for.

## Implementation notes

The off-diagonal transitions are the restriction of `u` and of `u⁻¹`, and the diagonal ones are
`1`; the four fields are then proved by exhausting the two or three indices, every case reducing
to a group law in `𝒪_X(V)^*` or to `overlapUnit_restrict`. The two proofs that a given open lies
in `U₀ ⊓ U₁` which the cocycle identity produces on its two sides are different terms of the same
`Prop`, hence definitionally equal, so no transport is needed.

A scheme `Y` is a ringed space with `Y.toRingedSpace`, and the glued module is then an object of
`Y.Modules` with no transport: `Y.ringCatSheaf` and the sheaf of rings the gluing is indexed by
agree by `rfl`, the sheaf condition being a `Prop` field. So the scheme-level statement is the
ringed-space one, restated.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

section

variable {X : RingedSpace.{u, u}}

/-- The two-element family of opens `{U₀, U₁}`, indexed by `ULift Bool` so that the index type
lies in the universe the gluing data requires. -/
def twoChartFamily (U₀ U₁ : Opens X.carrier) : ULift.{u} Bool → Opens X.carrier :=
  fun i => bif i.down then U₁ else U₀

/-- The open of `twoChartFamily U₀ U₁` at the index `false` is `U₀`. -/
@[simp]
lemma twoChartFamily_up_false (U₀ U₁ : Opens X.carrier) :
    twoChartFamily U₀ U₁ ⟨false⟩ = U₀ := rfl

/-- The open of `twoChartFamily U₀ U₁` at the index `true` is `U₁`. -/
@[simp]
lemma twoChartFamily_up_true (U₀ U₁ : Opens X.carrier) :
    twoChartFamily U₀ U₁ ⟨true⟩ = U₁ := rfl

/-- The union of the two opens of `twoChartFamily U₀ U₁` is `U₀ ⊔ U₁`. -/
lemma iSup_twoChartFamily (U₀ U₁ : Opens X.carrier) :
    ⨆ i, twoChartFamily U₀ U₁ i = U₀ ⊔ U₁ :=
  le_antisymm (iSup_le (by rintro ⟨b⟩; cases b; exacts [le_sup_left, le_sup_right]))
    (sup_le (le_iSup (twoChartFamily U₀ U₁) ⟨false⟩) (le_iSup (twoChartFamily U₀ U₁) ⟨true⟩))

variable {U₀ U₁ : Opens X.carrier}

/-- The restriction of a unit on the overlap `U₀ ∩ U₁` to an open contained in both charts. -/
def overlapUnit (u : (X.presheaf.obj (op (U₀ ⊓ U₁)))ˣ) (V : Opens X.carrier)
    (h : V ≤ U₀ ⊓ U₁) : (X.presheaf.obj (op V))ˣ :=
  Units.map (X.presheaf.map (homOfLE h).op).hom u

/-- The restriction of `overlapUnit u V hV` to an open `W ≤ V` is `overlapUnit u W`. -/
lemma overlapUnit_restrict (u : (X.presheaf.obj (op (U₀ ⊓ U₁)))ˣ) {V W : Opens X.carrier}
    (hV : V ≤ U₀ ⊓ U₁) (h : W ≤ V) :
    Units.map (X.presheaf.map (homOfLE h).op).hom (overlapUnit u V hV) =
      overlapUnit u W (h.trans hV) := by
  refine Units.ext ?_
  have hcomp := X.presheaf.map_comp (homOfLE hV).op (homOfLE h).op
  rw [show (homOfLE hV).op ≫ (homOfLE h).op = (homOfLE (h.trans hV)).op from
    Subsingleton.elim _ _] at hcomp
  show (X.presheaf.map (homOfLE h).op).hom ((X.presheaf.map (homOfLE hV).op).hom u.val) =
    (X.presheaf.map (homOfLE (h.trans hV)).op).hom u.val
  simpa only [ConcreteCategory.comp_apply] using (congrArg (fun φ => φ u.val) hcomp).symm

/-- A single unit on the overlap of a two-chart cover, read as a unit transition cocycle: the
off-diagonal transitions are the restrictions of `u` and of `u⁻¹`, the diagonal ones are `1`. -/
def twoChartCocycle (u : (X.presheaf.obj (op (U₀ ⊓ U₁)))ˣ) :
    UnitTransitionCocycle X (twoChartFamily U₀ U₁) where
  transition i j V hi hj :=
    match i, j, hi, hj with
    | ⟨false⟩, ⟨false⟩, _, _ => 1
    | ⟨true⟩, ⟨true⟩, _, _ => 1
    | ⟨false⟩, ⟨true⟩, hi, hj => overlapUnit u V (le_inf hi hj)
    | ⟨true⟩, ⟨false⟩, hi, hj => (overlapUnit u V (le_inf hj hi))⁻¹
  restrict := by
    rintro ⟨i⟩ ⟨j⟩ V W hi hj h
    cases i <;> cases j
    · exact map_one _
    · exact overlapUnit_restrict u _ h
    · rw [map_inv]
      exact congrArg (·⁻¹) (overlapUnit_restrict u _ h)
    · exact map_one _
  symm := by
    rintro ⟨i⟩ ⟨j⟩ V hi hj
    cases i <;> cases j
    · exact inv_one.symm
    · rfl
    · exact (inv_inv _).symm
    · exact inv_one.symm
  cocycle := by
    rintro ⟨i⟩ ⟨j⟩ ⟨k⟩ V hi hj hk
    cases i <;> cases j <;> cases k
    · exact one_mul _
    · exact mul_one _
    · exact inv_mul_cancel _
    · exact one_mul _
    · exact one_mul _
    · exact mul_inv_cancel _
    · exact mul_one _
    · exact one_mul _

/-- **A unit on the overlap of a two-chart cover of a ringed space glues to an invertible
module.** This is clause 1 of Tag 0B8M for the two-chart gluing datum of a single unit. -/
theorem isInvertible_glue_twoChartCocycle (u : (X.presheaf.obj (op (U₀ ⊓ U₁)))ˣ)
    (hU : (⊤ : Opens X.carrier) ≤ U₀ ⊔ U₁) :
    IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property (twoChartCocycle u).glue :=
  (twoChartCocycle u).isInvertible_glue (by rw [iSup_twoChartFamily]; exact hU)

end

/-- **A unit on the overlap of a two-open cover of a scheme glues to an invertible module.**
This is `Stacks.SheafOfModules.isInvertible_glue_twoChartCocycle` in the spelling
`Stacks.Ample.IsInvertibleModule`, the one `Stacks.Coherent.IsInvertibleAdic` asks for. -/
theorem isInvertibleModule_glue_twoChartCocycle {Y : Scheme.{u}} {V₀ V₁ : Y.Opens}
    (u : Γ(Y, V₀ ⊓ V₁)ˣ) (hY : (⊤ : Y.Opens) ≤ V₀ ⊔ V₁) :
    Stacks.Ample.IsInvertibleModule Y
      (twoChartCocycle (X := Y.toRingedSpace) (U₀ := V₀) (U₁ := V₁) u).glue :=
  isInvertible_glue_twoChartCocycle u hY

end Stacks.SheafOfModules

end
