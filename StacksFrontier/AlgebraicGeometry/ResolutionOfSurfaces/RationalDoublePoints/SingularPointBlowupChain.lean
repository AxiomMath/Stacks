module

public import Mathlib.Logic.Hydra
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Properties.RegularLocus

/-!
# Sequences of blowups in singular closed points

A *singular point blowup chain* of a scheme `X`, with stages subject to a property `P`, is a
finite composition `Xₙ → Xₙ₋₁ → … → X₀ = X` in which each `Xᵢ₊₁ → Xᵢ` is the blowup of `Xᵢ` at a
closed point of `Xᵢ` at which `Xᵢ` is singular, and every `Xᵢ` satisfies `P`. This is the shape of
the conclusion of [Stacks, Tag 0BGE].

The existence of such a chain ending in a regular scheme is reduced here to a termination
statement: if a multiset of elements of a type with a well-founded relation is attached to every
scheme satisfying `P`, which is empty only for a regular scheme, and some blowup in a singular
closed point replaces one element of it by finitely many smaller ones, then every scheme
satisfying `P` has a chain ending in a regular scheme. The ordering on multisets is the one of
`Relation.CutExpand`, whose well-foundedness is `WellFounded.cutExpand`.

## Main definitions

* `AlgebraicGeometry.SingularPointBlowupChain`: a finite sequence of blowups in singular closed
  points with stages satisfying a property, indexed by its composite morphism.

## Main results

* `AlgebraicGeometry.SingularPointBlowupChain.prepend`: a chain of the blowup of `X` in a singular
  closed point is, after composing with the blowup morphism, a chain of `X`.
* `AlgebraicGeometry.exists_singularPointBlowupChain_isRegular_of_wellFounded`: the reduction to
  a well-founded multiset measure.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A finite sequence of blowups in singular closed points, all of whose stages satisfy `P`,
indexed by its composite morphism to `X`: either the identity of `X`, for `X` satisfying `P`, or
the blowup of the last stage of such a sequence at a closed point at which that stage is
singular, the blowup again satisfying `P`. -/
inductive SingularPointBlowupChain (P : Scheme.{u} → Prop) (X : Scheme.{u}) :
    ∀ Y : Scheme.{u}, (Y ⟶ X) → Prop
  | refl (hX : P X) : SingularPointBlowupChain P X X (𝟙 X)
  | step {W : Scheme.{u}} {h : W ⟶ X} (hh : SingularPointBlowupChain P X W h) (w : W)
      (hw : IsClosed ({w} : Set W)) (hsing : w ∈ singularLocus W)
      (hP : P (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))) :
      SingularPointBlowupChain P X
        (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩))
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩) ≫ h)

namespace SingularPointBlowupChain

variable {P : Scheme.{u} → Prop}

/-- The first stage of a chain satisfies the property of the chain. -/
theorem base {X Y : Scheme.{u}} {f : Y ⟶ X} (h : SingularPointBlowupChain P X Y f) : P X := by
  induction h with
  | refl hX => exact hX
  | step _ _ _ _ _ ih => exact ih

/-- The last stage of a chain satisfies the property of the chain. -/
theorem last {X Y : Scheme.{u}} {f : Y ⟶ X} (h : SingularPointBlowupChain P X Y f) : P Y := by
  cases h with
  | refl hX => exact hX
  | step _ _ _ _ hP => exact hP

/-- **Prepending a blowup.** A chain of the blowup of `X` at a singular closed point `x`, composed
with the blowup morphism, is a chain of `X`, provided `X` itself satisfies the property. -/
theorem prepend {X : Scheme.{u}} (hX : P X) (x : X) (hx : IsClosed ({x} : Set X))
    (hsing : x ∈ singularLocus X) {Y : Scheme.{u}}
    {g : Y ⟶ blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)}
    (h : SingularPointBlowupChain P (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩))
      Y g) :
    SingularPointBlowupChain P X Y
      (g ≫ blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)) := by
  induction h with
  | refl hB =>
    rw [Category.id_comp, ← Category.comp_id
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩))]
    exact step (refl hX) x hx hsing hB
  | step _ w hw hsingw hP ih =>
    rw [Category.assoc]
    exact step ih w hw hsingw hP

end SingularPointBlowupChain

/-- **A well-founded measure produces a chain ending in a regular scheme.** Attach to every
scheme a multiset `M W` of elements of a type with a well-founded relation `r`. Suppose that a
scheme satisfying `P` with empty multiset is regular, and that a scheme `W` satisfying `P` with
nonempty multiset has a singular closed point `w` whose blowup satisfies `P` and has a multiset
obtained from `M W` by replacing one element by finitely many `r`-smaller ones. Then every scheme
satisfying `P` has a chain of blowups in singular closed points, with stages satisfying `P`,
ending in a regular scheme. -/
theorem exists_singularPointBlowupChain_isRegular_of_wellFounded {α : Type*}
    {r : α → α → Prop} (hr : WellFounded r) (P : Scheme.{u} → Prop)
    (M : Scheme.{u} → Multiset α)
    (hreg : ∀ W : Scheme.{u}, P W → M W = 0 → IsRegular W)
    (hstep : ∀ W : Scheme.{u}, P W → M W ≠ 0 →
      ∃ (w : W) (hw : IsClosed ({w} : Set W)), w ∈ singularLocus W ∧
        P (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩)) ∧
        Relation.CutExpand r (M (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩)))
          (M W))
    (X : Scheme.{u}) (hX : P X) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), SingularPointBlowupChain P X Y f ∧ IsRegular Y := by
  induction X using (InvImage.wf M hr.cutExpand).induction with
  | _ X ih =>
    by_cases hM : M X = 0
    · exact ⟨X, 𝟙 X, .refl hX, hreg X hX hM⟩
    · obtain ⟨w, hw, hsing, hP, hlt⟩ := hstep X hX hM
      obtain ⟨Y, g, hchain, hY⟩ := ih _ hlt hP
      exact ⟨Y, _, hchain.prepend hX w hw hsing, hY⟩

end AlgebraicGeometry
