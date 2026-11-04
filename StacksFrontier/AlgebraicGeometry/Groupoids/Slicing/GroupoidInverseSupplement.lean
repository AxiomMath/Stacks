module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.GroupoidInverse
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.FieldExtensionEvaluation
import all StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.GroupoidInverse

/-!
# Inverses and cancellation of composites of generalized arrows

For a groupoid scheme `G` over `S` and `T` over `S`, we compute the inverse of the composite
`G.compose a b w` of two generalized arrows `a b : T ⟶ G.arrows`, and show that a generalized
arrow may be cancelled from the left of such a composite.

## Main results

* `AlgebraicGeometry.groupoidCompose_comp_inverse`: the inverse of a composite of generalized
  arrows is the composite of their inverses in the reverse order.
* `AlgebraicGeometry.groupoidCompose_cancel_left`: if `G.compose a b w = G.compose a b' w'`,
  then `b = b'`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The inverse of the composite of two generalized arrows of a groupoid scheme is the composite
of their inverses in the reverse order. -/
theorem groupoidCompose_comp_inverse {S : Scheme.{u}} (G : GroupoidScheme S) {T : Over S}
    (a b : T ⟶ G.arrows) (w : a ≫ G.source = b ≫ G.target)
    (w' : (b ≫ G.inverse) ≫ G.source = (a ≫ G.inverse) ≫ G.target) :
    G.compose a b w ≫ G.inverse = G.compose (b ≫ G.inverse) (a ≫ G.inverse) w' := by
  let x : G.Evaluation T := b ≫ G.source
  let y : G.Evaluation T := b ≫ G.target
  let z : G.Evaluation T := a ≫ G.target
  let f : x ⟶ y := ⟨b, rfl, rfl⟩
  let g : y ⟶ z := ⟨a, w, rfl⟩
  have hL : (CategoryTheory.inv (f ≫ g)).arrow = G.compose a b w ≫ G.inverse := by
    rw [← Groupoid.inv_eq_inv]
    rfl
  have hR : (CategoryTheory.inv g ≫ CategoryTheory.inv f).arrow =
      G.compose (b ≫ G.inverse) (a ≫ G.inverse) w' := by
    rw [← Groupoid.inv_eq_inv, ← Groupoid.inv_eq_inv]
    rfl
  rw [← hL, ← hR, IsIso.inv_comp]

/-- A generalized arrow of a groupoid scheme may be cancelled from the left of a composite: if
`G.compose a b w = G.compose a b' w'`, then `b = b'`. -/
theorem groupoidCompose_cancel_left {S : Scheme.{u}} (G : GroupoidScheme S) {T : Over S}
    (a b b' : T ⟶ G.arrows) (w : a ≫ G.source = b ≫ G.target)
    (w' : a ≫ G.source = b' ≫ G.target)
    (h : G.compose a b w = G.compose a b' w') : b = b' := by
  have hsource : ∀ (c : T ⟶ G.arrows) (wc : a ≫ G.source = c ≫ G.target),
      G.compose a c wc ≫ G.source = c ≫ G.source := by
    intro c wc
    show (pullback.lift a c wc ≫ G.comp) ≫ G.source = c ≫ G.source
    rw [Category.assoc, G.source_comp, pullback.lift_snd_assoc]
  have hs : b ≫ G.source = b' ≫ G.source := by
    rw [← hsource b w, h, hsource b' w']
  let x : G.Evaluation T := b ≫ G.source
  let y : G.Evaluation T := a ≫ G.source
  let z : G.Evaluation T := a ≫ G.target
  let u : x ⟶ y := ⟨b, rfl, w.symm⟩
  let u' : x ⟶ y := ⟨b', hs.symm, w'.symm⟩
  let v : y ⟶ z := ⟨a, rfl, rfl⟩
  have huv : u ≫ v = u' ≫ v := GroupoidScheme.EvaluationHom.ext h
  exact congrArg GroupoidScheme.EvaluationHom.arrow ((cancel_mono v).1 huv)

end AlgebraicGeometry

end

