module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.CartesianTransport

/-!
# Transporting the base-change comparison, at a module universe above the ring universe

`Stacks.PresheafOfModules.bijective_restrictionBaseChange_restrictScalars_pushforward₀_iff` says
that the base-change comparison of a presheaf of modules is unchanged by restricting the module
along a functor and moving its scalars along an isomorphism of presheaves of rings; it is stated
with the sections of the module in the universe of the rings. This file states it with the
sections in an arbitrary universe `max m r` above it, which is where the modules of a ringed site
live once their sections are allowed to be as large as the site, as for the modules of Stacks
06WJ at module universe `u + 1`.

## Main results

* `bijective_restrictionBaseChange_restrictScalars_pushforward₀_iff_freeModuleUniverse`: the
  transport, at module sections in `Type (max m r)`.

## References

* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.PresheafOfModules

universe u v u' v' r m

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- **The base-change comparison after restriction along a functor and an isomorphism of rings,
at a module universe above the ring universe.** Let `q : D ⥤ C`, and let `ψ : R' ⟶ q.op ⋙ R` be
an isomorphism of presheaves of rings on `D`. The module obtained from `M` by restricting along
`q` and then restricting scalars along `ψ` is cartesian over `g` exactly when `M` is cartesian
over `q.op.map g`. This is
`Stacks.PresheafOfModules.bijective_restrictionBaseChange_restrictScalars_pushforward₀_iff` with
the sections of `M` in `Type (max m r)`. -/
theorem bijective_restrictionBaseChange_restrictScalars_pushforward₀_iff_freeModuleUniverse
    (q : D ⥤ C) (R : Cᵒᵖ ⥤ CommRingCat.{r}) (R' : Dᵒᵖ ⥤ CommRingCat.{r})
    (ψ : R' ⋙ forget₂ CommRingCat RingCat ⟶ q.op ⋙ R ⋙ forget₂ CommRingCat RingCat)
    (hψ : ∀ Z, IsIso (ψ.app Z))
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat)) {X Y : Dᵒᵖ}
    (g : X ⟶ Y) :
    Function.Bijective (restrictionBaseChange.{u', v', r, m} (R := R')
      ((_root_.PresheafOfModules.restrictScalars ψ).obj
        ((_root_.PresheafOfModules.pushforward₀ q (R ⋙ forget₂ CommRingCat RingCat)).obj M))
      g) ↔
    Function.Bijective (restrictionBaseChange.{u, v, r, m} (R := R) M (q.op.map g)) := by
  have _ : IsIso (ψ.app X) := hψ X
  have _ : IsIso (ψ.app Y) := hψ Y
  set NM := (_root_.PresheafOfModules.restrictScalars ψ).obj
      ((_root_.PresheafOfModules.pushforward₀ q (R ⋙ forget₂ CommRingCat RingCat)).obj M)
  let _ : Module (R'.obj X) (R'.obj Y) := Module.compHom _ (R'.map g).hom
  let _ : Module (R.obj (q.op.obj X)) (R.obj (q.op.obj Y)) :=
    Module.compHom _ (R.map (q.op.map g)).hom
  let _ : Module (R'.obj X) (M.obj (q.op.obj X)) := Module.compHom _ (ψ.app X).hom
  let u := Stacks.RingSquare.tensorMap (P := M.obj (q.op.obj X)) (R'.map g).hom
    (R.map (q.op.map g)).hom
    (asIso (ψ.app X)).ringCatIsoToRingEquiv (asIso (ψ.app Y)).ringCatIsoToRingEquiv
    (RingHom.congr_fun (congrArg RingCat.Hom.hom (ψ.naturality g)))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  have hu : Function.Bijective u := Stacks.RingSquare.bijective_tensorMap _ _ _ _ _ _ _ _
  have hcomp : ∀ z, (restrictionBaseChange (R := R) M (q.op.map g)).hom (u z)
      = (restrictionBaseChange (R := R') NM g).hom z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul c x =>
      refine Eq.trans (restrictionBaseChange_tmul M (q.op.map g) ((ψ.app Y).hom c) x) ?_
      exact (restrictionBaseChange_tmul NM g c x).symm
    | add z w hz hw =>
      refine Eq.trans (congrArg _ (map_add u z w)) ?_
      refine Eq.trans (map_add (restrictionBaseChange (R := R) M (q.op.map g)).hom _ _) ?_
      exact (congrArg₂ (· + ·) hz hw).trans
        (map_add (restrictionBaseChange (R := R') NM g).hom z w).symm
  have hfun : (⇑(restrictionBaseChange (R := R') NM g).hom)
      = (⇑(restrictionBaseChange (R := R) M (q.op.map g)).hom) ∘ (⇑u) :=
    (funext hcomp).symm
  change Function.Bijective (⇑(restrictionBaseChange (R := R') NM g).hom) ↔ _
  rw [hfun]
  exact Function.Bijective.of_comp_iff _ hu

end Stacks.PresheafOfModules
