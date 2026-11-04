module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.ExtendScalarsCancel
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsModelComp

/-!
# The two spellings of the composition isomorphism for extension of scalars

Extending scalars along `f : R →+* A` and then along `g : A →+* B` is extending them along
`g ∘ f`. This file identifies two constructions of that isomorphism of functors:

* `StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp`, the conjugate of
  `ModuleCat.restrictScalarsComp` across the two extension/restriction adjunctions;
* `Stacks.ModuleCat.cancelIso`, built from `TensorProduct.AlgebraTensorModule.cancelBaseChange`.

## Main results

* `StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp_hom_app_one_tmul` — the
  composition isomorphism sends `1 ⊗ m` to `1 ⊗ (1 ⊗ m)`, at three independent ring universes.
* `StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp_eq_cancelIso_symm` — the two
  constructions agree, at one universe.
* `StacksDraft.DerivedExtensionScalarsModelComp.cancelIso_eq_extendScalarsComp_symm` — the same
  for a composite ring map spelled some other way than `g.comp f`, up to the transport along the
  equality of the two ring maps.

## References

* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped ChangeOfRings TensorProduct

namespace StacksDraft.DerivedExtensionScalarsModelComp

universe u₁ u₂ u₃ v u

section Elt

variable {R : Type u₁} {A : Type u₂} {B : Type u₃} [CommRing R] [CommRing A] [CommRing B]

/-- **The composition isomorphism on the elements `1 ⊗ m`.**  At three independent ring universes,
`StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp` sends `1 ⊗ m` to `1 ⊗ (1 ⊗ m)`.
-/
theorem extendScalarsComp_hom_app_one_tmul (f : R →+* A) (g : A →+* B)
    (M : ModuleCat.{max v u₁ u₂ u₃} R) (m : M) :
    (extendScalarsComp.{u₁, u₂, u₃, v} f g).hom.app M ((1 : B) ⊗ₜ[R, g.comp f] m)
      = (1 : B) ⊗ₜ[A, g]
          (show (ModuleCat.extendScalars.{u₁, u₂, max v u₁ u₂ u₃} f).obj M from
            (1 : A) ⊗ₜ[R, f] m) :=
  (congrFun (congrArg (fun φ : M ⟶ _ => (ModuleCat.Hom.hom φ).toFun)
    (unit_extendScalarsComp'.{u₁, u₂, u₃, v} f g M)) m).symm

end Elt

section Cancel

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]

/-- **The two spellings of the composition isomorphism agree.**  The conjugate of
`ModuleCat.restrictScalarsComp` across the two extension/restriction adjunctions is the inverse
of the cancellation isomorphism built from
`TensorProduct.AlgebraTensorModule.cancelBaseChange`. -/
theorem extendScalarsComp_eq_cancelIso_symm (f : R →+* A) (g : A →+* B) :
    extendScalarsComp.{u, u, u, u} f g =
      (Stacks.ModuleCat.cancelIso f g (g.comp f) (fun _ => rfl)).symm := by
  refine Iso.ext (NatTrans.ext (funext fun M => (Iso.comp_hom_eq_id
    (Stacks.ModuleCat.cancelIsoApp f g (g.comp f) (fun _ => rfl) M)).1 ?_))
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  show (Stacks.ModuleCat.cancelIsoApp f g (g.comp f) (fun _ => rfl) M).hom
      ((extendScalarsComp.{u, u, u, u} f g).hom.app M ((1 : B) ⊗ₜ[R, g.comp f] m))
    = (1 : B) ⊗ₜ[R, g.comp f] m
  let _ : Algebra R A := f.toAlgebra
  let _ : Algebra R B := (g.comp f).toAlgebra
  let gAlg : A →ₐ[R] B := { g with commutes' := fun _ => rfl }
  have h1 := Stacks.ModuleCat.cancelIsoApp_hom_one_tmul f g (g.comp f) (fun _ => rfl) M gAlg
    (fun _ => rfl)
    (show (ModuleCat.extendScalars.{u, u, u} f).obj M from (1 : A) ⊗ₜ[R, f] m)
  have h2 : LinearMap.rTensor (↑M) gAlg.toLinearMap
      (show (ModuleCat.extendScalars.{u, u, u} f).obj M from (1 : A) ⊗ₜ[R, f] m)
        = (1 : B) ⊗ₜ[R, g.comp f] m := by
    show gAlg (1 : A) ⊗ₜ[R, g.comp f] m = _
    rw [map_one]
  rw [extendScalarsComp_hom_app_one_tmul]
  exact h1.trans h2

/-- `StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp_eq_cancelIso_symm` for a
composite ring map `p` spelled some other way than `g.comp f`, up to the transport along the
equality `g.comp f = p`. -/
theorem cancelIso_eq_extendScalarsComp_symm (f : R →+* A) (g : A →+* B) (p : R →+* B)
    (hp : ∀ x, p x = g (f x)) :
    Stacks.ModuleCat.cancelIso f g p hp =
      (extendScalarsComp.{u, u, u, u} f g).symm ≪≫
        eqToIso (congrArg (fun φ : R →+* B => ModuleCat.extendScalars.{u, u, u} φ)
          (RingHom.ext fun x => (hp x).symm)) := by
  have hcomp : g.comp f = p := RingHom.ext fun x => (hp x).symm
  subst hcomp
  refine Iso.ext ?_
  rw [extendScalarsComp_eq_cancelIso_symm]
  exact (Category.comp_id _).symm

end Cancel

end StacksDraft.DerivedExtensionScalarsModelComp

end
