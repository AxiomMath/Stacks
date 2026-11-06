module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLift
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Raising the universe of the coefficient rings commutes with the objectwise tensor product

The tensor product of two modules over a commutative ring is unchanged by raising the universe
of the ring and of the two modules: there is a canonical isomorphism

`ULift M ⊗[ULift A] ULift N ≅ ULift (M ⊗[A] N)`,

linear over `ULift A`, which on pure tensors lifts a pure tensor.  It is natural in the ring and
the modules, so it identifies the objectwise tensor product formed over the universe lift of the
structure presheaf of a ringed site, applied to the universe lifts of two presheaves of modules,
with the universe lift of the objectwise tensor product formed over the structure presheaf
itself.

This is the comparison that transports the theory of tensor products of quasi-coherent modules,
which is available only when the coefficient universe dominates the site, to a pair of modules
whose sections lie in two universes unrelated to the site: raising the universe of the rings is
an isomorphism of categories of presheaves of modules
(`Stacks.Modules.presheafRingULiftEquiv`), raising the universe of the sections commutes with
sheafification (`PresheafOfModules.sheafificationUliftObjIso`), and the present file is what
makes the two compatible with the tensor product.

## Main definitions

* `TensorProduct.ringULiftEquiv`: **`ULift M ⊗[ULift A] ULift N ≅ ULift (M ⊗[A] N)`**, linear
  over `ULift A`.
* `Stacks.Modules.tensorRingULiftAppEquiv` and `Stacks.Modules.tensorRingULiftAppIso`: the same
  comparison at an object of a ringed site, as a linear equivalence resp. an isomorphism of
  modules over the sections of the structure presheaf there.
* `Stacks.Modules.tensorPresheafRingULiftDownIso`: **raising the universe of the coefficient
  rings commutes with the objectwise tensor product of presheaves of modules.**
* `PresheafOfModules.uliftSectionsCompIso`: two successive universe lifts of the sections of a
  presheaf of modules, the second dominating the first, compose to the second.

## Main results

* `TensorProduct.ringULiftEquiv_tmul` and `TensorProduct.ringULiftInvAddHom_tmul`: the
  comparison and its inverse send a pure tensor of lifted sections to the lift of the pure
  tensor, and back.

## Implementation notes

The comparison is built from `TensorProduct.lift` over `ULift A` in one direction and from
`TensorProduct.liftAddHom` over `A` in the other.  The second direction cannot be a
`TensorProduct.lift`: that would need `M ⊗[A] N` to be a module over `ULift A`, whereas the
tensor product over `ULift A` of two `A`-modules carries no `A`-module structure that instance
synthesis can find — the `A`-action on it is the restriction of scalars along `ULift.ringEquiv`,
which is how `Stacks.Modules.presheafRingULiftDown` installs it, and is not an instance.  So the
inverse is produced as a morphism of additive groups and its semilinearity is proved separately
by induction on the tensor product, which is `TensorProduct.ringULiftInvAddHom_smul`.

For the same reason the comparison at an object of the site is built as a structure instance
whose `map_smul'` field is the `ULift A`-linearity of the comparison evaluated at a lifted
scalar: the two actions agree by definition, the action of `A` on either side being the
restriction of the action of `ULift A`.  The definitions whose unfolding that argument needs are
made reducible locally with `attribute [local implicit_reducible]`.

The universes are arranged so that the statements typecheck with no hypothesis relating them.
The two factors have sections in independent universes `m` and `n`; the universe lift of the
sections of the first is by an amount containing `n` and that of the second by an amount
containing `m`, so that both land in one universe, as the objectwise tensor product over the
lifted rings requires; and the universe lift of the tensor product is by the common part of the
two amounts.  Writing the lifting amounts in that form is what makes the two sides of the
comparison have sections in the same universe by universe normalisation alone.

## References

* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe so sm r w m n d c

namespace TensorProduct

variable (A : Type r) [CommRing A] (M : Type m) [AddCommGroup M] [Module A M]
  (N : Type n) [AddCommGroup N] [Module A N]

/-- The comparison from the tensor product of the universe lifts of two modules over the
universe lift of the ring to the universe lift of their tensor product: on a pure tensor of
lifted sections it is the lift of the pure tensor. -/
noncomputable def ringULiftHom :
    (ULift.{max d n} M ⊗[ULift.{c} A] ULift.{max d m} N) →ₗ[ULift.{c} A]
      ULift.{d} (M ⊗[A] N) :=
  TensorProduct.lift
    (LinearMap.mk₂ (ULift.{c} A) (fun x y ↦ ULift.up (x.down ⊗ₜ[A] y.down))
      (fun _ _ _ ↦ congrArg ULift.up (TensorProduct.add_tmul _ _ _))
      (fun s x y ↦ congrArg ULift.up (TensorProduct.smul_tmul' s.down x.down y.down))
      (fun _ _ _ ↦ congrArg ULift.up (TensorProduct.tmul_add _ _ _))
      (fun s x y ↦ congrArg ULift.up (TensorProduct.tmul_smul s.down x.down y.down)))

/-- The inverse comparison as a morphism of additive groups: it sends a pure tensor to the pure
tensor of the lifted factors.  It cannot be produced by `TensorProduct.lift`, the target
carrying no module structure over the ring that instance synthesis can find. -/
noncomputable def ringULiftInvAddHom :
    (M ⊗[A] N) →+ (ULift.{max d n} M ⊗[ULift.{c} A] ULift.{max d m} N) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun x ↦ AddMonoidHom.mk'
        (fun y ↦ (ULift.up.{max d n} x : ULift.{max d n} M) ⊗ₜ[ULift.{c} A]
          (ULift.up.{max d m} y : ULift.{max d m} N))
        (fun _ _ ↦ TensorProduct.tmul_add _ _ _))
      (fun _ _ ↦ by ext y; exact TensorProduct.add_tmul _ _ _))
    (fun s _ _ ↦ TensorProduct.smul_tmul (ULift.up.{c} s) _ _)

/-- The inverse comparison sends a pure tensor to the pure tensor of the lifted factors. -/
theorem ringULiftInvAddHom_tmul (x : M) (y : N) :
    ringULiftInvAddHom.{r, m, n, d, c} A M N (x ⊗ₜ[A] y) =
      (ULift.up.{max d n} x : ULift.{max d n} M) ⊗ₜ[ULift.{c} A]
        (ULift.up.{max d m} y : ULift.{max d m} N) :=
  rfl

/-- The inverse comparison is semilinear for the universe lift of the ring: scaling by an
element of the ring is scaling by its lift. -/
theorem ringULiftInvAddHom_smul (s : A) (z : M ⊗[A] N) :
    ringULiftInvAddHom.{r, m, n, d, c} A M N (s • z) =
      (ULift.up.{c} s) • ringULiftInvAddHom.{r, m, n, d, c} A M N z := by
  refine TensorProduct.inductionOn z (fun x y ↦ ?_) (fun p q hp hq ↦ ?_)
  · rw [TensorProduct.smul_tmul', ringULiftInvAddHom_tmul, ringULiftInvAddHom_tmul]
    exact TensorProduct.smul_tmul' (ULift.up.{c} s) (ULift.up.{max d n} x) (ULift.up.{max d m} y)
  · rw [smul_add, map_add, map_add, hp, hq, smul_add]

/-- The comparison undoes the inverse comparison. -/
theorem ringULiftHom_ringULiftInvAddHom (z : M ⊗[A] N) :
    ringULiftHom.{r, m, n, d, c} A M N (ringULiftInvAddHom.{r, m, n, d, c} A M N z) =
      ULift.up.{d} z := by
  refine TensorProduct.inductionOn z (fun x y ↦ ?_)
    (fun p q hp hq ↦ ?_)
  · rw [ringULiftInvAddHom_tmul]
    rfl
  · rw [map_add, map_add, hp, hq]
    rfl

/-- The inverse comparison, as a linear map over the universe lift of the ring. -/
noncomputable def ringULiftInv :
    ULift.{d} (M ⊗[A] N) →ₗ[ULift.{c} A]
      (ULift.{max d n} M ⊗[ULift.{c} A] ULift.{max d m} N) where
  toFun z := ringULiftInvAddHom.{r, m, n, d, c} A M N z.down
  map_add' _ _ := map_add _ _ _
  map_smul' s z := ringULiftInvAddHom_smul.{r, m, n, d, c} A M N s.down z.down

/-- **The tensor product of the universe lifts of two modules over the universe lift of the
ring is the universe lift of their tensor product.** -/
noncomputable def ringULiftEquiv :
    (ULift.{max d n} M ⊗[ULift.{c} A] ULift.{max d m} N) ≃ₗ[ULift.{c} A]
      ULift.{d} (M ⊗[A] N) :=
  LinearEquiv.ofLinearMap (ringULiftHom.{r, m, n, d, c} A M N)
    (ringULiftInv.{r, m, n, d, c} A M N)
    (LinearMap.ext fun z ↦ ringULiftHom_ringULiftInvAddHom.{r, m, n, d, c} A M N z.down)
    (TensorProduct.ext (LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ rfl))

/-- The comparison sends a pure tensor of lifted sections to the lift of the pure tensor. -/
theorem ringULiftEquiv_tmul (x : M) (y : N) :
    ringULiftEquiv.{r, m, n, d, c} A M N
        ((ULift.up.{max d n} x : ULift.{max d n} M) ⊗ₜ[ULift.{c} A]
          (ULift.up.{max d m} y : ULift.{max d m} N)) = ULift.up.{d} (x ⊗ₜ[A] y) :=
  rfl

end TensorProduct

namespace PresheafOfModules

variable {C : Type so} [Category.{sm} C] {R₀ : Cᵒᵖ ⥤ RingCat.{r}}

/-- Two successive universe lifts of the sections of a presheaf of modules, the second
dominating the first, compose to the second. -/
noncomputable def uliftSectionsCompIso (P : PresheafOfModules.{m} R₀) :
    (P.uliftSections.{n}).uliftSections.{max d n} ≅ P.uliftSections.{max d n} :=
  isoMk (fun X ↦ (ULift.moduleEquiv (R := R₀.obj X) (M := ULift.{n} (P.obj X))).trans
      (ULift.moduleEquiv.trans
        (ULift.moduleEquiv (R := R₀.obj X) (M := P.obj X)).symm) |>.toModuleIso)
    (by intro X Y f; exact ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl))

end PresheafOfModules

namespace Stacks.Modules

attribute [local implicit_reducible] ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' PresheafOfModules.presheaf
  presheafRingULiftDown presheafRingULiftDownObj presheafRingULiftUp presheafRingULiftUpObj
  PresheafOfModules.ofPresheaf PresheafOfModules.uliftSections

open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf)

variable {C : Type so} [Category.{sm} C] (𝒪 : Cᵒᵖ ⥤ CommRingCat.{r})
  (F : PresheafOfModules.{m} (structureRingPresheaf 𝒪))
  (G : PresheafOfModules.{n} (structureRingPresheaf 𝒪))

/-- The objectwise tensor product over the universe lift of the structure presheaf of a ringed
site, of the universe lifts of the sections of two presheaves of modules.  Its sections lie in
the universe of the lifted rings. -/
@[sga "4 IV 12.10" "(X), special case"]
noncomputable abbrev tensorPresheafRingULift : PresheafOfModules.{max so sm r w m n}
    (structureRingPresheaf (ringULift.{so, sm, r, max w m n} 𝒪)) :=
  PresheafOfModules.tensorObj (O := ringULift.{so, sm, r, max w m n} 𝒪)
    ((presheafRingULiftUp.{so, sm, r, max w m n, max so sm r w m n} 𝒪).obj
      (F.uliftSections.{max so sm r w n}))
    ((presheafRingULiftUp.{so, sm, r, max w m n, max so sm r w m n} 𝒪).obj
      (G.uliftSections.{max so sm r w m}))

/-- The comparison of `TensorProduct.ringULiftEquiv` at an object of the site: the tensor
product over the lifted rings of the lifted sections is the universe lift of the tensor product
of the sections, linearly over the sections of the structure presheaf there. -/
noncomputable def tensorRingULiftAppEquiv (X : Cᵒᵖ) :
    ((presheafRingULiftDown.{so, sm, r, max w m n, max so sm r w m n} 𝒪).obj
          (tensorPresheafRingULift.{so, sm, r, w, m, n} 𝒪 F G)).obj X ≃ₗ[
        (structureRingPresheaf 𝒪).obj X]
      ((PresheafOfModules.tensorObj F G).uliftSections.{max so sm r w}).obj X where
  __ := TensorProduct.ringULiftEquiv.{r, m, n, max so sm r w, max so sm w m n}
    (𝒪.obj X) (F.obj X) (G.obj X)
  map_smul' s x := (TensorProduct.ringULiftEquiv.{r, m, n, max so sm r w, max so sm w m n}
    (𝒪.obj X) (F.obj X) (G.obj X)).map_smul (ULift.up s) x

/-- The comparison at an object of the site, as an isomorphism of modules over the sections of
the structure presheaf there. -/
noncomputable def tensorRingULiftAppIso (X : Cᵒᵖ) :
    ((presheafRingULiftDown.{so, sm, r, max w m n, max so sm r w m n} 𝒪).obj
        (tensorPresheafRingULift.{so, sm, r, w, m, n} 𝒪 F G)).obj X ≅
      ((PresheafOfModules.tensorObj F G).uliftSections.{max so sm r w}).obj X :=
  (tensorRingULiftAppEquiv.{so, sm, r, w, m, n} 𝒪 F G X).toModuleIso

/-- **Raising the universe of the coefficient rings commutes with the objectwise tensor product
of presheaves of modules.**  The tensor product formed over the universe lift of the structure
presheaf, of the universe lifts of the sections of two presheaves of modules, is the universe
lift of the sections of their objectwise tensor product. -/
noncomputable def tensorPresheafRingULiftDownIso :
    (presheafRingULiftDown.{so, sm, r, max w m n, max so sm r w m n} 𝒪).obj
        (tensorPresheafRingULift.{so, sm, r, w, m, n} 𝒪 F G) ≅
      (PresheafOfModules.tensorObj F G).uliftSections.{max so sm r w} :=
  PresheafOfModules.isoMk (tensorRingULiftAppIso.{so, sm, r, w, m, n} 𝒪 F G) (by
    intro X Y f
    refine ModuleCat.hom_ext (LinearMap.ext fun z ↦ ?_)
    refine TensorProduct.inductionOn z
      (fun _ _ ↦ rfl) (fun p q hp hq ↦ ?_)
    exact ((map_add _ p q).trans (congrArg₂ (· + ·) hp hq)).trans (map_add _ p q).symm)

end Stacks.Modules

end
