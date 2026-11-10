module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness

/-!
# Tensoring commutes with multiplication by a global section

Let `O` be a sheaf of commutative rings on a site and `F` a sheaf of `O`-modules. Multiplying
by a compatible family `a` of local sections of `O` is an endomorphism of the identity functor
of the category of sheaves of modules, `Stacks.SheafOfModules.globalSectionToEnd`. This file
proves that the endofunctor `G ↦ G ⊗_O F`, the tensor bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor` with its right factor fixed, carries that
endomorphism to itself: tensoring the multiplication-by-`a` map of `G` is the
multiplication-by-`a` map of `G ⊗_O F`.

That statement is the scalar half of the `R`-linearity of a tensor functor: an additive
functor between `R`-linear categories is `R`-linear as soon as it carries `r · 1` to `r · 1`
(`CategoryTheory.Functor.linear_iff`), and for the categories of sheaves of modules the scalar
action is by these multiplication endomorphisms.

## Main definitions

* `CategoryTheory.Adjunction.map_endOfId`: a left adjoint carries an endomorphism `a` of the
  identity functor of its source to an endomorphism `b` of the identity functor of its target,
  as soon as the right adjoint carries `b` back to `a`.
* `Stacks.presheafSectionToEnd`: multiplication by a compatible family of local sections, on
  presheaves of modules; the presheaf-level counterpart of
  `Stacks.SheafOfModules.globalSectionToEnd`.

## Main results

* `Stacks.tensorRight_map_presheafSmul`: the objectwise tensor product carries multiplication
  by `a` to multiplication by `a`.
* `Stacks.sheafification_map_presheafSmul`: so does sheafification.
* `Stacks.sheafTensorRight_map_globalSmul`: hence so does `G ↦ G ⊗_O F`, the tensor bifunctor
  with its right factor fixed.

## Implementation notes

`CategoryTheory.Adjunction.map_endOfId` is the mechanism behind the sheafification step and,
in the applications, behind pullback: for a left adjoint there is no formula for the value on
a morphism, but the adjunction determines it, and the naturality of the unit turns the
hypothesis about the right adjoint into the conclusion about the left one.

The tensor step is a computation on pure tensors, `TensorProduct.smul_tmul'`; the scalar has
to be re-ascribed to the ring of sections, because `(R ⋙ forget RingCat).sections` records it
in the forgetful image of the ring and the scalar action is not found there.

The sheafification step is stated for `PresheafOfModules.sheafification (𝟙 R.obj)`, the
functor `Stacks.SheafOfModules.Tensor.sheafTensor` is built from; the hypothesis of
`CategoryTheory.Adjunction.map_endOfId` holds by definition there, because both multiplication
endomorphisms are given by the same formula on sections and the right adjoint of sheafification
only forgets structure.

Fixing the right factor of the tensor bifunctor is `Functor.flip`, so the value of
`G ↦ G ⊗_O F` on a morphism `φ` is `((sheafTensor O).map φ).app F`, which
`Stacks.SheafOfModules.Tensor.sheafTensor_map_app` identifies with the sheafification of
`PresheafOfModules.tensorHom φ.val (𝟙 F.val)`. The presheaf step is therefore stated for that
canonical objectwise tensor of morphisms, and the two steps compose with no comparison in
between.

## References

* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped TensorProduct IsMulCommutative

universe v u w m

namespace CategoryTheory.Adjunction

/-- **A left adjoint transports endomorphisms of the identity functor**, provided the right
adjoint transports them back: if `U.map (b.asHom.app N) = a.asHom.app (U.obj N)` for every `N`, then
`L.map (a.asHom.app X) = b.asHom.app (L.obj X)` for every `X`. Both sides correspond, under the
adjunction,
to `a.asHom.app X ≫ unit.app X`, by the naturality of the unit and of `a`. -/
theorem map_endOfId {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {U : D ⥤ C}
    (adj : L ⊣ U) {a : End (𝟭 C)} {b : End (𝟭 D)}
    (h : ∀ N : D, U.map (b.asHom.app N) = a.asHom.app (U.obj N)) (X : C) :
    L.map (a.asHom.app X) = b.asHom.app (L.obj X) := by
  apply (adj.homEquiv X (L.obj X)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, h]
  have h1 := adj.unit.naturality (a.asHom.app X)
  have h2 := a.asHom.naturality (adj.unit.app X)
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_map] at h1 h2
  rw [← h1, ← h2]
  rfl

end CategoryTheory.Adjunction

namespace Stacks

section Presheaf

variable {C : Type u} [Category.{v} C] (R₀ : Cᵒᵖ ⥤ RingCat.{w})
  [∀ U, IsMulCommutative (R₀.obj U)]

/-- **Multiplication by a compatible family of local sections, on presheaves of modules.**
This is the presheaf-level counterpart of `Stacks.SheafOfModules.globalSectionToEnd`: on
sections over `U` it is multiplication by the local scalar `f U`. -/
def presheafSectionToEnd (f : (R₀ ⋙ forget RingCat).sections) :
    End (𝟭 (PresheafOfModules.{m} R₀)) :=
  .of
    { app M := {
        app U := ModuleCat.ofHom (LinearMap.lsmul (R₀.obj U) (M.obj U) (f.val U))
        naturality := by
          intro U V i; ext x
          change f.val V • M.map i x = M.map i (f.val U • x)
          rw [M.map_smul]
          exact congrArg (fun r => r • M.map i x) (f.property i).symm }
      naturality M N g := by
        ext U x; exact (PresheafOfModules.Hom.app g U).hom.map_smul (f.val U) x |>.symm }

/-- On local sections, `Stacks.presheafSectionToEnd` is scalar multiplication. -/
@[simp] theorem presheafSectionToEnd_apply (f : (R₀ ⋙ forget RingCat).sections)
    (M : PresheafOfModules.{m} R₀) (U : Cᵒᵖ) (x : M.obj U) :
    PresheafOfModules.Hom.app ((presheafSectionToEnd R₀ f).asHom.app M) U x = f.val U • x := rfl

/-- The rings of sections of the presheaf of rings underlying a presheaf of commutative rings
are commutative, in the unbundled form the multiplication endomorphisms ask for. -/
instance ringPresheaf_isMulCommutative (O : Cᵒᵖ ⥤ CommRingCat.{w}) (U : Cᵒᵖ) :
    IsMulCommutative ((ringPresheaf O).obj U) :=
  ⟨⟨mul_comm⟩⟩

/-- **The objectwise tensor product commutes with multiplication by a section**: on a pure
tensor both sides are `(a · x) ⊗ y`. -/
theorem tensorRight_map_presheafSmul {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (F : PresheafOfModules.{w} (ringPresheaf O))
    (f : (ringPresheaf O ⋙ forget RingCat).sections)
    (P : PresheafOfModules.{w} (ringPresheaf O)) :
    PresheafOfModules.tensorHom (O := O)
        ((presheafSectionToEnd (ringPresheaf O) f).asHom.app P) (𝟙 F) =
      (presheafSectionToEnd (ringPresheaf O) f).asHom.app
        (PresheafOfModules.tensorObj (O := O) P F) := by
  refine PresheafOfModules.tensorObj_hom_ext fun U x y ↦ ?_
  let r : ((ringPresheaf O).obj U) := f.val U
  change (r • x) ⊗ₜ[(ringPresheaf O).obj U] y = r • (x ⊗ₜ[(ringPresheaf O).obj U] y)
  rw [TensorProduct.smul_tmul']

end Presheaf

section Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **Sheafification commutes with multiplication by a section.** The right adjoint of
sheafification only forgets structure, so it carries the multiplication endomorphism of
sheaves of modules to that of presheaves of modules, by definition. -/
theorem sheafification_map_presheafSmul (R : Sheaf J RingCat.{w})
    [∀ U, IsMulCommutative (R.obj.obj U)]
    (f : (R.obj ⋙ forget RingCat).sections) (P : PresheafOfModules.{w} R.obj) :
    (PresheafOfModules.sheafification (𝟙 R.obj)).map
        ((presheafSectionToEnd R.obj f).asHom.app P) =
      (SheafOfModules.globalSectionToEnd R f).asHom.app
        ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P) :=
  Adjunction.map_endOfId (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj))
    (fun _ => rfl) P

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] {O : Sheaf J CommRingCat.{w}}
  [∀ U, IsMulCommutative ((commRingSheafToRingSheaf O).obj.obj U)]
  (F : _root_.SheafOfModules.{w} (commRingSheafToRingSheaf O))

/-- **Tensoring with `F` commutes with multiplication by a section**: the endofunctor
`G ↦ G ⊗_O F` carries multiplication by a compatible family `f` of local sections of `O` on
`G` to multiplication by `f` on `G ⊗_O F`. -/
theorem sheafTensorRight_map_globalSmul
    (f : ((commRingSheafToRingSheaf O).obj ⋙ forget RingCat).sections)
    (G : _root_.SheafOfModules.{w} (commRingSheafToRingSheaf O)) :
    ((SheafOfModules.Tensor.sheafTensor O).flip.obj F).map
        ((SheafOfModules.globalSectionToEnd (commRingSheafToRingSheaf O) f).asHom.app G) =
      (SheafOfModules.globalSectionToEnd (commRingSheafToRingSheaf O) f).asHom.app
        (((SheafOfModules.Tensor.sheafTensor O).flip.obj F).obj G) := by
  have h1 : PresheafOfModules.tensorHom (O := O.obj)
        (((SheafOfModules.globalSectionToEnd (commRingSheafToRingSheaf O) f).asHom.app G).val)
          (𝟙 F.val) =
      (presheafSectionToEnd (commRingSheafToRingSheaf O).obj f).asHom.app
        (PresheafOfModules.tensorObj (O := O.obj) G.val F.val) :=
    tensorRight_map_presheafSmul (O := O.obj) F.val f G.val
  have h2 := congrArg (fun ψ => (PresheafOfModules.sheafification
    (𝟙 (commRingSheafToRingSheaf O).obj)).map ψ) h1
  exact h2.trans (sheafification_map_presheafSmul (commRingSheafToRingSheaf O) f _)

end Sheaf

/-- **Multiplication by a scalar, as an endomorphism of the identity functor of the category
of modules over a commutative ring.** -/
def scalarEnd (R : CommRingCat.{u}) (r : ↑R) : End (𝟭 (ModuleCat.{u} ↑R)) :=
  .of
    { app M := r • 𝟙 M
      naturality M N f := by simp }

/-- `Stacks.scalarEnd` is scalar multiplication on the identity. -/
@[simp] theorem scalarEnd_app (R : CommRingCat.{u}) (r : ↑R) (M : ModuleCat.{u} ↑R) :
    (scalarEnd R r).asHom.app M = r • 𝟙 M := rfl

end Stacks

end
