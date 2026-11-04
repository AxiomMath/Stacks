module

public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Invertible
public import StacksFrontier.AlgebraicGeometry.ProjTwistTheta.DegreeSection

/-!
# The Tag 01CD comparison, read through the restriction functor of an open immersion

For a morphism of ringed spaces `f` the comparison of Tag 01CD,
`Stacks.PullbackTensorIso.pullbackTensorIso`, is characterized by its value on the pullback
unit: its adjoint transpose carries the sheafification-unit image of a pure tensor `x ⊗ y` to
the sheafification-unit image of the tensor of the two pullback-unit images
(`Stacks.RingedSpace.comparison_homEquiv_unit_tmul`). A pullback-unit image is the only kind
of section of a pullback that can be written down, so that is the only handle on the
comparison, and it is a handle on sections over an open of the form `f ⁻¹ᵁ W`.

Along an *open immersion* `g : X ⟶ Y` of schemes a second description of the pullback is
available: `AlgebraicGeometry.Scheme.Modules.restrictFunctor`, whose sections over an open `V`
of `X` are literally the sections of the module over `g ''ᵁ V`, traded for the pullback by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`. This file computes the Tag 01CD
comparison in that description, at *every* open of `X` and on *every* pure tensor:

`comparison_restrictFunctorIsoPullback_tensorSheafUnit` says that the comparison carries the
image under `restrictFunctorIsoPullback` of a pure tensor of honest sections over `g ''ᵁ V` to
the pure tensor of their images. Its inverse form,
`restrictFunctorIsoPullback_tensorSheafUnit_eq`, is the one consumers need: a multiplication on
the pullback of a graded algebra runs through the *inverse* comparison, which no formula
reaches directly.

## Main results

* `Stacks.AlgebraicGeometry.ProjMapCard.pullbackUnit_eq_restrictFunctorIsoPullback`: the
  pullback unit at an open `W` of `Y` is the restriction of a section to `g ''ᵁ (g ⁻¹ᵁ W)`
  followed by `restrictFunctorIsoPullback`. This is
  `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` read on an element, and it is what
  lets the comparison be evaluated on something other than a pullback unit.
* `Stacks.AlgebraicGeometry.ProjMapCard.comparison_restrictFunctorIsoPullback_tensorSheafUnit`:
  the comparison on a pure tensor, at an arbitrary open of `X`.
* `Stacks.AlgebraicGeometry.ProjMapCard.restrictFunctorIsoPullback_tensorSheafUnit_eq`: the
  same identity read through the inverse of the comparison.

## The transport, and why it is the whole difficulty

The pullback-unit formula lives at the open `g ⁻¹ᵁ W` for an open `W` of `Y`. The identity
wanted lives at an arbitrary open `V` of `X`, with sections over `g ''ᵁ V`. Taking
`W := g ''ᵁ V` turns the first into the second at the open `g ⁻¹ᵁ (g ''ᵁ V)`, with sections
over `g ''ᵁ (g ⁻¹ᵁ (g ''ᵁ V))`, and `AlgebraicGeometry.Scheme.Hom.preimage_image_eq` identifies
that open with `V` — *propositionally*, not definitionally, so the identification has to be
transported through the types of the sections.

The transport is done by rewriting the goal, in the direction `V ↦ g ⁻¹ᵁ (g ''ᵁ V)`, before the
sections are introduced: the statement is well-typed at every open, so the rewrite's motive is
fine once the section variables are still under a binder, and it fails if they are introduced
first. What remains is that the restriction map
`Γ(M, g ''ᵁ V) ⟶ Γ(M, g ''ᵁ (g ⁻¹ᵁ (g ''ᵁ V)))` is a bijection, which holds because its two
opens are equal and the category of opens is thin, so the restriction in the other direction
is a two-sided inverse (`map_op_map_op_eq_self`). No `eqToHom` is written by hand anywhere.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite
open Stacks.RingedSpace PresheafOfModules RingedSpaceModuleAdjunction
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.ProjMapCard

universe u

/-! ### Two generalities -/

/-- Restriction along `U ⟶ V` followed by restriction along `V ⟶ U` is the identity: the
category of opens is thin, so the two compose to the identity morphism of `U`. -/
public theorem map_op_map_op_eq_self {T : Type u} [TopologicalSpace T]
    (P : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{u}) {U V : Opens T} (h₁ : U ⟶ V) (h₂ : V ⟶ U)
    (x : P.obj (op U)) : (P.map h₁.op) ((P.map h₂.op) x) = x := by
  have h : P.map h₂.op ≫ P.map h₁.op = 𝟙 _ := by
    rw [← P.map_comp, show h₂.op ≫ h₁.op = (h₁ ≫ h₂).op from rfl,
      show h₁ ≫ h₂ = 𝟙 U from Subsingleton.elim _ _]
    exact P.map_id _
  exact congrArg (fun k => (ConcreteCategory.hom k) x) h

variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsOpenImmersion g] (M N : Y.Modules)

/-- Restriction commutes with the unit exhibiting the tensor product of two sheaves of modules
as a sheafification, on a pure tensor of sections. -/
public theorem tensorSheafUnit_map_tmul {W W' : Y.Opens} (h : op W ⟶ op W')
    (x : M.val.obj (op W)) (y : N.val.obj (op W)) :
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y.toRingedSpace)).presheaf,
      ((Y.toRingedSpace)).IsSheaf⟩))).obj (M, N)).val.presheaf.map h
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf (Y.toRingedSpace))
          (𝟙 (Stacks.RingedSpace.structureRingSheaf (Y.toRingedSpace)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := (Y.toRingedSpace).presheaf) (M).val (N).val))
          (op W) (x ⊗ₜ y)) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.RingedSpace.structureRingSheaf (Y.toRingedSpace))
        (𝟙 (Stacks.RingedSpace.structureRingSheaf (Y.toRingedSpace)).obj)).unit.app
        (PresheafOfModules.tensorObj (O := (Y.toRingedSpace).presheaf) (M).val (N).val)) (op W')
        (M.val.presheaf.map h x ⊗ₜ N.val.presheaf.map h y) :=
  Eq.trans (restrictₛₗ_naturality_apply ((PresheafOfModules.sheafificationAdjunction
    (R := Stacks.RingedSpace.structureRingSheaf (Y.toRingedSpace))
    (𝟙 (Stacks.RingedSpace.structureRingSheaf (Y.toRingedSpace)).obj)).unit.app
    (PresheafOfModules.tensorObj (O := (Y.toRingedSpace).presheaf) (M).val
    (N).val)) h (x ⊗ₜ y)).symm
    (congrArg (Hom.app ((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.RingedSpace.structureRingSheaf (Y.toRingedSpace))
      (𝟙 (Stacks.RingedSpace.structureRingSheaf (Y.toRingedSpace)).obj)).unit.app
      (PresheafOfModules.tensorObj (O := (Y.toRingedSpace).presheaf) (M).val (N).val)) (op W'))
      (tensorObj_restrictₛₗ_tmul h x y))

/-! ### The pullback unit along an open immersion -/

/-- The unit of the pullback--pushforward adjunction along an open immersion, at an open `W` of
the target, is the restriction of a section to `g ''ᵁ (g ⁻¹ᵁ W)` followed by the identification
of restriction with pullback.

This is `Stacks.AlgebraicGeometry.ProjTwistTheta.restrictUnit_comp_map_restrictFunctorIsoPullback`
read on an element; the restriction map is the unit of the restriction adjunction, which is a
presheaf restriction map by `AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app`. -/
public theorem pullbackUnit_eq_restrictFunctorIsoPullback (W : Y.Opens)
    (x : M.val.obj (op W)) :
    pullbackUnit g.toLRSHom.toShHom M (op W) x =
      Hom.app ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M).val (op (g ⁻¹ᵁ W))
        (M.val.presheaf.map (homOfLE (g.image_preimage_le W)).op x) :=
  (congrArg (fun φ => Hom.app (SheafOfModules.Hom.val φ) (op W) x)
    (Stacks.AlgebraicGeometry.ProjTwistTheta.restrictUnit_comp_map_restrictFunctorIsoPullback
      g M)).symm

/-! ### The comparison on a pure tensor -/

/-- The Tag 01CD comparison on a pure tensor, at an open of `X` of the form `g ⁻¹ᵁ W`. This is
`Stacks.RingedSpace.comparison_homEquiv_unit_tmul` with every pullback unit replaced by a
restriction followed by `restrictFunctorIsoPullback`. -/
public theorem comparison_restrictFunctorIsoPullback_tensorSheafUnit_preimage (W : Y.Opens)
    (x : M.val.obj (op W)) (y : N.val.obj (op W)) :
    Hom.app ((Stacks.PullbackTensorIso.pullbackTensorIso
          g.toLRSHom.toShHom).hom.app (M, N)).val (op (g ⁻¹ᵁ W))
        (Hom.app ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app
            (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩))).obj
              (M, N))).val (op (g ⁻¹ᵁ W))
          ((((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩))).obj
            (M, N)).val.presheaf.map
              (homOfLE (g.image_preimage_le W)).op
            (Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.RingedSpace.structureRingSheaf (Y.toRingedSpace))
              (𝟙 (Stacks.RingedSpace.structureRingSheaf (Y.toRingedSpace)).obj)).unit.app
              (PresheafOfModules.tensorObj (O := (Y.toRingedSpace).presheaf) (M).val (N).val))
              (op W) (x ⊗ₜ y)))) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.RingedSpace.structureRingSheaf (X.toRingedSpace))
        (𝟙 (Stacks.RingedSpace.structureRingSheaf (X.toRingedSpace)).obj)).unit.app
        (PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf)
        (((pullbackFunctor g.toLRSHom.toShHom).obj M)).val
        (((pullbackFunctor g.toLRSHom.toShHom).obj N)).val)) (op (g ⁻¹ᵁ W))
        (Hom.app ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M).val (op (g ⁻¹ᵁ W))
            (M.val.presheaf.map (homOfLE (g.image_preimage_le W)).op x) ⊗ₜ
          Hom.app ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app N).val (op (g ⁻¹ᵁ W))
            (N.val.presheaf.map (homOfLE (g.image_preimage_le W)).op y)) := by
  refine Eq.trans (congrArg
    (Hom.app ((Stacks.PullbackTensorIso.pullbackTensorIso
      g.toLRSHom.toShHom).hom.app (M, N)).val (op (g ⁻¹ᵁ W)))
    (pullbackUnit_eq_restrictFunctorIsoPullback g (((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((Y.toRingedSpace)).presheaf,
      ((Y.toRingedSpace)).IsSheaf⟩))).obj (M, N)) W _).symm) ?_
  refine Eq.trans (Stacks.PullbackTensorIso.comparison_val_app_pullbackUnit
    g.toLRSHom.toShHom M N W _) ?_
  refine Eq.trans (comparison_homEquiv_unit_tmul _ M N (op W) x y) ?_
  rw [pullbackUnit_eq_restrictFunctorIsoPullback g M W x,
    pullbackUnit_eq_restrictFunctorIsoPullback g N W y]
  rfl

/-- **The Tag 01CD comparison on a pure tensor, at an arbitrary open of `X`.** The comparison
carries the image under `restrictFunctorIsoPullback` of the sheafification-unit image of a pure
tensor of sections over `g ''ᵁ V` to the sheafification-unit image of the pure tensor of their
images.

The sections are arbitrary: the open `g ''ᵁ V` need not be of the form `g ⁻¹ᵁ W` nor the
sections restrictions from a larger open. -/
public theorem comparison_restrictFunctorIsoPullback_tensorSheafUnit (V : X.Opens) :
    ∀ (x : M.val.obj (op (g ''ᵁ V))) (y : N.val.obj (op (g ''ᵁ V))),
      Hom.app ((Stacks.PullbackTensorIso.pullbackTensorIso
            g.toLRSHom.toShHom).hom.app (M, N)).val (op V)
          (Hom.app ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app
              (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩))).obj
                (M, N))).val (op V)
            (Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.RingedSpace.structureRingSheaf (Y.toRingedSpace))
              (𝟙 (Stacks.RingedSpace.structureRingSheaf (Y.toRingedSpace)).obj)).unit.app
              (PresheafOfModules.tensorObj (O := (Y.toRingedSpace).presheaf) (M).val (N).val))
              (op (g ''ᵁ V)) (x ⊗ₜ y))) =
        Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf (X.toRingedSpace))
          (𝟙 (Stacks.RingedSpace.structureRingSheaf (X.toRingedSpace)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf)
          (((pullbackFunctor g.toLRSHom.toShHom).obj M)).val
          (((pullbackFunctor g.toLRSHom.toShHom).obj N)).val)) (op V)
          (Hom.app ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M).val (op V) x ⊗ₜ
            Hom.app ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app N).val (op V) y) := by
  rw [← g.preimage_image_eq V]
  intro x y
  have hEq : g ''ᵁ (g ⁻¹ᵁ (g ''ᵁ V)) = g ''ᵁ V :=
    congrArg (fun U => g ''ᵁ U) (g.preimage_image_eq V)
  set r := homOfLE (g.image_preimage_le (g ''ᵁ V)) with hr
  set k : g ''ᵁ V ⟶ g ''ᵁ (g ⁻¹ᵁ (g ''ᵁ V)) := homOfLE (le_of_eq hEq.symm) with hk
  have hx : M.val.presheaf.map r.op (M.val.presheaf.map k.op x) = x :=
    map_op_map_op_eq_self M.val.presheaf r k x
  have hy : N.val.presheaf.map r.op (N.val.presheaf.map k.op y) = y :=
    map_op_map_op_eq_self N.val.presheaf r k y
  have h := comparison_restrictFunctorIsoPullback_tensorSheafUnit_preimage g M N (g ''ᵁ V)
    (M.val.presheaf.map k.op x) (N.val.presheaf.map k.op y)
  rw [← hr] at h
  rw [tensorSheafUnit_map_tmul M N r.op (M.val.presheaf.map k.op x) (N.val.presheaf.map k.op y),
    hx, hy] at h
  exact h

/-- **The inverse Tag 01CD comparison on a pure tensor of restricted sections.** The direction
consumers need: the inverse of the comparison carries the pure tensor of the
`restrictFunctorIsoPullback` images of two sections over `g ''ᵁ V` to the image of their pure
tensor. -/
public theorem restrictFunctorIsoPullback_tensorSheafUnit_eq (V : X.Opens)
    (x : M.val.obj (op (g ''ᵁ V))) (y : N.val.obj (op (g ''ᵁ V))) :
    Hom.app ((Stacks.PullbackTensorIso.pullbackTensorIso
          g.toLRSHom.toShHom).inv.app (M, N)).val (op V)
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf (X.toRingedSpace))
          (𝟙 (Stacks.RingedSpace.structureRingSheaf (X.toRingedSpace)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf)
          (((pullbackFunctor g.toLRSHom.toShHom).obj M)).val
          (((pullbackFunctor g.toLRSHom.toShHom).obj N)).val)) (op V)
          (Hom.app ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M).val (op V) x ⊗ₜ
            Hom.app ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app N).val (op V) y)) =
      Hom.app ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩))).obj (M, N))).val (op V)
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf (Y.toRingedSpace))
          (𝟙 (Stacks.RingedSpace.structureRingSheaf (Y.toRingedSpace)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := (Y.toRingedSpace).presheaf) (M).val (N).val))
          (op (g ''ᵁ V)) (x ⊗ₜ y)) := by
  refine Eq.trans (congrArg (Hom.app ((Stacks.PullbackTensorIso.pullbackTensorIso
      g.toLRSHom.toShHom).inv.app (M, N)).val (op V))
    (comparison_restrictFunctorIsoPullback_tensorSheafUnit g M N V x y).symm) ?_
  exact congrArg (fun φ => Hom.app (SheafOfModules.Hom.val φ) (op V)
      (Hom.app ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩))).obj (M, N))).val (op V)
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf (Y.toRingedSpace))
          (𝟙 (Stacks.RingedSpace.structureRingSheaf (Y.toRingedSpace)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := (Y.toRingedSpace).presheaf) (M).val (N).val))
          (op (g ''ᵁ V)) (x ⊗ₜ y))))
    (Iso.hom_inv_id_app (Stacks.PullbackTensorIso.pullbackTensorIso g.toLRSHom.toShHom) (M, N))

end Stacks.AlgebraicGeometry.ProjMapCard

end
