module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.SheafTensorPairing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The naive cup product on sections, and the Čech coefficient pairing

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `ℱ` and `𝒢` be sheaves of
`𝒪_X`-modules.  The *degreewise* naive cup product is the map of sheaves of `𝒪_Y`-modules

`f_*ℱ ⊗_{𝒪_Y} f_*𝒢 ⟶ f_*(ℱ ⊗_{𝒪_X} 𝒢)`

adjoint, under `f^* ⊣ f_*` of Stacks 0096, to the comparison of Stacks 01CD followed by the
ordinary counit in each tensor factor.  This is the summandwise part of
`Stacks.Cohomology.NaiveCupProductOnRingedSpaces.naiveCupProduct`, built here on sheaves rather
than on complexes so that it can be read on local sections.

The point of the file is that computation.  On sections over an open `V ⊆ Y` the map carries the
sheafification-unit image of a pure tensor `x ⊗ y`, `x` and `y` sections over `f⁻¹V`, to the
sheafification-unit image of `x ⊗ y` over `f⁻¹V` — the two pure tensors being taken over
`𝒪_Y(V)` on the source side and over `𝒪_X(f⁻¹V)` on the target side.  Equivalently: the
degreewise naive cup product is base change of scalars along `f^♯` followed by the unit of
sheafification, which is exactly the coefficient pairing
`Stacks.Cech.SheafTensorPairing.sheafTensorPairing` that the Čech cup product of Stacks Tag
0FKV consumes.  `pushforwardTensorMap_eq_sheafTensorPairing` is that identification.

## Main definitions

* `Stacks.RingedSpace.pushforwardTensorMap` — **the degreewise naive cup product**
  `f_*ℱ ⊗_{𝒪_Y} f_*𝒢 ⟶ f_*(ℱ ⊗_{𝒪_X} 𝒢)`.

## Main results

* `Stacks.RingedSpace.pushforwardTensorMap_unit_tmul` — **the unit computation**: the degreewise
  naive cup product on the sheafification-unit image of a pure tensor of local sections.
* `Stacks.RingedSpace.pushforwardTensorMap_unique` — that computation determines it.
* `Stacks.RingedSpace.sheafTensorPairing_app_tmul` — the Čech coefficient pairing on a pure
  tensor of sections over an open below `V` is the unit of sheafification, by `rfl`.
* `Stacks.RingedSpace.pushforwardTensorMap_eq_sheafTensorPairing` — **the two agree**: the
  degreewise naive cup product of a morphism of ringed spaces, read on sections over `V ⊆ Y`,
  is the sheaf-tensor coefficient pairing of the Čech cup product on `X`, read at the terminal
  object of the slice over `f⁻¹V`.

## Implementation notes

*Why this is not a formality.*  `RingedSpaceModuleAdjunction.modulePullback` is an abstract left
adjoint: nothing describes its sections.  So the adjoint transpose defining the naive cup product
cannot be computed by unfolding it.  What can be computed is the comparison of Stacks 01CD on
the sheafification-unit image of a pure tensor —
`Stacks.RingedSpace.comparison_homEquiv_unit_tmul`, which produces the two *pullback-unit*
images `η x` and `η y` — and then the two occurrences of `η` are removed by the triangle
identity, the counit being applied to the unit of a pushforward.  That is the only step with
content, and it is isolated as the file-local `counit_pullbackUnit`.  That triangle identity is
already stated publicly, at the `structureSheafRing` spelling of the structure ring sheaf, as
`Stacks.RingedSpace.counit_pullbackUnit` of
`StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaSections`; the copy here is `private`
rather than a second declaration of that name, because importing that file would put 369 further
modules — the whole scheme-theoretic quasi-coherent stack — under this one.

*The crossing budget.*  Each declaration below crosses at most one spelling boundary.
`pushforwardTensorMap_eq` pays the `Adjunction.homEquiv_naturality_right` crossing and nothing
else; `pushforwardTensorMap_unit_tmul` consumes it as a hypothesis-free equation and pays only
the pushforward-on-sections reindexing, which is `rfl`; and
`pushforwardTensorMap_eq_sheafTensorPairing` is a `Eq.trans` of two finished equations and pays
none.  Combining any two of these into one declaration is what exhausts the heartbeat budget in
this part of the tree.

*The commutative ring structure on a ring of sections.*
`Stacks.Cech.ModuleCupProduct.sectionCommRing` is not found by instance search once the space is
written as the carrier of a `RingedSpace` — the `TopologicalSpace` instance stays a metavariable
— although it applies by name.  `coeffCommRing` is that instance restated at the `RingedSpace`
spelling, as a local instance: it is the *same term*, so a pure tensor written here and the one
inside the type of `Stacks.Cech.SheafTensorPairing.sheafTensorPairing` carry the same scalars.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
* [Stacks Project, Tag 0FP3](https://stacks.math.columbia.edu/tag/0FP3)
-/

@[expose] public noncomputable section

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf TopCat.Presheaf.IsSheaf

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.RingedSpace

open RingedSpaceModuleAdjunction PresheafOfModules CategoryTheory.Sheaf
open Stacks.Cech.ModuleCupProduct Stacks.Cech.SheafTensorPairing

/-- **The ring of sections of the structure sheaf on an open is commutative**, at the
`RingedSpace` spelling of the space.  This is `Stacks.Cech.ModuleCupProduct.sectionCommRing`,
which applies by name but is not found by instance search here. -/
local instance coeffCommRing (X : RingedSpace.{u, u}) (V : Opens X.carrier) :
    CommRing (CoeffRing X.sheaf V) :=
  sectionCommRing X.sheaf V

section Degreewise

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (F G : SheafOfModules.{u} (structureRingSheaf X))

/-- The two ordinary counits `f^*f_*ℱ ⟶ ℱ` and `f^*f_*𝒢 ⟶ 𝒢`, as one morphism of the product
category, which is the form in which the tensor product bifunctor consumes them. -/
abbrev counitPair :
    (((pullbackFunctor f).obj ((pushforwardFunctor f).obj F),
      (pullbackFunctor f).obj ((pushforwardFunctor f).obj G)) :
        SheafOfModules.{u} (structureRingSheaf X) × _) ⟶ (F, G) :=
  ((pullbackAdjunction f).counit.app F, (pullbackAdjunction f).counit.app G)

/-- **The degreewise naive cup product** `f_*ℱ ⊗_{𝒪_Y} f_*𝒢 ⟶ f_*(ℱ ⊗_{𝒪_X} 𝒢)`: the map
adjoint, under `f^* ⊣ f_*` of Stacks 0096, to the comparison of Stacks 01CD followed by the
ordinary counit `f^*f_* ⟶ id` in each of the two tensor factors.

This is the summandwise part of the complex-level naive cup product of Stacks Tag 0FP3,
`Stacks.Cohomology.NaiveCupProductOnRingedSpaces.naiveCupProduct`, with the same recipe at the
same adjunction and the same Stacks 01CD comparison; it is built on sheaves so that it can be
read on local sections, which the total-complex form cannot be. -/
@[ega "0 12.2.2" "special case"]
def pushforwardTensorMap :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf))).obj
        ((pushforwardFunctor f).obj F, (pushforwardFunctor f).obj G) ⟶
      (pushforwardFunctor f).obj
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          X.sheaf))).obj (F, G)) :=
  (pullbackAdjunction f).homEquiv _ _
    (comparison f ((pushforwardFunctor f).obj F) ((pushforwardFunctor f).obj G) ≫
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).map
        (counitPair f F G))

/-- The degreewise naive cup product written through the adjoint transpose of the Stacks 01CD
comparison: the transpose of a composite is the transpose of the first factor followed by the
pushforward of the second. -/
theorem pushforwardTensorMap_eq :
    pushforwardTensorMap f F G =
      comparisonTranspose f ((pushforwardFunctor f).obj F) ((pushforwardFunctor f).obj G) ≫
        (pushforwardFunctor f).map
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            X.sheaf))).map (counitPair f F G)) := by
  refine ((pullbackAdjunction f).homEquiv_naturality_right _ _).trans ?_
  exact congrArg (· ≫ _) (homEquiv_comparison f _ _)

/-- **The counit undoes the unit on a local section of a pushforward.**  For `x` a section of
`ℱ` over `f⁻¹V`, the image of `x` under the unit `f_*ℱ ⟶ f_*f^*f_*ℱ` is carried back to `x` by
the counit `f^*f_*ℱ ⟶ ℱ`.  This is the triangle identity of the adjunction of Stacks 0096,
read on sections.

File-local: the same identity is public at the `structureSheafRing` spelling as
`Stacks.RingedSpace.counit_pullbackUnit` of
`StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaSections`. -/
private theorem counit_pullbackUnit (V : (Opens Y.carrier)ᵒᵖ)
    (x : ((pushforwardFunctor f).obj F).val.obj V) :
    Hom.app ((pullbackAdjunction f).counit.app F).val ((opensMap f).op.obj V)
        (pullbackUnit f ((pushforwardFunctor f).obj F) V x) = x :=
  hom_congr_apply' (congrArg (fun h ↦ SheafOfModules.Hom.val h)
    ((pullbackAdjunction f).right_triangle_components F)) V x

/-- **The degreewise naive cup product on local sections.**  Over an open `V ⊆ Y` it carries the
sheafification-unit image of the pure tensor `x ⊗ y` of two sections over `f⁻¹V`, taken over
`𝒪_Y(V)`, to the sheafification-unit image of the pure tensor `x ⊗ y` taken over `𝒪_X(f⁻¹V)`.

In other words the map is base change of scalars along `f^♯ : 𝒪_Y(V) ⟶ 𝒪_X(f⁻¹V)` followed by
the unit exhibiting `ℱ ⊗_{𝒪_X} 𝒢` as a sheafification.  Both occurrences of the unit of
`f^* ⊣ f_*` produced by the Stacks 01CD comparison are removed by `counit_pullbackUnit`. -/
theorem pushforwardTensorMap_unit_tmul (V : (Opens Y.carrier)ᵒᵖ)
    (x : ((pushforwardFunctor f).obj F).val.obj V)
    (y : ((pushforwardFunctor f).obj G).val.obj V) :
    Hom.app (pushforwardTensorMap f F G).val V
        (Hom.app ((PresheafOfModules.sheafificationAdjunction (R := structureRingSheaf (Y))
            (𝟙 (structureRingSheaf (Y)).obj)).unit.app
            (PresheafOfModules.tensorObj (O := (Y).presheaf) (((pushforwardFunctor f).obj F)).val
              (((pushforwardFunctor f).obj G)).val)) V (x ⊗ₜ y)) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction (R := structureRingSheaf (X))
          (𝟙 (structureRingSheaf (X)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := (X).presheaf) (F).val (G).val))
        ((opensMap f).op.obj V) (x ⊗ₜ y) := by
  refine (hom_congr_apply' (congrArg (fun h ↦ SheafOfModules.Hom.val h)
    (pushforwardTensorMap_eq f F G)) V _).trans ?_
  refine (congrArg (fun sectionValue => Hom.app
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      X.sheaf)).map (counitPair f F G)).val ((opensMap f).op.obj V) sectionValue)
    (comparisonTranspose_unit_tmul f _ _ V x y)).trans ?_
  refine (tensorSheaf_map_unit_tmul X _ _ _ _ _).trans ?_
  rw [counit_pullbackUnit, counit_pullbackUnit]
  rfl

/-- **The computation of `pushforwardTensorMap_unit_tmul` determines the degreewise naive cup
product.**  Pure tensors of local sections generate the objectwise tensor product and a morphism
out of a sheafification is determined by its restriction along the unit, so a morphism
`f_*ℱ ⊗_{𝒪_Y} f_*𝒢 ⟶ f_*(ℱ ⊗_{𝒪_X} 𝒢)` with that effect on sections is the degreewise naive cup
product. -/
theorem pushforwardTensorMap_unique
    (θ : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          Y.sheaf))).obj ((pushforwardFunctor f).obj F, (pushforwardFunctor f).obj G) ⟶
      (pushforwardFunctor f).obj
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          X.sheaf))).obj (F, G)))
    (hθ : ∀ (V : (Opens Y.carrier)ᵒᵖ) (x : ((pushforwardFunctor f).obj F).val.obj V)
      (y : ((pushforwardFunctor f).obj G).val.obj V),
      Hom.app θ.val V
          (Hom.app ((PresheafOfModules.sheafificationAdjunction (R := structureRingSheaf (Y))
              (𝟙 (structureRingSheaf (Y)).obj)).unit.app
              (PresheafOfModules.tensorObj (O := (Y).presheaf) (((pushforwardFunctor f).obj F)).val
                (((pushforwardFunctor f).obj G)).val)) V (x ⊗ₜ y)) =
        Hom.app ((PresheafOfModules.sheafificationAdjunction (R := structureRingSheaf (X))
            (𝟙 (structureRingSheaf (X)).obj)).unit.app
            (PresheafOfModules.tensorObj (O := (X).presheaf) (F).val (G).val))
          ((opensMap f).op.obj V) (x ⊗ₜ y)) :
    θ = pushforwardTensorMap f F G :=
  sheafification_hom_ext (tensorObj_hom_ext fun V x y ↦
    (hθ V x y).trans (pushforwardTensorMap_unit_tmul f F G V x y).symm)

end Degreewise

section Cech

variable {X : RingedSpace.{u, u}} (V : Opens X.carrier)
  (F G : SheafOfModules.{u} (structureRingSheaf X))

/-- **The Čech coefficient pairing of Stacks Tag 0FKV on a pure tensor of sections.**  On an open
`Z ≤ V` the pairing
`Stacks.Cech.SheafTensorPairing.sheafTensorPairing` carries the pure tensor `x ⊗ y` over the
ring `𝒪_X(V)` to the sheafification-unit image of `x ⊗ y` over `𝒪_X(Z)`; base change of scalars
is the identity on a pure tensor, so this holds by `rfl`.

This is the asymmetry that Stacks Tag 0FKV displays: the source tensors over the ring of
sections on `V`, the target's coefficients over the structure sheaf. -/
theorem sheafTensorPairing_app_tmul (Z : (Over V)ᵒᵖ)
    (x : F.val.obj (sliceOpen V Z)) (y : G.val.obj (sliceOpen V Z)) :
    ((sheafTensorPairing X.sheaf V F G).app Z).hom (x ⊗ₜ y) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction (R := structureRingSheaf (X))
          (𝟙 (structureRingSheaf (X)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := (X).presheaf) (F).val (G).val))
        (sliceOpen V Z) (x ⊗ₜ y) :=
  rfl

end Cech

/-- **The degreewise naive cup product of a morphism of ringed spaces is the Čech coefficient
pairing.**  For `f : X ⟶ Y` and an open `V ⊆ Y`, the degreewise naive cup product of Stacks Tag
0FP3, read on sections over `V` at the sheafification-unit image of a pure tensor, agrees with
the sheaf-tensor coefficient pairing of Stacks Tag 0FKV on `X` for the open `f⁻¹V`, read at the
terminal object of the slice over `f⁻¹V`.

The two pure tensors are taken over different rings — `𝒪_Y(V)` on the left, `𝒪_X(f⁻¹V)` on the
right — which is why the statement is an equation between the two *values* at the same pair of
sections rather than between two maps out of one tensor product.  There is no such map: the
source of the naive cup product tensors over `𝒪_Y(V)` and the source of the Čech pairing over
`𝒪_X(f⁻¹V)`, and the comparison of the two is the base change along `f^♯` that both sides
contain.

This is a step of the proof of Tag 0FKV — the identification of the two cup products that its
diagram compares — and not a clause of its statement, so it carries no tag. -/
@[ega "0 12.2.2" "partial"]
theorem pushforwardTensorMap_eq_sheafTensorPairing {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (F G : SheafOfModules.{u} (structureRingSheaf X)) (V : (Opens Y.carrier)ᵒᵖ)
    (x : ((pushforwardFunctor f).obj F).val.obj V)
    (y : ((pushforwardFunctor f).obj G).val.obj V) :
    Hom.app (pushforwardTensorMap f F G).val V
        (Hom.app ((PresheafOfModules.sheafificationAdjunction (R := structureRingSheaf (Y))
            (𝟙 (structureRingSheaf (Y)).obj)).unit.app
            (PresheafOfModules.tensorObj (O := (Y).presheaf) (((pushforwardFunctor f).obj F)).val
              (((pushforwardFunctor f).obj G)).val)) V (x ⊗ₜ y)) =
      ((sheafTensorPairing X.sheaf ((opensMap f).obj V.unop) F G).app
          (op (Over.mk (𝟙 ((opensMap f).obj V.unop))))).hom (x ⊗ₜ y) :=
  (pushforwardTensorMap_unit_tmul f F G V x y).trans
    (sheafTensorPairing_app_tmul ((opensMap f).obj V.unop) F G
      (op (Over.mk (𝟙 ((opensMap f).obj V.unop)))) x y).symm

end Stacks.RingedSpace

end
