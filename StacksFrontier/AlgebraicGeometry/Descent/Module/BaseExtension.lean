module

public import StacksFrontier.AlgebraicGeometry.Descent.Module.DescentData
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base extension and descent morphisms for modules

For a homomorphism of commutative rings, extension of scalars carries its canonical descent
datum.  This gives the base-extension functor from modules over the source to module descent
data over the target.  A descent morphism is one for which this functor is fully faithful, and
an effective descent morphism is one for which it is an equivalence.

## Main definitions

* `ModuleCat.baseExtension` is the functor from modules to their canonical descent data.
* `ModuleCat.IsDescentMorphismForModules` means that base extension is fully faithful.
* `ModuleCat.IsEffectiveDescentMorphismForModules` means that base extension is an equivalence.

## Main results

* `ModuleCat.canonicalFunctor` assembles the canonical descent datum of an extension of
  scalars into a functor.

## Implementation notes

The construction records the standard identification of its underlying module with extension
of scalars.  Under this identification its transition sends `(a ⊗ m) ⊗ b` to
`a ⊗ (b ⊗ m)`, and the identifications are natural in the module.  Thus the functor is fixed as
the canonical base-extension functor, rather than merely as an arbitrary functor between the
same categories.  Both module categories use universe `max v w`, so base extension can be an
equivalence even when the target ring lives in a larger universe than the source ring.
Full faithfulness is propositionally truncated because Mathlib packages the
corresponding data in `Functor.FullyFaithful`.

## References

* [Stacks Project, Tag 08WY](https://stacks.math.columbia.edu/tag/08WY)
-/

@[expose] public section

universe u v w

noncomputable section

open CategoryTheory TensorProduct
open scoped ChangeOfRings

namespace ModuleCat

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]

/-- Data specifying the canonical base-extension functor.  The last two fields record its
value on objects and morphisms, including the canonical transition map. -/
structure BaseExtension where
  /-- The underlying functor from `R`-modules to module descent data along `R → A`. -/
  functor : ModuleCat.{max v w} R ⥤ DescentData.{u, v, max v w} R A
  /-- The identification of the underlying module with extension of scalars. -/
  comparison (M : ModuleCat.{max v w} R) :
    (functor.obj M).module ≅
      (ModuleCat.extendScalars.{u, v, max v w} (algebraMap R A)).obj M
  /-- The value of the transition isomorphism on pure tensors. -/
  transition_tmul (M : ModuleCat.{max v w} R) (a b : A) (m : M) :
    (functor.obj M).transition
        ((comparison M).inv (a ⊗ₜ[R, algebraMap R A] m) ⊗ₜ[R] b) =
      a ⊗ₜ[R]
        (show restrictModule R A (functor.obj M).module from
          (comparison M).inv (b ⊗ₜ[R, algebraMap R A] m))
  /-- Naturality of the identification in the module. -/
  naturality {M N : ModuleCat.{max v w} R} (g : M ⟶ N) :
    (functor.map g).hom ≫ (comparison N).hom =
      (comparison M).hom ≫
        (ModuleCat.extendScalars.{u, v, max v w} (algebraMap R A)).map g

/-- The underlying `R`-module of an extension of scalars, identified with the tensor product
over `R`. -/
def restrictionEquiv (M : ModuleCat.{max v w} R) :
    restrictModule R A (ModuleCat.of A (A ⊗[R] M)) ≃ₗ[R] (A ⊗[R] M) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change (algebraMap R A r) • (show A ⊗[R] M from x) =
      r • (show A ⊗[R] M from x)
    exact IsScalarTower.algebraMap_smul A r (show A ⊗[R] M from x)

/-- The canonical transition isomorphism of an extension of scalars, sending `(a ⊗ m) ⊗ b` to
`a ⊗ (b ⊗ m)`. -/
def canonicalTransition (M : ModuleCat.{max v w} R) :
    (restrictModule R A
          (ModuleCat.of A (A ⊗[R] M)) ⊗[R] A) ≃ₗ[A ⊗[R] A]
      (A ⊗[R] restrictModule R A
          (ModuleCat.of A (A ⊗[R] M))) where
  toFun := ((TensorProduct.congr (restrictionEquiv R A M) (LinearEquiv.refl R A)) ≪≫ₗ
    TensorProduct.rightComm R A M A ≪≫ₗ TensorProduct.assoc R A A M ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl R A) (restrictionEquiv R A M).symm)
  invFun := (((TensorProduct.congr (restrictionEquiv R A M) (LinearEquiv.refl R A)) ≪≫ₗ
    TensorProduct.rightComm R A M A ≪≫ₗ TensorProduct.assoc R A A M ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl R A) (restrictionEquiv R A M).symm)).symm
  left_inv := (((TensorProduct.congr (restrictionEquiv R A M) (LinearEquiv.refl R A)) ≪≫ₗ
    TensorProduct.rightComm R A M A ≪≫ₗ TensorProduct.assoc R A A M ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl R A) (restrictionEquiv R A M).symm)).left_inv
  right_inv := (((TensorProduct.congr (restrictionEquiv R A M) (LinearEquiv.refl R A)) ≪≫ₗ
    TensorProduct.rightComm R A M A ≪≫ₗ TensorProduct.assoc R A A M ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl R A) (restrictionEquiv R A M).symm)).right_inv
  map_add' := (((TensorProduct.congr (restrictionEquiv R A M) (LinearEquiv.refl R A)) ≪≫ₗ
    TensorProduct.rightComm R A M A ≪≫ₗ TensorProduct.assoc R A A M ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl R A) (restrictionEquiv R A M).symm)).map_add
  map_smul' x y := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [zero_smul, map_zero]
    | add x y hx hy => simp_all only [add_smul, map_add, RingHom.id_apply]
    | tmul a b =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [smul_zero, map_zero]
      | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
      | tmul n c =>
        obtain ⟨n, rfl⟩ := (restrictionEquiv R A M).symm.surjective n
        induction n using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy =>
          rw [map_add, add_tmul, smul_add, map_add, map_add, hx, hy, smul_add]
        | tmul d m => rfl

/-- The canonical descent datum carried by an extension of scalars.

This is reducible so that its `module` and `transition` projections compute, which is what
lets morphisms of descent data out of it be given by their underlying `A`-linear maps. -/
abbrev canonicalDatum (M : ModuleCat.{max v w} R) :
    DescentData.{u, v, max v w} R A where
  module := ModuleCat.of A (A ⊗[R] M)
  transition := canonicalTransition R A M
  cocycle := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add u v hu hv => rw [map_add, map_add, hu, hv]
    | tmul x c =>
      induction x using TensorProduct.induction_on with
      | zero => rw [zero_tmul, map_zero, map_zero]
      | add u v hu hv => rw [add_tmul, map_add, map_add, hu, hv]
      | tmul y b =>
        obtain ⟨y, rfl⟩ := (restrictionEquiv R A M).symm.surjective y
        induction y using TensorProduct.induction_on with
        | zero => rw [map_zero, zero_tmul, zero_tmul, map_zero, map_zero]
        | add u v hu hv =>
          rw [map_add (restrictionEquiv R A M).symm, add_tmul, add_tmul,
            map_add, map_add, hu, hv]
        | tmul a m => rfl

/-- The morphism of canonical descent data induced by a map of `R`-modules. -/
def canonicalMap {M N : ModuleCat.{max v w} R} (g : M ⟶ N) :
    canonicalDatum R A M ⟶ canonicalDatum R A N where
  hom := ModuleCat.ofHom (LinearMap.baseChange A g.hom)
  comm := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add u v hu hv => rw [map_add, map_add, hu, hv]
    | tmul x b =>
      obtain ⟨x, rfl⟩ := (restrictionEquiv R A M).symm.surjective x
      induction x using TensorProduct.induction_on with
      | zero => rw [map_zero, zero_tmul, map_zero, map_zero]
      | add u v hu hv =>
        rw [map_add (restrictionEquiv R A M).symm, add_tmul, map_add, map_add, hu, hv]
      | tmul a m => rfl

/-- Extension of scalars as a functor from `R`-modules to module descent data. -/
def canonicalFunctor :
    CategoryTheory.Functor (ModuleCat.{max v w} R)
      (DescentData.{u, v, max v w} R A) where
  obj := canonicalDatum R A
  map := canonicalMap R A
  map_id M := by
    apply DescentData.Hom.ext
    dsimp only [canonicalMap, canonicalDatum]
    apply ModuleCat.hom_ext
    change LinearMap.baseChange A (𝟙 M : M ⟶ M).hom = LinearMap.id
    ext x
    rfl
  map_comp g h := by
    apply DescentData.Hom.ext
    dsimp only [canonicalMap, canonicalDatum]
    apply ModuleCat.hom_ext
    change LinearMap.baseChange A (g ≫ h).hom =
      (LinearMap.baseChange A h.hom).comp (LinearMap.baseChange A g.hom)
    ext x
    rfl

/-- The algebra `A`, viewed as an `A`-module and restricted back to `R`. -/
def algebraRestrictionEquiv :
    A ≃ₗ[R] (ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A A) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := (IsScalarTower.algebraMap_smul A r x).symm

/-- The identification of `A ⊗[R] M` with Mathlib's extension of scalars. -/
def extensionComparison (M : ModuleCat.{max v w} R) :
    ModuleCat.of A (A ⊗[R] M) ≅
      (ModuleCat.extendScalars.{u, v, max v w} (algebraMap R A)).obj M :=
  LinearEquiv.toModuleIso (show (A ⊗[R] M) ≃ₗ[A]
      (ModuleCat.extendScalars.{u, v, max v w} (algebraMap R A)).obj M from {
    toFun := TensorProduct.congr (algebraRestrictionEquiv R A) (LinearEquiv.refl R M)
    invFun := (TensorProduct.congr (algebraRestrictionEquiv R A)
      (LinearEquiv.refl R M)).symm
    left_inv := (TensorProduct.congr (algebraRestrictionEquiv R A)
      (LinearEquiv.refl R M)).left_inv
    right_inv := (TensorProduct.congr (algebraRestrictionEquiv R A)
      (LinearEquiv.refl R M)).right_inv
    map_add' := (TensorProduct.congr (algebraRestrictionEquiv R A)
      (LinearEquiv.refl R M)).map_add
    map_smul' := by
      intro a x
      induction x using TensorProduct.induction_on with
      | zero =>
        rw [smul_zero, map_zero]
        change (0 : (ModuleCat.extendScalars.{u, v, max v w} (algebraMap R A)).obj M) =
          a • (0 : (ModuleCat.extendScalars.{u, v, max v w} (algebraMap R A)).obj M)
        exact (smul_zero a).symm
      | add x y hx hy =>
        rw [smul_add, map_add, hx, hy, map_add]
        exact (smul_add _ _ _).symm
      | tmul b m => rfl })

/-- **Stacks Project, Tag 08WY.** The base-extension functor from `R`-modules to descent data
for modules along `R → A`, bundled with its canonical objectwise description. -/
@[stacks 08WY "the functor"]
def baseExtension : BaseExtension.{u, v, w} R A where
  functor := canonicalFunctor R A
  comparison := extensionComparison R A
  transition_tmul M a b m := rfl
  naturality g := by
    dsimp only [canonicalFunctor, canonicalDatum, canonicalMap, extensionComparison]
    apply ModuleCat.hom_ext
    ext m
    induction m using TensorProduct.induction_on with
    | zero => rfl
    | add x y hx hy => simp_all
    | tmul a m => rfl

/-- **Stacks Project, Tag 08WY.** An algebra map is a descent morphism for modules when its
base-extension functor is fully faithful. -/
@[stacks 08WY "descent morphism"]
abbrev IsDescentMorphismForModules : Prop :=
  Nonempty (baseExtension.{u, v, w} R A).functor.FullyFaithful

/-- **Stacks Project, Tag 08WY.** An algebra map is an effective descent morphism for modules
when its base-extension functor is an equivalence of categories. -/
@[stacks 08WY "effective descent morphism",
  sga "4 Vbis 2.4.10" "modules over a ring map",
  sga "4 Vbis 2.2.2" "modules over rings"]
abbrev IsEffectiveDescentMorphismForModules : Prop :=
  (baseExtension.{u, v, w} R A).functor.IsEquivalence

end ModuleCat

end
