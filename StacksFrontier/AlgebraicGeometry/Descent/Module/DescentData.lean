module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksCore.Tactic.StacksAttribute

/-!
# Descent data for modules along a ring homomorphism

For a homomorphism of commutative rings `R → A`, a descent datum is an `A`-module together
with an isomorphism between its two pullbacks to `A ⊗[R] A`.  The isomorphism is required to
satisfy the usual cocycle condition.  Morphisms are `A`-linear maps compatible with the
transition isomorphisms.

A descent datum is *effective* when it is isomorphic to the canonical datum obtained from an
`R`-module by extension of scalars.

## Main definitions

* `ModuleCat.DescentData` is the category of descent data for modules along a ring
  homomorphism.
* `ModuleCat.DescentData.transition` is the `A ⊗[R] A`-linear transition isomorphism
  `N ⊗[R] A ≃ A ⊗[R] N`.
* `ModuleCat.DescentData.Hom` is the type of morphisms of descent data.
* `ModuleCat.DescentData.IsEffective` says that a module descent datum is effective.

## Implementation notes

The two canonical `A ⊗[R] A`-module structures are constructed explicitly: on `N ⊗[R] A`,
`(a ⊗ b) • (n ⊗ c) = (a • n) ⊗ bc`, while on `A ⊗[R] N`,
`(a ⊗ b) • (c ⊗ n) = ac ⊗ (b • n)`.  Thus the transition isomorphism is bundled
with precisely the linearity required in the source.  The maps `transition01`, `transition12`,
and `transition02` are the three pullbacks of the transition isomorphism to a triple tensor
product, so the `cocycle` field is exactly the commuting triangle in the source.

Extension of scalars is represented as `A ⊗[R] M`, rather than the isomorphic `M ⊗[R] A`.
The equality displayed by `DescentData.IsEffective` is compatibility with the canonical
transition map `(a ⊗ m) ⊗ b ↦ a ⊗ (b ⊗ m)`.  Since pure tensors generate both tensor
products, it is precisely the condition that the module isomorphism be an isomorphism of
descent data.  The definition is an abbreviation so clients can use this existential
description directly.

## References

* [Stacks Project, Tag 023G](https://stacks.math.columbia.edu/tag/023G)
* [Stacks Project, Tag 023J](https://stacks.math.columbia.edu/tag/023J)
-/

@[expose] public section

universe u v w

noncomputable section

namespace ModuleCat

open CategoryTheory TensorProduct

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]

/-- An `A`-module regarded as an `R`-module. -/
abbrev restrictModule (N : ModuleCat.{w} A) : ModuleCat.{w} R :=
  (ModuleCat.restrictScalars (algebraMap R A)).obj N

/-- An `A`-linear map regarded as an `R`-linear map. -/
abbrev restrictHom {N P : ModuleCat.{w} A} (g : N ⟶ P) :
    restrictModule R A N →ₗ[R] restrictModule R A P :=
  ((ModuleCat.restrictScalars (algebraMap R A)).map g).hom

/-- Restricting the identity of an `A`-module gives the identity `R`-linear map. -/
@[simp]
lemma restrictHom_id (N : ModuleCat.{w} A) :
    restrictHom R A (𝟙 N) = LinearMap.id := by ext x; rfl

/-- Restriction of scalars of `A`-linear maps preserves composition. -/
@[simp]
lemma restrictHom_comp {N P Q : ModuleCat.{w} A} (g : N ⟶ P) (h : P ⟶ Q) :
    restrictHom R A (g ≫ h) =
      (restrictHom R A h).comp (restrictHom R A g) := by ext x; rfl

/-- The action of `A` on an `A`-module after restriction of scalars to `R`. -/
def restrictedScalarAction (N : ModuleCat.{w} A) :
    A →ₐ[R] Module.End R (restrictModule R A N) where
  toFun a := restrictHom R A (ModuleCat.ofHom (LinearMap.lsmul A N a))
  map_one' := by
    ext x
    change (1 : A) • (show N from x) = (show N from x)
    exact one_smul A _
  map_mul' a b := by
    ext x
    change (a * b) • (show N from x) = a • b • (show N from x)
    exact mul_smul a b _
  map_zero' := by
    ext x
    change (0 : A) • (show N from x) = 0
    exact zero_smul A _
  map_add' a b := by
    ext x
    change (a + b) • (show N from x) =
      a • (show N from x) + b • (show N from x)
    exact add_smul a b _
  commutes' r := by
    ext x
    change (algebraMap R A r) • (show N from x) = r • x
    simp

/-- `restrictedScalarAction R A N a` acts on `N` as multiplication by `a`. -/
@[simp]
lemma restrictedScalarAction_apply (N : ModuleCat.{w} A) (a : A)
    (n : restrictModule R A N) :
    (show N from restrictedScalarAction R A N a n) = a • (show N from n) := rfl

/-- The first-factor action on `N ⊗[R] A`. -/
def sourceLeftAction (N : ModuleCat.{w} A) :
    A →ₐ[R] Module.End R (restrictModule R A N ⊗[R] A) :=
  (Module.End.rTensorAlgHom R (restrictModule R A N) A).comp
    (restrictedScalarAction R A N)

/-- The second-factor action on `N ⊗[R] A`. -/
def sourceRightAction (N : ModuleCat.{w} A) :
    A →ₐ[R] Module.End R (restrictModule R A N ⊗[R] A) :=
  (Module.End.lTensorAlgHom R A (restrictModule R A N)).comp (Algebra.lsmul R R A)

/-- The first-factor and second-factor actions of `A` on `N ⊗[R] A` commute. -/
lemma source_actions_commute (N : ModuleCat.{w} A) (a b : A) :
    Commute (sourceLeftAction R A N a) (sourceRightAction R A N b) := by
  rw [Commute]; ext n c; rfl

/-- The representation of `A ⊗[R] A` on `N ⊗[R] A`. -/
def sourceTensorAction (N : ModuleCat.{w} A) :
    A ⊗[R] A →ₐ[R] Module.End R (restrictModule R A N ⊗[R] A) :=
  Algebra.TensorProduct.lift (sourceLeftAction R A N) (sourceRightAction R A N)
    (source_actions_commute R A N)

/-- The `A ⊗[R] A`-module structure on `N ⊗[R] A` given by `sourceTensorAction`. -/
instance sourceTensorModule (N : ModuleCat.{w} A) :
    Module (A ⊗[R] A) (restrictModule R A N ⊗[R] A) :=
  Module.compHom _ (sourceTensorAction R A N).toRingHom

/-- On `N ⊗[R] A`, `(a ⊗ b) • (n ⊗ c) = (a • n) ⊗ bc`. -/
@[simp]
lemma sourceTensor_smul_tmul (N : ModuleCat.{w} A) (a b c : A)
    (n : restrictModule R A N) :
    (a ⊗ₜ[R] b) • (n ⊗ₜ[R] c) =
      (restrictedScalarAction R A N a n) ⊗ₜ[R] (b * c) := rfl

/-- The first-factor action on `A ⊗[R] N`. -/
def targetLeftAction (N : ModuleCat.{w} A) :
    A →ₐ[R] Module.End R (A ⊗[R] restrictModule R A N) :=
  (Module.End.rTensorAlgHom R A (restrictModule R A N)).comp (Algebra.lsmul R R A)

/-- The second-factor action on `A ⊗[R] N`. -/
def targetRightAction (N : ModuleCat.{w} A) :
    A →ₐ[R] Module.End R (A ⊗[R] restrictModule R A N) :=
  (Module.End.lTensorAlgHom R (restrictModule R A N) A).comp
    (restrictedScalarAction R A N)

/-- The first-factor and second-factor actions of `A` on `A ⊗[R] N` commute. -/
lemma target_actions_commute (N : ModuleCat.{w} A) (a b : A) :
    Commute (targetLeftAction R A N a) (targetRightAction R A N b) := by
  rw [Commute]; ext c n; rfl

/-- The representation of `A ⊗[R] A` on `A ⊗[R] N`. -/
def targetTensorAction (N : ModuleCat.{w} A) :
    A ⊗[R] A →ₐ[R] Module.End R (A ⊗[R] restrictModule R A N) :=
  Algebra.TensorProduct.lift (targetLeftAction R A N) (targetRightAction R A N)
    (target_actions_commute R A N)

/-- The `A ⊗[R] A`-module structure on `A ⊗[R] N` given by `targetTensorAction`. -/
instance targetTensorModule (N : ModuleCat.{w} A) :
    Module (A ⊗[R] A) (A ⊗[R] restrictModule R A N) :=
  Module.compHom _ (targetTensorAction R A N).toRingHom

/-- On `A ⊗[R] N`, `(a ⊗ b) • (c ⊗ n) = ac ⊗ (b • n)`. -/
@[simp]
lemma targetTensor_smul_tmul (N : ModuleCat.{w} A) (a b c : A)
    (n : restrictModule R A N) :
    (a ⊗ₜ[R] b) • (c ⊗ₜ[R] n) =
      (a * c) ⊗ₜ[R] (restrictedScalarAction R A N b n) := rfl

/-- The `R`-action on `N ⊗[R] A` factors through the `A ⊗[R] A`-module structure. -/
instance sourceTensor_isScalarTower (N : ModuleCat.{w} A) :
    IsScalarTower R (A ⊗[R] A) (restrictModule R A N ⊗[R] A) :=
  IsScalarTower.of_algebraMap_smul (fun r x ↦ by
    induction x with
    | zero => simp
    | add x y hx hy => simp_all
    | tmul n a =>
      rw [show algebraMap R (A ⊗[R] A) r = algebraMap R A r ⊗ₜ[R] 1 from rfl,
        sourceTensor_smul_tmul, one_mul]
      change (restrictedScalarAction R A N (algebraMap R A r) n) ⊗ₜ[R] a =
        (r • n) ⊗ₜ[R] a
      congr 1)

/-- The `R`-action on `A ⊗[R] N` factors through the `A ⊗[R] A`-module structure. -/
instance targetTensor_isScalarTower (N : ModuleCat.{w} A) :
    IsScalarTower R (A ⊗[R] A) (A ⊗[R] restrictModule R A N) :=
  IsScalarTower.of_algebraMap_smul (fun r x ↦ by
    induction x with
    | zero => simp
    | add x y hx hy => simp_all
    | tmul a n =>
      rw [show algebraMap R (A ⊗[R] A) r = algebraMap R A r ⊗ₜ[R] 1 from rfl,
        targetTensor_smul_tmul]
      rw [show restrictedScalarAction R A N 1 n = n from
        LinearMap.congr_fun ((restrictedScalarAction R A N).map_one) n]
      change ((algebraMap R A r) * a) ⊗ₜ[R] n = r • (a ⊗ₜ[R] n)
      exact congrArg (fun z : A ↦ z ⊗ₜ[R] n) (Algebra.smul_def r a).symm)

/-- The pullback of a transition isomorphism along the inclusion of tensor positions `0, 1`. -/
def transition01 (N : ModuleCat.{w} A)
    (e : (restrictModule R A N ⊗[R] A) ≃ₗ[A ⊗[R] A]
      (A ⊗[R] restrictModule R A N)) :
    ((restrictModule R A N ⊗[R] A) ⊗[R] A) →ₗ[R]
      ((A ⊗[R] restrictModule R A N) ⊗[R] A) :=
  (e.toLinearMap.restrictScalars R).rTensor A

/-- The pullback of a transition isomorphism along the inclusion of tensor positions `1, 2`. -/
def transition12 (N : ModuleCat.{w} A)
    (e : (restrictModule R A N ⊗[R] A) ≃ₗ[A ⊗[R] A]
      (A ⊗[R] restrictModule R A N)) :
    ((A ⊗[R] restrictModule R A N) ⊗[R] A) →ₗ[R]
      ((A ⊗[R] A) ⊗[R] restrictModule R A N) :=
  (TensorProduct.assoc R A A (restrictModule R A N)).symm.toLinearMap.comp
    (((e.toLinearMap.restrictScalars R).lTensor A).comp
      (TensorProduct.assoc R A (restrictModule R A N) A).toLinearMap)

/-- The pullback of a transition isomorphism along the inclusion of tensor positions `0, 2`. -/
def transition02 (N : ModuleCat.{w} A)
    (e : (restrictModule R A N ⊗[R] A) ≃ₗ[A ⊗[R] A]
      (A ⊗[R] restrictModule R A N)) :
    ((restrictModule R A N ⊗[R] A) ⊗[R] A) →ₗ[R]
      ((A ⊗[R] A) ⊗[R] restrictModule R A N) :=
  (TensorProduct.rightComm R A (restrictModule R A N) A).toLinearMap.comp
    (((e.toLinearMap.restrictScalars R).rTensor A).comp
      (TensorProduct.rightComm R (restrictModule R A N) A A).toLinearMap)

/-- A descent datum for modules for an `R`-algebra `A`.

The transition is bundled as an `A ⊗[R] A`-linear equivalence, and `cocycle` is the equality
`φ₁₂ ∘ φ₀₁ = φ₀₂`. -/
@[stacks 023G "descent data",
  stacks 08WX "the cocycle condition, as the cocycle field",
  stacks 03OB "descent datum for a module along a ring map"]
structure DescentData where
  /-- The underlying `A`-module. -/
  module : ModuleCat.{w} A
  /-- The isomorphism between the two pullbacks of the underlying module. -/
  transition : (restrictModule R A module ⊗[R] A) ≃ₗ[A ⊗[R] A]
    (A ⊗[R] restrictModule R A module)
  /-- The cocycle condition on the triple tensor product. -/
  cocycle : (transition12 R A module transition).comp (transition01 R A module transition) =
    transition02 R A module transition

namespace DescentData

/-- The transition isomorphism after restricting scalars from `A ⊗[R] A` to `R`. -/
def transitionRestrictScalars (D : DescentData.{u, v, w} R A) :
    (restrictModule R A D.module ⊗[R] A) ≃ₗ[R]
      (A ⊗[R] restrictModule R A D.module) :=
  D.transition.restrictScalars R

/-- `transitionRestrictScalars` agrees with the transition isomorphism on elements. -/
@[simp]
lemma transitionRestrictScalars_apply (D : DescentData.{u, v, w} R A)
    (x : restrictModule R A D.module ⊗[R] A) :
    D.transitionRestrictScalars R A x = D.transition x := rfl

/-- A morphism of module descent data is an `A`-linear map commuting with the transition
isomorphisms. -/
@[stacks 023G "morphisms", ext]
structure Hom (D E : DescentData.{u, v, w} R A) where
  /-- The underlying `A`-linear map. -/
  hom : D.module ⟶ E.module
  /-- The compatibility square with the transition isomorphisms. -/
  comm : (E.transition.toLinearMap.restrictScalars R).comp
      ((restrictHom R A hom).rTensor A) =
    ((restrictHom R A hom).lTensor A).comp
      (D.transition.toLinearMap.restrictScalars R)

/-- Identity morphism of module descent data. -/
def Hom.id (D : DescentData.{u, v, w} R A) : Hom R A D D where
  hom := 𝟙 D.module
  comm := by simp [restrictHom_id]

/-- Composition of morphisms of module descent data. -/
def Hom.comp {D E F : DescentData.{u, v, w} R A}
    (g : Hom R A D E) (h : Hom R A E F) : Hom R A D F where
  hom := g.hom ≫ h.hom
  comm := by
    rw [restrictHom_comp, LinearMap.rTensor_comp, LinearMap.lTensor_comp,
      ← LinearMap.comp_assoc, h.comm, LinearMap.comp_assoc, g.comm, ← LinearMap.comp_assoc]

/-- Module descent data with their morphisms, identities and composition. -/
instance : CategoryTheory.CategoryStruct (DescentData.{u, v, w} R A) where
  Hom := Hom R A
  id := Hom.id R A
  comp := Hom.comp R A

/-- The category of module descent data. -/
instance : CategoryTheory.Category (DescentData.{u, v, w} R A) where
  id_comp g := by apply Hom.ext; exact Category.id_comp g.hom
  comp_id g := by apply Hom.ext; exact Category.comp_id g.hom
  assoc g h k := by apply Hom.ext; exact Category.assoc g.hom h.hom k.hom

end DescentData

/-- A module descent datum is effective if it is isomorphic to the canonical descent datum
obtained by extending scalars from an `R`-module. -/
@[stacks 023J, stacks 03OC "effectivity of a module descent datum"]
abbrev DescentData.IsEffective (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    [Algebra R A] (D : DescentData.{u, v, w} R A) : Prop :=
  ∃ (M : ModuleCat.{w} R) (e : (A ⊗[R] M) ≃ₗ[A] D.module), ∀ (a b : A) (m : M),
    D.transition ((e (a ⊗ₜ[R] m)) ⊗ₜ[R] b) =
      a ⊗ₜ[R] (show restrictModule R A D.module from e (b ⊗ₜ[R] m))

end ModuleCat

end
