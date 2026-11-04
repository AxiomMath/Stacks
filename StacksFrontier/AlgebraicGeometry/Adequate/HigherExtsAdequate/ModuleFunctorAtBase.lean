module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.Algebra.Module.Adequate.Defs

/-!
# Morphisms out of the module-valued functor of a module

Let `A` be a ring and let `M` be an `A`-module.  A morphism of module-valued functors out of
`B ↦ B ⊗[A] M` is the same thing as its single component at the base algebra: extension of
scalars is left adjoint to evaluation at `A`.  The lifted base ring `ULift A` is the initial
object of `Alg_A`, so for every algebra `B` the value at a pure tensor `b ⊗ m` is forced to be
`b` times the transport of the value at `1 ⊗ m`, and conversely any prescribed component at
the base algebra extends by that formula.

## Main results

* `AdequateFunctor.bijective_app_baseAlgebra`: taking the component at the base algebra is a
  bijection from the morphisms out of `B ↦ B ⊗[A] M` onto *all* linear maps out of its value
  there.
* `AdequateFunctor.projective_moduleExtension`: the module-valued functor of a projective
  module is a projective object, since an epimorphism of module-valued functors is surjective
  at every algebra.

## Implementation notes

The `A`-module structure that a tensor product over `A` would want on a value `F(B)` is not
available there — a value is a module over its own algebra — so the component is built with
`TensorProduct.liftAddHom`, whose balancing condition is checked against the algebra's
structure morphism, and `B`-linearity is then checked on pure tensors.
-/


@[expose] public section

open CategoryTheory

universe v u w

namespace AdequateFunctor

/-- The base ring, lifted to the universe of the algebras, as an object of the index category
of module-valued functors.  It is the initial object of `Alg_A`. -/
abbrev liftedBaseAlgebra (A : Type u) [CommRing A] : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ :=
  Opposite.op (Opposite.op (CommAlgCat.of A (ULift.{v} A)))

/-- The structure morphism of an `A`-algebra, viewed as a morphism out of the lifted base
ring. -/
noncomputable def baseAlgebraHom (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A) :
    CommAlgCat.of A (ULift.{v} A) ⟶ B :=
  CommAlgCat.ofHom ((Algebra.ofId A B).comp ULift.algEquiv.toAlgHom)

variable {A : Type u} [CommRing A]

/-- The lifted base ring is initial in `Alg_A`: every morphism out of it is the structure
morphism. -/
lemma eq_baseAlgebraHom {B : CommAlgCat.{max u v} A}
    (f : CommAlgCat.of A (ULift.{v} A) ⟶ B) : f = baseAlgebraHom.{v} A B := by
  refine CommAlgCat.hom_ext (AlgHom.ext fun x => ?_)
  show f.hom x = algebraMap A B x.down
  rw [show x = algebraMap A (ULift.{v} A) x.down from rfl]
  exact f.hom.commutes x.down

section Transitions

variable {F : ModuleValuedFunctor.{max u v w, v} A}

/-- Semilinearity of a transition map of a module-valued functor, with the scalar written as
an element of the source algebra. -/
lemma map_smul_algebra {X Y : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ} (f : X ⟶ Y)
    (b : X.unop.unop) (y : F.obj X) :
    F.map f (b • y) = f.unop.unop.hom b • F.map f y :=
  PresheafOfModules.map_smul F f b y

/-- Functoriality of the transition maps of a module-valued functor, in composed form. -/
lemma map_map {X Y Z : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ} (i : X ⟶ Y) (j : Y ⟶ Z) (y : F.obj X) :
    F.map j (F.map i y) = F.map (i ≫ j) y :=
  (PresheafOfModules.map_comp_apply F i j y).symm

/-- The transition map along the structure morphism of the base algebra itself is the
identity. -/
lemma map_baseAlgebraHom_self (y : F.obj (liftedBaseAlgebra.{v} A)) :
    F.map (baseAlgebraHom.{v} A (CommAlgCat.of A (ULift.{v} A))).op.op y = y := by
  rw [show (baseAlgebraHom.{v} A (CommAlgCat.of A (ULift.{v} A))).op.op =
    𝟙 (liftedBaseAlgebra.{v} A) from congrArg (fun g => Quiver.Hom.op (Quiver.Hom.op g))
      (eq_baseAlgebraHom (𝟙 (CommAlgCat.of A (ULift.{v} A)))).symm]
  refine (CategoryTheory.congr_fun (F.map_id (liftedBaseAlgebra.{v} A)) y).trans ?_
  exact ModuleCat.restrictScalarsId'App_inv_apply _ (by simp) _ y

end Transitions

section Determined

variable {M : ModuleCat.{w} A} {F : ModuleValuedFunctor.{max u v w, v} A}

/-- A pure tensor `b ⊗ m` is `b` times the pure tensor `1 ⊗ m`. -/
private lemma tmul_eq_smul_one_tmul (X : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ) (b : X.unop.unop)
    (m : M) :
    (b ⊗ₜ[A] m : (moduleExtension.{w, v} A M).obj X) = b • ((1 : X.unop.unop) ⊗ₜ[A] m) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- A morphism out of the module-valued functor of `M` is determined by its component at the
base algebra: at a pure tensor it is `b` times the transport of the value at `1 ⊗ m`. -/
lemma app_tmul_eq (η : moduleExtension.{w, v} A M ⟶ F)
    (X : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ) (b : X.unop.unop) (m : M) :
    η.app X (b ⊗ₜ[A] m) =
      b • F.map (baseAlgebraHom.{v} A X.unop.unop).op.op
        (η.app (liftedBaseAlgebra.{v} A) ((1 : ULift.{v} A) ⊗ₜ[A] m)) := by
  have hone : (moduleExtension.{w, v} A M).map (baseAlgebraHom.{v} A X.unop.unop).op.op
      ((1 : ULift.{v} A) ⊗ₜ[A] m) = (1 : X.unop.unop) ⊗ₜ[A] m :=
    (moduleExtension_map_tmul A M _ 1 m).trans (by rw [map_one])
  have key : η.app X ((1 : X.unop.unop) ⊗ₜ[A] m) =
      F.map (baseAlgebraHom.{v} A X.unop.unop).op.op
        (η.app (liftedBaseAlgebra.{v} A) ((1 : ULift.{v} A) ⊗ₜ[A] m)) := by
    rw [← hone]
    exact PresheafOfModules.naturality_apply η _ _
  rw [← key, tmul_eq_smul_one_tmul, map_smul]
  rfl

/-- Two morphisms out of the module-valued functor of `M` with the same component at the base
algebra are equal. -/
lemma hom_ext_of_app_baseAlgebra {η θ : moduleExtension.{w, v} A M ⟶ F}
    (h : η.app (liftedBaseAlgebra.{v} A) = θ.app (liftedBaseAlgebra.{v} A)) : η = θ := by
  refine PresheafOfModules.hom_ext fun X => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  induction x using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul b m =>
    rw [app_tmul_eq η X b m, app_tmul_eq θ X b m]
    exact congrArg (fun y => b • F.map (baseAlgebraHom.{v} A X.unop.unop).op.op y)
      (congrArg (fun k : (moduleExtension.{w, v} A M).obj (liftedBaseAlgebra.{v} A) ⟶
        F.obj (liftedBaseAlgebra.{v} A) => k ((1 : ULift.{v} A) ⊗ₜ[A] m)) h)
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end Determined

section Construct

variable {M : ModuleCat.{w} A} {F : ModuleValuedFunctor.{max u v w, v} A}
  (ψ : (moduleExtension.{w, v} A M).obj (liftedBaseAlgebra.{v} A) ⟶ F.obj (liftedBaseAlgebra.{v} A))

/-- The value at an algebra of the morphism extending a prescribed component at the base
algebra, as an additive map on the tensor product. -/
noncomputable def appAddHomOfAppBase (X : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ) :
    (moduleExtension.{w, v} A M).obj X →+ F.obj X := by
  refine TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun b : X.unop.unop =>
      AddMonoidHom.mk' (fun m : M => b • F.map (baseAlgebraHom.{v} A X.unop.unop).op.op
        (ψ ((1 : ULift.{v} A) ⊗ₜ[A] m))) ?_) ?_) ?_
  · intro m₁ m₂
    simp only [TensorProduct.tmul_add, map_add, smul_add]
    rfl
  · intro b₁ b₂
    refine AddMonoidHom.ext fun m => ?_
    exact add_smul b₁ b₂ _
  · intro a b m
    have h₁ : ((1 : ULift.{v} A) ⊗ₜ[A] (a • m) :
        (moduleExtension.{w, v} A M).obj (liftedBaseAlgebra.{v} A)) =
        algebraMap A (ULift.{v} A) a • ((1 : ULift.{v} A) ⊗ₜ[A] m) := by
      rw [← TensorProduct.smul_tmul]
      rfl
    change (a • b) • F.map (baseAlgebraHom.{v} A X.unop.unop).op.op
        (ψ ((1 : ULift.{v} A) ⊗ₜ[A] m)) =
      b • F.map (baseAlgebraHom.{v} A X.unop.unop).op.op
        (ψ ((1 : ULift.{v} A) ⊗ₜ[A] (a • m)))
    have h₂ : ψ (algebraMap A (ULift.{v} A) a • ((1 : ULift.{v} A) ⊗ₜ[A] m)) =
        algebraMap A (ULift.{v} A) a • ψ ((1 : ULift.{v} A) ⊗ₜ[A] m) :=
      (ConcreteCategory.hom ψ).map_smul _ _
    have h₃ : F.map (baseAlgebraHom.{v} A X.unop.unop).op.op
          (algebraMap A (ULift.{v} A) a • ψ ((1 : ULift.{v} A) ⊗ₜ[A] m)) =
        algebraMap A X.unop.unop a • F.map (baseAlgebraHom.{v} A X.unop.unop).op.op
          (ψ ((1 : ULift.{v} A) ⊗ₜ[A] m)) :=
      PresheafOfModules.map_smul F _ _ _
    rw [h₁, h₂, h₃, Algebra.smul_def, smul_smul, mul_comm]

/-- On a pure tensor `b ⊗ m`, the extending component is `b` times the image of `ψ (1 ⊗ m)`
under the transition map of `F` from the base algebra. -/
@[simp] lemma appAddHomOfAppBase_tmul (X : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ)
    (b : X.unop.unop) (m : M) :
    appAddHomOfAppBase ψ X (b ⊗ₜ[A] m) =
      b • F.map (baseAlgebraHom.{v} A X.unop.unop).op.op
        (ψ ((1 : ULift.{v} A) ⊗ₜ[A] m)) :=
  TensorProduct.liftAddHom_tmul _ _ b m

/-- The extending component is linear over the algebra. -/
lemma appAddHomOfAppBase_smul (X : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ) (c : X.unop.unop)
    (x : (moduleExtension.{w, v} A M).obj X) :
    appAddHomOfAppBase ψ X (c • x) = c • appAddHomOfAppBase ψ X x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul b m =>
    rw [TensorProduct.smul_tmul', appAddHomOfAppBase_tmul, appAddHomOfAppBase_tmul,
      smul_eq_mul, mul_smul]
    rfl
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- The extending component commutes with the transition maps. -/
lemma appAddHomOfAppBase_naturality {X Y : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ} (f : X ⟶ Y)
    (x : (moduleExtension.{w, v} A M).obj X) :
    appAddHomOfAppBase ψ Y ((moduleExtension.{w, v} A M).map f x) =
      F.map f (appAddHomOfAppBase ψ X x) := by
  induction x using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul b m =>
    have hcomp : (baseAlgebraHom.{v} A X.unop.unop).op.op ≫ f =
        (baseAlgebraHom.{v} A Y.unop.unop).op.op := by
      refine Quiver.Hom.unop_inj (Quiver.Hom.unop_inj ?_)
      show baseAlgebraHom.{v} A X.unop.unop ≫ f.unop.unop =
        baseAlgebraHom.{v} A Y.unop.unop
      exact eq_baseAlgebraHom _
    have h₄ := map_smul_algebra (F := F) f b
      (F.map (baseAlgebraHom.{v} A X.unop.unop).op.op
        (ψ ((1 : ULift.{v} A) ⊗ₜ[A] m)))
    have h₅ := map_map (F := F) (baseAlgebraHom.{v} A X.unop.unop).op.op f
      (ψ ((1 : ULift.{v} A) ⊗ₜ[A] m))
    rw [moduleExtension_map_tmul, appAddHomOfAppBase_tmul, appAddHomOfAppBase_tmul,
      ← hcomp, ← h₅]
    exact h₄.symm
  | add x y hx hy =>
    refine (congrArg (fun z => appAddHomOfAppBase ψ Y z) (map_add _ x y)).trans ?_
    refine (map_add _ _ _).trans ?_
    refine (congrArg₂ (· + ·) hx hy).trans ?_
    refine ((map_add _ _ _).symm).trans ?_
    exact congrArg (fun z => F.map f z) (map_add _ x y).symm

/-- The morphism of module-valued functors out of `B ↦ B ⊗[A] M` extending a prescribed
component at the base algebra. -/
noncomputable def homOfAppBase : moduleExtension.{w, v} A M ⟶ F :=
  PresheafOfModules.homMk
    { app := fun X => AddCommGrpCat.ofHom (appAddHomOfAppBase ψ X)
      naturality := fun X Y f => by
        ext x
        exact appAddHomOfAppBase_naturality ψ f x }
    (fun X c x => appAddHomOfAppBase_smul ψ X c x)

/-- The extending morphism does have the prescribed component at the base algebra. -/
@[simp] lemma homOfAppBase_app_baseAlgebra :
    (homOfAppBase ψ).app (liftedBaseAlgebra.{v} A) = ψ := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  induction x using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul b m =>
    show appAddHomOfAppBase ψ (liftedBaseAlgebra.{v} A) (b ⊗ₜ[A] m) = ψ (b ⊗ₜ[A] m)
    rw [appAddHomOfAppBase_tmul, map_baseAlgebraHom_self,
      tmul_eq_smul_one_tmul (liftedBaseAlgebra.{v} A) b m]
    exact ((ConcreteCategory.hom ψ).map_smul b _).symm
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

end Construct

section Adjunction

variable (M : ModuleCat.{w} A) (F : ModuleValuedFunctor.{max u v w, v} A)

/-- **Extension of scalars is left adjoint to evaluation at the base algebra.**  Taking the
component at the base algebra is a bijection from the morphisms of module-valued functors out
of `B ↦ B ⊗[A] M` onto all linear maps out of the value of that functor there. -/
theorem bijective_app_baseAlgebra :
    Function.Bijective fun η : moduleExtension.{w, v} A M ⟶ F =>
      η.app (liftedBaseAlgebra.{v} A) :=
  ⟨fun _ _ h => hom_ext_of_app_baseAlgebra h,
    fun ψ => ⟨homOfAppBase ψ, homOfAppBase_app_baseAlgebra ψ⟩⟩

end Adjunction

section Projective

open Limits

variable (Q : ModuleCat.{w} A) [Module.Projective A Q]

/-- **The module-valued functor of a projective module is a projective object.**  A morphism
out of it is a linear map out of a projective module over the base algebra, by
`AdequateFunctor.bijective_app_baseAlgebra`, and an epimorphism of module-valued functors is
surjective at every algebra. -/
instance projective_moduleExtension : Projective (moduleExtension.{w, v} A Q) where
  factors {E X} f e he := by
    have hsurj : Function.Surjective (e.app (liftedBaseAlgebra.{v} A)).hom :=
      PresheafOfModules.surjective_of_epi (f := e) (liftedBaseAlgebra.{v} A)
    obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property
      (h := Module.Projective.tensorProduct (R := ULift.{v} A) (R₀ := A)
        (M := ULift.{v} A) (N := Q))
      (e.app (liftedBaseAlgebra.{v} A)).hom (f.app (liftedBaseAlgebra.{v} A)).hom hsurj
    refine ⟨homOfAppBase (ModuleCat.ofHom ψ), hom_ext_of_app_baseAlgebra ?_⟩
    rw [PresheafOfModules.comp_app, homOfAppBase_app_baseAlgebra]
    exact ModuleCat.hom_ext hψ

end Projective

end AdequateFunctor

end
