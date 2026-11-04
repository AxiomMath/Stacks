module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CurryingAnyModuleUniverse
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.TensorHomAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom

/-!
# The tensor–Hom adjunction for the internal Hom on an essentially small ringed site

Let `X` be a ringed site whose underlying category is essentially `w`-small, `w` being the
universe of the structure sheaf and of the modules.
`AlgebraicGeometry.RingedSite.internalHomSheafSmall` is the internal Hom of Stacks 03EM in the
module universe `w`. This file proves Stacks 03EO for it:
tensoring on the right by `L` is left adjoint to internal Hom out of `L`,

`Hom(Z ⊗_O L, K) = Hom(Z, Hom_O(L, K))`.

The existing sheaf and presheaf clauses of Stacks 03EO
(`Stacks.SheafOfModules.InternalHom.sheafTensorHomAdjunction`,
`Stacks.PresheafOfModules.InternalHom.presheafTensorHomAdjunction`) need structure sheaf and
modules in the universe `max u v` of the site, so they do not apply on the small étale site of a
scheme or an algebraic space, where the site universes are `{u + 1, u}` and modules live in `u`.

## Main definitions

* `AlgebraicGeometry.RingedSite.internalHomSheafSmallTensorHomEquiv`: the currying bijection
  `Hom(Z ⊗ L, K) ≃ Hom(Z, Hom(L, K))`, with the presheaf tensor product on the left.
* `AlgebraicGeometry.RingedSite.internalHomSheafSmallAdjunction`: the adjunction
  `(sheafTensor X.O).flip.obj L ⊣ internalHomSheafSmallFunctor X L`.
* `AlgebraicGeometry.RingedSite.internalHomSheafSmallBifunctor`: the small internal Hom as a
  bifunctor `Modᵒᵖ ⥤ Mod ⥤ Mod`, whose value at `op L` is `internalHomSheafSmallFunctor X L`.

## Main results

* `AlgebraicGeometry.RingedSite.internalHomSheafSmallAdjunction_counit_app_val_app`: the counit is
  evaluation on sheafified pure tensors.
* `AlgebraicGeometry.RingedSite.internalHomSheafSmallAdjunction_homEquiv_app`: the
  hom-equivalence is currying on sections.

## Implementation notes

The currying maps are those of the presheaf clause of Stacks 03EO in the namespace
`Stacks.PresheafOfModules.InternalHom.AnyUniverse` (`AnyUniverse.curryGlobalMap`,
`AnyUniverse.evalAtIdLinear`, ...), which are stated in an arbitrary module universe; only the
final step, a morphism into the internal Hom presheaf, needs the universe `max u v`. Here that step
is replaced by a morphism into the descended internal Hom, conjugating by `Shrink.linearEquiv`
sectionwise (`internalHomSheafSmallSectionEquiv`).

## References

* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite MonoidalCategory
open Stacks.PresheafOfModules.InternalHom

universe u v w

namespace Stacks.PresheafOfModules.InternalHom

attribute [local instance 5000] SheafOfModules.instAbelian


variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat.{w})

/-- Global currying is natural in the target. -/
theorem curryGlobalMap_comp (F G H H' : _root_.PresheafOfModules.{w} (Oforget O))
    (b : F ⊗ G ⟶ H) (h : H ⟶ H') (U : C) (x : F.obj (op U)) :
    AnyUniverse.curryGlobalMap O F G H' (b ≫ h) U x =
      AnyUniverse.curryGlobalMap O F G H b U x ≫ (restrFun O U).map h :=
  rfl

end Stacks.PresheafOfModules.InternalHom

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w}) [EssentiallySmall.{w} X.C]

section Currying

variable (Z L K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- A section of `internalHomSheafSmall X L K` over `U`, read as a section of the internal Hom
presheaf, that is, as a morphism `L|_U ⟶ K|_U`: the `O(U)`-linear equivalence `Shrink.linearEquiv`
undoing the descent to the module universe. -/
def internalHomSheafSmallSectionEquiv (U : X.C) :
    (valOf X (internalHomSheafSmall X L K)).obj (op U) ≃ₗ[X.O.obj.obj (op U)]
      (internalHom X.O.obj (valOf X L) (valOf X K)).obj (op U) :=
  haveI : Small.{w} ((internalHom X.O.obj (valOf X L) (valOf X K)).obj (op U)) :=
    small_internalHomSheaf_obj X L K (op U)
  Shrink.linearEquiv.{w} (X.O.obj.obj (op U))
    ((internalHom X.O.obj (valOf X L) (valOf X K)).obj (op U))

/-- `internalHomSheafSmallSectionEquiv` commutes with restriction. -/
theorem internalHomSheafSmallSectionEquiv_restrict {U U' : X.C} (k : U' ⟶ U)
    (s : (valOf X (internalHomSheafSmall X L K)).obj (op U)) :
    internalHomSheafSmallSectionEquiv X L K U'
        ((valOf X (internalHomSheafSmall X L K)).restrictₛₗ k.op s) =
      homRestr X.O.obj (valOf X L) (valOf X K) k (internalHomSheafSmallSectionEquiv X L K U s) := by
  have := small_internalHomSheaf_obj X L K
  exact Stacks.shrinkPresheaf_map_apply.{w, max u v} (internalHomSheaf X L K).val.presheaf k.op s

/-- Currying into the small internal Hom, on sections over `U`: `x ↦ (y ↦ b (x|_· ⊗ y))`. -/
def internalHomSheafSmallCurryApp (b : valOf X Z ⊗ valOf X L ⟶ valOf X K) (U : X.C) :
    (valOf X Z).obj (op U) →ₗ[X.O.obj.obj (op U)]
      (valOf X (internalHomSheafSmall X L K)).obj (op U) :=
  (internalHomSheafSmallSectionEquiv X L K U).symm.toLinearMap ∘ₗ
    AnyUniverse.curryGlobalMap X.O.obj (valOf X Z) (valOf X L) (valOf X K) b U

/-- `internalHomSheafSmallCurryApp` commutes with restriction. -/
theorem internalHomSheafSmallCurryApp_restrict (b : valOf X Z ⊗ valOf X L ⟶ valOf X K) {U U' : X.C}
    (k : U' ⟶ U) (x : (valOf X Z).obj (op U)) :
    internalHomSheafSmallCurryApp X Z L K b U' ((valOf X Z).restrictₛₗ k.op x) =
      (valOf X (internalHomSheafSmall X L K)).restrictₛₗ k.op
        (internalHomSheafSmallCurryApp X Z L K b U x) := by
  apply (internalHomSheafSmallSectionEquiv X L K U').injective
  rw [internalHomSheafSmallSectionEquiv_restrict]
  simp only [internalHomSheafSmallCurryApp, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, LinearEquiv.apply_symm_apply]
  exact AnyUniverse.curryGlobalMap_restrict X.O.obj (valOf X Z) (valOf X L) (valOf X K) b k x

/-- **Currying**: a morphism `Z ⊗ L ⟶ K` of presheaves of modules becomes a morphism
`Z ⟶ Hom(L, K)` into the small internal Hom. -/
def internalHomSheafSmallCurry (b : valOf X Z ⊗ valOf X L ⟶ valOf X K) :
    Z ⟶ internalHomSheafSmall X L K :=
  ⟨PresheafOfModules.Hom.mk
    (fun U ↦ AnyUniverse.ofGlobalHom X.O.obj (valOf X Z) (valOf X (internalHomSheafSmall X L K)) U
      (internalHomSheafSmallCurryApp X Z L K b U.unop))
    (fun {U V} f ↦ by
      ext x
      exact internalHomSheafSmallCurryApp_restrict X Z L K b f.unop x)⟩

/-- A morphism into the small internal Hom, on sections over `W`, as an `O(W)`-linear map. -/
def internalHomSheafSmallApplyLinear (a : Z ⟶ internalHomSheafSmall X L K) (W : X.C) :
    (valOf X Z).obj (op W) →ₗ[X.O.obj.obj (op W)]
      (valOf X (internalHomSheafSmall X L K)).obj (op W) :=
  (a.val.app (op W)).hom

/-- Uncurrying, on sections over `W`: `x ⊗ y ↦ a(x)(y)`, the value of `a(x) : L|_W ⟶ K|_W` at the
identity of the slice. -/
def internalHomSheafSmallUncurryApp (a : Z ⟶ internalHomSheafSmall X L K) (W : X.C) :
    TensorProduct (X.O.obj.obj (op W)) ((valOf X Z).obj (op W)) ((valOf X L).obj (op W))
      →ₗ[X.O.obj.obj (op W)] (valOf X K).obj (op W) :=
  TensorProduct.lift ((AnyUniverse.evalAtIdLinear X.O.obj (valOf X L) (valOf X K) W).comp
    ((internalHomSheafSmallSectionEquiv X L K W).toLinearMap.comp
      (internalHomSheafSmallApplyLinear X Z L K a W)))

/-- `internalHomSheafSmallUncurryApp` on a pure tensor. -/
theorem internalHomSheafSmallUncurryApp_tmul (a : Z ⟶ internalHomSheafSmall X L K) (W : X.C)
    (x : (valOf X Z).obj (op W)) (y : (valOf X L).obj (op W)) :
    internalHomSheafSmallUncurryApp X Z L K a W (x ⊗ₜ y) =
      AnyUniverse.sectionOfRestr X.O.obj (valOf X K) W (𝟙 W)
        (((internalHomSheafSmallSectionEquiv X L K W
          (internalHomSheafSmallApplyLinear X Z L K a W x)).app (op (Over.mk (𝟙 W)))).hom
          (AnyUniverse.restrSection X.O.obj (valOf X L) W (𝟙 W) y)) := rfl

/-- Naturality of a morphism into the small internal Hom, read in the internal Hom presheaf. -/
theorem internalHomSheafSmallApplyLinear_restrict (a : Z ⟶ internalHomSheafSmall X L K)
    {S S' : X.C} (k : S' ⟶ S) (x : (valOf X Z).obj (op S)) :
    internalHomSheafSmallSectionEquiv X L K S'
        (internalHomSheafSmallApplyLinear X Z L K a S' ((valOf X Z).restrictₛₗ k.op x)) =
      homRestr X.O.obj (valOf X L) (valOf X K) k
        (internalHomSheafSmallSectionEquiv X L K S
          (internalHomSheafSmallApplyLinear X Z L K a S x)) :=
  (congrArg (internalHomSheafSmallSectionEquiv X L K S')
    (PresheafOfModules.naturality_apply a.val k.op x)).trans
    (internalHomSheafSmallSectionEquiv_restrict X L K k _)

/-- `internalHomSheafSmallUncurryApp` on a restricted section tensored with `y`, read at the slice
`k`. -/
private theorem internalHomSheafSmallUncurryApp_restrict_tmul (a : Z ⟶ internalHomSheafSmall X L K)
    {S S' : X.C} (k : S' ⟶ S) (x : (valOf X Z).obj (op S)) (y : (valOf X L).obj (op S')) :
    internalHomSheafSmallUncurryApp X Z L K a S' ((valOf X Z).restrictₛₗ k.op x ⊗ₜ y) =
      AnyUniverse.sectionOfRestr X.O.obj (valOf X K) S k
        (((internalHomSheafSmallSectionEquiv X L K S
          (internalHomSheafSmallApplyLinear X Z L K a S x)).app (op (Over.mk k))).hom
            (AnyUniverse.restrSection X.O.obj (valOf X L) S k y)) := by
  have hb := internalHomSheafSmallApplyLinear_restrict X Z L K a k x
  have hr := AnyUniverse.homRestr_section X.O.obj (valOf X L) (valOf X K) k
    (internalHomSheafSmallSectionEquiv X L K S (internalHomSheafSmallApplyLinear X Z L K a S x))
    (𝟙 S') y
  rw [Category.id_comp] at hr
  rw [internalHomSheafSmallUncurryApp_tmul, hb]
  exact hr

/-- `internalHomSheafSmallUncurryApp` commutes with restriction. -/
theorem internalHomSheafSmallUncurryApp_restrict (a : Z ⟶ internalHomSheafSmall X L K) {S S' : X.C}
    (k : S' ⟶ S) (x : (valOf X Z).obj (op S)) (y : (valOf X L).obj (op S)) :
    internalHomSheafSmallUncurryApp X Z L K a S'
        ((valOf X Z).restrictₛₗ k.op x ⊗ₜ (valOf X L).restrictₛₗ k.op y) =
      (valOf X K).restrictₛₗ k.op (internalHomSheafSmallUncurryApp X Z L K a S (x ⊗ₜ y)) := by
  have hα := AnyUniverse.restrMorphism_nat X.O.obj (valOf X L) (valOf X K)
    (internalHomSheafSmallSectionEquiv X L K S (internalHomSheafSmallApplyLinear X Z L K a S x))
    (𝟙 S) k y
  rw [Category.comp_id] at hα
  rw [internalHomSheafSmallUncurryApp_restrict_tmul, internalHomSheafSmallUncurryApp_tmul]
  exact hα

/-- **Uncurrying**, inverse to `internalHomSheafSmallCurry`. -/
def internalHomSheafSmallUncurry (a : Z ⟶ internalHomSheafSmall X L K) :
    valOf X Z ⊗ valOf X L ⟶ valOf X K :=
  PresheafOfModules.Hom.mk
    (fun W ↦ AnyUniverse.ofGlobalTensorHom X.O.obj (valOf X Z) (valOf X L) (valOf X K) W
      (internalHomSheafSmallUncurryApp X Z L K a W.unop))
    (fun {W W'} f ↦ by
      refine AnyUniverse.globalTensor_hom_ext X.O.obj (valOf X Z) (valOf X L) ?_
      intro x y
      exact internalHomSheafSmallUncurryApp_restrict X Z L K a f.unop x y)

/-- The sections of a curried morphism, read in the internal Hom presheaf, are those of
`Stacks.PresheafOfModules.InternalHom.AnyUniverse.curryGlobalMap`. -/
theorem internalHomSheafSmallSectionEquiv_curry
    (b : valOf X Z ⊗ valOf X L ⟶ valOf X K) (U : X.C) (x : (valOf X Z).obj (op U)) :
    internalHomSheafSmallSectionEquiv X L K U
        (internalHomSheafSmallApplyLinear X Z L K (internalHomSheafSmallCurry X Z L K b) U x) =
      AnyUniverse.curryGlobalMap X.O.obj (valOf X Z) (valOf X L) (valOf X K) b U x :=
  (internalHomSheafSmallSectionEquiv X L K U).apply_symm_apply _

/-- Uncurrying undoes currying. -/
theorem internalHomSheafSmallUncurry_curry (b : valOf X Z ⊗ valOf X L ⟶ valOf X K) :
    internalHomSheafSmallUncurry X Z L K (internalHomSheafSmallCurry X Z L K b) = b := by
  apply PresheafOfModules.hom_ext
  intro W
  refine AnyUniverse.globalTensor_hom_ext X.O.obj (valOf X Z) (valOf X L) ?_
  intro x y
  show internalHomSheafSmallUncurryApp X Z L K (internalHomSheafSmallCurry X Z L K b) W.unop
      (x ⊗ₜ y) =
    AnyUniverse.globalTensorHom X.O.obj (valOf X Z) (valOf X L) (valOf X K) b W.unop (x ⊗ₜ y)
  rw [internalHomSheafSmallUncurryApp_tmul, internalHomSheafSmallSectionEquiv_curry,
    AnyUniverse.curryGlobalMap_apply, op_id, AnyUniverse.restrictₛₗ_id]

/-- Currying an uncurried morphism recovers its values on sections. -/
theorem internalHomSheafSmallCurry_uncurry_app (a : Z ⟶ internalHomSheafSmall X L K) (S : X.C)
    (x : (valOf X Z).obj (op S)) {T : X.C} (q : T ⟶ S) (y : (valOf X L).obj (op T)) :
    AnyUniverse.sectionOfRestr X.O.obj (valOf X K) S q
        (((internalHomSheafSmallSectionEquiv X L K S (internalHomSheafSmallApplyLinear X Z L K
          (internalHomSheafSmallCurry X Z L K (internalHomSheafSmallUncurry X Z L K a)) S x)).app
            (op (Over.mk q))).hom
            (AnyUniverse.restrSection X.O.obj (valOf X L) S q y)) =
      AnyUniverse.sectionOfRestr X.O.obj (valOf X K) S q
        (((internalHomSheafSmallSectionEquiv X L K S
          (internalHomSheafSmallApplyLinear X Z L K a S x)).app (op (Over.mk q))).hom
            (AnyUniverse.restrSection X.O.obj (valOf X L) S q y)) := by
  rw [internalHomSheafSmallSectionEquiv_curry, AnyUniverse.curryGlobalMap_apply]
  exact internalHomSheafSmallUncurryApp_restrict_tmul X Z L K a q x y

/-- Currying undoes uncurrying. -/
theorem internalHomSheafSmallCurry_uncurry (a : Z ⟶ internalHomSheafSmall X L K) :
    internalHomSheafSmallCurry X Z L K (internalHomSheafSmallUncurry X Z L K a) = a := by
  ext U x
  apply (internalHomSheafSmallSectionEquiv X L K U.unop).injective
  refine PresheafOfModules.hom_ext fun W ↦ ?_
  ext y
  exact internalHomSheafSmallCurry_uncurry_app X Z L K a U.unop x W.unop.hom y

/-- **The tensor–Hom correspondence for the small internal Hom**:
`Hom(Z ⊗ L, K) ≃ Hom(Z, Hom(L, K))`, with `Z ⊗ L` the presheaf tensor product. -/
def internalHomSheafSmallTensorHomEquiv :
    (valOf X Z ⊗ valOf X L ⟶ valOf X K) ≃ (Z ⟶ internalHomSheafSmall X L K) where
  toFun := internalHomSheafSmallCurry X Z L K
  invFun := internalHomSheafSmallUncurry X Z L K
  left_inv := internalHomSheafSmallUncurry_curry X Z L K
  right_inv := internalHomSheafSmallCurry_uncurry X Z L K

/-- The functoriality of `internalHomSheafSmallFunctor` in the second variable is postcomposition,
read in the internal Hom presheaf. -/
theorem internalHomSheafSmallSectionEquiv_map
    {K' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (h : K ⟶ K') (U : X.C)
    (s : (valOf X (internalHomSheafSmall X L K)).obj (op U)) :
    internalHomSheafSmallSectionEquiv X L K' U
        ((((internalHomSheafSmallFunctor X L).map h).val.app (op U)).hom s) =
      internalHomSheafSmallSectionEquiv X L K U s ≫ (restrFun X.O.obj U).map (homOf X h) := by
  apply (internalHomSheafSmallSectionEquiv X L K' U).symm.injective
  refine (LinearEquiv.symm_apply_apply _ _).trans ?_
  exact congrArg ULift.down (congrArg (fun φ ↦ (φ.val.app (op U)).hom (ULift.up s))
    (moduleULift_map_internalHomSheafSmallFunctor_map X L h))

/-- Currying is natural in the target. -/
theorem internalHomSheafSmallCurry_comp (b : valOf X Z ⊗ valOf X L ⟶ valOf X K)
    {K' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (h : K ⟶ K') :
    internalHomSheafSmallCurry X Z L K' (b ≫ homOf X h) =
      internalHomSheafSmallCurry X Z L K b ≫ (internalHomSheafSmallFunctor X L).map h := by
  ext U x
  apply (internalHomSheafSmallSectionEquiv X L K' U.unop).injective
  refine (internalHomSheafSmallSectionEquiv_curry X Z L K' (b ≫ homOf X h) U.unop x).trans ?_
  refine Eq.trans ?_ (internalHomSheafSmallSectionEquiv_map X L K h U.unop _).symm
  refine (curryGlobalMap_comp X.O.obj (valOf X Z) (valOf X L) (valOf X K) (valOf X K') b
    (homOf X h) U.unop x).trans ?_
  exact congrArg (· ≫ (restrFun X.O.obj U.unop).map (homOf X h))
    (internalHomSheafSmallSectionEquiv_curry X Z L K b U.unop x).symm

/-- Uncurrying is natural in the first tensor factor. -/
theorem internalHomSheafSmallUncurry_comp
    {Z' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f : Z' ⟶ Z)
    (a : Z ⟶ internalHomSheafSmall X L K) :
    internalHomSheafSmallUncurry X Z' L K (f ≫ a) =
      (homOf X f ▷ valOf X L) ≫ internalHomSheafSmallUncurry X Z L K a := by
  apply PresheafOfModules.hom_ext
  intro W
  refine AnyUniverse.globalTensor_hom_ext X.O.obj (valOf X Z') (valOf X L) ?_
  intro x y
  rfl

end Currying

section Adjunction

variable [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks 03EO for the small internal Hom.** On an essentially `w`-small ringed site, tensoring
on the right by `L` is left adjoint to `internalHomSheafSmallFunctor X L`, the internal Hom out of
`L` in the module universe `w`. The hom-equivalence is the sheafification adjunction followed by
`internalHomSheafSmallTensorHomEquiv`. -/
def internalHomSheafSmallAdjunction
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj L ⊣ internalHomSheafSmallFunctor X L :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun Z K ↦
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).homEquiv
          ((valOf X Z ⊗ valOf X L : PresheafOfModules (Oforget X.O.obj))) K).trans
          (internalHomSheafSmallTensorHomEquiv X Z L K)
      homEquiv_naturality_left_symm := by
        intro Z₁ Z₂ K f g
        exact (congrArg ((PresheafOfModules.sheafificationAdjunction
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).homEquiv
            ((valOf X Z₁ ⊗ valOf X L : PresheafOfModules (Oforget X.O.obj))) K).symm
            (internalHomSheafSmallUncurry_comp X Z₂ L K f g)).trans
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).homEquiv_naturality_left_symm
            (homOf X f ▷ valOf X L) (internalHomSheafSmallUncurry X Z₂ L K g))
      homEquiv_naturality_right := by
        intro Z K K' b h
        exact (congrArg (internalHomSheafSmallCurry X Z L K')
            ((PresheafOfModules.sheafificationAdjunction
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).homEquiv_naturality_right
              b h)).trans (internalHomSheafSmallCurry_comp X Z L K _ h) }

/-- **The counit on sheafified pure tensors** is evaluation: `φ ⊗ l ↦ φ(l)`, the value at the
identity of the slice of the morphism `L|_U ⟶ K|_U` underlying `φ`. -/
theorem internalHomSheafSmallAdjunction_counit_app_val_app
    (L K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (φ : (valOf X (internalHomSheafSmall X L K)).obj (op U)) (l : (valOf X L).obj (op U)) :
    (((internalHomSheafSmallAdjunction X L).counit.app K).val.app (op U)).hom
        ((((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          ((valOf X (internalHomSheafSmall X L K) ⊗ valOf X L :
            PresheafOfModules (Oforget X.O.obj)))).app (op U)).hom (φ ⊗ₜ l)) =
      AnyUniverse.sectionOfRestr X.O.obj (valOf X K) U (𝟙 U)
        (((internalHomSheafSmallSectionEquiv X L K U φ).app (op (Over.mk (𝟙 U)))).hom
          (AnyUniverse.restrSection X.O.obj (valOf X L) U (𝟙 U) l)) := by
  have h := ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).homEquiv_unit
    (f := ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).homEquiv
      ((valOf X (internalHomSheafSmall X L K) ⊗ valOf X L : PresheafOfModules (Oforget X.O.obj)))
        K).symm
          (internalHomSheafSmallUncurry X (internalHomSheafSmall X L K) L K (𝟙 _)))).symm.trans
    (Equiv.apply_symm_apply _ _)
  exact congrArg (fun c ↦ (c.app (op U)).hom (φ ⊗ₜ l)) h

/-- **The hom-equivalence on sections** is currying: `g` goes to `z ↦ (y ↦ g(z|_T ⊗ y))`. -/
theorem internalHomSheafSmallAdjunction_homEquiv_app
    (Z L K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (g : ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj L).obj Z ⟶ K)
    (U : X.C) (z : (valOf X Z).obj (op U)) {T : X.C} (q : T ⟶ U) (y : (valOf X L).obj (op T)) :
    AnyUniverse.sectionOfRestr X.O.obj (valOf X K) U q
        (((internalHomSheafSmallSectionEquiv X L K U (internalHomSheafSmallApplyLinear X Z L K
          ((internalHomSheafSmallAdjunction X L).homEquiv Z K g) U z)).app (op (Over.mk q))).hom
            (AnyUniverse.restrSection X.O.obj (valOf X L) U q y)) =
      (g.val.app (op T)).hom
        ((((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          ((valOf X Z ⊗ valOf X L : PresheafOfModules (Oforget X.O.obj)))).app (op T)).hom
            ((valOf X Z).restrictₛₗ q.op z ⊗ₜ y)) := by
  have h0 : (internalHomSheafSmallAdjunction X L).homEquiv Z K g =
      internalHomSheafSmallCurry X Z L K
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).homEquiv
        ((valOf X Z ⊗ valOf X L : PresheafOfModules (Oforget X.O.obj))) K g) := by
    unfold internalHomSheafSmallAdjunction
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    rfl
  have h1 := (PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).homEquiv_unit
    (X := (valOf X Z ⊗ valOf X L : PresheafOfModules (Oforget X.O.obj))) (Y := K) (f := g)
  refine (congrArg (fun α ↦ AnyUniverse.sectionOfRestr X.O.obj (valOf X K) U q
    (((internalHomSheafSmallSectionEquiv X L K U
      (internalHomSheafSmallApplyLinear X Z L K α U z)).app
      (op (Over.mk q))).hom (AnyUniverse.restrSection X.O.obj (valOf X L) U q y))) h0).trans ?_
  refine (congrArg (fun α ↦ AnyUniverse.sectionOfRestr X.O.obj (valOf X K) U q
    ((α.app (op (Over.mk q))).hom (AnyUniverse.restrSection X.O.obj (valOf X L) U q y)))
      (internalHomSheafSmallSectionEquiv_curry X Z L K
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).homEquiv
          ((valOf X Z ⊗ valOf X L : PresheafOfModules (Oforget X.O.obj))) K g) U z)).trans ?_
  refine (AnyUniverse.curryGlobalMap_apply X.O.obj (valOf X Z) (valOf X L) (valOf X K) _ U z q
    y).trans ?_
  exact congrArg (fun c ↦ (c.app (op T)).hom ((valOf X Z).restrictₛₗ q.op z ⊗ₜ y)) h1

/-- **The small internal Hom as a bifunctor**, contravariant in the source: its value at `L` is
`internalHomSheafSmallFunctor X L`, and its action on morphisms is the conjugate, under the
adjunctions `internalHomSheafSmallAdjunction`, of the action of the tensor product. -/
def internalHomSheafSmallBifunctor :
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))ᵒᵖ ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
        SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) where
  obj L := internalHomSheafSmallFunctor X L.unop
  map {L L'} f := conjugateEquiv (internalHomSheafSmallAdjunction X L.unop)
    (internalHomSheafSmallAdjunction X L'.unop)
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} X.O).flip.map f.unop)
  map_id L := (congrArg (conjugateEquiv (internalHomSheafSmallAdjunction X L.unop)
      (internalHomSheafSmallAdjunction X L.unop))
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} X.O).flip.map_id L.unop)).trans
    (conjugateEquiv_id _)
  map_comp f g := (congrArg (conjugateEquiv _ _)
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} X.O).flip.map_comp
        g.unop f.unop)).trans
    (conjugateEquiv_comp _ _ _ _ _).symm

end Adjunction

end AlgebraicGeometry.RingedSite

end
