module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsBetweenCategories.RegularAction
public import StacksCore.Tactic.StacksAttribute

/-!
# Functors between module categories which are tensor products

A functor between categories of modules is tensoring with a bimodule exactly when it is right
exact and preserves arbitrary direct sums. Equivalently, it preserves all colimits, or it has a
right adjoint.

## Main definitions

* `ModuleCat.tensorFunctorOverInt` is the functor from `A`-modules to `B`-modules obtained by
  tensoring with a module over `A ⊗[ℤ] B`.

## Main results

* `ModuleCat.tfae_iso_tensorFunctor_preserves_colimits_isLeftAdjoint` gives the four equivalent
  characterizations of such a functor.

## Implementation notes

The tensor functor is extension of scalars from `A` to `A ⊗[ℤ] B`, tensoring there with the
bimodule, and restriction of scalars to `B`. Right exactness is expressed categorically as
preservation of finite colimits, and preservation of arbitrary direct sums as preservation of
colimits of discrete diagrams.

Because `ℤ` lives in `Type 0` while `A` and `B` may live in any universe, this is not an
instance of `ModuleCat.tensorFunctor`, whose base ring is constrained to the universe of `A`
and `B`; the two definitions have the same body and are kept separate for that reason.

The bimodule realizing a colimit-preserving functor `F` is `F` applied to the rank-one free
module, with the left action of `A` by `ModuleCat.imageAction` and the right action of `B`
already present; `ModuleCat.isoOfRegularAction` then identifies `F` with tensoring by it.

## References

* [Stacks Project, Tag 0GNS](https://stacks.math.columbia.edu/tag/0GNS)
-/

@[expose] public section

namespace ModuleCat

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct MonoidalCategory

variable (A B : Type u) [CommRing A] [CommRing B]

/-- Tensoring with an `A ⊗[ℤ] B`-module, regarded as a functor from `A`-modules to
`B`-modules. -/
public noncomputable def tensorFunctorOverInt
    (K : ModuleCat.{u} (A ⊗[ℤ] B)) :
    ModuleCat.{u} A ⥤ ModuleCat.{u} B :=
  ModuleCat.extendScalars
      (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := B)) ⋙
    (MonoidalCategory.tensoringRight
      (ModuleCat.{u} (A ⊗[ℤ] B))).obj K ⋙
    ModuleCat.restrictScalars
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := B)).toRingHom

private lemma tensorFunctorOverInt_isLeftAdjoint
    (K : ModuleCat.{u} (A ⊗[ℤ] B)) :
    (tensorFunctorOverInt A B K).IsLeftAdjoint := by
  unfold tensorFunctorOverInt
  infer_instance

private noncomputable abbrev imageTensorModule
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B)
    [PreservesFiniteColimits F] (M : ModuleCat.{u} A) :
    ModuleCat.{u} (A ⊗[ℤ] B) := by
  let K := F.obj M
  letI : Module A K := Module.compHom K (imageAction A B F M)
  letI : SMulCommClass A B K := ⟨fun a b x => by
    change (imageAction A B F M a) (b • x) = b • (imageAction A B F M a) x
    exact map_smul (imageAction A B F M a) b x⟩
  letI : Module (A ⊗[ℤ] B) K := TensorProduct.Algebra.module
  exact ModuleCat.of (A ⊗[ℤ] B) K

private lemma imageTensorModule_smul (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B)
    [PreservesFiniteColimits F] (M : ModuleCat.{u} A) (a : A) (b : B) (x : F.obj M) :
    (imageTensorModule A B F M).isModule.smul (a ⊗ₜ[ℤ] b) x =
      b • (F.map (scalarMul A M a)) x := by
  dsimp [imageTensorModule]
  change (imageAction A B F M a) (b • x) = b • (F.map (scalarMul A M a)) x
  exact map_smul (imageAction A B F M a) b x

private noncomputable def imageTensorMap (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B)
    [PreservesFiniteColimits F] {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    imageTensorModule A B F M ⟶ imageTensorModule A B F N := by
  refine ConcreteCategory.ofHom (C := ModuleCat (A ⊗[ℤ] B)) {
    toFun := fun x => F.map f x
    map_add' := fun x y => (F.map f).hom.map_add x y
    map_smul' := by
      intro c x
      dsimp [imageTensorModule] at x ⊢
      let : Module (A ⊗[ℤ] B) (F.obj M) := (imageTensorModule A B F M).isModule
      let : Module (A ⊗[ℤ] B) (F.obj N) := (imageTensorModule A B F N).isModule
      induction c using TensorProduct.inductionOn with
      | tmul a b =>
        change F.map f ((imageTensorModule A B F M).isModule.smul (a ⊗ₜ[ℤ] b) x) =
          (imageTensorModule A B F N).isModule.smul (a ⊗ₜ[ℤ] b) (F.map f x)
        rw [imageTensorModule_smul, imageTensorModule_smul, map_smul]
        congr 1
        simpa only [F.map_comp, ModuleCat.comp_apply] using
          congrArg (fun g => g x) (congrArg F.map (scalarMul_natural A f a))
      | add c d hc hd =>
        simpa [add_smul, map_add] using congrArg₂ (· + ·) hc hd }

private noncomputable def imageTensorFunctor
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [PreservesFiniteColimits F] :
    ModuleCat.{u} A ⥤ ModuleCat.{u} (A ⊗[ℤ] B) where
  obj M := imageTensorModule A B F M
  map f := imageTensorMap A B F f
  map_id M := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change F.map (𝟙 M) x = x
    simp
  map_comp f g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change F.map (f ≫ g) x = F.map g (F.map f x)
    rw [F.map_comp]
    rfl

private lemma imageTensorModule_restrict_smul
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [PreservesFiniteColimits F]
    (M : ModuleCat.{u} A) (b : B) (x : F.obj M) :
    (((imageTensorFunctor A B F ⋙
        ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight
            (R := ℤ) (A := A) (B := B)).toRingHom).obj M).isModule).smul
      b x = b • x := by
  change (imageTensorModule A B F M).isModule.smul
    ((Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := B)) b) x = b • x
  rw [Algebra.TensorProduct.includeRight_apply, imageTensorModule_smul]
  simp [scalarMul_one]

private noncomputable def imageTensorRestrictEquiv
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [PreservesFiniteColimits F]
    (M : ModuleCat.{u} A) :
    (imageTensorFunctor A B F ⋙
      ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := B)).toRingHom).obj M
      ≃ₗ[B] F.obj M where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun b x => imageTensorModule_restrict_smul A B F M b x

private noncomputable def imageTensorRestrictIso
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [PreservesFiniteColimits F] :
    imageTensorFunctor A B F ⋙
      ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := B)).toRingHom ≅ F :=
  NatIso.ofComponents (fun M => LinearEquiv.toModuleIso (imageTensorRestrictEquiv A B F M))
    fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

private noncomputable def extendScalarsRegularIso :
    (ModuleCat.extendScalars
      (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := B))).obj
        (ModuleCat.of A A) ≅
      (𝟙_ (ModuleCat.{u} (A ⊗[ℤ] B))) := by
  letI : Algebra A (A ⊗[ℤ] B) :=
    (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := B)).toAlgebra
  letI : Module A (A ⊗[ℤ] B) :=
    (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := B)).toModule
  exact LinearEquiv.toModuleIso
    (TensorProduct.AlgebraTensorModule.rid A (A ⊗[ℤ] B) (A ⊗[ℤ] B))

private noncomputable def tensorFunctorRegularIso
    (K : ModuleCat.{u} (A ⊗[ℤ] B)) :
    (tensorFunctorOverInt A B K).obj (ModuleCat.of A A) ≅
      (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := B)).toRingHom).obj K :=
  (ModuleCat.restrictScalars
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := B)).toRingHom).mapIso
    (((MonoidalCategory.tensoringRight (ModuleCat.{u} (A ⊗[ℤ] B))).obj K).mapIso
        (extendScalarsRegularIso A B) ≪≫
      MonoidalCategory.leftUnitor K)

private noncomputable def tensorFunctorRegularImageIso
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [PreservesFiniteColimits F] :
    (tensorFunctorOverInt A B (imageTensorModule A B F (ModuleCat.of A A))).obj
      (ModuleCat.of A A) ≅ F.obj (ModuleCat.of A A) :=
  tensorFunctorRegularIso A B (imageTensorModule A B F (ModuleCat.of A A)) ≪≫
    (imageTensorRestrictIso A B F).app (ModuleCat.of A A)

private lemma tensorFunctorRegularImageIso_hom_tmul
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [PreservesFiniteColimits F]
    (t : A ⊗[ℤ] B) (z : A)
    (k : imageTensorModule A B F (ModuleCat.of A A)) :
    (tensorFunctorRegularImageIso A B F).hom
        ((t ⊗ₜ[A] z) ⊗ₜ[A ⊗[ℤ] B] k) =
      (imageTensorModule A B F (ModuleCat.of A A)).isModule.smul
        ((Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := B)) z * t) k := by
  rfl

private lemma imageTensorModule_includeLeft_smul
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [PreservesFiniteColimits F]
    (a : A) (k : imageTensorModule A B F (ModuleCat.of A A)) :
    (imageTensorModule A B F (ModuleCat.of A A)).isModule.smul
      ((Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := B)) a) k =
        F.map (regularMul A a) k := by
  change (imageTensorModule A B F (ModuleCat.of A A)).isModule.smul
    (a ⊗ₜ[ℤ] (1 : B)) k = F.map (regularMul A a) k
  rw [imageTensorModule_smul]
  simp [regularMul_eq_scalarMul]

private lemma tensorFunctorRegularImageIso_natural
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [PreservesColimits F] (a : A) :
    (tensorFunctorOverInt A B (imageTensorModule A B F (ModuleCat.of A A))).map
        (regularMul A a) ≫ (tensorFunctorRegularImageIso A B F).hom =
      (tensorFunctorRegularImageIso A B F).hom ≫ F.map (regularMul A a) := by
  apply ModuleCat.hom_ext
  let T := tensorFunctorOverInt A B (imageTensorModule A B F (ModuleCat.of A A))
  let e := tensorFunctorRegularImageIso A B F
  let L : T.obj (ModuleCat.of A A) →ₗ[B] F.obj (ModuleCat.of A A) :=
    (T.map (regularMul A a) ≫ e.hom).hom
  let R : T.obj (ModuleCat.of A A) →ₗ[B] F.obj (ModuleCat.of A A) :=
    (e.hom ≫ F.map (regularMul A a)).hom
  change L = R
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul s k =>
    induction s using TensorProduct.inductionOn with
    | tmul t z =>
      change A ⊗[ℤ] B at t
      change A at z
      change (tensorFunctorRegularImageIso A B F).hom
          ((t ⊗ₜ[A] (a * z)) ⊗ₜ[A ⊗[ℤ] B] k) =
        F.map (regularMul A a)
          ((tensorFunctorRegularImageIso A B F).hom
            ((t ⊗ₜ[A] z) ⊗ₜ[A ⊗[ℤ] B] k))
      rw [tensorFunctorRegularImageIso_hom_tmul, tensorFunctorRegularImageIso_hom_tmul]
      let iL := Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := B)
      change (iL (a * z) * t) • k = (imageTensorMap A B F (regularMul A a)) ((iL z * t) • k)
      calc
        (iL (a * z) * t) • k = (iL z * t) • (iL a • k) := by
          rw [← mul_smul, map_mul]
          congr 1
          ring
        _ = (iL z * t) • (imageTensorMap A B F (regularMul A a) k) :=
          congrArg (fun v => (iL z * t) • v) (imageTensorModule_includeLeft_smul A B F a k)
        _ = (imageTensorMap A B F (regularMul A a)) ((iL z * t) • k) :=
          ((imageTensorMap A B F (regularMul A a)).hom.map_smul (iL z * t) k).symm
    | add s t hs ht =>
      let E := (ModuleCat.extendScalars
        (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := B))).obj
          (ModuleCat.of A A)
      let : Module (A ⊗[ℤ] B)
          (((ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := B))).obj
              (ModuleCat.of (A ⊗[ℤ] B) (A ⊗[ℤ] B))) ⊗[A] (ModuleCat.of A A)) :=
        E.isModule
      have hadd : (((s : E) + (t : E)) ⊗ₜ[A ⊗[ℤ] B] k : T.obj (ModuleCat.of A A)) =
          ((s : E) ⊗ₜ[A ⊗[ℤ] B] k : T.obj (ModuleCat.of A A)) +
            ((t : E) ⊗ₜ[A ⊗[ℤ] B] k : T.obj (ModuleCat.of A A)) :=
        TensorProduct.add_tmul (s : E) (t : E) k
      calc
        L ((s + t) ⊗ₜ[A ⊗[ℤ] B] k) =
            L (s ⊗ₜ[A ⊗[ℤ] B] k + t ⊗ₜ[A ⊗[ℤ] B] k) := congrArg L hadd
        _ = L (s ⊗ₜ[A ⊗[ℤ] B] k) + L (t ⊗ₜ[A ⊗[ℤ] B] k) := L.map_add _ _
        _ = R (s ⊗ₜ[A ⊗[ℤ] B] k) + R (t ⊗ₜ[A ⊗[ℤ] B] k) :=
          congrArg₂ (· + ·) hs ht
        _ = R (s ⊗ₜ[A ⊗[ℤ] B] k + t ⊗ₜ[A ⊗[ℤ] B] k) := (R.map_add _ _).symm
        _ = R ((s + t) ⊗ₜ[A ⊗[ℤ] B] k) := congrArg R hadd.symm
  | add x y hx hy =>
    calc
      L (x + y) = L x + L y := L.map_add x y
      _ = R x + R y := congrArg₂ (· + ·) hx hy
      _ = R (x + y) := (R.map_add x y).symm

/-- A functor between module categories is tensoring with a bimodule iff it is right exact and
commutes with arbitrary direct sums; these are also equivalent to preserving all colimits and
to having a right adjoint. -/
@[stacks 0GNS,
  ega "III 7.3.1" "(a) <=> (e)",
  ega "III 7.2.6" "(1) <=> (2)",
  ega "III 7.2.5" "(a) <=> (c)"]
public lemma tfae_iso_tensorFunctor_preserves_colimits_isLeftAdjoint
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) :
    List.TFAE
      [ ∃ K : ModuleCat.{u} (A ⊗[ℤ] B),
          Nonempty (tensorFunctorOverInt A B K ≅ F),
        PreservesFiniteColimits F ∧
          ∀ J : Type u, PreservesColimitsOfShape (Discrete J) F,
        PreservesColimits F,
        F.IsLeftAdjoint ] := by
  tfae_have 1 → 4 := by
    rintro ⟨K, ⟨e⟩⟩
    have := tensorFunctorOverInt_isLeftAdjoint A B K
    exact Functor.isLeftAdjoint_of_iso e
  tfae_have 4 → 3 := by
    intro h
    let := h
    infer_instance
  tfae_have 3 → 2 := by
    intro h
    have := h
    exact ⟨inferInstance, fun _ ↦ inferInstance⟩
  tfae_have 2 → 3 := by
    intro h
    let := h.1
    let (J : Type u) := h.2 J
    exact preservesColimits_of_preservesCoequalizers_and_coproducts F
  tfae_have 3 → 1 := by
    intro h
    let := h
    let : PreservesFiniteColimits F := inferInstance
    let K := imageTensorModule A B F (ModuleCat.of A A)
    refine ⟨K, ⟨?_⟩⟩
    have := tensorFunctorOverInt_isLeftAdjoint A B K
    have : PreservesColimits (tensorFunctorOverInt A B K) := inferInstance
    exact isoOfRegularAction A B (tensorFunctorOverInt A B K) F
      (tensorFunctorRegularImageIso A B F)
      (tensorFunctorRegularImageIso_natural A B F)
  tfae_finish

end ModuleCat
