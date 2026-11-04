module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsBetweenCategories.LinearTensorEquivalence
public import StacksCore.Tactic.StacksAttribute

/-!
# Composing tensor functors between module categories

Let `A`, `B` and `C` be algebras over a commutative ring `R`. If the functors between their
module categories are represented by a module `K` over `A ⊗[R] B` and a module `K'` over
`B ⊗[R] C`, then their composite is represented by `K ⊗[B] K'`.

## Main results

* `ModuleCat.moduleTensorFunctor_comp` constructs the natural `A ⊗[R] C`-module structure on
  `K ⊗[B] K'` and identifies its tensor functor with the composite of the two given ones.

## Implementation notes

The actions of `A`, `B` and `C` on the two modules are obtained by restriction of scalars along
the two inclusions into a tensor product of algebras. The displayed formula on pure tensors
pins down the `A ⊗[R] C`-module structure, and the conclusion is a natural isomorphism of
functors, so it includes naturality in the input `A`-module. Together with
`ModuleCat.tensorFunctorEquivalence_functorIso` this expresses the correspondence under
`ModuleCat.tensorFunctorEquivalence`.

## References

* [Stacks Project, Tag 0GNW](https://stacks.math.columbia.edu/tag/0GNW)
-/

@[expose] public section

namespace ModuleCat

universe u

open CategoryTheory
open scoped ModuleCat.Algebra TensorProduct

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]

private noncomputable def bimoduleTensorMap {A B K X Y : Type u}
    [CommRing A] [CommRing B] [AddCommGroup K] [Module A K] [Module B K]
    [SMulCommClass A B K] [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] (f : X →ₗ[A] Y) :
    K ⊗[A] X →ₗ[B] K ⊗[A] Y where
  toFun := TensorProduct.map LinearMap.id f
  map_add' := (TensorProduct.map LinearMap.id f).map_add
  map_smul' b z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp [hz, hw]
    | tmul k x => simp only [TensorProduct.smul_tmul', TensorProduct.map_tmul,
        LinearMap.id_apply, RingHom.id_apply]

private noncomputable def bimoduleTensorFunctor (A B K : Type u)
    [CommRing A] [CommRing B] [AddCommGroup K] [Module A K] [Module B K]
    [SMulCommClass A B K] : ModuleCat.{u} A ⥤ ModuleCat.{u} B where
  obj X := ModuleCat.of B (K ⊗[A] X)
  map f := ModuleCat.ofHom (bimoduleTensorMap f.hom)
  map_id X := by ext z; simp [bimoduleTensorMap]
  map_comp f g := by
    ext z
    change TensorProduct.map LinearMap.id (g.hom.comp f.hom) z =
      TensorProduct.map LinearMap.id g.hom (TensorProduct.map LinearMap.id f.hom z)
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp [hz, hw]
    | tmul k x => rfl

private noncomputable def scalarTensorIso (A B S : Type u)
    [CommRing A] [CommRing B] [CommRing S] (f : A →+* S) (g : B →+* S)
    (K : ModuleCat.{u} S) [Module A K] [Module B K] [SMulCommClass A B K]
    (hf : ∀ (a : A) (k : K), f a • k = a • k)
    (hg : ∀ (b : B) (k : K), g b • k = b • k) :
    ModuleCat.extendScalars f ⋙
        (MonoidalCategory.tensoringRight (ModuleCat S)).obj K ⋙
        ModuleCat.restrictScalars g ≅ bimoduleTensorFunctor A B K := by
  let : Algebra A S := f.toAlgebra
  let : Algebra B S := g.toAlgebra
  let : IsScalarTower A S K := IsScalarTower.of_algebraMap_smul hf
  let : IsScalarTower B S K := IsScalarTower.of_algebraMap_smul hg
  refine NatIso.ofComponents (fun X => ?_) ?_
  · let e := TensorProduct.comm S (S ⊗[A] X) K ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange A S S K X
    let : Module B ((S ⊗[A] X) ⊗[S] K) := Module.compHom _ (algebraMap B S)
    let : SMul B ((S ⊗[A] X) ⊗[S] K) :=
      (Module.compHom _ (algebraMap B S)).toSMul
    let : IsScalarTower B S ((S ⊗[A] X) ⊗[S] K) :=
      IsScalarTower.of_compHom B S _
    let : LinearMap.CompatibleSMul ((S ⊗[A] X) ⊗[S] K) (K ⊗[A] X) B S :=
      ⟨fun f b z => by rw [← IsScalarTower.algebraMap_smul S b z,
        f.map_smul, IsScalarTower.algebraMap_smul]⟩
    exact (e.restrictScalars B).toModuleIso
  · intro X Y φ
    ext z
    change (TensorProduct.AlgebraTensorModule.cancelBaseChange A S S K Y)
        (TensorProduct.comm S _ _ (TensorProduct.map
          (TensorProduct.AlgebraTensorModule.map (LinearMap.id : S →ₗ[S] S) φ.hom)
          LinearMap.id z)) =
      TensorProduct.map LinearMap.id φ.hom
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange A S S K X)
          (TensorProduct.comm S _ _ z))
    let : Module S (↑((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)) ⊗[A] ↑X) :=
      ((ModuleCat.extendScalars f).obj X).isModule
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | add z w hz hw =>
      refine (congrArg _ (congrArg _ (map_add _ z w))).trans ?_
      refine (congrArg _ (map_add _ _ _)).trans ?_
      refine (map_add _ _ _).trans ?_
      refine (congrArg₂ (· + ·) hz hw).trans ?_
      refine (map_add _ _ _).symm.trans ?_
      refine (congrArg _ (map_add _ _ _).symm).trans ?_
      exact congrArg _ (congrArg _ (map_add _ z w).symm)
    | tmul sx k =>
      induction sx using TensorProduct.induction_on with
      | zero => rfl
      | add sx sy hx hy =>
        have hadd : (sx + sy) ⊗ₜ[S] k = sx ⊗ₜ[S] k + sy ⊗ₜ[S] k :=
          TensorProduct.add_tmul _ _ _
        refine (congrArg _ (congrArg _ (congrArg _ hadd))).trans ?_
        refine (congrArg _ (congrArg _ (map_add _ _ _))).trans ?_
        refine (congrArg _ (map_add _ _ _)).trans ?_
        refine (map_add _ _ _).trans ?_
        refine (congrArg₂ (· + ·) hx hy).trans ?_
        refine (map_add _ _ _).symm.trans ?_
        refine (congrArg _ (map_add _ _ _).symm).trans ?_
        refine (congrArg _ (congrArg _ (map_add _ _ _).symm)).trans ?_
        exact congrArg _ (congrArg _ (congrArg _ hadd.symm))
      | tmul s x => rfl

@[instance_reducible]
private noncomputable def rightTensorAction {B C : Type u} [CommRing B] [CommRing C]
    (M N : Type u) [AddCommGroup M] [Module B M] [AddCommGroup N]
    [Module B N] [Module C N] [SMulCommClass B C N] : Module C (M ⊗[B] N) :=
  (TensorProduct.comm B M N).toAddEquiv.module C

private theorem rightTensorAction_tmul {B C : Type u} [CommRing B] [CommRing C]
    (M N : Type u) [AddCommGroup M] [Module B M] [AddCommGroup N]
    [Module B N] [Module C N] [SMulCommClass B C N] (c : C) (m : M) (n : N) :
    letI : Module C (M ⊗[B] N) := rightTensorAction (B := B) (C := C) M N
    c • (m ⊗ₜ[B] n) = m ⊗ₜ[B] (c • n) := rfl

/-- Two commuting ring homomorphisms into a commutative ring give commuting scalar actions. -/
private theorem smulCommClass_compHom {A B S : Type u} [CommRing A] [CommRing B] [CommRing S]
    (f : A →+* S) (g : B →+* S) (K : Type u) [AddCommGroup K] [Module S K] :
    letI : Module A K := Module.compHom K f
    letI : Module B K := Module.compHom K g
    SMulCommClass A B K := by
  let : Module A K := Module.compHom K f
  let : Module B K := Module.compHom K g
  refine ⟨fun a b k => ?_⟩
  change f a • (g b • k) = g b • (f a • k)
  rw [smul_smul, smul_smul, mul_comm]

/-- Restricting scalars along a ring homomorphism compatible with the `R`-algebra structures
gives an `R`-scalar tower. -/
private theorem isScalarTower_compHom_of_comp {R A S : Type u} [CommRing R] [CommRing A]
    [CommRing S] [Algebra R A] [Algebra R S] (f : A →+* S)
    (hf : ∀ r : R, f (algebraMap R A r) = algebraMap R S r) (K : Type u) [AddCommGroup K]
    [Module S K] :
    letI : Module A K := Module.compHom K f
    letI : Module R K := Module.compHom K (algebraMap R S)
    IsScalarTower R A K := by
  let : Module A K := Module.compHom K f
  let : Module R K := Module.compHom K (algebraMap R S)
  refine IsScalarTower.of_algebraMap_smul fun r k => ?_
  change f (algebraMap R A r) • k = algebraMap R S r • k
  rw [hf]

/-- The `A`- and `C`-actions on `K ⊗[B] K'` (the latter through `K'`) commute. -/
private theorem smulCommClass_rightTensorAction (A B C : Type u) [CommRing A] [CommRing B]
    [CommRing C] (K K' : Type u) [AddCommGroup K] [Module A K] [Module B K] [SMulCommClass B A K]
    [AddCommGroup K'] [Module B K'] [Module C K'] [SMulCommClass B C K'] :
    letI : Module C (K ⊗[B] K') := rightTensorAction (C := C) K K'
    SMulCommClass A C (K ⊗[B] K') := by
  let : Module C (K ⊗[B] K') := rightTensorAction (C := C) K K'
  refine ⟨fun a c z => ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp [hz, hw]
  | tmul k k' => rfl

private noncomputable def bimoduleTensorAssocIso (A B C S : Type u)
    [CommRing A] [CommRing B] [CommRing C] [CommRing S]
    (f : A →+* S) (g : B →+* S) (K : ModuleCat.{u} S)
    (K' : Type u) [AddCommGroup K'] [Module B K'] [Module C K']
    [SMulCommClass B C K'] :
    letI : Module A K := Module.compHom K f
    letI : Module B K := Module.compHom K g
    letI : SMulCommClass A B K := smulCommClass_compHom f g K
    letI : SMulCommClass B A K := SMulCommClass.symm A B K
    letI : Module C (K ⊗[B] K') := rightTensorAction (C := C) K K'
    letI : SMulCommClass A C (K ⊗[B] K') := smulCommClass_rightTensorAction A B C K K'
    bimoduleTensorFunctor A C (K ⊗[B] K') ≅
      bimoduleTensorFunctor A B K ⋙ bimoduleTensorFunctor B C K' := by
  let : Algebra A S := f.toAlgebra
  let : Algebra B S := g.toAlgebra
  let : Module A K := Module.compHom K f
  let : Module B K := Module.compHom K g
  let : IsScalarTower A S K := IsScalarTower.of_compHom A S K
  let : IsScalarTower B S K := IsScalarTower.of_compHom B S K
  let : SMulCommClass A B K := smulCommClass_compHom f g K
  let : SMulCommClass B A K := SMulCommClass.symm A B K
  let : Module C (K ⊗[B] K') := rightTensorAction (C := C) K K'
  let : SMulCommClass A C (K ⊗[B] K') := smulCommClass_rightTensorAction A B C K K'
  refine NatIso.ofComponents (fun X => ?_) ?_
  · let : Module C ((K ⊗[A] X) ⊗[B] K') :=
      rightTensorAction (B := B) (C := C) (K ⊗[A] X) K'
    let e := TensorProduct.AlgebraTensorModule.rightComm A B S K K' X
    let h : ((K ⊗[B] K') ⊗[A] X) →ₗ[C] ((K ⊗[A] X) ⊗[B] K') := {
      toFun := e
      map_add' := e.map_add
      map_smul' := by
        intro c z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | add z w hz hw => simp [hz, hw]
        | tmul q x =>
          induction q using TensorProduct.induction_on with
          | zero => simp
          | add q q' hq hq' =>
            simpa only [smul_add, TensorProduct.add_tmul, map_add] using
              congrArg₂ (· + ·) hq hq'
          | tmul k k' => rfl }
    exact ((LinearEquiv.ofBijective h e.bijective) ≪≫ₗ
      (TensorProduct.comm B (K ⊗[A] X) K').toAddEquiv.linearEquiv C).toModuleIso
  · intro X Y h
    ext z
    change (TensorProduct.comm B _ _)
        ((TensorProduct.AlgebraTensorModule.rightComm A B S K K' Y)
          (TensorProduct.map LinearMap.id h.hom z)) =
      TensorProduct.map LinearMap.id (bimoduleTensorMap h.hom)
        (TensorProduct.comm B _ _
          ((TensorProduct.AlgebraTensorModule.rightComm A B S K K' X) z))
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp [hz, hw]
    | tmul q x =>
      induction q using TensorProduct.induction_on with
      | zero => simp
      | add q q' hq hq' =>
        simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) hq hq'
      | tmul k k' => rfl

/-- The tensor product over the middle algebra represents the composite of two tensor functors. The
equation on pure tensors records the canonical action of `A ⊗[R] C`, and the functor isomorphism
includes naturality in the input `A`-module. -/
@[stacks 0GNW]
public lemma moduleTensorFunctor_comp
    (K : ModuleCat.{u} (A ⊗[R] B)) (K' : ModuleCat.{u} (B ⊗[R] C)) :
    letI : Module A K := Module.compHom K
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B))
    letI : Module B K := Module.compHom K
      (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom
    letI : Module B K' := Module.compHom K'
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := B) (B := C))
    letI : Module C K' := Module.compHom K'
      (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := C)).toRingHom
    ∃ inst : Module (A ⊗[R] C) (K ⊗[B] K'),
      letI : Module (A ⊗[R] C) (K ⊗[B] K') := inst
      (∀ (a : A) (c : C) (k : K) (k' : K'),
        (a ⊗ₜ[R] c) • (k ⊗ₜ[B] k') = (a • k) ⊗ₜ[B] (c • k')) ∧
      Nonempty
        ((moduleTensorFunctor R A C).obj
            (ModuleCat.of (A ⊗[R] C) (K ⊗[B] K')) ≅
          ((moduleTensorFunctor R A B).obj K ⋙
            (moduleTensorFunctor R B C).obj K')) := by
  let : Module A K := Module.compHom K
    (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B))
  let : Module B K := Module.compHom K
    (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom
  let : Module B K' := Module.compHom K'
    (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := B) (B := C))
  let : Module C K' := Module.compHom K'
    (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := C)).toRingHom
  have : SMulCommClass A B K := smulCommClass_compHom _ _ K
  have : SMulCommClass B A K := SMulCommClass.symm A B K
  have : SMulCommClass B C K' := smulCommClass_compHom _ _ K'
  let : Module R K := Module.compHom K (algebraMap R (A ⊗[R] B))
  let : Module R K' := Module.compHom K' (algebraMap R (B ⊗[R] C))
  have : IsScalarTower R A K := isScalarTower_compHom_of_comp _ (fun r => rfl) K
  have : IsScalarTower R B K := isScalarTower_compHom_of_comp _ (fun r => by simp) K
  have : IsScalarTower R B K' := isScalarTower_compHom_of_comp _ (fun r => rfl) K'
  have : IsScalarTower R C K' := isScalarTower_compHom_of_comp _ (fun r => by simp) K'
  let : Module C (K ⊗[B] K') := rightTensorAction (C := C) K K'
  have : IsScalarTower R C (K ⊗[B] K') := by
    refine ⟨fun r c z => ?_⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp [hz, hw]
    | tmul k k' =>
      simp [rightTensorAction_tmul, TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  have : SMulCommClass A C (K ⊗[B] K') := smulCommClass_rightTensorAction A B C K K'
  let : Module (A ⊗[R] C) (K ⊗[B] K') := TensorProduct.Algebra.module
  refine ⟨inferInstance, fun _ _ _ _ => rfl, ?_⟩
  let Q := ModuleCat.of (A ⊗[R] C) (K ⊗[B] K')
  have hA : ∀ (a : A) (z : Q),
      Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := C) a • z =
        a • z := by
    intro a z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => rw [smul_add, smul_add, hz, hw]
    | tmul k k' =>
      show TensorProduct.Algebra.moduleAux (a ⊗ₜ[R] (1 : C))
        (k ⊗ₜ[B] k') = _
      rw [TensorProduct.Algebra.moduleAux_apply, one_smul]
  have hC : ∀ (c : C) (z : Q),
      (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := C)).toRingHom c • z =
        c • z := by
    intro c z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => rw [smul_add, smul_add, hz, hw]
    | tmul k k' =>
      show TensorProduct.Algebra.moduleAux ((1 : A) ⊗ₜ[R] c)
        (k ⊗ₜ[B] k') = _
      rw [TensorProduct.Algebra.moduleAux_apply, one_smul]
  have iQ : (moduleTensorFunctor R A C).obj Q ≅
      bimoduleTensorFunctor A C (K ⊗[B] K') :=
    scalarTensorIso A C (A ⊗[R] C)
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := C))
      (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := C)).toRingHom Q hA hC
  let iK := scalarTensorIso A B (A ⊗[R] B)
    (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B))
    (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom K
    (fun _ _ => rfl) (fun _ _ => rfl)
  let iK' := scalarTensorIso B C (B ⊗[R] C)
    (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := B) (B := C))
    (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := C)).toRingHom K'
    (fun _ _ => rfl) (fun _ _ => rfl)
  let iAssoc := bimoduleTensorAssocIso A B C (A ⊗[R] B)
    (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := B))
    (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom K K'
  exact ⟨iQ ≪≫ iAssoc ≪≫
    Functor.isoWhiskerLeft (bimoduleTensorFunctor A B K) iK'.symm ≪≫
    Functor.isoWhiskerRight iK.symm ((moduleTensorFunctor R B C).obj K')⟩

end ModuleCat
