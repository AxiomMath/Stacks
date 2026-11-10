module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerConstraints
public import StacksFrontier.CategoryTheory.Equivalence.Pow
public import StacksCore.Tactic.StacksAttribute

/-!
# The canonical multiplication on the tensor powers of an invertible sheaf of modules

Let `O` be a sheaf of commutative rings on a site and let `L` be an invertible sheaf of
`O`-modules. The integer tensor powers `L^{⊗ n}`, defined as the powers of the autoequivalence
`e = - ⊗_O L` applied to the structure sheaf, carry canonical multiplication isomorphisms
`L^{⊗ n} ⊗_O L^{⊗ m} ≅ L^{⊗ (n + m)}`, obtained from the addition law for the integer powers of
`e` and the identification of `(e ^ m).functor` with `- ⊗_O L^{⊗ m}`.

## Main definitions

* `Stacks.SheafOfModules.TensorPower.tensorRightFunctorObjIso`: tensoring on the right by a
  tensor product sheaf is the composite of the two right-tensor functors.
* `Stacks.SheafOfModules.TensorPower.tensorRightUnitIso`: tensoring on the right by the structure
  sheaf is the identity functor.
* `Stacks.SheafOfModules.TensorPower.cancelRightEquivalence`: two endofunctors which agree after
  composing with an equivalence are isomorphic.
* `Stacks.SheafOfModules.TensorPower.powFunctorIsoTensorRight`: the isomorphism
  `(e ^ m).functor ≅ - ⊗_O L^{⊗ m}`, for every `m : ℤ`.
* `Stacks.SheafOfModules.TensorPower.tensorSheafMapIso`: the tensor product sheaf of two
  isomorphisms.
* `Stacks.SheafOfModules.TensorPower.tensorPowerMulIso`: the canonical multiplication
  isomorphism `L^{⊗ n} ⊗_O L^{⊗ m} ≅ L^{⊗ (n + m)}`.

## Main results

* `Stacks.Equivalence.powSucc_app`: the successor comparison `Stacks.Equivalence.powSuccIso` is
  the addition law `CategoryTheory.Equivalence.powAdd` at right exponent one, evaluated at an
  object.
* `Stacks.Equivalence.powAdd_app_cast`: the addition law at a target exponent presented by an
  equation is the addition law at the literal sum, reindexed along that equation.
* `Stacks.SheafOfModules.TensorPower.tensorPowerMulIso_one_right`: multiplication by the first
  power is the successor comparison, after identifying `L^{⊗ 1}` with `L`.
* `Stacks.SheafOfModules.TensorPower.tensorPowerMulIso_zero_right`: multiplication by the
  zeroth power on the right is the right unit constraint of the tensor product sheaf.
* `Stacks.SheafOfModules.TensorPower.tensorPowerReindex_eq_eqToIso`: reindexing a tensor power
  along an equality of exponents is the transport isomorphism.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u w

namespace Stacks.Equivalence

variable {A : Type u} [Category.{v} A] (e : A ≌ A)

/-- Composition of morphisms respects equality in both arguments. -/
theorem comp_congr {X Y Z : A} {a a' : X ⟶ Y} {b b' : Y ⟶ Z} (ha : a = a') (hb : b = b') :
    a ≫ b = a' ≫ b' := by rw [ha, hb]

private theorem id_comp' {X Z : A} (a : X ⟶ X) (ha : a = 𝟙 X) (f : X ⟶ Z) : a ≫ f = f := by
  rw [ha, Category.id_comp]

private theorem comp_id' {X Z : A} (b : Z ⟶ Z) (hb : b = 𝟙 Z) (f : X ⟶ Z) : f ≫ b = f := by
  rw [hb, Category.comp_id]

/-- `Stacks.Equivalence.powSucc_app` at a non-negative exponent. -/
theorem powSucc_app_ofNat : (k : ℕ) → (M : A) →
    (CategoryTheory.Equivalence.powSucc e (Int.ofNat k) (Int.ofNat k + 1) rfl).app M =
      powSuccIso e (Int.ofNat k) M
  | 0, M => (congrArg (Iso.app · M) (CategoryTheory.Equivalence.powSucc_zero e)).trans rfl
  | 1, M => by
      have h1 : (CategoryTheory.Equivalence.powStepUp e (Int.ofNat 0)
          (Int.ofNat 1) rfl).inv.app M = 𝟙 _ := rfl
      have h2 : (CategoryTheory.Equivalence.powStepUp e (Int.ofNat 1)
          (Int.ofNat 1 + 1) rfl).hom.app M = 𝟙 _ := rfl
      have ha := (congrArg (fun g => e.functor.map g) h1).trans (e.functor.map_id _)
      have ih := congrArg Iso.hom (powSucc_app_ofNat 0 (e.functor.obj M))
      rw [CategoryTheory.Equivalence.powSucc_succ e (Int.ofNat 0)
        (Int.ofNat 1) (Int.ofNat 1 + 1) rfl rfl]
      exact Iso.ext ((id_comp' _ ha _).trans ((comp_id' _ h2 _).trans ih))
  | k + 2, M => by
      have h1 : (CategoryTheory.Equivalence.powStepUp e (Int.ofNat (k + 1))
          (Int.ofNat (k + 2)) rfl).inv.app M = 𝟙 _ := rfl
      have h2 : (CategoryTheory.Equivalence.powStepUp e (Int.ofNat (k + 2))
          (Int.ofNat (k + 2) + 1) rfl).hom.app M = 𝟙 _ := rfl
      have ha := (congrArg (fun g => e.functor.map g) h1).trans (e.functor.map_id _)
      have ih := congrArg Iso.hom (powSucc_app_ofNat (k + 1) (e.functor.obj M))
      rw [CategoryTheory.Equivalence.powSucc_succ e (Int.ofNat (k + 1))
        (Int.ofNat (k + 2)) (Int.ofNat (k + 2) + 1) rfl rfl]
      exact Iso.ext ((id_comp' _ ha _).trans ((comp_id' _ h2 _).trans ih))

/-- `Stacks.Equivalence.powSucc_app` at a negative exponent. -/
theorem powSucc_app_negSucc : (k : ℕ) → (M : A) →
    (CategoryTheory.Equivalence.powSucc e (Int.negSucc k) (Int.negSucc k + 1) rfl).app M =
      powSuccIso e (Int.negSucc k) M
  | 0, M => by
      have hstep := CategoryTheory.Equivalence.powAdd_pred e 0 1 1 0 (Int.negSucc 0)
        rfl rfl rfl
      simp only [CategoryTheory.Equivalence.powAdd_one_right] at hstep
      have h1 : (CategoryTheory.Equivalence.powStepDown e 0 (Int.negSucc 0) rfl).inv.app M =
          𝟙 _ := rfl
      have ha := (congrArg (fun g => (e ^ (1 : ℤ)).functor.map g) h1).trans
        ((e ^ (1 : ℤ)).functor.map_id _)
      have hb : (CategoryTheory.Equivalence.powSucc e 0 1 rfl).hom.app (e.inverse.obj M) =
          𝟙 _ := rfl
      have hc : (CategoryTheory.Equivalence.powStepDown e 1 0 rfl).hom.app M =
          e.counitIso.hom.app M := by
        rw [CategoryTheory.Equivalence.powStepDown_of_pos e (n := (1 : ℤ)) (p := (0 : ℤ))
          rfl one_pos]
        exact id_comp' _ rfl _
      change (CategoryTheory.Equivalence.powSucc e (Int.negSucc 0) 0 rfl).app M =
        powSuccIso e (Int.negSucc 0) M
      rw [hstep]
      exact Iso.ext ((id_comp' _ ha _).trans ((id_comp' _ hb _).trans hc))
  | 1, M => by
      have hstep := CategoryTheory.Equivalence.powAdd_pred e (Int.negSucc 0) 1
        (Int.negSucc 0 + 1) (Int.negSucc 0) (Int.negSucc 1) rfl rfl rfl
      simp only [CategoryTheory.Equivalence.powAdd_one_right] at hstep
      have h1 : (CategoryTheory.Equivalence.powStepDown e (Int.negSucc 0)
          (Int.negSucc 1) rfl).inv.app M = 𝟙 _ := rfl
      have h2 : (CategoryTheory.Equivalence.powStepDown e (Int.negSucc 0 + 1)
          (Int.negSucc 0) rfl).hom.app M = 𝟙 _ := rfl
      have ha := (congrArg (fun g => (e ^ (1 : ℤ)).functor.map g) h1).trans
        ((e ^ (1 : ℤ)).functor.map_id _)
      have ih := congrArg Iso.hom (powSucc_app_negSucc 0 (e.inverse.obj M))
      change (CategoryTheory.Equivalence.powSucc e (Int.negSucc 1) (Int.negSucc 0) rfl).app M =
        powSuccIso e (Int.negSucc 1) M
      rw [hstep]
      exact Iso.ext ((id_comp' _ ha _).trans ((comp_id' _ h2 _).trans ih))
  | k + 2, M => by
      have hstep := CategoryTheory.Equivalence.powAdd_pred e (Int.negSucc (k + 1)) 1
        (Int.negSucc (k + 1) + 1) (Int.negSucc (k + 1)) (Int.negSucc (k + 2)) rfl rfl rfl
      simp only [CategoryTheory.Equivalence.powAdd_one_right] at hstep
      have h1 : (CategoryTheory.Equivalence.powStepDown e (Int.negSucc (k + 1))
          (Int.negSucc (k + 2)) rfl).inv.app M = 𝟙 _ := rfl
      have h2 : (CategoryTheory.Equivalence.powStepDown e (Int.negSucc (k + 1) + 1)
          (Int.negSucc (k + 1)) rfl).hom.app M = 𝟙 _ := rfl
      have ha := (congrArg (fun g => (e ^ (1 : ℤ)).functor.map g) h1).trans
        ((e ^ (1 : ℤ)).functor.map_id _)
      have ih := congrArg Iso.hom (powSucc_app_negSucc (k + 1) (e.inverse.obj M))
      change (CategoryTheory.Equivalence.powSucc e (Int.negSucc (k + 2))
          (Int.negSucc (k + 1)) rfl).app M = powSuccIso e (Int.negSucc (k + 2)) M
      rw [hstep]
      exact Iso.ext ((id_comp' _ ha _).trans ((comp_id' _ h2 _).trans ih))

/-- The addition law at a target exponent given by an equation is the addition law at the literal
sum, reindexed along that equation. -/
theorem powAdd_app_cast (n m p : ℤ) (h : n + m = p) (M : A) :
    (CategoryTheory.Equivalence.powAdd e n m p h).app M =
      (CategoryTheory.Equivalence.powAdd e n m (n + m) rfl).app M ≪≫
        eqToIso (congrArg (fun q => (e ^ q).functor.obj M) h) := by
  subst h
  simp

/-- The successor comparison `powSuccIso` is the addition law
`CategoryTheory.Equivalence.powAdd` at right exponent one, evaluated at an object. -/
theorem powSucc_app (n : ℤ) (M : A) :
    (CategoryTheory.Equivalence.powSucc e n (n + 1) rfl).app M = powSuccIso e n M := by
  match n with
  | Int.ofNat k => exact powSucc_app_ofNat e k M
  | Int.negSucc k => exact powSucc_app_negSucc e k M

end Stacks.Equivalence

namespace Stacks.SheafOfModules.TensorPower

open Stacks.SheafOfModules Stacks.Equivalence

attribute [local instance] monoidalCategoryPresheafOfModules symmetricCategoryPresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- Tensoring on the right by a tensor product sheaf is the composite of the two right-tensor
functors: `Z ⊗ (X ⊗ Y) ≅ (Z ⊗ Y) ⊗ X`. -/
noncomputable def tensorRightFunctorObjIso
    (X Y : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂ CommRingCat RingCat) (hO)⟩).obj (X)).obj (Y))) ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj Y ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj X :=
  (tensorLeftIsoTensorRight O hO ((((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (X)).obj
    (Y)))).symm ≪≫
    Stacks.SheafOfModules.tensorLeftFunctorObjIso O hO X Y ≪≫
    Functor.isoWhiskerRight (tensorLeftIsoTensorRight O hO Y)
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj X) ≪≫
    Functor.isoWhiskerLeft ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj Y)
        (tensorLeftIsoTensorRight O hO X)

/-- Tensoring on the right by the structure sheaf is the identity functor: the right unit
constraint of the presheaf tensor product, followed by the counit of sheafification. -/
noncomputable def tensorRightUnitIso :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        (SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ≅ 𝟭 _ :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (SheafOfModules.forget
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
        (rightUnitorNatIso (PresheafOfModules.{w}
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)))
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO) ≪≫
    Stacks.SheafOfModules.forgetSheafifyIso O hO

/-- Cancellation of an equivalence composed on the right: two functors which agree after
composing with an equivalence are isomorphic. -/
noncomputable def cancelRightEquivalence {D : Type u} [Category.{v} D] (e : D ≌ D)
    {P Q : D ⥤ D} (i : P ⋙ e.functor ≅ Q ⋙ e.functor) : P ≅ Q :=
  NatIso.ofComponents (fun X => e.functor.preimageIso (i.app X))
    (fun {X Y} f => e.functor.map_injective (by
      rw [e.functor.map_comp, e.functor.map_comp, Functor.preimageIso_hom,
        Functor.preimageIso_hom, Functor.map_preimage, Functor.map_preimage]
      exact i.hom.naturality f))

variable (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
  [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).IsEquivalence]

/-- Tensoring on the right by `L^{⊗ (n+1)}` is tensoring on the right by `L^{⊗ n}` and then
by `L`. -/
noncomputable def tensorRightFunctorPowSuccIso (n : ℤ) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        (tensorPower O hO L (n + 1)) ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        (tensorPower O hO L n) ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj L :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.mapIso
      ((tensorPowerSuccIso O hO L n).symm ≪≫
        Stacks.SheafOfModules.tensorSheafBraiding O hO (tensorPower O hO L n) L) ≪≫
    tensorRightFunctorObjIso O hO L (tensorPower O hO L n)

/-- The isomorphism `((- ⊗ L) ^ k).functor ≅ - ⊗ L^{⊗ k}` for `k : ℕ`, given at `0` by the right
unit constraint and at `1` by the identification of `L^{⊗ 1}` with `L`. -/
noncomputable def powFunctorIsoNat : (k : ℕ) →
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).asEquivalence ^ (Int.ofNat k)).functor ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        (tensorPower O hO L (Int.ofNat k)))
  | 0 => (tensorRightUnitIso O hO).symm
  | 1 => (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.mapIso
        (tensorPowerOneIso O hO L).symm
  | k + 2 =>
      (CategoryTheory.Equivalence.powSucc ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).asEquivalence
          (Int.ofNat (k + 1)) (Int.ofNat (k + 1) + 1) rfl).symm ≪≫
        Functor.isoWhiskerRight (powFunctorIsoNat (k + 1))
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj L) ≪≫
        (tensorRightFunctorPowSuccIso O hO L (Int.ofNat (k + 1))).symm

/-- An isomorphism `((- ⊗ L) ^ (m + 1)).functor ≅ - ⊗ L^{⊗ (m + 1)}` induces one
`((- ⊗ L) ^ m).functor ≅ - ⊗ L^{⊗ m}`, by cancelling the equivalence `- ⊗ L`. -/
noncomputable def powFunctorIsoPred (m : ℤ)
    (x : ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).asEquivalence) ^ (m + 1)).functor ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        (tensorPower O hO L (m + 1))) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).asEquivalence) ^ m).functor ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        (tensorPower O hO L m) :=
  cancelRightEquivalence ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).asEquivalence
    (CategoryTheory.Equivalence.powSucc ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).asEquivalence m (m + 1) rfl ≪≫
      x ≪≫ tensorRightFunctorPowSuccIso O hO L m)

/-- The isomorphism `((- ⊗ L) ^ m).functor ≅ - ⊗ L^{⊗ m}` for negative `m`. -/
noncomputable def powFunctorIsoNegSucc : (k : ℕ) →
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).asEquivalence ^ (Int.negSucc k)).functor ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        (tensorPower O hO L (Int.negSucc k)))
  | 0 => powFunctorIsoPred O hO L (Int.negSucc 0) (powFunctorIsoNat O hO L 0)
  | k + 1 => powFunctorIsoPred O hO L (Int.negSucc (k + 1)) (powFunctorIsoNegSucc k)

/-- Tensoring `m` times on the right by `L` is tensoring once on the right by `L^{⊗ m}`. -/
noncomputable def powFunctorIsoTensorRight : (m : ℤ) →
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).asEquivalence ^ m).functor ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        (tensorPower O hO L m))
  | Int.ofNat k => powFunctorIsoNat O hO L k
  | Int.negSucc k => powFunctorIsoNegSucc O hO L k

/-- The tensor product sheaf of two isomorphisms of sheaves of modules. -/
noncomputable def tensorSheafMapIso
    {M M' N N' : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)}
    (i : M ≅ M') (j : N ≅ N') :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂
      CommRingCat RingCat) (hO)⟩).obj (M)).obj (N)) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂ CommRingCat RingCat) (hO)⟩).obj (M')).obj (N')) :=
  (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).mapIso
    (tensorIso ((SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)).mapIso i)
      ((SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
        hO)).mapIso j))

/-- The canonical multiplication isomorphism `L^{⊗ n} ⊗_O L^{⊗ m} ≅ L^{⊗ (n + m)}`, the addition
law `CategoryTheory.Equivalence.powAdd` for the powers of `- ⊗ L` applied to the structure sheaf,
read through `powFunctorIsoTensorRight`. -/
@[stacks 01CU "canonical multiplication"]
noncomputable def tensorPowerMulIso (n m : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂
      CommRingCat RingCat) (hO)⟩).obj ((tensorPower O hO L n))).obj ((tensorPower
      O hO L m))) ≅
      tensorPower O hO L (n + m) :=
  ((powFunctorIsoTensorRight O hO L m).app (tensorPower O hO L n)).symm ≪≫
    (CategoryTheory.Equivalence.powAdd ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).asEquivalence n m (n + m)
      rfl).app (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
        hO))

/-- Multiplication by the first power is the successor comparison `tensorPowerSuccIso`, after
identifying `L^{⊗ 1}` with `L`. -/
theorem tensorPowerMulIso_one_right (n : ℤ) :
    tensorPowerMulIso O hO L n 1 =
      tensorSheafMapIso O hO (Iso.refl (tensorPower O hO L n)) (tensorPowerOneIso O hO L) ≪≫
        tensorPowerSuccIso O hO L n := by
  have hA : (((powFunctorIsoTensorRight O hO L 1).app (tensorPower O hO L n)).symm).hom =
      (tensorSheafMapIso O hO (Iso.refl (tensorPower O hO L n))
        (tensorPowerOneIso O hO L)).hom :=
    congrArg (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
      (MonoidalCategory.id_tensorHom (tensorPower O hO L n).val
        ((SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
          hO)).map
          (tensorPowerOneIso O hO L).hom)).symm
  have hB : ((CategoryTheory.Equivalence.powAdd
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).asEquivalence n 1
        (n + 1) rfl).app (SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))).hom =
      (tensorPowerSuccIso O hO L n).hom :=
    congrArg Iso.hom (Stacks.Equivalence.powSucc_app
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).asEquivalence n
      (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)))
  exact Iso.ext (comp_congr hA hB)

/-- Reindexing a tensor power along an equality of exponents is the transport isomorphism. -/
theorem tensorPowerReindex_eq_eqToIso {n m : ℤ} (h : n = m) :
    tensorPowerReindex O hO L h = eqToIso (congrArg (tensorPower O hO L) h) := by
  subst h
  simp

/-- Multiplication by the zeroth power on the right is the right unit constraint of the tensor
product sheaf, the presheaf right unitor followed by the counit of sheafification. -/
theorem tensorPowerMulIso_zero_right (n : ℤ) :
    tensorPowerMulIso O hO L n 0 ≪≫ tensorPowerReindex O hO L (Int.add_zero n) =
      Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso O hO (tensorPower O hO L n) := by
  have hz : (CategoryTheory.Equivalence.powAdd
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).asEquivalence n 0
        (n + 0) rfl).app (SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ≪≫
      tensorPowerReindex O hO L (Int.add_zero n) = Iso.refl _ := by
    rw [tensorPowerReindex_eq_eqToIso]
    have h := Stacks.Equivalence.powAdd_app_cast
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).asEquivalence n 0 n (Int.add_zero n)
      (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    rw [CategoryTheory.Equivalence.powAdd_zero_right] at h
    exact h.symm
  have key : tensorPowerMulIso O hO L n 0 ≪≫ tensorPowerReindex O hO L (Int.add_zero n) =
      ((powFunctorIsoTensorRight O hO L 0).app (tensorPower O hO L n)).symm :=
    (Iso.trans_assoc _ _ _).trans
      ((congrArg (fun z =>
          ((powFunctorIsoTensorRight O hO L 0).app (tensorPower O hO L n)).symm ≪≫ z) hz).trans
        (Iso.trans_refl _))
  exact key.trans rfl

end Stacks.SheafOfModules.TensorPower

end
