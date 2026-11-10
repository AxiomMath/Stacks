module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.RingTheory.Flat.TorsionFree
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsBetweenCategories.BimoduleTensor
public import StacksCore.Tactic.StacksAttribute

/-!
# Monoidal functors between categories of modules

A monoidal functor between categories of modules induces a multiplicative map of the
coefficient rings. Additivity makes that map a ring homomorphism, and preservation of colimits
characterizes extension of scalars. Tensor squaring and the torsion-free quotient give a
nonadditive and a nonidentity example.

## Main definitions

* `ModuleCat.scalarValue` is the value on the unit of the image of multiplication by a scalar.
* `ModuleCat.tensorSquareFunctor` and `ModuleCat.torsionFreeQuotientFunctor` are the two
  examples.

## Main results

* `ModuleCat.monoidHomOfMonoidal` constructs the induced multiplicative map, and
  `ModuleCat.ringHomOfAdditive` upgrades it to a ring homomorphism for an additive functor.
* `ModuleCat.tensorSquare`, `ModuleCat.torsionFreeQuotient`,
  `ModuleCat.torsionFreeQuotient_scalarValue`,
  `ModuleCat.torsionFreeQuotient_scalar_action` and
  `ModuleCat.torsionFreeQuotient_not_iso_id` are the two examples and their properties.
* `ModuleCat.iso_extendScalars_of_rightExact_preservesDirectSums` identifies a right-exact
  monoidal functor preserving direct sums with extension of scalars, and
  `ModuleCat.extendScalars_injective_up_to_iso` together with
  `ModuleCat.extendScalars_monoidal_preservesColimits` say that this is a bijection onto the
  ring homomorphisms.

## References

* [Stacks Project, Tag 0GP2](https://stacks.math.columbia.edu/tag/0GP2)
-/

@[expose] public section

namespace ModuleCat

open scoped TensorProduct

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The diagonal tensor-product functor on modules. -/
public def tensorSquareFunctor (A : Type u) [CommRing A] :
    ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  (𝟭 (ModuleCat.{u} A)).prod' (𝟭 (ModuleCat.{u} A)) ⋙
    MonoidalCategory.tensor (ModuleCat.{u} A)

/-- The quotient by the torsion submodule, on objects and linear maps. -/
@[ega "II 6.4.2"]
public def torsionFreeQuotientFunctor : ModuleCat.{u} ℤ ⥤ ModuleCat.{u} ℤ where
  obj M := ModuleCat.of ℤ (M ⧸ Submodule.torsion ℤ M)
  map {M N} f := ModuleCat.ofHom <|
    Submodule.mapQ (Submodule.torsion ℤ M) (Submodule.torsion ℤ N) f.hom
      (by
        intro x hx
        obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff (R := ℤ) x).mp hx
        exact (Submodule.mem_torsion_iff (R := ℤ) (f.hom x)).mpr
          ⟨a, by
            simp only [Submonoid.smul_def] at ha ⊢
            rw [← f.hom.map_smul, ha, map_zero]⟩)
  map_id M := by
    apply ModuleCat.hom_ext
    ext x
    induction x using Submodule.Quotient.induction_on
    rfl
  map_comp {M N P} f g := by
    apply ModuleCat.hom_ext
    ext x
    induction x using Submodule.Quotient.induction_on
    rfl

/-- The value at `1` of the image under `F` of multiplication by `a`, transported across the
monoidal unit isomorphism `CategoryTheory.Functor.Monoidal.εIso F`. -/
public noncomputable def scalarValue (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B)
    [F.Monoidal] (a : A) : B :=
  ((Functor.Monoidal.εIso F).hom ≫
    F.map (ModuleCat.ofHom (LinearMap.mulLeft A a)) ≫
    (Functor.Monoidal.εIso F).inv).hom (1 : B)

add_to_stacks 0GP2 "part (1): the unit isomorphism" CategoryTheory.Functor.Monoidal.εIso

/-- A monoidal functor canonically induces a multiplicative map on scalars. -/
@[stacks 0GP2 "part (2): multiplicative scalar map"]
public noncomputable def monoidHomOfMonoidal
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.Monoidal] :
    { φ : A →* B // ∀ a, φ a = scalarValue F a } := by
  let f : A →* B := {
    toFun := scalarValue F
    map_one' := by
      have h1 : ModuleCat.ofHom (LinearMap.mulLeft A (1 : A)) =
          𝟙 (𝟙_ (ModuleCat.{u} A)) := by
        apply ModuleCat.hom_ext
        ext
        simp
        rfl
      have he : (Functor.Monoidal.εIso F).hom ≫
          F.map (ModuleCat.ofHom (LinearMap.mulLeft A (1 : A))) ≫
          (Functor.Monoidal.εIso F).inv = 𝟙 _ := by
        rw [h1]
        simp
      change ((Functor.Monoidal.εIso F).hom ≫
        F.map (ModuleCat.ofHom (LinearMap.mulLeft A (1 : A))) ≫
        (Functor.Monoidal.εIso F).inv).hom 1 = 1
      rw [he]
      rfl
    map_mul' := by
      intro a b
      let e (x : A) : ModuleCat.of B B ⟶ ModuleCat.of B B :=
        (Functor.Monoidal.εIso F).hom ≫
          F.map (ModuleCat.ofHom (LinearMap.mulLeft A x)) ≫
          (Functor.Monoidal.εIso F).inv
      have hab : ModuleCat.ofHom (LinearMap.mulLeft A (a * b)) =
          ModuleCat.ofHom (LinearMap.mulLeft A a) ≫
            ModuleCat.ofHom (LinearMap.mulLeft A b) := by
        apply ModuleCat.hom_ext
        ext
        simp [LinearMap.mulLeft_apply, mul_comm]
      have he : e (a * b) = e a ≫ e b := by
        dsimp [e]
        rw [hab, Functor.map_comp]
        simp [Category.assoc]
      change (e (a * b)).hom 1 = (e a).hom 1 * (e b).hom 1
      rw [he]
      simpa [smul_eq_mul] using (e b).hom.map_smul ((e a).hom 1) (1 : B)
  }
  exact ⟨f, fun _ => rfl⟩

/-- The scalar map of an additive monoidal functor preserves addition. -/
@[stacks 0GP2 "part (4): additive scalar map"]
public theorem scalarValue_add (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B)
    [F.Monoidal] [F.Additive] (a b : A) :
    scalarValue F (a + b) = scalarValue F a + scalarValue F b := by
  let e (x : A) : ModuleCat.of B B ⟶ ModuleCat.of B B :=
    (Functor.Monoidal.εIso F).hom ≫
      F.map (ModuleCat.ofHom (LinearMap.mulLeft A x)) ≫
      (Functor.Monoidal.εIso F).inv
  have hab : ModuleCat.ofHom (LinearMap.mulLeft A (a + b)) =
      ModuleCat.ofHom (LinearMap.mulLeft A a) +
        ModuleCat.ofHom (LinearMap.mulLeft A b) := by
    apply ModuleCat.hom_ext
    ext
    simp [LinearMap.mulLeft_apply]
  have he : e (a + b) = e a + e b := by
    apply ModuleCat.hom_ext
    ext
    simp only [e, hab, F.map_add, ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.hom_add, LinearMap.add_apply]
    exact (Functor.Monoidal.εIso F).inv.hom.map_add _ _
  change (e (a + b)).hom 1 = (e a).hom 1 + (e b).hom 1
  rw [he]
  rfl

/-- An additive monoidal functor induces a ring homomorphism. -/
@[stacks 0GP2 "part (4): ring homomorphism"]
public noncomputable def ringHomOfAdditive
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.Monoidal] [F.Additive] :
    { φ : A →+* B // ∀ a, φ a = scalarValue F a } := by
  let φ := (monoidHomOfMonoidal F).1
  have hadd : ∀ a b, φ (a + b) = φ a + φ b := by
    intro a b
    rw [(monoidHomOfMonoidal F).2, (monoidHomOfMonoidal F).2,
      (monoidHomOfMonoidal F).2]
    exact scalarValue_add F a b
  exact ⟨RingHom.mk' φ hadd, (monoidHomOfMonoidal F).2⟩

/-- Tensor squaring is a monoidal functor whose scalar map is squaring. -/
@[stacks 0GP2 "part (3): tensor-square example"]
public theorem tensorSquare (A : Type u) [CommRing A] :
    ∃ h : (tensorSquareFunctor A).Monoidal,
      ∀ a : A, letI : (tensorSquareFunctor A).Monoidal := h
        scalarValue (tensorSquareFunctor A) a = a ^ 2 := by
  let h : (tensorSquareFunctor A).Monoidal := by
    change (((𝟭 (ModuleCat.{u} A)).prod' (𝟭 (ModuleCat.{u} A))) ⋙
      MonoidalCategory.tensor (ModuleCat.{u} A)).Monoidal
    infer_instance
  refine ⟨h, fun a => ?_⟩
  let : (tensorSquareFunctor A).Monoidal := h
  dsimp [scalarValue, tensorSquareFunctor]
  simp only [Functor.id_obj,
    Functor.prod'_ε_fst, Functor.LaxMonoidal.id_ε, Functor.prod'_ε_snd, tensorHom_id,
    whiskerRight_id, Category.id_comp, Iso.hom_inv_id, Functor.prod'_η_fst,
    Functor.OplaxMonoidal.id_η, Functor.prod'_η_snd, ModuleCat.hom_hom_leftUnitor,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply, LinearEquiv.coe_coe, pow_two]
  change TensorProduct.lid A A ((a * 1) ⊗ₜ[A] (a * 1)) = a * a
  simp [smul_eq_mul]

private lemma torsion_le_ker {R M N : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.IsTorsionFree R N] (f : M →ₗ[R] N) :
    Submodule.torsion R M ≤ LinearMap.ker f := by
  intro x hx
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
  have hf : f x ∈ Submodule.torsion R N := by
    refine (Submodule.mem_torsion_iff _).mpr ⟨a, ?_⟩
    change (a : R) • x = 0 at ha
    change (a : R) • f x = 0
    rw [← f.map_smul, ha, map_zero]
  rwa [(Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)] at hf

private def torsionTensorHom {R M N : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    (M ⧸ Submodule.torsion R M) ⊗[R] (N ⧸ Submodule.torsion R N) →ₗ[R]
      (M ⊗[R] N) ⧸ Submodule.torsion R (M ⊗[R] N) :=
  TensorProduct.lift (LinearMap.liftQ₂ (Submodule.torsion R M)
    (Submodule.torsion R N)
    (TensorProduct.curry (Submodule.torsion R (M ⊗[R] N)).mkQ)
    (torsion_le_ker _) (torsion_le_ker _))

private def torsionTensorInv {R M N : Type*} [CommRing R] [IsDedekindDomain R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    ((M ⊗[R] N) ⧸ Submodule.torsion R (M ⊗[R] N)) →ₗ[R]
      (M ⧸ Submodule.torsion R M) ⊗[R] (N ⧸ Submodule.torsion R N) :=
  (Submodule.torsion R (M ⊗[R] N)).liftQ
    (TensorProduct.map (Submodule.torsion R M).mkQ (Submodule.torsion R N).mkQ)
    (torsion_le_ker _)

private def quotientTorsionModule (M : ModuleCat.{u} ℤ) : ModuleCat.{u} ℤ :=
  @ModuleCat.of ℤ _ (M ⧸ Submodule.torsion ℤ M) _ (Submodule.Quotient.module _)

private def quotientTorsionComparison (M : ModuleCat.{u} ℤ) :
    quotientTorsionModule M ≅ torsionFreeQuotientFunctor.obj M :=
  (AddEquiv.toIntLinearEquiv
    (modM := (quotientTorsionModule M).isModule)
    (modM₂ := (torsionFreeQuotientFunctor.obj M).isModule)
    (AddEquiv.refl _)).toModuleIso

private def quotientTorsionTensorIso (M N : ModuleCat.{u} ℤ) :
    quotientTorsionModule M ⊗ quotientTorsionModule N ≅
      quotientTorsionModule (M ⊗ N) where
  hom := ModuleCat.homEquiv.symm
    (@torsionTensorHom ℤ M N _ _ M.isAddCommGroup M.isModule N.isAddCommGroup N.isModule)
  inv := ModuleCat.homEquiv.symm
    (@torsionTensorInv ℤ M N _ _ M.isAddCommGroup M.isModule N.isAddCommGroup N.isModule)
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    induction x using Submodule.Quotient.induction_on
    induction y using Submodule.Quotient.induction_on
    rfl
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply (Submodule.torsion ℤ ((M ⊗ N) : ModuleCat ℤ)).linearMap_qext
    apply TensorProduct.ext'
    intro x y
    rfl

private def torsionTensorIso (M N : ModuleCat.{u} ℤ) :
    torsionFreeQuotientFunctor.obj M ⊗ torsionFreeQuotientFunctor.obj N ≅
      torsionFreeQuotientFunctor.obj (M ⊗ N) :=
  tensorIso (quotientTorsionComparison M).symm (quotientTorsionComparison N).symm ≪≫
    quotientTorsionTensorIso M N ≪≫ quotientTorsionComparison (M ⊗ N)

private def torsionUnitIso :
    𝟙_ (ModuleCat.{u} ℤ) ≅ torsionFreeQuotientFunctor.obj (𝟙_ (ModuleCat.{u} ℤ)) :=
  ((Submodule.torsion ℤ (𝟙_ (ModuleCat.{u} ℤ))).quotEquivOfEqBot
    (Submodule.isTorsionFree_iff_torsion_eq_bot.mp
      (inferInstanceAs (Module.IsTorsionFree ℤ (ULift.{u} ℤ))))).symm.toModuleIso

private lemma torsionTensorIso_hom_tmul (M N : ModuleCat.{u} ℤ) (m : M) (n : N) :
    (torsionTensorIso M N).hom.hom (Submodule.Quotient.mk m ⊗ₜ[ℤ] Submodule.Quotient.mk n) =
      (Submodule.torsion ℤ ((M ⊗ N) : ModuleCat ℤ)).mkQ (m ⊗ₜ[ℤ] n) := rfl

private lemma lifted_leftUnitor_hom_tmul (M : ModuleCat.{u} ℤ)
    (a : 𝟙_ (ModuleCat.{u} ℤ)) (m : M) :
    (λ_ M).hom.hom (a ⊗ₜ[ℤ] m) = a.down • m := by
  change (TensorProduct.lid ℤ M)
    ((TensorProduct.congr ULift.moduleEquiv (LinearEquiv.refl ℤ M)) (a ⊗ₜ[ℤ] m)) = _
  rw [TensorProduct.congr_tmul, TensorProduct.lid_tmul]
  exact Int.cast_smul_eq_zsmul ℤ a.down m

private lemma lifted_rightUnitor_hom_tmul (M : ModuleCat.{u} ℤ)
    (a : 𝟙_ (ModuleCat.{u} ℤ)) (m : M) :
    (ρ_ M).hom.hom (m ⊗ₜ[ℤ] a) = a.down • m := by
  change (TensorProduct.rid ℤ M)
    ((TensorProduct.congr (LinearEquiv.refl ℤ M) ULift.moduleEquiv) (m ⊗ₜ[ℤ] a)) = _
  rw [TensorProduct.congr_tmul, TensorProduct.rid_tmul]
  exact Int.cast_smul_eq_zsmul ℤ a.down m

/-- Quotienting abelian groups by torsion is monoidal. -/
@[stacks 0GP2 "part (5): monoidal torsion-free quotient"]
public theorem torsionFreeQuotient :
    Nonempty torsionFreeQuotientFunctor.{u}.Monoidal := by
  refine ⟨Functor.CoreMonoidal.toMonoidal {
    εIso := torsionUnitIso
    μIso := torsionTensorIso
    μIso_hom_natural_left := ?_
    μIso_hom_natural_right := ?_
    associativity := ?_
    left_unitality := ?_
    right_unitality := ?_ }⟩
  · intro X Y f Z
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x z
    induction x using Submodule.Quotient.induction_on
    induction z using Submodule.Quotient.induction_on
    rfl
  · intro X Y Z f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro z x
    induction z using Submodule.Quotient.induction_on
    induction x using Submodule.Quotient.induction_on
    rfl
  · intro X Y Z
    apply ModuleCat.hom_ext
    apply TensorProduct.ext_threefold
    intro x y z
    induction x using Submodule.Quotient.induction_on
    induction y using Submodule.Quotient.induction_on
    induction z using Submodule.Quotient.induction_on
    rfl
  · intro X
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro a x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      refine (lifted_leftUnitor_hom_tmul _ a _).trans ?_
      change a.down • (Submodule.Quotient.mk x : torsionFreeQuotientFunctor.obj X) =
        (torsionFreeQuotientFunctor.map (λ_ X).hom).hom
          ((torsionTensorIso (𝟙_ (ModuleCat.{u} ℤ)) X).hom.hom
            (Submodule.Quotient.mk a ⊗ₜ[ℤ] Submodule.Quotient.mk x))
      rw [torsionTensorIso_hom_tmul]
      change a.down • (Submodule.Quotient.mk x : torsionFreeQuotientFunctor.obj X) =
        Submodule.Quotient.mk ((λ_ X).hom.hom (a ⊗ₜ[ℤ] x))
      rw [lifted_leftUnitor_hom_tmul]
      simp
  · intro X
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x a
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      refine (lifted_rightUnitor_hom_tmul _ a _).trans ?_
      change a.down • (Submodule.Quotient.mk x : torsionFreeQuotientFunctor.obj X) =
        (torsionFreeQuotientFunctor.map (ρ_ X).hom).hom
          ((torsionTensorIso X (𝟙_ (ModuleCat.{u} ℤ))).hom.hom
            (Submodule.Quotient.mk x ⊗ₜ[ℤ] Submodule.Quotient.mk a))
      rw [torsionTensorIso_hom_tmul]
      change a.down • (Submodule.Quotient.mk x : torsionFreeQuotientFunctor.obj X) =
        Submodule.Quotient.mk ((ρ_ X).hom.hom (x ⊗ₜ[ℤ] a))
      rw [lifted_rightUnitor_hom_tmul]
      simp

private theorem torsionFreeQuotient_scalar_action_aux
    (M : ModuleCat.{u} ℤ) (a : ℤ) :
    torsionFreeQuotientFunctor.{u}.map
        (ModuleCat.ofHom (a • (LinearMap.id : M →ₗ[ℤ] M))) =
      ModuleCat.ofHom (a • (LinearMap.id :
        torsionFreeQuotientFunctor.{u}.obj M →ₗ[ℤ]
          torsionFreeQuotientFunctor.{u}.obj M)) := by
  apply ModuleCat.hom_ext
  ext x
  induction x using Submodule.Quotient.induction_on
  rfl

/-- For any monoidal structure on torsion-free quotient, conjugating the image of
each scalar endomorphism of the monoidal unit gives that same scalar endomorphism.
This expresses that the induced scalar map is the identity in every module universe. -/
@[stacks 0GP2 "part (5): induced scalar map is the identity"]
public theorem torsionFreeQuotient_scalarValue
    (h : torsionFreeQuotientFunctor.{u}.Monoidal) (a : ℤ) :
    letI : torsionFreeQuotientFunctor.{u}.Monoidal := h
    (Functor.Monoidal.εIso torsionFreeQuotientFunctor.{u}).hom ≫
      torsionFreeQuotientFunctor.{u}.map
        (a • (𝟙 (𝟙_ (ModuleCat.{u} ℤ)))) ≫
      (Functor.Monoidal.εIso torsionFreeQuotientFunctor.{u}).inv =
        a • (𝟙 (𝟙_ (ModuleCat.{u} ℤ))) := by
  let : torsionFreeQuotientFunctor.{u}.Monoidal := h
  have hact := torsionFreeQuotient_scalar_action_aux
    (M := 𝟙_ (ModuleCat.{u} ℤ)) a
  have hsmul (N : ModuleCat.{u} ℤ) :
      a • (𝟙 N) = ModuleCat.ofHom (a • (LinearMap.id : N →ₗ[ℤ] N)) := by
    apply ModuleCat.hom_ext
    ext x
    rfl
  have hact' : torsionFreeQuotientFunctor.map
      (a • (𝟙 (𝟙_ (ModuleCat.{u} ℤ)))) =
        a • (𝟙 (torsionFreeQuotientFunctor.obj (𝟙_ (ModuleCat.{u} ℤ)))) := by
    rw [hsmul, hsmul]
    exact hact
  rw [hact']
  simp

/-- Torsion-free quotient preserves multiplication by every integer on every module. -/
@[stacks 0GP2 "part (5): scalar endomorphisms on all modules"]
public theorem torsionFreeQuotient_scalar_action (M : ModuleCat.{u} ℤ) (a : ℤ) :
    torsionFreeQuotientFunctor.{u}.map
        (ModuleCat.ofHom (a • (LinearMap.id : M →ₗ[ℤ] M))) =
      ModuleCat.ofHom (a • (LinearMap.id :
        torsionFreeQuotientFunctor.{u}.obj M →ₗ[ℤ]
          torsionFreeQuotientFunctor.{u}.obj M)) :=
  torsionFreeQuotient_scalar_action_aux M a

/-- Torsion-free quotient is not naturally isomorphic to the identity functor. -/
@[stacks 0GP2 "part (5): nonidentity example"]
public theorem torsionFreeQuotient_not_iso_id :
    ¬ Nonempty (torsionFreeQuotientFunctor.{u} ≅ 𝟭 (ModuleCat.{u} ℤ)) := by
  rintro ⟨e⟩
  let M : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} (ZMod 2))
  have ht : Submodule.torsion ℤ (ULift.{u} (ZMod 2)) = ⊤ := by
    apply top_unique
    intro x hx
    rw [Submodule.mem_torsion_iff]
    refine ⟨⟨2, by norm_num⟩, ?_⟩
    simp only [Submonoid.smul_def]
    change ULift.up ((2 : ℤ) • x.down) = 0
    apply ULift.ext
    have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
    calc
      (2 : ℤ) • x.down = (2 : ZMod 2) * x.down := by
        simp [zsmul_eq_mul, Int.cast_ofNat]
      _ = 0 := by rw [htwo]; simp
  have : Subsingleton (torsionFreeQuotientFunctor.obj M) := by
    change Subsingleton ((ULift.{u} (ZMod 2)) ⧸ Submodule.torsion ℤ _)
    rwa [Submodule.Quotient.subsingleton_iff]
  let y : M := ULift.up (1 : ZMod 2)
  have h := Iso.inv_hom_id_apply (e.app M) y
  rw [show (e.app M).inv y = 0 from Subsingleton.elim _ _, map_zero] at h
  exact one_ne_zero (ULift.up_injective h.symm : (1 : ZMod 2) = 0)

private def elementHom {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (m : M) :
    ModuleCat.of R R ⟶ M :=
  ModuleCat.ofHom (LinearMap.smulRight (1 : R →ₗ[R] R) m)

private lemma elementHom_add {R : Type u} [CommRing R] (M : ModuleCat.{u} R)
    (x y : M) : elementHom M (x + y) = elementHom M x + elementHom M y :=
  ModuleCat.hom_ext (LinearMap.ext fun a => smul_add a x y)

private lemma elementHom_smul {R : Type u} [CommRing R] (M : ModuleCat.{u} R)
    (a : R) (x : M) : elementHom M (a • x) =
      ModuleCat.ofHom (LinearMap.mulLeft R a) ≫ elementHom M x := by
  ext
  simp [elementHom]

private lemma map_mulLeft_eq_scalarValue_smul (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B)
    [F.Monoidal] (a : A) :
    F.map (ModuleCat.ofHom (LinearMap.mulLeft A a)) =
      scalarValue F a • 𝟙 (F.obj (ModuleCat.of A A)) := by
  let e : ModuleCat.of B B ≅ F.obj (ModuleCat.of A A) := Functor.Monoidal.εIso F
  have hv : e.hom ≫ F.map (ModuleCat.ofHom (LinearMap.mulLeft A a)) ≫ e.inv =
      scalarValue F a • 𝟙 (ModuleCat.of B B) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change scalarValue F a = scalarValue F a * 1
    exact (mul_one _).symm
  apply (cancel_epi e.hom).mp
  apply (cancel_mono e.inv).mp
  simpa [Category.assoc] using hv

private def elementEquiv {R : Type u} [CommRing R] (M : ModuleCat.{u} R) :
    (ModuleCat.of R R ⟶ M) ≃ M :=
  ModuleCat.homEquiv.trans (LinearMap.ringLmapEquivSelf R R M).toEquiv

private noncomputable def rightAdjointElementEquiv
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.Monoidal]
    {G : ModuleCat.{u} B ⥤ ModuleCat.{u} A} (adj : F ⊣ G) (N : ModuleCat.{u} B) :
    G.obj N ≃ N :=
  (elementEquiv (G.obj N)).symm.trans ((adj.homEquiv (ModuleCat.of A A) N).symm.trans
    (((Functor.Monoidal.εIso F).symm.homCongr (Iso.refl N)).trans (elementEquiv N)))

private lemma rightAdjointElementEquiv_apply
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.Monoidal]
    {G : ModuleCat.{u} B ⥤ ModuleCat.{u} A} (adj : F ⊣ G) (N : ModuleCat.{u} B)
    (x : G.obj N) :
    rightAdjointElementEquiv F adj N x =
      ((Functor.Monoidal.εIso F).hom ≫ F.map (elementHom (G.obj N) x) ≫
        adj.counit.app N).hom 1 := by
  simp [rightAdjointElementEquiv, elementEquiv, elementHom,
    Iso.homCongr, Adjunction.homEquiv_symm_apply]
  rfl

private noncomputable def rightAdjointRestrictionIso
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.Monoidal] [F.Additive]
    {G : ModuleCat.{u} B ⥤ ModuleCat.{u} A} (adj : F ⊣ G)
    (φ : A →+* B) (hφ : ∀ a, φ a = scalarValue F a) :
    G ≅ ModuleCat.restrictScalars φ := by
  let e (N : ModuleCat.{u} B) : G.obj N ≃ₗ[A] (ModuleCat.restrictScalars φ).obj N := {
    __ := rightAdjointElementEquiv F adj N
    map_add' := by
      intro x y
      change rightAdjointElementEquiv F adj N (x + y) =
        rightAdjointElementEquiv F adj N x + rightAdjointElementEquiv F adj N y
      simp only [rightAdjointElementEquiv_apply, elementHom_add, F.map_add,
        Preadditive.comp_add, Preadditive.add_comp, ModuleCat.hom_add, LinearMap.add_apply]
    map_smul' := by
      intro a x
      change rightAdjointElementEquiv F adj N (a • x) =
        φ a • rightAdjointElementEquiv F adj N x
      rw [rightAdjointElementEquiv_apply, rightAdjointElementEquiv_apply,
        elementHom_smul, F.map_comp, map_mulLeft_eq_scalarValue_smul, hφ]
      simp [Category.assoc] }
  refine NatIso.ofComponents (fun N => (e N).toModuleIso) ?_
  intro N N' f
  apply ModuleCat.hom_ext
  ext x
  change rightAdjointElementEquiv F adj N' ((G.map f).hom x) =
    f.hom (rightAdjointElementEquiv F adj N x)
  have hx : elementHom (G.obj N') ((G.map f).hom x) =
      elementHom (G.obj N) x ≫ G.map f :=
    ModuleCat.hom_ext (LinearMap.ext fun a => ((G.map f).hom.map_smul a x).symm)
  rw [rightAdjointElementEquiv_apply, rightAdjointElementEquiv_apply, hx, F.map_comp]
  have hn := adj.counit.naturality f
  dsimp at hn
  simp only [Category.assoc, hn]
  rfl

private noncomputable def extensionIso
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.Monoidal] [F.Additive]
    {G : ModuleCat.{u} B ⥤ ModuleCat.{u} A} (adj : F ⊣ G)
    (φ : A →+* B) (hφ : ∀ a, φ a = scalarValue F a) :
    ModuleCat.extendScalars.{u, u, u} φ ≅ F :=
  (ModuleCat.extendRestrictScalarsAdj φ).leftAdjointUniq
    (adj.ofNatIsoRight (rightAdjointRestrictionIso F adj φ hφ))

private lemma extensionIso_apply_one_tmul
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.Monoidal] [F.Additive]
    {G : ModuleCat.{u} B ⥤ ModuleCat.{u} A} (adj : F ⊣ G)
    (φ : A →+* B) (hφ : ∀ a, φ a = scalarValue F a)
    (M : ModuleCat.{u} A) (m : M) :
    let := φ.toAlgebra
    ((extensionIso F adj φ hφ).hom.app M).hom ((1 : B) ⊗ₜ[A] m) =
      (F.map (elementHom M m)).hom ((Functor.Monoidal.εIso F).hom.hom 1) := by
  let := φ.toAlgebra
  have hh := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (ModuleCat.extendRestrictScalarsAdj φ)
    (adj.ofNatIsoRight (rightAdjointRestrictionIso F adj φ hφ)) M
  have hv := congrArg (fun f => f.hom m) hh
  change ((extensionIso F adj φ hφ).hom.app M).hom ((1 : B) ⊗ₜ[A] m) =
    rightAdjointElementEquiv F adj (F.obj M) ((adj.unit.app M).hom m) at hv
  rw [hv, rightAdjointElementEquiv_apply]
  have hm : elementHom (G.obj (F.obj M)) ((adj.unit.app M).hom m) =
      elementHom M m ≫ adj.unit.app M :=
    ModuleCat.hom_ext (LinearMap.ext fun a => ((adj.unit.app M).hom.map_smul a m).symm)
  rw [hm, F.map_comp, Category.assoc, adj.left_triangle_components, Category.comp_id]
  rfl

private lemma map_elementHom_tensor
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.Monoidal]
    (M N : ModuleCat.{u} A) (m : M) (n : N) :
    (F.map (elementHom (M ⊗ N) (m ⊗ₜ[A] n))).hom
        ((Functor.Monoidal.εIso F).hom.hom 1) =
      (Functor.LaxMonoidal.μ F M N).hom
        ((F.map (elementHom M m)).hom ((Functor.Monoidal.εIso F).hom.hom 1) ⊗ₜ[B]
          (F.map (elementHom N n)).hom ((Functor.Monoidal.εIso F).hom.hom 1)) := by
  have he : elementHom (M ⊗ N) (m ⊗ₜ[A] n) =
      (λ_ (ModuleCat.of A A)).inv ≫ (elementHom M m ⊗ₘ elementHom N n) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change (1 : A) • (m ⊗ₜ[A] n) = ((1 : A) • m) ⊗ₜ[A] ((1 : A) • n)
    simp
  rw [he, F.map_comp]
  have hunit := Functor.LaxMonoidal.left_unitality_inv F (ModuleCat.of A A)
  have hnat := Functor.LaxMonoidal.μ_natural F (elementHom M m) (elementHom N n)
  change (F.map (elementHom M m) ⊗ₘ F.map (elementHom N n)) ≫
    Functor.LaxMonoidal.μ F M N =
    Functor.LaxMonoidal.μ F (𝟙_ (ModuleCat.{u} A)) (ModuleCat.of A A) ≫
      F.map (elementHom M m ⊗ₘ elementHom N n) at hnat
  rw [← hunit]
  simp only [Category.assoc, ← hnat]
  rfl

private lemma extensionIso_isMonoidal
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.Monoidal] [F.Additive]
    {G : ModuleCat.{u} B ⥤ ModuleCat.{u} A} (adj : F ⊣ G)
    (φ : A →+* B) (hφ : ∀ a, φ a = scalarValue F a) :
    NatTrans.IsMonoidal (extensionIso F adj φ hφ).hom := by
  let := φ.toAlgebra
  constructor
  · apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change ((extensionIso F adj φ hφ).hom.app (ModuleCat.of A A)).hom
      ((1 : B) ⊗ₜ[A] (1 : A)) = (Functor.Monoidal.εIso F).hom.hom 1
    rw [extensionIso_apply_one_tmul]
    have he : elementHom (ModuleCat.of A A) (1 : A) = 𝟙 _ :=
      ModuleCat.hom_ext (LinearMap.ext fun a => mul_one a)
    rw [he, F.map_id]
    rfl
  · intro M N
    apply (cancel_epi (Functor.Monoidal.μIso (ModuleCat.extendScalars φ) M N).inv).mp
    simp only [← Category.assoc, ← Functor.Monoidal.μIso_hom, Iso.inv_hom_id,
      Category.id_comp]
    apply ModuleCat.ExtendScalars.hom_ext
    intro z
    change ((extensionIso F adj φ hφ).hom.app (M ⊗ N)).hom ((1 : B) ⊗ₜ[A] z) =
      ((Functor.Monoidal.μIso (ModuleCat.extendScalars φ) M N).inv ≫
        ((extensionIso F adj φ hφ).hom.app M ⊗ₘ (extensionIso F adj φ hφ).hom.app N) ≫
        Functor.LaxMonoidal.μ F M N).hom ((1 : B) ⊗ₜ[A] z)
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
      refine (congrArg _ (TensorProduct.tmul_add _ x y)).trans ?_
      refine (map_add _ _ _).trans ?_
      refine (congrArg₂ (· + ·) hx hy).trans ?_
      refine (map_add _ _ _).symm.trans ?_
      exact congrArg _ (TensorProduct.tmul_add _ x y).symm
    | tmul m n =>
      change ((extensionIso F adj φ hφ).hom.app (M ⊗ N)).hom
        ((1 : B) ⊗ₜ[A] (m ⊗ₜ[A] n)) =
        (Functor.LaxMonoidal.μ F M N).hom
          (((extensionIso F adj φ hφ).hom.app M).hom ((1 : B) ⊗ₜ[A] m) ⊗ₜ[B]
            ((extensionIso F adj φ hφ).hom.app N).hom ((1 : B) ⊗ₜ[A] n))
      simp only [extensionIso_apply_one_tmul]
      exact map_elementHom_tensor F M N m n

/-- A right-exact monoidal functor commuting with direct sums is extension of
scalars along its induced ring map, compatibly with the monoidal structures. -/
@[stacks 0GP2 "part (6): extension of scalars"]
public theorem iso_extendScalars_of_rightExact_preservesDirectSums
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.Monoidal]
    [PreservesFiniteColimits F]
    (hF : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) F) :
    ∃ φ : A →+* B,
      (∀ a, φ a = scalarValue F a) ∧
        ∃ i : F ≅ ModuleCat.extendScalars φ,
          NatTrans.IsMonoidal i.hom := by
  have hcol : PreservesFiniteColimits F ∧
      ∀ J : Type u, PreservesColimitsOfShape (Discrete J) F := ⟨inferInstance, hF⟩
  have hleft : F.IsLeftAdjoint :=
    ((tfae_iso_tensorFunctor_preserves_colimits_isLeftAdjoint A B F).out 2 4).mp
      hcol
  let : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  let : F.Additive := F.additive_of_preservesBinaryBiproducts
  obtain ⟨G, ⟨adj⟩⟩ := hleft
  let φ := (ringHomOfAdditive F).1
  have hφ : ∀ a, φ a = scalarValue F a := (ringHomOfAdditive F).2
  let e := extensionIso F adj φ hφ
  have : NatTrans.IsMonoidal e.hom := extensionIso_isMonoidal F adj φ hφ
  refine ⟨φ, hφ, e.symm, ?_⟩
  change NatTrans.IsMonoidal e.inv
  infer_instance

private lemma extendScalars_map_smul_id (φ : A →+* B)
    (M : ModuleCat.{u} A) (a : A) :
    (ModuleCat.extendScalars φ).map (a • 𝟙 M) =
      φ a • 𝟙 ((ModuleCat.extendScalars φ).obj M) := by
  let := φ.toAlgebra
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (1 : B) ⊗ₜ[A] (a • m) = φ a • ((1 : B) ⊗ₜ[A] m)
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  rfl

/-- Ring maps are uniquely determined by the corresponding monoidal extension-of-scalars
functors, up to natural isomorphism. -/
@[stacks 0GP2 "classification: uniqueness"]
public theorem extendScalars_injective_up_to_iso (φ ψ : A →+* B)
    (h : Nonempty (ModuleCat.extendScalars.{u, u, u} φ ≅
      ModuleCat.extendScalars.{u, u, u} ψ)) :
    φ = ψ := by
  obtain ⟨i⟩ := h
  ext a
  have ha := i.hom.naturality (a • 𝟙 (ModuleCat.of A A))
  rw [extendScalars_map_smul_id, extendScalars_map_smul_id] at ha
  have hscalar : φ a • 𝟙 ((ModuleCat.extendScalars ψ).obj (ModuleCat.of A A)) =
      ψ a • 𝟙 ((ModuleCat.extendScalars ψ).obj (ModuleCat.of A A)) := by
    apply (cancel_epi (i.hom.app (ModuleCat.of A A))).mp
    simpa using ha
  let e : ModuleCat.of B B ≅ (ModuleCat.extendScalars ψ).obj (ModuleCat.of A A) :=
    Functor.Monoidal.εIso (ModuleCat.extendScalars.{u, u, u} ψ)
  have he := congrArg (fun f => e.hom ≫ f ≫ e.inv) hscalar
  have he' : φ a • 𝟙 (ModuleCat.of B B) = ψ a • 𝟙 (ModuleCat.of B B) := by
    simpa only [Linear.comp_smul, Linear.smul_comp, Category.id_comp,
      Iso.hom_inv_id] using he
  simpa using congrArg (fun f => f.hom (1 : B)) he'

/-- Every ring map gives a cocontinuous monoidal extension-of-scalars functor. -/
@[stacks 0GP2 "classification: existence"]
public theorem extendScalars_monoidal_preservesColimits (φ : A →+* B) :
    Nonempty (ModuleCat.extendScalars.{u, u, u} φ).Monoidal ∧
      PreservesColimits (ModuleCat.extendScalars.{u, u, u} φ) :=
  ⟨⟨inferInstance⟩, (ModuleCat.extendRestrictScalarsAdj φ).leftAdjoint_preservesColimits⟩

end ModuleCat
