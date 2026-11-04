module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChangePlainComparison
public import StacksFrontier.Algebra.DifferentialGraded.TensorProductLift
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorTriangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorPureSpan

/-!
# Extension of scalars preserves orthogonality to the acyclic modules

Let `ψ : A → B` be a homomorphism of differential graded algebras over a commutative ring `R`.
Extension of scalars `- ⊗_A B : K(A, d) ⥤ K(B, d)` is left adjoint to restriction of scalars on
the homotopy categories (Tags 09LN and 0BYX), and restriction of scalars carries acyclic modules
to acyclic modules, the underlying complex being unchanged. Consequently extension of scalars
carries a module orthogonal on the left to the acyclic modules (a K-projective module) to one.

## Main definitions

* `DifferentialGraded.Bimodule.tensorHomotopyAdjRestrict`: the adjunction
  `- ⊗_A B ⊣ res_ψ` on the homotopy categories.

## Main results

* `DifferentialGradedModule.acyclic'_restrictScalarsHomotopyFunctor_obj`: restriction of scalars
  preserves acyclicity.
* `DifferentialGraded.Bimodule.leftOrthogonal_tensorHomotopyFunctor_obj` and
  `leftOrthogonal_tensorCompFunctor_obj`: **extension of scalars preserves orthogonality on the
  left to the acyclic modules.**
* `DifferentialGraded.Bimodule.tensorRegularAdj_unit_apply`: the unit of extension of scalars is
  `x ↦ x ⊗ 1`.
* `DifferentialGraded.Bimodule.compIso`: **extension of scalars along a composite is the composite
  of the extensions**, `X ⊗_A C ≅ (X ⊗_A B) ⊗_B C`, `x ⊗ c ↦ (x ⊗ 1) ⊗ c`.

## References

* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX)
* [Stacks Project, Tag 09LN](https://stacks.math.columbia.edu/tag/09LN)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

/-- **Restriction of scalars preserves acyclicity**: it does not change the underlying
complex. -/
theorem acyclic'_restrictScalarsHomotopyFunctor_obj (ψ : A.Hom B) {Y : HomotopyCategory B}
    (hY : acyclic' B Y) : acyclic' A ((restrictScalarsHomotopyFunctor ψ).obj Y) :=
  hY

end DifferentialGradedModule

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

/-- **Extension of scalars is left adjoint to restriction of scalars on the homotopy
categories**: tensoring with the regular bimodule is left adjoint to the internal hom out of it
(Tag 09LN), which is restriction of scalars (Tag 0BYX). -/
def tensorHomotopyAdjRestrict (ψ : A.Hom B) :
    tensorHomotopyFunctor (regular ψ) ⊣ restrictScalarsHomotopyFunctor ψ :=
  (tensorHomotopyFunctor_adj_homHomotopyCategoryFunctor (regular ψ)).ofNatIsoRight
    (homHomotopyFunctorRegularIso ψ)

/-- **Extension of scalars carries a module orthogonal on the left to the acyclic modules to one**,
on the homotopy categories. -/
theorem leftOrthogonal_tensorHomotopyFunctor_obj (ψ : A.Hom B) {X : HomotopyCategory A}
    (hX : (acyclic' A).leftOrthogonal X) :
    (acyclic' B).leftOrthogonal ((tensorHomotopyFunctor (regular ψ)).obj X) := by
  intro Y f hY
  have h0 : (tensorHomotopyAdjRestrict ψ).homEquiv X Y f = 0 :=
    hX _ (acyclic'_restrictScalarsHomotopyFunctor_obj ψ hY)
  have hf : f = ((tensorHomotopyAdjRestrict ψ).homEquiv X Y).symm 0 := by
    rw [← h0, Equiv.symm_apply_apply]
  have : (tensorHomotopyFunctor (regular ψ)).IsLeftAdjoint :=
    (tensorHomotopyAdjRestrict ψ).isLeftAdjoint
  rw [hf, Adjunction.homEquiv_counit, Functor.map_zero, Limits.zero_comp]

/-- **Extension of scalars carries a module orthogonal on the left to the acyclic modules to
one.** -/
theorem leftOrthogonal_tensorCompFunctor_obj (ψ : A.Hom B) {X : DifferentialGradedModule A}
    (hX : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj X)) :
    (acyclic' B).leftOrthogonal
      ((toHomotopyCategory B).obj ((tensorCompFunctor (regular ψ)).obj X)) :=
  (acyclic' B).leftOrthogonal.prop_of_iso ((tensorCompFunctor_quotient (regular ψ)).app X).symm
    (leftOrthogonal_tensorHomotopyFunctor_obj ψ hX)

/-! ### The unit of extension of scalars -/

/-- Two `R`-linear maps out of a graded module agree if they agree on homogeneous elements. -/
private theorem linearMap_ext_of_homogeneous {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (𝒜 : ℤ → Submodule R M) [DirectSum.Decomposition 𝒜]
    {f g : M →ₗ[R] N} (h : ∀ (p : ℤ) (x : 𝒜 p), f x = g x) : f = g :=
  DirectSum.decompose_lhom_ext 𝒜 fun p => LinearMap.ext (h p)

/-- **The unit of extension of scalars is `x ↦ x ⊗ 1`.** -/
theorem tensorRegularAdj_unit_apply (ψ : A.Hom B) (X : DifferentialGradedModule.{u, u, u} A)
    (x : X.M) :
    ((tensorRegularAdjRestrictScalars ψ).unit.app X).toFun x =
      (tensorPure (regular ψ) X).toLinearMap x (1 : B.A) := by
  have h0 : (tensorRegularAdjRestrictScalars ψ).homEquiv X _ (𝟙 _) =
      (tensorRegularAdjRestrictScalars ψ).unit.app X := by
    rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  have h1 : plainTranspose ψ ((tensorRegularAdjRestrictScalars ψ).unit.app X) = 𝟙 _ := by
    rw [plainTranspose, ← h0]
    exact Equiv.symm_apply_apply _ _
  refine LinearMap.congr_fun (linearMap_ext_of_homogeneous X.grading
    (f := ((tensorRegularAdjRestrictScalars ψ).unit.app X).toFun.restrictScalars R)
    (g := (tensorPure (regular ψ) X).toLinearMap.flip (1 : B.A)) fun p x => ?_) x
  have h2 := plainTranspose_pure ψ ((tensorRegularAdjRestrictScalars ψ).unit.app X) p x 1
  rw [h1, MulOpposite.op_one] at h2
  exact (h2.trans (one_smul _ _)).symm

/-! ### Extension of scalars along a composite -/

/-- The unit `x ↦ x ⊗ 1` of extension of scalars, with its target read as a restriction of
scalars. -/
def unitHom (ψ : A.Hom B) (X : DifferentialGradedModule.{u, u, u} A) :
    X ⟶ (restrictScalarsFunctor ψ).obj ((tensorCompFunctor (regular ψ)).obj X) :=
  (tensorRegularAdjRestrictScalars ψ).unit.app X

/-- The unit `unitHom ψ X` sends `x` to `x ⊗ 1`. -/
theorem unitHom_apply (ψ : A.Hom B) (X : DifferentialGradedModule.{u, u, u} A) (x : X.M) :
    (unitHom ψ X).toFun x = (tensorPure (regular ψ) X).toLinearMap x (1 : B.A) :=
  tensorRegularAdj_unit_apply ψ X x

/-- Restriction of scalars along two homomorphisms which agree: the identity. -/
def restrictScalarsCongr {ψ ψ' : A.Hom B} (h : ∀ a, ψ.toAlgebraHom a = ψ'.toAlgebraHom a)
    (N : DifferentialGradedModule.{u, u, u} B) :
    (restrictScalarsFunctor ψ).obj N ⟶ (restrictScalarsFunctor ψ').obj N where
  toFun := LinearMap.id
  map_smul x a :=
    congrArg (fun b : B.A => (MulOpposite.op b • (show N.M from x) : N.M)) (h a)
  map_grading _ _ hx := hx
  map_d := rfl

section Composite

variable {C : DifferentialGradedAlgebra.{u, u} R} (ψ₁ : A.Hom B) (ψ₂ : B.Hom C) (κ : A.Hom C)
  (h : ∀ a, ψ₂.toAlgebraHom (ψ₁.toAlgebraHom a) = κ.toAlgebraHom a)
  (X : DifferentialGradedModule.{u, u, u} A)

/-- The map `x ↦ (x ⊗ 1) ⊗ 1`, a homomorphism of differential graded `A`-modules into
`(X ⊗_A B) ⊗_B C` read over `A` through `κ = ψ₂ ∘ ψ₁`. -/
def compForwardUnit :
    X ⟶ (restrictScalarsFunctor κ).obj ((tensorCompFunctor (regular ψ₂)).obj
      ((tensorCompFunctor (regular ψ₁)).obj X)) :=
  unitHom ψ₁ X ≫ (restrictScalarsFunctor ψ₁).map (unitHom ψ₂ _) ≫
    restrictScalarsCongr (ψ := ψ₂.comp ψ₁) h _

/-- The map `compForwardUnit` sends `x` to `(x ⊗ 1) ⊗ 1`. -/
theorem compForwardUnit_apply (x : X.M) :
    (compForwardUnit ψ₁ ψ₂ κ h X).toFun x =
      (tensorPure (regular ψ₂) ((tensorCompFunctor (regular ψ₁)).obj X)).toLinearMap
        ((tensorPure (regular ψ₁) X).toLinearMap x (1 : B.A)) (1 : C.A) := by
  show (unitHom ψ₂ _).toFun ((unitHom ψ₁ X).toFun x) = _
  exact (congrArg (unitHom ψ₂ _).toFun (unitHom_apply ψ₁ X x)).trans (unitHom_apply ψ₂ _ _)

/-- **The comparison `X ⊗_A C ⟶ (X ⊗_A B) ⊗_B C`**, `x ⊗ c ↦ (x ⊗ 1) ⊗ c`. -/
def compForward :
    (tensorCompFunctor (regular κ)).obj X ⟶
      (tensorCompFunctor (regular ψ₂)).obj ((tensorCompFunctor (regular ψ₁)).obj X) :=
  plainTranspose κ (compForwardUnit ψ₁ ψ₂ κ h X)

/-- The comparison `compForward` sends `x ⊗ c` to `(x ⊗ 1) ⊗ c` for homogeneous `x`. -/
theorem compForward_pure (p : ℤ) (x : X.grading p) (c : C.A) :
    (compForward ψ₁ ψ₂ κ h X).toFun ((tensorPure (regular κ) X).toLinearMap (x : X.M) c) =
      (tensorPure (regular ψ₂) ((tensorCompFunctor (regular ψ₁)).obj X)).toLinearMap
        ((tensorPure (regular ψ₁) X).toLinearMap (x : X.M) (1 : B.A)) c := by
  rw [compForward, plainTranspose_pure, compForwardUnit_apply]
  refine (((tensorDGFunctor (regular ψ₂)).pure _).map_right _ _ c).symm.trans ?_
  exact congrArg _ (one_mul c)

/-- The map `x ↦ x ⊗ 1` into `X ⊗_A C`, read over `A` through `ψ₁` and then `ψ₂`. -/
def compBackwardUnit :
    X ⟶ (restrictScalarsFunctor ψ₁).obj
      ((restrictScalarsFunctor ψ₂).obj ((tensorCompFunctor (regular κ)).obj X)) :=
  unitHom κ X ≫ restrictScalarsCongr (ψ' := ψ₂.comp ψ₁) (fun a => (h a).symm) _

/-- The map `x ⊗ b ↦ x ⊗ ψ₂(b)` from `X ⊗_A B` to `X ⊗_A C` read over `B`. -/
def compBackwardInner :
    (tensorCompFunctor (regular ψ₁)).obj X ⟶
      (restrictScalarsFunctor ψ₂).obj ((tensorCompFunctor (regular κ)).obj X) :=
  plainTranspose ψ₁ (compBackwardUnit ψ₁ ψ₂ κ h X)

/-- **The comparison `(X ⊗_A B) ⊗_B C ⟶ X ⊗_A C`**, `(x ⊗ b) ⊗ c ↦ x ⊗ ψ₂(b) c`. -/
def compBackward :
    (tensorCompFunctor (regular ψ₂)).obj ((tensorCompFunctor (regular ψ₁)).obj X) ⟶
      (tensorCompFunctor (regular κ)).obj X :=
  plainTranspose ψ₂ (compBackwardInner ψ₁ ψ₂ κ h X)

/-- The map `compBackwardInner` sends `x ⊗ b` to `x ⊗ ψ₂(b)` for homogeneous `x`. -/
theorem compBackwardInner_pure (p : ℤ) (x : X.grading p) (b : B.A) :
    (compBackwardInner ψ₁ ψ₂ κ h X).toFun ((tensorPure (regular ψ₁) X).toLinearMap (x : X.M) b) =
      (tensorPure (regular κ) X).toLinearMap (x : X.M) (ψ₂.toAlgebraHom b) := by
  have hu : (compBackwardUnit ψ₁ ψ₂ κ h X).toFun (x : X.M) =
      (tensorPure (regular κ) X).toLinearMap (x : X.M) (1 : C.A) := unitHom_apply κ X x
  rw [compBackwardInner, plainTranspose_pure, hu]
  exact (((tensorDGFunctor (regular κ)).pure X).map_right _ _ _).symm.trans
    (congrArg _ (one_mul (ψ₂.toAlgebraHom b)))

/-- The comparison `compBackward` sends `(x ⊗ b) ⊗ c` to `x ⊗ ψ₂(b) c` for homogeneous `x` and
`b`. -/
theorem compBackward_pure (p q : ℤ) (x : X.grading p) (b : B.grading q) (c : C.A) :
    (compBackward ψ₁ ψ₂ κ h X).toFun
        ((tensorPure (regular ψ₂) ((tensorCompFunctor (regular ψ₁)).obj X)).toLinearMap
          ((tensorPure (regular ψ₁) X).toLinearMap (x : X.M) (b : B.A)) c) =
      (tensorPure (regular κ) X).toLinearMap (x : X.M) (ψ₂.toAlgebraHom b * c) := by
  have hz := ((tensorDGFunctor (regular ψ₁)).pure X).map_grading p q x b
  refine (plainTranspose_pure ψ₂ (compBackwardInner ψ₁ ψ₂ κ h X) (p + q) ⟨_, hz⟩ c).trans ?_
  rw [compBackwardInner_pure]
  exact (((tensorDGFunctor (regular κ)).pure X).map_right _ _ _).symm

/-- For `c : C`, `ψ₂(1) * c = c`. -/
theorem map_one_mul (c : C.A) : ψ₂.toAlgebraHom 1 * c = c := by
  rw [map_one, one_mul]

/-- The composite `compForward ≫ compBackward` is the identity of `X ⊗_A C`. -/
theorem compForward_compBackward :
    compForward ψ₁ ψ₂ κ h X ≫ compBackward ψ₁ ψ₂ κ h X = 𝟙 _ := by
  refine tensorObj_hom_ext' (regular κ) X _ _ fun x c => ?_
  induction x using DirectSum.Decomposition.inductionOn X.grading with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | @homogeneous p x =>
      exact (congrArg (compBackward ψ₁ ψ₂ κ h X).toFun (compForward_pure ψ₁ ψ₂ κ h X p x c)).trans
        ((compBackward_pure ψ₁ ψ₂ κ h X p 0 x ⟨1, SetLike.one_mem_graded B.grading⟩ c).trans
          (congrArg (((tensorDGFunctor (regular κ)).pure X).toLinearMap (x : X.M))
            (map_one_mul ψ₂ c)))

/-- The composite `compBackward ≫ compForward` fixes `(x ⊗ b) ⊗ c` for homogeneous `x` and `b`.
-/
private theorem compForward_compBackward_pure_tmul (p q : ℤ) (x : X.grading p) (b : B.grading q)
    (c : C.A) :
    (compForward ψ₁ ψ₂ κ h X).toFun ((compBackward ψ₁ ψ₂ κ h X).toFun
      ((tensorPure (regular ψ₂) ((tensorCompFunctor (regular ψ₁)).obj X)).toLinearMap
        ((tensorPure (regular ψ₁) X).toLinearMap (x : X.M) (b : B.A)) c)) =
      (tensorPure (regular ψ₂) ((tensorCompFunctor (regular ψ₁)).obj X)).toLinearMap
        ((tensorPure (regular ψ₁) X).toLinearMap (x : X.M) (b : B.A)) c := by
  rw [compBackward_pure, compForward_pure]
  let P₁ := (tensorPure (regular ψ₁) X).toLinearMap
  let P₂ := (tensorPure (regular ψ₂) ((tensorCompFunctor (regular ψ₁)).obj X)).toLinearMap
  have hz := ((tensorDGFunctor (regular ψ₁)).pure X).map_grading p 0 x
    ⟨(1 : B.A), SetLike.one_mem_graded B.grading⟩
  have hr : P₁ (x : X.M) (b : B.A) = MulOpposite.op (b : B.A) • P₁ (x : X.M) (1 : B.A) :=
    (congrArg (P₁ (x : X.M)) (one_mul (b : B.A)).symm).trans
      (((tensorDGFunctor (regular ψ₁)).pure X).map_right (x : X.M) (1 : B.A) b)
  refine LinearMap.congr_fun (linearMap_ext_of_homogeneous C.grading
    (f := P₂ (P₁ (x : X.M) (1 : B.A)) ∘ₗ LinearMap.mulLeft R (ψ₂.toAlgebraHom (b : B.A)))
    (g := P₂ (P₁ (x : X.M) (b : B.A))) fun r c => ?_) c
  have hbal := ((tensorDGFunctor (regular ψ₂)).pure _).balance (p + 0) r q ⟨_, hz⟩ c b
  have hact := regularBimoduleStructure_action ψ₂ q r b c
  refine (congrArg (P₂ (P₁ (x : X.M) (1 : B.A))) hact.symm).trans (hbal.symm.trans ?_)
  exact congrArg (fun w => P₂ w (c : C.A)) hr.symm

/-- The composite `compBackward ≫ compForward` fixes every pure tensor `z ⊗ c` of
`(X ⊗_A B) ⊗_B C`. -/
theorem compBackward_compForward_pure (z : ((tensorCompFunctor (regular ψ₁)).obj X).M)
    (c : C.A) :
    (compForward ψ₁ ψ₂ κ h X).toFun ((compBackward ψ₁ ψ₂ κ h X).toFun
      ((tensorPure (regular ψ₂) ((tensorCompFunctor (regular ψ₁)).obj X)).toLinearMap z c)) =
    (tensorPure (regular ψ₂) ((tensorCompFunctor (regular ψ₁)).obj X)).toLinearMap z c := by
  let L1 : ((tensorCompFunctor (regular ψ₁)).obj X).M →ₗ[R]
      ((tensorCompFunctor (regular ψ₂)).obj ((tensorCompFunctor (regular ψ₁)).obj X)).M :=
    (compForward ψ₁ ψ₂ κ h X).toFun ∘ₗ (compBackward ψ₁ ψ₂ κ h X).toFun ∘ₗ
      ((tensorPure (regular ψ₂) ((tensorCompFunctor (regular ψ₁)).obj X)).toLinearMap.flip c)
  let L2 : ((tensorCompFunctor (regular ψ₁)).obj X).M →ₗ[R]
      ((tensorCompFunctor (regular ψ₂)).obj ((tensorCompFunctor (regular ψ₁)).obj X)).M :=
    (tensorPure (regular ψ₂) ((tensorCompFunctor (regular ψ₁)).obj X)).toLinearMap.flip c
  have key : L1 = L2 := by
    refine tensorObj_linearMap_ext (regular ψ₁) X L1 L2 fun x b => ?_
    let P₁ := (tensorPure (regular ψ₁) X).toLinearMap
    refine LinearMap.congr_fun (linearMap_ext_of_homogeneous X.grading
      (f := L1 ∘ₗ P₁.flip b) (g := L2 ∘ₗ P₁.flip b) fun p x => ?_) x
    refine LinearMap.congr_fun (linearMap_ext_of_homogeneous B.grading
      (f := L1 ∘ₗ P₁ x) (g := L2 ∘ₗ P₁ x) fun q b => ?_) b
    exact compForward_compBackward_pure_tmul ψ₁ ψ₂ κ h X p q x b c
  exact LinearMap.congr_fun key z

/-- The composite `compBackward ≫ compForward` is the identity of `(X ⊗_A B) ⊗_B C`. -/
theorem compBackward_compForward :
    compBackward ψ₁ ψ₂ κ h X ≫ compForward ψ₁ ψ₂ κ h X = 𝟙 _ :=
  tensorObj_hom_ext' (regular ψ₂) _ _ _ fun z c => compBackward_compForward_pure ψ₁ ψ₂ κ h X z c

/-- **Extension of scalars along a composite is the composite of the extensions**:
`X ⊗_A C ≅ (X ⊗_A B) ⊗_B C` for `κ = ψ₂ ∘ ψ₁`, `x ⊗ c ↦ (x ⊗ 1) ⊗ c`. -/
def compIso :
    (tensorCompFunctor (regular κ)).obj X ≅
      (tensorCompFunctor (regular ψ₂)).obj ((tensorCompFunctor (regular ψ₁)).obj X) where
  hom := compForward ψ₁ ψ₂ κ h X
  inv := compBackward ψ₁ ψ₂ κ h X
  hom_inv_id := compForward_compBackward ψ₁ ψ₂ κ h X
  inv_hom_id := compBackward_compForward ψ₁ ψ₂ κ h X

end Composite

end DifferentialGraded.Bimodule

end
