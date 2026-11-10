module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChangeLeftOrthogonal
public import StacksFrontier.Algebra.DifferentialGraded.TensorProductLift
public import StacksFrontier.RingTheory.Koszul.PowBaseTensorBalanceLadder

/-!
# Base change along a commutative square of differential graded algebras

Let
```
B₁ --ψ₁--> C₁
|θ         |χ
v          v
B₂ --ψ₂--> C₂
```
be a commutative square of homomorphisms of differential graded algebras over a commutative ring
`R`, let `X₁` be a right differential graded `B₁`-module, `X₂` a right differential graded
`B₂`-module and `g : X₁ ⟶ (X₂)_{B₁}` a homomorphism of differential graded `B₁`-modules, the
target being read through `θ`. Then `x ⊗ c ↦ g(x) ⊗ χ(c)` is a homomorphism
`X₁ ⊗_{B₁} C₁ ⟶ (X₂ ⊗_{B₂} C₂)_{C₁}` of differential graded `C₁`-modules. This is the base change
of `g` along the square; it is functorial in the square.

## Main definitions

* `DifferentialGraded.Bimodule.tensorSquareMap`: the base change of `g` along the square.

## Main results

* `DifferentialGraded.Bimodule.tensorSquareMap_pure`: on a pure tensor it is
  `x ⊗ c ↦ g(x) ⊗ χ(c)`.
* `DifferentialGraded.Bimodule.tensorSquareMap_comp_apply`: base change along a composite of
  squares is the composite of the base changes.
* `DifferentialGraded.Bimodule.tensorSquareMap_id_apply`: base change along the identity square is
  the identity.
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedModule

universe u

namespace DifferentialGradedAlgebra.Hom

variable {R : Type u} [CommRing R]

/-- The identity homomorphism of differential graded algebras acts as the identity. -/
@[simp] theorem id_toAlgebraHom_apply (A : DifferentialGradedAlgebra.{u, u} R) (a : A.A) :
    (Hom.id A).toAlgebraHom a = a := rfl

end DifferentialGradedAlgebra.Hom

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}

/-- Restriction of scalars along the identity, read as the module itself. -/
def restrictScalarsIdHom (M : DifferentialGradedModule.{u, u, u} A) :
    (restrictScalarsFunctor (DifferentialGradedAlgebra.Hom.id A)).obj M ⟶ M where
  toFun := LinearMap.id
  map_smul _ _ := rfl
  map_grading _ _ hx := hx
  map_d := rfl

/-- A module, read as its restriction of scalars along the identity. -/
def restrictScalarsIdInv (M : DifferentialGradedModule.{u, u, u} A) :
    M ⟶ (restrictScalarsFunctor (DifferentialGradedAlgebra.Hom.id A)).obj M where
  toFun := LinearMap.id
  map_smul _ _ := rfl
  map_grading _ _ hx := hx
  map_d := rfl

section Square

variable {B₁ B₂ C₁ C₂ : DifferentialGradedAlgebra.{u, u} R} (ψ₁ : B₁.Hom C₁) (ψ₂ : B₂.Hom C₂)
  (θ : B₁.Hom B₂) (χ : C₁.Hom C₂)
  (h : ∀ b, χ.toAlgebraHom (ψ₁.toAlgebraHom b) = ψ₂.toAlgebraHom (θ.toAlgebraHom b))
  {N₁ : DifferentialGradedModule.{u, u, u} C₁} {N₂ : DifferentialGradedModule.{u, u, u} C₂}

include h in
/-- **A homomorphism read through a commutative square of restrictions of scalars**: a
homomorphism `N₁ ⟶ (N₂)_{C₁}` is also one `(N₁)_{B₁} ⟶ ((N₂)_{B₂})_{B₁}` when
`χ ∘ ψ₁ = ψ₂ ∘ θ`; the underlying map is the same. -/
def restrictScalarsAlongSquare (g : N₁ ⟶ restrictScalars χ N₂) :
    restrictScalars ψ₁ N₁ ⟶ restrictScalars θ (restrictScalars ψ₂ N₂) where
  toFun := g.toFun
  map_smul x b := (g.map_smul x (ψ₁.toAlgebraHom b)).trans
    (congrArg (fun c => (MulOpposite.op c • (show N₂.M from g.toFun x) : N₂.M)) (h b))
  map_grading := g.map_grading
  map_d := g.map_d

/-- The underlying map of `restrictScalarsAlongSquare ψ₁ ψ₂ θ χ h g` is that of `g`. -/
@[simp] theorem restrictScalarsAlongSquare_toFun (g : N₁ ⟶ restrictScalars χ N₂) :
    (restrictScalarsAlongSquare ψ₁ ψ₂ θ χ h g).toFun = g.toFun := rfl

/-- `restrictScalarsAlongSquare ψ₁ ψ₂ θ χ h g` sends `x` to `g x`. -/
theorem restrictScalarsAlongSquare_apply (g : N₁ ⟶ restrictScalars χ N₂) (x : N₁.M) :
    (restrictScalarsAlongSquare ψ₁ ψ₂ θ χ h g).toFun x = g.toFun x := rfl

end Square

section Trans

variable {B C₁ C₂ : DifferentialGradedAlgebra.{u, u} R} (ψ : B.Hom C₁) (χ : C₁.Hom C₂)
  (κ : B.Hom C₂) (h : ∀ b, χ.toAlgebraHom (ψ.toAlgebraHom b) = κ.toAlgebraHom b)
  {N₁ : DifferentialGradedModule.{u, u, u} C₁} {N₂ : DifferentialGradedModule.{u, u, u} C₂}

include h in
/-- **A homomorphism read through a composite of restrictions of scalars**: a homomorphism
`N₁ ⟶ (N₂)_{C₁}` is also one `(N₁)_B ⟶ (N₂)_B` when `κ = χ ∘ ψ`; the underlying map is the
same. -/
def restrictScalarsTransHom (g : N₁ ⟶ restrictScalars χ N₂) :
    restrictScalars ψ N₁ ⟶ restrictScalars κ N₂ where
  toFun := g.toFun
  map_smul x b := (g.map_smul x (ψ.toAlgebraHom b)).trans
    (congrArg (fun c => (MulOpposite.op c • (show N₂.M from g.toFun x) : N₂.M)) (h b))
  map_grading := g.map_grading
  map_d := g.map_d

/-- `restrictScalarsTransHom ψ χ κ h g` sends `x` to `g x`. -/
theorem restrictScalarsTransHom_apply (g : N₁ ⟶ restrictScalars χ N₂)
    (x : (restrictScalars ψ N₁).M) :
    (restrictScalarsTransHom ψ χ κ h g).toFun x = g.toFun x := rfl

end Trans

section TransLaws

variable {B B₁ C₁ C₂ C₃ D : DifferentialGradedAlgebra.{u, u} R}

/-- Composing a homomorphism read through a composite of restrictions with a further
homomorphism. -/
theorem restrictScalarsTransHom_comp_apply (ψ : B.Hom C₁) (χ₁ : C₁.Hom C₂) (κ₁ : B.Hom C₂)
    (h₁ : ∀ b, χ₁.toAlgebraHom (ψ.toAlgebraHom b) = κ₁.toAlgebraHom b) (χ₂ : C₁.Hom C₃)
    (κ₂ : B.Hom C₃) (h₂ : ∀ b, χ₂.toAlgebraHom (ψ.toAlgebraHom b) = κ₂.toAlgebraHom b)
    (χ' : C₂.Hom C₃) {N : DifferentialGradedModule.{u, u, u} C₁}
    {P : DifferentialGradedModule.{u, u, u} C₂} {P' : DifferentialGradedModule.{u, u, u} C₃}
    (ρ : P ⟶ restrictScalars χ' P') (g₁ : N ⟶ restrictScalars χ₁ P)
    (g₂ : N ⟶ restrictScalars χ₂ P') (hg : ∀ y, ρ.toFun (g₁.toFun y) = g₂.toFun y)
    (z : (restrictScalars ψ N).M) :
    ρ.toFun ((restrictScalarsTransHom ψ χ₁ κ₁ h₁ g₁).toFun z) =
      (restrictScalarsTransHom ψ χ₂ κ₂ h₂ g₂).toFun z :=
  hg z

/-- A homomorphism read through a composite of restrictions, after one read through a square. -/
theorem restrictScalarsTransHom_squareHom_apply (ψ₁ : B₁.Hom C₁) (ψ₂ : B.Hom C₂)
    (θ : B₁.Hom B) (χ : C₁.Hom C₂)
    (h : ∀ b, χ.toAlgebraHom (ψ₁.toAlgebraHom b) = ψ₂.toAlgebraHom (θ.toAlgebraHom b))
    (χ₂ : C₂.Hom D) (κ₂ : B.Hom D)
    (h₂ : ∀ b, χ₂.toAlgebraHom (ψ₂.toAlgebraHom b) = κ₂.toAlgebraHom b)
    (χ₁ : C₁.Hom D) (κ₁ : B₁.Hom D)
    (h₁ : ∀ b, χ₁.toAlgebraHom (ψ₁.toAlgebraHom b) = κ₁.toAlgebraHom b)
    {N₁ : DifferentialGradedModule.{u, u, u} C₁} {N₂ : DifferentialGradedModule.{u, u, u} C₂}
    {P : DifferentialGradedModule.{u, u, u} D} (g : N₁ ⟶ restrictScalars χ N₂)
    (g₂ : N₂ ⟶ restrictScalars χ₂ P) (g₁ : N₁ ⟶ restrictScalars χ₁ P)
    (hg : ∀ y, g₂.toFun (g.toFun y) = g₁.toFun y) (x : (restrictScalars ψ₁ N₁).M) :
    (restrictScalarsTransHom ψ₂ χ₂ κ₂ h₂ g₂).toFun
        ((restrictScalarsAlongSquare ψ₁ ψ₂ θ χ h g).toFun x) =
      (restrictScalarsTransHom ψ₁ χ₁ κ₁ h₁ g₁).toFun x :=
  hg x

end TransLaws

section SquareLaws

variable {B₁ B₂ B₃ C₁ C₂ C₃ : DifferentialGradedAlgebra.{u, u} R}

/-- **The identity law for homomorphisms read through squares of restrictions**: if `g` is the
identity pointwise, so is its reading through a square. -/
theorem restrictScalarsAlongSquare_apply_eq_self (ψ₁ : B₁.Hom C₁) (θ : B₁.Hom B₁)
    (χ : C₁.Hom C₁)
    (h : ∀ b, χ.toAlgebraHom (ψ₁.toAlgebraHom b) = ψ₁.toAlgebraHom (θ.toAlgebraHom b))
    {N : DifferentialGradedModule.{u, u, u} C₁} (g : N ⟶ restrictScalars χ N)
    (hg : ∀ x, g.toFun x = x) (x : (restrictScalars ψ₁ N).M) :
    (restrictScalarsAlongSquare ψ₁ ψ₁ θ χ h g).toFun x = x :=
  hg x

/-- **The composition law for homomorphisms read through squares of restrictions.** -/
theorem restrictScalarsAlongSquare_apply_comp (ψ₁ : B₁.Hom C₁) (ψ₂ : B₂.Hom C₂) (ψ₃ : B₃.Hom C₃)
    (θ₁₂ : B₁.Hom B₂) (θ₂₃ : B₂.Hom B₃) (θ₁₃ : B₁.Hom B₃) (χ₁₂ : C₁.Hom C₂)
    (χ₂₃ : C₂.Hom C₃) (χ₁₃ : C₁.Hom C₃)
    (h₁₂ : ∀ b, χ₁₂.toAlgebraHom (ψ₁.toAlgebraHom b) = ψ₂.toAlgebraHom (θ₁₂.toAlgebraHom b))
    (h₂₃ : ∀ b, χ₂₃.toAlgebraHom (ψ₂.toAlgebraHom b) = ψ₃.toAlgebraHom (θ₂₃.toAlgebraHom b))
    (h₁₃ : ∀ b, χ₁₃.toAlgebraHom (ψ₁.toAlgebraHom b) = ψ₃.toAlgebraHom (θ₁₃.toAlgebraHom b))
    {N₁ : DifferentialGradedModule.{u, u, u} C₁} {N₂ : DifferentialGradedModule.{u, u, u} C₂}
    {N₃ : DifferentialGradedModule.{u, u, u} C₃} (g₁₂ : N₁ ⟶ restrictScalars χ₁₂ N₂)
    (g₂₃ : N₂ ⟶ restrictScalars χ₂₃ N₃) (g₁₃ : N₁ ⟶ restrictScalars χ₁₃ N₃)
    (hg : ∀ x, g₁₃.toFun x = g₂₃.toFun (g₁₂.toFun x)) (x : (restrictScalars ψ₁ N₁).M) :
    (restrictScalarsAlongSquare ψ₁ ψ₃ θ₁₃ χ₁₃ h₁₃ g₁₃).toFun x =
      (restrictScalarsAlongSquare ψ₂ ψ₃ θ₂₃ χ₂₃ h₂₃ g₂₃).toFun
        ((restrictScalarsAlongSquare ψ₁ ψ₂ θ₁₂ χ₁₂ h₁₂ g₁₂).toFun x) :=
  hg x

/-- **Naturality of homomorphisms read through squares of restrictions.** -/
theorem restrictScalarsAlongSquare_naturality (ψ₁ : B₁.Hom C₁) (ψ₂ : B₂.Hom C₂)
    (θ : B₁.Hom B₂) (χ : C₁.Hom C₂)
    (h : ∀ b, χ.toAlgebraHom (ψ₁.toAlgebraHom b) = ψ₂.toAlgebraHom (θ.toAlgebraHom b))
    {N₁ N₁' : DifferentialGradedModule.{u, u, u} C₁}
    {N₂ N₂' : DifferentialGradedModule.{u, u, u} C₂} (g : N₁ ⟶ restrictScalars χ N₂)
    (g' : N₁' ⟶ restrictScalars χ N₂') (f₁ : N₁ ⟶ N₁') (f₂ : N₂ ⟶ N₂')
    (hf : ∀ x, g'.toFun (f₁.toFun x) = f₂.toFun (g.toFun x)) (x : (restrictScalars ψ₁ N₁).M) :
    (restrictScalarsAlongSquare ψ₁ ψ₂ θ χ h g').toFun ((restrictScalarsHom ψ₁ f₁).toFun x) =
      (restrictScalarsHom ψ₂ f₂).toFun ((restrictScalarsAlongSquare ψ₁ ψ₂ θ χ h g).toFun x) :=
  hf x

end SquareLaws

end DifferentialGradedModule

namespace DifferentialGraded.Bimodule

/-- **Extensionality for linear maps out of a relative tensor product, on homogeneous pure
tensors.** -/
theorem tensorObj_linearMap_ext_homogeneous {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra.{u, u} R} (N : Bimodule A B)
    (M : DifferentialGradedModule.{u, u, u} A) {P : Type u} [AddCommGroup P] [Module R P]
    (f g : (tensorObj N M).M →ₗ[R] P)
    (h : ∀ (p : ℤ) (x : M.grading p) (y : N.rightModule.M),
      f ((tensorPure N M).toLinearMap (x : M.M) y) = g ((tensorPure N M).toLinearMap (x : M.M) y)) :
    f = g := by
  refine tensorObj_linearMap_ext N M f g fun x y => ?_
  have key :
      f ∘ₗ (tensorPure N M).toLinearMap.flip y = g ∘ₗ (tensorPure N M).toLinearMap.flip y := by
    exact DirectSum.decompose_lhom_ext M.grading fun p => LinearMap.ext fun x => h p x y
  exact LinearMap.congr_fun key x

/-- Two linear maps out of a relative tensor product agree pointwise once they agree on
homogeneous pure tensors. -/
private theorem tensorObj_apply_eq_of_pure {R : Type u} [CommRing R]
    {A B : DifferentialGradedAlgebra.{u, u} R} (N : Bimodule A B)
    (M : DifferentialGradedModule.{u, u, u} A) {P : Type u} [AddCommGroup P] [Module R P]
    (f g : (tensorObj N M).M →ₗ[R] P)
    (h : ∀ (p : ℤ) (x : M.grading p) (y : N.rightModule.M),
      f ((tensorPure N M).toLinearMap (x : M.M) y) = g ((tensorPure N M).toLinearMap (x : M.M) y))
    (z : (tensorObj N M).M) : f z = g z :=
  LinearMap.congr_fun (tensorObj_linearMap_ext_homogeneous N M f g h) z

variable {R : Type u} [CommRing R]
  {B₁ B₂ C₁ C₂ : DifferentialGradedAlgebra.{u, u} R} (θ : B₁.Hom B₂) (ψ₁ : B₁.Hom C₁)
  (ψ₂ : B₂.Hom C₂) (χ : C₁.Hom C₂)
  (h : ∀ b, χ.toAlgebraHom (ψ₁.toAlgebraHom b) = ψ₂.toAlgebraHom (θ.toAlgebraHom b))
  {X₁ : DifferentialGradedModule.{u, u, u} B₁} {X₂ : DifferentialGradedModule.{u, u, u} B₂}
  (g : X₁ ⟶ (restrictScalarsFunctor θ).obj X₂)

/-- The map `x ↦ g(x) ⊗ 1`, read over `B₁` through `χ ∘ ψ₁ = ψ₂ ∘ θ`. -/
def tensorSquareInner :
    X₁ ⟶ (restrictScalarsFunctor ψ₁).obj ((restrictScalarsFunctor χ).obj
      ((tensorCompFunctor (regular ψ₂)).obj X₂)) :=
  g ≫ (restrictScalarsFunctor θ).map (unitHom ψ₂ X₂) ≫
    restrictScalarsCongr (ψ := ψ₂.comp θ) (ψ' := χ.comp ψ₁) (fun b => (h b).symm) _

/-- `tensorSquareInner θ ψ₁ ψ₂ χ h g` sends `x` to `g(x) ⊗ 1`. -/
theorem tensorSquareInner_apply (x : X₁.M) :
    (tensorSquareInner θ ψ₁ ψ₂ χ h g).toFun x =
      (tensorPure (regular ψ₂) X₂).toLinearMap (g.toFun x) (1 : C₂.A) :=
  unitHom_apply ψ₂ X₂ (g.toFun x)

/-- **The base change of `g` along the square**: `x ⊗ c ↦ g(x) ⊗ χ(c)`. -/
def tensorSquareMap :
    (tensorCompFunctor (regular ψ₁)).obj X₁ ⟶
      (restrictScalarsFunctor χ).obj ((tensorCompFunctor (regular ψ₂)).obj X₂) :=
  plainTranspose ψ₁ (tensorSquareInner θ ψ₁ ψ₂ χ h g)

/-- **The base change along the square on a pure tensor**: `x ⊗ c ↦ g(x) ⊗ χ(c)`. -/
theorem tensorSquareMap_pure (p : ℤ) (x : X₁.grading p) (c : C₁.A) :
    (tensorSquareMap θ ψ₁ ψ₂ χ h g).toFun ((tensorPure (regular ψ₁) X₁).toLinearMap (x : X₁.M) c) =
      (tensorPure (regular ψ₂) X₂).toLinearMap (g.toFun (x : X₁.M)) (χ.toAlgebraHom c) := by
  refine (plainTranspose_pure ψ₁ (tensorSquareInner θ ψ₁ ψ₂ χ h g) p x c).trans ?_
  let Y := (tensorCompFunctor (regular ψ₂)).obj X₂
  change @HSMul.hSMul C₂.Aᵐᵒᵖ Y.M Y.M _ (MulOpposite.op (χ.toAlgebraHom c))
    ((tensorSquareInner θ ψ₁ ψ₂ χ h g).toFun (x : X₁.M)) = _
  refine (congrArg (fun z => @HSMul.hSMul C₂.Aᵐᵒᵖ Y.M Y.M _ (MulOpposite.op (χ.toAlgebraHom c)) z)
    (tensorSquareInner_apply θ ψ₁ ψ₂ χ h g x)).trans ?_
  refine ((tensorPure (regular ψ₂) X₂).map_right _ _ _).symm.trans ?_
  congr 1
  change (1 : C₂.A) * χ.toAlgebraHom c = _
  exact one_mul _

/-- **The base change along a square depends only on `g` and `χ`, pointwise.** -/
theorem tensorSquareMap_congr_apply (θ' : B₁.Hom B₂) (χ' : C₁.Hom C₂)
    (h' : ∀ b, χ'.toAlgebraHom (ψ₁.toAlgebraHom b) = ψ₂.toAlgebraHom (θ'.toAlgebraHom b))
    (g' : X₁ ⟶ (restrictScalarsFunctor θ').obj X₂) (hg : ∀ x, g'.toFun x = g.toFun x)
    (hχ : ∀ c, χ'.toAlgebraHom c = χ.toAlgebraHom c)
    (z : ((tensorCompFunctor (regular ψ₁)).obj X₁).M) :
    (tensorSquareMap θ' ψ₁ ψ₂ χ' h' g').toFun z = (tensorSquareMap θ ψ₁ ψ₂ χ h g).toFun z := by
  refine tensorObj_apply_eq_of_pure (regular ψ₁) X₁ _ _ (fun p x c => ?_) z
  refine (tensorSquareMap_pure θ' ψ₁ ψ₂ χ' h' g' p x c).trans ?_
  refine Eq.trans ?_ (tensorSquareMap_pure θ ψ₁ ψ₂ χ h g p x c).symm
  rw [hg]
  exact congrArg _ (hχ c)

/-- **Base change along the identity square is the identity.** -/
theorem tensorSquareMap_id_apply {B C : DifferentialGradedAlgebra.{u, u} R} (ψ : B.Hom C)
    (X : DifferentialGradedModule.{u, u, u} B)
    (z : ((tensorCompFunctor (regular ψ)).obj X).M) :
    (tensorSquareMap (DifferentialGradedAlgebra.Hom.id B) ψ ψ (DifferentialGradedAlgebra.Hom.id C)
      (fun _ => rfl) (restrictScalarsIdInv X)).toFun z = z := by
  refine tensorObj_apply_eq_of_pure (regular ψ) X
    ((tensorSquareMap (DifferentialGradedAlgebra.Hom.id B) ψ ψ
      (DifferentialGradedAlgebra.Hom.id C) (fun _ => rfl)
        (restrictScalarsIdInv X)).toFun.restrictScalars R) LinearMap.id (fun p x c => ?_) z
  exact tensorSquareMap_pure _ ψ ψ _ (fun _ => rfl) (restrictScalarsIdInv X) p x c

section Comp

variable {B₃ C₃ : DifferentialGradedAlgebra.{u, u} R} (θ' : B₂.Hom B₃) (ψ₃ : B₃.Hom C₃)
  (χ' : C₂.Hom C₃)
  (h' : ∀ b, χ'.toAlgebraHom (ψ₂.toAlgebraHom b) = ψ₃.toAlgebraHom (θ'.toAlgebraHom b))
  {X₃ : DifferentialGradedModule.{u, u, u} B₃} (g' : X₂ ⟶ (restrictScalarsFunctor θ').obj X₃)

/-- The composite of `g` and `g'`, read over `B₁` through `θ' ∘ θ`. -/
def compRestrict : X₁ ⟶ (restrictScalarsFunctor (θ'.comp θ)).obj X₃ :=
  g ≫ (restrictScalarsFunctor θ).map g' ≫ restrictScalarsCongr (fun _ => rfl) _

/-- `compRestrict θ g θ' g'` sends `x` to `g'(g(x))`. -/
@[simp] theorem compRestrict_apply (x : X₁.M) :
    (compRestrict θ g θ' g').toFun x = g'.toFun (g.toFun x) := rfl

include h h' in
/-- Pasting two commutative squares of homomorphisms of differential graded algebras gives a
commutative square: `(χ' ∘ χ) ∘ ψ₁ = ψ₃ ∘ (θ' ∘ θ)`. -/
theorem comp_square (b : B₁.A) :
    (χ'.comp χ).toAlgebraHom (ψ₁.toAlgebraHom b) =
      ψ₃.toAlgebraHom ((θ'.comp θ).toAlgebraHom b) := by
  change χ'.toAlgebraHom (χ.toAlgebraHom (ψ₁.toAlgebraHom b)) =
    ψ₃.toAlgebraHom (θ'.toAlgebraHom (θ.toAlgebraHom b))
  rw [h b, h']

/-- **Base change along a composite of squares is the composite of the base changes.** -/
theorem tensorSquareMap_comp_apply (z : ((tensorCompFunctor (regular ψ₁)).obj X₁).M) :
    (tensorSquareMap θ' ψ₂ ψ₃ χ' h' g').toFun ((tensorSquareMap θ ψ₁ ψ₂ χ h g).toFun z) =
      (tensorSquareMap (θ'.comp θ) ψ₁ ψ₃ (χ'.comp χ) (comp_square θ ψ₁ ψ₂ χ h θ' ψ₃ χ' h')
        (compRestrict θ g θ' g')).toFun z := by
  refine tensorObj_apply_eq_of_pure (regular ψ₁) X₁
    (((tensorSquareMap θ' ψ₂ ψ₃ χ' h' g').toFun.restrictScalars R).comp
      ((tensorSquareMap θ ψ₁ ψ₂ χ h g).toFun.restrictScalars R))
    ((tensorSquareMap (θ'.comp θ) ψ₁ ψ₃ (χ'.comp χ) (comp_square θ ψ₁ ψ₂ χ h θ' ψ₃ χ' h')
      (compRestrict θ g θ' g')).toFun.restrictScalars R) (fun p x c => ?_) z
  exact (congrArg (tensorSquareMap θ' ψ₂ ψ₃ χ' h' g').toFun
    (tensorSquareMap_pure θ ψ₁ ψ₂ χ h g p x c)).trans
    ((tensorSquareMap_pure θ' ψ₂ ψ₃ χ' h' g' p ⟨g.toFun x, g.map_grading p x x.2⟩
      (χ.toAlgebraHom c)).trans
      (tensorSquareMap_pure (θ'.comp θ) ψ₁ ψ₃ (χ'.comp χ) (comp_square θ ψ₁ ψ₂ χ h θ' ψ₃ χ' h')
        (compRestrict θ g θ' g') p x c).symm)

/-- **Base change along a square which is pointwise the identity is the identity.** -/
theorem tensorSquareMap_apply_eq_self {B C : DifferentialGradedAlgebra.{u, u} R} (θ : B.Hom B)
    (ψ : B.Hom C) (χ : C.Hom C)
    (h : ∀ b, χ.toAlgebraHom (ψ.toAlgebraHom b) = ψ.toAlgebraHom (θ.toAlgebraHom b))
    {X : DifferentialGradedModule.{u, u, u} B} (g : X ⟶ (restrictScalarsFunctor θ).obj X)
    (hg : ∀ x, g.toFun x = x) (hχ : ∀ c, χ.toAlgebraHom c = c)
    (z : ((tensorCompFunctor (regular ψ)).obj X).M) :
    (tensorSquareMap θ ψ ψ χ h g).toFun z = z :=
  (tensorSquareMap_congr_apply (DifferentialGradedAlgebra.Hom.id B) ψ ψ
    (DifferentialGradedAlgebra.Hom.id C) (fun _ => rfl) (restrictScalarsIdInv X) θ χ h g hg hχ
    z).trans (tensorSquareMap_id_apply ψ X z)

/-- **Base change along a square of isomorphisms, of an isomorphism, is bijective.** -/
theorem bijective_tensorSquareMap (θ' : B₂.Hom B₁) (χ' : C₂.Hom C₁)
    (h' : ∀ b, χ'.toAlgebraHom (ψ₂.toAlgebraHom b) = ψ₁.toAlgebraHom (θ'.toAlgebraHom b))
    (g' : X₂ ⟶ (restrictScalarsFunctor θ').obj X₁) (hgg : ∀ x, g'.toFun (g.toFun x) = x)
    (hgg' : ∀ y, g.toFun (g'.toFun y) = y) (hχχ : ∀ c, χ'.toAlgebraHom (χ.toAlgebraHom c) = c)
    (hχχ' : ∀ c, χ.toAlgebraHom (χ'.toAlgebraHom c) = c) :
    Function.Bijective (tensorSquareMap θ ψ₁ ψ₂ χ h g).toFun := by
  refine Function.bijective_iff_has_inverse.2
    ⟨(tensorSquareMap θ' ψ₂ ψ₁ χ' h' g').toFun, fun z => ?_, fun z => ?_⟩
  · refine (tensorSquareMap_comp_apply θ ψ₁ ψ₂ χ h g θ' ψ₁ χ' h' g' z).trans ?_
    exact tensorSquareMap_apply_eq_self _ ψ₁ _ _ _ hgg hχχ z
  · refine (tensorSquareMap_comp_apply θ' ψ₂ ψ₁ χ' h' g' θ ψ₂ χ h g z).trans ?_
    exact tensorSquareMap_apply_eq_self _ ψ₂ _ _ _ hgg' hχχ' z

section Transpose

variable {B B' D D' : DifferentialGradedAlgebra.{u, u} R}

/-- **The plain transpose is natural in the source.** -/
theorem plainTranspose_naturality_left (ψ : B.Hom D) {X X' : DifferentialGradedModule.{u, u, u} B}
    {Y : DifferentialGradedModule.{u, u, u} D} (f : X' ⟶ X)
    (k : X ⟶ (restrictScalarsFunctor ψ).obj Y) :
    plainTranspose ψ (f ≫ k) = (tensorCompFunctor (regular ψ)).map f ≫ plainTranspose ψ k :=
  (tensorRegularAdjRestrictScalars ψ).homEquiv_naturality_left_symm f k

/-- **The plain transpose is natural in the target.** -/
theorem plainTranspose_naturality_right (ψ : B.Hom D) {X : DifferentialGradedModule.{u, u, u} B}
    {Y Y' : DifferentialGradedModule.{u, u, u} D} (k : X ⟶ (restrictScalarsFunctor ψ).obj Y)
    (g : Y ⟶ Y') :
    plainTranspose ψ (k ≫ (restrictScalarsFunctor ψ).map g) = plainTranspose ψ k ≫ g :=
  (tensorRegularAdjRestrictScalars ψ).homEquiv_naturality_right_symm k g

/-- **The unit followed by the restriction of the plain transpose is the given map.** -/
theorem unitHom_comp_plainTranspose (ψ : B.Hom D) {X : DifferentialGradedModule.{u, u, u} B}
    {Y : DifferentialGradedModule.{u, u, u} D} (k : X ⟶ (restrictScalarsFunctor ψ).obj Y) :
    unitHom ψ X ≫ (restrictScalarsFunctor ψ).map (plainTranspose ψ k) = k := by
  have h := ((tensorRegularAdjRestrictScalars ψ).homEquiv X Y).apply_symm_apply k
  rwa [Adjunction.homEquiv_unit] at h

/-- **A map out of `X ⊗_B D` is the plain transpose of its composite with the unit.** -/
theorem plainTranspose_unitHom_comp (ψ : B.Hom D) {X : DifferentialGradedModule.{u, u, u} B}
    {Y : DifferentialGradedModule.{u, u, u} D} (m : (tensorCompFunctor (regular ψ)).obj X ⟶ Y) :
    plainTranspose ψ (unitHom ψ X ≫ (restrictScalarsFunctor ψ).map m) = m := by
  have h := ((tensorRegularAdjRestrictScalars ψ).homEquiv X Y).symm_apply_apply m
  rwa [Adjunction.homEquiv_unit] at h

/-- **Base change along a square followed by a plain transpose**: the transition of a diagram of
extensions of scalars followed by the plain transpose at the target is the plain transpose at
the source, when the two maps being transposed are compatible. -/
theorem tensorSquareMap_comp_plainTranspose (θ : B.Hom B') (ψ : B.Hom D) (ψ' : B'.Hom D)
    (h : ∀ b, (DifferentialGradedAlgebra.Hom.id D).toAlgebraHom (ψ.toAlgebraHom b) =
      ψ'.toAlgebraHom (θ.toAlgebraHom b))
    {X : DifferentialGradedModule.{u, u, u} B} {X' : DifferentialGradedModule.{u, u, u} B'}
    {Y : DifferentialGradedModule.{u, u, u} D} (r : X ⟶ (restrictScalarsFunctor θ).obj X')
    (k : X ⟶ (restrictScalarsFunctor ψ).obj Y) (k' : X' ⟶ (restrictScalarsFunctor ψ').obj Y)
    (hk : ∀ x, k'.toFun (r.toFun x) = k.toFun x) :
    tensorSquareMap θ ψ ψ' (DifferentialGradedAlgebra.Hom.id D) h r ≫ restrictScalarsIdHom _ ≫
      plainTranspose ψ' k' = plainTranspose ψ k := by
  refine _root_.DifferentialGradedModule.Hom.ext
    (tensorObj_linearMap_ext_homogeneous (regular ψ) X _ _ fun p x c => ?_)
  change (plainTranspose ψ' k').toFun ((tensorSquareMap θ ψ ψ' _ h r).toFun
      ((tensorPure (regular ψ) X).toLinearMap (x : X.M) c)) =
    (plainTranspose ψ k).toFun ((tensorPure (regular ψ) X).toLinearMap (x : X.M) c)
  refine (congrArg (plainTranspose ψ' k').toFun (tensorSquareMap_pure θ ψ ψ' _ h r p x c)).trans ?_
  refine (plainTranspose_pure ψ' k' p ⟨r.toFun x, r.map_grading p x x.2⟩ _).trans ?_
  refine Eq.trans ?_ (plainTranspose_pure ψ k p x c).symm
  exact congrArg (fun z => @HSMul.hSMul D.Aᵐᵒᵖ Y.M Y.M _ (MulOpposite.op c) z) (hk x)

/-- **Restriction of a plain transpose**: a plain transpose followed by a homomorphism read
through `χ` is the base change along `χ` followed by the plain transpose of the composite. -/
theorem plainTranspose_comp_restrict (ψ : B.Hom D) (χ : D.Hom D') (ψ' : B.Hom D')
    (h : ∀ b, χ.toAlgebraHom (ψ.toAlgebraHom b) =
      ψ'.toAlgebraHom ((DifferentialGradedAlgebra.Hom.id B).toAlgebraHom b))
    {X : DifferentialGradedModule.{u, u, u} B} {Y : DifferentialGradedModule.{u, u, u} D}
    {Y' : DifferentialGradedModule.{u, u, u} D'} (k : X ⟶ (restrictScalarsFunctor ψ).obj Y)
    (ρ : Y ⟶ (restrictScalarsFunctor χ).obj Y') (k' : X ⟶ (restrictScalarsFunctor ψ').obj Y')
    (hk : ∀ x, ρ.toFun (k.toFun x) = k'.toFun x) :
    plainTranspose ψ k ≫ ρ =
      tensorSquareMap (DifferentialGradedAlgebra.Hom.id B) ψ ψ' χ h (restrictScalarsIdInv X) ≫
        (restrictScalarsFunctor χ).map (plainTranspose ψ' k') := by
  refine _root_.DifferentialGradedModule.Hom.ext
    (tensorObj_linearMap_ext_homogeneous (regular ψ) X _ _ fun p x c => ?_)
  change ρ.toFun ((plainTranspose ψ k).toFun
      ((tensorPure (regular ψ) X).toLinearMap (x : X.M) c)) =
    (plainTranspose ψ' k').toFun ((tensorSquareMap _ ψ ψ' χ h (restrictScalarsIdInv X)).toFun
      ((tensorPure (regular ψ) X).toLinearMap (x : X.M) c))
  refine (congrArg ρ.toFun (plainTranspose_pure ψ k p x c)).trans ?_
  refine (ρ.map_smul _ c).trans ?_
  refine Eq.trans ?_ (congrArg (plainTranspose ψ' k').toFun
    (tensorSquareMap_pure _ ψ ψ' χ h (restrictScalarsIdInv X) p x c)).symm
  refine Eq.trans ?_ (plainTranspose_pure ψ' k' p x (χ.toAlgebraHom c)).symm
  exact congrArg (fun z => @HSMul.hSMul D'.Aᵐᵒᵖ Y'.M Y'.M _ (MulOpposite.op (χ.toAlgebraHom c)) z)
    (hk x)

end Transpose

section Regular

variable {B D : DifferentialGradedAlgebra.{u, u} R}

/-- **Extensionality for linear maps out of a relative tensor product, on pure tensors of
homogeneous elements.** -/
theorem tensorObj_linearMap_ext_bihomogeneous {A' B' : DifferentialGradedAlgebra.{u, u} R}
    (N : Bimodule A' B') (M : DifferentialGradedModule.{u, u, u} A') {P : Type u}
    [AddCommGroup P] [Module R P] (f g : (tensorObj N M).M →ₗ[R] P)
    (h : ∀ (p q : ℤ) (x : M.grading p) (y : N.rightModule.grading q),
      f ((tensorPure N M).toLinearMap (x : M.M) (y : N.rightModule.M)) =
        g ((tensorPure N M).toLinearMap (x : M.M) (y : N.rightModule.M))) : f = g := by
  refine tensorObj_linearMap_ext_homogeneous N M f g fun p x y => ?_
  have key : f ∘ₗ (tensorPure N M).toLinearMap (x : M.M) =
      g ∘ₗ (tensorPure N M).toLinearMap (x : M.M) := by
    exact DirectSum.decompose_lhom_ext N.rightModule.grading fun q =>
      LinearMap.ext fun y => h p q x y
  exact LinearMap.congr_fun key y

variable (ψ : B.Hom D) (ψ' : D.Hom B) (h₁ : ∀ b, ψ'.toAlgebraHom (ψ.toAlgebraHom b) = b)
  (h₂ : ∀ d, ψ.toAlgebraHom (ψ'.toAlgebraHom d) = d) (X : DifferentialGradedModule.{u, u, u} B)

include h₁ in
/-- The module `X`, read over `B` through `ψ' ∘ ψ = id`. -/
def restrictScalarsInverseHom :
    X ⟶ (restrictScalarsFunctor ψ).obj ((restrictScalarsFunctor ψ').obj X) where
  toFun := LinearMap.id
  map_smul x b := congrArg (fun c => (MulOpposite.op c • x : X.M)) (h₁ b).symm
  map_grading _ _ hx := hx
  map_d := rfl

include h₁ in
/-- The module `X` read over `B` through `ψ' ∘ ψ = id`, back to `X`. -/
def restrictScalarsInverseInv :
    (restrictScalarsFunctor ψ).obj ((restrictScalarsFunctor ψ').obj X) ⟶ X where
  toFun := LinearMap.id
  map_smul x b :=
    congrArg (fun c => (MulOpposite.op c • (show X.M from x) : X.M)) (h₁ b)
  map_grading _ _ hx := hx
  map_d := rfl

include h₁ in
/-- **A module read over `B` through `ψ' ∘ ψ = id` is the module itself.** -/
def restrictScalarsInverseIso :
    X ≅ (restrictScalarsFunctor ψ).obj ((restrictScalarsFunctor ψ').obj X) where
  hom := restrictScalarsInverseHom ψ ψ' h₁ X
  inv := restrictScalarsInverseInv ψ ψ' h₁ X
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- **Extension of scalars along an isomorphism is restriction along its inverse**:
`x ⊗ d ↦ x ψ'(d)`. -/
abbrev tensorInverseHom :
    (tensorCompFunctor (regular ψ)).obj X ⟶ (restrictScalarsFunctor ψ').obj X :=
  plainTranspose ψ (restrictScalarsInverseHom ψ ψ' h₁ X)

include h₁ h₂ in
/-- The unit `x ↦ x ⊗ 1` is a left inverse of `tensorInverseHom ψ ψ' h₁ X`. -/
theorem unitHom_tensorInverseHom (z : ((tensorCompFunctor (regular ψ)).obj X).M) :
    (unitHom ψ X).toFun ((tensorInverseHom ψ ψ' h₁ X).toFun z) = z := by
  have key : ((unitHom ψ X).toFun.restrictScalars R).comp
      ((tensorInverseHom ψ ψ' h₁ X).toFun.restrictScalars R) = LinearMap.id := by
    refine tensorObj_linearMap_ext_bihomogeneous (regular ψ) X _ _ fun p q x d => ?_
    change (unitHom ψ X).toFun ((tensorInverseHom ψ ψ' h₁ X).toFun
      ((tensorPure (regular ψ) X).toLinearMap (x : X.M) (d : (regular ψ).rightModule.M))) =
        (tensorPure (regular ψ) X).toLinearMap (x : X.M) (d : (regular ψ).rightModule.M)
    let d' : D.A := (d : (regular ψ).rightModule.M)
    refine (congrArg (unitHom ψ X).toFun (plainTranspose_pure ψ _ p x d')).trans ?_
    refine (unitHom_apply ψ X _).trans ?_
    let a : B.grading q := ⟨ψ'.toAlgebraHom d', ψ'.map_grading q _ d.2⟩
    let one : (regular ψ).rightModule.grading 0 := ⟨(1 : D.A), SetLike.one_mem_graded D.grading⟩
    refine ((tensorPure (regular ψ) X).balance p 0 q x one a).trans ?_
    refine congrArg ((tensorPure (regular ψ) X).toLinearMap (x : X.M))
      ((regularBimoduleStructure_action ψ q 0 a one).trans ?_)
    change ψ.toAlgebraHom (ψ'.toAlgebraHom d') * 1 = d'
    rw [mul_one, h₂]
  exact LinearMap.congr_fun key z

/-- `tensorInverseHom ψ ψ' h₁ X` is a left inverse of the unit `x ↦ x ⊗ 1`. -/
theorem tensorInverseHom_unitHom (x : X.M) :
    (tensorInverseHom ψ ψ' h₁ X).toFun ((unitHom ψ X).toFun x) = x :=
  congrArg (fun f => f.toFun x)
    (unitHom_comp_plainTranspose ψ (restrictScalarsInverseHom ψ ψ' h₁ X))

include h₁ h₂ in
/-- **The unit `x ↦ x ⊗ 1` of extension of scalars along an isomorphism is bijective.** -/
theorem bijective_unitHom : Function.Bijective (unitHom ψ X).toFun :=
  Function.bijective_iff_has_inverse.2 ⟨(tensorInverseHom ψ ψ' h₁ X).toFun,
    tensorInverseHom_unitHom ψ ψ' h₁ X, unitHom_tensorInverseHom ψ ψ' h₁ h₂ X⟩

include h₁ h₂ in
/-- **Extension of scalars along an isomorphism is restriction along its inverse**, as an
isomorphism `X ⊗_B D ≅ X_D`. -/
def tensorInverseIso : (tensorCompFunctor (regular ψ)).obj X ≅ (restrictScalarsFunctor ψ').obj X :=
  Hom.isoOfBijective (tensorInverseHom ψ ψ' h₁ X)
    (Function.bijective_iff_has_inverse.2 ⟨(unitHom ψ X).toFun,
      unitHom_tensorInverseHom ψ ψ' h₁ h₂ X, tensorInverseHom_unitHom ψ ψ' h₁ X⟩)

include h₁ h₂ in
/-- **Restriction of scalars along an isomorphism preserves orthogonality on the left to the
acyclic modules.** -/
theorem leftOrthogonal_restrictScalars_of_inverse
    (hX : (acyclic' B).leftOrthogonal ((toHomotopyCategory B).obj X)) :
    (acyclic' D).leftOrthogonal ((toHomotopyCategory D).obj ((restrictScalarsFunctor ψ').obj X)) :=
  ObjectProperty.prop_of_iso _ ((toHomotopyCategory D).mapIso (tensorInverseIso ψ ψ' h₁ h₂ X))
    (leftOrthogonal_tensorCompFunctor_obj ψ hX)

end Regular

end Comp

end DifferentialGraded.Bimodule
