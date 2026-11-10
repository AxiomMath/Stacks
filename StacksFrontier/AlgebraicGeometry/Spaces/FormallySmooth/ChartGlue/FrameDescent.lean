module

public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FaithfullyFlatEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Descent.Module.CocycleCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.FrameModule
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.Transport

/-!
# Descent of the frame module along a cover

Let `Φ` be a formally étale chart `R` of a functor `X` on a class `P` of `A'`-algebras, let
`A → B` be a map of `A'`-algebras, and let `ū : R → B` be a frame of the restriction to `B` of a
point of `X` over `A`. The two composites `R → B ⇉ B ⊗[A] B` are then two frames of one point,
and the transport of derivations between them, `Stacks.ChartGlue.FormallyEtaleChart.transport`,
is a natural isomorphism between the functors of derivations along the two frames.

Read on the representing module `B ⊗[R] Ω[R⁄A']` of `Stacks.ChartGlue.FrameModule`, that natural
isomorphism is an isomorphism between the two pullbacks of the frame module to `B ⊗[A] B`: a
transition isomorphism in the sense of `ModuleCat.DescentData`. This file constructs it.

## Main definitions

* `Stacks.ChartGlue.FrameDescent.unit`: the unit `σ : n ↦ e(n ⊗ 1)` of the transition.
* `Stacks.ChartGlue.FrameDescent.transition`: the transition isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct ModuleCat

universe v u

namespace Stacks.ChartGlue

namespace FrameDescent

variable {A' : Type u} [CommRing A'] {P : ObjectProperty (CommAlgCat.{u} A')}
  {X : P.FullSubcategory ⥤ Type v} (R : Type u) [CommRing R] [Algebra A' R]
  {Φ : FormallyEtaleChart P X R}
  (A : Type u) [CommRing A] [Algebra A' A]
  (B : Type u) [CommRing B] [Algebra A B] [Algebra A' B] [IsScalarTower A' A B] [Algebra R B]
  [IsScalarTower A' R B]

/-- The frame `ū : R → B`. -/
abbrev frame : R →ₐ[A'] B := IsScalarTower.toAlgHom A' R B

/-- The first inclusion `B → B ⊗[A] B`. -/
abbrev q₁ : B →ₐ[A'] B ⊗[A] B :=
  (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).restrictScalars A'

/-- The second inclusion `B → B ⊗[A] B`. -/
abbrev q₂ : B →ₐ[A'] B ⊗[A] B := (Algebra.TensorProduct.includeRight).restrictScalars A'

/-- The frame module, as a module over `B`. -/
abbrev frameModuleCat : ModuleCat.{u} B := ModuleCat.of B (FrameModule (A' := A') R B)

/-- The first pullback of the frame module to `B ⊗[A] B`. -/
abbrev E₁ := restrictModule A B (frameModuleCat (A' := A') R B) ⊗[A] B

/-- The second pullback of the frame module to `B ⊗[A] B`. -/
abbrev E₂ := B ⊗[A] restrictModule A B (frameModuleCat (A' := A') R B)

variable (hC₂ : P (CommAlgCat.of A' (B ⊗[A] B)))

/-- The algebra `B ⊗[A] B`, as an object of `P`. -/
abbrev C₂ : P.FullSubcategory := ⟨CommAlgCat.of A' (B ⊗[A] B), hC₂⟩

variable {A B}

/-- The inclusion of the frame module into its first pullback, `n ↦ n ⊗ 1`. -/
def ι₁ : FrameModule (A' := A') R B →ₛₗ[((q₁ (A' := A') A B : B →ₐ[A'] B ⊗[A] B) : B →+* B ⊗[A] B)]
    E₁ (A' := A') R A B where
  toFun n := (show restrictModule A B (frameModuleCat (A' := A') R B) from n) ⊗ₜ[A] (1 : B)
  map_add' n n' := add_tmul _ _ _
  map_smul' b n := by
    change _ = (b ⊗ₜ[A] (1 : B)) • _
    rw [sourceTensor_smul_tmul, mul_one]
    rfl

omit [IsScalarTower A' R B] in
/-- `ι₁` sends `n` to `n ⊗ 1`. -/
@[simp] lemma ι₁_apply (n : FrameModule (A' := A') R B) :
    ι₁ R (A := A) (B := B) n =
      (show restrictModule A B (frameModuleCat (A' := A') R B) from n) ⊗ₜ[A] (1 : B) := rfl

/-- The inclusion of the frame module into its second pullback, `n ↦ 1 ⊗ n`. -/
def ι₂ : FrameModule (A' := A') R B →ₛₗ[((q₂ (A' := A') A B : B →ₐ[A'] B ⊗[A] B) : B →+* B ⊗[A] B)]
    E₂ (A' := A') R A B where
  toFun n := (1 : B) ⊗ₜ[A] (show restrictModule A B (frameModuleCat (A' := A') R B) from n)
  map_add' n n' := tmul_add _ _ _
  map_smul' b n := by
    change _ = ((1 : B) ⊗ₜ[A] b) • _
    rw [targetTensor_smul_tmul, mul_one]
    rfl

omit [IsScalarTower A' R B] in
/-- `ι₂` sends `n` to `1 ⊗ n`. -/
@[simp] lemma ι₂_apply (n : FrameModule (A' := A') R B) :
    ι₂ R (A := A) (B := B) n =
      (1 : B) ⊗ₜ[A] (show restrictModule A B (frameModuleCat (A' := A') R B) from n) := rfl

variable (A B) in
/-- The first frame `R → B → B ⊗[A] B`. -/
abbrev w₁ : R →ₐ[A'] (C₂ A B hC₂).obj := (q₁ A B).comp (frame R B)

variable (A B) in
/-- The second frame `R → B → B ⊗[A] B`. -/
abbrev w₂ : R →ₐ[A'] (C₂ A B hC₂).obj := (q₂ A B).comp (frame R B)

variable (Φ) (hpt : Φ.pt (C₂ A B hC₂) (w₁ R A B hC₂) = Φ.pt (C₂ A B hC₂) (w₂ R A B hC₂))
  (hE₁ : P (CommAlgCat.of A' (TrivExt (B ⊗[A] B) (E₁ (A' := A') R A B))))
  (hE₂ : P (CommAlgCat.of A' (TrivExt (B ⊗[A] B) (E₂ (A' := A') R A B))))

/-- The universal derivation along the first frame, `r ↦ dr ⊗ 1`. -/
abbrev d₁ : DerAlong (w₁ R A B hC₂) (E₁ (A' := A') R A B) :=
  (frameDiff (A' := A') R B).map (q₁ A B) (ι₁ R)

/-- The universal derivation along the second frame, `r ↦ 1 ⊗ dr`. -/
abbrev d₂ : DerAlong (w₂ R A B hC₂) (E₂ (A' := A') R A B) :=
  (frameDiff (A' := A') R B).map (q₂ A B) (ι₂ R)

/-- The transport of the universal derivation along the second frame to the first. -/
abbrev ψ₂₁ : DerAlong (w₁ R A B hC₂) (E₂ (A' := A') R A B) :=
  Φ.transportFun (C := C₂ A B hC₂) hE₂ hpt.symm (d₂ R hC₂)

/-- The transport of the universal derivation along the first frame to the second. -/
abbrev ψ₁₂ : DerAlong (w₂ R A B hC₂) (E₁ (A' := A') R A B) :=
  Φ.transportFun (C := C₂ A B hC₂) hE₁ hpt (d₁ R hC₂)

/-- **The unit of the transition**, `σ : M → B ⊗[A] M`, semilinear along the first inclusion. -/
abbrev σ : FrameModule (A' := A') R B →ₛₗ[((q₁ A B : B →ₐ[A'] B ⊗[A] B) : B →+* B ⊗[A] B)]
    E₂ (A' := A') R A B :=
  frameLift (q₁ A B) (ψ₂₁ R Φ hC₂ hpt hE₂)

/-- The unit of the inverse transition, `σ' : M → M ⊗[A] B`, semilinear along the second
inclusion. -/
abbrev σ' : FrameModule (A' := A') R B →ₛₗ[((q₂ A B : B →ₐ[A'] B ⊗[A] B) : B →+* B ⊗[A] B)]
    E₁ (A' := A') R A B :=
  frameLift (q₂ A B) (ψ₁₂ R Φ hC₂ hpt hE₁)

section Extend

variable {F : Type u} [AddCommGroup F] [Module (B ⊗[A] B) F] [Module A F]
  [IsScalarTower A (B ⊗[A] B) F]

variable (A) in
/-- An element of the frame module, read in the restriction of scalars to `A`. -/
abbrev toRM (n : FrameModule (A' := A') R B) :
    restrictModule A B (frameModuleCat (A' := A') R B) := n

variable (A) in
/-- An element of the restriction of scalars of the frame module, read in the frame module. -/
abbrev fromRM (n : restrictModule A B (frameModuleCat (A' := A') R B)) :
    FrameModule (A' := A') R B := n

omit [Algebra A' A] [Algebra A' B] [IsScalarTower A' A B] [IsScalarTower A' R B] in
/-- `fromRM` is additive. -/
lemma fromRM_add (n n' : restrictModule A B (frameModuleCat (A' := A') R B)) :
    fromRM R A (n + n') = fromRM R A n + fromRM R A n' := rfl

omit [Algebra A' A] [Algebra A' B] [IsScalarTower A' A B] [IsScalarTower A' R B] in
/-- `fromRM` turns the action of `a : A` into the action of its image in `B`. -/
lemma fromRM_smul (a : A) (n : restrictModule A B (frameModuleCat (A' := A') R B)) :
    fromRM R A (a • n) = algebraMap A B a • fromRM R A n := rfl

omit [IsScalarTower A' R B] in
/-- In the first pullback, `n ⊗ b = (1 ⊗ b) • ι₁ n`. -/
lemma tmul_eq_smul_ι₁ (n : FrameModule (A' := A') R B) (b : B) :
    (toRM R A n ⊗ₜ[A] b : E₁ (A' := A') R A B) = ((1 : B) ⊗ₜ[A] b) • ι₁ R n := by
  rw [ι₁_apply, sourceTensor_smul_tmul, mul_one]
  congr 1
  exact (LinearMap.congr_fun (restrictedScalarAction A B _).map_one (toRM R A n)).symm

omit [IsScalarTower A' R B] in
/-- In the second pullback, `b ⊗ n = (b ⊗ 1) • ι₂ n`. -/
lemma tmul_eq_smul_ι₂ (b : B) (n : FrameModule (A' := A') R B) :
    (b ⊗ₜ[A] toRM R A n : E₂ (A' := A') R A B) = (b ⊗ₜ[A] (1 : B)) • ι₂ R n := by
  rw [ι₂_apply, targetTensor_smul_tmul, mul_one]
  congr 1
  exact (LinearMap.congr_fun (restrictedScalarAction A B _).map_one (toRM R A n)).symm

/-- The `A`-linear map underlying `extendLeft`. -/
def extendLeftAux
    (g : FrameModule (A' := A') R B →ₛₗ[((q₁ A B : B →ₐ[A'] B ⊗[A] B) : B →+* B ⊗[A] B)] F) :
    E₁ (A' := A') R A B →ₗ[A] F :=
  TensorProduct.lift (LinearMap.mk₂ A (fun n b ↦ ((1 : B) ⊗ₜ[A] b) • g (fromRM R A n))
    (fun n n' b ↦ by rw [fromRM_add, map_add, smul_add])
    (fun a n b ↦ by
      rw [fromRM_smul, g.map_smulₛₗ, ← IsScalarTower.algebraMap_smul (B ⊗[A] B) a, smul_smul,
        smul_smul, mul_comm]
      rfl)
    (fun n b b' ↦ by rw [tmul_add, add_smul])
    (fun a n b ↦ by rw [TensorProduct.tmul_smul, smul_assoc]))

omit [IsScalarTower A' R B] in
/-- `extendLeftAux g` sends `n ⊗ b` to `(1 ⊗ b) • g n`. -/
lemma extendLeftAux_tmul
    (g : FrameModule (A' := A') R B →ₛₗ[((q₁ A B : B →ₐ[A'] B ⊗[A] B) : B →+* B ⊗[A] B)] F)
    (n : FrameModule (A' := A') R B) (b : B) :
    extendLeftAux R g (toRM R A n ⊗ₜ[A] b) = ((1 : B) ⊗ₜ[A] b) • g n := rfl

/-- The `B ⊗[A] B`-linear map out of the first pullback attached to a map semilinear along the
first inclusion: `n ⊗ b ↦ (1 ⊗ b) • g n`. -/
def extendLeft
    (g : FrameModule (A' := A') R B →ₛₗ[((q₁ A B : B →ₐ[A'] B ⊗[A] B) : B →+* B ⊗[A] B)] F) :
    E₁ (A' := A') R A B →ₗ[B ⊗[A] B] F where
  toFun := extendLeftAux R g
  map_add' := map_add _
  map_smul' c x := by
    simp only [RingHom.id_apply]
    induction c using TensorProduct.inductionOn with
    | add c c' hc hc' => rw [add_smul, map_add, hc, hc', add_smul]
    | tmul x' y' =>
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
      | tmul n b =>
        rw [sourceTensor_smul_tmul]
        change extendLeftAux R g (toRM R A (x' • fromRM R A n) ⊗ₜ[A]
          (y' * b)) = (x' ⊗ₜ[A] y') • extendLeftAux R g (toRM R A (fromRM R A n) ⊗ₜ[A] b)
        rw [extendLeftAux_tmul, extendLeftAux_tmul, g.map_smulₛₗ, smul_smul, smul_smul]
        congr 1
        simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]

omit [IsScalarTower A' R B] in
/-- `extendLeft g` sends `n ⊗ b` to `(1 ⊗ b) • g n`. -/
@[simp] lemma extendLeft_tmul
    (g : FrameModule (A' := A') R B →ₛₗ[((q₁ A B : B →ₐ[A'] B ⊗[A] B) : B →+* B ⊗[A] B)] F)
    (n : FrameModule (A' := A') R B) (b : B) :
    extendLeft R g (toRM R A n ⊗ₜ[A] b) = ((1 : B) ⊗ₜ[A] b) • g n := rfl

omit [IsScalarTower A' R B] in
/-- `extendLeft g` restricts to `g` along `ι₁`. -/
lemma extendLeft_ι₁
    (g : FrameModule (A' := A') R B →ₛₗ[((q₁ A B : B →ₐ[A'] B ⊗[A] B) : B →+* B ⊗[A] B)] F)
    (n : FrameModule (A' := A') R B) : extendLeft R g (ι₁ R n) = g n := by
  change extendLeft R g (toRM R A n ⊗ₜ[A] (1 : B)) = _
  rw [extendLeft_tmul, ← Algebra.TensorProduct.one_def, one_smul]

omit [IsScalarTower A' R B] [Module A F] [IsScalarTower A (B ⊗[A] B) F] in
/-- A `B ⊗[A] B`-linear map out of the first pullback is determined on `n ⊗ 1`. -/
lemma ext_left {f f' : E₁ (A' := A') R A B →ₗ[B ⊗[A] B] F}
    (h : ∀ n : FrameModule (A' := A') R B, f (ι₁ R n) = f' (ι₁ R n)) : f = f' := by
  ext x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul n b =>
    change f (toRM R A (fromRM R A n) ⊗ₜ[A] b) = f' (toRM R A (fromRM R A n) ⊗ₜ[A] b)
    rw [tmul_eq_smul_ι₁ R (fromRM R A n) b, f.map_smul, f'.map_smul, h]

/-- The `A`-linear map underlying `extendRight`. -/
def extendRightAux
    (g : FrameModule (A' := A') R B →ₛₗ[((q₂ A B : B →ₐ[A'] B ⊗[A] B) : B →+* B ⊗[A] B)] F) :
    E₂ (A' := A') R A B →ₗ[A] F :=
  TensorProduct.lift (LinearMap.mk₂ A (fun b n ↦ (b ⊗ₜ[A] (1 : B)) • g (fromRM R A n))
    (fun b b' n ↦ by rw [add_tmul, add_smul])
    (fun a b n ↦ by rw [← TensorProduct.smul_tmul', smul_assoc])
    (fun b n n' ↦ by rw [fromRM_add, map_add, smul_add])
    (fun a b n ↦ by
      rw [fromRM_smul, g.map_smulₛₗ, ← IsScalarTower.algebraMap_smul (B ⊗[A] B) a, smul_smul,
        smul_smul]
      congr 1
      simp only [AlgHom.coe_restrictScalars', RingHom.coe_coe,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [Algebra.algebraMap_eq_smul_one a, ← TensorProduct.smul_tmul, Algebra.smul_def,
        Algebra.smul_def, mul_one]))

omit [IsScalarTower A' R B] in
/-- `extendRightAux g` sends `b ⊗ n` to `(b ⊗ 1) • g n`. -/
lemma extendRightAux_tmul
    (g : FrameModule (A' := A') R B →ₛₗ[((q₂ A B : B →ₐ[A'] B ⊗[A] B) : B →+* B ⊗[A] B)] F)
    (b : B) (n : FrameModule (A' := A') R B) :
    extendRightAux R g (b ⊗ₜ[A] toRM R A n) = (b ⊗ₜ[A] (1 : B)) • g n := rfl

/-- The `B ⊗[A] B`-linear map out of the second pullback attached to a map semilinear along the
second inclusion: `b ⊗ n ↦ (b ⊗ 1) • g n`. -/
def extendRight
    (g : FrameModule (A' := A') R B →ₛₗ[((q₂ A B : B →ₐ[A'] B ⊗[A] B) : B →+* B ⊗[A] B)] F) :
    E₂ (A' := A') R A B →ₗ[B ⊗[A] B] F where
  toFun := extendRightAux R g
  map_add' := map_add _
  map_smul' c x := by
    simp only [RingHom.id_apply]
    induction c using TensorProduct.inductionOn with
    | add c c' hc hc' => rw [add_smul, map_add, hc, hc', add_smul]
    | tmul x' y' =>
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
      | tmul b n =>
        rw [targetTensor_smul_tmul]
        change extendRightAux R g ((x' * b) ⊗ₜ[A]
          toRM R A (y' • fromRM R A n)) =
            (x' ⊗ₜ[A] y') • extendRightAux R g (b ⊗ₜ[A] toRM R A (fromRM R A n))
        rw [extendRightAux_tmul, extendRightAux_tmul, g.map_smulₛₗ, smul_smul, smul_smul]
        congr 1
        simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]

omit [IsScalarTower A' R B] in
/-- `extendRight g` sends `b ⊗ n` to `(b ⊗ 1) • g n`. -/
@[simp] lemma extendRight_tmul
    (g : FrameModule (A' := A') R B →ₛₗ[((q₂ A B : B →ₐ[A'] B ⊗[A] B) : B →+* B ⊗[A] B)] F)
    (b : B) (n : FrameModule (A' := A') R B) :
    extendRight R g (b ⊗ₜ[A] toRM R A n) = (b ⊗ₜ[A] (1 : B)) • g n := rfl

omit [IsScalarTower A' R B] in
/-- `extendRight g` restricts to `g` along `ι₂`. -/
lemma extendRight_ι₂
    (g : FrameModule (A' := A') R B →ₛₗ[((q₂ A B : B →ₐ[A'] B ⊗[A] B) : B →+* B ⊗[A] B)] F)
    (n : FrameModule (A' := A') R B) : extendRight R g (ι₂ R n) = g n := by
  change extendRight R g ((1 : B) ⊗ₜ[A] toRM R A n) = _
  rw [extendRight_tmul, ← Algebra.TensorProduct.one_def, one_smul]

omit [IsScalarTower A' R B] [Module A F] [IsScalarTower A (B ⊗[A] B) F] in
/-- A `B ⊗[A] B`-linear map out of the second pullback is determined on `1 ⊗ n`. -/
lemma ext_right {f f' : E₂ (A' := A') R A B →ₗ[B ⊗[A] B] F}
    (h : ∀ n : FrameModule (A' := A') R B, f (ι₂ R n) = f' (ι₂ R n)) : f = f' := by
  ext x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul b n =>
    change f (b ⊗ₜ[A] toRM R A (fromRM R A n)) = f' (b ⊗ₜ[A] toRM R A (fromRM R A n))
    rw [tmul_eq_smul_ι₂ R b (fromRM R A n), f.map_smul, f'.map_smul, h]

end Extend

/-- The transition map `M ⊗ B → B ⊗ M`, `n ⊗ b ↦ (1 ⊗ b) • σ n`. -/
abbrev transitionMap : E₁ (A' := A') R A B →ₗ[B ⊗[A] B] E₂ (A' := A') R A B :=
  extendLeft R (σ R Φ hC₂ hpt hE₂)

/-- The inverse transition map `B ⊗ M → M ⊗ B`, `b ⊗ n ↦ (b ⊗ 1) • σ' n`. -/
abbrev transitionInvMap : E₂ (A' := A') R A B →ₗ[B ⊗[A] B] E₁ (A' := A') R A B :=
  extendRight R (σ' R Φ hC₂ hpt hE₁)

/-- The unit `σ` sends `dr` to the transported derivation `ψ₂₁` at `r`. -/
lemma σ_frameDiff (r : R) :
    σ R Φ hC₂ hpt hE₂ (frameDiff (A' := A') R B r) = ψ₂₁ R Φ hC₂ hpt hE₂ r :=
  frameLift_frameDiff _ _ r

/-- The unit `σ'` sends `dr` to the transported derivation `ψ₁₂` at `r`. -/
lemma σ'_frameDiff (r : R) :
    σ' R Φ hC₂ hpt hE₁ (frameDiff (A' := A') R B r) = ψ₁₂ R Φ hC₂ hpt hE₁ r :=
  frameLift_frameDiff _ _ r

/-- The inverse transition map carries the universal derivation `d₂` to `ψ₁₂`. -/
lemma postcomp_transitionInvMap_d₂ :
    (d₂ R hC₂).postcomp (transitionInvMap R Φ hC₂ hpt hE₁) = ψ₁₂ R Φ hC₂ hpt hE₁ :=
  DerAlong.ext (funext fun r ↦ by
    change transitionInvMap R Φ hC₂ hpt hE₁ (ι₂ R (frameDiff (A' := A') R B r)) = _
    rw [extendRight_ι₂, σ'_frameDiff])

/-- The transition map carries the universal derivation `d₁` to `ψ₂₁`. -/
lemma postcomp_transitionMap_d₁ :
    (d₁ R hC₂).postcomp (transitionMap R Φ hC₂ hpt hE₂) = ψ₂₁ R Φ hC₂ hpt hE₂ :=
  DerAlong.ext (funext fun r ↦ by
    change transitionMap R Φ hC₂ hpt hE₂ (ι₁ R (frameDiff (A' := A') R B r)) = _
    rw [extendLeft_ι₁, σ_frameDiff])

/-- The inverse transition map is a left inverse of the transition map. -/
lemma transitionInvMap_comp_transitionMap :
    (transitionInvMap R Φ hC₂ hpt hE₁).comp (transitionMap R Φ hC₂ hpt hE₂) = LinearMap.id := by
  refine ext_left R fun n ↦ ?_
  rw [LinearMap.comp_apply, extendLeft_ι₁, LinearMap.id_apply]
  have key : (transitionInvMap R Φ hC₂ hpt hE₁ : E₂ (A' := A') R A B →ₗ[B ⊗[A] B]
      E₁ (A' := A') R A B).comp (σ R Φ hC₂ hpt hE₂) = ι₁ R := by
    refine frame_semilinear_ext fun r ↦ ?_
    rw [LinearMap.comp_apply, σ_frameDiff]
    change ((Φ.transportFun (C := C₂ A B hC₂) hE₂ hpt.symm (d₂ R hC₂)).postcomp
      (transitionInvMap R Φ hC₂ hpt hE₁)) r = d₁ R hC₂ r
    rw [← Φ.transportFun_postcomp (C := C₂ A B hC₂) (hN := hE₂) hE₁,
      postcomp_transitionInvMap_d₂, Φ.transportFun_symm]
  exact LinearMap.congr_fun key n

/-- The inverse transition map is a right inverse of the transition map. -/
lemma transitionMap_comp_transitionInvMap :
    (transitionMap R Φ hC₂ hpt hE₂).comp (transitionInvMap R Φ hC₂ hpt hE₁) = LinearMap.id := by
  refine ext_right R fun n ↦ ?_
  rw [LinearMap.comp_apply, extendRight_ι₂, LinearMap.id_apply]
  have key : (transitionMap R Φ hC₂ hpt hE₂ : E₁ (A' := A') R A B →ₗ[B ⊗[A] B]
      E₂ (A' := A') R A B).comp (σ' R Φ hC₂ hpt hE₁) = ι₂ R := by
    refine frame_semilinear_ext fun r ↦ ?_
    rw [LinearMap.comp_apply, σ'_frameDiff]
    change ((Φ.transportFun (C := C₂ A B hC₂) hE₁ hpt (d₁ R hC₂)).postcomp
      (transitionMap R Φ hC₂ hpt hE₂)) r = d₂ R hC₂ r
    rw [← Φ.transportFun_postcomp (C := C₂ A B hC₂) (hN := hE₁) hE₂,
      postcomp_transitionMap_d₁, Φ.transportFun_symm]
  exact LinearMap.congr_fun key n

/-- **The transition isomorphism** of the frame module, from the transport of derivations. -/
def transition : E₁ (A' := A') R A B ≃ₗ[B ⊗[A] B] E₂ (A' := A') R A B :=
  LinearEquiv.ofLinearMap (transitionMap R Φ hC₂ hpt hE₂) (transitionInvMap R Φ hC₂ hpt hE₁)
    (transitionMap_comp_transitionInvMap R Φ hC₂ hpt hE₁ hE₂)
    (transitionInvMap_comp_transitionMap R Φ hC₂ hpt hE₁ hE₂)

/-- The transition isomorphism sends `n ⊗ 1` to `σ n`. -/
lemma transition_ι₁ (n : FrameModule (A' := A') R B) :
    transition R Φ hC₂ hpt hE₁ hE₂ (ι₁ R n) = σ R Φ hC₂ hpt hE₂ n :=
  extendLeft_ι₁ R _ n

end FrameDescent

end Stacks.ChartGlue

end
