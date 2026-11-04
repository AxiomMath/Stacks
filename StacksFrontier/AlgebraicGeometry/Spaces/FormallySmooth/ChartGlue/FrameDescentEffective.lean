module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.FrameDescentCocycle
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Projective

/-!
# The descended frame module and the untwisting of the frame transport

Let `Φ` be a formally étale chart `R` of a functor `X`, let `A → B` be faithfully flat and let
`ū : R → B` be a frame of the restriction to `B` of a point of `X` over `A`. The frame module
`B ⊗[R] Ω[R⁄A']` carries the descent datum `Stacks.ChartGlue.FrameDescent.descentData`, which is
effective ([Stacks Project, Tag 023N]): there is an `A`-module `M` with `B ⊗[A] M ≅ B ⊗[R] Ω[R⁄A']`
compatibly with the transitions. For an `A`-algebra map `q : B → C` and a `C`-module `N`, an
`A`-linear map `φ : M → N` gives a derivation `Ψ_q φ` along the frame `q ∘ ū`.

**Untwisting.** For the two inclusions `q₁, q₂ : B → B ⊗[A] B`, the transport of derivations
from the frame `q₁ ∘ ū` to the frame `q₂ ∘ ū` sends `Ψ_{q₁} φ` to `Ψ_{q₂} φ`. In other words, in
terms of `M` the transport is the identity. This is what turns the twisted Čech cohomology of the
gluing problem into the Čech cohomology of the coefficients.

If `R` is formally smooth over `A'`, then `M` is projective ([Stacks Project, Tag 05A9]).

## Main definitions

* `Stacks.ChartGlue.FrameDescent.Descended`: the descended module `M` with its isomorphism.
* `Stacks.ChartGlue.FrameDescent.Descended.psi`: the derivation `Ψ_q φ`.

## Main results

* `Stacks.ChartGlue.FrameDescent.exists_descended`: effectivity.
* `Stacks.ChartGlue.FrameDescent.Descended.transportFun_psi`: untwisting.
* `Stacks.ChartGlue.FrameDescent.Descended.projective`: projectivity.
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct ModuleCat

universe v u

namespace Stacks.ChartGlue

namespace FrameDescent

variable {A' : Type u} [CommRing A'] {P : ObjectProperty (CommAlgCat.{u} A')}
  {X : P.FullSubcategory ⥤ Type v} (R : Type u) [CommRing R] [Algebra A' R]
  (Φ : FormallyEtaleChart P X R)
  {A : Type u} [CommRing A] [Algebra A' A]
  {B : Type u} [CommRing B] [Algebra A B] [Algebra A' B] [IsScalarTower A' A B] [Algebra R B]
  [IsScalarTower A' R B]

variable (A B) in
/-- A descent of the frame module along `A → B`: an `A`-module `M` with `B ⊗[A] M ≅ B ⊗[R] Ω`
compatible with a given transition. -/
structure Descended (t : E₁ (A' := A') R A B ≃ₗ[B ⊗[A] B] E₂ (A' := A') R A B) where
  /-- The descended module. -/
  M : ModuleCat.{u} A
  /-- The identification of its base change with the frame module. -/
  e : (B ⊗[A] M) ≃ₗ[B] FrameModule (A' := A') R B
  /-- Compatibility with the transition. -/
  compat : ∀ (a b : B) (m : M),
    t ((show restrictModule A B (frameModuleCat (A' := A') R B) from e (a ⊗ₜ[A] m)) ⊗ₜ[A] b) =
      a ⊗ₜ[A] (show restrictModule A B (frameModuleCat (A' := A') R B) from e (b ⊗ₜ[A] m))

variable (hC₂ : P (CommAlgCat.of A' (B ⊗[A] B)))
  (hpt : Φ.pt (C₂ A B hC₂) (w₁ R A B hC₂) = Φ.pt (C₂ A B hC₂) (w₂ R A B hC₂))
  (hE₁ : P (CommAlgCat.of A' (TrivExt (B ⊗[A] B) (E₁ (A' := A') R A B))))
  (hE₂ : P (CommAlgCat.of A' (TrivExt (B ⊗[A] B) (E₂ (A' := A') R A B))))
  (hC₃ : P (CommAlgCat.of A' (B ⊗[A] (B ⊗[A] B))))
  (hF₃ : P (CommAlgCat.of A' (TrivExt (B ⊗[A] (B ⊗[A] B)) (F₃ (A' := A') R (A := A) (B := B)))))

include hC₃ hF₃ in
/-- **The frame module descends**, by effectivity of descent along a faithfully flat map. -/
theorem exists_descended [Module.FaithfullyFlat A B] :
    Nonempty (Descended R A B (transition R Φ hC₂ hpt hE₁ hE₂)) := by
  obtain ⟨M, e, he⟩ :=
    DescentData.isEffective_of_faithfullyFlat A B (descentData R Φ hC₂ hpt hE₁ hE₂ hC₃ hF₃)
  exact ⟨⟨M, e, he⟩⟩

namespace Descended

variable {R} {t : E₁ (A' := A') R A B ≃ₗ[B ⊗[A] B] E₂ (A' := A') R A B}
  (Dm : Descended R A B t)

section Psi

variable {C : Type u} [CommRing C] [Algebra A C] [Algebra A' C] [IsScalarTower A' A C]
  {N : Type u} [AddCommGroup N] [Module C N] [Module A N] [IsScalarTower A C N]

/-- The `q`-semilinear map `B ⊗[A] M → N`, `b ⊗ m ↦ q b • φ m`. -/
def tensorLift (q : B →ₐ[A] C) (φ : Dm.M →ₗ[A] N) :
    B ⊗[A] Dm.M →ₛₗ[((q.restrictScalars A' : B →ₐ[A'] C) : B →+* C)] N where
  toFun := TensorProduct.lift
    (LinearMap.mk₂ A (fun b m ↦ q b • φ m)
      (fun b b' m ↦ by rw [map_add, add_smul])
      (fun a b m ↦ by rw [map_smul, smul_assoc])
      (fun b m m' ↦ by rw [map_add, smul_add])
      (fun a b m ↦ by rw [map_smul, smul_comm]))
  map_add' := map_add _
  map_smul' b x := by
    change TensorProduct.lift _ (b • x) = q b • TensorProduct.lift _ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
    | tmul b' m =>
      rw [smul_tmul', TensorProduct.lift.tmul, TensorProduct.lift.tmul, LinearMap.mk₂_apply,
        LinearMap.mk₂_apply, smul_eq_mul, map_mul, mul_smul]

/-- `tensorLift q φ (b ⊗ m) = q b • φ m`. -/
@[simp] lemma tensorLift_tmul (q : B →ₐ[A] C) (φ : Dm.M →ₗ[A] N) (b : B) (m : Dm.M) :
    Dm.tensorLift q φ (b ⊗ₜ[A] m) = q b • φ m := TensorProduct.lift.tmul _ _

/-- The frame module map `B ⊗[R] Ω → N` attached to `φ`, semilinear along `q`. -/
def frameMap (q : B →ₐ[A] C) (φ : Dm.M →ₗ[A] N) :
    FrameModule (A' := A') R B →ₛₗ[((q.restrictScalars A' : B →ₐ[A'] C) : B →+* C)] N :=
  (Dm.tensorLift q φ).comp Dm.e.symm.toLinearMap

/-- **The derivation `Ψ_q φ`** along the frame `q ∘ ū`. -/
def psi (q : B →ₐ[A] C) (φ : Dm.M →ₗ[A] N) :
    DerAlong ((q.restrictScalars A').comp (frame R B)) N :=
  (frameDiff (A' := A') R B).map (q.restrictScalars A') (Dm.frameMap q φ)

/-- `Ψ_q φ r` is `frameMap q φ` applied to the differential of `r`. -/
lemma psi_apply (q : B →ₐ[A] C) (φ : Dm.M →ₗ[A] N) (r : R) :
    Dm.psi q φ r = Dm.frameMap q φ (frameDiff (A' := A') R B r) := rfl

end Psi

section Untwist

variable {Φ hC₂ hpt hE₁ hE₂}
variable (Dm' : Descended R A B (transition R Φ hC₂ hpt hE₁ hE₂))
  {N : Type u} [AddCommGroup N] [Module (B ⊗[A] B) N] [Module A N] [IsScalarTower A (B ⊗[A] B) N]
  (hN : P (CommAlgCat.of A' (TrivExt (B ⊗[A] B) N)))

/-- The first inclusion, as an `A`-algebra map. -/
abbrev incl₁ : B →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeLeft
/-- The second inclusion, as an `A`-algebra map. -/
abbrev incl₂ : B →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeRight

/-- `frameMap q φ (e (a ⊗ m)) = q a • φ m`, for `q : B → B ⊗[A] B`. -/
lemma frameMap_e_tmul (q : B →ₐ[A] B ⊗[A] B) (φ : Dm'.M →ₗ[A] N) (a : B) (m : Dm'.M) :
    Dm'.frameMap q φ (Dm'.e (a ⊗ₜ[A] m)) = q a • φ m := by
  show Dm'.tensorLift q φ (Dm'.e.symm (Dm'.e _)) = _
  rw [LinearEquiv.symm_apply_apply, tensorLift_tmul]

/-- The two linear extensions of `φ` agree through the transition. -/
lemma extendLeft_eq_extendRight_comp (φ : Dm'.M →ₗ[A] N) :
    extendLeft R (Dm'.frameMap (incl₁ (A := A) (B := B)) φ) =
      (extendRight R (Dm'.frameMap (incl₂ (A := A) (B := B)) φ)).comp
        (transition R Φ hC₂ hpt hE₁ hE₂).toLinearMap := by
  refine ext_left R fun n ↦ ?_
  obtain ⟨x, rfl⟩ := Dm'.e.surjective n
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
  | tmul a m =>
    rw [extendLeft_ι₁, frameMap_e_tmul, LinearMap.comp_apply, LinearEquiv.coe_coe]
    show _ = extendRight R _ (transition R Φ hC₂ hpt hE₁ hE₂
      ((show restrictModule A B (frameModuleCat (A' := A') R B) from Dm'.e (a ⊗ₜ[A] m)) ⊗ₜ[A]
        (1 : B)))
    rw [Dm'.compat]
    show _ = extendRight R _ (a ⊗ₜ[A] toRM R A (Dm'.e ((1 : B) ⊗ₜ[A] m)))
    rw [extendRight_tmul, frameMap_e_tmul, map_one, one_smul]
    rfl

/-- **Untwisting.** The transport between the two frames of `B ⊗[A] B` sends `Ψ_{q₁} φ` to
`Ψ_{q₂} φ`. -/
theorem transportFun_psi (φ : Dm'.M →ₗ[A] N) :
    Φ.transportFun (C := C₂ A B hC₂) hN hpt (Dm'.psi (incl₁ (A := A) (B := B)) φ) =
      Dm'.psi (incl₂ (A := A) (B := B)) φ := by
  have h₁ : Dm'.psi (incl₁ (A := A) (B := B)) φ =
      (d₁ R hC₂).postcomp (extendLeft R (Dm'.frameMap (incl₁ (A := A) (B := B)) φ)) :=
    DerAlong.ext (funext fun r ↦ (extendLeft_ι₁ R _ _).symm)
  rw [h₁, Φ.transportFun_postcomp (C := C₂ A B hC₂) (hN := hE₁) hN,
    extendLeft_eq_extendRight_comp,
    show Φ.transportFun (C := C₂ A B hC₂) hE₁ hpt (d₁ R hC₂) = ψ₁₂ R Φ hC₂ hpt hE₁ from rfl,
    ← postcomp_transitionInvMap_d₂ R Φ hC₂ hpt hE₁]
  refine DerAlong.ext (funext fun r ↦ ?_)
  show extendRight R (Dm'.frameMap (incl₂ (A := A) (B := B)) φ)
    (transition R Φ hC₂ hpt hE₁ hE₂ ((transition R Φ hC₂ hpt hE₁ hE₂).symm
      (ι₂ R (frameDiff (A' := A') R B r)))) = _
  rw [LinearEquiv.apply_symm_apply, extendRight_ι₂]
  rfl

end Untwist

/-- **The descended module is projective** when the differentials of the chart are, by
[Stacks Project, Tag 05A9]. -/
theorem projective [Module.FaithfullyFlat A B] [Module.Projective R Ω[R⁄A']] :
    Module.Projective A Dm.M := by
  have : Module.Projective B (FrameModule (A' := A') R B) := Module.Projective.tensorProduct
  have : Module.Projective B (B ⊗[A] Dm.M) := Module.Projective.of_equiv Dm.e.symm
  exact Module.Projective.of_projective_tensorProduct B

section PsiProps

variable {C : Type u} [CommRing C] [Algebra A C] [Algebra A' C] [IsScalarTower A' A C]
  {N : Type u} [AddCommGroup N] [Module C N] [Module A N] [IsScalarTower A C N]

/-- `frameMap q φ (e (a ⊗ m)) = q a • φ m`. -/
lemma frameMap_e (q : B →ₐ[A] C) (φ : Dm.M →ₗ[A] N) (a : B) (m : Dm.M) :
    Dm.frameMap q φ (Dm.e (a ⊗ₜ[A] m)) = q a • φ m := by
  show Dm.tensorLift q φ (Dm.e.symm (Dm.e _)) = _
  rw [LinearEquiv.symm_apply_apply, tensorLift_tmul]

/-- **Compatibility of `frameMap` with a map of coefficients.** -/
lemma map_frameMap {C₀ : Type u} [CommRing C₀] [Algebra A C₀] [Algebra A' C₀]
    [IsScalarTower A' A C₀] {N₀ : Type u} [AddCommGroup N₀] [Module C₀ N₀] [Module A N₀]
    [IsScalarTower A C₀ N₀] (q₀ : B →ₐ[A] C₀) (q : B →ₐ[A] C) (φ : Dm.M →ₗ[A] N₀)
    (g : N₀ →ₗ[A] N) (hg : ∀ (b : B) (n : N₀), g (q₀ b • n) = q b • g n)
    (y : FrameModule (A' := A') R B) :
    g (Dm.frameMap q₀ φ y) = Dm.frameMap q (g.comp φ) y := by
  obtain ⟨x, rfl⟩ := Dm.e.surjective y
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x x' hx hx' => rw [map_add, map_add, map_add, hx, hx', map_add]
  | tmul b m => rw [frameMap_e, frameMap_e, hg, LinearMap.comp_apply]

/-- `frameMap` is determined by its values on `e (b ⊗ m)`. -/
lemma frameMap_ext {q : B →ₐ[A] C} {φ : Dm.M →ₗ[A] N}
    {l : FrameModule (A' := A') R B →+ N}
    (h : ∀ (b : B) (m : Dm.M), l (Dm.e (b ⊗ₜ[A] m)) = q b • φ m)
    (y : FrameModule (A' := A') R B) : Dm.frameMap q φ y = l y := by
  obtain ⟨x, rfl⟩ := Dm.e.surjective y
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x x' hx hx' => rw [map_add, map_add, map_add, hx, hx']
  | tmul b m => rw [frameMap_e, h]

/-- `frameMap q (φ - φ') = frameMap q φ - frameMap q φ'`. -/
lemma frameMap_sub (q : B →ₐ[A] C) (φ φ' : Dm.M →ₗ[A] N) (y : FrameModule (A' := A') R B) :
    Dm.frameMap q (φ - φ') y = Dm.frameMap q φ y - Dm.frameMap q φ' y :=
  Dm.frameMap_ext (l := (Dm.frameMap q φ).toAddMonoidHom - (Dm.frameMap q φ').toAddMonoidHom)
    (fun b m ↦ by
      simp only [AddMonoidHom.sub_apply, LinearMap.toAddMonoidHom_coe, frameMap_e,
        LinearMap.sub_apply, smul_sub]) y

/-- `Ψ_q (φ - φ') = Ψ_q φ - Ψ_q φ'`. -/
lemma psi_sub (q : B →ₐ[A] C) (φ φ' : Dm.M →ₗ[A] N) (r : R) :
    Dm.psi q (φ - φ') r = Dm.psi q φ r - Dm.psi q φ' r :=
  Dm.frameMap_sub q φ φ' _

/-- The `A`-linear map `M → N` attached to a derivation along `q ∘ ū`. -/
def phiOf (q : B →ₐ[A] C) (δ : DerAlong ((q.restrictScalars A').comp (frame R B)) N) :
    Dm.M →ₗ[A] N where
  toFun m := frameLift (q.restrictScalars A') δ (Dm.e ((1 : B) ⊗ₜ[A] m))
  map_add' m m' := by rw [tmul_add, map_add, map_add]
  map_smul' a m := by
    have hm : (a • (1 : B)) ⊗ₜ[A] m = algebraMap A B a • ((1 : B) ⊗ₜ[A] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one]
    rw [RingHom.id_apply, ← TensorProduct.smul_tmul, hm, LinearEquiv.map_smul,
      LinearMap.map_smulₛₗ]
    change q (algebraMap A B a) • _ = _
    rw [AlgHom.commutes, algebraMap_smul]

/-- **Every derivation along `q ∘ ū` is `Ψ_q φ`.** -/
lemma psi_phiOf (q : B →ₐ[A] C) (δ : DerAlong ((q.restrictScalars A').comp (frame R B)) N) :
    Dm.psi q (Dm.phiOf q δ) = δ := by
  have h : ∀ y, Dm.frameMap q (Dm.phiOf q δ) y = frameLift (q.restrictScalars A') δ y :=
    Dm.frameMap_ext (l := (frameLift (q.restrictScalars A') δ).toAddMonoidHom) fun b m ↦ by
      have hb : (b ⊗ₜ[A] m : B ⊗[A] Dm.M) = b • ((1 : B) ⊗ₜ[A] m) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [LinearMap.toAddMonoidHom_coe, hb, LinearEquiv.map_smul, LinearMap.map_smulₛₗ]
      show q b • _ = q b • _
      rfl
  refine DerAlong.ext (funext fun r ↦ ?_)
  show Dm.frameMap q _ _ = δ r
  rw [h, frameLift_frameDiff]

/-- The semilinear extension of `Ψ_q φ` to the frame module is `frameMap q φ`. -/
lemma frameLift_psi (q : B →ₐ[A] C) (φ : Dm.M →ₗ[A] N) :
    frameLift (q.restrictScalars A') (Dm.psi q φ) = Dm.frameMap q φ :=
  frame_semilinear_ext fun r ↦ by rw [frameLift_frameDiff]; rfl

/-- `phiOf q` is a left inverse of `φ ↦ Ψ_q φ`. -/
lemma phiOf_psi (q : B →ₐ[A] C) (φ : Dm.M →ₗ[A] N) : Dm.phiOf q (Dm.psi q φ) = φ := by
  ext m
  show frameLift _ (Dm.psi q φ) (Dm.e ((1 : B) ⊗ₜ[A] m)) = φ m
  rw [frameLift_psi, frameMap_e, map_one, one_smul]

/-- `φ ↦ Ψ_q φ` is injective. -/
lemma psi_injective (q : B →ₐ[A] C) {φ φ' : Dm.M →ₗ[A] N}
    (h : ∀ r, Dm.psi q φ r = Dm.psi q φ' r) : φ = φ' := by
  rw [← Dm.phiOf_psi q φ, ← Dm.phiOf_psi q φ', show Dm.psi q φ = Dm.psi q φ' from
    DerAlong.ext (funext h)]

/-- `frameMap q (φ + φ') = frameMap q φ + frameMap q φ'`. -/
lemma frameMap_add (q : B →ₐ[A] C) (φ φ' : Dm.M →ₗ[A] N) (y : FrameModule (A' := A') R B) :
    Dm.frameMap q (φ + φ') y = Dm.frameMap q φ y + Dm.frameMap q φ' y :=
  Dm.frameMap_ext (l := (Dm.frameMap q φ).toAddMonoidHom + (Dm.frameMap q φ').toAddMonoidHom)
    (fun b m ↦ by
      simp only [AddMonoidHom.add_apply, LinearMap.toAddMonoidHom_coe, frameMap_e,
        LinearMap.add_apply, smul_add]) y

/-- `Ψ_q (φ + φ') = Ψ_q φ + Ψ_q φ'`. -/
lemma psi_add (q : B →ₐ[A] C) (φ φ' : Dm.M →ₗ[A] N) (r : R) :
    Dm.psi q (φ + φ') r = Dm.psi q φ r + Dm.psi q φ' r :=
  Dm.frameMap_add q φ φ' _

/-- If `g : N → N₁` is semilinear along `e : C → C₁` and `e ∘ q₀ = q`, then
`g ∘ Ψ_{q₀} φ = Ψ_q (g ∘ φ)`. -/
lemma psi_comp_eq (q₀ : B →ₐ[A] C) {C₁ : Type u} [CommRing C₁] [Algebra A C₁] [Algebra A' C₁]
    [IsScalarTower A' A C₁] {N₁ : Type u} [AddCommGroup N₁] [Module C₁ N₁] [Module A N₁]
    [IsScalarTower A C₁ N₁] (e : C →ₐ[A] C₁) (q : B →ₐ[A] C₁) (hq : e.comp q₀ = q)
    (φ : Dm.M →ₗ[A] N) (g : N →ₗ[A] N₁) (hg : ∀ (c : C) (n : N), g (c • n) = e c • g n)
    (r : R) : g (Dm.psi q₀ φ r) = Dm.psi q (g.comp φ) r :=
  Dm.map_frameMap q₀ q φ g (fun b n ↦ by rw [hg, ← hq]; rfl) _

end PsiProps

section UntwistPair

variable {Φ hC₂ hpt hE₁ hE₂}
variable (Dm' : Descended R A B (transition R Φ hC₂ hpt hE₁ hE₂))
  {C : P.FullSubcategory} [Algebra A C.obj] [IsScalarTower A' A C.obj]
  {N : Type u} [AddCommGroup N] [Module C.obj N] [Module A N] [IsScalarTower A C.obj N]

/-- Equal `A`-algebra maps `a = a'` give the same derivation: `Ψ_a φ = Ψ_{a'} φ`. -/
lemma psi_apply_eq_of_eq {C' : Type u} [CommRing C'] [Algebra A C'] [Algebra A' C']
    [IsScalarTower A' A C'] {N' : Type u} [AddCommGroup N'] [Module C' N'] [Module A N']
    [IsScalarTower A C' N'] {a a' : B →ₐ[A] C'} (h : a = a') (φ : Dm'.M →ₗ[A] N') (r : R) :
    Dm'.psi a φ r = Dm'.psi a' φ r := by subst h; rfl

/-- Transporting along `f` and then recasting equals pushing forward along `f` and then
transporting. -/
private theorem transportFun_map_cast_eq {C₀ : P.FullSubcategory} {N₀ : Type u}
    [AddCommGroup N₀] [Module C₀.obj N₀] {hN₀ : P (CommAlgCat.of A' (TrivExt C₀.obj N₀))}
    {w₁ w₂ : R →ₐ[A'] C₀.obj} (h : Φ.pt C₀ w₁ = Φ.pt C₀ w₂) (f : C₀ ⟶ C)
    (t : N₀ →ₛₗ[((f.hom.hom : C₀.obj →ₐ[A'] C.obj) : C₀.obj →+* C.obj)] N)
    {w₁' w₂' : R →ₐ[A'] C.obj} (e₁ : f.hom.hom.comp w₁ = w₁') (e₂ : f.hom.hom.comp w₂ = w₂')
    (hN : P (CommAlgCat.of A' (TrivExt C.obj N))) (h' : Φ.pt C w₁' = Φ.pt C w₂')
    (δ : DerAlong w₁ N₀) :
    Φ.transportFun hN h' ((δ.map f.hom.hom t).cast e₁) =
      ((Φ.transportFun hN₀ h δ).map f.hom.hom t).cast e₂ := by
  have h'' : Φ.pt C (f.hom.hom.comp w₁) = Φ.pt C (f.hom.hom.comp w₂) := by
    rw [Φ.pt_comp, Φ.pt_comp, h]
  rw [Φ.transportFun_cast (hN := hN) e₁ e₂ h'' h', Φ.transportFun_map f t hN h h'' δ]

/-- **Untwisting for an arbitrary pair** `a, b : B → C` of `A`-algebra maps. -/
theorem transportFun_psi_pair (a b : B →ₐ[A] C.obj) (hN : P (CommAlgCat.of A' (TrivExt C.obj N)))
    (hNf : letI := Module.compHom N (Algebra.TensorProduct.lift a b
        (fun _ _ ↦ Commute.all _ _) : B ⊗[A] B →ₐ[A] C.obj).toRingHom
      P (CommAlgCat.of A' (TrivExt (B ⊗[A] B) N)))
    (hab : Φ.pt C ((a.restrictScalars A').comp (frame R B)) =
      Φ.pt C ((b.restrictScalars A').comp (frame R B)))
    (φ : Dm'.M →ₗ[A] N) (r : R) :
    Φ.transportFun hN hab (Dm'.psi a φ) r = Dm'.psi b φ r := by
  let f : B ⊗[A] B →ₐ[A] C.obj := Algebra.TensorProduct.lift a b (fun _ _ ↦ Commute.all _ _)
  let : Module (B ⊗[A] B) N := Module.compHom N f.toRingHom
  have : IsScalarTower A (B ⊗[A] B) N := ⟨fun a' c n ↦ by
    show f (a' • c) • n = a' • (f c • n)
    rw [map_smul, smul_assoc]⟩
  let fm : C₂ A B hC₂ ⟶ C := ObjectProperty.homMk (CommAlgCat.ofHom (f.restrictScalars A'))
  let g : N →ₛₗ[((f.restrictScalars A' : B ⊗[A] B →ₐ[A'] C.obj) : B ⊗[A] B →+* C.obj)] N :=
    { toFun := id, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  have hfa :
      (f.restrictScalars A').comp (w₁ R A B hC₂) = (a.restrictScalars A').comp (frame R B) :=
    AlgHom.ext fun r ↦ by simp [f]
  have hfb :
      (f.restrictScalars A').comp (w₂ R A B hC₂) = (b.restrictScalars A').comp (frame R B) :=
    AlgHom.ext fun r ↦ by simp [f]
  have hval₁ : ∀ r, ((Dm'.psi (incl₁ (A := A) (B := B)) φ).map fm.hom.hom g) r = Dm'.psi a φ r :=
    fun r ↦ Dm'.map_frameMap (incl₁ (A := A) (B := B)) a φ LinearMap.id
      (fun b' n ↦ by change f (b' ⊗ₜ[A] 1) • n = a b' • n; simp [f]) _
  have hval₂ : ∀ r, ((Dm'.psi (incl₂ (A := A) (B := B)) φ).map fm.hom.hom g) r = Dm'.psi b φ r :=
    fun r ↦ Dm'.map_frameMap (incl₂ (A := A) (B := B)) b φ LinearMap.id
      (fun b' n ↦ by change f (1 ⊗ₜ[A] b') • n = b b' • n; simp [f]) _
  have key := transportFun_map_cast_eq (Φ := Φ) (hN₀ := hNf) hpt fm g hfa hfb hN hab
    (Dm'.psi (incl₁ (A := A) (B := B)) φ)
  have e₁ : ((Dm'.psi (incl₁ (A := A) (B := B)) φ).map fm.hom.hom g).cast hfa = Dm'.psi a φ :=
    DerAlong.ext (funext hval₁)
  rw [Dm'.transportFun_psi hNf, e₁] at key
  rw [key]
  exact hval₂ r

/-- **Transport of a derivation over a thickened algebra, untwisted.** If a derivation `δ` over
`C₀` along `w₁` pushes forward along `f : C₀ → C` and `t : N₀ → N` to `Ψ_a φ`, then its transport
to `w₂` pushes forward to `Ψ_b φ`, where `f ∘ w₁ = a ∘ ū` and `f ∘ w₂ = b ∘ ū`. -/
theorem transportFun_map_psi_pair {C₀ : P.FullSubcategory} {N₀ : Type u} [AddCommGroup N₀]
    [Module C₀.obj N₀] {hN₀ : P (CommAlgCat.of A' (TrivExt C₀.obj N₀))}
    {w₁ w₂ : R →ₐ[A'] C₀.obj} (h : Φ.pt C₀ w₁ = Φ.pt C₀ w₂) (f : C₀ ⟶ C)
    (t : N₀ →ₛₗ[((f.hom.hom : C₀.obj →ₐ[A'] C.obj) : C₀.obj →+* C.obj)] N)
    (a b : B →ₐ[A] C.obj) (e₁ : f.hom.hom.comp w₁ = (a.restrictScalars A').comp (frame R B))
    (e₂ : f.hom.hom.comp w₂ = (b.restrictScalars A').comp (frame R B))
    (hN : P (CommAlgCat.of A' (TrivExt C.obj N)))
    (hNf : letI := Module.compHom N (Algebra.TensorProduct.lift a b
        (fun _ _ ↦ Commute.all _ _) : B ⊗[A] B →ₐ[A] C.obj).toRingHom
      P (CommAlgCat.of A' (TrivExt (B ⊗[A] B) N)))
    (hab : Φ.pt C ((a.restrictScalars A').comp (frame R B)) =
      Φ.pt C ((b.restrictScalars A').comp (frame R B)))
    (φ : Dm'.M →ₗ[A] N) (δ : DerAlong w₁ N₀) (hδ : ∀ r, t (δ r) = Dm'.psi a φ r) (r : R) :
    t (Φ.transportFun hN₀ h δ r) = Dm'.psi b φ r := by
  have hδ' : (δ.map f.hom.hom t).cast e₁ = Dm'.psi a φ := DerAlong.ext (funext hδ)
  have hc := transportFun_map_cast_eq (Φ := Φ) (hN₀ := hN₀) h f t e₁ e₂ hN hab δ
  rw [hδ'] at hc
  have hp := Dm'.transportFun_psi_pair a b hN hNf hab φ r
  rwa [hc] at hp

end UntwistPair

end Descended

end FrameDescent

end Stacks.ChartGlue

end
