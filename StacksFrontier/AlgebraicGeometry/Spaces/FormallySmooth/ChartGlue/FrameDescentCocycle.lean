module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.FrameDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.Glue

/-!
# The cocycle condition for the transition of the frame module

This file proves that the transition isomorphism of the frame module,
`Stacks.ChartGlue.FrameDescent.transition`, satisfies the cocycle condition of
`ModuleCat.DescentData`, so that it is a descent datum for modules along `A → B`.

The cocycle condition is reduced, by `ModuleCat.cocycle_of_unitTransition`, to the
coassociativity of the unit `σ : M → B ⊗[A] M`. Both sides of that equation are semilinear maps
out of the frame module along the first of the three inclusions `B → B ⊗[A] (B ⊗[A] B)`, so they
agree once they agree on the universal derivation, and there each of them is the transport of
the universal derivation along the third inclusion: the left-hand side in two steps, the
right-hand side in one, and transitivity of the transport,
`Stacks.ChartGlue.FormallyEtaleChart.transportFun_trans`, identifies them.

## Main definitions

* `Stacks.ChartGlue.FrameDescent.descentData`: the descent datum.
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

/-- The triple pullback of the frame module, `B ⊗[A] (B ⊗[A] M)`. -/
abbrev F₃ := B ⊗[A] E₂ (A' := A') R A B

/-- The action of `B ⊗[A] (B ⊗[A] B)` on the triple pullback. -/
def F₃Action : B ⊗[A] (B ⊗[A] B) →ₐ[A] Module.End A (F₃ (A' := A') R (A := A) (B := B)) :=
  Algebra.TensorProduct.lift
    ((Module.End.rTensorAlgHom A B (E₂ (A' := A') R A B)).comp (Algebra.lsmul A A B))
    ((Module.End.lTensorAlgHom A (E₂ (A' := A') R A B) B).comp
      (targetTensorAction A B (frameModuleCat (A' := A') R B)))
    fun _ _ ↦ by ext; rfl

/-- The `B ⊗ (B ⊗ B)`-module structure on the triple pullback given by `F₃Action`. -/
instance F₃Module : Module (B ⊗[A] (B ⊗[A] B)) (F₃ (A' := A') R (A := A) (B := B)) :=
  Module.compHom _ (F₃Action (A' := A') R (A := A) (B := B)).toRingHom

omit [Algebra A' A] [Algebra A' B] [IsScalarTower A' A B] [IsScalarTower A' R B] in
/-- `(x ⊗ c) • (b ⊗ e) = (x * b) ⊗ (c • e)` in the triple pullback. -/
lemma F₃_smul_tmul (x : B) (c : B ⊗[A] B) (b : B) (e : E₂ (A' := A') R A B) :
    (x ⊗ₜ[A] c) • (b ⊗ₜ[A] e : F₃ (A' := A') R (A := A) (B := B)) = (x * b) ⊗ₜ[A] (c • e) := by
  induction c using TensorProduct.inductionOn with
  | add c c' hc hc' => rw [tmul_add, add_smul, hc, hc', add_smul, tmul_add]
  | tmul y z => rfl

variable (A B) in
/-- The inclusion `B ⊗ B → B ⊗ (B ⊗ B)`, `x ⊗ y ↦ x ⊗ (y ⊗ 1)`. -/
abbrev e₁₂ₐ : B ⊗[A] B →ₐ[A'] B ⊗[A] (B ⊗[A] B) :=
  ((Algebra.TensorProduct.map (AlgHom.id A B) Algebra.TensorProduct.includeLeft :
    B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B))).restrictScalars A'

variable (A B) in
/-- The inclusion `B ⊗ B → B ⊗ (B ⊗ B)`, `x ⊗ y ↦ 1 ⊗ (x ⊗ y)`. -/
abbrev e₂₃ₐ : B ⊗[A] B →ₐ[A'] B ⊗[A] (B ⊗[A] B) :=
  ((Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B))).restrictScalars A'

variable (A B) in
/-- The inclusion `B ⊗ B → B ⊗ (B ⊗ B)`, `x ⊗ y ↦ x ⊗ (1 ⊗ y)`. -/
abbrev e₁₃ₐ : B ⊗[A] B →ₐ[A'] B ⊗[A] (B ⊗[A] B) :=
  ((Algebra.TensorProduct.map (AlgHom.id A B) Algebra.TensorProduct.includeRight :
    B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B))).restrictScalars A'

/-- `e₁₂ ∘ q₂ = e₂₃ ∘ q₁` as maps `B → B ⊗ (B ⊗ B)`: both send `b` to `1 ⊗ (b ⊗ 1)`. -/
lemma e₁₂_q₂ : (e₁₂ₐ (A' := A') A B).comp (q₂ A B) = (e₂₃ₐ A B).comp (q₁ A B) := by
  ext b; simp

/-- `e₂₃ ∘ q₂ = e₁₃ ∘ q₂` as maps `B → B ⊗ (B ⊗ B)`: both send `b` to `1 ⊗ (1 ⊗ b)`. -/
lemma e₂₃_q₂ : (e₂₃ₐ (A' := A') A B).comp (q₂ A B) = (e₁₃ₐ A B).comp (q₂ A B) := by
  ext b; simp

/-- `e₁₂ ∘ q₁ = e₁₃ ∘ q₁` as maps `B → B ⊗ (B ⊗ B)`: both send `b` to `b ⊗ (1 ⊗ 1)`. -/
lemma e₁₂_q₁ : (e₁₂ₐ (A' := A') A B).comp (q₁ A B) = (e₁₃ₐ A B).comp (q₁ A B) := by
  ext b; simp

variable (hC₂ : P (CommAlgCat.of A' (B ⊗[A] B)))
  (hpt : Φ.pt (C₂ A B hC₂) (w₁ R A B hC₂) = Φ.pt (C₂ A B hC₂) (w₂ R A B hC₂))
  (hE₁ : P (CommAlgCat.of A' (TrivExt (B ⊗[A] B) (E₁ (A' := A') R A B))))
  (hE₂ : P (CommAlgCat.of A' (TrivExt (B ⊗[A] B) (E₂ (A' := A') R A B))))
  (hC₃ : P (CommAlgCat.of A' (B ⊗[A] (B ⊗[A] B))))
  (hF₃ : P (CommAlgCat.of A' (TrivExt (B ⊗[A] (B ⊗[A] B)) (F₃ (A' := A') R (A := A) (B := B)))))

/-- The algebra `B ⊗ (B ⊗ B)`, as an object of `P`. -/
abbrev C₃ : P.FullSubcategory := ⟨CommAlgCat.of A' (B ⊗[A] (B ⊗[A] B)), hC₃⟩

/-- `e₁₂`, as a morphism of `P`. -/
abbrev e₁₂ : C₂ A B hC₂ ⟶ C₃ hC₃ := ObjectProperty.homMk (CommAlgCat.ofHom (e₁₂ₐ A B))
/-- `e₂₃`, as a morphism of `P`. -/
abbrev e₂₃ : C₂ A B hC₂ ⟶ C₃ hC₃ := ObjectProperty.homMk (CommAlgCat.ofHom (e₂₃ₐ A B))
/-- `e₁₃`, as a morphism of `P`. -/
abbrev e₁₃ : C₂ A B hC₂ ⟶ C₃ hC₃ := ObjectProperty.homMk (CommAlgCat.ofHom (e₁₃ₐ A B))

/-- `id ⊗ σ : B ⊗ M → B ⊗ (B ⊗ M)`, semilinear along `e₁₂`. -/
def Lσ : E₂ (A' := A') R A B →ₛₗ[((e₁₂ₐ (A' := A') A B : B ⊗[A] B →ₐ[A'] B ⊗[A] (B ⊗[A] B)) :
    B ⊗[A] B →+* B ⊗[A] (B ⊗[A] B))] F₃ (A' := A') R (A := A) (B := B) where
  toFun := LinearMap.lTensor B (unitTransition A B (frameModuleCat (A' := A') R B)
    (transition R Φ hC₂ hpt hE₁ hE₂))
  map_add' := map_add _
  map_smul' c x := by
    induction c using TensorProduct.inductionOn with
    | add c c' hc hc' => rw [add_smul, map_add, hc, hc', map_add, add_smul]
    | tmul x' y' =>
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
      | tmul b m =>
        rw [targetTensor_smul_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
          unitTransition_restrictedScalarAction]
        change _ = (x' ⊗ₜ[A] (y' ⊗ₜ[A] (1 : B))) • _
        rw [F₃_smul_tmul]

/-- `Lσ (b ⊗ m) = b ⊗ σ m`. -/
lemma Lσ_tmul (b : B) (m : restrictModule A B (frameModuleCat (A' := A') R B)) :
    Lσ R Φ hC₂ hpt hE₁ hE₂ (b ⊗ₜ[A] m) =
      b ⊗ₜ[A] σ R Φ hC₂ hpt hE₂ (fromRM R A m) := by
  change b ⊗ₜ[A] transition R Φ hC₂ hpt hE₁ hE₂ (m ⊗ₜ[A] (1 : B)) = _
  exact congrArg (b ⊗ₜ[A] ·) (transition_ι₁ R Φ hC₂ hpt hE₁ hE₂ (fromRM R A m))

/-- `x ↦ 1 ⊗ x : B ⊗ M → B ⊗ (B ⊗ M)`, semilinear along `e₂₃`. -/
def Lι : E₂ (A' := A') R A B →ₛₗ[((e₂₃ₐ (A' := A') A B : B ⊗[A] B →ₐ[A'] B ⊗[A] (B ⊗[A] B)) :
    B ⊗[A] B →+* B ⊗[A] (B ⊗[A] B))] F₃ (A' := A') R (A := A) (B := B) where
  toFun := TensorProduct.mk A B (E₂ (A' := A') R A B) 1
  map_add' := map_add _
  map_smul' c x := by
    induction c using TensorProduct.inductionOn with
    | add c c' hc hc' => rw [add_smul, map_add, hc, hc', map_add, add_smul]
    | tmul x' y' =>
      change (1 : B) ⊗ₜ[A] ((x' ⊗ₜ[A] y') • x) = ((1 : B) ⊗ₜ[A] (x' ⊗ₜ[A] y')) • ((1 : B) ⊗ₜ[A] x)
      rw [F₃_smul_tmul, mul_one]

/-- `id ⊗ (1 ⊗ ·) : B ⊗ M → B ⊗ (B ⊗ M)`, semilinear along `e₁₃`. -/
def Lμ : E₂ (A' := A') R A B →ₛₗ[((e₁₃ₐ (A' := A') A B : B ⊗[A] B →ₐ[A'] B ⊗[A] (B ⊗[A] B)) :
    B ⊗[A] B →+* B ⊗[A] (B ⊗[A] B))] F₃ (A' := A') R (A := A) (B := B) where
  toFun := LinearMap.lTensor B (TensorProduct.mk A B
    (restrictModule A B (frameModuleCat (A' := A') R B)) 1)
  map_add' := map_add _
  map_smul' c x := by
    induction c using TensorProduct.inductionOn with
    | add c c' hc hc' => rw [add_smul, map_add, hc, hc', map_add, add_smul]
    | tmul x' y' =>
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
      | tmul b m =>
        rw [targetTensor_smul_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
        change _ = (x' ⊗ₜ[A] ((1 : B) ⊗ₜ[A] y')) • _
        rw [F₃_smul_tmul, TensorProduct.mk_apply, TensorProduct.mk_apply, targetTensor_smul_tmul,
          mul_one]

include hC₃ hF₃ in
/-- **Coassociativity of the unit, on derivations.** The two composites of the unit with the
triple pullback maps, read as derivations along the first inclusion into `B ⊗ (B ⊗ B)`, agree. -/
lemma coassoc_derivation (r : R) :
    Lσ R Φ hC₂ hpt hE₁ hE₂ (ψ₂₁ R Φ hC₂ hpt hE₂ r) = Lμ R (ψ₂₁ R Φ hC₂ hpt hE₂ r) := by
  let D₁ := (ψ₂₁ R Φ hC₂ hpt hE₂).map (ah (e₁₂ hC₂ hC₃)) (Lσ R Φ hC₂ hpt hE₁ hE₂)
  let D₂ := (ψ₂₁ R Φ hC₂ hpt hE₂).map (ah (e₁₃ hC₂ hC₃)) (Lμ (A' := A') R (A := A) (B := B))
  have hfr : (ah (e₁₃ hC₂ hC₃)).comp (w₁ R A B hC₂) = (ah (e₁₂ hC₂ hC₃)).comp (w₁ R A B hC₂) :=
    congrArg (·.comp (frame R B) : (B →ₐ[A'] B ⊗[A] (B ⊗[A] B)) → _) e₁₂_q₁.symm
  have hpt₁ : Φ.derPt hF₃ D₁ = Φ.derPt hF₃ (D₂.cast hfr) := by
    rw [Φ.derPt_cast]
    simp only [D₁, D₂]
    rw [Φ.derPt_map (C := C₂ A B hC₂) (hN := hE₂), Φ.derPt_map (C := C₂ A B hC₂) (hN := hE₂),
      Φ.derPt_transportFun, ← Φ.derPt_map (C := C₂ A B hC₂) (hN := hE₂),
      ← Φ.derPt_map (C := C₂ A B hC₂) (hN := hE₂)]
    have h₁ : Φ.derPt hF₃ ((d₂ R hC₂).map (ah (e₁₂ hC₂ hC₃)) (Lσ R Φ hC₂ hpt hE₁ hE₂)) =
        Φ.derPt hF₃ ((d₂ R hC₂).map (ah (e₂₃ hC₂ hC₃)) (Lι (A' := A') R (A := A) (B := B))) := by
      have hfr' : (ah (e₁₂ hC₂ hC₃)).comp (w₂ R A B hC₂) =
          (ah (e₂₃ hC₂ hC₃)).comp (w₁ R A B hC₂) :=
        congrArg (·.comp (frame R B) : (B →ₐ[A'] B ⊗[A] (B ⊗[A] B)) → _) e₁₂_q₂
      rw [Φ.derPt_eq_of_apply_eq hfr' (δ' := (ψ₂₁ R Φ hC₂ hpt hE₂).map (ah (e₂₃ hC₂ hC₃))
          (Lι (A' := A') R (A := A) (B := B))) fun r ↦ ?_,
        Φ.derPt_map (C := C₂ A B hC₂) (hN := hE₂), Φ.derPt_transportFun,
        ← Φ.derPt_map (C := C₂ A B hC₂) (hN := hE₂)]
      change Lσ R Φ hC₂ hpt hE₁ hE₂ ((1 : B) ⊗ₜ[A] toRM R A (frameDiff (A' := A') R B r)) =
        (1 : B) ⊗ₜ[A] ψ₂₁ R Φ hC₂ hpt hE₂ r
      rw [Lσ_tmul]
      exact congrArg ((1 : B) ⊗ₜ[A] ·) (σ_frameDiff R Φ hC₂ hpt hE₂ r)
    have h₂ : Φ.derPt hF₃ ((d₂ R hC₂).map (ah (e₂₃ hC₂ hC₃)) (Lι (A' := A') R (A := A) (B := B))) =
        Φ.derPt hF₃ ((d₂ R hC₂).map (ah (e₁₃ hC₂ hC₃)) (Lμ (A' := A') R (A := A) (B := B))) := by
      have hfr' : (ah (e₂₃ hC₂ hC₃)).comp (w₂ R A B hC₂) =
          (ah (e₁₃ hC₂ hC₃)).comp (w₂ R A B hC₂) :=
        congrArg (·.comp (frame R B) : (B →ₐ[A'] B ⊗[A] (B ⊗[A] B)) → _) e₂₃_q₂
      exact Φ.derPt_eq_of_apply_eq hfr' fun r ↦ rfl
    exact h₁.trans h₂
  exact congrArg (fun δ : DerAlong _ _ ↦ δ r) (Φ.eq_of_derPt_eq hpt₁)

include hC₃ hF₃ in
/-- **Coassociativity of the unit.** -/
lemma coassoc (n : FrameModule (A' := A') R B) :
    Lσ R Φ hC₂ hpt hE₁ hE₂ (σ R Φ hC₂ hpt hE₂ n) = Lμ R (σ R Φ hC₂ hpt hE₂ n) := by
  have hn : n ∈ Submodule.span B (Set.range (frameDiff (A' := A') R B)) := by
    rw [frame_span]; trivial
  induction hn using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, rfl⟩ := hx
    rw [σ_frameDiff]
    exact coassoc_derivation R Φ hC₂ hpt hE₁ hE₂ hC₃ hF₃ r
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, hx, hy]
  | smul b x _ hx =>
    rw [(σ R Φ hC₂ hpt hE₂).map_smulₛₗ, (Lσ R Φ hC₂ hpt hE₁ hE₂).map_smulₛₗ,
      (Lμ (A' := A') R (A := A) (B := B)).map_smulₛₗ, hx]
    congr 1

include hC₃ hF₃ in
/-- **The cocycle condition** for the transition of the frame module. -/
theorem transition_cocycle :
    (transition12 A B (frameModuleCat (A' := A') R B) (transition R Φ hC₂ hpt hE₁ hE₂)).comp
        (transition01 A B (frameModuleCat (A' := A') R B) (transition R Φ hC₂ hpt hE₁ hE₂)) =
      transition02 A B (frameModuleCat (A' := A') R B) (transition R Φ hC₂ hpt hE₁ hE₂) := by
  refine cocycle_of_unitTransition A B _ _ fun n ↦ ?_
  have h := coassoc R Φ hC₂ hpt hE₁ hE₂ hC₃ hF₃ (fromRM R A n)
  rwa [← transition_ι₁ R Φ hC₂ hpt hE₁ hE₂] at h

/-- **The descent datum of the frame module** along `A → B`. -/
def descentData : ModuleCat.DescentData.{u, u, u} A B where
  module := frameModuleCat (A' := A') R B
  transition := transition R Φ hC₂ hpt hE₁ hE₂
  cocycle := transition_cocycle R Φ hC₂ hpt hE₁ hE₂ hC₃ hF₃

end FrameDescent

end Stacks.ChartGlue

end
