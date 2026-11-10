module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# The weight-one part of a symmetric algebra

For a commutative ring `R` and an `R`-module `W`, the symmetric algebra `Sym_R W` is graded by
degree. This file isolates its degree-one part without using the grading: the linear part
`AdequateFunctor.symmetricLinearPart : Sym_R W → W` is the `W`-component of the algebra map
`Sym_R W → R ⊕ W` to the square-zero extension that sends `w` to `(0, w)`. It is a retraction of
the inclusion `ι : W → Sym_R W`, it is natural for maps of pairs `(R, W) → (R', W')`, and it
computes the `ε`-coefficient of the weight coaction `Sym_R W → Sym_R W [ε]`, `w ↦ ε w`:
that coefficient is `ι ∘ symmetricLinearPart`.

## Main results

* `AdequateFunctor.symmetricLinearPart_ι` — the linear part is a retraction of `ι`.
* `AdequateFunctor.symmetricLinearPart_naturality` — naturality in the pair `(R, W)`.
* `AdequateFunctor.snd_symmetricWeightCoaction` — the `ε`-coefficient of the weight coaction
  is `ι` composed with the linear part.
-/

@[expose] public section

namespace AdequateFunctor

open TrivSqZeroExt

universe u₁ u₂ u₃ u₄

section LinearPart

variable (R : Type u₁) [CommRing R] (W : Type u₂) [AddCommGroup W] [Module R W]

/-- The right action of `R` on `W` through the left one, needed for the square-zero extension
`R ⊕ W` to be an `R`-algebra. -/
@[reducible] def oppositeModuleOfComm : Module Rᵐᵒᵖ W :=
  Module.compHom W ((RingHom.id R).fromOpposite mul_comm)

attribute [local instance 10] oppositeModuleOfComm

/-- The left and right actions of `R` on `W` agree. -/
instance isCentralScalar_oppositeModuleOfComm : IsCentralScalar R W := ⟨fun _ _ => rfl⟩

/-- The algebra map `Sym_R W → R ⊕ W` to the square-zero extension sending `w` to `(0, w)`. -/
noncomputable def symmetricSqZeroLift : SymmetricAlgebra R W →ₐ[R] TrivSqZeroExt R W :=
  SymmetricAlgebra.lift (inrHom R W)

/-- The linear part of an element of the symmetric algebra: its degree-one component. -/
noncomputable def symmetricLinearPart : SymmetricAlgebra R W →ₗ[R] W :=
  sndHom R W ∘ₗ (symmetricSqZeroLift R W).toLinearMap

variable {R W}

/-- The linear part of a generator `ι w` is `w`. -/
@[simp] lemma symmetricLinearPart_ι (w : W) :
    symmetricLinearPart R W (SymmetricAlgebra.ι R W w) = w := by
  simp [symmetricLinearPart, symmetricSqZeroLift, SymmetricAlgebra.lift_ι_apply]

/-- The linear part of a scalar `algebraMap R (SymmetricAlgebra R W) r` is zero. -/
@[simp] lemma symmetricLinearPart_algebraMap (r : R) :
    symmetricLinearPart R W (algebraMap R (SymmetricAlgebra R W) r) = 0 := by
  simp [symmetricLinearPart, TrivSqZeroExt.algebraMap_eq_inl]

/-- The scalar component of the square-zero lift of `algebraMap R _ r` is `r`. -/
private lemma fst_symmetricSqZeroLift_algebraMap (r : R) :
    (symmetricSqZeroLift R W (algebraMap R (SymmetricAlgebra R W) r)).fst = r := by
  rw [AlgHom.commutes, TrivSqZeroExt.algebraMap_eq_inl, fst_inl]

/-- The linear part of a product obeys the Leibniz rule, with the scalars acting through the
`R`-components of the square-zero lift. -/
lemma symmetricLinearPart_mul (x y : SymmetricAlgebra R W) :
    symmetricLinearPart R W (x * y) =
      (symmetricSqZeroLift R W x).fst • symmetricLinearPart R W y +
        (symmetricSqZeroLift R W y).fst • symmetricLinearPart R W x := by
  simp only [symmetricLinearPart, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    map_mul, sndHom_apply, snd_mul]
  rfl

/-- The linear part is linear for multiplication by scalars. -/
lemma symmetricLinearPart_algebraMap_mul (r : R) (x : SymmetricAlgebra R W) :
    symmetricLinearPart R W (algebraMap R (SymmetricAlgebra R W) r * x) =
      r • symmetricLinearPart R W x := by
  rw [symmetricLinearPart_mul, symmetricLinearPart_algebraMap, smul_zero, add_zero,
    fst_symmetricSqZeroLift_algebraMap]

section Naturality

variable {R' : Type u₃} [CommRing R'] {W' : Type u₄} [AddCommGroup W'] [Module R' W']

/-- **Naturality of the linear part.** A ring map of symmetric algebras lying over a ring map
`f : R → R'` and a semilinear map `g : W → W'` on generators commutes with the linear parts. -/
lemma symmetricLinearPart_naturality (f : R →+* R') (g : W →ₛₗ[f] W')
    (F : SymmetricAlgebra R W →+* SymmetricAlgebra R' W')
    (hF₁ : ∀ r, F (algebraMap R (SymmetricAlgebra R W) r) =
      algebraMap R' (SymmetricAlgebra R' W') (f r))
    (hF₂ : ∀ w, F (SymmetricAlgebra.ι R W w) = SymmetricAlgebra.ι R' W' (g w))
    (x : SymmetricAlgebra R W) :
    symmetricLinearPart R' W' (F x) = g (symmetricLinearPart R W x) := by
  suffices h : (symmetricSqZeroLift R' W' (F x)).fst = f (symmetricSqZeroLift R W x).fst ∧
      symmetricLinearPart R' W' (F x) = g (symmetricLinearPart R W x) from h.2
  induction x using SymmetricAlgebra.induction with
  | algebraMap r =>
    exact ⟨by rw [hF₁, fst_symmetricSqZeroLift_algebraMap, fst_symmetricSqZeroLift_algebraMap],
      by rw [hF₁, symmetricLinearPart_algebraMap, symmetricLinearPart_algebraMap, map_zero]⟩
  | ι w =>
    exact ⟨by rw [hF₂]; simp [symmetricSqZeroLift, SymmetricAlgebra.lift_ι_apply],
      by rw [hF₂, symmetricLinearPart_ι, symmetricLinearPart_ι]⟩
  | mul a b ha hb =>
    exact ⟨by simp [ha.1, hb.1],
      by rw [map_mul, symmetricLinearPart_mul, symmetricLinearPart_mul, ha.1, hb.1, ha.2, hb.2,
        map_add, g.map_smulₛₗ, g.map_smulₛₗ]⟩
  | add a b ha hb => exact ⟨by simp [ha.1, hb.1], by simp [ha.2, hb.2]⟩

end Naturality

section WeightCoaction

variable (R W)

/-- The weight coaction `Sym_R W → Sym_R W [ε]`, `w ↦ ε w`, with values in the square-zero
extension of the symmetric algebra by itself. -/
noncomputable def symmetricWeightCoaction :
    SymmetricAlgebra R W →ₐ[R] TrivSqZeroExt (SymmetricAlgebra R W) (SymmetricAlgebra R W) :=
  SymmetricAlgebra.lift
    ((inrHom (SymmetricAlgebra R W) (SymmetricAlgebra R W)).restrictScalars R ∘ₗ
      SymmetricAlgebra.ι R W)

/-- The comparison `R ⊕ W → Sym_R W [ε]`, `(r, w) ↦ (r, ι w)`. -/
noncomputable def symmetricSqZeroCompare :
    TrivSqZeroExt R W →ₐ[R]
      TrivSqZeroExt (SymmetricAlgebra R W) (SymmetricAlgebra R W) :=
  TrivSqZeroExt.lift (Algebra.ofId R _)
    ((inrHom (SymmetricAlgebra R W) (SymmetricAlgebra R W)).restrictScalars R ∘ₗ
      SymmetricAlgebra.ι R W)
    (fun x y => by simp)
    (fun r x => by
      simp [Algebra.smul_def])
    (fun r x => by
      change _ = _ * algebraMap R _ r
      simp [Algebra.smul_def, mul_comm])

variable {R W}

/-- **The `ε`-coefficient of the weight coaction is the projection to degree one.** -/
lemma snd_symmetricWeightCoaction (x : SymmetricAlgebra R W) :
    (symmetricWeightCoaction R W x).snd =
      SymmetricAlgebra.ι R W (symmetricLinearPart R W x) := by
  have h : (symmetricSqZeroCompare R W).comp (symmetricSqZeroLift R W) =
      symmetricWeightCoaction R W := by
    apply SymmetricAlgebra.algHom_ext
    refine LinearMap.ext fun w => ?_
    change symmetricSqZeroCompare R W (symmetricSqZeroLift R W (SymmetricAlgebra.ι R W w)) =
      symmetricWeightCoaction R W (SymmetricAlgebra.ι R W w)
    rw [symmetricSqZeroLift, SymmetricAlgebra.lift_ι_apply, symmetricWeightCoaction,
      SymmetricAlgebra.lift_ι_apply, symmetricSqZeroCompare]
    exact TrivSqZeroExt.lift_apply_inr _ _ _ _ _ w
  rw [← h, AlgHom.comp_apply, symmetricSqZeroCompare, TrivSqZeroExt.lift_def]
  simp only [symmetricLinearPart, Algebra.ofId_apply, TrivSqZeroExt.snd_add,
    LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars, inrHom_apply,
    snd_inr, AlgHom.toLinearMap_apply, sndHom_apply, add_eq_right]
  rw [IsScalarTower.algebraMap_apply R (SymmetricAlgebra R W), TrivSqZeroExt.algebraMap_eq_inl,
    snd_inl]

end WeightCoaction

end LinearPart

end AdequateFunctor

end
