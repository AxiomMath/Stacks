module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTripleCoordinates
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# The antidiagonal `Q_Δ` is the affine line over `𝔸¹_u`

Let `Q = 𝔸¹_x ×_k 𝔸¹_t ×_k 𝔸¹_u` and `Q_Δ = {x + u = 0} = Spec k[x, t]` (`u = -x`), the support
of the kernel of the composite of two Fourier transforms
(`Stacks.EtaleCohomology.fourierAntidiagonal`). The projection `u : Q_Δ ⟶ 𝔸¹_u` makes `Q_Δ` the
affine line over `𝔸¹_u` with coordinate `t`: the square

`Q_Δ --t--> 𝔸¹`, `Q_Δ --u--> 𝔸¹_u`, `𝔸¹ ⟶ Spec k`, `𝔸¹_u ⟶ Spec k`

is cartesian, since `k[x, t] = k[u] ⊗_k k[t]` with `u ↦ -x`. Moreover the coordinate `x` of
`Q_Δ` is `u` followed by the negation `X ↦ -X` of the affine line.

The ring of the coordinate `t` is presented as `k[X₀] = MvPolynomial (Fin 1) k`, so that the
pushout `k[u] ⊗_k k[X₀] = k[u][X₀]` involves no `Algebra k[X] k[X][X]` instance (whose two
candidate structures, `C` and `map C`, do not agree); it is identified with `k[X]` afterwards.

## Main results

* `Stacks.EtaleCohomology.fourierAntidiagonalRelEquiv`: `k[u][X₀] ≃ k[x, t]`.
* `Stacks.EtaleCohomology.isPushout_fourierAntidiagonal`: `k[x, t] = k[u] ⊗_k k[t]`.
* `Stacks.EtaleCohomology.affineLineNeg`: `X ↦ -X` on `𝔸¹_k`.
* `Stacks.EtaleCohomology.isPullback_fourierAntidiagonal`: `Q_Δ` is the affine line over `𝔸¹_u`.
* `Stacks.EtaleCohomology.fourierAntidiagonalProjX_eq`: `x = -u` on `Q_Δ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

open Stacks.Blowup Stacks.ArtinSchreier

variable (k : Type u) [Field k]

local notation "𝔸f" => affineLineStructureMap k

/-! ### Rings -/

/-- The `k`-algebra map `k[X] → k[x, t]`, `X ↦ -x`: the coordinate `u = -x` of `Q_Δ`. -/
abbrev fourierAntidiagonalU : Polynomial k →ₐ[k] MvPolynomial (Fin 2) k :=
  Polynomial.aeval (-MvPolynomial.X 0)

/-- The `k`-algebra map `k[X] → k[x, t]`, `X ↦ t`: the coordinate `t` of `Q_Δ`. -/
abbrev fourierAntidiagonalT : Polynomial k →ₐ[k] MvPolynomial (Fin 2) k :=
  Polynomial.aeval (MvPolynomial.X 1)

/-- The ring map `k[u][X₀] → k[x, t]`, `u ↦ -x`, `X₀ ↦ t`. -/
def fourierAntidiagonalRelHom : MvPolynomial (Fin 1) (Polynomial k) →+* MvPolynomial (Fin 2) k :=
  MvPolynomial.eval₂Hom (fourierAntidiagonalU k).toRingHom fun _ => MvPolynomial.X 1

/-- The ring map `k[x, t] → k[u][X₀]`, `x ↦ -u`, `t ↦ X₀`. -/
def fourierAntidiagonalRelInv : MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 1) (Polynomial k) :=
  (MvPolynomial.aeval ![-MvPolynomial.C Polynomial.X, MvPolynomial.X 0] :
    MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 1) (Polynomial k)).toRingHom

/-- `fourierAntidiagonalRelHom` sends a constant `p ∈ k[u]` to `p(-x)`. -/
theorem fourierAntidiagonalRelHom_C (p : Polynomial k) :
    fourierAntidiagonalRelHom k (MvPolynomial.C p) = fourierAntidiagonalU k p :=
  MvPolynomial.eval₂Hom_C _ _ _

/-- `fourierAntidiagonalRelHom` sends the variable `X₀` to `t`. -/
theorem fourierAntidiagonalRelHom_X (i : Fin 1) :
    fourierAntidiagonalRelHom k (MvPolynomial.X i) = MvPolynomial.X 1 :=
  MvPolynomial.eval₂Hom_X' _ _ _

/-- The composite `k[u] → k[x, t] → k[u][X₀]`, `u ↦ -x ↦ u`, is the inclusion of constants. -/
theorem fourierAntidiagonalRelInv_comp_U :
    (fourierAntidiagonalRelInv k).comp (fourierAntidiagonalU k).toRingHom = MvPolynomial.C := by
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp [fourierAntidiagonalRelInv, MvPolynomial.algebraMap_eq]
  · simp [fourierAntidiagonalRelInv]

/-- `fourierAntidiagonalRelHom` is a left inverse of `fourierAntidiagonalRelInv`. -/
theorem fourierAntidiagonalRelHom_comp_inv :
    (fourierAntidiagonalRelHom k).comp (fourierAntidiagonalRelInv k) = RingHom.id _ := by
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
  · simp [fourierAntidiagonalRelInv, fourierAntidiagonalRelHom, MvPolynomial.algebraMap_eq]
  · fin_cases i <;> simp [fourierAntidiagonalRelInv, fourierAntidiagonalRelHom]

/-- `fourierAntidiagonalRelInv` is a left inverse of `fourierAntidiagonalRelHom`. -/
theorem fourierAntidiagonalRelInv_comp :
    (fourierAntidiagonalRelInv k).comp (fourierAntidiagonalRelHom k) = RingHom.id _ := by
  refine MvPolynomial.ringHom_ext (fun p => ?_) (fun i => ?_)
  · rw [RingHom.comp_apply, fourierAntidiagonalRelHom_C]
    exact RingHom.congr_fun (fourierAntidiagonalRelInv_comp_U k) p
  · rw [RingHom.comp_apply, fourierAntidiagonalRelHom_X, Subsingleton.elim i 0]
    simp [fourierAntidiagonalRelInv]

/-- **`k[u][X₀] ≃ k[x, t]`**, `u ↦ -x`, `X₀ ↦ t`. -/
def fourierAntidiagonalRelEquiv : MvPolynomial (Fin 1) (Polynomial k) ≃+* MvPolynomial (Fin 2) k :=
  RingEquiv.ofRingHom (fourierAntidiagonalRelHom k) (fourierAntidiagonalRelInv k)
    (fourierAntidiagonalRelHom_comp_inv k) (fourierAntidiagonalRelInv_comp k)

attribute [local instance] MvPolynomial.algebraMvPolynomial in
/-- **`k[x, t] = k[u] ⊗_k k[t]`**, `u ↦ -x`: a pushout of commutative rings. -/
theorem isPushout_fourierAntidiagonal :
    IsPushout (CommRingCat.ofHom (algebraMap k (Polynomial k)))
      (CommRingCat.ofHom (algebraMap k (Polynomial k)))
      (CommRingCat.ofHom (fourierAntidiagonalU k).toRingHom)
      (CommRingCat.ofHom (fourierAntidiagonalT k).toRingHom) := by
  have h₀ := CommRingCat.isPushout_of_isPushout k (Polynomial k) (MvPolynomial (Fin 1) k)
    (MvPolynomial (Fin 1) (Polynomial k))
  let φ := MvPolynomial.uniqueAlgEquiv k (Fin 1)
  refine h₀.of_iso (Iso.refl _) (Iso.refl _) φ.toRingEquiv.toCommRingCatIso
    (fourierAntidiagonalRelEquiv k).toCommRingCatIso (by simp) ?_ ?_ ?_
  · refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
    exact φ.commutes c
  · refine CommRingCat.hom_ext (RingHom.ext fun p => ?_)
    exact fourierAntidiagonalRelHom_C k p
  · refine CommRingCat.hom_ext (MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_))
    · change fourierAntidiagonalRelHom k (MvPolynomial.map (algebraMap k (Polynomial k))
          (MvPolynomial.C c)) = fourierAntidiagonalT k (φ (MvPolynomial.C c))
      rw [MvPolynomial.map_C, fourierAntidiagonalRelHom_C, ← MvPolynomial.algebraMap_eq,
        φ.commutes, AlgHom.commutes, AlgHom.commutes]
    · change fourierAntidiagonalRelHom k (MvPolynomial.map (algebraMap k (Polynomial k))
          (MvPolynomial.X i)) = fourierAntidiagonalT k (φ (MvPolynomial.X i))
      rw [MvPolynomial.map_X, fourierAntidiagonalRelHom_X]
      change _ = fourierAntidiagonalT k (φ (MvPolynomial.monomial (Finsupp.single i 1) 1))
      rw [MvPolynomial.uniqueAlgEquiv_monomial, Subsingleton.elim (default : Fin 1) i,
        Finsupp.single_eq_same, Polynomial.monomial_one_one_eq_X, Polynomial.aeval_X]

/-! ### Schemes -/

/-- **The negation `X ↦ -X` of the affine line**. -/
abbrev affineLineNeg :
    Spec (CommRingCat.of (Polynomial k)) ⟶ Spec (CommRingCat.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval (-Polynomial.X : Polynomial k)).toRingHom)

/-- The negation of the affine line is an involution. -/
theorem affineLineNeg_comp_affineLineNeg : affineLineNeg k ≫ affineLineNeg k = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  refine CommRingCat.hom_ext (Polynomial.ringHom_ext (fun c => ?_) ?_) <;> simp

/-- The negation of the affine line is an isomorphism (an involution). -/
instance isIso_affineLineNeg : IsIso (affineLineNeg k) :=
  ⟨affineLineNeg k, affineLineNeg_comp_affineLineNeg k, affineLineNeg_comp_affineLineNeg k⟩

/-- The coordinate `u : Q_Δ ⟶ 𝔸¹`. -/
abbrev fourierAntidiagonalProjU : fourierAntidiagonal k ⟶ Spec (CommRingCat.of (Polynomial k)) :=
  fourierAntidiagonalι k ≫ tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd _ _

/-- The coordinate `x : Q_Δ ⟶ 𝔸¹`. -/
abbrev fourierAntidiagonalProjX : fourierAntidiagonal k ⟶ Spec (CommRingCat.of (Polynomial k)) :=
  fourierAntidiagonalι k ≫ tripleProduct₁₂ 𝔸f 𝔸f 𝔸f ≫ pullback.fst _ _

/-- The `i`-th coordinate of `Q ≅ 𝔸³` restricted to `Q_Δ` is `Spec φ` composed with
`Q_Δ ⟶ Spec k[x, t]`, for any `k`-algebra map `φ : k[X] → k[x, t]` sending `X` to the image of
the `i`-th variable in `k[x, t]`. -/
theorem fourierAntidiagonal_coordinate_eq (i : Fin 3)
    (φ : Polynomial k →ₐ[k] MvPolynomial (Fin 2) k)
    (hφ : φ Polynomial.X = fourierAntidiagonalRingHom k (MvPolynomial.X i)) :
    fourierAntidiagonalι k ≫ fourierTripleCoords k ≫ affineSpaceCoordinate k i =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) := by
  rw [← Category.assoc, pullback.condition, Category.assoc, ← Spec.map_comp]
  congr 2
  refine CommRingCat.hom_ext (Polynomial.ringHom_ext (fun c => ?_) ?_)
  · change fourierAntidiagonalRingHom k (Polynomial.aeval (MvPolynomial.X i) (Polynomial.C c)) =
      φ (Polynomial.C c)
    rw [Polynomial.aeval_C, AlgHom.commutes, ← Polynomial.algebraMap_eq, AlgHom.commutes]
  · change fourierAntidiagonalRingHom k (Polynomial.aeval (MvPolynomial.X i) Polynomial.X) =
      φ Polynomial.X
    rw [Polynomial.aeval_X, hφ]

/-- **The coordinate `u` of `Q_Δ`** through `Q_Δ ≅ Spec k[x, t]`: `u = -x`. -/
theorem fourierAntidiagonalProjU_eq :
    fourierAntidiagonalProjU k =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (fourierAntidiagonalU k).toRingHom) := by
  have h := fourierTripleCoords_comp_affineSpaceCoordinate k 2
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h
  rw [fourierAntidiagonalProjU, ← h]
  exact fourierAntidiagonal_coordinate_eq k 2 _ (by simp)

/-- **The coordinate `x` of `Q_Δ` is `-u`**. -/
theorem fourierAntidiagonalProjX_eq :
    fourierAntidiagonalProjX k = fourierAntidiagonalProjU k ≫ affineLineNeg k := by
  have h := fourierTripleCoords_comp_affineSpaceCoordinate k 0
  simp only [Matrix.cons_val_zero] at h
  rw [fourierAntidiagonalProjX, ← h, fourierAntidiagonal_coordinate_eq k 0
    (Polynomial.aeval (MvPolynomial.X 0)) (by simp), fourierAntidiagonalProjU_eq, Category.assoc,
    ← Spec.map_comp]
  congr 2
  refine CommRingCat.hom_ext (Polynomial.ringHom_ext (fun c => ?_) ?_) <;> simp

/-- `Q_Δ ⟶ Spec k[x, t]` is an isomorphism: it is the base change of the isomorphism
`Q ≅ Spec k[x, t, u]`. -/
instance isIso_fourierAntidiagonal_snd :
    IsIso (pullback.snd (fourierTripleCoords k)
      (Spec.map (CommRingCat.ofHom (fourierAntidiagonalRingHom k).toRingHom))) :=
  inferInstance

/-- **`Q_Δ` is the affine line over `𝔸¹_u`**: with the coordinate `t`, the square
`Q_Δ --t--> 𝔸¹`, `Q_Δ --u--> 𝔸¹_u` over `Spec k` is cartesian. -/
theorem isPullback_fourierAntidiagonal :
    IsPullback (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (fourierAntidiagonalT k).toRingHom))
      (fourierAntidiagonalProjU k) 𝔸f 𝔸f := by
  have h := (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_fourierAntidiagonal k)).flip
  rw [fourierAntidiagonalProjU_eq]
  exact h.of_iso (asIso (pullback.snd (fourierTripleCoords k)
      (Spec.map (CommRingCat.ofHom (fourierAntidiagonalRingHom k).toRingHom)))).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)

end Stacks.EtaleCohomology

end
