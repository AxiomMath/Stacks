module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BaseFieldExtension.Kunneth
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BaseFieldExtension.Graded
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TraceDiagonal

/-!
# The linear algebra of axioms (A6) and (A9) along a field extension

This is the linear algebra principle of the proof of Tag 0FVT for axiom (A6): for `F`-vector
spaces `V`, `W`, `v ∈ V` and `ξ ∈ V ⊗_F W`, there is an `F`-linear `λ : W → F` with
`(1 ⊗ λ)ξ = v` if and only if there is an `F'`-linear `λ' : W ⊗_F F' → F'` with
`(1 ⊗ λ')ξ' = v'`. It is applied to the Künneth decomposition of a class `g ∈ H^*(X × X)(d)`
and of a class `g' ∈ (H')^*(X_{k'} × X_{k'})(d)` whose image in `(H')^*((X × X)_{k'})` is the
image of `g`, both read in the coordinates of the twists.

In one direction a trace `λ'` for `g'` gives a trace for `g` by composing with an `F`-linear
retraction `F' → F` of `F → F'`; in the other a trace `λ` for `g` extends to a trace `λ'` for
`g'` that restricts to `λ` up to the scalar comparing the coordinates of the twists. The second
direction is what the proof of (A9) uses.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct DirectSum Function

universe u w w'

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme

namespace FirstChernClassData

variable {k : Type u} [Field k] {F : Type w} [Field F] (𝔇 : FirstChernClassData k F)

/-- `untwistTrace` of a map read in the coordinate of the twist is that map on the projection. -/
theorem untwistTrace_comp_tateTwistCoordinates (X : (SmoothProjectiveScheme k).FullSubcategory)
    (d : ℕ) (ℓ : 𝔇.grade X (2 * (d : ℤ)) →ₗ[F] F) :
    𝔇.untwistTrace X d (ℓ ∘ₗ (tateTwistCoordinates 𝔇.coord (d : ℤ)).toLinearMap) =
      ℓ ∘ₗ 𝔇.projGrade X (2 * (d : ℤ)) := by
  ext b
  simp [untwistTrace]

/-- `untwistTrace` is the map read in coordinates on the projection. -/
theorem untwistTrace_eq (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (lam : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d →ₗ[F] F) :
    𝔇.untwistTrace X d lam =
      (lam ∘ₗ (tateTwistCoordinates 𝔇.coord (d : ℤ)).symm.toLinearMap) ∘ₗ
        𝔇.projGrade X (2 * (d : ℤ)) :=
  rfl

/-- The projection onto `H^n(X)` is the identity on `H^n(X)`. -/
theorem projGrade_coe (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) (x : 𝔇.grade X n) :
    𝔇.projGrade X n (x : 𝔇.H X) = x :=
  Subtype.ext (by rw [coe_projGrade]; exact decompose_of_mem_same _ x.2)

end FirstChernClassData

namespace DiagonalExpansion

variable {F : Type*} [Field F] {A : Type*} [Ring A] [Algebra F A]

/-- Contraction against `c • L` is `c` times contraction against `L`. -/
theorem contractRight_smul (c : F) (L : A →ₗ[F] F) (t : A ⊗[F] A) :
    contractRight (c • L) t = c • contractRight L t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [smul_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

end DiagonalExpansion

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
  {F : Type w} [Field F] {F' : Type w'} [Field F'] [Algebra F F']
  {𝔇 : FirstChernClassData k F} {𝔇' : FirstChernClassData k' F'}

namespace FieldExtensionComparison

variable (Φ : FieldExtensionComparison 𝔇 𝔇')

/-- The comparison of tensor products `F' ⊗_F (H^*(X) ⊗_F H^*(Y)) ≅ (H')^*(X_{k'}) ⊗_{F'}
(H')^*(Y_{k'})`. -/
def tensorIso (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    F' ⊗[F] (𝔇.H X ⊗[F] 𝔇.H Y) ≃ₗ[F']
      𝔇'.H ((baseChange k k').obj X) ⊗[F'] 𝔇'.H ((baseChange k k').obj Y) :=
  (TensorProduct.AlgebraTensorModule.distribBaseChange F F' (𝔇.H X) (𝔇.H Y)).trans
    (TensorProduct.congr (Φ.iso X).toLinearEquiv (Φ.iso Y).toLinearEquiv)

/-- `tensorIso` sends `1 ⊗ (a ⊗ b)` to `ρ(a) ⊗ ρ(b)`. -/
@[simp]
theorem tensorIso_tmul (X Y : (SmoothProjectiveScheme k).FullSubcategory) (a : 𝔇.H X) (b : 𝔇.H Y) :
    Φ.tensorIso X Y (1 ⊗ₜ (a ⊗ₜ b)) = Φ.ρ X a ⊗ₜ Φ.ρ Y b := by
  simp [tensorIso, ρ_apply]

/-- The Künneth maps are compatible with `tensorIso`. -/
theorem pull_kunnethMap_tensorIso (X Y : (SmoothProjectiveScheme k).FullSubcategory)
    (t : 𝔇.H X ⊗[F] 𝔇.H Y) :
    𝔇'.pull (baseChangeProdIso X Y).hom
        (𝔇'.kunnethMap ((baseChange k k').obj X) ((baseChange k k').obj Y)
          (Φ.tensorIso X Y (1 ⊗ₜ t))) =
      Φ.ρ (prod X Y) (𝔇.kunnethMap X Y t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [tensorIso_tmul, Φ.iso_kunnethMap]
  | add x y hx hy =>
    rw [TensorProduct.tmul_add, map_add, map_add, map_add, hx, hy, map_add, map_add]

/-- **The Künneth decompositions correspond**: if the image of `η' ∈ (H')^*(X'×Y')` in
`(H')^*((X × Y)_{k'})` is `c` times the image of `η ∈ H^*(X × Y)`, then the Künneth
decomposition of `η'` is `c` times the image of that of `η`. -/
theorem kunnethEquiv_symm_eq (hA5 : 𝔇.KunnethAxiom) (hA5' : 𝔇'.KunnethAxiom)
    (X Y : (SmoothProjectiveScheme k).FullSubcategory) (η : 𝔇.H (prod X Y))
    (η' : 𝔇'.H (prod ((baseChange k k').obj X) ((baseChange k k').obj Y))) (c : F')
    (h : 𝔇'.pull (baseChangeProdIso X Y).hom η' = c • Φ.ρ (prod X Y) η) :
    (𝔇'.kunnethEquiv hA5' _ _).symm η' =
      c • Φ.tensorIso X Y (1 ⊗ₜ (𝔇.kunnethEquiv hA5 X Y).symm η) := by
  rw [LinearEquiv.symm_apply_eq]
  apply (𝔇'.bijective_pull_of_iso (baseChangeProdIso X Y)).injective
  rw [h, map_smul]
  show c • Φ.ρ _ η = 𝔇'.pull _ (c • 𝔇'.kunnethMap _ _ _)
  rw [map_smul, pull_kunnethMap_tensorIso]
  congr 2
  exact ((𝔇.kunnethEquiv hA5 X Y).apply_symm_apply η).symm

/-- `b ↦ L'(ρ(b))`, an `F`-linear map `H^*(X) → F'`. -/
def restrictTrace (X : (SmoothProjectiveScheme k).FullSubcategory)
    (L' : 𝔇'.H ((baseChange k k').obj X) →ₗ[F'] F') : 𝔇.H X →ₗ[F] F' :=
  (L' ∘ₗ (Φ.iso X).toLinearMap).restrictScalars F ∘ₗ TensorProduct.mk F F' (𝔇.H X) 1

/-- `restrictTrace X L'` sends `b` to `L'(ρ(b))`. -/
theorem restrictTrace_apply (X : (SmoothProjectiveScheme k).FullSubcategory)
    (L' : 𝔇'.H ((baseChange k k').obj X) →ₗ[F'] F') (b : 𝔇.H X) :
    Φ.restrictTrace X L' b = L' (Φ.ρ X b) :=
  rfl

/-- `a ⊗ b ↦ L'(ρ(b)) ⊗ a`. -/
def contractAux (X : (SmoothProjectiveScheme k).FullSubcategory)
    (L' : 𝔇'.H ((baseChange k k').obj X) →ₗ[F'] F') :
    𝔇.H X ⊗[F] 𝔇.H X →ₗ[F] F' ⊗[F] 𝔇.H X :=
  (TensorProduct.comm F (𝔇.H X) F').toLinearMap ∘ₗ
    LinearMap.lTensor (𝔇.H X) (Φ.restrictTrace X L')

/-- `contractAux X L'` sends `a ⊗ b` to `L'(ρ(b)) ⊗ a`. -/
@[simp]
theorem contractAux_tmul (X : (SmoothProjectiveScheme k).FullSubcategory)
    (L' : 𝔇'.H ((baseChange k k').obj X) →ₗ[F'] F') (a b : 𝔇.H X) :
    Φ.contractAux X L' (a ⊗ₜ b) = L' (Φ.ρ X b) ⊗ₜ a :=
  rfl

/-- The image of `contractAux X L' t` under the comparison isomorphism is the contraction of the
image of `t` against `L'`. -/
theorem iso_contractAux (X : (SmoothProjectiveScheme k).FullSubcategory)
    (L' : 𝔇'.H ((baseChange k k').obj X) →ₗ[F'] F') (t : 𝔇.H X ⊗[F] 𝔇.H X) :
    Φ.iso X (Φ.contractAux X L' t) =
      DiagonalExpansion.contractRight L' (Φ.tensorIso X X (1 ⊗ₜ t)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [contractAux_tmul, tensorIso_tmul, DiagonalExpansion.contractRight_tmul, iso_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, TensorProduct.tmul_add, map_add, map_add]

/-- Applying an `F`-linear `π : F' → F` to the first factor of `contractAux X L' t` gives the
contraction of `t` against `π ∘ restrictTrace X L'`. -/
theorem lid_rTensor_contractAux (X : (SmoothProjectiveScheme k).FullSubcategory)
    (L' : 𝔇'.H ((baseChange k k').obj X) →ₗ[F'] F') (π : F' →ₗ[F] F)
    (t : 𝔇.H X ⊗[F] 𝔇.H X) :
    TensorProduct.lid F (𝔇.H X) (LinearMap.rTensor (𝔇.H X) π (Φ.contractAux X L' t)) =
      DiagonalExpansion.contractRight (π ∘ₗ Φ.restrictTrace X L') t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [restrictTrace_apply]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

/-- If `L'(ρ(b)) = c · L(b)` for all `b`, then `contractAux X L' t` is `c • (1 ⊗ t')`, where `t'`
is the contraction of `t` against `L`. -/
theorem contractAux_of_eq (X : (SmoothProjectiveScheme k).FullSubcategory)
    (L' : 𝔇'.H ((baseChange k k').obj X) →ₗ[F'] F') (L : 𝔇.H X →ₗ[F] F) (c : F')
    (hL : ∀ b, L' (Φ.ρ X b) = c * algebraMap F F' (L b)) (t : 𝔇.H X ⊗[F] 𝔇.H X) :
    Φ.contractAux X L' t = c • (1 ⊗ₜ DiagonalExpansion.contractRight L t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [contractAux_tmul, hL, DiagonalExpansion.contractRight_tmul, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, Algebra.smul_def, mul_one]
  | add x y hx hy => rw [map_add, map_add, hx, hy, TensorProduct.tmul_add, smul_add]

/-- The image of a class of `H^n(X)` lies in `(H')^n(X_{k'})`. -/
def ρGrade (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) (x : 𝔇.grade X n) :
    𝔇'.grade ((baseChange k k').obj X) n :=
  ⟨Φ.ρ X x, Φ.iso_grade X n x x.2⟩

/-- `ρGrade X n x` is the image of `1 ⊗ x` under `gradeEquiv X n`. -/
theorem ρGrade_eq_gradeEquiv (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ)
    (x : 𝔇.grade X n) :
    Φ.ρGrade X n x = Φ.gradeEquiv X n (1 ⊗ₜ x) :=
  Subtype.ext (Φ.coe_gradeEquiv_tmul X n 1 x).symm

/-- The projection onto `(H')^n(X_{k'})` of `ρ(b)` is the image of the projection of `b` onto
`H^n(X)`. -/
theorem projGrade_ρ (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) (b : 𝔇.H X) :
    𝔇'.projGrade _ n (Φ.ρ X b) = Φ.ρGrade X n (𝔇.projGrade X n b) :=
  Subtype.ext (by
    show (𝔇'.projGrade _ n (Φ.ρ X b) : 𝔇'.H _) = Φ.iso X (1 ⊗ₜ (𝔇.projGrade X n b : 𝔇.H X))
    rw [FirstChernClassData.coe_projGrade, FirstChernClassData.coe_projGrade, Φ.iso_decompose]
    rfl)

/-- `untwistTrace` of `ρ` of the projection of `b` onto `H^{2d}(X)` equals `untwistTrace` of
`ρ(b)`. -/
theorem untwistTrace_ρ_projGrade (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (lam' : tateTwist F' 𝔇'.tate (𝔇'.grade ((baseChange k k').obj X) (2 * (d : ℤ))) d →ₗ[F'] F')
    (b : 𝔇.H X) :
    𝔇'.untwistTrace _ d lam' (Φ.ρ X (𝔇.projGrade X (2 * (d : ℤ)) b)) =
      𝔇'.untwistTrace _ d lam' (Φ.ρ X b) := by
  simp only [FirstChernClassData.untwistTrace_eq, LinearMap.coe_comp, Function.comp_apply]
  rw [Φ.projGrade_ρ, Φ.projGrade_ρ, FirstChernClassData.projGrade_coe]

/-! ### (A6): a trace for `g'` gives a trace for `g` -/

/-- Under `hg`, `traceContract` of `g'` is the contraction of the scaled image of the Künneth
decomposition of `g`. -/
private theorem traceContract_eq_contractRight_smul (hA5 : 𝔇.KunnethAxiom)
    (hA5' : 𝔇'.KunnethAxiom) (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (g : tateTwist F 𝔇.tate (𝔇.H (prod X X)) d)
    (g' : tateTwist F' 𝔇'.tate
      (𝔇'.H (prod ((baseChange k k').obj X) ((baseChange k k').obj X))) d)
    (hg : 𝔇'.pull (baseChangeProdIso X X).hom (𝔇'.κ _ d g') =
      Φ.tateUnit ^ (d : ℤ) • Φ.ρ (prod X X) (𝔇.κ _ d g))
    (lam' : tateTwist F' 𝔇'.tate (𝔇'.grade ((baseChange k k').obj X) (2 * (d : ℤ))) d →ₗ[F'] F') :
    𝔇'.traceContract hA5' _ d lam' g' =
      DiagonalExpansion.contractRight (𝔇'.untwistTrace _ d lam')
        (Φ.tateUnit ^ (d : ℤ) •
          Φ.tensorIso X X (1 ⊗ₜ (𝔇.kunnethEquiv hA5 X X).symm (𝔇.κ _ d g))) := by
  simp only [FirstChernClassData.traceContract, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, Φ.kunnethEquiv_symm_eq hA5 hA5' X X _ _ _ hg, map_smul]

/-- **The linear algebra principle of (A6), descent direction.** Let `g ∈ H^*(X × X)(d)` and
`g' ∈ (H')^*(X_{k'} × X_{k'})(d)` have the same image in `(H')^*((X × X)_{k'})`, up to the
scalar `u^d` comparing the coordinates of the twists. If `(1 ⊗ λ')g' = 1` for an `F'`-linear
`λ'`, then `(1 ⊗ λ)g = 1` for an `F`-linear `λ`. -/
theorem exists_traceContract_eq_one (hA5 : 𝔇.KunnethAxiom) (hA5' : 𝔇'.KunnethAxiom)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (g : tateTwist F 𝔇.tate (𝔇.H (prod X X)) d)
    (g' : tateTwist F' 𝔇'.tate
      (𝔇'.H (prod ((baseChange k k').obj X) ((baseChange k k').obj X))) d)
    (hg : 𝔇'.pull (baseChangeProdIso X X).hom (𝔇'.κ _ d g') =
      Φ.tateUnit ^ (d : ℤ) • Φ.ρ (prod X X) (𝔇.κ _ d g))
    (lam' : tateTwist F' 𝔇'.tate (𝔇'.grade ((baseChange k k').obj X) (2 * (d : ℤ))) d →ₗ[F'] F')
    (hlam' : 𝔇'.traceContract hA5' _ d lam' g' = 1) :
    ∃ lam : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d →ₗ[F] F,
      𝔇.traceContract hA5 X d lam g = 1 := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F F')
    (LinearMap.ker_eq_bot.mpr (algebraMap F F').injective)
  have hπ1 : π 1 = 1 := by simpa using LinearMap.congr_fun hπ 1
  set L' := 𝔇'.untwistTrace _ d lam'
  set c : F' := Φ.tateUnit ^ (d : ℤ)
  let ℓ : 𝔇.grade X (2 * (d : ℤ)) →ₗ[F] F :=
    π ∘ₗ Φ.restrictTrace X (c • L') ∘ₗ (𝔇.grade X (2 * (d : ℤ))).subtype
  refine ⟨ℓ ∘ₗ (tateTwistCoordinates 𝔇.coord (d : ℤ)).toLinearMap, ?_⟩
  have hL : 𝔇.untwistTrace X d (ℓ ∘ₗ (tateTwistCoordinates 𝔇.coord (d : ℤ)).toLinearMap) =
      π ∘ₗ Φ.restrictTrace X (c • L') := by
    rw [FirstChernClassData.untwistTrace_comp_tateTwistCoordinates]
    refine LinearMap.ext fun b => ?_
    simp only [ℓ, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      restrictTrace_apply, LinearMap.smul_apply]
    rw [Φ.untwistTrace_ρ_projGrade]
  set t := (𝔇.kunnethEquiv hA5 X X).symm (𝔇.κ _ d g)
  have h1 : Φ.contractAux X (c • L') t = 1 ⊗ₜ 1 := by
    apply (Φ.iso X).injective
    rw [iso_contractAux, ← Algebra.TensorProduct.one_def, map_one, ← hlam',
      Φ.traceContract_eq_contractRight_smul hA5 hA5' X d g g' hg, map_smul,
      DiagonalExpansion.contractRight_smul]
  have h2 := congrArg (fun x => TensorProduct.lid F (𝔇.H X) (LinearMap.rTensor (𝔇.H X) π x)) h1
  simp only [lid_rTensor_contractAux, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, hπ1,
    one_smul] at h2
  simpa only [FirstChernClassData.traceContract, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, hL] using h2

/-! ### (A9): a trace for `g` extends to a trace for `g'` -/

/-- **The linear algebra principle of (A6), extension direction.** In the situation of
`exists_traceContract_eq_one`, a trace `λ` with `(1 ⊗ λ)g = 1` extends to a trace `λ'` with
`(1 ⊗ λ')g' = 1`, and `λ'(b') = u^{-d} λ(b)` for the image `b'` of `b ∈ H^*(X)`. -/
theorem exists_traceContract_eq_one_extend (hA5 : 𝔇.KunnethAxiom) (hA5' : 𝔇'.KunnethAxiom)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (g : tateTwist F 𝔇.tate (𝔇.H (prod X X)) d)
    (g' : tateTwist F' 𝔇'.tate
      (𝔇'.H (prod ((baseChange k k').obj X) ((baseChange k k').obj X))) d)
    (hg : 𝔇'.pull (baseChangeProdIso X X).hom (𝔇'.κ _ d g') =
      Φ.tateUnit ^ (d : ℤ) • Φ.ρ (prod X X) (𝔇.κ _ d g))
    (lam : tateTwist F 𝔇.tate (𝔇.grade X (2 * (d : ℤ))) d →ₗ[F] F)
    (hlam : 𝔇.traceContract hA5 X d lam g = 1) :
    ∃ lam' : tateTwist F' 𝔇'.tate (𝔇'.grade ((baseChange k k').obj X) (2 * (d : ℤ))) d →ₗ[F'] F',
      𝔇'.traceContract hA5' _ d lam' g' = 1 ∧
        ∀ b : 𝔇.H X, 𝔇'.untwistTrace _ d lam' (Φ.ρ X b) =
          (Φ.tateUnit ^ (d : ℤ))⁻¹ * algebraMap F F' (𝔇.untwistTrace X d lam b) := by
  set c : F' := Φ.tateUnit ^ (d : ℤ)
  have hc : c ≠ 0 := zpow_ne_zero _ Φ.tateUnit_ne_zero
  set ℓ := lam ∘ₗ (tateTwistCoordinates 𝔇.coord (d : ℤ)).symm.toLinearMap
  let ℓ' : 𝔇'.grade ((baseChange k k').obj X) (2 * (d : ℤ)) →ₗ[F'] F' :=
    c⁻¹ • ((TensorProduct.AlgebraTensorModule.rid F F' F').toLinearMap ∘ₗ ℓ.baseChange F') ∘ₗ
      (Φ.gradeEquiv X (2 * (d : ℤ))).symm.toLinearMap
  have hL : ∀ b : 𝔇.H X, 𝔇'.untwistTrace _ d
      (ℓ' ∘ₗ (tateTwistCoordinates 𝔇'.coord (d : ℤ)).toLinearMap) (Φ.ρ X b) =
      c⁻¹ * algebraMap F F' (𝔇.untwistTrace X d lam b) := fun b => by
    rw [FirstChernClassData.untwistTrace_comp_tateTwistCoordinates]
    simp only [ℓ', LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
      LinearEquiv.coe_coe, Φ.projGrade_ρ, Φ.ρGrade_eq_gradeEquiv, LinearEquiv.symm_apply_apply,
      LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.rid_tmul, smul_eq_mul,
      Algebra.smul_def, mul_one, FirstChernClassData.untwistTrace_eq, ℓ]
  refine ⟨ℓ' ∘ₗ (tateTwistCoordinates 𝔇'.coord (d : ℤ)).toLinearMap, ?_, hL⟩
  set t := (𝔇.kunnethEquiv hA5 X X).symm (𝔇.κ _ d g)
  have h1 := Φ.contractAux_of_eq X _ _ c⁻¹ hL t
  have h2 : DiagonalExpansion.contractRight (𝔇.untwistTrace X d lam) t = 1 := by
    simpa [FirstChernClassData.traceContract, t] using hlam
  rw [Φ.traceContract_eq_contractRight_smul hA5 hA5' X d g g' hg, map_smul,
    ← iso_contractAux, h1, h2, map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul,
    ← Algebra.TensorProduct.one_def, map_one]

end FieldExtensionComparison

end Stacks.WeilCohomology
