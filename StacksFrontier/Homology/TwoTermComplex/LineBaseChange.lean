module

public import Mathlib.LinearAlgebra.Contraction
public import StacksFrontier.Algebra.Module.Projective.Determinant.BaseChange
public import StacksFrontier.Homology.TwoTermComplex.DeterminantLine

/-!
# Base change of the determinant line of a two-term complex

Let `R → S` be a ring map and `K : K₁ → K₀` a two-term complex of finite projective
`R`-modules. Its determinant line `det K₀ ⊗ (det K₁)⁻¹ = Hom(det K₁, det K₀)` commutes with base
change: `S ⊗_R det(K) ≅ det(K ⊗_R S)`, compatibly with the canonical element of a rank-zero
complex.

## Main definitions

* `TwoTermComplex.lineCongr`: the equivalence of determinant lines induced by an isomorphism of
  two-term complexes.
* `TwoTermComplex.homBaseChangeEquiv`: `S ⊗_R Hom_R(M, N) ≅ Hom_S(S ⊗_R M, S ⊗_R N)` for `M`
  finite projective.
* `TwoTermComplex.lineBaseChange`: `S ⊗_R det(K) ≅ det(K ⊗_R S)`.
* `TwoTermComplex.Hom.baseChange`: the base change of a morphism of two-term complexes.

## Main results

* `ProjectiveDeterminant.exteriorAlgebraBaseChange_comp_map` and
  `ProjectiveDeterminant.baseChangeEquiv_comp_baseChange_map`: naturality of the base change of
  exterior algebras and of determinant lines of modules.
* `TwoTermComplex.lineBaseChange_delta`: base change of determinant lines preserves the canonical
  element.

## References

* [Stacks Project, Section 15.87 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

/-! ### Base change of the determinant line of a module -/

namespace ProjectiveDeterminant

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The base-change comparison of exterior algebras is natural in the module. -/
theorem exteriorAlgebraBaseChange_comp_map (f : M →ₗ[R] N) :
    (exteriorAlgebraBaseChange R A N).toAlgHom.comp (ExteriorAlgebra.map (f.baseChange A)) =
      (Algebra.TensorProduct.map (AlgHom.id A A) (ExteriorAlgebra.map f)).comp
        (exteriorAlgebraBaseChange R A M).toAlgHom := by
  apply ExteriorAlgebra.hom_ext
  apply TensorProduct.AlgebraTensorModule.ext
  intro a m
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    AlgHom.coe_comp, AlgEquiv.coe_algHom]
  rw [TensorProduct.tmul_eq_smul_one_tmul a m, map_smul, map_smul, ExteriorAlgebra.map_apply_ι,
    LinearMap.baseChange_tmul, map_smul, exteriorAlgebraBaseChange_ι,
    map_smul, exteriorAlgebraBaseChange_ι, map_smul, Algebra.TensorProduct.map_tmul,
    ExteriorAlgebra.map_apply_ι]
  rfl

variable [Module.Finite R M] [Module.Projective R M] [Module.Finite R N] [Module.Projective R N]

/-- The base-change comparison of determinant lines is natural for the determinant maps. -/
theorem baseChangeEquiv_comp_baseChange_map
    (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = Module.rankAtStalk N p)
    (h' : ∀ p : PrimeSpectrum A,
      Module.rankAtStalk (A ⊗[R] M) p = Module.rankAtStalk (A ⊗[R] N) p) (f : M →ₗ[R] N) :
    (baseChangeEquiv (R := R) (A := A) (M := N)).toLinearMap ∘ₗ (map h f).baseChange A =
      map h' (f.baseChange A) ∘ₗ (baseChangeEquiv (R := R) (A := A) (M := M)).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  apply Subtype.ext
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.baseChange_tmul]
  rw [coe_baseChangeEquiv_tmul]
  show _ = ExteriorAlgebra.map (f.baseChange A) (baseChangeEquiv (R := R) (A := A) (M := M)
    (a ⊗ₜ[R] x) : ExteriorAlgebra A (A ⊗[R] M))
  rw [coe_baseChangeEquiv_tmul]
  apply (exteriorAlgebraBaseChange R A N).injective
  rw [AlgEquiv.apply_symm_apply]
  have := congrArg (fun φ => φ ((exteriorAlgebraBaseChange R A M).symm (a ⊗ₜ[R] (x : _))))
    (exteriorAlgebraBaseChange_comp_map A f)
  simp only [AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_algHom,
    AlgEquiv.apply_symm_apply, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq] at this
  rw [this]
  rfl

section Transitivity

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  (C : Type u) [CommRing C] [Algebra R C] [Algebra A C] [IsScalarTower R A C]
variable {M : Type u} [AddCommGroup M] [Module R M]

/-- In `A ⊗_R Λ(M)`, the element `1 ⊗ r` for `r ∈ R` is the image of `r` under the algebra map
`R → A ⊗_R Λ(M)`. -/
theorem one_tmul_algebraMap (r : R) :
    ((1 : A) ⊗ₜ[R] (algebraMap R (ExteriorAlgebra R M) r) : A ⊗[R] ExteriorAlgebra R M) =
      algebraMap A (A ⊗[R] ExteriorAlgebra R M) (algebraMap R A r) := by
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]

/-- **Transitivity of the base change of exterior algebras.** -/
theorem exteriorAlgebraBaseChange_trans (w : ExteriorAlgebra R M) :
    ExteriorAlgebra.map (TensorProduct.AlgebraTensorModule.cancelBaseChange R A C C M).toLinearMap
        ((exteriorAlgebraBaseChange A C (A ⊗[R] M)).symm ((1 : C) ⊗ₜ[A]
          (exteriorAlgebraBaseChange R A M).symm ((1 : A) ⊗ₜ[R] w))) =
      (exteriorAlgebraBaseChange R C M).symm ((1 : C) ⊗ₜ[R] w) := by
  have hsymm (R' A' : Type u) [CommRing R'] [CommRing A'] [Algebra R' A'] (N : Type u)
      [AddCommGroup N] [Module R' N] (n : N) :
      (exteriorAlgebraBaseChange R' A' N).symm ((1 : A') ⊗ₜ[R'] ExteriorAlgebra.ι R' n) =
        ExteriorAlgebra.ι A' ((1 : A') ⊗ₜ[R'] n) := by
    rw [AlgEquiv.symm_apply_eq, exteriorAlgebraBaseChange_ι]
  have hmul (R' A' : Type u) [CommRing R'] [CommRing A'] [Algebra R' A'] (E : Type u) [Ring E]
      [Algebra R' E] (a b : E) :
      ((1 : A') ⊗ₜ[R'] (a * b) : A' ⊗[R'] E) = ((1 : A') ⊗ₜ[R'] a) * ((1 : A') ⊗ₜ[R'] b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  induction w using ExteriorAlgebra.induction with
  | algebraMap r =>
    rw [one_tmul_algebraMap, AlgEquiv.commutes, one_tmul_algebraMap, AlgEquiv.commutes,
      AlgHom.commutes, one_tmul_algebraMap, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply R A C]
  | ι m =>
    rw [hsymm, hsymm, ExteriorAlgebra.map_apply_ι, hsymm]
    congr 1
    rw [LinearEquiv.coe_coe, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  | mul a b ha hb => rw [hmul, map_mul, hmul, map_mul, map_mul, ha, hb, hmul, map_mul]
  | add a b ha hb => rw [TensorProduct.tmul_add, map_add, TensorProduct.tmul_add, map_add,
      map_add, ha, hb, TensorProduct.tmul_add, map_add]

/-- **Transitivity of the base change of determinant lines of modules.** -/
theorem baseChangeEquiv_trans [Module.Finite R M] [Module.Projective R M]
    (x : module (R := R) (M := M)) :
    mapEquiv (TensorProduct.AlgebraTensorModule.cancelBaseChange R A C C M)
        (baseChangeEquiv (R := A) (A := C) (M := A ⊗[R] M)
          ((1 : C) ⊗ₜ[A] baseChangeEquiv (R := R) (A := A) (M := M) ((1 : A) ⊗ₜ[R] x))) =
      baseChangeEquiv (R := R) (A := C) (M := M) ((1 : C) ⊗ₜ[R] x) := by
  apply Subtype.ext
  show ExteriorAlgebra.map
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R A C C M).toLinearMap
      (baseChangeEquiv (R := A) (A := C) (M := A ⊗[R] M) ((1 : C) ⊗ₜ[A]
        baseChangeEquiv (R := R) (A := A) (M := M) ((1 : A) ⊗ₜ[R] x)) :
          ExteriorAlgebra C (C ⊗[A] (A ⊗[R] M))) = _
  rw [coe_baseChangeEquiv_tmul, coe_baseChangeEquiv_tmul, coe_baseChangeEquiv_tmul]
  exact exteriorAlgebraBaseChange_trans A C x.1

end Transitivity

end ProjectiveDeterminant

/-! ### Base change of the determinant line of a two-term complex -/

namespace TwoTermComplex

/-! ### Determinant lines of isomorphic two-term complexes -/

section LineCongr

variable {R : Type*} [CommRing R]
variable {K₁ K₀ L₁ L₀ : Type*}
variable [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
variable [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]
variable [AddCommGroup L₁] [Module R L₁] [Module.Finite R L₁] [Module.Projective R L₁]
variable [AddCommGroup L₀] [Module R L₀] [Module.Finite R L₀] [Module.Projective R L₀]

/-- The equivalence of determinant lines induced by an isomorphism of two-term complexes, given
by its two components. -/
def lineCongr (d : K₁ →ₗ[R] K₀) (d' : L₁ →ₗ[R] L₀) (e₁ : K₁ ≃ₗ[R] L₁) (e₀ : K₀ ≃ₗ[R] L₀) :
    TwoTermComplex.determinantLine d ≃ₗ[R] TwoTermComplex.determinantLine d' :=
  LinearEquiv.arrowCongr (ProjectiveDeterminant.mapEquiv e₁) (ProjectiveDeterminant.mapEquiv e₀)

/-- An isomorphism of rank-zero two-term complexes carries the canonical element of the
determinant line to the canonical element. -/
theorem lineCongr_delta (d : K₁ →ₗ[R] K₀) (d' : L₁ →ₗ[R] L₀) (e₁ : K₁ ≃ₗ[R] L₁)
    (e₀ : K₀ ≃ₗ[R] L₀) (h : d' ∘ₗ e₁.toLinearMap = e₀.toLinearMap ∘ₗ d)
    (hd : TwoTermComplex.IsRankZero d) (hd' : TwoTermComplex.IsRankZero d') :
    lineCongr d d' e₁ e₀ (TwoTermComplex.delta d hd) = TwoTermComplex.delta d' hd' := by
  have hd'' : d' = e₀.toLinearMap ∘ₗ d ∘ₗ e₁.symm.toLinearMap := by
    rw [← LinearMap.comp_assoc, ← h, LinearMap.comp_assoc]
    simp
  apply LinearMap.ext
  intro x
  simp only [lineCongr, LinearEquiv.arrowCongr_apply, TwoTermComplex.delta]
  have h1 := ProjectiveDeterminant.map_comp
    (fun p => (ProjectiveDeterminant.rankAtStalk_congr e₁ p).symm) hd e₁.symm.toLinearMap d
  have h2 := ProjectiveDeterminant.map_comp
    (fun p => ((ProjectiveDeterminant.rankAtStalk_congr e₁ p).symm).trans (hd p))
    (fun p => ProjectiveDeterminant.rankAtStalk_congr e₀ p) (d ∘ₗ e₁.symm.toLinearMap)
    e₀.toLinearMap
  have hx : (ProjectiveDeterminant.mapEquiv e₁).symm x =
      ProjectiveDeterminant.map (fun p => (ProjectiveDeterminant.rankAtStalk_congr e₁ p).symm)
        e₁.symm.toLinearMap x := by
    apply (ProjectiveDeterminant.mapEquiv e₁).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    show x.1 = ExteriorAlgebra.map e₁.toLinearMap
      (ExteriorAlgebra.map e₁.symm.toLinearMap x.1)
    rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
    simp
  rw [hx]
  show _ = ProjectiveDeterminant.map hd' d' x
  subst hd''
  have h2x := LinearMap.congr_fun h2 x
  have h1x := LinearMap.congr_fun h1 x
  simp only [LinearMap.comp_apply] at h2x h1x
  rw [← h1x]
  show ProjectiveDeterminant.mapEquiv e₀ _ = _
  rw [← LinearMap.comp_assoc] at h2x
  exact h2x.symm

omit [Module.Finite R L₁] [Module.Projective R L₁] [Module.Finite R L₀] [Module.Projective R L₀]
  in
/-- The determinant equivalence of a composite of linear equivalences. -/
theorem _root_.ProjectiveDeterminant.mapEquiv_trans {M N P : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P] (e : M ≃ₗ[R] N) (f : N ≃ₗ[R] P) :
    ProjectiveDeterminant.mapEquiv (e.trans f) =
      (ProjectiveDeterminant.mapEquiv e).trans (ProjectiveDeterminant.mapEquiv f) := by
  ext x
  show ExteriorAlgebra.map (e.trans f).toLinearMap x.1 =
    ExteriorAlgebra.map f.toLinearMap (ExteriorAlgebra.map e.toLinearMap x.1)
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
  rfl

/-- The determinant equivalence of the identity. -/
theorem _root_.ProjectiveDeterminant.mapEquiv_refl {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    ProjectiveDeterminant.mapEquiv (LinearEquiv.refl R M) = LinearEquiv.refl R _ := by
  ext x
  show ExteriorAlgebra.map LinearMap.id x.1 = x.1
  simp

/-- `lineCongr` is compatible with composition. -/
theorem lineCongr_trans {M₁ M₀ : Type*} [AddCommGroup M₁] [Module R M₁] [Module.Finite R M₁]
    [Module.Projective R M₁] [AddCommGroup M₀] [Module R M₀] [Module.Finite R M₀]
    [Module.Projective R M₀] (d : K₁ →ₗ[R] K₀) (d' : L₁ →ₗ[R] L₀) (d'' : M₁ →ₗ[R] M₀)
    (e₁ : K₁ ≃ₗ[R] L₁) (e₀ : K₀ ≃ₗ[R] L₀) (f₁ : L₁ ≃ₗ[R] M₁) (f₀ : L₀ ≃ₗ[R] M₀) :
    (lineCongr d d' e₁ e₀).trans (lineCongr d' d'' f₁ f₀) =
      lineCongr d d'' (e₁.trans f₁) (e₀.trans f₀) := by
  ext φ x
  simp [lineCongr, ProjectiveDeterminant.mapEquiv_trans, LinearEquiv.arrowCongr_apply]

/-- `lineCongr` of the identities is the identity. -/
theorem lineCongr_refl (d : K₁ →ₗ[R] K₀) :
    lineCongr d d (LinearEquiv.refl R K₁) (LinearEquiv.refl R K₀) = LinearEquiv.refl R _ := by
  ext φ x
  simp [lineCongr, ProjectiveDeterminant.mapEquiv_refl, LinearEquiv.arrowCongr_apply]

end LineCongr

section LineBaseChange

variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]

/-- **Base change of linear maps out of a finite projective module**, `S ⊗_R Hom_R(M, N) ≅
Hom_S(S ⊗_R M, S ⊗_R N)`, `s ⊗ φ ↦ s · (φ ⊗ S)`. -/
def homBaseChangeEquiv (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [Module.Finite R M] [Module.Projective R M] :
    S ⊗[R] (M →ₗ[R] N) ≃ₗ[S] (S ⊗[R] M →ₗ[S] S ⊗[R] N) :=
  LinearEquiv.ofBijective ((LinearMap.baseChangeHom R S M N).liftBaseChange S) (by
    have h : ⇑((LinearMap.baseChangeHom R S M N).liftBaseChange S) =
        ⇑(LinearMap.liftBaseChangeEquiv S) ∘ ⇑(lTensorHomEquivHomLTensor R M S N) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
        simp only [map_add, Function.comp_apply] at hx hy ⊢
        rw [hx, hy]
      | tmul s φ =>
        apply TensorProduct.AlgebraTensorModule.ext
        intro t m
        simp [lTensorHomEquivHomLTensor_apply, TensorProduct.lTensorHomToHomLTensor_apply,
          TensorProduct.smul_tmul', mul_comm]
    rw [h]
    exact (LinearMap.liftBaseChangeEquiv S).bijective.comp
      (lTensorHomEquivHomLTensor R M S N).bijective)

/-- `homBaseChangeEquiv` sends `s ⊗ φ` to `s · (φ ⊗ S)`. -/
theorem homBaseChangeEquiv_tmul (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [Module.Finite R M] [Module.Projective R M] (s : S) (φ : M →ₗ[R] N) :
    homBaseChangeEquiv S M N (s ⊗ₜ φ) = s • φ.baseChange S := by
  simp [homBaseChangeEquiv]

variable {K₁ K₀ : Type u}
variable [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
variable [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]

/-- **Base change of the determinant line**, `S ⊗_R det(K) ≅ det(K ⊗_R S)` for a two-term
complex `K` of finite projective modules. -/
def lineBaseChange (d : K₁ →ₗ[R] K₀) :
    S ⊗[R] TwoTermComplex.determinantLine d ≃ₗ[S]
      TwoTermComplex.determinantLine (d.baseChange S) :=
  haveI := ProjectiveDeterminant.invertible (R := R) (M := K₁)
  (homBaseChangeEquiv S _ _).trans
    (LinearEquiv.arrowCongr ProjectiveDeterminant.baseChangeEquiv
      ProjectiveDeterminant.baseChangeEquiv)

/-- `lineBaseChange` sends `s ⊗ φ` to `s` times the base change of `φ`, conjugated by the
base-change isomorphisms of the determinant lines of `K₁` and `K₀`. -/
theorem lineBaseChange_tmul (d : K₁ →ₗ[R] K₀) (s : S) (φ : TwoTermComplex.determinantLine d) :
    lineBaseChange S d (s ⊗ₜ φ) =
      s • ((ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S) (M := K₀)).toLinearMap ∘ₗ
        φ.baseChange S ∘ₗ
          (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S)
            (M := K₁)).symm.toLinearMap) := by
  have := ProjectiveDeterminant.invertible (R := R) (M := K₁)
  ext x
  simp [lineBaseChange, homBaseChangeEquiv_tmul, LinearEquiv.arrowCongr_apply]

/-- Base change of the determinant line carries the canonical element to the canonical
element. -/
theorem lineBaseChange_delta (d : K₁ →ₗ[R] K₀) (hd : TwoTermComplex.IsRankZero d)
    (hd' : TwoTermComplex.IsRankZero (d.baseChange S)) :
    lineBaseChange S d (1 ⊗ₜ TwoTermComplex.delta d hd) =
      TwoTermComplex.delta (d.baseChange S) hd' := by
  rw [lineBaseChange_tmul, one_smul]
  show _ = ProjectiveDeterminant.map hd' (d.baseChange S)
  rw [TwoTermComplex.delta, ← LinearMap.comp_assoc,
    ProjectiveDeterminant.baseChangeEquiv_comp_baseChange_map S (fun p => hd p) (fun p => hd' p) d,
    LinearMap.comp_assoc]
  ext x
  simp

end LineBaseChange

section HomBaseChange

variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
variable {K₁ K₀ L₁ L₀ : Type*} [AddCommGroup K₁] [Module R K₁] [AddCommGroup K₀] [Module R K₀]
  [AddCommGroup L₁] [Module R L₁] [AddCommGroup L₀] [Module R L₀]

/-- The base change of a morphism of two-term complexes. -/
abbrev Hom.baseChange {d : K₁ →ₗ[R] K₀} {d' : L₁ →ₗ[R] L₀} (a : Hom d d') :
    Hom (d.baseChange S) (d'.baseChange S) where
  neg := a.neg.baseChange S
  zero := a.zero.baseChange S
  comm := by rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, a.comm]

end HomBaseChange

section LineBaseChangeTrans

variable {R : Type u} [CommRing R]
variable {K₁ K₀ : Type u}
variable [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
variable [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]

/-- `lineBaseChange S d (1 ⊗ φ)` sends the image of `s ⊗ z` in `det(S ⊗_R K₁)` to the image of
`s ⊗ φ z` in `det(S ⊗_R K₀)`. -/
theorem lineBaseChange_one_tmul_apply (S : Type u) [CommRing S] [Algebra R S]
    (d : K₁ →ₗ[R] K₀) (φ : determinantLine d) (s : S)
    (z : ProjectiveDeterminant.module (R := R) (M := K₁)) :
    lineBaseChange S d (1 ⊗ₜ φ) (ProjectiveDeterminant.baseChangeEquiv (s ⊗ₜ z)) =
      ProjectiveDeterminant.baseChangeEquiv (s ⊗ₜ φ z) := by
  rw [lineBaseChange_tmul, one_smul]
  simp

variable (A : Type u) [CommRing A] [Algebra R A]
  (C : Type u) [CommRing C] [Algebra R C] [Algebra A C] [IsScalarTower R A C]

/-- **Transitivity of the base change of determinant lines.** Base changing along `R → A` and
then along `A → C` is base changing along `R → C`, up to the cancellation isomorphisms
`C ⊗_A (A ⊗_R K) ≅ C ⊗_R K`. -/
theorem lineBaseChange_trans (d : K₁ →ₗ[R] K₀) (φ : determinantLine d) :
    lineCongr ((d.baseChange A).baseChange C) (d.baseChange C)
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R A C C K₁)
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R A C C K₀)
        (lineBaseChange C (d.baseChange A) (1 ⊗ₜ lineBaseChange A d (1 ⊗ₜ φ))) =
      lineBaseChange C d (1 ⊗ₜ φ) := by
  apply LinearMap.ext
  intro y
  obtain ⟨w, rfl⟩ :=
    (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := C) (M := K₁)).surjective y
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' => rw [map_add, map_add, map_add, hw, hw']
  | tmul c z =>
    rw [TensorProduct.tmul_eq_smul_one_tmul c z, map_smul, map_smul, map_smul,
      lineBaseChange_one_tmul_apply]
    congr 1
    rw [← ProjectiveDeterminant.baseChangeEquiv_trans A C z]
    simp only [lineCongr, LinearEquiv.arrowCongr_apply, LinearEquiv.symm_apply_apply]
    rw [lineBaseChange_one_tmul_apply, lineBaseChange_one_tmul_apply,
      ProjectiveDeterminant.baseChangeEquiv_trans A C]

end LineBaseChangeTrans

end TwoTermComplex

end
