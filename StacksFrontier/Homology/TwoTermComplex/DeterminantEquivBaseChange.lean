module

public import StacksFrontier.Homology.TwoTermComplex.LineBaseChange

/-!
# Base change of the determinant equivalence of a surjective quasi-isomorphism

Let `R → S` be a ring map and `a : K → L` a degreewise-surjective quasi-isomorphism of two-term
complexes of finite projective `R`-modules. The canonical equivalence of determinant lines
`det(K) ≅ det(L)` attached to `a` commutes with base change to `S`.

## Main definitions

* `TwoTermComplex.kerBaseChangeEquiv`: for a surjection `f : M → N` onto a projective module,
  `S ⊗_R ker f ≅ ker (S ⊗_R f)`.

## Main results

* `TwoTermComplex.kernelDeterminantEquiv_baseChange`: the determinant of the short exact
  sequence `0 → ker f → M → N → 0` commutes with base change.
* `TwoTermComplex.lineBaseChange_determinantEquivOfSurjectiveQuasiIso`: the main statement.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace TwoTermComplex

variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]

section KerBaseChange

variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Module.Projective R N]

theorem injective_baseChange_subtype_ker (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Function.Injective ((LinearMap.ker f).subtype.baseChange S) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  let p : M →ₗ[R] LinearMap.ker f :=
    LinearMap.codRestrict (LinearMap.ker f) (LinearMap.id - s.comp f) fun x => by
      rw [LinearMap.mem_ker]
      simpa only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub,
        sub_eq_zero] using (LinearMap.congr_fun hs (f x)).symm
  have hp : p.comp (LinearMap.ker f).subtype = LinearMap.id := by
    ext x
    simp [p, LinearMap.mem_ker.mp x.2]
  have hp' : (p.baseChange S).comp ((LinearMap.ker f).subtype.baseChange S) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hp, LinearMap.baseChange_id]
  exact Function.LeftInverse.injective (g := p.baseChange S) fun x ↦
    LinearMap.congr_fun hp' x

omit [Module.Projective R N] in
theorem range_baseChange_subtype_ker (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    LinearMap.range ((LinearMap.ker f).subtype.baseChange S) =
      LinearMap.ker (f.baseChange S) := by
  ext x
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  exact (lTensor_exact S f.exact_subtype_ker_map hf x).symm

/-- For a surjection `f : M → N` onto a projective module, the kernel commutes with base
change. -/
def kerBaseChangeEquiv (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    S ⊗[R] LinearMap.ker f ≃ₗ[S] LinearMap.ker (f.baseChange S) :=
  (LinearEquiv.ofInjective _ (injective_baseChange_subtype_ker S f hf)).trans
    (LinearEquiv.ofEq _ _ (range_baseChange_subtype_ker S f hf))

theorem coe_kerBaseChangeEquiv (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (z : S ⊗[R] LinearMap.ker f) :
    (kerBaseChangeEquiv S f hf z : S ⊗[R] M) = (LinearMap.ker f).subtype.baseChange S z :=
  rfl

theorem subtype_comp_kerBaseChangeEquiv (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    (LinearMap.ker (f.baseChange S)).subtype.comp (kerBaseChangeEquiv S f hf).toLinearMap =
      (LinearMap.ker f).subtype.baseChange S :=
  rfl

end KerBaseChange

section KernelDeterminant

variable {R' : Type u} [CommRing R']
variable {M N : Type u} [AddCommGroup M] [Module R' M] [Module.Finite R' M] [Module.Projective R' M]
  [AddCommGroup N] [Module R' N] [Module.Finite R' N] [Module.Projective R' N]

omit [Module.Finite R' N] in
/-- The determinant of `0 → ker f → M → N → 0`, read in the exterior algebra of `M`: the wedge of
the image of `x` with any lift of `y`. -/
theorem coe_kernelDeterminantEquiv [Module.Finite R' N] (f : M →ₗ[R'] N)
    (hf : Function.Surjective f)
    [Module.Finite R' (LinearMap.ker f)] [Module.Projective R' (LinearMap.ker f)]
    (x : ProjectiveDeterminant.module (R := R') (M := LinearMap.ker f))
    (y : ProjectiveDeterminant.module (R := R') (M := N)) (z : ExteriorAlgebra R' M)
    (hz : ExteriorAlgebra.map f z = (y : ExteriorAlgebra R' N)) :
    (kernelDeterminantEquiv f hf (x ⊗ₜ[R'] y) : ExteriorAlgebra R' M) =
      ExteriorAlgebra.map (LinearMap.ker f).subtype (x : ExteriorAlgebra R' (LinearMap.ker f)) *
        z :=
  (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
      (LinearMap.ker f).subtype f (LinearMap.ker f).injective_subtype
        f.exact_subtype_ker_map hf).property
    (determinantAnnihilatorEquiv x) (determinantAnnihilatorEquiv y) z hz

end KernelDeterminant

section BaseChangeExterior

variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The base change of exterior algebras is natural, read on pure tensors `1 ⊗ z`. -/
theorem map_baseChange_exteriorAlgebraBaseChange_symm (f : M →ₗ[R] N) (z : ExteriorAlgebra R M) :
    ExteriorAlgebra.map (f.baseChange S)
        ((ProjectiveDeterminant.exteriorAlgebraBaseChange R S M).symm (1 ⊗ₜ[R] z)) =
      (ProjectiveDeterminant.exteriorAlgebraBaseChange R S N).symm
        (1 ⊗ₜ[R] ExteriorAlgebra.map f z) := by
  apply (ProjectiveDeterminant.exteriorAlgebraBaseChange R S N).injective
  rw [AlgEquiv.apply_symm_apply]
  have := congrArg (fun φ ↦ φ ((ProjectiveDeterminant.exteriorAlgebraBaseChange R S M).symm
    (1 ⊗ₜ[R] z))) (ProjectiveDeterminant.exteriorAlgebraBaseChange_comp_map S f)
  simp only [AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq] at this
  exact this

end BaseChangeExterior

section KernelDeterminantBaseChange

variable {M N : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
  [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]

/-- **The determinant of a short exact sequence commutes with base change.** -/
theorem kernelDeterminantEquiv_baseChange (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (hfS : Function.Surjective (f.baseChange S))
    [Module.Finite R (LinearMap.ker f)] [Module.Projective R (LinearMap.ker f)]
    [Module.Finite S (LinearMap.ker (f.baseChange S))]
    [Module.Projective S (LinearMap.ker (f.baseChange S))]
    (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker f))
    (y : ProjectiveDeterminant.module (R := R) (M := N)) :
    kernelDeterminantEquiv (f.baseChange S) hfS
        (ProjectiveDeterminant.mapEquiv (kerBaseChangeEquiv S f hf)
            (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S) (1 ⊗ₜ[R] x)) ⊗ₜ[S]
          ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S) (1 ⊗ₜ[R] y)) =
      ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S)
        (1 ⊗ₜ[R] kernelDeterminantEquiv f hf (x ⊗ₜ[R] y)) := by
  obtain ⟨z, hz⟩ := (ExteriorAlgebra.map_surjective_iff.mpr hf) (y : ExteriorAlgebra R N)
  apply Subtype.ext
  rw [coe_kernelDeterminantEquiv (f.baseChange S) hfS _ _
      ((ProjectiveDeterminant.exteriorAlgebraBaseChange R S M).symm (1 ⊗ₜ[R] z)) (by
        rw [map_baseChange_exteriorAlgebraBaseChange_symm, hz]
        rfl),
    ProjectiveDeterminant.coe_baseChangeEquiv_tmul,
    coe_kernelDeterminantEquiv f hf x y z hz]
  change ExteriorAlgebra.map (LinearMap.ker (f.baseChange S)).subtype
      (ExteriorAlgebra.map (kerBaseChangeEquiv S f hf).toLinearMap
        ((ProjectiveDeterminant.exteriorAlgebraBaseChange R S (LinearMap.ker f)).symm
          (1 ⊗ₜ[R] (x : ExteriorAlgebra R (LinearMap.ker f))))) * _ = _
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, subtype_comp_kerBaseChangeEquiv,
    map_baseChange_exteriorAlgebraBaseChange_symm, ← map_mul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end KernelDeterminantBaseChange

section KernelComplex

variable {K₁ K₀ L₁ L₀ : Type u}
variable [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
variable [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]
variable [AddCommGroup L₁] [Module R L₁] [Module.Finite R L₁] [Module.Projective R L₁]
variable [AddCommGroup L₀] [Module R L₀] [Module.Finite R L₀] [Module.Projective R L₀]
variable {d : K₁ →ₗ[R] K₀} {d' : L₁ →ₗ[R] L₀}

omit [Module.Finite R K₁] [Module.Projective R K₁] [Module.Finite R K₀] [Module.Projective R K₀]
  [Module.Finite R L₁] [Module.Finite R L₀] in
/-- The kernel complex of the base change of a degreewise-surjective morphism is the base change
of its kernel complex. -/
theorem kernelDifferential_baseChange_comp (a : Hom d d') (ha : a.IsDegreewiseSurjective) :
    (a.baseChange S).kernelDifferential.comp (kerBaseChangeEquiv S a.neg ha.1).toLinearMap =
      (kerBaseChangeEquiv S a.zero ha.2).toLinearMap.comp (a.kernelDifferential.baseChange S) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s x
  apply Subtype.ext
  change (d.baseChange S) ((LinearMap.ker a.neg).subtype.baseChange S (s ⊗ₜ x)) =
    (LinearMap.ker a.zero).subtype.baseChange S (s ⊗ₜ a.kernelDifferential x)
  simp only [LinearMap.baseChange_tmul]
  rfl

omit [Module.Finite R K₁] [Module.Projective R K₁] [Module.Finite R K₀] [Module.Projective R K₀]
  [Module.Finite R L₁] [Module.Finite R L₀] in
/-- The canonical element of the kernel complex commutes with base change. -/
theorem delta_kernelDifferential_baseChange (a : Hom d d') (ha : a.IsDegreewiseSurjective)
    [Module.Finite R (LinearMap.ker a.neg)] [Module.Projective R (LinearMap.ker a.neg)]
    [Module.Finite R (LinearMap.ker a.zero)] [Module.Projective R (LinearMap.ker a.zero)]
    [Module.Finite S (LinearMap.ker (a.baseChange S).neg)]
    [Module.Projective S (LinearMap.ker (a.baseChange S).neg)]
    [Module.Finite S (LinearMap.ker (a.baseChange S).zero)]
    [Module.Projective S (LinearMap.ker (a.baseChange S).zero)]
    (h : IsRankZero a.kernelDifferential) (hS : IsRankZero (a.baseChange S).kernelDifferential)
    (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg)) :
    letI : Module.Finite S (LinearMap.ker (a.neg.baseChange S)) :=
      ‹Module.Finite S (LinearMap.ker (a.baseChange S).neg)›
    letI : Module.Projective S (LinearMap.ker (a.neg.baseChange S)) :=
      ‹Module.Projective S (LinearMap.ker (a.baseChange S).neg)›
    letI : Module.Finite S (LinearMap.ker (a.zero.baseChange S)) :=
      ‹Module.Finite S (LinearMap.ker (a.baseChange S).zero)›
    letI : Module.Projective S (LinearMap.ker (a.zero.baseChange S)) :=
      ‹Module.Projective S (LinearMap.ker (a.baseChange S).zero)›
    delta (a.baseChange S).kernelDifferential hS
        (ProjectiveDeterminant.mapEquiv (kerBaseChangeEquiv S a.neg ha.1)
          (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S) (1 ⊗ₜ[R] x))) =
      ProjectiveDeterminant.mapEquiv (kerBaseChangeEquiv S a.zero ha.2)
        (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S)
          (1 ⊗ₜ[R] delta a.kernelDifferential h x)) := by
  apply Subtype.ext
  change ExteriorAlgebra.map (a.baseChange S).kernelDifferential
      (ExteriorAlgebra.map (kerBaseChangeEquiv S a.neg ha.1).toLinearMap
        ((ProjectiveDeterminant.exteriorAlgebraBaseChange R S (LinearMap.ker a.neg)).symm
          (1 ⊗ₜ[R] (x : ExteriorAlgebra R (LinearMap.ker a.neg))))) =
    ExteriorAlgebra.map (kerBaseChangeEquiv S a.zero ha.2).toLinearMap
      ((ProjectiveDeterminant.exteriorAlgebraBaseChange R S (LinearMap.ker a.zero)).symm
        (1 ⊗ₜ[R] ExteriorAlgebra.map a.kernelDifferential
          (x : ExteriorAlgebra R (LinearMap.ker a.neg))))
  have key : ∀ w, ExteriorAlgebra.map (a.baseChange S).kernelDifferential
      (ExteriorAlgebra.map (kerBaseChangeEquiv S a.neg ha.1).toLinearMap w) =
      ExteriorAlgebra.map (kerBaseChangeEquiv S a.zero ha.2).toLinearMap
        (ExteriorAlgebra.map (a.kernelDifferential.baseChange S) w) := fun w ↦ by
    have h1 := congrArg (fun φ ↦ φ w) (ExteriorAlgebra.map_comp_map
      (kerBaseChangeEquiv S a.neg ha.1).toLinearMap (a.baseChange S).kernelDifferential)
    have h2 := congrArg (fun φ ↦ φ w) (ExteriorAlgebra.map_comp_map
      (a.kernelDifferential.baseChange S) (kerBaseChangeEquiv S a.zero ha.2).toLinearMap)
    simp only [AlgHom.comp_apply] at h1 h2
    exact h1.trans ((congrArg (fun F ↦ ExteriorAlgebra.map F w)
      (kernelDifferential_baseChange_comp S a ha)).trans h2.symm)
  rw [key, map_baseChange_exteriorAlgebraBaseChange_symm]

/-- `S ⊗_R ker(a₋₁) ≅ ker((S ⊗_R a)₋₁)` for a degreewise-surjective morphism `a`. -/
def kerNegBaseChange (a : Hom d d') (ha : a.IsDegreewiseSurjective) :
    S ⊗[R] LinearMap.ker a.neg ≃ₗ[S] LinearMap.ker (a.baseChange S).neg :=
  kerBaseChangeEquiv S a.neg ha.1

/-- `S ⊗_R ker(a₀) ≅ ker((S ⊗_R a)₀)` for a degreewise-surjective morphism `a`. -/
def kerZeroBaseChange (a : Hom d d') (ha : a.IsDegreewiseSurjective) :
    S ⊗[R] LinearMap.ker a.zero ≃ₗ[S] LinearMap.ker (a.baseChange S).zero :=
  kerBaseChangeEquiv S a.zero ha.2

section Hom

variable (a : Hom d d') (ha : a.IsDegreewiseSurjective)
  (ha' : (a.baseChange S).IsDegreewiseSurjective)
  [Module.Finite R (LinearMap.ker a.neg)] [Module.Projective R (LinearMap.ker a.neg)]
  [Module.Finite R (LinearMap.ker a.zero)] [Module.Projective R (LinearMap.ker a.zero)]
  [Module.Finite S (LinearMap.ker (a.baseChange S).neg)]
  [Module.Projective S (LinearMap.ker (a.baseChange S).neg)]
  [Module.Finite S (LinearMap.ker (a.baseChange S).zero)]
  [Module.Projective S (LinearMap.ker (a.baseChange S).zero)]

omit [Module.Finite R K₀] [Module.Projective R K₀] [Module.Finite R L₀] [Module.Projective R L₀]
  [Module.Finite R (LinearMap.ker a.zero)] [Module.Projective R (LinearMap.ker a.zero)]
  [Module.Finite S (LinearMap.ker (a.baseChange S).zero)]
  [Module.Projective S (LinearMap.ker (a.baseChange S).zero)] in
theorem kernelDeterminantEquiv_neg_baseChange
    (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))
    (y : ProjectiveDeterminant.module (R := R) (M := L₁)) :
    kernelDeterminantEquiv (a.baseChange S).neg ha'.1
        (ProjectiveDeterminant.mapEquiv (kerNegBaseChange S a ha)
            (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S) (1 ⊗ₜ[R] x)) ⊗ₜ[S]
          ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S) (1 ⊗ₜ[R] y)) =
      ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S)
        (1 ⊗ₜ[R] kernelDeterminantEquiv a.neg ha.1 (x ⊗ₜ[R] y)) := by
  let : Module.Finite S (LinearMap.ker (a.neg.baseChange S)) :=
    ‹Module.Finite S (LinearMap.ker (a.baseChange S).neg)›
  let : Module.Projective S (LinearMap.ker (a.neg.baseChange S)) :=
    ‹Module.Projective S (LinearMap.ker (a.baseChange S).neg)›
  exact kernelDeterminantEquiv_baseChange S a.neg ha.1 ha'.1 x y

omit [Module.Finite R K₁] [Module.Projective R K₁] [Module.Finite R L₁] [Module.Projective R L₁]
  [Module.Finite R (LinearMap.ker a.neg)] [Module.Projective R (LinearMap.ker a.neg)]
  [Module.Finite S (LinearMap.ker (a.baseChange S).neg)]
  [Module.Projective S (LinearMap.ker (a.baseChange S).neg)] in
theorem kernelDeterminantEquiv_zero_baseChange
    (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.zero))
    (y : ProjectiveDeterminant.module (R := R) (M := L₀)) :
    kernelDeterminantEquiv (a.baseChange S).zero ha'.2
        (ProjectiveDeterminant.mapEquiv (kerZeroBaseChange S a ha)
            (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S) (1 ⊗ₜ[R] x)) ⊗ₜ[S]
          ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S) (1 ⊗ₜ[R] y)) =
      ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S)
        (1 ⊗ₜ[R] kernelDeterminantEquiv a.zero ha.2 (x ⊗ₜ[R] y)) := by
  let : Module.Finite S (LinearMap.ker (a.zero.baseChange S)) :=
    ‹Module.Finite S (LinearMap.ker (a.baseChange S).zero)›
  let : Module.Projective S (LinearMap.ker (a.zero.baseChange S)) :=
    ‹Module.Projective S (LinearMap.ker (a.baseChange S).zero)›
  exact kernelDeterminantEquiv_baseChange S a.zero ha.2 ha'.2 x y

omit [Module.Finite R K₁] [Module.Projective R K₁] [Module.Finite R K₀] [Module.Projective R K₀]
  [Module.Finite R L₁] [Module.Finite R L₀] in
theorem delta_kernelDifferential_baseChange'
    (h : IsRankZero a.kernelDifferential) (hS : IsRankZero (a.baseChange S).kernelDifferential)
    (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg)) :
    delta (a.baseChange S).kernelDifferential hS
        (ProjectiveDeterminant.mapEquiv (kerNegBaseChange S a ha)
          (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S) (1 ⊗ₜ[R] x))) =
      ProjectiveDeterminant.mapEquiv (kerZeroBaseChange S a ha)
        (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S)
          (1 ⊗ₜ[R] delta a.kernelDifferential h x)) :=
  delta_kernelDifferential_baseChange S a ha h hS x

end Hom

end KernelComplex

section Main

variable {K₁ K₀ L₁ L₀ : Type u}
variable [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
variable [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]
variable [AddCommGroup L₁] [Module R L₁] [Module.Finite R L₁] [Module.Projective R L₁]
variable [AddCommGroup L₀] [Module R L₀] [Module.Finite R L₀] [Module.Projective R L₀]

omit [Module.Finite R K₁] [Module.Projective R K₁] [Module.Finite R K₀] [Module.Projective R K₀]
  [Module.Finite R L₁] [Module.Projective R L₁] [Module.Finite R L₀] [Module.Projective R L₀] in
/-- The base change of a degreewise-surjective morphism is degreewise surjective. -/
theorem Hom.isDegreewiseSurjective_baseChange {d : K₁ →ₗ[R] K₀} {d' : L₁ →ₗ[R] L₀}
    (a : Hom d d') (ha : a.IsDegreewiseSurjective) :
    (a.baseChange S).IsDegreewiseSurjective := by
  refine ⟨?_, ?_⟩
  · change Function.Surjective (a.neg.baseChange S)
    rw [LinearMap.baseChange_eq_lTensor]
    exact LinearMap.lTensor_surjective S ha.1
  · change Function.Surjective (a.zero.baseChange S)
    rw [LinearMap.baseChange_eq_lTensor]
    exact LinearMap.lTensor_surjective S ha.2

variable {d : K₁ →ₗ[R] K₀} {d' : L₁ →ₗ[R] L₀}

section Steps

variable (a : Hom d d') (ha : a.IsDegreewiseSurjective) (hqa : a.IsQuasiIso)
  (ha' : (a.baseChange S).IsDegreewiseSurjective)
  [Module.Finite R (LinearMap.ker a.neg)] [Module.Projective R (LinearMap.ker a.neg)]
  [Module.Finite R (LinearMap.ker a.zero)] [Module.Projective R (LinearMap.ker a.zero)]
  [Module.Finite S (LinearMap.ker (a.baseChange S).neg)]
  [Module.Projective S (LinearMap.ker (a.baseChange S).neg)]
  [Module.Finite S (LinearMap.ker (a.baseChange S).zero)]
  [Module.Projective S (LinearMap.ker (a.baseChange S).zero)]
  (hS : IsRankZero (a.baseChange S).kernelDifferential)

/-- The candidate for the base-changed determinant equivalence. -/
def baseChangeDeterminantEquiv :
    determinantLine (d.baseChange S) ≃ₗ[S] determinantLine (d'.baseChange S) :=
  (lineBaseChange S d).symm ≪≫ₗ
    (determinantEquivOfSurjectiveQuasiIso d d' a ha hqa).equiv.baseChange R S _ _ ≪≫ₗ
      lineBaseChange S d'

omit [Module.Finite R (LinearMap.ker a.neg)] [Module.Projective R (LinearMap.ker a.neg)]
  [Module.Finite R (LinearMap.ker a.zero)] [Module.Projective R (LinearMap.ker a.zero)]
  [Module.Finite S (LinearMap.ker (a.baseChange S).neg)]
  [Module.Projective S (LinearMap.ker (a.baseChange S).neg)]
  [Module.Finite S (LinearMap.ker (a.baseChange S).zero)]
  [Module.Projective S (LinearMap.ker (a.baseChange S).zero)] in
theorem baseChangeDeterminantEquiv_one_tmul (φ₀ : determinantLine d) :
    letI : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
    letI : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
    letI : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha.2
    letI : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha.2
    baseChangeDeterminantEquiv S a ha hqa (lineBaseChange S d (1 ⊗ₜ φ₀)) =
      lineBaseChange S d' (1 ⊗ₜ (determinantEquivOfSurjectiveQuasiIso d d' a ha hqa).equiv φ₀) := by
  simp [baseChangeDeterminantEquiv]

theorem one_tmul_smul' {P : Type u} [AddCommGroup P] [Module R P] (c : S) (z : P) :
    (c ⊗ₜ[R] z : S ⊗[R] P) = c • ((1 : S) ⊗ₜ[R] z) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- Two `S`-linear maps out of `S ⊗[R] P` agree if they agree on the pure tensors `1 ⊗ p`. -/
private theorem linearMap_ext_one_tmul {P Q : Type u} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]
    {F G : S ⊗[R] P →ₗ[S] Q} (h : ∀ p, F (1 ⊗ₜ[R] p) = G (1 ⊗ₜ[R] p)) : F = G :=
  TensorProduct.AlgebraTensorModule.ext fun c p ↦ by
    rw [one_tmul_smul' S c p, LinearMap.map_smul, LinearMap.map_smul, h]

omit [Module.Finite R (LinearMap.ker a.neg)] [Module.Projective R (LinearMap.ker a.neg)]
  [Module.Finite R (LinearMap.ker a.zero)] [Module.Projective R (LinearMap.ker a.zero)] in
theorem baseChangeDeterminantEquiv_compat_gen (φ₀ : determinantLine d)
    (x₀ : letI : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
      letI : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
      ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))
    (y₀ : ProjectiveDeterminant.module (R := R) (M := L₁)) :
    letI : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
    letI : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
    letI : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha.2
    letI : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha.2
    kernelDeterminantEquiv (a.baseChange S).zero ha'.2
        (delta (a.baseChange S).kernelDifferential hS
          (ProjectiveDeterminant.mapEquiv (kerNegBaseChange S a ha)
            (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S) (1 ⊗ₜ[R] x₀))) ⊗ₜ[S]
          baseChangeDeterminantEquiv S a ha hqa (lineBaseChange S d (1 ⊗ₜ φ₀))
            (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S) (1 ⊗ₜ[R] y₀))) =
      lineBaseChange S d (1 ⊗ₜ φ₀) (kernelDeterminantEquiv (a.baseChange S).neg ha'.1
        (ProjectiveDeterminant.mapEquiv (kerNegBaseChange S a ha)
            (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S) (1 ⊗ₜ[R] x₀)) ⊗ₜ[S]
          ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S) (1 ⊗ₜ[R] y₀))) := by
  let : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
  let : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
  let : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha.2
  let : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha.2
  set D := determinantEquivOfSurjectiveQuasiIso d d' a ha hqa
  rw [baseChangeDeterminantEquiv_one_tmul, lineBaseChange_one_tmul_apply,
    delta_kernelDifferential_baseChange' S a ha D.kernelRankZero hS x₀]
  have h1 := kernelDeterminantEquiv_zero_baseChange S a ha ha'
    (delta a.kernelDifferential D.kernelRankZero x₀) (D.equiv φ₀ y₀)
  have h2 := kernelDeterminantEquiv_neg_baseChange S a ha ha' x₀ y₀
  refine h1.trans ?_
  refine Eq.trans ?_ (congrArg (lineBaseChange S d (1 ⊗ₜ φ₀)) h2).symm
  rw [lineBaseChange_one_tmul_apply, D.compatibility]

omit [Module.Finite R (LinearMap.ker a.neg)] [Module.Projective R (LinearMap.ker a.neg)]
  [Module.Finite R (LinearMap.ker a.zero)] [Module.Projective R (LinearMap.ker a.zero)] in
theorem baseChangeDeterminantEquiv_compat₀ (φ₀ : determinantLine d)
    (x₀ : letI : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
      letI : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
      ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))
    (y : ProjectiveDeterminant.module (R := S) (M := S ⊗[R] L₁)) :
    letI : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
    letI : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
    letI : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha.2
    letI : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha.2
    kernelDeterminantEquiv (a.baseChange S).zero ha'.2
        (delta (a.baseChange S).kernelDifferential hS
          (ProjectiveDeterminant.mapEquiv (kerNegBaseChange S a ha)
            (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S) (1 ⊗ₜ[R] x₀))) ⊗ₜ[S]
          baseChangeDeterminantEquiv S a ha hqa (lineBaseChange S d (1 ⊗ₜ φ₀)) y) =
      (lineBaseChange S d (1 ⊗ₜ φ₀)) (kernelDeterminantEquiv (a.baseChange S).neg ha'.1
        (ProjectiveDeterminant.mapEquiv (kerNegBaseChange S a ha)
            (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S) (1 ⊗ₜ[R] x₀)) ⊗ₜ[S] y)) := by
  let : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
  let : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
  let : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha.2
  let : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha.2
  let F := (kernelDeterminantEquiv (a.baseChange S).zero ha'.2).toLinearMap ∘ₗ
    TensorProduct.mk S _ _ (delta (a.baseChange S).kernelDifferential hS
      (ProjectiveDeterminant.mapEquiv (kerNegBaseChange S a ha)
        (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S) (1 ⊗ₜ[R] x₀)))) ∘ₗ
    (baseChangeDeterminantEquiv S a ha hqa (lineBaseChange S d (1 ⊗ₜ φ₀))) ∘ₗ
    (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S) (M := L₁)).toLinearMap
  let G := (lineBaseChange S d (1 ⊗ₜ φ₀)) ∘ₗ
    (kernelDeterminantEquiv (a.baseChange S).neg ha'.1).toLinearMap ∘ₗ
    TensorProduct.mk S _ _ (ProjectiveDeterminant.mapEquiv (kerNegBaseChange S a ha)
        (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S) (1 ⊗ₜ[R] x₀))) ∘ₗ
    (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S) (M := L₁)).toLinearMap
  have hFG : F = G := by
    refine linearMap_ext_one_tmul S fun y₀ ↦ ?_
    exact baseChangeDeterminantEquiv_compat_gen S a ha hqa ha' hS φ₀ x₀ y₀
  simpa [F, G] using LinearMap.congr_fun hFG
    ((ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S) (M := L₁)).symm y)

omit [Module.Finite R (LinearMap.ker a.neg)] [Module.Projective R (LinearMap.ker a.neg)]
  [Module.Finite R (LinearMap.ker a.zero)] [Module.Projective R (LinearMap.ker a.zero)] in
theorem baseChangeDeterminantEquiv_compat₁ (φ₀ : determinantLine d)
    (t' : letI : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
      letI : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
      S ⊗[R] ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))
    (y : ProjectiveDeterminant.module (R := S) (M := S ⊗[R] L₁)) :
    letI : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
    letI : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
    letI : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha.2
    letI : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha.2
    kernelDeterminantEquiv (a.baseChange S).zero ha'.2
        (delta (a.baseChange S).kernelDifferential hS
          (ProjectiveDeterminant.mapEquiv (kerNegBaseChange S a ha)
            (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S) t')) ⊗ₜ[S]
          baseChangeDeterminantEquiv S a ha hqa (lineBaseChange S d (1 ⊗ₜ φ₀)) y) =
      (lineBaseChange S d (1 ⊗ₜ φ₀)) (kernelDeterminantEquiv (a.baseChange S).neg ha'.1
        (ProjectiveDeterminant.mapEquiv (kerNegBaseChange S a ha)
            (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S) t') ⊗ₜ[S] y)) := by
  let : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
  let : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
  let : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha.2
  let : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha.2
  let F := (kernelDeterminantEquiv (a.baseChange S).zero ha'.2).toLinearMap ∘ₗ
    (TensorProduct.mk S _ _).flip
      (baseChangeDeterminantEquiv S a ha hqa (lineBaseChange S d (1 ⊗ₜ φ₀)) y) ∘ₗ
    delta (a.baseChange S).kernelDifferential hS ∘ₗ
    (ProjectiveDeterminant.mapEquiv (kerNegBaseChange S a ha)).toLinearMap ∘ₗ
    (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S)
      (M := LinearMap.ker a.neg)).toLinearMap
  let G := (lineBaseChange S d (1 ⊗ₜ φ₀)) ∘ₗ
    (kernelDeterminantEquiv (a.baseChange S).neg ha'.1).toLinearMap ∘ₗ
    (TensorProduct.mk S _ _).flip y ∘ₗ
    (ProjectiveDeterminant.mapEquiv (kerNegBaseChange S a ha)).toLinearMap ∘ₗ
    (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S)
      (M := LinearMap.ker a.neg)).toLinearMap
  have hFG : F = G := by
    refine linearMap_ext_one_tmul S fun x₀ ↦ ?_
    exact baseChangeDeterminantEquiv_compat₀ S a ha hqa ha' hS φ₀ x₀ y
  exact LinearMap.congr_fun hFG t'

omit [Module.Finite R (LinearMap.ker a.neg)] [Module.Projective R (LinearMap.ker a.neg)]
  [Module.Finite R (LinearMap.ker a.zero)] [Module.Projective R (LinearMap.ker a.zero)] in
theorem baseChangeDeterminantEquiv_compat₂ (t : S ⊗[R] determinantLine d)
    (t' : letI : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
      letI : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
      S ⊗[R] ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))
    (y : ProjectiveDeterminant.module (R := S) (M := S ⊗[R] L₁)) :
    letI : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
    letI : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
    letI : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha.2
    letI : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha.2
    kernelDeterminantEquiv (a.baseChange S).zero ha'.2
        (delta (a.baseChange S).kernelDifferential hS
          (ProjectiveDeterminant.mapEquiv (kerNegBaseChange S a ha)
            (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S) t')) ⊗ₜ[S]
          baseChangeDeterminantEquiv S a ha hqa (lineBaseChange S d t) y) =
      (lineBaseChange S d t) (kernelDeterminantEquiv (a.baseChange S).neg ha'.1
        (ProjectiveDeterminant.mapEquiv (kerNegBaseChange S a ha)
            (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S) t') ⊗ₜ[S] y)) := by
  let : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
  let : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
  let : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha.2
  let : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha.2
  let F := (kernelDeterminantEquiv (a.baseChange S).zero ha'.2).toLinearMap ∘ₗ
    TensorProduct.mk S _ _ (delta (a.baseChange S).kernelDifferential hS
      (ProjectiveDeterminant.mapEquiv (kerNegBaseChange S a ha)
        (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S) t'))) ∘ₗ
    LinearMap.applyₗ y ∘ₗ (baseChangeDeterminantEquiv S a ha hqa).toLinearMap ∘ₗ
      (lineBaseChange S d).toLinearMap
  let G := LinearMap.applyₗ (kernelDeterminantEquiv (a.baseChange S).neg ha'.1
        (ProjectiveDeterminant.mapEquiv (kerNegBaseChange S a ha)
            (ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S) t') ⊗ₜ[S] y)) ∘ₗ
    (lineBaseChange S d).toLinearMap
  have hFG : F = G := by
    refine linearMap_ext_one_tmul S fun φ₀ ↦ ?_
    exact baseChangeDeterminantEquiv_compat₁ S a ha hqa ha' hS φ₀ t' y
  exact LinearMap.congr_fun hFG t

end Steps

/-- **The determinant equivalence of a degreewise-surjective quasi-isomorphism commutes with base
change.** -/
theorem lineBaseChange_determinantEquivOfSurjectiveQuasiIso (a : Hom d d')
    (ha : a.IsDegreewiseSurjective) (hqa : a.IsQuasiIso)
    (ha' : (a.baseChange S).IsDegreewiseSurjective) (hqa' : (a.baseChange S).IsQuasiIso)
    (x : S ⊗[R] determinantLine d) :
    letI : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
    letI : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
    letI : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha.2
    letI : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha.2
    letI : Module.Finite S (LinearMap.ker (a.baseChange S).neg) :=
      kernel_finite (a.baseChange S).neg ha'.1
    letI : Module.Projective S (LinearMap.ker (a.baseChange S).neg) :=
      kernel_projective (a.baseChange S).neg ha'.1
    letI : Module.Finite S (LinearMap.ker (a.baseChange S).zero) :=
      kernel_finite (a.baseChange S).zero ha'.2
    letI : Module.Projective S (LinearMap.ker (a.baseChange S).zero) :=
      kernel_projective (a.baseChange S).zero ha'.2
    lineBaseChange S d' (LinearEquiv.baseChange R S _ _
        (determinantEquivOfSurjectiveQuasiIso d d' a ha hqa).equiv x) =
      (determinantEquivOfSurjectiveQuasiIso (d.baseChange S) (d'.baseChange S) (a.baseChange S)
        ha' hqa').equiv (lineBaseChange S d x) := by
  let : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
  let : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
  let : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha.2
  let : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha.2
  let : Module.Finite S (LinearMap.ker (a.baseChange S).neg) :=
    kernel_finite (a.baseChange S).neg ha'.1
  let : Module.Projective S (LinearMap.ker (a.baseChange S).neg) :=
    kernel_projective (a.baseChange S).neg ha'.1
  let : Module.Finite S (LinearMap.ker (a.baseChange S).zero) :=
    kernel_finite (a.baseChange S).zero ha'.2
  let : Module.Projective S (LinearMap.ker (a.baseChange S).zero) :=
    kernel_projective (a.baseChange S).zero ha'.2
  set E := determinantEquivOfSurjectiveQuasiIso (d.baseChange S) (d'.baseChange S)
    (a.baseChange S) ha' hqa'
  have he : baseChangeDeterminantEquiv S a ha hqa = E.equiv := by
    refine E.unique _ fun φ x y ↦ ?_
    obtain ⟨t, rfl⟩ := (lineBaseChange S d).surjective φ
    have h := baseChangeDeterminantEquiv_compat₂ S a ha hqa ha' E.kernelRankZero t
      (((ProjectiveDeterminant.baseChangeEquiv (R := R) (A := S)
        (M := LinearMap.ker a.neg)).trans
          (ProjectiveDeterminant.mapEquiv (kerNegBaseChange S a ha))).symm x) y
    rwa [← LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply] at h
  rw [← he]
  simp [baseChangeDeterminantEquiv]


end Main

end TwoTermComplex
