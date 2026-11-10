module

public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Etale.Basic

/-!
# A quotient of a polynomial ring localized at its Jacobian is étale

Let `P` be a commutative ring and let `g : ρ → P[x_τ]` be finitely many polynomials in finitely
many variables, with an injection `m : ρ → τ` and as many relations as variables. Then the
quotient `P[x_τ]/(g)` localized at the Jacobian determinant `det(∂gⱼ/∂x_{m i})` is an étale
`P`-algebra, with no condition on the coefficients of `g`.

When the polynomials `g` come from the relations of a submersive presentation `P₀` of an
étale algebra `D₀` over a `P`-algebra `C₀`, the base change of that localized quotient to `C₀`
is `D₀` again.  This is the device by which an étale algebra over a ring which is not of finite
type is approximated by an étale algebra over a ring which only knows the coefficients of the
relations (compare the proof of Stacks 07SQ, whose presentation comes from Stacks 00U9).

## Main definitions

* `Algebra.LocalizedQuotient.quot`: the quotient `P[x_τ]/(g)`.
* `Algebra.LocalizedQuotient.jac`: the Jacobian of its naive presentation.
* `Algebra.LocalizedQuotient.ring`: the localization of the quotient at the Jacobian.
* `Algebra.LocalizedQuotient.toAlgHom`: the map of the localized quotient to the algebra a
  submersive presentation with relations `g` presents.

## Main results

* `Algebra.LocalizedQuotient.etale`: the localized quotient is étale.
* `Algebra.LocalizedQuotient.bijective_tensorLift`: its base change to `C₀` is `D₀`.
-/

@[expose] public section

open MvPolynomial TensorProduct

namespace Algebra.LocalizedQuotient

universe u

variable {P : Type u} [CommRing P] {τ ρ : Type} [Finite τ] [Finite ρ]
  (g : ρ → MvPolynomial τ P) (m : ρ → τ) (hm : Function.Injective m)

/-- The quotient `P[x_τ]/(g)`. -/
abbrev quot : Type u := MvPolynomial τ P ⧸ Ideal.span (Set.range g)

/-- The naive presentation of the quotient, with relations `g` and differential read along
`m`. -/
noncomputable abbrev pre : PreSubmersivePresentation P (quot g) τ ρ :=
  PreSubmersivePresentation.naive m hm

/-- The Jacobian of the naive presentation of the quotient. -/
noncomputable abbrev jac : quot g := (pre g m hm).jacobian

/-- The quotient localized at its Jacobian. -/
abbrev ring : Type u := Localization.Away (jac g m hm)

/-- **The localized quotient is étale** as soon as there are as many relations as variables. -/
theorem etale (hcard : Nat.card τ = Nat.card ρ) : Algebra.Etale P (ring g m hm) := by
  have hΔ : IsUnit (algebraMap (quot g) (ring g m hm) (jac g m hm)) :=
    IsLocalization.Away.algebraMap_isUnit _
  let Q : Algebra.SubmersivePresentation P (ring g m hm) _ _ :=
    { toPreSubmersivePresentation :=
        .comp (.localizationAway (ring g m hm) (jac g m hm)) (pre g m hm),
      jacobian_isUnit := by simp [Algebra.smul_def, -isUnit_map_iff, hΔ] }
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 P (ring g m hm) :=
    ⟨_, _, _, inferInstance, Q, by
      simp only [Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension, Q]
      simp [Algebra.Presentation.dimension, hcard]⟩
  infer_instance

section BaseChange

variable {C₀ D₀ : Type u} [CommRing C₀] [CommRing D₀] [Algebra P C₀] [Algebra C₀ D₀]
  [Algebra P D₀] [IsScalarTower P C₀ D₀]
  (P₀ : Algebra.SubmersivePresentation C₀ D₀ τ ρ)
  (hrel : ∀ j, P₀.relation j = (g j).map (algebraMap P C₀)) (hmap : P₀.map = m)

/-- The map of the quotient to `D₀`, sending the variables to the generators of `P₀`. -/
noncomputable def quotToAlgHom : quot g →ₐ[P] D₀ :=
  Ideal.Quotient.liftₐ _ (aeval (R := P) P₀.val) (by
    intro x hx
    refine Submodule.span_induction ?_ (by simp) (fun _ _ _ _ ha hb ↦ by simp [ha, hb])
      (fun a _ _ hb ↦ by simp [hb]) hx
    rintro _ ⟨j, rfl⟩
    rw [← MvPolynomial.aeval_map_algebraMap C₀, ← hrel]
    exact P₀.aeval_val_relation j)

omit [Finite τ] in
/-- `quotToAlgHom` sends the class of a polynomial `x` to `x` evaluated at the generators of
`P₀`. -/
theorem quotToAlgHom_mk (x : MvPolynomial τ P) :
    quotToAlgHom g P₀ hrel (Ideal.Quotient.mk _ x) = aeval P₀.val x := rfl

omit [Finite τ] in
include hmap in
/-- `quotToAlgHom` sends the Jacobian of the quotient to the Jacobian of `P₀`. -/
theorem quotToAlgHom_jac : quotToAlgHom g P₀ hrel (jac g m hm) = P₀.jacobian := by
  classical
  let := Fintype.ofFinite ρ
  rw [jac, PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    P₀.jacobian_eq_jacobiMatrix_det]
  have hmat : P₀.jacobiMatrix =
      (MvPolynomial.map (algebraMap P C₀)).mapMatrix (pre g m hm).jacobiMatrix := by
    ext i j : 1
    simp only [PreSubmersivePresentation.jacobiMatrix_apply, hmap, hrel,
      MvPolynomial.pderiv_map, RingHom.mapMatrix_apply, Matrix.map_apply]
    rfl
  rw [hmat, ← RingHom.map_det, Generators.algebraMap_apply (P := P₀.toGenerators)]
  change quotToAlgHom g P₀ hrel (Ideal.Quotient.mk _ _) = _
  rw [quotToAlgHom_mk, MvPolynomial.aeval_map_algebraMap]

/-- The map of the localized quotient to `D₀`: the Jacobian goes to the Jacobian of `P₀`,
which is a unit. -/
noncomputable def toAlgHom : ring g m hm →ₐ[P] D₀ :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (jac g m hm))
    (f := quotToAlgHom g P₀ hrel) (by
      rintro ⟨_, n, rfl⟩
      simpa [quotToAlgHom_jac g m hm P₀ hrel hmap] using P₀.jacobian_isUnit.pow n)

omit [Finite τ] in
/-- `toAlgHom` restricts to `quotToAlgHom` on the quotient. -/
theorem toAlgHom_algebraMap (x : quot g) :
    toAlgHom g m hm P₀ hrel hmap (algebraMap _ _ x) = quotToAlgHom g P₀ hrel x :=
  IsLocalization.lift_eq _ _

/-- The base change of the localized quotient to `C₀`, mapped to `D₀`. -/
noncomputable def tensorLift : C₀ ⊗[P] ring g m hm →ₐ[C₀] D₀ :=
  Algebra.TensorProduct.lift (Algebra.ofId C₀ D₀) (toAlgHom g m hm P₀ hrel hmap)
    (fun _ _ ↦ Commute.all _ _)

/-- The inverse map, out of the presentation `P₀`. -/
noncomputable def tensorInv : D₀ →ₐ[C₀] C₀ ⊗[P] ring g m hm :=
  (Ideal.Quotient.liftₐ P₀.ker
      (aeval (R := C₀) fun i ↦ (1 : C₀) ⊗ₜ[P]
        algebraMap (quot g) (ring g m hm) (Ideal.Quotient.mk _ (X i))) (by
      intro x hx
      rw [← P₀.span_range_relation_eq_ker] at hx
      refine Submodule.span_induction ?_ (by simp) (fun _ _ _ _ ha hb ↦ by simp [ha, hb])
        (fun a _ _ hb ↦ by simp [hb]) hx
      rintro _ ⟨j, rfl⟩
      rw [hrel, MvPolynomial.aeval_map_algebraMap]
      have : (aeval (R := P) fun i ↦ (1 : C₀) ⊗ₜ[P]
          algebraMap (quot g) (ring g m hm) (Ideal.Quotient.mk _ (X i))) =
          ((Algebra.TensorProduct.includeRight (R := P) (A := C₀)).comp
            ((IsScalarTower.toAlgHom P (quot g) (ring g m hm)).comp
              (Ideal.Quotient.mkₐ P _))) := by
        ext i; simp
      rw [this]
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
      rw [show (Ideal.Quotient.mk (Ideal.span (Set.range g)) (g j) : quot g) = 0 from
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)]
      simp)).comp
    ((P₀.quotientEquiv.symm.toAlgHom).restrictScalars C₀)

omit [Finite τ] [Algebra P D₀] [IsScalarTower P C₀ D₀] in
/-- `tensorInv` sends a polynomial `p` evaluated at the generators of `P₀` to `p` evaluated at
the elements `1 ⊗ xᵢ` of the base change. -/
theorem tensorInv_aeval (p : MvPolynomial τ C₀) :
    tensorInv g m hm P₀ hrel (aeval P₀.val p) = aeval (R := C₀) (fun i ↦ (1 : C₀) ⊗ₜ[P]
        algebraMap (quot g) (ring g m hm) (Ideal.Quotient.mk _ (X i))) p := by
  rw [← Generators.algebraMap_apply (P := P₀.toGenerators), ← P₀.quotientEquiv_mk]
  have h : ((P₀.quotientEquiv.symm.toAlgHom).restrictScalars C₀)
      (P₀.quotientEquiv (Ideal.Quotient.mk _ p)) = Ideal.Quotient.mk _ p :=
    P₀.quotientEquiv.symm_apply_apply _
  simp only [tensorInv, AlgHom.comp_apply, h]
  rfl

omit [Finite τ] in
/-- `tensorLift` sends a polynomial `p` evaluated at the elements `1 ⊗ xᵢ` of the base change to
`p` evaluated at the generators of `P₀`. -/
theorem tensorLift_aeval (p : MvPolynomial τ C₀) :
    tensorLift g m hm P₀ hrel hmap (aeval (R := C₀) (fun i ↦ (1 : C₀) ⊗ₜ[P]
        algebraMap (quot g) (ring g m hm) (Ideal.Quotient.mk _ (X i))) p) =
      aeval P₀.val p := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  exact congrArg (fun v ↦ aeval v p) (funext fun i ↦ by
    simp [tensorLift, toAlgHom_algebraMap, quotToAlgHom_mk])

omit [Finite τ] in
/-- The base change of the localized quotient to `C₀` is isomorphic to `D₀` via `tensorLift`. -/
theorem bijective_tensorLift : Function.Bijective (tensorLift g m hm P₀ hrel hmap) := by
  have hl : Function.LeftInverse (tensorLift g m hm P₀ hrel hmap)
      (tensorInv g m hm P₀ hrel) := by
    intro d
    obtain ⟨p, rfl⟩ := P₀.aeval_val_surjective d
    rw [tensorInv_aeval, tensorLift_aeval]
  have hr : (tensorInv g m hm P₀ hrel).comp (tensorLift g m hm P₀ hrel hmap) =
      AlgHom.id C₀ _ := by
    refine Algebra.TensorProduct.ext (Subsingleton.elim _ _)
      (IsLocalization.algHom_ext (Submonoid.powers (jac g m hm))
        (Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext fun i ↦ ?_)))
    have h := tensorLift_aeval g m hm P₀ hrel hmap (X i)
    have h' := tensorInv_aeval g m hm P₀ hrel (X i)
    simp only [aeval_X] at h h'
    exact (congrArg _ h).trans h'
  exact ⟨Function.LeftInverse.injective (g := tensorInv g m hm P₀ hrel)
    fun x ↦ DFunLike.congr_fun hr x, hl.surjective⟩

end BaseChange

section Roots

variable {E : Type u} [CommRing E] [Algebra P E]

/-- The map of the quotient to an algebra in which `v` is a root of the relations. -/
noncomputable def quotLift (v : τ → E) (hv : ∀ j, aeval v (g j) = 0) : quot g →ₐ[P] E :=
  Ideal.Quotient.liftₐ _ (aeval v) (by
    intro x hx
    refine Submodule.span_induction ?_ (by simp) (fun _ _ _ _ ha hb ↦ by simp [ha, hb])
      (fun a _ _ hb ↦ by simp [hb]) hx
    rintro _ ⟨j, rfl⟩
    exact hv j)

omit [Finite τ] [Finite ρ] in
/-- `quotLift` sends the class of a polynomial `x` to `x` evaluated at `v`. -/
theorem quotLift_mk (v : τ → E) (hv : ∀ j, aeval v (g j) = 0) (x : MvPolynomial τ P) :
    quotLift g v hv (Ideal.Quotient.mk _ x) = aeval v x := rfl

/-- **The universal property of the localized quotient**: a root of the relations at which the
Jacobian is a unit. -/
noncomputable def liftOfRoots (v : τ → E) (hv : ∀ j, aeval v (g j) = 0)
    (hu : IsUnit (quotLift g v hv (jac g m hm))) : ring g m hm →ₐ[P] E :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (jac g m hm)) (f := quotLift g v hv) (by
    rintro ⟨_, n, rfl⟩
    simpa using hu.pow n)

omit [Finite τ] in
/-- `liftOfRoots` restricts to `quotLift` on the quotient. -/
theorem liftOfRoots_algebraMap (v : τ → E) (hv : ∀ j, aeval v (g j) = 0)
    (hu : IsUnit (quotLift g v hv (jac g m hm))) (x : quot g) :
    liftOfRoots g m hm v hv hu (algebraMap _ _ x) = quotLift g v hv x :=
  IsLocalization.lift_eq _ _

end Roots

end Algebra.LocalizedQuotient

end
