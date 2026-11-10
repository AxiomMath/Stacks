module

public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.JacobianDualizingModule
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingComposition.Factorizations
public import StacksFrontier.AlgebraicGeometry.Discriminant.FinitePresentationFactorization
public import StacksFrontier.RingTheory.Different.Formula.LocalizedCompleteIntersectionBaseChange
public import StacksFrontier.RingTheory.FinitePresentation.IsoDescent
public import StacksFrontier.RingTheory.TraceElement.BaseChangeIso

/-!
# The dualizing module of a localized complete intersection over an arbitrary ring

Let `A` be a ring, `h, f_1, …, f_n` polynomials in `n` variables over `A`, and
`B = A[x_1, …, x_n, 1/h]/(f_1, …, f_n)` quasi-finite over `A`. Over a Noetherian `A`,
`ω_{B/A}` is free of rank one on a generator carrying `det(∂f_i/∂x_j)` to the trace element
(`Stacks.Discriminant.exists_linearEquiv_dualizingModule_map_det_eq_traceElement`). This file
extends the statement to an arbitrary ring `A` by descent to a Noetherian ring, and states Tag
0BWH in full.

## Main results

* `Stacks.Discriminant.exists_linearEquiv_dualizingModule_jacobianDet`: **Stacks Project, Tag
  0BWH**.
* `Stacks.Discriminant.exists_linearEquiv_traceCandidate_of_algEquiv`: the isomorphism
  `B ≅ ω_{B/A}` carrying the Jacobian determinant to the canonical element, over an arbitrary
  ring, for every finite-open factorization with finitely presented intermediate algebra.
* `Stacks.Discriminant.exists_stage_finiteOpenFactorization`: such a factorization is the base
  change of a finite-open factorization over a subring of `A` of finite type over `ℤ`.
* `Stacks.Discriminant.exists_subring_models`: models of `B` and of a finite, finitely presented
  `A`-algebra over such a subring.
* `Stacks.Discriminant.exists_linearEquiv_traceCandidate_of_isPushout`: the Noetherian statement
  for any base change of a localized complete intersection.

## Implementation notes

The source defines the relative dualizing module and the trace element only for Noetherian rings
(Section 0BUK and Definition 0BT6). Over an arbitrary ring the dualizing module is computed from a
finite-open factorization whose intermediate algebra is finitely presented, and the trace element
is `Stacks.Discriminant.dualizingModule.traceCandidate`, which over a Noetherian ring is the trace
element by definition. Finite presentation cannot be dropped: see the docstring of the main
theorem.

The descent writes `A` as the directed union of its subrings of finite type over `ℤ`
(`Algebra.FiniteTypeSystem`). The intermediate algebra and `B` have finitely presented models
over one such subring, the map between them and finitely many local isomorphisms covering
`Spec B` descend to a later stage, and there they assemble into a finite-open factorization
(`Stacks.Discriminant.FiniteOpenFactorization.ofLocalData`). The Noetherian case is applied at
that stage, and the resulting isomorphism is base changed back to `A` by Tag 0BVF.

## References

* [Stacks Project, Tag 0BWH](https://stacks.math.columbia.edu/tag/0BWH)
* [Stacks Project, Tag 0BVF](https://stacks.math.columbia.edu/tag/0BVF)
* [Stacks Project, Tag 0BTB](https://stacks.math.columbia.edu/tag/0BTB)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Stacks.Discriminant

section Noetherian

variable {R : Type u} [CommRing R] (n : ℕ) (h : MvPolynomial (Fin n) R)
  (f : Fin n → MvPolynomial (Fin n) R)

/-- The Jacobian determinant `det(∂f_i/∂x_j)` in `R[x_1, …, x_n, 1/h]/(f_1, …, f_n)`. -/
noncomputable abbrev jacobianDet : localizedCompleteIntersection R n h f :=
  Matrix.det fun i j : Fin n ↦ algebraMap (MvPolynomial (Fin n) R)
    (localizedCompleteIntersection R n h f) (MvPolynomial.pderiv j (f i))

/-- The map induced by a ring map `R → A` carries the Jacobian determinant to the Jacobian
determinant. -/
theorem localizedCompleteIntersectionMap_jacobianDet (A : Type*) [CommRing A] [Algebra R A] :
    localizedCompleteIntersectionMap R A n h f (jacobianDet n h f) =
      jacobianDet n (MvPolynomial.map (algebraMap R A) h)
        (fun i ↦ MvPolynomial.map (algebraMap R A) (f i)) := by
  have := localizedCompleteIntersectionBaseChange_tmul_det R A n h f
  rw [localizedCompleteIntersectionBaseChange_tmul, one_smul] at this
  exact this

variable {n h f}

/-- A base change of a localized complete intersection is isomorphic over `A₀` to the localized
complete intersection over `A₀`, compatibly with the maps from the one over `R`. -/
private theorem exists_algEquiv_localizedCompleteIntersection_of_isPushout
    {A₀ : Type u} [CommRing A₀] [Algebra R A₀]
    {B₀ : Type u} [CommRing B₀] [Algebra A₀ B₀] [Algebra (localizedCompleteIntersection R n h f) B₀]
    [Algebra R B₀] [IsScalarTower R A₀ B₀]
    [IsScalarTower R (localizedCompleteIntersection R n h f) B₀]
    [Algebra.IsPushout R A₀ (localizedCompleteIntersection R n h f) B₀] :
    ∃ e : localizedCompleteIntersection A₀ n (MvPolynomial.map (algebraMap R A₀) h)
        (fun i ↦ MvPolynomial.map (algebraMap R A₀) (f i)) ≃ₐ[A₀] B₀,
      ∀ x, e.symm (algebraMap _ B₀ x) = localizedCompleteIntersectionMap R A₀ n h f x := by
  let L := localizedCompleteIntersection A₀ n (MvPolynomial.map (algebraMap R A₀) h)
    (fun i ↦ MvPolynomial.map (algebraMap R A₀) (f i))
  let : Algebra (localizedCompleteIntersection R n h f) L :=
    (localizedCompleteIntersectionMap R A₀ n h f).toRingHom.toAlgebra
  have : IsScalarTower R (localizedCompleteIntersection R n h f) L :=
    IsScalarTower.of_algebraMap_eq fun r ↦
      ((localizedCompleteIntersectionMap R A₀ n h f).commutes r).symm
  have := isPushout_localizedCompleteIntersection R A₀ n h f
  refine ⟨(Algebra.IsPushout.equiv R A₀ (localizedCompleteIntersection R n h f) L).symm.trans
      (Algebra.IsPushout.equiv R A₀ (localizedCompleteIntersection R n h f) B₀), fun x ↦ ?_⟩
  rw [AlgEquiv.symm_apply_eq]
  change _ = Algebra.IsPushout.equiv R A₀ (localizedCompleteIntersection R n h f) B₀
    ((Algebra.IsPushout.equiv R A₀ (localizedCompleteIntersection R n h f) L).symm
      (algebraMap _ L x))
  rw [Algebra.IsPushout.equiv_symm_algebraMap_right, Algebra.IsPushout.equiv_tmul, map_one,
    one_mul]

/-- An algebra over a Noetherian ring that is a base change of a localized complete intersection
is flat as soon as it admits a finite-open factorization. -/
theorem flat_of_isPushout_localizedCompleteIntersection
    {A₀ : Type u} [CommRing A₀] [Algebra R A₀]
    {B₀ : Type u} [CommRing B₀] [Algebra A₀ B₀] [Algebra (localizedCompleteIntersection R n h f) B₀]
    [Algebra R B₀] [IsScalarTower R A₀ B₀]
    [IsScalarTower R (localizedCompleteIntersection R n h f) B₀]
    [Algebra.IsPushout R A₀ (localizedCompleteIntersection R n h f) B₀]
    (F₀ : FiniteOpenFactorization.{u, u, w} A₀ B₀) : Module.Flat A₀ B₀ := by
  let L := localizedCompleteIntersection A₀ n (MvPolynomial.map (algebraMap R A₀) h)
    (fun i ↦ MvPolynomial.map (algebraMap R A₀) (f i))
  obtain ⟨e, -⟩ := exists_algEquiv_localizedCompleteIntersection_of_isPushout (R := R) (n := n)
    (h := h) (f := f) (A₀ := A₀) (B₀ := B₀)
  let F₀' := retargetFactorization F₀ e.symm
  have : Algebra.QuasiFinite A₀ L :=
    (dualizingModule.finiteType_quasiFinite_of_finiteOpenFactorization F₀').2
  have : Module.Flat A₀ L := flat_localizedCompleteIntersection A₀ n _ _
  exact Module.Flat.of_linearEquiv e.symm.toLinearEquiv

/-- **The Noetherian case for a base change of a localized complete intersection.** Let
`B₀ = A₀ ⊗_R R[x_1, …, x_n, 1/h]/(f_1, …, f_n)` over a Noetherian `R`-algebra `A₀`, given as a
pushout. For every finite-open factorization `F₀` of `B₀` over `A₀` there is an isomorphism
`B₀ ≅ ω_{F₀}` carrying the image of `det(∂f_i/∂x_j)` to the canonical element. -/
theorem exists_linearEquiv_traceCandidate_of_isPushout
    {A₀ : Type u} [CommRing A₀] [IsNoetherianRing A₀] [Algebra R A₀]
    {B₀ : Type u} [CommRing B₀] [Algebra A₀ B₀] [Algebra (localizedCompleteIntersection R n h f) B₀]
    [Algebra R B₀] [IsScalarTower R A₀ B₀]
    [IsScalarTower R (localizedCompleteIntersection R n h f) B₀]
    [Algebra.IsPushout R A₀ (localizedCompleteIntersection R n h f) B₀] [Module.Flat A₀ B₀]
    (F₀ : FiniteOpenFactorization.{u, u, w} A₀ B₀) [Module.FinitePresentation A₀ F₀.middle] :
    ∃ ε₀ : B₀ ≃ₗ[B₀] dualizingModule F₀,
      ε₀ (algebraMap (localizedCompleteIntersection R n h f) B₀ (jacobianDet n h f)) =
        dualizingModule.traceCandidate F₀ := by
  let L := localizedCompleteIntersection A₀ n (MvPolynomial.map (algebraMap R A₀) h)
    (fun i ↦ MvPolynomial.map (algebraMap R A₀) (f i))
  obtain ⟨e, he⟩ := exists_algEquiv_localizedCompleteIntersection_of_isPushout (R := R) (n := n)
    (h := h) (f := f) (A₀ := A₀) (B₀ := B₀)
  let F₀' := retargetFactorization F₀ e.symm
  have : Algebra.QuasiFinite A₀ L :=
    (dualizingModule.finiteType_quasiFinite_of_finiteOpenFactorization F₀').2
  have : Module.Flat A₀ L := flat_localizedCompleteIntersection A₀ n _ _
  obtain ⟨ε', hε'⟩ := exists_linearEquiv_dualizingModule_map_det_eq_traceElement A₀ n
    (MvPolynomial.map (algebraMap R A₀) h) (fun i ↦ MvPolynomial.map (algebraMap R A₀) (f i)) F₀'
  let : Algebra L B₀ := e.toAlgHom.toRingHom.toAlgebra
  have he' : ∀ b : L, e.symm (algebraMap L B₀ b) = b := fun b ↦ e.symm_apply_apply b
  let : Module L (dualizingModule F₀) := Module.compHom _ (algebraMap L B₀)
  let eR : dualizingModule F₀ ≃ₗ[L] dualizingModule F₀' :=
    dualizingModule_retargetEquiv F₀ e.symm he'
  have heR : eR (dualizingModule.traceCandidate F₀) = dualizingModule.traceCandidate F₀' :=
    dualizingModule.retargetEquiv_traceCandidate F₀ e.symm he'
  let ε₀ : B₀ ≃ₗ[B₀] dualizingModule F₀ :=
    { toFun := fun b ↦ eR.symm (ε' (e.symm b))
      invFun := fun z ↦ e (ε'.symm (eR z))
      map_add' := fun x y ↦ by simp
      map_smul' := fun b x ↦ by
        change eR.symm (ε' (e.symm (b * x))) = b • eR.symm (ε' (e.symm x))
        rw [map_mul, ← smul_eq_mul, map_smul, map_smul]
        exact congrArg (fun c : B₀ ↦ c • eR.symm (ε' (e.symm x))) (e.apply_symm_apply b)
      left_inv := fun b ↦ by simp
      right_inv := fun z ↦ by simp }
  refine ⟨ε₀, ?_⟩
  change eR.symm (ε' (e.symm _)) = _
  rw [he, LinearEquiv.symm_apply_eq, heR]
  change ε' (localizedCompleteIntersectionMap R A₀ n h f (jacobianDet n h f)) = _
  rw [localizedCompleteIntersectionMap_jacobianDet]
  exact hε'

end Noetherian

section Models

/-- A finite, finitely presented algebra has a finite presentation in which every generator
satisfies one of the relations as a monic polynomial in that generator alone. -/
theorem exists_presentation_monic_relations (A C : Type*) [CommRing A] [CommRing C]
    [Algebra A C] [Algebra.FinitePresentation A C] [Module.Finite A C] :
    ∃ (k l : ℕ) (P : Algebra.Presentation A C (Fin k) (Fin l ⊕ Fin k))
      (p : Fin k → Polynomial A), (∀ i, (p i).Monic) ∧
        ∀ i, P.relation (Sum.inr i) = Polynomial.aeval (MvPolynomial.X i) (p i) := by
  classical
  let P₀ := Algebra.Presentation.ofFinitePresentation A C
  have hint (i) : IsIntegral A (P₀.val i) := Algebra.IsIntegral.isIntegral _
  choose p hpm hp using hint
  let g : Fin (Algebra.Presentation.ofFinitePresentationVars A C) →
      MvPolynomial (Fin (Algebra.Presentation.ofFinitePresentationVars A C)) A :=
    fun i ↦ Polynomial.aeval (MvPolynomial.X i) (p i)
  have hg (i) : g i ∈ P₀.ker := by
    rw [P₀.ker_eq_ker_aeval_val, RingHom.mem_ker]
    change MvPolynomial.aeval P₀.val (Polynomial.aeval (MvPolynomial.X i) (p i)) = 0
    rw [← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]
    exact hp i
  refine ⟨_, _,
    { toGenerators := P₀.toGenerators
      relation := Sum.elim P₀.relation g
      span_range_relation_eq_ker := ?_ }, p, hpm, fun i ↦ rfl⟩
  rw [Set.Sum.elim_range, Ideal.span_union, P₀.span_range_relation_eq_ker]
  refine le_antisymm (sup_le le_rfl (Ideal.span_le.mpr ?_)) le_sup_left
  rintro _ ⟨i, rfl⟩
  exact hg i

/-- The model over `R₀` of a presentation whose relations include, for each generator, a monic
polynomial in that generator with coefficients coming from `R₀`, is finite over `R₀`. -/
theorem finite_modelOfHasCoeffs {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]
    {k l : ℕ} (P : Algebra.Presentation A C (Fin k) (Fin l ⊕ Fin k))
    (p : Fin k → Polynomial A) (hpm : ∀ i, (p i).Monic)
    (hrel : ∀ i, P.relation (Sum.inr i) = Polynomial.aeval (MvPolynomial.X i) (p i))
    (R₀ : Type*) [CommRing R₀] [Algebra R₀ A] [Algebra R₀ C] [IsScalarTower R₀ A C]
    [FaithfulSMul R₀ A] [P.HasCoeffs R₀]
    (hcoeff : ∀ i m, (p i).coeff m ∈ Set.range (algebraMap R₀ A)) :
    Module.Finite R₀ (P.ModelOfHasCoeffs R₀) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · have : Subsingleton R₀ := (FaithfulSMul.algebraMap_injective R₀ A).subsingleton
    have : Subsingleton (P.ModelOfHasCoeffs R₀) := Module.subsingleton R₀ _
    infer_instance
  have hinj : Function.Injective (MvPolynomial.map (σ := Fin k) (algebraMap R₀ A)) :=
    MvPolynomial.map_injective _ (FaithfulSMul.algebraMap_injective R₀ A)
  have hlift (i : Fin k) : ∃ q : Polynomial R₀, q.Monic ∧
      P.relationOfHasCoeffs R₀ (Sum.inr i) = Polynomial.aeval (MvPolynomial.X i) q := by
    have hl : p i ∈ Polynomial.lifts (algebraMap R₀ A) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr (hcoeff i)
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (hpm i)
    refine ⟨q, hqm, hinj ?_⟩
    rw [Algebra.Presentation.map_relationOfHasCoeffs, hrel, ← hq]
    simp only [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.eval₂_map]
    congr 1
    · ext a
      simp
    · simp
  have hint (i : Fin k) : IsIntegral R₀
      (Ideal.Quotient.mk (Ideal.span (Set.range (P.relationOfHasCoeffs R₀)))
        (MvPolynomial.X i)) := by
    obtain ⟨q, hqm, hq⟩ := hlift i
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Ideal.Quotient.mkₐ_eq_mk R₀, Polynomial.aeval_algHom_apply,
      ← hq, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨_, rfl⟩
  have hadj : Algebra.adjoin R₀ (Set.range fun i : Fin k ↦
      Ideal.Quotient.mk (Ideal.span (Set.range (P.relationOfHasCoeffs R₀)))
        (MvPolynomial.X i)) = ⊤ := by
    have hs : (Set.range fun i : Fin k ↦
        Ideal.Quotient.mk (Ideal.span (Set.range (P.relationOfHasCoeffs R₀)))
          (MvPolynomial.X i)) =
        (Ideal.Quotient.mkₐ R₀ (Ideal.span (Set.range (P.relationOfHasCoeffs R₀)))) ''
          Set.range MvPolynomial.X := by
      rw [← Set.range_comp]
      rfl
    rw [hs, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top,
      AlgHom.range_eq_top]
    exact Ideal.Quotient.mkₐ_surjective R₀ _
  refine ⟨?_⟩
  rw [← Algebra.top_toSubmodule, ← hadj]
  exact fg_adjoin_of_finite (Set.finite_range _) (by rintro _ ⟨i, rfl⟩; exact hint i)

/-- **Models over a subring of finite type over `ℤ`.** Let `B ≅ A[x_1, …, x_n, 1/h]/(f)` and let
`C` be a finite, finitely presented `A`-algebra. There is a subring `R₀ ⊆ A` of finite type over
`ℤ` containing the coefficients of `h` and `f`, over which `B` is the base change of
`R₀[x_1, …, x_n, 1/h₀]/(f₀)` with the Jacobian determinant mapping to the Jacobian determinant,
and over which `C` is the base change of a finite, finitely presented `R₀`-algebra. -/
theorem exists_subring_models (A : Type u) [CommRing A] (n : ℕ) (h : MvPolynomial (Fin n) A)
    (f : Fin n → MvPolynomial (Fin n) A) {B : Type u} [CommRing B] [Algebra A B]
    (eB : localizedCompleteIntersection A n h f ≃ₐ[A] B) (C : Type w) [CommRing C] [Algebra A C]
    [Module.Finite A C] [Module.FinitePresentation A C] :
    ∃ (R₀ : Subring A) (_ : Algebra.FiniteType ℤ R₀) (h₀ : MvPolynomial (Fin n) R₀)
      (f₀ : Fin n → MvPolynomial (Fin n) R₀)
      (_ : Algebra (localizedCompleteIntersection R₀ n h₀ f₀) B)
      (_ : IsScalarTower R₀ (localizedCompleteIntersection R₀ n h₀ f₀) B)
      (_ : Algebra.IsPushout R₀ A (localizedCompleteIntersection R₀ n h₀ f₀) B)
      (T₀ : Type u) (_ : CommRing T₀) (_ : Algebra R₀ T₀) (_ : Algebra.FinitePresentation R₀ T₀)
      (_ : Module.Finite R₀ T₀) (_ : Algebra T₀ C) (_ : IsScalarTower R₀ T₀ C)
      (_ : Algebra.IsPushout R₀ A T₀ C),
      algebraMap (localizedCompleteIntersection R₀ n h₀ f₀) B (jacobianDet n h₀ f₀) =
        eB (jacobianDet n h f) := by
  classical
  have : Algebra.FinitePresentation A C :=
    (Module.FinitePresentation.iff_finitePresentation_of_finite A C).mp inferInstance
  obtain ⟨k, l, P, p, hpm, hrel⟩ := exists_presentation_monic_relations A C
  let s : Set A := (h.coeffs : Set A) ∪ (⋃ i, ((f i).coeffs : Set A)) ∪ P.coeffs ∪
    ⋃ i, ((p i).coeffs : Set A)
  have hs : s.Finite :=
    (((Finset.finite_toSet _).union (Set.finite_iUnion fun i ↦ Finset.finite_toSet _)).union
      P.finite_coeffs).union (Set.finite_iUnion fun i ↦ Finset.finite_toSet _)
  obtain ⟨R₀, hR₀fin, hrange⟩ : ∃ R₀ : Subring A, Algebra.FiniteType ℤ R₀ ∧
      ∀ x ∈ s, x ∈ Set.range (algebraMap R₀ A) :=
    ⟨(Algebra.adjoin ℤ s).toSubring,
      Algebra.FiniteTypeSystem.finiteType_int_of_algebra _ _
        ((Subalgebra.fg_iff_finiteType _).mp ⟨hs.toFinset, by simp⟩),
      fun x hx ↦ ⟨⟨x, Algebra.subset_adjoin hx⟩, rfl⟩⟩
  -- the localized complete intersection
  have hh : h ∈ Set.range (MvPolynomial.map (algebraMap R₀ A)) :=
    MvPolynomial.mem_range_map_iff_coeffs_subset.mpr fun x hx ↦
      hrange x (Or.inl (Or.inl (Or.inl hx)))
  have hf (i : Fin n) : f i ∈ Set.range (MvPolynomial.map (algebraMap R₀ A)) :=
    MvPolynomial.mem_range_map_iff_coeffs_subset.mpr fun x hx ↦
      hrange x (Or.inl (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩))))
  choose h₀ hh₀ using hh
  choose f₀ hf₀ using hf
  let S₀ := localizedCompleteIntersection R₀ n h₀ f₀
  let e : localizedCompleteIntersection A n (MvPolynomial.map (algebraMap R₀ A) h₀)
      (fun i ↦ MvPolynomial.map (algebraMap R₀ A) (f₀ i)) ≃ₐ[A] B :=
    (localizedCompleteIntersectionCongr hh₀ (funext hf₀)).trans eB
  let φ : S₀ →ₐ[R₀] B :=
    (e.toAlgHom.restrictScalars R₀).comp (localizedCompleteIntersectionMap R₀ A n h₀ f₀)
  let : Algebra S₀ B := φ.toRingHom.toAlgebra
  have : IsScalarTower R₀ S₀ B := IsScalarTower.of_algebraMap_eq fun r ↦ (φ.commutes r).symm
  have hpushB : Algebra.IsPushout R₀ A S₀ B := by
    let : Algebra S₀ (localizedCompleteIntersection A n (MvPolynomial.map (algebraMap R₀ A) h₀)
        (fun i ↦ MvPolynomial.map (algebraMap R₀ A) (f₀ i))) :=
      (localizedCompleteIntersectionMap R₀ A n h₀ f₀).toRingHom.toAlgebra
    have : IsScalarTower R₀ S₀ (localizedCompleteIntersection A n
        (MvPolynomial.map (algebraMap R₀ A) h₀)
        (fun i ↦ MvPolynomial.map (algebraMap R₀ A) (f₀ i))) :=
      IsScalarTower.of_algebraMap_eq fun r ↦
        ((localizedCompleteIntersectionMap R₀ A n h₀ f₀).commutes r).symm
    have := isPushout_localizedCompleteIntersection R₀ A n h₀ f₀
    exact ⟨IsBaseChange.of_equiv
      ((Algebra.IsPushout.equiv R₀ A S₀ _).toLinearEquiv.trans e.toLinearEquiv) fun x ↦ by
        simp [Algebra.IsPushout.equiv_tmul]; rfl⟩
  -- the model of `C`
  have : P.HasCoeffs R₀ := ⟨fun x hx ↦ hrange x (Or.inl (Or.inr hx))⟩
  let T₀ := P.ModelOfHasCoeffs R₀
  have : Module.Finite R₀ T₀ := finite_modelOfHasCoeffs P p hpm hrel R₀ fun i m ↦ by
    by_cases hm : (p i).coeff m = 0
    · exact ⟨0, by simp [hm]⟩
    · exact hrange _ (Or.inr (Set.mem_iUnion.mpr ⟨i, Polynomial.coeff_mem_coeffs hm⟩))
  let eC := P.tensorModelOfHasCoeffsEquiv R₀
  let ψ : T₀ →ₐ[R₀] C :=
    (eC.toAlgHom.restrictScalars R₀).comp Algebra.TensorProduct.includeRight
  let : Algebra T₀ C := ψ.toRingHom.toAlgebra
  have : IsScalarTower R₀ T₀ C := IsScalarTower.of_algebraMap_eq fun r ↦ (ψ.commutes r).symm
  have hpushC : Algebra.IsPushout R₀ A T₀ C :=
    ⟨IsBaseChange.of_equiv (eC.toLinearEquiv) fun _ ↦ rfl⟩
  refine ⟨R₀, hR₀fin, h₀, f₀, inferInstance, inferInstance, hpushB, T₀, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hpushC, ?_⟩
  change e (localizedCompleteIntersectionMap R₀ A n h₀ f₀ (jacobianDet n h₀ f₀)) = _
  rw [localizedCompleteIntersectionMap_jacobianDet]
  change eB (localizedCompleteIntersectionCongr hh₀ (funext hf₀) _) = _
  congr 1
  have hf' : (fun i ↦ MvPolynomial.map (algebraMap R₀ A) (f₀ i)) = f := funext hf₀
  subst hh₀ hf'
  rfl

end Models

section Descent

/-- The images in the target of finitely many elements of the intermediate algebra whose basic
opens lie in the image of the target generate the unit ideal. -/
theorem FiniteOpenFactorization.exists_cover {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] (F : FiniteOpenFactorization.{u, v, w} A B) :
    ∃ (ι : Type v) (_ : Fintype ι) (c : ι → F.middle) (a : ι → B),
      (∀ i, (PrimeSpectrum.basicOpen (c i) : Set (PrimeSpectrum F.middle)) ⊆
        Set.range (PrimeSpectrum.comap (algebraMap F.middle B))) ∧
      ∑ i, a i * algebraMap F.middle B (c i) = 1 := by
  classical
  let S : Set B := {b | ∃ c : F.middle, (PrimeSpectrum.basicOpen c : Set (PrimeSpectrum F.middle)) ⊆
    Set.range (PrimeSpectrum.comap (algebraMap F.middle B)) ∧ algebraMap F.middle B c = b}
  have hS : Ideal.span S = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hne
    let Q : PrimeSpectrum B := ⟨q, hq.isPrime⟩
    obtain ⟨_, ⟨_, ⟨c, rfl⟩, rfl⟩, hpc, hc⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
        (show PrimeSpectrum.comap (algebraMap F.middle B) Q ∈
          Set.range (PrimeSpectrum.comap (algebraMap F.middle B)) from ⟨Q, rfl⟩)
        F.isOpenEmbedding_comap.isOpen_range
    exact hpc (hle (Ideal.subset_span ⟨c, hc, rfl⟩))
  obtain ⟨T, hTS, hT⟩ := Submodule.mem_span_finite_of_mem_span
    (show (1 : B) ∈ Ideal.span S from hS ▸ Submodule.mem_top)
  obtain ⟨a, -, ha⟩ := Submodule.mem_span_finset.mp hT
  choose c hc hcb using fun t : T ↦ hTS t.2
  refine ⟨T, inferInstance, c, fun t ↦ a t, hc, ?_⟩
  rw [← ha, ← Finset.sum_coe_sort T]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [hcb, smul_eq_mul]

end Descent

section Main

open Algebra.FiniteTypeSystem

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **Descent of a finite-open factorization.** Let `R₀ ⊆ A` be a subring of finite type over
`ℤ`, and let `B` and the intermediate algebra of a finite-open factorization `F` of `A → B` be the
base changes of finitely presented `R₀`-algebras `S₀` and `T₀`, with `T₀` finite. Then for some
subring `R_λ ⊇ R₀` of finite type over `ℤ` there is a finite-open factorization of
`R_λ ⊗_{R₀} S₀` over `R_λ` whose base change to `A` is `F`. -/
theorem exists_stage_finiteOpenFactorization {A : Type u} [CommRing A] (R₀ : Subring A)
    [Algebra.FiniteType ℤ R₀]
    (T₀ S₀ : Type u) [CommRing T₀] [CommRing S₀] [Algebra R₀ T₀] [Algebra R₀ S₀]
    [Algebra.FinitePresentation R₀ T₀] [Algebra.FinitePresentation R₀ S₀] [Module.Finite R₀ T₀]
    {B : Type u} [CommRing B] [Algebra A B] [Algebra S₀ B] [IsScalarTower R₀ S₀ B]
    [Algebra.IsPushout R₀ A S₀ B]
    (F : FiniteOpenFactorization.{u, u, w} A B) [Algebra T₀ F.middle]
    [IsScalarTower R₀ T₀ F.middle] [Algebra.IsPushout R₀ A T₀ F.middle] :
    ∃ (i : Index R₀) (F₀ : FiniteOpenFactorization.{u, u, u} (Base R₀ i) (Ring R₀ S₀ i))
      (r : A ⊗[Base R₀ i] F₀.middle ≃ₐ[A] F.middle),
      haveI := ringToRing_isPushout R₀ S₀ (S := B) i
      ∀ x, algebraMap F.middle B (r x) =
        Algebra.IsPushout.equiv (Base R₀ i) A (Ring R₀ S₀ i) B
          (algebraMap (FiniteOpenFactorization.baseChange F₀ A).middle
            (A ⊗[Base R₀ i] Ring R₀ S₀ i) x) := by
  classical
  have hcolS := ring_colimit R₀ S₀ (S := B)
  have hcolT := ring_colimit R₀ T₀ (S := F.middle)
  -- the map `T₀ → C → B` descends to a stage
  let w : T₀ →ₐ[R₀] B :=
    ((IsScalarTower.toAlgHom A F.middle B).restrictScalars R₀).comp
      (IsScalarTower.toAlgHom R₀ T₀ F.middle)
  obtain ⟨i₁, ψ₁, hψ₁⟩ := AlgHom.exists_comp_eq_of_finitePresentation
    (G := Ring R₀ S₀) (fun _ _ h ↦ ringMap R₀ S₀ h) (fun i ↦ ringToRing R₀ S₀ (S := B) i)
    (fun _ _ h x ↦ ring_cocone R₀ S₀ h x) hcolS.1
    (fun i x hx ↦ hcolS.2 i x 0 (hx.trans (map_zero _).symm) |>.imp fun _ ⟨h, e⟩ ↦
      ⟨h, e.trans (map_zero _)⟩) w
  -- a finite cover of the target by local isomorphisms
  obtain ⟨ι, _, c, a, hc, hca⟩ := F.exists_cover
  choose jc γ hγ using fun t ↦ hcolT.1 (c t)
  choose ja α hα using fun t ↦ hcolS.1 (a t)
  obtain ⟨i₂, hi₂⟩ := (insert i₁ (Finset.univ.image jc ∪ Finset.univ.image ja)).exists_le
  have h12 : i₁ ≤ i₂ := hi₂ _ (Finset.mem_insert_self _ _)
  have hjc (t : ι) : jc t ≤ i₂ := hi₂ _ (by simp)
  have hja (t : ι) : ja t ≤ i₂ := hi₂ _ (by simp)
  let ψ : T₀ →ₐ[R₀] Ring R₀ S₀ i₂ := (ringMap R₀ S₀ h12).comp ψ₁
  have hψ (t : T₀) : algebraMap (Ring R₀ S₀ i₂) B (ψ t) =
      algebraMap F.middle B (algebraMap T₀ F.middle t) := by
    change ringToRing R₀ S₀ i₂ (ringMap R₀ S₀ h12 (ψ₁ t)) = _
    rw [ring_cocone]
    exact DFunLike.congr_fun hψ₁ t
  let γ' (t : ι) : Ring R₀ T₀ i₂ := ringMap R₀ T₀ (hjc t) (γ t)
  let α' (t : ι) : Ring R₀ S₀ i₂ := ringMap R₀ S₀ (hja t) (α t)
  have hγ' (t : ι) : ringToRing R₀ T₀ (S := F.middle) i₂ (γ' t) = c t := by
    rw [ring_cocone, hγ]
  have hα' (t : ι) : ringToRing R₀ S₀ (S := B) i₂ (α' t) = a t := by
    rw [ring_cocone, hα]
  -- the relation `∑ aₜ cₜ = 1` descends
  have hrel : ringToRing R₀ S₀ (S := B) i₂
      (∑ t, α' t * stageMap R₀ ψ le_rfl (γ' t)) = ringToRing R₀ S₀ (S := B) i₂ 1 := by
    rw [map_sum, map_one, ← hca]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [map_mul, hα', ringToRing_stageMap R₀ ψ hψ, hγ']
  obtain ⟨i₃, h23, hi₃⟩ := hcolS.2 i₂ _ _ hrel
  -- local bijectivity descends
  have hct (t : ι) : Function.Bijective (Localization.awayMap (algebraMap F.middle B)
      (algebraMap (Ring R₀ T₀ i₂) F.middle (γ' t))) := by
    rw [show algebraMap (Ring R₀ T₀ i₂) F.middle (γ' t) = c t from hγ' t]
    exact F.awayMap_bijective (c t) (hc t)
  have hloc (t : ι) := exists_forall_bijective_awayMap R₀ T₀ S₀ (C := F.middle) (B := B)
    i₂ ψ hψ (γ' t) (hct t)
  choose i' hi' hbij using hloc
  obtain ⟨k, hk⟩ := (insert i₃ (Finset.univ.image i')).exists_le
  have h3k : i₃ ≤ k := hk _ (Finset.mem_insert_self _ _)
  have h2k : i₂ ≤ k := h23.trans h3k
  have hik (t : ι) : i' t ≤ k := hk _ (by simp)
  let : Algebra (Ring R₀ T₀ k) (Ring R₀ S₀ k) := (stageMap R₀ ψ h2k).toRingHom.toAlgebra
  have : IsScalarTower (Base R₀ k) (Ring R₀ T₀ k) (Ring R₀ S₀ k) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ ((stageMap R₀ ψ h2k).commutes x).symm
  have H := FiniteOpenFactorization.forall_exists_awayMap_bijective_of_span_eq_top
    (B := Ring R₀ S₀ k) (Set.range fun t ↦ ringMap R₀ T₀ h2k (γ' t)) ?_ ?_
  · let F₀ := FiniteOpenFactorization.ofLocalData (A := Base R₀ k) H
    have := ringToRing_isPushout R₀ T₀ (S := F.middle) k
    have := ringToRing_isPushout R₀ S₀ (S := B) k
    refine ⟨k, F₀, Algebra.IsPushout.equiv (Base R₀ k) A (Ring R₀ T₀ k) F.middle, fun x ↦ ?_⟩
    have key : ((IsScalarTower.toAlgHom A F.middle B).comp
        (Algebra.IsPushout.equiv (Base R₀ k) A (Ring R₀ T₀ k) F.middle).toAlgHom) =
        (Algebra.IsPushout.equiv (Base R₀ k) A (Ring R₀ S₀ k) B).toAlgHom.comp
          (Algebra.TensorProduct.map (AlgHom.id A A) (stageMap R₀ ψ h2k)) := by
      refine Algebra.TensorProduct.ext (AlgHom.ext fun x ↦ ?_) (AlgHom.ext fun y ↦ ?_)
      · simp [Algebra.IsPushout.equiv_tmul, ← IsScalarTower.algebraMap_apply]
      · simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_restrictScalars',
          Algebra.TensorProduct.includeRight_apply, AlgEquiv.coe_toAlgHom,
          IsScalarTower.coe_toAlgHom', Algebra.TensorProduct.map_tmul,
          Algebra.IsPushout.equiv_tmul, map_one, one_mul]
        exact (ringToRing_stageMap R₀ ψ hψ h2k y).symm
    exact DFunLike.congr_fun key x
  · rw [Ideal.eq_top_iff_one]
    have h1 : (1 : Ring R₀ S₀ k) =
        ∑ t, ringMap R₀ S₀ h2k (α' t) * stageMap R₀ ψ h2k (ringMap R₀ T₀ h2k (γ' t)) := by
      have := congrArg (ringMap R₀ S₀ h3k) hi₃
      simp only [map_one, ringMap_ringMap, map_sum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun t _ ↦ ?_
      rw [map_mul, ← stageMap_ringMap R₀ ψ le_rfl h2k]
    rw [h1]
    exact Ideal.sum_mem _ fun t _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, ⟨t, rfl⟩, rfl⟩)
  · rintro _ ⟨t, rfl⟩
    exact hbij t k (hik t)

/-- The general case, for an algebra `B` identified with
`A[x_1, …, x_n, 1/h]/(f_1, …, f_n)`. -/
theorem exists_linearEquiv_traceCandidate_of_algEquiv (A : Type u) [CommRing A] (n : ℕ)
    (h : MvPolynomial (Fin n) A) (f : Fin n → MvPolynomial (Fin n) A) {B : Type u} [CommRing B]
    [Algebra A B] (eB : localizedCompleteIntersection A n h f ≃ₐ[A] B) [Module.Flat A B]
    (F : FiniteOpenFactorization.{u, u, w} A B) [Module.FinitePresentation A F.middle] :
    ∃ ε : B ≃ₗ[B] dualizingModule F,
      ε (eB (jacobianDet n h f)) = dualizingModule.traceCandidate F := by
  obtain ⟨R₀, _, h₀, f₀, _, _, _, T₀, _, _, _, _, _, _, _, hdet⟩ :=
    exists_subring_models A n h f eB F.middle
  have := finitePresentation_localizedCompleteIntersection R₀ n h₀ f₀
  obtain ⟨i, F₀, r, hr⟩ := exists_stage_finiteOpenFactorization R₀ T₀
    (localizedCompleteIntersection R₀ n h₀ f₀) F
  have : IsNoetherianRing (Base R₀ i) := Algebra.FiniteType.isNoetherianRing ℤ _
  have : IsScalarTower R₀ (Base R₀ i) (Ring R₀ (localizedCompleteIntersection R₀ n h₀ f₀) i) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R₀ (localizedCompleteIntersection R₀ n h₀ f₀)
      (Ring R₀ (localizedCompleteIntersection R₀ n h₀ f₀) i) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap R₀ (Base R₀ i) r ⊗ₜ (1 : localizedCompleteIntersection R₀ n h₀ f₀) =
        (1 : Base R₀ i) ⊗ₜ algebraMap R₀ (localizedCompleteIntersection R₀ n h₀ f₀) r
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have := flat_of_isPushout_localizedCompleteIntersection (R := R₀) (n := n) (h := h₀) (f := f₀)
    (A₀ := Base R₀ i) (B₀ := Ring R₀ (localizedCompleteIntersection R₀ n h₀ f₀) i) F₀
  have : Module.FinitePresentation (Base R₀ i) F₀.middle :=
    Module.finitePresentation_of_finite _ _
  obtain ⟨ε₀, hε₀⟩ := exists_linearEquiv_traceCandidate_of_isPushout (R := R₀) (n := n) (h := h₀)
    (f := f₀) (A₀ := Base R₀ i) (B₀ := Ring R₀ (localizedCompleteIntersection R₀ n h₀ f₀) i) F₀
  have := ringToRing_isPushout R₀ (localizedCompleteIntersection R₀ n h₀ f₀) (S := B) i
  obtain ⟨ε, hε⟩ := dualizingModule.exists_linearEquiv_traceCandidate_of_baseChange F₀ _ ε₀ hε₀
    (Algebra.IsPushout.equiv (Base R₀ i) A _ B) F r hr
  refine ⟨ε, ?_⟩
  rw [← hε, Algebra.IsPushout.equiv_tmul, map_one, one_mul, ← hdet,
    IsScalarTower.algebraMap_apply (localizedCompleteIntersection R₀ n h₀ f₀)
      (Ring R₀ (localizedCompleteIntersection R₀ n h₀ f₀) i) B]


/-- **Stacks Project, Tag 0BWH.** Let `A` be a ring, let `h, f_1, …, f_n` be polynomials in `n`
variables over `A` and set `B = A[x_1, …, x_n, 1/h]/(f_1, …, f_n)`, assumed quasi-finite over `A`.
Then there is an isomorphism `B → ω_{B/A}` mapping `det(∂f_i/∂x_j)` to `τ_{B/A}`.

The three parts of the statement are:

* over a Noetherian ring `A`, for every finite-open factorization `F` of `A → B` (so for the
  dualizing module `ω_{B/A} = Hom_A(B', A) ⊗_{B'} B` of Tag 0BSZ, which does not depend on `F`),
  an isomorphism `B ≅ ω_{B/A}` carrying the Jacobian determinant to the trace element
  `τ_{B/A}` of Definition 0BT6;
* over an arbitrary ring `A`, a finite-open factorization `A → B' → B` with `B'` a finitely
  presented `A`-module exists;
* over an arbitrary ring `A`, for every such factorization, an isomorphism
  `B ≅ Hom_A(B', A) ⊗_{B'} B` carrying the Jacobian determinant to the canonical element
  `Stacks.Discriminant.dualizingModule.traceCandidate` (the element of the proof of Tag 0BTB,
  which is the trace element when `A` is Noetherian).

The source defines `ω_{B/A}` and `τ_{B/A}` only for Noetherian rings: Section 0BUK opens with
"Let `A → B` be a quasi-finite homomorphism of Noetherian rings ... We set
`ω_{B/A} = Hom_A(B', A) ⊗_{B'} B`", and Definition 0BT6 reads "Let `A → B` be a flat quasi-finite
map of Noetherian rings. The trace element is the unique element `τ_{B/A} ∈ ω_{B/A}` with the
following property: for any Noetherian `A`-algebra `A_1` ...". The first part is the statement at
those definitions. The last two parts extend it to an arbitrary ring, with `ω_{B/A}` computed from
a factorization whose intermediate algebra is finitely presented, the class of factorizations that
base change correctly, and `τ_{B/A}` the canonical element. Finite presentation of the
intermediate algebra cannot be dropped over a non-Noetherian ring: for
`A = k[t, a_1, a_2, …]/(t^i a_i, a_i a_j)` and `I = (a_1, a_2, …)`, the algebra
`B = A[x]/(tx - 1) = A_t` is quasi-finite, and `A → A/I → A_t` is a finite-open factorization
(`A/I = k[t]` and `A_t = k[t, 1/t]`), but `Hom_A(A/I, A) ⊗_{A/I} A_t = (Ann_A I)_t = I_t = 0`.

The proof of the last part writes `A` as the union of its subrings of finite type over `ℤ`,
descends `B`, the factorization and its local isomorphisms to such a subring `A₀`, which is
Noetherian, applies the first part there, and base changes back to `A` (Tag 0BVF). The source
assumes `n ≥ 1`; the statement also holds for `n = 0`. -/
@[stacks 0BWH "the isomorphism of B with its dualizing module carrying the Jacobian determinant
to the trace element, at the source's definitions over a Noetherian ring and for factorizations
with finitely presented intermediate algebra over an arbitrary ring"]
theorem exists_linearEquiv_dualizingModule_jacobianDet (A : Type u) [CommRing A] (n : ℕ)
    (h : MvPolynomial (Fin n) A) (f : Fin n → MvPolynomial (Fin n) A)
    [Algebra.QuasiFinite A (localizedCompleteIntersection A n h f)] :
    letI : Module.Flat A (localizedCompleteIntersection A n h f) :=
      flat_localizedCompleteIntersection A n h f
    (∀ [IsNoetherianRing A]
        (F : FiniteOpenFactorization.{u, u, w} A (localizedCompleteIntersection A n h f)),
        ∃ ε : localizedCompleteIntersection A n h f ≃ₗ[localizedCompleteIntersection A n h f]
            dualizingModule F,
          ε (Matrix.det fun i j : Fin n ↦ algebraMap (MvPolynomial (Fin n) A)
              (localizedCompleteIntersection A n h f) (MvPolynomial.pderiv j (f i))) =
            dualizingModule.traceElement F) ∧
      (∃ F : FiniteOpenFactorization.{u, u, u} A (localizedCompleteIntersection A n h f),
        Module.FinitePresentation A F.middle) ∧
      ∀ (F : FiniteOpenFactorization.{u, u, w} A (localizedCompleteIntersection A n h f))
        [Module.FinitePresentation A F.middle],
        ∃ ε : localizedCompleteIntersection A n h f ≃ₗ[localizedCompleteIntersection A n h f]
            dualizingModule F,
          ε (Matrix.det fun i j : Fin n ↦ algebraMap (MvPolynomial (Fin n) A)
              (localizedCompleteIntersection A n h f) (MvPolynomial.pderiv j (f i))) =
            dualizingModule.traceCandidate F := by
  let : Module.Flat A (localizedCompleteIntersection A n h f) :=
    flat_localizedCompleteIntersection A n h f
  refine ⟨fun F ↦ exists_linearEquiv_dualizingModule_map_det_eq_traceElement A n h f F, ?_,
    fun F _ ↦ exists_linearEquiv_traceCandidate_of_algEquiv A n h f AlgEquiv.refl F⟩
  have := finitePresentation_localizedCompleteIntersection A n h f
  exact exists_finiteOpenFactorization_finitePresentation

end Main

end Stacks.Discriminant
