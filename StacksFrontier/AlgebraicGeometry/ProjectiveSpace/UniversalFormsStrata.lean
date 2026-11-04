module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.UniversalForms
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatStratificationFieldPoints
public import StacksFrontier.RingTheory.ULiftRingModules
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# The flat strata of the universal family of projective schemes cut out by forms

The universal family `Proj (R[T₀, …, Tₙ] ⧸ (f_1, …, f_M)) ⟶ Spec R` of
`StacksFrontier/AlgebraicGeometry/ProjectiveSpace/UniversalForms.lean`, over the coefficient ring
`R = ℤ[a_{j,E}]`, is proper, and `R` is Noetherian. So the Noetherian case of Stacks 0H3Z applies
to it: finitely many Noetherian strata of `Spec R` carry flat base changes of the universal
family, and every point of `Spec R` with values in a field lies on one of them. Combined with the
computation of the fibres, every projective scheme over a field `K` cut out by `M` forms of
degree `m` is the fibre at a `K`-valued point of one of finitely many flat proper families over
Noetherian bases. This is the parameter space of the proof of Stacks 0DPA, for quotients of `𝒪`.

## Main results

* `Stacks.UniversalForms.isProper_univToBase`: the universal family is proper.
* `Stacks.UniversalForms.exists_flat_families_of_forms`: finitely many flat proper families over
  Noetherian bases, the base changes of the universal family to its flat strata, such that every
  projective scheme over a field cut out by `M` forms of degree `m` is a fibre of one of them.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
* [Stacks Project, Tag 0H3Z](https://stacks.math.columbia.edu/tag/0H3Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

namespace Stacks.UniversalForms

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n M m : ℕ)

/-- The coefficient ring of the universal family is Noetherian. -/
instance : IsNoetherianRing (CoeffRing.{u} n M m) :=
  haveI := Stacks.ULiftTransport.isNoetherianRing_ulift (R := ℤ)
  inferInstance

/-- The universal quotient is of finite type over the coefficient ring. -/
instance : Algebra.FiniteType (CoeffRing.{u} n M m) (UnivQuot.{u} n M m) :=
  Algebra.FiniteType.trans (S := MvPolynomial (Fin (n + 1)) (CoeffRing.{u} n M m))
    inferInstance inferInstance

/-- The universal quotient is of finite type over its degree-zero part. -/
instance : Algebra.FiniteType ↥(univGrading.{u} n M m 0) (UnivQuot.{u} n M m) :=
  Algebra.FiniteType.of_restrictScalars_finiteType (CoeffRing.{u} n M m) _ _

/-- The degree-zero part of the universal quotient is the image of the coefficient ring. -/
theorem surjective_algebraMap_univGrading_zero :
    Function.Surjective (algebraMap (CoeffRing.{u} n M m) ↥(univGrading.{u} n M m 0)) := by
  rintro ⟨x, hx⟩
  obtain ⟨a, ha, rfl⟩ := (Stacks.RingTheory.HomogeneousQuotient.mem_quotientGrading_iff
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (CoeffRing.{u} n M m))
    (ideal.{u} n M m)).1 hx
  have ha' : a.IsHomogeneous 0 := (MvPolynomial.mem_homogeneousSubmodule _ _).1 ha
  have hC : a = MvPolynomial.C (a.coeff 0) := by
    refine MvPolynomial.ext _ _ fun d => ?_
    rw [MvPolynomial.coeff_C]
    split_ifs with hd
    · rw [hd]
    · by_contra h
      apply hd
      have h1 := ha' h
      have h2 : d.degree = 0 := by rw [Finsupp.degree_eq_weight_one]; exact h1
      exact ((Finsupp.degree_eq_zero_iff d).mp h2).symm
  refine ⟨a.coeff 0, Subtype.ext ?_⟩
  show Ideal.Quotient.mk _ (algebraMap _ _ (a.coeff 0)) = Ideal.Quotient.mk _ a
  conv_rhs => rw [hC]
  rfl

/-- **The universal family is proper.** -/
instance isProper_univToBase : IsProper (univToBase.{u} n M m) := by
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (CoeffRing.{u} n M m) ↥(univGrading.{u} n M m 0)))) :=
    IsClosedImmersion.spec_of_surjective _ (surjective_algebraMap_univGrading_zero n M m)
  infer_instance

variable {n M m} in
/-- The grading of the quotient `K[T₀, …, Tₙ] ⧸ (s_1, …, s_M)` by prescribed forms. -/
abbrev formsGrading (K : Type u) [CommRing K] (s : Fin M → MvPolynomial (Fin (n + 1)) K)
    (hs : ∀ j, (s j).IsHomogeneous m) :
    ℕ → Submodule K (MvPolynomial (Fin (n + 1)) K ⧸ (formsIdeal K s hs).toIdeal) :=
  Stacks.RingTheory.HomogeneousQuotient.quotientGrading
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (formsIdeal K s hs)

variable {n M m} in
/-- The structure morphism `Proj (K[T₀, …, Tₙ] ⧸ (s_1, …, s_M)) ⟶ Spec K`. -/
abbrev formsToSpec (K : Type u) [CommRing K] (s : Fin M → MvPolynomial (Fin (n + 1)) K)
    (hs : ∀ j, (s j).IsHomogeneous m) : Proj (formsGrading K s hs) ⟶ Spec (.of K) :=
  Proj.toSpecZero (formsGrading K s hs) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K ↥(formsGrading K s hs 0)))

/-- **Finitely many flat proper families over Noetherian bases contain every projective scheme
cut out by `M` forms of degree `m` over a field.** There are finitely many flat proper morphisms
`πᵢ : Zᵢ ⟶ Tᵢ` with `Tᵢ` Noetherian — the base changes of the universal family to the flat
strata of its base — such that for every field `K` and every `M` forms `s_j` of degree `m` over
`K`, the scheme `Proj (K[T₀, …, Tₙ] ⧸ (s_1, …, s_M))` over `Spec K` is the fibre of one of the
`πᵢ` at a `K`-valued point. -/
theorem exists_flat_families_of_forms :
    ∃ (t : ℕ) (T : Fin t → Scheme.{u}) (Z : Fin t → Scheme.{u}) (π : ∀ i, Z i ⟶ T i),
      (∀ i, IsNoetherian (T i)) ∧ (∀ i, Flat (π i)) ∧ (∀ i, IsProper (π i)) ∧
      ∀ (K : Type u) [Field K] (s : Fin M → MvPolynomial (Fin (n + 1)) K)
        (hs : ∀ j, (s j).IsHomogeneous m),
        ∃ i, ∃ (x : Spec (.of K) ⟶ T i) (q : Proj (formsGrading K s hs) ⟶ Z i),
          IsPullback q (formsToSpec K s hs) (π i) x := by
  obtain ⟨t, T, j, -, hT, hflat, hpts⟩ := exists_flat_strata_of_isNoetherian (univToBase.{u} n M m)
  refine ⟨t, T, fun i => pullback (univToBase.{u} n M m) (j i),
    fun i => pullback.snd (univToBase.{u} n M m) (j i), hT, hflat, fun i => inferInstance, ?_⟩
  intro K _ s hs
  let : Algebra (CoeffRing.{u} n M m) K := (specialize K s).toAlgebra
  obtain ⟨i, x, hx⟩ := hpts K (Spec.map (CommRingCat.ofHom (specialize K s)))
  have hsq := isPullback_univToBase n M m K
  rw [← hx] at hsq
  have hbig := IsPullback.of_right (h₁₂ := pullback.fst (univToBase.{u} n M m) (j i))
    (v₁₂ := pullback.snd (univToBase.{u} n M m) (j i))
    (h₁₁ := pullback.lift (Proj.map (baseChangeGradedRingHom n M m K)
      (irrelevant_le_map_baseChangeGradedRingHom n M m K)) (baseToSpec n M m K ≫ x)
        (by rw [hsq.w]; simp only [Category.assoc]))
    (by rw [pullback.lift_fst]; exact hsq) (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback _ _)
  have key : ∀ (s₁ : Fin M → MvPolynomial (Fin (n + 1)) K) (h₁ : ∀ j, (s₁ j).IsHomogeneous m),
      s₁ = s → (∃ (q : Proj (formsGrading K s₁ h₁) ⟶ pullback (univToBase.{u} n M m) (j i)),
        IsPullback q (formsToSpec K s₁ h₁) (pullback.snd (univToBase.{u} n M m) (j i)) x) →
      ∃ (q : Proj (formsGrading K s hs) ⟶ pullback (univToBase.{u} n M m) (j i)),
        IsPullback q (formsToSpec K s hs) (pullback.snd (univToBase.{u} n M m) (j i)) x := by
    rintro s₁ h₁ rfl h
    exact h
  obtain ⟨q, hq⟩ := key (baseForms n M m K) (isHomogeneous_baseForms n M m K)
    (funext fun j => map_specialize_form K s hs j) ⟨_, hbig⟩
  exact ⟨i, x, q, hq⟩

end Stacks.UniversalForms
