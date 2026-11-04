module

public import StacksFrontier.RingTheory.Rig.NaiveCotangent.SmulIdBaseChange

/-!
# A scalar acting by zero, read on the two modules of a presentation

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `B` an `I`-adically complete `A`-algebra of
finite type modulo `I`, presented as `B = A[x₁, …, xᵣ]^∧ / J`.  By
`Rig.exists_factorization_of_smul_id_eq_zero` and `Rig.smul_id_eq_zero_of_factorization` the
condition `f • 𝟙 NL^∧_{B/A} = 0` in `D(B)` is the existence of a null-homotopy of `f • 𝟙` on the
two-term cochain complex of the presentation.  Those two statements are phrased with the
morphisms of `CochainComplex (ModuleCat B) ℤ`, whose terms are the *universe lifts* of the
conormal module `J / J²` and of the free module `⨁ i, B dxᵢ`.

This file restates both halves with an honest `B`-linear map

`σ : (Fin r → B) →ₗ[B] J / J²`,

satisfying `σ ∘ d = f • id` and `d ∘ σ = f • id` for the differential
`d : J / J² → (Fin r → B)` of `Rig.CompletedNaiveCotangentComplex`.  That is the form in which
the condition can be *transported*: a construction applied to the two modules of a presentation
produces module maps, not morphisms of lifted cochain complexes, and the universe lifts and the
term isomorphisms `Rig.CompletedNaiveCotangentComplex.degreeZeroIso`,
`Rig.CompletedNaiveCotangentComplex.degreeNegOneIso` only get in the way.

## Main definitions

* `Rig.liftedSection` — the universe lift of a `B`-linear map `(Fin r → B) → J / J²`.

## Main results

* `Rig.smul_id_eq_zero_of_differential_section` — a module-level null-homotopy makes `f` act by
  zero on `NL^∧_{B/A}` in `D(B)`.
* `Rig.exists_differential_section_of_smul_id_eq_zero` — conversely, `f` acting by zero produces
  such a module-level null-homotopy.

## References

* [Stacks Project, Tag 0AK2](https://stacks.math.columbia.edu/tag/0AK2)
* [Stacks Project, Tag 0ALN](https://stacks.math.columbia.edu/tag/0ALN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Rig

universe u v

open AdicFiniteTypeAlgebra CompletedNaiveCotangentComplex

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {I : Ideal A}
  (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B)

/-- The universe lift of a `B`-linear map `⨁ i, B dxᵢ → J / J²`, as a map between the terms of
`Rig.CompletedNaiveCotangentComplex.cochainComplex`. -/
public def liftedSection
    (σ : (Fin P.variableCount → B.carrier) →ₗ[B.carrier] P.extension.Cotangent) :
    LiftedDifferentials (P := P) →ₗ[B.carrier] LiftedCotangent (P := P) :=
  ULift.moduleEquiv.symm.toLinearMap.comp (σ.comp ULift.moduleEquiv.toLinearMap)

/-- The lifted section is `σ` on the underlying elements. -/
@[simp] public theorem liftedSection_apply
    (σ : (Fin P.variableCount → B.carrier) →ₗ[B.carrier] P.extension.Cotangent)
    (w : LiftedDifferentials (P := P)) :
    (liftedSection B P σ w).down = σ w.down := rfl

/-- The lifted differential is the differential on the underlying elements. -/
@[simp] public theorem liftedDifferential_down (K : CompletedNaiveCotangentComplex P)
    (z : LiftedCotangent (P := P)) :
    (K.liftedDifferential z).down = K.differential z.down := rfl

/-- Conjugating a relation `a ≫ b = f • 𝟙` by isomorphisms gives `f • 𝟙` on the other object. -/
private theorem iso_comp_comp_comp_eq_smul_id {R : Type*} [Semiring R] {C : Type*} [Category C]
    [Preadditive C] [Linear R C] {X Y X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y') (a : X' ⟶ Y')
    (b : Y' ⟶ X') (f : R) (h : a ≫ b = f • 𝟙 X') :
    (e.hom ≫ a ≫ e'.inv) ≫ e'.hom ≫ b ≫ e.inv = f • 𝟙 X := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc a, h]
  simp

/-- Transport of `(e.hom ≫ a ≫ e'.inv) ≫ s = f • 𝟙` to `a ≫ (e'.inv ≫ s ≫ e.hom) = f • 𝟙`. -/
private theorem comp_inv_comp_comp_hom_eq_smul_id {R : Type*} [Semiring R] {C : Type*}
    [Category C] [Preadditive C] [Linear R C] {X Y X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y')
    (a : X' ⟶ Y') (s : Y ⟶ X) (f : R) (h : (e.hom ≫ a ≫ e'.inv) ≫ s = f • 𝟙 X) :
    a ≫ e'.inv ≫ s ≫ e.hom = f • 𝟙 X' := by
  calc a ≫ e'.inv ≫ s ≫ e.hom = e.inv ≫ ((e.hom ≫ a ≫ e'.inv) ≫ s) ≫ e.hom := by simp
    _ = f • 𝟙 X' := by rw [h]; simp

/-- Transport of `s ≫ (e.hom ≫ a ≫ e'.inv) = f • 𝟙` to `(e'.inv ≫ s ≫ e.hom) ≫ a = f • 𝟙`. -/
private theorem inv_comp_comp_hom_comp_eq_smul_id {R : Type*} [Semiring R] {C : Type*}
    [Category C] [Preadditive C] [Linear R C] {X Y X' Y' : C} (e : X ≅ X') (e' : Y ≅ Y')
    (a : X' ⟶ Y') (s : Y ⟶ X) (f : R) (h : s ≫ e.hom ≫ a ≫ e'.inv = f • 𝟙 Y) :
    (e'.inv ≫ s ≫ e.hom) ≫ a = f • 𝟙 Y' := by
  calc (e'.inv ≫ s ≫ e.hom) ≫ a = e'.inv ≫ (s ≫ e.hom ≫ a ≫ e'.inv) ≫ e'.hom := by simp
    _ = f • 𝟙 Y' := by rw [h]; simp

variable [IsNoetherianRing A]

/-- A `B`-linear map `σ : ⨁ i, B dxᵢ → J / J²` which realizes multiplication by `f` on both
terms of the presentation's complex — a null-homotopy of `f • 𝟙` — makes `f` act by zero on
`NL^∧_{B/A}` in `D(B)`.

This direction says nothing about the degree-zero term, so it applies to data transported from
another algebra; it is the module-level form of
`Rig.smul_id_eq_zero_of_factorization`. -/
public theorem smul_id_eq_zero_of_differential_section (f : B.carrier)
    (σ : (Fin P.variableCount → B.carrier) →ₗ[B.carrier] P.extension.Cotangent)
    (hneg : ∀ y : P.extension.Cotangent,
      σ ((completedNaiveCotangentComplex B P).differential y) = f • y)
    (hzero : ∀ w : Fin P.variableCount → B.carrier,
      (completedNaiveCotangentComplex B P).differential (σ w) = f • w) :
    f • 𝟙 (derivedCompletedNaiveCotangentComplex B P) = 0 := by
  set K := completedNaiveCotangentComplex B P with hKdef
  have hcompneg : ModuleCat.ofHom K.liftedDifferential ≫
      ModuleCat.ofHom (liftedSection B P σ) =
      f • 𝟙 (ModuleCat.of B.carrier (LiftedCotangent (P := P))) :=
    ModuleCat.hom_ext (LinearMap.ext fun y => congrArg ULift.up (hneg y.down))
  have hcompzero : ModuleCat.ofHom (liftedSection B P σ) ≫
      ModuleCat.ofHom K.liftedDifferential =
      f • 𝟙 (ModuleCat.of B.carrier (LiftedDifferentials (P := P))) :=
    ModuleCat.hom_ext (LinearMap.ext fun w => congrArg ULift.up (hzero w.down))
  refine smul_id_eq_zero_of_factorization B P f
    (K.degreeZeroIso.hom ≫ ModuleCat.ofHom (liftedSection B P σ) ≫
      K.degreeNegOneIso.inv) ?_ ?_
  · rw [K.cochainComplex_d]
    exact iso_comp_comp_comp_eq_smul_id K.degreeNegOneIso K.degreeZeroIso _ _ f hcompneg
  · rw [K.cochainComplex_d]
    exact iso_comp_comp_comp_eq_smul_id K.degreeZeroIso K.degreeNegOneIso _ _ f hcompzero

/-- If `f` acts by zero on `NL^∧_{B/A}` in `D(B)`, then multiplication by `f` on both terms of
the presentation's complex is realized by a single `B`-linear map `σ : ⨁ i, B dxᵢ → J / J²`.

The degree-zero term is free, so this is the forcing direction; it is the module-level form of
`Rig.exists_factorization_of_smul_id_eq_zero`. -/
public theorem exists_differential_section_of_smul_id_eq_zero (f : B.carrier)
    (h : f • 𝟙 (derivedCompletedNaiveCotangentComplex B P) = 0) :
    ∃ σ : (Fin P.variableCount → B.carrier) →ₗ[B.carrier] P.extension.Cotangent,
      (∀ y : P.extension.Cotangent,
        σ ((completedNaiveCotangentComplex B P).differential y) = f • y) ∧
      (∀ w : Fin P.variableCount → B.carrier,
        (completedNaiveCotangentComplex B P).differential (σ w) = f • w) := by
  set K := completedNaiveCotangentComplex B P with hKdef
  obtain ⟨s, hneg, hzero⟩ := exists_factorization_of_smul_id_eq_zero B P f h
  rw [K.cochainComplex_d] at hneg hzero
  obtain ⟨t, keyneg, keyzero⟩ : ∃ t : ModuleCat.of B.carrier (LiftedDifferentials (P := P)) ⟶
      ModuleCat.of B.carrier (LiftedCotangent (P := P)),
      ModuleCat.ofHom K.liftedDifferential ≫ t =
        f • 𝟙 (ModuleCat.of B.carrier (LiftedCotangent (P := P))) ∧
      t ≫ ModuleCat.ofHom K.liftedDifferential =
        f • 𝟙 (ModuleCat.of B.carrier (LiftedDifferentials (P := P))) :=
    ⟨_, comp_inv_comp_comp_hom_eq_smul_id K.degreeNegOneIso K.degreeZeroIso _ s f hneg,
      inv_comp_comp_hom_comp_eq_smul_id K.degreeNegOneIso K.degreeZeroIso _ s f hzero⟩
  refine ⟨ULift.moduleEquiv.toLinearMap.comp
    (t.hom.comp ULift.moduleEquiv.symm.toLinearMap), fun y => ?_, fun w => ?_⟩
  · simpa using congrArg ULift.down (ConcreteCategory.congr_hom keyneg (ULift.up y))
  · simpa using congrArg ULift.down (ConcreteCategory.congr_hom keyzero (ULift.up w))

end Rig

end
