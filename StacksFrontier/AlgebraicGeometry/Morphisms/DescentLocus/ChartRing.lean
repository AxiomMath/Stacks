module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint

/-!
# The closed subscheme of a basic open cut out by an ideal

For a ring `A`, an element `g` and an ideal `I`, the ring `(A ⧸ I)_g` represents the ring maps
out of `A` which invert `g` and kill `I`; its spectrum is an immersion into `Spec A`, closed in
the basic open `D(g)`, and of finite presentation when `I` is finitely generated.

## Main definitions

* `AlgebraicGeometry.DescentLocus.chartRing`: the ring `(A ⧸ I)_g`.
* `AlgebraicGeometry.DescentLocus.chartRingHom`: the structure map `A →+* (A ⧸ I)_g`.
* `AlgebraicGeometry.DescentLocus.chartRingLift`: the factorization of a ring map inverting `g`
  and killing `I`.

## Main results

* `AlgebraicGeometry.DescentLocus.isImmersion_chartRingHom`: `Spec (A ⧸ I)_g ⟶ Spec A` is an
  immersion.
* `AlgebraicGeometry.DescentLocus.finitePresentation_chartRingHom`: it is of finite presentation
  when `I` is finitely generated.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.DescentLocus

variable {A : Type u} [CommRing A] (g : A) (I : Ideal A)

/-- The ring `(A ⧸ I)_g`. -/
abbrev chartRing : Type u := Localization.Away (Ideal.Quotient.mk I g)

/-- The structure map `A →+* (A ⧸ I)_g`. -/
def chartRingHom : A →+* chartRing g I :=
  (algebraMap (A ⧸ I) (chartRing g I)).comp (Ideal.Quotient.mk I)

theorem isUnit_chartRingHom : IsUnit (chartRingHom g I g) :=
  IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk I g)

theorem chartRingHom_eq_zero {a : A} (ha : a ∈ I) : chartRingHom g I a = 0 := by
  simp [chartRingHom, Ideal.Quotient.eq_zero_iff_mem.2 ha]

variable {g I} in
/-- A ring map inverting `g` and killing `I` factors through `(A ⧸ I)_g`. -/
def chartRingLift {B : Type u} [CommRing B] (ψ : A →+* B) (hg : IsUnit (ψ g))
    (hI : ∀ a ∈ I, ψ a = 0) : chartRing g I →+* B :=
  IsLocalization.Away.lift (Ideal.Quotient.mk I g)
    (g := Ideal.Quotient.lift I ψ hI) (by simpa using hg)

variable {g I} in
@[simp]
theorem chartRingLift_comp {B : Type u} [CommRing B] (ψ : A →+* B) (hg : IsUnit (ψ g))
    (hI : ∀ a ∈ I, ψ a = 0) : (chartRingLift ψ hg hI).comp (chartRingHom g I) = ψ := by
  ext a
  simp [chartRingLift, chartRingHom, IsLocalization.Away.lift]

/-- The spectrum of the structure map. -/
abbrev chartSpecMap : Spec (.of (chartRing g I)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (chartRingHom g I))

theorem chartSpecMap_eq : chartSpecMap g I =
    Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ I) (chartRing g I))) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  rw [← Spec.map_comp]
  rfl

instance isImmersion_chartSpecMap : IsImmersion (chartSpecMap g I) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  rw [chartSpecMap_eq]
  infer_instance

theorem finitePresentation_chartSpecMap (hI : I.FG) : FinitePresentation (chartSpecMap g I) := by
  refine ⟨?_, inferInstance, inferInstance⟩
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  have h₁ : (Ideal.Quotient.mk I).FinitePresentation :=
    RingHom.FinitePresentation.of_surjective _ Ideal.Quotient.mk_surjective (by simpa using hI)
  have h₂ : (algebraMap (A ⧸ I) (chartRing g I)).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.2
      (IsLocalization.Away.finitePresentation (Ideal.Quotient.mk I g))
  exact h₂.comp h₁

end AlgebraicGeometry.DescentLocus
