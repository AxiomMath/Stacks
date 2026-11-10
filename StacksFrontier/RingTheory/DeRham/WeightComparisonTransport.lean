module

public import StacksFrontier.RingTheory.DeRham.WeightComparison
public import StacksFrontier.RingTheory.DeRham.PolynomialAlgEquivQuasiIso
public import StacksFrontier.RingTheory.DeRham.LaurentResidueTransport
import StacksCore.Tactic.StacksAttribute

/-!
# The weight comparisons transported along an isomorphism of algebras

The weight gradings of the forms of the polynomial algebra `A[X]` and of the Laurent polynomial
algebra `A[T;T⁻¹]`, and the comparison between them under restriction, transported to algebras
`B ≅ A[X]` and `B' ≅ A[T;T⁻¹]` over `A`.

## Main definitions

* `KaehlerDifferential.mapGrading`: the grading of an `A`-algebra `B` induced by a grading of `A`.
* `PolynomialDeRham.polyGrading`: the weight grading of an algebra identified with `A[X]`.

## Main results

* `KaehlerDifferential.map_gradedDifferentialFormComponent`: restriction of forms along `A → B`
  carries the graded components of Tag 0FU9 onto those of the induced grading.
* `PolynomialDeRham.exists_mapExteriorPower_eq_of_mem_zero` and
  `PolynomialDeRham.injective_mapExteriorPower_of_algEquiv`: over an algebra identified with
  `A[X]` the weight-zero forms are exactly, and injectively, the forms pulled back from `A`.
* `PolynomialDeRham.algebraMap_smul_mem_polyComponent`: the weight components are stable under
  multiplication by functions pulled back from `A`.
* `LaurentDeRham.transport_weightComparison`: for `n > 0`, restriction of forms along `B → B'`
  carries the weight-`n` component of `B` injectively onto the weight-`n` component of `B'`.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial LaurentPolynomial KaehlerDifferential

universe u

namespace KaehlerDifferential

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B]

/-- The grading of `B` induced by a grading of `A` along the structure map `A → B`. -/
def mapGrading {G : Type*} (gr : G → Submodule R A) (g : G) : Submodule R B :=
  (gr g).map (IsScalarTower.toAlgHom R A B).toLinearMap

/-- **The restriction of forms along `A → B` carries the graded components of `A` onto those of
the induced grading of `B`.** -/
theorem map_gradedDifferentialFormComponent {G : Type*} [AddCommMonoid G]
    (gr : G → Submodule R A) (p : ℕ) (g : G) :
    (gradedDifferentialFormComponent gr p g).map
        ((mapExteriorPower R A B p).restrictScalars R) =
      gradedDifferentialFormComponent (mapGrading (B := B) gr) p g := by
  rw [gradedDifferentialFormComponent, gradedDifferentialFormComponent, Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨deg, a, hg, rfl⟩, rfl⟩
    refine ⟨deg, fun i => ⟨algebraMap A B (a i), (a i : A), (a i).2, rfl⟩, hg, ?_⟩
    exact mapExteriorPower_smul_ιMulti_D R A B p fun i => (a i : A)
  · rintro ⟨deg, c, hg, rfl⟩
    choose a ha hac using fun i => (c i).2
    refine ⟨_, ⟨deg, fun i => ⟨a i, ha i⟩, hg, rfl⟩, ?_⟩
    refine (mapExteriorPower_smul_ιMulti_D R A B p fun i => a i).trans ?_
    have h : ∀ i, algebraMap A B (a i) = (c i : B) := hac
    simp only [h]

end KaehlerDifferential

namespace PolynomialDeRham

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra A B] [IsScalarTower R A B]

/-- The weight grading of an `A`-algebra `B` identified with `A[X]` by `e`. -/
def polyGrading (e : A[X] ≃ₐ[A] B) (k : ℕ) : Submodule R B :=
  (weightGrading R A k).map (e.toLinearMap.restrictScalars R)

variable {R A B}

/-- The `A[X]`-algebra structure on `B` given by an identification `A[X] ≃ B`. -/
abbrev algebraOfAlgEquiv (e : A[X] ≃ₐ[A] B) : Algebra A[X] B := e.toRingHom.toAlgebra

/-- With the `A[X]`-algebra structure `algebraOfAlgEquiv e` on `B`, the maps `A → A[X] → B` form a
scalar tower. -/
theorem isScalarTower_algebraOfAlgEquiv (e : A[X] ≃ₐ[A] B) :
    letI := algebraOfAlgEquiv e
    IsScalarTower A A[X] B :=
  let := algebraOfAlgEquiv e
  IsScalarTower.of_algebraMap_eq fun a ↦ (e.commutes a).symm

/-- With the `A[X]`-algebra structure `algebraOfAlgEquiv e` on `B`, the maps `R → A[X] → B` form a
scalar tower. -/
theorem isScalarTower_algebraOfAlgEquiv' (e : A[X] ≃ₐ[A] B) :
    letI := algebraOfAlgEquiv e
    IsScalarTower R A[X] B :=
  let := algebraOfAlgEquiv e
  IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R A B, IsScalarTower.algebraMap_apply R A A[X]]
    exact (e.commutes _).symm

/-- The weight grading `polyGrading R A B e` is the grading of `B` induced by the weight grading of
`A[X]` along `algebraOfAlgEquiv e`. -/
theorem polyGrading_eq_mapGrading (e : A[X] ≃ₐ[A] B) (k : ℕ) :
    letI := algebraOfAlgEquiv e
    haveI := isScalarTower_algebraOfAlgEquiv' (R := R) e
    polyGrading R A B e k = mapGrading (B := B) (weightGrading R A) k := by
  let := algebraOfAlgEquiv e
  have := isScalarTower_algebraOfAlgEquiv' (R := R) e
  rfl

/-- The restriction of forms along an algebra map which is a ring isomorphism is injective. -/
private theorem injective_mapExteriorPower_of_algebraMap_eq {A' : Type u} [CommRing A']
    [Algebra R A'] [Algebra A' B] [IsScalarTower R A' B] (e : A' ≃+* B)
    (he : algebraMap A' B = e.toRingHom) (p : ℕ) :
    Function.Injective (mapExteriorPower R A' B p) := by
  let e' : A' ≃ₐ[R] B :=
    { e with
      commutes' := fun r ↦ by
        change e.toRingHom _ = _
        rw [← he, ← IsScalarTower.algebraMap_apply] }
  have := isIso_deRhamComplexMap_of_algEquiv R e' he
  exact (ConcreteCategory.bijective_of_isIso ((deRhamComplexMap R A' B).f p)).1

/-- The restriction of forms along `A[X] ≃ B` is injective. -/
theorem injective_mapExteriorPower_algEquiv (e : A[X] ≃ₐ[A] B) (p : ℕ) :
    letI := algebraOfAlgEquiv e
    haveI := isScalarTower_algebraOfAlgEquiv' (R := R) e
    Function.Injective (mapExteriorPower R A[X] B p) := by
  let := algebraOfAlgEquiv e
  have := isScalarTower_algebraOfAlgEquiv' (R := R) e
  exact injective_mapExteriorPower_of_algebraMap_eq e.toRingEquiv rfl p

/-- **Over an algebra identified with `A[X]`, the weight-zero forms are pulled back from `A`.** -/
theorem exists_mapExteriorPower_eq_of_mem_zero (e : A[X] ≃ₐ[A] B) {p : ℕ}
    {x : ⋀[B]^p (Ω[B⁄R])}
    (hx : x ∈ gradedDifferentialFormComponent (polyGrading R A B e) p 0) :
    ∃ y : ⋀[A]^p (Ω[A⁄R]), mapExteriorPower R A B p y = x := by
  let := algebraOfAlgEquiv e
  have := isScalarTower_algebraOfAlgEquiv e
  have := isScalarTower_algebraOfAlgEquiv' (R := R) e
  have hg : polyGrading R A B e = mapGrading (B := B) (weightGrading R A) :=
    funext (polyGrading_eq_mapGrading e)
  rw [hg, ← map_gradedDifferentialFormComponent] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  change z ∈ weightComponent R A 0 p at hz
  rw [weightComponent_zero_eq_range] at hz
  obtain ⟨y, rfl⟩ := hz
  exact ⟨y, (mapExteriorPower_mapExteriorPower R A A[X] B p y).symm⟩

/-- **Over an algebra identified with `A[X]`, the pullback of forms from `A` is injective.** -/
theorem injective_mapExteriorPower_of_algEquiv (e : A[X] ≃ₐ[A] B) (p : ℕ) :
    Function.Injective (mapExteriorPower R A B p) := by
  let := algebraOfAlgEquiv e
  have := isScalarTower_algebraOfAlgEquiv e
  have := isScalarTower_algebraOfAlgEquiv' (R := R) e
  intro y₁ y₂ h
  rw [← mapExteriorPower_mapExteriorPower R A A[X] B p y₁,
    ← mapExteriorPower_mapExteriorPower R A A[X] B p y₂] at h
  exact injective_mapExteriorPower R A p (injective_mapExteriorPower_algEquiv e p h)

/-- **The weight components of an algebra identified with `A[X]` are stable under multiplication
by the functions pulled back from `A`.** -/
theorem algebraMap_smul_mem_polyComponent (e : A[X] ≃ₐ[A] B) {p n : ℕ} (c : A)
    {x : ⋀[B]^p (Ω[B⁄R])}
    (hx : x ∈ gradedDifferentialFormComponent (polyGrading R A B e) p n) :
    algebraMap A B c • x ∈ gradedDifferentialFormComponent (polyGrading R A B e) p n := by
  let := algebraOfAlgEquiv e
  have := isScalarTower_algebraOfAlgEquiv e
  have := isScalarTower_algebraOfAlgEquiv' (R := R) e
  have hg : polyGrading R A B e = mapGrading (B := B) (weightGrading R A) :=
    funext (polyGrading_eq_mapGrading e)
  rw [hg, ← map_gradedDifferentialFormComponent] at hx ⊢
  obtain ⟨z, hz, rfl⟩ := hx
  refine ⟨(C c : A[X]) • z, ?_, ?_⟩
  · change z ∈ weightComponent R A n p at hz
    change (C c : A[X]) • z ∈ weightComponent R A n p
    rw [weightComponent_eq_weightForms] at hz ⊢
    have h := monomial_smul_mem_weightForms R A 0 c hz
    rwa [zero_add, monomial_zero_left] at h
  · change mapExteriorPower R A[X] B p ((C c : A[X]) • z) = _
    rw [map_smul]
    have h : algebraMap A[X] B (Polynomial.C c) = algebraMap A B c := by
      rw [IsScalarTower.algebraMap_apply A A[X] B, Polynomial.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
    rw [← algebraMap_smul B (Polynomial.C c : A[X]), h, algebraMap_smul]
    rfl

end PolynomialDeRham

namespace LaurentDeRham

open PolynomialDeRham

variable {R A B B' : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing B'] [Algebra R A]
  [Algebra R B] [Algebra R B'] [Algebra A B] [Algebra A B'] [Algebra B B'] [IsScalarTower R A B]
  [IsScalarTower R A B'] [IsScalarTower R B B'] [IsScalarTower A B B']

omit [IsScalarTower A B B'] in
/-- **The weight comparison of clause (3) of Stacks 0FUH, transported**: if `B ≅ A[X]` and
`B' ≅ A[T;T⁻¹]` compatibly with a map `B → B'` over `A` and the inclusion `A[X] → A[T;T⁻¹]`, then
for `n > 0` the restriction of forms carries the weight-`n` component of `B` onto the weight-`n`
component of `B'`, injectively. -/
theorem transport_weightComparison (eB : A[X] ≃ₐ[A] B) (eB' : A[T;T⁻¹] ≃ₐ[A] B')
    (hsq : ∀ q : A[X], algebraMap B B' (eB q) = eB' (Polynomial.toLaurent q))
    (n p : ℕ) (hn : 0 < n) :
    (gradedDifferentialFormComponent (polyGrading R A B eB) p n).map
        ((mapExteriorPower R B B' p).restrictScalars R) =
      gradedDifferentialFormComponent (transportGrading (R := R) eB') p (n : ℤ) ∧
    ∀ x ∈ gradedDifferentialFormComponent (polyGrading R A B eB) p n,
      mapExteriorPower R B B' p x = 0 → x = 0 := by
  let : Algebra A[X] B := algebraOfAlgEquiv eB
  have : IsScalarTower A A[X] B := isScalarTower_algebraOfAlgEquiv eB
  have : IsScalarTower R A[X] B := isScalarTower_algebraOfAlgEquiv' (R := R) eB
  let : Algebra A[T;T⁻¹] B' := eB'.toRingHom.toAlgebra
  have : IsScalarTower A A[T;T⁻¹] B' :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (eB'.commutes a).symm
  have : IsScalarTower R A[T;T⁻¹] B' := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R A B', IsScalarTower.algebraMap_apply R A A[T;T⁻¹]]
    exact (eB'.commutes _).symm
  let : Algebra A[X] B' := ((algebraMap B B').comp eB.toRingHom).toAlgebra
  have : IsScalarTower A[X] B B' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A[X] A[T;T⁻¹] B' := IsScalarTower.of_algebraMap_eq fun q ↦ hsq q
  have : IsScalarTower R A[X] B' := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R B B', IsScalarTower.algebraMap_apply R A[X] B]
    rfl
  have hgB : polyGrading R A B eB = mapGrading (B := B) (PolynomialDeRham.weightGrading R A) :=
    funext (polyGrading_eq_mapGrading eB)
  have hgB' : transportGrading (R := R) eB' = @mapGrading R A[T;T⁻¹] B' _ _ _ _ _ _ _ _
      (LaurentDeRham.weightGrading R A) := rfl
  have hcomp : ∀ y : ⋀[A[X]]^p (Ω[A[X]⁄R]),
      mapExteriorPower R B B' p (mapExteriorPower R A[X] B p y) =
        mapExteriorPower R A[T;T⁻¹] B' p (mapExteriorPower R A[X] A[T;T⁻¹] p y) := fun y ↦ by
    rw [mapExteriorPower_mapExteriorPower R A[X] B B' p y,
      ← mapExteriorPower_mapExteriorPower R A[X] A[T;T⁻¹] B' p y]
  have hinjB' : Function.Injective (mapExteriorPower R A[T;T⁻¹] B' p) :=
    injective_mapExteriorPower_of_algebraMap_eq eB'.toRingEquiv rfl p
  rw [hgB, hgB', ← map_gradedDifferentialFormComponent, ← map_gradedDifferentialFormComponent]
  constructor
  · have h := map_weightComponent_eq_laurentWeightComponent R A n p hn
    change _ = Submodule.map _ (LaurentDeRham.weightComponent R A (n : ℤ) p)
    rw [← h, ← Submodule.map_comp, ← Submodule.map_comp]
    congr 1
    exact LinearMap.ext fun y ↦ hcomp y
  · rintro _ ⟨y, hy, rfl⟩ h0
    change mapExteriorPower R B B' p (mapExteriorPower R A[X] B p y) = 0 at h0
    rw [hcomp] at h0
    have h1 := hinjB' (h0.trans (map_zero _).symm)
    change mapExteriorPower R A[X] B p y = 0
    rw [eq_zero_of_mem_weightComponent_of_mapExteriorPower_eq_zero R A n p hy h1, map_zero]

end LaurentDeRham

end
