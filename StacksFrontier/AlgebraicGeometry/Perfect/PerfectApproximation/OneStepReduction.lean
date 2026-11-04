module

public import StacksFrontier.Homology.DerivedCategory.PerfectApproximation
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportedCohomology
public import StacksFrontier.Topology.Sheaves.Modules.StalkExactness
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SheafLevel
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Topology.Constructible

/-!
# Approximation by perfect complexes from a one-step construction

For a scheme `X`, a closed subset `T`, an object `E` of the derived category of `𝒪_X`-modules and
an integer `m`, *approximation holds for the triple* `(T, E, m)` when a perfect object supported
on `T` maps to `E`, inducing isomorphisms on cohomology above `m` and a surjection in degree `m`.
This file shows that approximation holds for every object of a class of objects with cohomology
bounded above, as soon as the class is stable under cones of admissible maps and admits a
one-step approximation in each degree.

## Main definitions

* `AlgebraicGeometry.PerfectApproximation.ApproximationHolds`: the condition on a triple
  `(T, E, m)`.
* `AlgebraicGeometry.PerfectApproximation.ApproximationByPerfectComplexes`: approximation holds,
  for some `r`, for every triple `(T, E, m)` with `T` closed with retrocompact complement and `E`
  `(m - r)`-pseudo-coherent with quasi-coherent cohomology supported on `T` from degree `m - r`.
* `AlgebraicGeometry.PerfectApproximation.IsAdmissible`: the perfect objects cohomologically
  supported on `T`.

## Main results

* `AlgebraicGeometry.PerfectApproximation.isAdmissible_obj₂_of_distinguished`: the admissible
  objects are stable in the middle of a distinguished triangle.
* `AlgebraicGeometry.PerfectApproximation.approximationHolds_of_oneStep`: approximation holds for
  every object of a class `Q` with cohomology bounded above, provided `Q` is stable under passing
  to the cone of an admissible map and every object of `Q` whose cohomology vanishes above
  `t ≥ m` receives a degree-`t` surjection from an admissible object with the same vanishing.

## References

* [Stacks Project, Tag 08EQ](https://stacks.math.columbia.edu/tag/08EQ)
* [Stacks Project, Tag 08EM](https://stacks.math.columbia.edu/tag/08EM)
* [Stacks Project, Tag 08EN](https://stacks.math.columbia.edu/tag/08EN)
* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace

namespace AlgebraicGeometry.PerfectApproximation

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : Scheme.{u})

/-- Approximation holds for `(T, E, m)`: some perfect object `P` with cohomology supported on `T`
admits a map `P ⟶ E` inducing isomorphisms on cohomology above `m` and a surjection in degree
`m`. -/
def ApproximationHolds (T : Set X) (E : DerivedCategory.{u + 1} X.Modules) (m : ℤ) : Prop :=
  ∃ P : DerivedCategory.{u + 1} X.Modules,
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) P ∧
      CohomologySupportedOn X.ringCatSheaf T P ∧
        ∃ α : P ⟶ E, DerivedCategory.ApproximatesFrom α m

/-- Approximation by perfect complexes holds on `X`: for every closed `T ⊆ X` with retrocompact
complement there is an integer `r` such that approximation holds for `(T, E, m)` whenever `E` has
quasi-coherent cohomology, is `(m - r)`-pseudo-coherent, and has cohomology in degrees at least
`m - r` vanishing at every point outside `T`. -/
def ApproximationByPerfectComplexes : Prop :=
  ∀ T : Set X, IsClosed T → IsRetrocompact Tᶜ → ∃ r : ℤ,
    ∀ (E : DerivedCategory.{u + 1} X.Modules) (m : ℤ),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent) →
      RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace) E (m - r) →
      (∀ (i : ℤ) (x : X), m - r ≤ i → x ∉ T →
        IsZero (TopCat.Presheaf.stalk (X := X)
          (((DerivedCategory.homologyFunctor X.Modules i).obj E).val.presheaf) x)) →
      ApproximationHolds X T E m

/-- The objects that may serve as approximations for the closed subset `T`: the perfect
objects whose cohomology is supported on `T`. -/
def IsAdmissible (T : Set X) (P : DerivedCategory.{u + 1} X.Modules) : Prop :=
  Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) P ∧ CohomologySupportedOn
    X.ringCatSheaf T P

/-- If the outer objects of a distinguished triangle are perfect with cohomology supported on
`T`, so is the middle one. -/
theorem isAdmissible_obj₂_of_distinguished (T : Set X)
    (S : Triangle (DerivedCategory.{u + 1} X.Modules))
    (hS : S ∈ distTriang (DerivedCategory.{u + 1} X.Modules))
    (h₁ : IsAdmissible X T S.obj₁) (h₃ : IsAdmissible X T S.obj₃) :
    IsAdmissible X T S.obj₂ :=
  ⟨Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₂_of_distinguished S hS h₁.1 h₃.1,
    cohomologySupportedOn_obj₂_of_distinguished X.ringCatSheaf T S hS h₁.2 h₃.2⟩

/-- Let `Q` be a class of objects of the derived category of `𝒪_X`-modules such that

* `Q` passes to the cone of a map from an admissible object (`hcone`);
* every `E` in `Q` whose cohomology vanishes above some `t ≥ m` receives a map from an
  admissible object with the same vanishing, surjective on `H^t` (`hstep`).

Then approximation holds for `(T, E, m)` for every `E` in `Q` whose cohomology vanishes above
some degree. -/
theorem approximationHolds_of_oneStep (T : Set X) (m : ℤ)
    (Q : DerivedCategory.{u + 1} X.Modules → Prop)
    (hcone : ∀ S : Triangle (DerivedCategory.{u + 1} X.Modules),
      S ∈ distTriang (DerivedCategory.{u + 1} X.Modules) →
      IsAdmissible X T S.obj₁ → Q S.obj₂ → Q S.obj₃)
    (hstep : ∀ F : DerivedCategory.{u + 1} X.Modules, Q F → ∀ t : ℤ, m ≤ t →
      (∀ i : ℤ, t < i → IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj F)) →
      ∃ P : DerivedCategory.{u + 1} X.Modules, IsAdmissible X T P ∧
        (∀ i : ℤ, t < i → IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj P)) ∧
        ∃ α : P ⟶ F, Epi ((DerivedCategory.homologyFunctor X.Modules t).map α))
    (E : DerivedCategory.{u + 1} X.Modules) (hQE : Q E) (t : ℤ)
    (hvan : ∀ i : ℤ, t < i → IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj E)) :
    ApproximationHolds X T E m :=
  (DerivedCategory.exists_approximatesFrom_of_step Q (IsAdmissible X T) m
    (fun _ _ _ u v w => isAdmissible_obj₂_of_distinguished X T (Triangle.mk u v w))
    hcone hstep E hQE t hvan).imp fun _ ⟨h, hα⟩ => ⟨h.1, h.2, hα⟩

end AlgebraicGeometry.PerfectApproximation

end
