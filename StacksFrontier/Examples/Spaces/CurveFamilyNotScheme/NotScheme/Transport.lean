module

public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme

/-!
# Transporting a dominating closed subset through the contraction and the blowup

In the proof of Stacks 0D5E, if the contracted total space `X` were a scheme `U`, an affine open
neighbourhood of the image `x` of the curve `C` would produce a closed subset `T ⊆ U` avoiding
`x` and surjecting onto the affine line. The source pulls `T` back to the blowup `Z` and pushes it
down to the cubic surface `Y`, and observes that the result is a proper closed subset of `Y`
dominating the affine line which meets the central fibre `Y₀` only in the blown up point `y`. This
contradicts the choice of `y`.

This file proves that step at the level of the underlying topological spaces, which is all the
argument uses: with `π : Z → Y` a closed map whose central fibre `π⁻¹(Y₀)` is contained in
`E ∪ C`, `E` mapping to `y`, and `φ : Z → U` a surjection collapsing `C` to `x`, the set
`π(φ⁻¹ T)` is closed, surjects onto the base, and meets `Y₀` at most in `y`.

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.isClosed_image_preimage`,
  `Stacks.Examples.CurveFamilyNotScheme.surjective_image_preimage` and
  `Stacks.Examples.CurveFamilyNotScheme.image_preimage_inter_fibre_subset`: the three properties
  of the transported set.
* `Stacks.Examples.CurveFamilyNotScheme.not_exists_isClosed_notMem_surjective_of_transport`: the
  contradiction with the choice of `y`.
* `Stacks.Examples.CurveFamilyNotScheme.not_exists_scheme_of_transport`: no scheme proper over
  an affine base with infinite fibres receives such a surjection from `Z`.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

section Topology

variable {Z Y U S : Type*} [TopologicalSpace Z] [TopologicalSpace Y] [TopologicalSpace U]
  {π : Z → Y} {φ : Z → U} {p : Y → S} {q : U → S}

/-- The image in `Y` of the preimage in `Z` of a closed subset of `U` is closed when `π` is a
closed map and `φ` is continuous. -/
theorem isClosed_image_preimage (hπ : IsClosedMap π) (hφ : Continuous φ) {T : Set U}
    (hT : IsClosed T) : IsClosed (π '' (φ ⁻¹' T)) :=
  hπ _ (hT.preimage hφ)

/-- The transported set surjects onto the base when `T` does and `φ` is surjective. -/
theorem surjective_image_preimage (hcomm : ∀ z, p (π z) = q (φ z))
    (hφ : Function.Surjective φ) {T : Set U} (hT : ∀ s, ∃ u ∈ T, q u = s) (s : S) :
    ∃ w ∈ π '' (φ ⁻¹' T), p w = s := by
  obtain ⟨u, huT, rfl⟩ := hT s
  obtain ⟨z, rfl⟩ := hφ u
  exact ⟨π z, ⟨z, huT, rfl⟩, hcomm z⟩

/-- The transported set meets the fibre `p⁻¹(s₀)` at most in `y`, when the preimage of that fibre
in `Z` lies in `E ∪ C`, `E` maps to `y`, `C` maps to `x` and `x ∉ T`. -/
theorem image_preimage_inter_fibre_subset (hcomm : ∀ z, p (π z) = q (φ z)) {s₀ : S} {y : Y}
    {x : U} {E C : Set Z} (hfib : ∀ z, p (π z) = s₀ → z ∈ E ∪ C) (hE : ∀ z ∈ E, π z = y)
    (hC : ∀ z ∈ C, φ z = x) {T : Set U} (hxT : x ∉ T) :
    ∀ w ∈ π '' (φ ⁻¹' T), p w = s₀ → w = y := by
  rintro _ ⟨z, hzT, rfl⟩ hw
  rcases hfib z hw with hzE | hzC
  · exact hE z hzE
  · exact absurd (hC z hzC ▸ hzT : x ∈ T) hxT

/-- **The transport contradicts the choice of `y`.** Suppose every proper closed subset of `Y`
surjecting onto the base meets the fibre `p⁻¹(s₀)` in a point other than `y` (the source's
property (2)), and that fibre contains a point other than `y`. Then no closed `T ⊆ U` avoiding
`x` surjects onto the base. -/
theorem not_exists_isClosed_notMem_surjective_of_transport (hπ : IsClosedMap π)
    (hφc : Continuous φ) (hφ : Function.Surjective φ) (hcomm : ∀ z, p (π z) = q (φ z))
    {s₀ : S} {y : Y} {x : U} {E C : Set Z} (hfib : ∀ z, p (π z) = s₀ → z ∈ E ∪ C)
    (hE : ∀ z ∈ E, π z = y) (hC : ∀ z ∈ C, φ z = x) (y' : Y) (hy' : p y' = s₀) (hy'y : y' ≠ y)
    (hprop : ∀ T : Set Y, IsClosed T → T ≠ Set.univ → (∀ s, ∃ w ∈ T, p w = s) →
      ∃ w ∈ T, p w = s₀ ∧ w ≠ y) :
    ¬ ∃ T : Set U, IsClosed T ∧ x ∉ T ∧ ∀ s, ∃ u ∈ T, q u = s := by
  rintro ⟨T, hT, hxT, hTs⟩
  have hsub := image_preimage_inter_fibre_subset hcomm hfib hE hC hxT
  have hne : π '' (φ ⁻¹' T) ≠ Set.univ := fun h =>
    hy'y (hsub y' (h ▸ Set.mem_univ y') hy')
  obtain ⟨w, hwT, hw, hwy⟩ := hprop _ (isClosed_image_preimage hπ hφc hT) hne
    (surjective_image_preimage hcomm hφ hTs)
  exact hwy (hsub w hwT hw)

end Topology

/-- **No scheme receives the contraction.** Let `π : Z ⟶ Y` be a morphism of schemes which is a
closed map, `p : Y ⟶ S` with `S` affine, `s₀ ∈ S`, and suppose the fibre `p⁻¹(s₀)` contains a
point other than `y` and every proper closed subset of `Y` surjecting onto `S` meets `p⁻¹(s₀)` in
a point other than `y`. Let `E, C ⊆ Z` with `π⁻¹(p⁻¹(s₀)) ⊆ E ∪ C` and `π(E) = {y}`. Then there is
no scheme `U` with a proper morphism `q : U ⟶ S` all of whose fibres are infinite and a
surjective morphism `φ : Z ⟶ U` over `S` collapsing `C` to a point. -/
theorem not_exists_scheme_of_transport {Z Y S : Scheme.{u}} [IsAffine S] (π : Z ⟶ Y)
    (hπ : IsClosedMap π) (p : Y ⟶ S) {s₀ : S} {y : Y} {E C : Set Z}
    (hfib : ∀ z, p (π z) = s₀ → z ∈ E ∪ C) (hE : ∀ z ∈ E, π z = y) (y' : Y) (hy' : p y' = s₀)
    (hy'y : y' ≠ y)
    (hprop : ∀ T : Set Y, IsClosed T → T ≠ Set.univ → (∀ s, ∃ w ∈ T, p w = s) →
      ∃ w ∈ T, p w = s₀ ∧ w ≠ y) :
    ¬ ∃ (U : Scheme.{u}) (q : U ⟶ S) (_ : IsProper q) (φ : Z ⟶ U) (x : U),
        (∀ s : S, ¬ (q ⁻¹' {s}).Finite) ∧ Function.Surjective φ ∧ π ≫ p = φ ≫ q ∧
          ∀ z ∈ C, φ z = x := by
  rintro ⟨U, q, hq, φ, x, hfibres, hφ, hcomm, hC⟩
  have hcomm' : ∀ z, p (π z) = q (φ z) := fun z => by
    rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]
  exact not_exists_isClosed_notMem_surjective_of_transport hπ φ.continuous hφ hcomm' hfib hE hC
    y' hy' hy'y hprop (exists_isClosed_notMem_surjective q hfibres x)

end Stacks.Examples.CurveFamilyNotScheme

end
