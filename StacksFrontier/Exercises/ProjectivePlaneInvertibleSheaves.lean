module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpaceCocycle
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistGlobalSectionsPolynomial
public import StacksFrontier.AlgebraicGeometry.ProjTwistSectionRing.Bijectivity

/-!
# Invertible sheaves and twisted global sections on the projective plane

Let `k` be a field and `ℙ²_k = Proj k[X₀, X₁, X₂]`, the polynomial ring graded by total degree.
Every invertible sheaf on `ℙ²_k` is isomorphic to a twist `𝒪(n)` for some `n ∈ ℤ`, and the
global sections of `𝒪(n)` are the degree-`n` part of `k[X₀, X₁, X₂]`, which is zero for `n < 0`.

The first assertion is the case `R = k`, `n = 2` of the computation of the Picard group of
projective space over a unique factorization domain,
`Stacks.PicardUFD.exists_iso_twistingSheaf_general` (Tag 0BXJ). In nonnegative degree the second
assertion is the bijectivity of the canonical section map,
`Stacks.ProjectiveSpace.Cohomology.bijective_degreeSection_mvPolynomial`. In negative degree it
is the vanishing `Stacks.ProjectiveSpace.Cohomology.subsingleton_twistTopSections_of_neg`
proved here: a global section of `𝒪(d)` is one Laurent element regular on every standard chart
`D₊(Tᵢ)`, hence a polynomial of total degree `d`, and there is none when `d < 0`.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.subsingleton_twistTopSections_of_neg`:
  `Γ(ℙⁿ_R, 𝒪(d)) = 0` for `0 < n` and `d < 0`.
* `Stacks.ProjectiveSpace.Cohomology.twistTopSectionsAddEquivIntegerGrading`:
  `Γ(ℙⁿ_R, 𝒪(d))` is the degree-`d` part of `R[T₀, …, Tₙ]` for every `d ∈ ℤ`, for `0 < n`.
* `Stacks.ProjectiveSpace.Cohomology.projectivePlane_exists_iso_twistingSheaf_and_sections`:
  the statement of Tag 02AX.

## References

* [Stacks Project, Tag 02AX](https://stacks.math.columbia.edu/tag/02AX)
* [Stacks Project, Tag 0BXJ](https://stacks.math.columbia.edu/tag/0BXJ)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjectiveSpace.Cohomology

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (R : Type u) [CommRing R] (n : ℕ)

/-- **A global section of `𝒪(d)` with `d < 0` has zero chart element on every standard chart**
of `ℙⁿ_R`, `0 < n`: its chart element is regular on every chart `D₊(Tᵢ)`, hence a polynomial of
negative total degree. -/
theorem coe_chartElt_singleton_eq_zero_of_neg (hn : 0 < n) {d : ℤ} (hd : d < 0)
    (σ : twistTopSections R n d) (i : Fin (n + 1)) :
    ((chartElt R n d {i} ⟨i, Finset.mem_singleton_self i⟩ σ :
      twistChart R n d (↑({i} : Finset (Fin (n + 1))) : Set (Fin (n + 1)))) :
        (Fin (n + 1) → ℤ) →₀ R) = 0 := by
  have hsi : ∀ j : Fin (n + 1), ({j} : Finset (Fin (n + 1))).Nonempty :=
    fun j => ⟨j, Finset.mem_singleton_self j⟩
  have huniv : (Finset.univ : Finset (Fin (n + 1))).Nonempty := ⟨0, Finset.mem_univ 0⟩
  have hcoe : ∀ j : Fin (n + 1),
      (chartElt R n d Finset.univ huniv σ : (Fin (n + 1) → ℤ) →₀ R)
        = ((chartElt R n d {j} (hsi j) σ) : (Fin (n + 1) → ℤ) →₀ R) :=
    fun j => coe_chartElt_eq {j} Finset.univ (hsi j) huniv (Finset.subset_univ _) σ
  have hchart : ∀ j : Fin (n + 1),
      ((chartElt R n d Finset.univ huniv σ) : (Fin (n + 1) → ℤ) →₀ R)
        ∈ twistChart R n d (↑({j} : Finset (Fin (n + 1))) : Set (Fin (n + 1))) :=
    fun j => (hcoe j).symm ▸ (chartElt R n d {j} (hsi j) σ).2
  have hv0 : ((chartElt R n d Finset.univ huniv σ) : (Fin (n + 1) → ℤ) →₀ R)
      ∈ twistChart R n d (∅ : Set (Fin (n + 1))) := by
    rw [← twistChart_iInf_singleton n hn d]
    refine Submodule.mem_iInf _ |>.2 fun j => ?_
    have hj := hchart j
    rwa [Finset.coe_singleton] at hj
  rw [twistChart_eq_bot_of_neg n hd, Submodule.mem_bot] at hv0
  exact (hcoe i).symm.trans hv0

/-- **`Γ(ℙⁿ_R, 𝒪(d)) = 0` for `0 < n` and `d < 0`** ([Stacks, Tag 01XT], degree zero, negative
twist, read on the global sections themselves). -/
theorem subsingleton_twistTopSections_of_neg (hn : 0 < n) {d : ℤ} (hd : d < 0) :
    Subsingleton (twistTopSections R n d) :=
  ⟨fun σ τ => eq_of_twistRes_singleton_eq fun i =>
    (chartSectionsAddEquivTwistChart R n d {i} ⟨i, Finset.mem_singleton_self i⟩).injective
      (Subtype.ext ((coe_chartElt_singleton_eq_zero_of_neg R n hn hd σ i).trans
        (coe_chartElt_singleton_eq_zero_of_neg R n hn hd τ i).symm))⟩

/-- The degree-`k` homogeneous polynomials, read inside the grading of `R[T₀, …, Tₙ]` extended
by zero to all integer degrees. -/
def homogeneousAddEquivIntegerGrading (k : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R k ≃+
      integerGrading (S := MvPolynomial (Fin (n + 1)) R)
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (k : ℤ) :=
  (show MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R k ≃+
      homogeneousSubmodule (S := MvPolynomial (Fin (n + 1)) R)
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) k from
    { toFun := fun a => ⟨a.1, a.2⟩
      invFun := fun a => ⟨a.1, a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }).trans
    (LinearEquiv.ofEq _ _ (integerGrading_natCast
      (S := MvPolynomial (Fin (n + 1)) R)
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) k).symm).toAddEquiv

/-- **`Γ(ℙⁿ_R, 𝒪(d))` is the degree-`d` part of `R[T₀, …, Tₙ]`, for every `d ∈ ℤ`**, `0 < n`: in
degree `d ≥ 0` through the canonical section map, and in degree `d < 0` both sides vanish. -/
theorem nonempty_twistTopSections_addEquiv_integerGrading (hn : 0 < n) (d : ℤ) :
    Nonempty (twistTopSections R n d ≃+
      integerGrading (S := MvPolynomial (Fin (n + 1)) R)
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d) := by
  rcases le_or_gt 0 d with hd | hd
  · lift d to ℕ using hd
    exact ⟨(Stacks.AlgebraicGeometry.ProjTwistSectionRing.degreeSectionEquiv
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (bijective_degreeSection_mvPolynomial R n) d).symm.trans
        (homogeneousAddEquivIntegerGrading R n d)⟩
  · have := subsingleton_twistTopSections_of_neg R n hn hd
    have : Subsingleton (integerGrading (S := MvPolynomial (Fin (n + 1)) R)
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d) := by
      rw [integerGrading_neg _ _ hd]
      infer_instance
    exact ⟨{ toFun := 0
             invFun := 0
             left_inv := fun _ => Subsingleton.elim _ _
             right_inv := fun _ => Subsingleton.elim _ _
             map_add' := fun _ _ => Subsingleton.elim _ _ }⟩

/-- **Stacks Project, Tag 02AX.** Let `k` be a field and `ℙ²_k = Proj k[X₀, X₁, X₂]`.

1. Every invertible sheaf on `ℙ²_k` is isomorphic to `𝒪(n)` for some `n ∈ ℤ`.
2. For `n ≥ 0` the canonical map `k[X₀, X₁, X₂]_n ⟶ Γ(ℙ²_k, 𝒪(n))` is bijective.
3. For every `n ∈ ℤ`, `Γ(ℙ²_k, 𝒪(n))` is the degree-`n` part of `k[X₀, X₁, X₂]` (the grading
   extended by zero, so both sides vanish for `n < 0`).

The twist `ℱ(n) = ℱ ⊗ 𝒪(n)` of the last sentence of the source is the definition
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafOfModules`. -/
@[stacks 02AX "invertible sheaves on ℙ²_k are the twists 𝒪(n), and Γ(ℙ²_k, 𝒪(n)) is the \
  degree-n part of k[X₀, X₁, X₂] for every n ∈ ℤ (through the canonical map for n ≥ 0)"]
theorem projectivePlane_exists_iso_twistingSheaf_and_sections (k : Type u) [Field k] :
    (∀ L : (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (2 + 1)) k)).Modules,
      Stacks.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin (2 + 1)) k)).presheaf
        (AlgebraicGeometry.Proj
          (MvPolynomial.homogeneousSubmodule (Fin (2 + 1)) k)).ringCatIsSheaf L →
      ∃ m : ℤ, Nonempty
        (L ≅ twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (2 + 1)) k) m)) ∧
    (∀ n : ℕ, Function.Bijective
      (degreeSection (MvPolynomial.homogeneousSubmodule (Fin (2 + 1)) k) n)) ∧
    (∀ n : ℤ, Nonempty (twistTopSections k 2 n ≃+
      integerGrading (S := MvPolynomial (Fin (2 + 1)) k)
        (MvPolynomial.homogeneousSubmodule (Fin (2 + 1)) k) n)) :=
  ⟨fun L hL => Stacks.PicardUFD.exists_iso_twistingSheaf_general k 2 L hL,
    bijective_degreeSection_mvPolynomial k 2,
    nonempty_twistTopSections_addEquiv_integerGrading k 2 (by norm_num)⟩

end Stacks.ProjectiveSpace.Cohomology
