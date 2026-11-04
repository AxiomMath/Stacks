module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.AffineSpaceFibreChart

/-!
# Linear forms in the coordinates of relative affine space, read in the chart of a fibre

A tuple `g : n → Γ(X, ⊤)` of global functions on `X` gives the global function
`∑ i, pr^* (g i) · x_i` on `𝔸^n_X`, a *linear form in the coordinates with coefficients pulled
back from `X`*. Read in the chart `Spec κ(x)[x_i] ⟶ 𝔸^n_X` of the fibre over a point `x`
(`AlgebraicGeometry.AffineSpace.residueFibreChart`), such a function becomes the linear form of
`StacksFrontier.RingTheory.MvPolynomial.LinearSubspaceDimension` whose coefficients are the values
of the `g i` at `x`.

That identification is what turns a vanishing condition on finitely many such functions into a
containment in the zero locus of an ideal of linear forms, and hence — by
`AlgebraicGeometry.AffineSpace.topologicalKrullDim_le_finrank_ker_of_subset_image_zeroLocus` —
into a dimension bound for the set of points of `𝔸^n_X` over `x` where they all vanish. This is
the geometric half of the fibre-dimension count in the proof of [Stacks, Tag 0FD6]: there the
coefficients are the matrix of the evaluation `ev_x` of the linear system.

## Main definitions

* `AlgebraicGeometry.AffineSpace.coordForm`: the function `∑ i, pr^* (g i) · x_i` on `𝔸^n_X`.

## Main results

* `AlgebraicGeometry.Scheme.fromSpecResidueField_appTop_apply`: the pullback of a global function
  along `Spec κ(x) ⟶ X` is its value at `x`.
* `AlgebraicGeometry.AffineSpace.residueFibreChart_appTop_pullback`: the chart carries a function
  pulled back from `X` to the constant polynomial with its value at `x`.
* `AlgebraicGeometry.AffineSpace.residueFibreChart_appTop_coordForm`: the chart carries
  `coordForm g` to the linear form with coefficients the values of the `g i` at `x`.
* `AlgebraicGeometry.AffineSpace.topologicalKrullDim_le_finrank_ker_of_coordForm_vanishing`:
  **the dimension bound**, for the set of points of `𝔸^n_X` over `x` at which the coordinate
  forms of a surjective linear map `φ` over `κ(x)` all vanish.

## Implementation notes

The chart is `(SpecIso n κ(x)).inv ≫ map n (X.fromSpecResidueField x)`, so a function pulled
back from `X` travels along `Spec κ(x)[x_i] ⟶ Spec κ(x) ⟶ X`, the first leg being
`Spec` of the inclusion of constants (`AlgebraicGeometry.AffineSpace.SpecIso_inv_over`) and the
second contributing evaluation at `x`
(`AlgebraicGeometry.Scheme.fromSpecResidueField_appTop_apply`).

The vanishing hypothesis is phrased as non-membership in the basic open of the function, which
is what a geometric situation produces, and transported to membership in the prime of the chart
preimage by `AlgebraicGeometry.basicOpen_eq_of_affine`.

No `@[stacks]` attribute is attached: this is a step inside the proof of Tag 0FD6.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace MvPolynomial

universe u v w

namespace AlgebraicGeometry

/-- `Spec.map f` on global sections sends `(ΓSpecIso R).inv a` to `(ΓSpecIso S).inv (f a)`. -/
private theorem appTop_map_ΓSpecIso_inv {R S : CommRingCat.{u}} (f : R ⟶ S) (a : R) :
    (Spec.map f).appTop ((Scheme.ΓSpecIso R).inv a) = (Scheme.ΓSpecIso S).inv (f a) := by
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]

/-- **A global function pulled back to `Spec κ(x)` is its value at `x`.** -/
theorem Scheme.fromSpecResidueField_appTop_apply {X : Scheme.{u}} (x : X) (g : Γ(X, ⊤)) :
    (X.fromSpecResidueField x).appTop g =
      (Scheme.ΓSpecIso (X.residueField x)).inv (X.Γevaluation x g) := by
  rw [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    Scheme.fromSpecStalk_appTop]
  simp only [CommRingCat.comp_apply, homOfLE_refl, CategoryTheory.op_id,
    CategoryTheory.Functor.map_id, CommRingCat.id_apply]
  exact appTop_map_ΓSpecIso_inv _ _

namespace AffineSpace

variable (n : Type u) {X : Scheme.{u}} (x : X)

/-- **A linear form in the coordinates of `𝔸^n_X` with coefficients pulled back from `X`**:
the global function `∑ i, pr^* (g i) · x_i`. -/
def coordForm (g : n → Γ(X, ⊤)) [Fintype n] : Γ(𝔸(n; X), ⊤) :=
  ∑ i, (𝔸(n; X) ↘ X).appTop (g i) * coord X i

/-- **The chart carries a function pulled back from `X` to the constant with its value at `x`.**
The chart factors through `Spec κ(x)`, where a function pulled back from `X` becomes its value at
`x`, and the remaining leg `Spec κ(x)[x_i] ⟶ Spec κ(x)` is the inclusion of constants. -/
theorem residueFibreChart_appTop_pullback (g : Γ(X, ⊤)) :
    (residueFibreChart n x).appTop ((𝔸(n; X) ↘ X).appTop g) =
      (Scheme.ΓSpecIso _).inv (C (X.Γevaluation x g)) := by
  have hcomp : residueFibreChart n x ≫ (𝔸(n; X) ↘ X) =
      Spec.map (CommRingCat.ofHom (C (σ := n) (R := ↥(X.residueField x)))) ≫
        X.fromSpecResidueField x := by
    rw [residueFibreChart_comp_over, ← Category.assoc, SpecIso_inv_over]
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hcomp, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, Scheme.fromSpecResidueField_appTop_apply]
  exact appTop_map_ΓSpecIso_inv _ _

/-- **The chart carries `coordForm g` to the linear form whose coefficients are the values of the
`g i` at `x`.** -/
theorem residueFibreChart_appTop_coordForm [Fintype n] (g : n → Γ(X, ⊤)) :
    (residueFibreChart n x).appTop (coordForm n g) =
      (Scheme.ΓSpecIso _).inv
        (Stacks.LinearSubspace.linearForm (fun i => X.Γevaluation x (g i))) := by
  rw [coordForm, map_sum, Stacks.LinearSubspace.linearForm_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, residueFibreChart_appTop_pullback, residueFibreChart_appTop_coord, map_mul]

/-- **A point of `𝔸^n_X` lying over `x` at which a family of coordinate forms vanishes lies in
the chart image of the zero locus of the ideal those forms generate.** -/
theorem mem_image_zeroLocus_of_notMem_basicOpen_coordForm [Fintype n] {τ : Type w}
    (g : τ → n → Γ(X, ⊤)) (y : 𝔸(n; X)) (hy : (𝔸(n; X) ↘ X) y = x)
    (hvan : ∀ j, y ∉ 𝔸(n; X).basicOpen (coordForm n (g j))) :
    y ∈ (residueFibreChart n x).base '' PrimeSpectrum.zeroLocus
      ((Ideal.span (Set.range fun j => Stacks.LinearSubspace.linearForm
        (fun i => X.Γevaluation x (g j i))) :
          Ideal (MvPolynomial n ↥(X.residueField x))) :
        Set (MvPolynomial n ↥(X.residueField x))) := by
  have hrange : y ∈ Set.range (residueFibreChart n x).base := by
    rw [show Set.range (residueFibreChart n x).base =
      Set.range (residueFibreChart n x) from rfl, range_residueFibreChart]
    exact hy
  obtain ⟨p, hp⟩ := hrange
  refine ⟨p, PrimeSpectrum.mem_zeroLocus _ _ |>.mpr (Ideal.span_le.2 ?_), hp⟩
  rintro _ ⟨j, rfl⟩
  have hpre : (residueFibreChart n x) ⁻¹ᵁ 𝔸(n; X).basicOpen (coordForm n (g j)) =
      PrimeSpectrum.basicOpen (Stacks.LinearSubspace.linearForm
        (fun i => X.Γevaluation x (g j i))) := by
    rw [Scheme.preimage_basicOpen_top, residueFibreChart_appTop_coordForm,
      basicOpen_eq_of_affine]
  have hnot : p ∉ PrimeSpectrum.basicOpen (Stacks.LinearSubspace.linearForm
      (fun i => X.Γevaluation x (g j i))) := by
    rw [← hpre]
    intro hmem
    exact hvan j (hp ▸ hmem)
  by_contra hc
  exact hnot ((PrimeSpectrum.mem_basicOpen _ _).mpr hc)

/-- **The dimension bound for the locus of a fibre cut out by coordinate forms.** Let
`φ : κ(x)^n → κ(x)^τ` be a surjective linear map and let `g j i` be global functions on `X`
whose values at `x` are the entries of its matrix. Then every subset of `𝔸^n_X` consisting of
points which lie over `x` and at which all the forms `∑ i, pr^* (g j i) · x_i` vanish has
dimension at most `dim ker φ`.

With `φ` the evaluation `ev_x` of a linear system this is the fibre bound `r - (n + 1)` of the
dimension count in the proof of [Stacks, Tag 0FD6]. -/
theorem topologicalKrullDim_le_finrank_ker_of_coordForm_vanishing [Fintype n] [DecidableEq n]
    {τ : Type w} [Finite τ]
    {φ : (n → ↥(X.residueField x)) →ₗ[↥(X.residueField x)] (τ → ↥(X.residueField x))}
    (hφ : Function.Surjective φ) (g : τ → n → Γ(X, ⊤))
    (hg : ∀ j i, X.Γevaluation x (g j i) = φ (Pi.single i 1) j) (S : Set 𝔸(n; X))
    (hS : ∀ y ∈ S, (𝔸(n; X) ↘ X) y = x ∧
      ∀ j, y ∉ 𝔸(n; X).basicOpen (coordForm n (g j))) :
    topologicalKrullDim S ≤
      ((Module.finrank ↥(X.residueField x) (LinearMap.ker φ) : ℕ) : WithBot ℕ∞) := by
  refine topologicalKrullDim_le_finrank_ker_of_subset_image_zeroLocus n x
    (Ideal.span (Set.range fun j => Stacks.LinearSubspace.linearForm
      (fun i => X.Γevaluation x (g j i)))) hφ (fun j => ?_) S (fun y hy => ?_)
  · refine Ideal.subset_span ⟨j, ?_⟩
    exact congrArg Stacks.LinearSubspace.linearForm (funext fun i => hg j i)
  · exact mem_image_zeroLocus_of_notMem_basicOpen_coordForm n x g y (hS y hy).1 (hS y hy).2

end AffineSpace

end AlgebraicGeometry

end
