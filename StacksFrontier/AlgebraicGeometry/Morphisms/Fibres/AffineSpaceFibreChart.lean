module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.RingTheory.Nullstellensatz
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal
public import StacksFrontier.RingTheory.MvPolynomial.LinearSubspaceDimension
public import StacksFrontier.Topology.Dimension.Krull

/-!
# The chart of a fibre of relative affine space, and the dimension of a linear subspace in it

The fibre of `𝔸^n_X → X` over a point `x` is the affine space `𝔸^n_{κ(x)}` over the residue
field, by `AlgebraicGeometry.AffineSpace.isPullback_map`, and that affine space is the spectrum
of a polynomial ring, by `AlgebraicGeometry.AffineSpace.SpecIso`. Composing the two gives a
*chart* `Spec κ(x)[x_i] ⟶ 𝔸^n_X`, a topological embedding whose image is the set-theoretic fibre
over `x`.

The chart is what turns a dimension bound for a closed subscheme of `𝔸^n_{κ(x)}` into a
dimension bound for a subset of `𝔸^n_X`. The bound used in the proof of [Stacks, Tag 0FD6] is
`Stacks.LinearSubspace.topologicalKrullDim_quotient_le_finrank_ker`: a closed subscheme cut out
by an ideal containing the coordinate forms of a surjective linear map `φ` has dimension at most
`dim ker φ`. Read through the chart it bounds the dimension of any subset of `𝔸^n_X` contained
in the image of that subscheme.

## Main definitions

* `AlgebraicGeometry.AffineSpace.residueFibreChart`: the chart
  `Spec κ(x)[x_i] ⟶ 𝔸^n_X` of the fibre of `𝔸^n_X → X` over `x`.

## Main results

* `AlgebraicGeometry.AffineSpace.residueFibreChart_comp_over` and
  `AlgebraicGeometry.AffineSpace.residueFibreChart_appTop_coord`: the chart lies over `x`, and
  it carries the `i`-th coordinate function of `𝔸^n_X` to the `i`-th variable.
* `AlgebraicGeometry.AffineSpace.isEmbedding_residueFibreChart` and
  `AlgebraicGeometry.AffineSpace.range_residueFibreChart`: the chart is a topological embedding
  with image the set-theoretic fibre over `x`.
* `AlgebraicGeometry.AffineSpace.topologicalKrullDim_le_of_subset_image_zeroLocus`: a subset of
  `𝔸^n_X` inside the chart image of `V(I)` has dimension at most `dim κ(x)[x_i]/I`.
* `AlgebraicGeometry.AffineSpace.topologicalKrullDim_le_finrank_ker_of_subset_image_zeroLocus`:
  **the linear-subspace bound transported to `𝔸^n_X`**, the form a fibre-dimension count
  consumes.
* `AlgebraicGeometry.AffineSpace.exists_coords_of_isClosed_singleton`: a closed point of
  `𝔸^m_κ` over an algebraically closed field has a tuple of coordinates, and a linear condition
  on that tuple puts the point into the corresponding subspace.

## Implementation notes

The chart is a preimmersion, not a closed or open immersion: the fibre of `𝔸^n_X → X` over `x`
is neither closed nor open in general. A preimmersion is a topological embedding, which is all a
dimension comparison needs, and `AlgebraicGeometry.AffineSpace.map` of
`AlgebraicGeometry.Scheme.fromSpecResidueField` is one because preimmersions are stable under
base change and that square is cartesian.

The hypothesis of the main results is that the subset lies in the chart image of `V(I)`, rather
than that it is the fibre of some morphism: a dimension bound only needs a containment, and the
containment is what a geometric situation produces. Which ideal `I` to use, and why the points
in question satisfy it, is the business of the consumer; the coordinate identity
`residueFibreChart_appTop_coord` is the tool for that, since a linear form in the variables
pulls back from the corresponding combination of coordinate functions.

No `@[stacks]` attribute is attached: this is a step inside the proof of Tag 0FD6.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v w

namespace AlgebraicGeometry.AffineSpace

variable (n : Type u) {X : Scheme.{u}} (x : X)

/-- **`𝔸^n` over the residue field at `x` is the fibre of `𝔸^n_X → X` over `x`**, so the
projection to it is a preimmersion: preimmersions are stable under base change and
`Spec κ(x) ⟶ X` is one. -/
instance isPreimmersion_map_fromSpecResidueField :
    IsPreimmersion (map n (X.fromSpecResidueField x)) :=
  MorphismProperty.of_isPullback (isPullback_map (X.fromSpecResidueField x)).flip inferInstance

/-- **The chart of the fibre of `𝔸^n_X → X` over `x`**: the spectrum of the polynomial ring over
the residue field at `x`, mapping to `𝔸^n_X`. -/
def residueFibreChart : Spec (.of (MvPolynomial n ↥(X.residueField x))) ⟶ 𝔸(n; X) :=
  (SpecIso n (X.residueField x)).inv ≫ map n (X.fromSpecResidueField x)

/-- The chart of the fibre of `𝔸^n_X → X` over `x` is a preimmersion. -/
instance isPreimmersion_residueFibreChart : IsPreimmersion (residueFibreChart n x) := by
  rw [residueFibreChart]
  infer_instance

/-- **The chart lies over `x`**: composed with `𝔸^n_X → X` it is the canonical morphism
`Spec κ(x) ⟶ X` precomposed with the projection of the chart. -/
theorem residueFibreChart_comp_over :
    residueFibreChart n x ≫ (𝔸(n; X) ↘ X) =
      (SpecIso n (X.residueField x)).inv ≫ (𝔸(n; Spec (X.residueField x)) ↘
        Spec (X.residueField x)) ≫ X.fromSpecResidueField x := by
  rw [residueFibreChart, Category.assoc, map_over]

/-- **The chart carries the `i`-th coordinate function to the `i`-th variable.** This is what
identifies a linear form in the variables with the corresponding combination of coordinate
functions. -/
@[simp]
theorem residueFibreChart_appTop_coord (i : n) :
    (residueFibreChart n x).appTop (coord X i) =
      (Scheme.ΓSpecIso _).inv (MvPolynomial.X i) := by
  simp only [residueFibreChart, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    map_appTop_coord, SpecIso_inv_appTop_coord]

/-- **The chart is a topological embedding**, being a preimmersion. -/
theorem isEmbedding_residueFibreChart :
    Topology.IsEmbedding (residueFibreChart n x).base :=
  (residueFibreChart n x).isEmbedding

/-- **The image of the chart is exactly the set-theoretic fibre of `𝔸^n_X → X` over `x`.** This
is what lets a containment hypothesis about the chart image be discharged for a set of points
lying over `x`. -/
theorem range_residueFibreChart :
    Set.range (residueFibreChart n x) = (𝔸(n; X) ↘ X) ⁻¹' {x} := by
  have hsurj : Function.Surjective (SpecIso n (X.residueField x)).inv :=
    (Scheme.homeoOfIso (SpecIso n (X.residueField x)).symm).surjective
  have hmap : Set.range (map n (X.fromSpecResidueField x)) =
      (𝔸(n; X) ↘ X) ⁻¹' {x} := by
    set h := isPullback_map (n := n) (X.fromSpecResidueField x) with hdef
    have hs : Function.Surjective h.isoPullback.hom :=
      (Scheme.homeoOfIso h.isoPullback).surjective
    have happ : ∀ p, (map n (X.fromSpecResidueField x)) p =
        (Limits.pullback.fst (𝔸(n; X) ↘ X) (X.fromSpecResidueField x))
          (h.isoPullback.hom p) := fun p =>
      (congrArg (fun m : 𝔸(n; Spec (X.residueField x)) ⟶ 𝔸(n; X) => m p)
        h.isoPullback_hom_fst).symm.trans (Scheme.Hom.comp_apply _ _ p)
    have hfun : (fun p => (map n (X.fromSpecResidueField x)) p) =
        (Limits.pullback.fst (𝔸(n; X) ↘ X) (X.fromSpecResidueField x)) ∘ h.isoPullback.hom :=
      funext happ
    rw [show Set.range (map n (X.fromSpecResidueField x)) =
      Set.range ((Limits.pullback.fst (𝔸(n; X) ↘ X) (X.fromSpecResidueField x)) ∘
        h.isoPullback.hom) from congrArg Set.range hfun, hs.range_comp,
      Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
  rw [show Set.range (residueFibreChart n x) =
    Set.range ((map n (X.fromSpecResidueField x)) ∘
      (SpecIso n (X.residueField x)).inv) from rfl, hsurj.range_comp, hmap]

/-- **A subset of `𝔸^n_X` inside the chart image of a closed subscheme `V(I)` of `𝔸^n_{κ(x)}` has
dimension at most that of `V(I)`.** The chart is an embedding, so it preserves the dimension of
`V(I)`, and dimension is monotone under inclusion of subsets. -/
theorem topologicalKrullDim_le_of_subset_image_zeroLocus
    (I : Ideal (MvPolynomial n ↥(X.residueField x))) (S : Set 𝔸(n; X))
    (hS : S ⊆ (residueFibreChart n x).base ''
      PrimeSpectrum.zeroLocus (I : Set (MvPolynomial n ↥(X.residueField x)))) :
    topologicalKrullDim S ≤ ringKrullDim (MvPolynomial n ↥(X.residueField x) ⧸ I) := by
  refine le_trans (topologicalKrullDim_le_of_subset hS) (le_of_eq ?_)
  exact (IsHomeomorph.topologicalKrullDim_eq _
    (((isEmbedding_residueFibreChart n x).homeomorphImage _).isHomeomorph)).symm.trans
      (topologicalKrullDim_zeroLocus I)

/-- **The linear-subspace dimension bound, transported to `𝔸^n_X`.** Let `φ : κ(x)^n → κ(x)^τ`
be a surjective linear map and let `I` be an ideal of `κ(x)[x_i]` containing the linear forms of
the coordinates of `φ`. Then every subset of `𝔸^n_X` lying in the chart image of `V(I)` has
dimension at most `dim ker φ`.

With `φ` the evaluation `ev_x` of a linear system this is the fibre bound
`dim ≤ r - (dim X + 1)` of the dimension count in the proof of [Stacks, Tag 0FD6]. -/
theorem topologicalKrullDim_le_finrank_ker_of_subset_image_zeroLocus [Fintype n] [DecidableEq n]
    {τ : Type w} [Finite τ] (I : Ideal (MvPolynomial n ↥(X.residueField x)))
    {φ : (n → ↥(X.residueField x)) →ₗ[↥(X.residueField x)] (τ → ↥(X.residueField x))}
    (hφ : Function.Surjective φ)
    (hmem : ∀ j, Stacks.LinearSubspace.linearForm (fun i => φ (Pi.single i 1) j) ∈ I)
    (S : Set 𝔸(n; X))
    (hS : S ⊆ (residueFibreChart n x).base ''
      PrimeSpectrum.zeroLocus (I : Set (MvPolynomial n ↥(X.residueField x)))) :
    topologicalKrullDim S ≤
      ((Module.finrank ↥(X.residueField x) (LinearMap.ker φ) : ℕ) : WithBot ℕ∞) := by
  have := Fintype.ofFinite τ
  refine le_trans (topologicalKrullDim_le_of_subset_image_zeroLocus n x I S hS) ?_
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact Stacks.LinearSubspace.topologicalKrullDim_quotient_le_finrank_ker I hφ hmem

/-- **A closed point of `𝔸^m_κ` over an algebraically closed field has coordinates.** There is a
tuple `a : m → κ` such that the point lies in `V(I)` for every ideal `I` whose elements all
vanish at `a`.

This is the Nullstellensatz (`MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal`) read for a
closed point of the spectrum. Together with
`AlgebraicGeometry.AffineSpace.topologicalKrullDim_le_finrank_ker_of_subset_image_zeroLocus` it
closes the interface a fibre-dimension count needs: a closed point of the fibre is a tuple of
coordinates, and a linear condition on that tuple puts the point into the subspace whose
dimension is bounded. -/
theorem exists_coords_of_isClosed_singleton {κ : Type v} [Field κ] [IsAlgClosed κ] {m : Type w}
    [Finite m] (q : PrimeSpectrum (MvPolynomial m κ))
    (hq : IsClosed ({q} : Set (PrimeSpectrum (MvPolynomial m κ)))) :
    ∃ a : m → κ, ∀ I : Ideal (MvPolynomial m κ),
      (∀ f ∈ I, MvPolynomial.aeval a f = 0) →
        q ∈ PrimeSpectrum.zeroLocus (I : Set (MvPolynomial m κ)) := by
  obtain ⟨a, ha⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal κ
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp hq)
  refine ⟨a, fun I hI => PrimeSpectrum.mem_zeroLocus _ _ |>.mpr fun f hf => ?_⟩
  rw [ha]
  exact MvPolynomial.mem_vanishingIdeal_iff.mpr fun y hy => by
    rw [Set.mem_singleton_iff] at hy
    exact hy ▸ hI f hf

end AlgebraicGeometry.AffineSpace

end
