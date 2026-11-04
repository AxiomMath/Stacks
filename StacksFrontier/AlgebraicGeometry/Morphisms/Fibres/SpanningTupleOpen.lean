module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniAffineSpaceChart
public import StacksFrontier.RingTheory.MvPolynomial.SpanningTupleDeterminant

/-!
# The nonempty open of tuples whose images span

Let `κ` be a field, let `W` be a `κ`-vector space of dimension `d` and let `φ : κ^ι → W` be a
surjective linear map.  A `d`-tuple of vectors of `κ^ι` is a `κ`-point of the affine space
`𝔸^(Fin d × ι)_κ`, and this file produces the open subscheme of that affine space consisting of
the tuples whose images under `φ` span `W`, together with the two facts a consumer needs: it is
nonempty, and a `κ`-point lies in it exactly when its tuple spans.

The open is the basic open of the determinant
`Stacks.SpanningTuple.spanDet` of
`StacksFrontier.RingTheory.MvPolynomial.SpanningTupleDeterminant`, read as a global function on
`𝔸^(Fin d × ι)_κ` through `AlgebraicGeometry.AffineSpace.ΓIso`.  It is nonempty because the
determinant is a nonzero polynomial and the affine space over a field is reduced, which is the
recipe of `Stacks.Bertini.FamilyDivisors.nonempty_rationalPointOpen`.

## What consumes this

This is Step 4 of the proof of [Stacks, Tag 0FH5]: for a closed point `x` of a smooth projective
scheme `X` over a field `k`, with `ℒ` very ample and `V ⊆ H⁰(X, ℒ)` the sections vanishing at
`x`, the tuples `(s₁, …, s_d) ∈ V^d` whose images generate `𝔪_xℒ_x/𝔪_x²ℒ_x` form a nonempty
open subset of `V^d`; the surjection `V → 𝔪_xℒ_x/𝔪_x²ℒ_x` is the `φ` above and
`d = dim_k 𝔪_xℒ_x/𝔪_x²ℒ_x = dim X` is its dimension.  The instantiation at that quotient is
`StacksFrontier.AlgebraicGeometry.ImmersionEvaluationSurjective.VanishingJetQuotient`.  **The
consumer — the proof of Tag 0FH5, which goes on to intersect the divisors `H_i = Z(s_i)` and to
apply Bertini to the result — is not yet built**; the statements below are phrased to be
independent of it.

## Main definitions

* `Stacks.SpanningTuple.spanDetFunction`: the determinant read as a global function on
  `𝔸^(Fin d × ι)_κ`.
* `Stacks.SpanningTuple.spanningOpen`: **the open `U ⊆ 𝔸^(Fin d × ι)_κ`** of tuples whose images
  span `W`.
* `Stacks.SpanningTuple.tuplePoint`: the `κ`-point of `𝔸^(Fin d × ι)_κ` with a given tuple of
  coordinates.

## Main results

* `AlgebraicGeometry.AffineSpace.homOfVector_appTop_ΓIso_inv_map`: a `κ`-point of `𝔸^n_κ` given
  by coordinates pulls a polynomial function back to its value at those coordinates.
* `Stacks.SpanningTuple.nonempty_spanningOpen`: **the open is nonempty** when `φ` is surjective.
* `Stacks.SpanningTuple.mem_spanningOpen_iff`: **a `κ`-point lies in the open exactly when its
  tuple's images span `W`.**
* `Stacks.SpanningTuple.exists_mem_spanningOpen_and_span_eq_top`: the two together, for a reader
  who wants only the conclusion of Step 4.

## Implementation notes

The affine space is `𝔸(Fin d × ι; Spec κ)` for the *product* index type, so that a tuple of `d`
vectors is a single point; the coordinate of a point is indexed by a pair `(j, i)`, the `i`-th
coordinate of the `j`-th vector.  No `ULift` appears, unlike in the Bertini family of divisors,
because the index type is built here rather than being the basis index of a given `k`-vector
space.

The identification of `Γ(𝔸^n_κ, ⊤)` with `κ[xᵢ]` is `AlgebraicGeometry.AffineSpace.ΓIso`
composed with `MvPolynomial.map` of `AlgebraicGeometry.Scheme.ΓSpecIso`, since `ΓIso` produces
polynomials over `Γ(Spec κ, ⊤)` rather than over `κ`.  Injectivity of that composite, which is
what turns a nonzero polynomial into a nonzero function, is injectivity of `MvPolynomial.map` of
an injective ring map (`MvPolynomial.map_injective`).

No `@[stacks]` attribute is attached: this is a step inside the proof of [Stacks, Tag 0FH5], not
the assertion of a tag.

## References

* [Stacks Project, Tag 0FH5](https://stacks.math.columbia.edu/tag/0FH5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial

universe u

namespace AlgebraicGeometry.AffineSpace

/-- **A `κ`-point of `𝔸^n_κ` given by its coordinates pulls a polynomial function back to its
value at those coordinates.**  The polynomial is read as a function through
`AlgebraicGeometry.AffineSpace.ΓIso`, after transporting its coefficients along
`AlgebraicGeometry.Scheme.ΓSpecIso`. -/
theorem homOfVector_appTop_ΓIso_inv_map {n : Type u} {κ : Type u} [CommRing κ] (a : n → κ)
    (F : MvPolynomial n κ) :
    (homOfVector (𝟙 (Spec (CommRingCat.of κ)))
          (fun q => (Scheme.ΓSpecIso (CommRingCat.of κ)).inv (a q))).appTop
        ((ΓIso n (Spec (CommRingCat.of κ))).inv
          (MvPolynomial.map (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom F)) =
      (Scheme.ΓSpecIso (CommRingCat.of κ)).inv (MvPolynomial.eval a F) := by
  set pt := homOfVector (𝟙 (Spec (CommRingCat.of κ)))
    (fun q => (Scheme.ΓSpecIso (CommRingCat.of κ)).inv (a q)) with hpt
  have := congrArg (fun ψ : MvPolynomial n κ →+* Γ(Spec (CommRingCat.of κ), ⊤) => ψ F)
    (MvPolynomial.ringHom_ext
      (f := pt.appTop.hom.comp
        (((ΓIso n (Spec (CommRingCat.of κ))).inv).hom.comp
          (MvPolynomial.map (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom)))
      (g := (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom.comp (MvPolynomial.eval a))
      (fun r => ?_) (fun i => ?_))
  · exact this
  · have hC : (ΓIso n (Spec (CommRingCat.of κ))).inv
        (MvPolynomial.C ((Scheme.ΓSpecIso (CommRingCat.of κ)).inv r)) =
        (𝔸(n; Spec (CommRingCat.of κ)) ↘ Spec (CommRingCat.of κ)).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of κ)).inv r) := by
      rw [← ΓIso_hom_appTop (n := n) ((Scheme.ΓSpecIso (CommRingCat.of κ)).inv r),
        ← CommRingCat.comp_apply, Iso.hom_inv_id]
      rfl
    have hover : pt.appTop
        ((𝔸(n; Spec (CommRingCat.of κ)) ↘ Spec (CommRingCat.of κ)).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of κ)).inv r)) =
        (Scheme.ΓSpecIso (CommRingCat.of κ)).inv r := by
      have h := congrArg
        (fun m : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of κ) =>
          m.appTop ((Scheme.ΓSpecIso (CommRingCat.of κ)).inv r))
        (homOfVector_over (𝟙 (Spec (CommRingCat.of κ)))
          (fun q => (Scheme.ΓSpecIso (CommRingCat.of κ)).inv (a q)))
      simpa only [hpt, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.Hom.id_appTop,
        CommRingCat.id_apply] using h
    simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.map_C, MvPolynomial.eval_C]
    rw [hC, hover]
  · have hX : (ΓIso n (Spec (CommRingCat.of κ))).inv (MvPolynomial.X i) =
        coord (Spec (CommRingCat.of κ)) i := by
      rw [← ΓIso_hom_coord (n := n) (S := Spec (CommRingCat.of κ)) i, ← CommRingCat.comp_apply,
        Iso.hom_inv_id]
      rfl
    simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.map_X, MvPolynomial.eval_X]
    rw [hX, hpt, homOfVector_appTop_coord]

end AlgebraicGeometry.AffineSpace

namespace Stacks.SpanningTuple

variable {κ : Type u} [Field κ] {ι : Type u} [Fintype ι] [DecidableEq ι]
  {W : Type u} [AddCommGroup W] [Module κ W] {d : ℕ}

/-- The affine space `𝔸^(Fin d × ι)_κ` of `d`-tuples of vectors of `κ^ι`. -/
abbrev tupleSpace (κ : Type u) [Field κ] (ι : Type u) (d : ℕ) : Scheme.{u} :=
  𝔸(Fin d × ι; Spec (CommRingCat.of κ))

/-- **The determinant of `Stacks.SpanningTuple.spanDet`, read as a global function on the affine
space of tuples.** -/
def spanDetFunction (e : Module.Basis (Fin d) κ W) (φ : (ι → κ) →ₗ[κ] W) :
    Γ(tupleSpace κ ι d, ⊤) :=
  (AffineSpace.ΓIso (Fin d × ι) (Spec (CommRingCat.of κ))).inv
    (MvPolynomial.map (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom (spanDet e φ))

/-- The function is nonzero as soon as the determinant is a nonzero polynomial: the two
identifications it is read through are injective. -/
theorem spanDetFunction_ne_zero (e : Module.Basis (Fin d) κ W) {φ : (ι → κ) →ₗ[κ] W}
    (hφ : Function.Surjective φ) : spanDetFunction e φ ≠ 0 := by
  intro h0
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of κ)).commRingCatIsoToRingEquiv.symm.injective
  have hmap : MvPolynomial.map (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom (spanDet e φ) = 0 := by
    have h := congrArg (AffineSpace.ΓIso (Fin d × ι) (Spec (CommRingCat.of κ))).hom h0
    rwa [spanDetFunction, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply,
      map_zero] at h
  exact spanDet_ne_zero e hφ
    (MvPolynomial.map_injective _ hinj (by rw [hmap, map_zero]))

/-- **The open `U ⊆ 𝔸^(Fin d × ι)_κ` of `d`-tuples whose images under `φ` span `W`**: the basic
open of the determinant. -/
def spanningOpen (e : Module.Basis (Fin d) κ W) (φ : (ι → κ) →ₗ[κ] W) :
    (tupleSpace κ ι d).Opens :=
  (tupleSpace κ ι d).basicOpen (spanDetFunction e φ)

/-- **The open is nonempty** when `φ` is surjective.  The affine space over a field is reduced,
so a basic open is empty only for a function that is itself zero, and the determinant of a
surjective `φ` is a nonzero polynomial. -/
theorem nonempty_spanningOpen (e : Module.Basis (Fin d) κ W) {φ : (ι → κ) →ₗ[κ] W}
    (hφ : Function.Surjective φ) :
    ((spanningOpen e φ : (tupleSpace κ ι d).Opens) : Set (tupleSpace κ ι d)).Nonempty := by
  by_contra hne
  rw [TopologicalSpace.Opens.not_nonempty_iff_eq_bot, spanningOpen,
    AlgebraicGeometry.basicOpen_eq_bot_iff] at hne
  exact spanDetFunction_ne_zero e hφ hne

/-- **The `κ`-point of `𝔸^(Fin d × ι)_κ` with coordinate tuple `a`.** -/
def tuplePoint (a : Fin d × ι → κ) : Spec (CommRingCat.of κ) ⟶ tupleSpace κ ι d :=
  AffineSpace.homOfVector (𝟙 (Spec (CommRingCat.of κ)))
    (fun q => (Scheme.ΓSpecIso (CommRingCat.of κ)).inv (a q))

/-- The determinant function pulled back along a `κ`-point is the value of the determinant at
the point's tuple. -/
theorem tuplePoint_appTop_spanDetFunction (e : Module.Basis (Fin d) κ W) (φ : (ι → κ) →ₗ[κ] W)
    (a : Fin d × ι → κ) :
    (tuplePoint a).appTop (spanDetFunction e φ) =
      (Scheme.ΓSpecIso (CommRingCat.of κ)).inv (MvPolynomial.eval a (spanDet e φ)) :=
  AffineSpace.homOfVector_appTop_ΓIso_inv_map a (spanDet e φ)

/-- **A `κ`-point of `𝔸^(Fin d × ι)_κ` lies in the open exactly when the images of its tuple
span `W`.** -/
theorem mem_spanningOpen_iff (e : Module.Basis (Fin d) κ W) (φ : (ι → κ) →ₗ[κ] W)
    (a : Fin d × ι → κ) (p : Spec (CommRingCat.of κ)) :
    tuplePoint a p ∈ spanningOpen e φ ↔
      Submodule.span κ (Set.range fun t => φ (Function.curry a t)) = ⊤ := by
  rw [span_eq_top_iff_eval_spanDet_ne_zero e φ a]
  show p ∈ tuplePoint a ⁻¹ᵁ spanningOpen e φ ↔ _
  rw [spanningOpen, Scheme.preimage_basicOpen_top, tuplePoint_appTop_spanDetFunction e φ a]
  refine ⟨fun hmem h0 => ?_, fun hne => ?_⟩
  · rwa [h0, map_zero, Scheme.basicOpen_zero] at hmem
  · rw [Scheme.basicOpen_of_isUnit _
      ((isUnit_iff_ne_zero.mpr hne).map (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom)]
    trivial

/-- **Step 4 of [Stacks, Tag 0FH5]**: the tuples whose images under a surjective `φ` span `W`
form a nonempty open subset of the affine space of tuples, and it contains a `κ`-point whose
tuple spans. -/
theorem exists_mem_spanningOpen_and_span_eq_top (e : Module.Basis (Fin d) κ W)
    {φ : (ι → κ) →ₗ[κ] W} (hφ : Function.Surjective φ) :
    ((spanningOpen e φ : (tupleSpace κ ι d).Opens) : Set (tupleSpace κ ι d)).Nonempty ∧
      ∃ a : Fin d × ι → κ,
        (∀ p : Spec (CommRingCat.of κ), tuplePoint a p ∈ spanningOpen e φ) ∧
          Submodule.span κ (Set.range fun t => φ (Function.curry a t)) = ⊤ := by
  obtain ⟨a, ha⟩ := exists_span_eq_top e hφ
  exact ⟨nonempty_spanningOpen e hφ,
    a, fun p => (mem_spanningOpen_iff e φ a p).2 ha, ha⟩

end Stacks.SpanningTuple

end
