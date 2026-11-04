module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Ideal.Height

/-!
# The local ring of the reduced closure of a point, on an affine chart

Let `X` be a scheme, `V₀` an affine open with ring `R = Γ(X, V₀)`, and `x` a point of `V₀` with
prime `𝔭 ⊆ R`. Write `X'` for the reduced closed subscheme of `X` supported on the closure of
`{x}`. This file identifies, for a point `z'` of `X'` whose image `z` lies in `V₀` and has prime
`𝔮 ⊆ R`, the Krull dimension of the local ring `𝒪_{X', z'}` with the height of the image of `𝔮`
in `R ⧸ 𝔭`. In particular the codimension hypothesis `dim(𝒪_{\overline{\{x\}}, z}) ≤ 1` of
[Stacks, Tag 0AWC] is equivalent to `(𝔮.map (Ideal.Quotient.mk 𝔭)).height ≤ 1`.

## Main results

* `ideal_vanishingIdeal_closure_eq_primeIdealOf`: on an affine chart containing `x`, the
  vanishing ideal sheaf of the closure of `{x}` is the prime ideal of `x`.
* `ringKrullDim_stalk_vanishingIdeal_closure`: the dimension of the local ring of that reduced
  closure at a point over `z` is the height of the image of the prime ideal of `z` in `R ⧸ 𝔭`.

## Implementation notes

The ideal sheaf is taken as a variable `I` together with `hI : I = vanishingIdeal ...` rather than
spelled out, so that the long `vanishingIdeal (Closeds.closure {x})` term does not appear inside
every subterm of the proof.

## References

* [Stacks Project, Tag 0AWC](https://stacks.math.columbia.edu/tag/0AWC)
* [Stacks Project, Tag 00KF](https://stacks.math.columbia.edu/tag/00KF)
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.CodimensionOneObstruction

variable {X : Scheme.{u}}

/-- **On an affine chart, the vanishing ideal sheaf of the closure of `{x}` is the prime of
`x`.** For an affine open `V₀` containing `x`, the ideal of `Γ(X, V₀)` given by the vanishing ideal
sheaf of `closure {x}` is the prime ideal of `x`. -/
theorem ideal_vanishingIdeal_closure_eq_primeIdealOf {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀)
    {x : X} (hx : x ∈ V₀) :
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).ideal ⟨V₀, hV₀⟩
      = (hV₀.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have hemb : Topology.IsOpenEmbedding hV₀.fromSpec.base :=
    hV₀.fromSpec.isOpenEmbedding (H := hV₀.isOpenImmersion_fromSpec)
  have hpre : hV₀.fromSpec.base ⁻¹' (Closeds.closure ({x} : Set X) : Set X)
      = PrimeSpectrum.zeroLocus ((hV₀.primeIdealOf ⟨x, hx⟩).asIdeal : Set Γ(X, V₀)) := by
    have h1 : hV₀.fromSpec.base ⁻¹' (Closeds.closure ({x} : Set X) : Set X)
        = closure (hV₀.fromSpec.base ⁻¹' ({x} : Set X)) :=
      hemb.isOpenMap.preimage_closure_eq_closure_preimage hemb.continuous _
    have h2 : hV₀.fromSpec.base ⁻¹' ({x} : Set X) = {hV₀.primeIdealOf ⟨x, hx⟩} := by
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, fun y hy => hemb.injective ?_⟩
      · exact hV₀.fromSpec_primeIdealOf ⟨x, hx⟩
      · rw [hV₀.fromSpec_primeIdealOf ⟨x, hx⟩]
        exact hy
    rw [h1, h2]
    exact PrimeSpectrum.closure_singleton _
  have h3 : PrimeSpectrum.vanishingIdeal
      (PrimeSpectrum.zeroLocus ((hV₀.primeIdealOf ⟨x, hx⟩).asIdeal : Set Γ(X, V₀)))
      = (hV₀.primeIdealOf ⟨x, hx⟩).asIdeal := by
    rw [PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
    exact (hV₀.primeIdealOf ⟨x, hx⟩).isPrime.radical
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
  exact (congrArg PrimeSpectrum.vanishingIdeal hpre).trans h3

/-- **The dimension of the local ring of the reduced closure of `x` at `z`, read on an affine
chart.** Let `V₀` be an affine open containing `x`, let `X'` be the reduced closed subscheme
supported on the closure of `{x}`, and let `z'` be a point of `X'` whose image `z` lies in `V₀`.
Then `dim 𝒪_{X', z'}` is the height of the image of the prime of `z` in `Γ(X, V₀) ⧸ 𝔭`, where `𝔭`
is the prime of `x`. -/
theorem ringKrullDim_stalk_vanishingIdeal_closure {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀)
    {x : X} (hx : x ∈ V₀) {I : X.IdealSheafData}
    (hI : I = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)))
    (z' : I.subscheme) (hz : I.subschemeι z' ∈ V₀) :
    ringKrullDim (I.subscheme.presheaf.stalk z')
      = ((hV₀.primeIdealOf ⟨_, hz⟩).asIdeal.map
          (Ideal.Quotient.mk (hV₀.primeIdealOf ⟨x, hx⟩).asIdeal)).height := by
  set W : I.subscheme.Opens := I.subschemeι ⁻¹ᵁ V₀ with hW
  have hWaff : IsAffineOpen W := hV₀.preimage I.subschemeι
  have hz'W : z' ∈ W := hz
  have hsurj : Function.Surjective (I.subschemeι.app V₀).hom :=
    I.subschemeι_app_surjective ⟨V₀, hV₀⟩
  have hker : RingHom.ker (I.subschemeι.app V₀).hom
      = (hV₀.primeIdealOf ⟨x, hx⟩).asIdeal := by
    rw [I.ker_subschemeι_app ⟨V₀, hV₀⟩, hI]
    exact ideal_vanishingIdeal_closure_eq_primeIdealOf hV₀ hx
  have hvu : W ≤ I.subschemeι ⁻¹ᵁ V₀ := le_rfl
  have happ : I.subschemeι.appLE V₀ W hvu = I.subschemeι.app V₀ :=
    Scheme.Hom.appLE_eq_app _
  have hcomap : (hWaff.primeIdealOf ⟨z', hz'W⟩).asIdeal.comap (I.subschemeι.app V₀).hom
      = (hV₀.primeIdealOf ⟨_, hz⟩).asIdeal := by
    rw [← happ]
    exact congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE V₀ hV₀ W hWaff hvu hz'W)
  have hmap : (hV₀.primeIdealOf ⟨_, hz⟩).asIdeal.map (I.subschemeι.app V₀).hom
      = (hWaff.primeIdealOf ⟨z', hz'W⟩).asIdeal := by
    rw [← hcomap, Ideal.map_comap_of_surjective _ hsurj]
  let ψ : (Γ(X, V₀) ⧸ (hV₀.primeIdealOf ⟨x, hx⟩).asIdeal) →+* Γ(I.subscheme, W) :=
    Ideal.Quotient.lift _ (I.subschemeι.app V₀).hom
      (fun a ha => RingHom.mem_ker.mp (hker.ge ha))
  have hψsurj : Function.Surjective ψ := Ideal.Quotient.lift_surjective_of_surjective _ _ hsurj
  have hψinj : Function.Injective ψ := (Ideal.injective_lift_iff _).mpr hker
  let e : (Γ(X, V₀) ⧸ (hV₀.primeIdealOf ⟨x, hx⟩).asIdeal) ≃+* Γ(I.subscheme, W) :=
    RingEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  have hcomp : (e : (Γ(X, V₀) ⧸ (hV₀.primeIdealOf ⟨x, hx⟩).asIdeal) →+* Γ(I.subscheme, W)).comp
      (Ideal.Quotient.mk (hV₀.primeIdealOf ⟨x, hx⟩).asIdeal) = (I.subschemeι.app V₀).hom :=
    RingHom.ext fun a => rfl
  have hheight : (hWaff.primeIdealOf ⟨z', hz'W⟩).asIdeal.height
      = ((hV₀.primeIdealOf ⟨_, hz⟩).asIdeal.map
          (Ideal.Quotient.mk (hV₀.primeIdealOf ⟨x, hx⟩).asIdeal)).height := by
    rw [← hmap, ← hcomp, ← Ideal.map_map]
    exact RingEquiv.height_map e _
  let := TopCat.Presheaf.algebra_section_stalk I.subscheme.presheaf ⟨z', hz'W⟩
  have := hWaff.isLocalization_stalk ⟨z', hz'W⟩
  have key : ringKrullDim (I.subscheme.presheaf.stalk ↑(⟨z', hz'W⟩ : W))
      = ((hWaff.primeIdealOf ⟨z', hz'W⟩).asIdeal.height : WithBot ℕ∞) :=
    IsLocalization.AtPrime.ringKrullDim_eq_height _ _
  rwa [hheight] at key

end Stacks.AlgebraicGeometry.CodimensionOneObstruction

end
