/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# The nilradical of a local ring cut out by a reduction of finite presentation

Let `i : Z ⟶ X` be a surjective closed immersion from a reduced scheme (for instance the
reduction of `X`).  If `i` is of finite presentation over an affine open `U ∋ x`, then the
nilradical of `𝒪_{X, x}` is a finitely generated ideal: on `U = Spec A` the closed immersion is
`Spec (A ⧸ I)` with `I` finitely generated, `I` is the nilradical of `A` (it is contained in every
prime since `i` is surjective, and contains every nilpotent since `Z` is reduced), and the
nilradical of a localization is the extension of the nilradical.

## Main results

* `AlgebraicGeometry.ker_appLE_preimage_eq_nilradical`.
* `AlgebraicGeometry.fg_nilradical_stalk_of_locallyOfFinitePresentation`.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- For a surjective morphism `i : Z ⟶ X` from a reduced scheme and a quasi-compact open `U`, the
kernel of `Γ(X, U) → Γ(Z, i⁻¹ U)` is the nilradical of `Γ(X, U)`. -/
theorem ker_appLE_preimage_eq_nilradical {X Z : Scheme.{u}} (i : Z ⟶ X) [IsReduced Z]
    [Surjective i] {U : X.Opens} (hU : IsCompact (U : Set X)) :
    RingHom.ker (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom = nilradical Γ(X, U) := by
  refine le_antisymm (fun a ha => mem_nilradical.mpr ?_) (fun a ha => ?_)
  · rw [Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hU]
    refine eq_bot_iff.mpr fun y hy => ?_
    obtain ⟨z, rfl⟩ := i.surjective y
    have hz : z ∈ i ⁻¹ᵁ X.basicOpen a := hy
    rw [Scheme.preimage_basicOpen, Scheme.Hom.app_eq_appLE] at hz
    change z ∈ Z.basicOpen ((i.appLE U (i ⁻¹ᵁ U) le_rfl).hom a) at hz
    rwa [RingHom.mem_ker.mp ha, Scheme.basicOpen_zero] at hz
  · exact RingHom.mem_ker.mpr (IsReduced.eq_zero _ ((mem_nilradical.mp ha).map _))

/-- If a surjective closed immersion `i : Z ⟶ X` from a reduced scheme is of finite presentation
over an affine open `U`, then the nilradical of the local ring of `X` at every point of `U` is
finitely generated. -/
theorem fg_nilradical_stalk_of_locallyOfFinitePresentation {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsReduced Z] [Surjective i] {U : X.Opens} (hU : IsAffineOpen U)
    [LocallyOfFinitePresentation (i ∣_ U)] {x : X} (hx : x ∈ U) :
    (nilradical (X.presheaf.stalk x)).FG := by
  let φ := i.appLE U (i ⁻¹ᵁ U) le_rfl
  -- `φ` is of finite presentation
  have hfp : φ.hom.FinitePresentation := by
    have : IsAffine U := hU
    have : IsAffine (i ⁻¹ᵁ U) := hU.preimage i
    have h2 : ((i ∣_ U).appLE ⊤ ⊤ (by simp)).hom.FinitePresentation :=
      HasRingHomProperty.appLE @LocallyOfFinitePresentation (i ∣_ U) ‹_›
        ⟨⊤, isAffineOpen_top _⟩ ⟨⊤, isAffineOpen_top _⟩ (by simp)
    rw [morphismRestrict_appLE i U ⊤ ⊤ (by simp)] at h2
    exact (Scheme.Hom.appLE_congr _ _ (by simp) (by simp)
      (fun f => f.hom.FinitePresentation)).mp h2
  have hsurj : Function.Surjective φ.hom := by
    simpa only [Scheme.Hom.app_eq_appLE] using i.app_surjective U hU
  -- its kernel is finitely generated, and equal to the nilradical
  have hker : (RingHom.ker φ.hom).FG := by
    let := φ.hom.toAlgebra
    have : Algebra.FinitePresentation Γ(X, U) Γ(Z, i ⁻¹ᵁ U) := hfp
    exact Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId _ _) hsurj
  -- the local ring at `x` is a localization of `Γ(X, U)`
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  have hmap : (nilradical Γ(X, U)).map (algebraMap Γ(X, U) (X.presheaf.stalk x)) =
      nilradical (X.presheaf.stalk x) := by
    simpa [nilradical] using IsLocalization.map_radical (S := X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (⊥ : Ideal Γ(X, U))
  rw [← hmap, ← ker_appLE_preimage_eq_nilradical i hU.isCompact]
  exact hker.map _

end AlgebraicGeometry

end
