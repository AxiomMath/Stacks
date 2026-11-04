module

public import StacksFrontier.AlgebraicGeometry.ProjQuotientChartIdeal.Basic
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeChart

/-!
# The kernel ideal sheaf of `Proj.map`, read on a standard affine chart

Let `φ : 𝒜 →+*ᵍ ℬ` be a graded ring homomorphism satisfying Mathlib's hypothesis
`ℬ₊ ≤ 𝒜₊.map φ`, so that `AlgebraicGeometry.Proj.map φ hφ : Proj ℬ ⟶ Proj 𝒜` exists, and assume
it is quasi-compact, so that its kernel ideal sheaf `(Proj.map φ hφ).ker` is computed open by
open. For `s ∈ 𝒜 m` with `m > 0` the chart `Spec (A_s)₀ ⟶ Proj 𝒜` of
`AlgebraicGeometry.Proj.awayι` is an open immersion onto `D₊(s)`, and this file identifies the
inverse image of that kernel ideal sheaf on the chart: **it is the kernel of
`HomogeneousLocalization.Away.map φ s`**, as an ideal of `(A_s)₀`, under the canonical
identification of `Γ(Spec (A_s)₀, ⊤)` with `(A_s)₀`.

## Main results

* `Stacks.ProjAwayKernel.map_ΓSpecIso_ideal_comap_awayι`: the ideal of
  `(Proj.map φ hφ).ker.comap (Proj.awayι 𝒜 s hs hm)` on the affine open `⊤`, transported along
  `AlgebraicGeometry.Scheme.ΓSpecIso`, is `RingHom.ker (HomogeneousLocalization.Away.map φ s)`.

## Implementation notes

Three facts compose.

* `Stacks.IdealSheaf.ideal_comap_appLE` computes the ideal of an inverse-image ideal sheaf on a
  pair of affine charts `V ≤ f ⁻¹ᵁ U` as the image of the ideal upstairs under
  `AlgebraicGeometry.Scheme.Hom.appLE`. Here `U = D₊(s)`, affine by
  `AlgebraicGeometry.Proj.isAffineOpen_basicOpen`, and `V = ⊤`, with
  `Stacks.AlgebraicGeometry.ProjChartSections.awayι_preimage_basicOpen_self` supplying
  `⊤ ≤ awayι ⁻¹ᵁ D₊(s)`.
* `AlgebraicGeometry.Scheme.Hom.ker_apply` turns the ideal sheaf on the affine open `D₊(s)` into
  the ring-theoretic kernel of the map on sections — this is the one place quasi-compactness is
  spent.
* `Stacks.ProjQuotientChartIdeal.awayToSection_mem_ker_app_projMap_iff` identifies that kernel,
  elementwise through `AlgebraicGeometry.Proj.awayToSection`, with the kernel of
  `HomogeneousLocalization.Away.map φ s`.

What glues them is that the composite
`appLE D₊(s) ⊤ ≫ (Scheme.ΓSpecIso _).hom : Γ(Proj 𝒜, D₊(s)) ⟶ (A_s)₀` is inverse to
`AlgebraicGeometry.Proj.awayToSection`; one half of that is
`Stacks.AlgebraicGeometry.ProjChartSections.awayToSection_comp_awayι_appLE`, and the other half
follows because `Proj.awayToSection` is an isomorphism for `s` homogeneous of positive degree
(`Stacks.ProjQuotientChartIdeal.isIso_awayToSection`). The transport of the kernel along a
*bijective* ring map is then done by hand rather than through `Ideal.map_comap_of_surjective`,
since both inclusions are one line from the two round-trip identities.

The helper `Stacks.ProjAwayKernel.map_eq_ker_of_comp_eq_id` isolates that transport: it takes an
arbitrary section `χ` of `Proj.awayToSection` and does not mention `appLE` at all, which keeps
the chart bookkeeping and the ideal bookkeeping in separate proofs.

## Not done here

Nothing is said about the *generators* of this kernel, nor about its behaviour under the change
of chart `D₊(s) ⊇ D₊(s * t)`; the statement is one chart at a time. Nothing is said either about
when `(Proj.map φ hφ).ker` is the ideal sheaf of a closed subscheme — the quasi-compactness
hypothesis is assumed, not derived, and the surjectivity of `Away.map φ s` (which would make the
chart a closed immersion) is not discussed. No Stacks tag is claimed: this is the chart reading
of a kernel ideal sheaf, a step inside Tag 0801's reduction rather than an assertion of the
Stacks project.
-/

@[expose] public noncomputable section

open CategoryTheory HomogeneousLocalization
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjChartSections

universe u

namespace Stacks.ProjAwayKernel

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- **Transporting the chart kernel of `AlgebraicGeometry.Proj.map` along a section of
`AlgebraicGeometry.Proj.awayToSection`.** If `χ : Γ(Proj 𝒜, D₊(s)) ⟶ (A_s)₀` satisfies
`Proj.awayToSection 𝒜 s ≫ χ = 𝟙`, then, `Proj.awayToSection 𝒜 s` being an isomorphism, `χ` is its
inverse, and the image under `χ` of the kernel of `Proj.map φ hφ` on sections over `D₊(s)` is the
kernel of `HomogeneousLocalization.Away.map φ s`.

Stated for an arbitrary such `χ` so that the ideal-theoretic transport is proved once, with no
mention of the chart morphism; the chart morphism supplies `χ` in
`Stacks.ProjAwayKernel.map_ΓSpecIso_ideal_comap_awayι`. -/
theorem map_eq_ker_of_comp_eq_id (φ : 𝒜 →+*ᵍ ℬ)
    (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)
    {m : ℕ} {s : A} (hs : s ∈ 𝒜 m) (hm : 0 < m)
    (χ : Γ(Proj 𝒜, Proj.basicOpen 𝒜 s) ⟶ CommRingCat.of (Away 𝒜 s))
    (hχ : Proj.awayToSection 𝒜 s ≫ χ = 𝟙 _) :
    Ideal.map χ.hom (RingHom.ker ((Proj.map φ hφ).app (Proj.basicOpen 𝒜 s)).hom) =
      RingHom.ker (Away.map φ s) := by
  have hiso : IsIso (Proj.awayToSection 𝒜 s) := ProjQuotientChartIdeal.isIso_awayToSection hs hm
  have hχ' := IsIso.eq_inv_of_hom_inv_id hχ
  have hleft (z : Away 𝒜 s) : χ.hom ((Proj.awayToSection 𝒜 s).hom z) = z := by simp [hχ']
  have hright (y : Γ(Proj 𝒜, Proj.basicOpen 𝒜 s)) :
      (Proj.awayToSection 𝒜 s).hom (χ.hom y) = y := by simp [hχ']
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun y hy => ?_) fun z hz => ?_
  · refine Ideal.mem_comap.2 ?_
    refine (ProjQuotientChartIdeal.awayToSection_mem_ker_app_projMap_iff φ hφ hs hm
      (χ.hom y)).1 ?_
    rw [hright y]
    exact hy
  · have hmem := Ideal.mem_map_of_mem χ.hom
      ((ProjQuotientChartIdeal.awayToSection_mem_ker_app_projMap_iff φ hφ hs hm z).2 hz)
    rwa [hleft z] at hmem

/-- **The kernel ideal sheaf of `AlgebraicGeometry.Proj.map`, pulled back to a standard affine
chart of `Proj 𝒜`.** For `s ∈ 𝒜 m` with `m > 0`, the chart `Spec (A_s)₀ ⟶ Proj 𝒜` is an open
immersion onto `D₊(s)`, and the inverse image along it of the kernel ideal sheaf of a
quasi-compact `Proj.map φ hφ` has, on the affine open `⊤`, the ideal corresponding under
`AlgebraicGeometry.Scheme.ΓSpecIso` to `RingHom.ker (HomogeneousLocalization.Away.map φ s)`.

This is the chart statement
`Stacks.ProjQuotientChartIdeal.awayToSection_mem_ker_app_projMap_iff` carried from sections over
`D₊(s)` to the ideal sheaf pulled back along `AlgebraicGeometry.Proj.awayι`. -/
theorem map_ΓSpecIso_ideal_comap_awayι (φ : 𝒜 →+*ᵍ ℬ)
    (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)
    [QuasiCompact (Proj.map φ hφ)] {m : ℕ} {s : A} (hs : s ∈ 𝒜 m) (hm : 0 < m) :
    Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (Away 𝒜 s))).hom.hom
        (((Proj.map φ hφ).ker.comap (Proj.awayι 𝒜 s hs hm)).ideal
          ⟨⊤, isAffineOpen_top _⟩) =
      RingHom.ker (Away.map φ s) := by
  have hle : (⊤ : (Spec (CommRingCat.of (Away 𝒜 s))).Opens) ≤
      Proj.awayι 𝒜 s hs hm ⁻¹ᵁ Proj.basicOpen 𝒜 s :=
    (awayι_preimage_basicOpen_self 𝒜 hs hm).ge
  rw [Stacks.IdealSheaf.ideal_comap_appLE (Proj.map φ hφ).ker (Proj.awayι 𝒜 s hs hm)
      ⟨Proj.basicOpen 𝒜 s, Proj.isAffineOpen_basicOpen 𝒜 s hs hm⟩
      ⟨⊤, isAffineOpen_top _⟩ hle,
    Scheme.Hom.ker_apply, Ideal.map_map, ← CommRingCat.hom_comp]
  refine map_eq_ker_of_comp_eq_id φ hφ hs hm _ ?_
  rw [← Category.assoc, awayToSection_comp_awayι_appLE 𝒜 hs hm, Iso.inv_hom_id]

end Stacks.ProjAwayKernel

end
