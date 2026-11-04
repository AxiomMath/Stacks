module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The chart of `Proj` at a positive-degree element represents an affine functor

For a scheme `X`, a graded ring `𝒜` and a homogeneous element `r` of positive degree, the
morphisms `X ⟶ Proj 𝒜` whose preimage of the basic open `D₊(r)` is all of `X` are in bijection
with the ring homomorphisms from the degree-zero part of the localization of `𝒜` at `r` to
`Γ(X, ⊤)`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.opensHomEquiv`: morphisms to an open subscheme
  are exactly the morphisms to the ambient scheme whose preimage of the open is everything.
* `Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.specHomEquiv`: morphisms to an affine scheme
  are exactly the ring homomorphisms out of its ring of global sections.
* `Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.chartHomEquiv`: the bijection, for a
  positive-degree `r`, between the morphisms `X ⟶ Proj 𝒜` that land in `D₊(r)` and the ring
  homomorphisms out of the degree-zero part of the localization of `𝒜` at `r`.
* `Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.fromOfIsUnit`: the morphism `X ⟶ Proj 𝒜`
  determined by a ring map to global sections that sends one positive-degree element to a unit.

## Main results

* `Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.map_irrelevant_eq_top_of_isUnit`: if a ring map
  sends a single positive-degree element to a unit, the image of the irrelevant ideal generates
  the whole ring.
* `Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.fromOfIsUnit_preimage_basicOpen`: the morphism
  `fromOfIsUnit` lands in the chart at `r`.
* `Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.eq_of_chartHomEquiv_eq` and
  `Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.exists_hom_chartHomEquiv_eq`: uniqueness and
  existence, read off the bijection.

## References

* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace Stacks.AlgebraicGeometry.ProjF1DegreeOneChart

universe u w

variable {X Y : Scheme.{u}}

/-- **Morphisms to an open subscheme are the morphisms to the ambient scheme that land in it.**
The forward map is the factorization through the open immersion, the inverse is composition with
the inclusion. -/
public def opensHomEquiv (U : Y.Opens) :
    {g : X ⟶ Y // g ⁻¹ᵁ U = ⊤} ≃ (X ⟶ U.toScheme) where
  toFun g := IsOpenImmersion.lift U.ι g.1 (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact show y ∈ g.1 ⁻¹ᵁ U by rw [g.2]; trivial)
  invFun h := ⟨h ≫ U.ι, by
    rw [Scheme.Hom.comp_preimage, U.ι_preimage_self]
    simp⟩
  left_inv g := Subtype.ext (IsOpenImmersion.lift_fac _ _ _)
  right_inv h := (cancel_mono U.ι).mp (IsOpenImmersion.lift_fac _ _ _)

/-- **Morphisms to an affine scheme are the ring homomorphisms out of its global sections.**
This is the `Γ`–`Spec` adjunction. -/
@[ega "I 2.2.4"]
public def specHomEquiv (R : CommRingCat.{u}) (X : Scheme.{u}) :
    (X ⟶ Spec R) ≃ (R ⟶ Γ(X, ⊤)) :=
  (ΓSpec.adjunction.homEquiv X (op R)).symm.trans (opEquiv _ _)

variable {σ : Type w} {R : Type u} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **Inverting one positive-degree element already generates the irrelevant ideal.**  If a ring
map `φ` sends a positive-degree element to a unit, the image of the irrelevant ideal under `φ`
generates the whole ring. -/
public theorem map_irrelevant_eq_top_of_isUnit (φ : R →+* Γ(X, ⊤)) {r : R} {d : ℕ}
    (hd : 0 < d) (hr : r ∈ 𝒜 d) (hu : IsUnit (φ r)) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map φ = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hd hr)) hu

/-- **The chart of `Proj 𝒜` at a positive-degree element represents an affine functor.**
A morphism `X ⟶ Proj 𝒜` whose preimage of `D₊(r)` is all of `X` is the same thing as a ring
homomorphism from the degree-zero part of the localization of `𝒜` at `r` to `Γ(X, ⊤)`. -/
public def chartHomEquiv {r : R} {d : ℕ} (hr : r ∈ 𝒜 d) (hd : 0 < d) (X : Scheme.{u}) :
    {g : X ⟶ Proj 𝒜 // g ⁻¹ᵁ Proj.basicOpen 𝒜 r = ⊤} ≃
      (CommRingCat.of (HomogeneousLocalization.Away 𝒜 r) ⟶ Γ(X, ⊤)) :=
  (opensHomEquiv (Proj.basicOpen 𝒜 r)).trans
    (((Iso.refl X).homCongr (Proj.basicOpenIsoSpec 𝒜 r hr hd)).trans
      (specHomEquiv _ X))

/-- **Uniqueness.** Two morphisms landing in the chart at `r` that induce the same homomorphism
out of the `Away` ring are equal. -/
public theorem eq_of_chartHomEquiv_eq {r : R} {d : ℕ} (hr : r ∈ 𝒜 d) (hd : 0 < d)
    {g₁ g₂ : X ⟶ Proj 𝒜} (h₁ : g₁ ⁻¹ᵁ Proj.basicOpen 𝒜 r = ⊤)
    (h₂ : g₂ ⁻¹ᵁ Proj.basicOpen 𝒜 r = ⊤)
    (h : chartHomEquiv 𝒜 hr hd X ⟨g₁, h₁⟩ = chartHomEquiv 𝒜 hr hd X ⟨g₂, h₂⟩) :
    g₁ = g₂ :=
  congrArg Subtype.val ((chartHomEquiv 𝒜 hr hd X).injective h)

/-- **Existence.** Every homomorphism out of the `Away` ring at a positive-degree element is
induced by a morphism to `Proj 𝒜` landing in the chart at that element. -/
public theorem exists_hom_chartHomEquiv_eq {r : R} {d : ℕ} (hr : r ∈ 𝒜 d) (hd : 0 < d)
    (ρ : CommRingCat.of (HomogeneousLocalization.Away 𝒜 r) ⟶ Γ(X, ⊤)) :
    ∃ (g : X ⟶ Proj 𝒜) (hg : g ⁻¹ᵁ Proj.basicOpen 𝒜 r = ⊤),
      chartHomEquiv 𝒜 hr hd X ⟨g, hg⟩ = ρ :=
  ⟨((chartHomEquiv 𝒜 hr hd X).symm ρ).1, ((chartHomEquiv 𝒜 hr hd X).symm ρ).2,
    (chartHomEquiv 𝒜 hr hd X).apply_symm_apply ρ⟩

variable (φ : R →+* Γ(X, ⊤)) {r : R} {d : ℕ}

/-- The morphism to `Proj 𝒜` determined by a ring map to global sections that sends one
positive-degree element to a unit. -/
public def fromOfIsUnit (hd : 0 < d) (hr : r ∈ 𝒜 d) (hu : IsUnit (φ r)) : X ⟶ Proj 𝒜 :=
  Proj.fromOfGlobalSections 𝒜 φ (map_irrelevant_eq_top_of_isUnit 𝒜 φ hd hr hu)

/-- **The morphism `fromOfIsUnit` lands in the chart at `r`**: the preimage of `D₊(r)` is all
of `X`. -/
public theorem fromOfIsUnit_preimage_basicOpen (hd : 0 < d) (hr : r ∈ 𝒜 d)
    (hu : IsUnit (φ r)) :
    fromOfIsUnit 𝒜 φ hd hr hu ⁻¹ᵁ Proj.basicOpen 𝒜 r = ⊤ :=
  (Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 φ _ hd hr).trans
    (Scheme.basicOpen_of_isUnit _ hu)

end Stacks.AlgebraicGeometry.ProjF1DegreeOneChart

end
