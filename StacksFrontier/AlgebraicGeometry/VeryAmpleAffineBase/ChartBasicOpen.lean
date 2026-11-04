module

public import StacksFrontier.AlgebraicGeometry.ProjGradedModuleQcoh.ChartLocalization

/-!
# Standard opens of a chart of `Proj` as standard opens of `Proj`

On the affine chart `D₊(f) = Spec A₍f₎` of `Proj A` the standard opens are cut out by the
degree-zero fractions `a / f ^ n`. This file identifies the nonvanishing locus, *as an open of
`Proj A`*, of the section of the structure sheaf of `Proj A` over `D₊(f)` attached to such a
fraction: it is `D₊(f) ⊓ D₊(a)`.

## Main results

* `Stacks.ProjChartBasicOpen.SpecMap_awayToSection_awayι`: the open immersion
  `Spec A₍f₎ ⟶ Proj A` precomposed with the spectrum of `A₍f₎ ⟶ Γ(Proj A, D₊(f))` is the
  canonical morphism `Spec Γ(Proj A, D₊(f)) ⟶ Proj A` of the affine open `D₊(f)`.
* `Stacks.ProjChartBasicOpen.fromSpec_preimage_basicOpen_mul`: the inverse image of `D₊(a f)`
  along that canonical morphism is the standard open of the fraction `a / f ^ n`.
* `Stacks.ProjChartBasicOpen.basicOpen_awayToSection_mk`: **the nonvanishing locus in `Proj A` of
  the section attached to `a / f ^ n` is `D₊(f) ⊓ D₊(a)`.**
* `Stacks.ProjChartBasicOpen.basicOpen_appLE_awayToSection_mk`: the same read on a scheme over
  `Proj A`: for `U ≤ α⁻¹(D₊(f))` the inverse image of `a / f ^ n` cuts `U ⊓ α⁻¹(D₊(a))` out of `U`.

## Implementation notes

Every step is taken with inverse images rather than images: `f ''ᵁ U` carries an
`IsOpenImmersion f` instance argument, so rewriting one morphism into another inside it produces
an ill-typed motive, whereas `f ⁻¹ᵁ U` depends on `f` only through its underlying map. The two
opens being compared both lie inside `D₊(f)`, which is the range of the chart, so comparing their
inverse images loses nothing: `AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf`
turns the comparison back into one of the opens themselves.

## References

* [Stacks Project, Tag 01M3](https://stacks.math.columbia.edu/tag/01M3)
* [Stacks Project, Tag 02NP](https://stacks.math.columbia.edu/tag/02NP)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

universe u w

namespace Stacks.ProjChartBasicOpen

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A} {d : ℕ}

/-- **The chart `Spec A₍f₎ ⟶ Proj A` is the canonical morphism of the affine open `D₊(f)`**, up
to the comparison `A₍f₎ ⟶ Γ(Proj A, D₊(f))` of rings. -/
theorem SpecMap_awayToSection_awayι (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    Spec.map (Proj.awayToSection 𝒜 f) ≫ Proj.awayι 𝒜 f hf hd =
      (Proj.isAffineOpen_basicOpen 𝒜 f hf hd).fromSpec := by
  have key : Spec.map (Proj.awayToSection 𝒜 f) ≫ (Proj.basicOpenIsoSpec 𝒜 f hf hd).inv =
      (Proj.isAffineOpen_basicOpen 𝒜 f hf hd).isoSpec.inv := by
    rw [Iso.comp_inv_eq, Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec, ← Category.assoc,
      IsAffineOpen.isoSpec_inv_toSpecΓ, Category.id_comp]
  rw [Proj.awayι, ← Category.assoc, key, IsAffineOpen.isoSpec_inv_ι]

/-- Inverse images along the canonical morphism of the affine open `D₊(f)` are computed by the
chart `Spec A₍f₎ ⟶ Proj A` followed by the spectrum of `A₍f₎ ⟶ Γ(Proj A, D₊(f))`. -/
theorem fromSpec_preimage (hf : f ∈ 𝒜 d) (hd : 0 < d) (W : (AlgebraicGeometry.Proj 𝒜).Opens) :
    (Proj.isAffineOpen_basicOpen 𝒜 f hf hd).fromSpec ⁻¹ᵁ W =
      Spec.map (Proj.awayToSection 𝒜 f) ⁻¹ᵁ (Proj.awayι 𝒜 f hf hd ⁻¹ᵁ W) := by
  rw [← SpecMap_awayToSection_awayι 𝒜 hf hd]
  rfl

/-- **The inverse image of `D₊(a f)` in the affine chart `Spec Γ(Proj A, D₊(f))`** is the
standard open of the degree-zero fraction `a / f ^ n`. -/
theorem fromSpec_preimage_basicOpen_mul (hf : f ∈ 𝒜 d) (hd : 0 < d) (n : ℕ) (a : A)
    (ha : a ∈ 𝒜 (n • d)) (hg : a * f ∈ 𝒜 (n * d + d)) (he : 0 < n * d + d) :
    (Proj.isAffineOpen_basicOpen 𝒜 f hf hd).fromSpec ⁻¹ᵁ Proj.basicOpen 𝒜 (a * f) =
      PrimeSpectrum.basicOpen ((Proj.awayToSection 𝒜 f).hom (Away.mk 𝒜 hf n a ha)) := by
  rw [fromSpec_preimage 𝒜 hf hd, Proj.awayι_preimage_basicOpen 𝒜 hf hd hg he,
    ProjectiveSpectrum.isLocalizationElem_eq_pow 𝒜 hf n a ha hg, SpecMap_preimage_basicOpen,
    map_pow, PrimeSpectrum.basicOpen_pow _ d hd]

/-- **Stacks Tag 02NP's remaining geometric step.** The nonvanishing locus in `Proj A` of the
section of the structure sheaf over `D₊(f)` attached to the degree-zero fraction `a / f ^ n` is
`D₊(f) ⊓ D₊(a)`. -/
theorem basicOpen_awayToSection_mk (hf : f ∈ 𝒜 d) (hd : 0 < d) (n : ℕ) (a : A)
    (ha : a ∈ 𝒜 (n • d)) :
    (AlgebraicGeometry.Proj 𝒜).basicOpen ((Proj.awayToSection 𝒜 f).hom (Away.mk 𝒜 hf n a ha)) =
      Proj.basicOpen 𝒜 f ⊓ Proj.basicOpen 𝒜 a := by
  have hg : a * f ∈ 𝒜 (n * d + d) := by
    simpa [smul_eq_mul] using SetLike.mul_mem_graded ha hf
  have he : 0 < n * d + d := Nat.lt_of_lt_of_le hd (Nat.le_add_left d _)
  have hfg : Proj.basicOpen 𝒜 (a * f) ≤ Proj.basicOpen 𝒜 f :=
    Proj.basicOpen_mono 𝒜 f (a * f) ⟨a, mul_comm a f⟩
  have hrange : (Proj.isAffineOpen_basicOpen 𝒜 f hf hd).fromSpec.opensRange =
      Proj.basicOpen 𝒜 f := IsAffineOpen.opensRange_fromSpec _
  have hpre : (Proj.isAffineOpen_basicOpen 𝒜 f hf hd).fromSpec ⁻¹ᵁ
        ((AlgebraicGeometry.Proj 𝒜).basicOpen
          ((Proj.awayToSection 𝒜 f).hom (Away.mk 𝒜 hf n a ha))) =
      (Proj.isAffineOpen_basicOpen 𝒜 f hf hd).fromSpec ⁻¹ᵁ Proj.basicOpen 𝒜 (a * f) := by
    rw [IsAffineOpen.fromSpec_preimage_basicOpen,
      fromSpec_preimage_basicOpen_mul 𝒜 hf hd n a ha hg he]
  have himage : ∀ V ≤ Proj.basicOpen 𝒜 f,
      (Proj.isAffineOpen_basicOpen 𝒜 f hf hd).fromSpec ''ᵁ
        ((Proj.isAffineOpen_basicOpen 𝒜 f hf hd).fromSpec ⁻¹ᵁ V) = V := fun V hV => by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, hrange]
    exact inf_eq_right.mpr hV
  rw [← himage _ (Scheme.basicOpen_le _ _), hpre, himage _ hfg, Proj.basicOpen_mul, inf_comm]

/-- **The chart overlap of a morphism into `Proj A` is a standard open of the chart.** For
`α : X ⟶ Proj A` and an open `U` of `X` inside `α⁻¹(D₊(f))`, the nonvanishing locus of the
inverse image along `α` of the degree-zero fraction `a / f ^ n` is `U ⊓ α⁻¹(D₊(a))`.

This is the form in which Stacks Tag 02NP's coordinate cut uses
`Stacks.ProjChartBasicOpen.basicOpen_awayToSection_mk`: taking `U = α⁻¹(D₊(y))` for a degree-one
coordinate `y` and `a = y g`, the overlap `α⁻¹(D₊(y)) ⊓ α⁻¹(D₊(g))` is exhibited as a standard
open of the affine chart, cut out by a section that `AlgebraicGeometry.Scheme.preimage_basicOpen`
matches with a standard open of the corresponding chart of projective space. -/
theorem basicOpen_appLE_awayToSection_mk {X : Scheme.{u}}
    (α : X ⟶ AlgebraicGeometry.Proj 𝒜) (hf : f ∈ 𝒜 d) (hd : 0 < d) (n : ℕ) (a : A)
    (ha : a ∈ 𝒜 (n • d)) {U : X.Opens} (hU : U ≤ α ⁻¹ᵁ Proj.basicOpen 𝒜 f) :
    X.basicOpen (α.appLE (Proj.basicOpen 𝒜 f) U hU
        ((Proj.awayToSection 𝒜 f).hom (Away.mk 𝒜 hf n a ha))) =
      U ⊓ α ⁻¹ᵁ Proj.basicOpen 𝒜 a := by
  have hinf : α ⁻¹ᵁ (Proj.basicOpen 𝒜 f ⊓ Proj.basicOpen 𝒜 a) =
      (α ⁻¹ᵁ Proj.basicOpen 𝒜 f) ⊓ (α ⁻¹ᵁ Proj.basicOpen 𝒜 a) :=
    TopologicalSpace.Opens.ext (Set.preimage_inter)
  rw [Scheme.basicOpen_appLE, basicOpen_awayToSection_mk 𝒜 hf hd n a ha, hinf,
    ← inf_assoc, inf_eq_left.mpr hU]

end Stacks.ProjChartBasicOpen

end
