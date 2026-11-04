module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.CartierProduct
public import StacksFrontier.AlgebraicGeometry.DivisorSum.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartBlowupUniversal
public import StacksFrontier.Homology.Eta.Perfect.NormalizedDeterminantalProduct

/-!
# Two charts on a common affine open, and the normalized centre of a chart

Let `(X, D, M)` be a triple as in Situation 0F8S.  The last assertion of Stacks tag 0GTY glues,
over a quasi-compact open `W ⊆ X`, the *normalized* centres of the charts of a finite cover of
`W`: the ideal `∏_{i ∈ s} f^{q - χ_i(M^•)} I_i(M^•, f)` of
`StacksFrontier.Homology.Eta.Perfect.NormalizedDeterminantalProduct`, which unlike the centre
`∏ᵢ I_i(M^•, f)` of the tag's affine-chart clause does not depend on the chart.

This file supplies the two inputs of that independence — on an affine open lying under the
domains of two charts, their complexes become isomorphic in the derived category and their
equations differ by a unit — and reads the normalized centre off on a chart.

## Main results

* `AffineChart.nonempty_derivedIso_overlap`: the base changes to a common affine open of the
  bounded complexes of two charts are isomorphic in the derived category of that open's
  coordinate ring.  Both represent the restriction of `Lh^*M`, by part (1) of Stacks tag 0F8T,
  and derived sheafification on an affine open is fully faithful.
* `AffineChart.exists_unit_pullbackRingHom_f`: the two equations differ there by a unit, both
  generating the ideal of the pulled-back divisor.
* `AffineChart.normalizedCentre` and `AffineChart.normalizedCentreIdealSheaf`: the normalized
  centre of a chart, as an ideal of `Γ(X, U)` and as an ideal sheaf on `U`.
* `AffineChart.map_normalizedCentre_eq`: **the independence** — two charts have the same
  normalized centre on a common affine open under their domains.
* `AffineChart.normalizedCentreIdealSheaf_eq_mul_pow`: the normalized centre is the centre of
  the tag's affine-chart clause times a power of the ideal of `D ∩ U`.
* `AffineChart.nonempty_overIso_blowUpToBase_normalizedCentreIdealSheaf`: hence, by Stacks tag
  080H part (1), blowing up the chart in the normalized centre is blowing it up in the centre of
  the affine-chart clause.

## Implementation notes

The derived isomorphism is read off
`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.nonempty_derivedIso_pullback` at the
chart that `AffineChart.pullback` produces from the second chart: both charts of the pulled-back
triple then have the same open, and that is exactly the shape that result consumes.

## References

* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0F8T](https://stacks.math.columbia.edu/tag/0F8T)
* [Stacks Project, Tag 080H](https://stacks.math.columbia.edu/tag/080H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect

attribute [local instance 10000] HasDerivedCategory.standard

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart

variable {S : ComplexAndDivisorSituation.{u, d}}

/-- For two affine charts `C`, `D` and an affine open `V` of `Y` lying over both `C.U` and `D.U`
along `h : Y ⟶ X`, the base changes of the complexes of `C` and `D` to `Γ(Y, V)` are isomorphic in
the derived category. -/
theorem nonempty_derivedIso_overlap (C D : AffineChart S) {Y : Scheme.{u}} (h : Y ⟶ S.X)
    (hD : Stacks.Divisors.IsPullbackDefined h S.D) (V : Y.affineOpens)
    (hVC : (V : Y.Opens) ≤ h ⁻¹ᵁ (C.U : S.X.Opens))
    (hVD : (V : Y.Opens) ≤ h ⁻¹ᵁ (D.U : S.X.Opens)) :
    Nonempty (DerivedCategory.Q.obj
        (C.complex.baseChange (C.pullbackRingHom h V hVC).hom).toCochainComplex ≅
      DerivedCategory.Q.obj
        (D.complex.baseChange (D.pullbackRingHom h V hVD).hom).toCochainComplex) :=
  C.nonempty_derivedIso_pullback h hD (D.pullback h hD V hVD) hVC

/-- For two affine charts `C`, `D` and an affine open `V` of `Y` lying over both `C.U` and `D.U`
along `h : Y ⟶ X`, the images of their equations `C.f` and `D.f` in `Γ(Y, V)` differ by a unit. -/
theorem exists_unit_pullbackRingHom_f (C D : AffineChart S) {Y : Scheme.{u}} (h : Y ⟶ S.X)
    (hD : Stacks.Divisors.IsPullbackDefined h S.D) (V : Y.affineOpens)
    (hVC : (V : Y.Opens) ≤ h ⁻¹ᵁ (C.U : S.X.Opens))
    (hVD : (V : Y.Opens) ≤ h ⁻¹ᵁ (D.U : S.X.Opens)) :
    ∃ u : Γ(Y, (V : Y.Opens))ˣ,
      D.pullbackRingHom h V hVD D.f
        = (u : Γ(Y, (V : Y.Opens))) * C.pullbackRingHom h V hVC C.f :=
  exists_unit_mul_of_span_singleton_eq
    (C.isRegular_pullbackRingHom_f h hD V hVC).mem_nonZeroDivisors
    ((D.comap_ideal_eq_span h V hVD).symm.trans (C.comap_ideal_eq_span h V hVC))

/-- The **normalized centre** of an affine chart. -/
def normalizedCentre (C : AffineChart S) (s : Finset ℤ) (q : ℕ) : Ideal Γ(S.X, C.U) :=
  C.complex.normalizedProduct C.f s q

/-- The normalized centre of an affine chart is a finitely generated ideal. -/
theorem normalizedCentre_fg (C : AffineChart S) (s : Finset ℤ) (q : ℕ) :
    (C.normalizedCentre s q).FG :=
  C.complex.normalizedProduct_fg C.f s q

/-- The power `f ^ ∑_{i ∈ s} (q - χ_i + rank_i)` of the chart's equation `f` lies in the
normalized centre. -/
theorem pow_mem_normalizedCentre (C : AffineChart S) (s : Finset ℤ) (q : ℕ) :
    C.f ^ (∑ i ∈ s, (C.complex.normalizedExponent q i + C.complex.rank i))
      ∈ C.normalizedCentre s q :=
  C.complex.pow_mem_normalizedProduct C.f s q

/-- If `s` contains the degrees in which the chart's complex is nonzero, the normalized centre is
`(f ^ ∑_{i ∈ s} (q - χ_i))` times the centre `blowupCentre` of the chart. -/
theorem normalizedCentre_eq_pow_mul_blowupCentre (C : AffineChart S) {s : Finset ℤ}
    (q : ℕ) (hs : C.complex.bounded.toFinset ⊆ s) :
    C.normalizedCentre s q
      = Ideal.span {C.f ^ (∑ i ∈ s, C.complex.normalizedExponent q i)} * C.blowupCentre := by
  rw [normalizedCentre, BoundedComplex.normalizedProduct_eq_pow_mul,
    C.prod_determinantalIdeal_eq_blowupCentre hs]

/-- Two affine charts `C`, `D` have the same normalized centre on an affine open `V` of `Y` lying
over both `C.U` and `D.U` along `h : Y ⟶ X`, provided `q` bounds the tail Euler characteristics of
both complexes on `s`. -/
theorem map_normalizedCentre_eq (C D : AffineChart S) {Y : Scheme.{u}} (h : Y ⟶ S.X)
    (hD : Stacks.Divisors.IsPullbackDefined h S.D) (V : Y.affineOpens)
    (hVC : (V : Y.Opens) ≤ h ⁻¹ᵁ (C.U : S.X.Opens))
    (hVD : (V : Y.Opens) ≤ h ⁻¹ᵁ (D.U : S.X.Opens)) (s : Finset ℤ) (q : ℕ)
    (hqC : ∀ i ∈ s, C.complex.tailEulerCharacteristic i ≤ (q : ℤ))
    (hqD : ∀ i ∈ s, D.complex.tailEulerCharacteristic i ≤ (q : ℤ)) :
    (C.normalizedCentre s q).map (C.pullbackRingHom h V hVC).hom
      = (D.normalizedCentre s q).map (D.pullbackRingHom h V hVD).hom := by
  obtain ⟨u, hu⟩ := C.exists_unit_pullbackRingHom_f D h hD V hVC hVD
  exact BoundedComplex.map_normalizedProduct_eq_of_derived_iso_unit
    (C.pullbackRingHom h V hVC).hom (D.pullbackRingHom h V hVD).hom C.f D.f C.complex D.complex
    u s q (C.isRegular_pullbackRingHom_f h hD V hVC).mem_nonZeroDivisors
    (C.nonempty_derivedIso_overlap D h hD V hVC hVD) hu hqC hqD

/-- The normalized centre of an affine chart, read as an ideal sheaf on the open subscheme `U`. -/
def normalizedCentreIdealSheaf (C : AffineChart S) (s : Finset ℤ) (q : ℕ) :
    (C.U : S.X.Opens).toScheme.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    ((C.normalizedCentre s q).map (C.U : S.X.Opens).topIso.inv.hom)

/-- On the open subscheme `U` of an affine chart, the ideal of `D ∩ U` on global sections is
generated by the chart's equation `f`. -/
theorem ideal_comap_D_top (C : AffineChart S) :
    (S.D.comap (C.U : S.X.Opens).ι).ideal
        ⟨⊤, isAffineOpen_top (C.U : S.X.Opens).toScheme⟩
      = Ideal.span {(C.U : S.X.Opens).topIso.inv.hom C.f} := by
  rw [Stacks.IdealSheaf.ideal_comap_appLE S.D (C.U : S.X.Opens).ι C.U
      ⟨⊤, isAffineOpen_top _⟩ (by simp), Scheme.Opens.ι_appLE_top, C.divisor_ideal,
    Ideal.map_span, Set.image_singleton]

/-- If `s` contains the degrees in which the chart's complex is nonzero, the normalized centre
ideal sheaf on `U` is `blowupCentreIdealSheaf` times the power `∑_{i ∈ s} (q - χ_i)` of the ideal
sheaf of `D ∩ U`. -/
theorem normalizedCentreIdealSheaf_eq_mul_pow (C : AffineChart S) {s : Finset ℤ} (q : ℕ)
    (hs : C.complex.bounded.toFinset ⊆ s) :
    C.normalizedCentreIdealSheaf s q
      = C.blowupCentreIdealSheaf *
        S.D.comap (C.U : S.X.Opens).ι ^ (∑ i ∈ s, C.complex.normalizedExponent q i) := by
  let : IsAffine (C.U : S.X.Opens).toScheme := C.U.2
  have hofTop : ∀ J : Ideal Γ((C.U : S.X.Opens).toScheme, ⊤),
      (Scheme.IdealSheafData.ofIdealTop J).ideal
        ⟨⊤, isAffineOpen_top (C.U : S.X.Opens).toScheme⟩ = J := by
    intro J
    simp only [Scheme.IdealSheafData.ofIdealTop_ideal]
    simp only [homOfLE_refl, CategoryTheory.op_id, CategoryTheory.Functor.map_id]
    rw [CommRingCat.hom_id, Ideal.map_id]
  refine Scheme.IdealSheafData.ext_of_isAffine ?_
  simp only [Scheme.IdealSheafData.ideal_mul, Scheme.IdealSheafData.ideal_pow, Pi.mul_apply,
    Pi.pow_apply]
  rw [normalizedCentreIdealSheaf, blowupCentreIdealSheaf, hofTop, hofTop, C.ideal_comap_D_top,
    Ideal.span_singleton_pow, C.normalizedCentre_eq_pow_mul_blowupCentre q hs, Ideal.map_mul,
    Ideal.map_span, Set.image_singleton, map_pow]
  ring

/-- If `s` contains the degrees in which the chart's complex is nonzero, the blowup of `U` in the
normalized centre is isomorphic over `U` to the blowup of `U` in `blowupCentreIdealSheaf`. -/
theorem nonempty_overIso_blowUpToBase_normalizedCentreIdealSheaf (C : AffineChart S)
    {s : Finset ℤ} (q : ℕ) (hs : C.complex.bounded.toFinset ⊆ s) :
    Nonempty (Over.mk (AlgebraicGeometry.blowUpToBase C.blowupCentreIdealSheaf) ≅
      Over.mk (AlgebraicGeometry.blowUpToBase (C.normalizedCentreIdealSheaf s q))) := by
  rw [C.normalizedCentreIdealSheaf_eq_mul_pow q hs]
  exact AlgebraicGeometry.blowUpProductIso_exists _ _
    (Stacks.Divisors.isEffectiveCartierDivisor_pow
      (Stacks.Divisors.isPullbackDefined_of_flat (C.U : S.X.Opens).ι S.D
        S.isEffectiveCartierDivisor) _)

end AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart

end
