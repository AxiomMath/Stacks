module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.NonAlgebraizableChartLocalization
public import StacksFrontier.AlgebraicGeometry.NormInvertible.TwoChart

/-!
# The modules `L_n` of the non-algebraizable example, on the punctured spectrum of `A/tⁿA`

For `A = k[x,y][[t]]` the two charts of the example are the basic opens `D(x̄)` and `D(ȳ)` of
`Spec(A/tⁿA)`, their union is the part of `Spec(A/tⁿA)` lying over `U = Spec(A) ∖ V(x,y,t)`, and
their overlap is `D(x̄ȳ)`. This file identifies the chart rings `A_r/tⁿA_r` with the rings of
sections of `𝒪` on those basic opens, reads the transition element as a unit of the sections over
the overlap, and glues the two charts along it: the result is the module `L_n`, an invertible
module on the punctured spectrum of `A/tⁿA`. It also computes the kernel of the reduction
`A_r/t^{n+1}A_r → A_r/tⁿA_r` on each chart.

## Main definitions

* `Stacks.Algebraization.NonAlgebraizableExample.levelScheme` — the scheme `Spec(A/tⁿA)`.
* `Stacks.Algebraization.NonAlgebraizableExample.chartOpen` — the basic open `D(r̄)` of it.
* `Stacks.Algebraization.NonAlgebraizableExample.levelOpen` — the union `D(x̄) ∪ D(ȳ)`, the
  punctured spectrum of `A/tⁿA`.
* `Stacks.Algebraization.NonAlgebraizableExample.levelChart` — a chart, as an open of the
  punctured spectrum.
* `Stacks.Algebraization.NonAlgebraizableExample.levelOverlapUnit` — the transition element, as a
  unit of the sections of `𝒪` over the overlap of the two charts.
* `Stacks.Algebraization.NonAlgebraizableExample.levelModule` — the module `L_n`.
* `Stacks.Algebraization.NonAlgebraizableExample.levelToAmbient` and `levelStructureMap` — the
  structure map `Spec(A/tⁿA) ⟶ Spec(A)` and its restriction to the punctured spectra.
* `Stacks.Algebraization.NonAlgebraizableExample.levelModuleOnOpen` — `L_n` as a module on `U`,
  the direct image along the structure map.

## Main results

* `Stacks.Algebraization.NonAlgebraizableExample.chartOpenEquiv` — the chart ring `A_r/tⁿA_r` is
  the ring of sections of `𝒪` on `D(r̄)`.
* `Stacks.Algebraization.NonAlgebraizableExample.coe_levelOpen` — `D(x̄) ∪ D(ȳ)` is the part of
  `Spec(A/tⁿA)` lying over `U`.
* `Stacks.Algebraization.NonAlgebraizableExample.isInvertibleModule_levelModule` — `L_n` is
  invertible.
* `Stacks.Algebraization.NonAlgebraizableExample.ker_chartReduction` — the kernel of
  `A_r/t^{n+1}A_r → A_r/tⁿA_r` is `tⁿ · A_r/t^{n+1}A_r`.
* `Stacks.Algebraization.NonAlgebraizableExample.preimage_U_levelToAmbient` — the punctured
  spectrum of `A/tⁿA` is the preimage of `U` under the structure map, so the structure map
  restricts to one between the punctured spectra.

## References

* [Stacks Project, Tag 0EHE](https://stacks.math.columbia.edu/tag/0EHE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Algebraization.NonAlgebraizableExample

variable (k : Type u) [Field k]

/-- The scheme `Spec(A/tⁿA)`. -/
public abbrev levelScheme (n : ℕ) : Scheme.{u} := Spec (.of (levelRing k n))

/-- The image of `r` in the level ring `A/tⁿA`. -/
public abbrev levelElt (r : AmbientRing k) (n : ℕ) : levelRing k n :=
  Ideal.Quotient.mk ((idealT k) ^ n) r

/-- The basic open `D(r̄)` of `Spec(A/tⁿA)`. -/
public abbrev chartOpen (r : AmbientRing k) (n : ℕ) : (levelScheme k n).Opens :=
  PrimeSpectrum.basicOpen (levelElt k r n)

/-- The level ring `A/tⁿA` acts on the chart ring `A_r/tⁿA_r` through the restriction map. -/
public instance chartAlgebra (r : AmbientRing k) (n : ℕ) :
    Algebra (levelRing k n) (chartRing k r n) := (levelToChart k r n).toAlgebra

/-- The level ring `A/tⁿA` acts on the sections of `𝒪` over the basic open `D(r̄)`. -/
public instance chartOpenAlgebra (r : AmbientRing k) (n : ℕ) :
    Algebra (levelRing k n) Γ(levelScheme k n, chartOpen k r n) := by
  change Algebra (levelRing k n)
    ((Spec.structureSheaf (CommRingCat.of (levelRing k n))).obj.obj _)
  exact StructureSheaf.openAlgebra (CommRingCat.of (levelRing k n)) _

/-- The sections of `𝒪` over the basic open `D(r̄)` are the localization of `A/tⁿA` away from
`r̄`. -/
public instance chartOpenIsLocalization (r : AmbientRing k) (n : ℕ) :
    IsLocalization.Away (levelElt k r n) Γ(levelScheme k n, chartOpen k r n) :=
  StructureSheaf.IsLocalization.to_basicOpen (CommRingCat.of (levelRing k n)) _

/-- The chart ring `A_r/tⁿA_r` is the ring of sections of `𝒪` on the basic open `D(r̄)` of
`Spec(A/tⁿA)`, as `A/tⁿA`-algebras. -/
@[stacks 0EHE "A_r/t^n A_r is the ring of sections of O on D(r) in Spec(A/t^n A)"]
public def chartOpenEquiv (r : AmbientRing k) (n : ℕ) :
    chartRing k r n ≃ₐ[levelRing k n] Γ(levelScheme k n, chartOpen k r n) :=
  haveI : IsLocalization.Away (levelElt k r n) (chartRing k r n) :=
    isLocalization_away_levelToChart k r n
  IsLocalization.algEquiv (Submonoid.powers (levelElt k r n)) _ _

/-- The punctured spectrum of `A/tⁿA`: the union of the two charts `D(x̄)` and `D(ȳ)`. -/
public def levelOpen (n : ℕ) : (levelScheme k n).Opens :=
  chartOpen k (xVar k) n ⊔ chartOpen k (yVar k) n

/-- The union of the two charts is the part of `Spec(A/tⁿA)` lying over `U`, namely the complement
of the vanishing locus of the image of `𝔞 = (x,y,t)`. -/
@[stacks 0EHE "D(x) union D(y) is the part of Spec(A/t^n A) lying over U"]
public theorem coe_levelOpen (n : ℕ) :
    (levelOpen k n : Set (levelScheme k n)) =
      (PrimeSpectrum.zeroLocus
        (((idealXYT k).map (Ideal.Quotient.mk ((idealT k) ^ n)) : Ideal (levelRing k n)) :
          Set (levelRing k n)))ᶜ :=
  (compl_zeroLocus_map_idealXYT k n).symm

/-- The overlap of the two charts is the chart of `xy`. -/
public theorem chartOpen_mul (n : ℕ) :
    chartOpen k (xVar k * yVar k) n = chartOpen k (xVar k) n ⊓ chartOpen k (yVar k) n := by
  rw [chartOpen, levelElt, map_mul, PrimeSpectrum.basicOpen_mul]
  rfl

/-- The chart of `xy` lies in the punctured spectrum of `A/tⁿA`. -/
public theorem chartOpen_mul_le_levelOpen (n : ℕ) :
    chartOpen k (xVar k * yVar k) n ≤ levelOpen k n :=
  (chartOpen_mul k n).le.trans (inf_le_left.trans le_sup_left)

/-- The chart `D(r̄)`, as an open of the punctured spectrum of `A/tⁿA`. -/
public abbrev levelChart (r : AmbientRing k) (n : ℕ) : (levelOpen k n).toScheme.Opens :=
  (levelOpen k n).ι ⁻¹ᵁ chartOpen k r n

/-- The two charts cover the punctured spectrum of `A/tⁿA`. -/
public theorem sup_levelChart (n : ℕ) :
    (⊤ : (levelOpen k n).toScheme.Opens) ≤
      levelChart k (xVar k) n ⊔ levelChart k (yVar k) n := fun z _ ↦ z.2

/-- The overlap of the two charts of the punctured spectrum of `A/tⁿA` is the chart of `xy`. -/
public theorem inf_levelChart (n : ℕ) :
    levelChart k (xVar k) n ⊓ levelChart k (yVar k) n = levelChart k (xVar k * yVar k) n := by
  change (levelOpen k n).ι ⁻¹ᵁ chartOpen k (xVar k) n ⊓
      (levelOpen k n).ι ⁻¹ᵁ chartOpen k (yVar k) n =
    (levelOpen k n).ι ⁻¹ᵁ chartOpen k (xVar k * yVar k) n
  rw [chartOpen_mul]
  rfl

/-- The image in `Spec(A/tⁿA)` of the chart of `xy` of the punctured spectrum is the basic open
`D(x̄ȳ)`. -/
public theorem image_levelChart_mul (n : ℕ) :
    (levelOpen k n).ι ''ᵁ levelChart k (xVar k * yVar k) n =
      chartOpen k (xVar k * yVar k) n := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
    inf_eq_right.mpr (chartOpen_mul_le_levelOpen k n)]

/-- The sections of `𝒪` on the overlap of the two charts of the punctured spectrum of `A/tⁿA`
are the chart ring `A_{xy}/tⁿA_{xy}`. -/
public def levelOverlapRingEquiv (n : ℕ) :
    chartRing k (xVar k * yVar k) n ≃+*
      Γ((levelOpen k n).toScheme, levelChart k (xVar k) n ⊓ levelChart k (yVar k) n) :=
  ((chartOpenEquiv k (xVar k * yVar k) n).toRingEquiv.trans
      ((levelScheme k n).presheaf.mapIso
        (eqToIso (image_levelChart_mul k n)).op).commRingCatIsoToRingEquiv).trans
    ((levelOpen k n).toScheme.presheaf.mapIso
      (eqToIso (inf_levelChart k n)).op).commRingCatIsoToRingEquiv

/-- The transition element, as a unit of the sections of `𝒪` over the overlap of the two charts
of the punctured spectrum of `A/tⁿA`. -/
public def levelOverlapUnit (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (n : ℕ) :
    Γ((levelOpen k n).toScheme, levelChart k (xVar k) n ⊓ levelChart k (yVar k) n)ˣ :=
  Units.map (levelOverlapRingEquiv k n).toRingHom.toMonoidHom
    (isUnit_transitionElement k a φ n).unit

/-- The module `L_n`: the sheaf of modules on the punctured spectrum of `A/tⁿA` glued from the two
charts `D(x̄)` and `D(ȳ)` along the transition element
`u = 1 + t/(xy) + ∑_{m ≥ 2} aₘtᵐ/(xy)^{φ(m)}`. -/
@[stacks 0EHE "the module L_n, glued from A_x/t^n A_x and A_y/t^n A_y along u"]
public def levelModule (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (n : ℕ) :
    (levelOpen k n).toScheme.Modules :=
  (Stacks.SheafOfModules.twoChartCocycle (X := (levelOpen k n).toScheme.toRingedSpace)
    (U₀ := levelChart k (xVar k) n) (U₁ := levelChart k (yVar k) n)
    (levelOverlapUnit k a φ n)).glue

/-- The module `L_n` is an invertible module on the punctured spectrum of `A/tⁿA`. -/
@[stacks 0EHE "L_n is an invertible module on the punctured spectrum of A/t^n A"]
public theorem isInvertibleModule_levelModule (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (n : ℕ) :
    Stacks.Ample.IsInvertibleModule (levelOpen k n).toScheme (levelModule k a φ n) :=
  Stacks.SheafOfModules.isInvertibleModule_glue_twoChartCocycle _ (sup_levelChart k n)

/-- The kernel of the reduction `A_r/t^{n+1}A_r → A_r/tⁿA_r` is `tⁿ·A_r/t^{n+1}A_r`. -/
@[stacks 0EHE "ker(A_r/t^(n+1) A_r -> A_r/t^n A_r) = t^n A_r/t^(n+1) A_r"]
public theorem ker_chartReduction (r : AmbientRing k) (n : ℕ) :
    LinearMap.ker (chartReduction k r n).toLinearMap =
      Ideal.span {algebraMap (AmbientRing k) (Localization.Away r) (tVar k)} ^ n •
        (⊤ : Submodule (Localization.Away r) (chartRing k r (n + 1))) := by
  refine le_antisymm ?_ ?_
  · intro z hz
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [LinearMap.mem_ker] at hz
    have hw : w ∈ Ideal.span
        {(algebraMap (AmbientRing k) (Localization.Away r) (tVar k)) ^ n} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa only [AlgHom.toLinearMap_apply, chartReduction_mk] using hz
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hw
    have hsmul : Ideal.Quotient.mk _ w =
        (algebraMap (AmbientRing k) (Localization.Away r) (tVar k)) ^ n •
          (Ideal.Quotient.mk (Ideal.span
            {(algebraMap (AmbientRing k) (Localization.Away r) (tVar k)) ^ (n + 1)}) c) := by
      rw [hc]; rfl
    rw [hsmul]
    exact Submodule.smul_mem_smul
      (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n) Submodule.mem_top
  · refine Submodule.smul_le.mpr fun a ha m _ ↦ ?_
    rw [Ideal.span_singleton_pow] at ha
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (chartReduction k r n m)
    rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply, map_smul, ← hc]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right c _ ha)

/-! ### The level schemes over the punctured spectrum of `A` -/

/-- The structure map `Spec(A/tⁿA) ⟶ Spec(A)`, induced by the quotient map of `A`. -/
public abbrev levelToAmbient (n : ℕ) :
    levelScheme k n ⟶ Spec (CommRingCat.of (AmbientRing k)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((idealT k) ^ n)))

/-- The punctured spectrum of `A/tⁿA` is the preimage of the punctured spectrum `U` of `A` under
the structure map `Spec(A/tⁿA) ⟶ Spec(A)`. -/
@[stacks 0EHE "the preimage of U in Spec(A/t^n A) is its punctured spectrum"]
public theorem preimage_U_levelToAmbient (n : ℕ) :
    levelToAmbient k n ⁻¹ᵁ (situation k).U = levelOpen k n := by
  refine TopologicalSpace.Opens.ext (Set.ext fun z ↦ ?_)
  rw [coe_levelOpen]
  change (levelToAmbient k n).base z ∈ (PrimeSpectrum.zeroLocus
      ((idealXYT k) : Set (AmbientRing k)))ᶜ ↔ _
  have hz : ((levelToAmbient k n).base z).asIdeal =
      Ideal.comap (Ideal.Quotient.mk ((idealT k) ^ n)) z.asIdeal := rfl
  refine not_congr (Iff.trans (PrimeSpectrum.mem_zeroLocus _ _)
    (Iff.trans ?_ (Iff.symm (PrimeSpectrum.mem_zeroLocus _ _))))
  rw [SetLike.coe_subset_coe, SetLike.coe_subset_coe, hz]
  exact Ideal.map_le_iff_le_comap.symm

/-- The map from the punctured spectrum of `A/tⁿA` to the punctured spectrum `U` of `A`, the
restriction of the structure map to the two opens it carries one into the other. -/
public def levelStructureMap (n : ℕ) :
    (levelOpen k n).toScheme ⟶ (situation k).U.toScheme :=
  (levelToAmbient k n).resLE (situation k).U (levelOpen k n)
    (preimage_U_levelToAmbient k n).ge

/-- The module `L_n` as a module on the punctured spectrum `U` of `A`: its direct image along the
structure map `levelStructureMap`. -/
@[stacks 0EHE "L_n pushed forward to U along Spec(A/t^n A) ∩ U → U"]
public def levelModuleOnOpen (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (n : ℕ) :
    (situation k).U.toScheme.Modules :=
  (Scheme.Modules.pushforward (levelStructureMap k n)).obj (levelModule k a φ n)

end Stacks.Algebraization.NonAlgebraizableExample

end
