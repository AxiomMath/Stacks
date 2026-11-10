module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPrime
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleImageData

/-!
# The prime of an étale chart at a point: functoriality and the affine case

`AlgebraicGeometry.Space.chartPrimeAt` is the prime ideal of the ring of an étale chart cut out by
a point of its scheme. This file records how it behaves along the morphism of schemes of a diagram
of étale charts, and that on an affine chart it is the prime of `Spec Γ` corresponding to the
point: every prime of the ring arises from exactly one point, and inclusion of primes is
specialization of points.

## Main results

* `AlgebraicGeometry.Space.comap_chartPrimeAt`: the pullback of the prime at `x` along the ring map
  of a chart diagram is the prime at the image of `x`.
* `AlgebraicGeometry.Space.chartPrimeAt_eq_primeIdealOf`: on an affine chart the prime at `u` is
  `IsAffineOpen.primeIdealOf` of the whole chart at `u`.
* `AlgebraicGeometry.Space.bijective_chartPrimeAt`: on an affine chart every prime is the prime at
  exactly one point.
* `AlgebraicGeometry.Space.chartPrimeAt_le_chartPrime_iff`: on an affine chart the prime at `u` is
  contained in the prime at `v` exactly when `u` specializes to `v`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The pullback of the prime of a chart at a point, along the ring map of a diagram of étale
charts, is the prime of the target chart at the image point: the germ maps intertwine the ring
map with the local map of stalks, and a local map pulls the maximal ideal back to the maximal
ideal. -/
theorem comap_chartPrimeAt {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (x : chartScheme d.U) :
    (chartPrimeAt B S hS X.2 d.U x).comap (chartDiagramPullback B S hS f d).hom =
      chartPrimeAt B S hS Y.2 d.V (((BigFppfOver.toScheme B S hS).map d.g).base x) := by
  set r := (BigFppfOver.toScheme B S hS).map d.g
  ext a
  have h : ((chartScheme d.U).presheaf.germ ⊤ x trivial).hom
        ((chartDiagramPullback B S hS f d).hom a) =
      (r.stalkMap x).hom (((chartScheme d.V).presheaf.germ ⊤ (r.base x) trivial).hom a) :=
    (Scheme.Hom.germ_stalkMap_apply r ⊤ x trivial a).symm
  change ((chartScheme d.U).presheaf.germ ⊤ x trivial).hom
      ((chartDiagramPullback B S hS f d).hom a) ∈ IsLocalRing.maximalIdeal _ ↔
    ((chartScheme d.V).presheaf.germ ⊤ (r.base x) trivial).hom a ∈ IsLocalRing.maximalIdeal _
  rw [h, ← Ideal.mem_comap, IsLocalRing.maximalIdeal_comap]

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- On an affine chart, the prime at `u` is the prime of `Spec Γ` corresponding to `u`. -/
theorem chartPrimeAt_eq_primeIdealOf (W : SmallEtale B S hS X) (hW : IsAffine (chartScheme W))
    (u : chartScheme W) :
    chartPrimeAt B S hS hX W u =
      ((isAffineOpen_top (chartScheme W)).primeIdealOf ⟨u, trivial⟩).asIdeal := by
  rw [IsAffineOpen.primeIdealOf_eq_map_closedPoint]
  rfl

/-- The homeomorphism of an affine chart scheme with the spectrum of its ring of functions. -/
private noncomputable def chartIsoSpecHomeo (W : SmallEtale B S hS X)
    (hW : IsAffine (chartScheme W)) :
    ((⊤ : (chartScheme W).Opens) : Type u) ≃ₜ PrimeSpectrum Γ(chartScheme W, ⊤) :=
  TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (isAffineOpen_top (chartScheme W)).isoSpec)

/-- On an affine chart, the prime at `u` is the prime of `u` under `chartIsoSpecHomeo`. -/
private theorem chartPrimeAt_eq_asIdeal_chartIsoSpecHomeo (W : SmallEtale B S hS X)
    (hW : IsAffine (chartScheme W)) (u : chartScheme W) :
    chartPrimeAt B S hS hX W u = (chartIsoSpecHomeo B S hS W hW ⟨u, trivial⟩).asIdeal :=
  chartPrimeAt_eq_primeIdealOf B S hS hX W hW u

/-- On an affine chart every prime of the ring of the chart is the prime at exactly one point. -/
theorem bijective_chartPrimeAt (W : SmallEtale B S hS X) (hW : IsAffine (chartScheme W)) :
    Function.Bijective (fun u : chartScheme W =>
      (⟨chartPrimeAt B S hS hX W u, inferInstance⟩ : PrimeSpectrum (chartRing B S hS X hX W))) := by
  refine ⟨fun u v h => ?_, fun P => ?_⟩
  · have h' := congrArg PrimeSpectrum.asIdeal h
    simp only [chartPrimeAt_eq_asIdeal_chartIsoSpecHomeo B S hS hX W hW] at h'
    exact congrArg Subtype.val ((chartIsoSpecHomeo B S hS W hW).injective (PrimeSpectrum.ext h'))
  · obtain ⟨w, hw⟩ := (chartIsoSpecHomeo B S hS W hW).surjective
      (⟨P.asIdeal, P.2⟩ : PrimeSpectrum Γ(chartScheme W, ⊤))
    exact ⟨w.1, PrimeSpectrum.ext <| by
      rw [← congrArg PrimeSpectrum.asIdeal hw]
      exact chartPrimeAt_eq_asIdeal_chartIsoSpecHomeo B S hS hX W hW w.1⟩

/-- On an affine chart, the prime at `u` is contained in the prime at `v` exactly when `u`
specializes to `v`. -/
theorem chartPrimeAt_le_chartPrime_iff (W : SmallEtale B S hS X) (hW : IsAffine (chartScheme W))
    (u v : chartScheme W) :
    chartPrimeAt B S hS hX W u ≤ chartPrimeAt B S hS hX W v ↔ u ⤳ v := by
  rw [chartPrimeAt_eq_asIdeal_chartIsoSpecHomeo B S hS hX W hW,
    chartPrimeAt_eq_asIdeal_chartIsoSpecHomeo B S hS hX W hW v]
  exact (PrimeSpectrum.le_iff_specializes _ _).trans <|
    ((chartIsoSpecHomeo B S hS W hW).isInducing.specializes_iff).trans
    (Topology.IsInducing.subtypeVal.specializes_iff (x := (⟨u, trivial⟩ :
      ((⊤ : (chartScheme W).Opens) : Type u))) (y := ⟨v, trivial⟩)).symm

end AlgebraicGeometry.Space

end
