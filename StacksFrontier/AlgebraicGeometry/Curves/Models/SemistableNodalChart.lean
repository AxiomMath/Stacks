module

public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.NodalEtaleLocalStructure
public import StacksFrontier.AlgebraicGeometry.F6Rank136.AtWorstNodalRelativeDimensionOne
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution
public import StacksFrontier.RingTheory.Etale.PermanenceOfProperties

/-!
# Étale local charts of a nodal curve over a discrete valuation ring

Let `R` be a discrete valuation ring and let `f : X ⟶ Spec R` be at-worst-nodal of relative
dimension one. Near a point `x` of the special fibre the family is, étale locally on source and
target, one of the two standard models

`R'[u, v]/(uv)`  or  `R'[u, v]/(uv - π ^ n)`

over an étale extension `R ⊆ R'` of discrete valuation rings with uniformizer `π`. This file
carries out that normalisation, starting from the étale local structure in chart form over an
*arbitrary* affine étale base, which is what the general étale local structure theorem for nodal
families supplies.

Two things have to be arranged, and they are the whole content of the file. First the affine
étale base `Spec B` of the chart has to be shrunk to a discrete valuation ring: `B` is étale over
`R`, hence has finite spectrum and regular local rings of dimension one above the maximal ideal
of `R`, so the local ring of `B` at the image of the chosen point is a discrete valuation ring,
and it is a localization of `B` away from a single element, hence again étale over `R` and an
extension of `R` in the sense of a local injection of discrete valuation rings. Second the
parameter of the chart has to be normalised: in a discrete valuation ring a nonzero element is a
unit times a power of a uniformizer, and rescaling the first coordinate by that unit carries the
chart `R'[u, v]/(uv - εh)` isomorphically onto `R'[u, v]/(uv - h)`.

## Main definitions

* `Stacks.Models.nodalChartMap` — the map of nodal charts `A[x, y]/(xy - h) → B[x, y]/(xy - ρ h)`
  induced by a ring map `ρ : A → B` of the bases.

## Main results

* `Stacks.Models.isPushout_nodalChartMap` and
  `Stacks.Models.isPullback_specMap_nodalChartMap` — a nodal chart base changes to a nodal chart:
  the square of bases and charts is a pushout of rings, so the square of spectra is cartesian.
* `Stacks.Models.exists_pow_irreducible_nodalChartRing_algEquiv` — over a discrete valuation ring
  every nodal chart is isomorphic to one whose parameter is zero or a power of a uniformizer.
* `Stacks.Models.exists_isDiscreteValuationRing_localizationAtPrime_of_etale` — a prime of an
  étale algebra over a discrete valuation ring lying over the maximal ideal has local ring a
  discrete valuation ring, étale over the base and an extension of it.
* `Stacks.Models.exists_etale_nodalChart_pow_uniformizer` — **Tag 0CDD**, granted the étale local
  structure in chart form.

## Implementation notes

The chart form of the étale local structure is taken as the hypothesis
`Stacks.NodalEtaleLocalStructure.NodalChartNeighbourhood f x`. The étale local structure theorem
for nodal families, [Stacks, Tag 0CBY], *is* proved in this repository —
`Stacks.NodalEtaleLocalStructure.nonempty_standardNodalDiagram_of_isAtWorstNodal` in
`StacksFrontier.AlgebraicGeometry.Curves.NodalEtaleLocalStructureAssembly`, with no hypothesis
beyond the tag's own — but in the tag's own *diagram* form
`Stacks.NodalEtaleLocalStructure.StandardNodalDiagram`, whose base `V` is an arbitrary étale
scheme over `S` rather than an affine one carrying a parameter. The chart form is therefore not
available as it stands: it asks for `V` to be shrunk to an affine open and for the local model
to be read off `Stacks.NodalEtaleLocalStructure.chartIsoOfIsPullback`, and that step has not
been taken. Accordingly the main theorem of this file carries the chart form as an explicit
hypothesis rather than deriving it, and the at-worst-nodal hypothesis of the tag, which is
consumed entirely by that input, appears in the statement but is not used.

The base of the chart arrives as a bare morphism of affine schemes `Spec B ⟶ Spec R`; its
`R`-algebra structure is recovered from the full faithfulness of `Spec` on affines through
`AlgebraicGeometry.Spec.preimage`.

The chart form is the common input of *both* branches of the source argument, because at a point
where the family is smooth over the base the chart is the one with parameter `1`, that is the
standard open `R[u, v]/(uv - 1)` of the affine line, which is the case `n = 0` of the second
model. So the smooth branch is not a separate conclusion but a separate way of producing the
hypothesis `hCBY`, and what is missing for it is exactly that production. Two steps are needed
and neither is available here. A morphism smooth at a point is étale-locally an affine space over
the base of *some* dimension `d`; that is the étale affine-space chart, and it is proved in this
repository. Forcing `d = 1` from the relative dimension of the family is not: it needs the
comparison of the rank of the sheaf of relative differentials with the dimension of the fibre and
the behaviour of fibre dimension along a composition, neither of which is set up here in a form
that applies to the chart. And the identification of the standard open of the affine line with
the nodal chart of parameter `1`, together with the translation `u ↦ u + 1` that moves the chosen
point into that standard open, is also absent.

## References

* [Stacks Project, Tag 0CDD](https://stacks.math.columbia.edu/tag/0CDD)
* [Stacks Project, Tag 0CBY](https://stacks.math.columbia.edu/tag/0CBY)
* [Stacks Project, Tag 0AP2](https://stacks.math.columbia.edu/tag/0AP2)
* [Stacks Project, Tag 09E4](https://stacks.math.columbia.edu/tag/09E4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks
  Stacks.NodalEtaleLocalStructure

universe u

namespace Stacks.Models

/-! ### Rescaling a coordinate of a nodal chart -/

section Scale

variable {R : Type u} [CommRing R]

/-- The endomorphism of `R[x, y]` scaling the first coordinate by an element `c` of `R`. -/
private def scaleFirstCoordHom (c : R) :
    MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  MvPolynomial.aeval fun i ↦
    if i = 0 then MvPolynomial.C c * MvPolynomial.X 0 else MvPolynomial.X i

@[simp] private theorem scaleFirstCoordHom_X_zero (c : R) :
    scaleFirstCoordHom c (MvPolynomial.X 0) = MvPolynomial.C c * MvPolynomial.X 0 := by
  simp [scaleFirstCoordHom]

@[simp] private theorem scaleFirstCoordHom_X_one (c : R) :
    scaleFirstCoordHom c (MvPolynomial.X 1) = MvPolynomial.X 1 := by
  simp [scaleFirstCoordHom]

@[simp] private theorem scaleFirstCoordHom_C (c r : R) :
    scaleFirstCoordHom c (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [scaleFirstCoordHom]

/-- Rescaling the first coordinate by `a` and by `b` with `b * a = 1` compose to the identity. -/
private theorem scaleFirstCoordHom_comp_of_mul_eq_one (a b : R) (hab : b * a = 1) :
    (scaleFirstCoordHom a).comp (scaleFirstCoordHom b) = AlgHom.id R (MvPolynomial (Fin 2) R) := by
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  fin_cases i
  · change scaleFirstCoordHom a (scaleFirstCoordHom b (MvPolynomial.X 0)) = MvPolynomial.X 0
    rw [scaleFirstCoordHom_X_zero, map_mul, scaleFirstCoordHom_C,
      scaleFirstCoordHom_X_zero, ← mul_assoc, ← MvPolynomial.C_mul, hab, map_one, one_mul]
  · change scaleFirstCoordHom a (scaleFirstCoordHom b (MvPolynomial.X 1)) = MvPolynomial.X 1
    rw [scaleFirstCoordHom_X_one, scaleFirstCoordHom_X_one]

/-- Rescaling the first coordinate by a unit is an automorphism of `R[x, y]`. -/
private def scaleFirstCoord (ε : Rˣ) :
    MvPolynomial (Fin 2) R ≃ₐ[R] MvPolynomial (Fin 2) R :=
  AlgEquiv.ofAlgHom (scaleFirstCoordHom (ε : R)) (scaleFirstCoordHom ((ε⁻¹ : Rˣ) : R))
    (scaleFirstCoordHom_comp_of_mul_eq_one _ _ ε.inv_mul)
    (scaleFirstCoordHom_comp_of_mul_eq_one _ _ ε.mul_inv)

/-- Rescaling the first coordinate by `c` carries the nodal equation with parameter `c * a` to
`c` times the nodal equation with parameter `a`. -/
private theorem scaleFirstCoordHom_nodalEquation (c a : R) :
    scaleFirstCoordHom c (nodalEquation R (c * a)) =
      MvPolynomial.C c * nodalEquation R a := by
  rw [nodalEquation_def, nodalEquation_def, map_sub, map_mul, scaleFirstCoordHom_X_zero,
    scaleFirstCoordHom_X_one, scaleFirstCoordHom_C, MvPolynomial.C_mul]
  ring

/-- Rescaling the first coordinate by a unit `ε` identifies the nodal chart with parameter
`ε * a` with the nodal chart with parameter `a`. -/
private def nodalChartRingScaleUnit (ε : Rˣ) (a : R) :
    nodalChartRing R ((ε : R) * a) ≃ₐ[R] nodalChartRing R a :=
  Ideal.quotientEquivAlg _ _ (scaleFirstCoord ε) <| by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {nodalEquation R a} =
      Ideal.span {scaleFirstCoordHom (ε : R) (nodalEquation R ((ε : R) * a))}
    rw [scaleFirstCoordHom_nodalEquation]
    exact (Ideal.span_singleton_mul_left_unit
      (RingHom.isUnit_map MvPolynomial.C ε.isUnit) (nodalEquation R a)).symm

end Scale

/-- **Normalisation of the parameter of a nodal chart over a discrete valuation ring.** Every
nodal chart over a discrete valuation ring is isomorphic, as an algebra over that ring, to one
whose parameter is either zero or a power of a uniformizer. -/
public theorem exists_pow_irreducible_nodalChartRing_algEquiv {R : Type u} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] (h : R) :
    ∃ h' : R, (h' = 0 ∨ ∃ (π : R) (n : ℕ), Irreducible π ∧ h' = π ^ n) ∧
      Nonempty (nodalChartRing R h ≃ₐ[R] nodalChartRing R h') := by
  by_cases hh : h = 0
  · subst hh
    exact ⟨0, Or.inl rfl, ⟨AlgEquiv.refl⟩⟩
  · obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    obtain ⟨n, ε, hε⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hh hπ
    refine ⟨π ^ n, Or.inr ⟨π, n, hπ, rfl⟩, ⟨?_⟩⟩
    rw [hε]
    exact nodalChartRingScaleUnit ε (π ^ n)

/-! ### Base change of a nodal chart -/

section BaseChange

variable {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B) (h : A)

/-- The map of nodal charts `A[x, y]/(xy - h) → B[x, y]/(xy - ρ h)` induced by a ring map
`ρ : A → B` of the bases: it sends each coordinate to the coordinate of the same index. -/
public def nodalChartMap : nodalChartRing A h →+* nodalChartRing B (ρ h) :=
  chartLift h ((algebraMap B (nodalChartRing B (ρ h))).comp ρ) (nodalGen B (ρ h))
    (by simpa using nodalGen_zero_mul_nodalGen_one (R := B) (ρ h))

@[simp] public theorem nodalChartMap_nodalGen (i : Fin 2) :
    nodalChartMap ρ h (nodalGen A h i) = nodalGen B (ρ h) i :=
  chartLift_nodalGen h _ _ _ i

@[simp] public theorem nodalChartMap_algebraMap (a : A) :
    nodalChartMap ρ h (algebraMap A (nodalChartRing A h) a) =
      algebraMap B (nodalChartRing B (ρ h)) (ρ a) :=
  chartLift_algebraMap h _ _ _ a

section Cocone

variable (s : PushoutCocone (CommRingCat.ofHom (algebraMap A (nodalChartRing A h)))
  (CommRingCat.ofHom ρ))

/-- The commutativity of a cocone over the base square, read on elements of `A`. -/
private theorem cocone_algebraMap (a : A) :
    s.inl.hom (algebraMap A (nodalChartRing A h) a) = s.inr.hom (ρ a) := by
  have hc := congrArg (fun φ : CommRingCat.of A ⟶ s.pt => φ.hom a) s.condition
  simpa using hc

/-- The images of the two coordinates of the chart under a cocone over the base square. -/
private def coconeGens : Fin 2 → s.pt :=
  ![s.inl.hom (nodalGen A h 0), s.inl.hom (nodalGen A h 1)]

private theorem coconeGens_apply (i : Fin 2) :
    coconeGens ρ h s i = s.inl.hom (nodalGen A h i) := by
  fin_cases i <;> rfl

/-- The two images multiply to the image of the parameter, by the defining relation of the
chart and the commutativity of the cocone. -/
private theorem coconeGens_mul :
    coconeGens ρ h s 0 * coconeGens ρ h s 1 = s.inr.hom (ρ h) := by
  rw [coconeGens_apply, coconeGens_apply, ← map_mul, nodalGen_zero_mul_nodalGen_one]
  exact cocone_algebraMap ρ h s h

/-- The map out of the base-changed chart determined by a cocone over the base square. -/
private def coconeDesc : CommRingCat.of (nodalChartRing B (ρ h)) ⟶ s.pt :=
  CommRingCat.ofHom (chartLift (ρ h) s.inr.hom (coconeGens ρ h s) (coconeGens_mul ρ h s))

private theorem coconeDesc_comp_nodalChartMap :
    CommRingCat.ofHom (nodalChartMap ρ h) ≫ coconeDesc ρ h s = s.inl := by
  refine CommRingCat.hom_ext ?_
  rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  refine nodalChartRing_ringHom_ext (fun a => ?_) (fun i => ?_)
  · change chartLift (ρ h) s.inr.hom (coconeGens ρ h s) (coconeGens_mul ρ h s)
        (nodalChartMap ρ h (algebraMap A (nodalChartRing A h) a)) = _
    rw [nodalChartMap_algebraMap, chartLift_algebraMap]
    exact (cocone_algebraMap ρ h s a).symm
  · change chartLift (ρ h) s.inr.hom (coconeGens ρ h s) (coconeGens_mul ρ h s)
        (nodalChartMap ρ h (nodalGen A h i)) = _
    rw [nodalChartMap_nodalGen, chartLift_nodalGen, coconeGens_apply]

private theorem coconeDesc_comp_algebraMap :
    CommRingCat.ofHom (algebraMap B (nodalChartRing B (ρ h))) ≫ coconeDesc ρ h s = s.inr := by
  refine CommRingCat.hom_ext ?_
  rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  exact RingHom.ext fun b =>
    chartLift_algebraMap (ρ h) s.inr.hom (coconeGens ρ h s) (coconeGens_mul ρ h s) b

private theorem coconeDesc_uniq (m : CommRingCat.of (nodalChartRing B (ρ h)) ⟶ s.pt)
    (hl : CommRingCat.ofHom (nodalChartMap ρ h) ≫ m = s.inl)
    (hr : CommRingCat.ofHom (algebraMap B (nodalChartRing B (ρ h))) ≫ m = s.inr) :
    m = coconeDesc ρ h s := by
  have hl' := congrArg CommRingCat.Hom.hom hl
  have hr' := congrArg CommRingCat.Hom.hom hr
  rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at hl' hr'
  refine CommRingCat.hom_ext (nodalChartRing_ringHom_ext (fun b => ?_) (fun i => ?_))
  · have hb := RingHom.congr_fun hr' b
    simpa [coconeDesc] using hb
  · have hi := RingHom.congr_fun hl' (nodalGen A h i)
    rw [RingHom.comp_apply, nodalChartMap_nodalGen] at hi
    rw [hi]
    change _ = chartLift (ρ h) s.inr.hom (coconeGens ρ h s) (coconeGens_mul ρ h s)
      (nodalGen B (ρ h) i)
    rw [chartLift_nodalGen, coconeGens_apply]

end Cocone

/-- **A nodal chart base changes to a nodal chart.** The square of rings
`A → A[x, y]/(xy - h)`, `A → B`, `A[x, y]/(xy - h) → B[x, y]/(xy - ρ h)`,
`B → B[x, y]/(xy - ρ h)` is a pushout: a ring map out of a nodal chart is a ring map on the base
together with a pair of elements whose product is the parameter. -/
public theorem isPushout_nodalChartMap :
    IsPushout (CommRingCat.ofHom (algebraMap A (nodalChartRing A h)))
      (CommRingCat.ofHom ρ) (CommRingCat.ofHom (nodalChartMap ρ h))
      (CommRingCat.ofHom (algebraMap B (nodalChartRing B (ρ h)))) where
  w := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 1
    exact RingHom.ext fun a => nodalChartMap_algebraMap ρ h a
  isColimit' :=
    ⟨PushoutCocone.IsColimit.mk _ (fun s => coconeDesc ρ h s)
      (fun s => coconeDesc_comp_nodalChartMap ρ h s)
      (fun s => coconeDesc_comp_algebraMap ρ h s)
      (fun s m hl hr => coconeDesc_uniq ρ h s m hl hr)⟩

/-- **The square of spectra of a base change of nodal charts is cartesian.** -/
public theorem isPullback_specMap_nodalChartMap :
    IsPullback (Spec.map (CommRingCat.ofHom (nodalChartMap ρ h)))
      (Spec.map (CommRingCat.ofHom (algebraMap B (nodalChartRing B (ρ h)))))
      (Spec.map (CommRingCat.ofHom (algebraMap A (nodalChartRing A h))))
      (Spec.map (CommRingCat.ofHom ρ)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_nodalChartMap ρ h)

end BaseChange

/-! ### Shrinking an étale neighbourhood of a discrete valuation ring -/

/-- In a ring with finite spectrum the local ring at a prime is a localization away from a single
element: take the product of elements witnessing, for each prime not contained in the given one,
that it is not contained in it. -/
private theorem exists_isLocalizationAway_atPrime_of_finite_primeSpectrum
    (A : Type*) [CommRing A] [Finite (PrimeSpectrum A)] (p : Ideal A) [p.IsPrime] :
    ∃ f ∉ p, IsLocalization.Away f (Localization.AtPrime p) := by
  classical
  let T := {q : PrimeSpectrum A // ¬ q.asIdeal ≤ p}
  have hex (q : T) : ∃ x : A, x ∈ q.1.asIdeal ∧ x ∉ p :=
    SetLike.not_le_iff_exists.mp q.2
  choose x hx hxp using hex
  have := Fintype.ofFinite T
  let f := ∏ q : T, x q
  have hfp : f ∉ p := by
    simpa only [f, Ideal.IsPrime.prod_mem_iff, Finset.mem_univ, true_and, not_exists]
      using hxp
  have hpow : ∀ s ∈ p.primeCompl, ∃ m ∈ Submonoid.powers f, s ∣ m := by
    intro s hs
    have hf : f ∈ (Ideal.span ({s} : Set A)).radical := by
      rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
      intro q hq
      have hnot : ¬ q ≤ p := fun hle ↦
        hs (hle (hq.1 (Ideal.subset_span (Set.mem_singleton s))))
      let q' : T := ⟨⟨q, hq.2⟩, hnot⟩
      exact q.mem_of_dvd (Finset.dvd_prod_of_mem x (Finset.mem_univ q')) (hx q')
    obtain ⟨n, hn⟩ := hf
    exact ⟨f ^ n, ⟨n, rfl⟩, Ideal.mem_span_singleton.mp hn⟩
  exact ⟨f, hfp, (IsLocalization.iff_of_le_of_exists_dvd
    (Submonoid.powers f) p.primeCompl (Submonoid.powers_le.mpr hfp) hpow).mpr inferInstance⟩

/-- **The local ring of an étale algebra over a discrete valuation ring above the maximal ideal
is a discrete valuation ring.** It is étale over the base, and the inclusion is an extension of
discrete valuation rings in the sense of Tag 09E4; moreover it is étale over the algebra itself,
being a localization away from a single element.

This is the geometric content of Tag 0AP2 in the form needed to shrink an affine étale
neighbourhood of a discrete valuation ring to a discrete valuation ring. -/
public theorem exists_isDiscreteValuationRing_localizationAtPrime_of_etale
    {R B : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing B] [Algebra R B] [Algebra.Etale R B]
    (q : PrimeSpectrum B)
    (hq : PrimeSpectrum.comap (algebraMap R B) q = IsLocalRing.closedPoint R) :
    ∃ (_ : IsDomain (Localization.AtPrime q.asIdeal))
      (_ : IsDiscreteValuationRing (Localization.AtPrime q.asIdeal)),
      IsDiscreteValuationRing.IsExtension R (Localization.AtPrime q.asIdeal) ∧
        Algebra.Etale R (Localization.AtPrime q.asIdeal) ∧
        Algebra.Etale B (Localization.AtPrime q.asIdeal) := by
  have : Finite (PrimeSpectrum R) := by
    apply Finite.of_injective (fun y : PrimeSpectrum R ↦ y = ⊥)
    intro y z hyz
    rcases IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top y with hy | hy <;>
      rcases IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top z with hz | hz <;>
      simp_all
  have : Finite (PrimeSpectrum B) := Algebra.QuasiFinite.finite_primeSpectrum R B
  obtain ⟨s, hs, hloc⟩ :=
    exists_isLocalizationAway_atPrime_of_finite_primeSpectrum B q.asIdeal
  let L := Localization.AtPrime q.asIdeal
  have : IsLocalization.Away s L := hloc
  have : Algebra.Etale B L := Algebra.Etale.of_isLocalizationAway s
  have : Algebra.Etale R L := Algebra.Etale.comp R B L
  have hpoint : PrimeSpectrum.comap (algebraMap R L) (IsLocalRing.closedPoint L) =
      IsLocalRing.closedPoint R := by
    rw [IsScalarTower.algebraMap_eq R B L, PrimeSpectrum.comap_comp_apply]
    have hclosed : PrimeSpectrum.comap (algebraMap B L) (IsLocalRing.closedPoint L) = q :=
      PrimeSpectrum.ext (IsLocalization.AtPrime.under_maximalIdeal L q.asIdeal)
    rw [hclosed]
    exact hq
  have : IsLocalHom (algebraMap R L) :=
    (IsLocalRing.isLocalHom_iff_comap_closedPoint _).mpr hpoint
  have heq : IsLocalRing.maximalIdeal R = Ideal.comap (algebraMap R B) q.asIdeal :=
    (congrArg PrimeSpectrum.asIdeal hq).symm
  have : q.asIdeal.LiesOver (IsLocalRing.maximalIdeal R) := ⟨heq⟩
  have : IsRegularLocalRing L :=
    (isRegularLocalRing_localization_iff_of_etale (IsLocalRing.maximalIdeal R)
      q.asIdeal).mp inferInstance
  have hpne : IsLocalRing.maximalIdeal R ≠ ⊥ := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    intro hp
    have hm : π ∈ IsLocalRing.maximalIdeal R := hπ.not_isUnit
    rw [hp] at hm
    exact hπ.ne_zero hm
  have : IsDiscreteValuationRing (Localization.AtPrime (IsLocalRing.maximalIdeal R)) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hpne _
  have hdim : ringKrullDim L = 1 := by
    rw [← RingHom.Etale.ringKrullDim_localization_atPrime_eq (f := algebraMap R B)
      (RingHom.etale_algebraMap.mpr inferInstance) (IsLocalRing.maximalIdeal R)
      q.asIdeal heq]
    exact IsDiscreteValuationRing.ringKrullDim_eq_one _
  obtain ⟨hd, hv⟩ := ((isDiscreteValuationRing_tfae L).out 3 1).mp
    (show IsRegularLocalRing L ∧ ringKrullDim L = 1 from ⟨inferInstance, hdim⟩)
  have : IsDomain L := hd
  have : IsDiscreteValuationRing L := hv
  have : Module.FaithfullyFlat R L := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact ⟨hd, hv, { toFaithfulSMul := inferInstance, toIsLocalHom := inferInstance },
    inferInstance, inferInstance⟩

/-! ### Tag 0CDD -/

/-- An isomorphism of algebras induces, on spectra, a morphism over the base. -/
private theorem specMap_algEquiv_comp_algebraMap {R A B : Type u} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) :
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  exact congrArg CommRingCat.ofHom e.toAlgHom.comp_algebraMap

/-- **Stacks 0CDD.** Let `R` be a discrete valuation ring, let `f : X ⟶ Spec R` be at-worst-nodal
of relative dimension one, and let `x` be a point of the special fibre. Then there is an étale
extension `R ⊆ R'` of discrete valuation rings, a scheme `U` with étale morphisms `U ⟶ X` and
`U ⟶ Spec A` over `Spec R'`, and a point `x'` of `U` above `x`, with

`A = R'[u, v]/(uv)`  or  `A = R'[u, v]/(uv - π ^ n)`

for a uniformizer `π` of `R'` and `n ≥ 0`; the two cases are the vanishing and the nonvanishing
of the parameter `h`, which is a power of a uniformizer in the second case.

The étale local structure in chart form over an arbitrary affine étale base is carried as the
hypothesis `hCBY`; everything else — shrinking that base to a discrete valuation ring and
normalising the parameter — is proved here. -/
@[stacks 0CDD "the TRANSLATION STEP ONLY, with the etale local structure carried as a \
hypothesis.  CARRIED HYPOTHESES, each inherited and not discharged here: \
`hCBY : Stacks.NodalEtaleLocalStructure.NodalChartNeighbourhood f x` is the EXISTENCE half of \
[Stacks, Tag 0CBY] -- an etale neighbourhood `U` of `x`, an affine etale neighbourhood `Spec B` \
of its image, a parameter `h` of `B` and an etale `U -> Spec B[x,y]/(xy-h)` over `Spec B` -- \
which is the CHART form of the tag and is still not proved in this repository.  [Stacks, Tag \
0CBY] ITSELF IS PROVED: \
`Stacks.NodalEtaleLocalStructure.nonempty_standardNodalDiagram_of_isAtWorstNodal` at \
StacksFrontier/AlgebraicGeometry/Curves/NodalEtaleLocalStructureAssembly.lean proves the tag's own \
statement, with no hypothesis beyond the tag's, in the DIAGRAM form \
`Stacks.NodalEtaleLocalStructure.StandardNodalDiagram` -- etale `U -> X`, etale `V -> S`, etale \
`U -> W` and a cartesian square presenting `W` as a base change of the standard nodal family.  \
What separates that from `hCBY` is not the existence but the PACKAGING: the chart form asks for \
the base `V` to be AFFINE, say `Spec B`, and for an actual parameter `h` in `B`, so passing \
from the diagram to the chart means shrinking `V` to an affine open and reading the local model \
off `Stacks.NodalEtaleLocalStructure.chartIsoOfIsPullback`, which is a step nobody has taken.  \
`_hf : IsAtWorstNodalOfRelativeDimensionOne f` is the tag's \
own hypothesis; it appears in the statement for faithfulness but is NOT consumed, because the \
whole use of nodality in the source proof is to produce `hCBY`.  WHAT IS PROVED HERE, and is \
exactly what the source calls the translation: the affine etale base `Spec B` is shrunk to a \
discrete valuation ring `R'` with `R` -> `R'` etale and `R` ⊆ `R'` an extension of discrete \
valuation rings in the sense of [Stacks, Tag 09E4] \
(`exists_isDiscreteValuationRing_localizationAtPrime_of_etale`, the route of [Stacks, Tag \
0AP2]); the chart is base changed along `B -> R'` and is again a nodal chart \
(`isPullback_specMap_nodalChartMap`); and the resulting parameter is normalised to `0` or a \
power of a uniformizer by rescaling a coordinate by a unit \
(`exists_pow_irreducible_nodalChartRing_algEquiv`).  The SMOOTH case of the source proof, which \
routes through [Stacks, Tag 054L] instead of 0CBY, is not covered by this statement: see the \
module documentation"]
public theorem exists_etale_nodalChart_pow_uniformizer
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (_hf : IsAtWorstNodalOfRelativeDimensionOne f)
    (x : X) (hx : f.base x = IsLocalRing.closedPoint R)
    (hCBY : NodalChartNeighbourhood f x) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R')
      (_ : IsDiscreteValuationRing R') (_ : Algebra R R')
      (_ : IsDiscreteValuationRing.IsExtension R R') (_ : Algebra.Etale R R') (h : R'),
      (h = 0 ∨ ∃ (π : R') (n : ℕ), Irreducible π ∧ h = π ^ n) ∧
        ∃ (U : Scheme.{u}) (g : U ⟶ X) (j : U ⟶ Spec (.of (nodalChartRing R' h))) (x' : U),
          Etale g ∧ Etale j ∧ g.base x' = x ∧
            g ≫ f = j ≫
              Spec.map (CommRingCat.ofHom (algebraMap R' (nodalChartRing R' h))) ≫
                Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
  classical
  have := hCBY.etale_toSource
  have := hCBY.etale_toBase
  have := hCBY.etale_toChart
  -- The base of the chart, with the `R`-algebra structure recovered from `Spec.preimage`.
  let φ : R →+* hCBY.base := (Spec.preimage hCBY.toBase).hom
  let : Algebra R hCBY.base := φ.toAlgebra
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap R hCBY.base)) = hCBY.toBase :=
    Spec.map_preimage _
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap R hCBY.base))) := by
    rw [hφ]; infer_instance
  have : Algebra.Etale R hCBY.base := RingHom.etale_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Etale)).mp inferInstance)
  -- The structure morphism of the chart, and the image of the chosen point in its base.
  let w₀ : Spec (.of (nodalChartRing hCBY.base hCBY.param)) ⟶ Spec (.of hCBY.base) :=
    Spec.map (CommRingCat.ofHom
      (algebraMap hCBY.base (nodalChartRing hCBY.base hCBY.param)))
  have hcomm : hCBY.toSource ≫ f = hCBY.toChart ≫ w₀ ≫ hCBY.toBase := hCBY.comm
  let z₀ := hCBY.toChart hCBY.pt
  let q : PrimeSpectrum hCBY.base := w₀ z₀
  have hbase : hCBY.toBase (w₀ z₀) = f x := by
    conv_rhs => rw [← hCBY.pt_mem]
    exact (congrArg (fun k : hCBY.U ⟶ Spec (.of R) => k hCBY.pt) hcomm).symm
  have hq : PrimeSpectrum.comap (algebraMap R hCBY.base) q = IsLocalRing.closedPoint R := by
    change (Spec.map (CommRingCat.ofHom (algebraMap R hCBY.base))) q = _
    rw [hφ]
    change hCBY.toBase (w₀ z₀) = _
    rw [hbase, hx]
  -- Shrink the base to a discrete valuation ring.
  obtain ⟨hd, hv, hext, hetR, hetB⟩ :=
    exists_isDiscreteValuationRing_localizationAtPrime_of_etale q hq
  let R₁ := Localization.AtPrime q.asIdeal
  have : IsDomain R₁ := hd
  have : IsDiscreteValuationRing R₁ := hv
  have : IsDiscreteValuationRing.IsExtension R R₁ := hext
  have : Algebra.Etale R R₁ := hetR
  have : Algebra.Etale hCBY.base R₁ := hetB
  let ρ : hCBY.base →+* R₁ := algebraMap hCBY.base R₁
  let i : Spec (.of R₁) ⟶ Spec (.of hCBY.base) := Spec.map (CommRingCat.ofHom ρ)
  have : Etale i := HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hetB)
  -- The base-changed chart, with its cartesian square over the old one.
  have hsq : IsPullback (Spec.map (CommRingCat.ofHom (nodalChartMap ρ hCBY.param)))
      (Spec.map (CommRingCat.ofHom (algebraMap R₁ (nodalChartRing R₁ (ρ hCBY.param)))))
      w₀ i :=
    isPullback_specMap_nodalChartMap ρ hCBY.param
  -- The closed point of the shrunk base sits over the image of the chosen point.
  have hi : i (IsLocalRing.closedPoint R₁) = q :=
    PrimeSpectrum.ext (IsLocalization.AtPrime.under_maximalIdeal R₁ q.asIdeal)
  -- A point of the base-changed chart over `z₀`, and then a point of the new neighbourhood.
  obtain ⟨y, hy₁, hy₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := w₀) (g := i) z₀ (IsLocalRing.closedPoint R₁) hi.symm
  obtain ⟨u, hu₁, hu₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := hCBY.toChart) (g := pullback.fst w₀ i) hCBY.pt y hy₁.symm
  -- Normalise the parameter.
  obtain ⟨h', hh', ⟨e⟩⟩ := exists_pow_irreducible_nodalChartRing_algEquiv (ρ hCBY.param)
  have : IsIso (CommRingCat.ofHom e.symm.toRingHom) :=
    inferInstanceAs (IsIso e.symm.toRingEquiv.toCommRingCatIso.hom)
  have : IsIso (Spec.map (CommRingCat.ofHom e.symm.toRingHom)) := inferInstance
  refine ⟨R₁, inferInstance, hd, hv, inferInstance, hext, hetR, h', hh',
    pullback hCBY.toChart (pullback.fst w₀ i),
    pullback.fst hCBY.toChart (pullback.fst w₀ i) ≫ hCBY.toSource,
    pullback.snd hCBY.toChart (pullback.fst w₀ i) ≫ hsq.isoPullback.inv ≫
      Spec.map (CommRingCat.ofHom e.symm.toRingHom),
    u, inferInstance, inferInstance, ?_, ?_⟩
  · change hCBY.toSource (pullback.fst hCBY.toChart (pullback.fst w₀ i) u) = x
    rw [hu₁]
    exact hCBY.pt_mem
  · -- The two composites to `Spec R` agree.
    have hw : hsq.isoPullback.inv ≫
        Spec.map (CommRingCat.ofHom (algebraMap R₁ (nodalChartRing R₁ (ρ hCBY.param)))) =
        pullback.snd w₀ i := by
      rw [Iso.inv_comp_eq]
      exact hsq.isoPullback_hom_snd.symm
    have hχ : (hsq.isoPullback.inv ≫ Spec.map (CommRingCat.ofHom e.symm.toRingHom)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R₁ (nodalChartRing R₁ h'))) =
        pullback.snd w₀ i := by
      rw [Category.assoc, specMap_algEquiv_comp_algebraMap e.symm]
      exact hw
    have hiφ : i ≫ hCBY.toBase = Spec.map (CommRingCat.ofHom (algebraMap R R₁)) := by
      rw [← hφ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hcond1 : pullback.fst hCBY.toChart (pullback.fst w₀ i) ≫ hCBY.toChart =
        pullback.snd hCBY.toChart (pullback.fst w₀ i) ≫ pullback.fst w₀ i :=
      pullback.condition
    have hcond2 : pullback.fst w₀ i ≫ w₀ = pullback.snd w₀ i ≫ i := pullback.condition
    calc (pullback.fst hCBY.toChart (pullback.fst w₀ i) ≫ hCBY.toSource) ≫ f
        = (pullback.fst hCBY.toChart (pullback.fst w₀ i) ≫ hCBY.toChart) ≫
            w₀ ≫ hCBY.toBase := by rw [Category.assoc, hcomm, Category.assoc]
      _ = pullback.snd hCBY.toChart (pullback.fst w₀ i) ≫
            (pullback.fst w₀ i ≫ w₀) ≫ hCBY.toBase := by
          rw [hcond1]; simp only [Category.assoc]
      _ = pullback.snd hCBY.toChart (pullback.fst w₀ i) ≫
            pullback.snd w₀ i ≫ i ≫ hCBY.toBase := by
          rw [hcond2]; simp only [Category.assoc]
      _ = pullback.snd hCBY.toChart (pullback.fst w₀ i) ≫
            pullback.snd w₀ i ≫ Spec.map (CommRingCat.ofHom (algebraMap R R₁)) := by
          rw [hiφ]
      _ = _ := by
          rw [← hχ]
          simp only [Category.assoc]

end Stacks.Models

end
