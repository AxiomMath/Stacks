module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.ChartStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.Colength.ChartData
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.Colength.ChartOverlapRange
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChain
public import StacksFrontier.RingTheory.Length.MaximalIdealPower

/-!
# The colength drop of the residual ideal sheaf on the blowup of a regular local surface

Let `(A, 𝔪)` be a two-dimensional regular local ring with `𝔪 = (x, y)`, let `X` be the blowup of
`Spec A` at its closed point with exceptional divisor `E`, and let `L` be an ideal of `A` with
`𝔪 ^ n ⊆ L ⊆ 𝔪`. Suppose `L·𝒪_X = 𝒪_X(-dE)·J'` with `d` maximal and positive, as produced by
`Stacks.ResolutionOfSurfaces.CartierDescent.exists_residual_isEffectiveCartier_support`. This
file proves the inequality of [Stacks, Tag 0AGT]:

`∑_{z ∈ T} ℓ_{𝒪_z}(𝒪_z / J'_z) < ℓ_A(A / L)`

for every finite set `T` of points of `X` containing the support of `J'`.

## The argument

The two standard charts `Spec A[𝔪/x]` and `Spec A[𝔪/y]` cover `X`, so every point of the support
of `J'` is a prime of one of the two chart algebras above the residual ideal there, and its stalk
colength is the colength of the residual ideal at that prime
(`Stacks.ResolutionOfSurfaces.CartierDescent.length_stalk_quotient_chart_eq`). Points of `T` off
the support contribute nothing. Taking for the first chart *all* the primes above its residual
ideal, and for the second only those at which the chart element `x / y` is not invertible — which
by `Stacks.ResolutionOfSurfaces.CartierDescent.mem_opensRange_blowUpAffineChart_of_notMem` is all
that is needed to account for the points lying off the first chart — the sum over `T` is at most
the sum of the two chart sums. That sum is then bounded by
`Stacks.ResolutionOfSurfaces.CartierDescent.sum_length_affineBlowup_lt`.

The source's argument deduces the same inequality from `H¹(X, L·𝒪_X) = 0` together with
`Γ(X, 𝒪_X) = A`; neither is used here. Their place is taken by the two elementary identities
`B + C = D` and `B ∩ C = A` for the two chart subalgebras of the fraction field, which is what
the gluing in `CartierDescent.Colength.Realization` runs on.

## Main results

* `Stacks.ResolutionOfSurfaces.CartierDescent.sum_length_stalk_quotient_lt`: the colength drop.
* `Stacks.ResolutionOfSurfaces.CartierDescent.finite_setOf_le_of_finite_isPrime` and
  `Stacks.ResolutionOfSurfaces.CartierDescent.isArtinian_quotient_of_pow_maximalIdeal_le`: the two
  bookkeeping facts the drop needs about the chart data — finiteness of the family of primes above
  the residual ideal, and finiteness of the colength of `L`.

## Implementation notes

The reduction of the sum over `T` to the two chart sums is isolated as a lemma about an arbitrary
scheme and two injections into it, so that the only scheme-theoretic inputs to it are the
vanishing of the colength off the support
(`Stacks.ResolutionOfSurfaces.length_quotient_stalk_eq_zero_of_notMem_support`) and the covering
property, both supplied as hypotheses. All the blowup geometry therefore happens in the main
theorem, where it is one application each of
`Stacks.ResolutionOfSurfaces.CartierDescent.mem_opensRange_chart_or`,
`Stacks.ResolutionOfSurfaces.CartierDescent.mem_support_chart_iff` and the chart-overlap lemma.

The base ring of the charts is `Γ(Spec A, ⊤)`, not `A`, since that is where the sections of the
centre live; the colength of `L` is transported to it at the very end by
`Module.quotient_length_eq_of_ringEquiv`, as in the sibling file `CartierDescent.ResidualSupport`.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
* [Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS)
* [Stacks Project, Tag 0AGB](https://stacks.math.columbia.edu/tag/0AGB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CommRingCat

universe u

namespace Stacks.ResolutionOfSurfaces.CartierDescent

/-- **Splitting a sum of stalk colengths between two charts.** Let `J'` be a quasi-coherent ideal
sheaf on a scheme `X`, let `T` be a finite set of points containing its support, and let two
injections `bx : Bq → X`, `by' : Cq → X` be given together with finite sets `Sx`, `Sy` whose
images cover the support. Then the sum of the stalk colengths over `T` is at most the sum of the
stalk colengths over `Sx` plus the sum over `Sy`.

Points of `T` off the support contribute nothing, and the remaining ones are distributed between
the two families; double counting can only increase the right-hand side, so the two families need
not be disjoint. -/
private theorem sum_stalk_colength_le_of_two_families {X : Scheme.{u}} (J' : X.IdealSheafData)
    (T : Finset X) {Bq Cq : Type u} (bx : Bq → X) (byy : Cq → X)
    (hbx : Function.Injective bx) (hby : Function.Injective byy)
    (Sx : Finset Bq) (Sy : Finset Cq)
    (hcover : ∀ z ∈ T, z ∈ (J'.support : Set X) →
      (∃ w ∈ Sx, bx w = z) ∨ ∃ v ∈ Sy, byy v = z) :
    ∑ z ∈ T, Module.length (X.presheaf.stalk z)
        (X.presheaf.stalk z ⧸ AlgebraicGeometry.IdealSheafData.stalk J' z) ≤
      (∑ w ∈ Sx, Module.length (X.presheaf.stalk (bx w))
          (X.presheaf.stalk (bx w) ⧸
            AlgebraicGeometry.IdealSheafData.stalk J' (bx w))) +
        ∑ v ∈ Sy, Module.length (X.presheaf.stalk (byy v))
          (X.presheaf.stalk (byy v) ⧸
            AlgebraicGeometry.IdealSheafData.stalk J' (byy v)) := by
  classical
  set F : X → ℕ∞ := fun z => Module.length (X.presheaf.stalk z)
    (X.presheaf.stalk z ⧸ AlgebraicGeometry.IdealSheafData.stalk J' z) with hF
  have hzero : ∀ z : X, z ∉ (J'.support : Set X) → F z = 0 := fun z hz =>
    Stacks.ResolutionOfSurfaces.length_quotient_stalk_eq_zero_of_notMem_support J' hz
  -- discard the points off the support
  have hTsupp : ∑ z ∈ T, F z = ∑ z ∈ T.filter (fun z => z ∈ (J'.support : Set X)), F z :=
    (Finset.sum_subset (Finset.filter_subset _ _) fun z hz hz' => hzero z fun hmem =>
      hz' (Finset.mem_filter.2 ⟨hz, hmem⟩)).symm
  -- split the remaining points according to the first chart
  have hsplit : ∑ z ∈ T.filter (fun z => z ∈ (J'.support : Set X)), F z =
      (∑ z ∈ (T.filter (fun z => z ∈ (J'.support : Set X))).filter
        (fun z => ∃ w ∈ Sx, bx w = z), F z) +
      ∑ z ∈ (T.filter (fun z => z ∈ (J'.support : Set X))).filter
        (fun z => ¬ ∃ w ∈ Sx, bx w = z), F z :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  -- a sum over points covered by an injective family is bounded by the sum over the family
  have hle : ∀ {ι : Type u} (U : Finset X) (s : Finset ι) (f : ι → X), Function.Injective f →
      (∀ z ∈ U, ∃ w ∈ s, f w = z) → ∑ z ∈ U, F z ≤ ∑ w ∈ s, F (f w) := by
    intro ι U s f hf hU
    refine le_trans (Finset.sum_le_sum_of_subset fun z hz => ?_)
      (le_of_eq (Finset.sum_image fun w _ w' _ h => hf h))
    obtain ⟨w, hw, rfl⟩ := hU z hz
    exact Finset.mem_image.2 ⟨w, hw, rfl⟩
  rw [hTsupp, hsplit]
  refine add_le_add (hle _ Sx bx hbx fun z hz => (Finset.mem_filter.1 hz).2)
    (hle _ Sy byy hby ?_)
  intro z hz
  obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
  obtain ⟨hzT, hzs⟩ := Finset.mem_filter.1 hz1
  exact (hcover z hzT hzs).resolve_left hz2

/-- The primes of `B` above an ideal, as a subset of the prime spectrum, are finite as soon as
the prime *ideals* above it are. -/
public theorem finite_setOf_le_of_finite_isPrime {B : Type u} [CommRing B] {Lc : Ideal B}
    (h : {p : Ideal B | p.IsPrime ∧ Lc ≤ p}.Finite) :
    {w : PrimeSpectrum B | Lc ≤ w.asIdeal}.Finite := by
  refine Set.Finite.of_finite_image (f := PrimeSpectrum.asIdeal) (h.subset ?_)
    (fun w _ w' _ hww => PrimeSpectrum.ext hww)
  rintro p ⟨w, hw, rfl⟩
  exact ⟨w.isPrime, hw⟩

/-- **A quotient by an ideal containing a power of the maximal ideal is Artinian over the
ring.** This is `Module.finiteLength_quotient_of_contains_maximalIdealPower` in the form in which
the colength drop consumes it. -/
public theorem isArtinian_quotient_of_pow_maximalIdeal_le {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] {L : Ideal R} {n : ℕ}
    (hmn : IsLocalRing.maximalIdeal R ^ (n + 1) ≤ L) : IsArtinian R (R ⧸ L) := by
  refine (isFiniteLength_iff_isNoetherian_isArtinian.1
    (Module.finiteLength_quotient_of_contains_maximalIdealPower R R (L : Submodule R R) n ?_)).2
  exact Submodule.smul_le.2 fun r hr m _ => Ideal.mul_mem_right m L (hmn hr)

/-- The residual ideal read on the chart of a section of the centre: the ideal cut out by `J'` on
the affine blowup algebra `A[𝔪/a]`. -/
public def chartIdeal (A : Type u) [CommRing A] [IsLocalRing A]
    (J' : (Stacks.Blowup.blowUp (centre A)).IdealSheafData)
    {a : Γ(Spec (CommRingCat.of A), ⊤)}
    (ha : a ∈ (centre A).ideal ⟨⊤, isAffineOpen_top _⟩) :
    Ideal (affineBlowup ((centre A).ideal ⟨⊤, isAffineOpen_top _⟩) a) :=
  Ideal.map (Scheme.ΓSpecIso (CommRingCat.of
      (affineBlowup ((centre A).ideal ⟨⊤, isAffineOpen_top _⟩) a))).hom.hom
    ((J'.comap (Stacks.Blowup.blowUpAffineChart (centre A) ⟨⊤, isAffineOpen_top _⟩ ha)).ideal
      ⟨⊤, isAffineOpen_top _⟩)

section Charts

variable (A : Type u) [CommRing A] [IsLocalRing A] {x y : A}
  (hspan : Ideal.span ({x, y} : Set A) = IsLocalRing.maximalIdeal A)
  (J' : (Stacks.Blowup.blowUp (centre A)).IdealSheafData)
  (Sx : Finset (PrimeSpectrum (affineBlowup ((centre A).ideal ⟨⊤, isAffineOpen_top _⟩)
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom x))))
  (hSx : ∀ w, w ∈ Sx ↔ chartIdeal A J' (mem_centre_ideal_top_x hspan) ≤ w.asIdeal)
  (Sy : Finset (PrimeSpectrum (affineBlowup ((centre A).ideal ⟨⊤, isAffineOpen_top _⟩)
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom y))))
  (hSy : ∀ v, v ∈ Sy ↔ chartIdeal A J' (mem_centre_ideal_top_y hspan) ≤ v.asIdeal ∧
    chartOverlapFraction (mem_centre_ideal_top_x hspan)
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom y) ∈ v.asIdeal)

include hSx hSy in
/-- **Every point of the support belongs to one of the two chart families.** A point of the
support of `J'` lying on the first chart is the image of a prime above the residual ideal there;
one not lying on the first chart lies on the second, and at the corresponding prime the chart
element `x / y` cannot be invertible, by
`Stacks.ResolutionOfSurfaces.CartierDescent.mem_opensRange_blowUpAffineChart_of_notMem`. -/
private theorem exists_mem_chart_family (z : Stacks.Blowup.blowUp (centre A))
    (hzs : z ∈ (J'.support : Set (Stacks.Blowup.blowUp (centre A)))) :
    (∃ w ∈ Sx, (Stacks.Blowup.blowUpAffineChart (centre A) ⟨⊤, isAffineOpen_top _⟩
        (mem_centre_ideal_top_x hspan)).base w = z) ∨
      ∃ v ∈ Sy, (Stacks.Blowup.blowUpAffineChart (centre A) ⟨⊤, isAffineOpen_top _⟩
        (mem_centre_ideal_top_y hspan)).base v = z := by
  by_cases hzx : z ∈ Set.range (Stacks.Blowup.blowUpAffineChart (centre A)
      ⟨⊤, isAffineOpen_top _⟩ (mem_centre_ideal_top_x hspan)).base
  · obtain ⟨w, rfl⟩ := hzx
    exact Or.inl ⟨w,
      (hSx w).2 ((mem_support_chart_iff (mem_centre_ideal_top_x hspan) J' w).1 hzs), rfl⟩
  · obtain hz1 | hz2 := mem_opensRange_chart_or A x y hspan z
    · exact absurd hz1 hzx
    · obtain ⟨v, rfl⟩ := hz2
      refine Or.inr ⟨v, (hSy v).2
        ⟨(mem_support_chart_iff (mem_centre_ideal_top_y hspan) J' v).1 hzs, ?_⟩, rfl⟩
      by_contra hnot
      exact hzx (mem_opensRange_blowUpAffineChart_of_notMem (mem_centre_ideal_top_x hspan)
        (mem_centre_ideal_top_y hspan) v hnot)

include hSx hSy in
/-- **The sum of the stalk colengths over `T` is at most the two chart sums.** The two families
cover the support by
`Stacks.ResolutionOfSurfaces.CartierDescent.exists_mem_chart_family`, points of `T` off the
support contribute nothing, and at a chart point the stalk colength is the colength of the
localized residual ideal by
`Stacks.ResolutionOfSurfaces.CartierDescent.length_stalk_quotient_chart_eq`. -/
private theorem sum_stalk_le_chart_sums (T : Finset (Stacks.Blowup.blowUp (centre A))) :
    ∑ z ∈ T, Module.length ((Stacks.Blowup.blowUp (centre A)).presheaf.stalk z)
        ((Stacks.Blowup.blowUp (centre A)).presheaf.stalk z ⧸
          AlgebraicGeometry.IdealSheafData.stalk J' z) ≤
      (∑ w ∈ Sx, Module.length (Localization.AtPrime w.asIdeal)
          (Localization.AtPrime w.asIdeal ⧸
            Ideal.map (algebraMap _ (Localization.AtPrime w.asIdeal))
              (chartIdeal A J' (mem_centre_ideal_top_x hspan)))) +
        ∑ v ∈ Sy, Module.length (Localization.AtPrime v.asIdeal)
          (Localization.AtPrime v.asIdeal ⧸
            Ideal.map (algebraMap _ (Localization.AtPrime v.asIdeal))
              (chartIdeal A J' (mem_centre_ideal_top_y hspan))) := by
  refine (sum_stalk_colength_le_of_two_families J' T
    (Stacks.Blowup.blowUpAffineChart (centre A) ⟨⊤, isAffineOpen_top _⟩
      (mem_centre_ideal_top_x hspan)).base
    (Stacks.Blowup.blowUpAffineChart (centre A) ⟨⊤, isAffineOpen_top _⟩
      (mem_centre_ideal_top_y hspan)).base
    (Stacks.Blowup.blowUpAffineChart (centre A) ⟨⊤, isAffineOpen_top _⟩
      (mem_centre_ideal_top_x hspan)).isOpenEmbedding.injective
    (Stacks.Blowup.blowUpAffineChart (centre A) ⟨⊤, isAffineOpen_top _⟩
      (mem_centre_ideal_top_y hspan)).isOpenEmbedding.injective Sx Sy
    (fun z _ hzs => exists_mem_chart_family A hspan J' Sx hSx Sy hSy z hzs)).trans ?_
  refine le_of_eq (congrArg₂ (· + ·) (Finset.sum_congr rfl fun w _ => ?_)
    (Finset.sum_congr rfl fun v _ => ?_))
  · exact length_stalk_quotient_chart_eq (mem_centre_ideal_top_x hspan) J' w
  · exact length_stalk_quotient_chart_eq (mem_centre_ideal_top_y hspan) J' v

end Charts

/-- **Stacks Project, Tag 0AGT, the colength drop.** Let `A` be a two-dimensional regular local
ring with maximal ideal `𝔪 = (x, y)`, let `L` be an ideal with `𝔪 ^ n ⊆ L ⊆ 𝔪`, let `X` be the
blowup of `Spec A` at its closed point with exceptional divisor `E`, and suppose
`𝒪_X(-dE)·J' = L·𝒪_X` with `d` positive and maximal. Then for every finite set `T` of points of
`X` containing the support of `J'`,

`∑_{z ∈ T} ℓ_{𝒪_z}(𝒪_z / J'_z) < ℓ_A(A / L)`.

This is the central inequality of [Stacks, Tag 0AGT]. The proof replaces the source's
cohomological argument — `H¹(X, L·𝒪_X) = 0` together with `Γ(X, 𝒪_X) = A` — by the two-chart
identities `B + C = D` and `B ∩ C = A` for the two standard affine charts read inside the
fraction field of `A`, which is what the gluing of
`Stacks.ResolutionOfSurfaces.CartierDescent.exists_mem_gluedIdeal_realizing` runs on. -/
public theorem sum_length_stalk_quotient_lt (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 2) {x y : A}
    (hspan : Ideal.span ({x, y} : Set A) = IsLocalRing.maximalIdeal A)
    (L : Ideal A) (n : ℕ) (hmn : IsLocalRing.maximalIdeal A ^ n ≤ L)
    {d : ℕ} (hd : 0 < d) {J' : (Stacks.Blowup.blowUp (centre A)).IdealSheafData}
    (hfac : Stacks.Blowup.exceptionalIdeal (centre A) ^ d * J' =
      (idealSheafOf A L).comap (Stacks.Blowup.blowUpToBase (centre A)))
    (hmax : ¬ ((idealSheafOf A L).comap (Stacks.Blowup.blowUpToBase (centre A)) ≤
      Stacks.Blowup.exceptionalIdeal (centre A) ^ (d + 1)))
    (T : Finset (Stacks.Blowup.blowUp (centre A))) :
    ∑ z ∈ T, Module.length ((Stacks.Blowup.blowUp (centre A)).presheaf.stalk z)
        ((Stacks.Blowup.blowUp (centre A)).presheaf.stalk z ⧸
          AlgebraicGeometry.IdealSheafData.stalk J' z) <
      Module.length A (A ⧸ L) := by
  classical
  have := isRegularLocalRing_sections A
  have hdimR : ringKrullDim Γ(Spec (CommRingCat.of A), ⊤) = 2 := by
    rw [ringKrullDim_sections A, hdim]
  have hspanR : Ideal.span ({(Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom x,
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom y} :
        Set Γ(Spec (CommRingCat.of A), ⊤)) =
      IsLocalRing.maximalIdeal Γ(Spec (CommRingCat.of A), ⊤) :=
    span_pair_inv_eq_maximalIdeal A hspan
  have hIc : (centre A).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom x,
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom y} :=
    centre_ideal_top A x y hspan
  have hspan2 : Ideal.span ({y, x} : Set A) = IsLocalRing.maximalIdeal A := by
    rw [Set.pair_comm]; exact hspan
  have hspanR2 : Ideal.span ({(Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom y,
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom x} :
        Set Γ(Spec (CommRingCat.of A), ⊤)) =
      IsLocalRing.maximalIdeal Γ(Spec (CommRingCat.of A), ⊤) := by
    rw [Set.pair_comm]; exact hspanR
  have hIc2 : (centre A).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom y,
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom x} := by
    rw [hIc, Set.pair_comm]
  -- the three facts about the residual ideal on each chart
  have hRxeq := span_pow_mul_ideal_comap_chart A hfac (mem_centre_ideal_top_x hspan)
  have hRyeq := span_pow_mul_ideal_comap_chart A hfac (mem_centre_ideal_top_y hspan)
  obtain ⟨kx, hkx⟩ := exists_pow_mem_ideal_comap_chart A hdim hspan hmn hfac
    (mem_centre_ideal_top_x hspan) rfl
  obtain ⟨ky, hky⟩ := exists_pow_mem_ideal_comap_chart A hdim hspan2 hmn hfac
    (mem_centre_ideal_top_y hspan) rfl
  have hnx := not_ideal_comap_chart_le_span A hdim hspan hfac hmax
    (mem_centre_ideal_top_x hspan) rfl
  have hny := not_ideal_comap_chart_le_span A hdim hspan2 hfac hmax
    (mem_centre_ideal_top_y hspan) rfl
  -- the colength of `L` is finite
  have hmapm : Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
      (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal Γ(Spec (CommRingCat.of A), ⊤) := by
    rw [← hspan, Ideal.map_span, Set.image_pair]
    exact hspanR
  have : IsArtinian Γ(Spec (CommRingCat.of A), ⊤)
      (Γ(Spec (CommRingCat.of A), ⊤) ⧸
        Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom L) := by
    refine isArtinian_quotient_of_pow_maximalIdeal_le (n := n) ?_
    rw [← hmapm, ← Ideal.map_pow]
    exact Ideal.map_mono ((Ideal.pow_le_pow_right (Nat.le_succ n)).trans hmn)
  -- the two finite families of primes
  have hfinX' := finite_setOf_le_of_finite_isPrime
    (finite_setOf_isPrime_le' (isRegular_pair_of_span hdimR hspanR) hspanR _ hIc _ kx hkx hnx)
  have hfinY' := (finite_setOf_le_of_finite_isPrime
    (finite_setOf_isPrime_le' (isRegular_pair_of_span hdimR hspanR2) hspanR2 _ hIc2 _ ky hky
      hny)).subset (fun v hv => hv.1 :
    {v | _ ≤ PrimeSpectrum.asIdeal v ∧
      chartOverlapFraction (mem_centre_ideal_top_x hspan)
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom y) ∈ PrimeSpectrum.asIdeal v} ⊆ _)
  have hSxmem : ∀ w, w ∈ hfinX'.toFinset ↔
      chartIdeal A J' (mem_centre_ideal_top_x hspan) ≤ w.asIdeal :=
    fun w => Set.Finite.mem_toFinset hfinX'
  have hSymem : ∀ v, v ∈ hfinY'.toFinset ↔
      (chartIdeal A J' (mem_centre_ideal_top_y hspan) ≤ v.asIdeal ∧
        chartOverlapFraction (mem_centre_ideal_top_x hspan)
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom y) ∈ v.asIdeal) :=
    fun v => Set.Finite.mem_toFinset hfinY'
  refine lt_of_le_of_lt (sum_stalk_le_chart_sums A hspan J' hfinX'.toFinset hSxmem
    hfinY'.toFinset hSymem T) ?_
  refine lt_of_lt_of_le (sum_length_affineBlowup_lt Γ(Spec (CommRingCat.of A), ⊤) hdimR hspanR _
    hIc (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom L) hd _ _ hRxeq hRyeq
    kx hkx hnx ky hky hny hfinX'.toFinset hSxmem
    hfinY'.toFinset (fun v hv => ((hSymem v).1 hv).1)
    (chartOverlapFraction (mem_centre_ideal_top_x hspan)
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom y))
    (coe_chartOverlapFraction (mem_centre_ideal_top_x hspan) _)
    (fun v hv => ((hSymem v).1 hv).2)) (le_of_eq ?_)
  exact (Module.quotient_length_eq_of_ringEquiv
    (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv L).symm

end Stacks.ResolutionOfSurfaces.CartierDescent

end

