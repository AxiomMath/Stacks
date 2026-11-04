module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.Examples.Scheme.PinchedPlane.Restrictions
public import StacksFrontier.Topology.Maps.Induced

/-!
# The two punctured axes as a closed subscheme of the punctured plane

The two punctured coordinate axes of `A²_k ∖ {0}`, parametrized as `Spec k[t, 1/t]` through
`(0, t)` and `(t⁻¹, 0)`, together form the scheme `Spec (k[t, 1/t] × k[t, 1/t])`, and this file
realizes them as a closed subscheme of the punctured plane.

They are not closed in the plane itself — their closures contain the origin — but they are
closed in the punctured plane. The verification is local on the affine chart
`D((x + y)(x + y³))`, where the pair of restriction maps is surjective, so that the axes are
closed there. That chart is not all of the punctured plane; what makes the image closed anyway
is that the zero locus of `xy` in the punctured plane is closed, contains the image, and is
itself contained in the chart.

The morphism folding the two axes onto one copy of `Spec k[t, 1/t]` is the other half of the
pinching datum: it is integral, being the spectrum of a diagonal into a product, and surjective.

## Main definitions

* `Stacks.Examples.PinchedPlane.puncturedPlane`: the punctured plane over `k`.
* `Stacks.Examples.PinchedPlane.pinchingChart`: the affine chart `D((x + y)(x + y³))` of the
  punctured plane, which contains both axes.
* `Stacks.Examples.PinchedPlane.axesToPuncturedPlane`: the two punctured axes inside the
  punctured plane.
* `Stacks.Examples.PinchedPlane.axesToAxis`: the morphism folding the two axes onto one, and
  `Stacks.Examples.PinchedPlane.firstAxisToPuncturedPlane`,
  `Stacks.Examples.PinchedPlane.secondAxisToPuncturedPlane` its two sections viewed in the
  punctured plane.

## Main results

* `Stacks.Examples.PinchedPlane.axesToPuncturedPlane_isClosedImmersion`: the two axes are a
  closed subscheme of the punctured plane.
* `Stacks.Examples.PinchedPlane.axesToAxis_isIntegralHom` and
  `Stacks.Examples.PinchedPlane.axesToAxis_surjective`: the folding morphism is integral and
  surjective.

## References

* [Stacks Project, Tag 0272](https://stacks.math.columbia.edu/tag/0272)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Examples.PinchedPlane

variable (k : Type u) [Field k]

section Opens

/-- The complement of the origin in `Spec k[x, y]`, as an open subset. -/
abbrev puncturedPlaneOpen : (affinePlane k).Opens := (puncturedAffinePlaneOf k).U

/-- The punctured plane over `k`. -/
abbrev puncturedPlane : Scheme.{u} := (puncturedPlaneOpen k).toScheme

/-- The punctured plane is quasi-compact. -/
instance puncturedPlane_compactSpace : CompactSpace (puncturedPlane k) :=
  PuncturedAffinePlane.compactSpace (puncturedAffinePlaneOf k)

/-- The punctured plane is nonempty. -/
instance puncturedPlane_nonempty : Nonempty (puncturedPlane k) :=
  PuncturedAffinePlane.nonempty (puncturedAffinePlaneOf k)

/-- The punctured plane is integral. -/
instance puncturedPlane_isIntegral : IsIntegral (puncturedPlane k) :=
  PuncturedAffinePlane.isIntegral (puncturedAffinePlaneOf k)

/-- The punctured plane is quasi-affine. -/
instance puncturedPlane_isQuasiAffine : (puncturedPlane k).IsQuasiAffine :=
  PuncturedAffinePlane.isQuasiAffine (puncturedAffinePlaneOf k)

/-- The standard open of `Spec k[x, y]` on which `(x + y)(x + y³)` is invertible. It contains
both punctured coordinate axes. -/
abbrev pinchingAffineOpen : (affinePlane k).Opens :=
  PrimeSpectrum.basicOpen (pinchingDenominator k)

/-- Where `x + y` is invertible, at least one of `x` and `y` is. -/
theorem basicOpen_sum_le_puncturedPlaneOpen :
    (PrimeSpectrum.basicOpen (MvPolynomial.X 0 + MvPolynomial.X 1 : affinePlaneRing k) :
      (affinePlane k).Opens) ≤ puncturedPlaneOpen k := by
  intro z hz
  rw [PrimeSpectrum.mem_basicOpen] at hz
  simp only [puncturedPlaneOpen, puncturedAffinePlaneOf_U, Opens.mem_sup,
    PrimeSpectrum.mem_basicOpen]
  by_contra h
  push Not at h
  exact hz (add_mem h.1 h.2)

/-- The chart `D((x + y)(x + y³))` lies in the punctured plane. -/
theorem pinchingAffineOpen_le_puncturedPlaneOpen :
    pinchingAffineOpen k ≤ puncturedPlaneOpen k := by
  refine le_trans (fun z hz => ?_) (basicOpen_sum_le_puncturedPlaneOpen k)
  have hz' : pinchingDenominator k ∉ z.asIdeal := hz
  exact fun h => hz' (Ideal.mul_mem_right _ _ h)

end Opens

section Chart

/-- The identification of the chart `D((x + y)(x + y³))` with the spectrum of its coordinate
ring. -/
def pinchingChartIso : (pinchingAffineOpen k).toScheme ≅ Spec (.of (pinchingRing k)) :=
  basicOpenIsoSpecAway (R := .of (affinePlaneRing k)) (pinchingDenominator k)

/-- The chart, read as a morphism into the affine plane, is the
spectrum of the localization map. -/
theorem pinchingChartIso_inv_ι :
    (pinchingChartIso k).inv ≫ (pinchingAffineOpen k).ι =
      Spec.map (CommRingCat.ofHom (algebraMap (affinePlaneRing k) (pinchingRing k))) := by
  rw [← basicOpenIsoSpecAway_hom_SpecMap (R := .of (affinePlaneRing k)) (pinchingDenominator k),
    pinchingChartIso, Iso.inv_hom_id_assoc]

/-- The affine chart of the punctured plane that contains both punctured axes. -/
def pinchingChart : Spec (.of (pinchingRing k)) ⟶ puncturedPlane k :=
  (pinchingChartIso k).inv ≫
    (affinePlane k).homOfLE (pinchingAffineOpen_le_puncturedPlaneOpen k)

/-- The chart is an open subscheme of the punctured plane. -/
instance pinchingChart_isOpenImmersion : IsOpenImmersion (pinchingChart k) := by
  unfold pinchingChart
  infer_instance

/-- The chart, read as a morphism into the affine plane, is the
spectrum of the localization map. -/
theorem pinchingChart_ι :
    pinchingChart k ≫ (puncturedPlaneOpen k).ι =
      Spec.map (CommRingCat.ofHom (algebraMap (affinePlaneRing k) (pinchingRing k))) := by
  rw [pinchingChart, Category.assoc, Scheme.homOfLE_ι, pinchingChartIso_inv_ι]

end Chart

section Axes

/-- The two punctured axes, inside the affine chart. -/
def axesToPinchingChart :
    Spec (.of (LaurentPolynomial k × LaurentPolynomial k)) ⟶ Spec (.of (pinchingRing k)) :=
  Spec.map (CommRingCat.ofHom (pinchingRestrictions k).toRingHom)

/-- The two axes are closed in the chart, because the pair of
restrictions to them is surjective. -/
instance axesToPinchingChart_isClosedImmersion :
    IsClosedImmersion (axesToPinchingChart k) :=
  IsClosedImmersion.spec_of_surjective _ (pinchingRestrictions_surjective k)

/-- The two punctured axes, inside the punctured plane. -/
def axesToPuncturedPlane :
    Spec (.of (LaurentPolynomial k × LaurentPolynomial k)) ⟶ puncturedPlane k :=
  axesToPinchingChart k ≫ pinchingChart k

/-- The two axes, read as a morphism into the affine plane, are the
spectrum of the pair of restrictions. -/
theorem axesToPuncturedPlane_ι :
    axesToPuncturedPlane k ≫ (puncturedPlaneOpen k).ι =
      Spec.map (CommRingCat.ofHom (axisRestrictions k).toRingHom) := by
  rw [axesToPuncturedPlane, Category.assoc, pinchingChart_ι, axesToPinchingChart,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    pinchingRestrictions_toRingHom_comp_algebraMap]

/-- The two axes are a locally closed subscheme of the punctured
plane. -/
instance axesToPuncturedPlane_isPreimmersion : IsPreimmersion (axesToPuncturedPlane k) := by
  unfold axesToPuncturedPlane
  infer_instance

/-- Both axes lie in the zero locus of `xy`. -/
theorem axesToPuncturedPlane_mem_zeroLocus
    (z : Spec (.of (LaurentPolynomial k × LaurentPolynomial k))) :
    (MvPolynomial.X 0 * MvPolynomial.X 1 : affinePlaneRing k) ∈
      ((puncturedPlaneOpen k).ι (axesToPuncturedPlane k z)).asIdeal := by
  have h : (MvPolynomial.X 0 * MvPolynomial.X 1 : affinePlaneRing k) ∈
      ((axesToPuncturedPlane k ≫ (puncturedPlaneOpen k).ι) z).asIdeal := by
    rw [axesToPuncturedPlane_ι]
    change (axisRestrictions k) (MvPolynomial.X 0 * MvPolynomial.X 1) ∈ z.asIdeal
    rw [axisRestrictions_X_mul_X]
    exact z.asIdeal.zero_mem
  exact h

/-- The chart, as an open subscheme of the punctured plane. -/
abbrev pinchingChartOpen : (puncturedPlane k).Opens :=
  (puncturedPlaneOpen k).ι ⁻¹ᵁ pinchingAffineOpen k

/-- The chart is an affine open of the punctured plane. -/
theorem isAffineOpen_pinchingChartOpen : IsAffineOpen (pinchingChartOpen k) :=
  (IsAffineOpen.Spec_basicOpen (R := .of (affinePlaneRing k))
      (pinchingDenominator k)).preimage_of_isOpenImmersion (puncturedPlaneOpen k).ι (by
    rw [Scheme.Opens.opensRange_ι]
    exact pinchingAffineOpen_le_puncturedPlaneOpen k)

/-- Both axes lie in the chart. -/
theorem axesToPuncturedPlane_mem_pinchingChartOpen
    (z : Spec (.of (LaurentPolynomial k × LaurentPolynomial k))) :
    axesToPuncturedPlane k z ∈ pinchingChartOpen k := by
  have h : pinchingDenominator k ∉
      ((axesToPuncturedPlane k ≫ (puncturedPlaneOpen k).ι) z).asIdeal := by
    rw [axesToPuncturedPlane_ι]
    change (axisRestrictions k) (pinchingDenominator k) ∉ z.asIdeal
    have : z.asIdeal.IsPrime := z.isPrime
    exact z.asIdeal.notMem_of_isUnit (isUnit_axisRestrictions_pinchingDenominator k)
  exact h

/-- A point of the punctured plane at which `xy` vanishes lies in the chart: one of `x` and `y`
vanishes there and the other does not, so both `x + y` and `x + y³` are invertible. -/
theorem pinchingDenominator_notMem (p : PrimeSpectrum (affinePlaneRing k))
    (hp : p ∈ puncturedPlaneOpen k)
    (hxy : (MvPolynomial.X 0 * MvPolynomial.X 1 : affinePlaneRing k) ∈ p.asIdeal) :
    pinchingDenominator k ∉ p.asIdeal := by
  have hp' : (MvPolynomial.X 0 : affinePlaneRing k) ∉ p.asIdeal ∨
      (MvPolynomial.X 1 : affinePlaneRing k) ∉ p.asIdeal := hp
  have : p.asIdeal.IsPrime := p.isPrime
  have hmem : pinchingDenominator k ∈ p.asIdeal →
      (MvPolynomial.X 0 + MvPolynomial.X 1 : affinePlaneRing k) ∈ p.asIdeal ∨
        (MvPolynomial.X 0 + MvPolynomial.X 1 ^ 3 : affinePlaneRing k) ∈ p.asIdeal :=
    fun hd => p.isPrime.mem_or_mem hd
  rcases p.isPrime.mem_or_mem hxy with hx | hy
  · have hy : (MvPolynomial.X 1 : affinePlaneRing k) ∉ p.asIdeal :=
      hp'.resolve_left (not_not.mpr hx)
    intro hd
    rcases hmem hd with h | h
    · exact hy ((p.asIdeal.add_mem_iff_right hx).mp h)
    · exact hy (p.isPrime.mem_of_pow_mem 3 ((p.asIdeal.add_mem_iff_right hx).mp h))
  · have hx : (MvPolynomial.X 0 : affinePlaneRing k) ∉ p.asIdeal :=
      hp'.resolve_right (not_not.mpr hy)
    intro hd
    rcases hmem hd with h | h
    · exact hx ((p.asIdeal.add_mem_iff_left hy).mp h)
    · exact hx ((p.asIdeal.add_mem_iff_left
        (p.asIdeal.pow_mem_of_mem hy 3 (by decide))).mp h)

/-- **The two punctured axes are closed in the punctured plane.** Their image is sandwiched
between the zero locus of `xy`, which is closed, and the chart, which contains that zero locus
and inside which the axes are closed. -/
instance axesToPuncturedPlane_isClosedImmersion :
    IsClosedImmersion (axesToPuncturedPlane k) := by
  set V : (affinePlane k).Opens :=
    PrimeSpectrum.basicOpen (MvPolynomial.X 0 * MvPolynomial.X 1 : affinePlaneRing k) with hV
  set C : Set (puncturedPlane k) :=
    (((puncturedPlaneOpen k).ι ⁻¹ᵁ V : (puncturedPlane k).Opens) : Set (puncturedPlane k))ᶜ
    with hCdef
  have hC : IsClosed C := ((puncturedPlaneOpen k).ι ⁻¹ᵁ V).isOpen.isClosed_compl
  have hmemC (p : puncturedPlane k)
      (hp : (MvPolynomial.X 0 * MvPolynomial.X 1 : affinePlaneRing k) ∈
        ((puncturedPlaneOpen k).ι p).asIdeal) : p ∈ C := fun hcon => hcon hp
  have hCmem (p : puncturedPlane k) (hp : p ∈ C) :
      (MvPolynomial.X 0 * MvPolynomial.X 1 : affinePlaneRing k) ∈
        ((puncturedPlaneOpen k).ι p).asIdeal := not_not.mp hp
  apply IsClosedImmersion.of_isPreimmersion
  have hrange : Set.range (axesToPuncturedPlane k) =
      pinchingChart k '' Set.range (axesToPinchingChart k) := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun z => Scheme.Hom.comp_apply _ _ z)
  rw [hrange]
  refine (pinchingChart k).isOpenEmbedding.isEmbedding.isInducing
    |>.isClosed_image_of_subset_of_subset_range
      (axesToPinchingChart k).isClosedEmbedding.isClosed_range hC ?_ ?_
  · rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    exact hmemC _ (axesToPuncturedPlane_mem_zeroLocus k z)
  · intro p hp
    have hd : p.1 ∈ pinchingAffineOpen k := pinchingDenominator_notMem k p.1 p.2 (hCmem p hp)
    refine ⟨(pinchingChartIso k).hom ⟨p.1, hd⟩, ?_⟩
    have heq := Scheme.Hom.comp_apply (pinchingChartIso k).hom (pinchingChartIso k).inv
      ⟨p.1, hd⟩
    rw [Iso.hom_inv_id] at heq
    change pinchingChart k _ = p
    rw [pinchingChart, Scheme.Hom.comp_apply]
    refine Eq.trans (congrArg ((affinePlane k).homOfLE
      (pinchingAffineOpen_le_puncturedPlaneOpen k)) heq.symm) ?_
    exact Subtype.ext (Scheme.homOfLE_apply _ _)

end Axes

section Fold

/-- Folding the two punctured axes onto a single copy of `Spec k[t, 1/t]`. -/
def axesToAxis :
    Spec (.of (LaurentPolynomial k × LaurentPolynomial k)) ⟶
      Spec (.of (LaurentPolynomial k)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (LaurentPolynomial k) (LaurentPolynomial k × LaurentPolynomial k)))

/-- The folding morphism is integral: a product of two copies of a
ring is finite over the diagonal copy. -/
instance axesToAxis_isIntegralHom : IsIntegralHom (axesToAxis k) := by
  rw [axesToAxis, IsIntegralHom.SpecMap_iff]
  exact Algebra.IsIntegral.isIntegral

/-- A ring map retracting the diagonal gives a section of the folding morphism. -/
private theorem spec_map_comp_axesToAxis
    (f : LaurentPolynomial k × LaurentPolynomial k →+* LaurentPolynomial k)
    (hf : f.comp (algebraMap (LaurentPolynomial k) (LaurentPolynomial k × LaurentPolynomial k)) =
      RingHom.id _) :
    Spec.map (CommRingCat.ofHom f) ≫ axesToAxis k = 𝟙 _ := by
  rw [axesToAxis, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hf, CommRingCat.ofHom_id,
    Spec.map_id]

/-- The section of the folding morphism given by the first of the two axes. -/
def firstAxisToAxes :
    Spec (.of (LaurentPolynomial k)) ⟶
      Spec (.of (LaurentPolynomial k × LaurentPolynomial k)) :=
  Spec.map (CommRingCat.ofHom (RingHom.fst (LaurentPolynomial k) (LaurentPolynomial k)))

/-- The section of the folding morphism given by the second of the two axes. -/
def secondAxisToAxes :
    Spec (.of (LaurentPolynomial k)) ⟶
      Spec (.of (LaurentPolynomial k × LaurentPolynomial k)) :=
  Spec.map (CommRingCat.ofHom (RingHom.snd (LaurentPolynomial k) (LaurentPolynomial k)))

/-- The first axis is a section of the folding morphism. -/
theorem firstAxisToAxes_axesToAxis : firstAxisToAxes k ≫ axesToAxis k = 𝟙 _ := by
  exact spec_map_comp_axesToAxis k _ rfl

/-- The second axis is a section of the folding morphism. -/
theorem secondAxisToAxes_axesToAxis : secondAxisToAxes k ≫ axesToAxis k = 𝟙 _ := by
  exact spec_map_comp_axesToAxis k _ rfl

/-- The folding morphism is surjective, having a section. -/
instance axesToAxis_surjective : Surjective (axesToAxis k) where
  surj y := ⟨firstAxisToAxes k y, by
    rw [← Scheme.Hom.comp_apply, firstAxisToAxes_axesToAxis]
    rfl⟩

/-- The first punctured axis, inside the punctured plane. -/
def firstAxisToPuncturedPlane :
    Spec (.of (LaurentPolynomial k)) ⟶ puncturedPlane k :=
  firstAxisToAxes k ≫ axesToPuncturedPlane k

/-- The second punctured axis, inside the punctured plane. -/
def secondAxisToPuncturedPlane :
    Spec (.of (LaurentPolynomial k)) ⟶ puncturedPlane k :=
  secondAxisToAxes k ≫ axesToPuncturedPlane k

/-- Precomposing the axes with a ring map `f` gives the spectrum of `g`, if `f` followed by the
restrictions to the axes is `g`. -/
private theorem spec_map_comp_axesToPuncturedPlane_ι
    (f : LaurentPolynomial k × LaurentPolynomial k →+* LaurentPolynomial k)
    (g : affinePlaneRing k →+* LaurentPolynomial k)
    (h : f.comp (axisRestrictions k).toRingHom = g) :
    Spec.map (CommRingCat.ofHom f) ≫ axesToPuncturedPlane k ≫ (puncturedPlaneOpen k).ι =
      Spec.map (CommRingCat.ofHom g) := by
  rw [axesToPuncturedPlane_ι, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

/-- The first axis, read as a morphism into the affine plane, is the
spectrum of the restriction to it. -/
theorem firstAxisToPuncturedPlane_ι :
    firstAxisToPuncturedPlane k ≫ (puncturedPlaneOpen k).ι =
      Spec.map (CommRingCat.ofHom (restrictToFirstAxisBase k).toRingHom) := by
  rw [firstAxisToPuncturedPlane, Category.assoc]
  exact spec_map_comp_axesToPuncturedPlane_ι k _ _ (fst_comp_axisRestrictions k)

/-- The second axis, read as a morphism into the affine plane, is the
spectrum of the restriction to it. -/
theorem secondAxisToPuncturedPlane_ι :
    secondAxisToPuncturedPlane k ≫ (puncturedPlaneOpen k).ι =
      Spec.map (CommRingCat.ofHom (restrictToSecondAxisBase k).toRingHom) := by
  rw [secondAxisToPuncturedPlane, Category.assoc]
  exact spec_map_comp_axesToPuncturedPlane_ι k _ _ (snd_comp_axisRestrictions k)

end Fold

end Stacks.Examples.PinchedPlane

end
