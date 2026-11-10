module

public import StacksFrontier.AlgebraicGeometry.Blowup.FiniteOverLocalDimensionOne
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Bijective
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Difference
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtension
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertPointAddition
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.AffineIdealSheaf
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.BlowupTransport
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.LocalCentre
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.StalkDetection
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.SurfaceCharts
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.FactorizationBirationalMaps
public import StacksFrontier.RingTheory.Support.Finite

/-!
# Globalising the local splitting of a blowup at a closed point

Let `Y` be a scheme, let `W` be a finite set of closed points of `Y` whose local rings are
regular of dimension two, and let `J` be a quasi-coherent sheaf of ideals whose support is
contained in `W`. For a point `y` of the support of `J`, let `M` be the sheaf of ideals of the
reduced closed point `y` and let `X` be the blowup of `Y` in `M`, with exceptional divisor `E`.
Then

`J·𝒪_X = 𝒪_X(-dE)·J'`

for a positive `d` and a sheaf of ideals `J'` again supported on finitely many closed points,
lying over `W`, with regular two-dimensional local rings and of strictly smaller total colength.
That statement is `Stacks.ResolutionOfSurfaces.PointBlowupColengthDescent`, the inductive step of
[Stacks, Tag 0AHH].

This file deduces it from the corresponding statement about a two-dimensional regular local ring,
the local half of [Stacks, Tag 0AGT], here taken as the hypothesis
`Stacks.ResolutionOfSurfaces.CartierDescent.LocalColengthSplitting`, by flat base change along
`Y.fromSpecStalk y : Spec 𝒪_{Y, y} ⟶ Y` ([Stacks, Tag 0805]); away from `y` the blowup is an
isomorphism ([Stacks, Tag 02OS]).

## Main definitions

* `Stacks.ResolutionOfSurfaces.CartierDescent.LocalColengthSplitting`: the local splitting of
  [Stacks, Tag 0AGT], stated for `AlgebraicGeometry.blowUp`.
* `Stacks.ResolutionOfSurfaces.CartierDescent.LocalColengthSplittingChart`: the same local
  splitting, stated for `Stacks.Blowup.blowUp`.

## Main results

* `Stacks.ResolutionOfSurfaces.CartierDescent.pointBlowupColengthDescent_of_local`: the local
  splitting implies `Stacks.ResolutionOfSurfaces.PointBlowupColengthDescent`.
* `Stacks.ResolutionOfSurfaces.CartierDescent.localColengthSplitting_of_chart`: the local
  splitting for `Stacks.Blowup.blowUp` implies the one for `AlgebraicGeometry.blowUp`.

## References

* [Stacks Project, Tag 0AHH](https://stacks.math.columbia.edu/tag/0AHH)
* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces.CartierDescent

/-! ### The local splitting, as a hypothesis -/

/-- The local splitting of [Stacks, Tag 0AGT]: for a two-dimensional regular local ring `A` and an
ideal `L` with `𝔪 ^ n ≤ L ≤ 𝔪`, one blowup at the closed point splits the inverse image of `L` as
a power of the exceptional divisor times an ideal sheaf supported at finitely many closed points
with regular two-dimensional local rings and of strictly smaller total colength. -/
public abbrev LocalColengthSplitting : Prop :=
  ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A], ringKrullDim A = 2 →
    ∀ (L : Ideal A) (n : ℕ), IsLocalRing.maximalIdeal A ^ n ≤ L →
      L ≤ IsLocalRing.maximalIdeal A →
      ∃ (d : ℕ) (T : Finset (AlgebraicGeometry.blowUp
            (Stacks.ResolutionOfSurfaces.CartierDescent.centre A)))
        (J' : (AlgebraicGeometry.blowUp
            (Stacks.ResolutionOfSurfaces.CartierDescent.centre A)).IdealSheafData),
        0 < d ∧
        AlgebraicGeometry.exceptionalIdeal
            (Stacks.ResolutionOfSurfaces.CartierDescent.centre A) ^ d * J' =
          (Stacks.ResolutionOfSurfaces.CartierDescent.idealSheafOf A L).comap
            (AlgebraicGeometry.blowUpToBase
              (Stacks.ResolutionOfSurfaces.CartierDescent.centre A)) ∧
        ((J'.support : Set (AlgebraicGeometry.blowUp
            (Stacks.ResolutionOfSurfaces.CartierDescent.centre A))) ⊆
          (T : Set (AlgebraicGeometry.blowUp
            (Stacks.ResolutionOfSurfaces.CartierDescent.centre A)))) ∧
        (∀ z ∈ T, IsClosed ({z} : Set (AlgebraicGeometry.blowUp
            (Stacks.ResolutionOfSurfaces.CartierDescent.centre A)))) ∧
        (∀ z ∈ T, IsRegularLocalRing ((AlgebraicGeometry.blowUp
            (Stacks.ResolutionOfSurfaces.CartierDescent.centre A)).presheaf.stalk z)) ∧
        (∀ z ∈ T, ringKrullDim ((AlgebraicGeometry.blowUp
            (Stacks.ResolutionOfSurfaces.CartierDescent.centre A)).presheaf.stalk z) = 2) ∧
        ∑ z ∈ T, Module.length ↥((AlgebraicGeometry.blowUp
            (Stacks.ResolutionOfSurfaces.CartierDescent.centre A)).presheaf.stalk z)
          (↥((AlgebraicGeometry.blowUp
            (Stacks.ResolutionOfSurfaces.CartierDescent.centre A)).presheaf.stalk z) ⧸
              AlgebraicGeometry.IdealSheafData.stalk J' z) <
          Module.length A (A ⧸ L)

/-! ### Localising at a closed point -/

section Localise

variable {Y : Scheme.{u}}

/-- The inverse image of an ideal sheaf along `Spec 𝒪_{Y, y} ⟶ Y` is the ideal sheaf cut out by
the stalk at `y`. -/
private theorem comap_fromSpecStalk_eq_ofIdealTop (I : Y.IdealSheafData) (y : Y) :
    I.comap (Y.fromSpecStalk y) = Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv.hom
        (AlgebraicGeometry.IdealSheafData.stalk I y)) := by
  rw [← AlgebraicGeometry.ideal_comap_fromSpecStalk I y]
  exact (ofIdealTop_ideal_top _).symm

/-- The support of the inverse image of an ideal sheaf along `Spec 𝒪_{Y, y} ⟶ Y` is the zero
locus of the stalk at `y`. -/
private theorem coe_support_comap_fromSpecStalk (I : Y.IdealSheafData) (y : Y) :
    ((I.comap (Y.fromSpecStalk y)).support : Set (Spec (Y.presheaf.stalk y))) =
      PrimeSpectrum.zeroLocus
        ((AlgebraicGeometry.IdealSheafData.stalk I y : Ideal ↥(Y.presheaf.stalk y)) : Set _) := by
  rw [comap_fromSpecStalk_eq_ofIdealTop, Scheme.IdealSheafData.coe_support_ofIdealTop,
    AlgebraicGeometry.Spec_zeroLocus, ← Ideal.coe_comap,
    Ideal.comap_map_of_bijective _ (ConcreteCategory.bijective_of_isIso _)]

/-- The zero locus of the stalk of an ideal sheaf supported at closed points is the closed point
of the spectrum of the local ring. -/
private theorem zeroLocus_stalk_subset_closedPoint (J : Y.IdealSheafData)
    (hclosed : ∀ w ∈ (J.support : Set Y), IsClosed ({w} : Set Y)) (y : Y) :
    PrimeSpectrum.zeroLocus
        ((AlgebraicGeometry.IdealSheafData.stalk J y : Ideal ↥(Y.presheaf.stalk y)) : Set _) ⊆
      {IsLocalRing.closedPoint ↥(Y.presheaf.stalk y)} := by
  rw [← coe_support_comap_fromSpecStalk]
  intro p hp
  rw [Scheme.IdealSheafData.support_comap] at hp
  have hmem : (Y.fromSpecStalk y).base p ∈ (J.support : Set Y) := hp
  have hspec : (Y.fromSpecStalk y).base p ⤳ y :=
    Scheme.range_fromSpecStalk.subset ⟨p, rfl⟩
  have hy : (Y.fromSpecStalk y).base p = y := by
    have h := hspec.mem_closure
    rw [(hclosed _ hmem).closure_eq, Set.mem_singleton_iff] at h
    exact h.symm
  refine Set.mem_singleton_iff.mpr ((Y.fromSpecStalk y).isEmbedding.injective ?_)
  rwa [Scheme.fromSpecStalk_closedPoint]

/-- A power of the maximal ideal lies inside the stalk of an ideal sheaf supported at closed
points. -/
private theorem exists_pow_maximalIdeal_le_stalk (J : Y.IdealSheafData)
    (hclosed : ∀ w ∈ (J.support : Set Y), IsClosed ({w} : Set Y)) (y : Y)
    (hN : IsNoetherianRing ↥(Y.presheaf.stalk y)) :
    ∃ n : ℕ, IsLocalRing.maximalIdeal ↥(Y.presheaf.stalk y) ^ n ≤
      AlgebraicGeometry.IdealSheafData.stalk J y := by
  have := hN
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)
  rw [← PrimeSpectrum.zeroLocus_subset_zeroLocus_iff]
  simpa only [zeroLocus_maximalIdeal] using zeroLocus_stalk_subset_closedPoint J hclosed y

/-- The colength of the stalk of an ideal sheaf supported at closed points is finite. -/
private theorem length_quotient_stalk_lt_top (J : Y.IdealSheafData)
    (hclosed : ∀ w ∈ (J.support : Set Y), IsClosed ({w} : Set Y)) (y : Y)
    (hN : IsNoetherianRing ↥(Y.presheaf.stalk y)) :
    Module.length ↥(Y.presheaf.stalk y)
      (↥(Y.presheaf.stalk y) ⧸ AlgebraicGeometry.IdealSheafData.stalk J y) < ⊤ := by
  have := hN
  by_cases hI : AlgebraicGeometry.IdealSheafData.stalk J y = ⊤
  · rw [Stacks.ResolutionOfSurfaces.length_quotient_stalk_eq_zero_of_notMem_support J
      ((AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_not_mem_support J y).mp hI)]
    exact lt_top_iff_ne_top.mpr (by simp)
  · refine lt_top_iff_ne_top.mpr (Module.length_ne_top_iff.mpr (isFiniteLength_of_support ?_))
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
    exact (zeroLocus_stalk_subset_closedPoint J hclosed y).antisymm
      (Set.singleton_subset_iff.mpr (IsLocalRing.le_maximalIdeal hI))

end Localise

/-! ### A closed-image criterion and colength arithmetic -/

/-- A point of an embedded source which is closed there and whose image is a closed point whose
whole fibre lies in the range of the embedding has closed image. -/
private theorem isClosed_singleton_image_of_fibre_subset_range
    {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {j : A → B} (hj : Topology.IsEmbedding j) {g : B → C} (hg : Continuous g)
    {c : C} (hc : IsClosed ({c} : Set C)) (hrange : g ⁻¹' {c} ⊆ Set.range j)
    {a : A} (ha : IsClosed ({a} : Set A)) (hac : g (j a) = c) :
    IsClosed ({j a} : Set B) := by
  rw [← closure_subset_iff_isClosed]
  intro b hb
  have hab : j a ⤳ b := specializes_iff_mem_closure.mpr hb
  have hcb : g b = c := by
    have h := (hab.map hg).mem_closure
    rwa [hac, hc.closure_eq, Set.mem_singleton_iff] at h
  obtain ⟨a', rfl⟩ := hrange hcb
  have haa' : a ⤳ a' := hj.isInducing.specializes_iff.mp hab
  have h := haa'.mem_closure
  rw [ha.closure_eq, Set.mem_singleton_iff] at h
  exact Set.mem_singleton_iff.mpr (congrArg j h)

/-- **Adding a strict inequality to an equality of total colengths.** If the points of `P`
contribute strictly less than the single point `y` does, and the points of `Q` contribute exactly
what the points of `W` other than `y` do, then the total colength over `P ∪ Q` is smaller than
the total colength over `W`, provided the contributions of `W \ {y}` are finite. -/
private theorem totalColength_lt_of_split {Y X : Scheme.{u}} [DecidableEq ↥Y] [DecidableEq ↥X]
    (W : Finset Y) (J : Y.IdealSheafData) (K : X.IdealSheafData) (P Q : Finset X) (y : Y)
    (hyW : y ∈ W)
    (hdisj : Disjoint P Q)
    (hP : ∑ z ∈ P, Module.length ↥(X.presheaf.stalk z)
        (↥(X.presheaf.stalk z) ⧸ AlgebraicGeometry.IdealSheafData.stalk K z) <
      Module.length ↥(Y.presheaf.stalk y)
        (↥(Y.presheaf.stalk y) ⧸ AlgebraicGeometry.IdealSheafData.stalk J y))
    (hQ : ∑ z ∈ Q, Module.length ↥(X.presheaf.stalk z)
        (↥(X.presheaf.stalk z) ⧸ AlgebraicGeometry.IdealSheafData.stalk K z) =
      ∑ w ∈ W.erase y, Module.length ↥(Y.presheaf.stalk w)
        (↥(Y.presheaf.stalk w) ⧸ AlgebraicGeometry.IdealSheafData.stalk J w))
    (hfin : ∀ w ∈ W.erase y, Module.length ↥(Y.presheaf.stalk w)
        (↥(Y.presheaf.stalk w) ⧸ AlgebraicGeometry.IdealSheafData.stalk J w) ≠ ⊤) :
    Stacks.ResolutionOfSurfaces.totalColength K (P ∪ Q) <
      Stacks.ResolutionOfSurfaces.totalColength J W := by
  classical
  simp only [Stacks.ResolutionOfSurfaces.totalColength]
  rw [Finset.sum_union hdisj, hQ, ← Finset.add_sum_erase W _ hyW]
  exact WithTop.add_lt_add_right
    (WithTop.sum_lt_top.mpr fun w hw => lt_top_iff_ne_top.mpr (hfin w hw)).ne hP

/-- Regularity of the local rings is invariant under a morphism that is an isomorphism on
stalks. -/
private theorem isRegularLocalRing_stalk_iff_of_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (z : X) [IsIso (f.stalkMap z)] :
    IsRegularLocalRing ↥(X.presheaf.stalk z) ↔ IsRegularLocalRing ↥(Y.presheaf.stalk (f z)) :=
  ⟨fun _ => .of_ringEquiv (asIso (f.stalkMap z)).commRingCatIsoToRingEquiv.symm,
    fun _ => .of_ringEquiv (asIso (f.stalkMap z)).commRingCatIsoToRingEquiv⟩

/-- The Krull dimension of the local rings is invariant under a morphism that is an isomorphism on
stalks. -/
private theorem ringKrullDim_stalk_eq_of_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (z : X) [IsIso (f.stalkMap z)] :
    ringKrullDim ↥(X.presheaf.stalk z) = ringKrullDim ↥(Y.presheaf.stalk (f z)) :=
  (ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap z)).commRingCatIsoToRingEquiv).symm

/-! ### The globalisation -/

/-- The local splitting of [Stacks, Tag 0AGT] for a two-dimensional regular local ring implies the
colength-descent statement `Stacks.ResolutionOfSurfaces.PointBlowupColengthDescent` for an
arbitrary scheme: at a point `y` of the support of a sheaf of ideals supported on finitely many
closed points with regular two-dimensional local rings, blowing up `y` splits the inverse image of
the ideal as a power of the exceptional divisor times a sheaf of ideals again of that shape, over
the same set of points and of strictly smaller total colength. -/
public theorem pointBlowupColengthDescent_of_local (hlocal : LocalColengthSplitting.{u}) :
    Stacks.ResolutionOfSurfaces.PointBlowupColengthDescent.{u} := by
  classical
  intro Y W J hWclosed hWreg hWdim hJW y hyJ hy M hM
  have hyW : y ∈ W := hJW hyJ
  have hregy : IsRegularLocalRing ↥(Y.presheaf.stalk y) := hWreg y hyW
  have hNy : IsNoetherianRing ↥(Y.presheaf.stalk y) := inferInstance
  have hJclosed : ∀ w ∈ (J.support : Set Y), IsClosed ({w} : Set Y) := fun w hw =>
    hWclosed w (hJW hw)
  have hLm : IdealSheafData.stalk J y ≤ IsLocalRing.maximalIdeal ↥(Y.presheaf.stalk y) :=
    IsLocalRing.le_maximalIdeal fun h =>
      (IdealSheafData.stalk_eq_top_iff_not_mem_support J y).mp h hyJ
  obtain ⟨n, hn⟩ := exists_pow_maximalIdeal_le_stalk J hJclosed y hNy
  have hcentre : M.comap (Y.fromSpecStalk y) = centre ↥(Y.presheaf.stalk y) := by
    rw [hM]; exact comap_vanishingIdeal_fromSpecStalk_of y hy
  have hJloc : J.comap (Y.fromSpecStalk y) =
      idealSheafOf ↥(Y.presheaf.stalk y) (IdealSheafData.stalk J y) :=
    comap_fromSpecStalk_eq_ofIdealTop J y
  have hMsupp : (M.support : Set Y) = {y} := by
    rw [hM]; exact Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have key := hlocal ↥(Y.presheaf.stalk y) (hWdim y hyW) (IdealSheafData.stalk J y) n hn hLm
  rw [← hcentre, ← hJloc] at key
  obtain ⟨d, T, J₀, hd, hsplit, hTsupp, hTclosed, hTreg, hTdim, hTsum⟩ := key
  have hsplit' : exceptionalIdeal (M.comap (Y.fromSpecStalk y)) ^ d * J₀ =
      (J.comap (Y.fromSpecStalk y)).comap
        (blowUpToBase (M.comap (Y.fromSpecStalk y))) := hsplit
  obtain ⟨q, sq⟩ := exists_isPullback_blowUpToBase_comap_fromSpecStalk y M
  have hqiso : ∀ z, IsIso (q.stalkMap z) := isIso_stalkMap_of_isPullback y sq
  have hqemb : Topology.IsEmbedding q.base := by
    have := (flat_and_isPreimmersion_of_isPullback y sq).2
    exact q.isEmbedding
  have hfib : (blowUpToBase M).base ⁻¹' {y} ⊆ Set.range q.base :=
    fibre_subset_range_of_isPullback y sq
  have hlocLe : (J.comap (Y.fromSpecStalk y)).comap
      (blowUpToBase (M.comap (Y.fromSpecStalk y))) ≤
      exceptionalIdeal (M.comap (Y.fromSpecStalk y)) ^ d := by
    rw [← hsplit']; exact Scheme.IdealSheafData.mul_le_left _ _
  have hleE := le_exceptionalIdeal_pow_of_comap_le y M J hMsupp d sq hlocLe
  obtain ⟨K, hK⟩ := exists_mul_eq_of_le_of_isEffectiveCartierDivisor (exceptionalIdeal M ^ d)
    (J.comap (blowUpToBase M)) (Stacks.Divisors.isEffectiveCartierDivisor_pow inferInstance d)
    hleE
  have hEq : (exceptionalIdeal M ^ d).comap q =
      exceptionalIdeal (M.comap (Y.fromSpecStalk y)) ^ d := by
    rw [Stacks.IdealSheaf.comap_pow, comap_exceptionalIdeal_of_isPullback y q sq]
  have hpull : (J.comap (blowUpToBase M)).comap q =
      (J.comap (Y.fromSpecStalk y)).comap (blowUpToBase (M.comap (Y.fromSpecStalk y))) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, sq.w]
  have hKq : K.comap q = J₀ := by
    refine Stacks.Divisors.eq_of_mul_eq_mul_of_isEffectiveCartierDivisor
      (K := exceptionalIdeal (M.comap (Y.fromSpecStalk y)) ^ d)
      (Stacks.Divisors.isEffectiveCartierDivisor_pow inferInstance d) ?_
    calc exceptionalIdeal (M.comap (Y.fromSpecStalk y)) ^ d * K.comap q
        = (exceptionalIdeal M ^ d * K).comap q := by rw [Stacks.IdealSheaf.comap_mul, hEq]
      _ = (J.comap (blowUpToBase M)).comap q := by rw [← hK]
      _ = (J.comap (Y.fromSpecStalk y)).comap
            (blowUpToBase (M.comap (Y.fromSpecStalk y))) := hpull
      _ = exceptionalIdeal (M.comap (Y.fromSpecStalk y)) ^ d * J₀ := hsplit'.symm
  have hEsupp : ((exceptionalIdeal M ^ d).support : Set (blowUp M)) =
      (blowUpToBase M).base ⁻¹' {y} := by
    obtain ⟨m, hm⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    rw [hm, Scheme.IdealSheafData.support_pow_succ]
    simp only [exceptionalIdeal, Scheme.IdealSheafData.support_comap,
      TopologicalSpace.Closeds.coe_preimage, hMsupp]
  have hEtop : ∀ z : blowUp M, (blowUpToBase M).base z ≠ y →
      IdealSheafData.stalk (exceptionalIdeal M ^ d) z = ⊤ := by
    intro z hz
    refine (IdealSheafData.stalk_eq_top_iff_not_mem_support _ z).mpr fun hmem => ?_
    exact hz (hEsupp.subset hmem)
  have hstalkK : ∀ z : blowUp M, (blowUpToBase M).base z ≠ y →
      IdealSheafData.stalk (J.comap (blowUpToBase M)) z = IdealSheafData.stalk K z := by
    intro z hz
    rw [hK, IdealSheafData.stalk_mul, hEtop z hz, Ideal.top_mul]
  have hKsupp : ∀ z : blowUp M, z ∈ (K.support : Set (blowUp M)) →
      (blowUpToBase M).base z ∈ (J.support : Set Y) := by
    intro z hz
    have h2 := Scheme.IdealSheafData.support_antitone (Scheme.IdealSheafData.mul_le_right
      (exceptionalIdeal M ^ d) K) hz
    rwa [← hK, Scheme.IdealSheafData.support_comap] at h2
  have hclosedPt : ((J.comap (Y.fromSpecStalk y)).support :
      Set (Spec (Y.presheaf.stalk y))) ⊆ {IsLocalRing.closedPoint ↥(Y.presheaf.stalk y)} := by
    rw [coe_support_comap_fromSpecStalk]
    exact zeroLocus_stalk_subset_closedPoint J hJclosed y
  have hJ₀fib : ∀ z₀ : blowUp (M.comap (Y.fromSpecStalk y)), z₀ ∈ (J₀.support : Set _) →
      (blowUpToBase M).base (q.base z₀) = y := by
    intro z₀ hz₀
    have h1 : (J.comap (Y.fromSpecStalk y)).comap
        (blowUpToBase (M.comap (Y.fromSpecStalk y))) ≤ J₀ := by
      rw [← hsplit']
      exact Scheme.IdealSheafData.mul_le_right _ _
    have h2 := Scheme.IdealSheafData.support_antitone h1 hz₀
    rw [Scheme.IdealSheafData.support_comap] at h2
    have h3 : (blowUpToBase (M.comap (Y.fromSpecStalk y))).base z₀ =
        IsLocalRing.closedPoint ↥(Y.presheaf.stalk y) := hclosedPt h2
    have h4 : (Y.fromSpecStalk y).base
        ((blowUpToBase (M.comap (Y.fromSpecStalk y))).base z₀) =
        (blowUpToBase M).base (q.base z₀) := by
      simpa using congrArg (fun g : _ ⟶ Y => g.base z₀) sq.w
    rw [← h4, h3]
    exact Scheme.fromSpecStalk_closedPoint
  have hstalkAway : ∀ z : blowUp M, (blowUpToBase M).base z ∉ (M.support : Set Y) →
      IsIso ((blowUpToBase M).stalkMap z) := fun z hz =>
    isIso_stalkMap_of_isIso_morphismRestrict _ (isIso_blowUp_restrict_compl_support M) hz
  have hinjAway : ∀ z₁ z₂ : blowUp M, (blowUpToBase M).base z₁ ∉ (M.support : Set Y) →
      (blowUpToBase M).base z₁ = (blowUpToBase M).base z₂ → z₁ = z₂ :=
    fun z₁ z₂ h1 h2 => blowUpToBase_injective_of_notMem_support M h1 h2
  have hpreW : ∀ w ∈ W.erase y, ∃ z : blowUp M, (blowUpToBase M).base z = w := by
    intro w hw
    refine exists_blowUpToBase_eq_of_notMem_support M ?_
    rw [hMsupp, Set.mem_singleton_iff]
    exact Finset.ne_of_mem_erase hw
  choose σ hσ using hpreW
  have hσne : ∀ (w : Y) (hw : w ∈ W.erase y),
      (blowUpToBase M).base (σ w hw) ∉ (M.support : Set Y) := by
    intro w hw
    rw [hσ w hw, hMsupp, Set.mem_singleton_iff]
    exact Finset.ne_of_mem_erase hw
  set T' : Finset (blowUp (M.comap (Y.fromSpecStalk y))) :=
    T.filter (fun z => z ∈ (J₀.support : Set _)) with hT'
  set P : Finset (blowUp M) := T'.image q.base with hPdef
  set Q : Finset (blowUp M) := (W.erase y).attach.image (fun w => σ w.1 w.2) with hQdef
  have hmemP : ∀ z ∈ P, ∃ z₀ ∈ T', q.base z₀ = z := by
    intro z hz; rw [hPdef] at hz; exact Finset.mem_image.mp hz
  have hmemQ : ∀ z ∈ Q, ∃ w, ∃ hw : w ∈ W.erase y, σ w hw = z := by
    intro z hz
    rw [hQdef] at hz
    obtain ⟨w, -, hwz⟩ := Finset.mem_image.mp hz
    exact ⟨w.1, w.2, hwz⟩
  have hQmem : ∀ (w : Y) (hw : w ∈ W.erase y), σ w hw ∈ Q := by
    intro w hw
    rw [hQdef]
    exact Finset.mem_image.mpr ⟨⟨w, hw⟩, Finset.mem_attach _ _, rfl⟩
  have hPfib : ∀ z ∈ P, (blowUpToBase M).base z = y := by
    intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := hmemP z hz
    exact hJ₀fib z₀ (Finset.mem_filter.mp hz₀).2
  have hQfib : ∀ z ∈ Q, (blowUpToBase M).base z ≠ y := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hmemQ z hz
    rw [hσ w hw]
    exact Finset.ne_of_mem_erase hw
  refine ⟨d, P ∪ Q, K, hK.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases Finset.mem_union.mp hz with hzP | hzQ
    · obtain ⟨z₀, hz₀, rfl⟩ := hmemP z hzP
      exact isClosed_singleton_image_of_fibre_subset_range hqemb
        (blowUpToBase M).continuous hy hfib (hTclosed z₀ (Finset.mem_filter.mp hz₀).1)
        (hJ₀fib z₀ (Finset.mem_filter.mp hz₀).2)
    · obtain ⟨w, hw, rfl⟩ := hmemQ z hzQ
      have hpre : (blowUpToBase M).base ⁻¹' {w} = {σ w hw} := by
        ext z'
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        refine ⟨fun hz' => (hinjAway (σ w hw) z' (hσne w hw) ?_).symm, fun hz' => ?_⟩
        · rw [hσ w hw, hz']
        · rw [hz', hσ w hw]
      rw [← hpre]
      exact (hWclosed w (Finset.mem_of_mem_erase hw)).preimage (blowUpToBase M).continuous
  · intro z hz
    rcases Finset.mem_union.mp hz with hzP | hzQ
    · obtain ⟨z₀, hz₀, rfl⟩ := hmemP z hzP
      have := hqiso z₀
      exact (isRegularLocalRing_stalk_iff_of_isIso_stalkMap q z₀).mp
        (hTreg z₀ (Finset.mem_filter.mp hz₀).1)
    · obtain ⟨w, hw, rfl⟩ := hmemQ z hzQ
      have := hstalkAway _ (hσne w hw)
      refine (isRegularLocalRing_stalk_iff_of_isIso_stalkMap (blowUpToBase M) (σ w hw)).mpr ?_
      rw [hσ w hw]
      exact hWreg w (Finset.mem_of_mem_erase hw)
  · intro z hz
    rcases Finset.mem_union.mp hz with hzP | hzQ
    · obtain ⟨z₀, hz₀, rfl⟩ := hmemP z hzP
      have := hqiso z₀
      exact (ringKrullDim_stalk_eq_of_isIso_stalkMap q z₀).symm.trans
        (hTdim z₀ (Finset.mem_filter.mp hz₀).1)
    · obtain ⟨w, hw, rfl⟩ := hmemQ z hzQ
      have := hstalkAway _ (hσne w hw)
      rw [ringKrullDim_stalk_eq_of_isIso_stalkMap (blowUpToBase M) (σ w hw), hσ w hw]
      exact hWdim w (Finset.mem_of_mem_erase hw)
  · intro z hz
    by_cases hzy : (blowUpToBase M).base z = y
    · obtain ⟨z₀, rfl⟩ := hfib hzy
      have hz₀ : z₀ ∈ (J₀.support : Set _) := by
        rwa [← hKq, Scheme.IdealSheafData.support_comap]
      refine Finset.mem_coe.mpr (Finset.mem_union_left _ ?_)
      rw [hPdef]
      exact Finset.mem_image.mpr ⟨z₀, Finset.mem_filter.mpr ⟨hTsupp hz₀, hz₀⟩, rfl⟩
    · have hwW : (blowUpToBase M).base z ∈ W.erase y :=
        Finset.mem_erase.mpr ⟨hzy, Finset.mem_coe.mp (hJW (hKsupp z hz))⟩
      have heq := hinjAway (σ _ hwW) z (hσne _ hwW) (by rw [hσ _ hwW])
      rw [← heq]
      exact Finset.mem_coe.mpr (Finset.mem_union_right _ (hQmem _ hwW))
  · intro z hz
    rcases Finset.mem_union.mp hz with hzP | hzQ
    · rw [hPfib z hzP]; exact hyW
    · obtain ⟨w, hw, rfl⟩ := hmemQ z hzQ
      rw [hσ w hw]
      exact Finset.mem_of_mem_erase hw
  · refine totalColength_lt_of_split W J K P Q y hyW ?_ ?_ ?_ ?_
    · refine Finset.disjoint_left.mpr fun z hzP hzQ => ?_
      exact hQfib z hzQ (hPfib z hzP)
    · have e1 : ∑ z ∈ P, Module.length ↥((blowUp M).presheaf.stalk z)
            (↥((blowUp M).presheaf.stalk z) ⧸ IdealSheafData.stalk K z) =
          ∑ z₀ ∈ T', Module.length ↥((blowUp (M.comap (Y.fromSpecStalk y))).presheaf.stalk z₀)
            (↥((blowUp (M.comap (Y.fromSpecStalk y))).presheaf.stalk z₀) ⧸
              IdealSheafData.stalk J₀ z₀) := by
        rw [hPdef, Finset.sum_image fun a _ b _ h => hqemb.injective h]
        refine Finset.sum_congr rfl fun z₀ _ => ?_
        rw [← hKq]
        exact (length_stalk_quotient_comap_of_isIso_stalkMap q K z₀ (hqiso z₀)).symm
      have e2 : ∑ z₀ ∈ T', Module.length
            ↥((blowUp (M.comap (Y.fromSpecStalk y))).presheaf.stalk z₀)
            (↥((blowUp (M.comap (Y.fromSpecStalk y))).presheaf.stalk z₀) ⧸
              IdealSheafData.stalk J₀ z₀) =
          ∑ z₀ ∈ T, Module.length
            ↥((blowUp (M.comap (Y.fromSpecStalk y))).presheaf.stalk z₀)
            (↥((blowUp (M.comap (Y.fromSpecStalk y))).presheaf.stalk z₀) ⧸
              IdealSheafData.stalk J₀ z₀) := by
        refine Finset.sum_subset (by rw [hT']; exact Finset.filter_subset _ _) ?_
        intro z₀ hz₀T hz₀
        refine Stacks.ResolutionOfSurfaces.length_quotient_stalk_eq_zero_of_notMem_support J₀ ?_
        intro hmem
        exact hz₀ (by rw [hT']; exact Finset.mem_filter.mpr ⟨hz₀T, hmem⟩)
      rwa [e1, e2]
    · refine Finset.sum_bij (fun z _ => (blowUpToBase M).base z) ?_ ?_ ?_ ?_
      · intro z hz
        obtain ⟨w, hw, rfl⟩ := hmemQ z hz
        rw [hσ w hw]
        exact hw
      · intro z₁ hz₁ z₂ _ h
        obtain ⟨w, hw, rfl⟩ := hmemQ z₁ hz₁
        exact hinjAway _ z₂ (hσne w hw) h
      · intro w hw
        exact ⟨σ w hw, hQmem w hw, hσ w hw⟩
      · intro z hz
        have := hstalkAway z (by rw [hMsupp, Set.mem_singleton_iff]; exact hQfib z hz)
        rw [← hstalkK z (hQfib z hz)]
        exact length_stalk_quotient_comap_of_isIso_stalkMap (blowUpToBase M) J z inferInstance
    · intro w hw
      have := hWreg w (Finset.mem_of_mem_erase hw)
      have : IsNoetherianRing ↥(Y.presheaf.stalk w) := inferInstance
      exact (length_quotient_stalk_lt_top J hJclosed w inferInstance).ne

/-! ### The local splitting for `Stacks.Blowup.blowUp` -/

/-- The local splitting of [Stacks, Tag 0AGT] stated for `Stacks.Blowup.blowUp`, the blowup
construction carrying the affine-chart API, rather than for `AlgebraicGeometry.blowUp`. -/
public abbrev LocalColengthSplittingChart : Prop :=
  ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A], ringKrullDim A = 2 →
    ∀ (L : Ideal A) (n : ℕ), IsLocalRing.maximalIdeal A ^ n ≤ L →
      L ≤ IsLocalRing.maximalIdeal A →
      ∃ (d : ℕ) (T : Finset (Stacks.Blowup.blowUp
            (Stacks.ResolutionOfSurfaces.CartierDescent.centre A)))
        (J' : (Stacks.Blowup.blowUp
            (Stacks.ResolutionOfSurfaces.CartierDescent.centre A)).IdealSheafData),
        0 < d ∧
        Stacks.Blowup.exceptionalIdeal
            (Stacks.ResolutionOfSurfaces.CartierDescent.centre A) ^ d * J' =
          (Stacks.ResolutionOfSurfaces.CartierDescent.idealSheafOf A L).comap
            (Stacks.Blowup.blowUpToBase
              (Stacks.ResolutionOfSurfaces.CartierDescent.centre A)) ∧
        ((J'.support : Set (Stacks.Blowup.blowUp
            (Stacks.ResolutionOfSurfaces.CartierDescent.centre A))) ⊆
          (T : Set (Stacks.Blowup.blowUp
            (Stacks.ResolutionOfSurfaces.CartierDescent.centre A)))) ∧
        (∀ z ∈ T, IsClosed ({z} : Set (Stacks.Blowup.blowUp
            (Stacks.ResolutionOfSurfaces.CartierDescent.centre A)))) ∧
        (∀ z ∈ T, IsRegularLocalRing ((Stacks.Blowup.blowUp
            (Stacks.ResolutionOfSurfaces.CartierDescent.centre A)).presheaf.stalk z)) ∧
        (∀ z ∈ T, ringKrullDim ((Stacks.Blowup.blowUp
            (Stacks.ResolutionOfSurfaces.CartierDescent.centre A)).presheaf.stalk z) = 2) ∧
        ∑ z ∈ T, Module.length ↥((Stacks.Blowup.blowUp
            (Stacks.ResolutionOfSurfaces.CartierDescent.centre A)).presheaf.stalk z)
          (↥((Stacks.Blowup.blowUp
            (Stacks.ResolutionOfSurfaces.CartierDescent.centre A)).presheaf.stalk z) ⧸
              AlgebraicGeometry.IdealSheafData.stalk J' z) <
          Module.length A (A ⧸ L)

/-- The local splitting of [Stacks, Tag 0AGT] stated for `Stacks.Blowup.blowUp` implies the one
stated for `AlgebraicGeometry.blowUp`. -/
public theorem localColengthSplitting_of_chart (h : LocalColengthSplittingChart.{u}) :
    LocalColengthSplitting.{u} := by
  classical
  intro A _ _ hdim L n hn hL
  obtain ⟨d, T₀, J₀, hd, hsplit, hTsupp, hTclosed, hTreg, hTdim, hTsum⟩ := h A hdim L n hn hL
  have hbij : Function.Bijective (Blowup.blowUpIso (centre A)).hom.base := by
    simpa only [Scheme.coe_homeoOfIso] using
      (Scheme.homeoOfIso (Blowup.blowUpIso (centre A))).bijective
  have himg : ∀ z₀ : Blowup.blowUp (centre A), IsClosed ({z₀} : Set (Blowup.blowUp (centre A))) →
      IsClosed ({(Blowup.blowUpIso (centre A)).hom.base z₀} :
        Set (AlgebraicGeometry.blowUp (centre A))) := by
    intro z₀ hz₀
    simpa only [Set.image_singleton, Scheme.coe_homeoOfIso] using
      (Scheme.homeoOfIso (Blowup.blowUpIso (centre A))).isClosedMap {z₀} hz₀
  have hJ'g : (J₀.comap (inv (Blowup.blowUpIso (centre A)).hom)).comap
      (Blowup.blowUpIso (centre A)).hom = J₀ := by
    rw [← Scheme.IdealSheafData.comap_comp, IsIso.hom_inv_id, Scheme.IdealSheafData.comap_id]
  refine ⟨d, T₀.image (Blowup.blowUpIso (centre A)).hom.base,
    J₀.comap (inv (Blowup.blowUpIso (centre A)).hom), hd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine eq_of_comap_blowUpIso_hom_eq (centre A) ?_
    rw [comap_blowUpIso_hom_mul, comap_blowUpIso_hom_exceptionalIdeal_pow,
      comap_blowUpIso_hom_comap_blowUpToBase, hJ'g]
    exact hsplit
  · intro z hz
    obtain ⟨z₀, rfl⟩ := hbij.2 z
    have hz₀ : z₀ ∈ ((J₀.comap (inv (Blowup.blowUpIso (centre A)).hom)).comap
        (Blowup.blowUpIso (centre A)).hom).support := by
      rwa [Scheme.IdealSheafData.support_comap]
    rw [hJ'g] at hz₀
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨z₀, Finset.mem_coe.mp (hTsupp hz₀), rfl⟩)
  · intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := Finset.mem_image.mp hz
    exact himg z₀ (hTclosed z₀ hz₀)
  · intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := Finset.mem_image.mp hz
    exact (isRegularLocalRing_stalk_iff (centre A) z₀).mp (hTreg z₀ hz₀)
  · intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := Finset.mem_image.mp hz
    exact (ringKrullDim_stalk_eq (centre A) z₀).symm.trans (hTdim z₀ hz₀)
  · rw [Finset.sum_image fun a _ b _ hab => hbij.1 hab]
    refine lt_of_eq_of_lt (Finset.sum_congr rfl fun z₀ _ => ?_) hTsum
    have e := length_stalk_quotient_comap_blowUpIso_hom (centre A)
      (J₀.comap (inv (Blowup.blowUpIso (centre A)).hom)) z₀
    rw [hJ'g] at e
    exact e.symm

end Stacks.ResolutionOfSurfaces.CartierDescent

end
