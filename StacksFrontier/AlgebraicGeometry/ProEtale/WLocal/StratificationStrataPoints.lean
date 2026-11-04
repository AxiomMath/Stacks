module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationLimit
public import StacksCore.Tactic.StacksAttribute

/-!
# Points of the closed strata of a finite vanishing stratification

For a commutative ring `A` and a finite subset `E ⊆ A`, the closed stratum `Z_E` of the
stratification of `Spec A` by the vanishing patterns of `E` is a finite coproduct of affine
schemes, one for each vanishing pattern `E' ⊆ E`. This file describes its points: each one lies
in exactly one summand, at a prime of that summand's coordinate ring, and its image in `Spec A`
is the contraction of that prime along the coordinate map of the stratum.

## Main definitions

* `AlgebraicGeometry.ProEtale.specPointEquiv`: the points of `Spec R` are the primes of `R`.
* `AlgebraicGeometry.ProEtale.closedStrataPoint`: the point of `Z_E` in a given summand
  determined by a prime of that summand's coordinate ring.
* `AlgebraicGeometry.ProEtale.closedStrataToBase`: the canonical map `Z_E ⟶ Spec A`.

## Main results

* `AlgebraicGeometry.ProEtale.exists_closedStrataPoint_eq`: every point of `Z_E` arises this way.
* `AlgebraicGeometry.ProEtale.closedStrataMap_point_formula`: the image in `Spec A` of such a
  point is the contraction of its prime along the coordinate map of the stratum.
* `AlgebraicGeometry.ProEtale.closedStrataMap_mem_component`: such a point lands in the clopen
  piece of `X_E` cut out by the projection onto its summand.
* `AlgebraicGeometry.ProEtale.stratumIndex_eq_of_mem`: a point of `Spec A` lies in at most one
  stratum.
* `AlgebraicGeometry.ProEtale.bijective_closedStrataToBase`: the closed stratum `Z_E` maps
  bijectively onto `Spec A`.
* `AlgebraicGeometry.ProEtale.closedDiagram_hasAffineTransitions`: the transition morphisms of
  the inverse system of closed strata are affine.
* `AlgebraicGeometry.ProEtale.inclusion_stage_factor`: the map from the limiting closed
  subscheme to `Spec A` factors through every finite closed stratum.

## Implementation notes

The underlying set of `Spec R` is Mathlib's `PrimeSpectrum R`, but the two are not syntactically
equal, so the identification is packaged as an equivalence whose round trips hold by `rfl`.

## References

* [Stacks Project, Tag 0971](https://stacks.math.columbia.edu/tag/0971)
* [Stacks Project, Tag 0974](https://stacks.math.columbia.edu/tag/0974)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.ProEtale

open CategoryTheory CategoryTheory.Limits

universe u

variable {A : Type u} [CommRing A]

/-- The points of `Spec R` are the primes of `R`. -/
def specPointEquiv (R : Type u) [CommRing R] : PrimeSpectrum R ≃ Spec (.of R) where
  toFun p := OrderDual.ofDual (primeSpectrumOrderIsoSpec R p)
  invFun x := OrderDual.ofDual (specOrderIsoPrimeSpectrum (.of R) x)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reading points of affine spectra as primes turns `Spec.map` into contraction of primes. -/
theorem specMap_specPointEquiv {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PrimeSpectrum S) :
    (Spec.map (CommRingCat.ofHom f)).base (specPointEquiv S p) =
      specPointEquiv R (PrimeSpectrum.comap f p) :=
  (specPointEquiv R).injective rfl

/-- The map out of a coproduct of schemes, evaluated on a point of one summand. -/
theorem sigmaDesc_apply {ι : Type u} (X : ι → Scheme) {Y : Scheme}
    (f : ∀ i, X i ⟶ Y) (i : ι) (x : X i) :
    (Sigma.desc f).base (Sigma.ι X i x) = (f i).base x := by
  simpa only [Scheme.Hom.comp_apply] using congrArg (fun g => g x) (Sigma.ι_desc f i)

/-- The coordinate ring of `D(f) ∩ V(I)` has injective contraction of primes into `Spec A`. -/
theorem locallyClosedCoordinateMap_comap_injective (I : Ideal A) (f : A) :
    Function.Injective (PrimeSpectrum.comap (locallyClosedCoordinateMap I f)) := by
  rw [locallyClosedCoordinateMap, PrimeSpectrum.comap_comp]
  intro q q' h
  exact (PrimeSpectrum.localization_comap_isEmbedding (locallyClosedCoordinateRing I f)
      (Submonoid.powers (Ideal.Quotient.mk I f))).injective
    ((PrimeSpectrum.comap_injective_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective) h)

/-- The point of `Z_E` in the summand indexed by the vanishing pattern `E'` determined by a
prime of the coordinate ring of that stratum. -/
def closedStrataPoint (E : Finset A) (i : {E' : Finset A // E' ⊆ E})
    (q : PrimeSpectrum (stratumCoordinateRing E i)) : closedStrata E :=
  (Sigma.ι (fun j : {E' : Finset A // E' ⊆ E} =>
    Spec (.of (stratumCoordinateRing E j))) i).base (specPointEquiv _ q)

/-- Every point of `Z_E` lies in one of the summands, at a prime of its coordinate ring. -/
theorem exists_closedStrataPoint_eq (E : Finset A) (w : closedStrata E) :
    ∃ (i : {E' : Finset A // E' ⊆ E}) (q : PrimeSpectrum (stratumCoordinateRing E i)),
      closedStrataPoint E i q = w := by
  obtain ⟨⟨i, x⟩, hx⟩ := (sigmaMk fun j : {E' : Finset A // E' ⊆ E} =>
    Spec (.of (stratumCoordinateRing E j))).surjective w
  refine ⟨i, (specPointEquiv _).symm x, ?_⟩
  show (Sigma.ι (fun j : {E' : Finset A // E' ⊆ E} =>
    Spec (.of (stratumCoordinateRing E j))) i).base x = w
  exact (sigmaMk_mk (fun j : {E' : Finset A // E' ⊆ E} =>
    Spec (.of (stratumCoordinateRing E j))) i x).symm.trans hx

/-- On the summand indexed by `E'`, the map `Z_E ⟶ X_E` is the spectrum of the coordinate map
of that stratum followed by the `E'`-th projection of the product ring `A_E`. -/
theorem closedStrataMap_closedStrataPoint (E : Finset A)
    (i : {E' : Finset A // E' ⊆ E}) (q : PrimeSpectrum (stratumCoordinateRing E i)) :
    (closedStrataMap E).base (closedStrataPoint E i q) =
      (Spec.map (CommRingCat.ofHom (localizationToCoordinateRing (stratumIdeal E i)
            (stratumOpenElement i.val))) ≫
          Spec.map (CommRingCat.ofHom (Pi.evalRingHom
            (fun j : {E' : Finset A // E' ⊆ E} =>
              localizationRing (stratumIdeal E j) (stratumOpenElement j.val)) i))).base
        (specPointEquiv _ q) :=
  sigmaDesc_apply (fun j : {E' : Finset A // E' ⊆ E} =>
      Spec (.of (stratumCoordinateRing E j)))
    (fun j => Spec.map (CommRingCat.ofHom (localizationToCoordinateRing (stratumIdeal E j)
        (stratumOpenElement j.val))) ≫
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom
        (fun k : {E' : Finset A // E' ⊆ E} =>
          localizationRing (stratumIdeal E k) (stratumOpenElement k.val)) j)))
    i (specPointEquiv _ q)

/-- The image in `Spec A` of a point of the stratum indexed by `E'` is the prime it contracts
to along the coordinate map of that stratum. -/
theorem closedStrataMap_point_formula (E : Finset A) (i : {E' : Finset A // E' ⊆ E})
    (q : PrimeSpectrum (stratumCoordinateRing E i)) :
    (closedStrataMap E ≫ Spec.map (CommRingCat.ofHom (stratificationAlgebraMap E))).base
        (closedStrataPoint E i q) =
      specPointEquiv A (PrimeSpectrum.comap
        (locallyClosedCoordinateMap (stratumIdeal E i) (stratumOpenElement i.val)) q) := by
  rw [Scheme.Hom.comp_apply, closedStrataMap_closedStrataPoint, Scheme.Hom.comp_apply]
  simp only [specMap_specPointEquiv]
  refine congrArg (specPointEquiv A) ?_
  rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
  congr 1
  ext a
  show localizationToCoordinateRing _ _ (algebraMap A (localizationRing _ _) a) = _
  exact IsLocalization.lift_eq _ _

/-- A point of the stratum indexed by `E'` lands in the clopen piece of `X_E` cut out by the
`E'`-th projection. -/
theorem closedStrataMap_mem_component (E : Finset A) (i : {E' : Finset A // E' ⊆ E})
    (q : PrimeSpectrum (stratumCoordinateRing E i)) :
    (closedStrataMap E).base (closedStrataPoint E i q) ∈
      Set.range (PrimeSpectrum.comap (Pi.evalRingHom
        (fun j : {E' : Finset A // E' ⊆ E} =>
          localizationRing (stratumIdeal E j) (stratumOpenElement j.val)) i)) := by
  rw [closedStrataMap_closedStrataPoint, Scheme.Hom.comp_apply]
  simp only [specMap_specPointEquiv]
  exact ⟨PrimeSpectrum.comap (localizationToCoordinateRing (stratumIdeal E i)
    (stratumOpenElement i.val)) q, rfl⟩

/-- A point of `Spec A` lies in at most one stratum of a finite stratification. -/
theorem stratumIndex_eq_of_mem (E : Finset A) (i j : {E' : Finset A // E' ⊆ E})
    (p : PrimeSpectrum A)
    (hi : p ∈ locallyClosedPoints (stratumIdeal E i) (stratumOpenElement i.val))
    (hj : p ∈ locallyClosedPoints (stratumIdeal E j) (stratumOpenElement j.val)) : i = j := by
  classical
  have key : ∀ k : {E' : Finset A // E' ⊆ E},
      p ∈ locallyClosedPoints (stratumIdeal E k) (stratumOpenElement k.val) →
        ∀ a ∈ E, (a ∈ k.val ↔ a ∉ p.asIdeal) := by
    intro k hk a haE
    refine ⟨fun hak hap => hk.2 ?_, fun hap => ?_⟩
    · simpa [stratumOpenElement] using p.isPrime.prod_mem_iff.mpr ⟨a, hak, hap⟩
    · by_contra hakn
      exact hap (hk.1 (Ideal.subset_span (Finset.mem_sdiff.mpr ⟨haE, hakn⟩)))
  refine Subtype.ext (Finset.ext fun a => ?_)
  by_cases haE : a ∈ E
  · rw [key i hi a haE, key j hj a haE]
  · exact iff_of_false (fun h => haE (i.2 h)) (fun h => haE (j.2 h))

/-- The vanishing pattern of `E` at a point of `Spec A`: the elements of `E` not vanishing
there. -/
def finiteStratumIndex (E : Finset A) (p : PrimeSpectrum A) : {E' : Finset A // E' ⊆ E} := by
  classical
  exact ⟨E.filter fun a => a ∉ p.asIdeal, Finset.filter_subset _ _⟩

/-- A point of `Spec A` lies in the stratum of its own vanishing pattern. -/
theorem finiteStratumIndex_mem (E : Finset A) (p : PrimeSpectrum A) :
    p ∈ locallyClosedPoints (stratumIdeal E (finiteStratumIndex E p))
      (stratumOpenElement (finiteStratumIndex E p).val) := by
  classical
  refine ⟨Ideal.span_le.2 fun a ha => ?_, fun hprod => ?_⟩
  · obtain ⟨haE, hain⟩ := Finset.mem_sdiff.mp ha
    by_contra hap
    exact hain (Finset.mem_filter.mpr ⟨haE, hap⟩)
  · obtain ⟨a, ha, hap⟩ := Ideal.IsPrime.prod_mem_iff.mp
      (by simpa [stratumOpenElement] using hprod)
    exact (Finset.mem_filter.mp ha).2 hap

/-- The closed stratum `Z_E` maps bijectively onto `Spec A`. -/
theorem bijective_closedStrataMap_comp_algebraMap (E : Finset A) :
    Function.Bijective (closedStrataMap E ≫
      Spec.map (CommRingCat.ofHom (stratificationAlgebraMap E))).base := by
  classical
  constructor
  · intro x y h
    obtain ⟨i, q, rfl⟩ := exists_closedStrataPoint_eq E x
    obtain ⟨j, r, rfl⟩ := exists_closedStrataPoint_eq E y
    rw [closedStrataMap_point_formula, closedStrataMap_point_formula] at h
    have hbase := (specPointEquiv A).injective h
    have hmem (k : {E' : Finset A // E' ⊆ E}) (r : PrimeSpectrum (stratumCoordinateRing E k)) :
        PrimeSpectrum.comap
          (locallyClosedCoordinateMap (stratumIdeal E k) (stratumOpenElement k.val)) r ∈
          locallyClosedPoints (stratumIdeal E k) (stratumOpenElement k.val) := by
      rw [← locallyClosedCoordinateMap_range]
      exact ⟨r, rfl⟩
    obtain rfl := stratumIndex_eq_of_mem E i j _ (hbase ▸ hmem i q) (hmem j r)
    obtain rfl := locallyClosedCoordinateMap_comap_injective (stratumIdeal E i)
      (stratumOpenElement i.val) hbase
    rfl
  · intro x
    obtain ⟨q, hq⟩ : (specPointEquiv A).symm x ∈ Set.range (PrimeSpectrum.comap
        (locallyClosedCoordinateMap
          (stratumIdeal E (finiteStratumIndex E ((specPointEquiv A).symm x)))
          (stratumOpenElement
            (finiteStratumIndex E ((specPointEquiv A).symm x)).val))) := by
      rw [locallyClosedCoordinateMap_range]
      exact finiteStratumIndex_mem E _
    refine ⟨closedStrataPoint E (finiteStratumIndex E ((specPointEquiv A).symm x)) q, ?_⟩
    rw [closedStrataMap_point_formula, hq]
    exact (specPointEquiv A).apply_symm_apply x

/-- The canonical map from the closed stratum `Z_E` to `Spec A`. -/
def closedStrataToBase (E : Finset A) : closedStrata E ⟶ Spec (.of A) :=
  closedStrataMap E ≫ Spec.map (CommRingCat.ofHom (stratificationAlgebraMap E))

/-- The image in `Spec A` of a point of the stratum indexed by `E'`. -/
theorem closedStrataToBase_closedStrataPoint (E : Finset A) (i : {E' : Finset A // E' ⊆ E})
    (q : PrimeSpectrum (stratumCoordinateRing E i)) :
    (closedStrataToBase E).base (closedStrataPoint E i q) =
      specPointEquiv A (PrimeSpectrum.comap
        (locallyClosedCoordinateMap (stratumIdeal E i) (stratumOpenElement i.val)) q) :=
  closedStrataMap_point_formula E i q

/-- The closed stratum `Z_E` maps bijectively onto `Spec A`. -/
theorem bijective_closedStrataToBase (E : Finset A) :
    Function.Bijective (closedStrataToBase E).base :=
  bijective_closedStrataMap_comp_algebraMap E

/-- `Spec` of a composite of ring maps is the composite of the `Spec` maps. -/
private theorem spec_map_ofHom_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (k : R →+* T) (h : g.comp f = k) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom k) := by
  subst h
  rw [← Spec.map_comp]
  rfl

/-- The transition morphisms of the closed strata are compatible with their maps to
`Spec A`. -/
theorem closedStrataTransition_comp_algebraMap (E₁ E₂ : Finset A) (h : E₁ ⊆ E₂) :
    (closedStrataTransition E₁ E₂ h).val ≫ closedStrataMap E₁ ≫
        Spec.map (CommRingCat.ofHom (stratificationAlgebraMap E₁)) =
      closedStrataMap E₂ ≫ Spec.map (CommRingCat.ofHom (stratificationAlgebraMap E₂)) := by
  rw [← Category.assoc, (closedStrataTransition E₁ E₂ h).property, Category.assoc,
    stratificationSchemeMap, spec_map_ofHom_comp _ _ _
      (stratificationRingMap_comp_algebraMap E₁ E₂ h)]

/-- The map from `Z` to `Spec A` factors through any finite closed stratum. -/
theorem inclusion_stage_factor (L : StratificationLimit A) (E : Finset A) :
    L.inclusion ≫ Spec.map (CommRingCat.ofHom (stratificationColimitAlgebraMap (A := A))) =
      L.closedProjection.app (Opposite.op E) ≫ (L.closedStage E).hom ≫ closedStrataMap E ≫
        Spec.map (CommRingCat.ofHom (stratificationAlgebraMap E)) := by
  have hinc : L.inclusion ≫ Spec.map (CommRingCat.ofHom (stratificationColimitMap E)) =
      L.closedProjection.app (Opposite.op E) ≫ (L.closedStage E).hom ≫ closedStrataMap E := by
    rw [← L.schemeProjection_spec E]
    exact L.inclusion_spec E
  rw [← spec_map_ofHom_comp _ _ _ (stratificationColimitMap_comp_algebraMap E),
    ← Category.assoc, hinc]
  rfl

/-- The transition morphisms of the closed strata commute with their maps to `Spec A`. -/
theorem closedStrataTransition_comp_closedStrataToBase (E₁ E₂ : Finset A) (h : E₁ ⊆ E₂) :
    (closedStrataTransition E₁ E₂ h).val ≫ closedStrataToBase E₁ = closedStrataToBase E₂ :=
  closedStrataTransition_comp_algebraMap E₁ E₂ h

/-- The transition morphisms of the inverse system of finite closed strata are affine. -/
theorem closedDiagram_hasAffineTransitions (L : StratificationLimit A) :
    ∀ {i j : (Finset A)ᵒᵖ} (f : i ⟶ j), IsAffineHom (L.closedDiagram.map f) := by
  intro i j f
  have : IsAffine (closedStrata i.unop) := closedStrata_isAffine i.unop
  have : IsAffine (closedStrata j.unop) := closedStrata_isAffine j.unop
  have : IsAffine (L.closedDiagram.obj i) := IsAffine.of_isIso (L.closedStage i.unop).hom
  have : IsAffine (L.closedDiagram.obj j) := IsAffine.of_isIso (L.closedStage j.unop).hom
  exact isAffineHom_of_isAffine (L.closedDiagram.map f)

/-- An isomorphism of schemes undoes its inverse on points. -/
theorem schemeIso_hom_inv_base_apply {X Y : Scheme} (e : X ≅ Y) (x : Y) :
    e.hom.base (e.inv.base x) = x := by
  simp

/-- An isomorphism of schemes is injective on points. -/
theorem schemeIso_base_injective {X Y : Scheme} (e : X ≅ Y) :
    Function.Injective e.hom.base := fun x y h => by
  simpa [Scheme.Hom.comp_apply] using congrArg e.inv.base h

end AlgebraicGeometry.ProEtale

end
