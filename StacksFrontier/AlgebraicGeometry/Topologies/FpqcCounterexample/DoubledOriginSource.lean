module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.Scheme.Separation.DoubledOrigin

/-!
# A flat surjection onto the doubled-origin scheme

Over a field `k`, let `X` be countably infinite-dimensional affine space with its origin doubled.
This file sets up the morphism which, in the standard counterexample, is flat and surjective and
satisfies the pointwise quasi-compact-neighbourhood condition yet is not an fpqc covering: the
source is the disjoint union of the first affine chart with the spectrum of the local ring of the
second chart at its origin, and the morphism is the chart inclusion on the first summand and the
canonical map from the local scheme followed by the second chart inclusion on the second.

Flatness holds summand by summand: the first summand is an open immersion, and the second is a
localization followed by an open immersion. Surjectivity holds because a point of `X` not in the
doubled origin lies in both charts and so is hit by the first summand, while the second origin is
the image of the closed point of the local scheme.

## Main definitions

* `AlgebraicGeometry.DoubledOriginSource`: a ground field together with a doubled-origin gluing
  datum over it, packaging the affine space, the doubled-origin scheme, the origin, the two
  chart inclusions, the source and the morphism.

## Main results

* `AlgebraicGeometry.DoubledOriginSource.flat_map`: the morphism is flat.
* `AlgebraicGeometry.DoubledOriginSource.surjective_map`: the morphism is surjective.

## Implementation notes

Flatness and surjectivity are the morphism properties `AlgebraicGeometry.Flat` and
`AlgebraicGeometry.Surjective`. Both affine charts are identified with the same
`Spec k[t₀, t₁, …]`, with indices `0` and `1` for the first and second chart; evaluation of every
coordinate at zero defines their common model origin.

The gluing datum is a field of `DoubledOriginSource` rather than a fixed construction, so the
results below hold for any datum exhibiting a doubled-origin scheme. The charts of such a datum
are the canonical open immersions of the underlying scheme gluing datum composed with the chart
identifications, which is what `DoubledOriginData.chart` records; `surjective_map` therefore
transports a point along the chart identification before applying joint surjectivity of those
canonical immersions.

## References

* [Stacks Project, Tag 01KL](https://stacks.math.columbia.edu/tag/01KL)
* [Stacks Project, Tag 0H7E](https://stacks.math.columbia.edu/tag/0H7E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- A ground field together with a doubled-origin gluing datum over it. -/
public structure DoubledOriginSource where
  /-- The ground field. -/
  k : Type u
  /-- Its field structure. -/
  [field : Field k]
  /-- The gluing datum exhibiting the target as infinite-dimensional affine space with its
  origin doubled. -/
  gluing : DoubledOriginData k

attribute [instance] DoubledOriginSource.field

namespace DoubledOriginSource

/-- The affine space used for both charts. -/
public abbrev affine (S : DoubledOriginSource.{u}) : Scheme.{u} :=
  infiniteAffineSpace S.k

/-- The infinite-dimensional affine space with its origin doubled. -/
public abbrev target (S : DoubledOriginSource.{u}) : Scheme.{u} :=
  S.gluing.scheme

/-- The origin of either affine chart, obtained by evaluating all variables at zero. -/
public def origin (S : DoubledOriginSource.{u}) : S.affine :=
  PrimeSpectrum.comap (MvPolynomial.eval 0) (⊤ : PrimeSpectrum S.k)

/-- The first affine chart included into the doubled-origin scheme. -/
public def firstChart (S : DoubledOriginSource.{u}) : S.affine ⟶ S.target :=
  S.gluing.chart 0

/-- The second affine chart included into the doubled-origin scheme. -/
public def secondChart (S : DoubledOriginSource.{u}) : S.affine ⟶ S.target :=
  S.gluing.chart 1

/-- The first chart together with the local scheme of the second chart at its origin. -/
public abbrev source (S : DoubledOriginSource.{u}) : Scheme.{u} :=
  S.affine ⨿ Spec (.of (S.affine.presheaf.stalk S.origin))

/-- The map from the first chart and the local scheme of the second chart into the
doubled-origin scheme. -/
public def map (S : DoubledOriginSource.{u}) : S.source ⟶ S.target :=
  coprod.desc S.firstChart (S.affine.fromSpecStalk S.origin ≫ S.secondChart)

/-- The canonical map from the first chart and the local scheme of the second
chart to the doubled-origin scheme is flat. -/
@[stacks 0H7E "flatness"]
public instance flat_map (S : DoubledOriginSource.{u}) : Flat S.map := by
  have : Flat S.firstChart := inferInstanceAs (Flat (S.gluing.chart 0))
  have : Flat (S.affine.fromSpecStalk S.origin) := flat_fromSpecStalk S.affine S.origin
  have : Flat S.secondChart := inferInstanceAs (Flat (S.gluing.chart 1))
  have : IsZariskiLocalAtSource (@AlgebraicGeometry.Flat) :=
    AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource
  refine (IsZariskiLocalAtSource.iff_of_openCover (P := @Flat) (f := S.map)
    (coprodOpenCover.{u, 0} S.affine (Spec (.of (S.affine.presheaf.stalk S.origin))))).2 ?_
  intro i
  cases i with
  | inl _ => simpa [coprodOpenCover, DoubledOriginSource.map, coprod.inl_desc]
      using (inferInstance : Flat S.firstChart)
  | inr _ => simpa [coprodOpenCover, DoubledOriginSource.map, coprod.inr_desc]
      using (inferInstance : Flat (S.affine.fromSpecStalk S.origin ≫ S.secondChart))

/-- A polynomial vanishes at the origin exactly when it lies in the ideal generated by the
coordinates. -/
private lemma eval_zero_ker_eq_span_X (k : Type u) [Field k] :
    RingHom.ker (MvPolynomial.eval (0 : ℕ → k)) =
      Ideal.span (MvPolynomial.X '' (Set.univ : Set ℕ)) := by
  ext f
  rw [RingHom.mem_ker, MvPolynomial.eval_zero, MvPolynomial.mem_ideal_span_X_image]
  refine ⟨fun hf m hm => ?_, fun hf => ?_⟩
  · have hm0 : m ≠ 0 := by
      rintro rfl
      exact MvPolynomial.mem_support_iff.mp hm (by simpa [MvPolynomial.constantCoeff_eq] using hf)
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hm0
    exact ⟨i, Set.mem_univ _, Finsupp.mem_support_iff.mp hi⟩
  · by_contra hcoeff
    have h0 : (0 : ℕ →₀ ℕ) ∈ f.support :=
      MvPolynomial.mem_support_iff.mpr (by simpa [MvPolynomial.constantCoeff_eq] using hcoeff)
    obtain ⟨i, _, hi⟩ := hf 0 h0
    simp at hi

/-- A prime containing every coordinate is the origin. -/
private lemma origin_eq_of_variables_mem (S : DoubledOriginSource.{u})
    (p : PrimeSpectrum (MvPolynomial ℕ S.k))
    (hp : ∀ i, MvPolynomial.X i ∈ p.asIdeal) :
    p = S.origin := by
  apply PrimeSpectrum.ext
  show p.asIdeal = (DoubledOriginSource.origin S).asIdeal
  simp only [DoubledOriginSource.origin, PrimeSpectrum.comap_asIdeal,
    IsLocalRing.PrimeSpectrum.asIdeal_top, IsLocalRing.maximalIdeal_eq_bot,
    ← RingHom.ker_eq_comap_bot]
  symm
  apply (RingHom.ker_isMaximal_of_surjective (MvPolynomial.eval (0 : ℕ → S.k))
    fun a => ⟨MvPolynomial.C a, by simp⟩).eq_of_le p.2.ne_top
  rw [eval_zero_ker_eq_span_X]
  refine Ideal.span_le.2 ?_
  rintro _ ⟨i, -, rfl⟩
  exact hp i

/-- A point of the affine space other than the origin lies in the punctured affine space. -/
private lemma punctured_of_ne_origin (S : DoubledOriginSource.{u})
    (x : S.affine) (hx : x ≠ S.origin) :
    x ∈ puncturedInfiniteAffineSpace S.k := by
  show x ∈ ⨆ i : ℕ,
    S.affine.basicOpen ((Scheme.ΓSpecIso (.of (MvPolynomial ℕ S.k))).inv (MvPolynomial.X i))
  rw [TopologicalSpace.Opens.mem_iSup]
  by_contra! h
  have hvars : ∀ i, MvPolynomial.X i ∈ (x : PrimeSpectrum (MvPolynomial ℕ S.k)).asIdeal := by
    intro i
    by_contra hi
    apply h i
    rw [AlgebraicGeometry.basicOpen_eq_of_affine]
    exact (PrimeSpectrum.mem_basicOpen _ x).2 hi
  exact hx (origin_eq_of_variables_mem S x hvars)

/-- A chart of a doubled-origin datum, precomposed with its chart identification, is the
corresponding canonical open immersion of the underlying gluing datum. -/
private lemma chartIso_comp_chart {k : Type u} [Field k] (D : DoubledOriginData k) (i : Fin 2) :
    (D.chartIso i).hom ≫ D.chart i = D.glueData.ι (D.indexEquiv i) := by
  rw [DoubledOriginData.chart, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The two chart inclusions agree on the punctured affine space. -/
private lemma charts_agree_on_punctured (S : DoubledOriginSource.{u})
    (y : S.affine)
    (hy : y ∈ puncturedInfiniteAffineSpace S.k) :
    S.firstChart y = S.secondChart y := by
  let D := S.gluing
  let i₀ := D.indexEquiv 0
  let i₁ := D.indexEquiv 1
  let z : doubledOriginOverlap S.k 0 1 := ⟨y, hy⟩
  have hf : ∀ a b (w : doubledOriginOverlap S.k a b),
      D.glueData.f (D.indexEquiv a) (D.indexEquiv b) ((D.overlapIso a b).hom w) =
        (D.chartIso a).inv (doubledOriginOverlapι S.k a b w) := by
    intro a b w
    have h := congrArg (fun f : _ ⟶ S.affine => f w) (D.overlap_f a b)
    simp only [Scheme.Hom.comp_apply] at h
    rw [← h]
    simp
  have hcharts : D.glueData.ι i₀ ((D.chartIso 0).inv y) =
      D.glueData.ι i₁ ((D.chartIso 1).inv y) := by
    apply (D.glueData.ι_eq_iff i₀ i₁ _ _).2
    refine ⟨(D.overlapIso 0 1).hom z, hf 0 1 z, ?_⟩
    have hval : D.glueData.t i₀ i₁ ((D.overlapIso 0 1).hom z) =
        (D.overlapIso 1 0).hom (doubledOriginOverlapSwap S.k 0 1 z) := by
      have ht := congrArg (fun f : doubledOriginOverlap S.k 0 1 ⟶ _ => f z) (D.transition 0 1)
      simp only [Scheme.Hom.comp_apply] at ht
      rw [← ht]
      simp [i₀, i₁]
    rw [Scheme.Hom.comp_apply, hval, hf 1 0]
    rfl
  exact hcharts

/-- The canonical map from an affine chart and the local spectrum covers the
scheme with doubled origin. -/
@[stacks 0H7E "surjectivity"]
public theorem surjective_map (S : DoubledOriginSource.{u}) :
    Surjective S.map := by
  refine ⟨fun x => ?_⟩
  obtain ⟨j, y, hy⟩ := S.gluing.glueData.ι_jointly_surjective x
  obtain ⟨i, rfl⟩ : ∃ i, S.gluing.indexEquiv i = j :=
    ⟨S.gluing.indexEquiv.symm j, S.gluing.indexEquiv.apply_symm_apply j⟩
  have hchart : S.gluing.chart i ((S.gluing.chartIso i).hom y) = x := by
    have h := congrArg (fun f : _ ⟶ S.target => f y) (chartIso_comp_chart S.gluing i)
    simpa only [Scheme.Hom.comp_apply] using h.trans hy
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  set y' : S.affine := (S.gluing.chartIso i).hom y with hy'
  have hinl : S.firstChart y' = x → ∃ a, S.map a = x := fun h => by
    refine ⟨(coprod.inl : S.affine ⟶ S.source) y', ?_⟩
    show (coprod.inl ≫ S.map) y' = x
    rw [DoubledOriginSource.map, coprod.inl_desc]
    exact h
  rcases hi with rfl | rfl
  · exact hinl hchart
  · by_cases hyOrigin : y' = S.origin
    · refine ⟨(coprod.inr : Spec (.of (S.affine.presheaf.stalk S.origin)) ⟶ S.source)
        (IsLocalRing.closedPoint _), ?_⟩
      show (coprod.inr ≫ S.map) (IsLocalRing.closedPoint _) = x
      rw [DoubledOriginSource.map, coprod.inr_desc]
      show S.secondChart (S.affine.fromSpecStalk S.origin
        (IsLocalRing.closedPoint _)) = x
      rw [Scheme.fromSpecStalk_closedPoint]
      show (S.gluing.chart 1) S.origin = x
      rw [← hyOrigin]
      exact hchart
    · exact hinl ((charts_agree_on_punctured S y' (punctured_of_ne_origin S y' hyOrigin)).trans
        hchart)

end DoubledOriginSource

end AlgebraicGeometry

end
