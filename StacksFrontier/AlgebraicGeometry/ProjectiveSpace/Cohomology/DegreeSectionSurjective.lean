module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionRing
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.ChartSectionsComparison

/-!
# The degree-`d` forms exhaust the global sections of `𝒪(d)` on projective space

Let `R` be a commutative ring, let `n d : ℕ`, and let `P = R[T₀, …, Tₙ]` carry its grading by
total degree. A homogeneous polynomial `a` of degree `d` determines a global section of `𝒪(d)`
on `ℙⁿ_R = Proj P`, the one whose value at every point is the fraction `a / 1`
(`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection`). This file proves that **every**
global section of `𝒪(d)` arises this way, over an arbitrary commutative ring.

The argument is the degree-zero computation of [Stacks, Tag 01XT] carried out on sections rather
than on cohomology. The sections of `𝒪(d)` over the standard open `D₊(∏_{i ∈ s} Tᵢ)` are the free
`R`-module on the degree-`d` Laurent monomials that are nonnegative outside `s`; all these charts
are submodules of one free module on all Laurent exponent vectors, and the restriction maps
between them are the inclusions. So the restrictions of a single global section to the charts
`D₊(Tᵢ)` are all the *same* element `u` of that ambient module: the charts `{i}` and `{j}` both
compare with the chart `{i, j}`. Hence `u` is allowed in every one-variable chart, so all its
exponents are nonnegative and it is a degree-`d` form `a`. Finally `a` and the given section have
the same restriction to each `D₊(Tᵢ)`, both being the fraction `a / 1`, and the `D₊(Tᵢ)` cover
`ℙⁿ_R`.

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.chartRestrict` — a global section of `𝒪(d)`, restricted to
  the standard open `D₊(∏_{i ∈ s} Tᵢ)`.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.twistChart_iInf_singleton_of_nonneg` — in nonnegative degree
  a Laurent monomial regular on every chart `D₊(Tᵢ)` is a polynomial monomial, for every `n`.
* `Stacks.ProjectiveSpace.Cohomology.exists_homogeneous_mk_eq` — an element of the polynomial
  chart is, read in any chart containing it, the fraction `a / 1` for a single degree-`d` form
  `a`.
* `Stacks.ProjectiveSpace.Cohomology.coe_chartSectionsAddEquivTwistChart_mono` — the monomial
  coordinates of a global section do not depend on which chart it is read in.
* `Stacks.ProjectiveSpace.Cohomology.exists_degreeSection_eq_of_commRing` — **every global
  section of `𝒪(d)` on `ℙⁿ_R` is the section of a form of degree `d`.**

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory TopologicalSpace
  Opposite

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjectiveSpace.Cohomology

attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-! ### Laurent monomials regular on every one-variable chart -/

/-- **A Laurent monomial of nonnegative total degree that is allowed in every chart `D₊(Tᵢ)` is a
polynomial monomial.** For `n > 0` the condition at an index other than `i` covers the index `i`;
for `n = 0` there is a single index and the conclusion is the nonnegativity of the degree. -/
theorem iInter_laurentMonomials_singleton_of_nonneg (n : ℕ) {d : ℤ} (hd : 0 ≤ d) :
    ⋂ i : Fin (n + 1), laurentMonomials n d {i}
      = laurentMonomials n d (∅ : Set (Fin (n + 1))) := by
  ext e
  simp only [Set.mem_iInter, mem_laurentMonomials, Set.mem_singleton_iff,
    Set.mem_empty_iff_false, not_false_eq_true, forall_const]
  refine ⟨fun h => ⟨(h 0).1, fun i => ?_⟩, fun h i => ⟨h.1, fun j _ => h.2 j⟩⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 : (∑ j : Fin 1, e j) = d := (h 0).1
    rw [Fin.sum_univ_one] at h0
    have hi : i = 0 := Fin.eq_zero i
    rw [hi]
    omega
  · obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), j ≠ i := by
      rcases eq_or_ne i 0 with hi | hi
      · exact ⟨⟨1, by omega⟩, by simp [hi, Fin.ext_iff]⟩
      · exact ⟨0, fun hji => hi hji.symm⟩
    exact (h j).2 i hj.symm

/-- **Stacks 01XT, the degree-zero chart intersection in nonnegative degree.** A Laurent section
of `𝒪(d)` with `0 ≤ d` that is regular on every standard open `D₊(Tᵢ)` is a polynomial
section. -/
theorem twistChart_iInf_singleton_of_nonneg (R : Type u) [CommRing R] (n : ℕ) {d : ℤ}
    (hd : 0 ≤ d) :
    ⨅ i : Fin (n + 1), twistChart R n d {i} = twistChart R n d (∅ : Set (Fin (n + 1))) := by
  rw [twistChart_iInf, iInter_laurentMonomials_singleton_of_nonneg n hd, twistChart]

/-- The exponent vector of the numerator of a Laurent monomial over the denominator `1`: the
exponents with their negative entries truncated, so for a nonnegative `e` the vector `e`
itself.

This is `Stacks.ProjectiveSpace.Cohomology.numExp_zero` of
`StacksFrontier/AlgebraicGeometry/ProjectiveSpace/Cohomology/PolynomialChartFractions.lean` with the
right-hand side written out instead of through `toNatExp`; the two are the same statement and
should become one declaration when that file and this one are brought into a common closure. -/
theorem numExp_zero_toNat {n : ℕ} (s : Finset (Fin (n + 1))) (e : Fin (n + 1) → ℤ) :
    numExp s e 0 = Finsupp.equivFunOnFinite.symm fun i => (e i).toNat := by
  refine Finsupp.ext fun i => ?_
  show (e i + (if i ∈ s then ((0 : ℕ) : ℤ) else 0)).toNat = (e i).toNat
  simp

/-! ### A polynomial chart element as a fraction with denominator one -/

/-- Fractions with denominator `1` add by adding their numerators. -/
theorem mk_one_add_mk_one {A : Type u} [CommRing A] {f : A} (x y : A) :
    (LocalizedModule.mk x (1 : Submonoid.powers f) : LocalizedModule.Away f A)
        + LocalizedModule.mk y 1
      = LocalizedModule.mk (x + y) 1 := by
  rw [LocalizedModule.mk_add_mk]
  simp

/-- **A Laurent section with no negative exponent is a polynomial.** An element of the chart with
no variable inverted is, read in any chart `s` that contains it, the fraction `a / 1` for one
homogeneous polynomial `a` of degree `d`, independent of `s`. -/
theorem exists_homogeneous_mk_eq (R : Type u) [CommRing R] (n d : ℕ)
    {u : (Fin (n + 1) → ℤ) →₀ R}
    (hu : u ∈ twistChart R n (d : ℤ) (∅ : Set (Fin (n + 1)))) :
    ∃ a : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d,
      ∀ (s : Finset (Fin (n + 1)))
        (hus : u ∈ twistChart R n (d : ℤ) (↑s : Set (Fin (n + 1)))),
        ((twistChartEquivTwistSections R n (d : ℤ) s ⟨u, hus⟩ :
            LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R)))
          = LocalizedModule.mk (a : MvPolynomial (Fin (n + 1)) R) 1 := by
  have hspan : twistChart R n (d : ℤ) (∅ : Set (Fin (n + 1)))
      = Submodule.span R
          ((fun e => Finsupp.single e (1 : R)) ''
            laurentMonomials n (d : ℤ) (∅ : Set (Fin (n + 1)))) :=
    Finsupp.supported_eq_span_single R _
  have hconv : ∀ z : (Fin (n + 1) → ℤ) →₀ R,
      z ∈ Submodule.span R
          ((fun e => Finsupp.single e (1 : R)) ''
            laurentMonomials n (d : ℤ) (∅ : Set (Fin (n + 1)))) →
      ∀ s : Finset (Fin (n + 1)), z ∈ twistChart R n (d : ℤ) (↑s : Set (Fin (n + 1))) :=
    fun z hz s => twistChart_mono (Set.empty_subset _) (by rwa [hspan])
  rw [hspan] at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨e, he, rfl⟩ := hx
      have hnonneg : ∀ i, 0 ≤ e i := fun i => he.2 i (by simp)
      have hdeg : (Finsupp.equivFunOnFinite.symm fun i => (e i).toNat).degree = d := by
        rw [Finsupp.degree_eq_sum]
        show (∑ i, (e i).toNat) = d
        have key : ((∑ i, (e i).toNat : ℕ) : ℤ) = (d : ℤ) := by
          rw [Nat.cast_sum]
          exact Eq.trans
            (Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (hnonneg i)) he.1
        omega
      refine ⟨⟨MvPolynomial.monomial
        (Finsupp.equivFunOnFinite.symm fun i => (e i).toNat) (1 : R),
        (MvPolynomial.mem_homogeneousSubmodule _ _).2
          (MvPolynomial.isHomogeneous_monomial (1 : R) hdeg)⟩, fun s hus => ?_⟩
      have hes : e ∈ laurentMonomials n (d : ℤ) (↑s : Set (Fin (n + 1))) :=
        laurentMonomials_mono (Set.empty_subset _) he
      rw [coe_twistChartEquivTwistSections_single R n (d : ℤ) s hes ⟨_, hus⟩ rfl,
        laurentFrac_eq_mk (R := R) (N := 0) (fun i _ => hnonneg i)
          (fun i _ => by simpa using hnonneg i),
        numExp_zero_toNat]
      exact congrArg (LocalizedModule.mk _) (Subtype.ext (pow_zero _))
  | zero =>
      refine ⟨0, fun s hus => ?_⟩
      have h0 : (⟨(0 : (Fin (n + 1) → ℤ) →₀ R), hus⟩ :
          twistChart R n (d : ℤ) (↑s : Set (Fin (n + 1)))) = 0 := rfl
      rw [h0, map_zero]
      simp
  | add x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      refine ⟨a + b, fun s hus => ?_⟩
      have hsum : (⟨x + y, hus⟩ : twistChart R n (d : ℤ) (↑s : Set (Fin (n + 1))))
          = ⟨x, hconv x hx s⟩ + ⟨y, hconv y hy s⟩ := rfl
      rw [hsum, map_add, AddMemClass.coe_add, ha s (hconv x hx s), hb s (hconv y hy s),
        mk_one_add_mk_one, AddMemClass.coe_add]
  | smul r x hx ih =>
      obtain ⟨a, ha⟩ := ih
      refine ⟨r • a, fun s hus => ?_⟩
      have hsmul : (⟨r • x, hus⟩ : twistChart R n (d : ℤ) (↑s : Set (Fin (n + 1))))
          = r • (⟨x, hconv x hx s⟩ : twistChart R n (d : ℤ) (↑s : Set (Fin (n + 1)))) := rfl
      rw [hsmul, map_smul, SetLike.val_smul, ha s (hconv x hx s), SetLike.val_smul,
        LocalizedModule.smul'_mk]

/-! ### Restricting a global section to a chart -/

/-- A global section of `𝒪(d)` on `ℙⁿ_R`, restricted to the standard open
`D₊(∏_{i ∈ s} Tᵢ)`. -/
def chartRestrict (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (s : Finset (Fin (n + 1)))
    (σ : (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d).val.obj (op ⊤)) :
    chartSheafSections R n d s :=
  (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d).val.map
    (homOfLE (le_top : ProjectiveSpectrum.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (chartDenom R n s) ≤ ⊤)).op σ

/-- Restriction on the twisting sheaf is restriction of functions, so restricting a global
section to the chart `s` and then to a smaller chart `t` restricts it to `t`. -/
theorem chartRestrict_restrict (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s t : Finset (Fin (n + 1))) (hst : s ⊆ t)
    (σ : (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d).val.obj (op ⊤)) :
    ((twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d).val.map
          (homOfLE (basicOpen_chartDenom_le R n s t hst)).op).hom (chartRestrict R n d s σ)
      = chartRestrict R n d t σ := rfl

/-- **The monomial coordinates of a global section are the same in every chart.** The monomial
charts are submodules of one free module on the Laurent exponent vectors, and restriction of
`𝒪(d)` is their inclusion, so passing to a smaller standard open does not move the coordinates
of a section that is defined on all of `ℙⁿ_R`. -/
theorem coe_chartSectionsAddEquivTwistChart_mono (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s t : Finset (Fin (n + 1))) (hs : s.Nonempty) (hst : s ⊆ t)
    (σ : (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d).val.obj (op ⊤)) :
    ((chartSectionsAddEquivTwistChart R n d t (hs.mono hst) (chartRestrict R n d t σ) :
        (Fin (n + 1) → ℤ) →₀ R))
      = ((chartSectionsAddEquivTwistChart R n d s hs (chartRestrict R n d s σ) :
        (Fin (n + 1) → ℤ) →₀ R)) := by
  have h : chartSectionsAddEquivTwistChart R n d t (hs.mono hst) (chartRestrict R n d t σ)
      = Submodule.inclusion (twistChart_mono (R := R) (d := d) (Finset.coe_subset.2 hst))
          (chartSectionsAddEquivTwistChart R n d s hs (chartRestrict R n d s σ)) :=
    chartSectionsAddEquivTwistChart_map_homOfLE R n d s t hs hst (chartRestrict R n d s σ)
  exact congrArg (fun w : twistChart R n d (↑t : Set (Fin (n + 1))) =>
    (w : (Fin (n + 1) → ℤ) →₀ R)) h

/-- The sections of `𝒪(d)` over a chart, read as a graded piece of a localization, are the
monomial coordinates read back through the monomial basis. -/
theorem chartSectionsAddEquiv_eq (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s : Finset (Fin (n + 1))) (hs : s.Nonempty) (x : chartSheafSections R n d s) :
    chartSectionsAddEquiv R n d s hs x
      = twistChartEquivTwistSections R n d s (chartSectionsAddEquivTwistChart R n d s hs x) := by
  show chartSectionsAddEquiv R n d s hs x
      = twistChartEquivTwistSections R n d s
          ((twistChartEquivTwistSections R n d s).symm (chartSectionsAddEquiv R n d s hs x))
  exact ((twistChartEquivTwistSections R n d s).apply_symm_apply _).symm

/-! ### The section attached to a form, read on a chart -/

/-- A form of degree `d` lies in the degree-zero part of the `d`-th shift of the polynomial
ring. -/
theorem coe_mem_twistGrading_zero (R : Type u) [CommRing R] (n d : ℕ)
    (a : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d) :
    (a : MvPolynomial (Fin (n + 1)) R) ∈
      twistGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ) 0 := by
  simp [twistGrading, integerGrading]

/-- **The section attached to a form, read on a chart, is the fraction `a / 1`.** Restricting the
global section of `𝒪(d)` attached to a degree-`d` form `a` to `D₊(∏_{i ∈ s} Tᵢ)` and reading it as
a degree-`d` element of `R[T₀, …, Tₙ][1/∏_{i ∈ s} Tᵢ]` gives `a` over the denominator `1`. -/
theorem coe_chartSectionsAddEquiv_chartRestrict_degreeSection (R : Type u) [CommRing R]
    (n d : ℕ) (s : Finset (Fin (n + 1))) (hs : s.Nonempty)
    (a : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d) :
    ((chartSectionsAddEquiv R n (d : ℤ) s hs
        (chartRestrict R n (d : ℤ) s
          (degreeSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d a)) :
        LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R)))
      = LocalizedModule.mk (a : MvPolynomial (Fin (n + 1)) R) 1 := by
  have hz : (a : MvPolynomial (Fin (n + 1)) R) ∈
      twistGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ)
        (0 • (s.card : ℤ)) := by
    simpa only [zero_smul] using coe_mem_twistGrading_zero R n d a
  have hbase : associatedModuleSheafStandardOpenEquiv
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (twistGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ))
        (chartDenom_mem_homogeneousSubmodule (R := R) n s) (Finset.card_pos.2 hs)
        (chartRestrict R n (d : ℤ) s
          (degreeSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d a))
      = degreeZeroFraction (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          (twistGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ))
          (chartDenom_mem_homogeneousSubmodule (R := R) n s) 0
          (a : MvPolynomial (Fin (n + 1)) R) hz :=
    Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections_basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (twistGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ))
      (chartDenom_mem_homogeneousSubmodule (R := R) n s) (Finset.card_pos.2 hs)
      ⟨(a : MvPolynomial (Fin (n + 1)) R), coe_mem_twistGrading_zero R n d a⟩
  calc ((chartSectionsAddEquiv R n (d : ℤ) s hs
        (chartRestrict R n (d : ℤ) s
          (degreeSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d a)) :
        LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R)))
      = ((associatedModuleSheafStandardOpenEquiv
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          (twistGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ))
          (chartDenom_mem_homogeneousSubmodule (R := R) n s) (Finset.card_pos.2 hs)
          (chartRestrict R n (d : ℤ) s
            (degreeSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d a)) :
          LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R))) := rfl
    _ = ((degreeZeroFraction (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          (twistGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ))
          (chartDenom_mem_homogeneousSubmodule (R := R) n s) 0
          (a : MvPolynomial (Fin (n + 1)) R) hz :
          LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R))) := by
        rw [hbase]
    _ = LocalizedModule.mk (a : MvPolynomial (Fin (n + 1)) R) 1 :=
        congrArg (LocalizedModule.mk _) (Subtype.ext (pow_zero _))

/-! ### Every section of a twist is a form -/

/-- **The standard opens `D₊(Tᵢ)` cover `ℙⁿ_R`.** A relevant homogeneous prime containing every
variable would contain the irrelevant ideal, which is spanned by the variables. -/
theorem exists_mem_basicOpen_X (R : Type u) [CommRing R] (n : ℕ)
    (x : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) :
    ∃ i : Fin (n + 1),
      x ∈ ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i) := by
  by_contra hcon
  have hXi : ∀ i : Fin (n + 1),
      (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ∈ x.asHomogeneousIdeal := fun i =>
    not_not.1 fun h => hcon ⟨i, (ProjectiveSpectrum.mem_basicOpen _ _ x).2 h⟩
  refine x.not_irrelevant_le fun f hf => ?_
  refine HomogeneousIdeal.mem_iff.1 ?_
  refine Ideal.span_le.2 ?_
    (Stacks.AlgebraicGeometry.ProjPolyChart.irrelevant_le_span_X R n
      (HomogeneousIdeal.mem_iff.mpr hf))
  rintro g ⟨i, rfl⟩
  exact HomogeneousIdeal.mem_iff.mpr (hXi i)

/-- **Every global section of `𝒪(d)` on `ℙⁿ_R` is the section of a form of degree `d`**, over an
arbitrary commutative ring. The restrictions of the section to the charts `D₊(Tᵢ)` have one
common monomial expansion, which has no negative exponent and so is a degree-`d` form. -/
theorem exists_degreeSection_eq_of_commRing (R : Type u) [CommRing R] (n d : ℕ)
    (σ : (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ)).val.obj
      (op ⊤)) :
    ∃ a : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d,
      degreeSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d a = σ := by
  classical
  have hs : ∀ i : Fin (n + 1), ({i} : Finset (Fin (n + 1))).Nonempty :=
    fun i => ⟨i, Finset.mem_singleton_self i⟩
  set u : (Fin (n + 1) → ℤ) →₀ R :=
    ((chartSectionsAddEquivTwistChart R n (d : ℤ) {0} (hs 0)
      (chartRestrict R n (d : ℤ) {0} σ) : twistChart R n (d : ℤ)
        (↑({0} : Finset (Fin (n + 1))) : Set (Fin (n + 1)))) : (Fin (n + 1) → ℤ) →₀ R) with hudef
  have hall : ∀ i : Fin (n + 1),
      ((chartSectionsAddEquivTwistChart R n (d : ℤ) {i} (hs i)
        (chartRestrict R n (d : ℤ) {i} σ) : twistChart R n (d : ℤ)
          (↑({i} : Finset (Fin (n + 1))) : Set (Fin (n + 1)))) :
        (Fin (n + 1) → ℤ) →₀ R) = u := by
    intro i
    have h0 : ({0} : Finset (Fin (n + 1))) ⊆ {0, i} := Finset.singleton_subset_iff.2 (by simp)
    have hi : ({i} : Finset (Fin (n + 1))) ⊆ {0, i} := Finset.singleton_subset_iff.2 (by simp)
    rw [hudef]
    exact (coe_chartSectionsAddEquivTwistChart_mono R n (d : ℤ) {i} {0, i} (hs i) hi σ).symm.trans
      (coe_chartSectionsAddEquivTwistChart_mono R n (d : ℤ) {0} {0, i} (hs 0) h0 σ)
  have humem : ∀ i : Fin (n + 1),
      u ∈ twistChart R n (d : ℤ) (↑({i} : Finset (Fin (n + 1))) : Set (Fin (n + 1))) := by
    intro i
    exact hall i ▸ (chartSectionsAddEquivTwistChart R n (d : ℤ) {i} (hs i)
      (chartRestrict R n (d : ℤ) {i} σ)).2
  have hu : u ∈ twistChart R n (d : ℤ) (∅ : Set (Fin (n + 1))) := by
    rw [← twistChart_iInf_singleton_of_nonneg R n (Int.natCast_nonneg d), Submodule.mem_iInf]
    intro i
    simpa using humem i
  obtain ⟨a, ha⟩ := exists_homogeneous_mk_eq R n d hu
  refine ⟨a, ?_⟩
  have hrest : ∀ i : Fin (n + 1),
      chartRestrict R n (d : ℤ) {i}
          (degreeSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d a)
        = chartRestrict R n (d : ℤ) {i} σ := by
    intro i
    have hv : chartSectionsAddEquivTwistChart R n (d : ℤ) {i} (hs i)
        (chartRestrict R n (d : ℤ) {i} σ) = ⟨u, humem i⟩ := Subtype.ext (hall i)
    have hσ : chartSectionsAddEquiv R n (d : ℤ) {i} (hs i) (chartRestrict R n (d : ℤ) {i} σ)
        = twistChartEquivTwistSections R n (d : ℤ) {i} ⟨u, humem i⟩ :=
      (chartSectionsAddEquiv_eq R n (d : ℤ) {i} (hs i) (chartRestrict R n (d : ℤ) {i} σ)).trans
        (congrArg (twistChartEquivTwistSections R n (d : ℤ) {i}) hv)
    have hσ' : ((chartSectionsAddEquiv R n (d : ℤ) {i} (hs i)
          (chartRestrict R n (d : ℤ) {i} σ) : twistSections R n (d : ℤ) {i}) :
          LocalizedModule.Away (chartDenom R n {i}) (MvPolynomial (Fin (n + 1)) R))
        = LocalizedModule.mk (a : MvPolynomial (Fin (n + 1)) R) 1 :=
      (congrArg (fun z : twistSections R n (d : ℤ) {i} =>
        (z : LocalizedModule.Away (chartDenom R n {i})
          (MvPolynomial (Fin (n + 1)) R))) hσ).trans (ha {i} (humem i))
    exact (chartSectionsAddEquiv R n (d : ℤ) {i} (hs i)).injective (Subtype.ext
      ((coe_chartSectionsAddEquiv_chartRestrict_degreeSection R n d {i} (hs i) a).trans
        hσ'.symm))
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨i, hxi⟩ := exists_mem_basicOpen_X R n x.1
  have hxi' : x.1 ∈ ProjectiveSpectrum.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (chartDenom R n {i}) := by
    rwa [chartDenom, Finset.prod_singleton]
  exact congrArg
    (fun y : chartSheafSections R n (d : ℤ) {i} => y.1 ⟨x.1, hxi'⟩) (hrest i)

end Stacks.ProjectiveSpace.Cohomology

end
