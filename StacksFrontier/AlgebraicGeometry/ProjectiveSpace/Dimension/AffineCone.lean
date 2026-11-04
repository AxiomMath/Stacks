module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.Topology.Homeomorph.Lemmas
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.Basic
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal
public import StacksFrontier.RingTheory.GradedAlgebra.Proj.ChartHeight
public import StacksFrontier.RingTheory.MvPolynomial.HypersurfaceDimension
public import StacksFrontier.RingTheory.Spectrum.Prime.LocalDimension
public import StacksFrontier.Topology.Dimension.NowhereDense

/-!
# The affine cone over a projective subscheme is one dimension bigger

Grade `A = k[X₀, …, X_{N-1}]` by total degree and let `p` be a homogeneous prime of `A`. The
closed subset `Z = V₊(p)` of `Proj A` and the closed subset `V(p)` of `Spec A` — the affine cone
over `Z` — are related by `dim Z + 1 = dim V(p)`, and `dim V(p)` is the Krull dimension of
`A ⧸ p`. This is the dimension bridge that the projective-dimension theory needs.

The proof is the standard chart computation. A homogeneous prime that is not the unit ideal is
contained in the irrelevant ideal (`le_irrelevant_of_isHomogeneous_of_ne_top`), so if `Z` has a
point at all then some variable `Xᵢ` is outside `p`. On the standard chart `D₊(Xᵢ)`, which is the
spectrum of the degree-zero chart ring `A₍Xᵢ₎`, the subset `Z` becomes the closed subset cut out
by the degree-zero part `q` of `p · A[1/Xᵢ]`, so

`dim (Z ∩ D₊(Xᵢ)) = dim A₍Xᵢ₎ ⧸ q`.

The dimension formula for a finite type domain over a field,
`Stacks.Spectrum.LocalDimensionFormula.ringKrullDim_eq_height_add_ringKrullDim_quotient`, applied
to `A` at `p` and to `A₍Xᵢ₎` at `q`, gives `N = height p + dim A ⧸ p` and
`N - 1 = height q + dim A₍Xᵢ₎ ⧸ q`; the two heights agree
(`Stacks.GradedLaurent.height_eq_height_under_away_of_isNoetherianRing`) and are finite, so they
cancel and `dim A₍Xᵢ₎ ⧸ q + 1 = dim A ⧸ p`. Finally `dim Z` equals the dimension of any one of
its nonempty charts, because the dimension of a space is the supremum of its local dimensions and
the charts `Z ∩ D₊(Xᵢ)` cover `Z` and all have the same dimension.

## Main results

* `Stacks.ProjectiveSpace.le_irrelevant_of_isHomogeneous_of_ne_top`: a proper homogeneous ideal of
  a polynomial algebra over a field lies in the irrelevant ideal.
* `Stacks.ProjectiveSpace.topologicalKrullDim_projectiveSpectrum_zeroLocus_add_one`:
  `dim V₊(p) + 1 = dim A ⧸ p`.

## References

* [Stacks Project, Tag 0B2R](https://stacks.math.columbia.edu/tag/0B2R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousLocalization MvPolynomial TopologicalSpace

namespace Stacks.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

/-! ### Cancelling a finite summand in `WithBot ℕ∞` -/

/-- A summand coming from `ℕ∞` and different from `⊤` cancels on the right in `WithBot ℕ∞`. The
two exceptional values have to be dealt with by hand: `⊥` absorbs, and `⊤` does not cancel. -/
private lemma withBot_add_right_cancel_coe {c : ℕ∞} (hc : c ≠ ⊤) {a b : WithBot ℕ∞}
    (h : a + (c : WithBot ℕ∞) = b + (c : WithBot ℕ∞)) : a = b := by
  induction a using WithBot.recBotCoe <;> induction b using WithBot.recBotCoe <;>
    simp_all only [WithBot.bot_add, ← WithBot.coe_add, WithBot.coe_ne_bot, WithBot.bot_ne_coe,
      WithBot.coe_eq_coe]
  exact WithTop.add_right_cancel hc h

/-- A summand coming from `ℕ∞` and different from `⊤` cancels on the left in `WithBot ℕ∞`. -/
private lemma withBot_add_left_cancel_coe {c : ℕ∞} (hc : c ≠ ⊤) {a b : WithBot ℕ∞}
    (h : (c : WithBot ℕ∞) + a = (c : WithBot ℕ∞) + b) : a = b :=
  withBot_add_right_cancel_coe hc (by rw [add_comm a, add_comm b]; exact h)

/-! ### A topological preliminary -/

/-- **The dimension of the intersection of two subsets is symmetric in them.** Reading `T` inside
the subspace `S` and reading `S` inside the subspace `T` both compute the dimension of `S ∩ T`. -/
private lemma topologicalKrullDim_preimage_val_comm {X : Type*} [TopologicalSpace X]
    (S T : Set X) :
    topologicalKrullDim ((Subtype.val : ↥S → X) ⁻¹' T)
      = topologicalKrullDim ((Subtype.val : ↥T → X) ⁻¹' S) := by
  have h : ∀ S T : Set X, (Subtype.val : ↥S → X) ⁻¹' T = (Subtype.val : ↥S → X) ⁻¹' (S ∩ T) :=
    fun S T => by ext y; exact ⟨fun hy => ⟨y.2, hy⟩, fun hy => hy.2⟩
  rw [h S T, h T S, Set.inter_comm T S,
    topologicalKrullDim_preimage_val S (S ∩ T) Set.inter_subset_left,
    topologicalKrullDim_preimage_val T (S ∩ T) Set.inter_subset_right]

/-! ### A proper homogeneous ideal is irrelevant -/

/-- **A proper homogeneous ideal of a polynomial algebra over a field is contained in the
irrelevant ideal.** The degree-zero homogeneous component of a member of the ideal is again a
member, and it is a constant; a nonzero constant is a unit, which would make the ideal the unit
ideal. -/
theorem le_irrelevant_of_isHomogeneous_of_ne_top
    {k : Type u} [Field k] {N : ℕ} {p : Ideal (MvPolynomial (Fin N) k)}
    (hp : p.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin N) k)) (hp1 : p ≠ ⊤) :
    p ≤ (HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule (Fin N) k)).toIdeal := by
  intro a ha
  rw [HomogeneousIdeal.toIdeal_irrelevant, RingHom.mem_ker, GradedRing.projZeroRingHom_apply]
  by_contra hne
  refine hp1 (Ideal.eq_top_of_isUnit_mem _ (hp 0 ha) ?_)
  have hmem : GradedRing.proj (homogeneousSubmodule (Fin N) k) 0 a
      ∈ homogeneousSubmodule (Fin N) k 0 := SetLike.coe_mem _
  rw [MvPolynomial.homogeneousSubmodule_zero, Submodule.mem_one] at hmem
  obtain ⟨r, hr⟩ := hmem
  rw [MvPolynomial.algebraMap_eq] at hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hne (by simpa using hr.symm)
  change IsUnit (GradedRing.proj (homogeneousSubmodule (Fin N) k) 0 a)
  rw [← hr]
  exact (isUnit_iff_ne_zero.mpr hr0).map (MvPolynomial.C : k →+* MvPolynomial (Fin N) k)

/-! ### The chart ideal -/

section Chart

variable {k : Type u} [Field k] {N : ℕ} {f : MvPolynomial (Fin N) k}
  {p : Ideal (MvPolynomial (Fin N) k)}

/-- The ideal of the degree-zero chart ring `A₍f₎` cut out by an ideal `J` of `A`: the degree-zero
part of `J · A[1/f]`. This is the prime that the chart `D₊(f) ≅ Spec A₍f₎` assigns to a point of
`Proj A`, spelled out for an arbitrary ideal. -/
private def chartIdeal (f : MvPolynomial (Fin N) k) (J : Ideal (MvPolynomial (Fin N) k)) :
    Ideal (Away (homogeneousSubmodule (Fin N) k) f) :=
  (J.map (algebraMap (MvPolynomial (Fin N) k) (Localization.Away f))).under
    (Away (homogeneousSubmodule (Fin N) k) f)

/-- A homogeneous element of `J` of degree `d` contributes the degree-zero fraction `a / f ^ d` to
the chart ideal, because `f ^ d` is a unit after inverting `f`. -/
private lemma mk_mem_chartIdeal (hf : f ∈ homogeneousSubmodule (Fin N) k 1)
    {J : Ideal (MvPolynomial (Fin N) k)} {d : ℕ} {a : MvPolynomial (Fin N) k}
    (ha : a ∈ homogeneousSubmodule (Fin N) k (d • 1)) (haJ : a ∈ J) :
    Away.mk (homogeneousSubmodule (Fin N) k) hf d a ha ∈ chartIdeal f J := by
  rw [chartIdeal, Ideal.under, Ideal.mem_comap, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk, Stacks.GradedLaurent.mk_eq_algebraMap_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ haJ)

/-- The chart ideal of a homogeneous prime `p` with `f ∉ p` is prime: it is the contraction of the
prime `p · A[1/f]`. -/
private lemma isPrime_chartIdeal [p.IsPrime] (hfp : f ∉ p) : (chartIdeal f p).IsPrime := by
  have hP : (p.map (algebraMap (MvPolynomial (Fin N) k) (Localization.Away f))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) (Localization.Away f) p
      ‹_› ((Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hfp)
  exact Ideal.IsPrime.under _ _

/-- The chart ideal of a homogeneous prime `p` with `f ∉ p` has the same height as `p`. -/
private lemma height_chartIdeal (hf : f ∈ homogeneousSubmodule (Fin N) k 1)
    (hp : p.IsHomogeneous (homogeneousSubmodule (Fin N) k)) [p.IsPrime] (hfp : f ∉ p) :
    (chartIdeal f p).height = p.height :=
  (Stacks.GradedLaurent.height_eq_height_under_away_of_isNoetherianRing
    (homogeneousSubmodule (Fin N) k) hf hp hfp).symm

/-- **A homogeneous ideal is read faithfully on a standard chart.** For a point `x` of `Proj A`
lying in `D₊(f)`, the homogeneous ideal `p` is contained in `x` exactly when the chart ideal of
`p` is contained in the chart ideal of `x`. Monotonicity gives one direction; the other uses that
`p` is generated by its homogeneous elements, each of which is visible in the chart ideal as a
degree-zero fraction. -/
private lemma le_iff_chartIdeal_le (hf : f ∈ homogeneousSubmodule (Fin N) k 1)
    (hp : p.IsHomogeneous (homogeneousSubmodule (Fin N) k))
    (x : ↥(ProjectiveSpectrum.basicOpen (homogeneousSubmodule (Fin N) k) f :
      Set (ProjectiveSpectrum (homogeneousSubmodule (Fin N) k)))) :
    p ≤ x.1.asHomogeneousIdeal.toIdeal
      ↔ chartIdeal f p ≤ chartIdeal f x.1.asHomogeneousIdeal.toIdeal := by
  classical
  refine ⟨fun h => Ideal.comap_mono (Ideal.map_mono h), fun h a ha => ?_⟩
  rw [← DirectSum.sum_support_decompose (homogeneousSubmodule (Fin N) k) a]
  refine Ideal.sum_mem _ fun d _ => ?_
  have hd : ((DirectSum.decompose (homogeneousSubmodule (Fin N) k) a d :
      MvPolynomial (Fin N) k)) ∈ homogeneousSubmodule (Fin N) k (d • 1) := by
    simpa only [smul_eq_mul, mul_one] using
      (DirectSum.decompose (homogeneousSubmodule (Fin N) k) a d).2
  exact (ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier x _).mp (h (mk_mem_chartIdeal hf hd
    (hp d ha)))

/-- Membership in a projective zero locus is containment of ideals. -/
private lemma mem_projectiveSpectrum_zeroLocus_iff
    (p : Ideal (MvPolynomial (Fin N) k))
    (x : ProjectiveSpectrum (homogeneousSubmodule (Fin N) k)) :
    x ∈ ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin N) k)
        (p : Set (MvPolynomial (Fin N) k))
      ↔ p ≤ x.asHomogeneousIdeal.toIdeal := Iff.rfl

/-- **The standard chart `D₊(f)` of `Proj A` is the spectrum of the degree-zero chart ring.** This
is `AlgebraicGeometry.projIsoSpecTopComponent`, whose underlying function is exactly the
assignment `x ↦ chartIdeal f x`. -/
private def chartEquiv (hf : f ∈ homogeneousSubmodule (Fin N) k 1) :
    ↥(ProjectiveSpectrum.basicOpen (homogeneousSubmodule (Fin N) k) f :
        Set (ProjectiveSpectrum (homogeneousSubmodule (Fin N) k)))
      ≃ₜ PrimeSpectrum (Away (homogeneousSubmodule (Fin N) k) f) :=
  TopCat.homeoOfIso (projIsoSpecTopComponent hf Nat.one_pos)

/-- The chart homeomorphism sends a point of `D₊(f)` to its chart ideal. -/
private lemma chartEquiv_asIdeal (hf : f ∈ homogeneousSubmodule (Fin N) k 1)
    (x : ↥(ProjectiveSpectrum.basicOpen (homogeneousSubmodule (Fin N) k) f :
      Set (ProjectiveSpectrum (homogeneousSubmodule (Fin N) k)))) :
    (chartEquiv hf x).asIdeal = chartIdeal f x.1.asHomogeneousIdeal.toIdeal := rfl

/-- **The chart homeomorphism carries `V₊(p) ∩ D₊(f)` onto `V(chartIdeal f p)`.** -/
private lemma mem_preimage_zeroLocus_iff (hf : f ∈ homogeneousSubmodule (Fin N) k 1)
    (hp : p.IsHomogeneous (homogeneousSubmodule (Fin N) k))
    (x : ↥(ProjectiveSpectrum.basicOpen (homogeneousSubmodule (Fin N) k) f :
      Set (ProjectiveSpectrum (homogeneousSubmodule (Fin N) k)))) :
    x ∈ (Subtype.val : _ → ProjectiveSpectrum (homogeneousSubmodule (Fin N) k)) ⁻¹'
        ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin N) k)
          (p : Set (MvPolynomial (Fin N) k))
      ↔ chartEquiv hf x ∈ PrimeSpectrum.zeroLocus
          (chartIdeal f p : Set (Away (homogeneousSubmodule (Fin N) k) f)) := by
  rw [Set.mem_preimage, mem_projectiveSpectrum_zeroLocus_iff, PrimeSpectrum.mem_zeroLocus,
    chartEquiv_asIdeal, SetLike.coe_subset_coe]
  exact le_iff_chartIdeal_le hf hp x

/-- **The dimension of `V₊(p)` read on the standard chart `D₊(f)`.** The chart identifies
`V₊(p) ∩ D₊(f)` with the closed subset of `Spec A₍f₎` cut out by the chart ideal, whose dimension
is the Krull dimension of the quotient. -/
private lemma topologicalKrullDim_preimage_basicOpen
    (hf : f ∈ homogeneousSubmodule (Fin N) k 1)
    (hp : p.IsHomogeneous (homogeneousSubmodule (Fin N) k)) :
    topologicalKrullDim ((Subtype.val : ↥(ProjectiveSpectrum.zeroLocus
          (homogeneousSubmodule (Fin N) k) (p : Set (MvPolynomial (Fin N) k)))
        → ProjectiveSpectrum (homogeneousSubmodule (Fin N) k)) ⁻¹'
        (ProjectiveSpectrum.basicOpen (homogeneousSubmodule (Fin N) k) f :
          Set (ProjectiveSpectrum (homogeneousSubmodule (Fin N) k))))
      = ringKrullDim (Away (homogeneousSubmodule (Fin N) k) f ⧸ chartIdeal f p) := by
  rw [topologicalKrullDim_preimage_val_comm,
    IsHomeomorph.topologicalKrullDim_eq _
      ((chartEquiv hf).subtype (mem_preimage_zeroLocus_iff hf hp)).isHomeomorph,
    topologicalKrullDim_zeroLocus]

end Chart

/-! ### The dimension of a projective zero locus -/

section Dimension

variable {k : Type u} [Field k] {N : ℕ} {p : Ideal (MvPolynomial (Fin N) k)}

/-- The dimension formula on the standard chart `D₊(Xᵢ)`: `#σ - 1 = height p + dim A₍Xᵢ₎ ⧸ q`,
where `q` is the chart ideal of `p`. The chart ring is a polynomial algebra on one fewer
variable, hence a finite type domain over `k` of dimension `#σ - 1`, and the chart ideal has the
same height as `p`. -/
private lemma natCard_sub_one_eq_height_add_ringKrullDim_quotient_chart
    (hp : p.IsHomogeneous (homogeneousSubmodule (Fin N) k)) [p.IsPrime] (i : Fin N)
    (hi : (X i : MvPolynomial (Fin N) k) ∉ p) :
    ((Nat.card (Fin N) - 1 : ℕ) : WithBot ℕ∞)
      = (p.height : WithBot ℕ∞)
        + ringKrullDim (Away (homogeneousSubmodule (Fin N) k) (X i) ⧸ chartIdeal (X i) p) := by
  have hX : (X i : MvPolynomial (Fin N) k) ∈ homogeneousSubmodule (Fin N) k 1 :=
    Stacks.SymmetricAway.X_mem_homogeneousSubmodule_one i
  have : Algebra.FiniteType k (Away (homogeneousSubmodule (Fin N) k) (X i)) :=
    Algebra.FiniteType.equiv inferInstance (Stacks.SymmetricAway.chartAlgEquiv (R := k) i)
  have : (chartIdeal (X i) p).IsPrime := isPrime_chartIdeal hi
  rw [← height_chartIdeal hX hp hi, ← Stacks.ProjectiveSpace.ringKrullDim_chartRing (K := k) i]
  exact Stacks.Spectrum.LocalDimensionFormula.ringKrullDim_eq_height_add_ringKrullDim_quotient
    k (Away (homogeneousSubmodule (Fin N) k) (X i)) (chartIdeal (X i) p)

/-- The height of a prime of a polynomial algebra over a field in finitely many variables is
finite: it is bounded by the Krull dimension, which is the number of variables. -/
private lemma height_ne_top_of_isPrime (p : Ideal (MvPolynomial (Fin N) k)) [p.IsPrime] :
    p.height ≠ ⊤ := by
  intro htop
  have hle : (p.height : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin N) k) :=
    Ideal.height_le_ringKrullDim_of_isPrime
  rw [htop, Stacks.MvPolynomial.ringKrullDim_mvPolynomial k (Fin N), ← WithBot.coe_natCast,
    WithBot.coe_le_coe, top_le_iff] at hle
  exact ENat.natCast_ne_top _ hle

/-- A standard chart on which `p` does not vanish does not meet `V₊(p)`: a point of the
intersection would have `Xᵢ` both inside and outside its homogeneous ideal. -/
private lemma isEmpty_preimage_basicOpen_of_mem (i : Fin N)
    (hip : (X i : MvPolynomial (Fin N) k) ∈ p) :
    IsEmpty ↥((Subtype.val : ↥(ProjectiveSpectrum.zeroLocus
          (homogeneousSubmodule (Fin N) k) (p : Set (MvPolynomial (Fin N) k)))
        → ProjectiveSpectrum (homogeneousSubmodule (Fin N) k)) ⁻¹'
        (ProjectiveSpectrum.basicOpen (homogeneousSubmodule (Fin N) k) (X i) :
          Set (ProjectiveSpectrum (homogeneousSubmodule (Fin N) k)))) := by
  refine ⟨fun y => ?_⟩
  have h1 : p ≤ y.1.1.asHomogeneousIdeal.toIdeal := y.1.2
  have h2 : (X i : MvPolynomial (Fin N) k) ∉ y.1.1.asHomogeneousIdeal := y.2
  exact h2 (h1 hip)

/-- **The dimension of `V₊(p)` is bounded by the dimensions of the standard charts.** The
dimension of a space is the supremum of its local dimensions, and every point of `Proj` lies in
some standard chart, which is an open neighbourhood of it inside `V₊(p)`. -/
private lemma topologicalKrullDim_zeroLocus_le {c : WithBot ℕ∞}
    (hc : ∀ i : Fin N, topologicalKrullDim ((Subtype.val : ↥(ProjectiveSpectrum.zeroLocus
          (homogeneousSubmodule (Fin N) k) (p : Set (MvPolynomial (Fin N) k)))
        → ProjectiveSpectrum (homogeneousSubmodule (Fin N) k)) ⁻¹'
        (ProjectiveSpectrum.basicOpen (homogeneousSubmodule (Fin N) k) (X i) :
          Set (ProjectiveSpectrum (homogeneousSubmodule (Fin N) k)))) ≤ c) :
    topologicalKrullDim ↥(ProjectiveSpectrum.zeroLocus
      (homogeneousSubmodule (Fin N) k) (p : Set (MvPolynomial (Fin N) k))) ≤ c := by
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun x => ?_
  obtain ⟨i, hi⟩ := Stacks.ProjectiveSpace.exists_mem_basicOpen_X (R := k) (σ := Fin N) x.1
  refine le_trans ?_ (hc i)
  exact iInf_le_of_le ((Subtype.val : ↥(ProjectiveSpectrum.zeroLocus
      (homogeneousSubmodule (Fin N) k) (p : Set (MvPolynomial (Fin N) k)))
      → ProjectiveSpectrum (homogeneousSubmodule (Fin N) k)) ⁻¹'
      (ProjectiveSpectrum.basicOpen (homogeneousSubmodule (Fin N) k) (X i) :
        Set (ProjectiveSpectrum (homogeneousSubmodule (Fin N) k))))
    (iInf_le_of_le ((ProjectiveSpectrum.basicOpen (homogeneousSubmodule (Fin N) k)
      (X i)).2.preimage continuous_subtype_val) (iInf_le _ hi))

/-- **The dimension of a projective zero locus, plus one, is the dimension of its affine cone.**
For a homogeneous prime `p` of `k[X₀, …, X_{N-1}]` whose projective zero locus `Z = V₊(p)` is
nonempty, `dim Z + 1 = dim k[X₀, …, X_{N-1}] ⧸ p`.

Each standard chart `Z ∩ D₊(Xᵢ)` on which `Z` is nonempty has dimension `dim A ⧸ p - 1`, by the
chart identification and the dimension formula for a finite type domain over a field; the charts
cover `Z`, and the dimension of a space is the supremum of its local dimensions, so `Z` itself has
that dimension. -/
theorem topologicalKrullDim_projectiveSpectrum_zeroLocus_add_one
    {k : Type u} [Field k] {N : ℕ} (p : Ideal (MvPolynomial (Fin N) k)) [p.IsPrime]
    (hp : p.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin N) k))
    (hne : (ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin N) k)
            (p : Set (MvPolynomial (Fin N) k))).Nonempty) :
    topologicalKrullDim ↥(ProjectiveSpectrum.zeroLocus
        (MvPolynomial.homogeneousSubmodule (Fin N) k) (p : Set (MvPolynomial (Fin N) k))) + 1
      = ringKrullDim (MvPolynomial (Fin N) k ⧸ p) := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨i₀, hi₀⟩ := Stacks.ProjectiveSpace.exists_mem_basicOpen_X (R := k) (σ := Fin N) x₀
  have hi₀p : (X i₀ : MvPolynomial (Fin N) k) ∉ p := fun h => hi₀ (hx₀ h)
  have : Nonempty (Fin N) := ⟨i₀⟩
  have hNe : Nat.card (Fin N) ≠ 0 := Nat.card_pos.ne'
  -- the two instances of the dimension formula
  have eqA := Stacks.Spectrum.LocalDimensionFormula.ringKrullDim_eq_height_add_ringKrullDim_quotient
    k (MvPolynomial (Fin N) k) p
  rw [Stacks.MvPolynomial.ringKrullDim_mvPolynomial k (Fin N)] at eqA
  have hsplit : ((Nat.card (Fin N) : ℕ) : WithBot ℕ∞)
      = ((Nat.card (Fin N) - 1 : ℕ) : WithBot ℕ∞) + 1 := by
    rw [← Nat.cast_one (R := WithBot ℕ∞), ← Nat.cast_add,
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hNe)]
  -- every nonempty chart has the same dimension
  have hchart : ∀ i : Fin N, (X i : MvPolynomial (Fin N) k) ∉ p →
      ringKrullDim (Away (homogeneousSubmodule (Fin N) k) (X i) ⧸ chartIdeal (X i) p)
        = ringKrullDim (Away (homogeneousSubmodule (Fin N) k) (X i₀) ⧸ chartIdeal (X i₀) p) :=
    fun i hi => withBot_add_left_cancel_coe (height_ne_top_of_isPrime p)
      ((natCard_sub_one_eq_height_add_ringKrullDim_quotient_chart hp i hi).symm.trans
        (natCard_sub_one_eq_height_add_ringKrullDim_quotient_chart hp i₀ hi₀p))
  have hdim := fun i : Fin N => topologicalKrullDim_preimage_basicOpen (p := p)
    (Stacks.SymmetricAway.X_mem_homogeneousSubmodule_one i) hp
  -- the dimension of `Z` is the dimension of the chart at `i₀`
  have hZ : topologicalKrullDim ↥(ProjectiveSpectrum.zeroLocus
        (homogeneousSubmodule (Fin N) k) (p : Set (MvPolynomial (Fin N) k)))
      = ringKrullDim (Away (homogeneousSubmodule (Fin N) k) (X i₀) ⧸ chartIdeal (X i₀) p) := by
    refine le_antisymm (topologicalKrullDim_zeroLocus_le fun i => ?_) ?_
    · by_cases hip : (X i : MvPolynomial (Fin N) k) ∈ p
      · exact ((topologicalKrullDim_eq_bot_iff_isEmpty _).mpr
          (isEmpty_preimage_basicOpen_of_mem i hip)).trans_le bot_le
      · exact (hdim i).trans_le (hchart i hip).le
    · rw [← hdim i₀]
      exact topologicalKrullDim_subspace_le _ _
  rw [hZ]
  refine (withBot_add_left_cancel_coe (height_ne_top_of_isPrime p) ?_).symm
  rw [← eqA, hsplit, natCard_sub_one_eq_height_add_ringKrullDim_quotient_chart hp i₀ hi₀p,
    add_assoc]

end Dimension

end Stacks.ProjectiveSpace

end
