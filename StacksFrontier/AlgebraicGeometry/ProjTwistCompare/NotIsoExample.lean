module

public import StacksFrontier.AlgebraicGeometry.ProjTwistCompare.RestrictIso
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.DegreeSection
public import StacksFrontier.RingTheory.GradedAlgebra.WeightedQuotient

/-!
# The comparison maps on twists need not be isomorphisms

Let `R` be a nonzero commutative ring, `A = R[x, y]/(x²)` with `x` of degree `1` and `y` of
degree `2`, and `B = A/(x) = R[x, y]/(x)`. The quotient map `ψ : A ⟶ B` is a surjective
homomorphism of graded rings, so by Stacks 07ZI it is defined on all of `Proj B` and induces a
closed immersion `Proj B ⟶ Proj A`; here that morphism is even an isomorphism. Nevertheless the
comparison map `θ₁ : r_ψ^*𝒪_{Proj A}(1) ⟶ 𝒪_{Proj B}(1)` of Tag 01MY is not an isomorphism: the
global section `x` of `𝒪_{Proj A}(1)` is nonzero at every point, because the annihilator of `x`
is `(x)`, while `θ₁` sends it to the section `ψ x = 0`. So the comparison maps of Stacks 07ZI (3)
and Stacks 085H (3) are not isomorphisms in general, even when `𝒜 ⟶ ℬ` is surjective.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistCompare.NotIsoExample.surjective_psi` and
  `Stacks.AlgebraicGeometry.ProjTwistCompare.NotIsoExample.surjOn_psi`: `ψ` is surjective, in
  every degree.
* `Stacks.AlgebraicGeometry.ProjTwistCompare.NotIsoExample.isIso_projMap`: `Proj B ⟶ Proj A` is
  an isomorphism.
* `Stacks.AlgebraicGeometry.ProjTwistCompare.NotIsoExample.not_isIso_twistMap_of_map_eq_zero`:
  when `Proj ℬ ⟶ Proj 𝒜` is an isomorphism, `θ_k` is not an isomorphism as soon as `ψ` kills a
  homogeneous element of degree `k` that is nonzero at some point of `Proj 𝒜`.
* `Stacks.AlgebraicGeometry.ProjTwistCompare.NotIsoExample.not_isIso_twistMap`: `θ₁` is not an
  isomorphism.

## References

* [Stacks Project, Tag 07ZI](https://stacks.math.columbia.edu/tag/07ZI)
* [Stacks Project, Tag 085H](https://stacks.math.columbia.edu/tag/085H)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial

namespace Stacks.AlgebraicGeometry.ProjTwistCompare.NotIsoExample

universe u

variable (R : Type u) [CommRing R]

/-! ### The two graded rings -/

/-- The weights `(1, 2)` of the variables `x = X 0` and `y = X 1`. -/
def weights : Fin 2 → ℕ := ![1, 2]

/-- The weight of an exponent vector `m` for the weights `(1, 2)` is `m 0 + 2 * m 1`. -/
theorem weight_eq (m : Fin 2 →₀ ℕ) : Finsupp.weight weights m = m 0 + 2 * m 1 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fin.sum_univ_two, weights, mul_comm]

/-- The relation `x²` presenting `A`. -/
def relA : Unit → MvPolynomial (Fin 2) R := fun _ => X 0 ^ 2

/-- The relation `x` presenting `B`. -/
def relB : Unit → MvPolynomial (Fin 2) R := fun _ => X 0

/-- The relation `x²` is weighted homogeneous of degree `2`. -/
theorem relA_isWeightedHomogeneous (j : Unit) :
    (relA R j).IsWeightedHomogeneous weights 2 := by
  simpa [relA, weights] using (isWeightedHomogeneous_X R weights 0).pow 2

/-- The relation `x` is weighted homogeneous of degree `1`. -/
theorem relB_isWeightedHomogeneous (j : Unit) :
    (relB R j).IsWeightedHomogeneous weights 1 := by
  simpa [relB, weights] using isWeightedHomogeneous_X R weights 0

/-- The ring `A = R[x, y]/(x²)`. -/
abbrev RingA : Type u := WeightedQuotient.ring (relA R)

/-- The ring `B = R[x, y]/(x)`. -/
abbrev RingB : Type u := WeightedQuotient.ring (relB R)

/-- The grading of `A`. -/
abbrev gradA : ℕ → Submodule R (RingA R) := WeightedQuotient.grading weights (relA R)

/-- The grading of `B`. -/
abbrev gradB : ℕ → Submodule R (RingB R) := WeightedQuotient.grading weights (relB R)

/-- The grading of `A` makes it a graded algebra. -/
instance gradedAlgebraA : _root_.GradedAlgebra (gradA R) :=
  WeightedQuotient.gradedAlgebra weights (fun _ => 2) (relA R) (relA_isWeightedHomogeneous R)

/-- The grading of `B` makes it a graded algebra. -/
instance gradedAlgebraB : _root_.GradedAlgebra (gradB R) :=
  WeightedQuotient.gradedAlgebra weights (fun _ => 1) (relB R) (relB_isWeightedHomogeneous R)

/-- A polynomial lies in the ideal `(x²)` if and only if every monomial in its support has
`x`-exponent at least `2`. -/
theorem mem_relA_iff (p : MvPolynomial (Fin 2) R) :
    p ∈ WeightedQuotient.relationIdeal (relA R) ↔ ∀ m ∈ p.support, 2 ≤ m 0 := by
  have h : WeightedQuotient.relationIdeal (relA R) =
      Ideal.span ((fun s => monomial s (1 : R)) '' {Finsupp.single 0 2}) := by
    change Ideal.span (Set.range fun _ : Unit => (X 0 ^ 2 : MvPolynomial (Fin 2) R)) = _
    rw [Set.range_const, Set.image_singleton, X_pow_eq_monomial]
  rw [h, mem_ideal_span_monomial_image]
  simp [Finsupp.single_le_iff]

/-- A polynomial lies in the ideal `(x)` if and only if every monomial in its support has nonzero
`x`-exponent. -/
theorem mem_relB_iff (p : MvPolynomial (Fin 2) R) :
    p ∈ WeightedQuotient.relationIdeal (relB R) ↔ ∀ m ∈ p.support, m 0 ≠ 0 := by
  have h : WeightedQuotient.relationIdeal (relB R) = Ideal.span (X '' {0}) := by
    change Ideal.span (Set.range fun _ : Unit => (X 0 : MvPolynomial (Fin 2) R)) = _
    rw [Set.range_const, Set.image_singleton]
  rw [h, mem_ideal_span_X_image]
  simp

/-- An element of a weighted quotient of `R[x, y]` has degree `d` if and only if it is the class of
a weighted homogeneous polynomial of degree `d`. -/
theorem mem_grading_iff {κ : Type} (rel : κ → MvPolynomial (Fin 2) R) (d : ℕ)
    (a : WeightedQuotient.ring rel) :
    a ∈ WeightedQuotient.grading weights rel d ↔
      ∃ p : MvPolynomial (Fin 2) R, p.IsWeightedHomogeneous weights d ∧
        Ideal.Quotient.mk _ p = a := by
  change a ∈ Submodule.map _ _ ↔ _
  rw [Submodule.mem_map]
  simp only [mem_weightedHomogeneousSubmodule]
  rfl

/-! ### The quotient map -/

/-- The ideal `(x²)` is contained in the ideal `(x)`. -/
theorem relA_le_relB :
    WeightedQuotient.relationIdeal (relA R) ≤ WeightedQuotient.relationIdeal (relB R) := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨_, rfl⟩
  change X 0 ^ 2 ∈ _
  rw [pow_two]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨(), rfl⟩)

/-- **The quotient map `ψ : A ⟶ B`**, a homomorphism of graded rings. -/
def psi : gradA R →+*ᵍ gradB R where
  toRingHom := Ideal.Quotient.factor (relA_le_relB R)
  map_mem {d a} ha := by
    obtain ⟨p, hp, rfl⟩ := (mem_grading_iff R (relA R) d a).1 ha
    exact (mem_grading_iff R (relB R) d _).2 ⟨p, hp, by simp⟩

/-- `ψ` sends the class of a polynomial in `A` to its class in `B`. -/
theorem psi_mk (p : MvPolynomial (Fin 2) R) :
    psi R (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ p :=
  Ideal.Quotient.factor_mk (relA_le_relB R) p

/-- `ψ` is surjective in every degree. -/
theorem surjOn_psi (d : ℕ) {b : RingB R} (hb : b ∈ gradB R d) :
    ∃ a ∈ gradA R d, psi R a = b := by
  obtain ⟨p, hp, rfl⟩ := (mem_grading_iff R (relB R) d b).1 hb
  exact ⟨Ideal.Quotient.mk _ p, (mem_grading_iff R (relA R) d _).2 ⟨p, hp, rfl⟩, psi_mk R p⟩

/-- **`ψ` is surjective.** -/
theorem surjective_psi : Function.Surjective (psi R) := by
  intro b
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨_, psi_mk R p⟩

/-- `ψ` is injective in even degrees: the kernel `(x)/(x²)` lives in odd degrees. -/
theorem eq_zero_of_psi_eq_zero {n : ℕ} {a : RingA R} (ha : a ∈ gradA R (2 * n))
    (h : psi R a = 0) : a = 0 := by
  obtain ⟨p, hp, rfl⟩ := (mem_grading_iff R (relA R) _ a).1 ha
  rw [psi_mk, Ideal.Quotient.eq_zero_iff_mem, mem_relB_iff] at h
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_relA_iff]
  intro m hm
  have hw := hp (mem_support_iff.1 hm)
  rw [weight_eq] at hw
  have := h m hm
  lia

/-- The class `x` of the first variable in `A`. -/
def xA : RingA R := Ideal.Quotient.mk _ (X 0)

/-- The class `y` of the second variable in `A`. -/
def yA : RingA R := Ideal.Quotient.mk _ (X 1)

/-- The variable `x` is weighted homogeneous of degree `1`. -/
theorem isWeightedHomogeneous_X0 : (X 0 : MvPolynomial (Fin 2) R).IsWeightedHomogeneous weights 1 :=
  by simpa [weights] using isWeightedHomogeneous_X R weights 0

/-- The variable `y` is weighted homogeneous of degree `2`. -/
theorem isWeightedHomogeneous_X1 : (X 1 : MvPolynomial (Fin 2) R).IsWeightedHomogeneous weights 2 :=
  by simpa [weights] using isWeightedHomogeneous_X R weights 1

/-- The class `x` has degree `1` in `A`. -/
theorem xA_mem : xA R ∈ gradA R 1 :=
  (mem_grading_iff R (relA R) 1 _).2 ⟨X 0, isWeightedHomogeneous_X0 R, rfl⟩

/-- The class `y` has degree `2` in `A`. -/
theorem yA_mem : yA R ∈ gradA R 2 :=
  (mem_grading_iff R (relA R) 2 _).2 ⟨X 1, isWeightedHomogeneous_X1 R, rfl⟩

/-- `ψ` sends `x` to `0`. -/
theorem psi_xA : psi R (xA R) = 0 := by
  rw [xA, psi_mk, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨(), rfl⟩

/-- `x² = 0` in `A`. -/
theorem xA_sq : xA R * xA R = 0 := by
  rw [xA, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← pow_two]
  exact Ideal.subset_span ⟨(), rfl⟩

/-- The annihilator of `x` in `A` is `(x)`. -/
theorem mem_span_xA_of_mul_eq_zero {s : RingA R} (h : s * xA R = 0) :
    s ∈ Ideal.span {xA R} := by
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [xA, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, mem_relA_iff, support_mul_X] at h
  have hq : q ∈ Ideal.span (X '' {0} : Set (MvPolynomial (Fin 2) R)) := by
    rw [mem_ideal_span_X_image]
    intro m hm
    have := h (m + Finsupp.single 0 1) (Finset.mem_map_of_mem _ hm)
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
    exact ⟨0, rfl, by lia⟩
  rw [Set.image_singleton] at hq
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hq
  rw [map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

/-! ### The two homogeneous spectra -/

/-- A homogeneous ideal containing the classes of both variables contains the irrelevant ideal. -/
theorem irrelevant_le_of_mem {κ : Type} (rel : κ → MvPolynomial (Fin 2) R)
    [_root_.GradedAlgebra (WeightedQuotient.grading weights rel)]
    (I : Ideal (WeightedQuotient.ring rel)) (h0 : Ideal.Quotient.mk _ (X 0) ∈ I)
    (h1 : Ideal.Quotient.mk _ (X 1) ∈ I) :
    (HomogeneousIdeal.irrelevant (WeightedQuotient.grading weights rel)).toIdeal ≤ I := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi a ha
  obtain ⟨p, hp, rfl⟩ := (mem_grading_iff R rel i a).1 ha
  have hX : p ∈ Ideal.span (X '' Set.univ : Set (MvPolynomial (Fin 2) R)) := by
    rw [mem_ideal_span_X_image]
    intro m hm
    have hw := hp (mem_support_iff.1 hm)
    rw [weight_eq] at hw
    by_cases h : m 0 = 0
    · exact ⟨1, trivial, by lia⟩
    · exact ⟨0, trivial, h⟩
  have hle : Ideal.map (Ideal.Quotient.mk _) (Ideal.span (X '' Set.univ :
      Set (MvPolynomial (Fin 2) R))) ≤ I := by
    rw [Ideal.map_span]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨_, ⟨j, -, rfl⟩, rfl⟩
    fin_cases j
    exacts [h0, h1]
  exact hle (Ideal.mem_map_of_mem _ hX)

/-- If all of `Proj` lies in `D₊(f)`, the chart `Spec 𝒜_(f) ⟶ Proj 𝒜` is an isomorphism. -/
private theorem isIso_awayι_of_basicOpen_eq_top {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A} {m : ℕ} (hf : f ∈ 𝒜 m)
    (hm : 0 < m) (h : AlgebraicGeometry.Proj.basicOpen 𝒜 f = ⊤) :
    IsIso (AlgebraicGeometry.Proj.awayι 𝒜 f hf hm) := by
  have : IsIso (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι := by
    rw [h]
    exact (AlgebraicGeometry.Scheme.topIso _).isIso_hom
  rw [← AlgebraicGeometry.Proj.basicOpenIsoSpec_inv_ι]
  infer_instance

/-- If the class of `x` lies in every point of `Proj`, then every point lies in `D₊(y)`. -/
private theorem basicOpen_eq_top_of_X0_mem {κ : Type} (rel : κ → MvPolynomial (Fin 2) R)
    [_root_.GradedAlgebra (WeightedQuotient.grading weights rel)] (y : WeightedQuotient.ring rel)
    (hy : y = Ideal.Quotient.mk _ (X 1))
    (h0 : ∀ p : ProjectiveSpectrum (WeightedQuotient.grading weights rel),
      Ideal.Quotient.mk _ (X 0) ∈ p.asHomogeneousIdeal.toIdeal) :
    AlgebraicGeometry.Proj.basicOpen (WeightedQuotient.grading weights rel) y = ⊤ := by
  refine top_unique fun p _ => ?_
  change y ∉ p.asHomogeneousIdeal
  intro hy'
  exact p.not_irrelevant_le (toIdeal_le_toIdeal_iff.1
    (irrelevant_le_of_mem R rel _ (h0 p) (hy ▸ hy')))

/-- Every point of `Proj A` lies in `D₊(y)`. -/
theorem basicOpen_yA : AlgebraicGeometry.Proj.basicOpen (gradA R) (yA R) = ⊤ :=
  basicOpen_eq_top_of_X0_mem R (relA R) _ rfl fun p =>
    p.isPrime.mem_of_pow_mem 2 <| by
      rw [pow_two]; change xA R * xA R ∈ _; rw [xA_sq]; exact zero_mem _

/-- Every point of `Proj B` lies in `D₊(ψ y)`. -/
theorem basicOpen_psi_yA :
    AlgebraicGeometry.Proj.basicOpen (gradB R) (psi R (yA R)) = ⊤ :=
  basicOpen_eq_top_of_X0_mem R (relB R) _ (psi_mk R _) fun p => by
    have h : (Ideal.Quotient.mk _ (X 0) : RingB R) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨(), rfl⟩)
    rw [h]
    exact zero_mem _

/-- The chart `Spec A_(y) ⟶ Proj A` is an isomorphism. -/
theorem isIso_awayι_A :
    IsIso (AlgebraicGeometry.Proj.awayι (gradA R) (yA R) (yA_mem R) two_pos) :=
  isIso_awayι_of_basicOpen_eq_top _ _ _ (basicOpen_yA R)

/-- The chart `Spec B_(ψ y) ⟶ Proj B` is an isomorphism. -/
theorem isIso_awayι_B :
    IsIso (AlgebraicGeometry.Proj.awayι (gradB R) (psi R (yA R)) ((psi R).map_mem (yA_mem R))
      two_pos) :=
  isIso_awayι_of_basicOpen_eq_top _ _ _ (basicOpen_psi_yA R)

/-- The induced map `A_(y) ⟶ B_(ψ y)` of degree-zero localizations is bijective. -/
theorem bijective_awayMap :
    Function.Bijective (HomogeneousLocalization.Away.map (psi R) (yA R)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (gradA R) (yA_mem R) z
    rw [HomogeneousLocalization.Away.map_mk] at hz
    have hv := congrArg HomogeneousLocalization.val hz
    rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
      Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at hv
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := hv
    have hmem : yA R ^ k * a ∈ gradA R (2 * (k + n)) := by
      have := SetLike.mul_mem_graded (SetLike.pow_mem_graded k (yA_mem R)) ha
      convert this using 2
      simp only [smul_eq_mul]
      ring
    have h0 : yA R ^ k * a = 0 :=
      eq_zero_of_psi_eq_zero R hmem (by rw [map_mul, map_pow]; exact hk)
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
      Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
    exact ⟨⟨_, k, rfl⟩, h0⟩
  · intro z
    obtain ⟨n, b, hb, rfl⟩ :=
      HomogeneousLocalization.Away.mk_surjective (gradB R) ((psi R).map_mem (yA_mem R)) z
    obtain ⟨a, ha, rfl⟩ := surjOn_psi R _ hb
    exact ⟨HomogeneousLocalization.Away.mk (gradA R) (yA_mem R) n a ha,
      HomogeneousLocalization.Away.map_mk _ _ _ _ _ _⟩

/-- The irrelevant ideal of `B` is contained in the image under `ψ` of the irrelevant ideal of
`A`. -/
theorem irrelevant_le_map :
    HomogeneousIdeal.irrelevant (gradB R) ≤
      (HomogeneousIdeal.irrelevant (gradA R)).map (psi R) := by
  rw [← toIdeal_le_toIdeal_iff, HomogeneousIdeal.toIdeal_map,
    HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi b hb
  obtain ⟨a, ha, rfl⟩ := surjOn_psi R i hb
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ hi ha)

/-- **`Proj B ⟶ Proj A` is an isomorphism.** -/
instance isIso_projMap : IsIso (AlgebraicGeometry.Proj.map (psi R) (irrelevant_le_map R)) := by
  have := isIso_awayι_A R
  have := isIso_awayι_B R
  have : IsIso (CommRingCat.ofHom (HomogeneousLocalization.Away.map (psi R) (yA R))) :=
    (RingEquiv.ofBijective _ (bijective_awayMap R)).toCommRingCatIso.isIso_hom
  have e := AlgebraicGeometry.Proj.awayι_comp_map (psi R) (irrelevant_le_map R) two_pos
    (yA R) (yA_mem R)
  rw [← IsIso.eq_inv_comp] at e
  rw [e]
  infer_instance

/-! ### A criterion for the comparison map not to be an isomorphism -/

section General

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.ProjectiveSpectrum.Proj

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose _root_.AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] {ψ : 𝒜 →+*ᵍ ℬ}

/-- **A criterion for `θ_k` not to be an isomorphism.** Let `ψ : 𝒜 ⟶ ℬ` be a homomorphism of
graded rings for which `Proj ℬ ⟶ Proj 𝒜` is defined and an isomorphism. If `ψ` kills a
homogeneous element `a` of degree `k` whose fraction `a / 1` is nonzero at some point of
`Proj 𝒜`, then the comparison map `twistMap 𝒜 ℬ ψ k` is not an isomorphism. -/
theorem not_isIso_twistMap_of_map_eq_zero
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
    [IsIso (AlgebraicGeometry.Proj.map ψ hψ)] (k : ℕ) (a : 𝒜 k) (ha : ψ a = 0)
    (w : ProjectiveSpectrum 𝒜)
    (hz : LocalizedModule.mk (a : A) (1 : w.asHomogeneousIdeal.toIdeal.primeCompl) ≠ 0) :
    ¬ IsIso (twistMap 𝒜 ℬ ψ k) := by
  intro hθ
  have hdom := Stacks.AlgebraicGeometry.ProjShared.mapDomain_eq_top_of_irrelevant_le_map
    𝒜 ℬ ψ hψ
  have := isIso_restrictTwistMap 𝒜 ℬ ψ hψ hdom k
  set s := (twistingSheaf 𝒜 k).val.map
    (homOfLE (le_top : AlgebraicGeometry.Proj.map ψ hψ ''ᵁ ⊤ ≤ ⊤)).op
    (degreeSection 𝒜 k a) with hsdef
  have himg : (restrictTwistMap 𝒜 ℬ ψ hψ hdom k).val.app (Opposite.op ⊤) s = 0 := by
    refine (restrictTwistMap_degreeSection 𝒜 ℬ ψ hψ hdom k a ⊤).trans ?_
    apply Subtype.ext
    funext y
    change (degreeSection ℬ k ⟨ψ a, ψ.map_mem a.2⟩).1 ⟨y.1, trivial⟩ = 0
    rw [Stacks.AlgebraicGeometry.ProjTwistSections.degreeSection_apply]
    simp only [ha]
    exact LocalizedModule.zero_mk _
  have hs : s = 0 := by
    have h1 := congrArg (fun t => (inv (restrictTwistMap 𝒜 ℬ ψ hψ hdom k)).val.app
      (Opposite.op ⊤) t) himg
    simp only [map_zero] at h1
    exact ((congrArg (fun φ => (φ.val.app (Opposite.op ⊤)).hom s)
      (IsIso.hom_inv_id (restrictTwistMap 𝒜 ℬ ψ hψ hdom k))).symm).trans h1
  have hw : w ∈ AlgebraicGeometry.Proj.map ψ hψ ''ᵁ ⊤ := by
    refine ⟨(inv (AlgebraicGeometry.Proj.map ψ hψ)).base w, trivial, ?_⟩
    have h : (inv (AlgebraicGeometry.Proj.map ψ hψ) ≫ AlgebraicGeometry.Proj.map ψ hψ).base w =
        w := by
      rw [IsIso.inv_hom_id]
      rfl
    exact h
  have hval := congrArg (fun t => t.1 ⟨w, hw⟩) hs
  change (degreeSection 𝒜 k a).1 ⟨w, trivial⟩ = 0 at hval
  rw [Stacks.AlgebraicGeometry.ProjTwistSections.degreeSection_apply] at hval
  exact hz hval

/-- **A square-zero element whose annihilator is the ideal it generates is nonzero at every point
of `Proj`.** -/
theorem mk_ne_zero_of_mul_self_eq_zero (a : A) (h₂ : a * a = 0)
    (hann : ∀ s : A, s * a = 0 → s ∈ Ideal.span {a}) (p : ProjectiveSpectrum 𝒜) :
    LocalizedModule.mk a (1 : p.asHomogeneousIdeal.toIdeal.primeCompl) ≠ 0 := by
  intro h
  rw [← LocalizedModule.zero_mk (1 : p.asHomogeneousIdeal.toIdeal.primeCompl),
    LocalizedModule.mk_eq] at h
  obtain ⟨u, hu⟩ := h
  simp only [one_smul, smul_zero] at hu
  have hua : (u : A) * a = 0 := hu
  have hx : a ∈ p.asHomogeneousIdeal.toIdeal :=
    p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, h₂]; exact zero_mem _)
  exact u.2 ((Ideal.span_singleton_le_iff_mem _).2 hx (hann _ hua))

end General

/-! ### The counterexample -/

section Counterexample

variable [Nontrivial R]

attribute [local instance] ProjectiveSpectrum.isPrime

/-- `ψ y` is not nilpotent in `B`. -/
theorem psi_yA_pow_ne_zero (k : ℕ) : psi R (yA R) ^ k ≠ 0 := by
  classical
  rw [yA, psi_mk, ← map_pow, Ne, Ideal.Quotient.eq_zero_iff_mem, mem_relB_iff]
  intro h
  have hm : Finsupp.single 1 k ∈ (X 1 ^ k : MvPolynomial (Fin 2) R).support := by
    rw [X_pow_eq_monomial, support_monomial, ite_eq_right one_ne_zero]
    exact Finset.mem_singleton_self _
  exact h _ hm (by simp)

/-- The degree-zero localization `B_(ψ y)` is a nontrivial ring. -/
instance nontrivial_away :
    Nontrivial (HomogeneousLocalization.Away (gradB R) (psi R (yA R))) := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have hv := congrArg HomogeneousLocalization.val h
  rw [HomogeneousLocalization.val_zero, HomogeneousLocalization.val_one] at hv
  have h1 : algebraMap (RingB R) (Localization.Away (psi R (yA R))) 1 = 0 :=
    (map_one _).trans hv.symm
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers (psi R (yA R)))] at h1
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := h1
  exact psi_yA_pow_ne_zero R k (by simpa using hk)

omit [Nontrivial R] in
/-- The fraction `x / 1` is nonzero at every point of `Proj A`. -/
theorem mk_xA_ne_zero (p : ProjectiveSpectrum (gradA R)) :
    LocalizedModule.mk (xA R) (1 : p.asHomogeneousIdeal.toIdeal.primeCompl) ≠ 0 :=
  mk_ne_zero_of_mul_self_eq_zero (xA R) (xA_sq R) (fun _ h => mem_span_xA_of_mul_eq_zero R h) p

/-- **The comparison map `θ₁ : r_ψ^*𝒪_{Proj A}(1) ⟶ 𝒪_{Proj B}(1)` is not an isomorphism**,
although `ψ : A ⟶ B` is surjective (`surjective_psi`) and `Proj B ⟶ Proj A` is an isomorphism
(`isIso_projMap`). -/
theorem not_isIso_twistMap : ¬ IsIso (twistMap (gradA R) (gradB R) (psi R) ((1 : ℕ) : ℤ)) := by
  obtain ⟨pt⟩ : Nonempty (PrimeSpectrum (HomogeneousLocalization.Away (gradB R)
    (psi R (yA R)))) := inferInstance
  let w : ProjectiveSpectrum (gradA R) :=
    (AlgebraicGeometry.Proj.map (psi R) (irrelevant_le_map R)).base
      ((AlgebraicGeometry.Proj.awayι (gradB R) (psi R (yA R)) ((psi R).map_mem (yA_mem R))
        two_pos).base pt)
  exact not_isIso_twistMap_of_map_eq_zero (irrelevant_le_map R) 1 ⟨xA R, xA_mem R⟩ (psi_xA R) w
    (mk_xA_ne_zero R w)

end Counterexample

end Stacks.AlgebraicGeometry.ProjTwistCompare.NotIsoExample

end
