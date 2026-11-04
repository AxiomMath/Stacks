module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.Flat.Localization
public import StacksFrontier.RingTheory.Depth.FlatLocalHom
public import StacksFrontier.RingTheory.Depth.RingEquiv
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeOverField
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedConeDepthDimension
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationDimensionBounds

/-!
# Depth and dimension along the fibres of the punctured cone

Let `A = ⨁_{d ≥ 0} A_d` be a graded Noetherian ring, let `f ∈ A₁` and let `p` be a prime of `A`
with `f ∉ p`. Its homogeneous core `p*` is a relevant homogeneous prime, that is a point of
`Proj A`, and the homogeneous localization `A_{(p*)}` is the local ring of `Proj A` there. A prime
`p` of the punctured cone lies on the fibre over `p*`, as its generic point (`p = p*`) or as a
closed point (`p ≠ p*`). This file computes how depth and dimension change along that fibre, in
the form consumed by Faltings' annihilator theorem in the proof of [Stacks, Tag 0EL1]:

* `depth(A_p) ≥ depth(A_{(p*)}) + [p ≠ p*]`;
* `dim((A/p)_q) ≥ trdeg_k κ(p*) + [p = p*]` for `q ⊇ p` maximal, when `A` is of finite type over a
  field `k` that lands in `A₀`.

The extra unit falls on the depth at a closed point of the fibre and on the dimension at its
generic point, so in both cases the sum gains one.

## The structure of the fibre

Write `A_{(p)}` for the fractions `a / s` with `a`, `s` homogeneous of the same degree and `s ∉ p`
(`DegreeZeroLocal`); it is `A_{(p*)}` (`degreeZeroLocalEquiv`). The ring map
`A → A_{(p)}[X]`, `a ↦ ∑ᵢ (aᵢ / fⁱ) Xⁱ` (`polynomialOfGraded`) is a section of the evaluation at
`X ↦ f`, and from it one proves that `A_p` is the localization of the polynomial ring
`A_{(p)}[X]` at a prime (`isLocalization_evalAtPrime`). Hence `A_{(p)} → A_p` is flat
(`flat_degreeZeroToAtPrime`) and local (`isLocalHom_degreeZeroToAtPrime`), and its closed fibre is
`A_p / p* A_p` (`map_maximalIdeal_degreeZeroToAtPrime`), a domain whose maximal ideal is nonzero
when `p ≠ p*`. Stacks 0337 then gives the depth bound.

For the dimension, `dim((A/p)_q) = trdeg_k κ(p)` by Stacks 00P0 (`relativeDimAt_eq_trdeg`), the
residue field `κ(p*)` embeds in `κ(p)` (`residueFieldAlgHom`), and when `p` is homogeneous the
residue of `f` is transcendental over it (`transcendental_residue_algebraMap`).

## Main results

* `Stacks.Algebraization.SectionRingCone.depth_atPrime_homogeneousCore_add_le_localizedDepth` —
  the depth bound.
* `Stacks.Algebraization.SectionRingCone.trdeg_residueField_core_add_le_relativeDimAt` — the
  dimension bound.
* `Stacks.Algebraization.SectionRingCone.isMaximal_of_irrelevant_le` — a prime containing the
  irrelevant ideal is maximal when `A₀` is Artinian, so the dimension bound applies at it.
* `Stacks.Algebraization.SectionRingCone.depth_add_trdeg_add_one_le_depthAddRelativeDim` — the two
  combined, in the arithmetic of Faltings' annihilator theorem.

## Implementation notes

The `k`-algebra structure on `A_{(p*)}` is not an instance: it exists only when the image of `k`
lies in `A₀`, which is the hypothesis `hk`, and it is introduced by `degreeZeroAlgebra`. The
statements that mention it bind it with `letI`.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0337](https://stacks.math.columbia.edu/tag/0337)
* [Stacks Project, Tag 00P0](https://stacks.math.columbia.edu/tag/00P0)
-/

@[expose] public noncomputable section

open DirectSum IsLocalRing Polynomial

namespace Stacks.Algebraization.SectionRingCone

variable {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-! ### The homogeneous elements outside a prime -/

section Submonoid

variable (p : Ideal A) [p.IsPrime]

/-- The multiplicative set of homogeneous elements of `A` outside the prime `p`. -/
def homogeneousCompl : Submonoid A where
  carrier := {a | a ∉ p ∧ SetLike.IsHomogeneousElem 𝒜 a}
  mul_mem' {a b} ha hb :=
    ⟨fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim ha.1 hb.1, ha.2.mul hb.2⟩
  one_mem' := ⟨(Ideal.ne_top_iff_one p).mp (Ideal.IsPrime.ne_top inferInstance),
    SetLike.isHomogeneousElem_one 𝒜⟩

variable {𝒜 p}

/-- Membership in `homogeneousCompl`. -/
theorem mem_homogeneousCompl_iff {a : A} :
    a ∈ homogeneousCompl 𝒜 p ↔ a ∉ p ∧ SetLike.IsHomogeneousElem 𝒜 a := Iff.rfl

/-- An element of a graded piece outside `p` lies in `homogeneousCompl`. -/
theorem mem_homogeneousCompl_of_mem {a : A} {i : ℕ} (ha : a ∈ 𝒜 i) (hap : a ∉ p) :
    a ∈ homogeneousCompl 𝒜 p := ⟨hap, ⟨i, ha⟩⟩

/-- The homogeneous elements outside `p` are outside `p`. -/
theorem homogeneousCompl_le_primeCompl : homogeneousCompl 𝒜 p ≤ p.primeCompl :=
  fun _ ha => ha.1

/-- **A homogeneous element killed by an element outside a homogeneous ideal is killed by a
homogeneous component outside it.** -/
theorem exists_component_notMem_mul_eq_zero {J : Ideal A} (hJ : J.IsHomogeneous 𝒜) {c a : A}
    {i : ℕ} (ha : a ∈ 𝒜 i) (hc : c ∉ J) (hca : c * a = 0) :
    ∃ j : ℕ, (decompose 𝒜 c j : A) ∉ J ∧ (decompose 𝒜 c j : A) * a = 0 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, (decompose 𝒜 c j : A) ∉ J := by
    by_contra h
    push Not at h
    exact hc ((hJ.mem_iff).mpr h)
  refine ⟨j, hj, ?_⟩
  rw [← DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 ha, hca, decompose_zero]
  rfl

end Submonoid


/-! ### The homogeneous core and the degree-zero local ring -/

section Core

variable (p : Ideal A) [p.IsPrime]

/-- The homogeneous core `p*` of `p`, as an ideal of `A`. -/
abbrev coreIdeal : Ideal A := (Ideal.homogeneousCore 𝒜 p).toIdeal

/-- The homogeneous core of a prime is prime. -/
instance coreIdeal_isPrime : (coreIdeal 𝒜 p).IsPrime :=
  Ideal.IsPrime.homogeneousCore inferInstance

/-- The homogeneous core is a homogeneous ideal. -/
theorem coreIdeal_isHomogeneous : (coreIdeal 𝒜 p).IsHomogeneous 𝒜 :=
  (Ideal.homogeneousCore 𝒜 p).isHomogeneous

/-- The homogeneous core of `p` is contained in `p`. -/
theorem coreIdeal_le : coreIdeal 𝒜 p ≤ p := Ideal.toIdeal_homogeneousCore_le 𝒜 p

variable {𝒜 p}

/-- A homogeneous element lies in `p` exactly when it lies in its homogeneous core. -/
theorem mem_coreIdeal_iff_of_mem {a : A} {i : ℕ} (ha : a ∈ 𝒜 i) : a ∈ coreIdeal 𝒜 p ↔ a ∈ p :=
  ⟨fun h => coreIdeal_le 𝒜 p h,
    fun h => Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨i, ha⟩ h⟩

variable (𝒜 p)

/-- **The degree-zero local ring.** The fractions `a / s` with `a`, `s` homogeneous of the same
degree and `s ∉ p`. It is the homogeneous localization at the homogeneous core of `p`
(`degreeZeroLocalEquiv`), presented with denominators in `homogeneousCompl 𝒜 p` so that it sits
inside the localization of `A` at the homogeneous elements outside `p`. -/
abbrev DegreeZeroLocal := HomogeneousLocalization 𝒜 (homogeneousCompl 𝒜 p)

/-- The localization of `A` at the homogeneous elements outside `p`. -/
abbrev HomogeneousFractions := Localization (homogeneousCompl 𝒜 p)

/-- The homogeneous elements outside `p` lie outside its homogeneous core. -/
theorem homogeneousCompl_le_comap :
    homogeneousCompl 𝒜 p ≤ (coreIdeal 𝒜 p).primeCompl.comap (GradedRingHom.id 𝒜) :=
  fun a ha h => ha.1 (coreIdeal_le 𝒜 p h)

/-- **The degree-zero local ring is the homogeneous localization at the homogeneous core.** -/
def degreeZeroLocalEquiv :
    DegreeZeroLocal 𝒜 p ≃+* HomogeneousLocalization.AtPrime 𝒜 (coreIdeal 𝒜 p) :=
  RingEquiv.ofBijective
    (HomogeneousLocalization.map (GradedRingHom.id 𝒜) (homogeneousCompl_le_comap 𝒜 p)) <| by
    refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx => ?_, fun y => ?_⟩
    · obtain ⟨z, rfl⟩ := HomogeneousLocalization.mk_surjective x
      rw [HomogeneousLocalization.map_mk, HomogeneousLocalization.ext_iff_val,
        HomogeneousLocalization.val_mk, HomogeneousLocalization.val_zero,
        Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at hx
      obtain ⟨⟨c, hc⟩, hcz⟩ := hx
      obtain ⟨j, hj, hj0⟩ :=
        exists_component_notMem_mul_eq_zero (coreIdeal_isHomogeneous 𝒜 p) z.num.2 hc hcz
      rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk,
        HomogeneousLocalization.val_zero, Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
      exact ⟨⟨_, mem_homogeneousCompl_of_mem (decompose 𝒜 c j).2
        fun h => hj ((mem_coreIdeal_iff_of_mem (decompose 𝒜 c j).2).mpr h)⟩, hj0⟩
    · obtain ⟨w, rfl⟩ := HomogeneousLocalization.mk_surjective y
      refine ⟨HomogeneousLocalization.mk ⟨w.deg, w.num, w.den,
        mem_homogeneousCompl_of_mem w.den.2 fun h => w.den_mem
          ((mem_coreIdeal_iff_of_mem w.den.2).mpr h)⟩, ?_⟩
      rw [HomogeneousLocalization.map_mk]
      rfl

/-- The degree-zero local ring is nontrivial. -/
instance degreeZeroLocal_nontrivial : Nontrivial (DegreeZeroLocal 𝒜 p) :=
  (degreeZeroLocalEquiv 𝒜 p).symm.injective.nontrivial

/-- The degree-zero local ring is local. -/
instance degreeZeroLocal_isLocalRing : IsLocalRing (DegreeZeroLocal 𝒜 p) :=
  IsLocalRing.of_surjective' (degreeZeroLocalEquiv 𝒜 p).symm.toRingHom
    (degreeZeroLocalEquiv 𝒜 p).symm.surjective

end Core

/-! ### Fractions and common denominators -/

section Fractions

variable {𝒜} {p : Ideal A} [p.IsPrime]

/-- The fraction `a / s` of `DegreeZeroLocal 𝒜 p`, for `a` and `s` homogeneous of degree `i`. -/
def degreeZeroFraction {i : ℕ} {a s : A} (ha : a ∈ 𝒜 i) (hs : s ∈ 𝒜 i)
    (hsp : s ∈ homogeneousCompl 𝒜 p) : DegreeZeroLocal 𝒜 p :=
  HomogeneousLocalization.mk ⟨i, ⟨a, ha⟩, ⟨s, hs⟩, hsp⟩

/-- The value of `a / s` in the localization at the homogeneous elements outside `p`. -/
theorem val_degreeZeroFraction {i : ℕ} {a s : A} (ha : a ∈ 𝒜 i) (hs : s ∈ 𝒜 i)
    (hsp : s ∈ homogeneousCompl 𝒜 p) :
    (degreeZeroFraction ha hs hsp).val = Localization.mk a ⟨s, hsp⟩ :=
  HomogeneousLocalization.val_mk _

/-- Every element of the degree-zero local ring is a fraction `a / s` of homogeneous elements of
the same degree. -/
theorem exists_eq_degreeZeroFraction (x : DegreeZeroLocal 𝒜 p) :
    ∃ (i : ℕ) (a s : A) (ha : a ∈ 𝒜 i) (hs : s ∈ 𝒜 i) (hsp : s ∈ homogeneousCompl 𝒜 p),
      x = degreeZeroFraction ha hs hsp := by
  obtain ⟨w, rfl⟩ := HomogeneousLocalization.mk_surjective x
  exact ⟨w.deg, w.num, w.den, w.num.2, w.den.2, w.den_mem, rfl⟩

/-- In a localization, multiplying the numerator and the denominator by the same element of the
multiplicative set does not change the fraction. -/
theorem localization_mk_mul_mul {M : Submonoid A} (a : A) (s t : M) :
    Localization.mk (t * a) (t * s) = Localization.mk a s :=
  Localization.mk_eq_mk_iff.mpr (Localization.r_iff_exists.mpr ⟨1, by simp; ring⟩)

/-- **Finitely many elements of the degree-zero local ring have a common denominator.** -/
theorem exists_common_denominator_degreeZeroLocal (s : Finset ℕ) (c : ℕ → DegreeZeroLocal 𝒜 p) :
    ∃ (I : ℕ) (d : homogeneousCompl 𝒜 p) (h : ℕ → A), (d : A) ∈ 𝒜 I ∧
      ∀ n ∈ s, h n ∈ 𝒜 I ∧ (c n).val = Localization.mk (h n) d := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 1, fun _ => 0, SetLike.GradedOne.one_mem, by simp⟩
  | insert a s ha ih =>
    obtain ⟨I, d, h, hd, hh⟩ := ih
    obtain ⟨w, hw⟩ := HomogeneousLocalization.mk_surjective (c a)
    refine ⟨w.deg + I, ⟨w.den, w.den_mem⟩ * d,
      fun n => if n = a then w.num * d else w.den * h n, SetLike.mul_mem_graded w.den.2 hd, ?_⟩
    intro n hn
    rcases Finset.mem_insert.mp hn with rfl | hn'
    · simp only [if_pos rfl]
      refine ⟨SetLike.mul_mem_graded w.num.2 hd, ?_⟩
      rw [← hw, HomogeneousLocalization.val_mk]
      exact Localization.mk_eq_mk_iff.mpr (Localization.r_iff_exists.mpr ⟨1, by simp; ring⟩)
    · have hne : n ≠ a := fun h' => ha (h' ▸ hn')
      simp only [if_neg hne]
      obtain ⟨hhn, hcn⟩ := hh n hn'
      refine ⟨SetLike.mul_mem_graded w.den.2 hhn, ?_⟩
      rw [hcn]
      exact (localization_mk_mul_mul (h n) d ⟨w.den, w.den_mem⟩).symm

/-- The projection to a graded piece of a homogeneous element. -/
theorem gradedRingProj_of_mem {x : A} {j : ℕ} (hx : x ∈ 𝒜 j) (k : ℕ) :
    GradedRing.proj 𝒜 k x = if j = k then x else 0 := by
  rw [GradedRing.proj_apply]
  split_ifs with h
  · subst h
    exact DirectSum.decompose_of_mem_same 𝒜 hx
  · exact DirectSum.decompose_of_mem_ne 𝒜 hx h

/-- A power of a degree-one element has the degree of the exponent. -/
private theorem pow_mem_graded_of_mem_one {f : A} (hf : f ∈ 𝒜 1) (i : ℕ) : f ^ i ∈ 𝒜 i := by
  simpa using SetLike.pow_mem_graded i hf

/-- The component of a sum of homogeneous elements of pairwise distinct degrees `m + k` in degree
`m + n` is the summand `g n`. -/
private theorem proj_sum_eq_of_mem {s : Finset ℕ} {g : ℕ → A} {m n : ℕ}
    (hg : ∀ k ∈ s, g k ∈ 𝒜 (m + k)) (hn : n ∈ s) :
    GradedRing.proj 𝒜 (m + n) (∑ k ∈ s, g k) = g n := by
  rw [map_sum, Finset.sum_eq_single n (fun k hk hkn => by
      rw [gradedRingProj_of_mem (hg k hk), if_neg (by omega)]) (fun h' => absurd hn h'),
    gradedRingProj_of_mem (hg n hn), if_pos rfl]

end Fractions


/-! ### The polynomial presentation of the local ring at `p` -/

section Polynomial

variable {𝒜} {p : Ideal A} [p.IsPrime] {f : A} (hf : f ∈ 𝒜 1) (hfp : f ∉ p)

include hf hfp in
/-- The powers of `f` are homogeneous elements outside `p`. -/
theorem pow_mem_homogeneousCompl (i : ℕ) : f ^ i ∈ homogeneousCompl 𝒜 p :=
  mem_homogeneousCompl_of_mem (pow_mem_graded_of_mem_one hf i)
    fun h => hfp (Ideal.IsPrime.mem_of_pow_mem inferInstance i h)

/-- The fraction `a / f ^ i` of degree zero, for `a` of degree `i`. -/
def fracPow (i : ℕ) (a : 𝒜 i) : DegreeZeroLocal 𝒜 p :=
  degreeZeroFraction a.2 (by simpa using SetLike.pow_mem_graded i hf : f ^ i ∈ 𝒜 i)
    (pow_mem_homogeneousCompl hf hfp i)

/-- The value of `a / f ^ i` in the localization at the homogeneous elements outside `p`. -/
theorem val_fracPow (i : ℕ) (a : 𝒜 i) :
    (fracPow hf hfp i a).val = Localization.mk (a : A) ⟨f ^ i, pow_mem_homogeneousCompl hf hfp i⟩ :=
  val_degreeZeroFraction _ _ _

/-- The degree-`i` component `a ↦ (a / f ^ i) X ^ i` of `polynomialOfGraded`. -/
def polyComponent (i : ℕ) : 𝒜 i →+ (DegreeZeroLocal 𝒜 p)[X] where
  toFun a := C (fracPow hf hfp i a) * X ^ i
  map_zero' := by
    rw [show fracPow hf hfp i 0 = 0 from HomogeneousLocalization.ext_iff_val _ _ |>.mpr (by
      rw [val_fracPow, HomogeneousLocalization.val_zero]; exact Localization.mk_zero _)]
    simp
  map_add' a b := by
    rw [show fracPow hf hfp i (a + b) = fracPow hf hfp i a + fracPow hf hfp i b from
      HomogeneousLocalization.ext_iff_val _ _ |>.mpr (by
        rw [HomogeneousLocalization.val_add, val_fracPow, val_fracPow, val_fracPow,
          Localization.add_mk_self]; rfl)]
    simp [add_mul]

/-- **The ring map `A → A_{(p)}[X]`, `a ↦ ∑ᵢ (aᵢ / fⁱ) Xⁱ`.** It reads the grading of `A` as powers
of the variable, the variable standing for the unit `f` of degree one. -/
def polynomialOfGraded : A →+* (DegreeZeroLocal 𝒜 p)[X] :=
  (DirectSum.toSemiring (fun i => polyComponent hf hfp i)
      (by
        change C (fracPow hf hfp 0 _) * X ^ 0 = 1
        rw [pow_zero, mul_one, ← C_1]
        congr 1
        rw [HomogeneousLocalization.ext_iff_val, val_fracPow, HomogeneousLocalization.val_one]
        simp [Localization.mk_one])
      (fun {i j} a b => by
        change C (fracPow hf hfp (i + j) ⟨(a : A) * b, SetLike.mul_mem_graded a.2 b.2⟩) *
            X ^ (i + j) = (C (fracPow hf hfp i a) * X ^ i) * (C (fracPow hf hfp j b) * X ^ j)
        have : fracPow hf hfp (i + j) ⟨(a : A) * b, SetLike.mul_mem_graded a.2 b.2⟩ =
            fracPow hf hfp i a * fracPow hf hfp j b := by
          rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul, val_fracPow,
            val_fracPow, val_fracPow, Localization.mk_mul]
          congr 1
          exact Subtype.ext (pow_add f i j)
        rw [this, C_mul, pow_add]
        ring)).comp (decomposeRingEquiv 𝒜).toRingHom

/-- On an element `a` of degree `i`, `polynomialOfGraded` is the monomial `(a / fⁱ) Xⁱ`. -/
theorem polynomialOfGraded_of_mem {a : A} {i : ℕ} (ha : a ∈ 𝒜 i) :
    polynomialOfGraded hf hfp a = C (fracPow hf hfp i ⟨a, ha⟩) * X ^ i := by
  have h1 : (decomposeRingEquiv 𝒜).toRingHom a = DirectSum.of (fun i => 𝒜 i) i ⟨a, ha⟩ :=
    decompose_of_mem 𝒜 ha
  rw [polynomialOfGraded, RingHom.comp_apply, h1, DirectSum.toSemiring_of]
  rfl

end Polynomial


/-! ### The polynomial ring over the degree-zero local ring maps onto a localization -/

section Evaluation

variable (p : Ideal A) [p.IsPrime]

/-- The localization map `A_{h(p)} → A_p` from the homogeneous fractions to the local ring. -/
def fractionsToAtPrime : HomogeneousFractions 𝒜 p →+* Localization.AtPrime p :=
  IsLocalization.map (Localization.AtPrime p) (RingHom.id A)
    (show homogeneousCompl 𝒜 p ≤ p.primeCompl.comap (RingHom.id A) from fun _ ha => ha.1)

/-- The structure map `A_{(p)} → A_p`, sending `a / s` to `a / s`. -/
def degreeZeroToAtPrime : DegreeZeroLocal 𝒜 p →+* Localization.AtPrime p :=
  (fractionsToAtPrime 𝒜 p).comp (algebraMap (DegreeZeroLocal 𝒜 p) (HomogeneousFractions 𝒜 p))

variable {𝒜 p}

/-- `fractionsToAtPrime` is compatible with the structure maps from `A`. -/
theorem fractionsToAtPrime_algebraMap (a : A) :
    fractionsToAtPrime 𝒜 p (algebraMap A _ a) = algebraMap A (Localization.AtPrime p) a :=
  IsLocalization.map_eq _ _

/-- The image of `a / s` in the localization at the homogeneous elements outside `p`. -/
theorem algebraMap_degreeZeroFraction {i : ℕ} {a s : A} (ha : a ∈ 𝒜 i) (hs : s ∈ 𝒜 i)
    (hsp : s ∈ homogeneousCompl 𝒜 p) :
    algebraMap (DegreeZeroLocal 𝒜 p) (HomogeneousFractions 𝒜 p) (degreeZeroFraction ha hs hsp) =
      IsLocalization.mk' (HomogeneousFractions 𝒜 p) a (⟨s, hsp⟩ : homogeneousCompl 𝒜 p) := by
  rw [HomogeneousLocalization.algebraMap_apply, val_degreeZeroFraction, Localization.mk_eq_mk']

/-- The image of `a / s` in `A_p` is the fraction `a / s`. -/
theorem degreeZeroToAtPrime_fraction {i : ℕ} {a s : A} (ha : a ∈ 𝒜 i) (hs : s ∈ 𝒜 i)
    (hsp : s ∈ homogeneousCompl 𝒜 p) :
    degreeZeroToAtPrime 𝒜 p (degreeZeroFraction ha hs hsp) =
      IsLocalization.mk' (Localization.AtPrime p) a (⟨s, hsp.1⟩ : p.primeCompl) := by
  rw [degreeZeroToAtPrime, RingHom.comp_apply, algebraMap_degreeZeroFraction, fractionsToAtPrime,
    IsLocalization.map_mk']
  rfl

variable {f : A} (hf : f ∈ 𝒜 1) (hfp : f ∉ p)

variable (𝒜 p) in
/-- The evaluation `A_{(p)}[X] → A_{h(p)}` at the unit `X ↦ f`. -/
def evalFractions (f : A) : (DegreeZeroLocal 𝒜 p)[X] →+* HomogeneousFractions 𝒜 p :=
  Polynomial.eval₂RingHom (algebraMap _ _) (algebraMap A (HomogeneousFractions 𝒜 p) f)

variable (𝒜 p) in
/-- The evaluation `A_{(p)}[X] → A_p` at `X ↦ f`. -/
def evalAtPrime (f : A) : (DegreeZeroLocal 𝒜 p)[X] →+* Localization.AtPrime p :=
  (fractionsToAtPrime 𝒜 p).comp (evalFractions 𝒜 p f)

/-- `evalAtPrime` on constants is the structure map `A_{(p)} → A_p`. -/
theorem evalAtPrime_C (b : DegreeZeroLocal 𝒜 p) :
    evalAtPrime 𝒜 p f (C b) = degreeZeroToAtPrime 𝒜 p b := by
  rw [evalAtPrime, RingHom.comp_apply, evalFractions, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_C]
  rfl

/-- `evalAtPrime` sends the variable to `f`. -/
theorem evalAtPrime_X : evalAtPrime 𝒜 p f X = algebraMap A (Localization.AtPrime p) f := by
  rw [evalAtPrime, RingHom.comp_apply, evalFractions, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X, fractionsToAtPrime_algebraMap]

/-- **Evaluating `∑ᵢ (aᵢ / fⁱ) Xⁱ` at `f` gives back `a`.** -/
theorem evalFractions_polynomialOfGraded (a : A) :
    evalFractions 𝒜 p f (polynomialOfGraded hf hfp a) = algebraMap A _ a := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i a =>
    obtain ⟨a, ha'⟩ := a
    rw [polynomialOfGraded_of_mem hf hfp ha', evalFractions, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, fracPow,
      algebraMap_degreeZeroFraction, ← map_pow, IsLocalization.mk'_spec]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]

/-- **Evaluating `∑ᵢ (aᵢ / fⁱ) Xⁱ` at `f` in `A_p` gives back `a`.** -/
theorem evalAtPrime_polynomialOfGraded (a : A) :
    evalAtPrime 𝒜 p f (polynomialOfGraded hf hfp a) = algebraMap A (Localization.AtPrime p) a := by
  rw [evalAtPrime, RingHom.comp_apply, evalFractions_polynomialOfGraded,
    fractionsToAtPrime_algebraMap]

/-- **Clearing a common denominator in the evaluation.** If the coefficients of `t` are
`h n / d`, then `d · t(f) = ∑ₙ h n fⁿ`. -/
theorem algebraMap_mul_evalFractions (t : (DegreeZeroLocal 𝒜 p)[X]) (d : homogeneousCompl 𝒜 p)
    (h : ℕ → A) (hh : ∀ n ∈ t.support, (t.coeff n).val = Localization.mk (h n) d) :
    algebraMap A (HomogeneousFractions 𝒜 p) d * evalFractions 𝒜 p f t =
      algebraMap A _ (∑ n ∈ t.support, h n * f ^ n) := by
  rw [evalFractions, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
    Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [← mul_assoc, HomogeneousLocalization.algebraMap_apply, hh n hn, Localization.mk_eq_mk',
    IsLocalization.mk'_spec', map_mul, map_pow]

/-- **Clearing a common denominator in the evaluation in `A_p`.** -/
private theorem algebraMap_mul_evalAtPrime (t : (DegreeZeroLocal 𝒜 p)[X])
    (d : homogeneousCompl 𝒜 p) (h : ℕ → A)
    (hh : ∀ n ∈ t.support, (t.coeff n).val = Localization.mk (h n) d) :
    algebraMap A (Localization.AtPrime p) d * evalAtPrime 𝒜 p f t =
      algebraMap A _ (∑ n ∈ t.support, h n * f ^ n) := by
  have := congrArg (fractionsToAtPrime 𝒜 p) (algebraMap_mul_evalFractions (f := f) t d h hh)
  rw [map_mul, fractionsToAtPrime_algebraMap, fractionsToAtPrime_algebraMap] at this
  exact this

include hf hfp in
/-- **The evaluation `A_{(p)}[X] → A_{h(p)}` is injective.** A polynomial whose value at `f`
vanishes has, over a common homogeneous denominator, numerators `h n` with `∑ₙ h n fⁿ` killed by a
homogeneous element `v ∉ p`; the summands have distinct degrees, so `v h n fⁿ = 0` for each `n`,
and `h n / d = 0` already in the degree-zero local ring. -/
theorem evalFractions_injective : Function.Injective (evalFractions 𝒜 p f) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨I, d, h, hd, hh⟩ := exists_common_denominator_degreeZeroLocal t.support t.coeff
  have key : algebraMap A (HomogeneousFractions 𝒜 p) (∑ n ∈ t.support, h n * f ^ n) = 0 := by
    rw [← algebraMap_mul_evalFractions t d h fun n hn => (hh n hn).2, ht, mul_zero]
  obtain ⟨⟨v, hv⟩, hv0⟩ := (IsLocalization.map_eq_zero_iff (homogeneousCompl 𝒜 p) _ _).mp key
  obtain ⟨e, he⟩ := hv.2
  refine Polynomial.ext fun n => ?_
  rw [Polynomial.coeff_zero]
  by_cases hn : n ∈ t.support
  swap
  · exact Polynomial.notMem_support_iff.mp hn
  have hmem : ∀ k ∈ t.support, v * (h k * f ^ k) ∈ 𝒜 (e + I + k) := fun k hk => by
    rw [add_assoc]
    exact SetLike.mul_mem_graded he
      (SetLike.mul_mem_graded (hh k hk).1 (pow_mem_graded_of_mem_one hf k))
  have hcomp : v * (h n * f ^ n) = 0 := by
    have h1 := congrArg (GradedRing.proj 𝒜 (e + I + n)) hv0
    rw [Finset.mul_sum, proj_sum_eq_of_mem hmem hn, map_zero] at h1
    exact h1
  rw [HomogeneousLocalization.ext_iff_val, (hh n hn).2, HomogeneousLocalization.val_zero,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨v * f ^ n, (homogeneousCompl 𝒜 p).mul_mem hv (pow_mem_homogeneousCompl hf hfp n)⟩, ?_⟩
  show v * f ^ n * h n = 0
  rw [mul_assoc, mul_comm (f ^ n), hcomp]

end Evaluation



/-! ### The local ring at `p` is a localization of a polynomial ring over `A_{(p)}` -/

section LocalizationOfPolynomial

variable (p : Ideal A) [p.IsPrime]

/-- The prime of `A_{(p)}[X]` lying under the maximal ideal of `A_p` along the evaluation. -/
abbrev polynomialPrime (f : A) : Ideal (DegreeZeroLocal 𝒜 p)[X] :=
  (maximalIdeal (Localization.AtPrime p)).comap (evalAtPrime 𝒜 p f)

variable {𝒜 p} {f : A} (hf : f ∈ 𝒜 1) (hfp : f ∉ p)

/-- The polynomial of an element outside `p` lies outside the prime `polynomialPrime 𝒜 p f`. -/
private theorem polynomialOfGraded_mem_primeCompl {u : A} (hu : u ∈ p.primeCompl) :
    polynomialOfGraded hf hfp u ∈ (polynomialPrime 𝒜 p f).primeCompl := by
  show evalAtPrime 𝒜 p f (polynomialOfGraded hf hfp u) ∉ maximalIdeal _
  rw [evalAtPrime_polynomialOfGraded, IsLocalization.AtPrime.to_map_mem_maximal_iff _ p]
  exact hu

include hf hfp in
/-- **A polynomial killed by the evaluation at `f` is killed by a polynomial outside the prime.**
Over a common homogeneous denominator the value is `∑ₙ h n fⁿ`, killed by some `u ∉ p`; the
polynomial of `u` is outside the prime, and kills the given polynomial because the evaluation into
the homogeneous fractions is injective. -/
theorem exists_mul_eq_zero_of_evalAtPrime_eq_zero (t : (DegreeZeroLocal 𝒜 p)[X])
    (ht : evalAtPrime 𝒜 p f t = 0) :
    ∃ c : (polynomialPrime 𝒜 p f).primeCompl, (c : (DegreeZeroLocal 𝒜 p)[X]) * t = 0 := by
  classical
  obtain ⟨I, d, h, -, hh⟩ := exists_common_denominator_degreeZeroLocal t.support t.coeff
  have hmul := algebraMap_mul_evalFractions (f := f) t d h fun n hn => (hh n hn).2
  have hAp : algebraMap A (Localization.AtPrime p) (∑ n ∈ t.support, h n * f ^ n) = 0 := by
    rw [← algebraMap_mul_evalAtPrime (f := f) t d h fun n hn => (hh n hn).2, ht, mul_zero]
  obtain ⟨⟨u, hu⟩, hu0⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl _ _).mp hAp
  refine ⟨⟨polynomialOfGraded hf hfp u, polynomialOfGraded_mem_primeCompl hf hfp hu⟩, ?_⟩
  · apply evalFractions_injective hf hfp
    rw [map_zero, map_mul, evalFractions_polynomialOfGraded]
    have hunit := IsLocalization.map_units (HomogeneousFractions 𝒜 p) d
    refine (hunit.mul_right_eq_zero).mp ?_
    rw [mul_left_comm, hmul, ← map_mul, hu0, map_zero]

include hf hfp in
/-- **`A_p` is a localization of `A_{(p)}[X]`**, the algebra structure being the evaluation at
`X ↦ f`, at the prime lying under the maximal ideal of `A_p`. -/
theorem isLocalization_evalAtPrime :
    letI := (evalAtPrime 𝒜 p f).toAlgebra
    IsLocalization (polynomialPrime 𝒜 p f).primeCompl (Localization.AtPrime p) := by
  let := (evalAtPrime 𝒜 p f).toAlgebra
  refine ⟨fun y => IsLocalRing.notMem_maximalIdeal.mp (show evalAtPrime 𝒜 p f y ∉ _ from y.2),
    fun z => ?_, fun {g g'} hgg' => ?_⟩
  · obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
    refine ⟨⟨polynomialOfGraded hf hfp x,
      ⟨polynomialOfGraded hf hfp s, polynomialOfGraded_mem_primeCompl hf hfp s.2⟩⟩, ?_⟩
    · simp only [RingHom.algebraMap_toAlgebra, evalAtPrime_polynomialOfGraded]
      exact IsLocalization.mk'_spec _ _ _
  · have h0 : evalAtPrime 𝒜 p f (g - g') = 0 := by
      rw [map_sub, sub_eq_zero]
      exact hgg'
    obtain ⟨c, hc⟩ := exists_mul_eq_zero_of_evalAtPrime_eq_zero hf hfp _ h0
    exact ⟨c, by rw [mul_sub, sub_eq_zero] at hc; exact hc⟩

include hf hfp in
/-- The structure map `A_{(p)} → A_p` factors as `A_{(p)} → A_{(p)}[X] → A_p`. -/
theorem degreeZeroToAtPrime_eq_comp :
    degreeZeroToAtPrime 𝒜 p = (evalAtPrime 𝒜 p f).comp Polynomial.C :=
  RingHom.ext fun b => (evalAtPrime_C b).symm

include hf hfp in
/-- **The structure map `A_{(p)} → A_p` is flat**: it is a polynomial extension followed by a
localization. -/
theorem flat_degreeZeroToAtPrime : (degreeZeroToAtPrime 𝒜 p).Flat := by
  have hcomp := degreeZeroToAtPrime_eq_comp hf hfp
  rw [hcomp]
  refine RingHom.Flat.comp ?_ ?_
  · exact (RingHom.flat_algebraMap_iff (R := DegreeZeroLocal 𝒜 p)
      (S := (DegreeZeroLocal 𝒜 p)[X])).mpr inferInstance
  · let := (evalAtPrime 𝒜 p f).toAlgebra
    have := isLocalization_evalAtPrime hf hfp
    have : Module.Flat (DegreeZeroLocal 𝒜 p)[X] (Localization.AtPrime p) :=
      IsLocalization.flat _ (polynomialPrime 𝒜 p f).primeCompl
    exact (RingHom.flat_algebraMap_iff).mpr this

end LocalizationOfPolynomial

/-! ### The structure map is local, and its maximal ideal -/

section Local

variable {p : Ideal A} [p.IsPrime]

/-- A fraction `a / s` with numerator outside `p` is a unit, with inverse `s / a`. -/
theorem isUnit_degreeZeroFraction_of_notMem {i : ℕ} {a s : A} (ha : a ∈ 𝒜 i) (hs : s ∈ 𝒜 i)
    (hsp : s ∈ homogeneousCompl 𝒜 p) (hap : a ∉ p) : IsUnit (degreeZeroFraction ha hs hsp) := by
  refine IsUnit.of_mul_eq_one (degreeZeroFraction hs ha (mem_homogeneousCompl_of_mem ha hap)) ?_
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul, val_degreeZeroFraction,
    val_degreeZeroFraction, HomogeneousLocalization.val_one, Localization.mk_mul]
  convert Localization.mk_self
    ((⟨s, hsp⟩ : homogeneousCompl 𝒜 p) * ⟨a, mem_homogeneousCompl_of_mem ha hap⟩) using 2
  simp [mul_comm]

/-- If the image of `a / s` in `A_p` is a unit then `a ∉ p`. -/
theorem notMem_of_isUnit_degreeZeroToAtPrime {i : ℕ} {a s : A} (ha : a ∈ 𝒜 i) (hs : s ∈ 𝒜 i)
    (hsp : s ∈ homogeneousCompl 𝒜 p)
    (hu : IsUnit (degreeZeroToAtPrime 𝒜 p (degreeZeroFraction ha hs hsp))) : a ∉ p := by
  rw [degreeZeroToAtPrime_fraction] at hu
  have hs' : IsUnit (algebraMap A (Localization.AtPrime p) s) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff _ p s).mpr hsp.1
  have := hu.mul hs'
  rw [IsLocalization.mk'_spec] at this
  exact (IsLocalization.AtPrime.isUnit_to_map_iff _ p a).mp this

/-- **The structure map `A_{(p)} → A_p` is a local homomorphism.** -/
instance isLocalHom_degreeZeroToAtPrime : IsLocalHom (degreeZeroToAtPrime 𝒜 p) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨i, a, s, ha, hs, hsp, rfl⟩ := exists_eq_degreeZeroFraction x
  exact isUnit_degreeZeroFraction_of_notMem 𝒜 ha hs hsp
    (notMem_of_isUnit_degreeZeroToAtPrime 𝒜 ha hs hsp hx)

/-- A fraction `a / s` is in the maximal ideal of `A_{(p)}` exactly when `a ∈ p`. -/
theorem degreeZeroFraction_mem_maximalIdeal_iff {i : ℕ} {a s : A} (ha : a ∈ 𝒜 i)
    (hs : s ∈ 𝒜 i) (hsp : s ∈ homogeneousCompl 𝒜 p) :
    degreeZeroFraction ha hs hsp ∈ maximalIdeal (DegreeZeroLocal 𝒜 p) ↔ a ∈ p := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro h
    by_contra hap
    exact h (isUnit_degreeZeroFraction_of_notMem 𝒜 ha hs hsp hap)
  · intro hap hu
    exact notMem_of_isUnit_degreeZeroToAtPrime 𝒜 ha hs hsp (hu.map _) hap

variable {f : A} (hf : f ∈ 𝒜 1) (hfp : f ∉ p)

include hf hfp in
/-- **The closed fibre ideal is the homogeneous core.** The ideal of `A_p` generated by the
maximal ideal of `A_{(p)}` is the extension of the homogeneous core `p*` of `p`. -/
theorem map_maximalIdeal_degreeZeroToAtPrime :
    (maximalIdeal (DegreeZeroLocal 𝒜 p)).map (degreeZeroToAtPrime 𝒜 p) =
      (coreIdeal 𝒜 p).map (algebraMap A (Localization.AtPrime p)) := by
  classical
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun x hx => ?_)
    (Ideal.map_le_iff_le_comap.mpr fun a ha => ?_)
  · obtain ⟨i, a, s, ha, hs, hsp, rfl⟩ := exists_eq_degreeZeroFraction x
    rw [degreeZeroFraction_mem_maximalIdeal_iff 𝒜 ha hs hsp] at hx
    rw [Ideal.mem_comap, degreeZeroToAtPrime_fraction, IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _
      (Ideal.mem_map_of_mem _ ((mem_coreIdeal_iff_of_mem ha).mpr hx))
  · rw [Ideal.mem_comap, ← DirectSum.sum_support_decompose 𝒜 a, map_sum]
    refine Ideal.sum_mem _ fun i _ => ?_
    have hfrac : algebraMap A (Localization.AtPrime p) (decompose 𝒜 a i : A) =
        degreeZeroToAtPrime 𝒜 p (fracPow hf hfp i (decompose 𝒜 a i)) *
          algebraMap A (Localization.AtPrime p) (f ^ i) := by
      rw [fracPow, degreeZeroToAtPrime_fraction, IsLocalization.mk'_spec]
    rw [hfrac]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    rw [fracPow, degreeZeroFraction_mem_maximalIdeal_iff]
    exact coreIdeal_le 𝒜 p ((coreIdeal_isHomogeneous 𝒜 p).mem_iff.mp ha i)

end Local


/-! ### Depth -/

section Depth

variable {p : Ideal A} [p.IsPrime]

/-- **The closed fibre has depth at least one off the homogeneous core.** If `p` is not
homogeneous, an element `a ∈ p` outside `p*` is a nonzerodivisor of the domain `A_p / p* A_p`
lying in the maximal ideal of `A_p`. -/
theorem one_le_depth_quotient_coreIdeal (hne : p ≠ coreIdeal 𝒜 p) :
    1 ≤ Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
      (Localization.AtPrime p ⧸ (coreIdeal 𝒜 p).map (algebraMap A (Localization.AtPrime p))) := by
  obtain ⟨a, hap, haP⟩ : ∃ a ∈ p, a ∉ coreIdeal 𝒜 p := by
    by_contra h
    push Not at h
    exact hne (le_antisymm h (coreIdeal_le 𝒜 p))
  have hdisj : Disjoint (p.primeCompl : Set A) (coreIdeal 𝒜 p) :=
    Set.disjoint_left.mpr fun x hx hxP => hx (coreIdeal_le 𝒜 p hxP)
  set J := (coreIdeal 𝒜 p).map (algebraMap A (Localization.AtPrime p))
  have hJ : J.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl _ _ inferInstance hdisj
  have hxJ : algebraMap A (Localization.AtPrime p) a ∉ J := by
    intro h
    have := IsLocalization.comap_map_of_isPrime_disjoint p.primeCompl (Localization.AtPrime p)
      (I := coreIdeal 𝒜 p) inferInstance hdisj
    exact haP (this ▸ (show a ∈ Ideal.under A J from h))
  have hreg : IsSMulRegular (Localization.AtPrime p ⧸ J)
      (algebraMap A (Localization.AtPrime p) a) := by
    intro y z hyz
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hyz' : Ideal.Quotient.mk J (algebraMap A (Localization.AtPrime p) a * y) =
        Ideal.Quotient.mk J (algebraMap A (Localization.AtPrime p) a * z) := hyz
    rw [Ideal.Quotient.eq, ← mul_sub] at hyz'
    rw [Ideal.Quotient.eq]
    exact (hJ.mem_or_mem hyz').resolve_left hxJ
  have hmem : algebraMap A (Localization.AtPrime p) a ∈ maximalIdeal (Localization.AtPrime p) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ p a).mpr hap
  simpa using Stacks.Depth.ModNonzerodivisor.length_le_depth_of_isWeaklyRegular
    (maximalIdeal (Localization.AtPrime p))
    (M := Localization.AtPrime p ⧸ J) (rs := [algebraMap A (Localization.AtPrime p) a])
    (by simpa using hmem) ((RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).mpr hreg)

variable [IsNoetherianRing A] {f : A} (hf : f ∈ 𝒜 1) (hfp : f ∉ p)

include hf hfp in
/-- **Depth along the flat map `A_{(p)} → A_p`.** The depth of `A_p` is at least that of the
degree-zero local ring, and one more when `p` is not homogeneous. This is Stacks 0337 for the flat
local map `A_{(p)} → A_p`, whose closed fibre is `A_p / p* A_p`. -/
theorem depth_degreeZeroLocal_add_le_depth_atPrime :
    Module.depth (DegreeZeroLocal 𝒜 p) (maximalIdeal (DegreeZeroLocal 𝒜 p))
        (DegreeZeroLocal 𝒜 p) + (if p = coreIdeal 𝒜 p then 0 else 1) ≤
      Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
        (Localization.AtPrime p) := by
  let := (degreeZeroToAtPrime 𝒜 p).toAlgebra
  have : IsLocalHom (algebraMap (DegreeZeroLocal 𝒜 p) (Localization.AtPrime p)) :=
    isLocalHom_degreeZeroToAtPrime 𝒜
  have : Module.Flat (DegreeZeroLocal 𝒜 p) (Localization.AtPrime p) :=
    flat_degreeZeroToAtPrime hf hfp
  rw [Module.depth_self_eq_depth_self_add_depth_quotient_map_maximalIdeal
    (DegreeZeroLocal 𝒜 p) (Localization.AtPrime p), RingHom.algebraMap_toAlgebra,
    map_maximalIdeal_degreeZeroToAtPrime 𝒜 hf hfp]
  gcongr
  split_ifs with h
  · exact zero_le
  · exact one_le_depth_quotient_coreIdeal 𝒜 h

/-- The localized module `A_p` of `A` over itself is the localization `A_p`, as `A_p`-modules. -/
def localizedModuleSelfEquiv (p : Ideal A) [p.IsPrime] :
    LocalizedModule p.primeCompl A ≃ₗ[Localization.AtPrime p] Localization.AtPrime p :=
  LinearEquiv.extendScalarsOfIsLocalization p.primeCompl (Localization.AtPrime p)
    (IsLocalizedModule.linearEquiv p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl A)
      (Algebra.linearMap A (Localization.AtPrime p)))

end Depth

/-- **The depth along the fibres of the punctured cone, ring case.** Let `A` be a graded Noetherian
ring, `f ∈ A₁` and `p` a prime of `A` with `f ∉ p`, with homogeneous core `p*`. Then
`depth(A_p) ≥ depth(A_{(p*)})`, with one more when `p` is not homogeneous; here `A_{(p*)}` is the
homogeneous localization of `A` at `p*`, the local ring of `Proj A` at the point `p*`. -/
theorem depth_atPrime_homogeneousCore_add_le_localizedDepth [IsNoetherianRing A]
    (p : PrimeSpectrum A) {f : A} (hf : f ∈ 𝒜 1) (hfp : f ∉ p.asIdeal) :
    Module.depth (HomogeneousLocalization.AtPrime 𝒜 (coreIdeal 𝒜 p.asIdeal))
        (maximalIdeal (HomogeneousLocalization.AtPrime 𝒜 (coreIdeal 𝒜 p.asIdeal)))
        (HomogeneousLocalization.AtPrime 𝒜 (coreIdeal 𝒜 p.asIdeal)) +
      (if p.asIdeal = coreIdeal 𝒜 p.asIdeal then 0 else 1) ≤
      localizedDepth A A p := by
  rw [← Module.depth_self_eq_of_ringEquiv (degreeZeroLocalEquiv 𝒜 p.asIdeal), localizedDepth,
    Module.depth_eq_depth_of_linearEquiv _ (localizedModuleSelfEquiv p.asIdeal)]
  exact depth_degreeZeroLocal_add_le_depth_atPrime 𝒜 hf hfp


/-! ### Primes over the irrelevant ideal -/

/-- **A prime containing the irrelevant ideal is maximal when `A₀` is Artinian.** The quotient
`A / q` is then a quotient of `A₀`, hence an Artinian domain, hence a field. -/
theorem isMaximal_of_irrelevant_le [IsArtinianRing (𝒜 0)] (q : Ideal A) [q.IsPrime]
    (hq : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ q) : q.IsMaximal := by
  classical
  let φ : 𝒜 0 →+* A ⧸ q := (Ideal.Quotient.mk q).comp (algebraMap (𝒜 0) A)
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨decompose 𝒜 a 0, ?_⟩
    show Ideal.Quotient.mk q (decompose 𝒜 a 0 : A) = Ideal.Quotient.mk q a
    rw [Ideal.Quotient.eq]
    refine hq ((HomogeneousIdeal.mem_irrelevant_iff 𝒜 _).mpr ?_)
    rw [map_sub, GradedRing.proj_apply, GradedRing.proj_apply, decompose_coe, of_eq_same,
      sub_self]
  have : IsArtinianRing (A ⧸ q) := hφ.isArtinianRing
  exact Ideal.Quotient.maximal_of_isField q (IsArtinianRing.isField_of_isDomain _)

/-! ### Dimension -/

section Dimension

variable (k : Type*) [Field k] [Algebra k A]

/-- **The localization of `A / p` at `q / p` is `A_q / p A_q`.** -/
theorem isLocalization_quotient_map_atPrime (p q : Ideal A) [q.IsPrime]
    [(q.map (Ideal.Quotient.mk p)).IsPrime] (hpq : p ≤ q) :
    IsLocalization (q.map (Ideal.Quotient.mk p)).primeCompl
      (Localization.AtPrime q ⧸ p.map (algebraMap A (Localization.AtPrime q))) := by
  have hsub : Algebra.algebraMapSubmonoid (A ⧸ p) q.primeCompl =
      (q.map (Ideal.Quotient.mk p)).primeCompl := by
    have hmem : ∀ r, Ideal.Quotient.mk p r ∈ q.map (Ideal.Quotient.mk p) ↔ r ∈ q := by
      intro r
      rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective (Ideal.Quotient.mk p)
        Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
        sup_eq_left.mpr hpq]
    ext y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    constructor
    · rintro ⟨s, hs, heq⟩ hqr
      refine hs ((hmem s).mp ?_)
      rwa [show Ideal.Quotient.mk p s = algebraMap A (A ⧸ p) s from rfl, heq]
    · exact fun hr => ⟨r, fun hrq => hr ((hmem r).mpr hrq), rfl⟩
  rw [← hsub]
  infer_instance

/-- **`relativeDimAt` is the transcendence degree of the residue field.** For `A` of finite type
over a field `k`, primes `p ⊆ q` with `q` maximal, the dimension of `A_q / p A_q` is
`trdeg_k κ(p)` (Stacks 00P0 for the domain `A / p` at its maximal ideal `q / p`). -/
theorem relativeDimAt_eq_trdeg [Algebra.FiniteType k A] (p q : PrimeSpectrum A)
    (hq : q.asIdeal.IsMaximal) (hpq : p.asIdeal ≤ q.asIdeal) :
    relativeDimAt A p q =
      (Cardinal.toENat (Algebra.trdeg k p.asIdeal.ResidueField) : WithBot ℕ∞) := by
  have hmax : (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk p.asIdeal)
      Ideal.Quotient.mk_surjective hq with
      h | h
    · exfalso
      have := congrArg (Ideal.comap (Ideal.Quotient.mk p.asIdeal)) h
      rw [Ideal.comap_map_of_surjective (Ideal.Quotient.mk p.asIdeal)
        Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
        sup_eq_left.mpr hpq, Ideal.comap_top] at this
      exact hq.ne_top this
    · exact h
  have := hmax.isPrime
  have := isLocalization_quotient_map_atPrime p.asIdeal q.asIdeal hpq
  exact (ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg k (A ⧸ p.asIdeal)
    p.asIdeal.ResidueField).2 (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal))
    (Localization.AtPrime q.asIdeal ⧸
      p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))

end Dimension


/-! ### The residue field of `A_{(p*)}` inside the residue field of `A_p` -/

section ResidueField

variable {k : Type*} [Field k] [Algebra k A] (hk : ∀ c : k, algebraMap k A c ∈ 𝒜 0)

/-- **The scalars of the degree-zero local rings.** When `k` lands in `A₀`, a scalar `c` is the
fraction `c / 1` of degree zero. -/
def degreeZeroAlgebraMap (x : Submonoid A) : k →+* HomogeneousLocalization 𝒜 x where
  toFun c := HomogeneousLocalization.mk
    ⟨0, ⟨algebraMap k A c, hk c⟩, ⟨1, SetLike.GradedOne.one_mem⟩, x.one_mem⟩
  map_one' := by
    rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk,
      HomogeneousLocalization.val_one]
    simp only [map_one]
    exact Localization.mk_one
  map_mul' a b := by
    rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul,
      HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk,
      HomogeneousLocalization.val_mk, Localization.mk_mul]
    simp only [map_mul]
    congr 1
    exact Subtype.ext (mul_one 1).symm
  map_zero' := by
    rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk,
      HomogeneousLocalization.val_zero]
    simp only [map_zero]
    exact Localization.mk_zero _
  map_add' a b := by
    rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_add,
      HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk,
      HomogeneousLocalization.val_mk]
    simp only [map_add]
    exact (Localization.add_mk_self _ _ _).symm

/-- The value of the scalar `c / 1` is the image of `c`. -/
theorem val_degreeZeroAlgebraMap (x : Submonoid A) (c : k) :
    (degreeZeroAlgebraMap 𝒜 hk x c).val = algebraMap A (Localization x) (algebraMap k A c) := by
  show (HomogeneousLocalization.mk _).val = _
  rw [HomogeneousLocalization.val_mk]
  exact Localization.mk_one_eq_algebraMap _

variable {p : Ideal A} [p.IsPrime]

/-- The local homomorphism `A_{(p*)} → A_p`. -/
def coreToAtPrime : HomogeneousLocalization.AtPrime 𝒜 (coreIdeal 𝒜 p) →+*
    Localization.AtPrime p :=
  (degreeZeroToAtPrime 𝒜 p).comp (degreeZeroLocalEquiv 𝒜 p).symm.toRingHom

/-- `A_{(p*)} → A_p` is a local homomorphism. -/
instance isLocalHom_coreToAtPrime : IsLocalHom (coreToAtPrime 𝒜 (p := p)) := by
  refine ⟨fun x hx => ?_⟩
  have h1 : IsUnit ((degreeZeroLocalEquiv 𝒜 p).symm x) :=
    (isLocalHom_degreeZeroToAtPrime 𝒜).map_nonunit _ hx
  simpa using h1.map (degreeZeroLocalEquiv 𝒜 p)

/-- `A_{(p*)} → A_p` is compatible with the scalars of `k`. -/
theorem coreToAtPrime_degreeZeroAlgebraMap (c : k) :
    coreToAtPrime 𝒜 (p := p) (degreeZeroAlgebraMap 𝒜 hk (coreIdeal 𝒜 p).primeCompl c) =
      algebraMap k (Localization.AtPrime p) c := by
  have he : (degreeZeroLocalEquiv 𝒜 p).symm
      (degreeZeroAlgebraMap 𝒜 hk (coreIdeal 𝒜 p).primeCompl c) =
      degreeZeroAlgebraMap 𝒜 hk (homogeneousCompl 𝒜 p) c := by
    rw [RingEquiv.symm_apply_eq, HomogeneousLocalization.ext_iff_val]
    show _ = (HomogeneousLocalization.map (GradedRingHom.id 𝒜)
      (homogeneousCompl_le_comap 𝒜 p) (HomogeneousLocalization.mk _)).val
    rw [HomogeneousLocalization.map_mk]
    rfl
  rw [coreToAtPrime, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, he]
  show degreeZeroToAtPrime 𝒜 p (degreeZeroFraction (hk c) SetLike.GradedOne.one_mem
    (homogeneousCompl 𝒜 p).one_mem) = _
  rw [degreeZeroToAtPrime_fraction, IsScalarTower.algebraMap_apply k A (Localization.AtPrime p)]
  exact IsLocalization.mk'_one _ _

/-- The algebra structure over `k` on a degree-zero local ring, through `degreeZeroAlgebraMap`. -/
abbrev degreeZeroAlgebra (x : Submonoid A) : Algebra k (HomogeneousLocalization 𝒜 x) :=
  (degreeZeroAlgebraMap 𝒜 hk x).toAlgebra

/-- The field map `κ(p*) → κ(p)` induced by `A_{(p*)} → A_p`, over `k`. -/
def residueFieldAlgHom :
    letI := degreeZeroAlgebra 𝒜 hk (coreIdeal 𝒜 p).primeCompl
    ResidueField (HomogeneousLocalization.AtPrime 𝒜 (coreIdeal 𝒜 p)) →ₐ[k] p.ResidueField :=
  letI := degreeZeroAlgebra 𝒜 hk (coreIdeal 𝒜 p).primeCompl
  { ResidueField.map (coreToAtPrime 𝒜 (p := p)) with
    commutes' := fun c => by
      change ResidueField.map (coreToAtPrime 𝒜 (p := p)) (residue _
        (degreeZeroAlgebraMap 𝒜 hk (coreIdeal 𝒜 p).primeCompl c)) = residue _ (algebraMap k _ c)
      rw [ResidueField.map_residue, coreToAtPrime_degreeZeroAlgebraMap] }

/-- **`trdeg_k κ(p*) ≤ trdeg_k κ(p)`.** -/
theorem trdeg_residueField_core_le :
    letI := degreeZeroAlgebra 𝒜 hk (coreIdeal 𝒜 p).primeCompl
    Algebra.trdeg k (ResidueField (HomogeneousLocalization.AtPrime 𝒜 (coreIdeal 𝒜 p))) ≤
      Algebra.trdeg k p.ResidueField :=
  let := degreeZeroAlgebra 𝒜 hk (coreIdeal 𝒜 p).primeCompl
  trdeg_le_of_injective (residueFieldAlgHom 𝒜 hk) (residueFieldAlgHom 𝒜 hk).toRingHom.injective

end ResidueField


/-! ### The extra transcendental at a homogeneous prime -/

section Transcendental

variable {k : Type*} [Field k] [Algebra k A] (hk : ∀ c : k, algebraMap k A c ∈ 𝒜 0)
  {p : Ideal A} [p.IsPrime] {f : A} (hf : f ∈ 𝒜 1) (hfp : f ∉ p)

/-- `evalAtPrime` is the evaluation `eval₂` along `A_{(p)} → A_p` at the image of `f`. -/
theorem evalAtPrime_eq_eval₂ (t : (DegreeZeroLocal 𝒜 p)[X]) :
    evalAtPrime 𝒜 p f t = t.eval₂ (degreeZeroToAtPrime 𝒜 p) (algebraMap A _ f) := by
  rw [evalAtPrime, RingHom.comp_apply, evalFractions, Polynomial.coe_eval₂RingHom,
    Polynomial.hom_eval₂, fractionsToAtPrime_algebraMap]
  rfl

include hf hfp in
/-- **At a homogeneous prime, a polynomial whose value at `f` is in the maximal ideal has all its
coefficients in the maximal ideal.** Over a common homogeneous denominator the value is
`∑ₙ h n fⁿ / d ∈ p A_p`, so `∑ₙ h n fⁿ ∈ p`; the summands have distinct degrees and `p` is
homogeneous, so each `h n fⁿ ∈ p`, whence `h n ∈ p`. -/
theorem coeff_mem_maximalIdeal_of_evalAtPrime_mem (hp : p = coreIdeal 𝒜 p)
    (t : (DegreeZeroLocal 𝒜 p)[X]) (ht : evalAtPrime 𝒜 p f t ∈ maximalIdeal _) (n : ℕ) :
    t.coeff n ∈ maximalIdeal (DegreeZeroLocal 𝒜 p) := by
  classical
  by_cases hn : n ∈ t.support
  swap
  · rw [Polynomial.notMem_support_iff.mp hn]
    exact zero_mem _
  obtain ⟨I, d, h, hd, hh⟩ := exists_common_denominator_degreeZeroLocal t.support t.coeff
  have hmul := algebraMap_mul_evalAtPrime (f := f) t d h fun n hn => (hh n hn).2
  have hsum : (∑ k ∈ t.support, h k * f ^ k) ∈ p := by
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p, ← hmul]
    exact Ideal.mul_mem_left _ _ ht
  have hhom : p.IsHomogeneous 𝒜 :=
    (congrArg (Ideal.IsHomogeneous 𝒜) hp).mpr (coreIdeal_isHomogeneous 𝒜 p)
  have hmem : ∀ k ∈ t.support, h k * f ^ k ∈ 𝒜 (I + k) := fun k hk =>
    SetLike.mul_mem_graded (hh k hk).1 (pow_mem_graded_of_mem_one hf k)
  have hcomp : h n * f ^ n ∈ p := by
    have h1 := hhom.mem_iff.mp hsum (I + n)
    rwa [← GradedRing.proj_apply, proj_sum_eq_of_mem hmem hn] at h1
  have hhn : h n ∈ p :=
    (Ideal.IsPrime.mem_or_mem inferInstance hcomp).resolve_right
      (pow_mem_homogeneousCompl hf hfp n).1
  have hc : t.coeff n = degreeZeroFraction (hh n hn).1 hd d.2 :=
    (HomogeneousLocalization.ext_iff_val _ _).mpr
      ((hh n hn).2.trans (val_degreeZeroFraction _ _ _).symm)
  rw [hc, degreeZeroFraction_mem_maximalIdeal_iff]
  exact hhn

include hf hfp in
/-- **At a homogeneous prime the residue of `f` is transcendental over `κ(p*)`.** -/
theorem transcendental_residue_algebraMap (hp : p = coreIdeal 𝒜 p) :
    letI := (ResidueField.map (coreToAtPrime 𝒜 (p := p))).toAlgebra
    Transcendental (ResidueField (HomogeneousLocalization.AtPrime 𝒜 (coreIdeal 𝒜 p)))
      (residue (Localization.AtPrime p) (algebraMap A _ f)) := by
  let := (ResidueField.map (coreToAtPrime 𝒜 (p := p))).toAlgebra
  rintro ⟨g, hg0, hg⟩
  apply hg0
  obtain ⟨G, rfl⟩ := Polynomial.map_surjective _ residue_surjective g
  set G' := G.map (degreeZeroLocalEquiv 𝒜 p).symm.toRingHom with hG'
  have hcomp : (algebraMap (ResidueField (HomogeneousLocalization.AtPrime 𝒜 (coreIdeal 𝒜 p)))
      p.ResidueField).comp (residue _) = (residue (Localization.AtPrime p)).comp
        ((degreeZeroToAtPrime 𝒜 p).comp (degreeZeroLocalEquiv 𝒜 p).symm.toRingHom) :=
    RingHom.ext fun x => ResidueField.map_residue _ x
  have heval : Polynomial.aeval (residue _ (algebraMap A _ f)) (G.map (residue _)) =
      residue _ (evalAtPrime 𝒜 p f G') := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, evalAtPrime_eq_eval₂, hG',
      Polynomial.eval₂_map, Polynomial.hom_eval₂, hcomp]
  rw [heval, residue_eq_zero_iff] at hg
  refine Polynomial.ext fun n => ?_
  rw [Polynomial.coeff_map, Polynomial.coeff_zero, residue_eq_zero_iff]
  have h1 := coeff_mem_maximalIdeal_of_evalAtPrime_mem 𝒜 hf hfp hp G' hg n
  rw [hG', Polynomial.coeff_map] at h1
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h1 ⊢
  exact fun hu => h1 (hu.map _)

include hf hfp in
/-- **`trdeg_k κ(p*) + 1 ≤ trdeg_k κ(p)` when `p` is homogeneous**, the extra transcendental being
the residue of `f`. -/
theorem trdeg_residueField_core_add_one_le (hp : p = coreIdeal 𝒜 p) :
    letI := degreeZeroAlgebra 𝒜 hk (coreIdeal 𝒜 p).primeCompl
    Algebra.trdeg k (ResidueField (HomogeneousLocalization.AtPrime 𝒜 (coreIdeal 𝒜 p))) + 1 ≤
      Algebra.trdeg k p.ResidueField := by
  let := degreeZeroAlgebra 𝒜 hk (coreIdeal 𝒜 p).primeCompl
  let : Algebra (ResidueField (HomogeneousLocalization.AtPrime 𝒜 (coreIdeal 𝒜 p)))
      p.ResidueField := (ResidueField.map (coreToAtPrime 𝒜 (p := p))).toAlgebra
  have : IsScalarTower k (ResidueField (HomogeneousLocalization.AtPrime 𝒜 (coreIdeal 𝒜 p)))
      p.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun c => ((residueFieldAlgHom 𝒜 hk).commutes c).symm
  have : FaithfulSMul k (ResidueField (HomogeneousLocalization.AtPrime 𝒜 (coreIdeal 𝒜 p))) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap k _).injective
  have : FaithfulSMul (ResidueField (HomogeneousLocalization.AtPrime 𝒜 (coreIdeal 𝒜 p)))
      p.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (algebraMap (ResidueField (HomogeneousLocalization.AtPrime 𝒜 (coreIdeal 𝒜 p)))
        p.ResidueField).injective
  have : Algebra.Transcendental
      (ResidueField (HomogeneousLocalization.AtPrime 𝒜 (coreIdeal 𝒜 p))) p.ResidueField :=
    ⟨⟨_, transcendental_residue_algebraMap 𝒜 hf hfp hp⟩⟩
  calc _ ≤ Algebra.trdeg k (ResidueField (HomogeneousLocalization.AtPrime 𝒜 (coreIdeal 𝒜 p))) +
        Algebra.trdeg (ResidueField (HomogeneousLocalization.AtPrime 𝒜 (coreIdeal 𝒜 p)))
          p.ResidueField :=
          add_le_add_right (Cardinal.one_le_iff_ne_zero.mpr (trdeg_ne_zero_iff.mpr inferInstance)) _
    _ ≤ _ := trdeg_add_le

end Transcendental

/-- **The dimension along the fibres of the punctured cone.** Let `A` be a graded ring of finite
type over a field `k` with `k → A` landing in `A₀`, `f ∈ A₁`, `p` a prime with `f ∉ p` and
homogeneous core `p*`, and `q ⊇ p` a maximal ideal. Then
`dim((A/p)_q) ≥ trdeg_k κ(p*)`, with one more when `p` is homogeneous; here `κ(p*)` is the residue
field of `A_{(p*)}`, that is of `Proj A` at `p*`, over `k`. -/
theorem trdeg_residueField_core_add_le_relativeDimAt {k : Type*} [Field k] [Algebra k A]
    [Algebra.FiniteType k A] (hk : ∀ c : k, algebraMap k A c ∈ 𝒜 0) (p q : PrimeSpectrum A)
    (hq : q.asIdeal.IsMaximal) (hpq : p.asIdeal ≤ q.asIdeal) {f : A} (hf : f ∈ 𝒜 1)
    (hfp : f ∉ p.asIdeal) :
    letI := degreeZeroAlgebra 𝒜 hk (coreIdeal 𝒜 p.asIdeal).primeCompl
    ((Cardinal.toENat (Algebra.trdeg k
        (ResidueField (HomogeneousLocalization.AtPrime 𝒜 (coreIdeal 𝒜 p.asIdeal)))) :
        WithBot ℕ∞) + (if p.asIdeal = coreIdeal 𝒜 p.asIdeal then 1 else 0)) ≤
      relativeDimAt A p q := by
  let := degreeZeroAlgebra 𝒜 hk (coreIdeal 𝒜 p.asIdeal).primeCompl
  rw [relativeDimAt_eq_trdeg k p q hq hpq]
  split_ifs with hp
  · have h := trdeg_residueField_core_add_one_le 𝒜 hk hf hfp hp
    have h2 := OrderHomClass.mono Cardinal.toENat h
    rw [map_add, map_one] at h2
    exact_mod_cast h2
  · rw [add_zero]
    exact_mod_cast OrderHomClass.mono Cardinal.toENat (trdeg_residueField_core_le 𝒜 hk)


/-- **The fibre dichotomy of the punctured cone, in the arithmetic of Faltings' annihilator
theorem.** Let `A` be a graded Noetherian ring of finite type over a field `k` with `k → A` landing
in `A₀`, let `f ∈ A₁`, let `p` be a prime of `A` with `f ∉ p` and homogeneous core `p*`, and let
`q ⊇ p` be a maximal ideal. Then

`depth(A_p) + dim((A/p)_q) ≥ depth(A_{(p*)}) + trdeg_k κ(p*) + 1`,

the extra unit falling on the depth when `p ≠ p*` and on the dimension when `p = p*`. Here
`A_{(p*)}` and `κ(p*)` are the local ring and the residue field of `Proj A` at `p*`, and
`trdeg_k κ(p*)` is the dimension of the closure of that point. -/
theorem depth_add_trdeg_add_one_le_depthAddRelativeDim [IsNoetherianRing A] {k : Type*}
    [Field k] [Algebra k A] [Algebra.FiniteType k A] (hk : ∀ c : k, algebraMap k A c ∈ 𝒜 0)
    (p q : PrimeSpectrum A) (hq : q.asIdeal.IsMaximal) (hpq : p.asIdeal ≤ q.asIdeal)
    {f : A} (hf : f ∈ 𝒜 1) (hfp : f ∉ p.asIdeal) :
    letI := degreeZeroAlgebra 𝒜 hk (coreIdeal 𝒜 p.asIdeal).primeCompl
    enatToEInt (Module.depth (HomogeneousLocalization.AtPrime 𝒜 (coreIdeal 𝒜 p.asIdeal))
        (maximalIdeal (HomogeneousLocalization.AtPrime 𝒜 (coreIdeal 𝒜 p.asIdeal)))
        (HomogeneousLocalization.AtPrime 𝒜 (coreIdeal 𝒜 p.asIdeal))) +
      krullDimToEInt ((Cardinal.toENat (Algebra.trdeg k
        (ResidueField (HomogeneousLocalization.AtPrime 𝒜 (coreIdeal 𝒜 p.asIdeal)))) :
          WithBot ℕ∞)) + 1 ≤
      depthAddRelativeDim A A p q := by
  let := degreeZeroAlgebra 𝒜 hk (coreIdeal 𝒜 p.asIdeal).primeCompl
  have hdep := depth_atPrime_homogeneousCore_add_le_localizedDepth 𝒜 p hf hfp
  have hdim := trdeg_residueField_core_add_le_relativeDimAt 𝒜 hk p q hq hpq hf hfp
  rw [depthAddRelativeDim]
  split_ifs at hdep hdim with hp
  · rw [add_zero] at hdep
    rw [add_assoc, ← krullDimToEInt_add_one]
    exact add_le_add (enatToEInt_mono hdep) (krullDimToEInt_mono hdim)
  · rw [add_zero] at hdim
    rw [add_right_comm, ← enatToEInt_add_one]
    exact add_le_add (enatToEInt_mono hdep) (krullDimToEInt_mono hdim)

end Stacks.Algebraization.SectionRingCone

end
