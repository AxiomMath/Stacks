module

public import StacksFrontier.RingTheory.GradedAlgebra.Truncation
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CoordinateBlowup
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesGrading
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesComparison
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Comparison
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjAndSpecTruncation
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupDifferentialFormsComparison
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CoordinateBlowupSmooth

/-!
# The standard coordinate blowup is the cone `Proj(⨁_d A_{≥ d})`

Fix a ring `R` and `m, n ≥ 0`, and grade `A = R[x₁, …, x_m, y₁, …, y_n]` by `deg xᵢ = 0`,
`deg yⱼ = 1`. The ideal of the centre `Z = 𝐀^m_S ⊆ X = 𝐀^{m+n}_S` is `A₊`, its powers are
`(A₊)ᵈ = A_{≥ d}`, and hence the blowing up `L` of `X` along `Z` is the Proj of
`⨁_{d ≥ 0} A_{≥ d}`, the cone over `P = Proj(A)` with its projection `π : L ⟶ P` and zero section
`0 : P ⟶ L`. We construct this identification for `AlgebraicGeometry.blowUp` as an isomorphism
over `X`.

## Main definitions

* `Stacks.DeRham.CoordinateCone.yGrading`: the grading `deg xᵢ = 0`, `deg yⱼ = 1` of `A`.
* `Stacks.DeRham.CoordinateCone.truncReesEquiv`: the ring isomorphism
  `⨁_d A_{≥ d} ≅ Γ(X, 𝒪_X)[I t]` with the Rees algebra of the centre on global sections.
* `Stacks.DeRham.CoordinateCone.coneBlowupIso`: **the isomorphism `Proj(⨁_d A_{≥ d}) ≅ L`**.

## Main results

* `Stacks.DeRham.CoordinateCone.mem_coordinateRingIdeal_pow_iff`: `(A₊)ᵈ = A_{≥ d}`.
* `Stacks.DeRham.CoordinateCone.coneBlowupIso_hom_comp`: the isomorphism is one over `X`: it
  carries the structure morphism of the cone to the blowing-up morphism `b`.

## References

* [Stacks Project, Tag 0FUB](https://stacks.math.columbia.edu/tag/0FUB)
* [Stacks Project, Tag 0EKF](https://stacks.math.columbia.edu/tag/0EKF)
-/

@[expose] public noncomputable section

open MvPolynomial AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Truncation

/-- **The cone `Proj(⨁_d A_{≥ d})` of a graded ring**, the scheme of
`Stacks.AlgebraicGeometry.ProjAndSpecTruncation.truncationConeData`. -/
abbrev truncationProj {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] : Scheme.{u} :=
  AlgebraicGeometry.Proj (grading 𝒜)

end Stacks.Truncation

namespace Stacks.DeRham.CoordinateCone

variable (R : Type u) [CommRing R] (m n : ℕ)

/-- The weights of the standard coordinate situation: the first `m` coordinates `xᵢ` have weight
`0` and the last `n` coordinates `yⱼ` have weight `1`. -/
abbrev yWeight : Fin m ⊕ Fin n → ℕ := Sum.elim 0 1

/-- The grading of `A = R[x₁, …, x_m, y₁, …, y_n]` by `deg xᵢ = 0`, `deg yⱼ = 1`. -/
abbrev yGrading : ℕ → Submodule R (MvPolynomial (Fin m ⊕ Fin n) R) :=
  weightedHomogeneousSubmodule R (yWeight m n)

/-- The grading `deg xᵢ = 0`, `deg yⱼ = 1` makes `A` a graded `R`-algebra. -/
instance : _root_.GradedAlgebra (yGrading R m n) := weightedGradedAlgebra R (yWeight m n)

/-- **The cone `L = Proj(⨁_d A_{≥ d})`** of the standard coordinate situation. -/
abbrev coneTotal : Scheme.{u} := Stacks.Truncation.truncationProj (yGrading R m n)

/-- Each coordinate `yⱼ` is homogeneous of degree `1`. -/
theorem X_inr_mem_yGrading (j : Fin n) :
    (X (Sum.inr j) : MvPolynomial (Fin m ⊕ Fin n) R) ∈ yGrading R m n 1 :=
  isWeightedHomogeneous_X R (yWeight m n) (Sum.inr j)

/-- Every polynomial lies in `A_{≥ 0}`. -/
theorem mem_truncation_zero (a : MvPolynomial (Fin m ⊕ Fin n) R) :
    a ∈ Stacks.Truncation.truncation (yGrading R m n) 0 :=
  (Stacks.Truncation.mem_truncation_iff (yGrading R m n)).mpr fun d hd => absurd hd (by omega)

/-- The ideal `A₊ = (y₁, …, y_n)` of the centre lies in `A_{≥ 1}`. -/
theorem coordinateRingIdeal_le_truncation_one {a : MvPolynomial (Fin m ⊕ Fin n) R}
    (ha : a ∈ Stacks.MoreMorphisms.coordinateRingIdeal R m n) :
    a ∈ Stacks.Truncation.truncation (yGrading R m n) 1 := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact Stacks.Truncation.mem_truncation_of_mem _ le_rfl (X_inr_mem_yGrading R m n j)
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx =>
    simpa using Stacks.Truncation.mul_mem_truncation (yGrading R m n)
      (mem_truncation_zero R m n c) hx

/-- `(A₊)ᵈ ⊆ A_{≥ d}`. -/
theorem coordinateRingIdeal_pow_le_truncation (d : ℕ) {a : MvPolynomial (Fin m ⊕ Fin n) R}
    (ha : a ∈ Stacks.MoreMorphisms.coordinateRingIdeal R m n ^ d) :
    a ∈ Stacks.Truncation.truncation (yGrading R m n) d := by
  induction d generalizing a with
  | zero => exact mem_truncation_zero R m n a
  | succ d ih =>
    rw [pow_succ] at ha
    exact Submodule.mul_induction_on ha
      (fun x hx y hy => Stacks.Truncation.mul_mem_truncation (yGrading R m n) (ih hx)
        (coordinateRingIdeal_le_truncation_one R m n hy))
      (fun x y hx hy => add_mem hx hy)

/-- A monomial lies in the power of `A₊` given by its weight. -/
theorem monomial_mem_coordinateRingIdeal_pow (s : Fin m ⊕ Fin n →₀ ℕ) (c : R) :
    monomial s c ∈
      Stacks.MoreMorphisms.coordinateRingIdeal R m n ^ (Finsupp.weight (yWeight m n) s) := by
  classical
  have hX : ∀ v : Fin m ⊕ Fin n, (X v : MvPolynomial (Fin m ⊕ Fin n) R) ^ s v ∈
      Stacks.MoreMorphisms.coordinateRingIdeal R m n ^ (s v * yWeight m n v) := by
    rintro (i | j)
    · simp
    · simpa using Ideal.pow_mem_pow
        (Stacks.MoreMorphisms.X_inr_mem_coordinateRingIdeal R m n j) (s (Sum.inr j))
  have hprod : (∏ v ∈ s.support, (X v : MvPolynomial (Fin m ⊕ Fin n) R) ^ s v) ∈
      Stacks.MoreMorphisms.coordinateRingIdeal R m n ^ (Finsupp.weight (yWeight m n) s) := by
    rw [Finsupp.weight_apply, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun v _ => by simpa [smul_eq_mul, mul_comm] using hX v
  rw [monomial_eq, Finsupp.prod]
  exact Ideal.mul_mem_left _ _ hprod

/-- `A_{≥ d} ⊆ (A₊)ᵈ`. -/
theorem truncation_le_coordinateRingIdeal_pow (d : ℕ) {a : MvPolynomial (Fin m ⊕ Fin n) R}
    (ha : a ∈ Stacks.Truncation.truncation (yGrading R m n) d) :
    a ∈ Stacks.MoreMorphisms.coordinateRingIdeal R m n ^ d := by
  induction ha using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨e, hde, hx⟩ := hx
    rw [mem_weightedHomogeneousSubmodule] at hx
    rw [as_sum x]
    refine Ideal.sum_mem _ fun s hs => ?_
    have hw : Finsupp.weight (yWeight m n) s = e := hx (mem_support_iff.mp hs)
    exact Ideal.pow_le_pow_right (hw ▸ hde)
      (monomial_mem_coordinateRingIdeal_pow R m n s (x.coeff s))
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

/-- **`(A₊)ᵈ = A_{≥ d}`**: the `d`-th power of the ideal of the centre is the `d`-th truncation of
`A` for the grading `deg xᵢ = 0`, `deg yⱼ = 1`. -/
theorem mem_coordinateRingIdeal_pow_iff (d : ℕ) (a : MvPolynomial (Fin m ⊕ Fin n) R) :
    a ∈ Stacks.MoreMorphisms.coordinateRingIdeal R m n ^ d ↔
      a ∈ Stacks.Truncation.truncation (yGrading R m n) d :=
  ⟨coordinateRingIdeal_pow_le_truncation R m n d, truncation_le_coordinateRingIdeal_pow R m n d⟩

/-! ### The Rees algebra of the centre on global sections is the truncation ring -/

section ReesTruncation

open Stacks.MoreMorphisms Stacks.Truncation Polynomial

/-- The ideal of the centre on global sections of `X`. -/
abbrev topIdeal : Ideal Γ(Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R)), ⊤) :=
  (coordinateIdeal R m n).ideal (topAffineOpen R m n)

/-- `x ∈ I(X)ᵈ` exactly when the corresponding polynomial lies in `A_{≥ d}`. -/
theorem mem_topIdeal_pow_iff (d : ℕ) (x : Γ(Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R)), ⊤)) :
    x ∈ topIdeal R m n ^ d ↔ (gammaEquiv R m n).symm x ∈ truncation (yGrading R m n) d := by
  rw [topIdeal, coordinateIdeal_ideal_top, ← Ideal.map_pow, Ideal.map_comap_of_equiv,
    Ideal.mem_comap, ← mem_coordinateRingIdeal_pow_iff]

/-- The `d`-th summand of the truncation ring, sent to the monomial of degree `d` of the
polynomial ring over the global functions. -/
def truncToPolyComponent (d : ℕ) :
    truncation (yGrading R m n) d →+
      Polynomial Γ(Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R)), ⊤) :=
  ((monomial d).toAddMonoidHom.comp (gammaEquiv R m n).toAddMonoidHom).comp
    (truncation (yGrading R m n) d).subtype

/-- The ring map `⨁_d A_{≥ d} ⟶ Γ(X, 𝒪_X)[t]`, `a⁽ᵈ⁾ ↦ a tᵈ`. -/
def truncToPoly :
    TruncationRing (yGrading R m n) →+*
      Polynomial Γ(Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R)), ⊤) :=
  DirectSum.toSemiring (truncToPolyComponent R m n)
    (by
      change Polynomial.monomial 0 (gammaEquiv R m n 1) = 1
      rw [map_one, Polynomial.monomial_zero_one])
    (fun {d e} a b => by
      change Polynomial.monomial (d + e)
          (gammaEquiv R m n ((a : MvPolynomial (Fin m ⊕ Fin n) R) * b)) =
        Polynomial.monomial d (gammaEquiv R m n a) * Polynomial.monomial e (gammaEquiv R m n b)
      rw [Polynomial.monomial_mul_monomial, map_mul])

/-- `truncToPoly` sends `a ∈ A_{≥ d}` in degree `d` to the monomial `a tᵈ`. -/
theorem truncToPoly_of (d : ℕ) (a : truncation (yGrading R m n) d) :
    truncToPoly R m n (DirectSum.of _ d a) = monomial d (gammaEquiv R m n a) :=
  DirectSum.toSemiring_of _ _ _ _ _

/-- The `i`-th coefficient of `truncToPoly x` is the degree `i` component of `x`. -/
theorem coeff_truncToPoly (x : TruncationRing (yGrading R m n)) (i : ℕ) :
    (truncToPoly R m n x).coeff i = gammaEquiv R m n (x i) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of d a =>
    rw [truncToPoly_of, Polynomial.coeff_monomial]
    obtain rfl | h := eq_or_ne d i
    · simp
    · rw [ite_eq_right h, DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
      simp
  | add x y hx hy => simp [hx, hy]

/-- `truncToPoly` is injective. -/
theorem truncToPoly_injective : Function.Injective (truncToPoly R m n) := fun x y hxy =>
  DFinsupp.ext fun i => Subtype.ext <| (gammaEquiv R m n).injective <| by
    simpa only [coeff_truncToPoly] using congrArg (Polynomial.coeff · i) hxy

/-- `truncToPoly` takes values in the Rees algebra `Γ(X, 𝒪_X)[I t]` of the centre. -/
theorem truncToPoly_mem_reesAlgebra (x : TruncationRing (yGrading R m n)) :
    truncToPoly R m n x ∈ reesAlgebra (topIdeal R m n) := by
  rw [mem_reesAlgebra_iff]
  intro i
  rw [coeff_truncToPoly, mem_topIdeal_pow_iff, RingEquiv.symm_apply_apply]
  exact (x i).2

/-- **The truncation ring is the Rees algebra of the centre, on global sections**: the ring map
`a⁽ᵈ⁾ ↦ a tᵈ` is an isomorphism `⨁_d A_{≥ d} ≅ Γ(X, 𝒪_X)[I t]`. -/
def truncReesEquiv : TruncationRing (yGrading R m n) ≃+* reesAlgebra (topIdeal R m n) :=
  RingEquiv.ofBijective
    ((truncToPoly R m n).codRestrict (reesAlgebra (topIdeal R m n)).toSubring
      (truncToPoly_mem_reesAlgebra R m n))
    ⟨fun x y hxy => truncToPoly_injective R m n (congrArg Subtype.val hxy), by
      classical
      rintro ⟨p, hp⟩
      rw [mem_reesAlgebra_iff] at hp
      refine ⟨∑ i ∈ p.support, DirectSum.of _ i
        ⟨(gammaEquiv R m n).symm (p.coeff i), (mem_topIdeal_pow_iff R m n i _).mp (hp i)⟩, ?_⟩
      refine Subtype.ext ?_
      change truncToPoly R m n _ = p
      rw [map_sum]
      simp only [truncToPoly_of, RingEquiv.apply_symm_apply]
      exact (as_sum_support p).symm⟩

/-- The underlying polynomial of `truncReesEquiv x` is `truncToPoly x`. -/
theorem coe_truncReesEquiv (x : TruncationRing (yGrading R m n)) :
    (truncReesEquiv R m n x : Polynomial Γ(Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R)), ⊤)) =
      truncToPoly R m n x :=
  rfl

/-- A graded ring homomorphism with a graded right inverse carries the irrelevant ideal of its
source onto that of its target, so it induces a morphism of projective spectra. -/
theorem irrelevant_le_map_of_rightInverse {A B : Type*} [CommRing A] [CommRing B]
    {σ τ : Type*} [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (h : ∀ x, f (g x) = x) :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi x hx
  rw [← h x]
  exact Ideal.mem_map_of_mem f (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hi (g.map_mem hx))

/-- The isomorphism `⨁_d A_{≥ d} ≅ Γ(X, 𝒪_X)[I t]` preserves degrees. -/
theorem truncReesEquiv_mem (d : ℕ) {x : TruncationRing (yGrading R m n)}
    (hx : x ∈ grading (yGrading R m n) d) :
    truncReesEquiv R m n x ∈ Stacks.Blowup.reesGrading (topIdeal R m n) d := by
  obtain ⟨a, rfl⟩ := hx
  intro i hi
  rw [coe_truncReesEquiv, truncToPoly_of, Polynomial.coeff_monomial, ite_eq_right (Ne.symm hi)]

/-- The inverse of `truncReesEquiv` preserves degrees. -/
theorem truncReesEquiv_symm_mem (d : ℕ) {f : reesAlgebra (topIdeal R m n)}
    (hf : f ∈ Stacks.Blowup.reesGrading (topIdeal R m n) d) :
    (truncReesEquiv R m n).symm f ∈ grading (yGrading R m n) d := by
  refine ⟨⟨(gammaEquiv R m n).symm ((f : Polynomial _).coeff d),
    (mem_topIdeal_pow_iff R m n d _).mp ((mem_reesAlgebra_iff _ _).mp f.2 d)⟩, ?_⟩
  rw [RingEquiv.eq_symm_apply]
  refine Subtype.ext ?_
  rw [coe_truncReesEquiv, truncToPoly_of, RingEquiv.apply_symm_apply]
  exact (Stacks.Blowup.coe_eq_monomial (topIdeal R m n) hf).symm

/-- `truncReesEquiv`, as a homomorphism of graded rings. -/
def truncReesGradedHom :
    grading (yGrading R m n) →+*ᵍ Stacks.Blowup.reesGrading (topIdeal R m n) where
  toRingHom := (truncReesEquiv R m n).toRingHom
  map_mem hx := truncReesEquiv_mem R m n _ hx

/-- The inverse of `truncReesEquiv`, as a homomorphism of graded rings. -/
def truncReesGradedHomInv :
    Stacks.Blowup.reesGrading (topIdeal R m n) →+*ᵍ grading (yGrading R m n) where
  toRingHom := (truncReesEquiv R m n).symm.toRingHom
  map_mem hx := truncReesEquiv_symm_mem R m n _ hx

/-- The graded ring of homogeneous sections of the Rees algebra of the centre over `X` is the
truncation ring: the comparison of the two, as a homomorphism of graded rings. -/
def sectionTruncGradedHom :
    (reesSituation (coordinateIdeal R m n)).sectionRingGrading (topAffineOpen R m n).1 →+*ᵍ
      grading (yGrading R m n) :=
  (truncReesGradedHomInv R m n).comp (reesSectionGradedHom _ (topAffineOpen R m n))

/-- The homomorphism of graded rings from the truncation ring to the graded ring of homogeneous
sections of the Rees algebra of the centre over `X`, inverse to `sectionTruncGradedHom`. -/
def truncSectionGradedHom :
    grading (yGrading R m n) →+*ᵍ
      (reesSituation (coordinateIdeal R m n)).sectionRingGrading (topAffineOpen R m n).1 :=
  (reesSectionGradedHomInv _ (topAffineOpen R m n)).comp (truncReesGradedHom R m n)

/-- `sectionTruncGradedHom` is a left inverse of `truncSectionGradedHom`. -/
theorem sectionTruncGradedHom_truncSectionGradedHom (x : TruncationRing (yGrading R m n)) :
    sectionTruncGradedHom R m n (truncSectionGradedHom R m n x) = x := by
  simp only [sectionTruncGradedHom, truncSectionGradedHom, GradedRingHom.comp_apply]
  change (truncReesEquiv R m n).symm ((reesSectionRingEquiv _ (topAffineOpen R m n))
    ((reesSectionRingEquiv _ (topAffineOpen R m n)).symm (truncReesEquiv R m n x))) = x
  simp

/-- `truncSectionGradedHom` is a left inverse of `sectionTruncGradedHom`. -/
theorem truncSectionGradedHom_sectionTruncGradedHom
    (x : (reesSituation (coordinateIdeal R m n)).sectionRing (topAffineOpen R m n).1) :
    truncSectionGradedHom R m n (sectionTruncGradedHom R m n x) = x := by
  simp only [sectionTruncGradedHom, truncSectionGradedHom, GradedRingHom.comp_apply]
  change (reesSectionRingEquiv _ (topAffineOpen R m n)).symm (truncReesEquiv R m n
    ((truncReesEquiv R m n).symm ((reesSectionRingEquiv _ (topAffineOpen R m n)) x))) = x
  simp

end ReesTruncation

/-! ### The blowup is the cone over the projective spectrum -/

section Cone

open Stacks.MoreMorphisms Stacks.Truncation

/-- The irrelevant ideal of the truncation ring lies in the image of that of the Rees section
ring under `sectionTruncGradedHom`. -/
theorem irrelevant_le_map_sectionTruncGradedHom :
    HomogeneousIdeal.irrelevant (grading (yGrading R m n)) ≤
      (HomogeneousIdeal.irrelevant _).map (sectionTruncGradedHom R m n) :=
  irrelevant_le_map_of_rightInverse _ _ (sectionTruncGradedHom_truncSectionGradedHom R m n)

/-- The irrelevant ideal of the Rees section ring lies in the image of that of the truncation
ring under `truncSectionGradedHom`. -/
theorem irrelevant_le_map_truncSectionGradedHom :
    HomogeneousIdeal.irrelevant
        ((reesSituation (coordinateIdeal R m n)).sectionRingGrading (topAffineOpen R m n).1) ≤
      (HomogeneousIdeal.irrelevant _).map (truncSectionGradedHom R m n) :=
  irrelevant_le_map_of_rightInverse _ _ (truncSectionGradedHom_sectionTruncGradedHom R m n)

/-- `Proj` of a graded ring endomorphism equal to the identity is the identity. -/
theorem proj_map_eq_id {A : Type u} [CommRing A] {σ' : Type u} [SetLike σ' A]
    [AddSubgroupClass σ' A] {𝒜 : ℕ → σ'} [GradedRing 𝒜] (φ : 𝒜 →+*ᵍ 𝒜)
    (h : HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)
    (hφ : φ = GradedRingHom.id 𝒜) : Proj.map φ h = 𝟙 _ := by
  subst hφ
  exact Proj.map_id

/-- **The projective spectrum of the Rees algebra of the centre over `X` is the cone
`Proj(⨁_d A_{≥ d})`.** -/
def reesProjConeIso :
    AlgebraicGeometry.Proj
        ((reesSituation (coordinateIdeal R m n)).sectionRingGrading (topAffineOpen R m n).1) ≅
      AlgebraicGeometry.Proj (grading (yGrading R m n)) where
  hom := Proj.map (truncSectionGradedHom R m n) (irrelevant_le_map_truncSectionGradedHom R m n)
  inv := Proj.map (sectionTruncGradedHom R m n) (irrelevant_le_map_sectionTruncGradedHom R m n)
  hom_inv_id := by
    rw [← Proj.map_comp]
    exact proj_map_eq_id _ _
      (GradedRingHom.ext (truncSectionGradedHom_sectionTruncGradedHom R m n))
  inv_hom_id := by
    rw [← Proj.map_comp]
    exact proj_map_eq_id _ _
      (GradedRingHom.ext (sectionTruncGradedHom_truncSectionGradedHom R m n))

/-- The chart of the relative Proj of the Rees algebra of the centre over the whole of `X` is an
isomorphism. -/
instance isIso_relativeProjChart_top :
    IsIso (Stacks.RelativeProj.Situation.relativeProjChart (reesSituation (coordinateIdeal R m n))
      (topAffineOpen R m n)) :=
  haveI : IsIso (⊤ : (Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R))).Opens).ι :=
    (Scheme.topIso _).isIso_hom
  (Stacks.RelativeProj.Situation.relativeProjChart_isPullback _ _).isIso_fst_of_isIso

/-- **The standard coordinate blowup is the cone `L = Proj(⨁_d A_{≥ d})`**, with
`A = R[x₁, …, x_m, y₁, …, y_n]` graded by `deg xᵢ = 0`, `deg yⱼ = 1`. -/
def coneBlowupIso :
    AlgebraicGeometry.Proj (grading (yGrading R m n)) ≅ Stacks.DeRham.coordinateBlowup R m n :=
  (reesProjConeIso R m n).symm ≪≫ asIso (Stacks.RelativeProj.Situation.relativeProjChart
    (reesSituation (coordinateIdeal R m n)) (topAffineOpen R m n))

/-- Sending a function on `X` to degree zero of the Rees section ring and then to the truncation
ring by `sectionTruncGradedHom` is the map `σ` of the cone data. -/
theorem sectionRingZeroMap_comp_zeroHom :
    (Scheme.ΓSpecIso (.of (MvPolynomial (Fin m ⊕ Fin n) R))).inv ≫
        Stacks.RelativeProj.Situation.sectionRingZeroMap (reesSituation (coordinateIdeal R m n))
          (topAffineOpen R m n).1 ≫
        CommRingCat.ofHom (Stacks.AlgebraicGeometry.RelativeProj.zeroHom _ _
          (sectionTruncGradedHom R m n)) =
      CommRingCat.ofHom (Stacks.AlgebraicGeometry.ProjAndSpecTruncation.truncationConeData
        (yGrading R m n)).sigma.toRingHom := by
  refine CommRingCat.hom_ext (RingHom.ext fun a => Subtype.ext ?_)
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
    Function.comp_apply, Stacks.AlgebraicGeometry.RelativeProj.coe_zeroHom_apply]
  rw [coe_sectionRingZeroMap (coordinateIdeal R m n) (topAffineOpen R m n)]
  change (truncReesEquiv R m n).symm (reesSectionGradedHom _ (topAffineOpen R m n)
    ((reesSituation (coordinateIdeal R m n)).sectionRingBaseMap (topAffineOpen R m n).1
      ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin m ⊕ Fin n) R))).inv.hom a))) = _
  rw [RingEquiv.symm_apply_eq]
  refine Subtype.ext ?_
  refine (coe_reesSectionGradedHom_baseMap _ _ _).trans ?_
  change Polynomial.C ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin m ⊕ Fin n) R))).inv.hom a) =
    truncToPoly R m n
      ((sigma (yGrading R m n) a : Stacks.Truncation.grading _ 0) : TruncationRing _)
  rw [coe_sigma_apply _ a (mem_truncation_zero R m n a), coe_degreeEquiv,
    truncToPoly_of, Polynomial.monomial_zero_left]
  rfl

/-- The inverse of `IsAffineOpen.isoSpec` for the top open of `X`, followed by the inclusion of
that open, is `Spec` of the inverse of `Scheme.ΓSpecIso`. -/
theorem isoSpec_inv_ι_topAffineOpen :
    (IsAffineOpen.isoSpec (topAffineOpen R m n).2).inv ≫ (topAffineOpen R m n).1.ι =
      Spec.map (Scheme.ΓSpecIso (.of (MvPolynomial (Fin m ⊕ Fin n) R))).inv := by
  have h : (isAffineOpen_top (Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R)))).isoSpec.inv ≫
      (⊤ : (Spec (.of (MvPolynomial (Fin m ⊕ Fin n) R))).Opens).ι =
      Spec.map (Scheme.ΓSpecIso (.of (MvPolynomial (Fin m ⊕ Fin n) R))).inv := by
    rw [IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  exact h

/-- **`coneBlowupIso` is an isomorphism over `X`**: it carries the structure morphism
`L = Proj(⨁_d A_{≥ d}) ⟶ Spec A` of the cone to the blowing-up morphism `b`. -/
theorem coneBlowupIso_hom_comp :
    (coneBlowupIso R m n).hom ≫ Stacks.DeRham.coordinateBlowupToAmbient R m n =
      Stacks.AlgebraicGeometry.ProjAndSpec.toSpecA
        (Stacks.AlgebraicGeometry.ProjAndSpecTruncation.truncationConeData (yGrading R m n)) := by
  have hw := (Stacks.RelativeProj.Situation.relativeProjChart_isPullback
    (reesSituation (coordinateIdeal R m n)) (topAffineOpen R m n)).w
  have hdom := Stacks.AlgebraicGeometry.ProjShared.mapDomain_eq_top_of_irrelevant_le_map _ _ _
    (irrelevant_le_map_sectionTruncGradedHom R m n)
  have hmap := Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop_toSpecZero _ _
    (sectionTruncGradedHom R m n) hdom
  rw [Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop_eq_map _ _ _
    (irrelevant_le_map_sectionTruncGradedHom R m n)] at hmap
  simp only [coneBlowupIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
  change (reesProjConeIso R m n).inv ≫ Stacks.RelativeProj.Situation.relativeProjChart _ _ ≫
    (reesSituation (coordinateIdeal R m n)).relativeProjToBase = _
  rw [hw]
  change Proj.map (sectionTruncGradedHom R m n) _ ≫ (Proj.toSpecZero _ ≫ Spec.map _ ≫
    (topAffineOpen R m n).2.isoSpec.inv) ≫ (topAffineOpen R m n).1.ι = _
  rw [← Category.assoc, ← Category.assoc, hmap]
  simp only [Category.assoc]
  rw [isoSpec_inv_ι_topAffineOpen, ← Spec.map_comp, ← Spec.map_comp,
    Stacks.AlgebraicGeometry.ProjAndSpec.toSpecA]
  congr 2
  simpa only [Category.assoc] using sectionRingZeroMap_comp_zeroHom R m n

end Cone

end Stacks.DeRham.CoordinateCone

end
