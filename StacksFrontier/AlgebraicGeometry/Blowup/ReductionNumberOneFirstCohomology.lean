module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorFirstCohomology
public import StacksFrontier.AlgebraicGeometry.MayerVietorisHgroup.TwoAffineCoverVanishing

/-!
# Blowups in an ideal of reduction number one have no higher cohomology

Let `A` be a commutative ring, `I ⊆ A` an ideal and `a, b ∈ I` with `I² = (a, b) I`, so that
`(a, b)` is a reduction of `I` of reduction number at most one. The blowup
`X = Proj(⨁ Iⁿ)` of `Spec A` in `I` is then covered by the two affine charts `D₊(a⁽¹⁾)` and
`D₊(b⁽¹⁾)`, whose intersection `D₊(a⁽¹⁾b⁽¹⁾)` is affine, and every function on the
intersection is the sum of a function on each chart. Hence `H¹(X, 𝒪_X) = 0`, and `Hᵖ(X, ℱ) = 0`
for every quasi-coherent `ℱ` and `p ≥ 2`.

This applies to the maximal ideal `𝔪 = (π, x, y)` of the local ring `R[x, y]/(xy - πⁿ)` at the
origin when `n ≥ 2`: there `𝔪² = (π, x + y) 𝔪`. It contains the case `I = (a, b)` of
`Stacks.Blowup.isZero_Hgroup_one_proj_reesGrading_of_two_generators`.

The argument is graded: if `𝒜` is an `ℕ`-graded ring and `f, g ∈ 𝒜₁` satisfy
`𝒜_{m+1} ⊆ f 𝒜_m + g 𝒜_m` for `m ≥ 1`, then the irrelevant ideal lies in the radical of
`(f, g)`, so `D₊(f) ∪ D₊(g) = Proj 𝒜`, and an element `s / fᵖ gᵠ` of `𝒜_{(fg)}` with
`s ∈ 𝒜_{p+q}` splits, by induction on `p + q`, as a sum of elements of `𝒜_{(f)}` and `𝒜_{(g)}`.

## Main results

* `Stacks.Blowup.exists_awayMap_add_awayMap_eq_of_le`: `𝒜_{(fg)} = 𝒜_{(f)} + 𝒜_{(g)}`.
* `Stacks.Blowup.basicOpen_sup_basicOpen_eq_top_of_le`: `D₊(f) ∪ D₊(g) = Proj 𝒜`.
* `Stacks.Blowup.isZero_Hgroup_one_proj_of_le`: `H¹(Proj 𝒜, 𝒪) = 0`.
* `Stacks.Blowup.isZero_Hgroup_proj_of_le_of_two_le`: `Hᵖ(Proj 𝒜, ℱ) = 0` for `p ≥ 2`.
* `Stacks.Blowup.isZero_Hgroup_one_proj_reesGrading_of_sq_eq`: `H¹(Proj(⨁ Iⁿ), 𝒪) = 0` when
  `I² = (a, b) I`.

## References

* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open HomogeneousLocalization

universe u

namespace Stacks.Blowup

section Algebra

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)

include hf hg in
private theorem mul_mem_two : f * g ∈ 𝒜 2 := by
  simpa using SetLike.mul_mem_graded hf hg

/-- The element `s / (fᵖ gᵠ) = s fᵠ gᵖ / (fg)^{p+q}` of `𝒜_{(fg)}`, for `s ∈ 𝒜_{p+q}`. -/
private def fracAway (p q : ℕ) (s : A) (hs : s ∈ 𝒜 (p + q)) : Away 𝒜 (f * g) :=
  Away.mk 𝒜 (mul_mem_two 𝒜 hf hg) (p + q) (s * f ^ q * g ^ p) (by
    have h := SetLike.mul_mem_graded (SetLike.mul_mem_graded hs (SetLike.pow_mem_graded q hf))
      (SetLike.pow_mem_graded p hg)
    convert h using 2
    simp only [smul_eq_mul]
    ring)

include hf hg in
/-- **`𝒜_{(fg)} = 𝒜_{(f)} + 𝒜_{(g)}` when `(f, g)` is a reduction of reduction number one.** In
an `ℕ`-graded ring with `f, g` of degree one and `𝒜_{m+1} ⊆ f 𝒜_m + g 𝒜_m` for `m ≥ 1`, every
element of the degree-zero part of the localization at `fg` is the image of an element of
`𝒜_{(f)}` plus the image of an element of `𝒜_{(g)}`. -/
theorem exists_awayMap_add_awayMap_eq_of_le
    (hred : ∀ m : ℕ, 1 ≤ m → ∀ s ∈ 𝒜 (m + 1), ∃ c ∈ 𝒜 m, ∃ d ∈ 𝒜 m, s = f * c + g * d)
    (z : Away 𝒜 (f * g)) :
    ∃ (z₀ : Away 𝒜 f) (z₁ : Away 𝒜 g),
      z = awayMap 𝒜 hg rfl z₀ + awayMap 𝒜 hf (mul_comm f g) z₁ := by
  let S : AddSubgroup (Away 𝒜 (f * g)) :=
    (awayMap 𝒜 hg rfl).range.toAddSubgroup ⊔ (awayMap 𝒜 hf (mul_comm f g)).range.toAddSubgroup
  suffices hz : z ∈ S by
    obtain ⟨_, ⟨z₀, rfl⟩, _, ⟨z₁, rfl⟩, h⟩ := AddSubgroup.mem_sup.mp hz
    exact ⟨z₀, z₁, h.symm⟩
  have key : ∀ N p q, p + q = N → ∀ (s : A) (hs : s ∈ 𝒜 (p + q)),
      fracAway 𝒜 hf hg p q s hs ∈ S := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro p q hN s hs
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · refine AddSubgroup.mem_sup_left ⟨Away.mk 𝒜 hf p s (by simpa using hs), ?_⟩
        rw [awayMap_mk]
        ext
        simp [fracAway]
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · refine AddSubgroup.mem_sup_right ⟨Away.mk 𝒜 hg q s (by simpa using hs), ?_⟩
        rw [awayMap_mk]
        ext
        simp only [fracAway, Away.val_mk]
        rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
        exact ⟨1, by simp only [OneMemClass.coe_one, one_mul, pow_zero, mul_one]; ring⟩
      obtain ⟨m, hm⟩ : ∃ m, p + q = m + 1 := ⟨p + q - 1, by omega⟩
      obtain ⟨c, hc, d, hd, rfl⟩ := hred m (by omega) s (hm ▸ hs)
      obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      have hc' : c ∈ 𝒜 (p' + (q' + 1)) := by convert hc using 2; omega
      have hd' : d ∈ 𝒜 (p' + 1 + q') := by convert hd using 2; omega
      have h₁ := ih (p' + (q' + 1)) (by omega) p' (q' + 1) rfl c hc'
      have h₂ := ih (p' + 1 + q') (by omega) (p' + 1) q' rfl d hd'
      convert S.add_mem h₁ h₂ using 1
      ext
      simp only [fracAway, Away.val_mk, HomogeneousLocalization.val_add, Localization.add_mk]
      rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      exact ⟨1, by simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]; ring⟩
  obtain ⟨n, s, hs, rfl⟩ := Away.mk_surjective 𝒜 (mul_mem_two 𝒜 hf hg) z
  have hs' : s ∈ 𝒜 (n + n) := by rwa [smul_eq_mul, mul_two] at hs
  convert key (n + n) n n rfl s hs' using 1
  ext
  simp only [fracAway, Away.val_mk]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [OneMemClass.coe_one, one_mul]; ring⟩

include hf hg in
/-- **The two charts `D₊(f)`, `D₊(g)` cover `Proj 𝒜`** when `𝒜_{m+1} ⊆ f 𝒜_m + g 𝒜_m` for
`m ≥ 1`: every homogeneous element of positive degree has its square in `(f, g)`, so a relevant
homogeneous prime cannot contain both `f` and `g`. -/
theorem basicOpen_sup_basicOpen_eq_top_of_le
    (hred : ∀ m : ℕ, 1 ≤ m → ∀ s ∈ 𝒜 (m + 1), ∃ c ∈ 𝒜 m, ∃ d ∈ 𝒜 m, s = f * c + g * d) :
    Proj.basicOpen 𝒜 f ⊔ Proj.basicOpen 𝒜 g = ⊤ := by
  refine top_le_iff.mp fun x _ => ?_
  by_contra hx
  obtain ⟨hfx, hgx⟩ : f ∈ x.asHomogeneousIdeal ∧ g ∈ x.asHomogeneousIdeal := by
    simpa [Opens.mem_sup, Proj.mem_basicOpen] using hx
  have hmem : ∀ m : ℕ, 1 ≤ m → ∀ s ∈ 𝒜 (m + 1), s ∈ x.asHomogeneousIdeal := by
    intro m hm s hs
    obtain ⟨c, -, d, -, rfl⟩ := hred m hm s hs
    exact add_mem (Ideal.mul_mem_right _ _ hfx) (Ideal.mul_mem_right _ _ hgx)
  refine x.not_irrelevant_le ((HomogeneousIdeal.irrelevant_le 𝒜).mpr fun i hi s hs => ?_)
  change s ∈ 𝒜 i at hs
  show s ∈ x.asHomogeneousIdeal.toIdeal
  rcases Nat.lt_or_ge i 2 with h | h
  · obtain rfl : i = 1 := by omega
    have hs2 : s * s ∈ 𝒜 (1 + 1) := SetLike.mul_mem_graded hs hs
    exact (x.isPrime.mem_or_mem (hmem 1 le_rfl _ hs2)).elim id id
  · obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    exact hmem m (by omega) s hs

end Algebra

section Geometry

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)

open Stacks.Cohomology.CechSheaf Stacks.Cohomology.Basis in
include hf hg in
/-- **`H¹(Proj 𝒜, 𝒪) = 0` when `(f, g)` is a reduction of reduction number one**: the two charts
`D₊(f)`, `D₊(g)` cover `Proj 𝒜` (`Stacks.Blowup.basicOpen_sup_basicOpen_eq_top_of_le`), their
intersection is affine, and every function on the intersection is a sum of functions on the two
charts (`Stacks.Blowup.exists_awayMap_add_awayMap_eq_of_le`). -/
theorem isZero_Hgroup_one_proj_of_le
    (hred : ∀ m : ℕ, 1 ≤ m → ∀ s ∈ 𝒜 (m + 1), ∃ c ∈ 𝒜 m, ∃ d ∈ 𝒜 m, s = f * c + g * d) :
    IsZero (Hgroup (AlgebraicGeometry.Proj 𝒜).ringCatSheaf ⊤ 1
      (SheafOfModules.unit (AlgebraicGeometry.Proj 𝒜).ringCatSheaf)) := by
  have hfg : f * g ∈ 𝒜 2 := mul_mem_two 𝒜 hf hg
  let U₀ : (AlgebraicGeometry.Proj 𝒜).Opens := Proj.basicOpen 𝒜 f
  let U₁ : (AlgebraicGeometry.Proj 𝒜).Opens := Proj.basicOpen 𝒜 g
  have htop : U₀ ⊔ U₁ = ⊤ := basicOpen_sup_basicOpen_eq_top_of_le 𝒜 hf hg hred
  have h₀ : IsAffineOpen U₀ := Proj.isAffineOpen_basicOpen 𝒜 f hf one_pos
  have h₁ : IsAffineOpen U₁ := Proj.isAffineOpen_basicOpen 𝒜 g hg one_pos
  have hint : U₀ ⊓ U₁ = Proj.basicOpen 𝒜 (f * g) := (Proj.basicOpen_mul 𝒜 f g).symm
  have h₀₁ : IsAffineOpen (U₀ ⊓ U₁) := by
    rw [hint]
    exact Proj.isAffineOpen_basicOpen 𝒜 (f * g) hfg two_pos
  rw [← htop]
  refine Stacks.Cohomology.TwoCover.isZero_Hgroup_one_of_surjective _ h₀ h₁ h₀₁ ?_
  intro c
  let d : Γ(AlgebraicGeometry.Proj 𝒜, Proj.basicOpen 𝒜 (f * g)) :=
    (AlgebraicGeometry.Proj 𝒜).presheaf.map (homOfLE hint.ge).op (secToΓ c)
  obtain ⟨z₀, z₁, hz⟩ := exists_awayMap_add_awayMap_eq_of_le 𝒜 hf hg hred
    ((Proj.basicOpenIsoAway 𝒜 (f * g) hfg two_pos).inv d)
  refine ⟨Γtosec (-(Proj.awayToSection 𝒜 f z₀)), Γtosec (Proj.awayToSection 𝒜 g z₁), ?_⟩
  apply secToΓ_injective
  rw [secToΓ_sub, secToΓ_res, secToΓ_res, secToΓ_Γtosec, secToΓ_Γtosec]
  have hd : d = Proj.awayToSection 𝒜 (f * g)
      ((Proj.basicOpenIsoAway 𝒜 (f * g) hfg two_pos).inv d) :=
    (ConcreteCategory.congr_hom (Proj.basicOpenIsoAway 𝒜 (f * g) hfg two_pos).inv_hom_id d).symm
  have e0 := ConcreteCategory.congr_hom
    (Proj.awayMap_awayToSection 𝒜 hg (rfl : f * g = f * g)) z₀
  have e1 := ConcreteCategory.congr_hom
    (Proj.awayMap_awayToSection 𝒜 hf (mul_comm f g : f * g = g * f)) z₁
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at e0 e1
  rw [hz, map_add] at hd
  change Proj.awayToSection 𝒜 (f * g) (awayMap 𝒜 hg rfl z₀) = _ at e0
  change Proj.awayToSection 𝒜 (f * g) (awayMap 𝒜 hf (mul_comm f g) z₁) = _ at e1
  rw [e0, e1] at hd
  have hc : secToΓ c = (AlgebraicGeometry.Proj 𝒜).presheaf.map (homOfLE hint.le).op d := by
    show secToΓ c = ((AlgebraicGeometry.Proj 𝒜).presheaf.map (homOfLE hint.ge).op ≫
      (AlgebraicGeometry.Proj 𝒜).presheaf.map (homOfLE hint.le).op) (secToΓ c)
    rw [← Functor.map_comp]
    exact (ConcreteCategory.congr_hom ((AlgebraicGeometry.Proj 𝒜).presheaf.map_id _)
      (secToΓ c)).symm
  rw [hc, hd]
  exact presheaf_map_add_eq_sub_neg _ _ _ _ _ _ _

include hf hg in
/-- **`Hᵖ(Proj 𝒜, ℱ) = 0` for `p ≥ 2` when `(f, g)` is a reduction of reduction number one**:
`Proj 𝒜` is the union of the two affine opens `D₊(f)`, `D₊(g)` with affine intersection
`D₊(fg)`. -/
theorem isZero_Hgroup_proj_of_le_of_two_le
    (hred : ∀ m : ℕ, 1 ≤ m → ∀ s ∈ 𝒜 (m + 1), ∃ c ∈ 𝒜 m, ∃ d ∈ 𝒜 m, s = f * c + g * d)
    (F : (AlgebraicGeometry.Proj 𝒜).Modules) [F.IsQuasicoherent] (p : ℕ) (hp : 2 ≤ p) :
    IsZero (Hgroup (AlgebraicGeometry.Proj 𝒜).ringCatSheaf ⊤ p F) := by
  refine Stacks.Cohomology.AmbientMayerVietoris.isZero_hgroup_of_two_affine_cover_of_two_le _
    (Proj.basicOpen 𝒜 f) (Proj.basicOpen 𝒜 g) (Proj.isAffineOpen_basicOpen 𝒜 f hf one_pos)
    (Proj.isAffineOpen_basicOpen 𝒜 g hg one_pos) ?_
    (basicOpen_sup_basicOpen_eq_top_of_le 𝒜 hf hg hred) F p hp
  rw [← Proj.basicOpen_mul 𝒜 f g]
  exact Proj.isAffineOpen_basicOpen 𝒜 (f * g) (mul_mem_two 𝒜 hf hg) two_pos

end Geometry

section Rees

variable {R : Type u} [CommRing R] (I : Ideal R) {a b : R} (ha : a ∈ I) (hb : b ∈ I)

include ha hb in
/-- If `I² = (a, b) I`, the Rees algebra satisfies `𝒜_{m+1} ⊆ a⁽¹⁾ 𝒜_m + b⁽¹⁾ 𝒜_m` for `m ≥ 1`. -/
theorem reesGrading_succ_le (hI : I ^ 2 = Ideal.span {a, b} * I) (m : ℕ) (hm : 1 ≤ m)
    (s : reesAlgebra I) (hs : s ∈ reesGrading I (m + 1)) :
    ∃ c ∈ reesGrading I m, ∃ d ∈ reesGrading I m,
      s = reesDegOne I ha * c + reesDegOne I hb * d := by
  obtain ⟨⟨r, hr⟩, rfl⟩ : ∃ r : (I ^ (m + 1) : Ideal R),
      (reesGrading I (m + 1)).subtype (reesMonomial I (m + 1) r) = s :=
    (reesGrading_eq_range I (m + 1)).le hs
  have hpow : I ^ (m + 1) = Ideal.span {a, b} * I ^ m := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [show k + 1 + 1 = 2 + k by ring, pow_add, hI, mul_assoc, ← pow_succ']
  rw [hpow, Ideal.span_insert, Ideal.sup_mul, Submodule.mem_sup] at hr
  obtain ⟨y, hy, z, hz, rfl⟩ := hr
  obtain ⟨c, hc, rfl⟩ := Ideal.mem_span_singleton_mul.mp hy
  obtain ⟨d, hd, rfl⟩ := Ideal.mem_span_singleton_mul.mp hz
  refine ⟨reesMonomial I m ⟨c, hc⟩, (reesMonomial I m ⟨c, hc⟩).2,
    reesMonomial I m ⟨d, hd⟩, (reesMonomial I m ⟨d, hd⟩).2, ?_⟩
  apply Subtype.ext
  simp only [Submodule.subtype_apply, coe_reesMonomial, Subalgebra.coe_add, Subalgebra.coe_mul,
    coe_reesDegOne, Polynomial.monomial_mul_monomial, map_add]
  rw [add_comm 1 m]

include ha hb in
/-- **`H¹(Proj(⨁ Iⁿ), 𝒪) = 0` when `I² = (a, b) I`.** -/
theorem isZero_Hgroup_one_proj_reesGrading_of_sq_eq (hI : I ^ 2 = Ideal.span {a, b} * I) :
    IsZero (Hgroup (AlgebraicGeometry.Proj (reesGrading I)).ringCatSheaf ⊤ 1
      (SheafOfModules.unit (AlgebraicGeometry.Proj (reesGrading I)).ringCatSheaf)) :=
  isZero_Hgroup_one_proj_of_le (reesGrading I) (reesDegOne_mem_reesGrading I ha)
    (reesDegOne_mem_reesGrading I hb) (reesGrading_succ_le I ha hb hI)

include ha hb in
/-- **`Hᵖ(Proj(⨁ Iⁿ), ℱ) = 0` for `p ≥ 2` and quasi-coherent `ℱ` when `I² = (a, b) I`.** -/
theorem isZero_Hgroup_proj_reesGrading_of_sq_eq_of_two_le (hI : I ^ 2 = Ideal.span {a, b} * I)
    (F : (AlgebraicGeometry.Proj (reesGrading I)).Modules) [F.IsQuasicoherent] (p : ℕ)
    (hp : 2 ≤ p) :
    IsZero (Hgroup (AlgebraicGeometry.Proj (reesGrading I)).ringCatSheaf ⊤ p F) :=
  isZero_Hgroup_proj_of_le_of_two_le (reesGrading I) (reesDegOne_mem_reesGrading I ha)
    (reesDegOne_mem_reesGrading I hb) (reesGrading_succ_le I ha hb hI) F p hp

end Rees

end Stacks.Blowup

end
