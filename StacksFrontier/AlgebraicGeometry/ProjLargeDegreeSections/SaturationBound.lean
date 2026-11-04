module

public import StacksFrontier.AlgebraicGeometry.ProjSaturation.Basic

/-!
# A uniform degree bound for `𝒮₊`-power torsion in a graded module

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a Noetherian graded ring generated in degree one over `𝒮 0`, let
`M = ⨁_{d ∈ ℤ} 𝒨 d` be a finite graded `S`-module and let `N ⊆ M` be a homogeneous submodule.
A homogeneous element `x` of `M` that some power of the irrelevant ideal `𝒮₊` carries into `N`
need not itself lie in `N`; this file shows that it does as soon as its degree is large enough,
and that *one* degree bound works for every such `x` at once.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjLargeDegreeSections.IsHomogeneousSubmodule`: a submodule of a
  graded module is homogeneous when it contains all homogeneous components of its elements.

## Main results

* `Stacks.AlgebraicGeometry.ProjLargeDegreeSections.coe_decompose_smul_add_of_left_mem` and
  `Stacks.AlgebraicGeometry.ProjLargeDegreeSections.coe_decompose_smul_add_of_right_mem`: a
  homogeneous scalar shifts the homogeneous components of a module element by its degree.
* `Stacks.AlgebraicGeometry.ProjLargeDegreeSections.isHomogeneousSubmodule_ker_lsmul`,
  `Stacks.AlgebraicGeometry.ProjLargeDegreeSections.isHomogeneousSubmodule_top`,
  `Stacks.AlgebraicGeometry.ProjLargeDegreeSections.isHomogeneousSubmodule_inf` and
  `Stacks.AlgebraicGeometry.ProjLargeDegreeSections.isHomogeneousSubmodule_map_lsmul`: the
  kernel of multiplication by a homogeneous scalar, the whole module, the intersection of two
  homogeneous submodules and the image of a homogeneous submodule under multiplication by a
  homogeneous scalar are homogeneous submodules.
* `Stacks.AlgebraicGeometry.ProjLargeDegreeSections`
  `.exists_homogeneous_spanning_of_isHomogeneousSubmodule`: over a Noetherian ring a homogeneous
  submodule of a finite module is spanned by finitely many homogeneous elements of itself.
* `Stacks.AlgebraicGeometry.ProjLargeDegreeSections.exists_irrelevant_pow_smul_mem`: if every
  member of a family generating the irrelevant ideal pushes `x` into `N` after being raised to
  a power, then one whole power of the irrelevant ideal does.
* `Stacks.AlgebraicGeometry.ProjLargeDegreeSections`
  `.exists_forall_mem_of_irrelevant_pow_smul_mem`: there is a degree beyond which every
  homogeneous element that a power of the irrelevant ideal carries into `N` lies in `N`.
* `Stacks.AlgebraicGeometry.ProjLargeDegreeSections.exists_forall_mem_of_forall_pow_smul_mem`:
  the same bound with the torsion hypothesis phrased along a generating family.

## References

* [Stacks Project, Tag 0AG7](https://stacks.math.columbia.edu/tag/0AG7)
-/

@[expose] public noncomputable section

open DirectSum
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjLargeDegreeSections

universe u v w t

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]

omit [AddSubgroupClass σ S] [GradedRing 𝒮] in
/-- **A homogeneous scalar shifts the homogeneous components of a module element.** If
`a ∈ 𝒮 e` then the degree-`e + j` component of `a • x` is `a` times the degree-`j` component of
`x`. This is the module analogue of `DirectSum.coe_decompose_mul_add_of_left_mem`. -/
theorem coe_decompose_smul_add_of_left_mem {e : ℕ} {a : S} (ha : a ∈ 𝒮 e) (x : M) (j : ℤ) :
    (decompose 𝒨 (a • x) ((e : ℤ) + j) : M) = a • (decompose 𝒨 x j : M) := by
  induction x using DirectSum.Decomposition.inductionOn 𝒨 with
  | zero => simp
  | homogeneous m =>
      rename_i i
      have hm : a • (m : M) ∈ 𝒨 ((e : ℤ) + i) := SetLike.GradedSMul.smul_mem ha m.2
      rcases eq_or_ne i j with rfl | hij
      · rw [DirectSum.decompose_of_mem_same 𝒨 hm, DirectSum.decompose_of_mem_same 𝒨 m.2]
      · rw [DirectSum.decompose_of_mem_ne 𝒨 hm (by omega),
          DirectSum.decompose_of_mem_ne 𝒨 m.2 hij, smul_zero]
  | add m m' hm hm' => simp [smul_add, hm, hm']

/-- **The component of a scalar seen by a homogeneous module element.** If `x ∈ 𝒨 j` then the
degree-`e + j` component of `c • x` is the degree-`e` component of `c` acting on `x`: only that
one component of `c` contributes in that degree. This is the module analogue of
`DirectSum.coe_decompose_mul_add_of_right_mem`. -/
theorem coe_decompose_smul_add_of_right_mem (c : S) (e : ℕ) {j : ℤ} {x : M} (hx : x ∈ 𝒨 j) :
    (decompose 𝒨 (c • x) ((e : ℤ) + j) : M) = (decompose 𝒮 c e : S) • x := by
  induction c using DirectSum.Decomposition.inductionOn 𝒮 with
  | zero => simp
  | homogeneous b =>
      rename_i i
      have hb : (b : S) • x ∈ 𝒨 ((i : ℤ) + j) := SetLike.GradedSMul.smul_mem b.2 hx
      rcases eq_or_ne i e with rfl | hie
      · rw [DirectSum.decompose_of_mem_same 𝒨 hb, DirectSum.decompose_of_mem_same 𝒮 b.2]
      · rw [DirectSum.decompose_of_mem_ne 𝒨 hb (by omega),
          DirectSum.decompose_of_mem_ne 𝒮 b.2 hie, zero_smul]
  | add c c' hc hc' => simp [add_smul, hc, hc']

/-- A submodule of a graded module is **homogeneous**, or graded, when every homogeneous
component of every one of its elements again belongs to it. -/
def IsHomogeneousSubmodule (N : Submodule S M) : Prop :=
  ∀ x ∈ N, ∀ d : ℤ, (decompose 𝒨 x d : M) ∈ N

omit [AddSubgroupClass σ S] [GradedRing 𝒮] in
/-- **The annihilator of a homogeneous scalar is a homogeneous submodule.** If `a ∈ 𝒮 e` kills
`x` then it kills each homogeneous component of `x`. -/
theorem isHomogeneousSubmodule_ker_lsmul {e : ℕ} {a : S} (ha : a ∈ 𝒮 e) :
    IsHomogeneousSubmodule 𝒨 (LinearMap.ker (LinearMap.lsmul S M a)) := by
  intro x hx d
  simp only [LinearMap.mem_ker, LinearMap.lsmul_apply] at hx ⊢
  rw [← coe_decompose_smul_add_of_left_mem 𝒮 𝒨 ha x d, hx]
  simp

/-- **The whole module is a homogeneous submodule.** -/
theorem isHomogeneousSubmodule_top : IsHomogeneousSubmodule 𝒨 (⊤ : Submodule S M) :=
  fun _ _ _ => Submodule.mem_top

/-- **The intersection of two homogeneous submodules is homogeneous.** -/
theorem isHomogeneousSubmodule_inf {P Q : Submodule S M} (hP : IsHomogeneousSubmodule 𝒨 P)
    (hQ : IsHomogeneousSubmodule 𝒨 Q) : IsHomogeneousSubmodule 𝒨 (P ⊓ Q) :=
  fun _ hx _ => ⟨hP _ hx.1 _, hQ _ hx.2 _⟩

omit [AddSubgroupClass σ S] [GradedRing 𝒮] in
/-- **`a • P` is a homogeneous submodule when `P` is one and `a` is homogeneous.** -/
theorem isHomogeneousSubmodule_map_lsmul {e : ℕ} {a : S} (ha : a ∈ 𝒮 e) {P : Submodule S M}
    (hP : IsHomogeneousSubmodule 𝒨 P) :
    IsHomogeneousSubmodule 𝒨 (P.map (LinearMap.lsmul S M a)) := by
  intro x hx d
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
  have key := coe_decompose_smul_add_of_left_mem 𝒮 𝒨 ha p (d - (e : ℤ))
  rw [add_sub_cancel] at key
  refine Submodule.mem_map.mpr ⟨(decompose 𝒨 p (d - (e : ℤ)) : M), hP _ hp _, ?_⟩
  simpa only [LinearMap.lsmul_apply] using key.symm

/-- **A homogeneous submodule of a finite module over a Noetherian ring is spanned by finitely
many homogeneous elements of itself.** -/
theorem exists_homogeneous_spanning_of_isHomogeneousSubmodule [IsNoetherianRing S]
    [Module.Finite S M] {N : Submodule S M} (hN : IsHomogeneousSubmodule 𝒨 N) :
    ∃ (r : ℕ) (x : Fin r → M) (d : Fin r → ℤ), (∀ j, x j ∈ 𝒨 (d j)) ∧ (∀ j, x j ∈ N) ∧
      N ≤ Submodule.span S (Set.range x) := by
  classical
  obtain ⟨t, ht⟩ : N.FG := IsNoetherian.noetherian N
  have hsub : ∀ y ∈ t, y ∈ N := fun y hy => ht ▸ Submodule.subset_span hy
  set U : Finset (ℤ × M) := t.biUnion fun g =>
    (decompose 𝒨 g).support.image fun i => (i, (decompose 𝒨 g i : M)) with hUdef
  have hU : ∀ p ∈ U, p.2 ∈ 𝒨 p.1 ∧ p.2 ∈ N := by
    intro p hp
    simp only [hUdef, Finset.mem_biUnion, Finset.mem_image] at hp
    obtain ⟨g, hg, i, -, rfl⟩ := hp
    exact ⟨SetLike.coe_mem _, hN g (hsub g hg) i⟩
  refine ⟨Fintype.card ↥U, fun j => (((Fintype.equivFin ↥U).symm j : ↥U) : ℤ × M).2,
    fun j => (((Fintype.equivFin ↥U).symm j : ↥U) : ℤ × M).1,
    fun j => (hU _ ((Fintype.equivFin ↥U).symm j).2).1,
    fun j => (hU _ ((Fintype.equivFin ↥U).symm j).2).2, ?_⟩
  rw [← ht, Submodule.span_le]
  intro g hg
  rw [SetLike.mem_coe, ← DirectSum.sum_support_decompose 𝒨 g]
  refine Submodule.sum_mem _ fun i hi => Submodule.subset_span ?_
  have hmem : ((i, (decompose 𝒨 g i : M)) : ℤ × M) ∈ U := by
    simp only [hUdef, Finset.mem_biUnion, Finset.mem_image]
    exact ⟨g, hg, i, hi, rfl⟩
  exact ⟨Fintype.equivFin ↥U ⟨_, hmem⟩, by simp⟩

/-- **From torsion along a generating family to torsion along a power of the irrelevant
ideal.** If `S` is Noetherian and each member of a family `f` generating the irrelevant ideal
carries `x` into `N` after being raised to some power, then one whole power of the irrelevant ideal
carries `x` into `N`. -/
theorem exists_irrelevant_pow_smul_mem [IsNoetherianRing S] {N : Submodule S M} {x : M}
    {ι : Type*} (f : ι → S)
    (hspan : Ideal.span (Set.range f) = (HomogeneousIdeal.irrelevant 𝒮).toIdeal)
    (hf : ∀ j, ∃ k : ℕ, (f j) ^ k • x ∈ N) :
    ∃ e : ℕ, ∀ a ∈ (HomogeneousIdeal.irrelevant 𝒮).toIdeal ^ e, a • x ∈ N := by
  set I : Ideal S := N.comap (LinearMap.toSpanSingleton S M x) with hI
  have hmemI : ∀ c : S, c ∈ I ↔ c • x ∈ N := by
    intro c
    simp [hI, LinearMap.toSpanSingleton_apply]
  have hrad : (HomogeneousIdeal.irrelevant 𝒮).toIdeal ≤ I.radical := by
    rw [← hspan, Ideal.span_le]
    rintro - ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hf j
    exact Ideal.mem_radical_iff.mpr ⟨k, (hmemI _).mpr hk⟩
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (Ideal.fg_of_isNoetherianRing _)
  exact ⟨e, fun a ha => (hmemI a).mp (he ha)⟩

/-- Every power of the irrelevant ideal is a homogeneous ideal. -/
private theorem isHomogeneous_irrelevant_pow (e : ℕ) :
    ((HomogeneousIdeal.irrelevant 𝒮).toIdeal ^ e).IsHomogeneous 𝒮 := by
  induction e with
  | zero =>
      rw [pow_zero, Ideal.one_eq_top]
      exact Ideal.IsHomogeneous.top 𝒮
  | succ n ih =>
      rw [pow_succ]
      exact ih.mul (HomogeneousIdeal.irrelevant 𝒮).isHomogeneous

/-- The **saturation** of a submodule `N`: the elements that some power of the irrelevant ideal
carries into `N`. -/
private def irrelevantSaturation (N : Submodule S M) : Submodule S M where
  carrier := {x | ∃ e : ℕ, ∀ a ∈ (HomogeneousIdeal.irrelevant 𝒮).toIdeal ^ e, a • x ∈ N}
  zero_mem' := ⟨0, fun a _ => by simp⟩
  add_mem' := by
    rintro x z ⟨e₁, h₁⟩ ⟨e₂, h₂⟩
    refine ⟨max e₁ e₂, fun a ha => ?_⟩
    rw [smul_add]
    exact N.add_mem (h₁ a (Ideal.pow_le_pow_right (le_max_left e₁ e₂) ha))
      (h₂ a (Ideal.pow_le_pow_right (le_max_right e₁ e₂) ha))
  smul_mem' := by
    rintro c x ⟨e, he⟩
    refine ⟨e, fun a ha => ?_⟩
    rw [smul_comm]
    exact N.smul_mem c (he a ha)

/-- Membership in the saturation, unfolded. -/
private theorem mem_irrelevantSaturation {N : Submodule S M} {x : M} :
    x ∈ irrelevantSaturation 𝒮 N ↔
      ∃ e : ℕ, ∀ a ∈ (HomogeneousIdeal.irrelevant 𝒮).toIdeal ^ e, a • x ∈ N :=
  Iff.rfl

/-- **The saturation of a homogeneous submodule is homogeneous.** -/
private theorem isHomogeneousSubmodule_irrelevantSaturation {N : Submodule S M}
    (hN : IsHomogeneousSubmodule 𝒨 N) :
    IsHomogeneousSubmodule 𝒨 (irrelevantSaturation 𝒮 N) := by
  classical
  rintro x ⟨e, he⟩ d
  refine (mem_irrelevantSaturation 𝒮).mpr ⟨e, fun a ha => ?_⟩
  rw [← DirectSum.sum_support_decompose 𝒮 a, Finset.sum_smul]
  refine N.sum_mem fun i _ => ?_
  have hcomp : (decompose 𝒮 a i : S) ∈ (HomogeneousIdeal.irrelevant 𝒮).toIdeal ^ e :=
    isHomogeneous_irrelevant_pow 𝒮 e i ha
  rw [← coe_decompose_smul_add_of_left_mem 𝒮 𝒨 (SetLike.coe_mem (decompose 𝒮 a i)) x d]
  exact hN _ (he _ hcomp) _

/-- **The uniform degree bound.** Let `S` be a Noetherian graded ring generated in degree one
over `𝒮 0`, let `M` be a finite graded `S`-module and let `N ⊆ M` be a homogeneous submodule.
Then there is a degree `d₀` beyond which no homogeneous element is `𝒮₊`-power torsion modulo
`N` without already lying in `N`. -/
theorem exists_forall_mem_of_irrelevant_pow_smul_mem [IsNoetherianRing S] [Module.Finite S M]
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤)
    {N : Submodule S M} (hN : IsHomogeneousSubmodule 𝒨 N) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ x : M, x ∈ 𝒨 d →
      (∃ e : ℕ, ∀ a ∈ (HomogeneousIdeal.irrelevant 𝒮).toIdeal ^ e, a • x ∈ N) → x ∈ N := by
  classical
  obtain ⟨r, y, dy, hy, hyT, hspanT⟩ :=
    exists_homogeneous_spanning_of_isHomogeneousSubmodule 𝒨
      (isHomogeneousSubmodule_irrelevantSaturation 𝒮 𝒨 hN)
  choose ey hey using fun j => (mem_irrelevantSaturation 𝒮).mp (hyT j)
  refine ⟨∑ j, (|dy j| + (ey j : ℤ)), fun d hd x hx hxT => ?_⟩
  have hk : ∀ j, ey j ≤ (d - dy j).toNat ∧ (((d - dy j).toNat : ℕ) : ℤ) + dy j = d := fun j => by
    grind [le_abs_self (dy j), Finset.single_le_sum (f := fun j => |dy j| + (ey j : ℤ))
      (fun i _ => by positivity) (Finset.mem_univ j)]
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).mp
    (hspanT ((mem_irrelevantSaturation 𝒮).mpr hxT))
  have hxeq : x = ∑ j, (decompose 𝒮 (c j) ((d - dy j).toNat) : S) • y j := by
    calc x = (decompose 𝒨 x d : M) := (DirectSum.decompose_of_mem_same 𝒨 hx).symm
      _ = (decompose 𝒨 (∑ j, c j • y j) d : M) := by rw [hc]
      _ = ∑ j, (decompose 𝒨 (c j • y j) d : M) := by simp
      _ = ∑ j, (decompose 𝒮 (c j) ((d - dy j).toNat) : S) • y j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          have := coe_decompose_smul_add_of_right_mem 𝒮 𝒨 (c j) (d - dy j).toNat (hy j)
          rwa [(hk j).2] at this
  rw [hxeq]
  exact N.sum_mem fun j _ => hey j _ (Ideal.pow_le_pow_right (hk j).1
    (AlgebraicGeometry.ProjectiveSpectrum.Proj.mem_irrelevant_pow_of_mem 𝒮 hgen _
      (SetLike.coe_mem (decompose 𝒮 (c j) ((d - dy j).toNat)))))

/-- **The uniform degree bound, with the torsion hypothesis along a generating family.** The
same statement as `exists_forall_mem_of_irrelevant_pow_smul_mem`, with "some power of the
irrelevant ideal carries `x` into `N`" replaced by "each `f j` carries `x` into `N` after being
raised to a power", for any family `f` generating the irrelevant ideal. -/
theorem exists_forall_mem_of_forall_pow_smul_mem [IsNoetherianRing S] [Module.Finite S M]
    (hgen : Algebra.adjoin (𝒮 0) (𝒮 1 : Set S) = ⊤)
    {ι : Type*} (f : ι → S)
    (hspan : Ideal.span (Set.range f) = (HomogeneousIdeal.irrelevant 𝒮).toIdeal)
    {N : Submodule S M} (hN : IsHomogeneousSubmodule 𝒨 N) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ x : M, x ∈ 𝒨 d →
      (∀ j, ∃ k : ℕ, (f j) ^ k • x ∈ N) → x ∈ N := by
  obtain ⟨d₀, hd₀⟩ := exists_forall_mem_of_irrelevant_pow_smul_mem 𝒮 𝒨 hgen hN
  exact ⟨d₀, fun d hd x hx hf =>
    hd₀ d hd x hx (exists_irrelevant_pow_smul_mem 𝒮 f hspan hf)⟩

end Stacks.AlgebraicGeometry.ProjLargeDegreeSections

end
