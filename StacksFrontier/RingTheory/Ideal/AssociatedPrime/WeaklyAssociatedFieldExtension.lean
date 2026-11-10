module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.Functoriality
public import StacksFrontier.RingTheory.Ideal.Annihilator.FlatBaseChange
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Weakly associated primes and extension of the ground field

Let `K / k` be a field extension, `R` a `k`-algebra and `M` an `R`-module. If a prime
`𝔮 ⊂ R ⊗_k K` lying over `𝔭 ⊂ R` is weakly associated to the `R ⊗_k K`-module `M ⊗_k K`, then
`𝔭` is weakly associated to `M`.

The proof reduces the statement in three steps. First, an element `z ∈ M ⊗_k K` whose annihilator
has `𝔮` as a minimal prime already lives in `M ⊗_k E` for an intermediate field `E` which is
finite over `L = k(xᵢ)`, where `(xᵢ)` is a transcendence basis of `K / k`; since
`R ⊗_k E → R ⊗_k K` is flat, `𝔮 ∩ (R ⊗_k E)` is minimal over the annihilator of `z` in the
smaller ring. Second, `R ⊗_k L → R ⊗_k E` is finite, so the contraction of `𝔮` to `R ⊗_k L` is
weakly associated to `M ⊗_k E` viewed as an `R ⊗_k L`-module. Third, since `κ(𝔭) ⊗_k L` is a
domain, every element of `R ⊗_k L` outside that contraction acts on `M ⊗_k E` injectively up to
elements of `R \ 𝔭`, which shows that `𝔭` is weakly associated to `M ⊗_k E`, a direct sum of
copies of `M`.

## Main results

* `IsWeaklyAssociatedPrime.comap_tensorProduct_field`: the statement above (Stacks 0CUB).
* `IsWeaklyAssociatedPrime.comap_of_finite_of_flat`: the abstract form of the last two steps,
  for a finite flat map `A → T` of free `R`-algebras.
* `IsWeaklyAssociatedPrime.of_tensorProduct_free`: a prime weakly associated to `P ⊗[R] M`,
  with `P` free, is weakly associated to `M`.
* `Algebra.TensorProduct.isDomain_fractionRing_mvPolynomial`: `κ ⊗_k k(xᵢ)` is a domain for a
  field extension `κ / k`.

## Implementation notes

The `R ⊗_k K`-module `M ⊗_k K` is written as the base change `(R ⊗[k] K) ⊗[R] M`, to which it is
canonically isomorphic; this is the form in which Mathlib equips it with its module structure.
The prime `𝔭` that `𝔮` lies over is `𝔮.comap (algebraMap R (R ⊗[k] K))`.

The argument follows the source, except that the purely transcendental case is not reduced to a
local ring `R`: the Nakayama argument there is replaced by a nonzero `R`-linear map from a finite
submodule of `M` to `κ(𝔭)` (`Module.exists_linearMap_residueField_ne_zero`), and the finite step
does not split `M ⊗_k E` into copies of `M ⊗_k L` but uses flatness of `R ⊗_k E` over
`R ⊗_k L` (`TensorProduct.exists_notMem_smul_eq_zero_of_flat`).

## References

* [Stacks, Tag 0CUB](https://stacks.math.columbia.edu/tag/0CUB)
-/

@[expose] public section

open TensorProduct

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- A prime weakly associated to a direct sum `⨁_{i ∈ ι} M` of copies of `M` is weakly
associated to `M`: the annihilator of `(m_i)_i` is the finite intersection of the annihilators
of the nonzero `m_i`, and a prime minimal over a finite intersection is minimal over one of the
ideals intersected. -/
theorem IsWeaklyAssociatedPrime.of_finsupp {ι : Type*} {p : Ideal R}
    (h : IsWeaklyAssociatedPrime R (ι →₀ M) p) : IsWeaklyAssociatedPrime R M p := by
  classical
  obtain ⟨c, hc⟩ := h
  have hp : p.IsPrime := hc.1.1
  have hle : ∀ i, (R ∙ c).annihilator ≤ (R ∙ c i).annihilator := by
    intro i r hr
    rw [Submodule.mem_annihilator_span_singleton] at hr ⊢
    simpa using DFunLike.congr_fun hr i
  obtain ⟨i, hi⟩ : ∃ i, (R ∙ c i).annihilator ≤ p := by
    by_contra! H
    have H' : ∀ i ∈ c.support, ∃ a : R, a • c i = 0 ∧ a ∉ p := by
      intro i _
      obtain ⟨a, ha, hap⟩ := Set.not_subset.mp (H i)
      exact ⟨a, (Submodule.mem_annihilator_span_singleton _ _).mp ha, hap⟩
    choose! a ha using H'
    have hprod : (∏ i ∈ c.support, a i) ∈ (R ∙ c).annihilator := by
      rw [Submodule.mem_annihilator_span_singleton]
      ext j
      by_cases hj : j ∈ c.support
      · rw [Finsupp.smul_apply, ← Finset.mul_prod_erase _ _ hj, mul_comm, mul_smul, (ha j hj).1,
          smul_zero, Finsupp.zero_apply]
      · simp [Finsupp.notMem_support_iff.mp hj]
    obtain ⟨j, hj, hjp⟩ := Ideal.IsPrime.prod_mem_iff.mp (hc.1.2 hprod)
    exact (ha j hj).2 hjp
  exact ⟨c i, ⟨hp, hi⟩, fun P hP hPp => hc.2 ⟨hP.1, (hle i).trans hP.2⟩ hPp⟩

/-- A linear equivalence preserves the annihilator of the span of an element. -/
private theorem annihilator_span_singleton_equiv {N N' : Type*} [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N'] (e : N ≃ₗ[R] N') (z : N) :
    (R ∙ e z).annihilator = (R ∙ z).annihilator := by
  ext r
  simp only [Submodule.mem_annihilator_span_singleton, ← map_smul, e.map_eq_zero_iff]

/-- If `P` is a free `R`-module, a prime weakly associated to `P ⊗[R] M` is weakly associated
to `M`, since `P ⊗[R] M` is a direct sum of copies of `M`. -/
@[ega "IV 3.3.8" "special case"]
theorem IsWeaklyAssociatedPrime.of_tensorProduct_free (P : Type*) [AddCommGroup P] [Module R P]
    [Module.Free R P] {p : Ideal R} (h : IsWeaklyAssociatedPrime R (P ⊗[R] M) p) :
    IsWeaklyAssociatedPrime R M p := by
  obtain ⟨z, hz⟩ := h
  let e := TensorProduct.equivFinsuppOfBasisLeft (M := P) (N := M) (Module.Free.chooseBasis R P)
  refine IsWeaklyAssociatedPrime.of_finsupp (ι := Module.Free.ChooseBasisIndex R P) ⟨e z, ?_⟩
  rwa [annihilator_span_singleton_equiv]

/-- Naturality of `TensorProduct.equivFinsuppOfBasisLeft` with respect to base change of a
linear map. -/
theorem LinearMap.baseChange_equivFinsuppOfBasisLeft_symm {A : Type*} [CommRing A] [Algebra R A]
    {ι : Type*} [DecidableEq ι] (b : Module.Basis ι R A) {N N' : Type*} [AddCommGroup N]
    [Module R N] [AddCommGroup N'] [Module R N'] (f : N →ₗ[R] N') (c : ι →₀ N) :
    f.baseChange A ((equivFinsuppOfBasisLeft b).symm c) =
      (equivFinsuppOfBasisLeft b).symm (c.mapRange f f.map_zero) := by
  simp [equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_mapRange_index, map_finsuppSum]

/-- A finite `R`-module `N` with `𝔭` in its support, i.e. `Ann_R(N) ⊆ 𝔭`, has a nonzero
`R`-linear map to the residue field `κ(𝔭)`. -/
theorem Module.exists_linearMap_residueField_ne_zero {N : Type*} [AddCommGroup N] [Module R N]
    [Module.Finite R N] (p : Ideal R) [p.IsPrime] (h : Module.annihilator R N ≤ p) :
    ∃ μ : N →ₗ[R] p.ResidueField, μ ≠ 0 := by
  have hs : (⟨p, inferInstance⟩ : PrimeSpectrum R) ∈ Module.support R N :=
    Module.mem_support_iff_of_finite.mpr h
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hs
  obtain ⟨x, hx⟩ := exists_ne (0 : p.ResidueField ⊗[R] N)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual p.ResidueField (p.ResidueField ⊗[R] N), φ x ≠ 0 := by
    by_contra! H
    exact hx ((Module.forall_dual_apply_eq_zero_iff _ _).mp H)
  refine ⟨(φ.restrictScalars R).comp (TensorProduct.mk R p.ResidueField N 1), fun h0 => hφ ?_⟩
  have key : ∀ y, φ y = 0 := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul a n =>
      have := LinearMap.congr_fun h0 n
      simp only [LinearMap.coe_comp, Function.comp_apply, mk_apply, LinearMap.coe_restrictScalars,
        LinearMap.zero_apply] at this
      rw [← mul_one a, ← smul_eq_mul, ← smul_tmul', map_smul, this, smul_zero]
    | add y y' hy hy' => rw [map_add, hy, hy', add_zero]
  exact key x

/-- An element of `Ann_R(N)` kills `A ⊗[R] N`. -/
theorem TensorProduct.smul_eq_zero_of_mem_annihilator {A N : Type*} [AddCommGroup A] [Module R A]
    [AddCommGroup N] [Module R N] {g : R} (hg : g ∈ Module.annihilator R N) (t : A ⊗[R] N) :
    g • t = 0 := by
  induction t using TensorProduct.inductionOn with
  | tmul a n => rw [← tmul_smul, Module.mem_annihilator.mp hg, tmul_zero]
  | add u v hu hv => rw [smul_add, hu, hv, add_zero]

/-- Let `A` be a free `R`-algebra, `𝔭 ⊂ R` a prime and `G ∈ A` an element acting injectively on
`A ⊗[R] κ(𝔭)`. If `G` kills `y ∈ A ⊗[R] M`, then so does some `g ∈ R \ 𝔭`.

Write `y = ∑ bᵢ ⊗ mᵢ` in a basis `(bᵢ)` of `A` and let `N` be the span of the `mᵢ`. If some
`g ∉ 𝔭` kills `N` we are done. Otherwise there is a nonzero `μ : N → κ(𝔭)`, which is nonzero on
some `mᵢ`, and `id ⊗ μ` maps `y` to a nonzero element of `A ⊗[R] κ(𝔭)` killed by `G`. -/
theorem TensorProduct.exists_notMem_smul_eq_zero_of_basis {A : Type*} [CommRing A] [Algebra R A]
    {ι : Type*} (b : Module.Basis ι R A) (p : Ideal R) [p.IsPrime] {G : A}
    (hG : ∀ x : A ⊗[R] p.ResidueField, G • x = 0 → x = 0) {y : A ⊗[R] M} (hy : G • y = 0) :
    ∃ g ∉ p, g • y = 0 := by
  classical
  let e := equivFinsuppOfBasisLeft (M := A) (N := M) b
  set c := e y with hc
  let N : Submodule R M := Submodule.span R (Finset.image c c.support : Set M)
  have hcN : ∀ i, c i ∈ N := fun i => by
    by_cases hi : i ∈ c.support
    · exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem c hi))
    · simp [Finsupp.notMem_support_iff.mp hi]
  let c' : ι →₀ N := Finsupp.onFinset c.support (fun i => ⟨c i, hcN i⟩)
    (fun i hi => Finsupp.mem_support_iff.mpr (fun h => hi (Subtype.ext h)))
  have hc' : c'.mapRange N.subtype N.subtype.map_zero = c := by
    ext i
    simp [c']
  set yN := (equivFinsuppOfBasisLeft (M := A) (N := N) b).symm c' with hyN_def
  have hyN : N.subtype.baseChange A yN = y := by
    rw [hyN_def, LinearMap.baseChange_equivFinsuppOfBasisLeft_symm, hc', hc]
    exact e.symm_apply_apply y
  have : Module.Free R A := Module.Free.of_basis b
  have hinj : Function.Injective (N.subtype.baseChange A) := by
    have := Module.Flat.lTensor_preserves_injective_linearMap (M := A) _ N.injective_subtype
    rwa [← LinearMap.baseChange_eq_lTensor] at this
  have hGyN : G • yN = 0 := hinj (by rw [map_smul, hyN, hy, map_zero])
  have : Module.Finite R N := Module.Finite.span_finset R _
  by_cases hann : Module.annihilator R N ≤ p
  · exfalso
    obtain ⟨μ, hμ⟩ := Module.exists_linearMap_residueField_ne_zero p hann
    have h1 : μ.baseChange A yN = 0 := hG _ (by rw [← map_smul, hGyN, map_zero])
    rw [hyN_def, LinearMap.baseChange_equivFinsuppOfBasisLeft_symm] at h1
    have h2 : c'.mapRange μ μ.map_zero = 0 :=
      (equivFinsuppOfBasisLeft b).symm.injective (by rw [h1, map_zero])
    have hgen : ∀ i, μ ⟨c i, hcN i⟩ = 0 := fun i => by
      simpa [c'] using DFunLike.congr_fun h2 i
    apply hμ
    ext ⟨m, hm⟩
    simp only [LinearMap.zero_apply]
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      exact hgen i
    | zero => exact μ.map_zero
    | add x y hx hy ihx ihy =>
      have := μ.map_add ⟨x, hx⟩ ⟨y, hy⟩
      rwa [ihx, ihy, add_zero] at this
    | smul a x hx ih =>
      have := μ.map_smul a ⟨x, hx⟩
      rwa [ih, smul_zero] at this
  · obtain ⟨g, hg, hgp⟩ := Set.not_subset.mp hann
    refine ⟨g, hgp, ?_⟩
    rw [← hyN, ← LinearMap.map_smul_of_tower, smul_eq_zero_of_mem_annihilator hg, map_zero]

/-- The version of `TensorProduct.exists_notMem_smul_eq_zero_of_basis` for a flat `A`-algebra
`T`: if `G ∈ A` acts injectively on `A ⊗[R] κ(𝔭)` and kills `y ∈ T ⊗[R] M`, then so does some
`g ∈ R \ 𝔭`. By flatness the kernel of `G` on `T ⊗[A] (A ⊗[R] M) = T ⊗[R] M` is the image of
`T ⊗[A] ker(G)`, and every element of `ker(G) ⊆ A ⊗[R] M` is killed by an element of `R \ 𝔭`. -/
theorem TensorProduct.exists_notMem_smul_eq_zero_of_flat {A T : Type*} [CommRing A] [Algebra R A]
    {ι : Type*} (b : Module.Basis ι R A) [CommRing T] [Algebra R T] [Algebra A T]
    [IsScalarTower R A T]
    [Module.Flat A T] (p : Ideal R) [p.IsPrime] {G : A}
    (hG : ∀ x : A ⊗[R] p.ResidueField, G • x = 0 → x = 0) {y : T ⊗[R] M}
    (hy : algebraMap A T G • y = 0) : ∃ g ∉ p, g • y = 0 := by
  let e := AlgebraTensorModule.cancelBaseChange R A T T M
  let φ : (A ⊗[R] M) →ₗ[A] (A ⊗[R] M) := G • LinearMap.id
  have hφ : ∀ t : T ⊗[A] (A ⊗[R] M), φ.lTensor T t = algebraMap A T G • t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a x =>
      simp only [LinearMap.lTensor_tmul, φ, LinearMap.smul_apply, LinearMap.id_apply,
        algebraMap_smul, smul_tmul', ← smul_tmul]
    | add u v hu hv => rw [map_add, hu, hv, smul_add]
  have hy' : φ.lTensor T (e.symm y) = 0 := by
    rw [hφ, ← map_smul, hy, map_zero]
  obtain ⟨u, hu⟩ := (Module.Flat.lTensor_exact (R := A) (N := LinearMap.ker φ) (N' := A ⊗[R] M)
    (N'' := A ⊗[R] M) T (LinearMap.exact_subtype_ker_map φ) (e.symm y)).mp hy'
  have key : ∀ u : T ⊗[A] (LinearMap.ker φ), ∃ g ∉ p,
      g • ((LinearMap.ker φ).subtype.lTensor T u) = 0 := by
    intro u
    induction u using TensorProduct.inductionOn with
    | tmul t k =>
      obtain ⟨g, hgp, hg⟩ := TensorProduct.exists_notMem_smul_eq_zero_of_basis b p hG
        (y := (k : A ⊗[R] M))
        (LinearMap.mem_ker.mp k.2 :)
      refine ⟨g, hgp, ?_⟩
      rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, smul_tmul', ← algebraMap_smul A g t,
        smul_tmul, algebraMap_smul, hg, tmul_zero]
    | add u v hu hv =>
      obtain ⟨g₁, hg₁p, hg₁⟩ := hu
      obtain ⟨g₂, hg₂p, hg₂⟩ := hv
      refine ⟨g₁ * g₂, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hg₁p hg₂p, ?_⟩
      simp only [map_add, smul_add, mul_smul, hg₂, smul_zero, add_zero]
      rw [smul_comm, hg₁, smul_zero]
  obtain ⟨g, hgp, hg⟩ := key u
  refine ⟨g, hgp, ?_⟩
  rw [hu] at hg
  have := congrArg e hg
  rwa [← algebraMap_smul T g, map_smul, LinearEquiv.apply_symm_apply, map_zero,
    algebraMap_smul] at this

/-- Let `A → B` be flat and `z` an element of an `A`-module `N`. If `𝔮 ⊂ B` is minimal over
the annihilator of `1 ⊗ z ∈ B ⊗[A] N`, then `𝔮 ∩ A` is minimal over the annihilator of `z`.
This combines `Ann_B(1 ⊗ z) = Ann_A(z) B` (Stacks 07T8) with going down for flat maps
(Stacks 00HS). -/
@[sga "1 IV 2.4" "case M = B"]
theorem Ideal.comap_mem_minimalPrimes_annihilator_of_flat {A B N : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Module.Flat A B] [AddCommGroup N] [Module A N] (z : N)
    {Q : Ideal B} (hQ : Q ∈ (B ∙ ((1 : B) ⊗ₜ[A] z)).annihilator.minimalPrimes) :
    Q.comap (algebraMap A B) ∈ (A ∙ z).annihilator.minimalPrimes := by
  have hann : (A ∙ z).annihilator.map (algebraMap A B) = (B ∙ ((1 : B) ⊗ₜ[A] z)).annihilator := by
    rw [Ideal.annihilator_span_singleton_eq_torsionOf,
      Ideal.annihilator_span_singleton_eq_torsionOf,
      ann_extension_eq_ann_baseChange_elem]
  have hQp : Q.IsPrime := hQ.1.1
  refine ⟨⟨Ideal.comap_isPrime _ _, Ideal.map_le_iff_le_comap.mp (hann ▸ hQ.1.2)⟩, ?_⟩
  rintro P ⟨hP, hIP⟩ hPQ
  have : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat
  have : Q.LiesOver (Q.comap (algebraMap A B)) := ⟨rfl⟩
  obtain ⟨P', hP'Q, hP', hP'P⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := P) Q hPQ
  have hle : (B ∙ ((1 : B) ⊗ₜ[A] z)).annihilator ≤ P' := by
    rw [← hann, Ideal.map_le_iff_le_comap]
    exact hIP.trans hP'P.over.le
  exact (Ideal.comap_mono (hQ.2 ⟨hP', hle⟩ hP'Q)).trans hP'P.over.symm.le

/-- Let `R → A → T` be ring maps with `A` and `T` free over `R`, and `T` finite and flat over
`A`. Let `𝔮 ⊂ T` be weakly associated to `T ⊗[R] M` and lying over `𝔭 ⊂ R`. Suppose that every
`G ∈ A` not in `𝔮 ∩ A` acts injectively on `A ⊗[R] κ(𝔭)`. Then `𝔭` is weakly associated to `M`.

By Stacks 05E1, `𝔮 ∩ A` is weakly associated to `T ⊗[R] M` as an `A`-module, via some `w`. For
`f ∈ 𝔭` there are `G ∉ 𝔮 ∩ A` and `n` with `G fⁿ w = 0`, and then some `g ∉ 𝔭` has `g fⁿ w = 0`
by `TensorProduct.exists_notMem_smul_eq_zero_of_flat`. So `𝔭` is minimal over `Ann_R(w)`, and
`T ⊗[R] M` is a direct sum of copies of `M`. -/
theorem IsWeaklyAssociatedPrime.comap_of_finite_of_flat {A T : Type*} [CommRing A] [Algebra R A]
    [Module.Free R A] [CommRing T] [Algebra R T] [Algebra A T] [IsScalarTower R A T]
    [Module.Flat A T] [hfin : Module.Finite A T] [Module.Free R T] {Q : Ideal T}
    (hQ : IsWeaklyAssociatedPrime T (T ⊗[R] M) Q) {p : Ideal R} [p.IsPrime]
    (hp : Q.comap (algebraMap R T) = p)
    (hG : ∀ G : A, G ∉ Q.comap (algebraMap A T) →
      ∀ x : A ⊗[R] p.ResidueField, G • x = 0 → x = 0) :
    IsWeaklyAssociatedPrime R M p := by
  obtain ⟨w, hw⟩ := comap_isWeaklyAssociatedPrime_of_finite (R := A) (S := T)
    (M := T ⊗[R] M) hfin Q hQ
  have hQA : (Q.comap (algebraMap A T)).comap (algebraMap R A) = p := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, hp]
  apply IsWeaklyAssociatedPrime.of_tensorProduct_free T
  refine ⟨w, minimalPrimes_of_radical_condition _ p ‹_› ?_ ?_⟩
  · intro r hr
    rw [Submodule.mem_annihilator_span_singleton] at hr
    rw [← hQA, Ideal.mem_comap]
    apply hw.1.2
    rwa [Submodule.mem_annihilator_span_singleton, algebraMap_smul]
  · intro f hf
    have hfA : algebraMap R A f ∈ Q.comap (algebraMap A T) := by
      rwa [← hQA] at hf
    obtain ⟨G, hGQ, n, hGn⟩ := exists_mul_pow_mem_of_mem_minimalPrimes hw hfA
    rw [Submodule.mem_annihilator_span_singleton] at hGn
    have hGw : algebraMap A T G • (f ^ n • w) = 0 := by
      rwa [algebraMap_smul, ← algebraMap_smul A (f ^ n) w, smul_smul, map_pow]
    obtain ⟨g, hgp, hg⟩ :=
      TensorProduct.exists_notMem_smul_eq_zero_of_flat (Module.Free.chooseBasis R A) p (hG G hGQ)
        hGw
    exact ⟨g, hgp, n, by rwa [Submodule.mem_annihilator_span_singleton, mul_smul]⟩

/-- For a field extension `κ / k`, the ring `κ ⊗[k] k(xᵢ : i ∈ σ)` is a domain: it is a
localization of `κ ⊗[k] k[xᵢ] ≅ κ[xᵢ]` at nonzero elements. -/
@[ega "IV 4.3.9" "special case"]
theorem Algebra.TensorProduct.isDomain_fractionRing_mvPolynomial (k κ σ : Type*) [Field k]
    [Field κ] [Algebra k κ] : IsDomain (κ ⊗[k] FractionRing (MvPolynomial σ k)) := by
  let P := MvPolynomial σ k
  let F := FractionRing P
  have e1 : P ⊗[k] κ ≃ₐ[k] MvPolynomial σ κ :=
    (Algebra.TensorProduct.comm k P κ).trans
      ((MvPolynomial.algebraTensorAlgEquiv k κ).restrictScalars k)
  have : IsDomain (P ⊗[k] κ) := e1.toMulEquiv.isDomain
  let _ : Algebra (P ⊗[k] κ) (F ⊗[P] (P ⊗[k] κ)) := Algebra.TensorProduct.rightAlgebra
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid (P ⊗[k] κ) (nonZeroDivisors P))
      (F ⊗[P] (P ⊗[k] κ)) := IsLocalization.tensorRight _ _
  have hle : Algebra.algebraMapSubmonoid (P ⊗[k] κ) (nonZeroDivisors P) ≤
      nonZeroDivisors (P ⊗[k] κ) := by
    rintro _ ⟨a, ha, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h => nonZeroDivisors.ne_zero ha ?_
    refine Algebra.TensorProduct.includeLeft_injective (S := k) (algebraMap k κ).injective ?_
    rwa [map_zero]
  have : IsDomain (F ⊗[P] (P ⊗[k] κ)) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (F ⊗[P] (P ⊗[k] κ)) hle
  exact ((Algebra.TensorProduct.comm k κ F).toMulEquiv.trans
    (Algebra.TensorProduct.cancelBaseChange k P F F κ).toMulEquiv.symm).isDomain

/-- Let `𝔮 ⊂ R ⊗[k] L` be an ideal whose contraction to `R` is the prime `𝔭`. An element of
`R ⊗[k] L` outside `𝔮` has nonzero image in `κ(𝔭) ⊗[k] L`: the kernel of
`R ⊗[k] L → κ(𝔭) ⊗[k] L` is `𝔭 (R ⊗[k] L) ⊆ 𝔮`, as one sees in a `k`-basis of `L`. -/
theorem Algebra.TensorProduct.map_residueField_ne_zero_of_notMem {k R L : Type*} [Field k]
    [CommRing R] [Algebra k R] [CommRing L] [Algebra k L] (p : Ideal R) [p.IsPrime]
    {Q : Ideal (R ⊗[k] L)} (hQ : Q.comap (algebraMap R (R ⊗[k] L)) = p) {G : R ⊗[k] L}
    (hG : G ∉ Q) :
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k R p.ResidueField) (AlgHom.id k L) G ≠ 0 :=
    by
  classical
  let b := Module.Free.chooseBasis k L
  let B := Algebra.TensorProduct.basis R b
  let Bκ := Algebra.TensorProduct.basis p.ResidueField b
  have hrepr : ∀ G : R ⊗[k] L, ∀ i, Bκ.repr (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom k R p.ResidueField) (AlgHom.id k L) G) i =
      algebraMap R p.ResidueField (B.repr G i) := by
    intro G i
    induction G using TensorProduct.inductionOn with
    | tmul r l =>
      simp only [Algebra.TensorProduct.map_tmul, IsScalarTower.coe_toAlgHom', AlgHom.coe_id,
        id_eq, Bκ, B, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply,
        Finsupp.mapRange_apply, smul_eq_mul, map_mul]
      rw [← IsScalarTower.algebraMap_apply]
    | add x y hx hy => simp [hx, hy]
  intro h0
  apply hG
  rw [← B.linearCombination_repr G, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Q.sum_mem fun i _ => ?_
  rw [Algebra.smul_def]
  refine Q.mul_mem_right _ ?_
  rw [← Ideal.mem_comap, hQ, ← Ideal.algebraMap_residueField_eq_zero, ← hrepr, h0, map_zero,
    Finsupp.zero_apply]

/-- Let `𝔮 ⊂ R ⊗[k] L` be an ideal lying over the prime `𝔭 ⊂ R` and suppose that
`κ(𝔭) ⊗[k] L` is a domain. Then every `G ∉ 𝔮` acts injectively on
`(R ⊗[k] L) ⊗[R] κ(𝔭) ≅ κ(𝔭) ⊗[k] L`. -/
theorem Algebra.TensorProduct.eq_zero_of_smul_eq_zero_residueField {k R L : Type*} [Field k]
    [CommRing R] [Algebra k R] [CommRing L] [Algebra k L] (p : Ideal R) [p.IsPrime]
    [IsDomain (p.ResidueField ⊗[k] L)]
    {Q : Ideal (R ⊗[k] L)} (hQ : Q.comap (algebraMap R (R ⊗[k] L)) = p) {G : R ⊗[k] L}
    (hG : G ∉ Q) {x : (R ⊗[k] L) ⊗[R] p.ResidueField} (hx : G • x = 0) : x = 0 := by
  let φ := Algebra.TensorProduct.map (IsScalarTower.toAlgHom k R p.ResidueField) (AlgHom.id k L)
  let Ψ : (R ⊗[k] L) ⊗[R] p.ResidueField ≃+* p.ResidueField ⊗[k] L :=
    (Algebra.TensorProduct.comm R (R ⊗[k] L) p.ResidueField).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange k R p.ResidueField p.ResidueField L).toRingEquiv
  have hΨ : ∀ G : R ⊗[k] L, Ψ (G ⊗ₜ 1) = φ G := by
    intro G
    induction G using TensorProduct.inductionOn with
    | tmul r l => simp [Ψ, φ, Algebra.smul_def]
    | add x y hx hy => rw [add_tmul, map_add, hx, hy, map_add]
  have h1 : φ G * Ψ x = 0 := by
    have e : G • x = (G ⊗ₜ[R] (1 : p.ResidueField)) * x := by
      clear hx
      induction x using TensorProduct.inductionOn with
      | tmul a c => rw [smul_tmul', Algebra.TensorProduct.tmul_mul_tmul, one_mul, smul_eq_mul]
      | add u v hu hv => rw [smul_add, mul_add, hu, hv]
    rw [← hΨ, ← map_mul, ← e, hx, map_zero]
  exact Ψ.injective (((mul_eq_zero.mp h1).resolve_left
    (Algebra.TensorProduct.map_residueField_ne_zero_of_notMem p hQ hG)).trans Ψ.map_zero.symm)

section IntermediateField

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [Algebra k R] {L : IntermediateField k K}

variable (R) in
/-- The base change `R ⊗[k] E → R ⊗[k] K` of the inclusion of an intermediate field. -/
private noncomputable abbrev baseChangeVal (E : IntermediateField L K) :
    R ⊗[k] E →ₐ[R] R ⊗[k] K :=
  Algebra.TensorProduct.lTensor (S := R) R (E.val.restrictScalars k)

/-- `baseChangeVal` is compatible with inclusions of intermediate fields. -/
private theorem baseChangeVal_comp_of_le {E E' : IntermediateField L K} (h : E ≤ E') :
    baseChangeVal R E = (baseChangeVal R E').comp (Algebra.TensorProduct.lTensor (S := R) R
      ((IntermediateField.inclusion h).restrictScalars k)) := by
  ext
  simp

/-- Every element of `R ⊗[k] K` comes from `R ⊗[k] E` for some finite `E / L`. -/
private theorem exists_finiteDimensional_mem_range [Algebra.IsAlgebraic L K] (t : R ⊗[k] K) :
    ∃ E : IntermediateField L K, FiniteDimensional L E ∧ t ∈ (baseChangeVal R E).range := by
  induction t using TensorProduct.inductionOn with
  | tmul r c =>
    refine ⟨IntermediateField.adjoin L {c},
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral c),
      ⟨r ⊗ₜ ⟨c, IntermediateField.mem_adjoin_simple_self L c⟩, by simp⟩⟩
  | add t t' ht ht' =>
    obtain ⟨E, hE, x, rfl⟩ := ht
    obtain ⟨E', hE', x', rfl⟩ := ht'
    refine ⟨E ⊔ E', inferInstance, ?_⟩
    rw [baseChangeVal_comp_of_le (le_sup_left : E ≤ E ⊔ E'),
      baseChangeVal_comp_of_le (le_sup_right : E' ≤ E ⊔ E')]
    exact Subalgebra.add_mem _ ⟨_, rfl⟩ ⟨_, rfl⟩

/-- Every element of `(R ⊗[k] K) ⊗[R] M` comes from `(R ⊗[k] E) ⊗[R] M` for some finite
`E / L`. -/
private theorem exists_finiteDimensional_mem_range_rTensor [Algebra.IsAlgebraic L K]
    (z : (R ⊗[k] K) ⊗[R] M) : ∃ E : IntermediateField L K, FiniteDimensional L E ∧
      z ∈ LinearMap.range (LinearMap.rTensor M (baseChangeVal R E).toLinearMap) := by
  induction z using TensorProduct.inductionOn with
  | tmul t m =>
    obtain ⟨E, hE, x, rfl⟩ := exists_finiteDimensional_mem_range (R := R) (L := L) t
    exact ⟨E, hE, x ⊗ₜ m, rfl⟩
  | add z z' hz hz' =>
    obtain ⟨E, hE, x, rfl⟩ := hz
    obtain ⟨E', hE', x', rfl⟩ := hz'
    refine ⟨E ⊔ E', inferInstance, ?_⟩
    rw [baseChangeVal_comp_of_le (le_sup_left : E ≤ E ⊔ E'),
      baseChangeVal_comp_of_le (le_sup_right : E' ≤ E ⊔ E'),
      AlgHom.comp_toLinearMap, AlgHom.comp_toLinearMap, LinearMap.rTensor_comp,
      LinearMap.rTensor_comp]
    exact Submodule.add_mem _ ⟨_, rfl⟩ ⟨_, rfl⟩

end IntermediateField

/-- Let `T → S` be a flat map of `R`-algebras and `z ∈ T ⊗[R] M`. If `𝔮 ⊂ S` is minimal over
the annihilator of the image of `z` in `S ⊗[R] M`, then `𝔮 ∩ T` is weakly associated to
`T ⊗[R] M`. -/
theorem IsWeaklyAssociatedPrime.comap_of_flat_rTensor {R M T S : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [CommRing T] [Algebra R T] [CommRing S] [Algebra R S]
    [Algebra T S] [IsScalarTower R T S] [Module.Flat T S] (z : T ⊗[R] M) {q : Ideal S}
    (hq : q ∈ Ideal.minimalPrimes
      (S ∙ LinearMap.rTensor M (IsScalarTower.toAlgHom R T S).toLinearMap z).annihilator) :
    IsWeaklyAssociatedPrime T (T ⊗[R] M) (q.comap (algebraMap T S)) := by
  refine ⟨z, Ideal.comap_mem_minimalPrimes_annihilator_of_flat z ?_⟩
  let e := AlgebraTensorModule.cancelBaseChange R T S S M
  have he : ∀ x, e (1 ⊗ₜ x) = LinearMap.rTensor M (IsScalarTower.toAlgHom R T S).toLinearMap x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul t m => simp [e, Algebra.smul_def]
    | add x y hx hy => rw [tmul_add, map_add, hx, hy, map_add]
  rwa [← annihilator_span_singleton_equiv e, he]

/-- **Stacks 0CUB.** Let `K / k` be a field extension, `R` a `k`-algebra and `M` an
`R`-module. If a prime `𝔮 ⊂ R ⊗[k] K` is weakly associated to `M ⊗[k] K`, here written as the
base change `(R ⊗[k] K) ⊗[R] M`, then the prime `𝔭 = 𝔮 ∩ R` it lies over is weakly associated to
`M`. -/
@[stacks 0CUB]
theorem IsWeaklyAssociatedPrime.comap_tensorProduct_field {k K R M : Type*} [Field k]
    [Field K] [Algebra k K] [CommRing R] [Algebra k R] [AddCommGroup M] [Module R M]
    {q : Ideal (R ⊗[k] K)} (hq : IsWeaklyAssociatedPrime (R ⊗[k] K) ((R ⊗[k] K) ⊗[R] M) q) :
    IsWeaklyAssociatedPrime R M (q.comap (algebraMap R (R ⊗[k] K))) := by
  obtain ⟨z, hz⟩ := hq
  have hqp : q.IsPrime := hz.1.1
  set p := q.comap (algebraMap R (R ⊗[k] K))
  have hpp : p.IsPrime := Ideal.comap_isPrime _ q
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k K
  let L := IntermediateField.adjoin k (Set.range ((↑) : s → K))
  have : Algebra.IsAlgebraic L K := hs.isAlgebraic_field
  have hdom : IsDomain (p.ResidueField ⊗[k] L) := by
    have := Algebra.TensorProduct.isDomain_fractionRing_mvPolynomial k p.ResidueField s
    exact (Algebra.TensorProduct.congr (AlgEquiv.refl : p.ResidueField ≃ₐ[k] p.ResidueField)
      hs.1.aevalEquivField).toMulEquiv.symm.isDomain
  obtain ⟨E, hE, z', hz'⟩ := exists_finiteDimensional_mem_range_rTensor (R := R) (M := M) (L := L) z
  let _ : Algebra (R ⊗[k] E) (R ⊗[k] K) := (baseChangeVal R E).toRingHom.toAlgebra
  have : IsScalarTower R (R ⊗[k] E) (R ⊗[k] K) :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := R ⊗[k] E) (A := R ⊗[k] K)
      fun r => ((baseChangeVal R E).commutes r).symm
  have : Module.Flat (R ⊗[k] E) (R ⊗[k] K) := RingHom.flat_algebraMap_iff.mp
    (RingHom.Flat.lTensor (S := R) R (RingHom.Flat.of_isField (Field.toIsField _) _))
  let gLE : L →ₐ[k] E := IsScalarTower.toAlgHom k L E
  let φ : R ⊗[k] L →ₐ[R] R ⊗[k] E := Algebra.TensorProduct.lTensor (S := R) R gLE
  let _ : Algebra (R ⊗[k] L) (R ⊗[k] E) := φ.toRingHom.toAlgebra
  have : IsScalarTower R (R ⊗[k] L) (R ⊗[k] E) :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := R ⊗[k] L) (A := R ⊗[k] E)
      fun r => (φ.commutes r).symm
  have : Module.Flat (R ⊗[k] L) (R ⊗[k] E) :=
    (RingHom.flat_algebraMap_iff (R := R ⊗[k] L) (S := R ⊗[k] E)).mp
    (RingHom.Flat.lTensor (S := R) R (RingHom.Flat.of_isField (Field.toIsField _) _))
  have hfinLE := (RingHom.finite_algebraMap (A := R ⊗[k] L) (B := R ⊗[k] E)).mp
    (RingHom.Finite.tensorProductMap (f := AlgHom.id k R) (g := gLE) (AlgHom.Finite.id k R)
      (RingHom.finite_algebraMap.mpr hE))
  have hQ := IsWeaklyAssociatedPrime.comap_of_flat_rTensor (S := R ⊗[k] K) z' (q := q)
    (hz' ▸ hz)
  have hQp : (q.comap (algebraMap (R ⊗[k] E) (R ⊗[k] K))).comap (algebraMap R (R ⊗[k] E)) = p := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  refine IsWeaklyAssociatedPrime.comap_of_finite_of_flat (R := R) (M := M) (A := R ⊗[k] L)
    (T := R ⊗[k] E) (hfin := hfinLE) hQ hQp fun G hG x hx =>
      Algebra.TensorProduct.eq_zero_of_smul_eq_zero_residueField p
        (by rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, hQp]) hG hx

end
