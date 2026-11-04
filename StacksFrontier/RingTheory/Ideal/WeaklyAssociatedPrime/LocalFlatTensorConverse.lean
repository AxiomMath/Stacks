module

public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.ProjectiveClosedFibre

/-!
# The converse implication of Stacks 05IH at a point, for a flat module

Let `R → B` be a local homomorphism of local rings whose closed fibre ring `B / 𝔪_R B` is
Noetherian, let `N` be a `B`-module which is flat over `R`, and let `M` be an `R`-module. This
file proves that if `𝔪_R` is weakly associated to `M` and `𝔪_B` is an associated prime — in the
strict sense of [Stacks, Tag 00LA] — of the closed fibre `N / 𝔪_R N`, then `𝔪_B` is weakly
associated to `N ⊗_R M`.

This is the implication `⟸` of [Stacks, Tag 05IH] read on the stalks at a point and its image.
No finiteness of `N` and no projectivity over `R` is needed: the maximal ideal of a local ring
is maximal among the primes associated to any module, so the étale-local reduction the source
uses for [Stacks, Tag 05IG] — whose only purpose there is to make the fibre prime maximal among
the associated primes of the fibre and the module projective — has nothing to do.

## The argument

Choose `y : M` whose annihilator `I` has radical `𝔪_R`, an element `ν : N` whose image in the
closed fibre is annihilated exactly by `𝔪_B`, and elements `g₁, …, gₙ` of `B` generating `𝔪_B`
modulo `𝔪_R B` (the closed fibre ring is Noetherian). Each `gᵢ ν` lies in `J N` for one finitely
generated ideal `J ⊆ 𝔪_R`, and some power of `J` lies in `I`; for the least such power `J^k`,
pick `c ∈ J^{k-1}` outside `I`. Then `z = ν ⊗ c y` is killed by every `gᵢ` (as `cJ ⊆ I`) and by
a power of every element of `𝔪_R` (as `𝔪_R` is the radical of `I`), so the radical of its
annihilator in `B` is `𝔪_B`. It is nonzero: `R (c y) ≅ R / K` with `K = (I : c)` a proper ideal,
`N ⊗_R R (c y) ⊆ N ⊗_R M` by flatness, and `ν ∉ K N ⊆ 𝔪_R N`.

## Main results

* `Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_maximalIdeal_tensorProduct_of_closedFibre`

## References

* [Stacks Project, Tag 05IH](https://stacks.math.columbia.edu/tag/05IH)
* [Stacks Project, Tag 05IG](https://stacks.math.columbia.edu/tag/05IG)
-/

@[expose] public section

open TensorProduct IsLocalRing

namespace Stacks.WeaklyAssociatedPrimes

/-- An element of `I • ⊤` already lies in `J • ⊤` for a finitely generated ideal `J ≤ I`. -/
theorem exists_fg_le_mem_smul_top {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    {I : Ideal R} {x : N} (hx : x ∈ I • (⊤ : Submodule R N)) :
    ∃ J : Ideal R, Submodule.FG J ∧ J ≤ I ∧ x ∈ J • (⊤ : Submodule R N) := by
  induction hx using Submodule.smul_induction_on' with
  | smul r hr n _ =>
      exact ⟨Ideal.span {r}, Submodule.fg_span_singleton r,
        (Ideal.span_singleton_le_iff_mem I).mpr hr,
        Submodule.smul_mem_smul (Ideal.mem_span_singleton_self r) Submodule.mem_top⟩
  | add x _ y _ hx hy =>
      obtain ⟨J₁, hJ₁, hJ₁I, hx₁⟩ := hx
      obtain ⟨J₂, hJ₂, hJ₂I, hy₂⟩ := hy
      exact ⟨J₁ ⊔ J₂, hJ₁.sup hJ₂, sup_le hJ₁I hJ₂I,
        Submodule.add_mem _ (Submodule.smul_mono_left le_sup_left hx₁)
          (Submodule.smul_mono_left le_sup_right hy₂)⟩

/-- Let `R → B` be a local homomorphism of local rings with Noetherian closed fibre ring
`B / 𝔪_R B`, let `N` be a `B`-module flat over `R` and let `M` be an `R`-module. If `𝔪_R` is weakly
associated to `M` and `𝔪_B` is associated to the closed fibre `N / 𝔪_R N`, then `𝔪_B` is weakly
associated to `N ⊗_R M`: the converse implication of Stacks Tag 05IH on stalks. -/
theorem isWeaklyAssociatedPrime_maximalIdeal_tensorProduct_of_closedFibre
    {R B : Type*} [CommRing R] [CommRing B] [IsLocalRing R] [IsLocalRing B]
    [Algebra R B] [IsLocalHom (algebraMap R B)]
    {N : Type*} [AddCommGroup N] [Module B N] [Module R N] [IsScalarTower R B N]
    [Module.Flat R N] {M : Type*} [AddCommGroup M] [Module R M]
    [IsNoetherianRing (B ⧸ Ideal.map (algebraMap R B) (maximalIdeal R))]
    (hM : IsWeaklyAssociatedPrime R M (maximalIdeal R))
    (hN : IsAssociatedPrimeStacks B
      (N ⧸ Ideal.map (algebraMap R B) (maximalIdeal R) • (⊤ : Submodule B N))
      (maximalIdeal B)) :
    IsWeaklyAssociatedPrime B (N ⊗[R] M) (maximalIdeal B) := by
  classical
  set 𝔪 : Ideal R := maximalIdeal R with h𝔪
  -- an element of `M` whose annihilator has radical `𝔪`
  obtain ⟨y, hy⟩ := weaklyAssociated_maximalIdeal_iff_exists_radical_eq.mp hM
  set I : Ideal R := annihilatorOfElem_semiring (R := R) y with hI
  have hmemI : ∀ a : R, a ∈ I ↔ a • y = 0 := mem_annihilatorOfElem_semiring_iff y
  -- the witness of association on the closed fibre
  obtain ⟨-, ν₀, hν₀⟩ := hN
  obtain ⟨ν, rfl⟩ := Submodule.Quotient.mk_surjective _ ν₀
  have hcolon : ∀ b : B, b ∈ maximalIdeal B ↔
      b • ν ∈ Ideal.map (algebraMap R B) 𝔪 • (⊤ : Submodule B N) := by
    intro b
    rw [← hν₀, Submodule.mem_colon_span_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
  have hνnot : ν ∉ 𝔪 • (⊤ : Submodule R N) := by
    intro h
    rw [mem_smul_top_iff_mem_map_smul_top (S := B)] at h
    exact (maximalIdeal.isMaximal B).ne_top (Ideal.eq_top_iff_one _ |>.mpr
      ((hcolon 1).mpr (by rwa [one_smul])))
  -- generators of `𝔪_B` modulo `𝔪_R B`
  have hle : Ideal.map (algebraMap R B) 𝔪 ≤ maximalIdeal B :=
    Ideal.map_le_iff_le_comap.mpr (le_of_eq (maximalIdeal_comap (algebraMap R B)).symm)
  obtain ⟨n, g, hg⟩ := exists_eq_sup_span_range_of_isNoetherianRing_quotient hle
  have hgmem : ∀ i, g i ∈ maximalIdeal B := fun i => by
    rw [hg]; exact Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
  have hgν : ∀ i, g i • ν ∈ 𝔪 • (⊤ : Submodule R N) := fun i => by
    rw [mem_smul_top_iff_mem_map_smul_top (S := B)]
    exact (hcolon (g i)).mp (hgmem i)
  -- one finitely generated `J ≤ 𝔪` serving all `gᵢ`
  choose J hJfg hJle hJmem using fun i => exists_fg_le_mem_smul_top (hgν i)
  set J₀ : Ideal R := Finset.univ.sup J with hJ₀
  have hJ₀fg : Submodule.FG J₀ := by
    rw [hJ₀]
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty => exact Submodule.fg_bot
    | insert a s _ ih => rw [Finset.sup_insert]; exact (hJfg a).sup ih
  have hJ₀le : J₀ ≤ 𝔪 := Finset.sup_le fun i _ => hJle i
  have hgJ₀ : ∀ i, g i • ν ∈ J₀ • (⊤ : Submodule R N) := fun i =>
    Submodule.smul_mono_left (Finset.le_sup (f := J) (Finset.mem_univ i)) (hJmem i)
  -- `c ∈ J₀^{k-1} \ I` with `c J₀ ⊆ I`
  have hJ₀rad : J₀ ≤ I.radical := hy ▸ hJ₀le
  have hex : ∃ k, J₀ ^ k ≤ I := Ideal.exists_pow_le_of_le_radical_of_fg hJ₀rad hJ₀fg
  set k := Nat.find hex with hk
  have hIne : I ≠ ⊤ := by
    intro h
    have : I.radical = ⊤ := by rw [h, Ideal.radical_top]
    exact (maximalIdeal.isMaximal R).ne_top (hy.symm.trans this)
  have hk0 : k ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [← hk, h0, pow_zero, Ideal.one_eq_top, top_le_iff] at this
    exact hIne this
  obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hnot : ¬ J₀ ^ k' ≤ I := Nat.find_min hex (by omega)
  obtain ⟨c, hcJ, hcI⟩ := Set.not_subset.mp hnot
  have hcJI : ∀ a ∈ J₀, a * c ∈ I := fun a ha =>
    Nat.find_spec hex (by rw [← hk, hk', pow_succ']; exact Ideal.mul_mem_mul ha hcJ)
  -- the element `z = ν ⊗ c y`
  set z : N ⊗[R] M := ν ⊗ₜ[R] (c • y) with hz
  have hJkill : ∀ x ∈ J₀ • (⊤ : Submodule R N), x ⊗ₜ[R] (c • y) = 0 := by
    intro x hx
    induction hx using Submodule.smul_induction_on' with
    | smul a ha m _ =>
        rw [TensorProduct.smul_tmul, smul_smul, (hmemI _).mp (hcJI a ha), tmul_zero]
    | add x _ x' _ hx hx' => rw [add_tmul, hx, hx', add_zero]
  have hgz : ∀ i, g i • z = 0 := fun i => by
    rw [hz, TensorProduct.smul_tmul']
    exact hJkill _ (hgJ₀ i)
  have h𝔪z : ∀ a ∈ 𝔪, ∃ j : ℕ, (algebraMap R B a) ^ j • z = 0 := by
    intro a ha
    rw [h𝔪, ← hy] at ha
    obtain ⟨j, hj⟩ := ha
    refine ⟨j, ?_⟩
    rw [← map_pow, algebraMap_smul, hz, TensorProduct.smul_tmul', TensorProduct.smul_tmul,
      smul_smul, mul_comm, ← smul_smul,
      (hmemI _).mp hj, smul_zero, tmul_zero]
  -- `z ≠ 0`, by flatness
  have hz0 : z ≠ 0 := by
    intro hz0
    set w : M := c • y with hw
    let ι : (R ∙ w) →ₗ[R] M := (R ∙ w).subtype
    have hinj : Function.Injective (ι.lTensor N) :=
      Module.Flat.lTensor_preserves_injective_linearMap ι (Submodule.injective_subtype _)
    have h1 : ι.lTensor N (ν ⊗ₜ[R] ⟨w, Submodule.mem_span_singleton_self w⟩) = 0 := by
      simpa [ι, hz] using hz0
    have h2 : (ν ⊗ₜ[R] (⟨w, Submodule.mem_span_singleton_self w⟩ : R ∙ w)) = 0 :=
      hinj (h1.trans (map_zero _).symm)
    set K : Ideal R := Ideal.torsionOf R M w with hK
    let e := Ideal.quotTorsionOfEquivSpanSingleton R M w
    have he1 : e (Submodule.Quotient.mk 1) = ⟨w, Submodule.mem_span_singleton_self w⟩ := by
      rw [Ideal.quotTorsionOfEquivSpanSingleton_apply_mk, one_smul]
    have h3 : (e.symm.lTensor N) (ν ⊗ₜ[R] (⟨w, Submodule.mem_span_singleton_self w⟩ : R ∙ w)) =
        ν ⊗ₜ[R] (Ideal.Quotient.mk K 1) := by
      rw [LinearEquiv.lTensor_tmul, ← he1, LinearEquiv.symm_apply_apply]
      rfl
    have h4 : (ν ⊗ₜ[R] (Ideal.Quotient.mk K 1) : N ⊗[R] (R ⧸ K)) = 0 := by
      rw [← h3, h2, map_zero]
    have h5 := congrArg (tensorQuotEquivQuotSMul N K) h4
    rw [tensorQuotEquivQuotSMul_tmul_mk, one_smul, map_zero, Submodule.Quotient.mk_eq_zero] at h5
    have hKle : K ≤ 𝔪 := by
      apply le_maximalIdeal
      intro htop
      apply hcI
      show c ∈ I
      rw [hmemI]
      have : (1 : R) ∈ K := htop ▸ Submodule.mem_top
      simpa [hK, Ideal.mem_torsionOf_iff] using this
    exact hνnot (Submodule.smul_mono_left hKle h5)
  -- conclusion
  show WeaklyAssociated (maximalIdeal B) (N ⊗[R] M)
  refine weaklyAssociated_maximalIdeal_iff_exists_radical_eq.mpr ⟨z, le_antisymm ?_ ?_⟩
  · have hne : annihilatorOfElem_semiring (R := B) z ≠ ⊤ := by
      intro h
      apply hz0
      have : (1 : B) ∈ annihilatorOfElem_semiring (R := B) z := h ▸ Submodule.mem_top
      simpa using (mem_annihilatorOfElem_semiring_iff z 1).mp this
    exact (Ideal.radical_mono (le_maximalIdeal hne)).trans_eq
      (maximalIdeal.isMaximal B).isPrime.radical
  · rw [hg]
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      obtain ⟨j, hj⟩ := h𝔪z a ha
      exact ⟨j, (mem_annihilatorOfElem_semiring_iff z _).mpr hj⟩
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact Ideal.le_radical ((mem_annihilatorOfElem_semiring_iff z _).mpr (hgz i))

end Stacks.WeaklyAssociatedPrimes

end
