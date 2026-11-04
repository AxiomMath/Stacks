module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.TensorProduct.Finite
public import StacksFrontier.Algebra.Module.ContentIdeal
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.HenselizationTensorPrime
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.ZeroLocusOnLocalSpectrum
public import StacksFrontier.RingTheory.Flat.ContentIdealFromColimitFree
public import StacksFrontier.RingTheory.Henselian.Henselization.Basic
public import StacksFrontier.RingTheory.Henselian.HenselizationMinimalPrimes
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties
public import StacksFrontier.RingTheory.Henselian.Quotient

/-!
# Separatedness of a flat finite module over a local domain

Let `A` be a local domain which is not a field, let `A → B` be a local homomorphism which is
essentially of finite type, and let `N` be a finite `B`-module which is flat over `A`. This
file proves that `N` is separated for the topology defined by the submodules `aN`, `a` a
nonzero element of `A`: their intersection is zero.

This is the separatedness step of the second paragraph of Claim 2 in the proof of Stacks
05U9, with `A`, `B`, `N` standing for the quotients `A/𝔭`, `B/𝔭B`, `N/𝔭N` of the source.

The argument of the source is followed. Let `A^h` be a henselization of `A` and let `B'` be
the localization of `A^h ⊗_A B` at the kernel of the canonical map to the residue field of
`B`; this is a prime lying over the maximal ideals of both `A^h` and `B`, so `B → B'` is a
flat local homomorphism of local rings, hence faithfully flat, and `A^h → B'` is a local
homomorphism essentially of finite type. Setting `N' = B' ⊗_B N`, the module `N'` is finite
over `B'` and flat over `A^h`, so its elements have content ideals in `A^h` by Stacks 05U7
and Stacks 0ASD, which is
`Module.exists_isContentIdeal_of_colimit_free_presentation`. The intersection of the ideals
`a A^h`, for `a` a nonzero element of `A`, is zero, by Stacks 0ATA applied to `A^h ⧸ 𝔮` for
each minimal prime `𝔮` of the reduced ring `A^h`; so the intersection of the `a N'` is zero,
and `N → N'` is injective.

## Main results

* `Stacks.ResidueFibre.iInf_span_eq_bot_of_indEtale`: the intersection of the nonzero
  principal ideals extended from a local domain which is not a field is zero in any flat
  ind-étale local extension. This is Stacks 0ATA together with the zero-dimensionality of
  the generic fibre of such an extension.
* `Stacks.ResidueFibre.iInf_smul_top_eq_bot`: the separatedness.
* `Stacks.ResidueFibre.eq_zero_of_forall_mem_smul_top`: the form in which Claim 2 of the
  proof of Stacks 05U9 uses it, for the reduction of a finite module modulo a prime of the
  base other than the maximal ideal.

## Implementation notes

The module `N'` is built as `B' ⊗_{A^h ⊗_A B} ((A^h ⊗_A B) ⊗_B N)` rather than as
`B' ⊗_B N`, because in that shape its flatness over `A^h` is a single base change along the
flat localization `A^h ⊗_A B → B'` of a module which is flat over `A^h` by the pushout
identification `(A^h ⊗_A B) ⊗_B N = A^h ⊗_A N`. Its injectivity receives `B' ⊗_B N`
through `TensorProduct.AlgebraTensorModule.cancelBaseChange`.

The minimal primes of `A^h` are the primes lying over the minimal prime `(0)` of `A`,
because `A → A^h` is flat with zero-dimensional fibres; this is what makes every nonzero
prime of `A^h ⧸ 𝔮` meet `A` nontrivially, which is the hypothesis of Stacks 0ATA.

## References

* [Stacks Project, Tag 05U7](https://stacks.math.columbia.edu/tag/05U7)
* [Stacks Project, Tag 0ASD](https://stacks.math.columbia.edu/tag/0ASD)
* [Stacks Project, Tag 0ATA](https://stacks.math.columbia.edu/tag/0ATA)
* [Stacks Project, Tag 05U9](https://stacks.math.columbia.edu/tag/05U9)
-/

@[expose] public section

universe u v w

open IsLocalRing TensorProduct

namespace Stacks.ResidueFibre

/-- **Stacks 0ATA, repackaged.** In a local domain `S` which is not a field, receiving an
injection from a domain `R` in such a way that every nonzero prime of `S` contains a nonzero
element of `R`, the nonzero principal ideals extended from `R` intersect in zero.

The family of those ideals is multiplicatively closed, consists of finitely generated
ideals, and its zero loci cover the complement of the generic point, which is exactly the
hypothesis of Stacks 0ATA. -/
theorem iInf_span_algebraMap_eq_bot
    {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [IsLocalRing S] [Algebra R S] (hS : ¬ IsField S)
    (hinj : Function.Injective (algebraMap R S))
    (hpr : ∀ p : PrimeSpectrum S, p.asIdeal ≠ ⊥ →
      ∃ r : R, r ≠ 0 ∧ algebraMap R S r ∈ p.asIdeal) :
    (⨅ r : {r : R // r ≠ 0}, Ideal.span {algebraMap R S r.val}) = ⊥ := by
  let J : {r : R // r ≠ 0} → Ideal S := fun r => Ideal.span {algebraMap R S r.val}
  have hfg : ∀ I ∈ Set.range J, I.FG := by
    rintro I ⟨r, rfl⟩
    exact Submodule.fg_span_singleton _
  have hmul : ∀ I ∈ Set.range J, ∀ K ∈ Set.range J, I * K ∈ Set.range J := by
    rintro I ⟨r, rfl⟩ K ⟨s, rfl⟩
    refine ⟨⟨r.val * s.val, mul_ne_zero r.property s.property⟩, ?_⟩
    simp [J, map_mul, Ideal.span_singleton_mul_span_singleton]
  have hcover : (⋃ I ∈ Set.range J, PrimeSpectrum.zeroLocus (I : Set S)) =
      {p : PrimeSpectrum S | p.asIdeal ≠ ⊥} := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨I, ⟨r, rfl⟩, hr⟩ hp
      have hrp : algebraMap R S r.val ∈ p.asIdeal :=
        (PrimeSpectrum.mem_zeroLocus p _).mp hr (Ideal.subset_span (Set.mem_singleton _))
      have hzero : algebraMap R S r.val = 0 := by simpa [hp] using hrp
      exact r.property (hinj (by simpa using hzero))
    · intro hp
      obtain ⟨r, hr, hrp⟩ := hpr p hp
      refine ⟨J ⟨r, hr⟩, ⟨⟨r, hr⟩, rfl⟩, ?_⟩
      rw [PrimeSpectrum.mem_zeroLocus]
      exact Ideal.span_le.mpr (by simpa using hrp)
  simpa only [sInf_range] using
    PrimeSpectrum.sInf_eq_bot_of_iUnion_zeroLocus_eq_compl_genericPoint hS (Set.range J)
      hfg hmul hcover

/-- **The nonzero principal ideals of a local domain which is not a field extend to ideals
with zero intersection in any flat ind-étale local extension.**

The extension is reduced, so it suffices to see that the extended element lies in every
minimal prime `𝔮`. The quotient by a minimal prime is a local domain into which `R` injects,
because flatness with zero-dimensional fibres makes the minimal primes exactly the primes
over `(0)`; for the same reason every prime strictly above `𝔮` contracts to a nonzero prime
of `R`, which is the hypothesis of Stacks 0ATA. -/
theorem iInf_span_eq_bot_of_indEtale
    {R Rh : Type u} [CommRing R] [IsDomain R] [IsLocalRing R] (hR : ¬ IsField R)
    [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh] [IsLocalHom (algebraMap R Rh)]
    [Module.Flat R Rh] (hind : StacksDraft.IndEtale R Rh) :
    (⨅ r : {r : R // r ≠ 0}, Ideal.span {algebraMap R Rh r.val}) = ⊥ := by
  have hred : IsReduced Rh := isReduced_of_ind_etale (StacksDraft.indEtale_iff.mp hind)
  have hdim : ∀ (p : Ideal R) [p.IsPrime], Ring.KrullDimLE 0 (p.Fiber Rh) :=
    fun p _ => (StacksDraft.fiber_reduced_and_krullDimLE_zero hind p).2
  have hbotmin : (⊥ : Ideal R) ∈ minimalPrimes R :=
    ⟨⟨Ideal.isPrime_bot, le_rfl⟩, fun J _ _ => bot_le⟩
  have hunder : ∀ q ∈ minimalPrimes Rh, q.under R = ⊥ := by
    intro q hq
    obtain ⟨-, p, hp, hlo⟩ :=
      (StacksDraft.minimalPrime_iff_of_flat_of_fiber_krullDimLE_zero hdim q).mp hq
    have hpbot : p = ⊥ := le_bot_iff.mp (hp.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le)
    exact hlo.over.symm.trans hpbot
  have key : ∀ q ∈ minimalPrimes Rh,
      ∀ x ∈ ⨅ r : {r : R // r ≠ 0}, Ideal.span {algebraMap R Rh r.val}, x ∈ q := by
    intro q hq x hx
    have hqp : q.IsPrime := hq.1.1
    let S := Rh ⧸ q
    have : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hqp.ne_top
    let : IsLocalRing S :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
    let : IsLocalHom (Ideal.Quotient.mk q) :=
      IsLocalHom.of_surjective (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
    have hlocRS : IsLocalHom (algebraMap R S) := by
      rw [IsScalarTower.algebraMap_eq R Rh S]
      infer_instance
    have hinj : Function.Injective (algebraMap R S) := by
      rw [injective_iff_map_eq_zero]
      intro r hr
      have : r ∈ q.under R := by
        rw [Ideal.mem_under]
        rw [IsScalarTower.algebraMap_apply R Rh S] at hr
        exact Ideal.Quotient.eq_zero_iff_mem.mp hr
      simpa [hunder q hq] using this
    have hSfield : ¬ IsField S := by
      intro hfield
      have hmS : IsLocalRing.maximalIdeal S = ⊥ :=
        IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
      have hmR : IsLocalRing.maximalIdeal R ≠ ⊥ := fun h =>
        hR (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmR
      refine ha0 (hinj ?_)
      rw [map_zero]
      have : algebraMap R S a ∈ IsLocalRing.maximalIdeal S := by
        rw [← IsLocalRing.maximalIdeal_comap (algebraMap R S)] at ha
        exact ha
      simpa [hmS] using this
    have hpr : ∀ P : PrimeSpectrum S, P.asIdeal ≠ ⊥ →
        ∃ r : R, r ≠ 0 ∧ algebraMap R S r ∈ P.asIdeal := by
      intro P hP
      by_contra hcon
      push Not at hcon
      let q' : Ideal Rh := P.asIdeal.comap (Ideal.Quotient.mk q)
      have hq'p : q'.IsPrime := Ideal.comap_isPrime _ _
      have hqq' : q ≤ q' := by
        intro y hy
        show Ideal.Quotient.mk q y ∈ P.asIdeal
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hy]
        exact P.asIdeal.zero_mem
      have hq'under : q'.under R = ⊥ := by
        apply le_bot_iff.mp
        intro r hr
        rw [Ideal.mem_under] at hr
        by_contra hr0
        refine hcon r hr0 ?_
        rw [IsScalarTower.algebraMap_apply R Rh S]
        exact hr
      have hq'min : q' ∈ minimalPrimes Rh :=
        (StacksDraft.minimalPrime_iff_of_flat_of_fiber_krullDimLE_zero hdim q').mpr
          ⟨hq'p, ⊥, hbotmin, ⟨hq'under.symm⟩⟩
      have hqeq : q' = q := le_antisymm (hq'min.2 ⟨hqp, bot_le⟩ hqq') hqq'
      apply hP
      apply le_bot_iff.mp
      intro z hz
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      have hy : y ∈ q' := hz
      rw [hqeq] at hy
      simpa using Ideal.Quotient.eq_zero_iff_mem.mpr hy
    have hbot := iInf_span_algebraMap_eq_bot (R := R) (S := S) hSfield hinj hpr
    have hmem : Ideal.Quotient.mk q x ∈
        ⨅ r : {r : R // r ≠ 0}, Ideal.span {algebraMap R S r.val} := by
      refine Ideal.mem_iInf.mpr fun r => ?_
      have hxr : x ∈ Ideal.span {algebraMap R Rh r.val} := Ideal.mem_iInf.mp hx r
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hxr
      refine Ideal.mem_span_singleton'.mpr ⟨Ideal.Quotient.mk q c, ?_⟩
      rw [IsScalarTower.algebraMap_apply R Rh S, Ideal.Quotient.algebraMap_eq,
        ← map_mul, hc]
    rw [hbot] at hmem
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hmem)
  apply le_bot_iff.mp
  intro x hx
  have hnil : x ∈ nilradical Rh := by
    rw [nilradical_eq_sInf, Ideal.mem_sInf]
    intro P hP
    have : P.IsPrime := hP
    obtain ⟨q, hq, hqP⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal Rh)) (J := P) bot_le
    exact hqP (key q hq x hx)
  simpa using IsReduced.eq_zero x (mem_nilradical.mp hnil)

/-- Content ideals turn a family of ideals with zero intersection into a family of
submodules with zero intersection. -/
theorem iInf_smul_top_eq_bot_of_isContentIdeal
    {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (hcontent : ∀ x : M, ∃ I : Ideal R, IsContentIdeal x I)
    (I : ι → Ideal R) (hI : iInf I = ⊥) :
    (⨅ i, I i • (⊤ : Submodule R M)) = ⊥ := by
  apply bot_unique
  intro x hx
  obtain ⟨J, hJ⟩ := hcontent x
  have hJI : J ≤ iInf I := le_iInf fun i =>
    hJ.le_of_mem_smul_top ((Submodule.mem_iInf _).mp hx i)
  have hJ0 : J = ⊥ := bot_unique (hI ▸ hJI)
  simpa [hJ0] using hJ.mem_smul_top

section BaseChange

open TensorProduct.AlgebraTensorModule in
/-- The associativity isomorphism of a double base change commutes with tensoring a map on
the left. -/
private theorem assoc_comp_lTensor
    {R C D P X Y : Type*} [CommRing R] [CommRing C] [CommRing D]
    [Algebra R C] [Algebra C D] [Algebra R D] [IsScalarTower R C D]
    [AddCommGroup P] [Module R P] [Module C P] [IsScalarTower R C P]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (u : X →ₗ[R] Y) :
    (assoc R C C D P Y).toLinearMap ∘ₗ lTensor C (D ⊗[C] P) u =
      LinearMap.lTensor D (lTensor C P u) ∘ₗ (assoc R C C D P X).toLinearMap := by
  ext
  rfl

open TensorProduct.AlgebraTensorModule in
/-- Tensoring a map with a double base change is tensoring it twice. -/
private theorem lTensor_baseChange_injective_iff
    {R C D P X Y : Type*} [CommRing R] [CommRing C] [CommRing D]
    [Algebra R C] [Algebra C D] [Algebra R D] [IsScalarTower R C D]
    [AddCommGroup P] [Module R P] [Module C P] [IsScalarTower R C P]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (u : X →ₗ[R] Y) :
    Function.Injective (LinearMap.lTensor (D ⊗[C] P) u) ↔
      Function.Injective (LinearMap.lTensor D (lTensor C P u)) := by
  rw [← coe_lTensor (A := C),
    ← EquivLike.comp_injective _ (assoc R C C D P Y),
    ← LinearEquiv.coe_coe, ← LinearMap.coe_comp, assoc_comp_lTensor,
    LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.injective_comp]

/-- The base change of an `R`-flat module along a flat ring map out of `C` stays `R`-flat. -/
theorem flat_baseChange_of_flat
    {R C D P : Type*} [CommRing R] [CommRing C] [CommRing D]
    [Algebra R C] [Algebra C D] [Algebra R D] [IsScalarTower R C D]
    [AddCommGroup P] [Module R P] [Module C P] [IsScalarTower R C P]
    [Module.Flat R P] [Module.Flat C D] :
    Module.Flat R (D ⊗[C] P) := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro X Y _ _ _ _ u hu
  rw [lTensor_baseChange_injective_iff]
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := D) _
    (Module.Flat.lTensor_preserves_injective_linearMap (M := P) u hu)

end BaseChange

section Separation

/-- **The separation, from an injection into a module with content ideals.** If `N` embeds
additively into a module `N'` over a flat ind-étale local extension `Ah` of the local domain
`A`, compatibly with the actions, and the elements of `N'` have content ideals, then the
submodules `aN` of `N`, for `a` a nonzero element of `A`, intersect in zero. -/
theorem iInf_smul_top_eq_bot_of_injective
    {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] (hA : ¬ IsField A)
    {Ah : Type u} [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsLocalHom (algebraMap A Ah)] [Module.Flat A Ah]
    (hind : StacksDraft.IndEtale A Ah)
    {N N' : Type*} [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module Ah N']
    (hcontent : ∀ x : N', ∃ I : Ideal Ah, IsContentIdeal x I)
    (ι : N →+ N') (hι : Function.Injective ι)
    (hsmul : ∀ (a : A) (n : N), ι (a • n) = (algebraMap A Ah a) • ι n) :
    (⨅ a : {a : A // a ≠ 0}, Ideal.span {(a : A)} • (⊤ : Submodule A N)) = ⊥ := by
  have hbot : (⨅ a : {a : A // a ≠ 0},
      (Ideal.span {algebraMap A Ah (a : A)}) • (⊤ : Submodule Ah N')) = ⊥ :=
    iInf_smul_top_eq_bot_of_isContentIdeal hcontent _
      (iInf_span_eq_bot_of_indEtale hA hind)
  apply bot_unique
  intro x hx
  have hmem : ι x ∈ ⨅ a : {a : A // a ≠ 0},
      (Ideal.span {algebraMap A Ah (a : A)}) • (⊤ : Submodule Ah N') := by
    refine (Submodule.mem_iInf _).mpr fun a => ?_
    have hxa : x ∈ Ideal.span {(a : A)} • (⊤ : Submodule A N) :=
      (Submodule.mem_iInf _).mp hx a
    refine Submodule.smul_induction_on hxa ?_ ?_
    · intro c hc n _
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      rw [show (d * (a : A)) • n = (a : A) • (d • n) by rw [mul_comm, mul_smul], hsmul]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
    · intro y z hy hz
      rw [map_add]
      exact Submodule.add_mem _ hy hz
  rw [hbot] at hmem
  have hzero : ι x = 0 := by simpa using hmem
  have : x = 0 := hι (by rw [hzero, map_zero])
  simpa using this

end Separation

section Pushout

/-- A ring map into `C` that pulls `P` back to the maximal ideal stays local after composing
with the localization of `C` at `P`. -/
private theorem isLocalHom_localization_atPrime
    {R C : Type*} [CommRing R] [IsLocalRing R] [CommRing C] [Algebra R C]
    (P : Ideal C) [P.IsPrime]
    (h : P.comap (algebraMap R C) = IsLocalRing.maximalIdeal R) :
    IsLocalHom (algebraMap R (Localization.AtPrime P)) := by
  refine ⟨fun r hr => ?_⟩
  by_contra hru
  have hrP : algebraMap R C r ∈ P := by
    rw [← Ideal.mem_comap, h]
    exact hru
  have hmem := (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (Localization.AtPrime P) P _).mpr hrP
  rw [← IsScalarTower.algebraMap_apply R C (Localization.AtPrime P)] at hmem
  exact hmem hr

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A]
variable {Ah : Type u} [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
  [HenselianLocalRing Ah] [IsLocalHom (algebraMap A Ah)] [Module.Flat A Ah]
variable {B : Type v} [CommRing B] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]
variable {C : Type (max u v)} [CommRing C] [Algebra Ah C] [Algebra B C] [Algebra A C]
  [IsScalarTower A Ah C] [IsScalarTower A B C] [Module.Flat B C]
  [Algebra.EssFiniteType Ah C]
variable {N : Type w} [AddCommGroup N] [Module A N] [Module B N]
  [IsScalarTower A B N] [Module.Finite B N] [Module.Flat A N]

omit [IsLocalHom (algebraMap A B)] in
/-- **The separatedness of Claim 2 in the proof of Stacks 05U9**, with the henselization
presented abstractly: `C` is a pushout of a flat ind-étale local extension `Ah` of the local
domain `A` along `A → B`, and `P` is a prime of `C` lying over the maximal ideals of `B` and
of `Ah`.

`P` lying over the maximal ideal of `B` makes `B → C_P` a flat local homomorphism of local
rings, hence faithfully flat, so `N` injects into `N' = C_P ⊗_C (C ⊗_B N)`; `P` lying over
the maximal ideal of `Ah` makes `Ah → C_P` local, and it is essentially of finite type as a
localization of `C`. Finally `N'` is finite over `C_P` and flat over `Ah`, so its elements have
content ideals by `Module.exists_isContentIdeal_of_colimit_free_presentation` and
`iInf_smul_top_eq_bot_of_injective` concludes. -/
theorem iInf_smul_top_eq_bot_of_isPushout
    (hA : ¬ IsField A) (hind : StacksDraft.IndEtale A Ah)
    (hpush : Algebra.IsPushout A Ah B C)
    (P : Ideal C) [P.IsPrime]
    (hPB : P.comap (algebraMap B C) = IsLocalRing.maximalIdeal B)
    (hPAh : P.comap (algebraMap Ah C) = IsLocalRing.maximalIdeal Ah) :
    (⨅ a : {a : A // a ≠ 0}, Ideal.span {(a : A)} • (⊤ : Submodule A N)) = ⊥ := by
  have hlocB : IsLocalHom (algebraMap B (Localization.AtPrime P)) :=
    isLocalHom_localization_atPrime P hPB
  have hlocAh : IsLocalHom (algebraMap Ah (Localization.AtPrime P)) :=
    isLocalHom_localization_atPrime P hPAh
  have : Module.Flat B (Localization.AtPrime P) :=
    Module.Flat.trans B C (Localization.AtPrime P)
  have : Module.FaithfullyFlat B (Localization.AtPrime P) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have : Algebra.IsPushout A Ah B C := hpush
  have : Module.Flat Ah (C ⊗[B] N) :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.cancelBaseChange A Ah B C N)
  have : Module.Flat Ah (Localization.AtPrime P ⊗[C] (C ⊗[B] N)) :=
    flat_baseChange_of_flat
  have : Module.Finite C (C ⊗[B] N) := Module.Finite.base_change B C N
  have : Module.Finite (Localization.AtPrime P)
      (Localization.AtPrime P ⊗[C] (C ⊗[B] N)) :=
    Module.Finite.base_change C (Localization.AtPrime P) (C ⊗[B] N)
  let ι : N →+ (Localization.AtPrime P ⊗[C] (C ⊗[B] N)) :=
    { toFun := fun n => 1 ⊗ₜ (1 ⊗ₜ n)
      map_zero' := by simp
      map_add' := fun n m => by simp [TensorProduct.tmul_add] }
  have hcancel : ∀ n : N,
      TensorProduct.AlgebraTensorModule.cancelBaseChange B C (Localization.AtPrime P)
        (Localization.AtPrime P) N (ι n) = (1 : Localization.AtPrime P) ⊗ₜ n := by
    intro n
    show TensorProduct.AlgebraTensorModule.cancelBaseChange B C (Localization.AtPrime P)
      (Localization.AtPrime P) N (1 ⊗ₜ (1 ⊗ₜ n)) = _
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    simp
  have hι : Function.Injective ι := by
    intro x y hxy
    apply Module.FaithfullyFlat.tensorProduct_mk_injective
      (A := B) (B := Localization.AtPrime P) N
    show (1 : Localization.AtPrime P) ⊗ₜ x = (1 : Localization.AtPrime P) ⊗ₜ y
    rw [← hcancel x, ← hcancel y, hxy]
  have hpull : ∀ (c : C) (n : N),
      (1 : Localization.AtPrime P) ⊗ₜ[C] (c ⊗ₜ[B] n) =
        (algebraMap C (Localization.AtPrime P) c) ⊗ₜ[C] ((1 : C) ⊗ₜ[B] n) := by
    intro c n
    rw [show c ⊗ₜ[B] n = c • ((1 : C) ⊗ₜ[B] n) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
      ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  have hsmul : ∀ (a : A) (n : N), ι (a • n) = (algebraMap A Ah a) • ι n := by
    intro a n
    show (1 : Localization.AtPrime P) ⊗ₜ[C] ((1 : C) ⊗ₜ[B] (a • n)) =
      (algebraMap A Ah a) • ((1 : Localization.AtPrime P) ⊗ₜ[C] ((1 : C) ⊗ₜ[B] n))
    rw [show a • n = (algebraMap A B a) • n from (IsScalarTower.algebraMap_smul B a n).symm,
      ← TensorProduct.smul_tmul, Algebra.smul_def (R := B) (A := C), mul_one,
      ← IsScalarTower.algebraMap_apply A B C, hpull,
      TensorProduct.smul_tmul' (algebraMap A Ah a)]
    congr 1
    rw [Algebra.smul_def, mul_one,
      IsScalarTower.algebraMap_apply Ah C (Localization.AtPrime P),
      ← IsScalarTower.algebraMap_apply A Ah C]
  exact iInf_smul_top_eq_bot_of_injective hA hind
    (fun x => Module.exists_isContentIdeal_of_colimit_free_presentation
      (A := Ah) (B := Localization.AtPrime P) inferInstance x) ι hι hsmul

end Pushout

section Assembly

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A]
variable {B : Type v} [CommRing B] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
variable {N : Type w} [AddCommGroup N] [Module A N] [Module B N]
  [IsScalarTower A B N] [Module.Finite B N] [Module.Flat A N]

include B in
/-- The separatedness, with a henselization of the base supplied. -/
private theorem iInf_smul_top_eq_bot_of_henselization
    (hA : ¬ IsField A)
    (Ah : Type u) [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsLocalRing.IsHenselization A (ResidueField A) Ah] :
    (⨅ a : {a : A // a ≠ 0}, Ideal.span {(a : A)} • (⊤ : Submodule A N)) = ⊥ := by
  have : IsLocalHom (algebraMap A Ah) :=
    IsLocalRing.IsHenselization.isLocalHom (L := ResidueField A)
  have : Module.Flat A Ah := IsLocalRing.IsHenselization.flat (L := ResidueField A)
  have : HenselianLocalRing Ah :=
    IsLocalRing.IsHenselization.henselian (R := A) (L := ResidueField A) (Rh := Ah)
  have hind : StacksDraft.IndEtale A Ah :=
    StacksDraft.indEtale_iff.mpr
      (IsLocalRing.IsHenselization.ind_etale_of_universe_le (ResidueField A))
  have : Module.Flat B (Ah ⊗[A] B) := by
    have hsym : Algebra.IsPushout A B Ah (Ah ⊗[A] B) := Algebra.IsPushout.symm inferInstance
    exact Module.Flat.of_linearEquiv
      (Algebra.IsPushout.equiv A B Ah (Ah ⊗[A] B)).symm.toLinearEquiv
  have : (tensorPrime (A := A) (B := B) Ah).IsPrime := (tensorPrime_isMaximal Ah).isPrime
  exact iInf_smul_top_eq_bot_of_isPushout hA hind inferInstance
    (tensorPrime (A := A) (B := B) Ah) (tensorPrime_comap_right Ah)
    (tensorPrime_comap_left Ah)

include B in
/-- **Separatedness of a flat finite module over a local domain which is not a field.** Let
`A` be a local domain which is not a field, let `A → B` be a local homomorphism essentially
of finite type, and let `N` be a finite `B`-module which is flat over `A`. Then the
submodules `aN`, for `a` a nonzero element of `A`, intersect in zero.

This is the separatedness assertion of the second paragraph of Claim 2 in the proof of
Stacks 05U9, applied there to `A/𝔭`, `B/𝔭B` and `N/𝔭N`. The content ideals it goes through
are Stacks 05U7 together with Stacks 0ASD, namely
`Module.exists_isContentIdeal_of_colimit_free_presentation`: over a henselian local base, a
finite module over a local algebra essentially of finite type which is flat over the base has
content ideals. -/
theorem iInf_smul_top_eq_bot (hA : ¬ IsField A) :
    (⨅ a : {a : A // a ≠ 0}, Ideal.span {(a : A)} • (⊤ : Submodule A N)) = ⊥ := by
  obtain ⟨Ah, _, _, _, _⟩ := IsLocalRing.exists_isHenselization_residueField A
  exact iInf_smul_top_eq_bot_of_henselization (B := B) (N := N) hA Ah

end Assembly

section Prime

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {B : Type v} [CommRing B] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
variable {N : Type w} [AddCommGroup N] [Module A N] [Module B N]
  [IsScalarTower A B N] [Module.Finite B N]

include B in
/-- **The separatedness of `N/𝔭N` used in Claim 2 of the proof of Stacks 05U9.** Let `A → B`
be a local homomorphism essentially of finite type, let `N` be a finite `B`-module, and let
`𝔭` be a prime of `A` other than the maximal ideal such that `N/𝔭N` is flat over `A/𝔭`.
Then an element of `N/𝔭N` lying in `f(N/𝔭N)` for every `f ∈ A ∖ 𝔭` is zero.

`A/𝔭` is a local domain which is not a field, `B/𝔭B` is a local `A/𝔭`-algebra essentially of
finite type, and `(B/𝔭B) ⊗_B N` is `N/𝔭N`, so this is `iInf_smul_top_eq_bot`. -/
theorem eq_zero_of_forall_mem_smul_top
    (p : Ideal A) [p.IsPrime] (hp : p ≠ IsLocalRing.maximalIdeal A)
    (hflat : Module.Flat (A ⧸ p) (N ⧸ (p • (⊤ : Submodule A N))))
    (x : N ⧸ (p • (⊤ : Submodule A N)))
    (hx : ∀ f : A, f ∉ p →
      x ∈ Ideal.span {f} • (⊤ : Submodule A (N ⧸ (p • (⊤ : Submodule A N))))) :
    x = 0 := by
  classical
  have hple : p ≤ IsLocalRing.maximalIdeal A := IsLocalRing.le_maximalIdeal
    (Ideal.IsPrime.ne_top inferInstance)
  -- the quotient base
  have : IsLocalRing (A ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk p) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have hAfield : ¬ IsField (A ⧸ p) := by
    intro hfield
    refine hp (le_antisymm hple fun a ha => ?_)
    have hmem : Ideal.Quotient.mk p a ∈ IsLocalRing.maximalIdeal (A ⧸ p) := by
      rw [← IsLocalRing.maximalIdeal_comap (Ideal.Quotient.mk p)] at ha
      exact ha
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield] at hmem
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hmem)
  -- the quotient algebra
  have hJle : p.map (algebraMap A B) ≤ IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]
    exact hple
  have hJtop : p.map (algebraMap A B) ≠ ⊤ := fun htop =>
    (IsLocalRing.maximalIdeal.isMaximal B).ne_top (top_le_iff.mp (htop ▸ hJle))
  let : Algebra (A ⧸ p) (B ⧸ p.map (algebraMap A B)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have : Nontrivial (B ⧸ p.map (algebraMap A B)) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  have : IsLocalRing (B ⧸ p.map (algebraMap A B)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk (p.map (algebraMap A B))) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk (p.map (algebraMap A B)))
      Ideal.Quotient.mk_surjective
  have hlocq : IsLocalHom (algebraMap (A ⧸ p) (B ⧸ p.map (algebraMap A B))) := by
    refine ⟨fun y hy => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hcomm : algebraMap (A ⧸ p) (B ⧸ p.map (algebraMap A B)) (Ideal.Quotient.mk p a) =
        Ideal.Quotient.mk (p.map (algebraMap A B)) (algebraMap A B a) := rfl
    rw [hcomm] at hy
    have h1 : IsUnit (algebraMap A B a) :=
      IsLocalHom.map_nonunit (f := Ideal.Quotient.mk (p.map (algebraMap A B))) _ hy
    exact (IsLocalHom.map_nonunit (f := algebraMap A B) a h1).map (Ideal.Quotient.mk p)
  have : Algebra.EssFiniteType (A ⧸ p) (B ⧸ p.map (algebraMap A B)) :=
    Algebra.EssFiniteType.quotient_map A B p
  -- the quotient module, as a base change
  have hpush : Algebra.IsPushout A (A ⧸ p) B (B ⧸ p.map (algebraMap A B)) :=
    Stacks.Henselian.isPushout_quotient_map p
  let e₁ : (A ⧸ p) ⊗[A] N ≃ₗ[A ⧸ p] N ⧸ (p • (⊤ : Submodule A N)) :=
    LinearEquiv.extendScalarsOfSurjective (S := A ⧸ p) Ideal.Quotient.mk_surjective
      (TensorProduct.quotTensorEquivQuotSMul N p)
  let e₂ : (B ⧸ p.map (algebraMap A B)) ⊗[B] N ≃ₗ[A ⧸ p] (A ⧸ p) ⊗[A] N :=
    Algebra.IsPushout.cancelBaseChange A (A ⧸ p) B (B ⧸ p.map (algebraMap A B)) N
  have : Module.Flat (A ⧸ p) ((A ⧸ p) ⊗[A] N) := Module.Flat.of_linearEquiv e₁
  have : Module.Flat (A ⧸ p) ((B ⧸ p.map (algebraMap A B)) ⊗[B] N) :=
    Module.Flat.of_linearEquiv e₂
  let ε : (N ⧸ (p • (⊤ : Submodule A N))) ≃ₗ[A ⧸ p]
      (B ⧸ p.map (algebraMap A B)) ⊗[B] N := e₁.symm.trans e₂.symm
  have hbot := iInf_smul_top_eq_bot (A := A ⧸ p)
    (B := B ⧸ p.map (algebraMap A B)) (N := (B ⧸ p.map (algebraMap A B)) ⊗[B] N) hAfield
  have hmem : ε x ∈ ⨅ a : {a : A ⧸ p // a ≠ 0},
      Ideal.span {(a : A ⧸ p)} • (⊤ : Submodule (A ⧸ p)
        ((B ⧸ p.map (algebraMap A B)) ⊗[B] N)) := by
    refine (Submodule.mem_iInf _).mpr fun a => ?_
    obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective a.val
    have hfp : f ∉ p := fun hfp => a.property (by
      rw [← hf]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hfp)
    refine Submodule.smul_induction_on (hx f hfp) ?_ ?_
    · intro c hc y _
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      have hlin : ε ((d * f) • y) = (algebraMap A (A ⧸ p) (d * f)) • ε y := by
        rw [← IsScalarTower.algebraMap_smul (A ⧸ p) (d * f) y, map_smul]
      rw [hlin]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      refine Ideal.mem_span_singleton'.mpr ⟨algebraMap A (A ⧸ p) d, ?_⟩
      rw [← hf]
      exact (map_mul (algebraMap A (A ⧸ p)) d f).symm
    · intro y z hy hz
      rw [map_add]
      exact Submodule.add_mem _ hy hz
  rw [hbot] at hmem
  exact ε.injective (by simpa using hmem)

end Prime

end Stacks.ResidueFibre

end
