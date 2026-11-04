module

public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.RingTheory.Support
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.AlgebraicGeometry.Duality.DivideByTorsion
public import StacksFrontier.RingTheory.AdicCompletion.TateModule.FiniteComplete
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.AdicQuotientComparison
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.CompletedLocalCohomologyLimit

/-!
# Degree-zero completed local cohomology

With the notation and hypotheses of Tag 0EEW — a Noetherian ring `A`, ideals `I` and `J`, a
finite `A`-module `M` and `Z = V(J)` — assume moreover that `A` is `I`-adically complete. Then
the degree-zero cohomology of the derived `I`-adic completion of `RΓ_Z(M)` is the filtered
colimit of `H⁰_{V(J')}(M)` over the ideals `J' ⊆ J` with `V(J') ∩ V(I) = V(J) ∩ V(I)`.

Each `H⁰_{V(J')}(M)` is the `J'`-power-torsion submodule of `M`, the maps of the colimit are the
inclusions between these submodules, and the index set is closed under products of ideals; so the
colimit is realized as the supremum `⨆ J', Γ_{J'}(M)` inside `M`. That supremum is described
pointwise by `Dualizing.supportTraceSubmodule`: an element `x` of `M` lies in it exactly when the
support of `A · x` meets `V(I)` only inside `V(J)`.

The proof follows the source. Tag 0EEW in degree zero has vanishing `R¹lim` term, because local
cohomology of a module vanishes in negative degrees, so `H⁰(RΓ_Z(M)^∧) = lim H⁰_Z(M/IⁿM)`. Each
`H⁰_Z(M/IⁿM)` is the `J`-power torsion of `M/IⁿM`, so the limit is the submodule of the `I`-adic
completion of `M` cut out by those torsion conditions; and `M`, being finite over an `I`-adically
complete Noetherian ring, is itself `I`-adically complete. The identification of that submodule
of `M` with the supremum of torsion submodules uses the Artin–Rees lemma.

## Implementation notes

The conclusion is first proved for every derived limit of the tower `n ↦ RΓ_Z(M/IⁿM)`, which
needs no identification of the derived limit. Tag 0EEW part (1),
`Dualizing.isDerivedLimit_completedLocalCohomology`, says that `RΓ_Z(M)^∧` is such a derived
limit, and specializing to it gives the tag. The finite generation of `I` and `J` that the
construction of `RΓ_Z(M)^∧` consumes is supplied by `Ideal.fg_of_isNoetherianRing`.

## Main definitions

* `Dualizing.supportTraceSubmodule` — the submodule of `M` of elements whose cyclic support meets
  `V(I)` only inside `V(J)`.
* `Dualizing.adicQuotientTorsionSubmodule` — the submodule of the `I`-adic completion of `M` of
  elements all of whose stages are `J`-power torsion.

## Main results

* `Dualizing.iSup_primaryComponent_eq_supportTraceSubmodule` — the colimit of the tag, as a
  supremum of torsion submodules of `M`, is `Dualizing.supportTraceSubmodule`; in particular the
  supremum is the union of its terms, so the colimit is filtered.
* `Dualizing.primaryComponent_le_primaryComponent_of_le` and
  `Dualizing.zeroLocus_mul_inter_eq_of_inter_eq` — the index set is directed under reverse
  inclusion and the terms grow along it, which is what makes the colimit filtered.
* `Dualizing.exists_iso_limit_homology_zero_adicQuotientLocalCohomologySystem` — the inverse
  limit of Tag 0EEW in degree zero, computed as a submodule of the `I`-adic completion of `M`.
* `Dualizing.exists_iso_homology_zero_of_isDerivedLimit` — the conclusion of Tag 0EEX for any
  derived limit of the tower.
* `Dualizing.exists_iso_homology_zero_completedLocalCohomology` — Tag 0EEX: the same conclusion
  for `RΓ_Z(M)^∧` itself, under exactly the hypotheses of the tag.

That each term `H⁰_{V(J')}(M)` of the colimit is the torsion submodule `Γ_{J'}(M)` is the
library's `Stacks.Duality.supportLocalCohomology_zero_iso_torsion`, which also pins down the
identification by its composite with the inclusion into `M`.

## References

* [Stacks Project, Tag 0EEX](https://stacks.math.columbia.edu/tag/0EEX)
* [Stacks Project, Tag 0EEW](https://stacks.math.columbia.edu/tag/0EEW)
* [Stacks Project, Tag 00IQ](https://stacks.math.columbia.edu/tag/00IQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.ProEtale (adicQuotientModuleSystem)

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

section SupportTrace

/-- A cyclic module whose support lies in `V(J)` is `J`-power torsion. -/
theorem mem_primaryComponent_of_support_span_singleton_le
    (A : Type u) [CommRing A] (J : Ideal A) (hJ : J.FG)
    (M : Type v) [AddCommGroup M] [Module A M] (x : M)
    (hSupp : Module.support A (A ∙ x) ⊆ PrimeSpectrum.zeroLocus (J : Set A)) :
    x ∈ Ideal.primaryComponent M J := by
  obtain ⟨n, -, hn⟩ := (isIPowerTorsion_of_support_subset hJ hSupp)
    ⟨x, Submodule.mem_span_singleton_self x⟩
  rw [Ideal.primaryComponent_mem]
  refine ⟨n, ?_⟩
  rw [Submodule.mem_torsionBySet_iff]
  intro a
  simpa using congrArg Subtype.val (hn a.1 a.2)

/-- The support of a cyclic module is the zero locus of the annihilator of its generator. -/
theorem support_span_singleton_eq_zeroLocus_annihilator
    (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A M] (x : M) :
    Module.support A (A ∙ x) = PrimeSpectrum.zeroLocus ((A ∙ x).annihilator : Set A) := by
  rw [Module.support_eq_zeroLocus,
    show Module.annihilator A (A ∙ x) = (A ∙ x).annihilator from
      Submodule.toSubMulAction_inj.mp rfl]

/-- An element killed by a power of `J` generates a cyclic module supported in `V(J)`. -/
theorem support_span_singleton_le_zeroLocus_of_mem_primaryComponent
    (A : Type u) [CommRing A] (J : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M] (x : M)
    (hx : x ∈ Ideal.primaryComponent M J) :
    Module.support A (A ∙ x) ⊆ PrimeSpectrum.zeroLocus (J : Set A) := by
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M J x).mp hx
  have hpow : J ^ n ≤ (A ∙ x).annihilator := fun a ha ↦
    (Submodule.mem_annihilator_span_singleton x a).2
      ((Submodule.mem_torsionBySet_iff (↑(J ^ n) : Set A) x).mp hn ⟨a, ha⟩)
  rw [support_span_singleton_eq_zeroLocus_annihilator A M x]
  intro p hp
  rw [PrimeSpectrum.mem_zeroLocus] at hp ⊢
  exact p.2.le_of_pow_le (hpow.trans hp)

/-- The cyclic support of a sum is contained in the union of the cyclic supports. -/
theorem support_span_singleton_add_le
    (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A M] (x y : M) :
    Module.support A (A ∙ (x + y)) ⊆
      Module.support A (A ∙ x) ∪ Module.support A (A ∙ y) := by
  intro p hp
  by_contra h
  have hx : p ∉ Module.support A (A ∙ x) := fun hpx ↦ h (Or.inl hpx)
  have hy : p ∉ Module.support A (A ∙ y) := fun hpy ↦ h (Or.inr hpy)
  obtain ⟨a, ha, hax⟩ := (Module.notMem_support_iff' (p := p) (M := A ∙ x)).mp hx
    ⟨x, Submodule.mem_span_singleton_self x⟩
  obtain ⟨b, hb, hby⟩ := (Module.notMem_support_iff' (p := p) (M := A ∙ y)).mp hy
    ⟨y, Submodule.mem_span_singleton_self y⟩
  have hax' : a • x = 0 := congrArg Subtype.val hax
  have hby' : b • y = 0 := congrArg Subtype.val hby
  have hc : (b * a) • (x + y) = 0 := by
    calc
      (b * a) • (x + y) = b • (a • x) + a • (b • y) := by
        simp [mul_smul, smul_comm b a y]
      _ = 0 := by simp [hax', hby']
  have hab : b * a ∉ p.asIdeal := p.asIdeal.primeCompl.mul_mem hb ha
  obtain ⟨z, hz⟩ := (Module.mem_support_iff_exists_annihilator (p := p)).mp hp
  have hkill : b * a ∈ (A ∙ (x + y)).annihilator :=
    (Submodule.mem_annihilator_span_singleton (x + y) (b * a)).mpr hc
  have hz0' : (b * a) • z = 0 :=
    Subtype.ext ((Submodule.mem_annihilator.mp hkill) z z.property)
  exact hab (hz ((Submodule.mem_annihilator_span_singleton z (b * a)).mpr hz0'))

/-- The submodule of `M` of elements `x` such that the support of `A · x` meets `V(I)` only
inside `V(J)`. For `A` Noetherian this is the union of the `J'`-power-torsion submodules over
the ideals `J' ⊆ J` with `V(J') ∩ V(I) = V(J) ∩ V(I)`. -/
def supportTraceSubmodule
    (A : Type u) [CommRing A] (I J : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M] : Submodule A M where
  carrier := {x | Module.support A (A ∙ x) ∩
    PrimeSpectrum.zeroLocus (I : Set A) ⊆ PrimeSpectrum.zeroLocus (J : Set A)}
  zero_mem' := by
    have hz : (A ∙ (0 : M)) = ⊥ := by simp
    change Module.support A (A ∙ (0 : M)) ∩
      PrimeSpectrum.zeroLocus (I : Set A) ⊆ PrimeSpectrum.zeroLocus (J : Set A)
    rw [hz, Module.support_eq_empty_iff.mpr inferInstance]
    simp
  add_mem' := by
    intro x y hx hy p hp
    rcases support_span_singleton_add_le A M x y hp.1 with hpx | hpy
    · exact hx ⟨hpx, hp.2⟩
    · exact hy ⟨hpy, hp.2⟩
  smul_mem' := by
    intro a x hx p hp
    exact hx ⟨Module.support_subset_of_injective
      (Submodule.inclusion (Submodule.span_singleton_smul_le A a x))
      (Submodule.inclusion_injective _) hp.1, hp.2⟩

/-- An element `x` lies in `Dualizing.supportTraceSubmodule A I J M` if and only if
`Supp(A · x) ∩ V(I) ⊆ V(J)`. -/
theorem mem_supportTraceSubmodule_iff_support_inter_le
    (A : Type u) [CommRing A] (I J : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M] (x : M) :
    x ∈ supportTraceSubmodule A I J M ↔
      Module.support A (A ∙ x) ∩ PrimeSpectrum.zeroLocus (I : Set A) ⊆
        PrimeSpectrum.zeroLocus (J : Set A) :=
  Iff.rfl

/-- Every term of the colimit of Tag 0EEX is contained in `Dualizing.supportTraceSubmodule`. -/
theorem primaryComponent_le_supportTraceSubmodule
    (A : Type u) [CommRing A] (I J J' : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M]
    (htrace : PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)) :
    Ideal.primaryComponent M J' ≤ supportTraceSubmodule A I J M := by
  intro x hx p hp
  exact (htrace.subset
    ⟨support_span_singleton_le_zeroLocus_of_mem_primaryComponent A J' M x hx hp.1, hp.2⟩).1

/-- An element of `Dualizing.supportTraceSubmodule` is `J'`-power torsion for some ideal `J'`
admissible for the colimit of Tag 0EEX: take `J' = ann(A · x) · J`. -/
theorem exists_primaryComponent_of_mem_supportTraceSubmodule
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I J : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M] (x : M)
    (hx : x ∈ supportTraceSubmodule A I J M) :
    ∃ J' : Ideal A, J' ≤ J ∧
      PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) ∧
      x ∈ Ideal.primaryComponent M J' := by
  have htrace : Module.support A (A ∙ x) ∩ PrimeSpectrum.zeroLocus (I : Set A) ⊆
    PrimeSpectrum.zeroLocus (J : Set A) := hx
  set K := (A ∙ x).annihilator
  have hsupp : Module.support A (A ∙ x) = PrimeSpectrum.zeroLocus (K : Set A) :=
    support_span_singleton_eq_zeroLocus_annihilator A M x
  have htrace' : PrimeSpectrum.zeroLocus (K : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A) ⊆ PrimeSpectrum.zeroLocus (J : Set A) := by
    simpa [hsupp] using htrace
  refine ⟨K * J, Ideal.mul_le_right, ?_, ?_⟩
  · rw [PrimeSpectrum.zeroLocus_mul, Set.union_inter_distrib_right,
      Set.union_eq_right.mpr (Set.subset_inter htrace' Set.inter_subset_right)]
  · refine mem_primaryComponent_of_support_span_singleton_le A (K * J)
      (K * J).fg_of_isNoetherianRing M x ?_
    rw [hsupp, PrimeSpectrum.zeroLocus_mul]
    exact Set.subset_union_left

/-- **The colimit of Tag 0EEX, computed.** The supremum of the `J'`-power-torsion submodules of
`M`, over the ideals `J' ⊆ J` with `V(J') ∩ V(I) = V(J) ∩ V(I)`, is the submodule of elements
whose cyclic support meets `V(I)` only inside `V(J)`. In particular the supremum is a filtered
union: every element of it is already `J'`-power torsion for one admissible `J'`. -/
theorem iSup_primaryComponent_eq_supportTraceSubmodule
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I J : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M] :
    (⨆ (J' : Ideal A) (_ : J' ≤ J)
      (_ : PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)),
      Ideal.primaryComponent M J') = supportTraceSubmodule A I J M := by
  refine le_antisymm (iSup_le fun J' ↦ iSup_le fun _ ↦ iSup_le fun htrace ↦
    primaryComponent_le_supportTraceSubmodule A I J J' M htrace) fun x hx ↦ ?_
  obtain ⟨J', hJ'le, htrace, hprimary⟩ :=
    exists_primaryComponent_of_mem_supportTraceSubmodule A I J M x hx
  exact Submodule.mem_iSup_of_mem J' <| Submodule.mem_iSup_of_mem hJ'le <|
    Submodule.mem_iSup_of_mem htrace hprimary

/-- The ideal-power-torsion submodule is antitone in the ideal: a smaller ideal has a larger
zero locus, hence more sections supported there. -/
theorem primaryComponent_le_primaryComponent_of_le
    (A : Type u) [CommRing A] {J₁ J₂ : Ideal A} (h : J₂ ≤ J₁)
    (M : Type v) [AddCommGroup M] [Module A M] :
    Ideal.primaryComponent M J₁ ≤ Ideal.primaryComponent M J₂ := by
  intro x hx
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M J₁ x).mp hx
  rw [Ideal.primaryComponent_mem]
  refine ⟨n, ?_⟩
  rw [Submodule.mem_torsionBySet_iff]
  intro a
  exact (Submodule.mem_torsionBySet_iff _ _).mp hn ⟨a.1, Ideal.pow_right_mono h n a.2⟩

/-- **The index set of the colimit of Tag 0EEX is directed.** If `J₁` and `J₂` both have the same
trace on `V(I)` as `J`, so does `J₁ * J₂`, which is contained in both. Together with
`Dualizing.primaryComponent_le_primaryComponent_of_le` this exhibits the colimit as filtered. -/
theorem zeroLocus_mul_inter_eq_of_inter_eq
    (A : Type u) [CommRing A] (I J J₁ J₂ : Ideal A)
    (h₁ : PrimeSpectrum.zeroLocus (J₁ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))
    (h₂ : PrimeSpectrum.zeroLocus (J₂ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)) :
    PrimeSpectrum.zeroLocus ((J₁ * J₂ : Ideal A) : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) := by
  rw [PrimeSpectrum.zeroLocus_mul, Set.union_inter_distrib_right, h₁, h₂, Set.union_self]

/-- The class of `x` in `M / S` is `J`-power torsion exactly when some power of `J` carries `x`
into `S`. -/
theorem mkQ_mem_primaryComponent_iff
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    (S : Submodule A M) (J : Ideal A) (x : M) :
    S.mkQ x ∈ Ideal.primaryComponent (M ⧸ S) J ↔ ∃ k : ℕ, ∀ a ∈ J ^ k, a • x ∈ S := by
  rw [Ideal.primaryComponent_mem]
  simp only [Submodule.mem_torsionBySet_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, fun a ha ↦ (Submodule.Quotient.mk_eq_zero S).mp (by simpa using hk ⟨a, ha⟩)⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, fun a ↦ by
      simpa using (Submodule.Quotient.mk_eq_zero S).mpr (hk a a.property)⟩

/-- **Membership in `Dualizing.supportTraceSubmodule`, stagewise.** For a finite module over a
Noetherian ring, the cyclic support of `x` meets `V(I)` only inside `V(J)` exactly when the class
of `x` in each `M/IⁿM` is `J`-power torsion. The implication from the stagewise condition uses
the Artin–Rees lemma. -/
theorem mem_supportTraceSubmodule_iff_forall_mkQ_mem_primaryComponent
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I J : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] (x : M) :
    x ∈ supportTraceSubmodule A I J M ↔
      ∀ n : ℕ, (I ^ n • (⊤ : Submodule A M)).mkQ x ∈
        Ideal.primaryComponent (M ⧸ (I ^ n • (⊤ : Submodule A M))) J := by
  rw [mem_supportTraceSubmodule_iff_support_inter_le,
    support_span_singleton_eq_zeroLocus_annihilator A M x]
  constructor
  · intro hx n
    rw [mkQ_mem_primaryComponent_iff]
    have hrad : J ≤ (I ^ n ⊔ (A ∙ x).annihilator).radical := by
      rw [← PrimeSpectrum.zeroLocus_subset_zeroLocus_iff]
      intro p hp
      rw [PrimeSpectrum.zeroLocus_sup] at hp
      exact hx ⟨hp.2, p.2.le_of_pow_le hp.1⟩
    obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad J.fg_of_isNoetherianRing
    refine ⟨k, fun a ha ↦ ?_⟩
    obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.mp (hk ha)
    rw [add_smul, (Submodule.mem_annihilator_span_singleton x c).mp hc, add_zero]
    exact Submodule.smul_mem_smul hb Submodule.mem_top
  · intro hx p hp
    obtain ⟨c, hc⟩ := I.exists_pow_inf_eq_pow_smul (A ∙ x)
    obtain ⟨k, hk⟩ := (mkQ_mem_primaryComponent_iff _ J x).mp (hx (c + 1))
    apply p.2.le_of_pow_le (n := k)
    intro a ha
    have hax : a • x ∈ I • (A ∙ x) := by
      have h : a • x ∈ (I ^ (c + 1) • (⊤ : Submodule A M)) ⊓ (A ∙ x) :=
        ⟨hk a ha, Submodule.smul_mem _ a (Submodule.mem_span_singleton_self x)⟩
      rw [hc (c + 1) (by omega), Nat.add_sub_cancel_left, pow_one] at h
      exact (show I • ((I ^ c • (⊤ : Submodule A M)) ⊓ (A ∙ x)) ≤ I • (A ∙ x) from
        smul_mono_right I inf_le_right) h
    obtain ⟨b, hb, hbx⟩ := Submodule.mem_smul_span_singleton.mp hax
    have hab : a - b ∈ (A ∙ x).annihilator := by
      rw [Submodule.mem_annihilator_span_singleton, sub_smul, hbx, sub_self]
    simpa using p.asIdeal.add_mem (hp.1 hab) (hp.2 hb)

/-- The submodule of the `I`-adic completion of `M` of elements whose image in each `M/IⁿM` is
`J`-power torsion. It is the inverse limit of the submodules `H⁰_{V(J)}(M/IⁿM)`. -/
abbrev adicQuotientTorsionSubmodule
    (A : Type u) [CommRing A] (I J : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M] : Submodule A (AdicCompletion I M) :=
  ⨅ n : ℕ, (Ideal.primaryComponent (M ⧸ (I ^ n • (⊤ : Submodule A M))) J).comap
    (AdicCompletion.eval I M n)

/-- For `M` finite over a Noetherian ring, `Dualizing.supportTraceSubmodule A I J M` is the
preimage of `Dualizing.adicQuotientTorsionSubmodule A I J M` under the map `M → M^∧`. -/
theorem supportTraceSubmodule_eq_comap_adicQuotientTorsionSubmodule
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I J : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    supportTraceSubmodule A I J M =
      (adicQuotientTorsionSubmodule A I J M).comap (AdicCompletion.of I M) := by
  ext x
  simpa only [adicQuotientTorsionSubmodule, Submodule.mem_comap, Submodule.mem_iInf,
    AdicCompletion.eval_of] using
    mem_supportTraceSubmodule_iff_forall_mkQ_mem_primaryComponent A I J M x

/-- For `M` finite over a Noetherian ring and `I`-adically complete, the submodule of `M` of
Tag 0EEX is carried isomorphically onto the inverse limit of the torsion submodules of the
`I`-adic quotients. -/
def supportTraceAdicEquiv
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I J : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] [IsAdicComplete I M] :
    supportTraceSubmodule A I J M ≃ₗ[A] adicQuotientTorsionSubmodule A I J M :=
  (LinearEquiv.ofEq _ _
    (supportTraceSubmodule_eq_comap_adicQuotientTorsionSubmodule A I J M)).trans
      ((AdicCompletion.ofLinearEquiv I M).ofSubmodule' (adicQuotientTorsionSubmodule A I J M))

/-- The equivalence `Dualizing.supportTraceAdicEquiv` sends `x` to its image in the `I`-adic
completion of `M`. -/
@[simp] theorem supportTraceAdicEquiv_apply
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I J : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] [IsAdicComplete I M]
    (x : supportTraceSubmodule A I J M) :
    (supportTraceAdicEquiv A I J M x).1 = AdicCompletion.of I M x.1 := rfl

end SupportTrace

section Limit

variable (A : Type u) [CommRing A]

/-- The transition maps of the tower `n ↦ M/IⁿM` are Mathlib's `AdicCompletion.transitionMap`. -/
theorem adicQuotientModuleSystem_map (I : Ideal A) (M : ModuleCat.{v} A) {m n : ℕ} (h : m ≤ n) :
    (adicQuotientModuleSystem A I M).map (homOfLE h).op =
      ModuleCat.ofHom (AdicCompletion.transitionMap I M h) := by
  induction h with
  | refl =>
    rw [show (homOfLE (le_refl m)).op = 𝟙 (Opposite.op m) from rfl, CategoryTheory.Functor.map_id]
    ext x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl
  | @step n h ih =>
    rw [show (homOfLE (Nat.le_succ_of_le h)).op =
      (homOfLE (Nat.le_succ n)).op ≫ (homOfLE h).op from rfl, Functor.map_comp, ih]
    dsimp only [adicQuotientModuleSystem]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    ext x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

/-- The evaluation of `Dualizing.adicQuotientTorsionSubmodule A I J M` at the `n`-th stage, landing
in the `J`-power torsion of `M/IⁿM`. -/
def adicQuotientTorsionEval (I J : Ideal A) (M : ModuleCat.{v} A) (n : ℕᵒᵖ) :
    ModuleCat.of A (adicQuotientTorsionSubmodule A I J M) ⟶
      ModuleCat.of A (Ideal.primaryComponent ((adicQuotientModuleSystem A I M).obj n) J) :=
  ModuleCat.ofHom (((AdicCompletion.eval I M n.unop).comp
    (adicQuotientTorsionSubmodule A I J M).subtype).codRestrict _
      (fun x ↦ ((Submodule.mem_iInf _).mp x.property) n.unop))

/-- Given a tower `F` mapping to `n ↦ M/IⁿM` by stagewise isomorphisms `e` onto the
`J`-power-torsion submodules, the cone over `F` with vertex
`Dualizing.adicQuotientTorsionSubmodule A I J M` whose legs are the stagewise evaluations. -/
def adicQuotientTorsionCone (I J : Ideal A) (M : ModuleCat.{v} A)
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} A)
    (τ : F ⟶ adicQuotientModuleSystem A I M)
    (e : ∀ n : ℕᵒᵖ, F.obj n ≅
      ModuleCat.of A (Ideal.primaryComponent ((adicQuotientModuleSystem A I M).obj n) J))
    (he : ∀ n : ℕᵒᵖ, (e n).hom ≫ ModuleCat.ofHom
      (Ideal.primaryComponent ((adicQuotientModuleSystem A I M).obj n) J).subtype =
      τ.app n) : Cone F :=
  have hmono (n : ℕᵒᵖ) : Mono (τ.app n) := by
    have : Mono (ModuleCat.ofHom
        (Ideal.primaryComponent ((adicQuotientModuleSystem A I M).obj n) J).subtype) :=
      (ModuleCat.mono_iff_injective _).mpr (Submodule.subtype_injective _)
    rw [← he n]
    infer_instance
  { pt := ModuleCat.of A (adicQuotientTorsionSubmodule A I J M)
    π :=
      { app n := adicQuotientTorsionEval A I J M n ≫ (e n).inv
        naturality := by
          intro n m g
          have := hmono m
          apply (cancel_mono (τ.app m)).mp
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
            Category.assoc, τ.naturality]
          rw [← he m, ← he n]
          simp only [Category.assoc, Iso.inv_hom_id_assoc]
          have hg : g = (homOfLE (leOfHom g.unop)).op := Subsingleton.elim _ _
          rw [hg, adicQuotientModuleSystem_map]
          ext x
          exact (AdicCompletion.transitionMap_comp_eval_apply I M
            (leOfHom g.unop) x.val).symm } }

/-- The cone `Dualizing.adicQuotientTorsionCone` is a limit cone. -/
def isLimitAdicQuotientTorsionCone (I J : Ideal A) (M : ModuleCat.{v} A)
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} A)
    (τ : F ⟶ adicQuotientModuleSystem A I M)
    (e : ∀ n : ℕᵒᵖ, F.obj n ≅
      ModuleCat.of A (Ideal.primaryComponent ((adicQuotientModuleSystem A I M).obj n) J))
    (he : ∀ n : ℕᵒᵖ, (e n).hom ≫ ModuleCat.ofHom
      (Ideal.primaryComponent ((adicQuotientModuleSystem A I M).obj n) J).subtype =
      τ.app n) : IsLimit (adicQuotientTorsionCone A I J M F τ e he) where
  lift s := ModuleCat.ofHom ((AdicCompletion.lift I
      (fun n ↦ (s.π.app (Opposite.op n) ≫ τ.app (Opposite.op n)).hom)
      (fun {m n} h ↦ by
        have hmor : (s.π.app (Opposite.op n) ≫ τ.app (Opposite.op n)) ≫
            (adicQuotientModuleSystem A I M).map (homOfLE h).op =
            s.π.app (Opposite.op m) ≫ τ.app (Opposite.op m) := by
          rw [Category.assoc, ← τ.naturality, ← Category.assoc, s.w]
        refine LinearMap.ext fun x ↦ ?_
        have h1 := ConcreteCategory.congr_hom hmor x
        rwa [adicQuotientModuleSystem_map A I M h] at h1)).codRestrict
      (adicQuotientTorsionSubmodule A I J M) (fun x ↦ by
        refine (Submodule.mem_iInf _).mpr fun n ↦ ?_
        simp only [Submodule.mem_comap, AdicCompletion.eval_apply]
        change (s.π.app (Opposite.op n) ≫ τ.app (Opposite.op n)).hom x ∈ _
        rw [← he (Opposite.op n)]
        exact ((e (Opposite.op n)).hom (s.π.app (Opposite.op n) x)).property))
  fac s n := by
    apply (cancel_mono (e n).hom).mp
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ Subtype.ext ?_)
    change _ = ((e n).hom (s.π.app n x)).val
    simp only [adicQuotientTorsionCone, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (ConcreteCategory.congr_hom (he n) (s.π.app n x)).symm
  uniq s a ha := by
    refine ModuleCat.hom_ext
      (LinearMap.ext fun x ↦ Subtype.ext (AdicCompletion.ext fun n ↦ ?_))
    change _ = τ.app (Opposite.op n) (s.π.app (Opposite.op n) x)
    rw [← ha, ← he]
    change _ = ModuleCat.ofHom (Ideal.primaryComponent
      ((adicQuotientModuleSystem A I M).obj (Opposite.op n)) J).subtype
        ((e (Opposite.op n)).hom ((e (Opposite.op n)).inv
          (adicQuotientTorsionEval A I J M (Opposite.op n) (a x))))
    rw [Iso.inv_hom_id_apply]
    rfl

/-- A tower of modules mapping to the tower `n ↦ M/IⁿM` by stagewise isomorphisms onto the
`J`-power-torsion submodules has `Dualizing.adicQuotientTorsionSubmodule` as its inverse limit,
compatibly with the limit projections. -/
theorem exists_iso_limit_adicQuotientTorsionSubmodule (I J : Ideal A) (M : ModuleCat.{v} A)
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} A)
    (τ : F ⟶ adicQuotientModuleSystem A I M)
    (e : ∀ n : ℕᵒᵖ, F.obj n ≅
      ModuleCat.of A (Ideal.primaryComponent ((adicQuotientModuleSystem A I M).obj n) J))
    (he : ∀ n : ℕᵒᵖ, (e n).hom ≫ ModuleCat.ofHom
      (Ideal.primaryComponent ((adicQuotientModuleSystem A I M).obj n) J).subtype =
      τ.app n) :
    ∃ a : limit F ≅ ModuleCat.of A (adicQuotientTorsionSubmodule A I J M),
      ∀ n : ℕ, a.hom ≫ ModuleCat.ofHom (adicQuotientTorsionSubmodule A I J M).subtype ≫
          ModuleCat.ofHom (AdicCompletion.eval I M n) =
        limit.π F (Opposite.op n) ≫ τ.app (Opposite.op n) := by
  let hc := isLimitAdicQuotientTorsionCone A I J M F τ e he
  refine ⟨(limit.isLimit F).conePointUniqueUpToIso hc, fun n ↦ ?_⟩
  have h := congrArg (fun g ↦ g ≫ (e (Opposite.op n)).hom ≫ ModuleCat.ofHom
    (Ideal.primaryComponent ((adicQuotientModuleSystem A I M).obj (Opposite.op n)) J).subtype)
    (IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit F) hc (Opposite.op n))
  simp only [adicQuotientTorsionCone, Category.assoc, Iso.inv_hom_id_assoc, limit.cone_π] at h
  rwa [he] at h

/-- The canonical map `H⁰_{V(J)}(N) ⟶ N` is natural in the module `N`: it is the degree-zero
cohomology of the counit of the local-cohomology adjunction, followed by the identification of
the cohomology of a module placed in degree zero with the module. -/
theorem supportLocalCohomologyToModule_naturality (J : Ideal A) (hJ : J.FG)
    {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    (Stacks.Duality.supportLocalCohomology.{u, u} A J hJ 0).map f ≫
        Stacks.Duality.supportLocalCohomologyToModule.{u, u} A J hJ N =
      Stacks.Duality.supportLocalCohomologyToModule.{u, u} A J hJ M ≫ f := by
  set S := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  set H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
  set ε := (localCohomologyAdjunction A J hJ).counit
  set β := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0
  have h1 : (localCohomologyFunctor A J hJ ⋙ (derivedPowerTorsionProperty A J hJ).ι).map
        (S.map f) ≫ ε.app (S.obj N) = ε.app (S.obj M) ≫ S.map f := ε.naturality (S.map f)
  have h2 : H.map (S.map f) ≫ β.hom.app N = β.hom.app M ≫ f := β.hom.naturality f
  have e1 : H.map ((localCohomologyFunctor A J hJ ⋙
        (derivedPowerTorsionProperty A J hJ).ι).map (S.map f)) ≫ H.map (ε.app (S.obj N)) =
      H.map (ε.app (S.obj M)) ≫ H.map (S.map f) :=
    (H.map_comp _ _).symm.trans ((congrArg H.map h1).trans (H.map_comp _ _))
  show H.map ((localCohomologyFunctor A J hJ ⋙ (derivedPowerTorsionProperty A J hJ).ι).map
      (S.map f)) ≫ H.map (ε.app (S.obj N)) ≫ β.hom.app N =
    (H.map (ε.app (S.obj M)) ≫ β.hom.app M) ≫ f
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun g ↦ g ≫ β.hom.app N) e1).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun g ↦ H.map (ε.app (S.obj M)) ≫ g) h2).trans ?_
  exact (Category.assoc _ _ _).symm

/-- **The inverse limit of Tag 0EEW in degree zero.** The inverse limit of the modules
`H⁰_{V(J)}(M/IⁿM)` is the submodule of the `I`-adic completion of `M` of elements whose stages
are all `J`-power torsion, compatibly with the limit projections and the canonical maps
`H⁰_{V(J)}(M/IⁿM) ⟶ M/IⁿM`. -/
theorem exists_iso_limit_homology_zero_adicQuotientLocalCohomologySystem
    (I J : Ideal A) (hJ : J.FG) (M : ModuleCat.{u} A) :
    ∃ a : limit (adicQuotientLocalCohomologySystem A I J hJ M ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0) ≅
        ModuleCat.of A (adicQuotientTorsionSubmodule A I J M),
      ∀ n : ℕ, a.hom ≫ ModuleCat.ofHom (adicQuotientTorsionSubmodule A I J M).subtype ≫
          ModuleCat.ofHom (AdicCompletion.eval I M n) =
        limit.π (adicQuotientLocalCohomologySystem A I J hJ M ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0) (Opposite.op n) ≫
          Stacks.Duality.supportLocalCohomologyToModule.{u, u} A J hJ
            ((adicQuotientModuleSystem A I M).obj
              (Opposite.op n)) := by
  classical
  set Q := adicQuotientModuleSystem A I M with hQ
  set F := adicQuotientLocalCohomologySystem A I J hJ M ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0 with hF
  let τ : F ⟶ Q :=
    { app := fun n ↦
        Stacks.Duality.supportLocalCohomologyToModule.{u, u} A J hJ (Q.obj n)
      naturality := fun n m g ↦ supportLocalCohomologyToModule_naturality A J hJ (Q.map g) }
  have hiso (n : ℕᵒᵖ) : ∃ d : F.obj n ≅
      ModuleCat.of A (Ideal.primaryComponent (Q.obj n) J),
      d.hom ≫ ModuleCat.ofHom (Ideal.primaryComponent (Q.obj n) J).subtype = τ.app n :=
    Stacks.Duality.supportLocalCohomology_zero_iso_torsion.{u, u} A J hJ (Q.obj n)
  choose e he using hiso
  exact exists_iso_limit_adicQuotientTorsionSubmodule A I J M F τ e he

attribute [local instance] Dualizing.AdicQuotientComparison.derivedCategoryHasProductsNat

/-- **Tag 0EEW in degree zero.** The comparison map from `H⁰(RΓ_Z(M)^∧)` to the inverse limit of
the modules `H⁰_Z(M/IⁿM)` is invertible: the `R¹lim` term of the Milnor sequence involves the
local cohomology of the tower in degree `-1`, which vanishes. -/
theorem isIso_completedLocalCohomologyToLimit_zero (I J : Ideal A) (hJ : J.FG)
    (M : ModuleCat.{u} A) (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsDerivedLimit (adicQuotientLocalCohomologySystem A I J hJ M) K) :
    IsIso (completedLocalCohomologyToLimit A I J hJ M K hK 0) := by
  obtain ⟨i, w, hs⟩ := completedLocalCohomologyToLimit_shortExact A I J hJ M K hK 0
  have hzP : IsZero (∏ᶜ fun n : ℕ ↦ (adicQuotientLocalCohomologySystem A I J hJ M ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) (0 - 1)).obj (Opposite.op n)) := by
    rw [IsZero.iff_id_eq_zero]
    refine Pi.hom_ext _ _ fun n ↦ ?_
    exact (Stacks.LocalCohomology.isZero_localCohomologyModule_of_neg A J hJ
      ((adicQuotientModuleSystem A I M).obj (Opposite.op n))
      (0 - 1) (by decide)).eq_of_tgt _ _
  have : Mono (completedLocalCohomologyToLimit A I J hJ M K hK 0) :=
    hs.exact.mono_g ((@isZero_cokernel_of_epi _ _ _ _ _ _ (hzP.epi _) _).eq_of_src i 0)
  have : Epi (completedLocalCohomologyToLimit A I J hJ M K hK 0) := hs.epi_g
  exact isIso_of_mono_of_epi _

/-- **The conclusion of Stacks 0EEX, for an arbitrary derived limit of the tower.** Let `A` be
Noetherian and `I`-adically complete, let `J` be an ideal, let `M` be a finite `A`-module and
`Z = V(J)`. The degree-zero cohomology of a derived limit of `n ↦ RΓ_Z(M/IⁿM)` is the filtered
colimit of `H⁰_{V(J')}(M)` over the ideals `J' ⊆ J` with `V(J') ∩ V(I) = V(J) ∩ V(I)`. The colimit
is realized as the supremum of the `J'`-power-torsion submodules of `M`, and the identification is
the one induced by the comparison with `lim H⁰_Z(M/IⁿM)`: composing it with the inclusion into `M`
and the projection to `M/IⁿM` gives the `n`-th limit projection followed by the canonical map
`H⁰_Z(M/IⁿM) ⟶ M/IⁿM`. Tag 0EEX itself, for `RΓ_Z(M)^∧`, is
`Dualizing.exists_iso_homology_zero_completedLocalCohomology`. -/
theorem exists_iso_homology_zero_of_isDerivedLimit [IsNoetherianRing A]
    (I J : Ideal A) (hJ : J.FG) [IsAdicComplete I A] (M : ModuleCat.{u} A)
    [Module.Finite A M] (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsDerivedLimit (adicQuotientLocalCohomologySystem A I J hJ M) K)
    (P : Submodule A M)
    (hP : P = ⨆ (J' : Ideal A) (_ : J' ≤ J)
      (_ : PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)),
      Ideal.primaryComponent M J') :
    ∃ e : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj K ≅ ModuleCat.of A P,
      ∀ n : ℕ, e.hom ≫ ModuleCat.ofHom P.subtype ≫
          ModuleCat.ofHom (I ^ n • (⊤ : Submodule A M)).mkQ =
        completedLocalCohomologyToLimit A I J hJ M K hK 0 ≫
          limit.π (adicQuotientLocalCohomologySystem A I J hJ M ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0) (Opposite.op n) ≫
          Stacks.Duality.supportLocalCohomologyToModule.{u, u} A J hJ
            ((adicQuotientModuleSystem A I M).obj
              (Opposite.op n)) := by
  have : IsAdicComplete I M :=
    AdicCompletion.isAdicComplete_of_finite_of_isNoetherianRing I M
  rw [iSup_primaryComponent_eq_supportTraceSubmodule A I J M] at hP
  subst hP
  obtain ⟨a, ha⟩ :=
    exists_iso_limit_homology_zero_adicQuotientLocalCohomologySystem A I J hJ M
  have hiso := isIso_completedLocalCohomologyToLimit_zero A I J hJ M K hK
  refine ⟨asIso (completedLocalCohomologyToLimit A I J hJ M K hK 0) ≪≫ a ≪≫
    (supportTraceAdicEquiv A I J M).symm.toModuleIso, fun n ↦ ?_⟩
  have key : ∀ z : adicQuotientTorsionSubmodule A I J M,
      (I ^ n • (⊤ : Submodule A M)).mkQ ((supportTraceAdicEquiv A I J M).symm z).1 =
        AdicCompletion.eval I M n z.1 := by
    intro z
    have h2 : AdicCompletion.of I M ((supportTraceAdicEquiv A I J M).symm z).1 = z.1 := by
      rw [← supportTraceAdicEquiv_apply A I J M ((supportTraceAdicEquiv A I J M).symm z),
        LinearEquiv.apply_symm_apply]
    rw [← AdicCompletion.eval_of I M n, h2]
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  refine Eq.trans ?_ (ConcreteCategory.congr_hom (ha n)
    ((completedLocalCohomologyToLimit A I J hJ M K hK 0).hom x))
  exact key _

/-- **Stacks 0EEX.** Let `I` and `J` be ideals of a Noetherian ring `A` which is `I`-adically
complete, let `M` be a finite `A`-module and `Z = V(J)`. The degree-zero cohomology of the
derived `I`-adic completion `RΓ_Z(M)^∧` of local cohomology is the filtered colimit of
`H⁰_{V(J')}(M)` over the ideals `J' ⊆ J` with `V(J') ∩ V(I) = V(J) ∩ V(I)`.

The colimit is realized as the supremum `P` of the `J'`-power-torsion submodules `Γ_{J'}(M)`
of `M` (each `H⁰_{V(J')}(M)` is `Γ_{J'}(M)` by
`Stacks.Duality.supportLocalCohomology_zero_iso_torsion`; the index set is directed and the
supremum is the union of its terms by `Dualizing.iSup_primaryComponent_eq_supportTraceSubmodule`).
The isomorphism is the one induced by the comparison of Tag 0EEW with `lim H⁰_Z(M/IⁿM)`:
composing it with the inclusion into `M` and the projection to `M/IⁿM` gives the `n`-th limit
projection followed by the canonical map `H⁰_Z(M/IⁿM) ⟶ M/IⁿM`. Tag 0EEW part (1),
`Dualizing.isDerivedLimit_completedLocalCohomology`, identifies `RΓ_Z(M)^∧` with the derived
limit of the tower `n ↦ RΓ_Z(M/IⁿM)`. -/
@[stacks 0EEX]
theorem exists_iso_homology_zero_completedLocalCohomology [IsNoetherianRing A]
    (I J : Ideal A) [IsAdicComplete I A] (M : ModuleCat.{u} A) [Module.Finite A M]
    (P : Submodule A M)
    (hP : P = ⨆ (J' : Ideal A) (_ : J' ≤ J)
      (_ : PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)),
      Ideal.primaryComponent M J') :
    ∃ e : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        (completedLocalCohomology A I J I.fg_of_isNoetherianRing J.fg_of_isNoetherianRing M) ≅
          ModuleCat.of A P,
      ∀ n : ℕ, e.hom ≫ ModuleCat.ofHom P.subtype ≫
          ModuleCat.ofHom (I ^ n • (⊤ : Submodule A M)).mkQ =
        completedLocalCohomologyToLimit A I J J.fg_of_isNoetherianRing M _
            (isDerivedLimit_completedLocalCohomology A I J I.fg_of_isNoetherianRing
              J.fg_of_isNoetherianRing M) 0 ≫
          limit.π (adicQuotientLocalCohomologySystem A I J J.fg_of_isNoetherianRing M ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0) (Opposite.op n) ≫
          Stacks.Duality.supportLocalCohomologyToModule.{u, u} A J J.fg_of_isNoetherianRing
            ((adicQuotientModuleSystem A I M).obj
              (Opposite.op n)) :=
  exists_iso_homology_zero_of_isDerivedLimit A I J J.fg_of_isNoetherianRing M _
    (isDerivedLimit_completedLocalCohomology A I J I.fg_of_isNoetherianRing
      J.fg_of_isNoetherianRing M) P hP

end Limit

end Dualizing

end
