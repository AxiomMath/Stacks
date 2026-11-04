module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalSections.Tower
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.TorsionNakayama

/-!
# Krull's intersection theorem at a prime containing `f`, and the vanishing locus of a section

Let `A` be a Noetherian ring, `M` a finite `A`-module on which `f` is a nonzerodivisor, and `p`
a prime containing `f`. An element of `M` lying in `fⁿM` up to a factor outside `p`, for every
`n`, is annihilated by a factor outside `p`: the localization `M_p` has `⋂ₙ fⁿ M_p = 0`.

The proof is Nakayama's lemma applied to the submodule of all such elements. That submodule is
`f`-divisible up to factors outside `p` — this is where the nonzerodivisor hypothesis enters —
and it is finitely generated because `A` is Noetherian and `M` is finite, so
`Stacks.AlgebraicGeometry.CodimensionOneObstruction.exists_notMem_smul_eq_zero_of_mem`
applies with `s = f`.

The second half of the file records that the locus where a locally fractional section of `M̃`
vanishes is open, which is what turns the pointwise statement above into a statement about a
neighbourhood.

## Main definitions

* `Stacks.Algebraization.FormalSections.powDivisible` — the submodule of elements lying in every
  `fⁿM` up to a factor outside `p`.
* `Stacks.Algebraization.FormalSections.vanishingOpen` — the open locus on which a section
  vanishes.

## Main results

* `Stacks.Algebraization.FormalSections.exists_notMem_smul_eq_zero_of_forall_mem_powSmul`
* `Stacks.Algebraization.FormalSections.mem_vanishingOpen` and
  `Stacks.Algebraization.FormalSections.restrict_vanishingOpen_eq_zero`

## References

* [Stacks Project, Tag 00IP](https://stacks.math.columbia.edu/tag/00IP)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open PrimeSpectrum (basicOpen)
open Stacks.LocalCohomology

universe u v

namespace Stacks.Algebraization.FormalSections

variable {A : Type u} [CommRing A] (f : A) (M : ModuleCat.{v} A) (p : PrimeSpectrum A)

/-- The elements of `M` which, up to a factor outside `p`, lie in every `fⁿM`. -/
def powDivisible : Submodule A (M : Type v) where
  carrier := {m | ∀ n : ℕ, ∃ c ∈ p.asIdeal.primeCompl, c • m ∈ powSmul f M n}
  zero_mem' n := ⟨1, p.asIdeal.primeCompl.one_mem, by rw [smul_zero]; exact zero_mem _⟩
  add_mem' {x y} hx hy n := by
    obtain ⟨c, hc, hcx⟩ := hx n
    obtain ⟨d, hd, hdy⟩ := hy n
    refine ⟨c * d, p.asIdeal.primeCompl.mul_mem hc hd, ?_⟩
    have hsum : (c * d) • (x + y) = d • (c • x) + c • (d • y) := by
      simp only [smul_add, mul_smul]
      rw [smul_comm c d x]
    rw [hsum]
    exact add_mem (Submodule.smul_mem _ _ hcx) (Submodule.smul_mem _ _ hdy)
  smul_mem' r {x} hx n := by
    obtain ⟨c, hc, hcx⟩ := hx n
    refine ⟨c, hc, ?_⟩
    rw [smul_comm]
    exact Submodule.smul_mem _ _ hcx

/-- Membership in `powDivisible`: for every `n`, some factor outside `p` carries `m` into
`fⁿM`. -/
theorem mem_powDivisible {m : M} :
    m ∈ powDivisible f M p ↔ ∀ n : ℕ, ∃ c ∈ p.asIdeal.primeCompl, c • m ∈ powSmul f M n :=
  Iff.rfl

variable [IsNoetherianRing A] [Module.Finite A (M : Type v)] (hf : IsSMulRegular (M : Type v) f)

omit [IsNoetherianRing A] [Module.Finite A (M : Type v)] in
include hf in
/-- The submodule of `f`-power divisible elements is divisible by `f` up to factors outside
`p`. -/
theorem powDivisible_div {m : M} (hm : m ∈ powDivisible f M p) :
    ∃ m' ∈ powDivisible f M p, ∃ g : A, g ∉ p.asIdeal ∧ f • m' = g • m := by
  obtain ⟨c, hc, hcm⟩ := (mem_powDivisible f M p).1 hm 1
  obtain ⟨y, hy⟩ := (mem_powSmul f M).1 hcm
  rw [pow_one] at hy
  refine ⟨y, ?_, c, hc, hy⟩
  intro n
  obtain ⟨d, hd, hdm⟩ := (mem_powDivisible f M p).1 hm (n + 1)
  obtain ⟨z, hz⟩ := (mem_powSmul f M).1 hdm
  refine ⟨d, hd, (mem_powSmul f M).2 ⟨c • z, hf ?_⟩⟩
  change f • (f ^ n • (c • z)) = f • (d • y)
  rw [smul_smul, ← pow_succ', smul_comm (f ^ (n + 1)) c, hz, smul_comm c d, ← hy]
  exact smul_comm d f y

include hf in
/-- **Krull's intersection theorem at `p`.** If `f` lies in `p` and, for every `n`, some factor
outside `p` carries `m` into `fⁿM`, then some factor outside `p` annihilates `m`. -/
theorem exists_notMem_smul_eq_zero_of_forall_mem_powSmul (hfp : f ∈ p.asIdeal) {m : M}
    (hm : ∀ n : ℕ, ∃ c ∈ p.asIdeal.primeCompl, c • m ∈ powSmul f M n) :
    ∃ c : A, c ∉ p.asIdeal ∧ c • m = 0 := by
  have : p.asIdeal.IsPrime := p.2
  have hmP : m ∈ powDivisible f M p := (mem_powDivisible f M p).2 hm
  exact Stacks.AlgebraicGeometry.CodimensionOneObstruction.exists_notMem_smul_eq_zero_of_mem
    (powDivisible f M p) hfp (fun w hw ↦ powDivisible_div f M p hf hw) hmP

end Stacks.Algebraization.FormalSections

/-! ### The vanishing locus of a section -/

namespace Stacks.Algebraization.FormalSections

variable {A : Type u} [CommRing A] (M : ModuleCat.{v} A)
  {V : Opens (PrimeSpectrum.Top A)} (s : moduleSections M V)

/-- **The locus where a section vanishes is open.** -/
def vanishingOpen : Opens (PrimeSpectrum.Top A) where
  carrier := {q | ∃ h : q ∈ V, s.1 ⟨q, h⟩ = 0}
  is_open' := by
    rw [isOpen_iff_forall_mem_open]
    rintro q ⟨hqV, hq⟩
    obtain ⟨W, hqW, i, m, a, hma⟩ := s.2 ⟨q, hqV⟩
    obtain ⟨haq, hqa⟩ := hma ⟨q, hqW⟩
    have h0 : LocalizedModule.mk m (⟨a, haq⟩ : q.asIdeal.primeCompl) = 0 := by
      rw [← hqa]; exact hq
    obtain ⟨c, hc⟩ := (localizedModule_mk_eq_zero_iff m ⟨a, haq⟩).1 h0
    refine ⟨(W ⊓ basicOpen (c : A) : Opens (PrimeSpectrum.Top A)), ?_,
      (W ⊓ basicOpen (c : A) : Opens (PrimeSpectrum.Top A)).2, ⟨hqW, c.2⟩⟩
    rintro r ⟨hrW, hrc⟩
    refine ⟨i.le hrW, ?_⟩
    obtain ⟨har, hr⟩ := hma ⟨r, hrW⟩
    refine Eq.trans hr ?_
    exact (localizedModule_mk_eq_zero_iff m ⟨a, har⟩).2 ⟨⟨(c : A), hrc⟩, hc⟩

/-- The vanishing locus of a section over `V` is contained in `V`. -/
theorem vanishingOpen_le : vanishingOpen M s ≤ V := fun _ hq ↦ hq.1

/-- A point of `V` at which the section vanishes lies in its vanishing locus. -/
theorem mem_vanishingOpen {q : PrimeSpectrum A} (hq : q ∈ V) (h : s.1 ⟨q, hq⟩ = 0) :
    q ∈ vanishingOpen M s := ⟨hq, h⟩

/-- The restriction of a section to its vanishing locus is zero. -/
theorem restrict_vanishingOpen_eq_zero :
    moduleSectionsRestrict M (vanishingOpen_le M s) s = 0 :=
  ext_moduleSections fun x ↦ x.2.2

end Stacks.Algebraization.FormalSections

end
