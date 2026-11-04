module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Support
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.LocalCohomology.DimensionBoundUnconditional
public import StacksFrontier.RingTheory.LocalCohomology.LongExactSequence.Triangulated

/-!
# Hartshorne–Lichtenbaum vanishing

Let `A` be a Noetherian ring of dimension `d` and `I ⊆ A` an ideal. If `H^d_{V(I)}(M) = 0` for
some finite `A`-module `M` whose support contains every irreducible component of `Spec A` of
dimension `d`, then the cohomological dimension of `I` is strictly less than `d`.

Since `H^i_{V(I)}` vanishes above `d` on every finite module, the property `H^d_{V(I)}(N) = 0`
passes to quotients of `N` and to extensions, and it holds automatically when the support of `N`
misses every `d`-dimensional minimal prime. A finite module is built from the quotients `A/𝔭` by
iterated extensions, so it is enough to treat `N = A/𝔭`. For `𝔭` not minimal of dimension `d`
the support condition applies; for the remaining `𝔭`, membership of `𝔭` in the support of `M`
produces a nonzero map `M → A/𝔭`, whose image `J` is a nonzero ideal of the domain `A/𝔭`, so
`(A/𝔭)/J` has small support and `J` is a quotient of `M`.

## Main results

* `Stacks.LocalCohomology.cohomologicalDimension_lt_of_isZero_localCohomologyModule` —
  [Stacks Project, Tag 0EB2].
* `Stacks.LocalCohomology.isZero_localCohomologyModule_of_isQuotientPrime` — the dévissage of a
  finite module into prime quotients, carried out for the vanishing of a single local cohomology
  degree.
* `Stacks.LocalCohomology.supportDim_lt_of_notMem_support_of_top_minimalPrimes` — a module whose
  support avoids every minimal prime of full dimension has support of smaller dimension.

## Implementation notes

The dévissage is Mathlib's `IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime`, which
replaces the dévissage of coherent sheaves on a Noetherian scheme ([Stacks Project, Tag 01YM])
that the source invokes: the latter is available here only for sheaves on a scheme, and the
module statement is exactly what the argument consumes.

Everything happens in the single universe `u` of the ring, because the cohomological dimension of
Stacks 0DX8 is defined by the vanishing of the local cohomology of `A` itself in that universe.

## References

* [Stacks Project, Tag 0EB2](https://stacks.math.columbia.edu/tag/0EB2)
* [Stacks Project, Tag 0DXC](https://stacks.math.columbia.edu/tag/0DXC)
* [Stacks Project, Tag 0DX8](https://stacks.math.columbia.edu/tag/0DX8)
* [Stacks Project, Tag 01YM](https://stacks.math.columbia.edu/tag/01YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-! ### Closure properties of the vanishing of one local cohomology degree -/

/-- The vanishing of `H^i_{V(I)}` on the outer terms of a short exact sequence gives the
vanishing on the middle term. -/
theorem isZero_localCohomologyModule_X₂_of_shortExact
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (S : ShortComplex (ModuleCat.{u} A)) (i : ℤ) (hS : S.ShortExact)
    (h₁ : IsZero (localCohomologyModule A I hI S.X₁ i))
    (h₃ : IsZero (localCohomologyModule A I hI S.X₃ i)) :
    IsZero (localCohomologyModule A I hI S.X₂ i) := by
  have hex := exact_localCohomologyModuleMap A I hI S i hS
  have : Subsingleton (localCohomologyModule A I hI S.X₁ i) :=
    ModuleCat.isZero_iff_subsingleton.mp h₁
  have : Subsingleton (localCohomologyModule A I hI S.X₃ i) :=
    ModuleCat.isZero_iff_subsingleton.mp h₃
  have key : ∀ x : localCohomologyModule A I hI S.X₂ i, x = 0 := by
    intro x
    have hx : (localCohomologyModuleMap A I hI S.X₂ S.X₃ S.g i).hom x = 0 :=
      Subsingleton.elim _ _
    obtain ⟨z, hz⟩ := Set.mem_range.mp ((hex x).mp hx)
    rw [← hz, show z = 0 from Subsingleton.elim _ _, map_zero]
  exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b => by rw [key a, key b]⟩

/-- The vanishing of `H^i_{V(I)}` on the middle term of a short exact sequence, together with the
vanishing of `H^{i+1}_{V(I)}` on the submodule, gives the vanishing on the quotient. -/
theorem isZero_localCohomologyModule_X₃_of_shortExact
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (S : ShortComplex (ModuleCat.{u} A)) (i : ℤ) (hS : S.ShortExact)
    (h₂ : IsZero (localCohomologyModule A I hI S.X₂ i))
    (h₁ : IsZero (localCohomologyModule A I hI S.X₁ (i + 1))) :
    IsZero (localCohomologyModule A I hI S.X₃ i) := by
  have hsurj := surjective_localCohomologyModuleMap_of_isZero_X₁_succ A I hI S i hS h₁
  have : Subsingleton (localCohomologyModule A I hI S.X₂ i) :=
    ModuleCat.isZero_iff_subsingleton.mp h₂
  refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := hsurj a
  obtain ⟨y, rfl⟩ := hsurj b
  rw [Subsingleton.elim x y]

/-- The vanishing of `H^i_{V(I)}` on the outer terms of an exact sequence `0 → N₁ → N₂ → N₃ → 0`
of modules gives the vanishing on the middle term. -/
private theorem isZero_localCohomologyModule_of_exact
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG) (i : ℤ)
    {N₁ N₂ N₃ : Type u} [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂] [Module A N₂]
    [AddCommGroup N₃] [Module A N₃] (f : N₁ →ₗ[A] N₂) (g : N₂ →ₗ[A] N₃)
    (hfg : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g)
    (h₁ : IsZero (localCohomologyModule A I hI (ModuleCat.of A N₁) i))
    (h₃ : IsZero (localCohomologyModule A I hI (ModuleCat.of A N₃) i)) :
    IsZero (localCohomologyModule A I hI (ModuleCat.of A N₂) i) :=
  isZero_localCohomologyModule_X₂_of_shortExact A I hI
    (ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
      (by ext x; exact LinearMap.congr_fun hfg.linearMap_comp_eq_zero x))
    i (ModuleCat.shortComplex_shortExact _ hfg hf hg) h₁ h₃

/-- Above the Krull dimension of the ring, every local cohomology module of a finite module
vanishes. This is the first assertion of Stacks 0DXC combined with
`Module.supportDim_le_ringKrullDim`. -/
@[sga "2 V 3.1" "(i), special case"]
theorem isZero_localCohomologyModule_of_ringKrullDim_lt
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (d : ℕ) (hd : ringKrullDim A ≤ (d : WithBot ℕ∞)) (i : ℤ) (hi : (d : ℤ) < i) :
    IsZero (localCohomologyModule A I hI M i) := by
  refine localCohomologyModule_isZero_of_supportDim_lt.{u, u} A I hI M i ?_
  have hdi : d < i.toNat := by omega
  exact lt_of_le_of_lt ((Module.supportDim_le_ringKrullDim A M).trans hd)
    (by exact_mod_cast hdi)

/-! ### Supports avoiding the top-dimensional components -/

/-- A module whose support contains no minimal prime `𝔭` with `dim A/𝔭 = d` has support of
dimension less than `d`, provided `dim A ≤ d`: a chain of length `d` in the support would be as
long as a chain of primes can be, so its bottom is a minimal prime with `dim A/𝔭 = d`. -/
theorem supportDim_lt_of_notMem_support_of_top_minimalPrimes
    (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]
    (d : ℕ) (hd : ringKrullDim A ≤ (d : WithBot ℕ∞))
    (havoid : ∀ p : PrimeSpectrum A, IsMinimalPrime p.asIdeal →
      ringKrullDim (A ⧸ p.asIdeal) = (d : WithBot ℕ∞) → p ∉ Module.support A M) :
    Module.supportDim A M < (d : WithBot ℕ∞) := by
  by_contra h
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp (not_lt.mp h)
  let c : LTSeries (PrimeSpectrum A) := l.map Subtype.val (fun _ _ h ↦ h)
  have hc : c.length = d := hl
  have hmin : IsMin c.head := by
    intro q hq
    by_contra hnot
    have hh := (Order.LTSeries.length_le_krullDim (c.cons q (lt_of_le_not_ge hq hnot))).trans hd
    have hh' : (c.cons q (lt_of_le_not_ge hq hnot)).length ≤ d := by exact_mod_cast hh
    simp only [RelSeries.cons_length, hc] at hh'
    omega
  have hp : IsMinimalPrime c.head.asIdeal :=
    ⟨⟨c.head.isPrime, bot_le⟩, fun J hJ hle ↦ hmin (b := ⟨J, hJ.1⟩) hle⟩
  have hdim : ringKrullDim (A ⧸ c.head.asIdeal) = (d : WithBot ℕ∞) := by
    apply le_antisymm ((ringKrullDim_quotient_le _).trans hd)
    rw [ringKrullDim_quotient]
    let c' : LTSeries (PrimeSpectrum.zeroLocus (c.head.asIdeal : Set A)) :=
      { length := c.length
        toFun := fun i ↦ ⟨c i, c.head_le i⟩
        step := c.step }
    simpa only [← hc] using Order.LTSeries.length_le_krullDim c'
  exact havoid c.head hp hdim l.head.property

open TensorProduct in
/-- At a prime in the support of a finitely presented module there is a nonzero linear map from
the module to the residue domain `A/𝔭`: the generic fibre is a nonzero vector space over the
residue field, so some functional on it is nonzero, and a finitely presented module lifts such a
functional along the localization. -/
theorem exists_linearMap_quotient_ne_zero_of_mem_support
    (A : Type u) [CommRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.FinitePresentation A M]
    (p : PrimeSpectrum A) (hp : p ∈ Module.support A M) :
    ∃ f : M →ₗ[A] A ⧸ p.asIdeal, f ≠ 0 := by
  let B := A ⧸ p.asIdeal
  let K := p.asIdeal.ResidueField
  have : Nontrivial (K ⊗[A] M) :=
    (Module.mem_support_iff_nontrivial_residueField_tensorProduct p).mp hp
  obtain ⟨l, hl⟩ := exists_ne (0 : Module.Dual K (K ⊗[A] M))
  let g : M →ₗ[A] K := l.restrictScalars A ∘ₗ TensorProduct.mk A K M 1
  have hg : g ≠ 0 := fun h ↦ hl <| LinearMap.restrictScalars_injective A <| by
    ext a m
    have hm : l (1 ⊗ₜ[A] m) = 0 := LinearMap.congr_fun h m
    have ham : a ⊗ₜ[A] m = a • (1 ⊗ₜ[A] m) := by rw [smul_tmul', smul_eq_mul, mul_one]
    show l (a ⊗ₜ[A] m) = 0
    rw [ham, map_smul, hm, smul_zero]
  have hS : Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl = nonZeroDivisors B := by
    ext b
    simp only [Algebra.algebraMapSubmonoid, Submonoid.mem_map, mem_nonZeroDivisors_iff_ne_zero]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact mt (Ideal.Quotient.eq_zero_iff_mem).mp ha
    · intro hb
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
      exact ⟨a, mt (Ideal.Quotient.eq_zero_iff_mem).mpr hb, rfl⟩
  let : IsLocalization (Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl) K := by
    rw [hS]
    infer_instance
  let q : B →ₗ[A] K := (IsScalarTower.toAlgHom A B K).toLinearMap
  obtain ⟨f, s, hf⟩ :=
    Module.FinitePresentation.exists_lift_of_isLocalizedModule p.asIdeal.primeCompl q g
  refine ⟨f, fun h ↦ hg (LinearMap.ext fun m ↦ ?_)⟩
  subst h
  have hm := LinearMap.congr_fun hf m
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero, LinearMap.smul_apply] at hm
  exact (IsLocalizedModule.smul_inj q s _ _).mp (by simpa using hm.symm)

/-- A minimal prime `𝔮` in the support of `A/𝔭` is equal to `𝔭`. -/
private theorem eq_of_mem_support_quotient_of_isMinimalPrime
    {A : Type u} [CommRing A] (p q : PrimeSpectrum A) (hq : IsMinimalPrime q.asIdeal)
    (h : q ∈ Module.support A (A ⧸ p.asIdeal)) : p.asIdeal = q.asIdeal := by
  have hpq : p.asIdeal ≤ q.asIdeal := (PrimeSpectrum.mem_zeroLocus q (p.asIdeal : Set A)).mp
    (by simpa [Module.support_eq_zeroLocus, Ideal.annihilator_quotient] using h)
  exact le_antisymm hpq (hq.2 ⟨p.isPrime, bot_le⟩ hpq)

/-- The image of a nonzero map `M → A/𝔭` is a nonzero ideal of the domain `A/𝔭`, so the quotient
by it has support of dimension less than `dim A`. -/
theorem supportDim_quotient_range_lt_of_ne_zero
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (M : Type v) [AddCommGroup M] [Module A M] (p : PrimeSpectrum A)
    (f : M →ₗ[A] A ⧸ p.asIdeal) (hf : f ≠ 0)
    (d : ℕ) (hd : ringKrullDim A ≤ (d : WithBot ℕ∞)) :
    Module.supportDim A ((A ⧸ p.asIdeal) ⧸ LinearMap.range f) < (d : WithBot ℕ∞) := by
  let B := A ⧸ p.asIdeal
  let J := LinearMap.range f
  obtain ⟨m, hm⟩ : ∃ m : M, f m ≠ 0 := not_forall.mp fun h ↦ hf (LinearMap.ext h)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (f m)
  have haJ : (Ideal.Quotient.mk p.asIdeal a : B) ∈ J := by rw [ha]; exact ⟨m, rfl⟩
  have ha_not : a ∉ p.asIdeal := fun h =>
    hm (ha ▸ (Ideal.Quotient.eq_zero_iff_mem).mpr h)
  apply supportDim_lt_of_notMem_support_of_top_minimalPrimes A (B ⧸ J) d hd
  intro q hqmin _ hq
  have hqB : q ∈ Module.support A B :=
    Module.support_subset_of_surjective J.mkQ (Submodule.mkQ_surjective J) hq
  have heq := eq_of_mem_support_quotient_of_isMinimalPrime p q hqmin hqB
  have haann : a ∈ Module.annihilator A (B ⧸ J) := by
    rw [Module.mem_annihilator]
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [← Submodule.Quotient.mk_smul]
      apply (Submodule.Quotient.mk_eq_zero J).mpr
      have hcomm : a • (Ideal.Quotient.mk p.asIdeal t : B) =
          t • (Ideal.Quotient.mk p.asIdeal a : B) := by
        simp [Algebra.smul_def, mul_comm]
      rw [hcomm]
      exact J.smul_mem t haJ
  have ha_q : a ∈ q.asIdeal :=
    (PrimeSpectrum.mem_zeroLocus q (Module.annihilator A (B ⧸ J) : Set A)).mp
      (by simpa [Module.support_eq_zeroLocus] using hq) haann
  exact ha_not (heq ▸ ha_q)

/-! ### The dévissage -/

/-- The image of a map out of a module with vanishing `H^d_{V(I)}` again has vanishing
`H^d_{V(I)}`, because it is a quotient and `H^{d+1}_{V(I)}` vanishes everywhere. -/
theorem isZero_localCohomologyModule_range
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (d : ℕ) (hd : ringKrullDim A ≤ (d : WithBot ℕ∞))
    (X Y : ModuleCat.{u} A) [Module.Finite A X] (f : X →ₗ[A] Y)
    (hX : IsZero (localCohomologyModule A I hI X (d : ℤ))) :
    IsZero (localCohomologyModule A I hI (ModuleCat.of A (LinearMap.range f)) (d : ℤ)) := by
  have hS := LinearMap.shortExact_shortComplexKer (LinearMap.surjective_rangeRestrict f)
  refine isZero_localCohomologyModule_X₃_of_shortExact A I hI _ (d : ℤ) hS hX ?_
  exact isZero_localCohomologyModule_of_ringKrullDim_lt A I hI
    (ModuleCat.of A (LinearMap.ker f.rangeRestrict)) d hd ((d : ℤ) + 1) (by omega)

/-- `H^d_{V(I)}(A/𝔭) = 0` for a prime `𝔭` lying in the support of `M`: a nonzero map `M → A/𝔭`
has for image a nonzero ideal `J`, which inherits the vanishing from `M`, while `(A/𝔭)/J` has
support of dimension below `d`. -/
theorem isZero_localCohomologyModule_quotient_of_mem_support
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (d : ℕ) (hd : ringKrullDim A ≤ (d : WithBot ℕ∞))
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (hM : IsZero (localCohomologyModule A I hI M (d : ℤ)))
    (p : PrimeSpectrum A) (hp : p ∈ Module.support A M)
    (N : ModuleCat.{u} A) (e : N ≃ₗ[A] A ⧸ p.asIdeal) :
    IsZero (localCohomologyModule A I hI N (d : ℤ)) := by
  have : Module.Finite A N := Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  have := Module.finitePresentation_of_finite A M
  obtain ⟨g, hg⟩ := exists_linearMap_quotient_ne_zero_of_mem_support A M p hp
  let f : M →ₗ[A] N := e.symm.toLinearMap.comp g
  have hf : f ≠ 0 := fun h ↦ hg <| LinearMap.ext fun x ↦ by
    simpa [f] using congrArg e (LinearMap.congr_fun h x)
  let J := LinearMap.range f
  have hJ : IsZero (localCohomologyModule A I hI (ModuleCat.of A J) (d : ℤ)) :=
    isZero_localCohomologyModule_range A I hI d hd M N f hM
  have : Module.Finite A (N ⧸ J) :=
    Module.Finite.of_surjective J.mkQ (Submodule.mkQ_surjective J)
  have hQ : IsZero (localCohomologyModule A I hI (ModuleCat.of A (N ⧸ J)) (d : ℤ)) := by
    refine localCohomologyModule_isZero_of_supportDim_lt.{u, u} A I hI _ (d : ℤ) ?_
    have eQ : (N ⧸ J) ≃ₗ[A] ((A ⧸ p.asIdeal) ⧸ LinearMap.range g) :=
      Submodule.Quotient.equiv J (LinearMap.range g) e (by
        simp only [J, f, LinearMap.range_comp, Submodule.map_equiv_eq_comap_symm]
        ext x
        show e (e.symm x) ∈ LinearMap.range g ↔ x ∈ LinearMap.range g
        simp)
    rw [Int.toNat_natCast, Module.supportDim_eq_of_equiv eQ]
    exact supportDim_quotient_range_lt_of_ne_zero A M p g hg d hd
  exact isZero_localCohomologyModule_of_exact I hI (d : ℤ) J.subtype J.mkQ
    (LinearMap.exact_subtype_mkQ J) J.subtype_injective (Submodule.mkQ_surjective J) hJ hQ

/-- `H^d_{V(I)}(A/𝔮) = 0` for every prime `𝔮`. Either `𝔮` is minimal with `dim A/𝔮 = d`, when
the support hypothesis on `M` applies, or the support of `A/𝔮` avoids all those primes and the
dimension bound of Stacks 0DXC applies. -/
theorem isZero_localCohomologyModule_quotient_prime
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (d : ℕ) (hd : ringKrullDim A ≤ (d : WithBot ℕ∞))
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (hM : ∀ p : PrimeSpectrum A, IsMinimalPrime p.asIdeal →
      ringKrullDim (A ⧸ p.asIdeal) = (d : WithBot ℕ∞) → p ∈ Module.support A M)
    (hvan : IsZero (localCohomologyModule A I hI M (d : ℤ)))
    (q : PrimeSpectrum A) (N : ModuleCat.{u} A) (e : N ≃ₗ[A] A ⧸ q.asIdeal) :
    IsZero (localCohomologyModule A I hI N (d : ℤ)) := by
  have : Module.Finite A N := Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  by_cases htop : IsMinimalPrime q.asIdeal ∧
      ringKrullDim (A ⧸ q.asIdeal) = (d : WithBot ℕ∞)
  · exact isZero_localCohomologyModule_quotient_of_mem_support A I hI d hd M hvan q
      (hM q htop.1 htop.2) N e
  · have hav : ∀ p : PrimeSpectrum A, IsMinimalPrime p.asIdeal →
        ringKrullDim (A ⧸ p.asIdeal) = (d : WithBot ℕ∞) →
          p ∉ Module.support A (A ⧸ q.asIdeal) := by
      intro p hp hdp hpsupp
      have hqeq : q = p :=
        PrimeSpectrum.ext (eq_of_mem_support_quotient_of_isMinimalPrime q p hp hpsupp)
      exact htop (hqeq ▸ ⟨hp, hdp⟩)
    refine localCohomologyModule_isZero_of_supportDim_lt.{u, u} A I hI N (d : ℤ) ?_
    rw [Int.toNat_natCast, Module.supportDim_eq_of_equiv e]
    exact supportDim_lt_of_notMem_support_of_top_minimalPrimes A (A ⧸ q.asIdeal) d hd hav

/-- **Dévissage for the vanishing of one local cohomology degree.** If `H^d_{V(I)}` vanishes on
every finite module isomorphic to some `A/𝔮`, and `H^{d+1}_{V(I)}` vanishes on all finite
modules, then `H^d_{V(I)}` vanishes on every finite module. -/
theorem isZero_localCohomologyModule_of_isQuotientPrime
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG) (d : ℕ)
    (X : ModuleCat.{u} A) [Module.Finite A X]
    (hprime : ∀ (N : ModuleCat.{u} A) [Module.Finite A N] (q : PrimeSpectrum A),
      (N ≃ₗ[A] A ⧸ q.asIdeal) → IsZero (localCohomologyModule A I hI N (d : ℤ))) :
    IsZero (localCohomologyModule A I hI X (d : ℤ)) := by
  refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime A (M := X)
    (motive := fun N _ _ _ =>
      IsZero (localCohomologyModule A I hI (ModuleCat.of A N) (d : ℤ)))
    inferInstance ?_ ?_ ?_
  · exact fun N _ _ _ _ ↦
      isZero_homology_localCohomology_of_subsingleton.{u, u} A I hI (ModuleCat.of A N) (d : ℤ)
  · exact fun N _ _ _ q e ↦ hprime (ModuleCat.of A N) q e
  · intro N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ f g hf hg hfg h₁ h₃
    exact isZero_localCohomologyModule_of_exact I hI (d : ℤ) f g hfg hf hg h₁ h₃

/-! ### Hartshorne–Lichtenbaum vanishing -/

/-- **Stacks Project, Tag 0EB2 (Hartshorne–Lichtenbaum vanishing).** Let `A` be a Noetherian ring
of dimension `d` and let `I ⊆ A` be an ideal. If `H^d_{V(I)}(M) = 0` for some finite `A`-module
`M` whose support contains every irreducible component of `Spec A` of dimension `d`, then the
cohomological dimension of `I` in `A` is strictly less than `d`. -/
@[stacks 0EB2]
theorem cohomologicalDimension_lt_of_isZero_localCohomologyModule
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (d : ℕ) (hd : ringKrullDim A = (d : WithBot ℕ∞)) (I : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (hM : ∀ p : PrimeSpectrum A, IsMinimalPrime p.asIdeal →
      ringKrullDim (A ⧸ p.asIdeal) = (d : WithBot ℕ∞) → p ∈ Module.support A M)
    (hvan : IsZero
      (localCohomologyModule A I (Ideal.fg_of_isNoetherianRing I) M (d : ℤ))) :
    cohomologicalDimension A I (Ideal.fg_of_isNoetherianRing I) < (d : ℤ) := by
  set hI := Ideal.fg_of_isNoetherianRing I
  have hA : IsZero (localCohomologyModule A I hI (ModuleCat.of A A) (d : ℤ)) :=
    isZero_localCohomologyModule_of_isQuotientPrime A I hI d (ModuleCat.of A A)
      fun N _ q e => isZero_localCohomologyModule_quotient_prime A I hI d hd.le M hM hvan q N e
  have hbound : IsLocalCohomologyBound A I hI ((d : ℤ) - 1) := by
    refine ⟨by omega, fun i hi => ?_⟩
    rcases eq_or_lt_of_le (show (d : ℤ) ≤ i by omega) with heq | hlt
    · exact heq ▸ hA
    · exact isZero_localCohomologyModule_of_ringKrullDim_lt A I hI (ModuleCat.of A A) d hd.le i hlt
  have := cohomologicalDimension_le A I hI _ hbound
  omega

end Stacks.LocalCohomology

end
