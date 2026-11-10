module

public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.RingTheory.Rig.RigEtaleIsLocal
public import StacksFrontier.RingTheory.Rig.RigSmoothRigFlat
public import StacksFrontier.RingTheory.Restricted.RigSmoothCriteria
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.CombinedRigSmooth

/-!
# Pointwise descent of rig-smoothness and rig-étaleness

Let `φ : C → B` be an adic homomorphism of topologically finite type between Noetherian adic
topological rings. Suppose that for every ideal of definition `I` of `C` and every prime `𝔮` of
`B` not containing `I B` there is a Noetherian adic ring `A` with a continuous homomorphism
`ψ : B → A` such that `ψ` and `ψ ∘ φ` are rig-smooth and `𝔮` is the contraction of a prime of
`A`. Then `φ` is rig-smooth. The same holds with rig-étale in place of rig-smooth.

This is the ring-theoretic half of the proof of Stacks 0GH6.

## Main results

* `Rig.isRigSmooth_of_forall_prime_exists_rigSmooth`: the rig-smooth statement.
* `Rig.isRigEtale_of_forall_prime_exists_rigEtale`: the rig-étale statement.

## Implementation notes

Fix `I` and a completed polynomial presentation `P` of `B` over `(C, I)`. By the converse of
Stacks 0GAJ read at a single prime (`Rig.isRigSmooth_of_forall_prime`) it suffices to show, for
each prime `𝔮` of `B` off `V(I B)`, that `H⁻¹(NL^∧_{B/C})_𝔮` vanishes and `H⁰(NL^∧_{B/C})_𝔮` is
free. Take `A`, `ψ` and a prime `𝔭` of `A` over `𝔮`. In the six-term exact sequence of
Stacks 0ALM for `C → B → A`,

```
H⁻¹(NL^∧_{B/C} ⊗_B A) → H⁻¹(NL^∧_{A/C}) → H⁻¹(NL^∧_{A/B}) →
  H⁰(NL^∧_{B/C} ⊗_B A) → H⁰(NL^∧_{A/C}) → H⁰(NL^∧_{A/B}) → 0,
```

localized at `𝔭`, the terms of `NL^∧_{A/C}` and `NL^∧_{A/B}` have vanishing `H⁻¹` and free `H⁰`
by rig-smoothness (`Rig.subsingleton_hneg_and_free_hzero_localizedAtPrime_of_isRigSmooth`), and
the kernel of the first map vanishes by Stacks 0GH2. Hence `H⁻¹(NL^∧_{B/C} ⊗_B A)_𝔭 = 0` and
`H⁰(NL^∧_{B/C} ⊗_B A)_𝔭` is projective. As `A_𝔭` is flat over `B` (Stacks 0GH1, through
`Rig.flat_localization_atPrime_of_isRigSmooth`), `B_𝔮 → A_𝔭` is a faithfully flat local
homomorphism, and both conclusions descend to `𝔮`. In the rig-étale case `H⁰(NL^∧_{A/C})_𝔭`
vanishes, hence so does `H⁰(NL^∧_{B/C})_𝔮`, and a finite module vanishing off `V(I B)` is
killed by a power of `I B`.

## References

* [Stacks Project, Tag 0ALM](https://stacks.math.columbia.edu/tag/0ALM)
* [Stacks Project, Tag 0GAJ](https://stacks.math.columbia.edu/tag/0GAJ)
* [Stacks Project, Tag 0GH1](https://stacks.math.columbia.edu/tag/0GH1)
* [Stacks Project, Tag 0GH2](https://stacks.math.columbia.edu/tag/0GH2)
* [Stacks Project, Tag 0GH6](https://stacks.math.columbia.edu/tag/0GH6)
-/

@[expose] public noncomputable section

open TopologicalRing Rig.CompletedPolynomialPresentation
open scoped TensorProduct

universe u

namespace Rig

namespace PointwiseDescent

/-! ### Localized linear algebra -/

/-- A linear map which becomes injective after localization has localized kernel zero. -/
theorem localized_kernel_subsingleton {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (S : Submonoid R) (d : M →ₗ[R] N)
    (hd : Function.Injective (LocalizedModule.map S d)) :
    Subsingleton (LocalizedModule S (LinearMap.ker d)) := by
  have hinclusion := LocalizedModule.map_injective S (LinearMap.ker d).subtype
    Subtype.val_injective
  refine subsingleton_of_forall_eq 0 fun x ↦ hinclusion (hd ?_)
  induction x using LocalizedModule.induction_on with
  | h x t =>
    simp [LocalizedModule.map_mk]

/-- The second map of an exact sequence `L → M → N` is injective if `L` is a subsingleton. -/
private theorem injective_of_exact_of_subsingleton {R L M N : Type*} [CommRing R]
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N] [Module R L] [Module R M] [Module R N]
    [Subsingleton L] {f : L →ₗ[R] M} {g : M →ₗ[R] N} (h : Function.Exact f g) :
    Function.Injective g :=
  (LinearMap.injective_iff_eq_zero_of_exact h).mpr (LinearMap.ext fun y ↦ by
    rw [Subsingleton.elim y 0, map_zero]; rfl)

/-- A linear map whose localized kernel vanishes becomes injective after localization. -/
theorem localized_injective_of_kernel_subsingleton {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (S : Submonoid R)
    (f : M →ₗ[R] N) [Subsingleton (LocalizedModule S (LinearMap.ker f))] :
    Function.Injective (LocalizedModule.map S f) := by
  have hex : Function.Exact (LocalizedModule.map S (LinearMap.ker f).subtype)
      (LocalizedModule.map S f) :=
    LocalizedModule.map_exact S _ f (LinearMap.exact_subtype_ker_map f)
  exact injective_of_exact_of_subsingleton hex

/-- A module annihilated by an element of `S` has zero localization at `S`. -/
theorem localized_subsingleton_of_mem_annihilator {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (S : Submonoid R) (a : R) (ha : a ∈ S)
    (hann : a ∈ Module.annihilator R M) : Subsingleton (LocalizedModule S M) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  induction x using LocalizedModule.induction_on with
  | h x t =>
    apply LocalizedModule.eq_zero_of_smul_eq_zero a ha
    rw [LocalizedModule.smul'_mk, Module.mem_annihilator.mp hann x]
    exact LocalizedModule.zero_mk t

/-- If the localized target vanishes and the kernel is killed by an element of `S`, the
localized source vanishes. -/
theorem localized_source_subsingleton {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (S : Submonoid R)
    (f : M →ₗ[R] N) [Subsingleton (LocalizedModule S N)] (a : R) (ha : a ∈ S)
    (hann : a ∈ Module.annihilator R (LinearMap.ker f)) :
    Subsingleton (LocalizedModule S M) := by
  have := localized_subsingleton_of_mem_annihilator S a ha hann
  exact (localized_injective_of_kernel_subsingleton S f).subsingleton

/-- The kernel of a surjection between projective modules is projective. -/
theorem projective_of_shortExact {R M N L : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup L] [Module R M] [Module R N] [Module R L]
    [Module.Projective R N] [Module.Projective R L]
    (f : M →ₗ[R] N) (g : N →ₗ[R] L) (hinj : Function.Injective f) (hex : Function.Exact f g)
    (hsurj : Function.Surjective g) : Module.Projective R M := by
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property g (LinearMap.id : L →ₗ[R] L) hsurj
  let e := LinearEquiv.ofInjective f hinj
  have hrange : LinearMap.range f = LinearMap.ker g := (LinearMap.exact_iff.mp hex).symm
  let e' := e.trans (LinearEquiv.ofEq _ _ hrange)
  let π : N →ₗ[R] LinearMap.ker g :=
    (LinearMap.id - σ.comp g).codRestrict (LinearMap.ker g) (fun x ↦ by
      have h := LinearMap.congr_fun hσ (g x)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
      simp [h])
  refine Module.Projective.of_split f (e'.symm.toLinearMap.comp π) ?_
  ext x
  apply e'.injective
  apply Subtype.ext
  have hzero : g (f x) = 0 := (hex (f x)).mpr ⟨x, rfl⟩
  simp [π, e', e, hzero]

/-- In an exact sequence `L → M → N → K → 0` whose localization has `L` zero and `N`, `K`
projective, the localization of `M` is projective. -/
theorem localized_projective_of_exact {R L M N K : Type*} [CommRing R]
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N] [AddCommGroup K]
    [Module R L] [Module R M] [Module R N] [Module R K] (S : Submonoid R)
    (δ : L →ₗ[R] M) (f : M →ₗ[R] N) (g : N →ₗ[R] K)
    [Subsingleton (LocalizedModule S L)]
    [Module.Projective (Localization S) (LocalizedModule S N)]
    [Module.Projective (Localization S) (LocalizedModule S K)]
    (hδ : Function.Exact δ f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Module.Projective (Localization S) (LocalizedModule S M) := by
  have hex := LocalizedModule.map_exact S δ f hδ
  exact projective_of_shortExact (LocalizedModule.map S f) (LocalizedModule.map S g)
    (injective_of_exact_of_subsingleton (f := LocalizedModule.map S δ) hex)
    (LocalizedModule.map_exact S f g hfg) (LocalizedModule.map_surjective S g hg)

/-- Localization at a prime of `S` lying over a prime of `R` commutes with base change. -/
def localizedTensorEquiv {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal R) [q.IsPrime] (p : Ideal S) [p.IsPrime] [p.LiesOver q]
    (M : Type*) [AddCommGroup M] [Module R M] :
    letI := Localization.AtPrime.algebraOfLiesOver q p
    Localization.AtPrime p ⊗[Localization.AtPrime q] LocalizedModule q.primeCompl M
      ≃ₗ[Localization.AtPrime p] LocalizedModule p.primeCompl (S ⊗[R] M) := by
  letI := Localization.AtPrime.algebraOfLiesOver q p
  exact ((LocalizedModule.equivTensorProduct q.primeCompl M).baseChange
    (Localization.AtPrime q) (Localization.AtPrime p)).trans
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime q)
        (Localization.AtPrime p) (Localization.AtPrime p) M).trans
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S (Localization.AtPrime p)
          (Localization.AtPrime p) M).symm.trans
          (LocalizedModule.equivTensorProduct p.primeCompl (S ⊗[R] M)).symm))

/-- **Faithfully flat descent of the localized cohomology of a two-term complex.** Let `R → S`
be a ring map, `𝔭` a prime of `S` over the prime `𝔮` of `R` with `R_𝔮 → S_𝔭` flat, and let
`d : M → N` be a map of `R`-modules with finite cokernel, `R` Noetherian. If the localized kernel
of `S ⊗ d` vanishes at `𝔭` then the localized kernel of `d` vanishes at `𝔮`; if moreover the
localization of `S ⊗_R coker d` at `𝔭` is free, so is that of `coker d` at `𝔮`. -/
theorem localized_descent {R S M N : Type*} [CommRing R] [IsNoetherianRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (q : Ideal R) [q.IsPrime] (p : Ideal S) [p.IsPrime] [p.LiesOver q]
    (hflat : letI := Localization.AtPrime.algebraOfLiesOver q p
      Module.Flat (Localization.AtPrime q) (Localization.AtPrime p))
    (d : M →ₗ[R] N)
    (hneg : Subsingleton (LocalizedModule p.primeCompl (LinearMap.ker (d.baseChange S)))) :
    Subsingleton (LocalizedModule q.primeCompl (LinearMap.ker d)) := by
  let := Localization.AtPrime.algebraOfLiesOver q p
  have : IsLocalHom (algebraMap (Localization.AtPrime q) (Localization.AtPrime p)) :=
    Localization.isLocalHom_localRingHom q p (algebraMap R S) Ideal.LiesOver.over
  have : Module.FaithfullyFlat (Localization.AtPrime q) (Localization.AtPrime p) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj := localized_injective_of_kernel_subsingleton p.primeCompl (d.baseChange S)
  let source := localizedTensorEquiv q p M
  let target := localizedTensorEquiv q p N
  have commutes : (LocalizedModule.map p.primeCompl (d.baseChange S)).comp
      source.toLinearMap = target.toLinearMap.comp
        ((LocalizedModule.map q.primeCompl d).baseChange (Localization.AtPrime p)) := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul c x =>
      induction x using LocalizedModule.induction_on with
      | h x t =>
        simp only [localizedTensorEquiv, LinearMap.coe_comp, LinearEquiv.coe_coe,
          Function.comp_apply, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
          LocalizedModule.equivTensorProduct_apply_mk,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul,
          LocalizedModule.map_mk, source, target]
        have naturality : ∀ c' : Localization.AtPrime p,
            LocalizedModule.map p.primeCompl (d.baseChange S)
              ((LocalizedModule.equivTensorProduct p.primeCompl (S ⊗[R] M)).symm
                (c' ⊗ₜ[S] (1 ⊗ₜ[R] x))) =
            (LocalizedModule.equivTensorProduct p.primeCompl (S ⊗[R] N)).symm
              (c' ⊗ₜ[S] (1 ⊗ₜ[R] d x)) := by
          intro c'
          induction c' using Localization.induction_on with
          | H fraction =>
            rcases fraction with ⟨a, b⟩
            simp [LocalizedModule.equivTensorProduct_symm_apply_tmul]
        exact naturality _
    | add x y hx hy => simp_all
  have hbaseinj : Function.Injective
      ((LocalizedModule.map q.primeCompl d).baseChange (Localization.AtPrime p)) := by
    intro x y hxy
    apply source.injective
    apply hinj
    change ((LocalizedModule.map p.primeCompl (d.baseChange S)).comp source.toLinearMap) x =
      ((LocalizedModule.map p.primeCompl (d.baseChange S)).comp source.toLinearMap) y
    rw [commutes]
    exact congrArg target hxy
  exact localized_kernel_subsingleton _ _
    ((Module.FaithfullyFlat.lTensor_injective_iff_injective
      (Localization.AtPrime q) (Localization.AtPrime p) _).mp hbaseinj)

/-- Freeness of a localized finite module descends along a flat local homomorphism of
localizations at primes. -/
theorem localized_free_descent {R S M : Type*} [CommRing R] [IsNoetherianRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (q : Ideal R) [q.IsPrime] (p : Ideal S) [p.IsPrime] [p.LiesOver q]
    (hflat : letI := Localization.AtPrime.algebraOfLiesOver q p
      Module.Flat (Localization.AtPrime q) (Localization.AtPrime p)) :
    (Subsingleton (LocalizedModule p.primeCompl (S ⊗[R] M)) →
        Subsingleton (LocalizedModule q.primeCompl M)) ∧
      (Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl (S ⊗[R] M)) →
        Module.Free (Localization.AtPrime q) (LocalizedModule q.primeCompl M)) := by
  let := Localization.AtPrime.algebraOfLiesOver q p
  have : IsLocalHom (algebraMap (Localization.AtPrime q) (Localization.AtPrime p)) :=
    Localization.isLocalHom_localRingHom q p (algebraMap R S) Ideal.LiesOver.over
  have : Module.Flat (Localization.AtPrime q) (Localization.AtPrime p) := hflat
  have hd := subsingleton_and_free_of_flat_isLocalHom (Localization.AtPrime q)
    (Localization.AtPrime p) (LocalizedModule q.primeCompl M)
  let e := localizedTensorEquiv q p M
  exact ⟨fun h ↦ hd.1 e.injective.subsingleton, fun h ↦ hd.2 (Module.Free.of_equiv e.symm)⟩

/-! ### The six-term sequence localized at a prime -/

section SixTerm

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
  {base total : AdicFiniteTypeAlgebra.{u, u} R I}
  [Algebra base.carrier total.carrier] [IsScalarTower R base.carrier total.carrier]

/-- **The inner complex of Stacks 0ALM at a prime.** Let `base → total` be a morphism of
(Stacks 0AL4) over `(R, I)` presented over `base` by `ψ`, with `total` rig-smooth over `(R, I)`
and over `base`. At a prime `𝔭` of `total` off `V(I total)` at which `H⁻¹(NL^∧_{total/base})`
vanishes and `H⁰(NL^∧_{total/base})` is projective, `H⁻¹(NL^∧_{base/R} ⊗ total)` vanishes and
`H⁰(NL^∧_{base/R} ⊗ total)` is projective. -/
theorem localized_inner_of_localized_outer (P : CompletedPolynomialPresentation I base) (s : ℕ)
    (ψ : AdicCompletion.completedMvPolynomial base.adicIdeal (Fin s) →ₐ[base.carrier]
      total.carrier)
    (hψ : Function.Surjective (ψ.restrictScalars R))
    (F : Fin s → Derivation base.carrier
      (AdicCompletion.completedMvPolynomial base.adicIdeal (Fin s))
      (AdicCompletion.completedMvPolynomial base.adicIdeal (Fin s)))
    (hFc : ∀ j, @Continuous _ _
      (RestrictedPowerSeries.polynomialCompletionLimitTopology base.adicIdeal (Fin s))
      (RestrictedPowerSeries.polynomialCompletionLimitTopology base.adicIdeal (Fin s)) (F j))
    (hFp : ∀ (j : Fin s) (q : MvPolynomial (Fin s) base.carrier),
      F j (algebraMap (MvPolynomial (Fin s) base.carrier)
          (AdicCompletion.completedMvPolynomial base.adicIdeal (Fin s)) q) =
        algebraMap (MvPolynomial (Fin s) base.carrier)
          (AdicCompletion.completedMvPolynomial base.adicIdeal (Fin s))
          (MvPolynomial.pderiv j q))
    (hBC : IsRigSmooth (AdicFiniteTypeAlgebra.overBase (B := base) (C := total)))
    (htotal : IsRigSmooth total)
    (p : Ideal total.carrier) [p.IsPrime] (hp : ¬ total.adicIdeal ≤ p)
    (hneg : Subsingleton (LocalizedModule p.primeCompl
      (LinearMap.ker (outerDifferential s ψ hψ F))))
    (hzero : Module.Projective (Localization.AtPrime p) (LocalizedModule p.primeCompl
      ((Fin s → total.carrier) ⧸ LinearMap.range (outerDifferential s ψ hψ F)))) :
    Subsingleton (LocalizedModule p.primeCompl (LinearMap.ker
        (P.innerBaseChangeDifferential (C := total) (completedNaiveCotangentComplex base P)))) ∧
      Module.Projective (Localization.AtPrime p) (LocalizedModule p.primeCompl
        (NaiveCotangent.H₀ (NaiveCotangent.TwoTerm.ofFree
          (P.innerBaseChangeDifferential (C := total)
            (completedNaiveCotangentComplex base P))))) ∧
      (IsRigEtale total → Subsingleton (LocalizedModule p.primeCompl
        (NaiveCotangent.H₀ (NaiveCotangent.TwoTerm.ofFree
          (P.innerBaseChangeDifferential (C := total)
            (completedNaiveCotangentComplex base P)))))) := by
  classical
  let Pt := P.combinedPresentation s (ψ.restrictScalars R) hψ
  let KB := completedNaiveCotangentComplex base P
  let KC := completedNaiveCotangentComplex total Pt
  obtain ⟨hnegC, hzeroC⟩ :=
    subsingleton_hneg_and_free_hzero_localizedAtPrime_of_isRigSmooth total Pt htotal p hp
  have hzeroC' : Module.Projective (Localization.AtPrime p) (LocalizedModule p.primeCompl
      (NaiveCotangent.H₀ (NaiveCotangent.TwoTerm.ofFree (P.combinedDifferential s ψ hψ KC)))) :=
    @Module.Projective.of_free _ _ _ _ _ hzeroC
  have hnegC' : Subsingleton (LocalizedModule p.primeCompl
      (NaiveCotangent.H₁ (NaiveCotangent.TwoTerm.ofFree (P.combinedDifferential s ψ hψ KC)))) :=
    hnegC
  obtain ⟨δ, -, -, hexδ, hex0, hsurj⟩ := P.exists_sixTerm_exact_combined s ψ hψ KB KC F hFc hFp
  obtain ⟨n, hann⟩ := P.exists_pow_adicIdeal_le_annihilator_ker_onH₁_chainMapInl s ψ hψ KB KC hBC
  obtain ⟨x, hxI, hxp⟩ := IsConcreteLE.not_le_iff_exists.mp hp
  have hneg' : Subsingleton (LocalizedModule p.primeCompl
      (NaiveCotangent.H₁ (NaiveCotangent.TwoTerm.ofFree (outerDifferential s ψ hψ F)))) :=
    hneg
  refine ⟨?_, ?_, fun het ↦ ?_⟩
  · exact localized_source_subsingleton p.primeCompl _ (x ^ n) (p.primeCompl.pow_mem hxp n)
      (hann (Ideal.pow_mem_pow hxI n))
  · have hzero' : Module.Projective (Localization.AtPrime p) (LocalizedModule p.primeCompl
        (NaiveCotangent.H₀ (NaiveCotangent.TwoTerm.ofFree (outerDifferential s ψ hψ F)))) :=
      hzero
    exact localized_projective_of_exact p.primeCompl δ _ _ hexδ hex0 hsurj
  · obtain ⟨c, -, hc⟩ := (isRigEtale_iff_exists_annihilator_cohomology total Pt).mp het
    have hmem : x ^ c ∈ (I ^ c).map (algebraMap R total.carrier) := by
      rw [Ideal.map_pow]; exact Ideal.pow_mem_pow hxI c
    have hC0 : Subsingleton (LocalizedModule p.primeCompl
        (NaiveCotangent.H₀ (NaiveCotangent.TwoTerm.ofFree (P.combinedDifferential s ψ hψ KC)))) :=
      localized_subsingleton_of_mem_annihilator p.primeCompl (x ^ c)
        (p.primeCompl.pow_mem hxp c) (hc hmem)
    have hex : Function.Exact (LocalizedModule.map p.primeCompl δ) (LocalizedModule.map
        p.primeCompl (NaiveCotangent.chainMapInl _
          (P.combinedDifferential_comp_innerCotangentMap s ψ hψ KB KC)).onH₀) :=
      LocalizedModule.map_exact p.primeCompl δ _ hexδ
    exact (injective_of_exact_of_subsingleton hex).subsingleton

end SixTerm

/-! ### The pointwise conclusion -/

section Pointwise

variable {C B A : Type u}
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
  [IsNoetherianRing C]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
  [IsNoetherianRing B]
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [IsNoetherianRing A]

/-- **The cotangent cohomology of `B` over `C` at a prime dominated by a rig-smooth `C → B → A`.**
Let `φ : C → B` be adic of topologically finite type and `ψ : B → A` continuous with `ψ` and
`ψ ∘ φ` rig-smooth, all rings Noetherian adic. For a prime `𝔭` of `A` over a prime `𝔮` of `B`
not containing `I B`, `H⁻¹(NL^∧_{B/C})_𝔮` vanishes and `H⁰(NL^∧_{B/C})_𝔮` is free; if `ψ ∘ φ`
is rig-étale then `H⁰(NL^∧_{B/C})_𝔮` vanishes. -/
theorem localized_cotangent_of_isRigSmooth_comp
    (hC : TopologicalRing.IsAdic C) (hB : TopologicalRing.IsAdic B)
    (hA : TopologicalRing.IsAdic A)
    (φ : C →+* B) (hφ : Continuous φ) (hft : FiniteTypeAdicAlgebraForEveryIdeal φ)
    (ψ : B →+* A) (hψ : Continuous ψ) (hψs : RingHom.IsRigSmooth ψ)
    (hψφs : RingHom.IsRigSmooth (ψ.comp φ))
    (I : Ideal C) (hI : TopologicalRing.IsIdealOfDefinition I)
    (P : CompletedPolynomialPresentation I (adicFiniteTypeAlgebra φ hft I hI))
    (q : Ideal (adicFiniteTypeAlgebra φ hft I hI).carrier) [q.IsPrime]
    (hq : ¬ (adicFiniteTypeAlgebra φ hft I hI).adicIdeal ≤ q)
    (p : Ideal A) [p.IsPrime] (hpq : p.comap ψ = q) :
    Subsingleton (LocalizedModule q.primeCompl
        (completedNaiveCotangentComplex (adicFiniteTypeAlgebra φ hft I hI) P).Hneg) ∧
      Module.Free (Localization.AtPrime q) (LocalizedModule q.primeCompl
        (completedNaiveCotangentComplex (adicFiniteTypeAlgebra φ hft I hI) P).Hzero) ∧
      (RingHom.IsRigEtale (ψ.comp φ) → Subsingleton (LocalizedModule q.primeCompl
        (completedNaiveCotangentComplex (adicFiniteTypeAlgebra φ hft I hI) P).Hzero)) := by
  classical
  have hCw := weaklyAdmissible_of_isAdicRing hC
  have hBw := weaklyAdmissible_of_isAdicRing hB
  have hAw := weaklyAdmissible_of_isAdicRing hA
  have hftc := hψφs.1
  have hftψ := hψs.1
  have hJadic : _root_.IsAdic (I.map φ) := (hft I hI).1
  have hJ : TopologicalRing.IsIdealOfDefinition (I.map φ) := isIdealOfDefinition_of_isAdic hJadic
  let base := adicFiniteTypeAlgebra φ hft I hI
  let total := adicFiniteTypeAlgebra (ψ.comp φ) hftc I hI
  let fiber : AdicFiniteTypeAlgebra.{u, u} base.carrier base.adicIdeal :=
    adicFiniteTypeAlgebra ψ hftψ (I.map φ) hJ
  let : Algebra base.carrier total.carrier := (inferInstance : Algebra base.carrier fiber.carrier)
  let : IsScalarTower C base.carrier total.carrier :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsNoetherianRing base.carrier := inferInstanceAs (IsNoetherianRing B)
  let Q := completedPolynomialPresentation base.adicIdeal (Ideal.fg_of_isNoetherianRing _) fiber
  let KF := completedNaiveCotangentComplex fiber Q
  let KB := completedNaiveCotangentComplex base P
  let ψ' : AdicCompletion.completedMvPolynomial base.adicIdeal (Fin Q.variableCount)
      →ₐ[base.carrier] total.carrier := Q.toAlgHom
  have hψ' : Function.Surjective (ψ'.restrictScalars C) := Q.toAlgHom_surjective
  have houter : outerDifferential Q.variableCount ψ' hψ' (fun j => KF.partialDeriv j) =
      KF.differential := by
    refine LinearMap.ext fun z => ?_
    obtain ⟨w, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective (P := Q.extension) z
    funext j
    exact (cotangentMapOfDerivation_mk (Algebra.Extension.ofSurjective ψ' hψ')
      (KF.partialDeriv j) w).trans (congrFun (KF.differential_mk w).symm j)
  have hfiber : IsRigSmooth fiber :=
    hψs.forall_idealOfDefinition hψ hBw hAw hftψ (I.map φ) hJ
  have htotal : IsRigSmooth total :=
    hψφs.forall_idealOfDefinition (hψ.comp hφ) hCw hAw hftc I hI
  have hBC : IsRigSmooth (AdicFiniteTypeAlgebra.overBase (B := base) (C := total)) := by
    have heq : AdicFiniteTypeAlgebra.overBase (B := base) (C := total) = fiber := by
      apply CategoryTheory.ObjectProperty.FullSubcategory.ext
      rfl
    rw [heq]
    exact hfiber
  let p' : Ideal total.carrier := p
  have : p'.IsPrime := ‹p.IsPrime›
  have hp' : ¬ total.adicIdeal ≤ p' := by
    intro hle
    refine hq ?_
    rw [← hpq]
    change I.map φ ≤ p.comap ψ
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_map]
    exact hle
  let pF : Ideal fiber.carrier := p
  have : pF.IsPrime := ‹p.IsPrime›
  have hpF : ¬ fiber.adicIdeal ≤ pF := by
    intro hle
    refine hq ?_
    rw [← hpq]
    exact Ideal.map_le_iff_le_comap.mp hle
  obtain ⟨hnegF, hzeroF⟩ :=
    subsingleton_hneg_and_free_hzero_localizedAtPrime_of_isRigSmooth fiber Q hfiber pF hpF
  have hnegO : Subsingleton (LocalizedModule p'.primeCompl
      (LinearMap.ker (outerDifferential Q.variableCount ψ' hψ' (fun j => KF.partialDeriv j)))) := by
    rw [houter]; exact hnegF
  have hzeroO : Module.Projective (Localization.AtPrime p') (LocalizedModule p'.primeCompl
      ((Fin Q.variableCount → total.carrier) ⧸ LinearMap.range
        (outerDifferential Q.variableCount ψ' hψ' (fun j => KF.partialDeriv j)))) := by
    rw [houter]; exact @Module.Projective.of_free _ _ _ _ _ hzeroF
  obtain ⟨hnegI, hzeroI, hetI⟩ := localized_inner_of_localized_outer P Q.variableCount ψ' hψ'
    (fun j => KF.partialDeriv j) (fun j => KF.partialDeriv_continuous j)
    (fun j => KF.partialDeriv_polynomial j) hBC htotal p' hp' hnegO hzeroO
  -- flatness of `A_𝔭` over `B_𝔮`
  have : p'.LiesOver q := ⟨hpq.symm⟩
  let := Localization.AtPrime.algebraOfLiesOver q p'
  have hflatB : Module.Flat base.carrier (Localization.AtPrime pF) :=
    flat_localization_atPrime_of_isRigSmooth hB hJadic fiber hfiber pF hpF
  have hflat : Module.Flat (Localization.AtPrime q) (Localization.AtPrime p') :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime q) q.primeCompl
      (Localization.AtPrime p')).mpr hflatB
  -- the kernel of the base-changed differential
  have hE : (TensorProduct.piScalarRight base.carrier total.carrier total.carrier
      (Fin P.variableCount)).toLinearMap ∘ₗ (KB.differential.baseChange total.carrier) =
      P.innerBaseChangeDifferential (C := total) KB := by
    refine TensorProduct.AlgebraTensorModule.curry_injective ?_
    refine LinearMap.ext fun c => LinearMap.ext fun m => ?_
    funext j
    simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply]
    change _ = (c • ((Algebra.linearMap base.carrier total.carrier).compLeft (Fin P.variableCount)
      (KB.differential m))) j
    simp [Algebra.smul_def, mul_comm]
  have hker : LinearMap.ker (P.innerBaseChangeDifferential (C := total) KB) =
      LinearMap.ker (KB.differential.baseChange total.carrier) := by
    rw [← hE, LinearEquiv.ker_comp]
  rw [hker] at hnegI
  have hnegB := localized_descent q p' hflat KB.differential hnegI
  -- `H⁰`: the inner complex computes `A ⊗_B H⁰(NL^∧_{B/C})`
  let e := P.innerBaseChangeH0Equiv (C := total) KB
  let eL : LocalizedModule p'.primeCompl (total.carrier ⊗[base.carrier] KB.Hzero) ≃ₗ[
      Localization.AtPrime p'] LocalizedModule p'.primeCompl
        (NaiveCotangent.H₀ (NaiveCotangent.TwoTerm.ofFree
          (P.innerBaseChangeDifferential (C := total) KB))) :=
    LinearEquiv.ofBijective (LocalizedModule.map p'.primeCompl e.toLinearMap)
      ⟨LocalizedModule.map_injective _ _ e.injective,
        LocalizedModule.map_surjective _ _ e.surjective⟩
  have : Module.Finite base.carrier KB.Hzero := Module.Finite.quotient _ _
  have hdesc := localized_free_descent (S := total.carrier) (M := KB.Hzero) q p' hflat
  refine ⟨hnegB, hdesc.2 ?_, fun het ↦ hdesc.1 ?_⟩
  · have : Module.Projective (Localization.AtPrime p')
        (LocalizedModule p'.primeCompl (total.carrier ⊗[base.carrier] KB.Hzero)) :=
      have := hzeroI
      Module.Projective.of_equiv eL.symm
    exact Module.free_of_flat_of_isLocalRing
  · have htot : IsRigEtale total := by
      obtain ⟨hcI, hfinI, htotI⟩ := het.forall_idealOfDefinition (hψ.comp hφ) hC hA I hI
      let _ := hfinI
      let : Algebra C A := (ψ.comp φ).toAlgebra
      have heq : total = AdicFiniteTypeAlgebra.of (I := I) A hcI := by
        apply CategoryTheory.ObjectProperty.FullSubcategory.ext
        rfl
      rw [heq]
      exact htotI
    have := hetI htot
    exact eL.injective.subsingleton

end Pointwise

/-- A finite module which is `J`-power torsion is killed by a single power of `J`. -/
theorem exists_pow_le_annihilator_of_isIPowerTorsion {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] {J : Ideal R}
    (h : IsIPowerTorsion R M J) : ∃ c : ℕ, J ^ c ≤ Module.annihilator R M := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  choose n hn hmem using h
  refine ⟨s.sup n, fun a ha ↦ Module.mem_annihilator.mpr fun m ↦ ?_⟩
  have hm : m ∈ Submodule.span R (s : Set M) := hs ▸ Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx => exact hmem x a (Ideal.pow_le_pow_right (Finset.le_sup hx) ha)
  | zero => exact smul_zero a
  | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
  | smul r x _ hx => rw [smul_comm, hx, smul_zero]

end PointwiseDescent

open PointwiseDescent

variable {C B : Type u}
  [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
  [IsNoetherianRing C]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
  [IsNoetherianRing B]

/-- **Pointwise descent of rig-smoothness** (the ring-theoretic half of Stacks 0GH6). Let
`φ : C → B` be an adic homomorphism of topologically finite type of Noetherian adic rings.
Suppose that for every ideal of definition `I` of `C` and every prime `𝔮` of `B` not containing
`I B` there are a Noetherian adic ring `A` and a continuous `ψ : B → A` with `ψ` and `ψ ∘ φ`
rig-smooth, and a prime of `A` contracting to `𝔮`. Then `φ` is rig-smooth. -/
theorem isRigSmooth_of_forall_prime_exists_rigSmooth
    (hC : TopologicalRing.IsAdic C) (hB : TopologicalRing.IsAdic B)
    (φ : C →+* B) (hφ : Continuous φ) (hft : FiniteTypeAdicAlgebraForEveryIdeal φ)
    (h : ∀ (I : Ideal C), TopologicalRing.IsIdealOfDefinition I → ∀ (q : Ideal B), q.IsPrime →
      ¬ I.map φ ≤ q →
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
        (_ : IsLinearTopology A A) (_ : IsNoetherianRing A), TopologicalRing.IsAdic A ∧
        ∃ ψ : B →+* A, Continuous ψ ∧ RingHom.IsRigSmooth ψ ∧ RingHom.IsRigSmooth (ψ.comp φ) ∧
          ∃ p : Ideal A, p.IsPrime ∧ p.comap ψ = q) :
    RingHom.IsRigSmooth φ := by
  obtain ⟨I, hI, -⟩ := hC.1
  let P := completedPolynomialPresentation I (Ideal.fg_of_isNoetherianRing I)
    (adicFiniteTypeAlgebra φ hft I hI)
  refine ⟨hft, I, hI, isRigSmooth_of_forall_prime _ P fun q _ hq ↦ ?_⟩
  obtain ⟨A, _, _, _, _, _, hA, ψ, hψ, hψs, hψφs, p, hp, hpq⟩ := h I hI q ‹_› hq
  obtain ⟨h1, h2, -⟩ :=
    localized_cotangent_of_isRigSmooth_comp hC hB hA φ hφ hft ψ hψ hψs hψφs I hI P q hq p hpq
  exact ⟨h1, h2⟩

/-- **Pointwise descent of rig-étaleness** (the ring-theoretic half of Stacks 0GH6, rig-étale
case). Let `φ : C → B` be an adic homomorphism of topologically finite type of Noetherian adic
rings. Suppose that for every ideal of definition `I` of `C` and every prime `𝔮` of `B` not
containing `I B` there are a Noetherian adic ring `A` and a continuous `ψ : B → A` with `ψ` and
`ψ ∘ φ` rig-étale, and a prime of `A` contracting to `𝔮`. Then `φ` is rig-étale. -/
theorem isRigEtale_of_forall_prime_exists_rigEtale
    (hC : TopologicalRing.IsAdic C) (hB : TopologicalRing.IsAdic B)
    (φ : C →+* B) (hφ : Continuous φ) (hft : FiniteTypeAdicAlgebraForEveryIdeal φ)
    (h : ∀ (I : Ideal C), TopologicalRing.IsIdealOfDefinition I → ∀ (q : Ideal B), q.IsPrime →
      ¬ I.map φ ≤ q →
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
        (_ : IsLinearTopology A A) (_ : IsNoetherianRing A), TopologicalRing.IsAdic A ∧
        ∃ ψ : B →+* A, Continuous ψ ∧ RingHom.IsRigEtale ψ ∧ RingHom.IsRigEtale (ψ.comp φ) ∧
          ∃ p : Ideal A, p.IsPrime ∧ p.comap ψ = q) :
    RingHom.IsRigEtale φ := by
  obtain ⟨I, hI, -⟩ := hC.1
  let base := adicFiniteTypeAlgebra φ hft I hI
  let P := completedPolynomialPresentation I (Ideal.fg_of_isNoetherianRing I) base
  have hsmooth (D A : Type u) [CommRing D] [TopologicalSpace D] [IsTopologicalRing D]
      [IsLinearTopology D D] [IsNoetherianRing D] [CommRing A] [TopologicalSpace A]
      [IsTopologicalRing A] [IsLinearTopology A A] [IsNoetherianRing A] (ψ : D →+* A)
      (hψ : RingHom.IsRigEtale ψ) : RingHom.IsRigSmooth ψ := by
    let _ : Algebra D A := ψ.toAlgebra
    obtain ⟨hft', J, hJ, hc, hfin, hrig⟩ := hψ
    refine ⟨hft', J, hJ, ?_⟩
    let _ : Algebra.FiniteType (D ⧸ J) (A ⧸ J.map (algebraMap D A)) := hfin
    have heq : adicFiniteTypeAlgebra ψ hft' J hJ = AdicFiniteTypeAlgebra.of (I := J) A hc := by
      apply CategoryTheory.ObjectProperty.FullSubcategory.ext
      rfl
    rw [heq]
    exact isRigSmooth_of_isRigEtale _ hrig
  have hpt : ∀ (q : Ideal base.carrier) [q.IsPrime], ¬ base.adicIdeal ≤ q →
      Subsingleton (LocalizedModule q.primeCompl (completedNaiveCotangentComplex base P).Hneg) ∧
        Module.Free (Localization.AtPrime q)
          (LocalizedModule q.primeCompl (completedNaiveCotangentComplex base P).Hzero) ∧
        Subsingleton
          (LocalizedModule q.primeCompl (completedNaiveCotangentComplex base P).Hzero) := by
    intro q _ hq
    obtain ⟨A, _, _, _, _, _, hA, ψ, hψ, hψe, hψφe, p, hp, hpq⟩ := h I hI q ‹_› hq
    obtain ⟨h1, h2, h3⟩ := localized_cotangent_of_isRigSmooth_comp hC hB hA φ hφ hft ψ hψ
      (hsmooth B A ψ hψe) (hsmooth C A (ψ.comp φ) hψφe) I hI P q hq p hpq
    exact ⟨h1, h2, h3 hψφe⟩
  have hrs : IsRigSmooth base :=
    isRigSmooth_of_forall_prime base P fun q _ hq ↦ ⟨(hpt q hq).1, (hpt q hq).2.1⟩
  have : IsNoetherianRing base.carrier := inferInstanceAs (IsNoetherianRing B)
  have htor : IsIPowerTorsion base.carrier (completedNaiveCotangentComplex base P).Hzero
      base.adicIdeal := by
    rw [isIPowerTorsion_iff_localization_eq_zero _ _ _ (Ideal.fg_of_isNoetherianRing _)]
    intro q hq
    have := q.isPrime
    exact not_nontrivial_iff_subsingleton.mpr (hpt q.asIdeal hq).2.2
  have : Module.Finite base.carrier (completedNaiveCotangentComplex base P).Hzero :=
    Module.Finite.quotient _ _
  obtain ⟨c, hc⟩ := exists_pow_le_annihilator_of_isIPowerTorsion htor
  refine ⟨hft, I, hI, isRigEtaleOver_of_isRigEtale φ hft I hI
    ((isRigEtale_iff_isRigSmooth_and_annihilator base P).mpr ⟨hrs, c, ?_⟩)⟩
  rw [Ideal.map_pow]
  exact hc


end Rig

end
