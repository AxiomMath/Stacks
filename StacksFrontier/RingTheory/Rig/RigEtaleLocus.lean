module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Rig.BaseChangeAlgEquiv
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.Completion
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.SixTerm
public import StacksFrontier.RingTheory.Rig.RigEtaleBaseChange
public import StacksFrontier.RingTheory.Rig.RigEtaleCriterion

/-!
# Rig-étaleness of a completion and étaleness off the ideal of definition

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `B` a finite type `A`-algebra.  Write
`B^ = B^∧_{IB}` for the `I`-adic completion, an object of the category of Stacks 0AL4 by
Stacks 0AJQ.  This file relates rig-étaleness of `B^` over `(A, I)` to étaleness of
`Spec(B) → Spec(A)` over the open `Spec(A) ∖ V(I)`:

* if `Spec(B) → Spec(A)` is étale over `Spec(A) ∖ V(I)`, then `B^` is rig-étale;
* conversely, if `B^` is rig-étale, then there is `g ∈ 1 + IB` such that `Spec(B_g)` is étale
  over `Spec(A) ∖ V(I)`.

The element `g` cannot be dispensed with: rig-étaleness only sees `B` through its completion,
and a power of `I` annihilating a finite `B`-module *after* completion annihilates it on the
nose only up to the submodule `⋂ₙ (IB)ⁿ M`, which Nakayama's lemma kills after inverting one
element of `1 + IB`.

## Main definitions

* `Rig.IsEtaleOutside I B`: `Spec(B) → Spec(A)` is étale over `Spec(A) ∖ V(I)`, that is, the
  preimage of the complement of `V(I)` lies in the étale locus of `B` over `A`.

## Main results

* `Rig.isRigEtale_adicCompletionObj_iff`: the pivot. Rig-étaleness of `B^` over `(A, I)` is
  the existence of a `c` with `Iᶜ B^` annihilating both `B^ ⊗_B H¹(L_{B/A})` and
  `B^ ⊗_B Ω_{B/A}`.  This combines **Stacks 0GAF** — the completed naive cotangent complex of
  `B^` is `NL(α) ⊗_B B^` — with **Stacks 0AJU, (1) ⇔ (3)** and flatness of `B^` over `B`
  (**Stacks 00MB**).
* `Rig.isRigEtale_adicCompletionObj_of_isEtaleOutside`: **Stacks 0ALQ, part (1)**.
* `Rig.exists_isEtaleOutside_localization_of_isRigEtale_adicCompletionObj`:
  **Stacks 0ALQ, part (2)**.
* `Rig.isEtaleOutside_iff_isRigEtale_adicCompletionObj`: **Stacks 0ALQ**, the two parts
  together.
* `Rig.isRigEtale_of_algEquiv`: rig-étaleness only depends on the isomorphism class of an
  object of `Rig.AdicFiniteTypeAlgebra A I`.
* `Rig.isRigEtale_of_isEtaleOutside_of_algEquiv`: **Stacks 0AKG**, the implication from its
  condition (8) to the equivalent conditions of Stacks 0AJU.

## Implementation notes

"The equivalent conditions of Stacks 0AJU" are taken in the form of their first condition,
`Rig.IsRigEtale` (**Stacks 0GAY**), which is how the library states them; the passage to the
cohomological condition (3) is `Rig.isRigEtale_iff_exists_annihilator_cohomology`.

Étaleness over `Spec(A) ∖ V(I)` is phrased with Mathlib's `Algebra.etaleLocus`, so it is
étaleness at every prime of `B` not lying over `V(I)`, in Mathlib's sense of étale at a prime
(formal étaleness of the local ring).  `Rig.isEtaleOutside_iff` is the elementwise form.  The
conclusion of part (2) is `Rig.IsEtaleOutside I (Localization.Away g)` — literally the same
predicate for the algebra `B_g`, as in the source — which is tied to the primes of `B` in
`D(g)` by `Algebra.etaleLocus_comap_of_isLocalization`.

The pivot runs over a *finite* presentation `G : Algebra.Generators A B (Fin n)`: the comparison
of Stacks 0GAF is stated for such a presentation, and `Algebra.FiniteType.iff_exists_generators`
produces one.  The two cohomology modules of `NL(α)` are then identified with the
presentation-independent `Algebra.H1Cotangent A B` and `Ω_{B/A}` by
`Algebra.Generators.equivH1Cotangent` and by right exactness of `NL(α) → Ω_{B/A}`.

`NaiveCotangent.ChainMap.bijective_onH₁` and `NaiveCotangent.ChainMap.bijective_onH₀` are the
public counterparts of `Rig.surjective_onH₁_of_surjective_f₁` and
`Rig.bijective_onH₀_of_surjective_f₁` in
`StacksFrontier.RingTheory.Rig.NaiveCotangent.BaseChangeComparison`, which are `private` there and
so unavailable; they are proved from the public two-term API of
`StacksFrontier.RingTheory.Rig.NaiveCotangent.SixTerm` (`ChainMap.comm_apply`,
`ChainMap.onH₀_mkQ`, `NaiveCotangent.surjective_onH₀`), which is also what that file's private
versions use.

Nakayama's lemma is used in Mathlib's form
`Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`, which is the clause of
Stacks 00DV producing an annihilator in `1 + I`; the other clauses of 00DV are in
`StacksCore.RingTheory.Nakayama` and are not of this shape.

Condition (8) of Stacks 0AKG asks for an isomorphism `B ≅ C^∧` rather than for `B` to *be* a
completion, so it needs rig-étaleness to be invariant under isomorphism of objects.  That is
`Rig.isRigEtale_of_algEquiv`, obtained from **Stacks 0GB2** by reading an isomorphism
`B ≅ C` as an identification of `B` with the completed base change of `C` along the identity
of `A`: the base change is `(C ⊗_A A)^∧_I`, which the right unitor and the completeness of `C`
identify with `C`.  Only the implication from condition (8) is proved here; the converse over a
principal ideal is
`Rig.exists_isEtaleOutside_finiteType_algEquiv_of_isRigEtale_principal` in
`StacksFrontier.RingTheory.Rig.Algebraization.EtaleOutside`, and over a general ideal it rests on
the algebraization Lemma 0AKA, which this library does not carry.

## References

* [Stacks Project, Tag 0ALQ](https://stacks.math.columbia.edu/tag/0ALQ)
* [Stacks Project, Tag 0AJU](https://stacks.math.columbia.edu/tag/0AJU)
* [Stacks Project, Tag 0GAF](https://stacks.math.columbia.edu/tag/0GAF)
* [Stacks Project, Tag 00MB](https://stacks.math.columbia.edu/tag/00MB)
* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
* [Stacks Project, Tag 0AKG](https://stacks.math.columbia.edu/tag/0AKG)
* [Stacks Project, Tag 0GB2](https://stacks.math.columbia.edu/tag/0GB2)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v

/-! ## Generic tools -/

namespace NaiveCotangent.ChainMap

variable {S : Type*} [CommRing S] {X Y : TwoTerm S}

/-- A chain map of two-term complexes which is bijective in degree `1` and injective in degree
`0` is bijective on `H₁ = ker d`: a cycle of the target lifts, and its lift is a cycle because
the boundary of the lift dies in degree `0`. -/
public theorem bijective_onH₁ (f : ChainMap X Y)
    (h₁ : Function.Bijective f.f₁) (h₀ : Function.Injective f.f₀) :
    Function.Bijective f.onH₁ := by
  refine ⟨fun x y hxy => Subtype.ext (h₁.1 (congrArg Subtype.val hxy)), ?_⟩
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := h₁.2 y
  have hx : X.d x = 0 := h₀ (by
    rw [map_zero, ← ChainMap.comm_apply]; exact hy)
  exact ⟨⟨x, hx⟩, rfl⟩

/-- A chain map of two-term complexes which is surjective in degree `1` and bijective in degree
`0` is bijective on `H₀ = coker d`: an element of the source whose image is a boundary is
itself the boundary of any lift of the witness. -/
public theorem bijective_onH₀ (f : ChainMap X Y)
    (h₁ : Function.Surjective f.f₁) (h₀ : Function.Bijective f.f₀) :
    Function.Bijective f.onH₀ := by
  refine ⟨?_, _root_.NaiveCotangent.surjective_onH₀ f h₀.2⟩
  rw [injective_iff_map_eq_zero]
  intro xbar hxbar
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range X.d) xbar
  rw [ChainMap.onH₀_mkQ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hxbar
  obtain ⟨y, hy⟩ := hxbar
  obtain ⟨z, hz⟩ := h₁ y
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨z, h₀.1 ?_⟩
  rw [← ChainMap.comm_apply, hz]
  exact hy

end NaiveCotangent.ChainMap

/-- Exactness is preserved by replacing the middle term by an isomorphic one. -/
public theorem Function.Exact.linearEquiv_comp {R M N N' P : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    [AddCommGroup P] [Module R P] (e : N ≃ₗ[R] N') {c : M →ₗ[R] N} {k : N →ₗ[R] P}
    (h : Function.Exact c k) :
    Function.Exact (e.toLinearMap ∘ₗ c) (k ∘ₗ e.symm.toLinearMap) := by
  rw [LinearMap.exact_iff, LinearMap.ker_comp, LinearMap.range_comp,
    LinearMap.exact_iff.mp h, Submodule.map_equiv_eq_comap_symm]

/-- The cokernel of the base change of a linear map is the base change of its cokernel. -/
public def LinearMap.baseChangeCokerEquiv {R : Type*} [CommRing R] (S : Type*) [CommRing S]
    [Algebra R S] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    (S ⊗[R] N ⧸ LinearMap.range (LinearMap.baseChange S f)) ≃ₗ[S]
      S ⊗[R] (N ⧸ LinearMap.range f) := by
  have he : Function.Exact (LinearMap.baseChange S f)
      (LinearMap.baseChange S (Submodule.mkQ (LinearMap.range f))) :=
    lTensor_exact S (LinearMap.exact_iff.mpr (Submodule.ker_mkQ _))
      (Submodule.mkQ_surjective _)
  exact he.linearEquivOfSurjective
    (LinearMap.lTensor_surjective S (Submodule.mkQ_surjective _))

/-- The étale locus is compatible with localization away from an element: a prime of `A_f` is
étale over `R` exactly when the prime of `A` below it is.  This is the analogue for the étale
locus of Mathlib's `Algebra.smoothLocus_comap_of_isLocalization`. -/
public theorem Algebra.etaleLocus_comap_of_isLocalization {R A Af : Type*} [CommRing R]
    [CommRing A] [CommRing Af] [Algebra R A] [Algebra A Af] [Algebra R Af]
    [IsScalarTower R A Af] (f : A) [IsLocalization.Away f Af] :
    PrimeSpectrum.comap (algebraMap A Af) ⁻¹' Algebra.etaleLocus R A = Algebra.etaleLocus R Af := by
  ext p
  let q := PrimeSpectrum.comap (algebraMap A Af) p
  have : IsLocalization.AtPrime (Localization.AtPrime p.asIdeal) q.asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (.powers f) _ p.asIdeal
  refine Algebra.FormallyEtale.iff_of_equiv ?_
  exact (IsLocalization.algEquiv q.asIdeal.primeCompl _ _).restrictScalars R

namespace Rig

/-! ## Étaleness over the complement of `V(I)` -/

variable {A : Type u} [CommRing A]

/-- **`Spec(B) → Spec(A)` is étale over `Spec(A) ∖ V(I)`.**  Every prime of `B` whose image in
`Spec(A)` avoids `V(I)` lies in the étale locus of `B` over `A`. -/
public def IsEtaleOutside (I : Ideal A) (B : Type v) [CommRing B] [Algebra A B] : Prop :=
  PrimeSpectrum.comap (algebraMap A B) ⁻¹' (PrimeSpectrum.zeroLocus (I : Set A))ᶜ ⊆
    Algebra.etaleLocus A B

/-- Elementwise form of `Rig.IsEtaleOutside`: étaleness at every prime `q` of `B` with
`I ⊄ q ∩ A`. -/
public theorem isEtaleOutside_iff (I : Ideal A) (B : Type v) [CommRing B] [Algebra A B] :
    IsEtaleOutside I B ↔
      ∀ (q : Ideal B) (_ : q.IsPrime), ¬ I ≤ q.comap (algebraMap A B) →
        Algebra.IsEtaleAt A q := by
  have key : ∀ p : PrimeSpectrum B,
      p ∈ PrimeSpectrum.comap (algebraMap A B) ⁻¹' (PrimeSpectrum.zeroLocus (I : Set A))ᶜ ↔
        ¬ I ≤ p.asIdeal.comap (algebraMap A B) := by
    intro p
    simp only [Set.mem_preimage, Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus,
      PrimeSpectrum.comap_asIdeal, SetLike.coe_subset_coe]
  exact ⟨fun h q hq hqI => h ((key ⟨q, hq⟩).mpr hqI),
    fun h p hp => h p.asIdeal p.2 ((key p).mp hp)⟩

/-! ## The two cohomology modules of a finite presentation -/

section Presentation

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {B : Type v} [CommRing B] [Algebra A B] [Algebra.FiniteType A B] {n : ℕ}

/-- `H⁻¹(NL(α)) = ker d` of a finite presentation is `H¹(L_{B/A})`. -/
public def presentationKerEquiv (G : Algebra.Generators A B (Fin n)) :
    LinearMap.ker (presentationDifferential G) ≃ₗ[B] Algebra.H1Cotangent A B := by
  refine LinearEquiv.trans (LinearEquiv.ofEq _ _ ?_) G.equivH1Cotangent
  exact LinearMap.ker_comp_of_ker_eq_bot _
    (LinearMap.ker_eq_bot_of_injective G.cotangentSpaceBasis.equivFun.injective)

/-- `H⁰(NL(α)) = coker d` of a finite presentation is `Ω_{B/A}`. -/
public def presentationCokerEquiv (G : Algebra.Generators A B (Fin n)) :
    ((Fin n → B) ⧸ LinearMap.range (presentationDifferential G)) ≃ₗ[B] Ω[B⁄A] := by
  have hex : Function.Exact (presentationDifferential G)
      (G.toExtension.toKaehler ∘ₗ G.cotangentSpaceBasis.equivFun.symm.toLinearMap) :=
    Function.Exact.linearEquiv_comp G.cotangentSpaceBasis.equivFun
      G.toExtension.exact_cotangentComplex_toKaehler
  exact hex.linearEquivOfSurjective
    (G.toExtension.toKaehler_surjective.comp G.cotangentSpaceBasis.equivFun.symm.surjective)

/-- `H¹(L_{B/A})` is a finite `B`-module when `B` is of finite type over a Noetherian ring. -/
public theorem finite_h1Cotangent : Module.Finite B (Algebra.H1Cotangent A B) := by
  obtain ⟨n, ⟨G⟩⟩ :=
    Algebra.FiniteType.iff_exists_generators.mp (inferInstance : Algebra.FiniteType A B)
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have hring : IsNoetherianRing G.toExtension.Ring := by
    change IsNoetherianRing (MvPolynomial (Fin n) A); infer_instance
  have hcot : Module.Finite B G.toExtension.Cotangent :=
    Algebra.Extension.Cotangent.finite (Ideal.fg_of_isNoetherianRing G.toExtension.ker)
  have hH : Module.Finite B G.toExtension.H1Cotangent :=
    inferInstanceAs (Module.Finite B (LinearMap.ker G.toExtension.cotangentComplex))
  exact Module.Finite.of_surjective G.equivH1Cotangent.toLinearMap G.equivH1Cotangent.surjective

end Presentation

/-! ## The pivot: rig-étaleness of the completion -/

section Pivot

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  {B : Type v} [CommRing B] [Algebra A B] [Algebra.FiniteType A B]

/-- **Rig-étaleness of `B^` read on the cohomology of `NL(α)`.**  For `A` Noetherian and `B` of
finite type over `A`, the `I`-adic completion `B^` is rig-étale over `(A, I)` exactly when some
power `Iᶜ B^` annihilates both `B^ ⊗_B H¹(L_{B/A})` and `B^ ⊗_B Ω_{B/A}`.

This is **Stacks 0GAF** — the completed naive cotangent complex of `B^` is the base change
`NL(α) ⊗_B B^` of the naive cotangent complex of a finite presentation `α` of `B`
(`Rig.completionComparison`, bijective in both degrees) — combined with **Stacks 0AJU,
(1) ⇔ (3)** and the flatness of `B^` over `B` for `B` Noetherian (**Stacks 00MB**), which turns
the kernel and cokernel of the base-changed differential into base changes of the kernel and the
cokernel.  Those in turn are `H¹(L_{B/A})` and `Ω_{B/A}` by
`Rig.presentationKerEquiv` and `Rig.presentationCokerEquiv`. -/
public theorem isRigEtale_adicCompletionObj_iff :
    IsRigEtale (adicCompletionObj I (B := B)) ↔
      ∃ c : ℕ,
        (I ^ c).map (algebraMap A (adicCompletionObj I (B := B)).carrier) ≤
          Module.annihilator (adicCompletionObj I (B := B)).carrier
            ((adicCompletionObj I (B := B)).carrier ⊗[B] Algebra.H1Cotangent A B) ∧
        (I ^ c).map (algebraMap A (adicCompletionObj I (B := B)).carrier) ≤
          Module.annihilator (adicCompletionObj I (B := B)).carrier
            ((adicCompletionObj I (B := B)).carrier ⊗[B] Ω[B⁄A]) := by
  obtain ⟨n, ⟨G⟩⟩ :=
    Algebra.FiniteType.iff_exists_generators.mp (inferInstance : Algebra.FiniteType A B)
  have hBnoeth : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have hflat : Module.Flat B (adicCompletionObj I (B := B)).carrier :=
    inferInstanceAs (Module.Flat B (adicCompletionAlgebra I (B := B)))
  have hb₁ := bijective_completionComparison_f₁ I G
  have hb₀ := bijective_completionComparison_f₀ I G
  -- `H⁻¹`: `ker NL^∧_{B^/A} ≅ B^ ⊗_B H¹(L_{B/A})`.
  have hker : Module.annihilator (adicCompletionObj I (B := B)).carrier
        (LinearMap.ker (completedNaiveCotangentComplex (adicCompletionObj I (B := B))
          (presentationCompletion I G)).differential) =
      Module.annihilator (adicCompletionObj I (B := B)).carrier
        ((adicCompletionObj I (B := B)).carrier ⊗[B] Algebra.H1Cotangent A B) :=
    ((LinearEquiv.ofBijective (NaiveCotangent.ChainMap.onH₁ (completionComparison I G))
      (NaiveCotangent.ChainMap.bijective_onH₁ _ hb₁ hb₀.1)).symm.trans
      ((LinearMap.tensorKerEquiv (adicCompletionObj I (B := B)).carrier
          (adicCompletionObj I (B := B)).carrier (presentationDifferential G)).symm.trans
        (LinearEquiv.baseChange B (adicCompletionObj I (B := B)).carrier _ _
          (presentationKerEquiv G)))).annihilator_eq
  -- `H⁰`: `coker NL^∧_{B^/A} ≅ B^ ⊗_B Ω_{B/A}`.
  have hcoker : Module.annihilator (adicCompletionObj I (B := B)).carrier
        ((Fin (presentationCompletion I G).variableCount →
            (adicCompletionObj I (B := B)).carrier) ⧸
          LinearMap.range (completedNaiveCotangentComplex (adicCompletionObj I (B := B))
            (presentationCompletion I G)).differential) =
      Module.annihilator (adicCompletionObj I (B := B)).carrier
        ((adicCompletionObj I (B := B)).carrier ⊗[B] Ω[B⁄A]) :=
    ((LinearEquiv.ofBijective (NaiveCotangent.ChainMap.onH₀ (completionComparison I G))
      (NaiveCotangent.ChainMap.bijective_onH₀ _ hb₁.2 hb₀)).symm.trans
      ((LinearMap.baseChangeCokerEquiv (adicCompletionObj I (B := B)).carrier
          (presentationDifferential G)).trans
        (LinearEquiv.baseChange B (adicCompletionObj I (B := B)).carrier _ _
          (presentationCokerEquiv G)))).annihilator_eq
  rw [isRigEtale_iff_exists_annihilator_cohomology (adicCompletionObj I (B := B))
    (presentationCompletion I G), hker, hcoker]

end Pivot

/-! ## Annihilators, supports and Nakayama -/

section Annihilators

/-- A finite module over a Noetherian ring whose support lies in `V(J)` is annihilated by a
power of `J`: the annihilator has `J` in its radical. -/
private theorem exists_pow_le_annihilator_of_support_subset {R M : Type*} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] (J : Ideal R)
    (hsupport : Module.support R M ⊆ PrimeSpectrum.zeroLocus (J : Set R)) :
    ∃ c : ℕ, J ^ c ≤ Module.annihilator R M := by
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ J.fg_of_isNoetherianRing
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun p hp => ?_
  exact hsupport ((Module.mem_support_iff_of_finite (p := ⟨p, hp.2⟩)).mpr hp.1)

/-- An ideal annihilating `M` extends to an ideal annihilating every base change of `M`. -/
private theorem map_le_annihilator_tensor {R S M : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] {J : Ideal R}
    (hJ : J ≤ Module.annihilator R M) :
    J.map (algebraMap R S) ≤ Module.annihilator S (S ⊗[R] M) := by
  rw [Ideal.map_le_iff_le_comap]
  intro s hs
  refine Module.mem_annihilator.mpr fun t => ?_
  induction t with
  | add x y hx hy => simp [smul_add, hx, hy]
  | tmul b m =>
    change (algebraMap R S s * b) ⊗ₜ[R] m = 0
    rw [← Algebra.smul_def, TensorProduct.smul_tmul]
    simp [Module.mem_annihilator.mp (hJ hs) m]

/-- **Nakayama's lemma, Stacks 00DV, applied to `⋂ₙ Jⁿ M`.**  For a finite module `M` over a
Noetherian ring there is `g ∈ 1 + J` annihilating `⋂ₙ Jⁿ M`: that submodule is its own `J`-fold
multiple, by the Artin–Rees stability of the `J`-adic filtration. -/
private theorem exists_sub_one_mem_and_smul_iInf_eq_zero {R M : Type*} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] (J : Ideal R) :
    ∃ g : R, g - 1 ∈ J ∧ ∀ x ∈ (⨅ n : ℕ, J ^ n • ⊤ : Submodule R M), g • x = 0 := by
  set N := (⨅ n : ℕ, J ^ n • ⊤ : Submodule R M) with hN
  have hconstant : ∀ n, (J.stableFiltration ⊤ ⊓ J.trivialFiltration N).N n = N :=
    fun n => inf_eq_right.mpr ((iInf_le _ n).trans (le_of_eq (by simp)))
  refine Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J N
    (IsNoetherian.noetherian N) ?_
  obtain ⟨index, hstable⟩ :=
    (J.stableFiltration_stable (⊤ : Submodule R M)).inter_right (J.trivialFiltration N)
  have heq := hstable index (le_refl _)
  rw [hconstant, hconstant] at heq
  exact le_of_eq heq.symm

/-- **The element of `1 + J` of Stacks 0ALQ, part (2).**  If an ideal `K` of `R` annihilates
`R^ ⊗_R M` after `J`-adic completion, then some `g ∈ 1 + J` makes `g · K` annihilate the finite
module `M` itself.

Annihilation after completion puts `s • x`, for `s ∈ K`, in every `Jⁿ M`, hence in the
intersection, which Nakayama's lemma kills after multiplying by one element of `1 + J`. -/
private theorem exists_sub_one_mem_and_smul_smul_eq_zero {R M : Type*} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] (J K : Ideal R)
    (hK : K.map (algebraMap R (AdicCompletion J R)) ≤
      Module.annihilator (AdicCompletion J R) (AdicCompletion J R ⊗[R] M)) :
    ∃ g : R, g - 1 ∈ J ∧ ∀ s ∈ K, ∀ x : M, g • (s • x) = 0 := by
  obtain ⟨g, hg, hzero⟩ := exists_sub_one_mem_and_smul_iInf_eq_zero (M := M) J
  refine ⟨g, hg, fun s hs x => hzero _ ?_⟩
  have htensor := Module.mem_annihilator.mp
    (hK (Ideal.mem_map_of_mem (algebraMap R (AdicCompletion J R)) hs)) (1 ⊗ₜ[R] x)
  have hcompletion : AdicCompletion.of J M (s • x) = 0 := by
    have heq := congrArg (AdicCompletion.ofTensorProduct J M) htensor
    simpa [AdicCompletion.ofTensorProduct_tmul, TensorProduct.smul_tmul',
      IsScalarTower.algebraMap_smul] using heq
  rw [Submodule.mem_iInf]
  intro n
  have heval := congrArg (AdicCompletion.eval J M n) hcompletion
  simpa only [AdicCompletion.eval_of, map_zero, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] using heval

end Annihilators

/-! ## Stacks 0ALQ -/

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  {B : Type v} [CommRing B] [Algebra A B] [Algebra.FiniteType A B]

omit [IsNoetherianRing A] [Algebra.FiniteType A B] in
/-- A prime of `B` avoids `V(IB)` exactly when it does not lie over `V(I)`. -/
private theorem notMem_zeroLocus_iff (p : PrimeSpectrum B) :
    p ∉ PrimeSpectrum.zeroLocus ((I.map (algebraMap A B) : Ideal B) : Set B) ↔
      ¬ I ≤ p.asIdeal.comap (algebraMap A B) := by
  rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.map_le_iff_le_comap]

/-- The extension to `B^` of a power of `IB` is the extension of the same power of `I`. -/
private theorem map_pow_map_algebraMap_adicCompletionObj (c : ℕ) :
    ((I.map (algebraMap A B)) ^ c).map (algebraMap B (adicCompletionObj I (B := B)).carrier) =
      (I ^ c).map (algebraMap A (adicCompletionObj I (B := B)).carrier) := by
  simp only [← Ideal.map_pow, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq A B (adicCompletionObj I (B := B)).carrier]

/-- A prime avoiding `g` and `s` is outside the support of a module killed by `g * s`. -/
private theorem notMem_support_of_smul_smul_eq_zero {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {q : PrimeSpectrum R} {g s : R} (hg : g ∉ q.asIdeal) (hs : s ∉ q.asIdeal)
    (h : ∀ x : M, g • s • x = 0) : q ∉ Module.support R M := fun hsup =>
  (q.2.mem_or_mem (Module.annihilator_le_of_mem_support hsup
    (Module.mem_annihilator.mpr fun x => by simpa only [mul_smul] using h x))).elim hg hs

/-- **Stacks 0ALQ, part (1).**  Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `B` a finite
type `A`-algebra.  If `Spec(B) → Spec(A)` is étale over `Spec(A) ∖ V(I)`, then the `I`-adic
completion `B^` satisfies the equivalent conditions of Stacks 0AJU, that is, `B^` is rig-étale
over `(A, I)`.

Étaleness off `V(I)` says that `H¹(L_{B/A})` and `Ω_{B/A}` are supported in `V(IB)`, so — both
being finite modules over the Noetherian ring `B` — a power of `IB` annihilates them, hence
also their base changes to `B^`.  The pivot
`Rig.isRigEtale_adicCompletionObj_iff` turns that into rig-étaleness. -/
@[stacks 0ALQ "part (1)"]
public theorem isRigEtale_adicCompletionObj_of_isEtaleOutside (h : IsEtaleOutside I B) :
    IsRigEtale (adicCompletionObj I (B := B)) := by
  have hBnoeth : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have hfin : Module.Finite B (Algebra.H1Cotangent A B) := finite_h1Cotangent
  have hsupp : ∀ p : PrimeSpectrum B,
      p ∈ Module.support B Ω[B⁄A] ∨ p ∈ Module.support B (Algebra.H1Cotangent A B) →
        p ∈ PrimeSpectrum.zeroLocus ((I.map (algebraMap A B) : Ideal B) : Set B) := by
    intro p hp
    by_contra hnot
    have hlocus : p ∈ Algebra.etaleLocus A B :=
      (isEtaleOutside_iff I B).mp h p.asIdeal p.2 ((notMem_zeroLocus_iff I p).mp hnot)
    rw [Algebra.etaleLocus_eq_compl_support] at hlocus
    exact hp.elim hlocus.1 hlocus.2
  obtain ⟨c₁, hc₁⟩ := exists_pow_le_annihilator_of_support_subset
    (M := Algebra.H1Cotangent A B) (I.map (algebraMap A B)) fun p hp => hsupp p (.inr hp)
  obtain ⟨c₂, hc₂⟩ := exists_pow_le_annihilator_of_support_subset
    (M := Ω[B⁄A]) (I.map (algebraMap A B)) fun p hp => hsupp p (.inl hp)
  rw [isRigEtale_adicCompletionObj_iff]
  refine ⟨max c₁ c₂, ?_, ?_⟩
  · rw [← map_pow_map_algebraMap_adicCompletionObj]
    exact map_le_annihilator_tensor
      ((Ideal.pow_le_pow_right (Nat.le_max_left c₁ c₂)).trans hc₁)
  · rw [← map_pow_map_algebraMap_adicCompletionObj]
    exact map_le_annihilator_tensor
      ((Ideal.pow_le_pow_right (Nat.le_max_right c₁ c₂)).trans hc₂)

/-- **Stacks 0ALQ, part (2).**  Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `B` a finite
type `A`-algebra.  If the `I`-adic completion `B^` satisfies the equivalent conditions of
Stacks 0AJU — that is, if `B^` is rig-étale over `(A, I)` — then there is `g ∈ 1 + IB` such that
`Spec(B_g) → Spec(A)` is étale over `Spec(A) ∖ V(I)`.

The element `g` is produced by Nakayama's lemma: rig-étaleness gives a `c` with `Iᶜ B^`
annihilating `B^ ⊗_B H¹(L_{B/A})` and `B^ ⊗_B Ω_{B/A}`, so `Iᶜ B` annihilates both finite
`B`-modules only modulo `⋂ₙ (IB)ⁿ`, and one element of `1 + IB` kills that intersection.  After
inverting it, every prime of `B` off `V(IB)` contains no element of `Iᶜ B` and so lies outside
the supports of the two modules, which is étaleness there. -/
@[stacks 0ALQ "part (2)"]
public theorem exists_isEtaleOutside_localization_of_isRigEtale_adicCompletionObj
    (h : IsRigEtale (adicCompletionObj I (B := B))) :
    ∃ g : B, g - 1 ∈ I.map (algebraMap A B) ∧ IsEtaleOutside I (Localization.Away g) := by
  have hBnoeth : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have hfin : Module.Finite B (Algebra.H1Cotangent A B) := finite_h1Cotangent
  obtain ⟨c, h₁, h₂⟩ := (isRigEtale_adicCompletionObj_iff I).mp h
  rw [← map_pow_map_algebraMap_adicCompletionObj] at h₁ h₂
  obtain ⟨g₁, hg₁, hz₁⟩ := exists_sub_one_mem_and_smul_smul_eq_zero
    (M := Algebra.H1Cotangent A B) (I.map (algebraMap A B)) _ h₁
  obtain ⟨g₂, hg₂, hz₂⟩ := exists_sub_one_mem_and_smul_smul_eq_zero
    (M := Ω[B⁄A]) (I.map (algebraMap A B)) _ h₂
  refine ⟨g₁ * g₂, ?_, ?_⟩
  · have hsum := (I.map (algebraMap A B)).add_mem
      ((I.map (algebraMap A B)).mul_mem_left g₁ hg₂) hg₁
    simpa only [mul_sub, mul_one, sub_add_sub_cancel] using hsum
  -- Every prime of `B` in `D(g₁ g₂)` off `V(IB)` is in the étale locus of `B`.
  have hBg : ∀ q : PrimeSpectrum B, g₁ * g₂ ∉ q.asIdeal →
      q ∉ PrimeSpectrum.zeroLocus ((I.map (algebraMap A B) : Ideal B) : Set B) →
      q ∈ Algebra.etaleLocus A B := by
    intro q hgq hqI
    have hg₁q : g₁ ∉ q.asIdeal := fun hm => hgq (q.asIdeal.mul_mem_right g₂ hm)
    have hg₂q : g₂ ∉ q.asIdeal := fun hm => hgq (q.asIdeal.mul_mem_left g₁ hm)
    have hJq : ¬ I.map (algebraMap A B) ≤ q.asIdeal := by
      rw [Ideal.map_le_iff_le_comap]
      exact (notMem_zeroLocus_iff I q).mp hqI
    obtain ⟨s, hs, hsq⟩ := IsConcreteLE.not_le_iff_exists.mp
      (fun hle => hJq (Ideal.IsPrime.le_of_pow_le (n := c) hle))
    rw [Algebra.etaleLocus_eq_compl_support]
    exact ⟨notMem_support_of_smul_smul_eq_zero hg₂q hsq (hz₂ s hs),
      notMem_support_of_smul_smul_eq_zero hg₁q hsq (hz₁ s hs)⟩
  -- Transfer along `B → B_{g₁ g₂}`.
  intro p hp
  rw [← Algebra.etaleLocus_comap_of_isLocalization (R := A) (g₁ * g₂), Set.mem_preimage]
  rw [Set.mem_preimage, Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus,
    SetLike.coe_subset_coe, PrimeSpectrum.comap_asIdeal] at hp
  refine hBg (PrimeSpectrum.comap (algebraMap B (Localization.Away (g₁ * g₂))) p) ?_ ?_
  · rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    intro hm
    exact p.2.1 (p.asIdeal.eq_top_of_isUnit_mem hm
      (IsLocalization.map_units (M := Submonoid.powers (g₁ * g₂)) _
        ⟨g₁ * g₂, Submonoid.mem_powers _⟩))
  · rw [notMem_zeroLocus_iff, PrimeSpectrum.comap_asIdeal]
    intro hle
    refine hp ?_
    rw [IsScalarTower.algebraMap_eq A B (Localization.Away (g₁ * g₂)), ← Ideal.comap_comap]
    exact hle

/-- **Stacks 0ALQ.**  Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `B` a finite type
`A`-algebra, and write `B^` for the `I`-adic completion of `B`.

1. If `Spec(B) → Spec(A)` is étale over `Spec(A) ∖ V(I)`, then `B^` satisfies the equivalent
   conditions of Stacks 0AJU, in the form of their first condition `Rig.IsRigEtale`.
2. If `B^` satisfies those conditions, then there exists `g ∈ 1 + IB` such that
   `Spec(B_g) → Spec(A)` is étale over `Spec(A) ∖ V(I)`.

The two implications are `Rig.isRigEtale_adicCompletionObj_of_isEtaleOutside` and
`Rig.exists_isEtaleOutside_localization_of_isRigEtale_adicCompletionObj`. -/
@[stacks 0ALQ]
public theorem isEtaleOutside_and_isRigEtale_adicCompletionObj :
    (IsEtaleOutside I B → IsRigEtale (adicCompletionObj I (B := B))) ∧
      (IsRigEtale (adicCompletionObj I (B := B)) →
        ∃ g : B, g - 1 ∈ I.map (algebraMap A B) ∧ IsEtaleOutside I (Localization.Away g)) :=
  ⟨isRigEtale_adicCompletionObj_of_isEtaleOutside I,
    exists_isEtaleOutside_localization_of_isRigEtale_adicCompletionObj I⟩

end Main

/-! ## The algebraization condition of Stacks 0AKG -/

section Algebraization

universe w

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}

omit [IsNoetherianRing A] in
/-- The right unitor of `C ⊗_A A` carries the structure map of `A` to the inclusion of the
right factor: both send `a` to `1 ⊗ a`. -/
private theorem ridSymm_algebraMap_eq_includeRight (C : Type v) [CommRing C] [Algebra A C]
    (a : A) :
    (Algebra.TensorProduct.rid A A C).symm ((algebraMap A C) a) =
      Algebra.TensorProduct.includeRight a := by
  rw [Algebra.TensorProduct.rid_symm_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, smul_eq_mul, mul_one]

/-- **Rig-étaleness depends only on the isomorphism class.**  If the carriers of two objects of
`Rig.AdicFiniteTypeAlgebra A I` are isomorphic as `A`-algebras and one of them is rig-étale
over `(A, I)`, so is the other.

An isomorphism `B ≅ C` identifies `B` with the completed base change `(C ⊗_A A)^∧_I` of `C`
along the identity of `A`
(`Rig.exists_ringEquiv_completedBaseChangedAlgebra_of_algEquiv`, where the right unitor matches
the two ideals and `C` is already `I`-adically complete); **Stacks 0GB2** then transports the
annihilation of the completed naive cotangent complex.  Its rig-smooth counterpart
`Rig.isRigSmooth_of_algEquiv` is the same proof over the engine form of Stacks 0GAM. -/
public theorem isRigEtale_of_algEquiv {B : AdicFiniteTypeAlgebra.{u, w} A I}
    {C : AdicFiniteTypeAlgebra.{u, v} A I} (e : B.carrier ≃ₐ[A] C.carrier)
    (hC : IsRigEtale C) : IsRigEtale B := by
  let _ : Algebra C.carrier B.carrier :=
    (e.symm : C.carrier →ₐ[A] B.carrier).toRingHom.toAlgebra
  have halg : ∀ c : C.carrier, algebraMap C.carrier B.carrier c = e.symm c := fun _ => rfl
  have : IsScalarTower A C.carrier B.carrier :=
    .of_algebraMap_eq fun a => (e.symm.commutes a).symm
  obtain ⟨e', heA, heB⟩ := exists_ringEquiv_completedBaseChangedAlgebra_of_algEquiv e halg
  refine isRigEtale_of_completedBaseChange ?_ e' heA heB hC
  rw [show (algebraMap A A) = RingHom.id A from rfl, Ideal.map_id]

/-- **Stacks 0AKG, condition (8) implies the equivalent conditions of Stacks 0AJU.**  Let `A`
be a Noetherian ring, `I ⊆ A` an ideal and `B` an `I`-adically complete `A`-algebra of finite
type modulo `I`.  If `B` is isomorphic as an `A`-algebra to the `I`-adic completion `C^∧` of a
finite type `A`-algebra `C` with `Spec(C) → Spec(A)` étale over `Spec(A) ∖ V(I)`, then `B` is
rig-étale over `(A, I)`.

This is Stacks 0ALQ, part (1) applied to `C`, followed by the invariance of rig-étaleness
under isomorphism. -/
@[stacks 0AKG "condition (8) implies the equivalent conditions of Stacks 0AJU; the converse \
implication is not covered, since it rests on the algebraization lemma — that a rig-étale \
object of this category is the completion of a finite type algebra — which this library does \
not carry"]
public theorem isRigEtale_of_isEtaleOutside_of_algEquiv
    {B : AdicFiniteTypeAlgebra.{u, w} A I} {C : Type v} [CommRing C] [Algebra A C]
    [Algebra.FiniteType A C] (hC : IsEtaleOutside I C)
    (e : B.carrier ≃ₐ[A] (adicCompletionObj I (B := C)).carrier) :
    IsRigEtale B :=
  isRigEtale_of_algEquiv e (isRigEtale_adicCompletionObj_of_isEtaleOutside I (B := C) hC)

end Algebraization

end Rig

end
