module
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.Topology.Dimension.Equidimensional
import StacksFrontier.RingTheory.Depth.ExactnessCriterion
import StacksFrontier.RingTheory.Flat.LocalCriteria
import StacksFrontier.RingTheory.Sequence.RegularLocus

/-!
# Openness of the locus where the fibre of a complex of finite free modules is exact

Let `R` be Noetherian, let `R → S` be flat of finite type all of whose nonempty fibres
`S ⊗_R κ(𝔭)` are Cohen–Macaulay and equidimensional of one and the same dimension `d`, and let
`0 → F_{e+1} →[φ e] ⋯ →[φ 0] F_0` be a finite complex of finite free `S`-modules. This file proves
that the locus of primes `𝔮` of `S` at which the fibre complex
`F̄_{•,𝔮} = (S_𝔮/𝔭S_𝔮) ⊗_S F_•`, `𝔭 = R ∩ 𝔮`, is exact is open in `Spec S`.

This is Lemma 00RB with the hypothesis its proof consumes. The source states 00RB for fibres
Cohen–Macaulay *of dimension `d`* and proves it by an appeal to Lemma 00RA, whose hypothesis is
that the fibres be Cohen–Macaulay *and equidimensional* of dimension `d` — strictly stronger, as
`R = k`, `S = k × k[x]`, `d = 1` shows. Closing that step for the source's weaker hypothesis needs
a shrinking of `Spec S` to a neighbourhood on which the relative dimension is constant, which is
Lemma 00RH; and 00RH is proved from Theorem 00RC, the openness of the flat locus, whose own proof
is this lemma applied to a polynomial ring `S = R[x_1, …, x_n]` — whose fibres `κ(𝔭)[x_1, …, x_n]`
*are* equidimensional. So the equidimensional form proved here is the form on the critical path:
00RC needs no more, and the source's 00RB follows from 00RC through 00RH.

## Main results

*
`Algebra.isOpen_setOf_exact_baseChange_fiber_of_flat_of_isMaximalCohenMacaulay_of_equidimensional`:
  the set of primes `𝔮` of `S` at which the fibre complex `F_{•,𝔮} ⊗_R κ(𝔭)` is exact is open.

## Implementation notes

Openness is local, so the whole content is the source's first sentence: a prime `𝔮` at which the
fibre complex is exact has a basic open neighbourhood `D(g)` inside the locus. That reduction is
`exists_basicOpen_subset_setOf_baseChangeExact_fiber`, and `solution` is it plus
`isOpen_iff_forall_mem_open`.

The predicate whose locus is at stake is named `BaseChangeExact T e φ`: injectivity of `φ̄ e` and
exactness at the `e` intermediate terms, for the complex base-changed along `S → T`. For
`T = fiberLocalRing R 𝔮 = S_𝔮/𝔭S_𝔮` it is the condition of the statement.

*Base change in two steps.* `baseChangeExact_baseChange_iff` says that `BaseChangeExact T e φ` may
be read over an intermediate `S`-algebra `A` first: `T ⊗_S F_i = T ⊗_A (A ⊗_S F_i)`, by
`AlgebraTensorModule.cancelBaseChange`. With `A = S_𝔮` and `T = S_𝔮/𝔭S_𝔮` this is what lets a
criterion stated over the local ring `S_𝔮` — the local criterion of Lemma 00MI, or the
Buchsbaum–Eisenbud criterion of Proposition 00N1 — be applied to the fibre complex, which the
statement presents as a base change from `S`.

*Exactness after a flat base change is a support condition.* `injective_lTensor_iff_subsingleton`
and `exact_lTensor_iff_subsingleton` express injectivity of `A ⊗ φ_e` and exactness of
`A ⊗ φ_{k+1}, A ⊗ φ_k`, for `A` flat over `S`, as the vanishing of `A ⊗ H` for the relevant kernel
resp. homology `H = ker φ_k / im φ_{k+1}`. Taking `A = S_𝔮` and using
`notMem_support_iff_subsingleton_tensor`, the locus where the *localised* complex `F_{•,𝔮}` is
exact is the complement of the union of the supports of the finitely many homology modules, hence
open: this is `isOpen_setOf_baseChangeExact_localization`. It is the step by which exactness at one
prime spreads to a neighbourhood, the source's "the complex `F_•` becomes exact after localizing by
an element `g ∈ S`, `g ∉ 𝔮`".

*Lemma 00MI at one index.* `baseChangeExact_localization_of_baseChangeExact_fiber` runs the local
criterion of Lemma 00MI degree by degree rather than on a chain complex: the per-index form
`Module.Flat.ker_eq_range_and_flat_quotient_range_of_mem_sup_smul_top` is applied to
`S_𝔮 ⊗_S F_{k+2} → S_𝔮 ⊗_S F_{k+1} → S_𝔮 ⊗_S F_k` over the local homomorphism `R_𝔭 → S_𝔮`, with
the zero map in place of the incoming differential at the top index, where the conclusion is
injectivity. `Ideal.map_maximalIdeal_eq_map_under` identifies the ring the criterion reduces
modulo with `fiberLocalRing R 𝔮` on the nose, and `mem_sup_range_of_exact_baseChange` is the
elementwise form of exactness of the reduced complex that the criterion asks for.

*Proposition 00N1 in coordinates.* Proposition 00N1 is stated for complexes of standard free
modules `Fin (n i) → R`, so the base-changed complex is read in coordinates: `matBaseChange T f` is
the matrix of `f` with its entries carried into `T`, and `matBaseChange_comp_tensorPiEquiv` is the
ladder, through `Algebra.TensorProduct.piScalarRight`, that identifies it with
`LinearMap.baseChange T f`. Minors commute with this: `minorsIdeal_matBaseChange` says that the
ideal of `r × r` minors over `T` is the image of the ideal of `r × r` minors over `S`, for the same
`r`, since a minor of a matrix mapped entrywise is the image of that minor.

*The rank condition.* `baseChangeExact_fiber_iff_forall_le_depth` applies Proposition 00N1 twice,
over `S_𝔮` and over `S_𝔮/𝔭S_𝔮`, and the only difference between the two conditions is the rank
clause `IsGreatest {j | ⋀^j φ̄_k ≠ 0} r`. Exactness of `F_{•,𝔮}` supplies its upper half: over
`S_𝔮` the rank of `φ_k` is the expected rank `r`, and a nonzero `j × j` minor over `S_𝔮/𝔭S_𝔮` is
the image of one over `S_𝔮` (`exteriorPower_map_ne_zero_of_matBaseChange`), so `j ≤ r`. The depth
bound supplies the lower half: if `⋀^r φ̄_k` vanished the ideal of `r × r` minors would be zero
(`minorsIdeal_eq_bot_iff`), and the depth along the zero ideal of a nonzero ring is `0`
(`not_one_le_depth_bot`).

*Lemma 00RA.* `exists_basicOpen_le_depth_map_fiberLocalRing` is the last step. If some element of
`I` lies outside `𝔮` it is a unit in every `S_{𝔮'}/𝔭'S_{𝔮'}` with `𝔮'` in the basic open it
defines, so there the depth is `⊤`. Otherwise `I ⊆ 𝔮`, the image of `I` in `S_𝔮/𝔭S_𝔮` is proper
and the depth bound is witnessed by a regular sequence of length `k` in it
(`exists_isRegular_length_ge_of_le_depth`, `isRegular_take`), whose terms may be replaced by images
of elements `x_1, …, x_k` of `I` generating the same ideal
(`exists_mem_mul_isUnit_of_mem_map`, `exists_list_mem_ofList_eq`): every element of `I S_𝔮` is
`x/t` with `x ∈ I` and `t ∉ 𝔮`, so the generators only change by units, and over the
Cohen–Macaulay local ring `S_𝔮/𝔭S_𝔮` regularity of a sequence in the maximal ideal depends only on
the ideal it generates (Lemma 02JN). Lemma 00RA then makes the locus where `x_1, …, x_k` is regular
in the fibre open in `V(x_1, …, x_k)`, and outside `V(x_1, …, x_k)` one of the `x_i` is again a
unit in the fibre; the union of the two loci is the complement of a closed subset of
`V(x_1, …, x_k)`, hence open, and it contains `𝔮`.

An earlier draft of this file reduced the lemma instead to the openness of the locus where the
cokernels `F_i/φ_i(F_{i+1})` are flat over `R`, using Lemma 00MI in both directions. That
equivalence is correct — it is the standard consequence of the local criterion — but the openness
of the relative flat locus is Theorem 00RC, whose only proof runs through the present lemma applied
to a finite free resolution, so that reduction is circular and is not used here. The route above is
the source's.

## References

* [StacksProject 00RB](https://stacks.math.columbia.edu/tag/00RB)
* [StacksProject 00MI](https://stacks.math.columbia.edu/tag/00MI)
* [StacksProject 00N1](https://stacks.math.columbia.edu/tag/00N1)
* [StacksProject 00RA](https://stacks.math.columbia.edu/tag/00RA)
* [StacksProject 02JN](https://stacks.math.columbia.edu/tag/02JN)
* [StacksProject 00RH](https://stacks.math.columbia.edu/tag/00RH)

## Tags

exact complex, finite free module, fibre, flat ring map, Cohen-Macaulay ring, open locus
-/

namespace Stacks.Flatness.FibreExactnessLocus
open Stacks.RegularSequence.FibrewiseLocus

open TensorProduct

/-- Exactness of the complex `0 → A ⊗ F_{e+1} → ⋯ → A ⊗ F_0` obtained from
`0 → F_{e+1} →[φ e] ⋯ →[φ 0] F_0` by base change along `S → A`, at every term but the last. -/
private def BaseChangeExact {S : Type*} [CommRing S] {F : ℕ → Type*} [∀ i, AddCommGroup (F i)]
    [∀ i, Module S (F i)] (A : Type*) [CommRing A] [Algebra S A] (e : ℕ)
    (φ : ∀ i, F (i + 1) →ₗ[S] F i) : Prop :=
  Function.Injective (LinearMap.baseChange A (φ e)) ∧
    ∀ k < e, Function.Exact (LinearMap.baseChange A (φ (k + 1))) (LinearMap.baseChange A (φ k))

/-- Base change along `S → T` factors through an intermediate `S`-algebra `A`: the cancellation
isomorphism `T ⊗[A] (A ⊗[S] M) ≅ T ⊗[S] M` intertwines the base change to `T` of `f : M →ₗ[S] N`
with the base change to `T` of its base change to `A`. -/
public lemma baseChange_comp_cancelBaseChange {S : Type*} [CommRing S] {M N : Type*}
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N] (A : Type*) [CommRing A]
    [Algebra S A] (T : Type*) [CommRing T] [Algebra S T] [Algebra A T] [IsScalarTower S A T]
    (f : M →ₗ[S] N) :
    LinearMap.baseChange T f ∘ₗ (AlgebraTensorModule.cancelBaseChange S A T T M).toLinearMap =
      (AlgebraTensorModule.cancelBaseChange S A T T N).toLinearMap ∘ₗ
        LinearMap.baseChange T (LinearMap.baseChange A f) := by
  ext t
  simp

/-- A map of `S`-modules becomes injective after tensoring with a flat `S`-module `A` exactly when
`A ⊗ ker` vanishes. -/
private lemma injective_lTensor_iff_subsingleton {S : Type*} [CommRing S] {N P : Type*}
    [AddCommGroup N] [Module S N] [AddCommGroup P] [Module S P] (A : Type*) [AddCommGroup A]
    [Module S A] [Module.Flat S A] (g : N →ₗ[S] P) :
    Function.Injective (g.lTensor A) ↔ Subsingleton (A ⊗[S] LinearMap.ker g) := by
  have key : Function.Exact ((LinearMap.ker g).subtype.lTensor A) (g.lTensor A) :=
    Module.Flat.lTensor_exact _ (LinearMap.exact_subtype_ker_map g)
  have hinj : Function.Injective ((LinearMap.ker g).subtype.lTensor A) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.subtype_injective _)
  constructor
  · intro h
    have ha : ∀ x : A ⊗[S] (LinearMap.ker g), x = 0 := fun x =>
      hinj
        (by
          rw [map_zero];
          exact
            h
              (by
                rw [map_zero]; exact key.apply_apply_eq_zero x))
    exact ⟨fun x y => by rw [ha x, ha y]⟩
  · intro h
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, hy⟩ := (key x).mp hx
    rw [← hy, Subsingleton.elim y 0, map_zero]

/-- A two-term complex of `S`-modules becomes exact after tensoring with a flat `S`-module `A`
exactly when `A ⊗ H` vanishes, `H` its homology `ker g / im f`. -/
private lemma exact_lTensor_iff_subsingleton {S : Type*} [CommRing S] {M N P : Type*}
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N] [AddCommGroup P] [Module S P]
    (A : Type*) [AddCommGroup A] [Module S A] [Module.Flat S A] (f : M →ₗ[S] N) (g : N →ₗ[S] P)
    (hfg : ∀ x, f x ∈ LinearMap.ker g) :
    Function.Exact (f.lTensor A) (g.lTensor A) ↔
      Subsingleton
        (A ⊗[S]
          (↥(LinearMap.ker g) ⧸
            LinearMap.range (LinearMap.codRestrict (LinearMap.ker g) f hfg))) := by
  set K := LinearMap.ker g with hK
  set f' := LinearMap.codRestrict K f hfg with hf'
  have hcomp : K.subtype ∘ₗ f' = f := rfl
  have key1 : Function.Exact (K.subtype.lTensor A) (g.lTensor A) :=
    Module.Flat.lTensor_exact _ (LinearMap.exact_subtype_ker_map g)
  have hinj1 : Function.Injective (K.subtype.lTensor A) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.subtype_injective _)
  have key2 : Function.Exact (f'.lTensor A) ((Submodule.mkQ (LinearMap.range f')).lTensor A) :=
    Module.Flat.lTensor_exact _ (LinearMap.exact_map_mkQ_range f')
  have hsurj2 : Function.Surjective ((Submodule.mkQ (LinearMap.range f')).lTensor A) :=
    LinearMap.lTensor_surjective A (Submodule.mkQ_surjective _)
  have hfac : ∀ u : A ⊗[S] M, (f.lTensor A) u = (K.subtype.lTensor A) ((f'.lTensor A) u) := by
    intro u
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hcomp]
  constructor
  · intro h
    have ha : ∀ z : A ⊗[S] (↥K ⧸ LinearMap.range f'), z = 0 := by
      intro z
      obtain ⟨w, hw⟩ := hsurj2 z
      obtain ⟨u, hu⟩ := (h ((K.subtype.lTensor A) w)).mp (key1.apply_apply_eq_zero w)
      have hwu : w = (f'.lTensor A) u := hinj1 (by rw [← hfac u, hu])
      rw [← hw, hwu]
      exact key2.apply_apply_eq_zero u
    exact ⟨fun x y => by rw [ha x, ha y]⟩
  · intro h x
    constructor
    · intro hx
      obtain ⟨w, hw⟩ := (key1 x).mp hx
      obtain ⟨u, hu⟩ := (key2 w).mp (Subsingleton.elim _ _)
      exact ⟨u, by rw [hfac u, hu, hw]⟩
    · rintro ⟨u, rfl⟩
      rw [hfac u]
      exact key1.apply_apply_eq_zero _

/-- A prime lies outside the support of an `S`-module exactly when that module dies after
tensoring with the local ring there. -/
private lemma notMem_support_iff_subsingleton_tensor {S : Type*} [CommRing S] (X : Type*)
    [AddCommGroup X] [Module S X] (q : PrimeSpectrum S) :
    q ∉ Module.support S X ↔ Subsingleton (Localization.AtPrime q.asIdeal ⊗[S] X) := by
  rw [Module.notMem_support_iff]
  exact (LocalizedModule.equivTensorProduct q.asIdeal.primeCompl X).toEquiv.subsingleton_congr

/-- Exactness of the localised complex `F_{•,𝔮}` is an open condition on `𝔮`: the homology of
`F_•` is a finite `S`-module in each degree, localisation commutes with homology, and the support
of a finite module is closed. -/
private theorem isOpen_setOf_baseChangeExact_localization {S : Type*} [CommRing S]
    [IsNoetherianRing S] {F : ℕ → Type*} [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    [∀ i, Module.Finite S (F i)] (e : ℕ) (φ : ∀ i, F (i + 1) →ₗ[S] F i)
    (hφ : ∀ k < e, φ k ∘ₗ φ (k + 1) = 0) :
    IsOpen {q : PrimeSpectrum S | BaseChangeExact (Localization.AtPrime q.asIdeal) e φ} := by
  have hmem : ∀ k, k < e → ∀ x, φ (k + 1) x ∈ LinearMap.ker (φ k) := by
    intro k hk x
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hφ k hk, LinearMap.zero_apply]
  have hset :
    {q : PrimeSpectrum S | BaseChangeExact (Localization.AtPrime q.asIdeal) e φ} =
      (Module.support S ↥(LinearMap.ker (φ e)))ᶜ ∩
        ⋂ k : Fin e,
          (Module.support S
              (↥(LinearMap.ker (φ k.1)) ⧸
                LinearMap.range
                  (LinearMap.codRestrict (LinearMap.ker (φ k.1)) (φ (k.1 + 1))
                    (hmem k.1 k.2))))ᶜ := by
    ext q
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff, Set.mem_ofPred_eq,
      notMem_support_iff_subsingleton_tensor]
    rw [BaseChangeExact, ← injective_lTensor_iff_subsingleton]
    refine and_congr Iff.rfl ?_
    constructor
    · intro h k
      exact (exact_lTensor_iff_subsingleton _ _ _ (hmem k.1 k.2)).mp (h k.1 k.2)
    · intro h k hk
      exact (exact_lTensor_iff_subsingleton _ _ _ (hmem k hk)).mpr (h ⟨k, hk⟩)
  rw [hset]
  exact
    (Module.isClosed_support (R := S)).isOpen_compl.inter
      (isOpen_iInter_of_finite fun _ => (Module.isClosed_support (R := S)).isOpen_compl)

/-- The ideal `𝔭S_𝔮` generated in `S_𝔮` by the image of `𝔭 = R ∩ 𝔮` lies in the maximal ideal:
an element of `𝔭` maps into `𝔮`, hence into `𝔮S_𝔮`. -/
private lemma map_under_le_maximalIdeal {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal S) [q.IsPrime] :
    (q.under R).map (algebraMap R (Localization.AtPrime q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply R S (Localization.AtPrime q)]
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q _).mpr hx

/-- The ideal `𝔭S_𝔮` is proper. -/
private lemma map_under_ne_top {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (q : Ideal S)
    [q.IsPrime] : (q.under R).map (algebraMap R (Localization.AtPrime q)) ≠ ⊤ :=
  ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top (map_under_le_maximalIdeal q)

/-- The fibre local ring `S_𝔮/𝔭S_𝔮` is nonzero: the fibre through `𝔮` is nonempty. -/
private lemma nontrivial_fiberLocalRing (R : Type*) {S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (q : Ideal S) [q.IsPrime] : Nontrivial (fiberLocalRing R q) := by
  refine nontrivial_of_ne (0 : fiberLocalRing R q) 1 fun h => map_under_ne_top (R := R) q ?_
  rw [Ideal.eq_top_iff_one]
  exact
    Ideal.Quotient.eq_zero_iff_mem.mp
      (by
        rw [map_one]; exact h.symm)

attribute [local instance] nontrivial_fiberLocalRing

attribute [local instance] Stacks.RegularSequence.FibrewiseLocus.isLocalRing_fiberLocalRing

/-- The fibre local ring `S_𝔮/𝔭S_𝔮` is Noetherian when `S` is: it is a quotient of a
localization of `S`. -/
private lemma isNoetherianRing_fiberLocalRing (R : Type*) {S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing S] (q : Ideal S) [q.IsPrime] :
    IsNoetherianRing (fiberLocalRing R q) := by
  have : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
  infer_instance

attribute [local instance] isNoetherianRing_fiberLocalRing

-- The canonical local homomorphism `R_𝔭 → S_𝔮` for `𝔭 = R ∩ 𝔮`, the homomorphism of local rings
-- to which the local criterion of Lemma 00MI is applied, together with the tower over `R` and its
-- locality: `Ideal.algebraLocalizationAtPrimeUnder` and its companions.
attribute [local instance] Ideal.algebraLocalizationAtPrimeUnder
  Ideal.isScalarTower_localizationAtPrimeUnder
  Ideal.isLocalHom_algebraMap_localizationAtPrimeUnder

/-- The depth of an ideal containing a unit is `⊤`. -/
private lemma depth_eq_top_of_isUnit_mem {T : Type*} [CommRing T] {I : Ideal T} {u : T}
    (hu : u ∈ I) (hunit : IsUnit u) : Module.depth T I T = ⊤ := by
  have h : I • (⊤ : Submodule T T) = ⊤ := by
    rw [I.eq_top_of_isUnit_mem hu hunit, Submodule.top_smul]
  unfold Module.depth
  rw [ite_eq_left h]

/-- A commuting ladder square whose vertical maps are isomorphisms transports injectivity. -/
public lemma injective_iff_of_ladder_linearEquiv {R M M' N N' : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M'] [AddCommMonoid N] [Module R N]
    [AddCommMonoid N'] [Module R N'] {f : M →ₗ[R] N} {g : M' →ₗ[R] N'} {e₁ : M ≃ₗ[R] M'}
    {e₂ : N ≃ₗ[R] N'} (h : g ∘ₗ (e₁ : M →ₗ[R] M') = (e₂ : N →ₗ[R] N') ∘ₗ f) :
    Function.Injective g ↔ Function.Injective f := by
  constructor
  · intro hg x y hxy
    have h1 := LinearMap.congr_fun h x
    have h2 := LinearMap.congr_fun h y
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at h1 h2
    exact e₁.injective (hg (by rw [h1, h2, hxy]))
  · intro hf x y hxy
    obtain ⟨x, rfl⟩ := e₁.surjective x
    obtain ⟨y, rfl⟩ := e₁.surjective y
    have h1 := LinearMap.congr_fun h x
    have h2 := LinearMap.congr_fun h y
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at h1 h2
    rw [h1, h2] at hxy
    exact congrArg _ (hf (e₂.injective hxy))

/-- The base change of a linear equivalence, as a linear map, is the base change of the underlying
linear map. -/
public lemma coe_baseChange_linearEquiv {S : Type*} [CommRing S] {M N : Type*} [AddCommGroup M]
    [Module S M] [AddCommGroup N] [Module S N] (T : Type*) [CommRing T] [Algebra S T]
    (E : M ≃ₗ[S] N) :
    ((E.baseChange S T M N) : T ⊗[S] M →ₗ[T] T ⊗[S] N) = LinearMap.baseChange T E.toLinearMap := by
  ext t
  simp [LinearEquiv.baseChange]

/-- Injectivity of the last map and exactness of the others in a complex are invariant under an
isomorphism of complexes. -/
private lemma injective_and_exact_iff_of_ladder {R : Type*} [Semiring R] {M M' : ℕ → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, AddCommMonoid (M' i)]
    [∀ i, Module R (M' i)] (e : ℕ) {f : ∀ i, M (i + 1) →ₗ[R] M i} {g : ∀ i, M' (i + 1) →ₗ[R] M' i}
    (E : ∀ i, M i ≃ₗ[R] M' i)
    (h : ∀ i, g i ∘ₗ (E (i + 1) : M (i + 1) →ₗ[R] M' (i + 1)) = (E i : M i →ₗ[R] M' i) ∘ₗ f i) :
    (Function.Injective (g e) ∧ ∀ k < e, Function.Exact (g (k + 1)) (g k)) ↔
      (Function.Injective (f e) ∧ ∀ k < e, Function.Exact (f (k + 1)) (f k)) :=
  and_congr (injective_iff_of_ladder_linearEquiv (h e))
    (forall_congr' fun k =>
      imp_congr_right fun _ => Function.Exact.iff_of_ladder_linearEquiv (h (k + 1)) (h k))

/-- Exactness of the complex base-changed to `T` may be read off in two steps, first over an
intermediate `S`-algebra `A` and then over `T`. With `A = S_𝔮` and `T = S_𝔮/𝔭S_𝔮` this is what
lets a criterion over the local ring `S_𝔮`, such as Lemma 00MI, be applied to the fibre complex,
which the statement presents as a base change from `S`. -/
private lemma baseChangeExact_baseChange_iff {S : Type*} [CommRing S] {F : ℕ → Type*}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] (A : Type*) [CommRing A] [Algebra S A]
    (T : Type*) [CommRing T] [Algebra S T] [Algebra A T] [IsScalarTower S A T] (e : ℕ)
    (φ : ∀ i, F (i + 1) →ₗ[S] F i) :
    BaseChangeExact (S := A) (F := fun i => A ⊗[S] F i) T e
        (fun i => LinearMap.baseChange A (φ i)) ↔
      BaseChangeExact T e φ :=
  (injective_and_exact_iff_of_ladder e (fun i => AlgebraTensorModule.cancelBaseChange S A T T (F i))
    fun i => baseChange_comp_cancelBaseChange A T (φ i)).symm

/-- Exactness of the base-changed complex is invariant under an isomorphism of complexes: a family
of linear equivalences `E i : F i ≃ₗ[S] G i` intertwining the differentials induces one of the
base-changed complexes. This is what lets a complex of arbitrary finite free `S`-modules be
replaced by a complex of standard free modules `Fin (n i) → S`, the form in which Proposition 00N1
is stated. -/
private lemma baseChangeExact_congr {S : Type*} [CommRing S] {F G : ℕ → Type*}
    [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, AddCommGroup (G i)] [∀ i, Module S (G i)]
    (T : Type*) [CommRing T] [Algebra S T] (e : ℕ) (φ : ∀ i, F (i + 1) →ₗ[S] F i)
    (ψ : ∀ i, G (i + 1) →ₗ[S] G i) (E : ∀ i, F i ≃ₗ[S] G i)
    (h : ∀ i, ψ i ∘ₗ (E (i + 1) : F (i + 1) →ₗ[S] G (i + 1)) = (E i : F i →ₗ[S] G i) ∘ₗ φ i) :
    BaseChangeExact T e ψ ↔ BaseChangeExact T e φ := by
  have hsq :
    ∀ i,
      LinearMap.baseChange T (ψ i) ∘ₗ
          ((E (i + 1)).baseChange S T (F (i + 1)) (G (i + 1)) :
            T ⊗[S] F (i + 1) →ₗ[T] T ⊗[S] G (i + 1)) =
        ((E i).baseChange S T (F i) (G i) : T ⊗[S] F i →ₗ[T] T ⊗[S] G i) ∘ₗ
          LinearMap.baseChange T (φ i) := by
    intro i
    rw [coe_baseChange_linearEquiv, coe_baseChange_linearEquiv, ← LinearMap.baseChange_comp, ←
      LinearMap.baseChange_comp, h i]
  exact injective_and_exact_iff_of_ladder e (fun i => (E i).baseChange S T (F i) (G i)) hsq

/-- A point of an open subset of `Spec S` has a basic open neighbourhood inside it. -/
public lemma exists_basicOpen_subset_of_isOpen {S : Type*} [CommRing S] {U : Set (PrimeSpectrum S)}
    (hU : IsOpen U) {q : PrimeSpectrum S} (hq : q ∈ U) :
    ∃ g : S, g ∉ q.asIdeal ∧ ↑(PrimeSpectrum.basicOpen g) ⊆ U := by
  obtain ⟨s, hs⟩ := (PrimeSpectrum.isOpen_iff U).mp hU
  have h1 : ¬s ⊆ q.asIdeal := by
    intro h
    have hmem : q ∈ Uᶜ := by
      rw [hs]; exact (PrimeSpectrum.mem_zeroLocus _ _).mpr h
    exact hmem hq
  obtain ⟨g, hgs, hgq⟩ := Set.not_subset.mp h1
  refine ⟨g, hgq, fun q' hq' => ?_⟩
  by_contra hq'U
  have hmem : q' ∈ PrimeSpectrum.zeroLocus s := by
    rw [← hs]; exact hq'U
  exact (PrimeSpectrum.mem_basicOpen g q').mp hq' ((PrimeSpectrum.mem_zeroLocus _ _).mp hmem hgs)

/-- The expected rank of the `k`-th differential of a complex of finite free modules of ranks
`n 0, …, n (e + 1)`: the alternating sum `n_{k+1} - n_{k+2} + ⋯ ± n_{e+1}` of Proposition 00N1. -/
private abbrev expectedRank (e : ℕ) (n : ℕ → ℕ) (k : ℕ) : ℤ :=
  ∑ t ∈ Finset.range (e + 1 - k), (-1) ^ t * (n (k + 1 + t) : ℤ)

/-- The ideal generated by the `r × r` minors of the matrix of a linear map between standard finite
free modules, in the spelling of Proposition 00N1. -/
private abbrev minorsIdeal {S : Type*} [CommRing S] {a b : ℕ} (f : (Fin b → S) →ₗ[S] (Fin a → S))
    (r : ℕ) : Ideal S :=
  Ideal.span
    {x : S |
      ∃ (ρ : Fin r → Fin a) (γ : Fin r → Fin b), ((LinearMap.toMatrix' f).submatrix ρ γ).det = x}

/-- **Exactness modulo `J` read on elements.** If `X →[g] Y →[f] Z` becomes exact after reducing
modulo `J` and `f y ∈ JZ`, then `y ∈ JY + g(X)`. -/
public lemma mem_sup_range_of_exact_baseChange {A : Type*} [CommRing A] (J : Ideal A)
    {X Y Z : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y] [AddCommGroup Z]
    [Module A Z] (g : X →ₗ[A] Y) (f : Y →ₗ[A] Z)
    (h : Function.Exact (LinearMap.baseChange (A ⧸ J) g) (LinearMap.baseChange (A ⧸ J) f)) (y : Y)
    (hy : f y ∈ J • (⊤ : Submodule A Z)) : y ∈ J • (⊤ : Submodule A Y) ⊔ LinearMap.range g := by
  have h0 : (LinearMap.baseChange (A ⧸ J) f) ((1 : A ⧸ J) ⊗ₜ[A] y) = 0 := by
    rw [LinearMap.baseChange_tmul]
    exact (TensorProduct.one_tmul_eq_zero_iff_mem_smul_top J _).mpr hy
  obtain ⟨t, ht⟩ := (h _).mp h0
  obtain ⟨x, rfl⟩ := TensorProduct.exists_one_tmul J t
  rw [LinearMap.baseChange_tmul] at ht
  refine
    Submodule.mem_sup.mpr ⟨y - g x, ?_, g x, LinearMap.mem_range_self _ x, sub_add_cancel y (g x)⟩
  rw [← TensorProduct.one_tmul_eq_zero_iff_mem_smul_top, TensorProduct.tmul_sub, ht, sub_self]

/-- **Injectivity modulo `J` read on elements.** If `f : Y → Z` becomes injective after reducing
modulo `J` and `f y ∈ JZ`, then `y ∈ JY`. -/
private lemma mem_smul_top_of_injective_baseChange {A : Type*} [CommRing A] (J : Ideal A)
    {Y Z : Type*} [AddCommGroup Y] [Module A Y] [AddCommGroup Z] [Module A Z] (f : Y →ₗ[A] Z)
    (h : Function.Injective (LinearMap.baseChange (A ⧸ J) f)) (y : Y)
    (hy : f y ∈ J • (⊤ : Submodule A Z)) : y ∈ J • (⊤ : Submodule A Y) := by
  refine (TensorProduct.one_tmul_eq_zero_iff_mem_smul_top J y).mp (h ?_)
  rw [LinearMap.baseChange_tmul, map_zero]
  exact (TensorProduct.one_tmul_eq_zero_iff_mem_smul_top J _).mpr hy

/-- **The local criterion 00MI at one index, for a base change.** Let `R → A` be a local
homomorphism of local rings with `A` Noetherian and flat over `R`, let `J = 𝔪_R A`, and let
`X →[g] Y →[f] Z` be a complex of `A`-modules with `Y` finite and `Z` flat over `A`. If the complex
becomes exact at `Y` after reducing modulo `J`, then it is exact at `Y`. -/
private lemma ker_eq_range_of_exact_baseChange_quotient {R A : Type*} [CommRing R] [CommRing A]
    [IsLocalRing R] [IsLocalRing A] [Algebra R A] [IsLocalHom (algebraMap R A)]
    [IsNoetherianRing A] [Module.Flat R A] {X Y Z : Type*} [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] [Module.Finite A Y] [AddCommGroup Z] [Module A Z]
    [Module.Flat A Z] (J : Ideal A) (hJ : J = (IsLocalRing.maximalIdeal R).map (algebraMap R A))
    (g : X →ₗ[A] Y) (f : Y →ₗ[A] Z) (hfg : f ∘ₗ g = 0)
    (h : Function.Exact (LinearMap.baseChange (A ⧸ J) g) (LinearMap.baseChange (A ⧸ J) f)) :
    LinearMap.ker f = LinearMap.range g := by
  subst hJ
  let _ : Module R Y := Module.compHom _ (algebraMap R A)
  let _ : Module R Z := Module.compHom _ (algebraMap R A)
  have _ : IsScalarTower R A Y := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have _ : IsScalarTower R A Z := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have _ : Module.Flat R Z := Module.Flat.trans R A Z
  exact
    (Module.Flat.ker_eq_range_and_flat_quotient_range_of_mem_sup_smul_top g f hfg
        (fun y hy => mem_sup_range_of_exact_baseChange _ g f h y hy)).1

/-- **The local criterion 00MI at the top index, for a base change.** In the situation of
`ker_eq_range_of_exact_baseChange_quotient`, if `f` becomes injective after reducing modulo `J`
then `f` is injective. -/
private lemma injective_of_injective_baseChange_quotient {R A : Type*} [CommRing R] [CommRing A]
    [IsLocalRing R] [IsLocalRing A] [Algebra R A] [IsLocalHom (algebraMap R A)]
    [IsNoetherianRing A] [Module.Flat R A] {Y Z : Type*} [AddCommGroup Y] [Module A Y]
    [Module.Finite A Y] [AddCommGroup Z] [Module A Z] [Module.Flat A Z] (J : Ideal A)
    (hJ : J = (IsLocalRing.maximalIdeal R).map (algebraMap R A)) (f : Y →ₗ[A] Z)
    (h : Function.Injective (LinearMap.baseChange (A ⧸ J) f)) : Function.Injective f := by
  rw [← LinearMap.ker_eq_bot]
  refine
    (ker_eq_range_of_exact_baseChange_quotient J hJ (0 : Y →ₗ[A] Y) f (by simp) ?_).trans
      LinearMap.range_zero
  rw [LinearMap.exact_iff, LinearMap.baseChange_zero, LinearMap.range_zero, LinearMap.ker_eq_bot]
  exact h

/-- **The source's first step, from Lemma 00MI.** If the fibre complex `F̄_{•,𝔮}` is exact then so
is the localised complex `F_{•,𝔮}`.

Each `F_i` is free over `S` and `S` is flat over `R`, so `S_𝔮 ⊗_S F_i` is flat over `R` and hence
over `R_𝔭`; the local homomorphism `R_𝔭 → S_𝔮` of Noetherian local rings and the complex
`S_𝔮 ⊗_S F_•` therefore satisfy the hypotheses of Lemma 00MI, whose reduction modulo
`𝔪_{R_𝔭}` is `F̄_{•,𝔮}` by `Ideal.map_maximalIdeal_eq_map_under` and
`baseChangeExact_baseChange_iff`. -/
private theorem baseChangeExact_localization_of_baseChangeExact_fiber {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S] (e : ℕ)
    {F : ℕ → Type*} [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)] [∀ i, Module.Free S (F i)]
    [∀ i, Module.Finite S (F i)] (φ : ∀ i, F (i + 1) →ₗ[S] F i)
    (hφ : ∀ k < e, φ k ∘ₗ φ (k + 1) = 0) (q : Ideal S) [q.IsPrime]
    (hq : BaseChangeExact (fiberLocalRing R q) e φ) :
    BaseChangeExact (Localization.AtPrime q) e φ := by
  have _ : Module.Flat (Localization.AtPrime (q.under R)) (Localization.AtPrime q) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime (q.under R)) (q.under R).primeCompl
          (Localization.AtPrime q)).mpr
      inferInstance
  -- the fibre complex, read as a base change from `S_𝔮`
  obtain ⟨hqinj, hqex⟩ :=
    (baseChangeExact_baseChange_iff (Localization.AtPrime q) (fiberLocalRing R q) e φ).mpr hq
  -- the ideal the local criterion reduces modulo
  have hJ :
    (q.under R).map (algebraMap R (Localization.AtPrime q)) =
      Ideal.map (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q))
        (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R))) :=
    (Ideal.map_maximalIdeal_eq_map_under q).symm
  refine ⟨injective_of_injective_baseChange_quotient _ hJ _ hqinj, fun k hk => ?_⟩
  rw [LinearMap.exact_iff]
  exact
    ker_eq_range_of_exact_baseChange_quotient _ hJ _ _
      (by rw [← LinearMap.baseChange_comp, hφ k hk, LinearMap.baseChange_zero]) (hqex k hk)

/-! ### The complex of standard free modules over a base change -/

/-- The base change to `T` of a map between standard finite free `S`-modules, read as a map of
standard finite free `T`-modules: the matrix of `f` with its entries carried into `T`. -/
private noncomputable abbrev matBaseChange {S : Type*} [CommRing S] (T : Type*) [CommRing T]
    [Algebra S T] {a b : ℕ} (f : (Fin b → S) →ₗ[S] (Fin a → S)) : (Fin b → T) →ₗ[T] (Fin a → T) :=
  Matrix.toLin' ((LinearMap.toMatrix' f).map (algebraMap S T))

/-- The identification `T ⊗[S] (Fin m → S) = (Fin m → T)`. -/
private noncomputable abbrev tensorPiEquiv (S T : Type*) [CommRing S] [CommRing T] [Algebra S T]
    (m : ℕ) : T ⊗[S] (Fin m → S) ≃ₗ[T] (Fin m → T) :=
  (Algebra.TensorProduct.piScalarRight S T T (Fin m)).toLinearEquiv

/-- **The base change of a map of standard free modules, in coordinates.** Reading
`T ⊗[S] (Fin m → S)` as `Fin m → T` turns `LinearMap.baseChange T f` into `matBaseChange T f`. -/
private lemma matBaseChange_comp_tensorPiEquiv {S : Type*} [CommRing S] (T : Type*) [CommRing T]
    [Algebra S T] {a b : ℕ} (f : (Fin b → S) →ₗ[S] (Fin a → S)) :
    matBaseChange T f ∘ₗ ((tensorPiEquiv S T b) : T ⊗[S] (Fin b → S) →ₗ[T] (Fin b → T)) =
      ((tensorPiEquiv S T a) : T ⊗[S] (Fin a → S) →ₗ[T] (Fin a → T)) ∘ₗ
        LinearMap.baseChange T f := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul t v =>
    funext i
    have hfv : f v i = ∑ j, LinearMap.toMatrix' f i j * v j := by
      rw [LinearMap.pi_apply_eq_sum_univ f v]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, LinearMap.toMatrix'_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show (fun j' => if j = j' then (1 : S) else 0) = Pi.single j (1 : S) from by
          funext j'; simp [Pi.single_apply, eq_comm]]
      ring
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      AlgEquiv.toLinearEquiv_apply, Algebra.TensorProduct.piScalarRight_tmul_apply,
      LinearMap.baseChange_tmul, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
      hfv, Algebra.smul_def, map_sum, map_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring

/-- **Exactness of the base-changed complex, in coordinates.** -/
private lemma baseChangeExact_iff_matBaseChange {S : Type*} [CommRing S] (T : Type*) [CommRing T]
    [Algebra S T] (e : ℕ) (n : ℕ → ℕ) (φ : ∀ i, (Fin (n (i + 1)) → S) →ₗ[S] (Fin (n i) → S)) :
    BaseChangeExact (F := fun i => Fin (n i) → S) T e φ ↔
      (Function.Injective (matBaseChange T (φ e)) ∧
        ∀ k < e, Function.Exact (matBaseChange T (φ (k + 1))) (matBaseChange T (φ k))) := by
  exact
    (injective_and_exact_iff_of_ladder e (fun i => tensorPiEquiv S T (n i))
      fun i => matBaseChange_comp_tensorPiEquiv T (φ i)).symm

/-- The coordinate complex over `T` is a complex. -/
private lemma matBaseChange_comp_eq_zero {S : Type*} [CommRing S] (T : Type*) [CommRing T]
    [Algebra S T] {a b c : ℕ} (f : (Fin b → S) →ₗ[S] (Fin a → S))
    (g : (Fin c → S) →ₗ[S] (Fin b → S)) (h : f ∘ₗ g = 0) :
    matBaseChange T f ∘ₗ matBaseChange T g = 0 := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := (tensorPiEquiv S T c).surjective x
  have h1 := LinearMap.congr_fun (matBaseChange_comp_tensorPiEquiv T g) y
  have h2 :=
    LinearMap.congr_fun (matBaseChange_comp_tensorPiEquiv T f) (LinearMap.baseChange T g y)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.zero_apply] at h1 h2 ⊢
  rw [h1, h2, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, h, LinearMap.baseChange_zero,
    LinearMap.zero_apply, map_zero]

/-- The matrix of the coordinate complex over `T` is the entrywise image of the matrix over `S`. -/
private lemma toMatrix'_matBaseChange {S : Type*} [CommRing S] (T : Type*) [CommRing T]
    [Algebra S T] {a b : ℕ} (f : (Fin b → S) →ₗ[S] (Fin a → S)) :
    LinearMap.toMatrix' (matBaseChange T f) = (LinearMap.toMatrix' f).map (algebraMap S T) :=
  LinearMap.toMatrix'_toLin' _

/-- The ideal of `r × r` minors of the base-changed complex is the image of the ideal of `r × r`
minors: a minor of a matrix mapped entrywise is the image of that minor. -/
private lemma minorsIdeal_matBaseChange {S : Type*} [CommRing S] (T : Type*) [CommRing T]
    [Algebra S T] {a b : ℕ} (f : (Fin b → S) →ₗ[S] (Fin a → S)) (r : ℕ) :
    minorsIdeal (matBaseChange T f) r = (minorsIdeal f r).map (algebraMap S T) := by
  rw [minorsIdeal, minorsIdeal, Ideal.map_span, toMatrix'_matBaseChange]
  congr 1
  ext x
  constructor
  · rintro ⟨ρ, γ, rfl⟩
    exact ⟨_, ⟨ρ, γ, rfl⟩, by rw [Matrix.submatrix_map, RingHom.map_det, RingHom.mapMatrix_apply]⟩
  · rintro ⟨y, ⟨ρ, γ, rfl⟩, rfl⟩
    exact ⟨ρ, γ, by rw [Matrix.submatrix_map, RingHom.map_det, RingHom.mapMatrix_apply]⟩

/-- Depth along the zero ideal vanishes over a nonzero ring: a regular sequence with all its terms
zero must be empty, since `0` is not a nonzerodivisor. -/
private lemma not_one_le_depth_bot {T : Type*} [CommRing T] [Nontrivial T] :
    ¬(1 : ℕ∞) ≤ Module.depth T (⊥ : Ideal T) T := by
  classical
  have hne : (⊥ : Ideal T) • (⊤ : Submodule T T) ≠ ⊤ := by
    rw [Submodule.bot_smul]
    exact bot_ne_top
  have hzero :
    (⨆ rs ∈ {rs : List T | (∀ r ∈ rs, r ∈ (⊥ : Ideal T)) ∧ RingTheory.Sequence.IsRegular T rs},
        ((rs.length : ℕ) : ℕ∞)) =
      0 := by
    refine le_antisymm (iSup₂_le ?_) (by simp)
    rintro (_ | ⟨f, t⟩) ⟨hmem, hreg⟩
    · simp
    · exfalso
      have hf : f = 0 := Ideal.mem_bot.mp (hmem f (by simp))
      have hsmul : IsSMulRegular T f :=
        ((RingTheory.Sequence.isWeaklyRegular_cons_iff T f t).mp
            ((RingTheory.Sequence.isRegular_iff T _).mp hreg).1).1
      exact
        one_ne_zero
          (hsmul
            (show f • (1 : T) = f • 0 by
              rw [hf]; simp))
  rw [Module.depth, ite_eq_right hne, hzero]
  simp

/-- The ideal of `r × r` minors vanishes exactly when the `r`-th exterior power of the map does:
the minors are the generators of the ideal, and a nonzero one is exactly what makes `⋀^r f`
nonzero (Stacks 00MV). -/
private lemma minorsIdeal_eq_bot_iff {S : Type*} [CommRing S] {a b : ℕ}
    (f : (Fin b → S) →ₗ[S] (Fin a → S)) (r : ℕ) :
    minorsIdeal f r = ⊥ ↔ exteriorPower.map r f = 0 := by
  have hmv : (LinearMap.toMatrix' f).mulVecLin = f :=
    (Matrix.toLin'_apply' (LinearMap.toMatrix' f)).symm.trans (Matrix.toLin'_toMatrix' f)
  have h := Stacks.DeterminantalRank.exteriorPower_map_ne_zero_iff_exists_minor (LinearMap.toMatrix'
    f) r
  rw [hmv] at h
  constructor
  · intro hbot
    by_contra hne
    obtain ⟨x, ⟨ρ, γ, hx⟩, hx0⟩ := h.mp hne
    rw [minorsIdeal, Ideal.span_eq_bot] at hbot
    exact hx0 (hbot x ⟨ρ, γ, hx.symm⟩)
  · intro h0
    rw [minorsIdeal, Ideal.span_eq_bot]
    rintro x ⟨ρ, γ, rfl⟩
    by_contra hx0
    exact h.mpr ⟨_, ⟨ρ, γ, rfl⟩, hx0⟩ h0

/-- A nonzero `r × r` minor of the coordinate complex over `T` comes from a nonzero `r × r` minor
of the coordinate complex over an intermediate algebra `A`. -/
private lemma exteriorPower_map_ne_zero_of_matBaseChange {S : Type*} [CommRing S] (A T : Type*)
    [CommRing A] [CommRing T] [Algebra S A] [Algebra S T] [Algebra A T] [IsScalarTower S A T]
    {a b : ℕ} (f : (Fin b → S) →ₗ[S] (Fin a → S)) (r : ℕ)
    (h : exteriorPower.map r (matBaseChange T f) ≠ 0) :
    exteriorPower.map r (matBaseChange A f) ≠ 0 := by
  rw [Ne, ← minorsIdeal_eq_bot_iff] at h ⊢
  intro hbot
  refine h ?_
  rw [minorsIdeal_matBaseChange, IsScalarTower.algebraMap_eq S A T, ← Ideal.map_map, ←
    minorsIdeal_matBaseChange, hbot, Ideal.map_bot]

/-- **The Buchsbaum–Eisenbud criterion read in the fibre, from Proposition 00N1.** At a prime `𝔮`
at which the localised complex `F_{•,𝔮}` is already exact, the fibre complex `F̄_{•,𝔮}` is exact
if and only if for every `k ≤ e` the expected rank `r_k` is a natural number and the ideal of
`r_k × r_k` minors of `φ_k` has depth at least `k + 1` in `S_𝔮/𝔭S_𝔮`.

Proposition 00N1 over the Noetherian local ring `S_𝔮/𝔭S_𝔮` characterises exactness of `F̄_{•,𝔮}`
by the rank of `φ̄_k` being `r_k` together with that depth bound. Exactness of `F_{•,𝔮}` is what
makes the rank condition automatic: Proposition 00N1 over `S_𝔮` gives that `φ_k` has rank `r_k`
there, hence that `⋀^{r_k + 1} φ_k` vanishes over `S_𝔮` and so over its quotient
`S_𝔮/𝔭S_𝔮`, while `⋀^{r_k} φ̄_k ≠ 0` follows from the depth bound, the minors ideal of a map of
rank `< r_k` being zero and the depth of the zero ideal in a nonzero ring being `0`. -/
private theorem baseChangeExact_fiber_iff_forall_le_depth {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] (e : ℕ) (n : ℕ → ℕ)
    (φ : ∀ i, (Fin (n (i + 1)) → S) →ₗ[S] (Fin (n i) → S)) (hφ : ∀ k < e, φ k ∘ₗ φ (k + 1) = 0)
    (q : Ideal S) [q.IsPrime]
    (hloc : BaseChangeExact (F := fun i => Fin (n i) → S) (Localization.AtPrime q) e φ) :
    BaseChangeExact (F := fun i => Fin (n i) → S) (fiberLocalRing R q) e φ ↔
      ∀ k ≤ e,
        ∃ r : ℕ,
          (r : ℤ) = expectedRank e n k ∧
            ((k + 1 : ℕ) : ℕ∞) ≤
              Module.depth (fiberLocalRing R q)
                ((minorsIdeal (φ k) r).map (algebraMap S (fiberLocalRing R q)))
                (fiberLocalRing R q) := by
  have _ : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
  have hcompA :
    ∀ k < e,
      matBaseChange (Localization.AtPrime q) (φ k) ∘ₗ
          matBaseChange (Localization.AtPrime q) (φ (k + 1)) =
        0 :=
    fun k hk => matBaseChange_comp_eq_zero _ _ _ (hφ k hk)
  have hcompT :
    ∀ k < e,
      matBaseChange (fiberLocalRing R q) (φ k) ∘ₗ matBaseChange (fiberLocalRing R q) (φ (k + 1)) =
        0 :=
    fun k hk => matBaseChange_comp_eq_zero _ _ _ (hφ k hk)
  -- Proposition 00N1 over `S_𝔮`: exactness there pins the ranks of the `φ_k`
  have hA :=
    (LinearMap.injective_and_exact_iff_forall_rank_eq_and_le_depth_minors (R :=
          Localization.AtPrime q) e n (fun i => matBaseChange (Localization.AtPrime q) (φ i))
          hcompA).mp
      ((baseChangeExact_iff_matBaseChange (Localization.AtPrime q) e n φ).mp hloc)
  -- Proposition 00N1 over the fibre `S_𝔮/𝔭S_𝔮`
  rw [baseChangeExact_iff_matBaseChange (fiberLocalRing R q) e n φ,
    LinearMap.injective_and_exact_iff_forall_rank_eq_and_le_depth_minors (R := fiberLocalRing R q)
      e n (fun i => matBaseChange (fiberLocalRing R q) (φ i)) hcompT]
  refine forall_congr' fun k => imp_congr_right fun hk => ?_
  have hdepthEq :
    ∀ r : ℕ,
      Module.depth (fiberLocalRing R q) (minorsIdeal (matBaseChange (fiberLocalRing R q) (φ k)) r)
          (fiberLocalRing R q) =
        Module.depth (fiberLocalRing R q)
          ((minorsIdeal (φ k) r).map (algebraMap S (fiberLocalRing R q))) (fiberLocalRing R q) :=
    fun r => by rw [minorsIdeal_matBaseChange]
  constructor
  · rintro ⟨r, hr, -, hd⟩
    exact ⟨r, hr, hd.trans (le_of_eq (hdepthEq r))⟩
  · rintro ⟨r, hr, hd⟩
    obtain ⟨r', hr', hG', -⟩ := hA k hk
    obtain rfl : r = r' := by exact_mod_cast hr.trans hr'.symm
    refine ⟨r, hr, ⟨fun h0 => ?_, fun j hj => ?_⟩, hd.trans (le_of_eq (hdepthEq r).symm)⟩
    · have hbot : (minorsIdeal (φ k) r).map (algebraMap S (fiberLocalRing R q)) = ⊥ := by
        rw [← minorsIdeal_matBaseChange]
        exact (minorsIdeal_eq_bot_iff _ r).mpr h0
      rw [hbot] at hd
      exact not_one_le_depth_bot (le_trans (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)) hd)
    · exact
        hG'.2
          (exteriorPower_map_ne_zero_of_matBaseChange (Localization.AtPrime q) (fiberLocalRing R q)
            (φ k) j hj)

/-! ### The depth of the fibre local ring along an ideal of `S` -/

/-- A unit of a proper quotient of a local ring lifts to a unit: if `y*z - 1` lies in an ideal
inside the maximal ideal then `y*z` is a unit, hence so is `y`. -/
private lemma isUnit_of_isUnit_quotient_mk {A : Type*} [CommRing A] [IsLocalRing A] {J : Ideal A}
    (hJ : J ≤ IsLocalRing.maximalIdeal A) {y : A} (h : IsUnit (Ideal.Quotient.mk J y)) :
    IsUnit y := by
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp h
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective v
  rw [← map_mul, ← map_one (Ideal.Quotient.mk J), Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hv
  have hmem : y * z - 1 ∈ IsLocalRing.maximalIdeal A := hJ hv
  have hnot : y * z ∉ IsLocalRing.maximalIdeal A := fun hc => by
    refine (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
    simpa using Ideal.sub_mem _ hc hmem
  exact isUnit_of_mul_isUnit_left (IsLocalRing.notMem_maximalIdeal.mp hnot)

/-- An element of `S` outside `𝔮` becomes a unit in `S_𝔮/𝔭S_𝔮`. -/
private lemma isUnit_algebraMap_fiberLocalRing {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (q : Ideal S) [q.IsPrime] {x : S} (hxq : x ∉ q) :
    IsUnit (algebraMap S (fiberLocalRing R q) x) := by
  rw [IsScalarTower.algebraMap_apply S (Localization.AtPrime q) (fiberLocalRing R q)]
  exact (IsLocalization.map_units (Localization.AtPrime q) (⟨x, hxq⟩ : q.primeCompl)).map _

/-- An element of `𝔮` becomes a nonunit in `S_𝔮/𝔭S_𝔮`, hence lands in its maximal ideal. -/
private lemma algebraMap_mem_maximalIdeal_fiberLocalRing {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (q : Ideal S) [q.IsPrime] {x : S} (hxq : x ∈ q) :
    algebraMap S (fiberLocalRing R q) x ∈ IsLocalRing.maximalIdeal (fiberLocalRing R q) := by
  by_contra hnot
  have h1 : IsUnit (algebraMap S (fiberLocalRing R q) x) := IsLocalRing.notMem_maximalIdeal.mp hnot
  rw [IsScalarTower.algebraMap_apply S (Localization.AtPrime q) (fiberLocalRing R q)] at h1
  have h2 : IsUnit (algebraMap S (Localization.AtPrime q) x) :=
    isUnit_of_isUnit_quotient_mk (map_under_le_maximalIdeal (R := R) q) h1
  exact
    IsLocalRing.notMem_maximalIdeal.mpr h2
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q x).mpr hxq)

/-- **An element of `I` outside `𝔮` makes the depth `⊤`**: it is a unit in `S_𝔮/𝔭S_𝔮`, so the
image of `I` there is the unit ideal. -/
private lemma depth_map_eq_top_of_notMem {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal S) (q : Ideal S) [q.IsPrime] {x : S} (hxI : x ∈ I) (hxq : x ∉ q) :
    Module.depth (fiberLocalRing R q) (I.map (algebraMap S (fiberLocalRing R q)))
        (fiberLocalRing R q) =
      ⊤ :=
  depth_eq_top_of_isUnit_mem (Ideal.mem_map_of_mem _ hxI) (isUnit_algebraMap_fiberLocalRing q hxq)

/-- If `I ≤ 𝔮` then the image of `I` in `S_𝔮/𝔭S_𝔮` is a proper ideal. -/
private lemma map_le_maximalIdeal_fiberLocalRing {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (I : Ideal S) (q : Ideal S) [q.IsPrime] (hIq : I ≤ q) :
    I.map (algebraMap S (fiberLocalRing R q)) ≤ IsLocalRing.maximalIdeal (fiberLocalRing R q) := by
  rw [Ideal.map_le_iff_le_comap]
  exact fun x hx => algebraMap_mem_maximalIdeal_fiberLocalRing q (hIq hx)

/-- **Every element of `I·(S_𝔮/𝔭S_𝔮)` is the image of an element of `I` times a unit.** The ideal
`I S_𝔮` consists of the fractions `x/t` with `x ∈ I` and `t ∉ 𝔮`, and `S_𝔮/𝔭S_𝔮` is a quotient of
`S_𝔮`. -/
private lemma exists_mem_mul_isUnit_of_mem_map {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (I : Ideal S) (q : Ideal S) [q.IsPrime] {z : fiberLocalRing R q}
    (hz : z ∈ I.map (algebraMap S (fiberLocalRing R q))) :
    ∃ x ∈ I, ∃ u : fiberLocalRing R q, IsUnit u ∧ z = algebraMap S (fiberLocalRing R q) x * u := by
  have hmap :
    I.map (algebraMap S (fiberLocalRing R q)) =
      (I.map (algebraMap S (Localization.AtPrime q))).map
        (algebraMap (Localization.AtPrime q) (fiberLocalRing R q)) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  rw [hmap] at hz
  have hsurj : Function.Surjective (algebraMap (Localization.AtPrime q) (fiberLocalRing R q)) :=
    Ideal.Quotient.mk_surjective
  obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp hz
  obtain ⟨⟨⟨x, hxI⟩, ⟨t, ht⟩⟩, hxt⟩ :=
    IsLocalization.mem_map_algebraMap_iff (M := q.primeCompl) (S := Localization.AtPrime q) |>.mp
      hw
  have hunit : IsUnit (algebraMap S (Localization.AtPrime q) t) :=
    IsLocalization.map_units (Localization.AtPrime q) (⟨t, ht⟩ : q.primeCompl)
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hunit
  refine ⟨x, hxI, algebraMap (Localization.AtPrime q) (fiberLocalRing R q) v, ?_, ?_⟩
  · refine
      isUnit_iff_exists_inv.mpr
        ⟨algebraMap (Localization.AtPrime q) (fiberLocalRing R q)
            (algebraMap S (Localization.AtPrime q) t),
          ?_⟩
    rw [← map_mul, mul_comm, hv, map_one]
  · rw [IsScalarTower.algebraMap_apply S (Localization.AtPrime q) (fiberLocalRing R q), ← map_mul]
    congr 1
    calc
      w = w * (algebraMap S (Localization.AtPrime q) t * v) := by rw [hv, mul_one]
      _ = algebraMap S (Localization.AtPrime q) x * v := by rw [← mul_assoc, hxt]

/-- **Lifting a list of elements of `I·(S_𝔮/𝔭S_𝔮)`** to elements of `I` generating the same
ideal: the generators only change by units. -/
private lemma exists_list_mem_ofList_eq {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal S) (q : Ideal S) [q.IsPrime] (rs : List (fiberLocalRing R q))
    (hrs : ∀ z ∈ rs, z ∈ I.map (algebraMap S (fiberLocalRing R q))) :
    ∃ xs : List S,
      (∀ x ∈ xs, x ∈ I) ∧
        xs.length = rs.length ∧
        Ideal.ofList (xs.map (algebraMap S (fiberLocalRing R q))) = Ideal.ofList rs := by
  induction rs with
  | nil => exact ⟨[], by simp, by simp, by simp⟩
  | cons z t
    ih =>
    obtain ⟨xs, hxsI, hlen, hideal⟩ := ih fun y hy => hrs y (List.mem_cons_of_mem _ hy)
    obtain ⟨x, hxI, u, hu, hzx⟩ := exists_mem_mul_isUnit_of_mem_map I q (hrs z List.mem_cons_self)
    refine ⟨x :: xs, ?_, by simp [hlen], ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hxI
      · exact hxsI y hy
    · rw [List.map_cons, Ideal.ofList_cons, Ideal.ofList_cons, hideal, hzx]
      congr 1
      exact (Ideal.span_singleton_mul_right_unit hu _).symm

/-- **A depth bound is witnessed by a regular sequence.** -/
private lemma exists_isRegular_length_ge_of_le_depth {T : Type*} [CommRing T] {J : Ideal T}
    (hJ : J ≠ ⊤) {c : ℕ} (hc : (c : ℕ∞) ≤ Module.depth T J T) :
    ∃ rs : List T, (∀ r ∈ rs, r ∈ J) ∧ RingTheory.Sequence.IsRegular T rs ∧ c ≤ rs.length := by
  classical
  have hsmul : J • (⊤ : Submodule T T) ≠ ⊤ := by simpa using hJ
  have hnt : Nontrivial T := by
    rcases subsingleton_or_nontrivial T with h | h
    · exact
        absurd
          ((Ideal.eq_top_iff_one J).mpr
            (by
              rw [Subsingleton.elim (1 : T) 0]; exact J.zero_mem))
          hJ
    · exact h
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · exact ⟨[], by simp, RingTheory.Sequence.IsRegular.nil T T, by simp⟩
  by_contra hcon
  push Not at hcon
  rw [Module.depth, ite_eq_right hsmul] at hc
  have hle :
    (⨆ rs ∈ {rs : List T | (∀ r ∈ rs, r ∈ J) ∧ RingTheory.Sequence.IsRegular T rs},
        ((rs.length : ℕ) : ℕ∞)) ≤
      ((c - 1 : ℕ) : ℕ∞) := by
    refine iSup₂_le fun rs hrs => ?_
    have h := hcon rs hrs.1 hrs.2
    exact_mod_cast Nat.le_sub_one_of_lt h
  have : (c : ℕ∞) ≤ ((c - 1 : ℕ) : ℕ∞) := hc.trans hle
  have : c ≤ c - 1 := by exact_mod_cast this
  omega

/-- **The source's last step, from Lemma 00RA.** For a fixed ideal `I` of `S`, the set of primes
`𝔮` at which the depth of `I S_𝔮/𝔭S_𝔮` in `S_𝔮/𝔭S_𝔮` is at least `k` is open.

If `I S_𝔮` is the unit ideal then so is `I S_{𝔮'}` for every `𝔮'` in a basic open neighbourhood
of `𝔮`, and the depth of the unit ideal is `⊤`. Otherwise `I S_𝔮` contains a sequence
`f_1, …, f_k` which is regular in `S_𝔮/𝔭S_𝔮`, and after shrinking to a basic open neighbourhood
`f_1, …, f_k ∈ I`. Outside `V(f_1, …, f_k)` the ideal `I S_{𝔮'}` is the unit ideal, while inside
it the locus where `f_1, …, f_k` is regular in `S_{𝔮'}/𝔭'S_{𝔮'}` is open by Lemma 00RA; the union
of the complement of `V(f_1, …, f_k)` and that relatively open set is the complement of a closed
subset of `V(f_1, …, f_k)`, hence open, and it contains `𝔮`.

Lemma 00RA is stated for a ring map all of whose nonempty fibres are Cohen–Macaulay *and
equidimensional* of dimension `d`, which is strictly stronger than the hypothesis available here:
`R = k`, `S = k × k[x]`, `d = 1` has Cohen–Macaulay fibres of dimension `1` that are not
equidimensional. Applying Lemma 00RA therefore requires first shrinking `Spec S` to a
neighbourhood of `𝔮` on which the relative dimension is constant, which is possible because the
relative dimension of a flat ring map of finite type is locally constant. -/
private theorem exists_basicOpen_le_depth_map_fiberLocalRing {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing R] [Algebra.FiniteType R S] [Module.Flat R S]
    (d : ℕ)
    (hfib :
      ∀ (p : Ideal R) [p.IsPrime],
        Nontrivial (p.Fiber S) →
          (∀ (Q : Ideal (p.Fiber S)) [Q.IsPrime],
              Module.IsMaximalCohenMacaulay (Localization.AtPrime Q) (Localization.AtPrime Q)) ∧
            TopologicalSpace.Equidimensional (PrimeSpectrum (p.Fiber S)) ∧
            ringKrullDim (p.Fiber S) = (d : WithBot ℕ∞))
    (I : Ideal S) (k : ℕ) (q : PrimeSpectrum S)
    (hq :
      (k : ℕ∞) ≤
        Module.depth (fiberLocalRing R q.asIdeal)
          (I.map (algebraMap S (fiberLocalRing R q.asIdeal))) (fiberLocalRing R q.asIdeal)) :
    ∃ g : S,
      g ∉ q.asIdeal ∧
        ∀ q' ∈ PrimeSpectrum.basicOpen g,
          (k : ℕ∞) ≤
            Module.depth (fiberLocalRing R q'.asIdeal)
              (I.map (algebraMap S (fiberLocalRing R q'.asIdeal)))
              (fiberLocalRing R q'.asIdeal) := by
  classical
  have _ : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  -- if `I` is not contained in `𝔮` then `I` is the unit ideal on a neighbourhood of `𝔮`
  by_cases hIq : ∃ x ∈ I, x ∉ q.asIdeal
  · obtain ⟨x, hxI, hxq⟩ := hIq
    refine ⟨x, hxq, fun q' hq' => ?_⟩
    rw [depth_map_eq_top_of_notMem I q'.asIdeal hxI ((PrimeSpectrum.mem_basicOpen x q').mp hq')]
    exact le_top
  push Not at hIq
  have hIle : I ≤ q.asIdeal := fun x hx => hIq x hx
  -- the fibre local rings are Cohen–Macaulay
  have hnt : ∀ q' : PrimeSpectrum S, Nontrivial ((q'.asIdeal.under R).Fiber S) := fun q' =>
    (PrimeSpectrum.nontrivial_iff_mem_rangeComap
          (⟨q'.asIdeal.under R, inferInstance⟩ : PrimeSpectrum R)).mpr
      ⟨q', rfl⟩
  have hCM :
    ∀ q' : PrimeSpectrum S,
      Module.IsMaximalCohenMacaulay (fiberLocalRing R q'.asIdeal) (fiberLocalRing R q'.asIdeal) :=
    fun q' =>
    Algebra.isMaximalCohenMacaulay_quotient_map_under_localizationAtPrime q'.asIdeal
      (hfib (q'.asIdeal.under R) (hnt q')).1
  -- the image of `I` in `S_𝔮/𝔭S_𝔮` is a proper ideal, so the depth is a supremum of lengths
  have hJne : I.map (algebraMap S (fiberLocalRing R q.asIdeal)) ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (map_le_maximalIdeal_fiberLocalRing I q.asIdeal hIle)
  obtain ⟨rs, hrsJ, hrsreg, hrslen⟩ := exists_isRegular_length_ge_of_le_depth hJne hq
  have hrsmem : ∀ z ∈ rs, z ∈ IsLocalRing.maximalIdeal (fiberLocalRing R q.asIdeal) := fun z hz =>
    map_le_maximalIdeal_fiberLocalRing I q.asIdeal hIle (hrsJ z hz)
  have hreg' : RingTheory.Sequence.IsRegular (fiberLocalRing R q.asIdeal) (rs.take k) :=
    isRegular_take rs hrsreg k
  -- replace its terms by images of elements of `I`, which generate the same ideal
  obtain ⟨xs, hxsI, hxslen, hxsideal⟩ :=
    exists_list_mem_ofList_eq I q.asIdeal (rs.take k)
      (fun z hz => hrsJ z (List.mem_of_mem_take hz))
  have hxsk : xs.length = k := by
    rw [hxslen, List.length_take]; omega
  have hmemxs :
    ∀ q' : PrimeSpectrum S,
      (∀ x ∈ xs, x ∈ q'.asIdeal) →
        ∀ z ∈ xs.map (algebraMap S (fiberLocalRing R q'.asIdeal)),
          z ∈ IsLocalRing.maximalIdeal (fiberLocalRing R q'.asIdeal) := by
    intro q' hq' z hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    exact algebraMap_mem_maximalIdeal_fiberLocalRing q'.asIdeal (hq' x hx)
  have hxsq : ∀ x ∈ xs, x ∈ q.asIdeal := fun x hx => hIq x (hxsI x hx)
  -- the images of `xs` form a regular sequence at `𝔮`: in a Cohen–Macaulay local ring regularity
  -- of a sequence in the maximal ideal depends only on the ideal it generates (Lemma 02JN)
  have hxsreg :
    RingTheory.Sequence.IsRegular (fiberLocalRing R q.asIdeal)
      (xs.map (algebraMap S (fiberLocalRing R q.asIdeal))) := by
    have h1 :=
      (Module.IsMaximalCohenMacaulay.isRegular_iff_ringKrullDim_add_length_eq_ringKrullDim (hCM q)
          (xs.map (algebraMap S (fiberLocalRing R q.asIdeal))) (hmemxs q hxsq)).1
    have h2 :=
      (Module.IsMaximalCohenMacaulay.isRegular_iff_ringKrullDim_add_length_eq_ringKrullDim (hCM q)
          (rs.take k) (fun z hz => hrsmem z (List.mem_of_mem_take hz))).1
    refine h1.mpr ?_
    rw [hxsideal, List.length_map, hxslen]
    exact h2.mp hreg'
  -- Lemma 00RA: the locus in `V(xs)` where `xs` is regular in the fibre is open in `V(xs)`
  obtain ⟨V, hVopen, hVeq⟩ :=
    isOpen_induced_iff.mp
      (Algebra.isOpen_setOf_isRegular_fiber_of_isMaximalCohenMacaulay_of_equidimensional (R := R)
        (S := S) d hfib xs)
  have hZ : IsClosed (PrimeSpectrum.zeroLocus (Ideal.ofList xs : Set S)) :=
    PrimeSpectrum.isClosed_zeroLocus _
  have hofList_le : Ideal.ofList xs ≤ I := Ideal.span_le.mpr fun x hx => hxsI x hx
  have hqZ : q ∈ PrimeSpectrum.zeroLocus (Ideal.ofList xs : Set S) :=
    (PrimeSpectrum.mem_zeroLocus _ _).mpr (Ideal.span_le.mpr hxsq)
  have hqV : q ∈ V := by
    have h :
      (⟨q, hqZ⟩ : ↥(PrimeSpectrum.zeroLocus (Ideal.ofList xs : Set S))) ∈ Subtype.val ⁻¹' V := by
      rw [hVeq]
      exact hxsreg
    exact h
  obtain ⟨g, hgq, hgU⟩ :=
    exists_basicOpen_subset_of_isOpen (hZ.isOpen_compl.union hVopen) (Set.mem_union_right _ hqV)
  refine ⟨g, hgq, fun q' hq' => ?_⟩
  by_cases hq'Z : q' ∈ PrimeSpectrum.zeroLocus (Ideal.ofList xs : Set S)
  · -- inside `V(xs)`: Lemma 00RA makes `xs` regular in the fibre, which bounds the depth
    have hq'V : q' ∈ V := by
      rcases hgU hq' with h | h
      · exact absurd hq'Z h
      · exact h
    have hreg :
      RingTheory.Sequence.IsRegular (fiberLocalRing R q'.asIdeal)
        (xs.map (algebraMap S (fiberLocalRing R q'.asIdeal))) := by
      have h :
        (⟨q', hq'Z⟩ : ↥(PrimeSpectrum.zeroLocus (Ideal.ofList xs : Set S))) ∈ Subtype.val ⁻¹' V :=
        hq'V
      rw [hVeq] at h
      exact h
    have h :=
      Module.le_depth_of_isRegular (I.map (algebraMap S (fiberLocalRing R q'.asIdeal)))
        (rs := xs.map (algebraMap S (fiberLocalRing R q'.asIdeal)))
        (fun z hz => by
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
          exact Ideal.mem_map_of_mem _ (hxsI x hx))
        hreg
    rwa [List.length_map, hxsk] at h
  · -- outside `V(xs)`: some element of `I` is a unit in the fibre, so the depth is `⊤`
    rw [PrimeSpectrum.mem_zeroLocus] at hq'Z
    obtain ⟨z, hzmem, hznot⟩ := Set.not_subset.mp hq'Z
    rw [depth_map_eq_top_of_notMem I q'.asIdeal (hofList_le hzmem) hznot]
    exact le_top

/-- **The source's reduction for Stacks 00RB, for a complex of standard finite free modules.**
A prime `𝔮` at which the fibre complex is exact has a basic open neighbourhood inside the locus
where it is exact.

The three steps are the source's: Lemma 00MI turns exactness of `F̄_{•,𝔮}` into exactness of
`F_{•,𝔮}`, which by `isOpen_setOf_baseChangeExact_localization` persists on an open neighbourhood
`U` of `𝔮`; on `U` Proposition 00N1 reduces exactness of the fibre complex to depth bounds on the
ideals of minors of the `φ_k`, uniformly in the prime; and each of those `e + 1` depth conditions
holds on a basic open neighbourhood of `𝔮` by Lemma 00RA. -/
private theorem exists_basicOpen_subset_setOf_baseChangeExact_fiber_std {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.FiniteType R S]
    [Module.Flat R S] (d : ℕ)
    (hfib :
      ∀ (p : Ideal R) [p.IsPrime],
        Nontrivial (p.Fiber S) →
          (∀ (Q : Ideal (p.Fiber S)) [Q.IsPrime],
              Module.IsMaximalCohenMacaulay (Localization.AtPrime Q) (Localization.AtPrime Q)) ∧
            TopologicalSpace.Equidimensional (PrimeSpectrum (p.Fiber S)) ∧
            ringKrullDim (p.Fiber S) = (d : WithBot ℕ∞))
    (e : ℕ) (n : ℕ → ℕ) (φ : ∀ i, (Fin (n (i + 1)) → S) →ₗ[S] (Fin (n i) → S))
    (hφ : ∀ k < e, φ k ∘ₗ φ (k + 1) = 0) (q : PrimeSpectrum S)
    (hq : BaseChangeExact (F := fun i => Fin (n i) → S) (fiberLocalRing R q.asIdeal) e φ) :
    ∃ g : S,
      g ∉ q.asIdeal ∧
        ∀ q' ∈ PrimeSpectrum.basicOpen g,
          BaseChangeExact (F := fun i => Fin (n i) → S) (fiberLocalRing R q'.asIdeal) e φ := by
  have hUopen :
    IsOpen
      {q' : PrimeSpectrum S |
        BaseChangeExact (F := fun i => Fin (n i) → S) (Localization.AtPrime q'.asIdeal) e φ} :=
    isOpen_setOf_baseChangeExact_localization (F := fun i => Fin (n i) → S) e φ hφ
  have hqU : BaseChangeExact (F := fun i => Fin (n i) → S) (Localization.AtPrime q.asIdeal) e φ :=
    baseChangeExact_localization_of_baseChangeExact_fiber (F := fun i => Fin (n i) → S) e φ hφ
      q.asIdeal hq
  rw [baseChangeExact_fiber_iff_forall_le_depth e n φ hφ q.asIdeal hqU] at hq
  choose! r hr hdepth using hq
  have hstep :
    ∀ k,
      k ≤ e →
        ∃ g : S,
          g ∉ q.asIdeal ∧
            ∀ q' ∈ PrimeSpectrum.basicOpen g,
              ((k + 1 : ℕ) : ℕ∞) ≤
                Module.depth (fiberLocalRing R q'.asIdeal)
                  ((minorsIdeal (φ k) (r k)).map (algebraMap S (fiberLocalRing R q'.asIdeal)))
                  (fiberLocalRing R q'.asIdeal) :=
    fun k hk =>
    exists_basicOpen_le_depth_map_fiberLocalRing d hfib (minorsIdeal (φ k) (r k)) (k + 1) q
      (hdepth k hk)
  choose! G hGq hG using hstep
  have hWopen :
    IsOpen
      ({q' : PrimeSpectrum S |
          BaseChangeExact (F := fun i => Fin (n i) → S) (Localization.AtPrime q'.asIdeal) e φ} ∩
        ⋂ k : Fin (e + 1), ↑(PrimeSpectrum.basicOpen (G k.1))) :=
    hUopen.inter (isOpen_iInter_of_finite fun k => (PrimeSpectrum.basicOpen (G k.1)).isOpen)
  have hqW :
    q ∈
      ({q' : PrimeSpectrum S |
          BaseChangeExact (F := fun i => Fin (n i) → S) (Localization.AtPrime q'.asIdeal) e φ} ∩
        ⋂ k : Fin (e + 1), ↑(PrimeSpectrum.basicOpen (G k.1))) :=
    ⟨hqU,
      Set.mem_iInter.mpr fun k =>
        PrimeSpectrum.mem_basicOpen _ _ |>.mpr (hGq k.1 (Nat.lt_succ_iff.mp k.2))⟩
  obtain ⟨g, hgq, hgW⟩ := exists_basicOpen_subset_of_isOpen hWopen hqW
  refine ⟨g, hgq, fun q' hq' => ?_⟩
  obtain ⟨hq'U, hq'G⟩ := hgW hq'
  rw [baseChangeExact_fiber_iff_forall_le_depth e n φ hφ q'.asIdeal hq'U]
  intro k hk
  exact ⟨r k, hr k hk, hG k hk q' (Set.mem_iInter.mp hq'G ⟨k, Nat.lt_succ_iff.mpr hk⟩)⟩

/-- **The source's reduction for Stacks 00RB.** A prime `𝔮` at which the fibre complex
`F̄_{•,𝔮} = (S_𝔮/𝔭S_𝔮) ⊗_S F_•` is exact has a basic open neighbourhood `D(g)` inside the locus
where the fibre complex is exact; equivalently, after replacing `S` by `S_g` the locus is all of
`Spec S`.

Exactness of `F̄_{•,𝔮}` gives, by Lemma 00MI applied to `R_𝔭 → S_𝔮`, exactness of the localised
complex `F_{•,𝔮}`, hence of `F_•` over `S_g` for some `g ∉ 𝔮`
(`isOpen_setOf_baseChangeExact_localization`). Over `S_g`, Proposition 00N1 applied at every
prime bounds the rank of `φ_i` by the expected rank `r_i = n_i - n_{i+1} + ⋯ ± n_e`, and then, for
`I_i` the ideal of `r_i × r_i` minors of `φ_i`, it says that `F̄_{•,𝔮'}` is exact if and only if
for each `1 ≤ i ≤ e` either `(I_i)_{𝔮'}` is the unit ideal — an open condition — or it contains a
sequence which is regular in `S_{𝔮'}/𝔭'S_{𝔮'}`, and outside the zero locus of such a sequence
`I_i` is already the unit ideal, so that alternative is open by Lemma 00RA. -/
private theorem exists_basicOpen_subset_setOf_baseChangeExact_fiber {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing R] [Algebra.FiniteType R S] [Module.Flat R S]
    (d : ℕ)
    (hfib :
      ∀ (p : Ideal R) [p.IsPrime],
        Nontrivial (p.Fiber S) →
          (∀ (Q : Ideal (p.Fiber S)) [Q.IsPrime],
              Module.IsMaximalCohenMacaulay (Localization.AtPrime Q) (Localization.AtPrime Q)) ∧
            TopologicalSpace.Equidimensional (PrimeSpectrum (p.Fiber S)) ∧
            ringKrullDim (p.Fiber S) = (d : WithBot ℕ∞))
    (e : ℕ) (F : ℕ → Type*) [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    [∀ i, Module.Free S (F i)] [∀ i, Module.Finite S (F i)] (φ : ∀ i, F (i + 1) →ₗ[S] F i)
    (hφ : ∀ k < e, φ k ∘ₗ φ (k + 1) = 0) (q : PrimeSpectrum S)
    (hq : BaseChangeExact (fiberLocalRing R q.asIdeal) e φ) :
    ∃ g : S,
      g ∉ q.asIdeal ∧
        ∀ q' ∈ PrimeSpectrum.basicOpen g, BaseChangeExact (fiberLocalRing R q'.asIdeal) e φ := by
  classical
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  obtain ⟨n, ⟨b⟩⟩ : ∃ n : ℕ → ℕ, Nonempty (∀ i, Module.Basis (Fin (n i)) S (F i)) :=
    ⟨fun i => Fintype.card (Module.Free.ChooseBasisIndex S (F i)),
      ⟨fun i => (Module.Free.chooseBasis S (F i)).reindex (Fintype.equivFin _)⟩⟩
  set E : ∀ i, F i ≃ₗ[S] (Fin (n i) → S) := fun i => (b i).equivFun with hEdef
  set ψ : ∀ i, (Fin (n (i + 1)) → S) →ₗ[S] (Fin (n i) → S) := fun i =>
    (E i).toLinearMap ∘ₗ φ i ∘ₗ (E (i + 1)).symm.toLinearMap with hψdef
  have hsq :
    ∀ i,
      ψ i ∘ₗ (E (i + 1) : F (i + 1) →ₗ[S] (Fin (n (i + 1)) → S)) =
        (E i : F i →ₗ[S] (Fin (n i) → S)) ∘ₗ φ i := by
    intro i
    refine LinearMap.ext fun x => ?_
    simp [hψdef]
  have hψ : ∀ k < e, ψ k ∘ₗ ψ (k + 1) = 0 := by
    intro k hk
    refine LinearMap.ext fun x => ?_
    have h0 := LinearMap.congr_fun (hφ k hk) ((E (k + 1 + 1)).symm x)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply] at h0
    simp only [hψdef, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.zero_apply]
    rw [h0, map_zero]
  obtain ⟨g, hgq, hg⟩ :=
    exists_basicOpen_subset_setOf_baseChangeExact_fiber_std d hfib e n ψ hψ q
      ((baseChangeExact_congr (G := fun i => Fin (n i) → S) _ e φ ψ E hsq).mpr hq)
  exact
    ⟨g, hgq, fun q' hq' =>
      (baseChangeExact_congr (G := fun i => Fin (n i) → S) _ e φ ψ E hsq).mp (hg q' hq')⟩

/-- **Stacks 00RB.** Let `R` be Noetherian, let `R → S` be a flat ring map of finite type all of
whose nonempty fibres `S ⊗_R κ(𝔭)` are Cohen–Macaulay of dimension `d`, and let
`0 → F_{e+1} →[φ e] F_e → ⋯ → F_1 →[φ 0] F_0` be a finite complex of finite free `S`-modules.
Then the set of primes `𝔮` of `S` at which the fibre complex `(S_𝔮/𝔭S_𝔮) ⊗_S F_•`, where
`𝔭 = R ∩ 𝔮`, is exact at `F̄_{e+1}, …, F̄_1` is open in `Spec S`. -/
public theorem solution {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.FiniteType R S] [Module.Flat R S] (d : ℕ)
    (hfib :
      ∀ (p : Ideal R) [p.IsPrime],
        Nontrivial (p.Fiber S) →
          (∀ (Q : Ideal (p.Fiber S)) [Q.IsPrime],
              Module.IsMaximalCohenMacaulay (Localization.AtPrime Q) (Localization.AtPrime Q)) ∧
            TopologicalSpace.Equidimensional (PrimeSpectrum (p.Fiber S)) ∧
            ringKrullDim (p.Fiber S) = (d : WithBot ℕ∞))
    (e : ℕ) (F : ℕ → Type*) [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    [∀ i, Module.Free S (F i)] [∀ i, Module.Finite S (F i)] (φ : ∀ i, F (i + 1) →ₗ[S] F i)
    (hφ : ∀ k < e, φ k ∘ₗ φ (k + 1) = 0) :
    IsOpen
      {q : PrimeSpectrum S |
        Function.Injective
            (LinearMap.baseChange
              (Localization.AtPrime q.asIdeal ⧸
                (q.asIdeal.under R).map (algebraMap R (Localization.AtPrime q.asIdeal)))
              (φ e)) ∧
          ∀ k < e,
            Function.Exact
              (LinearMap.baseChange
                (Localization.AtPrime q.asIdeal ⧸
                  (q.asIdeal.under R).map (algebraMap R (Localization.AtPrime q.asIdeal)))
                (φ (k + 1)))
              (LinearMap.baseChange
                (Localization.AtPrime q.asIdeal ⧸
                  (q.asIdeal.under R).map (algebraMap R (Localization.AtPrime q.asIdeal)))
                (φ k))} := by
  rw [isOpen_iff_forall_mem_open]
  intro q hq
  obtain ⟨g, hgq, hg⟩ := exists_basicOpen_subset_setOf_baseChangeExact_fiber d hfib e F φ hφ q hq
  exact
    ⟨PrimeSpectrum.basicOpen g, fun q' hq' => hg q' hq', (PrimeSpectrum.basicOpen g).isOpen,
      (PrimeSpectrum.mem_basicOpen g q).mpr hgq⟩

end Stacks.Flatness.FibreExactnessLocus

namespace Algebra
open Stacks.RegularSequence.FibrewiseLocus

/-- **Stacks 00RB, for equidimensional fibres.** Let `R` be Noetherian, let `R → S` be a flat ring
map of finite type all of whose nonempty fibres `S ⊗_R κ(𝔭)` are Cohen–Macaulay (each of their
local rings `A` satisfies `depth_{𝔪_A}(A) = dim A`) and equidimensional of dimension `d`, and let
`0 → F_{e+1} →[φ e] F_e → ⋯ → F_1 →[φ 0] F_0` be a finite complex of finite free `S`-modules. Then
the set of primes `𝔮` of `S` at which the fibre complex
`F̄_{•,𝔮} = F_{•,𝔮} ⊗_R κ(𝔭) = (S_𝔮/𝔭S_𝔮) ⊗_S F_•`, where `𝔭 = R ∩ 𝔮`, is exact at
`F̄_{e+1}, …, F̄_1` is open in `Spec S`.

Equidimensionality of the fibres is the hypothesis the source's proof consumes, through Lemma
00RA, and it is what Theorem 00RC needs, where the lemma is applied to a polynomial ring over `R`;
the source's own statement asks only that the fibres be Cohen–Macaulay of dimension `d`, and
follows from Theorem 00RC through Lemma 00RH. See the module docstring. -/
public theorem
  isOpen_setOf_exact_baseChange_fiber_of_flat_of_isMaximalCohenMacaulay_of_equidimensional
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.FiniteType R S] [Module.Flat R S] (d : ℕ)
    (hfib :
      ∀ (p : Ideal R) [p.IsPrime],
        Nontrivial (p.Fiber S) →
          (∀ (Q : Ideal (p.Fiber S)) [Q.IsPrime],
              Module.IsMaximalCohenMacaulay (Localization.AtPrime Q) (Localization.AtPrime Q)) ∧
            TopologicalSpace.Equidimensional (PrimeSpectrum (p.Fiber S)) ∧
            ringKrullDim (p.Fiber S) = (d : WithBot ℕ∞))
    (e : ℕ) (F : ℕ → Type*) [∀ i, AddCommGroup (F i)] [∀ i, Module S (F i)]
    [∀ i, Module.Free S (F i)] [∀ i, Module.Finite S (F i)] (φ : ∀ i, F (i + 1) →ₗ[S] F i)
    (hφ : ∀ k < e, φ k ∘ₗ φ (k + 1) = 0) :
    IsOpen
      {q : PrimeSpectrum S |
        Function.Injective
            (LinearMap.baseChange
              (Localization.AtPrime q.asIdeal ⧸
                (q.asIdeal.under R).map (algebraMap R (Localization.AtPrime q.asIdeal)))
              (φ e)) ∧
          ∀ k < e,
            Function.Exact
              (LinearMap.baseChange
                (Localization.AtPrime q.asIdeal ⧸
                  (q.asIdeal.under R).map (algebraMap R (Localization.AtPrime q.asIdeal)))
                (φ (k + 1)))
              (LinearMap.baseChange
                (Localization.AtPrime q.asIdeal ⧸
                  (q.asIdeal.under R).map (algebraMap R (Localization.AtPrime q.asIdeal)))
                (φ k))} :=
  Stacks.Flatness.FibreExactnessLocus.solution d hfib e F φ hφ

end Algebra
