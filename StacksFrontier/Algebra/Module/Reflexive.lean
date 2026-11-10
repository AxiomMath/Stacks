module

public import StacksFrontier.Algebra.Module.LocalizedEquiv
public import StacksFrontier.RingTheory.Depth.UnqualifiedDepth
public import StacksFrontier.RingTheory.Depth.Nakayama
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.List.TFAE
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.TensorProduct.Free
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Adjoin.FG
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.DepthSubsingleton
public import StacksFrontier.Algebra.Module.Reflexive.Localization
public import StacksFrontier.Algebra.Module.TorsionFree
public import StacksFrontier.RingTheory.AssociatedPrime.Injective
public import StacksFrontier.RingTheory.Depth.Defs
public import StacksFrontier.RingTheory.Depth.Localization
public import StacksFrontier.RingTheory.Depth.ShortExact
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Basic
public import StacksFrontier.RingTheory.Serre.Criterion
public import StacksFrontier.RingTheory.Serre.Defs
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Algebra.Module.LocalizedRingEquiv
public import StacksFrontier.Algebra.Module.DepthRegularElement

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

universe u v w x

/-!
# Reflexive modules

A module is *reflexive* when the canonical evaluation map into its double dual, the *reflexive
hull*, is an isomorphism. This file develops the theory of reflexive modules over Noetherian
domains: the comparison with torsion-freeness, the characterisation by short exact sequences with
finite free middle term, stability under `Hom` and under flat base change, the local criteria in
terms of depth and associated primes, the description over a normal domain by Serre's condition
`(S₂)` and as an intersection of height-one localisations, and a counterexample showing that a
finite reflexive `(S₂)` module can live over a ring which is not itself `(S₂)`.

## Main results

* `isTorsionFree_of_isReflexive_and_dualEval_isTorsion_and_injective_iff`: over a domain a
  reflexive module is torsion-free, and for a finite module the kernel and cokernel of the
  evaluation map are torsion while the evaluation map is injective exactly when the module is
  torsion-free.
* `isReflexive_of_exact_of_isReflexive_of_isTorsionFree`: reflexivity descends to the kernel of a
  map from a reflexive module to a torsion-free module.
* `isReflexive_iff_exists_finFree_shortExact`: a finite module over a Noetherian domain is
  reflexive exactly when it is the kernel of a surjection from a finite free module onto a
  torsion-free module.
* `isReflexive_linearMap`, `isReflexive_baseChange_of_flat`: reflexivity is inherited by modules
  of linear maps and is stable under flat base change.
* `one_le_depth_and_two_le_depth_linearMap`, `propertySk_linearMap_one_two_and_isTorsionFree`,
  `depth_localized_ge_two_and_propertyS2_of_isReflexive`: the depth and Serre-condition
  properties of `Hom` modules and of reflexive modules.
* `bijective_of_bijective_localized_or_depth_two_and_notMem_associatedPrimes`,
  `bijective_of_bijective_localized_or_depth_two_of_isTorsionFree`,
  `isReflexive_iff_localized_isReflexive_or_depth_two`: the local criteria.
* `isReflexive_isTorsionFree_propertyS2_intersection_tfae`,
  `reflexiveHull_eq_iInf_localization_mod_torsion`, `integralClosure_isReflexive`: the theory over
  a Noetherian normal domain.
* `mvPolynomial_adjoin_reflexive_propertyS2_module_not_propertyS2`: the example of Stacks 0EBB.

## References

* [Stacks Project, Tag 0AUZ](https://stacks.math.columbia.edu/tag/0AUZ)
* [Stacks Project, Tag 0AV0](https://stacks.math.columbia.edu/tag/0AV0)
* [Stacks Project, Tag 0AV2](https://stacks.math.columbia.edu/tag/0AV2)
* [Stacks Project, Tag 0AV3](https://stacks.math.columbia.edu/tag/0AV3)
* [Stacks Project, Tag 0AV4](https://stacks.math.columbia.edu/tag/0AV4)
* [Stacks Project, Tag 0AV5](https://stacks.math.columbia.edu/tag/0AV5)
* [Stacks Project, Tag 0AV6](https://stacks.math.columbia.edu/tag/0AV6)
* [Stacks Project, Tag 0AV8](https://stacks.math.columbia.edu/tag/0AV8)
* [Stacks Project, Tag 0AV9](https://stacks.math.columbia.edu/tag/0AV9)
* [Stacks Project, Tag 0AVA](https://stacks.math.columbia.edu/tag/0AVA)
* [Stacks Project, Tag 0AVB](https://stacks.math.columbia.edu/tag/0AVB)
* [Stacks Project, Tag 0AVC](https://stacks.math.columbia.edu/tag/0AVC)
* [Stacks Project, Tag 0B36](https://stacks.math.columbia.edu/tag/0B36)
* [Stacks Project, Tag 0BM4](https://stacks.math.columbia.edu/tag/0BM4)
* [Stacks Project, Tag 0EB8](https://stacks.math.columbia.edu/tag/0EB8)
* [Stacks Project, Tag 0EB9](https://stacks.math.columbia.edu/tag/0EB9)
* [Stacks Project, Tag 0EBA](https://stacks.math.columbia.edu/tag/0EBA)
* [Stacks Project, Tag 0EBB](https://stacks.math.columbia.edu/tag/0EBB)
-/

/-! ### The reflexive hull -/

/-- **Stacks Tag 0AV4.** The reflexive hull of an `R`-module `M` is its double dual
`Hom_R(Hom_R(M, R), R)`. -/
@[stacks 0AV4]
abbrev Module.reflexiveHull (R : Type u) [CommSemiring R]
    (M : Type v) [AddCommMonoid M] [Module R M] :=
  Module.Dual R (Module.Dual R M)

/-! ### Shared helpers

The lemmas of this section are used by several of the results below; each of them is recorded once
here rather than once per result. -/

/-- Over a domain, a linear functional on a module factors through the quotient by the torsion
submodule, so restriction along that quotient map is surjective on duals. -/
theorem dualMap_mkQ_torsion_surjective
    {R : Type u} [CommRing R] [IsDomain R]
    {M : Type v} [AddCommGroup M] [Module R M] :
    Function.Surjective (Submodule.torsion R M).mkQ.dualMap := by
  intro f
  refine ⟨(Submodule.torsion R M).liftQ f ?_, ?_⟩
  · intro m hm
    obtain ⟨s, hs⟩ := (Submodule.mem_torsion_iff m).mp hm
    apply (smul_right_injective (M := R) (nonZeroDivisors.ne_zero s.property))
    simpa only [Submonoid.smul_def, map_smul, map_zero, smul_zero] using congrArg f hs
  · ext m
    rfl

/-- Linear maps out of a finite free module are the same thing as tuples of elements of the
target. -/
private noncomputable def linearMapFinFreeEquivPi
    {R : Type u} [CommRing R] {N : Type w} [AddCommGroup N] [Module R N] (n : ℕ) :
    ((Fin n → R) →ₗ[R] N) ≃ₗ[R] (Fin n → N) :=
  ((Pi.basisFun R (Fin n)).constr R).symm

/-- The unqualified depth over a local ring is invariant under linear equivalence. -/
public lemma moduleDepth_eq_of_linearEquiv {R : Type*} [CommRing R] [IsLocalRing R]
    {A B : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (e : A ≃ₗ[R] B) : moduleDepth R A = moduleDepth R B := by
  unfold moduleDepth
  simp only [e.isRegular_congr]

/-- The dimension of the support is invariant under linear equivalence. -/
public lemma moduleSupportDim_eq_of_linearEquiv {R : Type*} [CommRing R]
    {A B : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (e : A ≃ₗ[R] B) : moduleSupportDim R A = moduleSupportDim R B := by
  unfold moduleSupportDim
  rw [e.support_eq]

/-- The support of a ring as a module over itself is its whole spectrum, so the two notions of
dimension agree. -/
private lemma moduleSupportDim_self_eq_ringKrullDim (R : Type*) [CommRing R] :
    moduleSupportDim R R = ringKrullDim R := by
  unfold moduleSupportDim
  rw [show Module.support R R = Set.univ by
    ext p
    rw [Module.mem_support_iff]
    simp only [Set.mem_univ, iff_true]
    infer_instance]
  exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph).trans
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim R)

/-- Serre's condition for a ring is the same as Serre's condition for the ring viewed as a module
over itself. -/
@[ega "IV 5.7.2" "special case"]
public lemma propertySkModule_self_iff_propertySkRing {R : Type*} [CommRing R]
    [IsNoetherianRing R] (n : ℕ) :
    PropertySkModule R R n ↔ PropertySkRing R n := by
  constructor <;> intro h p hp
  · have hp' := h p
    rw [moduleSupportDim_eq_of_linearEquiv (localizedRingEquiv p),
      moduleSupportDim_self_eq_ringKrullDim,
      moduleDepth_eq_of_linearEquiv (localizedRingEquiv p)] at hp'
    exact hp'
  · rw [moduleSupportDim_eq_of_linearEquiv (localizedRingEquiv p),
      moduleSupportDim_self_eq_ringKrullDim,
      moduleDepth_eq_of_linearEquiv (localizedRingEquiv p)]
    exact h p

/-- Serre's condition for modules is invariant under linear equivalence. -/
public theorem propertySkModule_of_linearEquiv {R : Type*} [CommRing R] [IsNoetherianRing R]
    {A B : Type*} [AddCommGroup A] [Module R A] [Module.Finite R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B] (e : A ≃ₗ[R] B) (k : ℕ)
    (h : PropertySkModule R B k) : PropertySkModule R A k := by
  intro p _
  rw [moduleSupportDim_eq_of_linearEquiv (Module.localizedEquiv p.primeCompl e),
    moduleDepth_eq_of_linearEquiv (Module.localizedEquiv p.primeCompl e)]
  exact h p

/-- At a prime `p`, the maximal ideal of the localized ring is an associated prime of the
localized module exactly when `p` is an associated prime of the module. -/
private lemma maximalIdeal_mem_associatedPrimes_localized_iff
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (p : Ideal R) [p.IsPrime] :
    IsLocalRing.maximalIdeal (Localization.AtPrime p) ∈
        associatedPrimes (Localization.AtPrime p) (LocalizedModule p.primeCompl M) ↔
      p ∈ associatedPrimes R M := by
  rw [←
    Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
    p.primeCompl (Localization.AtPrime p) (LocalizedModule.mkLinearMap p.primeCompl M)]
  change (Ideal.comap (algebraMap R (Localization.AtPrime p))
    (IsLocalRing.maximalIdeal (Localization.AtPrime p)) ∈ associatedPrimes R M) ↔ _
  rw [show Ideal.comap (algebraMap R (Localization.AtPrime p))
    (IsLocalRing.maximalIdeal (Localization.AtPrime p)) = p from
      Localization.AtPrime.under_maximalIdeal]

/-- A regular sequence inside the maximal ideal gives a lower bound on the depth. -/
private lemma length_le_moduleDepth {R X : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup X] [Module R X] {rs : List R}
    (hmem : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R)
    (hreg : RingTheory.Sequence.IsRegular X rs) :
    (rs.length : ℕ∞) ≤ moduleDepth R X := by
  unfold moduleDepth
  exact le_iSup_of_le rs (le_iSup_of_le (And.intro hmem hreg) le_rfl)

/-! ### Reflexive and finite modules over a domain

Over a domain a reflexive module is torsion-free, and for a finite module the canonical evaluation
map into the reflexive hull is injective with torsion kernel and cokernel. -/

/-- A linear map out of a finite module into a localised module lifts, after multiplying by a
single denominator, to a map into the unlocalised module. -/
private lemma finite_lift_of_isLocalizedModule_of_injective
    {R M N N' : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (S : Submonoid R) (f : N →ₗ[R] N') [IsLocalizedModule S f]
    [Module.Finite R M] (g : M →ₗ[R] N') (hf : Function.Injective f) :
    ∃ (h : M →ₗ[R] N) (s : S), f ∘ₗ h = s • g := by
  classical
  obtain ⟨σ, hσ⟩ := (inferInstance : Module.Finite R M)
  let π := Finsupp.linearCombination R ((↑) : σ → M)
  have hπ : Function.Surjective π :=
    LinearMap.range_eq_top.mp (by rw [Finsupp.range_linearCombination, Subtype.range_val, ← hσ])
  choose q hq using IsLocalizedModule.surj S f
  let i : σ → N := fun x ↦
    (∏ j ∈ σ.erase x.1, (q (g j)).2) • (q (g x)).1
  let s₀ := ∏ j ∈ σ, (q (g j)).2
  have hi : f ∘ₗ Finsupp.linearCombination R i = (s₀ • g) ∘ₗ π := by
    ext j
    simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
      Finsupp.linearCombination_single, one_smul, LinearMap.map_smul_of_tower, ← hq,
      LinearMap.smul_apply, i, s₀, π]
    rw [← mul_smul, Finset.prod_erase_mul]
    exact j.prop
  have hker : LinearMap.ker π ≤ LinearMap.ker (Finsupp.linearCombination R i) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    apply hf
    rw [← LinearMap.comp_apply, hi, LinearMap.comp_apply, hx, map_zero]
    simp
  refine ⟨Submodule.liftQ _ _ hker ∘ₗ
      (LinearMap.quotKerEquivOfSurjective _ hπ).symm.toLinearMap, s₀, ?_⟩
  ext x
  obtain ⟨x, rfl⟩ := hπ x
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← hi]
  simp

/-- A finite module over a domain is sandwiched between a finite free module and itself, up to
multiplication by a single nonzero scalar in both directions. -/
private lemma exists_scalar_retract
    {R : Type u} [CommRing R] [IsDomain R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (ι : Type (max u v)), Nonempty (Fintype ι) ∧
      ∃ a : (ι → R) →ₗ[R] M, ∃ b : M →ₗ[R] (ι → R), ∃ c : nonZeroDivisors R,
        a.comp b = c • LinearMap.id ∧ b.comp a = c • LinearMap.id := by
  let S := nonZeroDivisors R
  let K := Localization S
  let MK := LocalizedModule S M
  let mM : M →ₗ[R] MK := LocalizedModule.mkLinearMap S M
  let ι := Module.Free.ChooseBasisIndex K MK
  let P := ι → R
  let PK := ι → K
  let mP : P →ₗ[R] PK := LinearMap.pi fun i ↦
    (Algebra.linearMap R K) ∘ₗ LinearMap.proj i
  let e : PK ≃ₗ[K] MK := (Module.Free.chooseBasis K MK).equivFun.symm
  let eR : PK →ₗ[R] MK := e.toLinearMap.restrictScalars R
  have : Finite ι := by
    rw [← Cardinal.mk_lt_aleph0_iff, ← Module.Free.rank_eq_card_chooseBasisIndex]
    exact (Module.rank_lt_aleph0_iff (R := K) (M := MK)).mpr inferInstance
  have hmP : IsLocalizedModule S mP := by
    dsimp [mP]
    infer_instance
  have hmM : IsLocalizedModule S mM := inferInstance
  obtain ⟨a, s, ha, hsurj⟩ :=
    Module.exists_localizedMap_surjective_of_surjective S mP mM (ϕ := eR) e.surjective
  have hinj : Function.Injective (IsLocalizedModule.map S mP mM a) := by
    rw [ha]
    exact ((IsLocalizedModule.smul_injective mM s).comp e.injective)
  let e' : PK ≃ₗ[R] MK :=
    LinearEquiv.ofBijective (IsLocalizedModule.map S mP mM a) ⟨hinj, hsurj⟩
  let e'R : M →ₗ[R] PK := e'.symm.toLinearMap ∘ₗ mM
  obtain ⟨b, t, hb⟩ := finite_lift_of_isLocalizedModule_of_injective S mP e'R
    (by
      intro x y h
      funext j
      apply IsFractionRing.injective R K
      exact congr_fun h j)
  have hmP_inj : Function.Injective mP := by
    intro x y h
    funext j
    apply IsFractionRing.injective R K
    exact congr_fun h j
  have hab_loc : mM ∘ₗ (a ∘ₗ b) = mM ∘ₗ (t • LinearMap.id) := by
    ext x
    have ha_x := LinearMap.congr_fun (IsLocalizedModule.map_comp S mP mM a) (b x)
    have hb_x := LinearMap.congr_fun hb x
    simp only [LinearMap.comp_apply] at ha_x hb_x ⊢
    rw [← ha_x, hb_x]
    rw [show (IsLocalizedModule.map S mP mM) a = e'.toLinearMap from rfl,
      show e'R = e'.symm.toLinearMap ∘ₗ mM from rfl]
    simp
  obtain ⟨q, hq⟩ :=
    Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule S mM
      (a ∘ₗ b) (t • LinearMap.id) hab_loc
  let b' := q • b
  let c : nonZeroDivisors R := q * t
  have hba' : b ∘ₗ a = t • LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply hmP_inj
    have ha_x := LinearMap.congr_fun (IsLocalizedModule.map_comp S mP mM a) x
    have hb_x := LinearMap.congr_fun hb (a x)
    simp only [LinearMap.comp_apply] at ha_x hb_x ⊢
    rw [hb_x]
    rw [show e'R = e'.symm.toLinearMap ∘ₗ mM from rfl]
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← ha_x, show (IsLocalizedModule.map S mP mM) a = e'.toLinearMap from rfl]
    simp
  refine ⟨ι, ⟨Fintype.ofFinite ι⟩, a, b', c, ?_, ?_⟩
  · dsimp [b', c]
    rw [LinearMap.comp_smul, hq]
    simp [mul_smul]
  · dsimp [b', c]
    rw [LinearMap.smul_comp, hba']
    simp [mul_smul]

/-- If the evaluation map of the target is injective, a vector is killed by a linear map as soon as
its image in the double dual is killed by the double dual of the map. -/
private lemma eq_zero_of_dualMap_dualMap_eval_eq_zero
    {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N)
    (hN : Function.Injective (Module.Dual.eval R N)) {x : M}
    (hx : f.dualMap.dualMap (Module.Dual.eval R M x) = 0) : f x = 0 :=
  hN ((LinearMap.congr_fun (Module.Dual.eval_naturality f) x).symm.trans
    (hx.trans (map_zero _).symm))

/-- For a finite module over a domain the kernel and the cokernel of the evaluation map into the
reflexive hull are torsion, and the evaluation map is injective exactly when the module is
torsion-free. -/
private lemma dualEval_isTorsion_and_injective_iff
    {R : Type u} [CommRing R] [IsDomain R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.IsTorsion R (LinearMap.ker (Module.Dual.eval R M)) ∧
      Module.IsTorsion R
        (Module.Dual R (Module.Dual R M) ⧸ LinearMap.range (Module.Dual.eval R M)) ∧
      (Function.Injective (Module.Dual.eval R M) ↔ Module.IsTorsionFree R M) := by
  obtain ⟨ι, hι, a, b, c, hab, hba⟩ :=
    exists_scalar_retract (R := R) (M := M)
  have := Classical.choice hι
  let P := ι → R
  have hc : (c : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp c.prop
  have hker : ∀ x : LinearMap.ker (Module.Dual.eval R M), (c : R) • x = 0 := by
    intro x
    apply Subtype.ext
    have hx : Module.Dual.eval R M x = 0 := x.property
    have hbx : b x = 0 :=
      eq_zero_of_dualMap_dualMap_eval_eq_zero b (Module.eval_apply_injective R)
        (by rw [hx, map_zero])
    have h := LinearMap.congr_fun hab x.1
    rw [LinearMap.comp_apply, hbx, map_zero, LinearMap.smul_apply] at h
    exact h.symm
  have hcoker : ∀ x : Module.Dual R (Module.Dual R M),
      (c : R) • (Submodule.Quotient.mk x :
        Module.Dual R (Module.Dual R M) ⧸ LinearMap.range (Module.Dual.eval R M)) = 0 := by
    intro x
    obtain ⟨p, hp⟩ := (Module.bijective_dual_eval R P).2 (b.dualMap.dualMap x)
    change Submodule.Quotient.mk ((c : R) • x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨a p, ?_⟩
    calc
      Module.Dual.eval R M (a p) = a.dualMap.dualMap (Module.Dual.eval R P p) :=
        LinearMap.congr_fun (Module.Dual.eval_naturality a).symm p
      _ = a.dualMap.dualMap (b.dualMap.dualMap x) := congr_arg _ hp
      _ = (a.dualMap.dualMap.comp b.dualMap.dualMap) x := rfl
      _ = (a.comp b).dualMap.dualMap x := by
        rw [← LinearMap.dualMap_comp_dualMap, ← LinearMap.dualMap_comp_dualMap]
      _ = (c : R) • x := by
        rw [hab]
        ext f
        simp only [LinearMap.dualMap_apply', LinearMap.comp_apply, LinearMap.smul_apply,
          Submonoid.smul_def]
        rw [show f ∘ₗ ((c : R) • LinearMap.id) = (c : R) • f by ext m; simp]
        exact map_smul x (c : R) f
  refine ⟨fun {_} ↦ ⟨c, by simpa [Submonoid.smul_def] using hker _⟩, ?_, ?_⟩
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => exact ⟨c, by simpa [Submonoid.smul_def] using hcoker x⟩
  constructor
  · intro hinj
    exact Function.Injective.moduleIsTorsionFree (Module.Dual.eval R M) hinj
      (fun r m ↦ map_smul (Module.Dual.eval R M) r m)
  · intro htf x y hxy
    have := htf
    have hreg : IsRegular (c : R) := isRegular_iff_ne_zero.mpr hc
    apply (Module.IsTorsionFree.isSMulRegular hreg : IsSMulRegular M (c : R))
    rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker] at hxy
    have := congr_arg Subtype.val (hker ⟨x - y, hxy⟩)
    simpa [smul_sub, sub_eq_zero] using this

/-- **Stacks Tag 0AV0.** A reflexive module over a domain is torsion-free. For a finite module,
the kernel and cokernel of the canonical evaluation map into the double dual are torsion,
and that map is injective if and only if the module is torsion-free. -/
@[stacks 0AV0]
theorem isTorsionFree_of_isReflexive_and_dualEval_isTorsion_and_injective_iff
    {R : Type u} [CommRing R] [IsDomain R]
    {M : Type v} [AddCommGroup M] [Module R M] :
    (Module.IsReflexive R M → Module.IsTorsionFree R M) ∧
      (Module.Finite R M →
        Module.IsTorsion R (LinearMap.ker (Module.Dual.eval R M)) ∧
          Module.IsTorsion R
            (Module.Dual R (Module.Dual R M) ⧸ LinearMap.range (Module.Dual.eval R M))) ∧
      (Module.Finite R M →
        (Function.Injective (Module.Dual.eval R M) ↔ Module.IsTorsionFree R M)) :=
  ⟨fun _ ↦ inferInstance,
    fun _ ↦ ⟨(dualEval_isTorsion_and_injective_iff (R := R) (M := M)).1,
      (dualEval_isTorsion_and_injective_iff (R := R) (M := M)).2.1⟩,
    fun _ ↦ (dualEval_isTorsion_and_injective_iff (R := R) (M := M)).2.2⟩

/-! ### Reflexivity in an exact sequence -/

/-- **Stacks Tag 0EB8.** Let `R` be a Noetherian domain and let `0 → M → M' → M''` be an exact
sequence of finite `R`-modules. If `M'` is reflexive and `M''` is torsion-free, then `M` is
reflexive. -/
@[stacks 0EB8]
theorem isReflexive_of_exact_of_isReflexive_of_isTorsionFree
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {M : Type v} {M' : Type w} {M'' : Type x}
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
    (f : M →ₗ[R] M') (g : M' →ₗ[R] M'')
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hM' : Module.IsReflexive R M') (hM'' : Module.IsTorsionFree R M'') :
    Module.IsReflexive R M := by
  let eM := Module.Dual.eval R M
  let eM' := Module.Dual.eval R M'
  let eM'' := Module.Dual.eval R M''
  let ff := f.dualMap.dualMap
  let gg := g.dualMap.dualMap
  have heM'_bij : Function.Bijective eM' := by
    let _ := hM'
    exact Module.bijective_dual_eval R M'
  have heM''_inj : Function.Injective eM'' :=
    (isTorsionFree_of_isReflexive_and_dualEval_isTorsion_and_injective_iff
      (R := R) (M := M'')).2.2 inferInstance |>.2 hM''
  have hcoker : Module.IsTorsion R
      (Module.Dual R (Module.Dual R M) ⧸ LinearMap.range eM) :=
    (isTorsionFree_of_isReflexive_and_dualEval_isTorsion_and_injective_iff
      (R := R) (M := M)).2.1 inferInstance |>.2
  have hff : Function.Injective ff := by
    rw [← LinearMap.ker_eq_bot]
    ext z
    simp only [LinearMap.mem_ker, Submodule.mem_bot]
    constructor
    · intro hz
      obtain ⟨r, hr⟩ := @hcoker (Submodule.Quotient.mk z)
      have hrmem : r • z ∈ LinearMap.range eM := by
        rw [← Submodule.Quotient.mk_eq_zero]
        simpa using hr
      obtain ⟨m, hm⟩ := hrmem
      have hfm : f m = 0 := eq_zero_of_dualMap_dualMap_eval_eq_zero f heM'_bij.1 (by
        change ff (eM m) = 0
        rw [hm]
        change ff ((r : R) • z) = 0
        rw [map_smul, hz, smul_zero])
      have hm0 : m = 0 := hf (by simpa using hfm)
      rw [hm0, map_zero] at hm
      have hrz : (r : R) • z = 0 := hm.symm
      have hinj : Function.Injective
          (fun y : Module.Dual R (Module.Dual R M) ↦ (r : R) • y) :=
        Module.IsTorsionFree.isSMulRegular
          (R := R) (M := Module.Dual R (Module.Dual R M))
          (IsRegular.of_ne_zero (nonZeroDivisors.ne_zero r.property))
      exact hinj (by simpa using hrz)
    · rintro rfl
      exact map_zero ff
  refine ⟨⟨?_, ?_⟩⟩
  · intro m n hmn
    apply hf
    apply heM'_bij.1
    change ff (eM m) = ff (eM n)
    exact congrArg ff hmn
  · intro z
    obtain ⟨m', hm'⟩ := heM'_bij.2 (ff z)
    have hgm' : g m' = 0 := eq_zero_of_dualMap_dualMap_eval_eq_zero g heM''_inj (by
      change gg (eM' m') = 0
      rw [hm']
      change (f.dualMap.comp g.dualMap).dualMap z = 0
      have hgf : g.comp f = 0 := LinearMap.ext fun m ↦ hfg.apply_apply_eq_zero m
      rw [LinearMap.dualMap_comp_dualMap, hgf]
      ext φ
      simp only [LinearMap.dualMap_apply, LinearMap.zero_apply]
      rw [show (0 : M →ₗ[R] M'').dualMap φ = 0 by ext; simp, map_zero])
    obtain ⟨m, hm⟩ := (hfg m').mp hgm'
    refine ⟨m, hff ?_⟩
    change eM' (f m) = ff z
    rw [hm, hm']

/-! ### Reflexivity of finite modules, of `Hom` modules and under flat base change -/

/-- **Stacks Tag 0AV2.** A finite module over a Noetherian domain is reflexive if and only if it
fits into a short exact sequence `0 → M → F → N → 0` with `F` finite free and `N`
torsion-free. -/
@[stacks 0AV2]
theorem isReflexive_iff_exists_finFree_shortExact
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.IsReflexive R M ↔
      ∃ (n : ℕ) (N : Type u) (_ : AddCommGroup N) (_ : Module R N),
        Module.IsTorsionFree R N ∧
          ∃ (f : M →ₗ[R] (Fin n → R)) (g : (Fin n → R) →ₗ[R] N),
            Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g := by
  constructor
  · intro hM
    have : Module.IsReflexive R M := hM
    have : Module.Finite R (Module.Dual R M) := inferInstance
    obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R (Module.Dual R M)
    let b := Pi.basisFun R (Fin n)
    let e : (Fin n → R) ≃ₗ[R] Module.Dual R (Fin n → R) := b.toDualEquiv
    let d : Module.Dual R (Fin n → R) →ₗ[R] Module.Dual R p.ker := p.ker.subtype.dualMap
    let N := d.range
    let f : M →ₗ[R] (Fin n → R) :=
      e.symm.toLinearMap.comp (p.dualMap.comp (Module.Dual.eval R M))
    let g : (Fin n → R) →ₗ[R] N := d.rangeRestrict.comp e.toLinearMap
    have hdker : d.ker = p.dualMap.range := by
      rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range]
      change p.ker.subtype.range.dualAnnihilator = p.dualMap.range
      rw [p.ker.range_subtype,
        LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective p hp]
    have hf : Function.Injective f :=
      e.symm.injective.comp
        ((LinearMap.dualMap_injective_of_surjective hp).comp
          (Module.bijective_dual_eval R M).injective)
    have hfg : Function.Exact f g := by
      intro y
      constructor
      · intro hy
        have hey : e y ∈ d.ker := by
          change d (e y) = 0
          exact congrArg Subtype.val hy
        rw [hdker] at hey
        obtain ⟨z, hz⟩ := hey
        obtain ⟨x, hx⟩ := (Module.bijective_dual_eval R M).surjective z
        refine ⟨x, ?_⟩
        apply e.injective
        simp only [f, LinearMap.comp_apply]
        rw [hx, hz]
        exact e.apply_symm_apply (e y)
      · rintro ⟨x, rfl⟩
        apply Subtype.ext
        change d (e (f x)) = 0
        have hm : p.dualMap (Module.Dual.eval R M x) ∈ d.ker := by
          rw [hdker]
          exact LinearMap.mem_range_self _ _
        simpa [f] using hm
    refine ⟨n, N, inferInstance, inferInstance, inferInstance, f, g, hf, hfg, ?_⟩
    intro z
    obtain ⟨w, hw⟩ := LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict d) z
    refine ⟨e.symm w, ?_⟩
    change d.rangeRestrict (e (e.symm w)) = z
    rw [e.apply_symm_apply, hw]
  · rintro ⟨n, N, _, _, hN, f, g, hf, hfg, hg⟩
    have : Module.IsTorsionFree R N := hN
    have : Module.Finite R N := Module.Finite.of_surjective g hg
    exact isReflexive_of_exact_of_isReflexive_of_isTorsionFree
      f g hf hfg (Module.IsReflexive.of_finite_of_free R (Fin n → R)) hN

/-- Exactness is preserved when the codomain of the second map is restricted to its range. -/
private lemma exact_rangeRestrict {R M N P : Type*} [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid N] [AddCommMonoid P] [Module R M] [Module R N] [Module R P]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P} (h : Function.Exact f g) :
    Function.Exact f g.rangeRestrict := by
  rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict]
  exact LinearMap.exact_iff.mp h

/-- A finite product of copies of a reflexive module is reflexive. -/
private theorem isReflexive_fin_pi
    {R : Type u} [CommRing R] {N : Type w} [AddCommGroup N] [Module R N]
    [Module.IsReflexive R N] (n : ℕ) : Module.IsReflexive R (Fin n → N) := by
  induction n with
  | zero => infer_instance
  | succ n ih =>
      let e :=
        (LinearEquiv.piCongrLeft R (fun _ : Fin (n + 1) ↦ N) (finSuccEquiv n).symm).symm ≪≫ₗ
          LinearEquiv.piOptionEquivProd R
      exact Module.equiv e.symm

/-- **Stacks Tag 0AV3.** Over a Noetherian domain, the module of linear maps from a finite module
into a finite reflexive module is reflexive. -/
@[stacks 0AV3]
theorem isReflexive_linearMap
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {N : Type w} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (hN : Module.IsReflexive R N) :
    Module.IsReflexive R (M →ₗ[R] N) := by
  have : Module.IsReflexive R N := hN
  have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  obtain ⟨n, m, f, g, hf, hgf⟩ := Module.FinitePresentation.exists_fin' R M
  let a := LinearMap.lcomp R N g
  have hq : Function.Exact (LinearMap.lcomp R N f) a.rangeRestrict :=
    exact_rangeRestrict (LinearMap.exact_lcomp_of_exact_of_surjective N hgf hf)
  have hf' : Function.Injective (LinearMap.lcomp R N f) :=
    LinearMap.lcomp_injective_of_surjective f hf
  have hfree : Module.IsReflexive R ((Fin n → R) →ₗ[R] N) := by
    have := isReflexive_fin_pi (R := R) (N := N) n
    exact Module.equiv (linearMapFinFreeEquivPi (R := R) (N := N) n).symm
  exact isReflexive_of_exact_of_isReflexive_of_isTorsionFree
    (LinearMap.lcomp R N f) a.rangeRestrict hf' hq hfree inferInstance

/-- **Stacks Tag 0EB9.** A finite reflexive module over a Noetherian domain remains reflexive
after flat base change to a Noetherian domain. The base-changed module is automatically
finite. -/
@[stacks 0EB9]
theorem isReflexive_baseChange_of_flat
    {R : Type u} {R' : Type v} [CommRing R] [CommRing R'] [Algebra R R']
    [IsDomain R] [IsDomain R'] [IsNoetherianRing R] [IsNoetherianRing R']
    [Module.Flat R R'] {M : Type w} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.IsReflexive R M] :
    Module.IsReflexive R' (TensorProduct R R' M) := by
  obtain ⟨n, N, _, _, hN, f, g, hf, hfg, hg⟩ :=
    isReflexive_iff_exists_finFree_shortExact.mp
      (inferInstance : Module.IsReflexive R M)
  let e : TensorProduct R R' (Fin n → R) ≃ₗ[R'] (Fin n → R') :=
    Algebra.TensorProduct.equivPiOfFiniteBasis R' (Pi.basisFun R (Fin n))
  let f' : TensorProduct R R' M →ₗ[R'] (Fin n → R') :=
    e.toLinearMap.comp (f.baseChange R')
  let g' : (Fin n → R') →ₗ[R'] TensorProduct R R' N :=
    (g.baseChange R').comp e.symm.toLinearMap
  have hf_base : Function.Injective (f.baseChange R') := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap f hf
  have hf' : Function.Injective f' := e.injective.comp hf_base
  have hfg_base : Function.Exact (f.baseChange R') (g.baseChange R') := by
    simpa only [LinearMap.baseChange_eq_lTensor] using
      Module.Flat.lTensor_exact R' hfg
  have hfg' : Function.Exact f' g' := by
    apply Function.Exact.of_ladder_linearEquiv_of_exact
      (e₁ := LinearEquiv.refl R' (TensorProduct R R' M))
      (e₂ := e)
      (e₃ := LinearEquiv.refl R' (TensorProduct R R' N))
      (f₁₂ := f.baseChange R') (f₂₃ := g.baseChange R')
    · simp [f']
    · ext
      simp [g']
    · exact hfg_base
  have : Module.Finite R N := Module.Finite.of_surjective g hg
  have : Module.IsTorsionFree R' (TensorProduct R R' N) :=
    isTorsionFree_baseChange_of_flat
  exact isReflexive_of_exact_of_isReflexive_of_isTorsionFree
    f' g' hf' hfg' inferInstance inferInstance

/-! ### Surjectivity over a Dedekind domain -/

/-- **Stacks Tag 0B36.** The canonical evaluation map from a finite module over a Dedekind domain
to its double dual is surjective. -/
@[stacks 0B36]
theorem surjective_dualEval_of_finite
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Surjective (Module.Dual.eval R M) := by
  let T := Submodule.torsion R M
  let Q := M ⧸ T
  let q : M →ₗ[R] Q := T.mkQ
  have hqDual : Function.Surjective q.dualMap := dualMap_mkQ_torsion_surjective
  have : Module.Projective R Q := projective_of_finite_isTorsionFree R Q
  intro phi
  obtain ⟨x, hx⟩ := (Module.bijective_dual_eval R Q).surjective (q.dualMap.dualMap phi)
  obtain ⟨m, rfl⟩ := T.mkQ_surjective x
  refine ⟨m, q.dualMap.dualMap_injective_of_surjective hqDual ?_⟩
  have hn := LinearMap.congr_fun (Module.Dual.eval_naturality q) m
  exact hn.trans hx

/-! ### Depth and Serre's conditions for `Hom` modules and reflexive modules -/

/-- Depth is bounded below by the minimum of the depths of the two factors of a product. -/
private lemma min_depth_le_depth_prod {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (A B : Type*) [AddCommGroup A] [Module R A] [Module.Finite R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B] :
    min (Module.depth R I A) (Module.depth R I B) ≤ Module.depth R I (A × B) :=
  (Module.min_depth_le_depth_of_exact I (f := LinearMap.inl R A B)
    (g := LinearMap.snd R A B) Function.Exact.inl_snd LinearMap.inl_injective
    LinearMap.snd_surjective).1

/-- Depth does not decrease when passing to a finite product of copies of a module. -/
private lemma depth_le_depth_pi {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (A : Type*) [AddCommGroup A] [Module R A] [Module.Finite R A] (n : ℕ) :
    Module.depth R I A ≤ Module.depth R I (Fin n → A) := by
  induction n with
  | zero =>
      exact le_top.trans (Module.depth_eq_top_of_subsingleton I).ge
  | succ n ih =>
      rw [← Module.depth_eq_depth_of_linearEquiv I
        (Fin.consLinearEquiv R (fun _ : Fin (n + 1) => A))]
      exact (le_min le_rfl ih).trans (min_depth_le_depth_prod I A (Fin n → A))

/-- A submodule of a module of positive depth has positive depth. -/
private lemma one_le_depth_submodule {R A : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [AddCommGroup A] [Module R A] [Module.Finite R A] (P : Submodule R A)
    (h : (1 : ℕ∞) ≤ Module.depth R I A) :
    (1 : ℕ∞) ≤ Module.depth R I P := by
  refine le_trans (le_min h ?_) (Module.min_depth_le_depth_of_exact I
    (LinearMap.exact_subtype_mkQ P) P.injective_subtype (Submodule.mkQ_surjective P)).2.2
  exact Order.one_le_iff_ne_zero.mpr (by simp)

/-- **Stacks Tag 0AV5.** If `M` and `N` are finite modules over a Noetherian local ring, then
`Hom(M, N)` has depth at least one (respectively, at least two) whenever `N` does. -/
@[stacks 0AV5]
theorem one_le_depth_and_two_le_depth_linearMap
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {N : Type w} [AddCommGroup N] [Module R N] [Module.Finite R N] :
    ((1 : ℕ∞) ≤ Module.depth R (IsLocalRing.maximalIdeal R) N →
      (1 : ℕ∞) ≤ Module.depth R (IsLocalRing.maximalIdeal R) (M →ₗ[R] N)) ∧
    ((2 : ℕ∞) ≤ Module.depth R (IsLocalRing.maximalIdeal R) N →
      (2 : ℕ∞) ≤ Module.depth R (IsLocalRing.maximalIdeal R) (M →ₗ[R] N)) := by
  let I := IsLocalRing.maximalIdeal R
  have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  obtain ⟨n, m, f, g, hf, hgf⟩ := Module.FinitePresentation.exists_fin' R M
  let f' : (M →ₗ[R] N) →ₗ[R] ((Fin n → R) →ₗ[R] N) := LinearMap.lcomp R N f
  let g' : ((Fin n → R) →ₗ[R] N) →ₗ[R] ((Fin m → R) →ₗ[R] N) := LinearMap.lcomp R N g
  let C := LinearMap.range g'
  have hf' : Function.Injective f' := LinearMap.lcomp_injective_of_surjective f hf
  have hex : Function.Exact f' g'.rangeRestrict :=
    exact_rangeRestrict (LinearMap.exact_lcomp_of_exact_of_surjective N hgf hf)
  have hBn (k : ℕ) : Module.depth R I N ≤ Module.depth R I ((Fin k → R) →ₗ[R] N) := by
    calc
      Module.depth R I N ≤ Module.depth R I (Fin k → N) := depth_le_depth_pi I N k
      _ = Module.depth R I ((Fin k → R) →ₗ[R] N) :=
        (Module.depth_eq_depth_of_linearEquiv I (linearMapFinFreeEquivPi k)).symm
  have hC (h : (1 : ℕ∞) ≤ Module.depth R I N) :
      (1 : ℕ∞) ≤ Module.depth R I C :=
    one_le_depth_submodule I (LinearMap.range g') (h.trans (hBn m))
  have hle := (Module.min_depth_le_depth_of_exact I hex hf' g'.surjective_rangeRestrict).2.2
  constructor
  · intro h
    refine le_trans (le_min (h.trans (hBn n)) ?_) hle
    exact Order.one_le_iff_ne_zero.mpr (by simp)
  · intro h
    refine le_trans (le_min (h.trans (hBn n)) ?_) hle
    have hc : (1 : ℕ∞) ≤ Module.depth R I C := hC (le_trans (by norm_num) h)
    simpa only [show (2 : ℕ∞) = 1 + 1 by norm_num, add_comm] using add_le_add_right hc 1

/-- The zero module has depth zero in the unqualified sense. -/
private lemma moduleDepth_eq_zero_of_subsingleton {R X : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup X] [Module R X] [Subsingleton X] : moduleDepth R X = 0 := by
  apply le_antisymm
  · refine iSup₂_le fun xs hxs ↦ ?_
    exact absurd (Subsingleton.elim (⊤ : Submodule R X) (Ideal.ofList xs • ⊤))
      hxs.2.top_ne_smul
  · exact zero_le

/-- The support of a module of linear maps is contained in the support of the target. -/
public lemma support_linearMap_subset {R X Y : Type*} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [Module.Finite R Y] [Module.Finite R (X →ₗ[R] Y)] :
    Module.support R (X →ₗ[R] Y) ⊆ Module.support R Y := by
  intro p hp
  rw [Module.mem_support_iff_of_finite] at hp ⊢
  refine fun r hr ↦ hp ?_
  rw [Module.mem_annihilator]
  rw [Module.mem_annihilator] at hr
  intro f
  ext x
  exact hr (f x)

/-- The support dimension of a module of linear maps is at most that of the target. -/
private lemma moduleSupportDim_linearMap_le {R X Y : Type*} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [Module.Finite R Y] [Module.Finite R (X →ₗ[R] Y)] :
    moduleSupportDim R (X →ₗ[R] Y) ≤ moduleSupportDim R Y :=
  topologicalKrullDim_le_of_subset support_linearMap_subset

/-- The local form of Serre's condition `(S₁)` and `(S₂)` for a module of linear maps. -/
lemma propertySk_linearMap_local {R X Y : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [AddCommGroup X] [Module R X] [Module.Finite R X]
    [AddCommGroup Y] [Module R Y] [Module.Finite R Y] (k : ℕ) (hk : k = 1 ∨ k = 2)
    (hY : min (k : ℕ∞) ((moduleSupportDim R Y).unbotD 0) ≤ moduleDepth R Y) :
    min (k : ℕ∞) ((moduleSupportDim R (X →ₗ[R] Y)).unbotD 0) ≤
      moduleDepth R (X →ₗ[R] Y) := by
  let d := min (k : ℕ∞) ((moduleSupportDim R (X →ₗ[R] Y)).unbotD 0)
  by_cases hXY : Nontrivial (X →ₗ[R] Y)
  · have := hXY
    have hYnt : Nontrivial Y := not_subsingleton_iff_nontrivial.mp fun h ↦ by
      have := h
      exact (not_subsingleton_iff_nontrivial.mpr hXY) (by infer_instance)
    have := hYnt
    change d ≤ moduleDepth R (X →ₗ[R] Y)
    rw [moduleDepth_eq_depth]
    rw [moduleDepth_eq_depth] at hY
    have hdim : d ≤ min (k : ℕ∞) ((moduleSupportDim R Y).unbotD 0) :=
      min_le_min_left _ (WithBot.unbotD_mono
        (by
          rw [moduleSupportDim, Ne, topologicalKrullDim_eq_bot_iff_isEmpty]
          exact not_isEmpty_iff.mpr Module.nonempty_support_of_nontrivial.to_subtype)
        moduleSupportDim_linearMap_le)
    have hd : d ≤ Module.depth R (IsLocalRing.maximalIdeal R) Y := hdim.trans hY
    have hone (hd1 : d ≤ 1) : d ≤ Module.depth R (IsLocalRing.maximalIdeal R) (X →ₗ[R] Y) := by
      by_cases hz : d = 0
      · simp [hz]
      · have h1 : d = 1 := (Order.le_one_iff.mp hd1).resolve_left hz
        rw [h1]
        exact one_le_depth_and_two_le_depth_linearMap.1 (h1 ▸ hd)
    rcases hk with rfl | rfl
    · exact hone (min_le_left _ _)
    · by_cases h2 : (2 : ℕ∞) ≤ d
      · exact (min_le_left _ _).trans
          (one_le_depth_and_two_le_depth_linearMap.2 (h2.trans hd))
      · exact hone (ENat.lt_two_iff.mp (lt_of_not_ge h2))
  · have : Subsingleton (X →ₗ[R] Y) := not_nontrivial_iff_subsingleton.mp hXY
    rw [moduleDepth_eq_zero_of_subsingleton]
    have hs : moduleSupportDim R (X →ₗ[R] Y) = ⊥ := by
      rw [moduleSupportDim, topologicalKrullDim_eq_bot_iff_isEmpty]
      exact Set.isEmpty_coe_sort.mpr (Module.support_eq_empty_iff.mpr
        (show Subsingleton (X →ₗ[R] Y) from inferInstance))
    simp [hs]

/-- **Stacks Tag 0AV6.** For finite modules `M` and `N` over a Noetherian ring, the module
`Hom_R(M, N)` inherits `(S₁)` and `(S₂)` from `N`; if the ring is a domain, it also
inherits the conjunction of torsion-freeness and `(S₂)`. -/
@[stacks 0AV6]
theorem propertySk_linearMap_one_two_and_isTorsionFree
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {N : Type w} [AddCommGroup N] [Module R N] [Module.Finite R N] :
    (PropertySkModule R N 1 → PropertySkModule R (M →ₗ[R] N) 1) ∧
      (PropertySkModule R N 2 → PropertySkModule R (M →ₗ[R] N) 2) ∧
      (IsDomain R → Module.IsTorsionFree R N → PropertySkModule R N 2 →
        Module.IsTorsionFree R (M →ₗ[R] N) ∧ PropertySkModule R (M →ₗ[R] N) 2) := by
  have key (k : ℕ) (hk : k = 1 ∨ k = 2) (h : PropertySkModule R N k) :
      PropertySkModule R (M →ₗ[R] N) k := by
    intro p hp
    have := Module.finitePresentation_of_finite R M
    let e := (Module.FinitePresentation.linearEquivMapExtendScalars p.primeCompl
      (M := M) (N := N)).extendScalarsOfIsLocalization p.primeCompl (Localization.AtPrime p)
    rw [moduleSupportDim_eq_of_linearEquiv e, moduleDepth_eq_of_linearEquiv e]
    exact propertySk_linearMap_local k hk (h p)
  refine ⟨key 1 (Or.inl rfl), key 2 (Or.inr rfl), fun hR hN h ↦ ?_⟩
  have := hR
  have := hN
  exact ⟨inferInstance, key 2 (Or.inr rfl) h⟩

/-- **Stacks Tag 0EBA.** A finite reflexive module over a Noetherian commutative ring has depth at
least two at a prime whenever the localized ring does, and inherits Serre's condition `(S₂)`
from the ring. -/
@[stacks 0EBA]
theorem depth_localized_ge_two_and_propertyS2_of_isReflexive
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsReflexive R M] (p : Ideal R) [p.IsPrime] :
    ((2 : ℕ∞) ≤
        Module.depth (Localization.AtPrime p)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p) →
      (2 : ℕ∞) ≤
        Module.depth (Localization.AtPrime p)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p)) (LocalizedModule.AtPrime p M)) ∧
      (PropertySkRing R 2 → PropertySkModule R M 2) := by
  have hlocal : Module.IsReflexive (Localization.AtPrime p) (LocalizedModule.AtPrime p M) := by
    rw [reflexive_localized_iff_map_bijective R M p]
    exact ⟨IsLocalizedModule.map_injective _ _ _ _ (Module.bijective_dual_eval R M).1,
      IsLocalizedModule.map_surjective _ _ _ _ (Module.bijective_dual_eval R M).2⟩
  constructor
  · intro hdepth
    have := hlocal
    have hdual := (one_le_depth_and_two_le_depth_linearMap
      (R := Localization.AtPrime p)
      (M := Module.Dual (Localization.AtPrime p) (LocalizedModule.AtPrime p M))
      (N := Localization.AtPrime p)).2 hdepth
    rw [Module.depth_eq_depth_of_linearEquiv _ (Module.evalEquiv (Localization.AtPrime p)
      (LocalizedModule.AtPrime p M))]
    exact hdual
  · intro hS2
    have hdual : PropertySkModule R (Module.Dual R (Module.Dual R M)) 2 :=
      (propertySk_linearMap_one_two_and_isTorsionFree
        (R := R) (M := Module.Dual R M) (N := R)).2.1
        ((propertySkModule_self_iff_propertySkRing 2).mpr hS2)
    exact propertySkModule_of_linearEquiv (Module.evalEquiv R M) 2 hdual

/-! ### Detecting isomorphisms by local depth and associated primes -/

/-- A prime is associated to a finite module over a Noetherian ring exactly when the localization
of the module there has depth zero. -/
@[ega "IV 21.1.10" "more general"]
private lemma depth_localized_eq_zero_iff_mem_associatedPrimes
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : Ideal R) (hp : p.IsPrime) :
    Module.depth (Localization.AtPrime p)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (LocalizedModule p.primeCompl M) = 0 ↔ p ∈ associatedPrimes R M := by
  have := hp
  rw [← Order.lt_one_iff, ← not_le,
    Module.one_le_depth_iff_exists_isSMulRegular
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)),
    Ideal.exists_mem_isSMulRegular_iff_forall_associatedPrimes_not_le _ _
      (associatedPrimes.finite _ _)]
  push Not
  rw [show (∃ q ∈ associatedPrimes (Localization.AtPrime p)
          (LocalizedModule p.primeCompl M),
        IsLocalRing.maximalIdeal (Localization.AtPrime p) ≤ q) ↔
      IsLocalRing.maximalIdeal (Localization.AtPrime p) ∈
        associatedPrimes (Localization.AtPrime p) (LocalizedModule p.primeCompl M) by
      constructor
      · rintro ⟨q, hq, hqle⟩
        exact ((IsLocalRing.maximalIdeal.isMaximal _).eq_of_le hq.1.ne_top hqle) ▸ hq
      · intro hq
        exact ⟨_, hq, le_rfl⟩]
  exact maximalIdeal_mem_associatedPrimes_localized_iff p

/-- A map from a finite module is injective if, at every prime, it is bijective after localization
or the localized source has depth at least two. -/
private lemma injective_of_bijective_localized_or_depth_two
    {R M N : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N)
    (h : ∀ (p : Ideal R) (_ : p.IsPrime),
      Function.Bijective (LocalizedModule.map p.primeCompl φ) ∨
        2 ≤ Module.depth (Localization.AtPrime p)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (LocalizedModule p.primeCompl M)) :
    Function.Injective φ :=
  injective_of_injective_localized_at_associatedPrimes φ fun p hp =>
    (h p hp).imp Function.Bijective.injective fun hdepth hpM => by
      have hz := (Module.depth_localized_eq_zero_iff ⟨p, hp⟩).2 hpM
      rw [hz] at hdepth
      simp at hdepth

/-- The special case of Stacks 0AV8 in which the target is finite as well. -/
private theorem bijective_of_local_depth_of_finite_target
    {R M N : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] (φ : M →ₗ[R] N)
    (h : ∀ (p : Ideal R) (_ : p.IsPrime),
      Function.Bijective (LocalizedModule.map p.primeCompl φ) ∨
        2 ≤ Module.depth (Localization.AtPrime p)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (LocalizedModule p.primeCompl M) ∧ p ∉ associatedPrimes R N) :
    Function.Bijective φ := by
  have hinj : Function.Injective φ :=
    injective_of_bijective_localized_or_depth_two φ fun p hp => (h p hp).imp_right And.left
  refine ⟨hinj, ?_⟩
  rw [← LinearMap.range_eq_top]
  apply (Submodule.Quotient.subsingleton_iff).mp
  let Q := N ⧸ LinearMap.range φ
  suffices Subsingleton Q by exact this
  by_contra hQ
  have : Nontrivial Q := not_subsingleton_iff_nontrivial.mp hQ
  obtain ⟨p, hpQ⟩ := associatedPrimes.nonempty R Q
  have hp : p.IsPrime := hpQ.1
  let Rp := Localization.AtPrime p
  let Mp := LocalizedModule p.primeCompl M
  let Np := LocalizedModule p.primeCompl N
  let Qp := LocalizedModule p.primeCompl Q
  have hQdepth : Module.depth Rp (IsLocalRing.maximalIdeal Rp) Qp = 0 :=
    (Module.depth_localized_eq_zero_iff ⟨p, hp⟩).2 hpQ
  have hsurj := LocalizedModule.map_surjective p.primeCompl
    (Submodule.mkQ (LinearMap.range φ)) (Submodule.mkQ_surjective _)
  have hexact := LocalizedModule.map_exact p.primeCompl φ
    (Submodule.mkQ (LinearMap.range φ)) (LinearMap.exact_map_mkQ_range φ)
  rcases h p hp with hbij | hdepth
  · have : Subsingleton Qp := ⟨fun a b => by
      obtain ⟨x, rfl⟩ := hsurj a
      obtain ⟨y, rfl⟩ := hsurj b
      exact ((hexact x).2 (hbij.2 x)).trans ((hexact y).2 (hbij.2 y)).symm⟩
    have hpQp : IsLocalRing.maximalIdeal Rp ∈ associatedPrimes Rp Qp :=
      (maximalIdeal_mem_associatedPrimes_localized_iff p).mpr hpQ
    rw [associatedPrimes.eq_empty_of_subsingleton] at hpQp
    exact hpQp
  · have hNdepth : 1 ≤ Module.depth Rp (IsLocalRing.maximalIdeal Rp) Np := by
      rw [← not_lt, Order.lt_one_iff]
      exact fun hz => hdepth.2
        ((Module.depth_localized_eq_zero_iff ⟨p, hp⟩).1 hz)
    have hbound := (Module.min_depth_le_depth_of_exact (IsLocalRing.maximalIdeal Rp)
      hexact (LocalizedModule.map_injective p.primeCompl φ hinj) hsurj).2.1
    have hsub : (1 : ℕ∞) ≤
        Module.depth Rp (IsLocalRing.maximalIdeal Rp) Mp - 1 := by
      apply ENat.le_sub_of_add_le_left (by simp)
      norm_num
      exact hdepth.1
    have : (1 : ℕ∞) ≤ Module.depth Rp (IsLocalRing.maximalIdeal Rp) Qp :=
      le_trans (le_min hNdepth hsub) hbound
    simp [hQdepth] at this

/-- **Stacks Tag 0AV8.** A map from a finite module over a Noetherian ring is bijective if, at
every prime, it is bijective after localization or the localized source has depth at least two
and the prime is not associated to the target. -/
@[stacks 0AV8]
theorem bijective_of_bijective_localized_or_depth_two_and_notMem_associatedPrimes
    {R M N : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N)
    (h : ∀ (p : Ideal R) (_ : p.IsPrime),
      Function.Bijective (LocalizedModule.map p.primeCompl φ) ∨
        2 ≤ Module.depth (Localization.AtPrime p)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (LocalizedModule p.primeCompl M) ∧ p ∉ associatedPrimes R N) :
    Function.Bijective φ := by
  have hinj : Function.Injective φ :=
    injective_of_bijective_localized_or_depth_two φ fun p hp => (h p hp).imp_right And.left
  refine ⟨hinj, fun y => ?_⟩
  let P : Submodule R N := LinearMap.range φ ⊔ Submodule.span R {y}
  have hrange : (LinearMap.range φ).FG := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map φ
  have hPfg : P.FG := hrange.sup (Submodule.fg_span_singleton y)
  let ψ : M →ₗ[R] P := φ.codRestrict P fun x =>
    show φ x ∈ LinearMap.range φ ⊔ Submodule.span R {y} from
      Submodule.mem_sup_left (LinearMap.mem_range_self φ x)
  have : Module.Finite R P := Module.Finite.iff_fg.mpr hPfg
  have hbij := bijective_of_local_depth_of_finite_target ψ fun p hp => by
    rcases h p hp with hloc | hdepth
    · left
      have hsubinj := LocalizedModule.map_injective p.primeCompl P.subtype P.injective_subtype
      have hmaps : LocalizedModule.map p.primeCompl φ =
          (LocalizedModule.map p.primeCompl P.subtype).comp
            (LocalizedModule.map p.primeCompl ψ) := by
        ext z
        induction z using LocalizedModule.induction_on with
        | _ m s => simp [ψ]
      refine ⟨fun x₁ x₂ hx => hloc.1 ?_, fun z => ?_⟩
      · apply_fun LocalizedModule.map p.primeCompl P.subtype at hx
        simpa [hmaps] using hx
      · obtain ⟨x, hx⟩ := hloc.2 ((LocalizedModule.map p.primeCompl P.subtype) z)
        refine ⟨x, hsubinj ?_⟩
        simpa [hmaps] using hx
    · right
      exact ⟨hdepth.1, fun hpP => hdepth.2
        (associatedPrimes.subset_of_injective P.injective_subtype hpP)⟩
  have hyP : y ∈ P := Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)
  obtain ⟨x, hx⟩ := hbij.2 ⟨y, hyP⟩
  exact ⟨x, congr_arg Subtype.val hx⟩

/-- Over a domain, the only associated prime of a torsion-free module is the zero ideal. -/
private lemma associatedPrime_eq_bot_of_isTorsionFree
    {R N : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup N] [Module R N] [Module.IsTorsionFree R N]
    {p : Ideal R} (hp : p ∈ associatedPrimes R N) : p = ⊥ := by
  change IsAssociatedPrime p N at hp
  rw [isAssociatedPrime_iff] at hp
  obtain ⟨hprime, x, rfl⟩ := hp
  apply le_antisymm
  · intro r hr
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hr
    have hx : x ≠ 0 := by
      intro hx
      subst x
      exact hprime.ne_top (by simp)
    exact Ideal.mem_bot.mpr ((smul_eq_zero.mp hr).resolve_right hx)
  · exact bot_le

/-- At an associated prime the localization of a finite module has depth zero. -/
private lemma depth_localized_eq_zero_of_isAssociatedPrime
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : Ideal R) [p.IsPrime] (hp : IsAssociatedPrime p M) :
    Module.depth (Localization.AtPrime p)
      (IsLocalRing.maximalIdeal (Localization.AtPrime p))
      (LocalizedModule p.primeCompl M) = 0 := by
  by_contra hne
  obtain ⟨y, hymem, hyreg⟩ :=
    Module.exists_mem_isSMulRegular_of_depth_ne_zero
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)) hne
  obtain ⟨a, s, rfl⟩ : ∃ (a : R) (s : p.primeCompl),
      y = IsLocalization.mk' (Localization.AtPrime p) a s :=
    let ⟨⟨a, s⟩, hy⟩ := IsLocalization.mk'_surjective p.primeCompl y
    ⟨a, s, hy.symm⟩
  have hmap : algebraMap R (Localization.AtPrime p) a =
      algebraMap R (Localization.AtPrime p) (s : R) *
        IsLocalization.mk' (Localization.AtPrime p) a s :=
    (IsLocalization.mk'_spec' (Localization.AtPrime p) a s).symm
  have ha : a ∈ p := (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (Localization.AtPrime p) p a).mp (hmap ▸ Ideal.mul_mem_left _ _ hymem)
  have hareg : IsSMulRegular (LocalizedModule p.primeCompl M)
      (algebraMap R (Localization.AtPrime p) a) :=
    hmap ▸ (IsUnit.isSMulRegular _ (IsLocalization.map_units
      (Localization.AtPrime p) s)).mul hyreg
  obtain ⟨m, hm⟩ := hp.eq_radical_colon
  have hcol : (⊥ : Submodule R M).colon {m} ≤ p := by rw [hm]; exact Ideal.le_radical
  obtain ⟨k, hk0⟩ : ∃ k : ℕ, a ^ k ∈ (⊥ : Submodule R M).colon {m} := hm.le ha
  have hk : a ^ k • m = 0 := by simpa using Submodule.mem_colon_singleton.mp hk0
  have hzero : LocalizedModule.mk m 1 =
      (0 : LocalizedModule p.primeCompl M) := by
    refine hareg.pow k ?_
    change (algebraMap R (Localization.AtPrime p) a) ^ k • LocalizedModule.mk m 1 =
      (algebraMap R (Localization.AtPrime p) a) ^ k • 0
    rw [smul_zero]
    rw [← map_pow]
    rw [algebraMap_smul]
    change a ^ k • (LocalizedModule.mkLinearMap p.primeCompl M) m = 0
    rw [← (LocalizedModule.mkLinearMap p.primeCompl M).map_smul, hk, map_zero]
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M)).mp hzero
  exact t.2 (hcol (Submodule.mem_colon_singleton.mpr (Submodule.mem_bot R |>.mpr ht)))

/-- **Stacks Tag 0AV9.** A map from a finite nonzero module to a torsion-free module over a
Noetherian domain is bijective if, at every prime, either its localization is bijective or the
localized source has depth at least two. -/
@[stacks 0AV9]
theorem bijective_of_bijective_localized_or_depth_two_of_isTorsionFree
    {R M N : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    [AddCommGroup N] [Module R N] [Module.IsTorsionFree R N]
    (φ : M →ₗ[R] N)
    (h : ∀ (p : Ideal R) (_ : p.IsPrime),
      Function.Bijective (LocalizedModule.map p.primeCompl φ) ∨
        2 ≤ Module.depth (Localization.AtPrime p)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (LocalizedModule p.primeCompl M)) :
    Function.Bijective φ := by
  have hinj : Function.Injective φ := injective_of_bijective_localized_or_depth_two φ h
  have : Module.IsTorsionFree R M :=
    hinj.moduleIsTorsionFree φ (fun r m => φ.map_smul r m)
  apply bijective_of_bijective_localized_or_depth_two_and_notMem_associatedPrimes φ
  intro p hp
  rcases h p hp with hbij | hdepth
  · exact Or.inl hbij
  · refine Or.inr ⟨hdepth, ?_⟩
    intro hpN
    have hp0 := associatedPrime_eq_bot_of_isTorsionFree hpN
    subst p
    let ⟨m, hm⟩ := exists_ne (0 : M)
    have : Nontrivial (LocalizedModule (⊥ : Ideal R).primeCompl M) :=
      ⟨⟨LocalizedModule.mk m 1, 0, fun heq => by
        obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (⊥ : Ideal R).primeCompl
          (LocalizedModule.mkLinearMap (⊥ : Ideal R).primeCompl M)).mp heq
        exact hm ((smul_eq_zero.mp ht).resolve_left (by
          intro ht0
          exact t.2 (Ideal.mem_bot.mpr ht0)))⟩⟩
    have hzero : Module.depth (Localization.AtPrime (⊥ : Ideal R))
        (IsLocalRing.maximalIdeal (Localization.AtPrime (⊥ : Ideal R)))
        (LocalizedModule (⊥ : Ideal R).primeCompl M) = 0 := by
      rw [show IsLocalRing.maximalIdeal (Localization.AtPrime (⊥ : Ideal R)) = ⊥ by
        ext z
        obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective
          (⊥ : Ideal R).primeCompl z
        rw [IsLocalRing.mem_maximalIdeal, Ideal.mem_bot]
        constructor
        · intro hnonunit
          by_contra hne
          apply hnonunit
          rw [IsLocalization.AtPrime.isUnit_mk'_iff]
          intro ha
          apply hne
          rw [IsLocalization.mk'_eq_zero_iff]
          exact ⟨s, by rw [Ideal.mem_bot.mp ha, mul_zero]⟩
        · intro hzero
          rw [hzero]
          simp]
      exact Module.depth_bot_eq_zero (LocalizedModule (⊥ : Ideal R).primeCompl M)
    rw [hzero] at hdepth
    simp at hdepth

/-- **Stacks Tag 0AVA.** A finite module over a Noetherian domain is reflexive if and only if, at
every prime, its localization is reflexive or has depth at least two. -/
@[stacks 0AVA]
theorem isReflexive_iff_localized_isReflexive_or_depth_two
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.IsReflexive R M ↔
      ∀ (p : Ideal R) [p.IsPrime],
        Module.IsReflexive (Localization.AtPrime p) (LocalizedModule p.primeCompl M) ∨
          2 ≤ Module.depth (Localization.AtPrime p)
            (IsLocalRing.maximalIdeal (Localization.AtPrime p))
            (LocalizedModule p.primeCompl M) := by
  constructor
  · intro h p _
    left
    have hall : ∀ (q : Ideal R) [q.IsPrime],
        Module.IsReflexive (Localization.AtPrime q) (LocalizedModule q.primeCompl M) :=
      ((reflexive_tfae R M).out 1 2).mp h
    exact hall p
  · intro h
    by_cases hM : Nontrivial M
    · have := hM
      constructor
      apply bijective_of_bijective_localized_or_depth_two_of_isTorsionFree
      intro p hp
      have := hp
      exact (h p).imp_left ((reflexive_localized_iff_map_bijective R M p).mp)
    · have : Subsingleton M := not_nontrivial_iff_subsingleton.mp hM
      constructor
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

/-! ### Reflexive modules over a Noetherian normal domain -/

/-- A Noetherian normal domain satisfies Serre's condition `(S₂)`. -/
private lemma propertyS2_of_isIntegrallyClosed {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] : PropertySkRing R 2 := by
  intro p hp
  have h :=
    (isDomain_and_isIntegrallyClosed_atPrime_iff_isRegularLocalRing_and_min_two_le_depth
      (R := R)).mp (fun p _ => ⟨inferInstance,
        isIntegrallyClosed_of_isLocalization _ _ p.primeCompl_le_nonZeroDivisors⟩)
  have hdepth := h.2 p
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p] at hdepth ⊢
  change min (2 : ℕ∞) p.height ≤ moduleDepth _ _
  rw [moduleDepth_eq_depth]
  change min (↑(2 : ℕ∞) : WithBot ℕ∞) (↑p.height) ≤ _ at hdepth
  rwa [← WithBot.coe_min, WithBot.coe_le_coe] at hdepth

/-- Over a Noetherian normal domain the localization at a prime of height at most one is a
Dedekind domain. -/
private lemma isDedekindDomain_atPrime_of_height_le_one
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (p : Ideal R) [p.IsPrime] (hp : p.height ≤ 1) :
    IsDedekindDomain (Localization.AtPrime p) := by
  let A := Localization.AtPrime p
  have hdim : Ring.KrullDimLE 1 A := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height p A]
    exact_mod_cast hp
  have : Ring.DimensionLEOne A :=
    ⟨fun hne hprime => hprime.isMaximal_of_ne_bot hne⟩
  have : IsIntegrallyClosed A :=
    isIntegrallyClosed_of_isLocalization A p.primeCompl p.primeCompl_le_nonZeroDivisors
  exact { ‹IsIntegrallyClosed A› with }

/-- Over a Noetherian normal domain, the evaluation map of a finite torsion-free module becomes
bijective after localizing at a prime of height at most one. -/
private lemma localized_dualEval_bijective_of_height_le_one
    {R M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsTorsionFree R M] (p : Ideal R) [p.IsPrime] (hp : p.height ≤ 1) :
    Function.Bijective (LocalizedModule.map p.primeCompl (Module.Dual.eval R M)) := by
  have := isDedekindDomain_atPrime_of_height_le_one p hp
  have : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
    Module.free_iff_isTorsionFree.mpr inferInstance
  have h := (reflexive_localized_iff_map_bijective R M p).mp inferInstance
  exact (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective _ _).mp h

/-- Over a Noetherian normal domain a finite torsion-free `(S₂)` module is reflexive. -/
private lemma isReflexive_of_isTorsionFree_propertyS2
    {R M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsTorsionFree R M] (h : PropertySkModule R M 2) : Module.IsReflexive R M := by
  cases subsingleton_or_nontrivial M
  · infer_instance
  refine ⟨bijective_of_bijective_localized_or_depth_two_of_isTorsionFree
    (Module.Dual.eval R M) ?_⟩
  intro p hp
  by_cases hlow : p.height ≤ 1
  · exact Or.inl (localized_dualEval_bijective_of_height_le_one p hlow)
  right
  have : Nontrivial (LocalizedModule p.primeCompl M) :=
    (Module.mem_support_iff (R := R) (M := M) (p := ⟨p, hp⟩)).mp (by
    rw [Module.support_of_isTorsionFree]
    trivial)
  have hs : moduleSupportDim (Localization.AtPrime p) (LocalizedModule p.primeCompl M) =
      ringKrullDim (Localization.AtPrime p) := by
    unfold moduleSupportDim
    rw [Module.support_of_isTorsionFree]
    exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph).trans
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _)
  have hd := h p
  rw [hs, IsLocalization.AtPrime.ringKrullDim_eq_height p] at hd
  have htwo : (2 : ℕ∞) ≤ p.height := Order.add_one_le_of_lt (lt_of_not_ge hlow)
  change min (2 : ℕ∞) p.height ≤ moduleDepth _ _ at hd
  rwa [min_eq_left htwo, moduleDepth_eq_depth] at hd

/-- Surjectivity of a localized map produces, for every element of the target, a denominator
carrying it into the image. -/
private lemma exists_smul_eq_of_localized_surjective {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (S : Submonoid R) (f : M →ₗ[R] N) (h : Function.Surjective (LocalizedModule.map S f))
    (z : N) : ∃ (m : M) (s : S), (s : R) • z = f m := by
  obtain ⟨x, hx⟩ := h (LocalizedModule.mk z 1)
  induction x using LocalizedModule.induction_on with | _ m s
  rw [LocalizedModule.map_mk] at hx
  obtain ⟨t, ht⟩ := LocalizedModule.mk_eq.mp hx
  refine ⟨(t : R) • m, t * s, ?_⟩
  simpa only [Submonoid.smul_def, OneMemClass.coe_one, one_smul, map_smul,
    Submonoid.coe_mul, mul_smul] using ht.symm

/-- Over a Noetherian normal domain, divisibility may be checked at the height-one primes. -/
private lemma dvd_of_forall_height_one {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] {a b : R} (hb : b ≠ 0)
    (h : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      ∃ c t : R, t ∉ p ∧ t * a = b * c) : b ∣ a := by
  let K := FractionRing R
  have hbK : algebraMap R K b ≠ 0 := by simpa using hb
  have hz : algebraMap R K a / algebraMap R K b ∈ (⊥ : Subalgebra R K) := by
    rw [← (associatedPrimes_minimal_and_height_eq_one_and_iInf_localization_eq_bot K).2.1]
    refine Algebra.mem_iInf.mpr fun p => Algebra.mem_iInf.mpr fun hp => ?_
    obtain ⟨c, t, ht, he⟩ := h p.asIdeal hp
    refine ⟨c, t, ht, ?_⟩
    rw [← div_eq_mul_inv]
    have htK : algebraMap R K t ≠ 0 := by
      simpa using (show t ≠ 0 from fun he => ht (he ▸ p.asIdeal.zero_mem))
    apply (div_eq_div_iff hbK htK).mpr
    simpa only [map_mul, mul_comm] using congrArg (algebraMap R K) he
  obtain ⟨c, hc⟩ := Algebra.mem_bot.mp hz
  refine ⟨c, (IsFractionRing.injective R K) ?_⟩
  rw [map_mul, hc]
  exact (mul_div_cancel₀ _ hbK).symm

/-- For a reflexive module over a Noetherian normal domain, an element of the generic fibre lying
in every height-one localisation already lies in the module. -/
private lemma mem_range_of_forall_height_one_of_isReflexive
    {R M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [AddCommGroup M] [Module R M]
    [Module.IsReflexive R M]
    (x : LocalizedModule (nonZeroDivisors R) M)
    (h : ∀ (p : Ideal R) (_ : p.IsPrime), p.height = 1 →
      ∃ (m : M) (s : R), s ∉ p ∧
        s • x = LocalizedModule.mkLinearMap (nonZeroDivisors R) M m) :
    x ∈ LinearMap.range (LocalizedModule.mkLinearMap (nonZeroDivisors R) M) := by
  classical
  have : Module.IsTorsionFree R M :=
    (isTorsionFree_of_isReflexive_and_dualEval_isTorsion_and_injective_iff
      (R := R) (M := M)).1 inferInstance
  induction x using LocalizedModule.induction_on with | _ m s
  have hs : (s : R) ≠ 0 := nonZeroDivisors.ne_zero s.property
  have hdiv (φ : Module.Dual R M) : (s : R) ∣ φ m := by
    apply dvd_of_forall_height_one hs
    intro p hp hheight
    obtain ⟨n, t, ht, hn⟩ := h p hp hheight
    rw [LocalizedModule.smul'_mk, LocalizedModule.mkLinearMap_apply] at hn
    obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp hn
    have hu' : (u : R) • (t • m) = (u : R) • ((s : R) • n) := by
      simpa only [Submonoid.smul_def, OneMemClass.coe_one, one_smul] using hu
    have hm : t • m = (s : R) • n := smul_right_injective M
      (nonZeroDivisors.ne_zero u.property) hu'
    exact ⟨φ n, t, ht, by simpa only [map_smul, smul_eq_mul] using congrArg φ hm⟩
  let f : Module.Dual R M → R := fun φ => (hdiv φ).choose
  have hf (φ : Module.Dual R M) : (s : R) * f φ = φ m := (hdiv φ).choose_spec.symm
  let ψ : Module.Dual R (Module.Dual R M) :=
    { toFun := f
      map_add' := fun φ χ => mul_left_cancel₀ hs (by
        rw [mul_add, hf, hf, hf, LinearMap.add_apply])
      map_smul' := fun r φ => mul_left_cancel₀ hs (by
        change (s : R) * f (r • φ) = (s : R) * (r * f φ)
        rw [mul_left_comm, hf, hf, LinearMap.smul_apply, smul_eq_mul]) }
  obtain ⟨n, hn⟩ := Module.bijective_dual_eval R M |>.surjective ψ
  have hmn : (s : R) • n = m := Module.bijective_dual_eval R M |>.injective (by
    ext φ
    change φ ((s : R) • n) = φ m
    rw [map_smul]
    change (s : R) * (Module.Dual.eval R M n) φ = φ m
    rw [hn]
    exact hf φ)
  refine ⟨n, ?_⟩
  change LocalizedModule.mk n 1 = LocalizedModule.mk m s
  exact LocalizedModule.mk_eq.mpr ⟨1, by
    simpa only [Submonoid.smul_def, OneMemClass.coe_one, one_smul] using hmn⟩

/-- Over a Noetherian normal domain, a finite torsion-free module which is the intersection of its
height-one localisations inside its generic fibre is reflexive. -/
private lemma isReflexive_of_isTorsionFree_intersection
    {R M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsTorsionFree R M]
    (h : ∀ x : LocalizedModule (nonZeroDivisors R) M,
      x ∈ LinearMap.range (LocalizedModule.mkLinearMap (nonZeroDivisors R) M) ↔
        ∀ (p : Ideal R) (_ : p.IsPrime), p.height = 1 →
          ∃ (m : M) (s : R), s ∉ p ∧
            s • x = LocalizedModule.mkLinearMap (nonZeroDivisors R) M m) :
    Module.IsReflexive R M := by
  have hj : Function.Injective (Module.Dual.eval R M) :=
    (isTorsionFree_of_isReflexive_and_dualEval_isTorsion_and_injective_iff
      (R := R) (M := M)).2.2 inferInstance |>.mpr inferInstance
  refine ⟨hj, ?_⟩
  intro z
  have htors :=
    (isTorsionFree_of_isReflexive_and_dualEval_isTorsion_and_injective_iff
      (R := R) (M := M)).2.1 inferInstance |>.2
  obtain ⟨s, hs⟩ := htors (x := Submodule.Quotient.mk z)
  have hmem : (s : R) • z ∈ LinearMap.range (Module.Dual.eval R M) :=
    (Submodule.Quotient.mk_eq_zero _).mp hs
  obtain ⟨m, hm⟩ := hmem
  have hx : LocalizedModule.mk m s ∈
      LinearMap.range (LocalizedModule.mkLinearMap (nonZeroDivisors R) M) := by
    apply (h _).mpr
    intro p hp hheight
    obtain ⟨n, t, ht⟩ := exists_smul_eq_of_localized_surjective p.primeCompl
      (Module.Dual.eval R M)
      (localized_dualEval_bijective_of_height_le_one p hheight.le).surjective z
    refine ⟨n, t, t.property, ?_⟩
    rw [LocalizedModule.smul'_mk, LocalizedModule.mkLinearMap_apply]
    apply LocalizedModule.mk_eq.mpr
    refine ⟨1, ?_⟩
    have he : (t : R) • m = (s : R) • n := hj (by
      rw [map_smul, map_smul, hm, ← ht, smul_comm])
    simpa only [Submonoid.smul_def, OneMemClass.coe_one, one_smul] using he
  obtain ⟨n, hn⟩ := hx
  obtain ⟨t, ht⟩ := LocalizedModule.mk_eq.mp hn
  have he : (s : R) • n = m := smul_right_injective M
    (nonZeroDivisors.ne_zero t.property) (by
      simpa only [Submonoid.smul_def, OneMemClass.coe_one, one_smul] using ht)
  refine ⟨n, smul_right_injective _ (nonZeroDivisors.ne_zero s.property) ?_⟩
  change (s : R) • Module.Dual.eval R M n = (s : R) • z
  rw [← (Module.Dual.eval R M).map_smul, he, hm]

/-- **Stacks Tag 0AVB.** Let `R` be a Noetherian normal domain and `M` a finite `R`-module. The
following are equivalent: `M` is reflexive; `M` is torsion-free and satisfies `(S₂)`; and `M` is
torsion-free and equals the intersection of its localizations at the height-one primes inside
its generic fibre. -/
@[stacks 0AVB, ega "0 23.2.9" "special case", ega "IV 7.8.3" "(viii), special case"]
theorem isReflexive_isTorsionFree_propertyS2_intersection_tfae
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    List.TFAE [
      Module.IsReflexive R M,
      Module.IsTorsionFree R M ∧ PropertySkModule R M 2,
      Module.IsTorsionFree R M ∧
        ∀ x : LocalizedModule (nonZeroDivisors R) M,
          x ∈ LinearMap.range (LocalizedModule.mkLinearMap (nonZeroDivisors R) M) ↔
            ∀ (p : Ideal R) (_ : p.IsPrime), p.height = 1 →
              ∃ (m : M) (s : R), s ∉ p ∧
                s • x = LocalizedModule.mkLinearMap (nonZeroDivisors R) M m] := by
  tfae_have 1 → 2 := by
    intro h
    have := h
    exact ⟨(isTorsionFree_of_isReflexive_and_dualEval_isTorsion_and_injective_iff
      (R := R) (M := M)).1 h,
      (depth_localized_ge_two_and_propertyS2_of_isReflexive (R := R) (M := M) ⊥).2
        propertyS2_of_isIntegrallyClosed⟩
  tfae_have 2 → 1 := by
    rintro ⟨hfree, hS2⟩
    have := hfree
    exact isReflexive_of_isTorsionFree_propertyS2 hS2
  tfae_have 1 → 3 := by
    intro h
    have := h
    have ht := (isTorsionFree_of_isReflexive_and_dualEval_isTorsion_and_injective_iff
      (R := R) (M := M)).1 h
    refine ⟨ht, fun x => ⟨?_, mem_range_of_forall_height_one_of_isReflexive x⟩⟩
    rintro ⟨m, rfl⟩ p hp _
    exact ⟨m, 1, p.ne_top_iff_one.mp hp.ne_top, one_smul _ _⟩
  tfae_have 3 → 1 := by
    rintro ⟨hfree, h⟩
    have := hfree
    exact isReflexive_of_isTorsionFree_intersection h
  tfae_finish

/-- The canonical map from a module modulo its torsion submodule to its generic fibre. -/
noncomputable def Module.torsionQuotientToGenericFiber
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] :
    (M ⧸ Submodule.torsion R M) →ₗ[R] LocalizedModule (nonZeroDivisors R) M :=
  Submodule.liftQ (Submodule.torsion R M)
    (LocalizedModule.mkLinearMap (nonZeroDivisors R) M) (by
      intro m hm
      rw [LinearMap.mem_ker, IsLocalizedModule.eq_zero_iff (nonZeroDivisors R)
        (LocalizedModule.mkLinearMap (nonZeroDivisors R) M)]
      exact (Submodule.mem_torsion_iff m).mp hm)

/-- The map to the generic fibre is computed on representatives by the localization map. -/
@[simp]
theorem Module.torsionQuotientToGenericFiber_mk
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (m : M) :
    Module.torsionQuotientToGenericFiber R M (Submodule.Quotient.mk m) =
      LocalizedModule.mkLinearMap (nonZeroDivisors R) M m :=
  rfl

/-- A split injection with torsion cokernel into a torsion-free module is surjective. -/
private theorem surjective_of_leftInverse_of_isTorsion_coker
    {R : Type u} [CommRing R] [IsDomain R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N] [Module.IsTorsionFree R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] M) (hgf : g.comp f = LinearMap.id)
    (ht : Module.IsTorsion R (N ⧸ LinearMap.range f)) : Function.Surjective f := by
  intro y
  obtain ⟨s, hs⟩ := ht (x := Submodule.Quotient.mk y)
  have hsy : (s : R) • y ∈ LinearMap.range f := by
    rw [← Submodule.Quotient.mk_eq_zero]
    exact hs
  obtain ⟨m, hm⟩ := hsy
  refine ⟨g y, ?_⟩
  apply (smul_right_injective (M := N) (nonZeroDivisors.ne_zero s.property))
  calc
    (s : R) • f (g y) = f (g ((s : R) • y)) := by simp
    _ = f (g (f m)) := by rw [hm]
    _ = f m := congrArg f (LinearMap.congr_fun hgf m)
    _ = (s : R) • y := hm

/-- Over a domain, a dual module with finite dual is reflexive. -/
private theorem isReflexive_dual
    {R : Type u} [CommRing R] [IsDomain R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R (Module.Dual R M)] :
    Module.IsReflexive R (Module.Dual R M) := by
  let e := Module.Dual.eval R (Module.Dual R M)
  let r := (Module.Dual.eval R M).dualMap
  have hre : r.comp e = LinearMap.id := by ext; rfl
  refine ⟨⟨?_, ?_⟩⟩
  · exact LinearMap.injective_of_comp_eq_id e r hre
  · apply surjective_of_leftInverse_of_isTorsion_coker e r hre
    exact (isTorsionFree_of_isReflexive_and_dualEval_isTorsion_and_injective_iff
      (R := R) (M := Module.Dual R M)).2.1 inferInstance |>.2

/-- Over a Noetherian normal domain the localization at a prime of height at most one is a
principal ideal domain. -/
theorem isPrincipalIdealRing_atPrime_of_height_le_one
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (p : Ideal R) [p.IsPrime] (hp : p.height ≤ 1) :
    IsPrincipalIdealRing (Localization.AtPrime p) := by
  have := isDedekindDomain_atPrime_of_height_le_one p hp
  infer_instance

/-- At a prime of height at most one, every element of the reflexive hull of a finite module is
represented, up to a denominator outside the prime, by an element of the module. -/
theorem exists_smul_eq_dualEval_of_height_le_one
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : Ideal R) [p.IsPrime] (hp : p.height ≤ 1)
    (d : Module.Dual R (Module.Dual R M)) :
    ∃ (m : M) (s : R), s ∉ p ∧ s • d = Module.Dual.eval R M m := by
  let Q := M ⧸ Submodule.torsion R M
  let q : M →ₗ[R] Q := (Submodule.torsion R M).mkQ
  let S := p.primeCompl
  let A := Localization.AtPrime p
  have : IsPrincipalIdealRing A := isPrincipalIdealRing_atPrime_of_height_le_one p hp
  have : Module.Free A (LocalizedModule S Q) := Module.free_of_finite_type_torsion_free'
  have hlocal : Module.IsReflexive A (LocalizedModule S Q) := inferInstance
  let e := IsLocalizedModule.map S (LocalizedModule.mkLinearMap S Q)
    (LocalizedModule.mkLinearMap S (Module.Dual R (Module.Dual R Q))) (Module.Dual.eval R Q)
  have he : Function.Surjective e :=
    ((reflexive_localized_iff_map_bijective R Q p).mp hlocal).2
  obtain ⟨z, hz⟩ := he (LocalizedModule.mkLinearMap S _ (q.dualMap.dualMap d))
  obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj S (LocalizedModule.mkLinearMap S Q) z
  have hsm : LocalizedModule.mkLinearMap S _ ((s : R) • q.dualMap.dualMap d) =
      LocalizedModule.mkLinearMap S _ (Module.Dual.eval R Q m) := by
    rw [map_smul, ← hz, ← e.map_smul]
    change e (s • z) = _
    rw [hs]
    exact IsLocalizedModule.map_apply S _ _ _ m
  obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := S) hsm
  obtain ⟨m, rfl⟩ := (Submodule.torsion R M).mkQ_surjective m
  refine ⟨(t : R) • m, (t : R) * (s : R), (t * s).property, ?_⟩
  apply LinearMap.dualMap_injective_of_surjective
    (dualMap_mkQ_torsion_surjective (R := R) (M := M))
  change (t : R) • (s : R) • q.dualMap.dualMap d =
    (t : R) • q.dualMap.dualMap (Module.Dual.eval R M m) at ht
  simpa only [map_smul, mul_smul] using ht

/-- A map with torsion kernel stays injective after localizing at the nonzero divisors. -/
private theorem map_injective_of_isTorsion_ker
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (ht : Module.IsTorsion R (LinearMap.ker f)) :
    Function.Injective (IsLocalizedModule.map (nonZeroDivisors R)
      (LocalizedModule.mkLinearMap (nonZeroDivisors R) M)
      (LocalizedModule.mkLinearMap (nonZeroDivisors R) N) f) := by
  let S := nonZeroDivisors R
  let i := LocalizedModule.mkLinearMap S M
  let j := LocalizedModule.mkLinearMap S N
  let e := IsLocalizedModule.map S i j f
  change Function.Injective e
  rw [← LinearMap.ker_eq_bot]
  apply eq_bot_iff.mpr
  intro z hz
  change e z = 0 at hz
  change z = 0
  obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj S i z
  have hfm : j (f m) = 0 := by
    rw [← IsLocalizedModule.map_apply S i j f m, ← hs]
    change e ((s : R) • z) = 0
    rw [map_smul, hz, smul_zero]
  obtain ⟨t, htm⟩ := (IsLocalizedModule.eq_zero_iff S j).mp hfm
  have hmker : (t : R) • m ∈ LinearMap.ker f := by
    simpa only [LinearMap.mem_ker, map_smul, Submonoid.smul_def] using htm
  obtain ⟨uu, hu⟩ := ht (x := ⟨(t : R) • m, hmker⟩)
  have hum : (uu : R) • (t : R) • m = 0 := congrArg Subtype.val hu
  apply IsLocalizedModule.smul_injective i (uu * t * s)
  change ((uu : R) * (t : R) * (s : R)) • z = _
  rw [mul_smul, mul_smul]
  change (uu : R) • (t : R) • (s • z) = _
  rw [hs, ← map_smul, ← map_smul, hum, map_zero]
  simp

/-- **Stacks Tag 0AVC.** Let `R` be a Noetherian normal domain and `M` a finite `R`-module. Inside
the generic fibre, the reflexive hull `M⁎⁎` is the intersection over height-one primes `p` of
`M_p / (M_p)_tors`, and this is also the intersection of `(M / M_tors)_p`.

Membership in the three submodules is written elementwise, with the first condition using the
canonical localization of the evaluation map `M → M⁎⁎`. -/
@[stacks 0AVC, ega "0 23.2.9" "special case"]
theorem reflexiveHull_eq_iInf_localization_mod_torsion
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∀ x : LocalizedModule (nonZeroDivisors R) M,
      (((IsLocalizedModule.map (nonZeroDivisors R)
          (LocalizedModule.mkLinearMap (nonZeroDivisors R) M)
          (LocalizedModule.mkLinearMap (nonZeroDivisors R)
            (Module.Dual R (Module.Dual R M)))
          (Module.Dual.eval R M)) x ∈
            LinearMap.range (LocalizedModule.mkLinearMap (nonZeroDivisors R)
              (Module.Dual R (Module.Dual R M)))) ↔
        ∀ (p : Ideal R) (_ : p.IsPrime), p.height = 1 →
          ∃ (m : M) (s : R), s ∉ p ∧
            s • x = LocalizedModule.mkLinearMap (nonZeroDivisors R) M m) ∧
      ((∀ (p : Ideal R) (_ : p.IsPrime), p.height = 1 →
          ∃ (m : M) (s : R), s ∉ p ∧
            s • x = LocalizedModule.mkLinearMap (nonZeroDivisors R) M m) ↔
        ∀ (p : Ideal R) (_ : p.IsPrime), p.height = 1 →
          ∃ (q : M ⧸ Submodule.torsion R M) (s : R), s ∉ p ∧
            s • x = Module.torsionQuotientToGenericFiber R M q) := by
  intro x
  let S := nonZeroDivisors R
  let D := Module.Dual R (Module.Dual R M)
  let i := LocalizedModule.mkLinearMap S M
  let j := LocalizedModule.mkLinearMap S D
  let e := IsLocalizedModule.map S i j (Module.Dual.eval R M)
  have he : Function.Injective e := map_injective_of_isTorsion_ker _
    ((isTorsionFree_of_isReflexive_and_dualEval_isTorsion_and_injective_iff
      (R := R) (M := M)).2.1 inferInstance).1
  constructor
  · constructor
    · rintro ⟨d, hd⟩ p hp hheight
      obtain ⟨m, s, hs, hsm⟩ := exists_smul_eq_dualEval_of_height_le_one (M := M) p hheight.le d
      refine ⟨m, s, hs, he ?_⟩
      change e (s • x) = e (i m)
      rw [map_smul, ← hd, ← map_smul, hsm, IsLocalizedModule.map_apply]
    · intro hx
      have : Module.IsReflexive R (Module.Dual R M) := isReflexive_dual
      have : Module.IsReflexive R D := inferInstance
      have hD := ((isReflexive_isTorsionFree_propertyS2_intersection_tfae
        (R := R) (M := D)).out 1 3).mp ‹Module.IsReflexive R D›
      apply (hD.2 (e x)).mpr
      intro p hp hheight
      obtain ⟨m, s, hs, hsm⟩ := hx p hp hheight
      refine ⟨Module.Dual.eval R M m, s, hs, ?_⟩
      change s • e x = j (Module.Dual.eval R M m)
      rw [← map_smul, hsm, IsLocalizedModule.map_apply]
  · constructor
    · intro hx p hp hheight
      obtain ⟨m, s, hs, hsm⟩ := hx p hp hheight
      exact ⟨Submodule.Quotient.mk m, s, hs, hsm⟩
    · intro hx p hp hheight
      obtain ⟨q, s, hs, hsq⟩ := hx p hp hheight
      obtain ⟨m, rfl⟩ := (Submodule.torsion R M).mkQ_surjective q
      exact ⟨m, s, hs, hsq⟩

/-- **Stacks Tag 0BM4.** If `A` is a Noetherian normal domain, `K` is its fraction field, and `L`
is a finite extension of `K`, then a module-finite integral closure of `A` in `L` is reflexive as
an `A`-module. -/
@[stacks 0BM4]
theorem integralClosure_isReflexive
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] (hB : Module.Finite A (integralClosure A L)) :
    Module.IsReflexive A (integralClosure A L) := by
  let B := integralClosure A L
  let S := nonZeroDivisors A
  let f : B →ₗ[A] L := (Algebra.linearMap B L).restrictScalars A
  have : Module.Finite A B := hB
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have : Module.IsTorsionFree A L := Module.IsTorsionFree.trans_faithfulSMul A K L
  have : IsLocalization (Algebra.algebraMapSubmonoid B S) L :=
    IsIntegralClosure.isLocalization A K L B
  have : IsLocalizedModule S f := IsLocalizedModule.restrictScalars S (Algebra.linearMap B L)
  have hchar := isReflexive_isTorsionFree_propertyS2_intersection_tfae (R := A) (M := B)
  apply (hchar.out 3 1).mp
  refine ⟨IsIntegralClosure.isTorsionFree A L, fun x ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨b, rfl⟩ p hp hp1
    exact ⟨b, 1, (Ideal.ne_top_iff_one p).mp hp.ne_top, by simp⟩
  · intro hx
    let e : LocalizedModule S B ≃ₗ[A] L := IsLocalizedModule.iso S f
    let y : L := e x
    have hy_coeff : ∀ i, (minpoly K y).coeff i ∈ (algebraMap A K).range := by
      intro i
      have hinter : (⨅ p : PrimeSpectrum A, ⨅ _ : p.asIdeal.height = 1,
          Localization.subalgebra.ofField K p.asIdeal.primeCompl
            p.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥ :=
        (associatedPrimes_minimal_and_height_eq_one_and_iInf_localization_eq_bot K).2.1
      apply Algebra.mem_bot.mp
      rw [← hinter, Algebra.mem_iInf]
      intro p
      rw [Algebra.mem_iInf]
      intro hp1
      obtain ⟨b, s, hs, hsx⟩ := hx p.asIdeal p.isPrime hp1
      have hse : (s : A) • y = algebraMap B L b := by
        change (s : A) • e x = f b
        rw [← e.map_smul, hsx]
        exact IsLocalizedModule.iso_mk_one S f b
      have hs0 : (s : A) ≠ 0 := fun h ↦ hs (h ▸ p.asIdeal.zero_mem)
      have hsk0 : algebraMap A K (s : A) ≠ 0 := by simpa using hs0
      have hscale : minpoly K (algebraMap B L b) =
          (minpoly K y).scaleRoots (algebraMap A K s) := by
        rw [← hse]
        convert IsIntegrallyClosed.minpoly_smul hsk0
          (Algebra.IsIntegral.isIntegral y) using 1
        simp [Algebra.smul_def, IsScalarTower.algebraMap_apply A K L]
      have hbint : IsIntegral A (algebraMap B L b) :=
        (IsIntegralClosure.isIntegral A L b).algebraMap
      have hbcoeff : (minpoly K (algebraMap B L b)).coeff i ∈
          (algebraMap A K).range := by
        refine ⟨(minpoly A (algebraMap B L b)).coeff i, ?_⟩
        have hpoly := congrArg (fun q : Polynomial K ↦ q.coeff i)
          (minpoly.isIntegrallyClosed_eq_field_fractions K L hbint)
        simpa using hpoly.symm
      obtain ⟨a, ha⟩ := hbcoeff
      have hcoeff : algebraMap A K a =
          (minpoly K y).coeff i * (algebraMap A K s) ^
            ((minpoly K y).natDegree - i) := by
        rw [ha, hscale, Polynomial.coeff_scaleRoots]
      unfold Localization.subalgebra.ofField
      refine ⟨a, s ^ ((minpoly K y).natDegree - i), ?_, ?_⟩
      · exact fun h ↦ hs (p.isPrime.mem_of_pow_mem _ h)
      · rw [map_pow, hcoeff]
        field_simp
    have hy : IsIntegral A y := by
      have hlifts : minpoly K y ∈ Polynomial.lifts (algebraMap A K) :=
        (Polynomial.lifts_iff_coeff_lifts _).2 hy_coeff
      obtain ⟨q, hq, -, hqmonic⟩ :=
        Polynomial.lifts_and_natDegree_eq_and_monic hlifts
          (minpoly.monic (Algebra.IsIntegral.isIntegral y))
      refine ⟨q, hqmonic, ?_⟩
      calc
        Polynomial.eval₂ (algebraMap A L) y q =
            Polynomial.eval₂ ((algebraMap K L).comp (algebraMap A K)) y q := by
              congr 1
              ext a
              exact IsScalarTower.algebraMap_apply A K L a
        _ = Polynomial.eval₂ (algebraMap K L) y
            (Polynomial.map (algebraMap A K) q) :=
              (Polynomial.eval₂_map (algebraMap A K) (algebraMap K L) y).symm
        _ = Polynomial.eval₂ (algebraMap K L) y (minpoly K y) := by rw [hq]
        _ = 0 := minpoly.aeval K y
    obtain ⟨b, hb⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp hy
    refine ⟨b, e.injective ?_⟩
    change e ((LocalizedModule.mkLinearMap S B) b) = e x
    rw [show (LocalizedModule.mkLinearMap S B) b = LocalizedModule.mk b (1 : S) by rfl,
      IsLocalizedModule.iso_apply_mk]
    simpa [y, f] using hb

/-! ### A reflexive `(S₂)` module over a ring which is not `(S₂)`

The subalgebra of `k[x, y]` generated by `1`, `y`, `x²`, `xy` and `x³` is a Noetherian domain
which does not satisfy Serre's condition `(S₂)`, while the ambient polynomial ring is a finite
reflexive `(S₂)` module over it. -/

open scoped Pointwise

set_option synthInstance.maxHeartbeats 400000 in
-- Instances for the subalgebra `k[1, y, x², xy, x³]` and for its ideals unfold through
-- several coercion layers, which exhausts the default instance-search budget.
/-- The subalgebra `k[1, y, x², xy, x³]` of `k[x, y]` is Noetherian. -/
private theorem adjoin_isNoetherianRing (k : Type u) [Field k] :
    IsNoetherianRing
      (Algebra.adjoin k
        ({1, MvPolynomial.X 1, MvPolynomial.X 0 ^ 2,
          MvPolynomial.X 0 * MvPolynomial.X 1, MvPolynomial.X 0 ^ 3} :
          Set (MvPolynomial (Fin 2) k))) := by
  classical
  let s : Finset (MvPolynomial (Fin 2) k) :=
    {1, MvPolynomial.X 1, MvPolynomial.X 0 ^ 2,
      MvPolynomial.X 0 * MvPolynomial.X 1, MvPolynomial.X 0 ^ 3}
  have hs : (s : Set (MvPolynomial (Fin 2) k)) =
      {1, MvPolynomial.X 1, MvPolynomial.X 0 ^ 2,
        MvPolynomial.X 0 * MvPolynomial.X 1, MvPolynomial.X 0 ^ 3} := by
    ext q
    simp [s]
  rw [← hs]
  exact isNoetherianRing_of_fg (Subalgebra.fg_adjoin_finset s)

set_option synthInstance.maxHeartbeats 400000 in
-- Instances for the subalgebra `k[1, y, x², xy, x³]` and for its ideals unfold through
-- several coercion layers, which exhausts the default instance-search budget.
/-- The polynomial ring `k[x, y]` is a finite module over the subalgebra
`k[1, y, x², xy, x³]`. -/
private theorem adjoin_polynomial_finite (k : Type u) [Field k] :
    Module.Finite
      (Algebra.adjoin k
        ({1, MvPolynomial.X 1, MvPolynomial.X 0 ^ 2,
          MvPolynomial.X 0 * MvPolynomial.X 1, MvPolynomial.X 0 ^ 3} :
          Set (MvPolynomial (Fin 2) k)))
      (MvPolynomial (Fin 2) k) := by
  let P := MvPolynomial (Fin 2) k
  let x : P := MvPolynomial.X 0
  let y : P := MvPolynomial.X 1
  let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
  change Module.Finite R P
  have hx2 : x ^ 2 ∈ R := Algebra.subset_adjoin (by simp)
  have hy : y ∈ R := Algebra.subset_adjoin (by simp)
  have hxi : IsIntegral R x := by
    apply IsIntegral.of_pow (by decide : 0 < 2)
    simpa only [Subalgebra.algebraMap_apply] using
      (isIntegral_algebraMap (A := P) (x := (⟨x ^ 2, hx2⟩ : R)))
  have hyi : IsIntegral R y := by
    simpa only [Subalgebra.algebraMap_apply] using
      (isIntegral_algebraMap (A := P) (x := (⟨y, hy⟩ : R)))
  have hfin : Algebra.FiniteType R P :=
    Algebra.FiniteType.of_restrictScalars_finiteType k R P
  apply Algebra.finite_iff_isIntegral_and_finiteType.mpr
  constructor
  · apply Algebra.isIntegral_def.mpr
    intro q
    induction q using MvPolynomial.induction_on with
    | C a =>
        have hca : (MvPolynomial.C a : P) ∈ R := Subalgebra.algebraMap_mem R a
        simpa only [Subalgebra.algebraMap_apply] using
          (isIntegral_algebraMap (A := P) (x :=
            (⟨MvPolynomial.C a, hca⟩ : R)))
    | add q₁ q₂ h₁ h₂ => exact h₁.add h₂
    | mul_X q i hq =>
        have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
        rcases hi with rfl | rfl
        · exact hq.mul hxi
        · exact hq.mul hyi
  · exact hfin

set_option synthInstance.maxHeartbeats 400000 in
-- Instances for the subalgebra `k[1, y, x², xy, x³]` and for its ideals unfold through
-- several coercion layers, which exhausts the default instance-search budget.
/-- The polynomial ring is spanned over the subalgebra by `1` and `x`. -/
private theorem adjoin_polynomial_span (k : Type u) [Field k] :
    let P := MvPolynomial (Fin 2) k
    let x : P := MvPolynomial.X 0
    let y : P := MvPolynomial.X 1
    let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
    Submodule.span R ({1, x} : Set P) = ⊤ := by
  classical
  let P := MvPolynomial (Fin 2) k
  let x : P := MvPolynomial.X 0
  let y : P := MvPolynomial.X 1
  let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
  let S : Submodule R P := Submodule.span R {1, x}
  change S = ⊤
  have hx2 : x ^ 2 ∈ R := Algebra.subset_adjoin (by simp)
  have hy : y ∈ R := Algebra.subset_adjoin (by simp)
  have hmulx (q : P) (hq : q ∈ S) : q * x ∈ S := by
    obtain ⟨a, b, hab⟩ := (Submodule.mem_span_pair).mp hq
    apply (Submodule.mem_span_pair).mpr
    refine ⟨b * ⟨x ^ 2, hx2⟩, a, ?_⟩
    have hab' : (a : P) + (b : P) * x = q := by
      simpa only [Algebra.smul_def, Subalgebra.algebraMap_apply, mul_one] using hab
    simp only [Algebra.smul_def, Subalgebra.algebraMap_apply,
      Subalgebra.coe_mul, mul_one]
    rw [← hab']
    ring
  have hmuly (q : P) (hq : q ∈ S) : q * y ∈ S := by
    convert S.smul_mem ⟨y, hy⟩ hq using 1
    change q * y = y * q
    ring
  suffices h : ∀ q : P, q ∈ S by
    exact top_unique fun q _ => h q
  intro q
  induction q using MvPolynomial.induction_on with
  | C a =>
      apply (Submodule.mem_span_pair).mpr
      refine ⟨⟨MvPolynomial.C a, R.algebraMap_mem a⟩, 0, ?_⟩
      simp [Algebra.smul_def]
  | add q₁ q₂ h₁ h₂ => exact S.add_mem h₁ h₂
  | mul_X q i hq =>
      fin_cases i
      · exact hmulx q hq
      · exact hmuly q hq

set_option synthInstance.maxHeartbeats 400000 in
-- Instances for the subalgebra `k[1, y, x², xy, x³]` and for its ideals unfold through
-- several coercion layers, which exhausts the default instance-search budget.
/-- An `R`-linear functional on the polynomial ring is multiplication by its value at `1`.
The relation `x² · x = x³ · 1` forces the same relation on its values. -/
private theorem dual_adjoin_polynomial_mul_apply (k : Type u) [Field k] :
    let P := MvPolynomial (Fin 2) k
    let x : P := MvPolynomial.X 0
    let y : P := MvPolynomial.X 1
    let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
    ∀ (f : Module.Dual R P) (q : P), (↑(f q) : P) = (↑(f 1) : P) * q := by
  classical
  let P := MvPolynomial (Fin 2) k
  let x : P := MvPolynomial.X 0
  let y : P := MvPolynomial.X 1
  let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
  change ∀ (f : Module.Dual R P) (q : P), (↑(f q) : P) = (↑(f 1) : P) * q
  have hx2 : x ^ 2 ∈ R := Algebra.subset_adjoin (by simp)
  have hx3 : x ^ 3 ∈ R := Algebra.subset_adjoin (by simp)
  have hxne : x ^ 2 ≠ (0 : P) := pow_ne_zero _ (MvPolynomial.X_ne_zero (0 : Fin 2))
  intro f q
  have hrel : (⟨x ^ 2, hx2⟩ : R) • f x = (⟨x ^ 3, hx3⟩ : R) • f (1 : P) := by
    calc
      _ = f ((⟨x ^ 2, hx2⟩ : R) • x) := (map_smul f _ _).symm
      _ = f ((⟨x ^ 3, hx3⟩ : R) • (1 : P)) := by
        congr 1
        simp only [Algebra.smul_def, Subalgebra.algebraMap_apply, mul_one]
        ring
      _ = _ := map_smul f _ _
  have hrel' : x ^ 2 * (↑(f x) : P) = x ^ 3 * (↑(f 1) : P) := by
    change (⟨x ^ 2, hx2⟩ : R) * f x = (⟨x ^ 3, hx3⟩ : R) * f 1 at hrel
    simpa only [Subalgebra.coe_mul] using congrArg (fun r : R => (r : P)) hrel
  have hfx : (↑(f x) : P) = (↑(f 1) : P) * x := by
    apply mul_left_cancel₀ hxne
    calc
      x ^ 2 * (↑(f x) : P) = x ^ 3 * (↑(f 1) : P) := hrel'
      _ = x ^ 2 * ((↑(f 1) : P) * x) := by ring
  have hq : q ∈ Submodule.span R ({1, x} : Set P) := by
    rw [adjoin_polynomial_span k]
    trivial
  obtain ⟨a, b, hab⟩ := (Submodule.mem_span_pair).mp hq
  have hab' : (a : P) + (b : P) * x = q := by
    simpa only [Algebra.smul_def, Subalgebra.algebraMap_apply, mul_one] using hab
  have hfq : (f q : P) = (a : P) * (f 1 : P) + (b : P) * (f x : P) := by
    calc
      (f q : P) = (f (a • (1 : P) + b • x) : P) := by rw [hab]
      _ = (a : P) * (f 1 : P) + (b : P) * (f x : P) := by
        rw [map_add, map_smul, map_smul]
        simp
  calc
    (f q : P) = (a : P) * (f 1 : P) + (b : P) * (f x : P) := hfq
    _ = (f 1 : P) * q := by rw [← hab', hfx]; ring

set_option synthInstance.maxHeartbeats 400000 in
-- Instances for the subalgebra `k[1, y, x², xy, x³]` and for its ideals unfold through
-- several coercion layers, which exhausts the default instance-search budget.
/-- Every element of the subalgebra has vanishing `x`-derivative at the origin. -/
private theorem pderiv_constantCoeff_eq_zero_of_mem_adjoin (k : Type u) [Field k] :
    let P := MvPolynomial (Fin 2) k
    let x : P := MvPolynomial.X 0
    let y : P := MvPolynomial.X 1
    let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
    ∀ q : P, q ∈ R → MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 q) = 0 := by
  let P := MvPolynomial (Fin 2) k
  let x : P := MvPolynomial.X 0
  let y : P := MvPolynomial.X 1
  let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
  change ∀ q : P, q ∈ R → MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 q) = 0
  intro q hq
  apply Algebra.adjoin_induction (p := fun r _ =>
    MvPolynomial.constantCoeff (MvPolynomial.pderiv 0 r) = 0) _ _ _ _ hq
  · intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    all_goals simp [x, y]
  · intro a
    simp
  · intro a b _ _ hda hdb
    simp [map_add, hda, hdb]
  · intro a b _ _ hda hdb
    simp [map_add, map_mul, hda, hdb]

set_option synthInstance.maxHeartbeats 400000 in
-- Instances for the subalgebra `k[1, y, x², xy, x³]` and for its ideals unfold through
-- several coercion layers, which exhausts the default instance-search budget.
/-- Every element of the subalgebra differs from its constant coefficient by an element of the
ideal generated by `y`, `x²`, `xy` and `x³`. -/
private theorem sub_constantCoeff_mem_adjoinMaxIdeal (k : Type u) [Field k] :
    let P := MvPolynomial (Fin 2) k
    let x : P := MvPolynomial.X 0
    let y : P := MvPolynomial.X 1
    let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
    let m : Ideal R := Ideal.span {r | (r : P) ∈ ({y, x ^ 2, x * y, x ^ 3} : Set P)}
    ∀ (r : R), r - algebraMap k R (MvPolynomial.constantCoeff (r : P)) ∈ m := by
  classical
  let P := MvPolynomial (Fin 2) k
  let x : P := MvPolynomial.X 0
  let y : P := MvPolynomial.X 1
  let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
  let m : Ideal R := Ideal.span {r | (r : P) ∈ ({y, x ^ 2, x * y, x ^ 3} : Set P)}
  change ∀ (r : R), r - algebraMap k R (MvPolynomial.constantCoeff (r : P)) ∈ m
  intro r
  have hpre : ∀ (q : P) (hq : q ∈ R),
      (⟨q, hq⟩ : R) - algebraMap k R (MvPolynomial.constantCoeff q) ∈ m := by
    intro q hq
    apply Algebra.adjoin_induction (p := fun t ht =>
      (⟨t, ht⟩ : R) - algebraMap k R (MvPolynomial.constantCoeff t) ∈ m)
      _ _ _ _ hq
    · intro t ht
      have ht' : t = 1 ∨ t ∈ ({y, x ^ 2, x * y, x ^ 3} : Set P) := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ht
      rcases ht' with rfl | ht'
      · change (1 : R) - algebraMap k R (MvPolynomial.constantCoeff (1 : P)) ∈ m
        simp
      · have hc : MvPolynomial.constantCoeff t = 0 := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht'
          rcases ht' with rfl | rfl | rfl | rfl
          all_goals simp [x, y]
        rw [hc, map_zero, sub_zero]
        exact Ideal.subset_span ht'
    · intro a
      change algebraMap k R a -
        algebraMap k R (MvPolynomial.constantCoeff (MvPolynomial.C a)) ∈ m
      rw [MvPolynomial.constantCoeff_C, sub_self]
      exact m.zero_mem
    · intro a b ha hb hda hdb
      have heq :
          (⟨a + b, R.add_mem ha hb⟩ : R) -
              algebraMap k R (MvPolynomial.constantCoeff (a + b)) =
            ((⟨a, ha⟩ : R) - algebraMap k R (MvPolynomial.constantCoeff a)) +
              ((⟨b, hb⟩ : R) - algebraMap k R (MvPolynomial.constantCoeff b)) := by
        change (⟨a, ha⟩ : R) + (⟨b, hb⟩ : R) -
          algebraMap k R (MvPolynomial.constantCoeff (a + b)) =
          ((⟨a, ha⟩ : R) - algebraMap k R (MvPolynomial.constantCoeff a)) +
          ((⟨b, hb⟩ : R) - algebraMap k R (MvPolynomial.constantCoeff b))
        simp only [map_add]
        abel
      rw [heq]
      exact m.add_mem hda hdb
    · intro a b ha hb hda hdb
      have heq :
          (⟨a * b, R.mul_mem ha hb⟩ : R) -
              algebraMap k R (MvPolynomial.constantCoeff (a * b)) =
            ((⟨a, ha⟩ : R) - algebraMap k R (MvPolynomial.constantCoeff a)) *
                (⟨b, hb⟩ : R) +
              algebraMap k R (MvPolynomial.constantCoeff a) *
                ((⟨b, hb⟩ : R) - algebraMap k R (MvPolynomial.constantCoeff b)) := by
        change (⟨a, ha⟩ : R) * (⟨b, hb⟩ : R) -
          algebraMap k R (MvPolynomial.constantCoeff (a * b)) = _
        simp only [map_mul]
        ring
      rw [heq]
      exact m.add_mem (m.mul_mem_right _ hda) (m.mul_mem_left _ hdb)
  exact hpre r r.property

set_option synthInstance.maxHeartbeats 400000 in
-- Instances for the subalgebra `k[1, y, x², xy, x³]` and for its ideals unfold through
-- several coercion layers, which exhausts the default instance-search budget.
/-- The ideal generated by `y`, `x²`, `xy` and `x³` consists of the elements of the subalgebra
with vanishing constant coefficient. -/
private theorem mem_adjoinMaxIdeal_iff_constantCoeff_eq_zero (k : Type u) [Field k] :
    let P := MvPolynomial (Fin 2) k
    let x : P := MvPolynomial.X 0
    let y : P := MvPolynomial.X 1
    let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
    let m : Ideal R := Ideal.span {r | (r : P) ∈ ({y, x ^ 2, x * y, x ^ 3} : Set P)}
    ∀ r : R, r ∈ m ↔ MvPolynomial.constantCoeff (r : P) = 0 := by
  let P := MvPolynomial (Fin 2) k
  let x : P := MvPolynomial.X 0
  let y : P := MvPolynomial.X 1
  let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
  let m : Ideal R := Ideal.span {r | (r : P) ∈ ({y, x ^ 2, x * y, x ^ 3} : Set P)}
  change ∀ r : R, r ∈ m ↔ MvPolynomial.constantCoeff (r : P) = 0
  let ε : R →+* k := MvPolynomial.constantCoeff.comp R.subtype
  have hmker : m ≤ RingHom.ker ε := by
    apply Ideal.span_le.mpr
    intro r hr
    change MvPolynomial.constantCoeff (r : P) = 0
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with h | h | h | h
    all_goals (rw [h]; simp [x, y])
  intro r
  constructor
  · intro hr
    exact hmker hr
  · intro hr
    have hs := sub_constantCoeff_mem_adjoinMaxIdeal k r
    rw [hr, map_zero, sub_zero] at hs
    exact hs

set_option synthInstance.maxHeartbeats 400000 in
-- Instances for the subalgebra `k[1, y, x², xy, x³]` and for its ideals unfold through
-- several coercion layers, which exhausts the default instance-search budget.
/-- An element of the subalgebra is carried into it by multiplication by `x` exactly when it lies
in the ideal generated by `y`, `x²`, `xy` and `x³`. -/
private theorem mul_x_mem_adjoin_iff_mem_adjoinMaxIdeal (k : Type u) [Field k] :
    let P := MvPolynomial (Fin 2) k
    let x : P := MvPolynomial.X 0
    let y : P := MvPolynomial.X 1
    let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
    let m : Ideal R := Ideal.span {r | (r : P) ∈ ({y, x ^ 2, x * y, x ^ 3} : Set P)}
    ∀ r : R, (r : P) * x ∈ R ↔ r ∈ m := by
  classical
  let P := MvPolynomial (Fin 2) k
  let x : P := MvPolynomial.X 0
  let y : P := MvPolynomial.X 1
  let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
  let m : Ideal R := Ideal.span {r | (r : P) ∈ ({y, x ^ 2, x * y, x ^ 3} : Set P)}
  change ∀ r : R, (r : P) * x ∈ R ↔ r ∈ m
  have hy : y ∈ R := Algebra.subset_adjoin (by simp)
  have hx2 : x ^ 2 ∈ R := Algebra.subset_adjoin (by simp)
  have hxy : x * y ∈ R := Algebra.subset_adjoin (by simp)
  have hx3 : x ^ 3 ∈ R := Algebra.subset_adjoin (by simp)
  intro r
  constructor
  · intro hr
    apply (mem_adjoinMaxIdeal_iff_constantCoeff_eq_zero k r).2
    have hd := pderiv_constantCoeff_eq_zero_of_mem_adjoin k ((r : P) * x) hr
    simpa [MvPolynomial.pderiv_mul, x] using hd
  · intro hr
    induction hr using Submodule.span_induction with
    | mem a ha =>
        simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with h | h | h | h
        · rw [h]
          rw [mul_comm y x]
          exact hxy
        · rw [h]
          simpa only [← pow_succ] using hx3
        · rw [h]
          convert R.mul_mem hx2 hy using 1
          ring
        · rw [h]
          convert R.mul_mem hx2 hx2 using 1
          ring
    | zero => simp
    | add a b _ _ iha ihb =>
        simpa only [Subalgebra.coe_add, add_mul] using R.add_mem iha ihb
    | smul c a _ iha =>
        have h : ((c • a : R) : P) * x = (c : P) * ((a : P) * x) := by
          simp [mul_assoc]
        rw [h]
        exact R.mul_mem c.property iha

set_option synthInstance.maxHeartbeats 400000 in
-- Instances for the subalgebra `k[1, y, x², xy, x³]` and for its ideals unfold through
-- several coercion layers, which exhausts the default instance-search budget.
/-- Multiplication by an element of the ideal generated by `y`, `x²`, `xy` and `x³` carries the
whole polynomial ring into the subalgebra. -/
private theorem mul_mem_adjoin_of_mem_adjoinMaxIdeal (k : Type u) [Field k] :
    let P := MvPolynomial (Fin 2) k
    let x : P := MvPolynomial.X 0
    let y : P := MvPolynomial.X 1
    let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
    let m : Ideal R := Ideal.span {r | (r : P) ∈ ({y, x ^ 2, x * y, x ^ 3} : Set P)}
    ∀ (a : m) (q : P), (↑(↑a : R) : P) * q ∈ R := by
  classical
  let P := MvPolynomial (Fin 2) k
  let x : P := MvPolynomial.X 0
  let y : P := MvPolynomial.X 1
  let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
  let m : Ideal R := Ideal.span {r | (r : P) ∈ ({y, x ^ 2, x * y, x ^ 3} : Set P)}
  change ∀ (a : m) (q : P), (↑(↑a : R) : P) * q ∈ R
  intro a q
  have hax : (↑(↑a : R) : P) * x ∈ R :=
    (mul_x_mem_adjoin_iff_mem_adjoinMaxIdeal k (a : R)).2 a.property
  have hq : q ∈ Submodule.span R ({1, x} : Set P) := by
    rw [adjoin_polynomial_span k]
    trivial
  obtain ⟨b, c, hbc⟩ := (Submodule.mem_span_pair).mp hq
  have hbc' : (b : P) + (c : P) * x = q := by
    simpa only [Algebra.smul_def, Subalgebra.algebraMap_apply, mul_one] using hbc
  rw [← hbc']
  have hab : (↑(↑a : R) : P) * (b : P) ∈ R := R.mul_mem a.1.property b.property
  have hac : (↑(↑a : R) : P) * ((c : P) * x) ∈ R := by
    convert R.mul_mem c.property hax using 1
    ring
  convert R.add_mem hab hac using 1
  ring

set_option synthInstance.maxHeartbeats 400000 in
-- Instances for the subalgebra `k[1, y, x², xy, x³]` and for its ideals unfold through
-- several coercion layers, which exhausts the default instance-search budget.
/-- The `R`-dual of `k[x, y]` is the ideal generated by `y`, `x²`, `xy` and `x³`. -/
private noncomputable def dualPolynomialEquivAdjoinMaxIdeal (k : Type u) [Field k] :
    let P := MvPolynomial (Fin 2) k
    let x : P := MvPolynomial.X 0
    let y : P := MvPolynomial.X 1
    let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
    let m : Ideal R := Ideal.span {r | (r : P) ∈ ({y, x ^ 2, x * y, x ^ 3} : Set P)}
    Module.Dual R P ≃ₗ[R] m := by
  classical
  let P := MvPolynomial (Fin 2) k
  let x : P := MvPolynomial.X 0
  let y : P := MvPolynomial.X 1
  let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
  let m : Ideal R := Ideal.span {r | (r : P) ∈ ({y, x ^ 2, x * y, x ^ 3} : Set P)}
  change Module.Dual R P ≃ₗ[R] m
  let φ : Module.Dual R P →ₗ[R] m :=
    { toFun := fun f => ⟨f 1, by
          apply (mul_x_mem_adjoin_iff_mem_adjoinMaxIdeal k (f 1)).1
          have hf := dual_adjoin_polynomial_mul_apply k f x
          rw [← hf]
          exact (f x).property⟩
      map_add' := by
        intro f g
        apply Subtype.ext
        simp
      map_smul' := by
        intro r f
        apply Subtype.ext
        simp }
  apply LinearEquiv.ofBijective φ
  constructor
  · intro f g hfg
    have h1 : f 1 = g 1 := congrArg Subtype.val hfg
    apply LinearMap.ext
    intro q
    apply Subtype.ext
    change (f q : P) = (g q : P)
    rw [dual_adjoin_polynomial_mul_apply k f q, dual_adjoin_polynomial_mul_apply k g q, h1]
  · intro a
    let f : Module.Dual R P :=
      { toFun := fun q => ⟨(↑(↑a : R) : P) * q,
            mul_mem_adjoin_of_mem_adjoinMaxIdeal k a q⟩
        map_add' := by
          intro q₁ q₂
          apply Subtype.ext
          simp [mul_add]
        map_smul' := by
          intro r q
          apply Subtype.ext
          simp only [Algebra.smul_def, Subalgebra.algebraMap_apply,
            Subalgebra.coe_mul, Algebra.algebraMap_self, RingHom.id_apply]
          ring }
    refine ⟨f, ?_⟩
    apply Subtype.ext
    simp [φ, f]

set_option synthInstance.maxHeartbeats 400000 in
-- Instances for the subalgebra `k[1, y, x², xy, x³]` and for its ideals unfold through
-- several coercion layers, which exhausts the default instance-search budget.
set_option maxHeartbeats 1000000 in
-- Building this dual identification by hand elaborates large subtype terms.
/-- The `R`-dual of the ideal generated by `y`, `x²`, `xy` and `x³` is `k[x, y]`. -/
private noncomputable def dualAdjoinMaxIdealEquivPolynomial (k : Type u) [Field k] :
    let P := MvPolynomial (Fin 2) k
    let x : P := MvPolynomial.X 0
    let y : P := MvPolynomial.X 1
    let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
    let m : Ideal R := Ideal.span {r | (r : P) ∈ ({y, x ^ 2, x * y, x ^ 3} : Set P)}
    Module.Dual R m ≃ₗ[R] P := by
  classical
  let P := MvPolynomial (Fin 2) k
  let x : P := MvPolynomial.X 0
  let y : P := MvPolynomial.X 1
  let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
  let m : Ideal R := Ideal.span {r | (r : P) ∈ ({y, x ^ 2, x * y, x ^ 3} : Set P)}
  change Module.Dual R m ≃ₗ[R] P
  let ψ : P →ₗ[R] Module.Dual R m :=
    { toFun := fun q =>
        { toFun := fun a => ⟨q * (↑(↑a : R) : P), by
              convert mul_mem_adjoin_of_mem_adjoinMaxIdeal k a q using 1
              ring⟩
          map_add' := by
            intro a b
            apply Subtype.ext
            simp [mul_add]
          map_smul' := by
            intro r a
            apply Subtype.ext
            change q * ((r : P) * (↑(↑a : R) : P)) =
              (r : P) * (q * (↑(↑a : R) : P))
            ring }
      map_add' := by
        intro q₁ q₂
        apply LinearMap.ext
        intro a
        apply Subtype.ext
        simp [add_mul]
      map_smul' := by
        intro r q
        apply LinearMap.ext
        intro a
        apply Subtype.ext
        change ((r : P) * q) * (↑(↑a : R) : P) =
          (r : P) * (q * (↑(↑a : R) : P))
        ring }
  apply (LinearEquiv.ofBijective ψ ?_).symm
  constructor
  · intro q₁ q₂ hq
    have hy : y ∈ R := Algebra.subset_adjoin (by simp)
    have hym : (⟨y, hy⟩ : R) ∈ m := Ideal.subset_span (by simp)
    let ym : m := ⟨⟨y, hy⟩, hym⟩
    have h := congrArg (fun f : Module.Dual R m => (f ym : P)) hq
    have hyne : y ≠ (0 : P) := MvPolynomial.X_ne_zero (1 : Fin 2)
    exact mul_right_cancel₀ hyne h
  · intro g
    have hy : y ∈ R := Algebra.subset_adjoin (by simp)
    have hx2 : x ^ 2 ∈ R := Algebra.subset_adjoin (by simp)
    have hym : (⟨y, hy⟩ : R) ∈ m := Ideal.subset_span (by simp)
    have hx2m : (⟨x ^ 2, hx2⟩ : R) ∈ m := Ideal.subset_span (by simp)
    let ym : m := ⟨⟨y, hy⟩, hym⟩
    let x2m : m := ⟨⟨x ^ 2, hx2⟩, hx2m⟩
    have hrel (a b : m) :
        (↑(↑a : R) : P) * (g b : P) = (↑(↑b : R) : P) * (g a : P) := by
      have h : (a : R) * g b = (b : R) * g a := by
        calc
          _ = g ((a : R) • b) := (map_smul g _ _).symm
          _ = g ((b : R) • a) := by
            congr 1
            apply Subtype.ext
            change (a : R) * (b : R) = (b : R) * (a : R)
            ring
          _ = _ := map_smul g _ _
      simpa only [Subalgebra.coe_mul] using congrArg (fun r : R => (r : P)) h
    have hyprime : Prime y := MvPolynomial.X_prime
    have hyx : ¬ y ∣ x := by
      intro hd
      exact (by decide : (1 : Fin 2) ≠ 0) ((MvPolynomial.X_dvd_X).mp hd)
    have hyx2 : ¬ y ∣ x ^ 2 := fun hd => hyx (hyprime.dvd_of_dvd_pow hd)
    have hdiv : y ∣ x ^ 2 * (g ym : P) := by
      rw [← hrel ym x2m]
      exact dvd_mul_right y _
    have hy_g : y ∣ (g ym : P) := (hyprime.dvd_or_dvd hdiv).resolve_left hyx2
    obtain ⟨q, hq⟩ := hy_g
    have hg (a : m) : (g a : P) = q * (↑(↑a : R) : P) := by
      have hyne : y ≠ (0 : P) := MvPolynomial.X_ne_zero (1 : Fin 2)
      apply mul_left_cancel₀ hyne
      calc
        y * (g a : P) = (↑(↑a : R) : P) * (g ym : P) := (hrel a ym).symm
        _ = (↑(↑a : R) : P) * (y * q) := by rw [hq]
        _ = y * (q * (↑(↑a : R) : P)) := by ring
    refine ⟨q, ?_⟩
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    exact (hg a).symm

set_option synthInstance.maxHeartbeats 400000 in
-- Instances for the subalgebra `k[1, y, x², xy, x³]` and for its ideals unfold through
-- several coercion layers, which exhausts the default instance-search budget.
/-- The first dual identification sends a functional to its multiplication coefficient. -/
private theorem dualPolynomialEquivAdjoinMaxIdeal_mul_apply (k : Type u) [Field k] :
    let P := MvPolynomial (Fin 2) k
    let x : P := MvPolynomial.X 0
    let y : P := MvPolynomial.X 1
    let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
    ∀ (f : Module.Dual R P) (q : P),
      (↑(↑(dualPolynomialEquivAdjoinMaxIdeal k f) : R) : P) * q = (↑(f q) : P) := by
  intro P x y R f q
  change (↑(f 1) : P) * q = (↑(f q) : P)
  exact (dual_adjoin_polynomial_mul_apply k f q).symm

set_option synthInstance.maxHeartbeats 400000 in
-- Instances for the subalgebra `k[1, y, x², xy, x³]` and for its ideals unfold through
-- several coercion layers, which exhausts the default instance-search budget.
/-- The inverse of the second dual identification is multiplication on the conductor. -/
private theorem dualAdjoinMaxIdealEquivPolynomial_symm_apply (k : Type u) [Field k] :
    let P := MvPolynomial (Fin 2) k
    let x : P := MvPolynomial.X 0
    let y : P := MvPolynomial.X 1
    let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
    let m : Ideal R := Ideal.span {r | (r : P) ∈ ({y, x ^ 2, x * y, x ^ 3} : Set P)}
    ∀ (q : P) (a : m),
      (↑((dualAdjoinMaxIdealEquivPolynomial k).symm q a) : P) = q * (↑(↑a : R) : P) := by
  intro P x y R _m q a
  rfl

set_option synthInstance.maxHeartbeats 400000 in
-- Instances for the subalgebra `k[1, y, x², xy, x³]` and for its ideals unfold through
-- several coercion layers, which exhausts the default instance-search budget.
/-- The polynomial ring is a reflexive module over the subalgebra. -/
private theorem adjoin_polynomial_isReflexive (k : Type u) [Field k] :
    let P := MvPolynomial (Fin 2) k
    let x : P := MvPolynomial.X 0
    let y : P := MvPolynomial.X 1
    let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
    Module.IsReflexive R P := by
  classical
  let P := MvPolynomial (Fin 2) k
  let x : P := MvPolynomial.X 0
  let y : P := MvPolynomial.X 1
  let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
  let m : Ideal R := Ideal.span {r | (r : P) ∈ ({y, x ^ 2, x * y, x ^ 3} : Set P)}
  change Module.IsReflexive R P
  let e₁ : Module.Dual R P ≃ₗ[R] m := dualPolynomialEquivAdjoinMaxIdeal k
  let e₂ : Module.Dual R m ≃ₗ[R] P := dualAdjoinMaxIdealEquivPolynomial k
  have h₁ (f : Module.Dual R P) (q : P) :
      (↑(↑(e₁ f) : R) : P) * q = (↑(f q) : P) :=
    dualPolynomialEquivAdjoinMaxIdeal_mul_apply k f q
  have h₂ (q : P) (a : m) :
      (↑((e₂.symm q) a) : P) = q * (↑(↑a : R) : P) :=
    dualAdjoinMaxIdealEquivPolynomial_symm_apply k q a
  have heval : Module.Dual.eval R P =
      e₁.dualMap.toLinearMap.comp e₂.symm.toLinearMap := by
    apply LinearMap.ext
    intro q
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change (↑(f q) : P) = (↑((e₂.symm q) (e₁ f)) : P)
    rw [h₂, ← h₁ f q]
    ring
  exact ⟨by
    rw [heval]
    exact e₁.dualMap.bijective.comp e₂.symm.bijective⟩

set_option synthInstance.maxHeartbeats 400000 in
-- Instances for the subalgebra `k[1, y, x², xy, x³]` and for its ideals unfold through
-- several coercion layers, which exhausts the default instance-search budget.
/-- The ideal generated by `y`, `x²`, `xy` and `x³` is a maximal ideal of the subalgebra. -/
private theorem adjoinMaxIdeal_isMaximal (k : Type u) [Field k] :
    let P := MvPolynomial (Fin 2) k
    let x : P := MvPolynomial.X 0
    let y : P := MvPolynomial.X 1
    let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
    let m : Ideal R := Ideal.span {r | (r : P) ∈ ({y, x ^ 2, x * y, x ^ 3} : Set P)}
    m.IsMaximal := by
  let P := MvPolynomial (Fin 2) k
  let x : P := MvPolynomial.X 0
  let y : P := MvPolynomial.X 1
  let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
  let m : Ideal R := Ideal.span {r | (r : P) ∈ ({y, x ^ 2, x * y, x ^ 3} : Set P)}
  let ε : R →+* k := MvPolynomial.constantCoeff.comp R.subtype
  have hε : Function.Surjective ε := by
    intro a
    refine ⟨algebraMap k R a, ?_⟩
    change MvPolynomial.constantCoeff (MvPolynomial.C a) = a
    simp
  have hm : m = RingHom.ker ε := by
    ext r
    exact mem_adjoinMaxIdeal_iff_constantCoeff_eq_zero k r
  change m.IsMaximal
  rw [hm]
  exact RingHom.ker_isMaximal_of_surjective ε hε

set_option synthInstance.maxHeartbeats 400000 in
-- Instances for the subalgebra `k[1, y, x², xy, x³]` and for its ideals unfold through
-- several coercion layers, which exhausts the default instance-search budget.
/-- The origin has a nonzero prime strictly below it. -/
private theorem exists_prime_between_zero_and_adjoinMaxIdeal (k : Type u) [Field k] :
    let P := MvPolynomial (Fin 2) k
    let x : P := MvPolynomial.X 0
    let y : P := MvPolynomial.X 1
    let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
    let m : Ideal R := Ideal.span {r | (r : P) ∈ ({y, x ^ 2, x * y, x ^ 3} : Set P)}
    ∃ q : Ideal R, q.IsPrime ∧ (⊥ : Ideal R) < q ∧ q < m := by
  classical
  let P := MvPolynomial (Fin 2) k
  let x : P := MvPolynomial.X 0
  let y : P := MvPolynomial.X 1
  let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
  let m : Ideal R := Ideal.span {r | (r : P) ∈ ({y, x ^ 2, x * y, x ^ 3} : Set P)}
  let q : Ideal R := Ideal.comap R.subtype (Ideal.span {x})
  have : (Ideal.span ({x} : Set P)).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime MvPolynomial.X_prime
  have hq : q.IsPrime :=
    Ideal.comap_isPrime R.subtype (Ideal.span {x})
  have hx2 : x ^ 2 ∈ R := Algebra.subset_adjoin (by simp)
  have hy : y ∈ R := Algebra.subset_adjoin (by simp)
  have hx2q : (⟨x ^ 2, hx2⟩ : R) ∈ q := by
    change x ^ 2 ∈ Ideal.span ({x} : Set P)
    rw [Ideal.mem_span_singleton]
    exact ⟨x, by ring⟩
  have hqne : q ≠ ⊥ := by
    intro he
    have heq : (⟨x ^ 2, hx2⟩ : R) = 0 := by
      rw [he] at hx2q
      simpa using hx2q
    have : x ^ 2 = (0 : P) := congrArg (fun r : R => (r : P)) heq
    exact pow_ne_zero _ (MvPolynomial.X_ne_zero (0 : Fin 2)) this
  have hqle : q ≤ m := by
    intro r hr
    apply (mem_adjoinMaxIdeal_iff_constantCoeff_eq_zero k r).2
    change (r : P) ∈ Ideal.span ({x} : Set P) at hr
    rw [Ideal.mem_span_singleton] at hr
    obtain ⟨t, ht⟩ := hr
    rw [ht]
    simp [x]
  have hy_m : (⟨y, hy⟩ : R) ∈ m := Ideal.subset_span (by simp)
  have hy_not_q : (⟨y, hy⟩ : R) ∉ q := by
    change y ∉ Ideal.span ({x} : Set P)
    rw [Ideal.mem_span_singleton]
    intro hd
    exact (by decide : (0 : Fin 2) ≠ 1) ((MvPolynomial.X_dvd_X).mp hd)
  refine ⟨q, hq, bot_lt_iff_ne_bot.mpr hqne, lt_of_le_of_ne hqle ?_⟩
  intro he
  exact hy_not_q (he ▸ hy_m)

set_option synthInstance.maxHeartbeats 400000 in
-- Instances for the subalgebra `k[1, y, x², xy, x³]` and for its ideals unfold through
-- several coercion layers, which exhausts the default instance-search budget.
/-- The maximal ideal at the origin has height at least two. -/
private theorem adjoinMaxIdeal_height_ge_two (k : Type u) [Field k] :
    let P := MvPolynomial (Fin 2) k
    let x : P := MvPolynomial.X 0
    let y : P := MvPolynomial.X 1
    let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
    let m : Ideal R := Ideal.span {r | (r : P) ∈ ({y, x ^ 2, x * y, x ^ 3} : Set P)}
    (2 : ℕ∞) ≤ m.height := by
  let P := MvPolynomial (Fin 2) k
  let x : P := MvPolynomial.X 0
  let y : P := MvPolynomial.X 1
  let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
  let m : Ideal R := Ideal.span {r | (r : P) ∈ ({y, x ^ 2, x * y, x ^ 3} : Set P)}
  change (2 : ℕ∞) ≤ m.height
  obtain ⟨q, hq, h0q, hqm⟩ := exists_prime_between_zero_and_adjoinMaxIdeal k
  have : q.IsPrime := hq
  have : m.IsPrime := (adjoinMaxIdeal_isMaximal k).isPrime
  have h₁ := Ideal.height_add_one_le_of_lt_of_isPrime h0q
  have h₂ := Ideal.height_add_one_le_of_lt_of_isPrime hqm
  simpa using
    (show (2 : ℕ∞) ≤ m.height from
      calc
        (2 : ℕ∞) = (⊥ : Ideal R).height + 1 + 1 := by norm_num
        _ ≤ q.height + 1 := by
          simpa [add_comm, add_left_comm, add_assoc] using (add_le_add_right h₁ 1)
        _ ≤ m.height := h₂)

/-- A local domain admitting an element of a strictly larger domain whose conductor contains the
maximal ideal has depth at most one. -/
private lemma moduleDepth_le_one_of_conductor {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsDomain B] (f : A →+* B)
    (hf : Function.Injective f) (z : B) (hz : z ∉ Set.range f)
    (hcon : ∀ a ∈ IsLocalRing.maximalIdeal A, f a * z ∈ Set.range f) :
    moduleDepth A A ≤ 1 := by
  apply iSup₂_le
  intro rs hrs
  rcases rs with _ | ⟨a, rs⟩
  · simp
  rcases rs with _ | ⟨b, rs⟩
  · simp
  exfalso
  obtain ⟨ha, hr⟩ := (RingTheory.Sequence.isRegular_cons_iff A a (b :: rs)).mp hrs.2
  have hb := ((RingTheory.Sequence.isRegular_cons_iff (QuotSMulTop a A) b rs).mp hr).1
  obtain ⟨az, haz⟩ := hcon a (hrs.1 a (by simp))
  obtain ⟨bz, hbz⟩ := hcon b (hrs.1 b (by simp))
  have hrel : b * az = a * bz := hf (by rw [map_mul, map_mul, haz, hbz]; ring)
  have hazmem : az ∈ a • (⊤ : Submodule A A) :=
    mem_of_isSMulRegular_quotient_of_smul_mem hb (by
      rw [Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨bz, trivial, hrel.symm⟩)
  obtain ⟨c, _, hc⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hazmem
  have hane : f a ≠ 0 := by
    intro hzero
    have ha0 : a = 0 := hf (by simpa using hzero)
    have : (1 : A) = 0 := ha (by simp [ha0])
    exact one_ne_zero this
  apply hz
  refine ⟨c, mul_left_cancel₀ hane ?_⟩
  rw [← map_mul, show a * c = az from hc, haz]

/-- The localization of a domain at a prime has depth at most one when a fixed element of a
larger domain has conductor exactly that prime. -/
private lemma moduleDepth_localization_le_one_of_conductor {R B : Type*}
    [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
    (i : R →+* B) (hi : Function.Injective i) (p : Ideal R) [p.IsPrime]
    (z : B) (hz : ∀ s ∉ p, i s * z ∉ Set.range i)
    (hcon : ∀ a ∈ p, i a * z ∈ Set.range i) :
    moduleDepth (Localization.AtPrime p) (Localization.AtPrime p) ≤ 1 := by
  let A := Localization.AtPrime p
  let K := FractionRing B
  let j : R →+* K := (algebraMap B K).comp i
  have hj : Function.Injective j := (IsFractionRing.injective B K).comp hi
  have hj0 {s : R} (hs : s ∉ p) : j s ≠ 0 := by
    intro he
    exact hs (hj (he.trans (map_zero j).symm) ▸ p.zero_mem)
  have hu : ∀ s : p.primeCompl, IsUnit (j s) := fun s => isUnit_iff_ne_zero.mpr (hj0 s.2)
  let f : A →+* K := IsLocalization.lift hu
  have hf : Function.Injective f := by
    apply IsLocalization.injective_of_map_algebraMap_zero (M := p.primeCompl) A f
    intro a ha
    change (IsLocalization.lift hu) ((algebraMap R A) a) = 0 at ha
    rw [IsLocalization.lift_eq hu] at ha
    rw [hj (ha.trans (map_zero j).symm), map_zero]
  have hspec (a : R) (s : p.primeCompl) :
      f (IsLocalization.mk' A a s) * j s = j a := by
    have h := congrArg f (IsLocalization.mk'_spec A a s)
    simpa only [map_mul, f, IsLocalization.lift_eq hu] using h
  apply moduleDepth_le_one_of_conductor f hf (algebraMap B K z)
  · rintro ⟨a, ha⟩
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl a
    have hr : i s * z = i r := IsFractionRing.injective B K (by
      rw [map_mul]
      change j s * algebraMap B K z = j r
      rw [← ha, mul_comm]
      exact hspec r s)
    exact hz s s.2 ⟨r, hr.symm⟩
  · intro a ha
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl a
    have hr : r ∈ p := (IsLocalization.AtPrime.mk'_mem_maximal_iff A p r s).mp ha
    obtain ⟨b, hb⟩ := hcon r hr
    refine ⟨IsLocalization.mk' A b s, ?_⟩
    apply mul_right_cancel₀ (hj0 s.2)
    rw [hspec b s]
    calc
      j b = j r * algebraMap B K z := by
        change algebraMap B K (i b) = algebraMap B K (i r) * algebraMap B K z
        rw [hb, map_mul]
      _ = f (IsLocalization.mk' A r s) * algebraMap B K z * j s := by
        rw [← hspec r s]
        ring

set_option synthInstance.maxHeartbeats 400000 in
-- Instances for the subalgebra `k[1, y, x², xy, x³]` and for its ideals unfold through
-- several coercion layers, which exhausts the default instance-search budget.
/-- The subalgebra `k[1, y, x², xy, x³]` does not satisfy Serre's condition `(S₂)`. -/
private theorem adjoin_not_propertySkRing (k : Type u) [Field k] :
    let P := MvPolynomial (Fin 2) k
    let x : P := MvPolynomial.X 0
    let y : P := MvPolynomial.X 1
    let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
    letI := adjoin_isNoetherianRing k
    ¬ PropertySkRing R 2 := by
  intro P x y R
  have := adjoin_isNoetherianRing k
  let m : Ideal R := Ideal.span {r | (r : P) ∈ ({y, x ^ 2, x * y, x ^ 3} : Set P)}
  have : m.IsPrime := (adjoinMaxIdeal_isMaximal k).isPrime
  have hdep : moduleDepth (Localization.AtPrime m) (Localization.AtPrime m) ≤ 1 := by
    apply moduleDepth_localization_le_one_of_conductor R.subtype Subtype.val_injective m x
    · intro s hs ⟨r, hr⟩
      exact hs ((mul_x_mem_adjoin_iff_mem_adjoinMaxIdeal k s).mp (hr ▸ r.property))
    · intro a ha
      exact ⟨⟨(a : P) * x, (mul_x_mem_adjoin_iff_mem_adjoinMaxIdeal k a).mpr ha⟩, rfl⟩
  intro h
  have hm := h m
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m),
    WithBot.unbotD_coe] at hm
  have hheight : (2 : ℕ∞) ≤ m.height := adjoinMaxIdeal_height_ge_two k
  norm_num only [Nat.cast_ofNat] at hm
  rw [min_eq_left hheight] at hm
  exact (by decide : ¬ (2 : ℕ∞) ≤ 1) (hm.trans hdep)

/-- A Noetherian normal local domain satisfies the local `(S₂)` inequality. -/
lemma min_two_le_moduleDepth_of_isIntegrallyClosed (A : Type*)
    [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsIntegrallyClosed A] :
    min (2 : ℕ∞) ((ringKrullDim A).unbotD 0) ≤ moduleDepth A A := by
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, WithBot.unbotD_coe]
  let m := IsLocalRing.maximalIdeal A
  change min (2 : ℕ∞) m.height ≤ _
  by_cases hm : m = ⊥
  · simp [hm]
  obtain ⟨a, ham, ha0⟩ := (Submodule.ne_bot_iff m).mp hm
  have ha : IsSMulRegular A a := fun b c h => mul_left_cancel₀ ha0 h
  have h₁ : 1 ≤ moduleDepth A A := by
    have hmem : ∀ r ∈ [a], r ∈ m := by simpa using ham
    have hreg : RingTheory.Sequence.IsRegular A [a] :=
      (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr
        ((RingTheory.Sequence.isWeaklyRegular_singleton_iff A a).mpr ha)
    simpa using length_le_moduleDepth hmem hreg
  by_cases hd : m.height ≤ 1
  · exact (min_le_right _ _).trans (hd.trans h₁)
  have havoid : ∀ q ∈ associatedPrimes A (A ⧸ Ideal.span {a}), ¬ m ≤ q := by
    intro q hq hle
    have : q.IsPrime := hq.isPrime
    have hqm : q = m := le_antisymm (IsLocalRing.le_maximalIdeal_of_isPrime q) hle
    have hqh := (associatedPrimes_minimal_and_height_eq_one_and_iInf_localization_eq_bot
      (FractionRing A)).1 a ha0 q hq
    exact hd (by rw [← hqm, hqh.2])
  obtain ⟨b, hbm, hb⟩ :=
    (Ideal.exists_mem_isSMulRegular_iff_forall_associatedPrimes_not_le m
      (A ⧸ Ideal.span {a}) (associatedPrimes.finite A _)).mpr havoid
  have heq : a • (⊤ : Submodule A A) = Ideal.span {a} := by
    ext c
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and,
      smul_eq_mul, Ideal.mem_span_singleton]
    exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  have hb' : IsSMulRegular (QuotSMulTop a A) b := by
    change IsSMulRegular (A ⧸ a • (⊤ : Submodule A A)) b
    rwa [heq]
  have hmem : ∀ r ∈ [a, b], r ∈ m := by simp_all only [List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_self]
  have hreg : RingTheory.Sequence.IsRegular A [a, b] :=
    (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr
      ((RingTheory.Sequence.isWeaklyRegular_cons_iff A a [b]).mpr
        ⟨ha, (RingTheory.Sequence.isWeaklyRegular_singleton_iff (QuotSMulTop a A) b).mpr hb'⟩)
  exact (min_le_left _ _).trans (by simpa using length_le_moduleDepth hmem hreg)

/-- If some element outside a prime multiplies a larger algebra into the base ring, then the
localizations of the two rings at that prime agree. -/
private lemma algebraMap_localization_bijective_of_conductor
    {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S] (p : Ideal R) [p.IsPrime]
    (c : R) (hc : c ∉ p)
    (hcon : ∀ t : S, ∃ a : R, algebraMap R S a = algebraMap R S c * t) :
    Function.Bijective (algebraMap (Localization.AtPrime p)
      (Localization (Algebra.algebraMapSubmonoid S p.primeCompl))) := by
  let A := Localization.AtPrime p
  let B := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  refine ⟨FaithfulSMul.algebraMap_injective A B, ?_⟩
  intro b
  obtain ⟨t, s, rfl⟩ := IsLocalization.exists_mk'_eq
    (Algebra.algebraMapSubmonoid S p.primeCompl) b
  obtain ⟨r, hr, hrs⟩ := s.2
  obtain ⟨a, ha⟩ := hcon t
  let d : p.primeCompl := ⟨c * r, p.primeCompl.mul_mem hc hr⟩
  refine ⟨IsLocalization.mk' A a d, ?_⟩
  rw [IsLocalization.algebraMap_mk' S A B]
  apply (IsLocalization.mk'_eq_iff_eq_mul).mpr
  change algebraMap S B (algebraMap R S a) =
    IsLocalization.mk' B t s * algebraMap S B (algebraMap R S (c * r))
  rw [ha, map_mul, map_mul, map_mul]
  have hs : algebraMap S B (algebraMap R S r) = algebraMap S B s := congrArg _ hrs
  rw [hs]
  rw [mul_left_comm, IsLocalization.mk'_spec]

/-- Localizing an algebra at a prime of the base ring. -/
private noncomputable abbrev localizedAlgebraModuleEquiv
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] :
    LocalizedModule.AtPrime p S ≃ₗ[Localization.AtPrime p]
      Localization (Algebra.algebraMapSubmonoid S p.primeCompl) :=
  (LocalizedModule.equivTensorProduct p.primeCompl S).trans
    (Localization.tensorRightAlgEquiv p.primeCompl S).toLinearEquiv

/-- Under the conductor hypothesis the localization of the base ring is normal. -/
private lemma isIntegrallyClosed_localization_of_conductor
    {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S] [IsIntegrallyClosed S]
    (p : Ideal R) [p.IsPrime] (c : R) (hc : c ∉ p)
    (hcon : ∀ t : S, ∃ a : R, algebraMap R S a = algebraMap R S c * t) :
    IsIntegrallyClosed (Localization.AtPrime p) := by
  let A := Localization.AtPrime p
  let B := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  have hM : Algebra.algebraMapSubmonoid S p.primeCompl ≤ nonZeroDivisors S := by
    rintro t ⟨r, hr, rfl⟩
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro he
    exact hr ((FaithfulSMul.algebraMap_injective R S
      (he.trans (map_zero (algebraMap R S)).symm)) ▸ p.zero_mem)
  have : IsIntegrallyClosed B := isIntegrallyClosed_of_isLocalization B
    (Algebra.algebraMapSubmonoid S p.primeCompl) hM
  exact IsIntegrallyClosed.of_equiv
    (RingEquiv.ofBijective (algebraMap A B)
      (algebraMap_localization_bijective_of_conductor p c hc hcon)).symm

/-- A prime element together with an element it does not divide forms a weakly regular pair. -/
private lemma isWeaklyRegular_pair_of_prime {A : Type*} [CommRing A] [IsDomain A]
    {a b : A} (ha : Prime a) (hab : ¬ a ∣ b) :
    RingTheory.Sequence.IsWeaklyRegular A [a, b] := by
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  refine ⟨fun x y h => mul_left_cancel₀ ha.ne_zero h, ?_⟩
  change IsSMulRegular (A ⧸ a • (⊤ : Submodule A A)) b
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro x hx
  obtain ⟨v, _, hv⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  have hax : a ∣ x := (ha.dvd_or_dvd (show a ∣ b * x from ⟨v, hv.symm⟩)).resolve_left hab
  obtain ⟨v, hv⟩ := hax
  exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨v, trivial, hv.symm⟩

/-- Under the conductor hypothesis the localized algebra satisfies the local `(S₂)`
inequality. -/
private lemma min_two_le_moduleDepth_localized_of_conductor
    {R S : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S]
    [IsIntegrallyClosed S] (p : Ideal R) [p.IsPrime] (c : R) (hc : c ∉ p)
    (hcon : ∀ t : S, ∃ a : R, algebraMap R S a = algebraMap R S c * t) :
    min (2 : ℕ∞)
      ((moduleSupportDim (Localization.AtPrime p) (LocalizedModule.AtPrime p S)).unbotD 0) ≤
      moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p S) := by
  let A := Localization.AtPrime p
  let B := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let e : A ≃ₗ[A] B := LinearEquiv.ofBijective (Algebra.linearMap A B)
    (algebraMap_localization_bijective_of_conductor p c hc hcon)
  let eN := (localizedAlgebraModuleEquiv (S := S) p).trans e.symm
  have : IsIntegrallyClosed A := isIntegrallyClosed_localization_of_conductor p c hc hcon
  rw [moduleSupportDim_eq_of_linearEquiv eN, moduleSupportDim_self_eq_ringKrullDim,
    moduleDepth_eq_of_linearEquiv eN]
  exact min_two_le_moduleDepth_of_isIntegrallyClosed A

set_option synthInstance.maxHeartbeats 400000 in
-- Instances for the subalgebra `k[1, y, x², xy, x³]` and for its ideals unfold through
-- several coercion layers, which exhausts the default instance-search budget.
set_option maxSynthPendingDepth 1 in
/-- The polynomial ring satisfies Serre's condition `(S₂)` as a module over the subalgebra. -/
private theorem adjoin_polynomial_propertySkModule (k : Type u) [Field k] :
    let P := MvPolynomial (Fin 2) k
    let x : P := MvPolynomial.X 0
    let y : P := MvPolynomial.X 1
    let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
    letI := adjoin_isNoetherianRing k
    letI := adjoin_polynomial_finite k
    PropertySkModule R P 2 := by
  intro P x y R
  have := adjoin_isNoetherianRing k
  have := adjoin_polynomial_finite k
  let m : Ideal R := Ideal.span {r | (r : P) ∈ ({y, x ^ 2, x * y, x ^ 3} : Set P)}
  intro p hp
  by_cases hpm : p = m
  · subst p
    have hy : y ∈ R := Algebra.subset_adjoin (by simp)
    have hx2 : x ^ 2 ∈ R := Algebra.subset_adjoin (by simp)
    let yr : R := ⟨y, hy⟩
    let x2r : R := ⟨x ^ 2, hx2⟩
    have hregP : RingTheory.Sequence.IsWeaklyRegular P [yr, x2r] := by
      apply (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff P P [yr, x2r]).mp
      change RingTheory.Sequence.IsWeaklyRegular P [y, x ^ 2]
      apply isWeaklyRegular_pair_of_prime MvPolynomial.X_prime
      intro hdiv
      have hd : y ∣ x := (show Prime y from MvPolynomial.X_prime).dvd_of_dvd_pow hdiv
      exact (by decide : (1 : Fin 2) ≠ 0) (MvPolynomial.X_dvd_X.mp hd)
    have hmem : ∀ r ∈ [yr, x2r], r ∈ m := by
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact Ideal.subset_span (by simp [yr])
      · have hr' : r = x2r := by simpa using hr
        subst r
        exact Ideal.subset_span (by simp [x2r])
    let A := Localization.AtPrime m
    let N := LocalizedModule.AtPrime m P
    have : Nontrivial N := (localizedAlgebraModuleEquiv (S := P) m).toEquiv.nontrivial
    have : Module.Finite A N := Module.Finite.of_isLocalizedModule m.primeCompl
      (Rₚ := A) (LocalizedModule.mkLinearMap m.primeCompl P)
    have hreg : RingTheory.Sequence.IsRegular N ([yr, x2r].map (algebraMap R A)) :=
      hregP.isRegular_of_isLocalizedModule_of_mem (R := R) (M := P) (N := N) A m
        (LocalizedModule.mkLinearMap m.primeCompl P) hmem
    have hmemA : ∀ a ∈ [yr, x2r].map (algebraMap R A), a ∈ IsLocalRing.maximalIdeal A := by
      intro a ha
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A m r).mpr (hmem r hr)
    exact (min_le_left _ _).trans (by simpa using length_le_moduleDepth hmemA hreg)
  · have hmnot : ¬ m ≤ p := by
      intro hle
      exact hpm ((adjoinMaxIdeal_isMaximal k).eq_of_le hp.ne_top hle).symm
    obtain ⟨c, hcm, hcp⟩ := IsConcreteLE.not_le_iff_exists.mp hmnot
    apply min_two_le_moduleDepth_localized_of_conductor (S := P) p c hcp
    intro t
    exact ⟨⟨(c : P) * t, mul_mem_adjoin_of_mem_adjoinMaxIdeal k ⟨c, hcm⟩ t⟩, rfl⟩

set_option synthInstance.maxHeartbeats 400000 in
-- Instances for the subalgebra `k[1, y, x², xy, x³]` and for its ideals unfold through
-- several coercion layers, which exhausts the default instance-search budget.
/-- **Stacks Tag 0EBB.** The subalgebra `R = k[1, y, x², xy, x³]` of `k[x, y]` is a
Noetherian domain which is not `(S₂)`.  Both `R` and `k[x, y]` are reflexive as
`R`-modules, while `k[x, y]` is `(S₂)`.  Moreover, if
`m = (y, x², xy, x³)`, then the two successive `R`-duals of `k[x, y]` are `m`
and `k[x, y]`, respectively. -/
@[stacks 0EBB]
theorem mvPolynomial_adjoin_reflexive_propertyS2_module_not_propertyS2
    (k : Type u) [Field k] :
    let P := MvPolynomial (Fin 2) k
    let x : P := MvPolynomial.X 0
    let y : P := MvPolynomial.X 1
    let R : Subalgebra k P := Algebra.adjoin k {1, y, x ^ 2, x * y, x ^ 3}
    let m : Ideal R := Ideal.span {r | (r : P) ∈ ({y, x ^ 2, x * y, x ^ 3} : Set P)}
    ∃ (_ : IsNoetherianRing R) (_ : IsDomain R) (_ : Module.Finite R P),
      ∃ (dualPToM : Module.Dual R P ≃ₗ[R] m) (dualMToP : Module.Dual R m ≃ₗ[R] P),
        ¬ PropertySkRing R 2 ∧
          Module.IsReflexive R R ∧
          ¬ PropertySkModule R R 2 ∧
          (∀ (f : Module.Dual R P) (q : P),
            (↑(↑(dualPToM f) : R) : P) * q = (↑(f q) : P)) ∧
          (∀ (g : Module.Dual R m) (a : m),
            (↑(g a) : P) = dualMToP g * (↑(↑a : R) : P)) ∧
          Module.IsReflexive R P ∧
          PropertySkModule R P 2 := by
  intro P x y R m
  have := adjoin_isNoetherianRing k
  have := adjoin_polynomial_finite k
  let e₁ : Module.Dual R P ≃ₗ[R] m := dualPolynomialEquivAdjoinMaxIdeal k
  let e₂ : Module.Dual R m ≃ₗ[R] P := dualAdjoinMaxIdealEquivPolynomial k
  have hnot : ¬ PropertySkRing R 2 := adjoin_not_propertySkRing k
  refine ⟨inferInstance, inferInstance, inferInstance, e₁, e₂,
    hnot, inferInstance, ?_, ?_, ?_, adjoin_polynomial_isReflexive k,
    adjoin_polynomial_propertySkModule k⟩
  · exact fun h => hnot ((propertySkModule_self_iff_propertySkRing 2).mp h)
  · exact dualPolynomialEquivAdjoinMaxIdeal_mul_apply k
  · intro g a
    have h₂ (q : P) : (↑((e₂.symm q) a) : P) = q * (↑(↑a : R) : P) :=
      dualAdjoinMaxIdealEquivPolynomial_symm_apply k q a
    simpa only [LinearEquiv.symm_apply_apply] using h₂ (e₂ g)

/-! ### Coverage supplied by Mathlib

Mathlib's `Module.IsReflexive` is defined over a commutative semiring and an additive commutative
monoid, which is more general than the source's formulation over a domain; a linear map is an
isomorphism exactly when its underlying function is bijective, so the two agree. -/

add_to_stacks 0AUZ Module.IsReflexive
