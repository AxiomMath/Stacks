module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.RelativeAssassinTwo.AffineOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.FlatBaseChange
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction

/-!
# Bourbaki's lemma on the associated points of a flat tensor product

Let `f : X ⟶ S` be a morphism of schemes, let `F` be an `𝒪_X`-module which is flat over `S`,
and let `G` be an `𝒪_S`-module. The associated points of `F ⊗_{𝒪_X} f^* G` always *contain*
the union, over the associated points `s` of `G`, of the images in `X` of the associated points
of the restriction of `F` to the scheme-theoretic fibre `X_s`; if `S` is locally Noetherian the
two sets are equal.

The proof is stalkwise and reduces to the corresponding statement for modules
(`associatedPrimes.tensorProduct_of_flat`, Stacks 0312): with `R = 𝒪_{S, f x}` and
`A = 𝒪_{X, x}`, the stalk of the tensor product is `F_x ⊗_R G_{f x}`, the stalk of `F` on the
fibre is `F_x / 𝔪_R F_x`, and the maximal ideal of `A` is an associated prime of `F_x ⊗_R G_{f x}`
exactly when `𝔪_R ∈ Ass(G_{f x})` and `𝔪_A ∈ Ass(F_x / 𝔪_R F_x)`. The forward implication of
that last equivalence is where Noetherianity of `R` enters: it is used to see that the prime of
`R` contributed by the module-level statement can only be `𝔪_R`.

## Main results

* `AlgebraicGeometry.relativeAssassin_subset_associatedPoints_tensor_pullback`: the inclusion.
* `AlgebraicGeometry.associatedPoints_tensor_pullback_eq_relativeAssassin`: the equality over a
  locally Noetherian base.
* `AlgebraicGeometry.stalkModule_eq_moduleStalk` identifies the two module structures that
  exist on the stalk of an `𝒪_X`-module, and
  `AlgebraicGeometry.tensorSheafStalkEquiv` restates the tensor-stalk comparison of Stacks
  01CB against the one typeclass resolution finds.

## Implementation notes

The union in the source is indexed by the associated points of `G` and is written out
explicitly as a union of images under the fibre inclusions `f.fiberι s`, rather than through
`Stacks.Divisors.relativeAssassin`, because the source's index set is `Ass(G)` and not all of
`S`.

The tensor product of sheaves of modules is
  `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` and the pullback is
Mathlib's `AlgebraicGeometry.Scheme.Modules.pullback`. Two module structures on the stalk of a
sheaf of modules occur: `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule`, which the
  tensor-stalk comparison
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso` is stated against, and
`AlgebraicGeometry.Scheme.Modules.moduleStalk`, which is the structure found by typeclass
resolution and the one the associated-point predicate and the pullback-stalk comparison are
stated against. The two are the same instance (`stalkModule_eq_moduleStalk`, by `rfl`), and the
comparison is moved
across that equality once and for all in `tensorSheafStalkEquiv`; every other statement below
uses only the structure typeclass resolution finds, so that no local module structure ever
competes with a global one.

Associated primes are taken in the exact-annihilator sense of Stacks 00LA. They are spelled
here with `Submodule.colon` of a singleton *set* (`exactAssPrimes`), which is the form
`associatedPrimes.tensorProduct_of_flat` is stated in; `assStacks` is the same set spelled with
the span of a singleton, and `mem_exactAssPrimes_iff` is the bridge.

## References

* [Stacks Project, Tag 05DB](https://stacks.math.columbia.edu/tag/05DB)
-/

@[expose] public section

open CategoryTheory Limits TensorProduct

universe u

namespace AlgebraicGeometry

/-! ### Associated primes in the exact-annihilator form -/

/-- The set of primes that are *exactly* the annihilator of an element of `M`, spelled with
`Submodule.colon` of a singleton set.

This is `assStacks R M` written in the form `associatedPrimes.tensorProduct_of_flat` uses; see
`mem_exactAssPrimes_iff`. -/
private def exactAssPrimes (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :
    Set (Ideal R) :=
  {p | p.IsPrime ∧ ∃ m : M, (⊥ : Submodule R M).colon {m} = p}

/-- Alias of `AlgebraicGeometry.colon_span_singleton_eq_colon_singleton`. -/
private alias bot_colon_span_singleton := colon_span_singleton_eq_colon_singleton

private lemma mem_exactAssPrimes_iff
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {p : Ideal R} :
    p ∈ exactAssPrimes R M ↔ IsAssociatedPrimeStacks R M p := by
  constructor
  · rintro ⟨hp, m, hm⟩
    exact ⟨hp, m, (bot_colon_span_singleton m).trans hm⟩
  · rintro ⟨hp, m, hm⟩
    exact ⟨hp, m, (bot_colon_span_singleton m).symm.trans hm⟩

/-- A linear equivalence carries exact-annihilator associated primes of `M` to those of `N`. -/
private lemma exactAssPrimes_subset_of_linearEquiv
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    exactAssPrimes R M ⊆ exactAssPrimes R N := by
  rintro p ⟨hp, m, hm⟩
  refine ⟨hp, e m, ?_⟩
  ext r
  simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
  change (r • e m = 0) ↔ r ∈ p
  rw [← map_smul, ← map_zero e, e.injective.eq_iff]
  change (r • m = 0) ↔ r ∈ p
  rw [← hm]
  simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]

private lemma exactAssPrimes_eq_of_linearEquiv
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    exactAssPrimes R M = exactAssPrimes R N :=
  (exactAssPrimes_subset_of_linearEquiv e).antisymm
    (exactAssPrimes_subset_of_linearEquiv e.symm)

private lemma mem_exactAssPrimes_congr
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) {p : Ideal R} :
    p ∈ exactAssPrimes R M ↔ p ∈ exactAssPrimes R N := by
  rw [exactAssPrimes_eq_of_linearEquiv e]

/-! ### The module-theoretic input: Stacks 0312 -/

/-- **Stacks 0312**, the inclusion, at the level of modules: an exact-annihilator associated
prime of `N / 𝔭N` over `S` is one of `N ⊗_R M` whenever `𝔭` is one of `M` over `R`. -/
private lemma exact_associated_primes_tensor_flat_fiber_subset
    {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] [Module R N]
    [IsScalarTower R S N] [Module.Flat R N]
    (p : Ideal R) (hp : p ∈ exactAssPrimes R M)
    (q : Ideal S)
    (hq : q ∈ exactAssPrimes S
      (N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N)))) :
    q ∈ exactAssPrimes S (N ⊗[R] M) := by
  refine (associatedPrimes.tensorProduct_of_flat (R := R) (S := S) (M := M) (N := N)).1 ?_
  simp only [Set.mem_iUnion]
  exact ⟨p, hp, hq⟩

/-- **Stacks 0312**, the Noetherian equality, at the level of modules. -/
private lemma exact_associated_primes_tensor_flat_fiber_eq
    {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] [Module R N]
    [IsScalarTower R S N] [Module.Flat R N] [IsNoetherianRing R] :
    exactAssPrimes S (N ⊗[R] M) =
      ⋃ p ∈ associatedPrimes R M,
        exactAssPrimes S
          (N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N))) :=
  (associatedPrimes.tensorProduct_of_flat (R := R) (S := S) (M := M) (N := N)).2 inferInstance

/-- If the maximal ideal of `S` is an exact-annihilator associated prime of `N / 𝔭N` for a
prime `𝔭` of the local ring `R`, and `N` is flat over `R`, then `𝔭` is the maximal ideal. -/
private lemma maximalIdeal_eq_of_maximalIdeal_associated_quotient
    {R S N : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [AddCommGroup N] [Module S N]
    [Module R N] [IsScalarTower R S N] [Module.Flat R N]
    (p : Ideal R) (hp : p.IsPrime) (hpmax : p ≤ IsLocalRing.maximalIdeal R)
    (hq : IsLocalRing.maximalIdeal S ∈ exactAssPrimes S
      (N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N)))) :
    p = IsLocalRing.maximalIdeal R := by
  by_contra hne
  have hplt : p < IsLocalRing.maximalIdeal R := lt_of_le_of_ne hpmax hne
  have hnot : ¬ IsLocalRing.maximalIdeal R ≤ p := not_le_of_gt hplt
  change ¬ (IsLocalRing.maximalIdeal R : Set R) ⊆ (p : Set R) at hnot
  obtain ⟨r, hrmax, hrp⟩ := Set.not_subset.mp hnot
  obtain ⟨_, z, hz⟩ := hq
  let Q := N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N))
  let _ : Module R Q :=
    Submodule.Quotient.module' (R := S) (S := R)
      (p.map (algebraMap R S) • (⊤ : Submodule S N))
  have hsub : (p.map (algebraMap R S) • (⊤ : Submodule S N)).restrictScalars R =
      p • (⊤ : Submodule R N) := by
    rw [Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
  let e : N ⊗[R] (R ⧸ p) ≃ₗ[R] Q :=
    (TensorProduct.tensorQuotEquivQuotSMul N p).trans
      ((Submodule.quotEquivOfEq _ _ hsub.symm).trans
        (Submodule.Quotient.restrictScalarsEquiv R
          (p.map (algebraMap R S) • (⊤ : Submodule S N))))
  let rbar : R ⧸ p := Ideal.Quotient.mk p r
  let g : (R ⧸ p) →ₗ[R] (R ⧸ p) := LinearMap.mulLeft R rbar
  have hrbar : rbar ≠ 0 := fun h => hrp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hginj : Function.Injective g := by
    intro a b hab
    apply mul_left_cancel₀ hrbar
    simpa [g, LinearMap.mulLeft_apply, mul_comm] using hab
  have hTinj : Function.Injective (g.lTensor N) :=
    Module.Flat.lTensor_preserves_injective_linearMap g hginj
  have hgt (t : N ⊗[R] (R ⧸ p)) : (g.lTensor N) t = r • t := by
    refine TensorProduct.induction_on t ?_ ?_ ?_
    · simp
    · intro n a
      change n ⊗ₜ[R] (rbar * a) = (r • n) ⊗ₜ[R] a
      rw [TensorProduct.smul_tmul]
      simp [rbar, Algebra.smul_def]
    · intro x y hx hy
      simp [hx, hy]
  have he_g (t : N ⊗[R] (R ⧸ p)) :
      e ((g.lTensor N) t) = (algebraMap R S r) • e t := by
    calc
      e ((g.lTensor N) t) = e (r • t) := by rw [hgt]
      _ = r • e t := map_smul e r t
      _ = (algebraMap R S r) • e t := (IsScalarTower.algebraMap_smul S r _).symm
  have hqinj : ∀ w : Q, (algebraMap R S r) • w = 0 → w = 0 := by
    intro w hw
    have hmap : e ((g.lTensor N) (e.symm w)) = 0 := by
      rw [he_g, e.apply_symm_apply, hw]
    have hzero : (g.lTensor N) (e.symm w) = 0 := e.injective hmap
    have hsymmzero : e.symm w = 0 := hTinj hzero
    exact e.symm.injective (by simpa using hsymmzero)
  have hrkill : (algebraMap R S r) • z = 0 := by
    have hrmem : (algebraMap R S r) ∈ (⊥ : Submodule S Q).colon {z} := by
      rw [hz]
      exact map_nonunit (algebraMap R S) r hrmax
    have hzmem := Submodule.mem_colon_singleton.mp hrmem
    simpa only [IsScalarTower.algebraMap_smul S, Submodule.mem_bot] using hzmem
  have hztop : (⊥ : Submodule S Q).colon {z} = ⊤ := by
    rw [hqinj z hrkill]
    ext a
    simp [Submodule.mem_colon_singleton]
  refine absurd hz ?_
  rw [hztop]
  exact Ne.symm (IsLocalRing.maximalIdeal.isMaximal S).ne_top

/-- For a surjective map of local rings, the maximal ideal of the target is an
exact-annihilator associated prime of a module exactly when the maximal ideal of the source
is. -/
private lemma maximalIdeal_mem_exactAssPrimes_surjective_iff
    {R S M : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M] (hsurj : Function.Surjective (algebraMap R S)) :
    IsLocalRing.maximalIdeal S ∈ exactAssPrimes S M ↔
      IsLocalRing.maximalIdeal R ∈ exactAssPrimes R M := by
  have hcomap (m : M) :
      Ideal.comap (algebraMap R S) ((⊥ : Submodule S M).colon {m}) =
        (⊥ : Submodule R M).colon {m} := by
    ext r
    simp only [Ideal.mem_comap, Submodule.mem_colon_singleton, Submodule.mem_bot]
    rw [IsScalarTower.algebraMap_smul S]
  constructor
  · rintro ⟨_, m, hm⟩
    refine ⟨(IsLocalRing.maximalIdeal.isMaximal R).isPrime, m, ?_⟩
    calc
      (⊥ : Submodule R M).colon {m} =
          Ideal.comap (algebraMap R S) ((⊥ : Submodule S M).colon {m}) := (hcomap m).symm
      _ = Ideal.comap (algebraMap R S) (IsLocalRing.maximalIdeal S) := by rw [hm]
      _ = IsLocalRing.maximalIdeal R := IsLocalRing.maximalIdeal_comap _
  · rintro ⟨_, m, hm⟩
    refine ⟨(IsLocalRing.maximalIdeal.isMaximal S).isPrime, m, ?_⟩
    calc
      (⊥ : Submodule S M).colon {m} =
          Ideal.map (algebraMap R S)
            (Ideal.comap (algebraMap R S) ((⊥ : Submodule S M).colon {m})) :=
        (Ideal.map_comap_of_surjective _ hsurj _).symm
      _ = Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) := by rw [hcomap m, hm]
      _ = IsLocalRing.maximalIdeal S :=
        IsLocalRing.map_maximalIdeal_of_surjective _ hsurj

/-- **Stacks 0312** over a Noetherian local base, read at the maximal ideals: the maximal ideal
of `A` is associated to `M ⊗_R N` exactly when the maximal ideal of `R` is associated to `N`
and the maximal ideal of `A` is associated to `M / 𝔪_R M`. -/
private lemma maximalIdeal_mem_exactAssPrimes_tensor_iff
    {R A M N : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing A] [IsLocalRing A] [Algebra R A] [IsLocalHom (algebraMap R A)]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M] [Module.Flat R M]
    [AddCommGroup N] [Module R N] :
    IsLocalRing.maximalIdeal A ∈ exactAssPrimes A (M ⊗[R] N) ↔
      IsLocalRing.maximalIdeal R ∈ exactAssPrimes R N ∧
        IsLocalRing.maximalIdeal A ∈ exactAssPrimes A
          (M ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A) •
            (⊤ : Submodule A M)) := by
  constructor
  · intro h
    rw [exact_associated_primes_tensor_flat_fiber_eq (R := R) (S := A) (M := N) (N := M)] at h
    simp only [Set.mem_iUnion] at h
    obtain ⟨p, hp, hq⟩ := h
    have hprime : p.IsPrime := by
      rw [AssociatedPrimes.mem_iff] at hp
      exact hp.1
    have hpmax : p ≤ IsLocalRing.maximalIdeal R :=
      IsLocalRing.le_maximalIdeal hprime.ne_top
    have hp_eq : p = IsLocalRing.maximalIdeal R :=
      maximalIdeal_eq_of_maximalIdeal_associated_quotient p hprime hpmax hq
    subst p
    refine ⟨?_, hq⟩
    rw [mem_exactAssPrimes_iff]
    rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hp
    obtain ⟨hprime', n, hn⟩ := hp
    exact ⟨hprime', n, (bot_colon_span_singleton n).trans hn.symm⟩
  · rintro ⟨hp, hq⟩
    exact exact_associated_primes_tensor_flat_fiber_subset
      (R := R) (S := A) (M := N) (N := M)
      (IsLocalRing.maximalIdeal R) hp (IsLocalRing.maximalIdeal A) hq

/-! ### Two base-change identifications of a stalk

Both are stated purely in terms of abstract modules, so that at their use sites the module
structures involved are arguments and never the outcome of a typeclass search over a goal
spelled two ways at once. -/

/-- Cancelling a base change: if `T` is `N ⊗_A P` and `P` is `A ⊗_R M`, then `T` is
`N ⊗_R M`. -/
private noncomputable def tensorCancelBaseChangeEquiv
    {R A T N P M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup T] [Module A T]
    [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module R M]
    (eT : T ≃ₗ[A] N ⊗[A] P) (eP : P ≃ₗ[A] A ⊗[R] M) :
    T ≃ₗ[A] N ⊗[R] M :=
  eT.trans ((TensorProduct.congr (LinearEquiv.refl A N) eP).trans
    (AlgebraTensorModule.cancelBaseChange R A A N M))

/-- Base change along a quotient map: if `C` is `A ⧸ I` and `L` is `C ⊗_A M`, then `L` is
`M ⧸ I • M`. -/
noncomputable def quotientBaseChangeStalkEquiv
    {A C M L : Type*} [CommRing A] [CommRing C] [Algebra A C]
    [AddCommGroup L] [Module C L] [Module A L] [IsScalarTower A C L]
    [AddCommGroup M] [Module A M] (I : Ideal A)
    (eAlg : (A ⧸ I) ≃ₐ[A] C) (eL : L ≃ₗ[C] C ⊗[A] M) :
    L ≃ₗ[A] M ⧸ (I • (⊤ : Submodule A M)) :=
  (eL.restrictScalars A).trans
    ((TensorProduct.comm A C M).trans
      ((TensorProduct.congr (LinearEquiv.refl A M) eAlg.symm.toLinearEquiv).trans
        (TensorProduct.tensorQuotEquivQuotSMul M I)))

/-! ### The two module structures on the stalk of a sheaf of modules -/

/-- The module structure on the stalk of a sheaf of modules used by the tensor-stalk
comparison of Stacks 01CB is the one typeclass resolution finds. -/
lemma stalkModule_eq_moduleStalk {X : Scheme.{u}} (F : X.Modules) (x : X) :
    Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace F.val x =
      Scheme.Modules.moduleStalk F x :=
  rfl

/-- Transport a linear equivalence onto a tensor product along equalities of the three module
structures involved. The structures are ordinary arguments, so the transport is a `subst` and
needs no definitional unfolding. -/
noncomputable def transportLinearEquivTensor {R T M N : Type*} [CommRing R]
    [AddCommGroup T] [AddCommGroup M] [AddCommGroup N]
    {mT mT' : Module R T} {mM mM' : Module R M} {mN mN' : Module R N}
    (hT : mT = mT') (hM : mM = mM') (hN : mN = mN')
    (e : letI : Module R T := mT
         letI : Module R M := mM
         letI : Module R N := mN
         T ≃ₗ[R] M ⊗[R] N) :
    letI : Module R T := mT'
    letI : Module R M := mM'
    letI : Module R N := mN'
    T ≃ₗ[R] M ⊗[R] N := by
  subst hT
  subst hM
  subst hN
  exact e

/-- **Stacks 01CB** for an `𝒪_X`-module on a scheme, stated against the module structure on
stalks that typeclass resolution finds: the stalk of a tensor product is the tensor product of
the stalks.

The tensor product is presented as a sheaf of modules `T` on `X` *equal* to
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`, rather than as that term itself,
  because the module structure
typeclass resolution finds on the stalk of the latter is the Stacks 01CB one and not
`Scheme.Modules.moduleStalk`: matching the carrier of `moduleStalk` against the stalk of
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` requires unfolding `Scheme.ringCatSheaf`
  past `sheafCompose`,
beyond `instances` transparency. -/
@[ega "I 9.1.12" "special case"]
noncomputable def tensorSheafStalkEquiv {X : Scheme.{u}} (F G T : X.Modules)
    (hT : T = (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (G))) (x : X)
      :
    TopCat.Presheaf.stalk (C := Ab.{u}) T.val.presheaf x ≃ₗ[X.presheaf.stalk x]
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x ⊗[X.presheaf.stalk x]
        TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) := by
  subst hT
  exact transportLinearEquivTensor
    (stalkModule_eq_moduleStalk
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (G)) : X.Modules) x)
    (stalkModule_eq_moduleStalk F x) (stalkModule_eq_moduleStalk G x)
    (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso X.toRingedSpace x F G)

/-! ### The stalkwise criterion -/

/-- The point of the fibre corresponding to `x` is associated to the restriction of `F` to the
fibre exactly when the maximal ideal of `𝒪_{X, x}` is associated to `F_x / 𝔪_{f x} F_x`. -/
private lemma mem_associatedPoints_fiber_iff {X S : Scheme.{u}}
    (f : X ⟶ S) (F : X.Modules) (x : X) :
    f.asFiber x ∈ Stacks.Divisors.associatedPoints
        ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) ↔
      IsLocalRing.maximalIdeal (X.presheaf.stalk (f.fiberι (f x) (f.asFiber x))) ∈
        exactAssPrimes (X.presheaf.stalk (f.fiberι (f x) (f.asFiber x)))
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf
              (f.fiberι (f x) (f.asFiber x)) ⧸
            (Ideal.map (f.stalkMap (f.fiberι (f x) (f.asFiber x))).hom
                (IsLocalRing.maximalIdeal
                  (S.presheaf.stalk (f (f.fiberι (f x) (f.asFiber x))))) •
              (⊤ : Submodule (X.presheaf.stalk (f.fiberι (f x) (f.asFiber x)))
                (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf
                  (f.fiberι (f x) (f.asFiber x)))))) := by
  let : Algebra (X.presheaf.stalk (f.fiberι (f x) (f.asFiber x)))
      ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
    ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom.toAlgebra
  let : Module (X.presheaf.stalk (f.fiberι (f x) (f.asFiber x)))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.pullback (f.fiberι (f x))).obj F).val.presheaf (f.asFiber x)) :=
    Module.compHom _ ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom
  let : IsScalarTower (X.presheaf.stalk (f.fiberι (f x) (f.asFiber x)))
      ((f.fiber (f x)).presheaf.stalk (f.asFiber x))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.pullback (f.fiberι (f x))).obj F).val.presheaf (f.asFiber x)) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have hsurj : Function.Surjective
      (algebraMap (X.presheaf.stalk (f.fiberι (f x) (f.asFiber x)))
        ((f.fiber (f x)).presheaf.stalk (f.asFiber x))) :=
    (f.fiberι (f x)).stalkMap_surjective (f.asFiber x)
  have hlocal : IsLocalHom
      (algebraMap (X.presheaf.stalk (f.fiberι (f x) (f.asFiber x)))
        ((f.fiber (f x)).presheaf.stalk (f.asFiber x))) :=
    (f.fiberι (f x)).toLRSHom.prop (f.asFiber x)
  have eL : TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.pullback (f.fiberι (f x))).obj F).val.presheaf (f.asFiber x)
      ≃ₗ[(f.fiber (f x)).presheaf.stalk (f.asFiber x)]
      ((f.fiber (f x)).presheaf.stalk (f.asFiber x))
        ⊗[X.presheaf.stalk (f.fiberι (f x) (f.asFiber x))]
        TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf
          (f.fiberι (f x) (f.asFiber x)) :=
    Classical.choose (RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
      (f.fiberι (f x)).toLRSHom.toShHom F (f.asFiber x))
  have heR := Classical.choose_spec (quotientStalk_bridge f x)
  have eAlg : (X.presheaf.stalk (f.fiberι (f x) (f.asFiber x)) ⧸
        Ideal.map (f.stalkMap (f.fiberι (f x) (f.asFiber x))).hom
          (IsLocalRing.maximalIdeal
            (S.presheaf.stalk (f (f.fiberι (f x) (f.asFiber x))))))
      ≃ₐ[X.presheaf.stalk (f.fiberι (f x) (f.asFiber x))]
      ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
    AlgEquiv.ofRingEquiv (f := Classical.choose (quotientStalk_bridge f x)) fun a => heR a
  exact (mem_exactAssPrimes_iff.symm.trans
    (maximalIdeal_mem_exactAssPrimes_surjective_iff hsurj)).trans
      (mem_exactAssPrimes_congr (quotientBaseChangeStalkEquiv _ eAlg eL))

/-- **The stalkwise criterion for Stacks 05DB.** A point `x` is associated to
`F ⊗_{𝒪_X} f^* G` as soon as `f x` is associated to `G` and the corresponding point of the
fibre is associated to the restriction of `F`; over a Noetherian base stalk the converse holds
as well. -/
private lemma mem_associatedPoints_tensor_criterion {X S : Scheme.{u}}
    (f : X ⟶ S) (F : X.Modules) (G : S.Modules) (T : X.Modules)
    (hT : T = (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (((Scheme.Modules.pullback f).obj G))))
    (hF : IsFlatOver f.toLRSHom.toShHom F) (x : X) :
    ((f x ∈ Stacks.Divisors.associatedPoints G ∧
        f.asFiber x ∈ Stacks.Divisors.associatedPoints
          ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)) →
      x ∈ Stacks.Divisors.associatedPoints T) ∧
    (IsNoetherianRing (S.presheaf.stalk (f x)) →
      x ∈ Stacks.Divisors.associatedPoints T →
        f x ∈ Stacks.Divisors.associatedPoints G ∧
          f.asFiber x ∈ Stacks.Divisors.associatedPoints
            ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)) := by
  let : Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Module (S.presheaf.stalk (f x))
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
    Module.compHom _ (f.stalkMap x).hom
  let : IsScalarTower (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have hlocal : IsLocalHom (algebraMap (S.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    f.toLRSHom.prop x
  have hflat : Module.Flat (S.presheaf.stalk (f x))
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) := hF x
  -- The stalk of the pullback of `G`, as a base change of the stalk of `G`.
  have eP : TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.pullback f).obj G).val.presheaf x ≃ₗ[X.presheaf.stalk x]
      (X.presheaf.stalk x) ⊗[S.presheaf.stalk (f x)]
        TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f x) :=
    Classical.choose (RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
      f.toLRSHom.toShHom G x)
  -- The stalk of `F ⊗ f^* G`, as the base change `F_x ⊗_{𝒪_{S, f x}} G_{f x}`.
  have eT : TopCat.Presheaf.stalk (C := Ab.{u}) T.val.presheaf x
      ≃ₗ[X.presheaf.stalk x]
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x
        ⊗[S.presheaf.stalk (f x)]
        TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f x)) :=
    tensorCancelBaseChangeEquiv
      (tensorSheafStalkEquiv F ((Scheme.Modules.pullback f).obj G) T hT x) eP
  have hTmem := mem_exactAssPrimes_iff
    (R := X.presheaf.stalk x)
    (M := TopCat.Presheaf.stalk (C := Ab.{u}) T.val.presheaf x)
    (p := IsLocalRing.maximalIdeal (X.presheaf.stalk x))
  have hassoc := hTmem.symm.trans (mem_exactAssPrimes_congr eT)
  have hG := mem_exactAssPrimes_iff
    (R := S.presheaf.stalk (f x))
    (M := TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f x))
    (p := IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))
  have hfib := mem_associatedPoints_fiber_iff f F x
  rw [Scheme.Hom.fiberι_asFiber f x] at hfib
  constructor
  · rintro ⟨hGx, hXx⟩
    exact hassoc.2 (exact_associated_primes_tensor_flat_fiber_subset
      _ (hG.2 hGx) _ (hfib.1 hXx))
  · intro hnoeth hx
    have hsplit := (maximalIdeal_mem_exactAssPrimes_tensor_iff
      (R := S.presheaf.stalk (f x)) (A := X.presheaf.stalk x)
      (M := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)
      (N := TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f x))).1 (hassoc.1 hx)
    exact ⟨hG.1 hsplit.1, hfib.2 hsplit.2⟩

/-! ### The main results -/

/-- **Stacks Project, Tag 05DB, inclusion.** The associated points of the tensor
product with a pulled-back module contain the images of the associated points
of `F` on scheme-theoretic fibres over associated points of `G`. -/
@[stacks 05DB "the inclusion",
  ega "IV 3.3.1" "inclusion (3.3.1.1)",
  ega "IV 3.3.6" "⊇ only, one factor ="]
theorem relativeAssassin_subset_associatedPoints_tensor_pullback
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (G : S.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hF : IsFlatOver f.toLRSHom.toShHom F) :
    (⋃ s ∈ Stacks.Divisors.associatedPoints G,
      f.fiberι s ''
        Stacks.Divisors.associatedPoints
          ((Scheme.Modules.pullback (f.fiberι s)).obj F)) ⊆
    Stacks.Divisors.associatedPoints
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toLocallyRingedSpace.toRingedSpace)).presheaf, ((X.toLocallyRingedSpace.toRingedSpace)).IsSheaf⟩).obj (F)).obj (((Scheme.Modules.pullback f).obj G)))) := by
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_image] at hx
  obtain ⟨s, hsG, y, hy, hxy⟩ := hx
  have hfs : f x = s := by
    have hm : f.fiberι s y ∈ f ⁻¹' ({s} : Set S) := (f.range_fiberι s).le ⟨y, rfl⟩
    have hm' : f (f.fiberι s y) = s := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hm
    simpa [hxy] using hm'
  subst s
  have hyx : y = f.asFiber x := by
    apply (f.fiberι (f x)).isEmbedding.injective
    calc
      (f.fiberι (f x)) y = x := hxy
      _ = (f.fiberι (f x)) (f.asFiber x) := (Scheme.Hom.fiberι_asFiber f x).symm
  subst y
  exact (mem_associatedPoints_tensor_criterion f F G _ rfl hF x).1 ⟨hsG, hy⟩

/-- **Stacks Project, Tag 05DB, equality.** Over a locally Noetherian base, the
associated points of the tensor product are exactly the images of the
associated points of `F` on fibres over associated points of `G`. -/
@[stacks 05DB "equality for a locally Noetherian base",
  ega "IV 3.3.1" "equality (Noetherian)",
  ega "IV 3.3.6" "one factor = base"]
theorem associatedPoints_tensor_pullback_eq_relativeAssassin
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (G : S.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hF : IsFlatOver f.toLRSHom.toShHom F)
    [IsLocallyNoetherian S] :
    Stacks.Divisors.associatedPoints
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toLocallyRingedSpace.toRingedSpace)).presheaf, ((X.toLocallyRingedSpace.toRingedSpace)).IsSheaf⟩).obj (F)).obj (((Scheme.Modules.pullback f).obj G)))) =
      ⋃ s ∈ Stacks.Divisors.associatedPoints G,
        f.fiberι s ''
          Stacks.Divisors.associatedPoints
            ((Scheme.Modules.pullback (f.fiberι s)).obj F) := by
  refine Set.Subset.antisymm (fun x hx => ?_)
    (relativeAssassin_subset_associatedPoints_tensor_pullback f F G hF)
  obtain ⟨hG, hXx⟩ :=
    (mem_associatedPoints_tensor_criterion f F G _ rfl hF x).2 inferInstance hx
  simp only [Set.mem_iUnion, Set.mem_image]
  exact ⟨f x, hG, f.asFiber x, hXx, Scheme.Hom.fiberι_asFiber f x⟩

end AlgebraicGeometry
