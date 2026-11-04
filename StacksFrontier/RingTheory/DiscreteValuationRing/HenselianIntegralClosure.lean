module

public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.RingTheory.Henselian.FiniteType.Basic
public import StacksFrontier.RingTheory.IntegralClosure.DedekindDomain
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Integral closures over a henselian discrete valuation ring

Let `A` be a discrete valuation ring which is *henselian*, with fraction field `K`, and let
`K₁ / K` be a finite extension.  This file assembles the full instance package for the integral
closure `C = integralClosure A K₁`:

* `C` is a Dedekind domain, by the Krull–Akizuki variant `IsIntegralClosure`
  `.isDedekindDomain_and_comap_surjective_and_quasiFinite` (Stacks 09IG);
* `C` is **local**, because a domain integral over a henselian local ring is local (this is where
  henselianness enters, via the product decomposition of Stacks 04GJ);
* hence `C` is a discrete valuation ring with fraction field `K₁`, the structure map
  `A → C` is a local homomorphism, and `C` is flat over `A`;
* and if moreover `K₁ / K` is *separable*, `C` is module-finite over `A`.

Without henselianness `C` is only semilocal, and without separability it need not be
module-finite; both hypotheses are used exactly once, in the places named above.

This file is the public home of these statements; the Stacks 09EM omnibus, which needs them
behind its full base-change presentation data, delegates here.

## Main results

* `Stacks.DiscreteValuationRing.Ramification.isLocalRing_of_finite_of_henselianLocalRing`: a
  module-finite domain over a
  henselian local ring is local.
* `Stacks.DiscreteValuationRing.Ramification.isLocalRing_of_isIntegral_of_henselianLocalRing`: the
  same for an integral domain
  extension, by reduction to the module-finite case on simple subalgebras.
* `Stacks.DiscreteValuationRing.Ramification.isDiscreteValuationRing_of_isIntegral`: a local
  Dedekind domain integral over a
  discrete valuation ring is a discrete valuation ring.
* `Stacks.DiscreteValuationRing.Ramification.isDiscreteValuationRing_integralClosure`: the integral
  closure of a henselian
  discrete valuation ring in a finite extension of its fraction field is a discrete valuation
  ring.
* `Stacks.DiscreteValuationRing.Ramification.isLocalHom_algebraMap_integralClosure`,
  `Stacks.DiscreteValuationRing.Ramification.flat_integralClosure`,
  `Stacks.DiscreteValuationRing.Ramification.module_finite_integralClosure`,
    `Stacks.DiscreteValuationRing.Ramification.isFractionRing_integralClosure`: the
  remaining instances needed to apply the local fundamental identity to `A → C`.

## References

* [The Stacks Project, Tag 04GJ](https://stacks.math.columbia.edu/tag/04GJ)
* [The Stacks Project, Tag 09IG](https://stacks.math.columbia.edu/tag/09IG)
* [The Stacks Project, Tag 032L](https://stacks.math.columbia.edu/tag/032L)
-/

@[expose] public section

universe uA uB uK uK₁ u

namespace Stacks.DiscreteValuationRing.Ramification

/-! ### Locality over a henselian base -/

/-- A module-finite algebra over a henselian local ring which happens to be a domain is local.

Stacks 04GJ decomposes it as a finite product of local rings; a domain has no nontrivial
idempotents, so the product has exactly one factor. -/
@[ega "IV 18.5.9" "(ii), special case", sga "4 VIII 4.1" "(i), special case"]
theorem isLocalRing_of_finite_of_henselianLocalRing
    (R : Type uA) (S : Type uB) [CommRing R] [HenselianLocalRing R]
    [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S] : IsLocalRing S := by
  classical
  have : Module.Finite R (ULift.{uA} S) :=
    Module.Finite.equiv (ULift.moduleEquiv (R := R)).symm
  obtain ⟨n, D, hD, hAlg, hloc, hfin, ⟨e⟩⟩ :=
    exists_algEquiv_pi_isLocalRing R (ULift.{uA} S)
  let e' : S ≃+* ∀ i, D i := ULift.ringEquiv.symm.trans e.toRingEquiv
  have : IsDomain (∀ i, D i) := e'.symm.toMulEquiv.isDomain _
  have hn : n ≠ 0 := by
    intro hn
    subst n
    exact one_ne_zero (show (1 : ∀ i, D i) = 0 by ext i; exact Fin.elim0 i)
  have : Subsingleton (Fin n) := by
    refine ⟨fun i j => ?_⟩
    by_contra hij
    have hz : (Pi.single i (1 : D i) : ∀ k, D k) * Pi.single j 1 = 0 := by
      ext k
      by_cases hki : k = i
      · subst k; simp [hij]
      · simp [Pi.single_eq_of_ne hki]
    rcases mul_eq_zero.mp hz with h | h
    · have : (1 : D i) = 0 := by simpa using congrFun h i
      exact one_ne_zero this
    · have : (1 : D j) = 0 := by simpa using congrFun h j
      exact one_ne_zero this
  let : Unique (Fin n) := ⟨⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩, fun _ => Subsingleton.elim _ _⟩
  have : IsLocalRing (∀ i, D i) := (RingEquiv.piUnique D).symm.isLocalRing
  exact e'.symm.isLocalRing

/-- A domain integral over a henselian local ring is local.

Each element lies in a simple subalgebra, which is module-finite over the base and therefore
local by `isLocalRing_of_finite_of_henselianLocalRing`; locality is detected element by element
through `IsLocalRing.of_isUnit_or_isUnit_one_sub_self`. -/
@[sga "4 VIII 4.1" "(i), special case"]
theorem isLocalRing_of_isIntegral_of_henselianLocalRing
    (R S : Type*) [CommRing R] [HenselianLocalRing R]
    [CommRing S] [IsDomain S] [Algebra R S] [Algebra.IsIntegral R S] : IsLocalRing S := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  have : Module.Finite R (Algebra.adjoin R {x}) :=
    Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral x)
  have : IsLocalRing (Algebra.adjoin R {x}) :=
    isLocalRing_of_finite_of_henselianLocalRing R _
  let y : Algebra.adjoin R {x} := ⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self y with h | h
  · exact Or.inl (h.map (Algebra.adjoin R {x}).val)
  · exact Or.inr (h.map (Algebra.adjoin R {x}).val)

/-- A local Dedekind domain integral over a discrete valuation ring is a discrete valuation ring.

The only thing to check is that it is not a field, which follows from the base not being one. -/
theorem isDiscreteValuationRing_of_isIntegral
    (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDedekindDomain S] [IsLocalRing S]
    [Algebra R S] [Algebra.IsIntegral R S] [FaithfulSMul R S] :
    IsDiscreteValuationRing S := by
  have hnf : ¬ IsField S := fun h => IsDiscreteValuationRing.not_isField R
    (isField_of_isIntegral_of_isField (FaithfulSMul.algebraMap_injective R S) h)
  exact ((IsDiscreteValuationRing.TFAE S hnf).out 3 1).mp
    (show IsDedekindDomain S from inferInstance)

/-- A faithful domain extension of a discrete valuation ring is flat: it is torsion free, and a
discrete valuation ring is a Dedekind domain. -/
@[ega "0 6.3.4" "last assertion, A a DVR"]
theorem flat_of_faithfulSMul (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S] : Module.Flat R S := by
  have htf : Module.IsTorsionFree R S := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro r m hrm
    rw [Algebra.smul_def] at hrm
    rcases mul_eq_zero.mp hrm with h | h
    · exact Or.inl (FaithfulSMul.algebraMap_injective R S (by simpa using h))
    · exact Or.inr h
  infer_instance

/-- Clearing denominators identifies the generic fiber of an integral closure: if `S` is the
localization of `R` at `M` and `T` is integral over `S`, then `T` is the localization of an
integral closure `C` of `R` in `T` at the image of `M`. -/
theorem isLocalization_integralClosure_of_isIntegral
    (R : Type*) (S : Type*) (T : Type*) (C : Type*)
    [CommRing R] [CommRing S] [CommRing T] [CommRing C]
    [Algebra R S] [Algebra S T] [Algebra R T] [Algebra R C] [Algebra C T]
    [IsScalarTower R S T] [IsScalarTower R C T]
    (M : Submonoid R) [IsLocalization M S]
    [Algebra.IsIntegral S T] [IsIntegralClosure C R T] :
    IsLocalization (Algebra.algebraMapSubmonoid C M) T where
  map_units := by
    rintro ⟨_, r, hr, rfl⟩
    rw [← IsScalarTower.algebraMap_apply R C T, IsScalarTower.algebraMap_apply R S T]
    exact (IsLocalization.map_units S (⟨r, hr⟩ : M)).map (algebraMap S T)
  surj t := by
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization M t
      (Algebra.IsIntegral.isIntegral (R := S) t)
    obtain ⟨c, hc⟩ := (IsIntegralClosure.isIntegral_iff (A := C)).mp hm
    refine ⟨⟨c, ⟨algebraMap R C m, m, m.property, rfl⟩⟩, ?_⟩
    simpa only [← IsScalarTower.algebraMap_apply R C T, Submonoid.smul_def,
      Algebra.smul_def, mul_comm] using hc.symm
  exists_of_eq h := ⟨1, by simpa using IsIntegralClosure.algebraMap_injective C R T h⟩

/-! ### The integral closure in a finite extension of the fraction field -/

section IntegralClosure

variable (A : Type uA) (K : Type uK) (K₁ : Type uK₁) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
  [Field K] [Field K₁] [Algebra A K] [IsFractionRing A K]
  [Algebra K K₁] [Algebra A K₁] [IsScalarTower A K K₁] [FiniteDimensional K K₁]

omit [IsDomain A] [IsDiscreteValuationRing A] [FiniteDimensional K K₁] in
include K in
/-- A finite extension of the fraction field is a faithful `A`-algebra. -/
theorem faithfulSMul_of_isScalarTower : FaithfulSMul A K₁ :=
  (faithfulSMul_iff_algebraMap_injective A K₁).mpr (by
    rw [IsScalarTower.algebraMap_eq A K K₁]
    exact (algebraMap K K₁).injective.comp (IsFractionRing.injective A K))

omit [IsDomain A] [IsDiscreteValuationRing A] [FiniteDimensional K K₁] in
include K in
/-- The integral closure is a faithful `A`-algebra. -/
theorem faithfulSMul_integralClosure : FaithfulSMul A (integralClosure A K₁) := by
  have := faithfulSMul_of_isScalarTower A K K₁
  exact (faithfulSMul_iff_algebraMap_injective A _).mpr fun x y h =>
    FaithfulSMul.algebraMap_injective A K₁ (congrArg Subtype.val h)

omit [IsDiscreteValuationRing A] in
include K in
/-- `K₁` is the fraction field of the integral closure of `A` in it. -/
theorem isFractionRing_integralClosure : IsFractionRing (integralClosure A K₁) K₁ :=
  IsIntegralClosure.isFractionRing_of_finite_extension A K K₁ _

include K in
/-- **Krull–Akizuki.** The integral closure of a discrete valuation ring in a finite extension of
its fraction field is a Dedekind domain. -/
theorem isDedekindDomain_integralClosure : IsDedekindDomain (integralClosure A K₁) :=
  (IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite
    A K K₁ (integralClosure A K₁)).1

variable [HenselianLocalRing A]

omit [IsDomain A] [IsDiscreteValuationRing A] [FiniteDimensional K K₁] in
/-- Henselianness makes the integral closure local, not merely semilocal. -/
@[ega "0 23.2.6" "special case"]
theorem isLocalRing_integralClosure : IsLocalRing (integralClosure A K₁) :=
  isLocalRing_of_isIntegral_of_henselianLocalRing A _

include K in
/-- **The integral closure of a henselian discrete valuation ring in a finite extension of its
fraction field is a discrete valuation ring.**

This is the statement that makes the local fundamental identity `[K₁ : K] = e f` available at
every finite subextension of an algebraic extension of `K`. -/
@[sga "6 X 7.16" "special case"]
theorem isDiscreteValuationRing_integralClosure :
    IsDiscreteValuationRing (integralClosure A K₁) := by
  have := isDedekindDomain_integralClosure A K K₁
  have := isLocalRing_integralClosure A K₁
  have := faithfulSMul_integralClosure A K K₁
  exact isDiscreteValuationRing_of_isIntegral A _

omit [IsDomain A] [IsDiscreteValuationRing A] [FiniteDimensional K K₁] in
include K in
/-- The structure map to the integral closure is a local homomorphism: the maximal ideal of an
integral extension contracts to the maximal ideal. -/
theorem isLocalHom_algebraMap_integralClosure :
    IsLocalHom (algebraMap A (integralClosure A K₁)) := by
  have := isLocalRing_integralClosure A K₁
  have := faithfulSMul_integralClosure A K K₁
  exact RingHom.IsIntegral.isLocalHom (fun y => Algebra.IsIntegral.isIntegral y)
    (FaithfulSMul.algebraMap_injective A _)

omit [HenselianLocalRing A] in
/-- **Stacks 032L.** For a *separable* finite extension the integral closure is module-finite over
the base.  Separability is used only here. -/
theorem module_finite_integralClosure [Algebra.IsSeparable K K₁] :
    Module.Finite A (integralClosure A K₁) :=
  IsIntegralClosure.finite A K K₁ _

omit [HenselianLocalRing A] [FiniteDimensional K K₁] in
include K in
/-- The integral closure is flat over `A`: it is a torsion-free module over a discrete valuation
ring. -/
@[ega "0 6.3.4" "special case"]
theorem flat_integralClosure : Module.Flat A (integralClosure A K₁) :=
  have := faithfulSMul_integralClosure A K K₁
  flat_of_faithfulSMul A _

end IntegralClosure

end Stacks.DiscreteValuationRing.Ramification
