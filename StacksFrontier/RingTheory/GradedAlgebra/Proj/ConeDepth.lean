module

public import StacksFrontier.RingTheory.GradedAlgebra.Proj.DegreeOneUnitAwayBaseChange
public import StacksFrontier.RingTheory.Depth.FlatLocalHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Flat.Localization
public import StacksFrontier.RingTheory.Catenary.FormalFibresAssociatedDimension

/-!
# Depth on the punctured affine cone over a projective spectrum

Let `A` be a Noetherian graded ring, `g = cb` with `c ∈ A_{m+1}` and `b ∈ A_m`, `M` a finite graded
`A`-module and `𝔭` a prime of `A` not containing `g`. Write `B = A₍g₎`, `N = M₍g₎`, and `𝔮 ⊂ B`
for the prime under `𝔭`. Since `M[1/g]` is the base change of `N` along the free extension
`B → A[1/g]` (`Stacks.DegreeOneUnitAway.isBaseChange_degreeZero`), the localization `M_𝔭` is the
base change of `N_𝔮` along the flat local homomorphism `B_𝔮 → A_𝔭`, and the depth formula of
Stacks 0338 gives

`depth_{A_𝔭}(M_𝔭) = depth_{B_𝔮}(N_𝔮) + depth(A_𝔭 / 𝔮A_𝔭)`.

The fibre `A_𝔭 / 𝔮A_𝔭` is the localization of the domain `A/𝔭*`, `𝔭*` the homogeneous core of `𝔭`,
so it has depth at least one when `𝔭 ≠ 𝔭*`. This is the depth half of "either the depth goes up
by `1` or the dimension" in the proof of Stacks 0EL5: on the punctured cone `U → P`, a point is
either the generic point of its fibre (`𝔭 = 𝔭*`) or a closed point of it.

## Main definitions

* `Stacks.DegreeOneUnitAway.awayToAtPrime`: `A[1/g] → A_𝔭`.
* `Stacks.DegreeOneUnitAway.conePrime`: the prime `𝔮` of `A₍g₎` under `𝔭`.

## Main results

* `Stacks.DegreeOneUnitAway.depth_add_le_depth_localizedModule`
-/

@[expose] public noncomputable section

namespace Stacks.DegreeOneUnitAway

open HomogeneousLocalization Stacks.GradedLocalization TensorProduct IsLocalRing

universe u v

variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {g : A}

omit [SetLike σ A] [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- **The map `A[1/g] → A_𝔭`**, for a prime `𝔭` not containing `g`. -/
def awayToAtPrime (p : Ideal A) [p.IsPrime] (hgp : g ∉ p) :
    Localization.Away g →+* Localization.AtPrime p :=
  IsLocalization.Away.lift g
    (IsLocalization.map_units (Localization.AtPrime p) (⟨g, hgp⟩ : p.primeCompl))

omit [SetLike σ A] [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The map `A[1/g] → A_𝔭` sends the image of `a ∈ A` to the image of `a`. -/
theorem awayToAtPrime_algebraMap (p : Ideal A) [p.IsPrime] (hgp : g ∉ p) (a : A) :
    awayToAtPrime p hgp (algebraMap A (Localization.Away g) a) =
      algebraMap A (Localization.AtPrime p) a :=
  IsLocalization.Away.lift_eq _ _ _

variable (𝒜) in
/-- The composite `A₍g₎ → A[1/g] → A_𝔭`. -/
abbrev degreeZeroToAtPrime (p : Ideal A) [p.IsPrime] (hgp : g ∉ p) :
    Away 𝒜 g →+* Localization.AtPrime p :=
  (awayToAtPrime p hgp).comp (algebraMap (Away 𝒜 g) (Localization.Away g))

variable (𝒜) in
/-- **The prime `𝔮` of `A₍g₎` under `𝔭`.** -/
def conePrime (p : Ideal A) [p.IsPrime] (hgp : g ∉ p) : Ideal (Away 𝒜 g) :=
  (maximalIdeal (Localization.AtPrime p)).comap (degreeZeroToAtPrime 𝒜 p hgp)

/-- The ideal `𝔮` of `A₍g₎` under `𝔭` is prime. -/
theorem conePrime_isPrime (p : Ideal A) [p.IsPrime] (hgp : g ∉ p) :
    (conePrime 𝒜 p hgp).IsPrime :=
  Ideal.comap_isPrime _ _

variable (𝒜) in
/-- **The local homomorphism `A₍g₎_𝔮 → A_𝔭`.** -/
def coneLocalHom (p : Ideal A) [p.IsPrime] (hgp : g ∉ p) :
    letI := conePrime_isPrime (𝒜 := 𝒜) p hgp
    Localization.AtPrime (conePrime 𝒜 p hgp) →+* Localization.AtPrime p :=
  letI := conePrime_isPrime (𝒜 := 𝒜) p hgp
  IsLocalization.lift (M := (conePrime 𝒜 p hgp).primeCompl) (g := degreeZeroToAtPrime 𝒜 p hgp)
    fun y => notMem_maximalIdeal.mp y.2

/-- The map `A₍g₎_𝔮 → A_𝔭` restricts on `A₍g₎` to the composite `A₍g₎ → A[1/g] → A_𝔭`. -/
theorem coneLocalHom_algebraMap (p : Ideal A) [p.IsPrime] (hgp : g ∉ p) (z : Away 𝒜 g) :
    letI := conePrime_isPrime (𝒜 := 𝒜) p hgp
    coneLocalHom 𝒜 p hgp (algebraMap (Away 𝒜 g) (Localization.AtPrime (conePrime 𝒜 p hgp)) z) =
      degreeZeroToAtPrime 𝒜 p hgp z :=
  let := conePrime_isPrime (𝒜 := 𝒜) p hgp
  IsLocalization.lift_eq _ _

/-- The homomorphism `A₍g₎_𝔮 → A_𝔭` is local. -/
theorem isLocalHom_coneLocalHom (p : Ideal A) [p.IsPrime] (hgp : g ∉ p) :
    letI := conePrime_isPrime (𝒜 := 𝒜) p hgp
    IsLocalHom (coneLocalHom 𝒜 p hgp) := by
  let := conePrime_isPrime (𝒜 := 𝒜) p hgp
  refine ⟨fun a ha => ?_⟩
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (conePrime 𝒜 p hgp).primeCompl a
  rw [coneLocalHom, IsLocalization.lift_mk'] at ha
  have hx : IsUnit (degreeZeroToAtPrime 𝒜 p hgp x) := by
    have hs := notMem_maximalIdeal.mp s.2
    rw [IsUnit.mul_iff] at ha
    exact ha.1
  exact (IsLocalization.AtPrime.isUnit_mk'_iff _ _ _ _).2 (notMem_maximalIdeal.mpr hx)

omit [SetLike σ A] [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- `A[1/g] → A_𝔭` on fractions. -/
theorem awayToAtPrime_mk (p : Ideal A) [p.IsPrime] (hgp : g ∉ p) (r : A)
    (t : Submonoid.powers g) :
    awayToAtPrime p hgp (Localization.mk r t) =
      Localization.mk r (⟨t, Submonoid.powers_le.2 hgp t.2⟩ : p.primeCompl) := by
  rw [Localization.mk_eq_mk', awayToAtPrime, IsLocalization.Away.lift,
    IsLocalization.lift_mk'_spec, Localization.mk_eq_mk']
  have h := IsLocalization.mk'_spec (Localization.AtPrime p) r
    (⟨t, Submonoid.powers_le.2 hgp t.2⟩ : p.primeCompl)
  rw [mul_comm] at h
  exact h.symm

section Module

variable {M : Type v} [AddCommGroup M] [Module A M]

omit [SetLike σ A] [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The powers of `g` lie in the complement of `𝔭`. -/
theorem powers_le_primeCompl (p : Ideal A) [p.IsPrime] (hgp : g ∉ p) :
    Submonoid.powers g ≤ p.primeCompl :=
  Submonoid.powers_le.2 hgp

omit [SetLike σ A] [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- **The map `M[1/g] → M_𝔭`**, `x / gᵏ ↦ x / gᵏ`. -/
def awayToAtPrimeModule (p : Ideal A) [p.IsPrime] (hgp : g ∉ p) :
    LocalizedModule.Away (R := A) g M →+ LocalizedModule p.primeCompl M where
  toFun x := LocalizedModule.liftOn x
    (fun ms => LocalizedModule.mk ms.1 ⟨ms.2, powers_le_primeCompl p hgp ms.2.2⟩)
    (by
      rintro ⟨m, s⟩ ⟨m', s'⟩ ⟨u, hu⟩
      exact LocalizedModule.mk_eq.2 ⟨⟨u, powers_le_primeCompl p hgp u.2⟩, hu⟩)
  map_zero' := by
    rw [← LocalizedModule.zero_mk 1, LocalizedModule.liftOn_mk, LocalizedModule.zero_mk]
  map_add' x y := by
    induction x using LocalizedModule.induction_on with
    | h m s =>
    induction y using LocalizedModule.induction_on with
    | h m' s' =>
    rw [LocalizedModule.mk_add_mk, LocalizedModule.liftOn_mk, LocalizedModule.liftOn_mk,
      LocalizedModule.liftOn_mk, LocalizedModule.mk_add_mk]
    rfl

omit [SetLike σ A] [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The map `M[1/g] → M_𝔭` sends the fraction `m / s` to `m / s`. -/
theorem awayToAtPrimeModule_mk (p : Ideal A) [p.IsPrime] (hgp : g ∉ p) (m : M)
    (s : Submonoid.powers g) :
    awayToAtPrimeModule (M := M) p hgp (LocalizedModule.mk m s) =
      LocalizedModule.mk m (⟨s, powers_le_primeCompl p hgp s.2⟩ : p.primeCompl) :=
  rfl

end Module

section Tower

variable (p : Ideal A) [p.IsPrime] [hgp : Fact (g ∉ p)]
  {M : Type v} [AddCommGroup M] [Module A M]

/-- `A_𝔭` as an `A[1/g]`-algebra via `awayToAtPrime`. -/
local instance algAwayAtPrime : Algebra (Localization.Away g) (Localization.AtPrime p) :=
  (awayToAtPrime p hgp.out).toAlgebra

omit [SetLike σ A] [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The scalar tower `A → A[1/g] → A_𝔭`. -/
local instance isScalarTower_awayAtPrime :
    IsScalarTower A (Localization.Away g) (Localization.AtPrime p) :=
  IsScalarTower.of_algebraMap_eq fun a => (awayToAtPrime_algebraMap p hgp.out a).symm

/-- `M_𝔭` as an `A[1/g]`-module via `awayToAtPrime`. -/
local instance moduleAwayAtPrime :
    Module (Localization.Away g) (LocalizedModule p.primeCompl M) :=
  Module.compHom _ (awayToAtPrime p hgp.out)

omit [SetLike σ A] [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The scalar tower `A[1/g] → A_𝔭 → M_𝔭`. -/
local instance isScalarTower_awayAtPrimeModule :
    IsScalarTower (Localization.Away g) (Localization.AtPrime p)
      (LocalizedModule p.primeCompl M) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

omit [SetLike σ A] [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- **`M[1/g] → M_𝔭`**, linear over `A[1/g]`. -/
def awayToAtPrimeLinear :
    LocalizedModule.Away (R := A) g M →ₗ[Localization.Away g] LocalizedModule p.primeCompl M where
  toFun := awayToAtPrimeModule p hgp.out
  map_add' := map_add _
  map_smul' a x := by
    induction a using Localization.induction_on with
    | H a =>
    obtain ⟨r, t⟩ := a
    induction x using LocalizedModule.induction_on with
    | h m s =>
    rw [LocalizedModule.mk_smul_mk, awayToAtPrimeModule_mk, RingHom.id_apply,
      awayToAtPrimeModule_mk]
    change _ = awayToAtPrime p hgp.out (Localization.mk r t) •
      (LocalizedModule.mk m (⟨s, powers_le_primeCompl p hgp.out s.2⟩ : p.primeCompl) :
        LocalizedModule p.primeCompl M)
    rw [awayToAtPrime_mk, LocalizedModule.mk_smul_mk]
    rfl

omit [SetLike σ A] [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- `A_𝔭` is the localization of `A[1/g]` at the image of the complement of `𝔭`. -/
theorem isLocalization_atPrime_away :
    IsLocalization ((p.primeCompl).map (algebraMap A (Localization.Away g)))
      (Localization.AtPrime p) :=
  IsLocalization.isLocalization_of_submonoid_le (Localization.Away g) (Localization.AtPrime p)
    (Submonoid.powers g) p.primeCompl (powers_le_primeCompl p hgp.out)

omit [SetLike σ A] [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- **`M_𝔭` is the localization of `M[1/g]`** at the image of the complement of `𝔭`. -/
theorem isLocalizedModule_awayToAtPrimeLinear :
    IsLocalizedModule ((p.primeCompl).map (algebraMap A (Localization.Away g)))
      (awayToAtPrimeLinear (M := M) p) where
  map_units := by
    rintro ⟨_, s, hs, rfl⟩
    have h := IsLocalizedModule.map_units (LocalizedModule.mkLinearMap p.primeCompl M)
      (⟨s, hs⟩ : p.primeCompl)
    rw [Module.End.isUnit_iff] at h ⊢
    convert h using 1
    funext y
    change awayToAtPrime p hgp.out (algebraMap A (Localization.Away g) s) • y = s • y
    rw [awayToAtPrime_algebraMap, algebraMap_smul]
  surj y := by
    induction y using LocalizedModule.induction_on with
    | h m s =>
    refine ⟨⟨LocalizedModule.mk m 1, ⟨_, s, s.2, rfl⟩⟩, ?_⟩
    change awayToAtPrime p hgp.out (algebraMap A (Localization.Away g) s) •
      LocalizedModule.mk m s = awayToAtPrimeModule p hgp.out (LocalizedModule.mk m 1)
    rw [awayToAtPrime_algebraMap, algebraMap_smul, awayToAtPrimeModule_mk,
      LocalizedModule.smul'_mk]
    exact LocalizedModule.mk_eq.2 ⟨1, by simp [Submonoid.smul_def]⟩
  exists_of_eq {x₁ x₂} h := by
    induction x₁ using LocalizedModule.induction_on with
    | h m s =>
    induction x₂ using LocalizedModule.induction_on with
    | h m' s' =>
    have h' : awayToAtPrimeModule (M := M) p hgp.out (LocalizedModule.mk m s) =
        awayToAtPrimeModule p hgp.out (LocalizedModule.mk m' s') := h
    rw [awayToAtPrimeModule_mk, awayToAtPrimeModule_mk] at h'
    obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.1 h'
    refine ⟨⟨_, u, u.2, rfl⟩, ?_⟩
    change algebraMap A (Localization.Away g) u • LocalizedModule.mk m s =
      algebraMap A (Localization.Away g) u • LocalizedModule.mk m' s'
    rw [algebraMap_smul, algebraMap_smul, LocalizedModule.smul'_mk, LocalizedModule.smul'_mk,
      LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def] at hu ⊢
    rw [smul_comm (s' : A), smul_comm (s : A)]
    exact hu

/-! ### The graded part of the tower -/

variable {τ : Type*} [SetLike τ M] [AddSubgroupClass τ M] {𝓜 : ℤ → τ}
  [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝒜 𝓜]

/-- `M[1/g]` as an `A₍g₎`-module by restriction of scalars along `A₍g₎ → A[1/g]`. -/
local instance moduleAwayCD : Module (Away 𝒜 g) (LocalizedModule.Away (R := A) g M) :=
  Module.compHom (R := Localization.Away g) (LocalizedModule.Away (R := A) g M)
    (algebraMap (Away 𝒜 g) (Localization.Away g))

/-- The scalar tower `A₍g₎ → A[1/g] → M[1/g]`. -/
local instance isScalarTowerAwayCD :
    IsScalarTower (Away 𝒜 g) (Localization.Away g) (LocalizedModule.Away (R := A) g M) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- `A_𝔭` as an `A₍g₎`-algebra via `degreeZeroToAtPrime`. -/
local instance algDegreeZeroAtPrime : Algebra (Away 𝒜 g) (Localization.AtPrime p) :=
  (degreeZeroToAtPrime 𝒜 p hgp.out).toAlgebra

/-- The scalar tower `A₍g₎ → A[1/g] → A_𝔭`. -/
local instance isScalarTower_degreeZeroAwayAtPrime :
    IsScalarTower (Away 𝒜 g) (Localization.Away g) (Localization.AtPrime p) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- `M_𝔭` as an `A₍g₎`-module via `degreeZeroToAtPrime`. -/
local instance moduleDegreeZeroAtPrime : Module (Away 𝒜 g) (LocalizedModule p.primeCompl M) :=
  Module.compHom _ (degreeZeroToAtPrime 𝒜 p hgp.out)

/-- The scalar tower `A₍g₎ → A[1/g] → M_𝔭`. -/
local instance isScalarTower_degreeZeroAwayModule :
    IsScalarTower (Away 𝒜 g) (Localization.Away g) (LocalizedModule p.primeCompl M) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The scalar tower `A₍g₎ → A_𝔭 → M_𝔭`. -/
local instance isScalarTower_degreeZeroAtPrimeModule :
    IsScalarTower (Away 𝒜 g) (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The ideal `𝔮` of `A₍g₎` under `𝔭` is prime. -/
local instance conePrime_isPrime' : (conePrime 𝒜 p hgp.out).IsPrime := conePrime_isPrime p hgp.out

/-- `A_𝔭` as an `A₍g₎_𝔮`-algebra via `coneLocalHom`. -/
local instance algConeLocal :
    Algebra (Localization.AtPrime (conePrime 𝒜 p hgp.out)) (Localization.AtPrime p) :=
  (coneLocalHom 𝒜 p hgp.out).toAlgebra

/-- The scalar tower `A₍g₎ → A₍g₎_𝔮 → A_𝔭`. -/
local instance isScalarTower_coneLocal :
    IsScalarTower (Away 𝒜 g) (Localization.AtPrime (conePrime 𝒜 p hgp.out))
      (Localization.AtPrime p) :=
  IsScalarTower.of_algebraMap_eq fun z => (coneLocalHom_algebraMap p hgp.out z).symm

/-- `M_𝔭` as an `A₍g₎_𝔮`-module via `coneLocalHom`. -/
local instance moduleConeLocal :
    Module (Localization.AtPrime (conePrime 𝒜 p hgp.out)) (LocalizedModule p.primeCompl M) :=
  Module.compHom _ (coneLocalHom 𝒜 p hgp.out)

/-- The scalar tower `A₍g₎_𝔮 → A_𝔭 → M_𝔭`. -/
local instance isScalarTower_coneLocalModule :
    IsScalarTower (Localization.AtPrime (conePrime 𝒜 p hgp.out)) (Localization.AtPrime p)
      (LocalizedModule p.primeCompl M) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The scalar tower `A₍g₎ → A₍g₎_𝔮 → M_𝔭`. -/
local instance isScalarTower_coneLocalModule' :
    IsScalarTower (Away 𝒜 g) (Localization.AtPrime (conePrime 𝒜 p hgp.out))
      (LocalizedModule p.primeCompl M) :=
  IsScalarTower.of_algebraMap_smul fun z y => by
    change coneLocalHom 𝒜 p hgp.out _ • y = degreeZeroToAtPrime 𝒜 p hgp.out z • y
    rw [coneLocalHom_algebraMap]

/-- **`M_𝔭` is the base change of `N_𝔮` along `A₍g₎_𝔮 → A_𝔭`**, `N = M₍g₎`. -/
theorem exists_isBaseChange_conePrime {c b : A} {m : ℕ} (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m)
    (hcb : c * b = g) :
    ∃ j : LocalizedModule (conePrime 𝒜 p hgp.out).primeCompl
        (GradedModuleDegreeZeroLocalization 𝒜 𝓜 g) →ₗ[Localization.AtPrime (conePrime 𝒜 p hgp.out)]
          LocalizedModule p.primeCompl M,
      IsBaseChange (Localization.AtPrime p) j := by
  set N := GradedModuleDegreeZeroLocalization 𝒜 𝓜 g with hN
  have h0 : IsBaseChange (Localization.Away g) N.subtype := isBaseChange_degreeZero hc hb hcb
  have := isLocalization_atPrime_away (g := g) p
  have hι : IsBaseChange (Localization.AtPrime p) (awayToAtPrimeLinear (M := M) p) :=
    (isLocalizedModule_iff_isBaseChange ((p.primeCompl).map (algebraMap A (Localization.Away g)))
      (Localization.AtPrime p) _).1 (isLocalizedModule_awayToAtPrimeLinear p)
  have hcomp := h0.comp hι
  have hNR : IsBaseChange (Localization.AtPrime (conePrime 𝒜 p hgp.out))
      (LocalizedModule.mkLinearMap (conePrime 𝒜 p hgp.out).primeCompl N) :=
    (isLocalizedModule_iff_isBaseChange (conePrime 𝒜 p hgp.out).primeCompl _ _).1 inferInstance
  refine ⟨hNR.lift (((awayToAtPrimeLinear (M := M) p).restrictScalars (Away 𝒜 g)).comp
    N.subtype), IsBaseChange.of_comp hNR ?_⟩
  rw [hNR.lift_comp]
  exact hcomp

/-- `A_𝔭` is flat over `A₍g₎_𝔮`: `A[1/g]` is free over `A₍g₎`, and `A_𝔭` is a localization of
`A[1/g]`. -/
theorem flat_coneLocal {c b : A} {m : ℕ} (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m) (hcb : c * b = g) :
    Module.Flat (Localization.AtPrime (conePrime 𝒜 p hgp.out)) (Localization.AtPrime p) := by
  have := isLocalization_atPrime_away (g := g) p
  have : Module.Flat (Away 𝒜 g) (Localization.Away g) := flat_away hc hb hcb
  have : Module.Flat (Localization.Away g) (Localization.AtPrime p) :=
    IsLocalization.flat (Localization.AtPrime p)
      ((p.primeCompl).map (algebraMap A (Localization.Away g)))
  have : Module.Flat (Away 𝒜 g) (Localization.AtPrime p) :=
    Module.Flat.trans (Away 𝒜 g) (Localization.Away g) (Localization.AtPrime p)
  exact (Module.flat_iff_of_isLocalization (Localization.AtPrime (conePrime 𝒜 p hgp.out))
    (conePrime 𝒜 p hgp.out).primeCompl (Localization.AtPrime p)).2 this

/-- **The depth formula on the cone**: `depth(M_𝔭) = depth(N_𝔮) + depth(A_𝔭/𝔮A_𝔭)`, `N = M₍g₎`. -/
theorem depth_localizedModule_eq_add {c b : A} {m : ℕ} (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m)
    (hcb : c * b = g) [IsNoetherianRing A] [IsNoetherianRing (Away 𝒜 g)]
    [Module.Finite (Away 𝒜 g) (GradedModuleDegreeZeroLocalization 𝒜 𝓜 g)] :
    Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
        (LocalizedModule p.primeCompl M) =
      Module.depth (Localization.AtPrime (conePrime 𝒜 p hgp.out))
          (maximalIdeal (Localization.AtPrime (conePrime 𝒜 p hgp.out)))
          (LocalizedModule (conePrime 𝒜 p hgp.out).primeCompl
            (GradedModuleDegreeZeroLocalization 𝒜 𝓜 g)) +
        Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p ⧸
            ((maximalIdeal (Localization.AtPrime (conePrime 𝒜 p hgp.out))).map
              (algebraMap _ (Localization.AtPrime p)) •
                (⊤ : Submodule (Localization.AtPrime p) (Localization.AtPrime p)))) := by
  obtain ⟨j, hj⟩ := exists_isBaseChange_conePrime (𝓜 := 𝓜) p hc hb hcb
  have := flat_coneLocal (𝒜 := 𝒜) p hc hb hcb
  have : IsLocalHom (algebraMap (Localization.AtPrime (conePrime 𝒜 p hgp.out))
      (Localization.AtPrime p)) := isLocalHom_coneLocalHom (𝒜 := 𝒜) p hgp.out
  rw [← Module.depth_eq_depth_of_linearEquiv _ hj.equiv]
  exact Module.depth_tensorProduct_of_flat

/-- The image of a degree-zero fraction `a / gᵏ` in `A_𝔭`. -/
theorem degreeZeroToAtPrime_mk {m : ℕ} (hg : g ∈ 𝒜 (2 * m + 1)) (k : ℕ) (a : A)
    (ha : a ∈ 𝒜 (k • (2 * m + 1))) :
    degreeZeroToAtPrime 𝒜 p hgp.out (Away.mk 𝒜 hg k a ha) =
      IsLocalization.mk' (Localization.AtPrime p) a
        (⟨g ^ k, p.primeCompl.pow_mem hgp.out k⟩ : p.primeCompl) := by
  change awayToAtPrime p hgp.out (Away.mk 𝒜 hg k a ha).val = _
  rw [Away.val_mk, awayToAtPrime_mk, Localization.mk_eq_mk']

/-- A degree-zero fraction `a / gᵏ` lies in `𝔮` iff `a ∈ 𝔭`. -/
private theorem mk_mem_conePrime_iff {m : ℕ} (hg : g ∈ 𝒜 (2 * m + 1)) (k : ℕ) (a : A)
    (ha : a ∈ 𝒜 (k • (2 * m + 1))) :
    Away.mk 𝒜 hg k a ha ∈ conePrime 𝒜 p hgp.out ↔ a ∈ p := by
  change degreeZeroToAtPrime 𝒜 p hgp.out _ ∈ maximalIdeal (Localization.AtPrime p) ↔ _
  rw [degreeZeroToAtPrime_mk p hg k a ha,
    IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime p) p]

/-- **`𝔮 A_𝔭 = 𝔭* A_𝔭`**, `𝔭*` the homogeneous core of `𝔭`. -/
theorem map_conePrime_eq {c b : A} {m : ℕ} (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m)
    (hcb : c * b = g) :
    (conePrime 𝒜 p hgp.out).map (degreeZeroToAtPrime 𝒜 p hgp.out) =
      ((p.homogeneousCore 𝒜).toIdeal).map (algebraMap A (Localization.AtPrime p)) := by
  have hg := mul_mem hc hb hcb
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro z hz
    obtain ⟨k, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hg z
    have haP : a ∈ (p.homogeneousCore 𝒜).toIdeal :=
      Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨_, ha⟩
        ((mk_mem_conePrime_iff p hg k a ha).1 hz)
    rw [Ideal.mem_comap, degreeZeroToAtPrime_mk p hg k a ha, IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ haP)
  · rw [Ideal.map_le_iff_le_comap]
    change Ideal.span _ ≤ _
    rw [Ideal.span_le]
    rintro _ ⟨⟨a, ⟨d, had⟩⟩, hap, rfl⟩
    have hab : a * b ^ (2 * d) ∈ 𝒜 (d • (2 * m + 1)) := by
      have h := SetLike.mul_mem_graded had (SetLike.pow_mem_graded (2 * d) hb)
      convert h using 2
      simp only [smul_eq_mul]
      ring
    have hzmem : Away.mk 𝒜 hg d (a * b ^ (2 * d)) hab ∈ conePrime 𝒜 p hgp.out :=
      (mk_mem_conePrime_iff p hg d _ hab).2 (Ideal.mul_mem_right _ _ hap)
    have hloc : Localization.mk (a * b ^ (2 * d)) (genPow g d) *
        Localization.mk (c ^ (2 * d)) (genPow g d) =
          algebraMap A (Localization.Away g) a := by
      rw [Localization.mk_mul, ← Localization.mk_one_eq_algebraMap, Localization.mk_eq_mk_iff,
        Localization.r_iff_exists]
      refine ⟨1, ?_⟩
      subst hcb
      simp only [genPow, OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
      ring
    have heq : algebraMap A (Localization.AtPrime p) a =
        degreeZeroToAtPrime 𝒜 p hgp.out (Away.mk 𝒜 hg d (a * b ^ (2 * d)) hab) *
          awayToAtPrime p hgp.out (Localization.mk (c ^ (2 * d)) (genPow g d)) := by
      rw [← awayToAtPrime_algebraMap p hgp.out a, ← hloc, map_mul]
      rfl
    rw [SetLike.mem_coe, Ideal.mem_comap, heq]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hzmem)

/-- **The fibre of the cone has positive depth at a non-homogeneous prime.** When `𝔭` is not
homogeneous, `A_𝔭 / 𝔮A_𝔭 = A_𝔭 / 𝔭*A_𝔭` is a local domain which is not a field. -/
theorem one_le_depth_coneFibre {c b : A} {m : ℕ} (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m)
    (hcb : c * b = g) (hne : (p.homogeneousCore 𝒜).toIdeal ≠ p) :
    1 ≤ Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
      (Localization.AtPrime p ⧸
        ((maximalIdeal (Localization.AtPrime (conePrime 𝒜 p hgp.out))).map
          (algebraMap _ (Localization.AtPrime p)) •
            (⊤ : Submodule (Localization.AtPrime p) (Localization.AtPrime p)))) := by
  set J := (maximalIdeal (Localization.AtPrime (conePrime 𝒜 p hgp.out))).map
    (algebraMap _ (Localization.AtPrime p)) with hJdef
  set P := (p.homogeneousCore 𝒜).toIdeal with hPdef
  have hPprime : P.IsPrime := (inferInstance : p.IsPrime).homogeneousCore
  have hPle : P ≤ p := Ideal.toIdeal_homogeneousCore_le 𝒜 p
  have hJ : J = P.map (algebraMap A (Localization.AtPrime p)) := by
    rw [hJdef, ← IsLocalization.AtPrime.map_eq_maximalIdeal (conePrime 𝒜 p hgp.out)
      (Localization.AtPrime (conePrime 𝒜 p hgp.out)), Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
    exact map_conePrime_eq p hc hb hcb
  have hdisj : Disjoint (p.primeCompl : Set A) (P : Set A) :=
    Set.disjoint_left.2 fun _ hx hxP => hx (hPle hxP)
  have hQprime : (P.map (algebraMap A (Localization.AtPrime p))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl _ P hPprime hdisj
  obtain ⟨t, htp, htP⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hPle hne)
  have htmem : algebraMap A (Localization.AtPrime p) t ∈ maximalIdeal (Localization.AtPrime p) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p t).2 htp
  have htQ : algebraMap A (Localization.AtPrime p) t ∉
      P.map (algebraMap A (Localization.AtPrime p)) :=
    fun h => htP <| by
      rwa [← IsLocalization.under_map_of_isPrime_disjoint p.primeCompl (Localization.AtPrime p)
        hPprime hdisj]
  refine Module.one_le_depth_of_isSMulRegular _ _ htmem ?_
  intro x y hxy
  induction x using Submodule.Quotient.induction_on with
  | H x =>
  induction y using Submodule.Quotient.induction_on with
  | H y =>
  simp only [← Submodule.Quotient.mk_smul] at hxy
  rw [Submodule.Quotient.eq] at hxy ⊢
  rw [smul_eq_mul, Ideal.mul_top, hJ] at hxy ⊢
  rw [smul_eq_mul, smul_eq_mul, ← mul_sub] at hxy
  exact (hQprime.mem_or_mem hxy).resolve_left htQ

/-- **Depth on the cone**: `depth(N_𝔮) + ε ≤ depth(M_𝔭)`, with `ε = 1` when `𝔭` is not homogeneous
(a closed point of its fibre over `Proj A`) and `ε = 0` otherwise. -/
theorem depth_add_le_depth_localizedModule {c b : A} {m : ℕ} (hc : c ∈ 𝒜 (m + 1))
    (hb : b ∈ 𝒜 m) (hcb : c * b = g) [IsNoetherianRing A] [IsNoetherianRing (Away 𝒜 g)]
    [Module.Finite (Away 𝒜 g) (GradedModuleDegreeZeroLocalization 𝒜 𝓜 g)] :
    Module.depth (Localization.AtPrime (conePrime 𝒜 p hgp.out))
        (maximalIdeal (Localization.AtPrime (conePrime 𝒜 p hgp.out)))
        (LocalizedModule (conePrime 𝒜 p hgp.out).primeCompl
          (GradedModuleDegreeZeroLocalization 𝒜 𝓜 g)) +
      (if (p.homogeneousCore 𝒜).toIdeal = p then 0 else 1) ≤
    Module.depth (Localization.AtPrime p) (maximalIdeal (Localization.AtPrime p))
        (LocalizedModule p.primeCompl M) := by
  rw [depth_localizedModule_eq_add (𝓜 := 𝓜) p hc hb hcb]
  split_ifs with h
  · rw [add_zero]
    exact le_self_add
  · exact add_le_add_right (one_le_depth_coneFibre p hc hb hcb h) _

/-- The prime `𝔮` is the degree-zero part of `𝔭* A[1/g]`. -/
theorem conePrime_eq_comap {c b : A} {m : ℕ} (hc : c ∈ 𝒜 (m + 1)) (hb : b ∈ 𝒜 m)
    (hcb : c * b = g) :
    conePrime 𝒜 p hgp.out = Ideal.comap (algebraMap (Away 𝒜 g) (Localization.Away g))
      (((p.homogeneousCore 𝒜).toIdeal).map (algebraMap A (Localization.Away g))) := by
  have hg := mul_mem hc hb hcb
  have hPprime : ((p.homogeneousCore 𝒜).toIdeal).IsPrime :=
    (inferInstance : p.IsPrime).homogeneousCore
  have hdisj : Disjoint ((Submonoid.powers g : Submonoid A) : Set A)
      ((p.homogeneousCore 𝒜).toIdeal : Set A) := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ hk
    exact hgp.out (Ideal.toIdeal_homogeneousCore_le 𝒜 p (hPprime.mem_of_pow_mem k hk))
  ext z
  obtain ⟨k, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hg z
  rw [mk_mem_conePrime_iff p hg k a ha, Ideal.mem_comap,
    show algebraMap (Away 𝒜 g) (Localization.Away g) (Away.mk 𝒜 hg k a ha) =
      (Away.mk 𝒜 hg k a ha).val from rfl,
    Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
  refine ⟨fun hap => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _
    (Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨_, ha⟩ hap)), fun h => ?_⟩
  have h2 : algebraMap A (Localization.Away g) a ∈
      ((p.homogeneousCore 𝒜).toIdeal).map (algebraMap A (Localization.Away g)) := by
    have := Ideal.mul_mem_right (algebraMap A (Localization.Away g)
      ((⟨g ^ k, k, rfl⟩ : Submonoid.powers g) : A)) _ h
    rwa [mul_assoc, IsLocalization.mk'_spec, map_one, mul_one] at this
  refine Ideal.toIdeal_homogeneousCore_le 𝒜 p ?_
  rwa [← IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g)
    (Localization.Away g) hPprime hdisj]

end Tower

end Stacks.DegreeOneUnitAway

end
