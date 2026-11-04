module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.Sections
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.Topology.Dimension.DimensionFunctionCatenary

/-!
# Depth one at an immediate specialization of an associated point

Let `F` be a quasi-coherent module on a locally Noetherian scheme `X`, let `x'` be a point
associated to `F`, and let `x'` specialize immediately to `x`. Then the prime of the local ring
`𝒪_{X, x}` cut out by `x'` is an associated prime of the stalk `F_x`, it is strictly smaller than
the maximal ideal, and the quotient of `𝒪_{X, x}` by it has Krull dimension at most one. For a
stalk which is finite over the local ring this bounds `depth 𝒪_{X,x}(F_x)` by one.

Conversely every associated prime of the stalk `F_x` is cut out by an associated point of `F`,
namely its image under `Spec 𝒪_{X, x} → X`, and a prime immediately below the maximal ideal of
`𝒪_{X, x}` is cut out by a point specializing immediately to `x`. So the four statements below
translate the two sides of the condition "`x` is reached by an immediate specialization from an
associated point of `F`" between the scheme and the local ring at `x`.

## Main results

* `AlgebraicGeometry.depth_stalk_le_one_of_isAssociatedPoint_of_isImmediateSpecialization`: the
  stalk at the target of an immediate specialization from an associated point has depth at most
  one.
* `AlgebraicGeometry.exists_associatedPrime_stalk_of_isImmediateSpecialization`: the same
  hypotheses produce an associated prime of the stalk, strictly below the maximal ideal, with
  one-dimensional quotient, cut out by the associated point.
* `AlgebraicGeometry.isAssociatedPoint_fromSpecStalk_of_isAssociatedPrimeStacks`: the point of
  `X` cut out by an associated prime of the stalk is an associated point of `F`.
* `AlgebraicGeometry.isImmediateSpecialization_fromSpecStalk`: the point of `X` cut out by a
  prime immediately below the maximal ideal of `𝒪_{X, x}` specializes immediately to `x`.
* `AlgebraicGeometry.isAssociatedPrimeStacks_of_injective`: an injective linear map carries an
  associated prime to an associated prime.

## Implementation notes

The module structure on the stalk of an `𝒪_X`-module is spelled out as
`PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier`, as in
`AlgebraicGeometry.two_le_depth_stalk_pullback_of_flat` and `AlgebraicGeometry.IsImprovement`,
so the statements fit together with the existing depth results without transport.

Both directions pass through an affine open `U` containing `x`, on which the stalk is the
localization of `Γ(F, U)` at the prime of `Γ(X, U)` corresponding to `x`
(`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`), and associated points of `F` in `U`
are the associated primes of `Γ(F, U)`
(`AlgebraicGeometry.isAssociatedPrime_sections_of_isAssociatedPoint_of_fg` and
`AlgebraicGeometry.isAssociatedPoint_of_isAssociatedPrime_sections`). Going up, the annihilator
of a germ is computed by
`AlgebraicGeometry.isLocalizedModule_restriction_basicOpen_of_qcqs`: a germ vanishes exactly
when some function not vanishing at the point kills the section. Going down, a witness for the
associated prime upstairs is multiplied by a product of such functions, one for each generator
of the contracted prime, which is where Noetherianness of `Γ(X, U)` is used.

The bound on the depth is `Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes`, which
needs the stalk to be finite over the local ring; that is the only place finiteness enters, so
the three other statements assume none.

Immediate specialization is `TopologicalSpace.IsImmediateSpecialization`, whose three components
are the specialization, its nontriviality, and the absence of an intermediate point. The
intermediate-point clause corresponds, on an affine open, to the interval condition on prime
ideals used below, by `PrimeSpectrum.le_iff_specializes` and the injectivity of
`AlgebraicGeometry.IsAffineOpen.fromSpec`.

## References

* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
* [Stacks Project, Tag 02OK](https://stacks.math.columbia.edu/tag/02OK)
* [Stacks Project, Tag 0BK4](https://stacks.math.columbia.edu/tag/0BK4)
* [Stacks Project, Tag 0DX5](https://stacks.math.columbia.edu/tag/0DX5)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A germ of a quasi-coherent module over an affine open vanishes exactly when the section is
killed by a function not vanishing at the point. -/
private lemma affine_germ_eq_zero_iff {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) (m : Γ(F, U)) :
    F.presheaf.germ U x hx m = 0 ↔
      ∃ r : Γ(X, U), r ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ∧ r • m = 0 := by
  let p := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  let : IsLocalization.AtPrime (X.presheaf.stalk x) p := hU.isLocalization_stalk ⟨x, hx⟩
  constructor
  · intro hm
    obtain ⟨V, hxV, i, j, hij⟩ := TopCat.Presheaf.germ_eq F.presheaf x hx hx m 0
      (by simpa using hm)
    obtain ⟨r, hrV, hxr⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ hx
    let k : X.basicOpen r ⟶ U := homOfLE (X.basicOpen_le r)
    let φ := Scheme.Modules.restrictionLinearMap F k
    let : Module Γ(X, U) Γ(F, X.basicOpen r) :=
      Module.compHom Γ(F, X.basicOpen r) (X.presheaf.map k.op).hom
    have : IsLocalizedModule.Away r φ :=
      isLocalizedModule_restriction_basicOpen_of_qcqs F hU.isCompact hU.isQuasiSeparated r
    have hφ : φ m = 0 := by
      have he := congrArg (F.presheaf.map (homOfLE hrV).op) hij
      have hi : i.op ≫ (homOfLE hrV).op = k.op := Subsingleton.elim _ _
      simp only [map_zero, ← F.presheaf.map_comp_apply, hi] at he
      exact he
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (.powers r) φ).mp hφ
    have hr : r ∉ p := by
      apply (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x) p r).mp
      exact hxr.2
    exact ⟨r ^ n, fun h => hr ((hU.primeIdealOf ⟨x, hx⟩).isPrime.mem_of_pow_mem n h), hn⟩
  · rintro ⟨r, hr, hm⟩
    have hunit : IsUnit ((X.presheaf.germ U x hx).hom r) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x) p r).mpr hr
    apply (hunit.smul_eq_zero).mp
    calc
      _ = F.presheaf.germ U x hx (r • m) := (F.val.germ_smul x U hx r m).symm
      _ = 0 := by rw [hm, map_zero]

/-- The image of the annihilator of `m` is the annihilator of the image of `m`, for a map `g`
into a localization at a prime `q`: if `g` is compatible with the scalars (`hsmul`) and a value
`g y` vanishes exactly when some scalar outside `q` kills `y` (`hzero`), then a prime `p ≤ q`
which is the annihilator of `m` maps to the annihilator of `g m`.

Stated for bare rings and modules, with `g` a function and its two properties as hypotheses,
rather than inside the proof of `AlgebraicGeometry.associatedPrime_stalk_of_sections`, which is
its only caller. The module structure on the stalk of an `𝒪_X`-module is type-correct only after
`TopCat.Sheaf` is unfolded, and `rw` does not unfold it: the rewrite of the `Submodule.colon`
membership below fails there, on a goal `rw` reports as not type-correct at `implicit`
transparency. Here the same rewrites meet no coercion at all, and the single `exact` that applies
this lemma does the unfolding once, in its own `isDefEq` check. -/
private lemma isAssociatedPrimeStacks_map_of_isLocalizationAtPrime
    {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (q : Ideal R) [q.IsPrime] [IsLocalization.AtPrime S q]
    (p : Ideal R) (hp : p.IsPrime) (hpq : p ≤ q) (g : M → N) (m : M)
    (hsmul : ∀ (r : R) (y : M), algebraMap R S r • g y = g (r • y))
    (hzero : ∀ y : M, g y = 0 ↔ ∃ r : R, r ∉ q ∧ r • y = 0)
    (hm : (⊥ : Submodule R M).colon (Submodule.span R {m}) = p) :
    IsAssociatedPrimeStacks S N (p.map (algebraMap R S)) := by
  let : p.IsPrime := hp
  refine ⟨Ideal.isPrime_map_of_isLocalizationAtPrime q hpq, g m, ?_⟩
  ext z
  obtain ⟨r, t, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl z
  rw [Submodule.mem_colon_span_singleton, Submodule.mem_bot,
    IsLocalization.mk'_mem_map_algebraMap_iff q.primeCompl S]
  have hu : IsUnit (IsLocalization.mk' S 1 t) :=
    (IsLocalization.AtPrime.isUnit_mk'_iff S q 1 t).mpr q.primeCompl.one_mem
  rw [IsLocalization.mk'_eq_mul_mk'_one, mul_smul,
    smul_comm (algebraMap R S r) (IsLocalization.mk' S 1 t), hu.smul_eq_zero,
    hsmul r m, hzero]
  simp only [← mul_smul, ← hm, Submodule.mem_colon_span_singleton, Submodule.mem_bot]
  exact Iff.rfl

/-- An associated prime of the sections over an affine open which is contained in the prime of a
point of that open stays an associated prime after localizing at that point. -/
private lemma associatedPrime_stalk_of_sections {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) (p : Ideal Γ(X, U))
    (hp : IsAssociatedPrimeStacks Γ(X, U) Γ(F, U) p)
    (hpq : p ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    IsAssociatedPrimeStacks (X.presheaf.stalk x) (F.presheaf.stalk x)
      (p.map (X.presheaf.germ U x hx).hom) := by
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  let : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hx⟩
  let : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.IsPrime := (hU.primeIdealOf ⟨x, hx⟩).isPrime
  obtain ⟨hpp, m, hm⟩ := hp
  exact isAssociatedPrimeStacks_map_of_isLocalizationAtPrime _ p hpp hpq
    (fun y => F.presheaf.germ U x hx y) m
    (fun r y => (F.val.germ_smul x U hx r y).symm)
    (fun y => affine_germ_eq_zero_iff F U hU x hx y) hm

/-- If no prime lies strictly between `p` and `q`, then the quotient of the localization at `q`
by the image of `p` has Krull dimension at most one. -/
private lemma localized_quotient_dim_le_one {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsLocalRing S] (p q : Ideal R) [p.IsPrime] [q.IsPrime]
    [IsLocalization.AtPrime S q] (hpq : p ≤ q)
    (hinterval : ∀ r : Ideal R, r.IsPrime → p ≤ r → r ≤ q → r = p ∨ r = q) :
    ringKrullDim (S ⧸ p.map (algebraMap R S)) ≤ 1 := by
  let P := p.map (algebraMap R S)
  have hP : P.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime q hpq
  have hdim : ringKrullDim (S ⧸ P) =
      (Order.coheight (⟨P, hP⟩ : PrimeSpectrum S) : WithBot ℕ∞) := by
    rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]; rfl
  rw [hdim]
  suffices Order.coheight (⟨P, hP⟩ : PrimeSpectrum S) ≤ 1 by exact_mod_cast this
  rw [Order.coheight_eq_iSup_gt_coheight]
  refine iSup_le fun Q => iSup_le fun hPQ => ?_
  have hPr : p ≤ Q.asIdeal.under R := by
    rw [← Ideal.under_map_of_isLocalizationAtPrime (S := S) q hpq]
    exact Ideal.comap_mono hPQ.le
  have hrq : Q.asIdeal.under R ≤ q := by
    rw [← IsLocalization.AtPrime.under_maximalIdeal S q]
    exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal Q.isPrime.ne_top)
  rcases hinterval (Q.asIdeal.under R) (inferInstance : (Q.asIdeal.under R).IsPrime) hPr hrq with
    h | h
  · have he : Q.asIdeal = P := by
      rw [← IsLocalization.map_under q.primeCompl S Q.asIdeal, h]
    exact (hPQ.ne (PrimeSpectrum.ext he.symm)).elim
  · have he : Q.asIdeal = IsLocalRing.maximalIdeal S := by
      apply (IsLocalization.orderEmbedding q.primeCompl S).injective
      exact h.trans (IsLocalization.AtPrime.under_maximalIdeal S q).symm
    have hmax : IsMax Q := PrimeSpectrum.isMax_iff.mpr (he ▸ IsLocalRing.maximalIdeal.isMaximal S)
    rw [Order.IsMax.coheight_eq_zero hmax]
    simp

/-- An injective linear map carries an associated prime of the source to an associated prime of
the target: the image of a witness has the same annihilator. -/
public theorem isAssociatedPrimeStacks_of_injective {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M →ₗ[R] N) (he : Function.Injective e) (p : Ideal R)
    (hp : IsAssociatedPrimeStacks R M p) : IsAssociatedPrimeStacks R N p := by
  obtain ⟨hp, m, hm⟩ := hp
  refine ⟨hp, e m, ?_⟩
  ext r
  rw [← hm, Submodule.mem_colon_span_singleton, Submodule.mem_colon_span_singleton,
    ← e.map_smul, Submodule.mem_bot, Submodule.mem_bot, map_eq_zero_iff e he]

/-- An affine open containing `x`, together with the primes of its ring of functions cut out by
an associated point `x'` specializing immediately to `x`, the induced inclusion of primes, and
the interval condition that inclusion inherits from immediacy. -/
private lemma exists_affine_interval_of_isImmediateSpecialization {X : Scheme.{u}}
    (x' x : X) (himm : IsImmediateSpecialization x' x) :
    ∃ (U : X.Opens) (hU : IsAffineOpen U) (hx : x ∈ U) (hx' : x' ∈ U),
      (hU.primeIdealOf ⟨x', hx'⟩).asIdeal ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ∧
      (∀ r : Ideal Γ(X, U), r.IsPrime → (hU.primeIdealOf ⟨x', hx'⟩).asIdeal ≤ r →
        r ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal →
        r = (hU.primeIdealOf ⟨x', hx'⟩).asIdeal ∨ r = (hU.primeIdealOf ⟨x, hx⟩).asIdeal) := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x)
    (U := ⊤) (by trivial)
  have hx' : x' ∈ U := himm.1.mem_open U.isOpen hx
  have ep : hU.fromSpec (hU.primeIdealOf ⟨x', hx'⟩) = x' := hU.fromSpec_primeIdealOf ⟨x', hx'⟩
  have eq : hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) = x := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  refine ⟨U, hU, hx, hx', ?_, ?_⟩
  · exact (PrimeSpectrum.le_iff_specializes _ _).mpr
      (hU.fromSpec.isOpenEmbedding.isEmbedding.isInducing.specializes_iff.mp
        (by simpa only [ep, eq] using himm.1))
  · intro r hr hpr hrq
    have h₁ : x' ⤳ hU.fromSpec ⟨r, hr⟩ := by
      rw [← ep]
      exact ((PrimeSpectrum.le_iff_specializes _ _).mp hpr).map hU.fromSpec.continuous
    have h₂ : hU.fromSpec ⟨r, hr⟩ ⤳ x := by
      rw [← eq]
      exact ((PrimeSpectrum.le_iff_specializes _ _).mp hrq).map hU.fromSpec.continuous
    rcases himm.2.2 _ h₁ h₂ with h | h
    · exact Or.inl (congrArg PrimeSpectrum.asIdeal (hU.fromSpec.isOpenEmbedding.injective
        (h.trans ep.symm)))
    · exact Or.inr (congrArg PrimeSpectrum.asIdeal (hU.fromSpec.isOpenEmbedding.injective
        (h.trans eq.symm)))

/-- An affine open containing `x`, with the interval condition of immediacy and an associated prime
of the stalk at `x` cut out by an associated point `x'` specializing immediately to `x`. -/
private lemma exists_affine_interval_associatedPrime_stalk {X : Scheme.{u}}
    [IsLocallyNoetherian X] (F : X.Modules) [F.IsQuasicoherent] (x' x : X)
    (hass : x' ∈ Stacks.Divisors.associatedPoints F) (himm : IsImmediateSpecialization x' x) :
    ∃ (U : X.Opens) (hU : IsAffineOpen U) (hx : x ∈ U) (hx' : x' ∈ U),
      (hU.primeIdealOf ⟨x', hx'⟩).asIdeal ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ∧
      (∀ r : Ideal Γ(X, U), r.IsPrime → (hU.primeIdealOf ⟨x', hx'⟩).asIdeal ≤ r →
        r ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal →
        r = (hU.primeIdealOf ⟨x', hx'⟩).asIdeal ∨ r = (hU.primeIdealOf ⟨x, hx⟩).asIdeal) ∧
      letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      IsAssociatedPrimeStacks (X.presheaf.stalk x) (F.presheaf.stalk x)
        ((hU.primeIdealOf ⟨x', hx'⟩).asIdeal.map (X.presheaf.germ U x hx).hom) := by
  obtain ⟨U, hU, hx, hx', hpq, hinterval⟩ :=
    exists_affine_interval_of_isImmediateSpecialization x' x himm
  have : IsNoetherianRing Γ(X, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  exact ⟨U, hU, hx, hx', hpq, hinterval, associatedPrime_stalk_of_sections F U hU x hx _
    (isAssociatedPrime_sections_of_isAssociatedPoint_of_fg F U hU hx'
      (Ideal.FG.of_isNoetherianRing _) hass) hpq⟩

/-- The stalk of a quasi-coherent module at the target of an immediate specialization from an
associated point has depth at most one, provided the stalk is finite over the local ring.

The associated point cuts out an associated prime of the stalk whose quotient has Krull
dimension at most one, by
`AlgebraicGeometry.exists_associatedPrime_stalk_of_isImmediateSpecialization`, and the depth of
a finite module is bounded by the dimension of the quotient by an associated prime, which is
`Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes`. -/
public theorem depth_stalk_le_one_of_isAssociatedPoint_of_isImmediateSpecialization
    {X : Scheme.{u}} [IsLocallyNoetherian X] (F : X.Modules) [F.IsQuasicoherent]
    (x' x : X) (hass : x' ∈ Stacks.Divisors.associatedPoints F)
    (himm : IsImmediateSpecialization x' x)
    (hfinite :
      letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x)) :
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (F.presheaf.stalk x) ≤ 1 := by
  obtain ⟨U, hU, hx, hx', hpq, hinterval, hP⟩ :=
    exists_affine_interval_associatedPrime_stalk F x' x hass himm
  let p := hU.primeIdealOf ⟨x', hx'⟩
  let q := hU.primeIdealOf ⟨x, hx⟩
  let S := X.presheaf.stalk x
  let : Module S (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : Algebra Γ(X, U) S := (X.presheaf.germ U x hx).hom.toAlgebra
  let : IsLocalization.AtPrime S q.asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  have : Module.Finite S (F.presheaf.stalk x) := hfinite
  have hP' : p.asIdeal.map (algebraMap Γ(X, U) S) ∈ associatedPrimes S (F.presheaf.stalk x) := by
    obtain ⟨hP, m, hm⟩ := hP
    refine isAssociatedPrime_iff.mpr ⟨hP, m, ?_⟩
    change (⊥ : Submodule S (F.presheaf.stalk x)).colon _ =
      p.asIdeal.map (algebraMap Γ(X, U) S) at hm
    ext r
    rw [← hm, Submodule.mem_colon_span_singleton, Submodule.mem_colon_singleton]
  have hle := Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes hP'
  have hdim := localized_quotient_dim_le_one (S := S) p.asIdeal q.asIdeal hpq hinterval
  exact_mod_cast hle.trans hdim

/-- At the target of an immediate specialization from an associated point of a quasi-coherent
module on a locally Noetherian scheme, the local ring has an associated prime of the stalk which
is strictly below the maximal ideal, whose quotient has Krull dimension at most one, and which
cuts out the associated point.

No finiteness of the stalk is needed; the depth bound this yields for a finite stalk is
`AlgebraicGeometry.depth_stalk_le_one_of_isAssociatedPoint_of_isImmediateSpecialization`. -/
public theorem exists_associatedPrime_stalk_of_isImmediateSpecialization
    {X : Scheme.{u}} [IsLocallyNoetherian X] (F : X.Modules) [F.IsQuasicoherent]
    (x' x : X) (hass : x' ∈ Stacks.Divisors.associatedPoints F)
    (himm : IsImmediateSpecialization x' x) :
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    ∃ p : PrimeSpectrum (X.presheaf.stalk x),
      IsAssociatedPrimeStacks (X.presheaf.stalk x) (F.presheaf.stalk x) p.asIdeal ∧
      p.asIdeal < IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
      ringKrullDim ((X.presheaf.stalk x) ⧸ p.asIdeal) ≤ 1 ∧
      X.fromSpecStalk x p = x' := by
  obtain ⟨U, hU, hx, hx', hpq, hinterval, hP⟩ :=
    exists_affine_interval_associatedPrime_stalk F x' x hass himm
  let p := hU.primeIdealOf ⟨x', hx'⟩
  let q := hU.primeIdealOf ⟨x, hx⟩
  have ep : hU.fromSpec p = x' := hU.fromSpec_primeIdealOf ⟨x', hx'⟩
  have eq : hU.fromSpec q = x := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  let S := X.presheaf.stalk x
  let : Module S (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : Algebra Γ(X, U) S := (X.presheaf.germ U x hx).hom.toAlgebra
  let : IsLocalization.AtPrime S q.asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  let P := p.asIdeal.map (algebraMap Γ(X, U) S)
  let PP : PrimeSpectrum S := ⟨P, hP.1⟩
  have hunder : P.under Γ(X, U) = p.asIdeal :=
    Ideal.under_map_of_isLocalizationAtPrime (S := S) q.asIdeal hpq
  have hlt : P < IsLocalRing.maximalIdeal S := by
    refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hP.1.ne_top) ?_
    intro he
    have hpeq : p = q := PrimeSpectrum.ext (hunder.symm.trans
      ((congrArg (Ideal.under Γ(X, U)) he).trans
        (IsLocalization.AtPrime.under_maximalIdeal S q.asIdeal)))
    exact himm.2.1 (ep.symm.trans ((congrArg hU.fromSpec hpeq).trans eq))
  refine ⟨PP, hP, hlt, localized_quotient_dim_le_one (S := S)
    p.asIdeal q.asIdeal hpq hinterval, ?_⟩
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hx]
  show hU.fromSpec (PrimeSpectrum.comap (algebraMap Γ(X, U) S) PP) = x'
  rw [show PrimeSpectrum.comap (algebraMap Γ(X, U) S) PP = p from PrimeSpectrum.ext hunder]
  exact ep

/-- Transport of an associated prime of the sections over an affine open along a ring map whose
kernel on elements is detected by units: the contraction of an associated prime upstairs is an
associated prime downstairs.

A witness is obtained by multiplying a witness upstairs by a product of unit-witnesses, one for
each generator of the contracted prime, which is why the base ring is assumed Noetherian. -/
private lemma associatedPrime_comap_of_witness
    {R S M N : Type*} [CommRing R] [CommRing S] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (φ : R →+* S) (g : M →+ N) (hg : ∀ r m, g (r • m) = φ r • g m)
    (hz : ∀ m, g m = 0 → ∃ t : R, IsUnit (φ t) ∧ t • m = 0)
    (q : Ideal S) [q.IsPrime] (m : M)
    (hm : (⊥ : Submodule S N).colon (Submodule.span S {g m}) = q) :
    IsAssociatedPrimeStacks R M (q.comap φ) := by
  classical
  let p := q.comap φ
  obtain ⟨T, hT⟩ := Ideal.FG.of_isNoetherianRing p
  have kill (a : T) : ∃ t : R, IsUnit (φ t) ∧ t • (a.1 • m) = 0 := by
    apply hz
    rw [hg]
    exact Submodule.mem_colon_span_singleton.mp
      (hm.symm ▸ (show φ a.1 ∈ q from by
        show a.1 ∈ p
        rw [← hT]
        exact Ideal.subset_span a.2))
  choose t ht hk using kill
  let v : R := ∏ a : T, t a
  have hv : IsUnit (φ v) := by
    simpa only [v, map_prod] using IsUnit.prod_iff.mpr (fun a _ => ht a)
  have hkill (a : T) : a.1 • (v • m) = 0 := by
    obtain ⟨w, hw⟩ := Finset.dvd_prod_of_mem (s := Finset.univ)
      (f := fun a : T => t a) (Finset.mem_univ a)
    change v = t a * w at hw
    calc
      a.1 • (v • m) = w • (t a • (a.1 • m)) := by
        rw [hw]
        simp only [mul_smul]
        rw [smul_comm a.1 (t a), smul_comm a.1 w, smul_comm (t a) w]
      _ = 0 := by rw [hk a, smul_zero]
  refine ⟨inferInstance, v • m, le_antisymm ?_ ?_⟩
  · intro r hr
    have hzero : g (r • (v • m)) = 0 := by
      rw [Submodule.mem_colon_span_singleton, Submodule.mem_bot] at hr
      rw [hr, map_zero]
    rw [hg, hg, smul_comm, hv.smul_eq_zero] at hzero
    show φ r ∈ q
    rw [← hm, Submodule.mem_colon_span_singleton, Submodule.mem_bot]
    exact hzero
  · show p ≤ _
    rw [← hT, Ideal.span_le]
    intro a ha
    exact Submodule.mem_colon_span_singleton.mpr (hkill ⟨a, ha⟩)

/-- The point of `X` cut out by an associated prime of the stalk of a quasi-coherent module is an
associated point of that module.

The prime is contracted to an affine open containing `x`, where it becomes an associated prime of
the module of sections by `AlgebraicGeometry.associatedPrime_comap_of_witness`, and an associated
prime of the sections over an affine open is an associated point by
`AlgebraicGeometry.isAssociatedPoint_of_isAssociatedPrime_sections`. -/
public theorem isAssociatedPoint_fromSpecStalk_of_isAssociatedPrimeStacks
    {X : Scheme.{u}} [IsLocallyNoetherian X] (F : X.Modules) [F.IsQuasicoherent]
    (x : X) (q : PrimeSpectrum (X.presheaf.stalk x))
    (hq :
      letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) F.val x
      IsAssociatedPrimeStacks (X.presheaf.stalk x) (F.presheaf.stalk x) q.asIdeal) :
    X.fromSpecStalk x q ∈ Stacks.Divisors.associatedPoints F := by
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  obtain ⟨_, m, hm⟩ := hq
  obtain ⟨V, hxV, a, ha⟩ := F.presheaf.exists_germ_eq m
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hxV
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let aU : Γ(F, U) := F.presheaf.map (homOfLE (show U ≤ V from hUV)).op a
  have ham : F.presheaf.germ U x hxU aU = m := by
    dsimp only [aU]
    rw [TopCat.Presheaf.germ_res_apply]
    exact ha
  let φ := (X.presheaf.germ U x hxU).hom
  let p : PrimeSpectrum Γ(X, U) := PrimeSpectrum.comap φ q
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := φ.toAlgebra
  let : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := hU.isLocalization_stalk ⟨x, hxU⟩
  have hp : IsAssociatedPrimeStacks Γ(X, U) Γ(F, U) p.asIdeal := by
    refine associatedPrime_comap_of_witness φ (F.presheaf.germ U x hxU).hom
      (fun r a => F.val.germ_smul x U hxU r a) ?_ q.asIdeal aU ?_
    · intro a hzero
      obtain ⟨t, ht, hta⟩ := (affine_germ_eq_zero_iff F U hU x hxU a).mp hzero
      exact ⟨t, (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x)
        (hU.primeIdealOf ⟨x, hxU⟩).asIdeal t).mpr ht, hta⟩
    · simpa only [ham] using hm
  have he : hU.fromSpec p = X.fromSpecStalk x q :=
    congrArg (fun g : Spec (X.presheaf.stalk x) ⟶ X => g q)
      (hU.fromSpecStalk_eq_fromSpecStalk hxU)
  have hyU : hU.fromSpec p ∈ U := (hU.isoSpec.inv p).2
  have hprime : hU.primeIdealOf ⟨hU.fromSpec p, hyU⟩ = p :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)
  rw [← he]
  exact isAssociatedPoint_of_isAssociatedPrime_sections F U hU hyU
    (by simpa only [hprime] using hp)

/-- The point of `X` cut out by a prime of `𝒪_{X, x}` which is strictly below the maximal ideal
and has no prime strictly between it and the maximal ideal specializes immediately to `x`.

The three components of immediacy come from `Spec 𝒪_{X, x} → X` being an embedding with range the
set of points specializing to `x`: the specialization from the closed point, the injectivity of
the map, and the interval condition on primes. -/
public theorem isImmediateSpecialization_fromSpecStalk
    {X : Scheme.{u}} (x : X) (q : PrimeSpectrum (X.presheaf.stalk x))
    (hlt : q.asIdeal < IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hinterval : ∀ r : Ideal (X.presheaf.stalk x), r.IsPrime → q.asIdeal ≤ r →
      r ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) →
      r = q.asIdeal ∨ r = IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    IsImmediateSpecialization (X.fromSpecStalk x q) x := by
  let j := X.fromSpecStalk x
  have he : j (IsLocalRing.closedPoint (X.presheaf.stalk x)) = x :=
    Scheme.fromSpecStalk_closedPoint
  refine ⟨?_, ?_, ?_⟩
  · exact ((IsLocalRing.specializes_closedPoint q).map j.continuous).trans
      (specializes_of_eq he)
  · intro h
    exact hlt.ne (congrArg PrimeSpectrum.asIdeal (j.isEmbedding.injective (h.trans he.symm)))
  · intro z hqz hzx
    obtain ⟨r, hr⟩ := (Scheme.range_fromSpecStalk (x := x)).symm.subset hzx
    have hqr : q.asIdeal ≤ r.asIdeal := (PrimeSpectrum.le_iff_specializes _ _).mpr
      (j.isEmbedding.isInducing.specializes_iff.mp (by simpa only [j, hr] using hqz))
    rcases hinterval r.asIdeal r.isPrime hqr
      (IsLocalRing.le_maximalIdeal r.isPrime.ne_top) with h | h
    · exact Or.inl (hr.symm.trans (congrArg j (PrimeSpectrum.ext h)))
    · exact Or.inr (hr.symm.trans ((congrArg j (PrimeSpectrum.ext h)).trans he))

end AlgebraicGeometry

end
