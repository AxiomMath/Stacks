module

public import StacksFrontier.AlgebraicGeometry.Variety.DimensionOne.IntegralClosure
public import StacksFrontier.RingTheory.AbsolutelyIntegrallyClosed.HochsterHuneke.Local
public import StacksFrontier.RingTheory.Excellent.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The normalization of a one-dimensional local domain

Let `A` be a Noetherian local domain of dimension one with fraction field `F`, and let
`A' = integralClosure A F` be its normalization. This file collects, in the form a construction
of a tame symbol on Milnor K-theory consumes, the standard facts about `A'`:

* `A'` is a Dedekind domain with the same fraction field `F`, and it is semi-local: its maximal
  spectrum is finite;
* the localization `A'_𝔪` at a maximal ideal `𝔪` is a discrete valuation ring whose fraction
  field is again `F`, and whose residue field is a finite extension of the residue field of `A`;
* `A'` is a finite `A`-module as soon as `A` is a Nagata ring, in particular as soon as `A` is
  excellent.

The first two items are packaged as `Stacks.Normalization.semilocalDvrFamily`: a finite index
set, one discrete valuation ring per index together with the identification of its fraction field
with `F`, and the finiteness of each residue field extension.

## Main definitions

* `Stacks.Normalization.localizationAlgebra` — the `F`-algebra structure on `A'_𝔪` exhibiting `F`
  as the fraction field of `A'_𝔪`.
* `Stacks.Normalization.SemilocalDvrFamily` — the packaging: a finite family of discrete
  valuation rings with fraction field `F` and finite residue field extensions over the residue
  field of a local ring.
* `Stacks.Normalization.semilocalDvrFamily` — the family cut out by the normalization of a
  one-dimensional Noetherian local domain.

## Main results

* `Stacks.Normalization.isDedekindDomain_integralClosure`,
  `Stacks.Normalization.isFractionRing_integralClosure`,
  `Stacks.Normalization.finite_maximalSpectrum_integralClosure` — `A'` is a semi-local Dedekind
  domain with fraction field `F`.
* `Stacks.Normalization.isDiscreteValuationRing_localization`,
  `Stacks.Normalization.isFractionRing_localization`,
  `Stacks.Normalization.module_finite_residueField_localization` — the local rings of `A'` at its
  maximal ideals are discrete valuation rings with fraction field `F` and finite residue
  extensions over `κ(A)`.
* `Stacks.Normalization.module_finite_integralClosure_of_isNagataRing`,
  `Stacks.Normalization.module_finite_integralClosure_of_isExcellent` — finiteness of the
  normalization.
* `Stacks.Normalization.module_finite_residueField_of_quotient` — the auxiliary step that reads a
  residue field at a maximal ideal as the quotient by that ideal.

## Implementation notes

*Nothing here is re-proved.* The Dedekind, quasi-finiteness and semi-locality assertions are
Krull–Akizuki, `IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite` (Tag
09IG) and `IsIntegralClosure.finite_maximalSpectrum` (Tag 09N2), instantiated at `L = K = F`; the
finiteness of the residue extensions is Tag 031F,
`Ideal.isMaximal_and_finite_primesOver_and_module_finite_quotient`, transported along the
canonical bijection `A' ⧸ 𝔪 ≃ κ(𝔪)`; the discrete valuation ring assertion is Mathlib's
`IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`; and finiteness of the
normalization is `module_finite_integralClosure_of_isN1` applied to the N-1 property, which a
Nagata domain has by `IsAbsoluteIntegralClosure.isJapaneseRing_of_isNagataRing` and which an
excellent ring reaches through `isNagataRing_of_isQuasiExcellent` (Tag 07QV).

*Finiteness of the normalization is a Nagata hypothesis, not an excellence hypothesis.* It is
false for a general Noetherian local domain of dimension one, and the weakest condition on `A`
named in this development that gives it is `IsNagataRing` (equivalently, for a domain,
`IsJapaneseRing`, i.e. N-2 of Tag 032F); `IsExcellent` is strictly stronger and is recorded only
because it is the hypothesis the source of the tame symbol uses. `IsNagataRing` and `IsExcellent`
are both passed as explicit arguments: the first because it is not wanted as an instance here, the
second because `IsExcellent` is a `def` returning a conjunction rather than a class.

*Dimension one is `Ring.DimensionLEOne` together with `maximalIdeal A ≠ ⊥`.* The dimension bound
alone is what Krull–Akizuki needs; the non-vanishing of the maximal ideal, that is, `A` not being
a field, is needed exactly once, to know that the maximal ideals of `A'` are nonzero and hence
that the localizations there are not fields.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
* [Stacks Project, Tag 09IG](https://stacks.math.columbia.edu/tag/09IG)
* [Stacks Project, Tag 09N2](https://stacks.math.columbia.edu/tag/09N2)
* [Stacks Project, Tag 031F](https://stacks.math.columbia.edu/tag/031F)
* [Stacks Project, Tag 07QV](https://stacks.math.columbia.edu/tag/07QV)
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace Stacks.Normalization

/-! ### The normalization as a semi-local Dedekind domain -/

/-- The residue field at a maximal ideal `m` of an `R`-algebra `C` is a finite `R`-module as soon
as `C ⧸ m` is: the canonical map `C ⧸ m → κ(m)` is surjective, being bijective for `m` maximal. -/
theorem module_finite_residueField_of_quotient (R : Type*) [CommRing R] (C : Type*) [CommRing C]
    [Algebra R C] (m : Ideal C) [m.IsMaximal] [Module.Finite R (C ⧸ m)] :
    Module.Finite R (ResidueField (Localization.AtPrime m)) :=
  Module.Finite.of_surjective ((Algebra.linearMap (C ⧸ m) m.ResidueField).restrictScalars R)
    (Ideal.bijective_algebraMap_quotient_residueField m).2

section Normalization

variable (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
  [Ring.DimensionLEOne A] (F : Type v) [Field F] [Algebra A F] [IsFractionRing A F]

omit [IsLocalRing A] [IsNoetherianRing A] [Ring.DimensionLEOne A] in
/-- The fraction field of the normalization of `A` is the fraction field of `A`. -/
theorem isFractionRing_integralClosure : IsFractionRing ↥(integralClosure A F) F :=
  IsIntegralClosure.isFractionRing_of_finite_extension A F F ↥(integralClosure A F)

omit [IsLocalRing A] in
/-- **The normalization of a one-dimensional Noetherian local domain is a Dedekind domain.** -/
@[ega "IV 18.9.7.8" "special case"]
theorem isDedekindDomain_integralClosure : IsDedekindDomain ↥(integralClosure A F) :=
  (IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite A F F
    ↥(integralClosure A F)).1

omit [IsLocalRing A] in
/-- The normalization of a one-dimensional Noetherian local domain is quasi-finite over it: every
fibre of `Spec A' → Spec A` is a finite-dimensional vector space over the residue field. -/
theorem quasiFinite_integralClosure : Algebra.QuasiFinite A ↥(integralClosure A F) :=
  (IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite A F F
    ↥(integralClosure A F)).2.2

/-- **The normalization of a one-dimensional Noetherian local domain is semi-local:** it has only
finitely many maximal ideals. -/
@[ega "0 23.2.6" "special case"]
theorem finite_maximalSpectrum_integralClosure :
    Finite (MaximalSpectrum ↥(integralClosure A F)) :=
  IsIntegralClosure.finite_maximalSpectrum A F ↥(integralClosure A F)

/-! ### Finiteness of the normalization -/

omit [IsLocalRing A] [IsNoetherianRing A] [Ring.DimensionLEOne A] in
/-- **The normalization of a Nagata local domain of dimension one is a finite module over it.**
Being a Nagata domain, `A` is N-2, hence N-1, which is finiteness of the integral closure in any
field of fractions. -/
theorem module_finite_integralClosure_of_isNagataRing (hA : IsNagataRing A) :
    Module.Finite A ↥(integralClosure A F) :=
  let := hA
  module_finite_integralClosure_of_isN1 A F
    ((IsAbsoluteIntegralClosure.isJapaneseRing_of_isNagataRing A).finite (FractionRing A))

omit [IsLocalRing A] [IsNoetherianRing A] [Ring.DimensionLEOne A] in
/-- **The normalization of an excellent local domain of dimension one is a finite module over
it.** A quasi-excellent ring is Nagata (Tag 07QV). -/
@[ega "IV 7.8.3" "special case"]
theorem module_finite_integralClosure_of_isExcellent (hA : IsExcellent A) :
    Module.Finite A ↥(integralClosure A F) :=
  module_finite_integralClosure_of_isNagataRing A F (isNagataRing_of_isQuasiExcellent hA.1)

/-! ### The local rings of the normalization at its maximal ideals -/

omit [IsDomain A] [IsNoetherianRing A] [Ring.DimensionLEOne A] [IsFractionRing A F] in
/-- A maximal ideal of the normalization lies over the maximal ideal of `A`: it contracts to a
maximal ideal along an integral extension, and `A` is local. -/
theorem liesOver_maximalIdeal (m : Ideal ↥(integralClosure A F)) [m.IsMaximal] :
    m.LiesOver (maximalIdeal A) :=
  let : Algebra.IsIntegral A ↥(integralClosure A F) := IsIntegralClosure.isIntegral_algebra A F
  ⟨(eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) m)).symm⟩

omit [IsDomain A] [IsNoetherianRing A] [Ring.DimensionLEOne A] in
/-- A maximal ideal of the normalization of a one-dimensional local domain is nonzero: it
contracts to the maximal ideal of `A`, which is nonzero. -/
theorem ne_bot_of_isMaximal (hA : maximalIdeal A ≠ ⊥) (m : Ideal ↥(integralClosure A F))
    [m.IsMaximal] : m ≠ ⊥ := by
  let := liesOver_maximalIdeal A F m
  intro h
  refine hA ?_
  rw [Ideal.LiesOver.over (p := maximalIdeal A) (P := m), h]
  refine Ideal.comap_bot_of_injective _ fun a b hab => IsFractionRing.injective A F ?_
  rw [IsScalarTower.algebraMap_apply A ↥(integralClosure A F) F, hab,
    ← IsScalarTower.algebraMap_apply A ↥(integralClosure A F) F]

omit [IsLocalRing A] [IsNoetherianRing A] [Ring.DimensionLEOne A] in
/-- An element of the normalization outside a prime `m` is invertible in `F`. -/
theorem isUnit_algebraMap_of_mem_primeCompl (m : Ideal ↥(integralClosure A F))
    [m.IsPrime] (y : m.primeCompl) :
    IsUnit (algebraMap ↥(integralClosure A F) F (y : ↥(integralClosure A F))) :=
  let := isFractionRing_integralClosure A F
  isUnit_iff_ne_zero.mpr fun h => y.2 (by
    rw [IsFractionRing.to_map_eq_zero_iff.mp h]
    exact Ideal.zero_mem _)

/-- **`F` as an algebra over the local ring of the normalization at a prime `m`.** The structure
map is the one induced by `A' → F`, which inverts everything outside `m`. -/
noncomputable abbrev localizationAlgebra (m : Ideal ↥(integralClosure A F)) [m.IsPrime] :
    Algebra (Localization.AtPrime m) F :=
  (IsLocalization.lift (isUnit_algebraMap_of_mem_primeCompl A F m)).toAlgebra

omit [IsLocalRing A] [IsNoetherianRing A] [Ring.DimensionLEOne A] in
/-- `A' → A'_m → F` is `A' → F`. -/
theorem isScalarTower_localization (m : Ideal ↥(integralClosure A F)) [m.IsPrime] :
    letI := localizationAlgebra A F m
    IsScalarTower ↥(integralClosure A F) (Localization.AtPrime m) F :=
  let := localizationAlgebra A F m
  .of_algebraMap_eq fun x =>
    (IsLocalization.lift_eq (S := Localization.AtPrime m)
      (isUnit_algebraMap_of_mem_primeCompl A F m) x).symm

omit [IsLocalRing A] [IsNoetherianRing A] [Ring.DimensionLEOne A] in
/-- `A → A'_m → F` is `A → F`. -/
theorem isScalarTower_localization' (m : Ideal ↥(integralClosure A F)) [m.IsPrime] :
    letI := localizationAlgebra A F m
    IsScalarTower A (Localization.AtPrime m) F :=
  let := localizationAlgebra A F m
  let := isScalarTower_localization A F m
  .of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply A ↥(integralClosure A F) F,
      IsScalarTower.algebraMap_apply ↥(integralClosure A F) (Localization.AtPrime m) F,
      ← IsScalarTower.algebraMap_apply A ↥(integralClosure A F) (Localization.AtPrime m)]

omit [IsLocalRing A] [IsNoetherianRing A] [Ring.DimensionLEOne A] in
/-- **The fraction field of the local ring of the normalization at a prime is `F`.** -/
theorem isFractionRing_localization (m : Ideal ↥(integralClosure A F)) [m.IsPrime] :
    letI := localizationAlgebra A F m
    IsFractionRing (Localization.AtPrime m) F :=
  let := isFractionRing_integralClosure A F
  let := localizationAlgebra A F m
  let := isScalarTower_localization A F m
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization m.primeCompl
    (Localization.AtPrime m) F

/-- **The local ring of the normalization at a maximal ideal is a discrete valuation ring.** The
normalization is a Dedekind domain and the maximal ideal is nonzero. -/
theorem isDiscreteValuationRing_localization (hA : maximalIdeal A ≠ ⊥)
    (m : Ideal ↥(integralClosure A F)) [m.IsMaximal] :
    IsDiscreteValuationRing (Localization.AtPrime m) :=
  let := isFractionRing_integralClosure A F
  let := isDedekindDomain_integralClosure A F
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ↥(integralClosure A F)
    (ne_bot_of_isMaximal A F hA m) (Localization.AtPrime m)

omit [IsDomain A] [IsNoetherianRing A] [Ring.DimensionLEOne A] [IsFractionRing A F] in
/-- `A → A'_m` is a local ring homomorphism: the maximal ideal of `A` lands in `m`, hence in the
maximal ideal of the localization. -/
theorem isLocalHom_algebraMap_localization (m : Ideal ↥(integralClosure A F)) [m.IsMaximal] :
    IsLocalHom (algebraMap A (Localization.AtPrime m)) := by
  let := liesOver_maximalIdeal A F m
  refine ((local_hom_TFAE (algebraMap A (Localization.AtPrime m))).out 4 1).mp ?_
  intro a ha
  show algebraMap A (Localization.AtPrime m) a ∈ maximalIdeal _
  rw [IsScalarTower.algebraMap_apply A ↥(integralClosure A F) (Localization.AtPrime m)]
  refine (IsLocalization.AtPrime.to_map_mem_maximal_iff _ m _).mpr ?_
  rwa [Ideal.LiesOver.over (p := maximalIdeal A) (P := m)] at ha

/-- **The residue field at a maximal ideal of the normalization is a finite `A`-module.** This is
the residue field assertion of Tag 031F, read through the canonical isomorphism `A' ⧸ m ≃ κ(m)`. -/
theorem module_finite_residueField (m : Ideal ↥(integralClosure A F)) [m.IsMaximal] :
    Module.Finite A (ResidueField (Localization.AtPrime m)) := by
  let := isFractionRing_integralClosure A F
  let := isDedekindDomain_integralClosure A F
  let := liesOver_maximalIdeal A F m
  have h031F : Module.Finite (A ⧸ maximalIdeal A) (↥(integralClosure A F) ⧸ m) :=
    (Ideal.isMaximal_and_finite_primesOver_and_module_finite_quotient A
      ↥(integralClosure A F) F F (maximalIdeal A)).2.2.1 m
  let : Module.Finite A (↥(integralClosure A F) ⧸ m) :=
    Module.Finite.trans (A ⧸ maximalIdeal A) _
  exact module_finite_residueField_of_quotient A ↥(integralClosure A F) m

/-- **The residue field of the local ring of the normalization at a maximal ideal is a finite
extension of the residue field of `A`**, along the residue field map of `A → A'_m`. -/
@[ega "0 23.2.6" "special case"]
theorem module_finite_residueField_localization (m : Ideal ↥(integralClosure A F))
    [m.IsMaximal] :
    letI := isLocalHom_algebraMap_localization A F m
    Module.Finite (ResidueField A) (ResidueField (Localization.AtPrime m)) :=
  let := isLocalHom_algebraMap_localization A F m
  let := module_finite_residueField A F m
  Module.Finite.of_restrictScalars_finite A (ResidueField A)
    (ResidueField (Localization.AtPrime m))

end Normalization

/-! ### The packaging -/

/-- **A finite family of discrete valuation rings with a common fraction field, finite over a
local ring.** The data a tame symbol `∂_A : K^M_{i+1}(F) → K^M_i(κ(A))` built as a sum
`Σ N_{κ_i/κ(A)} ∘ ∂_{A_i}` consumes: a finite index set, a discrete valuation ring `A_i` for each
index whose fraction field is identified with `F` compatibly with `A → F`, and the finiteness of
each residue field extension `κ(A_i)/κ(A)`. -/
structure SemilocalDvrFamily (A : Type u) [CommRing A] [IsLocalRing A]
    (F : Type v) [Field F] [Algebra A F] where
  /-- The index set. -/
  Index : Type w
  [finite_index : Finite Index]
  /-- The discrete valuation ring at the index `i`. -/
  Dvr : Index → Type w
  [commRing : ∀ i, CommRing (Dvr i)]
  [isDomain : ∀ i, IsDomain (Dvr i)]
  [isDiscreteValuationRing : ∀ i, IsDiscreteValuationRing (Dvr i)]
  [algebraBase : ∀ i, Algebra A (Dvr i)]
  [isLocalHom : ∀ i, IsLocalHom (algebraMap A (Dvr i))]
  [algebraFractionField : ∀ i, Algebra (Dvr i) F]
  [isScalarTower : ∀ i, IsScalarTower A (Dvr i) F]
  [isFractionRing : ∀ i, IsFractionRing (Dvr i) F]
  [moduleFiniteResidueField : ∀ i, Module.Finite (ResidueField A) (ResidueField (Dvr i))]

/-- **The normalization of a one-dimensional Noetherian local domain, packaged.** The index set is
the (finite) maximal spectrum of the normalization `A'` of `A` in `F`, the ring at a maximal ideal
`m` is the localization `A'_m`, which is a discrete valuation ring with fraction field `F`, and
each residue field `κ(m)` is a finite extension of `κ(A)`. -/
noncomputable def semilocalDvrFamily (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Ring.DimensionLEOne A] (F : Type v) [Field F] [Algebra A F]
    [IsFractionRing A F] (hA : maximalIdeal A ≠ ⊥) : SemilocalDvrFamily.{u, v, v} A F where
  Index := MaximalSpectrum ↥(integralClosure A F)
  finite_index := finite_maximalSpectrum_integralClosure A F
  Dvr m := Localization.AtPrime m.asIdeal
  isDiscreteValuationRing m := isDiscreteValuationRing_localization A F hA m.asIdeal
  isLocalHom m := isLocalHom_algebraMap_localization A F m.asIdeal
  algebraFractionField m := localizationAlgebra A F m.asIdeal
  isScalarTower m := isScalarTower_localization' A F m.asIdeal
  isFractionRing m := isFractionRing_localization A F m.asIdeal
  moduleFiniteResidueField m := module_finite_residueField_localization A F m.asIdeal

end Stacks.Normalization
