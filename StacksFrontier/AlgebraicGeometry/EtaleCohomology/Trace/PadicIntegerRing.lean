module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DedekindDomain.PID
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# The ring of integers of a finite extension of `ℚ_ℓ`

For a finite extension `E` of `ℚ_ℓ`, the integral closure `O_E` of `ℤ_ℓ` in `E` is a principal
ideal domain (a Dedekind domain with finitely many maximal ideals, all over the maximal ideal of
the discrete valuation ring `ℤ_ℓ`), finite and free over `ℤ_ℓ`, and `E` is its localization at
the nonzero elements of `ℤ_ℓ`: a `ℤ_ℓ`-basis of `O_E` is a `ℚ_ℓ`-basis of `E`. All names are in
the namespace `Stacks.EtaleCohomology`.

## Main definitions

* `padicIntAlgebraOfRat`: the `ℤ_ℓ`-algebra structure of `E`.
* `padicIntegerRingBasis`: a `ℤ_ℓ`-basis of `O_E` indexed by `Fin [E : ℚ_ℓ]`.
* `padicIntegerRingBasisRat`: the same basis, as a `ℚ_ℓ`-basis of `E`.

## Main results

* `isPrincipalIdealRing_padicIntegerRing`: `O_E` is a principal ideal domain.
* `padicIntegerRingBasisRat_apply`: `padicIntegerRingBasisRat` is the image of
  `padicIntegerRingBasis` in `E`.
-/

@[expose] public noncomputable section

open Module

namespace Stacks.EtaleCohomology

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra ℚ_[ℓ] E]

/-- The `ℤ_ℓ`-algebra structure of a `ℚ_ℓ`-algebra, through `ℤ_ℓ ⊆ ℚ_ℓ`. -/
public abbrev padicIntAlgebraOfRat : Algebra ℤ_[ℓ] E :=
  ((algebraMap ℚ_[ℓ] E).comp (algebraMap ℤ_[ℓ] ℚ_[ℓ])).toAlgebra

attribute [local instance] padicIntAlgebraOfRat

/-- `ℤ_ℓ`, `ℚ_ℓ` and `E` form a scalar tower for `padicIntAlgebraOfRat`. -/
public instance isScalarTower_padicIntAlgebraOfRat : IsScalarTower ℤ_[ℓ] ℚ_[ℓ] E :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

variable [FiniteDimensional ℚ_[ℓ] E]

/-- **`O_E` is a principal ideal domain.** -/
public theorem isPrincipalIdealRing_padicIntegerRing :
    IsPrincipalIdealRing (integralClosure ℤ_[ℓ] E) := by
  have : FaithfulSMul ℤ_[ℓ] E := by
    rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq ℤ_[ℓ] ℚ_[ℓ] E]
    exact (algebraMap ℚ_[ℓ] E).injective.comp (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ])
  have : FaithfulSMul ℤ_[ℓ] (integralClosure ℤ_[ℓ] E) := inferInstance
  have : Module.Finite ℤ_[ℓ] (integralClosure ℤ_[ℓ] E) :=
    IsIntegralClosure.finite ℤ_[ℓ] ℚ_[ℓ] E (integralClosure ℤ_[ℓ] E)
  have : IsDedekindDomain (integralClosure ℤ_[ℓ] E) :=
    IsIntegralClosure.isDedekindDomain ℤ_[ℓ] ℚ_[ℓ] E (integralClosure ℤ_[ℓ] E)
  refine IsPrincipalIdealRing.of_finite_maximals ?_
  apply (Algebra.QuasiFinite.finite_primesOver (S := integralClosure ℤ_[ℓ] E)
    (IsLocalRing.maximalIdeal ℤ_[ℓ])).subset
  intro Q hQ
  have : Q.IsMaximal := hQ
  exact ⟨inferInstance, ⟨(IsLocalRing.eq_maximalIdeal inferInstance).symm⟩⟩

/-- `O_E` is a finite `ℤ_ℓ`-module. -/
public instance finite_padicIntegerRing : Module.Finite ℤ_[ℓ] (integralClosure ℤ_[ℓ] E) :=
  IsIntegralClosure.finite ℤ_[ℓ] ℚ_[ℓ] E (integralClosure ℤ_[ℓ] E)

/-- `O_E` is a free `ℤ_ℓ`-module. -/
public instance free_padicIntegerRing : Module.Free ℤ_[ℓ] (integralClosure ℤ_[ℓ] E) := by
  have : Module.IsTorsionFree ℤ_[ℓ] (integralClosure ℤ_[ℓ] E) := by
    have : FaithfulSMul ℤ_[ℓ] E := by
      rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq ℤ_[ℓ] ℚ_[ℓ] E]
      exact (algebraMap ℚ_[ℓ] E).injective.comp (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ])
    exact IsIntegralClosure.isTorsionFree ℤ_[ℓ] E
  exact Module.free_of_finite_type_torsion_free'

/-- `E` is the localization of `O_E` at the nonzero elements of `ℤ_ℓ`. -/
public instance isLocalization_padicIntegerRing :
    IsLocalization (Algebra.algebraMapSubmonoid (integralClosure ℤ_[ℓ] E) (nonZeroDivisors ℤ_[ℓ]))
      E :=
  IsIntegralClosure.isLocalization ℤ_[ℓ] ℚ_[ℓ] E (integralClosure ℤ_[ℓ] E)

/-- The basis of `O_E` over `ℤ_ℓ` chosen by `Module.Free`, as a basis of `E` over `ℚ_ℓ`. -/
public abbrev padicIntegerRingChosenBasisRat :
    Basis (Module.Free.ChooseBasisIndex ℤ_[ℓ] (integralClosure ℤ_[ℓ] E)) ℚ_[ℓ] E :=
  (Module.Free.chooseBasis ℤ_[ℓ] (integralClosure ℤ_[ℓ] E)).localizationLocalization ℚ_[ℓ]
    (nonZeroDivisors ℤ_[ℓ]) E

/-- The rank of `O_E` over `ℤ_ℓ` is the degree of `E` over `ℚ_ℓ`. -/
public theorem card_chooseBasisIndex_padicIntegerRing :
    Fintype.card (Module.Free.ChooseBasisIndex ℤ_[ℓ] (integralClosure ℤ_[ℓ] E)) =
      Module.finrank ℚ_[ℓ] E :=
  (Module.finrank_eq_card_basis (padicIntegerRingChosenBasisRat ℓ E)).symm

/-- **A basis of `O_E` over `ℤ_ℓ` indexed by `Fin [E : ℚ_ℓ]`.** -/
public def padicIntegerRingBasis :
    Basis (Fin (Module.finrank ℚ_[ℓ] E)) ℤ_[ℓ] (integralClosure ℤ_[ℓ] E) :=
  (Module.Free.chooseBasis ℤ_[ℓ] (integralClosure ℤ_[ℓ] E)).reindex
    (Fintype.equivFinOfCardEq (card_chooseBasisIndex_padicIntegerRing ℓ E))

/-- The basis of `O_E`, as a basis of `E` over `ℚ_ℓ`. -/
public def padicIntegerRingBasisRat : Basis (Fin (Module.finrank ℚ_[ℓ] E)) ℚ_[ℓ] E :=
  (padicIntegerRingBasis ℓ E).localizationLocalization ℚ_[ℓ] (nonZeroDivisors ℤ_[ℓ]) E

/-- The `i`-th vector of `padicIntegerRingBasisRat` is the `i`-th vector of
`padicIntegerRingBasis`, as an element of `E`. -/
public theorem padicIntegerRingBasisRat_apply (i : Fin (Module.finrank ℚ_[ℓ] E)) :
    padicIntegerRingBasisRat ℓ E i = (padicIntegerRingBasis ℓ E i : E) :=
  Basis.localizationLocalization_apply _ _ _ _ _

/-- The coordinates of an element of `O_E` in `padicIntegerRingBasisRat` are its coordinates in
`padicIntegerRingBasis`, as elements of `ℚ_ℓ`. -/
public theorem padicIntegerRingBasisRat_repr (x : integralClosure ℤ_[ℓ] E)
    (i : Fin (Module.finrank ℚ_[ℓ] E)) :
    (padicIntegerRingBasisRat ℓ E).repr (x : E) i =
      ((padicIntegerRingBasis ℓ E).repr x i : ℚ_[ℓ]) :=
  Basis.localizationLocalization_repr_algebraMap _ _ _ _ _ _

end Stacks.EtaleCohomology

end
