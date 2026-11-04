module
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute
@[expose] public section

set_option linter.style.show false

/-!
# Flatness and localization

Let `R` be a ring, `S ⊆ R` a multiplicative subset and `M` an `R`-module. The localization
`S⁻¹R` is `R`-flat; an `S⁻¹R`-module is `R`-flat if and only if it is `S⁻¹R`-flat; `M` is flat
if and only if every `M_𝔭` is `R_𝔭`-flat, or every `M_𝔪` is `R_𝔪`-flat. For an `R`-algebra `A`
and an `A`-module `M`, if every `M_𝔮` (`𝔮 ⊆ A` prime, or maximal) is flat over `R_𝔭` with
`𝔭 = R ∩ 𝔮`, then `M` is `R`-flat.

## Main results

* `flat_of_isLocalization`: `S⁻¹R` is a flat `R`-algebra.
* `flat_iff_flat_localization`: for an `S⁻¹R`-module, flatness over `R` is equivalent to
  flatness over `S⁻¹R`.
* `flat_iff_forall_flat_atPrime`: `M` is `R`-flat iff `M_𝔭` is `R_𝔭`-flat for every prime `𝔭`.
* `flat_iff_flat_localizedModule_atMaximal`: `M` is `R`-flat iff `M_𝔪` is `R_𝔪`-flat for every
  maximal ideal `𝔪`.
* `flat_of_flat_localizedModule_maximal`: an `A`-module `M` is `R`-flat if every `M_𝔪` is flat
  over `R_𝔭`, `𝔭 = R ∩ 𝔪`, for `𝔪 ⊆ A` maximal.
* `flat_of_flat_atPrime`: an `A`-module `M` is `R`-flat if every `M_𝔮` is flat over `R_𝔭`,
  `𝔭 = R ∩ 𝔮`, for `𝔮 ⊆ A` prime.
-/

open Module

/-- The localisation `S⁻¹R` is a flat `R`-algebra. -/
@[stacks 00HT "part1", sga "1 IV 1.2" "M = B = A"]
theorem flat_of_isLocalization
    {R : Type*} [CommRing R] (S : Submonoid R)
    (Rs : Type*) [CommRing Rs] [Algebra R Rs] [IsLocalization S Rs] :
    Module.Flat R Rs :=
  IsLocalization.flat Rs S

/-- For an `S⁻¹R`-module `M`, flatness over `R` is equivalent to flatness over `S⁻¹R`. -/
@[stacks 00HT "part2", sga "1 IV 1.2" "(i) 2nd assertion"]
theorem flat_iff_flat_localization
    {R : Type*} [CommRing R] (S : Submonoid R)
    (Rs : Type*) [CommRing Rs] [Algebra R Rs] [IsLocalization S Rs]
    (M : Type*) [AddCommGroup M] [Module R M] [Module Rs M] [IsScalarTower R Rs M] :
    Module.Flat R M ↔ Module.Flat Rs M :=
  (Module.flat_iff_of_isLocalization Rs S M).symm

/-- If `M_𝔭` is flat over `R_𝔭` for a prime `𝔭`, then `M_𝔭` is flat over `R`. -/
private theorem flat_localizedModule_atPrime_of_flat
    {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (P : Ideal R) [P.IsPrime]
    (h : Module.Flat (Localization.AtPrime P) (LocalizedModule.AtPrime P M)) :
    Module.Flat R (LocalizedModule.AtPrime P M) :=
  (Module.flat_iff_of_isLocalization (S := Localization.AtPrime P)
    P.primeCompl (LocalizedModule.AtPrime P M)).mp h

/-- `M` is flat over `R` iff `M_𝔭` is flat over `R_𝔭` for every prime `𝔭` of `R`. -/
@[stacks 00HT "part3", sga "1 IV 1.2" "B = A, primes"]
theorem flat_iff_forall_flat_atPrime
    {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔
      ∀ (P : Ideal R) (_ : P.IsPrime),
        Module.Flat (Localization.AtPrime P) (LocalizedModule.AtPrime P M) := by
  refine ⟨fun _ P _ ↦ Module.Flat.localizedModule (S := P.primeCompl), fun h ↦ ?_⟩
  refine Module.flat_of_localized_maximal M fun P hP ↦ ?_
  have : P.IsPrime := hP.isPrime
  exact flat_localizedModule_atPrime_of_flat M P (h P this)

/-- `M` is flat over `R` iff `M_𝔪` is flat over `R_𝔪` for every maximal ideal `𝔪` of `R`. -/
@[stacks 00HT "part4", sga "1 IV 1.2" "B = A"]
theorem flat_iff_flat_localizedModule_atMaximal
    {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔
      ∀ (m : Ideal R) (_ : m.IsMaximal),
        haveI : m.IsPrime := Ideal.IsMaximal.isPrime ‹_›
        Module.Flat (Localization.AtPrime m) (LocalizedModule.AtPrime m M) := by
  refine ⟨fun _ m hm ↦ ?_, fun h ↦ Module.flat_of_localized_maximal M ?_⟩
  · have : m.IsPrime := hm.isPrime
    exact Module.Flat.localizedModule (S := m.primeCompl)
  · intro m hm
    have : m.IsPrime := hm.isPrime
    exact flat_localizedModule_atPrime_of_flat M m (h m hm)

/-- For a prime `𝔮` of `A` over `𝔭 = R ∩ 𝔮`, with `M_𝔮` an `R_𝔭`-module through
`R_𝔭 → A_𝔮`, the scalar actions `R → R_𝔭 → M_𝔮` form a scalar tower. -/
private lemma part6_scalarTower
    {R : Type*} [CommRing R]
    {A : Type*} [CommRing A] [Algebra R A]
    (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (Q : Ideal A) (hQ : Q.IsPrime) :
    letI : (Q.comap (algebraMap R A)).IsPrime := Ideal.comap_isPrime _ _
    letI : Q.LiesOver (Q.comap (algebraMap R A)) := ⟨rfl⟩
    letI : Algebra (Localization.AtPrime (Q.comap (algebraMap R A)))
                   (Localization.AtPrime Q) :=
      Localization.AtPrime.algebraOfLiesOver _ _
    letI : Module (Localization.AtPrime (Q.comap (algebraMap R A)))
                  (LocalizedModule.AtPrime Q M) :=
      Module.compHom _ (algebraMap _ (Localization.AtPrime Q))
    IsScalarTower R
      (Localization.AtPrime (Q.comap (algebraMap R A)))
      (LocalizedModule.AtPrime Q M) := by
  have : (Q.comap (algebraMap R A)).IsPrime := Ideal.comap_isPrime _ _
  have : Q.LiesOver (Q.comap (algebraMap R A)) := ⟨rfl⟩
  let : Algebra (Localization.AtPrime (Q.comap (algebraMap R A)))
                   (Localization.AtPrime Q) :=
    Localization.AtPrime.algebraOfLiesOver _ _
  let : Module (Localization.AtPrime (Q.comap (algebraMap R A)))
                  (LocalizedModule.AtPrime Q M) :=
    Module.compHom _ (algebraMap _ (Localization.AtPrime Q))
  change IsScalarTower R
      (Localization.AtPrime (Q.comap (algebraMap R A)))
      (LocalizedModule.AtPrime Q M)
  refine IsScalarTower.of_algebraMap_smul fun r x ↦ ?_
  change (algebraMap (Localization.AtPrime (Q.comap (algebraMap R A))) (Localization.AtPrime Q))
        ((algebraMap R (Localization.AtPrime (Q.comap (algebraMap R A)))) r) • x = r • x
  rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime (Q.comap (algebraMap R A)))
        (Localization.AtPrime Q) r, IsScalarTower.algebraMap_smul]

/-- For a maximal ideal `𝔪` of `A` over `𝔭 = R ∩ 𝔪`, if `M_𝔪` is flat over `R_𝔭` then it is
flat over `R`. -/
private lemma flat_R_of_flat_local
    {R : Type*} [CommRing R]
    {A : Type*} [CommRing A] [Algebra R A]
    (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (m : Ideal A) (hm : m.IsMaximal) :
    letI : m.IsPrime := Ideal.IsMaximal.isPrime hm
    letI : (m.comap (algebraMap R A)).IsPrime := Ideal.comap_isPrime _ _
    letI : m.LiesOver (m.comap (algebraMap R A)) := ⟨rfl⟩
    letI : Algebra (Localization.AtPrime (m.comap (algebraMap R A)))
                   (Localization.AtPrime m) :=
      Localization.AtPrime.algebraOfLiesOver _ _
    letI : Module (Localization.AtPrime (m.comap (algebraMap R A)))
                  (LocalizedModule.AtPrime m M) :=
      Module.compHom _ (algebraMap _ (Localization.AtPrime m))
    Module.Flat (Localization.AtPrime (m.comap (algebraMap R A)))
                (LocalizedModule.AtPrime m M) →
    Module.Flat R (LocalizedModule.AtPrime m M) := by
  intro hflat
  have : m.IsPrime := Ideal.IsMaximal.isPrime hm
  have : (m.comap (algebraMap R A)).IsPrime := Ideal.comap_isPrime _ _
  have : m.LiesOver (m.comap (algebraMap R A)) := ⟨rfl⟩
  let : Algebra (Localization.AtPrime (m.comap (algebraMap R A)))
                 (Localization.AtPrime m) :=
    Localization.AtPrime.algebraOfLiesOver _ _
  let : Module (Localization.AtPrime (m.comap (algebraMap R A)))
                (LocalizedModule.AtPrime m M) :=
    Module.compHom _ (algebraMap _ (Localization.AtPrime m))
  have : Module.Flat R (Localization.AtPrime (m.comap (algebraMap R A))) :=
    IsLocalization.flat (Localization.AtPrime (m.comap (algebraMap R A)))
      (m.comap (algebraMap R A)).primeCompl
  have := part6_scalarTower (R := R) M m (Ideal.IsMaximal.isPrime hm)
  exact Module.Flat.trans R (Localization.AtPrime (m.comap (algebraMap R A)))
      (LocalizedModule.AtPrime m M)

/-- If every `M_𝔪` (for `𝔪 ⊆ A` maximal) is flat over `R_𝔭` (with `𝔭 = R ∩ 𝔪`), then `M` is flat
over `R`. -/
@[stacks 00HT "part7_backward", sga "1 IV 1.2" "(ii)"]
theorem flat_of_flat_localizedModule_maximal
    {R : Type*} [CommRing R]
    {A : Type*} [CommRing A] [Algebra R A]
    (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (h : ∀ (m : Ideal A) (_ : m.IsMaximal),
        letI : m.IsPrime := Ideal.IsMaximal.isPrime ‹_›
        letI : (m.comap (algebraMap R A)).IsPrime := Ideal.comap_isPrime _ _
        letI : m.LiesOver (m.comap (algebraMap R A)) := ⟨rfl⟩
        letI : Algebra (Localization.AtPrime (m.comap (algebraMap R A)))
                       (Localization.AtPrime m) :=
          Localization.AtPrime.algebraOfLiesOver _ _
        letI : Module (Localization.AtPrime (m.comap (algebraMap R A)))
                      (LocalizedModule.AtPrime m M) :=
          Module.compHom _ (algebraMap _ (Localization.AtPrime m))
        Module.Flat
          (Localization.AtPrime (m.comap (algebraMap R A)))
          (LocalizedModule.AtPrime m M)) :
    Module.Flat R M := by
  refine Module.flat_of_isLocalized_maximal A M
    (fun P _ ↦ LocalizedModule.AtPrime P M)
    (fun P _ ↦ LocalizedModule.mkLinearMap P.primeCompl M) ?_
  intro m hm
  exact flat_R_of_flat_local M m hm (h m hm)

/-- If every `M_𝔮` (for `𝔮 ⊆ A` prime) is flat over `R_𝔭` (with `𝔭 = 𝔮 ∩ R`), then `M` is flat
over `R`. -/
@[stacks 00HT "part6_backward", sga "1 IV 1.2" "(ii) with all primes"]
theorem flat_of_flat_atPrime
    {R : Type*} [CommRing R]
    {A : Type*} [CommRing A] [Algebra R A]
    (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (h : ∀ (Q : Ideal A) (_ : Q.IsPrime),
        letI : (Q.comap (algebraMap R A)).IsPrime := Ideal.comap_isPrime _ _
        letI : Q.LiesOver (Q.comap (algebraMap R A)) := ⟨rfl⟩
        letI : Algebra (Localization.AtPrime (Q.comap (algebraMap R A)))
                       (Localization.AtPrime Q) :=
          Localization.AtPrime.algebraOfLiesOver _ _
        letI : Module (Localization.AtPrime (Q.comap (algebraMap R A)))
                      (LocalizedModule.AtPrime Q M) :=
          Module.compHom _ (algebraMap _ (Localization.AtPrime Q))
        Module.Flat
          (Localization.AtPrime (Q.comap (algebraMap R A)))
          (LocalizedModule.AtPrime Q M)) :
    Module.Flat R M := by
  refine flat_of_flat_localizedModule_maximal (R := R) (A := A) M ?_
  intro m hm
  exact h m hm.isPrime

