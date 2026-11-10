module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Length
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.Basic
public import StacksFrontier.AlgebraicGeometry.SemilocalFibre.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Parameters
public import StacksFrontier.RingTheory.Length.SemilocalDecomposition
public import StacksFrontier.RingTheory.Localization.Glueing.RingHomGluing.Away
import StacksFrontier.RingTheory.Length.SemiLocal
public import StacksCore.Tactic.StacksAttribute

/-!
# Preparing nonzerodivisors for the tame symbol: definitions

Finitely many nonzerodivisors in a one-dimensional Noetherian local ring can be made, after a
finite modification supported at the maximal ideal, into unit multiples of powers of one common
element at every maximal ideal of the modification. This file defines the data of such a
preparation and the two ring-theoretic inputs of its construction, and proves the first facts
about it; the construction itself is in
`StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.Preparation.Construction`.

## Main definitions

* `AlgebraicGeometry.TameSymbolPreparation` packages the finite modification, the common local
  elements, and all the factorizations.
* `AlgebraicGeometry.PreparedTameSymbolExtension` packages the extension ring together with its
  `TameSymbolPreparation`.
* `AlgebraicGeometry.RingHomGluingAtMaximalIdeals` and
  `AlgebraicGeometry.FiniteExtensionPreparingTwoNonzerodivisors` name the two ring-theoretic
  inputs the construction consumes, so that they can be supplied as hypotheses.

## Main results

* `AlgebraicGeometry.TameSymbolPreparation.finite_maximalSpectrum`,
  `AlgebraicGeometry.TameSymbolPreparation.isLocalHom` and
  `AlgebraicGeometry.TameSymbolPreparation.finiteDimensional_residueField` supply the instances
  needed to evaluate the tame-symbol formula on any preparation.
* `AlgebraicGeometry.TameSymbolPreparation.parameter_mem_maximal` shows that the local parameters
  are nonunits whenever the prepared family is not entirely made of units.

The file also proves, as private lemmas for the construction, that a family with at most one
nonunit is prepared without any extension, that an integral extension of a one-dimensional local
ring has local rings of dimension one at its maximal ideals, and that finite extensions of a
local ring are local at their maximal ideals.

## Implementation notes

The finite extension `A ⊆ B` is represented by an injective algebra map with `B` finite as an
`A`-module. The assertion that a power of the maximal ideal annihilates `B/A` is written without
choosing a quotient: that power times `B` is contained in the range of the algebra map. At a
maximal ideal `q` of `B`, the ring `B_q` is Mathlib's `Localization.AtPrime q`; the units and
exponents are retained as data so that the tame symbol can use them directly. The chosen
extension is bundled with its ring and algebra structures, so its carrier and preparation data
are available by projection without making a second choice of witnesses.

For a preparation `P`, the three instances required by the tame-symbol formula can be installed,
in order, with `let := P.finite_maximalSpectrum`, `let := P.isLocalHom`, and
`let := P.finiteDimensional_residueField`. They follow from module finiteness alone.

A local parameter is only required to be regular. A unit parameter forces every prepared element
to be a unit, since the map to the localization is local; so the nonunit conclusion for the family
is a theorem rather than a further field of the preparation.

The unit parts of the factorizations are units **of the localizations** `B_q`, not of the base
ring `A`. That is what the construction yields, and it is weaker than a factorization whose unit
parts come from `A`.

Two ring-theoretic inputs are taken as explicit hypotheses rather than proved here, each named by
a `Prop`-valued definition stating it in full, and each used exactly once:
`RingHomGluingAtMaximalIdeals` is the glueing of ring maps over the localizations at finitely many
maximal ideals, and `FiniteExtensionPreparingTwoNonzerodivisors` produces a finite extension in
which two nonzerodivisors acquire a common factor with comaximal cofactors. Both are stated with
all universes equal, which is the instance this development consumes.

## References

* [Stacks Project, Tag 0EAG](https://stacks.math.columbia.edu/tag/0EAG)
-/

@[expose] public section

open IsLocalRing

universe u v

namespace AlgebraicGeometry

/-- **The glueing of ring maps over the localizations at finitely many maximal ideals.** Ring maps
out of the localizations of a Noetherian ring at finitely many pairwise distinct maximal ideals,
each with kernel and cokernel killed by a power of the corresponding maximal ideal, glue to a
single ring map out of the base whose kernel and cokernel are killed by a power of the
intersection, which localizes to the given maps, and which inherits finiteness, injectivity and
surjectivity from them. All universes are taken equal, which is the instance consumed below. -/
def RingHomGluingAtMaximalIdeals : Prop :=
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Type u} [Finite I]
    (m : I → Ideal A) [∀ i, (m i).IsMaximal] (B : I → Type u) [∀ i, CommRing (B i)],
    Pairwise (fun i j ↦ m i ≠ m j) →
    ∀ f : ∀ i, Localization.AtPrime (m i) →+* B i,
      (∀ i, Stacks.RingHomGluing.KernelIsKilledByIdealPower (f i)
        ((m i).map (algebraMap A (Localization.AtPrime (m i))))) →
      (∀ i, Stacks.RingHomGluing.CokernelIsKilledByIdealPower (f i)
        ((m i).map (algebraMap A (Localization.AtPrime (m i))))) →
      ∃ (B' : Type u) (_ : CommRing B') (g : A →+* B'),
        (∀ i, ∃ gᵢ : B' →+* B i,
          gᵢ.comp g = (f i).comp (algebraMap A (Localization.AtPrime (m i))) ∧
          (Submonoid.map g (m i).primeCompl).IsLocalizationMap gᵢ) ∧
        Stacks.RingHomGluing.KernelIsKilledByIdealPower g (⨅ i, m i) ∧
        Stacks.RingHomGluing.CokernelIsKilledByIdealPower g (⨅ i, m i) ∧
        ((∀ i, (f i).Finite) → g.Finite) ∧
        ((∀ i, Function.Injective (f i)) → Function.Injective g) ∧
        ((∀ i, Function.Surjective (f i)) → Function.Surjective g)

/-- **A finite extension preparing two nonzerodivisors.** Over a one-dimensional Noetherian local
ring, two nonzerodivisors acquire a common nonzerodivisor factor in a finite ring extension whose
quotient by the base is annihilated by a power of the maximal ideal, the two remaining factors
generating the unit ideal. -/
def FiniteExtensionPreparingTwoNonzerodivisors : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
    ringKrullDim R = 1 → ∀ a b : R, a ∈ nonZeroDivisors R → b ∈ nonZeroDivisors R →
      ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
        Module.Finite R S ∧
        Function.Injective (algebraMap R S) ∧
        (∃ n : ℕ, maximalIdeal R ^ n ≤
          Module.annihilator R (S ⧸ (Algebra.linearMap R S).range)) ∧
        ∃ t a' b' : S,
          t ∈ nonZeroDivisors S ∧
          a' ∈ nonZeroDivisors S ∧
          b' ∈ nonZeroDivisors S ∧
          algebraMap R S a = t * a' ∧
          algebraMap R S b = t * b' ∧
          Ideal.span ({a', b'} : Set S) = ⊤

/-- A simultaneous local power factorization of a family of elements after a
finite modification supported at the maximal ideal. -/
structure TameSymbolPreparation {A : Type u} [CommRing A] [IsLocalRing A]
    {r : ℕ} (a : Fin r → A) (B : Type v) [CommRing B] [Algebra A B] where
  /-- The modification is finite over the original ring. -/
  finite : Module.Finite A B
  /-- The structure map realizes the original ring as a subring. -/
  algebraMap_injective : Function.Injective (algebraMap A B)
  /-- A power of the maximal ideal annihilates the quotient `B/A`. -/
  quotient_annihilated_by_maximalIdeal_power :
    ∃ n : ℕ, maximalIdeal A ^ n • (⊤ : Submodule A B) ≤
      LinearMap.range (Algebra.linearMap A B)
  /-- The common nonzerodivisor in the localization at a maximal ideal. -/
  parameter (q : Ideal B) [q.IsMaximal] : Localization.AtPrime q
  /-- Every chosen local parameter is a nonzerodivisor. -/
  parameter_isRegular (q : Ideal B) [q.IsMaximal] : IsRegular (parameter q)
  /-- The unit appearing in the factorization of each original element. -/
  factorUnit (q : Ideal B) [q.IsMaximal] : Fin r → (Localization.AtPrime q)ˣ
  /-- The exponent appearing in the factorization of each original element. -/
  exponent (q : Ideal B) [q.IsMaximal] : Fin r → ℕ
  /-- Each original element is a unit times a power of the common parameter. -/
  factorization (q : Ideal B) [q.IsMaximal] (i : Fin r) :
    algebraMap B (Localization.AtPrime q) (algebraMap A B (a i)) =
      (factorUnit q i : Localization.AtPrime q) * parameter q ^ exponent q i

namespace TameSymbolPreparation

variable {A : Type u} {B : Type v} [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] {r : ℕ} {a : Fin r → A}
    (P : TameSymbolPreparation a B)

include P

/-- A finite preparation over a local ring has only finitely many maximal ideals. -/
theorem finite_maximalSpectrum : Finite (MaximalSpectrum B) := by
  let := P.finite
  have hfin := Algebra.QuasiFinite.finite_primesOver (S := B) (maximalIdeal A)
  let f : MaximalSpectrum B → (maximalIdeal A).primesOver B := fun q ↦
    ⟨q.asIdeal, q.isMaximal.isPrime, ⟨(eq_maximalIdeal
      (inferInstance : (q.asIdeal.under A).IsMaximal)).symm⟩⟩
  let := hfin.to_subtype
  exact Finite.of_injective f fun q q' h ↦ MaximalSpectrum.ext (congrArg Subtype.val h)

/-- Every localization of a finite preparation at a maximal ideal is local over `A`. -/
theorem isLocalHom (q : MaximalSpectrum B) :
    IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) :=
  have := P.finite
  Stacks.Length.isLocalHom_algebraMap_localization q

/-- The local residue fields of a finite preparation are finite over the base residue field.
The local-map instance may be supplied by `P.isLocalHom`. -/
theorem finiteDimensional_residueField (q : MaximalSpectrum B)
    [IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal))] :
    FiniteDimensional (ResidueField A) (ResidueField (Localization.AtPrime q.asIdeal)) := by
  let := P.finite
  have : Module.Finite A q.asIdeal.ResidueField := Module.Finite.trans B _
  exact Module.Finite.of_restrictScalars_finite A _ _

/-- If the prepared family contains a nonunit, every common local parameter lies in
the maximal ideal. No extra condition on the preparation is needed. -/
theorem parameter_mem_maximal (hunit : ¬ ∀ i, IsUnit (a i))
    (q : Ideal B) [q.IsMaximal] :
    P.parameter q ∈ maximalIdeal (Localization.AtPrime q) := by
  let := P.isLocalHom ⟨q, inferInstance⟩
  change ¬ IsUnit (P.parameter q)
  refine fun h => hunit fun i =>
    isUnit_of_map_unit (algebraMap A (Localization.AtPrime q)) _ ?_
  rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime q), P.factorization q i]
  exact (P.factorUnit q i).isUnit.mul (h.pow _)

end TameSymbolPreparation

private theorem exists_tameSymbolPreparation_of_power_factorization
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {r : ℕ} (a : Fin r → A) (p : A) (hp : IsRegular p)
    (v : Fin r → Aˣ) (e : Fin r → ℕ)
    (h : ∀ i, a i = (v i : A) * p ^ e i) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
      Nonempty (TameSymbolPreparation a B) := by
  refine ⟨A, inferInstance, inferInstance, ⟨{
    finite := inferInstance
    algebraMap_injective := ?_
    quotient_annihilated_by_maximalIdeal_power := ?_
    parameter := fun q _ => algebraMap A (Localization.AtPrime q) p
    parameter_isRegular := ?_
    factorUnit := fun q _ i => Units.map (algebraMap A (Localization.AtPrime q)).toMonoidHom (v i)
    exponent := fun _ _ => e
    factorization := ?_ }⟩⟩
  · simpa using (Function.injective_id : Function.Injective (id : A → A))
  · refine ⟨0, ?_⟩; intro x hx; exact ⟨x, by simp⟩
  · intro q hq
    apply isRegular_iff_mem_nonZeroDivisors.mpr
    apply IsLocalization.map_nonZeroDivisors_le (Ideal.primeCompl q)
      (Localization.AtPrime q)
    exact ⟨p, hp.mem_nonZeroDivisors, rfl⟩
  · intro q hq i
    simp [h i]

private theorem exists_tameSymbolPreparation_of_one_nonunit
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {r : ℕ} (a : Fin r → A) (ha : ∀ i, IsRegular (a i))
    (k : Fin r) (h : ∀ i, i ≠ k → IsUnit (a i)) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
      Nonempty (TameSymbolPreparation a B) := by
  classical
  let v : Fin r → Aˣ := fun i => if hi : i = k then 1 else (h i hi).unit
  let e : Fin r → ℕ := fun i => if i = k then 1 else 0
  apply exists_tameSymbolPreparation_of_power_factorization a (a k) (ha k) v e
  intro i
  by_cases hi : i = k
  · subst i
    simp [v, e]
  · simp [v, e, hi, IsUnit.unit_spec]

private theorem ringKrullDim_le_of_integral
    {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] :
    ringKrullDim B ≤ ringKrullDim A := by
  unfold ringKrullDim
  let f : PrimeSpectrum B → PrimeSpectrum A :=
    PrimeSpectrum.comap (algebraMap A B)
  have hmono : Monotone f := by
    intro x y hxy
    change Ideal.comap (algebraMap A B) x.asIdeal ≤
      Ideal.comap (algebraMap A B) y.asIdeal
    exact Ideal.comap_mono hxy
  have hfiber (z : PrimeSpectrum A) :
      Order.krullDim (f ⁻¹' {z}) ≤ (0 : WithBot ℕ∞) := by
    rw [Order.krullDim_nonpos_iff_forall_isMax]
    intro x y hxy
    by_contra hnot
    have hle : x.1.asIdeal ≤ y.1.asIdeal := hxy
    have hne : x.1.asIdeal ≠ y.1.asIdeal := fun heq =>
      hnot (le_of_eq (Subtype.ext (PrimeSpectrum.ext heq)).symm)
    have hlt : x.1.asIdeal < y.1.asIdeal := lt_of_le_of_ne hle hne
    have hcomap := Ideal.IsIntegral.under_lt_under (R := A) hlt
    have heq : Ideal.comap (algebraMap A B) x.1.asIdeal =
        Ideal.comap (algebraMap A B) y.1.asIdeal := by
      have hxy' : f x.1 = f y.1 := x.2.trans y.2.symm
      exact congrArg PrimeSpectrum.asIdeal hxy'
    exact hcomap.ne heq
  have h := Order.krullDim_le_of_krullDim_preimage_le' (m := 0) f hmono hfiber
  simpa using h

private theorem local_dimension_one_of_integral
    {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [Algebra A B] [Algebra.IsIntegral A B]
    (hdim : ringKrullDim A = 1) {a : A}
    (ham : a ∈ maximalIdeal A)
    (ha : IsRegular (algebraMap A B a))
    (q : Ideal B) [q.IsMaximal] :
    ringKrullDim (Localization.AtPrime q) = 1 := by
  have hqunder : (q.under A).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal q
  have hqeq : q.under A = maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal hqunder
  have haq : algebraMap A B a ∈ q := by
    change a ∈ q.under A
    rw [hqeq]
    exact ham
  have hspan : Ideal.span {algebraMap A B a} ≤ q :=
    (Ideal.span_singleton_le_iff_mem q).mpr haq
  have hlo : (1 : ℕ∞) ≤ q.height :=
    (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      ha.mem_nonZeroDivisors).trans (Ideal.height_mono hspan)
  have hhi : (q.height : WithBot ℕ∞) ≤ (1 : WithBot ℕ∞) := by
    calc
      (q.height : WithBot ℕ∞) ≤ ringKrullDim B :=
        q.height_le_ringKrullDim_of_isPrime
      _ ≤ ringKrullDim A := ringKrullDim_le_of_integral
      _ = 1 := hdim
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)]
  exact le_antisymm hhi (WithBot.coe_mono hlo)

private theorem isLocalHom_atPrime_of_module_finite
    {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B]
    (q : MaximalSpectrum B) :
    IsLocalHom (algebraMap A (Localization.AtPrime q.asIdeal)) :=
  Stacks.Length.isLocalHom_algebraMap_localization q

private theorem isLocalHom_of_module_finite_local
    {A S : Type*} [CommRing A] [IsLocalRing A]
    [CommRing S] [IsLocalRing S] [Algebra A S] [Module.Finite A S] :
    IsLocalHom (algebraMap A S) :=
  ((local_hom_TFAE (algebraMap A S)).out 5 1).mp
    (eq_maximalIdeal (inferInstance : ((maximalIdeal S).under A).IsMaximal))

/-- A finite extension together with all of its tame-symbol preparation data. -/
structure PreparedTameSymbolExtension {A : Type u} [CommRing A] [IsLocalRing A]
    {r : ℕ} (a : Fin r → A) where
  /-- The finite extension, bundled with its ring and algebra structures. -/
  extension : CommAlgCat.{u} A
  /-- The local parameters and simultaneous factorizations on the extension. -/
  preparation : TameSymbolPreparation a extension

end AlgebraicGeometry
