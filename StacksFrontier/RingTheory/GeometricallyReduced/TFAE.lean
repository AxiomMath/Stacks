module

public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.FieldTheory.IsPerfectClosure
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Lie.OfAssociative

public import StacksFrontier.RingTheory.FormallySmooth.Field
public import StacksFrontier.RingTheory.GeometricallyReduced.SeparableBaseChange
public import StacksFrontier.FieldTheory.TranscendentalSeparable
public import StacksFrontier.RingTheory.Nilpotent.GeometricallyReduced
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Geometric reducedness is detected by purely inseparable base change

Let `k` be a field of exponential characteristic `p` and let `S` be a commutative `k`-algebra. The
following are equivalent: reducedness of `k' ⊗[k] S` for all finite purely inseparable extensions
`k'/k`; reducedness of `k^{1/p} ⊗[k] S`; reducedness of `k^{perf} ⊗[k] S` for a perfect closure
`k^{perf}` of `k`; reducedness of `K ⊗[k] S` for an algebraic closure `K` of `k`; reducedness of
`L ⊗[k] S` for every field extension `L/k`; and `Algebra.IsGeometricallyReduced k S`.

Here `k^{1/p}` is Mathlib's `AdjoinPthRoots k`, the field `k` with the `k`-algebra structure given
by `frobenius k p`; the perfect closure and the algebraic closure are any fields `kperf` and `K`
with `IsPerfectClosure (algebraMap k kperf) p` and `IsAlgClosure k K`; the extensions `k'` and `L`
range over the universe of `k`.

## Main results

* `Algebra.isGeometricallyReduced_tfae`: the six conditions above are equivalent.
* `Stacks.GeometricallyReduced.TestFields.solution`: the six conditions above are equivalent.
* `Stacks.GeometricallyReduced.TestFields.isReduced_tensorProduct_fractionRing_mvPolynomial`: the
  base change of a reduced `k`-algebra to the rational function field
  `FractionRing (MvPolynomial σ k)` is reduced.
* `Stacks.LocalHom.isLocalHom_of_isIntegral`: an integral algebra over a local ring which is itself
  local is a local homomorphism.

## References

* [Stacks 030V](https://stacks.math.columbia.edu/tag/030V)
-/

@[expose] public section

universe u v w w'

namespace Stacks.GeometricallyReduced.TestFields

open scoped TensorProduct
open Stacks.GeometricallyReduced.SeparableBaseChange

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ### Base change along a separable, or separably generated, extension -/

/-- If `R ⊗[k] T` is reduced, then so is `A ⊗[k] T` for every localization `A` of `R`. -/
private theorem isReduced_tensorProduct_of_isLocalization {k T : Type*} {R A : Type w} [Field k]
    [CommRing R] [CommRing A] [CommRing T] [Algebra k R] [Algebra k A] [Algebra k T] [Algebra R A]
    [IsScalarTower k R A] (M : Submonoid R) [IsLocalization M A] (h : IsReduced (R ⊗[k] T)) :
    IsReduced (A ⊗[k] T) := by
  rw [isReduced_congr (Algebra.TensorProduct.cancelBaseChange k R A A T).symm.toRingEquiv]
  exact isReduced_localizationPreserves (Algebra.algebraMapSubmonoid (R ⊗[k] T) M) _ h

/-- The base change of a reduced `k`-algebra `S` to the rational function field
`FractionRing (MvPolynomial σ k)` is reduced. -/
public theorem isReduced_tensorProduct_fractionRing_mvPolynomial (k : Type u) [Field k]
    (σ : Type v) (S : Type w) [CommRing S] [Algebra k S] [IsReduced S] :
    IsReduced (FractionRing (MvPolynomial σ k) ⊗[k] S) := by
  have h : IsReduced (MvPolynomial σ k ⊗[k] S) :=
    isReduced_of_injective
      ((Algebra.TensorProduct.comm k (MvPolynomial σ k) S).trans
        ((MvPolynomial.algebraTensorAlgEquiv k S).restrictScalars k)) (AlgEquiv.injective _)
  exact isReduced_tensorProduct_of_isLocalization (nonZeroDivisors (MvPolynomial σ k)) h

/-- The base change of a reduced `F`-algebra along a separably generated field extension `K/F` is
reduced. -/
@[ega "0 23.1.7" "partial", ega "IV 4.3.5" "special case", ega "IV 4.3.6" "special case"]
private theorem isReduced_tensorProduct_of_isSeparablyGenerated (F : Type u) (K : Type v) [Field F]
    [Field K] [Algebra F K] [Algebra.IsSeparablyGenerated F K] (T : Type w) [CommRing T]
    [Algebra F T] [IsReduced T] : IsReduced (K ⊗[F] T) := by
  obtain ⟨s, hs, hsep⟩ :=
    Algebra.IsSeparablyGenerated.isSeparable (k := F) (K := K)
  have e : FractionRing (MvPolynomial (s : Type v) F) ≃ₐ[F] IntermediateField.adjoin F s :=
    hs.1.aevalEquivField.trans (IntermediateField.equivOfEq (by rw [Subtype.range_coe]))
  have : IsReduced (↥(IntermediateField.adjoin F s) ⊗[F] T) :=
    (isReduced_congr (Algebra.TensorProduct.congr e.symm AlgEquiv.refl).toRingEquiv).2
      (isReduced_tensorProduct_fractionRing_mvPolynomial F (s : Type v) T)
  rw [isReduced_congr (Algebra.TensorProduct.cancelBaseChange F
    ↥(IntermediateField.adjoin F s) K K T).symm.toRingEquiv]
  exact isReduced_tensorProduct_of_isSeparable

/-- For a tower of fields `k → k' → K'` with `K'/k'` separably generated, if `k' ⊗[k] S` is
reduced, then `K' ⊗[k] S` is reduced. -/
private theorem isReduced_tensorProduct_of_isSeparablyGenerated_of_isScalarTower
    {k k' K' S : Type*} [Field k] [Field k'] [Field K'] [CommRing S] [Algebra k S]
    [Algebra k k'] [Algebra k K'] [Algebra k' K'] [IsScalarTower k k' K']
    [Algebra.IsSeparablyGenerated k' K'] (h : IsReduced (k' ⊗[k] S)) :
    IsReduced (K' ⊗[k] S) := by
  rw [isReduced_congr (Algebra.TensorProduct.cancelBaseChange k k' K' K' S).symm.toRingEquiv]
  exact isReduced_tensorProduct_of_isSeparablyGenerated k' K' _

/-! ### Reducedness of base changes from that of special ones -/

/-- If `k' ⊗[k] S` is reduced for every finite purely inseparable extension `k'/k`, then
`L ⊗[k] S` is reduced for every field extension `L/k`. -/
@[ega "IV 4.6.16" "special case", ega "IV 7.3.16" "special case"]
private theorem isReduced_tensorProduct_of_forall_finiteDimensional_isPurelyInseparable
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    (H : ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
      [IsPurelyInseparable k k'], IsReduced (k' ⊗[k] S))
    (L : Type u) [Field L] [Algebra k L] : IsReduced (L ⊗[k] S) := by
  refine isReduced_tensorProduct_of_forall_fg_intermediateField fun F hF ↦ ?_
  have : Algebra.EssFiniteType k ↥F := IntermediateField.essFiniteType_iff.2 hF
  obtain ⟨K', k', -, -, hfin, hpi, hsg⟩ :=
    exists_isPurelyInseparable_and_isSeparablyGenerated_of_essFiniteType k ↥F
      (AlgebraicClosure ↥F)
  exact isReduced_tensorProduct_of_injective_left (IsScalarTower.toAlgHom k ↥F ↥K')
    (algebraMap ↥F ↥K').injective
    (isReduced_tensorProduct_of_isSeparablyGenerated_of_isScalarTower (H ↥k'))

/-- If `k^{1/p} ⊗[k] S` is reduced, then `S` is geometrically reduced over `k`. -/
private theorem isGeometricallyReduced_of_isReduced_tensorProduct_adjoinPthRoots
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S]
    (h : IsReduced (AdjoinPthRoots k ⊗[k] S)) : Algebra.IsGeometricallyReduced k S := by
  have hS : IsReduced S :=
    isReduced_of_injective
      (Algebra.TensorProduct.includeRight : S →ₐ[k] AdjoinPthRoots k ⊗[k] S)
      (Algebra.TensorProduct.includeRight_injective (RingHom.injective _))
  refine Algebra.IsGeometricallyReduced.of_forall_minimalPrimes fun q hq hqmin ↦ ?_
  have hred : IsReduced (Localization.AtPrime q ⊗[k] AdjoinPthRoots k) := by
    exact isReduced_tensorProduct_of_isLocalization q.primeCompl
      ((isReduced_congr (Algebra.TensorProduct.comm k S (AdjoinPthRoots k)).toRingEquiv).2 h)
  let _ : Field (Localization.AtPrime q) :=
    (minimal_prime_reduced_localization_isField S q hqmin).toField
  exact ((Algebra.isSeparableExtension_of_charZero_and_tfae k
    (Localization.AtPrime q)).2.out 2 3).mp hred

/-- For a field `k` of exponential characteristic `p`, a commutative `k`-algebra `S`, a perfect
closure `kperf` and an algebraic closure `K` of `k`, the six conditions of
`Algebra.isGeometricallyReduced_tfae` on `S` are equivalent. -/
public theorem solution
    (k : Type u) [Field k] (p : ℕ) [ExpChar k p] (S : Type v) [CommRing S] [Algebra k S]
    (kperf : Type w) [Field kperf] [Algebra k kperf] [ExpChar kperf p] [PerfectRing kperf p]
    [IsPerfectClosure (algebraMap k kperf) p]
    (K : Type w') [Field K] [Algebra k K] [IsAlgClosure k K] :
    [∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [IsPurelyInseparable k k'], IsReduced (k' ⊗[k] S),
      IsReduced (AdjoinPthRoots k ⊗[k] S),
      IsReduced (kperf ⊗[k] S),
      IsReduced (K ⊗[k] S),
      ∀ (L : Type u) [Field L] [Algebra k L], IsReduced (L ⊗[k] S),
      Algebra.IsGeometricallyReduced k S].TFAE := by
  have : IsPurelyInseparable k kperf := IsPRadical.isPurelyInseparable k kperf p
  tfae_have 1 → 5 := fun H ↦
    isReduced_tensorProduct_of_forall_finiteDimensional_isPurelyInseparable H
  tfae_have 5 → 6 := fun H ↦ (Algebra.isGeometricallyReduced_field_iff ..).2 (H _)
  tfae_have 6 → 1 := fun _ _ _ _ _ _ ↦ inferInstance
  tfae_have 6 → 2 := fun _ ↦ inferInstance
  tfae_have 6 → 3 := fun _ ↦ inferInstance
  tfae_have 6 → 4 := fun _ ↦ inferInstance
  tfae_have 4 → 6 := by
    intro h
    rw [Algebra.isGeometricallyReduced_field_iff]
    exact isReduced_tensorProduct_of_injective_left
      (IsAlgClosure.equiv k (AlgebraicClosure k) K).toAlgHom
      (IsAlgClosure.equiv k (AlgebraicClosure k) K).injective h
  tfae_have 3 → 2 := by
    intro h
    have : PerfectField kperf := PerfectRing.toPerfectField kperf p
    obtain ⟨f⟩ : Nonempty (AdjoinPthRoots k →ₐ[k] kperf) := inferInstance
    exact isReduced_tensorProduct_of_injective_left f f.toRingHom.injective h
  tfae_have 2 → 6 := isGeometricallyReduced_of_isReduced_tensorProduct_adjoinPthRoots
  tfae_finish

end Stacks.GeometricallyReduced.TestFields

@[expose] public section

open scoped TensorProduct

namespace Algebra

/-- Let `k` be a field of exponential characteristic `p` and let `S` be a
commutative `k`-algebra. The following are equivalent:
(1) `k' ⊗[k] S` is reduced for every finite purely inseparable extension `k'/k`;
(2) `k^{1/p} ⊗[k] S` is reduced, where `k^{1/p} = AdjoinPthRoots k`;
(3) `k^{perf} ⊗[k] S` is reduced for a perfect closure `k^{perf}` of `k`;
(4) `K ⊗[k] S` is reduced for an algebraic closure `K` of `k`;
(5) `L ⊗[k] S` is reduced for every field extension `L/k`;
(6) `Algebra.IsGeometricallyReduced k S`. -/
@[stacks 030V "The source's five conditions in its order, with its definition of geometric
  reducedness spelled out as item (5), plus item (6), Mathlib's `Algebra.IsGeometricallyReduced`;
  `k^{1/p}` is `AdjoinPthRoots k`, and the perfect and algebraic closures are taken abstractly, as
  `IsPerfectClosure` and `IsAlgClosure`."]
public theorem isGeometricallyReduced_tfae
    (k : Type u) [Field k] (p : ℕ) [ExpChar k p] (S : Type v) [CommRing S] [Algebra k S]
    (kperf : Type w) [Field kperf] [Algebra k kperf] [ExpChar kperf p] [PerfectRing kperf p]
    [IsPerfectClosure (algebraMap k kperf) p]
    (K : Type w') [Field K] [Algebra k K] [IsAlgClosure k K] :
    [∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [IsPurelyInseparable k k'], IsReduced (k' ⊗[k] S),
      IsReduced (AdjoinPthRoots k ⊗[k] S),
      IsReduced (kperf ⊗[k] S),
      IsReduced (K ⊗[k] S),
      ∀ (L : Type u) [Field L] [Algebra k L], IsReduced (L ⊗[k] S),
      IsGeometricallyReduced k S].TFAE :=
    Stacks.GeometricallyReduced.TestFields.solution k p S kperf K

end Algebra

namespace Stacks.LocalHom

/-- An integral algebra over a local ring which is itself local is a local homomorphism. -/
public lemma isLocalHom_of_isIntegral
    (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [Algebra.IsIntegral R S] : IsLocalHom (algebraMap R S) := by
  exact ((IsLocalRing.local_hom_TFAE (algebraMap R S)).out 5 1).mp <|
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) _)

end Stacks.LocalHom

end
