module

public import Mathlib.RingTheory.Regular.RegularSequence
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

/-!
# Faithfully flat base change preserves and reflects regular sequences

Let `R` be a commutative ring, `M` an `R`-module, `S` a faithfully flat `R`-algebra and `N` the
base change of `M` to `S`. A sequence `x₁, …, x_r` of elements of `R` is `M`-regular if and only if
its image in `S` is `N`-regular. Here an `M`-regular sequence is one where `x_i` acts injectively
on `M/(x₁, …, x_{i-1})M` for every `i` and `M/(x₁, …, x_r)M ≠ 0`, which is Mathlib's
`RingTheory.Sequence.IsRegular`.

## Main results

* `RingTheory.Sequence.isRegular_map_algebraMap_iff_of_faithfullyFlat_of_isBaseChange`: over a
  faithfully flat algebra, a sequence is regular on a module if and only if its image is regular
  on the base change of that module.

## Implementation notes

The base change is taken abstractly, as an `S`-module `N` together with an `R`-linear
`f : M →ₗ[R] N` satisfying `IsBaseChange S f`, rather than as the module `M ⊗[R] S`. For a flat
local homomorphism of local rings, `Module.FaithfullyFlat.of_flat_of_isLocalHom` supplies the
faithful flatness hypothesis.

## References

* [Stacks Project, Tag 00LM](https://stacks.math.columbia.edu/tag/00LM)
-/

@[expose] public section

namespace Stacks.RegularSequence.FlatBaseChange

open Module RingTheory.Sequence TensorProduct

section BaseChange

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- Acting by `x : R` on `S ⊗[R] M` is tensoring the action of `x` on `M` with `S`. -/
private theorem lTensor_lsmul (x : R) :
    LinearMap.lTensor S (LinearMap.lsmul R M x) = LinearMap.lsmul R (S ⊗[R] M) x := by
  ext s m; simp

/-- If `N` is a base change of `M` to `S`, then `N/(algebraMap R S x)N` is a base change of
`M/xM` to `S`. -/
private theorem exists_isBaseChange_quotSMulTop {f : M →ₗ[R] N} (hf : IsBaseChange S f) (x : R) :
    ∃ g : QuotSMulTop x M →ₗ[R] QuotSMulTop (algebraMap R S x) N, IsBaseChange S g :=
  let e := (QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop x M S).symm ≪≫ₗ
    QuotSMulTop.congr (algebraMap R S x) hf.equiv
  ⟨e.toLinearMap.restrictScalars R ∘ₗ TensorProduct.mk R S (QuotSMulTop x M) 1,
    IsBaseChange.of_equiv e fun _ ↦ by simp⟩

end BaseChange

section FaithfullyFlat

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- Over a faithfully flat algebra `S`, an element `x : R` acts injectively on `S ⊗[R] M` if and
only if it acts injectively on `M`. -/
@[ega "0 15.1.13" "special case", ega "0 15.1.14" "special case"]
private theorem isSMulRegular_tensorProduct_iff (x : R) :
    IsSMulRegular (S ⊗[R] M) x ↔ IsSMulRegular M x := by
  have h := Module.FaithfullyFlat.lTensor_injective_iff_injective R S (LinearMap.lsmul R M x)
  rwa [lTensor_lsmul] at h

/-- Over a faithfully flat algebra `S`, an element `x : R` acts injectively on an `R`-module `M`
if and only if its image acts injectively on a base change of `M` to `S`. The `←` direction is
`IsSMulRegular.of_flat_of_isBaseChange`. -/
@[ega "0 15.1.13" "special case", ega "0 15.1.14" "special case"]
private theorem isSMulRegular_algebraMap_iff_of_faithfullyFlat_of_isBaseChange
    {f : M →ₗ[R] N} (hf : IsBaseChange S f) (x : R) :
    IsSMulRegular N (algebraMap R S x) ↔ IsSMulRegular M x := by
  rw [isSMulRegular_map (M := N) (algebraMap R S) (algebraMap_smul S x),
    ← (hf.equiv.restrictScalars R).isSMulRegular_congr x]
  exact isSMulRegular_tensorProduct_iff x

/-- Over a faithfully flat algebra `S`, a sequence `rs` in `R` is weakly `M`-regular if and only
if its image in `S` is weakly regular on a base change of `M` to `S`. The `←` direction is
`RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange`. -/
@[ega "0 15.1.14", sga "3 VIIB 5.5.2" "partial"]
private theorem isWeaklyRegular_map_algebraMap_iff_of_faithfullyFlat_of_isBaseChange
    {f : M →ₗ[R] N} (hf : IsBaseChange S f) (rs : List R) :
    IsWeaklyRegular N (rs.map (algebraMap R S)) ↔ IsWeaklyRegular M rs := by
  induction rs generalizing M N with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨g, hg⟩ := exists_isBaseChange_quotSMulTop hf x
    simp only [List.map_cons, isWeaklyRegular_cons_iff]
    exact and_congr (isSMulRegular_algebraMap_iff_of_faithfullyFlat_of_isBaseChange hf x) (ih hg)

end FaithfullyFlat

/-- Over a faithfully flat algebra `S`, a sequence `rs` in `R` is `M`-regular if and only if its
image in `S` is regular on a base change of `M` to `S`. -/
public theorem solution {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module S N] [IsScalarTower R S N] {f : M →ₗ[R] N} (hf : IsBaseChange S f) (rs : List R) :
    IsRegular N (rs.map (algebraMap R S)) ↔ IsRegular M rs := by
  rw [isRegular_iff, isRegular_iff, ← Ideal.map_ofList]
  exact and_congr (isWeaklyRegular_map_algebraMap_iff_of_faithfullyFlat_of_isBaseChange hf rs)
    (ne_comm.trans ((hf.map_smul_top_ne_top_iff_of_faithfullyFlat R M _).trans ne_comm))

end Stacks.RegularSequence.FlatBaseChange

namespace RingTheory.Sequence

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- Let `R` be a commutative ring, `M` an `R`-module, `S` a faithfully flat `R`-algebra and
`f : M →ₗ[R] N` a base change of `M` to `S`. Then a sequence `rs` in `R` is `M`-regular if and
only if its image in `S` is `N`-regular. -/
@[stacks 00LM,
  ega "0 15.1.14" "converse (ff case)",
  ega "0 15.2.5" "affine, faithfully flat",
  ega "0 15.1.13" "special case", sga "3 VIIB 5.5.2" "special case"]
public theorem isRegular_map_algebraMap_iff_of_faithfullyFlat_of_isBaseChange
    {f : M →ₗ[R] N} (hf : IsBaseChange S f) (rs : List R) :
    IsRegular N (rs.map (algebraMap R S)) ↔ IsRegular M rs :=
  Stacks.RegularSequence.FlatBaseChange.solution hf rs

end RingTheory.Sequence
