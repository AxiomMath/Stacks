module

public import StacksFrontier.FieldTheory.PurelyInseparable.BaseChange
public import StacksFrontier.RingTheory.GeometricallyRegular.Defs
public import StacksFrontier.RingTheory.RegularRing.Defs
public import StacksFrontier.RingTheory.RegularRing.FaithfullyFlatDescent
public import StacksFrontier.RingTheory.Smooth.Field
public import StacksFrontier.RingTheory.Smooth.RegularRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Regularity of base changes is detected by the finite purely inseparable extensions

Let `k` be a field and `A` a `k`-algebra. Then `K ⊗[k] A` is a regular ring for every finitely
generated field extension `K/k` if and only if `k' ⊗[k] A` is a regular ring for every finite
purely inseparable extension `k'/k`. This equivalence makes Definition 0382 (*geometrically
regular*) well posed.

## Main results

* `IsRegularRing.of_isLocalization`: a localization of a regular ring is regular.
* `Stacks.GeometricallyRegular.Criterion.solution` and
  `Algebra.forall_isRegularRing_tensorProduct_essFiniteType_iff_finite_isPurelyInseparable`: the
  equivalence above.
* `Algebra.isRegularRing_tensorProduct_of_isGeometricallyRegular`: for a geometrically regular
  `k`-algebra `R`, the ring `K ⊗[k] R` is regular for every essentially finite type field extension
  `K/k`, in any universe.

## Implementation notes

Regularity is Mathlib's `IsRegularRing`, which is Definition 00OD (Noetherian, with all
localizations at primes regular local rings). "Finitely generated field extension" is
`Algebra.EssFiniteType k K` (`IntermediateField.fg_top_iff`), and "finite purely inseparable" is
`Module.Finite k K` together with `IsPurelyInseparable k K`.

The source's hypothesis that `A` be Noetherian is not assumed: it is implied by either side of the
equivalence, since `A ≃ₐ[k] k ⊗[k] A` (`Algebra.TensorProduct.lid`) and `IsRegularRing` contains
`IsNoetherianRing`.

The extension fields range over a single universe `w`, the same on both sides and independent of
the universe of `k`. Taking `w := u` gives the source's statement in full, since every finitely
generated extension of `k : Type u` has a model in `Type u` and regularity transports along ring
equivalences (`IsRegularRing.of_ringEquiv`).

## References

* [Stacks Project, Tag 0381](https://stacks.math.columbia.edu/tag/0381)
* [Stacks Project, Tag 00OD](https://stacks.math.columbia.edu/tag/00OD)
* [Stacks Project, Tag 030R](https://stacks.math.columbia.edu/tag/030R)
* [Stacks Project, Tag 037X](https://stacks.math.columbia.edu/tag/037X)
* [Stacks Project, Tag 07NF](https://stacks.math.columbia.edu/tag/07NF)
* [Stacks Project, Tag 07NG](https://stacks.math.columbia.edu/tag/07NG)
-/

@[expose] public section

universe u v w

@[expose] public section

/-- **A localization of a regular ring is a regular ring.** If `R` is a regular ring and `S` is a
localization of `R` at a submonoid `M`, then `S` is a regular ring. -/
public theorem IsRegularRing.of_isLocalization {R : Type u} [CommRing R] [IsRegularRing R]
    (M : Submonoid R) (S : Type v) [CommRing S] [Algebra R S] [IsLocalization M S] :
    IsRegularRing S := by
  have : IsNoetherianRing S := IsLocalization.isNoetherianRing M S inferInstance
  rw [isRegularRing_iff]
  intro q hq
  have : IsLocalization.AtPrime (Localization.AtPrime q) (q.comap (algebraMap R S)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (T := Localization.AtPrime q) q
  exact _root_.IsRegularRing.isRegularLocalRing_of_isLocalization (q.comap (algebraMap R S))
    (Localization.AtPrime q)

namespace Stacks.GeometricallyRegular.Criterion

open scoped TensorProduct

/-- Let `C` be a regular `R`-algebra, let `B` be a smooth `R`-algebra and let `L` be a localization
of `B` at a submonoid `M`. Then `C ⊗[R] L` is a regular ring. -/
@[ega "0 19.6.5" "special case",
  ega "0 22.6.7" "special case",
  ega "IV 17.15.1" "necessity",
  ega "IV 6.7.4.1" "special case",
  ega "IV 7.5.3" "(iv), special case", sga "3 XI 1.2" "(i)"]
private theorem isRegularRing_tensorProduct_of_smooth_of_isLocalization (R : Type u) (C : Type v)
    (B : Type w) (L : Type w) [CommRing R] [CommRing C] [CommRing B] [CommRing L] [Algebra R C]
    [Algebra R B] [Algebra R L] [Algebra B L] [IsScalarTower R B L] [Algebra.Smooth R B]
    [IsRegularRing C] (M : Submonoid B) [IsLocalization M L] : IsRegularRing (C ⊗[R] L) := by
  have : Algebra.Smooth C (C ⊗[R] B) := Algebra.Smooth.baseChange R B C
  have : IsRegularRing (C ⊗[R] B) := Algebra.isRegularRing_of_smooth C (C ⊗[R] B)
  let F : (C ⊗[R] B) →ₐ[R] (C ⊗[R] L) :=
    Algebra.TensorProduct.map (AlgHom.id R C) (IsScalarTower.toAlgHom R B L)
  let _algTensor : Algebra (C ⊗[R] B) (C ⊗[R] L) := F.toRingHom.toAlgebra
  have : IsScalarTower C (C ⊗[R] B) (C ⊗[R] L) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change _ = F _
    simp [F]
  have : IsLocalization (M.map (Algebra.TensorProduct.includeRight (R := R) (A := C)))
      (C ⊗[R] L) :=
    IsLocalization.tensorProduct_tensorProduct_right R C M L
      (by ext r; simp [RingHom.algebraMap_toAlgebra, F])
  exact _root_.IsRegularRing.of_isLocalization
    (M.map (Algebra.TensorProduct.includeRight (R := R) (A := C))) (C ⊗[R] L)

/-- For field extensions `F/k` and `K'/F`, the ring `(F ⊗[k] A) ⊗[F] K'` is regular if and only
if `K' ⊗[k] A` is. -/
private theorem isRegularRing_tensorProduct_cancel_iff (k : Type u) (A : Type v)
    (F K' : Type w) [Field k] [CommRing A] [Algebra k A] [Field F] [Field K'] [Algebra k F]
    [Algebra k K'] [Algebra F K'] [IsScalarTower k F K'] :
    IsRegularRing ((F ⊗[k] A) ⊗[F] K') ↔ IsRegularRing (K' ⊗[k] A) :=
  let e := ((Algebra.TensorProduct.comm F (F ⊗[k] A) K').trans
    (Algebra.TensorProduct.cancelBaseChange k F F K' A)).toRingEquiv
  ⟨fun _ => .of_ringEquiv e, fun _ => .of_ringEquiv e.symm⟩

/-- Let `A` be an algebra over a field `k` and let
```
K  →  K'
↑     ↑
k  →  k'
```
be a diagram of field extensions of `k` with `K'/k'` separable (Definition 030O(2)) and finitely
generated. If `k' ⊗[k] A` is a regular ring, then so is `K ⊗[k] A`. -/
@[ega "IV 4.3.5" "special case", ega "IV 6.7.4.1" "special case"]
private theorem isRegularRing_tensorProduct_of_isSeparableExtension (k : Type u) (A : Type v)
    (K k' K' : Type w) [Field k] [CommRing A] [Algebra k A] [Field K] [Field k'] [Field K']
    [Algebra k K] [Algebra k k'] [Algebra k K'] [Algebra K K'] [Algebra k' K']
    [IsScalarTower k K K'] [IsScalarTower k k' K'] [Algebra.EssFiniteType k' K']
    [IsRegularRing (k' ⊗[k] A)] (hsep : Algebra.IsSeparableExtension k' K') :
    IsRegularRing (K ⊗[k] A) := by
  obtain ⟨B, _, _⟩ := ((Algebra.IsSeparableExtension.tfae_exists_smooth k' K').out 1 2).mp hsep
  have : IsRegularRing ((K ⊗[k] A) ⊗[K] K') :=
    (isRegularRing_tensorProduct_cancel_iff k A K K').mpr
      ((isRegularRing_tensorProduct_cancel_iff k A k' K').mp
        (isRegularRing_tensorProduct_of_smooth_of_isLocalization k' (k' ⊗[k] A) ↥B K'
          (nonZeroDivisors ↥B)))
  exact _root_.IsRegularRing.of_faithfullyFlat ((K ⊗[k] A) ⊗[K] K')

end Stacks.GeometricallyRegular.Criterion

end

@[expose] public section

open scoped TensorProduct

namespace Algebra

/-- **Regularity of all base changes to finitely generated field extensions is detected by the
finite purely inseparable ones.** Let `k` be a field and `A` a `k`-algebra. Then `K ⊗[k] A` is a
regular ring (Definition 00OD) for every finitely generated field extension `K/k` if and only if
`k' ⊗[k] A` is a regular ring for every finite purely inseparable extension `k'/k`. -/
@[stacks 0381 "Regular ring is Definition 00OD, that is Mathlib's `IsRegularRing`, which already
contains Noetherianness; a finitely generated field extension is `Algebra.EssFiniteType`
(`IntermediateField.fg_top_iff`) and a finite purely inseparable one is `Module.Finite` together
with `IsPurelyInseparable`. The source's hypothesis that `A` be Noetherian is not assumed: it is
implied by either side, since `A ≃ₐ[k] k ⊗[k] A`. The extension fields range over a single free
universe, `w := u` giving the source's statement in full. See the module docstring.",
  ega "0 22.5.8" "b) ⇔ b')", ega "IV 6.7.7" "(b) ⇔ (c), special case"]
public theorem forall_isRegularRing_tensorProduct_essFiniteType_iff_finite_isPurelyInseparable
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A] :
    (∀ (K : Type w) [Field K] [Algebra k K] [Algebra.EssFiniteType k K],
        IsRegularRing (K ⊗[k] A)) ↔
      ∀ (K : Type w) [Field K] [Algebra k K] [Module.Finite k K] [IsPurelyInseparable k K],
        IsRegularRing (K ⊗[k] A) := by
  refine ⟨fun h K _ _ _ _ => h K, fun h K _ _ _ => ?_⟩
  obtain ⟨K', k', _, -, _, _, hsep, -, -, -⟩ :=
    exists_isPurelyInseparable_and_isSeparableExtension_of_essFiniteType k K (AlgebraicClosure K)
  have : IsRegularRing (↥k' ⊗[k] A) := h ↥k'
  have : Algebra.EssFiniteType K ↥K' := inferInstance
  have : Algebra.EssFiniteType k ↥K' := Algebra.EssFiniteType.comp k K ↥K'
  have : Algebra.EssFiniteType ↥k' ↥K' := Algebra.EssFiniteType.of_comp k ↥k' ↥K'
  exact Stacks.GeometricallyRegular.Criterion.isRegularRing_tensorProduct_of_isSeparableExtension
    k A K ↥k' ↥K' hsep

/-- Geometric regularity can be tested after an essentially finite type field extension in any
universe. -/
public theorem isRegularRing_tensorProduct_of_isGeometricallyRegular
    (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R]
    [Algebra.IsGeometricallyRegular k R]
    (K : Type w) [Field K] [Algebra k K] [Algebra.EssFiniteType k K] :
    IsRegularRing (K ⊗[k] R) := by
  refine (Algebra.forall_isRegularRing_tensorProduct_essFiniteType_iff_finite_isPurelyInseparable
    k R).mpr (fun L _ _ _ _ => ?_) K
  have : Algebra.IsAlgebraic k L := Algebra.IsAlgebraic.of_finite k L
  let f : L →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
  have : Module.Finite k ↥f.fieldRange := Module.Finite.equiv f.equivFieldRange.toLinearEquiv
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.congr f.equivFieldRange.symm AlgEquiv.refl).toRingEquiv

end Algebra

namespace Stacks.GeometricallyRegular.Criterion

/-- For a field `k` and a `k`-algebra `A`, the ring `K ⊗[k] A` is regular for every essentially
finite type field extension `K/k` if and only if it is regular for every finite purely inseparable
extension `K/k`. -/
public alias solution :=
  Algebra.forall_isRegularRing_tensorProduct_essFiniteType_iff_finite_isPurelyInseparable

end Stacks.GeometricallyRegular.Criterion

end
