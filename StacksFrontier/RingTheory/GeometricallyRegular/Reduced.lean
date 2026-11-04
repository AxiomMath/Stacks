module

public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.RingTheory.LocalProperties.Reduced
public import StacksFrontier.RingTheory.GeometricallyReduced.TFAE
public import StacksFrontier.RingTheory.GeometricallyRegular.Defs
public import StacksFrontier.RingTheory.RegularLocalRing.Basic

@[expose] public section

open scoped TensorProduct

universe u v

/-!
# A geometrically regular algebra over a field is geometrically reduced

Geometric regularity of a `k`-algebra `R` asks that `K ⊗[k] R` be a regular ring for every
finitely generated field extension `K/k`; geometric reducedness asks that `L ⊗[k] R` be reduced
for every field extension `L/k`. The first implies the second.

## Main results

* `Algebra.isGeometricallyReduced_of_isGeometricallyRegular`: a geometrically regular algebra over
  a field is geometrically reduced.
-/

namespace Algebra

/-- A geometrically regular algebra over a field is geometrically reduced. -/
public theorem isGeometricallyReduced_of_isGeometricallyRegular
    (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R]
    [Algebra.IsGeometricallyRegular k R] : Algebra.IsGeometricallyReduced k R := by
  apply ((Algebra.isGeometricallyReduced_tfae k (ringExpChar k) R
    (perfectClosure k (AlgebraicClosure k)) (AlgebraicClosure k)).out 1 6).mp
  intro L _ _ _ _
  exact isReduced_ofLocalizationMaximal _ fun p hp ↦ by
    have : p.IsPrime := hp.isPrime
    have : IsDomain (Localization.AtPrime p) := IsRegularLocalRing.isDomain _
    infer_instance

end Algebra

end
