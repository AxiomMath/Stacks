module

public import Mathlib.FieldTheory.PurelyInseparable.AdjoinPthRoots
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Testing geometric reducedness after a purely inseparable extension

For a scheme over a field of positive characteristic, geometric reducedness at a point can be
checked after finite purely inseparable extensions. Equivalently, it can be checked after the
single extensions obtained by adjoining all first-order roots or by passing to a perfect
closure.

## Main results

* `AlgebraicGeometry.isGeometricallyReducedAt_tfae` gives the four equivalent tests for
  geometric reducedness at a point.

## Implementation notes

The field denoted `k^{1/p}` in the source is `AdjoinPthRoots k`, and `k^{perf}` is
`perfectClosure k (AlgebraicClosure k)`, the largest purely inseparable extension of `k` inside
an algebraic closure. For a purely inseparable extension the point above `x` is unique;
consequently the local-ring conditions are stated invariantly for every point mapping to `x`,
without making a noncanonical choice of that unique point.

## References

* [Stacks Project, Tag 035Y](https://stacks.math.columbia.edu/tag/035Y)
-/

@[expose] public section

open CategoryTheory Limits CommRingCat

namespace AlgebraicGeometry

open scoped TensorProduct

universe u

/-- **Stacks Project, Tag 035Y.** For a scheme over a field of positive characteristic,
geometric reducedness at a point is equivalent to reducedness of the local rings above that
point after every finite purely inseparable extension, after adjoining all `p`-th roots, or
after passing to a perfect closure. -/
@[stacks 035Y,
  ega "IV 6.7.7" "reduced: b), e), f)",
  ega "IV 4.6.1" "special case",
  ega "IV 4.6.12" "special case"]
public theorem isGeometricallyReducedAt_tfae
    {k : Type u} [Field k] (p : ℕ) [CharP k p] (hp : p ≠ 0)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    [IsGeometricallyReducedAt f x,
      ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
          [IsPurelyInseparable k k'],
        let g : Spec (.of k') ⟶ Spec (.of k) :=
          Spec.map (CommRingCat.ofHom (algebraMap k k'))
        ∀ x' : (pullback f g : Scheme), pullback.fst f g x' = x →
          _root_.IsReduced ((pullback f g).presheaf.stalk x'),
      let g : Spec (.of (AdjoinPthRoots k)) ⟶ Spec (.of k) :=
        Spec.map (CommRingCat.ofHom (algebraMap k (AdjoinPthRoots k)))
      ∀ x' : (pullback f g : Scheme), pullback.fst f g x' = x →
        _root_.IsReduced ((pullback f g).presheaf.stalk x'),
      let g : Spec (.of (perfectClosure k (AlgebraicClosure k))) ⟶ Spec (.of k) :=
        Spec.map (CommRingCat.ofHom
          (algebraMap k (perfectClosure k (AlgebraicClosure k))))
      ∀ x' : (pullback f g : Scheme), pullback.fst f g x' = x →
        _root_.IsReduced ((pullback f g).presheaf.stalk x')].TFAE := by
  have expCharK : ExpChar k p :=
    ExpChar.prime ((CharP.char_is_prime_or_zero k p).resolve_right hp)
  have expCharPerf : ExpChar (perfectClosure k (AlgebraicClosure k)) p :=
    expChar_of_injective_algebraMap
      (algebraMap k (perfectClosure k (AlgebraicClosure k))).injective p
  let algebraKS : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x)) :=
    StructureSheaf.stalkAlgebra k (f.base x)
  let algebraKX : Algebra k (X.presheaf.stalk x) :=
    ((f.stalkMap x).hom.comp
      (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x)))).toAlgebra
  have hring := Algebra.isGeometricallyReduced_tfae k p (X.presheaf.stalk x)
    (perfectClosure k (AlgebraicClosure k)) (AlgebraicClosure k)
  have hgeo := isGeometricallyReducedAt_iff_isGeometricallyReduced_stalk f x
  tfae_have 1 → 2 := fun h K _ _ _ _ => h K
  tfae_have 1 → 3 := fun h => h (AdjoinPthRoots k)
  tfae_have 1 → 4 := fun h => h (perfectClosure k (AlgebraicClosure k))
  tfae_have 2 → 1 := by
    intro h
    apply hgeo.mpr
    apply (hring.out 1 6).mp
    intro K _ _ _ _
    exact isReduced_tensorProduct_of_forall_isReduced_stalk f x (h K)
  tfae_have 3 → 1 := fun h => hgeo.mpr ((hring.out 2 6).mp
    (isReduced_tensorProduct_of_forall_isReduced_stalk f x h))
  tfae_have 4 → 1 := fun h => hgeo.mpr ((hring.out 3 6).mp
    (isReduced_tensorProduct_of_forall_isReduced_stalk f x h))
  tfae_finish

end AlgebraicGeometry
