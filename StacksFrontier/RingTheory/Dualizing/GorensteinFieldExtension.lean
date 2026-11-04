module

public import Mathlib.RingTheory.Localization.Submodule
public import StacksFrontier.RingTheory.CompleteIntersection.FieldGlobalToRingMap
public import StacksFrontier.RingTheory.CompleteIntersection.Relative
public import StacksFrontier.RingTheory.Dualizing.GorensteinLocalCompleteIntersection
public import StacksFrontier.RingTheory.Dualizing.GorensteinLocalization
public import StacksFrontier.RingTheory.EssFiniteType.TensorLocalization

/-!
# Gorensteinness after a finitely generated extension of the ground field

Let `k` be a field, let `R` be a Noetherian `k`-algebra and let `K/k` be a field extension which
is finitely generated as a field extension. This file proves that if `R` is Gorenstein then so is
`R ⊗_k K`.

## Main results

* `Dualizing.isGorensteinRing_tensorProduct_of_essFiniteType_fieldExtension` — Tag 0BJN,
  clause (A): a Noetherian Gorenstein algebra over a field stays Gorenstein after base change
  along a finitely generated field extension of the ground field.

This file proves clause (A) only. Clauses (B), (C), (D) and (E) of Tag 0BJN, and the conjunction
of all five that carries the tag whole, are in
`StacksFrontier/RingTheory/Dualizing/GorensteinFormalFibreAxioms.lean`.

## The argument

Write `K` as a localization of a `k`-subalgebra `C ⊆ K` which is a global complete intersection
over `k`, in such a way that `R ⊗_k K` is a localization of `R ⊗_k C`
(`Stacks.EssFiniteType.exists_isGlobalCompleteIntersectionOver_isLocalization_tensorProduct`).
A global complete intersection over a field is a relative global complete intersection over that
field, and that property is stable under base change along `k → R`, so `R → R ⊗_k C` is a
relative global complete intersection, hence a local complete intersection ring map. Tag 0DWA
then makes `R ⊗_k C` Gorenstein, and `R ⊗_k K` is Gorenstein because Gorensteinness passes to
localizations.

## Implementation notes

Noetherianness of `R ⊗_k K` is not a hypothesis but a consequence: `K` is essentially of finite
type over `k`, hence `R ⊗_k K` is essentially of finite type over the Noetherian ring `R`. Since
`Dualizing.IsGorensteinRing` cannot be spelled without it, the instance is supplied by a `letI`
inside the statement, as in `Dualizing.isGorensteinRing_of_isLocalization`.

The three rings `k`, `R` and `K` live in three independent universes. The intermediate ring
`R ⊗_k C` shares the universe `max v w` of `R ⊗_k K`, because `C` is a subalgebra of `K`, so the
single-universe hypothesis of `Dualizing.isGorensteinRing_of_isLocalization` is met without
collapsing any universe of the statement.

Neither the `C`-algebra structure on `R ⊗_k C` nor the `(R ⊗_k C)`-algebra structure on `R ⊗_k K`
is a global instance: the first is `Algebra.TensorProduct.rightAlgebra`, made a local instance
below, and the second is existentially quantified in
`Stacks.EssFiniteType.exists_isGlobalCompleteIntersectionOver_isLocalization_tensorProduct`.

## References

* [Stacks Project, Tag 0BJN](https://stacks.math.columbia.edu/tag/0BJN)
* [Stacks Project, Tag 0DWA](https://stacks.math.columbia.edu/tag/0DWA)
* [Stacks Project, Tag 00SS](https://stacks.math.columbia.edu/tag/00SS)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Dualizing

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **Stacks Project, Tag 0BJN, clause (A).** Let `k` be a field, `R` a Noetherian `k`-algebra and
`K/k` an extension of fields which is finitely generated as a field extension. If `R` is
Gorenstein, then `R ⊗_k K` is Gorenstein.

The extension `K/k` is a localization of a global complete intersection `C` over `k`; base
changing `C` along `k → R` gives a relative global complete intersection `R → R ⊗_k C`, so
`R ⊗_k C` is Gorenstein by Tag 0DWA, and `R ⊗_k K` is a localization of `R ⊗_k C`. -/
@[stacks 0BJN "gorenstein_field_extension"]
public theorem isGorensteinRing_tensorProduct_of_essFiniteType_fieldExtension
    {k : Type u} {R : Type v} {K : Type w}
    [Field k] [CommRing R] [Field K] [Algebra k R] [Algebra k K]
    [IsNoetherianRing R] [Algebra.EssFiniteType k K]
    (hR : IsGorensteinRing R) :
    letI : IsNoetherianRing (R ⊗[k] K) :=
      Algebra.EssFiniteType.isNoetherianRing R (R ⊗[k] K)
    IsGorensteinRing (R ⊗[k] K) := by
  let : IsNoetherianRing (R ⊗[k] K) := Algebra.EssFiniteType.isNoetherianRing R (R ⊗[k] K)
  obtain ⟨C, M, _, hC, _, _⟩ :=
    Stacks.EssFiniteType.exists_isGlobalCompleteIntersectionOver_isLocalization_tensorProduct
      k K R
  have : Algebra.IsRelativeGlobalCompleteIntersection k C :=
    Algebra.IsRelativeGlobalCompleteIntersection.of_isGlobalCompleteIntersectionOver k C hC
  have : Algebra.IsRelativeGlobalCompleteIntersection R (R ⊗[k] C) :=
    Algebra.IsRelativeGlobalCompleteIntersection.baseChange k C R (R ⊗[k] C)
  have hlci : RingHom.IsLocalCompleteIntersection (algebraMap R (R ⊗[k] C)) :=
    RingHom.IsLocalCompleteIntersection.of_isRelativeGlobalCompleteIntersection
  have : Algebra.FiniteType R (R ⊗[k] C) := RingHom.finiteType_algebraMap.mp hlci.1
  have : IsNoetherianRing (R ⊗[k] C) := Algebra.FiniteType.isNoetherianRing R (R ⊗[k] C)
  have hGC : IsGorensteinRing (R ⊗[k] C) :=
    isGorensteinRing_of_isLocalCompleteIntersection (algebraMap R (R ⊗[k] C)) hlci hR
  exact isGorensteinRing_of_isLocalization hGC
    (Algebra.algebraMapSubmonoid (R ⊗[k] C) M) (R ⊗[k] K)

end Dualizing

end
