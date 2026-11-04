module

public import StacksFrontier.RingTheory.Flat.HenselianFlattening

/-!
# Flat descent of the local flattening condition

In the situation of Stacks Tag 05MK — a local homomorphism of local rings `A → B` together with
a `B`-module `M`, tested against the category `C` of local `A`-algebras with local structure map
— the functor `F_lf` of Stacks Tag 05MM takes the same value on a local `A`-algebra `R` and on a
flat local `A`-algebra `T` over it. This is part (1) of Stacks Tag 05MN.

One direction is base-change stability of the flatness condition, which is
`Module.FlatAtPointSituation.ConditionOn.of_isLocalHom`. The other is descent along `R → T`,
and it is the case `I' = m_R`, `I'' = m_T` of Stacks Tag 05LS
(`Module.IsFlatAtPrimesOver.of_baseChange`): the two hypotheses of that lemma become trivial
here because the only prime of a local ring containing its maximal ideal is the maximal ideal
itself. Surjectivity of `V(m_T) → V(m_R)` is then `IsLocalRing.maximalIdeal_comap`, and the
localization of `T` at the complement of `m_T` is `T`, which is flat over `R` by hypothesis.

## Main results

* `Module.FlatAtPointSituation.flat_localization_of_maximalIdeal_le`: a localization of a local
  ring `T` at (the complement of) a prime containing `m_T` is flat over any base over which `T`
  is flat; the prime is forced to be `m_T` and the localization is `T` itself.
* `Module.FlatAtPointSituation.ConditionOn.of_flat`: descent of the flatness condition of
  Stacks Tag 05ML along a flat local homomorphism of local `A`-algebras.
* `Module.FlatAtPointSituation.conditionOn_iff_of_flat`,
  `Module.FlatAtPointSituation.condition_iff_of_flat` and
  `Module.FlatAtPointSituation.flatAtPointFunctor_obj_eq_of_flat`: **Stacks Tag 05MN part (1)**,
  unbundled, read on a morphism of the category `C`, and read on the functor `F_lf` itself.

## Implementation notes

The unbundled form takes the source and the target in independent universes, as
`Module.FlatAtPointSituation.ConditionOn.of_isLocalHom` does; the categorical form fixes them to
the universe of the objects of `LocalAlgCat`. Flatness of a morphism of `LocalAlgCat` is
expressed by `RingHom.Flat` on the underlying ring homomorphism, rather than by a `Module.Flat`
instance, because the `Algebra` structure witnessing it is the one carried by the morphism and so
is not available before the morphism is given.

## References

* [Stacks Project, Tag 05MN](https://stacks.math.columbia.edu/tag/05MN)
* [Stacks Project, Tag 05LS](https://stacks.math.columbia.edu/tag/05LS)
* [Stacks Project, Tag 05MK](https://stacks.math.columbia.edu/tag/05MK)
* [Stacks Project, Tag 05ML](https://stacks.math.columbia.edu/tag/05ML)
-/

@[expose] public section

open CategoryTheory IsLocalRing

open scoped TensorProduct

universe u v w x y

namespace Module.FlatAtPointSituation

/-- A prime of a local ring `T` containing the maximal ideal is the maximal ideal, so the
localization of `T` at its complement is `T` itself and is therefore flat over any ring over
which `T` is flat. This is the second hypothesis of Stacks Tag 05LS in the local case. -/
theorem flat_localization_of_maximalIdeal_le {R : Type x} {T : Type y} [CommRing R] [CommRing T]
    [IsLocalRing T] [Algebra R T] [Module.Flat R T] {p : Ideal T} [p.IsPrime]
    (hp : maximalIdeal T ≤ p) :
    Module.Flat R (Localization p.primeCompl) := by
  obtain rfl : p = maximalIdeal T := le_antisymm (le_maximalIdeal_of_isPrime p) hp
  have e : T ≃ₐ[T] Localization (maximalIdeal T).primeCompl :=
    IsLocalization.atUnits T (maximalIdeal T).primeCompl fun _ hx ↦ notMem_maximalIdeal.mp hx
  exact Module.Flat.of_linearEquiv (e.toLinearEquiv.restrictScalars R).symm

/-- **Descent of the flatness condition of Stacks Tag 05ML along a flat local homomorphism.** If
`R → T` is a flat local homomorphism of local `A`-algebras and the condition holds over `T`, then
it holds over `R`.

This is Stacks Tag 05LS, `Module.IsFlatAtPrimesOver.of_baseChange`, at `I' = m_R` and
`I'' = m_T`: the only prime of `T` containing `m_T` is `m_T`, whose contraction is `m_R` because
`R → T` is local, and the localization of `T` at the complement of `m_T` is `T`. -/
theorem ConditionOn.of_flat {S : FlatAtPointSituation.{u, v, w}} (R : Type x) (T : Type y)
    [CommRing R] [IsLocalRing R] [Algebra S.A R] [CommRing T] [IsLocalRing T] [Algebra S.A T]
    [Algebra R T] [IsScalarTower S.A R T] [IsLocalHom (algebraMap R T)] [Module.Flat R T]
    (h : S.ConditionOn T) :
    S.ConditionOn R :=
  Module.IsFlatAtPrimesOver.of_baseChange _ (maximalIdeal R) (maximalIdeal T)
    (map_maximalIdeal_le (algebraMap R T))
    (fun p' hp' hle ↦
      have _ : p'.IsPrime := hp'
      ⟨maximalIdeal T, (maximalIdeal.isMaximal T).isPrime, le_rfl, by
        rw [maximalIdeal_comap]
        exact (le_antisymm (le_maximalIdeal_of_isPrime p') hle).symm⟩)
    (fun _ _ hp ↦ flat_localization_of_maximalIdeal_le hp) h

/-- **Stacks Project, Tag 05MN part (1).** The flatness condition of Stacks Tag 05ML takes the
same value on a local `A`-algebra `R` and on a flat local `A`-algebra `T` over it; equivalently,
the functor `F_lf` of Stacks Tag 05MM is unchanged along a flat morphism of the category `C`.

The forward implication is base-change stability,
`Module.FlatAtPointSituation.ConditionOn.of_isLocalHom`, and does not use flatness; the backward
implication is `Module.FlatAtPointSituation.ConditionOn.of_flat`. -/
theorem conditionOn_iff_of_flat {S : FlatAtPointSituation.{u, v, w}} (R : Type x) (T : Type y)
    [CommRing R] [IsLocalRing R] [Algebra S.A R] [CommRing T] [IsLocalRing T] [Algebra S.A T]
    [Algebra R T] [IsScalarTower S.A R T] [IsLocalHom (algebraMap R T)] [Module.Flat R T] :
    S.ConditionOn R ↔ S.ConditionOn T :=
  ⟨ConditionOn.of_isLocalHom R T, ConditionOn.of_flat R T⟩

/-- **Stacks Project, Tag 05MN part (1)**, read on a morphism of the category `C` of local
`A`-algebras of Stacks Tag 05MK: if `f : R ⟶ T` is flat then `F_lf(R) = F_lf(T)`, both being
determined by the flatness condition of Stacks Tag 05ML. -/
@[stacks 05MN "flat_base_change"]
theorem condition_iff_of_flat (S : FlatAtPointSituation.{u, v, w}) {R T : LocalAlgCat.{u, x} S.A}
    (f : R ⟶ T) (hf : f.hom.toRingHom.Flat) :
    S.Condition R ↔ S.Condition T := by
  let _ : Algebra (R : Type x) (T : Type x) := f.hom.toRingHom.toAlgebra
  have _ : IsScalarTower S.A R T := IsScalarTower.of_algebraMap_eq fun a ↦ (f.hom.commutes a).symm
  have _ : IsLocalHom (algebraMap (R : Type x) (T : Type x)) := f.isLocal
  have _ : Module.Flat (R : Type x) (T : Type x) := hf
  exact conditionOn_iff_of_flat (S := S) R T

/-- **Stacks Project, Tag 05MN part (1)**, in the shape the source states it: the functor `F_lf`
of Stacks Tag 05MM takes the same value at the two ends of a flat morphism of the category `C`.

The values are `PLift` of the flatness condition of Stacks Tag 05ML, so this is
`Module.FlatAtPointSituation.condition_iff_of_flat` read through `propext`. -/
@[stacks 05MN "flat_base_change"]
theorem flatAtPointFunctor_obj_eq_of_flat (S : FlatAtPointSituation.{u, v, w})
    {R T : LocalAlgCat.{u, x} S.A} (f : R ⟶ T) (hf : f.hom.toRingHom.Flat) :
    S.flatAtPointFunctor.obj R = S.flatAtPointFunctor.obj T :=
  congrArg PLift (propext (S.condition_iff_of_flat f hf))

end FlatAtPointSituation

end Module

end
