module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Nagata
public import StacksFrontier.RingTheory.Nagata.Japanese

/-!
# Universally Japanese schemes under locally finite type morphisms

The source of a locally finite type morphism to a universally Japanese scheme is universally
Japanese.

## Main results

* `AlgebraicGeometry.isUniversallyJapaneseScheme_of_locallyOfFiniteType`
  establishes preservation of the universally Japanese property under locally finite type
  morphisms.

## Implementation notes

The morphism is locally of finite type in the sense of Mathlib's
`AlgebraicGeometry.LocallyOfFiniteType`. Universally Japanese schemes are expressed using the
predicate `AlgebraicGeometry.IsUniversallyJapaneseScheme`.

## References

* [Stacks Project, Tag 035A](https://stacks.math.columbia.edu/tag/035A)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- **Stacks Project, Tag 035A (universally Japanese case).** The source of a locally finite type
morphism to a universally Japanese scheme is universally Japanese. -/
@[stacks 035A "universally_japanese", ega "IV 7.7.2" "finite type stability"]
public theorem isUniversallyJapaneseScheme_of_locallyOfFiniteType {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (hS : IsUniversallyJapaneseScheme S) :
    IsUniversallyJapaneseScheme X := by
  intro x
  obtain ⟨U, hxU, hU⟩ := hS (f.base x)
  obtain ⟨V, hVaff, hxV, hVsub⟩ :=
    exists_isAffineOpen_mem_and_subset (U := f ⁻¹ᵁ U.1) (by simpa using hxU)
  refine ⟨⟨V, hVaff⟩, hxV, ?_⟩
  let : Algebra Γ(S, U.1) Γ(X, V) := (f.appLE U.1 V hVsub).hom.toAlgebra
  let : Algebra.FiniteType Γ(S, U.1) Γ(X, V) :=
    LocallyOfFiniteType.finiteType_appLE f U.2 hVaff hVsub
  have hA := isUniversallyJapanese_of_isEssentiallyOfFiniteType (Γ(S, U.1)) (Γ(X, V))
    (by intro T _ _ _ _ L _ _ _ _ _; exact (hU.japanese T).finite L)
    ⟨Γ(X, V), inferInstance, inferInstance, inferInstance,
      IsUnit.submonoid (Γ(X, V)), inferInstance, ⟨inferInstance, inferInstance⟩⟩
  constructor
  intro T _ _ _ _
  constructor
  intro L _ _ _ _ _
  exact hA T L

end AlgebraicGeometry

end
