module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral

/-!
# The spectrum of a purely inseparable field extension

For a purely inseparable extension `K/k` of fields the morphism `Spec K ⟶ Spec k` is a
universal homeomorphism: it is integral because `K/k` is algebraic, surjective because both
spectra are single points, and universally injective because a purely inseparable extension
admits at most one `k`-embedding into any field.

## Main results

* `AlgebraicGeometry.universalHomeomorphism_specMap_algebraMap` — the spectrum of a purely
  inseparable field extension is a universal homeomorphism.
* `AlgebraicGeometry.isHomeomorph_pullbackFst_specMap_algebraMap` — consequently every base
  change of it along a scheme over `k` is a homeomorphism on underlying spaces.

## Implementation notes

Universal injectivity is checked through the criterion of Stacks 01S4 that a morphism is
universally injective exactly when it is injective on `L`-points for every field `L`; for
`Spec K ⟶ Spec k` an `L`-point is a ring map out of `K`, and two such agreeing on `k` agree by
`IsPurelyInseparable.injective_comp_algebraMap`.

## References

* [Stacks Project, Tag 04DF](https://stacks.math.columbia.edu/tag/04DF)
* [Stacks Project, Tag 01S4](https://stacks.math.columbia.edu/tag/01S4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The spectrum of a purely inseparable field extension is a universal homeomorphism. -/
instance universalHomeomorphism_specMap_algebraMap (k K : Type u) [Field k] [Field K]
    [Algebra k K] [IsPurelyInseparable k K] :
    UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  rw [universalHomeomorphism_iff_integral_universallyInjective_surjective]
  refine ⟨IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr
    ⟨fun x ↦ IsPurelyInseparable.isIntegral' k x⟩), ?_, ?_⟩
  · apply ((tfae_universallyInjective
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).out 2 1).mp
    intro L _ a b hab
    obtain ⟨a, rfl⟩ := Spec.map_surjective a
    obtain ⟨b, rfl⟩ := Spec.map_surjective b
    refine congrArg Spec.map (CommRingCat.hom_ext ?_)
    exact IsPurelyInseparable.injective_comp_algebraMap k K L <| congrArg CommRingCat.Hom.hom
      (Spec.map_injective (by simpa only [← Spec.map_comp] using hab))
  · exact ⟨fun _ ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩

/-- Base change of the spectrum of a purely inseparable field extension along a scheme over the
base field is a homeomorphism on underlying topological spaces. -/
theorem isHomeomorph_pullbackFst_specMap_algebraMap (k K : Type u) [Field k] [Field K]
    [Algebra k K] [IsPurelyInseparable k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    IsHomeomorph (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base :=
  (universalHomeomorphism_specMap_algebraMap k K).universally_isHomeomorph
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) f
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (IsPullback.of_hasPullback _ _)

end AlgebraicGeometry

end
