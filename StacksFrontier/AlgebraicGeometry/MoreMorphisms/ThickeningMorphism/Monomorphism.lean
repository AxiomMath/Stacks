module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Unramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Differentials

/-!
# Relative differentials and monomorphisms across a cartesian morphism of thickenings

Let

```
X --f--→ Y
|        |
i        j
↓        ↓
X' -f'-→ Y'
```

be a morphism of thickenings of schemes identifying `X` with `Y ×_{Y'} X'`, in which `f` and
`f'` are locally of finite type. Then the sheaf of relative differentials `Ω_{X/Y}` vanishes
exactly when `Ω_{X'/Y'}` does, and `f` is a monomorphism exactly when `f'` is.

## Main results

* `Stacks.Thickenings.CartesianFiniteTypeMorphism.isZero_relativeDifferentials_iff`:
  **Stacks 0BPG**, part (4).
* `Stacks.Thickenings.CartesianFiniteTypeMorphism.mono_iff`: **Stacks 0BPG**, part (6).

## Implementation notes

For a morphism locally of finite type, the vanishing of the sheaf of relative differentials is
unramifiedness (Tag 02G5), so part (4) is part (5) of the same tag,
`Stacks.Thickenings.CartesianFiniteTypeMorphism.unramified_iff`, read through
`AlgebraicGeometry.unramified_iff_locallyOfFiniteType_and_isZero_relativeDifferentials`. The
source instead proves part (4) by Nakayama's lemma and deduces part (5) from it; in this library
part (5) is proved by the fibrewise criterion, so the order is reversed.

For part (6), a monomorphism base changes to a monomorphism. Conversely, if `f` is a
monomorphism then it is unramified (its diagonal is an isomorphism), hence so is `f'` by part
(5), and the diagonal `Δ_{X'/Y'}` is an open immersion. It is also surjective: the map
`X ×_Y X ⟶ X' ×_{Y'} X'` induced by the two thickenings is surjective because its range is cut
out by the ranges of `i` in both factors (`j` being a monomorphism), and it carries the
diagonal of `X`, which is surjective, to the diagonal of `X'`. A surjective open immersion is
an isomorphism, so `f'` is a monomorphism. This replaces the source's argument through the
conormal sheaf of the diagonal.

## References

* [Stacks Project, Tag 0BPG](https://stacks.math.columbia.edu/tag/0BPG)
* [Stacks Project, Tag 02G5](https://stacks.math.columbia.edu/tag/02G5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings.CartesianFiniteTypeMorphism

/-- **Stacks 0BPG, part (4).** In a cartesian morphism of thickenings whose two component
morphisms are locally of finite type, the sheaf of relative differentials `Ω_{X/Y}` is zero if
and only if `Ω_{X'/Y'}` is zero. -/
@[stacks 0BPG "vanishing_differentials"]
theorem isZero_relativeDifferentials_iff (S : CartesianFiniteTypeMorphism.{u}) :
    IsZero S.f.relativeDifferentials ↔ IsZero S.f'.relativeDifferentials := by
  have h := S.unramified_iff
  rw [unramified_iff_locallyOfFiniteType_and_isZero_relativeDifferentials,
    unramified_iff_locallyOfFiniteType_and_isZero_relativeDifferentials] at h
  exact ⟨fun hf ↦ (h.mp ⟨inferInstance, hf⟩).2, fun hf ↦ (h.mpr ⟨inferInstance, hf⟩).2⟩

/-- If the morphism `f` between the closed subschemes of a cartesian, locally finite type
morphism of thickenings is a monomorphism, so is the morphism `f'` between the ambient
schemes. -/
theorem mono_right_of_mono_left (S : CartesianFiniteTypeMorphism.{u}) [Mono S.f] :
    Mono S.f' := by
  have : IsClosedImmersion S.j := S.targetThickening.1
  have : Unramified S.f :=
    (unramified_iff_locallyOfFiniteType_and_formallyUnramified S.f).mpr
      ⟨inferInstance, inferInstance⟩
  have : Unramified S.f' := S.unramified_iff.mp this
  have : FormallyUnramified S.f' :=
    ((unramified_iff_locallyOfFiniteType_and_formallyUnramified S.f').mp this).2
  have : IsIso (pullback.diagonal S.f) := (pullback.isIso_diagonal_iff S.f).mpr inferInstance
  let φ := pullback.map S.f S.f S.f' S.f' S.i S.i S.j S.cartesian.w S.cartesian.w
  have hφ : Function.Surjective φ := by
    intro z
    have hz : z ∈ Set.range φ := by
      rw [Scheme.Pullback.range_map]
      exact ⟨S.sourceThickening.2 _, S.sourceThickening.2 _⟩
    exact hz
  have hcomm : S.i ≫ pullback.diagonal S.f' = pullback.diagonal S.f ≫ φ := by
    ext <;> simp [φ]
  have hsurj : Surjective (pullback.diagonal S.f') := by
    refine ⟨fun z ↦ ?_⟩
    obtain ⟨w, rfl⟩ := hφ z
    obtain ⟨x, rfl⟩ := (pullback.diagonal S.f).surjective w
    exact ⟨S.i x, by rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]⟩
  have : IsIso (pullback.diagonal S.f') :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, hsurj⟩
  exact (pullback.isIso_diagonal_iff S.f').mp this

/-- **Stacks 0BPG, part (6).** Being a monomorphism is invariant under a cartesian, locally
finite type morphism of thickenings. -/
@[stacks 0BPG "monomorphism"]
theorem mono_iff (S : CartesianFiniteTypeMorphism.{u}) : Mono S.f ↔ Mono S.f' :=
  ⟨fun _ ↦ S.mono_right_of_mono_left, fun _ ↦ S.cartesian.mono_fst_of_mono⟩

end Stacks.Thickenings.CartesianFiniteTypeMorphism

end
