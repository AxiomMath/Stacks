module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Cartesian
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Extension
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.SchemeModels
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedFormallyUnramified

/-!
# Étale-local properties across a cartesian morphism of thickenings

Let

```
X --f--→ Y
|        |
i        j
↓        ↓
X' -f'-→ Y'
```

be a commutative square identifying `X` with `Y ×_{Y'} X'`, in which `i` and `j` are
thickenings and both `f` and `f'` are locally of finite type. For a property of morphisms which
is étale local on the source and target, `f` has the property exactly when `f'` does, both for
schemes and for algebraic spaces.

Local quasi-finiteness is such a property. For morphisms of schemes the two thickenings are
homeomorphisms matching the fibres of `f` with the fibres of `f'`, so the fibre-isolation
condition transfers; no finiteness condition on the thickenings is needed once both horizontal
maps are assumed locally of finite type, which is the difference between this situation and the
finite-order one of Tag 09ZW.

The vanishing of the module of relative differentials is the same property as unramifiedness
for a morphism which is locally of finite type, and the equivalence is recorded here in that
form.

## Main results

* `Stacks.Thickenings.CartesianFiniteTypeMorphism.locallyQuasiFinite_iff`: **Stacks 0BPG**,
  part (1), for morphisms of thickenings of schemes.
* `AlgebraicGeometry.Space.isLocallyQuasiFinite_iff_of_cartesianMorphismOfThickenings`:
  **Stacks 0BPJ**, part (1).
* `AlgebraicGeometry.Space.formallyUnramifiedCharts_iff_of_cartesianMorphismOfThickenings`:
  **Stacks 0BPJ**, part (4), the vanishing of the relative differentials.

## Implementation notes

Following Tag 03XJ, local quasi-finiteness of a morphism of algebraic spaces is the étale-chart
condition for the conjunction of Mathlib's `AlgebraicGeometry.LocallyOfFiniteType` and
`AlgebraicGeometry.LocallyQuasiFinite`, so the scheme-level statement is stated for that
conjunction too; on a `Stacks.Thickenings.CartesianFiniteTypeMorphism` the first conjunct holds
on both sides by hypothesis and only the second has content.

The library has no quasi-coherent module of relative differentials of a morphism of algebraic
spaces, and the vanishing of the relative differentials is expressed instead by the étale-chart
condition for Mathlib's `AlgebraicGeometry.FormallyUnramified`, which on an affine chart is
exactly the vanishing of the Kähler differentials of the corresponding ring map. Since
`Ω_{X/Y}` restricts to `Ω_{U/V}` on an étale chart square `(U → X, V → Y)`, that chart
condition is the vanishing of `Ω_{X/Y}`. In this form part (4) is part (5) for a morphism whose
two component maps are locally of finite type: unramifiedness of a morphism of schemes is local
finite type together with formal unramifiedness (Tag 02HE), which for morphisms of algebraic
spaces is
`AlgebraicGeometry.Space.isUnramified_iff_isLocallyOfFiniteType_and_formallyUnramifiedCharts`.

## References

* [Stacks Project, Tag 02HE](https://stacks.math.columbia.edu/tag/02HE)
* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
* [Stacks Project, Tag 04GA](https://stacks.math.columbia.edu/tag/04GA)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 0BPG](https://stacks.math.columbia.edu/tag/0BPG)
* [Stacks Project, Tag 0BPJ](https://stacks.math.columbia.edu/tag/0BPJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-- **Stacks 0BPG, part (1).** Being locally quasi-finite is invariant under a cartesian,
locally finite type morphism of thickenings of schemes. -/
@[stacks 0BPG "locally_quasi_finite"]
theorem CartesianFiniteTypeMorphism.locallyQuasiFinite_iff
    (S : CartesianFiniteTypeMorphism.{u}) :
    (LocallyOfFiniteType S.f ∧ LocallyQuasiFinite S.f) ↔
      (LocallyOfFiniteType S.f' ∧ LocallyQuasiFinite S.f') :=
  have h : LocallyQuasiFinite S.f ↔ LocallyQuasiFinite S.f' :=
    locallyQuasiFinite_iff_of_isThickening S.sourceThickening S.targetThickening
      S.cartesian.flip
  ⟨fun hf ↦ ⟨inferInstance, h.mp hf.2⟩, fun hf ↦ ⟨inferInstance, h.mpr hf.2⟩⟩

end Stacks.Thickenings

/-! ### Algebraic spaces -/

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0BPJ, part (1).** Being locally quasi-finite is invariant under a cartesian
morphism of thickenings of algebraic spaces whose two component maps are locally of finite
type. -/
@[stacks 0BPJ "locally_quasi_finite"]
theorem isLocallyQuasiFinite_iff_of_cartesianMorphismOfThickenings
    (T : CartesianLocallyFiniteTypeMorphismOfThickenings B S hS) :
    IsLocallyQuasiFinite B S hS T.f ↔ IsLocallyQuasiFinite B S hS T.f' :=
  holdsOnEveryEtaleChart_iff_of_cartesianMorphismOfThickenings B S hS T _
    locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget
    fun E ↦ E.locallyQuasiFinite_iff

/-- **Stacks 0BPJ, part (4).** In a cartesian morphism of thickenings of algebraic spaces whose
two component maps are locally of finite type, the module of relative differentials of `f`
vanishes exactly when the module of relative differentials of `f'` does.

The vanishing of `Ω_{X/Y}` is expressed by the condition that the morphism of schemes in every
commuting square of étale charts of `f` is formally unramified, which on an affine chart is the
vanishing of the Kähler differentials of the corresponding ring map. -/
@[stacks 0BPJ "vanishing_differentials"]
theorem formallyUnramifiedCharts_iff_of_cartesianMorphismOfThickenings
    (T : CartesianLocallyFiniteTypeMorphismOfThickenings B S hS) :
    HoldsOnEveryEtaleChart B S hS
        (@_root_.AlgebraicGeometry.FormallyUnramified.{u} : MorphismProperty Scheme.{u}) T.f ↔
      HoldsOnEveryEtaleChart B S hS
        (@_root_.AlgebraicGeometry.FormallyUnramified.{u} : MorphismProperty Scheme.{u}) T.f' := by
  have h := isUnramified_iff_of_cartesianMorphismOfThickenings B S hS T
  rw [isUnramified_iff_isLocallyOfFiniteType_and_formallyUnramifiedCharts,
    isUnramified_iff_isLocallyOfFiniteType_and_formallyUnramifiedCharts] at h
  exact ⟨fun hf ↦ (h.mp ⟨T.locallyOfFiniteType_left, hf⟩).2,
    fun hf ↦ (h.mpr ⟨T.locallyOfFiniteType_right, hf⟩).2⟩

end AlgebraicGeometry.Space

end
