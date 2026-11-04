module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleReducedDimensionOne.Extension
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafGeneral

/-!
# [Stacks, Tag 0AYM] on a curve: the ampleness hypothesis is not needed

`AlgebraicGeometry.InvertibleSheafGeneral.exists_effectiveCartierDivisors_tensor_invertibleSheaf`
proves [Stacks, Tag 0AYM](https://stacks.math.columbia.edu/tag/0AYM) — every invertible
`𝒪_X`-module on a Noetherian `X` is `𝒪_X(D - D')` for effective Cartier divisors `D`, `D'`
avoiding a prescribed finite set — for an `X` that *carries an ample invertible module*. This
file removes that hypothesis when `X` is **reduced of dimension at most one**, where ampleness is
free: [Stacks, Tag 09NX],
`Stacks.AmpleReducedDimensionOne.exists_isAmple_of_isReduced_of_topologicalKrullDim_le_one`,
produces an ample invertible module on any reduced Noetherian separated scheme of topological
Krull dimension at most one, with nothing assumed.

## Main results

* `InvertibleSheafGeneral.exists_isAmple_of_isReduced_of_topologicalKrullDim_le_one`:
  Tag 09NX in the `Stacks.Ample.IsAmple` spelling that the Tag 0AYM proof consumes.
* `InvertibleSheafGeneral.exists_effectiveCartierDivisors_tensor_invertibleSheaf_of_isReduced`:
  **Tag 0AYM with no ampleness hypothesis**, for `X` reduced, Noetherian, separated and of
  topological Krull dimension at most one.

## Implementation notes

There are two ampleness predicates for an invertible module on a scheme, both registered at
[Stacks, Tag 01PS]: `Stacks.Ample.IsAmple`, over the integer tensor powers
`Stacks.Ample.tensorPowModule`, which is what the Tag 0AYM proof is written against, and
`AlgebraicGeometry.Scheme.Modules.IsAmple`, over `Stacks.SheafOfModules.Invertible.tensorPower`,
which is what Tag 09NX produces. They agree by `Stacks.AmpleBridge.isAmple_iff_isAmple`, with no
hypothesis.

The conclusion is the multiplicative one of
`AlgebraicGeometry.InvertibleSheafGeneral.exists_effectiveCartierDivisors_tensor_invertibleSheaf`,
`𝒩 ⊗ 𝒪_X(D') ≅ 𝒪_X(D)`, which is the same assertion as `𝒩 ≅ 𝒪_X(D) ⊗ 𝒪_X(D')^{⊗ -1}`.

## References

* [Stacks Project, Tag 0AYM](https://stacks.math.columbia.edu/tag/0AYM)
* [Stacks Project, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX)
* [Stacks Project, Tag 09NZ](https://stacks.math.columbia.edu/tag/09NZ)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.Ample

universe u

namespace AlgebraicGeometry.InvertibleSheafGeneral

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj

variable {X : Scheme.{u}}

/-- **[Stacks, Tag 09NX] in the `Stacks.Ample.IsAmple` spelling.** A reduced Noetherian separated
scheme of topological Krull dimension at most one carries an ample invertible module. -/
theorem exists_isAmple_of_isReduced_of_topologicalKrullDim_le_one (X : Scheme.{u})
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsReduced X] [X.IsSeparated]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    ∃ (L : X.Modules) (_ : IsInvertibleModule X L), IsAmple X L := by
  obtain ⟨L, hL, hA⟩ :=
    Stacks.AmpleReducedDimensionOne.exists_isAmple_of_isReduced_of_topologicalKrullDim_le_one
      X hdim
  exact ⟨L, hL, (Stacks.AmpleBridge.isAmple_iff_isAmple X L).mpr hA⟩

/-- **[Stacks, Tag 0AYM] on a reduced curve, with no ampleness hypothesis.** Let `X` be a
reduced, Noetherian, separated scheme of topological Krull dimension at most one and let `𝒩` be
an invertible `𝒪_X`-module. Then `𝒩` is the sheaf `𝒪_X(D - D')` of a difference of two effective
Cartier divisors, and `D` and `D'` may both be chosen disjoint from any prescribed finite subset
`E` of `X`. -/
theorem exists_effectiveCartierDivisors_tensor_invertibleSheaf_of_isReduced
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsReduced X] [X.IsSeparated]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1)
    (N : X.Modules) [IsInvertibleModule X N] {E : Set X} (hE : E.Finite) :
    ∃ D D' : X.IdealSheafData,
      Stacks.Divisors.IsEffectiveCartierDivisor D ∧
      Stacks.Divisors.IsEffectiveCartierDivisor D' ∧
      Disjoint E D.supportSet ∧ Disjoint E D'.supportSet ∧
      Nonempty ((N ⊗ Stacks.Divisors.invertibleSheaf' D' : X.Modules) ≅
        Stacks.Divisors.invertibleSheaf' D) := by
  obtain ⟨L, _, hA⟩ := exists_isAmple_of_isReduced_of_topologicalKrullDim_le_one X hdim
  exact exists_effectiveCartierDivisors_tensor_invertibleSheaf L hA N hE

end AlgebraicGeometry.InvertibleSheafGeneral

end
