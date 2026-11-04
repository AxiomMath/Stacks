module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.StructureSheafPushforward
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.StructureSheafSplitting
import StacksCore.Tactic.StacksAttribute

/-!
# The direct image of the structure sheaf of a proper flat family with nice geometric fibres

[Stacks, Tag 0E0L]: let `f : X ⟶ S` be proper, flat and of finite presentation, with geometric
fibres reduced and connected. Then `f_*𝒪_X = 𝒪_S`, and this holds after any base change.

The proof is the source's: it is part (a) of [Stacks, Tag 0E62]
(`Stacks.AlgebraicGeometry.ProperFlatStructureSheafSplitting.properFlat_structureSheaf_splitting`),
whose hypothesis `κ(s) = H⁰(X_s, 𝒪_{X_s})` holds at every `s ∈ S` because each fibre `X_s` is
proper, geometrically reduced and geometrically connected over `κ(s)`, by [Stacks, Tag 0BUG] (7):
`Stacks.AlgebraicGeometry.ProperFlatStructureSheaf.bijective_fiber_appTop_of_geomReducedConnected`.

## Main results

* `Stacks.AlgebraicGeometry.ProperFlatStructureSheaf.isIso_c_and_isIso_c_of_isPullback`:
  [Stacks, Tag 0E0L], both conclusions.

## Implementation notes

"`f_*𝒪_X = 𝒪_S`" is the invertibility of `f.c : 𝒪_S ⟶ f_*𝒪_X`, the comparison of sheaves of
rings. "The geometric fibres are reduced and connected" is `GeometricallyReduced f` and
`GeometricallyConnected f`. "Of finite presentation" is `LocallyOfFinitePresentation f` together
with quasi-compactness and quasi-separatedness, which properness supplies.

## References

* [Stacks Project, Tag 0E0L](https://stacks.math.columbia.edu/tag/0E0L)
* [Stacks Project, Tag 0E62](https://stacks.math.columbia.edu/tag/0E62)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ProperFlatStructureSheaf

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Stacks Project, Tag 0E0L.** Let `f : X ⟶ S` be proper, flat and of finite presentation, with
geometric fibres reduced and connected. Then `f_*𝒪_X = 𝒪_S`, i.e. `f.c : 𝒪_S ⟶ f_*𝒪_X` is
invertible, and this holds after any base change: for every cartesian square
```
X' --g'--> X
|f'        |f
v          v
S' --g---> S
```
the comparison `f'.c : 𝒪_{S'} ⟶ f'_*𝒪_{X'}` is invertible.

Finite presentation is `LocallyOfFinitePresentation f` together with quasi-compactness and
quasi-separatedness, which properness supplies. The geometric fibres being reduced and connected
is `GeometricallyReduced f` and `GeometricallyConnected f`. -/
@[stacks 0E0L "both conclusions: f_*O_X = O_S, as invertibility of the comparison f.c of sheaves \
of rings, and the same for every base change, stated for every cartesian square over S."]
theorem isIso_c_and_isIso_c_of_isPullback [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] [GeometricallyReduced f] [GeometricallyConnected f] :
    IsIso f.c ∧ ∀ {X' S' : Scheme.{u}} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'},
      IsPullback g' f' f g → IsIso f'.c :=
  have h := (ProperFlatStructureSheafSplitting.properFlat_structureSheaf_splitting f
    (FinitePresentation.mk inferInstance inferInstance inferInstance)
    (bijective_fiber_appTop_of_geomReducedConnected f)).1
  ⟨h.1, fun {_ _ g g' f'} sq ↦ h.2 g f' g' sq⟩

end Stacks.AlgebraicGeometry.ProperFlatStructureSheaf

end
