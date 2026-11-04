module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.EtaleLocalProperties
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.EtaleLocalPropertiesPointTest
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SeparatedAndClosed

/-!
# Properness and finiteness across a morphism of thickenings of algebraic spaces

Let

```
X --f--→ Y
|        |
i        j
↓        ↓
X' -f'-→ Y'
```

be a morphism of thickenings of algebraic spaces over `S` with `f` and `f'` locally of finite
type and `X = Y ×_{Y'} X'`. Then `f` is proper exactly when `f'` is, and `f` is finite exactly
when `f'` is: parts (8) and (2) of Stacks 0BPJ. The square is given by four objects and four
morphisms of the category of algebraic spaces over `S`, its two vertical maps thickenings in the
sense of `AlgebraicGeometry.Space.IsThickeningHom`.

## Main results

* `AlgebraicGeometry.Space.properProperty_iff_of_cartesianSquareOfThickeningHoms`: `f` is proper
  if and only if `f'` is proper.
* `AlgebraicGeometry.Space.finiteMorphismProperty_iff_of_cartesianSquareOfThickeningHoms`: `f` is
  finite if and only if `f'` is finite.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 09ZY](https://stacks.math.columbia.edu/tag/09ZY)
* [Stacks Project, Tag 0A4X](https://stacks.math.columbia.edu/tag/0A4X)
* [Stacks Project, Tag 0BPJ](https://stacks.math.columbia.edu/tag/0BPJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X X' Y Y' : AlgebraicSpaces B S hS} {i : X ⟶ X'} {j : Y ⟶ Y'} {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- Let `(f, f') : (X ⊂ X') → (Y ⊂ Y')` be a morphism of thickenings of algebraic spaces over
`S` with `f` and `f'` locally of finite type and `X = Y ×_{Y'} X'`. Then `f` is proper if and
only if `f'` is proper. -/
@[stacks 0BPJ "part (8): proper, at the Section 04XB point test"]
theorem properProperty_iff_of_cartesianSquareOfThickeningHoms
    (hi : IsThickeningHom B S hS i) (hj : IsThickeningHom B S hS j) (hsq : IsPullback f i j f')
    (hft : locallyOfFiniteTypeProperty B S hS f)
    (hft' : locallyOfFiniteTypeProperty B S hS f') :
    properProperty B S hS f ↔ properProperty B S hS f' := by
  obtain ⟨hici, hisurj⟩ := (isThickeningHom_iff_isClosedImmersion_and_isSurjective B S hS i).mp hi
  have hjci := hj.isClosedImmersion
  have hw : f.hom ≫ j.hom = i.hom ≫ f'.hom := congrArg (fun k => k.hom) hsq.w
  have hsep := isSeparated_iff_isSeparated_of_isClosedImmersion_square B S hS X.property
    X'.property Y.property Y'.property f.hom f'.hom hici hisurj hjci hw
  have hqc := isQuasiCompact_iff_isQuasiCompact_of_isClosedImmersion_square B S hS X.property
    X'.property Y.property Y'.property f.hom f'.hom hici hisurj hjci hw
  have huc := universallyClosed_iff_universallyClosed_of_isClosedImmersion_square B S hS
    X.property X'.property Y.property Y'.property f.hom f'.hom hici hisurj hjci hw
  exact ⟨fun h => ⟨hsep.mp h.1, ⟨hft', hqc.mp h.2.1.2⟩, huc.mp h.2.2⟩,
    fun h => ⟨hsep.mpr h.1, ⟨hft, hqc.mpr h.2.1.2⟩, huc.mpr h.2.2⟩⟩

/-- Let `(f, f') : (X ⊂ X') → (Y ⊂ Y')` be a morphism of thickenings of algebraic spaces over
`S` with `f` and `f'` locally of finite type and `X = Y ×_{Y'} X'`. Then `f` is finite if and
only if `f'` is finite. -/
@[stacks 0BPJ "part (2): finite, at the Section 04XB point test"]
theorem finiteMorphismProperty_iff_of_cartesianSquareOfThickeningHoms
    (hi : IsThickeningHom B S hS i) (hj : IsThickeningHom B S hS j) (hsq : IsPullback f i j f')
    (hft : locallyOfFiniteTypeProperty B S hS f)
    (hft' : locallyOfFiniteTypeProperty B S hS f') :
    finiteMorphismProperty B S hS f ↔ finiteMorphismProperty B S hS f' := by
  rw [finiteMorphismProperty_eq_inf B S hS]
  exact and_congr (properProperty_iff_of_cartesianSquareOfThickeningHoms B S hS hi hj hsq hft hft')
    (locallyQuasiFiniteProperty_iff_of_cartesianSquareOfThickeningHoms B S hS hi hj hsq hft hft')

end AlgebraicGeometry.Space

end
