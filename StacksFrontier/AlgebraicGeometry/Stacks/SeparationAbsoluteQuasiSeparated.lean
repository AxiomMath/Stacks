module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationConstructionAQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationOverBaseSource

/-!
# Absolute quasi-separatedness passes from the target of a 1-morphism to its source
(Stacks 050L, part (8))

Stacks 050L has eight assertions: for each of the four separation conditions of Stacks 04YW, if
`f : 𝒳 ⟶ 𝒴` has it and `𝒴` has it over the base, then `𝒳` has it over the base (parts (1)–(4)),
and the same four statements with "over the base" read absolutely (parts (5)–(8)).

Part (8) is part (4) at the terminal scheme `Spec ℤ`. Absolute quasi-separatedness of an
algebraic stack is quasi-separatedness over the terminal scheme of its view there
(`AlgebraicGeometry.Stack.AlgebraicStacks.viewOverIntegers`), and that view is
`AlgebraicGeometry.Stack.changeBaseAlgebraicStack` along `terminal.from S` on the nose, so the
source and target of the 1-morphism of views need no further identification. What has to be
supplied is a 1-morphism of views carrying the quasi-separatedness of `f`: the hom-bijection
`AlgebraicGeometry.Stack.algebraicStackConstructionHomEquiv` of Stacks 04X5 produces the
1-morphism, and `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_changeBase` carries the
condition across.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyQuasiSeparated_of_isQuasiSeparated`:
  **Stacks 050L**, part (8).

## Implementation notes

The transfer of the quasi-separatedness condition of Stacks 04YW along Construction A runs from
the smaller base to the larger one and not back, so unlike the Deligne–Mumford and quasi-DM cases
(`AlgebraicGeometry.Stack.isDM_changeBase_iff` and
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_changeBase_iff`, which are equivalences) the
input here is an implication. That is the direction part (8) needs, and it is the whole of what it
needs: the base pair is `S ⟶ Spec ℤ`, with `S` the smaller base.

The hypothesis on the target comes before the hypothesis on the 1-morphism, as in
`AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyDM_of_isDM` and
`AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyQuasiDM_of_isQuasiDM`, rather than in the
reverse order in which Stacks 050L lists them.

## References

* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050L](https://stacks.math.columbia.edu/tag/050L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u})) {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 050L, part (8).** If `f : 𝒳 ⟶ 𝒴` is quasi-separated and `𝒴` is quasi-separated, then
`𝒳` is quasi-separated.

Both absolute properties are quasi-separatedness over the terminal scheme of the views
`AlgebraicGeometry.Stack.AlgebraicStacks.viewOverIntegers` of `𝒳` and `𝒴` there, and that view is
`AlgebraicGeometry.Stack.changeBaseAlgebraicStack` along `terminal.from S` on the nose. So this is
part (4) at the terminal scheme, applied to the 1-morphism of views that the hom-bijection of
Stacks 04X5 assigns to `f`, which is quasi-separated by
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_changeBase`. -/
@[stacks 050L "quasi_separated_absolute"]
theorem isAbsolutelyQuasiSeparated_of_isQuasiSeparated (f : 𝒳 ⟶ 𝒴)
    (hY : IsAbsolutelyQuasiSeparated B S hS hZ 𝒴) (hf : IsQuasiSeparated B S hS f) :
    IsAbsolutelyQuasiSeparated B S hS hZ 𝒳 :=
  isQuasiSeparatedOver_of_isQuasiSeparated B (⊤_ Scheme.{u}) hZ
    (Bicategory.InducedBicategory.mkHom
      (Stack.algebraicStackConstructionHomEquiv B S (⊤_ Scheme.{u}) hS hZ
        (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) 𝒳 𝒴 f).val)
    hY
    (isQuasiSeparated_changeBase B S (⊤_ Scheme.{u}) hS hZ
      (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) f hf)

end AlgebraicGeometry.Stack.AlgebraicStacks

end
