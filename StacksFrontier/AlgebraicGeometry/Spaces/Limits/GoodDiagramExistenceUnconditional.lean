module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.Main
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GoodDiagramExistence

/-!
# Stacks 0CP7: existence of the diagrams of Stacks 0CP8

Let `B = lim_i B_i` be the limit of a directed inverse system of Noetherian algebraic spaces
over a scheme `S` with affine transition morphisms (Situation 0CP6,
`AlgebraicGeometry.Space.NoetherianLimitSystem`), and let `X ⟶ B` be a quasi-separated morphism
of finite type of algebraic spaces. Then there are an index `i` and a diagram

```
X ⟶ W
↓    ↓
B ⟶ B_i
```

with `W ⟶ B_i` of finite type and `X ⟶ B ×_{B_i} W` a closed immersion, that is, an
`AlgebraicGeometry.Space.GoodDiagram` (Stacks 0CP8).

## Main results

* `AlgebraicGeometry.Space.NoetherianLimitSystem.nonempty_goodDiagram`: **Stacks 0CP7**.

## Implementation notes

The source embeds `X` by a closed immersion into an algebraic space `X'` of finite presentation
over `B` (Stacks 0872) and descends `X'` to a stage (Stacks 07SK). Both steps are carried out in
`AlgebraicGeometry.Space.GoodDiagram.nonempty_goodDiagram_of_noetherianApproximation`, whose
form of Stacks 0872 runs through absolute Noetherian approximation of quasi-compact
quasi-separated algebraic spaces over `Spec ℤ`; that input is Stacks 07SU,
`AlgebraicGeometry.Space.hasNoetherianApproximation_of_isQuasiCompactSpace`, supplied here. No
bound on the size of the index set is assumed, so the diagram is produced for every Noetherian
limit system, in the form consumed by Stacks 0CP9
(`AlgebraicGeometry.Space.GoodDiagram.isLimit_imageCone_of_algebraicLimit`) and Stacks 0CPA
(`AlgebraicGeometry.Space.GoodDiagram.exists_systemMorphism`). For the situation recorded by its
data alone, `AlgebraicGeometry.Space.NoetherianSpaceSystem`, it applies to
`AlgebraicGeometry.Space.NoetherianSpaceSystem.toNoetherianLimitSystem`.

## References

* [Stacks Project, Tag 0CP7](https://stacks.math.columbia.edu/tag/0CP7)
* [Stacks Project, Tag 0CP6](https://stacks.math.columbia.edu/tag/0CP6)
* [Stacks Project, Tag 0CP8](https://stacks.math.columbia.edu/tag/0CP8)
* [Stacks Project, Tag 0872](https://stacks.math.columbia.edu/tag/0872)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.NoetherianLimitSystem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]

/-- **Stacks 0CP7.** In Situation 0CP6, let `f : X ⟶ B` be a quasi-separated morphism of finite
type of algebraic spaces over `S`. Then there are a stage `i`, an algebraic space `W` with a
morphism `W ⟶ B_i` of finite type, and a morphism `X ⟶ W` over `B ⟶ B_i`, such that the induced
morphism `X ⟶ B ×_{B_i} W` is a closed immersion: a diagram as in Stacks 0CP8. -/
@[stacks 0CP7]
theorem nonempty_goodDiagram (D : NoetherianLimitSystem B S hS hZ I)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ D.limitCone.pt)
    (hX : IsAlgebraicSpace B S hS X) (hfqs : IsQuasiSeparated B S hS f)
    (hfft : IsFiniteType B S hS f) :
    Nonempty (GoodDiagram B S hS hZ D f) :=
  GoodDiagram.nonempty_goodDiagram_of_noetherianApproximation D f hX hfqs hfft
    fun _ hZalg hZqc hZqs => hasNoetherianApproximation_of_isQuasiCompactSpace hZalg hZqc hZqs

end AlgebraicGeometry.Space.NoetherianLimitSystem

end
