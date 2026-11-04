module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisZariskiSquareIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RingedCrystallineTopos
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StructureMorphism

/-!
# The square of topoi of [Stacks, Tag 07MS]

For a morphism `f : (S, I, γ) ⟶ (S', I', γ')` of divided power schemes and a compatible
`g : X ⟶ X'` the four morphisms of topoi

```
  (X/S)_cris --f_cris--> (X'/S')_cris
      | τ_{X/S}                | τ_{X'/S'}
      v                        v
    Sh(S_Zar) ---f_Zar---> Sh(S'_Zar)
```

commute up to a canonical isomorphism of their direct images.

## Main definitions

* `structureSquareOpensIso` — the two routes `X ⟶ S'` pull opens back alike.
* `structureSquarePushforwardIso` — `f_{Zar, *} ∘ τ_{X/S, *} ≅ τ_{X'/S', *} ∘ f_{cris, *}` on
  sheaves of sets.

## References

* [Stacks Project, Tag 07MS](https://stacks.math.columbia.edu/tag/07MS)
* [Stacks Project, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Tag 07IM](https://stacks.math.columbia.edu/tag/07IM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S S' : GlobalCrystallineSituation.{u}} (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
  (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)

/-- **The two routes `X ⟶ S ⟶ S'` and `X ⟶ X' ⟶ S'` pull opens back alike**: the preimage of an
open of `S'` in `X` along `(X ⟶ S) ≫ f` is its preimage along `g ≫ (X' ⟶ S')`. -/
def structureSquareOpensIso :
    Opens.map f.hom.base ⋙ Opens.map (sourceToBase S).base ≅
      Opens.map (sourceToBase S').base ⋙ Opens.map g.base :=
  NatIso.ofComponents
    (fun V ↦ eqToIso (by
      change (Opens.map (sourceToBase S).base).obj ((Opens.map f.hom.base).obj V) =
        (Opens.map g.base).obj ((Opens.map (sourceToBase S').base).obj V)
      rw [← Opens.map_comp_obj, ← Opens.map_comp_obj]
      congr 2
      exact (congrArg (fun φ : S.X ⟶ S'.S.scheme => φ.base)
        (comp_sourceToBase (f := f) (g := g) (h := h))).symm))
    (fun _ ↦ Subsingleton.elim _ _)

/-- **The square of [Stacks, Tag 07MS] commutes on direct images of sheaves of sets**:

`f_{Zar, *} ∘ τ_{X/S, *} ≅ τ_{X'/S', *} ∘ f_{cris, *}`. -/
def structureSquarePushforwardIso :
    ((StacksZariskiSite.opensMapMorphismOfTopoi f.hom.base).comp
        (structureToposMorphism S)).pushforward ≅
      ((structureToposMorphism S').comp (crisMorphism S S' f g h)).pushforward :=
  Functor.isoWhiskerLeft (zariskiToposMorphism S).pushforward
      (Functor.sheafPushforwardContinuousIso (structureSquareOpensIso f g h) (Type (u + 1))
        (Opens.grothendieckTopology S'.S.scheme.carrier)
        (Opens.grothendieckTopology S.X.carrier)) ≪≫
    Functor.isoWhiskerRight
      (asIso (crisZariskiCellCoeff S S' f g h (Type (u + 1))))
      (StacksZariskiSite.opensMapMorphismOfTopoi (sourceToBase S').base).pushforward

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
