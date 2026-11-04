module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Functoriality

/-!
# Change of divided power base along a pair of isomorphisms is an equivalence

Let `(p, (S, I, γ), X)` and `(p, (S', I', γ'), X')` be global crystalline situations and let
`f : S ⟶ S'` and `g : X ⟶ X'` be *isomorphisms* — of divided power schemes and of schemes
respectively — compatible with the two structure morphisms to the closed fibres, which is the
datum of change of divided power base, [Stacks, Tag 07IC].  Then the functor
`Cris(X/S) ⥤ Cris(X'/S')` it induces is an equivalence.

This is clause (b) of [Stacks, Tag 07KL] for a pair of isomorphisms.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation`.

* `smallChangeBase_essSurj_of_isIso` — change of base along a pair of isomorphisms is essentially
  surjective.
* `smallChangeBase_isEquivalence_of_isIso` — hence it is an equivalence.
* `smallChangeBaseEquivalenceOfIsIso` — that equivalence, bundled.

## References

* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 07MJ](https://stacks.math.columbia.edu/tag/07MJ)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation

variable {S S' : GlobalCrystallineSituation.{u}} {f : S.S ⟶ S'.S} {g : S.X ⟶ S'.X}
  {h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber}

/-- **Change of divided power base along a pair of isomorphisms is essentially surjective.** -/
instance smallChangeBase_essSurj_of_isIso [IsIso f] [IsIso g] :
    (smallChangeBase S S' f g h).EssSurj where
  mem_essImage B :=
    smallChangeBase_essImage_of_range_toX_subset (h := h)
      (DividedPowerScheme.isInducedOpen_of_isIso f) B
      fun _ _ ↦ Scheme.Hom.surjective g _

/-- **Change of divided power base along a pair of isomorphisms is an equivalence of the small
crystalline sites.** -/
instance smallChangeBase_isEquivalence_of_isIso [IsIso f] [IsIso g] :
    (smallChangeBase S S' f g h).IsEquivalence where
  full := smallChangeBase_full_of_mono (f := f) (g := g) (h := h) inferInstance

/-- **`Cris(X/S)` and `Cris(X'/S')` are equivalent when the two situations are compared by a pair
of isomorphisms**, the equivalence being change of divided power base. -/
def smallChangeBaseEquivalenceOfIsIso (S S' : GlobalCrystallineSituation.{u}) (f : S.S ⟶ S'.S)
    (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    [IsIso f] [IsIso g] :
    CrystallineThickening S ≌ CrystallineThickening S' :=
  (smallChangeBase S S' f g h).asEquivalence

/-- The equivalence is change of divided power base. -/
@[simp]
theorem smallChangeBaseEquivalenceOfIsIso_functor (S S' : GlobalCrystallineSituation.{u})
    (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    [IsIso f] [IsIso g] :
    (smallChangeBaseEquivalenceOfIsIso S S' f g h).functor = smallChangeBase S S' f g h := rfl

end Crystalline.GlobalCrystallineSituation

end
