module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimitDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.GeneralCoefficients

/-!
# Inverse images along named composites, and of constant sheaves

For morphisms `f : X ⟶ Y`, `g : Y ⟶ Z` and `h : X ⟶ Z` of schemes with `f ≫ g = h`, inverse
image of étale sheaves along `g` followed by inverse image along `f` is inverse image along `h`;
and the inverse image of the constant sheaf with value `E` is the constant sheaf with value `E`.

## Main definitions

* `AlgebraicGeometry.smallEtaleSheafPullbackCompIso'`: the composition comparison
  `AlgebraicGeometry.smallEtaleSheafPullbackCompIso` transported along an equation `f ≫ g = h`.
* `AlgebraicGeometry.smallEtaleConstantPullbackIso`: the isomorphism between the inverse image of
  the constant sheaf with value `E` and the constant sheaf with value `E`.

## Main results

* `AlgebraicGeometry.smallEtaleSheafPullbackCompIso'_rfl`: for `h := f ≫ g` and `rfl`,
  `AlgebraicGeometry.smallEtaleSheafPullbackCompIso'` is
  `AlgebraicGeometry.smallEtaleSheafPullbackCompIso`.

## References

* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
* [Stacks Project, Tag 0GL2](https://stacks.math.columbia.edu/tag/0GL2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (A : Type t) [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

/-- **Inverse image along a named composite.** For `f : X ⟶ Y`, `g : Y ⟶ Z` and `h : X ⟶ Z` with
`f ≫ g = h`, inverse image along `g` followed by inverse image along `f` is inverse image along
`h`: the composition comparison `AlgebraicGeometry.smallEtaleSheafPullbackCompIso` of Tag 021J,
transported along the equation. -/
public def smallEtaleSheafPullbackCompIso' {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (e : f ≫ g = h) :
    smallEtaleSheafPullback B A g ⋙ smallEtaleSheafPullback B A f ≅
      smallEtaleSheafPullback B A h :=
  smallEtaleSheafPullbackCompIso B X Y Z f g A ≪≫
    eqToIso (congrArg (fun k => smallEtaleSheafPullback B A k) e)

/-- For `h := f ≫ g` and `rfl`, `AlgebraicGeometry.smallEtaleSheafPullbackCompIso'` is the
composition comparison `AlgebraicGeometry.smallEtaleSheafPullbackCompIso`. -/
@[simp]
public theorem smallEtaleSheafPullbackCompIso'_rfl {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtaleSheafPullbackCompIso' B A f g (f ≫ g) rfl =
      smallEtaleSheafPullbackCompIso B X Y Z f g A := by
  simp [smallEtaleSheafPullbackCompIso']

variable [∀ (S : B.Scheme), HasWeakSheafify (SmallEtale.topology B S.obj S.property) A]

/-- **The inverse image of a constant sheaf is constant**, as an isomorphism of sheaves for a
single value `E`: the component at `E` of
`AlgebraicGeometry.smallEtaleSheafPullbackConstantSheafIso`. -/
public abbrev smallEtaleConstantPullbackIso {S T : B.Scheme} (f : T ⟶ S) (E : A) :
    (smallEtaleSheafPullback B A f).obj
        ((constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E) ≅
      (constantSheaf (SmallEtale.topology B T.obj T.property) A).obj E :=
  (smallEtaleSheafPullbackConstantSheafIso B f A).app E

end AlgebraicGeometry

end
