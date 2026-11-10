module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedBaseChangeGlobal
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnitCoherence

/-!
# The derived base change map commutes with the shift

For a commutative square of ringed spaces

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

the derived base change map `Lg^* Rf_* ⟶ Rf'_* L(g')^*` of Stacks 08HY is compatible with the
shift functors of the four derived categories.  It is the mate, under the derived adjunctions
`Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*`, of the comparison of the two iterated derived pullbacks, and
a mate of a shift-compatible two-square across two shift-compatible adjunctions is
shift-compatible.

## Main results

* `Stacks.Cohomology.DerivedBaseChange.commShift_mateEquiv`: the mate of a shift-compatible
  two-square across two shift-compatible adjunctions is shift-compatible.
* `Stacks.Cohomology.DerivedBaseChange.commShift_derivedBaseChangeNatTrans`: the derived base
  change map is shift-compatible.

## Implementation notes

The shift datum of `Rf_*` is `derivedPushforwardCommShift`, the one transported across the
derived adjunction from that of `Lf^*`, so the adjunction is shift-compatible by
`CategoryTheory.Adjunction.commShift_of_leftAdjoint`; the comparison of the two iterated derived
pullbacks is shift-compatible because the composition isomorphism of Stacks 0D5S is,
`StacksDraft.UnitPullbackComposition.commShift_derivedPullbackCompIsoCanonical_hom`.

## References

* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.Cohomology.DerivedBaseChange

section Abstract

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {A : Type*} [AddMonoid A] [HasShift C A] [HasShift D A] [HasShift E A] [HasShift F A]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  [G.CommShift A] [H.CommShift A] [L₁.CommShift A] [R₁.CommShift A] [L₂.CommShift A]
  [R₂.CommShift A]
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [adj₁.CommShift A] [adj₂.CommShift A]

/-- **The mate of a shift-compatible two-square is shift-compatible.**  For adjunctions
`L₁ ⊣ R₁` and `L₂ ⊣ R₂` compatible with the shifts and a two-square `G ⋙ L₂ ⟶ L₁ ⋙ H`
compatible with the shifts, the mate `R₁ ⋙ G ⟶ H ⋙ R₂` is compatible with the shifts: it is a
composite of whiskerings of the unit of `L₂ ⊣ R₂`, of the two-square and of the counit of
`L₁ ⊣ R₁`, together with associators and unitors. -/
theorem commShift_mateEquiv (α : G ⋙ L₂ ⟶ L₁ ⋙ H) [NatTrans.CommShift α A] :
    NatTrans.CommShift (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α)) A := by
  change NatTrans.CommShift ((R₁ ⋙ G).rightUnitor.inv ≫
            (R₁ ⋙ G).whiskerLeft adj₂.unit ≫
              (R₁.associator G (L₂ ⋙ R₂)).hom ≫
                R₁.whiskerLeft (G.associator L₂ R₂).inv ≫
                  R₁.whiskerLeft (Functor.whiskerRight α R₂) ≫
                    R₁.whiskerLeft (L₁.associator H R₂).hom ≫
                      (R₁.associator L₁ (H ⋙ R₂)).inv ≫
                        Functor.whiskerRight adj₁.counit (H ⋙ R₂) ≫ (H ⋙ R₂).leftUnitor.hom) A
  infer_instance

end Abstract

open _root_.AlgebraicGeometry Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

attribute [local instance] HasDerivedCategory.standard derivedPushforwardCommShift

variable {X' X S' S : RingedSpace.{u, u}}
  (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)

/-- The derived adjunction `Lf^* ⊣ Rf_*` is compatible with the shifts, for the shift datum of
`Rf_*` transported across it. -/
instance derivedAdjunction_commShift {Y Z : RingedSpace.{u, u}} (p : Y ⟶ Z) :
    (derivedAdjunction p).CommShift ℤ :=
  (derivedAdjunction p).commShift_of_leftAdjoint ℤ

/-- Transport of derived pullback along an equality of morphisms commutes with the shift. -/
theorem commShift_eqToHom_derivedPullback {Y Z : RingedSpace.{u, u}} {p q : Y ⟶ Z} (h : p = q) :
    NatTrans.CommShift (eqToHom (congrArg (fun k : Y ⟶ Z => derivedPullback k) h)) ℤ := by
  subst h
  exact NatTrans.CommShift.id _ _

/-- The comparison `Lg^* ⋙ Lf'^* ⟶ Lf^* ⋙ L(g')^*` of the two iterated derived pullbacks around
the square commutes with the shift. -/
theorem commShift_derivedPullbackSquare :
    NatTrans.CommShift ((derivedPullbackCompIsoLeft g' f' f g sq).hom ≫
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g' f).inv) ℤ := by
  have := commShift_eqToHom_derivedPullback sq.symm
  dsimp only [derivedPullbackCompIsoLeft, Iso.trans_hom, eqToIso.hom]
  infer_instance

/-- **The derived base change map of Stacks 08HY commutes with the shift.** -/
instance commShift_derivedBaseChangeNatTrans :
    NatTrans.CommShift (derivedBaseChangeNatTrans g' f' f g sq) ℤ := by
  have := commShift_derivedPullbackSquare g' f' f g sq
  exact commShift_mateEquiv (derivedAdjunction f) (derivedAdjunction f')
    ((derivedPullbackCompIsoLeft g' f' f g sq).hom ≫
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical g' f).inv)

end Stacks.Cohomology.DerivedBaseChange

end
