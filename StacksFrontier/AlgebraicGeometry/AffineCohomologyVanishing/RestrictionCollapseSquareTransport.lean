module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.RestrictionCollapseSquare

/-!
# The restriction-collapse square at a pushforward hoisted onto a variable

`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_restrictChosenResolution_square`
(`RestrictionCollapseSquare.lean`) states the compatibility of Grothendieck's collapse at the
ambient pair `(f_*, (-|_V) ⋙ P)` with the one at the restricted pair
`((f ∣ V)_*, P)`, with the restricted pushforward written at
`Stacks.Cohomology.HigherDirectImage.restrictedMorphism` — the morphism of ringed spaces the
abstract squares build from `f` themselves.

A consumer that meets the restricted pushforward under a *different* name, equal to that one only
propositionally, cannot use the square as it stands: the three places the restricted pushforward
occurs in the square's statement acquire an `eqToIso` conjugation. This file states the square with
the restricted pushforward on a variable `Q`, taking the equality `Q = (f ∣ V)_*` and the two
derived composite equalities it does *not* imply as separate hypotheses, so that the conjugation is
**discharged** rather than moved.

## Main results

* `…AffineBase.rightDerivedCompNatIso_restrictChosenResolution_square_of_eq`: the square at a
  variable restricted pushforward `Q`, with the two `eqToIso` conjugations its statement then
  carries.

## Implementation notes

*Why the cast is discharged by `subst` and not by a cancellation lemma.* Hoisting the pushforward
onto `Q` and substituting turns both `eqToIso`s into `eqToIso` of reflexivity, which
`CategoryTheory.eqToIso_refl` and `CategoryTheory.Iso.refl_trans` delete outright. A cancellation
lemma taking the original equation and the two conjugations to the conjugated one would *move* the
cast onto its other side instead, which serves no consumer.

*Why the three equalities are separate hypotheses, and why `hd` is not a `congrArg` of `hu`.*
`subst hQ` is refused if `hQ` occurs in the type of another hypothesis, so `hu` and `hd` cannot be
written as `congrArg … hQ` inside the statement; they must be variables of their own. And `hd` is
not `congrArg (fun F => F.rightDerived p) hu`, because
`CategoryTheory.Functor.rightDerived` takes the additivity of its argument as an instance argument,
so `fun F => F.rightDerived p` is not a function of the functor alone.

*Nothing is assumed* of `f`, of `V`, of `E`, of `Z` or of `p`, and nothing of `P` or of `Q` beyond
additivity: the hypotheses are exactly those of the square being transported, plus the three
equalities.

*No `@[stacks …]` attribute is placed.* This is a change of spelling of a compatibility of two
instantiations of Grothendieck's collapse; [Stacks, Tag 01E5] and [Stacks, Tag 01E1] carry their
tags where they are built.

## References

* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction (modulePushforward)
open Stacks.Cohomology.HigherDirectImage

universe u

namespace Stacks.Cohomology.AffineBase

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y)
  {Dc : Type*} [Category* Dc] (E : Dc ⥤ SheafOfModules.{u} (structureSheafRing X))
  {W : Type*} [Category* W] [Abelian W]
  (P : SheafOfModules.{u} (structureSheafRing (restrictToOpen Y V)) ⥤ W) [instP : P.Additive]
  (p : ℕ)

/-- **`…AffineBase.rightDerivedCompNatIso_restrictChosenResolution_square` with the restricted
pushforward on a variable.** Let `Q` be an additive functor from the modules on `f⁻¹V` to the
modules on `V` which is *equal* to the pushforward along
`Stacks.Cohomology.HigherDirectImage.restrictedMorphism f V`, let `hu` and `hd` be the two
equalities of composites with `(-|_{f⁻¹V})` that equality induces on the underived and on the
`p`-th derived pushforward, and conjugate the square's two restricted factors by the
corresponding `eqToIso`s. Then the square still holds.

The hypotheses `hamb`, `hres`, `τ`, `hτ` are the square's own, with the restricted pushforward
read at `Q`; a caller takes `τ` to be the derived transport along the inverse of
`eqToIso hu ≪≫ …HigherDirectImage.modulePushforwardRestrictIso f V`, for which `hτ` is its
reading on the chosen injective resolution.

**Nothing is assumed** of `f`, of `V`, of `E`, of `Z` or of `p`, and nothing of `P` or `Q` beyond
additivity. -/
theorem rightDerivedCompNatIso_restrictChosenResolution_square_of_eq
    (Q : SheafOfModules.{u} (structureSheafRing (restrictToOpen X (preimageOpen f V))) ⥤
      SheafOfModules.{u} (structureSheafRing (restrictToOpen Y V))) [instQ : Q.Additive]
    (hQ : Q = modulePushforward (restrictedMorphism f V))
    (hu : moduleRestriction X (preimageOpen f V) ⋙ Q =
      moduleRestriction X (preimageOpen f V) ⋙ modulePushforward (restrictedMorphism f V))
    (hd : moduleRestriction X (preimageOpen f V) ⋙ Q.rightDerived p =
      moduleRestriction X (preimageOpen f V) ⋙
        (modulePushforward (restrictedMorphism f V)).rightDerived p)
    (hamb : ∀ Z : Dc, (moduleRestriction Y V ⋙ P).PreservesLeftHomologyOf
      ((((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc p))
    (hres : ∀ Z : Dc, P.PreservesLeftHomologyOf
      (((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution
          ((E ⋙ moduleRestriction X (preimageOpen f V)).obj Z)).cocomplex).sc p))
    (τ : (modulePushforward f ⋙ moduleRestriction Y V ⋙ P).rightDerived p ⟶
      (moduleRestriction X (preimageOpen f V) ⋙ Q ⋙ P).rightDerived p)
    (Z : Dc)
    [instAmb : (moduleRestriction Y V ⋙ P).PreservesLeftHomologyOf
      ((((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc p)]
    [instRes : P.PreservesLeftHomologyOf
      (((Q.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution
          ((E ⋙ moduleRestriction X (preimageOpen f V)).obj Z)).cocomplex).sc p)]
    (hτ : τ.app (E.obj Z) =
      ((injectiveResolution (E.obj Z)).isoRightDerivedObj
          (modulePushforward f ⋙ moduleRestriction Y V ⋙ P) p).hom ≫
        (HomologicalComplex.homologyFunctor W (ComplexShape.up ℕ) p).map
          (((Functor.whiskerRight
              (eqToIso hu ≪≫ modulePushforwardRestrictIso f V).inv P).mapHomologicalComplex
            (ComplexShape.up ℕ)).app (injectiveResolution (E.obj Z)).cocomplex) ≫
          ((injectiveResolution (E.obj Z)).isoRightDerivedObj
            (moduleRestriction X (preimageOpen f V) ⋙ Q ⋙ P) p).inv) :
    P.map ((eqToIso hd ≪≫ higherDirectImageRestrictIso f V p).hom.app (E.obj Z)) ≫
        (rightDerivedCompNatIso E (modulePushforward f) (moduleRestriction Y V ⋙ P) p
          hamb).hom.app Z ≫ τ.app (E.obj Z) =
      (rightDerivedCompNatIso (E ⋙ moduleRestriction X (preimageOpen f V)) Q P p
          hres).hom.app Z ≫
        (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
          (moduleRestriction X (preimageOpen f V)) (Q ⋙ P) p).inv.app (E.obj Z) := by
  subst hQ
  simp only [eqToIso_refl, Iso.refl_trans] at hτ ⊢
  exact rightDerivedCompNatIso_restrictChosenResolution_square f V E P p hamb hres τ Z hτ

end Stacks.Cohomology.AffineBase

end
