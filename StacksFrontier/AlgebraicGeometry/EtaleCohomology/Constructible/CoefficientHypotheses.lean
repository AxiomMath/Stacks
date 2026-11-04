module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantIsConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerre.FiniteTypeLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreSets.FiniteLocallyConstantClosure

/-!
# The coefficient hypotheses of the constructibility statements are satisfiable

The constructibility statements for module coefficients carry two instance hypotheses: that the
direct image between small étale sites is a right adjoint, and that the localizations of a small
étale site admit weak sheafification. Both hold for sheaves of modules over a commutative ring, at
the coefficient universe of `AlgebraicGeometry.SmallEtale.hasSheafify_moduleCat`. A terminal sheaf
of sets and the zero sheaf of modules over a Noetherian ring are constructible.

## Main results

* `AlgebraicGeometry.SmallEtale.hasWeakSheafify_over_moduleCat` — the localizations of a small
  étale site admit weak sheafification with module coefficients.
* `AlgebraicGeometry.SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat` — the direct
  image of module-valued sheaves between small étale sites is a right adjoint.
* `AlgebraicGeometry.isConstructibleSetSheaf_of_isTerminal` and
  `AlgebraicGeometry.isConstructibleModuleSheaf_zero` — a terminal sheaf of sets and the zero
  sheaf of modules over a Noetherian ring are constructible.

## References

* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject

universe w r u

namespace AlgebraicGeometry

/-- The forgetful functor from `ModuleCat.{max (u + 1) r w} R` preserves `u + 1`-small filtered
colimits. -/
private theorem preservesFilteredColimitsOfSize_forget_moduleCat (R : Type r) [CommRing R] :
    PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (forget (ModuleCat.{max (u + 1) r w} R)) := by
  let : PreservesColimits
      (forget₂ (ModuleCat.{max (u + 1) r w} R) AddCommGrpCat) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max (u + 1) r w, r,
      max (u + 1) r w, max (u + 1) r w} R
  let : PreservesFilteredColimits (forget (ModuleCat.{max (u + 1) r w} R)) :=
    comp_preservesFilteredColimits
      (forget₂ (ModuleCat.{max (u + 1) r w} R) AddCommGrpCat) (forget AddCommGrpCat)
  exact preservesFilteredColimitsOfSize_shrink.{u + 1, max r w, u + 1, max r w} _

/-- The localizations of a small étale site admit weak sheafification with coefficients in
`ModuleCat.{max (u + 1) r w} R`. -/
public theorem SmallEtale.hasWeakSheafify_over_moduleCat (B : BigEtaleSite.{u})
    (R : Type r) [CommRing R] (T : B.Scheme) (V : SmallEtale B T.obj T.property) :
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) r w} R) := by
  have := preservesFilteredColimitsOfSize_forget_moduleCat.{w, r, u} R
  infer_instance

/-- The direct image of sheaves with values in `ModuleCat.{max (u + 1) r w} R` along a morphism
of small étale sites is a right adjoint. -/
public theorem SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat (B : BigEtaleSite.{u})
    (R : Type r) [CommRing R] (S T : B.Scheme) (g : T ⟶ S) :
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r w} R)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint := by
  have := preservesFilteredColimitsOfSize_forget_moduleCat.{w, r, u} R
  infer_instance

/-- A terminal sheaf of sets on the small étale site of `X` is constructible. -/
public theorem isConstructibleSetSheaf_of_isTerminal (B : BigEtaleSite.{u}) (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hF : IsTerminal F) : IsConstructibleSetSheaf B X F :=
  have : Stacks.ConstantSheaf.IsFiniteLocallyConstant
      (SmallEtale.topology B X.obj X.property) F :=
    Stacks.ConstantSheaf.isFiniteLocallyConstant_of_isTerminal _ F hF
  isConstructibleSetSheaf_of_isFiniteLocallyConstant B X F

/-- The zero sheaf of modules over a Noetherian ring on the small étale site of `X` is
constructible. -/
public theorem isConstructibleModuleSheaf_zero (B : BigEtaleSite.{u}) (X : B.Scheme)
    (R : Type r) [CommRing R] [IsNoetherianRing R]
    [∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} R)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} R)]
    [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} R)] :
    IsConstructibleModuleSheaf B X R
      (0 : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} R)) :=
  isConstructibleModuleSheaf_of_isFiniteTypeLocallyConstant B X R _
    (Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_zero
      (SmallEtale.topology B X.obj X.property) R)

end AlgebraicGeometry

end
