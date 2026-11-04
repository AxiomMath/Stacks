module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomCoreLHS
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomCohomologyIso

/-!
# The two readings of `H^n(Hom^•(K, Y))` factor through the same comparison

Step 3 of the replacement proof of [Stacks, Tag 09LK] needs the left-hand side of its elementwise
equation — the comparison `ν` followed by the explicit cohomology of the complex of the right
differential graded module, reduced by `CochainComplex.coreLHS_step1` — to agree with the
identification `CochainComplex.homologyGradedCohomologyIso` that
[Tag 09LC] is stated against. The two are built from different material and this file lines them
up.

## What was in the way, and why it was not really there

`DGCategory.HomRepresentation.forgetSquareIso` is the first factor of `ν`, and it is built by a
tactic block that begins by *rewriting the goal* along the two equations
`DGCategory.HomRepresentation.homotopyFunctor_eq` and
`...complexesFunctor_eq`. The resulting term carries two `Eq.mpr` casts, which is why it looked as
though nothing about `forgetSquareIso` could be read off its definition.

It can. For the canonical `DGCategory.homRepresentation` both of those equations are *proved by
`rfl`*, so the types on the two sides of each cast are definitionally equal; proofs in `Prop` are
irrelevant, so each cast is definitionally the identity, and `forgetSquareIso` at an object
reduces to the composite of its factors with no bookkeeping at all. That is
`CochainComplex.forgetSquareIso_hom_app`, and it is a bare `rfl`. The same holds for
`DifferentialGradedModule.derivedForgetHomologyIso` and
`CochainComplex.homologyGradedCohomologyIso`, whose whiskerings and associators are identities on
components.

Once all three are written out, the two sides visibly share their *second* and *third* factors —
`DifferentialGradedModule.derivedForgetFactorization` and
`DifferentialGradedModule.forgetHomotopyToDerivedCategoryIso` — and differ in the first, where one
has `DifferentialGradedModule.complexesQuotientSquareIso` and the other
`CochainComplex.homHomotopyFunctorQuotientIso`. Those two are the content, and
`CochainComplex.complexesQuotientSquareIso_inv_app_onComp` identifies them.

## Main results

* `CochainComplex.complexesQuotientSquareIso_inv_app_onComp`: **the content** — the inverse of
  `DifferentialGradedModule.complexesQuotientSquareIso` at the `Hom(K, -)`-image of a complex is
  `CochainComplex.homHomotopyFunctorQuotientIso` at that complex.
* `CochainComplex.forgetSquareIso_hom_app`,
  `DifferentialGradedModule.derivedForgetHomologyIso_hom_app` and
  `CochainComplex.homologyGradedCohomologyIso_hom_app`: the three factorizations, each by `rfl`.

## Implementation notes

`CochainComplex.complexesQuotientSquareIso_inv_app_onComp` is proved by faithfulness, since the
target is a `CategoryTheory.Functor.fullyFaithfulCancelRight` and therefore characterised only
after the cancelled functor is applied. The two steps that pass through that characterisation are
terms, not rewrites: `rw [CategoryTheory.Functor.map_preimage]` fails here with a goal that is not
type-correct at `implicit` transparency, reported as
`((dgCategory A).homRepresentation K).functor.onComp.obj` receiving a `CochainComplex A ℤ` where a
`(dgCategory A).Comp` was expected. `congrArg` and `Eq.trans` have no occurrence to look for.

What is left after that is the unit-counit relation of
`DifferentialGradedModule.homotopyCategoryEquivalence` together with two `eqToHom`s of
`rfl`-equations, which are proof-irrelevant; `simp` with the definition of
`DifferentialGradedModule.complexesQuotientSquareIso` and a closing `rfl` discharge it.

*What is still owed.* This file does not finish the comparison of the two sides. What remains is
the agreement of the *last* factors: the composite of `CochainComplex.homEvaluationComparisonIso`,
`DerivedCategory.quotientCompQhIso`, `CochainComplex.homDerivedLiftForgetIsoMid` and the two
factorizations of cohomology against
`DerivedCategory.homologyFunctorFactors` followed by
`DifferentialGradedModule.gradedCohomologyFunctorIso`. That comparison is not an identity but the
*bridge* between the two explicit cohomologies — the one indexed by the morphism modules of
`dgCategory A` and the one indexed by the direct sum `DGCategory.representableModule` — which is
degreewise `CochainComplex.homGradingEquiv` by
`CochainComplex.homEvaluationComparisonIso_hom_app_f_apply`.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK), whose step 3 the
  equation belongs to; [Tag 09LE](https://stacks.math.columbia.edu/tag/09LE), the functor
  `Hom(K, -)`.
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGradedModule

universe w u

namespace CochainComplex

variable (A : Type u) [Category.{0} A] [Preadditive A] (K : CochainComplex A ℤ)

/-- **The two quotient comparisons agree.** The inverse of
`DifferentialGradedModule.complexesQuotientSquareIso`, evaluated at the image of a complex `Y`
under `Hom(K, -)` on closed degree-zero morphisms, is
`CochainComplex.homHomotopyFunctorQuotientIso` at `Y`.

This is the single piece of content in the comparison of the first factor of the comparison `ν`
of step 3 of [Stacks, Tag 09LK] with the first factor of
`CochainComplex.homologyGradedCohomologyIso`: everything else in those two composites either
coincides on the nose or is one of the two factorizations of the forgetful functor, which both
sides carry.

The target is a `CategoryTheory.Functor.fullyFaithfulCancelRight`, so it is pinned only by what it
becomes after the cancelled functor is applied; the proof therefore goes by faithfulness of that
functor, and what is left is the unit-counit relation of
`DifferentialGradedModule.homotopyCategoryEquivalence`. -/
theorem complexesQuotientSquareIso_inv_app_onComp (Y : CochainComplex A ℤ) :
    (complexesQuotientSquareIso (endAlgebra A K)).inv.app
        (((DGCategory.homRepresentation (dgCategory A) K).functor.onComp).obj Y) =
      (homHomotopyFunctorQuotientIso A K).hom.app Y := by
  have h1 : (homHomotopyFunctorQuotientIso A K).hom.app Y =
      (DifferentialGradedModule.homotopyCategoryEquivalence (endAlgebra A K)).functor.preimage
        ((Functor.isoWhiskerLeft (homComplexesViaDG A K)
            (DifferentialGradedModule.homotopyCategoryEquivalence
              (endAlgebra A K)).counitIso ≪≫
          (homComplexesViaDG A K).rightUnitor ≪≫
            eqToIso (homotopyFunctor_quotient_eq A K)).hom.app Y) :=
    Functor.fullyFaithfulCancelRight_hom_app _ _
  apply (DifferentialGradedModule.homotopyCategoryEquivalence
    (endAlgebra A K)).functor.map_injective
  refine Eq.trans ?_ ((congrArg
      (DifferentialGradedModule.homotopyCategoryEquivalence (endAlgebra A K)).functor.map h1).trans
    (Functor.map_preimage _ _)).symm
  simp [complexesQuotientSquareIso]
  rfl

variable [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]

/-- **`DGCategory.HomRepresentation.forgetSquareIso` at an object, as its three factors.** The
two `Eq.mpr` casts its definition carries are casts along equations that hold by `rfl` for the
canonical `DGCategory.homRepresentation`, hence — proofs being irrelevant — definitionally the
identity. So this is `rfl`, and no part of the construction has to be reproduced. -/
theorem forgetSquareIso_hom_app (Y : (dgCategory A).Comp) :
    ((DGCategory.homRepresentation (dgCategory A) K).forgetSquareIso).hom.app Y =
      (derivedForget (endAlgebra A K)).map
          ((quasiIsomorphisms' (endAlgebra A K)).Q.map
            ((complexesQuotientSquareIso (endAlgebra A K)).inv.app
              (((DGCategory.homRepresentation (dgCategory A) K).functor.onComp).obj Y))) ≫
        (derivedForgetFactorization (endAlgebra A K)).hom.app
            ((toHomotopyCategory (endAlgebra A K)).obj
              ((DGCategory.homRepresentation (dgCategory A) K).complexesFunctor.obj Y)) ≫
          (forgetHomotopyToDerivedCategoryIso (endAlgebra A K)).hom.app
            ((DGCategory.homRepresentation (dgCategory A) K).complexesFunctor.obj Y) :=
  rfl

/-- **`CochainComplex.homologyGradedCohomologyIso` at a complex, as its three factors**: the
comparison of the two routes to the homotopy category of differential graded modules, the
compatibility of the forgetful functor with cohomology, and the explicit cohomology of a
differential graded module. -/
theorem homologyGradedCohomologyIso_hom_app (n : ℤ) (Y : CochainComplex A ℤ) :
    (homologyGradedCohomologyIso A K n).hom.app Y =
      ((quasiIsomorphisms' (endAlgebra A K)).Q ⋙ derivedForget (endAlgebra A K) ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((homHomotopyFunctorQuotientIso A K).hom.app Y) ≫
        (derivedForgetHomologyIso (endAlgebra A K) n).hom.app
            ((homComplexesFunctor A K).obj Y) ≫
          (gradedCohomologyFunctorIso (endAlgebra A K) n).hom.app
            ((homComplexesFunctor A K).obj Y) :=
  rfl

end CochainComplex

namespace DifferentialGradedModule

universe u'

variable {R : Type u'} [CommRing R] (Aa : DifferentialGradedAlgebra R)
  [HasDerivedCategory.{w} (ModuleCat.{u'} R)]

/-- **`DifferentialGradedModule.derivedForgetHomologyIso` at a module, as its three factors.**
The first two are the ones `DGCategory.HomRepresentation.forgetSquareIso` also carries, which is
what makes the two sides of step 3's left-hand side share everything but their first factor. -/
theorem derivedForgetHomologyIso_hom_app (n : ℤ) (M : DifferentialGradedModule Aa) :
    (derivedForgetHomologyIso Aa n).hom.app M =
      (DerivedCategory.homologyFunctor (ModuleCat.{u'} R) n).map
          ((derivedForgetFactorization Aa).hom.app ((toHomotopyCategory Aa).obj M)) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u'} R) n).map
            ((forgetHomotopyToDerivedCategoryIso Aa).hom.app M) ≫
          (DerivedCategory.homologyFunctorFactors (ModuleCat.{u'} R) n).hom.app
            ((forgetToCochainComplex Aa).obj M) :=
  rfl

end DifferentialGradedModule

end
