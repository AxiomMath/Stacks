module

public import StacksFrontier.AlgebraicGeometry.Duality.CohomologyHypercohomology
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.GrauertRiemenschneider

/-!
# Sheaf cohomology over a base ring is hypercohomology of the module in degree zero

Let `A` be a commutative ring, let `f : X ⟶ Spec A` be a scheme over `A` and let `ℱ` be a sheaf
of `𝒪_X`-modules. There are two `A`-modules called `Hⁿ(X, ℱ)`:

* the `n`-th classical right derived functor of global sections, `Γ(X, 𝒪_X)`-linear by
  functoriality and read over `A` by restriction of scalars along `A ⟶ Γ(X, 𝒪_X)`; this is the
  shape of `AlgebraicGeometry.firstCohomologySheafAsBaseModule` and, over a field, of
  `AlgebraicGeometry.cohomologyOverField`; and
* the degree-`n` cohomology of `RΓ(X, -) : D(𝒪_X) ⥤ D(A)` applied to `ℱ` placed in degree zero,
  which is the shape that statements in the derived category are written against.

This file identifies them as objects of `ModuleCat A`, naturally in `ℱ`, over an arbitrary
commutative ring base. No field hypothesis enters: the two steps of the comparison are
restriction of scalars pulled out of a right derived functor, which needs only that restriction
of scalars along a ring homomorphism is exact, and the comparison between a total right derived
functor at an object in degree zero and the classical right derived functor, which is generic in
the sheaf and the degree.

## Main definitions

* `AlgebraicGeometry.cohomologyOverRingFunctorIsoDerivedCohomology` — **the comparison**, as a
  natural isomorphism of functors `X.Modules ⥤ ModuleCat A`.
* `AlgebraicGeometry.cohomologyOverRingIsoDerivedCohomology` — its component at `ℱ`.
* `AlgebraicGeometry.firstCohomologySheafAsBaseModuleIsoDerivedCohomology` — the component in
  degree one, with the left-hand side spelled as
  `AlgebraicGeometry.firstCohomologySheafAsBaseModule`.
* `AlgebraicGeometry.firstCohomologySheafAsBaseModuleLinearEquivDerivedCohomology` — the same as
  an `A`-linear equivalence, which is the form in which a statement about `A`-linear maps out of
  `H¹(X, ℱ)` consumes it.

## Implementation notes

The derived categories are taken at free binders `[HasDerivedCategory.{w₁} X.Modules]` and
`[HasDerivedCategory.{w₂} (ModuleCat A)]`, with independent morphism universes, so that the
comparison is available at either choice of model. Nothing in the proof depends on the model:
both steps are statements about right derived functors computed on resolutions.

`AlgebraicGeometry.globalSectionsOver` is by definition evaluation on the whole space followed
by restriction of scalars along `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)` written through
`AlgebraicGeometry.Scheme.Hom.appTop`, so the comparison of the composite with the two factors
is the identity. Over a field the corresponding step is not an identity, because
`AlgebraicGeometry.cohomologyOverField` restricts scalars along `appLE ⊤ ⊤` instead, and
`AlgebraicGeometry.Scheme.Hom.appLE_eq_app` is not a definitional equality.

The two additivity hypotheses of
`Stacks.Duality.rightDerivedCompRestrictScalarsIso` are passed by name. Instance search does not
reach `AlgebraicGeometry.evaluationAdditive` at the goal that declaration produces, the two
spellings of the topology on `X` being only definitionally equal, whereas a named term is
accepted up to definitional equality.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w₁ w₂ u

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  [HasDerivedCategory.{w₁} X.Modules] [HasDerivedCategory.{w₂} (ModuleCat.{u} A)]

/-- **`Hⁿ(X, -) ≅ (-)[0] ⋙ RΓ(X, -) ⋙ H^n` over the base ring `A`**, as a natural isomorphism
of functors `X.Modules ⥤ ModuleCat A`.

The left-hand side is the `n`-th classical right derived functor of global sections with its
scalars restricted along `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)`; the right-hand side is the degree-`n`
cohomology of unbounded derived global sections at the module placed in degree zero. -/
def cohomologyOverRingFunctorIsoDerivedCohomology (n : ℕ) :
    (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n ⋙
        ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom ≅
      DerivedCategory.singleFunctor X.Modules 0 ⋙ derivedGlobalSectionsOver f ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n : ℤ) :=
  Stacks.Duality.rightDerivedCompRestrictScalarsIso
      ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom
      (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens)))
      (globalSectionsOver f) (Iso.refl _) n
      (hE := AlgebraicGeometry.evaluationAdditive X)
      (hH := AlgebraicGeometry.globalSectionsOver_additive f) ≪≫
    Stacks.Duality.rightDerivedGlobalSectionsIsoDerivedCohomology f n

/-- **`Hⁿ(X, ℱ) ≅ H^n(X, ℱ[0])` in `ModuleCat A`.** The component of
`AlgebraicGeometry.cohomologyOverRingFunctorIsoDerivedCohomology` at a sheaf of modules. -/
def cohomologyOverRingIsoDerivedCohomology (ℱ : X.Modules) (n : ℕ) :
    (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
        (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n).obj ℱ) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n : ℤ)).obj
        ((derivedGlobalSectionsOver f).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj ℱ)) :=
  (cohomologyOverRingFunctorIsoDerivedCohomology f n).app ℱ

/-- **`H¹(X, ℱ) ≅ H^1(X, ℱ[0])` in `ModuleCat A`.** The first cohomology of `ℱ` read as a module
over the base ring is the degree-one hypercohomology of `ℱ` placed in degree zero. -/
def firstCohomologySheafAsBaseModuleIsoDerivedCohomology (ℱ : X.Modules) :
    firstCohomologySheafAsBaseModule X f ℱ ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (1 : ℤ)).obj
        ((derivedGlobalSectionsOver f).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj ℱ)) :=
  cohomologyOverRingIsoDerivedCohomology f ℱ 1

/-- **`H¹(X, ℱ) ≃ₗ[A] H^1(X, ℱ[0])`.** The comparison of
`AlgebraicGeometry.firstCohomologySheafAsBaseModuleIsoDerivedCohomology` as an `A`-linear
equivalence. -/
def firstCohomologySheafAsBaseModuleLinearEquivDerivedCohomology (ℱ : X.Modules) :
    firstCohomologySheafAsBaseModule X f ℱ ≃ₗ[A]
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (1 : ℤ)).obj
        ((derivedGlobalSectionsOver f).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj ℱ)) :=
  (firstCohomologySheafAsBaseModuleIsoDerivedCohomology f ℱ).toLinearEquiv

end AlgebraicGeometry

end
