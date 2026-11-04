module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.AlgebraicGeometry.DerivedTilde.Basic
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Homology.DerivedCategory.LocallySmall

/-!
# `A`-linear unbounded derived global sections of a scheme over `A`

Let `A` be a commutative ring and let `f : X ⟶ Spec A` be a scheme over `A`. Global sections
`Γ(X, -)` of a sheaf of `𝒪_X`-modules carry an action of `Γ(X, 𝒪_X)` and hence, by restriction
of scalars along `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)`, an action of `A`; this is an additive functor
`X.Modules ⥤ ModuleCat A`. Its total right derived functor `RΓ(X, -) : D(𝒪_X) ⥤ D(A)` exists on
the *unbounded* derived category, with no boundedness hypothesis on the complex and no
cohomological-dimension hypothesis on `X`: sheaves of `𝒪_X`-modules form a Grothendieck abelian
category, so every cochain complex of them admits a quasi-isomorphism into a K-injective complex
(Stacks 079P), and the derivability criterion of Stacks 070K turns such resolutions into a
pointwise right derived functor.

This is the only route available. Mathlib's `Functor.rightDerivedFunctorPlus` is bounded below,
and the general unbounded construction via countable exact limits asks for
`HasExactLimitsOfShape (Discrete ℕ)`, which sheaves of modules do not satisfy.

## Main definitions

* `AlgebraicGeometry.derivedUnitObject` — the structure sheaf `𝒪_X` placed in degree zero, as an
  object of `D(𝒪_X)`.
* `AlgebraicGeometry.globalSectionsOver` — `A`-linear global sections
  `X.Modules ⥤ ModuleCat A` of a scheme over `A`.
* `AlgebraicGeometry.homotopyGlobalSectionsOver` — the same functor read on the homotopy
  category of cochain complexes and composed with the localization to `D(A)`.
* `AlgebraicGeometry.derivedGlobalSectionsOver` — `A`-linear unbounded derived global sections
  `RΓ(X, -) : D(𝒪_X) ⥤ D(A)`.
* `AlgebraicGeometry.derivedGlobalSectionsOverUnit` — the canonical comparison exhibiting it as
  that right derived functor.

## Main results

* `AlgebraicGeometry.Scheme.Modules.exists_quasiIso_isKInjective` — K-injective resolutions of
  complexes of `𝒪_X`-modules.
* `AlgebraicGeometry.Scheme.Modules.hasRightDerivedFunctor` — every functor out of the homotopy
  category of complexes of `𝒪_X`-modules has an unbounded right derived functor along the
  quasi-isomorphisms.
* `AlgebraicGeometry.derivedGlobalSectionsOver_isRightDerivedFunctor` — the universal property
  of `RΓ(X, -)`.

## Implementation notes

The two derived categories are taken at **free** `[HasDerivedCategory.{w₁} X.Modules]` and
`[HasDerivedCategory.{w₂} (ModuleCat.{u} A)]` binders, with independent morphism universes.
Nothing here depends on the model: existence of the right derived functor comes from the
K-injective resolutions of `Scheme.Modules.exists_quasiIso_isKInjective`, which are a statement
about cochain complexes and not about any derived category.

The default a consumer gets, from the instances `ModuleCat.hasDerivedCategory` and
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, is still the *locally small* model, whose
morphisms are in `Type u` rather than `Type (u + 1)`. That is the model Brown representability
(Stacks 0A8G, and hence Stacks 0A86) needs: at `HasDerivedCategory.standard` the morphisms of
`D(𝒪_X)` live a universe above the objects, which makes the `HasCoproducts.{u}` hypothesis false
rather than merely unavailable. Since `HasDerivedCategory` carries the localized category as
data, a consumer that must meet a statement baked at `HasDerivedCategory.standard` cannot get
there by a local instance attribute — the imported instances win — and supplies the model to the
free binders instead.

`globalSectionsOver` is stated with source `X.Modules`, the scheme API's alias for
`SheafOfModules X.ringCatSheaf`, and its body is Mathlib's evaluation functor for that sheaf of
rings. The two spellings are definitionally equal but carry separately declared `Category` and
`Preadditive` instances which instance search does not cross, so each declaration below stays in
one view and the only crossing is by passing a term.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor Opposite

universe w₁ w₂ w v u

namespace AlgebraicGeometry

namespace Scheme.Modules

/-- Every cochain complex of sheaves of modules on a scheme admits a quasi-isomorphism into a
K-injective complex: `𝒪_X`-modules form a Grothendieck abelian category, and such a category
carries a functorial K-injective resolution (Stacks 079P). -/
theorem exists_quasiIso_isKInjective (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ) :
    ∃ (I : CochainComplex X.Modules ℤ) (f : K ⟶ I), I.IsKInjective ∧ QuasiIso f :=
  ⟨_, (Stacks.Injectives.kInjectiveResolutionInclusion X.Modules).app K,
    inferInstance, inferInstance⟩

/-- **Unbounded right derived functors out of `K(𝒪_X)` always exist.** Any functor from the
homotopy category of cochain complexes of `𝒪_X`-modules to any category has a right derived
functor along the quasi-isomorphisms: the K-injective resolutions of
`exists_quasiIso_isKInjective` feed the derivability criterion of Stacks 070K. No boundedness
hypothesis is involved. -/
theorem hasRightDerivedFunctor (X : Scheme.{u}) {H : Type v} [Category.{w} H]
    (F : HomotopyCategory X.Modules (ComplexShape.up ℤ) ⥤ H) :
    F.HasRightDerivedFunctor (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
  have : F.HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{u, w,
      0, u + 1, v, 0} F (exists_quasiIso_isKInjective X)).1
  inferInstance

end Scheme.Modules

/-- `𝒪_W` placed in degree zero, as an object of the unbounded derived category of
`𝒪_W`-modules. It is the unit of the monoidal structure of [Stacks, Tag 0FPB] on `D(𝒪_W)`, and
the complex whose derived global sections are `RΓ(W, 𝒪_W)`. -/
abbrev derivedUnitObject (W : Scheme.{u}) [HasDerivedCategory.{w₁} W.Modules] :
    DerivedCategory W.Modules :=
  (DerivedCategory.singleFunctor W.Modules 0).obj (SheafOfModules.unit W.ringCatSheaf)

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  [HasDerivedCategory.{w₁} X.Modules] [HasDerivedCategory.{w₂} (ModuleCat.{u} A)]

/-- **`A`-linear global sections of a scheme over `A`.** Global sections of a sheaf of
`𝒪_X`-modules, regarded as an `A`-module by restriction of scalars along
`A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)`. -/
abbrev globalSectionsOver : X.Modules ⥤ ModuleCat.{u} A :=
  SheafOfModules.evaluation X.ringCatSheaf (op ⊤) ⋙
    ModuleCat.restrictScalars (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom)

/-- `A`-linear global sections is an additive functor; addition of sections of a sheaf of
modules is computed open by open. -/
instance globalSectionsOver_additive : (globalSectionsOver f).Additive where
  map_add := rfl

/-- `A`-linear global sections read on the homotopy category of cochain complexes of
`𝒪_X`-modules, with values in `D(A)`. This is the functor whose right derived functor is
`derivedGlobalSectionsOver`. -/
abbrev homotopyGlobalSectionsOver :
    HomotopyCategory X.Modules (ComplexShape.up ℤ) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  (globalSectionsOver f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- `A`-linear unbounded derived global sections exist for every scheme over `A`. -/
instance homotopyGlobalSectionsOver_hasRightDerivedFunctor :
    (homotopyGlobalSectionsOver f).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
  Scheme.Modules.hasRightDerivedFunctor X _

/-- **`A`-linear unbounded derived global sections** `RΓ(X, -) : D(𝒪_X) ⥤ D(A)` of a scheme over
`A`: the total right derived functor of `globalSectionsOver` on the whole unbounded derived
category. -/
abbrev derivedGlobalSectionsOver :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} A) :=
  (homotopyGlobalSectionsOver f).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))

/-- The canonical comparison from termwise `A`-linear global sections to their unbounded right
derived functor. -/
abbrev derivedGlobalSectionsOverUnit :
    homotopyGlobalSectionsOver f ⟶ DerivedCategory.Qh ⋙ derivedGlobalSectionsOver f :=
  (homotopyGlobalSectionsOver f).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))

/-- The comparison exhibits `derivedGlobalSectionsOver` as the right derived functor of
`A`-linear global sections, which is the universal property that characterizes it. -/
instance derivedGlobalSectionsOver_isRightDerivedFunctor :
    (derivedGlobalSectionsOver f).IsRightDerivedFunctor (derivedGlobalSectionsOverUnit f)
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
  inferInstance

end AlgebraicGeometry

end
