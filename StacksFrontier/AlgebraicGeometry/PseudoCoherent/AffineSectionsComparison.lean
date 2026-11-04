module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveRepresentative
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineDerivedPresentation
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictKInjective
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeOpenImmersion
public import StacksFrontier.AlgebraicGeometry.FromSpecImageTop

/-!
# Derived sections of a complex over an affine open, read on its spectrum

Let `X` be a scheme, `U` an affine open of `X` and `E` an object of the unbounded derived category
of `𝒪_X`-modules. There are two ways to form the complex of `Γ(X, U)`-modules `RΓ(U, E)`: restrict
`E` to `U`, carry it to `Spec Γ(X, U)` along `AlgebraicGeometry.IsAffineOpen.isoSpec` and take
derived global sections there, or take derived sections over `U` directly on `X`. This file proves
that the two agree, and with that the comparison of Stacks 09VF becomes unconditional.

## Main results

* `AlgebraicGeometry.IsAffineOpen.derivedSectionsSpecIso`: derived global sections on the spectrum
  of an affine open are the derived sections over that open, as an isomorphism of **functors** on
  the unbounded derived category. No hypothesis on the object.
  `AlgebraicGeometry.IsAffineOpen.nonempty_iso_derivedSectionsSpec` is its objectwise form.
* `AlgebraicGeometry.affineDerivedSectionsPresentation`: the affine presentation hypothesis of
  Stacks 09VF, unconditionally, for every complex with quasi-coherent cohomology sheaves.
* `AlgebraicGeometry.derivedSectionsPseudoCoherentComparison'`: **Stacks 09VF.** For `f : X ⟶ S`
  locally of finite type and `E` in `D_{QCoh}(𝒪_X)`, the three conditions of the source are
  equivalent.

Two auxiliary facts are proved on the way and are of independent use:

* `AlgebraicGeometry.Scheme.Modules.isKInjective_mapHomologicalComplex_restrictFunctor_ι`
  (Stacks 08BS) and
  `AlgebraicGeometry.Scheme.Modules.isKInjective_mapHomologicalComplex_restrictFunctor_of_isIso`:
  restriction to an open subscheme, and restriction along an isomorphism, carry K-injective
  complexes to K-injective complexes.
* `AlgebraicGeometry.IsAffineOpen.restrictFromSpecGlobalSectionsIso`: restricting a sheaf of
  `𝒪_X`-modules along `AlgebraicGeometry.IsAffineOpen.fromSpec` and taking `Γ(X, U)`-linear global
  sections is evaluating it at `U`.

## Implementation notes

**Why the comparison is a universal property and not a computation on a chosen complex.** Both
sides are right derived functors of *left* exact functors of sections, so neither is induced by an
exact functor and no formal manipulation of `CategoryTheory.Functor.mapDerivedCategory` reaches the
comparison. Choosing a K-injective representative of the object and evaluating both sides there
does reach it, but only objectwise: the choice is not functorial, so that route proves
`Nonempty (… ≅ …)` and nothing stronger, and a `Nonempty` isomorphism cannot be used to identify a
given morphism.

What is done instead is to recognize the left-hand side as a right derived functor of sections over
`U` in its own right, and let the universal property produce the isomorphism. The two restrictions
are induced by exact functors, so they commute with the localization
(`CategoryTheory.Functor.mapDerivedCategoryFactorsh`) and can be pushed through the unit of derived
global sections on `Spec Γ(X, U)`; the resulting comparison
`AlgebraicGeometry.IsAffineOpen.derivedSectionsSpecUnit` is tested on K-injective complexes only
(`Stacks.Cohomology.Localization.rightDerived_of_kInjectives`, Stacks 070K and 079P), where the
sole factor that is not already invertible is that unit. Then
`CategoryTheory.Functor.rightDerivedNatIso` compares the two right derived functors of the *same*
functor of sections, which is an isomorphism of functors — natural in the object, and pinned down
by `AlgebraicGeometry.IsAffineOpen.derivedSectionsSpecUnit_comp_derivedSectionsSpecIso_hom`.

**Why the restriction has to preserve K-injectivity.** Testing the unit at a K-injective complex
`I` requires the restriction of `I` to `Spec Γ(X, U)` to be K-injective, which is Stacks 08BS. The
repository holds that statement for `AlgebraicGeometry.RingedSpace.restrictModules`
(`AlgebraicGeometry.RingedSpace.isKInjective_restrictComplex`) and the restriction here is
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`. The two functors are *not* definitionally
equal at this pin — the `inv` field of `AlgebraicGeometry.Scheme.Hom.appIso`, through which
Mathlib's restriction acts on scalars, is sealed — so the identification is made along the
isomorphism `AlgebraicGeometry.RingedSpace.restrictModulesIsoRestrictFunctor`. For the second
factor, restriction along the isomorphism `hU.isoSpec.inv`, Stacks 08BS is not available in either
spelling; instead that restriction is a *pushforward* along the inverse isomorphism
(`AlgebraicGeometry.Scheme.Modules.pushforwardIsoRestrictInv`), and a pushforward along an open
immersion preserves K-injectivity by the adjoint criterion of Stacks 08BJ applied to the exact
pullback.

**How the sections are identified.** Composing the two restrictions into one along
`AlgebraicGeometry.IsAffineOpen.fromSpec`, the functor
`Γ(X, U)`-linear-global-sections-after-restriction is *definitionally*
`AlgebraicGeometry.SheafOfModules.evaluation` at the open `hU.fromSpec ''ᵁ ⊤` followed by one
restriction of scalars: the sections of a restriction are the sections over the image open on the
nose, and a composite of restrictions of scalars is the restriction of scalars along the composite
ring map. So the comparison with evaluation at `U` is exactly two statements, the equality of opens
`hU.fromSpec ''ᵁ ⊤ = U` and the identification of that composite ring map with the restriction map
of `𝒪_X` along it; the latter is Mathlib's
`AlgebraicGeometry.IsAffineOpen.fromSpec_app_self`.

**The two models of the derived category.** `CategoryTheory.HasDerivedCategory` carries the
localized category as data and this development fixes `CategoryTheory.HasDerivedCategory.standard`.
The import closure here contains the *global* locally small instances of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, so a `HasDerivedCategory` binder whose
universe is still a metavariable is resolved at the locally small model unless something stops it,
and then the statements below are off by a universe. Raising the priority of the local instance is
what stops it, exactly as in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/AffineDerivedPresentation.lean`.

## References

* [The Stacks Project, Lemma 36.61.8 (09VF)](https://stacks.math.columbia.edu/tag/09VF)
* [The Stacks Project, Tag 08BS](https://stacks.math.columbia.edu/tag/08BS)
* [The Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [The Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [The Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Scheme.Modules

/-! ### Restriction and K-injectivity -/

/-- **Pushforward along an open immersion preserves K-injectivity.** Pullback along an open
immersion is exact — it is `AlgebraicGeometry.Scheme.Modules.restrictFunctor` up to isomorphism by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` — so the adjoint criterion of
Stacks 08BJ applies to `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`.

The K-injectivity hypothesis is an explicit argument, so that the lemma applies at a category with
two definitionally equal spellings without instance search having to choose between them. -/
public theorem isKInjective_mapHomologicalComplex_pushforward {Y Z : Scheme.{u}} (k : Y ⟶ Z)
    [IsOpenImmersion k] (I : CochainComplex Y.Modules ℤ) (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      (((pushforward k).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  have := hI
  have : PreservesFiniteLimits (pullback k) :=
    preservesFiniteLimits_of_natIso (restrictFunctorIsoPullback k)
  have : PreservesFiniteColimits (pullback k) :=
    preservesFiniteColimits_of_natIso (restrictFunctorIsoPullback k)
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact (pushforward k) (pullback k)
    (pullbackPushforwardAdjunction k) I

/-- **Stacks 08BS for restriction along an isomorphism of schemes.** Restriction along an
isomorphism `k` is pushforward along `inv k`, by
`AlgebraicGeometry.Scheme.Modules.pushforwardIsoRestrictInv`, so this is
`AlgebraicGeometry.Scheme.Modules.isKInjective_mapHomologicalComplex_pushforward`. -/
public theorem isKInjective_mapHomologicalComplex_restrictFunctor_of_isIso {Y Z : Scheme.{u}}
    (k : Y ⟶ Z) [IsIso k] (I : CochainComplex Z.Modules ℤ) (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      (((restrictFunctor k).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  have := isKInjective_mapHomologicalComplex_pushforward (inv k) I hI
  CochainComplex.isKInjective_of_iso
    ((NatIso.mapHomologicalComplex
      (pushforwardIsoRestrictInv (inv k) ≪≫ restrictFunctorCongr (IsIso.inv_inv (f := k)))
        (ComplexShape.up ℤ)).app I)

/-- **Stacks 08BS in Mathlib's spelling of restriction to an open subscheme.** The degreewise
restriction to an open subscheme `U` of a K-injective complex of `𝒪_X`-modules is K-injective.

The content is `AlgebraicGeometry.RingedSpace.isKInjective_restrictComplex`, which is Stacks 08BS
for `AlgebraicGeometry.RingedSpace.restrictModules`; the two spellings of restriction are
identified by `AlgebraicGeometry.RingedSpace.restrictModulesIsoRestrictFunctor`. The two functors
are not definitionally equal, and instance search does not cross between the two spellings of the
category of `𝒪_X`-modules either, so both the K-injectivity hypothesis and the two
`CategoryTheory.Functor.PreservesZeroMorphisms` facts are supplied by hand. -/
public theorem isKInjective_mapHomologicalComplex_restrictFunctor_ι {X : Scheme.{u}}
    (U : X.Opens) (I : CochainComplex X.Modules ℤ) (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  let : (RingedSpace.restrictModules X.toRingedSpace U).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ by ext _ _; rfl⟩
  let : (show StrictlyPerfect.OXMod.{u, u} X.toRingedSpace ⥤
        StrictlyPerfect.OXMod.{u, u} (X.toRingedSpace.restrict U.isOpenEmbedding) from
      restrictFunctor U.ι).PreservesZeroMorphisms := ⟨fun _ _ ↦ by ext _ _; rfl⟩
  (CochainComplex.isKInjective_iff_of_iso
    ((NatIso.mapHomologicalComplex (RingedSpace.restrictModulesIsoRestrictFunctor X U)
      (ComplexShape.up ℤ)).app I)).1
    (@RingedSpace.isKInjective_restrictComplex X.toRingedSpace I hI U)

end Scheme.Modules

/-! ### Sections of a restriction to the spectrum of an affine open -/

/-- The restriction maps of the structure sheaf of a scheme between an open and itself are the
identity: the category of opens is a poset, so there is only one morphism to take. -/
public lemma Scheme.presheaf_map_eq_id {Z : Scheme.{u}} {V : Z.Opens} (c : op V ⟶ op V) :
    Z.presheaf.map c = 𝟙 _ := by
  rw [Subsingleton.elim c (𝟙 _), CategoryTheory.Functor.map_id]

/-- **Evaluating a sheaf of modules at an open, with a change of scalars along the restriction map
of an equality of opens, is evaluating it at the other open.** Transport along `h` reduces the
restriction of scalars to the identity, which is `ModuleCat.restrictScalarsId'`.

This is the shape in which `AlgebraicGeometry.IsAffineOpen.restrictFromSpecGlobalSectionsIso` is
proved: the left-hand side there is definitionally an evaluation followed by one restriction of
scalars. -/
public def evaluationRestrictScalarsIso {X : Scheme.{u}} {W U : X.Opens} (h : W = U) :
    ∀ (r : ↥Γ(X, U) →+* ↥Γ(X, W)), r = (X.presheaf.map (eqToHom h).op).hom →
      (SheafOfModules.evaluation X.ringCatSheaf (op W) ⋙ ModuleCat.restrictScalars r ≅
        SheafOfModules.evaluation X.ringCatSheaf (op U)) := by
  subst h
  intro r hr
  have hid : r = RingHom.id _ := by
    rw [hr, Scheme.presheaf_map_eq_id]
    exact CommRingCat.hom_id
  exact Functor.isoWhiskerLeft _ (ModuleCat.restrictScalarsId' r hid) ≪≫ Functor.rightUnitor _

namespace IsAffineOpen

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)

/-- **The scalars of the comparison.** The ring map along which
`AlgebraicGeometry.IsAffineOpen.restrictFromSpecGlobalSectionsIso` changes scalars — identify
`Γ(X, U)` with `Γ(Spec Γ(X, U), ⊤)` and then transport along `hU.fromSpec` — is the restriction map
of `𝒪_X` along `hU.fromSpec ''ᵁ ⊤ = U`.

The content is `AlgebraicGeometry.IsAffineOpen.fromSpec_app_self`, the statement that
`hU.fromSpec` induces the canonical identification on sections over `U`, read through
`AlgebraicGeometry.Scheme.Hom.appIso`; what is left over is a composite of restriction maps of
`𝒪_{Spec Γ(X, U)}` from `⊤` to `⊤`, which is the identity. -/
public lemma fromSpec_scalars_eq :
    ((Scheme.ΓSpecIso Γ(X, U)).inv ≫ Scheme.Hom.appTop (𝟙 (Spec Γ(X, U)))) ≫
        (hU.fromSpec.appIso (⊤ : (Spec Γ(X, U)).Opens)).inv =
      X.presheaf.map (eqToHom hU.fromSpec_image_top).op := by
  rw [Scheme.Hom.id_appTop, Category.comp_id, Iso.comp_inv_eq, Scheme.Hom.appIso_hom',
    Scheme.Hom.map_appLE, Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc,
    ← CategoryTheory.Functor.map_comp, Scheme.presheaf_map_eq_id, Category.comp_id]

/-- **Global sections of a restriction to the spectrum of an affine open are sections over that
open.** Restricting a sheaf of `𝒪_X`-modules along `AlgebraicGeometry.IsAffineOpen.fromSpec` and
taking `Γ(X, U)`-linear global sections on `Spec Γ(X, U)` is evaluating it at `U`.

Both sides are evaluation of the sheaf at an open followed by a restriction of scalars — the
sections of a restriction along an open immersion are the sections over the image open on the
nose, and a composite of restrictions of scalars is the restriction of scalars along the composite
ring map — so the identification is `AlgebraicGeometry.IsAffineOpen.fromSpec_image_top` together
with `AlgebraicGeometry.IsAffineOpen.fromSpec_scalars_eq`. -/
public def restrictFromSpecGlobalSectionsIso :
    Scheme.Modules.restrictFunctor hU.fromSpec ⋙ globalSectionsOver (𝟙 (Spec Γ(X, U))) ≅
      Stacks.Cohomology.sectionsFunctor X U :=
  evaluationRestrictScalarsIso (W := hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens))
    hU.fromSpec_image_top
    ((hU.fromSpec.appIso (⊤ : (Spec Γ(X, U)).Opens)).inv.hom.comp
      ((Scheme.ΓSpecIso Γ(X, U)).inv ≫ Scheme.Hom.appTop (𝟙 (Spec Γ(X, U)))).hom)
    (by rw [← CommRingCat.hom_comp, hU.fromSpec_scalars_eq])

/-- The two restrictions carrying a sheaf of `𝒪_X`-modules to `Spec Γ(X, U)` compose to the
restriction along `AlgebraicGeometry.IsAffineOpen.fromSpec`, which is what
`AlgebraicGeometry.IsAffineOpen.isoSpec_inv_ι` says that morphism is. -/
public def restrictCompIso :
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.inv ≅
      Scheme.Modules.restrictFunctor hU.fromSpec :=
  (Scheme.Modules.restrictFunctorComp hU.isoSpec.inv U.ι).symm

/-- **Sections over an affine open, as the two restrictions followed by global sections on the
spectrum.** Composing `AlgebraicGeometry.IsAffineOpen.restrictCompIso` with
`AlgebraicGeometry.IsAffineOpen.restrictFromSpecGlobalSectionsIso`: restricting a sheaf of
`𝒪_X`-modules to `U`, carrying it to `Spec Γ(X, U)` along
`AlgebraicGeometry.IsAffineOpen.isoSpec` and taking `Γ(X, U)`-linear global sections there is
evaluating it at `U`.

This is the *natural* input of the derived comparison below: it is an isomorphism of functors, so
it identifies the two functors of sections and not merely their values. -/
public def sectionsCompIso :
    (Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.inv) ⋙
        globalSectionsOver (𝟙 (Spec Γ(X, U))) ≅
      Stacks.Cohomology.sectionsFunctor X U :=
  Functor.isoWhiskerRight hU.restrictCompIso (globalSectionsOver (𝟙 (Spec Γ(X, U)))) ≪≫
    hU.restrictFromSpecGlobalSectionsIso

/-- `RΓ(Spec Γ(X, U), (-)|_U)`, the functor on the unbounded derived category of `𝒪_X`-modules
whose value at `E` is `AlgebraicGeometry.IsAffineOpen.derivedSectionsSpec`: restrict to `U`, carry
to `Spec Γ(X, U)` along `AlgebraicGeometry.IsAffineOpen.isoSpec`, take derived global sections.
The first two steps are induced by exact functors, the third is a right derived functor. -/
public abbrev derivedSectionsSpecFunctor :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} Γ(X, U)) :=
  (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory ⋙
    (Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapDerivedCategory ⋙
      derivedGlobalSectionsOver (𝟙 (Spec Γ(X, U)))

/-- `AlgebraicGeometry.IsAffineOpen.sectionsCompIso` read on homotopy categories of cochain
complexes, which is where the universal property of a right derived functor is tested. -/
public def homotopySectionsCompIso :
    ((Scheme.Modules.restrictFunctor U.ι).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapHomotopyCategory
            (ComplexShape.up ℤ)) ⋙
        (globalSectionsOver (𝟙 (Spec Γ(X, U)))).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (Stacks.Cohomology.sectionsFunctor X U).mapHomotopyCategory (ComplexShape.up ℤ) :=
  Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (Scheme.Modules.restrictFunctor U.ι ⋙
          Scheme.Modules.restrictFunctor hU.isoSpec.inv)) (ComplexShape.up ℤ))
      ((globalSectionsOver (𝟙 (Spec Γ(X, U)))).mapHomotopyCategory (ComplexShape.up ℤ)) ≪≫
    Functor.mapHomotopyCategoryCompIso hU.sectionsCompIso (ComplexShape.up ℤ)

/-- **The canonical comparison from termwise sections over `U` to
`AlgebraicGeometry.IsAffineOpen.derivedSectionsSpecFunctor`.** It is the unit
`AlgebraicGeometry.derivedGlobalSectionsOverUnit` of derived global sections on `Spec Γ(X, U)`,
read on the two restrictions: the restrictions are induced by exact functors, so they commute with
the localization up to the canonical isomorphisms
`CategoryTheory.Functor.mapDerivedCategoryFactorsh`, and the termwise sections are identified by
`AlgebraicGeometry.IsAffineOpen.homotopySectionsCompIso`. -/
public def derivedSectionsSpecUnit :
    (Stacks.Cohomology.sectionsFunctor X U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ hU.derivedSectionsSpecFunctor :=
  Functor.whiskerRight hU.homotopySectionsCompIso.inv DerivedCategory.Qh ≫
    Functor.whiskerLeft
      ((Scheme.Modules.restrictFunctor U.ι).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapHomotopyCategory (ComplexShape.up ℤ))
      (derivedGlobalSectionsOverUnit (𝟙 (Spec Γ(X, U)))) ≫
    Functor.whiskerLeft
      ((Scheme.Modules.restrictFunctor U.ι).mapHomotopyCategory (ComplexShape.up ℤ))
      (Functor.whiskerRight
        (Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapDerivedCategoryFactorsh.inv
        (derivedGlobalSectionsOver (𝟙 (Spec Γ(X, U))))) ≫
    Functor.whiskerRight
      (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategoryFactorsh.inv
      ((Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapDerivedCategory ⋙
        derivedGlobalSectionsOver (𝟙 (Spec Γ(X, U))))

/-- **`AlgebraicGeometry.IsAffineOpen.derivedSectionsSpecFunctor` is a right derived functor of
sections over `U`.** Its unit is invertible at a K-injective complex `I`: the two restrictions
carry `I` to a K-injective complex (Stacks 08BS, in the two spellings
`AlgebraicGeometry.Scheme.Modules.isKInjective_mapHomologicalComplex_restrictFunctor_ι` and
`...restrictFunctor_of_isIso`), so the one factor that is not already an isomorphism — the unit of
derived global sections on `Spec Γ(X, U)` — is invertible there by Stacks 070K. That is all the
universal property tests, by
`Stacks.Cohomology.Localization.rightDerived_of_kInjectives`. -/
public theorem isRightDerivedFunctor_derivedSectionsSpecUnit :
    hU.derivedSectionsSpecFunctor.IsRightDerivedFunctor hU.derivedSectionsSpecUnit
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) := by
  apply Stacks.Cohomology.Localization.rightDerived_of_kInjectives
  intro I hI
  have := Scheme.Modules.isKInjective_mapHomologicalComplex_restrictFunctor_of_isIso
    hU.isoSpec.inv _
    (Scheme.Modules.isKInjective_mapHomologicalComplex_restrictFunctor_ι U I hI)
  have : IsIso ((derivedGlobalSectionsOverUnit (𝟙 (Spec Γ(X, U)))).app
      (((Scheme.Modules.restrictFunctor U.ι).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I))) :=
    Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective
      (homotopyGlobalSectionsOver (𝟙 (Spec Γ(X, U))))
      (derivedGlobalSectionsOver (𝟙 (Spec Γ(X, U))))
      (derivedGlobalSectionsOverUnit (𝟙 (Spec Γ(X, U))))
      (((Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
  dsimp only [derivedSectionsSpecUnit]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

/-- **Derived global sections on the spectrum of an affine open are the derived sections over that
open, naturally in the object.** `RΓ(Spec Γ(X, U), (-)|_U) ≅ RΓ(U, -)` as functors on the
unbounded derived category of `𝒪_X`-modules. No hypothesis on the object.

This is the identification that `AlgebraicGeometry.IsAffineOpen.nonempty_iso_derivedSectionsSpec`
asserts only objectwise. Being an isomorphism of functors it *names* the map and is compatible
with morphisms of the object, which is what is needed to compare two specific morphisms through
it; `AlgebraicGeometry.IsAffineOpen.derivedSectionsSpecUnit_comp_derivedSectionsSpecIso_hom` pins
the map down by its defining property.

Both sides are right derived functors of sections over `U` — the left one by
`AlgebraicGeometry.IsAffineOpen.isRightDerivedFunctor_derivedSectionsSpecUnit`, the right one by
construction — so the universal property of a right derived functor,
`CategoryTheory.Functor.rightDerivedNatIso`, identifies them. The underived input is the natural
`AlgebraicGeometry.IsAffineOpen.sectionsCompIso`; no K-injective representative of an object is
chosen anywhere, which is exactly why the result is natural. -/
public def derivedSectionsSpecIso :
    hU.derivedSectionsSpecFunctor ≅ derivedSectionsUnbounded X U :=
  haveI := hU.isRightDerivedFunctor_derivedSectionsSpecUnit
  Functor.rightDerivedNatIso hU.derivedSectionsSpecFunctor (derivedSectionsUnbounded X U)
    hU.derivedSectionsSpecUnit (derivedSectionsUnboundedUnit X U)
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) (Iso.refl _)

/-- **What pins `AlgebraicGeometry.IsAffineOpen.derivedSectionsSpecIso` down.** It is the unique
isomorphism carrying the comparison
`AlgebraicGeometry.IsAffineOpen.derivedSectionsSpecUnit` to the comparison
`AlgebraicGeometry.derivedSectionsUnboundedUnit`: on the termwise sections of a cochain complex
the two agree. -/
public lemma derivedSectionsSpecUnit_comp_derivedSectionsSpecIso_hom
    (K : HomotopyCategory X.Modules (ComplexShape.up ℤ)) :
    hU.derivedSectionsSpecUnit.app K ≫
        hU.derivedSectionsSpecIso.hom.app (DerivedCategory.Qh.obj K) =
      (derivedSectionsUnboundedUnit X U).app K := by
  have := hU.isRightDerivedFunctor_derivedSectionsSpecUnit
  exact (Functor.rightDerivedNatTrans_app hU.derivedSectionsSpecFunctor
    (derivedSectionsUnbounded X U) hU.derivedSectionsSpecUnit (derivedSectionsUnboundedUnit X U)
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) (𝟙 _) K).trans
      (Category.id_comp _)

/-- **Derived global sections on the spectrum of an affine open are the derived sections over that
open.** For every object `E` of the unbounded derived category of `𝒪_X`-modules, the complex
`RΓ(Spec Γ(X, U), E|_U)` of `Γ(X, U)`-modules is `RΓ(U, E)`. No quasi-coherence is needed.

This is the step the proof of Stacks 09VF takes silently after setting `U = Spec A`, and it is the
last input the unconditional
`AlgebraicGeometry.derivedSectionsPseudoCoherentComparison'` was waiting for.

This is `AlgebraicGeometry.IsAffineOpen.derivedSectionsSpecIso`, which is an isomorphism of
functors, read at the object `E`. -/
public theorem nonempty_iso_derivedSectionsSpec (E : DerivedCategory X.Modules) :
    Nonempty (hU.derivedSectionsSpec E ≅ (derivedSectionsUnbounded X U).obj E) :=
  ⟨hU.derivedSectionsSpecIso.app E⟩

end IsAffineOpen

/-! ### Stacks 09VF -/

section Comparison

variable {X S : Scheme.{u}}

/-- **The affine presentation hypothesis of Stacks 09VF.** Let `E` be an object of the derived
category of `𝒪_X`-modules all of whose cohomology sheaves are quasi-coherent. Then on every affine
open `U` the restriction `E|_U` is the complex of quasi-coherent sheaves attached to `RΓ(U, E)`.

This is `AlgebraicGeometry.affineDerivedSectionsPresentation_of_isQuasicoherent_homology` with its
hypothesis discharged by
`AlgebraicGeometry.IsAffineOpen.nonempty_iso_derivedSectionsSpec`. -/
public theorem affineDerivedSectionsPresentation (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent) :
    AffineDerivedSectionsPresentation E :=
  affineDerivedSectionsPresentation_of_isQuasicoherent_homology E hE
    fun _ hU => hU.nonempty_iso_derivedSectionsSpec E

/-- **Stacks 09VF.** Let `f : X ⟶ S` be locally of finite type, let `E` be an object of the derived
category of `𝒪_X`-modules all of whose cohomology sheaves are quasi-coherent, and let `m` be an
integer. Then the following are equivalent:

1. `E` is `m`-pseudo-coherent relative to `S`;
2. there are affine open coverings `S = ⋃ Vⱼ` and `f ⁻¹ᵁ Vⱼ = ⋃ Uⱼᵢ` such that each complex
   `RΓ(Uⱼᵢ, E)` is `m`-pseudo-coherent relative to `Γ(S, Vⱼ)`;
3. for every affine open `V ⊆ S` and every affine open `U ⊆ f ⁻¹ᵁ V`, the complex `RΓ(U, E)` is
   `m`-pseudo-coherent relative to `Γ(S, V)`.

This is `AlgebraicGeometry.derivedSectionsPseudoCoherentComparison'_of_derivedSectionsSpec` with
its hypothesis discharged by
`AlgebraicGeometry.IsAffineOpen.nonempty_iso_derivedSectionsSpec`. -/
@[stacks 09VF]
public theorem derivedSectionsPseudoCoherentComparison' (f : X ⟶ S) [LocallyOfFiniteType f]
    (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent) (m : ℤ) :
    DerivedSectionsPseudoCoherentComparison' f E hE m :=
  derivedSectionsPseudoCoherentComparison'_of_derivedSectionsSpec f E hE
    (fun _ hU => hU.nonempty_iso_derivedSectionsSpec E) m

end Comparison

end AlgebraicGeometry

end
