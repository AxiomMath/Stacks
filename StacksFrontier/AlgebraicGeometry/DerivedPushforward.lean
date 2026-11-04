module

public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentPushforwardAdjoint
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CohomologyOnAnOpenSubspace

/-!
# Unbounded derived pushforward and the Leray comparison

Let `f : X ⟶ Y` be a morphism of schemes and let `V ⊆ Y` be an open. Sections over `V` of a
pushforward are sections over the inverse image,
`Γ(V, f_* ℱ) = Γ(f⁻¹ V, ℱ)`, and this holds on the nose: the two functors
`X.Modules ⥤ ModuleCat Γ(V, 𝒪_Y)` are equal, once the right-hand side is read as a
`Γ(V, 𝒪_Y)`-module by restriction of scalars along `f` (`pushforwardSectionsOnIso` below is
`Iso.refl`). Deriving the two sides produces the *Leray comparison*
`R Γ(f⁻¹ V, -) ⟶ R Γ(V, -) ∘ Rf_*`, the unique transformation whose composite with the
right-derived unit of `Γ(f⁻¹ V, -)` is the canonical transformation assembled from the units of
`R Γ(V, -)` and `Rf_*`. [Stacks, Tag 0D5W] asserts that it is invertible.

This file constructs that comparison on the *unbounded* derived categories, records the
equation characterizing it, and reduces its invertibility to a single statement about
K-injective complexes: `isIso_lerayComparison_iff` says that the comparison is an isomorphism
**if and only if** the right-derived unit of `Γ(V, -)` is invertible at `f_* I` for every
K-injective complex `I` of `𝒪_X`-modules. See the implementation notes for why that hypothesis
is not discharged here.

Nothing in this file re-derives K-injective resolutions or redefines derived pushforward:
`Rf_*` is the already available `Stacks.Duality.derivedPushforward`, and the existence of every
unbounded right derived functor out of `K(𝒪_X)` is
`AlgebraicGeometry.Scheme.Modules.hasRightDerivedFunctor`.

## Main definitions

* `AlgebraicGeometry.sectionsOn` — sections over an open `U ⊆ X`, as `Γ(U, 𝒪_X)`-modules.
* `AlgebraicGeometry.sectionsOnPreimage` — sections over `f⁻¹ V`, as `Γ(V, 𝒪_Y)`-modules.
* `AlgebraicGeometry.derivedSectionsOn`, `AlgebraicGeometry.derivedSectionsOnPreimage` — their
  unbounded total right derived functors, with their units.
* `AlgebraicGeometry.derivedPushforwardUnit` — the canonical unit exhibiting
  `Stacks.Duality.derivedPushforward` as a right derived functor.
* `AlgebraicGeometry.lerayUnit` and `AlgebraicGeometry.lerayComparison` — the canonical
  transformation `Γ(f⁻¹ V, -) ⟶ Qh ⋙ (Rf_* ⋙ RΓ(V, -))` and the comparison of derived
  functors it induces.

## Main results

* `AlgebraicGeometry.lerayComparison_fac` — the equation characterizing `lerayComparison`.
* `AlgebraicGeometry.lerayComparison_ext` — the uniqueness that equation gives.
* `AlgebraicGeometry.isIso_lerayComparison_iff` — the comparison is invertible exactly when the
  unit of `RΓ(V, -)` is invertible at the pushforward of every K-injective complex.
* `AlgebraicGeometry.isIso_lerayComparison_of_isKInjective_pushforward` — it is invertible when
  `f_*` preserves K-injectivity.
* `AlgebraicGeometry.isIso_lerayComparison_of_preservesFiniteLimits_pullback` — it is invertible
  when `f^*` is exact, i.e. for a flat morphism.

## Implementation notes

The derived categories in force are the locally small ones,
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` and `ModuleCat.hasDerivedCategory`; as in
`StacksFrontier/AlgebraicGeometry/DerivedGlobalSections.lean`, no file in this chain may open with
`attribute [local instance] HasDerivedCategory.standard`, because at the standard model the two
sides are different categories and the morphisms of `D(𝒪_X)` sit a universe above its objects.

`sectionsOn` is stated with source `X.Modules` and body
`SheafOfModules.evaluation X.ringCatSheaf (op U)`. The two spellings of the source category are
definitionally equal with separately declared `Preadditive` instances that instance search does
not cross, so each declaration stays inside one view.

**What is not proved here, and why the remaining hypothesis is not vacuous.** The usual way to
collapse a composite of derived functors is to show that the inner functor carries K-injective
complexes to K-injective complexes — that is the adjoint criterion [Stacks, Tag 08BJ],
available as `CochainComplex.isKInjective_mapHomologicalComplex_of_exact`, and it is how
[Stacks, Tag 0D5V] is proved, as `Stacks.Cohomology.OpenSubspace.cohomologyOnOpenIsoRestriction`,
the left adjoint of restriction to an open subspace being extension by zero, which is exact. That
route is **not** available for pushforward: the left adjoint of
`AlgebraicGeometry.Scheme.Modules.pushforward f` is `Scheme.Modules.pullback f`, which is a
tensor product and is not exact, and direct image genuinely fails to preserve K-injectivity.
For the closed immersion `i : Spec k ⟶ Spec k[x]/(x²)`, the complex `k` in degree `0` is
K-injective on the source (`k` is an injective `k`-module) while `i_* k = k` is not injective
over `k[x]/(x²)`, and a complex concentrated in one degree is K-injective only if that object is
injective. So the hypothesis of `isIso_lerayComparison_iff` is strictly weaker than
K-injectivity of `f_* I`, and that weaker statement is the content of Tag 0D5W. The Stacks
proof obtains it from Tag 0D5T for `X ⟶ Y ⟶ Z` with `Z` a one-point ringed space, hence from
the derived adjunction `Lf^* ⊣ Rf_*` of [Stacks, Tag 079W]; the left derived pullback `Lf^*`,
which needs K-flat resolutions of complexes of module sheaves, does not exist in this library
yet, and is what the invertibility statement is waiting on.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0D5V](https://stacks.math.columbia.edu/tag/0D5V)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor Opposite
open Stacks.Cohomology.Localization (derivedUnit_isIsoOnKInjective natTrans_isIso_of_kInjectives)

universe u

namespace AlgebraicGeometry

/-! ### Sections over an open, and over the inverse image of an open -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)

/-- **Sections over the inverse image of an open.** Sections over `f⁻¹ V` of a sheaf of
`𝒪_X`-modules, regarded as a module over `Γ(V, 𝒪_Y)` by restriction of scalars along
`f.app V : Γ(V, 𝒪_Y) ⟶ Γ(f⁻¹ V, 𝒪_X)`. This is the target in which Tag 0D5W compares derived
sections on `X` with derived sections on `Y`. -/
abbrev sectionsOnPreimage : X.Modules ⥤ ModuleCat.{u} Γ(Y, V) :=
  sectionsOn X (f ⁻¹ᵁ V) ⋙ ModuleCat.restrictScalars (f.app V).hom

/-- Sections over `f⁻¹ V`, as `Γ(V, 𝒪_Y)`-modules, form an additive functor. -/
instance sectionsOnPreimage_additive : (sectionsOnPreimage f V).Additive where
  map_add := rfl

/-! ### The three unbounded right derived functors -/

/-- Sections over `U ⊆ X` read on the homotopy category of cochain complexes of `𝒪_X`-modules,
with values in `D(Γ(U, 𝒪_X))`. Its right derived functor is `derivedSectionsOn`. -/
abbrev homotopySectionsOn (X : Scheme.{u}) (U : X.Opens) :
    HomotopyCategory X.Modules (ComplexShape.up ℤ) ⥤ DerivedCategory (ModuleCat.{u} Γ(X, U)) :=
  (sectionsOn X U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- Sections over `U` on the homotopy category admit a right derived functor with respect to
quasi-isomorphisms. -/
instance homotopySectionsOn_hasRightDerivedFunctor (X : Scheme.{u}) (U : X.Opens) :
    (homotopySectionsOn X U).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
  Scheme.Modules.hasRightDerivedFunctor X _

/-- **Unbounded derived sections over an open** `RΓ(U, -) : D(𝒪_X) ⥤ D(Γ(U, 𝒪_X))`. -/
abbrev derivedSectionsOn (X : Scheme.{u}) (U : X.Opens) :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} Γ(X, U)) :=
  (homotopySectionsOn X U).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))

/-- The canonical comparison from termwise sections over `U` to their right derived functor. -/
abbrev derivedSectionsOnUnit (X : Scheme.{u}) (U : X.Opens) :
    homotopySectionsOn X U ⟶ DerivedCategory.Qh ⋙ derivedSectionsOn X U :=
  (homotopySectionsOn X U).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))

/-- Sections over `f⁻¹ V` read on the homotopy category of cochain complexes of `𝒪_X`-modules,
with values in `D(Γ(V, 𝒪_Y))`. -/
abbrev homotopySectionsOnPreimage :
    HomotopyCategory X.Modules (ComplexShape.up ℤ) ⥤ DerivedCategory (ModuleCat.{u} Γ(Y, V)) :=
  (sectionsOnPreimage f V).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- Sections over `f⁻¹ V` on the homotopy category admit a right derived functor with respect
to quasi-isomorphisms. -/
instance homotopySectionsOnPreimage_hasRightDerivedFunctor :
    (homotopySectionsOnPreimage f V).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
  Scheme.Modules.hasRightDerivedFunctor X _

/-- **Unbounded derived sections over an inverse image**
`RΓ(f⁻¹ V, -) : D(𝒪_X) ⥤ D(Γ(V, 𝒪_Y))`. -/
abbrev derivedSectionsOnPreimage :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} Γ(Y, V)) :=
  (homotopySectionsOnPreimage f V).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))

/-- The canonical comparison from termwise sections over `f⁻¹ V` to their right derived
functor. -/
abbrev derivedSectionsOnPreimageUnit :
    homotopySectionsOnPreimage f V ⟶ DerivedCategory.Qh ⋙ derivedSectionsOnPreimage f V :=
  (homotopySectionsOnPreimage f V).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))

/-- The canonical comparison exhibiting `Stacks.Duality.derivedPushforward` as the unbounded
right derived functor of direct image. -/
abbrev derivedPushforwardUnit :
    Stacks.Duality.homotopyPushforward f ⟶
      DerivedCategory.Qh ⋙ Stacks.Duality.derivedPushforward f :=
  (Stacks.Duality.homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))

/-! ### The Leray comparison -/

/-- **Sections of a pushforward are sections on the inverse image.** The identification
`Γ(V, f_* ℱ) = Γ(f⁻¹ V, ℱ)` of `Γ(V, 𝒪_Y)`-modules, which holds on the nose: it is the identity
natural transformation. -/
def pushforwardSectionsOnIso :
    Scheme.Modules.pushforward f ⋙ sectionsOn Y V ≅ sectionsOnPreimage f V :=
  Iso.refl _

/-- The canonical transformation from termwise sections over `f⁻¹ V` to the composite of the
two chosen derived functors: the identification `Γ(V, f_* -) = Γ(f⁻¹ V, -)`, followed by the
unit of `RΓ(V, -)` and then the unit of `Rf_*`. -/
def lerayUnit :
    homotopySectionsOnPreimage f V ⟶ DerivedCategory.Qh ⋙
      (Stacks.Duality.derivedPushforward f ⋙ derivedSectionsOn Y V) :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (pushforwardSectionsOnIso f V)
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft
      ((Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
      (derivedSectionsOnUnit Y V) ≫
    Functor.whiskerRight (derivedPushforwardUnit f) (derivedSectionsOn Y V)

/-- **The Leray comparison** `RΓ(f⁻¹ V, -) ⟶ RΓ(V, -) ∘ Rf_*`, the transformation induced by
`lerayUnit` through the universal property of the right derived functor of sections over
`f⁻¹ V`. By `lerayComparison_fac` its composite with `derivedSectionsOnPreimageUnit` is
`lerayUnit`, and by `lerayComparison_ext` that equation determines it. [Stacks, Tag 0D5W]
asserts that it is an isomorphism; see `isIso_lerayComparison_iff`. -/
def lerayComparison :
    derivedSectionsOnPreimage f V ⟶
      Stacks.Duality.derivedPushforward f ⋙ derivedSectionsOn Y V :=
  (derivedSectionsOnPreimage f V).rightDerivedDesc (derivedSectionsOnPreimageUnit f V)
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) _ (lerayUnit f V)

/-- The equation characterizing the Leray comparison: composing it with the unit of
`RΓ(f⁻¹ V, -)` recovers `lerayUnit`. -/
theorem lerayComparison_fac :
    derivedSectionsOnPreimageUnit f V ≫
        Functor.whiskerLeft DerivedCategory.Qh (lerayComparison f V) =
      lerayUnit f V :=
  (derivedSectionsOnPreimage f V).rightDerived_fac (derivedSectionsOnPreimageUnit f V)
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) _ (lerayUnit f V)

/-- The equation of `lerayComparison_fac` determines the Leray comparison: two transformations
out of `RΓ(f⁻¹ V, -)` that agree after composition with the unit are equal. -/
theorem lerayComparison_ext
    {G : DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} Γ(Y, V))}
    (τ₁ τ₂ : derivedSectionsOnPreimage f V ⟶ G)
    (h : derivedSectionsOnPreimageUnit f V ≫ Functor.whiskerLeft DerivedCategory.Qh τ₁ =
      derivedSectionsOnPreimageUnit f V ≫ Functor.whiskerLeft DerivedCategory.Qh τ₂) :
    τ₁ = τ₂ :=
  (derivedSectionsOnPreimage f V).rightDerived_ext (derivedSectionsOnPreimageUnit f V)
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) _ _ _ h

/-- At a K-injective complex `I` of `𝒪_X`-modules, `lerayUnit` is invertible exactly when the
unit of `RΓ(V, -)` is invertible at the pushforward `f_* I`: the other two factors of
`lerayUnit` are invertible there, the first because it is a component of an isomorphism and the
third because the unit of `Rf_*` is invertible at a K-injective complex. -/
theorem isIso_lerayUnit_app_iff (I : CochainComplex X.Modules ℤ) [I.IsKInjective] :
    IsIso ((lerayUnit f V).app
        ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I)) ↔
      IsIso ((derivedSectionsOnUnit Y V).app
        (((Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I))) := by
  have hunit := derivedUnit_isIsoOnKInjective (Stacks.Duality.homotopyPushforward f)
    (Stacks.Duality.derivedPushforward f) (derivedPushforwardUnit f) I
  have hmap : IsIso ((derivedSectionsOn Y V).map ((derivedPushforwardUnit f).app
    ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I))) := inferInstance
  dsimp only [lerayUnit, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [isIso_comp_left_iff, isIso_comp_right_iff]

/-- **The formal half of [Stacks, Tag 0D5W].** The Leray comparison
`RΓ(f⁻¹ V, -) ⟶ RΓ(V, -) ∘ Rf_*` is an isomorphism **if and only if** the unit of `RΓ(V, -)`
is invertible at `f_* I` for every K-injective complex `I` of `𝒪_X`-modules.

Both implications are the universal property of the right derived functor of
`Γ(f⁻¹ V, -)` together with the fact that its unit, and the unit of `Rf_*`, are invertible at
K-injective complexes; the reduction to K-injective complexes is possible because every complex
of `𝒪_X`-modules admits a quasi-isomorphism into one. The right-hand condition is the
geometric content of the tag and is not proved here — see the implementation notes. -/
theorem isIso_lerayComparison_iff :
    IsIso (lerayComparison f V) ↔
      ∀ (I : CochainComplex X.Modules ℤ) [I.IsKInjective],
        IsIso ((derivedSectionsOnUnit Y V).app
          (((Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I))) := by
  have key : ∀ (I : CochainComplex X.Modules ℤ) [I.IsKInjective],
      IsIso ((lerayComparison f V).app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I))) ↔
        IsIso ((lerayUnit f V).app
          ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I)) := by
    intro I _
    have := derivedUnit_isIsoOnKInjective (homotopySectionsOnPreimage f V)
      (derivedSectionsOnPreimage f V) (derivedSectionsOnPreimageUnit f V) I
    have heq : (derivedSectionsOnPreimageUnit f V).app
          ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I) ≫
        (lerayComparison f V).app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I)) =
          (lerayUnit f V).app
            ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I) := by
      simpa using NatTrans.congr_app (lerayComparison_fac f V)
        ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I)
    rw [← heq, isIso_comp_left_iff]
  refine ⟨fun _ I _ => ?_, fun h => natTrans_isIso_of_kInjectives _ fun I _ => ?_⟩
  · exact (isIso_lerayUnit_app_iff f V I).1 ((key I).1 inferInstance)
  · exact (key I).2 ((isIso_lerayUnit_app_iff f V I).2 (h I))

/-- **Leray when direct image preserves K-injectivity.** If `f_*` carries K-injective complexes
of `𝒪_X`-modules to K-injective complexes of `𝒪_Y`-modules then the Leray comparison is an
isomorphism, since the unit of a right derived functor is invertible at a K-injective
complex. -/
theorem isIso_lerayComparison_of_isKInjective_pushforward
    (h : ∀ I : CochainComplex X.Modules ℤ, I.IsKInjective →
      CochainComplex.IsKInjective
        (((Scheme.Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    IsIso (lerayComparison f V) := by
  rw [isIso_lerayComparison_iff]
  intro I hI
  have := h I hI
  exact derivedUnit_isIsoOnKInjective (homotopySectionsOn Y V) (derivedSectionsOn Y V)
    (derivedSectionsOnUnit Y V)
    (((Scheme.Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)

/-- **Leray for a morphism with exact pullback, in particular a flat morphism.** If
`f^* : Y.Modules ⥤ X.Modules` preserves finite limits — it always preserves finite colimits,
being a left adjoint, so this is exactly exactness of `f^*`, i.e. flatness of `f` — then the
Leray comparison `RΓ(f⁻¹ V, -) ⟶ RΓ(V, -) ∘ Rf_*` is an isomorphism.

This is the adjoint criterion for K-injectivity [Stacks, Tag 08BJ] applied to
`f^* ⊣ f_*`, fed to `isIso_lerayComparison_of_isKInjective_pushforward`. It is a special case
of [Stacks, Tag 0D5W], which asserts the same with no hypothesis on `f` at all; the general
case is not available here, pullback being a tensor product and hence inexact in general. -/
theorem isIso_lerayComparison_of_preservesFiniteLimits_pullback
    [Limits.PreservesFiniteLimits (Scheme.Modules.pullback f)] :
    IsIso (lerayComparison f V) :=
  isIso_lerayComparison_of_isKInjective_pushforward f V fun I hI =>
    have := hI
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _
      (Scheme.Modules.pullbackPushforwardAdjunction f) I

end AlgebraicGeometry

end
