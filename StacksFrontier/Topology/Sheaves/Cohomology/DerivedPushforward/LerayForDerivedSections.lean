module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionUnconditional
import StacksCore.Tactic.StacksAttribute

/-!
# Derived sections of an unbounded derived pushforward

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `V ⊆ Y` be open.  Sections
over `V` of a direct image are sections over the inverse image, `Γ(V, f_* ℱ) = Γ(f⁻¹ V, ℱ)`, and
this holds on the nose once the right-hand side is read as a `Γ(V, 𝒪_Y)`-module by restriction of
scalars along `f^♯`: `pushforwardPreimageSectionsIso` is the identity.  Deriving the two sides
produces the *Leray comparison*

`R Γ(f⁻¹ V, -) ⟶ R Γ(V, -) ∘ Rf_*`,

the unique transformation whose composite with the right-derived unit of `Γ(f⁻¹ V, -)` is the
transformation assembled from the units of `R Γ(V, -)` and `Rf_*`.  This file proves it
invertible, with **no hypothesis on `f`**, which is [Stacks, Tag 0D5W]: at `V = ⊤` it says that
`R Γ(Y, -) ∘ Rf_*` and `R Γ(X, -)` agree as functors `D(𝒪_X) ⥤ D(Γ(Y, 𝒪_Y))`.

## Main definitions

* `Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen` — sections over an open `U ⊆ X`, as
  `Γ(U, 𝒪_X)`-modules.
* `Stacks.Cohomology.DerivedSectionsLeray.preimageSections` — sections over `f⁻¹ V`, as
  `Γ(V, 𝒪_Y)`-modules.
* `Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen` and
  `Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections` — their unbounded total right
  derived functors, with their units.
* `Stacks.Cohomology.DerivedSectionsLeray.lerayUnit` and
  `Stacks.Cohomology.DerivedSectionsLeray.lerayComparison` — the canonical transformation
  `Γ(f⁻¹ V, -) ⟶ Qh ⋙ (Rf_* ⋙ RΓ(V, -))` and the comparison of derived functors it induces.
* `Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsPushforwardIso` — the resulting natural
  isomorphism.

## Main results

* `Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_fac` and
  `Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_ext` — the equation characterizing the
  Leray comparison, and the uniqueness it gives.
* `Stacks.Cohomology.DerivedSectionsLeray.isIso_lerayComparison` — **Tag 0D5W over an open**: the
  Leray comparison is an isomorphism.
* `Stacks.Cohomology.DerivedSectionsLeray.isIso_lerayComparison_top` — **Tag 0D5W for global
  sections**.

## Implementation notes

*Where the content sits.*  By the universal property of `RΓ(f⁻¹ V, -)` the comparison is
invertible as soon as `lerayUnit` is invertible at every K-injective complex `ℐ` of
`𝒪_X`-modules, and there its outer two factors are invertible for free — the first is a component
of an isomorphism and the third is the image of the unit of `Rf_*`, which a K-injective complex
computes.  So everything reduces to one statement: *the unit of `RΓ(V, -)` is invertible at
`f_* ℐ`*.  This is `isIso_derivedSectionsOverOpenUnit_app_pushforward`, and it is proved from the
unconditional composition formula
`Stacks.Cohomology.DerivedPushforwardComposition.pushforwardComputesDerived` (Tag 0D5T) rather
than from preservation of K-injectivity, which direct image genuinely fails: for the closed
immersion `i : Spec k ⟶ Spec k[x]/(x²)` the complex `k` in degree `0` is K-injective on the
source while `i_* k = k` is not an injective `k[x]/(x²)`-module.

*The space that turns sections into a pushforward.*  Tag 0D5T applies to a composite
`X ⟶ Y ⟶ Z`, so `Γ(V, -)` must be exhibited as a direct image followed by an exact functor.  The
source takes `Z` to be a singleton ringed space with `Γ(Z, 𝒪_Z) = Γ(Y, 𝒪_Y)`, which gives the
global statement, and then deduces the statement over an open from Tag 08FE.  Here both are
obtained at once by taking `Z` to be the *Sierpiński space* — `ULift Prop` with the topology whose
proper nonempty open is `{True}` — carrying the direct image of `𝒪_Y` along the map classifying
`V`.  Then `openClassifierPoint`, that one proper open, pulls back to `V`, so
`openClassifierSectionsIso` is the identity: `Γ(V, -)` *is* the direct image along
`toOpenClassifier` followed by sections over `openClassifierPoint`.  Sections over an open with at
most one point are exact, because a covering sieve of such an open must contain the open itself,
so local surjectivity there is surjectivity; that is
`preservesEpimorphisms_evaluation_of_subsingleton`.  With `V = ⊤` the classifying map is constant
and `Z` is a singleton up to the empty open, recovering the source's argument.

*No instance baggage.*  The three right derived functors exist unconditionally, because sheaves of
modules on a ringed space form a Grothendieck abelian category and so every complex admits a
quasi-isomorphism into a K-injective one
(`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective`, Tag 079P).
They are therefore supplied as instances here and appear in no statement as a hypothesis.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPushforward derivedPushforwardUnit exists_quasiIso_isKInjective
    isIso_derivedPushforwardUnit_app_of_isKInjective
    isRightDerivedFunctor_of_isIso_app_isKInjective)

namespace Stacks.Cohomology.DerivedSectionsLeray

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### Sections over an open, and over the inverse image of an open -/

/-- **Sections over an open.**  Sections over `U ⊆ X` of a sheaf of `𝒪_X`-modules, as a module
over the ring `Γ(U, 𝒪_X)` of functions on `U`. -/
abbrev sectionsOverOpen (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    SheafOfModules.{u} (structureSheafRing X) ⥤
      ModuleCat.{u} ((structureSheafRing X).obj.obj (op U)) :=
  SheafOfModules.evaluation (structureSheafRing X) (op U)

/-- Sections over an open form an additive functor: addition of sections of a sheaf of modules is
computed open by open. -/
instance sectionsOverOpen_additive (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    (sectionsOverOpen X U).Additive where
  map_add := rfl

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y.carrier)

/-- **Sections over the inverse image of an open.**  Sections over `f⁻¹ V` of a sheaf of
`𝒪_X`-modules, regarded as a module over `Γ(V, 𝒪_Y)` by restriction of scalars along
`f^♯ : Γ(V, 𝒪_Y) ⟶ Γ(f⁻¹ V, 𝒪_X)`.  This is the target in which Tag 0D5W compares derived
sections on `X` with derived sections on `Y`. -/
abbrev preimageSections :
    SheafOfModules.{u} (structureSheafRing X) ⥤
      ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V)) :=
  sectionsOverOpen X ((opensMap f).obj V) ⋙
    ModuleCat.restrictScalars ((structureSheafHom f).hom.app (op V)).hom

/-- Sections over an inverse image, with scalars restricted, form an additive functor. -/
instance preimageSections_additive : (preimageSections f V).Additive where
  map_add := rfl

/-! ### The two unbounded right derived functors -/

/-- Sections over `U ⊆ X` read on the homotopy category of cochain complexes of `𝒪_X`-modules,
with values in `D(Γ(U, 𝒪_X))`.  Its right derived functor is `derivedSectionsOverOpen`. -/
abbrev homotopySectionsOverOpen (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U))) :=
  (sectionsOverOpen X U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- Sections over `f⁻¹ V` read on the homotopy category of cochain complexes of `𝒪_X`-modules,
with values in `D(Γ(V, 𝒪_Y))`. -/
abbrev homotopyPreimageSections :
    HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) :=
  (preimageSections f V).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- K-injective resolutions compute every right derived functor out of the homotopy category of
complexes of modules on a ringed space, pointwise.  This is Tag 079P, through the K-injective
resolutions of `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective`
and Mathlib's criterion for a pointwise right derived functor along them. -/
instance moduleSheaves_hasPointwiseRightDerivedFunctor (Z : RingedSpace.{u, u}) {H : Type (u + 1)}
    [Category.{u + 1} H]
    (F : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ) ⥤ H) :
    F.HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u, u + 1, u + 1, u + 1, u + 1, u + 1} F (exists_quasiIso_isKInjective Z)).1

/-- Every functor out of the homotopy category of complexes of modules on a ringed space has an
unbounded right derived functor. -/
instance moduleSheaves_hasRightDerivedFunctor (Z : RingedSpace.{u, u}) {H : Type (u + 1)}
    [Category.{u + 1} H]
    (F : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ) ⥤ H) :
    F.HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Z)) (ComplexShape.up ℤ)) :=
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

/-- **Unbounded derived sections over an open** `RΓ(U, -) : D(𝒪_X) ⥤ D(Γ(U, 𝒪_X))`. -/
abbrev derivedSectionsOverOpen (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op U))) :=
  (homotopySectionsOverOpen X U).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))

/-- The canonical comparison from termwise sections over `U` to their right derived functor. -/
abbrev derivedSectionsOverOpenUnit (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    homotopySectionsOverOpen X U ⟶ DerivedCategory.Qh ⋙ derivedSectionsOverOpen X U :=
  (homotopySectionsOverOpen X U).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))

/-- **Unbounded derived sections over an inverse image**
`RΓ(f⁻¹ V, -) : D(𝒪_X) ⥤ D(Γ(V, 𝒪_Y))`. -/
abbrev derivedPreimageSections :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) :=
  (homotopyPreimageSections f V).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))

/-- The canonical comparison from termwise sections over `f⁻¹ V` to their right derived
functor. -/
abbrev derivedPreimageSectionsUnit :
    homotopyPreimageSections f V ⟶ DerivedCategory.Qh ⋙ derivedPreimageSections f V :=
  (homotopyPreimageSections f V).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))

/-! ### Sections over an open as a direct image to the Sierpiński space -/

/-- The classifying map of an open `V ⊆ Y`: the continuous map to the Sierpiński space sending a
point to the proposition that it lies in `V`. -/
private def openClassifierMap (Y : RingedSpace.{u, u}) (V : Opens Y.carrier) :
    Y.carrier ⟶ TopCat.of (ULift.{u} Prop) :=
  TopCat.ofHom ⟨fun y => ⟨y ∈ V⟩, continuous_uliftUp.comp (continuous_Prop.mpr V.isOpen)⟩

/-- The Sierpiński space carrying the direct image of `𝒪_Y` along the classifying map of `V`. -/
private def openClassifierSpace (Y : RingedSpace.{u, u}) (V : Opens Y.carrier) :
    RingedSpace.{u, u} where
  carrier := TopCat.of (ULift.{u} Prop)
  presheaf := (Opens.map (openClassifierMap Y V)).op ⋙ Y.presheaf
  IsSheaf := TopCat.Sheaf.pushforward_sheaf_of_sheaf (openClassifierMap Y V) Y.IsSheaf

/-- The morphism of ringed spaces classifying `V ⊆ Y`, with the identity on structure sheaves. -/
private def toOpenClassifier (Y : RingedSpace.{u, u}) (V : Opens Y.carrier) :
    Y ⟶ openClassifierSpace Y V :=
  ⟨{ base := openClassifierMap Y V, c := 𝟙 _ }⟩

/-- The proper nonempty open of the Sierpiński space.  Its inverse image under the classifying
map of `V` is `V`. -/
private def openClassifierPoint (Y : RingedSpace.{u, u}) (V : Opens Y.carrier) :
    Opens (openClassifierSpace Y V).carrier :=
  ⟨{p | p.down}, continuous_Prop.mp continuous_uliftDown⟩

private lemma openClassifierPoint_eq {Y : RingedSpace.{u, u}} {V : Opens Y.carrier}
    (p : openClassifierPoint Y V) : p = ⟨⟨True⟩, trivial⟩ :=
  Subtype.ext <| ULift.ext _ _ <| propext ⟨fun _ => trivial, fun _ => p.property⟩

private instance (Y : RingedSpace.{u, u}) (V : Opens Y.carrier) :
    Subsingleton (openClassifierPoint Y V) :=
  ⟨fun a b => openClassifierPoint_eq a |>.trans (openClassifierPoint_eq b).symm⟩

private instance (Y : RingedSpace.{u, u}) (V : Opens Y.carrier) :
    Nonempty (openClassifierPoint Y V) := ⟨⟨⟨True⟩, trivial⟩⟩

/-- **Sections over an open with at most one point are exact**: taking sections over such an open
preserves epimorphisms of sheaves of modules. -/
private theorem preservesEpimorphisms_evaluation_of_subsingleton {Z : RingedSpace.{u, u}}
    (W : Opens Z.carrier) [Subsingleton W] [Nonempty W] :
    (SheafOfModules.evaluation.{u} (structureSheafRing Z) (op W)).PreservesEpimorphisms where
  preserves {M N} φ hφ := by
    rw [ModuleCat.epi_iff_surjective]
    intro t
    have hloc := (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u}
      ((SheafOfModules.toSheaf.{u} (structureSheafRing Z)).map φ)).mpr inferInstance
    obtain ⟨x, hx⟩ := ‹Nonempty W›
    obtain ⟨U, i, ⟨s, hs⟩, hxU⟩ := Presheaf.imageSieve_mem (Opens.grothendieckTopology Z.carrier)
      ((SheafOfModules.toSheaf.{u} (structureSheafRing Z)).map φ).hom t x hx
    have hUW : U = W := le_antisymm (leOfHom i) fun y hy => by
      obtain rfl : y = x := congrArg Subtype.val (Subsingleton.elim (⟨y, hy⟩ : W) ⟨x, hx⟩)
      exact hxU
    subst U
    obtain rfl : i = 𝟙 W := Subsingleton.elim _ _
    exact ⟨s, by
      change φ.val.app (op W) s = t
      rwa [op_id, (((SheafOfModules.toSheaf.{u} (structureSheafRing Z)).obj N).obj).map_id] at hs⟩

/-- Sections over the proper open of the Sierpiński space attached to `V ⊆ Y`. -/
private abbrev openClassifierSections (Y : RingedSpace.{u, u}) (V : Opens Y.carrier) :
    SheafOfModules.{u} (structureSheafRing (openClassifierSpace Y V)) ⥤
      ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V)) :=
  sectionsOverOpen (openClassifierSpace Y V) (openClassifierPoint Y V)

private instance openClassifierSections_additive
    (Y : RingedSpace.{u, u}) (V : Opens Y.carrier) :
    (openClassifierSections Y V).Additive where
  map_add := rfl

private instance openClassifierSections_preservesEpimorphisms
    (Y : RingedSpace.{u, u}) (V : Opens Y.carrier) :
    (openClassifierSections Y V).PreservesEpimorphisms :=
  preservesEpimorphisms_evaluation_of_subsingleton _

private instance openClassifierSections_preservesHomology
    (Y : RingedSpace.{u, u}) (V : Opens Y.carrier) :
    (openClassifierSections Y V).PreservesHomology :=
  have : ∀ {M N : SheafOfModules.{u} (structureSheafRing (openClassifierSpace Y V))} (φ : M ⟶ N),
      PreservesLimit (parallelPair φ 0) (openClassifierSections Y V) := fun {_ _} φ =>
    show PreservesLimit (parallelPair φ 0)
      (sectionsOverOpen (openClassifierSpace Y V) (openClassifierPoint Y V)) from inferInstance
  Functor.preservesHomology_of_preservesEpis_and_kernels _

private instance openClassifierSections_preservesFiniteColimits
    (Y : RingedSpace.{u, u}) (V : Opens Y.carrier) :
    PreservesFiniteColimits (openClassifierSections Y V) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

private instance openClassifierSections_preservesFiniteLimits
    (Y : RingedSpace.{u, u}) (V : Opens Y.carrier) :
    PreservesFiniteLimits (openClassifierSections Y V) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

/-- **Sections over `V` are a direct image followed by sections over a point.**  The proper open
of the Sierpiński space pulls back to `V`, so the two functors are equal on the nose. -/
private def openClassifierSectionsIso (Y : RingedSpace.{u, u}) (V : Opens Y.carrier) :
    modulePushforward (toOpenClassifier Y V) ⋙ openClassifierSections Y V ≅
      sectionsOverOpen Y V :=
  Iso.refl _

private def openClassifierHomotopyIso (Y : RingedSpace.{u, u}) (V : Opens Y.carrier) :
    homotopySectionsOverOpen Y V ≅
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pushforwardToDerivedCategory
          (toOpenClassifier Y V) ⋙
        (openClassifierSections Y V).mapDerivedCategory :=
  (Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso (openClassifierSectionsIso Y V) (ComplexShape.up ℤ))
      DerivedCategory.Qh).symm ≪≫
    Functor.isoWhiskerLeft
      ((modulePushforward (toOpenClassifier Y V)).mapHomotopyCategory (ComplexShape.up ℤ))
      (openClassifierSections Y V).mapDerivedCategoryFactorsh.symm

/-- The comparison exhibiting `Rg_*` followed by sections over a point as a right derived functor
of sections over `V`, where `g` classifies `V`. -/
private def openClassifierDerivedUnit (Y : RingedSpace.{u, u}) (V : Opens Y.carrier) :
    homotopySectionsOverOpen Y V ⟶ DerivedCategory.Qh ⋙
      (derivedPushforward (toOpenClassifier Y V) ⋙
        (openClassifierSections Y V).mapDerivedCategory) :=
  (openClassifierHomotopyIso Y V).hom ≫
    Functor.whiskerRight (derivedPushforwardUnit (toOpenClassifier Y V))
      (openClassifierSections Y V).mapDerivedCategory

/-- Wherever the unit of `Rg_*` is invertible, so is `openClassifierDerivedUnit`. -/
private theorem isIso_openClassifierDerivedUnit_app
    (Y : RingedSpace.{u, u}) (V : Opens Y.carrier)
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
    (hK : IsIso ((derivedPushforwardUnit (toOpenClassifier Y V)).app K)) :
    IsIso ((openClassifierDerivedUnit Y V).app K) :=
  IsIso.comp_isIso' inferInstance
    (inferInstance : IsIso ((openClassifierSections Y V).mapDerivedCategory.map
      ((derivedPushforwardUnit (toOpenClassifier Y V)).app K)))

private theorem isRightDerivedFunctor_openClassifier
    (Y : RingedSpace.{u, u}) (V : Opens Y.carrier) :
    (derivedPushforward (toOpenClassifier Y V) ⋙
        (openClassifierSections Y V).mapDerivedCategory).IsRightDerivedFunctor
      (openClassifierDerivedUnit Y V)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_of_isIso_app_isKInjective.{u, u + 1, u + 1, u + 1, u + 1, u + 1}
    _ (exists_quasiIso_isKInjective Y) DerivedCategory.Qh _ _ fun J hJ =>
      isIso_openClassifierDerivedUnit_app Y V _
        (isIso_derivedPushforwardUnit_app_of_isKInjective (toOpenClassifier Y V) J hJ)

/-- **The unit of `RΓ(V, -)` is invertible at the direct image of a K-injective complex.** -/
private theorem isIso_derivedSectionsOverOpenUnit_app_pushforward
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (hI : I.IsKInjective) :
    IsIso ((derivedSectionsOverOpenUnit Y V).app
      (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ)).obj I))) := by
  have hfac := fun K => (derivedSectionsOverOpen Y V).rightDerived_fac_app
    (derivedSectionsOverOpenUnit Y V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) _
    (openClassifierDerivedUnit Y V) K
  have hdesc : IsIso ((derivedSectionsOverOpen Y V).rightDerivedDesc
      (derivedSectionsOverOpenUnit Y V)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) _
      (openClassifierDerivedUnit Y V)) :=
    (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _ _ _ _
      (openClassifierDerivedUnit Y V)).1 (isRightDerivedFunctor_openClassifier Y V)
  have hunit := isIso_openClassifierDerivedUnit_app Y V _
    (Stacks.Cohomology.DerivedPushforwardComposition.pushforwardComputesDerived
      f (toOpenClassifier Y V) (derivedPushforward (toOpenClassifier Y V))
      (derivedPushforwardUnit (toOpenClassifier Y V)) I hI)
  exact (isIso_comp_right_iff _ _).mp (hfac _ ▸ hunit)

/-! ### The Leray comparison -/

/-- **Sections of a direct image are sections on the inverse image.**  The identification
`Γ(V, f_* ℱ) = Γ(f⁻¹ V, ℱ)` of `Γ(V, 𝒪_Y)`-modules, which holds on the nose: it is the identity
natural transformation. -/
def pushforwardPreimageSectionsIso :
    modulePushforward f ⋙ sectionsOverOpen Y V ≅ preimageSections f V :=
  Iso.refl _

/-- The canonical transformation from termwise sections over `f⁻¹ V` to the composite of the two
chosen derived functors: the identification `Γ(V, f_* -) = Γ(f⁻¹ V, -)`, followed by the unit of
`RΓ(V, -)` and then the unit of `Rf_*`. -/
def lerayUnit :
    homotopyPreimageSections f V ⟶
      DerivedCategory.Qh ⋙ (derivedPushforward f ⋙ derivedSectionsOverOpen Y V) :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (pushforwardPreimageSectionsIso f V)
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
      (derivedSectionsOverOpenUnit Y V) ≫
    Functor.whiskerRight (derivedPushforwardUnit f) (derivedSectionsOverOpen Y V)

/-- **The Leray comparison** `RΓ(f⁻¹ V, -) ⟶ RΓ(V, -) ∘ Rf_*`, the transformation induced by
`lerayUnit` through the universal property of the right derived functor of sections over `f⁻¹ V`.
By `lerayComparison_fac` its composite with `derivedPreimageSectionsUnit` is `lerayUnit`, and by
`lerayComparison_ext` that equation determines it. -/
def lerayComparison :
    derivedPreimageSections f V ⟶ derivedPushforward f ⋙ derivedSectionsOverOpen Y V :=
  (derivedPreimageSections f V).rightDerivedDesc (derivedPreimageSectionsUnit f V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) _
    (lerayUnit f V)

/-- The equation characterizing the Leray comparison: composing it with the unit of
`RΓ(f⁻¹ V, -)` recovers `lerayUnit`. -/
theorem lerayComparison_fac :
    derivedPreimageSectionsUnit f V ≫
        Functor.whiskerLeft DerivedCategory.Qh (lerayComparison f V) =
      lerayUnit f V :=
  (derivedPreimageSections f V).rightDerived_fac (derivedPreimageSectionsUnit f V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) _
    (lerayUnit f V)

/-- The equation of `lerayComparison_fac` determines the Leray comparison: two transformations out
of `RΓ(f⁻¹ V, -)` that agree after composition with the unit are equal. -/
theorem lerayComparison_ext
    {G : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V)))}
    (τ₁ τ₂ : derivedPreimageSections f V ⟶ G)
    (h : derivedPreimageSectionsUnit f V ≫ Functor.whiskerLeft DerivedCategory.Qh τ₁ =
      derivedPreimageSectionsUnit f V ≫ Functor.whiskerLeft DerivedCategory.Qh τ₂) :
    τ₁ = τ₂ :=
  (derivedPreimageSections f V).rightDerived_ext (derivedPreimageSectionsUnit f V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    _ _ _ h

/-- **Stacks 0D5W, over an open.**  For a morphism `f : X ⟶ Y` of ringed spaces and an open
`V ⊆ Y`, derived sections over `V` after derived pushforward along `f` agree with derived sections
over `f⁻¹ V`, as functors `D(𝒪_X) ⥤ D(Γ(V, 𝒪_Y))`: the canonical Leray comparison is an
isomorphism, with no hypothesis on `f`. -/
@[stacks 0D5W "over an open"]
theorem isIso_lerayComparison : IsIso (lerayComparison f V) := by
  have hderived : (derivedPushforward f ⋙ derivedSectionsOverOpen Y V).IsRightDerivedFunctor
      (lerayUnit f V)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) := by
    refine isRightDerivedFunctor_of_isIso_app_isKInjective.{u, u + 1, u + 1, u + 1, u + 1, u + 1}
      _ (exists_quasiIso_isKInjective X) DerivedCategory.Qh _ _ fun I hI => ?_
    have h₂ := isIso_derivedSectionsOverOpenUnit_app_pushforward f V I hI
    have h₃ := isIso_derivedPushforwardUnit_app_of_isKInjective f I hI
    change IsIso (DerivedCategory.Qh.map _ ≫ (derivedSectionsOverOpenUnit Y V).app _ ≫
      (derivedSectionsOverOpen Y V).map ((derivedPushforwardUnit f).app _))
    infer_instance
  exact (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _
    (derivedPreimageSectionsUnit f V) _ _ (lerayUnit f V)).1 hderived

/-- The canonical natural isomorphism `RΓ(V, -) ∘ Rf_* ≅ RΓ(f⁻¹ V, -)` of Tag 0D5W. -/
def derivedSectionsPushforwardIso :
    derivedPushforward f ⋙ derivedSectionsOverOpen Y V ≅ derivedPreimageSections f V :=
  have := isIso_lerayComparison f V
  (asIso (lerayComparison f V)).symm

/-- **Stacks 0D5W, global sections.**  `R Γ(Y, -) ∘ Rf_*` and `R Γ(X, -)` agree as functors
`D(𝒪_X) ⥤ D(Γ(Y, 𝒪_Y))`: the Leray comparison at `V = ⊤` is an isomorphism.  Its source is
derived sections over `f⁻¹ ⊤ = ⊤`, that is global derived sections on `X`, regarded as complexes
of `Γ(Y, 𝒪_Y)`-modules by restriction of scalars along `f^♯`. -/
@[stacks 0D5W "global sections"]
theorem isIso_lerayComparison_top : IsIso (lerayComparison f ⊤) :=
  isIso_lerayComparison f ⊤

/-- **Stacks 0D5W**, the whole lemma, stated for an arbitrary morphism of ringed spaces
`f : X ⟶ Y` with no further hypothesis.  The canonical Leray comparison
`RΓ(X, -) ⟶ RΓ(Y, -) ∘ Rf_*` of functors `D(𝒪_X) ⥤ D(Γ(Y, 𝒪_Y))` is an isomorphism, and more
generally for every open `V ⊆ Y` with `U = f⁻¹ V` the comparison
`RΓ(U, -) ⟶ RΓ(V, -) ∘ Rf_*` of functors `D(𝒪_X) ⥤ D(Γ(V, 𝒪_Y))` is an isomorphism. -/
@[stacks 0D5W "both statements, for a morphism of ringed spaces: `RΓ(Y, -) ∘ Rf_* = RΓ(X, -)`, \
and `RΓ(U, -) = RΓ(V, -) ∘ Rf_*` for `V ⊆ Y` open and `U = f⁻¹ V`"]
theorem isIso_lerayComparison_top_and_forall_open {X₀ Y₀ : RingedSpace.{u, u}} (g : X₀ ⟶ Y₀) :
    IsIso (lerayComparison g ⊤) ∧ ∀ W : Opens Y₀.carrier, IsIso (lerayComparison g W) :=
  ⟨isIso_lerayComparison_top g, isIso_lerayComparison g⟩

end Stacks.Cohomology.DerivedSectionsLeray

end
