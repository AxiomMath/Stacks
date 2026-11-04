module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AbelianSupportedEndoModelBridge

/-!
# The factors of the two readings of Stacks 0G74 part (2), and what separates them

`Stacks.Perfect.AbelianSupportedEndoModelBridge` reduces the naturality of the class map of
[Stacks, Tag 0G7Q] in a merely additive morphism — step (ii) of [Stacks, Tag 0G85] — to one
`ψ`-free identity of isomorphisms, the hypothesis `forgetIsoApp` of
`Stacks.Perfect.AbelianSupportedEndoModelBridge.forgetIsoSquare_of_forgetIsoApp`:

`(abelianSheaf X).map (supportCohomologyToPushforward f ℱ).hom ≫ pushIsoApp.hom`
`  = endoForgetIsoApp.hom`.

Its left-hand side runs through
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafFunctorForgetIso`, an eleven-factor
`Iso.trans` chain of whiskerings and associators, about which the library proved nothing.  This
file opens that chain up and uses the result to cut the identity down to a single statement about
the **derived-category** comparisons of [Stacks, Tag 0G74] part (2) — one that mentions no
cohomology sheaf, no `ℕ`-indexed derived functor and no model bridge.

## Main results

* `localCohomologySheafFunctorForgetIso_eq`: **the module-side model bridge cancels.**  The
  eleven-factor chain is the bridge
  `Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplexFunctorIso` inverted,
  followed by `localCohomologySheafOfComplexForgetIso`; equivalently, the chain's leading
  factor is exactly undone by the bridge that
  `Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplexForgetIsoOfRightDerived`
  prefixes to it.
* `localCohomologySheafFunctorForgetIso_hom_app`: **the chain at an object, factor by factor.**
  Eight of the eleven factors are associators or whiskerings which contribute an identity; what
  survives is a composite of four named morphisms, of which only one — the degree-`c` cohomology of
  `Stacks.Cohomology.SupportedComplexes.localCohomologySheafForgetComparison` — carries content.
* `pushIsoApp_hom` and `endoForgetIsoApp_hom`: the two sides of `forgetIsoApp` at a module, each
  written as an explicit composite with its **last** factor — the abelian model bridge
  `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` at the underlying abelian
  sheaf, pushed forward — split off.  The two last factors are the same morphism.
* `forgetIsoApp_of_derivedForgetIdentity`: **`forgetIsoApp` follows from `DerivedForgetIdentity`**,
  the identity obtained by deleting that common last factor.
* `singleForgetIso_eq`: **the two spellings of `Φ(ℱ[0]) ≅ (Φℱ)[0]` agree** — the bridge's
  `Stacks.Perfect.AbelianSupportedEndoModelBridge.singleForgetIso` is Mathlib's
  `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`.

## The one input this file does not supply

**That input is now supplied**, by
`Stacks.Perfect.SupportedEndoForgetDegreewise.derivedForgetIdentity`, and with it
`Stacks.Perfect.SupportedEndoForgetDegreewise.forgetIsoApp`.  The rest of this section records what
it took.

`DerivedForgetIdentity` says that the degree-`c` cohomology of the comparison of
[Stacks, Tag 0G74] part (2) **on `Z`**
(`Stacks.Cohomology.SupportedComplexes.localCohomologySheafForgetComparison`), pushed forward along
the closed immersion, agrees with the degree-`c` cohomology of the comparison **with `i_*` folded
in** (`Stacks.Perfect.AbelianCechDerivedSquare.forgetComparison`, which is
`Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedEndoForgetComparison` at the canonical
derived functors), read across the four "an exact functor commutes with `Hⁿ`" comparisons that
separate the two spellings.  It mentions no Čech complex, no cokernel and no class map.

Both comparisons are `CategoryTheory.Functor.rightDerivedDesc` of their respective transported
underived comparisons, so the route is a `CategoryTheory.Functor.rightDerived_ext` argument of the
same shape as
`Stacks.Cohomology.AbelianSupportedCounitForget.whiskerRight_derivedSupportedSectionsToId`,
establishing the identity of the two **transformations** before any cohomology sheaf is taken, and
then feeding it through the four homology comparisons.  **The first step is now done**, by
`Stacks.Perfect.SupportedEndoForgetIdentity.forgetComparison_eq`: the comparison with `i_*` folded
in *is* the comparison on `Z`, read through the derived pushforward/forget comparison.  The second
step — taking the degree-`c` cohomology of that identity and matching it against the four homology
comparisons and the two readings of `Φ(ℱ[0]) ≅ (Φℱ)[0]` — is carried out in
`StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/SupportedEndoForgetDegreewise.lean`,
not here.  What it needs beyond the identifications already available is the degreewise reading of
the derived
pushforward/forget comparison: how `Hᶜ` of
`Stacks.Cohomology.ModulePushforwardComparison.derivedModulePushforwardCompToSheafIso` at an
object compares with the *underived* `modulePushforwardCompToSheafIso` — which is `Iso.refl` — once
the three "an exact functor commutes with `Hⁿ`" comparisons of the two forgetful functors and of
the direct image are inserted.  That is
`Stacks.Cohomology.ModulePushforwardComparison.derivedModulePushforwardCompToSheafIso_homology`,
obtained by reading each of the comparison's three factors in degree `n` separately
(`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso_comp_app` and
`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso_isoOfNatIso_app`) rather than by one
`CategoryTheory.Localization.natTrans_ext` argument.

The transformations do not even have the same source until the direct image is moved past the
forgetful functor on *derived* categories, which is
`Stacks.Cohomology.ModulePushforwardComparison.derivedModulePushforwardCompToSheafIso`, pinned
down by `derivedModulePushforwardCompToSheafIso_fac` over `DerivedCategory.Q` and by
`derivedModulePushforwardCompToSheafIso_fach` over `DerivedCategory.Qh`.  Underived that move is
`Iso.refl` (`modulePushforwardCompToSheafIso`); on derived categories it is a composite of two
comparisons of "the descent of a composite" with "the composite of the descents", and so is not.

Three of the four homology comparisons are recorded in the library as mutually non-`rfl` copies
of one statement — see the implementation note on
`Stacks.Perfect.AbelianCechCokernelPassage.forgetDerivedHomologyIso`.  All three are now proved
equal, by
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso_eq_mapDerivedCategoryHomologyFunctorIso`
and `Stacks.Cohomology.SupportedComplexes.exactFunctorDerivedHomologyIso_eq`.
`Stacks.Perfect.AbelianSupportedEndoModelBridge.singleForgetIso` is likewise *not* `rfl`-equal to
Mathlib's `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, although the two have the same
type; `singleForgetIso_eq` below identifies them.

## Implementation notes

**Why the comparisons are named as values at an object.**  `modelForgetHomology`,
`singleForgetMathlib` and `pushHomologySingle` are values of natural isomorphisms at an object with
both ends of their types written as `Functor.obj` applied to an object, for the reason recorded in
the implementation notes of `Stacks.Perfect.AbelianSupportedEndoModelBridge`: a term whose type is
stated through a composite functor is type-correct only up to unfolding
`CategoryTheory.Functor.comp`, and here it also pins down the `HasDerivedCategory` universe, which
is otherwise left as a metavariable and resolved at the wrong level.

**Why the assembly is term-level.**  `rw` fails on every goal below with *target expression is not
type-correct under the implicit transparency level*: `AlgebraicGeometry.Scheme.Modules` and
`SheafOfModules (structureSheafRing X.toRingedSpace)` are definitionally equal but not
interchangeable in a rewrite motive.  The reassociations are therefore done by the two `private`
lemmas `map_comp_head_id` and `assoc_of_head`, stated at a variable category, which `exact`
instantiates up to default transparency.  This is the device of
`Stacks.Perfect.AbelianCechDerivedSquare.square_formal`.

**No `@[stacks ...]` attribute is attached to any declaration here**, and nothing here proves
[Stacks, Tag 0G85] or [Stacks, Tag 0G74].

## References

* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.AbelianModelComparison (abelianPushHomologySingleIso)
open Stacks.Cohomology.AbelianSupportedCounit (derivedAbelianSupportedPushforward)
open Stacks.Cohomology.ModulePushforwardComparison (modulePushforwardCompToSheafIso)
open Stacks.Cohomology.SupportedComplexes
open Stacks.Cohomology.UnderlyingAbelianSheaf (underlyingDerivedSheaf)
open Stacks.Perfect.AbelianCechCokernelPassage (forgetDerivedHomology)
open Stacks.Perfect.AbelianCechDerivedSquare (forgetComparisonIso)
open Stacks.Perfect.AbelianFraction (abelianSheaf)
open Stacks.Perfect.AbelianSupportedEndoModelBridge
open Stacks.Perfect.CechDerivedSupport (isClosed_equationsClosedSet)
open Stacks.Perfect.CechSupportTransport (supportCohomologyToPushforward)
open Stacks.Perfect.GysinAbelianSquare (abelianClosedPushforward)
open Stacks.Perfect.SupportedFraction (supportPushSingle)
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.AbelianSupportedEndoModelFactors

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Formal reassociations -/

/-- Cancelling a whiskered isomorphism against its inverse at the head of a composite of natural
isomorphisms, at abstract categories. -/
private lemma whiskerRight_symm_cancel {C₀ D₀ E₀ : Type*} [Category* C₀] [Category* D₀]
    [Category* E₀] {F G : C₀ ⥤ D₀} (A : F ≅ G) (W : D₀ ⥤ E₀) {S : C₀ ⥤ E₀} (R : F ⋙ W ≅ S) :
    Functor.isoWhiskerRight A W ≪≫ Functor.isoWhiskerRight A.symm W ≪≫ R = R := by
  rw [← Iso.trans_assoc, ← Functor.isoWhiskerRight_trans, A.self_symm_id,
    Functor.isoWhiskerRight_refl, Iso.refl_trans]

/-- Cancelling a composable pair whose composite is the identity at the head of the argument of a
functor, at an abstract category; stated at a variable category for the reason recorded in the
implementation notes. -/
private lemma map_comp_head_id {C₀ D₀ : Type*} [Category* C₀] [Category* D₀] (W : C₀ ⥤ D₀)
    {A B M : C₀} (a : A ⟶ B) (b : B ⟶ A) (hab : a ≫ b = 𝟙 A) (r : A ⟶ M) {P : D₀}
    (p : P ⟶ W.obj A) :
    p ≫ W.map (a ≫ b ≫ r) = p ≫ W.map r := by
  rw [← Category.assoc, hab, Category.id_comp]

/-- Splitting a trailing factor off a four-fold composite whose first three factors are known, at
an abstract category. -/
lemma assoc_of_head {C₀ : Type*} [Category* C₀] {A B C D E : C₀} (a : A ⟶ B) (b : B ⟶ C)
    (c : C ⟶ D) (l : D ⟶ E) (r : A ⟶ D) (h : a ≫ b ≫ c = r) :
    a ≫ b ≫ c ≫ l = r ≫ l := by
  rw [← h]; simp only [Category.assoc]

/-! ### The factors of the degreewise comparison of Stacks 0G74 part (2) -/

section RingedSpace

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z) (c : ℕ)

/-- **Forgetting the module structure on `Z` commutes with the degree-`c` cohomology of the
derived category**, at `R𝓗_Z(ℱ[0])`, with both ends of the type written as `Functor.obj` applied to
an object.  This is `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` at the spot in the
eleven-factor chain where it occurs. -/
def modelForgetHomology (H : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (_root_.SheafOfModules.toSheaf
          (structureSheafRing (closedSubsetRingedSpace X Z))).obj
        ((localCohomologySheafOfComplexFunctor X Z hZ (c : ℤ)).obj H) ≅
      (DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}) (c : ℤ)).obj
        ((underlyingDerivedSheaf (structureSheafRing (closedSubsetRingedSpace X Z))).obj
          ((derivedSupportedSectionsOnClosed X Z hZ).obj
            ((DerivedCategory.singleFunctor
              (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj H))) :=
  (((_root_.SheafOfModules.toSheaf
    (structureSheafRing (closedSubsetRingedSpace X Z))).mapDerivedCategoryHomologyIso
      (c : ℤ)).app _).symm

/-- **Forgetting the module structure commutes with placing a module in degree `0`**, in Mathlib's
spelling `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, at an object, with both ends of
the type written as `Functor.obj` applied to an object.

This has the same type as `Stacks.Perfect.AbelianSupportedEndoModelBridge.singleForgetIso`, which
is assembled differently; the two are **not** `rfl`-equal. -/
def singleForgetMathlib (H : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (underlyingDerivedSheaf (structureSheafRing X)).obj
        ((DerivedCategory.singleFunctor
          (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj H) ≅
      (DerivedCategory.singleFunctor
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) 0).obj
        ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj H) :=
  ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapDerivedCategorySingleFunctor 0).app H

/-- **The module-side model bridge cancels out of the degreewise comparison of
[Stacks, Tag 0G74] part (2).**

`Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplexForgetIso` is by definition the
bridge `localCohomologySheafOfComplexFunctorIso` between the unbounded and the `ℕ`-indexed model of
`ℋ ⁿ_Z` on modules, followed by the eleven-factor chain
`localCohomologySheafFunctorForgetIso`, whose own leading factor is that same bridge inverted.  So
the two cancel: the chain is the bridge inverted followed by the `localCohomologySheafOfComplex`
spelling of the comparison, and nothing of the `ℕ`-indexed model of `ℋ ⁿ_Z` on **modules** survives
in it. -/
theorem localCohomologySheafFunctorForgetIso_eq :
    Functor.isoWhiskerRight (localCohomologySheafOfComplexFunctorIso X Z hZ c).symm
          (_root_.SheafOfModules.toSheaf
            (structureSheafRing (closedSubsetRingedSpace X Z))) ≪≫
        localCohomologySheafOfComplexForgetIso X Z hZ c =
      localCohomologySheafFunctorForgetIso X Z hZ
        (derivedAbelianSupportedSectionsOnClosed X Z hZ)
        (derivedAbelianSupportedSectionsOnClosedUnit X Z hZ)
        (derivedSupportedSectionsOnClosed X Z hZ)
        (derivedSupportedSectionsOnClosedUnit X Z hZ) c :=
  whiskerRight_symm_cancel _ _ _

/-- **The eleven-factor chain at an object, factor by factor.**

Eight of the eleven factors are associators or whiskered associators and contribute an identity.
What is left is: the module-side model bridge inverted; `modelForgetHomology`, moving the
forgetful functor past the degree-`c` cohomology; the degree-`c` cohomology of the canonical
comparison `Stacks.Cohomology.SupportedComplexes.localCohomologySheafForgetComparison` of
[Stacks, Tag 0G74] part (2), which is the only factor carrying content; the degree-`c` cohomology
of `R𝓗_Z^{ab}` applied to `singleForgetMathlib`; and the abelian model bridge. -/
theorem localCohomologySheafFunctorForgetIso_hom_app
    (H : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (localCohomologySheafFunctorForgetIso X Z hZ
          (derivedAbelianSupportedSectionsOnClosed X Z hZ)
          (derivedAbelianSupportedSectionsOnClosedUnit X Z hZ)
          (derivedSupportedSectionsOnClosed X Z hZ)
          (derivedSupportedSectionsOnClosedUnit X Z hZ) c).hom.app H =
      (_root_.SheafOfModules.toSheaf
            (structureSheafRing (closedSubsetRingedSpace X Z))).map
          ((localCohomologySheafOfComplexFunctorIso X Z hZ c).inv.app H) ≫
        (modelForgetHomology X Z hZ c H).hom ≫
        (DerivedCategory.homologyFunctor
            (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}) (c : ℤ)).map
          ((localCohomologySheafForgetComparison X Z hZ
              (derivedAbelianSupportedSectionsOnClosed X Z hZ)
              (derivedAbelianSupportedSectionsOnClosedUnit X Z hZ)
              (derivedSupportedSectionsOnClosed X Z hZ)
              (derivedSupportedSectionsOnClosedUnit X Z hZ)).app
            ((DerivedCategory.singleFunctor
              (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj H)) ≫
        (DerivedCategory.homologyFunctor
            (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}) (c : ℤ)).map
          ((derivedAbelianSupportedSectionsOnClosed X Z hZ).map
            (singleForgetMathlib X H).hom) ≫
        (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
            (abelianSupportedSectionsOnClosed X Z hZ)
            (derivedAbelianSupportedSectionsOnClosed X Z hZ)
            (derivedAbelianSupportedSectionsOnClosedUnit X Z hZ)
            Stacks.Cohomology.Localization.enoughKInjectives c).hom.app
          ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj H) := rfl

end RingedSpace

/-! ### The two sides of `forgetIsoApp`, with their common last factor split off -/

section Scheme

variable {X : Scheme.{u}} {T : Set X} (hT : IsClosed T) (c : ℕ) (H : X.Modules)

/-- **`Stacks.Perfect.AbelianSupportedEndoModelBridge.singleForgetIso` is Mathlib's
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`.**

The two have the same type and are assembled differently — the bridge's spelling is
`CategoryTheory.Functor.mapDerivedCategoryFactors` followed by the localization of
`HomologicalComplex.singleMapHomologicalComplex`, Mathlib's is a seven-factor chain of whiskerings
and associators — and they are not `rfl`-equal.  Mathlib's
`CategoryTheory.Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app`
cancels the leading factor off Mathlib's spelling, and what it leaves is the localization of
`CategoryTheory.Functor.mapCochainComplexSingleFunctor`, which *is*
`HomologicalComplex.singleMapHomologicalComplex` by definition. -/
theorem singleForgetIso_eq : singleForgetIso H = singleForgetMathlib X.toRingedSpace H :=
  Iso.ext ((Iso.inv_comp_eq
      ((abelianSheaf X).mapDerivedCategoryFactors.app
        ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj H))).mp
    ((abelianSheaf X).mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app
      H)).symm

/-- The common last factor of the two sides of `forgetIsoApp`: the abelian model bridge at the
underlying abelian sheaf, pushed forward from `T`. -/
def abelianModelTail :
    (abelianClosedPushforward X.toRingedSpace T).obj
        ((DerivedCategory.homologyFunctor
            (Sheaf (Opens.grothendieckTopology (TopCat.of T)) AddCommGrpCat.{u}) (c : ℤ)).obj
          ((derivedAbelianSupportedSectionsOnClosed X.toRingedSpace T hT).obj
            ((DerivedCategory.singleFunctor
              (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) 0).obj
              ((abelianSheaf X).obj H)))) ⟶
      (Stacks.Perfect.GysinAbelianSquare.abelianLocalCohomologyPushforward
        X.toRingedSpace T hT c).obj ((abelianSheaf X).obj H) :=
  (abelianClosedPushforward X.toRingedSpace T).map
    ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
        (abelianSupportedSectionsOnClosed X.toRingedSpace T hT)
        (derivedAbelianSupportedSectionsOnClosed X.toRingedSpace T hT)
        (derivedAbelianSupportedSectionsOnClosedUnit X.toRingedSpace T hT)
        Stacks.Cohomology.Localization.enoughKInjectives c).hom.app ((abelianSheaf X).obj H))

/-- **[Stacks, Tag 0G74] part (2) for the exact direct image, at a module placed in degree `0`**,
for an arbitrary closed subset and degree.  This is
`Stacks.Perfect.CechSupportTransport.supportCohomologyToPushforward` with the family of equations
removed; `supportCohomologyToPushforward_eq` records that it *is* that comparison. -/
def pushHomologySingle :
    (DerivedCategory.homologyFunctor X.Modules (c : ℤ)).obj (supportPushSingle hT H) ≅
      (modulePushforward (closedSubsetInclusion X.toRingedSpace T)).obj
        ((localCohomologySheafOfComplexFunctor X.toRingedSpace T hT (c : ℤ)).obj H) :=
  letI := pushforward_preservesFiniteLimits X.toRingedSpace T
  letI := pushforward_preservesFiniteColimits X.toRingedSpace T hT
  (Functor.mapDerivedCategoryHomologyFunctorIso
      (modulePushforward (closedSubsetInclusion X.toRingedSpace T)) (c : ℤ)).app
    ((derivedSupportedSectionsOnClosed X.toRingedSpace T hT).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj H))

/-- The comparison of the two places at which the degree-`c` cohomology sheaf is taken is
`pushHomologySingle` at the closed subset cut out by the equations. -/
theorem supportCohomologyToPushforward_eq {n : ℕ} (f : Fin (n + 1) → Γ(X, ⊤)) :
    (supportCohomologyToPushforward f H).hom =
      (pushHomologySingle (isClosed_equationsClosedSet f) (n + 1) H).hom := rfl

/-- **The classical-model side of `forgetIsoApp` at a module**, with the model bridge cancelled
and the common last factor `abelianModelTail` split off. -/
theorem pushIsoApp_hom :
    (pushIsoApp hT c H).hom =
      (modulePushforwardCompToSheafIso (closedSubsetInclusion X.toRingedSpace T)).hom.app
          ((localCohomologySheafOfComplexFunctor X.toRingedSpace T hT (c : ℤ)).obj H) ≫
        (abelianClosedPushforward X.toRingedSpace T).map
          ((modelForgetHomology X.toRingedSpace T hT c H).hom ≫
            (DerivedCategory.homologyFunctor
                (Sheaf (Opens.grothendieckTopology (TopCat.of T)) AddCommGrpCat.{u}) (c : ℤ)).map
              ((localCohomologySheafForgetComparison X.toRingedSpace T hT
                  (derivedAbelianSupportedSectionsOnClosed X.toRingedSpace T hT)
                  (derivedAbelianSupportedSectionsOnClosedUnit X.toRingedSpace T hT)
                  (derivedSupportedSectionsOnClosed X.toRingedSpace T hT)
                  (derivedSupportedSectionsOnClosedUnit X.toRingedSpace T hT)).app
                ((DerivedCategory.singleFunctor X.Modules 0).obj H)) ≫
            (DerivedCategory.homologyFunctor
                (Sheaf (Opens.grothendieckTopology (TopCat.of T)) AddCommGrpCat.{u}) (c : ℤ)).map
              ((derivedAbelianSupportedSectionsOnClosed X.toRingedSpace T hT).map
                (singleForgetMathlib X.toRingedSpace H).hom)) ≫
        abelianModelTail hT c H :=
  map_comp_head_id (abelianClosedPushforward X.toRingedSpace T)
    ((_root_.SheafOfModules.toSheaf
        (structureSheafRing (closedSubsetRingedSpace X.toRingedSpace T))).map
      ((localCohomologySheafOfComplexFunctorIso X.toRingedSpace T hT c).hom.app H))
    ((_root_.SheafOfModules.toSheaf
        (structureSheafRing (closedSubsetRingedSpace X.toRingedSpace T))).map
      ((localCohomologySheafOfComplexFunctorIso X.toRingedSpace T hT c).inv.app H))
    ((_root_.SheafOfModules.toSheaf
      (structureSheafRing (closedSubsetRingedSpace X.toRingedSpace T))).mapIso
        ((localCohomologySheafOfComplexFunctorIso X.toRingedSpace T hT c).app H)).hom_inv_id
    _ _

/-- **The unbounded-model side of `forgetIsoApp` at a module**, with the same last factor
`abelianModelTail` split off. -/
theorem endoForgetIsoApp_hom :
    (endoForgetIsoApp hT c H).hom =
      ((forgetDerivedHomology (supportPushSingle hT H) (c : ℤ)).inv ≫
          (DerivedCategory.homologyFunctor
              (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (c : ℤ)).map
            (forgetComparisonIso hT ((DerivedCategory.singleFunctor X.Modules 0).obj H)).hom ≫
          (DerivedCategory.homologyFunctor
              (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (c : ℤ)).map
            ((derivedAbelianSupportedPushforward X.toRingedSpace T hT).map
              (singleForgetIso H).hom) ≫
          (abelianPushHomologySingleIso X.toRingedSpace T hT (c : ℤ)
            ((abelianSheaf X).obj H)).hom) ≫
        abelianModelTail hT c H := by
  simp only
  rfl

/-- **The identity that `forgetIsoApp` reduces to.**

The classical-model and the unbounded-model readings of [Stacks, Tag 0G74] part (2) agree once the
common abelian model bridge `abelianModelTail` is stripped off both.  What is left mentions only
the two comparisons of [Stacks, Tag 0G74] part (2) *on derived categories* —
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafForgetComparison`, stated on `T`, and
`Stacks.Perfect.AbelianCechDerivedSquare.forgetComparison`, stated with `i_*` folded in — together
with the four comparisons that move an exact functor past the degree-`c` cohomology of a derived
category and the two readings of `Φ(ℱ[0]) ≅ (Φℱ)[0]`.  No `ℕ`-indexed derived functor, no model
bridge, no Čech complex and no morphism of coefficient modules occurs. -/
def DerivedForgetIdentity : Prop :=
  ∀ H : X.Modules,
    (abelianSheaf X).map (pushHomologySingle hT c H).hom ≫
        (modulePushforwardCompToSheafIso (closedSubsetInclusion X.toRingedSpace T)).hom.app
          ((localCohomologySheafOfComplexFunctor X.toRingedSpace T hT (c : ℤ)).obj H) ≫
        (abelianClosedPushforward X.toRingedSpace T).map
          ((modelForgetHomology X.toRingedSpace T hT c H).hom ≫
            (DerivedCategory.homologyFunctor
                (Sheaf (Opens.grothendieckTopology (TopCat.of T)) AddCommGrpCat.{u}) (c : ℤ)).map
              ((localCohomologySheafForgetComparison X.toRingedSpace T hT
                  (derivedAbelianSupportedSectionsOnClosed X.toRingedSpace T hT)
                  (derivedAbelianSupportedSectionsOnClosedUnit X.toRingedSpace T hT)
                  (derivedSupportedSectionsOnClosed X.toRingedSpace T hT)
                  (derivedSupportedSectionsOnClosedUnit X.toRingedSpace T hT)).app
                ((DerivedCategory.singleFunctor X.Modules 0).obj H)) ≫
            (DerivedCategory.homologyFunctor
                (Sheaf (Opens.grothendieckTopology (TopCat.of T)) AddCommGrpCat.{u}) (c : ℤ)).map
              ((derivedAbelianSupportedSectionsOnClosed X.toRingedSpace T hT).map
                (singleForgetMathlib X.toRingedSpace H).hom)) =
      (forgetDerivedHomology (supportPushSingle hT H) (c : ℤ)).inv ≫
        (DerivedCategory.homologyFunctor
            (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (c : ℤ)).map
          (forgetComparisonIso hT ((DerivedCategory.singleFunctor X.Modules 0).obj H)).hom ≫
        (DerivedCategory.homologyFunctor
            (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (c : ℤ)).map
          ((derivedAbelianSupportedPushforward X.toRingedSpace T hT).map
            (singleForgetIso H).hom) ≫
        (abelianPushHomologySingleIso X.toRingedSpace T hT (c : ℤ) ((abelianSheaf X).obj H)).hom

/-- **The hypothesis `forgetIsoApp` of
`Stacks.Perfect.AbelianSupportedEndoModelBridge.forgetIsoSquare_of_forgetIsoApp` follows from
`DerivedForgetIdentity`.**

Both sides of `forgetIsoApp` end in the same factor `abelianModelTail`, by `pushIsoApp_hom` and
`endoForgetIsoApp_hom`; deleting it is exactly `DerivedForgetIdentity`. -/
theorem forgetIsoApp_of_derivedForgetIdentity {n : ℕ} (f : Fin (n + 1) → Γ(X, ⊤))
    (key : DerivedForgetIdentity (isClosed_equationsClosedSet f) (n + 1)) (H : X.Modules) :
    (abelianSheaf X).map (supportCohomologyToPushforward f H).hom ≫
        (pushIsoApp (isClosed_equationsClosedSet f) (n + 1) H).hom =
      (endoForgetIsoApp (isClosed_equationsClosedSet f) (n + 1) H).hom :=
  ((congrArg (fun z => (abelianSheaf X).map (supportCohomologyToPushforward f H).hom ≫ z)
        (pushIsoApp_hom (isClosed_equationsClosedSet f) (n + 1) H)).trans
      (assoc_of_head _ _ _ _ _ (key H))).trans
    (endoForgetIsoApp_hom (isClosed_equationsClosedSet f) (n + 1) H).symm

end Scheme

end Stacks.Perfect.AbelianSupportedEndoModelFactors

end
