module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedClassicalExcisionSquare
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.LocalCohomologySheafExcision
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.LocalCohomologySpellingBridge
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SupportedPullbackOpenImmersion

/-!
# The derived excision of Tag 0G78 is the classical excision of `ℋ ⁿ_Z`

Let `f : X' ⟶ X` be an open immersion of ringed spaces, `Z ⊆ X` closed and `Z' = f^{-1}(Z)`.
The project has two excision isomorphisms for the local cohomology of sheaves of
`𝒪_X`-modules along `Z`, both built from the single degreewise comparison
`Stacks.SheafOfModules.SupportedSections.supportedSectionsOnClosedPullbackNatIso`:

* the **derived** one,
  `Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsOnClosedPullbackNatIso`, an
  isomorphism `R𝓗_Z ⋙ L(f|_{Z'})^* ≅ Lf^* ⋙ R𝓗_{Z'}` of functors on the unbounded derived
  category; and
* the **classical** one,
  `Stacks.Cohomology.SupportedComplexes.localCohomologySheafPullbackNatIso`, an isomorphism
  `ℋ ⁿ_Z(-)|_{Z'} ≅ ℋ ⁿ_{Z'}(f^*-)` of Mathlib's right derived functors.

This file proves that **they agree**: the derived excision, read on the degree-`n` cohomology
sheaf of the value at a module placed in degree `0` and transported by the bridge
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplexFunctorIso` between the two
spellings of `ℋ ⁿ_Z`, is the classical excision. That is
`Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsOnClosedPullbackNatIso_eq_classical`,
the only result of the file; it is the comparison recorded as not claimed in the implementation
notes of `Stacks.Cohomology.SupportedComplexes.LocalCohomologySheafExcision`.

## Main definitions

* `Stacks.Cohomology.SupportedComplexes.derivedExcisionSourceComparison`: the left-hand vertical
  of the square — the derived pullback along `f|_{Z'}` identified with the degreewise one, an
  exact functor pulled out of the cohomology of the derived category, and the bridge at `X`.
* `Stacks.Cohomology.SupportedComplexes.derivedExcisionTargetComparison`: the right-hand
  vertical — the derived pullback along `f` identified with the degreewise one, the single
  functor of an exact functor, and the bridge at `X'`.

## Main results

* `derivedSupportedSectionsOnClosedPullbackNatIso_eq_classical`, in the namespace
  `Stacks.Cohomology.SupportedComplexes`: **the square commutes.**

## Implementation notes

**All the work is `Stacks.DerivedIndexing.derivedExcisionSquare`**, the same statement for an
abstract `δ : w ⋙ G ≅ F ⋙ w'`, whose proof is the three coherences of the bridge
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` together with the
identification of the two spellings of `rightDerivedCompIso`. What is left here is the
instantiation and the two copies of
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso` that the derived
excision carries at its two ends: the one at `f|_{Z'}` is the first factor of the left vertical,
and the one at `f` cancels against the first factor of the right vertical, which is why the
square is stated with those factors present rather than against the inner comparison.

**The presuppositions of the two composite derived functors** are discharged here, not assumed:

* `Rw ⋙ G.mapDerivedCategory` is a right derived functor of `w ⋙ G` by
  `Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose`, which needs only K-injective
  resolutions in `Mod(𝒪_X)` — `Stacks.Cohomology.Localization.enoughKInjectives`;
* `F.mapDerivedCategory ⋙ Rw'` is a right derived functor of `F ⋙ w'` by
  `Stacks.DerivedFunctor.isRightDerivedFunctor_precompose`, which additionally needs `f^*` to
  carry K-injective complexes to K-injective ones —
  `Stacks.Cohomology.openImmersionModulePullback_preservesKInjective`.

The units the derived excision actually carries are `α` whiskered by `G.mapDerivedCategory` and
the two-factor whiskering on the other side, not the canonical
`Stacks.DerivedFunctor.postcomposeUnit` and `Stacks.DerivedFunctor.precomposeUnit` the bridge is
stated at; `Stacks.DerivedFunctor.postcomposeUnit_whiskerRight` and
`Stacks.DerivedFunctor.precomposeUnit_whisker` identify them, and
`Stacks.DerivedFunctor.rightDerivedNatTrans_unit_iso` inside the abstract square does the
transport.

**Which `mapDerivedCategoryHomologyIso` the left vertical contains.** The library has two
independent `CategoryTheory.Localization.liftNatIso`s of the same datum, and they are *not*
identified: `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` of
`StacksFrontier/Algebra/Homology/DerivedCategory/MapDerivedCategoryHomology.lean` and
`StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso` of
`StacksFrontier/Homology/DerivedCategory/MapHomologyIso.lean`.
`derivedExcisionSourceComparison` contains **the first**, because that is the one
`Stacks.DerivedIndexing.singleCompDerivedCompHomologyIsoRightDerived_postComp_app` is stated with
(through `CategoryTheory.Functor.mapDerivedCategoryHomologyIso_hom_app_Qh`).
`Stacks.Gysin.supportCohomologyPullbackIso` contains the second, at a different functor and a
different object; nothing here identifies them, and nothing here needs to.  They ARE identified
elsewhere, by `Stacks.Gysin.mapDerivedCategoryHomologyIso_eq`
(`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinTargetExcisionComp.lean`) together with
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso_eq_mapDerivedCategoryHomologyFunctorIso`
(`StacksFrontier/Algebra/Homology/DerivedCategory/MapDerivedCategoryHomologyCompare.lean`), so a
consumer that needs the crossing has it and should not write a third copy.

**No `@[stacks ...]` attribute is attached.** This is a component of the square of
[Stacks, Tag 0G87] and not the statement of a tag; excision in this shape is not a tag either,
exactly as recorded for `localCohomologySheafPullbackNatIso`.

## References

* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 0G87](https://stacks.math.columbia.edu/tag/0G87)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedOpenImmersion (derivedPullbackOpenImmersionIso)
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.openImmersionModulePullback_preservesHomology
attribute [local instance] preservesFiniteLimits_modulePullback_of_isOpenImmersion
attribute [local instance] RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback
attribute [local instance]
  Stacks.Cohomology.RelativeMayerVietoris.modulePullback_preservesInjectiveObjects
attribute [local instance] isRightDerivedFunctor_derivedSupportedSectionsOnClosed_comp
attribute [local instance]
  isRightDerivedFunctor_modulePullback_comp_derivedSupportedSectionsOnClosed

variable {X' X : RingedSpace.{u, u}} (f : X' ⟶ X) [SheafedSpace.IsOpenImmersion f]
  (Z : Set X.carrier)

/-! ### The two verticals of the square -/

/-- **The left-hand vertical of the comparison**: from the degree-`n` cohomology sheaf of
`L(f|_{Z'})^* R𝓗_Z(ℱ[0])` to the pullback along `f|_{Z'}` of `ℋ ⁿ_Z(ℱ)`.

Three steps: the derived pullback along the open immersion `f|_{Z'}` is the degreewise one
(`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso`), an exact functor
commutes with the cohomology of the derived category
(`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`), and the bridge
`localCohomologySheafOfComplexFunctorIso` between the two spellings of `ℋ ⁿ_Z`, pushed forward
along `f|_{Z'}`. -/
def derivedExcisionSourceComparison (hZ : IsClosed Z) (n : ℕ)
    (M : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (DerivedCategory.homologyFunctor
          (_root_.SheafOfModules.{u} (structureSheafRing
            (closedSubsetRingedSpace X' (closedSubsetPreimage f Z)))) (n : ℤ)).obj
        ((derivedSupportedSectionsOnClosed X Z hZ ⋙
          derivedPullback (closedSubsetRestriction f Z)).obj
            ((DerivedCategory.singleFunctor
              (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj M)) ⟶
      (modulePullback (closedSubsetRestriction f Z)).obj
        ((localCohomologySheafFunctor X Z hZ n).obj M) :=
  (DerivedCategory.homologyFunctor _ (n : ℤ)).map
      ((derivedPullbackOpenImmersionIso (closedSubsetRestriction f Z)).hom.app
        ((derivedSupportedSectionsOnClosed X Z hZ).obj
          ((DerivedCategory.singleFunctor
            (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj M))) ≫
    ((modulePullback (closedSubsetRestriction f Z)).mapDerivedCategoryHomologyIso
          (n : ℤ)).hom.app
        ((derivedSupportedSectionsOnClosed X Z hZ).obj
          ((DerivedCategory.singleFunctor
            (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj M)) ≫
      (modulePullback (closedSubsetRestriction f Z)).map
        ((localCohomologySheafOfComplexFunctorIso X Z hZ n).hom.app M)

/-- **The right-hand vertical of the comparison**: from the degree-`n` cohomology sheaf of
`R𝓗_{Z'}(Lf^*(ℱ[0]))` to `ℋ ⁿ_{Z'}(f^*ℱ)`.

Three steps: the derived pullback along `f` is the degreewise one, an exact functor commutes
with the embedding of a module as a complex in degree `0`
(`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`), and the bridge
`localCohomologySheafOfComplexFunctorIso` at `X'` read at `f^*ℱ`. -/
def derivedExcisionTargetComparison (hZ' : IsClosed (closedSubsetPreimage f Z)) (n : ℕ)
    (M : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (DerivedCategory.homologyFunctor
          (_root_.SheafOfModules.{u} (structureSheafRing
            (closedSubsetRingedSpace X' (closedSubsetPreimage f Z)))) (n : ℤ)).obj
        ((derivedPullback f ⋙
          derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ').obj
            ((DerivedCategory.singleFunctor
              (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj M)) ⟶
      (localCohomologySheafFunctor X' (closedSubsetPreimage f Z) hZ' n).obj
        ((modulePullback f).obj M) :=
  (DerivedCategory.homologyFunctor _ (n : ℤ)).map
      ((derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ').map
        ((derivedPullbackOpenImmersionIso f).hom.app
          ((DerivedCategory.singleFunctor
            (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj M))) ≫
    (DerivedCategory.homologyFunctor _ (n : ℤ)).map
        ((derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ').map
          (((modulePullback f).mapDerivedCategorySingleFunctor 0).hom.app M)) ≫
      (localCohomologySheafOfComplexFunctorIso X' (closedSubsetPreimage f Z) hZ' n).hom.app
        ((modulePullback f).obj M)

/-! ### The square -/

/-- The outer cancellation: a three-factor comparison pushed through a functor, whose last
factor is inverted by the first factor of the right-hand vertical. Stated at arbitrary
categories with the objects implicit and the morphisms explicit. -/
private theorem outer {D E : Type*} [Category* D] [Category* E] (Hn : D ⥤ E)
    {x x' y' y : D} (p₁ : x ⟶ x') (mid : x' ⟶ y') (p₂ : y' ⟶ y) (q₂ : y ⟶ y') (dd : x ⟶ y)
    {u v : E} (lv₀ : Hn.obj x' ⟶ u) (rv₀ : Hn.obj y' ⟶ v) (cl : u ⟶ v)
    (hdd : dd = p₁ ≫ mid ≫ p₂)
    (hpq : Hn.map p₂ ≫ Hn.map q₂ = CategoryStruct.id (Hn.obj y'))
    (hcore : Hn.map mid ≫ rv₀ = lv₀ ≫ cl) :
    Hn.map dd ≫ Hn.map q₂ ≫ rv₀ = (Hn.map p₁ ≫ lv₀) ≫ cl := by
  calc Hn.map dd ≫ Hn.map q₂ ≫ rv₀
      = Hn.map p₁ ≫ Hn.map mid ≫ Hn.map p₂ ≫ Hn.map q₂ ≫ rv₀ := by
        rw [hdd, Hn.map_comp, Hn.map_comp]
        simp only [Category.assoc]
    _ = Hn.map p₁ ≫ Hn.map mid ≫ rv₀ := by
        rw [← Category.assoc (Hn.map p₂), hpq, Category.id_comp]
    _ = Hn.map p₁ ≫ lv₀ ≫ cl := by rw [hcore]
    _ = (Hn.map p₁ ≫ lv₀) ≫ cl := by rw [Category.assoc]

/-- **The derived excision of [Stacks, Tag 0G78] along an open immersion *is* the classical
excision of the local cohomology sheaves.** For an open immersion of ringed spaces
`f : X' ⟶ X`, a closed `Z ⊆ X`, `Z' = f^{-1}(Z)`, a degree `n` and an `𝒪_X`-module `ℱ`, the
square

```
Hⁿ(L(f|_{Z'})^* R𝓗_Z(ℱ[0])) ----> Hⁿ(R𝓗_{Z'}(Lf^*(ℱ[0])))
          |                                 |
          v                                 v
    ℋ ⁿ_Z(ℱ)|_{Z'}       ---------->  ℋ ⁿ_{Z'}(f^*ℱ)
```

commutes, the top edge being
`Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsOnClosedPullbackNatIso` read on
degree-`n` cohomology sheaves, the bottom edge
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafPullbackNatIso`, and the two verticals
`derivedExcisionSourceComparison` and `derivedExcisionTargetComparison`, each of which contains
one copy of the bridge
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplexFunctorIso` between the two
spellings of `ℋ ⁿ_Z`.

This is the comparison the implementation notes of
`Stacks.Cohomology.SupportedComplexes.LocalCohomologySheafExcision` record as not claimed; the
three coherences it needs are now all proved, and the abstract form of this statement is
`Stacks.DerivedIndexing.derivedExcisionSquare`. -/
theorem derivedSupportedSectionsOnClosedPullbackNatIso_eq_classical (hZ : IsClosed Z)
    (hZ' : IsClosed (closedSubsetPreimage f Z)) (n : ℕ)
    (M : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (DerivedCategory.homologyFunctor _ (n : ℤ)).map
          ((derivedSupportedSectionsOnClosedPullbackNatIso f Z hZ hZ').hom.app
            ((DerivedCategory.singleFunctor
              (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj M)) ≫
        derivedExcisionTargetComparison f Z hZ' n M =
      derivedExcisionSourceComparison f Z hZ n M ≫
        (localCohomologySheafPullbackNatIso f Z hZ hZ' n).hom.app M := by
  let := Stacks.DerivedFunctor.isRightDerivedFunctor_postcompose
    (supportedSectionsOnClosedFunctor X Z hZ) (modulePullback (closedSubsetRestriction f Z))
    (derivedSupportedSectionsOnClosed X Z hZ) (derivedSupportedSectionsOnClosedUnit X Z hZ)
    Stacks.Cohomology.Localization.enoughKInjectives
  let := Stacks.DerivedFunctor.isRightDerivedFunctor_precompose
    (modulePullback f) (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ')
    (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ')
    (derivedSupportedSectionsOnClosedUnit X' (closedSubsetPreimage f Z) hZ')
    Stacks.Cohomology.Localization.enoughKInjectives
    Stacks.Cohomology.Localization.enoughKInjectives
    (fun I hI => have := hI
      Stacks.Cohomology.openImmersionModulePullback_preservesKInjective f I)
  have hcore := Stacks.DerivedIndexing.derivedExcisionSquare
    (w := supportedSectionsOnClosedFunctor X Z hZ)
    (G := modulePullback (closedSubsetRestriction f Z))
    (F := modulePullback f)
    (w' := supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ')
    (δ := supportedSectionsOnClosedPullbackNatIso f Z hZ hZ')
    (Rw := derivedSupportedSectionsOnClosed X Z hZ)
    (α := derivedSupportedSectionsOnClosedUnit X Z hZ)
    (Rw' := derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ')
    (α' := derivedSupportedSectionsOnClosedUnit X' (closedSubsetPreimage f Z) hZ')
    (β₁ := derivedSupportedSectionsOnClosedCompUnit f Z hZ)
    (β₂ := Functor.whiskerLeft
        ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ))
        (derivedSupportedSectionsOnClosedUnit X' (closedSubsetPreimage f Z) hZ') ≫
      Functor.whiskerRight (modulePullback f).mapDerivedCategoryFactorsh.inv
        (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ'))
    (hβ₁ := Stacks.DerivedFunctor.postcomposeUnit_whiskerRight
      (supportedSectionsOnClosedFunctor X Z hZ)
      (modulePullback (closedSubsetRestriction f Z))
      (derivedSupportedSectionsOnClosed X Z hZ) (derivedSupportedSectionsOnClosedUnit X Z hZ))
    (hβ₂ := Stacks.DerivedFunctor.precomposeUnit_whisker (modulePullback f)
      (supportedSectionsOnClosedFunctor X' (closedSubsetPreimage f Z) hZ')
      (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ')
      (derivedSupportedSectionsOnClosedUnit X' (closedSubsetPreimage f Z) hZ'))
    (hres := Stacks.Cohomology.Localization.enoughKInjectives)
    (hres' := Stacks.Cohomology.Localization.enoughKInjectives)
    (n := n) (M := M)
  exact outer (DerivedCategory.homologyFunctor _ (n : ℤ)) _ _ _ _ _ _ _ _ rfl
    (Stacks.DerivedIndexing.map_comp_id (DerivedCategory.homologyFunctor _ (n : ℤ)) _ _
      (Stacks.DerivedIndexing.map_comp_id
        (derivedSupportedSectionsOnClosed X' (closedSubsetPreimage f Z) hZ') _ _
        (Iso.inv_hom_id_app (derivedPullbackOpenImmersionIso f)
          ((DerivedCategory.singleFunctor
            (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj M))))
    hcore

end Stacks.Cohomology.SupportedComplexes

end
