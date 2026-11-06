module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiDerivedUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiProperBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ProperDerivedImage

/-!
# The derived base-change map of the Zariski comparison morphisms

Let `f : X ⟶ Y` be a morphism of the locally quasi-compact Zariski site. This file constructs the
canonical map `π_Y^{-1} ∘ Rf_* ⟶ Rf_{Zar,*} ∘ π_X^{-1}` between functors from `D⁺(X)` to
`D⁺(LC_Zar/Y)`, extending the underived base-change map `abelianZariskiComparisonBaseChangeMap`
through the universal property of bounded below right derivation. Clause (7b) of Stacks 0DCU
asserts that it is an isomorphism when `f` is proper.

The map is characterized by a factorization equation. The relevant right derived functor is the
composite `Rf_* ⋙ Rπ_Y^{-1}`, which is a right derived functor of `f_* ⋙ π_Y^{-1}` because
right derivation on bounded below derived categories is compatible with postcomposition
(`CategoryTheory.Functor.isRightDerivedFunctor_postcomp`); and `Rπ_Y^{-1}` is identified with
`π_Y^{-1}` itself because the latter is exact
(`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology`).

## Main definitions

In the namespace `Stacks.Topology.LocallyQuasiCompactZariskiSituation`:

* `derivedComparisonBaseChangeOnHomotopy`: the underived base-change map applied degreewise on
  bounded below homotopy categories, composed with the units of right derivation.
* `derivedComparisonBaseChangeMap`: the canonical derived base-change map
  `π_Y^{-1} Rf_* ⟶ Rf_{Zar,*} π_X^{-1}` on bounded below derived categories.

## Main results

In the same namespace:

* `derivedComparisonBaseChangeMap_fac`: the equation defining the derived base-change map.
* `eq_derivedComparisonBaseChangeMap_of_fac`: the uniqueness that equation provides.

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace CategoryTheory

/-- Restriction of abelian sheaves along a continuous functor of sites is additive: addition of
morphisms of sheaves is computed componentwise. -/
instance sheafPushforwardContinuous_additive {C : Type*} [Category* C] {D : Type*} [Category* D]
    (u : C ⥤ D) {A : Type*} [Category* A] [Preadditive A] (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [u.IsContinuous J K] :
    (u.sheafPushforwardContinuous A J K).Additive where
  map_add := rfl

end CategoryTheory

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})]

/-- The underived base-change map applied degreewise on bounded below homotopy categories and
composed with the units of right derivation, the unit for the exact functor `π_Y^{-1}`
inverted. -/
def derivedComparisonBaseChangeOnHomotopy :
    (spaceDirectImage S f AddCommGrpCat.{max (u + 1) v}).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⋙
        (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).rightDerivedFunctorPlus ⟶
      DerivedCategory.Plus.Qh ⋙
        (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).rightDerivedFunctorPlus ⋙
        (sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlus :=
  let F := spaceDirectImage S f AddCommGrpCat.{max (u + 1) v}
  let G := sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}
  let PX := S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X
  let PY := S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y
  Functor.whiskerLeft F.mapHomotopyCategoryPlus (inv PY.rightDerivedFunctorPlusUnith) ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ PY))).hom
      DerivedCategory.Plus.Qh ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryPlusNatTrans (abelianZariskiComparisonBaseChangeMap S f))
      DerivedCategory.Plus.Qh ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (PX ⋙ G))).inv
      DerivedCategory.Plus.Qh ≫
    Functor.whiskerLeft PX.mapHomotopyCategoryPlus G.rightDerivedFunctorPlusUnith ≫
    Functor.whiskerRight PX.rightDerivedFunctorPlusUnith G.rightDerivedFunctorPlus

/-- **The canonical derived base-change map of the Zariski comparison morphisms,**
`π_Y^{-1} Rf_* ⟶ Rf_{Zar,*} π_X^{-1}` on bounded below derived categories. -/
def derivedComparisonBaseChangeMap :
    (spaceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlus ⋙
        (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).rightDerivedFunctorPlus ⟶
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).rightDerivedFunctorPlus ⋙
        (sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlus :=
  Functor.rightDerivedDesc
    ((spaceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlus ⋙
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).rightDerivedFunctorPlus)
    (L := DerivedCategory.Plus.Qh)
    (Functor.whiskerRight
      (spaceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlusUnith
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).rightDerivedFunctorPlus)
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}))
    _ (derivedComparisonBaseChangeOnHomotopy.{u, w, v} S f)

/-- The equation defining the canonical derived base-change map. -/
theorem derivedComparisonBaseChangeMap_fac :
    Functor.whiskerRight
        (spaceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlusUnith
        (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).rightDerivedFunctorPlus ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh
        (derivedComparisonBaseChangeMap.{u, w, v} S f) =
          derivedComparisonBaseChangeOnHomotopy.{u, w, v} S f :=
  Functor.rightDerived_fac
    ((spaceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlus ⋙
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).rightDerivedFunctorPlus)
    (L := DerivedCategory.Plus.Qh)
    (Functor.whiskerRight
      (spaceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlusUnith
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).rightDerivedFunctorPlus)
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}))
    _ (derivedComparisonBaseChangeOnHomotopy.{u, w, v} S f)

/-- A transformation satisfying the defining equation is the canonical derived base-change
map. -/
theorem eq_derivedComparisonBaseChangeMap_of_fac
    (τ : (spaceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlus ⋙
        (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).rightDerivedFunctorPlus ⟶
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).rightDerivedFunctorPlus ⋙
        (sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlus)
    (hτ : Functor.whiskerRight
        (spaceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlusUnith
        (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).rightDerivedFunctorPlus ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh τ =
        derivedComparisonBaseChangeOnHomotopy.{u, w, v} S f) :
    τ = derivedComparisonBaseChangeMap.{u, w, v} S f :=
  Functor.rightDerived_ext _ _ (HomotopyCategory.Plus.quasiIso
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})) _ _ _
    (hτ.trans (derivedComparisonBaseChangeMap_fac.{u, w, v} S f).symm)

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
