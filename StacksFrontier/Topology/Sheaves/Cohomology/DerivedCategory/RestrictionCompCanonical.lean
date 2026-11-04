module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.RestrictionComparisonCoherence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.LocallyGivenOfGlobalObject
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.TwoOpenGlueingCompatibility

/-!
# The comparison of restriction in two steps is the canonical one, for every system

Let `X` be a ringed space and let `S` be a system of locally given derived objects on it, as in
Situation 0D67.  For a chain `W ⊆ V ⊆ U` of open subsets, the system carries a comparison

`S.restrictionComp W V U : S.restriction W U _ ≅ S.restriction V U _ ⋙ S.restriction W V _`

of restriction in one step with restriction in two.  There is also a canonical such comparison,
not depending on `S`: the one of the restriction datum
`Stacks.DerivedGlueing.restrictionDatum`, whose displayed restriction is the functor induced on
derived categories by restriction of complexes of sheaves of modules.  This file proves that the
two agree, transported along the identification
`Stacks.DerivedGlueing.restrictionIsoMapDerivedCategory` of the displayed restriction with the
induced functor.

So a system of locally given derived objects carries no choice in its comparisons: the field
`restrictionComp` is determined by the field `restriction`, together with `restrictionFactors`.

## Main results

* `Stacks.DerivedGlueing.restrictionIsoMapDerivedCategory_inv_app_Q` — the identification of the
  displayed restriction with the induced functor, read at the class of a complex, in the inverse
  direction.  Its forward reading,
  `Stacks.DerivedGlueing.restrictionIsoMapDerivedCategory_hom_app_Q` — the system's own
  factorization followed by the inverse of the canonical one — is hosted in
  `StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.TwoOpenGlueingCompatibility`, which
  this file imports.
* `Stacks.DerivedGlueing.LocallyGiven.restrictionComp_eq` — the comparison carried by an
  arbitrary system is the canonical comparison of
  `Stacks.DerivedGlueing.restrictionDatum`, conjugated by
  `Stacks.DerivedGlueing.restrictionIsoMapDerivedCategory`.
* `Stacks.DerivedGlueing.LocallyGiven.restrictionComp_eq_app` — the same, componentwise, which
  is the form a consumer rewrites with.
* `Stacks.DerivedGlueing.LocallyGiven.restrictionComp_eq_mapDerivedCategoryComp` and
  `Stacks.DerivedGlueing.LocallyGiven.restrictionComp_hom_app_eq` — the same two statements with
  the canonical comparison spelled as the lifted comparison
  `Stacks.DerivedGlueing.mapDerivedCategoryComp` of the counit of extension by zero, which is
  what the restriction datum's field is.

## Implementation notes

Both sides are natural transformations between functors out of
`Stacks.DerivedGlueing.OpenDerivedCategory X U`, a localization of complexes of sheaves of
modules by the quasi-isomorphisms, so `CategoryTheory.Localization.natTrans_ext` reduces the
equality to its instances at `DerivedCategory.Q.obj C`.  There every comparison has an explicit
value: `Stacks.DerivedGlueing.LocallyGiven.restrictionCompFactors'` pins the system's comparison
and — the restriction datum being a system — the canonical one as well, and
`Stacks.DerivedGlueing.restrictionIsoMapDerivedCategory_inv_app_Q_comp` evaluates the
identification.  The two sides are then compared by composing each with one common invertible
leg, `Stacks.DerivedGlueing.eq_of_comp_right_eq_of_isIso`, the leg being the right-hand factor of
`restrictionCompFactors'`.

The proof is written throughout in the spelling
`(openModuleRestriction X V U hVU).mapDerivedCategory` rather than
`(restrictionDatum X).restriction V U hVU`; the two are definitionally equal, but a goal mixing
them is not type-correct at the transparency `rw` re-checks at, and no rewrite fires on it.  The
crossing is paid once, at the level of isomorphisms, by
`Stacks.DerivedGlueing.restrictionDatum_restrictionComp_eq`, after which the restriction-datum
form of each statement follows by a single application.

## References

* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)

Tags covered: none.  This is a step of a proof, not a clause of a tag statement.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ExtensionByZeroModules

namespace Stacks.DerivedGlueing

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃ u

/-! ### The lifted comparison of induced functors, with the identity comparison removed -/

/-- **The defining equation of `Stacks.DerivedGlueing.mapDerivedCategoryComp`, with the identity
comparison removed.** The identification of the two readings of the composite prolongation that
`Stacks.DerivedGlueing.mapDerivedCategoryComp_factors` inserts is the identity, by
`Stacks.DerivedGlueing.mapHomologicalComplexCompIso_refl_hom_app`; what is left is that the
comparison, read at the class of a complex and transported along the comparisons of each induced
functor with the degreewise one, is `θ` applied degreewise. -/
theorem mapDerivedCategoryComp_factors' {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
    [HasDerivedCategory.{w₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂]
    [HasDerivedCategory.{w₂} C₂] {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃]
    [HasDerivedCategory.{w₃} C₃] (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (G : C₂ ⥤ C₃) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] (H : C₁ ⥤ C₃) [H.Additive] [PreservesFiniteLimits H]
    [PreservesFiniteColimits H] (θ : F ⋙ G ≅ H)
    (C : HomologicalComplex C₁ (ComplexShape.up ℤ)) :
    (mapDerivedCategoryComp F G H θ).hom.app (DerivedCategory.Q.obj C) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app C) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app C) =
      H.mapDerivedCategoryFactors.hom.app C := by
  simpa using mapDerivedCategoryComp_factors F G H θ C

/-! ### The canonical comparison and the identification of the displayed restriction -/

section Derived

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-- **`Stacks.DerivedGlueing.restrictionIsoMapDerivedCategory` in the other direction, read at
the class of a complex**: the inverse of
`Stacks.DerivedGlueing.restrictionIsoMapDerivedCategory_hom_app_Q`. -/
theorem restrictionIsoMapDerivedCategory_inv_app_Q (S : LocallyGiven X) (V U : Opens X.carrier)
    (hVU : V ≤ U)
    (C : HomologicalComplex (SheafOfModules.{u} (restrictedRingSheaf X U))
      (ComplexShape.up ℤ)) :
    (restrictionIsoMapDerivedCategory S V U hVU).inv.app (DerivedCategory.Q.obj C) =
      (openModuleRestriction X V U hVU).mapDerivedCategoryFactors.hom.app C ≫
        (S.restrictionFactors V U hVU).inv.app C := by
  simp [restrictionIsoMapDerivedCategory, Localization.Lifting.iso]

/-- The identification of the displayed restriction with the induced functor turns the canonical
factorization into the system's own. -/
theorem restrictionIsoMapDerivedCategory_hom_app_Q_comp (S : LocallyGiven X)
    (V U : Opens X.carrier) (hVU : V ≤ U)
    (C : HomologicalComplex (SheafOfModules.{u} (restrictedRingSheaf X U))
      (ComplexShape.up ℤ)) :
    (restrictionIsoMapDerivedCategory S V U hVU).hom.app (DerivedCategory.Q.obj C) ≫
        (openModuleRestriction X V U hVU).mapDerivedCategoryFactors.hom.app C =
      (S.restrictionFactors V U hVU).hom.app C := by
  rw [restrictionIsoMapDerivedCategory_hom_app_Q]
  simp

/-- The identification of the displayed restriction with the induced functor turns the system's
own factorization into the canonical one. -/
theorem restrictionIsoMapDerivedCategory_inv_app_Q_comp (S : LocallyGiven X)
    (V U : Opens X.carrier) (hVU : V ≤ U)
    (C : HomologicalComplex (SheafOfModules.{u} (restrictedRingSheaf X U))
      (ComplexShape.up ℤ)) :
    (restrictionIsoMapDerivedCategory S V U hVU).inv.app (DerivedCategory.Q.obj C) ≫
        (S.restrictionFactors V U hVU).hom.app C =
      (openModuleRestriction X V U hVU).mapDerivedCategoryFactors.hom.app C := by
  rw [restrictionIsoMapDerivedCategory_inv_app_Q]
  simp

/-- **The canonical comparison of restriction in two steps, read at the class of a complex.**
This is `Stacks.DerivedGlueing.mapDerivedCategoryComp_factors'` for the comparison
`Stacks.DerivedGlueing.openModuleRestrictionComparison`, which is the counit of extension by
zero on the middle open. -/
theorem mapDerivedCategoryComp_openModuleRestriction_factors (X : RingedSpace.{u, u})
    (W V U : Opens X.carrier) (hWV : W ≤ V) (hVU : V ≤ U)
    (C : HomologicalComplex (SheafOfModules.{u} (restrictedRingSheaf X U))
      (ComplexShape.up ℤ)) :
    (mapDerivedCategoryComp (openModuleRestriction X V U hVU) (openModuleRestriction X W V hWV)
            (openModuleRestriction X W U (hWV.trans hVU))
            (asIso (openModuleRestrictionComparison X W V U hWV hVU))).hom.app
          (DerivedCategory.Q.obj C) ≫
        (openModuleRestriction X W V hWV).mapDerivedCategory.map
          ((openModuleRestriction X V U hVU).mapDerivedCategoryFactors.hom.app C) ≫
        (openModuleRestriction X W V hWV).mapDerivedCategoryFactors.hom.app
          (((openModuleRestriction X V U hVU).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (openModuleRestrictionComparison X W V U hWV hVU)
            (ComplexShape.up ℤ)).app C) =
      (openModuleRestriction X W U (hWV.trans hVU)).mapDerivedCategoryFactors.hom.app C :=
  mapDerivedCategoryComp_factors' _ _ _ _ C

/-- **The comparison of restriction carried by the restriction datum is the lifted comparison of
induced functors.** This is the definition of
`Stacks.DerivedGlueing.restrictionDatum`, and it is the one place the two spellings of the
displayed restriction are identified. -/
theorem restrictionDatum_restrictionComp_eq (X : RingedSpace.{u, u}) (W V U : Opens X.carrier)
    (hWV : W ≤ V) (hVU : V ≤ U) :
    (restrictionDatum X).restrictionComp W V U hWV hVU =
      mapDerivedCategoryComp (openModuleRestriction X V U hVU)
        (openModuleRestriction X W V hWV) (openModuleRestriction X W U (hWV.trans hVU))
        (asIso (openModuleRestrictionComparison X W V U hWV hVU)) :=
  rfl

/-! ### The comparison carried by a system is the canonical one -/

/-- **The comparison of restriction in two steps carried by a system is the canonical one, at the
class of a complex.**

Both sides are compared by composing with one common invertible leg — the right-hand factor of
`Stacks.DerivedGlueing.LocallyGiven.restrictionCompFactors'` — and
`Stacks.DerivedGlueing.eq_of_comp_right_eq_of_isIso`.  For the left-hand side that composite is
`restrictionCompFactors'` itself.  For the right-hand side it is the same statement for the
restriction datum, `Stacks.DerivedGlueing.mapDerivedCategoryComp_openModuleRestriction_factors`,
after the naturality of the identification
`Stacks.DerivedGlueing.restrictionIsoMapDerivedCategory` has moved the system's factorization
past it and `Stacks.DerivedGlueing.restrictionIsoMapDerivedCategory_inv_app_Q_comp` has replaced
each of the three remaining identifications by a canonical factorization. -/
theorem LocallyGiven.restrictionComp_hom_app_Q_eq (S : LocallyGiven X) (W V U : Opens X.carrier)
    (hWV : W ≤ V) (hVU : V ≤ U)
    (C : HomologicalComplex (SheafOfModules.{u} (restrictedRingSheaf X U))
      (ComplexShape.up ℤ)) :
    (S.restrictionComp W V U hWV hVU).hom.app (DerivedCategory.Q.obj C) =
      (restrictionIsoMapDerivedCategory S W U (hWV.trans hVU)).hom.app
          (DerivedCategory.Q.obj C) ≫
        (mapDerivedCategoryComp (openModuleRestriction X V U hVU)
              (openModuleRestriction X W V hWV) (openModuleRestriction X W U (hWV.trans hVU))
              (asIso (openModuleRestrictionComparison X W V U hWV hVU))).hom.app
            (DerivedCategory.Q.obj C) ≫
          (openModuleRestriction X W V hWV).mapDerivedCategory.map
              ((restrictionIsoMapDerivedCategory S V U hVU).inv.app
                (DerivedCategory.Q.obj C)) ≫
            (restrictionIsoMapDerivedCategory S W V hWV).inv.app
              ((S.restriction V U hVU).obj (DerivedCategory.Q.obj C)) := by
  have h1 := restrictionIsoMapDerivedCategory_inv_app_Q_comp S V U hVU C
  have h2 : (restrictionIsoMapDerivedCategory S W V hWV).inv.app
          ((S.restriction V U hVU).obj (DerivedCategory.Q.obj C)) ≫
        (S.restriction W V hWV).map ((S.restrictionFactors V U hVU).hom.app C) =
      (openModuleRestriction X W V hWV).mapDerivedCategory.map
          ((S.restrictionFactors V U hVU).hom.app C) ≫
        (restrictionIsoMapDerivedCategory S W V hWV).inv.app
          (DerivedCategory.Q.obj
            (((openModuleRestriction X V U hVU).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj C)) :=
    ((restrictionIsoMapDerivedCategory S W V hWV).inv.naturality
      ((S.restrictionFactors V U hVU).hom.app C)).symm
  have h3 := restrictionIsoMapDerivedCategory_inv_app_Q_comp S W V hWV
    (((openModuleRestriction X V U hVU).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)
  have hD := mapDerivedCategoryComp_openModuleRestriction_factors X W V U hWV hVU C
  have h0 := restrictionIsoMapDerivedCategory_hom_app_Q_comp S W U (hWV.trans hVU) C
  refine eq_of_comp_right_eq_of_isIso
    ((S.restriction W V hWV).map ((S.restrictionFactors V U hVU).hom.app C) ≫
        (S.restrictionFactors W V hWV).hom.app
          (((openModuleRestriction X V U hVU).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (openModuleRestrictionComparison X W V U hWV hVU)
            (ComplexShape.up ℤ)).app C))
    ((S.restrictionFactors W U (hWV.trans hVU)).hom.app C) ?_ ?_
  · exact S.restrictionCompFactors' W V U hWV hVU C
  · simp only [Category.assoc]
    rw [reassoc_of% h2, reassoc_of% h3, ← Functor.map_comp_assoc, h1, hD]
    exact h0

/-- **The comparison of restriction in two steps carried by a system is the canonical one**,
with the canonical comparison spelled as the lifted comparison
`Stacks.DerivedGlueing.mapDerivedCategoryComp` of
`Stacks.DerivedGlueing.openModuleRestrictionComparison`.

Both sides are natural transformations between functors out of
`Stacks.DerivedGlueing.OpenDerivedCategory X U`, so by
`CategoryTheory.Localization.natTrans_ext` it is enough to compare them at the class of a
complex, which is
`Stacks.DerivedGlueing.LocallyGiven.restrictionComp_hom_app_Q_eq`. -/
theorem LocallyGiven.restrictionComp_eq_mapDerivedCategoryComp (S : LocallyGiven X)
    (W V U : Opens X.carrier) (hWV : W ≤ V) (hVU : V ≤ U) :
    S.restrictionComp W V U hWV hVU =
      restrictionIsoMapDerivedCategory S W U (hWV.trans hVU) ≪≫
        mapDerivedCategoryComp (openModuleRestriction X V U hVU)
            (openModuleRestriction X W V hWV) (openModuleRestriction X W U (hWV.trans hVU))
            (asIso (openModuleRestrictionComparison X W V U hWV hVU)) ≪≫
          Functor.isoWhiskerRight (restrictionIsoMapDerivedCategory S V U hVU).symm
              (openModuleRestriction X W V hWV).mapDerivedCategory ≪≫
            Functor.isoWhiskerLeft (S.restriction V U hVU)
              (restrictionIsoMapDerivedCategory S W V hWV).symm := by
  refine Iso.ext (Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (restrictedRingSheaf X U))
      (ComplexShape.up ℤ)) fun C => ?_)
  simpa using S.restrictionComp_hom_app_Q_eq W V U hWV hVU C

/-- **The comparison of restriction in two steps carried by a system is the canonical one, read
at an object**, with the canonical comparison spelled as the lifted comparison
`Stacks.DerivedGlueing.mapDerivedCategoryComp`. -/
theorem LocallyGiven.restrictionComp_hom_app_eq (S : LocallyGiven X) (W V U : Opens X.carrier)
    (hWV : W ≤ V) (hVU : V ≤ U) (K : OpenDerivedCategory X U) :
    (S.restrictionComp W V U hWV hVU).hom.app K =
      (restrictionIsoMapDerivedCategory S W U (hWV.trans hVU)).hom.app K ≫
        (mapDerivedCategoryComp (openModuleRestriction X V U hVU)
              (openModuleRestriction X W V hWV) (openModuleRestriction X W U (hWV.trans hVU))
              (asIso (openModuleRestrictionComparison X W V U hWV hVU))).hom.app K ≫
          (openModuleRestriction X W V hWV).mapDerivedCategory.map
              ((restrictionIsoMapDerivedCategory S V U hVU).inv.app K) ≫
            (restrictionIsoMapDerivedCategory S W V hWV).inv.app
              ((S.restriction V U hVU).obj K) := by
  rw [S.restrictionComp_eq_mapDerivedCategoryComp W V U hWV hVU]
  simp

/-- **The comparison of restriction in two steps carried by an arbitrary system of locally given
derived objects is the canonical one.** For a chain `W ⊆ V ⊆ U` of opens, the comparison
`S.restrictionComp W V U` is the comparison carried by the restriction datum
`Stacks.DerivedGlueing.restrictionDatum` — the one induced on derived categories by the counit of
extension by zero on the middle open — conjugated by the identification
`Stacks.DerivedGlueing.restrictionIsoMapDerivedCategory` of the displayed restriction with the
functor induced by restriction of complexes.

So the field `restrictionComp` of `Stacks.DerivedGlueing.LocallyGiven` carries no choice: it is
determined by `restriction` and `restrictionFactors`.

This is
`Stacks.DerivedGlueing.LocallyGiven.restrictionComp_eq_mapDerivedCategoryComp` with the
restriction datum's comparison in place of its definition,
`Stacks.DerivedGlueing.restrictionDatum_restrictionComp_eq`. -/
theorem LocallyGiven.restrictionComp_eq (S : LocallyGiven X) (W V U : Opens X.carrier)
    (hWV : W ≤ V) (hVU : V ≤ U) :
    S.restrictionComp W V U hWV hVU =
      restrictionIsoMapDerivedCategory S W U (hWV.trans hVU) ≪≫
        (restrictionDatum X).restrictionComp W V U hWV hVU ≪≫
          Functor.isoWhiskerRight (restrictionIsoMapDerivedCategory S V U hVU).symm
              (openModuleRestriction X W V hWV).mapDerivedCategory ≪≫
            Functor.isoWhiskerLeft (S.restriction V U hVU)
              (restrictionIsoMapDerivedCategory S W V hWV).symm :=
  S.restrictionComp_eq_mapDerivedCategoryComp W V U hWV hVU

/-- **The comparison of restriction in two steps carried by an arbitrary system of locally given
derived objects is the canonical one, read at an object.** This is the componentwise form of
`Stacks.DerivedGlueing.LocallyGiven.restrictionComp_eq`: at every object `K` of the derived
category over `U`, the component `(S.restrictionComp W V U hWV hVU).hom.app K` is the canonical
component `((restrictionDatum X).restrictionComp W V U hWV hVU).hom.app K` conjugated by
components of `Stacks.DerivedGlueing.restrictionIsoMapDerivedCategory`. -/
theorem LocallyGiven.restrictionComp_eq_app (S : LocallyGiven X) (W V U : Opens X.carrier)
    (hWV : W ≤ V) (hVU : V ≤ U) (K : OpenDerivedCategory X U) :
    (S.restrictionComp W V U hWV hVU).hom.app K =
      (restrictionIsoMapDerivedCategory S W U (hWV.trans hVU)).hom.app K ≫
        ((restrictionDatum X).restrictionComp W V U hWV hVU).hom.app K ≫
          (openModuleRestriction X W V hWV).mapDerivedCategory.map
              ((restrictionIsoMapDerivedCategory S V U hVU).inv.app K) ≫
            (restrictionIsoMapDerivedCategory S W V hWV).inv.app
              ((S.restriction V U hVU).obj K) :=
  S.restrictionComp_hom_app_eq W V U hWV hVU K

end Derived

end Stacks.DerivedGlueing

end
