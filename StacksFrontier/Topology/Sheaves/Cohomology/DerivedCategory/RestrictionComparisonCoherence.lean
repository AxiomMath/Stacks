module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.LocallyGivenObjects

/-!
# The coherence of the comparisons of restriction in one and in two steps

Let `X` be a ringed space and let `S` be a system of locally given derived objects on it, as in
Situation 0D67.  For a chain `W ⊆ T ⊆ O ⊆ U` of open subsets, comparing restriction from `U` to
`W` first through `O` and then through `T` agrees with comparing it first through `T` and then
through `O`.  This file proves that coherence, for *every* system.

The coherence is a property, not extra data.  The field `restrictionCompFactors` of
`Stacks.DerivedGlueing.LocallyGiven` pins each comparison down, on the image of the localization
functor `DerivedCategory.Q`, to the one induced on complexes of sheaves of modules by the counit
of extension by zero on the middle open; and on sheaves of modules the coherence *is* the
naturality of that counit, nothing else.  Since both sides of the coherence are natural
transformations between functors out of a derived category,
`CategoryTheory.Localization.natTrans_ext` promotes the equality from the image of `Q` to every
object.

## Main results

* `Stacks.DerivedGlueing.openModuleRestrictionComparison_pentagon` — the coherence on sheaves of
  modules: the naturality of the counit of extension by zero.
* `Stacks.DerivedGlueing.mapHomologicalComplex_openModuleRestrictionComparison_pentagon` — the
  same, degreewise, on complexes of sheaves of modules.
* `Stacks.DerivedGlueing.LocallyGiven.restrictionCompFactors'` — the field
  `restrictionCompFactors` with the identification of the two readings of a composite
  prolongation removed, that identification being the identity.
* `Stacks.DerivedGlueing.LocallyGiven.restrictionComp_pentagon` — the coherence in the derived
  categories, for every system of locally given derived objects.

## Implementation notes

Restriction from `U` to `V ⊆ U` is extension by zero from `U` followed by restriction to `V`, so
the comparison for a nested pair `W ⊆ V ⊆ U` is the counit `j_!j^* ⟶ 𝟭` of the
extension-by-zero adjunction on `V`, evaluated at the extension by zero of the argument from `U`
and then restricted to `W`.  The coherence along `W ⊆ T ⊆ O ⊆ U` is the naturality square of the
counit on `T` at the component of the counit on `O`.

The equality in the derived categories is reduced to its instances at `DerivedCategory.Q.obj C`
by `CategoryTheory.Localization.natTrans_ext`, and there each of the four comparisons involved is
replaced by the complex-level data of `restrictionCompFactors`.  The resulting identity is the
degreewise coherence, transported across the comparison isomorphisms `restrictionFactors` by
their naturality.

## References

* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ExtensionByZeroModules

namespace Stacks.DerivedGlueing

universe v₁ u₁ u

/-! ### A cancellation lemma -/

/-- **Two factorisations of one isomorphism through a common morphism agree.** If `l ≫ e` is
invertible and `l` is invertible, then so is `e`; it is therefore cancellable, so a second
morphism `r` with `r ≫ e = l ≫ e` equals `l`. -/
theorem eq_of_comp_right_eq_of_isIso {𝒟 : Type u₁} [Category.{v₁} 𝒟] {A B D : 𝒟} {l r : A ⟶ B}
    (e : B ⟶ D) (i : A ⟶ D) [IsIso l] [IsIso i] (hl : l ≫ e = i) (hr : r ≫ e = i) : l = r := by
  have : IsIso e := by
    have he : e = inv l ≫ i := by rw [← hl, IsIso.inv_hom_id_assoc]
    rw [he]
    infer_instance
  exact (cancel_mono e).mp (hl.trans hr.symm)

/-! ### The identification of the two readings of a composite prolongation -/

/-- The prolongation to complexes of a composite of additive functors is the composite of the
prolongations, and the identification of the two readings is the identity: the prolongation acts
degreewise. -/
@[simp]
theorem mapHomologicalComplexCompIso_refl_hom_app {V₁ V₂ V₃ : Type*} [Category V₁] [Category V₂]
    [Category V₃] [Preadditive V₁] [Preadditive V₂] [Preadditive V₃] {ι : Type*}
    (F : V₁ ⥤ V₂) (G : V₂ ⥤ V₃) [F.Additive] [G.Additive] (c : ComplexShape ι)
    (C : HomologicalComplex V₁ c) :
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) c).hom.app C = 𝟙 _ := by
  ext n
  simp

/-! ### The coherence on sheaves of modules -/

/-- The comparison from restriction in two steps to direct restriction, evaluated at a sheaf of
modules: the counit of extension by zero on the middle open, taken at the extension by zero from
the largest open and restricted to the smallest. -/
theorem openModuleRestrictionComparison_app (X : RingedSpace.{u, u}) (W V U : Opens X.carrier)
    (hWV : W ≤ V) (hVU : V ≤ U) (M : SheafOfModules.{u} (restrictedRingSheaf X U)) :
    (openModuleRestrictionComparison X W V U hWV hVU).app M =
      (jStar W (underlyingRingSheaf X)).map
        ((jShriekAdjunction V (underlyingRingSheaf X)).counit.app
          ((jShriek U (underlyingRingSheaf X)).obj M)) :=
  rfl

/-- **The associativity of the comparisons of restriction, on sheaves of modules.** For a chain
`W ⊆ T ⊆ O ⊆ U` of opens, comparing restriction from `U` to `W` first through `O` and then
through `T` agrees with comparing it first through `T` and then through `O`.

Both composites are the restriction to `W` of a composite of two counits of extension by zero,
and the two orders agree by the naturality of the counit on `T` at the component of the counit
on `O`. -/
theorem openModuleRestrictionComparison_pentagon (X : RingedSpace.{u, u})
    (W T O U : Opens X.carrier) (hWT : W ≤ T) (hTO : T ≤ O) (hOU : O ≤ U)
    (N : SheafOfModules.{u} (restrictedRingSheaf X U)) :
    (openModuleRestriction X W T hWT).map
          ((openModuleRestrictionComparison X T O U hTO hOU).app N) ≫
        (openModuleRestrictionComparison X W T U hWT (hTO.trans hOU)).app N =
      (openModuleRestrictionComparison X W T O hWT hTO).app
          ((openModuleRestriction X O U hOU).obj N) ≫
        (openModuleRestrictionComparison X W O U (hWT.trans hTO) hOU).app N := by
  have key := (jShriekAdjunction T (underlyingRingSheaf X)).counit.naturality
    ((jShriekAdjunction O (underlyingRingSheaf X)).counit.app
      ((jShriek U (underlyingRingSheaf X)).obj N))
  simp only [Functor.comp_map, Functor.id_map] at key
  simp only [openModuleRestrictionComparison_app, openModuleRestriction, Functor.comp_map,
    Functor.comp_obj, ← Functor.map_comp]
  exact congrArg (jStar W (underlyingRingSheaf X)).map key

/-- **The associativity of the comparisons of restriction, on complexes of sheaves of modules.**
The prolongation of the comparisons to complexes is degreewise the comparison, so this is
`Stacks.DerivedGlueing.openModuleRestrictionComparison_pentagon` in each degree. -/
theorem mapHomologicalComplex_openModuleRestrictionComparison_pentagon (X : RingedSpace.{u, u})
    (W T O U : Opens X.carrier) (hWT : W ≤ T) (hTO : T ≤ O) (hOU : O ≤ U)
    (C : HomologicalComplex (SheafOfModules.{u} (restrictedRingSheaf X U))
      (ComplexShape.up ℤ)) :
    ((openModuleRestriction X W T hWT).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (openModuleRestrictionComparison X T O U hTO hOU)
            (ComplexShape.up ℤ)).app C) ≫
        (NatTrans.mapHomologicalComplex
            (openModuleRestrictionComparison X W T U hWT (hTO.trans hOU))
            (ComplexShape.up ℤ)).app C =
      (NatTrans.mapHomologicalComplex (openModuleRestrictionComparison X W T O hWT hTO)
            (ComplexShape.up ℤ)).app
          (((openModuleRestriction X O U hOU).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C) ≫
        (NatTrans.mapHomologicalComplex
            (openModuleRestrictionComparison X W O U (hWT.trans hTO) hOU)
            (ComplexShape.up ℤ)).app C := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  simpa using openModuleRestrictionComparison_pentagon X W T O U hWT hTO hOU (C.X n)

/-! ### The coherence in the derived categories -/

section Derived

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-- **The field `restrictionCompFactors`, with the identity comparison removed.** The
identification of the two readings of the composite prolongation that
`Stacks.DerivedGlueing.LocallyGiven.restrictionCompFactors` inserts is the identity, by
`Stacks.DerivedGlueing.mapHomologicalComplexCompIso_refl_hom_app`; what is left is that the
comparison `restrictionComp`, read at the class of a complex, is the prolongation of
`Stacks.DerivedGlueing.openModuleRestrictionComparison`. -/
theorem LocallyGiven.restrictionCompFactors' (S : LocallyGiven X) (W V U : Opens X.carrier)
    (hWV : W ≤ V) (hVU : V ≤ U)
    (C : HomologicalComplex (SheafOfModules.{u} (restrictedRingSheaf X U))
      (ComplexShape.up ℤ)) :
    (S.restrictionComp W V U hWV hVU).hom.app (DerivedCategory.Q.obj C) ≫
        (S.restriction W V hWV).map ((S.restrictionFactors V U hVU).hom.app C) ≫
        (S.restrictionFactors W V hWV).hom.app
          (((openModuleRestriction X V U hVU).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (openModuleRestrictionComparison X W V U hWV hVU)
            (ComplexShape.up ℤ)).app C) =
      (S.restrictionFactors W U (hWV.trans hVU)).hom.app C := by
  simpa using S.restrictionCompFactors W V U hWV hVU C

/-- The coherence of the comparisons of restriction, at the class of a complex. -/
theorem LocallyGiven.restrictionComp_pentagon_app_Q (S : LocallyGiven X)
    (W T O U : Opens X.carrier) (hWT : W ≤ T) (hTO : T ≤ O) (hOU : O ≤ U)
    (C : HomologicalComplex (SheafOfModules.{u} (restrictedRingSheaf X U))
      (ComplexShape.up ℤ)) :
    (S.restrictionComp W O U (hWT.trans hTO) hOU).hom.app (DerivedCategory.Q.obj C) ≫
        (S.restrictionComp W T O hWT hTO).hom.app
          ((S.restriction O U hOU).obj (DerivedCategory.Q.obj C)) =
      (S.restrictionComp W T U hWT (hTO.trans hOU)).hom.app (DerivedCategory.Q.obj C) ≫
        (S.restriction W T hWT).map
          ((S.restrictionComp T O U hTO hOU).hom.app (DerivedCategory.Q.obj C)) := by
  have hN := ((S.restrictionComp W T O hWT hTO).hom.naturality
      ((S.restrictionFactors O U hOU).hom.app C)).symm
  have hθ : (S.restrictionFactors W T hWT).hom.app
          (((openModuleRestriction X T O hTO).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((openModuleRestriction X O U hOU).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj C)) ≫
        DerivedCategory.Q.map
          (((openModuleRestriction X W T hWT).mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex (openModuleRestrictionComparison X T O U hTO hOU)
              (ComplexShape.up ℤ)).app C)) =
      (S.restriction W T hWT).map
          (DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (openModuleRestrictionComparison X T O U hTO hOU)
              (ComplexShape.up ℤ)).app C)) ≫
        (S.restrictionFactors W T hWT).hom.app
          (((openModuleRestriction X T U (hTO.trans hOU)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C) :=
    ((S.restrictionFactors W T hWT).hom.naturality
      ((NatTrans.mapHomologicalComplex (openModuleRestrictionComparison X T O U hTO hOU)
        (ComplexShape.up ℤ)).app C)).symm
  have hE1 := S.restrictionCompFactors' W O U (hWT.trans hTO) hOU C
  have hE2 := S.restrictionCompFactors' W T O hWT hTO
    (((openModuleRestriction X O U hOU).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)
  have hE3 := S.restrictionCompFactors' W T U hWT (hTO.trans hOU) C
  have hE4 := S.restrictionCompFactors' T O U hTO hOU C
  have hP := mapHomologicalComplex_openModuleRestrictionComparison_pentagon X W T O U
    hWT hTO hOU C
  refine eq_of_comp_right_eq_of_isIso
    ((S.restriction T O hTO ⋙ S.restriction W T hWT).map
          ((S.restrictionFactors O U hOU).hom.app C) ≫
        (S.restriction W T hWT).map
          ((S.restrictionFactors T O hTO).hom.app
            (((openModuleRestriction X O U hOU).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj C)) ≫
        (S.restrictionFactors W T hWT).hom.app
          (((openModuleRestriction X T O hTO).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((openModuleRestriction X O U hOU).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj C)) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (openModuleRestrictionComparison X W T O hWT hTO)
            (ComplexShape.up ℤ)).app
              (((openModuleRestriction X O U hOU).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj C)) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
            (openModuleRestrictionComparison X W O U (hWT.trans hTO) hOU)
            (ComplexShape.up ℤ)).app C))
    ((S.restrictionFactors W U ((hWT.trans hTO).trans hOU)).hom.app C) ?_ ?_
  · simp only [Category.assoc, Functor.comp_map]
    rw [reassoc_of% hN, reassoc_of% hE2]
    exact hE1
  · simp only [Category.assoc, Functor.comp_map]
    rw [← DerivedCategory.Q.map_comp, ← hP, DerivedCategory.Q.map_comp, reassoc_of% hθ,
      ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
    simp only [Category.assoc]
    rw [hE4]
    exact hE3

/-- **The associativity of the comparisons of restriction of Situation 0D67.** For a system of
locally given derived objects and a chain `W ⊆ T ⊆ O ⊆ U` of opens, comparing restriction from
`U` to `W` first through `O` and then through `T` agrees with comparing it first through `T` and
then through `O`.

Both sides are natural transformations between functors out of
`Stacks.DerivedGlueing.OpenDerivedCategory X U`, so by
`CategoryTheory.Localization.natTrans_ext` it is enough to compare them at the class of a
complex, which is
`Stacks.DerivedGlueing.LocallyGiven.restrictionComp_pentagon_app_Q`. -/
theorem LocallyGiven.restrictionComp_pentagon (S : LocallyGiven X)
    (W T O U : Opens X.carrier) (hWT : W ≤ T) (hTO : T ≤ O) (hOU : O ≤ U)
    (K : OpenDerivedCategory X U) :
    (S.restrictionComp W O U (hWT.trans hTO) hOU).hom.app K ≫
        (S.restrictionComp W T O hWT hTO).hom.app ((S.restriction O U hOU).obj K) =
      (S.restrictionComp W T U hWT (hTO.trans hOU)).hom.app K ≫
        (S.restriction W T hWT).map ((S.restrictionComp T O U hTO hOU).hom.app K) := by
  have h : (S.restrictionComp W O U (hWT.trans hTO) hOU).hom ≫
        Functor.whiskerLeft (S.restriction O U hOU) (S.restrictionComp W T O hWT hTO).hom =
      (S.restrictionComp W T U hWT (hTO.trans hOU)).hom ≫
        Functor.whiskerRight (S.restrictionComp T O U hTO hOU).hom (S.restriction W T hWT) :=
    Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (restrictedRingSheaf X U))
        (ComplexShape.up ℤ))
      fun C => S.restrictionComp_pentagon_app_Q W T O U hWT hTO hOU C
  simpa using NatTrans.congr_app h K

end Derived

end Stacks.DerivedGlueing

end
