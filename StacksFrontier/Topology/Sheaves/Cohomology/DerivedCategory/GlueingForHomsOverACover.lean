module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HomGluingOverACoveringCollection
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.TwoOpenGlueingInput
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOverACover

/-!
# The glueing of morphisms over a covering collection, in the vocabulary of Situation 0D67
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ExtensionByZeroModules RingedSpaceModuleAdjunction

namespace Stacks.DerivedGlueing

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃ u

/-! ### Two cancellations -/

/-- **The component of the inverse of an isomorphism of functors, identified by a right inverse
of the component of the isomorphism.**  Stated separately, with the object and the morphism
variables, so that it can be applied by `exact` where a rewrite would have to cross the
identification of two spellings of a functor. -/
theorem natIso_inv_app_eq_of_comp_eq_id {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {F G : C ⥤ D} (α : F ≅ G) (Y : C) (h : G.obj Y ⟶ F.obj Y)
    (H : α.hom.app Y ≫ h = 𝟙 (F.obj Y)) : α.inv.app Y = h :=
  have : IsIso (α.hom.app Y) := inferInstanceAs (IsIso (α.app Y).hom)
  ((cancel_epi (α.hom.app Y)).mp (H.trans (α.hom_inv_id_app Y).symm)).symm

/-- **Two conjugations of one morphism by isomorphisms agree once the isomorphisms are
compared.**  If `Λ : Φ ≅ Φ'` and the comparisons of the source and the target with the values of
`Φ` become, after composing with `Λ`, the comparisons with the values of `Φ'`, then conjugating a
morphism `χ` by the first pair is conjugating it by the second.

This is what reduces the identification of two restrictions of morphisms to a single equation
between the two comparison isomorphisms. -/
theorem conj_eq_conj_of_iso {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {Φ Φ' : C ⥤ D} (Λ : Φ ≅ Φ') {a b : D} {x y : C} (α : a ≅ Φ.obj x) (α' : a ≅ Φ'.obj x)
    (β : b ≅ Φ.obj y) (β' : b ≅ Φ'.obj y) (hα : α ≪≫ Λ.app x = α') (hβ : β ≪≫ Λ.app y = β')
    (χ : x ⟶ y) :
    α.hom ≫ Φ.map χ ≫ β.inv = α'.hom ≫ Φ'.map χ ≫ β'.inv := by
  subst hα
  subst hβ
  have hnat : Φ.map χ ≫ (Λ.app y).hom = (Λ.app x).hom ≫ Φ'.map χ := Λ.hom.naturality χ
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]
  rw [← reassoc_of% hnat, Iso.hom_inv_id_assoc]


/-! ### An exact equivalence induces an equivalence of derived categories -/

section Generic

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

/-! #### The two lifted comparisons, read at the class of a complex -/

/-- **`Stacks.DerivedGlueing.mapDerivedCategoryCongr` is
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso`.**  The two definitions have
the same body — the same `CategoryTheory.Localization.liftNatIso` of the same degreewise datum —
so this is `rfl`; only the second one carries the computations at the class of a complex.  The
duplication is free to collapse. -/
theorem mapDerivedCategoryCongr_eq {F F' : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] [F'.Additive] [PreservesFiniteLimits F']
    [PreservesFiniteColimits F'] (e : F ≅ F') :
    mapDerivedCategoryCongr e =
      Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso F F' e :=
  rfl

/-- **`Stacks.DerivedGlueing.mapDerivedCategoryCongr`, read at the class of a complex**: the
canonical factorization of each of the two induced functors, with the isomorphism applied
degreewise in between. -/
theorem mapDerivedCategoryCongr_hom_app_Q {F F' : C₁ ⥤ C₂} [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F'.Additive]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F'] (e : F ≅ F')
    (P : CochainComplex C₁ ℤ) :
    (mapDerivedCategoryCongr e).hom.app (DerivedCategory.Q.obj P) =
      F.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app P) ≫
          F'.mapDerivedCategoryFactors.inv.app P := by
  rw [mapDerivedCategoryCongr_eq]
  exact Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_hom_app_Q F F' e P

/-- **`Stacks.DerivedGlueing.mapDerivedCategoryCongr` in the other direction, read at the class of
a complex.** -/
theorem mapDerivedCategoryCongr_inv_app_Q {F F' : C₁ ⥤ C₂} [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F'.Additive]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F'] (e : F ≅ F')
    (P : CochainComplex C₁ ℤ) :
    (mapDerivedCategoryCongr e).inv.app (DerivedCategory.Q.obj P) =
      F'.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).inv.app P) ≫
          F.mapDerivedCategoryFactors.inv.app P := by
  rw [mapDerivedCategoryCongr_eq]
  exact Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_inv_app_Q F F' e P

/-- **`Stacks.DerivedGlueing.mapDerivedCategoryCompIso`, read at the class of a complex**: the
canonical factorization of each of the three induced functors involved.  The identification of
the two readings of the composite prolongation that the definition inserts is the identity, by
`Stacks.DerivedGlueing.mapHomologicalComplexCompIso_refl_hom_app`. -/
theorem mapDerivedCategoryCompIso_hom_app_Q (F : C₁ ⥤ C₂) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (G : C₂ ⥤ C₃) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] [(F ⋙ G).Additive]
    [PreservesFiniteLimits (F ⋙ G)] [PreservesFiniteColimits (F ⋙ G)]
    (P : CochainComplex C₁ ℤ) :
    (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj P) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (F ⋙ G).mapDerivedCategoryFactors.inv.app P := by
  simp [mapDerivedCategoryCompIso, Localization.Lifting.iso]

/-- `Stacks.DerivedGlueing.mapDerivedCategoryCompIso`, read at the class of a complex and
followed by the canonical factorization of the composite: the two factorizations in turn. -/
theorem mapDerivedCategoryCompIso_hom_app_Q_comp (F : C₁ ⥤ C₂) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (G : C₂ ⥤ C₃) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] [(F ⋙ G).Additive]
    [PreservesFiniteLimits (F ⋙ G)] [PreservesFiniteColimits (F ⋙ G)]
    (P : CochainComplex C₁ ℤ) :
    (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj P) ≫
        (F ⋙ G).mapDerivedCategoryFactors.hom.app P =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  rw [mapDerivedCategoryCompIso_hom_app_Q, Category.assoc, Category.assoc,
    Iso.inv_hom_id_app]
  exact (Category.assoc _ _ _).symm.trans (Category.comp_id _)

/-- **`Stacks.DerivedGlueing.mapDerivedCategoryCompIso` in the other direction, read at the class
of a complex**: the inverse of `Stacks.DerivedGlueing.mapDerivedCategoryCompIso_hom_app_Q`. -/
theorem mapDerivedCategoryCompIso_inv_app_Q (F : C₁ ⥤ C₂) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (G : C₂ ⥤ C₃) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] [(F ⋙ G).Additive]
    [PreservesFiniteLimits (F ⋙ G)] [PreservesFiniteColimits (F ⋙ G)]
    (P : CochainComplex C₁ ℤ) :
    (mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj P) =
      (F ⋙ G).mapDerivedCategoryFactors.hom.app P ≫
        G.mapDerivedCategoryFactors.inv.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app P) := by
  rw [← cancel_epi ((mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj P)),
    Iso.hom_inv_id_app, mapDerivedCategoryCompIso_hom_app_Q]
  simp [← Functor.map_comp]

/-- **An equivalence of abelian categories whose two halves are exact induces an equivalence of
unbounded derived categories.**  The two composite comparisons are
`Stacks.DerivedGlueing.mapDerivedCategoryCompIso` followed by the derived action of the unit and
the counit, `Stacks.DerivedGlueing.mapDerivedCategoryCongr`, and
`Stacks.Homology.mapDerivedCategoryIdIso`; `CategoryTheory.Equivalence.mk` adjointifies the unit,
so their coherence is not needed.

This is the companion of `Stacks.DerivedGlueing.faithful_mapDerivedCategory_of_comp`, which
extracts only faithfulness from the first of the two. -/
def mapDerivedCategoryEquivalence (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (G : C₂ ⥤ C₁) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] (η : 𝟭 C₁ ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 C₂) :
    DerivedCategory C₁ ≌ DerivedCategory C₂ :=
  have := comp_preservesFiniteLimits F G
  have := comp_preservesFiniteColimits F G
  have := comp_preservesFiniteLimits G F
  have := comp_preservesFiniteColimits G F
  CategoryTheory.Equivalence.mk F.mapDerivedCategory G.mapDerivedCategory
    (Stacks.Homology.mapDerivedCategoryIdIso.symm ≪≫ mapDerivedCategoryCongr η ≪≫
      (mapDerivedCategoryCompIso F G).symm)
    (mapDerivedCategoryCompIso G F ≪≫ mapDerivedCategoryCongr ε ≪≫
      Stacks.Homology.mapDerivedCategoryIdIso)

/-- **One half of an exact equivalence is full on unbounded derived categories.** -/
theorem full_mapDerivedCategory_of_equivalence (F : C₁ ⥤ C₂) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (G : C₂ ⥤ C₁) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (η : 𝟭 C₁ ≅ F ⋙ G)
    (ε : G ⋙ F ≅ 𝟭 C₂) :
    F.mapDerivedCategory.Full :=
  inferInstanceAs (mapDerivedCategoryEquivalence F G η ε).functor.Full

end Generic

/-! ### Restriction to an open subspace, read on the slice site -/

section Slice

variable {Z : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology Z) RingCat.{u})

/-- Passing between the two models of modules on an open is full, being one half of an
equivalence. -/
instance sliceToSubspace_full (U : Opens Z) : (sliceToSubspace O U).Full :=
  inferInstanceAs (U.sheafOfModulesEquivOver O).functor.Full

/-- Passing between the two models of modules on an open is faithful, being one half of an
equivalence. -/
instance sliceToSubspace_faithful (U : Opens Z) : (sliceToSubspace O U).Faithful :=
  inferInstanceAs (U.sheafOfModulesEquivOver O).functor.Faithful

/-- Restriction of modules to the opens contained in an open, followed by restriction to the
opens contained in a smaller one, is restriction to the opens contained in the smaller one.  This
is the equality of functors underlying Mathlib's `CategoryTheory.SheafOfModules.overFunctorMap`,
which holds on the nose. -/
theorem overFunctor_comp_overMap {T W : Opens Z} (hTW : T ≤ W) :
    SheafOfModules.overFunctor.{u} O W ⋙ SheafOfModules.overMap.{u} O hTW.hom =
      SheafOfModules.overFunctor.{u} O T :=
  rfl

/-- **Restriction to the opens contained in `W`, then to those contained in `T ⊆ W`, then the
passage to the open-subspace model, is restriction to the open subspace `T`.**

The proof chains `Stacks.DerivedGlueing.overFunctor_comp_overMap` with
`Stacks.DerivedGlueing.overFunctor_comp_sliceToSubspace` through a reassociation rather than
asking for the composite equality directly: the direct `rfl` compares the two spellings of a
*module* and costs upwards of half a million heartbeats, exactly as the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Slice/RestrictionOfDerivedHoms.lean` record.  This
is why the comparisons below are stated with the composite spelling and not with `jStar`. -/
theorem overFunctor_comp_overMap_comp_sliceToSubspace {T W : Opens Z} (hTW : T ≤ W) :
    SheafOfModules.overFunctor.{u} O W ⋙
        (SheafOfModules.overMap.{u} O hTW.hom ⋙ sliceToSubspace O T) =
      jStar T O :=
  (Functor.assoc _ _ _).symm.trans
    ((congrArg (fun F => F ⋙ sliceToSubspace O T) (overFunctor_comp_overMap O hTW)).trans
      (overFunctor_comp_sliceToSubspace O T))

/-- **Reading a module on the slice over `U` in the open-subspace model, extending it by zero and
restricting it back to the open subspace `U`, is reading it in the open-subspace model.**  This
is the invertible unit of extension by zero and restriction to the open subspace
([Stacks, Tag 00AB], `ExtensionByZeroModules.isIso_jShriekAdjunction_unit`), with the equality of
functors `Stacks.DerivedGlueing.overFunctor_comp_sliceToSubspace` inserted so that the source is
the composite that `Stacks.DerivedGlueing.sliceExtendOverIso` has to compare. -/
def sliceExtendOverCompIso (U : Opens Z) :
    (sliceToSubspace O U ⋙ jShriek U O ⋙ SheafOfModules.overFunctor.{u} O U) ⋙
        sliceToSubspace O U ≅
      𝟭 (SheafOfModules.{u} (O.over U)) ⋙ sliceToSubspace O U :=
  eqToIso
      ((Functor.assoc _ _ _).trans
        (congrArg (fun F => sliceToSubspace O U ⋙ F)
          ((Functor.assoc _ _ _).trans
            (congrArg (fun F => jShriek U O ⋙ F)
              (overFunctor_comp_sliceToSubspace O U))))) ≪≫
    Functor.isoWhiskerLeft (sliceToSubspace O U)
      (@asIso _ _ _ _ (jShriekAdjunction U O).unit
        (isIso_jShriekAdjunction_unit U O)).symm

/-- **Reading a module on the slice over `U` in the open-subspace model, extending it by zero and
restricting it back to the slice over `U`, is the identity.**

This is `Stacks.DerivedGlueing.sliceExtendOverCompIso` descended along the passage between the
two models of modules on `U`, which is fully faithful. -/
def sliceExtendOverIso (U : Opens Z) :
    sliceToSubspace O U ⋙ jShriek U O ⋙ SheafOfModules.overFunctor.{u} O U ≅
      𝟭 (SheafOfModules.{u} (O.over U)) :=
  Functor.fullyFaithfulCancelRight (sliceToSubspace O U) (sliceExtendOverCompIso O U)

/-- **Restricting a module on the slice over `W` to the slice over a smaller open `T`, read in the
open-subspace model, is reading it in the open-subspace model of `W`, extending it by zero and
restricting it again.**

This is `Stacks.DerivedGlueing.sliceExtendOverIso` with the restriction to `T` appended; it is
the comparison that identifies the restriction of morphisms of a system of locally given derived
objects with the restriction of morphisms along an arrow of the ringed site. -/
def sliceRestrictOverIso {T W : Opens Z} (hTW : T ≤ W) :
    (sliceToSubspace O W ⋙ jShriek W O ⋙ SheafOfModules.overFunctor.{u} O W) ⋙
        (SheafOfModules.overMap.{u} O hTW.hom ⋙ sliceToSubspace O T) ≅
      SheafOfModules.overMap.{u} O hTW.hom ⋙ sliceToSubspace O T :=
  Functor.isoWhiskerRight (sliceExtendOverIso O W)
    (SheafOfModules.overMap.{u} O hTW.hom ⋙ sliceToSubspace O T)

/-- The comparison of `Stacks.DerivedGlueing.sliceRestrictOverIso` is
`Stacks.DerivedGlueing.sliceExtendOverIso` restricted to the opens contained in `T`. -/
theorem sliceRestrictOverIso_hom_app {T W : Opens Z} (hTW : T ≤ W)
    (N : SheafOfModules.{u} (O.over W)) :
    (sliceRestrictOverIso O hTW).hom.app N =
      (SheafOfModules.overMap.{u} O hTW.hom ⋙ sliceToSubspace O T).map
        ((sliceExtendOverIso O W).hom.app N) :=
  rfl

/-- The comparison of `Stacks.DerivedGlueing.sliceExtendOverIso`, read in the open-subspace
model, is the inverse of the unit of extension by zero, up to the identification of the two
spellings of restriction to the open subspace. -/
theorem sliceToSubspace_map_sliceExtendOverIso_hom_app (U : Opens Z)
    (N : SheafOfModules.{u} (O.over U)) :
    (sliceToSubspace O U).map ((sliceExtendOverIso O U).hom.app N) =
      (sliceExtendOverCompIso O U).hom.app N :=
  Functor.map_preimage _ _

end Slice

/-! ### The two models of modules on an open, on unbounded derived categories -/

section SliceDerived

variable {Z : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology Z) RingCat.{u})

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Passing between the two models of modules on an open is full on derived categories.**
Together with `Stacks.DerivedGlueing.faithful_sliceToSubspace_mapDerivedCategory` this says that
a morphism between the open-subspace readings of two objects of the derived category of the slice
over `U` comes from a unique morphism there — which is what carries a family of morphisms given
in the vocabulary of Situation 0D67 to a family in the vocabulary of the ringed site. -/
theorem full_sliceToSubspace_mapDerivedCategory (U : Opens Z) :
    (sliceToSubspace O U).mapDerivedCategory.Full :=
  full_mapDerivedCategory_of_equivalence (sliceToSubspace O U) (subspaceToSlice O U)
    (U.sheafOfModulesEquivOver O).unitIso (U.sheafOfModulesEquivOver O).counitIso

end SliceDerived

end Stacks.DerivedGlueing

end
