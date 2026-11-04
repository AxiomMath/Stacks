module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.PointDetection
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology

/-!
# A complex supported at a closed point is the derived skyscraper of its stalk

Let `X` be a scheme and `x` a closed point. The stalk functor at `x` is left adjoint to the
skyscraper functor at `x`, both exact, so the adjunction descends to the derived categories:
`(-)_x ⊣ i_{x,*}` on `D(𝒪_X)` and `D(𝒪_{X,x})`. If `M ∈ D(𝒪_X)` has zero derived stalk at every
point other than `x`, the unit `M ⟶ i_{x,*}(M_x)` is an isomorphism: it is so on stalks at `x`
because the counit `(i_{x,*}N)_x ⟶ N` is an isomorphism, and at every other point both sides
vanish, the skyscraper at a closed point having zero stalk away from it.

## Main results

* `StacksDraft.DerivedRingIso.isIso_mapDerivedCategoryAdjunction_counit`: the derived counit is
  invertible when the abelian counit is.
* `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.isZero_stalkFunctor_skyscraperObj_of_ne`: the
  skyscraper at a closed point has zero stalk away from it.
* `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.isIso_derivedStalkAdjunction_unit_app`: the unit
  is an isomorphism at a complex supported at `x`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace StacksDraft.DerivedRingIso

variable {C D : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Category* D] [Abelian D] [HasDerivedCategory D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **The derived counit is invertible when the abelian counit is**, the mirror of
`StacksDraft.DerivedRingIso.isIso_mapDerivedCategoryAdjunction_unit`. -/
theorem isIso_mapDerivedCategoryAdjunction_counit (adj : F ⊣ G) (hadj : IsIso adj.counit) :
    IsIso (mapDerivedCategoryAdjunction adj).counit := by
  have hQ : ∀ X : CochainComplex D ℤ,
      IsIso ((mapDerivedCategoryAdjunction adj).counit.app (DerivedCategory.Q.obj X)) := by
    intro X
    have : IsIso ((NatTrans.mapHomologicalComplex adj.counit (ComplexShape.up ℤ)).app X) :=
      inferInstanceAs (IsIso ((NatIso.mapHomologicalComplex (asIso adj.counit)
        (ComplexShape.up ℤ)).hom.app X))
    have : ∀ i, IsIso (((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app X).f i) :=
      fun i => (inferInstance : IsIso (adj.counit.app (X.X i)))
    have : IsIso ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app X) :=
      HomologicalComplex.Hom.isIso_of_components _
    simp only [mapDerivedCategoryAdjunction, Adjunction.localization_counit_app]
    exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance
      (Functor.map_isIso _ _))
  rw [NatTrans.isIso_iff_isIso_app]
  intro Y
  let e := DerivedCategory.Q.objObjPreimageIso Y
  have := hQ (DerivedCategory.Q.objPreimage Y)
  have : IsIso ((G.mapDerivedCategory ⋙ F.mapDerivedCategory).map e.hom ≫
      (mapDerivedCategoryAdjunction adj).counit.app Y) := by
    rw [(mapDerivedCategoryAdjunction adj).counit.naturality e.hom]
    infer_instance
  exact IsIso.of_isIso_comp_left ((G.mapDerivedCategory ⋙ F.mapDerivedCategory).map e.hom) _

end StacksDraft.DerivedRingIso

namespace Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

attribute [local instance 100000] HasDerivedCategory.standard

variable (X : Scheme.{u}) (x : X)

/-- **The skyscraper at a closed point has zero stalk away from it.** Over an open missing `x`
the sections of the skyscraper are functions on the empty type `PLift (x ∈ U)`. -/
theorem isZero_stalkFunctor_skyscraperObj_of_ne (hx : IsClosed ({x} : Set X)) {y : X}
    (hy : y ≠ x)
    (N : ModuleCat.{u} (ToType (StacksDraft.StalkRingComparison.stalkRing X x))) :
    IsZero ((SheafOfModules.stalkFunctor X.ringCatSheaf y).obj
      (SheafOfModules.skyscraperObj X.ringCatSheaf x N)) := by
  rw [SheafOfModules.isZero_stalkFunctor_obj_iff, AddCommGrpCat.isZero_iff_subsingleton]
  refine ⟨fun a b => ?_⟩
  suffices ∀ t : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (SheafOfModules.skyscraperObj X.ringCatSheaf x N).val.presheaf y, t = 0 by
    rw [this a, this b]
  intro t
  obtain ⟨U, hyU, s, rfl⟩ := TopCat.Presheaf.germ_exist
    (SheafOfModules.skyscraperObj X.ringCatSheaf x N).val.presheaf (x := y) t
  let V : Opens X := ⟨{x}ᶜ, hx.isOpen_compl⟩
  have hyW : y ∈ U ⊓ V := ⟨hyU, hy⟩
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE (inf_le_left : U ⊓ V ≤ U)) y hyW s]
  have hsub : Subsingleton
      ((SheafOfModules.skyscraperObj X.ringCatSheaf x N).val.presheaf.obj (op (U ⊓ V))) :=
    ⟨fun f g => funext fun h => (h.down.2 rfl).elim⟩
  rw [Subsingleton.elim ((SheafOfModules.skyscraperObj X.ringCatSheaf x N).val.presheaf.map
    (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s) 0, map_zero]

/-- The derived skyscraper functor `D(𝒪_{X,x}) ⥤ D(𝒪_X)`. -/
abbrev derivedSkyscraper :
    DerivedCategory (ModuleCat.{u} (ToType (StacksDraft.StalkRingComparison.stalkRing X x))) ⥤
      DerivedCategory X.Modules :=
  (SheafOfModules.skyscraperFunctor X.ringCatSheaf x).mapDerivedCategory

/-- **The derived stalk is left adjoint to the derived skyscraper.** -/
abbrev derivedStalkAdjunction : derivedStalk X x ⊣ derivedSkyscraper X x :=
  StacksDraft.DerivedRingIso.mapDerivedCategoryAdjunction
    (SheafOfModules.stalkSkyscraperAdjunction X.ringCatSheaf x)

/-- The counit `(i_{x,*}N)_x ⟶ N` of the stalk-skyscraper adjunction is an isomorphism. -/
theorem isIso_stalkSkyscraperAdjunction_counit :
    IsIso (SheafOfModules.stalkSkyscraperAdjunction X.ringCatSheaf x).counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro N
  show IsIso (SheafOfModules.stalkSkyscraperDown X.ringCatSheaf x _ N (𝟙 _))
  unfold SheafOfModules.stalkSkyscraperDown
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ _)
    (SheafOfModules.skyscraperStalkIsoObj X.ringCatSheaf x N).isIso_hom

/-- The counit `(i_{x,*}N)_x ⟶ N` of the derived stalk-skyscraper adjunction is an isomorphism. -/
theorem isIso_derivedStalkAdjunction_counit : IsIso (derivedStalkAdjunction X x).counit :=
  StacksDraft.DerivedRingIso.isIso_mapDerivedCategoryAdjunction_counit _
    (isIso_stalkSkyscraperAdjunction_counit X x)

/-- **A complex whose derived stalks vanish away from a closed point `x` is the derived skyscraper
of its stalk at `x`**: the unit `M ⟶ i_{x,*}(M_x)` is an isomorphism. -/
theorem isIso_derivedStalkAdjunction_unit_app (hx : IsClosed ({x} : Set X))
    (M : DerivedCategory X.Modules)
    (hM : ∀ y : X, y ≠ x → IsZero ((derivedStalk X y).obj M)) :
    IsIso ((derivedStalkAdjunction X x).unit.app M) := by
  refine Stacks.Cohomology.StalkwiseIso.isIso_of_forall_stalk_isIso X.ringCatSheaf _
    fun i y => ?_
  by_cases hy : y = x
  · subst hy
    refine (Functor.isIso_homologyFunctor_map_mapDerivedCategory_map_iff
      (F := SheafOfModules.stalkFunctor X.ringCatSheaf y) _ i).1 ?_
    have := isIso_derivedStalkAdjunction_counit X y
    have hc : IsIso ((derivedStalkAdjunction X y).counit.app ((derivedStalk X y).obj M)) :=
      NatIso.isIso_app_of_isIso _ _
    have hfg : IsIso ((derivedStalk X y).map ((derivedStalkAdjunction X y).unit.app M) ≫
        (derivedStalkAdjunction X y).counit.app ((derivedStalk X y).obj M)) := by
      rw [(derivedStalkAdjunction X y).left_triangle_components M]
      exact IsIso.id _
    exact @Functor.map_isIso _ _ _ _ _ _ _ _ (@IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hc hfg)
  · have h1 : IsZero ((SheafOfModules.stalkFunctor X.ringCatSheaf y).obj
        ((DerivedCategory.homologyFunctor X.Modules i).obj M)) :=
      ((Functor.map_isZero (DerivedCategory.homologyFunctor _ i) (hM y hy)).of_iso
        (((SheafOfModules.stalkFunctor X.ringCatSheaf y).mapDerivedCategoryHomologyIso i).app
          M).symm)
    have h2 : IsZero ((SheafOfModules.stalkFunctor X.ringCatSheaf y).obj
        ((DerivedCategory.homologyFunctor X.Modules i).obj
          ((derivedSkyscraper X x).obj ((derivedStalk X x).obj M)))) :=
      (isZero_stalkFunctor_skyscraperObj_of_ne X x hx hy _).of_iso
        ((SheafOfModules.stalkFunctor X.ringCatSheaf y).mapIso
          (((SheafOfModules.skyscraperFunctor X.ringCatSheaf x).mapDerivedCategoryHomologyIso
            i).app _))
    exact ⟨h2.to_ _, h1.eq_of_src _ _, h2.eq_of_src _ _⟩

end Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

end
