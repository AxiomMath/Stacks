module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.EtaleModuleExtTwist
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedTwistEdge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInverseImageMonoidal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleExtForgetPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInverseImageMonoidalUnit

/-!
# The pullback action `φ^*` on `Hⁱ(Y, f^{-1} M)`, read on `Ext`

Let `f : Y ⟶ S` be a morphism of schemes, `φ : Y ⟶ Y` an endomorphism over `S` and `M` a sheaf of
`Λ`-modules on `S`. The endomorphism `φ^*` of `RΓ(S, Rf_*(f^{-1} M))`
(`Stacks.EtaleCohomology.selfMapCohomologyEndo`) is the derived twist endomorphism attached to
the twist `τ : f^{-1} M ⟶ φ_* f^{-1} M` (`Stacks.EtaleCohomology.selfMapTwist`). On cohomology,
under `Hⁱ(RΓ(S, Rf_*(f^{-1} M))) ≅ Hⁱ(Y, f^{-1} M) ≅ Ext^i(Λ_Y, f^{-1} M)`
(`Stacks.EtaleCohomology.selfMapCohomologySingleIsoExt`), it is

`b ↦ θ(b ∘ τ)`, `θ = Stacks.ExtCup.adjunctionExtMap φ^{-1} φ_*`,

that is, apply `φ^{-1}`, read out of `Λ_Y` through the lax unit of the monoidal inverse image,
and compose with the counit `φ^{-1} φ_* ⟶ 𝟭`. This computation enters Step 9 of the proof of
[Stacks, Tag 03UG].

The lax unit `Λ_Y ⟶ φ^{-1} Λ_Y` is the comparison of constant sheaves
(`Stacks.EtaleCohomology.etaleModuleInverseImageMonoidal_ε`), which turns `θ` into restriction of
`Ext` classes; on `Hⁱ(Y, U f^{-1} M)`, `φ^*` is the restriction map along `φ` followed by the
map induced by the adjoint of `τ`.

## Main results

* `Stacks.EtaleCohomology.selfMapComplexTwist_single`: the self-map twist of `M[0]` is the twist
  of `f^{-1} M`, placed in degree zero.
* `Stacks.EtaleCohomology.selfMapCohomologySingleIso_conj_selfMapCohomologyEndo`: `φ^*` on
  `Hⁱ(Y, f^{-1} M)` is `τ`, then the degreewise comparison for `φ_*` and `Γ(Y, -)`, then the map
  induced by `Γ(Y, φ_* -) ≅ Γ(Y, -)`.
* `Stacks.EtaleCohomology.selfMapCohomologySingleIsoExt_conj_selfMapCohomologyEndo`: `φ^*` on
  `Ext^i(Λ_Y, f^{-1} M)` is `b ↦ θ(b ∘ τ)`.
* `Stacks.EtaleCohomology.adjunctionExtMap_eq_etaleModuleExtRestriction`: `θ` is restriction of
  `Ext` classes followed by the counit.
* `Stacks.EtaleCohomology.extForgetSheafH_selfMapCohomologyEndo`: `φ^*` on `Hⁱ(Y, U f^{-1} M)` is
  the restriction map along `φ`, followed by the map induced by the adjoint of `τ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory
open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- The twist `t : I ⟶ I ⋙ P` applied degreewise to an object placed in degree zero, moved across
the identification of `I` of an object in degree zero with `I` of the object in degree zero, is
`t` at the object placed in degree zero. -/
private lemma homMk_twist_comp_map_singlePlusIso {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] (I : A ⥤ B) (P : B ⥤ B) [I.Additive] [P.Additive]
    (t : I ⟶ I ⋙ P) (M : A) :
    ObjectProperty.homMk ((NatTrans.mapHomologicalComplex t (ComplexShape.up ℤ)).app
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj M).obj) ≫
        P.mapCochainComplexPlus.map (mapCochainComplexPlusSinglePlusIso I M).hom =
      (mapCochainComplexPlusSinglePlusIso I M).hom ≫ Functor.singleTwist P (t.app M) := by
  refine ObjectProperty.hom_ext _ ?_
  ext n
  by_cases hn : n = 0
  · subst hn
    have hnat := t.naturality (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).hom
    simp only [Functor.comp_map] at hnat
    simp only [mapCochainComplexPlusSinglePlusIso, Functor.singleTwist,
      ObjectProperty.FullSubcategory.comp_hom, HomologicalComplex.comp_f]
    dsimp [Stacks.DerivedIndexing.mapSinglePlus, Stacks.DerivedIndexing.singlePlusFunctor]
    dsimp only [Functor.mapCochainComplexPlus, ObjectProperty.lift_map, Functor.comp_map]
    change ((NatTrans.mapHomologicalComplex t (ComplexShape.up ℤ)).app
          ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M)).f 0 ≫
        P.map (((HomologicalComplex.singleMapHomologicalComplex I (ComplexShape.up ℤ) 0).app
          M).hom.f 0) =
      ((HomologicalComplex.singleMapHomologicalComplex I (ComplexShape.up ℤ) 0).app M).hom.f 0 ≫
        ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).map (t.app M)).f 0 ≫
        ((HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℤ) 0).inv.app
          (I.obj M)).f 0
    rw [NatTrans.mapHomologicalComplex_app_f, Iso.app_hom,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp]
    rw [reassoc_of% hnat]
    simp
  · exact IsZero.eq_of_tgt (P.map_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (I.obj M) n hn)) _ _

section Twist

variable (Λ : Type) [CommRing Λ] {Y S : Scheme.{u}} (f : Y ⟶ S) (φ : Y ⟶ Y) (w : φ ≫ f = f)

/-- **The self-map twist of a sheaf placed in degree zero is the twist of its inverse image,
placed in degree zero.** -/
theorem selfMapComplexTwist_single (M : EtaleModules.{u, 0} Λ S) :
    selfMapComplexTwist.{u, 0} Λ f φ w ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj M) ≫
        (etaleModuleDirectImage.{u, 0} Λ φ).mapCochainComplexPlus.map
          (mapCochainComplexPlusSinglePlusIso (etaleModuleInverseImage.{u, 0} Λ f) M).hom =
      (mapCochainComplexPlusSinglePlusIso (etaleModuleInverseImage.{u, 0} Λ f) M).hom ≫
        Functor.singleTwist (etaleModuleDirectImage.{u, 0} Λ φ)
          ((selfMapTwist.{u, 0} Λ f φ w).app M) :=
  homMk_twist_comp_map_singlePlusIso _ _ _ M

/-- **`φ^*` on `Hⁱ(Y, f^{-1} M)`.** Under `Hⁱ(RΓ(S, Rf_*(f^{-1} M))) ≅ Hⁱ(Y, f^{-1} M)`, the
pullback action `φ^*` of an endomorphism `φ` of `Y` over `S` is the twist
`τ : f^{-1} M ⟶ φ_* f^{-1} M` on `Hⁱ(Y, -)`, followed by the degreewise comparison of
[Stacks, Tag 015M] for `φ_*` and `Γ(Y, -)`, and by the map induced by `Γ(Y, φ_* -) ≅ Γ(Y, -)`. -/
theorem selfMapCohomologySingleIso_conj_selfMapCohomologyEndo (M : EtaleModules.{u, 0} Λ S)
    (i : ℤ) :
    (selfMapCohomologySingleIso.{u, 0} Λ f M i).inv ≫
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
          (selfMapCohomologyEndo.{u, 0} Λ f φ w
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj M)) ≫
        (selfMapCohomologySingleIso.{u, 0} Λ f M i).hom =
      ((etaleModuleGlobalSections.{u, 0} Λ Y).rightDerivedPlus i).map
          ((selfMapTwist.{u, 0} Λ f φ w).app M) ≫
        (Stacks.DerivedIndexing.rightDerivedPlusEdge (etaleModuleDirectImage.{u, 0} Λ φ)
          (etaleModuleGlobalSections.{u, 0} Λ Y) i).app
          ((etaleModuleInverseImage.{u, 0} Λ f).obj M) ≫
        (Stacks.DerivedIndexing.rightDerivedPlusNatTrans
          (Functor.twistEdgeIso (etaleModuleDirectImage.{u, 0} Λ φ)
            (etaleModuleDirectImage.{u, 0} Λ f) (etaleModuleGlobalSections.{u, 0} Λ S)
            (etaleModuleGlobalSections.{u, 0} Λ Y) (selfMapDirectImageComp.{u, 0} Λ f φ w)
            (etaleModuleGlobalSectionsDirectImageIso f Λ)).hom i).app
          ((etaleModuleInverseImage.{u, 0} Λ f).obj M) := by
  have hL1 := Functor.homologyMap_derivedTwistEndo_single (etaleModuleDirectImage.{u, 0} Λ φ)
    (etaleModuleDirectImage.{u, 0} Λ f) (etaleModuleGlobalSections.{u, 0} Λ S)
    (etaleModuleGlobalSections.{u, 0} Λ Y) (selfMapDirectImageComp.{u, 0} Λ f φ w)
    (etaleModuleGlobalSectionsDirectImageIso f Λ) ((etaleModuleInverseImage.{u, 0} Λ f).obj M)
    ((selfMapTwist.{u, 0} Λ f φ w).app M) i
  have hnat := Functor.derivedTwistEndo_naturality (etaleModuleDirectImage.{u, 0} Λ φ)
    (etaleModuleDirectImage.{u, 0} Λ f) (etaleModuleGlobalSections.{u, 0} Λ S)
    (selfMapDirectImageComp.{u, 0} Λ f φ w)
    (mapCochainComplexPlusSinglePlusIso (etaleModuleInverseImage.{u, 0} Λ f) M).hom _ _
    (congrArg DerivedCategory.Plus.Q.map (selfMapComplexTwist_single Λ f φ w M))
  have aux : ∀ {A B : Type _} [Category A] [Category B] (G : A ⥤ B) {W X Y Z : A}
      {c : W ⟶ X} {r' : X ⟶ Y} {d : Y ⟶ Y} {r : Y ⟶ X} {d' : X ⟶ X} {ci : X ⟶ Z}
      (_ : d ≫ r = r ≫ d') (_ : r' ≫ r = 𝟙 X),
      G.map (c ≫ r') ≫ G.map d ≫ G.map (r ≫ ci) = G.map (c ≫ d' ≫ ci) := by
    intro A B _ _ G W X Y Z c r' d r d' ci hnat hri
    rw [← G.map_comp, ← G.map_comp]
    congr 1
    simp only [Category.assoc]
    rw [reassoc_of% hnat, reassoc_of% hri]
  exact (aux (DerivedCategory.Plus.homologyFunctor _ i) hnat (Iso.inv_hom_id _)).trans hL1

end Twist

section ExtTwist

attribute [local instance] Sheaf.monoidalCategory etaleModuleInverseImageSheafPullbackMonoidal
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [CommRing Λ] {Y S : Scheme.{u}} (f : Y ⟶ S) (φ : Y ⟶ Y) (w : φ ≫ f = f)
  [(Y.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal]
  [PreservesFiniteColimits (etaleModuleDirectImage.{u, 0} Λ φ)]

/-- **`φ^*` on `Ext^i(Λ_Y, f^{-1} M)` is `b ↦ θ(b ∘ τ)`**, for `θ` the map
`Ext^i(Λ_Y, φ_* N) ⟶ Ext^i(Λ_Y, N)`, `b ↦ ε_N ∘ φ^{-1}(b)` of the adjunction `φ^{-1} ⊣ φ_*`
(`Stacks.ExtCup.adjunctionExtMap`) and `τ : f^{-1} M ⟶ φ_* f^{-1} M` the self-map twist. -/
theorem selfMapCohomologySingleIsoExt_conj_selfMapCohomologyEndo
    (M : EtaleModules.{u, 0} Λ S) (i : ℕ)
    (b : Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ Y.smallEtaleTopology)
      ((etaleModuleInverseImage.{u, 0} Λ f).obj M) i) :
    ((selfMapCohomologySingleIsoExt Λ f M i).hom).hom
        (((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
            (selfMapCohomologyEndo.{u, 0} Λ f φ w
              ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj M)))).hom
          (((selfMapCohomologySingleIsoExt Λ f M i).inv).hom b)) =
      Stacks.ExtCup.adjunctionExtMap (etaleModuleInverseImage.{u, 0} Λ φ)
        (etaleModuleDirectImage.{u, 0} Λ φ) (etaleModuleInverseImageAdj.{u, 0} Λ φ)
        ((etaleModuleInverseImage.{u, 0} Λ f).obj M)
        (b.comp (Ext.mk₀ ((selfMapTwist.{u, 0} Λ f φ w).app M)) (add_zero i)) := by
  have key := etaleModuleRightDerivedPlusIsoExt_conj_edge Λ Y
    (etaleModuleInverseImage.{u, 0} Λ φ) (etaleModuleDirectImage.{u, 0} Λ φ)
    (etaleModuleInverseImageAdj.{u, 0} Λ φ) _
    (twistEdgeIso_whiskerRight_comp_corepresentation Λ φ f w.symm)
    ((etaleModuleInverseImage.{u, 0} Λ f).obj M)
    ((selfMapTwist.{u, 0} Λ f φ w).app M) i b
  rw [← selfMapCohomologySingleIso_conj_selfMapCohomologyEndo] at key
  refine Eq.trans ?_ key
  simp only [selfMapCohomologySingleIsoExt, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
  rfl

omit [PreservesFiniteColimits (etaleModuleDirectImage.{u, 0} Λ φ)] in
/-- **The `Ext` map of the adjunction `φ^{-1} ⊣ φ_*` is restriction followed by the counit**: the
lax unit of the monoidal inverse image is the comparison of constant sheaves. -/
theorem adjunctionExtMap_eq_etaleModuleExtRestriction
    (N : EtaleModules.{u, 0} Λ Y) {i : ℕ}
    (b : Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ Y.smallEtaleTopology)
      ((etaleModuleDirectImage.{u, 0} Λ φ).obj N) i) :
    Stacks.ExtCup.adjunctionExtMap (etaleModuleInverseImage.{u, 0} Λ φ)
        (etaleModuleDirectImage.{u, 0} Λ φ) (etaleModuleInverseImageAdj.{u, 0} Λ φ) N b =
      (etaleModuleExtRestriction Λ φ _ i b).comp
        (Ext.mk₀ ((etaleModuleInverseImageAdj.{u, 0} Λ φ).counit.app N)) (add_zero i) := by
  change ((Ext.mk₀ (Functor.LaxMonoidal.ε (etaleModuleInverseImage.{u, 0} Λ φ))).comp
    (b.mapExactFunctor (etaleModuleInverseImage.{u, 0} Λ φ)) (zero_add i)).comp _ _ = _
  rw [etaleModuleExtRestriction_apply, etaleModuleInverseImageMonoidal_ε]
  rfl

variable [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **`φ^*` on `Hⁱ(Y, U f^{-1} M)` is the restriction map along `φ`**: under
`Hⁱ(RΓ(S, Rf_*(f^{-1} M))) ≅ Ext^i(Λ_Y, f^{-1} M) ≃+ Hⁱ(Y, U f^{-1} M)`, the pullback action
`φ^*` is `etaleCohomologyRestrictionMap φ` followed by the isomorphism
`φ^{-1} U f^{-1} M ≅ U φ^{-1} f^{-1} M ⟶ U f^{-1} M`, the second map being the adjoint
`φ^{-1}(τ) ≫ ε` of the self-map twist (the canonical `φ^{-1} f^{-1} M ≅ f^{-1} M`). -/
theorem extForgetSheafH_selfMapCohomologyEndo
    (M : EtaleModules.{u, 0} Λ S) (i : ℕ)
    (b : Ext.{u + 1} (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ Y.smallEtaleTopology)
      ((etaleModuleInverseImage.{u, 0} Λ f).obj M) i) :
    extForgetSheafH Λ Y _ i (((selfMapCohomologySingleIsoExt Λ f M i).hom).hom
        (((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
            (selfMapCohomologyEndo.{u, 0} Λ f φ w
              ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj M)))).hom
          (((selfMapCohomologySingleIsoExt Λ f M i).inv).hom b))) =
      (etaleCohomologyRestrictionMap.{u, 0, u + 1} φ
          ((etaleModuleUnderlyingAbelian Y Λ).obj ((etaleModuleInverseImage.{u, 0} Λ f).obj M)) i
          (extForgetSheafH Λ Y _ i b)).comp
        (Ext.mk₀ ((etaleModuleUnderlyingAbelianInverseImageIso Λ φ).hom.app _ ≫
          (etaleModuleUnderlyingAbelian Y Λ).map
            ((etaleModuleInverseImage.{u, 0} Λ φ).map ((selfMapTwist.{u, 0} Λ f φ w).app M) ≫
              (etaleModuleInverseImageAdj.{u, 0} Λ φ).counit.app _))) (add_zero i) := by
  rw [selfMapCohomologySingleIsoExt_conj_selfMapCohomologyEndo Λ f φ w M i b,
    adjunctionExtMap_eq_etaleModuleExtRestriction Λ φ, etaleModuleExtRestriction_comp_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, extForgetSheafH_comp_mk₀,
    extForgetSheafH_etaleModuleExtRestriction,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]

end ExtTwist

end Stacks.EtaleCohomology

end
