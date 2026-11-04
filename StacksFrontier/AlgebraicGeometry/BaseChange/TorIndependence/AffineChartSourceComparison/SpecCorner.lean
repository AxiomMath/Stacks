module

public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartSourceComparison.SourceBridge
public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartSourceComparison.MergeCounit

/-!
# The reconciliation at the `Spec 𝒪_X(U)` corner

`AlgebraicGeometry.BaseChangeChart.localTailMorphism_eq`,
`AlgebraicGeometry.BaseChangeChart.specCornerComm` and the unconditional
`AlgebraicGeometry.BaseChangeChart.cohomologyComparisonMap_localRingsSourceMap`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars
  totalDerivedExtensionScalarsComp totalDerivedExtensionScalarsComp_comparison
  derivedExtensionScalarsAdjunction)
open scoped TensorProduct ChangeOfRings

universe u w v₁ v₂ v₃ u₁ u₂ u₃

namespace AlgebraicGeometry

section Shape

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A five-fold composite under a functor at the end of a five-fold composite, expanded. -/
private theorem comp4_map_comp5_expand (F : C ⥤ D) {W₀ W₁ W₂ W₃ : D} {X₀ X₁ X₂ X₃ X₄ X₅ : C}
    (p₁ : W₀ ⟶ W₁) (p₂ : W₁ ⟶ W₂) (p₃ : W₂ ⟶ W₃) (p₄ : W₃ ⟶ F.obj X₀)
    (m₁ : X₀ ⟶ X₁) (m₂ : X₁ ⟶ X₂) (m₃ : X₂ ⟶ X₃) (m₄ : X₃ ⟶ X₄) (m₅ : X₄ ⟶ X₅) :
    p₁ ≫ p₂ ≫ p₃ ≫ p₄ ≫ F.map (m₁ ≫ m₂ ≫ m₃ ≫ m₄ ≫ m₅) =
      p₁ ≫ p₂ ≫ p₃ ≫ p₄ ≫ F.map m₁ ≫ F.map m₂ ≫ F.map m₃ ≫ F.map m₄ ≫ F.map m₅ := by
  simp only [CategoryTheory.Functor.map_comp]

/-- An eight-fold composite under a functor, expanded, with its last factor and the tail
replaced. -/
private theorem map_comp6_comp2_subst (F : C ⥤ D) {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ : C} {W Z : D}
    (r₁ : X₀ ⟶ X₁) (r₂ : X₁ ⟶ X₂) (r₃ : X₂ ⟶ X₃) (r₄ : X₃ ⟶ X₄) (r₅ : X₄ ⟶ X₅)
    (r₆ : X₅ ⟶ X₆) (r₇ : X₆ ⟶ X₇) {r₈ : X₇ ⟶ X₈} {t : F.obj X₈ ⟶ W}
    {u : F.obj X₇ ⟶ Z} {v : Z ⟶ W} (h : F.map r₈ ≫ t = u ≫ v) :
    F.map ((r₁ ≫ r₂ ≫ r₃ ≫ r₄ ≫ r₅ ≫ r₆) ≫ r₇ ≫ r₈) ≫ t =
      F.map r₁ ≫ F.map r₂ ≫ F.map r₃ ≫ F.map r₄ ≫ F.map r₅ ≫
        F.map r₆ ≫ F.map r₇ ≫ u ≫ v := by
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [h]

/-- **A morphism carried across a transport of the functor it is applied to.** Given an
isomorphism `τ : F₁ ≅ F₂`, a five-fold head whose composite with `τ` is a three-fold composite
`q₁ ≫ q₂ ≫ q₃` and a three-fold tail which is `τ` followed by `s`, the two readings of `m`
agree. -/
private theorem comp5_map_comp3_transport3 (F₁ F₂ : C ⥤ D) (τ : F₁ ≅ F₂)
    {W₀ W₁ W₂ W₃ W₄ V₁ V₂ Z₀ Z₁ Z₂ : D} {Xa Ya : C}
    (p₁ : W₀ ⟶ W₁) (p₂ : W₁ ⟶ W₂) (p₃ : W₂ ⟶ W₃) (p₄ : W₃ ⟶ W₄) (p₅ : W₄ ⟶ F₁.obj Xa)
    (m : Xa ⟶ Ya) (t₁ : F₁.obj Ya ⟶ Z₀) (t₂ : Z₀ ⟶ Z₁) (t₃ : Z₁ ⟶ Z₂)
    (q₁ : W₀ ⟶ V₁) (q₂ : V₁ ⟶ V₂) (q₃ : V₂ ⟶ F₂.obj Xa) (s : F₂.obj Ya ⟶ Z₂)
    (hu : p₁ ≫ p₂ ≫ p₃ ≫ p₄ ≫ p₅ ≫ τ.hom.app Xa = q₁ ≫ q₂ ≫ q₃)
    (hv : t₁ ≫ t₂ ≫ t₃ = τ.hom.app Ya ≫ s) :
    p₁ ≫ p₂ ≫ p₃ ≫ p₄ ≫ p₅ ≫ F₁.map m ≫ t₁ ≫ t₂ ≫ t₃ =
      q₁ ≫ q₂ ≫ q₃ ≫ F₂.map m ≫ s := by
  rw [hv, τ.hom.naturality_assoc]
  simpa only [Category.assoc] using congrArg (· ≫ F₂.map m ≫ s) hu

/-- A morphism under a functor, split in two. -/
private theorem map_eq_comp (F : C ⥤ D) {X₀ X₁ X₂ : C} {a : X₀ ⟶ X₂} {x : X₀ ⟶ X₁}
    {z : X₁ ⟶ X₂} (h : a = x ≫ z) : F.map a = F.map x ≫ F.map z := by
  rw [h, CategoryTheory.Functor.map_comp]

/-- Two factors under a functor, replaced. -/
private theorem map_comp2_subst (F : C ⥤ D) {X₀ X₁ X₂ Y₁ : C} {a : X₀ ⟶ X₁} {bb : X₁ ⟶ X₂}
    {a' : X₀ ⟶ Y₁} {b' : Y₁ ⟶ X₂} (h : a ≫ bb = a' ≫ b') :
    F.map a ≫ F.map bb = F.map a' ≫ F.map b' := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, h]

/-- A three-fold composite under a functor, expanded. -/
private theorem comp_map_comp3_expand (F : C ⥤ D) {W₀ W₁ : D} {X₀ X₁ X₂ X₃ : C}
    (p : W₀ ⟶ F.obj X₀) (x : X₀ ⟶ X₁) (y : X₁ ⟶ X₂) (z : X₂ ⟶ X₃) (q : F.obj X₃ ⟶ W₁) :
    p ≫ F.map (x ≫ y ≫ z) ≫ q = p ≫ F.map x ≫ F.map y ≫ F.map z ≫ q := by
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]

end Shape

namespace BaseChangeChart

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **The chart's tail morphism, with no unit, counit or localization passage.** The composite
of the inverse composition isomorphism, the extension of
`AlgebraicGeometry.BaseChangeChart.germDerivedStalkSectionsIso`, the inverse passage
`RingTheory.TorIndependence.restrictScalarsDerivedExtendCompIso`, the merge of the restrictions
and the counit is a composition isomorphism read backwards, the generic
`AlgebraicGeometry.derivedStalkAffineSectionsIso` extended, a transport, a composition
isomorphism and `AlgebraicGeometry.totalDerivedExtensionScalarsIdOf` read backwards. -/
public theorem localTailMorphism_eq (ch : BaseChangeChart f g f' g') (y : Spec ch.A')
    (K : DerivedCategory X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent) :
    letI := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
    letI := (ch.toStalkA y).toAlgebra
    haveI : IsLocalization (ch.primeComplA y)
        (ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y))) :=
      isLocalization_atPrime_specGermRingHom ch.A (Spec.map ch.c y)
    (totalDerivedExtensionScalarsComp.{u, u} (specGermRingHom ch.A (Spec.map ch.c y))
            (ch.stalkCompAIso y).inv.hom).inv.app ((affineDerivedSections ch.incU).obj K) ≫
        (totalDerivedExtensionScalars.{u, u, u} (ch.stalkCompAIso y).inv.hom).functor.map
            (ch.germDerivedStalkSectionsIso y K hK).hom ≫
          (RingTheory.TorIndependence.restrictScalarsDerivedExtendCompIso.{u, u}
                (ch.primeComplA y) (ch.stalkCompAIso y).inv.hom).inv.app
              ((ModuleCat.restrictScalars.{u}
                  (ch.stalkCompAIso y).inv.hom).mapDerivedCategory.obj
                ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) ≫
            (totalDerivedExtensionScalars.{u, u, u} (ch.toStalkA y)).functor.map
                ((RingTheory.TorIndependence.mapDerivedCategoryCompNatIso
                  (ModuleCat.restrictScalars.{u} (ch.stalkCompAIso y).inv.hom)
                  (ModuleCat.restrictScalars.{u} (specGermRingHom ch.A (Spec.map ch.c y)))
                  (ModuleCat.restrictScalars.{u} (ch.toStalkA y))
                  (ModuleCat.restrictScalarsComp'.{u}
                      (specGermRingHom ch.A (Spec.map ch.c y))
                    (ch.stalkCompAIso y).inv.hom (ch.toStalkA y) rfl).symm).hom.app
                  ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) ≫
              (RingTheory.TorIndependence.derivedExtendRestrictAdjunction
                    (A := ToType ch.A)
                    (A₂ := ToType (X.presheaf.stalk (g' (ch.incU' y))))).counit.app
                ((derivedStalkFunctor (g' (ch.incU' y))).obj K) =
      (totalDerivedExtensionScalarsComp.{u, u} (specGermRingHom ch.A (Spec.map ch.c y))
            (ch.stalkCompAIso y).inv.hom).inv.app ((affineDerivedSections ch.incU).obj K) ≫
        (totalDerivedExtensionScalars.{u, u, u} (ch.stalkCompAIso y).inv.hom).functor.map
            (derivedStalkAffineSectionsIso ch.incU (Spec.map ch.c y) K hK).hom ≫
          (totalDerivedExtensionScalars.{u, u, u} (ch.stalkCompAIso y).inv.hom).functor.map
              (eqToHom (derivedStalkAffineSections_extend_obj_eq ch.incU (Spec.map ch.c y)
                (g' (ch.incU' y)) (ch.apply_g'_incU' y) K)) ≫
            (totalDerivedExtensionScalarsComp.{u, u}
                  ((X.presheaf.stalkCongr (.of_eq (ch.apply_g'_incU' y))).hom ≫
                    ch.incU.stalkMap (Spec.map ch.c y)).hom
                  (ch.stalkCompAIso y).inv.hom).hom.app
                ((derivedStalkFunctor (g' (ch.incU' y))).obj K) ≫
              (totalDerivedExtensionScalarsIdOf.{u, u}
                  ((ch.stalkCompAIso y).inv.hom.comp
                    ((X.presheaf.stalkCongr (.of_eq (ch.apply_g'_incU' y))).hom ≫
                      ch.incU.stalkMap (Spec.map ch.c y)).hom)
                  (RingHom.ext
                    (commRingCatIso_inv_hom_apply (ch.stalkCompAIso y)))).inv.app
                ((derivedStalkFunctor (g' (ch.incU' y))).obj K) := by
  let := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
  let := (ch.toStalkA y).toAlgebra
  have : IsLocalization (ch.primeComplA y)
      (ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y))) :=
    isLocalization_atPrime_specGermRingHom ch.A (Spec.map ch.c y)
  have := ch.isOpenImmersion_incU
  have hg : (ch.germDerivedStalkSectionsIso y K hK).hom =
      (derivedStalkAffineSectionsIso ch.incU (Spec.map ch.c y) K hK).hom ≫
        eqToHom (derivedStalkAffineSections_extend_obj_eq ch.incU (Spec.map ch.c y)
            (g' (ch.incU' y)) (ch.apply_g'_incU' y) K) ≫
          (totalDerivedExtensionScalarsIsoRestrict
              ((X.presheaf.stalkCongr (.of_eq (ch.apply_g'_incU' y))).hom ≫
                ch.incU.stalkMap (Spec.map ch.c y)).hom (ch.stalkCompAIso y).inv.hom
              (commRingCatIso_inv_hom_apply (ch.stalkCompAIso y))
              (commRingCatIso_hom_inv_apply (ch.stalkCompAIso y))).hom.app
            ((derivedStalkFunctor (g' (ch.incU' y))).obj K) :=
    congrArg Iso.hom (derivedStalkAffineSectionsCongrIso_eq ch.incU (Spec.map ch.c y)
      (g' (ch.incU' y)) (ch.apply_g'_incU' y) K hK (ch.stalkCompAIso y).inv.hom
      (commRingCatIso_inv_hom_apply (ch.stalkCompAIso y))
      (commRingCatIso_hom_inv_apply (ch.stalkCompAIso y)))
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (RingTheory.TorIndependence.inv_comp_map_merge_comp_counit (ch.primeComplA y)
      (ch.stalkCompAIso y).inv.hom _ rfl
      ((derivedStalkFunctor (g' (ch.incU' y))).obj K)))) ?_
  refine Eq.trans (whisker_eq _ (congrArg (· ≫ _) (congrArg
    (totalDerivedExtensionScalars.{u, u, u} (ch.stalkCompAIso y).inv.hom).functor.map hg))) ?_
  refine Eq.trans (comp_map_comp3_expand
    (totalDerivedExtensionScalars.{u, u, u} (ch.stalkCompAIso y).inv.hom).functor _ _ _ _ _) ?_
  exact whisker_eq _ (whisker_eq _ (whisker_eq _
    (AlgebraicGeometry.map_totalDerivedExtensionScalarsIsoRestrict_hom_comp_counit_eq
      ((X.presheaf.stalkCongr (.of_eq (ch.apply_g'_incU' y))).hom ≫
        ch.incU.stalkMap (Spec.map ch.c y)).hom (ch.stalkCompAIso y).inv.hom
      (commRingCatIso_inv_hom_apply (ch.stalkCompAIso y))
      (commRingCatIso_hom_inv_apply (ch.stalkCompAIso y))
      ((derivedStalkFunctor (g' (ch.incU' y))).obj K))))

/-- The chart's comparison at `U` read backwards and then along `g'` is the stalk map of
`Spec ch.c` read along the inverse `ε'` of the germ comparison of `U'`. -/
public theorem stalkMap_comp_stalkCompAIso_inv (ch : BaseChangeChart f g f' g') (y : Spec ch.A')
    (ε' : (Spec ch.A').presheaf.stalk y →+* X'.presheaf.stalk (ch.incU' y))
    (h₁ : ∀ x, ε' ((ch.incU'.stalkMap y).hom x) = x)
    (h₂ : ∀ z, (ch.incU'.stalkMap y).hom (ε' z) = z) :
    (g'.stalkMap (ch.incU' y)).hom.comp (ch.stalkCompAIso y).inv.hom =
      ε'.comp ((Spec.map ch.c).stalkMap y).hom := by
  have hinj : Function.Injective
      (fun z : X'.presheaf.stalk (ch.incU' y) => (ch.incU'.stalkMap y).hom z) :=
    fun z₁ z₂ h => (h₁ z₁).symm.trans ((congrArg ε' h).trans (h₁ z₂))
  refine RingHom.ext fun x => hinj ?_
  have hsq := DFunLike.congr_fun (ch.stalkCompA_stalkMap_g' y)
    ((ch.stalkCompAIso y).inv.hom x)
  simp only [RingHom.comp_apply] at hsq
  refine Eq.trans hsq ?_
  refine Eq.trans (congrArg ((Spec.map ch.c).stalkMap y).hom
    (commRingCatIso_hom_inv_apply (ch.stalkCompAIso y) x)) ?_
  exact (h₂ (((Spec.map ch.c).stalkMap y).hom x)).symm

/-- The transport the chase is read across. -/
private abbrev chaseTransport (ch : BaseChangeChart f g f' g') (y : Spec ch.A')
    (ε' : (Spec ch.A').presheaf.stalk y →+* X'.presheaf.stalk (ch.incU' y))
    (h₁ : ∀ x, ε' ((ch.incU'.stalkMap y).hom x) = x)
    (h₂ : ∀ z, (ch.incU'.stalkMap y).hom (ε' z) = z) :
    (totalDerivedExtensionScalars.{u, u, u} (ch.stalkCompAIso y).inv.hom).functor ⋙
        (totalDerivedExtensionScalars.{u, u, u} (g'.stalkMap (ch.incU' y)).hom).functor ≅
      (totalDerivedExtensionScalars.{u, u, u} ((Spec.map ch.c).stalkMap y).hom).functor ⋙
        (totalDerivedExtensionScalars.{u, u, u} ε').functor :=
  totalDerivedExtensionScalarsComp.{u, u} (ch.stalkCompAIso y).inv.hom
      (g'.stalkMap (ch.incU' y)).hom ≪≫
    RingTheory.TorIndependence.totalDerivedExtensionScalarsCongr.{u, u}
      (ch.stalkMap_comp_stalkCompAIso_inv y ε' h₁ h₂) ≪≫
    (totalDerivedExtensionScalarsComp.{u, u} ((Spec.map ch.c).stalkMap y).hom ε').symm

/-- **The head of the `Spec 𝒪_X(U)` corner's chase.** The five factors of the chart's route that
precede the germ localization of the derived sections, read across the transport
`AlgebraicGeometry.BaseChangeChart.chaseTransport`, are the three factors of the route through
`Spec 𝒪_X(U)` that precede it. -/
private theorem specCornerHead (ch : BaseChangeChart f g f' g') (y : Spec ch.A')
    (K : DerivedCategory X.Modules)
    (ε' : (Spec ch.A').presheaf.stalk y →+* X'.presheaf.stalk (ch.incU' y))
    (h₁ : ∀ x, ε' ((ch.incU'.stalkMap y).hom x) = x)
    (h₂ : ∀ z, (ch.incU'.stalkMap y).hom (ε' z) = z) :
    (totalDerivedExtensionScalarsComp.{u, u} (specGermRingHom ch.A' y) ε').hom.app
          ((totalDerivedExtensionScalars.{u, u, u} ch.c.hom).functor.obj
            ((affineDerivedSections ch.incU).obj K)) ≫
        (totalDerivedExtensionScalarsComp.{u, u} ch.c.hom (ch.toStalkA' y ε')).hom.app
            ((affineDerivedSections ch.incU).obj K) ≫
          (RingTheory.TorIndependence.totalDerivedExtensionScalarsCongr.{u, u}
                (ch.toStalkA'_c y ε' h₁ h₂)).inv.app
              ((affineDerivedSections ch.incU).obj K) ≫
            (totalDerivedExtensionScalarsComp.{u, u} (ch.toStalkA y)
                  (g'.stalkMap (ch.incU' y)).hom).inv.app
                ((affineDerivedSections ch.incU).obj K) ≫
              (totalDerivedExtensionScalars.{u, u, u}
                    (g'.stalkMap (ch.incU' y)).hom).functor.map
                  ((totalDerivedExtensionScalarsComp.{u, u}
                      (specGermRingHom ch.A (Spec.map ch.c y))
                      (ch.stalkCompAIso y).inv.hom).inv.app
                    ((affineDerivedSections ch.incU).obj K)) ≫
                (totalDerivedExtensionScalarsComp.{u, u} (ch.stalkCompAIso y).inv.hom
                      (g'.stalkMap (ch.incU' y)).hom).hom.app
                    ((totalDerivedExtensionScalars.{u, u, u}
                        (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
                      ((affineDerivedSections ch.incU).obj K)) ≫
                  (RingTheory.TorIndependence.totalDerivedExtensionScalarsCongr.{u, u}
                        (ch.stalkMap_comp_stalkCompAIso_inv y ε' h₁ h₂)).hom.app
                      ((totalDerivedExtensionScalars.{u, u, u}
                          (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
                        ((affineDerivedSections ch.incU).obj K)) ≫
                    (totalDerivedExtensionScalarsComp.{u, u}
                          ((Spec.map ch.c).stalkMap y).hom ε').inv.app
                        ((totalDerivedExtensionScalars.{u, u, u}
                            (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
                          ((affineDerivedSections ch.incU).obj K)) =
      (totalDerivedExtensionScalars.{u, u, u} ε').functor.map
          ((StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIsoGeneral ch.c.hom
              (specGermRingHom ch.A' y)).hom.app ((affineDerivedSections ch.incU).obj K)) ≫
        (totalDerivedExtensionScalars.{u, u, u} ε').functor.map
            (eqToHom (congrArg
              (fun ψ => (totalDerivedExtensionScalars.{u, u, u} ψ).functor.obj
                ((affineDerivedSections ch.incU).obj K))
              (specGermRingHom_stalkMap ch.c y).symm)) ≫
          (totalDerivedExtensionScalars.{u, u, u} ε').functor.map
            ((StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIsoGeneral
                  (specGermRingHom ch.A (Spec.map ch.c y))
                  ((Spec.map ch.c).stalkMap y).hom).inv.app
              ((affineDerivedSections ch.incU).obj K)) := by
  have hbσ := ch.stalkMap_comp_stalkCompAIso_inv y ε' h₁ h₂
  have hD1 : (StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIsoGeneral ch.c.hom
        (specGermRingHom ch.A' y)).hom.app ((affineDerivedSections ch.incU).obj K) =
      (totalDerivedExtensionScalarsComp.{u, u} ch.c.hom
          (specGermRingHom ch.A' y)).hom.app ((affineDerivedSections ch.incU).obj K) := by
    rw [StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso_eq_totalComp]
  have hD2 : (StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIsoGeneral
        (specGermRingHom ch.A (Spec.map ch.c y))
        ((Spec.map ch.c).stalkMap y).hom).inv.app ((affineDerivedSections ch.incU).obj K) =
      (totalDerivedExtensionScalarsComp.{u, u} (specGermRingHom ch.A (Spec.map ch.c y))
          ((Spec.map ch.c).stalkMap y).hom).inv.app
        ((affineDerivedSections ch.incU).obj K) := by
    rw [StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso_eq_totalComp]
  rw [hD1, hD2]
  refine Eq.trans (whisker_eq _ (whisker_eq _ (whisker_eq _
    (RingTheory.TorIndependence.comp3_reassoc_one
      (RingTheory.TorIndependence.comp_inv_comp_map_comp_inv_comp_comp_hom
        (specGermRingHom ch.A (Spec.map ch.c y)) (ch.stalkCompAIso y).inv.hom
        (g'.stalkMap (ch.incU' y)).hom ((affineDerivedSections ch.incU).obj K)) _)))) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ (whisker_eq _
    (RingTheory.TorIndependence.comp2_reassoc_two
      (RingTheory.TorIndependence.comp_inv_comp_congr_hom hbσ
        (specGermRingHom ch.A (Spec.map ch.c y))
        ((affineDerivedSections ch.incU).obj K)) _)))) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _
    (RingTheory.TorIndependence.comp_inv_comp_comp_inv
      (specGermRingHom ch.A (Spec.map ch.c y)) ((Spec.map ch.c).stalkMap y).hom ε'
      ((affineDerivedSections ch.incU).obj K)))))) ?_
  refine RingTheory.TorIndependence.comp5_reassoc_two ?_ _
  have hP3 := RingTheory.TorIndependence.congr_inv_app_comp_congr_hom_app
    (ch.toStalkA'_c y ε' h₁ h₂)
    (congrArg (fun m : ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)) →+*
        ToType (X'.presheaf.stalk (ch.incU' y)) =>
      m.comp (specGermRingHom ch.A (Spec.map ch.c y))) hbσ)
    ((affineDerivedSections ch.incU).obj K)
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (RingTheory.TorIndependence.comp2_reassoc_one hP3 _))) ?_
  have hH4 := RingTheory.TorIndependence.map_eqToHom_comp_comp_hom
    (specGermRingHom_stalkMap ch.c y).symm ε' ((affineDerivedSections ch.incU).obj K)
  have hassoc := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp_assoc
    ch.c.hom (specGermRingHom ch.A' y) ε' ((affineDerivedSections ch.incU).obj K)
  have hRHS := Eq.trans (whisker_eq _ hH4)
    (RingTheory.TorIndependence.comp2_reassoc_two hassoc _)
  refine Eq.trans (RingTheory.TorIndependence.comp3_reassoc_left _ _ _ _)
    (RingTheory.TorIndependence.eq_comp_inv_of _ _
      ((totalDerivedExtensionScalarsComp.{u, u}
        (((Spec.map ch.c).stalkMap y).hom.comp
          (specGermRingHom ch.A (Spec.map ch.c y))) ε').hom.app
        ((affineDerivedSections ch.incU).obj K))
      ((totalDerivedExtensionScalarsComp.{u, u}
        (((Spec.map ch.c).stalkMap y).hom.comp
          (specGermRingHom ch.A (Spec.map ch.c y))) ε').inv.app
        ((affineDerivedSections ch.incU).obj K))
      (Iso.hom_inv_id_app _ _)
      (Eq.trans (Category.assoc _ _ _) hRHS)).symm

/-- **The tail of the `Spec 𝒪_X(U)` corner's chase.** The three factors of the chart's route
that follow the germ localization of the derived sections are the transport
`AlgebraicGeometry.BaseChangeChart.chaseTransport` followed by the six factors of the route
through `Spec 𝒪_X(U)` that follow it. -/
private theorem specCornerTail (ch : BaseChangeChart f g f' g') (y : Spec ch.A')
    (K : DerivedCategory X.Modules)
    (ε' : (Spec ch.A').presheaf.stalk y →+* X'.presheaf.stalk (ch.incU' y))
    (h₁ : ∀ x, ε' ((ch.incU'.stalkMap y).hom x) = x)
    (h₂ : ∀ z, (ch.incU'.stalkMap y).hom (ε' z) = z) :
    (totalDerivedExtensionScalars.{u, u, u} (g'.stalkMap (ch.incU' y)).hom).functor.map
          ((totalDerivedExtensionScalars.{u, u, u} (ch.stalkCompAIso y).inv.hom).functor.map
            (eqToHom (derivedStalkAffineSections_extend_obj_eq ch.incU (Spec.map ch.c y)
              (g' (ch.incU' y)) (ch.apply_g'_incU' y) K))) ≫
        (totalDerivedExtensionScalars.{u, u, u} (g'.stalkMap (ch.incU' y)).hom).functor.map
            ((totalDerivedExtensionScalarsComp.{u, u}
                  ((X.presheaf.stalkCongr (.of_eq (ch.apply_g'_incU' y))).hom ≫
                    ch.incU.stalkMap (Spec.map ch.c y)).hom
                  (ch.stalkCompAIso y).inv.hom).hom.app
              ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) ≫
          (totalDerivedExtensionScalars.{u, u, u} (g'.stalkMap (ch.incU' y)).hom).functor.map
            ((totalDerivedExtensionScalarsIdOf.{u, u}
                ((ch.stalkCompAIso y).inv.hom.comp
                  ((X.presheaf.stalkCongr (.of_eq (ch.apply_g'_incU' y))).hom ≫
                    ch.incU.stalkMap (Spec.map ch.c y)).hom)
                (RingHom.ext (commRingCatIso_inv_hom_apply (ch.stalkCompAIso y)))).inv.app
              ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) =
      (ch.chaseTransport y ε' h₁ h₂).hom.app
          ((totalDerivedExtensionScalars.{u, u, u}
              (ch.incU.stalkMap (Spec.map ch.c y)).hom).functor.obj
            ((derivedStalkFunctor (ch.incU (Spec.map ch.c y))).obj K)) ≫
        (totalDerivedExtensionScalars.{u, u, u} ε').functor.map
            ((derivedStalkExtensionCompIsoGeneral (Spec.map ch.c) ch.incU y).hom.app
              ((derivedStalkFunctor (ch.incU (Spec.map ch.c y))).obj K)) ≫
          (totalDerivedExtensionScalars.{u, u, u} ε').functor.map
              (eqToHom (congrArg
                (fun t : Spec ch.A' ⟶ X =>
                  (totalDerivedExtensionScalars.{u, u, u} (t.stalkMap y).hom).functor.obj
                    ((derivedStalkFunctor (t y)).obj K))
                ch.wU'U.symm)) ≫
            (totalDerivedExtensionScalars.{u, u, u} ε').functor.map
                ((eqToIso (congrArg
                  (fun ψ => (totalDerivedExtensionScalars.{u, u, u} ψ).functor)
                  (Stacks.ModuleSkyscraper.stalkMap_hom_comp ch.incU' g' y).symm)).inv.app
                  ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) ≫
              (totalDerivedExtensionScalars.{u, u, u} ε').functor.map
                  ((totalDerivedExtensionScalarsComp.{u, u}
                      (g'.stalkMap (ch.incU' y)).hom
                      (ch.incU'.stalkMap y).hom).inv.app
                    ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) ≫
                (totalDerivedExtensionScalarsComp.{u, u} (ch.incU'.stalkMap y).hom ε').hom.app
                    ((totalDerivedExtensionScalars.{u, u, u}
                        (g'.stalkMap (ch.incU' y)).hom).functor.obj
                      ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) ≫
                  (totalDerivedExtensionScalarsIdOf.{u, u}
                      (ε'.comp (ch.incU'.stalkMap y).hom) (RingHom.ext h₁)).inv.app
                    ((totalDerivedExtensionScalars.{u, u, u}
                        (g'.stalkMap (ch.incU' y)).hom).functor.obj
                      ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) := by
  have hbσ := ch.stalkMap_comp_stalkCompAIso_inv y ε' h₁ h₂
  have hk : (ch.stalkCompAIso y).inv.hom.comp
      ((X.presheaf.stalkCongr (.of_eq (ch.apply_g'_incU' y))).hom ≫
        ch.incU.stalkMap (Spec.map ch.c y)).hom =
      RingHom.id (ToType (X.presheaf.stalk (g' (ch.incU' y)))) :=
    RingHom.ext (commRingCatIso_inv_hom_apply (ch.stalkCompAIso y))
  have hι : ε'.comp (ch.incU'.stalkMap y).hom =
      RingHom.id (ToType (X'.presheaf.stalk (ch.incU' y))) := RingHom.ext h₁
  have hιb : (ε'.comp (ch.incU'.stalkMap y).hom).comp (g'.stalkMap (ch.incU' y)).hom =
      (g'.stalkMap (ch.incU' y)).hom := by
    rw [hι]
    exact RingHom.id_comp _
  have hA := map_eqToHom_comp_comp_hom_extend ch.incU (Spec.map ch.c y) (g' (ch.incU' y))
    (ch.apply_g'_incU' y) K
    (RingHom.id (ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y))))
    (ch.stalkCompAIso y).inv.hom
  have hB := map_eqToHom_comp_comp_hom_extend ch.incU (Spec.map ch.c y) (g' (ch.incU' y))
    (ch.apply_g'_incU' y) K (ch.stalkCompAIso y).inv.hom (g'.stalkMap (ch.incU' y)).hom
  have h_L3 : (totalDerivedExtensionScalars.{u, u, u}
          (g'.stalkMap (ch.incU' y)).hom).functor.map
        ((totalDerivedExtensionScalarsIdOf.{u, u} _ hk).inv.app
          ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) =
      (totalDerivedExtensionScalars.{u, u, u} (g'.stalkMap (ch.incU' y)).hom).functor.map
          (eqToHom (congrArg
            (fun r : ToType (X.presheaf.stalk (g' (ch.incU' y))) →+*
                ToType (X.presheaf.stalk (g' (ch.incU' y))) =>
              (totalDerivedExtensionScalars.{u, u, u} r).functor.obj
                ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) hk)) ≫
        (totalDerivedExtensionScalarsComp.{u, u}
            (RingHom.id (ToType (X.presheaf.stalk (g' (ch.incU' y)))))
            (g'.stalkMap (ch.incU' y)).hom).hom.app
          ((derivedStalkFunctor (g' (ch.incU' y))).obj K) := by
    rw [RingTheory.TorIndependence.idOf_inv_app, CategoryTheory.Functor.map_comp,
      RingTheory.TorIndependence.map_id_inv_app]
  have hdsec : (derivedStalkExtensionCompIsoGeneral (Spec.map ch.c) ch.incU y).hom.app
        ((derivedStalkFunctor (ch.incU (Spec.map ch.c y))).obj K) =
      (totalDerivedExtensionScalarsComp.{u, u} (ch.incU.stalkMap (Spec.map ch.c y)).hom
            ((Spec.map ch.c).stalkMap y).hom).hom.app
          ((derivedStalkFunctor (ch.incU (Spec.map ch.c y))).obj K) ≫
        eqToHom (congrArg
          (fun m : ToType (X.presheaf.stalk (ch.incU (Spec.map ch.c y))) →+*
              ToType ((Spec ch.A').presheaf.stalk y) =>
            (totalDerivedExtensionScalars.{u, u, u} m).functor.obj
              ((derivedStalkFunctor (ch.incU (Spec.map ch.c y))).obj K))
          (Stacks.ModuleSkyscraper.stalkMap_hom_comp (Spec.map ch.c) ch.incU y).symm) := by
    have h0 : (derivedStalkExtensionCompIsoGeneral (Spec.map ch.c) ch.incU y).hom.app
          ((derivedStalkFunctor (ch.incU (Spec.map ch.c y))).obj K) =
        (StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIsoGeneral
              (ch.incU.stalkMap (Spec.map ch.c y)).hom
              ((Spec.map ch.c).stalkMap y).hom).hom.app
            ((derivedStalkFunctor (ch.incU (Spec.map ch.c y))).obj K) ≫
          (eqToIso (congrArg
            (fun ψ : ToType (X.presheaf.stalk (ch.incU (Spec.map ch.c y))) →+*
                ToType ((Spec ch.A').presheaf.stalk y) =>
              (totalDerivedExtensionScalars.{u, u, u} ψ).functor)
            (Stacks.ModuleSkyscraper.stalkMap_hom_comp (Spec.map ch.c) ch.incU
              y).symm)).hom.app ((derivedStalkFunctor (ch.incU (Spec.map ch.c y))).obj K) := rfl
    rw [h0, StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso_eq_totalComp]
    exact whisker_eq _ (RingTheory.TorIndependence.eqToIso_functor_hom_app
      (Stacks.ModuleSkyscraper.stalkMap_hom_comp (Spec.map ch.c) ch.incU y).symm
      ((derivedStalkFunctor (ch.incU (Spec.map ch.c y))).obj K))
  have hR6 : (totalDerivedExtensionScalars.{u, u, u} ε').functor.map
          ((eqToIso (congrArg
            (fun ψ : ToType (X.presheaf.stalk (g' (ch.incU' y))) →+*
                ToType ((Spec ch.A').presheaf.stalk y) =>
              (totalDerivedExtensionScalars.{u, u, u} ψ).functor)
            (Stacks.ModuleSkyscraper.stalkMap_hom_comp ch.incU' g' y).symm)).inv.app
            ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) ≫
        (totalDerivedExtensionScalarsComp.{u, u}
            ((ch.incU'.stalkMap y).hom.comp (g'.stalkMap (ch.incU' y)).hom) ε').hom.app
          ((derivedStalkFunctor (g' (ch.incU' y))).obj K) =
      (totalDerivedExtensionScalarsComp.{u, u}
            (((ch.incU' ≫ g').stalkMap y).hom) ε').hom.app
          ((derivedStalkFunctor ((ch.incU' ≫ g') y)).obj K) ≫
        eqToHom (congrArg
          (fun m : ToType (X.presheaf.stalk (g' (ch.incU' y))) →+*
              ToType ((Spec ch.A').presheaf.stalk y) =>
            (totalDerivedExtensionScalars.{u, u, u} (ε'.comp m)).functor.obj
              ((derivedStalkFunctor (g' (ch.incU' y))).obj K))
          (Stacks.ModuleSkyscraper.stalkMap_hom_comp ch.incU' g' y)) := by
    have hcv := RingTheory.TorIndependence.eqToIso_functor_inv_app
      (Stacks.ModuleSkyscraper.stalkMap_hom_comp ch.incU' g' y).symm
      ((derivedStalkFunctor (g' (ch.incU' y))).obj K)
    rw [hcv]
    exact RingTheory.TorIndependence.map_eqToHom_comp_comp_hom
      (Stacks.ModuleSkyscraper.stalkMap_hom_comp ch.incU' g' y) ε'
      ((derivedStalkFunctor (g' (ch.incU' y))).obj K)
  refine Eq.trans ?_ (RingTheory.TorIndependence.comp3_reassoc_left _ _ _ _)
  refine Eq.trans (RingTheory.TorIndependence.comp2_reassoc_two
    (map_comp2_subst (totalDerivedExtensionScalars.{u, u, u}
      (g'.stalkMap (ch.incU' y)).hom).functor hA) _) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ h_L3)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _
    (RingTheory.TorIndependence.map_eqToHom_comp_comp_hom hk
      (g'.stalkMap (ch.incU' y)).hom ((derivedStalkFunctor (g' (ch.incU' y))).obj K)))) ?_
  refine Eq.trans (whisker_eq _ (RingTheory.TorIndependence.comp2_reassoc_two hB _)) ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ (eqToHom_trans _ _))) ?_
  refine Eq.trans ?_ (whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _
    (whisker_eq _ (whisker_eq _ (RingTheory.TorIndependence.comp2_reassoc_two
      (RingTheory.TorIndependence.map_comp_inv_comp_comp_hom
        (g'.stalkMap (ch.incU' y)).hom (ch.incU'.stalkMap y).hom ε'
        ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) _))))))).symm
  refine Eq.trans ?_ (whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _
    (whisker_eq _ (whisker_eq _ (RingTheory.TorIndependence.comp_inv_comp_idOf_inv
      (ε'.comp (ch.incU'.stalkMap y).hom) hι (g'.stalkMap (ch.incU' y)).hom hιb
      ((derivedStalkFunctor (g' (ch.incU' y))).obj K))))))))).symm
  refine Eq.trans ?_ (whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _
    (RingTheory.TorIndependence.comp2_reassoc_two hR6 _)))))).symm
  refine Eq.trans ?_ (whisker_eq _ (whisker_eq _ (whisker_eq _
    (RingTheory.TorIndependence.comp1_reassoc_two
      (map_eq_comp (totalDerivedExtensionScalars.{u, u, u} ε').functor hdsec) _)))).symm
  refine Eq.trans ?_ (whisker_eq _ (whisker_eq _ (RingTheory.TorIndependence.comp2_reassoc_two
    (RingTheory.TorIndependence.comp_inv_comp_map_comp_hom
      (ch.incU.stalkMap (Spec.map ch.c y)).hom ((Spec.map ch.c).stalkMap y).hom ε'
      ((derivedStalkFunctor (ch.incU (Spec.map ch.c y))).obj K)) _))).symm
  refine Eq.trans ?_ (whisker_eq _ (whisker_eq _ (whisker_eq _
    (RingTheory.TorIndependence.comp2_reassoc_two
      (RingTheory.TorIndependence.comp_inv_comp_map_eqToHom
        (Stacks.ModuleSkyscraper.stalkMap_hom_comp (Spec.map ch.c) ch.incU y).symm ε'
        ((derivedStalkFunctor (ch.incU (Spec.map ch.c y))).obj K)) _)))).symm
  refine Eq.trans ?_ (whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _
    (RingTheory.TorIndependence.comp3_reassoc_one
      (comp_inv_comp_map_eqToHom_stalk y K (Spec.map ch.c ≫ ch.incU) (ch.incU' ≫ g')
        ch.wU'U.symm ε') _))))).symm
  refine Eq.trans ?_ (whisker_eq _ (RingTheory.TorIndependence.comp2_reassoc_two
    (RingTheory.TorIndependence.congr_hom_app_comp_comp_hom hbσ
      (ch.incU.stalkMap (Spec.map ch.c y)).hom
      ((derivedStalkFunctor (ch.incU (Spec.map ch.c y))).obj K)) _)).symm
  refine Eq.trans ?_ (RingTheory.TorIndependence.comp2_reassoc_two
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp_assoc
      (ch.incU.stalkMap (Spec.map ch.c y)).hom (ch.stalkCompAIso y).inv.hom
      (g'.stalkMap (ch.incU' y)).hom
      ((derivedStalkFunctor (ch.incU (Spec.map ch.c y))).obj K)).symm _).symm
  iterate 3 refine Eq.trans ?_ (whisker_eq _ (whisker_eq _
    (RingTheory.TorIndependence.eqToHom_trans_reassoc _ _ _))).symm
  refine Eq.trans ?_ (whisker_eq _ (whisker_eq _ (eqToHom_trans _ _))).symm
  rfl

/-- **The reconciliation at the `Spec 𝒪_X(U)` corner holds**:
`AlgebraicGeometry.BaseChangeChart.SpecCornerComm` is true at every chart, point, complex with
quasi-coherent cohomology and inverse `ε'` of the germ comparison. -/
public theorem specCornerComm (ch : BaseChangeChart f g f' g') (y : Spec ch.A')
    (K : DerivedCategory X.Modules)
    (hK : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X.Modules m).obj K).IsQuasicoherent)
    (ε' : (Spec ch.A').presheaf.stalk y →+* X'.presheaf.stalk (ch.incU' y))
    (h₁ : ∀ x, ε' ((ch.incU'.stalkMap y).hom x) = x)
    (h₂ : ∀ z, (ch.incU'.stalkMap y).hom (ε' z) = z) :
    ch.SpecCornerComm y K hK ε' h₁ h₂ := by
  let := (ch.toStalkA y).toAlgebra
  have := ch.isLocalization_toStalkA y
  let := ((ch.toStalkA' y ε').comp ch.c.hom).toAlgebra
  let := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
  refine Eq.trans (comp_map_comp7_cancel
    (ModuleCat.restrictScalars.{u} ε').mapDerivedCategory _ _ _ _ _ _ _
    ((derivedPullbackStalkIso g' (ch.incU' y)).inv.app K)
    ((derivedPullbackStalkIso g' (ch.incU' y)).hom.app K)
    (Iso.inv_hom_id_app (derivedPullbackStalkIso g' (ch.incU' y)) K) _) ?_
  refine Eq.trans (comp_map_subst_tail
    (ModuleCat.restrictScalars.{u} ε').mapDerivedCategory _ _ _
    (map_map_natTrans_comp
      (RingTheory.TorIndependence.totalDerivedExtensionScalarsCongr.{u, u}
        (ch.toStalkA'_c y ε' h₁ h₂)).inv
      _ _ _ _ (ch.unit_comp_restrictGermDerivedStalkSectionsIso_hom y K hK) _ _ _
      (RingTheory.TorIndependence.map_unit_comp_restrictScalarsDerivedExtendCompIso_hom_app_map
        (ch.primeComplA y) (g'.stalkMap (ch.incU' y)).hom _ _)) _) ?_
  refine unit_comp_map_comp_eq
    (@derivedExtensionScalarsAdjunction.{u, u, u, u, u}
      (ToType ((Spec ch.A').presheaf.stalk y)) (ToType (X'.presheaf.stalk (ch.incU' y))) _ _ ε' _ _
      (totalDerivedExtensionScalars.{u, u, u} ε').functor
      (totalDerivedExtensionScalars.{u, u, u} ε').comparison
      (totalDerivedExtensionScalars.{u, u, u} ε').isLeftDerived)
    (V := (totalDerivedExtensionScalars.{u, u, u} (g'.stalkMap (ch.incU' y)).hom).functor.obj
      ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) _ _
    ((eqToIso (congrArg (fun ψ => (totalDerivedExtensionScalars.{u, u, u} ψ).functor)
          (Stacks.ModuleSkyscraper.stalkMap_hom_comp ch.incU' g' y).symm)).inv.app
        ((derivedStalkFunctor (g' (ch.incU' y))).obj K) ≫
      (totalDerivedExtensionScalarsCompIsoRestrict (g'.stalkMap (ch.incU' y)).hom
          (ch.incU'.stalkMap y).hom ε' h₁ h₂).hom.app
        ((derivedStalkFunctor (g' (ch.incU' y))).obj K))
    (comp4_cancel_mid _ _ _ _ (Iso.hom_inv_id_app _ _) (Iso.inv_hom_id_app _ _)) _ ?_
  refine Eq.trans (whisker_eq _ (whisker_eq _ (whisker_eq _ (whisker_eq _
    (congrArg (totalDerivedExtensionScalars.{u, u, u} (g'.stalkMap (ch.incU' y)).hom).functor.map
      (ch.localTailMorphism_eq y K hK)))))) ?_
  refine Eq.trans (comp4_map_comp5_expand
    (totalDerivedExtensionScalars.{u, u, u} (g'.stalkMap (ch.incU' y)).hom).functor
    _ _ _ _ _ _ _ _ _) ?_
  refine Eq.trans ?_ (map_comp6_comp2_subst
    (totalDerivedExtensionScalars.{u, u, u} ε').functor _ _ _ _ _ _ _
    (map_totalDerivedExtensionScalarsCompIsoRestrict_hom_comp_counit
      (g'.stalkMap (ch.incU' y)).hom (ch.incU'.stalkMap y).hom ε' h₁ h₂
      ((derivedStalkFunctor (g' (ch.incU' y))).obj K))).symm
  exact comp5_map_comp3_transport3 _ _ (ch.chaseTransport y ε' h₁ h₂) _ _ _ _ _
    (derivedStalkAffineSectionsIso ch.incU (Spec.map ch.c y) K hK).hom _ _ _ _ _ _ _
    (ch.specCornerHead y K ε' h₁ h₂) (ch.specCornerTail y K ε' h₁ h₂)

/-- **The source bridge's commutation at a chart.** The comparison of the four local rings on
cohomology, read on the source identification of the cube, is the chart's own comparison inserted
at the germ generator of the `𝒪_{X'}(U')`-localization. -/
public theorem cohomologyComparisonMap_localRingsSourceMap
    (ch : BaseChangeChart f g f' g') (y : Spec ch.A') (w : g' ≫ f = f' ≫ g)
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (hK : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X.Modules m).obj K).IsQuasicoherent)
    (hK' : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X'.Modules m).obj K').IsQuasicoherent)
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K')
    (ε' : (Spec ch.A').presheaf.stalk y →+* X'.presheaf.stalk (ch.incU' y))
    (h₁ : ∀ x, ε' ((ch.incU'.stalkMap y).hom x) = x)
    (h₂ : ∀ z, (ch.incU'.stalkMap y).hom (ε' z) = z) (n : ℤ) :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    letI := ch.c.hom.toAlgebra
    letI := ch.d.hom.toAlgebra
    letI := (ch.c.hom.comp ch.a.hom).toAlgebra
    haveI : IsScalarTower ch.R ch.A ch.A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower ch.R ch.R' ch.A' :=
      IsScalarTower.of_algebraMap_eq fun r => DFunLike.congr_fun ch.isPushout_hom r
    letI := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
    letI := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
    letI := ((g'.stalkMap (ch.incU' y)).hom.comp (f.stalkMap (g' (ch.incU' y))).hom).toAlgebra
    letI := (g'.stalkMap (ch.incU' y)).hom.toAlgebra
    letI := (f'.stalkMap (ch.incU' y)).hom.toAlgebra
    haveI : IsScalarTower (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (ToType (X.presheaf.stalk (g' (ch.incU' y)))) (ToType (X'.presheaf.stalk (ch.incU' y))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        (ToType (X'.presheaf.stalk (ch.incU' y))) :=
      IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w (ch.incU' y))
    letI := (ch.toStalkR y).toAlgebra
    letI := (ch.toStalkA y).toAlgebra
    haveI := ch.isLocalization_toStalkA y
    letI := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
    letI := ((ch.toStalkA' y ε').comp ch.c.hom).toAlgebra
    letI := (((ch.toStalkA' y ε').comp ch.c.hom).comp ch.a.hom).toAlgebra
    haveI : IsScalarTower ch.R ch.A (ToType (X'.presheaf.stalk (ch.incU' y))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower ch.R (ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        (ToType (X'.presheaf.stalk (ch.incU' y))) :=
      IsScalarTower.of_algebraMap_eq' (ch.outerSquare_comm y ε' h₁ h₂)
    letI := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
    letI := ((specGermRingHom ch.A (Spec.map ch.c y)).comp ch.a.hom).toAlgebra
    haveI : IsScalarTower ch.R ch.A
        (ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    ∀ m₀ : (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
        ((affineDerivedSections ch.incU).obj K) n : Type u),
      (RingTheory.TorIndependence.cohomologyComparisonMapGeneral
            (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
            (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
            ((derivedStalkFunctor (g' (ch.incU' y))).obj K)
            ((derivedStalkFunctor (ch.incU' y)).obj K')
            ((derivedPullbackStalkIso g' (ch.incU' y)).inv.app K ≫
              (derivedStalkFunctor (ch.incU' y)).map φ) n).hom
          (ch.localRingsSourceMap y w K hK n m₀) =
        (homologyDerivedStalkAffineSectionsRestrictIso ch.incU' y K' hK' ε' h₁ h₂ n).hom.hom
          ((1 : ToType ((Spec ch.A').presheaf.stalk y)) ⊗ₜ[ch.A', specGermRingHom ch.A' y]
            (RingTheory.TorIndependence.cohomologyComparisonMapGeneral (R := ch.R) (R' := ch.R')
              ((affineDerivedSections ch.incU).obj K) ((affineDerivedSections ch.incU').obj K')
              (ch.sectionsBaseChangeMap K ≫ (affineDerivedSections ch.incU').map φ) n).hom m₀) :=
  ch.cohomologyComparisonMap_localRingsSourceMap_of_specCorner y w K K' hK hK' φ ε' h₁ h₂ n
    (ch.specCornerComm y K hK ε' h₁ h₂)

end BaseChangeChart

end AlgebraicGeometry

end
