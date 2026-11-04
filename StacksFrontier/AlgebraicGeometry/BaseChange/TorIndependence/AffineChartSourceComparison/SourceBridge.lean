module

public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartSourceComparison.PastedSquare
public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartSourceComparison.UnitRestrict
public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartSourceComparison.OuterSquare

/-!
# The source bridge under the `Spec 𝒪_X(U)` corner hypothesis

`AlgebraicGeometry.BaseChangeChart.SpecCornerComm`,
`AlgebraicGeometry.BaseChangeChart.unit_comp_localTail_of_specCorner`,
`AlgebraicGeometry.BaseChangeChart.cohomologyComparisonMap_localRingsSourceMap_of_specCorner`, and
the chart's target corner in the generic spelling.
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

namespace BaseChangeChart

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-! ### Three regroupings of a composite -/

section Regroup

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A tail inside the argument of a functor, pulled out of an eight-fold composite. -/
private theorem comp_map_comp8_tail (F : C ⥤ D) {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ : C} {W : D}
    (p : W ⟶ F.obj X₀) (r₁ : X₀ ⟶ X₁) (r₂ : X₁ ⟶ X₂) (r₃ : X₂ ⟶ X₃) (r₄ : X₃ ⟶ X₄)
    (r₅ : X₄ ⟶ X₅) (r₆ : X₅ ⟶ X₆) (r₇ : X₆ ⟶ X₇) (t : X₇ ⟶ X₈) :
    p ≫ F.map (r₁ ≫ r₂ ≫ r₃ ≫ r₄ ≫ r₅ ≫ r₆ ≫ r₇ ≫ t) =
      (p ≫ F.map (r₁ ≫ r₂ ≫ r₃ ≫ r₄ ≫ r₅ ≫ r₆ ≫ r₇)) ≫ F.map t := by
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]

/-- A square in the middle of a three-fold composite. -/
private theorem comp_tail_comm {W₀ W₁ W₂ W₃ W₄ : D} (p : W₀ ⟶ W₁) (q : W₁ ⟶ W₂) (t : W₂ ⟶ W₃)
    (q' : W₁ ⟶ W₄) (r' : W₄ ⟶ W₃) (h : q' ≫ r' = q ≫ t) :
    (p ≫ q) ≫ t = p ≫ q' ≫ r' := by
  rw [Category.assoc, h]

/-- The three middle factors of a five-fold composite, replaced and the head reassociated. -/
private theorem comp5_subst_middle3 {W₀ W₁ W₂ W₃ W₄ W₅ W₆ W₇ : D} (p : W₀ ⟶ W₁)
    {q : W₁ ⟶ W₂} {r : W₂ ⟶ W₃} {s : W₃ ⟶ W₄} (t : W₄ ⟶ W₅)
    {q' : W₁ ⟶ W₆} {r' : W₆ ⟶ W₇} {s' : W₇ ⟶ W₄}
    (h : q ≫ r ≫ s = q' ≫ r' ≫ s') :
    p ≫ q ≫ r ≫ s ≫ t = (p ≫ q') ≫ r' ≫ s' ≫ t := by
  simp only [Category.assoc]
  rw [reassoc_of% h]

end Regroup

/-- **The reconciliation at the `Spec 𝒪_X(U)` corner of the chart.** The chart's own route to
the target corner of its outer rectangle — the two composition isomorphisms of derived extension
of scalars, the unit of the derived change-of-rings adjunction along the germ map of `𝒪_X(U)`,
the merge of the two restrictions of
`AlgebraicGeometry.BaseChangeChart.restrictGermDerivedStalkSectionsIso` and the passage of
`RingTheory.TorIndependence.restrictScalarsDerivedExtendCompIso` — read, after its target corner
has been put back into the `𝒪_{Spec 𝒪_{X'}(U'), y}` spelling by
`AlgebraicGeometry.totalDerivedExtensionScalarsCompIsoRestrict`, against the six-factor route
through `Spec 𝒪_X(U)` on the right of
`AlgebraicGeometry.BaseChangeChart.extendScalars_map_sectionsBaseChangeMap_eq`.

Both sides are morphisms of `D(𝒪_{Spec 𝒪_{X'}(U'), y})` out of the germ localization of
`RΓ(U,K) ⊗ᴸ_{𝒪_X(U)} 𝒪_{X'}(U')`, and the equation says that the two ways of reaching the
derived stalk at `g' x'` through the `Spec 𝒪_X(U)` corner agree. -/
public abbrev SpecCornerComm (ch : BaseChangeChart f g f' g') (y : Spec ch.A')
    (K : DerivedCategory X.Modules)
    (hK : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X.Modules m).obj K).IsQuasicoherent)
    (ε' : (Spec ch.A').presheaf.stalk y →+* X'.presheaf.stalk (ch.incU' y))
    (h₁ : ∀ x, ε' ((ch.incU'.stalkMap y).hom x) = x)
    (h₂ : ∀ z, (ch.incU'.stalkMap y).hom (ε' z) = z) : Prop :=
  let := (ch.toStalkA y).toAlgebra
  have := ch.isLocalization_toStalkA y
  let := ((ch.toStalkA' y ε').comp ch.c.hom).toAlgebra
  let := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
  (((@derivedExtensionScalarsAdjunction.{u, u, u, u, u}
              (ToType ((Spec ch.A').presheaf.stalk y))
              (ToType (X'.presheaf.stalk (ch.incU' y))) _ _ ε' _ _
              (totalDerivedExtensionScalars.{u, u, u} ε').functor
              (totalDerivedExtensionScalars.{u, u, u} ε').comparison
              (totalDerivedExtensionScalars.{u, u, u} ε').isLeftDerived).unit.app
            ((totalDerivedExtensionScalars.{u, u, u} (specGermRingHom ch.A' y)).functor.obj
              ((totalDerivedExtensionScalars.{u, u, u} ch.c.hom).functor.obj
                ((affineDerivedSections ch.incU).obj K))) ≫
          (ModuleCat.restrictScalars.{u} ε').mapDerivedCategory.map
            ((totalDerivedExtensionScalarsComp.{u, u} (specGermRingHom ch.A' y) ε').hom.app
                ((totalDerivedExtensionScalars.{u, u, u} ch.c.hom).functor.obj
                  ((affineDerivedSections ch.incU).obj K)) ≫
              (totalDerivedExtensionScalarsComp.{u, u} ch.c.hom (ch.toStalkA' y ε')).hom.app
                  ((affineDerivedSections ch.incU).obj K) ≫
                (totalDerivedExtensionScalars.{u, u, u} (algebraMap (ToType ch.A)
                        (ToType (X'.presheaf.stalk (ch.incU' y))))).functor.map
                    ((RingTheory.TorIndependence.derivedExtendRestrictAdjunction (A := ToType ch.A)
                      (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))).unit.app
                      ((affineDerivedSections ch.incU).obj K)) ≫
                  (totalDerivedExtensionScalars.{u, u, u} (algebraMap (ToType ch.A)
                        (ToType (X'.presheaf.stalk (ch.incU' y))))).functor.map
                      (ch.restrictGermDerivedStalkSectionsIso y K hK).hom ≫
                    (RingTheory.TorIndependence.totalDerivedExtensionScalarsCongr.{u, u}
                          (ch.toStalkA'_c y ε' h₁ h₂)).inv.app
                        ((ModuleCat.restrictScalars.{u} (ch.toStalkA y)).mapDerivedCategory.obj
                          ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) ≫
                      (RingTheory.TorIndependence.restrictScalarsDerivedExtendCompIso.{u, u}
                            (ch.primeComplA y) (g'.stalkMap (ch.incU' y)).hom).hom.app
                          ((derivedStalkFunctor (g' (ch.incU' y))).obj K) ≫
                        (derivedPullbackStalkIso g' (ch.incU' y)).inv.app K)) ≫
      ((ModuleCat.restrictScalars.{u} ε').mapDerivedCategory.map
            ((derivedPullbackStalkIso g' (ch.incU' y)).hom.app K) ≫
          (totalDerivedExtensionScalarsCompIsoRestrict (g'.stalkMap (ch.incU' y)).hom
                (ch.incU'.stalkMap y).hom ε' h₁ h₂).inv.app
              ((derivedStalkFunctor (g' (ch.incU' y))).obj K) ≫
            (eqToIso (congrArg (fun ψ => (totalDerivedExtensionScalars.{u, u, u} ψ).functor)
                (Stacks.ModuleSkyscraper.stalkMap_hom_comp ch.incU' g' y).symm)).hom.app
              ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) =
      (StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIsoGeneral ch.c.hom
            (specGermRingHom ch.A' y)).hom.app ((affineDerivedSections ch.incU).obj K) ≫
        eqToHom (congrArg
          (fun ψ => (totalDerivedExtensionScalars.{u, u, u} ψ).functor.obj
            ((affineDerivedSections ch.incU).obj K))
          (specGermRingHom_stalkMap ch.c y).symm) ≫
        (StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIsoGeneral
            (specGermRingHom ch.A (Spec.map ch.c y))
            ((Spec.map ch.c).stalkMap y).hom).inv.app
          ((affineDerivedSections ch.incU).obj K) ≫
        (totalDerivedExtensionScalars.{u, u, u} ((Spec.map ch.c).stalkMap y).hom).functor.map
          ((derivedStalkAffineSectionsIso ch.incU (Spec.map ch.c y) K hK).hom) ≫
        (derivedStalkExtensionCompIsoGeneral (Spec.map ch.c) ch.incU y).hom.app
          ((derivedStalkFunctor (ch.incU (Spec.map ch.c y))).obj K) ≫
        eqToHom (congrArg
          (fun t : Spec ch.A' ⟶ X =>
            (totalDerivedExtensionScalars.{u, u, u} (t.stalkMap y).hom).functor.obj
              ((derivedStalkFunctor (t y)).obj K))
          ch.wU'U.symm))

/-- **The identification of the chart's target corner, before the pointwise morphism, under the
hypothesis `hspec : AlgebraicGeometry.BaseChangeChart.SpecCornerComm`.**

The hypothesis `hspec` is the chart's own route to the target corner — the two composition
isomorphisms, the unit along the germ map of `𝒪_X(U)`, the merge of the two restrictions of
`AlgebraicGeometry.BaseChangeChart.restrictGermDerivedStalkSectionsIso` and the passage of
`RingTheory.TorIndependence.restrictScalarsDerivedExtendCompIso` — read against the six-factor
route through `Spec 𝒪_X(U)` of
`AlgebraicGeometry.BaseChangeChart.extendScalars_map_sectionsBaseChangeMap_eq`, with the target
corner of both put into the `𝒪_{Spec 𝒪_{X'}(U'), y}` spelling by
`AlgebraicGeometry.totalDerivedExtensionScalarsCompIsoRestrict`. -/
public theorem unit_comp_localTailCore_of_specCorner (ch : BaseChangeChart f g f' g')
    (y : Spec ch.A')
    (K : DerivedCategory X.Modules)
    (hK : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X.Modules m).obj K).IsQuasicoherent)
    (hK'' : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X'.Modules m).obj
      ((Stacks.Duality.derivedPullback g').obj K)).IsQuasicoherent)
    (ε' : (Spec ch.A').presheaf.stalk y →+* X'.presheaf.stalk (ch.incU' y))
    (h₁ : ∀ x, ε' ((ch.incU'.stalkMap y).hom x) = x)
    (h₂ : ∀ z, (ch.incU'.stalkMap y).hom (ε' z) = z)
    (hspec : ch.SpecCornerComm y K hK ε' h₁ h₂) :
    letI := (ch.toStalkA y).toAlgebra
    haveI := ch.isLocalization_toStalkA y
    letI := ((ch.toStalkA' y ε').comp ch.c.hom).toAlgebra
    letI := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
    (@derivedExtensionScalarsAdjunction.{u, u, u, u, u}
            (ToType ((Spec ch.A').presheaf.stalk y))
            (ToType (X'.presheaf.stalk (ch.incU' y))) _ _ ε' _ _
            (totalDerivedExtensionScalars.{u, u, u} ε').functor
            (totalDerivedExtensionScalars.{u, u, u} ε').comparison
            (totalDerivedExtensionScalars.{u, u, u} ε').isLeftDerived).unit.app
          ((totalDerivedExtensionScalars.{u, u, u} (specGermRingHom ch.A' y)).functor.obj
            ((totalDerivedExtensionScalars.{u, u, u} ch.c.hom).functor.obj
              ((affineDerivedSections ch.incU).obj K))) ≫
        (ModuleCat.restrictScalars.{u} ε').mapDerivedCategory.map
          ((totalDerivedExtensionScalarsComp.{u, u} (specGermRingHom ch.A' y) ε').hom.app
              ((totalDerivedExtensionScalars.{u, u, u} ch.c.hom).functor.obj
                ((affineDerivedSections ch.incU).obj K)) ≫
            (totalDerivedExtensionScalarsComp.{u, u} ch.c.hom (ch.toStalkA' y ε')).hom.app
                ((affineDerivedSections ch.incU).obj K) ≫
              (totalDerivedExtensionScalars.{u, u, u} (algebraMap (ToType ch.A)
                      (ToType (X'.presheaf.stalk (ch.incU' y))))).functor.map
                  ((RingTheory.TorIndependence.derivedExtendRestrictAdjunction (A := ToType ch.A)
                    (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))).unit.app
                    ((affineDerivedSections ch.incU).obj K)) ≫
                (totalDerivedExtensionScalars.{u, u, u} (algebraMap (ToType ch.A)
                      (ToType (X'.presheaf.stalk (ch.incU' y))))).functor.map
                    (ch.restrictGermDerivedStalkSectionsIso y K hK).hom ≫
                  (RingTheory.TorIndependence.totalDerivedExtensionScalarsCongr.{u, u}
                        (ch.toStalkA'_c y ε' h₁ h₂)).inv.app
                      ((ModuleCat.restrictScalars.{u} (ch.toStalkA y)).mapDerivedCategory.obj
                        ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) ≫
                    (RingTheory.TorIndependence.restrictScalarsDerivedExtendCompIso.{u, u}
                          (ch.primeComplA y) (g'.stalkMap (ch.incU' y)).hom).hom.app
                        ((derivedStalkFunctor (g' (ch.incU' y))).obj K) ≫
                      (derivedPullbackStalkIso g' (ch.incU' y)).inv.app K) =
      (totalDerivedExtensionScalars.{u, u, u} (specGermRingHom ch.A' y)).functor.map
          (ch.sectionsBaseChangeMap K) ≫
        (derivedStalkAffineSectionsRestrictIso ch.incU' y
            ((Stacks.Duality.derivedPullback g').obj K) hK'' ε' h₁ h₂).hom := by
  let := (ch.toStalkA y).toAlgebra
  have := ch.isLocalization_toStalkA y
  let := ((ch.toStalkA' y ε').comp ch.c.hom).toAlgebra
  let := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
  have hB : (derivedStalkExtensionCompIsoGeneral ch.incU' g' y).hom.app
        ((derivedStalkFunctor (g' (ch.incU' y))).obj K) =
      (totalDerivedExtensionScalarsComp.{u, u} (g'.stalkMap (ch.incU' y)).hom
            (ch.incU'.stalkMap y).hom).hom.app
          ((derivedStalkFunctor (g' (ch.incU' y))).obj K) ≫
        (eqToIso (congrArg (fun ψ => (totalDerivedExtensionScalars.{u, u, u} ψ).functor)
            (Stacks.ModuleSkyscraper.stalkMap_hom_comp ch.incU' g' y).symm)).hom.app
          ((derivedStalkFunctor (g' (ch.incU' y))).obj K) := by
    have hd : derivedStalkExtensionCompIsoGeneral ch.incU' g' y =
        StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIsoGeneral
            (g'.stalkMap (ch.incU' y)).hom (ch.incU'.stalkMap y).hom ≪≫
          eqToIso (congrArg (fun ψ => (totalDerivedExtensionScalars.{u, u, u} ψ).functor)
            (Stacks.ModuleSkyscraper.stalkMap_hom_comp ch.incU' g' y).symm) := rfl
    rw [hd, StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso_eq_totalComp]
    dsimp only [Iso.trans_hom, NatTrans.comp_app]
  have hE := ch.extendScalars_map_sectionsBaseChangeMap_eq K hK hK'' y
  rw [hB] at hE
  have hmerge := derivedStalkAffineSectionsIso_hom_comp_merge ch.incU' y
    ((Stacks.Duality.derivedPullback g').obj K) hK'' ε' h₁ h₂
    (g'.stalkMap (ch.incU' y)).hom ((derivedStalkFunctor (g' (ch.incU' y))).obj K)
    ((derivedPullbackStalkIso g' (ch.incU' y)).hom.app K)
  have : IsIso ((derivedPullbackStalkIso g' (ch.incU' y)).hom.app K) :=
    inferInstanceAs (IsIso ((derivedPullbackStalkIso g' (ch.incU' y)).app K).hom)
  have : IsIso ((totalDerivedExtensionScalarsCompIsoRestrict (g'.stalkMap (ch.incU' y)).hom
      (ch.incU'.stalkMap y).hom ε' h₁ h₂).inv.app
      ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) :=
    inferInstance
  have : IsIso ((eqToIso (congrArg (fun ψ => (totalDerivedExtensionScalars.{u, u, u} ψ).functor)
      (Stacks.ModuleSkyscraper.stalkMap_hom_comp ch.incU' g' y).symm)).hom.app
      ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) :=
    inferInstance
  exact (cancel_mono _).mp (hspec.trans (hE.symm.trans (comp5_subst_middle3 _ _ hmerge)))

/-- **The identification of the chart's target corner, under the hypothesis
`hspec : AlgebraicGeometry.BaseChangeChart.SpecCornerComm`.** The unit along `ε'` followed by the
two composition isomorphisms and the tail of `AlgebraicGeometry.BaseChangeChart.localTail` is the
germ base change of the chart's own morphism followed by
`AlgebraicGeometry.derivedStalkAffineSectionsRestrictIso`. -/
public theorem unit_comp_localTail_of_specCorner (ch : BaseChangeChart f g f' g')
    (y : Spec ch.A')
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (hK : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X.Modules m).obj K).IsQuasicoherent)
    (hK' : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X'.Modules m).obj K').IsQuasicoherent)
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K')
    (ε' : (Spec ch.A').presheaf.stalk y →+* X'.presheaf.stalk (ch.incU' y))
    (h₁ : ∀ x, ε' ((ch.incU'.stalkMap y).hom x) = x)
    (h₂ : ∀ z, (ch.incU'.stalkMap y).hom (ε' z) = z)
    (hspec : ch.SpecCornerComm y K hK ε' h₁ h₂) :
    letI := (ch.toStalkA y).toAlgebra
    haveI := ch.isLocalization_toStalkA y
    letI := ((ch.toStalkA' y ε').comp ch.c.hom).toAlgebra
    letI := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
    (@derivedExtensionScalarsAdjunction.{u, u, u, u, u}
            (ToType ((Spec ch.A').presheaf.stalk y))
            (ToType (X'.presheaf.stalk (ch.incU' y))) _ _ ε' _ _
            (totalDerivedExtensionScalars.{u, u, u} ε').functor
            (totalDerivedExtensionScalars.{u, u, u} ε').comparison
            (totalDerivedExtensionScalars.{u, u, u} ε').isLeftDerived).unit.app
          ((totalDerivedExtensionScalars.{u, u, u} (specGermRingHom ch.A' y)).functor.obj
            ((totalDerivedExtensionScalars.{u, u, u} ch.c.hom).functor.obj
              ((affineDerivedSections ch.incU).obj K))) ≫
        (ModuleCat.restrictScalars.{u} ε').mapDerivedCategory.map
          ((totalDerivedExtensionScalarsComp.{u, u} (specGermRingHom ch.A' y) ε').hom.app
              ((totalDerivedExtensionScalars.{u, u, u} ch.c.hom).functor.obj
                ((affineDerivedSections ch.incU).obj K)) ≫
            (totalDerivedExtensionScalarsComp.{u, u} ch.c.hom (ch.toStalkA' y ε')).hom.app
                ((affineDerivedSections ch.incU).obj K) ≫
              ((totalDerivedExtensionScalars.{u, u, u} (algebraMap (ToType ch.A)
                      (ToType (X'.presheaf.stalk (ch.incU' y))))).functor.map
                  ((RingTheory.TorIndependence.derivedExtendRestrictAdjunction (A := ToType ch.A)
                    (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))).unit.app
                    ((affineDerivedSections ch.incU).obj K)) ≫
                (totalDerivedExtensionScalars.{u, u, u} (algebraMap (ToType ch.A)
                      (ToType (X'.presheaf.stalk (ch.incU' y))))).functor.map
                    (ch.restrictGermDerivedStalkSectionsIso y K hK).hom ≫
                  ch.localTail y ε' h₁ h₂ K φ)) =
      (totalDerivedExtensionScalars.{u, u, u} (specGermRingHom ch.A' y)).functor.map
          (ch.sectionsBaseChangeMap K ≫ (affineDerivedSections ch.incU').map φ) ≫
        (derivedStalkAffineSectionsRestrictIso ch.incU' y K' hK' ε' h₁ h₂).hom := by
  let := (ch.toStalkA y).toAlgebra
  have := ch.isLocalization_toStalkA y
  let := ((ch.toStalkA' y ε').comp ch.c.hom).toAlgebra
  let := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
  have hqc : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X'.Modules m).obj
      ((Stacks.Duality.derivedPullback g').obj K)).IsQuasicoherent :=
    fun m => Stacks.Duality.isQuasicoherent_homology_derivedPullback' g' ⟨K, hK⟩ m
  have hnat := derivedStalkAffineSectionsRestrictIso_hom_naturality ch.incU'
    ((Stacks.Duality.derivedPullback g').obj K) K' hqc hK' φ y ε' h₁ h₂
  have hcore := ch.unit_comp_localTailCore_of_specCorner y K hK hqc ε' h₁ h₂ hspec
  dsimp only [localTail]
  refine Eq.trans (comp_map_comp8_tail
    (ModuleCat.restrictScalars.{u} ε').mapDerivedCategory _ _ _ _ _ _ _ _ _) ?_
  rw [hcore]
  refine Eq.trans (comp_tail_comm _ _ _ _ _ hnat) ?_
  exact (CategoryTheory.Functor.map_comp_assoc _ _ _ _).symm

/-- **The source bridge's commutation, under the identification of the target corner as
hypothesis.** The comparison of the four local rings on cohomology, read on the source
identification of the cube, is the chart's own comparison inserted at the germ generator of the
`𝒪_{X'}(U')`-localization.

The hypothesis is the identification of the chart's target corner: the unit along `ε'` followed
by the two composition isomorphisms and the tail of
`AlgebraicGeometry.BaseChangeChart.localTail` is the germ base change of the chart's own morphism
followed by `AlgebraicGeometry.derivedStalkAffineSectionsRestrictIso`. -/
private theorem cohomologyComparisonMap_localRingsSourceMap_of_corner
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
    ((@derivedExtensionScalarsAdjunction.{u, u, u, u, u}
            (ToType ((Spec ch.A').presheaf.stalk y))
            (ToType (X'.presheaf.stalk (ch.incU' y))) _ _ ε' _ _
            (totalDerivedExtensionScalars.{u, u, u} ε').functor
            (totalDerivedExtensionScalars.{u, u, u} ε').comparison
            (totalDerivedExtensionScalars.{u, u, u} ε').isLeftDerived).unit.app
          ((totalDerivedExtensionScalars.{u, u, u} (specGermRingHom ch.A' y)).functor.obj
            ((totalDerivedExtensionScalars.{u, u, u} ch.c.hom).functor.obj
              ((affineDerivedSections ch.incU).obj K))) ≫
        (ModuleCat.restrictScalars.{u} ε').mapDerivedCategory.map
          ((totalDerivedExtensionScalarsComp.{u, u} (specGermRingHom ch.A' y) ε').hom.app
              ((totalDerivedExtensionScalars.{u, u, u} ch.c.hom).functor.obj
                ((affineDerivedSections ch.incU).obj K)) ≫
            (totalDerivedExtensionScalarsComp.{u, u} ch.c.hom (ch.toStalkA' y ε')).hom.app
                ((affineDerivedSections ch.incU).obj K) ≫
              ((totalDerivedExtensionScalars.{u, u, u} (algebraMap (ToType ch.A)
                      (ToType (X'.presheaf.stalk (ch.incU' y))))).functor.map
                  ((RingTheory.TorIndependence.derivedExtendRestrictAdjunction (A := ToType ch.A)
                    (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))).unit.app
                    ((affineDerivedSections ch.incU).obj K)) ≫
                (totalDerivedExtensionScalars.{u, u, u} (algebraMap (ToType ch.A)
                      (ToType (X'.presheaf.stalk (ch.incU' y))))).functor.map
                    (ch.restrictGermDerivedStalkSectionsIso y K hK).hom ≫
                  ch.localTail y ε' h₁ h₂ K φ)) =
      (totalDerivedExtensionScalars.{u, u, u} (specGermRingHom ch.A' y)).functor.map
          (ch.sectionsBaseChangeMap K ≫ (affineDerivedSections ch.incU').map φ) ≫
        (derivedStalkAffineSectionsRestrictIso ch.incU' y K' hK' ε' h₁ h₂).hom) →
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
              (ch.sectionsBaseChangeMap K ≫ (affineDerivedSections ch.incU').map φ) n).hom m₀) := by
  let := ch.a.hom.toAlgebra
  let := ch.b.hom.toAlgebra
  let := ch.c.hom.toAlgebra
  let := ch.d.hom.toAlgebra
  let := (ch.c.hom.comp ch.a.hom).toAlgebra
  have : IsScalarTower ch.R ch.A ch.A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ch.R ch.R' ch.A' :=
    IsScalarTower.of_algebraMap_eq fun r => DFunLike.congr_fun ch.isPushout_hom r
  let := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
  let := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
  let := ((g'.stalkMap (ch.incU' y)).hom.comp (f.stalkMap (g' (ch.incU' y))).hom).toAlgebra
  let := (g'.stalkMap (ch.incU' y)).hom.toAlgebra
  let := (f'.stalkMap (ch.incU' y)).hom.toAlgebra
  have : IsScalarTower (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (ToType (X.presheaf.stalk (g' (ch.incU' y)))) (ToType (X'.presheaf.stalk (ch.incU' y))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (ToType (S'.presheaf.stalk (f' (ch.incU' y))))
      (ToType (X'.presheaf.stalk (ch.incU' y))) :=
    IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w (ch.incU' y))
  let := (ch.toStalkR y).toAlgebra
  let := (ch.toStalkA y).toAlgebra
  have := ch.isLocalization_toStalkA y
  let := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
  let := ((ch.toStalkA' y ε').comp ch.c.hom).toAlgebra
  let := (((ch.toStalkA' y ε').comp ch.c.hom).comp ch.a.hom).toAlgebra
  have : IsScalarTower ch.R ch.A (ToType (X'.presheaf.stalk (ch.incU' y))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower ch.R (ToType (S'.presheaf.stalk (f' (ch.incU' y))))
      (ToType (X'.presheaf.stalk (ch.incU' y))) :=
    IsScalarTower.of_algebraMap_eq' (ch.outerSquare_comm y ε' h₁ h₂)
  let := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
  let := ((specGermRingHom ch.A (Spec.map ch.c y)).comp ch.a.hom).toAlgebra
  have : IsScalarTower ch.R ch.A
      (ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  intro htail m₀
  have hε'flat : ε'.Flat := RingHom.Flat.of_bijective
    ⟨fun z₁ z₂ hz => (h₂ z₁).symm.trans
      ((congrArg (ch.incU'.stalkMap y).hom hz).trans (h₂ z₂)),
      fun x => ⟨(ch.incU'.stalkMap y).hom x, h₁ x⟩⟩
  have hpflat : (specGermRingHom ch.A' y).Flat := flat_specGermRingHom ch.A' y
  have hvflat : (ch.toStalkA' y ε').Flat := RingHom.Flat.comp hpflat hε'flat
  have houter : RingTheory.TorIndependence.squareDerivedComparisonGeneral (R := ToType ch.R)
        (A := ToType ch.A) (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        (A' := ToType (X'.presheaf.stalk (ch.incU' y))) =
      RingTheory.TorIndependence.squareComparison.{u, u} ch.a.hom
        ((ch.toStalkR' y).comp ch.b.hom) ((ch.toStalkA' y ε').comp ch.c.hom)
        (f'.stalkMap (ch.incU' y)).hom (ch.outerSquare_comm y ε' h₁ h₂) := rfl
  have htop : RingTheory.TorIndependence.squareDerivedComparisonGeneral (R := ToType ch.R)
        (A := ToType ch.A) (R' := ToType ch.R') (A' := ToType ch.A') =
      RingTheory.TorIndependence.squareComparison.{u, u} ch.a.hom ch.b.hom ch.c.hom ch.d.hom
        ch.isPushout_hom := rfl
  have hRIap : ∀ x, (homologyDerivedStalkAffineSectionsRestrictIso ch.incU' y K' hK'
          ε' h₁ h₂ n).hom.hom x =
      (((ModuleCat.restrictScalars.{u} ε').mapDerivedCategoryHomologyIso n).hom.app
          ((derivedStalkFunctor (ch.incU' y)).obj K')).hom
        (((DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((Spec ch.A').presheaf.stalk y)) n).map
            (derivedStalkAffineSectionsRestrictIso ch.incU' y K' hK' ε' h₁ h₂).hom).hom
          (((RingTheory.TorIndependence.flatDerivedHomologyIso.{u, u} (specGermRingHom ch.A' y)
              hpflat n).app ((affineDerivedSections ch.incU').obj K')).inv.hom x)) :=
    fun _ => rfl
  have hnatd := NatTrans.naturality
    ((ModuleCat.restrictScalars.{u} ch.d.hom).mapDerivedCategoryHomologyIso n).hom
    (ch.sectionsBaseChangeMap K ≫ (affineDerivedSections ch.incU').map φ)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnatd
  have hq : ((DerivedCategory.homologyFunctor (ModuleCat.{u} ch.R') n).map
            ((RingTheory.TorIndependence.squareComparison.{u, u} ch.a.hom ch.b.hom ch.c.hom
                  ch.d.hom ch.isPushout_hom).app ((affineDerivedSections ch.incU).obj K) ≫
              (ModuleCat.restrictScalars.{u} ch.d.hom).mapDerivedCategory.map
                (ch.sectionsBaseChangeMap K ≫ (affineDerivedSections ch.incU').map φ)) ≫
          (((ModuleCat.restrictScalars.{u} ch.d.hom).mapDerivedCategoryHomologyIso n).hom.app
            ((affineDerivedSections ch.incU').obj K'))).hom m₀ =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} ch.A') n).map
          (ch.sectionsBaseChangeMap K ≫ (affineDerivedSections ch.incU').map φ)).hom
        ((((ModuleCat.restrictScalars.{u} ch.d.hom).mapDerivedCategoryHomologyIso n).hom.app
              ((totalDerivedExtensionScalars.{u, u, u} ch.c.hom).functor.obj
                ((affineDerivedSections ch.incU).obj K))).hom
          (((DerivedCategory.homologyFunctor (ModuleCat.{u} ch.R') n).map
            ((RingTheory.TorIndependence.squareComparison.{u, u} ch.a.hom ch.b.hom ch.c.hom
                ch.d.hom ch.isPushout_hom).app
              ((affineDerivedSections ch.incU).obj K))).hom m₀)) :=
    Eq.trans
      (ConcreteCategory.congr_hom
        (CategoryTheory.Functor.map_comp_assoc
          (DerivedCategory.homologyFunctor (ModuleCat.{u} ch.R') n) _ _ _) m₀)
      (ConcreteCategory.congr_hom hnatd _)
  refine Eq.trans (ch.cohomologyComparisonMap_localRingsSourceMap_eq_germGenerator y w K K' hK φ
    ε' h₁ h₂ n m₀) ?_
  rw [RingTheory.TorIndependence.cohomologyComparisonMap_eq (R₁ := ToType ch.R)
      (R₂ := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
      ((affineDerivedSections ch.incU).obj K) ((derivedStalkFunctor (ch.incU' y)).obj K') _ n,
    houter,
    RingTheory.TorIndependence.cohomologyComparisonMap_eq (R₁ := ToType ch.R)
      (R₂ := ToType ch.R') ((affineDerivedSections ch.incU).obj K)
      ((affineDerivedSections ch.incU').obj K') _ n,
    htop]
  refine Eq.trans (RingTheory.TorIndependence.squareComparison_pasted_unit_one_tmul
    ch.a.hom ch.b.hom ch.c.hom ch.d.hom (ch.toStalkR' y) (ch.toStalkA' y ε')
    (f'.stalkMap (ch.incU' y)).hom ch.isPushout_hom (ch.toStalkA'_d y ε' h₁ h₂)
    (ch.flat_toStalkR' y) n ((affineDerivedSections ch.incU).obj K)
    ((derivedStalkFunctor (ch.incU' y)).obj K') _ m₀) ?_
  refine Eq.trans (RingTheory.TorIndependence.unit_comp_restrictHomologyIso_apply
    (specGermRingHom ch.A' y) ε' hpflat hε'flat hvflat n
    ((totalDerivedExtensionScalars.{u, u, u} ch.c.hom).functor.obj
      ((affineDerivedSections ch.incU).obj K))
    ((derivedStalkFunctor (ch.incU' y)).obj K') _ _) ?_
  refine Eq.trans (congrArg (fun q =>
    (((ModuleCat.restrictScalars.{u} ε').mapDerivedCategoryHomologyIso n).hom.app
        ((derivedStalkFunctor (ch.incU' y)).obj K')).hom
      (((DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((Spec ch.A').presheaf.stalk y)) n).map q).hom _)) htail) ?_
  refine Eq.trans (congrArg
    (fun q => (((ModuleCat.restrictScalars.{u} ε').mapDerivedCategoryHomologyIso n).hom.app
        ((derivedStalkFunctor (ch.incU' y)).obj K')).hom q)
    (ConcreteCategory.congr_hom
      (CategoryTheory.Functor.map_comp
        (DerivedCategory.homologyFunctor (ModuleCat.{u} ((Spec ch.A').presheaf.stalk y)) n)
        ((totalDerivedExtensionScalars.{u, u, u} (specGermRingHom ch.A' y)).functor.map
          (ch.sectionsBaseChangeMap K ≫ (affineDerivedSections ch.incU').map φ))
        (derivedStalkAffineSectionsRestrictIso ch.incU' y K' hK' ε' h₁ h₂).hom) _)) ?_
  refine Eq.symm (Eq.trans (congrArg
    (fun q => (homologyDerivedStalkAffineSectionsRestrictIso ch.incU' y K' hK' ε' h₁ h₂ n).hom.hom
      ((1 : ToType ((Spec ch.A').presheaf.stalk y))
        ⊗ₜ[ch.A', specGermRingHom ch.A' y] q)) hq) ?_)
  refine Eq.trans (hRIap _) ?_
  exact congrArg
    (fun q => (((ModuleCat.restrictScalars.{u} ε').mapDerivedCategoryHomologyIso n).hom.app
        ((derivedStalkFunctor (ch.incU' y)).obj K')).hom
      (((DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((Spec ch.A').presheaf.stalk y)) n).map
        (derivedStalkAffineSectionsRestrictIso ch.incU' y K' hK' ε' h₁ h₂).hom).hom q))
    (RingTheory.TorIndependence.flatDerivedHomologyIso_inv_app_one_tmul_map
      (specGermRingHom ch.A' y) hpflat n
      (ch.sectionsBaseChangeMap K ≫ (affineDerivedSections ch.incU').map φ)
      ((((ModuleCat.restrictScalars.{u} ch.d.hom).mapDerivedCategoryHomologyIso n).hom.app
            ((totalDerivedExtensionScalars.{u, u, u} ch.c.hom).functor.obj
              ((affineDerivedSections ch.incU).obj K))).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} ch.R') n).map
          ((RingTheory.TorIndependence.squareComparison.{u, u} ch.a.hom ch.b.hom ch.c.hom
              ch.d.hom ch.isPushout_hom).app
            ((affineDerivedSections ch.incU).obj K))).hom m₀)))

/-- **The source bridge's commutation at a chart, under the hypothesis
`hspec : AlgebraicGeometry.BaseChangeChart.SpecCornerComm`.** The comparison of the four local
rings on cohomology, read on the source identification of the cube, is the chart's own comparison
inserted at the germ generator of the `𝒪_{X'}(U')`-localization. -/
public theorem cohomologyComparisonMap_localRingsSourceMap_of_specCorner
    (ch : BaseChangeChart f g f' g') (y : Spec ch.A') (w : g' ≫ f = f' ≫ g)
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (hK : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X.Modules m).obj K).IsQuasicoherent)
    (hK' : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X'.Modules m).obj K').IsQuasicoherent)
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K')
    (ε' : (Spec ch.A').presheaf.stalk y →+* X'.presheaf.stalk (ch.incU' y))
    (h₁ : ∀ x, ε' ((ch.incU'.stalkMap y).hom x) = x)
    (h₂ : ∀ z, (ch.incU'.stalkMap y).hom (ε' z) = z) (n : ℤ)
    (hspec : ch.SpecCornerComm y K hK ε' h₁ h₂) :
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
  ch.cohomologyComparisonMap_localRingsSourceMap_of_corner y w K K' hK hK' φ ε' h₁ h₂ n
    (ch.unit_comp_localTail_of_specCorner y K K' hK hK' φ ε' h₁ h₂ hspec)

/-! ### The chart's target corner, in the generic spelling -/

/-- **The chart's `𝒪_X(U)`-reading of the target corner, in the generic spelling.**
`AlgebraicGeometry.BaseChangeChart.restrictGermDerivedStalkSectionsIso` is
`AlgebraicGeometry.derivedStalkAffineSectionsIso` at the chart's affine open `U` — the derived
stalk at `g' x'` *extended* along the germ comparison — with that extension of scalars replaced
by restriction of scalars along the inverse of the chart's comparison at `U`, the whole
restricted along the germ map and the two restrictions merged. -/
public theorem restrictGermDerivedStalkSectionsIso_eq (ch : BaseChangeChart f g f' g')
    (y : Spec ch.A') (K : DerivedCategory X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent) :
    ch.restrictGermDerivedStalkSectionsIso y K hK =
      (ModuleCat.restrictScalars.{u}
            (specGermRingHom ch.A (Spec.map ch.c y))).mapDerivedCategory.mapIso
          (derivedStalkAffineSectionsIso ch.incU (Spec.map ch.c y) K hK ≪≫
            eqToIso (derivedStalkAffineSections_extend_obj_eq ch.incU (Spec.map ch.c y)
                (g' (ch.incU' y)) (ch.apply_g'_incU' y) K) ≪≫
              (totalDerivedExtensionScalarsIsoRestrict
                  ((X.presheaf.stalkCongr (.of_eq (ch.apply_g'_incU' y))).hom ≫
                    ch.incU.stalkMap (Spec.map ch.c y)).hom (ch.stalkCompAIso y).inv.hom
                  (commRingCatIso_inv_hom_apply (ch.stalkCompAIso y))
                  (commRingCatIso_hom_inv_apply (ch.stalkCompAIso y))).app
                ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) ≪≫
        (RingTheory.TorIndependence.mapDerivedCategoryCompNatIso
          (ModuleCat.restrictScalars.{u} (ch.stalkCompAIso y).inv.hom)
          (ModuleCat.restrictScalars.{u} (specGermRingHom ch.A (Spec.map ch.c y)))
          (ModuleCat.restrictScalars.{u} (ch.toStalkA y))
          (ModuleCat.restrictScalarsComp'.{u} (specGermRingHom ch.A (Spec.map ch.c y))
            (ch.stalkCompAIso y).inv.hom (ch.toStalkA y) rfl).symm).app
          ((derivedStalkFunctor (g' (ch.incU' y))).obj K) :=
  have := ch.isOpenImmersion_incU
  congrArg
    (fun t => (ModuleCat.restrictScalars.{u}
            (specGermRingHom ch.A (Spec.map ch.c y))).mapDerivedCategory.mapIso t ≪≫
      (RingTheory.TorIndependence.mapDerivedCategoryCompNatIso
        (ModuleCat.restrictScalars.{u} (ch.stalkCompAIso y).inv.hom)
        (ModuleCat.restrictScalars.{u} (specGermRingHom ch.A (Spec.map ch.c y)))
        (ModuleCat.restrictScalars.{u} (ch.toStalkA y))
        (ModuleCat.restrictScalarsComp'.{u} (specGermRingHom ch.A (Spec.map ch.c y))
          (ch.stalkCompAIso y).inv.hom (ch.toStalkA y) rfl).symm).app
        ((derivedStalkFunctor (g' (ch.incU' y))).obj K))
    (derivedStalkAffineSectionsCongrIso_eq ch.incU (Spec.map ch.c y) (g' (ch.incU' y))
      (ch.apply_g'_incU' y) K hK (ch.stalkCompAIso y).inv.hom
      (commRingCatIso_inv_hom_apply (ch.stalkCompAIso y))
      (commRingCatIso_hom_inv_apply (ch.stalkCompAIso y)))

/-- **The chart's target corner, read over `𝒪_{X, g' x'}` instead of over
`𝒪_{Spec 𝒪_X(U), Spec(c) y}`.** The unit of the derived change-of-rings adjunction along the germ
map of `𝒪_X(U)`, followed by
`AlgebraicGeometry.BaseChangeChart.restrictGermDerivedStalkSectionsIso`, is the unit along the
chart's own `ch.toStalkA` followed by an explicit morphism
`RΓ(U, K) ⊗ᴸ_{𝒪_X(U)} 𝒪_{X, g' x'} ⟶ K_{g' x'}` — the composition isomorphism of derived
extension of scalars read backwards, then
`AlgebraicGeometry.BaseChangeChart.germDerivedStalkSectionsIso` extended along the comparison at
`U`, then `RingTheory.TorIndependence.restrictScalarsDerivedExtendCompIso` read backwards, then
the merge of the two restrictions of scalars extended, and the counit. -/
public theorem unit_comp_restrictGermDerivedStalkSectionsIso_hom (ch : BaseChangeChart f g f' g')
    (y : Spec ch.A') (K : DerivedCategory X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent) :
    letI := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
    letI := (ch.toStalkA y).toAlgebra
    haveI : IsLocalization (ch.primeComplA y)
        (ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y))) :=
      isLocalization_atPrime_specGermRingHom ch.A (Spec.map ch.c y)
    (RingTheory.TorIndependence.derivedExtendRestrictAdjunction (A := ToType ch.A)
            (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))).unit.app
          ((affineDerivedSections ch.incU).obj K) ≫
        (ch.restrictGermDerivedStalkSectionsIso y K hK).hom =
      (RingTheory.TorIndependence.derivedExtendRestrictAdjunction (A := ToType ch.A)
            (A₂ := ToType (X.presheaf.stalk (g' (ch.incU' y))))).unit.app
          ((affineDerivedSections ch.incU).obj K) ≫
        (ModuleCat.restrictScalars.{u} (ch.toStalkA y)).mapDerivedCategory.map
          ((totalDerivedExtensionScalarsComp.{u, u} (specGermRingHom ch.A (Spec.map ch.c y))
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
                    ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) :=
  let := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
  let := (ch.toStalkA y).toAlgebra
  have : IsLocalization (ch.primeComplA y)
      (ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y))) :=
    isLocalization_atPrime_specGermRingHom ch.A (Spec.map ch.c y)
  RingTheory.TorIndependence.unit_comp_map_restrictScalarsMerge (ch.primeComplA y)
    (ch.stalkCompAIso y).inv.hom
    (RingTheory.TorIndependence.mapDerivedCategoryCompNatIso
      (ModuleCat.restrictScalars.{u} (ch.stalkCompAIso y).inv.hom)
      (ModuleCat.restrictScalars.{u} (specGermRingHom ch.A (Spec.map ch.c y)))
      (ModuleCat.restrictScalars.{u} (ch.toStalkA y))
      (ModuleCat.restrictScalarsComp'.{u} (specGermRingHom ch.A (Spec.map ch.c y))
        (ch.stalkCompAIso y).inv.hom (ch.toStalkA y) rfl).symm)
    ((affineDerivedSections ch.incU).obj K)
    ((derivedStalkFunctor (g' (ch.incU' y))).obj K) (ch.germDerivedStalkSectionsIso y K hK).hom

end BaseChangeChart

end AlgebraicGeometry

end
