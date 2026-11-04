module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsSchemeReadingPullback

/-!
# The unit identifications of an iterated inverse image on the unit section

For morphisms `ι : U ⟶ P` and `π : P ⟶ X` of algebraic spaces, the identification
`(π ∘ ι)^*𝒪_X ≅ ι^*π^*𝒪_X ≅ ι^*𝒪_P ≅ 𝒪_U` assembled from the identifications of Stacks 03LU
(`AlgebraicGeometry.Space.modulePullbackUnitIso`) and the comparison of iterated inverse images
sends the section of `(π ∘ ι)^*𝒪_X` given by the unit function to `1` over every chart of `U`
admitting chart diagrams over `ι` and `π`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U P X : AlgebraicSpaces B S hS} (ι : U ⟶ P) (π : P ⟶ X)

/-- The identification `ι^*𝒪_P ≅ (π ∘ ι)^*𝒪_X` of the unit identification along `π` and the
comparison of iterated inverse images. -/
def modulePullbackUnitCompIso :
    (modulePullback B S hS ι).obj (SheafOfModules.unit (structureRingSheaf B S hS P)) ≅
      (modulePullback B S hS (ι ≫ π)).obj (SheafOfModules.unit (structureRingSheaf B S hS X)) :=
  (modulePullback B S hS ι).mapIso (modulePullbackUnitIso B S hS π).symm ≪≫
    (modulePullbackCompIso B S hS ι π).app (SheafOfModules.unit (structureRingSheaf B S hS X))

/-- The forward map of `AlgebraicGeometry.Space.modulePullbackUnitCompIso` is `ι^*` of the inverse
of the unit identification along `π`, followed by the comparison of iterated inverse images at
`𝒪_X`. -/
theorem modulePullbackUnitCompIso_hom :
    (modulePullbackUnitCompIso ι π).hom =
      (modulePullback B S hS ι).map (modulePullbackUnitIso B S hS π).inv ≫
        (modulePullbackCompIso B S hS ι π).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS X)) :=
  rfl

/-- `AlgebraicGeometry.Space.modulePullbackUnitCompIso` carries the unit section of `ι^*𝒪_P` to
the unit section of `(π ∘ ι)^*𝒪_X`, at a chart with chart diagrams over `ι` and `π`. -/
theorem modulePullbackUnitCompIso_hom_unit {Uc : SmallEtale B S hS U.1} {W : SmallEtale B S hS P.1}
    {V : SmallEtale B S hS X.1}
    (a : (SmallEtale.toOver B S hS U.1).obj Uc ⟶ (SmallEtale.toOver B S hS P.1).obj W)
    (b : (SmallEtale.toOver B S hS P.1).obj W ⟶ (SmallEtale.toOver B S hS X.1).obj V)
    (ha : Uc.1.hom ≫ ι.hom = yoneda.map a ≫ W.1.hom)
    (hb : W.1.hom ≫ π.hom = yoneda.map b ≫ V.1.hom) :
    (modulePullbackUnitCompIso ι π).hom.val.app (op Uc)
        ((modulePullbackUnitIso B S hS ι).inv.val.app (op Uc)
          (1 : (structureRingSheaf B S hS U).obj.obj (op Uc))) =
      (modulePullbackUnitIso B S hS (ι ≫ π)).inv.val.app (op Uc)
        (1 : (structureRingSheaf B S hS U).obj.obj (op Uc)) := by
  have h1 := modulePullbackUnitIso_inv_val_app_one B S hS ι ⟨Uc, W, a, ha⟩
  have h2 := modulePullbackUnitIso_inv_val_app_one B S hS π ⟨W, V, b, hb⟩
  have h3 := modulePullbackChartSection_map B S hS ι (a := (modulePullbackUnitIso B S hS π).inv)
    (d := ⟨Uc, W, a, ha⟩) (s := (1 : (structureRingSheaf B S hS P).obj.obj (op W)))
  have h4 := modulePullbackCompIso_hom_modulePullbackChartSection ι π a b ha hb
    (SheafOfModules.unit (structureRingSheaf B S hS X))
    (1 : (structureRingSheaf B S hS X).obj.obj (op V))
  have h5 := modulePullbackUnitIso_inv_val_app_one B S hS (ι ≫ π)
    (ChartDiagram.comp B S hS ι π a b ha hb)
  rw [h2] at h3
  refine Eq.trans ?_ (h4.trans h5.symm)
  exact congrArg (fun z => ((modulePullbackCompIso B S hS ι π).hom.app
      (SheafOfModules.unit (structureRingSheaf B S hS X))).val.app (op Uc) z)
    ((congrArg (fun z => ((modulePullback B S hS ι).map
      (modulePullbackUnitIso B S hS π).inv).val.app (op Uc) z) h1).trans h3)

/-- **The identification `(π ∘ ι)^*𝒪_X ≅ 𝒪_U` through `ι^*𝒪_P` sends the unit section to `1`**, at
a chart with chart diagrams over `ι` and `π`. -/
theorem modulePullbackUnitCompIso_inv_comp_unitIso_unit {Uc : SmallEtale B S hS U.1}
    {W : SmallEtale B S hS P.1} {V : SmallEtale B S hS X.1}
    (a : (SmallEtale.toOver B S hS U.1).obj Uc ⟶ (SmallEtale.toOver B S hS P.1).obj W)
    (b : (SmallEtale.toOver B S hS P.1).obj W ⟶ (SmallEtale.toOver B S hS X.1).obj V)
    (ha : Uc.1.hom ≫ ι.hom = yoneda.map a ≫ W.1.hom)
    (hb : W.1.hom ≫ π.hom = yoneda.map b ≫ V.1.hom) :
    ((modulePullbackUnitCompIso ι π).inv ≫ (modulePullbackUnitIso B S hS ι).hom).val.app (op Uc)
        ((modulePullbackUnitIso B S hS (ι ≫ π)).inv.val.app (op Uc)
          (1 : (structureRingSheaf B S hS U).obj.obj (op Uc))) =
      (1 : (structureRingSheaf B S hS U).obj.obj (op Uc)) := by
  rw [← modulePullbackUnitCompIso_hom_unit ι π a b ha hb]
  have e1 : ∀ z,
      ((modulePullbackUnitCompIso ι π).inv ≫ (modulePullbackUnitIso B S hS ι).hom).val.app
      (op Uc) ((modulePullbackUnitCompIso ι π).hom.val.app (op Uc) z) =
      (modulePullbackUnitIso B S hS ι).hom.val.app (op Uc) z := fun z =>
    congrArg (fun k => k.val.app (op Uc) z)
      (Iso.hom_inv_id_assoc (modulePullbackUnitCompIso ι π) (modulePullbackUnitIso B S hS ι).hom)
  refine (e1 _).trans ?_
  exact congrArg (fun k => k.val.app (op Uc) (1 : (structureRingSheaf B S hS U).obj.obj (op Uc)))
    (modulePullbackUnitIso B S hS ι).inv_hom_id

end AlgebraicGeometry.Space

end
