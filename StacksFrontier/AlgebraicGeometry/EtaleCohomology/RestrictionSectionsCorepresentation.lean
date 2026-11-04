module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.ExtComparisonInPositiveDegree

/-!
# Restriction of étale cohomology, read on sections over terminal objects

Let `h : Y ⟶ X` be a morphism of schemes. Sections of abelian sheaves on `X.Etale` over a terminal
object `T` are corepresented by the constant sheaf `ℤ`, through the adjunction between constant
sheaves and sections over `T`. Restriction on étale cohomology,
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap`, is the map `e ↦ b ∘ h⁻¹(e)` on `Ext`
groups out of `ℤ`, with `b : ℤ_Y ⟶ h⁻¹ℤ_X` the canonical comparison of constant sheaves. This file
identifies, in degree zero, the induced map on corepresented functors
(`Stacks.Cohomology.ExtComparison.derivedSectionsMap`) with restriction of sections: the
adjunction unit `P ⟶ h_*h⁻¹P` read over `T`, followed by restriction along a morphism
`T' ⟶ T ×_X Y` from a terminal object of `Y.Etale`.

## Main definitions

* `Stacks.EtaleCohomology.sectionsCorepresentation`: sections over a terminal object are
  corepresented by the constant sheaf `ℤ`.
* `Stacks.EtaleCohomology.sectionsRestriction`: the restriction of sections along `h`.

## Main results

* `Stacks.EtaleCohomology.derivedSectionsMap_eq_sectionsRestriction`: in degree zero, the map
  on corepresented functors induced by `ℤ_Y ⟶ h⁻¹ℤ_X` is restriction of sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

/-- **The unit of the constant-sheaf adjunction is compatible with restriction between terminal
objects**: for terminal objects `T₁`, `T₂` and `k : T₂ ⟶ T₁`, the unit at `T₁` followed by
restriction along `k` is the unit at `T₂`. -/
theorem constantSheafAdj_unit_app_comp_map {C : Type*} [Category C] (J : GrothendieckTopology C)
    (D : Type*) [Category D] [HasWeakSheafify J D] {T₁ T₂ : C} (hT₁ : IsTerminal T₁)
    (hT₂ : IsTerminal T₂) (k : T₂ ⟶ T₁) (x : D) :
    (constantSheafAdj J D hT₁).unit.app x ≫ ((constantSheaf J D).obj x).obj.map k.op =
      (constantSheafAdj J D hT₂).unit.app x := by
  have h := (toSheafify J ((Functor.const Cᵒᵖ).obj x)).naturality k.op
  simp only [constantSheafAdj, Adjunction.comp_unit_app, constantPresheafAdj_unit_app,
    Functor.comp_obj, Functor.id_obj, evaluation_obj_map]
  simp only [Category.id_comp, sheafificationAdjunction_unit_app]
  exact h.symm.trans (Category.id_comp _)

/-- The constant abelian sheaf `ℤ` on the small étale site. -/
abbrev zSheaf (X : Scheme.{u}) : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- Sections over an object, as a functor on abelian sheaves. -/
abbrev sectionsOver {X : Scheme.{u}} (T : X.Etale) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op T)

/-- Sections over an object of the small étale site form an additive functor. -/
instance {X : Scheme.{u}} (T : X.Etale) : (sectionsOver T).Additive where
  map_add := by intros; rfl

/-- Sections over an object of the small étale site preserve finite limits. -/
instance {X : Scheme.{u}} (T : X.Etale) : PreservesFiniteLimits (sectionsOver T) :=
  preservesFiniteLimits_of_natIso (sheafSectionsNatIsoEvaluation
    (J := X.smallEtaleTopology) (A := AddCommGrpCat.{u + 1}) (X := T)).symm

/-- **Sections over a terminal object are corepresented by the constant sheaf `ℤ`**, through
the adjunction between constant sheaves and sections over `T`. -/
def sectionsCorepresentation {X : Scheme.{u}} {T : X.Etale} (hT : IsTerminal T) :
    sectionsOver T ≅ preadditiveCoyoneda.obj (op (zSheaf X)) :=
  (NatIso.ofComponents (fun F =>
    (((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} hT).homAddEquiv
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) F).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)).toAddCommGrpIso) (by
    intro F G φ
    ext x
    change ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ F) at x
    change ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} hT).homEquiv _ G
        (x ≫ φ)) (ULift.up (1 : ℤ)) =
      φ.hom.app (op T)
        (((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} hT).homEquiv _ F x)
          (ULift.up (1 : ℤ)))
    rw [Adjunction.homEquiv_naturality_right]
    rfl)).symm

section Restriction

variable {X Y : Scheme.{u}} (h : Y ⟶ X)

/-- The canonical comparison `ℤ_Y ⟶ h⁻¹ℤ_X` of constant sheaves. -/
abbrev zComparison : zSheaf Y ⟶ (etaleAbelianInverseImage.{u, 0} h).obj (zSheaf X) :=
  ((etaleAbelianInverseImageConstantIso.{u, 0} h).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv

/-- **Restriction of sections along `h`**, between terminal objects: the adjunction unit
`P ⟶ h_*h⁻¹P` read over `T`, followed by restriction along `k : T' ⟶ T ×_X Y`. -/
def sectionsRestriction {T : X.Etale} {T' : Y.Etale} (k : T' ⟶ (smallEtaleBaseChange h).obj T) :
    sectionsOver T ⟶ etaleAbelianInverseImage.{u, 0} h ⋙ sectionsOver T' where
  app P := ((etaleAbelianInverseImageDirectImageAdj.{u, 0} h).unit.app P).hom.app (op T) ≫
    ((etaleAbelianInverseImage.{u, 0} h).obj P).obj.map k.op
  naturality P Q φ := by
    have hn := congrArg (fun ψ => ψ.hom.app (op T))
      ((etaleAbelianInverseImageDirectImageAdj.{u, 0} h).unit.naturality φ)
    have hk := ((etaleAbelianInverseImage.{u, 0} h).map φ).hom.naturality k.op
    change φ.hom.app (op T) ≫ ((etaleAbelianInverseImageDirectImageAdj.{u, 0} h).unit.app Q).hom.app
        (op T) = ((etaleAbelianInverseImageDirectImageAdj.{u, 0} h).unit.app P).hom.app (op T) ≫
        ((etaleAbelianInverseImage.{u, 0} h).map φ).hom.app
          (op ((smallEtaleBaseChange h).obj T)) at hn
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hn)).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hk.symm).trans
        (Category.assoc _ _ _).symm))

/-- The final object `𝟙 X : X ⟶ X` of the small étale site of `X`. -/
abbrev finalObj (X : Scheme.{u}) : X.Etale :=
  let : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    (HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
      RingHom.Etale.containsIdentities :
        MorphismProperty.IsMultiplicative
          (@Etale : MorphismProperty Scheme.{u})).toContainsIdentities
  MorphismProperty.Over.mk ⊤ (𝟙 X) (by infer_instance)

/-- `finalObj X` is terminal. -/
def finalObj_isTerminal (X : Scheme.{u}) : IsTerminal (finalObj X) :=
  let : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    (HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
      RingHom.Etale.containsIdentities :
        MorphismProperty.IsMultiplicative
          (@Etale : MorphismProperty Scheme.{u})).toContainsIdentities
  MorphismProperty.Over.mkIdTerminal _ _

/-- **The comparison of constant sheaves, on the canonical section.** Read at the final object of
`Y.Etale` that is the base change of the final object of `X.Etale`, the canonical section of
`ℤ_Y` is carried by `ℤ_Y ⟶ h⁻¹ℤ_X` to the restriction along `h` of the canonical section of
`ℤ_X`. -/
theorem unit_comp_zComparison :
    (constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
        ((finalObj_isTerminal X).isTerminalObj (smallEtaleBaseChange h))).unit.app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫
        (zComparison h).hom.app (op ((smallEtaleBaseChange h).obj (finalObj X))) =
      (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
        (finalObj_isTerminal X)).unit.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫
        ((etaleAbelianInverseImageDirectImageAdj.{u, 0} h).unit.app (zSheaf X)).hom.app
          (op (finalObj X)) := by
  let adj1 := (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
    (finalObj_isTerminal X)).comp
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (smallEtaleBaseChange h) AddCommGrpCat.{u + 1} X.smallEtaleTopology Y.smallEtaleTopology)
  let adj2 := constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
        ((finalObj_isTerminal X).isTerminalObj (smallEtaleBaseChange h))
  let Z := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  have hz : (zComparison h).hom.app (op ((smallEtaleBaseChange h).obj (finalObj X))) =
      ((sheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op ((smallEtaleBaseChange h).obj (finalObj X)))).map
        ((adj1.leftAdjointUniq adj2).inv.app Z) := rfl
  have key := Adjunction.unit_leftAdjointUniq_hom_app_assoc adj1 adj2 Z
    (((sheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op ((smallEtaleBaseChange h).obj (finalObj X)))).map
        ((adj1.leftAdjointUniq adj2).inv.app Z))
  have hc : adj1.unit.app Z ≫ ((sheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op ((smallEtaleBaseChange h).obj (finalObj X)))).map
        ((adj1.leftAdjointUniq adj2).hom.app Z) ≫
      ((sheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op ((smallEtaleBaseChange h).obj (finalObj X)))).map
        ((adj1.leftAdjointUniq adj2).inv.app Z) = adj1.unit.app Z :=
    (congrArg (adj1.unit.app Z ≫ ·)
      ((Functor.map_comp ((sheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (op ((smallEtaleBaseChange h).obj (finalObj X)))) _ _).symm.trans
      ((congrArg (((sheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (op ((smallEtaleBaseChange h).obj (finalObj X)))).map) (Iso.hom_inv_id_app _ _)).trans
        (CategoryTheory.Functor.map_id _ _)))).trans (Category.comp_id _)
  have hu : adj1.unit.app Z =
      (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
        (finalObj_isTerminal X)).unit.app Z ≫
        ((etaleAbelianInverseImageDirectImageAdj.{u, 0} h).unit.app (zSheaf X)).hom.app
          (op (finalObj X)) := by
    rw [Adjunction.comp_unit_app]
    rfl
  rw [hz]
  exact key.symm.trans (hc.trans hu)

/-- **The comparison of constant sheaves, on canonical sections**: at terminal objects `T` of
`X.Etale` and `T'` of `Y.Etale` and `k : T' ⟶ T ×_X Y`, the canonical section of `ℤ_Y` over `T'`
is carried by `ℤ_Y ⟶ h⁻¹ℤ_X` to the restriction along `k` of the image under the unit of the
canonical section of `ℤ_X` over `T`. -/
theorem unit_comp_zComparison_of_isTerminal {T : X.Etale} (hT : IsTerminal T) {T' : Y.Etale}
    (hT' : IsTerminal T') (k : T' ⟶ (smallEtaleBaseChange h).obj T) :
    (constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1} hT').unit.app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫ (zComparison h).hom.app (op T') =
      (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} hT).unit.app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫
        ((etaleAbelianInverseImageDirectImageAdj.{u, 0} h).unit.app (zSheaf X)).hom.app (op T) ≫
          ((etaleAbelianInverseImage.{u, 0} h).obj (zSheaf X)).obj.map k.op := by
  let hT₀ := finalObj_isTerminal X
  let hT₀' := hT₀.isTerminalObj (smallEtaleBaseChange h)
  let m : T' ⟶ (smallEtaleBaseChange h).obj (finalObj X) := hT₀'.from T'
  let fT : T ⟶ finalObj X := hT₀.from T
  have h1 := constantSheafAdj_unit_app_comp_map Y.smallEtaleTopology AddCommGrpCat.{u + 1}
    hT₀' hT' m (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  have h2 := constantSheafAdj_unit_app_comp_map X.smallEtaleTopology AddCommGrpCat.{u + 1}
    hT₀ hT fT (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  have hb := (zComparison h).hom.naturality m.op
  have hu := ((etaleAbelianInverseImageDirectImageAdj.{u, 0} h).unit.app (zSheaf X)).hom.naturality
    fT.op
  have hm : k ≫ (smallEtaleBaseChange h).map fT = m := hT₀'.hom_ext _ _
  have e3 : ((etaleAbelianInverseImage.{u, 0} h).obj (zSheaf X)).obj.map
        ((smallEtaleBaseChange h).map fT).op ≫
        ((etaleAbelianInverseImage.{u, 0} h).obj (zSheaf X)).obj.map k.op =
      ((etaleAbelianInverseImage.{u, 0} h).obj (zSheaf X)).obj.map m.op := by
    rw [← Functor.map_comp, ← op_comp, hm]
  have hu' : (zSheaf X).obj.map fT.op ≫
      ((etaleAbelianInverseImageDirectImageAdj.{u, 0} h).unit.app (zSheaf X)).hom.app (op T) ≫
        ((etaleAbelianInverseImage.{u, 0} h).obj (zSheaf X)).obj.map k.op =
      ((etaleAbelianInverseImageDirectImageAdj.{u, 0} h).unit.app (zSheaf X)).hom.app
        (op (finalObj X)) ≫ ((etaleAbelianInverseImage.{u, 0} h).obj (zSheaf X)).obj.map m.op :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ((etaleAbelianInverseImage.{u, 0} h).obj
      (zSheaf X)).obj.map k.op) hu).trans ((Category.assoc _ _ _).trans
        (congrArg (_ ≫ ·) e3)))
  rw [← h1, ← h2, Category.assoc, hb, reassoc_of% (unit_comp_zComparison h)]
  exact (congrArg (_ ≫ ·) hu'.symm).trans (Category.assoc _ _ _).symm |>.symm |>.trans
    (Category.assoc _ _ _) |>.symm

/-- **In degree zero, the `Ext`-side restriction map is restriction of sections.** The map on
corepresented functors induced by `ℤ_Y ⟶ h⁻¹ℤ_X`, for the corepresentations of sections over
terminal objects `T` and `T'`, is `sectionsRestriction h k`. -/
theorem derivedSectionsMap_eq_sectionsRestriction {T : X.Etale} (hT : IsTerminal T)
    {T' : Y.Etale} (hT' : IsTerminal T') (k : T' ⟶ (smallEtaleBaseChange h).obj T) :
    Stacks.Cohomology.ExtComparison.derivedSectionsMap (etaleAbelianInverseImage.{u, 0} h)
        (sectionsOver T') (zSheaf Y) (sectionsCorepresentation hT')
        (sectionsOver T) (zSheaf X) (sectionsCorepresentation hT) (zComparison h) =
      sectionsRestriction h k := by
  ext P x
  let adjT := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} hT
  let adjT' := constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1} hT'
  let Z := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let adjh := etaleAbelianInverseImageDirectImageAdj.{u, 0} h
  let L := etaleAbelianInverseImage.{u, 0} h
  let φ : zSheaf X ⟶ P := ((adjT.homAddEquiv Z P).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv _)).symm x
  have hφ : (adjT.homEquiv Z P φ) (ULift.up (1 : ℤ)) = x :=
    ((adjT.homAddEquiv Z P).trans (AddCommGrpCat.uliftZMultiplesAddEquiv _)).apply_symm_apply x
  have hn := (sectionsRestriction h k).naturality φ
  have hkey := unit_comp_zComparison_of_isTerminal h hT hT' k
  have key2 : adjT'.unit.app Z ≫ (zComparison h ≫ L.map φ).hom.app (op T') =
      adjT.unit.app Z ≫ φ.hom.app (op T) ≫ (adjh.unit.app P).hom.app (op T) ≫
        (L.obj P).obj.map k.op := by
    change adjT'.unit.app Z ≫ (zComparison h).hom.app (op T') ≫ (L.map φ).hom.app (op T') = _
    rw [reassoc_of% hkey]
    exact congrArg (adjT.unit.app Z ≫ ·) hn.symm
  have e1 := ConcreteCategory.congr_hom key2 (ULift.up (1 : ℤ))
  have lhs : ((Stacks.Cohomology.ExtComparison.derivedSectionsMap
        (etaleAbelianInverseImage.{u, 0} h) (sectionsOver T') (zSheaf Y)
        (sectionsCorepresentation hT') (sectionsOver T) (zSheaf X) (sectionsCorepresentation hT)
        (zComparison h)).app P) x =
      (adjT'.homEquiv Z (L.obj P) (zComparison h ≫ L.map φ)) (ULift.up (1 : ℤ)) := rfl
  have rhs : ((sectionsRestriction h k).app P) x =
      ((adjh.unit.app P).hom.app (op T) ≫ (L.obj P).obj.map k.op) x := rfl
  rw [lhs, rhs, ← hφ, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact e1

end Restriction

end Stacks.EtaleCohomology
