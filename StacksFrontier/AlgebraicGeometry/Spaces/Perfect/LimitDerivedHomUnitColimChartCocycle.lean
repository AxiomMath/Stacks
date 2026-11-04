module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCompIsoSheafTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomUnitColimPushCocyclePullback
public import StacksFrontier.CategoryTheory.Sites.PushforwardContinuousCalculus
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapComp

/-!
# The composition law for the chart comparison of direct images of sheaves of sets

`AlgebraicGeometry.Space.spacesEtaleModelChartDirectImageIso` is the square of direct images of
sheaves of sets that carries the chart comparison
`AlgebraicGeometry.Space.spacesEtaleModelChartModulesPushforwardIso` of the direct images of
`𝒪`-modules of Stacks 03G1 — the comparison is that square on underlying sheaves of sets,
by `moduleSheafFunctor_map_spacesEtaleModelChartModulesPushforwardIso_hom_app`.  This file
proves that **that square is compatible with composition**.

The square has two factors: restriction along the comparison
`AlgebraicGeometry.Space.smallModelBaseChangeComparison` of the base change of the models with
the spaces-étale base change, and the geometric comparison
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comparison` of Stacks 03G2, part (3).  The
comparison of the base changes is compatible with composition already on the sites
(`AlgebraicGeometry.Space.smallModelBaseChangeComparison_cocycle`), and for the geometric
comparison the composition law is
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_comparison`.

## Main results

* `AlgebraicGeometry.Space.moduleSheafFunctor_map_spacesEtaleModelPushforwardComp_hom_app`: the
  composition isomorphism `AlgebraicGeometry.Space.spacesEtaleModelPushforwardComp` of the
  direct images along the morphisms of models is, **on underlying sheaves of sets**, restriction
  along the composition isomorphism `AlgebraicGeometry.Space.smallModelBaseChangeComp` of the
  base changes.
* `AlgebraicGeometry.Space.smallModelBaseChangeComparison_cocycle` and
  `AlgebraicGeometry.Space.smallModelBaseChangeRestrictionComparison_cocycle`: the comparison of
  the base changes of the models with the spaces-étale base changes is compatible with
  composition, on the sites and on sheaves of sets.
* `AlgebraicGeometry.Space.spacesEtaleModelChartDirectImageIso_cocycle`: **the square of direct
  images of sheaves of sets is compatible with composition**, against
  `AlgebraicGeometry.Space.smallModelBaseChangeComp` on the models and the comparison
  `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` of Stacks 03G2, part (3), on the small
  étale sites.
* `AlgebraicGeometry.Space.spacesEtaleModelChartDirectImageIso_cocycle_moduleSheaf`: the same at
  the underlying sheaf of sets of a module on the model, with every object written as the module
  side writes it.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y Z : AlgebraicSpaces B S hS}

/-- Restriction of sheaves of sets along the composition isomorphism
`AlgebraicGeometry.Space.smallModelBaseChangeComp` of the base changes of the models. -/
abbrev smallModelBaseChangeRestrictionComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallModelBaseChangeRestriction B S hS f ⋙ smallModelBaseChangeRestriction B S hS g ≅
      smallModelBaseChangeRestriction B S hS (f ≫ g) :=
  Functor.sheafPushforwardContinuousIso (smallModelBaseChangeComp B S hS f g) (Type u)
    (smallModelTopology B S hS Z) (smallModelTopology B S hS X)

/-- **The composition isomorphism of the direct images along the morphisms of models is, on
underlying sheaves of sets, restriction along the composition isomorphism of the base changes.**
Both sides are restriction of a section along the same morphism of the model of `X`. -/
theorem moduleSheafFunctor_map_spacesEtaleModelPushforwardComp_hom_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelStructureSheaf B S hS X))) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
        (spacesEtaleModelStructureSheaf B S hS Z))).map
        ((spacesEtaleModelPushforwardComp B S hS f g).hom.app M) =
      (smallModelBaseChangeRestrictionComp B S hS f g).hom.app
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleModelStructureSheaf B S hS X))).obj M) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- The base change of the models, read on the spaces-étale site: the comparison of
`AlgebraicGeometry.Space.smallModelBaseChange` with
`AlgebraicGeometry.Space.spacesBaseChange`. -/
def smallModelBaseChangeComparison (f : X ⟶ Y) :
    (equivSmallModel.{u} (SpacesEtale B S hS Y)).functor ⋙ smallModelBaseChange B S hS f ≅
      (spacesBaseChange B S hS f).functor ⋙
        (equivSmallModel.{u} (SpacesEtale B S hS X)).functor :=
  Functor.isoWhiskerRight (equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.symm
    ((spacesBaseChange B S hS f).functor ⋙ (equivSmallModel.{u} (SpacesEtale B S hS X)).functor)

/-- The comparison `AlgebraicGeometry.Space.spacesEtaleModelChartBaseChangeIso` is the comparison
`AlgebraicGeometry.Space.smallModelBaseChangeComparison` whiskered on the left by the comparison
functor of `Y`. -/
theorem spacesEtaleModelChartBaseChangeIso_eq (f : X ⟶ Y) :
    spacesEtaleModelChartBaseChangeIso B S hS f =
      Functor.isoWhiskerLeft (comparisonFunctor B S hS Y)
        (smallModelBaseChangeComparison B S hS f) :=
  rfl

/-- **The comparison of the base changes of the models with the spaces-étale base changes is
compatible with composition.** -/
theorem smallModelBaseChangeComparison_cocycle (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.isoWhiskerLeft (equivSmallModel.{u} (SpacesEtale B S hS Z)).functor
          (smallModelBaseChangeComp B S hS f g) ≪≫
        smallModelBaseChangeComparison B S hS (f ≫ g) =
      Functor.isoWhiskerRight (smallModelBaseChangeComparison B S hS g)
          (smallModelBaseChange B S hS f) ≪≫
        Functor.isoWhiskerLeft (spacesBaseChange B S hS g).functor
          (smallModelBaseChangeComparison B S hS f) ≪≫
        Functor.isoWhiskerRight (spacesBaseChange_comp B S hS f g)
          (equivSmallModel.{u} (SpacesEtale B S hS X)).functor := by
  refine Iso.ext (NatTrans.ext (funext fun U => ?_))
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  simp only [smallModelBaseChangeComparison, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.comp_map, Functor.comp_obj,
    smallModelBaseChangeComp, NatIso.ofComponents_hom_app, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_inv, Iso.app_hom]
  have hunit := (equivSmallModel.{u} (SpacesEtale B S hS Y)).unitIso.inv.naturality
    ((spacesBaseChange B S hS g).functor.map
      ((equivSmallModel.{u} (SpacesEtale B S hS Z)).unitIso.inv.app U))
  have hsbc := (spacesBaseChange_comp B S hS f g).hom.naturality
    ((equivSmallModel.{u} (SpacesEtale B S hS Z)).unitIso.inv.app U)
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hunit hsbc
  simp only [← Functor.map_comp, Category.assoc]
  congr 1
  rw [← Functor.map_comp_assoc, hunit, Functor.map_comp, Category.assoc, hsbc]

/-! ### The comparison on sheaves of sets -/

/-- Restriction of sheaves of sets along the comparison of a spaces-étale site with its small
model. -/
abbrev smallModelComparisonRestriction (Z : AlgebraicSpaces B S hS) :
    Sheaf (smallModelTopology B S hS Z) (Type u) ⥤
      Sheaf (SpacesEtale.topology B S hS Z) (Type u) :=
  (equivSmallModel.{u} (SpacesEtale B S hS Z)).functor.sheafPushforwardContinuous (Type u)
    (SpacesEtale.topology B S hS Z) (smallModelTopology B S hS Z)

/-- The composition of the equivalence of the spaces-étale site of `Y` with its small model and
the base change of the models along `f` is continuous. -/
instance isContinuous_equivSmallModel_comp_smallModelBaseChange (f : X ⟶ Y) :
    ((equivSmallModel.{u} (SpacesEtale B S hS Y)).functor ⋙
        smallModelBaseChange B S hS f).IsContinuous
      (SpacesEtale.topology B S hS Y) (smallModelTopology B S hS X) :=
  Functor.isContinuous_comp _ _ _ (smallModelTopology B S hS Y) _

/-- The composition of the spaces-étale base change along `f` and the equivalence of the
spaces-étale site of `X` with its small model is continuous. -/
instance isContinuous_spacesBaseChange_comp_equivSmallModel (f : X ⟶ Y) :
    ((spacesBaseChange B S hS f).functor ⋙
        (equivSmallModel.{u} (SpacesEtale B S hS X)).functor).IsContinuous
      (SpacesEtale.topology B S hS Y) (smallModelTopology B S hS X) :=
  Functor.isContinuous_comp _ _ _ (SpacesEtale.topology B S hS X) _

/-- `AlgebraicGeometry.Space.smallModelBaseChangeComparison` on sheaves of sets: the direct
image along the base change of the models, read on the spaces-étale site, is the spaces-étale
direct image. -/
abbrev smallModelBaseChangeRestrictionComparison (f : X ⟶ Y) :
    smallModelBaseChangeRestriction B S hS f ⋙ smallModelComparisonRestriction B S hS Y ≅
      smallModelComparisonRestriction B S hS X ⋙ spacesDirectImage B S hS f :=
  Functor.sheafPushforwardContinuousIso (smallModelBaseChangeComparison B S hS f) (Type u)
    (SpacesEtale.topology B S hS Y) (smallModelTopology B S hS X)

/-- **`AlgebraicGeometry.Space.smallModelBaseChangeComparison_cocycle` on sheaves of sets.** -/
theorem smallModelBaseChangeRestrictionComparison_cocycle (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.isoWhiskerRight (smallModelBaseChangeRestrictionComp B S hS f g)
          (smallModelComparisonRestriction B S hS Z) ≪≫
        smallModelBaseChangeRestrictionComparison B S hS (f ≫ g) =
      Functor.isoWhiskerLeft (smallModelBaseChangeRestriction B S hS f)
          (smallModelBaseChangeRestrictionComparison B S hS g) ≪≫
        Functor.isoWhiskerRight (smallModelBaseChangeRestrictionComparison B S hS f)
          (spacesDirectImage B S hS g) ≪≫
        Functor.isoWhiskerLeft (smallModelComparisonRestriction B S hS X)
          (spacesBaseChange_pushforward_compTypeU B S hS f g) := by
  have : ((equivSmallModel.{u} (SpacesEtale B S hS Z)).functor ⋙
      smallModelBaseChange B S hS g ⋙ smallModelBaseChange B S hS f).IsContinuous
      (SpacesEtale.topology B S hS Z) (smallModelTopology B S hS X) :=
    Functor.isContinuous_comp _ _ _ (smallModelTopology B S hS Z) _
  have : (((equivSmallModel.{u} (SpacesEtale B S hS Z)).functor ⋙
      smallModelBaseChange B S hS g) ⋙ smallModelBaseChange B S hS f).IsContinuous
      (SpacesEtale.topology B S hS Z) (smallModelTopology B S hS X) :=
    Functor.isContinuous_comp _ _ _ (smallModelTopology B S hS Y) _
  have : ((spacesBaseChange B S hS g).functor ⋙
      (equivSmallModel.{u} (SpacesEtale B S hS Y)).functor ⋙
        smallModelBaseChange B S hS f).IsContinuous
      (SpacesEtale.topology B S hS Z) (smallModelTopology B S hS X) :=
    Functor.isContinuous_comp _ _ _ (SpacesEtale.topology B S hS Y) _
  have : (((spacesBaseChange B S hS g).functor ⋙
      (equivSmallModel.{u} (SpacesEtale B S hS Y)).functor) ⋙
        smallModelBaseChange B S hS f).IsContinuous
      (SpacesEtale.topology B S hS Z) (smallModelTopology B S hS X) :=
    Functor.isContinuous_comp _ _ _ (smallModelTopology B S hS Y) _
  have : ((spacesBaseChange B S hS g).functor ⋙
      (spacesBaseChange B S hS f).functor ⋙
        (equivSmallModel.{u} (SpacesEtale B S hS X)).functor).IsContinuous
      (SpacesEtale.topology B S hS Z) (smallModelTopology B S hS X) :=
    Functor.isContinuous_comp _ _ _ (SpacesEtale.topology B S hS Y) _
  have : ((spacesBaseChange B S hS g).functor ⋙
      (spacesBaseChange B S hS f).functor).IsContinuous
      (SpacesEtale.topology B S hS Z) (SpacesEtale.topology B S hS X) :=
    Functor.isContinuous_comp _ _ _ (SpacesEtale.topology B S hS Y) _
  have : (((spacesBaseChange B S hS g).functor ⋙ (spacesBaseChange B S hS f).functor) ⋙
      (equivSmallModel.{u} (SpacesEtale B S hS X)).functor).IsContinuous
      (SpacesEtale.topology B S hS Z) (smallModelTopology B S hS X) :=
    Functor.isContinuous_comp _ _ _ (SpacesEtale.topology B S hS X) _
  have h1 : Functor.isoWhiskerRight (smallModelBaseChangeRestrictionComp B S hS f g)
        (smallModelComparisonRestriction B S hS Z) =
      Functor.sheafPushforwardContinuousIso (Functor.isoWhiskerLeft
        (equivSmallModel.{u} (SpacesEtale B S hS Z)).functor
        (smallModelBaseChangeComp B S hS f g)) (Type u)
        (SpacesEtale.topology B S hS Z) (smallModelTopology B S hS X) :=
    Iso.ext (Functor.whiskerRight_sheafPushforwardContinuousIso_hom _ _ _ _ _ _)
  have h2 : Functor.isoWhiskerLeft (smallModelBaseChangeRestriction B S hS f)
        (smallModelBaseChangeRestrictionComparison B S hS g) =
      Functor.sheafPushforwardContinuousIso (Functor.isoWhiskerRight
        (smallModelBaseChangeComparison B S hS g) (smallModelBaseChange B S hS f)) (Type u)
        (SpacesEtale.topology B S hS Z) (smallModelTopology B S hS X) :=
    Iso.ext (Functor.whiskerLeft_sheafPushforwardContinuousIso_hom _ _ _ _ _ _)
  have h3 : Functor.isoWhiskerRight (smallModelBaseChangeRestrictionComparison B S hS f)
        (spacesDirectImage B S hS g) =
      Functor.sheafPushforwardContinuousIso (Functor.isoWhiskerLeft
        (spacesBaseChange B S hS g).functor (smallModelBaseChangeComparison B S hS f)) (Type u)
        (SpacesEtale.topology B S hS Z) (smallModelTopology B S hS X) :=
    Iso.ext (Functor.whiskerRight_sheafPushforwardContinuousIso_hom _ _ _ _ _ _)
  have h4 : Functor.isoWhiskerLeft (smallModelComparisonRestriction B S hS X)
        (spacesBaseChange_pushforward_compTypeU B S hS f g) =
      Functor.sheafPushforwardContinuousIso (Functor.isoWhiskerRight
        (spacesBaseChange_comp B S hS f g)
        (equivSmallModel.{u} (SpacesEtale B S hS X)).functor) (Type u)
        (SpacesEtale.topology B S hS Z) (smallModelTopology B S hS X) := by
    have hpc : spacesBaseChange_pushforward_compTypeU B S hS f g =
        Functor.sheafPushforwardContinuousIso (spacesBaseChange_comp B S hS f g) (Type u)
          (SpacesEtale.topology B S hS Z) (SpacesEtale.topology B S hS X) :=
      Iso.ext (Functor.sheafPushforwardContinuousComp'_hom_eq _ _ _ _ _)
    rw [hpc]
    exact Iso.ext (Functor.whiskerLeft_sheafPushforwardContinuousIso_hom _ _ _ _ _ _)
  refine Eq.trans ?_ (Eq.trans (congrArg (fun e => Functor.sheafPushforwardContinuousIso e
      (Type u) (SpacesEtale.topology B S hS Z) (smallModelTopology B S hS X))
    (smallModelBaseChangeComparison_cocycle B S hS f g)) ?_)
  · rw [h1, Functor.sheafPushforwardContinuousIso_trans]
    rfl
  · rw [h2, h3, h4, Functor.sheafPushforwardContinuousIso_trans,
      Functor.sheafPushforwardContinuousIso_trans]
    rfl

/-- `AlgebraicGeometry.Space.smallModelBaseChangeRestrictionComparison_cocycle` at a sheaf. -/
theorem smallModelBaseChangeRestrictionComparison_cocycle_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Sheaf (smallModelTopology B S hS X) (Type u)) :
    (smallModelComparisonRestriction B S hS Z).map
          ((smallModelBaseChangeRestrictionComp B S hS f g).hom.app F) ≫
        (smallModelBaseChangeRestrictionComparison B S hS (f ≫ g)).hom.app F =
      (smallModelBaseChangeRestrictionComparison B S hS g).hom.app
          ((smallModelBaseChangeRestriction B S hS f).obj F) ≫
        (spacesDirectImage B S hS g).map
            ((smallModelBaseChangeRestrictionComparison B S hS f).hom.app F) ≫
          (spacesBaseChange_pushforward_compTypeU B S hS f g).hom.app
            ((smallModelComparisonRestriction B S hS X).obj F) := by
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app] using
    congrArg (fun e => e.hom.app F) (smallModelBaseChangeRestrictionComparison_cocycle B S hS f g)

/-! ### The cocycle for the square of direct images of sheaves of sets -/

/-- Restriction of sheaves of sets along the chart of Stacks 03G1. -/
abbrev spacesEtaleModelChartRestriction (Z : AlgebraicSpaces B S hS) :
    Sheaf (smallModelTopology B S hS Z) (Type u) ⥤
      Sheaf (SmallEtale.topology B S hS Z.1) (Type u) :=
  (spacesEtaleModelChart B S hS Z).sheafPushforwardContinuous (Type u)
    (SmallEtale.topology B S hS Z.1) (smallModelTopology B S hS Z)

/-- **The square of direct images of sheaves of sets is the comparison of the base changes,
restricted, followed by the geometric comparison of Stacks 03G2, part (3).** -/
theorem spacesEtaleModelChartDirectImageIso_hom_app (f : X ⟶ Y)
    (F : Sheaf (smallModelTopology B S hS X) (Type u)) :
    (spacesEtaleModelChartDirectImageIso B S hS f).hom.app F =
      (smallEtaleComparisonRestriction B S hS Y).map
          ((smallModelBaseChangeRestrictionComparison B S hS f).hom.app F) ≫
        (smallToposMorphismTypeU_comparison B S hS f).inv.app
          ((smallModelComparisonRestriction B S hS X).obj F) :=
  rfl

/-- Restriction along the chart is restriction along the comparison functor after restriction
along the comparison with the small model. -/
theorem spacesEtaleModelChartRestriction_map (W : AlgebraicSpaces B S hS)
    {F G : Sheaf (smallModelTopology B S hS W) (Type u)} (h : F ⟶ G) :
    (spacesEtaleModelChartRestriction B S hS W).map h =
      (smallEtaleComparisonRestriction B S hS W).map
        ((smallModelComparisonRestriction B S hS W).map h) :=
  rfl

/-- Cancelling an isomorphism off a composite, at an abstract category. -/
private theorem comp_inv_of_comparison {C : Type*} [Category C] {A₁ A₂ A₃ A₄ A₅ : C}
    (dγ : A₁ ⟶ A₂) (dh : A₂ ⟶ A₁) (T : A₂ ⟶ A₃) (hh : A₃ ⟶ A₄) (hi : A₄ ⟶ A₃)
    (v : A₁ ⟶ A₅) (cp : A₅ ⟶ A₄)
    (hid : dγ ≫ dh = 𝟙 A₁) (hiso : hh ≫ hi = 𝟙 A₃)
    (hc : dh ≫ v ≫ cp = T ≫ hh) :
    dγ ≫ T = v ≫ cp ≫ hi := by
  have hT : (dh ≫ v ≫ cp) ≫ hi = T := by
    rw [hc, Category.assoc, hiso, Category.comp_id]
  rw [← hT]
  simp only [Category.assoc]
  rw [← Category.assoc dγ dh, hid, Category.id_comp]

/-- Moving a naturality square past an isomorphism, at an abstract category. -/
private theorem inv_comp_of_naturality {C : Type*} [Category C] {A₁ A₂ A₃ A₄ : C}
    (gi : A₁ ⟶ A₂) (gh : A₂ ⟶ A₁) (n : A₂ ⟶ A₃) (v : A₃ ⟶ A₄) (q : A₁ ⟶ A₄)
    (hid : gi ≫ gh = 𝟙 A₁) (hnat : n ≫ v = gh ≫ q) :
    gi ≫ n ≫ v = q := by
  rw [hnat, ← Category.assoc, hid, Category.id_comp]

/-- The reassociation of the cocycle for the square of direct images, at an abstract pair of
categories: the three composites that have to be fed in are the cocycle for the comparison of
the base changes, the cocycle for the geometric comparison, and one naturality square. -/
private theorem chart_cocycle_aux {C D E : Type*} [Category C] [Category D] [Category E]
    (cz : C ⥤ D) (dg : E ⥤ D)
    {α₀ α₁ β₁ β₂ β₃ : C} {ε₁ ε₂ ε₃ : E} {a₄ : D}
    (k : α₀ ⟶ α₁) (ψ : α₁ ⟶ β₃) (ψ' : α₀ ⟶ β₁) (m : β₁ ⟶ β₂) (p : β₂ ⟶ β₃)
    (s : cz.obj β₃ ⟶ a₄) (t : cz.obj β₁ ⟶ dg.obj ε₁) (w : ε₁ ⟶ ε₂) (x : ε₂ ⟶ ε₃)
    (y : dg.obj ε₃ ⟶ a₄) (v : dg.obj ε₂ ⟶ cz.obj β₂)
    (hψ : k ≫ ψ = ψ' ≫ m ≫ p)
    (h1 : dg.map x ≫ y = v ≫ cz.map p ≫ s)
    (h2 : t ≫ dg.map w ≫ v = cz.map m) :
    cz.map k ≫ cz.map ψ ≫ s = (cz.map ψ' ≫ t) ≫ dg.map (w ≫ x) ≫ y := by
  rw [← Functor.map_comp_assoc, hψ, Functor.map_comp, Functor.map_comp, dg.map_comp]
  simp only [Category.assoc]
  rw [← h2, h1]
  simp only [Category.assoc]

/-- **The square of direct images of sheaves of sets is compatible with composition.** -/
theorem spacesEtaleModelChartDirectImageIso_cocycle (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Sheaf (smallModelTopology B S hS X) (Type u)) :
    (spacesEtaleModelChartRestriction B S hS Z).map
          ((smallModelBaseChangeRestrictionComp B S hS f g).hom.app F) ≫
        (spacesEtaleModelChartDirectImageIso B S hS (f ≫ g)).hom.app F =
      (spacesEtaleModelChartDirectImageIso B S hS g).hom.app
          ((smallModelBaseChangeRestriction B S hS f).obj F) ≫
        (smallToposMorphismTypeU B S hS g).pushforward.map
            ((spacesEtaleModelChartDirectImageIso B S hS f).hom.app F) ≫
          (smallToposMorphismTypeU_comp B S hS f g).hom.app
            ((spacesEtaleModelChartRestriction B S hS X).obj F) := by
  have hnat : (smallToposMorphismTypeU B S hS g).pushforward.map
          ((smallEtaleComparisonRestriction B S hS Y).map
            ((smallModelBaseChangeRestrictionComparison B S hS f).hom.app F)) ≫
        (smallToposMorphismTypeU_comparison B S hS g).hom.app
          ((spacesDirectImage B S hS f).obj
            ((smallModelComparisonRestriction B S hS X).obj F)) =
      (smallToposMorphismTypeU_comparison B S hS g).hom.app
          ((smallModelComparisonRestriction B S hS Y).obj
            ((smallModelBaseChangeRestriction B S hS f).obj F)) ≫
        (smallEtaleComparisonRestriction B S hS Z).map
          ((spacesDirectImage B S hS g).map
            ((smallModelBaseChangeRestrictionComparison B S hS f).hom.app F)) :=
    (smallToposMorphismTypeU_comparison B S hS g).hom.naturality
      ((smallModelBaseChangeRestrictionComparison B S hS f).hom.app F)
  have hc : (smallToposMorphismTypeU B S hS g).pushforward.map
          ((smallToposMorphismTypeU_comparison B S hS f).hom.app
            ((smallModelComparisonRestriction B S hS X).obj F)) ≫
        (smallToposMorphismTypeU_comparison B S hS g).hom.app
            ((spacesDirectImage B S hS f).obj
              ((smallModelComparisonRestriction B S hS X).obj F)) ≫
          (smallEtaleComparisonRestriction B S hS Z).map
            ((spacesBaseChange_pushforward_compTypeU B S hS f g).hom.app
              ((smallModelComparisonRestriction B S hS X).obj F)) =
      (smallToposMorphismTypeU_comp B S hS f g).hom.app
          ((spacesEtaleModelChartRestriction B S hS X).obj F) ≫
        (smallToposMorphismTypeU_comparison B S hS (f ≫ g)).hom.app
          ((smallModelComparisonRestriction B S hS X).obj F) :=
    smallToposMorphismTypeU_comp_comparison B S hS f g
      ((smallModelComparisonRestriction B S hS X).obj F)
  have h1 : (smallToposMorphismTypeU B S hS g).pushforward.map
          ((smallToposMorphismTypeU_comparison B S hS f).inv.app
            ((smallModelComparisonRestriction B S hS X).obj F)) ≫
        (smallToposMorphismTypeU_comp B S hS f g).hom.app
          ((spacesEtaleModelChartRestriction B S hS X).obj F) =
      (smallToposMorphismTypeU_comparison B S hS g).hom.app
          ((spacesDirectImage B S hS f).obj
            ((smallModelComparisonRestriction B S hS X).obj F)) ≫
        (smallEtaleComparisonRestriction B S hS Z).map
            ((spacesBaseChange_pushforward_compTypeU B S hS f g).hom.app
              ((smallModelComparisonRestriction B S hS X).obj F)) ≫
          (smallToposMorphismTypeU_comparison B S hS (f ≫ g)).inv.app
            ((smallModelComparisonRestriction B S hS X).obj F) :=
    comp_inv_of_comparison _ _ _ _ _ _ _
      (by rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id])
      (Iso.hom_inv_id_app _ _) hc
  have h2 : (smallToposMorphismTypeU_comparison B S hS g).inv.app
          ((smallModelComparisonRestriction B S hS Y).obj
            ((smallModelBaseChangeRestriction B S hS f).obj F)) ≫
        (smallToposMorphismTypeU B S hS g).pushforward.map
            ((smallEtaleComparisonRestriction B S hS Y).map
              ((smallModelBaseChangeRestrictionComparison B S hS f).hom.app F)) ≫
          (smallToposMorphismTypeU_comparison B S hS g).hom.app
            ((spacesDirectImage B S hS f).obj
              ((smallModelComparisonRestriction B S hS X).obj F)) =
      (smallEtaleComparisonRestriction B S hS Z).map
        ((spacesDirectImage B S hS g).map
          ((smallModelBaseChangeRestrictionComparison B S hS f).hom.app F)) :=
    inv_comp_of_naturality _ _ _ _ _ (Iso.inv_hom_id_app _ _) hnat
  rw [spacesEtaleModelChartDirectImageIso_hom_app, spacesEtaleModelChartDirectImageIso_hom_app,
    spacesEtaleModelChartDirectImageIso_hom_app, spacesEtaleModelChartRestriction_map]
  exact chart_cocycle_aux (smallEtaleComparisonRestriction B S hS Z)
    (smallToposMorphismTypeU B S hS g).pushforward _ _ _ _ _ _ _ _ _ _ _
    (smallModelBaseChangeRestrictionComparison_cocycle_app B S hS f g F) h1 h2

/-- **The composition isomorphism of the direct images along the morphisms of models, pushed
into the chart functor, is restriction along the composition isomorphism of the base changes.**
-/
theorem moduleSheafFunctor_map_spacesEtaleModelChartModules_map_pushforwardComp (f : X ⟶ Y)
    (g : Y ⟶ Z) (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelStructureSheaf B S hS X))) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z)).map
        ((spacesEtaleModelChartModules B S hS Z).map
          ((spacesEtaleModelPushforwardComp B S hS f g).hom.app M)) =
      (spacesEtaleModelChartRestriction B S hS Z).map
        ((smallModelBaseChangeRestrictionComp B S hS f g).hom.app
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
            (spacesEtaleModelStructureSheaf B S hS X))).obj M)) :=
  congrArg (spacesEtaleModelChartRestriction B S hS Z).map
    (moduleSheafFunctor_map_spacesEtaleModelPushforwardComp_hom_app B S hS f g M)

/-- **`AlgebraicGeometry.Space.spacesEtaleModelChartDirectImageIso_cocycle` at the underlying
sheaf of sets of a module on the model**, with each object written as the module side writes
it. -/
theorem spacesEtaleModelChartDirectImageIso_cocycle_moduleSheaf (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelStructureSheaf B S hS X))) :
    (spacesEtaleModelChartRestriction B S hS Z).map
          ((smallModelBaseChangeRestrictionComp B S hS f g).hom.app
            ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
              (spacesEtaleModelStructureSheaf B S hS X))).obj M)) ≫
        (spacesEtaleModelChartDirectImageIso B S hS (f ≫ g)).hom.app
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
            (spacesEtaleModelStructureSheaf B S hS X))).obj M) =
      (spacesEtaleModelChartDirectImageIso B S hS g).hom.app
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
            (spacesEtaleModelStructureSheaf B S hS Y))).obj
            ((spacesEtaleModelHom B S hS f).pushforwardTopos.obj M)) ≫
        (smallToposMorphismTypeU B S hS g).pushforward.map
            ((spacesEtaleModelChartDirectImageIso B S hS f).hom.app
              ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf
                (spacesEtaleModelStructureSheaf B S hS X))).obj M)) ≫
          (smallToposMorphismTypeU_comp B S hS f g).hom.app
            ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj
              ((spacesEtaleModelChartModules B S hS X).obj M)) :=
  spacesEtaleModelChartDirectImageIso_cocycle B S hS f g _

end AlgebraicGeometry.Space

end
