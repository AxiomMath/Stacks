module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.GermCohomologyColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedPushforwardStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationDirectedLimit
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.Comparison
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsCohomologyBridge
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stalks of higher direct images

Let `g : T ⟶ S` be a quasi-compact and quasi-separated morphism of schemes, `F` an abelian sheaf
on `T_étale` and `s` a geometric point of `S`. Then

`(R^n g_* F)_s = H^n_étale(T ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)`

where `p : T ×_S Spec(𝒪^{sh}_{S,s}) ⟶ T` is the projection (Stacks 03Q9). The strict
henselization is the limit of the affine étale neighbourhoods `V` of `s`, so the base change
`T ×_S Spec(𝒪^{sh}_{S,s})` is the limit of the quasi-compact and quasi-separated schemes
`T ×_S V`; étale cohomology commutes with such limits (Stacks 09YQ), and the stalk of
`R^n g_* F` is the colimit over the same neighbourhoods of `H^n(T ×_S V, F)`.

## Main definitions

* `AlgebraicGeometry.strictHenselizationBaseChangeDirectedSystem`: the inverse system of the
  base changes `T ×_S V` along the directed system of affine étale neighbourhoods of `s`.
* `AlgebraicGeometry.strictHenselizationBaseChangeDirectedCone`: the cone on it with vertex
  `T ×_S Spec(𝒪^{sh}_{S,s})`.

## Main results

* `AlgebraicGeometry.strictHenselizationBaseChangeDirectedConeIsLimit`: `T ×_S Spec(𝒪^{sh}_{S,s})`
  is the limit of the `T ×_S V`.

## References

* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### Sections of the inverse image along an étale morphism -/

section EtaleSections

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- The morphism of étale objects over `X` from `U` (with structure morphism `j`) to itself
obtained from the canonical morphism into the base change of `U` along `j` followed by the
projection is an isomorphism, its underlying morphism of schemes being the identity. -/
theorem isIso_map_smallEtaleBaseChangeLift_comp_counit :
    IsIso ((Scheme.Etale.smallEtaleCompose j).map
        (smallEtaleBaseChangeLift j (Scheme.Etale.mk j) (𝟙 U) (Category.id_comp _)) ≫
      (Scheme.Etale.smallEtaleComposeBaseChangeAdj j).counit.app (Scheme.Etale.mk j)) := by
  let e : (Scheme.Etale.smallEtaleCompose j).obj (Scheme.Etale.mk (𝟙 U)) ≅ Scheme.Etale.mk j :=
    MorphismProperty.Over.isoMk (Iso.refl U) (by simp)
  have he : (Scheme.Etale.smallEtaleCompose j).map
        (smallEtaleBaseChangeLift j (Scheme.Etale.mk j) (𝟙 U) (Category.id_comp _)) ≫
      (Scheme.Etale.smallEtaleComposeBaseChangeAdj j).counit.app (Scheme.Etale.mk j) = e.hom := by
    apply MorphismProperty.Over.Hom.ext
    exact pullback.lift_fst _ _ _
  rw [he]
  infer_instance

/-- **Sections of the inverse image along an étale morphism.** For an étale morphism `j : U ⟶ X`,
restriction of sections of an abelian sheaf `F` over `U`, as an object of the small étale site of
`X`, to global sections of its inverse image along `j` is an isomorphism `F(U) ≅ Γ(U, j⁻¹F)`. -/
theorem isIso_smallEtaleSectionsPullbackAb_self (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    IsIso ((smallEtaleSectionsPullbackAb j (Scheme.Etale.mk j) (𝟙 U)
      (Category.id_comp _)).app F) := by
  let adj2 := (Scheme.Etale.smallEtaleComposeBaseChangeAdj j).sheafPushforwardContinuous
    (E := Ab.{u + 1}) (smallEtaleTopology U) (smallEtaleTopology X)
  let lift := smallEtaleBaseChangeLift j (Scheme.Etale.mk j) (𝟙 U) (Category.id_comp _)
  have hu := congrArg (fun φ => φ.hom.app (op (Scheme.Etale.mk j)))
    (Adjunction.unit_leftAdjointUniq_hom_app (smallEtaleAdjunctionAb j) adj2 F)
  have hu2 : (adj2.unit.app F).hom.app (op (Scheme.Etale.mk j)) =
      F.obj.map ((Scheme.Etale.smallEtaleComposeBaseChangeAdj j).counit.app
        (Scheme.Etale.mk j)).op := by
    simp [adj2, Adjunction.sheafPushforwardContinuous]
    rfl
  have key : (Stacks.Sites.sectionsPullbackComparison (smallEtaleBaseChange j) Ab.{u + 1}
        (smallEtaleTopology X) (smallEtaleTopology U) (smallEtaleAdjunctionAb j) lift).app F ≫
      ((smallEtalePullbackAbIsoEtaleRestriction j).hom.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 U))) =
      F.obj.map ((Scheme.Etale.smallEtaleCompose j).map lift ≫
        (Scheme.Etale.smallEtaleComposeBaseChangeAdj j).counit.app (Scheme.Etale.mk j)).op := by
    have hnat := ((smallEtalePullbackAbIsoEtaleRestriction j).hom.app F).hom.naturality lift.op
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) hnat).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) hu).trans ?_
    refine (congrArg (· ≫ _) hu2).trans ?_
    exact (F.obj.map_comp _ _).symm
  have hiso : IsIso ((Stacks.Sites.sectionsPullbackComparison (smallEtaleBaseChange j) Ab.{u + 1}
      (smallEtaleTopology X) (smallEtaleTopology U) (smallEtaleAdjunctionAb j) lift).app F) := by
    have h3 : IsIso ((Stacks.Sites.sectionsPullbackComparison (smallEtaleBaseChange j) Ab.{u + 1}
        (smallEtaleTopology X) (smallEtaleTopology U) (smallEtaleAdjunctionAb j) lift).app F ≫
      ((smallEtalePullbackAbIsoEtaleRestriction j).hom.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 U)))) := by
      rw [key]
      have h4 : IsIso ((Scheme.Etale.smallEtaleCompose j).map lift ≫
          (Scheme.Etale.smallEtaleComposeBaseChangeAdj j).counit.app (Scheme.Etale.mk j)) :=
        isIso_map_smallEtaleBaseChangeLift_comp_counit j
      exact Iso.isIso_hom (F.obj.mapIso (asIso ((Scheme.Etale.smallEtaleCompose j).map lift ≫
          (Scheme.Etale.smallEtaleComposeBaseChangeAdj j).counit.app (Scheme.Etale.mk j))).op)
    exact IsIso.of_isIso_comp_right _ (((smallEtalePullbackAbIsoEtaleRestriction j).hom.app
      F).hom.app (op (Scheme.Etale.mk (𝟙 U))))
  unfold smallEtaleSectionsPullbackAb
  exact IsIso.comp_isIso' hiso inferInstance

end EtaleSections

/-! ### Pulling back restrictions of sections in degree zero -/

section DegreeZero

/-- Identities are étale, so the identity is the final object of a small étale site. -/
local instance : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
  ⟨fun _ => inferInstance⟩

variable {X Y Z : Scheme.{u}} (h : X ⟶ Y) (ι : Y ⟶ Z) (gf : X ⟶ Z) (hgf : gf = h ≫ ι)
  (H : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (W : Z.Etale) (r : Y ⟶ W.left)
  (hr : r ≫ W.hom = ι)

/-- The restriction of a section of `H` over an étale object `W` to the identity object of the
small étale site of `Y`, along a morphism `r : Y ⟶ W` lying over `ι : Y ⟶ Z`: a global section
of `ι⁻¹H`, read on the identity object. -/
abbrev sectionsRestrictionAlong : H.obj.obj (op W) ⟶
    ((smallEtalePullbackAb ι).obj H).obj.obj (op (Scheme.Etale.mk (𝟙 Y))) :=
  (Stacks.Sites.sectionsPullbackComparison (smallEtaleBaseChange ι) Ab.{u + 1}
    (smallEtaleTopology Z) (smallEtaleTopology Y) (smallEtaleAdjunctionAb ι)
    (smallEtaleBaseChangeLift ι W r hr)).app H

include hgf hr in
/-- The composite of a morphism into an étale object with a morphism into its source lies over
the composite. -/
theorem comp_hom_eq_of_hom_eq : (h ≫ r) ≫ W.hom = gf := by
  rw [Category.assoc, hr, hgf]

/-- **Pulling back the restriction of a section in degree zero.** Read as a degree-zero
cohomology class of `ι⁻¹H` on `Y`, the restriction of a section `σ` of `H` over `W` along
`r : Y ⟶ W` pulls back along `h : X ⟶ Y` to the restriction of `σ` along `h ≫ r`. -/
theorem equiv₀_etaleCohomologyPullback_sectionsRestrictionAlong (σ : ToType (H.obj.obj (op W))) :
    Sheaf.H.equiv₀ ((smallEtalePullbackAb gf).obj H) (MorphismProperty.Over.mkIdTerminal _ _)
        (etaleCohomologyPullback h ((smallEtalePullbackAbComp' h ι gf hgf).hom.app H) 0
          ((Sheaf.H.equiv₀ ((smallEtalePullbackAb ι).obj H)
            (MorphismProperty.Over.mkIdTerminal _ _)).symm
            (sectionsRestrictionAlong ι H W r hr σ))) =
      sectionsRestrictionAlong gf H W (h ≫ r) (comp_hom_eq_of_hom_eq h ι gf hgf W r hr) σ := by
  rw [etaleCohomologyPullback_equiv₀, AddEquiv.apply_symm_apply]
  change ((smallEtalePullbackAbComp' h ι gf hgf).hom.app H).hom.app _
      (((smallEtalePullbackAb h).obj ((smallEtalePullbackAb ι).obj H)).obj.map _
        (smallEtalePullbackAbUnitApp h ((smallEtalePullbackAb ι).obj H) _
          (((smallEtalePullbackAb ι).obj H).obj.map (smallEtaleBaseChangeLift ι W r hr).op
            (smallEtalePullbackAbUnitApp ι H W σ)))) =
    ((smallEtalePullbackAb gf).obj H).obj.map
      (smallEtaleBaseChangeLift gf W (h ≫ r) (comp_hom_eq_of_hom_eq h ι gf hgf W r hr)).op
      (smallEtalePullbackAbUnitApp gf H W σ)
  have hnat := ConcreteCategory.congr_hom
    (((smallEtalePullbackAbComp' h ι gf hgf).hom.app H).hom.naturality
      ((smallEtaleBaseChangeFinalIsTerminal h).from (Scheme.Etale.mk (𝟙 X))).op)
    (smallEtalePullbackAbUnitApp h ((smallEtalePullbackAb ι).obj H) _
      (((smallEtalePullbackAb ι).obj H).obj.map (smallEtaleBaseChangeLift ι W r hr).op
        (smallEtalePullbackAbUnitApp ι H W σ)))
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
  refine hnat.trans ?_
  let k' : (smallEtaleBaseChange h).obj (Scheme.Etale.mk (𝟙 Y)) ⟶
      (smallEtaleBaseChange gf).obj W :=
    smallEtaleBaseChangeHomMk gf (pullback.fst (𝟙 Y) h ≫ r) (by
      change (pullback.fst (𝟙 Y) h ≫ r) ≫ W.hom = pullback.snd (𝟙 Y) h ≫ gf
      rw [Category.assoc, hr, hgf, ← Category.assoc, ← pullback.condition, Category.comp_id])
  have hk := pullbackSectionsMap_map_unitApp ι H h gf hgf (smallEtaleBaseChangeLift ι W r hr) σ
    k' (by
      rw [smallEtaleBaseChangeHomMk_left_fst, smallEtaleBaseChangeLift_left]
      exact (congrArg (pullback.fst _ h ≫ ·) (pullback.lift_fst _ _ _)).symm)
  change ((smallEtalePullbackAb gf).obj H).obj.map _
      (pullbackSectionsMap h ι gf hgf H _ _) = _
  rw [hk, presheaf_map_map_apply]
  refine map_eq_map_of_left_fst gf H _ _ ?_ _
  refine Eq.trans ?_ ((congrArg (· ≫ pullback.fst W.hom gf)
    (smallEtaleBaseChangeLift_left gf W (h ≫ r) _)).trans (pullback.lift_fst _ _ _)).symm
  have hs : ((smallEtaleBaseChangeFinalIsTerminal h).from (Scheme.Etale.mk (𝟙 X))).left ≫
      pullback.snd (𝟙 Y) h = 𝟙 X :=
    MorphismProperty.Over.w ((smallEtaleBaseChangeFinalIsTerminal h).from (Scheme.Etale.mk (𝟙 X)))
  have hfrom : ((smallEtaleBaseChangeFinalIsTerminal h).from (Scheme.Etale.mk (𝟙 X))).left ≫
      pullback.fst (𝟙 Y) h = h :=
    ((congrArg (_ ≫ ·) (Category.comp_id (pullback.fst (𝟙 Y) h)).symm).trans
      (congrArg (_ ≫ ·) pullback.condition)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ h) hs).trans (Category.id_comp h)))
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (smallEtaleBaseChangeHomMk_left_fst gf _ _)).trans ?_
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ r) hfrom)

/-- The restriction of a section along `r`, read on the identity object, is the global section
produced by `Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb`. -/
theorem sectionsRestrictionAlong_apply (σ : ToType (H.obj.obj (op W))) :
    sectionsRestrictionAlong ι H W r hr σ =
      ((Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Y) Ab.{u + 1}
        (isTerminalEtaleMkId Y)).hom.app ((smallEtalePullbackAb ι).obj H))
        ((smallEtaleSectionsPullbackAb ι W r hr).app H σ) := by
  change _ = ((Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Y) Ab.{u + 1}
      (isTerminalEtaleMkId Y)).inv.app _ ≫ (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Y)
        Ab.{u + 1} (isTerminalEtaleMkId Y)).hom.app _) (sectionsRestrictionAlong ι H W r hr σ)
  rw [Iso.inv_hom_id_app]
  rfl

/-- The restriction of a section along `r` depends only on `r`. -/
theorem sectionsRestrictionAlong_congr {r' : Y ⟶ W.left} (hr' : r' ≫ W.hom = ι) (e : r = r') :
    sectionsRestrictionAlong ι H W r hr = sectionsRestrictionAlong ι H W r' hr' := by
  subst e
  rfl

/-- Restricting a section along a morphism of étale objects and then along `r` is restricting it
along the composite. -/
theorem sectionsRestrictionAlong_map {V : Z.Etale} (m : W ⟶ V) (hrm : (r ≫ m.left) ≫ V.hom = ι)
    (σ : ToType (H.obj.obj (op V))) :
    sectionsRestrictionAlong ι H W r hr (H.obj.map m.op σ) =
      sectionsRestrictionAlong ι H V (r ≫ m.left) hrm σ := by
  rw [sectionsRestrictionAlong_apply, sectionsRestrictionAlong_apply]
  congr 1
  exact ConcreteCategory.congr_hom (congrArg (fun φ => φ.app H)
    (map_comp_smallEtaleSectionsPullbackAb ι W r m hr hrm)) σ

/-- Restriction of sections along the identity of the source of an étale morphism `j`,
`F(U) ⟶ Γ(U, j⁻¹F)` read on the identity object, is bijective. -/
theorem bijective_sectionsRestrictionAlong_id {U : Scheme.{u}} (j : U ⟶ Z) [Etale j] :
    Function.Bijective (sectionsRestrictionAlong j H (Scheme.Etale.mk j) (𝟙 U)
      (Category.id_comp _)) := by
  have h1 := isIso_smallEtaleSectionsPullbackAb_self j H
  have h2 : IsIso ((Sheaf.ΓNatIsoSheafSections (smallEtaleTopology U) Ab.{u + 1}
      (isTerminalEtaleMkId U)).hom.app ((smallEtalePullbackAb j).obj H)) := inferInstance
  have h3 : IsIso ((smallEtaleSectionsPullbackAb j (Scheme.Etale.mk j) (𝟙 U)
      (Category.id_comp _)).app H ≫ (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology U) Ab.{u + 1}
        (isTerminalEtaleMkId U)).hom.app ((smallEtalePullbackAb j).obj H)) := inferInstance
  have h4 := (ConcreteCategory.isIso_iff_bijective _).1 h3
  have he : (ConcreteCategory.hom (sectionsRestrictionAlong j H (Scheme.Etale.mk j) (𝟙 U)
      (Category.id_comp _)) : _ → _) = ConcreteCategory.hom
        ((smallEtaleSectionsPullbackAb j (Scheme.Etale.mk j) (𝟙 U) (Category.id_comp _)).app H ≫
          (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology U) Ab.{u + 1}
            (isTerminalEtaleMkId U)).hom.app ((smallEtalePullbackAb j).obj H)) := by
    funext σ
    rw [ConcreteCategory.comp_apply]
    exact sectionsRestrictionAlong_apply j H _ _ _ σ
  rw [he]
  exact h4

end DegreeZero

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) {S T : Scheme.{u}} (hS : B.Contains S) (g : T ⟶ S)
  (s : GeometricPoint S)

/-- The directed system of affine étale neighbourhoods of `s`, as schemes over `S`. -/
abbrev etaleNeighborhoodDirectedOverDiagram :
    (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ ⥤ Over S :=
  affineEtaleNeighborhoodDirectedSystem B S hS s ⋙ CategoryOfElements.π _ ⋙
    MorphismProperty.Over.forget _ _ S

/-- The strict henselization as a cone over `S` on the directed system of affine étale
neighbourhoods. -/
def strictHenselizationDirectedOverCone : Cone (etaleNeighborhoodDirectedOverDiagram B hS s) where
  pt := Over.mk (strictHenselizationToBase B S hS s)
  π :=
    { app := fun a => Over.homMk ((strictHenselizationAffineDirectedCone B S hS s).π.app a)
        (strictHenselizationNeighborhoodLift_comp B S hS s _ _)
      naturality := fun a b m => by
        ext
        exact (strictHenselizationAffineDirectedCone B S hS s).π.naturality m }

/-- The base change `T ×_S V` of the affine étale neighbourhoods `V` of the directed system, as
étale schemes over `T`. -/
abbrev strictHenselizationBaseChangeDirectedSystem :
    (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ ⥤ T.Etale :=
  affineEtaleNeighborhoodDirectedSystem B S hS s ⋙ CategoryOfElements.π _ ⋙
    Stacks.EtaleCohomology.smallEtaleBaseChange g

/-- The inverse system of schemes `T ×_S V`, for `V` in the directed system of affine étale
neighbourhoods of `s`. -/
abbrev strictHenselizationBaseChangeDirectedDiagram :
    (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ ⥤ Scheme.{u} :=
  strictHenselizationBaseChangeDirectedSystem B hS g s ⋙ MorphismProperty.Over.forget _ _ T ⋙
    Over.forget T

/-- The lift of a morphism of the directed system of neighbourhoods to the base changes is the
base change of the transition morphism. -/
theorem strictHenselizationBaseChangeDirectedDiagram_map_fst
    {a b : (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ} (m : a ⟶ b) :
    (strictHenselizationBaseChangeDirectedDiagram B hS g s).map m ≫
        pullback.fst (etaleNeighborhoodDirectedObj B S hS s b).hom g =
      pullback.fst (etaleNeighborhoodDirectedObj B S hS s a).hom g ≫
        (etaleNeighborhoodDirectedDiagram B S hS s).map m :=
  smallEtaleBaseChange_map_left_fst g ((affineEtaleNeighborhoodDirectedSystem B S hS s).map m).1

/-- The transition morphisms of the inverse system of the `T ×_S V` commute with the projections to
`T`. -/
theorem strictHenselizationBaseChangeDirectedDiagram_map_snd
    {a b : (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ} (m : a ⟶ b) :
    (strictHenselizationBaseChangeDirectedDiagram B hS g s).map m ≫
        pullback.snd (etaleNeighborhoodDirectedObj B S hS s b).hom g =
      pullback.snd (etaleNeighborhoodDirectedObj B S hS s a).hom g :=
  MorphismProperty.Over.w ((Stacks.EtaleCohomology.smallEtaleBaseChange g).map
    ((affineEtaleNeighborhoodDirectedSystem B S hS s).map m).1)

/-- **`T ×_S Spec(𝒪^{sh}_{S,s})` as a cone on the inverse system of the `T ×_S V`**, with legs
the canonical morphisms `AlgebraicGeometry.strictHenselizationBaseChangeEtaleLift`. -/
def strictHenselizationBaseChangeDirectedCone :
    Cone (strictHenselizationBaseChangeDirectedDiagram B hS g s) where
  pt := strictHenselizationBaseChange B hS g s
  π :=
    { app := fun a => strictHenselizationBaseChangeEtaleLift B hS g s
        (etaleNeighborhoodDirectedObj B S hS s a) (etaleNeighborhoodDirectedPoint B S hS s a)
      naturality := fun a b m => by
        refine (Category.id_comp _).trans (pullback.hom_ext ?_ ?_)
        · refine (pullback.lift_fst _ _ _).trans ?_
          refine Eq.trans ?_ (Category.assoc _ _ _).symm
          refine Eq.trans ?_ (congrArg (_ ≫ ·)
            (strictHenselizationBaseChangeDirectedDiagram_map_fst B hS g s m).symm)
          refine Eq.trans ?_ (Category.assoc _ _ _)
          refine Eq.trans ?_ (congrArg (· ≫ _) (pullback.lift_fst _ _ _).symm)
          refine Eq.trans ?_ (Category.assoc _ _ _).symm
          exact congrArg (_ ≫ ·) (((strictHenselizationAffineDirectedCone B S hS s).π.naturality
            m).symm.trans (Category.id_comp _)).symm
        · refine (pullback.lift_snd _ _ _).trans ?_
          exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
            (strictHenselizationBaseChangeDirectedDiagram_map_snd B hS g s m)).trans
              (pullback.lift_snd _ _ _))).symm }

/-- The cone point of `strictHenselizationBaseChangeDirectedCone` is `T ×_S Spec(𝒪^{sh}_{S,s})`. -/
@[simp]
theorem strictHenselizationBaseChangeDirectedCone_pt :
    (strictHenselizationBaseChangeDirectedCone B hS g s).pt =
      strictHenselizationBaseChange B hS g s :=
  rfl

/-- The leg of `strictHenselizationBaseChangeDirectedCone` at a neighbourhood `V` is the canonical
morphism `T ×_S Spec(𝒪^{sh}_{S,s}) ⟶ T ×_S V`. -/
theorem strictHenselizationBaseChangeDirectedCone_π_app
    (a : (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ) :
    (strictHenselizationBaseChangeDirectedCone B hS g s).π.app a =
      strictHenselizationBaseChangeEtaleLift B hS g s
        (etaleNeighborhoodDirectedObj B S hS s a) (etaleNeighborhoodDirectedPoint B S hS s a) :=
  rfl

/-- The base change along `g` of the directed system of neighbourhoods over `S`, read on
underlying schemes, is the system of the `T ×_S V`. -/
def strictHenselizationBaseChangeDirectedDiagramIso :
    etaleNeighborhoodDirectedOverDiagram B hS s ⋙ Over.pullback g ⋙ Over.forget T ≅
      strictHenselizationBaseChangeDirectedDiagram B hS g s :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun {a b} m => by
    refine (Category.comp_id _).trans ((pullback.hom_ext ?_ ?_).trans (Category.id_comp _).symm)
    · exact (pullback.lift_fst _ _ _).trans
        (strictHenselizationBaseChangeDirectedDiagram_map_fst B hS g s m).symm
    · exact ((pullback.lift_snd _ _ _).trans (Category.comp_id _)).trans
        (strictHenselizationBaseChangeDirectedDiagram_map_snd B hS g s m).symm

/-- **`T ×_S Spec(𝒪^{sh}_{S,s})` is the limit of the base changes `T ×_S V` of the affine étale
neighbourhoods `V` of `s`.** Base change along `g` is a right adjoint on schemes over `S`, and
connected limits of schemes over a base are computed on underlying schemes. -/
@[sga "4 VIII 4.5" "more general"]
def strictHenselizationBaseChangeDirectedConeIsLimit :
    IsLimit (strictHenselizationBaseChangeDirectedCone B hS g s) := by
  haveI : IsConnected (affineEtaleNeighborhoodDirectedIndex B S hS s) := IsFiltered.isConnected _
  haveI : IsConnected (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ := isConnected_op
  have hc : IsLimit ((Over.forget S).mapCone (strictHenselizationDirectedOverCone B hS s)) :=
    strictHenselizationDirectedConeIsLimit B S hS s
  refine (IsLimit.equivOfNatIsoOfIso (strictHenselizationBaseChangeDirectedDiagramIso B hS g s)
    ((Over.pullback g ⋙ Over.forget T).mapCone (strictHenselizationDirectedOverCone B hS s))
    (strictHenselizationBaseChangeDirectedCone B hS g s)
    (Cones.ext (pullbackSymmetry (strictHenselizationToBase B S hS s) g) fun a => ?_)).1
    (isLimitOfPreserves (Over.pullback g ⋙ Over.forget T)
      (isLimitOfReflects (Over.forget S) hc))
  refine ((Category.comp_id _).trans ?_)
  refine (pullback.hom_ext ?_ ?_).symm
  · exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
        (pullbackSymmetry_hom_comp_snd _ _))))).trans (pullback.lift_fst _ _ _).symm
  · exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_snd _ _ _)).trans
      (pullbackSymmetry_hom_comp_fst _ _))).trans
        ((pullback.lift_snd _ _ _).trans (Category.comp_id _)).symm

/-- Each base change `T ×_S V` is quasi-compact when `g` is. -/
instance (a : (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ) [QuasiCompact g] :
    CompactSpace ((strictHenselizationBaseChangeDirectedDiagram B hS g s).obj a) := by
  have : CompactSpace (etaleNeighborhoodDirectedObj B S hS s a).left := inferInstance
  have h : QuasiCompact (pullback.fst (X := (etaleNeighborhoodDirectedObj B S hS s a).left)
      (Y := T) (Z := S) (etaleNeighborhoodDirectedObj B S hS s a).hom g) := inferInstance
  exact @QuasiCompact.compactSpace_of_compactSpace _ (etaleNeighborhoodDirectedObj B S hS s a).left
    (pullback.fst (Z := S) _ g) h this

/-- Each base change `T ×_S V` is quasi-separated when `g` is. -/
instance (a : (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ) [QuasiSeparated g] :
    QuasiSeparatedSpace ((strictHenselizationBaseChangeDirectedDiagram B hS g s).obj a) := by
  have : IsAffine (etaleNeighborhoodDirectedObj B S hS s a).left := inferInstance
  have h : QuasiSeparated (pullback.fst (X := (etaleNeighborhoodDirectedObj B S hS s a).left)
      (Y := T) (Z := S) (etaleNeighborhoodDirectedObj B S hS s a).hom g) := inferInstance
  exact (quasiSeparated_iff_quasiSeparatedSpace
    (Y := (etaleNeighborhoodDirectedObj B S hS s a).left) (pullback.fst (Z := S) _ g)).mp h

/-- The transition morphisms of the inverse system of the `T ×_S V` are affine. -/
instance {a b : (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ} (m : a ⟶ b) :
    IsAffineHom ((strictHenselizationBaseChangeDirectedDiagram B hS g s).map m) := by
  have hb := (IsPullback.of_hasPullback (etaleNeighborhoodDirectedObj B S hS s b).hom g).flip
  have ha := (IsPullback.of_hasPullback (etaleNeighborhoodDirectedObj B S hS s a).hom g).flip
  have hw : (etaleNeighborhoodDirectedDiagram B S hS s).map m ≫
      (etaleNeighborhoodDirectedObj B S hS s b).hom =
        (etaleNeighborhoodDirectedObj B S hS s a).hom :=
    MorphismProperty.Over.w ((affineEtaleNeighborhoodDirectedSystem B S hS s).map m).1
  have hs : IsPullback ((strictHenselizationBaseChangeDirectedDiagram B hS g s).map m ≫
        pullback.snd (etaleNeighborhoodDirectedObj B S hS s b).hom g)
      (pullback.fst (etaleNeighborhoodDirectedObj B S hS s a).hom g) g
      ((etaleNeighborhoodDirectedDiagram B S hS s).map m ≫
        (etaleNeighborhoodDirectedObj B S hS s b).hom) :=
    IsPullback.of_iso ha (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((Category.comp_id _).trans
        ((strictHenselizationBaseChangeDirectedDiagram_map_snd B hS g s m).symm.trans
          (Category.id_comp _).symm))
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans (hw.symm.trans (Category.id_comp _).symm))
  have hsq := IsPullback.of_right hs
    (strictHenselizationBaseChangeDirectedDiagram_map_fst B hS g s m) hb
  exact MorphismProperty.of_isPullback hsq.flip
    (isAffineHom_etaleNeighborhoodDirectedDiagram_map B S hS s m)

/-! ### The stalk of a direct image in degree zero -/

section DegreeZeroStalk

/-- Forgetting the group structure commutes with `u`-filtered colimits of abelian groups one
universe up. -/
local instance : PreservesFilteredColimitsOfSize.{u, u} (forget Ab.{u + 1}) :=
  preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} (forget Ab.{u + 1})

/-- The structure morphism `T ×_S V ⟶ T` of a member of the inverse system of base changes. -/
abbrev strictHenselizationBaseChangeDirectedι
    (a : (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ) :
    (strictHenselizationBaseChangeDirectedDiagram B hS g s).obj a ⟶ T :=
  ((strictHenselizationBaseChangeDirectedSystem B hS g s).obj a).hom

/-- The structure morphism `T ×_S V ⟶ T` is étale. -/
instance (a : (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ) :
    Etale (strictHenselizationBaseChangeDirectedι B hS g s a) :=
  ((strictHenselizationBaseChangeDirectedSystem B hS g s).obj a).prop

/-- The transition morphisms of the inverse system of the `T ×_S V` commute with the structure
morphisms to `T`. -/
theorem strictHenselizationBaseChangeDirectedDiagram_map_ι
    {a b : (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ} (m : a ⟶ b) :
    (strictHenselizationBaseChangeDirectedDiagram B hS g s).map m ≫
        strictHenselizationBaseChangeDirectedι B hS g s b =
      strictHenselizationBaseChangeDirectedι B hS g s a :=
  strictHenselizationBaseChangeDirectedDiagram_map_snd B hS g s m

/-- The leg `T ×_S Spec(𝒪^{sh}_{S,s}) ⟶ T ×_S V` followed by the structure morphism to `T` is the
projection `p`. -/
theorem strictHenselizationBaseChangeDirectedCone_π_app_ι
    (a : (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ) :
    (strictHenselizationBaseChangeDirectedCone B hS g s).π.app a ≫
        strictHenselizationBaseChangeDirectedι B hS g s a =
      strictHenselizationBaseChangeToSource B hS g s :=
  pullback.lift_snd _ _ _

variable [QuasiCompact g] [QuasiSeparated g]

/-- **Stacks 09YQ for the base change to the strict henselization.** The cohomology of the
inverse image of `F` on `T ×_S Spec(𝒪^{sh}_{S,s})` is the colimit of the cohomology of its
inverse images on the `T ×_S V`. -/
theorem isOfCoconeCohomologyColimit_strictHenselizationBaseChange
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (q : ℕ) :
    IsOfCoconeCohomologyColimit (strictHenselizationBaseChangeDirectedι B hS g s)
      (strictHenselizationBaseChangeDirectedDiagram_map_ι B hS g s)
      (strictHenselizationBaseChangeDirectedCone B hS g s)
      (strictHenselizationBaseChangeToSource B hS g s)
      (strictHenselizationBaseChangeDirectedCone_π_app_ι B hS g s) F q :=
  EtaleSheafSystem.isSystemColimit_etaleCohomologyPullback
    (strictHenselizationBaseChangeDirectedConeIsLimit B hS g s) q _ _ _
    (EtaleSheafSystem.isPullbackCocone_ofCocone _ _ _ _ _ F)
    (EtaleSheafSystem.isPullbackColimitPresentation_ofCocone _ _ _ _ _ F)

/-- **The higher cohomology of the inverse image of an injective sheaf on the base change to the
strict henselization vanishes.** It is the colimit of the cohomology of the restrictions of the
injective sheaf to the étale `T`-schemes `T ×_S V`, which are injective. -/
theorem subsingleton_sheafH_strictHenselizationBaseChange_of_injective
    (I : Sheaf (smallEtaleTopology T) Ab.{u + 1}) [Injective I] (q : ℕ) :
    Subsingleton (Sheaf.H.{u + 1}
      ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS g s)).obj I) (q + 1)) := by
  refine ⟨fun y y' => ?_⟩
  have h0 : ∀ y : Sheaf.H.{u + 1}
      ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS g s)).obj I) (q + 1),
      y = 0 := fun y => by
    obtain ⟨a, z, rfl⟩ :=
      (isOfCoconeCohomologyColimit_strictHenselizationBaseChange B hS g s I (q + 1)).exists_eq y
    have : Injective ((smallEtalePullbackAb (strictHenselizationBaseChangeDirectedι B hS g s a)).obj
        I) := (smallEtalePullbackAb _).injective_obj_of_injective inferInstance
    rw [Abelian.Ext.eq_zero_of_injective z]
    exact map_zero _
  rw [h0 y, h0 y']

variable (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})

/-- Identities are étale, so the identity is the final object of a small étale site. -/
local instance : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
  ⟨fun _ => inferInstance⟩

/-- The class in degree zero on `T ×_S V`, for `V` in the directed system, of a section of `F`
over the étale `T`-scheme `T ×_S V`. -/
def strictHenselizationStageClass (a : (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ)
    (σ : ToType (F.obj.obj (op ((strictHenselizationBaseChangeDirectedSystem B hS g s).obj a)))) :
    Sheaf.H.{u + 1}
      ((smallEtalePullbackAb (strictHenselizationBaseChangeDirectedι B hS g s a)).obj F) 0 :=
  (Sheaf.H.equiv₀ ((smallEtalePullbackAb (strictHenselizationBaseChangeDirectedι B hS g s a)).obj F)
    (MorphismProperty.Over.mkIdTerminal _ _)).symm
    (sectionsRestrictionAlong (strictHenselizationBaseChangeDirectedι B hS g s a) F
      ((strictHenselizationBaseChangeDirectedSystem B hS g s).obj a) (𝟙 _) (Category.id_comp _) σ)

omit [QuasiCompact g] [QuasiSeparated g] in
/-- The classes of sections at the stages are compatible with the transition maps. -/
theorem etaleCohomologyPullback_strictHenselizationStageClass
    {a b : (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ} (m : b ⟶ a)
    (σ : ToType (F.obj.obj (op ((strictHenselizationBaseChangeDirectedSystem B hS g s).obj a)))) :
    etaleCohomologyPullback ((strictHenselizationBaseChangeDirectedDiagram B hS g s).map m)
        ((EtaleSheafSystem.ofCocone (strictHenselizationBaseChangeDirectedι B hS g s)
          (strictHenselizationBaseChangeDirectedDiagram_map_ι B hS g s) F).map m) 0
        (strictHenselizationStageClass B hS g s F a σ) =
      strictHenselizationStageClass B hS g s F b
        (F.obj.map ((strictHenselizationBaseChangeDirectedSystem B hS g s).map m).op σ) := by
  apply (Sheaf.H.equiv₀
    ((smallEtalePullbackAb (strictHenselizationBaseChangeDirectedι B hS g s b)).obj F)
    (MorphismProperty.Over.mkIdTerminal _ _)).injective
  refine (equiv₀_etaleCohomologyPullback_sectionsRestrictionAlong _ _ _
    (strictHenselizationBaseChangeDirectedDiagram_map_ι B hS g s m).symm F _ _ _ σ).trans ?_
  refine Eq.trans ?_ (AddEquiv.apply_symm_apply _ _).symm
  refine Eq.trans ?_ (sectionsRestrictionAlong_map _ F _ (𝟙 _) (Category.id_comp _) _
    (by rw [Category.id_comp]; exact MorphismProperty.Over.w _) σ).symm
  exact ConcreteCategory.congr_hom (sectionsRestrictionAlong_congr _ F _ _ _ _
    ((Category.comp_id _).trans (Category.id_comp _).symm)) σ

omit [QuasiCompact g] [QuasiSeparated g] in
/-- In degree zero, the class at a stage of a section pulls back to `T ×_S Spec(𝒪^{sh}_{S,s})` to
the restriction of the section along the canonical morphism into the stage. -/
theorem equiv₀_etaleCohomologyPullback_strictHenselizationStageClass
    (a : (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ)
    (σ : ToType (F.obj.obj (op ((strictHenselizationBaseChangeDirectedSystem B hS g s).obj a)))) :
    Sheaf.H.equiv₀ ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS g s)).obj F)
        (MorphismProperty.Over.mkIdTerminal _ _)
        (etaleCohomologyPullback ((strictHenselizationBaseChangeDirectedCone B hS g s).π.app a)
          (EtaleSheafSystem.ofCoconeLeg (strictHenselizationBaseChangeDirectedι B hS g s)
            (strictHenselizationBaseChangeDirectedDiagram_map_ι B hS g s)
            (strictHenselizationBaseChangeDirectedCone B hS g s)
            (strictHenselizationBaseChangeToSource B hS g s)
            (strictHenselizationBaseChangeDirectedCone_π_app_ι B hS g s) F a) 0
          (strictHenselizationStageClass B hS g s F a σ)) =
      sectionsRestrictionAlong (strictHenselizationBaseChangeToSource B hS g s) F
        ((strictHenselizationBaseChangeDirectedSystem B hS g s).obj a)
        ((strictHenselizationBaseChangeDirectedCone B hS g s).π.app a)
        (strictHenselizationBaseChangeDirectedCone_π_app_ι B hS g s a) σ :=
  (equiv₀_etaleCohomologyPullback_sectionsRestrictionAlong _ _ _
    (strictHenselizationBaseChangeDirectedCone_π_app_ι B hS g s a).symm F _ _ _ σ).trans
      (ConcreteCategory.congr_hom (sectionsRestrictionAlong_congr _ F _ _ _ _
        (Category.comp_id _)) σ)

omit [QuasiCompact g] [QuasiSeparated g] in
/-- **The map from the stalk of a direct image on germs over the directed system**: read on the
identity object, the image of the germ of a section over `T ×_S V` is its restriction along the
canonical morphism `T ×_S Spec(𝒪^{sh}_{S,s}) ⟶ T ×_S V`. -/
theorem pushforwardStalkToStrictHenselizationSectionsAb_germ
    (a : (affineEtaleNeighborhoodDirectedIndex B S hS s)ᵒᵖ)
    (σ : ToType (F.obj.obj (op ((strictHenselizationBaseChangeDirectedSystem B hS g s).obj a)))) :
    (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology (strictHenselizationBaseChange B hS g s))
        Ab.{u + 1} (isTerminalEtaleMkId _)).hom.app _
      ((pushforwardStalkToStrictHenselizationSectionsAb B hS g s).app F
        ((Scheme.pointSmallEtale s.hom).toPresheafFiber (etaleNeighborhoodDirectedObj B S hS s a)
          (etaleNeighborhoodDirectedPoint B S hS s a) ((smallEtalePushforwardAb g).obj F).obj σ)) =
      sectionsRestrictionAlong (strictHenselizationBaseChangeToSource B hS g s) F
        ((strictHenselizationBaseChangeDirectedSystem B hS g s).obj a)
        ((strictHenselizationBaseChangeDirectedCone B hS g s).π.app a)
        (strictHenselizationBaseChangeDirectedCone_π_app_ι B hS g s a) σ := by
  have h := ConcreteCategory.congr_hom
    (pushforwardStalkToStrictHenselizationSectionsAb_toPresheafFiber B hS g s
      (etaleNeighborhoodDirectedObj B S hS s a) (etaleNeighborhoodDirectedPoint B S hS s a) F) σ
  refine (congrArg _ ((ConcreteCategory.comp_apply _ _ σ).symm.trans h)).trans ?_
  exact (sectionsRestrictionAlong_apply _ F _ _ _ σ).symm

/-- **Stacks 03Q9 in degree zero.** For `g : T ⟶ S` quasi-compact and quasi-separated, the
canonical map `(g_*F)_s ⟶ Γ(T ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)` is an isomorphism. -/
theorem isIso_pushforwardStalkToStrictHenselizationSectionsAb_app :
    IsIso ((pushforwardStalkToStrictHenselizationSectionsAb B hS g s).app F) := by
  have hcoh := isOfCoconeCohomologyColimit_strictHenselizationBaseChange B hS g s F 0
  let ΓN := (Sheaf.ΓNatIsoSheafSections
    (smallEtaleTopology (strictHenselizationBaseChange B hS g s)) Ab.{u + 1}
    (isTerminalEtaleMkId _)).app
      ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS g s)).obj F)
  let P := (pushforwardStalkToStrictHenselizationSectionsAb B hS g s).app F
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨U, u, σ, rfl⟩ := (Scheme.pointSmallEtale s.hom).toPresheafFiber_jointly_surjective
      (P := ((smallEtalePushforwardAb g).obj F).obj) x
    obtain ⟨a, ⟨k⟩⟩ := exists_etaleNeighborhoodDirectedSystem_hom B S hS s ⟨U, u⟩
    have hk := (Scheme.pointSmallEtale s.hom).toPresheafFiber_w_apply k.1
      (etaleNeighborhoodDirectedPoint B S hS s a)
      ((smallEtalePushforwardAb g).obj F).obj σ
    rw [k.2] at hk
    rw [← hk] at hx ⊢
    set σa := ((smallEtalePushforwardAb g).obj F).obj.map k.1.op σ
    have hx1 : ΓN.hom (P _) = 0 := (congrArg ΓN.hom hx).trans (map_zero _)
    have hx2 := (equiv₀_etaleCohomologyPullback_strictHenselizationStageClass B hS g s F a
      σa).trans ((pushforwardStalkToStrictHenselizationSectionsAb_germ B hS g s F a σa).symm.trans
        hx1)
    have hx3 := (AddEquiv.map_eq_zero_iff _).1 hx2
    obtain ⟨b, m, hm⟩ := IsSystemColimit.exists_eq_zero
      (fun a b => IsOfCoconeCohomologyColimit.transition_comp
        (hg := strictHenselizationBaseChangeDirectedCone_π_app_ι B hS g s) a b)
      (fun a => IsOfCoconeCohomologyColimit.transition_comp_leg a) hcoh
      (strictHenselizationStageClass B hS g s F a σa) hx3
    have hm1 : strictHenselizationStageClass B hS g s F b
        (F.obj.map ((strictHenselizationBaseChangeDirectedSystem B hS g s).map m).op σa) = 0 :=
      (etaleCohomologyPullback_strictHenselizationStageClass B hS g s F m σa).symm.trans hm
    have hσ : F.obj.map ((strictHenselizationBaseChangeDirectedSystem B hS g s).map m).op σa = 0 :=
      (bijective_sectionsRestrictionAlong_id F
        (strictHenselizationBaseChangeDirectedι B hS g s b)).1
        ((((Sheaf.H.equiv₀ ((smallEtalePullbackAb (strictHenselizationBaseChangeDirectedι B hS g s
          b)).obj F) (MorphismProperty.Over.mkIdTerminal _ _)).symm.map_eq_zero_iff).1 hm1).trans
            (map_zero _).symm)
    have hb := (Scheme.pointSmallEtale s.hom).toPresheafFiber_w_apply
      ((affineEtaleNeighborhoodDirectedSystem B S hS s).map m).1
      (etaleNeighborhoodDirectedPoint B S hS s b) ((smallEtalePushforwardAb g).obj F).obj σa
    rw [((affineEtaleNeighborhoodDirectedSystem B S hS s).map m).2] at hb
    exact hb.symm.trans ((congrArg _ hσ).trans (map_zero _))
  · intro t
    obtain ⟨a, z, hz⟩ := hcoh.exists_eq ((Sheaf.H.equiv₀
      ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS g s)).obj F)
      (MorphismProperty.Over.mkIdTerminal _ _)).symm (ΓN.hom t))
    obtain ⟨σ, hσ⟩ := (bijective_sectionsRestrictionAlong_id F
      (strictHenselizationBaseChangeDirectedι B hS g s a)).2
      (Sheaf.H.equiv₀
        ((smallEtalePullbackAb (strictHenselizationBaseChangeDirectedι B hS g s a)).obj F)
        (MorphismProperty.Over.mkIdTerminal _ _) z)
    refine ⟨(Scheme.pointSmallEtale s.hom).toPresheafFiber (etaleNeighborhoodDirectedObj B S hS s a)
      (etaleNeighborhoodDirectedPoint B S hS s a) ((smallEtalePushforwardAb g).obj F).obj σ, ?_⟩
    have hzσ : strictHenselizationStageClass B hS g s F a σ = z :=
      (congrArg (Sheaf.H.equiv₀
        ((smallEtalePullbackAb (strictHenselizationBaseChangeDirectedι B hS g s a)).obj F)
        (MorphismProperty.Over.mkIdTerminal _ _)).symm hσ).trans
          (AddEquiv.symm_apply_apply _ _)
    refine ((ConcreteCategory.isIso_iff_bijective ΓN.hom).1 inferInstance).1 ?_
    refine (pushforwardStalkToStrictHenselizationSectionsAb_germ B hS g s F a σ).trans ?_
    refine
      (equiv₀_etaleCohomologyPullback_strictHenselizationStageClass B hS g s F a σ).symm.trans ?_
    exact (congrArg _ ((congrArg _ hzσ).trans hz)).trans (AddEquiv.apply_symm_apply _ _)

end DegreeZeroStalk

/-! ### The stalks of the higher direct images -/

section HigherDirectImageStalk

open CategoryTheory.Abelian

attribute [local instance] HasDerivedCategory.standard

/-- Identities are étale, so the identity is the final object of a small étale site. -/
local instance : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
  ⟨fun _ => inferInstance⟩

/-- The constant abelian sheaf `ℤ` on the small étale site of a scheme, which étale cohomology is
`Ext` out of. -/
abbrev smallEtaleConstantSheafInt (X : Scheme.{u}) : Sheaf (smallEtaleTopology X) Ab.{u + 1} :=
  (constantSheaf (smallEtaleTopology X) Ab.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))

/-- Global sections of an abelian étale sheaf are its degree-zero étale cohomology, naturally. -/
def smallEtaleGlobalSectionsIsoExtZero (X : Scheme.{u}) :
    Sheaf.Γ (smallEtaleTopology X) Ab.{u + 1} ≅ extFunctorObj (smallEtaleConstantSheafInt X) 0 :=
  NatIso.ofComponents
    (fun G => (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology X) Ab.{u + 1}
      (isTerminalEtaleMkId X)).app G ≪≫
        (Sheaf.H.equiv₀ G (MorphismProperty.Over.mkIdTerminal _ _)).symm.toAddCommGrpIso)
    fun {G G'} φ => by
      ext x
      apply (Sheaf.H.equiv₀ G' (MorphismProperty.Over.mkIdTerminal _ _)).injective
      change Sheaf.H.equiv₀ G' _ ((Sheaf.H.equiv₀ G' _).symm _) =
        Sheaf.H.equiv₀ G' _ (Sheaf.H.map φ 0 ((Sheaf.H.equiv₀ G _).symm _))
      refine (AddEquiv.apply_symm_apply _ _).trans ?_
      refine Eq.trans ?_ (Sheaf.H.equiv₀_naturality _ φ _)
      refine Eq.trans ?_ (congrArg _ (AddEquiv.apply_symm_apply _ _).symm)
      exact ConcreteCategory.congr_hom
        (((Sheaf.ΓNatIsoSheafSections (smallEtaleTopology X) Ab.{u + 1}
          (isTerminalEtaleMkId X)).hom.naturality φ)) x

variable [QuasiCompact g] [QuasiSeparated g]

/-- **The stalks at `s` of the higher direct images along `g`**, `F ↦ (R^n g_* F)_s`, as a
δ-functor: the higher direct images followed by the exact stalk functor. -/
abbrev higherDirectImageStalkDeltaFunctor :
    DeltaFunctor (Sheaf (smallEtaleTopology T) Ab.{u + 1}) Ab.{u + 1} :=
  (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (smallEtalePushforwardAb g)).postcomp (smallEtaleStalkAb s.hom)

/-- **The cohomology of the base change to the strict henselization**,
`F ↦ H^n(T ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)`, as a δ-functor. -/
abbrev strictHenselizationBaseChangeCohomologyDeltaFunctor :
    DeltaFunctor (Sheaf (smallEtaleTopology T) Ab.{u + 1}) Ab.{u + 1} :=
  ModuleSheafCohomology.extDeltaFunctor
    (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS g s))
    (smallEtaleConstantSheafInt (strictHenselizationBaseChange B hS g s))

/-- The identification of the left exact functor `g_*` with its degree-zero right derived
functor. -/
def pushforwardIsoRightDerivedZero :
    smallEtalePushforwardAb g ≅ (smallEtalePushforwardAb g).rightDerived 0 :=
  have : PreservesFiniteLimits (smallEtalePushforwardAb g) :=
    have := (smallEtaleAdjunctionAb g).rightAdjoint_preservesLimits
    inferInstance
  NatIso.ofComponents (fun G => by
      haveI : IsIso (Stacks.RightDerivedPlus.rightDerivedZeroUnit (smallEtalePushforwardAb g) G) :=
        Stacks.RightDerivedPlus.isIso_rightDerivedZeroUnit _ _
      exact asIso (Stacks.RightDerivedPlus.rightDerivedZeroUnit (smallEtalePushforwardAb g) G) ≪≫
        (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) 0).symm.app G)
    fun {G G'} φ => by
      have h1 := Stacks.DerivedFunctor.rightDerivedZeroUnit_naturality
        (smallEtalePushforwardAb g) φ
      have h2 :=
        (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) 0).inv.naturality φ
      change (smallEtalePushforwardAb g).map φ ≫
          (Stacks.RightDerivedPlus.rightDerivedZeroUnit (smallEtalePushforwardAb g) G' ≫
            (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) 0).inv.app G') =
        (Stacks.RightDerivedPlus.rightDerivedZeroUnit (smallEtalePushforwardAb g) G ≫
            (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) 0).inv.app G) ≫
          ((smallEtalePushforwardAb g).rightDerived 0).map φ
      rw [← Category.assoc, h1, Category.assoc, Category.assoc]
      exact congrArg (_ ≫ ·) h2

/-- The degree-zero part of the comparison of Stacks 03Q9:
`(R⁰g_*F)_s ≅ (g_*F)_s ⟶ Γ(T ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)`
`≅ H⁰(T ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)`. -/
def higherDirectImageStalkComparisonZero :
    (higherDirectImageStalkDeltaFunctor g s).functor 0 ⟶
      (strictHenselizationBaseChangeCohomologyDeltaFunctor B hS g s).functor 0 :=
  Functor.whiskerRight (pushforwardIsoRightDerivedZero g).inv (smallEtaleStalkAb s.hom) ≫
    pushforwardStalkToStrictHenselizationSectionsAb B hS g s ≫
      Functor.whiskerLeft (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS g s))
        (smallEtaleGlobalSectionsIsoExtZero (strictHenselizationBaseChange B hS g s)).hom

/-- The δ-functor `F ↦ (R^n g_* F)_s` is universal. -/
instance : (higherDirectImageStalkDeltaFunctor g s).IsUniversal :=
  DeltaFunctor.isUniversal_of_isZero_injective _ fun _ _ _ =>
    (smallEtaleStalkAb s.hom).map_isZero (Functor.isZero_rightDerived_obj_injective_succ _ _ _)

/-- **The comparison of Stacks 03Q9 as a morphism of δ-functors**: the unique morphism of
δ-functors from the stalks of the higher direct images to the cohomology of the base change to the
strict henselization extending the canonical map in degree zero. -/
def higherDirectImageStalkComparison :
    higherDirectImageStalkDeltaFunctor g s ⟶
      strictHenselizationBaseChangeCohomologyDeltaFunctor B hS g s :=
  DeltaFunctor.IsUniversal.lift _ (higherDirectImageStalkComparisonZero B hS g s)

omit [QuasiCompact g] [QuasiSeparated g] in
/-- In degree zero, `higherDirectImageStalkComparison` is
`higherDirectImageStalkComparisonZero`. -/
theorem higherDirectImageStalkComparison_app_zero :
    (higherDirectImageStalkComparison B hS g s).app 0 =
      higherDirectImageStalkComparisonZero B hS g s :=
  DeltaFunctor.IsUniversal.lift_app_zero _ _

/-- For every `n` and every sheaf `F`, the comparison
`(R^n g_* F)_s ⟶ H^n(T ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)` is an isomorphism. -/
instance isIso_higherDirectImageStalkComparison_app (n : ℕ)
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    IsIso (((higherDirectImageStalkComparison B hS g s).app n).app F) := by
  refine DeltaFunctor.isIso_app_of_isIso_app_zero _ (fun G => ?_) (fun G => ?_) n F
  · rw [higherDirectImageStalkComparison_app_zero]
    have := isIso_pushforwardStalkToStrictHenselizationSectionsAb_app B hS g s G
    change IsIso ((smallEtaleStalkAb s.hom).map ((pushforwardIsoRightDerivedZero g).inv.app G) ≫
      _ ≫ ((smallEtaleGlobalSectionsIsoExtZero (strictHenselizationBaseChange B hS g s)).hom.app
        ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS g s)).obj G)))
    infer_instance
  · refine ⟨Injective.under G, Injective.ι G, inferInstance, fun n => ?_, fun n => ?_⟩
    · exact (smallEtaleStalkAb s.hom).map_isZero
        (Functor.isZero_rightDerived_obj_injective_succ _ _ _)
    · have := subsingleton_sheafH_strictHenselizationBaseChange_of_injective B hS g s
        (Injective.under G) n
      exact @AddCommGrpCat.isZero_of_subsingleton _ this

/-- **Stacks 03Q9: the stalks of the higher direct images.** Let `g : T ⟶ S` be a
quasi-compact and quasi-separated morphism of schemes, `F` an abelian sheaf on `T_étale` and `s`
a geometric point of `S`. Then `(R^n g_* F)_s = H^n_étale(T ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)`,
where `p : T ×_S Spec(𝒪^{sh}_{S,s}) ⟶ T` is the projection. The isomorphism is natural in `F`,
compatible with the connecting morphisms (it is the component of
`AlgebraicGeometry.higherDirectImageStalkComparison`), and in degree zero it is the canonical map
`AlgebraicGeometry.pushforwardStalkToStrictHenselizationSectionsAb`. -/
@[stacks 03Q9 "the first assertion: abelian sheaves", sga "4 IX 4.1.1" "more general"]
def higherDirectImageStalkIso (n : ℕ) (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    (smallEtaleStalkAb s.hom).obj (((smallEtalePushforwardAb g).rightDerived n).obj F) ≅
      AddCommGrpCat.of (Sheaf.H.{u + 1}
        ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS g s)).obj F) n) :=
  @asIso _ _ _ _ (((higherDirectImageStalkComparison B hS g s).app n).app F)
    (isIso_higherDirectImageStalkComparison_app B hS g s n F)

end HigherDirectImageStalk

end AlgebraicGeometry
