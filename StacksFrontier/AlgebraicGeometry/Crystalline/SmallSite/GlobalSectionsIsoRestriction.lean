module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ZariskiPushforwardLeray
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CocontinuousGlobalSections

/-!
# The comparisons of global sections of the crystalline sites, read against the restriction maps

The isomorphisms of global sections functors
`Crystalline.GlobalCrystallineSituation.SmallSite.zariskiPushforwardGlobalSectionsIso` (Zariski
direct image), `smallRestrictionGlobalSectionsIso` (restriction to the small crystalline site),
`bigDirectImageGlobalSectionsIso` and `changeBaseDirectImageGlobalSectionsIso` (the two
cocontinuous direct images) and `crisGlobalSectionsIso` (their composite), evaluated against the
restriction maps `CategoryTheory.Sheaf.ΓRes` out of global sections.

## Main results

* `zariskiPushforwardGlobalSectionsIso_hom_app_comp_ΓRes`: the Zariski comparison is the identity
  read through the sections at the terminal open.
* `zariskiGlobalSectionsDirectImageIso_eq`, `bigDirectImageGlobalSectionsIso_eq` and
  `changeBaseDirectImageGlobalSectionsIso_eq`: the three comparisons along a cocontinuous functor
  of sites are the general `Stacks.Sites.cocontinuousGlobalSectionsIso`; with
  `zariskiGlobalSectionsDirectImageIso_hom_app_comp_ΓRes`,
  `bigDirectImageGlobalSectionsIso_hom_app_comp_ΓRes` and
  `changeBaseDirectImageGlobalSectionsIso_hom_app_comp_ΓRes` their evaluations.
* `smallRestrictionGlobalSectionsIso_hom_app_comp_ΓRes` and
  `smallRestrictionGlobalSectionsIso_hom_app_comp_ΓRes_ι`: the restriction factor, at an
  arbitrary object of `CRIS(X/S)` and at one coming from `Cris(X/S)`.
* `crisGlobalSectionsIso_hom_app_comp_ΓRes`: the composite comparison along `f_cris`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S S' : GlobalCrystallineSituation.{u}) (fX : S.X ⟶ S'.X)

/-- The Zariski comparison of global sections is the identity on sections over the top open:
read against `ΓRes` at `⊤` it is the restriction map of `f_{Zar, *}G` to `⊤`. -/
@[reassoc (attr := simp)]
theorem zariskiPushforwardGlobalSectionsIso_hom_app_comp_ΓRes
    (G : Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) :
    (zariskiPushforwardGlobalSectionsIso S S' fX).hom.app G ≫ Sheaf.ΓRes G (op ⊤) =
      Sheaf.ΓRes ((zariskiPushforward S S' fX).obj G) (op ⊤) := by
  change ((Sheaf.ΓNatIsoSheafSections (opensTopology S') AddCommGrpCat.{u + 1}
      (isTerminalTop (α := S'.X.Opens))).hom.app ((zariskiPushforward S S' fX).obj G) ≫
    (Sheaf.ΓNatIsoSheafSections (opensTopology S) AddCommGrpCat.{u + 1}
      (isTerminalTop (α := S.X.Opens))).inv.app G) ≫ _ = _
  refine (Category.assoc _ _ _).trans ?_
  erw [← Sheaf.ΓNatIsoSheafSections_hom_app_general (isTerminalTop (α := S.X.Opens)) G,
    Iso.inv_hom_id_app, Category.comp_id, Sheaf.ΓNatIsoSheafSections_hom_app_general]

/-! ### The three comparisons along a cocontinuous functor of sites -/

/-- The comparison of global sections along `u_{X/S, *}` is the general comparison along a
cocontinuous functor of sites, `Stacks.Sites.cocontinuousGlobalSectionsIso`, for the forgetful
functor of [Stacks, Tag 07IH]. -/
theorem zariskiGlobalSectionsDirectImageIso_eq :
    zariskiGlobalSectionsDirectImageIso S =
      Stacks.Sites.cocontinuousGlobalSectionsIso (forgetToOpens S) AddCommGrpCat.{u + 1}
        (smallTopology S) (opensTopology S) :=
  rfl

/-- `Γ(X_Zar, u_{X/S, *}F) ≅ Γ(Cris(X/S), F)` read against the restriction maps: restricting a
global section of `F` to an object `A` of `Cris(X/S)` is restricting the corresponding global
section of `u_{X/S, *}F` to the open of `X` underlying `A` and then applying the counit of the
Kan extension. -/
theorem zariskiGlobalSectionsDirectImageIso_hom_app_comp_ΓRes
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (A : CrystallineThickening S) :
    (zariskiGlobalSectionsDirectImageIso S).hom.app F ≫ Sheaf.ΓRes F (op A) =
      Sheaf.ΓRes ((zariskiDirectImage S).obj F) (op ((forgetToOpens S).obj A)) ≫
        ((forgetToOpens S).op.ranCounit.app F.obj).app (op A) :=
  Stacks.Sites.cocontinuousGlobalSectionsIso_hom_app_comp_ΓRes F A

/-- The comparison of global sections along `i_{X, *}` is the general comparison along a
cocontinuous functor of sites for the inclusion `Cris(X/S) ⥤ CRIS(X/S)`. -/
theorem bigDirectImageGlobalSectionsIso_eq :
    bigDirectImageGlobalSectionsIso S =
      Stacks.Sites.cocontinuousGlobalSectionsIso (CrystallineThickening.ι S)
        AddCommGrpCat.{u + 1} (smallTopology S) (topology S) :=
  rfl

/-- `Γ(CRIS(X/S), i_{X, *}F) ≅ Γ(Cris(X/S), F)` read against the restriction maps: restricting a
global section of `F` to an object `A` of `Cris(X/S)` is restricting the corresponding global
section of `i_{X, *}F` to `A` viewed in `CRIS(X/S)` and then applying the counit of the Kan
extension. -/
theorem bigDirectImageGlobalSectionsIso_hom_app_comp_ΓRes
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (A : CrystallineThickening S) :
    (bigDirectImageGlobalSectionsIso S).hom.app F ≫ Sheaf.ΓRes F (op A) =
      Sheaf.ΓRes ((bigDirectImage S).obj F) (op ((CrystallineThickening.ι S).obj A)) ≫
        ((CrystallineThickening.ι S).op.ranCounit.app F.obj).app (op A) :=
  Stacks.Sites.cocontinuousGlobalSectionsIso_hom_app_comp_ΓRes F A

/-! ### The restriction factor -/

/-- `Γ(Cris(X/S), i_X^{-1}G) ≅ Γ(CRIS(X/S), G)` read against the restriction maps: the
restriction of a global section of `G` to an object `B` of `CRIS(X/S)` is read off the limit over
`Cris(X/S)` by the glued section `restrictionConeπ`, the leg at `B` of the cone
`restrictionCone`. -/
theorem smallRestrictionGlobalSectionsIso_hom_app_comp_ΓRes
    (G : Sheaf (topology S) AddCommGrpCat.{u + 1}) (B : Thickening S) :
    (smallRestrictionGlobalSectionsIso (S := S)).hom.app G ≫ Sheaf.ΓRes G (op B) =
      (Sheaf.ΓNatIsoLim (smallTopology S) AddCommGrpCat.{u + 1}).hom.app
          ((smallRestriction S).obj G) ≫ restrictionConeπ G (op B) := by
  have key : (Sheaf.ΓNatIsoLim (topology S) AddCommGrpCat.{u + 1}).inv.app G ≫
      Sheaf.ΓRes G (op B) = limit.π G.obj (op B) := by
    rw [← Sheaf.ΓNatIsoLim_hom_app_comp_π G (op B), ← Category.assoc, Iso.inv_hom_id_app,
      Category.id_comp]
  have h : restrictionInv G ≫ limit.pre G.obj (CrystallineThickening.ι S).op = 𝟙 _ :=
    limit.hom_ext fun A ↦ by
      rw [Category.assoc, limit.pre_π, Category.id_comp]
      exact restrictionInv_π G A.unop
  have hinv : (restrictionLimIso (S := S)).inv.app G = restrictionInv G := by
    simp only [restrictionLimIso, NatIso.ofComponents_inv_app]
    exact @IsIso.inv_eq_of_inv_hom_id _ _ _ _ _ (isIso_limitPre_ι G) _ h
  have hπ : (restrictionLimIso (S := S)).inv.app G ≫ limit.π G.obj (op B) =
      restrictionConeπ G (op B) :=
    (congrArg (fun z ↦ z ≫ limit.π G.obj (op B)) hinv).trans
      (limit.lift_π (restrictionCone G) (op B))
  simp [smallRestrictionGlobalSectionsIso, key, hπ]

/-- The restriction factor at an object of `Cris(X/S)`: restricting a global section of `G` to an
object `A` of the small crystalline site is restricting the corresponding global section of
`i_X^{-1}G` to `A`. -/
theorem smallRestrictionGlobalSectionsIso_hom_app_comp_ΓRes_ι
    (G : Sheaf (topology S) AddCommGrpCat.{u + 1}) (A : CrystallineThickening S) :
    (smallRestrictionGlobalSectionsIso (S := S)).hom.app G ≫
        Sheaf.ΓRes G (op ((CrystallineThickening.ι S).obj A)) =
      Sheaf.ΓRes ((smallRestriction S).obj G) (op A) :=
  (smallRestrictionGlobalSectionsIso_hom_app_comp_ΓRes S G
      ((CrystallineThickening.ι S).obj A)).trans
    ((congrArg (fun z ↦ (Sheaf.ΓNatIsoLim (smallTopology S) AddCommGrpCat.{u + 1}).hom.app
          ((smallRestriction S).obj G) ≫ z) (restrictionConeπ_ι G A)).trans
      (Sheaf.ΓNatIsoLim_hom_app_comp_π ((smallRestriction S).obj G) (op A)))

variable (fS : S.S ⟶ S'.S)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)

/-- The comparison of global sections along `f_{CRIS, *}` is the general comparison along a
cocontinuous functor of sites for change of divided power base, [Stacks, Tag 07IC]. -/
theorem changeBaseDirectImageGlobalSectionsIso_eq :
    changeBaseDirectImageGlobalSectionsIso S S' fS fX hf =
      Stacks.Sites.cocontinuousGlobalSectionsIso (changeBase S S' fS fX hf)
        AddCommGrpCat.{u + 1} (topology S) (topology S') :=
  rfl

/-- `Γ(CRIS(X'/S'), f_{CRIS, *}G) ≅ Γ(CRIS(X/S), G)` read against the restriction maps:
restricting a global section of `G` to an object `B` of `CRIS(X/S)` is restricting the
corresponding global section of `f_{CRIS, *}G` to the image of `B` under change of base and then
applying the counit of the Kan extension. -/
theorem changeBaseDirectImageGlobalSectionsIso_hom_app_comp_ΓRes
    (G : Sheaf (topology S) AddCommGrpCat.{u + 1}) (B : Thickening S) :
    (changeBaseDirectImageGlobalSectionsIso S S' fS fX hf).hom.app G ≫ Sheaf.ΓRes G (op B) =
      Sheaf.ΓRes ((changeBaseDirectImage S S' fS fX hf).obj G)
          (op ((changeBase S S' fS fX hf).obj B)) ≫
        ((changeBase S S' fS fX hf).op.ranCounit.app G.obj).app (op B) :=
  Stacks.Sites.cocontinuousGlobalSectionsIso_hom_app_comp_ΓRes G B

/-! ### The composite comparison along `f_cris` -/

/-- `Γ(Cris(X/S), f_{cris, *}F) ≅ Γ(Cris(X'/S), F)` read against the restriction maps: the
restriction of a global section to an object `A` of `Cris(X/S)` is the glued section
`restrictionConeπ` of `restrictionCone` at the image of `A` under change of base, followed by
the counits of the Kan extensions along change of divided power base and along the inclusion
`Cris(X/S) ⥤ CRIS(X/S)`. -/
theorem crisGlobalSectionsIso_hom_app_comp_ΓRes
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (A : CrystallineThickening S) :
    (crisGlobalSectionsIso S S' fS fX hf).hom.app F ≫ Sheaf.ΓRes F (op A) =
      (Sheaf.ΓNatIsoLim (smallTopology S') AddCommGrpCat.{u + 1}).hom.app
            ((smallRestriction S').obj
              ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj F))) ≫
          restrictionConeπ ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj F))
            (op ((changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A))) ≫
        ((changeBase S S' fS fX hf).op.ranCounit.app ((bigDirectImage S).obj F).obj).app
            (op ((CrystallineThickening.ι S).obj A)) ≫
          ((CrystallineThickening.ι S).op.ranCounit.app F.obj).app (op A) := by
  have h4 := bigDirectImageGlobalSectionsIso_hom_app_comp_ΓRes S F A
  have h3 := changeBaseDirectImageGlobalSectionsIso_hom_app_comp_ΓRes S S' fX fS hf
    ((bigDirectImage S).obj F) A.obj
  have h1 := smallRestrictionGlobalSectionsIso_hom_app_comp_ΓRes S'
    ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj F))
    ((changeBase S S' fS fX hf).obj A.obj)
  show (Functor.isoWhiskerLeft (bigDirectImage S ⋙ changeBaseDirectImage S S' fS fX hf)
        (smallRestrictionGlobalSectionsIso (S := S')) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (bigDirectImage S)
        (changeBaseDirectImageGlobalSectionsIso S S' fS fX hf) ≪≫
      bigDirectImageGlobalSectionsIso S).hom.app F ≫ Sheaf.ΓRes F (op A) = _
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.comp_obj, Category.id_comp,
    Category.assoc, ObjectProperty.ι_obj, h4]
  have step :
      (smallRestrictionGlobalSectionsIso (S := S')).hom.app
          ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj F)) ≫
        ((changeBaseDirectImageGlobalSectionsIso S S' fS fX hf).hom.app
            ((bigDirectImage S).obj F) ≫ Sheaf.ΓRes ((bigDirectImage S).obj F) (op A.obj)) =
      (Sheaf.ΓNatIsoLim (smallTopology S') AddCommGrpCat.{u + 1}).hom.app
          ((smallRestriction S').obj
            ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj F))) ≫
        (restrictionConeπ ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj F))
            (op ((changeBase S S' fS fX hf).obj A.obj)) ≫
          ((changeBase S S' fS fX hf).op.ranCounit.app ((bigDirectImage S).obj F).obj).app
            (op A.obj)) :=
    (congrArg (fun z ↦ (smallRestrictionGlobalSectionsIso (S := S')).hom.app
        ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj F)) ≫ z) h3).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z ↦ z ≫ ((changeBase S S' fS fX hf).op.ranCounit.app
            ((bigDirectImage S).obj F).obj).app (op A.obj)) h1).trans (Category.assoc _ _ _)))
  have final := (reassoc_of% step)
    (((CrystallineThickening.ι S).op.ranCounit.app F.obj).app (op A))
  exact final.trans (congrArg (fun z ↦ (Sheaf.ΓNatIsoLim (smallTopology S')
      AddCommGrpCat.{u + 1}).hom.app ((smallRestriction S').obj
        ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj F))) ≫ z)
    (Category.assoc _ _ _))

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
