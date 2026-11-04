module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationLevelSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SectionsRestrictionComposite

/-!
# Matching the cocone of restrictions with the degree-zero cocone of the base-change system

The degree-zero cocone of [Stacks, Tag 03Q6] at the system of base changes `Y_a = Z_a ×_U X_U`
has the groups `Γ(Y_a, π_a⁻¹F_U)`, where `F_U` is the restriction of `F` to `X_U` and
`π_a : Y_a ⟶ X_U` the projection, and its legs restrict global sections along the legs
`X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ Y_a` of the limit cone. The cocone of
`AlgebraicGeometry.strictHenselizationSectionsCocone` has the groups `F(X ×_S N_a)`. This file
identifies the two, object by object, compatibly with the legs and with the transition maps.

## Main definitions

* `AlgebraicGeometry.levelSectionsIso` — `F(X ×_S N_a) ≅ Γ(Y_a, π_a⁻¹F_U)`.
* `AlgebraicGeometry.limitSectionsIso` — `Γ(X', p'⁻¹F_U) ≅ Γ(X', p⁻¹F)` on the vertex.

## Main results

* `AlgebraicGeometry.levelSectionsIso_comp_leg` — compatibility with the legs.
* `AlgebraicGeometry.levelSectionsIso_comp_transition` — compatibility with the transitions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open AlgebraicGeometry.Scheme Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (U : S.Opens) (hU : s.hom (closedPoint s.residueField) ∈ U) {X : Scheme.{u}} (f : X ⟶ S)
  (F : Sheaf (smallEtaleTopology X) Ab.{u + 1})

/-- The projection of a level to `X_U`. -/
abbrev levelToSourceOverOpen (a : (etaleNeighborhoodDirectedIndex B S hS s U hU)ᵒᵖ) :
    (etaleNeighborhoodDirectedBaseChange B S hS s U hU f).obj a ⟶ (sourceOverOpen S U f).left :=
  pullback.snd ((etaleNeighborhoodDirectedSystem B S hS s U hU).obj a).hom
    (sourceOverOpen S U f).hom

/-- **The groups of the two cocones agree**: `F(X ×_S N_a) ≅ Γ(Y_a, π_a⁻¹F_U)`. -/
def levelSectionsIso (a : (etaleNeighborhoodDirectedIndex B S hS s U hU)ᵒᵖ) :
    ((smallEtalePushforwardAb f).obj F).obj.obj (op (directedNeighborhood B S hS s U hU a)) ≅
      (Sheaf.Γ (smallEtaleTopology ((etaleNeighborhoodDirectedBaseChange B S hS s U hU f).obj a))
        Ab.{u + 1}).obj ((smallEtalePullbackAb (levelToSourceOverOpen B S hS s U hU f a)).obj
          ((smallEtalePullbackAb (pullback.fst f U.ι)).obj F)) :=
  asIso (levelSections B S hS s U hU f a F) ≪≫
    (Sheaf.Γ _ Ab.{u + 1}).mapIso ((smallEtalePullbackAbCompIso'
      (levelToSourceOverOpen B S hS s U hU f a) (pullback.fst f U.ι)
      (levelToSource B S hS s U hU f a) rfl).symm.app F)

/-- **The vertices of the two cocones agree**: `Γ(X', p'⁻¹F_U) ≅ Γ(X', p⁻¹F)`. -/
def limitSectionsIso :
    (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1}).obj
        ((smallEtalePullbackAb (strictHenselizationToSourceOverOpen B S hS s U hU f)).obj
          ((smallEtalePullbackAb (pullback.fst f U.ι)).obj F)) ≅
      (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1}).obj
        ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s)).obj F) :=
  (Sheaf.Γ _ Ab.{u + 1}).mapIso ((smallEtalePullbackAbCompIso'
    (strictHenselizationToSourceOverOpen B S hS s U hU f) (pullback.fst f U.ι)
    (strictHenselizationBaseChangeToSource B hS f s)
    (strictHenselizationToSourceOverOpen_fst B S hS s U hU f).symm).app F)

/-- **Compatibility with the legs.** The leg of the cocone of restrictions is the identification
of the groups, the degree-zero leg (restriction of global sections along the leg of the limit cone,
read through the composition isomorphism), and the identification of the vertices. -/
theorem levelSectionsIso_comp_leg (a : (etaleNeighborhoodDirectedIndex B S hS s U hU)ᵒᵖ) :
    (levelSectionsIso B S hS s U hU f F a).hom ≫
        ((smallEtaleGlobalSectionsRestrictionAb
          ((strictHenselizationDirectedLimitCone B S hS s U hU f).π.app a)).app
            ((smallEtalePullbackAb (levelToSourceOverOpen B S hS s U hU f a)).obj
              ((smallEtalePullbackAb (pullback.fst f U.ι)).obj F)) ≫
          (Sheaf.Γ _ Ab.{u + 1}).map ((smallEtalePullbackAbCompIso'
            ((strictHenselizationDirectedLimitCone B S hS s U hU f).π.app a)
            (levelToSourceOverOpen B S hS s U hU f a)
            (strictHenselizationToSourceOverOpen B S hS s U hU f)
            (strictHenselizationDirectedLimitCone_π_snd B S hS s U hU f a).symm).hom.app
              ((smallEtalePullbackAb (pullback.fst f U.ι)).obj F))) ≫
        (limitSectionsIso B S hS s U hU f F).hom =
      pushforwardSectionsStage B hS f s (strictHenselizationBaseChangeToSource B hS f s)
        (strictHenselizationBaseChangeToStrictHenselization B hS f s) pullback.condition F
        (directedNeighborhood B S hS s U hU a)
        ((etaleNeighborhoodDirectedNeighborhoods B S hS s U hU).obj a).2 := by
  simp only [levelSectionsIso, limitSectionsIso, Iso.trans_hom, asIso_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.symm_hom, Category.assoc]
  exact smallEtaleSectionsPullbackAb_restriction_comp (pullback.fst f U.ι)
    (levelToSourceOverOpen B S hS s U hU f a)
    ((strictHenselizationDirectedLimitCone B S hS s U hU f).π.app a)
    (levelToSource B S hS s U hU f a) rfl
    (strictHenselizationToSourceOverOpen B S hS s U hU f)
    (strictHenselizationDirectedLimitCone_π_snd B S hS s U hU f a).symm
    (strictHenselizationBaseChangeToSource B hS f s)
    (strictHenselizationToSourceOverOpen_fst B S hS s U hU f).symm
    ((strictHenselizationToSourceOverOpen_fst B S hS s U hU f).symm.trans
      ((congrArg (· ≫ pullback.fst f U.ι)
        (strictHenselizationDirectedLimitCone_π_snd B S hS s U hU f a).symm).trans
          (Category.assoc _ _ _)))
    _ (levelToBaseChange B S hS s U hU f a) (levelToBaseChange_hom B S hS s U hU f a) _
    (strictHenselizationDirectedLimitCone_π_levelToBaseChange B S hS s U hU f a).symm
    (sectionsLift_hom B hS f s _ _ _ _ _) F

/-- The transition `Y_i ⟶ Y_j` of the levels, followed by the identification with the base change
`X ×_S N_j`, is the identification at `i` followed by the base change of the transition
`N_i ⟶ N_j` of neighbourhoods. -/
theorem levelToBaseChange_naturality {i j : (etaleNeighborhoodDirectedIndex B S hS s U hU)ᵒᵖ}
    (g : i ⟶ j) :
    (etaleNeighborhoodDirectedBaseChange B S hS s U hU f).map g ≫
        levelToBaseChange B S hS s U hU f j =
      levelToBaseChange B S hS s U hU f i ≫
        ((Stacks.EtaleCohomology.smallEtaleBaseChange f).map ((CategoryOfElements.π _).map
          ((etaleNeighborhoodDirectedNeighborhoods B S hS s U hU).map g))).left := by
  apply pullback.hom_ext
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (levelToBaseChange_fst B S hS s U hU f j)).trans ?_)
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_ (congrArg (levelToBaseChange B S hS s U hU f i ≫ ·)
      (pullback.lift_fst _ _ _).symm)
    refine Eq.trans ?_ (Category.assoc _ _ _)
    refine Eq.trans ?_ (congrArg (· ≫ _) (levelToBaseChange_fst B S hS s U hU f i).symm)
    exact pullback.lift_fst _ _ _
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (levelToBaseChange_hom B S hS s U hU f j)).trans ?_)
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_ (congrArg (levelToBaseChange B S hS s U hU f i ≫ ·)
      ((pullback.lift_snd _ _ _).trans (Category.comp_id _)).symm)
    refine Eq.trans ?_ (levelToBaseChange_hom B S hS s U hU f i).symm
    refine (Category.assoc _ _ _).symm.trans ?_
    exact congrArg (· ≫ pullback.fst f U.ι) (pullback.lift_snd _ _ _)

/-- The projections of the levels to `X_U` are compatible with the transitions. -/
theorem levelToSourceOverOpen_transition {i j : (etaleNeighborhoodDirectedIndex B S hS s U hU)ᵒᵖ}
    (g : i ⟶ j) :
    levelToSourceOverOpen B S hS s U hU f i =
      (etaleNeighborhoodDirectedBaseChange B S hS s U hU f).map g ≫
        levelToSourceOverOpen B S hS s U hU f j :=
  (Over.w ((etaleNeighborhoodDirectedSystem B S hS s U hU ⋙
    Over.pullback (sourceOverOpen S U f).hom).map g)).symm

/-- **Compatibility with the transitions.** The transition of the groups `F(X ×_S N_a)`
(restriction along `X ×_S N_i ⟶ X ×_S N_j`) corresponds to the transition of the degree-zero
diagram: restriction of global sections along `Y_i ⟶ Y_j`, read through the composition
isomorphism. -/
theorem levelSectionsIso_comp_transition {i j : (etaleNeighborhoodDirectedIndex B S hS s U hU)ᵒᵖ}
    (g : i ⟶ j) :
    (levelSectionsIso B S hS s U hU f F j).hom ≫
        (smallEtaleGlobalSectionsRestrictionAb
          ((etaleNeighborhoodDirectedBaseChange B S hS s U hU f).map g)).app
            ((smallEtalePullbackAb (levelToSourceOverOpen B S hS s U hU f j)).obj
              ((smallEtalePullbackAb (pullback.fst f U.ι)).obj F)) ≫
          (Sheaf.Γ _ Ab.{u + 1}).map ((smallEtalePullbackAbCompIso'
            ((etaleNeighborhoodDirectedBaseChange B S hS s U hU f).map g)
            (levelToSourceOverOpen B S hS s U hU f j) (levelToSourceOverOpen B S hS s U hU f i)
            (levelToSourceOverOpen_transition B S hS s U hU f g)).hom.app
              ((smallEtalePullbackAb (pullback.fst f U.ι)).obj F)) =
      ((smallEtalePushforwardAb f).obj F).obj.map ((CategoryOfElements.π _).map
          ((etaleNeighborhoodDirectedNeighborhoods B S hS s U hU).map g)).op ≫
        (levelSectionsIso B S hS s U hU f F i).hom := by
  let Γi := Sheaf.Γ (smallEtaleTopology ((etaleNeighborhoodDirectedBaseChange B S hS s U hU
    f).obj i)) Ab.{u + 1}
  let E := smallEtalePullbackAbCompIso' (levelToSourceOverOpen B S hS s U hU f i)
    (pullback.fst f U.ι) (levelToSource B S hS s U hU f i) rfl
  have hq₂ : levelToSource B S hS s U hU f i =
      (etaleNeighborhoodDirectedBaseChange B S hS s U hU f).map g ≫
        levelToSource B S hS s U hU f j := by
    show levelToSourceOverOpen B S hS s U hU f i ≫ pullback.fst f U.ι = _
    rw [levelToSourceOverOpen_transition B S hS s U hU f g, Category.assoc]
  have hr'' : ((etaleNeighborhoodDirectedBaseChange B S hS s U hU f).map g ≫
      levelToBaseChange B S hS s U hU f j) ≫
        ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj
          (directedNeighborhood B S hS s U hU j)).hom = levelToSource B S hS s U hU f i := by
    rw [Category.assoc, levelToBaseChange_hom, hq₂]
  have h1 := smallEtaleSectionsPullbackAb_restriction_comp (pullback.fst f U.ι)
    (levelToSourceOverOpen B S hS s U hU f j)
    ((etaleNeighborhoodDirectedBaseChange B S hS s U hU f).map g)
    (levelToSource B S hS s U hU f j) rfl (levelToSourceOverOpen B S hS s U hU f i)
    (levelToSourceOverOpen_transition B S hS s U hU f g) (levelToSource B S hS s U hU f i) rfl hq₂
    _ (levelToBaseChange B S hS s U hU f j) (levelToBaseChange_hom B S hS s U hU f j) _ rfl hr'' F
  have h2 := congrArg (fun φ => NatTrans.app φ F) (map_comp_smallEtaleSectionsPullbackAb
    (levelToSource B S hS s U hU f i)
    ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj (directedNeighborhood B S hS s U hU i))
    (levelToBaseChange B S hS s U hU f i)
    ((Stacks.EtaleCohomology.smallEtaleBaseChange f).map ((CategoryOfElements.π _).map
      ((etaleNeighborhoodDirectedNeighborhoods B S hS s U hU).map g)))
    (levelToBaseChange_hom B S hS s U hU f i)
    (by rw [← levelToBaseChange_naturality]; exact hr''))
  have h3 := congrArg (fun φ => NatTrans.app φ F) (smallEtaleSectionsPullbackAb_congr
    (levelToSource B S hS s U hU f i) _ _
    (by rw [← levelToBaseChange_naturality]; exact hr'') hr''
    (levelToBaseChange_naturality B S hS s U hU f g).symm)
  simp only [NatTrans.comp_app] at h2 h3
  rw [← cancel_mono (Γi.map (E.hom.app F))]
  simp only [levelSectionsIso, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, Category.assoc]
  have hc : Γi.map (E.inv.app F) ≫ Γi.map (E.hom.app F) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  refine h1.trans ?_
  refine (h3.symm.trans h2.symm).trans ?_
  show _ = _ ≫ _ ≫ Γi.map (E.inv.app F) ≫ Γi.map (E.hom.app F)
  rw [hc, Category.comp_id]
  rfl

/-- The groups `F(X ×_S N_a)` of the cocone of restrictions, as a diagram. -/
abbrev levelSectionsDiagram :
    (etaleNeighborhoodDirectedIndex B S hS s U hU)ᵒᵖᵒᵖ ⥤ Ab.{u + 1} :=
  (etaleNeighborhoodDirectedNeighborhoods B S hS s U hU).op ⋙
    (CategoryOfElements.π (Scheme.pointSmallEtale s.hom).fiber).op ⋙
      ((smallEtalePushforwardAb f).obj F).obj

/-- The transition map of the degree-zero diagram of the base-change system: restriction of global
sections along `Y_i ⟶ Y_j`, read through the composition isomorphism. -/
abbrev levelGammaTransition {i j : (etaleNeighborhoodDirectedIndex B S hS s U hU)ᵒᵖ} (g : i ⟶ j) :
    (Sheaf.Γ (smallEtaleTopology ((etaleNeighborhoodDirectedBaseChange B S hS s U hU f).obj j))
        Ab.{u + 1}).obj ((smallEtalePullbackAb (levelToSourceOverOpen B S hS s U hU f j)).obj
          ((smallEtalePullbackAb (pullback.fst f U.ι)).obj F)) ⟶
      (Sheaf.Γ (smallEtaleTopology ((etaleNeighborhoodDirectedBaseChange B S hS s U hU f).obj i))
        Ab.{u + 1}).obj ((smallEtalePullbackAb (levelToSourceOverOpen B S hS s U hU f i)).obj
          ((smallEtalePullbackAb (pullback.fst f U.ι)).obj F)) :=
  (smallEtaleGlobalSectionsRestrictionAb
      ((etaleNeighborhoodDirectedBaseChange B S hS s U hU f).map g)).app
        ((smallEtalePullbackAb (levelToSourceOverOpen B S hS s U hU f j)).obj
          ((smallEtalePullbackAb (pullback.fst f U.ι)).obj F)) ≫
    (Sheaf.Γ _ Ab.{u + 1}).map ((smallEtalePullbackAbCompIso'
      ((etaleNeighborhoodDirectedBaseChange B S hS s U hU f).map g)
      (levelToSourceOverOpen B S hS s U hU f j) (levelToSourceOverOpen B S hS s U hU f i)
      (levelToSourceOverOpen_transition B S hS s U hU f g)).hom.app
        ((smallEtalePullbackAb (pullback.fst f U.ι)).obj F))

/-- The transition `levelGammaTransition g` is the map of `levelSectionsDiagram` at `g.op`,
conjugated by the isomorphisms `levelSectionsIso`. -/
theorem levelGammaTransition_eq {i j : (etaleNeighborhoodDirectedIndex B S hS s U hU)ᵒᵖ}
    (g : i ⟶ j) :
    levelGammaTransition B S hS s U hU f F g =
      (levelSectionsIso B S hS s U hU f F j).inv ≫
        (levelSectionsDiagram B S hS s U hU f F).map g.op ≫
          (levelSectionsIso B S hS s U hU f F i).hom := by
  rw [Iso.eq_inv_comp]
  exact levelSectionsIso_comp_transition B S hS s U hU f F g

/-- **The degree-zero diagram of the base-change system**, `a ↦ Γ(Y_a, π_a⁻¹F_U)` with the
restrictions `levelGammaTransition` as transition maps. -/
def levelGammaDiagram : (etaleNeighborhoodDirectedIndex B S hS s U hU)ᵒᵖᵒᵖ ⥤ Ab.{u + 1} where
  obj a := (Sheaf.Γ (smallEtaleTopology ((etaleNeighborhoodDirectedBaseChange B S hS s U hU
    f).obj a.unop)) Ab.{u + 1}).obj ((smallEtalePullbackAb (levelToSourceOverOpen B S hS s U hU f
      a.unop)).obj ((smallEtalePullbackAb (pullback.fst f U.ι)).obj F))
  map g := levelGammaTransition B S hS s U hU f F g.unop
  map_id a := by
    change levelGammaTransition B S hS s U hU f F (𝟙 a.unop) = 𝟙 _
    rw [levelGammaTransition_eq, op_id, CategoryTheory.Functor.map_id]
    exact (congrArg (_ ≫ ·) (Category.id_comp _)).trans (Iso.inv_hom_id _)
  map_comp g h := by
    change levelGammaTransition B S hS s U hU f F (h.unop ≫ g.unop) =
      levelGammaTransition B S hS s U hU f F g.unop ≫ levelGammaTransition B S hS s U hU f F h.unop
    rw [levelGammaTransition_eq, levelGammaTransition_eq, levelGammaTransition_eq, op_comp,
      Functor.map_comp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The groups of the two diagrams agree, naturally. -/
def levelSectionsDiagramIso :
    levelSectionsDiagram B S hS s U hU f F ≅ levelGammaDiagram B S hS s U hU f F :=
  NatIso.ofComponents (fun a => levelSectionsIso B S hS s U hU f F a.unop) (fun {a b} g => by
    change _ = _ ≫ levelGammaTransition B S hS s U hU f F g.unop
    rw [levelGammaTransition_eq, Iso.hom_inv_id_assoc]
    rfl)

/-- **The degree-zero cocone of the base-change system**, with vertex `Γ(X', p'⁻¹F_U)` and legs the
restrictions of global sections along the legs of the limit cone. -/
def levelGammaCocone : Cocone (levelGammaDiagram B S hS s U hU f F) :=
  (Cocone.precompose (levelSectionsDiagramIso B S hS s U hU f F).inv).obj
    ((strictHenselizationSectionsCocone B S hS s U hU f F).extend
      (limitSectionsIso B S hS s U hU f F).inv)

/-- The legs of `levelGammaCocone` are the restrictions of global sections along the legs of the
limit cone, read through the composition isomorphism. -/
theorem levelGammaCocone_ι_app (a : (etaleNeighborhoodDirectedIndex B S hS s U hU)ᵒᵖᵒᵖ) :
    (levelGammaCocone B S hS s U hU f F).ι.app a =
      (smallEtaleGlobalSectionsRestrictionAb
          ((strictHenselizationDirectedLimitCone B S hS s U hU f).π.app a.unop)).app
            ((smallEtalePullbackAb (levelToSourceOverOpen B S hS s U hU f a.unop)).obj
              ((smallEtalePullbackAb (pullback.fst f U.ι)).obj F)) ≫
          (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1}).map
            ((smallEtalePullbackAbCompIso'
            ((strictHenselizationDirectedLimitCone B S hS s U hU f).π.app a.unop)
            (levelToSourceOverOpen B S hS s U hU f a.unop)
            (strictHenselizationToSourceOverOpen B S hS s U hU f)
            (strictHenselizationDirectedLimitCone_π_snd B S hS s U hU f a.unop).symm).hom.app
              ((smallEtalePullbackAb (pullback.fst f U.ι)).obj F)) := by
  show (levelSectionsIso B S hS s U hU f F a.unop).inv ≫
      (strictHenselizationSectionsCocone B S hS s U hU f F).ι.app a ≫
        (limitSectionsIso B S hS s U hU f F).inv = _
  rw [Iso.inv_comp_eq, Iso.comp_inv_eq, strictHenselizationSectionsCocone_ι_app,
    ← levelSectionsIso_comp_leg]
  simp only [Category.assoc]
  rfl

/-- **The cocone of restrictions is a colimit as soon as the degree-zero cocone of the base-change
system is.** -/
def isColimitStrictHenselizationSectionsCoconeOfLevelGamma
    (h : IsColimit (levelGammaCocone B S hS s U hU f F)) :
    IsColimit (strictHenselizationSectionsCocone B S hS s U hU f F) :=
  IsColimit.ofIsoColimit
    ((IsColimit.precomposeInvEquiv (levelSectionsDiagramIso B S hS s U hU f F) _) h)
    (Cocones.ext (limitSectionsIso B S hS s U hU f F) (fun _ => by simp))

end AlgebraicGeometry

end
