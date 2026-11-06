module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.AbelianModuleShriekComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LimitCategory.AbelianSectionsSurjectivity
public import StacksFrontier.CategoryTheory.Sites.PullbackSheafCompose

/-!
# Sections of an inverse image of a sheaf of modules over a limit come from a stage

The module-coefficient form of
`AlgebraicGeometry.exists_smallEtaleStageLeg_eq_abelian`: for a sheaf `G` of `Λ`-modules on the
small étale site of Stacks 021B of a stage `X_i` of a directed inverse system with affine
transition morphisms and limit `X`, and a quasi-compact quasi-separated étale `U` over `X_i`, every
section of `p_i⁻¹G` over `U ×_{X_i} X` comes through the leg from a section of `f_{ji}⁻¹G` over
`U ×_{X_i} X_j` for some `j ≥ i`.

Passing to the underlying abelian sheaves commutes with inverse image
(`CategoryTheory.Functor.sheafPullbackSheafComposeIso`), and the comparison is characterized by a
unit equation, so the two legs correspond by
`CategoryTheory.Adjunction.unitCharacterized_transport`; a section of a sheaf of modules is a
section of its underlying abelian sheaf.

## Main results

* `AlgebraicGeometry.smallEtaleStageLeg_forget₂` — the comparison of the two legs.
* `AlgebraicGeometry.exists_smallEtaleStageLeg_eq_module` — the surjectivity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (Λ : Type (u + 1)) [CommRing Λ]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

/-- Passing from sheaves of `Λ`-modules to the underlying abelian sheaves. -/
abbrev smallEtaleForget₂ (S : B.Scheme) :
    Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{u + 1} Λ) ⥤
      Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1} :=
  letI : (SmallEtale.topology B S.obj S.property).HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    Stacks.ModuleSheaf.hasSheafCompose_forget₂.{u + 1} Λ _
  sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

/-- **Passing to underlying abelian sheaves commutes with inverse image**: the comparison
`CategoryTheory.Functor.sheafPullbackSheafComposeHom` along small étale base change. -/
def smallEtaleForget₂PullbackHom {S T : B.Scheme} (f : T ⟶ S)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{u + 1} Λ)) :
    (smallEtaleSheafPullback B AddCommGrpCat.{u + 1} f).obj ((smallEtaleForget₂ B Λ S).obj F) ⟶
      (smallEtaleForget₂ B Λ T).obj ((smallEtaleSheafPullback B (ModuleCat.{u + 1} Λ) f).obj F) :=
  letI := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B T Λ
  letI : (SmallEtale.topology B S.obj S.property).HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    Stacks.ModuleSheaf.hasSheafCompose_forget₂.{u + 1} Λ _
  letI : (SmallEtale.topology B T.obj T.property).HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    Stacks.ModuleSheaf.hasSheafCompose_forget₂.{u + 1} Λ _
  (smallEtaleBaseChange B f).sheafPullbackSheafComposeHom (ModuleCat.{u + 1} Λ)
    (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) F

/-- The comparison of `AlgebraicGeometry.smallEtaleForget₂PullbackHom` is an isomorphism. -/
instance isIso_smallEtaleForget₂PullbackHom {S T : B.Scheme} (f : T ⟶ S)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{u + 1} Λ)) :
    IsIso (smallEtaleForget₂PullbackHom B Λ f F) := by
  let := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B T Λ
  let : (SmallEtale.topology B S.obj S.property).HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    Stacks.ModuleSheaf.hasSheafCompose_forget₂.{u + 1} Λ _
  let : (SmallEtale.topology B T.obj T.property).HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    Stacks.ModuleSheaf.hasSheafCompose_forget₂.{u + 1} Λ _
  let : (SmallEtale.topology B T.obj T.property).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    Stacks.ModuleSheaf.preservesSheafification_forget₂.{u + 1} Λ _
  let : ∀ P : (SmallEtale B S.obj S.property)ᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtaleBaseChange B f).op.HasPointwiseLeftKanExtension P := fun _ Y => by
    let := hasColimitsOfShape_of_essentiallySmall.{u + 1}
      (CostructuredArrow (smallEtaleBaseChange B f).op Y) (ModuleCat.{u + 1} Λ)
    infer_instance
  let : ∀ P : (SmallEtale B S.obj S.property)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallEtaleBaseChange B f).op.HasPointwiseLeftKanExtension P := fun _ Y => by
    let := hasColimitsOfShape_of_essentiallySmall.{u + 1}
      (CostructuredArrow (smallEtaleBaseChange B f).op Y) AddCommGrpCat.{u + 1}
    infer_instance
  let : ∀ Y : (SmallEtale B T.obj T.property)ᵒᵖ,
      PreservesColimitsOfShape (CostructuredArrow (smallEtaleBaseChange B f).op Y)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := fun Y => by
    let := hasColimitsOfShape_of_essentiallySmall.{u + 1}
      (CostructuredArrow (smallEtaleBaseChange B f).op Y) AddCommGrpCat.{u + 1}
    infer_instance
  exact Functor.isIso_sheafPullbackSheafComposeHom _ _ _ _ _ F

/-- **The unit equation of the comparison with the underlying abelian sheaves.** -/
theorem unit_comp_map_smallEtaleForget₂PullbackHom {S T : B.Scheme} (f : T ⟶ S)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{u + 1} Λ)) :
    (smallEtaleSheafAdjunction B AddCommGrpCat.{u + 1} f).unit.app
          ((smallEtaleForget₂ B Λ S).obj F) ≫
        (smallEtaleSheafPushforward B AddCommGrpCat.{u + 1} f).map
          (smallEtaleForget₂PullbackHom B Λ f F) =
      (smallEtaleForget₂ B Λ S).map
          ((smallEtaleSheafAdjunction B (ModuleCat.{u + 1} Λ) f).unit.app F) ≫
        𝟙 _ := by
  let := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B T Λ
  let : (SmallEtale.topology B S.obj S.property).HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    Stacks.ModuleSheaf.hasSheafCompose_forget₂.{u + 1} Λ _
  let : (SmallEtale.topology B T.obj T.property).HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    Stacks.ModuleSheaf.hasSheafCompose_forget₂.{u + 1} Λ _
  exact Functor.unit_comp_pushforward_map_sheafPullbackSheafComposeHom _ _ _ _ _ F

/-- Passing to underlying abelian sheaves commutes with direct image on the nose. -/
abbrev smallEtaleForget₂PushforwardHom {S T : B.Scheme} (f : T ⟶ S) :
    smallEtaleSheafPushforward B (ModuleCat.{u + 1} Λ) f ⋙ smallEtaleForget₂ B Λ S ⟶
      smallEtaleForget₂ B Λ T ⋙ smallEtaleSheafPushforward B AddCommGrpCat.{u + 1} f :=
  𝟙 _

omit [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint] in
/-- The comparisons of direct images along a composite are compatible with passing to underlying
abelian sheaves. -/
theorem smallEtaleForget₂_pushforwardComp_compat {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (e : f ≫ g = h)
    (K : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) :
    (smallEtaleForget₂ B Λ Z).map
        ((smallEtalePushforwardCompHom B (ModuleCat.{u + 1} Λ) f g h e).app K) ≫
      (smallEtaleForget₂PushforwardHom B Λ g).app
        ((smallEtaleSheafPushforward B (ModuleCat.{u + 1} Λ) f).obj K) ≫
      (smallEtaleSheafPushforward B AddCommGrpCat.{u + 1} g).map
        ((smallEtaleForget₂PushforwardHom B Λ f).app K) =
    (smallEtaleForget₂PushforwardHom B Λ h).app K ≫
      (smallEtalePushforwardCompHom B AddCommGrpCat.{u + 1} f g h e).app
        ((smallEtaleForget₂ B Λ X).obj K) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  induction U with | op V => ?_
  have h1 := AlgebraicGeometry.sheafPushforwardContinuousComp'_inv_app_hom_app B f g h e
    (ModuleCat.{u + 1} Λ) K V
  have h2 := AlgebraicGeometry.sheafPushforwardContinuousComp'_inv_app_hom_app B f g h e
    AddCommGrpCat.{u + 1} ((smallEtaleForget₂ B Λ X).obj K) V
  simp only [smallEtaleForget₂PushforwardHom, NatTrans.id_app, smallEtalePushforwardCompHom]
  exact (congrArg (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map h1).trans h2.symm

/-- **The legs of sections of a sheaf of modules and of its underlying abelian sheaf agree.** -/
theorem smallEtaleStageLeg_forget₂ {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (e : f ≫ g = h) (G : Sheaf (SmallEtale.topology B Z.obj Z.property) (ModuleCat.{u + 1} Λ)) :
    smallEtaleForget₂PullbackHom B Λ g G ≫
        (smallEtaleForget₂ B Λ Y).map (smallEtaleStageLeg B (ModuleCat.{u + 1} Λ) f g h e G) ≫
        (smallEtaleForget₂PushforwardHom B Λ f).app
          ((smallEtaleSheafPullback B (ModuleCat.{u + 1} Λ) h).obj G) =
      smallEtaleStageLeg B AddCommGrpCat.{u + 1} f g h e ((smallEtaleForget₂ B Λ Z).obj G) ≫
        (smallEtaleSheafPushforward B AddCommGrpCat.{u + 1} f).map
          (smallEtaleForget₂PullbackHom B Λ h G) :=
  Adjunction.unitCharacterized_transport (smallEtaleSheafAdjunction B AddCommGrpCat.{u + 1} g)
    (smallEtaleSheafAdjunction B AddCommGrpCat.{u + 1} h)
    (smallEtalePushforwardCompHom B AddCommGrpCat.{u + 1} f g h e)
    (smallEtaleSheafAdjunction B (ModuleCat.{u + 1} Λ) g)
    (smallEtaleSheafAdjunction B (ModuleCat.{u + 1} Λ) h)
    (smallEtalePushforwardCompHom B (ModuleCat.{u + 1} Λ) f g h e)
    (smallEtaleForget₂ B Λ Z) (smallEtaleForget₂ B Λ Y) (smallEtaleForget₂ B Λ X)
    (smallEtaleForget₂PushforwardHom B Λ g) (smallEtaleForget₂PushforwardHom B Λ h)
    (smallEtaleForget₂PushforwardHom B Λ f)
    (smallEtaleStageLeg B AddCommGrpCat.{u + 1} f g h e)
    (unit_comp_map_smallEtaleStageLeg B AddCommGrpCat.{u + 1} f g h e)
    (smallEtaleStageLeg B (ModuleCat.{u + 1} Λ) f g h e)
    (unit_comp_map_smallEtaleStageLeg B (ModuleCat.{u + 1} Λ) f g h e)
    (smallEtaleForget₂PullbackHom B Λ g) (unit_comp_map_smallEtaleForget₂PullbackHom B Λ g)
    (smallEtaleForget₂PullbackHom B Λ h) (unit_comp_map_smallEtaleForget₂PullbackHom B Λ h)
    (smallEtaleForget₂_pushforwardComp_compat B Λ f g h e) G

section Limit

/-- Equal morphisms of abelian sheaves agree on sections. -/
private theorem sheaf_hom_app_apply_congr {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F G : Sheaf J AddCommGrpCat.{u + 1}} {a b : F ⟶ G} (h : a = b) (V : Cᵒᵖ)
    (x : ToType (F.obj.obj V)) : a.hom.app V x = b.hom.app V x := by
  subst h
  rfl

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

set_option maxHeartbeats 1000000 in
/-- **Sections of an inverse image of a sheaf of modules over a limit come from a stage** (the
surjectivity half of Stacks 09YN, the degree zero case of Stacks 09YQ, for sheaves of modules on
the small étale sites of Stacks 021B). Let `X = lim X_i` be the limit of a directed inverse system
of schemes with affine transition morphisms, `G` a sheaf of `Λ`-modules on the small étale site of
a stage `X_i` and `U` a quasi-compact and quasi-separated object of that site. Every section of
`p_i⁻¹G` over `U ×_{X_i} X`, read through the comparison of direct images, is the image under the
leg `AlgebraicGeometry.smallEtaleStageLeg` of a section of `f_{ji}⁻¹G` over `U ×_{X_i} X_j` for
some `j ≥ i`. -/
theorem exists_smallEtaleStageLeg_eq_module (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e))) {i : I}
    (G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
      (ModuleCat.{u + 1} Λ))
    (U : SmallEtale B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
    [CompactSpace ((SmallEtale.toScheme B _ _).obj U)]
    [QuasiSeparatedSpace ((SmallEtale.toScheme B _ _).obj U)]
    (s : ToType (((smallEtaleSheafPushforward B (ModuleCat.{u + 1} Λ)
      (coneStageHom B Dg c hX i)).obj ((smallEtaleSheafPullback B (ModuleCat.{u + 1} Λ)
        (coneStageHom B Dg c hX i)).obj G)).obj.obj (op U))) :
    ∃ (j : I) (hij : i ≤ j)
      (t : ToType (((smallEtaleSheafPushforward B (ModuleCat.{u + 1} Λ)
        (systemStageHom B Dg hij)).obj ((smallEtaleSheafPullback B (ModuleCat.{u + 1} Λ)
          (systemStageHom B Dg hij)).obj G)).obj.obj (op U))),
      ((smallEtaleSheafPushforward B (ModuleCat.{u + 1} Λ) (systemStageHom B Dg hij)).map
          (smallEtaleStageLeg B (ModuleCat.{u + 1} Λ) (coneStageHom B Dg c hX j)
            (systemStageHom B Dg hij) (coneStageHom B Dg c hX i) (coneStageHom_comp B Dg c hX hij)
            G)).hom.app (op U) t =
        ((smallEtalePushforwardCompHom B (ModuleCat.{u + 1} Λ) (coneStageHom B Dg c hX j)
          (systemStageHom B Dg hij) (coneStageHom B Dg c hX i)
          (coneStageHom_comp B Dg c hX hij)).app
            ((smallEtaleSheafPullback B (ModuleCat.{u + 1} Λ) (coneStageHom B Dg c hX i)).obj
              G)).hom.app (op U) s := by
  let pi := coneStageHom B Dg c hX i
  let γi := smallEtaleForget₂PullbackHom B Λ pi G
  have : IsIso γi := isIso_smallEtaleForget₂PullbackHom B Λ pi G
  let s' :=
    (smallEtaleSheafPushforward B AddCommGrpCat.{u + 1} pi |>.map (inv γi)).hom.app (op U) s
  obtain ⟨j, hij, t', ht'⟩ := exists_smallEtaleStageLeg_eq_abelian B Dg c hX hc haff
    ((smallEtaleForget₂ B Λ _).obj G) U s'
  refine ⟨j, hij, (smallEtaleSheafPushforward B AddCommGrpCat.{u + 1} (systemStageHom B Dg hij)
    |>.map (smallEtaleForget₂PullbackHom B Λ (systemStageHom B Dg hij) G)).hom.app (op U) t', ?_⟩
  let g := systemStageHom B Dg hij
  let pj := coneStageHom B Dg c hX j
  let e := coneStageHom_comp B Dg c hX hij
  let Qg := smallEtaleSheafPushforward B AddCommGrpCat.{u + 1} g
  have h2 := sheaf_hom_app_apply_congr
    (congrArg Qg.map (smallEtaleStageLeg_forget₂ B Λ pj g pi e G)) (op U) t'
  have h4 := sheaf_hom_app_apply_congr
    ((smallEtalePushforwardCompHom B AddCommGrpCat.{u + 1} pj g pi e).naturality γi) (op U) s'
  have h5 :
      (smallEtaleSheafPushforward B AddCommGrpCat.{u + 1} pi |>.map γi).hom.app (op U) s' = s :=
    SmallEtale.sheaf_iso_hom_inv_apply
      ((smallEtaleSheafPushforward B AddCommGrpCat.{u + 1} pi).mapIso (asIso γi)) (op U) s
  have h6 := sheaf_hom_app_apply_congr
    (smallEtaleForget₂_pushforwardComp_compat B Λ pj g pi e
      ((smallEtaleSheafPullback B (ModuleCat.{u + 1} Λ) pi).obj G)) (op U) s
  refine h2.trans ?_
  refine (congrArg (ConcreteCategory.hom ((Qg.map ((smallEtaleSheafPushforward B
    AddCommGrpCat.{u + 1} pj).map γi)).hom.app (op U))) ht').trans ?_
  refine h4.symm.trans ?_
  refine (congrArg (ConcreteCategory.hom (((smallEtalePushforwardCompHom B AddCommGrpCat.{u + 1}
    pj g pi e).app _).hom.app (op U))) h5).trans ?_
  exact h6.symm

end Limit

end AlgebraicGeometry
