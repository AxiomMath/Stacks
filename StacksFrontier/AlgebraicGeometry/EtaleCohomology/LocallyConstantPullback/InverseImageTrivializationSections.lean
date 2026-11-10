module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.InverseImageFiniteLocallyConstant

/-!
# Sections of a trivialization carried along inverse image

Let `G : C ⥤ D` be a left exact continuous functor between sites whose pushforward has a left
adjoint `G^*`. If a sheaf `F` on `C` is constant with value `E` on an object `X`, then `G^*F` is
constant with the same value on `G X`
(`Stacks.ConstantSheaf.constantIsoOverPullbackSheafPullback`, the step of Tag 093R). This file
records what that trivialization does on sections over the top objects of the two slices: the
canonical map `E ⟶ Γ(G X, G^*F)` it defines is the canonical map `E ⟶ Γ(X, F)` followed by the
unit `F(X) ⟶ (G^*F)(G X)` of `G^* ⊣ G_*`. This is what is needed to read inverse image on
sections over a trivializing object, as the comparison of monodromy modules along a morphism of
schemes does.

Both isomorphisms entering the trivialization are obtained by uniqueness of left adjoints, so
their behaviour on sections comes from the units of the adjunctions they compare
(`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`).

## Main results

* `Stacks.ConstantSheaf.sheafPushforwardAdjunction_unit_app_hom_app` — the unit of the
  adjunction between the pushforwards along an adjoint pair of continuous functors is restriction
  along the counit.
* `Stacks.ConstantSheaf.sheafPullbackConstantSheafIso_inv_app_hom_app` — the identification of
  the inverse image of a constant sheaf with a constant sheaf, on sections over the final object.
* `Stacks.ConstantSheaf.overPullbackSheafPullbackIso_inv_app_top` — the localization square of
  Tag 093R, on sections over the top object of the slice: it identifies the unit of the inverse
  image along the slice functor with the unit of the inverse image along `G`.
* `Stacks.ConstantSheaf.toSheafify_comp_constantIsoOverPullbackSheafPullback_hom_app` — **the
  constants of the carried trivialization are the images under the unit of the constants of the
  original one.**

## Implementation notes

Several sections and restriction maps that occur here are definitionally but not reducibly equal,
because the objects of the two slices are reached through `Over.post`, `Over.star` and the
composite pushforwards. Rewriting under such composites fails, so the proofs chain equalities of
morphisms with `Eq.trans`, `congrArg` and `Category.assoc`, whose elaboration unifies up to
definitional equality.

## References

* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
* [Stacks Project, Tag 03CE](https://stacks.math.columbia.edu/tag/03CE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w' w v u v' u'

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (A : Type w) [Category.{w'} A]

section Unit

variable {J K} {u : C ⥤ D} {v : D ⥤ C} [u.IsContinuous J K] [v.IsContinuous K J]

/-- **The unit of the adjunction between pushforwards along an adjoint pair `u ⊣ v`** is the
restriction along the counit of `u ⊣ v`. -/
public lemma sheafPushforwardAdjunction_unit_app_hom_app (adj : u ⊣ v) (F : Sheaf K A)
    (Z : Dᵒᵖ) :
    ((adj.sheafPushforwardAdjunction (J := J) (K := K) A).unit.app F).hom.app Z =
      F.obj.map (adj.counit.app Z.unop).op := by
  have h := Adjunction.map_restrictFullyFaithful_unit_app
    (Functor.whiskeringLeftAdjunctionOfAdjunction A adj)
    (fullyFaithfulSheafToPresheaf K A) (fullyFaithfulSheafToPresheaf J A)
    (u.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
    (v.sheafPushforwardContinuousCompSheafToPresheafIso A K J).symm F
  have h2 := congrArg (fun φ => φ.app Z) h
  simp only [Functor.whiskeringLeftAdjunctionOfAdjunction] at h2
  simp at h2
  exact h2.trans ((congrArg _ (Category.id_comp _)).trans (Category.comp_id _))

end Unit

section Constant

variable {J K} (H : C ⥤ D) [H.IsContinuous J K]
  [(H.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [HasWeakSheafify J A] [HasWeakSheafify K A]

/-- The unit of the constant sheaf adjunction is `toSheafify` at the terminal object. -/
private theorem unit_app_constantSheafAdj {T : C} (hT : IsTerminal T) (E : A) :
    (constantSheafAdj J A hT).unit.app E =
      (toSheafify J ((Functor.const Cᵒᵖ).obj E)).app (op T) := by
  simp [constantSheafAdj, Adjunction.comp_unit_app, sheafificationAdjunction_unit_app]
  rfl

/-- **The inverse image of a constant sheaf is the constant sheaf, on sections over the final
object.** The constant sections of the constant sheaf on `D` at the final object `T'` are, under
`Stacks.ConstantSheaf.sheafPullbackConstantSheafIso`, the constant sections at the final object
`T` of `C` carried by the unit of `H^* ⊣ H_*` and transported along `H.obj T ≅ T'`. -/
public theorem sheafPullbackConstantSheafIso_inv_app_hom_app {T : C} (hT : IsTerminal T) {T' : D}
    (hT' : IsTerminal T') (e : H.obj T ≅ T') (E : A) :
    (toSheafify K ((Functor.const Dᵒᵖ).obj E)).app (op T') ≫
        ((sheafPullbackConstantSheafIso H A J K hT hT' e).inv.app E).hom.app (op T') =
      (toSheafify J ((Functor.const Cᵒᵖ).obj E)).app (op T) ≫
        ((H.sheafAdjunctionContinuous A J K).unit.app ((constantSheaf J A).obj E)).hom.app (op T) ≫
          ((H.sheafPullback A J K).obj ((constantSheaf J A).obj E)).obj.map e.inv.op := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (((constantSheafAdj J A hT).comp (H.sheafAdjunctionContinuous A J K)).ofNatIsoRight
      (pushforwardSectionsIsoOfTerminal H A J K e)) (constantSheafAdj K A hT') E
  have u1 : (((constantSheafAdj J A hT).comp (H.sheafAdjunctionContinuous A J K)).ofNatIsoRight
      (pushforwardSectionsIsoOfTerminal H A J K e)).unit.app E =
      (toSheafify J ((Functor.const Cᵒᵖ).obj E)).app (op T) ≫
        ((H.sheafAdjunctionContinuous A J K).unit.app ((constantSheaf J A).obj E)).hom.app (op T) ≫
          ((H.sheafPullback A J K).obj ((constantSheaf J A).obj E)).obj.map e.inv.op := by
    simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Adjunction.comp_unit_app, unit_app_constantSheafAdj, pushforwardSectionsIsoOfTerminal]
    exact Category.assoc _ _ _
  rw [u1, unit_app_constantSheafAdj] at h
  have h2 := congrArg (· ≫ ((sheafPullbackConstantSheafIso H A J K hT hT' e).inv.app E).hom.app
    (op T')) h
  refine h2.symm.trans ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (congrArg (fun φ => φ.hom.app (op T'))
      ((sheafPullbackConstantSheafIso H A J K hT hT' e).hom_inv_id_app E))).trans
    (Category.comp_id _)))

end Constant

section Main

variable [HasFiniteLimits C] [HasFiniteLimits D]
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  [∀ U : C, HasWeakSheafify (J.over U) A] [∀ V : D, HasWeakSheafify (K.over V) A]
  (G : C ⥤ D) [G.IsContinuous J K] [PreservesFiniteLimits G]
  [(G.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [∀ X : C, (Over.post (X := X) G).IsContinuous (J.over X) (K.over (G.obj X))]
  [∀ X : C, ((Over.post (X := X) G).sheafPushforwardContinuous A
    (J.over X) (K.over (G.obj X))).IsRightAdjoint]

omit [HasWeakSheafify J A] [HasWeakSheafify K A] [∀ U : C, HasWeakSheafify (J.over U) A]
  [∀ V : D, HasWeakSheafify (K.over V) A] in
/-- **The localization square of Tag 093R on sections over the top object.** Under
`Stacks.ConstantSheaf.overPullbackSheafPullbackIso`, the unit of the inverse image along the slice
functor `Over.post G` at the top object of `C/X` is the unit of the inverse image along `G` at
`X`. -/
public theorem overPullbackSheafPullbackIso_inv_app_top (X : C) (F : Sheaf J A) :
    (((Over.post (X := X) G).sheafAdjunctionContinuous A (J.over X)
        (K.over (G.obj X))).unit.app ((J.overPullback A X).obj F)).hom.app
          (op (Over.mk (𝟙 X))) ≫
      ((overPullbackSheafPullbackIso J K A G X).inv.app F).hom.app
        (op ((Over.post (X := X) G).obj (Over.mk (𝟙 X)))) =
    ((G.sheafAdjunctionContinuous A J K).unit.app F).hom.app (op X) := by
  let : (Over.star X ⋙ Over.post (X := X) G).IsContinuous J (K.over (G.obj X)) :=
    Functor.isContinuous_comp _ _ J (J.over X) (K.over (G.obj X))
  let : (G ⋙ Over.star (G.obj X)).IsContinuous J (K.over (G.obj X)) :=
    Functor.isContinuous_comp _ _ J K (K.over (G.obj X))
  -- the iso of right adjoints used by `overPullbackSheafPullbackIso`, componentwise
  let ε := Functor.sheafPushforwardContinuousComp'
          (Iso.refl (G ⋙ Over.star (G.obj X))) A J K (K.over (G.obj X)) ≪≫
        (Functor.sheafPushforwardContinuousIso (starPostIso G X) A J
          (K.over (G.obj X))).symm ≪≫
        (Functor.sheafPushforwardContinuousComp'
          (Iso.refl (Over.star X ⋙ Over.post (X := X) G)) A J (J.over X)
          (K.over (G.obj X))).symm
  have tε : ∀ (M : Sheaf (K.over (G.obj X)) A) (Z : Cᵒᵖ),
      (ε.hom.app M).hom.app Z = M.obj.map ((starPostIso G X).hom.app Z.unop).op := by
    intro M Z
    have t1 : ((Functor.sheafPushforwardContinuousComp'
          (Iso.refl (G ⋙ Over.star (G.obj X))) A J K (K.over (G.obj X))).hom.app M).hom.app Z =
          𝟙 _ := by
      simp only [Functor.sheafPushforwardContinuousComp'_hom_app_hom_app, Iso.refl_inv,
        NatTrans.id_app]
      exact (congrArg M.obj.map op_id).trans (M.obj.map_id _)
    have t2 : ((Functor.sheafPushforwardContinuousComp'
          (Iso.refl (Over.star X ⋙ Over.post (X := X) G)) A J (J.over X)
          (K.over (G.obj X))).inv.app M).hom.app Z = 𝟙 _ := by
      simp only [Functor.sheafPushforwardContinuousComp'_inv_app_hom_app, Iso.refl_hom,
        NatTrans.id_app]
      exact (congrArg M.obj.map op_id).trans (M.obj.map_id _)
    have hdec : (ε.hom.app M).hom.app Z =
        ((Functor.sheafPushforwardContinuousComp'
          (Iso.refl (G ⋙ Over.star (G.obj X))) A J K (K.over (G.obj X))).hom.app M).hom.app Z ≫
        M.obj.map ((starPostIso G X).hom.app Z.unop).op ≫
        ((Functor.sheafPushforwardContinuousComp'
          (Iso.refl (Over.star X ⋙ Over.post (X := X) G)) A J (J.over X)
          (K.over (G.obj X))).inv.app M).hom.app Z := rfl
    rw [hdec, t1, t2]
    exact (Category.id_comp _).trans (Category.comp_id _)
  let P := Over.post (X := X) G
  let adj2 := ((Over.forgetAdjStar X).sheafPushforwardAdjunction (J := J.over X) (K := J) A).comp
      (P.sheafAdjunctionContinuous A (J.over X) (K.over (G.obj X)))
  let adj1 := ((G.sheafAdjunctionContinuous A J K).comp
        ((Over.forgetAdjStar (G.obj X)).sheafPushforwardAdjunction
          (J := K.over (G.obj X)) (K := K) A)).ofNatIsoRight ε
  have h := Adjunction.unit_leftAdjointUniq_hom_app adj2 adj1 F
  have hκ : (overPullbackSheafPullbackIso J K A G X).inv.app F =
      (adj2.leftAdjointUniq adj1).hom.app F := rfl
  let δ : Over.mk (𝟙 X) ⟶ (Over.star X).obj X := (Over.forgetAdjStar X).unit.app (Over.mk (𝟙 X))
  let S := (G.sheafPullback A J K).obj F
  let H₁ := (K.overPullback A (G.obj X)).obj S
  let uP := (P.sheafAdjunctionContinuous A (J.over X) (K.over (G.obj X))).unit.app
    ((J.overPullback A X).obj F)
  let η := (G.sheafAdjunctionContinuous A J K).unit.app F
  let κi := (overPullbackSheafPullbackIso J K A G X).inv.app F
  have h3 := congrArg (fun φ => φ.hom.app (op X) ≫ H₁.obj.map (P.map δ).op) h
  have eL : (adj2.unit.app F ≫ (P.sheafPushforwardContinuous A (J.over X) (K.over (G.obj X)) ⋙
        (Over.star X).sheafPushforwardContinuous A J (J.over X)).map
          ((adj2.leftAdjointUniq adj1).hom.app F)).hom.app (op X) =
      F.obj.map ((Over.forgetAdjStar X).counit.app X).op ≫
        uP.hom.app (op ((Over.star X).obj X)) ≫ κi.hom.app (op (P.obj ((Over.star X).obj X))) := by
    simp only [adj2, Adjunction.comp_unit_app, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app, Functor.comp_map, Functor.sheafPushforwardContinuous_map_hom_app,
      sheafPushforwardAdjunction_unit_app_hom_app, Category.assoc]
    rfl
  have eR : (adj1.unit.app F).hom.app (op X) =
      η.hom.app (op X) ≫ S.obj.map ((Over.forgetAdjStar (G.obj X)).counit.app (G.obj X)).op ≫
        S.obj.map ((starPostIso G X).hom.app X).left.op := by
    simp only [adj1, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Adjunction.comp_unit_app, ObjectProperty.FullSubcategory.comp_hom,
      Functor.sheafPushforwardContinuous_map_hom_app, sheafPushforwardAdjunction_unit_app_hom_app,
      tε, Category.assoc]
    rfl
  have n1 : κi.hom.app (op (P.obj ((Over.star X).obj X))) ≫ H₁.obj.map (P.map δ).op =
      ((P.sheafPullback A (J.over X) (K.over (G.obj X))).obj
          ((J.overPullback A X).obj F)).obj.map (P.map δ).op ≫
        κi.hom.app (op (P.obj (Over.mk (𝟙 X)))) := (κi.hom.naturality (P.map δ).op).symm
  have n2 : uP.hom.app (op ((Over.star X).obj X)) ≫
      ((P.sheafPullback A (J.over X) (K.over (G.obj X))).obj
          ((J.overPullback A X).obj F)).obj.map (P.map δ).op =
        ((J.overPullback A X).obj F).obj.map δ.op ≫ uP.hom.app (op (Over.mk (𝟙 X))) :=
    (uP.hom.naturality δ.op).symm
  have tri : δ.left ≫ (Over.forgetAdjStar X).counit.app X = 𝟙 X :=
    (Over.forgetAdjStar X).left_triangle_components (Over.mk (𝟙 X))
  have t : F.obj.map ((Over.forgetAdjStar X).counit.app X).op ≫
      ((J.overPullback A X).obj F).obj.map δ.op = 𝟙 _ := by
    change F.obj.map ((Over.forgetAdjStar X).counit.app X).op ≫ F.obj.map δ.left.op = _
    rw [← F.obj.map_comp, ← op_comp, tri]
    exact (congrArg F.obj.map op_id).trans (F.obj.map_id _)
  let c := F.obj.map ((Over.forgetAdjStar X).counit.app X).op
  have hL : uP.hom.app (op (Over.mk (𝟙 X))) ≫ κi.hom.app (op (P.obj (Over.mk (𝟙 X)))) =
      c ≫ uP.hom.app (op ((Over.star X).obj X)) ≫ κi.hom.app (op (P.obj ((Over.star X).obj X))) ≫
          H₁.obj.map (P.map δ).op := by
    refine Eq.symm ((congrArg (fun k => c ≫ uP.hom.app (op ((Over.star X).obj X)) ≫ k) n1).trans
      ((congrArg (fun k => c ≫ k) (Category.assoc _ _ _).symm).trans
      ((congrArg (fun k => c ≫ k ≫ κi.hom.app (op (P.obj (Over.mk (𝟙 X))))) n2).trans
      (((congrArg (c ≫ ·) (Category.assoc _ _ _)).trans (Category.assoc _ _ _).symm).trans
      ((congrArg (· ≫ _) t).trans (Category.id_comp _))))))
  have key : G.map δ.left ≫ ((starPostIso G X).hom.app X).left ≫
      (Over.forgetAdjStar (G.obj X)).counit.app (G.obj X) = 𝟙 (G.obj X) := by
    have tri' : δ.left ≫ prod.snd = 𝟙 X := by
      rw [← Over.forgetAdjStar_counit_app X X]
      exact tri
    rw [Over.forgetAdjStar_counit_app,
      show ((starPostIso G X).hom.app X).left = (PreservesLimitPair.iso G X X).hom from rfl,
      PreservesLimitPair.iso_hom]
    exact ((congrArg (G.map δ.left ≫ ·) (prodComparison_snd G X X)).trans
      (G.map_comp _ _).symm).trans ((congrArg G.map tri').trans (G.map_id _))
  have hR : η.hom.app (op X) ≫ S.obj.map ((Over.forgetAdjStar (G.obj X)).counit.app (G.obj X)).op ≫
        S.obj.map ((starPostIso G X).hom.app X).left.op ≫ H₁.obj.map (P.map δ).op =
      η.hom.app (op X) := by
    have hop : ((Over.forgetAdjStar (G.obj X)).counit.app (G.obj X)).op ≫
        ((starPostIso G X).hom.app X).left.op ≫ (G.map δ.left).op = 𝟙 _ :=
      (congrArg (((Over.forgetAdjStar (G.obj X)).counit.app (G.obj X)).op ≫ ·)
        (op_comp (f := G.map δ.left) (g := ((starPostIso G X).hom.app X).left)).symm).trans
        ((op_comp (f := G.map δ.left ≫ ((starPostIso G X).hom.app X).left)
          (g := (Over.forgetAdjStar (G.obj X)).counit.app (G.obj X))).symm.trans
          ((congrArg Quiver.Hom.op ((Category.assoc _ _ _).trans key)).trans op_id))
    exact congrArg (η.hom.app (op X) ≫ ·)
      (((congrArg (S.obj.map ((Over.forgetAdjStar (G.obj X)).counit.app (G.obj X)).op ≫ ·)
        (S.obj.map_comp _ _).symm).trans (S.obj.map_comp _ _).symm).trans
        ((congrArg S.obj.map hop).trans (S.obj.map_id _))) |>.trans (Category.comp_id _)
  exact hL.trans
    (((Category.assoc _ _ _).trans (congrArg (c ≫ ·) (Category.assoc _ _ _))).symm.trans
    (((congrArg (· ≫ H₁.obj.map (P.map δ).op) eL).symm.trans h3).trans
    ((congrArg (· ≫ H₁.obj.map (P.map δ).op) eR).trans
    (((Category.assoc _ _ _).trans (congrArg (η.hom.app (op X) ≫ ·)
      (Category.assoc _ _ _))).trans hR))))

omit [HasWeakSheafify J A] [HasWeakSheafify K A] in
/-- **A trivialization carried along inverse image is compatible with the unit on sections.** If
`c` trivializes `F` over `X` with value `E`, the constant sections over `G X` of the trivialization
of `G^*F` carried along `G`
(`Stacks.ConstantSheaf.constantIsoOverPullbackSheafPullback`) are the constant sections over `X`
of `c` followed by the unit `F(X) ⟶ (G^*F)(G X)`. -/
public theorem toSheafify_comp_constantIsoOverPullbackSheafPullback_hom_app (X : C)
    (F : Sheaf J A) (E : A)
    (c : (constantSheaf (J.over X) A).obj E ≅ (J.overPullback A X).obj F) :
    (toSheafify (K.over (G.obj X)) ((Functor.const _).obj E)).app
        (op (Over.mk (𝟙 (G.obj X)))) ≫
      (constantIsoOverPullbackSheafPullback J K A G X F E c).hom.hom.app
        (op (Over.mk (𝟙 (G.obj X)))) =
    (toSheafify (J.over X) ((Functor.const _).obj E)).app (op (Over.mk (𝟙 X))) ≫
      c.hom.hom.app (op (Over.mk (𝟙 X))) ≫
        ((G.sheafAdjunctionContinuous A J K).unit.app F).hom.app (op X) := by
  have hU2 := sheafPullbackConstantSheafIso_inv_app_hom_app (J := J.over X)
    (K := K.over (G.obj X)) A (Over.post (X := X) G) Over.mkIdTerminal Over.mkIdTerminal
    (postMkIdIso G X) E
  have hU1 := overPullbackSheafPullbackIso_inv_app_top J K A G X F
  simp only [constantIsoOverPullbackSheafPullback, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Iso.app_hom,
    Functor.mapIso_hom, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  let P := Over.post (X := X) G
  let e := postMkIdIso G X
  let κi := (overPullbackSheafPullbackIso J K A G X).inv.app F
  let Pc := (P.sheafPullback A (J.over X) (K.over (G.obj X))).map c.hom
  have nPc : ((P.sheafPullback A (J.over X) (K.over (G.obj X))).obj
        ((constantSheaf (J.over X) A).obj E)).obj.map e.inv.op ≫
        Pc.hom.app (op (Over.mk (𝟙 (G.obj X)))) =
      Pc.hom.app (op (P.obj (Over.mk (𝟙 X)))) ≫
        ((P.sheafPullback A (J.over X) (K.over (G.obj X))).obj
          ((J.overPullback A X).obj F)).obj.map e.inv.op := Pc.hom.naturality e.inv.op
  have nU : ((P.sheafAdjunctionContinuous A (J.over X) (K.over (G.obj X))).unit.app
        ((constantSheaf (J.over X) A).obj E)).hom.app (op (Over.mk (𝟙 X))) ≫
        Pc.hom.app (op (P.obj (Over.mk (𝟙 X)))) =
      c.hom.hom.app (op (Over.mk (𝟙 X))) ≫
        ((P.sheafAdjunctionContinuous A (J.over X) (K.over (G.obj X))).unit.app
          ((J.overPullback A X).obj F)).hom.app (op (Over.mk (𝟙 X))) :=
    (congrArg (fun φ => φ.hom.app (op (Over.mk (𝟙 X))))
      ((P.sheafAdjunctionContinuous A (J.over X) (K.over (G.obj X))).unit.naturality c.hom)).symm
  have nκ : ((P.sheafPullback A (J.over X) (K.over (G.obj X))).obj
          ((J.overPullback A X).obj F)).obj.map e.inv.op ≫
        κi.hom.app (op (Over.mk (𝟙 (G.obj X)))) =
      κi.hom.app (op (P.obj (Over.mk (𝟙 X)))) ≫
        ((K.overPullback A (G.obj X)).obj ((G.sheafPullback A J K).obj F)).obj.map e.inv.op :=
    κi.hom.naturality e.inv.op
  have hid : ((K.overPullback A (G.obj X)).obj ((G.sheafPullback A J K).obj F)).obj.map
      e.inv.op = 𝟙 _ := ((G.sheafPullback A J K).obj F).obj.map_id _
  let t := (toSheafify (J.over X) ((Functor.const _).obj E)).app (op (Over.mk (𝟙 X)))
  let u := ((P.sheafAdjunctionContinuous A (J.over X) (K.over (G.obj X))).unit.app
        ((constantSheaf (J.over X) A).obj E)).hom.app (op (Over.mk (𝟙 X)))
  let m₁ := ((P.sheafPullback A (J.over X) (K.over (G.obj X))).obj
        ((constantSheaf (J.over X) A).obj E)).obj.map e.inv.op
  let p := Pc.hom.app (op (Over.mk (𝟙 (G.obj X))))
  let k := κi.hom.app (op (Over.mk (𝟙 (G.obj X))))
  let p' := Pc.hom.app (op (P.obj (Over.mk (𝟙 X))))
  let m₂ := ((P.sheafPullback A (J.over X) (K.over (G.obj X))).obj
          ((J.overPullback A X).obj F)).obj.map e.inv.op
  let cT := c.hom.hom.app (op (Over.mk (𝟙 X)))
  let u' := ((P.sheafAdjunctionContinuous A (J.over X) (K.over (G.obj X))).unit.app
          ((J.overPullback A X).obj F)).hom.app (op (Over.mk (𝟙 X)))
  let k' := κi.hom.app (op (P.obj (Over.mk (𝟙 X))))
  let m₃ := ((K.overPullback A (G.obj X)).obj ((G.sheafPullback A J K).obj F)).obj.map e.inv.op
  let η := ((G.sheafAdjunctionContinuous A J K).unit.app F).hom.app (op X)
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ p ≫ k) hU2).trans ?_
  refine ((Category.assoc t (u ≫ m₁) (p ≫ k)).trans
    (congrArg (t ≫ ·) (Category.assoc u m₁ (p ≫ k)))).trans ?_
  refine (congrArg (fun z => t ≫ u ≫ z) (Category.assoc m₁ p k).symm).trans ?_
  refine (congrArg (fun z => t ≫ u ≫ z ≫ k) nPc).trans ?_
  refine (congrArg (fun z => t ≫ u ≫ z) (Category.assoc p' m₂ k)).trans ?_
  refine (congrArg (t ≫ ·) (Category.assoc u p' (m₂ ≫ k)).symm).trans ?_
  refine (congrArg (fun z => t ≫ z ≫ m₂ ≫ k) nU).trans ?_
  refine (congrArg (t ≫ ·) (Category.assoc cT u' (m₂ ≫ k))).trans ?_
  refine (congrArg (fun z => t ≫ cT ≫ u' ≫ z) nκ).trans ?_
  refine (congrArg (fun z => t ≫ cT ≫ z) (Category.assoc u' k' m₃).symm).trans ?_
  refine (congrArg (fun z => t ≫ cT ≫ z ≫ m₃) hU1).trans ?_
  exact congrArg (fun z => t ≫ cT ≫ z) ((congrArg (η ≫ ·) hid).trans (Category.comp_id η))

end Main

end Stacks.ConstantSheaf
