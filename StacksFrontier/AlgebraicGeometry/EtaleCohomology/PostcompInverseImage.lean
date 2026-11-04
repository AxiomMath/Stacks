module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePostcomposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkSectionsTransitivity

/-!
# Inverse image along a composite with an étale morphism

Let `w : Z ⟶ X` be étale, `p : T ⟶ Z` any morphism and `q = p ≫ w`. For a sheaf of sets `F` on the
small étale site of `X`, the inverse image of `F` to `Z` along the étale morphism `w` is the
restriction `Σ_w^* F` of `F` along composition with `w`
(`Stacks.EtaleCohomology.smallEtaleRestrictionAdj`). This file identifies `p⁻¹(Σ_w^* F)` with
`q⁻¹F` as left adjoints of the two isomorphic direct images, and computes the identification on
the units: on sections over an étale `V ⟶ Z`, the unit of `p⁻¹` at `Σ_w^* F` is the unit of
`q⁻¹` over `V ⟶ Z ⟶ X`, followed by restriction along the canonical morphism
`V ×_Z T ⟶ V ×_X T`.

## Main definitions

* `Stacks.EtaleCohomology.postcompInverseImageIso`: `p⁻¹ ∘ Σ_w^* ≅ q⁻¹`.

## Main results

* `Stacks.EtaleCohomology.unit_comp_postcompInverseImageIso`: the identification on units.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

variable {X Z T : Scheme.{u}} (w : Z ⟶ X) [Etale w] (p : T ⟶ Z) (q : T ⟶ X) (h : q = p ≫ w)

/-- The canonical morphism `V ×_Z T ⟶ V ×_X T` of the small étale site of `T`, for `V` étale over
`Z`. -/
def baseChangePostcompMap (V : Z.Etale) :
    (smallEtaleBaseChange p).obj V ⟶ (smallEtaleBaseChange q).obj ((smallEtalePostcomp w).obj V) :=
  MorphismProperty.Over.homMk
    (pullback.lift (pullback.fst V.hom p) (pullback.snd V.hom p) (by
      change pullback.fst V.hom p ≫ V.hom ≫ w = pullback.snd V.hom p ≫ q
      rw [h, reassoc_of% (pullback.condition (f := V.hom) (g := p))]))
    (pullback.lift_snd _ _ _) trivial

/-- The morphism `baseChangePostcompMap` commutes with the first projections
`V ×_Z T ⟶ V` and `V ×_X T ⟶ V`. -/
theorem baseChangePostcompMap_left_fst (V : Z.Etale) :
    (baseChangePostcompMap w p q h V).left ≫ pullback.fst (V.hom ≫ w) q = pullback.fst V.hom p :=
  pullback.lift_fst _ _ _

/-- **The inverse image along `q = p ≫ w` is the inverse image along `p` of the restriction along
composition with `w`**, as left adjoints of the two isomorphic direct images. -/
def postcompInverseImageIso :
    (smallEtalePostcomp w).sheafPushforwardContinuous (Type (u + 1)) Z.smallEtaleTopology
        X.smallEtaleTopology ⋙ smallEtaleInverseImage.{u, 0} p ≅
      smallEtaleInverseImage.{u, 0} q :=
  Adjunction.leftAdjointUniq ((smallEtaleRestrictionAdj w (Type (u + 1))).comp
      (smallEtaleInverseImageAdjunction.{u, 0} p))
    (Adjunction.ofNatIsoRight (smallEtaleInverseImageAdjunction.{u, 0} q)
      (Functor.sheafPushforwardContinuousComp' (smallEtaleBaseChangeComp' p w q h).symm
        (Type (u + 1)) X.smallEtaleTopology Z.smallEtaleTopology T.smallEtaleTopology).symm)

omit [Etale w] in
/-- For `V` étale over `X`, the inverse of `smallEtaleBaseChangeComp'` at `V`, followed by the
first projection `V ×_X T ⟶ V`, is the composite of the first projections
`(V ×_X Z) ×_Z T ⟶ V ×_X Z ⟶ V`. -/
theorem smallEtaleBaseChangeComp'_inv_app_left_fst (V : X.Etale) :
    ((smallEtaleBaseChangeComp' p w q h).inv.app V).left ≫ pullback.fst V.hom q =
      pullback.fst ((smallEtaleBaseChange w).obj V).hom p ≫ pullback.fst V.hom w := by
  rw [← smallEtaleBaseChangeComp'_fst_fst p w q h V, ← Category.assoc]
  have h₂ : ((smallEtaleBaseChangeComp' p w q h).inv.app V).left ≫
      ((smallEtaleBaseChangeComp' p w q h).hom.app V).left = 𝟙 _ :=
    congrArg (fun m => m.left) ((smallEtaleBaseChangeComp' p w q h).inv_hom_id_app V)
  rw [h₂]
  exact Category.id_comp _

/-- Base change along `p` of the unit of `Σ_w ⊣ base change` at `V`, followed by the comparison
`smallEtaleBaseChangeComp'`, is `baseChangePostcompMap`. -/
private theorem smallEtaleBaseChange_map_unit_comp_baseChangeComp' (V : Z.Etale) :
    (smallEtaleBaseChange p).map ((smallEtalePostcompAdj w).unit.app V) ≫
        (smallEtaleBaseChangeComp' p w q h).symm.hom.app ((smallEtalePostcomp w).obj V) =
      baseChangePostcompMap w p q h V := by
  apply smallEtaleBaseChange_hom_ext
  have e1 := smallEtaleBaseChangeComp'_inv_app_left_fst w p q h ((smallEtalePostcomp w).obj V)
  have e2 := smallEtaleBaseChange_map_left_fst p ((smallEtalePostcompAdj w).unit.app V)
  have e3 : ((smallEtalePostcompAdj w).unit.app V).left ≫ pullback.fst (V.hom ≫ w) w = 𝟙 V.left :=
    pullback.lift_fst _ _ _
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e1).trans ?_)
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) e2)).trans ?_
  refine ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) e3).trans (Category.comp_id _))).trans ?_
  exact (baseChangePostcompMap_left_fst w p q h V).symm

/-- The unit of the restriction along composition with `w`, on sections, is restriction along the
counit of `Σ_w ⊣ base change`. -/
theorem smallEtaleRestrictionAdj_unit_app (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (U : X.Etale) :
    ((smallEtaleRestrictionAdj w (Type (u + 1))).unit.app F).hom.app (op U) =
      F.obj.map ((smallEtalePostcompAdj w).counit.app U).op :=
  rfl

/-- **The identification `p⁻¹ ∘ Σ_w^* ≅ q⁻¹` on units**, on a section `x` of `F` over
`V ⟶ Z ⟶ X`. -/
theorem unit_comp_postcompInverseImageIso (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (V : Z.Etale) (x : F.obj.obj (op ((smallEtalePostcomp w).obj V))) :
    ((postcompInverseImageIso w p q h).hom.app F).hom.app (op ((smallEtaleBaseChange p).obj V))
        (((smallEtaleInverseImageAdjunction.{u, 0} p).unit.app
          (((smallEtalePostcomp w).sheafPushforwardContinuous (Type (u + 1)) Z.smallEtaleTopology
            X.smallEtaleTopology).obj F)).hom.app (op V) x) =
      ((smallEtaleInverseImage.{u, 0} q).obj F).obj.map (baseChangePostcompMap w p q h V).op
        (((smallEtaleInverseImageAdjunction.{u, 0} q).unit.app F).hom.app
          (op ((smallEtalePostcomp w).obj V)) x) := by
  let η := (smallEtalePostcompAdj w).unit.app V
  have key := Stacks.Sites.unit_comp_leftAdjointUniq_app (smallEtaleBaseChange w)
    (smallEtaleBaseChange p) (smallEtaleBaseChange q) (Type (u + 1)) X.smallEtaleTopology
    Z.smallEtaleTopology T.smallEtaleTopology (smallEtaleRestrictionAdj w (Type (u + 1)))
    (smallEtaleInverseImageAdjunction.{u, 0} p) (smallEtaleInverseImageAdjunction.{u, 0} q)
    (smallEtaleBaseChangeComp' p w q h).symm F ((smallEtalePostcomp w).obj V)
  have n1 := ((smallEtaleInverseImageAdjunction.{u, 0} p).unit.app
    (((smallEtalePostcomp w).sheafPushforwardContinuous (Type (u + 1)) Z.smallEtaleTopology
      X.smallEtaleTopology).obj F)).hom.naturality η.op
  have n2 := ((postcompInverseImageIso w p q h).hom.app F).hom.naturality
    ((smallEtaleBaseChange p).map η).op
  have tri : F.obj.map ((smallEtalePostcompAdj w).counit.app ((smallEtalePostcomp w).obj V)).op ≫
      F.obj.map ((smallEtalePostcomp w).map η).op = 𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp, (smallEtalePostcompAdj w).left_triangle_components V]
    exact F.obj.map_id _
  let A := F.obj.map ((smallEtalePostcompAdj w).counit.app ((smallEtalePostcomp w).obj V)).op
  let Bm := F.obj.map ((smallEtalePostcomp w).map η).op
  have E1 : Bm (A x) = x := by
    simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] using
      ConcreteCategory.congr_hom tri x
  have hk := ConcreteCategory.congr_hom key x
  have hn1 := ConcreteCategory.congr_hom n1 (A x)
  have hn2 := ConcreteCategory.congr_hom n2
    (((smallEtaleInverseImageAdjunction.{u, 0} p).unit.app
      (((smallEtalePostcomp w).sheafPushforwardContinuous (Type (u + 1)) Z.smallEtaleTopology
        X.smallEtaleTopology).obj F)).hom.app (op ((smallEtaleBaseChange w).obj
          ((smallEtalePostcomp w).obj V))) (A x))
  have hm :
      ((smallEtaleInverseImage.{u, 0} q).obj F).obj.map (baseChangePostcompMap w p q h V).op =
      ((smallEtaleInverseImage.{u, 0} q).obj F).obj.map
          ((smallEtaleBaseChangeComp' p w q h).symm.hom.app ((smallEtalePostcomp w).obj V)).op ≫
        ((smallEtaleInverseImage.{u, 0} q).obj F).obj.map ((smallEtaleBaseChange p).map η).op := by
    rw [← smallEtaleBaseChange_map_unit_comp_baseChangeComp' w p q h V, op_comp,
      Functor.map_comp]
  have hm' := ConcreteCategory.congr_hom hm
    (((smallEtaleInverseImageAdjunction.{u, 0} q).unit.app F).hom.app
      (op ((smallEtalePostcomp w).obj V)) x)
  refine (congrArg (fun y => ((postcompInverseImageIso w p q h).hom.app F).hom.app
    (op ((smallEtaleBaseChange p).obj V)) (((smallEtaleInverseImageAdjunction.{u, 0} p).unit.app
      (((smallEtalePostcomp w).sheafPushforwardContinuous (Type (u + 1)) Z.smallEtaleTopology
        X.smallEtaleTopology).obj F)).hom.app (op V) y)) E1.symm).trans ?_
  refine (congrArg (((postcompInverseImageIso w p q h).hom.app F).hom.app
    (op ((smallEtaleBaseChange p).obj V))) hn1).trans ?_
  refine hn2.trans ?_
  refine (congrArg (((smallEtaleInverseImage.{u, 0} q).obj F).obj.map
    ((smallEtaleBaseChange p).map η).op) hk).trans ?_
  exact hm'.symm

end Stacks.EtaleCohomology
