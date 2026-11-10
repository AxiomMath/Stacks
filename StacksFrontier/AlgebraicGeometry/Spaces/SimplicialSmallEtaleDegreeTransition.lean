module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictBridgeCocycle
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictTransitionSets
public import StacksFrontier.CategoryTheory.Functor.KanExtension.RanBaseChange

/-!
# The degree transitions of a simplicial algebraic space

Let `X` be a simplicial algebraic space and `φ : [m] ⟶ [n]`. The morphisms
`(n, V ×_{X_m} X_n) ⟶ (m, V)` of `X_{spaces,étale}` give a 2-morphism
`τ_φ : d_n ⟶ d_m ∘ X(φ)` between the inclusions of degrees. This file computes the transitions of
the strict components through `τ_φ` and proves the identity
`AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.StrictTransitionSetsIdentity`, hence the
transition coherence of the strict system of a derived pullback.

## Main definitions

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.degreeTransition`: `τ_φ : d_n ⟶ d_m ∘ X(φ)`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.homEquiv_symm_componentPushforwardTransition_app`: the
  transition `g_n ⟶ g_m ∘ f_φ` of a simplicial site, transposed, is restriction.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictDegreeTwoIso_comp_componentTransition`
  and `augmentation_map_degreeTransition_comp`: the strict and augmentation sides through `τ_φ`.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictTransitionSetsIdentity`.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictAugmentationDegreeDerivedIso_transition`
  and `strictAugmentationDegreeDerivedIso_transition_app`: the transition coherence of the strict
  system of `Lb^*K` (Stacks 0D9P).

## References

* [Stacks Project, Tag 0D9P](https://stacks.math.columbia.edu/tag/0D9P)
* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CategoryTheory.Limits AlgebraicGeometry.RingedToposHom

universe u

namespace CategoryTheory.SimplicialSiteSituation

/-- **The transition `g_n ⟶ g_m ∘ f_φ` of a simplicial site, transposed.** Under restriction to the
component of degree `m` against right Kan extension, the transition of direct images becomes the
restriction transition followed by the counit of degree `n`. -/
theorem homEquiv_symm_componentPushforwardTransition_app (S : SimplicialSiteSituation.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) (H : Sheaf (S.componentTopology n) (Type u)) :
    (((componentFunctor S m).sheafAdjunctionCocontinuous (Type u) (S.componentTopology m)
        S.totalTopology).homEquiv _ _).symm ((S.componentPushforwardTransition φ).app H) =
      (S.restrictTransition φ).app (((componentFunctor S n).sheafPushforwardCocontinuous
          (Type u) (S.componentTopology n) S.totalTopology).obj H) ≫
        (S.transitionMorphism φ).pushforward.map
          (((componentFunctor S n).sheafAdjunctionCocontinuous (Type u) (S.componentTopology n)
            S.totalTopology).counit.app H) := by
  have hE1 : (((componentFunctor S m).sheafAdjunctionCocontinuous (Type u) (S.componentTopology m)
        S.totalTopology).homEquiv _ _).symm ((S.componentPushforwardTransition φ).app H) =
      ((componentFunctor S m).sheafPushforwardContinuous (Type u) (S.componentTopology m)
          S.totalTopology).map ((S.componentPushforwardTransition φ).app H) ≫
        ((componentFunctor S m).sheafAdjunctionCocontinuous (Type u) (S.componentTopology m)
          S.totalTopology).counit.app ((S.transitionMorphism φ).pushforward.obj H) :=
    Adjunction.homEquiv_counit _ _ _ _
  have hum : (S.componentRingedTopos_setRestrictionIso m).hom.app
        ((componentMorphism S m).pushforward.obj ((S.transitionMorphism φ).pushforward.obj H)) ≫
      ((componentFunctor S m).sheafAdjunctionCocontinuous (Type u) (S.componentTopology m)
          S.totalTopology).counit.app ((S.transitionMorphism φ).pushforward.obj H) =
      (componentMorphism S m).adj.counit.app ((S.transitionMorphism φ).pushforward.obj H) :=
    Adjunction.leftAdjointUniq_hom_app_counit _ _ _
  have hun : (S.componentRingedTopos_setRestrictionIso n).hom.app
        ((componentMorphism S n).pushforward.obj H) ≫
      ((componentFunctor S n).sheafAdjunctionCocontinuous (Type u) (S.componentTopology n)
          S.totalTopology).counit.app H =
      (componentMorphism S n).adj.counit.app H :=
    Adjunction.leftAdjointUniq_hom_app_counit _ _ _
  have hnat : (componentMorphism S m).inverseImage.map
        ((S.componentPushforwardTransition φ).app H) ≫
      (S.componentRingedTopos_setRestrictionIso m).hom.app
        ((componentMorphism S m).pushforward.obj ((S.transitionMorphism φ).pushforward.obj H)) =
      (S.componentRingedTopos_setRestrictionIso m).hom.app
        ((componentMorphism S n).pushforward.obj H) ≫
      ((componentFunctor S m).sheafPushforwardContinuous (Type u) (S.componentTopology m)
          S.totalTopology).map ((S.componentPushforwardTransition φ).app H) :=
    (S.componentRingedTopos_setRestrictionIso m).hom.naturality _
  have hc : (S.transitionMorphism φ).inverseImage.map
        ((componentMorphism S m).inverseImage.map ((S.componentPushforwardTransition φ).app H)) ≫
      (S.transitionMorphism φ).inverseImage.map
        ((componentMorphism S m).adj.counit.app ((S.transitionMorphism φ).pushforward.obj H)) ≫
      (S.transitionMorphism φ).adj.counit.app H =
      (S.transitionMorphism φ).inverseImage.map
          ((S.componentRingedTopos_setRestrictionIso m).hom.app
            ((componentMorphism S n).pushforward.obj H)) ≫
        (S.fiberTransition φ).app ((componentMorphism S n).pushforward.obj H) ≫
        (S.componentRingedTopos_setRestrictionIso n).inv.app
          ((componentMorphism S n).pushforward.obj H) ≫
        (componentMorphism S n).adj.counit.app H := by
    have h := conjugateEquiv_counit (componentMorphism S n).adj
      ((componentMorphism S m).comp (S.transitionMorphism φ)).adj
      (S.componentInverseImageTransition φ) H
    have h2 : ((componentMorphism S m).comp (S.transitionMorphism φ)).adj.counit.app H =
        (S.transitionMorphism φ).inverseImage.map
          ((componentMorphism S m).adj.counit.app ((S.transitionMorphism φ).pushforward.obj H)) ≫
        (S.transitionMorphism φ).adj.counit.app H :=
      Adjunction.comp_counit_app _ _ _
    rw [h2] at h
    refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ (h.trans ?_))
    · rw [Category.assoc]
      rfl
    · exact Category.assoc _ _ _
  have hfT : (S.fiberTransition φ).app ((componentMorphism S n).pushforward.obj H) =
      (S.transitionMorphism φ).inverseImage.map ((S.restrictTransition φ).app
          ((componentMorphism S n).pushforward.obj H)) ≫
        (S.transitionMorphism φ).adj.counit.app _ :=
    Adjunction.homEquiv_counit _ _ _ _
  apply ((S.transitionMorphism φ).adj.homEquiv _ _).symm.injective
  refine (Adjunction.homEquiv_counit _ _ _ _).trans
    (Eq.trans ?_ (Adjunction.homEquiv_counit _ _ _ _).symm)
  rw [← cancel_epi ((S.transitionMorphism φ).inverseImage.map
    ((S.componentRingedTopos_setRestrictionIso m).hom.app
      ((componentMorphism S n).pushforward.obj H)))]
  have hin : (S.componentRingedTopos_setRestrictionIso m).hom.app
        ((componentMorphism S n).pushforward.obj H) ≫
      ((componentFunctor S m).sheafPushforwardContinuous (Type u) (S.componentTopology m)
          S.totalTopology).map ((S.componentPushforwardTransition φ).app H) ≫
        ((componentFunctor S m).sheafAdjunctionCocontinuous (Type u) (S.componentTopology m)
          S.totalTopology).counit.app ((S.transitionMorphism φ).pushforward.obj H) =
      (componentMorphism S m).inverseImage.map ((S.componentPushforwardTransition φ).app H) ≫
        (componentMorphism S m).adj.counit.app ((S.transitionMorphism φ).pushforward.obj H) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hnat.symm).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hum)))
  have h3 : (S.componentRingedTopos_setRestrictionIso n).inv.app
        ((componentMorphism S n).pushforward.obj H) ≫ (componentMorphism S n).adj.counit.app H =
      ((componentFunctor S n).sheafAdjunctionCocontinuous (Type u) (S.componentTopology n)
          S.totalTopology).counit.app H :=
    (congrArg (_ ≫ ·) hun.symm).trans (Iso.inv_hom_id_app_assoc _ _ _)
  rw [hE1, ← Functor.map_comp_assoc, hin]
  refine (congrArg (· ≫ _) ((S.transitionMorphism φ).inverseImage.map_comp _ _)).trans
    ((Category.assoc _ _ _).trans (hc.trans ?_))
  exact congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) h3).trans ((congrArg (· ≫ _) hfT).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      ((S.transitionMorphism φ).adj.counit_naturality _).symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
        ((S.transitionMorphism φ).inverseImage.map_comp _ _).symm))))))

/-- **The transition `g_n ⟶ g_m ∘ f_φ` of a simplicial site of case (A), on sections**: followed
by the counit of right Kan extension along the component inclusion of degree `m`, it is
restriction along the cross-fibre arrow `(φ, 𝟙)` followed by the counit in degree `n`. -/
theorem componentPushforwardTransition_app_hom_app_comp_ranCounit (C : SimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n)
    (H : Sheaf ((SimplicialSite.situation C).componentTopology n) (Type u))
    (c : (SimplicialSite.situation C).component m) :
    (((SimplicialSite.situation C).componentPushforwardTransition φ).app H).hom.app
        (op ((componentFunctor (SimplicialSite.situation C) m).obj c)) ≫
      ((componentFunctor (SimplicialSite.situation C) m).op.ranCounit.app
        (((SimplicialSite.situation C).transitionMorphism φ).pushforward.obj H).obj).app (op c) =
      (((componentFunctor (SimplicialSite.situation C) n).op.ran.obj H.obj).map
          ((continuousInclusionTransition C φ).app c).op) ≫
        ((componentFunctor (SimplicialSite.situation C) n).op.ranCounit.app H.obj).app
          (op ((C.underlying.map φ).toFunctor.obj c)) := by
  exact congrArg (fun f ↦ f.hom.app (op c)) ((Adjunction.homEquiv_counit _ _ _ _).symm.trans
    ((SimplicialSite.situation C).homEquiv_symm_componentPushforwardTransition_app φ H))

end CategoryTheory.SimplicialSiteSituation
namespace CategoryTheory.TwoSquare

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ u₁ u₂ u₃ u₄ u₅ u₆ u₇

variable {Cm : Type u₁} {Cn : Type u₂} {T : Type u₃} {Xm : Type u₄} {Xn : Type u₅} {U : Type u₆}
  {A : Type u₇} [Category.{v₁} Cm] [Category.{v₂} Cn] [Category.{v₃} T] [Category.{v₄} Xm]
  [Category.{v₅} Xn] [Category.{v₆} U] [Category.{v₇} A]
  {ιm : Cm ⥤ T} {ιn : Cn ⥤ T} {uφ : Cm ⥤ Cn} {rm : Cm ⥤ Xm} {rn : Cn ⥤ Xn} {Q : T ⥤ U}
  {dm : Xm ⥤ U} {dn : Xn ⥤ U} {bc : Xm ⥤ Xn}
  [∀ F : Cmᵒᵖ ⥤ A, ιm.op.HasRightKanExtension F] [∀ F : Cnᵒᵖ ⥤ A, ιn.op.HasRightKanExtension F]
  [∀ F : Xmᵒᵖ ⥤ A, dm.op.HasRightKanExtension F] [∀ F : Xnᵒᵖ ⥤ A, dn.op.HasRightKanExtension F]

/-- `Stacks.SheafOfModules.ranBaseChange_fac` for the opposite of a 2-square, stated with the
components of the original square. -/
private theorem ranBaseChange_op_fac {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
    [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
    {T' : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄} (w : TwoSquare T' L R B)
    [∀ F : C₁ᵒᵖ ⥤ A, L.op.HasRightKanExtension F] [∀ F : C₂ᵒᵖ ⥤ A, R.op.HasRightKanExtension F]
    (F : C₂ᵒᵖ ⥤ A) (X : C₁) :
    (w.op.ranBaseChange.app F).app (Opposite.op (L.obj X)) ≫
        (L.op.ranCounit.app (T'.op ⋙ F)).app (Opposite.op X) =
      (R.op.ran.obj F).map (w.app X).op ≫
        (R.op.ranCounit.app F).app (Opposite.op (T'.obj X)) :=
  Stacks.SheafOfModules.ranBaseChange_fac w.op F (Opposite.op X)

/-- **Pasting the base changes of right Kan extensions along a transition.** Let `wn`, `wm` be
2-squares `r_k ⋙ d_k ⟶ ι_k ⋙ Q`, `κ : bc ⋙ d_n ⟶ d_m` and `κ' : u ⋙ ι_n ⟶ ι_m` arrows of the
two total categories, and `ρ : u ⋙ r_n ≅ r_m ⋙ bc`, compatible in that
`wn ≫ Q κ' = d_n ρ ≫ κ ≫ wm` at every object. Then for every map `τ'` of right Kan extensions
whose components are restriction along `κ'`, the transition `τ'` read through `wn` is the base
change along `κ` read through `wm` and `ρ`. -/
theorem ranBaseChange_transition_paste (wn : TwoSquare rn ιn dn Q) (wm : TwoSquare rm ιm dm Q)
    (κ : TwoSquare bc dm dn (𝟭 U)) (κ' : uφ ⋙ ιn ⟶ ιm) (ρ : uφ ⋙ rn ≅ rm ⋙ bc)
    (G : Xnᵒᵖ ⥤ A)
    (τ' : ιn.op.ran.obj (rn.op ⋙ G) ⟶ ιm.op.ran.obj (uφ.op ⋙ rn.op ⋙ G))
    (hτ : ∀ c : Cm, τ'.app (Opposite.op (ιm.obj c)) ≫
        (ιm.op.ranCounit.app (uφ.op ⋙ rn.op ⋙ G)).app (Opposite.op c) =
      (ιn.op.ran.obj (rn.op ⋙ G)).map (κ'.app c).op ≫
        (ιn.op.ranCounit.app (rn.op ⋙ G)).app (Opposite.op (uφ.obj c)))
    (hgeo : ∀ c : Cm, wn.app (uφ.obj c) ≫ Q.map (κ'.app c) =
      dn.map (ρ.hom.app c) ≫ κ.app (rm.obj c) ≫ wm.app c) (c : Cm) :
    (wn.op.ranBaseChange.app G).app (Opposite.op (ιm.obj c)) ≫ τ'.app (Opposite.op (ιm.obj c)) ≫
        (ιm.op.ranCounit.app (uφ.op ⋙ rn.op ⋙ G)).app (Opposite.op c) =
      (κ.op.ranBaseChange.app G).app (Opposite.op (Q.obj (ιm.obj c))) ≫
        (wm.op.ranBaseChange.app (bc.op ⋙ G)).app (Opposite.op (ιm.obj c)) ≫
        (ιm.op.ranCounit.app (rm.op ⋙ bc.op ⋙ G)).app (Opposite.op c) ≫ G.map (ρ.hom.app c).op := by
  rw [hτ]
  have n1 := (wn.op.ranBaseChange.app G).naturality (κ'.app c).op
  have f1 := ranBaseChange_op_fac wn G (uφ.obj c)
  have f2 := ranBaseChange_op_fac wm (bc.op ⋙ G) c
  have n2 := (κ.op.ranBaseChange.app G).naturality (wm.app c).op
  have f3 := ranBaseChange_op_fac κ G (rm.obj c)
  have n3 := (dn.op.ranCounit.app G).naturality (ρ.hom.app c).op
  dsimp only [Functor.comp_obj, Functor.whiskeringLeft_obj_obj, Functor.op_obj, Functor.id_obj,
    Functor.comp_map, Functor.whiskeringLeft_obj_map, Functor.op_map, Functor.id_map]
    at n1 n2 n3 f1 f2 f3 ⊢
  rw [← reassoc_of% n1, f1, reassoc_of% f2, ← reassoc_of% n2, reassoc_of% f3, ← n3]
  simp only [Quiver.Hom.unop_op]
  rw [← Functor.map_comp_assoc, ← op_comp, hgeo, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc, ← op_comp, ← op_comp]

/-- **Pasting the base changes of right Kan extensions along an augmentation.** Let `Sm`, `Sn` be
2-squares `pb_k ⋙ d_k ⟶ dc_k ⋙ pa` and `κ : bc ⋙ d_n ⟶ d_m`; let `ε : dc_n V ⟶ dc_m V`,
`gm : Y ⟶ bc (pb_m V)` and `gn : Y ⟶ pb_n V` with `d_n gn ≫ Sn ≫ pa ε = d_n gm ≫ κ ≫ Sm`. Then
the base change along `κ` read through `Sm` and `gm` is restriction along `pa ε` read through `Sn`
and `gn`. -/
theorem ranBaseChange_augmentation_paste {Zc : Type u₁} {K : Type u₂} [Category.{v₁} Zc]
    [Category.{v₂} K] {pa : K ⥤ U} {dcm dcn : Zc ⥤ K} {pbm : Zc ⥤ Xm} {pbn : Zc ⥤ Xn}
    [∀ F : Zcᵒᵖ ⥤ A, dcm.op.HasRightKanExtension F] [∀ F : Zcᵒᵖ ⥤ A, dcn.op.HasRightKanExtension F]
    (Sm : TwoSquare pbm dcm dm pa) (Sn : TwoSquare pbn dcn dn pa) (κ : TwoSquare bc dm dn (𝟭 U))
    (G : Xnᵒᵖ ⥤ A) (V : Zc) {Y : Xn} (gm : Y ⟶ bc.obj (pbm.obj V)) (gn : Y ⟶ pbn.obj V)
    (ε : dcn.obj V ⟶ dcm.obj V)
    (hgeo : dn.map gn ≫ Sn.app V ≫ pa.map ε =
      dn.map gm ≫ κ.app (pbm.obj V) ≫ Sm.app V) :
    (κ.op.ranBaseChange.app G).app (Opposite.op (pa.obj (dcm.obj V))) ≫
        (Sm.op.ranBaseChange.app (bc.op ⋙ G)).app (Opposite.op (dcm.obj V)) ≫
        (dcm.op.ranCounit.app (pbm.op ⋙ bc.op ⋙ G)).app (Opposite.op V) ≫ G.map gm.op =
      (dn.op.ran.obj G).map (pa.map ε).op ≫
        (Sn.op.ranBaseChange.app G).app (Opposite.op (dcn.obj V)) ≫
        (dcn.op.ranCounit.app (pbn.op ⋙ G)).app (Opposite.op V) ≫ G.map gn.op := by
  have f2 := ranBaseChange_op_fac Sm (bc.op ⋙ G) V
  have n2 := (κ.op.ranBaseChange.app G).naturality (Sm.app V).op
  have f3 := ranBaseChange_op_fac κ G (pbm.obj V)
  have n3 := (dn.op.ranCounit.app G).naturality gm.op
  have f1 := ranBaseChange_op_fac Sn G V
  have n4 := (dn.op.ranCounit.app G).naturality gn.op
  dsimp only [Functor.comp_obj, Functor.whiskeringLeft_obj_obj, Functor.op_obj, Functor.id_obj,
    Functor.comp_map, Functor.whiskeringLeft_obj_map, Functor.op_map, Functor.id_map]
    at n2 n3 n4 f1 f2 f3 ⊢
  simp only [Quiver.Hom.unop_op] at n2 n3 n4 ⊢
  rw [reassoc_of% f2, ← reassoc_of% n2, reassoc_of% f3, ← n3, reassoc_of% f1, ← n4]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc, ← op_comp, ← op_comp, ← op_comp, ← op_comp]
  rw [hgeo]

/-- The pasting that combines a transition identity upstairs, a transition identity downstairs and
the naturality of a comparison: if `In ≫ t = τe ≫ Im ≫ s`, `τa ≫ σm ≫ χ = σn` and
`sAn ≫ F τe = τa ≫ sAm`, then `σn⁻¹ ≫ sAn ≫ F In ≫ F t = χ⁻¹ ≫ σm⁻¹ ≫ sAm ≫ F Im ≫ F s`. -/
theorem transition_paste_of_comparisons {C : Type u₁} {D : Type u₂} [Category.{v₁} C]
    [Category.{v₂} D] (F : C ⥤ D) {P A₁ A₂ Q : D} {E₁ E₂ M N R : C} (σn : A₁ ≅ P) (σm : A₂ ≅ Q)
    (χ : Q ≅ P) (sAn : A₁ ⟶ F.obj E₁) (sAm : A₂ ⟶ F.obj E₂) (τa : A₁ ⟶ A₂) (τe : E₁ ⟶ E₂)
    (In : E₁ ⟶ M) (t : M ⟶ N) (Im : E₂ ⟶ R) (s : R ⟶ N) (hI : In ≫ t = τe ≫ Im ≫ s)
    (hII : τa ≫ σm.hom ≫ χ.hom = σn.hom) (hnat : τa ≫ sAm = sAn ≫ F.map τe) :
    σn.inv ≫ sAn ≫ F.map In ≫ F.map t = χ.inv ≫ σm.inv ≫ sAm ≫ F.map Im ≫ F.map s := by
  have h1 : σn.inv ≫ τa = χ.inv ≫ σm.inv := by
    rw [Iso.inv_comp_eq, ← hII]
    simp
  rw [← F.map_comp, hI, F.map_comp, F.map_comp, ← reassoc_of% hnat, reassoc_of% h1]

end CategoryTheory.TwoSquare

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : SimplicialObject (AlgebraicSpaces B S hS))

/-- The morphism `(n, V ×_{X_m} X_n) ⟶ (m, V)` of `X_{spaces,étale}` attached to `φ : [m] ⟶ [n]`
and `V` étale over `X_m`: the first projection, over `X(φ)`. -/
def degreeTransitionHom {m n : SimplexCategory} (φ : m ⟶ n)
    (V : SpacesEtale B S hS (X.obj (op m))) :
    (degreeInclusion X n).obj ((spacesBaseChange B S hS (X.map φ.op)).functor.obj V) ⟶
      (degreeInclusion X m).obj V :=
  ⟨φ, pullback.fst V.1.hom (X.map φ.op), pullback.condition⟩

/-- **The degree transitions as a 2-square**: `X(φ)^{-1}` followed by the inclusion of degree `n`
maps to the inclusion of degree `m`, through `degreeTransitionHom`. -/
def degreeTransitionSquare {m n : SimplexCategory} (φ : m ⟶ n) :
    TwoSquare (spacesBaseChange B S hS (X.map φ.op)).functor (degreeInclusion X m)
      (degreeInclusion X n) (𝟭 _) :=
  TwoSquare.mk _ _ _ _
    { app := degreeTransitionHom X φ
      naturality := fun {_ _} f ↦ Hom.ext ((Category.comp_id _).trans (Category.id_comp _).symm)
        ((spacesBaseChange_map_fst (X.map φ.op) f).trans rfl) }

/-- **The degree transition** `τ_φ : d_{n,*} ⟶ d_{m,*} ∘ X(φ)_*` of direct images of sheaves of
sets, for `φ : [m] ⟶ [n]`: the base change of right Kan extensions along
`degreeTransitionSquare`. -/
def degreeTransition {m n : SimplexCategory} (φ : m ⟶ n) :
    (degreeRingedToposHom X n).toToposHom.pushforward ⟶
      (spacesEtaleRingedToposHom (X.map φ.op)).toToposHom.pushforward ⋙
        (degreeRingedToposHom X m).toToposHom.pushforward where
  app G := ⟨(degreeTransitionSquare X φ).op.ranBaseChange.app G.obj⟩
  naturality {G G'} f := by
    ext : 1
    exact (degreeTransitionSquare X φ).op.ranBaseChange.naturality f.hom

/-- The degree transition on underlying presheaves is the base change of right Kan extensions. -/
theorem degreeTransition_app_hom {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf (SpacesEtale.topology B S hS (X.obj (op n))) (Type (u + 1))) :
    ((degreeTransition X φ).app G).hom = (degreeTransitionSquare X φ).op.ranBaseChange.app G.obj :=
  rfl

/-- The realization squares of degrees `n` and `m` paste with the strict transition and the degree
transition: both composites `(n, realize_n(u_φ c)) ⟶ (m, realize_m c)` are the projection of the
iterated base change, over `X(φ)`. -/
theorem componentRealizeSquare_comp_transition {m n : SimplexCategory} (φ : m ⟶ n)
    (c : (strictSituation X).component m) :
    (componentRealizeSquare X n).app ((componentStrictTransition X φ).obj c) ≫
        (componentTotalComparison X).map
          ((SimplicialSiteSituation.continuousInclusionTransition (strictSimplicialSite X) φ).app
            c) =
      (degreeInclusion X n).map ((componentStrictTransitionRealizeIso X φ).hom.app c) ≫
        (degreeTransitionSquare X φ).app ((componentRealize X m).obj c) ≫
        (componentRealizeSquare X m).app c := by
  refine Hom.ext ?_ ?_
  · rfl
  · change 𝟙 _ ≫ (𝟙 _ ≫ StrictObj.transitionProj φ c) =
      (StrictObj.transitionRealizeIso φ c).hom.hom.left ≫
        (pullback.fst (c.realize.1.hom) (X.map φ.op) ≫ 𝟙 _)
    rw [Category.id_comp, Category.id_comp]
    exact (congrArg (_ ≫ ·) (Category.comp_id _)).symm

/-- **The strict transitions through the degree transition**: for a sheaf of sets `G` on
`(X_n)_{spaces,étale}`, the transition `g_n ⟶ g_m ∘ f_φ` of the strict components at `G`, read
through `e ∘ d_n ≅ g_n ∘ realize_n`, is the degree transition `τ_φ` read through
`e ∘ d_m ≅ g_m ∘ realize_m` and `f_φ ∘ realize_n ≅ realize_m ∘ X(φ)`. -/
theorem strictDegreeTwoIso_comp_componentTransition {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf (SpacesEtale.topology B S hS (X.obj (op n))) (Type (u + 1))) :
    (strictDegreeTwoIso X n).e.hom.app G ≫
        ((strictSituation X).componentRingedTwoMorphism (strictStructureSheaf X) φ).t.app
          ((strictComponentRingedToposHom X n).toToposHom.pushforward.obj G) =
      (strictRingedToposHom X).toToposHom.pushforward.map ((degreeTransition X φ).app G) ≫
        (strictDegreeTwoIso X m).e.hom.app
          ((spacesEtaleRingedToposHom (X.map φ.op)).toToposHom.pushforward.obj G) ≫
        ((strictSituation X).componentRingedToposHom
            (strictStructureSheaf X) m).toToposHom.pushforward.map
          ((strictComponentTransitionTwoIso X φ).e.inv.app G) := by
  refine ObjectProperty.hom_ext _ ?_
  refine Functor.hom_ext_of_isRightKanExtension _
    ((SimplicialSiteSituation.componentFunctor (strictSituation X) m).op.ranCounit.app _) _ _ ?_
  refine NatTrans.ext (funext fun c ↦ ?_)
  have key := TwoSquare.ranBaseChange_transition_paste (componentRealizeSquare X n)
    (componentRealizeSquare X m) (degreeTransitionSquare X φ)
    (SimplicialSiteSituation.continuousInclusionTransition (strictSimplicialSite X) φ)
    (componentStrictTransitionRealizeIso X φ) G.obj
    (((strictSituation X).componentPushforwardTransition φ).app
      ((strictComponentRingedToposHom X n).toToposHom.pushforward.obj G)).hom
    (fun c ↦ SimplicialSiteSituation.componentPushforwardTransition_app_hom_app_comp_ranCounit
      (strictSimplicialSite X) φ _ c) (componentRealizeSquare_comp_transition X φ) c.unop
  have hn := congr_app
    ((SimplicialSiteSituation.componentFunctor (strictSituation X) m).op.ranCounit.naturality
      ((strictComponentTransitionTwoIso X φ).e.inv.app G).hom) c
  refine key.trans ?_
  exact congrArg (fun x ↦ _ ≫ _ ≫ x) hn.symm

/-- The 2-isomorphism of an equality of morphisms of algebraic spaces, on sections: restriction
along the transport of base changes. -/
theorem ofEq_spacesEtaleRingedToposHom_e_hom_app_hom_app {Z₁ Z₂ : AlgebraicSpaces B S hS}
    {f g : Z₁ ⟶ Z₂} (h : f = g) (G : Sheaf (SpacesEtale.topology B S hS Z₁) (Type (u + 1)))
    (V : (SpacesEtale B S hS Z₂)ᵒᵖ) :
    ((TwoIso.ofEq (A := spacesEtaleRingedTopos B S hS Z₁) (B := spacesEtaleRingedTopos B S hS Z₂)
        (congrArg (spacesEtaleRingedToposHom (Z₁ := Z₁) (Z₂ := Z₂)) h)).e.hom.app G).hom.app V =
      G.obj.map (eqToHom (congrArg (fun t ↦ (spacesBaseChange B S hS t).functor.obj V.unop)
        h.symm)).op := by
  subst h
  exact (G.obj.map_id _).symm

section Augmentation

variable {X} {Z : AlgebraicSpaces B S hS} (a : X ⟶ (Functor.const _).obj Z)

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp in
/-- The comparison `a ∘ d_k ≅ a_k` is the direct image along `ε` of the exchange of degrees
followed by `ε ∘ d_k ≅ 𝟙` for the constant simplicial algebraic space. -/
theorem augmentationDegreeTwoIso_e_hom_app (k : SimplexCategory)
    (H : Sheaf (SpacesEtale.topology B S hS (X.obj (op k))) (Type (u + 1))) :
    (augmentationDegreeTwoIso a k).e.hom.app H =
      (constRingedToposHom Z).toToposHom.pushforward.map ((degreeExchangeTwoIso a k).e.hom.app H) ≫
        (constDegreePushforwardIso Z k).hom.app
          ((spacesEtaleRingedToposHom (a.app (op k))).toToposHom.pushforward.obj H) := by
  simp only [comp_toToposHom, augmentationDegreeTwoIso, TwoIso.trans, TwoIso.symm,
    TwoIso.associator, Functor.const_obj_obj, TwoIso.whiskerRight, constDegreeCompTwoIso,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.comp_obj, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.id_obj, Functor.rightUnitor_hom_app, Category.comp_id]
  exact (Category.id_comp _).trans (congrArg (_ ≫ ·) (Category.id_comp _))

/-- `ε ∘ d_k ≅ 𝟙` on direct images is the counit of `d_k⁻¹ ∘ ε⁻¹ ⊣ ε_* ∘ d_{k,*}`. -/
theorem constDegreePushforwardIso_hom_app (k : SimplexCategory)
    (H : Sheaf (SpacesEtale.topology B S hS Z) (Type (u + 1))) :
    (constDegreePushforwardIso Z k).hom.app H = (constDegreeAdj Z k).counit.app H := by
  simp only [Functor.const_obj_obj, Functor.comp_obj, Functor.id_obj, constDegreePushforwardIso,
    conjugateIsoEquiv, Equiv.coe_fn_mk, conjugateEquiv_apply_app, Adjunction.id_unit,
    NatTrans.id_app, Functor.id_map, Category.id_comp]
  exact Category.id_comp _

set_option synthInstance.maxHeartbeats 400000 in
-- instance synthesis for right Kan extensions (`ran`) over the small étale sites of each degree
/-- **The comparison `a ∘ d_k ≅ a_k` on sections over `V/Z`**: projection to the degree-`k` object
`V`, base change of right Kan extensions along the degree square, projection to `V` again, and the
identification of the base changes along `a_k`. -/
theorem augmentationDegreeTwoIso_e_hom_app_hom_app (k : SimplexCategory)
    (H : Sheaf (SpacesEtale.topology B S hS (X.obj (op k))) (Type (u + 1)))
    (V : (SpacesEtale B S hS Z)ᵒᵖ) :
    ((augmentationDegreeTwoIso a k).e.hom.app H).hom.app V =
      ((constForget Z).op.ranCounit.app
          ((pullbackFunctor a).op ⋙ (degreeInclusion X k).op.ran.obj H.obj)).app
          (op ((degreeInclusion ((Functor.const _).obj Z) k).obj V.unop)) ≫
        ((degreeExchangeSquare a k).op.ranBaseChange.app H.obj).app
          (op ((degreeInclusion ((Functor.const _).obj Z) k).obj V.unop)) ≫
        ((degreeInclusion ((Functor.const _).obj Z) k).op.ranCounit.app
          ((degreePullback a k).op ⋙ H.obj)).app V ≫
        H.obj.map ((spacesBaseChangeIso a k).hom.app V.unop).op := by
  rw [augmentationDegreeTwoIso_e_hom_app, constDegreePushforwardIso_hom_app]
  have hL : ((constRingedToposHom Z).toToposHom.pushforward.map
        ((degreeExchangeTwoIso a k).e.hom.app H) ≫ (constDegreeAdj Z k).counit.app
          ((spacesEtaleRingedToposHom (a.app (op k))).toToposHom.pushforward.obj H)).hom.app V =
      ((constForget Z).op.ran.map ((degreeExchangeTwoIso a k).e.hom.app H).hom).app V ≫
        ((constForget Z).op.ranCounit.app
          ((degreeInclusion ((Functor.const _).obj Z) k).op.ran.obj
            ((spacesBaseChange B S hS (a.app (op k))).functor.op ⋙ H.obj))).app
          (op ((degreeInclusion ((Functor.const _).obj Z) k).obj V.unop)) ≫
        ((degreeInclusion ((Functor.const _).obj Z) k).op.ranCounit.app
          ((spacesBaseChange B S hS (a.app (op k))).functor.op ⋙ H.obj)).app V :=
    rfl
  have hD : ((degreeExchangeTwoIso a k).e.hom.app H).hom =
      (degreeExchangeSquare a k).op.ranBaseChange.app H.obj ≫
        (degreeInclusion ((Functor.const _).obj Z) k).op.ran.map
          ((Functor.sheafPushforwardContinuousIso (spacesBaseChangeIso a k).symm (Type (u + 1))
            (SpacesEtale.topology B S hS (((Functor.const _).obj Z).obj (op k)))
            (SpacesEtale.topology B S hS (X.obj (op k)))).hom.app H).hom :=
    rfl
  have n1 : ((constForget Z).op.ran.map ((degreeExchangeTwoIso a k).e.hom.app H).hom).app V ≫
        ((constForget Z).op.ranCounit.app
          ((degreeInclusion ((Functor.const _).obj Z) k).op.ran.obj
            ((spacesBaseChange B S hS (a.app (op k))).functor.op ⋙ H.obj))).app
          (op ((degreeInclusion ((Functor.const _).obj Z) k).obj V.unop)) =
      ((constForget Z).op.ranCounit.app
          ((pullbackFunctor a).op ⋙ (degreeInclusion X k).op.ran.obj H.obj)).app
          (op ((degreeInclusion ((Functor.const _).obj Z) k).obj V.unop)) ≫
        ((degreeExchangeTwoIso a k).e.hom.app H).hom.app
          (op ((degreeInclusion ((Functor.const _).obj Z) k).obj V.unop)) :=
    congr_app ((constForget Z).op.ranCounit.naturality
      ((degreeExchangeTwoIso a k).e.hom.app H).hom)
      (op ((degreeInclusion ((Functor.const _).obj Z) k).obj V.unop))
  have hDx : ((degreeExchangeTwoIso a k).e.hom.app H).hom.app
          (op ((degreeInclusion ((Functor.const _).obj Z) k).obj V.unop)) =
      ((degreeExchangeSquare a k).op.ranBaseChange.app H.obj).app
          (op ((degreeInclusion ((Functor.const _).obj Z) k).obj V.unop)) ≫
        ((degreeInclusion ((Functor.const _).obj Z) k).op.ran.map
          ((Functor.sheafPushforwardContinuousIso (spacesBaseChangeIso a k).symm (Type (u + 1))
            (SpacesEtale.topology B S hS (((Functor.const _).obj Z).obj (op k)))
            (SpacesEtale.topology B S hS (X.obj (op k)))).hom.app H).hom).app
          (op ((degreeInclusion ((Functor.const _).obj Z) k).obj V.unop)) :=
    congr_app hD _
  have n2 : ((degreeInclusion ((Functor.const _).obj Z) k).op.ran.map
          ((Functor.sheafPushforwardContinuousIso (spacesBaseChangeIso a k).symm (Type (u + 1))
            (SpacesEtale.topology B S hS (((Functor.const _).obj Z).obj (op k)))
            (SpacesEtale.topology B S hS (X.obj (op k)))).hom.app H).hom).app
          (op ((degreeInclusion ((Functor.const _).obj Z) k).obj V.unop)) ≫
        ((degreeInclusion ((Functor.const _).obj Z) k).op.ranCounit.app
          ((spacesBaseChange B S hS (a.app (op k))).functor.op ⋙ H.obj)).app V =
      ((degreeInclusion ((Functor.const _).obj Z) k).op.ranCounit.app
          ((degreePullback a k).op ⋙ H.obj)).app V ≫
        H.obj.map ((spacesBaseChangeIso a k).hom.app V.unop).op :=
    congr_app ((degreeInclusion ((Functor.const _).obj Z) k).op.ranCounit.naturality
      ((Functor.sheafPushforwardContinuousIso (spacesBaseChangeIso a k).symm (Type (u + 1))
        (SpacesEtale.topology B S hS (((Functor.const _).obj Z).obj (op k)))
        (SpacesEtale.topology B S hS (X.obj (op k)))).hom.app H).hom) V
  refine hL.trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) n1).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_))))
  exact (congrArg (· ≫ _) hDx).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) n2))

/-- The comparison `a_m ∘ X(φ) ≅ a_n` on sections: restriction along the composition isomorphism of
base changes and the transport along `X(φ) ≫ a_m = a_n`. -/
theorem augmentationTransitionTwoIso_e_hom_app_hom_app {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf (SpacesEtale.topology B S hS (X.obj (op n))) (Type (u + 1)))
    (V : (SpacesEtale B S hS Z)ᵒᵖ) :
    ((augmentationTransitionTwoIso a φ).e.hom.app G).hom.app V =
      G.obj.map ((spacesBaseChange_comp B S hS (X.map φ.op) (a.app (op m))).inv.app V.unop).op ≫
        G.obj.map (eqToHom (congrArg (fun t ↦ (spacesBaseChange B S hS t).functor.obj V.unop)
          (augmentation_map_comp_app a φ).symm)).op := by
  refine (congrArg (· ≫ _) ?_).trans (congrArg (_ ≫ ·)
    (ofEq_spacesEtaleRingedToposHom_e_hom_app_hom_app (augmentation_map_comp_app a φ) G V))
  exact Category.id_comp _

variable (Z) in
/-- The morphism `(n, V) ⟶ (m, V)` of `const(Z)_{spaces,étale}` attached to `φ : [m] ⟶ [n]`: the
identity of `V`, over `const(Z)(φ) = 𝟙`. -/
def constDegreeTransitionHom {m n : SimplexCategory} (φ : m ⟶ n) (V : SpacesEtale B S hS Z) :
    (degreeInclusion ((Functor.const _).obj Z) n).obj V ⟶
      (degreeInclusion ((Functor.const _).obj Z) m).obj V :=
  ⟨φ, 𝟙 _, (Category.id_comp _).trans (Category.comp_id _).symm⟩

/-- Forgetting the degree sends `constDegreeTransitionHom` to the identity. -/
theorem constForget_map_constDegreeTransitionHom {m n : SimplexCategory} (φ : m ⟶ n)
    (V : SpacesEtale B S hS Z) :
    (constForget Z).map (constDegreeTransitionHom Z φ V) = 𝟙 V :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext rfl)

/-- The degree squares of base change along `a` paste with the degree transition: both
composites `(n, V ×_Z X_n) ⟶ (m, V ×_Z X_m)` are the map of fibre products over `X(φ)`. -/
theorem degreeExchangeSquare_comp_transition {m n : SimplexCategory} (φ : m ⟶ n)
    (V : SpacesEtale B S hS Z) :
    (degreeInclusion X n).map ((spacesBaseChangeIso a n).hom.app V) ≫
        (degreeExchangeSquare a n).app V ≫
        (pullbackFunctor a).map (constDegreeTransitionHom Z φ V) =
      (degreeInclusion X n).map
          (eqToHom (congrArg (fun t ↦ (spacesBaseChange B S hS t).functor.obj V)
            (augmentation_map_comp_app a φ).symm) ≫
          (spacesBaseChange_comp B S hS (X.map φ.op) (a.app (op m))).inv.app V ≫
          (spacesBaseChange B S hS (X.map φ.op)).functor.map
            ((spacesBaseChangeIso a m).hom.app V)) ≫
        (degreeTransitionSquare X φ).app ((degreePullback a m).obj V) ≫
        (degreeExchangeSquare a m).app V := by
  refine Hom.ext ?_ ?_
  · rfl
  · simp only [comp_hom, degreeInclusion_map_hom]
    have hfst : ((spacesBaseChange B S hS (X.map φ.op)).functor.map
          ((spacesBaseChangeIso a m).hom.app V)).hom.left ≫
          pullback.fst (pullback.snd V.1.hom (a.app (op m))) (X.map φ.op) =
        pullback.fst (pullback.snd V.1.hom (a.app (op m))) (X.map φ.op) :=
      (spacesBaseChange_map_fst _ _).trans (Category.comp_id _)
    have hc := spacesBaseChange_comp_inv_app_hom_left_fst_fst (X.map φ.op) (a.app (op m)) V
    have he := spacesBaseChange_eqToHom_hom_left_fst (augmentation_map_comp_app a φ).symm V
    apply pullback.hom_ext
    · change (𝟙 _ ≫ 𝟙 _ ≫ ((pullbackFunctor a).map (constDegreeTransitionHom Z φ V)).hom) ≫
          pullback.fst V.1.hom (a.app (op m)) =
        ((eqToHom (congrArg (fun t ↦ (spacesBaseChange B S hS t).functor.obj V)
            (augmentation_map_comp_app a φ).symm)).hom.left ≫
          ((spacesBaseChange_comp B S hS (X.map φ.op) (a.app (op m))).inv.app V).hom.left ≫
          ((spacesBaseChange B S hS (X.map φ.op)).functor.map
            ((spacesBaseChangeIso a m).hom.app V)).hom.left ≫
          pullback.fst (pullback.snd V.1.hom (a.app (op m))) (X.map φ.op)) ≫
          pullback.fst V.1.hom (a.app (op m))
      have hA : ((pullbackFunctor a).map (constDegreeTransitionHom Z φ V)).hom ≫
          pullback.fst V.1.hom (a.app (op m)) = pullback.fst V.1.hom (a.app (op n)) :=
        (pullback.lift_fst _ _ _).trans (Category.comp_id _)
      have hR : ((eqToHom (congrArg (fun t ↦ (spacesBaseChange B S hS t).functor.obj V)
            (augmentation_map_comp_app a φ).symm)).hom.left ≫
          ((spacesBaseChange_comp B S hS (X.map φ.op) (a.app (op m))).inv.app V).hom.left ≫
          ((spacesBaseChange B S hS (X.map φ.op)).functor.map
            ((spacesBaseChangeIso a m).hom.app V)).hom.left ≫
          pullback.fst (pullback.snd V.1.hom (a.app (op m))) (X.map φ.op)) ≫
          pullback.fst V.1.hom (a.app (op m)) = pullback.fst V.1.hom (a.app (op n)) := by
        simp only [Category.assoc]
        rw [reassoc_of% hfst, hc, he]
      exact ((Category.id_comp _).trans (Category.id_comp _) =≫ _).trans (hA.trans hR.symm)
    · change (𝟙 _ ≫ 𝟙 _ ≫ ((pullbackFunctor a).map (constDegreeTransitionHom Z φ V)).hom) ≫
          pullback.snd V.1.hom (a.app (op m)) =
        ((eqToHom (congrArg (fun t ↦ (spacesBaseChange B S hS t).functor.obj V)
            (augmentation_map_comp_app a φ).symm) ≫
          (spacesBaseChange_comp B S hS (X.map φ.op) (a.app (op m))).inv.app V ≫
          (spacesBaseChange B S hS (X.map φ.op)).functor.map
            ((spacesBaseChangeIso a m).hom.app V)).hom.left ≫
          pullback.fst (pullback.snd V.1.hom (a.app (op m))) (X.map φ.op)) ≫
          pullback.snd V.1.hom (a.app (op m))
      have hA : ((pullbackFunctor a).map (constDegreeTransitionHom Z φ V)).hom ≫
          pullback.snd V.1.hom (a.app (op m)) = pullback.snd V.1.hom (a.app (op n)) ≫ X.map φ.op :=
        pullback.lift_snd _ _ _
      have hw := Over.w (eqToHom (congrArg (fun t ↦ (spacesBaseChange B S hS t).functor.obj V)
            (augmentation_map_comp_app a φ).symm) ≫
          (spacesBaseChange_comp B S hS (X.map φ.op) (a.app (op m))).inv.app V ≫
          (spacesBaseChange B S hS (X.map φ.op)).functor.map
            ((spacesBaseChangeIso a m).hom.app V)).hom
      have hR : (((eqToHom (congrArg (fun t ↦ (spacesBaseChange B S hS t).functor.obj V)
            (augmentation_map_comp_app a φ).symm) ≫
          (spacesBaseChange_comp B S hS (X.map φ.op) (a.app (op m))).inv.app V ≫
          (spacesBaseChange B S hS (X.map φ.op)).functor.map
            ((spacesBaseChangeIso a m).hom.app V)).hom.left ≫
          pullback.fst (pullback.snd V.1.hom (a.app (op m))) (X.map φ.op)) ≫
          pullback.snd V.1.hom (a.app (op m))) =
          pullback.snd V.1.hom (a.app (op n)) ≫ X.map φ.op :=
        (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ X.map φ.op) hw)))
      exact ((Category.id_comp _).trans (Category.id_comp _) =≫ _).trans (hA.trans hR.symm)

set_option synthInstance.maxHeartbeats 400000 in
-- instance synthesis for right Kan extensions (`ran`) over the small étale sites of each degree
/-- **The augmentation through the degree transition**, in the direction of the direct images:
`a ∘ d_n ≅ a_n` is `a_*τ_φ` followed by `a ∘ d_m ≅ a_m` and `a_m ∘ X(φ) ≅ a_n`. -/
theorem augmentation_map_degreeTransition_comp {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf (SpacesEtale.topology B S hS (X.obj (op n))) (Type (u + 1))) :
    (augmentationRingedToposHom a).toToposHom.pushforward.map ((degreeTransition X φ).app G) ≫
        (augmentationDegreeTwoIso a m).e.hom.app
          ((spacesEtaleRingedToposHom (X.map φ.op)).toToposHom.pushforward.obj G) ≫
        (augmentationTransitionTwoIso a φ).e.hom.app G =
      (augmentationDegreeTwoIso a n).e.hom.app G := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V ↦ ?_))
  have key := TwoSquare.ranBaseChange_augmentation_paste (degreeExchangeSquare a m)
    (degreeExchangeSquare a n) (degreeTransitionSquare X φ) G.obj V.unop
    (eqToHom (congrArg (fun t ↦ (spacesBaseChange B S hS t).functor.obj V.unop)
          (augmentation_map_comp_app a φ).symm) ≫
        (spacesBaseChange_comp B S hS (X.map φ.op) (a.app (op m))).inv.app V.unop ≫
        (spacesBaseChange B S hS (X.map φ.op)).functor.map
          ((spacesBaseChangeIso a m).hom.app V.unop))
    ((spacesBaseChangeIso a n).hom.app V.unop) (constDegreeTransitionHom Z φ V.unop)
    (degreeExchangeSquare_comp_transition a φ V.unop)
  have hm : ((augmentationDegreeTwoIso a m).e.hom.app
        ((spacesEtaleRingedToposHom (X.map φ.op)).toToposHom.pushforward.obj G)).hom.app V =
      ((constForget Z).op.ranCounit.app
        ((pullbackFunctor a).op ⋙ (degreeInclusion X m).op.ran.obj
          ((spacesBaseChange B S hS (X.map φ.op)).functor.op ⋙ G.obj))).app
        (op ((degreeInclusion ((Functor.const _).obj Z) m).obj V.unop)) ≫
      ((degreeExchangeSquare a m).op.ranBaseChange.app
          ((spacesBaseChange B S hS (X.map φ.op)).functor.op ⋙ G.obj)).app
          (op ((degreeInclusion ((Functor.const _).obj Z) m).obj V.unop)) ≫
        ((degreeInclusion ((Functor.const _).obj Z) m).op.ranCounit.app
          ((degreePullback a m).op ⋙ (spacesBaseChange B S hS (X.map φ.op)).functor.op ⋙
            G.obj)).app V ≫
        G.obj.map ((spacesBaseChange B S hS (X.map φ.op)).functor.map
          ((spacesBaseChangeIso a m).hom.app V.unop)).op :=
    augmentationDegreeTwoIso_e_hom_app_hom_app a m
      ((spacesEtaleRingedToposHom (X.map φ.op)).toToposHom.pushforward.obj G) V
  have hn := augmentationDegreeTwoIso_e_hom_app_hom_app a n G V
  have hx := augmentationTransitionTwoIso_e_hom_app_hom_app a φ G V
  have n0 := congr_app ((constForget Z).op.ranCounit.naturality
    (Functor.whiskerLeft (pullbackFunctor a).op ((degreeTransition X φ).app G).hom))
    (op ((degreeInclusion ((Functor.const _).obj Z) m).obj V.unop))
  have nc := ((constForget Z).op.ranCounit.app
    ((pullbackFunctor a).op ⋙ (degreeInclusion X n).op.ran.obj G.obj)).naturality
    (constDegreeTransitionHom Z φ V.unop).op
  change ((constForget Z).op.ran.map
      (Functor.whiskerLeft (pullbackFunctor a).op ((degreeTransition X φ).app G).hom)).app V ≫
      ((augmentationDegreeTwoIso a m).e.hom.app
        ((spacesEtaleRingedToposHom (X.map φ.op)).toToposHom.pushforward.obj G)).hom.app V ≫
      ((augmentationTransitionTwoIso a φ).e.hom.app G).hom.app V = _
  rw [hm, hx, hn]
  have nc' : ((constForget Z).op.ranCounit.app
        ((pullbackFunctor a).op ⋙ (degreeInclusion X n).op.ran.obj G.obj)).app
        (op ((degreeInclusion ((Functor.const _).obj Z) n).obj V.unop)) =
      ((constForget Z).op.ranCounit.app
        ((pullbackFunctor a).op ⋙ (degreeInclusion X n).op.ran.obj G.obj)).app
        (op ((degreeInclusion ((Functor.const _).obj Z) m).obj V.unop)) ≫
      ((degreeInclusion X n).op.ran.obj G.obj).map
        ((pullbackFunctor a).map (constDegreeTransitionHom Z φ V.unop)).op := by
    refine Eq.trans ?_ nc
    refine (Category.id_comp _).symm.trans (congrArg (· ≫ _) ?_)
    change 𝟙 _ = (((constForget Z).op.ran.obj
      ((pullbackFunctor a).op ⋙ (degreeInclusion X n).op.ran.obj G.obj)).map
        ((constForget Z).map (constDegreeTransitionHom Z φ V.unop)).op)
    rw [constForget_map_constDegreeTransitionHom]
    exact ((((constForget Z).op.ran.obj
      ((pullbackFunctor a).op ⋙ (degreeInclusion X n).op.ran.obj G.obj)).map_id _)).symm
  have n0' : ((constForget Z).op.ran.map
        (Functor.whiskerLeft (pullbackFunctor a).op ((degreeTransition X φ).app G).hom)).app V ≫
      ((constForget Z).op.ranCounit.app
        ((pullbackFunctor a).op ⋙ (degreeInclusion X m).op.ran.obj
          ((spacesBaseChange B S hS (X.map φ.op)).functor.op ⋙ G.obj))).app
        (op ((degreeInclusion ((Functor.const _).obj Z) m).obj V.unop)) =
      ((constForget Z).op.ranCounit.app
        ((pullbackFunctor a).op ⋙ (degreeInclusion X n).op.ran.obj G.obj)).app
        (op ((degreeInclusion ((Functor.const _).obj Z) m).obj V.unop)) ≫
      ((degreeTransitionSquare X φ).op.ranBaseChange.app G.obj).app
        (op ((pullbackFunctor a).obj ((degreeInclusion ((Functor.const _).obj Z) m).obj V.unop))) :=
    n0
  have hG : G.obj.map ((spacesBaseChange B S hS (X.map φ.op)).functor.map
          ((spacesBaseChangeIso a m).hom.app V.unop)).op ≫
      G.obj.map ((spacesBaseChange_comp B S hS (X.map φ.op) (a.app (op m))).inv.app V.unop).op ≫
      G.obj.map (eqToHom (congrArg (fun t ↦ (spacesBaseChange B S hS t).functor.obj V.unop)
          (augmentation_map_comp_app a φ).symm)).op =
      G.obj.map (eqToHom (congrArg (fun t ↦ (spacesBaseChange B S hS t).functor.obj V.unop)
          (augmentation_map_comp_app a φ).symm) ≫
        (spacesBaseChange_comp B S hS (X.map φ.op) (a.app (op m))).inv.app V.unop ≫
        (spacesBaseChange B S hS (X.map φ.op)).functor.map
          ((spacesBaseChangeIso a m).hom.app V.unop)).op := by
    rw [op_comp, op_comp, G.obj.map_comp, G.obj.map_comp]
    exact (Category.assoc _ _ _).symm
  rw [nc']
  change (((constForget Z).op.ran.map
        (Functor.whiskerLeft (pullbackFunctor a).op ((degreeTransition X φ).app G).hom)).app V ≫
      ((constForget Z).op.ranCounit.app
        ((pullbackFunctor a).op ⋙ (degreeInclusion X m).op.ran.obj
          ((spacesBaseChange B S hS (X.map φ.op)).functor.op ⋙ G.obj))).app
        (op ((degreeInclusion ((Functor.const _).obj Z) m).obj V.unop))) ≫
      (((degreeExchangeSquare a m).op.ranBaseChange.app
          ((spacesBaseChange B S hS (X.map φ.op)).functor.op ⋙ G.obj)).app
          (op ((degreeInclusion ((Functor.const _).obj Z) m).obj V.unop)) ≫
        ((degreeInclusion ((Functor.const _).obj Z) m).op.ranCounit.app
          ((degreePullback a m).op ⋙ (spacesBaseChange B S hS (X.map φ.op)).functor.op ⋙
            G.obj)).app V ≫
        (G.obj.map ((spacesBaseChange B S hS (X.map φ.op)).functor.map
            ((spacesBaseChangeIso a m).hom.app V.unop)).op ≫
          G.obj.map ((spacesBaseChange_comp B S hS (X.map φ.op) (a.app (op m))).inv.app V.unop).op ≫
          G.obj.map (eqToHom (congrArg (fun t ↦ (spacesBaseChange B S hS t).functor.obj V.unop)
            (augmentation_map_comp_app a φ).symm)).op)) = _
  rw [n0', hG]
  exact congrArg (_ ≫ ·) key

/-- **The transition identity of the strict model on direct images of sheaves of sets** holds for
every `φ : [m] ⟶ [n]`: both comparisons `a_{n*}G ⟶ b_* g_{m*} f_{φ*} sc_{n*} G` factor through
the degree transition `τ_φ`. -/
theorem strictTransitionSetsIdentity {m n : SimplexCategory} (φ : m ⟶ n) :
    StrictTransitionSetsIdentity a φ := by
  refine ⟨fun G ↦ ?_⟩
  exact TwoSquare.transition_paste_of_comparisons
    (strictAugmentationRingedToposHom a).toToposHom.pushforward
    ((augmentationDegreeTwoIso a n).e.app G)
    ((augmentationDegreeTwoIso a m).e.app
      ((spacesEtaleRingedToposHom (X.map φ.op)).toToposHom.pushforward.obj G))
    ((augmentationTransitionTwoIso a φ).e.app G)
    ((strictAugmentationTwoIso a).e.inv.app
      ((degreeRingedToposHom X n).toToposHom.pushforward.obj G))
    ((strictAugmentationTwoIso a).e.inv.app ((degreeRingedToposHom X m).toToposHom.pushforward.obj
      ((spacesEtaleRingedToposHom (X.map φ.op)).toToposHom.pushforward.obj G)))
    ((augmentationRingedToposHom a).toToposHom.pushforward.map ((degreeTransition X φ).app G))
    ((strictRingedToposHom X).toToposHom.pushforward.map ((degreeTransition X φ).app G))
    ((strictDegreeTwoIso X n).e.hom.app G)
    (((strictSituation X).componentRingedTwoMorphism (strictStructureSheaf X) φ).t.app
      ((strictComponentRingedToposHom X n).toToposHom.pushforward.obj G))
    ((strictDegreeTwoIso X m).e.hom.app
      ((spacesEtaleRingedToposHom (X.map φ.op)).toToposHom.pushforward.obj G))
    (((strictSituation X).componentRingedToposHom
        (strictStructureSheaf X) m).toToposHom.pushforward.map
      ((strictComponentTransitionTwoIso X φ).e.inv.app G))
    (strictDegreeTwoIso_comp_componentTransition X φ G)
    (augmentation_map_degreeTransition_comp a φ G)
    ((strictAugmentationTwoIso a).e.inv.naturality ((degreeTransition X φ).app G))

end Augmentation

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : SimplicialObject (AlgebraicSpaces B S hS)} {Z : AlgebraicSpaces B S hS}
  (a : X ⟶ (Functor.const _).obj Z)

/-- **The transition coherence of the strict system of `Lb^*K`** (Stacks 0D9P for the strict
model of an augmented simplicial algebraic space): the derived transition of the system of
`Lb^*K` along `φ : [m] ⟶ [n]`, read through the component isomorphisms
`Lb^* ⋙ D(g_n^{-1}) ⋙ L realize_n^* ≅ La_n^*`, is the derived square of the strict transitions
followed by `La_m^* ⋙ LX(φ)^* ≅ La_n^*`. -/
theorem strictAugmentationDegreeDerivedIso_transition {m n : SimplexCategory} (φ : m ⟶ n) :
    Functor.whiskerLeft (derivedPullback (X := strictRingedTopos X)
          (Y := spacesEtaleRingedTopos B S hS Z) (strictAugmentationRingedToposHom a))
        (Functor.whiskerRight
          ((strictSituation X).derivedComponentModuleTransition (strictStructureSheaf X) φ)
          (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
            (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
            (strictComponentRingedToposHom X n))) ≫
      (strictAugmentationDegreeDerivedIso a n).hom =
    Functor.whiskerLeft (derivedPullback (X := strictRingedTopos X)
          (Y := spacesEtaleRingedTopos B S hS Z) (strictAugmentationRingedToposHom a))
        (Functor.whiskerLeft
          ((strictSituation X).derivedComponentModuleRestriction (strictStructureSheaf X) m)
          (strictComponentDerivedTransitionIso X φ).hom) ≫
      Functor.whiskerRight (strictAugmentationDegreeDerivedIso a m).hom
        (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := spacesEtaleRingedTopos B S hS (X.obj (op m)))
          (spacesEtaleRingedToposHom (X.map φ.op))) ≫
      (augmentationTransitionDerivedIso a φ).hom :=
  strictAugmentationDegreeDerivedIso_transition_of_homotopy a φ
    (strictTransitionHomotopyIdentity_of_sheafIdentity a φ
      (strictTransitionSheafIdentity_of_setsIdentity a φ (strictTransitionSetsIdentity a φ)))

/-- `strictAugmentationDegreeDerivedIso_transition` at an object `K` of `D(Z)`. -/
theorem strictAugmentationDegreeDerivedIso_transition_app {m n : SimplexCategory}
    (φ : m ⟶ n)
    (K : @DerivedCategory (spacesEtaleRingedTopos B S hS Z).Modules _ _
      (HasDerivedCategory.standard _)) :
    (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
        (strictComponentRingedToposHom X n)).map
        (((strictSituation X).derivedComponentModuleTransition (strictStructureSheaf X) φ).app
          ((derivedPullback (X := strictRingedTopos X) (Y := spacesEtaleRingedTopos B S hS Z)
          (strictAugmentationRingedToposHom a)).obj K)) ≫
      (strictAugmentationDegreeDerivedIso a n).hom.app K =
    (strictComponentDerivedTransitionIso X φ).hom.app
        (((strictSituation X).derivedComponentModuleRestriction (strictStructureSheaf X) m).obj
          ((derivedPullback (X := strictRingedTopos X) (Y := spacesEtaleRingedTopos B S hS Z)
          (strictAugmentationRingedToposHom a)).obj K)) ≫
      (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := spacesEtaleRingedTopos B S hS (X.obj (op m)))
          (spacesEtaleRingedToposHom (X.map φ.op))).map
        ((strictAugmentationDegreeDerivedIso a m).hom.app K) ≫
      (augmentationTransitionDerivedIso a φ).hom.app K :=
  strictAugmentationDegreeDerivedIso_transition_app_of_homotopy a φ
    (strictTransitionHomotopyIdentity_of_sheafIdentity a φ
      (strictTransitionSheafIdentity_of_setsIdentity a φ (strictTransitionSetsIdentity a φ))) K

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite
