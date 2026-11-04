module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import StacksFrontier.CategoryTheory.Functor.KanExtension.Postcomposition

/-!
# Pullback of sheaves and change of coefficient category

Let `F : C ⥤ D` be a continuous functor between sites and let `G : A ⥤ B` be a functor between
coefficient categories along which sheaves may be composed. Pushforward of sheaves is
postcomposition on underlying presheaves, so it commutes with `G` on the nose; the adjoint
transpose of that identity is a canonical comparison `F^*(G ∘ S) ⟶ G ∘ F^*(S)` between the two
ways of pulling back a sheaf and changing coefficients. It is an isomorphism as soon as `G`
preserves the colimits computing the presheaf-level left Kan extension along `F.op` and
preserves sheafification, because both sides are then sheafifications of the same presheaf.

## Main definitions

* `CategoryTheory.Functor.sheafPullbackPresheafUnit` is the universal map from the presheaf-level
  left Kan extension of a sheaf along `F.op` to the underlying presheaf of its sheaf pullback.
* `CategoryTheory.Functor.sheafPullbackHomEquivPresheaf` is the bijection it induces on
  morphisms, which expresses the sheaf pullback as a sheafification of the presheaf pullback.
* `CategoryTheory.Functor.sheafPullbackSheafComposeHom` is the comparison
  `F^*(G ∘ S) ⟶ G ∘ F^*(S)`, and
  `CategoryTheory.Functor.sheafPullbackSheafComposeIso` is it as an isomorphism.

## Main results

* `CategoryTheory.Functor.W_sheafPullbackPresheafUnit`: the universal map above is a local
  isomorphism.
* `CategoryTheory.Functor.unit_comp_pushforward_map_sheafPullbackSheafComposeHom` characterises
  the comparison by its adjoint transpose, namely `G` applied to the unit of the
  pullback/pushforward adjunction.
* `CategoryTheory.Functor.sheafPullbackPresheafUnit_comp_sheafPullbackSheafComposeHom`
  identifies the comparison, on underlying presheaves, with the comparison
  `CategoryTheory.Functor.lanCompRightIso` for left Kan extensions.
* `CategoryTheory.Functor.isIso_sheafPullbackSheafComposeHom`: the comparison is an isomorphism.

## Implementation notes

Everything is phrased for `CategoryTheory.Functor.sheafPullback`, which is a *chosen* left
adjoint of the pushforward rather than an explicit construction, so no step unfolds it; the only
inputs used about it are the adjunction `sheafAdjunctionContinuous` and the identity
`sheafPushforwardContinuous ⋙ sheafToPresheaf = sheafToPresheaf ⋙ (- ∘ F.op)`.

## References

* [Stacks Project, Tag 00WX](https://stacks.math.columbia.edu/tag/00WX)
-/

@[expose] public section

open CategoryTheory.Limits

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (F : C ⥤ D)
  (A : Type u₃) [Category.{v₃} A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K] [HasWeakSheafify K A] [∀ P : Cᵒᵖ ⥤ A, F.op.HasLeftKanExtension P]

/-- The universal map from the presheaf-level left Kan extension of a sheaf `S` along `F.op` to
the underlying presheaf of the sheaf pullback of `S`: the adjoint transpose of the unit of the
pullback/pushforward adjunction on sheaves. -/
noncomputable def sheafPullbackPresheafUnit (S : Sheaf J A) :
    F.op.lan.obj S.obj ⟶ ((F.sheafPullback A J K).obj S).obj :=
  ((F.op.lanAdjunction A).homEquiv _ _).symm
    ((sheafToPresheaf J A).map ((F.sheafAdjunctionContinuous A J K).unit.app S))

/-- The sheaf pullback of `S` is a sheafification of the presheaf-level left Kan extension of `S`
along `F.op`: morphisms from it to a sheaf `T` are morphisms of presheaves from that left Kan
extension to `T`. -/
noncomputable def sheafPullbackHomEquivPresheaf (S : Sheaf J A) (T : Sheaf K A) :
    ((F.sheafPullback A J K).obj S ⟶ T) ≃ (F.op.lan.obj S.obj ⟶ T.obj) :=
  ((F.sheafAdjunctionContinuous A J K).homEquiv S T).trans
    (Sheaf.homEquiv.trans ((F.op.lanAdjunction A).homEquiv S.obj T.obj).symm)

/-- The bijection `sheafPullbackHomEquivPresheaf` is composition with
`sheafPullbackPresheafUnit`. -/
lemma sheafPullbackHomEquivPresheaf_apply (S : Sheaf J A) (T : Sheaf K A)
    (g : (F.sheafPullback A J K).obj S ⟶ T) :
    F.sheafPullbackHomEquivPresheaf A J K S T g =
      F.sheafPullbackPresheafUnit A J K S ≫ (sheafToPresheaf K A).map g :=
  (F.op.lanAdjunction A).homEquiv_naturality_right_symm
    ((sheafToPresheaf J A).map ((F.sheafAdjunctionContinuous A J K).unit.app S))
    ((sheafToPresheaf K A).map g)

/-- The adjoint transpose of `sheafPullbackHomEquivPresheaf g` is the underlying morphism of
presheaves of the adjoint transpose of `g` for the pullback/pushforward adjunction on sheaves. -/
lemma lanAdjunction_homEquiv_sheafPullbackHomEquivPresheaf (S : Sheaf J A) (T : Sheaf K A)
    (g : (F.sheafPullback A J K).obj S ⟶ T) :
    (F.op.lanAdjunction A).homEquiv _ _ (F.sheafPullbackHomEquivPresheaf A J K S T g) =
      (sheafToPresheaf J A).map ((F.sheafAdjunctionContinuous A J K).homEquiv S T g) :=
  Equiv.apply_symm_apply _ _

section

variable (S : Sheaf J A)

/-- The unit of an adjunction followed by the right adjoint of a transpose is the original map. -/
private lemma unit_app_comp_map_homEquiv_symm {E E' : Type*} [Category E] [Category E']
    {L : E ⥤ E'} {R : E' ⥤ E} (adj : L ⊣ R) {X : E} {Y : E'} (f : X ⟶ R.obj Y) :
    adj.unit.app X ≫ R.map ((adj.homEquiv X Y).symm f) = f :=
  (adj.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- The morphism from the sheafification of the presheaf-level left Kan extension of `S` to the
sheaf pullback of `S` induced by `sheafPullbackPresheafUnit`. -/
noncomputable def sheafPullbackSheafifyComparison :
    (presheafToSheaf K A).obj (F.op.lan.obj S.obj) ⟶ (F.sheafPullback A J K).obj S :=
  ((sheafificationAdjunction K A).homEquiv _ _).symm (F.sheafPullbackPresheafUnit A J K S)

/-- The unit of sheafification followed by `sheafPullbackSheafifyComparison` is
`sheafPullbackPresheafUnit`. -/
lemma unit_comp_sheafPullbackSheafifyComparison :
    (sheafificationAdjunction K A).unit.app (F.op.lan.obj S.obj) ≫
        (sheafToPresheaf K A).map (F.sheafPullbackSheafifyComparison A J K S) =
      F.sheafPullbackPresheafUnit A J K S :=
  unit_app_comp_map_homEquiv_symm (sheafificationAdjunction K A) _

/-- The inverse of `sheafPullbackSheafifyComparison`, obtained from the universal property of the
sheaf pullback applied to the unit of sheafification. -/
noncomputable def sheafPullbackSheafifyComparisonInv :
    (F.sheafPullback A J K).obj S ⟶ (presheafToSheaf K A).obj (F.op.lan.obj S.obj) :=
  (F.sheafPullbackHomEquivPresheaf A J K S _).symm
    ((sheafificationAdjunction K A).unit.app (F.op.lan.obj S.obj))

/-- `sheafPullbackPresheafUnit` followed by `sheafPullbackSheafifyComparisonInv` is the unit of
sheafification. -/
lemma sheafPullbackPresheafUnit_comp_inv :
    F.sheafPullbackPresheafUnit A J K S ≫
        (sheafToPresheaf K A).map (F.sheafPullbackSheafifyComparisonInv A J K S) =
      (sheafificationAdjunction K A).unit.app (F.op.lan.obj S.obj) := by
  rw [← F.sheafPullbackHomEquivPresheaf_apply A J K, sheafPullbackSheafifyComparisonInv,
    Equiv.apply_symm_apply]

/-- The comparison `sheafPullbackSheafifyComparison` is an isomorphism, with inverse
`sheafPullbackSheafifyComparisonInv`. -/
instance : IsIso (F.sheafPullbackSheafifyComparison A J K S) := by
  refine ⟨F.sheafPullbackSheafifyComparisonInv A J K S, ?_, ?_⟩
  · apply ((sheafificationAdjunction K A).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
      ← Category.assoc, unit_comp_sheafPullbackSheafifyComparison,
      sheafPullbackPresheafUnit_comp_inv]
    simp
  · apply (F.sheafPullbackHomEquivPresheaf A J K S _).injective
    rw [sheafPullbackHomEquivPresheaf_apply, sheafPullbackHomEquivPresheaf_apply,
      Functor.map_comp, ← Category.assoc, sheafPullbackPresheafUnit_comp_inv,
      unit_comp_sheafPullbackSheafifyComparison]
    simp

/-- The universal map to the underlying presheaf of a sheaf pullback is a local isomorphism. -/
lemma W_sheafPullbackPresheafUnit : K.W (F.sheafPullbackPresheafUnit A J K S) := by
  rw [← unit_comp_sheafPullbackSheafifyComparison, K.W_iff, Functor.map_comp]
  have h : IsIso ((presheafToSheaf K A).map
      ((sheafificationAdjunction K A).unit.app (F.op.lan.obj S.obj))) := by
    rw [← K.W_iff]
    exact K.W_adj_unit_app (sheafificationAdjunction K A) _
  infer_instance

/-- A local isomorphism from the presheaf-level left Kan extension of `S` to a sheaf `T` exhibits
`T` as a sheaf pullback of `S`. -/
lemma isIso_of_W_sheafPullbackHomEquivPresheaf_symm (T : Sheaf K A)
    (w : F.op.lan.obj S.obj ⟶ T.obj) (hw : K.W w) :
    IsIso ((F.sheafPullbackHomEquivPresheaf A J K S T).symm w) := by
  have hcomp : F.sheafPullbackPresheafUnit A J K S ≫ (sheafToPresheaf K A).map
      ((F.sheafPullbackHomEquivPresheaf A J K S T).symm w) = w := by
    rw [← F.sheafPullbackHomEquivPresheaf_apply A J K, Equiv.apply_symm_apply]
  rw [← K.W_sheafToPresheaf_map_iff_isIso]
  have h₁ := F.W_sheafPullbackPresheafUnit A J K S
  rw [K.W_iff] at h₁ hw ⊢
  rw [← hcomp, Functor.map_comp] at hw
  exact IsIso.of_isIso_comp_left
    ((presheafToSheaf K A).map (F.sheafPullbackPresheafUnit A J K S))
    ((presheafToSheaf K A).map ((sheafToPresheaf K A).map
      ((F.sheafPullbackHomEquivPresheaf A J K S T).symm w)))

end

section

variable {B : Type u₄} [Category.{v₄} B] (G : A ⥤ B)
  [HasWeakSheafify K B] [∀ P : Cᵒᵖ ⥤ B, F.op.HasLeftKanExtension P]
  [J.HasSheafCompose G] [K.HasSheafCompose G]

/-- Pushforward of sheaves along a continuous functor is postcomposition of underlying
presheaves, so it commutes with a change of coefficient category on the nose. -/
noncomputable def sheafComposeSheafPushforwardIso :
    sheafCompose K G ⋙ F.sheafPushforwardContinuous B J K ≅
      F.sheafPushforwardContinuous A J K ⋙ sheafCompose J G :=
  Iso.refl _

variable (S : Sheaf J A)

/-- The canonical comparison `F^*(G ∘ S) ⟶ G ∘ F^*(S)` between pulling back a sheaf along a
continuous functor and changing its coefficient category along `G`: the adjoint transpose of `G`
applied to the unit of the pullback/pushforward adjunction. -/
noncomputable def sheafPullbackSheafComposeHom :
    (F.sheafPullback B J K).obj ((sheafCompose J G).obj S) ⟶
      (sheafCompose K G).obj ((F.sheafPullback A J K).obj S) :=
  ((F.sheafAdjunctionContinuous B J K).homEquiv _ _).symm
    ((sheafCompose J G).map ((F.sheafAdjunctionContinuous A J K).unit.app S) ≫
      (F.sheafComposeSheafPushforwardIso A J K G).inv.app ((F.sheafPullback A J K).obj S))

/-- The comparison `sheafPullbackSheafComposeHom` is the unique morphism whose adjoint transpose
is `G` applied to the unit of the pullback/pushforward adjunction. -/
lemma unit_comp_pushforward_map_sheafPullbackSheafComposeHom :
    (F.sheafAdjunctionContinuous B J K).unit.app ((sheafCompose J G).obj S) ≫
        (F.sheafPushforwardContinuous B J K).map
          (F.sheafPullbackSheafComposeHom A J K G S) =
      (sheafCompose J G).map ((F.sheafAdjunctionContinuous A J K).unit.app S) ≫
        (F.sheafComposeSheafPushforwardIso A J K G).inv.app ((F.sheafPullback A J K).obj S) :=
  unit_app_comp_map_homEquiv_symm (F.sheafAdjunctionContinuous B J K) _

/-- Composing the comparison with a change of coefficients of an adjoint transpose: the
comparison carries the `A`-valued adjoint transpose of `ψ` to the `B`-valued one. -/
lemma sheafPullbackSheafComposeHom_comp_sheafCompose_map (T : Sheaf K A)
    (ψ : S ⟶ (F.sheafPushforwardContinuous A J K).obj T) :
    F.sheafPullbackSheafComposeHom A J K G S ≫ (sheafCompose K G).map
        (((F.sheafAdjunctionContinuous A J K).homEquiv S T).symm ψ) =
      ((F.sheafAdjunctionContinuous B J K).homEquiv _ _).symm
        ((sheafCompose J G).map ψ ≫
          (F.sheafComposeSheafPushforwardIso A J K G).inv.app T) := by
  rw [sheafPullbackSheafComposeHom, ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  have hnat := (F.sheafComposeSheafPushforwardIso A J K G).inv.naturality
    (((F.sheafAdjunctionContinuous A J K).homEquiv S T).symm ψ)
  dsimp at hnat
  rw [Category.assoc, ← hnat, ← Category.assoc, ← Functor.map_comp,
    unit_app_comp_map_homEquiv_symm]

variable [∀ P : Cᵒᵖ ⥤ A, HasPointwiseLeftKanExtension F.op P]
  [∀ Y : Dᵒᵖ, PreservesColimitsOfShape (CostructuredArrow F.op Y) G]

/-- Transporting a morphism out of a presheaf-level left Kan extension along `lanCompRightIso`
multiplies its adjoint transpose by `G`. -/
lemma lanAdjunction_homEquiv_lanCompRightIso_comp_whiskerRight
    {P : Cᵒᵖ ⥤ A} {Q : Dᵒᵖ ⥤ A} (β : F.op.lan.obj P ⟶ Q) :
    (F.op.lanAdjunction B).homEquiv _ _
        ((lanCompRightIso F.op P G).hom ≫ whiskerRight β G) =
      whiskerRight ((F.op.lanAdjunction A).homEquiv P Q β) G ≫
        (Functor.associator F.op Q G).hom := by
  ext X
  have hL := lanUnit_app_app_lanCompRightIso_hom_app F.op P G X
  simp only [Adjunction.homEquiv_unit, Functor.lanAdjunction_unit]
  dsimp at hL ⊢
  rw [← Category.assoc, hL, ← G.map_comp]
  simp

/-- On underlying presheaves the comparison `sheafPullbackSheafComposeHom` is the comparison
`lanCompRightIso` for left Kan extensions followed by `G` applied to the universal map of the
sheaf pullback. -/
lemma sheafPullbackPresheafUnit_comp_sheafPullbackSheafComposeHom :
    F.sheafPullbackPresheafUnit B J K ((sheafCompose J G).obj S) ≫
        (sheafToPresheaf K B).map (F.sheafPullbackSheafComposeHom A J K G S) =
      (lanCompRightIso F.op S.obj G).hom ≫
        whiskerRight (F.sheafPullbackPresheafUnit A J K S) G := by
  refine (F.sheafPullbackHomEquivPresheaf_apply B J K _ _ _).symm.trans ?_
  have step : Sheaf.homEquiv ((sheafCompose J G).map
        ((F.sheafAdjunctionContinuous A J K).unit.app S) ≫
      (F.sheafComposeSheafPushforwardIso A J K G).inv.app ((F.sheafPullback A J K).obj S)) =
      (F.op.lanAdjunction B).homEquiv _ _ ((lanCompRightIso F.op S.obj G).hom ≫
        whiskerRight (F.sheafPullbackPresheafUnit A J K S) G) :=
    ((congrArg (fun α : S.obj ⟶ F.op ⋙ ((F.sheafPullback A J K).obj S).obj =>
          whiskerRight α G ≫
            (Functor.associator F.op ((F.sheafPullback A J K).obj S).obj G).hom)
        (Equiv.apply_symm_apply
          ((F.op.lanAdjunction A).homEquiv S.obj ((F.sheafPullback A J K).obj S).obj)
          ((sheafToPresheaf J A).map ((F.sheafAdjunctionContinuous A J K).unit.app S)))).symm.trans
      (F.lanAdjunction_homEquiv_lanCompRightIso_comp_whiskerRight A G
        (F.sheafPullbackPresheafUnit A J K S)).symm)
  exact (congrArg _ (congrArg Sheaf.homEquiv
      (Equiv.apply_symm_apply ((F.sheafAdjunctionContinuous B J K).homEquiv
          ((sheafCompose J G).obj S) ((sheafCompose K G).obj ((F.sheafPullback A J K).obj S)))
        ((sheafCompose J G).map ((F.sheafAdjunctionContinuous A J K).unit.app S) ≫
          (F.sheafComposeSheafPushforwardIso A J K G).inv.app
            ((F.sheafPullback A J K).obj S))))).trans
    ((congrArg _ step).trans (Equiv.symm_apply_apply _ _))

variable [K.PreservesSheafification G]

/-- If `G` preserves sheafification and the colimits computing the presheaf-level left Kan
extension along `F.op`, then the comparison `sheafPullbackSheafComposeHom` is an isomorphism. -/
instance isIso_sheafPullbackSheafComposeHom :
    IsIso (F.sheafPullbackSheafComposeHom A J K G S) := by
  have key := F.sheafPullbackPresheafUnit_comp_sheafPullbackSheafComposeHom A J K G S
  have hw : K.W ((lanCompRightIso F.op S.obj G).hom ≫
      whiskerRight (F.sheafPullbackPresheafUnit A J K S) G) := by
    have h₂ : K.W (whiskerRight (F.sheafPullbackPresheafUnit A J K S) G) :=
      K.W_of_preservesSheafification G _ (F.W_sheafPullbackPresheafUnit A J K S)
    rw [K.W_iff] at h₂ ⊢
    rw [Functor.map_comp]
    infer_instance
  have hres := F.isIso_of_W_sheafPullbackHomEquivPresheaf_symm B J K ((sheafCompose J G).obj S)
    ((sheafCompose K G).obj ((F.sheafPullback A J K).obj S))
    ((lanCompRightIso F.op S.obj G).hom ≫
      whiskerRight (F.sheafPullbackPresheafUnit A J K S) G) hw
  have heq : (F.sheafPullbackHomEquivPresheaf B J K ((sheafCompose J G).obj S)
      ((sheafCompose K G).obj ((F.sheafPullback A J K).obj S))).symm
      ((lanCompRightIso F.op S.obj G).hom ≫
        whiskerRight (F.sheafPullbackPresheafUnit A J K S) G) =
      F.sheafPullbackSheafComposeHom A J K G S :=
    (F.sheafPullbackHomEquivPresheaf B J K _ _).injective
      ((Equiv.apply_symm_apply _ _).trans
        ((F.sheafPullbackHomEquivPresheaf_apply B J K _ _ _).trans key).symm)
  exact heq ▸ hres

/-- Pulling back a sheaf along a continuous functor commutes with changing the coefficient
category along a functor which preserves sheafification and the colimits computing the
presheaf-level left Kan extension. -/
noncomputable def sheafPullbackSheafComposeIso :
    (F.sheafPullback B J K).obj ((sheafCompose J G).obj S) ≅
      (sheafCompose K G).obj ((F.sheafPullback A J K).obj S) :=
  asIso (F.sheafPullbackSheafComposeHom A J K G S)

end

end CategoryTheory.Functor
