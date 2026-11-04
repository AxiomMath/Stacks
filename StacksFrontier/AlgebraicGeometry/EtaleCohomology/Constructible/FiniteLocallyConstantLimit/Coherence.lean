module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Basic
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescent

/-!
# Coherence of the inverse-image comparisons on small étale sites

The descent of finite locally constant sheaves along a limit of schemes (Stacks Tag 0GL2) is
carried out with two families of comparison isomorphisms: the comparison
`AlgebraicGeometry.smallEtaleSheafPullbackCompIso'` of the inverse image along a named composite
`h = f ≫ g` with the composite of the inverse images, and the comparison
`AlgebraicGeometry.smallEtaleConstantPullbackIso` of the inverse image of a constant sheaf with the
constant sheaf. This file proves the coherence laws relating them: the comparisons along composites
are associative and unital, the constant comparison is natural in the value, and the constant
comparisons are compatible with the comparisons along composites.

All of these are statements about left adjoints, and are reduced to the (trivial) corresponding
statements for the right adjoints, the direct images, which are precomposition with base change.
For associativity and the unit laws this is `CategoryTheory.Adjunction.leftAdjointCompIso_assoc`
and its unital companions, together with the coherence of the composition comparison
`AlgebraicGeometry.smallEtaleBaseChange_compIso` of small étale base change. For the constants
the reduction is `CategoryTheory.Adjunction.leftAdjointCompIso_inv_leftAdjointUniq`: the
constant sheaf functor is left adjoint to sections over the final object, and the comparison of
the right adjoints `F_* ⋙ Γ ≅ Γ` is restriction along a morphism between final objects, so its
compatibility with composition is automatic, all such morphisms being equal.

## Main results

* `AlgebraicGeometry.smallEtaleSheafPullbackCompIso'_assoc` — associativity of the comparisons
  along named composites.
* `AlgebraicGeometry.smallEtaleSheafPullbackCompIso'_comp_id` and
  `AlgebraicGeometry.smallEtaleSheafPullbackCompIso'_id_comp` — the two unit laws, against
  `AlgebraicGeometry.smallEtaleSheafPullbackIdIso`.
* `AlgebraicGeometry.smallEtaleSheafPullbackCompIso'_inv_app_constantSheaf` — the constant
  comparison along a composite is the composite of the constant comparisons.
* `AlgebraicGeometry.smallEtaleConstantPullbackIso_hom_naturality` — naturality of the constant
  comparison in the value.
* `AlgebraicGeometry.smallEtaleSheafPullbackCompIso'_eq` and
  `AlgebraicGeometry.smallEtaleSheafPullbackCompIso'_trans_eqToIso` — the comparison along a
  named composite as the inverse-image comparison of the factored base change comparison, and its
  transport along an equality of named composites.
* `CategoryTheory.Functor.sheafPullbackComp'_assoc` and
  `Stacks.ConstantSheaf.sheafPullbackComp'_inv_app_constantSheaf` — the same two laws for inverse
  images along arbitrary continuous functors.

## References

* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
* [Stacks Project, Tag 0GL2](https://stacks.math.columbia.edu/tag/0GL2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Functor

universe w t v u v₀ v₁ v₂ v₃ u₀ u₁ u₂ u₃

namespace CategoryTheory.Adjunction

variable {A C₀ C₁ C₂ : Type*} [Category* A] [Category* C₀] [Category* C₁] [Category* C₂]

/-- For `L ⊣ R`, `c₀ ⊣ Γ₀`, `c₁ ⊣ Γ₁` and `σ : R ⋙ Γ₀ ≅ Γ₁`, the comparison
`c₀ ⋙ L ≅ c₁` of left adjoints of `Γ₁` is characterized by its effect on units. -/
public theorem unit_leftAdjointUniq_ofNatIsoRight_comp {c₀ : A ⥤ C₀} {Γ₀ : C₀ ⥤ A} {c₁ : A ⥤ C₁}
    {Γ₁ : C₁ ⥤ A} {L : C₀ ⥤ C₁} {R : C₁ ⥤ C₀} (k₀ : c₀ ⊣ Γ₀) (k₁ : c₁ ⊣ Γ₁) (adj : L ⊣ R)
    (σ : R ⋙ Γ₀ ≅ Γ₁) (E : A) :
    k₀.unit.app E ≫ Γ₀.map (adj.unit.app (c₀.obj E)) ≫
        Γ₀.map (R.map ((leftAdjointUniq ((k₀.comp adj).ofNatIsoRight σ) k₁).hom.app E)) =
      k₁.unit.app E ≫ σ.inv.app (c₁.obj E) := by
  have h := unit_leftAdjointUniq_hom_app ((k₀.comp adj).ofNatIsoRight σ) k₁ E
  rw [← h]
  simp

/-- **Compatibility of uniqueness of left adjoints with composition.** Given adjunctions
`cᵢ ⊣ Γᵢ` and `Lᵢⱼ ⊣ Rⱼᵢ`, comparisons `σᵢⱼ : Rⱼᵢ ⋙ Γᵢ ≅ Γⱼ` and a composition comparison
`μ : R₂₁ ⋙ R₁₀ ≅ R₂₀` compatible with the `σ`s, the induced comparison `c₀ ⋙ L₀₂ ≅ c₂` is the
composite of `(leftAdjointCompIso μ)⁻¹` with the comparisons along `L₀₁` and `L₁₂`. -/
public theorem leftAdjointCompIso_inv_leftAdjointUniq
    {c₀ : A ⥤ C₀} {Γ₀ : C₀ ⥤ A} {c₁ : A ⥤ C₁} {Γ₁ : C₁ ⥤ A} {c₂ : A ⥤ C₂} {Γ₂ : C₂ ⥤ A}
    (k₀ : c₀ ⊣ Γ₀) (k₁ : c₁ ⊣ Γ₁) (k₂ : c₂ ⊣ Γ₂)
    {L₀₁ : C₀ ⥤ C₁} {R₁₀ : C₁ ⥤ C₀} {L₁₂ : C₁ ⥤ C₂} {R₂₁ : C₂ ⥤ C₁}
    {L₀₂ : C₀ ⥤ C₂} {R₂₀ : C₂ ⥤ C₀}
    (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁) (adj₀₂ : L₀₂ ⊣ R₂₀)
    (σ₀₁ : R₁₀ ⋙ Γ₀ ≅ Γ₁) (σ₁₂ : R₂₁ ⋙ Γ₁ ≅ Γ₂) (σ₀₂ : R₂₀ ⋙ Γ₀ ≅ Γ₂)
    (μ : R₂₁ ⋙ R₁₀ ≅ R₂₀)
    (hσ : ∀ M : C₂, Γ₀.map (μ.hom.app M) ≫ σ₀₂.hom.app M =
      σ₀₁.hom.app (R₂₁.obj M) ≫ σ₁₂.hom.app M) (E : A) :
    (leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ μ).inv.app (c₀.obj E) ≫
        L₁₂.map ((leftAdjointUniq ((k₀.comp adj₀₁).ofNatIsoRight σ₀₁) k₁).hom.app E) ≫
        (leftAdjointUniq ((k₁.comp adj₁₂).ofNatIsoRight σ₁₂) k₂).hom.app E =
      (leftAdjointUniq ((k₀.comp adj₀₂).ofNatIsoRight σ₀₂) k₂).hom.app E := by
  apply ((k₀.comp adj₀₂).homEquiv _ _).injective
  have h₂ := unit_conjugateEquiv (adj₀₁.comp adj₁₂) adj₀₂
    (leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ μ).inv (c₀.obj E)
  rw [conjugateEquiv_leftAdjointCompIso_inv] at h₂
  have h₂' := congrArg Γ₀.map h₂
  simp only [comp_unit_app, Functor.comp_obj, Functor.map_comp, Category.assoc] at h₂'
  have hσ' : σ₁₂.inv.app (c₂.obj E) ≫ σ₀₁.inv.app (R₂₁.obj (c₂.obj E)) ≫
      Γ₀.map (μ.hom.app (c₂.obj E)) = σ₀₂.inv.app (c₂.obj E) := by
    rw [← cancel_mono (σ₀₂.hom.app _), Category.assoc, Category.assoc, hσ]
    simp
  have e₀₂ := unit_leftAdjointUniq_ofNatIsoRight_comp k₀ k₂ adj₀₂ σ₀₂ E
  have e₀₁ := unit_leftAdjointUniq_ofNatIsoRight_comp k₀ k₁ adj₀₁ σ₀₁ E
  have e₁₂ := unit_leftAdjointUniq_ofNatIsoRight_comp k₁ k₂ adj₁₂ σ₁₂ E
  have nμ : ∀ {M N : C₂} (f : M ⟶ N), Γ₀.map (μ.hom.app M) ≫ Γ₀.map (R₂₀.map f) =
      Γ₀.map (R₁₀.map (R₂₁.map f)) ≫ Γ₀.map (μ.hom.app N) := fun f => by
    simp only [← Γ₀.map_comp]
    exact congrArg Γ₀.map (μ.hom.naturality f).symm
  have nη : ∀ {M N : C₁} (f : M ⟶ N), Γ₀.map (R₁₀.map (adj₁₂.unit.app M)) ≫
      Γ₀.map (R₁₀.map (R₂₁.map (L₁₂.map f))) =
      Γ₀.map (R₁₀.map f) ≫ Γ₀.map (R₁₀.map (adj₁₂.unit.app N)) := fun f => by
    simp only [← Γ₀.map_comp, ← R₁₀.map_comp]
    exact congrArg (fun x => Γ₀.map (R₁₀.map x)) (adj₁₂.unit.naturality f).symm
  have nσ : ∀ {M N : C₁} (f : M ⟶ N), σ₀₁.inv.app M ≫ Γ₀.map (R₁₀.map f) =
      Γ₁.map f ≫ σ₀₁.inv.app N := fun f => (σ₀₁.inv.naturality f).symm
  simp only [homEquiv_unit, comp_unit_app, Functor.comp_obj, Functor.comp_map, Functor.map_comp,
    Category.assoc]
  rw [e₀₂, ← reassoc_of% h₂', reassoc_of% nμ, nμ, reassoc_of% nη, reassoc_of% e₀₁, reassoc_of% nσ,
    reassoc_of% nσ, reassoc_of% e₁₂, hσ']

/-- `CategoryTheory.Adjunction.leftAdjointIdIso` is the comparison of the two left adjoints of
the identity functor, by uniqueness of left adjoints. -/
public theorem leftAdjointIdIso_eq_leftAdjointUniq {F G : C₀ ⥤ C₀} (adj : F ⊣ G)
    (e : G ≅ 𝟭 C₀) :
    leftAdjointIdIso adj e = leftAdjointUniq (adj.ofNatIsoRight e) Adjunction.id := by
  ext X
  apply ((adj.ofNatIsoRight e).homEquiv _ _).injective
  rw [homEquiv_leftAdjointUniq_hom_app, homEquiv_ofNatIsoRight_apply]
  simp only [leftAdjointIdIso_hom_app, id_obj, homEquiv_unit, Functor.map_comp,
    Category.assoc]
  rw [unit_naturality_assoc, right_triangle_components_assoc]
  simp

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

variable {C₀ : Type u₀} [Category.{v₀} C₀] {C₁ : Type u₁} [Category.{v₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] {C₃ : Type u₃} [Category.{v₃} C₃]
  (A : Type w) [Category.{t} A]
  (J₀ : GrothendieckTopology C₀) (J₁ : GrothendieckTopology C₁)
  (J₂ : GrothendieckTopology C₂) (J₃ : GrothendieckTopology C₃)
  {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₂₃ : C₂ ⥤ C₃} {F₀₂ : C₀ ⥤ C₂} {F₁₃ : C₁ ⥤ C₃}
  {F₀₃ : C₀ ⥤ C₃}
  [F₀₁.IsContinuous J₀ J₁] [F₁₂.IsContinuous J₁ J₂] [F₂₃.IsContinuous J₂ J₃]
  [F₀₂.IsContinuous J₀ J₂] [F₁₃.IsContinuous J₁ J₃] [F₀₃.IsContinuous J₀ J₃]
  [(F₀₁.sheafPushforwardContinuous A J₀ J₁).IsRightAdjoint]
  [(F₁₂.sheafPushforwardContinuous A J₁ J₂).IsRightAdjoint]
  [(F₂₃.sheafPushforwardContinuous A J₂ J₃).IsRightAdjoint]
  [(F₀₂.sheafPushforwardContinuous A J₀ J₂).IsRightAdjoint]
  [(F₁₃.sheafPushforwardContinuous A J₁ J₃).IsRightAdjoint]
  [(F₀₃.sheafPushforwardContinuous A J₀ J₃).IsRightAdjoint]

/-- **Associativity of the inverse-image comparisons** along continuous functors of sites:
`CategoryTheory.Functor.sheafPullbackComp'` inherits any associativity of the four isomorphisms of
continuous functors it is applied to, stated on components of their inverses. -/
@[reassoc]
public theorem sheafPullbackComp'_assoc
    (e₀₁₂ : F₀₁ ⋙ F₁₂ ≅ F₀₂) (e₁₂₃ : F₁₂ ⋙ F₂₃ ≅ F₁₃) (e₀₁₃ : F₀₁ ⋙ F₁₃ ≅ F₀₃)
    (e₀₂₃ : F₀₂ ⋙ F₂₃ ≅ F₀₃)
    (h : ∀ U : C₀, e₀₂₃.inv.app U ≫ F₂₃.map (e₀₁₂.inv.app U) =
      e₀₁₃.inv.app U ≫ e₁₂₃.inv.app (F₀₁.obj U)) (M : Sheaf J₀ A) :
    (sheafPullbackComp' e₁₂₃ A J₁ J₂ J₃).hom.app ((F₀₁.sheafPullback A J₀ J₁).obj M) ≫
        (sheafPullbackComp' e₀₁₃ A J₀ J₁ J₃).hom.app M =
      (F₂₃.sheafPullback A J₂ J₃).map ((sheafPullbackComp' e₀₁₂ A J₀ J₁ J₂).hom.app M) ≫
        (sheafPullbackComp' e₀₂₃ A J₀ J₂ J₃).hom.app M := by
  have hpf : isoWhiskerLeft (F₂₃.sheafPushforwardContinuous A J₂ J₃)
        (sheafPushforwardContinuousComp' e₀₁₂ A J₀ J₁ J₂) ≪≫
        sheafPushforwardContinuousComp' e₀₂₃ A J₀ J₂ J₃ =
      (associator _ _ _).symm ≪≫
        isoWhiskerRight (sheafPushforwardContinuousComp' e₁₂₃ A J₁ J₂ J₃)
          (F₀₁.sheafPushforwardContinuous A J₀ J₁) ≪≫
        sheafPushforwardContinuousComp' e₀₁₃ A J₀ J₁ J₃ := by
    refine Iso.ext (NatTrans.ext (funext fun M =>
      Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))))
    have := congrArg (fun x => M.obj.map x.op) (h U.unop)
    simp only [op_comp, Functor.map_comp] at this
    simp only [comp_obj, Iso.trans_hom, isoWhiskerLeft_hom, NatTrans.comp_app, whiskerLeft_app,
      ObjectProperty.FullSubcategory.comp_hom, sheafPushforwardContinuousComp'_hom_app_hom_app,
      sheafPushforwardContinuous_obj_obj_map, Quiver.Hom.unop_op, Iso.symm_hom, isoWhiskerRight_hom,
      associator_inv_app, whiskerRight_app, Category.id_comp,
      sheafPushforwardContinuous_map_hom_app]
    exact this
  have := Adjunction.leftAdjointCompIso_assoc (F₀₁.sheafAdjunctionContinuous A J₀ J₁)
    (F₁₂.sheafAdjunctionContinuous A J₁ J₂) (F₂₃.sheafAdjunctionContinuous A J₂ J₃)
    (F₀₂.sheafAdjunctionContinuous A J₀ J₂) (F₁₃.sheafAdjunctionContinuous A J₁ J₃)
    (F₀₃.sheafAdjunctionContinuous A J₀ J₃) _ _ _ _ hpf
  simpa [sheafPullbackComp'] using congrArg (fun i => i.hom.app M) this

end CategoryTheory.Functor

namespace Stacks.ConstantSheaf

variable {C₀ : Type u₀} [Category.{v₀} C₀] {C₁ : Type u₁} [Category.{v₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] (A : Type w) [Category.{t} A]
  (J₀ : GrothendieckTopology C₀) (J₁ : GrothendieckTopology C₁)
  (J₂ : GrothendieckTopology C₂)
  {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₀₂ : C₀ ⥤ C₂}
  [F₀₁.IsContinuous J₀ J₁] [F₁₂.IsContinuous J₁ J₂] [F₀₂.IsContinuous J₀ J₂]
  [(F₀₁.sheafPushforwardContinuous A J₀ J₁).IsRightAdjoint]
  [(F₁₂.sheafPushforwardContinuous A J₁ J₂).IsRightAdjoint]
  [(F₀₂.sheafPushforwardContinuous A J₀ J₂).IsRightAdjoint]
  [HasWeakSheafify J₀ A] [HasWeakSheafify J₁ A] [HasWeakSheafify J₂ A]

/-- **The constant comparisons are compatible with composition.** For continuous functors
`F₀₁`, `F₁₂`, `F₀₂` between sites with final objects, all preserving them, and `F₀₁ ⋙ F₁₂ ≅ F₀₂`,
the comparison of the inverse image along `F₀₂` of a constant sheaf with the constant sheaf is
the composite of the comparisons along `F₀₁` and along `F₁₂`. -/
@[reassoc]
public theorem sheafPullbackComp'_inv_app_constantSheaf (e : F₀₁ ⋙ F₁₂ ≅ F₀₂)
    {T₀ : C₀} (hT₀ : IsTerminal T₀) {T₁ : C₁} (hT₁ : IsTerminal T₁) {T₂ : C₂}
    (hT₂ : IsTerminal T₂) (e₀₁ : F₀₁.obj T₀ ≅ T₁) (e₁₂ : F₁₂.obj T₁ ≅ T₂)
    (e₀₂ : F₀₂.obj T₀ ≅ T₂) (E : A) :
    (Functor.sheafPullbackComp' e A J₀ J₁ J₂).inv.app ((constantSheaf J₀ A).obj E) ≫
        (F₁₂.sheafPullback A J₁ J₂).map
          ((sheafPullbackConstantSheafIso F₀₁ A J₀ J₁ hT₀ hT₁ e₀₁).hom.app E) ≫
        (sheafPullbackConstantSheafIso F₁₂ A J₁ J₂ hT₁ hT₂ e₁₂).hom.app E =
      (sheafPullbackConstantSheafIso F₀₂ A J₀ J₂ hT₀ hT₂ e₀₂).hom.app E := by
  refine Adjunction.leftAdjointCompIso_inv_leftAdjointUniq (constantSheafAdj J₀ A hT₀)
    (constantSheafAdj J₁ A hT₁) (constantSheafAdj J₂ A hT₂) _ _ _ _ _ _ _ (fun M => ?_) E
  have hT : IsTerminal (F₁₂.obj (F₀₁.obj T₀)) :=
    hT₂.ofIso ((F₁₂.mapIso e₀₁ ≪≫ e₁₂).symm)
  have := congrArg (fun x => M.obj.map x.op)
    (hT.hom_ext (e₀₂.inv ≫ e.inv.app T₀) (e₁₂.inv ≫ F₁₂.map e₀₁.inv))
  simp only [op_comp, Functor.map_comp] at this
  simp only [comp_obj, flip_obj_obj, ObjectProperty.ι_obj, flip_obj_map, ObjectProperty.ι_map,
    sheafPushforwardContinuousComp'_hom_app_hom_app, pushforwardSectionsIsoOfTerminal]
  exact this

end Stacks.ConstantSheaf

namespace AlgebraicGeometry

/-- Associativity of the composition comparisons of small étale base change along *named*
composites, in the form needed for the inverse images. -/
public theorem smallEtaleBaseChange_factoredCompIso_inv_assoc (B : BigEtaleSite.{u})
    {X Y Z W : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (fg : X ⟶ Z) (gh : Y ⟶ W)
    (fgh : X ⟶ W) (e₁ : f ≫ g = fg) (e₂ : g ≫ h = gh) (e₃ : fg ≫ h = fgh)
    (e₄ : f ≫ gh = fgh) (U : SmallEtale B W.obj W.property) :
    (smallEtaleBaseChange_factoredCompIso B X Y W f gh fgh e₄).inv.app U ≫
        (smallEtaleBaseChange B f).map
          ((smallEtaleBaseChange_factoredCompIso B Y Z W g h gh e₂).inv.app U) =
      (smallEtaleBaseChange_factoredCompIso B X Z W fg h fgh e₃).inv.app U ≫
        (smallEtaleBaseChange_factoredCompIso B X Y Z f g fg e₁).inv.app
          ((smallEtaleBaseChange B h).obj U) := by
  subst e₁ e₂ e₄
  have := baseChangeCompIso_assoc B f g h U
  simp only [smallEtaleBaseChange_factoredCompIso, Iso.trans_inv, eqToIso_refl, Iso.refl_inv,
    NatTrans.comp_app, Category.id_comp]
  rw [← cancel_mono
    ((smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app ((smallEtaleBaseChange B h).obj U) ≫
      (smallEtaleBaseChange_compIso B X Z W (f ≫ g) h).val.hom.app U)]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]
  refine this.trans ?_
  simp only [eqToIso.inv, eqToHom_app]
  exact (eqToHom_refl _ _).symm

/-- The identity comparison of small étale base change is the canonical comparison for slice
pullback along an identity, after forgetting the étale condition. -/
public theorem smallEtaleBaseChange_idIso_hom_inclusion (B : BigEtaleSite.{u}) (X : B.Scheme)
    (U : SmallEtale B X.1 X.property) :
    (SmallEtale.inclusion B X.1 X.property).map ((smallEtaleBaseChange_idIso B X).hom.app U) =
      Over.pullbackId.hom.app U.obj := by
  simp only [ObjectProperty.ι_obj, smallEtaleBaseChange_obj_obj, id_obj, smallEtaleBaseChange_idIso,
    fullyFaithfulCancelRight_hom_app, Iso.trans_hom, eqToIso.hom, isoWhiskerLeft_hom, Iso.symm_hom,
    NatTrans.comp_app, comp_obj, eqToHom_app, whiskerLeft_app, rightUnitor_hom_app,
    leftUnitor_inv_app, Category.comp_id, ObjectProperty.ι_map]
  exact (SmallEtale.inclusion B X.1 X.property).map_preimage _

/-- The composition comparison against an identity on the right is inverse to the identity
comparison. -/
public theorem smallEtaleBaseChange_compIso_comp_id (B : BigEtaleSite.{u})
    {Y X : B.Scheme} (r : Y ⟶ X) (U : SmallEtale B X.1 X.property) :
    (smallEtaleBaseChange_compIso B Y X X r (𝟙 X)).val.inv.app U ≫
        (smallEtaleBaseChange B r).map ((smallEtaleBaseChange_idIso B X).hom.app U) =
      𝟙 ((smallEtaleBaseChange B r).obj U) := by
  apply (SmallEtale.inclusion B _ _).map_injective
  simp only [Functor.map_comp, baseChange_map_inclusion,
    baseChangeComp_inv, smallEtaleBaseChange_idIso_hom_inclusion]
  apply (Over.forget _).map_injective
  apply Limits.pullback.hom_ext <;>
    simp only [ObjectProperty.ι_obj, smallEtaleBaseChange_obj_obj, Over.forget_obj,
      Over.pullback_obj_left, Functor.id_obj, Functor.comp_obj, Over.pullbackComp,
      conjugateIsoEquiv, conjugateEquiv, Iso.homCongr_symm, Equiv.trans_def, mateEquiv,
      Over.mapPullbackAdj, Over.map_obj_left, Equiv.trans_apply, Iso.homCongr_apply,
      Iso.symm_inv, Iso.symm_hom, TwoSquare.equivNatTrans_symm_apply, Equiv.coe_fn_mk,
      Functor.whiskerRight_comp, Functor.whiskerLeft_comp, Category.assoc,
      TwoSquare.equivNatTrans_apply, Equiv.symm_trans, Equiv.symm_mk, Equiv.symm_symm,
      Iso.symm_symm_eq, Over.mapComp, NatTrans.comp_app, Functor.rightUnitor_inv_app,
      Functor.whiskerLeft_app, Adjunction.comp_unit_app, Adjunction.mkOfHomEquiv_unit_app,
      Over.map_obj_hom, Over.pullback_obj_hom, Over.id_left, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
      Functor.comp_map, CategoryTheory.Functor.map_id, NatIso.ofComponents_inv_app,
      Adjunction.mkOfHomEquiv_counit_app, Category.id_comp, Functor.id_map,
      Category.comp_id, Over.pullbackId, Adjunction.id_unit, Functor.whiskerLeft_id',
      Adjunction.id_counit, Functor.whiskerRight_id', Over.mapId, Functor.map_comp,
      Over.forget_map, Over.comp_left, Over.homMk_left, Over.pullback_map_left,
      Over.isoMk_inv_left, Iso.refl_inv, Limits.pullback.lift_fst,
      Limits.pullback.lift_snd, Limits.pullback.lift_fst_assoc] <;>
    cat_disch

/-- The factored composition comparison along `r ≫ 𝟙 = r` is base change of the identity
comparison. -/
public theorem smallEtaleBaseChange_factoredCompIso_comp_id_inv (B : BigEtaleSite.{u})
    {Y X : B.Scheme} (r : Y ⟶ X) (U : SmallEtale B X.1 X.property) :
    (smallEtaleBaseChange_factoredCompIso B Y X X r (𝟙 X) r (Category.comp_id r)).inv.app U =
      (smallEtaleBaseChange B r).map ((smallEtaleBaseChange_idIso B X).inv.app U) := by
  rw [← cancel_mono ((smallEtaleBaseChange B r).map ((smallEtaleBaseChange_idIso B X).hom.app U)),
    ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  simp only [smallEtaleBaseChange_factoredCompIso, Iso.trans_inv, NatTrans.comp_app,
    eqToIso.inv, eqToHom_app, Category.assoc]
  rw [smallEtaleBaseChange_compIso_comp_id]
  exact (Category.comp_id _).trans (eqToHom_refl _ _)

/-- The composition comparison against an identity on the left is inverse to the identity
comparison. -/
public theorem smallEtaleBaseChange_compIso_id_comp (B : BigEtaleSite.{u})
    {Y X : B.Scheme} (r : Y ⟶ X) (U : SmallEtale B X.1 X.property) :
    (smallEtaleBaseChange_compIso B Y Y X (𝟙 Y) r).val.inv.app U ≫
        (smallEtaleBaseChange_idIso B Y).hom.app ((smallEtaleBaseChange B r).obj U) =
      𝟙 ((smallEtaleBaseChange B r).obj U) := by
  apply (SmallEtale.inclusion B _ _).map_injective
  simp only [Functor.map_comp, baseChangeComp_inv,
    smallEtaleBaseChange_idIso_hom_inclusion]
  apply (Over.forget _).map_injective
  apply Limits.pullback.hom_ext <;>
    simp only [ObjectProperty.ι_obj, smallEtaleBaseChange_obj_obj, Over.forget_obj,
      Over.pullback_obj_left, Functor.id_obj, Functor.comp_obj, Over.pullbackComp,
      conjugateIsoEquiv, conjugateEquiv, Iso.homCongr_symm, Equiv.trans_def, mateEquiv,
      Over.mapPullbackAdj, Over.map_obj_left, Equiv.trans_apply, Iso.homCongr_apply,
      Iso.symm_inv, Iso.symm_hom, TwoSquare.equivNatTrans_symm_apply, Equiv.coe_fn_mk,
      Functor.whiskerRight_comp, Functor.whiskerLeft_comp, Category.assoc,
      TwoSquare.equivNatTrans_apply, Equiv.symm_trans, Equiv.symm_mk, Equiv.symm_symm,
      Iso.symm_symm_eq, Over.mapComp, NatTrans.comp_app, Functor.rightUnitor_inv_app,
      Functor.whiskerLeft_app, Adjunction.comp_unit_app, Adjunction.mkOfHomEquiv_unit_app,
      Over.map_obj_hom, Over.pullback_obj_hom, Over.id_left, Category.comp_id,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Functor.comp_map, CategoryTheory.Functor.map_id,
      NatIso.ofComponents_inv_app, Adjunction.mkOfHomEquiv_counit_app, Category.id_comp,
      Functor.id_map, Over.pullbackId, Adjunction.id_unit, Functor.whiskerLeft_id',
      Adjunction.id_counit, Functor.whiskerRight_id', Over.mapId, Over.forget_map,
      Over.comp_left, Over.homMk_left, Over.pullback_map_left, Over.isoMk_inv_left,
      Iso.refl_inv, Limits.pullback.lift_fst, Limits.pullback.lift_snd,
      Limits.pullback.lift_fst_assoc] <;>
    cat_disch

/-- The factored composition comparison along `𝟙 ≫ r = r` is the identity comparison. -/
public theorem smallEtaleBaseChange_factoredCompIso_id_comp_inv (B : BigEtaleSite.{u})
    {Y X : B.Scheme} (r : Y ⟶ X) (U : SmallEtale B X.1 X.property) :
    (smallEtaleBaseChange_factoredCompIso B Y Y X (𝟙 Y) r r (Category.id_comp r)).inv.app U =
      (smallEtaleBaseChange_idIso B Y).inv.app ((smallEtaleBaseChange B r).obj U) := by
  rw [← cancel_mono ((smallEtaleBaseChange_idIso B Y).hom.app ((smallEtaleBaseChange B r).obj U)),
    Iso.inv_hom_id_app]
  simp only [smallEtaleBaseChange_factoredCompIso, Iso.trans_inv, NatTrans.comp_app,
    eqToIso.inv, eqToHom_app, Category.assoc]
  rw [smallEtaleBaseChange_compIso_id_comp]
  exact (Category.comp_id _).trans (eqToHom_refl _ _)

section Sheaves

variable (B : BigEtaleSite.{u}) (A : Type t) [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

/-- The comparison along a named composite is the inverse-image comparison of the factored
comparison `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso` of base changes. -/
public theorem smallEtaleSheafPullbackCompIso'_eq {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (e : f ≫ g = h) :
    smallEtaleSheafPullbackCompIso' B A f g h e =
      Functor.sheafPullbackComp' (smallEtaleBaseChange_factoredCompIso B X Y Z f g h e) A
        (SmallEtale.topology B Z.obj Z.property) (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property) := by
  subst e
  simp [smallEtaleBaseChange_factoredCompIso, smallEtaleSheafPullbackCompIso]

/-- **Associativity of the comparisons along named composites.** For `f : X ⟶ Y`, `g : Y ⟶ Z`,
`h : Z ⟶ W` with named composites `fg`, `gh`, `fgh`, the two comparisons of
`f⁻¹ g⁻¹ h⁻¹ F` with `fgh⁻¹ F` agree. -/
@[reassoc]
public theorem smallEtaleSheafPullbackCompIso'_assoc {X Y Z W : B.Scheme} (f : X ⟶ Y)
    (g : Y ⟶ Z) (h : Z ⟶ W) (fg : X ⟶ Z) (gh : Y ⟶ W) (fgh : X ⟶ W) (e₁ : f ≫ g = fg)
    (e₂ : g ≫ h = gh) (e₃ : fg ≫ h = fgh) (e₄ : f ≫ gh = fgh)
    (F : Sheaf (SmallEtale.topology B W.obj W.property) A) :
    (smallEtaleSheafPullback B A f).map
          ((smallEtaleSheafPullbackCompIso' B A g h gh e₂).hom.app F) ≫
        (smallEtaleSheafPullbackCompIso' B A f gh fgh e₄).hom.app F =
      (smallEtaleSheafPullbackCompIso' B A f g fg e₁).hom.app
          ((smallEtaleSheafPullback B A h).obj F) ≫
        (smallEtaleSheafPullbackCompIso' B A fg h fgh e₃).hom.app F := by
  simp only [smallEtaleSheafPullbackCompIso'_eq]
  exact (Functor.sheafPullbackComp'_assoc A _ _ _ _ _ _ _ _
    (smallEtaleBaseChange_factoredCompIso_inv_assoc B f g h fg gh fgh e₁ e₂ e₃ e₄) F).symm

/-- **Transport along an equality of named composites.** -/
public theorem smallEtaleSheafPullbackCompIso'_trans_eqToIso {X Y Z : B.Scheme} (f : X ⟶ Y)
    (g : Y ⟶ Z) {h h' : X ⟶ Z} (e : f ≫ g = h) (hh : h = h') :
    smallEtaleSheafPullbackCompIso' B A f g h e ≪≫
        eqToIso (congrArg (fun k => smallEtaleSheafPullback B A k) hh) =
      smallEtaleSheafPullbackCompIso' B A f g h' (e.trans hh) := by
  subst hh
  simp

/-- **Right unit law**: the comparison along `f ≫ 𝟙 = f` is inverse image along `f` of the
identity comparison `AlgebraicGeometry.smallEtaleSheafPullbackIdIso`. -/
public theorem smallEtaleSheafPullbackCompIso'_comp_id {X Y : B.Scheme} (f : X ⟶ Y)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) A) :
    (smallEtaleSheafPullbackCompIso' B A f (𝟙 Y) f (Category.comp_id f)).hom.app F =
      (smallEtaleSheafPullback B A f).map ((smallEtaleSheafPullbackIdIso B Y A).hom.app F) := by
  have h := Adjunction.leftAdjointCompIso_id_comp
    ((smallEtaleBaseChange B (𝟙 Y)).sheafAdjunctionContinuous A
      (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B Y.obj Y.property))
    ((smallEtaleBaseChange B f).sheafAdjunctionContinuous A
      (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property))
    (sheafPushforwardContinuousComp'
      (smallEtaleBaseChange_factoredCompIso B X Y Y f (𝟙 Y) f (Category.comp_id f)) A _ _ _)
    (sheafPushforwardContinuousId' (smallEtaleBaseChange_idIso B Y) A _) ?_
  · rw [smallEtaleSheafPullbackCompIso'_eq]
    have := congrArg (fun i => i.hom.app F) h
    simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app,
      leftUnitor_hom_app, Adjunction.leftAdjointIdIso_eq_leftAdjointUniq] at this
    exact this.trans (Category.comp_id _)
  · refine Iso.ext (NatTrans.ext (funext fun M =>
      Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))))
    have := congrArg (fun x => M.obj.map x.op)
      (smallEtaleBaseChange_factoredCompIso_comp_id_inv B f U.unop)
    simp only [comp_obj, sheafPushforwardContinuousComp'_hom_app_hom_app, Iso.trans_hom,
      isoWhiskerLeft_hom, NatTrans.comp_app, id_obj, whiskerLeft_app, rightUnitor_hom_app,
      Category.comp_id, sheafPushforwardContinuousId'_hom_app_hom_app,
      sheafPushforwardContinuous_obj_obj_map, Quiver.Hom.unop_op]
    exact this

/-- **Left unit law**: the comparison along `𝟙 ≫ g = g` is the identity comparison
`AlgebraicGeometry.smallEtaleSheafPullbackIdIso`. -/
public theorem smallEtaleSheafPullbackCompIso'_id_comp {X Y : B.Scheme} (g : X ⟶ Y)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) A) :
    (smallEtaleSheafPullbackCompIso' B A (𝟙 X) g g (Category.id_comp g)).hom.app F =
      (smallEtaleSheafPullbackIdIso B X A).hom.app ((smallEtaleSheafPullback B A g).obj F) := by
  have h := Adjunction.leftAdjointCompIso_comp_id
    ((smallEtaleBaseChange B g).sheafAdjunctionContinuous A
      (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property))
    ((smallEtaleBaseChange B (𝟙 X)).sheafAdjunctionContinuous A
      (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B X.obj X.property))
    (sheafPushforwardContinuousComp'
      (smallEtaleBaseChange_factoredCompIso B X X Y (𝟙 X) g g (Category.id_comp g)) A _ _ _)
    (sheafPushforwardContinuousId' (smallEtaleBaseChange_idIso B X) A _) ?_
  · rw [smallEtaleSheafPullbackCompIso'_eq]
    have := congrArg (fun i => i.hom.app F) h
    simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app,
      rightUnitor_hom_app, Adjunction.leftAdjointIdIso_eq_leftAdjointUniq] at this
    exact this.trans (Category.comp_id _)
  · refine Iso.ext (NatTrans.ext (funext fun M =>
      Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))))
    have := congrArg (fun x => M.obj.map x.op)
      (smallEtaleBaseChange_factoredCompIso_id_comp_inv B g U.unop)
    simp only [comp_obj, sheafPushforwardContinuousComp'_hom_app_hom_app, Iso.trans_hom,
      isoWhiskerRight_hom, NatTrans.comp_app, id_obj, whiskerRight_app, leftUnitor_hom_app,
      Category.comp_id, sheafPushforwardContinuous_map_hom_app,
      sheafPushforwardContinuousId'_hom_app_hom_app]
    exact this

variable [∀ (S : B.Scheme), HasWeakSheafify (SmallEtale.topology B S.obj S.property) A]

/-- **Constants versus composition.** For `f ≫ g = h`, the comparison of the inverse image
along `h` of the constant sheaf on `E` with the constant sheaf is the composite of the comparisons
along `g` and along `f`. -/
@[reassoc]
public theorem smallEtaleSheafPullbackCompIso'_inv_app_constantSheaf {X Y Z : B.Scheme}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (e : f ≫ g = h) (E : A) :
    (smallEtaleSheafPullbackCompIso' B A f g h e).inv.app
        ((constantSheaf (SmallEtale.topology B Z.obj Z.property) A).obj E) ≫
        (smallEtaleSheafPullback B A f).map (smallEtaleConstantPullbackIso B A g E).hom ≫
        (smallEtaleConstantPullbackIso B A f E).hom =
      (smallEtaleConstantPullbackIso B A h E).hom := by
  rw [smallEtaleSheafPullbackCompIso'_eq]
  exact Stacks.ConstantSheaf.sheafPullbackComp'_inv_app_constantSheaf A _ _ _ _
    (SmallEtale.finalIsTerminal B Z.obj Z.property) (SmallEtale.finalIsTerminal B Y.obj Y.property)
    (SmallEtale.finalIsTerminal B X.obj X.property) (smallEtaleFinalBaseChangeIso B g)
    (smallEtaleFinalBaseChangeIso B f) (smallEtaleFinalBaseChangeIso B h) E

/-- **Naturality of the constant comparison** in the value. -/
@[reassoc]
public theorem smallEtaleConstantPullbackIso_hom_naturality {S T : B.Scheme} (f : T ⟶ S)
    {E E' : A} (φ : E ⟶ E') :
    (smallEtaleSheafPullback B A f).map
        ((constantSheaf (SmallEtale.topology B S.obj S.property) A).map φ) ≫
        (smallEtaleConstantPullbackIso B A f E').hom =
      (smallEtaleConstantPullbackIso B A f E).hom ≫
        (constantSheaf (SmallEtale.topology B T.obj T.property) A).map φ :=
  (smallEtaleSheafPullbackConstantSheafIso B f A).hom.naturality φ

end Sheaves

end AlgebraicGeometry

end
