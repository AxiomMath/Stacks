module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.BaseChangeShriek
import all StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.BaseChangeShriek
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ProPushforwardLan
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.RestrictionHomColimit
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ExtensionByZeroOpenImmersion

/-!
# Base change of extension by zero along a functor

Let `j^* : 𝒟 ⥤ 𝒞` and `j'^* : 𝒟' ⥤ 𝒞'` carry Deligne-system assignments, and let `F : 𝒟 ⥤ 𝒟'`,
`G : 𝒞 ⥤ 𝒞'` with `β : F ⋙ j'^* ≅ j^* ⋙ G`. If for every `K` the image `(F K_n)` of the system
assigned to `K` satisfies the identification of [Stacks, Tag 0G2H] for `j'^*`, then

`Rj'_! ∘ G ≅ Pro F ∘ Rj_!`,

where `Pro F` is `F` applied to pro-objects termwise (`CategoryTheory.ProSeq.map`). On functors
of points the isomorphism is the left Kan extension along `F` of `α ↦ β⁻¹ ∘ G α`. This is the
formal part of the first proof of [Stacks, Tag 0G4W]: for a proper morphism `f` and an open `V` of
its target, with `F = Rf_*`, `G = Rg_*` and `β` flat base change, the identification of
[Stacks, Tag 0G2H] for `(Rf_* K_n)` is the geometric input.

## Main definitions

* `CategoryTheory.baseChangeShriekOfLifting`: base change of extension by zero along a functor
  `F` whose images of assigned Deligne systems satisfy Stacks 0G2H.

## References

* [Stacks Project, Tag 0G4W](https://stacks.math.columbia.edu/tag/0G4W)
* [Stacks Project, Tag 0G4N](https://stacks.math.columbia.edu/tag/0G4N)
* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u u₁ u₂ u₃ u₄

namespace CategoryTheory

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒞' : Type u₂} [Category.{v} 𝒞']
  {𝒟 : Type u₃} [Category.{v} 𝒟] {𝒟' : Type u₄} [Category.{v} 𝒟']

/-! ### Base change of extension by zero along a functor -/

section Lifting

variable {jX : 𝒟 ⥤ 𝒞} (A : DeligneSystemValues jX) {jY : 𝒟' ⥤ 𝒞'} (A' : DeligneSystemValues jY)
  (F : 𝒟 ⥤ 𝒟') (G : 𝒞 ⥤ 𝒞') (β : F ⋙ jY ≅ jX ⋙ G)

/-- The map `Hom(K, j^* L) ⟶ Hom(G K, j'^* (F L))`, `α ↦ G α` followed by the identification
`β : F ⋙ j'^* ≅ j^* ⋙ G`, as a transformation of functors in `L`. -/
public def baseChangeHomNatTrans (K : 𝒞) :
    jX ⋙ coyoneda.obj (op K) ⟶ F ⋙ jY ⋙ coyoneda.obj (op (G.obj K)) where
  app L := ↾fun (α : K ⟶ jX.obj L) => G.map α ≫ β.inv.app L
  naturality L L' ψ := by
    ext α
    change G.map (α ≫ jX.map ψ) ≫ β.inv.app L' = (G.map α ≫ β.inv.app L) ≫ jY.map (F.map ψ)
    rw [G.map_comp, Category.assoc, Category.assoc]
    congr 1
    exact β.inv.naturality ψ

/-- `CategoryTheory.baseChangeHomNatTrans` is natural in `K`. -/
public lemma baseChangeHomNatTrans_naturality {K K' : 𝒞} (φ : K ⟶ K') :
    Functor.whiskerLeft jX (coyoneda.map φ.op) ≫ baseChangeHomNatTrans F G β K =
      baseChangeHomNatTrans F G β K' ≫
        Functor.whiskerLeft F (Functor.whiskerLeft jY (coyoneda.map (G.map φ).op)) := by
  ext L α
  dsimp [baseChangeHomNatTrans]
  simp

/-- The restriction of the image `(F K_n)` of the system assigned to `K` is the constant system at
`G K`: `(F K_n)|_V ≅ G(K_n|_U) ≅ G K`. -/
public def baseChangeRestrictIso (K : 𝒞) :
    (A.system K ⋙ F) ⋙ jY ≅ (Functor.const ℕᵒᵖ).obj (G.obj K) :=
  NatIso.ofComponents (fun n => β.app ((A.system K).obj n) ≪≫ G.mapIso ((A.restrictIso K).app n))
    (fun {n m} a => by
      have h₁ : jY.map (F.map ((A.system K).map a)) ≫ β.hom.app ((A.system K).obj m) =
          β.hom.app ((A.system K).obj n) ≫ G.map (jX.map ((A.system K).map a)) :=
        β.hom.naturality _
      have h₂ : jX.map ((A.system K).map a) ≫ (A.restrictIso K).hom.app m =
          (A.restrictIso K).hom.app n := by
        simpa using (A.restrictIso K).hom.naturality a
      change jY.map (F.map ((A.system K).map a)) ≫ β.hom.app _ ≫ G.map _ =
        (β.hom.app _ ≫ G.map _) ≫ 𝟙 _
      rw [Category.comp_id, reassoc_of% h₁, ← G.map_comp]
      exact congrArg (fun t => _ ≫ G.map t) h₂)

variable [∀ P : 𝒟 ⥤ Type v, F.HasLeftKanExtension P]

/-- The transformation of functors of points underlying the base change map
`Rj'_!(G K) ⟶ Pro F (Rj_! K)`: the left Kan extension along `F` of
`CategoryTheory.baseChangeHomNatTrans`. -/
public def baseChangePointsHom (K : 𝒞) :
    F.lan.obj (jX ⋙ coyoneda.obj (op K)) ⟶ jY ⋙ coyoneda.obj (op (G.obj K)) :=
  ((F.lanAdjunction (Type v)).homEquiv _ _).symm (baseChangeHomNatTrans F G β K)

/-- The unit of the left Kan extension followed by `CategoryTheory.baseChangePointsHom` is
`CategoryTheory.baseChangeHomNatTrans`. -/
public lemma lanUnit_comp_baseChangePointsHom (K : 𝒞) :
    F.lanUnit.app _ ≫ Functor.whiskerLeft F (baseChangePointsHom F G β K) =
      baseChangeHomNatTrans F G β K := by
  have h := ((F.lanAdjunction (Type v)).homEquiv _ _).apply_symm_apply
    (baseChangeHomNatTrans F G β K)
  rw [Adjunction.homEquiv_unit, Functor.lanAdjunction_unit] at h
  exact h

/-- `CategoryTheory.baseChangePointsHom` is natural in `K`. -/
public lemma baseChangePointsHom_naturality {K K' : 𝒞} (φ : K ⟶ K') :
    F.lan.map (Functor.whiskerLeft jX (coyoneda.map φ.op)) ≫ baseChangePointsHom F G β K =
      baseChangePointsHom F G β K' ≫ Functor.whiskerLeft jY (coyoneda.map (G.map φ).op) := by
  rw [baseChangePointsHom, baseChangePointsHom,
    ← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm,
    baseChangeHomNatTrans_naturality]
  rfl

/-- `CategoryTheory.baseChangePointsHom` is read, through the identification of the functor of
points of `Rj_! K` with that of the assigned system `(K_n)` and `Pro.lanSeqHomColimIso`, as the
comparison `colim_n Hom(F K_n, -) ⟶ Hom(G K, j'^* -)` of `CategoryTheory.proHomComparison`. -/
public lemma baseChangePointsHom_eq (K : 𝒞) :
    baseChangePointsHom F G β K =
      F.lan.map (A.systemHomIso K).inv ≫ (Pro.lanSeqHomColimIso F (A.system K)).hom ≫
        proHomComparison (A.system K ⋙ F) jY
          (coneOfNatIso (baseChangeRestrictIso A F G β K) ⟨G.obj K, 𝟙 _⟩) := by
  refine Functor.hom_ext_of_isLeftKanExtension _ (F.lanUnit.app _) _ _ ?_
  rw [lanUnit_comp_baseChangePointsHom]
  ext L x
  obtain ⟨y, rfl⟩ : ∃ y, (A.systemHomIso K).hom.app L y = x :=
    ⟨(A.systemHomIso K).inv.app L x, by simp⟩
  obtain ⟨n, g, rfl⟩ := Pro.seqStage_surjective (A.system K) L y
  have h₁ := ConcreteCategory.congr_hom
    (congr_app (F.lanUnit.naturality (A.systemHomIso K).inv) L)
    ((A.systemHomIso K).hom.app L (Pro.seqStage (A.system K) g))
  have h₂ := ConcreteCategory.congr_hom
    (congr_app (Pro.lanUnit_comp_lanSeqHomColimHom F (A.system K)) L)
    (Pro.seqStage (A.system K) g)
  dsimp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map,
    Functor.whiskeringLeft_obj_map, NatTrans.comp_app, Functor.whiskerLeft_app] at h₁ h₂
  rw [ConcreteCategory.comp_apply] at h₂
  show (baseChangeHomNatTrans F G β K).app L ((A.systemHomIso K).hom.app L _) =
    (proHomComparison (A.system K ⋙ F) jY
      (coneOfNatIso (baseChangeRestrictIso A F G β K) ⟨G.obj K, 𝟙 _⟩)).app _
      ((Pro.lanSeqHomColimIso F (A.system K)).hom.app _
      ((F.lan.map (A.systemHomIso K).inv).app _
        ((F.lanUnit.app (jX ⋙ coyoneda.obj (op K))).app L _)))
  simp only [ConcreteCategory.comp_apply, Iso.hom_inv_id_app_apply] at h₁
  rw [← h₁]
  show _ = (proHomComparison (A.system K ⋙ F) jY
      (coneOfNatIso (baseChangeRestrictIso A F G β K) ⟨G.obj K, 𝟙 _⟩)).app _
    ((Pro.lanSeqHomColimHom F (A.system K)).app _ _)
  rw [h₂, Pro.seqHomColimToComp_app_seqStage, proHomComparison_stage]
  show (baseChangeHomNatTrans F G β K).app L ((proHomComparison (A.system K) jX
    (coneOfNatIso (A.restrictIso K) ⟨K, 𝟙 _⟩)).app L (Pro.seqStage (A.system K) g)) = _
  rw [proHomComparison_stage]
  show G.map ((𝟙 K ≫ (A.restrictIso K).inv.app _) ≫ jX.map g) ≫ β.inv.app L =
    (𝟙 _ ≫ G.map ((A.restrictIso K).inv.app _) ≫ β.inv.app _) ≫ jY.map (F.map g)
  have hβ : β.inv.app ((A.system K).obj (op n)) ≫ jY.map (F.map g) =
      G.map (jX.map g) ≫ β.inv.app L := (β.inv.naturality g).symm
  simp only [Category.id_comp, G.map_comp, Category.assoc, hβ]

/-- Under the identification of Stacks 0G2H for the image system `(F K_n)`, the base change map
on functors of points is an isomorphism. -/
public lemma isIso_baseChangePointsHom (K : 𝒞)
    (hlift : ∀ N, RestrictionLifting (A.system K ⋙ F) jY N) :
    IsIso (baseChangePointsHom F G β K) := by
  rw [baseChangePointsHom_eq A F G β K]
  have h₁ : IsIso (proHomComparison (A.system K ⋙ F) jY
      (coneOfNatIso (baseChangeRestrictIso A F G β K) ⟨G.obj K, 𝟙 _⟩)) :=
    (restrictHomIso (A.system K ⋙ F) jY (G.obj K) (baseChangeRestrictIso A F G β K)
      hlift).isIso_hom
  have h₂ : IsIso (F.lan.map (A.systemHomIso K).inv) := Functor.map_isIso _ _
  exact IsIso.comp_isIso' h₂ (IsIso.comp_isIso' (Iso.isIso_hom _) h₁)

/-- **Base change of extension by zero along a functor.** Let `j^* : 𝒟 ⥤ 𝒞`, `j'^* : 𝒟' ⥤ 𝒞'`
carry Deligne-system assignments `A`, `A'`, and let `F : 𝒟 ⥤ 𝒟'`, `G : 𝒞 ⥤ 𝒞'` with
`β : F ⋙ j'^* ≅ j^* ⋙ G`. If for every `K` the image `(F K_n)` of the system assigned to `K`
satisfies Stacks 0G2H for `j'^*`, then `Rj'_! ∘ G ≅ Pro F ∘ Rj_!`; on functors of points the
isomorphism is the left Kan extension of `α ↦ β⁻¹ ∘ G α`. -/
public def baseChangeShriekOfLifting
    (hlift : ∀ (K : 𝒞) (N : 𝒟'), RestrictionLifting (A.system K ⋙ F) jY N) :
    G ⋙ extensionByZero jY A'.toAssignment ≅ extensionByZero jX A.toAssignment ⋙ ProSeq.map F :=
  NatIso.ofComponents
    (fun K => (ObjectProperty.isoMk (IsSequentialProObject 𝒟')
      (X := ((extensionByZero jX A.toAssignment ⋙ ProSeq.map F).obj K).unop)
      (Y := ((G ⋙ extensionByZero jY A'.toAssignment).obj K).unop)
      (@asIso _ _ _ _ (baseChangePointsHom F G β K)
        (isIso_baseChangePointsHom A F G β K (hlift K)))).op)
    (fun φ => Quiver.Hom.unop_inj (ObjectProperty.hom_ext _
      (baseChangePointsHom_naturality F G β φ).symm))

end Lifting

end CategoryTheory

end
