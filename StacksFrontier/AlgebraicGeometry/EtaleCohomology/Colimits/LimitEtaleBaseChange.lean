module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.EtaleNeighbourhoodLimitSections

/-!
# Base change of an inverse system of étale neighbourhoods

Let `(W_i)` be an inverse system of étale `S`-schemes over a directed set with a least element,
with limit `T` and `π : T ⟶ S`, and let `φ : A ⟶ S` be a morphism of schemes. The base changes
`A ×_S W_i` form an inverse system of étale `A`-schemes, and `A ×_S T` is their limit. This file
records the system, the cone and the limit property.

## Main definitions

* `Stacks.EtaleCohomology.EtaleLimitSections.baseChangeSystem`: the system `A ×_S W_i`.
* `Stacks.EtaleCohomology.EtaleLimitSections.baseChangeCone`: the cone with apex `A ×_S T`.

## Main results

* `Stacks.EtaleCohomology.EtaleLimitSections.baseChangeConeIsLimit`: it is a limit cone.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology.EtaleLimitSections

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] [OrderBot I]
  {S : Scheme.{u}} (W : Iᵒᵖ ⥤ S.Etale)
  (c : Cone (W ⋙ Scheme.Etale.forget S ⋙ Over.forget S)) {π : c.pt ⟶ S}
  (hπ : ∀ i, c.π.app i ≫ (W.obj i).hom = π) {A : Scheme.{u}} (φ : A ⟶ S)

/-- The base change `A ×_S W_i` of the system. -/
abbrev baseChangeSystem : Iᵒᵖ ⥤ A.Etale := W ⋙ smallEtaleBaseChange φ

include hπ in
/-- The leg `A ×_S T ⟶ A ×_S W_i`. -/
def baseChangeLeg (i : Iᵒᵖ) : pullback φ π ⟶ pullback (W.obj i).hom φ :=
  pullback.lift (pullback.snd φ π ≫ c.π.app i) (pullback.fst φ π)
    ((Category.assoc _ _ _).trans ((congrArg (pullback.snd φ π ≫ ·) (hπ i)).trans
      pullback.condition.symm))

include hπ in
/-- The leg `A ×_S T ⟶ A ×_S W_i` followed by the projection to `W_i` is the projection
`A ×_S T ⟶ T` followed by the leg `T ⟶ W_i`. -/
theorem baseChangeLeg_fst (i : Iᵒᵖ) :
    baseChangeLeg W c hπ φ i ≫ pullback.fst (W.obj i).hom φ = pullback.snd φ π ≫ c.π.app i :=
  pullback.lift_fst _ _ _

include hπ in
/-- The leg `A ×_S T ⟶ A ×_S W_i` followed by the projection to `A` is the projection
`A ×_S T ⟶ A`. -/
theorem baseChangeLeg_snd (i : Iᵒᵖ) :
    baseChangeLeg W c hπ φ i ≫ pullback.snd (W.obj i).hom φ = pullback.fst φ π :=
  pullback.lift_snd _ _ _

include hπ in
/-- The cone `A ×_S T` over the system of base changes. -/
def baseChangeCone : Cone (baseChangeSystem W φ ⋙ Scheme.Etale.forget A ⋙ Over.forget A) where
  pt := pullback φ π
  π :=
    { app := fun i => baseChangeLeg W c hπ φ i
      naturality := fun i j a => by
        change 𝟙 _ ≫ baseChangeLeg W c hπ φ j =
          baseChangeLeg W c hπ φ i ≫ ((smallEtaleBaseChange φ).map (W.map a)).left
        rw [Category.id_comp]
        have h1 := smallEtaleBaseChange_map_left_fst φ (W.map a)
        have h2 : ((smallEtaleBaseChange φ).map (W.map a)).left ≫ pullback.snd (W.obj j).hom φ =
            pullback.snd (W.obj i).hom φ :=
          MorphismProperty.Over.w ((smallEtaleBaseChange φ).map (W.map a))
        have h3 := c.w a
        apply pullback.hom_ext
        · refine (baseChangeLeg_fst W c hπ φ j).trans ?_
          refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h1)).symm
          refine Eq.trans ?_ (Category.assoc _ _ _)
          refine Eq.trans ?_ (congrArg (· ≫ _) (baseChangeLeg_fst W c hπ φ i)).symm
          exact (congrArg (pullback.snd φ π ≫ ·) h3.symm).trans (Category.assoc _ _ _).symm
        · refine (baseChangeLeg_snd W c hπ φ j).trans ?_
          exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h2).trans
            (baseChangeLeg_snd W c hπ φ i))).symm }

/-- Each leg of `baseChangeCone` is a morphism over `A`: composed with the structure morphism
`A ×_S W_i ⟶ A` it is the projection `A ×_S T ⟶ A`. -/
theorem baseChangeCone_π_comp_hom (i : Iᵒᵖ) :
    (baseChangeCone W c hπ φ).π.app i ≫ ((baseChangeSystem W φ).obj i).hom = pullback.fst φ π :=
  baseChangeLeg_snd W c hπ φ i

include hπ in
/-- **`A ×_S T` is the limit of the `A ×_S W_i`.** -/
def baseChangeConeIsLimit (hc : IsLimit c) : IsLimit (baseChangeCone W c hπ φ) := by
  -- the legs of a cone over the base changes, read in `W_i` and in `A`
  have hsnd : ∀ (d : Cone (baseChangeSystem W φ ⋙ Scheme.Etale.forget A ⋙ Over.forget A))
      (i : Iᵒᵖ), d.π.app i ≫ pullback.snd (W.obj i).hom φ =
        d.π.app (op ⊥) ≫ pullback.snd (W.obj (op ⊥)).hom φ := fun d i => by
    have h2 : ((smallEtaleBaseChange φ).map (W.map (homOfLE (bot_le : ⊥ ≤ i.unop)).op)).left ≫
        pullback.snd (W.obj (op ⊥)).hom φ = pullback.snd (W.obj i).hom φ :=
      MorphismProperty.Over.w _
    exact (congrArg (_ ≫ ·) h2.symm).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) (d.w (homOfLE (bot_le : ⊥ ≤ i.unop)).op)))
  let e : ∀ d : Cone (baseChangeSystem W φ ⋙ Scheme.Etale.forget A ⋙ Over.forget A),
      Cone (W ⋙ Scheme.Etale.forget S ⋙ Over.forget S) := fun d =>
    { pt := d.pt
      π :=
        { app := fun i => d.π.app i ≫ pullback.fst (W.obj i).hom φ
          naturality := fun i j a => by
            change 𝟙 _ ≫ d.π.app j ≫ pullback.fst (W.obj j).hom φ =
              (d.π.app i ≫ pullback.fst (W.obj i).hom φ) ≫ (W.map a).left
            have h1 := smallEtaleBaseChange_map_left_fst φ (W.map a)
            refine (Category.id_comp _).trans ?_
            refine (congrArg (· ≫ _) (d.w a).symm).trans ?_
            refine (Category.assoc _ _ _).trans ?_
            refine (congrArg (_ ≫ ·) ((Category.id_comp _).symm.trans ?_)).trans
              (Category.assoc _ _ _).symm
            exact (congrArg (fun m => m ≫ pullback.fst (W.obj j).hom φ) (Category.id_comp _)).trans
              h1 } }
  have hcond : ∀ d, (d.π.app (op ⊥) ≫ pullback.snd (W.obj (op ⊥)).hom φ) ≫ φ =
      hc.lift (e d) ≫ π := fun d => by
    refine Eq.trans ?_ (congrArg (_ ≫ ·) (hπ (op ⊥)))
    refine Eq.trans ?_ (Category.assoc _ _ _)
    refine Eq.trans ?_ (congrArg (· ≫ _) (hc.fac (e d) (op ⊥))).symm
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition.symm).trans
      (Category.assoc _ _ _).symm)
  refine
    { lift := fun d => pullback.lift (d.π.app (op ⊥) ≫ pullback.snd (W.obj (op ⊥)).hom φ)
        (hc.lift (e d)) (hcond d)
      fac := fun d i => ?_
      uniq := fun d m hm => ?_ }
  · change pullback.lift _ _ (hcond d) ≫ baseChangeLeg W c hπ φ i = d.π.app i
    apply pullback.hom_ext
    · refine (Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (baseChangeLeg_fst W c hπ φ i)).trans ?_)
      refine (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) (pullback.lift_snd _ _ _)).trans ?_)
      exact hc.fac (e d) i
    · refine (Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (baseChangeLeg_snd W c hπ φ i)).trans ?_)
      exact (pullback.lift_fst _ _ _).trans (hsnd d i).symm
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      refine Eq.trans ?_ (congrArg (· ≫ _) (hm (op ⊥)))
      exact ((congrArg (m ≫ ·) (baseChangeLeg_snd W c hπ φ (op ⊥))).symm.trans
        (Category.assoc _ _ _).symm)
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      refine hc.hom_ext fun i => ?_
      refine Eq.trans ?_ (hc.fac (e d) i).symm
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans ?_ (congrArg (· ≫ _) (hm i))
      exact ((congrArg (m ≫ ·) (baseChangeLeg_fst W c hπ φ i)).symm.trans
        (Category.assoc _ _ _).symm)

end Stacks.EtaleCohomology.EtaleLimitSections
