module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProductFlatDescent
public import StacksFrontier.CategoryTheory.Limits.KernelPairBaseChange
public import StacksFrontier.CategoryTheory.Sites.RelocalizationMorphism

/-!
# Charts of a system of base changes of an algebraic space

Let `X₀` be an algebraic space over `S`, `T : I ⥤ (Sch/S)` a system of schemes over `S` with a
cone `c`, `i₀ : I`, and `a₀ : h_{U₀} ⟶ h_{T i₀} ⨯ X₀` a morphism from a scheme. The charts
`U₀ ×_{T i₀} T j` of the base changes `h_{T j} ⨯ X₀`
(`AlgebraicGeometry.Space.productChartMap`) form a system indexed by the morphisms `j ⟶ i₀`, and
if `c` is a limit of the underlying schemes then so is the chart `U₀ ×_{T i₀} c.pt` of the base
change to `c.pt`. A kernel pair of `a₀` base changes to a kernel pair of each chart.

## Main definitions

* `AlgebraicGeometry.Space.productChartSystem`: the system `U₀ ×_{T i₀} T j`.
* `AlgebraicGeometry.Space.productChartCone`: the cone `U₀ ×_{T i₀} c.pt`.

## Main results

* `AlgebraicGeometry.Space.isLimit_productChartCone`: it is a limit on underlying schemes.
* `AlgebraicGeometry.Space.productChartMap_comp_productSpaceMap`: the charts are compatible.
* `AlgebraicGeometry.Space.isPullback_productChartKernelPair`: base change of a kernel pair.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] IsCofiltered.isConnected preservesLimitsOfShape_walkingCospan_toScheme

section BaseChange

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {I : Type u} [Category.{u} I] (T : I ⥤ BigFppfOver B S hS) (c : Cone T) (i₀ : I)
  {U₀ : BigFppfOver B S hS} (p : U₀ ⟶ T.obj i₀)

/-- The system of base changes `T j ×_{T i₀} U₀`, indexed by the morphisms `j ⟶ i₀`. -/
noncomputable abbrev postPullbackSystem : Over i₀ ⥤ BigFppfOver B S hS :=
  Over.post T ⋙ Over.pullback p ⋙ Over.forget U₀

/-- The base change `c.pt ×_{T i₀} U₀`, as a cone over the system of base changes. -/
noncomputable abbrev postPullbackCone : Cone (postPullbackSystem T i₀ p) :=
  (Over.pullback p ⋙ Over.forget U₀).mapCone ((Over.conePost T i₀).obj c)

/-- **The base change of the limit is the limit of the base changes**, on underlying schemes, for
a cofiltered system. -/
noncomputable def isLimitPostPullbackCone [IsCofiltered I]
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) :
    IsLimit ((BigFppfOver.toScheme B S hS).mapCone (postPullbackCone T c i₀ p)) := by
  have h₁ : IsLimit ((Over.post (BigFppfOver.toScheme B S hS)).mapCone
      ((Over.conePost T i₀).obj c)) := Over.isLimitConePost i₀ hc
  have h₂ := isLimitOfPreserves
    (Over.pullback ((BigFppfOver.toScheme B S hS).map p) ⋙ Over.forget _) h₁
  exact IsLimit.mapConeEquiv (Functor.isoWhiskerRight
    (Over.postPullbackIso (BigFppfOver.toScheme B S hS) p).symm (Over.forget _)) h₂

end BaseChange

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (X₀ : AlgebraicSpaces B S hS)
  {I : Type u} [Category.{u} I] (T : I ⥤ BigFppfOver B S hS) (i₀ : I)
  {U₀ : BigFppfOver B S hS} (a₀ : yoneda.obj U₀ ⟶ (productSpace X₀ (T.obj i₀)).1)

/-- The system of charts `U₀ ×_{T i₀} T j` of the base changes `h_{T j} ⨯ X₀`, indexed by the
morphisms `j ⟶ i₀`. -/
noncomputable def productChartSystem : Over i₀ ⥤ BigFppfOver B S hS where
  obj k := pullback (productChartBase X₀ a₀) (T.map k.hom)
  map {k k'} f := pullback.map _ _ _ _ (𝟙 _) (T.map f.left) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ← T.map_comp, Over.w f])
  map_id k := by
    apply pullback.hom_ext <;> simp
  map_comp f g := by
    apply pullback.hom_ext <;> simp

/-- The object of `AlgebraicGeometry.Space.productChartSystem` at `k : j ⟶ i₀` is the fibre
product `U₀ ×_{T i₀} T j`. -/
theorem productChartSystem_obj (k : Over i₀) :
    (productChartSystem X₀ T i₀ a₀).obj k = pullback (productChartBase X₀ a₀) (T.map k.hom) :=
  rfl

/-- The chart `U₀ ×_{T i₀} c.pt` of the base change to the cone point. -/
noncomputable def productChartCone (c : Cone T) : Cone (productChartSystem X₀ T i₀ a₀) where
  pt := pullback (productChartBase X₀ a₀) (c.π.app i₀)
  π :=
    { app k := pullback.map _ _ _ _ (𝟙 _) (c.π.app k.left) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, c.w])
      naturality {k k'} f := by
        apply pullback.hom_ext <;> simp [productChartSystem] }

/-- The transition morphisms of `AlgebraicGeometry.Space.postPullbackSystem` are `T f` on the
first factor. -/
theorem postPullbackSystem_map_fst {p : U₀ ⟶ T.obj i₀} {k k' : Over i₀} (f : k ⟶ k') :
    (postPullbackSystem T i₀ p).map f ≫ pullback.fst ((Over.post T).obj k').hom p =
      pullback.fst ((Over.post T).obj k).hom p ≫ T.map f.left :=
  pullback.lift_fst _ _ _

/-- The transition morphisms of `AlgebraicGeometry.Space.postPullbackSystem` are the identity on
the second factor. -/
theorem postPullbackSystem_map_snd {p : U₀ ⟶ T.obj i₀} {k k' : Over i₀} (f : k ⟶ k') :
    (postPullbackSystem T i₀ p).map f ≫ pullback.snd ((Over.post T).obj k').hom p =
      pullback.snd ((Over.post T).obj k).hom p :=
  pullback.lift_snd _ _ _

/-- The transition morphisms of `AlgebraicGeometry.Space.productChartSystem` are the identity on
the first factor. -/
theorem productChartSystem_map_fst {k k' : Over i₀} (f : k ⟶ k') :
    (productChartSystem X₀ T i₀ a₀).map f ≫ pullback.fst (productChartBase X₀ a₀) (T.map k'.hom) =
      pullback.fst (productChartBase X₀ a₀) (T.map k.hom) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The transition morphisms of `AlgebraicGeometry.Space.productChartSystem` are `T f` on the
second factor. -/
theorem productChartSystem_map_snd {k k' : Over i₀} (f : k ⟶ k') :
    (productChartSystem X₀ T i₀ a₀).map f ≫ pullback.snd (productChartBase X₀ a₀) (T.map k'.hom) =
      pullback.snd (productChartBase X₀ a₀) (T.map k.hom) ≫ T.map f.left :=
  pullback.lift_snd _ _ _

/-- The charts of the system, compared with the base changes of the original one by the
symmetry of fibre products. -/
noncomputable def productChartSystemIso :
    productChartSystem X₀ T i₀ a₀ ≅ postPullbackSystem T i₀ (productChartBase X₀ a₀) :=
  NatIso.ofComponents
    (fun k => pullbackSymmetry (productChartBase X₀ a₀) ((Over.post T).obj k).hom)
    fun f => pullback.hom_ext
      ((Category.assoc _ _ _).trans <|
        (congrArg (_ ≫ ·) (pullbackSymmetry_hom_comp_fst _ _)).trans <|
        (productChartSystem_map_snd X₀ T i₀ a₀ f).trans <|
        ((pullbackSymmetry_hom_comp_fst_assoc _ _ _).symm.trans
          (congrArg (_ ≫ ·) (postPullbackSystem_map_fst T i₀ f).symm)).trans
        (Category.assoc _ _ _).symm)
      ((Category.assoc _ _ _).trans <|
        (congrArg (_ ≫ ·) (pullbackSymmetry_hom_comp_snd _ _)).trans <|
        (productChartSystem_map_fst X₀ T i₀ a₀ f).trans <|
        ((pullbackSymmetry_hom_comp_snd _ _).symm.trans
          (congrArg (_ ≫ ·) (postPullbackSystem_map_snd T i₀ f).symm)).trans
        (Category.assoc _ _ _).symm)

/-- The projections of `AlgebraicGeometry.Space.postPullbackCone` are `c.π` on the first
factor. -/
theorem postPullbackCone_π_app_fst (c : Cone T) {p : U₀ ⟶ T.obj i₀} (k : Over i₀) :
    (postPullbackCone T c i₀ p).π.app k ≫ pullback.fst ((Over.post T).obj k).hom p =
      pullback.fst ((Over.conePost T i₀).obj c).pt.hom p ≫ c.π.app k.left :=
  pullback.lift_fst _ _ _

/-- The projections of `AlgebraicGeometry.Space.postPullbackCone` are the identity on the second
factor. -/
theorem postPullbackCone_π_app_snd (c : Cone T) {p : U₀ ⟶ T.obj i₀} (k : Over i₀) :
    (postPullbackCone T c i₀ p).π.app k ≫ pullback.snd ((Over.post T).obj k).hom p =
      pullback.snd ((Over.conePost T i₀).obj c).pt.hom p :=
  pullback.lift_snd _ _ _

/-- The projections of `AlgebraicGeometry.Space.productChartCone` are the identity on the first
factor. -/
theorem productChartCone_π_app_fst (c : Cone T) (k : Over i₀) :
    (productChartCone X₀ T i₀ a₀ c).π.app k ≫ pullback.fst (productChartBase X₀ a₀) (T.map k.hom) =
      pullback.fst (productChartBase X₀ a₀) (c.π.app i₀) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The projections of `AlgebraicGeometry.Space.productChartCone` are `c.π` on the second
factor. -/
theorem productChartCone_π_app_snd (c : Cone T) (k : Over i₀) :
    (productChartCone X₀ T i₀ a₀ c).π.app k ≫ pullback.snd (productChartBase X₀ a₀) (T.map k.hom) =
      pullback.snd (productChartBase X₀ a₀) (c.π.app i₀) ≫ c.π.app k.left :=
  pullback.lift_snd _ _ _

/-- **The chart of the base change to the limit is the limit of the charts**, on underlying
schemes, for a cofiltered system. -/
noncomputable def isLimitProductChartCone [IsCofiltered I] (c : Cone T)
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) :
    IsLimit ((BigFppfOver.toScheme B S hS).mapCone (productChartCone X₀ T i₀ a₀ c)) := by
  refine (IsLimit.postcomposeHomEquiv (Functor.isoWhiskerRight (productChartSystemIso X₀ T i₀ a₀)
    (BigFppfOver.toScheme B S hS)) _) ?_
  refine IsLimit.ofIsoLimit (isLimitPostPullbackCone T c i₀ (productChartBase X₀ a₀) hc) ?_
  refine Cone.ext ((BigFppfOver.toScheme B S hS).mapIso
    (pullbackSymmetry (productChartBase X₀ a₀) ((Over.conePost T i₀).obj c).pt.hom).symm)
    fun k => ?_
  have key : (postPullbackCone T c i₀ (productChartBase X₀ a₀)).π.app k =
      (pullbackSymmetry (productChartBase X₀ a₀) ((Over.conePost T i₀).obj c).pt.hom).inv ≫
        (productChartCone X₀ T i₀ a₀ c).π.app k ≫ (productChartSystemIso X₀ T i₀ a₀).hom.app k :=
    pullback.hom_ext
      ((postPullbackCone_π_app_fst T i₀ c k).trans <| Eq.symm <|
        (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans <|
        (congrArg (fun x => _ ≫ _ ≫ x) (pullbackSymmetry_hom_comp_fst _ _)).trans <|
        (congrArg (_ ≫ ·) (productChartCone_π_app_snd X₀ T i₀ a₀ c k)).trans <|
        pullbackSymmetry_inv_comp_snd_assoc _ _ _)
      ((postPullbackCone_π_app_snd T i₀ c k).trans <| Eq.symm <|
        (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans <|
        (congrArg (fun x => _ ≫ _ ≫ x) (pullbackSymmetry_hom_comp_snd _ _)).trans <|
        (congrArg (_ ≫ ·) (productChartCone_π_app_fst X₀ T i₀ a₀ c k)).trans <|
        pullbackSymmetry_inv_comp_fst _ _)
  exact (congrArg (BigFppfOver.toScheme B S hS).map key).trans <|
    ((BigFppfOver.toScheme B S hS).map_comp _ _).trans <|
      congrArg (_ ≫ ·) ((BigFppfOver.toScheme B S hS).map_comp _ _)

/-! ### Compatibility of the charts -/

section Charts

variable {T₀ : BigFppfOver B S hS} (a₁ : yoneda.obj U₀ ⟶ (productSpace X₀ T₀).1)

/-- **The charts are compatible with the morphisms of base changes.** -/
theorem productChartMap_comp_productSpaceMap {V V' : BigFppfOver B S hS} (k : V ⟶ T₀)
    (k' : V' ⟶ T₀) (m : V' ⟶ V) (hm : m ≫ k = k') :
    productChartMap X₀ a₁ k' ≫ (productSpaceMap X₀ m).hom =
      yoneda.map (pullback.map _ _ _ _ (𝟙 _) m (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
        (by rw [Category.comp_id, hm])) ≫ productChartMap X₀ a₁ k := by
  dsimp only [productSpace, productChartMap, productSpaceMap_hom]
  apply prod.hom_ext
  · simp only [Category.assoc, prod.map_fst, prod.lift_fst, prod.lift_fst_assoc,
      ← Functor.map_comp, pullback.lift_snd]
  · simp only [Category.assoc, prod.map_snd, Category.comp_id, prod.lift_snd,
      ← Functor.map_comp_assoc, pullback.lift_fst]

/-- The chart is the base change of `a₁` along `h_{T₀} ⨯ X₀`'s projection, written as a
commuting square. -/
theorem productChartMap_comp_productSpaceMap_self {V : BigFppfOver B S hS} (k : V ⟶ T₀) :
    productChartMap X₀ a₁ k ≫ (productSpaceMap X₀ k).hom =
      yoneda.map (pullback.fst (productChartBase X₀ a₁) k) ≫ a₁ :=
  (isPullback_productChartMap X₀ a₁ k).w.symm

/-- If `yoneda.map g ≫ a₁ = a₂`, then the base morphism of `a₂` is `g` followed by the base
morphism of `a₁`. -/
theorem productChartBase_comp {R₀ : BigFppfOver B S hS} (g : R₀ ⟶ U₀)
    (a₂ : yoneda.obj R₀ ⟶ (productSpace X₀ T₀).1) (hg : yoneda.map g ≫ a₁ = a₂) :
    productChartBase X₀ a₂ = g ≫ productChartBase X₀ a₁ :=
  Yoneda.fullyFaithful.map_injective (by
    subst hg
    rw [yoneda_map_productChartBase, Functor.map_comp, yoneda_map_productChartBase]
    exact Category.assoc _ _ _)

/-- The morphism of charts induced by a morphism `g` of schemes over `h_{T₀} ⨯ X₀`. -/
noncomputable def productChartPairMap {R₀ : BigFppfOver B S hS} (g : R₀ ⟶ U₀)
    (a₂ : yoneda.obj R₀ ⟶ (productSpace X₀ T₀).1) (hg : yoneda.map g ≫ a₁ = a₂)
    {V : BigFppfOver B S hS} (k : V ⟶ T₀) :
    pullback (productChartBase X₀ a₂) k ⟶ pullback (productChartBase X₀ a₁) k :=
  pullback.map _ _ _ _ g (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, productChartBase_comp X₀ a₁ g a₂ hg])
    (by rw [Category.comp_id, Category.id_comp])

/-- `AlgebraicGeometry.Space.productChartPairMap` is `g` on the first factor. -/
theorem productChartPairMap_fst {R₀ : BigFppfOver B S hS} (g : R₀ ⟶ U₀)
    (a₂ : yoneda.obj R₀ ⟶ (productSpace X₀ T₀).1) (hg : yoneda.map g ≫ a₁ = a₂)
    {V : BigFppfOver B S hS} (k : V ⟶ T₀) :
    productChartPairMap X₀ a₁ g a₂ hg k ≫ pullback.fst _ _ = pullback.fst _ _ ≫ g :=
  pullback.lift_fst _ _ _

/-- `AlgebraicGeometry.Space.productChartPairMap` is the identity on the second factor. -/
theorem productChartPairMap_snd {R₀ : BigFppfOver B S hS} (g : R₀ ⟶ U₀)
    (a₂ : yoneda.obj R₀ ⟶ (productSpace X₀ T₀).1) (hg : yoneda.map g ≫ a₁ = a₂)
    {V : BigFppfOver B S hS} (k : V ⟶ T₀) :
    productChartPairMap X₀ a₁ g a₂ hg k ≫ pullback.snd _ _ = pullback.snd _ _ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The second component of the chart `AlgebraicGeometry.Space.productChartMap` is the first
projection followed by `a₁` and the projection to `X₀`. -/
theorem productChartMap_snd {V : BigFppfOver B S hS} (k : V ⟶ T₀) :
    productChartMap X₀ a₁ k ≫ prod.snd =
      yoneda.map (pullback.fst (productChartBase X₀ a₁) k) ≫ a₁ ≫ prod.snd :=
  prod.lift_snd _ _

/-- The morphism of charts lies over the morphism of the base change. -/
theorem yoneda_map_productChartPairMap {R₀ : BigFppfOver B S hS} (g : R₀ ⟶ U₀)
    (a₂ : yoneda.obj R₀ ⟶ (productSpace X₀ T₀).1) (hg : yoneda.map g ≫ a₁ = a₂)
    {V : BigFppfOver B S hS} (k : V ⟶ T₀) :
    yoneda.map (productChartPairMap X₀ a₁ g a₂ hg k) ≫ productChartMap X₀ a₁ k =
      productChartMap X₀ a₂ k := by
  subst hg
  apply prod.hom_ext
  · exact (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (productChartMap_fst X₀ a₁ k)).trans <|
      (yoneda.map_comp _ _).symm.trans <|
      (congrArg yoneda.map (productChartPairMap_snd X₀ a₁ g _ rfl k)).trans
      (productChartMap_fst X₀ _ k).symm
  · exact (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (productChartMap_snd X₀ a₁ k)).trans <|
      (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ _) (yoneda.map_comp _ _).symm).trans <|
      (congrArg (fun x => yoneda.map x ≫ a₁ ≫ prod.snd)
        (productChartPairMap_fst X₀ a₁ g _ rfl k)).trans <|
      (congrArg (· ≫ _) (yoneda.map_comp _ _)).trans <|
      (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans
      (productChartMap_snd X₀ _ k).symm

/-- **The base change of a kernel pair of `a₁` is a kernel pair of each chart.** -/
theorem isPullback_productChartKernelPair {R₀ : BigFppfOver B S hS} {s₀ t₀ : R₀ ⟶ U₀}
    (hk : IsPullback (yoneda.map s₀) (yoneda.map t₀) a₁ a₁)
    (a₂ : yoneda.obj R₀ ⟶ (productSpace X₀ T₀).1) (hs : yoneda.map s₀ ≫ a₁ = a₂)
    (ht : yoneda.map t₀ ≫ a₁ = a₂) {V : BigFppfOver B S hS} (k : V ⟶ T₀) :
    IsPullback (yoneda.map (productChartPairMap X₀ a₁ s₀ a₂ hs k))
      (yoneda.map (productChartPairMap X₀ a₁ t₀ a₂ ht k))
      (productChartMap X₀ a₁ k) (productChartMap X₀ a₁ k) := by
  refine IsPullback.of_isPullback_kernelPair hk (isPullback_productChartMap X₀ a₁ k)
    (ρ := yoneda.map (pullback.fst (productChartBase X₀ a₂) k)) ?_ ?_ ?_ ?_
  · rw [← Functor.map_comp, ← Functor.map_comp, productChartPairMap_fst]
  · rw [← Functor.map_comp, ← Functor.map_comp, productChartPairMap_fst]
  · rw [yoneda_map_productChartPairMap, yoneda_map_productChartPairMap]
  · rw [yoneda_map_productChartPairMap, hs]
    exact isPullback_productChartMap X₀ a₂ k

end Charts

/-! ### Affineness and quasi-compactness of the charts -/

section Finiteness

/-- Each transition morphism of `AlgebraicGeometry.Space.productChartSystem` is the base change of
the corresponding transition morphism of `T`. -/
theorem isPullback_productChartSystem_map {k k' : Over i₀} (f : k ⟶ k') :
    IsPullback ((productChartSystem X₀ T i₀ a₀).map f)
      (pullback.snd (productChartBase X₀ a₀) (T.map k.hom))
      (pullback.snd (productChartBase X₀ a₀) (T.map k'.hom)) (T.map f.left) := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback (productChartBase X₀ a₀) (T.map k'.hom))
  rw [productChartSystem_map_fst, ← T.map_comp, Over.w f]
  exact IsPullback.of_hasPullback _ _

/-- On underlying schemes, the object of `AlgebraicGeometry.Space.productChartSystem` at `k` is the
fibre product of the base morphism and `T k`. -/
theorem isPullback_toScheme_productChartSystem_obj (k : Over i₀) :
    IsPullback
      ((BigFppfOver.toScheme B S hS).map (pullback.fst (productChartBase X₀ a₀) (T.map k.hom)))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd (productChartBase X₀ a₀) (T.map k.hom)))
      ((BigFppfOver.toScheme B S hS).map (productChartBase X₀ a₀))
      ((BigFppfOver.toScheme B S hS).map (T.map k.hom)) :=
  (IsPullback.of_hasPullback _ _).map _

variable [∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (T.obj i))]

/-- For a system of affine schemes, the transition morphisms of the system of charts are
affine. -/
instance isAffineHom_productChartSystem_map {k k' : Over i₀} (f : k ⟶ k') :
    _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map ((productChartSystem X₀ T i₀ a₀).map f)) :=
  MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.IsAffineHom)
    ((isPullback_productChartSystem_map X₀ T i₀ a₀ f).map (BigFppfOver.toScheme B S hS)).flip
    (isAffineHom_of_isAffine ((BigFppfOver.toScheme B S hS).map (T.map f.left)))

/-- For a system of affine schemes and quasi-compact `U₀`, every chart of the system is
quasi-compact. -/
instance compactSpace_productChartSystem_obj
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj U₀)] (k : Over i₀) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj ((productChartSystem X₀ T i₀ a₀).obj k)) := by
  have : _root_.AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S hS).map (T.map k.hom)) := isAffineHom_of_isAffine _
  have : _root_.AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map
      (pullback.fst (productChartBase X₀ a₀) (T.map k.hom))) :=
    MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.QuasiCompact)
      (isPullback_toScheme_productChartSystem_obj X₀ T i₀ a₀ k).flip inferInstance
  exact @QuasiCompact.compactSpace_of_compactSpace _ _
    ((BigFppfOver.toScheme B S hS).map (pullback.fst (productChartBase X₀ a₀) (T.map k.hom)))
    this inferInstance

/-- For a system of affine schemes and affine `U₀`, every chart of the system is affine. -/
instance isAffine_productChartSystem_obj [IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)]
    (k : Over i₀) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj ((productChartSystem X₀ T i₀ a₀).obj k)) := by
  have hP := isPullback_toScheme_productChartSystem_obj X₀ T i₀ a₀ k
  exact @IsAffine.of_isIso _ _ hP.isoPullback.hom (Iso.isIso_hom _) inferInstance

/-- For a system of affine schemes with limit `c` and affine `U₀`, the chart over `c.pt` is
affine. -/
theorem isAffine_productChartCone_pt [IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)]
    (c : Cone T) (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (productChartCone X₀ T i₀ a₀ c).pt) := by
  have : ∀ i, IsAffine ((T ⋙ BigFppfOver.toScheme B S hS).obj i) := fun i =>
    inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj (T.obj i)))
  have h₁ : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt) :=
    Scheme.isAffine_of_isLimit (D := T ⋙ BigFppfOver.toScheme B S hS) _ hc
  have hP := (IsPullback.of_hasPullback (productChartBase X₀ a₀) (c.π.app i₀)).map
    (BigFppfOver.toScheme B S hS)
  exact @IsAffine.of_isIso _ _ hP.isoPullback.hom (Iso.isIso_hom _)
    (@AlgebraicGeometry.Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine _ _ _ _ _
      inferInstance h₁ inferInstance)

end Finiteness

end AlgebraicGeometry.Space

end
