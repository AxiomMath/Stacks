module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.Limits.PullbackOfLimitCones
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Filtered.Connected

/-!
# Fibre products of inverse systems in the big affine fppf category

Let `S` be a scheme of a big fppf site. Given inverse systems `F₁ ⟶ F₃ ⟵ F₂` of affine schemes
over `S`, indexed by a category `J`, their fibre product taken index by index is again an inverse
system of affine schemes over `S`. If each of `F₁`, `F₂`, `F₃` is presented as an inverse limit by
a cone, compatibly with the two transformations, then the fibre product of the three cone points
is the inverse limit of the fibre product system.

This is what is needed to pass from an affine inverse limit `T = lim Tᵢ` to the inverse limits
`W ×_{T₀} T = lim W ×_{T₀} Tᵢ` of the base changes of a scheme `W` over a stage `T₀`, and to the
inverse limits of the fibre products of such base changes, which index the overlaps of a covering
descended to a finite stage.

## Main definitions

* `AlgebraicGeometry.BigAffineFppf.pullbackSystem`: the index-wise fibre product of two inverse
  systems over a third.
* `AlgebraicGeometry.BigAffineFppf.pullbackSystemCone`: its cone with the fibre product of the cone
  points as cone point.
* `AlgebraicGeometry.BigAffineFppf.overSystem`: the restriction of an inverse system to the
  category of indices over a fixed index, and `AlgebraicGeometry.BigAffineFppf.overCone` the
  restricted cone.
* `AlgebraicGeometry.BigAffineFppf.baseChangeSystem`: the base changes `W ×_{D i₀} D j` of an
  object `W` over a stage `D i₀` along the transition maps, indexed by the indices over `i₀`.

## Main results

* `AlgebraicGeometry.BigAffineFppf.isLimit_pullbackSystemCone`: the fibre product cone is a limit
  cone in schemes as soon as the three given cones are.
* `AlgebraicGeometry.BigAffineFppf.isLimit_overCone` and
  `AlgebraicGeometry.BigAffineFppf.isLimit_baseChangeCone`: the same for the restricted system and
  for the base change system.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.BigAffineFppf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A fibre product, in the big fppf category over `S`, of objects with affine underlying schemes
has affine underlying scheme. -/
lemma isAffineOver_pullback {X₁ X₂ X₃ : BigFppfOver B S hS} (a : X₁ ⟶ X₃) (b : X₂ ⟶ X₃)
    (h₁ : IsAffineOver B S hS X₁) (h₂ : IsAffineOver B S hS X₂) (h₃ : IsAffineOver B S hS X₃) :
    IsAffineOver B S hS (pullback a b) :=
  have := h₁
  have := h₂
  have := h₃
  IsAffine.of_isIso (PreservesPullback.iso (BigFppfOver.toScheme B S hS) a b).hom

variable {J : Type v} [Category.{w} J] {F₁ F₂ F₃ : J ⥤ BigFppfOver B S hS}
  (α : F₁ ⟶ F₃) (β : F₂ ⟶ F₃)

/-- The index-wise fibre product of two inverse systems over a third, in the big fppf category
over `S`. -/
@[simps]
noncomputable def pullbackSystem : J ⥤ BigFppfOver B S hS where
  obj j := pullback (α.app j) (β.app j)
  map {j k} t := pullback.map _ _ _ _ (F₁.map t) (F₂.map t) (F₃.map t)
      (α.naturality t).symm (β.naturality t).symm
  map_id j := by
    apply pullback.hom_ext
    · rw [pullback.map, pullback.lift_fst, F₁.map_id, Category.comp_id, Category.id_comp]
    · rw [pullback.map, pullback.lift_snd, F₂.map_id, Category.comp_id, Category.id_comp]
  map_comp t t' := by
    apply pullback.hom_ext
    · rw [pullback.map, pullback.lift_fst, Category.assoc, pullback.map, pullback.map,
        pullback.lift_fst, pullback.lift_fst_assoc, F₁.map_comp, Category.assoc]
    · rw [pullback.map, pullback.lift_snd, Category.assoc, pullback.map, pullback.map,
        pullback.lift_snd, pullback.lift_snd_assoc, F₂.map_comp, Category.assoc]

/-- The first projection of the fibre product system. -/
@[simps]
noncomputable def pullbackSystemFst : pullbackSystem α β ⟶ F₁ where
  app _ := pullback.fst _ _
  naturality _ _ _ := pullback.lift_fst _ _ _

/-- The second projection of the fibre product system. -/
@[simps]
noncomputable def pullbackSystemSnd : pullbackSystem α β ⟶ F₂ where
  app _ := pullback.snd _ _
  naturality _ _ _ := pullback.lift_snd _ _ _

/-- The commutative square of the fibre product system at an index. -/
@[reassoc]
lemma pullbackSystem_condition (j : J) :
    (pullbackSystemFst α β).app j ≫ α.app j = (pullbackSystemSnd α β).app j ≫ β.app j :=
  pullback.condition

/-- The fibre product system forms a commutative square over `F₃`:
`pullbackSystemFst α β ≫ α = pullbackSystemSnd α β ≫ β`. -/
@[reassoc]
lemma pullbackSystemFst_comp :
    pullbackSystemFst α β ≫ α = pullbackSystemSnd α β ≫ β :=
  NatTrans.ext (funext fun j => pullback.condition (f := α.app j) (g := β.app j))

variable {α β} {c₁ : Cone F₁} {c₂ : Cone F₂} {c₃ : Cone F₃}
  {g₁ : c₁.pt ⟶ c₃.pt} {g₂ : c₂.pt ⟶ c₃.pt}

/-- The cone projections of the fibre product cone are compatible with the transition maps. -/
lemma pullbackMap_comp_pullbackSystem_map
    (hg₁ : ∀ j, c₁.π.app j ≫ α.app j = g₁ ≫ c₃.π.app j)
    (hg₂ : ∀ j, c₂.π.app j ≫ β.app j = g₂ ≫ c₃.π.app j) {j k : J} (t : j ⟶ k) :
    pullback.map _ _ _ _ (c₁.π.app j) (c₂.π.app j) (c₃.π.app j) (hg₁ j).symm (hg₂ j).symm ≫
        pullback.map _ _ _ _ (F₁.map t) (F₂.map t) (F₃.map t)
          (α.naturality t).symm (β.naturality t).symm =
      pullback.map _ _ _ _ (c₁.π.app k) (c₂.π.app k) (c₃.π.app k) (hg₁ k).symm (hg₂ k).symm := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.map, pullback.map, pullback.map,
      pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc, c₁.w t]
  · rw [Category.assoc, pullback.map, pullback.map, pullback.map,
      pullback.lift_snd, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc, c₂.w t]

/-- The cone over the fibre product system whose cone point is the fibre product of the cone
points of two cones over the given systems, mapping compatibly to a cone over the third. -/
@[simps]
noncomputable def pullbackSystemCone
    (hg₁ : ∀ j, c₁.π.app j ≫ α.app j = g₁ ≫ c₃.π.app j)
    (hg₂ : ∀ j, c₂.π.app j ≫ β.app j = g₂ ≫ c₃.π.app j) :
    Cone (pullbackSystem α β) where
  pt := pullback g₁ g₂
  π :=
    { app j := pullback.map _ _ _ _ (c₁.π.app j) (c₂.π.app j) (c₃.π.app j)
          (hg₁ j).symm (hg₂ j).symm
      naturality _ _ t :=
        (Category.id_comp _).trans (pullbackMap_comp_pullbackSystem_map hg₁ hg₂ t).symm }


/-- The fibre product cone followed by the first projection is the first projection of the
cone point followed by the cone `c₁`. -/
@[reassoc]
lemma pullbackSystemCone_π_app_fst
    (hg₁ : ∀ j, c₁.π.app j ≫ α.app j = g₁ ≫ c₃.π.app j)
    (hg₂ : ∀ j, c₂.π.app j ≫ β.app j = g₂ ≫ c₃.π.app j) (j : J) :
    (pullbackSystemCone hg₁ hg₂).π.app j ≫ (pullbackSystemFst α β).app j =
      pullback.fst g₁ g₂ ≫ c₁.π.app j :=
  pullback.lift_fst _ _ _

/-- The fibre product cone followed by the second projection is the second projection of the
cone point followed by the cone `c₂`. -/
@[reassoc]
lemma pullbackSystemCone_π_app_snd
    (hg₁ : ∀ j, c₁.π.app j ≫ α.app j = g₁ ≫ c₃.π.app j)
    (hg₂ : ∀ j, c₂.π.app j ≫ β.app j = g₂ ≫ c₃.π.app j) (j : J) :
    (pullbackSystemCone hg₁ hg₂).π.app j ≫ (pullbackSystemSnd α β).app j =
      pullback.snd g₁ g₂ ≫ c₂.π.app j :=
  pullback.lift_snd _ _ _

/-- **Fibre products of inverse limits are inverse limits.** If the three given cones are limit
cones after passing to schemes, so is the fibre product cone. -/
noncomputable def isLimit_pullbackSystemCone
    (hg₁ : ∀ j, c₁.π.app j ≫ α.app j = g₁ ≫ c₃.π.app j)
    (hg₂ : ∀ j, c₂.π.app j ≫ β.app j = g₂ ≫ c₃.π.app j)
    (hc₁ : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c₁))
    (hc₂ : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c₂))
    (hc₃ : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c₃)) :
    IsLimit ((BigFppfOver.toScheme B S hS).mapCone (pullbackSystemCone hg₁ hg₂)) := by
  let T := BigFppfOver.toScheme B S hS
  refine isLimitOfIsPullbackOfIsLimit (α := Functor.whiskerRight α T)
    (β := Functor.whiskerRight β T)
    (π₁ := Functor.whiskerRight (pullbackSystemFst α β) T)
    (π₂ := Functor.whiskerRight (pullbackSystemSnd α β) T)
    (c₁ := T.mapCone c₁) (c₂ := T.mapCone c₂) (c₃ := T.mapCone c₃)
    (d := T.mapCone (pullbackSystemCone hg₁ hg₂))
    (z₁ := T.map (pullback.fst g₁ g₂)) (z₂ := T.map (pullback.snd g₁ g₂))
    (g₁ := T.map g₁) (g₂ := T.map g₂)
    (fun j => ?_) hc₁ hc₂ hc₃ ?_ (fun j => ?_) (fun j => ?_) (fun j => ?_) (fun j => ?_)
  · exact (IsPullback.of_hasPullback _ _).map T
  · exact (IsPullback.of_hasPullback _ _).map T
  · exact (T.map_comp _ _).symm.trans
      ((congrArg T.map (pullback.lift_fst _ _ _)).trans (T.map_comp _ _))
  · exact (T.map_comp _ _).symm.trans
      ((congrArg T.map (pullback.lift_snd _ _ _)).trans (T.map_comp _ _))
  · exact (T.map_comp _ _).symm.trans ((congrArg T.map (hg₁ j)).trans (T.map_comp _ _))
  · exact (T.map_comp _ _).symm.trans ((congrArg T.map (hg₂ j)).trans (T.map_comp _ _))

/-! ### Lifting to the big affine fppf category -/

/-- A cone over a functor into the big fppf category over `S` whose cone point is affine, read as
a cone over its lift to the big affine fppf category. -/
@[simps]
def liftCone {G : J ⥤ BigFppfOver B S hS} (hG : ∀ j, IsAffineOver B S hS (G.obj j)) (c : Cone G)
    (hc : IsAffineOver B S hS c.pt) : Cone ((IsAffineOver B S hS).lift G hG) where
  pt := ⟨c.pt, hc⟩
  π :=
    { app j := ObjectProperty.homMk (c.π.app j)
      naturality _ _ _ := ObjectProperty.hom_ext _ (by simp) }

/-- The image in schemes of a lifted cone is a limit cone when the image of the original cone
is. -/
def isLimitLiftCone {G : J ⥤ BigFppfOver B S hS} (hG : ∀ j, IsAffineOver B S hS (G.obj j))
    (c : Cone G) (hc : IsAffineOver B S hS c.pt)
    (h : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) :
    IsLimit ((toScheme B S hS).mapCone (liftCone hG c hc)) :=
  IsLimit.ofIsoLimit h (Cone.ext (Iso.refl _) (fun _ => (Category.id_comp _).symm))

/-! ### Constant systems, restriction to an index, and base change systems -/

section Systems

variable {J : Type v} [Category.{w} J]

/-- The image of the constant cone of an object under a functor is a limit cone, over a connected
index category. -/
noncomputable def isLimitMapConeConstCone {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    [IsConnected J] (G : 𝒞 ⥤ 𝒟) (X : 𝒞) :
    IsLimit (G.mapCone (constCone J X)) where
  lift s := s.π.app (Classical.arbitrary J)
  fac s j := by
    have key : ∀ j₁ j₂ : J, (show s.pt ⟶ G.obj X from s.π.app j₁) = s.π.app j₂ := by
      intro j₁ j₂
      refine constant_of_preserves_morphisms (α := s.pt ⟶ G.obj X)
        (fun j => show s.pt ⟶ G.obj X from s.π.app j) (fun j₁ j₂ t => ?_) _ _
      have := s.w t
      dsimp only [Functor.comp_map, Functor.const_obj_map, Functor.const_obj_obj,
        Functor.comp_obj] at this
      rw [CategoryTheory.Functor.map_id, Category.comp_id] at this
      exact this
    have e : G.map (𝟙 X) = 𝟙 (G.obj X) := G.map_id X
    exact (congrArg (fun k => (show s.pt ⟶ G.obj X from s.π.app (Classical.arbitrary J)) ≫ k)
      e).trans ((Category.comp_id _).trans (key _ _))
  uniq s m hm := by
    have e : G.map (𝟙 X) = 𝟙 (G.obj X) := G.map_id X
    have := hm (Classical.arbitrary J)
    exact (Category.comp_id m).symm.trans
      ((congrArg (fun k => m ≫ k) e).symm.trans this)

end Systems

section Base

variable {I : Type v} [Category.{w} I] (D : I ⥤ BigAffineFppf B S hS) (c : Cone D) (i₀ : I)

/-- The restriction of an inverse system to the indices over `i₀`, in the big fppf category. -/
abbrev overSystem : Over i₀ ⥤ BigFppfOver B S hS := Over.forget i₀ ⋙ D ⋙ inclusion B S hS

/-- The restriction of a cone to the indices over `i₀`, in the big fppf category. -/
abbrev overCone : Cone (overSystem D i₀) := (inclusion B S hS).mapCone (c.whisker (Over.forget i₀))

/-- The restriction of a limit cone to the indices over `i₀` is a limit cone. -/
noncomputable def isLimit_overCone [IsCofiltered I]
    (hc : IsLimit ((toScheme B S hS).mapCone c)) :
    IsLimit ((BigFppfOver.toScheme B S hS).mapCone (overCone D c i₀)) :=
  (Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀) ((toScheme B S hS).mapCone c)).symm hc

/-- The constant system at the stage `i₀`. -/
abbrev stageConst : Over i₀ ⥤ BigFppfOver B S hS :=
  (Functor.const (Over i₀)).obj ((inclusion B S hS).obj (D.obj i₀))

/-- The transition maps to the stage `i₀`. -/
@[simps]
def toStage : overSystem D i₀ ⟶ stageConst D i₀ where
  app j := (inclusion B S hS).map (D.map j.hom)
  naturality j k t := by
    simp only [overSystem, Functor.comp_obj, Over.forget_obj, Functor.comp_map, Over.forget_map,
      Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, ← Functor.map_comp,
      Over.w t]

variable {W₀ : BigFppfOver B S hS} (w : W₀ ⟶ (inclusion B S hS).obj (D.obj i₀))

/-- The base change system `j ↦ W₀ ×_{D i₀} D j` of an object `W₀` over the stage `i₀`. -/
noncomputable abbrev baseChangeSystem : Over i₀ ⥤ BigFppfOver B S hS :=
  pullbackSystem ((Functor.const (Over i₀)).map w) (toStage D i₀)

/-- The cone of the base change system with cone point `W₀ ×_{D i₀} lim D`. -/
noncomputable abbrev baseChangeCone : Cone (baseChangeSystem D i₀ w) :=
  pullbackSystemCone (c₁ := constCone (Over i₀) W₀) (c₂ := overCone D c i₀)
    (c₃ := constCone (Over i₀) ((inclusion B S hS).obj (D.obj i₀))) (g₁ := w)
    (g₂ := (inclusion B S hS).map (c.π.app i₀))
    (fun j => (Category.id_comp w).trans (Category.comp_id w).symm) (fun j => by
      simp only [overCone, Functor.mapCone_π_app, Cone.whisker_π, Functor.whiskerLeft_app,
        Over.forget_obj, toStage_app, constCone_π, NatTrans.id_app, ← Functor.map_comp]
      exact congrArg (inclusion B S hS).map (c.w j.hom))

/-- The projection of the base change system to the restricted system. -/
noncomputable abbrev baseChangeSnd : baseChangeSystem D i₀ w ⟶ overSystem D i₀ :=
  pullbackSystemSnd ((Functor.const (Over i₀)).map w) (toStage D i₀)

/-- The base change cone followed by the projection to the restricted system is the second
projection of `W₀ ×_{D i₀} lim D` followed by the restricted cone. -/
lemma baseChangeCone_π_app_snd (j : Over i₀) :
    (baseChangeCone D c i₀ w).π.app j ≫ (baseChangeSnd D i₀ w).app j =
      pullback.snd w ((inclusion B S hS).map (c.π.app i₀)) ≫ (overCone D c i₀).π.app j :=
  pullback.lift_snd _ _ _

/-- The fibre square of the base change system over the restricted system. -/
noncomputable abbrev baseChangePairSystem : Over i₀ ⥤ BigFppfOver B S hS :=
  pullbackSystem (baseChangeSnd D i₀ w) (baseChangeSnd D i₀ w)

/-- The cone of the fibre square of the base change system. -/
noncomputable abbrev baseChangePairCone : Cone (baseChangePairSystem D i₀ w) :=
  pullbackSystemCone (c₁ := baseChangeCone D c i₀ w) (c₂ := baseChangeCone D c i₀ w)
    (c₃ := overCone D c i₀) (baseChangeCone_π_app_snd D c i₀ w)
    (baseChangeCone_π_app_snd D c i₀ w)

/-- The base change cone is a limit cone. -/
noncomputable def isLimit_baseChangeCone [IsCofiltered I]
    (hc : IsLimit ((toScheme B S hS).mapCone c)) :
    IsLimit ((BigFppfOver.toScheme B S hS).mapCone (baseChangeCone D c i₀ w)) :=
  haveI : IsConnected (Over i₀) := IsCofiltered.isConnected _
  isLimit_pullbackSystemCone _ _ (isLimitMapConeConstCone _ _) (isLimit_overCone D c i₀ hc)
    (isLimitMapConeConstCone _ _)

end Base

end AlgebraicGeometry.BigAffineFppf

end
