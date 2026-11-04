module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeTransitivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.ObstructionClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.ObstructionRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageFixedBaseCocycle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.PullbackSheafSystemPresentation
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Basic

/-!
# The obstruction class of [Stacks, Tag 0F07] along a directed limit

Let `fV : X_V ⟶ V` be a morphism of schemes, `g₀ : T₀ ⟶ V` a base for a sheaf `F₀` with
`Y₀ = X_V ×_V T₀`, and `ξ` a class in the stalk at a geometric point `x` of `X_V` of
`R^r h₀_* e₀⁻¹ F₀`. Let `W = lim W_i` be the limit of a directed inverse system of schemes over
`T₀` with affine transition morphisms. Hypothesis (2) of the dévissage
`AlgebraicGeometry.exists_field_point` of [Stacks, Tag 0F06] for the property `P` of the proof of
[Stacks, Tag 0F07] (`Stacks.EtaleCohomology.ObstructionSurvives`) asks that `P(W_i)` for all `i`
imply `P(W)`. The source proves it by [Stacks, Tag 09Z1]: over the fixed base `V`,
`R^r (W ⟶ V)_* F|_W = colim_i R^r (W_i ⟶ V)_* F|_{W_i}`, and over the fixed base `X_V`, the same
holds for the system of fibre products `X_V ×_V W_i`, whose limit is `X_V ×_V W`; inverse images
and stalks commute with these colimits. This file carries out that argument.

Over `W` and over each `W_i` the cartesian square is a fibre product, and these form an inverse
system with limit `X_V ×_V W` (`Stacks.EtaleCohomology.fibreProductConeIsLimit`). Since `P(W)` can
be tested on any cartesian square (`Stacks.EtaleCohomology.obstructionSurvives_iff_of_isPullback`),
it can be tested on these. The transfer maps of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeTransitivity` are, read
through the comparisons `e⁻¹ π⁻¹ ≅ (e ≫ π)⁻¹`, the maps of [Stacks, Tag 09Z1] for the system of
inverse images of `F₀` (`Stacks.EtaleCohomology.targetTransfer_comp_map`), and every class of the
source over `W` comes from a stage (`Stacks.EtaleCohomology.exists_stalk_sourceTransfer_eq`).

## Main definitions

* `Stacks.EtaleCohomology.FixedBaseHigherDirectImage.mapAlong` — the map
  `R^p g_* M ⟶ R^p g'_* N` along a morphism over the base, of which the maps of
  [Stacks, Tag 09Z1] are instances.
* `Stacks.EtaleCohomology.fibreProductSystem` — the inverse system `X ×_V W_i` of fibre
  products of a fixed scheme `X` over `V` with an inverse system of schemes over `V`.
* `Stacks.EtaleCohomology.fibreProductCone` — the cone `X ×_V W` over it.

## Main results

* `Stacks.EtaleCohomology.fibreProductConeIsLimit` — over a directed set, `X ×_V lim W_i` is the
  limit of the `X ×_V W_i`.
* `Stacks.EtaleCohomology.obstructionSurvives_iff_of_isPullback` — `P(W)` can be tested on any
  cartesian square over `W`.
* `Stacks.EtaleCohomology.targetTransfer_comp_map` — the transfer maps of the target are maps of
  [Stacks, Tag 09Z1].
* `Stacks.EtaleCohomology.exists_stalk_sourceTransfer_eq` — every class of the source over the
  limit comes from a stage.
* `Stacks.EtaleCohomology.FixedBaseHigherDirectImage.exists_stalk_transitionMap_eq_zero` — at a
  stalk, a class at a stage of [Stacks, Tag 09Z1] dying in the colimit dies at a later stage.
* `Stacks.EtaleCohomology.stalk_transitionMap_ofCocone`,
  `Stacks.EtaleCohomology.targetTransfer_comp_eq_mapAlong` — the transfer maps of the target are
  the transition and cocone maps of [Stacks, Tag 09Z1] for the system `(e_i ≫ π_i)⁻¹ F₀`.
* `Stacks.EtaleCohomology.stalk_higherBaseChangeMapAb_eq_iff_targetTransfer` — the obstruction
  condition transported along a transfer, on elements.
* `Stacks.EtaleCohomology.exists_stalk_targetTransfer_eq_zero` — a class over a stage of the
  target dying over the limit dies at a later stage.
* `Stacks.EtaleCohomology.obstructionSurvives_of_isLimit_of_isPullback`,
  `Stacks.EtaleCohomology.obstructionSurvives_of_isLimit` — hypothesis (2) of the dévissage of
  [Stacks, Tag 0F06] for the property `P` of the proof of [Stacks, Tag 0F07].

## References

* [Stacks Project, Tag 0F07](https://stacks.math.columbia.edu/tag/0F07)
* [Stacks Project, Tag 0F06](https://stacks.math.columbia.edu/tag/0F06)
* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### The inverse system of fibre products -/

section FibreProduct

variable {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} {V X : Scheme.{u}} (f : X ⟶ V)
  (g : ∀ i, D.obj i ⟶ V) (hg : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), D.map a ≫ g j = g i)

/-- **The inverse system of fibre products** `X ×_V W_i` of a fixed scheme `X` over `V` with an
inverse system `W_i` of schemes over `V`. -/
abbrev fibreProductSystem : Iᵒᵖ ⥤ Scheme.{u} where
  obj i := pullback f (g i)
  map {i j} a := pullback.lift (pullback.fst f (g i)) (pullback.snd f (g i) ≫ D.map a)
    (by rw [pullback.condition, Category.assoc, hg a])
  map_id i := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.id_comp]
    · rw [pullback.lift_snd, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  map_comp a b := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        Functor.map_comp, Category.assoc]

/-- A transition morphism of the system of fibre products commutes with the first projections to
`X`. -/
@[simp]
theorem fibreProductSystem_map_fst {i j : Iᵒᵖ} (a : i ⟶ j) :
    (fibreProductSystem f g hg).map a ≫ pullback.fst f (g j) = pullback.fst f (g i) :=
  pullback.lift_fst _ _ _

/-- A transition morphism of the system of fibre products covers the transition morphism of the
system of bases. -/
@[simp]
theorem fibreProductSystem_map_snd {i j : Iᵒᵖ} (a : i ⟶ j) :
    (fibreProductSystem f g hg).map a ≫ pullback.snd f (g j) = pullback.snd f (g i) ≫ D.map a :=
  pullback.lift_snd _ _ _

/-- A transition morphism of the system of fibre products is the base change of the transition
morphism of the system of bases. -/
theorem isPullback_fibreProductSystem_map {i j : Iᵒᵖ} (a : i ⟶ j) :
    IsPullback ((fibreProductSystem f g hg).map a) (pullback.snd f (g i)) (pullback.snd f (g j))
      (D.map a) := by
  refine IsPullback.of_right ?_ (fibreProductSystem_map_snd f g hg a) (.of_hasPullback f (g j))
  rw [fibreProductSystem_map_fst, hg a]
  exact .of_hasPullback f (g i)

/-- If the transition morphisms of the system of bases are affine, so are those of the system of
fibre products. -/
instance [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] {i j : Iᵒᵖ} (a : i ⟶ j) :
    IsAffineHom ((fibreProductSystem f g hg).map a) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
    (isPullback_fibreProductSystem_map f g hg a).flip inferInstance

variable (c : Cone D) (gc : c.pt ⟶ V) (hgc : ∀ i, c.π.app i ≫ g i = gc)

/-- **The cone `X ×_V W` over the system of fibre products**, for a cone `W` over the system of
bases with structure morphism `gc = π_i ≫ g_i`. -/
abbrev fibreProductCone : Cone (fibreProductSystem f g hg) where
  pt := pullback f gc
  π :=
    { app i := pullback.lift (pullback.fst f gc) (pullback.snd f gc ≫ c.π.app i)
        (by rw [pullback.condition, Category.assoc, hgc i])
      naturality i j a := by
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
        apply pullback.hom_ext
        · simp only [Category.id_comp, Category.assoc, pullback.lift_fst]
        · simp only [Category.id_comp, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
            c.w a] }

/-- A leg of the cone of fibre products commutes with the first projections to `X`. -/
@[simp]
theorem fibreProductCone_π_app_fst (i : Iᵒᵖ) :
    (fibreProductCone f g hg c gc hgc).π.app i ≫ pullback.fst f (g i) = pullback.fst f gc :=
  pullback.lift_fst _ _ _

/-- A leg of the cone of fibre products covers the corresponding leg of the cone `W`. -/
@[simp]
theorem fibreProductCone_π_app_snd (i : Iᵒᵖ) :
    (fibreProductCone f g hg c gc hgc).π.app i ≫ pullback.snd f (g i) =
      pullback.snd f gc ≫ c.π.app i :=
  pullback.lift_snd _ _ _

/-- The first projections of a cone over the system of fibre products agree, the index being
directed. -/
theorem fibreProductCone_fst_eq [IsDirected I (· ≤ ·)] (s : Cone (fibreProductSystem f g hg))
    (i j : Iᵒᵖ) : s.π.app i ≫ pullback.fst f (g i) = s.π.app j ≫ pullback.fst f (g j) := by
  obtain ⟨i⟩ := i
  obtain ⟨j⟩ := j
  obtain ⟨k, hi, hj⟩ := directed_of (· ≤ ·) i j
  rw [← s.w (homOfLE hi).op, ← s.w (homOfLE hj).op, Category.assoc, Category.assoc,
    fibreProductSystem_map_fst, fibreProductSystem_map_fst]

/-- The cone over the system of bases attached to a cone over the system of fibre products: its
legs are the second projections. -/
abbrev fibreProductBaseCone (s : Cone (fibreProductSystem f g hg)) : Cone D where
  pt := s.pt
  π :=
    { app i := s.π.app i ≫ pullback.snd f (g i)
      naturality i j a := by
        have := s.w a
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
          Category.assoc] at this ⊢
        rw [← fibreProductSystem_map_snd f g hg a, ← Category.assoc, this] }

/-- **The fibre product with a limit is the limit of the fibre products**: over a directed set,
`X ×_V lim W_i = lim (X ×_V W_i)`. -/
def fibreProductConeIsLimit [IsDirected I (· ≤ ·)] [Nonempty I] (hc : IsLimit c) :
    IsLimit (fibreProductCone f g hg c gc hgc) where
  lift s := pullback.lift (s.π.app (op (Classical.arbitrary I)) ≫ pullback.fst f _)
    (hc.lift (fibreProductBaseCone f g hg s)) (by
      have h := hc.fac (fibreProductBaseCone f g hg s) (op (Classical.arbitrary I))
      rw [← hgc (op (Classical.arbitrary I)), ← Category.assoc, h, Category.assoc,
        Category.assoc, pullback.condition])
  fac s i := by
    apply pullback.hom_ext
    · rw [Category.assoc, fibreProductCone_π_app_fst, pullback.lift_fst]
      exact fibreProductCone_fst_eq f g hg s _ _
    · rw [Category.assoc, fibreProductCone_π_app_snd, pullback.lift_snd_assoc, hc.fac]
  uniq s m hm := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, ← hm (op (Classical.arbitrary I)), Category.assoc,
        fibreProductCone_π_app_fst]
    · rw [pullback.lift_snd]
      refine hc.hom_ext fun j => ?_
      rw [hc.fac, Category.assoc, ← fibreProductCone_π_app_snd f g hg c gc hgc j,
        ← Category.assoc, hm]

/-- The first projection `X ×_V W_i ⟶ X` of a member of the system of fibre products. -/
def fibreProductFst (i : Iᵒᵖ) : (fibreProductSystem f g hg).obj i ⟶ X := pullback.fst f (g i)

/-- The second projection `X ×_V W_i ⟶ W_i` of a member of the system of fibre products. -/
def fibreProductSnd (i : Iᵒᵖ) : (fibreProductSystem f g hg).obj i ⟶ D.obj i :=
  pullback.snd f (g i)

/-- The square formed by `X ×_V W_i`, `X`, `W_i` and `V` is cartesian. -/
theorem isPullback_fibreProduct (i : Iᵒᵖ) :
    IsPullback (fibreProductFst f g hg i) (fibreProductSnd f g hg i) f (g i) :=
  IsPullback.of_hasPullback f (g i)

/-- A transition morphism of the system of fibre products commutes with `fibreProductFst`. -/
@[reassoc (attr := simp)]
theorem fibreProductSystem_map_fibreProductFst {i j : Iᵒᵖ} (a : i ⟶ j) :
    (fibreProductSystem f g hg).map a ≫ fibreProductFst f g hg j = fibreProductFst f g hg i :=
  fibreProductSystem_map_fst f g hg a

/-- A transition morphism of the system of fibre products covers, through `fibreProductSnd`, the
transition morphism of the system of bases. -/
@[reassoc (attr := simp)]
theorem fibreProductSystem_map_fibreProductSnd {i j : Iᵒᵖ} (a : i ⟶ j) :
    (fibreProductSystem f g hg).map a ≫ fibreProductSnd f g hg j =
      fibreProductSnd f g hg i ≫ D.map a :=
  fibreProductSystem_map_snd f g hg a

/-- The first projection `X ×_V W ⟶ X` of the apex of the cone of fibre products. -/
def fibreProductConeFst : (fibreProductCone f g hg c gc hgc).pt ⟶ X := pullback.fst f gc

/-- The second projection `X ×_V W ⟶ W` of the apex of the cone of fibre products. -/
def fibreProductConeSnd : (fibreProductCone f g hg c gc hgc).pt ⟶ c.pt := pullback.snd f gc

/-- The square formed by `X ×_V W`, `X`, `W` and `V` is cartesian. -/
theorem isPullback_fibreProductCone :
    IsPullback (fibreProductConeFst f g hg c gc hgc) (fibreProductConeSnd f g hg c gc hgc) f gc :=
  IsPullback.of_hasPullback f gc

/-- A leg of the cone of fibre products commutes with the first projections `fibreProductFst` and
`fibreProductConeFst`. -/
@[reassoc (attr := simp)]
theorem fibreProductCone_π_app_fibreProductFst (i : Iᵒᵖ) :
    (fibreProductCone f g hg c gc hgc).π.app i ≫ fibreProductFst f g hg i =
      fibreProductConeFst f g hg c gc hgc :=
  fibreProductCone_π_app_fst f g hg c gc hgc i

/-- A leg of the cone of fibre products covers, through the second projections `fibreProductSnd`
and `fibreProductConeSnd`, the corresponding leg of the cone `W`. -/
@[reassoc (attr := simp)]
theorem fibreProductCone_π_app_fibreProductSnd (i : Iᵒᵖ) :
    (fibreProductCone f g hg c gc hgc).π.app i ≫ fibreProductSnd f g hg i =
      fibreProductConeSnd f g hg c gc hgc ≫ c.π.app i :=
  fibreProductCone_π_app_snd f g hg c gc hgc i

end FibreProduct

/-! ### The transfer maps and the maps of Stacks 09Z1 -/

section Transfer

attribute [local instance] HasDerivedCategory.standard

variable {T₀ W₁ W₂ Y₁ Y₂ : Scheme.{u}} (F₀ : Sheaf (smallEtaleTopology T₀) Ab.{u + 1})
  (e₁ : Y₁ ⟶ W₁) (π₁ : W₁ ⟶ T₀) (e₂ : Y₂ ⟶ W₂) (π₂ : W₂ ⟶ T₀) (φ : W₁ ⟶ W₂)
  (hπ : π₁ = φ ≫ π₂) (yφ : Y₁ ⟶ Y₂) (hφe : yφ ≫ e₂ = e₁ ≫ φ) (ι₁ : Y₁ ⟶ T₀)
  (hι₁ : ι₁ = e₁ ≫ π₁) (ι₂ : Y₂ ⟶ T₀) (hι₂ : ι₂ = e₂ ≫ π₂) (hι : ι₁ = yφ ≫ ι₂)

/-- **The sheaf part of the transfer map of the target is a comparison of inverse images**: the
identification `yφ⁻¹ e₂⁻¹ π₂⁻¹ ≅ e₁⁻¹ π₁⁻¹` entering the transfer map of the target, read through
the identifications `e_k⁻¹ π_k⁻¹ ≅ ι_k⁻¹` with `ι_k = e_k ≫ π_k`, is the comparison
`yφ⁻¹ ι₂⁻¹ ≅ ι₁⁻¹`. Two instances of the associativity of the comparisons of inverse images. -/
theorem pullbackComp_transfer_coherence :
    (smallEtalePullbackAb yφ).map ((smallEtalePullbackAbComp' e₂ π₂ ι₂ hι₂).hom.app F₀) ≫
        (smallEtalePullbackAbComp' yφ ι₂ ι₁ hι).hom.app F₀ =
      ((smallEtalePullbackAbComp' yφ e₂ (e₁ ≫ φ) hφe.symm).hom.app
            ((smallEtalePullbackAb π₂).obj F₀) ≫
          (smallEtalePullbackAbComp' e₁ φ (e₁ ≫ φ) rfl).inv.app
            ((smallEtalePullbackAb π₂).obj F₀) ≫
          (smallEtalePullbackAb e₁).map ((smallEtalePullbackAbComp' φ π₂ π₁ hπ).hom.app F₀)) ≫
        (smallEtalePullbackAbComp' e₁ π₁ ι₁ hι₁).hom.app F₀ := by
  have h₁ : ι₁ = (e₁ ≫ φ) ≫ π₂ := by rw [hι₁, hπ, Category.assoc]
  have P1 := smallEtalePullbackAbComp'_assoc_app yφ e₂ π₂ (e₁ ≫ φ) hφe.symm ι₂ hι₂ ι₁ h₁ hι F₀
  have P2 := smallEtalePullbackAbComp'_assoc_app e₁ φ π₂ (e₁ ≫ φ) rfl π₁ hπ ι₁ h₁ hι₁ F₀
  rw [← P1, Category.assoc, Category.assoc, ← P2, Iso.inv_hom_id_app_assoc]

/-- **The transfer map of the target is a map of Stacks 09Z1.** For `h₁ ≫ 𝟙 = yφ ≫ h₂`, the
transfer map `R^r h₂_* e₂⁻¹ π₂⁻¹ F₀ ⟶ R^r h₁_* e₁⁻¹ π₁⁻¹ F₀` of
`Stacks.EtaleCohomology.obstructionPullbackMap_eq_comp` is, through the identifications
`e_k⁻¹ π_k⁻¹ ≅ ι_k⁻¹`, the base change map of the square followed by the comparison
`yφ⁻¹ ι₂⁻¹ ≅ ι₁⁻¹`: the shape of the maps of Stacks 09Z1 for the system of inverse images of
`F₀` along the `ι_k`. -/
theorem targetTransfer_comp_map {X : Scheme.{u}} (r : ℕ) (h₁ : Y₁ ⟶ X) (h₂ : Y₂ ⟶ X)
    (hφh : h₁ ≫ 𝟙 X = yφ ≫ h₂) :
    ((smallEtalePullbackAbIdOf (𝟙 X) rfl).inv.app (((smallEtalePushforwardAb h₂).rightDerived r).obj
          ((smallEtalePullbackAb e₂).obj ((smallEtalePullbackAb π₂).obj F₀))) ≫
        (higherBaseChangeMapAb (𝟙 X) h₂ h₁ yφ hφh r).app
          ((smallEtalePullbackAb e₂).obj ((smallEtalePullbackAb π₂).obj F₀)) ≫
        ((smallEtalePushforwardAb h₁).rightDerived r).map
          ((smallEtalePullbackAbComp' yφ e₂ (e₁ ≫ φ) hφe.symm).hom.app
              ((smallEtalePullbackAb π₂).obj F₀) ≫
            (smallEtalePullbackAbComp' e₁ φ (e₁ ≫ φ) rfl).inv.app
              ((smallEtalePullbackAb π₂).obj F₀) ≫
            (smallEtalePullbackAb e₁).map ((smallEtalePullbackAbComp' φ π₂ π₁ hπ).hom.app F₀))) ≫
      ((smallEtalePushforwardAb h₁).rightDerived r).map
        ((smallEtalePullbackAbComp' e₁ π₁ ι₁ hι₁).hom.app F₀) =
    ((smallEtalePushforwardAb h₂).rightDerived r).map
        ((smallEtalePullbackAbComp' e₂ π₂ ι₂ hι₂).hom.app F₀) ≫
      (smallEtalePullbackAbIdOf (𝟙 X) rfl).inv.app
          (((smallEtalePushforwardAb h₂).rightDerived r).obj
            ((smallEtalePullbackAb ι₂).obj F₀)) ≫
        (higherBaseChangeMapAb (𝟙 X) h₂ h₁ yφ hφh r).app ((smallEtalePullbackAb ι₂).obj F₀) ≫
          ((smallEtalePushforwardAb h₁).rightDerived r).map
            ((smallEtalePullbackAbComp' yφ ι₂ ι₁ hι).hom.app F₀) := by
  have hid := (smallEtalePullbackAbIdOf (𝟙 X) rfl).inv.naturality
    (((smallEtalePushforwardAb h₂).rightDerived r).map
      ((smallEtalePullbackAbComp' e₂ π₂ ι₂ hι₂).hom.app F₀))
  have hnat := (higherBaseChangeMapAb (𝟙 X) h₂ h₁ yφ hφh r).naturality
    ((smallEtalePullbackAbComp' e₂ π₂ ι₂ hι₂).hom.app F₀)
  dsimp only [Functor.comp_map, Functor.id_map] at hid hnat
  simp only [Category.assoc]
  rw [reassoc_of% hid, reassoc_of% hnat, ← Functor.map_comp, ← Functor.map_comp,
    pullbackComp_transfer_coherence F₀ e₁ π₁ e₂ π₂ φ hπ yφ hφe ι₁ hι₁ ι₂ hι₂ hι]

end Transfer

/-! ### The obstruction condition on the chosen fibre product -/

section Chosen

attribute [local instance] HasDerivedCategory.standard

variable {V X_V T₀ Y₀ : Scheme.{u}} {fV : X_V ⟶ V} {g₀ : T₀ ⟶ V} {h₀ : Y₀ ⟶ X_V}
  {e₀ : Y₀ ⟶ T₀} (sq₀ : IsPullback h₀ e₀ fV g₀) {W Y : Scheme.{u}} (π : W ⟶ T₀)
  {h : Y ⟶ X_V} {e : Y ⟶ W} (sq : IsPullback h e fV (π ≫ g₀))

/-- The morphism from a cartesian square `Y = X_V ×_V W` over `π : W ⟶ T₀` to
`Y₀ = X_V ×_V T₀`. -/
def obstructionLift : Y ⟶ Y₀ :=
  sq₀.lift h (e ≫ π) (by rw [sq.w, Category.assoc])

/-- `obstructionLift` lies over `π : W ⟶ T₀`. -/
theorem obstructionLift_snd : obstructionLift sq₀ π sq ≫ e₀ = e ≫ π :=
  sq₀.lift_snd _ _ _

/-- `obstructionLift` lies over `X_V`. -/
theorem obstructionLift_fst : h ≫ 𝟙 X_V = obstructionLift sq₀ π sq ≫ h₀ := by
  rw [Category.comp_id, obstructionLift, sq₀.lift_fst]

/-- `obstructionLift` factors as a morphism `a` of cartesian squares followed by any lift `y'`. -/
private theorem obstructionLift_eq_comp {Y' W' : Scheme.{u}} {h' : Y' ⟶ X_V} {e' : Y' ⟶ W'}
    (π' : W' ⟶ T₀) (a : Y ⟶ Y') (y' : Y' ⟶ Y₀) (ha : h ≫ 𝟙 X_V = a ≫ h')
    (hy'h : h' ≫ 𝟙 X_V = y' ≫ h₀) (hae : a ≫ e' ≫ π' = e ≫ π) (hy' : y' ≫ e₀ = e' ≫ π') :
    obstructionLift sq₀ π sq = a ≫ y' :=
  sq₀.hom_ext
    (by rw [obstructionLift, sq₀.lift_fst, Category.assoc, ← hy'h, Category.comp_id, ← ha,
      Category.comp_id])
    (by rw [obstructionLift_snd, Category.assoc, hy', hae])

variable (F₀ : Sheaf (smallEtaleTopology T₀) Ab.{u + 1}) (r : ℕ) (x : GeometricPoint X_V)
  (ξ : obstructionStalk h₀ e₀ F₀ r x)

/-- **The property `P(W)` of [Stacks, Tag 0F07] can be tested on any cartesian square**
`Y = X_V ×_V W`, any two such squares being isomorphic over `X_V` and `Y₀`. -/
theorem obstructionSurvives_iff_of_isPullback :
    ObstructionSurvives fV g₀ h₀ e₀ F₀ r x ξ W π ↔
      ∀ η, (smallEtaleStalkAb x.hom).map
          ((higherBaseChangeMapAb fV (π ≫ g₀) h e sq.w r).app
              ((smallEtalePullbackAb π).obj F₀)) η ≠
        (smallEtaleStalkAb x.hom).map
          ((higherBaseChangeMapAb (𝟙 X_V) h₀ h (obstructionLift sq₀ π sq)
              (obstructionLift_fst sq₀ π sq) r).app ((smallEtalePullbackAb e₀).obj F₀) ≫
            ((smallEtalePushforwardAb h).rightDerived r).map
              ((smallEtalePullbackAbComp' (obstructionLift sq₀ π sq) e₀
                  (obstructionLift sq₀ π sq ≫ e₀) rfl).hom.app F₀ ≫
                (smallEtalePullbackAbComp' e π (obstructionLift sq₀ π sq ≫ e₀)
                  (obstructionLift_snd sq₀ π sq)).inv.app F₀)) ξ := by
  refine ⟨?_, fun H => ⟨_, _, _, π ≫ g₀, rfl, sq, _, obstructionLift_snd sq₀ π sq,
    obstructionLift_fst sq₀ π sq, H⟩⟩
  rintro ⟨Y', h', e', g', rfl, sq', y', hy', hyh', hne⟩
  let ψ := sq.isoIsPullback _ _ sq'
  have hψh : h ≫ 𝟙 X_V = ψ.hom ≫ h' := by
    rw [Category.comp_id, IsPullback.isoIsPullback_hom_fst]
  have hψe : ψ.hom ≫ e' = e ≫ 𝟙 W := by
    rw [Category.comp_id, IsPullback.isoIsPullback_hom_snd]
  have hy : obstructionLift sq₀ π sq = ψ.hom ≫ y' :=
    obstructionLift_eq_comp sq₀ π sq π ψ.hom y' hψh hyh'
      (by rw [← Category.assoc, hψe, Category.comp_id]) hy'
  have : UniversalHomeomorphism ψ.hom := universalHomeomorphism_of_isIso _
  have : UniversalHomeomorphism (𝟙 W) := universalHomeomorphism_of_isIso _
  exact (forall_stalk_ne_iff_of_universalHomeomorphism h e π (π ≫ g₀) h' e' π (π ≫ g₀) (𝟙 W)
    (Category.id_comp π).symm ψ.hom hψh hψe (obstructionLift sq₀ π sq) y'
    (obstructionLift_snd sq₀ π sq) hy' (obstructionLift_fst sq₀ π sq) hyh' hy sq.w sq'.w
    (by rw [Category.comp_id, Category.id_comp]) x ξ).2 hne

end Chosen

/-- The leg of the colimit presentation of `Stacks.EtaleCohomology.EtaleSheafSystem.ofCoconeLeg`,
with the source of the cone leg written as the apex of the cone. -/
theorem ofCoconeLeg_eq {S : Scheme.{u}} {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
    (ι : ∀ i, D.obj i ⟶ S) (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), D.map a ≫ ι j = ι i)
    (c : Cone D) (g : c.pt ⟶ S) (hg : ∀ i, c.π.app i ≫ ι i = g)
    (G : Sheaf (smallEtaleTopology S) Ab.{u + 1}) (i : Iᵒᵖ) :
    EtaleSheafSystem.ofCoconeLeg ι hι c g hg G i =
      (smallEtalePullbackAbComp' (X := c.pt) (c.π.app i) (ι i) g (hg i).symm).hom.app G := rfl

/-- The transition maps of `Stacks.EtaleCohomology.EtaleSheafSystem.ofCocone`. -/
theorem ofCocone_map_eq {S : Scheme.{u}} {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
    (ι : ∀ i, D.obj i ⟶ S) (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), D.map a ≫ ι j = ι i)
    (G : Sheaf (smallEtaleTopology S) Ab.{u + 1}) {i j : Iᵒᵖ} (a : i ⟶ j) :
    (EtaleSheafSystem.ofCocone ι hι G).map a =
      (smallEtalePullbackAbComp' (D.map a) (ι j) (ι i) (hι a).symm).hom.app G := rfl

/-- The cocone maps of Stacks 09Z1 for the system of inverse images of a sheaf. -/
theorem projectionMap_ofCocone {S X : Scheme.{u}} {I : Type u} [Preorder I]
    {D : Iᵒᵖ ⥤ Scheme.{u}} (hX : ∀ i, D.obj i ⟶ X) (r : ℕ) (c : Cone D) (hXc : c.pt ⟶ X)
    (ι : ∀ i, D.obj i ⟶ S) (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), D.map a ≫ ι j = ι i)
    (g : c.pt ⟶ S) (hg : ∀ i, c.π.app i ≫ ι i = g)
    (G : Sheaf (smallEtaleTopology S) Ab.{u + 1}) (i : Iᵒᵖ) (w : hXc = c.π.app i ≫ hX i) :
    FixedBaseHigherDirectImage.projectionMap hX r c hXc ((smallEtalePullbackAb g).obj G)
        (EtaleSheafSystem.ofCocone ι hι G) (EtaleSheafSystem.ofCoconeLeg ι hι c g hg G) i w =
      (smallEtalePullbackAbIdOf (𝟙 X) rfl).inv.app
          (((smallEtalePushforwardAb (hX i)).rightDerived r).obj
            ((smallEtalePullbackAb (ι i)).obj G)) ≫
        (higherBaseChangeMapAb (𝟙 X) (hX i) hXc (c.π.app i) (by rw [Category.comp_id, w]) r).app
          ((smallEtalePullbackAb (ι i)).obj G) ≫
        ((smallEtalePushforwardAb hXc).rightDerived r).map
          ((smallEtalePullbackAbComp' (X := c.pt) (c.π.app i) (ι i) g (hg i).symm).hom.app G) := by
  rw [FixedBaseHigherDirectImage.projectionMap, ofCoconeLeg_eq]
  rfl

/-- The transition maps of Stacks 09Z1 for the system of inverse images of a sheaf. -/
theorem transitionMap_ofCocone {S X : Scheme.{u}} {I : Type u} [Preorder I]
    {D : Iᵒᵖ ⥤ Scheme.{u}} (hX : ∀ i, D.obj i ⟶ X) (r : ℕ)
    (ι : ∀ i, D.obj i ⟶ S) (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), D.map a ≫ ι j = ι i)
    (G : Sheaf (smallEtaleTopology S) Ab.{u + 1}) {i j : Iᵒᵖ} (a : i ⟶ j)
    (w : hX i = D.map a ≫ hX j) :
    FixedBaseHigherDirectImage.transitionMap hX r (EtaleSheafSystem.ofCocone ι hι G) a w =
      (smallEtalePullbackAbIdOf (𝟙 X) rfl).inv.app
          (((smallEtalePushforwardAb (hX j)).rightDerived r).obj
            ((smallEtalePullbackAb (ι j)).obj G)) ≫
        (higherBaseChangeMapAb (𝟙 X) (hX j) (hX i) (D.map a) (by rw [Category.comp_id, w]) r).app
          ((smallEtalePullbackAb (ι j)).obj G) ≫
        ((smallEtalePushforwardAb (hX i)).rightDerived r).map
          ((smallEtalePullbackAbComp' (D.map a) (ι j) (ι i) (hι a).symm).hom.app G) := by
  rw [FixedBaseHigherDirectImage.transitionMap, ofCocone_map_eq]
  rfl

/-! ### The limit argument -/

section Limit

attribute [local instance] HasDerivedCategory.standard

variable {V X_V T₀ : Scheme.{u}} (fV : X_V ⟶ V) (g₀ : T₀ ⟶ V)
  (F₀ : Sheaf (smallEtaleTopology T₀) Ab.{u + 1}) (r : ℕ) (x : GeometricPoint X_V)
  {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] {c : Cone D} (hc : IsLimit c)
  (π : c.pt ⟶ T₀) (πi : ∀ i, D.obj i ⟶ T₀)
  (hπi : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), D.map a ≫ πi j = πi i) (hπ : ∀ i, c.π.app i ≫ πi i = π)
  [∀ i, QuasiCompact (πi i ≫ g₀)] [∀ i, QuasiSeparated (πi i ≫ g₀)]

omit [IsDirected I (· ≤ ·)] [Nonempty I] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
  [∀ i, QuasiCompact (πi i ≫ g₀)] [∀ i, QuasiSeparated (πi i ≫ g₀)] in
include hπi in
/-- The structure morphisms `π_i ≫ g₀ : W_i ⟶ V` are compatible with the transition morphisms. -/
theorem stage_comp_eq {i j : Iᵒᵖ} (a : i ⟶ j) : D.map a ≫ πi j ≫ g₀ = πi i ≫ g₀ := by
  rw [← Category.assoc, hπi a]

omit [IsDirected I (· ≤ ·)] [Nonempty I] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
  [∀ i, QuasiCompact (πi i ≫ g₀)] [∀ i, QuasiSeparated (πi i ≫ g₀)] in
include hπ in
/-- The structure morphisms `π_i ≫ g₀ : W_i ⟶ V` are compatible with the cone legs. -/
theorem cone_comp_stage_eq (i : Iᵒᵖ) : c.π.app i ≫ πi i ≫ g₀ = π ≫ g₀ := by
  rw [← Category.assoc, hπ i]

include hc hπi hπ in
/-- **Every class over the limit comes from a stage.** By [Stacks, Tag 09Z1] over the fixed
base `V`, every element of the stalk at `x` of `fV⁻¹ R^r (π ≫ g₀)_* π⁻¹ F₀` is the image of an
element of the stalk of `fV⁻¹ R^r (π_i ≫ g₀)_* π_i⁻¹ F₀` under the transfer map of the source
of `Stacks.EtaleCohomology.obstructionSourceTransferMap_comp_higherBaseChangeMapAb`. -/
theorem exists_stalk_sourceTransfer_eq
    (η : (smallEtaleStalkAb x.hom).obj ((smallEtalePullbackAb fV).obj
      (((smallEtalePushforwardAb (π ≫ g₀)).rightDerived r).obj
        ((smallEtalePullbackAb π).obj F₀)))) :
    ∃ (i : Iᵒᵖ) (ζ : (smallEtaleStalkAb x.hom).obj ((smallEtalePullbackAb fV).obj
      (((smallEtalePushforwardAb (πi i ≫ g₀)).rightDerived r).obj
        ((smallEtalePullbackAb (πi i)).obj F₀)))),
      (smallEtaleStalkAb x.hom).map
        ((smallEtalePullbackAbComp' fV (𝟙 V) fV (Category.comp_id fV).symm).inv.app
            (((smallEtalePushforwardAb (πi i ≫ g₀)).rightDerived r).obj
              ((smallEtalePullbackAb (πi i)).obj F₀)) ≫
          (smallEtalePullbackAb fV).map
            ((higherBaseChangeMapAb (𝟙 V) (πi i ≫ g₀) (π ≫ g₀) (c.π.app i)
                (by rw [Category.comp_id, cone_comp_stage_eq g₀ π πi hπ i]) r).app
                ((smallEtalePullbackAb (πi i)).obj F₀) ≫
              ((smallEtalePushforwardAb (π ≫ g₀)).rightDerived r).map
                ((smallEtalePullbackAbComp' (X := c.pt) (c.π.app i) (πi i) π
                  (hπ i).symm).hom.app F₀)))
        ζ = η := by
  have hg : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), πi i ≫ g₀ = D.map a ≫ πi j ≫ g₀ :=
    fun a => (stage_comp_eq g₀ πi hπi a).symm
  have hw : ∀ i, π ≫ g₀ = c.π.app i ≫ πi i ≫ g₀ := fun i => (cone_comp_stage_eq g₀ π πi hπ i).symm
  have hι : LimitHigherDirectImage.IsPullbackCocone c (EtaleSheafSystem.ofCocone πi hπi F₀)
      (EtaleSheafSystem.ofCoconeLeg πi hπi c π hπ F₀) :=
    EtaleSheafSystem.isPullbackCocone_ofCocone πi hπi c π hπ F₀
  have H := (FixedBaseHigherDirectImage.isSystemColimit (fun i => πi i ≫ g₀) hg hc (π ≫ g₀) hw r
    (EtaleSheafSystem.ofCocone πi hπi F₀) ((smallEtalePullbackAb π).obj F₀)
    (EtaleSheafSystem.ofCoconeLeg πi hπi c π hπ F₀) hι
    (EtaleSheafSystem.isPullbackColimitPresentation_ofCocone πi hπi c π hπ F₀)).map_of_isLeftAdjoint
      ((smallEtaleAdjunctionAb fV).comp
        ((Scheme.pointSmallEtale x.hom).skyscraperSheafAdjunction (A := Ab.{u + 1})))
  obtain ⟨i, ζ, hζ⟩ := H.exists_eq
    (fun a b => by
      rw [FixedBaseHigherDirectImage.transitionMap_comp r (fun i => πi i ≫ g₀) hg,
        Functor.map_comp])
    (fun a => by
      rw [← Functor.map_comp, FixedBaseHigherDirectImage.projectionMap_cocone r
        (fun i => πi i ≫ g₀) hg c (π ≫ g₀) hw _ _ _ hι a]) η
  have he : ∀ y, (smallEtaleStalkAb x.hom).map
      ((smallEtalePullbackAbComp' fV (𝟙 V) fV (Category.comp_id fV).symm).inv.app
        (((smallEtalePushforwardAb (πi i ≫ g₀)).rightDerived r).obj
          ((smallEtalePullbackAb (πi i)).obj F₀)))
      ((smallEtaleStalkAb x.hom).map
        ((smallEtalePullbackAbComp' fV (𝟙 V) fV (Category.comp_id fV).symm).hom.app
          (((smallEtalePushforwardAb (πi i ≫ g₀)).rightDerived r).obj
            ((smallEtalePullbackAb (πi i)).obj F₀))) y) = y := fun y => by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  refine ⟨i, (smallEtaleStalkAb x.hom).map
    ((smallEtalePullbackAbComp' fV (𝟙 V) fV (Category.comp_id fV).symm).hom.app
      (((smallEtalePushforwardAb (πi i ≫ g₀)).rightDerived r).obj
        ((smallEtalePullbackAb (πi i)).obj F₀)))
    ((smallEtaleStalkAb x.hom).map ((smallEtalePullbackAb fV).map
      ((smallEtalePullbackAbIdOf (𝟙 V) rfl).inv.app
        (((smallEtalePushforwardAb (πi i ≫ g₀)).rightDerived r).obj
          ((smallEtalePullbackAb (πi i)).obj F₀)))) ζ), ?_⟩
  simp only [Functor.map_comp, ConcreteCategory.comp_apply]
  rw [he]
  simp only [Functor.comp_map, FixedBaseHigherDirectImage.projectionMap, Functor.map_comp,
    ConcreteCategory.comp_apply] at hζ
  exact (Eq.trans rfl hζ : _)

include hc hπi hπ in
/-- `Stacks.EtaleCohomology.exists_stalk_sourceTransfer_eq` with the leg of the cone at the stage
named `p`. -/
theorem exists_stalk_sourceTransfer_eq_of_eq
    (η : (smallEtaleStalkAb x.hom).obj ((smallEtalePullbackAb fV).obj
      (((smallEtalePushforwardAb (π ≫ g₀)).rightDerived r).obj
        ((smallEtalePullbackAb π).obj F₀)))) :
    ∃ (i : Iᵒᵖ) (ζ : (smallEtaleStalkAb x.hom).obj ((smallEtalePullbackAb fV).obj
      (((smallEtalePushforwardAb (πi i ≫ g₀)).rightDerived r).obj
        ((smallEtalePullbackAb (πi i)).obj F₀)))),
      ∀ (p : c.pt ⟶ D.obj i) (_hp : p = c.π.app i) (hπp : π = p ≫ πi i),
      (smallEtaleStalkAb x.hom).map
        ((smallEtalePullbackAbComp' fV (𝟙 V) fV (Category.comp_id fV).symm).inv.app
            (((smallEtalePushforwardAb (πi i ≫ g₀)).rightDerived r).obj
              ((smallEtalePullbackAb (πi i)).obj F₀)) ≫
          (smallEtalePullbackAb fV).map
            ((higherBaseChangeMapAb (𝟙 V) (πi i ≫ g₀) (π ≫ g₀) p
                (by rw [Category.comp_id, hπp, Category.assoc]) r).app
                ((smallEtalePullbackAb (πi i)).obj F₀) ≫
              ((smallEtalePushforwardAb (π ≫ g₀)).rightDerived r).map
                ((smallEtalePullbackAbComp' p (πi i) π hπp).hom.app F₀)))
        ζ = η := by
  obtain ⟨i, ζ, h⟩ := exists_stalk_sourceTransfer_eq fV g₀ F₀ r x hc π πi hπi hπ η
  refine ⟨i, ζ, ?_⟩
  rintro _ rfl _
  exact h

end Limit

/-! ### The target side of the limit argument -/

section Target

attribute [local instance] HasDerivedCategory.standard

/-- **[Stacks, Tag 09Z1] at a stalk: a class dying in the colimit dies at a stage.** Over a
directed set, with affine transition morphisms and quasi-compact quasi-separated structure
morphisms `h_i : Y_i ⟶ X`, an element of the stalk at a geometric point of `R^r h_{i,*} ℱ_i`
whose image in the stalk of `R^r h_* ℱ` vanishes is killed by a transition map `ψ_{ji}`. -/
theorem FixedBaseHigherDirectImage.exists_stalk_transitionMap_eq_zero {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] [Nonempty I] {E : Iᵒᵖ ⥤ Scheme.{u}}
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (E.map a)] {X : Scheme.{u}}
    (hX : ∀ i, E.obj i ⟶ X) [∀ i, QuasiCompact (hX i)] [∀ i, QuasiSeparated (hX i)]
    (hXa : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), hX i = E.map a ≫ hX j) {cE : Cone E} (hcE : IsLimit cE)
    (hXW : cE.pt ⟶ X) (hXw : ∀ i, hXW = cE.π.app i ≫ hX i) (r : ℕ)
    (F : EtaleSheafSystem E Ab.{u + 1}) (𝓕 : Sheaf (smallEtaleTopology cE.pt) Ab.{u + 1})
    (ι : ∀ i, (smallEtalePullbackAb (cE.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (hι : LimitHigherDirectImage.IsPullbackCocone cE F ι)
    (hpres : LimitHigherDirectImage.IsPullbackColimitPresentation cE 𝓕 F ι)
    (x : GeometricPoint X) {i : Iᵒᵖ}
    (z : (smallEtaleStalkAb x.hom).obj (FixedBaseHigherDirectImage.stage hX r F i))
    (hz : (smallEtaleStalkAb x.hom).map
      (FixedBaseHigherDirectImage.projectionMap hX r cE hXW 𝓕 F ι i (hXw i)) z = 0) :
    ∃ (j : Iᵒᵖ) (a : j ⟶ i), (smallEtaleStalkAb x.hom).map
      (FixedBaseHigherDirectImage.transitionMap hX r F a (hXa a)) z = 0 := by
  have H := (FixedBaseHigherDirectImage.isSystemColimit hX hXa hcE hXW hXw r F 𝓕 ι hι
    hpres).map_of_isLeftAdjoint
      ((Scheme.pointSmallEtale x.hom).skyscraperSheafAdjunction (A := Ab.{u + 1}))
  exact H.exists_eq_zero
    (fun a b => by
      rw [FixedBaseHigherDirectImage.transitionMap_comp r hX hXa, Functor.map_comp])
    (fun a => by
      rw [← Functor.map_comp, FixedBaseHigherDirectImage.projectionMap_cocone r hX hXa cE hXW
        hXw F 𝓕 ι hι a]) z hz

/-- An equation `a ≫ b = c ≫ d`, read on elements after a functor to abelian groups. -/
theorem map_map_apply_eq_of_comp_eq {𝒞 : Type*} [Category* 𝒞] (S : 𝒞 ⥤ Ab.{u + 1})
    {A B C D : 𝒞} {a : A ⟶ B} {b : B ⟶ C} {c : A ⟶ D} {d : D ⟶ C} (h : a ≫ b = c ≫ d)
    (z : S.obj A) : S.map b (S.map a z) = S.map d (S.map c z) := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, h, Functor.map_comp,
    ConcreteCategory.comp_apply]

/-- An equation `a = c ≫ d`, read on elements after a functor to abelian groups. -/
theorem map_apply_eq_of_eq_comp {𝒞 : Type*} [Category* 𝒞] (S : 𝒞 ⥤ Ab.{u + 1})
    {A C D : 𝒞} {a : A ⟶ C} {c : A ⟶ D} {d : D ⟶ C} (h : a = c ≫ d) (z : S.obj A) :
    S.map a z = S.map d (S.map c z) := by
  rw [h, Functor.map_comp, ConcreteCategory.comp_apply]

variable {X_V T₀ : Scheme.{u}} (F₀ : Sheaf (smallEtaleTopology T₀) Ab.{u + 1}) (r : ℕ)
  (x : GeometricPoint X_V) {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D}
  (π : c.pt ⟶ T₀) (πi : ∀ i, D.obj i ⟶ T₀)
  (hπi : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), D.map a ≫ πi j = πi i) (hπ : ∀ i, c.π.app i ≫ πi i = π)
  {E : Iᵒᵖ ⥤ Scheme.{u}} {cE : Cone E} (e : E ⟶ D) (eW : cE.pt ⟶ c.pt)
  (heW : ∀ i, cE.π.app i ≫ e.app i = eW ≫ c.π.app i)
  {hX : ∀ i, E.obj i ⟶ X_V} (hXa : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), hX i = E.map a ≫ hX j)
  {hXW : cE.pt ⟶ X_V} (hXw : ∀ i, hXW = cE.π.app i ≫ hX i)

include hπi in
/-- The composites `e_i ≫ π_i` are compatible with the transition morphisms. -/
theorem naturality_comp_eq {i j : Iᵒᵖ} (a : i ⟶ j) :
    E.map a ≫ e.app j ≫ πi j = e.app i ≫ πi i := by
  rw [← Category.assoc, e.naturality a, Category.assoc, hπi a]

include hπ heW in
/-- The composites `e_i ≫ π_i` are compatible with the cone legs. -/
theorem cone_naturality_comp_eq (i : Iᵒᵖ) : cE.π.app i ≫ e.app i ≫ πi i = eW ≫ π := by
  rw [← Category.assoc, heW i, Category.assoc, hπ i]

/-! Some lemmas below name the legs of the cones at the stage under consideration by variables
`q` and `p`, so that they apply to any morphisms equal to the legs. -/

/-- The map `R^p g_* M ⟶ R^p g'_* N` induced by a morphism `q : Y ⟶ X` over `S` and a map
`μ : q⁻¹ M ⟶ N`: the base change map of the square `g' ≫ 𝟙_S = q ≫ g`, read through the
identification of the inverse image along `𝟙_S` with the identity, followed by `R^p g'_* μ`. The
maps of [Stacks, Tag 09Z1] are of this form, with `q` a transition morphism or a leg of the
limit cone. -/
def FixedBaseHigherDirectImage.mapAlong {S X Y : Scheme.{u}} (g : X ⟶ S) (g' : Y ⟶ S)
    (q : Y ⟶ X) (w : g' ≫ 𝟙 S = q ≫ g) (p : ℕ) {M : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    {N : Sheaf (smallEtaleTopology Y) Ab.{u + 1}} (μ : (smallEtalePullbackAb q).obj M ⟶ N) :
    ((smallEtalePushforwardAb g).rightDerived p).obj M ⟶
      ((smallEtalePushforwardAb g').rightDerived p).obj N :=
  (smallEtalePullbackAbIdOf (𝟙 S) rfl).inv.app
      (((smallEtalePushforwardAb g).rightDerived p).obj M) ≫
    (higherBaseChangeMapAb (𝟙 S) g g' q w p).app M ≫
      ((smallEtalePushforwardAb g').rightDerived p).map μ

/-- The cocone map of [Stacks, Tag 09Z1] for the system of inverse images of `F₀` along the
`ι_i`, as a map along the leg of the cone. -/
theorem projectionMap_ofCocone_eq_mapAlong (ι : ∀ i, E.obj i ⟶ T₀)
    (hιa : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), E.map a ≫ ι j = ι i)
    (hιW : ∀ i, cE.π.app i ≫ ι i = eW ≫ π) (i : Iᵒᵖ) :
    FixedBaseHigherDirectImage.projectionMap hX r cE hXW ((smallEtalePullbackAb (eW ≫ π)).obj F₀)
        (EtaleSheafSystem.ofCocone ι hιa F₀) (EtaleSheafSystem.ofCoconeLeg ι hιa cE (eW ≫ π) hιW F₀)
        i (hXw i) =
      FixedBaseHigherDirectImage.mapAlong (hX i) hXW (cE.π.app i)
        (by rw [Category.comp_id, hXw i]) r
        ((smallEtalePullbackAbComp' (X := cE.pt) (cE.π.app i) (ι i) (eW ≫ π)
          (hιW i).symm).hom.app F₀) := by
  rw [projectionMap_ofCocone hX r cE hXW ι hιa (eW ≫ π) hιW F₀ i (hXw i)]
  rfl

/-- An instance of `Stacks.EtaleCohomology.targetTransfer_comp_map` for the transfer map of the
target from a stage `i` to the limit, with legs `q` and `p`. -/
theorem targetTransfer_comp_map_stage (ι : ∀ i, E.obj i ⟶ T₀) (hιe : ∀ i, ι i = e.app i ≫ πi i)
    (i : Iᵒᵖ) (q : cE.pt ⟶ E.obj i) (p : c.pt ⟶ D.obj i) (hπp : π = p ≫ πi i)
    (heq : q ≫ e.app i = eW ≫ p) (hιq : eW ≫ π = q ≫ ι i) (hφh : hXW ≫ 𝟙 X_V = q ≫ hX i) :
    ((smallEtalePullbackAbIdOf (𝟙 X_V) rfl).inv.app
          (((smallEtalePushforwardAb (hX i)).rightDerived r).obj
            ((smallEtalePullbackAb (e.app i)).obj ((smallEtalePullbackAb (πi i)).obj F₀))) ≫
        (higherBaseChangeMapAb (𝟙 X_V) (hX i) hXW q hφh r).app
          ((smallEtalePullbackAb (e.app i)).obj ((smallEtalePullbackAb (πi i)).obj F₀)) ≫
        ((smallEtalePushforwardAb hXW).rightDerived r).map
          ((smallEtalePullbackAbComp' q (e.app i) (eW ≫ p) heq.symm).hom.app
              ((smallEtalePullbackAb (πi i)).obj F₀) ≫
            (smallEtalePullbackAbComp' eW p (eW ≫ p) rfl).inv.app
              ((smallEtalePullbackAb (πi i)).obj F₀) ≫
            (smallEtalePullbackAb eW).map
              ((smallEtalePullbackAbComp' p (πi i) π hπp).hom.app F₀))) ≫
      ((smallEtalePushforwardAb hXW).rightDerived r).map
        ((smallEtalePullbackAbComp' eW π (eW ≫ π) rfl).hom.app F₀) =
    ((smallEtalePushforwardAb (hX i)).rightDerived r).map
        ((smallEtalePullbackAbComp' (e.app i) (πi i) (ι i) (hιe i)).hom.app F₀) ≫
      (smallEtalePullbackAbIdOf (𝟙 X_V) rfl).inv.app
          (((smallEtalePushforwardAb (hX i)).rightDerived r).obj
            ((smallEtalePullbackAb (ι i)).obj F₀)) ≫
        (higherBaseChangeMapAb (𝟙 X_V) (hX i) hXW q hφh r).app
          ((smallEtalePullbackAb (ι i)).obj F₀) ≫
        ((smallEtalePushforwardAb hXW).rightDerived r).map
          ((smallEtalePullbackAbComp' q (ι i) (eW ≫ π) hιq).hom.app F₀) :=
  targetTransfer_comp_map F₀ eW π (e.app i) (πi i) p hπp q heq (eW ≫ π) rfl (ι i) (hιe i) hιq
    r hXW (hX i) hφh

/-- `Stacks.EtaleCohomology.targetTransfer_comp_map_stage` with the cocone map written as a map
along `q`. -/
theorem targetTransfer_comp_eq_mapAlong (ι : ∀ i, E.obj i ⟶ T₀) (hιe : ∀ i, ι i = e.app i ≫ πi i)
    (i : Iᵒᵖ) (q : cE.pt ⟶ E.obj i) (p : c.pt ⟶ D.obj i) (hπp : π = p ≫ πi i)
    (heq : q ≫ e.app i = eW ≫ p) (hιq : eW ≫ π = q ≫ ι i) (hφh : hXW ≫ 𝟙 X_V = q ≫ hX i) :
    ((smallEtalePullbackAbIdOf (𝟙 X_V) rfl).inv.app
          (((smallEtalePushforwardAb (hX i)).rightDerived r).obj
            ((smallEtalePullbackAb (e.app i)).obj ((smallEtalePullbackAb (πi i)).obj F₀))) ≫
        (higherBaseChangeMapAb (𝟙 X_V) (hX i) hXW q hφh r).app
          ((smallEtalePullbackAb (e.app i)).obj ((smallEtalePullbackAb (πi i)).obj F₀)) ≫
        ((smallEtalePushforwardAb hXW).rightDerived r).map
          ((smallEtalePullbackAbComp' q (e.app i) (eW ≫ p) heq.symm).hom.app
              ((smallEtalePullbackAb (πi i)).obj F₀) ≫
            (smallEtalePullbackAbComp' eW p (eW ≫ p) rfl).inv.app
              ((smallEtalePullbackAb (πi i)).obj F₀) ≫
            (smallEtalePullbackAb eW).map
              ((smallEtalePullbackAbComp' p (πi i) π hπp).hom.app F₀))) ≫
      ((smallEtalePushforwardAb hXW).rightDerived r).map
        ((smallEtalePullbackAbComp' eW π (eW ≫ π) rfl).hom.app F₀) =
    ((smallEtalePushforwardAb (hX i)).rightDerived r).map
        ((smallEtalePullbackAbComp' (e.app i) (πi i) (ι i) (hιe i)).hom.app F₀) ≫
      FixedBaseHigherDirectImage.mapAlong (hX i) hXW q hφh r
        ((smallEtalePullbackAbComp' q (ι i) (eW ≫ π) hιq).hom.app F₀) :=
  targetTransfer_comp_map_stage F₀ r π πi e eW ι hιe i q p hπp heq hιq hφh

/-- **The transfer map of the target between two stages is a transition map of
[Stacks, Tag 09Z1]** for the system of inverse images of `F₀` along the `e_i ≫ π_i`, after the
identifications `e_i⁻¹ π_i⁻¹ ≅ (e_i ≫ π_i)⁻¹`, on elements of stalks. -/
theorem stalk_transitionMap_ofCocone (ι : ∀ i, E.obj i ⟶ T₀)
    (hιe : ∀ i, ι i = e.app i ≫ πi i) (hιa : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), E.map a ≫ ι j = ι i)
    {i j : Iᵒᵖ} (a : j ⟶ i)
    (z : (smallEtaleStalkAb x.hom).obj (((smallEtalePushforwardAb (hX i)).rightDerived r).obj
      ((smallEtalePullbackAb (e.app i)).obj ((smallEtalePullbackAb (πi i)).obj F₀)))) :
    (smallEtaleStalkAb x.hom).map
        (FixedBaseHigherDirectImage.transitionMap hX r (EtaleSheafSystem.ofCocone ι hιa F₀)
          a (hXa a))
        ((smallEtaleStalkAb x.hom).map (((smallEtalePushforwardAb (hX i)).rightDerived r).map
          ((smallEtalePullbackAbComp' (e.app i) (πi i) (ι i) (hιe i)).hom.app F₀)) z) =
      (smallEtaleStalkAb x.hom).map (((smallEtalePushforwardAb (hX j)).rightDerived r).map
          ((smallEtalePullbackAbComp' (e.app j) (πi j) (ι j) (hιe j)).hom.app F₀))
        ((smallEtaleStalkAb x.hom).map
          ((smallEtalePullbackAbIdOf (𝟙 X_V) rfl).inv.app
              (((smallEtalePushforwardAb (hX i)).rightDerived r).obj
                ((smallEtalePullbackAb (e.app i)).obj ((smallEtalePullbackAb (πi i)).obj F₀))) ≫
            (higherBaseChangeMapAb (𝟙 X_V) (hX i) (hX j) (E.map a)
                (by rw [Category.comp_id, hXa a]) r).app
              ((smallEtalePullbackAb (e.app i)).obj ((smallEtalePullbackAb (πi i)).obj F₀)) ≫
            ((smallEtalePushforwardAb (hX j)).rightDerived r).map
              ((smallEtalePullbackAbComp' (E.map a) (e.app i) (e.app j ≫ D.map a)
                  (e.naturality a).symm).hom.app ((smallEtalePullbackAb (πi i)).obj F₀) ≫
                (smallEtalePullbackAbComp' (e.app j) (D.map a) (e.app j ≫ D.map a) rfl).inv.app
                  ((smallEtalePullbackAb (πi i)).obj F₀) ≫
                (smallEtalePullbackAb (e.app j)).map
                  ((smallEtalePullbackAbComp' (D.map a) (πi i) (πi j)
                    (hπi a).symm).hom.app F₀))) z) := by
  have M := (targetTransfer_comp_map F₀ (e.app j) (πi j) (e.app i) (πi i) (D.map a)
    (hπi a).symm (E.map a) (e.naturality a) (ι j) (hιe j) (ι i) (hιe i)
    (hιa a).symm r (hX j) (hX i) (by rw [Category.comp_id, hXa a])).trans
    (congrArg (_ ≫ ·) (transitionMap_ofCocone hX r ι hιa F₀ a (hXa a)).symm)
  exact (map_map_apply_eq_of_comp_eq (smallEtaleStalkAb x.hom) M z).symm

/-- **A class killed by the transfer map of the target to the limit is killed by the cocone map
of [Stacks, Tag 09Z1]** for the system of inverse images of `F₀` along the `ι_i = e_i ≫ π_i`,
after the identification `e_i⁻¹ π_i⁻¹ ≅ ι_i⁻¹`. The leg of the cone `cE` at `i` is named `q`. -/
theorem stalk_projectionMap_ofCocone_eq_zero (ι : ∀ i, E.obj i ⟶ T₀)
    (hιe : ∀ i, ι i = e.app i ≫ πi i) (hιa : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), E.map a ≫ ι j = ι i)
    (hιW : ∀ i, cE.π.app i ≫ ι i = eW ≫ π) (i : Iᵒᵖ) (q : cE.pt ⟶ E.obj i)
    (hq : q = cE.π.app i) (p : c.pt ⟶ D.obj i) (hπp : π = p ≫ πi i)
    (heq : q ≫ e.app i = eW ≫ p) (hφh : hXW ≫ 𝟙 X_V = q ≫ hX i)
    (z : (smallEtaleStalkAb x.hom).obj (((smallEtalePushforwardAb (hX i)).rightDerived r).obj
      ((smallEtalePullbackAb (e.app i)).obj ((smallEtalePullbackAb (πi i)).obj F₀))))
    (hz : (smallEtaleStalkAb x.hom).map
      ((smallEtalePullbackAbIdOf (𝟙 X_V) rfl).inv.app
          (((smallEtalePushforwardAb (hX i)).rightDerived r).obj
            ((smallEtalePullbackAb (e.app i)).obj ((smallEtalePullbackAb (πi i)).obj F₀))) ≫
        (higherBaseChangeMapAb (𝟙 X_V) (hX i) hXW q hφh r).app
          ((smallEtalePullbackAb (e.app i)).obj ((smallEtalePullbackAb (πi i)).obj F₀)) ≫
        ((smallEtalePushforwardAb hXW).rightDerived r).map
          ((smallEtalePullbackAbComp' q (e.app i) (eW ≫ p) heq.symm).hom.app
              ((smallEtalePullbackAb (πi i)).obj F₀) ≫
            (smallEtalePullbackAbComp' eW p (eW ≫ p) rfl).inv.app
              ((smallEtalePullbackAb (πi i)).obj F₀) ≫
            (smallEtalePullbackAb eW).map
              ((smallEtalePullbackAbComp' p (πi i) π hπp).hom.app F₀))) z = 0) :
    (smallEtaleStalkAb x.hom).map
        (FixedBaseHigherDirectImage.projectionMap hX r cE hXW
          ((smallEtalePullbackAb (eW ≫ π)).obj F₀) (EtaleSheafSystem.ofCocone ι hιa F₀)
          (EtaleSheafSystem.ofCoconeLeg ι hιa cE (eW ≫ π) hιW F₀) i (hXw i))
      ((smallEtaleStalkAb x.hom).map (((smallEtalePushforwardAb (hX i)).rightDerived r).map
        ((smallEtalePullbackAbComp' (e.app i) (πi i) (ι i) (hιe i)).hom.app F₀)) z) = 0 := by
  subst hq
  have M := (targetTransfer_comp_eq_mapAlong F₀ r π πi e eW ι hιe i (cE.π.app i) p hπp heq
    (hιW i).symm hφh).trans (congrArg (_ ≫ ·)
      (projectionMap_ofCocone_eq_mapAlong F₀ r π eW hXw ι hιa hιW i).symm)
  exact (map_map_apply_eq_of_comp_eq (smallEtaleStalkAb x.hom) M z).symm.trans
    ((congrArg _ hz).trans (map_zero _))

include heW hπ hXw in
/-- **A class over a stage which dies over the limit already dies at a later stage.** Let
`Y = lim Y_i` be a directed limit with affine transition morphisms of schemes over `X_V`, with
quasi-compact and quasi-separated structure morphisms `h_i : Y_i ⟶ X_V`, lying over the system
`W = lim W_i` through a morphism of systems `e_i : Y_i ⟶ W_i`. By [Stacks, Tag 09Z1] over the
fixed base `X_V`, an element of the stalk at `x` of `R^r h_{i,*} e_i⁻¹ π_i⁻¹ F₀` killed by the
transfer map of the target of `Stacks.EtaleCohomology.obstructionPullbackMap_eq_comp` to `Y` is
killed by the transfer map to some `Y_j`, `j ≥ i`. The legs of the two cones at `i` are named
`q` and `p`. -/
theorem exists_stalk_targetTransfer_eq_zero [IsDirected I (· ≤ ·)] [Nonempty I]
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (E.map a)] (hcE : IsLimit cE)
    [∀ i, QuasiCompact (hX i)] [∀ i, QuasiSeparated (hX i)] (i : Iᵒᵖ) (q : cE.pt ⟶ E.obj i)
    (hq : q = cE.π.app i) (p : c.pt ⟶ D.obj i) (hπp : π = p ≫ πi i)
    (heq : q ≫ e.app i = eW ≫ p) (hφh : hXW ≫ 𝟙 X_V = q ≫ hX i)
    (z : (smallEtaleStalkAb x.hom).obj (((smallEtalePushforwardAb (hX i)).rightDerived r).obj
      ((smallEtalePullbackAb (e.app i)).obj ((smallEtalePullbackAb (πi i)).obj F₀))))
    (hz : (smallEtaleStalkAb x.hom).map
      ((smallEtalePullbackAbIdOf (𝟙 X_V) rfl).inv.app
          (((smallEtalePushforwardAb (hX i)).rightDerived r).obj
            ((smallEtalePullbackAb (e.app i)).obj ((smallEtalePullbackAb (πi i)).obj F₀))) ≫
        (higherBaseChangeMapAb (𝟙 X_V) (hX i) hXW q hφh r).app
          ((smallEtalePullbackAb (e.app i)).obj ((smallEtalePullbackAb (πi i)).obj F₀)) ≫
        ((smallEtalePushforwardAb hXW).rightDerived r).map
          ((smallEtalePullbackAbComp' q (e.app i) (eW ≫ p) heq.symm).hom.app
              ((smallEtalePullbackAb (πi i)).obj F₀) ≫
            (smallEtalePullbackAbComp' eW p (eW ≫ p) rfl).inv.app
              ((smallEtalePullbackAb (πi i)).obj F₀) ≫
            (smallEtalePullbackAb eW).map
              ((smallEtalePullbackAbComp' p (πi i) π hπp).hom.app F₀))) z = 0) :
    ∃ (j : Iᵒᵖ) (a : j ⟶ i), (smallEtaleStalkAb x.hom).map
      ((smallEtalePullbackAbIdOf (𝟙 X_V) rfl).inv.app
          (((smallEtalePushforwardAb (hX i)).rightDerived r).obj
            ((smallEtalePullbackAb (e.app i)).obj ((smallEtalePullbackAb (πi i)).obj F₀))) ≫
        (higherBaseChangeMapAb (𝟙 X_V) (hX i) (hX j) (E.map a)
            (by rw [Category.comp_id, hXa a]) r).app
          ((smallEtalePullbackAb (e.app i)).obj ((smallEtalePullbackAb (πi i)).obj F₀)) ≫
        ((smallEtalePushforwardAb (hX j)).rightDerived r).map
          ((smallEtalePullbackAbComp' (E.map a) (e.app i) (e.app j ≫ D.map a)
              (e.naturality a).symm).hom.app ((smallEtalePullbackAb (πi i)).obj F₀) ≫
            (smallEtalePullbackAbComp' (e.app j) (D.map a) (e.app j ≫ D.map a) rfl).inv.app
              ((smallEtalePullbackAb (πi i)).obj F₀) ≫
            (smallEtalePullbackAb (e.app j)).map
              ((smallEtalePullbackAbComp' (D.map a) (πi i) (πi j)
                (hπi a).symm).hom.app F₀))) z = 0 := by
  obtain ⟨ι, hιe⟩ : ∃ ι : ∀ i, E.obj i ⟶ T₀, ∀ i, ι i = e.app i ≫ πi i := ⟨_, fun _ => rfl⟩
  have hιa : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), E.map a ≫ ι j = ι i := fun a => by
    simpa only [hιe] using naturality_comp_eq πi hπi e a
  have hιW : ∀ i, cE.π.app i ≫ ι i = eW ≫ π := fun i => by
    simpa only [hιe] using cone_naturality_comp_eq π πi hπ e eW heW i
  obtain ⟨j, a, hj⟩ := FixedBaseHigherDirectImage.exists_stalk_transitionMap_eq_zero hX hXa hcE
    hXW hXw r (EtaleSheafSystem.ofCocone ι hιa F₀) ((smallEtalePullbackAb (eW ≫ π)).obj F₀)
    (EtaleSheafSystem.ofCoconeLeg ι hιa cE (eW ≫ π) hιW F₀)
    (EtaleSheafSystem.isPullbackCocone_ofCocone ι hιa cE (eW ≫ π) hιW F₀)
    (EtaleSheafSystem.isPullbackColimitPresentation_ofCocone ι hιa cE (eW ≫ π) hιW F₀) x _
    (stalk_projectionMap_ofCocone_eq_zero F₀ r x π πi e eW hXw ι hιe hιa hιW i q hq p hπp
      heq hφh z hz)
  have hj' := (stalk_transitionMap_ofCocone F₀ r x πi hπi e hXa ι hιe hιa a z).symm.trans hj
  exact ⟨j, a, (ConcreteCategory.bijective_of_isIso ((smallEtaleStalkAb x.hom).map
    (((smallEtalePushforwardAb (hX j)).rightDerived r).map
      ((smallEtalePullbackAbComp' (e.app j) (πi j) (ι j) (hιe j)).hom.app F₀)))).1
    (hj'.trans (map_zero _).symm)⟩

end Target

/-! ### Hypothesis (2) of the dévissage -/

section LimitHypothesis

attribute [local instance] HasDerivedCategory.standard

variable {V X_V T₀ Y₀ : Scheme.{u}} {fV : X_V ⟶ V} {g₀ : T₀ ⟶ V} {h₀ : Y₀ ⟶ X_V}
  {e₀ : Y₀ ⟶ T₀} (sq₀ : IsPullback h₀ e₀ fV g₀) (F₀ : Sheaf (smallEtaleTopology T₀) Ab.{u + 1})
  (r : ℕ) (x : GeometricPoint X_V) (ξ : obstructionStalk h₀ e₀ F₀ r x)

section Transfer

variable {W₁ W₂ Y₁ Y₂ : Scheme.{u}} (h₁ : Y₁ ⟶ X_V) (e₁ : Y₁ ⟶ W₁) (π₁ : W₁ ⟶ T₀)
  (h₂ : Y₂ ⟶ X_V) (e₂ : Y₂ ⟶ W₂) (π₂ : W₂ ⟶ T₀) (φ : W₁ ⟶ W₂) (hπ : π₁ = φ ≫ π₂)
  (yφ : Y₁ ⟶ Y₂) (hφh : h₁ ≫ 𝟙 X_V = yφ ≫ h₂) (hφe : yφ ≫ e₂ = e₁ ≫ φ)
  (sq₁ : IsPullback h₁ e₁ fV (π₁ ≫ g₀)) (sq₂ : IsPullback h₂ e₂ fV (π₂ ≫ g₀))
  (hy : obstructionLift sq₀ π₁ sq₁ = yφ ≫ obstructionLift sq₀ π₂ sq₂)

include hy in
/-- **The obstruction condition is transported along the transfer maps**, on elements. For a
morphism `φ : W₁ ⟶ W₂` over `T₀` covered by `yφ` between cartesian squares, the base change map
over `W₁` takes the transfer of `ζ` to the pullback of `ξ` exactly when the transfer map of the
target identifies the base change of `ζ` and the pullback of `ξ` over `W₂`. -/
theorem stalk_higherBaseChangeMapAb_eq_iff_targetTransfer
    (ζ : (smallEtaleStalkAb x.hom).obj ((smallEtalePullbackAb fV).obj
      (((smallEtalePushforwardAb (π₂ ≫ g₀)).rightDerived r).obj
        ((smallEtalePullbackAb π₂).obj F₀)))) :
    (smallEtaleStalkAb x.hom).map
        ((higherBaseChangeMapAb fV (π₁ ≫ g₀) h₁ e₁ sq₁.w r).app ((smallEtalePullbackAb π₁).obj F₀))
        ((smallEtaleStalkAb x.hom).map
          ((smallEtalePullbackAbComp' fV (𝟙 V) fV (Category.comp_id fV).symm).inv.app
              (((smallEtalePushforwardAb (π₂ ≫ g₀)).rightDerived r).obj
                ((smallEtalePullbackAb π₂).obj F₀)) ≫
            (smallEtalePullbackAb fV).map
              ((higherBaseChangeMapAb (𝟙 V) (π₂ ≫ g₀) (π₁ ≫ g₀) φ
                  (by rw [Category.comp_id, hπ, Category.assoc]) r).app
                  ((smallEtalePullbackAb π₂).obj F₀) ≫
                ((smallEtalePushforwardAb (π₁ ≫ g₀)).rightDerived r).map
                  ((smallEtalePullbackAbComp' φ π₂ π₁ hπ).hom.app F₀))) ζ) =
      (smallEtaleStalkAb x.hom).map
        ((higherBaseChangeMapAb (𝟙 X_V) h₀ h₁ (obstructionLift sq₀ π₁ sq₁)
            (obstructionLift_fst sq₀ π₁ sq₁) r).app ((smallEtalePullbackAb e₀).obj F₀) ≫
          ((smallEtalePushforwardAb h₁).rightDerived r).map
            ((smallEtalePullbackAbComp' (obstructionLift sq₀ π₁ sq₁) e₀
                (obstructionLift sq₀ π₁ sq₁ ≫ e₀) rfl).hom.app F₀ ≫
              (smallEtalePullbackAbComp' e₁ π₁ (obstructionLift sq₀ π₁ sq₁ ≫ e₀)
                (obstructionLift_snd sq₀ π₁ sq₁)).inv.app F₀)) ξ ↔
    (smallEtaleStalkAb x.hom).map
        ((smallEtalePullbackAbIdOf (𝟙 X_V) rfl).inv.app
            (((smallEtalePushforwardAb h₂).rightDerived r).obj
              ((smallEtalePullbackAb e₂).obj ((smallEtalePullbackAb π₂).obj F₀))) ≫
          (higherBaseChangeMapAb (𝟙 X_V) h₂ h₁ yφ hφh r).app
            ((smallEtalePullbackAb e₂).obj ((smallEtalePullbackAb π₂).obj F₀)) ≫
          ((smallEtalePushforwardAb h₁).rightDerived r).map
            ((smallEtalePullbackAbComp' yφ e₂ (e₁ ≫ φ) hφe.symm).hom.app
                ((smallEtalePullbackAb π₂).obj F₀) ≫
              (smallEtalePullbackAbComp' e₁ φ (e₁ ≫ φ) rfl).inv.app
                ((smallEtalePullbackAb π₂).obj F₀) ≫
              (smallEtalePullbackAb e₁).map ((smallEtalePullbackAbComp' φ π₂ π₁ hπ).hom.app F₀)))
        ((show (smallEtaleStalkAb x.hom).obj (((smallEtalePushforwardAb h₂).rightDerived r).obj
              ((smallEtalePullbackAb e₂).obj ((smallEtalePullbackAb π₂).obj F₀))) from
          (smallEtaleStalkAb x.hom).map
          ((higherBaseChangeMapAb fV (π₂ ≫ g₀) h₂ e₂ sq₂.w r).app
            ((smallEtalePullbackAb π₂).obj F₀)) ζ) -
          (show (smallEtaleStalkAb x.hom).obj (((smallEtalePushforwardAb h₂).rightDerived r).obj
              ((smallEtalePullbackAb e₂).obj ((smallEtalePullbackAb π₂).obj F₀))) from
          (smallEtaleStalkAb x.hom).map
            ((higherBaseChangeMapAb (𝟙 X_V) h₀ h₂ (obstructionLift sq₀ π₂ sq₂)
                (obstructionLift_fst sq₀ π₂ sq₂) r).app ((smallEtalePullbackAb e₀).obj F₀) ≫
              ((smallEtalePushforwardAb h₂).rightDerived r).map
                ((smallEtalePullbackAbComp' (obstructionLift sq₀ π₂ sq₂) e₀
                    (obstructionLift sq₀ π₂ sq₂ ≫ e₀) rfl).hom.app F₀ ≫
                  (smallEtalePullbackAbComp' e₂ π₂ (obstructionLift sq₀ π₂ sq₂ ≫ e₀)
                    (obstructionLift_snd sq₀ π₂ sq₂)).inv.app F₀)) ξ)) = 0 := by
  rw [map_sub, sub_eq_zero]
  exact Eq.congr
    (map_map_apply_eq_of_comp_eq (smallEtaleStalkAb x.hom)
      (obstructionSourceTransferMap_comp_higherBaseChangeMapAb (w₁ := sq₁.w) (w₂ := sq₂.w)
        (wφ := by rw [Category.comp_id, hπ, Category.assoc]) (hφe := hφe) ..) ζ)
    (map_apply_eq_of_eq_comp (smallEtaleStalkAb x.hom)
      (obstructionPullbackMap_eq_comp (hy₁ := obstructionLift_snd sq₀ π₁ sq₁)
        (hy₂ := obstructionLift_snd sq₀ π₂ sq₂) (hyh₁ := obstructionLift_fst sq₀ π₁ sq₁)
        (hyh₂ := obstructionLift_fst sq₀ π₂ sq₂) (hy := hy) (hφe := hφe) ..) ξ)

end Transfer

include sq₀ in
/-- **`P(lim W_i)` from `P(W_i)` for all `i`, on given cartesian squares.** Let `W = lim W_i` be
a directed limit with affine transition morphisms over `T₀`, with quasi-compact quasi-separated
`W_i ⟶ V`, and let `Y = lim Y_i` be a directed limit of the same kind over `X_V`, with cartesian
squares `Y_i = X_V ×_V W_i`, `Y = X_V ×_V W` compatible with the transition morphisms. If
`P(W_i)` holds for every `i`, then `P(W)` holds.

Suppose `ξ'` is the image of `η` under the base change map over `W`. By
`Stacks.EtaleCohomology.exists_stalk_sourceTransfer_eq` the class `η` comes from a class `ζ` over
some `W_i`. The transfer maps intertwine the base change maps and the pullback maps
(`Stacks.EtaleCohomology.stalk_higherBaseChangeMapAb_eq_iff_targetTransfer`), so the difference
of the image of `ζ` and the image of `ξ` over `Y_i` dies over `Y`. By
`Stacks.EtaleCohomology.exists_stalk_targetTransfer_eq_zero` it dies over some `Y_j`, `j ≥ i`,
where the image of `ζ` over `W_j` then maps to `ξ'`, against `P(W_j)`. -/
theorem obstructionSurvives_of_isLimit_of_isPullback {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] [Nonempty I] {D : Iᵒᵖ ⥤ Scheme.{u}}
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)] {c : Cone D} (hc : IsLimit c)
    (π : c.pt ⟶ T₀) (πi : ∀ i, D.obj i ⟶ T₀)
    (hπi : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), D.map a ≫ πi j = πi i) (hπ : ∀ i, c.π.app i ≫ πi i = π)
    [∀ i, QuasiCompact (πi i ≫ g₀)] [∀ i, QuasiSeparated (πi i ≫ g₀)]
    {E : Iᵒᵖ ⥤ Scheme.{u}} [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (E.map a)] {cE : Cone E}
    (hcE : IsLimit cE) (hX : ∀ i, E.obj i ⟶ X_V) [∀ i, QuasiCompact (hX i)]
    [∀ i, QuasiSeparated (hX i)] (hXa : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), hX i = E.map a ≫ hX j)
    (e : E ⟶ D) (sq : ∀ i, IsPullback (hX i) (e.app i) fV (πi i ≫ g₀)) (hXW : cE.pt ⟶ X_V)
    (hXw : ∀ i, hXW = cE.π.app i ≫ hX i) (eW : cE.pt ⟶ c.pt)
    (heW : ∀ i, cE.π.app i ≫ e.app i = eW ≫ c.π.app i) (sqW : IsPullback hXW eW fV (π ≫ g₀))
    (hP : ∀ i, ObstructionSurvives fV g₀ h₀ e₀ F₀ r x ξ (D.obj i) (πi i)) :
    ObstructionSurvives fV g₀ h₀ e₀ F₀ r x ξ c.pt π := by
  rw [obstructionSurvives_iff_of_isPullback sq₀ π sqW]
  intro η hη
  obtain ⟨i, ζ, hζ⟩ := exists_stalk_sourceTransfer_eq_of_eq fV g₀ F₀ r x hc π πi hπi hπ η
  obtain ⟨p, hp⟩ : ∃ p : c.pt ⟶ D.obj i, p = c.π.app i := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : cE.pt ⟶ E.obj i, q = cE.π.app i := ⟨_, rfl⟩
  have hπp : π = p ≫ πi i := by rw [hp, hπ]
  have heq : q ≫ e.app i = eW ≫ p := by rw [hp, hq, heW]
  have hXq : hXW = q ≫ hX i := by rw [hq, ← hXw i]
  have hφh : hXW ≫ 𝟙 X_V = q ≫ hX i := (Category.comp_id _).trans hXq
  rw [← hζ p hp hπp] at hη
  have hyW : obstructionLift sq₀ π sqW = q ≫ obstructionLift sq₀ (πi i) (sq i) :=
    obstructionLift_eq_comp sq₀ π sqW (πi i) q _ hφh (obstructionLift_fst sq₀ (πi i) (sq i))
      (by rw [← Category.assoc, heq, Category.assoc, ← hπp]) (obstructionLift_snd ..)
  have h0 := (stalk_higherBaseChangeMapAb_eq_iff_targetTransfer sq₀ F₀ r x ξ hXW eW π (hX i)
    (e.app i) (πi i) p hπp q hφh heq sqW (sq i) hyW ζ).1 hη
  obtain ⟨j, a, hj⟩ := exists_stalk_targetTransfer_eq_zero F₀ r x π πi hπi hπ e eW heW hXa hXw
    hcE i q hq p hπp heq hφh _ h0
  have hyj : obstructionLift sq₀ (πi j) (sq j) =
      E.map a ≫ obstructionLift sq₀ (πi i) (sq i) :=
    obstructionLift_eq_comp sq₀ (πi j) (sq j) (πi i) (E.map a) _
      (by rw [Category.comp_id, hXa a]) (obstructionLift_fst sq₀ (πi i) (sq i))
      (naturality_comp_eq πi hπi e a) (obstructionLift_snd ..)
  exact (obstructionSurvives_iff_of_isPullback sq₀ (πi j) (sq j) F₀ r x ξ).1 (hP j) _
    ((stalk_higherBaseChangeMapAb_eq_iff_targetTransfer sq₀ F₀ r x ξ (hX j) (e.app j) (πi j)
      (hX i) (e.app i) (πi i) (D.map a) (hπi a).symm (E.map a) (by rw [Category.comp_id, hXa a])
      (e.naturality a) (sq j) (sq i) hyj ζ).2 hj)

include sq₀ in
/-- **Hypothesis (2) of the dévissage of [Stacks, Tag 0F06] for the property `P` of the proof of
[Stacks, Tag 0F07].** Let `V` be affine and let `W = lim W_i` be the limit of a directed inverse
system of quasi-compact quasi-separated schemes over `T₀` with affine transition morphisms. If
`P(W_i)` holds for every `i`, then `P(W)` holds. The squares tested are the fibre products
`X_V ×_V W_i`, whose limit is `X_V ×_V W` (`Stacks.EtaleCohomology.fibreProductConeIsLimit`),
and the argument is `Stacks.EtaleCohomology.obstructionSurvives_of_isLimit_of_isPullback`. -/
theorem obstructionSurvives_of_isLimit [IsAffine V] {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] [Nonempty I] (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (π : c.pt ⟶ T₀) (πi : ∀ i, D.obj i ⟶ T₀)
    (hπi : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), D.map a ≫ πi j = πi i) (hπ : ∀ i, c.π.app i ≫ πi i = π)
    (hP : ∀ i, ObstructionSurvives fV g₀ h₀ e₀ F₀ r x ξ (D.obj i) (πi i)) :
    ObstructionSurvives fV g₀ h₀ e₀ F₀ r x ξ c.pt π := by
  have hqc : ∀ i, QuasiCompact (πi i ≫ g₀) := fun i =>
    (quasiCompact_iff_compactSpace (πi i ≫ g₀)).2 inferInstance
  have hqs : ∀ i, QuasiSeparated (πi i ≫ g₀) := fun i =>
    (quasiSeparated_iff_quasiSeparatedSpace (πi i ≫ g₀)).2 inferInstance
  have hg : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), D.map a ≫ πi j ≫ g₀ = πi i ≫ g₀ :=
    stage_comp_eq g₀ πi hπi
  have hgc : ∀ i, c.π.app i ≫ πi i ≫ g₀ = π ≫ g₀ := cone_comp_stage_eq g₀ π πi hπ
  have hqcX : ∀ i, QuasiCompact (fibreProductFst fV (fun i => πi i ≫ g₀) hg i) := fun i =>
    have := hqc i
    inferInstanceAs (QuasiCompact (pullback.fst _ _))
  have hqsX : ∀ i, QuasiSeparated (fibreProductFst fV (fun i => πi i ≫ g₀) hg i) := fun i =>
    have := hqs i
    inferInstanceAs (QuasiSeparated (pullback.fst _ _))
  exact obstructionSurvives_of_isLimit_of_isPullback sq₀ F₀ r x ξ hc π πi hπi hπ
    (fibreProductConeIsLimit fV (fun i => πi i ≫ g₀) hg c (π ≫ g₀) hgc hc)
    (fibreProductFst fV (fun i => πi i ≫ g₀) hg)
    (fun a => (fibreProductSystem_map_fibreProductFst fV (fun i => πi i ≫ g₀) hg a).symm)
    { app := fibreProductSnd fV (fun i => πi i ≫ g₀) hg
      naturality := fun _ _ a => fibreProductSystem_map_fibreProductSnd fV _ hg a }
    (isPullback_fibreProduct fV (fun i => πi i ≫ g₀) hg)
    (fibreProductConeFst fV (fun i => πi i ≫ g₀) hg c (π ≫ g₀) hgc)
    (fun i => (fibreProductCone_π_app_fibreProductFst fV _ hg c (π ≫ g₀) hgc i).symm)
    (fibreProductConeSnd fV (fun i => πi i ≫ g₀) hg c (π ≫ g₀) hgc)
    (fun i => fibreProductCone_π_app_fibreProductSnd fV _ hg c (π ≫ g₀) hgc i)
    (isPullback_fibreProductCone fV (fun i => πi i ≫ g₀) hg c (π ≫ g₀) hgc) hP

end LimitHypothesis

end Stacks.EtaleCohomology

end
