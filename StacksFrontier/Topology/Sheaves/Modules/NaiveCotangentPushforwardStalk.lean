module

public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentPushforwardMap

/-!
# The comparison of the scalar extensions of the differentials along `f` over a changed base

Let `f : Y ⟶ X` be a continuous map, `φ₁ : A₁ ⟶ B` and `φ₂ : A₂ ⟶ f⁻¹B` locally surjective
presentations, `ψ : A₁ ⟶ f_*A₂` compatible with them, and `a₁ : R ⟶ A₁`, `a₂ : R₂ ⟶ A₂` base rings
with `ρ : R ⟶ f_*R₂` compatible with `ψ`. The comparison
`f⁻¹(B ⊗[A₁] Ω[A₁/R]) ⟶ f⁻¹B ⊗[A₂] Ω[A₂/R₂]` adjoint to
`Stacks.Sites.Conormal.tensorSheafMapPush` is an isomorphism as soon as the induced maps on the
stalks of `A₁` and of `R` are bijective at every point of `Y`.

This is `Stacks.SheafOfModules.isIso_inverseImageTensorMapAlong` of
`StacksFrontier/Topology/Sheaves/Modules/NaiveCotangentInverseImage.lean`, where `R₂ = f⁻¹R` and `ρ`
is the unit, with the base changed: the inverse image `(gf)⁻¹𝒪_S` of the structure sheaf of a base
along a composite is not literally `g⁻¹f⁻¹𝒪_S`, and this is what lets the comparison
`g⁻¹𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{g⁻¹𝒪_X/(gf)⁻¹𝒪_S}` be treated (**Stacks 08TM**). The proof is the same: the map
on the stalks of the sectionwise differentials is induced by a square of ring isomorphisms.

## Main results

* `Stacks.SheafOfModules.bijective_stalkOmegaMapPushₛₗ`: the map on the stalks of the sectionwise
  differentials is bijective.
* `Stacks.SheafOfModules.isIso_inverseImageTensorMapPush`: the comparison of the scalar
  extensions of the differentials is an isomorphism.

## References

* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TensorProduct

universe u

namespace Stacks.SheafOfModules

open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open AlgebraicGeometry.SheafOfModules (inverseImageRingHom inverseImageAdjunction
  underlyingRingSheaf)

variable {X Y : TopCat.{u}} (f : Y ⟶ X) (B : TopCat.Sheaf CommRingCat.{u} X)
  {A₁ : TopCat.Sheaf CommRingCat.{u} X} {A₂ : TopCat.Sheaf CommRingCat.{u} Y}
  (φ₁ : A₁ ⟶ B) (φ₂ : A₂ ⟶ (TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
  (ψ : A₁ ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj A₂) (y : Y)
  (R : TopCat.Sheaf CommRingCat.{u} X) (R₂ : TopCat.Sheaf CommRingCat.{u} Y)
  (a₁ : R ⟶ A₁) (a₂ : R₂ ⟶ A₂)
  (ρ : R ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj R₂)
  (ha : a₁ ≫ ψ = ρ ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} f).map a₂)

include ha in
/-- The stalk at `y` of the sectionwise differentials of `a₂`, as a cocone over the diagram of
the sections of the sectionwise differentials of `a₁` near `f y`. -/
noncomputable def omegaStalkCoconePush :
    Cocone ((OpenNhds.inclusion (f y)).op ⋙ (differentialsPresheaf a₁.hom).presheaf) where
  pt := AddCommGrpCat.of (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
    (differentialsPresheaf a₂.hom).presheaf y))
  ι :=
    { app := fun V => AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun ω => (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            (differentialsPresheaf a₂.hom).presheaf ((Opens.map f).obj V.unop.1) y V.unop.2).hom
          (differentialsMapPush f ψ R R₂ a₁ a₂ ρ ha (op V.unop.1) ω))
        (fun ω ω' => (congrArg (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            (differentialsPresheaf a₂.hom).presheaf ((Opens.map f).obj V.unop.1) y V.unop.2).hom
            (map_add (differentialsMapPush f ψ R R₂ a₁ a₂ ρ ha (op V.unop.1)) ω ω')).trans
          (map_add _ _ _)))
      naturality := by
        intro V W g
        ext ω
        refine Eq.trans (congrArg (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            (differentialsPresheaf a₂.hom).presheaf ((Opens.map f).obj W.unop.1) y W.unop.2).hom
          (differentialsMapPush_naturality f ψ R R₂ a₁ a₂ ρ ha
            ((OpenNhds.inclusion (f y)).op.map g) ω)) ?_
        exact TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u})
          (differentialsPresheaf a₂.hom).presheaf
          ((Opens.map f).map ((OpenNhds.inclusion (f y)).map g.unop)) y W.unop.2 _ }

include ha in
/-- The map `(Ω[A₁/R])_{f y} → (Ω[A₂/R₂])_y` on the stalks of the sectionwise differentials
induced by `ψ`. -/
noncomputable def omegaStalkHomPush :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (differentialsPresheaf a₁.hom).presheaf (f y)) →+
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (differentialsPresheaf a₂.hom).presheaf y) :=
  (colimit.desc _ (omegaStalkCoconePush f ψ y R R₂ a₁ a₂ ρ ha)).hom

include ha in
/-- The induced map on the stalks of the sectionwise differentials carries the germ at `f y` of
a section `ω` to the germ at `y` of its image. -/
theorem omegaStalkHomPush_germ (U : Opens X) (hU : f y ∈ U)
    (ω : (differentialsPresheaf a₁.hom).obj (op U)) :
    omegaStalkHomPush f ψ y R R₂ a₁ a₂ ρ ha
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (differentialsPresheaf a₁.hom).presheaf U (f y) hU).hom ω) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (differentialsPresheaf a₂.hom).presheaf ((Opens.map f).obj U) y hU).hom
        (differentialsMapPush f ψ R R₂ a₁ a₂ ρ ha (op U) ω) :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (omegaStalkCoconePush f ψ y R R₂ a₁ a₂ ρ ha)
      (op (⟨U, hU⟩ : OpenNhds (f y)))) ω

include ha in
/-- The induced map on the stalks of the sectionwise differentials is semilinear over the
induced map on ring stalks. -/
theorem omegaStalkHomPush_smul (r : ToType (TopCat.Presheaf.stalk A₁.obj (f y)))
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (differentialsPresheaf a₁.hom).presheaf (f y))) :
    omegaStalkHomPush f ψ y R R₂ a₁ a₂ ρ ha (r • ξ) =
      stalkRingMapAlong f ψ y r • omegaStalkHomPush f ψ y R R₂ a₁ a₂ ρ ha ξ := by
  obtain ⟨Ur, hr, r₁, rfl⟩ := TopCat.Presheaf.exists_germ_eq A₁.obj r
  obtain ⟨Uw, hw, ω₁, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u})
    (differentialsPresheaf a₁.hom).presheaf ξ
  have hU : f y ∈ Ur ⊓ Uw := ⟨hr, hw⟩
  have er := TopCat.Presheaf.germ_res_apply A₁.obj
    (homOfLE (inf_le_left : Ur ⊓ Uw ≤ Ur)) (f y) hU r₁
  have ew := TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u})
    (differentialsPresheaf a₁.hom).presheaf (homOfLE (inf_le_right : Ur ⊓ Uw ≤ Uw)) (f y) hU ω₁
  rw [← er, ← ew]
  refine Eq.trans (congrArg (omegaStalkHomPush f ψ y R R₂ a₁ a₂ ρ ha)
    (PresheafOfModules.germ_smul (differentialsPresheaf a₁.hom) (f y) (Ur ⊓ Uw) hU _ _).symm) ?_
  refine (omegaStalkHomPush_germ f ψ y R R₂ a₁ a₂ ρ ha (Ur ⊓ Uw) hU _).trans ?_
  refine Eq.trans (congrArg (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
      (differentialsPresheaf a₂.hom).presheaf ((Opens.map f).obj (Ur ⊓ Uw)) y hU).hom
    (map_smulₛₗ (differentialsMapPush f ψ R R₂ a₁ a₂ ρ ha (op (Ur ⊓ Uw))) _ _)) ?_
  refine (PresheafOfModules.germ_smul (differentialsPresheaf a₂.hom) y
    ((Opens.map f).obj (Ur ⊓ Uw)) hU _ _).trans ?_
  refine congrArg₂ (· • ·) (stalkRingMapAlong_germ f ψ y (Ur ⊓ Uw) hU _).symm ?_
  exact (omegaStalkHomPush_germ f ψ y R R₂ a₁ a₂ ρ ha (Ur ⊓ Uw) hU _).symm

include ha in
/-- **The map on the stalks of the sectionwise differentials induced by `ψ`**, semilinear over
the induced map on ring stalks. -/
noncomputable def stalkOmegaMapPushₛₗ :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (differentialsPresheaf a₁.hom).presheaf (f y)) →ₛₗ[stalkRingMapAlong f ψ y]
      ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (differentialsPresheaf a₂.hom).presheaf y) where
  toFun := omegaStalkHomPush f ψ y R R₂ a₁ a₂ ρ ha
  map_add' := map_add _
  map_smul' := omegaStalkHomPush_smul f ψ y R R₂ a₁ a₂ ρ ha

include ha in
/-- **The induced maps on ring stalks are compatible with the two structural morphisms**:
`ψ` after `a₁` is `a₂` after `ρ`, on stalks. -/
theorem stalkRingMapAlong_comp_structureMapPush
    (r : ToType (TopCat.Presheaf.stalk R.obj (f y))) :
    stalkRingMapAlong f ψ y
        (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} (f y)).map a₁.hom).hom r) =
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map a₂.hom).hom
        (stalkRingMapAlong f ρ y r) := by
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq R.obj r
  refine Eq.trans (congrArg (stalkRingMapAlong f ψ y)
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U (f y) hU a₁.hom s)) ?_
  refine (stalkRingMapAlong_germ f ψ y U hU _).trans ?_
  refine Eq.symm (Eq.trans (congrArg
    (((TopCat.Presheaf.stalkFunctor CommRingCat.{u} y).map a₂.hom).hom)
    (stalkRingMapAlong_germ f ρ y U hU s)) ?_)
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply ((Opens.map f).obj U) y hU a₂.hom _).trans ?_
  refine congrArg (TopCat.Presheaf.germ A₂.obj ((Opens.map f).obj U) y hU).hom ?_
  exact congrArg (fun t : R.obj.obj (op U) ⟶ A₂.obj.obj ((Opens.map f).op.obj (op U)) => t.hom s)
    (differentialsSquarePush f ψ R R₂ a₁ a₂ ρ ha (op U))

include ha in
/-- The induced map on the stalks of the sectionwise differentials, on germs. -/
theorem stalkOmegaMapPushₛₗ_germ (U : Opens X) (hU : f y ∈ U)
    (ω : (differentialsPresheaf a₁.hom).obj (op U)) :
    stalkOmegaMapPushₛₗ f ψ y R R₂ a₁ a₂ ρ ha
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (differentialsPresheaf a₁.hom).presheaf U (f y) hU).hom ω) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (differentialsPresheaf a₂.hom).presheaf ((Opens.map f).obj U) y hU).hom
        (differentialsMapPush f ψ R R₂ a₁ a₂ ρ ha (op U) ω) :=
  omegaStalkHomPush_germ f ψ y R R₂ a₁ a₂ ρ ha U hU ω

include ha in
/-- **The induced map on the stalks of the sectionwise differentials is bijective** as soon as
the induced maps on the stalks of `A₁` and of `R` are. -/
theorem bijective_stalkOmegaMapPushₛₗ
    (hbij : Function.Bijective (stalkRingMapAlong f ψ y))
    (hρ : Function.Bijective (stalkRingMapAlong f ρ y)) :
    Function.Bijective (stalkOmegaMapPushₛₗ f ψ y R R₂ a₁ a₂ ρ ha) := by
  let : DecidableEq (OrderDual (TopologicalSpace.OpenNhds (f y))) := Classical.decEq _
  let : DecidableEq (OrderDual (TopologicalSpace.OpenNhds y)) := Classical.decEq _
  let := Stacks.RelativeDifferentialStalk.algebraStalk a₁.hom (f y)
  let := Stacks.RelativeDifferentialStalk.algebraStalk a₂.hom y
  set e₁ := Stacks.RelativeDifferentialStalk.stalkLinearEquiv a₁.hom (f y)
  set e₂ := Stacks.RelativeDifferentialStalk.stalkLinearEquiv a₂.hom y
  have hadd : ∀ x z, e₂ (stalkOmegaMapPushₛₗ f ψ y R R₂ a₁ a₂ ρ ha (e₁.symm (x + z))) =
      e₂ (stalkOmegaMapPushₛₗ f ψ y R R₂ a₁ a₂ ρ ha (e₁.symm x)) +
        e₂ (stalkOmegaMapPushₛₗ f ψ y R R₂ a₁ a₂ ρ ha (e₁.symm z)) := by
    intro x z
    simp only [map_add]
  have hsmul : ∀ (s : ToType (TopCat.Presheaf.stalk A₁.obj (f y))) ω,
      e₂ (stalkOmegaMapPushₛₗ f ψ y R R₂ a₁ a₂ ρ ha (e₁.symm (s • ω))) =
        stalkRingMapAlong f ψ y s •
          e₂ (stalkOmegaMapPushₛₗ f ψ y R R₂ a₁ a₂ ρ ha (e₁.symm ω)) := by
    intro s ω
    refine Eq.trans (congrArg (fun ζ => e₂ (stalkOmegaMapPushₛₗ f ψ y R R₂ a₁ a₂ ρ ha ζ))
      (map_smul e₁.symm s ω)) ?_
    refine Eq.trans (congrArg e₂
      (map_smulₛₗ (stalkOmegaMapPushₛₗ f ψ y R R₂ a₁ a₂ ρ ha) s (e₁.symm ω))) ?_
    exact map_smul e₂ _ _
  have hT : ∀ s : ToType (TopCat.Presheaf.stalk A₁.obj (f y)),
      e₂ (stalkOmegaMapPushₛₗ f ψ y R R₂ a₁ a₂ ρ ha
          (e₁.symm (KaehlerDifferential.D _ _ s))) =
        KaehlerDifferential.D _ _ (stalkRingMapAlong f ψ y s) := by
    intro s
    obtain ⟨U, hU, s₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq A₁.obj s
    have h₁ : e₁.symm (KaehlerDifferential.D _ _
          ((TopCat.Presheaf.germ A₁.obj U (f y) hU).hom s₀)) =
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (differentialsPresheaf a₁.hom).presheaf U (f y) hU).hom
          (CommRingCat.KaehlerDifferential.d (f := a₁.hom.app (op U)) s₀) :=
      (LinearEquiv.symm_apply_eq _).mpr
        (Stacks.RelativeDifferentialStalk.stalkLinearEquiv_germ_D a₁.hom (f y)
          (OrderDual.toDual (⟨U, hU⟩ : TopologicalSpace.OpenNhds (f y))) s₀).symm
    refine Eq.trans (congrArg (fun ζ => e₂ (stalkOmegaMapPushₛₗ f ψ y R R₂ a₁ a₂ ρ ha ζ)) h₁) ?_
    refine Eq.trans (congrArg e₂ (stalkOmegaMapPushₛₗ_germ f ψ y R R₂ a₁ a₂ ρ ha U hU _)) ?_
    refine Eq.trans (congrArg (fun ω : (differentialsPresheaf a₂.hom).obj
        ((Opens.map f).op.obj (op U)) => e₂ ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (differentialsPresheaf a₂.hom).presheaf ((Opens.map f).obj U) y hU).hom ω))
      (differentialsMapPush_d f ψ R R₂ a₁ a₂ ρ ha (op U) s₀)) ?_
    refine Eq.trans (Stacks.RelativeDifferentialStalk.stalkLinearEquiv_germ_D a₂.hom y
      (OrderDual.toDual (⟨(Opens.map f).obj U, hU⟩ : TopologicalSpace.OpenNhds y)) _) ?_
    exact congrArg (KaehlerDifferential.D _ _) (stalkRingMapAlong_germ f ψ y U hU s₀).symm
  have hTbij := Stacks.KaehlerDifferentialSquare.bijective_of_map_D
    (T := fun ω => e₂ (stalkOmegaMapPushₛₗ f ψ y R R₂ a₁ a₂ ρ ha (e₁.symm ω)))
    (stalkRingMapAlong_comp_structureMapPush f ψ y R R₂ a₁ a₂ ρ ha)
    hρ hbij hadd hsmul hT
  exact (EquivLike.bijective_comp e₁.symm _).1 ((EquivLike.comp_bijective _ e₂).1 hTbij)

section Tensor

variable (hψ : ψ ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} f).map φ₂ =
    φ₁ ≫ (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app B)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ₁.hom]
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y) φ₂.hom]

include hψ ha in
/-- **The comparison of the scalar extensions of the differentials along `f` over a changed
base**, in untransposed form: `f⁻¹(B ⊗[A₁] Ω[A₁/R]) ⟶ f⁻¹B ⊗[A₂] Ω[A₂/R₂]`. -/
noncomputable def inverseImageTensorMapPush :
    (_root_.SheafOfModules.pullback.{u} (inverseImageRingHom f B)).obj
        (tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology X) R A₁ B a₁ φ₁) ⟶
      tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology Y) R₂ A₂
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) a₂ φ₂ :=
  ((inverseImageAdjunction f B).homEquiv _ _).symm
    (tensorSheafMapPush f B ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app B)
      φ₁ φ₂ ψ hψ R R₂ a₁ a₂ ρ ha)

include hψ ha in
/-- The comparison on stalks, on germs of sections of the tensor presheaf. -/
theorem stalkMap_inverseImageTensorMapPush_germ
    (U : Opens X) (hU : f y ∈ U) (t : (tensorPresheaf φ₁.hom a₁.hom).obj (op U)) :
    (AlgebraicGeometry.SheafOfModules.stalkMap
          (underlyingRingSheaf.{u, u} ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)) y
          (inverseImageTensorMapPush f B φ₁ φ₂ ψ R R₂ a₁ a₂ ρ ha hψ)).hom
        (Stacks.InverseImageStalk.inverseImageModuleStalkEquiv f B y
          (tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology X) R A₁ B a₁ φ₁)
          ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            (tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology X) R A₁ B a₁
              φ₁).val.presheaf U (f y) hU).hom
            (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology X) A₁ B φ₁
              (tensorPresheaf φ₁.hom a₁.hom) (op U) t))) =
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        (tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology Y) R₂ A₂
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) a₂ φ₂).val.presheaf
        ((Opens.map f).obj U) y hU).hom
        (toAssociatedModule.{u, u, u, u} (Opens.grothendieckTopology Y) A₂
          ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) φ₂ (tensorPresheaf φ₂.hom a₂.hom)
          ((Opens.map f).op.obj (op U))
          (tensorMapPushₛₗ f B ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
            ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app B)
            φ₁ φ₂ ψ hψ R R₂ a₁ a₂ ρ ha (op U) t)) := by
  refine Eq.trans (congrArg (AlgebraicGeometry.SheafOfModules.stalkMap
      (underlyingRingSheaf.{u, u} ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)) y
      (inverseImageTensorMapPush f B φ₁ φ₂ ψ R R₂ a₁ a₂ ρ ha hψ)).hom
    (Stacks.InverseImageStalk.inverseImageModuleStalkEquiv_germ f B y
      (tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology X) R A₁ B a₁ φ₁)
      U hU _)) ?_
  refine Eq.trans (AlgebraicGeometry.SheafOfModules.stalkMap_germ
    (underlyingRingSheaf.{u, u} ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)) y
    (inverseImageTensorMapPush f B φ₁ φ₂ ψ R R₂ a₁ a₂ ρ ha hψ) ((Opens.map f).obj U) hU _) ?_
  refine congrArg (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
    (tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology Y) R₂ A₂
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) a₂ φ₂).val.presheaf
    ((Opens.map f).obj U) y hU).hom ?_
  refine Eq.trans (inverseImageAdjunction_homEquiv_symm_val_app_unit f B
    (tensorSheafMapPush f B ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app B)
      φ₁ φ₂ ψ hψ R R₂ a₁ a₂ ρ ha) (op U) _) ?_
  exact tensorSheafMapPush_toAssociatedModule f B _ _ φ₁ φ₂ ψ hψ R R₂ a₁ a₂ ρ ha (op U) t

include hψ ha in
/-- Under the identifications of the stalks the comparison is the tensor product of the map on
the stalks of the quotients with the map on the stalks of the differentials. -/
theorem tensorDifferentialsSheafStalkPresheafLinearEquiv_stalkMap_inverseImageTensorMapPush
    (ξ : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology X) R A₁ B a₁
        φ₁).val.presheaf (f y))) :
    tensorDifferentialsSheafStalkPresheafLinearEquiv R₂ A₂
        ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) a₂ φ₂ y
        ((AlgebraicGeometry.SheafOfModules.stalkMap
          (underlyingRingSheaf.{u, u} ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)) y
          (inverseImageTensorMapPush f B φ₁ φ₂ ψ R R₂ a₁ a₂ ρ ha hψ)).hom
          (Stacks.InverseImageStalk.inverseImageModuleStalkEquiv f B y
            (tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology X) R A₁ B a₁ φ₁)
            ξ)) =
      TensorProduct.map (stalkQuotientMapAlongₛₗ f B φ₁ φ₂ ψ y hψ)
          (stalkOmegaMapPushₛₗ f ψ y R R₂ a₁ a₂ ρ ha)
        (tensorDifferentialsSheafStalkPresheafLinearEquiv R A₁ B a₁ φ₁ (f y) ξ) := by
  obtain ⟨U, hU, ω, rfl⟩ := exists_germ_one_tmul_eq R A₁ B a₁ φ₁ (f y) ξ
  refine Eq.trans (congrArg (tensorDifferentialsSheafStalkPresheafLinearEquiv R₂ A₂
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) a₂ φ₂ y)
    (stalkMap_inverseImageTensorMapPush_germ f B φ₁ φ₂ ψ y R R₂ a₁ a₂ ρ ha hψ U hU _)) ?_
  refine Eq.trans (tensorDifferentialsSheafStalkPresheafLinearEquiv_germ_toAssociatedModule R₂ A₂
    ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) a₂ φ₂ y ((Opens.map f).obj U) hU _) ?_
  refine Eq.trans (congrArg (germTensorₛₗ φ₂.hom a₂.hom y ((Opens.map f).obj U) hU)
    (TensorProduct.map_tmul (quotientMapPushₛₗ f B ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app B)
        φ₁ φ₂ ψ hψ (op U))
      (differentialsMapPush f ψ R R₂ a₁ a₂ ρ ha (op U)) 1 ω)) ?_
  refine Eq.trans (TensorProduct.map_tmul (germQuotientₛₗ φ₂.hom y ((Opens.map f).obj U) hU)
    (germOmegaₛₗ a₂.hom y ((Opens.map f).obj U) hU) _ _) ?_
  refine Eq.symm (Eq.trans (congrArg (TensorProduct.map
      (stalkQuotientMapAlongₛₗ f B φ₁ φ₂ ψ y hψ) (stalkOmegaMapPushₛₗ f ψ y R R₂ a₁ a₂ ρ ha))
    ((tensorDifferentialsSheafStalkPresheafLinearEquiv_germ_toAssociatedModule R A₁ B a₁ φ₁
      (f y) U hU _).trans
      (TensorProduct.map_tmul (germQuotientₛₗ φ₁.hom (f y) U hU)
        (germOmegaₛₗ a₁.hom (f y) U hU) 1 ω))) ?_)
  refine Eq.trans (TensorProduct.map_tmul (stalkQuotientMapAlongₛₗ f B φ₁ φ₂ ψ y hψ)
    (stalkOmegaMapPushₛₗ f ψ y R R₂ a₁ a₂ ρ ha) _ _) ?_
  exact congrArg₂ (fun (q : ToType (TopCat.Presheaf.stalk A₂.obj y) ⧸ stalkKernelIdeal φ₂.hom y)
      (η : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (differentialsPresheaf a₂.hom).presheaf y)) =>
      q ⊗ₜ[ToType (TopCat.Presheaf.stalk A₂.obj y)] η)
    (stalkQuotientMapAlongₛₗ_germQuotient f B φ₁ φ₂ ψ y hψ U hU 1)
    (stalkOmegaMapPushₛₗ_germ f ψ y R R₂ a₁ a₂ ρ ha U hU ω)

include hψ ha in
/-- The comparison is bijective on the stalk at `y` as soon as the induced maps on the stalks
of `A₁` and `R` at `y` are. -/
theorem bijective_stalkMap_inverseImageTensorMapPush
    (hbij : Function.Bijective (stalkRingMapAlong f ψ y))
    (hρ : Function.Bijective (stalkRingMapAlong f ρ y)) :
    Function.Bijective (AlgebraicGeometry.SheafOfModules.stalkMap
      (underlyingRingSheaf.{u, u} ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B)) y
      (inverseImageTensorMapPush f B φ₁ φ₂ ψ R R₂ a₁ a₂ ρ ha hψ)).hom := by
  have hmap := TensorProduct.bijective_map hbij (stalkQuotientMapAlongₛₗ f B φ₁ φ₂ ψ y hψ)
    (stalkOmegaMapPushₛₗ f ψ y R R₂ a₁ a₂ ρ ha)
    (bijective_stalkQuotientMapAlongₛₗ f B φ₁ φ₂ ψ y hψ hbij)
    (bijective_stalkOmegaMapPushₛₗ f ψ y R R₂ a₁ a₂ ρ ha hbij hρ)
  refine (EquivLike.bijective_comp
    (Stacks.InverseImageStalk.inverseImageModuleStalkEquiv f B y
      (tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology X) R A₁ B a₁ φ₁)) _).1
    ((EquivLike.comp_bijective _ (tensorDifferentialsSheafStalkPresheafLinearEquiv R₂ A₂
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj B) a₂ φ₂ y)).1 ?_)
  exact (congrArg Function.Bijective (funext
    (tensorDifferentialsSheafStalkPresheafLinearEquiv_stalkMap_inverseImageTensorMapPush
      f B φ₁ φ₂ ψ y R R₂ a₁ a₂ ρ ha hψ))).mpr
    (hmap.comp (tensorDifferentialsSheafStalkPresheafLinearEquiv R A₁ B a₁ φ₁ (f y)).bijective)

omit y in
include hψ ha in
/-- **The comparison of the scalar extensions of the differentials along `f` over a changed base
is an isomorphism** as soon as the induced maps on the stalks of `A₁` and of `R` are bijective at
every point of `Y`. -/
theorem isIso_inverseImageTensorMapPush
    (hbij : ∀ w : Y, Function.Bijective (stalkRingMapAlong f ψ w))
    (hρ : ∀ w : Y, Function.Bijective (stalkRingMapAlong f ρ w)) :
    IsIso (inverseImageTensorMapPush f B φ₁ φ₂ ψ R R₂ a₁ a₂ ρ ha hψ) :=
  (AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap
    (inverseImageTensorMapPush f B φ₁ φ₂ ψ R R₂ a₁ a₂ ρ ha hψ)).2
    fun w => bijective_stalkMap_inverseImageTensorMapPush f B φ₁ φ₂ ψ w R R₂ a₁ a₂ ρ ha hψ
      (hbij w) (hρ w)

end Tensor

end Stacks.SheafOfModules
