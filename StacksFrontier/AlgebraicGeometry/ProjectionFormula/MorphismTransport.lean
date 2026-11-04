module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaAdjunctionTranspose
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.Locality

/-!
# Transporting the projection formula along the morphism

For a morphism of ringed spaces `f`, the projection-formula map
`Stacks.AffineProjectionFormula.projectionFormulaMap f 𝒢 ℋ : f_*𝒢 ⊗ ℋ ⟶ f_*(𝒢 ⊗ f^*ℋ)` is an
instance of `CategoryTheory.adjunctionTensorMap`. This file proves that the canonical map of a
composite of adjunctions factors as
`α^{g∘f}_{𝒢, ℋ} = α^f_{g_*𝒢, ℋ} ≫ f_*(α^g_{𝒢, f^*ℋ})`, that the inverse image of the
projection-formula map of an open immersion to the open is an isomorphism, that invertibility of
the projection-formula map restricted to an open `V` of the target depends on the module on the
source only through its restriction to `f ⁻¹ᵁ V`, and it reduces the composite maps for the two
factorisations `f ⁻¹ᵁ V → Z → X` and `f ⁻¹ᵁ V → V → X` to the projection-formula maps of `f`
and of `f ∣_ V`.

## Main definitions

* `Stacks.AffineProjectionFormula.comparisonComp`: the comparison of a composite of two
  adjunctions, built from the two comparisons.
* `Stacks.AffineProjectionFormula.projectionFormulaNatTransLeft`: the projection-formula map as a
  natural transformation in the module on the source.
* `Stacks.AffineProjectionFormula.projectionFormulaMapComp`: the projection-formula map of a
  composite of two morphisms of ringed spaces, at the composite adjunction.

## Main results

* `Stacks.AffineProjectionFormula.isIso_map_adjunctionTensorMap`: the image of the canonical map
  under the left adjoint is invertible as soon as the comparison and the counit are.
* `Stacks.AffineProjectionFormula.adjunctionTensorMap_comp`: the canonical map of a composite of
  adjunctions is the outer map followed by the outer right adjoint of the inner map.
* `Stacks.AffineProjectionFormula.isIso_adjunctionTensorMap_comp_iff`: the resulting
  two-out-of-three.
* `Stacks.AffineProjectionFormula.pushforwardFunctor_comp`: the direct image of sheaves of
  modules on ringed spaces is strictly functorial.
* `Stacks.AffineProjectionFormula.isIso_pullback_projectionFormulaMap_restrict`: the restriction
  to an open of the target of the projection-formula map of that open's inclusion is an
  isomorphism.
* `Stacks.AffineProjectionFormula.isIso_pullback_projectionFormulaMap_congr_left`: invertibility
  of the restricted projection-formula map is transported along a morphism of modules on the
  source that is invertible over `f ⁻¹ᵁ V`.
* `Stacks.AffineProjectionFormula.isIso_pullback_projectionFormulaMap_iff_pushforward_restrict`:
  invertibility of the restricted projection-formula map depends on the module on the source only
  through its restriction to `f ⁻¹ᵁ V`.
* `Stacks.AffineProjectionFormula.isIso_pullback_projectionFormulaMapComp_source_iff` and
  `Stacks.AffineProjectionFormula.isIso_pullback_projectionFormulaMapComp_open_iff`: the composite
  maps for the two factorisations, reduced to the projection-formula maps of `f` and of `f ∣_ V`.
* `Stacks.AffineProjectionFormula.isIso_pullback_projectionFormulaMap_iff_comp_source`: the
  restricted projection-formula map of `f` at any module, read at the factorisation through the
  source.

## References

* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry
open scoped CategoryTheory.Prod

namespace Stacks.AffineProjectionFormula

universe u

/-! ### The canonical map under the left adjoint -/

section Counit

variable {C : Type*} {D : Type*} [Category C] [Category D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- **The image of the canonical map under the left adjoint is invertible as soon as the
comparison and the two relevant components of the counit are.** -/
theorem isIso_map_adjunctionTensorMap (G : D) (H : C)
    (hα : IsIso (α.app (R.obj G, H))) (hε : IsIso (adj.counit.app G))
    (hεB : IsIso (adj.counit.app (B.obj (G, L.obj H)))) :
    IsIso (L.map (adjunctionTensorMap adj A B α G H)) := by
  have : IsIso (adj.counit.app G ×ₘ 𝟙 (L.obj H)) :=
    ((asIso (adj.counit.app G)).prod (Iso.refl (L.obj H))).isIso_hom
  rw [← isIso_comp_right_iff _ (adj.counit.app (B.obj (G, L.obj H))),
    CategoryTheory.map_adjunctionTensorMap_comp_counit]
  infer_instance

/-- **A morphism carried by the right and then the left adjoint is invertible exactly when it is
invertible**, provided the two relevant components of the counit are. -/
theorem isIso_map_map_iff_of_isIso_counit {Y Y' : D} (φ : Y ⟶ Y')
    (hY : IsIso (adj.counit.app Y)) (hY' : IsIso (adj.counit.app Y')) :
    IsIso (L.map (R.map φ)) ↔ IsIso φ := by
  rw [← isIso_comp_right_iff _ (adj.counit.app Y'), adj.counit_naturality φ,
    isIso_comp_left_iff]

end Counit

/-! ### The canonical map of a composite of adjunctions -/

section Comp

variable {C : Type*} {D : Type*} {E : Type*} [Category C] [Category D] [Category E]

/-- **The comparison of a composite of two adjunctions**, built from the comparison of each:
the image under the inner left adjoint of the outer comparison, followed by the inner comparison
at the outer inverse images. -/
def comparisonComp {L₁ : C ⥤ D} {L₂ : D ⥤ E} {A : C × C ⥤ C} {B : D × D ⥤ D} {K : E × E ⥤ E}
    (α : A ⋙ L₁ ⟶ L₁.prod L₁ ⋙ B) (β : B ⋙ L₂ ⟶ L₂.prod L₂ ⋙ K) :
    A ⋙ (L₁ ⋙ L₂) ⟶ (L₁ ⋙ L₂).prod (L₁ ⋙ L₂) ⋙ K where
  app P := L₂.map (α.app P) ≫ β.app (L₁.obj P.1, L₁.obj P.2)
  naturality := by
    intro P Q u
    have ha := α.naturality u
    have hb := β.naturality (L₁.map u.1 ×ₘ L₁.map u.2)
    simp only [Functor.comp_map, Functor.prod_map] at ha hb ⊢
    rw [← Category.assoc, ← L₂.map_comp, ha, L₂.map_comp, Category.assoc, hb,
      ← Category.assoc]

/-- The components of `comparisonComp`. -/
@[simp]
lemma comparisonComp_app {L₁ : C ⥤ D} {L₂ : D ⥤ E} {A : C × C ⥤ C} {B : D × D ⥤ D}
    {K : E × E ⥤ E} (α : A ⋙ L₁ ⟶ L₁.prod L₁ ⋙ B) (β : B ⋙ L₂ ⟶ L₂.prod L₂ ⋙ K)
    (P : C × C) :
    (comparisonComp α β).app P = L₂.map (α.app P) ≫ β.app (L₁.obj P.1, L₁.obj P.2) :=
  rfl

variable {L₁ : C ⥤ D} {R₁ : D ⥤ C} (adj₁ : L₁ ⊣ R₁)
  {L₂ : D ⥤ E} {R₂ : E ⥤ D} (adj₂ : L₂ ⊣ R₂)
  {A : C × C ⥤ C} {B : D × D ⥤ D} {K : E × E ⥤ E}
  (α : A ⋙ L₁ ⟶ L₁.prod L₁ ⋙ B) (β : B ⋙ L₂ ⟶ L₂.prod L₂ ⋙ K)

/-- **The canonical map of a composite of adjunctions factors**: it is the map of the outer
adjunction at the inner direct image, followed by the outer right adjoint applied to the map of
the inner adjunction.  For the projection formula this reads
`α^{g∘f}_{𝒢,ℋ} = α^f_{g_*𝒢,ℋ} ≫ f_*(α^g_{𝒢,f^*ℋ})`. -/
lemma adjunctionTensorMap_comp (G : E) (H : C) :
    adjunctionTensorMap (adj₁.comp adj₂) A K (comparisonComp α β) G H =
      adjunctionTensorMap adj₁ A B α (R₂.obj G) H ≫
        R₁.map (adjunctionTensorMap adj₂ B K β G (L₁.obj H)) := by
  rw [adjunctionTensorMap, adjunctionTensorMap, adjunctionTensorMap,
    ← Adjunction.homEquiv_naturality_right, Adjunction.comp_homEquiv]
  dsimp only
  rw [← Adjunction.homEquiv_naturality_left]
  simp only [Equiv.trans_apply]
  refine congrArg _ (congrArg _ ?_)
  dsimp only [comparisonComp]
  have hb := β.naturality (adj₁.counit.app (R₂.obj G) ×ₘ 𝟙 (L₁.obj H))
  simp only [Functor.comp_map, Functor.prod_map, CategoryTheory.Functor.map_id,
    Functor.comp_obj, Functor.id_obj] at hb ⊢
  have hsplit : ((adj₁.comp adj₂).counit.app G ×ₘ 𝟙 (L₂.obj (L₁.obj H))) =
      (L₂.map (adj₁.counit.app (R₂.obj G)) ×ₘ 𝟙 (L₂.obj (L₁.obj H))) ≫
        (adj₂.counit.app G ×ₘ 𝟙 (L₂.obj (L₁.obj H))) :=
    Prod.ext (by simp) (by simp)
  rw [hsplit, K.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    ← Category.assoc (β.app (L₁.obj (R₁.obj (R₂.obj G)), L₁.obj H)), ← hb]
  simp only [Category.assoc]

/-- **The morphism-side two-out-of-three.**  Given that the outer right adjoint carries the map
of the inner adjunction to an isomorphism, the map of the composite adjunction is invertible
exactly when the map of the outer adjunction at the inner direct image is. -/
theorem isIso_adjunctionTensorMap_comp_iff (G : E) (H : C)
    (h : IsIso (R₁.map (adjunctionTensorMap adj₂ B K β G (L₁.obj H)))) :
    IsIso (adjunctionTensorMap (adj₁.comp adj₂) A K (comparisonComp α β) G H) ↔
      IsIso (adjunctionTensorMap adj₁ A B α (R₂.obj G) H) := by
  rw [adjunctionTensorMap_comp, isIso_comp_right_iff]

end Comp

/-! ### Strict functoriality of the direct image -/

/-- **The direct image of sheaves of modules along a morphism of ringed spaces is strictly
functorial.** -/
lemma pushforwardFunctor_comp {W Z X : AlgebraicGeometry.RingedSpace.{u, u}}
    (g : W ⟶ Z) (f : Z ⟶ X) :
    pushforwardFunctor (g ≫ f) = pushforwardFunctor g ⋙ pushforwardFunctor f :=
  rfl

/-- **The two factorisations of a morphism over an open of its target have the same composite
direct image.** -/
lemma pushforwardFunctor_restrictSquare {Z X : Scheme.{u}} (f : Z ⟶ X) (V : X.Opens) :
    pushforwardFunctor (f ⁻¹ᵁ V).ι.toLRSHom.toShHom ⋙
        pushforwardFunctor f.toLRSHom.toShHom =
      pushforwardFunctor (f ∣_ V).toLRSHom.toShHom ⋙
        pushforwardFunctor V.ι.toLRSHom.toShHom := by
  rw [← pushforwardFunctor_comp, ← pushforwardFunctor_comp]
  exact congrArg pushforwardFunctor
    (congrArg (fun h => h.toLRSHom.toShHom) (AffineBaseChange.restrictSquare f V))

/-! ### The projection formula of an open immersion, restricted to the open -/

section OpenImmersion

variable {X : Scheme.{u}} (V : X.Opens)

/-- **The direct image along the inclusion of an open of a scheme is fully faithful**, the counit
of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction` being invertible. -/
def fullyFaithfulPushforwardRestrict : (Scheme.Modules.pushforward V.ι).FullyFaithful :=
  Adjunction.fullyFaithfulROfIsIsoCounit (Scheme.Modules.restrictAdjunction V.ι)

/-- **The counit of `f^* ⊣ f_*` along the inclusion of an open of a scheme is invertible.** -/
theorem isIso_counit_pullbackAdjunction_ι
    (M : SheafOfModules.{u} (structureRingSheaf (V : Scheme.{u}).toRingedSpace)) :
    IsIso ((pullbackAdjunction V.ι.toLRSHom.toShHom).counit.app M) := by
  have h := fullyFaithfulPushforwardRestrict V
  have : (pushforwardFunctor V.ι.toLRSHom.toShHom).Full := h.full
  have : (pushforwardFunctor V.ι.toLRSHom.toShHom).Faithful := h.faithful
  exact isIso_counit_app (pullbackAdjunction V.ι.toLRSHom.toShHom) M

/-- **The inverse image of the projection-formula map of a morphism along that same morphism is
invertible whenever the two relevant components of the counit of `f^* ⊣ f_*` are.** -/
theorem isIso_pullback_projectionFormulaMap_of_isIso_counit
    {Z Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : Z ⟶ Y)
    (G : SheafOfModules.{u} (structureRingSheaf Z))
    (H : SheafOfModules.{u} (structureRingSheaf Y))
    (hG : IsIso ((pullbackAdjunction f).counit.app G))
    (hT : IsIso ((pullbackAdjunction f).counit.app
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.presheaf, Z.IsSheaf⟩)).obj
        (G, (pullbackFunctor f).obj H)))) :
    IsIso ((pullbackFunctor f).map (projectionFormulaMap f G H)) :=
  isIso_map_adjunctionTensorMap (pullbackAdjunction f)
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.presheaf, Y.IsSheaf⟩))
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.presheaf, Z.IsSheaf⟩))
    (comparisonNatTrans f) G H (comparisonNatTrans_app_isIso f _) hG hT

/-- **The restriction to an open of a scheme of the projection-formula map of that open's
inclusion is an isomorphism**, for arbitrary sheaves of modules. -/
theorem isIso_pullback_projectionFormulaMap_restrict
    (N : SheafOfModules.{u} (structureRingSheaf (V : Scheme.{u}).toRingedSpace))
    (H : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) :
    IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map
      (projectionFormulaMap V.ι.toLRSHom.toShHom N H)) :=
  isIso_pullback_projectionFormulaMap_of_isIso_counit V.ι.toLRSHom.toShHom N H
    (isIso_counit_pullbackAdjunction_ι V N)
    (isIso_counit_pullbackAdjunction_ι V _)

end OpenImmersion

/-! ### Transporting along a morphism of the module upstairs -/

section Left

/-- If `j^*k` is invertible then so is `j^*(k ⊗ A)`. -/
theorem isIso_pullback_tensorSheaf_map_left
    {V X : AlgebraicGeometry.RingedSpace.{u, u}} (j : V ⟶ X)
    (A : SheafOfModules.{u} (structureRingSheaf X))
    {H H' : SheafOfModules.{u} (structureRingSheaf X)} (k : H ⟶ H')
    (hk : IsIso ((pullbackFunctor j).map k)) :
    IsIso ((pullbackFunctor j).map
      ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)).map (k ×ₘ 𝟙 A))) := by
  have hnat := (comparisonNatTrans j).naturality (k ×ₘ 𝟙 A)
  have hc1 : IsIso ((comparisonNatTrans j).app (H, A)) := comparisonNatTrans_app_isIso j _
  have hc2 : IsIso ((comparisonNatTrans j).app (H', A)) := comparisonNatTrans_app_isIso j _
  have e : ((pullbackFunctor j).prod (pullbackFunctor j)).map (k ×ₘ 𝟙 A) =
      ((pullbackFunctor j).map k ×ₘ 𝟙 ((pullbackFunctor j).obj A)) :=
    Prod.ext rfl (CategoryTheory.Functor.map_id _ _)
  have hpair : IsIso (((pullbackFunctor j).prod (pullbackFunctor j)).map (k ×ₘ 𝟙 A)) := by
    rw [e]
    exact ((@asIso _ _ _ _ _ hk).prod (Iso.refl ((pullbackFunctor j).obj A))).isIso_hom
  have hright : IsIso ((((pullbackFunctor j).prod (pullbackFunctor j)) ⋙
      (Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨V.presheaf, V.IsSheaf⟩))).map (k ×ₘ 𝟙 A)) :=
    @Functor.map_isIso _ _ _ _ _ _
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨V.presheaf, V.IsSheaf⟩))
      _ hpair
  have hcomp : IsIso (((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)) ⋙
        pullbackFunctor j).map (k ×ₘ 𝟙 A) ≫ (comparisonNatTrans j).app (H', A)) := by
    rw [hnat]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hc1 hright
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hc2 hcomp

variable {Z X : AlgebraicGeometry.RingedSpace.{u, u}} (f : Z ⟶ X)
  (H : SheafOfModules.{u} (structureRingSheaf X))

/-- The source of the projection-formula map as a functor of the module on the source,
`𝒢 ↦ f_*𝒢 ⊗ ℋ`. -/
abbrev tensorPushforwardFunctorLeft :
    SheafOfModules.{u} (structureRingSheaf Z) ⥤ SheafOfModules.{u} (structureRingSheaf X) :=
  pushforwardFunctor f ⋙ (Prod.sectL (SheafOfModules.{u} (structureRingSheaf X)) H ⋙
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)))

/-- The target of the projection-formula map as a functor of the module on the source,
`𝒢 ↦ f_*(𝒢 ⊗ f^*ℋ)`. -/
abbrev pushforwardTensorPullbackFunctorLeft :
    SheafOfModules.{u} (structureRingSheaf Z) ⥤ SheafOfModules.{u} (structureRingSheaf X) :=
  (Prod.sectL (SheafOfModules.{u} (structureRingSheaf Z)) ((pullbackFunctor f).obj H) ⋙
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.presheaf, Z.IsSheaf⟩))) ⋙
    pushforwardFunctor f

/-- **The projection-formula map as a natural transformation in the module on the source.** -/
def projectionFormulaNatTransLeft :
    tensorPushforwardFunctorLeft f H ⟶ pushforwardTensorPullbackFunctorLeft f H where
  app G := projectionFormulaMap f G H
  naturality G G' g := by
    have h := projectionFormulaMap_natural f g (𝟙 H)
    rwa [CategoryTheory.Functor.map_id] at h

/-- The components of `projectionFormulaNatTransLeft` are the projection-formula maps. -/
@[simp]
lemma projectionFormulaNatTransLeft_app (G : SheafOfModules.{u} (structureRingSheaf Z)) :
    (projectionFormulaNatTransLeft f H).app G = projectionFormulaMap f G H :=
  rfl

end Left

/-! ### The transport, for a morphism of schemes -/

section LeftScheme

variable {Z X : Scheme.{u}} (f : Z ⟶ X) (V : X.Opens)
  (H : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace))

/-- The source functor `𝒢 ↦ f_*𝒢 ⊗ ℋ` of the projection formula, followed by restriction to an
open of the target, carries a morphism restricting to an isomorphism over `f ⁻¹ᵁ V` to an
isomorphism. -/
theorem isIso_pullback_tensorPushforward_map_left
    {G G' : SheafOfModules.{u} (structureRingSheaf Z.toRingedSpace)} (g : G ⟶ G')
    (hg : IsIso ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).map
      (show (show Z.Modules from G) ⟶ (show Z.Modules from G') from g))) :
    IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map
      ((tensorPushforwardFunctorLeft f.toLRSHom.toShHom H).map g)) := by
  have hp : IsIso ((Scheme.Modules.pullback V.ι).map ((Scheme.Modules.pushforward f).map
      (show (show Z.Modules from G) ⟶ (show Z.Modules from G') from g))) :=
    isIso_pullback_pushforward_map f V _ hg
  exact isIso_pullback_tensorSheaf_map_left V.ι.toLRSHom.toShHom H
    ((pushforwardFunctor f.toLRSHom.toShHom).map g) hp

/-- The target functor `𝒢 ↦ f_*(𝒢 ⊗ f^*ℋ)` of the projection formula, followed by restriction to
an open of the target, carries a morphism restricting to an isomorphism over `f ⁻¹ᵁ V` to an
isomorphism. -/
theorem isIso_pullback_pushforwardTensorPullback_map_left
    {G G' : SheafOfModules.{u} (structureRingSheaf Z.toRingedSpace)} (g : G ⟶ G')
    (hg : IsIso ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).map
      (show (show Z.Modules from G) ⟶ (show Z.Modules from G') from g))) :
    IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map
      ((pushforwardTensorPullbackFunctorLeft f.toLRSHom.toShHom H).map g)) := by
  have hT := isIso_pullback_tensorSheaf_map_left (f ⁻¹ᵁ V).ι.toLRSHom.toShHom
    ((pullbackFunctor f.toLRSHom.toShHom).obj H) g hg
  exact isIso_pullback_pushforward_map f V _ hT

/-- **Invertibility of the restricted projection-formula map is transported along any morphism of
modules on the source whose restriction to `f ⁻¹ᵁ V` is invertible.** -/
theorem isIso_pullback_projectionFormulaMap_congr_left
    {G G' : SheafOfModules.{u} (structureRingSheaf Z.toRingedSpace)} (g : G ⟶ G')
    (hg : IsIso ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).map
      (show (show Z.Modules from G) ⟶ (show Z.Modules from G') from g))) :
    IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map
        (projectionFormulaMap f.toLRSHom.toShHom G H)) ↔
      IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map
        (projectionFormulaMap f.toLRSHom.toShHom G' H)) :=
  isIso_natTrans_app_iff_of_isIso_map
    (CategoryTheory.Functor.whiskerRight
      (projectionFormulaNatTransLeft f.toLRSHom.toShHom H)
      (pullbackFunctor V.ι.toLRSHom.toShHom)) g
    (isIso_pullback_tensorPushforward_map_left f V H g hg)
    (isIso_pullback_pushforwardTensorPullback_map_left f V H g hg)

/-- **Invertibility of the restricted projection-formula map depends on the module on the source
only through its restriction to `f ⁻¹ᵁ V`.** -/
theorem isIso_pullback_projectionFormulaMap_iff_pushforward_restrict
    (G : SheafOfModules.{u} (structureRingSheaf Z.toRingedSpace)) :
    IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map
        (projectionFormulaMap f.toLRSHom.toShHom G H)) ↔
      IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map
        (projectionFormulaMap f.toLRSHom.toShHom
          (openRestrictPushforwardModule (f ⁻¹ᵁ V) G) H)) :=
  isIso_pullback_projectionFormulaMap_congr_left f V H
    (openRestrictUnit (f ⁻¹ᵁ V) G) (isIso_pullback_openRestrictUnit (f ⁻¹ᵁ V) G)

end LeftScheme

/-! ### The projection-formula map of a composite of morphisms -/

section CompGeometric

variable {W Z X : AlgebraicGeometry.RingedSpace.{u, u}} (f : Z ⟶ X) (g : W ⟶ Z)
  (G : SheafOfModules.{u} (structureRingSheaf W))
  (H : SheafOfModules.{u} (structureRingSheaf X))

/-- **The projection-formula map of a composite of two morphisms of ringed spaces**, formed with
respect to the composite of the two adjunctions and the comparison `comparisonComp` of the two
pullback tensor comparisons. -/
abbrev projectionFormulaMapComp :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)).obj
        ((pushforwardFunctor g ⋙ pushforwardFunctor f).obj G, H) ⟶
      (pushforwardFunctor g ⋙ pushforwardFunctor f).obj
        ((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor ⟨W.presheaf, W.IsSheaf⟩)).obj
          (G, (pullbackFunctor f ⋙ pullbackFunctor g).obj H)) :=
  adjunctionTensorMap ((pullbackAdjunction f).comp (pullbackAdjunction g))
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩))
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨W.presheaf, W.IsSheaf⟩))
    (comparisonComp (comparisonNatTrans f) (comparisonNatTrans g)) G H

/-- **The projection-formula map of a composite factors**: the map of the outer morphism at the
inner direct image, followed by the outer direct image of the map of the inner morphism. -/
lemma projectionFormulaMapComp_eq :
    projectionFormulaMapComp f g G H =
      projectionFormulaMap f ((pushforwardFunctor g).obj G) H ≫
        (pushforwardFunctor f).map
          (projectionFormulaMap g G ((pullbackFunctor f).obj H)) :=
  adjunctionTensorMap_comp (pullbackAdjunction f) (pullbackAdjunction g)
    (comparisonNatTrans f) (comparisonNatTrans g) G H

end CompGeometric

/-! ### The two factorisations of a morphism over an open of its target -/

/-- If `c = a ≫ b` and `F b` is invertible, then `F c` is invertible exactly when `F a` is. -/
private theorem isIso_map_iff_of_eq_comp {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {x y z : C} {c : x ⟶ z} {a : x ⟶ y} {b : y ⟶ z} (h : c = a ≫ b) (hb : IsIso (F.map b)) :
    IsIso (F.map c) ↔ IsIso (F.map a) := by
  rw [h, F.map_comp, isIso_comp_right_iff _ (F.map b)]

/-- If `c = a ≫ b` and `F a` is invertible, then `F c` is invertible exactly when `F b` is. -/
private theorem isIso_map_iff_of_eq_comp' {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {x y z : C} {c : x ⟶ z} {a : x ⟶ y} {b : y ⟶ z} (h : c = a ≫ b) (ha : IsIso (F.map a)) :
    IsIso (F.map c) ↔ IsIso (F.map b) := by
  rw [h, F.map_comp, isIso_comp_left_iff (F.map a)]

section Factorisations

variable {Z X : Scheme.{u}} (f : Z ⟶ X) (V : X.Opens)
  (N : SheafOfModules.{u} (structureRingSheaf (f ⁻¹ᵁ V : Scheme.{u}).toRingedSpace))
  (H : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace))

/-- **Factorisation through the source.**  For the factorisation `f ⁻¹ᵁ V → Z → X` of the
inclusion of the preimage followed by `f`, the restriction to `V` of the composite
projection-formula map is invertible exactly when the restriction to `V` of the
projection-formula map of `f` at the direct image is. -/
theorem isIso_pullback_projectionFormulaMapComp_source_iff :
    IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map
        (projectionFormulaMapComp f.toLRSHom.toShHom (f ⁻¹ᵁ V).ι.toLRSHom.toShHom N H)) ↔
      IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map
        (projectionFormulaMap f.toLRSHom.toShHom
          ((pushforwardFunctor (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj N) H)) := by
  have hinner : IsIso ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).map
      (show (show Z.Modules from _) ⟶ (show Z.Modules from _) from
        projectionFormulaMap (f ⁻¹ᵁ V).ι.toLRSHom.toShHom N
          ((pullbackFunctor f.toLRSHom.toShHom).obj H))) :=
    isIso_pullback_projectionFormulaMap_restrict (f ⁻¹ᵁ V) N
      ((pullbackFunctor f.toLRSHom.toShHom).obj H)
  have h2 : IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map
      ((pushforwardFunctor f.toLRSHom.toShHom).map
        (projectionFormulaMap (f ⁻¹ᵁ V).ι.toLRSHom.toShHom N
          ((pullbackFunctor f.toLRSHom.toShHom).obj H)))) :=
    isIso_pullback_pushforward_map f V _ hinner
  exact isIso_map_iff_of_eq_comp _ (projectionFormulaMapComp_eq f.toLRSHom.toShHom
    (f ⁻¹ᵁ V).ι.toLRSHom.toShHom N H) h2

/-- **Factorisation through the open.**  For the factorisation `f ⁻¹ᵁ V → V → X` of `f ∣_ V`
followed by the inclusion of `V`, the restriction to `V` of the composite projection-formula map
is invertible exactly when the projection-formula map of `f ∣_ V` is. -/
theorem isIso_pullback_projectionFormulaMapComp_open_iff :
    IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map
        (projectionFormulaMapComp V.ι.toLRSHom.toShHom (f ∣_ V).toLRSHom.toShHom N H)) ↔
      IsIso (projectionFormulaMap (f ∣_ V).toLRSHom.toShHom N
        ((pullbackFunctor V.ι.toLRSHom.toShHom).obj H)) := by
  have h1 : IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map
      (projectionFormulaMap V.ι.toLRSHom.toShHom
        ((pushforwardFunctor (f ∣_ V).toLRSHom.toShHom).obj N) H)) :=
    isIso_pullback_projectionFormulaMap_restrict V _ H
  refine (isIso_map_iff_of_eq_comp' _ (projectionFormulaMapComp_eq V.ι.toLRSHom.toShHom
    (f ∣_ V).toLRSHom.toShHom N H) h1).trans ?_
  exact isIso_map_map_iff_of_isIso_counit
    (pullbackAdjunction V.ι.toLRSHom.toShHom)
    (projectionFormulaMap (f ∣_ V).toLRSHom.toShHom N
      ((pullbackFunctor V.ι.toLRSHom.toShHom).obj H))
    (isIso_counit_pullbackAdjunction_ι V _) (isIso_counit_pullbackAdjunction_ι V _)

/-- **The restricted projection-formula map of `f`, read at the factorisation through the
source.**  Invertibility over `V` of the projection-formula map of `f` at an arbitrary module
upstairs is invertibility over `V` of the composite map for the factorisation
`f ⁻¹ᵁ V → Z → X` at its restriction. -/
theorem isIso_pullback_projectionFormulaMap_iff_comp_source
    (G : SheafOfModules.{u} (structureRingSheaf Z.toRingedSpace)) :
    IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map
        (projectionFormulaMap f.toLRSHom.toShHom G H)) ↔
      IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map
        (projectionFormulaMapComp f.toLRSHom.toShHom (f ⁻¹ᵁ V).ι.toLRSHom.toShHom
          (openRestrictModule (f ⁻¹ᵁ V) G) H)) :=
  (isIso_pullback_projectionFormulaMap_iff_pushforward_restrict f V H G).trans
    (isIso_pullback_projectionFormulaMapComp_source_iff f V
      (openRestrictModule (f ⁻¹ᵁ V) G) H).symm

end Factorisations

end Stacks.AffineProjectionFormula

end
