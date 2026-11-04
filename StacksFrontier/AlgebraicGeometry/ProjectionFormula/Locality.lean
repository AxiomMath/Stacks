module

public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.FiniteFree
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.BaseChange

/-!
# The projection formula when the module on the target is finite locally free

For a morphism of schemes `f : Z ⟶ X`, a module `𝒢` on `Z` and a module `ℋ` on `X`, the
projection-formula map

`Stacks.AffineProjectionFormula.projectionFormulaMap f 𝒢 ℋ : f_*𝒢 ⊗_{𝒪_X} ℋ ⟶ f_*(𝒢 ⊗_{𝒪_Z} f^*ℋ)`

is an isomorphism as soon as `ℋ` is free of finite rank on each member of an open covering of
`X`, with no hypothesis on `𝒢` and none on `f`. This is the case `q = 0` of [Stacks, Tag 01E8].
Finite local freeness is stated as pointwise data: an isomorphism of `ℋ|_V` with the restriction
of `𝒪_X^{⊕ J}` for a finite `J : Type`.

## Main definitions

* `Stacks.AffineProjectionFormula.freeStructureModule`: `𝒪_X^{⊕ J}` for a finite `J`.
* `Stacks.AffineProjectionFormula.openRestrictModule` and `openRestrictHom`: restriction of a
  module, respectively of a morphism of modules, to an open of a scheme, with the codomain
  declared at the `Stacks.RingedSpace.structureRingSheaf` spelling.
* `Stacks.AffineProjectionFormula.pullbackRestrictSquareIso`: the two ways of pulling back
  around the square obtained by restricting a morphism over an open of its target agree.

## Main results

* `Stacks.AffineProjectionFormula.isIso_pullback_projectionFormulaMap_congr`: invertibility of
  the restricted projection-formula map is transported along any morphism of modules on the
  target whose own restriction is invertible.
* `Stacks.AffineProjectionFormula.isIso_openRestrictHom_projectionFormulaMap`: the restriction of
  the projection-formula map to an open on which `ℋ` is free of finite rank is invertible.
* `Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_of_cover_restrict_free` and
  `isIso_projectionFormulaMap_of_restrict_locally_free`: the projection formula for a morphism
  of schemes whenever the module on the target is finite locally free.

## References

* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry
open scoped CategoryTheory.Prod

namespace Stacks.AffineProjectionFormula

universe u

/-! ### Three facts about functors and natural transformations -/

/-- **A component of a natural transformation is invertible exactly when a neighbouring one is**,
provided the two are joined by a morphism whose images under both functors are invertible. -/
theorem isIso_natTrans_app_iff_of_isIso_map {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (β : F ⟶ G) {H H' : C} (k : H ⟶ H')
    (hF : IsIso (F.map k)) (hG : IsIso (G.map k)) :
    IsIso (β.app H) ↔ IsIso (β.app H') := by
  constructor <;> intro h
  · have : IsIso (F.map k ≫ β.app H') := by rw [β.naturality]; infer_instance
    exact IsIso.of_isIso_comp_left (F.map k) _
  · have : IsIso (β.app H ≫ G.map k) := by rw [← β.naturality]; infer_instance
    exact IsIso.of_isIso_comp_right _ (G.map k)

/-- **Naturally isomorphic functors carry the same morphisms to isomorphisms.** -/
theorem isIso_functor_map_of_natIso {C D : Type*} [Category C] [Category D] {P Q : C ⥤ D}
    (θ : P ≅ Q) {H H' : C} (k : H ⟶ H') (h : IsIso (Q.map k)) : IsIso (P.map k) :=
  (NatIso.isIso_map_iff θ k).2 h

/-- **The unit of an adjunction whose counit is invertible becomes invertible under the left
adjoint.** -/
theorem isIso_map_unit_of_isIso_counit {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (A : C)
    (h : IsIso (adj.counit.app (L.obj A))) : IsIso (L.map (adj.unit.app A)) := by
  have h₀ : IsIso (L.map (adj.unit.app A) ≫ adj.counit.app (L.obj A)) := by
    rw [adj.left_triangle_components A]
    exact IsIso.id _
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h h₀

/-! ### Restriction to an open, at the spelling of the projection-formula map -/

/-- The free module `𝒪_X^{⊕ J}` of finite rank on a ringed space. -/
abbrev freeStructureModule (X : AlgebraicGeometry.RingedSpace.{u, u}) (J : Type) [Finite J] :
    SheafOfModules.{u} (structureRingSheaf X) :=
  ⨁ fun _ : J => structureModule X

/-- The restriction of a sheaf of modules on a scheme to an open, with its codomain declared at
the `Stacks.RingedSpace.structureRingSheaf` spelling rather than at
`AlgebraicGeometry.Scheme.Modules`. -/
abbrev openRestrictModule {X : Scheme.{u}} (V : X.Opens)
    (M : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) :
    SheafOfModules.{u} (structureRingSheaf (V : Scheme.{u}).toRingedSpace) :=
  (Scheme.Modules.restrictFunctor V.ι).obj (show X.Modules from M)

/-- The restriction of a morphism of sheaves of modules on a scheme to an open, at the same
spelling. -/
abbrev openRestrictHom {X : Scheme.{u}} (V : X.Opens)
    {M N : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)} (φ : M ⟶ N) :
    openRestrictModule V M ⟶ openRestrictModule V N :=
  (Scheme.Modules.restrictFunctor V.ι).map
    (show (show X.Modules from M) ⟶ (show X.Modules from N) from φ)

/-- The direct image along the inclusion of an open of the restriction of a module to that open,
at the same spelling. -/
abbrev openRestrictPushforwardModule {X : Scheme.{u}} (V : X.Opens)
    (M : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) :
    SheafOfModules.{u} (structureRingSheaf X.toRingedSpace) :=
  (Scheme.Modules.pushforward V.ι).obj (openRestrictModule V M)

/-- The unit of the restriction adjunction at an open, at the same spelling: the canonical
morphism from a module to the direct image of its restriction. -/
abbrev openRestrictUnit {X : Scheme.{u}} (V : X.Opens)
    (M : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) :
    M ⟶ openRestrictPushforwardModule V M :=
  show _ ⟶ _ from
    (Scheme.Modules.restrictAdjunction V.ι).unit.app (show X.Modules from M)

/-- **Restriction to an open and inverse image along its inclusion carry the same morphisms to
isomorphisms.** -/
theorem isIso_openRestrictHom_iff {X : Scheme.{u}} (V : X.Opens)
    {M N : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)} (φ : M ⟶ N) :
    IsIso (openRestrictHom V φ) ↔
      IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map φ) :=
  ⟨fun h => isIso_functor_map_of_natIso
      (Scheme.Modules.restrictFunctorIsoPullback V.ι).symm _ h,
    fun h => isIso_functor_map_of_natIso
      (Scheme.Modules.restrictFunctorIsoPullback V.ι) _ h⟩

/-- **The unit of the restriction adjunction becomes invertible on the open it restricts to.** -/
theorem isIso_pullback_openRestrictUnit {X : Scheme.{u}} (V : X.Opens)
    (M : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) :
    IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map (openRestrictUnit V M)) :=
  (isIso_openRestrictHom_iff V (openRestrictUnit V M)).mp
    (isIso_map_unit_of_isIso_counit (Scheme.Modules.restrictAdjunction V.ι)
      (show X.Modules from M) inferInstance)

/-! ### The three geometric transports -/

/-- A morphism is inverted by `F` if it is inverted by `G` and a natural transformation `F ⟶ G` is
invertible at both ends. -/
private theorem isIso_map_of_isIso_natTrans_app {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (β : F ⟶ G) {H H' : C} (k : H ⟶ H') [IsIso (β.app H)] [IsIso (β.app H')]
    (hG : IsIso (G.map k)) : IsIso (F.map k) := by
  have : IsIso (F.map k ≫ β.app H') := by rw [β.naturality]; infer_instance
  exact IsIso.of_isIso_comp_right _ (β.app H')

/-- If the inverse image `j^*k` of a morphism of modules is invertible, then so is
`j^*(A ⊗ k)`. -/
theorem isIso_pullback_tensorSheaf_map {V X : AlgebraicGeometry.RingedSpace.{u, u}} (j : V ⟶ X)
    (A : SheafOfModules.{u} (structureRingSheaf X))
    {H H' : SheafOfModules.{u} (structureRingSheaf X)} (k : H ⟶ H')
    (hk : IsIso ((pullbackFunctor j).map k)) :
    IsIso ((pullbackFunctor j).map ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)).map (𝟙 A ×ₘ k))) := by
  have hc₁ : IsIso ((comparisonNatTrans j).app (A, H)) := comparisonNatTrans_app_isIso j _
  have hc₂ : IsIso ((comparisonNatTrans j).app (A, H')) := comparisonNatTrans_app_isIso j _
  have e : ((pullbackFunctor j).prod (pullbackFunctor j)).map (𝟙 A ×ₘ k) =
      (𝟙 ((pullbackFunctor j).obj A) ×ₘ (pullbackFunctor j).map k) :=
    Prod.ext (CategoryTheory.Functor.map_id _ _) rfl
  have hpair : IsIso (((pullbackFunctor j).prod (pullbackFunctor j)).map (𝟙 A ×ₘ k)) := by
    rw [e]
    exact ((Iso.refl ((pullbackFunctor j).obj A)).prod (@asIso _ _ _ _ _ hk)).isIso_hom
  have hright : IsIso ((((pullbackFunctor j).prod (pullbackFunctor j)) ⋙ (Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨V.presheaf, V.IsSheaf⟩))).map (𝟙 A ×ₘ k)) :=
    @Functor.map_isIso _ _ _ _ _ _ (Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨V.presheaf, V.IsSheaf⟩)) _ hpair
  exact isIso_map_of_isIso_natTrans_app (comparisonNatTrans j) (𝟙 A ×ₘ k) hright

/-- If the inverse image of `m` to `f ⁻¹ᵁ V` is invertible, then so is the inverse image to `V`
of `f_* m`. -/
theorem isIso_pullback_pushforward_map {Z X : Scheme.{u}} (f : Z ⟶ X) (V : X.Opens)
    {M N : Z.Modules} (m : M ⟶ N)
    (hm : IsIso ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).map m)) :
    IsIso ((Scheme.Modules.pullback V.ι).map ((Scheme.Modules.pushforward f).map m)) := by
  have hr : IsIso ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι ⋙
      Scheme.Modules.pushforward (f ∣_ V)).map m) :=
    Functor.map_isIso (Scheme.Modules.pushforward (f ∣_ V)) _
  have hb₁ := AffineBaseChange.isIso_baseChangeNatTrans_restrictSquare f V M
  have hb₂ := AffineBaseChange.isIso_baseChangeNatTrans_restrictSquare f V N
  exact isIso_map_of_isIso_natTrans_app
    (AffinePushforward.baseChangeNatTrans (AffineBaseChange.restrictSquare f V)) m hr

/-- **The two ways of pulling back around the restriction square agree**: restricting to
`f ⁻¹ᵁ V` an inverse image along `f` is the inverse image along `f ∣_ V` of a restriction to `V`.
-/
def pullbackRestrictSquareIso {Z X : Scheme.{u}} (f : Z ⟶ X) (V : X.Opens) :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback (f ⁻¹ᵁ V).ι ≅
      Scheme.Modules.pullback V.ι ⋙ Scheme.Modules.pullback (f ∣_ V) :=
  Scheme.Modules.pullbackComp (f ⁻¹ᵁ V).ι f ≪≫
    Scheme.Modules.pullbackCongr (AffineBaseChange.restrictSquare f V) ≪≫
    (Scheme.Modules.pullbackComp (f ∣_ V) V.ι).symm

/-- If the inverse image of `k` to `V` is invertible, then so is the inverse image to `f ⁻¹ᵁ V`
of `f^* k`. -/
theorem isIso_pullback_pullback_map {Z X : Scheme.{u}} (f : Z ⟶ X) (V : X.Opens)
    {H H' : X.Modules} (k : H ⟶ H')
    (hk : IsIso ((Scheme.Modules.pullback V.ι).map k)) :
    IsIso ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).map ((Scheme.Modules.pullback f).map k)) := by
  have hr : IsIso ((Scheme.Modules.pullback V.ι ⋙ Scheme.Modules.pullback (f ∣_ V)).map k) :=
    Functor.map_isIso (Scheme.Modules.pullback (f ∣_ V)) _
  exact isIso_functor_map_of_natIso (pullbackRestrictSquareIso f V) k hr

/-! ### The two functors of the projection formula, restricted to an open -/

section Functors

variable {Z X : Scheme.{u}} (f : Z ⟶ X) (V : X.Opens)
  (G : SheafOfModules.{u} (structureRingSheaf Z.toRingedSpace))

/-- The source functor `ℋ ↦ f_*𝒢 ⊗ ℋ` of the projection formula, followed by restriction to an
open of the target, carries a morphism restricting to an isomorphism to an isomorphism. -/
theorem isIso_pullback_tensorPushforward_map
    {H H' : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)} (k : H ⟶ H')
    (hk : IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map k)) :
    IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map
      ((tensorPushforwardFunctor f.toLRSHom.toShHom G).map k)) :=
  isIso_pullback_tensorSheaf_map V.ι.toLRSHom.toShHom
    ((pushforwardFunctor f.toLRSHom.toShHom).obj G) k hk

/-- The target functor `ℋ ↦ f_*(𝒢 ⊗ f^*ℋ)` of the projection formula, followed by restriction to
an open of the target, carries a morphism restricting to an isomorphism to an isomorphism. -/
theorem isIso_pullback_pushforwardTensorPullback_map
    {H H' : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)} (k : H ⟶ H')
    (hk : IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map k)) :
    IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map
      ((pushforwardTensorPullbackFunctor f.toLRSHom.toShHom G).map k)) := by
  have hd : IsIso ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).map
      ((Scheme.Modules.pullback f).map k)) :=
    isIso_pullback_pullback_map f V k hk
  have hB := isIso_pullback_tensorSheaf_map (f ⁻¹ᵁ V).ι.toLRSHom.toShHom G
    ((pullbackFunctor f.toLRSHom.toShHom).map k) hd
  exact isIso_pullback_pushforward_map f V _ hB

/-- **Invertibility of the restricted projection-formula map is transported along any morphism of
modules on the target whose own restriction is invertible.** -/
theorem isIso_pullback_projectionFormulaMap_congr
    {H H' : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)} (k : H ⟶ H')
    (hk : IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map k)) :
    IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map
        (projectionFormulaMap f.toLRSHom.toShHom G H)) ↔
      IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map
        (projectionFormulaMap f.toLRSHom.toShHom G H')) :=
  isIso_natTrans_app_iff_of_isIso_map
    (CategoryTheory.Functor.whiskerRight (projectionFormulaNatTrans f.toLRSHom.toShHom G)
      (pullbackFunctor V.ι.toLRSHom.toShHom)) k
    (isIso_pullback_tensorPushforward_map f V G k hk)
    (isIso_pullback_pushforwardTensorPullback_map f V G k hk)

end Functors

/-! ### The projection formula at a finite locally free module -/

section Locality

variable {Z X : Scheme.{u}} (f : Z ⟶ X)
  (G : SheafOfModules.{u} (structureRingSheaf Z.toRingedSpace))
  (H : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace))

/-- **The restriction of the projection-formula map to an open on which the module on the target
is free of finite rank is an isomorphism.** -/
theorem isIso_openRestrictHom_projectionFormulaMap (V : X.Opens) (J : Type) [Finite J]
    (e : openRestrictModule V (freeStructureModule X.toRingedSpace J) ≅
      openRestrictModule V H) :
    IsIso (openRestrictHom V (projectionFormulaMap f.toLRSHom.toShHom G H)) := by
  refine (isIso_openRestrictHom_iff V _).mpr ?_
  have c0 : IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map
      (projectionFormulaMap f.toLRSHom.toShHom G (freeStructureModule X.toRingedSpace J))) :=
    @Functor.map_isIso _ _ _ _ _ _ (pullbackFunctor V.ι.toLRSHom.toShHom) _
      (isIso_projectionFormulaMap_biproduct_structureModule f.toLRSHom.toShHom G J)
  have c1 := (isIso_pullback_projectionFormulaMap_congr f V G
    (openRestrictUnit V (freeStructureModule X.toRingedSpace J))
    (isIso_pullback_openRestrictUnit V _)).mp c0
  have hk2 : IsIso ((pullbackFunctor V.ι.toLRSHom.toShHom).map
      (show openRestrictPushforwardModule V (freeStructureModule X.toRingedSpace J) ⟶
        openRestrictPushforwardModule V H from
          (Scheme.Modules.pushforward V.ι).map e.hom)) := by
    have : IsIso (show openRestrictPushforwardModule V
        (freeStructureModule X.toRingedSpace J) ⟶ openRestrictPushforwardModule V H from
          (Scheme.Modules.pushforward V.ι).map e.hom) :=
      ((Scheme.Modules.pushforward V.ι).mapIso e).isIso_hom
    exact Functor.map_isIso (pullbackFunctor V.ι.toLRSHom.toShHom) _
  have c2 := (isIso_pullback_projectionFormulaMap_congr f V G _ hk2).mp c1
  exact (isIso_pullback_projectionFormulaMap_congr f V G (openRestrictUnit V H)
    (isIso_pullback_openRestrictUnit V H)).mpr c2

/-- **The projection formula for a morphism of schemes at a module on the target which is free of
finite rank on each member of an open covering**: the canonical map
`f_*𝒢 ⊗_{𝒪_X} ℋ ⟶ f_*(𝒢 ⊗_{𝒪_Z} f^*ℋ)` is an isomorphism, with no hypothesis on `𝒢` and none on
`f`. -/
theorem isIso_projectionFormulaMap_of_cover_restrict_free
    {I : Type*} (U : I → X.Opens) (hU : IsOpenCover U)
    (J : I → Type) [∀ i, Finite (J i)]
    (e : ∀ i, openRestrictModule (U i) (freeStructureModule X.toRingedSpace (J i)) ≅
      openRestrictModule (U i) H) :
    IsIso (projectionFormulaMap f.toLRSHom.toShHom G H) :=
  AffineBaseChange.isIso_of_isIso_restrict
    (show (show X.Modules from _) ⟶ (show X.Modules from _) from
      projectionFormulaMap f.toLRSHom.toShHom G H)
    U hU fun i => isIso_openRestrictHom_projectionFormulaMap f G H (U i) (J i) (e i)

/-- **The projection formula for a morphism of schemes at a finite locally free module on the
target**, from the pointwise data: an open neighbourhood of each point on which the module is
isomorphic to the restriction of `𝒪_X^{⊕ J}` for a finite `J`. -/
theorem isIso_projectionFormulaMap_of_restrict_locally_free
    (J : X.carrier → Type) [∀ x, Finite (J x)]
    (V : X.carrier → X.Opens) (hx : ∀ x, x ∈ V x)
    (e : ∀ x, openRestrictModule (V x) (freeStructureModule X.toRingedSpace (J x)) ≅
      openRestrictModule (V x) H) :
    IsIso (projectionFormulaMap f.toLRSHom.toShHom G H) := by
  refine isIso_projectionFormulaMap_of_cover_restrict_free f G H V (IsOpenCover.mk ?_) J e
  exact eq_top_iff.2 fun x _ => Opens.mem_iSup.mpr ⟨x, hx x⟩

end Locality

end Stacks.AffineProjectionFormula

end
