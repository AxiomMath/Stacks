module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeInverseImageComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafColimits
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.OverPushforwardMate

/-!
# Inverse image preserves the flat base change property of étale sheaves (Stacks 0764, part (1))

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category of
a scheme `S`, and let `F` be an étale sheaf of `𝒪_𝒴`-modules. **Stacks 0764** part (1) says that
if `F` has the flat base change property of **Stacks 0762** then so does the inverse image
`f^*F`. This file proves it in the source's ambient category `Mod(𝒳_étale, 𝒪_𝒳)`: the property
is `AlgebraicGeometry.Stack.HasFlatBaseChangePropertySheafUnivLE`, whose comparison maps are
taken with `a_{small}^*` the inverse image of *sheaves* of modules, and the inverse image along
`f` is the inverse image of sheaves of modules `AlgebraicGeometry.Stack.modulePullback` of
**Stacks 06WE**.

The source's proof is that a comparison map for `f^*F` at an arrow `φ` *is* the comparison map
for `F` at `f φ`. The precise statement proved here,
`AlgebraicGeometry.Stack.isIso_restrictSheafPullbackComparison_modulePullback_iff`, is that the
two are invertible together, for every arrow, with no flatness assumed. Both comparison maps are
transposes of direct-image comparisons of **Stacks 06W2**, across the composite of the
pullback–direct image adjunction along `a_{small}^♯` and the sheafification adjunction of the
small étale site. The square of **Stacks 075D** part (4) at the level of modules,
`AlgebraicGeometry.Stack.restrictModulePushforwardComparison_app_inverseImageIso`, compares the
two direct-image comparisons across the identifications of **Stacks 075D** part (3), so
`CategoryTheory.Adjunction.isIso_homEquiv_symm_iff_of_isoSquare` and
`PresheafOfModules.isIso_homEquiv_symm_iff_of_pushforward_eq_comp` finish the argument exactly
as they do for the presheaf reading in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FlatBaseChangeInverseImage.lean`.

## Main results

* `PresheafOfModules.isIso_homEquiv_symm_iff_of_pushforward_eq_comp`: transposes along two
  adjunctions whose right adjoints are a fixed functor followed by the direct images along two
  equal maps of presheaves of rings are invertible together.
* `AlgebraicGeometry.Stack.restrictSheafPullbackComparison_eq_comp_homEquiv_symm`: the comparison
  map of an étale sheaf of modules is one transpose, across the composite of the pullback–direct
  image adjunction along `a_{small}^♯` and the sheafification adjunction.
* `AlgebraicGeometry.Stack.isIso_restrictSheafPullbackComparison_modulePullback_iff`: the
  comparison map of an inverse image at an arrow is invertible exactly when the comparison map of
  the module at the image arrow is.
* `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_modulePullback`: **Stacks 0764**
  part (1) in the source's ambient category.

## Implementation notes

The 1-morphism is a functor `f : 𝒳 ⥤ 𝒴` with `f ⋙ q = p`, which is how a 1-morphism of
categories fibred in groupoids over `(Sch/S)_{fppf}` is presented throughout (Stacks 06WE and
`AlgebraicGeometry.Stack.modulePullback`); no algebraicity is used, so the statement holds for any
1-morphism of categories fibred in groupoids, which is more general than the source's morphisms
of algebraic stacks.

Four definitions are locally irreducible for the transport theorem, exactly as in the module
`SheafifiedPullbackComparisonRestrictionComposition` of this directory:
`AlgebraicGeometry.smallEtaleBaseChange`, `CategoryTheory.Over.post`,
`AlgebraicGeometry.Stack.baseStructureSheaf` and `AlgebraicGeometry.Stack.baseRingStructureSheaf`.
Without them the unifier, comparing the two spellings `(f ⋙ q).obj x` and `q.obj (f.obj x)` of
the scheme below an object, unfolds the structure sheaf of Stacks 06TV and the base-change
functor into pullback cones and exceeds every heartbeat budget; with them the comparison is
decided on the arguments. No statement depends on the attribute.

## References

* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w v' w' m

namespace PresheafOfModules

variable {C : Type*} [Category C] {D : Type*} [Category D] {F : C ⥤ D}
  {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}

/-- **Transposes along two adjunctions over two equal maps of presheaves of rings are invertible
together**, when the right adjoints are a fixed functor `G` followed by the two direct images.
Two equal maps `φ = ψ : S ⟶ F.op ⋙ R` have equal direct images, so `adj₁` and `adj₂` are two
adjunctions of one functor `G ⋙ pushforward φ`; morphisms agreeing on sections then have
transposes which are invertible together, by
`CategoryTheory.Adjunction.isIso_homEquiv_symm_iff_of_rightAdjointEq`.

This is `PresheafOfModules.isIso_homEquiv_symm_iff_of_pushforward_eq` with the right adjoints
allowed to start from another category, as they do for the comparison maps of sheaves of
modules, whose right adjoints start from sheaves. -/
theorem isIso_homEquiv_symm_iff_of_pushforward_eq_comp {φ ψ : S ⟶ F.op ⋙ R} (hφψ : φ = ψ)
    {D' : Type*} [Category D'] (G : D' ⥤ PresheafOfModules.{m} R)
    {L₁ L₂ : PresheafOfModules.{m} S ⥤ D'}
    (adj₁ : L₁ ⊣ G ⋙ pushforward.{m} φ) (adj₂ : L₂ ⊣ G ⋙ pushforward.{m} ψ)
    {M : PresheafOfModules.{m} S} {N : D'}
    (w : M ⟶ (pushforward.{m} φ).obj (G.obj N)) (w' : M ⟶ (pushforward.{m} ψ).obj (G.obj N))
    (hw : ∀ (X : C) (t : M.obj (Opposite.op X)),
      w.app (Opposite.op X) t = w'.app (Opposite.op X) t) :
    IsIso ((adj₁.homEquiv M N).symm w) ↔ IsIso ((adj₂.homEquiv M N).symm w') := by
  subst hφψ
  obtain rfl : w = w' := by
    refine PresheafOfModules.hom_ext fun X => ?_
    exact ModuleCat.hom_ext (LinearMap.ext (hw X.unop))
  exact Adjunction.isIso_homEquiv_symm_iff_of_rightAdjointEq adj₁ adj₂ w

end PresheafOfModules

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)

/-- `Stacks.CategoryTheory.homEquiv_symm_comp_apply` with the morphism typed into
`G.obj (I.obj Y)` rather than `(I ⋙ G).obj Y`, which is the form in which unification against a
comparison map succeeds. -/
theorem homEquiv_symm_comp_apply_obj {C D E : Type*} [Category C] [Category D]
    [Category E] {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D}
    (adj₁ : F ⊣ G) (adj₂ : H ⊣ I) (X : C) (Y : E) (g : X ⟶ G.obj (I.obj Y)) :
    ((adj₁.comp adj₂).homEquiv X Y).symm g =
      (adj₂.homEquiv (F.obj X) Y).symm ((adj₁.homEquiv X (I.obj Y)).symm g) :=
  Stacks.CategoryTheory.homEquiv_symm_comp_apply adj₁ adj₂ X Y g

/-- `CategoryTheory.Adjunction.isIso_homEquiv_symm_iff_of_isoSquare` with the second morphism
the first one conjugated by the two isomorphisms, so that no square has to be checked. -/
theorem isIso_homEquiv_symm_iff_of_conj {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {X₁ X₂ : C} {Y₁ Y₂ : D} (α : X₁ ≅ X₂)
    (β : Y₁ ≅ Y₂) (u : X₁ ⟶ R.obj Y₁) :
    IsIso ((adj.homEquiv X₁ Y₁).symm u) ↔
      IsIso ((adj.homEquiv X₂ Y₂).symm (α.inv ≫ u ≫ R.map β.hom)) :=
  Adjunction.isIso_homEquiv_symm_iff_of_isoSquare adj α β u _ (by simp)

variable [UnivLE.{u, m}]

/-- **The comparison map of an étale sheaf of modules as one transpose.** The comparison map
`c_φ` of **Stacks 0761**, in the source's reading, is the transpose of the direct-image
comparison of **Stacks 06W2** across the composite of the pullback–direct image adjunction along
`a_{small}^♯` and the sheafification adjunction of the small étale site of the scheme below the
source of `φ`; it is defined as the transpose across the two adjunctions in turn. -/
theorem restrictSheafPullbackComparison_eq_comp_homEquiv_symm {x y : 𝒳} (φ : x ⟶ y)
    (F : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :
    restrictSheafPullbackComparison B E h S hS p hp φ F =
      (((PresheafOfModules.pullbackPushforwardAdjunction.{m}
          (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
            (etaleTopology_le_topology B))).comp
        (smallEtaleSheafificationAdjunctionUnivLE B E h S hS p x)).homEquiv
          (restrictModuleToSmallEtale B E h S hS p hp y (etaleTopology B)
            (etaleTopology_le_topology B) F.val)
          ((restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x).obj F)).symm
        (restrictModulePushforwardComparison B E h S hS p hp φ (etaleTopology B)
          (etaleTopology_le_topology B) F.val) :=
  (homEquiv_symm_comp_apply_obj _ _ _ _ _).symm

/-- `AlgebraicGeometry.Stack.restrictSheafPullbackComparison_eq_comp_homEquiv_symm` for a sheaf
given by its underlying presheaf of modules and its sheaf condition, with the presheaf named
rather than read off the sheaf. -/
theorem restrictSheafPullbackComparison_mk_eq_comp_homEquiv_symm {x y : 𝒳} (φ : x ⟶ y)
    (M : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hM : Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B)) M.presheaf) :
    restrictSheafPullbackComparison B E h S hS p hp φ ⟨M, hM⟩ =
      (((PresheafOfModules.pullbackPushforwardAdjunction.{m}
          (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
            (etaleTopology_le_topology B))).comp
        (smallEtaleSheafificationAdjunctionUnivLE B E h S hS p x)).homEquiv
          (restrictModuleToSmallEtale B E h S hS p hp y (etaleTopology B)
            (etaleTopology_le_topology B) M)
          ((restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x).obj ⟨M, hM⟩)).symm
        (restrictModulePushforwardComparison B E h S hS p hp φ (etaleTopology B)
          (etaleTopology_le_topology B) M) :=
  restrictSheafPullbackComparison_eq_comp_homEquiv_symm B E h S hS p hp φ ⟨M, hM⟩

attribute [local irreducible] AlgebraicGeometry.smallEtaleBaseChange CategoryTheory.Over.post
  AlgebraicGeometry.Stack.baseStructureSheaf AlgebraicGeometry.Stack.baseRingStructureSheaf in
/-- **The comparison map of an inverse image is invertible exactly when the comparison map of
the module at the image arrow is.** Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in
groupoids, `F` an étale sheaf of `𝒪_𝒴`-modules and `φ : x' ⟶ x` an arrow of `𝒳`. The comparison
map `c_φ` of **Stacks 0761**, in the source's reading with `a_{small}^*` the inverse image of
sheaves of modules, is invertible for the inverse image `f^*F` exactly when `c_{f φ}` is
invertible for `F`. No flatness is assumed.

Both comparison maps are transposes across the composite of the pullback–direct image adjunction
along `a_{small}^♯` and the sheafification adjunction. The square of **Stacks 075D** part (4),
`AlgebraicGeometry.Stack.restrictModulePushforwardComparison_app_inverseImageIso`, has the
identifications of part (3) on its vertical sides, so
`CategoryTheory.Adjunction.isIso_homEquiv_symm_iff_of_isoSquare` replaces the comparison for
`f^*F` by the transpose of the composite across that square; the two maps of structure sheaves
are equal by `AlgebraicGeometry.Stack.smallEtaleStructureComparison_eq_of_comp`, and
`PresheafOfModules.isIso_homEquiv_symm_iff_of_pushforward_eq_comp` identifies that transpose with
the comparison for `F`. -/
theorem isIso_restrictSheafPullbackComparison_modulePullback_iff
    (F : SheafOfModules.{m} (ringStructureSheafCore B S hS q hq (etaleTopology B)
      (etaleTopology_le_topology B)))
    {x' x : 𝒳} (φ : x' ⟶ x) :
    IsIso (restrictSheafPullbackComparison B E h S hS p hp φ
        ((modulePullback B S hS p q hp hq f hf (etaleTopology B)
          (etaleTopology_le_topology B)).obj F)) ↔
      IsIso (restrictSheafPullbackComparison B E h S hS q hq (f.map φ) F) := by
  subst hf
  have hf' : (f ⋙ q).IsFibredOneMorphism q f := hq.isFibredOneMorphism rfl
  have hcmp := smallEtaleStructureComparison_eq_of_comp B E h S hS (etaleTopology B)
    (etaleTopology_le_topology B) q hq f hp φ
  have hGs : Presheaf.IsSheaf (associatedTopology B S hS (f ⋙ q) (etaleTopology B))
      ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj F.val).presheaf :=
    ((modulePullback B S hS (f ⋙ q) q hp hq f rfl (etaleTopology B)
      (etaleTopology_le_topology B)).obj F).isSheaf
  have hG : (modulePullback B S hS (f ⋙ q) q hp hq f rfl (etaleTopology B)
      (etaleTopology_le_topology B)).obj F =
      ⟨(modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj F.val, hGs⟩ := rfl
  let e := restrictModuleToSmallEtaleInverseImageIso.{u, v, w, v', w', m}
    B E h S hS q hq f hp F.val F.isSheaf hf'
  rw [hG, restrictSheafPullbackComparison_eq_comp_homEquiv_symm B E h S hS q hq (f.map φ) F,
    restrictSheafPullbackComparison_mk_eq_comp_homEquiv_symm B E h S hS (f ⋙ q) hp φ]
  refine (isIso_homEquiv_symm_iff_of_conj
    ((PresheafOfModules.pullbackPushforwardAdjunction.{m}
      (smallEtaleStructureComparison B E h S hS (f ⋙ q) hp φ (etaleTopology B)
        (etaleTopology_le_topology B))).comp
      (smallEtaleSheafificationAdjunctionUnivLE B E h S hS (f ⋙ q) x'))
    (e x)
    (Y₁ := (restrictSheafToSmallEtale.{u, v, w, m} B E h S hS (f ⋙ q) hp x').obj
        ⟨(modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj F.val, hGs⟩)
    (Y₂ := (restrictSheafToSmallEtale.{u, v', w', m} B E h S hS q hq (f.obj x')).obj F)
    ((SheafOfModules.fullyFaithfulForget _).preimageIso (e x'))
    (restrictModulePushforwardComparison B E h S hS (f ⋙ q) hp φ (etaleTopology B)
      (etaleTopology_le_topology B)
      ((modulePresheafPullback.{u, v, w, v', w', m} B S hS q hq f hp).obj F.val))).trans ?_
  refine PresheafOfModules.isIso_homEquiv_symm_iff_of_pushforward_eq_comp hcmp
    (SheafOfModules.forget _) _
    ((PresheafOfModules.pullbackPushforwardAdjunction.{m}
      (smallEtaleStructureComparison B E h S hS q hq (f.map φ) (etaleTopology B)
        (etaleTopology_le_topology B))).comp
      (smallEtaleSheafificationAdjunctionUnivLE B E h S hS q (f.obj x'))) _ _ ?_
  intro W t
  have hid := ConcreteCategory.congr_hom (congrArg
    (fun k : _ ⟶ _ => PresheafOfModules.Hom.app k (Opposite.op W))
    (e x).inv_hom_id) t
  simp only [PresheafOfModules.comp_app, PresheafOfModules.id_app, CategoryTheory.comp_apply,
    CategoryTheory.id_apply] at hid
  have hpart := restrictModulePushforwardComparison_app_inverseImageIso B E h S hS q hq f hp
    F.val F.isSheaf hf' φ W
    ((e x).inv.app (Opposite.op W) t)
  rw [hid] at hpart
  simp only [PresheafOfModules.comp_app, CategoryTheory.comp_apply]
  exact hpart

/-- **Stacks 0764, part (1), in the source's ambient category.** Let `f : 𝒳 ⥤ 𝒴` be a
1-morphism of categories fibred in groupoids over the big fppf category of `S`, and let `F` be an
étale sheaf of `𝒪_𝒴`-modules with the flat base change property of **Stacks 0762** (comparison
maps taken with the inverse image of sheaves of modules on the small étale sites). Then the
inverse image `f^*F` of sheaves of modules has the flat base change property.

An arrow `φ` of `𝒳` lies over the same morphism of schemes as `f φ`, so this is
`AlgebraicGeometry.Stack.isIso_restrictSheafPullbackComparison_modulePullback_iff` at each arrow
lying over a flat morphism. -/
@[stacks 0764 "part (1), the whole part, in the source's ambient category of étale sheaves of \
  modules (a_small^* the inverse image of sheaves of modules), for any 1-morphism f : 𝒳 ⥤ 𝒴 of \
  categories fibred in groupoids over (Sch/S)_fppf, in particular any morphism of algebraic \
  stacks: the inverse image f^*F of a module F with the flat base change property has the flat \
  base change property"]
theorem hasFlatBaseChangePropertySheaf_modulePullback
    (F : SheafOfModules.{m} (ringStructureSheafCore B S hS q hq (etaleTopology B)
      (etaleTopology_le_topology B)))
    (hF : HasFlatBaseChangePropertySheafUnivLE B E h S hS q hq F) :
    HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp
      ((modulePullback B S hS p q hp hq f hf (etaleTopology B)
        (etaleTopology_le_topology B)).obj F) := by
  intro x' x φ hflat
  refine (isIso_restrictSheafPullbackComparison_modulePullback_iff B E h S hS p q hp hq f hf
    F φ).mpr (hF (f.map φ) ?_)
  subst hf
  exact hflat

end AlgebraicGeometry.Stack

end
