module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.CompactGenerationOfAbelianSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.BrownRepresentability
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.PullbackPreservesQuasiCoherent
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftUniversalArrow
public import StacksFrontier.Homology.DerivedCategory.MapDerivedCategorySquare

/-!
# Restriction of scalars along an isomorphism of presheaves of rings preserves cartesian objects

Let `C` be a category viewed as a site with the chaotic topology, and let `φ : O ⟶ O'` be a
morphism of presheaves of rings on `C`. Restriction of scalars along `φ` is exact, so it induces
`φ^* : D(O') ⥤ D(O)`, and the derived sections of `φ^* K` over `U` are those of `K` with scalars
restricted along `φ(U) : O(U) ⟶ O'(U)`.

When `φ` is an isomorphism, the comparison map of `φ^* K` along an arrow `a` of `Cᵒᵖ`
(Stacks 0GYV) is an isomorphism exactly when the comparison map of `K` along `a` is. The
comparison map along `a` is the adjoint transpose of the derived restriction map, so it is an
isomorphism exactly when the restriction map is a universal arrow for derived restriction of
scalars along `O(a)`; and that property is transported along the equivalences `φ(U)^*` and
`φ(V)^*`, which commute with the derived restrictions of scalars.

## Main results

* `CategoryTheory.Functor.isUniversalArrow_iff_of_iso`: universal arrows are transported along a
  square of functors whose horizontal sides are fully faithful, the left one an equivalence, in
  both directions.
* `Stacks.ModulesOnACategory.QuasiCoherentRestrictScalars.isIso_comparison_iff_isUniversalArrow`:
  the comparison map is an isomorphism exactly when the restriction map is a universal arrow;
  `isIso_comparison_Q_iff` reads this at the image of a complex.
* `Stacks.ModulesOnACategory.QuasiCoherentRestrictScalars.isIso_comparison_iff_of_iso`: the
  comparison maps of isomorphic objects are invertible together.
* `Stacks.ModulesOnACategory.QuasiCoherentRestrictScalars.isIso_comparison_restrictScalars_iff`
  and `isQC_restrictScalars_iff`: for an isomorphism `φ`, the comparison maps of `φ^* K` and of
  `K` along an arrow are invertible together, and `φ^* K` lies in `QC(O)` exactly when `K` lies
  in `QC(O')`, for arbitrary base-change data on the two sides.

## References

* [Stacks Project, Tag 0GYV](https://stacks.math.columbia.edu/tag/0GYV)
* [Stacks Project, Tag 0GZ1](https://stacks.math.columbia.edu/tag/0GZ1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent (dRestrictScalars)

universe w u v r

namespace CategoryTheory.Functor

variable {D : Type*} [Category D] {E : Type*} [Category E] {D' : Type*} [Category D']
  {E' : Type*} [Category E']

/-- **Universal arrows are transported along a commuting square of fully faithful functors, in
both directions.** If `β : G ⋙ P ≅ Q ⋙ G'` with `P` fully faithful and `Q` an equivalence, then
`g : X ⟶ G.obj Y` is a universal arrow for `G` exactly when `P.map g ≫ β.hom.app Y` is one for
`G'`. -/
theorem isUniversalArrow_iff_of_iso {G : E ⥤ D} {G' : E' ⥤ D'} {P : D ⥤ D'} {Q : E ⥤ E'}
    [P.Full] [P.Faithful] [Q.Full] [Q.Faithful] [Q.EssSurj] (β : G ⋙ P ≅ Q ⋙ G')
    {X : D} {Y : E} (g : X ⟶ G.obj Y) :
    G.IsUniversalArrow g ↔ G'.IsUniversalArrow (P.map g ≫ β.hom.app Y) := by
  refine ⟨IsUniversalArrow.of_equivalence β.symm (Iso.refl _) (Iso.refl _) (by simp),
    fun hg Z ↦ ?_⟩
  have hP := FullyFaithful.ofFullyFaithful P
  have hQ := FullyFaithful.ofFullyFaithful Q
  have h : (fun f' : Q.obj Y ⟶ Q.obj Z ↦ (P.map g ≫ β.hom.app Y) ≫ G'.map f') =
      (Iso.homCongr (Iso.refl _) (β.app Z)) ∘ hP.homEquiv ∘
        (fun f : Y ⟶ Z ↦ g ≫ G.map f) ∘ hQ.homEquiv.symm := by
    funext f'
    have hn := β.hom.naturality (hQ.preimage f')
    simp only [Functor.comp_map, FullyFaithful.map_preimage] at hn
    simp only [Function.comp_apply, Iso.homCongr_apply, Iso.refl_inv, Iso.app_hom,
      Category.id_comp, FullyFaithful.homEquiv_apply, Functor.map_comp, Category.assoc]
    exact congrArg (P.map g ≫ ·) hn.symm
  have hb := hg (Q.obj Z)
  rwa [h, Equiv.comp_bijective, Equiv.comp_bijective, Equiv.bijective_comp] at hb

/-- Universality is invariant under isomorphisms of the source and of the target, compatibly with
the two arrows. -/
theorem IsUniversalArrow.iff_of_iso {G : E ⥤ D} {X X' : D} {Y Y' : E} {g : X ⟶ G.obj Y}
    {g' : X' ⟶ G.obj Y'} (eX : X ≅ X') (eY : Y ≅ Y') (he : g ≫ G.map eY.hom = eX.hom ≫ g') :
    G.IsUniversalArrow g ↔ G.IsUniversalArrow g' :=
  ⟨IsUniversalArrow.of_iso eX eY he, IsUniversalArrow.of_iso eX.symm eY.symm (by
    rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, ← he, Category.assoc,
      ← G.map_comp, Iso.hom_inv_id, G.map_id, Category.comp_id])⟩

end CategoryTheory.Functor

namespace Stacks.ModulesOnACategory.QuasiCoherentRestrictScalars

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C]

/-- **The comparison map is the adjoint transpose of the restriction map**, so it is an
isomorphism exactly when the derived restriction map along `a` is a universal arrow for derived
restriction of scalars along `O(a)`. In particular this does not depend on the base-change
datum. -/
theorem isIso_comparison_iff_isUniversalArrow {O : Cᵒᵖ ⥤ RingCat.{r}}
    (bc : BaseChangeData.{w} O) {U V : Cᵒᵖ} (a : V ⟶ U) (K : DMod.{w} O) :
    IsIso (comparison.{w} bc a K) ↔
      (DRestrict.{w} O a).IsUniversalArrow (restrictionMap.{w} O a K) :=
  (Functor.isUniversalArrow_iff_isIso (bc.baseChangeAdj a) _).symm

variable {O O' : Cᵒᵖ ⥤ RingCat.{r}} (φ : O ⟶ O')

/-- Restriction of scalars of presheaves of modules is exact. -/
instance restrictScalars_preservesHomology.{m} :
    (PresheafOfModules.restrictScalars.{m} φ).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ fun _ hS =>
    (PresheafOfModules.toPresheaf O).reflects_exact_of_faithful _
      (hS.map (PresheafOfModules.toPresheaf O'))

/-- Restriction of scalars of presheaves of modules is left exact. -/
instance restrictScalars_preservesFiniteLimits.{m} :
    PreservesFiniteLimits (PresheafOfModules.restrictScalars.{m} φ) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

/-- Restriction of scalars of presheaves of modules is right exact. -/
instance restrictScalars_preservesFiniteColimits.{m} :
    PreservesFiniteColimits (PresheafOfModules.restrictScalars.{m} φ) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- **Derived restriction of scalars `φ^* : D(O') ⥤ D(O)`** along a morphism of presheaves of
rings, the descent of the exact restriction of scalars of presheaves of modules. -/
abbrev derivedRestrictScalars : DMod.{w} O' ⥤ DMod.{w} O :=
  (PresheafOfModules.restrictScalars.{max u v r w} φ).mapDerivedCategory

omit φ

/-- The comparison maps of isomorphic objects are invertible together. -/
theorem isIso_comparison_iff_of_iso {O : Cᵒᵖ ⥤ RingCat.{r}} (bc : BaseChangeData.{w} O)
    {U V : Cᵒᵖ} (a : V ⟶ U) {K K' : DMod.{w} O} (e : K ≅ K') :
    IsIso (comparison.{w} bc a K) ↔ IsIso (comparison.{w} bc a K') := by
  rw [← isIso_comp_right_iff _ ((RGamma.{w} O U).map e.hom), ← comparison_naturality,
    isIso_comp_left_iff]

/-- **The comparison map at the image of a complex.** For a complex `P` of presheaves of
`O`-modules, the comparison map of `P` along `a` is an isomorphism exactly when the restriction
map of complexes `P(V) ⟶ P(U)`, viewed in the derived category of `O(V)`-modules, is a universal
arrow for derived restriction of scalars along `O(a)`. -/
theorem isIso_comparison_Q_iff {O : Cᵒᵖ ⥤ RingCat.{r}} (bc : BaseChangeData.{w} O)
    {U V : Cᵒᵖ} (a : V ⟶ U) (P : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) :
    IsIso (comparison.{w} bc a (DerivedCategory.Q.obj P)) ↔
      (DRestrict.{w} O a).IsUniversalArrow
        (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (PresheafOfModules.restriction O a) (ComplexShape.up ℤ)).app P) ≫
          (ModuleCat.restrictScalars.{max u v r w} (O.map a).hom).mapDerivedCategoryFactors.inv.app
            (((PresheafOfModules.evaluation.{max u v r w} O U).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) := by
  rw [isIso_comparison_iff_isUniversalArrow, restrictionMap_Q]
  refine (Functor.IsUniversalArrow.iff_of_iso
    ((PresheafOfModules.evaluation.{max u v r w} O V).mapDerivedCategoryFactors.app P)
    ((PresheafOfModules.evaluation.{max u v r w} O U).mapDerivedCategoryFactors.app P) ?_)
  simp only [Category.assoc, Iso.app_hom, ← Functor.map_comp, Iso.inv_hom_id_app,
    Functor.comp_obj, CategoryTheory.Functor.map_id, Category.comp_id]

variable {O O' : Cᵒᵖ ⥤ RingCat.{r}} (φ : O ⟶ O')

/-- The square of restrictions of scalars of modules attached to an arrow `a : V ⟶ U` of `Cᵒᵖ`:
restricting along `O'(a)` and then along `φ(V)` is restricting along `φ(U)` and then along
`O(a)`, both being restriction along the common diagonal. -/
def restrictScalarsSquare {U V : Cᵒᵖ} (a : V ⟶ U) :
    ModuleCat.restrictScalars.{max u v r w} (O'.map a).hom ⋙
        ModuleCat.restrictScalars.{max u v r w} (φ.app V).hom ≅
      ModuleCat.restrictScalars.{max u v r w} (φ.app U).hom ⋙
        ModuleCat.restrictScalars.{max u v r w} (O.map a).hom :=
  (ModuleCat.restrictScalarsComp' (φ.app V).hom (O'.map a).hom _ rfl).symm ≪≫
    ModuleCat.restrictScalarsComp' (O.map a).hom (φ.app U).hom _
      (by rw [← RingCat.hom_comp, ← RingCat.hom_comp, φ.naturality])

section Bookkeeping

universe t₁ t₂ t₃ s₁ s₂ s₃

variable {E₁ : Type t₁} [Category.{s₁} E₁] {E₂ : Type t₂} [Category.{s₂} E₂]
  {K : Type t₃} [Category.{s₃} K]

/-- A composite `G.map (x ≫ y) ≫ rest` rewritten through a naturality square `hnat` and the two
cancelling pairs `hcancel` and `hj`. -/
private theorem comp_eq_of_naturality {F : E₁ ⥤ E₂} {G : K ⥤ E₂} {k₀ k₁ k₂ : K}
    {x : k₀ ⟶ k₁} {y : k₁ ⟶ k₂} {e₀ e₁ e₂ : E₁} {ρ : e₀ ⟶ e₁} {jinv : e₁ ⟶ e₂}
    {jhom : e₂ ⟶ e₁} {z : E₂} {inv₀ : G.obj k₀ ⟶ F.obj e₀} {inv₁ : G.obj k₁ ⟶ F.obj e₁}
    {hom₁ : F.obj e₁ ⟶ G.obj k₁} {rest : G.obj k₂ ⟶ z}
    (hnat : G.map x ≫ inv₁ = inv₀ ≫ F.map ρ) (hcancel : inv₁ ≫ hom₁ = 𝟙 _)
    (hj : jinv ≫ jhom = 𝟙 e₁) :
    G.map (x ≫ y) ≫ rest = inv₀ ≫ F.map (ρ ≫ jinv) ≫ F.map jhom ≫ hom₁ ≫ G.map y ≫ rest := by
  rw [← F.map_comp_assoc, Category.assoc, hj, Category.comp_id, ← reassoc_of% hnat,
    reassoc_of% hcancel, G.map_comp, Category.assoc]

end Bookkeeping

/-- **Comparison maps under restriction of scalars along an isomorphism.** For an isomorphism
`φ : O ⟶ O'` of presheaves of rings and an arrow `a : V ⟶ U` of `Cᵒᵖ`, the comparison map of
`φ^* K` along `a` is an isomorphism exactly when the comparison map of `K` along `a` is, the
cartesian condition on either side being taken with respect to arbitrary base-change data. -/
theorem isIso_comparison_restrictScalars_iff [IsIso φ] (bc : BaseChangeData.{w} O)
    (bc' : BaseChangeData.{w} O') {U V : Cᵒᵖ} (a : V ⟶ U) (K : DMod.{w} O') :
    IsIso (comparison.{w} bc a ((derivedRestrictScalars.{w} φ).obj K)) ↔
      IsIso (comparison.{w} bc' a K) := by
  let P := DerivedCategory.Q.objPreimage K
  let eK : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let T := PresheafOfModules.restrictScalars.{max u v r w} φ
  let eT : (derivedRestrictScalars.{w} φ).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
    T.mapDerivedCategoryFactors.app P
  rw [← isIso_comparison_iff_of_iso bc' a eK,
    ← isIso_comparison_iff_of_iso bc a ((derivedRestrictScalars.{w} φ).mapIso eK),
    isIso_comparison_iff_of_iso bc a eT, isIso_comparison_Q_iff, isIso_comparison_Q_iff]
  have (W : Cᵒᵖ) : (ModuleCat.restrictScalars.{max u v r w} (φ.app W).hom).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv (asIso (φ.app W)).ringCatIsoToRingEquiv
  have (W : Cᵒᵖ) : (dRestrictScalars.{r, max u v r w} (φ.app W)).IsEquivalence :=
    Stacks.Cohomology.isEquivalence_mapDerivedCategory _
  let β := Functor.mapDerivedCategorySquareIso (restrictScalarsSquare.{w} φ a)
  rw [Functor.isUniversalArrow_iff_of_iso (P := dRestrictScalars.{r, max u v r w} (φ.app V))
    (Q := dRestrictScalars.{r, max u v r w} (φ.app U)) β]
  let BV := ModuleCat.restrictScalars.{max u v r w} (φ.app V).hom
  let BU := ModuleCat.restrictScalars.{max u v r w} (φ.app U).hom
  let PV := ((PresheafOfModules.evaluation.{max u v r w} O' V).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P
  let PU := ((PresheafOfModules.evaluation.{max u v r w} O' U).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P
  let eX : DerivedCategory.Q.obj ((BV.mapHomologicalComplex (ComplexShape.up ℤ)).obj PV) ≅
      BV.mapDerivedCategory.obj (DerivedCategory.Q.obj PV) :=
    (BV.mapDerivedCategoryFactors.app PV).symm
  let eY : DerivedCategory.Q.obj ((BU.mapHomologicalComplex (ComplexShape.up ℤ)).obj PU) ≅
      BU.mapDerivedCategory.obj (DerivedCategory.Q.obj PU) :=
    (BU.mapDerivedCategoryFactors.app PU).symm
  have hchain : (NatTrans.mapHomologicalComplex (PresheafOfModules.restriction O a)
        (ComplexShape.up ℤ)).app ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
      (BV.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (PresheafOfModules.restriction O' a)
            (ComplexShape.up ℤ)).app P) ≫
        (Functor.mapHomologicalComplexCompIso (restrictScalarsSquare.{w} φ a)
          (ComplexShape.up ℤ)).hom.app PU := by
    ext n x
    rfl
  refine Functor.IsUniversalArrow.iff_of_iso eX eY ?_
  simp only [β, eX, eY, Iso.symm_hom, Iso.app_inv, Functor.mapDerivedCategorySquareIso_hom_app_Q,
    Category.assoc]
  let ρ' := (NatTrans.mapHomologicalComplex (PresheafOfModules.restriction O' a)
    (ComplexShape.up ℤ)).app P
  rw [hchain]
  exact comp_eq_of_naturality (G := DerivedCategory.Q (C := ModuleCat.{max u v r w} (O.obj V)))
    (F := BV.mapDerivedCategory) (x := (BV.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ')
    (ρ := DerivedCategory.Q.map ρ')
    (inv₁ := BV.mapDerivedCategoryFactors.inv.app
      (((ModuleCat.restrictScalars.{max u v r w} (O'.map a).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj PU))
    (BV.mapDerivedCategoryFactors.inv.naturality ρ') (Iso.inv_hom_id_app _ _)
    (Iso.inv_hom_id_app _ _)

/-- **Restriction of scalars along an isomorphism of presheaves of rings preserves and reflects
cartesian objects.** For an isomorphism `φ : O ⟶ O'`, `φ^* K` lies in `QC(O)` exactly when `K`
lies in `QC(O')`, for arbitrary base-change data on the two sides. -/
theorem isQC_restrictScalars_iff [IsIso φ] (bc : BaseChangeData.{w} O)
    (bc' : BaseChangeData.{w} O') (K : DMod.{w} O') :
    IsQC.{w} bc ((derivedRestrictScalars.{w} φ).obj K) ↔ IsQC.{w} bc' K :=
  forall₂_congr fun _ _ ↦ forall_congr' fun a ↦ isIso_comparison_restrictScalars_iff φ bc bc' a K

end Stacks.ModulesOnACategory.QuasiCoherentRestrictScalars

end
