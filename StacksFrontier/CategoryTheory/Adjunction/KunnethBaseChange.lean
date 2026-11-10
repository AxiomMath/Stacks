module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormula
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethIsomorphism

/-!
# Base change maps of a square through the Künneth map

Consider a square of adjunctions `Lf ⊣ Rf`, `Lg ⊣ Rg`, `Lf' ⊣ Rf'`, `Lg' ⊣ Rg'` whose two
composites of left adjoints `Lg ⋙ Lf'` and `Lf ⋙ Lg'` are identified, with bifunctors on the four
corners and comparisons of them along the four left adjoints.  For `E` upstairs on the right and
`N` downstairs on the left, the Künneth map `Rf E ⊗ Rg N ⟶ R(L_g'E ⊗ L_f'N)` factors in two ways:
through the projection formula of `f`, the base change map of the square read with `f`
horizontal, and the opposite-order projection formula of `g'`; and through the opposite-order
projection formula of `g`, the base change map of the square in the first factor, and the
projection formula of `f'`.  This is the argument of Stacks 08IR: if every map of the first
chain and the two projection formulas of the second are invertible, so is the image under `Rg`
of the base change map tensored with `N`.

## Main results

* `Stacks.CategoryTheory.KunnethBaseChange.isIso_homEquiv_iff_of_iso`: transposes of maps out of
  two isomorphic left adjoints are invertible together.
* `Stacks.CategoryTheory.KunnethBaseChange.isIso_map_tensor_baseChange_of_isIso`: the conclusion
  above.

## References

* [Stacks Project, Tag 08IR](https://stacks.math.columbia.edu/tag/08IR)
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace Stacks.CategoryTheory.KunnethBaseChange


/-- Transposes, under two adjunctions with isomorphic left adjoints, of maps differing by that
isomorphism are invertible together. -/
theorem isIso_homEquiv_iff_of_iso {C D : Type*} [Category C] [Category D] {L₁ L₂ : C ⥤ D}
    {R₁ R₂ : D ⥤ C} (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (θ : L₁ ≅ L₂) {X : C} {Z : D}
    (u : L₂.obj X ⟶ Z) :
    IsIso (a₁.homEquiv X Z (θ.hom.app X ≫ u)) ↔ IsIso (a₂.homEquiv X Z u) := by
  have h : a₁.homEquiv X Z (θ.hom.app X ≫ u) =
      a₂.homEquiv X Z u ≫ (conjugateEquiv a₂ a₁ θ.hom).app Z := by
    rw [conjugateEquiv_apply_app, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    have n₁ := a₁.unit.naturality (a₂.unit.app X ≫ R₂.map u)
    simp only [Functor.id_map, Functor.comp_map] at n₁
    simp only [Category.assoc]
    rw [reassoc_of% n₁]
    congr 1
    rw [← R₁.map_comp, ← R₁.map_comp]
    congr 1
    have n₂ := θ.hom.naturality (a₂.unit.app X ≫ R₂.map u)
    rw [reassoc_of% n₂]
    simp
  have : IsIso (conjugateEquiv a₂ a₁ θ.hom) := by
    have := conjugateEquiv_iso a₂ a₁ θ.hom
    infer_instance
  rw [h]
  constructor
  · intro h'
    exact IsIso.of_isIso_comp_right _ ((conjugateEquiv a₂ a₁ θ.hom).app Z)
  · intro h'
    infer_instance

/-- The bifunctor with its two arguments interchanged. -/
abbrev flipBifunctor {C : Type*} [Category C] (T : C × C ⥤ C) : C × C ⥤ C :=
  CategoryTheory.Prod.swap C C ⋙ T

/-- A comparison of bifunctors along a functor, read for the bifunctors with interchanged
arguments. -/
def flipComparison {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {A : C × C ⥤ C}
    {B : D × D ⥤ D} (α : A ⋙ L ⟶ L.prod L ⋙ B) :
    flipBifunctor A ⋙ L ⟶ L.prod L ⋙ flipBifunctor B where
  app p := α.app (p.2, p.1)
  naturality _ _ φ := α.naturality ((CategoryTheory.Prod.swap C C).map φ)

section Square

variable {CY CX CY' CX' : Type*} [Category CY] [Category CX] [Category CY'] [Category CX']
  {Lf : CY ⥤ CX} {Rf : CX ⥤ CY} {Lg : CY ⥤ CY'} {Rg : CY' ⥤ CY}
  {Lf' : CY' ⥤ CX'} {Rf' : CX' ⥤ CY'} {Lg' : CX ⥤ CX'} {Rg' : CX' ⥤ CX} {Lc : CY ⥤ CX'}
  (af : Lf ⊣ Rf) (ag : Lg ⊣ Rg) (af' : Lf' ⊣ Rf') (ag' : Lg' ⊣ Rg')
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  (TY : CY × CY ⥤ CY) (TY' : CY' × CY' ⥤ CY') (TX : CX × CX ⥤ CX) (TX' : CX' × CX' ⥤ CX')
  (αf : TY ⋙ Lf ⟶ Lf.prod Lf ⋙ TX) (αf' : TY' ⋙ Lf' ⟶ Lf'.prod Lf' ⋙ TX')
  (αg : TY ⋙ Lg ⟶ Lg.prod Lg ⋙ TY') (αg' : TX ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ TX')

/-- **Base change through the Künneth map.**  If the projection formula of `f` at
`(E, Rg N)`, the base change map at `N` of the square read with `f` horizontal, the
opposite-order projection formula of `g'` at `(E, Lf' N)`, the opposite-order projection formula
of `g` at `(Rf E, N)` and the projection formula of `f'` at `(Lg' E, N)` are invertible, and the
four comparisons are compatible at `(Rf E, Rg N)`, then `Rg` of the base change map at `E`
tensored with `N` is invertible. -/
theorem isIso_map_tensor_baseChange_of_isIso (E : CX) (N : CY')
    (hsq : Stacks.AffineProjectionFormula.TensorComparisonCompatible eg ef TY TY' TX TX'
      αf αf' αg αg' (Rf.obj E) (Rg.obj N))
    (h₁ : IsIso (adjunctionTensorMap af TY TX αf E (Rg.obj N)))
    (h₂ : IsIso (Stacks.CategoryTheory.BaseChange.map ag ag' ef eg N))
    (h₃ : IsIso (Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight ag' TX TX' αg' E
      (Lf'.obj N)))
    (h₄ : IsIso (Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight ag TY TY' αg
      (Rf.obj E) N))
    (h₅ : IsIso (adjunctionTensorMap af' TY' TX' αf' (Lg'.obj E) N)) :
    IsIso (Rg.map (TY'.map (Stacks.CategoryTheory.BaseChange.map af af' eg ef E ×ₘ 𝟙 N))) := by
  let v₁ : Lg'.obj (Lf.obj (Rg.obj N)) ⟶ Lf'.obj N :=
    ef.hom.app (Rg.obj N) ≫ eg.inv.app (Rg.obj N) ≫ Lf'.map (ag.counit.app N)
  let v₂ : Lf'.obj (Lg.obj (Rf.obj E)) ⟶ Lg'.obj E :=
    eg.hom.app (Rf.obj E) ≫ ef.inv.app (Rf.obj E) ≫ Lg'.map (af.counit.app E)
  have c₁ := Stacks.Cohomology.DerivedKunneth.homEquiv_comp_bitensor_eq af ag' TY TX TX' αf αg'
    E (Rg.obj N) (Lf'.obj N) v₁
  have c₂ := Stacks.Cohomology.DerivedKunneth.homEquiv_comp_bitensor_eq ag af'
    (flipBifunctor TY) (flipBifunctor TY') (flipBifunctor TX') (flipComparison αg)
    (flipComparison αf') N (Rf.obj E) (Lg'.obj E) v₂
  rw [← Stacks.CategoryTheory.BaseChange.map_eq] at c₁ c₂
  have : IsIso (𝟙 E ×ₘ Stacks.CategoryTheory.BaseChange.map ag ag' ef eg N) :=
    (isIso_prod_iff _ _).mpr ⟨inferInstance, h₂⟩
  have i₁ : IsIso _ := (congrArg (fun x => IsIso x) c₁).mpr inferInstance
  let u₁ : (Lf ⋙ Lg').obj (TY.obj (Rf.obj E, Rg.obj N)) ⟶
      TX'.obj (Lg'.obj E, Lf'.obj N) :=
    Lg'.map (αf.app (Rf.obj E, Rg.obj N)) ≫ αg'.app (Lf.obj (Rf.obj E), Lf.obj (Rg.obj N)) ≫
      TX'.map (Lg'.map (af.counit.app E) ×ₘ v₁)
  let θ := Stacks.AffineProjectionFormula.squareCompositeIso eg ef
  have hu : Lf'.map (αg.app (Rf.obj E, Rg.obj N)) ≫
      αf'.app (Lg.obj (Rf.obj E), Lg.obj (Rg.obj N)) ≫
        TX'.map (v₂ ×ₘ Lf'.map (ag.counit.app N)) = θ.hom.app _ ≫ u₁ := by
    unfold Stacks.AffineProjectionFormula.TensorComparisonCompatible at hsq
    have hv₂ : v₂ = θ.hom.app (Rf.obj E) ≫ Lg'.map (af.counit.app E) := by
      simp only [v₂, θ, Stacks.AffineProjectionFormula.squareCompositeIso_hom_app,
        Category.assoc]
    have hv₁ : Lf'.map (ag.counit.app N) = θ.hom.app (Rg.obj N) ≫ v₁ := by
      simp only [v₁, θ, Stacks.AffineProjectionFormula.squareCompositeIso_hom_app,
        Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc]
    have hm : TX'.map (v₂ ×ₘ Lf'.map (ag.counit.app N)) =
        TX'.map (θ.hom.app (Rf.obj E) ×ₘ θ.hom.app (Rg.obj N)) ≫
          TX'.map (Lg'.map (af.counit.app E) ×ₘ v₁) := by
      rw [← TX'.map_comp, prod_comp, ← hv₂, ← hv₁]
    rw [hm, reassoc_of% hsq]
  have k₁ : IsIso ((af.comp ag').homEquiv _ _ u₁) := by
    rw [Adjunction.comp_homEquiv, Equiv.trans_apply]
    exact i₁
  have k := (isIso_homEquiv_iff_of_iso (ag.comp af') (af.comp ag') θ u₁).2 k₁
  rw [Adjunction.comp_homEquiv, Equiv.trans_apply, ← hu] at k
  have i₂ : IsIso _ := (congrArg (fun x => IsIso x) c₂).mp k
  have j₁ : IsIso (adjunctionTensorMap ag (flipBifunctor TY) (flipBifunctor TY')
      (flipComparison αg) N (Rf.obj E)) := h₄
  have := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ j₁ i₂
  have j₂ : IsIso (Rg.map (Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight af'
      (flipBifunctor TY') (flipBifunctor TX') (flipComparison αf') N (Lg'.obj E))) :=
    Functor.map_isIso Rg (f := adjunctionTensorMap af' TY' TX' αf' (Lg'.obj E) N)
  exact @IsIso.of_isIso_comp_right _ _ _ _ _
    (Rg.map (TY'.map (Stacks.CategoryTheory.BaseChange.map af af' eg ef E ×ₘ 𝟙 N)))
    (Rg.map (Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight af'
      (flipBifunctor TY') (flipBifunctor TX') (flipComparison αf') N (Lg'.obj E))) j₂ this

end Square

end Stacks.CategoryTheory.KunnethBaseChange

end
