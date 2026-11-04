module

public import StacksFrontier.CategoryTheory.Adjunction.KunnethBaseChange

/-!
# Base change maps followed by a map, through the Künneth map

In the situation of `StacksFrontier.CategoryTheory.Adjunction.KunnethBaseChange`, let moreover
`φ : Lg' E ⟶ K'`.  The Künneth argument of Stacks 08IR applies to the composite of the base change
map at `E` with `Rf' φ`: if the projection formula of `f` at `(E, Rg N)`, the opposite-order
projection formula of `g` at `(Rf E, N)` and the projection formula of `f'` at `(K', N)` are
invertible, then `Rg` of that composite tensored with `N` is invertible as soon as `Rf` of the
composite

`E ⊗ Lf Rg N ⟶ E ⊗ Rg' Lf' N ⟶ Rg'(Lg' E ⊗ Lf' N) ⟶ Rg'(K' ⊗ Lf' N)`

is.  This is the reduction of Stacks 0DKH over an affine base to a statement on `X`.

## Main results

* `Stacks.CategoryTheory.KunnethBaseChange.isIso_map_tensorBaseChangeCompMap_iff`
* `Stacks.CategoryTheory.KunnethBaseChange.isIso_map_tensor_baseChange_comp_of_isIso`
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace Stacks.CategoryTheory.KunnethBaseChange

section Square

variable {CY CX CY' CX' : Type*} [Category CY] [Category CX] [Category CY'] [Category CX']
  {Lf : CY ⥤ CX} {Rf : CX ⥤ CY} {Lg : CY ⥤ CY'} {Rg : CY' ⥤ CY}
  {Lf' : CY' ⥤ CX'} {Rf' : CX' ⥤ CY'} {Lg' : CX ⥤ CX'} {Rg' : CX' ⥤ CX} {Lc : CY ⥤ CX'}
  (af : Lf ⊣ Rf) (ag : Lg ⊣ Rg) (af' : Lf' ⊣ Rf') (ag' : Lg' ⊣ Rg')
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  (TY : CY × CY ⥤ CY) (TY' : CY' × CY' ⥤ CY') (TX : CX × CX ⥤ CX) (TX' : CX' × CX' ⥤ CX')
  (αf : TY ⋙ Lf ⟶ Lf.prod Lf ⋙ TX) (αf' : TY' ⋙ Lf' ⟶ Lf'.prod Lf' ⋙ TX')
  (αg : TY ⋙ Lg ⟶ Lg.prod Lg ⋙ TY') (αg' : TX ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ TX')

/-- The map `E ⊗ Lf Rg N ⟶ Rg'(K' ⊗ Lf' N)` on the upper right corner: the transposed base change
map at `N` in the second factor, the opposite-order projection formula of `g'` at `(E, Lf' N)`,
and `Rg'` of `φ` tensored with `Lf' N`. -/
def tensorBaseChangeCompMap (E : CX) (N : CY') {K' : CX'} (φ : Lg'.obj E ⟶ K') :
    TX.obj (E, Lf.obj (Rg.obj N)) ⟶ Rg'.obj (TX'.obj (K', Lf'.obj N)) :=
  TX.map (𝟙 E ×ₘ Stacks.CategoryTheory.BaseChange.map ag ag' ef eg N) ≫
    Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight ag' TX TX' αg' E (Lf'.obj N) ≫
      Rg'.map (TX'.map (φ ×ₘ 𝟙 (Lf'.obj N)))

/-- **Base change followed by a map, through the Künneth map, as an equivalence.**  If the
projection formula of `f` at `(E, Rg N)`, the opposite-order projection formula of `g` at
`(Rf E, N)` and the projection formula of `f'` at `(K', N)` are invertible and the four
comparisons are compatible at `(Rf E, Rg N)`, then `Rf` of `tensorBaseChangeCompMap` is invertible
exactly when `Rg` of the base change map at `E` followed by `Rf' φ`, tensored with `N`, is. -/
theorem isIso_map_tensorBaseChangeCompMap_iff (E : CX) (N : CY') {K' : CX'}
    (φ : Lg'.obj E ⟶ K')
    (hsq : Stacks.AffineProjectionFormula.TensorComparisonCompatible eg ef TY TY' TX TX'
      αf αf' αg αg' (Rf.obj E) (Rg.obj N))
    (h₁ : IsIso (adjunctionTensorMap af TY TX αf E (Rg.obj N)))
    (h₄ : IsIso (Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight ag TY TY' αg
      (Rf.obj E) N))
    (h₅ : IsIso (adjunctionTensorMap af' TY' TX' αf' K' N)) :
    IsIso (Rf.map (tensorBaseChangeCompMap ag ag' eg ef TX TX' αg' E N φ)) ↔
      IsIso (Rg.map (TY'.map ((Stacks.CategoryTheory.BaseChange.map af af' eg ef E ≫
        Rf'.map φ) ×ₘ 𝟙 N))) := by
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
  let m : TX'.obj (Lg'.obj E, Lf'.obj N) ⟶ TX'.obj (K', Lf'.obj N) :=
    TX'.map (φ ×ₘ 𝟙 (Lf'.obj N))
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
  -- the first factorization, followed by `φ`
  have k₁ : IsIso ((af.comp ag').homEquiv _ _ (u₁ ≫ m)) ↔
      IsIso (Rf.map (tensorBaseChangeCompMap ag ag' eg ef TX TX' αg' E N φ)) := by
    rw [Adjunction.homEquiv_naturality_right, Adjunction.comp_homEquiv, Equiv.trans_apply]
    rw [c₁]
    simp only [tensorBaseChangeCompMap, Functor.comp_map, Functor.map_comp, Category.assoc, m]
    exact ⟨fun h => @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ h₁ h, fun h => inferInstance⟩
  have k := (isIso_homEquiv_iff_of_iso (ag.comp af') (af.comp ag') θ (u₁ ≫ m)).trans k₁
  rw [← Category.assoc, ← hu, Adjunction.homEquiv_naturality_right, Adjunction.comp_homEquiv,
    Equiv.trans_apply] at k
  have c₂' := congrArg (fun x => x ≫ (Rf' ⋙ Rg).map m) c₂
  refine k.symm.trans ((Iff.of_eq (congrArg (fun x => IsIso x) c₂')).trans ?_)
  simp only [Category.assoc]
  have j₁ : IsIso (adjunctionTensorMap ag (flipBifunctor TY) (flipBifunctor TY')
      (flipComparison αg) N (Rf.obj E)) := h₄
  -- naturality of the projection formula of `f'` along `φ`
  have hn := CategoryTheory.adjunctionTensorMap_natural af' TY' TX' αf' φ (𝟙 N)
  rw [CategoryTheory.Functor.map_id] at hn
  have e₃ : Rg.map ((flipBifunctor TY').map (𝟙 N ×ₘ
        Stacks.CategoryTheory.BaseChange.map af af' eg ef E)) ≫
      Rg.map (Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight af'
        (flipBifunctor TY') (flipBifunctor TX') (flipComparison αf') N (Lg'.obj E)) ≫
        (Rf' ⋙ Rg).map m =
      Rg.map (TY'.map ((Stacks.CategoryTheory.BaseChange.map af af' eg ef E ≫
        Rf'.map φ) ×ₘ 𝟙 N)) ≫ Rg.map (adjunctionTensorMap af' TY' TX' αf' K' N) := by
    have hn' : Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight af'
        (flipBifunctor TY') (flipBifunctor TX') (flipComparison αf') N (Lg'.obj E) ≫
          Rf'.map m =
        TY'.map (Rf'.map φ ×ₘ 𝟙 N) ≫ adjunctionTensorMap af' TY' TX' αf' K' N := hn.symm
    have hsplit : TY'.map ((Stacks.CategoryTheory.BaseChange.map af af' eg ef E ≫
        Rf'.map φ) ×ₘ 𝟙 N) =
        (flipBifunctor TY').map (𝟙 N ×ₘ Stacks.CategoryTheory.BaseChange.map af af' eg ef E) ≫
          TY'.map (Rf'.map φ ×ₘ 𝟙 N) := by
      change _ = TY'.map _ ≫ TY'.map _
      rw [← TY'.map_comp, prod_comp, Category.comp_id]
      rfl
    have hc : (Rf' ⋙ Rg).map m = Rg.map (Rf'.map m) := rfl
    rw [hc, hsplit]
    simp only [← Rg.map_comp, Category.assoc, hn']
  rw [isIso_comp_left_iff, e₃, isIso_comp_right_iff]

/-- **Base change followed by a map, through the Künneth map.**  If the projection formula of
`f` at `(E, Rg N)`, the opposite-order projection formula of `g` at `(Rf E, N)` and the
projection formula of `f'` at `(K', N)` are invertible, the four comparisons are compatible at
`(Rf E, Rg N)`, and `Rf` of `tensorBaseChangeCompMap` is invertible, then `Rg` of the base change
map at `E` followed by `Rf' φ`, tensored with `N`, is invertible. -/
theorem isIso_map_tensor_baseChange_comp_of_isIso (E : CX) (N : CY') {K' : CX'}
    (φ : Lg'.obj E ⟶ K')
    (hsq : Stacks.AffineProjectionFormula.TensorComparisonCompatible eg ef TY TY' TX TX'
      αf αf' αg αg' (Rf.obj E) (Rg.obj N))
    (h₁ : IsIso (adjunctionTensorMap af TY TX αf E (Rg.obj N)))
    (hψ : IsIso (Rf.map (tensorBaseChangeCompMap ag ag' eg ef TX TX' αg' E N φ)))
    (h₄ : IsIso (Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight ag TY TY' αg
      (Rf.obj E) N))
    (h₅ : IsIso (adjunctionTensorMap af' TY' TX' αf' K' N)) :
    IsIso (Rg.map (TY'.map ((Stacks.CategoryTheory.BaseChange.map af af' eg ef E ≫
      Rf'.map φ) ×ₘ 𝟙 N))) :=
  (isIso_map_tensorBaseChangeCompMap_iff af ag af' ag' eg ef TY TY' TX TX' αf αf' αg αg' E N φ
    hsq h₁ h₄ h₅).mp hψ

end Square

/-- A morphism `c` is invertible as soon as `c` tensored with an object `N` whose tensoring
functor is isomorphic to the identity is. -/
theorem isIso_of_isIso_uncurry_map_prod_id {C : Type*} [Category C] (T : C ⥤ C ⥤ C) (N : C)
    (e : T.flip.obj N ≅ 𝟭 C) {a b : C} (c : a ⟶ b)
    (h : IsIso ((Functor.uncurry.obj T).map (c ×ₘ 𝟙 N))) : IsIso c := by
  have h' : IsIso ((T.flip.obj N).map c) := by
    have hc : (Functor.uncurry.obj T).map (c ×ₘ 𝟙 N) = (T.flip.obj N).map c := by
      simp
    rwa [hc] at h
  exact (NatIso.isIso_map_iff e c).1 h'

end Stacks.CategoryTheory.KunnethBaseChange

end
