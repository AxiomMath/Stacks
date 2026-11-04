module

public import StacksFrontier.CategoryTheory.Adjunction.KunnethBaseChangeComp
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquareMates

/-!
# The Künneth map of a base change square, restricted along a second square

In the situation of `StacksFrontier.CategoryTheory.Adjunction.KunnethBaseChangeComp`, the map
`E ⊗ Lf Rg N ⟶ Rg'(K' ⊗ Lf' N)` attached to `φ : Lg' E ⟶ K'` is the transpose under
`Lg' ⊣ Rg'` of `α_{g'} ≫ (φ ⊗ (Lg' Lf Rg N ≅ Lf' Lg Rg N ⟶ Lf' N))`, a map built from pullbacks
alone.  Consequently its restriction along a second square `Lu ⋙ Lh ≅ Lg' ⋙ Lu'` stacked on
top, followed by the base change map of that square, is the map attached to the outer square and
to the restriction of `φ`, up to the tensor comparisons of `Lu` and `Lu'`.  This is the
compatibility that makes the invertibility of the Künneth map of Stacks 0DKH local on `X`.

## Main results

* `Stacks.CategoryTheory.KunnethBaseChange.homEquiv_symm_tensorBaseChangeCompMap`
* `Stacks.CategoryTheory.KunnethBaseChange.map_tensorBaseChangeCompMap_comp_baseChange`
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace Stacks.CategoryTheory.KunnethBaseChange

section Transpose

variable {CY CX CY' CX' : Type*} [Category CY] [Category CX] [Category CY'] [Category CX']
  {Lf : CY ⥤ CX} {Lg : CY ⥤ CY'} {Rg : CY' ⥤ CY}
  {Lf' : CY' ⥤ CX'} {Lg' : CX ⥤ CX'} {Rg' : CX' ⥤ CX} {Lc : CY ⥤ CX'}
  (ag : Lg ⊣ Rg) (ag' : Lg' ⊣ Rg')
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  (TX : CX × CX ⥤ CX) (TX' : CX' × CX' ⥤ CX') (αg' : TX ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ TX')

/-- **The Künneth map is the transpose of a map built from pullbacks.**  Under `Lg' ⊣ Rg'`,
`tensorBaseChangeCompMap` is the comparison `α_{g'}` followed by `φ` in the first factor and, in
the second, the identification `Lg' Lf ≅ Lf' Lg` followed by `Lf'` of the counit of
`Lg ⊣ Rg`. -/
theorem homEquiv_symm_tensorBaseChangeCompMap (E : CX) (N : CY') {K' : CX'}
    (φ : Lg'.obj E ⟶ K') :
    (ag'.homEquiv _ _).symm (tensorBaseChangeCompMap ag ag' eg ef TX TX' αg' E N φ) =
      αg'.app (E, Lf.obj (Rg.obj N)) ≫
        TX'.map (φ ×ₘ (ef.hom.app (Rg.obj N) ≫ eg.inv.app (Rg.obj N) ≫
          Lf'.map (ag.counit.app N))) := by
  have hb := Stacks.CategoryTheory.BaseChange.homEquiv_symm_map ag ag' ef eg N
  rw [Adjunction.homEquiv_counit] at hb
  have hr : (ag'.homEquiv _ _).symm (Stacks.Cohomology.DerivedKunneth.adjunctionTensorMapRight ag'
      TX TX' αg' E (Lf'.obj N)) =
      αg'.app (E, Rg'.obj (Lf'.obj N)) ≫ TX'.map (𝟙 (Lg'.obj E) ×ₘ ag'.counit.app (Lf'.obj N)) :=
    Equiv.symm_apply_apply _ _
  have hn := αg'.naturality (𝟙 E ×ₘ Stacks.CategoryTheory.BaseChange.map ag ag' ef eg N)
  simp only [Functor.comp_map, Functor.prod_map, CategoryTheory.Functor.map_id] at hn
  rw [tensorBaseChangeCompMap, ← Category.assoc, Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_naturality_left_symm, hr, ← Category.assoc
      (Lg'.map (TX.map _)), hn]
  simp only [Category.assoc, ← TX'.map_comp, prod_comp, Category.id_comp, Category.comp_id]
  simpa using congrArg (fun t => αg'.app (E, Lf.obj (Rg.obj N)) ≫ TX'.map (φ ×ₘ t)) hb

end Transpose

section Restriction

variable {CY CX CY' CX' CU CU' : Type*} [Category CY] [Category CX] [Category CY']
  [Category CX'] [Category CU] [Category CU']
  {Lf : CY ⥤ CX} {Lg : CY ⥤ CY'} {Rg : CY' ⥤ CY}
  {Lf' : CY' ⥤ CX'} {Lg' : CX ⥤ CX'} {Rg' : CX' ⥤ CX} {Lc : CY ⥤ CX'}
  {Lh : CU ⥤ CU'} {Rh : CU' ⥤ CU} {Lu : CX ⥤ CU} {Lu' : CX' ⥤ CU'} {Ld : CX ⥤ CU'}
  {LfU : CY ⥤ CU} {Lf'U : CY' ⥤ CU'} {LcU : CY ⥤ CU'}
  (ag : Lg ⊣ Rg) (ag' : Lg' ⊣ Rg') (ah : Lh ⊣ Rh)
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  (egU : Lg ⋙ Lf'U ≅ LcU) (efU : LfU ⋙ Lh ≅ LcU)
  (eu : Lu ⋙ Lh ≅ Ld) (eu' : Lg' ⋙ Lu' ≅ Ld)
  (c : Lf ⋙ Lu ≅ LfU) (c' : Lf' ⋙ Lu' ≅ Lf'U)
  (TX : CX × CX ⥤ CX) (TX' : CX' × CX' ⥤ CX') (TU : CU × CU ⥤ CU) (TU' : CU' × CU' ⥤ CU')
  (αg' : TX ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ TX') (αh : TU ⋙ Lh ⟶ Lh.prod Lh ⋙ TU')
  (αu : TX ⋙ Lu ⟶ Lu.prod Lu ⋙ TU) (αu' : TX' ⋙ Lu' ⟶ Lu'.prod Lu' ⋙ TU')

/-- **Restriction of the Künneth map along a square stacked on top.**  Let `Lu ⋙ Lh ≅ Lg' ⋙ Lu'`
be a second square on top of the square `(Lf, Lg, Lf', Lg')`, and let the outer square
`(LfU, Lg, Lf'U, Lh)` have composites identified with `Lf ⋙ Lu` and `Lf' ⋙ Lu'` compatibly
(`hcube`), with the tensor comparisons of the second square compatible (`hhex`).  Then `Lu` of the
map attached to `φ`, followed by the base change map of the second square and the tensor
comparison of `Lu'`, is the tensor comparison of `Lu` followed by the map attached to the outer
square and to `Lh Lu E ≅ Lu' Lg' E ⟶ Lu' K'`. -/
theorem map_tensorBaseChangeCompMap_comp_baseChange (E : CX) (N : CY') {K' : CX'}
    (φ : Lg'.obj E ⟶ K')
    (hcube : egU.hom.app (Rg.obj N) ≫ efU.inv.app (Rg.obj N) =
      c'.inv.app (Lg.obj (Rg.obj N)) ≫
        Lu'.map (eg.hom.app (Rg.obj N) ≫ ef.inv.app (Rg.obj N)) ≫
          (eu'.hom.app (Lf.obj (Rg.obj N)) ≫ eu.inv.app (Lf.obj (Rg.obj N))) ≫
            Lh.map (c.hom.app (Rg.obj N)))
    (hhex : Stacks.AffineProjectionFormula.TensorComparisonCompatible eu eu' TX TU TX' TU'
      αg' αh αu αu' E (Lf.obj (Rg.obj N))) :
    Lu.map (tensorBaseChangeCompMap ag ag' eg ef TX TX' αg' E N φ) ≫
        Stacks.CategoryTheory.BaseChange.map ag' ah eu eu' (TX'.obj (K', Lf'.obj N)) ≫
          Rh.map (αu'.app (K', Lf'.obj N) ≫ TU'.map (𝟙 (Lu'.obj K') ×ₘ c'.hom.app N)) =
      (αu.app (E, Lf.obj (Rg.obj N)) ≫ TU.map (𝟙 (Lu.obj E) ×ₘ c.hom.app (Rg.obj N))) ≫
        tensorBaseChangeCompMap ag ah egU efU TU TU' αh (Lu.obj E) N
          ((eu.hom ≫ eu'.inv).app E ≫ Lu'.map φ) := by
  apply (ah.homEquiv _ _).symm.injective
  rw [← Category.assoc (Lu.map _), Adjunction.homEquiv_naturality_right_symm,
    Stacks.CategoryTheory.BaseChange.homEquiv_symm_map_comp_map,
    Adjunction.homEquiv_naturality_left_symm, homEquiv_symm_tensorBaseChangeCompMap,
    homEquiv_symm_tensorBaseChangeCompMap]
  -- the hexagon of the second square at `(E, Lf Rg N)`
  unfold Stacks.AffineProjectionFormula.TensorComparisonCompatible at hhex
  simp only [Stacks.AffineProjectionFormula.squareCompositeIso_hom_app] at hhex
  -- the second-factor map of the outer square, through `hcube`
  have hv : Lh.map (c.hom.app (Rg.obj N)) ≫ efU.hom.app (Rg.obj N) ≫ egU.inv.app (Rg.obj N) ≫
      Lf'U.map (ag.counit.app N) =
      (eu.hom.app _ ≫ eu'.inv.app _) ≫ Lu'.map (ef.hom.app (Rg.obj N) ≫ eg.inv.app (Rg.obj N) ≫
        Lf'.map (ag.counit.app N)) ≫ c'.hom.app N := by
    have h1 : efU.hom.app (Rg.obj N) ≫ egU.inv.app (Rg.obj N) =
        Lh.map (c.inv.app (Rg.obj N)) ≫
          (eu.hom.app (Lf.obj (Rg.obj N)) ≫ eu'.inv.app (Lf.obj (Rg.obj N))) ≫
            Lu'.map (ef.hom.app (Rg.obj N) ≫ eg.inv.app (Rg.obj N)) ≫
              c'.hom.app (Lg.obj (Rg.obj N)) := by
      rw [← cancel_epi (egU.hom.app (Rg.obj N) ≫ efU.inv.app (Rg.obj N))]
      conv_rhs => rw [hcube]
      have e1 : Lh.map (c.hom.app (Rg.obj N)) ≫ Lh.map (c.inv.app (Rg.obj N)) = 𝟙 _ :=
        (Lh.mapIso (c.app (Rg.obj N))).hom_inv_id
      have e2 : Lu'.map (eg.hom.app (Rg.obj N) ≫ ef.inv.app (Rg.obj N)) ≫
          Lu'.map (ef.hom.app (Rg.obj N) ≫ eg.inv.app (Rg.obj N)) = 𝟙 _ := by
        rw [← Lu'.map_comp]
        simp
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app]
      rw [reassoc_of% e1, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc,
        reassoc_of% e2, Iso.inv_hom_id_app]
      rfl
    have h2 : Lu'.map (Lf'.map (ag.counit.app N)) ≫ c'.hom.app N =
        c'.hom.app (Lg.obj (Rg.obj N)) ≫ Lf'U.map (ag.counit.app N) :=
      c'.hom.naturality (ag.counit.app N)
    rw [reassoc_of% h1]
    simp only [Category.assoc, ← Lh.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, Lu'.map_comp]
    rw [h2]
  have hn := αh.naturality (𝟙 (Lu.obj E) ×ₘ c.hom.app (Rg.obj N))
  simp only [Functor.comp_map, Functor.prod_map, CategoryTheory.Functor.map_id] at hn
  have hn' := αu'.naturality (φ ×ₘ (ef.hom.app (Rg.obj N) ≫ eg.inv.app (Rg.obj N) ≫
    Lf'.map (ag.counit.app N)))
  simp only [Functor.comp_map, Functor.prod_map] at hn'
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, ← TU'.map_comp, prod_comp, Category.id_comp, reassoc_of% hn',
    ← TU'.map_comp, prod_comp, Category.comp_id]
  rw [← reassoc_of% hhex]
  simp only [← TU'.map_comp, prod_comp, Category.assoc]
  rw [hv, NatTrans.comp_app]
  simp only [Category.assoc]

end Restriction

end Stacks.CategoryTheory.KunnethBaseChange

end
