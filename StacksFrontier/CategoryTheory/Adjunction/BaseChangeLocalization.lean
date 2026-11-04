module

public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare

/-!
# The derived base change map at a localized object

Consider a square of categories in which the underived pullbacks `pf, pf'` are left adjoint to
underived pushforwards `qf, qf'` and the derived pullbacks `Pf, Pf'` are left adjoint to derived
pushforwards `Rf, Rf'`, the derived categories being reached from the underived ones by
localization functors `Q`. The derived functors are tied to the underived ones by the derived
units `q ⋙ Q ⟶ Q ⋙ R` and by the comparisons `Q ⋙ P ⟶ p ⋙ Q`, and the derived counit is the
underived one read through them ([Stacks, Tag 0FPI]). This file computes the derived base change
map `Stacks.CategoryTheory.BaseChange.map` at a localized object `Q I` through the underived base
change map at `I`.

## Main results

* `Stacks.CategoryTheory.BaseChange.map_comp_localization`: the derived base change map at
  `Q I`, between the derived unit along `f` and the comparison along `g'`, is the comparison
  along `g`, the localization of the underived base change map at `I` and the derived unit along
  `f'`.
* `Stacks.CategoryTheory.BaseChange.map_trans_symm_refl`: the base change map only depends on
  the composite comparison of the two composite pullbacks.

## Implementation notes

The statement holds for every object `I`, with no K-injectivity: it only identifies two composite
maps. It is used where the derived unit along `f` and the comparisons are invertible, so that the
derived base change map at `Q I` is invertible exactly when the localization of the underived base
change map followed by the derived unit along `f'` is. The proof compares adjuncts under
`Pf' ⊣ Rf'`, where both sides become composites of comparisons, counits and the two square
isomorphisms.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory.BaseChange

variable {HY HX HY' HX' DY DX DY' DX' : Type*}
  [Category HY] [Category HX] [Category HY'] [Category HX']
  [Category DY] [Category DX] [Category DY'] [Category DX']
  {QY : HY ⥤ DY} {QX : HX ⥤ DX} {QY' : HY' ⥤ DY'} {QX' : HX' ⥤ DX'}
  {pf : HY ⥤ HX} {qf : HX ⥤ HY} {pf' : HY' ⥤ HX'} {qf' : HX' ⥤ HY'}
  {pg : HY ⥤ HY'} {pg' : HX ⥤ HX'}
  {Pf : DY ⥤ DX} {Rf : DX ⥤ DY} {Pf' : DY' ⥤ DX'} {Rf' : DX' ⥤ DY'}
  {Pg : DY ⥤ DY'} {Pg' : DX ⥤ DX'}
  (af : pf ⊣ qf) (af' : pf' ⊣ qf') (Af : Pf ⊣ Rf) (Af' : Pf' ⊣ Rf')
  (cf : qf ⋙ QY ⟶ QX ⋙ Rf) (cf' : qf' ⋙ QY' ⟶ QX' ⋙ Rf')
  (cmpf : QY ⋙ Pf ⟶ pf ⋙ QX) (cmpf' : QY' ⋙ Pf' ⟶ pf' ⋙ QX')
  (cmpg : QY ⋙ Pg ⟶ pg ⋙ QY') (cmpg' : QX ⋙ Pg' ⟶ pg' ⋙ QX')
  (m : pg ⋙ pf' ≅ pf ⋙ pg') (S : Pg ⋙ Pf' ≅ Pf ⋙ Pg')

/-- **The base change map of derived functors at a localized object.** Let `af, af'` be underived
adjunctions `pf ⊣ qf`, `pf' ⊣ qf'` and `Af, Af'` derived adjunctions `Pf ⊣ Rf`, `Pf' ⊣ Rf'`,
related by the derived units `cf : qf ⋙ QY ⟶ QX ⋙ Rf` and the comparisons
`cmp : Q ⋙ P ⟶ p ⋙ Q` of the derived pullbacks with the underived ones, such that the derived
counits factor through the underived ones (`hcf`, `hcf'`), and let the derived square
isomorphism `S` be compatible with the underived one `m` (`hS`). Then at the localization
`QX I` of an arbitrary object, the derived base change map, preceded by `Pg` of the derived unit
and followed by `Rf'` of the comparison along `g'`, is the comparison along `g` followed by the
localization of the underived base change map and by the derived unit along `f'`. -/
theorem map_comp_localization
    (hcf : ∀ K, Pf.map (cf.app K) ≫ Af.counit.app (QX.obj K) =
      cmpf.app (qf.obj K) ≫ QX.map (af.counit.app K))
    (hcf' : ∀ K, Pf'.map (cf'.app K) ≫ Af'.counit.app (QX'.obj K) =
      cmpf'.app (qf'.obj K) ≫ QX'.map (af'.counit.app K))
    (hS : ∀ K, S.hom.app (QY.obj K) ≫ Pg'.map (cmpf.app K) ≫ cmpg'.app (pf.obj K) =
      Pf'.map (cmpg.app K) ≫ cmpf'.app (pg.obj K) ≫ QX'.map (m.hom.app K))
    (I : HX) :
    Pg.map (cf.app I) ≫ map Af Af' S (Iso.refl _) (QX.obj I) ≫ Rf'.map (cmpg'.app I) =
      cmpg.app (qf.obj I) ≫ QY'.map (map af af' m (Iso.refl _) I) ≫ cf'.app (pg'.obj I) := by
  apply (Af'.homEquiv _ _).symm.injective
  have hbc := homEquiv_symm_map Af Af' S (Iso.refl _) (QX.obj I)
  have hbca := homEquiv_symm_map af af' m (Iso.refl _) I
  rw [Adjunction.homEquiv_counit] at hbc hbca
  simp only [Iso.refl_inv, NatTrans.id_app, Category.id_comp] at hbc hbca
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc]
  -- LHS
  rw [Af'.counit_naturality (cmpg'.app I)]
  dsimp only [Functor.comp_obj]
  rw [reassoc_of% hbc]
  have hSn := S.hom.naturality (cf.app I)
  dsimp at hSn
  rw [reassoc_of% hSn, ← Pg'.map_comp_assoc, hcf, Pg'.map_comp_assoc]
  have hcn := cmpg'.naturality (af.counit.app I)
  dsimp at hcn
  rw [hcn, reassoc_of% (hS (qf.obj I))]
  -- RHS
  rw [hcf' (pg'.obj I)]
  have hcn' := cmpf'.naturality (map af af' m (Iso.refl _) I)
  rw [reassoc_of% hcn', ← QX'.map_comp, ← QX'.map_comp, hbca]

/-- The base change map does not see how an isomorphism of the two composite pullbacks is split
into two identifications with a third functor. -/
theorem map_trans_symm_refl {A B A' B' : Type*} [Category A] [Category B] [Category A']
    [Category B']
    {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'} {Lg : A ⥤ A'} {Lg' : B ⥤ B'}
    {Lc : A ⥤ B'} (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
    (K : B) :
    map adjf adjf' (eg ≪≫ ef.symm) (Iso.refl _) K = map adjf adjf' eg ef K := by
  simp only [map, twoSquare, pullbackComparison, Iso.trans_hom, Iso.symm_hom, Iso.refl_inv,
    Category.comp_id]

end Stacks.CategoryTheory.BaseChange
