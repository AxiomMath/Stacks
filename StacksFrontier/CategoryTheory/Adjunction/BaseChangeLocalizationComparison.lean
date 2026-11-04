module

public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare

/-!
# A base change map of localized adjunctions through the base change map before localization

Consider two squares of adjunctions of the shape of `Stacks.CategoryTheory.BaseChange.map`: an
"underived" one, `pf ⊣ qf`, `pf' ⊣ qf'` with horizontal functors `pg`, `pg'`, and a "derived" one,
`Lf ⊣ Rf`, `Lf' ⊣ Rf'` with horizontal functors `Lg`, `Lg'`, together with functors `Q` from each
corner of the first square to the corresponding corner of the second (localizations, in the
application). Suppose given comparisons `c : Q ⋙ L ⟶ p ⋙ Q` of the left adjoints and units
`u : q ⋙ Q ⟶ Q ⋙ R` of the right adjoints such that

* the counits are compatible: `L (u K) ≫ ε (Q K) = c (q K) ≫ Q (ε K)`, and
* the comparisons of the composites around the squares are compatible with the comparisons.

Then the derived base change map, precomposed with `Lg` of the unit and followed by `Rf'` of the
comparison along `pg'`, is the comparison along `pg`, followed by `Q` of the underived base change
map and the unit of `pf' ⊣ qf'`. This is the formal part of the statement that the derived base
change map of a square of ringed topoi is induced by the base change map of modules.

## Main results

* `Stacks.CategoryTheory.BaseChange.map_comp_comparison_eq`: the identity above.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory.BaseChange

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

variable {HY : Type u₁} {HX : Type u₂} {HY' : Type u₃} {HX' : Type u₄}
  [Category.{v₁} HY] [Category.{v₂} HX] [Category.{v₃} HY'] [Category.{v₄} HX']
  {DY : Type u₅} {DX : Type u₆} {DY' : Type u₇} {DX' : Type u₈}
  [Category.{v₅} DY] [Category.{v₆} DX] [Category.{v₇} DY'] [Category.{v₈} DX']
  {pf : HY ⥤ HX} {qf : HX ⥤ HY} {pf' : HY' ⥤ HX'} {qf' : HX' ⥤ HY'}
  {pg : HY ⥤ HY'} {pg' : HX ⥤ HX'} {pc : HY ⥤ HX'}
  (af : pf ⊣ qf) (af' : pf' ⊣ qf') (egu : pg ⋙ pf' ≅ pc) (efu : pf ⋙ pg' ≅ pc)
  {Lf : DY ⥤ DX} {Rf : DX ⥤ DY} {Lf' : DY' ⥤ DX'} {Rf' : DX' ⥤ DY'}
  {Lg : DY ⥤ DY'} {Lg' : DX ⥤ DX'} {Lc : DY ⥤ DX'}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  {QY : HY ⥤ DY} {QX : HX ⥤ DX} {QY' : HY' ⥤ DY'} {QX' : HX' ⥤ DX'}
  (cf : QY ⋙ Lf ⟶ pf ⋙ QX) (cf' : QY' ⋙ Lf' ⟶ pf' ⋙ QX')
  (cg : QY ⋙ Lg ⟶ pg ⋙ QY') (cg' : QX ⋙ Lg' ⟶ pg' ⋙ QX') (cc : QY ⋙ Lc ⟶ pc ⋙ QX')
  (uf : qf ⋙ QY ⟶ QX ⋙ Rf) (uf' : qf' ⋙ QY' ⟶ QX' ⋙ Rf')

/-- **The derived base change map through the underived one.** Under compatibility of the counits
with the units and comparisons, and of the composites around the squares with the comparisons,
the derived base change map at `Q K`, precomposed with `Lg` of the unit at `K` and followed by
`Rf'` of the comparison along `pg'`, is the comparison along `pg` followed by `Q` of the
underived base change map at `K` and the unit of `pf' ⊣ qf'`. -/
theorem map_comp_comparison_eq
    (hf : ∀ K : HX, Lf.map (uf.app K) ≫ adjf.counit.app (QX.obj K) =
      cf.app (qf.obj K) ≫ QX.map (af.counit.app K))
    (hf' : ∀ K : HX', Lf'.map (uf'.app K) ≫ adjf'.counit.app (QX'.obj K) =
      cf'.app (qf'.obj K) ≫ QX'.map (af'.counit.app K))
    (heg : ∀ M : HY, eg.hom.app (QY.obj M) ≫ cc.app M =
      Lf'.map (cg.app M) ≫ cf'.app (pg.obj M) ≫ QX'.map (egu.hom.app M))
    (hef : ∀ M : HY, ef.hom.app (QY.obj M) ≫ cc.app M =
      Lg'.map (cf.app M) ≫ cg'.app (pf.obj M) ≫ QX'.map (efu.hom.app M))
    (K : HX) :
    Lg.map (uf.app K) ≫ map adjf adjf' eg ef (QX.obj K) ≫ Rf'.map (cg'.app K) =
      cg.app (qf.obj K) ≫ QY'.map (map af af' egu efu K) ≫ uf'.app (pg'.obj K) := by
  have hL : (adjf'.homEquiv _ _).symm
      (Lg.map (uf.app K) ≫ map adjf adjf' eg ef (QX.obj K) ≫ Rf'.map (cg'.app K)) =
      eg.hom.app (QY.obj (qf.obj K)) ≫ ef.inv.app (QY.obj (qf.obj K)) ≫
        Lg'.map (cf.app (qf.obj K)) ≫ Lg'.map (QX.map (af.counit.app K)) ≫ cg'.app K := by
    have hu : ∀ u : QY.obj (qf.obj K) ⟶ Rf.obj (QX.obj K),
        (adjf'.homEquiv (Lg.obj (QY.obj (qf.obj K))) (Lg'.obj (QX.obj K))).symm
          (Lg.map u ≫ map adjf adjf' eg ef (QX.obj K)) =
        eg.hom.app _ ≫ ef.inv.app _ ≫ Lg'.map ((adjf.homEquiv _ _).symm u) := fun u => by
      rw [Adjunction.homEquiv_naturality_left_symm, homEquiv_symm_map,
        Adjunction.homEquiv_counit, Functor.map_comp]
      have h1 := eg.hom.naturality u
      have h2 := ef.inv.naturality u
      simp only [Functor.comp_map] at h1 h2
      rw [← Category.assoc, ← Category.assoc, h1]
      simp only [Category.assoc]
      rw [← reassoc_of% h2]
    rw [← Category.assoc, Adjunction.homEquiv_naturality_right_symm]
    refine (congrArg (· ≫ cg'.app K) (hu (uf.app K))).trans ?_
    rw [Adjunction.homEquiv_counit]
    rw [hf, Functor.map_comp]
    simp only [Category.assoc]
  have h4 := homEquiv_symm_map af af' egu efu K
  rw [Adjunction.homEquiv_counit] at h4
  have hR : (adjf'.homEquiv _ _).symm
      (cg.app (qf.obj K) ≫ QY'.map (map af af' egu efu K) ≫ uf'.app (pg'.obj K)) =
      Lf'.map (cg.app (qf.obj K)) ≫ cf'.app (pg.obj (qf.obj K)) ≫
        QX'.map (egu.hom.app (qf.obj K)) ≫ QX'.map (efu.inv.app (qf.obj K)) ≫
          QX'.map (pg'.map (af.counit.app K)) := by
    rw [Adjunction.homEquiv_counit, Functor.map_comp, Functor.map_comp, Category.assoc,
      Category.assoc, hf']
    have h1 := cf'.naturality (map af af' egu efu K)
    simp only [Functor.comp_map] at h1
    rw [reassoc_of% h1, ← QX'.map_comp, h4]
    simp only [Functor.map_comp]
  have h2 : Lg'.map (QX.map (af.counit.app K)) ≫ cg'.app K =
      cg'.app (pf.obj (qf.obj K)) ≫ QX'.map (pg'.map (af.counit.app K)) :=
    cg'.naturality (af.counit.app K)
  have e : QX'.map (efu.hom.app (qf.obj K)) ≫ QX'.map (efu.inv.app (qf.obj K)) = 𝟙 _ :=
    (QX'.mapIso (efu.app (qf.obj K))).hom_inv_id
  have h3 : Lg'.map (cf.app (qf.obj K)) ≫ cg'.app (pf.obj (qf.obj K)) =
      ef.hom.app (QY.obj (qf.obj K)) ≫ cc.app (qf.obj K) ≫ QX'.map (efu.inv.app (qf.obj K)) := by
    rw [← Category.assoc (ef.hom.app _), hef]
    simp only [Category.assoc]
    rw [e]
    exact (congrArg (fun t => Lg'.map (cf.app (qf.obj K)) ≫ t)
      (Category.comp_id (cg'.app (pf.obj (qf.obj K))))).symm
  refine (adjf'.homEquiv _ _).symm.injective (hL.trans (Eq.trans ?_ hR.symm))
  rw [h2, reassoc_of% h3, Iso.inv_hom_id_app_assoc, reassoc_of% heg]

end Stacks.CategoryTheory.BaseChange
