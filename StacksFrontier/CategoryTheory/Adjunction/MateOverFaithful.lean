module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Mates computed over forgetful functors

Let `L ⊣ R` be an adjunction lying over another adjunction `L' ⊣ R'` along functors `UA` and
`UB`: the left and right adjoints commute with the `U`'s up to given isomorphisms, and `UA`
carries the unit to the unit. This file proves that the counits then correspond as well, and
that a mate formed with two such adjunctions is carried to the mate of the corresponding 2-cell
downstairs. The typical instance is a pullback of sheaves of modules lying over the inverse image
of sheaves of sets along the forgetful functors, where a statement about mates of sheaves of
modules can then be checked on underlying sheaves of sets.

## Main results

* `CategoryTheory.Adjunction.map_counit_app_of_map_unit_app`: if `UA` carries the unit of
  `L ⊣ R` to that of `L' ⊣ R'`, then `UB` carries the counit to the counit.
* `CategoryTheory.Adjunction.map_mateEquiv_symm_natTrans_app`: a mate, for two adjunctions lying
  over adjunctions downstairs, of a 2-cell lying over a 2-cell downstairs, lies over the mate of
  that 2-cell.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Adjunction

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {A' : Type u₃} [Category.{v₃} A'] {B' : Type u₄} [Category.{v₄} B']
  {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
  {UA : A ⥤ A'} {UB : B ⥤ B'}

/-- If an adjunction `L ⊣ R` lies over an adjunction `L' ⊣ R'` along functors `UA` and `UB`, in
the sense that `UA` carries the unit to the unit through isomorphisms `ρ : L ⋙ UB ≅ UA ⋙ L'` and
`e : R ⋙ UA ≅ UB ⋙ R'`, then it carries the counit to the counit through the same
isomorphisms. -/
theorem map_counit_app_of_map_unit_app (adj : L ⊣ R) (adj' : L' ⊣ R')
    (ρ : L ⋙ UB ≅ UA ⋙ L') (e : R ⋙ UA ≅ UB ⋙ R')
    (hunit : ∀ a, UA.map (adj.unit.app a) ≫ e.hom.app (L.obj a) ≫ R'.map (ρ.hom.app a) =
      adj'.unit.app (UA.obj a)) (b : B) :
    ρ.inv.app (R.obj b) ≫ UB.map (adj.counit.app b) =
      L'.map (e.hom.app b) ≫ adj'.counit.app (UB.obj b) := by
  apply (adj'.homEquiv _ _).injective
  have h1 : adj'.homEquiv (UA.obj (R.obj b)) (UB.obj b)
      (L'.map (e.hom.app b) ≫ adj'.counit.app (UB.obj b)) = e.hom.app b := by
    simp [Adjunction.homEquiv_unit]
  refine Eq.trans ?_ h1.symm
  rw [Adjunction.homEquiv_unit, ← hunit (R.obj b), R'.map_comp, Category.assoc,
    Category.assoc, ← R'.map_comp_assoc (ρ.hom.app (R.obj b)), Iso.hom_inv_id_app, R'.map_id,
    Category.id_comp]
  have h : e.hom.app (L.obj (R.obj b)) ≫ R'.map (UB.map (adj.counit.app b)) =
      UA.map (R.map (adj.counit.app b)) ≫ e.hom.app b :=
    (e.hom.naturality (adj.counit.app b)).symm
  rw [h, ← UA.map_comp_assoc, Adjunction.right_triangle_components]
  exact (congrArg (· ≫ e.hom.app b) (UA.map_id _)).trans (Category.id_comp _)

section OverFaithful

universe w₁ w₂ w₃ w₄ x₁ x₂ x₃ x₄ w₅ w₆ w₇ w₈ x₅ x₆ x₇ x₈

variable {MX : Type x₁} [Category.{w₁} MX] {MY : Type x₂} [Category.{w₂} MY]
  {MX' : Type x₃} [Category.{w₃} MX'] {MY' : Type x₄} [Category.{w₄} MY']
  {SX : Type x₅} [Category.{w₅} SX] {SY : Type x₆} [Category.{w₆} SY]
  {SX' : Type x₇} [Category.{w₇} SX'] {SY' : Type x₈} [Category.{w₈} SY']
  {fs : MX ⥤ MY} {fs' : MX' ⥤ MY'} {gu : MY ⥤ MY'} {gu' : MX ⥤ MX'}
  {gs : MY' ⥤ MY} {gs' : MX' ⥤ MX}
  {φs : SX ⥤ SY} {φs' : SX' ⥤ SY'} {γu : SY ⥤ SY'} {γu' : SX ⥤ SX'}
  {γs : SY' ⥤ SY} {γs' : SX' ⥤ SX}
  {UX : MX ⥤ SX} {UY : MY ⥤ SY} {UX' : MX' ⥤ SX'} {UY' : MY' ⥤ SY'}

/-- **A mate computed over forgetful functors.** Let `θ : gs' ⋙ fs ⟶ fs' ⋙ gs` be a 2-cell
between composites of right adjoints, and `β` its mate for the adjunctions `gu' ⊣ gs'` and
`gu ⊣ gs`. Suppose all of this lies, along functors `UX, UY, UX', UY'`, over the same kind of
data `τ`, `a' : γu' ⊣ γs'`, `a : γu ⊣ γs`: the four right adjoints and the two left adjoints
commute with the `U`'s up to the isomorphisms `eF, eF', eG, eG', ρ, ρ'`, the units of the two
adjunctions correspond, and `θ` corresponds to `τ`. Then `UY'` carries `β` to the mate of `τ`,
up to those isomorphisms. -/
theorem map_mateEquiv_symm_natTrans_app (ag : gu ⊣ gs) (ag' : gu' ⊣ gs') (a : γu ⊣ γs)
    (a' : γu' ⊣ γs') (θ : TwoSquare gs' fs' fs gs) (τ : TwoSquare γs' φs' φs γs)
    (eF : fs ⋙ UY ≅ UX ⋙ φs) (eF' : fs' ⋙ UY' ≅ UX' ⋙ φs') (eG : gs ⋙ UY ≅ UY' ⋙ γs)
    (eG' : gs' ⋙ UX ≅ UX' ⋙ γs') (ρ : gu ⋙ UY' ≅ UY ⋙ γu) (ρ' : gu' ⋙ UX' ≅ UX ⋙ γu')
    (hunit : ∀ N, UY.map (ag.unit.app N) ≫ eG.hom.app (gu.obj N) ≫ γs.map (ρ.hom.app N) =
      a.unit.app (UY.obj N))
    (hunit' : ∀ M, UX.map (ag'.unit.app M) ≫ eG'.hom.app (gu'.obj M) ≫ γs'.map (ρ'.hom.app M) =
      a'.unit.app (UX.obj M))
    (hθ : ∀ N, UY.map (θ.natTrans.app N) ≫ eG.hom.app (fs'.obj N) ≫ γs.map (eF'.hom.app N) =
      eF.hom.app (gs'.obj N) ≫ φs.map (eG'.hom.app N) ≫ τ.natTrans.app (UX'.obj N))
    (M : MX) :
    UY'.map (((mateEquiv ag' ag).symm θ).natTrans.app M) =
      ρ.hom.app (fs.obj M) ≫ γu.map (eF.hom.app M) ≫
        ((mateEquiv a' a).symm τ).natTrans.app (UX.obj M) ≫ φs'.map (ρ'.inv.app M) ≫
          eF'.inv.app (gu'.obj M) := by
  have h1 : ∀ {b b' : MY} (x : b ⟶ b'),
      UY'.map (gu.map x) = ρ.hom.app b ≫ γu.map (UY.map x) ≫ ρ.inv.app b' := fun x => by
    have := ρ.hom.naturality x
    simp only [Functor.comp_map] at this
    rw [← Category.assoc, ← this, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have h2 : ∀ {b b' : MX} (x : b ⟶ b'),
      UY.map (fs.map x) = eF.hom.app b ≫ φs.map (UX.map x) ≫ eF.inv.app b' := fun x => by
    have := eF.hom.naturality x
    simp only [Functor.comp_map] at this
    rw [← Category.assoc, ← this, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have hu : UX.map (ag'.unit.app M) =
      a'.unit.app (UX.obj M) ≫ γs'.map (ρ'.inv.app M) ≫ eG'.inv.app (gu'.obj M) := by
    rw [← hunit' M]
    simp [← Functor.map_comp_assoc]
  have hθ' : UY.map (θ.natTrans.app (gu'.obj M)) =
      eF.hom.app (gs'.obj (gu'.obj M)) ≫ φs.map (eG'.hom.app (gu'.obj M)) ≫
        τ.natTrans.app (UX'.obj (gu'.obj M)) ≫ γs.map (eF'.inv.app (gu'.obj M)) ≫
          eG.inv.app (fs'.obj (gu'.obj M)) := by
    rw [← reassoc_of% (hθ (gu'.obj M))]
    simp [← Functor.map_comp_assoc]
  have hc := map_counit_app_of_map_unit_app ag a ρ eG hunit (fs'.obj (gu'.obj M))
  have hτ := τ.natTrans.naturality (ρ'.inv.app M)
  simp only [Functor.comp_map] at hτ
  have hm : ((mateEquiv ag' ag).symm θ).natTrans.app M =
      gu.map (fs.map (ag'.unit.app M)) ≫ gu.map (θ.natTrans.app (gu'.obj M)) ≫
        ag.counit.app (fs'.obj (gu'.obj M)) := by simp [mateEquiv]
  have hm' : ((mateEquiv a' a).symm τ).natTrans.app (UX.obj M) =
      γu.map (φs.map (a'.unit.app (UX.obj M))) ≫ γu.map (τ.natTrans.app (γu'.obj (UX.obj M))) ≫
        a.counit.app (φs'.obj (γu'.obj (UX.obj M))) := by simp [mateEquiv]
  rw [hm, hm', UY'.map_comp, UY'.map_comp, h1, h1, h2, hu, hθ']
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc, Functor.comp_obj]
  rw [hc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
    Functor.comp_obj, Category.comp_id]
  simp only [Functor.comp_obj] at hτ
  have hτ' : φs.map (a'.unit.app (UX.obj M) ≫ γs'.map (ρ'.inv.app M)) ≫
      τ.natTrans.app (UX'.obj (gu'.obj M)) ≫ γs.map (eF'.inv.app (gu'.obj M)) =
      φs.map (a'.unit.app (UX.obj M)) ≫ τ.natTrans.app (γu'.obj (UX.obj M)) ≫
        γs.map (φs'.map (ρ'.inv.app M) ≫ eF'.inv.app (gu'.obj M)) := by
    rw [Functor.map_comp, Category.assoc, reassoc_of% hτ, Functor.map_comp]
  rw [hτ']
  simp only [Functor.map_comp, Category.assoc, Adjunction.counit_naturality,
    Adjunction.counit_naturality_assoc]
  rfl

end OverFaithful

end CategoryTheory.Adjunction
