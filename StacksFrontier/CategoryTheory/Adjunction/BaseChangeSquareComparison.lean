module

public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare

public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquareMates
/-!
# The base change map of derived adjunctions, read through the underived one

Let `pf ⊣ qf` and `pf' ⊣ qf'` be adjunctions between categories `H_X, H_Y, H_{X'}, H_{Y'}`
(degreewise pullback and direct image on homotopy categories), `pg, pg'` two further functors
(degreewise pullback along the horizontal morphisms), and `β₀ : qf ⋙ pg ⟶ pg' ⋙ qf'` the
underived base change map, i.e. the transpose of a comparison `θ₀ : pg ⋙ pf' ⟶ pf ⋙ pg'`
followed by `pg'` of the counit.  Let `Lf ⊣ Rf`, `Lf' ⊣ Rf'` be adjunctions between categories
`D_X, D_Y, D_{X'}, D_{Y'}` (derived categories), with functors `Q` from the first four, and
comparisons `c : Q ⋙ L ⟶ p ⋙ Q` and units `u : q ⋙ Q ⟶ Q ⋙ R` (the comparison maps of the left
derived pullbacks and the units of the right derived direct images).

If the derived counits are induced by the underived ones through `c` and `u` (Stacks 0FPI), and
the comparison of the two iterated derived pullbacks is induced by `θ₀` through `c`, then the
derived base change map `Lg Rf (Q K) ⟶ Rf' Lg' (Q K)`, composed on the two sides with `u` and
`c`, is `Q` of the underived base change map.  So the derived base change map is invertible at
`Q K` as soon as the underived one is invertible at `K` and the relevant components of `u` and
`c` are; this is how étale and flat base change for the derived direct image is deduced from the
underived statement.

## Main results

* `Stacks.CategoryTheory.BaseChange.map_comparison`: the derived base change map at `Q K`, read
  through `u` and `c`, is `Q` of the underived base change map at `K`.
* `Stacks.CategoryTheory.BaseChange.isIso_map_of_isIso`: hence its invertibility.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory.BaseChange

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

variable {DY : Type u₁} {DX : Type u₂} {DY' : Type u₃} {DX' : Type u₄}
  [Category.{v₁} DY] [Category.{v₂} DX] [Category.{v₃} DY'] [Category.{v₄} DX']
  {HY : Type u₅} {HX : Type u₆} {HY' : Type u₇} {HX' : Type u₈}
  [Category.{v₅} HY] [Category.{v₆} HX] [Category.{v₇} HY'] [Category.{v₈} HX']
  {QY : HY ⥤ DY} {QX : HX ⥤ DX} {QY' : HY' ⥤ DY'} {QX' : HX' ⥤ DX'}
  {pf : HY ⥤ HX} {qf : HX ⥤ HY} {pf' : HY' ⥤ HX'} {qf' : HX' ⥤ HY'}
  {pg : HY ⥤ HY'} {pg' : HX ⥤ HX'}
  (a : pf ⊣ qf) (a' : pf' ⊣ qf') (θ₀ : pg ⋙ pf' ⟶ pf ⋙ pg') (β₀ : qf ⋙ pg ⟶ pg' ⋙ qf')
  {Lf : DY ⥤ DX} {Rf : DX ⥤ DY} {Lf' : DY' ⥤ DX'} {Rf' : DX' ⥤ DY'}
  {Lg : DY ⥤ DY'} {Lg' : DX ⥤ DX'} {Lc : DY ⥤ DX'}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  (cf : QY ⋙ Lf ⟶ pf ⋙ QX) (cf' : QY' ⋙ Lf' ⟶ pf' ⋙ QX')
  (cg : QY ⋙ Lg ⟶ pg ⋙ QY') (cg' : QX ⋙ Lg' ⟶ pg' ⋙ QX')
  (uf : qf ⋙ QY ⟶ QX ⋙ Rf) (uf' : qf' ⋙ QY' ⟶ QX' ⋙ Rf')

/-- **The derived base change map is induced by the underived one.**  If the counits of the two
derived adjunctions are induced by the underived counits through the comparisons `c` and the
units `u` (`hf`, `hf'`), the comparison of the two iterated derived pullbacks is induced by `θ₀`
(`hθ`), and `β₀` is the underived base change map attached to `θ₀` (`hβ`), then

`Lg (u K) ≫ (base change map at Q K) ≫ Rf' (c_{g'} K) = c_g (qf K) ≫ Q (β₀ K) ≫ u' (pg' K)`.

Both sides are compared after transposing across `Lf' ⊣ Rf'`. -/
theorem map_comparison
    (hβ : ∀ K : HX, (a'.homEquiv _ _).symm (β₀.app K) =
      θ₀.app (qf.obj K) ≫ pg'.map (a.counit.app K))
    (hf : ∀ K : HX, Lf.map (uf.app K) ≫ adjf.counit.app (QX.obj K) =
      cf.app (qf.obj K) ≫ QX.map (a.counit.app K))
    (hf' : ∀ K : HX', Lf'.map (uf'.app K) ≫ adjf'.counit.app (QX'.obj K) =
      cf'.app (qf'.obj K) ≫ QX'.map (a'.counit.app K))
    (hθ : ∀ M : HY, eg.hom.app (QY.obj M) ≫ ef.inv.app (QY.obj M) ≫ Lg'.map (cf.app M) ≫
        cg'.app (pf.obj M) =
      Lf'.map (cg.app M) ≫ cf'.app (pg.obj M) ≫ QX'.map (θ₀.app M))
    (K : HX) :
    Lg.map (uf.app K) ≫ map adjf adjf' eg ef (QX.obj K) ≫ Rf'.map (cg'.app K) =
      cg.app (qf.obj K) ≫ QY'.map (β₀.app K) ≫ uf'.app (pg'.obj K) := by
  apply (adjf'.homEquiv _ _).symm.injective
  have hL : (adjf'.homEquiv _ _).symm
      (Lg.map (uf.app K) ≫ map adjf adjf' eg ef (QX.obj K) ≫ Rf'.map (cg'.app K)) =
      Lf'.map (cg.app (qf.obj K)) ≫ cf'.app (pg.obj (qf.obj K)) ≫
        QX'.map (θ₀.app (qf.obj K)) ≫ QX'.map (pg'.map (a.counit.app K)) := by
    rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm]
    simp only [Functor.comp_obj]
    rw [homEquiv_symm_map]
    simp only [Category.assoc]
    have h₁ := eg.hom.naturality (uf.app K)
    have h₂ := ef.inv.naturality (uf.app K)
    have h₃ := cg'.naturality (a.counit.app K)
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at h₁ h₂ h₃
    rw [reassoc_of% h₁, reassoc_of% h₂, ← Lg'.map_comp_assoc, hf, Lg'.map_comp_assoc, h₃]
    simpa only [Category.assoc] using hθ (qf.obj K) =≫ QX'.map (pg'.map (a.counit.app K))
  have hR : (adjf'.homEquiv _ _).symm
      (cg.app (qf.obj K) ≫ QY'.map (β₀.app K) ≫ uf'.app (pg'.obj K)) =
      Lf'.map (cg.app (qf.obj K)) ≫ cf'.app (pg.obj (qf.obj K)) ≫
        QX'.map (θ₀.app (qf.obj K)) ≫ QX'.map (pg'.map (a.counit.app K)) := by
    rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_left_symm,
      Adjunction.homEquiv_counit, hf']
    have h₄ := cf'.naturality (β₀.app K)
    simp only [Functor.comp_obj, Functor.comp_map] at h₄
    rw [reassoc_of% h₄, ← QX'.map_comp, ← QX'.map_comp, ← hβ, Adjunction.homEquiv_counit]
  exact hL.trans hR.symm

/-- **Invertibility of the derived base change map from the underived one.**  Under the
hypotheses of `map_comparison`, the derived base change map at `Q K` is invertible as soon as
the underived base change map at `K` is, together with the components of the units and
comparisons that occur. -/
theorem isIso_map_of_isIso
    (hβ : ∀ K : HX, (a'.homEquiv _ _).symm (β₀.app K) =
      θ₀.app (qf.obj K) ≫ pg'.map (a.counit.app K))
    (hf : ∀ K : HX, Lf.map (uf.app K) ≫ adjf.counit.app (QX.obj K) =
      cf.app (qf.obj K) ≫ QX.map (a.counit.app K))
    (hf' : ∀ K : HX', Lf'.map (uf'.app K) ≫ adjf'.counit.app (QX'.obj K) =
      cf'.app (qf'.obj K) ≫ QX'.map (a'.counit.app K))
    (hθ : ∀ M : HY, eg.hom.app (QY.obj M) ≫ ef.inv.app (QY.obj M) ≫ Lg'.map (cf.app M) ≫
        cg'.app (pf.obj M) =
      Lf'.map (cg.app M) ≫ cf'.app (pg.obj M) ≫ QX'.map (θ₀.app M))
    (K : HX) [IsIso (uf.app K)] [IsIso (cg'.app K)] [IsIso (cg.app (qf.obj K))]
    [IsIso (β₀.app K)] [IsIso (uf'.app (pg'.obj K))] :
    IsIso (map adjf adjf' eg ef (QX.obj K)) := by
  have h := map_comparison a a' θ₀ β₀ adjf adjf' eg ef cf cf' cg cg' uf uf' hβ hf hf' hθ K
  have h' : map adjf adjf' eg ef (QX.obj K) =
      inv (Lg.map (uf.app K)) ≫ (cg.app (qf.obj K) ≫ QY'.map (β₀.app K) ≫
        uf'.app (pg'.obj K)) ≫ inv (Rf'.map (cg'.app K)) := by
    rw [← h]
    simp
  rw [h']
  infer_instance

/-- **Invertibility of the derived base change map from the underived base change map of a
square of adjunctions.**  Here the underived base change map is the one attached to two
isomorphisms `eg₀ : pg ⋙ pf' ≅ pc`, `ef₀ : pf ⋙ pg' ≅ pc` identifying the two composites of
degreewise pullback, and the derived identifications `eg`, `ef` are induced by them through a
comparison `cc : Q ⋙ Lc ⟶ pc ⋙ Q` (`hg`, `hg'`).  If the derived counits are induced by the
underived ones (Stacks 0FPI), the derived base change map is invertible at `Q K` as soon as the
underived one is at `K`, together with the components of the units and comparisons that occur. -/
theorem isIso_map_of_isIso_twoSquare {pc : HY ⥤ HX'} (eg₀ : pg ⋙ pf' ≅ pc)
    (ef₀ : pf ⋙ pg' ≅ pc) (cc : QY ⋙ Lc ⟶ pc ⋙ QX')
    (hf : ∀ K : HX, Lf.map (uf.app K) ≫ adjf.counit.app (QX.obj K) =
      cf.app (qf.obj K) ≫ QX.map (a.counit.app K))
    (hf' : ∀ K : HX', Lf'.map (uf'.app K) ≫ adjf'.counit.app (QX'.obj K) =
      cf'.app (qf'.obj K) ≫ QX'.map (a'.counit.app K))
    (hg : ∀ M : HY, eg.hom.app (QY.obj M) ≫ cc.app M =
      Lf'.map (cg.app M) ≫ cf'.app (pg.obj M) ≫ QX'.map (eg₀.hom.app M))
    (hg' : ∀ M : HY, ef.hom.app (QY.obj M) ≫ cc.app M =
      Lg'.map (cf.app M) ≫ cg'.app (pf.obj M) ≫ QX'.map (ef₀.hom.app M))
    (K : HX) (h₁ : IsIso (uf.app K)) (h₂ : IsIso (cg'.app K)) (h₃ : IsIso (cg.app (qf.obj K)))
    (h₄ : IsIso (map a a' eg₀ ef₀ K)) (h₅ : IsIso (uf'.app (pg'.obj K))) :
    IsIso (map adjf adjf' eg ef (QX.obj K)) := by
  have h₄' : IsIso ((twoSquare a a' eg₀ ef₀).app K) := h₄
  refine isIso_map_of_isIso a a' (eg₀.hom ≫ ef₀.inv) (twoSquare a a' eg₀ ef₀) adjf adjf' eg ef
    cf cf' cg cg' uf uf' (fun K => ?_) hf hf' (fun M => ?_) K
  · exact (homEquiv_symm_map a a' eg₀ ef₀ K).trans (by rw [NatTrans.comp_app, Category.assoc])
  · have h₂ : Lg'.map (cf.app M) ≫ cg'.app (pf.obj M) =
        ef.hom.app (QY.obj M) ≫ cc.app M ≫ QX'.map (ef₀.inv.app M) := by
      rw [reassoc_of% (hg' M), ← QX'.map_comp, Iso.hom_inv_id_app]
      simp
    rw [h₂, Iso.inv_hom_id_app_assoc, reassoc_of% (hg M), NatTrans.comp_app, QX'.map_comp]

section Comparison

variable {H₀ : Type u₅} {H₁ : Type u₆} {D₀ : Type u₁} {D₁ : Type u₂}
  [Category.{v₅} H₀] [Category.{v₆} H₁] [Category.{v₁} D₀] [Category.{v₂} D₁]
  {Q₀ : H₀ ⥤ D₀} {Q₁ : H₁ ⥤ D₁}

/-- Composing a morphism and an isomorphism of functors, each induced through comparisons
`Q₀ ⋙ - ⟶ - ⋙ Q₁` by an underived one, gives a morphism induced by the composite: if `c₁` is
compatible with `e₁₀` (in the weak form `h₁`, where the source comparison is arbitrary) and `e₂`
with `e₂₀`, then `c₁ ≫ e₂.hom` is compatible with `e₁₀ ≪≫ e₂₀`. -/
theorem comp_app_comparison {F G K : D₀ ⥤ D₁} {G₀ K₀ F₀ : H₀ ⥤ H₁}
    (cG : Q₀ ⋙ G ⟶ G₀ ⋙ Q₁) (cK : Q₀ ⋙ K ⟶ K₀ ⋙ Q₁) (c₁ : F ⟶ G) (e₂ : G ≅ K)
    (e₁₀ : F₀ ≅ G₀) (e₂₀ : G₀ ≅ K₀) (M : H₀) {T : D₁} (x₁ : F.obj (Q₀.obj M) ⟶ T)
    (x₂ : T ⟶ Q₁.obj (F₀.obj M))
    (h₁ : c₁.app (Q₀.obj M) ≫ cG.app M = x₁ ≫ x₂ ≫ Q₁.map (e₁₀.hom.app M))
    (h₂ : e₂.hom.app (Q₀.obj M) ≫ cK.app M = cG.app M ≫ Q₁.map (e₂₀.hom.app M)) :
    (c₁ ≫ e₂.hom).app (Q₀.obj M) ≫ cK.app M = x₁ ≫ x₂ ≫ Q₁.map ((e₁₀ ≪≫ e₂₀).hom.app M) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc, Functor.map_comp]
  rw [h₂, reassoc_of% h₁]

/-- Postcomposing an equation `a ≫ b = d ≫ e ≫ f` with a further morphism. -/
theorem comp_comp_eq_of_eq {C : Type u₁} [Category.{v₁} C] {W X₁ X₂ X₃ X₄ X₅ : C}
    {a : W ⟶ X₁} {b : X₁ ⟶ X₂} {d : W ⟶ X₃} {e : X₃ ⟶ X₄} {f : X₄ ⟶ X₂} (c : X₂ ⟶ X₅)
    (h : a ≫ b = d ≫ e ≫ f) : a ≫ b ≫ c = d ≫ e ≫ f ≫ c := by
  rw [← Category.assoc, h]
  simp only [Category.assoc]

end Comparison

/-- `isIso_map_of_isIso_twoSquare` for a family of derived and underived functors `Λ t`, `π t`
with comparisons `cmp t`, when the two composites around the square are identified with the
members at two equal indices `t₂` and `t₁`: the identification `ef` around the top and right is
a composition law `ef₁` followed by the transport along `t₁ = t₂`. -/
theorem isIso_map_of_isIso_twoSquare_eq {T : Sort*} (Λ : T → (DY ⥤ DX')) (π : T → (HY ⥤ HX'))
    (cmp : ∀ t, QY ⋙ Λ t ⟶ π t ⋙ QX') {t₁ t₂ : T} (h : t₁ = t₂)
    (eg₂ : Lg ⋙ Lf' ≅ Λ t₂) (ef₁ : Lf ⋙ Lg' ≅ Λ t₁)
    (eg₀ : pg ⋙ pf' ≅ π t₂) (ef₁₀ : pf ⋙ pg' ≅ π t₁)
    (hf : ∀ K : HX, Lf.map (uf.app K) ≫ adjf.counit.app (QX.obj K) =
      cf.app (qf.obj K) ≫ QX.map (a.counit.app K))
    (hf' : ∀ K : HX', Lf'.map (uf'.app K) ≫ adjf'.counit.app (QX'.obj K) =
      cf'.app (qf'.obj K) ≫ QX'.map (a'.counit.app K))
    (hg : ∀ M : HY, eg₂.hom.app (QY.obj M) ≫ (cmp t₂).app M =
      Lf'.map (cg.app M) ≫ cf'.app (pg.obj M) ≫ QX'.map (eg₀.hom.app M))
    (hg₁ : ∀ M : HY, ef₁.hom.app (QY.obj M) ≫ (cmp t₁).app M =
      Lg'.map (cf.app M) ≫ cg'.app (pf.obj M) ≫ QX'.map (ef₁₀.hom.app M))
    (K : HX) (h₁ : IsIso (uf.app K)) (h₂ : IsIso (cg'.app K)) (h₃ : IsIso (cg.app (qf.obj K)))
    (h₄ : IsIso (map a a' eg₀ (ef₁₀ ≪≫ eqToIso (congrArg π h)) K))
    (h₅ : IsIso (uf'.app (pg'.obj K))) :
    IsIso (map adjf adjf' eg₂ (ef₁ ≪≫ eqToIso (congrArg Λ h)) (QX.obj K)) := by
  subst h
  refine isIso_map_of_isIso_twoSquare a a' adjf adjf' eg₂ _ cf cf' cg cg' uf uf' eg₀ _
    (cmp t₁) hf hf' hg (fun M => ?_) K h₁ h₂ h₃ h₄ h₅
  simpa using hg₁ M

end Stacks.CategoryTheory.BaseChange
