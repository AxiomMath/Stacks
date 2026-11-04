module

public import StacksFrontier.CategoryTheory.Functor.NatEndCentral

/-!
# Lifting a morphism through a factorization of a functor

Let `Fi : C ⥤ E` be isomorphic, through `κ : Fe ⋙ Fj ≅ Fi`, to a composite of `Fe : C ⥤ D` and
`Fj : D ⥤ E`. A morphism `φ : Fi.obj M ⟶ Fi.obj N` *descends along `κ`* when it is
`Fj.map ψ` for some `ψ : Fe.obj M ⟶ Fe.obj N`, read through `κ`. In limit arguments `Fi` and
`Fj` are inverse images to a limit, `Fe` an inverse image to a stage, and `κ` the comparison of
iterated inverse images; the morphism clause of Stacks 01ZR says that morphisms descend at some
stage.

Two facts make such statements robust under change of models:

* if every natural endomorphism of `Fi` is central, descent along one `κ` gives descent along
  every `κ`, with the same `ψ` (`AlgebraicGeometry`-free form of the observation that two choices
  of comparison isomorphisms differ by a central automorphism);
* descent transports along fully faithful comparison functors intertwining the three functors.

## Main definitions

* `CategoryTheory.Functor.DescendsAlong`: `φ` descends along `κ`.

## Main results

* `CategoryTheory.Functor.DescendsAlong.of_natEndCentral`: change of `κ`.
* `CategoryTheory.Functor.DescendsAlong.transport`: transport along fully faithful comparisons.
* `CategoryTheory.Functor.DescendsAlong.of_iso`: invariance under isomorphisms of `M` and `N`.
* `CategoryTheory.Functor.DescendsAlong.of_whiskerLeft`: restriction of the source.
-/

@[expose] public section

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-- `φ : Fi.obj M ⟶ Fi.obj N` is `Fj.map ψ` for some `ψ : Fe.obj M ⟶ Fe.obj N`, read through
`κ : Fe ⋙ Fj ≅ Fi`. -/
def DescendsAlong {Fe : C ⥤ D} {Fj : D ⥤ E} {Fi : C ⥤ E} (κ : Fe ⋙ Fj ≅ Fi) {M N : C}
    (φ : Fi.obj M ⟶ Fi.obj N) : Prop :=
  ∃ ψ : Fe.obj M ⟶ Fe.obj N, Fj.map ψ ≫ κ.hom.app N = κ.hom.app M ≫ φ

/-- If the natural endomorphisms of `Fi` are central, descent along one comparison gives descent
along any other, with the same lift. -/
theorem DescendsAlong.of_natEndCentral {Fe : C ⥤ D} {Fj : D ⥤ E} {Fi : C ⥤ E}
    (hFi : Fi.NatEndCentral) {κ₀ : Fe ⋙ Fj ≅ Fi} {M N : C} {φ : Fi.obj M ⟶ Fi.obj N}
    (h : DescendsAlong κ₀ φ) (κ : Fe ⋙ Fj ≅ Fi) : DescendsAlong κ φ := by
  obtain ⟨ψ, hψ⟩ := h
  refine ⟨ψ, ?_⟩
  have hc := hFi (κ₀.inv ≫ κ.hom) φ
  simp only [NatTrans.comp_app] at hc
  calc Fj.map ψ ≫ κ.hom.app N
      = (Fj.map ψ ≫ κ₀.hom.app N) ≫ κ₀.inv.app N ≫ κ.hom.app N := by simp
    _ = κ₀.hom.app M ≫ φ ≫ κ₀.inv.app N ≫ κ.hom.app N := by rw [hψ, Category.assoc]
    _ = κ₀.hom.app M ≫ (κ₀.inv.app M ≫ κ.hom.app M) ≫ φ := by rw [← hc, Category.assoc]
    _ = κ.hom.app M ≫ φ := by simp

/-- Descent is invariant under isomorphisms of the source and target. -/
theorem DescendsAlong.of_iso {Fe : C ⥤ D} {Fj : D ⥤ E} {Fi : C ⥤ E} (κ : Fe ⋙ Fj ≅ Fi)
    {M M' N N' : C} (a : M ≅ M') (b : N ≅ N') {φ : Fi.obj M' ⟶ Fi.obj N'}
    (h : DescendsAlong κ (Fi.map a.hom ≫ φ ≫ Fi.map b.inv)) : DescendsAlong κ φ := by
  obtain ⟨ψ, hψ⟩ := h
  refine ⟨Fe.map a.inv ≫ ψ ≫ Fe.map b.hom, ?_⟩
  have hb := κ.hom.naturality b.hom
  have ha := κ.hom.naturality a.inv
  simp only [Functor.comp_map] at hb ha
  simp only [Functor.map_comp, Category.assoc, hb]
  rw [reassoc_of% hψ, ← Fi.map_comp, Iso.inv_hom_id, Fi.map_id, Category.comp_id,
    reassoc_of% ha, ← Fi.map_comp_assoc, Iso.inv_hom_id, Fi.map_id, Category.id_comp]

/-- Descent along a comparison restricted along a functor `R` into the source is descent along
the comparison itself. -/
theorem DescendsAlong.of_whiskerLeft {C₀ : Type u₄} [Category.{v₄} C₀] (R : C₀ ⥤ C)
    {Fe : C ⥤ D} {Fj : D ⥤ E} {Fi : C ⥤ E} (κ : Fe ⋙ Fj ≅ Fi) {M N : C₀}
    {φ : Fi.obj (R.obj M) ⟶ Fi.obj (R.obj N)}
    (h : DescendsAlong (Functor.associator R Fe Fj ≪≫ Functor.isoWhiskerLeft R κ) φ) :
    DescendsAlong κ φ := by
  obtain ⟨ψ, hψ⟩ := h
  exact ⟨ψ, by simpa using hψ⟩

variable {C' : Type u₄} [Category.{v₄} C'] {D' : Type u₅} [Category.{v₅} D']
  {E' : Type u₆} [Category.{v₆} E']

/-- **Descent transports along fully faithful comparisons.** Let `Ri`, `Rj`, `Rl` compare
`(Fe, Fj, Fi)` on `C, D, E` with `(Ge, Gj, Gi)` on `C', D', E'`, through natural isomorphisms
`βe`, `βj`, `βi`, with `Rl` fully faithful. A morphism `φ' : Gi.obj (Ri.obj M) ⟶ Gi.obj (Ri.obj N)`
descends along every comparison `(Ri ⋙ Ge) ⋙ Gj ≅ Ri ⋙ Gi` as soon as the morphism it corresponds
to under `βi` descends along every comparison `Fe ⋙ Fj ≅ Fi`. -/
theorem DescendsAlong.transport {Fe : C ⥤ D} {Fj : D ⥤ E} {Fi : C ⥤ E}
    {Ge : C' ⥤ D'} {Gj : D' ⥤ E'} {Gi : C' ⥤ E'} {Ri : C ⥤ C'} {Rj : D ⥤ D'} {Rl : E ⥤ E'}
    (hR : Rl.FullyFaithful) (βe : Ri ⋙ Ge ≅ Fe ⋙ Rj) (βj : Rj ⋙ Gj ≅ Fj ⋙ Rl)
    (βi : Ri ⋙ Gi ≅ Fi ⋙ Rl) {M N : C}
    (φ' : Gi.obj (Ri.obj M) ⟶ Gi.obj (Ri.obj N))
    (h : ∀ κ : Fe ⋙ Fj ≅ Fi, DescendsAlong κ (hR.preimage (βi.inv.app M ≫ φ' ≫ βi.hom.app N)))
    (κ' : (Ri ⋙ Ge) ⋙ Gj ≅ Ri ⋙ Gi) : DescendsAlong κ' φ' := by
  let κ : Fe ⋙ Fj ≅ Fi := NatIso.ofComponents (fun X => hR.preimageIso
      ((βj.app (Fe.obj X)).symm ≪≫ Gj.mapIso (βe.app X).symm ≪≫ κ'.app X ≪≫ βi.app X))
    (fun {X Y} f => hR.map_injective (by
      simp only [Functor.comp_map, Functor.map_comp, FullyFaithful.preimageIso_hom,
        FullyFaithful.map_preimage, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
        Functor.mapIso_hom, Category.assoc]
      have h1 : Rl.map (Fj.map (Fe.map f)) ≫ βj.inv.app (Fe.obj Y) =
          βj.inv.app (Fe.obj X) ≫ Gj.map (Rj.map (Fe.map f)) := βj.inv.naturality (Fe.map f)
      have h2 : Rj.map (Fe.map f) ≫ βe.inv.app Y = βe.inv.app X ≫ Ge.map (Ri.map f) :=
        βe.inv.naturality f
      have h3 : Gj.map (Ge.map (Ri.map f)) ≫ κ'.hom.app Y = κ'.hom.app X ≫ Gi.map (Ri.map f) :=
        κ'.hom.naturality f
      have h4 : Gi.map (Ri.map f) ≫ βi.hom.app Y = βi.hom.app X ≫ Rl.map (Fi.map f) :=
        βi.hom.naturality f
      rw [reassoc_of% h1, ← Gj.map_comp_assoc, h2, Gj.map_comp_assoc, reassoc_of% h3, h4]))
  obtain ⟨ψ, hψ⟩ := h κ
  refine ⟨βe.hom.app M ≫ Rj.map ψ ≫ βe.inv.app N, ?_⟩
  have hψ' := congrArg Rl.map hψ
  simp only [κ, Functor.map_comp, NatIso.ofComponents_hom_app, FullyFaithful.preimageIso_hom,
    FullyFaithful.map_preimage, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_hom, Category.assoc] at hψ'
  have hn := βj.hom.naturality ψ
  simp only [Functor.comp_map] at hn
  rw [← cancel_mono (βi.hom.app N)]
  simp only [Functor.map_comp, Category.assoc]
  calc Gj.map (βe.hom.app M) ≫ Gj.map (Rj.map ψ) ≫ Gj.map (βe.inv.app N) ≫ κ'.hom.app N ≫
        βi.hom.app N
      = Gj.map (βe.hom.app M) ≫ (Gj.map (Rj.map ψ) ≫ βj.hom.app (Fe.obj N)) ≫
          βj.inv.app (Fe.obj N) ≫ Gj.map (βe.inv.app N) ≫ κ'.hom.app N ≫ βi.hom.app N := by
        simp
    _ = Gj.map (βe.hom.app M) ≫ βj.hom.app (Fe.obj M) ≫ Rl.map (Fj.map ψ) ≫
          βj.inv.app (Fe.obj N) ≫ Gj.map (βe.inv.app N) ≫ κ'.hom.app N ≫ βi.hom.app N := by
        rw [hn, Category.assoc]
    _ = κ'.hom.app M ≫ φ' ≫ βi.hom.app N := by
        rw [hψ']
        simp only [Iso.hom_inv_id_app_assoc]
        rw [← Gj.map_comp_assoc]
        simp only [Functor.comp_obj, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]

end CategoryTheory.Functor

end
