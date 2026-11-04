module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Identifications of right adjoints compatible with the counits

Given adjunctions `Lf ⊣ Rf`, `Lh ⊣ Rh` and `Lo ⊣ Ro` and an isomorphism `cL : Lf ⋙ Lh ≅ Lo`,
an isomorphism `cR : Rh ⋙ Rf ≅ Ro` is *counit compatible* with `cL` when it identifies the counit
of `Lo ⊣ Ro` with that of the composite adjunction; there is exactly one such `cR`, the
conjugate of `cL`. This file shows that coherence passes from the left adjoints to the right
adjoints: if the identifications of the left adjoints of a triple composite are associative, so
are the counit compatible identifications of the right adjoints, and likewise for the unit
constraints.

## Main definitions

* `Stacks.CategoryTheory.BaseChange.CounitCompatible` — the compatibility.

## Main results

* `Stacks.CategoryTheory.BaseChange.counitCompatible_assoc` — associativity passes to the right
  adjoints.
* `Stacks.CategoryTheory.BaseChange.counitCompatible_unit_left`,
  `Stacks.CategoryTheory.BaseChange.counitCompatible_unit_right` — so do the unit constraints.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory.BaseChange

section Def

variable {S T U : Type*} [Category S] [Category T] [Category U]
  {Lf : S ⥤ T} {Rf : T ⥤ S} {Lh : T ⥤ U} {Rh : U ⥤ T} {Lo : S ⥤ U} {Ro : U ⥤ S}
  (adjf : Lf ⊣ Rf) (adjh : Lh ⊣ Rh) (adjo : Lo ⊣ Ro) (cL : Lf ⋙ Lh ≅ Lo) (cR : Rh ⋙ Rf ≅ Ro)

/-- `cR` is the identification of right adjoints induced by `cL`: it is compatible with the
counits of `Lo ⊣ Ro` and of the composite adjunction. -/
def CounitCompatible : Prop :=
  ∀ M : U, Lo.map (cR.hom.app M) ≫ adjo.counit.app M =
    cL.inv.app ((Rh ⋙ Rf).obj M) ≫ (adjf.comp adjh).counit.app M

end Def

section Assoc

variable {C₀ C₁ C₂ C₃ : Type*} [Category C₀] [Category C₁] [Category C₂] [Category C₃]
  {L₁ : C₀ ⥤ C₁} {R₁ : C₁ ⥤ C₀} {L₂ : C₁ ⥤ C₂} {R₂ : C₂ ⥤ C₁} {L₃ : C₂ ⥤ C₃} {R₃ : C₃ ⥤ C₂}
  {L₁₂ : C₀ ⥤ C₂} {R₁₂ : C₂ ⥤ C₀} {L₂₃ : C₁ ⥤ C₃} {R₂₃ : C₃ ⥤ C₁} {L₁₂₃ : C₀ ⥤ C₃}
  {R₁₂₃ : C₃ ⥤ C₀}
  {A₁ : L₁ ⊣ R₁} {A₂ : L₂ ⊣ R₂} {A₃ : L₃ ⊣ R₃} {A₁₂ : L₁₂ ⊣ R₁₂} {A₂₃ : L₂₃ ⊣ R₂₃}
  {A₁₂₃ : L₁₂₃ ⊣ R₁₂₃}
  {l₁₂ : L₁ ⋙ L₂ ≅ L₁₂} {l₂₃ : L₂ ⋙ L₃ ≅ L₂₃} {l₁₂₃ : L₁₂ ⋙ L₃ ≅ L₁₂₃}
  {l₁₂₃' : L₁ ⋙ L₂₃ ≅ L₁₂₃}
  {r₁₂ : R₂ ⋙ R₁ ≅ R₁₂} {r₂₃ : R₃ ⋙ R₂ ≅ R₂₃} {r₁₂₃ : R₃ ⋙ R₁₂ ≅ R₁₂₃}
  {r₁₂₃' : R₂₃ ⋙ R₁ ≅ R₁₂₃}

/-- **Associativity passes to the counit compatible identifications of the right adjoints.** -/
theorem counitCompatible_assoc (h₁₂ : CounitCompatible A₁ A₂ A₁₂ l₁₂ r₁₂)
    (h₂₃ : CounitCompatible A₂ A₃ A₂₃ l₂₃ r₂₃) (h₁₂₃ : CounitCompatible A₁₂ A₃ A₁₂₃ l₁₂₃ r₁₂₃)
    (h₁₂₃' : CounitCompatible A₁ A₂₃ A₁₂₃ l₁₂₃' r₁₂₃')
    (hl : ∀ X : C₀, L₃.map (l₁₂.hom.app X) ≫ l₁₂₃.hom.app X =
      l₂₃.hom.app (L₁.obj X) ≫ l₁₂₃'.hom.app X) (Y : C₃) :
    R₁.map (r₂₃.hom.app Y) ≫ r₁₂₃'.hom.app Y = r₁₂.hom.app (R₃.obj Y) ≫ r₁₂₃.hom.app Y := by
  apply (A₁₂₃.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have k' := h₁₂₃' Y
  have k := h₁₂₃ Y
  have e₁ := h₂₃ Y
  have e₂ := h₁₂ (R₃.obj Y)
  simp only [Adjunction.comp_counit_app, Functor.comp_obj] at e₁ e₂ k k'
  rw [k', k]
  set Z := R₁.obj (R₂.obj (R₃.obj Y))
  have hl' : l₁₂₃'.inv.app Z ≫ l₂₃.inv.app (L₁.obj Z) =
      l₁₂₃.inv.app Z ≫ L₃.map (l₁₂.inv.app Z) := by
    rw [← cancel_epi (l₂₃.hom.app (L₁.obj Z) ≫ l₁₂₃'.hom.app Z)]
    conv_rhs => rw [← hl Z]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
    rw [← L₃.map_comp, Iso.hom_inv_id_app, L₃.map_id]
    rfl
  have n₁ : L₁₂₃.map (R₁.map (r₂₃.hom.app Y)) ≫ l₁₂₃'.inv.app (R₁.obj (R₂₃.obj Y)) =
      l₁₂₃'.inv.app Z ≫ L₂₃.map (L₁.map (R₁.map (r₂₃.hom.app Y))) :=
    l₁₂₃'.inv.naturality _
  have n₂ : L₁.map (R₁.map (r₂₃.hom.app Y)) ≫ A₁.counit.app (R₂₃.obj Y) =
      A₁.counit.app (R₂.obj (R₃.obj Y)) ≫ r₂₃.hom.app Y :=
    A₁.counit.naturality _
  have n₃ : L₂₃.map (A₁.counit.app (R₂.obj (R₃.obj Y))) ≫ l₂₃.inv.app (R₂.obj (R₃.obj Y)) =
      l₂₃.inv.app (L₁.obj Z) ≫ L₃.map (L₂.map (A₁.counit.app (R₂.obj (R₃.obj Y)))) :=
    l₂₃.inv.naturality _
  have n₄ : L₁₂₃.map (r₁₂.hom.app (R₃.obj Y)) ≫ l₁₂₃.inv.app (R₁₂.obj (R₃.obj Y)) =
      l₁₂₃.inv.app Z ≫ L₃.map (L₁₂.map (r₁₂.hom.app (R₃.obj Y))) :=
    l₁₂₃.inv.naturality _
  rw [reassoc_of% n₁, ← L₂₃.map_comp_assoc, n₂, L₂₃.map_comp_assoc, e₁, reassoc_of% n₃,
    reassoc_of% n₄, reassoc_of% hl']
  congr 1
  simp only [← L₃.map_comp_assoc]
  rw [e₂]

end Assoc

section Unit

variable {C₀ C₁ : Type*} [Category C₀] [Category C₁]

/-- Two morphisms into `R.obj Y` agree once their adjuncts agree, using the counit data of `A'`
transported along `d`. -/
private theorem comp_dR_eq_of_counit {C₀ C₁ : Type*} [Category C₀] [Category C₁]
    {L L' : C₀ ⥤ C₁} {R R' : C₁ ⥤ C₀} (A : L ⊣ R) (A' : L' ⊣ R') (d : L' ≅ L) (dR : R' ≅ R)
    (hd : ∀ M, L.map (dR.hom.app M) ≫ A.counit.app M = d.inv.app (R'.obj M) ≫ A'.counit.app M)
    {X : C₀} {Y W : C₁} (e : X ⟶ R'.obj Y) (f : X ⟶ R.obj Y) (q : L'.obj X ⟶ W) (r : W ⟶ Y)
    (g : L.obj X ⟶ W) (hY : L'.map e ≫ A'.counit.app Y = q ≫ r) (hX : d.inv.app X ≫ q = g)
    (h : g ≫ r = L.map f ≫ A.counit.app Y) : e ≫ dR.hom.app Y = f := by
  apply (A.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [hd, ← h, ← hX, Category.assoc, ← hY, d.inv.naturality_assoc]

/-- **The unit constraint passes to the right adjoints, identity on the target side.** Let
`L₀ ⊣ R₀` be an adjunction on `C₁` with `iL : L₀ ≅ 𝟭` and `iR : R₀ ≅ 𝟭` its conjugate, and let
`eL : L ⋙ L₀ ≅ L'` and `eR : R₀ ⋙ R ≅ R'` be counit compatible, `d : L' ≅ L` and `dR : R' ≅ R`
conjugate. If `eL ≫ d` is `iL` whiskered by `L`, then `eR ≫ dR` is `R` of `iR`. -/
theorem counitCompatible_unit_right {L₀ R₀ : C₁ ⥤ C₁} {L L' : C₀ ⥤ C₁} {R R' : C₁ ⥤ C₀}
    {A₀ : L₀ ⊣ R₀} {A : L ⊣ R} {A' : L' ⊣ R'} {iL : L₀ ≅ 𝟭 C₁} {iR : R₀ ≅ 𝟭 C₁}
    {eL : L ⋙ L₀ ≅ L'} {eR : R₀ ⋙ R ≅ R'} {d : L' ≅ L} {dR : R' ≅ R}
    (hiR : ∀ x, iR.hom.app x = iL.inv.app (R₀.obj x) ≫ A₀.counit.app x)
    (he : CounitCompatible A A₀ A' eL eR)
    (hd : ∀ M, L.map (dR.hom.app M) ≫ A.counit.app M = d.inv.app (R'.obj M) ≫ A'.counit.app M)
    (hL : ∀ X, eL.hom.app X ≫ d.hom.app X = iL.hom.app (L.obj X)) (Y : C₁) :
    eR.hom.app Y ≫ dR.hom.app Y = R.map (iR.hom.app Y) := by
  have hY := he Y
  simp only [Adjunction.comp_counit_app, Functor.comp_obj] at hY
  have hX : d.inv.app (R.obj (R₀.obj Y)) ≫ eL.inv.app (R.obj (R₀.obj Y)) =
      iL.inv.app (L.obj (R.obj (R₀.obj Y))) := by
    have hI : eL.app (R.obj (R₀.obj Y)) ≪≫ d.app (R.obj (R₀.obj Y)) =
        iL.app (L.obj (R.obj (R₀.obj Y))) := Iso.ext (hL _)
    simpa using congrArg Iso.inv hI
  have n₂ : A.counit.app (R₀.obj Y) ≫ iL.inv.app (R₀.obj Y) =
      iL.inv.app (L.obj (R.obj (R₀.obj Y))) ≫ L₀.map (A.counit.app (R₀.obj Y)) :=
    iL.inv.naturality _
  refine comp_dR_eq_of_counit A A' d dR hd _ _ _ _ _ hY hX ?_
  refine Eq.trans ?_ (A.counit_naturality (iR.hom.app Y)).symm
  rw [hiR, reassoc_of% n₂]

/-- **The unit constraint passes to the right adjoints, identity on the source side.** Let
`L₀ ⊣ R₀` be an adjunction on `C₀` with `iL : L₀ ≅ 𝟭` and `iR : R₀ ≅ 𝟭` its conjugate, and let
`eL : L₀ ⋙ L ≅ L'` and `eR : R ⋙ R₀ ≅ R'` be counit compatible, `d : L' ≅ L` and `dR : R' ≅ R`
conjugate. If `eL ≫ d` is `L` of `iL`, then `eR ≫ dR` is `iR` whiskered by `R`. -/
theorem counitCompatible_unit_left {L₀ R₀ : C₀ ⥤ C₀} {L L' : C₀ ⥤ C₁} {R R' : C₁ ⥤ C₀}
    {A₀ : L₀ ⊣ R₀} {A : L ⊣ R} {A' : L' ⊣ R'} {iL : L₀ ≅ 𝟭 C₀} {iR : R₀ ≅ 𝟭 C₀}
    {eL : L₀ ⋙ L ≅ L'} {eR : R ⋙ R₀ ≅ R'} {d : L' ≅ L} {dR : R' ≅ R}
    (hiR : ∀ x, iR.hom.app x = iL.inv.app (R₀.obj x) ≫ A₀.counit.app x)
    (he : CounitCompatible A₀ A A' eL eR)
    (hd : ∀ M, L.map (dR.hom.app M) ≫ A.counit.app M = d.inv.app (R'.obj M) ≫ A'.counit.app M)
    (hL : ∀ X, eL.hom.app X ≫ d.hom.app X = L.map (iL.hom.app X)) (Y : C₁) :
    eR.hom.app Y ≫ dR.hom.app Y = iR.hom.app (R.obj Y) := by
  have hY := he Y
  simp only [Adjunction.comp_counit_app, Functor.comp_obj] at hY
  have hX : d.inv.app (R₀.obj (R.obj Y)) ≫ eL.inv.app (R₀.obj (R.obj Y)) =
      L.map (iL.inv.app (R₀.obj (R.obj Y))) := by
    have hI : eL.app (R₀.obj (R.obj Y)) ≪≫ d.app (R₀.obj (R.obj Y)) =
        L.mapIso (iL.app (R₀.obj (R.obj Y))) := Iso.ext (hL _)
    simpa using congrArg Iso.inv hI
  refine comp_dR_eq_of_counit A A' d dR hd _ _ _ _ _ hY hX ?_
  rw [hiR, L.map_comp_assoc]

end Unit

end Stacks.CategoryTheory.BaseChange
