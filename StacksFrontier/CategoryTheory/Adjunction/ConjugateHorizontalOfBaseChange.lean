module

public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare

/-!
# Pasting the conjugate comparisons of two base change squares

Consider two base change squares side by side, in the notation of
`Stacks.CategoryTheory.BaseChange`:

```
      Lf          Lf₁         Lf₂
  A ----→ B   A₁ ----→ B₁  A₂ ----→ B₂
```

with horizontal left adjoints `Lg₁ : A ⥤ A₁`, `Lg₂ : A₁ ⥤ A₂`, `Lg₃ : A ⥤ A₂` and
`Lh₁ : B ⥤ B₁`, `Lh₂ : B₁ ⥤ B₂`, `Lh₃ : B ⥤ B₂` (right adjoints `Rg_*`, `Rh_*`), squares
`e₁ : Lg₁ ⋙ Lf₁ ≅ Lf ⋙ Lh₁`, `e₂ : Lg₂ ⋙ Lf₂ ≅ Lf₁ ⋙ Lh₂`, `e₃ : Lg₃ ⋙ Lf₂ ≅ Lf ⋙ Lh₃`, and
composition isomorphisms `γA : Lg₁ ⋙ Lg₂ ≅ Lg₃`, `γB : Lh₁ ⋙ Lh₂ ≅ Lh₃`. Each square has a
conjugate comparison `PFᵢ : Rhᵢ ⋙ Rf ⟶ Rf' ⋙ Rgᵢ` of right adjoints, and `γA`, `γB` have conjugates
`cA : Rg₂ ⋙ Rg₁ ⟶ Rg₃`, `cB : Rh₂ ⋙ Rh₁ ⟶ Rh₃`.

If the base change maps of the squares compose (the transitivity of base change, at one
object), the conjugate comparisons paste:
`Rf(cB) ≫ PF₃ = PF₁ ≫ Rg₁(PF₂) ≫ cA`.

Geometrically `Rf = RΓ(X, -)` over `A`, `Lg = - ⊗^L A'`, `Lh = Lg'^*`, and `PF` is the
identification `RΓ(X, Rg'_* -) = RΓ(X', -)` read over `A`; this is its composition law along
`Xₙ → Xₙ₊₁ → X` over `Aₙ ← Aₙ₊₁ ← A` ([Stacks, Tag 0DIM]).

## Main results

* `Stacks.CategoryTheory.BaseChange.conjugateEquiv_counit_comp`: the counit form of a conjugate
  comparison.
* `Stacks.CategoryTheory.BaseChange.conjugate_paste_of_map_comp`.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory.BaseChange

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

section Counit

variable {A : Type u₁} {B : Type u₂} {A' : Type u₃} {B' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A'] [Category.{v₄} B']
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
  {Lg : A ⥤ A'} {Rg : A' ⥤ A} {Lh : B ⥤ B'} {Rh : B' ⥤ B}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (ag : Lg ⊣ Rg) (ah : Lh ⊣ Rh)

/-- **The counit form of the conjugate comparison of a square.** For `e : Lg ⋙ Lf' ⟶ Lf ⋙ Lh`
with conjugate `PF : Rh ⋙ Rf ⟶ Rf' ⋙ Rg`, the transpose of `PF` at `W` under
`Lg ⋙ Lf' ⊣ Rf' ⋙ Rg` is `e` followed by the counits of `Lf ⊣ Rf` and `Lh ⊣ Rh`. -/
theorem conjugateEquiv_counit_comp (e : Lg ⋙ Lf' ⟶ Lf ⋙ Lh) (W : B') :
    Lf'.map (Lg.map ((conjugateEquiv (adjf.comp ah) (ag.comp adjf') e).app W)) ≫
        Lf'.map (ag.counit.app (Rf'.obj W)) ≫ adjf'.counit.app W =
      e.app (Rf.obj (Rh.obj W)) ≫ Lh.map (adjf.counit.app (Rh.obj W)) ≫ ah.counit.app W := by
  have h := conjugateEquiv_counit (adjf.comp ah) (ag.comp adjf') e W
  simp only [Adjunction.comp_counit_app, Functor.comp_map] at h
  exact h

end Counit

section Paste

variable {A : Type u₁} {B : Type u₂} {A₁ : Type u₃} {B₁ : Type u₄} {A₂ : Type*} {B₂ : Type*}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A₁] [Category.{v₄} B₁]
  [Category* A₂] [Category* B₂]
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf₁ : A₁ ⥤ B₁} {Rf₁ : B₁ ⥤ A₁} {Lf₂ : A₂ ⥤ B₂} {Rf₂ : B₂ ⥤ A₂}
  (adjf : Lf ⊣ Rf) (adjf₁ : Lf₁ ⊣ Rf₁) (adjf₂ : Lf₂ ⊣ Rf₂)
  {Lg₁ : A ⥤ A₁} {Rg₁ : A₁ ⥤ A} {Lg₂ : A₁ ⥤ A₂} {Rg₂ : A₂ ⥤ A₁} {Lg₃ : A ⥤ A₂} {Rg₃ : A₂ ⥤ A}
  (ag₁ : Lg₁ ⊣ Rg₁) (ag₂ : Lg₂ ⊣ Rg₂) (ag₃ : Lg₃ ⊣ Rg₃)
  {Lh₁ : B ⥤ B₁} {Rh₁ : B₁ ⥤ B} {Lh₂ : B₁ ⥤ B₂} {Rh₂ : B₂ ⥤ B₁} {Lh₃ : B ⥤ B₂} {Rh₃ : B₂ ⥤ B}
  (ah₁ : Lh₁ ⊣ Rh₁) (ah₂ : Lh₂ ⊣ Rh₂) (ah₃ : Lh₃ ⊣ Rh₃)
  (e₁ : Lg₁ ⋙ Lf₁ ≅ Lf ⋙ Lh₁) (e₂ : Lg₂ ⋙ Lf₂ ≅ Lf₁ ⋙ Lh₂) (e₃ : Lg₃ ⋙ Lf₂ ≅ Lf ⋙ Lh₃)
  (γA : Lg₁ ⋙ Lg₂ ≅ Lg₃) (γB : Lh₁ ⋙ Lh₂ ≅ Lh₃)

/-- **The conjugate comparisons of two squares paste, if their base change maps compose.** If
the base change map of the outer rectangle at `K = Rh₁ (Rh₂ W)` is `γA⁻¹`, then `Lg₂` of the base
change map of the left square, then that of the right square, then `Rf₂ (γB)`, the conjugate
comparisons satisfy `Rf(cB_W) ≫ PF₃_W = PF₁_{Rh₂ W} ≫ Rg₁(PF₂_W) ≫ cA_{Rf₂ W}`. -/
theorem conjugate_paste_of_map_comp (W : B₂)
    (hT : γA.inv.app (Rf.obj (Rh₁.obj (Rh₂.obj W))) ≫
        Lg₂.map (map adjf adjf₁ e₁ (Iso.refl _) (Rh₁.obj (Rh₂.obj W))) ≫
        map adjf₁ adjf₂ e₂ (Iso.refl _) (Lh₁.obj (Rh₁.obj (Rh₂.obj W))) ≫
        Rf₂.map (γB.hom.app (Rh₁.obj (Rh₂.obj W))) =
      map adjf adjf₂ e₃ (Iso.refl _) (Rh₁.obj (Rh₂.obj W))) :
    Rf.map ((conjugateEquiv (ah₁.comp ah₂) ah₃ γB.inv).app W) ≫
        (conjugateEquiv (adjf.comp ah₃) (ag₃.comp adjf₂) e₃.hom).app W =
      (conjugateEquiv (adjf.comp ah₁) (ag₁.comp adjf₁) e₁.hom).app (Rh₂.obj W) ≫
        Rg₁.map ((conjugateEquiv (adjf₁.comp ah₂) (ag₂.comp adjf₂) e₂.hom).app W) ≫
        (conjugateEquiv (ag₁.comp ag₂) ag₃ γA.inv).app (Rf₂.obj W) := by
  -- the counit form of `hT`
  have hT' : Lf₂.map (γA.inv.app (Rf.obj (Rh₁.obj (Rh₂.obj W)))) ≫
      e₂.hom.app (Lg₁.obj (Rf.obj (Rh₁.obj (Rh₂.obj W)))) ≫
      Lh₂.map (e₁.hom.app (Rf.obj (Rh₁.obj (Rh₂.obj W)))) ≫
      Lh₂.map (Lh₁.map (adjf.counit.app (Rh₁.obj (Rh₂.obj W)))) =
      e₃.hom.app (Rf.obj (Rh₁.obj (Rh₂.obj W))) ≫
        Lh₃.map (adjf.counit.app (Rh₁.obj (Rh₂.obj W))) ≫
        γB.inv.app (Rh₁.obj (Rh₂.obj W)) := by
    have h := congrArg (fun t => (adjf₂.homEquiv _ _).symm t) hT
    beta_reduce at h
    rw [homEquiv_symm_map, Adjunction.homEquiv_naturality_left_symm,
      Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm,
      homEquiv_symm_map] at h
    simp only [Iso.refl_inv, NatTrans.id_app, Category.id_comp, Functor.comp_obj] at h
    have hn := e₂.hom.naturality (map adjf adjf₁ e₁ (Iso.refl _) (Rh₁.obj (Rh₂.obj W)))
    simp only [Functor.comp_map] at hn
    simp only [Category.assoc] at h
    have hm := homEquiv_symm_map adjf adjf₁ e₁ (Iso.refl _) (Rh₁.obj (Rh₂.obj W))
    rw [Adjunction.homEquiv_counit] at hm
    have hm' := congrArg Lh₂.map hm
    simp only [Functor.map_comp] at hm'
    rw [reassoc_of% hn, reassoc_of% hm'] at h
    simp only [Iso.refl_inv, NatTrans.id_app] at h
    rw [← cancel_mono (γB.hom.app (Rh₁.obj (Rh₂.obj W))), Category.assoc, Category.assoc,
      Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id_app]
    refine Eq.trans ?_ (congrArg (_ ≫ ·) (Category.comp_id _)).symm
    refine Eq.trans ?_ h
    refine (congrArg (fun t => _ ≫ _ ≫ _ ≫ t) ?_).symm
    exact (congrArg (· ≫ _) (Lh₂.map_id _)).trans (Category.id_comp _)
  apply ((ag₃.comp adjf₂).homEquiv _ _).symm.injective
  -- the left-hand side
  have hL : ((ag₃.comp adjf₂).homEquiv _ _).symm
      (Rf.map ((conjugateEquiv (ah₁.comp ah₂) ah₃ γB.inv).app W) ≫
        (conjugateEquiv (adjf.comp ah₃) (ag₃.comp adjf₂) e₃.hom).app W) =
      e₃.hom.app (Rf.obj (Rh₁.obj (Rh₂.obj W))) ≫
        Lh₃.map (adjf.counit.app (Rh₁.obj (Rh₂.obj W))) ≫
        γB.inv.app (Rh₁.obj (Rh₂.obj W)) ≫ Lh₂.map (ah₁.counit.app (Rh₂.obj W)) ≫
        ah₂.counit.app W := by
    rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_counit,
      Adjunction.comp_counit_app]
    simp only [Functor.comp_map]
    rw [conjugateEquiv_counit_comp adjf adjf₂ ag₃ ah₃ e₃.hom W]
    have n2 := adjf.counit.naturality ((conjugateEquiv (ah₁.comp ah₂) ah₃ γB.inv).app W)
    simp only [Functor.comp_map, Functor.id_map] at n2
    erw [reassoc_of% (e₃.hom.naturality (Rf.map _)),
      ← Functor.map_comp_assoc, n2, Functor.map_comp, Category.assoc]
    have hc := conjugateEquiv_counit (ah₁.comp ah₂) ah₃ γB.inv W
    simp only [Adjunction.comp_counit_app] at hc
    rw [hc]
    rfl
  -- the right-hand side
  have hR : ((ag₃.comp adjf₂).homEquiv _ _).symm
      ((conjugateEquiv (adjf.comp ah₁) (ag₁.comp adjf₁) e₁.hom).app (Rh₂.obj W) ≫
        Rg₁.map ((conjugateEquiv (adjf₁.comp ah₂) (ag₂.comp adjf₂) e₂.hom).app W) ≫
        (conjugateEquiv (ag₁.comp ag₂) ag₃ γA.inv).app (Rf₂.obj W)) =
      Lf₂.map (γA.inv.app (Rf.obj (Rh₁.obj (Rh₂.obj W)))) ≫
        e₂.hom.app (Lg₁.obj (Rf.obj (Rh₁.obj (Rh₂.obj W)))) ≫
        Lh₂.map (e₁.hom.app (Rf.obj (Rh₁.obj (Rh₂.obj W)))) ≫
        Lh₂.map (Lh₁.map (adjf.counit.app (Rh₁.obj (Rh₂.obj W)))) ≫
        Lh₂.map (ah₁.counit.app (Rh₂.obj W)) ≫ ah₂.counit.app W := by
    rw [Adjunction.homEquiv_counit, Adjunction.comp_counit_app]
    simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
    -- the conjugate of `γA⁻¹`
    have hcA := congrArg Lf₂.map (conjugateEquiv_counit (ag₁.comp ag₂) ag₃ γA.inv (Rf₂.obj W))
    simp only [Adjunction.comp_counit_app, Functor.map_comp] at hcA
    rw [reassoc_of% hcA]
    -- `γA⁻¹` past `Lg₃ (Rg₁ PF₂)` and `Lg₃ PF₁`
    have n3a := congrArg Lf₂.map (γA.inv.naturality
      (Rg₁.map ((conjugateEquiv (adjf₁.comp ah₂) (ag₂.comp adjf₂) e₂.hom).app W)))
    simp only [Functor.comp_map, Functor.map_comp] at n3a
    rw [reassoc_of% n3a]
    have n3b := congrArg Lf₂.map (γA.inv.naturality
      ((conjugateEquiv (adjf.comp ah₁) (ag₁.comp adjf₁) e₁.hom).app (Rh₂.obj W)))
    simp only [Functor.comp_map, Functor.map_comp] at n3b
    rw [reassoc_of% n3b]
    -- the counit of `Lg₁ ⊣ Rg₁` past `PF₂`
    have n4 := congrArg (fun t => Lf₂.map (Lg₂.map t)) (ag₁.counit.naturality
      ((conjugateEquiv (adjf₁.comp ah₂) (ag₂.comp adjf₂) e₂.hom).app W))
    simp only [Functor.comp_map, Functor.id_map, Functor.map_comp] at n4
    rw [reassoc_of% n4]
    -- `PF₂` in counit form
    rw [conjugateEquiv_counit_comp adjf₁ adjf₂ ag₂ ah₂ e₂.hom W]
    -- `e₂` past `Lg₁ PF₁ ≫ εg₁`
    erw [reassoc_of% (e₂.hom.naturality (ag₁.counit.app (Rf₁.obj (Rh₂.obj W)))),
      reassoc_of% (e₂.hom.naturality (Lg₁.map ((conjugateEquiv (adjf.comp ah₁) (ag₁.comp adjf₁)
        e₁.hom).app (Rh₂.obj W))))]
    -- `PF₁` in counit form, under `Lh₂`
    have h1 := congrArg Lh₂.map (conjugateEquiv_counit_comp adjf adjf₁ ag₁ ah₁ e₁.hom
      (Rh₂.obj W))
    simp only [Functor.map_comp] at h1
    rw [reassoc_of% h1]
  refine hL.trans (Eq.trans ?_ hR.symm)
  rw [reassoc_of% hT']


end Paste

end Stacks.CategoryTheory.BaseChange
