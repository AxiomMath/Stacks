module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

/-!
# Comparisons of left derived functors along a cube

Left derived functors `L_g` of functors `F_g`, with comparisons `α_g : Q ⋙ L_g ⟶ F_g ⋙ Q`, are
arranged along a cube: four vertical squares `ρ_g : Lε ⋙ L_g ≅ L_{g₀} ⋙ Lε'` and 2-cells `Θ`, `Z`
on the top and bottom faces, each compatible with the comparisons through a degreewise
counterpart. The universal property of a left derived functor identified with the target
composite reduces the commutativity of the derived cube to that of the degreewise one.

## Main results

* `Stacks.Cohomology.DerivedBaseChangeComposition.leftDerived_comparison_cube`: the cube.
* `Stacks.Cohomology.DerivedBaseChangeComposition.fac_vcomp_inv`: comparisons of a composite
  `c₁ ≫ c₂ ≫ c₃⁻¹` of 2-cells.
* `Stacks.Cohomology.DerivedBaseChangeComposition.eqToIso_congr_fac`: transport along an
  equality of indices is compatible with comparisons.
* `Stacks.Cohomology.DerivedBaseChangeComposition.trans_hom_app_fac`: a comparison identity for a
  composite of isomorphisms from one for its components.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Cohomology.DerivedBaseChangeComposition

/-- **Comparisons of left derived functors along a cube.** Let the four squares `ρ_g` of left
derived functors around a cube be compatible with comparisons `α` through degreewise squares
`θ_g`, and let `Θ`, `Z` be 2-cells on the top and bottom faces, compatible with degreewise
2-cells `Θu`, `Zu`. If the degreewise cube commutes and the target composite is identified with
a left derived functor `H` compatibly with comparisons, the derived cube commutes. -/
theorem leftDerived_comparison_cube
    {K₁ K₂ K₃ K₄ K₅ K₆ K₇ K₈ D₁ D₂ D₃ D₄ D₅ D₆ D₇ D₈ : Type*}
    [Category* K₁] [Category* K₂] [Category* K₃] [Category* K₄]
    [Category* K₅] [Category* K₆] [Category* K₇] [Category* K₈]
    [Category* D₁] [Category* D₂] [Category* D₃] [Category* D₄]
    [Category* D₅] [Category* D₆] [Category* D₇] [Category* D₈]
    {Q₁ : K₁ ⥤ D₁} {Q₂ : K₂ ⥤ D₂} {Q₃ : K₃ ⥤ D₃} {Q₄ : K₄ ⥤ D₄}
    {Q₅ : K₅ ⥤ D₅} {Q₆ : K₆ ⥤ D₆} {Q₇ : K₇ ⥤ D₇} {Q₈ : K₈ ⥤ D₈}
    {Fq₀ : K₁ ⥤ K₂} {Fp₀ : K₂ ⥤ K₄} {Fs₀ : K₁ ⥤ K₃} {Fr₀ : K₃ ⥤ K₄}
    {FεT : K₁ ⥤ K₅} {FεW : K₂ ⥤ K₆} {FεT' : K₃ ⥤ K₇} {FεW' : K₄ ⥤ K₈}
    {Fq : K₅ ⥤ K₆} {Fp : K₆ ⥤ K₈} {Fs : K₅ ⥤ K₇} {Fr : K₇ ⥤ K₈}
    {Lq₀ : D₁ ⥤ D₂} {Lp₀ : D₂ ⥤ D₄} {Ls₀ : D₁ ⥤ D₃} {Lr₀ : D₃ ⥤ D₄}
    {LεT : D₁ ⥤ D₅} {LεW : D₂ ⥤ D₆} {LεT' : D₃ ⥤ D₇} {LεW' : D₄ ⥤ D₈}
    {Lq : D₅ ⥤ D₆} {Lp : D₆ ⥤ D₈} {Ls : D₅ ⥤ D₇} {Lr : D₇ ⥤ D₈}
    (αq₀ : Q₁ ⋙ Lq₀ ⟶ Fq₀ ⋙ Q₂) (αp₀ : Q₂ ⋙ Lp₀ ⟶ Fp₀ ⋙ Q₄)
    (αs₀ : Q₁ ⋙ Ls₀ ⟶ Fs₀ ⋙ Q₃) (αr₀ : Q₃ ⋙ Lr₀ ⟶ Fr₀ ⋙ Q₄)
    (αεT : Q₁ ⋙ LεT ⟶ FεT ⋙ Q₅) (αεW : Q₂ ⋙ LεW ⟶ FεW ⋙ Q₆)
    (αεT' : Q₃ ⋙ LεT' ⟶ FεT' ⋙ Q₇) (αεW' : Q₄ ⋙ LεW' ⟶ FεW' ⋙ Q₈)
    (αq : Q₅ ⋙ Lq ⟶ Fq ⋙ Q₆) (αp : Q₆ ⋙ Lp ⟶ Fp ⋙ Q₈)
    (αs : Q₅ ⋙ Ls ⟶ Fs ⋙ Q₇) (αr : Q₇ ⋙ Lr ⟶ Fr ⋙ Q₈)
    (ρq : LεT ⋙ Lq ≅ Lq₀ ⋙ LεW) (θq : FεT ⋙ Fq ≅ Fq₀ ⋙ FεW)
    (ρp : LεW ⋙ Lp ≅ Lp₀ ⋙ LεW') (θp : FεW ⋙ Fp ≅ Fp₀ ⋙ FεW')
    (ρs : LεT ⋙ Ls ≅ Ls₀ ⋙ LεT') (θs : FεT ⋙ Fs ≅ Fs₀ ⋙ FεT')
    (ρr : LεT' ⋙ Lr ≅ Lr₀ ⋙ LεW') (θr : FεT' ⋙ Fr ≅ Fr₀ ⋙ FεW')
    (facq : ∀ K, ρq.hom.app (Q₁.obj K) ≫ LεW.map (αq₀.app K) ≫ αεW.app (Fq₀.obj K) =
      Lq.map (αεT.app K) ≫ αq.app (FεT.obj K) ≫ Q₆.map (θq.hom.app K))
    (facp : ∀ K, ρp.hom.app (Q₂.obj K) ≫ LεW'.map (αp₀.app K) ≫ αεW'.app (Fp₀.obj K) =
      Lp.map (αεW.app K) ≫ αp.app (FεW.obj K) ≫ Q₈.map (θp.hom.app K))
    (facs : ∀ K, ρs.hom.app (Q₁.obj K) ≫ LεT'.map (αs₀.app K) ≫ αεT'.app (Fs₀.obj K) =
      Ls.map (αεT.app K) ≫ αs.app (FεT.obj K) ≫ Q₇.map (θs.hom.app K))
    (facr : ∀ K, ρr.hom.app (Q₃.obj K) ≫ LεW'.map (αr₀.app K) ≫ αεW'.app (Fr₀.obj K) =
      Lr.map (αεT'.app K) ≫ αr.app (FεT'.obj K) ≫ Q₈.map (θr.hom.app K))
    (Θ : Lq ⋙ Lp ⟶ Ls ⋙ Lr) (Θu : Fq ⋙ Fp ⟶ Fs ⋙ Fr)
    (facΘ : ∀ M, Θ.app (Q₅.obj M) ≫ Lr.map (αs.app M) ≫ αr.app (Fs.obj M) =
      Lp.map (αq.app M) ≫ αp.app (Fq.obj M) ≫ Q₈.map (Θu.app M))
    (Z : Lq₀ ⋙ Lp₀ ⟶ Ls₀ ⋙ Lr₀) (Zu : Fq₀ ⋙ Fp₀ ⟶ Fs₀ ⋙ Fr₀)
    (facZ : ∀ K, Z.app (Q₁.obj K) ≫ Lr₀.map (αs₀.app K) ≫ αr₀.app (Fs₀.obj K) =
      Lp₀.map (αq₀.app K) ≫ αp₀.app (Fq₀.obj K) ≫ Q₄.map (Zu.app K))
    {Lrs : D₅ ⥤ D₈} {Frs : K₅ ⥤ K₈} (αrs : Q₅ ⋙ Lrs ⟶ Frs ⋙ Q₈)
    (e₁ : Ls ⋙ Lr ≅ Lrs) (u₁ : Fs ⋙ Fr ⟶ Frs)
    (fac₁ : ∀ M, e₁.hom.app (Q₅.obj M) ≫ αrs.app M =
      Lr.map (αs.app M) ≫ αr.app (Fs.obj M) ≫ Q₈.map (u₁.app M))
    {H : D₁ ⥤ D₈} {FH : K₁ ⥤ K₈} (αH : Q₁ ⋙ H ⟶ FH ⋙ Q₈) (W : MorphismProperty K₁)
    [Q₁.IsLocalization W] [H.IsLeftDerivedFunctor αH W]
    (e₂ : LεT ⋙ Lrs ≅ H) (u₂ : FεT ⋙ Frs ⟶ FH)
    (fac₂ : ∀ K, e₂.hom.app (Q₁.obj K) ≫ αH.app K =
      Lrs.map (αεT.app K) ≫ αrs.app (FεT.obj K) ≫ Q₈.map (u₂.app K))
    (hu : ∀ K, Fp.map (θq.hom.app K) ≫ θp.hom.app (Fq₀.obj K) ≫ FεW'.map (Zu.app K) =
      Θu.app (FεT.obj K) ≫ Fr.map (θs.hom.app K) ≫ θr.hom.app (Fs₀.obj K))
    (Y : D₁) :
    ρp.inv.app (Lq₀.obj Y) ≫ Lp.map (ρq.inv.app Y) ≫ Θ.app (LεT.obj Y) =
      LεW'.map (Z.app Y) ≫ ρr.inv.app (Ls₀.obj Y) ≫ Lr.map (ρs.inv.app Y) := by
  let e : LεT ⋙ Ls ⋙ Lr ≅ H := Functor.isoWhiskerLeft LεT e₁ ≪≫ e₂
  let u : FεT ⋙ Fs ⋙ Fr ⟶ FH := Functor.whiskerLeft FεT u₁ ≫ u₂
  have face : ∀ K, e.hom.app (Q₁.obj K) ≫ αH.app K =
      Lr.map (Ls.map (αεT.app K)) ≫ Lr.map (αs.app (FεT.obj K)) ≫ αr.app (Fs.obj (FεT.obj K)) ≫
        Q₈.map (u.app K) := fun K => by
    have n := e₁.hom.naturality (αεT.app K)
    simp only [Functor.comp_obj, Functor.comp_map] at n
    simp only [e, u, Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
      Functor.whiskerLeft_app, Category.assoc, fac₂, Q₈.map_comp]
    rw [← reassoc_of% n, reassoc_of% (fac₁ (FεT.obj K))]
  replace hu : ∀ K, θp.inv.app (Fq₀.obj K) ≫ Fp.map (θq.inv.app K) ≫ Θu.app (FεT.obj K) =
      FεW'.map (Zu.app K) ≫ θr.inv.app (Fs₀.obj K) ≫ Fr.map (θs.inv.app K) := fun K => by
    rw [← cancel_epi (Fp.map (θq.hom.app K) ≫ θp.hom.app (Fq₀.obj K))]
    simp only [Category.assoc]
    conv_lhs => rw [Iso.hom_inv_id_app_assoc, ← Fp.map_comp_assoc, Iso.hom_inv_id_app]
    rw [reassoc_of% (hu K)]
    simp [← Fr.map_comp]
  have iq : ∀ K, ρq.inv.app (Q₁.obj K) ≫ Lq.map (αεT.app K) ≫ αq.app (FεT.obj K) =
      LεW.map (αq₀.app K) ≫ αεW.app (Fq₀.obj K) ≫ Q₆.map (θq.inv.app K) := fun K => by
    rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, reassoc_of% (facq K), ← Q₆.map_comp,
      Iso.hom_inv_id_app]
    simp
  have ip : ∀ K, ρp.inv.app (Q₂.obj K) ≫ Lp.map (αεW.app K) ≫ αp.app (FεW.obj K) =
      LεW'.map (αp₀.app K) ≫ αεW'.app (Fp₀.obj K) ≫ Q₈.map (θp.inv.app K) := fun K => by
    rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, reassoc_of% (facp K), ← Q₈.map_comp,
      Iso.hom_inv_id_app]
    simp
  have is : ∀ K, ρs.inv.app (Q₁.obj K) ≫ Ls.map (αεT.app K) ≫ αs.app (FεT.obj K) =
      LεT'.map (αs₀.app K) ≫ αεT'.app (Fs₀.obj K) ≫ Q₇.map (θs.inv.app K) := fun K => by
    rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, reassoc_of% (facs K), ← Q₇.map_comp,
      Iso.hom_inv_id_app]
    simp
  have ir : ∀ K, ρr.inv.app (Q₃.obj K) ≫ Lr.map (αεT'.app K) ≫ αr.app (FεT'.obj K) =
      LεW'.map (αr₀.app K) ≫ αεW'.app (Fr₀.obj K) ≫ Q₈.map (θr.inv.app K) := fun K => by
    rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, reassoc_of% (facr K), ← Q₈.map_comp,
      Iso.hom_inv_id_app]
    simp
  let τ₁ : Lq₀ ⋙ Lp₀ ⋙ LεW' ⟶ H :=
    Functor.whiskerLeft Lq₀ ρp.inv ≫ Functor.whiskerRight ρq.inv Lp ≫
      Functor.whiskerLeft LεT Θ ≫ e.hom
  let τ₂ : Lq₀ ⋙ Lp₀ ⋙ LεW' ⟶ H :=
    Functor.whiskerRight Z LεW' ≫ Functor.whiskerLeft Ls₀ ρr.inv ≫
      Functor.whiskerRight ρs.inv Lr ≫ e.hom
  have hτ : τ₁ = τ₂ := by
    refine H.leftDerived_ext αH W _ τ₁ τ₂ ?_
    ext K
    simp only [τ₁, τ₂, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.assoc, face]
    have n1 := Θ.naturality (αεT.app K)
    have n2 := αp.naturality (θq.inv.app K)
    have n3 := ρp.inv.naturality (αq₀.app K)
    have n4 := αr.naturality (θs.inv.app K)
    have n5 := ρr.inv.naturality (αs₀.app K)
    have n6 := αεW'.naturality (Zu.app K)
    simp only [Functor.comp_obj, Functor.comp_map] at n1 n2 n3 n4 n5 n6
    conv_lhs => rw [← reassoc_of% n1, reassoc_of% (facΘ (FεT.obj K)), ← Lp.map_comp_assoc,
      ← Lp.map_comp_assoc, Category.assoc, iq K, Lp.map_comp_assoc, Lp.map_comp_assoc,
      reassoc_of% n2, ← reassoc_of% n3, reassoc_of% (ip (Fq₀.obj K))]
    conv_rhs => rw [← Lr.map_comp_assoc, ← Lr.map_comp_assoc, Category.assoc, is K,
      Lr.map_comp_assoc, Lr.map_comp_assoc, reassoc_of% n4, ← reassoc_of% n5,
      reassoc_of% (ir (Fs₀.obj K)), ← LεW'.map_comp_assoc, ← LεW'.map_comp_assoc, Category.assoc,
      facZ K, LεW'.map_comp_assoc, LεW'.map_comp_assoc, reassoc_of% n6]
    simp only [← Q₈.map_comp]
    rw [reassoc_of% (hu K)]
  have h := NatTrans.congr_app hτ Y
  simp only [τ₁, τ₂, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  simpa only [Category.assoc] using
    (cancel_mono (e.hom.app Y)).1 (by simpa only [Category.assoc] using h)

/-- A comparison identity for `e₁ ≪≫ e₂` from one for its two components. -/
theorem trans_hom_app_fac {C D : Type*} [Category* C] [Category* D] {F G H : C ⥤ D}
    (e₁ : F ≅ G) (e₂ : G ≅ H) (X : C) {Y : D} (c : H.obj X ⟶ Y) {r : F.obj X ⟶ Y}
    (h : e₁.hom.app X ≫ e₂.hom.app X ≫ c = r) : (e₁ ≪≫ e₂).hom.app X ≫ c = r := by
  simpa using h

/-- Transport of a family of functors along an equality of indices is compatible with a family of
comparisons. -/
theorem eqToIso_congr_fac {ι K D K' D' : Type*} [Category* K] [Category* D] [Category* K']
    [Category* D'] {Q : K ⥤ D} {Q' : K' ⥤ D'} (L : ι → D ⥤ D') (F : ι → K ⥤ K')
    (α : ∀ i, Q ⋙ L i ⟶ F i ⋙ Q') {i j : ι} (h : i = j) (M : K) :
    (eqToIso (congrArg L h)).hom.app (Q.obj M) ≫ (α j).app M =
      (α i).app M ≫ Q'.map ((eqToIso (congrArg F h)).hom.app M) := by
  subst h
  simp

/-- **Comparisons of a composite 2-cell.** If `c₁`, `c₂`, `c₃` are compatible with comparisons
through degreewise isomorphisms `u₁`, `u₂`, `u₃`, so is `c₁ ≫ c₂ ≫ c₃⁻¹` through
`u₁ ≫ u₂ ≫ u₃⁻¹`. -/
theorem fac_vcomp_inv {K₅ K₆ K₇ K₈ D₅ D₆ D₇ D₈ : Type*}
    [Category* K₅] [Category* K₆] [Category* K₇] [Category* K₈]
    [Category* D₅] [Category* D₆] [Category* D₇] [Category* D₈]
    {Q₅ : K₅ ⥤ D₅} {Q₆ : K₆ ⥤ D₆} {Q₇ : K₇ ⥤ D₇} {Q₈ : K₈ ⥤ D₈}
    {Fq : K₅ ⥤ K₆} {Fp : K₆ ⥤ K₈} {Fs : K₅ ⥤ K₇} {Fr : K₇ ⥤ K₈}
    {Lq : D₅ ⥤ D₆} {Lp : D₆ ⥤ D₈} {Ls : D₅ ⥤ D₇} {Lr : D₇ ⥤ D₈}
    {αq : Q₅ ⋙ Lq ⟶ Fq ⋙ Q₆} {αp : Q₆ ⋙ Lp ⟶ Fp ⋙ Q₈}
    {αs : Q₅ ⋙ Ls ⟶ Fs ⋙ Q₇} {αr : Q₇ ⋙ Lr ⟶ Fr ⋙ Q₈}
    {L₁ L₂ : D₅ ⥤ D₈} {F₁ F₂ : K₅ ⥤ K₈} {α₁ : Q₅ ⋙ L₁ ⟶ F₁ ⋙ Q₈} {α₂ : Q₅ ⋙ L₂ ⟶ F₂ ⋙ Q₈}
    {c₁ : Lq ⋙ Lp ≅ L₁} {c₂ : L₁ ≅ L₂} {c₃ : Ls ⋙ Lr ≅ L₂}
    {u₁ : Fq ⋙ Fp ≅ F₁} {u₂ : F₁ ≅ F₂} {u₃ : Fs ⋙ Fr ≅ F₂}
    (h₁ : ∀ M, c₁.hom.app (Q₅.obj M) ≫ α₁.app M =
      Lp.map (αq.app M) ≫ αp.app (Fq.obj M) ≫ Q₈.map (u₁.hom.app M))
    (h₂ : ∀ M, c₂.hom.app (Q₅.obj M) ≫ α₂.app M = α₁.app M ≫ Q₈.map (u₂.hom.app M))
    (h₃ : ∀ M, c₃.hom.app (Q₅.obj M) ≫ α₂.app M =
      Lr.map (αs.app M) ≫ αr.app (Fs.obj M) ≫ Q₈.map (u₃.hom.app M)) (M : K₅) :
    (c₁.hom ≫ c₂.hom ≫ c₃.inv).app (Q₅.obj M) ≫ Lr.map (αs.app M) ≫ αr.app (Fs.obj M) =
      Lp.map (αq.app M) ≫ αp.app (Fq.obj M) ≫ Q₈.map ((u₁.hom ≫ u₂.hom ≫ u₃.inv).app M) := by
  have h₃' : c₃.inv.app (Q₅.obj M) ≫ Lr.map (αs.app M) ≫ αr.app (Fs.obj M) =
      α₂.app M ≫ Q₈.map (u₃.inv.app M) := by
    rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, reassoc_of% (h₃ M), ← Q₈.map_comp,
      Iso.hom_inv_id_app]
    simp
  simp only [NatTrans.comp_app, Category.assoc, Q₈.map_comp]
  rw [h₃', reassoc_of% (h₂ M), reassoc_of% (h₁ M)]

end Stacks.Cohomology.DerivedBaseChangeComposition
