module

public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology

/-!
# Comparisons of models of left derived functors along a commutative square

Let `Lz_g` and `LS_g` be left derived functors of degreewise functors `Pz_g` and `P_g` at two
models, and let `M_g : Lz_g ⋙ C ≅ C ⋙ LS_g` be isomorphisms through comparison functors `C`,
pinned on the image of the localization functors. Given a 2-cell `Θ` between composites of the
`Lz_g` along a commutative square and the composition isomorphisms of the `LS_g`, all pinned on
complexes, the isomorphisms `M_g` carry `Θ` to the composition isomorphisms as soon as the
degreewise counterparts agree.

## Main results

* `StacksDraft.DerivedModel.comp_comparison_chase`: one composite, on complexes.
* `StacksDraft.DerivedModel.modelIso_cube`: the cube.
-/

@[expose] public section

open CategoryTheory

namespace StacksDraft.DerivedModel

section Side

variable {H₁ H₂ H₃ D₁ D₂ D₃ E₁ E₂ E₃ : Type*} [Category* H₁] [Category* H₂] [Category* H₃]
  [Category* D₁] [Category* D₂] [Category* D₃] [Category* E₁] [Category* E₂] [Category* E₃]
  {Q₁ : H₁ ⥤ D₁} {Q₂ : H₂ ⥤ D₂} {Q₃ : H₃ ⥤ D₃} {Q'₁ : H₁ ⥤ E₁} {Q'₂ : H₂ ⥤ E₂}
  {Q'₃ : H₃ ⥤ E₃} {C₁ : D₁ ⥤ E₁} {C₂ : D₂ ⥤ E₂} {C₃ : D₃ ⥤ E₃}
  (sh₁ : Q'₁ ≅ Q₁ ⋙ C₁) (sh₂ : Q'₂ ≅ Q₂ ⋙ C₂) (sh₃ : Q'₃ ≅ Q₃ ⋙ C₃)
  {Pzg : H₁ ⥤ H₂} {Pzf : H₂ ⥤ H₃} {Pg : H₁ ⥤ H₂} {Pf : H₂ ⥤ H₃} {Pfg : H₁ ⥤ H₃}
  {Lzg : D₁ ⥤ D₂} {Lzf : D₂ ⥤ D₃} {LSg : E₁ ⥤ E₂} {LSf : E₂ ⥤ E₃} {LSfg : E₁ ⥤ E₃}
  (cmpZg : Q₁ ⋙ Lzg ⟶ Pzg ⋙ Q₂) (cmpZf : Q₂ ⋙ Lzf ⟶ Pzf ⋙ Q₃)
  (cmpLSg : Q'₁ ⋙ LSg ⟶ Pg ⋙ Q'₂) (cmpLSf : Q'₂ ⋙ LSf ⟶ Pf ⋙ Q'₃)
  (cmpLSfg : Q'₁ ⋙ LSfg ⟶ Pfg ⋙ Q'₃)
  (zpg : Pzg ≅ Pg) (zpf : Pzf ≅ Pf)
  (Mg : Lzg ⋙ C₂ ≅ C₁ ⋙ LSg) (Mf : Lzf ⋙ C₃ ≅ C₂ ⋙ LSf)
  (c : LSg ⋙ LSf ≅ LSfg) (β : Pg ⋙ Pf ≅ Pfg)

/-- **One composite, on complexes.** The comparisons of models for `g` and `f`, followed by the
composition isomorphism `c` at the second model and the comparison for the composite, are the
image of the comparisons at the first model followed by the degreewise composition `β`. -/
theorem comp_comparison_chase
    (hMg : ∀ K, Mg.hom.app (Q₁.obj K) ≫ LSg.map (sh₁.inv.app K) ≫ cmpLSg.app K =
      C₂.map (cmpZg.app K ≫ (Functor.isoWhiskerRight zpg Q₂).hom.app K) ≫
        sh₂.inv.app (Pg.obj K))
    (hMf : ∀ K, Mf.hom.app (Q₂.obj K) ≫ LSf.map (sh₂.inv.app K) ≫ cmpLSf.app K =
      C₃.map (cmpZf.app K ≫ (Functor.isoWhiskerRight zpf Q₃).hom.app K) ≫
        sh₃.inv.app (Pf.obj K))
    (hc : ∀ K, c.hom.app (Q'₁.obj K) ≫ cmpLSfg.app K =
      LSf.map (cmpLSg.app K) ≫ cmpLSf.app (Pg.obj K) ≫ Q'₃.map (β.hom.app K))
    (K : H₁) :
    Mf.hom.app (Lzg.obj (Q₁.obj K)) ≫ LSf.map (Mg.hom.app (Q₁.obj K)) ≫
        c.hom.app (C₁.obj (Q₁.obj K)) ≫ LSfg.map (sh₁.inv.app K) ≫ cmpLSfg.app K =
      C₃.map (Lzf.map (cmpZg.app K) ≫ cmpZf.app (Pzg.obj K) ≫
          Q₃.map (Pzf.map (zpg.hom.app K) ≫ zpf.hom.app (Pg.obj K) ≫ β.hom.app K)) ≫
        sh₃.inv.app (Pfg.obj K) := by
  have hcn := c.hom.naturality (sh₁.inv.app K)
  have hMfn := Mf.hom.naturality (cmpZg.app K ≫ (Functor.isoWhiskerRight zpg Q₂).hom.app K)
  have hZ := cmpZf.naturality (zpg.hom.app K)
  have hsh := sh₃.inv.naturality (β.hom.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hcn hMfn hZ hsh
  simp only [Functor.isoWhiskerRight_hom, Functor.whiskerRight_app] at hMg hMf hMfn
  rw [← reassoc_of% hcn, hc K, ← LSf.map_comp_assoc, ← LSf.map_comp_assoc, Category.assoc,
    hMg K, LSf.map_comp_assoc, ← reassoc_of% hMfn, reassoc_of% (hMf (Pg.obj K)), ← hsh]
  simp only [Functor.map_comp, Category.assoc, Functor.comp_obj]
  rw [← C₃.map_comp_assoc (Lzf.map (Q₂.map (zpg.hom.app K))), hZ]
  simp only [Functor.map_comp, Category.assoc]

end Side

section Cube

variable {H₁ H₂ H₃ H₄ D₁ D₂ D₃ D₄ E₁ E₂ E₃ E₄ : Type*} [Category* H₁] [Category* H₂]
  [Category* H₃] [Category* H₄] [Category* D₁] [Category* D₂] [Category* D₃] [Category* D₄]
  [Category* E₁] [Category* E₂] [Category* E₃] [Category* E₄]
  {Q₁ : H₁ ⥤ D₁} {Q₂ : H₂ ⥤ D₂} {Q₃ : H₃ ⥤ D₃} {Q₄ : H₄ ⥤ D₄} {Q'₁ : H₁ ⥤ E₁} {Q'₂ : H₂ ⥤ E₂}
  {Q'₃ : H₃ ⥤ E₃} {Q'₄ : H₄ ⥤ E₄} {C₁ : D₁ ⥤ E₁} {C₂ : D₂ ⥤ E₂} {C₃ : D₃ ⥤ E₃} {C₄ : D₄ ⥤ E₄}
  (sh₁ : Q'₁ ≅ Q₁ ⋙ C₁) (sh₂ : Q'₂ ≅ Q₂ ⋙ C₂) (sh₃ : Q'₃ ≅ Q₃ ⋙ C₃) (sh₄ : Q'₄ ≅ Q₄ ⋙ C₄)
  {Pzq : H₁ ⥤ H₂} {Pzp : H₂ ⥤ H₄} {Pzs : H₁ ⥤ H₃} {Pzr : H₃ ⥤ H₄}
  {Pq : H₁ ⥤ H₂} {Pp : H₂ ⥤ H₄} {Ps : H₁ ⥤ H₃} {Pr : H₃ ⥤ H₄} {Ppq Prs : H₁ ⥤ H₄}
  {Lzq : D₁ ⥤ D₂} {Lzp : D₂ ⥤ D₄} {Lzs : D₁ ⥤ D₃} {Lzr : D₃ ⥤ D₄}
  {LSq : E₁ ⥤ E₂} {LSp : E₂ ⥤ E₄} {LSs : E₁ ⥤ E₃} {LSr : E₃ ⥤ E₄} {LSpq LSrs : E₁ ⥤ E₄}
  (cmpZq : Q₁ ⋙ Lzq ⟶ Pzq ⋙ Q₂) (cmpZp : Q₂ ⋙ Lzp ⟶ Pzp ⋙ Q₄)
  (cmpZs : Q₁ ⋙ Lzs ⟶ Pzs ⋙ Q₃) (cmpZr : Q₃ ⋙ Lzr ⟶ Pzr ⋙ Q₄)
  (cmpLSq : Q'₁ ⋙ LSq ⟶ Pq ⋙ Q'₂) (cmpLSp : Q'₂ ⋙ LSp ⟶ Pp ⋙ Q'₄)
  (cmpLSs : Q'₁ ⋙ LSs ⟶ Ps ⋙ Q'₃) (cmpLSr : Q'₃ ⋙ LSr ⟶ Pr ⋙ Q'₄)
  (cmpLSpq : Q'₁ ⋙ LSpq ⟶ Ppq ⋙ Q'₄) (cmpLSrs : Q'₁ ⋙ LSrs ⟶ Prs ⋙ Q'₄)
  (zpq : Pzq ≅ Pq) (zpp : Pzp ≅ Pp) (zps : Pzs ≅ Ps) (zpr : Pzr ≅ Pr)
  (Mq : Lzq ⋙ C₂ ≅ C₁ ⋙ LSq) (Mp : Lzp ⋙ C₄ ≅ C₂ ⋙ LSp) (Ms : Lzs ⋙ C₃ ≅ C₁ ⋙ LSs)
  (Mr : Lzr ⋙ C₄ ≅ C₃ ⋙ LSr)
  (cpq : LSq ⋙ LSp ≅ LSpq) (crs : LSs ⋙ LSr ≅ LSrs) (βpq : Pq ⋙ Pp ≅ Ppq) (βrs : Ps ⋙ Pr ≅ Prs)
  (Θ : Lzq ⋙ Lzp ≅ Lzs ⋙ Lzr) (σz : Pzq ⋙ Pzp ≅ Pzs ⋙ Pzr) (κ : LSpq ≅ LSrs) (κH : Ppq ≅ Prs)

/-- **The cube for comparisons of models.** Along a commutative square, the comparisons of
models `M_g` of left derived functors carry a 2-cell `Θ` at the first model to the composition
isomorphisms at the second model, provided all of them are pinned on complexes and their
degreewise counterparts agree. -/
theorem modelIso_cube (W : MorphismProperty H₁) [hQ₁ : Q₁.IsLocalization W]
    [hQ'₁ : Q'₁.IsLocalization W]
    [hC₁ : C₁.IsEquivalence] [hLS : LSrs.IsLeftDerivedFunctor cmpLSrs W]
    (hMq : ∀ K, Mq.hom.app (Q₁.obj K) ≫ LSq.map (sh₁.inv.app K) ≫ cmpLSq.app K =
      C₂.map (cmpZq.app K ≫ (Functor.isoWhiskerRight zpq Q₂).hom.app K) ≫
        sh₂.inv.app (Pq.obj K))
    (hMp : ∀ K, Mp.hom.app (Q₂.obj K) ≫ LSp.map (sh₂.inv.app K) ≫ cmpLSp.app K =
      C₄.map (cmpZp.app K ≫ (Functor.isoWhiskerRight zpp Q₄).hom.app K) ≫
        sh₄.inv.app (Pp.obj K))
    (hMs : ∀ K, Ms.hom.app (Q₁.obj K) ≫ LSs.map (sh₁.inv.app K) ≫ cmpLSs.app K =
      C₃.map (cmpZs.app K ≫ (Functor.isoWhiskerRight zps Q₃).hom.app K) ≫
        sh₃.inv.app (Ps.obj K))
    (hMr : ∀ K, Mr.hom.app (Q₃.obj K) ≫ LSr.map (sh₃.inv.app K) ≫ cmpLSr.app K =
      C₄.map (cmpZr.app K ≫ (Functor.isoWhiskerRight zpr Q₄).hom.app K) ≫
        sh₄.inv.app (Pr.obj K))
    (hcpq : ∀ K, cpq.hom.app (Q'₁.obj K) ≫ cmpLSpq.app K =
      LSp.map (cmpLSq.app K) ≫ cmpLSp.app (Pq.obj K) ≫ Q'₄.map (βpq.hom.app K))
    (hcrs : ∀ K, crs.hom.app (Q'₁.obj K) ≫ cmpLSrs.app K =
      LSr.map (cmpLSs.app K) ≫ cmpLSr.app (Ps.obj K) ≫ Q'₄.map (βrs.hom.app K))
    (hΘ : ∀ K, Θ.hom.app (Q₁.obj K) ≫ Lzr.map (cmpZs.app K) ≫ cmpZr.app (Pzs.obj K) =
      Lzp.map (cmpZq.app K) ≫ cmpZp.app (Pzq.obj K) ≫ Q₄.map (σz.hom.app K))
    (hκ : ∀ K, κ.hom.app (Q'₁.obj K) ≫ cmpLSrs.app K = cmpLSpq.app K ≫ Q'₄.map (κH.hom.app K))
    (hH : ∀ K, σz.hom.app K ≫ Pzr.map (zps.hom.app K) ≫ zpr.hom.app (Ps.obj K) ≫
        βrs.hom.app K =
      Pzp.map (zpq.hom.app K) ≫ zpp.hom.app (Pq.obj K) ≫ βpq.hom.app K ≫ κH.hom.app K)
    (Y : D₁) :
    C₄.map (Θ.hom.app Y) ≫ Mr.hom.app (Lzs.obj Y) ≫ LSr.map (Ms.hom.app Y) =
      Mp.hom.app (Lzq.obj Y) ≫ LSp.map (Mq.hom.app Y) ≫ cpq.hom.app (C₁.obj Y) ≫
        κ.hom.app (C₁.obj Y) ≫ crs.inv.app (C₁.obj Y) := by
  have := isLeftDerivedFunctor_comp_isEquivalence W cmpLSrs sh₁.symm
  have key : ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight Θ.hom C₄ ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft Lzs Mr.hom ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight Ms.hom LSr ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft C₁ crs.hom :
        Lzq ⋙ Lzp ⋙ C₄ ⟶ C₁ ⋙ LSrs) =
      Functor.whiskerLeft Lzq Mp.hom ≫ (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight Mq.hom LSp ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft C₁ (cpq.hom ≫ κ.hom) := by
    refine (C₁ ⋙ LSrs).leftDerived_ext (transportLeftDerivedCounit cmpLSrs sh₁.symm) W _ _ _
      (NatTrans.ext (funext fun K => ?_))
    have h₁ := comp_comparison_chase sh₁ sh₃ sh₄ cmpZs cmpZr cmpLSs cmpLSr cmpLSrs zps zpr Ms Mr
      crs βrs hMs hMr hcrs K
    have h₂ := comp_comparison_chase sh₁ sh₂ sh₄ cmpZq cmpZp cmpLSq cmpLSp cmpLSpq zpq zpp Mq Mp
      cpq βpq hMq hMp hcpq K
    have hκn := κ.hom.naturality (sh₁.inv.app K)
    have hsh := sh₄.inv.naturality (κH.hom.app K)
    simp only [Functor.comp_obj, Functor.comp_map] at hκn hsh
    simp only [transportLeftDerivedCounit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.assoc, Functor.comp_obj, Iso.symm_hom]
    rw [h₁, ← reassoc_of% hκn, hκ, reassoc_of% h₂, ← hsh, ← C₄.map_comp_assoc,
      ← C₄.map_comp_assoc, Category.assoc, Category.assoc, reassoc_of% hΘ K]
    simp only [Category.assoc, ← Q₄.map_comp, hH K]
  have hY := NatTrans.congr_app key Y
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Functor.comp_obj] at hY
  rw [← cancel_mono (crs.hom.app (C₁.obj Y))]
  simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using hY

end Cube

section Chase

variable {C : Type*} [Category* C]

/-- A diagram chase: `ψ = a ≫ b ≫ c ≫ d ≫ i ≫ j ≫ l`, followed by `X ≫ Y = lh ≫ jh` where
`lh` inverts `l`, then by `Z`, is `R` as soon as `i ≫ j ≫ jh ≫ Z = w` and
`a ≫ b ≫ c ≫ d ≫ w = R`. -/
theorem comp_chase_square {O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ O₁₀ : C} (ψ : O₀ ⟶ O₇)
    (a : O₀ ⟶ O₁) (b : O₁ ⟶ O₂) (c : O₂ ⟶ O₃) (d : O₃ ⟶ O₄) (i : O₄ ⟶ O₅) (j : O₅ ⟶ O₆)
    (l : O₆ ⟶ O₇) (X : O₇ ⟶ O₈) (Y : O₈ ⟶ O₉) (Z : O₉ ⟶ O₁₀) (lh : O₇ ⟶ O₆)
    (jh : O₆ ⟶ O₉) (w : O₄ ⟶ O₁₀) (R : O₀ ⟶ O₁₀)
    (e : ψ = a ≫ b ≫ c ≫ d ≫ i ≫ j ≫ l) (hl : l ≫ lh = 𝟙 _) (hr : X ≫ Y = lh ≫ jh)
    (hjZ : i ≫ j ≫ jh ≫ Z = w) (hR : a ≫ b ≫ c ≫ d ≫ w = R) :
    ψ ≫ X ≫ Y ≫ Z = R := by
  rw [e, ← hR, ← hjZ, reassoc_of% hr]
  simp only [Category.assoc, reassoc_of% hl]

end Chase

section Degreewise

variable {A₁ A₂ A₃ A₄ : Type*} [Category* A₁] [Category* A₂] [Category* A₃] [Category* A₄]
  [Preadditive A₁] [Preadditive A₂] [Preadditive A₃] [Preadditive A₄]
  (c : ComplexShape ℤ)
  {Fzq : A₁ ⥤ A₂} {Fzp : A₂ ⥤ A₄} {Fzs : A₁ ⥤ A₃} {Fzr : A₃ ⥤ A₄}
  {Fq : A₁ ⥤ A₂} {Fp : A₂ ⥤ A₄} {Fs : A₁ ⥤ A₃} {Fr : A₃ ⥤ A₄} {Fzpq Fzrs Fpq Frs : A₁ ⥤ A₄}
  [hFzq : Fzq.Additive] [hFzp : Fzp.Additive] [hFzs : Fzs.Additive] [hFzr : Fzr.Additive]
  [hFq : Fq.Additive] [hFp : Fp.Additive] [hFs : Fs.Additive] [hFr : Fr.Additive]
  [hFzpq : Fzpq.Additive] [hFzrs : Fzrs.Additive] [hFpq : Fpq.Additive] [hFrs : Frs.Additive]
  (zq : Fzq ≅ Fq) (zp : Fzp ≅ Fp) (zs : Fzs ≅ Fs) (zr : Fzr ≅ Fr)
  (γpq : Fzpq ≅ Fzq ⋙ Fzp) (γrs : Fzrs ≅ Fzs ⋙ Fzr) (bpq : Fq ⋙ Fp ≅ Fpq) (brs : Fs ⋙ Fr ≅ Frs)
  (k : Fpq ≅ Frs) (ψ : Fzq ⋙ Fzp ≅ Fzs ⋙ Fzr)

/-- **A 2-cell of additive functors along a square, on homotopy categories.** If the 2-cell
`ψ : Fzq ⋙ Fzp ≅ Fzs ⋙ Fzr`, read through isomorphisms `Fz ≅ F`, is the composite of the
composition isomorphisms `bpq`, `k`, `brs⁻¹`, the same holds for the induced isomorphisms of
homotopy categories. -/
theorem mapHomotopyCategory_square_comp
    (hψ : ∀ M, ψ.hom.app M ≫ Fzr.map (zs.hom.app M) ≫ zr.hom.app (Fs.obj M) ≫ brs.hom.app M =
      Fzp.map (zq.hom.app M) ≫ zp.hom.app (Fq.obj M) ≫ bpq.hom.app M ≫ k.hom.app M)
    (K : HomotopyCategory A₁ c) :
    (Functor.mapHomotopyCategoryCompIso γpq.symm c ≪≫
        Stacks.Homology.mapHomotopyCategoryIso (γpq ≪≫ ψ ≪≫ γrs.symm) c ≪≫
        (Functor.mapHomotopyCategoryCompIso γrs.symm c).symm).hom.app K ≫
      (Fzr.mapHomotopyCategory c).map ((Stacks.Homology.mapHomotopyCategoryIso zs c).hom.app K) ≫
      (Stacks.Homology.mapHomotopyCategoryIso zr c).hom.app ((Fs.mapHomotopyCategory c).obj K) ≫
      (Functor.mapHomotopyCategoryCompIso brs c).hom.app K =
    (Fzp.mapHomotopyCategory c).map ((Stacks.Homology.mapHomotopyCategoryIso zq c).hom.app K) ≫
      (Stacks.Homology.mapHomotopyCategoryIso zp c).hom.app ((Fq.mapHomotopyCategory c).obj K) ≫
      (Functor.mapHomotopyCategoryCompIso bpq c).hom.app K ≫
      (Stacks.Homology.mapHomotopyCategoryIso k c).hom.app K := by
  rcases K with ⟨K⟩
  have key : ((NatTrans.mapHomologicalComplex γpq.inv c).app K ≫
        (NatTrans.mapHomologicalComplex (γpq ≪≫ ψ ≪≫ γrs.symm).hom c).app K ≫
        (NatTrans.mapHomologicalComplex γrs.hom c).app K) ≫
      (Fzr.mapHomologicalComplex c).map ((NatTrans.mapHomologicalComplex zs.hom c).app K) ≫
      (NatTrans.mapHomologicalComplex zr.hom c).app ((Fs.mapHomologicalComplex c).obj K) ≫
      (NatTrans.mapHomologicalComplex brs.hom c).app K =
    (Fzp.mapHomologicalComplex c).map ((NatTrans.mapHomologicalComplex zq.hom c).app K) ≫
      (NatTrans.mapHomologicalComplex zp.hom c).app ((Fq.mapHomologicalComplex c).obj K) ≫
      (NatTrans.mapHomologicalComplex bpq.hom c).app K ≫
      (NatTrans.mapHomologicalComplex k.hom c).app K := by
    ext n
    simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplex_map_f, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
      Category.assoc, Iso.inv_hom_id_app_assoc]
    exact hψ (K.X n)
  have := congrArg (HomotopyCategory.quotient A₄ c).map key
  simp only [Functor.map_comp] at this
  exact this

/-- `mapHomotopyCategory_square_comp`, with the isomorphisms of homotopy categories given as
variables equal to their constructions. -/
theorem mapHomotopyCategory_square_comp'
    (hψ : ∀ M, ψ.hom.app M ≫ Fzr.map (zs.hom.app M) ≫ zr.hom.app (Fs.obj M) ≫ brs.hom.app M =
      Fzp.map (zq.hom.app M) ≫ zp.hom.app (Fq.obj M) ≫ bpq.hom.app M ≫ k.hom.app M)
    (σz : Fzq.mapHomotopyCategory c ⋙ Fzp.mapHomotopyCategory c ≅
      Fzs.mapHomotopyCategory c ⋙ Fzr.mapHomotopyCategory c)
    (hσ : σz = Functor.mapHomotopyCategoryCompIso γpq.symm c ≪≫
        Stacks.Homology.mapHomotopyCategoryIso (γpq ≪≫ ψ ≪≫ γrs.symm) c ≪≫
        (Functor.mapHomotopyCategoryCompIso γrs.symm c).symm)
    (zHq : Fzq.mapHomotopyCategory c ≅ Fq.mapHomotopyCategory c)
    (hzq : zHq = Stacks.Homology.mapHomotopyCategoryIso zq c)
    (zHp : Fzp.mapHomotopyCategory c ≅ Fp.mapHomotopyCategory c)
    (hzp : zHp = Stacks.Homology.mapHomotopyCategoryIso zp c)
    (zHs : Fzs.mapHomotopyCategory c ≅ Fs.mapHomotopyCategory c)
    (hzs : zHs = Stacks.Homology.mapHomotopyCategoryIso zs c)
    (zHr : Fzr.mapHomotopyCategory c ≅ Fr.mapHomotopyCategory c)
    (hzr : zHr = Stacks.Homology.mapHomotopyCategoryIso zr c)
    (βpq : Fq.mapHomotopyCategory c ⋙ Fp.mapHomotopyCategory c ≅ Fpq.mapHomotopyCategory c)
    (hβpq : βpq = Functor.mapHomotopyCategoryCompIso bpq c)
    (βrs : Fs.mapHomotopyCategory c ⋙ Fr.mapHomotopyCategory c ≅ Frs.mapHomotopyCategory c)
    (hβrs : βrs = Functor.mapHomotopyCategoryCompIso brs c)
    (κH : Fpq.mapHomotopyCategory c ≅ Frs.mapHomotopyCategory c)
    (hκH : κH = Stacks.Homology.mapHomotopyCategoryIso k c)
    (K : HomotopyCategory A₁ c) :
    σz.hom.app K ≫ (Fzr.mapHomotopyCategory c).map (zHs.hom.app K) ≫
      zHr.hom.app ((Fs.mapHomotopyCategory c).obj K) ≫ βrs.hom.app K =
    (Fzp.mapHomotopyCategory c).map (zHq.hom.app K) ≫
      zHp.hom.app ((Fq.mapHomotopyCategory c).obj K) ≫ βpq.hom.app K ≫ κH.hom.app K := by
  subst hσ hzq hzp hzs hzr hβpq hβrs hκH
  exact mapHomotopyCategory_square_comp c zq zp zs zr γpq γrs bpq brs k ψ hψ K

end Degreewise

end StacksDraft.DerivedModel
