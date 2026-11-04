module

public import Mathlib.CategoryTheory.CatCommSq
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Horizontal inverses of 2-commutative squares along a cube

Let `E_X : 𝒜_X ≌ ℬ_X` be equivalences indexed by the corners of a commutative square
`p ≫ q = r ≫ s`, with 2-commutative squares `h_g : E.functor ⋙ G_g ≅ F_g ⋙ E'.functor` for
the four edges, and 2-cells `Θ_𝒜 : F_q ⋙ F_p ⟶ F_s ⋙ F_r`, `Θ_ℬ : G_q ⋙ G_p ⟶ G_s ⋙ G_r`.
If the four squares paste compatibly with the two 2-cells, so do their horizontal inverses
`CatCommSq.hInv`.

## Main results

* `CategoryTheory.CatCommSq.functor_map_hInv_iso_inv_app`: the image of the horizontal inverse
  under the bottom equivalence.
* `CategoryTheory.CatCommSq.hInv_cube`: the cube for the horizontal inverses.
* `CategoryTheory.CatCommSq.layeredSquare_inv_app`: the components of the inverse of a square
  pasted from a lower and an upper square.
* `CategoryTheory.CatCommSq.hInv_cube_of_layers`: the same for squares between full
  subcategories that are read, in the ambient categories, as pastes of two layers of squares.
-/

@[expose] public section

namespace CategoryTheory.CatCommSq

section Square

variable {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  (T : C₁ ≌ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ≌ C₄)

/-- The horizontal inverse of a square, read through the bottom equivalence: the counit, then
`R` of the inverse counit, then the square. -/
theorem functor_map_hInv_iso_inv_app (h : CatCommSq T.functor L R B.functor) (X : C₂) :
    B.functor.map ((hInv T L R B h).iso.inv.app X) =
      B.counitIso.hom.app (R.obj X) ≫ R.map (T.counitIso.inv.app X) ≫
        h.iso.hom.app (T.inverse.obj X) := by
  rw [hInv_iso_inv_app]
  simp [Equivalence.fun_inv_map, ← Equivalence.counit_app_functor]

end Square

section Cube

variable {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Type*} [Category* A₁] [Category* A₂] [Category* A₃]
  [Category* A₄] [Category* B₁] [Category* B₂] [Category* B₃] [Category* B₄]
  (E₁ : A₁ ≌ B₁) (E₂ : A₂ ≌ B₂) (E₃ : A₃ ≌ B₃) (E₄ : A₄ ≌ B₄)
  (Fq : A₁ ⥤ A₂) (Fp : A₂ ⥤ A₄) (Fs : A₁ ⥤ A₃) (Fr : A₃ ⥤ A₄)
  (Gq : B₁ ⥤ B₂) (Gp : B₂ ⥤ B₄) (Gs : B₁ ⥤ B₃) (Gr : B₃ ⥤ B₄)

/-- **Horizontal inverses along a cube.** If the four 2-commutative squares `h_g` paste
compatibly with the 2-cells `Θ_𝒜` and `Θ_ℬ`, so do their horizontal inverses. -/
theorem hInv_cube (hq : CatCommSq E₁.functor Fq Gq E₂.functor)
    (hp : CatCommSq E₂.functor Fp Gp E₄.functor) (hs : CatCommSq E₁.functor Fs Gs E₃.functor)
    (hr : CatCommSq E₃.functor Fr Gr E₄.functor)
    (ΘA : ∀ Y : A₁, Fp.obj (Fq.obj Y) ⟶ Fr.obj (Fs.obj Y)) (ΘB : Gq ⋙ Gp ⟶ Gs ⋙ Gr)
    (hcube : ∀ Y : A₁, E₄.functor.map (ΘA Y) ≫ hr.iso.inv.app (Fs.obj Y) ≫
        Gr.map (hs.iso.inv.app Y) =
      hp.iso.inv.app (Fq.obj Y) ≫ Gp.map (hq.iso.inv.app Y) ≫ ΘB.app (E₁.functor.obj Y))
    (X : B₁) :
    (hInv E₂ Fp Gp E₄ hp).iso.inv.app (Gq.obj X) ≫
        Fp.map ((hInv E₁ Fq Gq E₂ hq).iso.inv.app X) ≫ ΘA (E₁.inverse.obj X) =
      E₄.inverse.map (ΘB.app X) ≫ (hInv E₃ Fr Gr E₄ hr).iso.inv.app (Gs.obj X) ≫
        Fr.map ((hInv E₁ Fs Gs E₃ hs).iso.inv.app X) := by
  apply E₄.functor.map_injective
  have hc : Gp.map (hq.iso.hom.app (E₁.inverse.obj X)) ≫
      hp.iso.hom.app (Fq.obj (E₁.inverse.obj X)) ≫ E₄.functor.map (ΘA (E₁.inverse.obj X)) =
      ΘB.app (E₁.functor.obj (E₁.inverse.obj X)) ≫ Gr.map (hs.iso.hom.app (E₁.inverse.obj X)) ≫
        hr.iso.hom.app (Fs.obj (E₁.inverse.obj X)) := by
    rw [← cancel_epi (hp.iso.inv.app (Fq.obj (E₁.inverse.obj X)) ≫
      Gp.map (hq.iso.inv.app (E₁.inverse.obj X)))]
    simp only [Category.assoc]
    rw [← reassoc_of% (hcube (E₁.inverse.obj X))]
    simp [← Functor.map_comp_assoc]
  have hn₁ := hp.iso.hom.naturality ((hInv E₁ Fq Gq E₂ hq).iso.inv.app X)
  have hn₂ := hr.iso.hom.naturality ((hInv E₁ Fs Gs E₃ hs).iso.inv.app X)
  have hΘ := ΘB.naturality (E₁.counitIso.inv.app X)
  simp only [Functor.comp_obj, Functor.comp_map] at hn₁ hn₂ hΘ
  simp only [Functor.map_comp]
  rw [functor_map_hInv_iso_inv_app E₂ Fp Gp E₄ hp, functor_map_hInv_iso_inv_app E₃ Fr Gr E₄ hr,
    Equivalence.fun_inv_map]
  simp only [Category.assoc]
  rw [← reassoc_of% hn₁, ← hn₂, functor_map_hInv_iso_inv_app E₁ Fq Gq E₂ hq,
    functor_map_hInv_iso_inv_app E₁ Fs Gs E₃ hs]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Gp.map_comp_assoc, ← Gr.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [hc, reassoc_of% hΘ]
  simp

end Cube

section LayeredCube

variable {𝒟T 𝒟W 𝒟T' 𝒟W' 𝒵T 𝒵W 𝒵T' 𝒵W' ℰT ℰW ℰT' ℰW' : Type*}
  {_ : Category 𝒟T} {_ : Category 𝒟W} {_ : Category 𝒟T'} {_ : Category 𝒟W'}
  {_ : Category 𝒵T} {_ : Category 𝒵W} {_ : Category 𝒵T'} {_ : Category 𝒵W'}
  {_ : Category ℰT} {_ : Category ℰW} {_ : Category ℰT'} {_ : Category ℰW'}
  {PT : ObjectProperty 𝒟T} {PW : ObjectProperty 𝒟W} {PT' : ObjectProperty 𝒟T'}
  {PW' : ObjectProperty 𝒟W'} {QT : ObjectProperty ℰT} {QW : ObjectProperty ℰW}
  {QT' : ObjectProperty ℰT'} {QW' : ObjectProperty ℰW'}

/-- The square `sq_g` of a layered square, read componentwise: `ε'(M_g⁻¹) ≫ ρ_g⁻¹`. -/
theorem layeredSquare_inv_app {𝒟 𝒟' 𝒵 𝒵' ℰ ℰ' : Type*} {_ : Category 𝒟} {_ : Category 𝒟'}
    {_ : Category 𝒵} {_ : Category 𝒵'} {_ : Category ℰ} {_ : Category ℰ'}
    {L : 𝒟 ⥤ 𝒟'} {Z : 𝒵 ⥤ 𝒵'} {E : ℰ ⥤ ℰ'} {c : 𝒟 ⥤ 𝒵} {c' : 𝒟' ⥤ 𝒵'} {ε : 𝒵 ⥤ ℰ}
    {ε' : 𝒵' ⥤ ℰ'} (M : c ⋙ Z ≅ L ⋙ c') (ρ : ε ⋙ E ≅ Z ⋙ ε') (sq : c ⋙ ε ⋙ E ≅ L ⋙ c' ⋙ ε')
    (hsq : sq = Functor.isoWhiskerLeft c ρ ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight M ε' ≪≫ Functor.associator _ _ _) (X : 𝒟) :
    sq.inv.app X = ε'.map (M.inv.app X) ≫ ρ.inv.app (c.obj X) := by
  subst hsq
  simp

/-- **Pseudo-functoriality of horizontal inverses of layered squares.** Squares
`σ_g : F_g ⋙ E' ≅ E ⋙ G_g` between full subcategories, each read in the ambient categories as
the paste `ε'(M_g⁻¹) ≫ ρ_g⁻¹` of a lower square `M_g` and an upper square `ρ_g` (up to the
comparisons `e`), paste along a cube as soon as the `M_g` paste with the lower 2-cells and the
`ρ_g` with the upper ones. -/
theorem hInv_cube_of_layers
    (ET : PT.FullSubcategory ≌ QT.FullSubcategory) (EW : PW.FullSubcategory ≌ QW.FullSubcategory)
    (ET' : PT'.FullSubcategory ≌ QT'.FullSubcategory)
    (EW' : PW'.FullSubcategory ≌ QW'.FullSubcategory)
    (Lq₀ : 𝒟T ⥤ 𝒟W) (hLq₀ : ∀ X, PW ((PT.ι ⋙ Lq₀).obj X))
    (Lp₀ : 𝒟W ⥤ 𝒟W') (hLp₀ : ∀ X, PW' ((PW.ι ⋙ Lp₀).obj X))
    (Ls₀ : 𝒟T ⥤ 𝒟T') (hLs₀ : ∀ X, PT' ((PT.ι ⋙ Ls₀).obj X))
    (Lr₀ : 𝒟T' ⥤ 𝒟W') (hLr₀ : ∀ X, PW' ((PT'.ι ⋙ Lr₀).obj X))
    (Eq : ℰT ⥤ ℰW) (hEq : ∀ X, QW ((QT.ι ⋙ Eq).obj X))
    (Ep : ℰW ⥤ ℰW') (hEp : ∀ X, QW' ((QW.ι ⋙ Ep).obj X))
    (Es : ℰT ⥤ ℰT') (hEs : ∀ X, QT' ((QT.ι ⋙ Es).obj X))
    (Er : ℰT' ⥤ ℰW') (hEr : ∀ X, QW' ((QT'.ι ⋙ Er).obj X))
    {Zq : 𝒵T ⥤ 𝒵W} {Zp : 𝒵W ⥤ 𝒵W'} {Zs : 𝒵T ⥤ 𝒵T'} {Zr : 𝒵T' ⥤ 𝒵W'}
    {cT : 𝒟T ⥤ 𝒵T} {cW : 𝒟W ⥤ 𝒵W} {cT' : 𝒟T' ⥤ 𝒵T'} {cW' : 𝒟W' ⥤ 𝒵W'}
    {εT : 𝒵T ⥤ ℰT} {εW : 𝒵W ⥤ ℰW} {εT' : 𝒵T' ⥤ ℰT'} {εW' : 𝒵W' ⥤ ℰW'}
    (eT : ET.functor ⋙ QT.ι ≅ PT.ι ⋙ cT ⋙ εT) (eW : EW.functor ⋙ QW.ι ≅ PW.ι ⋙ cW ⋙ εW)
    (eT' : ET'.functor ⋙ QT'.ι ≅ PT'.ι ⋙ cT' ⋙ εT')
    (eW' : EW'.functor ⋙ QW'.ι ≅ PW'.ι ⋙ cW' ⋙ εW')
    (Mq : cT ⋙ Zq ≅ Lq₀ ⋙ cW) (Mp : cW ⋙ Zp ≅ Lp₀ ⋙ cW') (Ms : cT ⋙ Zs ≅ Ls₀ ⋙ cT')
    (Mr : cT' ⋙ Zr ≅ Lr₀ ⋙ cW')
    (ρq : εT ⋙ Eq ≅ Zq ⋙ εW) (ρp : εW ⋙ Ep ≅ Zp ⋙ εW') (ρs : εT ⋙ Es ≅ Zs ⋙ εT')
    (ρr : εT' ⋙ Er ≅ Zr ⋙ εW')
    (sqq : cT ⋙ εT ⋙ Eq ≅ Lq₀ ⋙ cW ⋙ εW)
    (hsqq : sqq = Functor.isoWhiskerLeft cT ρq ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight Mq εW ≪≫ Functor.associator _ _ _)
    (sqp : cW ⋙ εW ⋙ Ep ≅ Lp₀ ⋙ cW' ⋙ εW')
    (hsqp : sqp = Functor.isoWhiskerLeft cW ρp ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight Mp εW' ≪≫ Functor.associator _ _ _)
    (sqs : cT ⋙ εT ⋙ Es ≅ Ls₀ ⋙ cT' ⋙ εT')
    (hsqs : sqs = Functor.isoWhiskerLeft cT ρs ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight Ms εT' ≪≫ Functor.associator _ _ _)
    (sqr : cT' ⋙ εT' ⋙ Er ≅ Lr₀ ⋙ cW' ⋙ εW')
    (hsqr : sqr = Functor.isoWhiskerLeft cT' ρr ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight Mr εW' ≪≫ Functor.associator _ _ _)
    (σq : PW.lift (PT.ι ⋙ Lq₀) hLq₀ ⋙ EW.functor ≅ ET.functor ⋙ QW.lift (QT.ι ⋙ Eq) hEq)
    (hσq : ∀ X, (σq.hom.app X).hom = eW.hom.app ((PW.lift (PT.ι ⋙ Lq₀) hLq₀).obj X) ≫
      sqq.inv.app X.obj ≫ Eq.map (eT.inv.app X))
    (σp : PW'.lift (PW.ι ⋙ Lp₀) hLp₀ ⋙ EW'.functor ≅ EW.functor ⋙ QW'.lift (QW.ι ⋙ Ep) hEp)
    (hσp : ∀ X, (σp.hom.app X).hom = eW'.hom.app ((PW'.lift (PW.ι ⋙ Lp₀) hLp₀).obj X) ≫
      sqp.inv.app X.obj ≫ Ep.map (eW.inv.app X))
    (σs : PT'.lift (PT.ι ⋙ Ls₀) hLs₀ ⋙ ET'.functor ≅ ET.functor ⋙ QT'.lift (QT.ι ⋙ Es) hEs)
    (hσs : ∀ X, (σs.hom.app X).hom = eT'.hom.app ((PT'.lift (PT.ι ⋙ Ls₀) hLs₀).obj X) ≫
      sqs.inv.app X.obj ≫ Es.map (eT.inv.app X))
    (σr : PW'.lift (PT'.ι ⋙ Lr₀) hLr₀ ⋙ EW'.functor ≅ ET'.functor ⋙ QW'.lift (QT'.ι ⋙ Er) hEr)
    (hσr : ∀ X, (σr.hom.app X).hom = eW'.hom.app ((PW'.lift (PT'.ι ⋙ Lr₀) hLr₀).obj X) ≫
      sqr.inv.app X.obj ≫ Er.map (eT'.inv.app X))
    (θ₁ : Eq ⋙ Ep ⟶ Es ⋙ Er) (Zd : Zq ⋙ Zp ⟶ Zs ⋙ Zr)
    (ΘS : ∀ X, Lp₀.obj (Lq₀.obj X) ⟶ Lr₀.obj (Ls₀.obj X))
    (hL1 : ∀ Y, ρp.inv.app (Zq.obj Y) ≫ Ep.map (ρq.inv.app Y) ≫ θ₁.app (εT.obj Y) =
      εW'.map (Zd.app Y) ≫ ρr.inv.app (Zs.obj Y) ≫ Er.map (ρs.inv.app Y))
    (hL2 : ∀ X, Mp.inv.app (Lq₀.obj X) ≫ Zp.map (Mq.inv.app X) ≫ Zd.app (cT.obj X) =
      cW'.map (ΘS X) ≫ Mr.inv.app (Ls₀.obj X) ≫ Zr.map (Ms.inv.app X))
    (P : QT.FullSubcategory) :
    (PW'.lift (PW.ι ⋙ Lp₀) hLp₀).map ((hInv ET (PW.lift (PT.ι ⋙ Lq₀) hLq₀)
        (QW.lift (QT.ι ⋙ Eq) hEq) EW ⟨σq.symm⟩).iso.hom.app P) ≫
      (hInv EW (PW'.lift (PW.ι ⋙ Lp₀) hLp₀) (QW'.lift (QW.ι ⋙ Ep) hEp) EW' ⟨σp.symm⟩).iso.hom.app
        ((QW.lift (QT.ι ⋙ Eq) hEq).obj P) ≫
      EW'.inverse.map (ObjectProperty.homMk (θ₁.app P.obj) :
        (QW'.lift (QW.ι ⋙ Ep) hEp).obj ((QW.lift (QT.ι ⋙ Eq) hEq).obj P) ⟶
          (QW'.lift (QT'.ι ⋙ Er) hEr).obj ((QT'.lift (QT.ι ⋙ Es) hEs).obj P)) =
    (ObjectProperty.homMk (ΘS (ET.inverse.obj P).obj) :
        (PW'.lift (PW.ι ⋙ Lp₀) hLp₀).obj ((PW.lift (PT.ι ⋙ Lq₀) hLq₀).obj (ET.inverse.obj P)) ⟶
          (PW'.lift (PT'.ι ⋙ Lr₀) hLr₀).obj ((PT'.lift (PT.ι ⋙ Ls₀) hLs₀).obj
            (ET.inverse.obj P))) ≫
      (PW'.lift (PT'.ι ⋙ Lr₀) hLr₀).map ((hInv ET (PT'.lift (PT.ι ⋙ Ls₀) hLs₀)
        (QT'.lift (QT.ι ⋙ Es) hEs) ET' ⟨σs.symm⟩).iso.hom.app P) ≫
      (hInv ET' (PW'.lift (PT'.ι ⋙ Lr₀) hLr₀) (QW'.lift (QT'.ι ⋙ Er) hEr) EW'
        ⟨σr.symm⟩).iso.hom.app ((QT'.lift (QT.ι ⋙ Es) hEs).obj P) := by
  have hD : ∀ X, εW'.map (cW'.map (ΘS X)) ≫ sqr.inv.app (Ls₀.obj X) ≫ Er.map (sqs.inv.app X) =
      sqp.inv.app (Lq₀.obj X) ≫ Ep.map (sqq.inv.app X) ≫ θ₁.app (εT.obj (cT.obj X)) := by
    intro X
    rw [layeredSquare_inv_app Mr ρr sqr hsqr, layeredSquare_inv_app Ms ρs sqs hsqs,
      layeredSquare_inv_app Mp ρp sqp hsqp, layeredSquare_inv_app Mq ρq sqq hsqq]
    have n1 := ρp.inv.naturality (Mq.inv.app X)
    have n2 := ρr.inv.naturality (Ms.inv.app X)
    have h2 := congrArg εW'.map (hL2 X)
    simp only [Functor.comp_obj, Functor.comp_map] at n1 n2
    simp only [Functor.map_comp] at h2
    simp only [Functor.map_comp, Category.assoc]
    rw [← reassoc_of% n1, hL1, reassoc_of% h2, reassoc_of% n2]
  let ΘB : QW.lift (QT.ι ⋙ Eq) hEq ⋙ QW'.lift (QW.ι ⋙ Ep) hEp ⟶
      QT'.lift (QT.ι ⋙ Es) hEs ⋙ QW'.lift (QT'.ι ⋙ Er) hEr :=
    { app := fun P => (ObjectProperty.homMk (θ₁.app P.obj) :
        (QW'.lift (QW.ι ⋙ Ep) hEp).obj ((QW.lift (QT.ι ⋙ Eq) hEq).obj P) ⟶
          (QW'.lift (QT'.ι ⋙ Er) hEr).obj ((QT'.lift (QT.ι ⋙ Es) hEs).obj P))
      naturality := fun _ _ f => by ext; exact θ₁.naturality f.hom }
  have hcube : ∀ Y, EW'.functor.map (ObjectProperty.homMk (ΘS Y.obj) :
      (PW'.lift (PW.ι ⋙ Lp₀) hLp₀).obj ((PW.lift (PT.ι ⋙ Lq₀) hLq₀).obj Y) ⟶
        (PW'.lift (PT'.ι ⋙ Lr₀) hLr₀).obj ((PT'.lift (PT.ι ⋙ Ls₀) hLs₀).obj Y)) ≫
      (⟨σr.symm⟩ : CatCommSq ET'.functor _ _ EW'.functor).iso.inv.app
        ((PT'.lift (PT.ι ⋙ Ls₀) hLs₀).obj Y) ≫
      (QW'.lift (QT'.ι ⋙ Er) hEr).map
        ((⟨σs.symm⟩ : CatCommSq ET.functor _ _ ET'.functor).iso.inv.app Y) =
      (⟨σp.symm⟩ : CatCommSq EW.functor _ _ EW'.functor).iso.inv.app
        ((PW.lift (PT.ι ⋙ Lq₀) hLq₀).obj Y) ≫
      (QW'.lift (QW.ι ⋙ Ep) hEp).map
        ((⟨σq.symm⟩ : CatCommSq ET.functor _ _ EW.functor).iso.inv.app Y) ≫
      ΘB.app (ET.functor.obj Y) := by
    intro Y
    ext
    have ne := eW'.hom.naturality (ObjectProperty.homMk (ΘS Y.obj) :
      (PW'.lift (PW.ι ⋙ Lp₀) hLp₀).obj ((PW.lift (PT.ι ⋙ Lq₀) hLq₀).obj Y) ⟶
        (PW'.lift (PT'.ι ⋙ Lr₀) hLr₀).obj ((PT'.lift (PT.ι ⋙ Ls₀) hLs₀).obj Y))
    have nθ := θ₁.naturality (eT.inv.app Y)
    simp only [Functor.comp_obj, Functor.comp_map, ObjectProperty.ι_map,
      ObjectProperty.homMk_hom, ObjectProperty.ι_obj] at ne nθ
    simp only [Iso.symm_inv, ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.lift_map,
      Functor.comp_map, ObjectProperty.ι_map, hσq, hσp, hσs, hσr, Functor.map_comp,
      Category.assoc, ΘB, ObjectProperty.homMk_hom]
    rw [reassoc_of% ne]
    simp only [← Er.map_comp_assoc, ← Ep.map_comp_assoc, Iso.inv_hom_id_app_assoc]
    simp only [Functor.map_comp, Category.assoc]
    rw [nθ]
    have h3 := congrArg (fun t => eW'.hom.app ((PW'.lift (PW.ι ⋙ Lp₀) hLp₀).obj
      ((PW.lift (PT.ι ⋙ Lq₀) hLq₀).obj Y)) ≫ t ≫ Er.map (Es.map (eT.inv.app Y))) (hD Y.obj)
    simp only [Category.assoc] at h3
    exact h3
  have h := hInv_cube ET EW ET' EW' _ _ _ _ _ _ _ _ ⟨σq.symm⟩ ⟨σp.symm⟩ ⟨σs.symm⟩ ⟨σr.symm⟩
    (fun Y => (ObjectProperty.homMk (ΘS Y.obj) :
      (PW'.lift (PW.ι ⋙ Lp₀) hLp₀).obj ((PW.lift (PT.ι ⋙ Lq₀) hLq₀).obj Y) ⟶
        (PW'.lift (PT'.ι ⋙ Lr₀) hLr₀).obj ((PT'.lift (PT.ι ⋙ Ls₀) hLs₀).obj Y))) ΘB hcube P
  have comp_eq_of_inv : ∀ {A B A' B' : PW'.FullSubcategory} (a : A ⟶ B) (b : B ⟶ A)
      (y : B ⟶ B') (x : A ⟶ A') (c : A' ⟶ B') (d : B' ⟶ A'), a ≫ b = 𝟙 A → d ≫ c = 𝟙 B' →
        b ≫ x = y ≫ d → a ≫ y = x ≫ c := fun a b y x c d hab hdc h => by
    calc a ≫ y = a ≫ y ≫ d ≫ c := by rw [hdc, Category.comp_id]
      _ = x ≫ c := by rw [← reassoc_of% h, reassoc_of% hab]
  have key := comp_eq_of_inv
    ((PW'.lift (PW.ι ⋙ Lp₀) hLp₀).map ((hInv ET (PW.lift (PT.ι ⋙ Lq₀) hLq₀) (QW.lift
      (QT.ι ⋙ Eq) hEq) EW ⟨σq.symm⟩).iso.hom.app P) ≫ (hInv EW (PW'.lift (PW.ι ⋙ Lp₀) hLp₀)
        (QW'.lift (QW.ι ⋙ Ep) hEp) EW' ⟨σp.symm⟩).iso.hom.app ((QW.lift (QT.ι ⋙ Eq) hEq).obj P))
    ((hInv EW (PW'.lift (PW.ι ⋙ Lp₀) hLp₀) (QW'.lift (QW.ι ⋙ Ep) hEp) EW' ⟨σp.symm⟩).iso.inv.app
      ((QW.lift (QT.ι ⋙ Eq) hEq).obj P) ≫ (PW'.lift (PW.ι ⋙ Lp₀) hLp₀).map ((hInv ET (PW.lift
        (PT.ι ⋙ Lq₀) hLq₀) (QW.lift (QT.ι ⋙ Eq) hEq) EW ⟨σq.symm⟩).iso.inv.app P))
    (EW'.inverse.map (ΘB.app P))
    (ObjectProperty.homMk (ΘS (ET.inverse.obj P).obj) :
      (PW'.lift (PW.ι ⋙ Lp₀) hLp₀).obj ((PW.lift (PT.ι ⋙ Lq₀) hLq₀).obj (ET.inverse.obj P)) ⟶
        (PW'.lift (PT'.ι ⋙ Lr₀) hLr₀).obj ((PT'.lift (PT.ι ⋙ Ls₀) hLs₀).obj (ET.inverse.obj P)))
    ((PW'.lift (PT'.ι ⋙ Lr₀) hLr₀).map ((hInv ET (PT'.lift (PT.ι ⋙ Ls₀) hLs₀) (QT'.lift
      (QT.ι ⋙ Es) hEs) ET' ⟨σs.symm⟩).iso.hom.app P) ≫ (hInv ET' (PW'.lift (PT'.ι ⋙ Lr₀) hLr₀)
        (QW'.lift (QT'.ι ⋙ Er) hEr) EW' ⟨σr.symm⟩).iso.hom.app ((QT'.lift (QT.ι ⋙ Es) hEs).obj P))
    ((hInv ET' (PW'.lift (PT'.ι ⋙ Lr₀) hLr₀) (QW'.lift
      (QT'.ι ⋙ Er) hEr) EW' ⟨σr.symm⟩).iso.inv.app ((QT'.lift (QT.ι ⋙ Es) hEs).obj P) ≫ (PW'.lift
        (PT'.ι ⋙ Lr₀) hLr₀).map ((hInv ET (PT'.lift (PT.ι ⋙ Ls₀) hLs₀) (QT'.lift
          (QT.ι ⋙ Es) hEs) ET' ⟨σs.symm⟩).iso.inv.app P))
    (by rw [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      Functor.map_id])
    (by
      have e : (PW'.lift (PT'.ι ⋙ Lr₀) hLr₀).map ((hInv ET (PT'.lift (PT.ι ⋙ Ls₀) hLs₀) (QT'.lift
        (QT.ι ⋙ Es) hEs) ET' ⟨σs.symm⟩).iso.inv.app P) ≫ (PW'.lift (PT'.ι ⋙ Lr₀) hLr₀).map
          ((hInv ET (PT'.lift (PT.ι ⋙ Ls₀) hLs₀) (QT'.lift
            (QT.ι ⋙ Es) hEs) ET' ⟨σs.symm⟩).iso.hom.app P) = 𝟙 _ := by
        rw [← Functor.map_comp, Iso.inv_hom_id_app]; exact Functor.map_id _ _
      rw [Category.assoc, reassoc_of% e, Iso.inv_hom_id_app]; rfl)
    (by simpa only [Category.assoc] using h)
  simpa only [Category.assoc] using key

end LayeredCube

end CategoryTheory.CatCommSq
