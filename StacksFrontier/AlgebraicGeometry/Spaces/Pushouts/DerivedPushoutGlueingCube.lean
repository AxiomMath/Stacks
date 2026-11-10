module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.DerivedPushoutGlueingRestriction
public import StacksFrontier.CategoryTheory.Localization.MateLocalization
public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# The cube condition for the glueing map of Stacks 0DL7, over abstract categories

The restriction lemma `MilnorPatching.map_glueingMap_comp_baseChange` carries the glueing map of
Stacks 0DL7 along restriction functors `Φ`, given base change maps `β` for the four direct images
which are compatible with the units and with the identifications `c`, `c_W` of the two composite
direct images (the *cube condition* `hc`). This file reduces that hypothesis to a statement about
the inverse images alone and proves the latter for compositors that are associative.

Write the square `i, f, f', j` with its inverse images `Lj, Lf, Lf', Li`, its base change
`iW, fW, f'W, jW` along `h : W ⟶ Y'`, and the restrictions `Φ = Lh^*` and `Φ₁, Φ₂, Φ₀` to the
three other corners. The six faces of the cube carry 2-cells between composites of inverse images:
`σ : Lj ⋙ Lf ≅ Lf' ⋙ Li` and `σ_W` on the bottom and top, and `θj, θf, θf', θi` on the four
vertical faces. The base change maps are the mates of the `θ` (Stacks 07A7), and `c`, `c_W` are
the conjugates of `σ`, `σ_W`.

## Main results

* `MilnorPatching.mate_cube`: the cube condition `hc` for the mates of the `θ` follows from the
  equality of the two pastings of the six faces of the cube of inverse images.
* `MilnorPatching.map_glueingMap_comp_mate`: the restriction lemma with the base change maps the
  mates of the `θ`; its only hypothesis is the pasting equality.
* `Stacks.CategoryTheory.BaseChange.compositorCube_paste`: for 2-cells built from compositors
  subject to the cocycle identity, the two pastings agree. This is the argument for derived
  pullbacks along morphisms of algebraic spaces, Stacks 0D6D, with every functor and compositor a
  variable.
* `Stacks.CategoryTheory.BaseChange.conjSquare`: a 2-cell between composites of functors read at
  other models of the four categories, through equivalences; `conjSquare_cube` says that the
  pasting equality survives, and `conjSquare_mateEquiv` that taking mates commutes with it for
  adjunctions read at the other models (`Stacks.CategoryTheory.BaseChange.conjAdj`).
* `MilnorPatching.map_glueingMap_comp_conjSquare` and
  `MilnorPatching.map_glueingMap_comp_conjBaseChange`: the restriction lemma with the whole cube
  read at other models, the 2-cells of the bottom and top in the shape of
  `AlgebraicGeometry.Space.pushoutDerivedPullbackSquareIsoOfModels`; its only hypothesis is the
  pasting equality at the original models.
* `MilnorPatching.isIso_map_homEquiv_symm_of_restrict` and
  `MilnorPatching.isIso_map_homEquiv_symm_of_conjBaseChange`: **the isomorphism step of Stacks 0DL7
  is local** — for a triangulated restriction functor `Φ` and invertible base change maps, if
  the maps adjoint to the components of the first map of every distinguished triangle on the
  restricted glueing map are isomorphisms, then the maps adjoint to the components of the first
  map of a distinguished triangle on the glueing map become isomorphisms after restriction.
  `MilnorPatching.isIso_map_homEquiv_symm_of_conjBaseChange_iso` is the same for an isomorphism
  `α`, with the hypothesis on the restricted glueing maps asked for every isomorphism `αW`.

## Implementation notes

The category instances are implicit arguments, unified from the functors, not instance
arguments: at the derived categories of the small étale sites of algebraic spaces a synthesized
instance and the one in the type of a functor elaborated elsewhere are definitionally equal only
after unfolding the derived categories, which the kernel does not do within its budget.

## References

* [Stacks Project, Tag 0DL7](https://stacks.math.columbia.edu/tag/0DL7)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

universe v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25
  v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39


open CategoryTheory CategoryTheory.Limits

namespace Stacks.CategoryTheory.BaseChange

section Compositors

variable {𝒴' 𝒴 𝒳 𝒳' 𝒲 𝒴W 𝒳W 𝒳'W : Type*} {_ : Category.{v1} 𝒴'} {_ : Category.{v2} 𝒴}
  {_ : Category.{v3} 𝒳} {_ : Category.{v4} 𝒳'} {_ : Category.{v5} 𝒲} {_ : Category.{v6} 𝒴W}
  {_ : Category.{v7} 𝒳W} {_ : Category.{v8} 𝒳'W}
  {Li : 𝒳' ⥤ 𝒳} {Lf : 𝒴 ⥤ 𝒳} {Lf' : 𝒴' ⥤ 𝒳'} {Lj : 𝒴' ⥤ 𝒴} {LiW : 𝒳'W ⥤ 𝒳W}
  {LfW : 𝒴W ⥤ 𝒳W} {Lf'W : 𝒲 ⥤ 𝒳'W} {LjW : 𝒲 ⥤ 𝒴W} {Lh : 𝒴' ⥤ 𝒲} {LhY : 𝒴 ⥤ 𝒴W}
  {LhX : 𝒳 ⥤ 𝒳W} {LhX' : 𝒳' ⥤ 𝒳'W} {Lk : 𝒴' ⥤ 𝒳} {Le : 𝒲 ⥤ 𝒳W} {Ldj : 𝒴' ⥤ 𝒴W}
  {Ln : 𝒴 ⥤ 𝒳W} {Ldf' : 𝒴' ⥤ 𝒳'W} {Lm : 𝒳' ⥤ 𝒳W} {LK : 𝒴' ⥤ 𝒳W}

/-- The images of `α.inv.app X` and `α.hom.app X` under a functor cancel. -/
private theorem map_inv_app_map_hom_app_assoc {C D E : Type*} {_ : Category.{v1} C}
    {_ : Category.{v2} D} {_ : Category.{v3} E} (G : D ⥤ E) {F F' : C ⥤ D} (α : F ≅ F') (X : C)
    {Z : E} (g : G.obj (F'.obj X) ⟶ Z) :
    G.map (α.inv.app X) ≫ G.map (α.hom.app X) ≫ g = g := by
  rw [← Functor.map_comp_assoc]
  simp

/-- **The pasting of a cube of compositor 2-cells.** Consider a commutative cube with bottom face
`i ≫ f' = f ≫ j`, top face `iW ≫ f'W = fW ≫ jW` and vertical edges `h, hY, hX, hX'`, and inverse
image functors `L` along its edges, along the diagonals `k, e, dj, n, df', m` of its six faces and
along its long diagonal `K`. Let every face carry the 2-cell `F₁ ≫ F₂⁻¹` through its diagonal,
built from compositors `F : L q ⋙ L p ≅ L (p ≫ q)`, and let `G₁, …, G₆` be compositors onto `L K`
satisfying the six instances `a₁, …, a₆` of the cocycle identity that relate them. Then the two
pastings of the six faces, from `Lh ⋙ LjW ⋙ LfW` to `Lf' ⋙ Li ⋙ LhX`, agree.

The categories and functors are independent variables rather than a family indexed by a category,
so that an instance at derived pullbacks unifies with the exact universe levels of its functors. -/
theorem compositorCube_paste (Fσ₁ : Lj ⋙ Lf ≅ Lk) (Fσ₂ : Lf' ⋙ Li ≅ Lk)
    (FσW₁ : LjW ⋙ LfW ≅ Le) (FσW₂ : Lf'W ⋙ LiW ≅ Le) (Fj₁ : Lh ⋙ LjW ≅ Ldj)
    (Fj₂ : Lj ⋙ LhY ≅ Ldj) (Ff₁ : LhY ⋙ LfW ≅ Ln) (Ff₂ : Lf ⋙ LhX ≅ Ln)
    (Ff'₁ : Lh ⋙ Lf'W ≅ Ldf') (Ff'₂ : Lf' ⋙ LhX' ≅ Ldf') (Fi₁ : LhX' ⋙ LiW ≅ Lm)
    (Fi₂ : Li ⋙ LhX ≅ Lm) (G₁ : Lk ⋙ LhX ≅ LK) (G₂ : Lf' ⋙ Lm ≅ LK) (G₃ : Lj ⋙ Ln ≅ LK)
    (G₄ : Ldj ⋙ LfW ≅ LK) (G₅ : Lh ⋙ Le ≅ LK) (G₆ : Ldf' ⋙ LiW ≅ LK) (N : 𝒴')
    (a₁ : Fi₂.hom.app (Lf'.obj N) ≫ G₂.hom.app N = LhX.map (Fσ₂.hom.app N) ≫ G₁.hom.app N)
    (a₂ : Ff₂.hom.app (Lj.obj N) ≫ G₃.hom.app N = LhX.map (Fσ₁.hom.app N) ≫ G₁.hom.app N)
    (a₃ : Ff₁.hom.app (Lj.obj N) ≫ G₃.hom.app N = LfW.map (Fj₂.hom.app N) ≫ G₄.hom.app N)
    (a₄ : FσW₁.hom.app (Lh.obj N) ≫ G₅.hom.app N = LfW.map (Fj₁.hom.app N) ≫ G₄.hom.app N)
    (a₅ : Fi₁.hom.app (Lf'.obj N) ≫ G₂.hom.app N = LiW.map (Ff'₂.hom.app N) ≫ G₆.hom.app N)
    (a₆ : FσW₂.hom.app (Lh.obj N) ≫ G₅.hom.app N = LiW.map (Ff'₁.hom.app N) ≫ G₆.hom.app N) :
    LfW.map ((Fj₁.hom ≫ Fj₂.inv).app N) ≫ (Ff₁.hom ≫ Ff₂.inv).app (Lj.obj N) ≫
        LhX.map ((Fσ₁.hom ≫ Fσ₂.inv).app N) =
      (FσW₁.hom ≫ FσW₂.inv).app (Lh.obj N) ≫ LiW.map ((Ff'₁.hom ≫ Ff'₂.inv).app N) ≫
        (Fi₁.hom ≫ Fi₂.inv).app (Lf'.obj N) := by
  have hL : (LfW.map ((Fj₁.hom ≫ Fj₂.inv).app N) ≫ (Ff₁.hom ≫ Ff₂.inv).app (Lj.obj N) ≫
        LhX.map ((Fσ₁.hom ≫ Fσ₂.inv).app N)) ≫ Fi₂.hom.app (Lf'.obj N) ≫ G₂.hom.app N =
      FσW₁.hom.app (Lh.obj N) ≫ G₅.hom.app N := by
    simp only [NatTrans.comp_app, Functor.comp_obj, Category.assoc]
    simp only [Functor.map_comp, Category.assoc]
    rw [a₁, map_inv_app_map_hom_app_assoc, ← a₂, Iso.inv_hom_id_app_assoc, a₃,
      map_inv_app_map_hom_app_assoc, ← a₄]
  have hR : ((FσW₁.hom ≫ FσW₂.inv).app (Lh.obj N) ≫ LiW.map ((Ff'₁.hom ≫ Ff'₂.inv).app N) ≫
        (Fi₁.hom ≫ Fi₂.inv).app (Lf'.obj N)) ≫ Fi₂.hom.app (Lf'.obj N) ≫ G₂.hom.app N =
      FσW₁.hom.app (Lh.obj N) ≫ G₅.hom.app N := by
    simp only [NatTrans.comp_app, Functor.comp_obj, Category.assoc]
    simp only [Functor.map_comp, Category.assoc]
    rw [Iso.inv_hom_id_app_assoc, a₅, map_inv_app_map_hom_app_assoc, ← a₆,
      Iso.inv_hom_id_app_assoc]
  rw [← cancel_mono (Fi₂.hom.app (Lf'.obj N) ≫ G₂.hom.app N), hL, hR]

end Compositors

section Conjugation

variable {C₁ C₂ C₃ C₄ C₁' C₂' C₃' C₄' : Type*} {_ : Category.{v9} C₁} {_ : Category.{v10} C₂}
  {_ : Category.{v11} C₃} {_ : Category.{v12} C₄} {_ : Category.{v13} C₁'} {_ : Category.{v14} C₂'}
  {_ : Category.{v15} C₃'} {_ : Category.{v16} C₄'}
  (e₁ : C₁ ≌ C₁') (e₂ : C₂ ≌ C₂') (e₃ : C₃ ≌ C₃') (e₄ : C₄ ≌ C₄')

/-- **A 2-cell read at other models of its four categories.** For equivalences `eᵢ : Cᵢ ≌ Cᵢ'`
and a 2-cell `θ : T ⋙ R ⟶ L ⋙ B`, the 2-cell between the conjugated functors
`e.inverse ⋙ - ⋙ e.functor`, obtained by cancelling the unit of `e₂` in the middle of the source
and inserting the unit of `e₃` in the middle of the target. -/
def conjSquare {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
    (θ : TwoSquare T L R B) :
    TwoSquare (e₁.inverse ⋙ T ⋙ e₂.functor) (e₁.inverse ⋙ L ⋙ e₃.functor)
      (e₂.inverse ⋙ R ⋙ e₄.functor) (e₃.inverse ⋙ B ⋙ e₄.functor) :=
  Functor.whiskerLeft e₁.inverse (Functor.whiskerRight
    (Functor.whiskerLeft T (Functor.whiskerRight e₂.unitIso.inv R ≫ (Functor.leftUnitor R).hom) ≫
      θ ≫
      Functor.whiskerLeft L ((Functor.leftUnitor B).inv ≫ Functor.whiskerRight e₃.unitIso.hom B))
    e₄.functor)

/-- The component of `conjSquare e₁ e₂ e₃ e₄ θ` at `N` is the image under `e₄.functor` of the
component of `θ` at `e₁.inverse.obj N`, preceded by the inverse unit of `e₂` and followed by the
unit of `e₃`. -/
theorem conjSquare_app {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
    (θ : TwoSquare T L R B) (N : C₁') :
    (conjSquare e₁ e₂ e₃ e₄ θ).app N =
      e₄.functor.map (R.map (e₂.unitInv.app (T.obj (e₁.inverse.obj N))) ≫
        θ.app (e₁.inverse.obj N) ≫ B.map (e₃.unit.app (L.obj (e₁.inverse.obj N)))) := by
  simp [conjSquare]

/-- A 2-cell with invertible components, read at other models, has invertible components. -/
theorem isIso_conjSquare_app {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
    (θ : TwoSquare T L R B) (N : C₁') [hθ : IsIso (θ.app (e₁.inverse.obj N))] :
    IsIso ((conjSquare e₁ e₂ e₃ e₄ θ).app N) := by
  rw [conjSquare_app]
  infer_instance

/-- An invertible 2-cell read at other models, as an isomorphism. -/
def conjSquareIso {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
    (θ : T ⋙ R ≅ L ⋙ B) :
    (e₁.inverse ⋙ T ⋙ e₂.functor) ⋙ (e₂.inverse ⋙ R ⋙ e₄.functor) ≅
      (e₁.inverse ⋙ L ⋙ e₃.functor) ⋙ (e₃.inverse ⋙ B ⋙ e₄.functor) :=
  haveI : ∀ N, IsIso ((conjSquare e₁ e₂ e₃ e₄ θ.hom).app N) := fun N ↦
    isIso_conjSquare_app _ _ _ _ _ N
  haveI : IsIso (conjSquare e₁ e₂ e₃ e₄ θ.hom) := NatIso.isIso_of_isIso_app _
  asIso (conjSquare e₁ e₂ e₃ e₄ θ.hom)

/-- The forward map of `conjSquareIso e₁ e₂ e₃ e₄ θ` is `conjSquare e₁ e₂ e₃ e₄ θ.hom`. -/
@[simp]
theorem conjSquareIso_hom {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
    (θ : T ⋙ R ≅ L ⋙ B) : (conjSquareIso e₁ e₂ e₃ e₄ θ).hom = conjSquare e₁ e₂ e₃ e₄ θ.hom :=
  rfl

/-- The 2-cell of a composite of three isomorphisms, read at other models, in the shape in which
`AlgebraicGeometry.Space.pushoutDerivedPullbackSquareIsoOfModels` is built. -/
theorem isoWhiskerLeft_isoWhiskerRight_hom_app {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄}
    {B : C₃ ⥤ C₄} {P Q : C₁ ⥤ C₄} (σ₁ : T ⋙ R ≅ P) (σ₂ : P ≅ Q) (σ₃ : L ⋙ B ≅ Q) (N : C₁') :
    (Functor.isoWhiskerLeft e₁.inverse (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft T
          (Functor.isoWhiskerRight e₂.unitIso.symm R ≪≫ Functor.leftUnitor R) ≪≫
        σ₁ ≪≫ σ₂ ≪≫ σ₃.symm ≪≫
        Functor.isoWhiskerLeft L
          ((Functor.leftUnitor B).symm ≪≫ Functor.isoWhiskerRight e₃.unitIso B))
      e₄.functor)).hom.app N =
    (conjSquare e₁ e₂ e₃ e₄ (TwoSquare.mk _ _ _ _ (σ₁ ≪≫ σ₂ ≪≫ σ₃.symm).hom)).app N := by
  rw [conjSquare_app]
  simp

end Conjugation

section ConjugationCube

private theorem map_unit_app_unitInv_app_assoc {C C' D : Type*} {_ : Category.{v17} C}
    {_ : Category.{v18} C'} {_ : Category.{v19} D} (G : C ⥤ D) (e : C ≌ C') (X : C) {Z : D}
    (g : G.obj X ⟶ Z) :
    G.map (e.unit.app X) ≫ G.map (e.unitInv.app X) ≫ g = g := by
  rw [← Functor.map_comp_assoc]
  simp

private theorem map_map_unit_app_unitInv_app_assoc {C C' D E : Type*} {_ : Category.{v17} C}
    {_ : Category.{v18} C'} {_ : Category.{v19} D} {_ : Category.{v20} E} (H : C ⥤ D) (G : D ⥤ E)
    (e : C ≌ C') (X : C) {Z : E} (g : G.obj (H.obj X) ⟶ Z) :
    G.map (H.map (e.unit.app X)) ≫ G.map (H.map (e.unitInv.app X)) ≫ g = g :=
  map_unit_app_unitInv_app_assoc (H ⋙ G) e X g

variable {𝒟 𝒟₁ 𝒟₂ 𝒟₀ 𝒲 𝒲₁ 𝒲₂ 𝒲₀ 𝒟' 𝒟₁' 𝒟₂' 𝒟₀' 𝒲' 𝒲₁' 𝒲₂' 𝒲₀' : Type*}
  {_ : Category.{v21} 𝒟} {_ : Category.{v22} 𝒟₁} {_ : Category.{v23} 𝒟₂} {_ : Category.{v24} 𝒟₀}
  {_ : Category.{v5} 𝒲} {_ : Category.{v25} 𝒲₁} {_ : Category.{v26} 𝒲₂} {_ : Category.{v27} 𝒲₀}
  {_ : Category.{v28} 𝒟'} {_ : Category.{v29} 𝒟₁'} {_ : Category.{v30} 𝒟₂'} {_ : Category.{v31} 𝒟₀'}
  {_ : Category.{v32} 𝒲'} {_ : Category.{v33} 𝒲₁'} {_ : Category.{v34} 𝒲₂'} {_ : Category.{v35} 𝒲₀'}
  (e : 𝒟 ≌ 𝒟') (e₁ : 𝒟₁ ≌ 𝒟₁') (e₂ : 𝒟₂ ≌ 𝒟₂') (e₀ : 𝒟₀ ≌ 𝒟₀') (eW : 𝒲 ≌ 𝒲')
  (eW₁ : 𝒲₁ ≌ 𝒲₁') (eW₂ : 𝒲₂ ≌ 𝒲₂') (eW₀ : 𝒲₀ ≌ 𝒲₀')
  {Lj : 𝒟 ⥤ 𝒟₁} {Lf' : 𝒟 ⥤ 𝒟₂} {Lf : 𝒟₁ ⥤ 𝒟₀} {Li : 𝒟₂ ⥤ 𝒟₀}
  {LjW : 𝒲 ⥤ 𝒲₁} {Lf'W : 𝒲 ⥤ 𝒲₂} {LfW : 𝒲₁ ⥤ 𝒲₀} {LiW : 𝒲₂ ⥤ 𝒲₀}
  {Φ : 𝒟 ⥤ 𝒲} {Φ₁ : 𝒟₁ ⥤ 𝒲₁} {Φ₂ : 𝒟₂ ⥤ 𝒲₂} {Φ₀ : 𝒟₀ ⥤ 𝒲₀}

/-- **The pasting equality of a cube survives a change of models.** If the six faces of a cube of
categories paste to the same 2-cell, so do the six faces read at other models of the eight
corners (`Stacks.CategoryTheory.BaseChange.conjSquare`). -/
theorem conjSquare_cube (θj : TwoSquare Φ Lj LjW Φ₁) (θf : TwoSquare Φ₁ Lf LfW Φ₀)
    (θf' : TwoSquare Φ Lf' Lf'W Φ₂) (θi : TwoSquare Φ₂ Li LiW Φ₀) (σ : TwoSquare Lj Lf' Lf Li)
    (σW : TwoSquare LjW Lf'W LfW LiW)
    (h : ∀ N, LfW.map (θj.app N) ≫ θf.app (Lj.obj N) ≫ Φ₀.map (σ.app N) =
      σW.app (Φ.obj N) ≫ LiW.map (θf'.app N) ≫ θi.app (Lf'.obj N)) (N : 𝒟') :
    (eW₁.inverse ⋙ LfW ⋙ eW₀.functor).map ((conjSquare e eW e₁ eW₁ θj).app N) ≫
        (conjSquare e₁ eW₁ e₀ eW₀ θf).app ((e.inverse ⋙ Lj ⋙ e₁.functor).obj N) ≫
        (e₀.inverse ⋙ Φ₀ ⋙ eW₀.functor).map ((conjSquare e e₁ e₂ e₀ σ).app N) =
      (conjSquare eW eW₁ eW₂ eW₀ σW).app ((e.inverse ⋙ Φ ⋙ eW.functor).obj N) ≫
        (eW₂.inverse ⋙ LiW ⋙ eW₀.functor).map ((conjSquare e eW e₂ eW₂ θf').app N) ≫
        (conjSquare e₂ eW₂ e₀ eW₀ θi).app ((e.inverse ⋙ Lf' ⋙ e₂.functor).obj N) := by
  simp only [conjSquare_app, Functor.comp_map, Functor.comp_obj, Equivalence.inv_fun_map]
  simp only [← Functor.map_comp]
  congr 1
  simp only [Functor.map_comp, Category.assoc]
  have nf := θf.naturality (e₁.unit.app (Lj.obj (e.inverse.obj N)))
  have nσ := σW.naturality (eW.unitInv.app (Φ.obj (e.inverse.obj N)))
  have ni := θi.naturality (e₂.unit.app (Lf'.obj (e.inverse.obj N)))
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at nf nσ ni
  rw [map_unit_app_unitInv_app_assoc, reassoc_of% nf, map_unit_app_unitInv_app_assoc,
    map_map_unit_app_unitInv_app_assoc, reassoc_of% (h (e.inverse.obj N)),
    map_unit_app_unitInv_app_assoc, map_unit_app_unitInv_app_assoc, reassoc_of% ni,
    ← reassoc_of% nσ]

end ConjugationCube

section ConjugationMate

variable {C D E F C' D' E' F' : Type*} {_ : Category.{v17} C} {_ : Category.{v19} D}
  {_ : Category.{v20} E} {_ : Category.{v36} F} {_ : Category.{v18} C'} {_ : Category.{v37} D'}
  {_ : Category.{v38} E'} {_ : Category.{v39} F'}
  (eC : C ≌ C') (eD : D ≌ D') (eE : E ≌ E') (eF : F ≌ F')

/-- **An adjunction read at other models of its two categories**: `L ⊣ R` conjugated by
equivalences `eC : C ≌ C'` and `eD : D ≌ D'`. This is how
`AlgebraicGeometry.Space.smallEtaleDerivedModuleAdjunctionOfModels` is built. -/
abbrev conjAdj {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) :
    eC.inverse ⋙ L ⋙ eD.functor ⊣ eD.inverse ⋙ R ⋙ eC.functor :=
  eC.symm.toAdjunction.comp (adj.comp eD.toAdjunction)

/-- **Taking mates commutes with a change of models.** The mate, for adjunctions read at other
models (`Stacks.CategoryTheory.BaseChange.conjAdj`), of a 2-cell read at those models is the mate
read at those models. -/
theorem conjSquare_mateEquiv {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E} {G : C ⥤ E}
    {H : D ⥤ F} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ H) :
    mateEquiv (conjAdj eC eD adj₁) (conjAdj eE eF adj₂) (conjSquare eC eE eD eF α) =
      conjSquare eD eC eF eE (mateEquiv adj₁ adj₂ α) := by
  refine (eq_mateEquiv_of_counit _ _ _ _ fun Y ↦ ?_).symm
  simp only [Functor.comp_obj, Functor.id_obj, mateEquiv_apply, conjSquare_app, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp, Category.assoc,
    Functor.map_comp, Equivalence.inv_fun_map, Iso.hom_inv_id_app_assoc, Adjunction.comp_counit_app,
    Equivalence.symm_functor, Equivalence.symm_inverse, Equivalence.toAdjunction_counit,
    Equivalence.symm_counit, cancelIso, Equivalence.unit_inverse_comp]
  have n₁ := congrArg eF.functor.map
    (adj₂.counit.naturality (eF.unit.app (H.obj (eD.inverse.obj Y))))
  have n₂ := α.naturality (eC.unitInv.app (R₁.obj (eD.inverse.obj Y)))
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj,
    Functor.map_comp] at n₁ n₂
  rw [reassoc_of% n₁, Equivalence.functor_unit_comp, Category.comp_id]
  simp only [← Functor.map_comp]
  congr 1
  simp only [Functor.map_comp]
  rw [Adjunction.counit_naturality, Adjunction.counit_naturality_assoc,
    Adjunction.left_triangle_components_assoc, reassoc_of% n₂]

end ConjugationMate

section ConjugationTwoSquare

variable {A B A' B' C₁' C₂' C₃' C₄' : Type*} {_ : Category.{v9} A} {_ : Category.{v10} B}
  {_ : Category.{v11} A'} {_ : Category.{v12} B'} {_ : Category.{v13} C₁'} {_ : Category.{v14} C₂'}
  {_ : Category.{v15} C₃'} {_ : Category.{v16} C₄'}
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'} {Lg : A ⥤ A'} {Lg' : B ⥤ B'}
  {Lc : A ⥤ B'} (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  (e₁ : B ≌ C₁') (e₂ : A ≌ C₂') (e₃ : B' ≌ C₃') (e₄ : A' ≌ C₄')

/-- A base change map read at other models is invertible as soon as the base change map is. -/
theorem isIso_conjSquare_twoSquare_app (N : C₁')
    (h : @IsIso _ _ _ _ (map adjf adjf' eg ef (e₁.inverse.obj N))) :
    @IsIso _ _ _ _ ((conjSquare e₁ e₂ e₃ e₄ (twoSquare adjf adjf' eg ef)).app N) :=
  isIso_conjSquare_app e₁ e₂ e₃ e₄ _ N (hθ := h)

end ConjugationTwoSquare

end Stacks.CategoryTheory.BaseChange

namespace MilnorPatching

variable {𝒟 𝒟₁ 𝒟₂ 𝒟₀ 𝒲 𝒲₁ 𝒲₂ 𝒲₀ : Type*} {_ : Category.{v21} 𝒟} {_ : Category.{v22} 𝒟₁}
  {_ : Category.{v23} 𝒟₂} {_ : Category.{v24} 𝒟₀} {_ : Category.{v5} 𝒲} {_ : Category.{v25} 𝒲₁}
  {_ : Category.{v26} 𝒲₂} {_ : Category.{v27} 𝒲₀}
  {Lj : 𝒟 ⥤ 𝒟₁} {Rj : 𝒟₁ ⥤ 𝒟} {Lf' : 𝒟 ⥤ 𝒟₂} {Rf' : 𝒟₂ ⥤ 𝒟} {Lf : 𝒟₁ ⥤ 𝒟₀}
  {Rf : 𝒟₀ ⥤ 𝒟₁} {Li : 𝒟₂ ⥤ 𝒟₀} {Ri : 𝒟₀ ⥤ 𝒟₂}
  {LjW : 𝒲 ⥤ 𝒲₁} {RjW : 𝒲₁ ⥤ 𝒲} {Lf'W : 𝒲 ⥤ 𝒲₂} {Rf'W : 𝒲₂ ⥤ 𝒲} {LfW : 𝒲₁ ⥤ 𝒲₀}
  {RfW : 𝒲₀ ⥤ 𝒲₁} {LiW : 𝒲₂ ⥤ 𝒲₀} {RiW : 𝒲₀ ⥤ 𝒲₂}
  {Φ : 𝒟 ⥤ 𝒲} {Φ₁ : 𝒟₁ ⥤ 𝒲₁} {Φ₂ : 𝒟₂ ⥤ 𝒲₂} {Φ₀ : 𝒟₀ ⥤ 𝒲₀}
  (adjJ : Lj ⊣ Rj) (adjF' : Lf' ⊣ Rf') (adjF : Lf ⊣ Rf) (adjI : Li ⊣ Ri)
  (adjJW : LjW ⊣ RjW) (adjF'W : Lf'W ⊣ Rf'W) (adjFW : LfW ⊣ RfW) (adjIW : LiW ⊣ RiW)

/-- The conjugate `c⁻¹ : Ri ⋙ Rf' ⟶ Rf ⋙ Rj` of a 2-cell `σ : Lj ⋙ Lf ≅ Lf' ⋙ Li`, read under the
counits of the two composite adjunctions. -/
theorem map_glueingConjugateIso_inv_app_comp_counit (σ : Lj ⋙ Lf ≅ Lf' ⋙ Li) (N : 𝒟₀) :
    Lf.map (Lj.map ((glueingConjugateIso adjF adjI adjJ adjF' σ).inv.app N)) ≫
        Lf.map (adjJ.counit.app (Rf.obj N)) ≫ adjF.counit.app N =
      σ.hom.app (Rf'.obj (Ri.obj N)) ≫ Li.map (adjF'.counit.app (Ri.obj N)) ≫
        adjI.counit.app N := by
  have h := conjugateEquiv_counit (adjF'.comp adjI) (adjJ.comp adjF) σ.hom N
  simp only [Functor.comp_obj, Functor.comp_map, Adjunction.comp_counit_app] at h
  exact h

/-- **The cube condition for mates.** If the two pastings of the six faces of the cube of inverse
images agree (`h`), then the mates of the four vertical faces satisfy the cube condition of
`MilnorPatching.map_glueingMap_comp_baseChange` with respect to the conjugates `c`, `c_W` of `σ`,
`σ_W`. -/
theorem mate_cube (σ : Lj ⋙ Lf ≅ Lf' ⋙ Li) (σW : LjW ⋙ LfW ≅ Lf'W ⋙ LiW)
    (θj : TwoSquare Φ Lj LjW Φ₁) (θf : TwoSquare Φ₁ Lf LfW Φ₀) (θf' : TwoSquare Φ Lf' Lf'W Φ₂)
    (θi : TwoSquare Φ₂ Li LiW Φ₀)
    (h : ∀ N, LfW.map (θj.app N) ≫ θf.app (Lj.obj N) ≫ Φ₀.map (σ.hom.app N) =
      σW.hom.app (Φ.obj N) ≫ LiW.map (θf'.app N) ≫ θi.app (Lf'.obj N)) (N : 𝒟₀) :
    Φ.map ((glueingConjugateIso adjF adjI adjJ adjF' σ).inv.app N) ≫
        (mateEquiv adjJ adjJW θj).app (Rf.obj N) ≫ RjW.map ((mateEquiv adjF adjFW θf).app N) =
      (mateEquiv adjF' adjF'W θf').app (Ri.obj N) ≫ Rf'W.map ((mateEquiv adjI adjIW θi).app N) ≫
        (glueingConjugateIso adjFW adjIW adjJW adjF'W σW).inv.app (Φ₀.obj N) := by
  apply ((adjJW.comp adjFW).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Adjunction.comp_counit_app, Functor.comp_map,
    Functor.comp_obj, Functor.map_comp, Category.assoc]
  -- the left-hand side
  have l₁ := adjJW.counit.naturality ((mateEquiv adjF adjFW θf).app N)
  have l₂ := mateEquiv_counit adjJ adjJW θj (Rf.obj N)
  have l₃ := mateEquiv_counit adjF adjFW θf N
  have l₄ := θf.naturality (adjJ.counit.app (Rf.obj N))
  have l₅ := θj.naturality ((glueingConjugateIso adjF adjI adjJ adjF' σ).inv.app N)
  have l₆ := θf.naturality (Lj.map ((glueingConjugateIso adjF adjI adjJ adjF' σ).inv.app N))
  have l₇ := map_glueingConjugateIso_inv_app_comp_counit adjJ adjF' adjF adjI σ N
  -- the right-hand side
  have r₁ := adjF'W.counit.naturality ((mateEquiv adjI adjIW θi).app N)
  have r₂ := mateEquiv_counit adjF' adjF'W θf' (Ri.obj N)
  have r₃ := mateEquiv_counit adjI adjIW θi N
  have r₄ := θi.naturality (adjF'.counit.app (Ri.obj N))
  have r₅ := map_glueingConjugateIso_inv_app_comp_counit adjJW adjF'W adjFW adjIW σW (Φ₀.obj N)
  have r₆ := σW.hom.naturality
    ((mateEquiv adjF' adjF'W θf').app (Ri.obj N) ≫ Rf'W.map ((mateEquiv adjI adjIW θi).app N))
  simp only [Functor.id_obj, Functor.comp_obj, Functor.comp_map,
    Functor.id_map] at l₁ l₂ l₃ l₄ l₅ l₆ l₇ r₁ r₂ r₃ r₄ r₅ r₆
  have L₁ := congrArg LfW.map l₁
  have L₂ := congrArg LfW.map l₂
  have L₅ := congrArg LfW.map l₅
  have L₇ := congrArg Φ₀.map l₇
  have R₁ := congrArg LiW.map r₁
  have R₂ := congrArg LiW.map r₂
  simp only [Functor.map_comp] at L₁ L₂ L₅ L₇ R₁ R₂ r₆
  rw [reassoc_of% L₁, reassoc_of% L₂, l₃, reassoc_of% l₄, reassoc_of% L₅, reassoc_of% l₆, L₇,
    reassoc_of% h, r₅, reassoc_of% r₆, reassoc_of% R₁, reassoc_of% R₂, r₃, reassoc_of% r₄]

/-- **The glueing map of Stacks 0DL7 commutes with restriction, for base change maps that are
mates.** `MilnorPatching.map_glueingMap_comp_baseChange` with the base change maps the mates of
the 2-cells `θj, θf, θf', θi` of the four vertical faces of the cube and `c`, `c_W` the conjugates
of the 2-cells `σ`, `σ_W` of its bottom and top: the compatibility with the units holds for mates,
and the cube condition reduces to the equality `h` of the two pastings of the six faces. -/
theorem map_glueingMap_comp_mate {_ : Preadditive 𝒟} [HasBinaryBiproducts 𝒟] {_ : Preadditive 𝒲}
    [HasBinaryBiproducts 𝒲] [Φ.Additive] (σ : Lj ⋙ Lf ≅ Lf' ⋙ Li) (σW : LjW ⋙ LfW ≅ Lf'W ⋙ LiW)
    (θj : TwoSquare Φ Lj LjW Φ₁) (θf : TwoSquare Φ₁ Lf LfW Φ₀) (θf' : TwoSquare Φ Lf' Lf'W Φ₂)
    (θi : Φ₂ ⋙ LiW ≅ Li ⋙ Φ₀)
    (h : ∀ N, LfW.map (θj.app N) ≫ θf.app (Lj.obj N) ≫ Φ₀.map (σ.hom.app N) =
      σW.hom.app (Φ.obj N) ≫ LiW.map (θf'.app N) ≫ θi.hom.app (Lf'.obj N))
    (M : 𝒟₁) (K' : 𝒟₂) (α : Lf.obj M ⟶ Li.obj K') :
    (Φ.map biprod.inl ≫ Φ.map (glueingMap adjF adjI (glueingConjugateIso adjF adjI adjJ adjF' σ)
        M K' α) ≫ (mateEquiv adjJ adjJW θj).app (Rf.obj (Li.obj K')) ≫
        RjW.map ((mateEquiv adjF adjFW θf).app (Li.obj K')) ≫ RjW.map (RfW.map (θi.inv.app K')) =
      (mateEquiv adjJ adjJW θj).app M ≫ biprod.inl ≫
        glueingMap adjFW adjIW (glueingConjugateIso adjFW adjIW adjJW adjF'W σW) (Φ₁.obj M)
          (Φ₂.obj K') (θf.app M ≫ Φ₀.map α ≫ θi.inv.app K')) ∧
    (Φ.map biprod.inr ≫ Φ.map (glueingMap adjF adjI (glueingConjugateIso adjF adjI adjJ adjF' σ)
        M K' α) ≫ (mateEquiv adjJ adjJW θj).app (Rf.obj (Li.obj K')) ≫
        RjW.map ((mateEquiv adjF adjFW θf).app (Li.obj K')) ≫ RjW.map (RfW.map (θi.inv.app K')) =
      (mateEquiv adjF' adjF'W θf').app K' ≫ biprod.inr ≫
        glueingMap adjFW adjIW (glueingConjugateIso adjFW adjIW adjJW adjF'W σW) (Φ₁.obj M)
          (Φ₂.obj K') (θf.app M ≫ Φ₀.map α ≫ θi.inv.app K')) :=
  map_glueingMap_comp_baseChange adjF adjI _ adjFW adjIW _ (mateEquiv adjJ adjJW θj)
    (mateEquiv adjF' adjF'W θf') (mateEquiv adjF adjFW θf)
    (mateEquiv adjI adjIW θi.hom) θf θi.symm
    (fun M ↦ unit_mateEquiv adjF adjFW θf M) (fun K ↦ unit_mateEquiv adjI adjIW θi.hom K)
    (mate_cube adjJ adjF' adjF adjI adjJW adjF'W adjFW adjIW σ σW θj θf θf' θi.hom h) M K' α

end MilnorPatching


namespace MilnorPatching

section Models

open Stacks.CategoryTheory.BaseChange

variable {𝒟 𝒟₁ 𝒟₂ 𝒟₀ 𝒲 𝒲₁ 𝒲₂ 𝒲₀ 𝒟' 𝒟₁' 𝒟₂' 𝒟₀' 𝒲' 𝒲₁' 𝒲₂' 𝒲₀' : Type*}
  {_ : Category.{v21} 𝒟} {_ : Category.{v22} 𝒟₁} {_ : Category.{v23} 𝒟₂} {_ : Category.{v24} 𝒟₀}
  {_ : Category.{v5} 𝒲} {_ : Category.{v25} 𝒲₁} {_ : Category.{v26} 𝒲₂} {_ : Category.{v27} 𝒲₀}
  {_ : Category.{v28} 𝒟'} {_ : Category.{v29} 𝒟₁'} {_ : Category.{v30} 𝒟₂'} {_ : Category.{v31} 𝒟₀'}
  {_ : Category.{v32} 𝒲'} {_ : Category.{v33} 𝒲₁'} {_ : Category.{v34} 𝒲₂'} {_ : Category.{v35} 𝒲₀'}
  (e : 𝒟 ≌ 𝒟') (e₁ : 𝒟₁ ≌ 𝒟₁') (e₂ : 𝒟₂ ≌ 𝒟₂') (e₀ : 𝒟₀ ≌ 𝒟₀') (eW : 𝒲 ≌ 𝒲')
  (eW₁ : 𝒲₁ ≌ 𝒲₁') (eW₂ : 𝒲₂ ≌ 𝒲₂') (eW₀ : 𝒲₀ ≌ 𝒲₀')
  {Lj : 𝒟 ⥤ 𝒟₁} {Rj : 𝒟₁ ⥤ 𝒟} {Lf' : 𝒟 ⥤ 𝒟₂} {Rf' : 𝒟₂ ⥤ 𝒟} {Lf : 𝒟₁ ⥤ 𝒟₀}
  {Rf : 𝒟₀ ⥤ 𝒟₁} {Li : 𝒟₂ ⥤ 𝒟₀} {Ri : 𝒟₀ ⥤ 𝒟₂}
  {LjW : 𝒲 ⥤ 𝒲₁} {RjW : 𝒲₁ ⥤ 𝒲} {Lf'W : 𝒲 ⥤ 𝒲₂} {Rf'W : 𝒲₂ ⥤ 𝒲} {LfW : 𝒲₁ ⥤ 𝒲₀}
  {RfW : 𝒲₀ ⥤ 𝒲₁} {LiW : 𝒲₂ ⥤ 𝒲₀} {RiW : 𝒲₀ ⥤ 𝒲₂}
  {Φ : 𝒟 ⥤ 𝒲} {Φ₁ : 𝒟₁ ⥤ 𝒲₁} {Φ₂ : 𝒟₂ ⥤ 𝒲₂} {Φ₀ : 𝒟₀ ⥤ 𝒲₀}
  (adjJ : Lj ⊣ Rj) (adjF' : Lf' ⊣ Rf') (adjF : Lf ⊣ Rf) (adjI : Li ⊣ Ri)
  (adjJW : LjW ⊣ RjW) (adjF'W : Lf'W ⊣ Rf'W) (adjFW : LfW ⊣ RfW) (adjIW : LiW ⊣ RiW)

/-- **The glueing map of Stacks 0DL7 commutes with restriction, at arbitrary models.** Read the
whole cube at other models of its eight corners: the adjunctions through
`Stacks.CategoryTheory.BaseChange.conjAdj`, the 2-cells `σ = σ₁ ≪≫ σ₂ ≪≫ σ₃⁻¹` of the bottom and
top in the shape of `AlgebraicGeometry.Space.pushoutDerivedPullbackSquareIsoOfModels`, and the
vertical faces through `Stacks.CategoryTheory.BaseChange.conjSquare`. If the cube condition `h`
holds at the original models, then the glueing map read at the other models commutes with
restriction, the base change maps being the mates read at the other models. -/
theorem map_glueingMap_comp_conjSquare {_ : Preadditive 𝒟'} [HasBinaryBiproducts 𝒟']
    {_ : Preadditive 𝒲'} [HasBinaryBiproducts 𝒲'] [(e.inverse ⋙ Φ ⋙ eW.functor).Additive]
    {Lc Lc' : 𝒟 ⥤ 𝒟₀} (σ₁ : Lj ⋙ Lf ≅ Lc) (σ₂ : Lc ≅ Lc') (σ₃ : Lf' ⋙ Li ≅ Lc')
    {LcW LcW' : 𝒲 ⥤ 𝒲₀} (σW₁ : LjW ⋙ LfW ≅ LcW) (σW₂ : LcW ≅ LcW') (σW₃ : Lf'W ⋙ LiW ≅ LcW')
    (θj : TwoSquare Φ Lj LjW Φ₁) (θf : TwoSquare Φ₁ Lf LfW Φ₀) (θf' : TwoSquare Φ Lf' Lf'W Φ₂)
    (θi : Φ₂ ⋙ LiW ≅ Li ⋙ Φ₀)
    (h : ∀ N, LfW.map (θj.app N) ≫ θf.app (Lj.obj N) ≫ Φ₀.map ((σ₁ ≪≫ σ₂ ≪≫ σ₃.symm).hom.app N) =
      (σW₁ ≪≫ σW₂ ≪≫ σW₃.symm).hom.app (Φ.obj N) ≫ LiW.map (θf'.app N) ≫
        θi.hom.app (Lf'.obj N))
    (M : 𝒟₁') (K' : 𝒟₂') (α : (e₁.inverse ⋙ Lf ⋙ e₀.functor).obj M ⟶
      (e₂.inverse ⋙ Li ⋙ e₀.functor).obj K') :
    let σ := Functor.isoWhiskerLeft e.inverse (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft Lj
          (Functor.isoWhiskerRight e₁.unitIso.symm Lf ≪≫ Functor.leftUnitor Lf) ≪≫
        σ₁ ≪≫ σ₂ ≪≫ σ₃.symm ≪≫
        Functor.isoWhiskerLeft Lf'
          ((Functor.leftUnitor Li).symm ≪≫ Functor.isoWhiskerRight e₂.unitIso Li))
      e₀.functor)
    let σW := Functor.isoWhiskerLeft eW.inverse (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft LjW (Functor.isoWhiskerRight eW₁.unitIso.symm LfW ≪≫
          Functor.leftUnitor LfW) ≪≫
        σW₁ ≪≫ σW₂ ≪≫ σW₃.symm ≪≫
        Functor.isoWhiskerLeft Lf'W ((Functor.leftUnitor LiW).symm ≪≫
          Functor.isoWhiskerRight eW₂.unitIso LiW))
      eW₀.functor)
    let c := glueingConjugateIso (conjAdj e₁ e₀ adjF) (conjAdj e₂ e₀ adjI) (conjAdj e e₁ adjJ)
      (conjAdj e e₂ adjF') σ
    let cW := glueingConjugateIso (conjAdj eW₁ eW₀ adjFW) (conjAdj eW₂ eW₀ adjIW)
      (conjAdj eW eW₁ adjJW) (conjAdj eW eW₂ adjF'W) σW
    let α' := (conjSquare e₁ eW₁ e₀ eW₀ θf).app M ≫ (e₀.inverse ⋙ Φ₀ ⋙ eW₀.functor).map α ≫
      (conjSquareIso e₂ eW₂ e₀ eW₀ θi).inv.app K'
    ((e.inverse ⋙ Φ ⋙ eW.functor).map biprod.inl ≫
        (e.inverse ⋙ Φ ⋙ eW.functor).map
          (glueingMap (conjAdj e₁ e₀ adjF) (conjAdj e₂ e₀ adjI) c M K' α) ≫
        (conjSquare e₁ e eW₁ eW (mateEquiv adjJ adjJW θj)).app
          ((e₀.inverse ⋙ Rf ⋙ e₁.functor).obj ((e₂.inverse ⋙ Li ⋙ e₀.functor).obj K')) ≫
        (eW₁.inverse ⋙ RjW ⋙ eW.functor).map
          ((conjSquare e₀ e₁ eW₀ eW₁ (mateEquiv adjF adjFW θf)).app
            ((e₂.inverse ⋙ Li ⋙ e₀.functor).obj K')) ≫
        (eW₁.inverse ⋙ RjW ⋙ eW.functor).map ((eW₀.inverse ⋙ RfW ⋙ eW₁.functor).map
          ((conjSquareIso e₂ eW₂ e₀ eW₀ θi).inv.app K')) =
      (conjSquare e₁ e eW₁ eW (mateEquiv adjJ adjJW θj)).app M ≫ biprod.inl ≫
        glueingMap (conjAdj eW₁ eW₀ adjFW) (conjAdj eW₂ eW₀ adjIW) cW
          ((e₁.inverse ⋙ Φ₁ ⋙ eW₁.functor).obj M) ((e₂.inverse ⋙ Φ₂ ⋙ eW₂.functor).obj K') α') ∧
    ((e.inverse ⋙ Φ ⋙ eW.functor).map biprod.inr ≫
        (e.inverse ⋙ Φ ⋙ eW.functor).map
          (glueingMap (conjAdj e₁ e₀ adjF) (conjAdj e₂ e₀ adjI) c M K' α) ≫
        (conjSquare e₁ e eW₁ eW (mateEquiv adjJ adjJW θj)).app
          ((e₀.inverse ⋙ Rf ⋙ e₁.functor).obj ((e₂.inverse ⋙ Li ⋙ e₀.functor).obj K')) ≫
        (eW₁.inverse ⋙ RjW ⋙ eW.functor).map
          ((conjSquare e₀ e₁ eW₀ eW₁ (mateEquiv adjF adjFW θf)).app
            ((e₂.inverse ⋙ Li ⋙ e₀.functor).obj K')) ≫
        (eW₁.inverse ⋙ RjW ⋙ eW.functor).map ((eW₀.inverse ⋙ RfW ⋙ eW₁.functor).map
          ((conjSquareIso e₂ eW₂ e₀ eW₀ θi).inv.app K')) =
      (conjSquare e₂ e eW₂ eW (mateEquiv adjF' adjF'W θf')).app K' ≫ biprod.inr ≫
        glueingMap (conjAdj eW₁ eW₀ adjFW) (conjAdj eW₂ eW₀ adjIW) cW
          ((e₁.inverse ⋙ Φ₁ ⋙ eW₁.functor).obj M) ((e₂.inverse ⋙ Φ₂ ⋙ eW₂.functor).obj K') α') := by
  intro σ σW c cW α'
  have hσ : ∀ N, σ.hom.app N =
      (conjSquare e e₁ e₂ e₀ (TwoSquare.mk _ _ _ _ (σ₁ ≪≫ σ₂ ≪≫ σ₃.symm).hom)).app N :=
    fun N ↦ isoWhiskerLeft_isoWhiskerRight_hom_app e e₁ e₂ e₀ σ₁ σ₂ σ₃ N
  have hσW : ∀ N, σW.hom.app N =
      (conjSquare eW eW₁ eW₂ eW₀ (TwoSquare.mk _ _ _ _ (σW₁ ≪≫ σW₂ ≪≫ σW₃.symm).hom)).app N :=
    fun N ↦ isoWhiskerLeft_isoWhiskerRight_hom_app eW eW₁ eW₂ eW₀ σW₁ σW₂ σW₃ N
  have hcube : ∀ N, (eW₁.inverse ⋙ LfW ⋙ eW₀.functor).map ((conjSquare e eW e₁ eW₁ θj).app N) ≫
      (conjSquare e₁ eW₁ e₀ eW₀ θf).app ((e.inverse ⋙ Lj ⋙ e₁.functor).obj N) ≫
      (e₀.inverse ⋙ Φ₀ ⋙ eW₀.functor).map (σ.hom.app N) =
      σW.hom.app ((e.inverse ⋙ Φ ⋙ eW.functor).obj N) ≫
      (eW₂.inverse ⋙ LiW ⋙ eW₀.functor).map ((conjSquare e eW e₂ eW₂ θf').app N) ≫
      (conjSquareIso e₂ eW₂ e₀ eW₀ θi).hom.app ((e.inverse ⋙ Lf' ⋙ e₂.functor).obj N) := by
    intro N
    rw [hσ, hσW, conjSquareIso_hom]
    exact conjSquare_cube e e₁ e₂ e₀ eW eW₁ eW₂ eW₀ θj θf θf' θi.hom _ _ h N
  have key := map_glueingMap_comp_mate (conjAdj e e₁ adjJ) (conjAdj e e₂ adjF')
    (conjAdj e₁ e₀ adjF) (conjAdj e₂ e₀ adjI) (conjAdj eW eW₁ adjJW) (conjAdj eW eW₂ adjF'W)
    (conjAdj eW₁ eW₀ adjFW) (conjAdj eW₂ eW₀ adjIW) σ σW (conjSquare e eW e₁ eW₁ θj)
    (conjSquare e₁ eW₁ e₀ eW₀ θf) (conjSquare e eW e₂ eW₂ θf') (conjSquareIso e₂ eW₂ e₀ eW₀ θi)
    hcube M K' α
  rwa [conjSquare_mateEquiv, conjSquare_mateEquiv, conjSquare_mateEquiv] at key

/-- `MilnorPatching.map_glueingMap_comp_conjSquare` for 2-cells of the vertical faces given, as in
`Stacks.CategoryTheory.BaseChange.twoSquare`, by pairs of identifications `eg, ef` of the two
composites around each face with a common functor; the base change maps are then the
`Stacks.CategoryTheory.BaseChange.twoSquare`s read at the other models. -/
theorem map_glueingMap_comp_conjBaseChange {pre𝒟 : Preadditive 𝒟'} [HasBinaryBiproducts 𝒟']
    {pre𝒲 : Preadditive 𝒲'} [HasBinaryBiproducts 𝒲'] [hΦ : (e.inverse ⋙ Φ ⋙ eW.functor).Additive]
    {Lc Lc' : 𝒟 ⥤ 𝒟₀} (σ₁ : Lj ⋙ Lf ≅ Lc) (σ₂ : Lc ≅ Lc') (σ₃ : Lf' ⋙ Li ≅ Lc')
    {LcW LcW' : 𝒲 ⥤ 𝒲₀} (σW₁ : LjW ⋙ LfW ≅ LcW) (σW₂ : LcW ≅ LcW') (σW₃ : Lf'W ⋙ LiW ≅ LcW')
    {Mj : 𝒟 ⥤ 𝒲₁} {Mf : 𝒟₁ ⥤ 𝒲₀} {Mf' : 𝒟 ⥤ 𝒲₂} {Mi : 𝒟₂ ⥤ 𝒲₀}
    (egj : Φ ⋙ LjW ≅ Mj) (efj : Lj ⋙ Φ₁ ≅ Mj) (egf : Φ₁ ⋙ LfW ≅ Mf) (eff : Lf ⋙ Φ₀ ≅ Mf)
    (egf' : Φ ⋙ Lf'W ≅ Mf') (eff' : Lf' ⋙ Φ₂ ≅ Mf') (egi : Φ₂ ⋙ LiW ≅ Mi) (efi : Li ⋙ Φ₀ ≅ Mi)
    (h : ∀ N, LfW.map ((pullbackComparison egj efj).app N) ≫
      (pullbackComparison egf eff).app (Lj.obj N) ≫
        Φ₀.map ((σ₁ ≪≫ σ₂ ≪≫ σ₃.symm).hom.app N) =
      (σW₁ ≪≫ σW₂ ≪≫ σW₃.symm).hom.app (Φ.obj N) ≫ LiW.map ((pullbackComparison egf' eff').app N) ≫
        (pullbackComparison egi efi).app (Lf'.obj N))
    (M : 𝒟₁') (K' : 𝒟₂') (α : (e₁.inverse ⋙ Lf ⋙ e₀.functor).obj M ⟶
      (e₂.inverse ⋙ Li ⋙ e₀.functor).obj K') :
    let σ := Functor.isoWhiskerLeft e.inverse (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft Lj
          (Functor.isoWhiskerRight e₁.unitIso.symm Lf ≪≫ Functor.leftUnitor Lf) ≪≫
        σ₁ ≪≫ σ₂ ≪≫ σ₃.symm ≪≫
        Functor.isoWhiskerLeft Lf'
          ((Functor.leftUnitor Li).symm ≪≫ Functor.isoWhiskerRight e₂.unitIso Li))
      e₀.functor)
    let σW := Functor.isoWhiskerLeft eW.inverse (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft LjW (Functor.isoWhiskerRight eW₁.unitIso.symm LfW ≪≫
          Functor.leftUnitor LfW) ≪≫
        σW₁ ≪≫ σW₂ ≪≫ σW₃.symm ≪≫
        Functor.isoWhiskerLeft Lf'W ((Functor.leftUnitor LiW).symm ≪≫
          Functor.isoWhiskerRight eW₂.unitIso LiW))
      eW₀.functor)
    let c := glueingConjugateIso (conjAdj e₁ e₀ adjF) (conjAdj e₂ e₀ adjI) (conjAdj e e₁ adjJ)
      (conjAdj e e₂ adjF') σ
    let cW := glueingConjugateIso (conjAdj eW₁ eW₀ adjFW) (conjAdj eW₂ eW₀ adjIW)
      (conjAdj eW eW₁ adjJW) (conjAdj eW eW₂ adjF'W) σW
    let θi := conjSquareIso e₂ eW₂ e₀ eW₀ (egi ≪≫ efi.symm)
    let βj := conjSquare e₁ e eW₁ eW (twoSquare adjJ adjJW egj efj)
    let βf := conjSquare e₀ e₁ eW₀ eW₁ (twoSquare adjF adjFW egf eff)
    let βf' := conjSquare e₂ e eW₂ eW (twoSquare adjF' adjF'W egf' eff')
    let Φ' := e.inverse ⋙ Φ ⋙ eW.functor
    let RjW' := eW₁.inverse ⋙ RjW ⋙ eW.functor
    let α' := (conjSquareIso e₁ eW₁ e₀ eW₀ (egf ≪≫ eff.symm)).hom.app M ≫
      (e₀.inverse ⋙ Φ₀ ⋙ eW₀.functor).map α ≫ θi.inv.app K'
    let gW := glueingMap (conjAdj eW₁ eW₀ adjFW) (conjAdj eW₂ eW₀ adjIW) cW
      ((e₁.inverse ⋙ Φ₁ ⋙ eW₁.functor).obj M) ((e₂.inverse ⋙ Φ₂ ⋙ eW₂.functor).obj K') α'
    let rest := Φ'.map (glueingMap (conjAdj e₁ e₀ adjF) (conjAdj e₂ e₀ adjI) c M K' α) ≫
      βj.app ((e₀.inverse ⋙ Rf ⋙ e₁.functor).obj ((e₂.inverse ⋙ Li ⋙ e₀.functor).obj K')) ≫
      RjW'.map (βf.app ((e₂.inverse ⋙ Li ⋙ e₀.functor).obj K')) ≫
      RjW'.map ((eW₀.inverse ⋙ RfW ⋙ eW₁.functor).map (θi.inv.app K'))
    (Φ'.map biprod.inl ≫ rest = βj.app M ≫ biprod.inl ≫ gW) ∧
      (Φ'.map biprod.inr ≫ rest = βf'.app K' ≫ biprod.inr ≫ gW) :=
  map_glueingMap_comp_conjSquare e e₁ e₂ e₀ eW eW₁ eW₂ eW₀ adjJ adjF' adjF adjI adjJW adjF'W
    adjFW adjIW σ₁ σ₂ σ₃ σW₁ σW₂ σW₃ (pullbackComparison egj efj) (pullbackComparison egf eff)
    (pullbackComparison egf' eff') (egi ≪≫ efi.symm) h M K' α

end Models

end MilnorPatching


namespace MilnorPatching

section Chart

open Pretriangulated

variable {𝒟 𝒟₁ 𝒟₂ 𝒲 𝒲₁ 𝒲₂ : Type*} {_ : Category.{v21} 𝒟} {_ : Category.{v22} 𝒟₁}
  {_ : Category.{v23} 𝒟₂} {_ : Category.{v5} 𝒲} {_ : Category.{v25} 𝒲₁} {_ : Category.{v26} 𝒲₂}
  {Lj : 𝒟 ⥤ 𝒟₁} {Rj : 𝒟₁ ⥤ 𝒟} {Lf' : 𝒟 ⥤ 𝒟₂} {Rf' : 𝒟₂ ⥤ 𝒟}
  {LjW : 𝒲 ⥤ 𝒲₁} {RjW : 𝒲₁ ⥤ 𝒲} {Lf'W : 𝒲 ⥤ 𝒲₂} {Rf'W : 𝒲₂ ⥤ 𝒲}
  {Φ : 𝒟 ⥤ 𝒲} {Φ₁ : 𝒟₁ ⥤ 𝒲₁} {Φ₂ : 𝒟₂ ⥤ 𝒲₂}
  (adjJ : Lj ⊣ Rj) (adjF' : Lf' ⊣ Rf') (adjJW : LjW ⊣ RjW) (adjF'W : Lf'W ⊣ Rf'W)

/-- The transpose of a map followed by a base change map which is a mate: under `LjW ⊣ RjW`, the
map `Φ g` followed by the mate of `θ` is `θ` followed by `Φ₁` of the transpose of `g`. -/
theorem homEquiv_symm_map_comp_mateEquiv_app (θ : TwoSquare Φ Lj LjW Φ₁) {N : 𝒟} {M : 𝒟₁}
    (g : N ⟶ Rj.obj M) :
    (adjJW.homEquiv _ _).symm (Φ.map g ≫ (mateEquiv adjJ adjJW θ).app M) =
      θ.app N ≫ Φ₁.map ((adjJ.homEquiv _ _).symm g) := by
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    mateEquiv_counit, Functor.map_comp, ← Category.assoc, ← Category.assoc]
  congr 1
  exact θ.naturality g

/-- **The isomorphism step of Stacks 0DL7 is local.** Let `Φ` be a triangulated functor and let
`βj`, `βf'` be invertible base change maps which are the mates of invertible 2-cells `θj`, `θf'`.
Let the glueing map `g` of `(M, K')` and the glueing map `gW` of `(Φ₁ M, Φ₂ K')` correspond under
`Φ`, the base change maps and an isomorphism `e₃` of the targets (`h₁`, `h₂`, the conclusion of
`MilnorPatching.map_glueingMap_comp_baseChange`). If, for every distinguished triangle on `gW`,
the maps adjoint to the two components of its first map are isomorphisms (`hA`), then for the
distinguished triangle `T` on `g` the maps adjoint to the two components of its first map become
isomorphisms after `Φ₁` and `Φ₂`. -/
theorem isIso_map_homEquiv_symm_of_restrict [Preadditive 𝒟] [Preadditive 𝒲]
    [HasBinaryBiproducts 𝒟] [HasBinaryBiproducts 𝒲] [HasShift 𝒟 ℤ] [HasShift 𝒲 ℤ]
    [HasZeroObject 𝒟] [HasZeroObject 𝒲] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive]
    [∀ n : ℤ, (shiftFunctor 𝒲 n).Additive] [Pretriangulated 𝒟] [Pretriangulated 𝒲]
    [Φ.CommShift ℤ] [Φ.IsTriangulated] [Φ.Additive]
    (θj : TwoSquare Φ Lj LjW Φ₁) (θf' : TwoSquare Φ Lf' Lf'W Φ₂)
    [∀ N, IsIso (θj.app N)] [∀ N, IsIso (θf'.app N)]
    (βj : TwoSquare Rj Φ₁ Φ RjW) (βf' : TwoSquare Rf' Φ₂ Φ Rf'W)
    (hβj : mateEquiv adjJ adjJW θj = βj) (hβf' : mateEquiv adjF' adjF'W θf' = βf')
    {M : 𝒟₁} {K' : 𝒟₂} {Z : 𝒟} {ZW : 𝒲} [IsIso (βj.app M)] [IsIso (βf'.app K')]
    (g : Rj.obj M ⊞ Rf'.obj K' ⟶ Z) (gW : RjW.obj (Φ₁.obj M) ⊞ Rf'W.obj (Φ₂.obj K') ⟶ ZW)
    (e₃ : Φ.obj Z ⟶ ZW) [IsIso e₃]
    (h₁ : Φ.map biprod.inl ≫ Φ.map g ≫ e₃ = βj.app M ≫ biprod.inl ≫ gW)
    (h₂ : Φ.map biprod.inr ≫ Φ.map g ≫ e₃ = βf'.app K' ≫ biprod.inr ≫ gW)
    (hA : ∀ {MW : 𝒲} (uW : MW ⟶ RjW.obj (Φ₁.obj M) ⊞ Rf'W.obj (Φ₂.obj K'))
      (vW : ZW ⟶ MW⟦(1 : ℤ)⟧), Triangle.mk uW gW vW ∈ distTriang 𝒲 →
        IsIso ((adjJW.homEquiv _ _).symm (uW ≫ biprod.fst)) ∧
          IsIso ((adjF'W.homEquiv _ _).symm (uW ≫ biprod.snd)))
    {M' : 𝒟} (u : M' ⟶ Rj.obj M ⊞ Rf'.obj K') (v : Z ⟶ M'⟦(1 : ℤ)⟧)
    (hT : Triangle.mk u g v ∈ distTriang 𝒟) :
    IsIso (Φ₁.map ((adjJ.homEquiv _ _).symm (u ≫ biprod.fst))) ∧
      IsIso (Φ₂.map ((adjF'.homEquiv _ _).symm (u ≫ biprod.snd))) := by
  subst hβj hβf'
  have := preservesBinaryBiproducts_of_preservesBinaryProducts Φ
  let φ : Φ.obj (Rj.obj M ⊞ Rf'.obj K') ≅ RjW.obj (Φ₁.obj M) ⊞ Rf'W.obj (Φ₂.obj K') :=
    Φ.mapBiprod _ _ ≪≫ biprod.mapIso (asIso ((mateEquiv adjJ adjJW θj).app M))
      (asIso ((mateEquiv adjF' adjF'W θf').app K'))
  have hφ : Φ.map g ≫ e₃ = φ.hom ≫ gW := by
    rw [← cancel_epi (Φ.mapBiprod _ _).inv]
    simp only [φ, Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc, biprod.mapIso_hom,
      asIso_hom]
    apply biprod.hom_ext'
    · simp only [Functor.mapBiprod_inv, biprod.inl_desc_assoc, biprod.inl_map_assoc]
      exact h₁
    · simp only [Functor.mapBiprod_inv, biprod.inr_desc_assoc, biprod.inr_map_assoc]
      exact h₂
  have hW : Triangle.mk (Φ.map u ≫ φ.hom) gW
      (inv e₃ ≫ Φ.map v ≫ (Φ.commShiftIso (1 : ℤ)).hom.app M') ∈ distTriang 𝒲 := by
    let ψ : Φ.obj Z ≅ ZW := asIso e₃
    refine isomorphic_distinguished _ (Φ.map_distinguished _ hT) _
      (Triangle.isoMk (Φ.mapTriangle.obj (Triangle.mk u g v)) (Triangle.mk (Φ.map u ≫ φ.hom) gW
        (inv e₃ ≫ Φ.map v ≫ (Φ.commShiftIso (1 : ℤ)).hom.app M')) (Iso.refl _) φ ψ
        ?_ ?_ ?_).symm
    · exact (Category.id_comp _).symm
    · exact hφ
    · change (Φ.map v ≫ (Φ.commShiftIso (1 : ℤ)).hom.app M') ≫
          (shiftFunctor 𝒲 (1 : ℤ)).map (𝟙 (Φ.obj M')) =
            e₃ ≫ inv e₃ ≫ Φ.map v ≫ (Φ.commShiftIso (1 : ℤ)).hom.app M'
      simp
  obtain ⟨ha, hb⟩ := hA _ _ hW
  have hfst : (Φ.map u ≫ φ.hom) ≫ biprod.fst =
      Φ.map (u ≫ biprod.fst) ≫ (mateEquiv adjJ adjJW θj).app M := by
    simp only [φ, Iso.trans_hom, Functor.mapBiprod_hom, biprod.mapIso_hom, asIso_hom,
      Category.assoc, biprod.map_fst, biprod.lift_fst_assoc, Functor.map_comp]
  have hsnd : (Φ.map u ≫ φ.hom) ≫ biprod.snd =
      Φ.map (u ≫ biprod.snd) ≫ (mateEquiv adjF' adjF'W θf').app K' := by
    simp only [φ, Iso.trans_hom, Functor.mapBiprod_hom, biprod.mapIso_hom, asIso_hom,
      Category.assoc, biprod.map_snd, biprod.lift_snd_assoc, Functor.map_comp]
  rw [hfst, homEquiv_symm_map_comp_mateEquiv_app] at ha
  rw [hsnd, homEquiv_symm_map_comp_mateEquiv_app] at hb
  exact ⟨IsIso.of_isIso_comp_left (θj.app M') _, IsIso.of_isIso_comp_left (θf'.app M') _⟩

end Chart


section ChartModels

open Stacks.CategoryTheory.BaseChange

variable {𝒟 𝒟₁ 𝒟₂ 𝒟₀ 𝒲 𝒲₁ 𝒲₂ 𝒲₀ 𝒟' 𝒟₁' 𝒟₂' 𝒟₀' 𝒲' 𝒲₁' 𝒲₂' 𝒲₀' : Type*}
  {_ : Category.{v21} 𝒟} {_ : Category.{v22} 𝒟₁} {_ : Category.{v23} 𝒟₂} {_ : Category.{v24} 𝒟₀}
  {_ : Category.{v5} 𝒲} {_ : Category.{v25} 𝒲₁} {_ : Category.{v26} 𝒲₂} {_ : Category.{v27} 𝒲₀}
  {_ : Category.{v28} 𝒟'} {_ : Category.{v29} 𝒟₁'} {_ : Category.{v30} 𝒟₂'} {_ : Category.{v31} 𝒟₀'}
  {_ : Category.{v32} 𝒲'} {_ : Category.{v33} 𝒲₁'} {_ : Category.{v34} 𝒲₂'} {_ : Category.{v35} 𝒲₀'}
  (e : 𝒟 ≌ 𝒟') (e₁ : 𝒟₁ ≌ 𝒟₁') (e₂ : 𝒟₂ ≌ 𝒟₂') (e₀ : 𝒟₀ ≌ 𝒟₀') (eW : 𝒲 ≌ 𝒲')
  (eW₁ : 𝒲₁ ≌ 𝒲₁') (eW₂ : 𝒲₂ ≌ 𝒲₂') (eW₀ : 𝒲₀ ≌ 𝒲₀')
  {Lj : 𝒟 ⥤ 𝒟₁} {Rj : 𝒟₁ ⥤ 𝒟} {Lf' : 𝒟 ⥤ 𝒟₂} {Rf' : 𝒟₂ ⥤ 𝒟} {Lf : 𝒟₁ ⥤ 𝒟₀}
  {Rf : 𝒟₀ ⥤ 𝒟₁} {Li : 𝒟₂ ⥤ 𝒟₀} {Ri : 𝒟₀ ⥤ 𝒟₂}
  {LjW : 𝒲 ⥤ 𝒲₁} {RjW : 𝒲₁ ⥤ 𝒲} {Lf'W : 𝒲 ⥤ 𝒲₂} {Rf'W : 𝒲₂ ⥤ 𝒲} {LfW : 𝒲₁ ⥤ 𝒲₀}
  {RfW : 𝒲₀ ⥤ 𝒲₁} {LiW : 𝒲₂ ⥤ 𝒲₀} {RiW : 𝒲₀ ⥤ 𝒲₂}
  {Φ : 𝒟 ⥤ 𝒲} {Φ₁ : 𝒟₁ ⥤ 𝒲₁} {Φ₂ : 𝒟₂ ⥤ 𝒲₂} {Φ₀ : 𝒟₀ ⥤ 𝒲₀}
  (adjJ : Lj ⊣ Rj) (adjF' : Lf' ⊣ Rf') (adjF : Lf ⊣ Rf) (adjI : Li ⊣ Ri)
  (adjJW : LjW ⊣ RjW) (adjF'W : Lf'W ⊣ Rf'W) (adjFW : LfW ⊣ RfW) (adjIW : LiW ⊣ RiW)

open Pretriangulated

/-- **The isomorphism step of Stacks 0DL7 is local, at arbitrary models.** Read the cube at other
models as in `MilnorPatching.map_glueingMap_comp_conjBaseChange`, let the restriction `Φ` be a
triangulated functor and the base change maps of the faces of `j`, `f`, `f'` invertible. If the
isomorphism step holds for the glueing map `gW` of the restricted triple (`hA`), then for every
distinguished triangle on the glueing map of `(M, K', α)` the maps adjoint to the two components
of its first map become isomorphisms after restriction. -/
theorem isIso_map_homEquiv_symm_of_conjBaseChange {_ : Preadditive 𝒟'} [HasBinaryBiproducts 𝒟']
    {_ : Preadditive 𝒲'} [HasBinaryBiproducts 𝒲'] [HasShift 𝒟' ℤ] [HasShift 𝒲' ℤ]
    [HasZeroObject 𝒟'] [HasZeroObject 𝒲'] [∀ n : ℤ, (shiftFunctor 𝒟' n).Additive]
    [∀ n : ℤ, (shiftFunctor 𝒲' n).Additive] [Pretriangulated 𝒟'] [Pretriangulated 𝒲']
    [hΦ : (e.inverse ⋙ Φ ⋙ eW.functor).Additive] [hΦs : (e.inverse ⋙ Φ ⋙ eW.functor).CommShift ℤ]
    [hΦt : (e.inverse ⋙ Φ ⋙ eW.functor).IsTriangulated]
    {Lc Lc' : 𝒟 ⥤ 𝒟₀} (σ₁ : Lj ⋙ Lf ≅ Lc) (σ₂ : Lc ≅ Lc') (σ₃ : Lf' ⋙ Li ≅ Lc')
    {LcW LcW' : 𝒲 ⥤ 𝒲₀} (σW₁ : LjW ⋙ LfW ≅ LcW) (σW₂ : LcW ≅ LcW') (σW₃ : Lf'W ⋙ LiW ≅ LcW')
    {Mj : 𝒟 ⥤ 𝒲₁} {Mf : 𝒟₁ ⥤ 𝒲₀} {Mf' : 𝒟 ⥤ 𝒲₂} {Mi : 𝒟₂ ⥤ 𝒲₀}
    (egj : Φ ⋙ LjW ≅ Mj) (efj : Lj ⋙ Φ₁ ≅ Mj) (egf : Φ₁ ⋙ LfW ≅ Mf) (eff : Lf ⋙ Φ₀ ≅ Mf)
    (egf' : Φ ⋙ Lf'W ≅ Mf') (eff' : Lf' ⋙ Φ₂ ≅ Mf') (egi : Φ₂ ⋙ LiW ≅ Mi) (efi : Li ⋙ Φ₀ ≅ Mi)
    (h : ∀ N, LfW.map ((pullbackComparison egj efj).app N) ≫
      (pullbackComparison egf eff).app (Lj.obj N) ≫
        Φ₀.map ((σ₁ ≪≫ σ₂ ≪≫ σ₃.symm).hom.app N) =
      (σW₁ ≪≫ σW₂ ≪≫ σW₃.symm).hom.app (Φ.obj N) ≫ LiW.map ((pullbackComparison egf' eff').app N) ≫
        (pullbackComparison egi efi).app (Lf'.obj N))
    (hisoj : ∀ K, @IsIso _ _ _ _ (map adjJ adjJW egj efj K))
    (hisof : ∀ K, @IsIso _ _ _ _ (map adjF adjFW egf eff K))
    (hisof' : ∀ K, @IsIso _ _ _ _ (map adjF' adjF'W egf' eff' K))
    (M : 𝒟₁') (K' : 𝒟₂') (α : (e₁.inverse ⋙ Lf ⋙ e₀.functor).obj M ⟶
      (e₂.inverse ⋙ Li ⋙ e₀.functor).obj K') :
    let σ := Functor.isoWhiskerLeft e.inverse (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft Lj
          (Functor.isoWhiskerRight e₁.unitIso.symm Lf ≪≫ Functor.leftUnitor Lf) ≪≫
        σ₁ ≪≫ σ₂ ≪≫ σ₃.symm ≪≫
        Functor.isoWhiskerLeft Lf'
          ((Functor.leftUnitor Li).symm ≪≫ Functor.isoWhiskerRight e₂.unitIso Li))
      e₀.functor)
    let σW := Functor.isoWhiskerLeft eW.inverse (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft LjW (Functor.isoWhiskerRight eW₁.unitIso.symm LfW ≪≫
          Functor.leftUnitor LfW) ≪≫
        σW₁ ≪≫ σW₂ ≪≫ σW₃.symm ≪≫
        Functor.isoWhiskerLeft Lf'W ((Functor.leftUnitor LiW).symm ≪≫
          Functor.isoWhiskerRight eW₂.unitIso LiW))
      eW₀.functor)
    let c := glueingConjugateIso (conjAdj e₁ e₀ adjF) (conjAdj e₂ e₀ adjI) (conjAdj e e₁ adjJ)
      (conjAdj e e₂ adjF') σ
    let cW := glueingConjugateIso (conjAdj eW₁ eW₀ adjFW) (conjAdj eW₂ eW₀ adjIW)
      (conjAdj eW eW₁ adjJW) (conjAdj eW eW₂ adjF'W) σW
    let α' := (conjSquareIso e₁ eW₁ e₀ eW₀ (egf ≪≫ eff.symm)).hom.app M ≫
      (e₀.inverse ⋙ Φ₀ ⋙ eW₀.functor).map α ≫
        (conjSquareIso e₂ eW₂ e₀ eW₀ (egi ≪≫ efi.symm)).inv.app K'
    let gW := glueingMap (conjAdj eW₁ eW₀ adjFW) (conjAdj eW₂ eW₀ adjIW) cW
      ((e₁.inverse ⋙ Φ₁ ⋙ eW₁.functor).obj M) ((e₂.inverse ⋙ Φ₂ ⋙ eW₂.functor).obj K') α'
    (∀ {MW : 𝒲'} (uW : MW ⟶ (eW₁.inverse ⋙ RjW ⋙ eW.functor).obj
        ((e₁.inverse ⋙ Φ₁ ⋙ eW₁.functor).obj M) ⊞
          (eW₂.inverse ⋙ Rf'W ⋙ eW.functor).obj ((e₂.inverse ⋙ Φ₂ ⋙ eW₂.functor).obj K'))
      (vW : _ ⟶ MW⟦(1 : ℤ)⟧), Triangle.mk uW gW vW ∈ distTriang 𝒲' →
        IsIso (((conjAdj eW eW₁ adjJW).homEquiv _ _).symm (uW ≫ biprod.fst)) ∧
          IsIso (((conjAdj eW eW₂ adjF'W).homEquiv _ _).symm (uW ≫ biprod.snd))) →
    ∀ {M' : 𝒟'} (u : M' ⟶ (e₁.inverse ⋙ Rj ⋙ e.functor).obj M ⊞
        (e₂.inverse ⋙ Rf' ⋙ e.functor).obj K') (v : _ ⟶ M'⟦(1 : ℤ)⟧),
      Triangle.mk u (glueingMap (conjAdj e₁ e₀ adjF) (conjAdj e₂ e₀ adjI) c M K' α) v ∈
        distTriang 𝒟' →
      IsIso ((e₁.inverse ⋙ Φ₁ ⋙ eW₁.functor).map
          (((conjAdj e e₁ adjJ).homEquiv _ _).symm (u ≫ biprod.fst))) ∧
        IsIso ((e₂.inverse ⋙ Φ₂ ⋙ eW₂.functor).map
          (((conjAdj e e₂ adjF').homEquiv _ _).symm (u ≫ biprod.snd))) := by
  intro σ σW c cW α' gW hA M' u v hT
  obtain ⟨h₁, h₂⟩ := map_glueingMap_comp_conjBaseChange (pre𝒟 := ‹_›) (pre𝒲 := ‹_›) e e₁ e₂ e₀ eW
    eW₁ eW₂ eW₀ adjJ adjF' adjF adjI adjJW adjF'W adjFW adjIW σ₁ σ₂ σ₃ σW₁ σW₂ σW₃ egj efj egf eff
    egf' eff' egi efi h M K' α
  have : ∀ K, IsIso ((conjSquare e₁ e eW₁ eW (twoSquare adjJ adjJW egj efj)).app K) :=
    fun K ↦ isIso_conjSquare_twoSquare_app _ _ _ _ _ _ _ _ K (hisoj _)
  have : ∀ K, IsIso ((conjSquare e₀ e₁ eW₀ eW₁ (twoSquare adjF adjFW egf eff)).app K) :=
    fun K ↦ isIso_conjSquare_twoSquare_app _ _ _ _ _ _ _ _ K (hisof _)
  have : ∀ K, IsIso ((conjSquare e₂ e eW₂ eW (twoSquare adjF' adjF'W egf' eff')).app K) :=
    fun K ↦ isIso_conjSquare_twoSquare_app _ _ _ _ _ _ _ _ K (hisof' _)
  have : ∀ N, IsIso ((conjSquare e eW e₁ eW₁ (pullbackComparison egj efj)).app N) := fun N ↦
    isIso_conjSquare_app _ _ _ _ _ N (hθ := by
      dsimp [Stacks.CategoryTheory.BaseChange.pullbackComparison]; infer_instance)
  have : ∀ N, IsIso ((conjSquare e eW e₂ eW₂ (pullbackComparison egf' eff')).app N) := fun N ↦
    isIso_conjSquare_app _ _ _ _ _ N (hθ := by
      dsimp [Stacks.CategoryTheory.BaseChange.pullbackComparison]; infer_instance)
  refine isIso_map_homEquiv_symm_of_restrict (conjAdj e e₁ adjJ) (conjAdj e e₂ adjF')
    (conjAdj eW eW₁ adjJW) (conjAdj eW eW₂ adjF'W)
    (conjSquare e eW e₁ eW₁ (pullbackComparison egj efj))
    (conjSquare e eW e₂ eW₂ (pullbackComparison egf' eff'))
    (conjSquare e₁ e eW₁ eW (twoSquare adjJ adjJW egj efj))
    (conjSquare e₂ e eW₂ eW (twoSquare adjF' adjF'W egf' eff'))
    (conjSquare_mateEquiv _ _ _ _ _ _ _) (conjSquare_mateEquiv _ _ _ _ _ _ _)
    (glueingMap (conjAdj e₁ e₀ adjF) (conjAdj e₂ e₀ adjI) c M K' α) gW
    ((conjSquare e₁ e eW₁ eW (twoSquare adjJ adjJW egj efj)).app
        ((e₀.inverse ⋙ Rf ⋙ e₁.functor).obj ((e₂.inverse ⋙ Li ⋙ e₀.functor).obj K')) ≫
      (eW₁.inverse ⋙ RjW ⋙ eW.functor).map ((conjSquare e₀ e₁ eW₀ eW₁
        (twoSquare adjF adjFW egf eff)).app ((e₂.inverse ⋙ Li ⋙ e₀.functor).obj K')) ≫
      (eW₁.inverse ⋙ RjW ⋙ eW.functor).map ((eW₀.inverse ⋙ RfW ⋙ eW₁.functor).map
        ((conjSquareIso e₂ eW₂ e₀ eW₀ (egi ≪≫ efi.symm)).inv.app K'))) h₁ h₂
    (fun uW vW hW ↦ hA uW vW hW) u v hT

/-- `MilnorPatching.isIso_map_homEquiv_symm_of_conjBaseChange` for an isomorphism `α`, with the
hypothesis on the restricted glueing maps asked for every isomorphism
`αW : LfW^* (Φ₁ M) ≅ LiW^* (Φ₂ K')`, in particular for the restriction of `α`. The objects are
in the shape `G.obj (F.obj M)`, which a concrete instance unfolds to without comparing composite
functors. -/
theorem isIso_map_homEquiv_symm_of_conjBaseChange_iso {_ : Preadditive 𝒟'}
    [HasBinaryBiproducts 𝒟'] {_ : Preadditive 𝒲'} [HasBinaryBiproducts 𝒲'] [HasShift 𝒟' ℤ]
    [HasShift 𝒲' ℤ] [HasZeroObject 𝒟'] [HasZeroObject 𝒲'] [∀ n : ℤ, (shiftFunctor 𝒟' n).Additive]
    [∀ n : ℤ, (shiftFunctor 𝒲' n).Additive] [Pretriangulated 𝒟'] [Pretriangulated 𝒲']
    [hΦ : (e.inverse ⋙ Φ ⋙ eW.functor).Additive]
    [hΦs : (e.inverse ⋙ Φ ⋙ eW.functor).CommShift ℤ]
    [hΦt : (e.inverse ⋙ Φ ⋙ eW.functor).IsTriangulated]
    {Lc Lc' : 𝒟 ⥤ 𝒟₀} (σ₁ : Lj ⋙ Lf ≅ Lc) (σ₂ : Lc ≅ Lc') (σ₃ : Lf' ⋙ Li ≅ Lc')
    {LcW LcW' : 𝒲 ⥤ 𝒲₀} (σW₁ : LjW ⋙ LfW ≅ LcW) (σW₂ : LcW ≅ LcW') (σW₃ : Lf'W ⋙ LiW ≅ LcW')
    {Mj : 𝒟 ⥤ 𝒲₁} {Mf : 𝒟₁ ⥤ 𝒲₀} {Mf' : 𝒟 ⥤ 𝒲₂} {Mi : 𝒟₂ ⥤ 𝒲₀}
    (egj : Φ ⋙ LjW ≅ Mj) (efj : Lj ⋙ Φ₁ ≅ Mj) (egf : Φ₁ ⋙ LfW ≅ Mf) (eff : Lf ⋙ Φ₀ ≅ Mf)
    (egf' : Φ ⋙ Lf'W ≅ Mf') (eff' : Lf' ⋙ Φ₂ ≅ Mf') (egi : Φ₂ ⋙ LiW ≅ Mi) (efi : Li ⋙ Φ₀ ≅ Mi)
    (h : ∀ N, LfW.map ((pullbackComparison egj efj).app N) ≫
      (pullbackComparison egf eff).app (Lj.obj N) ≫
        Φ₀.map ((σ₁ ≪≫ σ₂ ≪≫ σ₃.symm).hom.app N) =
      (σW₁ ≪≫ σW₂ ≪≫ σW₃.symm).hom.app (Φ.obj N) ≫ LiW.map ((pullbackComparison egf' eff').app N) ≫
        (pullbackComparison egi efi).app (Lf'.obj N))
    (hisoj : ∀ K, @IsIso _ _ _ _ (map adjJ adjJW egj efj K))
    (hisof : ∀ K, @IsIso _ _ _ _ (map adjF adjFW egf eff K))
    (hisof' : ∀ K, @IsIso _ _ _ _ (map adjF' adjF'W egf' eff' K))
    (M : 𝒟₁') (K' : 𝒟₂') (α : (e₁.inverse ⋙ Lf ⋙ e₀.functor).obj M ≅
      (e₂.inverse ⋙ Li ⋙ e₀.functor).obj K') :
    let σ := Functor.isoWhiskerLeft e.inverse (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft Lj (Functor.isoWhiskerRight e₁.unitIso.symm Lf ≪≫
          Functor.leftUnitor Lf) ≪≫
        σ₁ ≪≫ σ₂ ≪≫ σ₃.symm ≪≫
        Functor.isoWhiskerLeft Lf' ((Functor.leftUnitor Li).symm ≪≫
          Functor.isoWhiskerRight e₂.unitIso Li))
      e₀.functor)
    let σW := Functor.isoWhiskerLeft eW.inverse (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft LjW (Functor.isoWhiskerRight eW₁.unitIso.symm LfW ≪≫
          Functor.leftUnitor LfW) ≪≫
        σW₁ ≪≫ σW₂ ≪≫ σW₃.symm ≪≫
        Functor.isoWhiskerLeft Lf'W ((Functor.leftUnitor LiW).symm ≪≫
          Functor.isoWhiskerRight eW₂.unitIso LiW))
      eW₀.functor)
    let c := glueingConjugateIso (conjAdj e₁ e₀ adjF) (conjAdj e₂ e₀ adjI) (conjAdj e e₁ adjJ)
      (conjAdj e e₂ adjF') σ
    let cW := glueingConjugateIso (conjAdj eW₁ eW₀ adjFW) (conjAdj eW₂ eW₀ adjIW)
      (conjAdj eW eW₁ adjJW) (conjAdj eW eW₂ adjF'W) σW
    (∀ (αW : (eW₁.inverse ⋙ LfW ⋙ eW₀.functor).obj ((e₁.inverse ⋙ Φ₁ ⋙ eW₁.functor).obj M) ≅
        (eW₂.inverse ⋙ LiW ⋙ eW₀.functor).obj ((e₂.inverse ⋙ Φ₂ ⋙ eW₂.functor).obj K'))
      {MW : 𝒲'} (uW : MW ⟶ (eW₁.inverse ⋙ RjW ⋙ eW.functor).obj
        ((e₁.inverse ⋙ Φ₁ ⋙ eW₁.functor).obj M) ⊞
          (eW₂.inverse ⋙ Rf'W ⋙ eW.functor).obj ((e₂.inverse ⋙ Φ₂ ⋙ eW₂.functor).obj K'))
      (vW : (eW₁.inverse ⋙ RjW ⋙ eW.functor).obj ((eW₀.inverse ⋙ RfW ⋙ eW₁.functor).obj
        ((eW₂.inverse ⋙ LiW ⋙ eW₀.functor).obj ((e₂.inverse ⋙ Φ₂ ⋙ eW₂.functor).obj K'))) ⟶
          MW⟦(1 : ℤ)⟧),
      Triangle.mk uW (glueingMap (conjAdj eW₁ eW₀ adjFW) (conjAdj eW₂ eW₀ adjIW) cW
        ((e₁.inverse ⋙ Φ₁ ⋙ eW₁.functor).obj M) ((e₂.inverse ⋙ Φ₂ ⋙ eW₂.functor).obj K')
          αW.hom) vW ∈ distTriang 𝒲' →
        IsIso (((conjAdj eW eW₁ adjJW).homEquiv _ _).symm (uW ≫ biprod.fst)) ∧
          IsIso (((conjAdj eW eW₂ adjF'W).homEquiv _ _).symm (uW ≫ biprod.snd))) →
    ∀ {M' : 𝒟'} (u : M' ⟶ (e₁.inverse ⋙ Rj ⋙ e.functor).obj M ⊞
        (e₂.inverse ⋙ Rf' ⋙ e.functor).obj K')
      (v : (e₁.inverse ⋙ Rj ⋙ e.functor).obj ((e₀.inverse ⋙ Rf ⋙ e₁.functor).obj
        ((e₂.inverse ⋙ Li ⋙ e₀.functor).obj K')) ⟶ M'⟦(1 : ℤ)⟧),
      Triangle.mk u (glueingMap (conjAdj e₁ e₀ adjF) (conjAdj e₂ e₀ adjI) c M K' α.hom) v ∈
        distTriang 𝒟' →
      IsIso ((e₁.inverse ⋙ Φ₁ ⋙ eW₁.functor).map
          (((conjAdj e e₁ adjJ).homEquiv _ _).symm (u ≫ biprod.fst))) ∧
        IsIso ((e₂.inverse ⋙ Φ₂ ⋙ eW₂.functor).map
          (((conjAdj e e₂ adjF').homEquiv _ _).symm (u ≫ biprod.snd))) := by
  intro σ σW c cW hA M' u v hT
  exact isIso_map_homEquiv_symm_of_conjBaseChange e e₁ e₂ e₀ eW eW₁ eW₂ eW₀ adjJ adjF' adjF adjI
    adjJW adjF'W adjFW adjIW σ₁ σ₂ σ₃ σW₁ σW₂ σW₃ egj efj egf eff egf' eff' egi efi h hisoj hisof
    hisof' M K' α.hom
    (fun uW vW hW ↦ hA ((conjSquareIso e₁ eW₁ e₀ eW₀ (egf ≪≫ eff.symm)).app M ≪≫
      (e₀.inverse ⋙ Φ₀ ⋙ eW₀.functor).mapIso α ≪≫
      ((conjSquareIso e₂ eW₂ e₀ eW₀ (egi ≪≫ efi.symm)).app K').symm) uW vW hW) u v hT

end ChartModels

end MilnorPatching

end
