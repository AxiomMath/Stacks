module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.DerivedPushoutGlueingCube
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquareTransport

/-!
# Carrying the isomorphism step of Stacks 0DL7 from rings to algebraic spaces

The isomorphism step of the proof of Stacks Tag 0DL7 says: for every distinguished triangle
`M' → Rj M ⊕ Rf' K' → Rj Rf Li K' → M'[1]` whose second map is the glueing map of `(M, K', α)`, the
maps `Lj M' ⟶ M` and `Lf' M' ⟶ K'` adjoint to the components of the first map are isomorphisms.
On an affine chart the source proves it on rings and carries it to the algebraic space along the
derived associated-module functors `Ψ`. This file proves that transport over abstract categories:
if `Ψ` is triangulated, its 2-cells `θj`, `θf'` with the inverse images are invertible, their mates
are invertible at `M` and `K'`, and the glueing maps correspond under `Ψ`, then the isomorphism
step for the glueing map of `(M, K', α)` gives the isomorphism step for the glueing map of
`(Ψ₁ M, Ψ₂ K', α_W)`. It also proves that the isomorphism step is invariant under isomorphisms of
triples, and that the 2-cells can be read at other models of the target categories.

## Main definitions

* `Stacks.CategoryTheory.BaseChange.conjSquareTarget`: a 2-cell `T ⋙ R ⟶ L ⋙ B` read at other
  models of the two target corners of `T` and `R`.

## Main results

* `Stacks.CategoryTheory.BaseChange.mateEquiv_conjAdj_conjSquareTarget_app`: taking mates commutes
  with reading at other models of the target corners.
* `Stacks.CategoryTheory.BaseChange.conjSquareTarget_cube`: the pasting equality of a cube whose
  top face is read at other models.
* `MilnorPatching.isIso_homEquiv_symm_of_iso_triple`: the isomorphism step is invariant under
  isomorphisms of triples `(M, K', α)`.
* `MilnorPatching.isIso_homEquiv_symm_of_transport`: **the isomorphism step is carried along a
  triangulated functor.**

## References

* [Stacks Project, Tag 0DL7](https://stacks.math.columbia.edu/tag/0DL7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃ v₁₄ v₁₅ v₁₆

namespace Stacks.CategoryTheory.BaseChange

section ConjugationTarget

variable {C₁ C₂ C₃ C₄ C₂' C₄' : Type*} {_ : Category.{v₁} C₁} {_ : Category.{v₂} C₂}
  {_ : Category.{v₃} C₃} {_ : Category.{v₄} C₄} {_ : Category.{v₅} C₂'} {_ : Category.{v₆} C₄'}
  (e₂ : C₂ ≌ C₂') (e₄ : C₄ ≌ C₄') {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}

/-- **A 2-cell read at other models of its two target corners.** For equivalences
`e₂ : C₂ ≌ C₂'` and `e₄ : C₄ ≌ C₄'` and a 2-cell `θ : T ⋙ R ⟶ L ⋙ B`, the 2-cell
`(T ⋙ e₂.functor) ⋙ (e₂.inverse ⋙ R ⋙ e₄.functor) ⟶ L ⋙ B ⋙ e₄.functor` obtained by cancelling
the unit of `e₂`. -/
def conjSquareTarget (θ : TwoSquare T L R B) :
    TwoSquare (T ⋙ e₂.functor) L (e₂.inverse ⋙ R ⋙ e₄.functor) (B ⋙ e₄.functor) :=
  TwoSquare.mk _ _ _ _
    { app := fun N ↦ e₄.functor.map (R.map (e₂.unitInv.app (T.obj N)) ≫ θ.app N)
      naturality := fun N N' φ ↦ by
        have h₁ := e₂.unitInv.naturality (T.map φ)
        have h₂ := θ.naturality φ
        simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h₁ h₂ ⊢
        rw [← e₄.functor.map_comp, ← e₄.functor.map_comp, ← Category.assoc, ← R.map_comp, h₁,
          R.map_comp, Category.assoc, h₂, Category.assoc] }

/-- The component of `conjSquareTarget e₂ e₄ θ` at `N` is the image under `e₄.functor` of
`R.map (e₂.unitInv.app (T.obj N)) ≫ θ.app N`. -/
theorem conjSquareTarget_app (θ : TwoSquare T L R B) (N : C₁) :
    (conjSquareTarget e₂ e₄ θ).app N =
      e₄.functor.map (R.map (e₂.unitInv.app (T.obj N)) ≫ θ.app N) :=
  rfl

/-- A 2-cell with invertible components, read at other models of its target corners, has
invertible components. -/
theorem isIso_conjSquareTarget_app (θ : TwoSquare T L R B) (N : C₁) [IsIso (θ.app N)] :
    IsIso ((conjSquareTarget e₂ e₄ θ).app N) := by
  rw [conjSquareTarget_app]
  infer_instance

/-- An invertible 2-cell read at other models of its target corners, as an isomorphism. -/
def conjSquareTargetIso (θ : T ⋙ R ≅ L ⋙ B) :
    (T ⋙ e₂.functor) ⋙ (e₂.inverse ⋙ R ⋙ e₄.functor) ≅ L ⋙ B ⋙ e₄.functor :=
  haveI : ∀ N, IsIso ((conjSquareTarget e₂ e₄ θ.hom).app N) := fun N ↦
    isIso_conjSquareTarget_app _ _ _ N
  haveI : IsIso (conjSquareTarget e₂ e₄ θ.hom).natTrans := NatIso.isIso_of_isIso_app _
  asIso (conjSquareTarget e₂ e₄ θ.hom).natTrans

/-- The forward map of `conjSquareTargetIso e₂ e₄ θ` is `conjSquareTarget e₂ e₄ θ.hom`. -/
@[simp]
theorem conjSquareTargetIso_hom (θ : T ⋙ R ≅ L ⋙ B) :
    (conjSquareTargetIso e₂ e₄ θ).hom = conjSquareTarget e₂ e₄ θ.hom :=
  rfl

end ConjugationTarget

section ConjugationTargetMate

variable {C D E F E' F' : Type*} {_ : Category.{v₁} C} {_ : Category.{v₂} D}
  {_ : Category.{v₃} E} {_ : Category.{v₄} F} {_ : Category.{v₅} E'} {_ : Category.{v₆} F'}
  (eE : E ≌ E') (eF : F ≌ F')

/-- **Taking mates commutes with reading at other models of the target corners.** For
adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂` and a 2-cell `α : G ⋙ L₂ ⟶ L₁ ⋙ H`, the mate of `α` read at
other models of the corners of `L₂ ⊣ R₂`, for the adjunction read at those models, is `eE` of the
mate of `α` followed by the unit of `eF`. -/
theorem mateEquiv_conjAdj_conjSquareTarget_app {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F}
    {R₂ : F ⥤ E} {G : C ⥤ E} {H : D ⥤ F} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : TwoSquare G L₁ L₂ H) (M : D) :
    (mateEquiv adj₁ (conjAdj eE eF adj₂) (conjSquareTarget eE eF α)).app M =
      eE.functor.map ((mateEquiv adj₁ adj₂ α).app M ≫ R₂.map (eF.unit.app (H.obj M))) := by
  let β : TwoSquare R₁ (H ⋙ eF.functor) (G ⋙ eE.functor) (eF.inverse ⋙ R₂ ⋙ eE.functor) :=
    TwoSquare.mk _ _ _ _
      { app := fun M ↦ eE.functor.map ((mateEquiv adj₁ adj₂ α).app M ≫
          R₂.map (eF.unit.app (H.obj M)))
        naturality := fun M M' φ ↦ by
          have h₁ := (mateEquiv adj₁ adj₂ α).naturality φ
          have h₂ := eF.unit.naturality (H.map φ)
          simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h₁ h₂ ⊢
          rw [← eE.functor.map_comp, ← eE.functor.map_comp, ← Category.assoc, h₁,
            Category.assoc, ← R₂.map_comp, h₂, R₂.map_comp, Category.assoc] }
  have hβ : β = mateEquiv adj₁ (conjAdj eE eF adj₂) (conjSquareTarget eE eF α) := by
    refine eq_mateEquiv_of_counit _ _ _ _ fun Y ↦ ?_
    have n₁ := mateEquiv_counit adj₁ adj₂ α Y
    simp only [β, conjSquareTarget_app, Adjunction.comp_counit_app, Functor.comp_obj,
      Functor.comp_map, Equivalence.symm_counit, Equivalence.toAdjunction_counit,
      Functor.map_comp, Category.assoc] at n₁ ⊢
    have n₂ := eE.unitInv.naturality
      ((mateEquiv adj₁ adj₂ α).app Y ≫ R₂.map (eF.unit.app (H.obj Y)))
    have n₃ := adj₂.counit.naturality (eF.unit.app (H.obj Y))
    have n₄ := eF.functor_unit_comp (H.obj Y)
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map,
      Functor.map_comp] at n₂ n₃
    have m₂ := congrArg (fun k ↦ eF.functor.map (L₂.map k)) n₂
    have m₃ := congrArg eF.functor.map n₃
    have m₁ := congrArg eF.functor.map n₁
    simp only [Functor.map_comp] at m₂ m₃ m₁
    rw [reassoc_of% m₂, reassoc_of% m₃, n₄, Category.comp_id, m₁]
  rw [← hβ]

end ConjugationTargetMate

section ConjugationTargetCube

/-- Cancelling the unit of an equivalence against its inverse, under a functor. -/
private theorem map_unit_unitInv_assoc {C C' D : Type*} {_ : Category.{v₁} C}
    {_ : Category.{v₂} C'} {_ : Category.{v₃} D} (G : C ⥤ D) (e : C ≌ C') (X : C) {Z : D}
    (g : G.obj X ⟶ Z) : G.map (e.unit.app X) ≫ G.map (e.unitInv.app X) ≫ g = g := by
  rw [← Functor.map_comp_assoc]
  simp

variable {𝒟 𝒟₁ 𝒟₂ 𝒟₀ 𝒲 𝒲₁ 𝒲₂ 𝒲₀ 𝒲' 𝒲₁' 𝒲₂' 𝒲₀' : Type*}
  {_ : Category.{v₁} 𝒟} {_ : Category.{v₂} 𝒟₁} {_ : Category.{v₃} 𝒟₂} {_ : Category.{v₄} 𝒟₀}
  {_ : Category.{v₅} 𝒲} {_ : Category.{v₆} 𝒲₁} {_ : Category.{v₇} 𝒲₂} {_ : Category.{v₈} 𝒲₀}
  {_ : Category.{v₉} 𝒲'} {_ : Category.{v₁₀} 𝒲₁'} {_ : Category.{v₁₁} 𝒲₂'}
  {_ : Category.{v₁₂} 𝒲₀'}
  (eW : 𝒲 ≌ 𝒲') (eW₁ : 𝒲₁ ≌ 𝒲₁') (eW₂ : 𝒲₂ ≌ 𝒲₂') (eW₀ : 𝒲₀ ≌ 𝒲₀')
  {Lj : 𝒟 ⥤ 𝒟₁} {Lf' : 𝒟 ⥤ 𝒟₂} {Lf : 𝒟₁ ⥤ 𝒟₀} {Li : 𝒟₂ ⥤ 𝒟₀}
  {LjW : 𝒲 ⥤ 𝒲₁} {Lf'W : 𝒲 ⥤ 𝒲₂} {LfW : 𝒲₁ ⥤ 𝒲₀} {LiW : 𝒲₂ ⥤ 𝒲₀}
  {Φ : 𝒟 ⥤ 𝒲} {Φ₁ : 𝒟₁ ⥤ 𝒲₁} {Φ₂ : 𝒟₂ ⥤ 𝒲₂} {Φ₀ : 𝒟₀ ⥤ 𝒲₀}

/-- **The pasting equality of a cube survives a change of models of its top face.** If the six
faces of a cube paste to the same 2-cell, so do the faces obtained by reading the four corners of
the top face at other models (`Stacks.CategoryTheory.BaseChange.conjSquare` on the top face,
`Stacks.CategoryTheory.BaseChange.conjSquareTarget` on the four vertical faces). -/
theorem conjSquareTarget_cube (θj : TwoSquare Φ Lj LjW Φ₁) (θf : TwoSquare Φ₁ Lf LfW Φ₀)
    (θf' : TwoSquare Φ Lf' Lf'W Φ₂) (θi : TwoSquare Φ₂ Li LiW Φ₀) (σ : TwoSquare Lj Lf' Lf Li)
    (σW : TwoSquare LjW Lf'W LfW LiW)
    (h : ∀ N, LfW.map (θj.app N) ≫ θf.app (Lj.obj N) ≫ Φ₀.map (σ.app N) =
      σW.app (Φ.obj N) ≫ LiW.map (θf'.app N) ≫ θi.app (Lf'.obj N)) (N : 𝒟) :
    (eW₁.inverse ⋙ LfW ⋙ eW₀.functor).map ((conjSquareTarget eW eW₁ θj).app N) ≫
        (conjSquareTarget eW₁ eW₀ θf).app (Lj.obj N) ≫ (Φ₀ ⋙ eW₀.functor).map (σ.app N) =
      (conjSquare eW eW₁ eW₂ eW₀ σW).app ((Φ ⋙ eW.functor).obj N) ≫
        (eW₂.inverse ⋙ LiW ⋙ eW₀.functor).map ((conjSquareTarget eW eW₂ θf').app N) ≫
        (conjSquareTarget eW₂ eW₀ θi).app (Lf'.obj N) := by
  simp only [conjSquareTarget_app, conjSquare_app, Functor.comp_map, Functor.comp_obj,
    Equivalence.inv_fun_map]
  simp only [← Functor.map_comp]
  congr 1
  simp only [Functor.map_comp, Category.assoc]
  rw [map_unit_unitInv_assoc, map_unit_unitInv_assoc, map_unit_unitInv_assoc]
  congr 1
  have nσ := σW.naturality (eW.unitInv.app (Φ.obj N))
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at nσ
  rw [h N, reassoc_of% nσ]

end ConjugationTargetCube

section TransportUnitMate

variable {C₁ D₁ C₂ D₂ : Type*} {_ : Category.{v₁} C₁} {_ : Category.{v₂} D₁}
  {_ : Category.{v₃} C₂} {_ : Category.{v₄} D₂}
  {Da : C₁ ⥤ D₁} {ra : D₁ ⥤ C₁} {Lf : C₂ ⥤ D₂} {Rf : D₂ ⥤ C₂}

/-- The transposed unit `Φ_R (ra M) ⟶ Rf (Φ_A M)` of an isomorphism `β : Φ_R ⋙ Lf ≅ Da ⋙ Φ_A`
is the mate of `β`. -/
theorem mateEquiv_app_eq_transportUnit (adja : Da ⊣ ra) (adjf : Lf ⊣ Rf) (ΦR : C₁ ⥤ C₂)
    (ΦA : D₁ ⥤ D₂) (βf : ΦR ⋙ Lf ≅ Da ⋙ ΦA) (M : D₁) :
    (mateEquiv adja adjf (TwoSquare.mk _ _ _ _ βf.hom)).app M =
      transportUnit adja adjf ΦR ΦA βf M := by
  simp [mateEquiv_apply, transportUnit, Adjunction.homEquiv_unit]

/-- The mate of a 2-cell read at other models of the target corners is invertible when the
transposed unit of the 2-cell is. -/
private theorem isIso_mateEquiv_conjAdj_conjSquareTarget_app {C D E F E' F' : Type*}
    {_ : Category.{v₁} C} {_ : Category.{v₂} D} {_ : Category.{v₃} E} {_ : Category.{v₄} F}
    {_ : Category.{v₅} E'} {_ : Category.{v₆} F'} (eE : E ≌ E') (eF : F ≌ F') {L₁ : C ⥤ D}
    {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E} {G : C ⥤ E} {H : D ⥤ F} (adj₁ : L₁ ⊣ R₁)
    (adj₂ : L₂ ⊣ R₂) (θ : G ⋙ L₂ ≅ L₁ ⋙ H) (M : D) [IsIso (transportUnit adj₁ adj₂ G H θ M)] :
    IsIso ((mateEquiv adj₁ (conjAdj eE eF adj₂)
      (conjSquareTarget eE eF (TwoSquare.mk _ _ _ _ θ.hom))).app M) := by
  rw [mateEquiv_conjAdj_conjSquareTarget_app, mateEquiv_app_eq_transportUnit]
  infer_instance

end TransportUnitMate

end Stacks.CategoryTheory.BaseChange

namespace MilnorPatching

open Pretriangulated

section Triple

variable {𝒟 𝒟₁ 𝒟₂ 𝒟₀ : Type*} {_ : Category.{v₁} 𝒟} {_ : Category.{v₂} 𝒟₁}
  {_ : Category.{v₃} 𝒟₂} {_ : Category.{v₄} 𝒟₀}
  {Lj : 𝒟 ⥤ 𝒟₁} {Rj : 𝒟₁ ⥤ 𝒟} {Lf' : 𝒟 ⥤ 𝒟₂} {Rf' : 𝒟₂ ⥤ 𝒟} {Lf : 𝒟₁ ⥤ 𝒟₀}
  {Rf : 𝒟₀ ⥤ 𝒟₁} {Li : 𝒟₂ ⥤ 𝒟₀} {Ri : 𝒟₀ ⥤ 𝒟₂}
  (adjJ : Lj ⊣ Rj) (adjF' : Lf' ⊣ Rf') (adjF : Lf ⊣ Rf) (adjI : Li ⊣ Ri)

/-- **The isomorphism step of Stacks 0DL7 is invariant under isomorphisms of triples.** If
`(M₁, K₁, α₁)` and `(M₂, K₂, α₂)` are isomorphic triples, and for every distinguished triangle on
the glueing map of the first the maps adjoint to the components of its first map are
isomorphisms, the same holds for the second. -/
theorem isIso_homEquiv_symm_of_iso_triple [Preadditive 𝒟] [HasBinaryBiproducts 𝒟]
    [HasShift 𝒟 ℤ] [HasZeroObject 𝒟] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]
    (c : Rf ⋙ Rj ≅ Ri ⋙ Rf') {M₁ M₂ : 𝒟₁} {K₁ K₂ : 𝒟₂} (eM : M₁ ≅ M₂) (eK : K₁ ≅ K₂)
    (α₁ : Lf.obj M₁ ⟶ Li.obj K₁) (α₂ : Lf.obj M₂ ⟶ Li.obj K₂)
    (hα : Lf.map eM.hom ≫ α₂ = α₁ ≫ Li.map eK.hom)
    (hA : ∀ {M' : 𝒟} (u : M' ⟶ Rj.obj M₁ ⊞ Rf'.obj K₁)
      (v : Rj.obj (Rf.obj (Li.obj K₁)) ⟶ M'⟦(1 : ℤ)⟧),
      Triangle.mk u (glueingMap adjF adjI c M₁ K₁ α₁) v ∈ distTriang 𝒟 →
        IsIso ((adjJ.homEquiv _ _).symm (u ≫ biprod.fst)) ∧
          IsIso ((adjF'.homEquiv _ _).symm (u ≫ biprod.snd)))
    {M' : 𝒟} (u : M' ⟶ Rj.obj M₂ ⊞ Rf'.obj K₂) (v : Rj.obj (Rf.obj (Li.obj K₂)) ⟶ M'⟦(1 : ℤ)⟧)
    (hT : Triangle.mk u (glueingMap adjF adjI c M₂ K₂ α₂) v ∈ distTriang 𝒟) :
    IsIso ((adjJ.homEquiv _ _).symm (u ≫ biprod.fst)) ∧
      IsIso ((adjF'.homEquiv _ _).symm (u ≫ biprod.snd)) := by
  let bm : Rj.obj M₁ ⊞ Rf'.obj K₁ ≅ Rj.obj M₂ ⊞ Rf'.obj K₂ :=
    biprod.mapIso (Rj.mapIso eM) (Rf'.mapIso eK)
  let e₃ := Rj.mapIso (Rf.mapIso (Li.mapIso eK))
  have hT₁ : Triangle.mk (u ≫ bm.inv) (glueingMap adjF adjI c M₁ K₁ α₁) (e₃.hom ≫ v) ∈
      distTriang 𝒟 := by
    refine isomorphic_distinguished _ hT _ (Triangle.isoMk _ _ (Iso.refl _) bm e₃ (by simp)
      (biprod_map_comp_glueingMap adjF adjI c eM.hom eK.hom α₁ α₂ hα).symm (by simp))
  obtain ⟨ha, hb⟩ := hA _ _ hT₁
  have hfst : (u ≫ bm.inv) ≫ biprod.fst = (u ≫ biprod.fst) ≫ Rj.map eM.inv := by simp [bm]
  have hsnd : (u ≫ bm.inv) ≫ biprod.snd = (u ≫ biprod.snd) ≫ Rf'.map eK.inv := by simp [bm]
  rw [hfst, Adjunction.homEquiv_naturality_right_symm] at ha
  rw [hsnd, Adjunction.homEquiv_naturality_right_symm] at hb
  exact ⟨IsIso.of_isIso_comp_right _ eM.inv, IsIso.of_isIso_comp_right _ eK.inv⟩

end Triple

section Transport

variable {𝒟 𝒟₁ 𝒟₂ 𝒲 𝒲₁ 𝒲₂ : Type*} {_ : Category.{v₁} 𝒟} {_ : Category.{v₂} 𝒟₁}
  {_ : Category.{v₃} 𝒟₂} {_ : Category.{v₅} 𝒲} {_ : Category.{v₆} 𝒲₁} {_ : Category.{v₇} 𝒲₂}
  {Lj : 𝒟 ⥤ 𝒟₁} {Rj : 𝒟₁ ⥤ 𝒟} {Lf' : 𝒟 ⥤ 𝒟₂} {Rf' : 𝒟₂ ⥤ 𝒟}
  {LjW : 𝒲 ⥤ 𝒲₁} {RjW : 𝒲₁ ⥤ 𝒲} {Lf'W : 𝒲 ⥤ 𝒲₂} {Rf'W : 𝒲₂ ⥤ 𝒲}
  {Φ : 𝒟 ⥤ 𝒲} {Φ₁ : 𝒟₁ ⥤ 𝒲₁} {Φ₂ : 𝒟₂ ⥤ 𝒲₂}
  (adjJ : Lj ⊣ Rj) (adjF' : Lf' ⊣ Rf') (adjJW : LjW ⊣ RjW) (adjF'W : Lf'W ⊣ Rf'W)

/-- If `w` has invertible transpose and the mate of `θ` is invertible at `M`, then `Φ w` followed by
that mate, precomposed with an isomorphism, has invertible transpose. -/
private theorem isIso_homEquiv_symm_comp_of_eq_map_comp_mateEquiv_app
    (θ : TwoSquare Φ Lj LjW Φ₁) [∀ N, IsIso (θ.app N)] {N : 𝒟} {X : 𝒲} (a : X ⟶ Φ.obj N) [IsIso a]
    {M : 𝒟₁} [IsIso ((mateEquiv adjJ adjJW θ).app M)] (p : Φ.obj N ⟶ RjW.obj (Φ₁.obj M))
    (w : N ⟶ Rj.obj M) (hp : p = Φ.map w ≫ (mateEquiv adjJ adjJW θ).app M)
    (hw : IsIso ((adjJ.homEquiv _ _).symm w)) : IsIso ((adjJW.homEquiv _ _).symm (a ≫ p)) := by
  rw [hp, Adjunction.homEquiv_naturality_left_symm, homEquiv_symm_map_comp_mateEquiv_app]
  infer_instance

/-- **The isomorphism step of Stacks 0DL7 is carried along a triangulated functor.** Let `Φ` be a
triangulated functor with invertible 2-cells `θj : Φ ⋙ LjW ⟶ Lj ⋙ Φ₁` and
`θf' : Φ ⋙ Lf'W ⟶ Lf' ⋙ Φ₂` whose mates are invertible at `M` and `K'`, and let the glueing map
`g` of `(M, K')` and the glueing map `gW` of `(Φ₁ M, Φ₂ K')` correspond under `Φ`, the mates and an
isomorphism `e₃` of the targets (`h₁`, `h₂`: the conclusion of
`MilnorPatching.map_glueingMap_comp_mate`). If the isomorphism step holds for `g` (`hA`), it holds
for `gW`: for every distinguished triangle on `gW` the maps adjoint to the two components of its
first map are isomorphisms. The given triangle is compared with the image under `Φ` of a
distinguished triangle on `g`. -/
theorem isIso_homEquiv_symm_of_transport [Preadditive 𝒟] [Preadditive 𝒲]
    [HasBinaryBiproducts 𝒟] [HasBinaryBiproducts 𝒲] [HasShift 𝒟 ℤ] [HasShift 𝒲 ℤ]
    [HasZeroObject 𝒟] [HasZeroObject 𝒲] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive]
    [∀ n : ℤ, (shiftFunctor 𝒲 n).Additive] [Pretriangulated 𝒟] [Pretriangulated 𝒲]
    [Φ.CommShift ℤ] [Φ.IsTriangulated] [Φ.Additive]
    (θj : TwoSquare Φ Lj LjW Φ₁) (θf' : TwoSquare Φ Lf' Lf'W Φ₂)
    [∀ N, IsIso (θj.app N)] [∀ N, IsIso (θf'.app N)]
    {M : 𝒟₁} {K' : 𝒟₂} {Z : 𝒟} {ZW : 𝒲}
    [IsIso ((mateEquiv adjJ adjJW θj).app M)] [IsIso ((mateEquiv adjF' adjF'W θf').app K')]
    (g : Rj.obj M ⊞ Rf'.obj K' ⟶ Z) (gW : RjW.obj (Φ₁.obj M) ⊞ Rf'W.obj (Φ₂.obj K') ⟶ ZW)
    (e₃ : Φ.obj Z ⟶ ZW) [IsIso e₃]
    (h₁ : Φ.map biprod.inl ≫ Φ.map g ≫ e₃ =
      (mateEquiv adjJ adjJW θj).app M ≫ biprod.inl ≫ gW)
    (h₂ : Φ.map biprod.inr ≫ Φ.map g ≫ e₃ =
      (mateEquiv adjF' adjF'W θf').app K' ≫ biprod.inr ≫ gW)
    (hA : ∀ {M' : 𝒟} (u : M' ⟶ Rj.obj M ⊞ Rf'.obj K') (v : Z ⟶ M'⟦(1 : ℤ)⟧),
      Triangle.mk u g v ∈ distTriang 𝒟 →
        IsIso ((adjJ.homEquiv _ _).symm (u ≫ biprod.fst)) ∧
          IsIso ((adjF'.homEquiv _ _).symm (u ≫ biprod.snd)))
    {MW : 𝒲} (uW : MW ⟶ RjW.obj (Φ₁.obj M) ⊞ Rf'W.obj (Φ₂.obj K'))
    (vW : ZW ⟶ MW⟦(1 : ℤ)⟧) (hTW : Triangle.mk uW gW vW ∈ distTriang 𝒲) :
    IsIso ((adjJW.homEquiv _ _).symm (uW ≫ biprod.fst)) ∧
      IsIso ((adjF'W.homEquiv _ _).symm (uW ≫ biprod.snd)) := by
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
  obtain ⟨M', u, v, hT⟩ := distinguished_cocone_triangle₁ g
  obtain ⟨ha, hb⟩ := hA u v hT
  have hT' := Φ.map_distinguished _ hT
  have hW : Triangle.mk (Φ.map u ≫ φ.hom) gW
      (inv e₃ ≫ Φ.map v ≫ (Φ.commShiftIso (1 : ℤ)).hom.app M') ∈ distTriang 𝒲 := by
    let ψ : Φ.obj Z ≅ ZW := asIso e₃
    refine isomorphic_distinguished _ hT' _
      (Triangle.isoMk (Φ.mapTriangle.obj (Triangle.mk u g v)) (Triangle.mk (Φ.map u ≫ φ.hom) gW
        (inv e₃ ≫ Φ.map v ≫ (Φ.commShiftIso (1 : ℤ)).hom.app M')) (Iso.refl _) φ ψ
        (Category.id_comp _).symm hφ ?_).symm
    show (Φ.map v ≫ (Φ.commShiftIso (1 : ℤ)).hom.app M') ≫
          (shiftFunctor 𝒲 (1 : ℤ)).map (𝟙 (Φ.obj M')) =
            e₃ ≫ inv e₃ ≫ Φ.map v ≫ (Φ.commShiftIso (1 : ℤ)).hom.app M'
    simp
  obtain ⟨a, ha₁, ha₂⟩ := complete_distinguished_triangle_morphism₁ _ _ hW hTW (𝟙 _) (𝟙 _)
    (by simp)
  have hiso : IsIso a :=
    isIso₁_of_isIso₂₃ (Triangle.homMk _ _ a (𝟙 _) (𝟙 _) ha₁ (by simp) ha₂) hW hTW
      (by show IsIso (𝟙 _); infer_instance) (by show IsIso (𝟙 _); infer_instance)
  have hu : uW = inv a ≫ Φ.map u ≫ φ.hom := by
    rw [IsIso.eq_inv_comp]
    simpa using ha₁.symm
  have hfst : (Φ.map u ≫ φ.hom) ≫ biprod.fst =
      Φ.map (u ≫ biprod.fst) ≫ (mateEquiv adjJ adjJW θj).app M := by
    simp only [φ, Iso.trans_hom, Functor.mapBiprod_hom, biprod.mapIso_hom, asIso_hom,
      Category.assoc, biprod.map_fst, biprod.lift_fst_assoc, Functor.map_comp]
  have hsnd : (Φ.map u ≫ φ.hom) ≫ biprod.snd =
      Φ.map (u ≫ biprod.snd) ≫ (mateEquiv adjF' adjF'W θf').app K' := by
    simp only [φ, Iso.trans_hom, Functor.mapBiprod_hom, biprod.mapIso_hom, asIso_hom,
      Category.assoc, biprod.map_snd, biprod.lift_snd_assoc, Functor.map_comp]
  rw [hu]
  constructor
  · rw [Category.assoc]
    exact isIso_homEquiv_symm_comp_of_eq_map_comp_mateEquiv_app adjJ adjJW θj (inv a) _ _ hfst ha
  · rw [Category.assoc]
    exact isIso_homEquiv_symm_comp_of_eq_map_comp_mateEquiv_app adjF' adjF'W θf' (inv a) _ _ hsnd
      hb

end Transport

section Pasting

variable {𝒟 𝒟₁ 𝒟₂ 𝒟₀ 𝒲 𝒲₁ 𝒲₂ 𝒲₀ : Type*}
  {_ : Category.{v₁} 𝒟} {_ : Category.{v₂} 𝒟₁} {_ : Category.{v₃} 𝒟₂} {_ : Category.{v₄} 𝒟₀}
  {_ : Category.{v₅} 𝒲} {_ : Category.{v₆} 𝒲₁} {_ : Category.{v₇} 𝒲₂} {_ : Category.{v₈} 𝒲₀}
  {Lj : 𝒟 ⥤ 𝒟₁} {Lf' : 𝒟 ⥤ 𝒟₂} {Lf : 𝒟₁ ⥤ 𝒟₀} {Li : 𝒟₂ ⥤ 𝒟₀} {Lc : 𝒟 ⥤ 𝒟₀}
  {LjW : 𝒲 ⥤ 𝒲₁} {Lf'W : 𝒲 ⥤ 𝒲₂} {LfW : 𝒲₁ ⥤ 𝒲₀} {LiW : 𝒲₂ ⥤ 𝒲₀} {LcW : 𝒲 ⥤ 𝒲₀}
  {Φ : 𝒟 ⥤ 𝒲} {Φ₁ : 𝒟₁ ⥤ 𝒲₁} {Φ₂ : 𝒟₂ ⥤ 𝒲₂} {Φ₀ : 𝒟₀ ⥤ 𝒲₀}

/-- Transport along an equality, read on the inverse: the inverse of `eqToIso (congrArg F h)` is
`eqToIso (congrArg F h.symm)`. -/
theorem eqToIso_congrArg_symm {α : Sort*} {C D : Type*} [Category* C] [Category* D]
    (F : α → C ⥤ D) {a b : α} (h : a = b) :
    (eqToIso (congrArg F h)).symm = eqToIso (congrArg F h.symm) := by
  subst h
  rfl

/-- **The pasting equality of the cube from a compatibility up to a central automorphism.** If
the two composites of the 2-cells `θ` around the square, through the composition isomorphisms
`c₁, c₂` of the inverse images on the first square and `d₁, d₂ = d₃ ≪≫ e` on the second, agree up
to an automorphism `t` of the identity of the last corner, then the cube with bottom
`c₁ ≪≫ c₂⁻¹`, top `d₁ ≪≫ e' ≪≫ d₃⁻¹` (for `e' = e⁻¹`) and the last 2-cell `θi` twisted by `t` has
equal pastings. -/
theorem pasting_of_compat {LeW : 𝒲 ⥤ 𝒲₀} (θj : Φ ⋙ LjW ≅ Lj ⋙ Φ₁) (θf : Φ₁ ⋙ LfW ≅ Lf ⋙ Φ₀)
    (θf' : Φ ⋙ Lf'W ≅ Lf' ⋙ Φ₂) (θi : Φ₂ ⋙ LiW ≅ Li ⋙ Φ₀) (c₁ : Lj ⋙ Lf ≅ Lc)
    (c₂ : Lf' ⋙ Li ≅ Lc) (d₁ : LjW ⋙ LfW ≅ LcW) (d₂ : Lf'W ⋙ LiW ≅ LcW)
    (d₃ : Lf'W ⋙ LiW ≅ LeW) (e : LeW ≅ LcW) (hd : d₂ = d₃ ≪≫ e)
    (e' : LcW ≅ LeW) (he : e' = e.symm) (t : 𝟭 𝒟₀ ≅ 𝟭 𝒟₀)
    (hcompat : ∀ N, LfW.map (θj.hom.app N) ≫ θf.hom.app (Lj.obj N) ≫ Φ₀.map (c₁.hom.app N) =
      d₁.hom.app (Φ.obj N) ≫ d₂.inv.app (Φ.obj N) ≫ LiW.map (θf'.hom.app N) ≫
        θi.hom.app (Lf'.obj N) ≫ Φ₀.map (c₂.hom.app N) ≫ Φ₀.map (t.hom.app (Lc.obj N)))
    (N : 𝒟) :
    LfW.map (θj.hom.app N) ≫ θf.hom.app (Lj.obj N) ≫ Φ₀.map ((c₁ ≪≫ c₂.symm).hom.app N) =
      (d₁ ≪≫ e' ≪≫ d₃.symm).hom.app (Φ.obj N) ≫ LiW.map (θf'.hom.app N) ≫
        (θi ≪≫ Functor.isoWhiskerLeft Li ((Functor.leftUnitor Φ₀).symm ≪≫
          Functor.isoWhiskerRight t Φ₀ ≪≫ Functor.leftUnitor Φ₀)).hom.app (Lf'.obj N) := by
  subst hd he
  have nt := t.hom.naturality (c₂.hom.app N)
  simp only [Functor.id_map, Functor.id_obj, Functor.comp_obj] at nt
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app,
    Category.assoc, Category.id_comp]
  rw [reassoc_of% (hcompat N)]
  simp only [Iso.trans_inv, NatTrans.comp_app, Category.assoc]
  congr 4
  rw [← Φ₀.map_comp, ← Φ₀.map_comp, reassoc_of% nt, Iso.hom_inv_id_app]
  exact congrArg (θi.hom.app (Lf'.obj N) ≫ ·)
    ((congrArg Φ₀.map (Category.comp_id _)).trans (Category.comp_id _).symm)

end Pasting

section TransportModels

open Stacks.CategoryTheory.BaseChange

variable {𝒟 𝒟₁ 𝒟₂ 𝒟₀ 𝒲 𝒲₁ 𝒲₂ 𝒲₀ 𝒲' 𝒲₁' 𝒲₂' 𝒲₀' : Type*}
  {_ : Category.{v₁} 𝒟} {_ : Category.{v₂} 𝒟₁} {_ : Category.{v₃} 𝒟₂} {_ : Category.{v₄} 𝒟₀}
  {_ : Category.{v₅} 𝒲} {_ : Category.{v₆} 𝒲₁} {_ : Category.{v₇} 𝒲₂} {_ : Category.{v₈} 𝒲₀}
  {_ : Category.{v₉} 𝒲'} {_ : Category.{v₁₀} 𝒲₁'} {_ : Category.{v₁₁} 𝒲₂'}
  {_ : Category.{v₁₂} 𝒲₀'}
  (eW : 𝒲 ≌ 𝒲') (eW₁ : 𝒲₁ ≌ 𝒲₁') (eW₂ : 𝒲₂ ≌ 𝒲₂') (eW₀ : 𝒲₀ ≌ 𝒲₀')
  {Lj : 𝒟 ⥤ 𝒟₁} {Rj : 𝒟₁ ⥤ 𝒟} {Lf' : 𝒟 ⥤ 𝒟₂} {Rf' : 𝒟₂ ⥤ 𝒟} {Lf : 𝒟₁ ⥤ 𝒟₀}
  {Rf : 𝒟₀ ⥤ 𝒟₁} {Li : 𝒟₂ ⥤ 𝒟₀} {Ri : 𝒟₀ ⥤ 𝒟₂}
  {LjW : 𝒲 ⥤ 𝒲₁} {RjW : 𝒲₁ ⥤ 𝒲} {Lf'W : 𝒲 ⥤ 𝒲₂} {Rf'W : 𝒲₂ ⥤ 𝒲} {LfW : 𝒲₁ ⥤ 𝒲₀}
  {RfW : 𝒲₀ ⥤ 𝒲₁} {LiW : 𝒲₂ ⥤ 𝒲₀} {RiW : 𝒲₀ ⥤ 𝒲₂}
  {Φ : 𝒟 ⥤ 𝒲} {Φ₁ : 𝒟₁ ⥤ 𝒲₁} {Φ₂ : 𝒟₂ ⥤ 𝒲₂} {Φ₀ : 𝒟₀ ⥤ 𝒲₀}
  (adjJ : Lj ⊣ Rj) (adjF' : Lf' ⊣ Rf') (adjF : Lf ⊣ Rf) (adjI : Li ⊣ Ri)
  (adjJW : LjW ⊣ RjW) (adjF'W : Lf'W ⊣ Rf'W) (adjFW : LfW ⊣ RfW) (adjIW : LiW ⊣ RiW)

/-- **The isomorphism step of Stacks 0DL7 is carried from rings to a square read at other
models.** Let `Φ, Φ₁, Φ₂, Φ₀` carry a square of adjunctions (the derived change-of-rings
adjunctions of a square of rings, with 2-cell `σ`) to a second one (the derived pullback and direct
image of a square of algebraic spaces, with 2-cell `σW`), through invertible 2-cells `θ` with the
inverse images whose transposed units (`Stacks.CategoryTheory.BaseChange.transportUnit`) are
invertible, and let the six faces of the cube paste to the same 2-cell (`h`). Let `Φ` be
triangulated and `Φ₀` fully faithful. Read the second square at other models through equivalences
`eW, eW₁, eW₂, eW₀`. If the isomorphism step holds on rings for
`(m, k)` and every isomorphism `α_r`, then it holds for every triple `(M, K', α)` with
`M ≅ eW₁ (Φ₁ m)` and `K' ≅ eW₂ (Φ₂ k)`. -/
theorem isIso_homEquiv_symm_of_transport_models [Preadditive 𝒟] [Preadditive 𝒲]
    [Preadditive 𝒲'] [HasBinaryBiproducts 𝒟] [HasBinaryBiproducts 𝒲'] [HasShift 𝒟 ℤ]
    [HasShift 𝒲 ℤ] [HasShift 𝒲' ℤ] [HasZeroObject 𝒟] [HasZeroObject 𝒲] [HasZeroObject 𝒲']
    [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [∀ n : ℤ, (shiftFunctor 𝒲 n).Additive]
    [∀ n : ℤ, (shiftFunctor 𝒲' n).Additive] [Pretriangulated 𝒟] [Pretriangulated 𝒲]
    [Pretriangulated 𝒲'] [Φ.CommShift ℤ] [Φ.IsTriangulated] [Φ.Additive]
    [eW.functor.CommShift ℤ] [eW.functor.IsTriangulated] [eW.functor.Additive]
    (σ : Lj ⋙ Lf ≅ Lf' ⋙ Li)
    {LcW LcW' : 𝒲 ⥤ 𝒲₀} (σW₁ : LjW ⋙ LfW ≅ LcW) (σW₂ : LcW ≅ LcW') (σW₃ : Lf'W ⋙ LiW ≅ LcW')
    (θj : Φ ⋙ LjW ≅ Lj ⋙ Φ₁) (θf : Φ₁ ⋙ LfW ≅ Lf ⋙ Φ₀) (θf' : Φ ⋙ Lf'W ≅ Lf' ⋙ Φ₂)
    (θi : Φ₂ ⋙ LiW ≅ Li ⋙ Φ₀)
    (h : ∀ N, LfW.map (θj.hom.app N) ≫ θf.hom.app (Lj.obj N) ≫ Φ₀.map (σ.hom.app N) =
      (σW₁ ≪≫ σW₂ ≪≫ σW₃.symm).hom.app (Φ.obj N) ≫ LiW.map (θf'.hom.app N) ≫
        θi.hom.app (Lf'.obj N))
    (hj : ∀ M, IsIso (transportUnit adjJ adjJW Φ Φ₁ θj M))
    (hf' : ∀ K, IsIso (transportUnit adjF' adjF'W Φ Φ₂ θf' K))
    (hf : ∀ N, IsIso (transportUnit adjF adjFW Φ₁ Φ₀ θf N))
    (hΦ₀ : Φ₀.FullyFaithful)
    (m : 𝒟₁) (k : 𝒟₂)
    (hR : ∀ (αr : Lf.obj m ≅ Li.obj k) {M' : 𝒟} (u : M' ⟶ Rj.obj m ⊞ Rf'.obj k)
      (v : Rj.obj (Rf.obj (Li.obj k)) ⟶ M'⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk u
          (glueingMap adjF adjI (glueingConjugateIso adjF adjI adjJ adjF' σ) m k αr.hom) v ∈
        distTriang 𝒟 →
        IsIso ((adjJ.homEquiv _ _).symm (u ≫ biprod.fst)) ∧
          IsIso ((adjF'.homEquiv _ _).symm (u ≫ biprod.snd)))
    {M : 𝒲₁'} {K' : 𝒲₂'} (eM : eW₁.functor.obj (Φ₁.obj m) ≅ M)
    (eK : eW₂.functor.obj (Φ₂.obj k) ≅ K')
    (α : (eW₁.inverse ⋙ LfW ⋙ eW₀.functor).obj M ≅ (eW₂.inverse ⋙ LiW ⋙ eW₀.functor).obj K')
    {M' : 𝒲'} (u : M' ⟶ (eW₁.inverse ⋙ RjW ⋙ eW.functor).obj M ⊞
      (eW₂.inverse ⋙ Rf'W ⋙ eW.functor).obj K')
    (v : (eW₁.inverse ⋙ RjW ⋙ eW.functor).obj ((eW₀.inverse ⋙ RfW ⋙ eW₁.functor).obj
      ((eW₂.inverse ⋙ LiW ⋙ eW₀.functor).obj K')) ⟶ M'⟦(1 : ℤ)⟧)
    (hT : Pretriangulated.Triangle.mk u
      (glueingMap (conjAdj eW₁ eW₀ adjFW) (conjAdj eW₂ eW₀ adjIW)
        (glueingConjugateIso (conjAdj eW₁ eW₀ adjFW) (conjAdj eW₂ eW₀ adjIW)
          (conjAdj eW eW₁ adjJW) (conjAdj eW eW₂ adjF'W)
          (Functor.isoWhiskerLeft eW.inverse (Functor.isoWhiskerRight
            (Functor.isoWhiskerLeft LjW (Functor.isoWhiskerRight eW₁.unitIso.symm LfW ≪≫
                Functor.leftUnitor LfW) ≪≫
              σW₁ ≪≫ σW₂ ≪≫ σW₃.symm ≪≫
              Functor.isoWhiskerLeft Lf'W ((Functor.leftUnitor LiW).symm ≪≫
                Functor.isoWhiskerRight eW₂.unitIso LiW))
            eW₀.functor))) M K' α.hom) v ∈ distTriang 𝒲') :
    IsIso (((conjAdj eW eW₁ adjJW).homEquiv _ _).symm (u ≫ biprod.fst)) ∧
      IsIso (((conjAdj eW eW₂ adjF'W).homEquiv _ _).symm (u ≫ biprod.snd)) := by
  let θj' := conjSquareTarget eW eW₁ (TwoSquare.mk _ _ _ _ θj.hom)
  let θf'' := conjSquareTarget eW₁ eW₀ (TwoSquare.mk _ _ _ _ θf.hom)
  let θf₂ := conjSquareTarget eW eW₂ (TwoSquare.mk _ _ _ _ θf'.hom)
  let θi' := conjSquareTargetIso eW₂ eW₀ θi
  have : ∀ N, IsIso (θj'.app N) := fun N ↦ isIso_conjSquareTarget_app _ _ _ N
  have : ∀ N, IsIso (θf₂.app N) := fun N ↦ isIso_conjSquareTarget_app _ _ _ N
  have : ∀ N, IsIso (θf''.app N) := fun N ↦ isIso_conjSquareTarget_app _ _ _ N
  have mj : ∀ N, IsIso ((mateEquiv adjJ (conjAdj eW eW₁ adjJW) θj').app N) := fun N ↦
    haveI := hj N
    isIso_mateEquiv_conjAdj_conjSquareTarget_app eW eW₁ adjJ adjJW θj N
  have mf' : ∀ N, IsIso ((mateEquiv adjF' (conjAdj eW eW₂ adjF'W) θf₂).app N) := fun N ↦
    haveI := hf' N
    isIso_mateEquiv_conjAdj_conjSquareTarget_app eW eW₂ adjF' adjF'W θf' N
  have mf : ∀ N, IsIso ((mateEquiv adjF (conjAdj eW₁ eW₀ adjFW) θf'').app N) := fun N ↦
    haveI := hf N
    isIso_mateEquiv_conjAdj_conjSquareTarget_app eW₁ eW₀ adjF adjFW θf N
  let σWm := Functor.isoWhiskerLeft eW.inverse (Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft LjW (Functor.isoWhiskerRight eW₁.unitIso.symm LfW ≪≫
        Functor.leftUnitor LfW) ≪≫
      σW₁ ≪≫ σW₂ ≪≫ σW₃.symm ≪≫
      Functor.isoWhiskerLeft Lf'W ((Functor.leftUnitor LiW).symm ≪≫
        Functor.isoWhiskerRight eW₂.unitIso LiW))
    eW₀.functor)
  have h' : ∀ N, (eW₁.inverse ⋙ LfW ⋙ eW₀.functor).map (θj'.app N) ≫ θf''.app (Lj.obj N) ≫
      (Φ₀ ⋙ eW₀.functor).map (σ.hom.app N) =
        σWm.hom.app ((Φ ⋙ eW.functor).obj N) ≫
          (eW₂.inverse ⋙ LiW ⋙ eW₀.functor).map (θf₂.app N) ≫ θi'.hom.app (Lf'.obj N) := by
    intro N
    rw [isoWhiskerLeft_isoWhiskerRight_hom_app]
    exact conjSquareTarget_cube eW eW₁ eW₂ eW₀ (TwoSquare.mk _ _ _ _ θj.hom)
      (TwoSquare.mk _ _ _ _ θf.hom) (TwoSquare.mk _ _ _ _ θf'.hom) (TwoSquare.mk _ _ _ _ θi.hom)
      (TwoSquare.mk _ _ _ _ σ.hom) (TwoSquare.mk _ _ _ _ (σW₁ ≪≫ σW₂ ≪≫ σW₃.symm).hom) h N
  let hΨ₀ : (Φ₀ ⋙ eW₀.functor).FullyFaithful := hΦ₀.comp eW₀.fullyFaithfulFunctor
  let αW : (eW₁.inverse ⋙ LfW ⋙ eW₀.functor).obj (eW₁.functor.obj (Φ₁.obj m)) ≅
      (eW₂.inverse ⋙ LiW ⋙ eW₀.functor).obj (eW₂.functor.obj (Φ₂.obj k)) :=
    (eW₁.inverse ⋙ LfW ⋙ eW₀.functor).mapIso eM ≪≫ α ≪≫
      (eW₂.inverse ⋙ LiW ⋙ eW₀.functor).mapIso eK.symm
  let αr : Lf.obj m ≅ Li.obj k :=
    hΨ₀.preimageIso ((asIso (θf''.app m)).symm ≪≫ αW ≪≫ θi'.app k)
  have hαr : θf''.app m ≫ (Φ₀ ⋙ eW₀.functor).map αr.hom ≫ θi'.inv.app k = αW.hom := by
    simp only [αr, Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage,
      Iso.trans_hom, Iso.symm_hom, asIso_inv, Iso.app_hom, Category.assoc, Iso.hom_inv_id_app,
      IsIso.hom_inv_id_assoc]
    exact Category.comp_id _
  obtain ⟨h₁, h₂⟩ := map_glueingMap_comp_mate adjJ adjF' adjF adjI (conjAdj eW eW₁ adjJW)
    (conjAdj eW eW₂ adjF'W) (conjAdj eW₁ eW₀ adjFW) (conjAdj eW₂ eW₀ adjIW) σ σWm θj' θf''
    θf₂ θi' h' m k αr.hom
  have := mj m
  have := mf' k
  have := mj (Rf.obj (Li.obj k))
  have := mf (Li.obj k)
  refine isIso_homEquiv_symm_of_iso_triple (conjAdj eW eW₁ adjJW) (conjAdj eW eW₂ adjF'W)
    (conjAdj eW₁ eW₀ adjFW) (conjAdj eW₂ eW₀ adjIW) _ eM eK _ α.hom ?_
    (fun u v hT ↦ isIso_homEquiv_symm_of_transport adjJ adjF' (conjAdj eW eW₁ adjJW)
      (conjAdj eW eW₂ adjF'W) θj' θf₂ (glueingMap adjF adjI
        (glueingConjugateIso adjF adjI adjJ adjF' σ) m k αr.hom) _ _ h₁ h₂ (hR αr) u v hT)
    u v hT
  rw [hαr]
  simp [αW]

end TransportModels

end MilnorPatching

end
