module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Transposing a map into a pushforward around a square of adjunctions

Given a square of adjunctions `Lj ⊣ Rj`, `Lv ⊣ Rv`, `Lf ⊣ Rf`, `Lw ⊣ Rw` with a comparison
`γL : Lf ⋙ Lw ⟶ Lj ⋙ Lv` of the two composite left adjoints, a map `m : H ⟶ Rv B` gives, through
the conjugate `γR` of `γL`, a map `Lf (Rj H) ⟶ Rw B`.  This file computes the restriction of that
map along `Lw`: it is `γL` followed by the counit of `Lj ⊣ Rj` and the transpose of `m`.

In the formal glueing square of Stacks 0AEV (`j : U → X`, `f : Y → X`, `j' : V → Y`,
`f|_V : V → U`) this says that the map `f^*j_*ℋ ⟶ j'_*𝒢|_V` attached to a glueing triple
`(ℋ, 𝒢, φ)` restricts over `V` to `φ` up to isomorphisms, which is how the stalkwise proof of
Stacks 0AF0 sees that it becomes invertible after inverting the generators of the ideal of `Z`.

## Main results

* `CategoryTheory.Adjunction.squareTranspose`: the map around the square.
* `CategoryTheory.Adjunction.map_homEquiv_symm_comp_counit` and
  `CategoryTheory.Adjunction.map_squareTranspose_comp_counit`: the computation.
* `CategoryTheory.Adjunction.isIso_map_squareTranspose`: invertibility after restriction.
* `CategoryTheory.Adjunction.map_unit_comp_squareTranspose`: for the triple of an object, the
  square transpose after the unit of `Lj ⊣ Rj` is the unit of `Lw ⊣ Rw` (the inner square of the
  bootstrap diagram in the proof of Stacks 0AF0, at the level of sheaves).

## References

* [Stacks Project, Tag 0AF0](https://stacks.math.columbia.edu/tag/0AF0)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Adjunction

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D₁ : Type u₂} [Category.{v₂} D₁]
  {D₂ : Type u₃} [Category.{v₃} D₂] {E : Type u₄} [Category.{v₄} E]
  {Lj : C ⥤ D₁} {Rj : D₁ ⥤ C} (adjj : Lj ⊣ Rj)
  {Lv : D₁ ⥤ D₂} {Rv : D₂ ⥤ D₁} (adjv : Lv ⊣ Rv)
  {Lf : C ⥤ E} {Rf : E ⥤ C} (adjf : Lf ⊣ Rf)
  {Lw : E ⥤ D₂} {Rw : D₂ ⥤ E} (adjw : Lw ⊣ Rw)

/-- **The transpose around a square, after restriction.**  Let `γL : Lf ⋙ Lw ⟶ Lj ⋙ Lv` and let
`γR` be its conjugate.  For `m : H ⟶ Rv B`, the transpose under `Lf ⊣ Rf` of `Rj m ≫ γR_B`,
followed by `Lw` and the counit of `Lw ⊣ Rw`, is `γL ≫ Lv(ε_j H)` followed by the transpose of `m`
under `Lv ⊣ Rv`. -/
theorem map_homEquiv_symm_comp_counit (γL : Lf ⋙ Lw ⟶ Lj ⋙ Lv) (H : D₁) {B : D₂}
    (m : H ⟶ Rv.obj B) :
    Lw.map ((adjf.homEquiv _ _).symm
        (Rj.map m ≫ (conjugateEquiv (adjj.comp adjv) (adjf.comp adjw) γL).app B)) ≫
        adjw.counit.app B =
      γL.app (Rj.obj H) ≫ Lv.map (adjj.counit.app H) ≫ Lv.map m ≫ adjv.counit.app B := by
  have h1 := conjugateEquiv_counit (adjj.comp adjv) (adjf.comp adjw) γL B
  simp only [comp_counit_app, Functor.comp_map] at h1
  have hnat := γL.naturality (Rj.map m)
  simp only [Functor.comp_map] at hnat
  have hcounit : Lj.map (Rj.map m) ≫ adjj.counit.app (Rv.obj B) = adjj.counit.app H ≫ m :=
    adjj.counit.naturality m
  rw [homEquiv_counit, Functor.map_comp, Functor.map_comp, Functor.map_comp, Category.assoc,
    Category.assoc, h1, ← Category.assoc]
  change (Lw.map (Lf.map (Rj.map m)) ≫ γL.app (Rj.obj (Rv.obj B))) ≫ _ = _
  rw [hnat, Category.assoc, ← Functor.map_comp_assoc, hcounit, Functor.map_comp_assoc]

/-- The map `Lf (Rj H) ⟶ Rw B` attached to `φ : Lv H ⟶ B` around the square: the transpose under
`Lf ⊣ Rf` of `Rj` of the transpose of `φ`, followed by the conjugate of `γL`. -/
def squareTranspose (γL : Lf ⋙ Lw ⟶ Lj ⋙ Lv) (H : D₁) {B : D₂} (φ : Lv.obj H ⟶ B) :
    Lf.obj (Rj.obj H) ⟶ Rw.obj B :=
  (adjf.homEquiv _ _).symm
    (Rj.map (adjv.homEquiv _ _ φ) ≫ (conjugateEquiv (adjj.comp adjv) (adjf.comp adjw) γL).app B)

/-- Restricted along `Lw`, the square transpose of `φ` is `γL ≫ Lv(ε_j H) ≫ φ`. -/
theorem map_squareTranspose_comp_counit (γL : Lf ⋙ Lw ⟶ Lj ⋙ Lv) (H : D₁) {B : D₂}
    (φ : Lv.obj H ⟶ B) :
    Lw.map (squareTranspose adjj adjv adjf adjw γL H φ) ≫ adjw.counit.app B =
      γL.app (Rj.obj H) ≫ Lv.map (adjj.counit.app H) ≫ φ := by
  rw [squareTranspose, map_homEquiv_symm_comp_counit]
  congr 2
  exact ((adjv.homEquiv_counit _ _ _).symm.trans (Equiv.symm_apply_apply _ _))

/-- **The square transpose is invertible after restriction along `Lw`** as soon as `φ`, `γL` and
the two counits involved are. -/
theorem isIso_map_squareTranspose (γL : Lf ⋙ Lw ⟶ Lj ⋙ Lv) [IsIso γL] (H : D₁) {B : D₂}
    (φ : Lv.obj H ⟶ B) [IsIso φ] [IsIso (adjj.counit.app H)] [IsIso (adjw.counit.app B)] :
    IsIso (Lw.map (squareTranspose adjj adjv adjf adjw γL H φ)) := by
  have : IsIso (Lw.map (squareTranspose adjj adjv adjf adjw γL H φ) ≫ adjw.counit.app B) := by
    rw [map_squareTranspose_comp_counit]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (adjw.counit.app B)

/-- **The inner square.**  For the triple `(Lj X, Lf X, δ_X)` attached to an object `X`, where
`δ_X : Lv (Lj X) ⟶ Lw (Lf X)` is inverse to `γL_X`, the square transpose precomposed with
`Lf` of the unit of `Lj ⊣ Rj` is the unit of `Lw ⊣ Rw` at `Lf X`. -/
theorem map_unit_comp_squareTranspose (γL : Lf ⋙ Lw ⟶ Lj ⋙ Lv) (X : C)
    (δ : Lv.obj (Lj.obj X) ⟶ Lw.obj (Lf.obj X)) (hδ : γL.app X ≫ δ = 𝟙 _) :
    Lf.map (adjj.unit.app X) ≫ squareTranspose adjj adjv adjf adjw γL (Lj.obj X) δ =
      adjw.unit.app (Lf.obj X) := by
  apply (adjw.homEquiv _ _).symm.injective
  rw [homEquiv_counit, homEquiv_counit, Functor.map_comp, Category.assoc,
    map_squareTranspose_comp_counit]
  rw [show Lw.map (adjw.unit.app (Lf.obj X)) ≫ adjw.counit.app (Lw.obj (Lf.obj X)) = 𝟙 _ from
    adjw.left_triangle_components _]
  have hnat : Lw.map (Lf.map (adjj.unit.app X)) ≫ γL.app (Rj.obj (Lj.obj X)) =
      γL.app X ≫ Lv.map (Lj.map (adjj.unit.app X)) := γL.naturality (adjj.unit.app X)
  rw [← Category.assoc, hnat, Category.assoc, ← Functor.map_comp_assoc,
    adjj.left_triangle_components, Functor.map_id, Category.id_comp, hδ]
  rfl

end CategoryTheory.Adjunction

end
