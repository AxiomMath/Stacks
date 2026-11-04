module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.DiagonalBaseChange

/-!
# A 2-fibre product over a base as a pullback along the relative diagonal (Stacks 04Z1)

We work in the `(2,1)`-category of categories and use the explicit 2-fibre product of
Example 003R, which is Mathlib's `CategoryTheory.Limits.CategoricalPullback P Q`: its objects are
triples `(x, y, φ)` with `φ : P x ≅ Q y` an isomorphism, and its morphisms are pairs of morphisms
making the evident square commute. The relative diagonal `Δ_{C/D} : C ⥤ C ×_D C` of a functor
`H : C ⥤ D` is `CategoricalPullback.relativeDiagonal H`, sending `c` to `(c, c, 𝟙)`.

Fix `F : A ⥤ C`, `G : B ⥤ C` and `H : C ⥤ D`. The square
```
  A ×_C B  --Θ-->  A ×_D B
    |                 |
    π                 ρ
    |                 |
    v                 v
    C  ----Δ_{C/D}--> C ×_D C
```
is a 2-fibre product diagram, where `Θ = mapBase : (a, b, f) ↦ (a, b, H f)`,
`π = toBase = π₁ ⋙ F : (a, b, f) ↦ F a`, and
`ρ = toRelativeDiagonalTarget : (a, b, g) ↦ (F a, G b, g)`. The square 2-commutes via the natural
isomorphism `relativeDiagonalSquareIso` whose component at `(a, b, f)` is `(𝟙, f⁻¹)`.

Being a 2-fibre product diagram means that the induced functor `toRelativeDiagonalPullback` from
the top-left corner into the explicit 2-fibre product of the cospan `ρ, Δ_{C/D}` is an equivalence
of categories. On objects it sends `(a, b, f)` to `((a, b, H f), F a, (𝟙, f⁻¹))`.

## Main definitions

* `mapBase`: the functor `A ×_C B ⥤ A ×_D B` sending `(a, b, f)` to `(a, b, H f)`.
* `toBase`: the functor `A ×_C B ⥤ C` sending `(a, b, f)` to `F a`.
* `toRelativeDiagonalTarget`: the functor `A ×_D B ⥤ C ×_D C` sending `(a, b, g)` to
  `(F a, G b, g)`.
* `relativeDiagonalSquareIso`: the natural isomorphism by which the square 2-commutes.
* `toRelativeDiagonalPullback`: the induced functor `A ×_C B ⥤ (A ×_D B) ×_{C ×_D C} C`.

## Main results

* `isEquivalence_toRelativeDiagonalPullback`: the induced functor
  `toRelativeDiagonalPullback` is an equivalence of categories.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Limits.CategoricalPullback

variable {A : Type*} [Category A] {B : Type*} [Category B]
variable {C : Type*} [Category C] {D : Type*} [Category D]
variable (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)

/-- The top map `Θ : A ×_C B ⥤ A ×_D B` of the square, sending `(a, b, f)` to `(a, b, H f)` and a
morphism `(x, y)` to `(x, y)`. -/
@[simps]
def mapBase : CategoricalPullback F G ⥤ CategoricalPullback (F ⋙ H) (G ⋙ H) where
  obj M := { fst := M.fst, snd := M.snd, iso := H.mapIso M.iso }
  map {M N} φ :=
    { fst := φ.fst
      snd := φ.snd
      w := by simp [← Functor.map_comp] }

/-- The left map `π : A ×_C B ⥤ C` of the square, namely `π₁ ⋙ F`, sending `(a, b, f)` to
`F a`. -/
def toBase : CategoricalPullback F G ⥤ C := π₁ F G ⋙ F

/-- The functor `toBase F G` sends `M` to `F.obj M.fst`. -/
@[simp] lemma toBase_obj (M : CategoricalPullback F G) : (toBase F G).obj M = F.obj M.fst := rfl

/-- The functor `toBase F G` sends a morphism `φ` to `F.map φ.fst`. -/
@[simp] lemma toBase_map {M N : CategoricalPullback F G} (φ : M ⟶ N) :
    (toBase F G).map φ = F.map φ.fst := rfl

/-- The right map `ρ : A ×_D B ⥤ C ×_D C` of the square, sending `(a, b, g)` to `(F a, G b, g)`
and a morphism `(x, y)` to `(F x, G y)`. -/
@[simps]
def toRelativeDiagonalTarget :
    CategoricalPullback (F ⋙ H) (G ⋙ H) ⥤ CategoricalPullback H H where
  obj M := { fst := F.obj M.fst, snd := G.obj M.snd, iso := M.iso }
  map {M N} φ := { fst := F.map φ.fst, snd := G.map φ.snd, w := φ.w }

/-- **Stacks 04Z1.** The natural isomorphism `σ : Θ ⋙ ρ ≅ π ⋙ Δ_{C/D}` witnessing that the
square 2-commutes; its component at `(a, b, f)` is `(𝟙_{F a}, f⁻¹)`. -/
@[stacks 04Z1, simps!]
def relativeDiagonalSquareIso :
    (mapBase F G H ⋙ toRelativeDiagonalTarget F G H) ≅ (toBase F G ⋙ relativeDiagonal H) :=
  NatIso.ofComponents
    (fun M => mkIso (F := H) (G := H) (Iso.refl (F.obj M.fst)) M.iso.symm (by
      simp [mapBase, toRelativeDiagonalTarget, toBase, ← Functor.map_comp]))
    (by
      intro M N φ
      refine hom_ext ?_ ?_
      · simp [mapBase, toRelativeDiagonalTarget, toBase]
      · simp only [Functor.comp_map, comp_snd, mkIso_hom_snd, Iso.symm_hom, mapBase_map_snd,
          toRelativeDiagonalTarget_map_snd, relativeDiagonal_map_snd, toBase_map]
        rw [Iso.comp_inv_eq, Category.assoc, φ.w, ← Category.assoc, Iso.inv_hom_id,
          Category.id_comp])

/-- **Stacks 04Z1.** The functor `A ×_C B ⥤ (A ×_D B) ×_{C ×_D C} C` induced by
`(Θ, π, σ)` into the explicit 2-fibre product of the cospan
`A ×_D B --ρ--> C ×_D C <--Δ_{C/D}-- C`. On objects it sends `(a, b, f)` to
`((a, b, H f), F a, (𝟙_{F a}, f⁻¹))`, and a morphism `(x, y)` to `((x, y), F x)`. -/
@[stacks 04Z1, simps]
def toRelativeDiagonalPullback :
    CategoricalPullback F G ⥤
      CategoricalPullback (toRelativeDiagonalTarget F G H) (relativeDiagonal H) where
  obj M :=
    { fst := (mapBase F G H).obj M
      snd := (toBase F G).obj M
      iso := (relativeDiagonalSquareIso F G H).app M }
  map {M N} φ :=
    { fst := (mapBase F G H).map φ
      snd := (toBase F G).map φ
      w := (relativeDiagonalSquareIso F G H).hom.naturality φ }

/-- The functor `toRelativeDiagonalPullback` is faithful. -/
instance faithful_toRelativeDiagonalPullback :
    (toRelativeDiagonalPullback F G H).Faithful where
  map_injective h :=
    hom_ext (congrArg (fun k => k.fst.fst) h) (congrArg (fun k => k.fst.snd) h)

/-- The functor `toRelativeDiagonalPullback` is full. -/
instance full_toRelativeDiagonalPullback : (toRelativeDiagonalPullback F G H).Full := by
  constructor
  intro M N g
  have hl0 : F.map (X := M.fst) (Y := N.fst) g.fst.fst ≫ 𝟙 (F.obj N.fst)
      = 𝟙 (F.obj M.fst) ≫ g.snd := congrArg Hom.fst g.w
  have hr : G.map (X := M.snd) (Y := N.snd) g.fst.snd ≫ N.iso.inv = M.iso.inv ≫ g.snd :=
    congrArg Hom.snd g.w
  have hl : F.map (X := M.fst) (Y := N.fst) g.fst.fst = g.snd := by simpa using hl0
  refine ⟨{ fst := g.fst.fst, snd := g.fst.snd, w := ?_ }, ?_⟩
  · rw [← hl, Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp] at hr
    exact hr.symm
  · exact hom_ext (hom_ext rfl rfl) hl

/-- The functor `toRelativeDiagonalPullback` is essentially surjective: an object
`((a, b, g), c, (h₁, h₂))` of the target is isomorphic to the image of `(a, b, h₁ ≪≫ h₂.symm)`. -/
instance essSurj_toRelativeDiagonalPullback : (toRelativeDiagonalPullback F G H).EssSurj := by
  constructor
  intro Y
  rw [Functor.essImage]
  set e1 : F.obj Y.fst.fst ≅ Y.snd := (π₁ H H).mapIso Y.iso with he1
  set e2 : G.obj Y.fst.snd ≅ Y.snd := (π₂ H H).mapIso Y.iso with he2
  refine ⟨{ fst := Y.fst.fst, snd := Y.fst.snd, iso := e1 ≪≫ e2.symm }, ⟨?_⟩⟩
  have hw := Y.iso.hom.w
  simp only [toRelativeDiagonalTarget, relativeDiagonal_obj_iso, relativeDiagonal_obj_fst,
    relativeDiagonal_obj_snd, Iso.refl_hom, Category.comp_id] at hw
  have hg : Y.fst.iso.hom = H.map e1.hom ≫ H.map e2.inv := by
    rw [show e1.hom = Y.iso.hom.fst from rfl, hw, Category.assoc, ← Functor.map_comp,
      show (Y.iso.hom.snd : _) = e2.hom from rfl, e2.hom_inv_id]
    simp
  refine mkIso (mkIso (Iso.refl _) (Iso.refl _) ?_) e1 ?_
  · simp only [Functor.comp_obj, Iso.refl_hom, Functor.comp_map, Functor.map_id, hg,
      Category.id_comp, Category.comp_id]
    exact (H.map_comp e1.hom e2.inv).symm
  · apply hom_ext
    · simp only [he1]
      simp only [relativeDiagonal_obj_fst, comp_fst, toRelativeDiagonalTarget_map_fst,
        mkIso_hom_fst, Iso.refl_hom, Functor.map_id, toRelativeDiagonalPullback_obj_iso,
        Iso.app_hom, Functor.mapIso_hom, π₁_map, relativeDiagonal_map,
        relativeDiagonalSquareIso_hom_app_fst]
      rfl
    · simp only [toRelativeDiagonalTarget, toRelativeDiagonalPullback, mapBase, toBase,
        Functor.comp_obj, relativeDiagonalSquareIso, Functor.comp_map, π₁_map,
        mkIso_hom_fst, Iso.refl_hom, Functor.map_id, mkIso_hom_snd, comp_snd, Category.id_comp,
        NatIso.ofComponents.app, he1, he2, Iso.trans_symm, Iso.symm_symm_eq, Functor.mapIso_hom,
        Iso.trans_hom, π₂_map, Iso.symm_hom, Functor.mapIso_inv, Category.assoc,
        relativeDiagonal_map_snd]
      rw [show Y.iso.inv.fst ≫ Y.iso.hom.fst = 𝟙 _ from congrArg Hom.fst Y.iso.inv_hom_id]
      simp

/-- **Stacks 04Z1.** The square above is a 2-fibre product diagram: the induced functor
`A ×_C B ⥤ (A ×_D B) ×_{C ×_D C} C` is an equivalence of categories. -/
@[stacks 04Z1]
theorem isEquivalence_toRelativeDiagonalPullback :
    (toRelativeDiagonalPullback F G H).IsEquivalence :=
  { faithful := faithful_toRelativeDiagonalPullback F G H
    full := full_toRelativeDiagonalPullback F G H
    essSurj := essSurj_toRelativeDiagonalPullback F G H }

end CategoryTheory.Limits.CategoricalPullback
