module

import StacksFrontier.CategoryTheory.Localization.RightFraction.Equality
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

public import StacksFrontier.CategoryTheory.Filtered.Cofiltered
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Morphisms of `S⁻¹𝒞` as a colimit over `S/X` (Stacks 05Q4)

Let `W` be a right multiplicative system on a category `C` and let `X` be an object of
`C`. Stacks 05Q4 concerns the category `S/X` whose objects are the morphisms
`s : X' ⟶ X` lying in `W` and whose morphisms `s ⟶ t` are the morphisms `a : X' ⟶ X''`
of `C` with `a ≫ t = s`. This is Mathlib's `W.Over ⊤ X`: the subcategory of `Over X`
whose objects are the `W`-morphisms to `X`, with no condition on the morphisms. Two
claims are made:

* `S/X` is cofiltered in the sense of Stacks 04AZ, and
* for every object `Y` the morphisms `X ⟶ Y` of the localization `W⁻¹C` are the colimit
  of the sets `Mor_C(X', Y)` over `(s : X' ⟶ X) ∈ (S/X)ᵒᵖ`.

The first claim is `isCofiltered_over`. Stacks 04AZ is a condition on a *diagram*, so
for the index category `S/X` it is applied to the identity diagram; the two nontrivial
conditions are then exactly the right Ore condition (a lower bound for two objects) and
right cancellability (equalizing two parallel morphisms). Both conditions for `𝟭 (S/X)`
are literally the conditions of Mathlib's `IsCofiltered (S/X)`, by
`Functor.isCofiltered_id_iff`, so the two notions of cofilteredness agree here; the
Mathlib form is recorded as an instance.

The second claim is `isColimitOverHomCocone`. Being a colimit is *data*, so it is a
`def`: the tautological cocone `overHomCocone`, whose leg at `(s : X' ⟶ X)` sends
`f : X' ⟶ Y` to the right fraction `f s⁻¹`, is exhibited as a colimit cocone. Its legs
are jointly surjective by Stacks 04VI in its one-morphism form — every morphism of
`W⁻¹C` is a right fraction, `Localization.exists_rightFraction` — which is what defines
the map out of the cocone point, and they identify exactly the right fractions related
by `RightFractionRel` by Stacks 04VJ (`map_eq_iff_rightFractionRel`), which is what makes that map
  well
defined: the relation supplies a common denominator, i.e. an object of `S/X` dominating
the two given ones, and the cocone relations at it do the rest.

The diagram takes values in `Type v`, the universe of the morphisms of `C`, so the
localization `L : C ⥤ D` is taken with `[Category.{v} D]`, i.e. with its morphisms in
that same universe. This holds for `W.Q'` under `MorphismProperty.HasLocalization.{v} W`,
in particular (by `HasLocalization.standard`) whenever `C` is a category in `Type v`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

namespace CategoryTheory.MorphismProperty

universe v u u₂

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  [W.HasRightCalculusOfFractions]

/-- **Stacks 05Q4**, first claim: for a right multiplicative system `W` on `C` and an
object `X` of `C`, the category `S/X = W.Over ⊤ X` of `W`-morphisms to `X` is cofiltered
in the sense of Stacks 04AZ, i.e. its identity diagram is a cofiltered diagram. -/
@[stacks 05Q4]
theorem isCofiltered_over (X : C) : (𝟭 (W.Over ⊤ X)).IsCofiltered where
  nonempty := ⟨Over.mk ⊤ (𝟙 X) (W.id_mem X)⟩
  cone_objs A B := by
    obtain ⟨ψ, hψ⟩ := (LeftFraction.mk B.hom A.hom A.prop).exists_rightFraction
    exact ⟨Over.mk ⊤ (ψ.s ≫ B.hom) (W.comp_mem _ _ ψ.hs B.prop),
      Over.homMk ψ.f hψ.symm, Over.homMk ψ.s rfl, trivial⟩
  cone_maps {A B} a b := by
    obtain ⟨Z, t, ht, hab⟩ := HasRightCalculusOfFractions.ext a.left b.left B.hom B.prop
      (by rw [Over.w a, Over.w b])
    exact ⟨Over.mk ⊤ (t ≫ A.hom) (W.comp_mem _ _ ht A.prop), Over.homMk t rfl,
      Over.Hom.ext hab⟩

/-- `S/X` is cofiltered in the sense of Mathlib, which for an index category is the same
condition as Stacks 04AZ for its identity diagram. -/
instance (X : C) : IsCofiltered (W.Over ⊤ X) :=
  (Functor.isCofiltered_id_iff _).1 (isCofiltered_over W X)

/-- The diagram `(S/X)ᵒᵖ ⥤ Type v` of Stacks 05Q4: it sends an object `s : X' ⟶ X` of
`S/X` to the set `Mor_C(X', Y)`, and a morphism `a : s ⟶ t` of `S/X` to precomposition
with `a`, viewed as a map `Mor_C(X'', Y) ⟶ Mor_C(X', Y)`. -/
def overHomDiagram (X Y : C) : (W.Over ⊤ X)ᵒᵖ ⥤ Type v :=
  (Over.forget W ⊤ X ⋙ CategoryTheory.Over.forget X).op ⋙ yoneda.obj Y

variable {D : Type u₂} [Category.{v} D] (L : C ⥤ D) [L.IsLocalization W]

/-- Precomposing the numerator of a right fraction with a morphism `α : s ⟶ t` of `S/X`
does not change the morphism of `W⁻¹C` it defines: `(α ≫ f) s⁻¹ = f t⁻¹`. -/
private lemma map_rightFraction_comp {X Y : C} (A B : W.Over ⊤ X) (α : A ⟶ B)
    (f : B.left ⟶ Y) :
    (RightFraction.mk (X := X) (Y := Y) A.hom A.prop (α.left ≫ f)).map L
        (Localization.inverts L W) =
      (RightFraction.mk (X := X) (Y := Y) B.hom B.prop f).map L (Localization.inverts L W) :=
  (map_eq_iff_rightFractionRel L _ _).2
    ⟨A.left, 𝟙 A.left, α.left, by simp [Over.w α], by simp, by simpa using A.prop⟩

/-- The cocone on `overHomDiagram W X Y` with vertex `Mor_{W⁻¹C}(X, Y)` whose leg at an
object `s : X' ⟶ X` of `S/X` sends `f : X' ⟶ Y` to the right fraction `f s⁻¹`. -/
noncomputable def overHomCocone (X Y : C) : Cocone (W.overHomDiagram X Y) where
  pt := L.obj X ⟶ L.obj Y
  ι :=
    { app := fun A => ↾fun f =>
        (RightFraction.mk (W := W) (X := X) (Y := Y) A.unop.hom A.unop.prop f).map L
          (Localization.inverts L W)
      naturality := fun A B a => by
        ext f
        exact map_rightFraction_comp W L B.unop A.unop a.unop f }

/-- The leg of `overHomCocone` at `s : X' ⟶ X` sends `f : X' ⟶ Y` to `f s⁻¹`. -/
@[simp]
lemma overHomCocone_ι_app_apply (X Y : C) (A : (W.Over ⊤ X)ᵒᵖ) (f : A.unop.left ⟶ Y) :
    (W.overHomCocone L X Y).ι.app A f =
      (RightFraction.mk (W := W) (X := X) (Y := Y) A.unop.hom A.unop.prop f).map L
        (Localization.inverts L W) :=
  rfl

omit [W.HasRightCalculusOfFractions] in
/-- The legs of any cocone on `overHomDiagram W X Y` identify two right fractions that
are `RightFractionRel`-related: the relation provides a third object of `S/X` mapping to
the two given ones, and the two cocone relations at it are compared using that the
relation also equalizes the numerators. -/
private lemma cocone_app_eq_of_rel {X Y : C} (c : Cocone (W.overHomDiagram X Y))
    (A B : W.Over ⊤ X) (f : A.left ⟶ Y) (g : B.left ⟶ Y)
    (h : RightFractionRel (RightFraction.mk (X := X) (Y := Y) A.hom A.prop f)
      (RightFraction.mk (X := X) (Y := Y) B.hom B.prop g)) :
    c.ι.app (Opposite.op A) f = c.ι.app (Opposite.op B) g := by
  obtain ⟨Z, t₁, t₂, hs, hf, hW⟩ := h
  have h₁ := types_congr_hom
    (c.w (Over.homMk (A := Over.mk ⊤ (t₁ ≫ A.hom) hW) (B := A) t₁ rfl).op) f
  have h₂ := types_congr_hom
    (c.w (Over.homMk (A := Over.mk ⊤ (t₁ ≫ A.hom) hW) (B := B) t₂ hs.symm).op) g
  rw [← h₁, ← h₂]
  exact TypeCat.congr_arg _ hf

/-- **Stacks 05Q4**, second claim: for a right multiplicative system `W` on `C`, a
localization functor `L : C ⥤ D` of `C` at `W` and objects `X`, `Y` of `C`, the
morphisms `L.obj X ⟶ L.obj Y` of `W⁻¹C` are the colimit
`colim_{(s : X' ⟶ X) ∈ (S/X)ᵒᵖ} Mor_C(X', Y)`, in the sense that the tautological cocone
`overHomCocone`, whose leg at `s` sends `f` to the right fraction `f s⁻¹`, is a colimit
cocone. The index category `(S/X)ᵒᵖ` is filtered by `isCofiltered_over`, so this
exhibits the morphisms of `W⁻¹C` as a filtered colimit of morphisms of `C`. -/
@[stacks 05Q4, sga "4½ Etat_0 2.3.2", sga "5 V 2.3.3" "Hom-set clause"]
noncomputable def isColimitOverHomCocone (X Y : C) : IsColimit (W.overHomCocone L X Y) where
  desc c := ↾fun g =>
    c.ι.app (Opposite.op (Over.mk ⊤ (Localization.exists_rightFraction L W g).choose.s
      (Localization.exists_rightFraction L W g).choose.hs))
      (Localization.exists_rightFraction L W g).choose.f
  fac c A := by
    ext f
    refine cocone_app_eq_of_rel W c _ A.unop _ f ((map_eq_iff_rightFractionRel L _ _).1 ?_)
    exact ((Localization.exists_rightFraction L W _).choose_spec).symm
  uniq c m hm := by
    ext g
    refine (TypeCat.congr_arg m (Localization.exists_rightFraction L W g).choose_spec).trans ?_
    exact types_congr_hom (hm (Opposite.op (Over.mk ⊤
      (Localization.exists_rightFraction L W g).choose.s
      (Localization.exists_rightFraction L W g).choose.hs)))
      (Localization.exists_rightFraction L W g).choose.f

end CategoryTheory.MorphismProperty
