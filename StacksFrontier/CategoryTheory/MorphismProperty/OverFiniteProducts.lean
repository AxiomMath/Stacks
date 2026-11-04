module

public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Structure morphisms of finite products in an over category

Let `P` be a class of morphisms of a category `C` which is stable under base change and under
composition and which contains every isomorphism followed by a member. In the over category
`C/U`, the binary product of `Y` and `Z` is the fibre product `Y ×_U Z`, whose structure
morphism to `U` is the base change of `Z → U` along `Y → U` followed by `Y → U`. So if the
structure morphisms of `Y` and `Z` lie in `P`, so does that of `Y × Z`, and by induction the
same holds for a product of finitely many objects.

This is the form in which the iterated fibre products `U_{i_0} ×_U … ×_U U_{i_n}` of a family
of morphisms lying in `P` — the objects of a Čech complex — are seen to lie over `U` by a
morphism in `P`, for `P` the flat morphisms locally of finite presentation.

## Main results

* `CategoryTheory.Over.prop_hom_of_isLimit_binaryFan`: the binary case, for any limit binary
  fan.
* `CategoryTheory.Over.prop_hom_of_isLimit_fan_fin`: the case of a nonempty finite family
  indexed by `Fin (n + 1)`, for any limit fan.
* `CategoryTheory.Over.prop_hom_piObj_fin`: the same for the chosen product.

## Implementation notes

The three closure properties are explicit hypotheses rather than the classes
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange` and
`CategoryTheory.MorphismProperty.IsStableUnderComposition`, so that the statements apply
directly to a class of morphisms defined through a functor to another category, such as the
flat morphisms of a size-bounded category of schemes, without first proving that the functor
preserves pullbacks as an instance.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Over

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] (P : ∀ {X Y : C}, (X ⟶ Y) → Prop)
  (hbc : ∀ {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ W) (k : Z ⟶ W),
    IsPullback f g h k → P k → P f)
  (hcomp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), P f → P g → P (f ≫ g))
  (hiso : ∀ {X Y Z : C} (e : X ≅ Y) (f : Y ⟶ Z), P f → P (e.hom ≫ f))

include hbc hcomp in
/-- **The structure morphism of a binary product in an over category.** For a limit binary
fan `c` on `Y` and `Z` in `C/U`, the structure morphism of its point is the base change of
`Z → U` along `Y → U` followed by `Y → U`, so it lies in `P` when those of `Y` and `Z` do. -/
theorem prop_hom_of_isLimit_binaryFan {U : C} {Y Z : Over U} (c : BinaryFan Y Z)
    (hc : IsLimit c) (hY : P Y.hom) (hZ : P Z.hom) : P c.pt.hom := by
  have hw : c.fst.left ≫ Y.hom = c.pt.hom := Over.w c.fst
  rw [← hw]
  exact hcomp _ _ (hbc _ _ _ _ (Over.isPullback_of_binaryFan_isLimit c hc) hZ) hY

/-- The structure morphism of an object isomorphic over `U` to one lying in `P` lies in `P`. -/
private theorem prop_hom_of_iso
    (hiso : ∀ {X Y Z : C} (e : X ≅ Y) (f : Y ⟶ Z), P f → P (e.hom ≫ f))
    {U : C} {X Y : Over U} (e : X ≅ Y) (h : P Y.hom) : P X.hom := by
  rw [← Over.w e.hom]
  exact hiso ((Over.forget U).mapIso e) _ h

include hiso in
/-- A limit fan whose structure morphism lies in `P` transfers that property to any other limit
fan on the same family. -/
theorem prop_hom_of_isLimit_fan_of_isLimit {U : C} {J : Type*} {A : J → Over U}
    {c c' : Fan A} (hc : IsLimit c) (hc' : IsLimit c') (h : P c'.pt.hom) : P c.pt.hom := by
  exact prop_hom_of_iso P hiso (hc.conePointUniqueUpToIso hc') h

variable [HasPullbacks C]

include hbc hcomp hiso in
/-- **The structure morphism of a finite product in an over category.** For a limit fan `c`
on a family `A : Fin (n + 1) → C/U` all of whose structure morphisms lie in `P`, the structure
morphism of the point of `c` lies in `P`. -/
theorem prop_hom_of_isLimit_fan_fin {U : C} :
    ∀ (n : ℕ) (A : Fin (n + 1) → Over U) (c : Fan A), IsLimit c →
      (∀ a, P (A a).hom) → P c.pt.hom := by
  intro n
  induction n with
  | zero =>
    intro A c hc hA
    have : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
    have : HasProduct A := hasProduct_unique A
    exact prop_hom_of_iso P hiso
      (hc.conePointUniqueUpToIso (productIsProduct A) ≪≫ productUniqueIso A) (hA _)
  | succ n ih =>
    intro A c hc hA
    have : HasBinaryProducts (Over U) := Over.ConstructProducts.over_binaryProduct_of_pullback
    have : HasTerminal (Over U) := Over.mkIdTerminal.hasTerminal
    have : HasFiniteProducts (Over U) := hasFiniteProducts_of_has_binary_and_terminal
    have hR := productIsProduct fun i : Fin (n + 1) => A i.succ
    exact prop_hom_of_isLimit_fan_of_isLimit P hiso hc
      (extendFanIsLimit A hR (prodIsProd (A 0) _))
      (prop_hom_of_isLimit_binaryFan P hbc hcomp _ (prodIsProd (A 0) _) (hA 0)
        (ih _ _ hR fun a => hA a.succ))

include hbc hcomp hiso in
/-- **The structure morphism of a chosen finite product in an over category** lies in `P` as
soon as those of the factors do. -/
theorem prop_hom_piObj_fin {U : C} (n : ℕ) (A : Fin (n + 1) → Over U) [HasProduct A]
    (hA : ∀ a, P (A a).hom) : P (∏ᶜ A).hom :=
  prop_hom_of_isLimit_fan_fin P hbc hcomp hiso n A _ (productIsProduct A) hA

end CategoryTheory.Over

end
