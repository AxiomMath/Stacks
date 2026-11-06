module

public import Mathlib.CategoryTheory.Sites.Point.Over
import StacksCore.Tactic.EgaSgaAttribute

/-! # Localization and points: a point of `C/U` above a point of `C`

Let `(C, J)` be a site, let `p` be a point of `C` with fibre functor `u = p.fiber`, let `U` be an
object of `C` and let `x ∈ u(U)`.  Stacks 04H2 does two things:

* it constructs a point `q` of the localized site `C/U` whose fibre functor sends
  `(φ : V ⟶ U)` to `{y ∈ u(V) | u(φ)(y) = x}`.  This is Mathlib's
  `CategoryTheory.GrothendieckTopology.Point.over`;
* it shows that `q` lies above `p`, i.e. that the triangle formed by `q`, `p` and the
  localization morphism `j_U : Sh(C/U) ⟶ Sh(C)` commutes: `F_p = (j_U⁻¹F)_q` for every sheaf
  `F` on `C`.  Since `j_U⁻¹` is `GrothendieckTopology.overPullback`, this is `sheafFiberOverIso`
  below.

The proof of the second part is the one the Stacks project gives, in the following form: the
fibre at `q` of the restriction of a presheaf to `C/U` is a colimit indexed by the category of
elements of `q`'s fibre functor, and `overElements` exhibits that indexing category as an
initial subcategory of the category of elements of `u` — it is the over category of `x`, and the
forgetful functor of an over category on a cofiltered category is initial.

## Main results

* `overElements`, `Functor.Initial` instance: the category of elements of the fibre functor of
  `q = p.over x` is initial over the category of elements of the fibre functor of `p`.
* `presheafFiberOverIso`: `F_p = (j_U⁻¹F)_q` for presheaves.
* `sheafFiberOverIso` (Stacks 04H2): `F_p = (j_U⁻¹F)_q` for sheaves, i.e. the triangle
  `q`, `p`, `j_U` of morphisms of topoi commutes.

Tags covered: 04H2.
-/

@[expose] public section

namespace CategoryTheory.GrothendieckTopology.Point

open Limits Opposite

universe w v' v u' u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : Point.{w} J) {X : C} (x : Φ.fiber.obj X)

/-- If `y : Φ.fiber.obj V` lies over `x` along `h : V ⟶ X` and `z : Φ.fiber.obj W` maps to `y`
along `g : W ⟶ V`, then `z` lies over `x` along `g ≫ h`. -/
lemma map_comp_apply_eq {V : C} {h : V ⟶ X} {y : Φ.fiber.obj V} (hy : Φ.fiber.map h y = x)
    {W : C} {z : Φ.fiber.obj W} (g : W ⟶ V) (hg : Φ.fiber.map g z = y) :
    Φ.fiber.map (g ≫ h) z = x := by simp [hg, hy]

variable [LocallySmall.{w} C]

/-- The category of elements of the fibre functor of `Φ.over x` is the over category of
`x`, viewed as an object of the category of elements of `Φ.fiber`: an element of the fibre of
`Φ.over x` at `(V ⟶ X)` is an element `y` of `Φ.fiber.obj V` lying over `x`.  This is the
resulting functor to the category of elements of `Φ.fiber`. -/
def overElements : (Φ.over x).fiber.Elements ⥤ Φ.fiber.Elements where
  obj u := Φ.fiber.elementsMk u.1.left u.2.val
  map f := Functor.Elements.homMk f.hom.left (congrArg Subtype.val f.map_val)

/-- `overElements` is compatible with the projections to `C`: it covers the forgetful functor
`Over X ⥤ C`. -/
lemma overElements_comp_π :
    overElements Φ x ⋙ Functor.Elements.π Φ.fiber =
      Functor.Elements.π (Φ.over x).fiber ⋙ Over.forget X :=
  rfl

/-- `overElements Φ x` is an initial functor, so a colimit over the elements of `Φ.fiber`
restricts to the same colimit over the elements of `(Φ.over x).fiber`.  It is the forgetful
functor of the over category of `x` in the cofiltered category `Φ.fiber.Elements`, so
`Functor.initial_of_exists_of_isCofiltered` applies; this is what makes
`presheafFiberOverIso` an isomorphism. -/
instance : (overElements Φ x).Initial :=
  Functor.initial_of_exists_of_isCofiltered _
    (fun d => by
      refine ⟨Functor.elementsMk _ (Over.mk (IsCofiltered.minToLeft (Φ.fiber.elementsMk X x) d).hom)
        ⟨_, (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).2
          (IsCofiltered.minToLeft (Φ.fiber.elementsMk X x) d).map_val⟩, ⟨?_⟩⟩
      exact IsCofiltered.minToRight (Φ.fiber.elementsMk X x) d)
    (fun {_} {c} s s' =>
      ⟨Functor.elementsMk _ (Over.mk ((IsCofiltered.eqHom s s').hom ≫ c.obj.hom))
        ⟨_, (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).2
          (map_comp_apply_eq Φ x
            ((FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).1 c.val.property) _
            (IsCofiltered.eqHom s s').map_val)⟩,
        Functor.Elements.homMk (Over.homMk (IsCofiltered.eqHom s s').hom)
          (Subtype.ext (IsCofiltered.eqHom s s').map_val),
        IsCofiltered.eq_condition s s'⟩)

variable (A : Type u') [Category.{v'} A] [HasColimitsOfSize.{w, w} A]

/-- **Stacks 04H2** for presheaves.  Restricting a presheaf on `C` to `C/U` and taking its fibre
at `q = Φ.over x` gives back its fibre at `Φ`. -/
noncomputable def presheafFiberOverIso :
    (Functor.whiskeringLeft _ _ A).obj (Over.forget X).op ⋙ (Φ.over x).presheafFiber ≅
      Φ.presheafFiber :=
  Functor.isoWhiskerLeft ((Functor.whiskeringLeft _ _ A).obj (Functor.Elements.π Φ.fiber).op)
    (Functor.Final.colimIso (overElements Φ x).op)

/-- **Stacks 04H2.** The point `q = Φ.over x` of the localized site `C/U` lies above the point
`Φ` of `C`: for every sheaf `F` on `C` the stalk of `F` at `Φ` agrees with the stalk of its
restriction `j_U⁻¹F = F.over U` at `q`.  In other words the triangle formed by `q`, `Φ` and the
localization morphism `j_U : Sh(C/U) ⟶ Sh(C)` commutes. -/
@[stacks 04H2, sga "4 IV 6.7" "point over (p,ξ), j_X", sga "4 IV 11.3.5" "partial"]
noncomputable def sheafFiberOverIso :
    J.overPullback A X ⋙ (Φ.over x).sheafFiber ≅ Φ.sheafFiber :=
  Functor.isoWhiskerLeft (sheafToPresheaf J A) (presheafFiberOverIso Φ x A)

end CategoryTheory.GrothendieckTopology.Point
