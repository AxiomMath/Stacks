module

public import Mathlib.CategoryTheory.Sites.CartesianClosed
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import StacksCore.Tactic.StacksAttribute

/-!
# Sheaves on a site are cartesian closed

Stacks 0BWQ, whose slogan is "the category of sheaves on a site is cartesian closed",
asserts a canonical bijection
`Mor_{Sh(C)}(F × G, H) = Mor_{Sh(C)}(F, SheafHom(G, H))`,
functorial in all three entries, where `SheafHom(G, H)` is the sheaf
`U ↦ Mor_{Sh(C/U)}(G|_{C/U}, H|_{C/U})`.

## What is proved here

`Sheaf.tensorHomEquivIhom` is a bijection of the shape of 0BWQ, for the abstract internal hom
that Mathlib's `MonoidalClosed (Sheaf J A)` instance supplies; this is the slogan (sheaves are
cartesian closed), not the displayed formula of 0BWQ, see below.

For sheaves of sets the instance costs nothing: `monoidalClosed_sheaf_type` records that
`MonoidalClosed (Sheaf J (Type (max u v)))` holds for *any* site, with no side conditions.
This is worth recording because it is not visible from
`Mathlib/CategoryTheory/Sites/CartesianClosed.lean` alone — that file's instance has
hypotheses `[HasSheafify J A]`, `[CartesianMonoidalCategory A]` and
`[MonoidalClosed (Cᵒᵖ ⥤ A)]`, and the two imports discharging the first and third for
`A = Type (max u v)` (`Sites/LeftExact` and `Monoidal/Closed/FunctorToTypes`) are not among its
imports, so the instance does not synthesize without them.

Note also that `CartesianClosed` is no longer a class in Mathlib; it survives only as a
namespace for the `⟹` notation, and the statement to make is `MonoidalClosed` together
with `CartesianMonoidalCategory`.

## What is NOT proved here

The internal hom of the `MonoidalClosed` instance is the abstract one produced by
`cartesianClosedOfReflective'` from the reflection `presheafToSheaf`. It is *not* identified here
with Stacks' `SheafHom`, which is Mathlib's `CategoryTheory.sheafHom`, so
`tensorHomEquivIhom` is not Stacks 0BWQ and does not carry the tag. The displayed formula of
0BWQ with `sheafHom`, for sheaves of sets on a site, natural in all three entries, is
`CategoryTheory.SheafHomAdj.prodHomEquivSheafHom` and `prodHomEquivSheafHom_natural`, in
`StacksFrontier/CategoryTheory/Sites/Glueing/SheafHomProdEquiv.lean`.
-/

@[expose] public section

namespace CategoryTheory.Sheaf

open Limits MonoidalCategory MonoidalClosed

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- For any site `C`, the category of sheaves of sets on `C` is monoidal closed for the
cartesian monoidal structure — i.e. cartesian closed — with no further hypotheses. -/
@[instance_reducible]
noncomputable def monoidalClosed_sheaf_type :
    MonoidalClosed (Sheaf J (Type (max u v))) :=
  inferInstance

/-- For sheaves `F`, `G`, `H` on a site `C` there is a bijection
`Mor(F ⊗ G, H) ≃ Mor(F, ihom G H)`, where `ihom G` is the abstract internal hom of Mathlib's
`MonoidalClosed (Sheaf J A)` instance. It is the hom-equivalence of the adjunction
`- ⊗ G ⊣ ihom G` (with a braiding swap), so it holds by construction of the instance and does not
identify `ihom G H` with the explicit sheaf `SheafHom(G, H)` of Stacks 0BWQ. Stacks 0BWQ itself,
with Mathlib's `sheafHom`, is `CategoryTheory.SheafHomAdj.prodHomEquivSheafHom`. -/
noncomputable def tensorHomEquivIhom {A : Type*} [Category.{max u v} A]
    [CartesianMonoidalCategory A] [MonoidalClosed (Cᵒᵖ ⥤ A)] [HasSheafify J A]
    (F G H : Sheaf J A) :
    (F ⊗ G ⟶ H) ≃ (F ⟶ (ihom G).obj H) :=
  letI : BraidedCategory (Sheaf J A) := .ofCartesianMonoidalCategory
  (Iso.homCongr (β_ F G) (Iso.refl H)).trans ((ihom.adjunction G).homEquiv F H)

end CategoryTheory.Sheaf
