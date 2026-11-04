module

public import Mathlib.CategoryTheory.Sites.CartesianClosed
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Monoidal.Closed.Types
public import StacksCore.Tactic.StacksAttribute

/-!
# Sheaves on a site are cartesian closed

Stacks 0BWQ, whose slogan is "the category of sheaves on a site is cartesian closed",
asserts a canonical bijection
`Mor_{Sh(C)}(F × G, H) = Mor_{Sh(C)}(F, SheafHom(G, H))`,
functorial in all three entries, where `SheafHom(G, H)` is the sheaf
`U ↦ Mor_{Sh(C/U)}(G|_{C/U}, H|_{C/U})`.

## What is proved here

`Sheaf.tensorHomEquivIhom` is the bijection, for the internal hom that Mathlib's
`MonoidalClosed (Sheaf J A)` instance supplies. Being the hom-equivalence of an adjunction
it is automatically natural in all three entries, which is Stacks' functoriality clause.

For sheaves of sets the instance costs nothing: `monoidalClosed_sheaf_type` records that
`MonoidalClosed (Sheaf J (Type (max u v)))` holds for *any* site, with no side conditions.
This is worth recording because it is not visible from
`Mathlib/CategoryTheory/Sites/CartesianClosed.lean` alone — that file's instance has
hypotheses `[HasSheafify J A]`, `[CartesianMonoidalCategory A]` and
`[MonoidalClosed (Cᵒᵖ ⥤ A)]`, and the two imports discharging the first and third for
`A = Type (max u v)` (`Sites/LeftExact` and `Monoidal/Closed/Types`) are not among its
imports, so the instance does not synthesize without them.

Note also that `CartesianClosed` is no longer a class in Mathlib; it survives only as a
namespace for the `⟹` notation, and the statement to make is `MonoidalClosed` together
with `CartesianMonoidalCategory`.

## What is NOT proved here

The internal hom of the `MonoidalClosed` instance is the abstract one produced by
`cartesianClosedOfReflective'` from the reflection `presheafToSheaf`. It is *not* known to
agree with Stacks' `SheafHom`, which is Mathlib's `CategoryTheory.sheafHom`. Both
`Mathlib/CategoryTheory/Sites/SheafHom.lean` and `Mathlib/CategoryTheory/Sites/Monoidal.lean`
carry a `TODO` for exactly that identification, and it is not supplied here: the internal
hom is characterised by the adjunction below, so deriving `ihom G H ≅ sheafHom G H` would
require proving the adjunction *for* `sheafHom`, which is the substance of the tag's
displayed formula. So the slogan is settled and the displayed formula, read with Stacks'
own `SheafHom`, is not.
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

/-- **Stacks 0BWQ.** For sheaves `F`, `G`, `H` on a site `C` there is a canonical bijection
`Mor(F × G, H) ≃ Mor(F, SheafHom(G, H))`, where `SheafHom(G, H)` is the internal hom of the
cartesian closed category of sheaves.

The bijection is the hom-equivalence of the adjunction `- ⊗ G ⊣ ihom G`, so it is natural
in all three entries, which is Stacks' functoriality clause. See the module docstring for
the caveat that the internal hom here is Mathlib's abstract one rather than Mathlib's
`sheafHom`. -/
@[stacks 0BWQ]
noncomputable def tensorHomEquivIhom {A : Type*} [Category.{max u v} A]
    [CartesianMonoidalCategory A] [MonoidalClosed (Cᵒᵖ ⥤ A)] [HasSheafify J A]
    (F G H : Sheaf J A) :
    (F ⊗ G ⟶ H) ≃ (F ⟶ (ihom G).obj H) :=
  letI : BraidedCategory (Sheaf J A) := .ofCartesianMonoidalCategory
  (Iso.homCongr (β_ F G) (Iso.refl H)).trans ((ihom.adjunction G).homEquiv F H)

end CategoryTheory.Sheaf
