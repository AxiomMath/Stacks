module

public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# The constant-diagram functor is monoidal, and `colim` is oplax monoidal

Let `D` be a monoidal category and `C` any category. The functor category `C ⥤ D` carries the
pointwise monoidal structure `CategoryTheory.Monoidal.functorCategoryMonoidal`, whose tensor
unit is by definition `(Functor.const C).obj (𝟙_ D)`. This file records the fact that the
constant-diagram functor itself is monoidal for that structure, with both the unit comparison
and the tensorator the identity in every component: `(const X ⊗ const Y).obj c` is `X ⊗ Y` on
the nose.

Mathlib has the analogous statement for precomposition
(`CategoryTheory.Functor.Monoidal.whiskeringLeft`) and for postcomposition
(`CategoryTheory.Functor.LaxMonoidal.whiskeringRight`), but not for `Functor.const`, which is
not syntactically a whiskering.

As a consequence `CategoryTheory.Limits.colim` is oplax monoidal: `colim` is left adjoint to
`Functor.const`, and a left adjoint of a lax monoidal functor is oplax monoidal by
`CategoryTheory.Adjunction.leftAdjointOplaxMonoidal`.

## Main definitions

* `CategoryTheory.Functor.constCoreMonoidal`: the monoidal core of `Functor.const C`, with
  `εIso` and `μIso` the identity.
* `CategoryTheory.Functor.constMonoidal`: `Functor.const C : D ⥤ (C ⥤ D)` is a monoidal
  functor.
* `CategoryTheory.Functor.constBraided`: it is braided when `D` is.
* `CategoryTheory.Limits.colimOplaxMonoidal`: `colim : (C ⥤ D) ⥤ D` is oplax monoidal.

## Main results

* `CategoryTheory.Functor.constMonoidal_μ_app` and
  `CategoryTheory.Functor.constMonoidal_ε_app`: the tensorator and the unit comparison of
  `Functor.const C` are the identity in every component; `constMonoidal_δ_app` and
  `constMonoidal_η_app` are the same read oplaxly.
* `CategoryTheory.Monoidal.braiding_app`: the braiding of the pointwise monoidal structure on a
  functor category is the braiding of the target in every component.

## Implementation notes

`(Functor.const C).obj X ⊗ (Functor.const C).obj Y` and `(Functor.const C).obj (X ⊗ Y)` agree on
objects but not as functors: the first sends `f : c ⟶ c'` to `𝟙 X ⊗ₘ 𝟙 Y` and the second to
`𝟙 (X ⊗ Y)`. So the tensorator is `NatIso.ofComponents (fun _ => Iso.refl _)` rather than
`Iso.refl`, and the coherence conditions are checked componentwise after `ext`.

The oplax structure on `colim` is obtained from the adjunction rather than constructed, so its
comparison map `δ` is the mate of the identity; no colimit-preservation hypothesis on the tensor
product is needed, and in particular `colim` is *not* claimed to be strong monoidal here.
-/

@[expose] public noncomputable section

universe v₁ u₁ v₂ u₂

namespace CategoryTheory

open MonoidalCategory CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- **The constant-diagram functor `D ⥤ (C ⥤ D)` is monoidal**, as a `Functor.CoreMonoidal`:
both the unit comparison and the tensorator are the identity in every component, because the
monoidal structure on `C ⥤ D` is pointwise and the tensor unit of `C ⥤ D` is by definition
`(Functor.const C).obj (𝟙_ D)`. -/
def Functor.constCoreMonoidal : (Functor.const C (C := D)).CoreMonoidal where
  εIso := Iso.refl _
  μIso _ _ := NatIso.ofComponents fun _ => Iso.refl _
  μIso_hom_natural_left _ _ := by ext; simp [NatIso.ofComponents]
  μIso_hom_natural_right _ _ := by ext; simp [NatIso.ofComponents]
  associativity _ _ _ := by ext; simp [NatIso.ofComponents]
  left_unitality _ := by ext; simp [NatIso.ofComponents]
  right_unitality _ := by ext; simp [NatIso.ofComponents]

/-- **`Functor.const C : D ⥤ (C ⥤ D)` is a monoidal functor** for the pointwise monoidal
structure on the functor category. -/
instance Functor.constMonoidal : (Functor.const C (C := D)).Monoidal :=
  Functor.constCoreMonoidal.toMonoidal

/-- The tensorator of `Functor.const C` is the identity in every component. -/
@[simp]
lemma Functor.constMonoidal_μ_app (X Y : D) (c : C) :
    (Functor.LaxMonoidal.μ (Functor.const C (C := D)) X Y).app c = 𝟙 (X ⊗ Y) :=
  rfl

/-- The unit comparison of `Functor.const C` is the identity in every component. -/
@[simp]
lemma Functor.constMonoidal_ε_app (c : C) :
    (Functor.LaxMonoidal.ε (Functor.const C (C := D))).app c = 𝟙 (𝟙_ D) :=
  rfl

/-- The oplax tensorator of `Functor.const C` is the identity in every component. -/
@[simp]
lemma Functor.constMonoidal_δ_app (X Y : D) (c : C) :
    (Functor.OplaxMonoidal.δ (Functor.const C (C := D)) X Y).app c = 𝟙 (X ⊗ Y) :=
  rfl

/-- The oplax unit comparison of `Functor.const C` is the identity in every component. -/
@[simp]
lemma Functor.constMonoidal_η_app (c : C) :
    (Functor.OplaxMonoidal.η (Functor.const C (C := D))).app c = 𝟙 (𝟙_ D) :=
  rfl

/-- The braiding of the pointwise monoidal structure on a functor category is the braiding of
the target in every component. -/
@[simp]
lemma Monoidal.braiding_app [BraidedCategory D] (F G : C ⥤ D) (c : C) :
    (β_ F G).hom.app c = (β_ (F.obj c) (G.obj c)).hom :=
  rfl

/-- **`Functor.const C` is a braided monoidal functor** whenever `D` is braided: its tensorator
is the identity, and the braiding of `C ⥤ D` is pointwise. -/
instance Functor.constBraided [BraidedCategory D] : (Functor.const C (C := D)).Braided where
  braided _ _ := by ext; simp

/-- **The colimit functor `(C ⥤ D) ⥤ D` is oplax monoidal.** It is left adjoint to
`Functor.const C`, which `CategoryTheory.Functor.constMonoidal` makes monoidal, hence in
particular lax monoidal, and a left adjoint of a lax monoidal functor is oplax monoidal. The
comparison map `δ : colim (F ⊗ G) ⟶ colim F ⊗ colim G` is the mate of the identity. -/
@[instance_reducible]
def Limits.colimOplaxMonoidal [HasColimitsOfShape C D] :
    (colim (J := C) (C := D)).OplaxMonoidal :=
  (colimConstAdj (J := C) (C := D)).leftAdjointOplaxMonoidal

end CategoryTheory

end
