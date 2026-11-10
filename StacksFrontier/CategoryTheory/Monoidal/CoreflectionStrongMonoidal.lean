module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# The right adjoint of a fully faithful monoidal functor, as a strong monoidal functor

Let `i : C ⥤ D` be a fully faithful monoidal functor with a right adjoint `Q`. By
`CategoryTheory.Adjunction.rightAdjointLaxMonoidal`, `Q` is lax monoidal, with tensor comparison
`μ : Q X ⊗ Q Y ⟶ Q (X ⊗ Y)` the adjoint transpose of `i(Q X ⊗ Q Y) ≅ i Q X ⊗ i Q Y ⟶ X ⊗ Y`, the
tensor product of the two counits. This file shows:

* the unit comparison `ε` of that lax structure is always an isomorphism, because the unit of the
  adjunction is;
* `μ` is an isomorphism at `X, Y` as soon as `Q` inverts the tensor product of the two counits
  (`CategoryTheory.Adjunction.isIso_rightAdjointLaxMonoidal_μ`);
* in that case `Q` is a strong monoidal functor whose lax structure is the one of the adjunction
  (`CategoryTheory.Adjunction.rightAdjointMonoidal`), and it is braided if `i` is
  (`CategoryTheory.Adjunction.rightAdjointBraided`).

This is the formal part of **Stacks 0GQM**: the coherator `Q : LQCoh^fbc(𝒪_𝒳) → QCoh(𝒪_𝒳)` is
a functor of symmetric monoidal categories, its comparison maps being the ones the remark draws.

## Main definitions

* `CategoryTheory.Adjunction.rightAdjointMonoidal`: `Q` as a strong monoidal functor.
* `CategoryTheory.Adjunction.rightAdjointBraided`: `Q` as a braided monoidal functor.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

section Monoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {i : C ⥤ D} {Q : D ⥤ C} (adj : i ⊣ Q) [i.Monoidal] [i.Full] [i.Faithful]

/-- The unit comparison of the lax monoidal structure of the right adjoint of a fully faithful
monoidal functor is an isomorphism. -/
theorem isIso_rightAdjointLaxMonoidal_ε :
    letI := adj.rightAdjointLaxMonoidal
    IsIso (ε Q) := by
  let := adj.rightAdjointLaxMonoidal
  change IsIso (adj.homEquiv _ _ (η i))
  rw [Adjunction.homEquiv_unit]
  infer_instance

/-- The tensor comparison of the right adjoint is the unit followed by the image of the tensor
product of the counits, precomposed with `δ`. -/
private theorem rightAdjointLaxMonoidal_μ_eq {i : C ⥤ D} {Q : D ⥤ C} (adj : i ⊣ Q) [i.Monoidal]
    (X Y : D) :
    letI := adj.rightAdjointLaxMonoidal
    μ Q X Y = adj.unit.app _ ≫ Q.map (δ i _ _ ≫ (adj.counit.app X ⊗ₘ adj.counit.app Y)) := by
  let := adj.rightAdjointLaxMonoidal
  change adj.homEquiv _ _ _ = _
  rw [Adjunction.homEquiv_unit]

/-- The tensor comparison of the lax monoidal structure of the right adjoint of a fully faithful
monoidal functor is an isomorphism at `X, Y` as soon as the right adjoint inverts the tensor
product of the two counits. -/
theorem isIso_rightAdjointLaxMonoidal_μ (X Y : D)
    (h : IsIso (Q.map (adj.counit.app X ⊗ₘ adj.counit.app Y))) :
    letI := adj.rightAdjointLaxMonoidal
    IsIso (μ Q X Y) := by
  let := adj.rightAdjointLaxMonoidal
  rw [adj.rightAdjointLaxMonoidal_μ_eq, Q.map_comp]
  infer_instance

variable (h : ∀ X Y : D, IsIso (Q.map (adj.counit.app X ⊗ₘ adj.counit.app Y)))

/-- **The right adjoint of a fully faithful monoidal functor is strong monoidal** when it inverts
the tensor products of counits. Its lax structure is
`CategoryTheory.Adjunction.rightAdjointLaxMonoidal`
(`CategoryTheory.Adjunction.rightAdjointMonoidal_toLaxMonoidal`). -/
@[instance_reducible]
def rightAdjointMonoidal : Q.Monoidal :=
  letI := adj.rightAdjointLaxMonoidal
  haveI := adj.isIso_rightAdjointLaxMonoidal_ε
  haveI := fun X Y => adj.isIso_rightAdjointLaxMonoidal_μ X Y (h X Y)
  (Functor.CoreMonoidal.ofLaxMonoidal Q).toMonoidal

/-- The lax structure underlying `CategoryTheory.Adjunction.rightAdjointMonoidal` is the one of
the adjunction. -/
theorem rightAdjointMonoidal_toLaxMonoidal :
    (adj.rightAdjointMonoidal h).toLaxMonoidal = adj.rightAdjointLaxMonoidal :=
  rfl

end Monoidal

section Braided

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
  {i : C ⥤ D} {Q : D ⥤ C} (adj : i ⊣ Q) [i.Braided] [i.Full] [i.Faithful]
  (h : ∀ X Y : D, IsIso (Q.map (adj.counit.app X ⊗ₘ adj.counit.app Y)))

omit [i.Full] [i.Faithful] in
/-- The tensor comparison of the right adjoint of a fully faithful braided functor is compatible
with the braidings. -/
theorem rightAdjointLaxMonoidal_braided (X Y : D) :
    letI := adj.rightAdjointLaxMonoidal
    μ Q X Y ≫ Q.map (β_ X Y).hom = (β_ (Q.obj X) (Q.obj Y)).hom ≫ μ Q Y X := by
  let := adj.rightAdjointLaxMonoidal
  rw [adj.rightAdjointLaxMonoidal_μ_eq, adj.rightAdjointLaxMonoidal_μ_eq, Category.assoc,
    ← Q.map_comp, ← adj.unit_naturality_assoc]
  rw [← Q.map_comp]
  congr 2
  have hn := BraidedCategory.braiding_naturality (adj.counit.app X) (adj.counit.app Y)
  have hb := Functor.map_braiding i (Q.obj X) (Q.obj Y)
  simp only [Functor.id_obj] at hn hb ⊢
  rw [Category.assoc, hn, hb, Category.assoc, Category.assoc]
  simp only [Functor.comp_obj, Functor.Monoidal.μ_δ_assoc]

/-- **The right adjoint of a fully faithful braided functor is braided** when it inverts the
tensor products of counits. -/
@[instance_reducible]
def rightAdjointBraided : Q.Braided :=
  letI := adj.rightAdjointMonoidal h
  { braided := adj.rightAdjointLaxMonoidal_braided }

end Braided

end CategoryTheory.Adjunction

end
