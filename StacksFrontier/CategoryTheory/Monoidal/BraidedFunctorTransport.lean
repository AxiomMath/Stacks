module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Transporting a braided functor structure along a natural isomorphism

`CategoryTheory.Functor.Monoidal.transport` carries a monoidal functor structure on `F` to one
on `G` along a natural isomorphism `i : F ≅ G`. When `F` is braided so is `G` for the
transported structure: its tensorator is `(i⁻¹ ⊗ i⁻¹) ≫ μ_F ≫ i`, and the braiding axiom for it
is the one for `F` together with the naturality of `i` and of the braiding.

## Main definitions

* `CategoryTheory.Functor.Braided.transport`: the transported braided structure, whose
  underlying monoidal structure is `CategoryTheory.Functor.Monoidal.transport i`.
-/

@[expose] public section

namespace CategoryTheory

open Category MonoidalCategory

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  [BraidedCategory C] [BraidedCategory D]

/-- **A braided functor structure transported along a natural isomorphism** `i : F ≅ G`: the
monoidal structure is `CategoryTheory.Functor.Monoidal.transport i`, and it is braided because
that of `F` is. -/
@[instance_reducible]
def Functor.Braided.transport {F G : C ⥤ D} [F.Braided] (i : F ≅ G) : G.Braided :=
  letI := Functor.Monoidal.transport i
  { braided X Y := by
      rw [Functor.Monoidal.transport_μ, Functor.Monoidal.transport_μ, assoc, assoc,
        ← i.hom.naturality, Functor.LaxBraided.braided_assoc,
        BraidedCategory.braiding_naturality_assoc] }

/-- The monoidal structure underlying `CategoryTheory.Functor.Braided.transport` is
`CategoryTheory.Functor.Monoidal.transport`. -/
theorem Functor.Braided.transport_toMonoidal {F G : C ⥤ D} [F.Braided] (i : F ≅ G) :
    (Functor.Braided.transport i).toMonoidal = Functor.Monoidal.transport i :=
  rfl

end CategoryTheory
