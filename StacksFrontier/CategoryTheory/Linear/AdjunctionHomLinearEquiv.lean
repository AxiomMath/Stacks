module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # The hom-set bijection of an adjunction is linear

Let `F ⊣ G` be an adjunction between two `R`-linear categories. Its hom-set bijection
`Hom(F X, Y) ≃ Hom(X, G Y)` is `f ↦ η_X ≫ G f`, so it is additive as soon as `F` is additive —
this is Mathlib's `CategoryTheory.Adjunction.homAddEquiv` — and it is moreover `R`-linear as soon
as the right adjoint `G` is `R`-linear, because `G` then carries `r • f` to `r • G f` and
composition on the left of a scalar multiple is the scalar multiple of the composition.

## Main definitions

* `CategoryTheory.Adjunction.homLinearEquiv`: the hom-set bijection of an adjunction, as an
  isomorphism of `R`-modules.

## Implementation notes

Only the right adjoint is assumed `R`-linear. That is the useful hypothesis in practice: the left
adjoint's linearity follows from it (`CategoryTheory.Adjunction.leftAdjointLinearOfRightAdjoint`
is not needed here, but the same argument gives it), whereas the converse direction would require
the counit form of the bijection. Additivity of the *left* adjoint is what Mathlib's
`CategoryTheory.Adjunction.homAddEquiv` asks for, and it is kept as the only additivity
hypothesis so that this definition is no harder to apply than that one.

The `map_smul'` field is stated through a `show` rather than proved by rewriting in place: the
field's own statement mentions `RingHom.id R r` where the bijection's value mentions `r`, and the
`show` discharges that difference definitionally before any rewriting happens.
-/

@[expose] public noncomputable section

universe v₁ v₂ u₁ u₂ w

namespace CategoryTheory.Adjunction

variable {R : Type w} [Semiring R] {C : Type u₁} {D : Type u₂} [Category.{v₁} C]
  [Category.{v₂} D] [Preadditive C] [Preadditive D] [Linear R C] [Linear R D] {F : C ⥤ D}
  {G : D ⥤ C}

/-- **The hom-set bijection of an adjunction, as an isomorphism of `R`-modules.** For an
adjunction `F ⊣ G` between `R`-linear categories with `F` additive and `G` `R`-linear, the
bijection `Hom(F X, Y) ≃ Hom(X, G Y)` of `CategoryTheory.Adjunction.homEquiv` is `R`-linear: it
sends `f` to `η_X ≫ G f`, and `G (r • f) = r • G f` because `G` is `R`-linear, while
`η_X ≫ (r • g) = r • (η_X ≫ g)` because composition is `R`-bilinear. -/
def homLinearEquiv (R : Type w) [Semiring R] [Linear R C] [Linear R D] (adj : F ⊣ G)
    [F.Additive] [G.Linear R] (X : C) (Y : D) : (F.obj X ⟶ Y) ≃ₗ[R] (X ⟶ G.obj Y) :=
  { adj.homAddEquiv X Y with
    map_smul' := fun r f => by
      change adj.homEquiv X Y (r • f) = r • adj.homEquiv X Y f
      rw [adj.homEquiv_unit, adj.homEquiv_unit, Functor.map_smul, Linear.comp_smul] }

/-- `CategoryTheory.Adjunction.homLinearEquiv` is the bijection of the adjunction. -/
@[simp]
theorem homLinearEquiv_apply (adj : F ⊣ G) [F.Additive] [G.Linear R] (X : C) (Y : D)
    (f : F.obj X ⟶ Y) : homLinearEquiv R adj X Y f = adj.homEquiv X Y f := rfl

/-- The inverse of `CategoryTheory.Adjunction.homLinearEquiv` is the inverse of the bijection of
the adjunction. -/
@[simp]
theorem homLinearEquiv_symm_apply (adj : F ⊣ G) [F.Additive] [G.Linear R] (X : C) (Y : D)
    (g : X ⟶ G.obj Y) : (homLinearEquiv R adj X Y).symm g = (adj.homEquiv X Y).symm g := rfl

end CategoryTheory.Adjunction

end
