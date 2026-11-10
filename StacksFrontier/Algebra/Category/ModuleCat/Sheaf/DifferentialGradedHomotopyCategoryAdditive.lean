module

public import Mathlib.CategoryTheory.Quotient.Preadditive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyCategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedModuleAbelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedProducts

/-!
# The homotopy category of differential graded modules is additive

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of differential graded
`R`-algebras. Homotopy of morphisms of right differential graded `A`-modules is compatible with
the degreewise addition of morphisms, so the homotopy category `K(A)` inherits an additive
structure on its arrow sets and the quotient functor is additive.

## Main results

* `SheafOfModules.DifferentialGradedModule.homotopic_add`: homotopy is compatible with addition
  of morphisms.
* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.instPreadditive`: the homotopy
  category is preadditive.
* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.quotient_additive`: the quotient
  functor is additive.
* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.quotient_map_eq_zero_iff`: an arrow
  of the homotopy category vanishes exactly when its representative is null homotopic.
* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.instHasZeroObject`: the homotopy
  category has a zero object.

## Implementation notes

Compatibility with addition is reduced to adding a fixed morphism on one side, where the
homotopy and its action compatibility are unchanged and only the homotopy equation has to be
rewritten; the two-sided statement then follows from transitivity and commutativity of addition.
The preadditive structure is `CategoryTheory.Quotient.preadditive` for the homotopy congruence.
A zero object is obtained by applying the quotient functor to a zero object of the category of
differential graded modules: the quotient functor is additive, so it takes an identity that
vanishes to an identity that vanishes. The zero object of differential graded modules comes from
their degreewise products, so no hypothesis on the site is needed.

The base is an arbitrary sheaf of rings on an arbitrary site rather than the structure sheaf of
a ringed site, and the universes of the site, the ring, the algebra pieces and the module pieces
are independent, matching
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedHomotopyCategory.lean`.

### No `@[stacks 0FS7]`

Stacks 0FS7 is the assertion that the homotopy category of differential graded modules over a
sheaf of differential graded algebras is a triangulated category. What is here is the additive
structure on its arrow sets and its zero object, two prerequisites of that assertion. The shift
functors, the distinguished triangles coming from admissible short exact sequences, the
pre-triangulated structure and the octahedron axiom are not here, so no `@[stacks]` attribute is
placed in this file.

The missing ingredient is Stacks 09QY, Differential Graded Algebra Proposition 22.27.16, which says
that the homotopy category of a differential graded category in a cone situation is triangulated;
it is not available in the library. The generic development in
`StacksFrontier/CategoryTheory/DifferentialGraded/` stops at the ingredients — the connecting
morphism and the associated triangles of Stacks 09P6, `DGCategory.ConeSituation` of Stacks 09QJ,
the octahedron of Stacks 09QX, and the comparison results `coneTriangleIsoOfShortExact`,
`rotatedAssociatedTriangle_iso_connectingConeTriangle`,
`associatedKTriangle_eq_of_same_sequence`, `exists_rectification_of_isAdmissibleMono` and
`exists_admissibleMono_factorization` — without assembling them into a pre-triangulated
structure, and the homotopy category of a differential graded category carries no `Preadditive`
instance at the generic `DGCategory` level either.

`SheafOfModules.DifferentialGradedModule.HomotopyCategory.quotient_map_eq_zero_iff` is the
vanishing-of-groups statement that the `IsKInjective` predicate of Stacks 0FSU currently stands
in for with a `Subsingleton` of the arrow type, so the implementation note recorded there can be
revisited once the shift functors exist.

## References

* [Stacks Project, Tag 0FS7](https://stacks.math.columbia.edu/tag/0FS7)
-/

@[expose] public section

open CategoryTheory

universe t a m v u

namespace SheafOfModules

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R}

/-- A homotopy stays a homotopy after adding a fixed morphism to both of its ends. -/
private def homotopyAddRight {M N : DifferentialGradedModule.{t, a, m} A} {f₁ f₂ : M ⟶ N}
    (h : Homotopy f₁ f₂) (g : M ⟶ N) : Homotopy (f₁ + g) (f₂ + g) where
  app := h.app
  map_mul := h.map_mul
  comm n := by
    rw [show (f₁ + g).toHomologicalComplex.f n - (f₂ + g).toHomologicalComplex.f n =
      f₁.toHomologicalComplex.f n - f₂.toHomologicalComplex.f n by
        simp only [add_f]; abel]
    exact h.comm n

/-- Homotopy of morphisms of right differential graded modules is compatible with the
degreewise addition of morphisms. -/
theorem homotopic_add {M N : DifferentialGradedModule.{t, a, m} A} (f₁ f₂ g₁ g₂ : M ⟶ N)
    (hf : Homotopic f₁ f₂) (hg : Homotopic g₁ g₂) : Homotopic (f₁ + g₁) (f₂ + g₂) := by
  obtain ⟨hf⟩ := hf
  obtain ⟨hg⟩ := hg
  refine (homotopic_congruence A).equivalence.trans ⟨homotopyAddRight hf g₁⟩ ?_
  rw [add_comm f₂ g₁, add_comm f₂ g₂]
  exact ⟨homotopyAddRight hg f₂⟩

namespace HomotopyCategory

/-- The arrow sets of the homotopy category of right differential graded modules are additive
groups and composition is bilinear. -/
instance instPreadditive (A : DifferentialGradedAlgebra.{t, a} R) :
    Preadditive (HomotopyCategory.{t, a, m} A) :=
  CategoryTheory.Quotient.preadditive
    (fun {M N : DifferentialGradedModule.{t, a, m} A} (f g : M ⟶ N) => Homotopic f g)
    (fun _ _ f₁ f₂ g₁ g₂ hf hg => homotopic_add f₁ f₂ g₁ g₂ hf hg)

/-- The functor to the homotopy category is additive. -/
instance quotient_additive (A : DifferentialGradedAlgebra.{t, a} R) :
    (quotient.{t, a, m} A).Additive :=
  CategoryTheory.Quotient.functor_additive
    (fun {M N : DifferentialGradedModule.{t, a, m} A} (f g : M ⟶ N) => Homotopic f g)
    (fun _ _ f₁ f₂ g₁ g₂ hf hg => homotopic_add f₁ f₂ g₁ g₂ hf hg)

/-- The homotopy class of a sum of morphisms is the sum of their homotopy classes. -/
@[simp]
theorem quotient_map_add {M N : DifferentialGradedModule.{t, a, m} A} (f g : M ⟶ N) :
    (quotient A).map (f + g) = (quotient A).map f + (quotient A).map g :=
  (quotient A).map_add

/-- The homotopy class of the zero morphism is zero. -/
@[simp]
theorem quotient_map_zero (M N : DifferentialGradedModule.{t, a, m} A) :
    (quotient A).map (0 : M ⟶ N) = 0 :=
  (quotient A).map_zero M N

/-- An arrow of the homotopy category vanishes exactly when a representative of it is
homotopic to zero. -/
theorem quotient_map_eq_zero_iff {M N : DifferentialGradedModule.{t, a, m} A} (f : M ⟶ N) :
    (quotient A).map f = 0 ↔ Homotopic f (0 : M ⟶ N) := by
  rw [← quotient_map_zero M N, quotient_map_eq_iff]

/-- The homotopy class of a zero object of differential graded modules is a zero object. -/
theorem isZero_quotient_obj {Z : DifferentialGradedModule.{t, a, m} A}
    (hZ : Limits.IsZero Z) : Limits.IsZero ((quotient A).obj Z) := by
  rw [Limits.IsZero.iff_id_eq_zero, ← (quotient A).map_id,
    (Limits.IsZero.iff_id_eq_zero Z).mp hZ]
  exact (quotient A).map_zero Z Z

/-- The homotopy category of right differential graded modules has a zero object. -/
instance instHasZeroObject (A : DifferentialGradedAlgebra.{t, a} R) :
    Limits.HasZeroObject (HomotopyCategory.{t, a, m} A) := by
  have : Limits.HasFiniteProducts (DifferentialGradedModule.{t, a, m} A) :=
    Limits.hasFiniteProducts_of_hasProducts.{m} _
  obtain ⟨Z, hZ⟩ :=
    (Limits.hasZeroObject_of_hasTerminal_object (C := DifferentialGradedModule.{t, a, m} A)).zero
  exact (isZero_quotient_obj hZ).hasZeroObject

end HomotopyCategory

end DifferentialGradedModule

end SheafOfModules
