module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategory
public import StacksFrontier.CategoryTheory.DifferentialGraded.HomRepresentation

/-! # The endomorphism differential graded algebra of a differential graded module

Let `(B, d)` be a differential graded algebra over a commutative ring `R` and let `Q` be a right
differential graded `B`-module. The right differential graded `B`-modules are the objects of a
differential graded category over `R` (Tag 09LC), so Tag 09LE applied to the object `Q` of that
category produces a differential graded `R`-algebra `E = End(Q)`, whose degree-`n` part is the
degree-`n` homogeneous right `B`-linear maps `Q → Q`, whose multiplication is composition and whose
differential is the Hom differential; together with the functor `Hom(Q, -)` from the differential
graded `B`-modules to the differential graded `E`-modules, and the functors it induces on closed
degree-zero morphisms, on homotopy classes and into `D(E, d)`.

## Main definitions

* `DifferentialGradedModule.endomorphismRepresentation`: the data of Tag 09LE for the object `Q` of
  the differential graded category of differential graded `B`-modules.
* `DifferentialGradedModule.endomorphismDGA`: the endomorphism differential graded algebra
  `E = End(Q)`.
* `DifferentialGradedModule.endomorphismAlgebraHom`: the degreewise identification of `E^n` with
  the degree-`n` homogeneous right `B`-linear endomorphisms of `Q`.
* `DifferentialGradedModule.endomorphismHomDGFunctor`: the functor of differential graded
  categories `Hom(Q, -)`, with values in differential graded `E`-modules, and
  `DifferentialGradedModule.endomorphismHomModuleHom` its degreewise identification.
* `DifferentialGradedModule.endomorphismHomFunctor`,
  `DifferentialGradedModule.endomorphismHomHomotopyFunctor` and
  `DifferentialGradedModule.endomorphismHomToDerivedCategory`: the induced functors
  `Mod_{(B, d)} ⥤ Mod_{(E, d)}`, `K(B, d) ⥤ K(E, d)` and `K(B, d) ⥤ D(E, d)`.

## Main results

* `DifferentialGradedModule.endomorphismAlgebraHom_d`,
  `DifferentialGradedModule.endomorphismAlgebraHom_mul` and
  `DifferentialGradedModule.endomorphismAlgebraHom_one`: under the degreewise identification the
  differential of `E` is the Hom differential, the multiplication is composition of homogeneous
  maps and the unit is the identity.
* `DifferentialGradedModule.endomorphismHomModuleHom_d` and
  `DifferentialGradedModule.endomorphismHomModuleHom_action`: under the degreewise identification
  the differential of `Hom(Q, N)` is the Hom differential and the action of `E` is composition.

## Implementation notes

The construction is `DGCategory.homRepresentation` (Tag 09LE) at the object `Q` of
`DifferentialGradedModule.dgCategory` (Tag 09LC). The specification theorems are the fields of
`DGCategory.HomRepresentation`, with the Hom groups of `DifferentialGradedModule.dgCategory`
unfolded to `DifferentialGradedModule.HomogeneousMap`. The multiplication and the unit are stated
as the existence of a homogeneous element with a prescribed underlying value, since the degree of a
product is `m + n` only up to a proof `h : m + n = k`.

*Universes.* The module universe of `Q` becomes the algebra universe of `E`: a differential graded
`B`-module in universe `w` has endomorphisms in universe `w`, so `E` is a differential graded
algebra on a type in `Type w` and its modules are taken in `Type w` as well. In the single-universe
convention of this chapter, following Tag 09JJ, all of these collapse.

## References

* [Stacks Project, Tag 09LE](https://stacks.math.columbia.edu/tag/09LE) for the endomorphism
  algebra and the representable functor, and
  [Tag 09LC](https://stacks.math.columbia.edu/tag/09LC) for the differential graded category of
  differential graded modules.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] (B : DifferentialGradedAlgebra.{u, v} R)
  (Q : DifferentialGradedModule.{u, v, w} B)

/-- The data of Tag 09LE for the object `Q` of the differential graded category of right
differential graded `B`-modules: its endomorphism differential graded algebra, the representable
functor `Hom(Q, -)`, and the identifications that pin them down. -/
@[stacks 09LE "the endomorphism algebra of a differential graded module"]
abbrev endomorphismRepresentation :
    DGCategory.HomRepresentation (dgCategory.{u, v, w} B) Q :=
  DGCategory.homRepresentation (dgCategory.{u, v, w} B) Q

/-- **The endomorphism differential graded algebra `E = End(Q)` of a right differential graded
`B`-module `Q`**: the endomorphism algebra of `Q` as an object of the differential graded category
of differential graded `B`-modules. Its degree-`n` part is the degree-`n` homogeneous right
`B`-linear maps `Q → Q`, its multiplication is composition and its differential is the Hom
differential. -/
@[sga "2 V 1.1" "(2), special case"]
abbrev endomorphismDGA : DifferentialGradedAlgebra.{u, w} R :=
  (endomorphismRepresentation B Q).algebra

/-- The degree-`n` part of the endomorphism algebra is the degree-`n` homogeneous right
`B`-linear endomorphisms of `Q`, `R`-linearly. -/
abbrev endomorphismAlgebraHom (n : ℤ) :
    (endomorphismDGA B Q).grading n ≃ₗ[R] HomogeneousMap B Q Q n :=
  (endomorphismRepresentation B Q).algebraHom n

/-- **The differential of `End(Q)` is the Hom differential.** -/
theorem endomorphismAlgebraHom_d (n : ℤ) (a : (endomorphismDGA B Q).grading n) :
    endomorphismAlgebraHom B Q (n + 1)
        ⟨(endomorphismDGA B Q).d a, (endomorphismDGA B Q).d_mem n a a.property⟩ =
      homogeneousMapDifferential B (endomorphismAlgebraHom B Q n a) :=
  (endomorphismRepresentation B Q).algebra_d n a

/-- **Multiplication in `End(Q)` is composition of homogeneous maps.** -/
theorem endomorphismAlgebraHom_mul (m n k : ℤ) (h : m + n = k)
    (a : (endomorphismDGA B Q).grading m) (b : (endomorphismDGA B Q).grading n) :
    ∃ c : (endomorphismDGA B Q).grading k,
      c.1 = a.1 * b.1 ∧
        endomorphismAlgebraHom B Q k c =
          homogeneousMapComp B h (endomorphismAlgebraHom B Q m a)
            (endomorphismAlgebraHom B Q n b) :=
  (endomorphismRepresentation B Q).algebra_mul m n k h a b

/-- **The unit of `End(Q)` is the identity of `Q`.** -/
theorem endomorphismAlgebraHom_one :
    ∃ e : (endomorphismDGA B Q).grading 0,
      e.1 = 1 ∧ endomorphismAlgebraHom B Q 0 e = homogeneousMapId B Q :=
  (endomorphismRepresentation B Q).algebra_one

/-- The functor of differential graded categories `Hom(Q, -)`, from the right differential graded
`B`-modules to the right differential graded `End(Q)`-modules. -/
abbrev endomorphismHomDGFunctor :
    DGCategory.DGFunctor (dgCategory.{u, v, w} B)
      (dgCategory.{u, w, w} (endomorphismDGA B Q)) :=
  (endomorphismRepresentation B Q).functor

/-- The degree-`n` part of `Hom(Q, N)` is the degree-`n` homogeneous right `B`-linear maps
`Q → N`, `R`-linearly. -/
abbrev endomorphismHomModuleHom (N : DifferentialGradedModule.{u, v, w} B) (n : ℤ) :
    ((endomorphismHomDGFunctor B Q).obj N).grading n ≃ₗ[R] HomogeneousMap B Q N n :=
  (endomorphismRepresentation B Q).moduleHom N n

/-- **The differential of `Hom(Q, N)` is the Hom differential.** -/
theorem endomorphismHomModuleHom_d (N : DifferentialGradedModule.{u, v, w} B) (n : ℤ)
    (a : ((endomorphismHomDGFunctor B Q).obj N).grading n) :
    endomorphismHomModuleHom B Q N (n + 1)
        ⟨((endomorphismHomDGFunctor B Q).obj N).d a,
          ((endomorphismHomDGFunctor B Q).obj N).d_mem n a a.property⟩ =
      homogeneousMapDifferential B (endomorphismHomModuleHom B Q N n a) :=
  (endomorphismRepresentation B Q).module_d N n a

/-- **The right action of `End(Q)` on `Hom(Q, N)` is composition.** -/
theorem endomorphismHomModuleHom_action (N : DifferentialGradedModule.{u, v, w} B)
    (m n k : ℤ) (h : m + n = k) (a : ((endomorphismHomDGFunctor B Q).obj N).grading m)
    (b : (endomorphismDGA B Q).grading n) :
    ∃ c : ((endomorphismHomDGFunctor B Q).obj N).grading k,
      c.1 = MulOpposite.op b.1 • a.1 ∧
        endomorphismHomModuleHom B Q N k c =
          homogeneousMapComp B h (endomorphismHomModuleHom B Q N m a)
            (endomorphismAlgebraHom B Q n b) :=
  (endomorphismRepresentation B Q).module_action N m n k h a b

/-- The induced functor on closed degree-zero morphisms,
`Hom(Q, -) : Mod_{(B, d)} ⥤ Mod_{(End(Q), d)}`: the comparison of Tag 09LC between the
differential graded `B`-modules and the category of complexes of their differential graded
category, followed by the functor of Tag 09LE. -/
def endomorphismHomFunctor :
    DifferentialGradedModule.{u, v, w} B ⥤
      DifferentialGradedModule.{u, w, w} (endomorphismDGA B Q) :=
  (dgCategoryCompEquivalence.{u, v, w} B).1.inverse ⋙
    (endomorphismRepresentation B Q).complexesFunctor

/-- The induced functor on homotopy classes, `Hom(Q, -) : K(B, d) ⥤ K(End(Q), d)`: the comparison
of Tag 09LC between `K(B, d)` and the homotopy category of the differential graded category of
differential graded `B`-modules, followed by the functor of Tag 09LE. -/
def endomorphismHomHomotopyFunctor :
    HomotopyCategory.{u, v, w} B ⥤ HomotopyCategory.{u, w, w} (endomorphismDGA B Q) :=
  (homotopyCategoryEquivalence.{u, v, w} B).functor ⋙
    (endomorphismRepresentation B Q).homotopyFunctor

/-- The differential graded Hom functor into the derived category,
`Hom(Q, -) : K(B, d) ⥤ D(End(Q), d)`: the functor on homotopy classes followed by the
localization at the quasi-isomorphisms.

The derived category `DifferentialGradedModule.derivedCategory'` is taken at equal universes, so
this is stated in the single-universe convention of Tag 09JJ, where the endomorphism algebra of a
module in universe `u` is again an algebra on a type in `Type u`. -/
def endomorphismHomToDerivedCategory (B : DifferentialGradedAlgebra.{u, u} R)
    (Q : DifferentialGradedModule.{u, u, u} B) :
    HomotopyCategory.{u, u, u} B ⥤ derivedCategory' (endomorphismDGA B Q) :=
  endomorphismHomHomotopyFunctor B Q ⋙ (quasiIsomorphisms' (endomorphismDGA B Q)).Q

end DifferentialGradedModule

end
