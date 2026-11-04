module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Localization.Construction
public import StacksCore.Algebra.Homology.QuasiIso
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyCategory

/-!
# The derived category of a sheaf of differential graded algebras

Let `R` be a sheaf of rings on a site admitting sheafification and let `A` be a sheaf of
differential graded `R`-algebras. A morphism of right differential graded `A`-modules is a
quasi-isomorphism when its underlying morphism of cochain complexes of sheaves of modules is,
and this only depends on the homotopy class, so being a quasi-isomorphism is a property of an
arrow of the homotopy category `K(Mod(A, d))`. The derived category `D(A, d)` is obtained from
`K(Mod(A, d))` by inverting those arrows.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.Homotopy.toComplexHomotopy` is the homotopy of
  underlying cochain complexes attached to a homotopy of right differential graded modules.
* `SheafOfModules.DifferentialGradedModule.quasiIsomorphisms` is the class of
  quasi-isomorphisms in the homotopy category of right differential graded modules.
* `SheafOfModules.DifferentialGradedModule.derivedCategory` is the derived category of
  `(A, d)`, the localization of the homotopy category at the quasi-isomorphisms.
* `SheafOfModules.DifferentialGradedModule.toDerivedCategory` is the canonical functor from
  the homotopy category to the derived category.

## Main results

* `SheafOfModules.DifferentialGradedModule.quasiIso_toHomologicalComplex_iff_of_homotopic`:
  homotopic morphisms of right differential graded modules are quasi-isomorphisms together.
* `SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_quotient_map_iff`: an arrow of the
  homotopy category represented by a morphism of right differential graded modules is a
  quasi-isomorphism exactly when that morphism is one on the underlying complexes.
* `SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_isMultiplicative`: the
  quasi-isomorphisms contain the identities and are stable under composition.

## Implementation notes

Being a quasi-isomorphism is read off the underlying complex of sheaves of modules, where it is
Mathlib's `QuasiIso`. The hypotheses `HasSheafify J AddCommGrpCat.{m}` and
`J.WEqualsLocallyBijective AddCommGrpCat.{m}` make `SheafOfModules.{m} R` abelian, so that the
homology of its cochain complexes is available.

The class of quasi-isomorphisms is phrased as a condition on *every* representing morphism of
right differential graded modules, so that it is a `CategoryTheory.MorphismProperty` with no
choice of representative; `quasiIsomorphisms_quotient_map_iff` shows that one representative
suffices.

The derived category is an `abbrev` for `CategoryTheory.MorphismProperty.Localization`. No
triangulated structure is asserted: Mathlib's `CategoryTheory.Localization.Triangulated` gives one
once the homotopy category is pretriangulated (Stacks Tag 0FS7) and the quasi-isomorphisms form a
multiplicative system compatible with the triangulation (Stacks Tag 0FT4).

The base is an arbitrary sheaf of rings on an arbitrary site; a ringed site `X` is the case
`R := X.ringSheaf`.

## References

* [Stacks Project, Tag 0FT5](https://stacks.math.columbia.edu/tag/0FT5)
-/

@[expose] public noncomputable section

open CategoryTheory

universe t a m v u

namespace SheafOfModules

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R}

/-- The homotopy of underlying cochain complexes of sheaves of modules attached to a homotopy of
morphisms of right differential graded modules. -/
def Homotopy.toComplexHomotopy {M N : DifferentialGradedModule.{t, a, m} A} {f g : M ⟶ N}
    (h : Homotopy f g) : _root_.Homotopy f.toHomologicalComplex g.toHomologicalComplex where
  hom i j := if hij : j + 1 = i then
      h.app i ≫ eqToHom (congrArg N.complex.X (by omega : i - 1 = j)) else 0
  zero i j hij := by
    change ¬ (j + 1 = i) at hij
    simp [hij]
  comm i := by
    rw [dNext_eq _ (ComplexShape.up_mk i (i + 1) (by omega)),
      prevD_eq _ (ComplexShape.up_mk (i - 1) i (by omega))]
    simp only [↓reduceDIte, sub_add_cancel, eqToHom_refl, Category.comp_id]
    rw [← sub_eq_iff_eq_add, h.comm i]
    simp only [Category.assoc, add_comm]

section Abelian

variable [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- Homotopic morphisms of right differential graded modules are quasi-isomorphisms on the
underlying complexes of sheaves of modules together. -/
theorem quasiIso_toHomologicalComplex_iff_of_homotopic
    {M N : DifferentialGradedModule.{t, a, m} A} {f g : M ⟶ N} (h : Homotopic f g) :
    QuasiIso f.toHomologicalComplex ↔ QuasiIso g.toHomologicalComplex := by
  rw [quasiIso_iff_isIso_homologyMap, quasiIso_iff_isIso_homologyMap]
  exact forall_congr' fun i => by rw [h.some.toComplexHomotopy.homologyMap_eq i]

/-- The quasi-isomorphisms in the homotopy category of right differential graded modules: the
arrows all of whose representing morphisms of right differential graded modules are
quasi-isomorphisms on the underlying complexes of sheaves of modules. -/
def quasiIsomorphisms (A : DifferentialGradedAlgebra.{t, a} R) :
    MorphismProperty (HomotopyCategory.{t, a, m} A) :=
  fun M N φ => ∀ f : M.as ⟶ N.as,
    (HomotopyCategory.quotient A).map f = φ → QuasiIso f.toHomologicalComplex

/-- An arrow of the homotopy category represented by a morphism `f` of right differential graded
modules is a quasi-isomorphism exactly when `f` is one on the underlying complexes of sheaves of
modules. -/
theorem quasiIsomorphisms_quotient_map_iff {M N : DifferentialGradedModule.{t, a, m} A}
    (f : M ⟶ N) :
    quasiIsomorphisms.{t, a, m} A ((HomotopyCategory.quotient A).map f) ↔
      QuasiIso f.toHomologicalComplex := by
  refine ⟨fun h => h f rfl, fun hf g hg => ?_⟩
  exact (quasiIso_toHomologicalComplex_iff_of_homotopic
    ((HomotopyCategory.quotient_map_eq_iff g f).1 hg)).2 hf

/-- The quasi-isomorphisms contain the identities of the homotopy category and are stable under
composition. -/
theorem quasiIsomorphisms_isMultiplicative (A : DifferentialGradedAlgebra.{t, a} R) :
    (quasiIsomorphisms.{t, a, m} A).IsMultiplicative where
  id_mem M := by
    have := (quasiIsomorphisms_quotient_map_iff (𝟙 M.as)).2
      (inferInstanceAs (QuasiIso (𝟙 M.as.complex)))
    rwa [(HomotopyCategory.quotient A).map_id] at this
  comp_mem φ ψ hφ hψ := by
    have h₁ := (quasiIsomorphisms_quotient_map_iff
      ((HomotopyCategory.quotient A).preimage φ)).1
      (by rwa [(HomotopyCategory.quotient A).map_preimage])
    have h₂ := (quasiIsomorphisms_quotient_map_iff
      ((HomotopyCategory.quotient A).preimage ψ)).1
      (by rwa [(HomotopyCategory.quotient A).map_preimage])
    have := (quasiIsomorphisms_quotient_map_iff
      ((HomotopyCategory.quotient A).preimage φ ≫ (HomotopyCategory.quotient A).preimage ψ)).2
      (inferInstanceAs (QuasiIso (_ ≫ _)))
    simpa using this

/-- The derived category of a sheaf of differential graded algebras `(A, d)`: the localization
of the homotopy category of right differential graded `A`-modules at the quasi-isomorphisms. -/
@[stacks 0FT5]
abbrev derivedCategory (A : DifferentialGradedAlgebra.{t, a} R) : Type _ :=
  (quasiIsomorphisms.{t, a, m} A).Localization

/-- The canonical functor from the homotopy category of right differential graded `A`-modules to
the derived category of `(A, d)`, which inverts the quasi-isomorphisms. -/
@[stacks 0FT5 "the localization functor"]
abbrev toDerivedCategory (A : DifferentialGradedAlgebra.{t, a} R) :
    HomotopyCategory.{t, a, m} A ⥤ derivedCategory.{t, a, m} A :=
  (quasiIsomorphisms.{t, a, m} A).Q

end Abelian

end DifferentialGradedModule

end SheafOfModules

end
