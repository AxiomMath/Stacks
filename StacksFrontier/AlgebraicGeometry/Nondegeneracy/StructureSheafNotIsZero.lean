module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Properties
public import StacksFrontier.CategoryTheory.Nondegeneracy.NotIsZero
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# The structure sheaf of a ringed space is not a zero module

The bottom of every non-degeneracy certificate in this part of the development is the assertion
that `𝒪_X`, viewed as a module over itself, is not a zero object. It is not automatic: over the
zero ring the structure sheaf really is zero, so a hypothesis is needed, and the weakest one that
works is that the sections over a single open form a ring in which `1 ≠ 0`.

On a scheme that hypothesis is discharged: the local rings of a scheme are nontrivial, so the
sections over any nonempty open are nontrivial, and `Nonempty X` suffices.

## Main results

* `Stacks.Nondegeneracy.not_isZero_unit_ringedSpace`: for a ringed space `X` and an open `U` on
  which `1 ≠ 0`, the structure sheaf is not a zero `𝒪_X`-module.
* `AlgebraicGeometry.Scheme.not_isZero_unit`: for a nonempty scheme, `𝒪_X` is not a zero
  `𝒪_X`-module, with no further hypothesis.
* `AlgebraicGeometry.Scheme.not_isZero_singleFunctor_unit`: `𝒪_X` placed in any single degree is
  a nonzero object of the derived category of `𝒪_X`-modules.
* `AlgebraicGeometry.Scheme.not_isZero_unit_toRingedSpace` and
  `Stacks.Nondegeneracy.not_isZero_unit_specRingedSpace`: the same statements in the
  `structureSheafRing` spelling, which is the one the global Künneth and cup-product
  constructions over an arbitrary `RingedSpace.{u, u}` are written in.
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

universe w u

namespace Stacks.Nondegeneracy

/-- **The structure sheaf of a ringed space is not a zero module, as soon as `1 ≠ 0` in its
sections over some open.**  Some such hypothesis is unavoidable: a ringed space whose structure
sheaf is the zero ring everywhere has `𝒪_X = 0`. -/
theorem not_isZero_unit_ringedSpace (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (h : (1 : X.presheaf.obj (op U)) ≠ 0) :
    ¬ IsZero (SheafOfModules.unit (structureSheafRing X)) :=
  not_isZero_unit_of_one_ne_zero (structureSheafRing X) (op U) h

/-- **The structure sheaf of a ringed space is not a zero module, as soon as its sections over
some open form a nontrivial ring.**  The instance-driven form of
`Stacks.Nondegeneracy.not_isZero_unit_ringedSpace`. -/
theorem not_isZero_unit_ringedSpace_of_nontrivial (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    [Nontrivial (X.presheaf.obj (op U))] :
    ¬ IsZero (SheafOfModules.unit (structureSheafRing X)) :=
  not_isZero_unit_ringedSpace X U one_ne_zero

end Stacks.Nondegeneracy

namespace AlgebraicGeometry.Scheme

/-- **The structure sheaf of a nonempty scheme is not a zero `𝒪_X`-module.**  Unlike the ringed
space statement `Stacks.Nondegeneracy.not_isZero_unit_ringedSpace`, this needs no nontriviality
input: the sections of a scheme over a nonempty open form a nontrivial ring, because they map to
the local ring at any of its points.

Nonemptiness is genuinely required — the empty scheme has `Γ(X, ⊤)` the zero ring and `𝒪_X = 0` —
and it cannot be an instance, since `Scheme` carries no nonemptiness. -/
theorem not_isZero_unit (X : Scheme.{u}) [Nonempty X] :
    ¬ IsZero (SheafOfModules.unit X.ringCatSheaf) := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.arbitrary X, trivial⟩⟩
  have : Nontrivial Γ(X, (⊤ : X.Opens)) := Scheme.component_nontrivial X ⊤
  have h : (1 : Γ(X, (⊤ : X.Opens))) ≠ 0 := one_ne_zero
  exact Stacks.Nondegeneracy.not_isZero_unit_of_one_ne_zero X.ringCatSheaf
    (op (⊤ : X.Opens)) h

/-- **The structure sheaf of a nonempty scheme, placed in a single degree, is a nonzero object
of the derived category of `𝒪_X`-modules.**  This is the `¬ IsZero` anchor the comparison data
of the derived Künneth and de Rham constructions are measured against: those data are bare
morphism types, inhabited by the zero morphism, so a certificate that one of them is not the
zero morphism has to start from a nonzero object. -/
theorem not_isZero_singleFunctor_unit (X : Scheme.{u}) [Nonempty X]
    [HasDerivedCategory.{w} X.Modules] (n : ℤ) :
    ¬ IsZero ((DerivedCategory.singleFunctor X.Modules n).obj
      (SheafOfModules.unit X.ringCatSheaf)) :=
  Stacks.Nondegeneracy.not_isZero_singleFunctor_obj n (not_isZero_unit X)

/-- **Over an empty scheme the structure sheaf really is a zero module.**  This is what makes
the `Nonempty X` hypothesis of `AlgebraicGeometry.Scheme.not_isZero_unit` sharp rather than an
artefact of the proof: the only open of an empty scheme is `⊥`, whose ring of sections is
terminal. -/
theorem isZero_unit_of_isEmpty (X : Scheme.{u}) [IsEmpty X] :
    IsZero (SheafOfModules.unit X.ringCatSheaf) := by
  have hsub : ∀ U : X.Opens, Subsingleton Γ(X, U) := by
    intro U
    have hU : U = ⊥ := by ext x; exact isEmptyElim x
    rw [hU]; infer_instance
  rw [IsZero.iff_id_eq_zero]
  ext U
  exact (hsub U.unop).elim _ _

/-- **The structure sheaf of a nonempty scheme is not zero in the `structureSheafRing`
spelling.**  This is the form the global Künneth and cup-product constructions use, since they
are stated over an arbitrary `RingedSpace.{u, u}` rather than over a scheme; it exhibits a
nonempty scheme as a ringed space to which they apply non-degenerately. -/
theorem not_isZero_unit_toRingedSpace (X : Scheme.{u}) [Nonempty X] :
    ¬ IsZero (SheafOfModules.unit (structureSheafRing X.toRingedSpace)) := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.arbitrary X, trivial⟩⟩
  have : Nontrivial Γ(X, (⊤ : X.Opens)) := Scheme.component_nontrivial X ⊤
  exact Stacks.Nondegeneracy.not_isZero_unit_ringedSpace_of_nontrivial X.toRingedSpace ⊤

end AlgebraicGeometry.Scheme

namespace Stacks.Nondegeneracy

/-- **A named unconditional witness: the structure sheaf of `Spec R` is not a zero module for a
nontrivial ring `R`.**  Statements quantifying over a `RingedSpace.{u, u}` have here a base at
which their conclusion is not about a zero object, with nothing assumed beyond `Nontrivial R`. -/
theorem not_isZero_unit_specRingedSpace (R : CommRingCat.{u}) [Nontrivial R] :
    ¬ IsZero (SheafOfModules.unit (structureSheafRing (Spec R).toRingedSpace)) :=
  AlgebraicGeometry.Scheme.not_isZero_unit_toRingedSpace (Spec R)

end Stacks.Nondegeneracy
