module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.IdealPowerQuotient
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleCompleteLattice

/-!
# Coherent adic systems along an ideal sheaf

Let `X` be a scheme and `I` a quasi-coherent ideal sheaf on `X`. A *coherent adic system*
along `I` is an inverse system `(F_n)` of coherent sheaves of modules in which `F_n` is
annihilated by `I ^ (n+1)` and is the quotient of `F_{n+1}` by that same power.

## Main definitions

* `Stacks.Coherent.IsCoherentAdicSystem` — the coherence, annihilation and quotient-transition
  conditions on an inverse system of sheaves of modules.
* `Stacks.Coherent.CoherentAdicSystems` — the category `Coh(X, I)` they cut out, as a full
  subcategory of `ℕᵒᵖ ⥤ X.Modules`.

## Implementation notes

The system is indexed by `ℕᵒᵖ`, and the term at `n` is annihilated by `I ^ (n+1)`. The third
clause asks for an isomorphism `F_{n+1} / I ^ (n+1) F_{n+1} ≅ F_n` which intertwines the cokernel
projection with the transition map. The ideal-power multiple and quotient are
`Stacks.Algebraization.idealPowerMultiple` and `Stacks.Algebraization.idealPowerQuotient`.

`CoherentAdicSystems` is a full subcategory, so a morphism of coherent adic systems is just a
natural transformation of the underlying functors.

The coherence universe is written explicitly as `SheafOfModules.IsCoherent.{u}`. The predicate
is universe-polymorphic with all four of its levels equal, and that is the instantiation
`X.Modules` needs for `X : Scheme.{u}`; left implicit, the level is defaulted to `0` before
unification reaches `Scheme.ringCatSheaf` and elaboration fails.

## References

* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

/-- The defining properties of a coherent inverse system along an ideal sheaf.
The term at `n` is annihilated by the `(n + 1)`-st power of the ideal and is
the quotient of the next term by that same power. -/
public def IsCoherentAdicSystem {X : Scheme.{u}} (I : X.IdealSheafData)
    (F : ℕᵒᵖ ⥤ X.Modules) : Prop :=
  (∀ n : ℕ, SheafOfModules.IsCoherent.{u} (F.obj (op n))) ∧
  (∀ n : ℕ, Stacks.Algebraization.idealPowerMultiple I (n + 1) (F.obj (op n)) = ⊥) ∧
  (∀ n : ℕ, ∃ e : Stacks.Algebraization.idealPowerQuotient I (n + 1)
      (F.obj (op (n + 1))) ≅ F.obj (op n),
    cokernel.π ((Stacks.Algebraization.idealPowerMultiple I (n + 1)
      (F.obj (op (n + 1)))).ι) ≫ e.hom =
      F.map (homOfLE (Nat.le_succ n)).op)

/-- The category `Coh(X,I)` of coherent adic inverse systems. -/
public abbrev CoherentAdicSystems {X : Scheme.{u}} (I : X.IdealSheafData) :=
  ObjectProperty.FullSubcategory
    (C := ℕᵒᵖ ⥤ X.Modules) (IsCoherentAdicSystem I)

end Stacks.Coherent

end
