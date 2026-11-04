module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Cokernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Vanishing

/-!
# Surjectivity of a morphism of coherent adic systems is detected at the first level

Let `X` be a scheme, `ℐ` a quasi-coherent ideal sheaf on `X` and `f : (F_n) ⟶ (G_n)` a morphism
of coherent adic systems along `ℐ`. Then `f` is an epimorphism of `Coh(X, ℐ)` precisely when its
component at the lowest level is an epimorphism of `𝒪_X`-modules.

One direction is formal: the cokernel of `f` in `Coh(X, ℐ)` is computed levelwise, and evaluation
at a level preserves that cokernel, so a vanishing cokernel vanishes at every level. The other
direction is the substance. If the cokernel vanishes at the lowest level only, then each of its
terms `C_n` satisfies `C_n = ℐ ⁿ⁺¹ C_n`; since `C_n` is also annihilated by `ℐ ⁿ⁺¹`, iterating
once gives that `C_n` is killed by `ℐ ²⁽ⁿ⁺¹⁾`, which lies inside `ℐ ⁿ⁺²`, and a module equal to a
power of the ideal times itself while being annihilated by that power is zero. So the whole
cokernel vanishes and `f` is an epimorphism.

Unlike the source, no Noetherian hypothesis is needed: the argument uses only the defining
properties of a coherent adic system.

## Main results

* `Stacks.Coherent.epi_iff_epi_app_zero` — a morphism of coherent adic systems is an epimorphism
  if and only if its component at level `0` is.

## Implementation notes

The system is indexed by `ℕᵒᵖ` and is zero-indexed: term `n` represents the source's `F_{n+1}`, so
the source's `F_1 → G_1` is the component at `op 0`.

An object of `Coh(X, ℐ)` is zero exactly when the underlying inverse system is, because the
category is a full subcategory and its identity morphisms are those of the ambient functor
category; that step is `Stacks.Coherent.isZero_coherentAdicSystems_iff`.

## References

* [Stacks Project, Tag 087Y](https://stacks.math.columbia.edu/tag/087Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- An object of `Coh(X, ℐ)` is zero exactly when the inverse system underlying it is zero. -/
public theorem isZero_coherentAdicSystems_iff (F : CoherentAdicSystems I) :
    IsZero F ↔ IsZero F.obj := by
  rw [IsZero.iff_id_eq_zero, IsZero.iff_id_eq_zero]
  exact ⟨fun h => congrArg InducedCategory.Hom.hom h, fun h => ObjectProperty.hom_ext _ h⟩

/-- **Stacks 087Y.** A morphism of coherent adic systems is surjective exactly when its
component at the lowest level is surjective. -/
@[stacks 087Y]
public theorem epi_iff_epi_app_zero {F G : CoherentAdicSystems I} (f : F ⟶ G) :
    Epi f ↔ Epi (f.hom.app (op 0)) := by
  have hsys : Epi f ↔ IsZero (cokernel f.hom) :=
    (Preadditive.epi_iff_isZero_cokernel' _ (coherentAdicCokernelIsColimit I f)).trans
      (isZero_coherentAdicSystems_iff I (coherentAdicCokernel I f))
  have hlev : Epi (f.hom.app (op 0)) ↔ IsZero (cokernel (f.hom.app (op 0))) :=
    Preadditive.epi_iff_isZero_cokernel _
  rw [hsys, hlev]
  refine ⟨fun h => ((cokernelObjIso f.hom (op 0)).isZero_iff).mp
      ((Functor.isZero_iff _).mp h (op 0)), fun h => ?_⟩
  refine (Functor.isZero_iff _).mpr fun n => ?_
  exact isZero_of_isZero_obj_zero (isCoherentAdicSystem_cokernel I f)
    (((cokernelObjIso f.hom (op 0)).isZero_iff).mpr h) n.unop

end Stacks.Coherent

end
