module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Extension.Cotangent.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The cotangent space of a canonical presentation does not depend on the base

Let `R ⟶ R' ⟶ T` be ring maps and let `α : R[T] ⟶ T` and `β : R'[T] ⟶ T` be the canonical
presentations of Stacks 07BL of `T` over `R` and over `R'`.  The cotangent space of either is
the free `T`-module on the set `T`, with basis the elements `1 ⊗ D X_t`
(`Algebra.Generators.cotangentSpaceBasis`), and a morphism of extensions `α ⟶ β` which carries
the variable `X_t` to the variable `X_t` carries that basis to that basis.  It is therefore an
isomorphism in degree `0`, *whatever the two bases are*.

This is the degree `0` half of the canonical map `g : NL_{T/R} ⟶ NL_{T/R'}`, and the reason the
six-term sequence of Stacks 00S2 can be read off a cokernel: the shifted cone of a map of
two-term complexes whose degree `0` component is invertible has only one interesting cohomology
group.

## Main results

* `NaiveCotangent.cotangentSpaceMap_cotangentSpaceBasis`: a morphism of extensions of `T`
  between two canonical presentations which fixes the variables carries the canonical basis to
  the canonical basis.
* `NaiveCotangent.bijective_cotangentSpaceMap_self`: such a morphism induces a bijection of
  cotangent spaces.

## References

* [Stacks Project, Tag 07BL](https://stacks.math.columbia.edu/tag/07BL), the canonical
  presentation.
* [Stacks Project, Tag 00S2](https://stacks.math.columbia.edu/tag/00S2), the six-term sequence.
-/

@[expose] public section

open Algebra

namespace NaiveCotangent

variable {R R' T : Type*} [CommRing R] [CommRing R'] [CommRing T]
  [Algebra R T] [Algebra R R'] [Algebra R' T] [IsScalarTower R R' T]

/-- **A morphism of canonical presentations of `T` which fixes the variables carries the
canonical basis of the cotangent space to the canonical basis.** -/
theorem cotangentSpaceMap_cotangentSpaceBasis
    (h : (Generators.self R T).toExtension.Hom (Generators.self R' T).toExtension)
    (hX : ∀ t : T, h.toRingHom (MvPolynomial.X t) = MvPolynomial.X t) (t : T) :
    Extension.CotangentSpace.map h ((Generators.self R T).cotangentSpaceBasis t) =
      (Generators.self R' T).cotangentSpaceBasis t := by
  have e₂ : h.toAlgHom (MvPolynomial.X t) = MvPolynomial.X t :=
    (Extension.Hom.toAlgHom_apply h _).trans (hX t)
  have e₃ : ((algebraMap T T) (1 : T)) ⊗ₜ[(Generators.self R' T).Ring]
        (KaehlerDifferential.D R' (Generators.self R' T).Ring
          (h.toAlgHom (MvPolynomial.X t))) =
      (1 : T) ⊗ₜ[(Generators.self R' T).Ring]
        (KaehlerDifferential.D R' (Generators.self R' T).Ring (MvPolynomial.X t)) := by
    rw [e₂, map_one]
  exact (congrArg (Extension.CotangentSpace.map h)
      (Generators.cotangentSpaceBasis_apply (Generators.self R T) t)).trans
    ((Extension.CotangentSpace.map_tmul h 1 (MvPolynomial.X t)).trans
      (e₃.trans (Generators.cotangentSpaceBasis_apply (Generators.self R' T) t).symm))

/-- **The degree `0` component of the comparison of two canonical presentations of `T` is
bijective.**  Both cotangent spaces are free `T`-modules on the set `T`, and a morphism of
extensions fixing the variables carries the basis to the basis. -/
theorem bijective_cotangentSpaceMap_self
    (h : (Generators.self R T).toExtension.Hom (Generators.self R' T).toExtension)
    (hX : ∀ t : T, h.toRingHom (MvPolynomial.X t) = MvPolynomial.X t) :
    Function.Bijective (Extension.CotangentSpace.map h) := by
  convert ((Generators.self R T).cotangentSpaceBasis.equiv
    (Generators.self R' T).cotangentSpaceBasis (Equiv.refl T)).bijective using 1
  refine congrArg _ ((Generators.self R T).cotangentSpaceBasis.ext fun t => ?_)
  exact (cotangentSpaceMap_cotangentSpaceBasis h hX t).trans
    (Module.Basis.equiv_apply _ t _ (Equiv.refl T)).symm

end NaiveCotangent

end
