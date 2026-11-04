module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Homology.ExtendScalars.IndependentUniverses
public import StacksFrontier.Homology.HomComplex.RHom.HomModuleBaseChange

/-!
# Ext base change along a flat ring map

Let `A → B` be a flat homomorphism of commutative rings, let `P` be a pseudo-coherent object of
the unbounded derived category `D(A)` and let `L` be an object of `D⁺(A)`, that is, an object
bounded below for the standard t-structure. Derived extension of scalars along a flat ring map
is the functor `D(A) ⥤ D(B)` induced by the exact functor `B ⊗_A -`. For every `n : ℤ` the
`B`-module `Ext^n_B(P ⊗_A B, L ⊗_A B)` is the base change `B ⊗_A Ext^n_A(P, L)`.

## Main results

* `Dualizing.nonempty_ext_extendScalars_linearEquiv`: the `B`-linear identification of
  `Ext^n_{D(B)}(P ⊗_A B, L ⊗_A B)` with `B ⊗_A Ext^n_{D(A)}(P, L)`, for `B` flat over `A`,
  `P` pseudo-coherent and `L` bounded below.
* `Dualizing.nonempty_ext_extendScalars_linearEquiv_of_flat`: the same statement for a flat ring
  homomorphism `f : A →+* B`, with the `A`-algebra structure on `B` supplied by `f`.

## References

* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

section FlatBaseChange

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]

/-- Extension of scalars along `algebraMap A B` preserves finite limits when `B` is flat over
`A`. -/
local instance :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) :=
  ModuleCat.extendScalars_preservesFiniteLimits_of_flat _
    (RingHom.flat_algebraMap_iff.mpr inferInstance)

/-- Extension of scalars along `algebraMap A B` preserves finite colimits. -/
local instance :
    PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) :=
  ModuleCat.extendScalars_preservesFiniteColimits _

/-- Let `B` be a flat `A`-algebra, let `P` be a pseudo-coherent object of `D(A)` and let `L` be
an object of `D(A)` bounded below for the standard t-structure. For every `n : ℤ` the `B`-module
of `n`-th extensions between the derived base changes of `P` and `L` is the base change of the
`A`-module of `n`-th extensions between `P` and `L`:
`Ext^n_{D(B)}(P ⊗ᴸ_A B, L ⊗ᴸ_A B) ≃ B ⊗_A Ext^n_{D(A)}(P, L)`. -/
theorem nonempty_ext_extendScalars_linearEquiv
    (P L : DerivedCategory (ModuleCat.{u} A))
    (hP : StacksDraft.PseudoCoherence.IsPseudoCoherent P)
    (hL : (DerivedCategory.TStructure.t).plus L) (n : ℤ) :
    Nonempty (DerivedCategory.Ext
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).mapDerivedCategory.obj P)
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).mapDerivedCategory.obj L) n ≃ₗ[B]
      TensorProduct A B (DerivedCategory.Ext P L n)) := by
  obtain ⟨b, hb⟩ := hL
  have hshift : DerivedCategory.IsGE (L⟦n⟧) (b - n) :=
    DerivedCategory.TStructure.t.isGE_shift L b n (b - n) (by lia)
  have hld :
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).mapDerivedCategory.IsLeftDerivedFunctor
        (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).mapDerivedCategoryFactors.hom
        (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).mapDerivedCategoryFactors
  have hbc : IsIso (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, u, u}
      (algebraMap A B)
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).mapDerivedCategory
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).mapDerivedCategoryFactors.hom
      P (L⟦n⟧)) :=
    Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange.{u, u, u} (algebraMap A B)
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).mapDerivedCategory
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).mapDerivedCategoryFactors.hom
      P (L⟦n⟧)
      (Or.inr (Or.inr (Or.inl
        ⟨RingHom.flat_algebraMap_iff.mpr inferInstance, hP, ⟨b - n, hshift⟩⟩)))
  let e : ((ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).mapDerivedCategory.obj L)⟦n⟧ ≅
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).mapDerivedCategory.obj (L⟦n⟧) :=
    (((ModuleCat.extendScalars.{u, u, u}
      (algebraMap A B)).mapDerivedCategory.commShiftIso n).app L).symm
  exact ⟨(StacksDraft.DerivedHom.HomModuleBaseChange.postcompLinearEquiv B
      ((ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).mapDerivedCategory.obj P) e).trans
    (StacksDraft.DerivedHom.HomModuleBaseChange.homBaseChangeLinearEquiv inferInstance
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).mapDerivedCategory
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).mapDerivedCategoryFactors.hom
      P (L⟦n⟧) hbc)⟩

end FlatBaseChange

/-- `Dualizing.nonempty_ext_extendScalars_linearEquiv` for a flat ring homomorphism
`f : A →+* B`, where `B` carries the `A`-algebra structure defined by `f`. -/
theorem nonempty_ext_extendScalars_linearEquiv_of_flat
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (hf : f.Flat)
    (P L : DerivedCategory (ModuleCat.{u} A))
    (hP : StacksDraft.PseudoCoherence.IsPseudoCoherent P)
    (hL : (DerivedCategory.TStructure.t).plus L) (n : ℤ) :
    letI : Algebra A B := f.toAlgebra
    letI : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) :=
      ModuleCat.extendScalars_preservesFiniteLimits_of_flat f hf
    letI : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} f) :=
      ModuleCat.extendScalars_preservesFiniteColimits f
    Nonempty (DerivedCategory.Ext
        ((ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategory.obj P)
        ((ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategory.obj L) n ≃ₗ[B]
      TensorProduct A B (DerivedCategory.Ext P L n)) :=
  let : Algebra A B := f.toAlgebra
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat f hf
  let : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} f) :=
    ModuleCat.extendScalars_preservesFiniteColimits f
  let : Module.Flat A B := hf
  nonempty_ext_extendScalars_linearEquiv P L hP hL n

end Dualizing

end

