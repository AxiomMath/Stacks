module

public import StacksFrontier.RingTheory.Dualizing.DualExtFlatBaseChange

/-!
# Base change of the Ext modules out of a single module, and the normalizing shift

Let `f : A → B` be a flat homomorphism of commutative rings, let `M` be an `A`-module whose
degree-zero complex `M[0]` is pseudo-coherent, and let `ω` be an object of `D⁺(A)` — for instance
a dualizing complex. Tag 0A6A says that the derived-Hom base-change map is invertible in this
situation, so each extension module base changes; this file specialises that statement to the
case where the source of the `Ext` is a single module, and rewrites the base change
`M[0] ⊗ᴸ_A B` as the single complex `(B ⊗_A M)[0]`, which is what the applications want:

`B ⊗_A Ext^n_A(M, ω) ≃ Ext^n_B(B ⊗_A M, ω ⊗ᴸ_A B)`.

It also records the degree shift that turns a dualizing complex into its normalization: shifting
the target of an `Ext` by `-d` shifts the degree by `+d`.

## Main results

* `Dualizing.nonempty_tensorProduct_ext_linearEquiv` — for `f : A →+* B` flat, `M[0]`
  pseudo-coherent and `ω` bounded below, the `B`-module `B ⊗_A Ext^n_{D(A)}(M[0], ω)` is
  `B`-linearly isomorphic to `Ext^n_{D(B)}((B ⊗_A M)[0], ω ⊗ᴸ_A B)`.
* `Dualizing.nonempty_extendScalars_ext_linearEquiv` — the same statement with the base change
  written as the extension of scalars along `f` of the `A`-module `Ext^n_{D(A)}(M[0], ω)`.
* `Dualizing.nonempty_ext_shift_linearEquiv` — over any commutative ring `R`, and for all
  `d n : ℤ`, the `R`-module `Ext^{d + n}_{D(R)}(P, D⟦-d⟧)` is `Ext^n_{D(R)}(P, D)`.

## Implementation notes

`DerivedCategory.Ext P L n` is `ShiftedHom P L n`, that is `P ⟶ L⟦n⟧`, and morphisms of the
derived category of `ModuleCat.{u} R` live in `Type (u + 1)`, one universe above the modules.
So the `A`-module `Ext^n_{D(A)}(M[0], ω)` is an object of `ModuleCat.{u + 1} A` and the extension
of scalars applied to it is `ModuleCat.extendScalars.{u, u, u + 1} f`, while the extension of
scalars acting on `M` itself and the induced functor on derived categories stay at
`ModuleCat.extendScalars.{u, u, u} f`. Both spellings of extension of scalars therefore occur in
`Dualizing.nonempty_extendScalars_ext_linearEquiv`; they are the same functor `B ⊗_A -` at two
module universes. The tensor-product form
`Dualizing.nonempty_tensorProduct_ext_linearEquiv` is the one to use downstream when the base
change is reached as a tensor product; the extension-of-scalars form is deduced from it.

The underlying module of an extension of scalars is the ordinary tensor product. The available
form of that identification,
`StacksDraft.DerivedHom.HomModuleBaseChange.extendScalarsObjTensorEquiv`, fixes the module
universe to the universe of the rings, so it does not apply at `ModuleCat.{u + 1} A`. The private
`extendScalarsObjTensorEquivAnyModuleUniverse` of this file is that identification with the
module universe freed, and it is the only place where the two forms are compared.

The shift statement is stated with the shift on the target and the compensating shift on the
degree, `Ext^{d + n}(P, D⟦-d⟧) ≃ Ext^n(P, D)`, because that is the direction in which a
normalized dualizing complex `D⟦-d⟧` is presented. It is the shift cancellation
`(D⟦-d⟧)⟦d + n⟧ ≅ D⟦n⟧` of `CategoryTheory.shiftFunctorAdd'`, read on Hom modules.

No `@[stacks]` attribute is attached: tag 0A6A is registered at
`Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange`, and these are re-readings of that
result rather than new registrations.

## References

* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- The underlying `B`-module of an extension of scalars along `algebraMap A B` is the ordinary
tensor product `B ⊗_A N`: the two differ only in the `A`-action carried by `B`.

This is `StacksDraft.DerivedHom.HomModuleBaseChange.extendScalarsObjTensorEquiv` with the module
universe freed from the universe of the rings. That form is stated for `N : ModuleCat.{u} A` with
`A B : Type u`, so it does not apply to an extension group of `D(ModuleCat.{u} A)`, which lives
in `Type (u + 1)`. -/
private def extendScalarsObjTensorEquivAnyModuleUniverse {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (N : ModuleCat.{v} A) :
    ((ModuleCat.extendScalars.{u, u, v} (algebraMap A B)).obj N : Type (max u v)) ≃ₗ[B]
      TensorProduct A B (N : Type v) := by
  letI : Module B (TensorProduct A
      ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) : Type u)
      (N : Type v)) :=
    inferInstanceAs (Module B
      ((ModuleCat.extendScalars.{u, u, v} (algebraMap A B)).obj N : Type (max u v)))
  let eB : ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) : Type u) ≃ₗ[A]
      B :=
    { AddEquiv.refl B with
      map_smul' := fun a x => (Algebra.smul_def (R := A) (A := B) a x).symm }
  let t := TensorProduct.congr eB (LinearEquiv.refl A (N : Type v))
  have key : ∀ (b : B) (w : TensorProduct A
      ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) : Type u)
      (N : Type v)), t (b • w) = b • t w := by
    intro b w
    induction w using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul c m => rfl
    | add w w' hw hw' => rw [smul_add, map_add, map_add, smul_add, hw, hw']
  exact { t.toAddEquiv with map_smul' := key }

/-- **Shifting the target of an `Ext` shifts the degree.** For objects `P` and `D` of the derived
category of `R`-modules and integers `d` and `n`, the `R`-module
`Ext^{d + n}_{D(R)}(P, D⟦-d⟧)` is `Ext^n_{D(R)}(P, D)`.

This is the index convention of a normalized dualizing complex: if `D` is dualizing and `D⟦-d⟧`
is its normalization at a point of dimension `d`, then the degree `n` extension groups of `D`
are the degree `d + n` extension groups of `D⟦-d⟧`. -/
theorem nonempty_ext_shift_linearEquiv {R : Type u} [CommRing R]
    (P D : DerivedCategory (ModuleCat.{u} R)) (d n : ℤ) :
    Nonempty (DerivedCategory.Ext P (D⟦-d⟧) (d + n) ≃ₗ[R] DerivedCategory.Ext P D n) :=
  ⟨StacksDraft.DerivedHom.HomModuleBaseChange.postcompLinearEquiv R P
    ((CategoryTheory.shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} R)) (-d) (d + n) n
      (by omega)).app D).symm⟩

/-- **Tag 0A6A for the extension groups out of a single module.** Let `f : A → B` be a flat
homomorphism of commutative rings, let `M` be an `A`-module whose degree-zero complex `M[0]` is
pseudo-coherent, and let `ω` be an object of `D(A)` bounded below for the standard t-structure.
For every `n : ℤ` the base change `B ⊗_A Ext^n_{D(A)}(M[0], ω)` is the `B`-module
`Ext^n_{D(B)}((B ⊗_A M)[0], ω ⊗ᴸ_A B)`. -/
theorem nonempty_tensorProduct_ext_linearEquiv
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (hf : f.Flat)
    (M : ModuleCat.{u} A) (ω : DerivedCategory (ModuleCat.{u} A))
    (hM : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))
    (hω : (DerivedCategory.TStructure.t).plus ω) (n : ℤ) :
    letI : Algebra A B := f.toAlgebra
    letI : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) :=
      ModuleCat.extendScalars_preservesFiniteLimits_of_flat f hf
    letI : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} f) :=
      ModuleCat.extendScalars_preservesFiniteColimits f
    Nonempty (TensorProduct A B
          (DerivedCategory.Ext ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ω n)
        ≃ₗ[B] DerivedCategory.Ext
          ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj
            ((ModuleCat.extendScalars.{u, u, u} f).obj M))
          ((ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategory.obj ω) n) :=
  let : Algebra A B := f.toAlgebra
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat f hf
  let : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} f) :=
    ModuleCat.extendScalars_preservesFiniteColimits f
  -- Tag 0A6A on extension groups, at the pseudo-coherent object `M[0]` and the bounded below
  -- object `ω`.
  (nonempty_ext_extendScalars_linearEquiv_of_flat f hf _ ω hM hω n).map fun e =>
    -- Extension of scalars is exact, so it carries a single complex to a single complex.
    e.symm.trans (StacksDraft.DerivedHom.HomModuleBaseChange.precompLinearEquiv B
      (((ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategorySingleFunctor 0).app M)
      (((ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategory.obj ω)⟦n⟧)).symm

/-- **Tag 0A6A for the extension groups out of a single module, as an extension of scalars.** The
statement of `Dualizing.nonempty_tensorProduct_ext_linearEquiv` with the base change written as
the extension of scalars of the `A`-module `Ext^n_{D(A)}(M[0], ω)` rather than as a tensor
product.

The two occurrences of `ModuleCat.extendScalars f` sit at different module universes: morphisms
of the derived category of `ModuleCat.{u} A` live in `Type (u + 1)`, so the extension group is an
object of `ModuleCat.{u + 1} A`, while `M` is an object of `ModuleCat.{u} A`. -/
theorem nonempty_extendScalars_ext_linearEquiv
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (hf : f.Flat)
    (M : ModuleCat.{u} A) (ω : DerivedCategory (ModuleCat.{u} A))
    (hM : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))
    (hω : (DerivedCategory.TStructure.t).plus ω) (n : ℤ) :
    letI : Algebra A B := f.toAlgebra
    letI : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) :=
      ModuleCat.extendScalars_preservesFiniteLimits_of_flat f hf
    letI : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} f) :=
      ModuleCat.extendScalars_preservesFiniteColimits f
    Nonempty (((ModuleCat.extendScalars.{u, u, u + 1} f).obj
          (ModuleCat.of A (DerivedCategory.Ext
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ω n)) : Type (u + 1))
        ≃ₗ[B] DerivedCategory.Ext
          ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj
            ((ModuleCat.extendScalars.{u, u, u} f).obj M))
          ((ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategory.obj ω) n) :=
  let : Algebra A B := f.toAlgebra
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) :=
    ModuleCat.extendScalars_preservesFiniteLimits_of_flat f hf
  let : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} f) :=
    ModuleCat.extendScalars_preservesFiniteColimits f
  -- The underlying `B`-module of the extension of scalars is the tensor product.
  (nonempty_tensorProduct_ext_linearEquiv f hf M ω hM hω n).map
    (extendScalarsObjTensorEquivAnyModuleUniverse _).trans

end Dualizing

end
