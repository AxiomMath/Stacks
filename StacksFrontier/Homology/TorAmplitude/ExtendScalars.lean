module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.Homology.TorAmplitude.FlatResolution

/-!
# Tor dimension under flat extension of scalars

Let `f : A →+* B` be a homomorphism of commutative rings which makes `B` a flat `A`-module, and
let `M` be an `A`-module of Tor dimension at most `d`. Then the `B`-module `B ⊗_A M` again has
Tor dimension at most `d`. This is Stacks 066M.

## Main results

* `StacksDraft.TorAmplitude.hasFlatRepresentative_extendScalars`: extension of scalars along a
  flat ring map carries a flat representative concentrated in `[a, b]` to one concentrated in
  `[a, b]`.
* `StacksDraft.TorAmplitude.hasTorDimensionLE_extendScalars_of_flat`: flat extension of scalars
  preserves an upper bound on the Tor dimension of a module, Stacks 066M.

## Implementation notes

An upper bound `d` on the Tor dimension of `M` is Tor amplitude in `[-d, 0]` of `M[0]`, for a
certified derived tensor product in the sense of Stacks 0652; the two rings carry two unrelated
certified derived tensor products, since nothing identifies them. The bridge between them is
Stacks 0654, which rewrites Tor amplitude as the existence of a flat representative, a condition
that mentions no derived tensor product at all. Base change is then performed on that
representative: the terms stay flat by `Module.Flat.baseChange`, the strict bounds are preserved
because extension of scalars is applied termwise, and the identification in the derived category
holds because extension of scalars along a flat ring map is exact, so its localisation commutes
with `DerivedCategory.Q` (`CategoryTheory.Functor.mapDerivedCategoryFactors`) and with the
functor placing a module in degree zero
(`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`).

## References

* [Stacks Project, Tag 066M](https://stacks.math.columbia.edu/tag/066M)
-/

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace StacksDraft.TorAmplitude

universe u

attribute [local instance] HasDerivedCategory.standard

@[expose] public section

/-- Extension of scalars along a flat ring map preserves finite limits, hence is exact. -/
public theorem preservesFiniteLimits_extendScalars {A B : Type u} [CommRing A] [CommRing B]
    {f : A →+* B} (hf : f.Flat) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf

/-- Extension of scalars is additive, being a functor that preserves binary products. -/
public theorem additive_extendScalars {A B : Type u} [CommRing A] [CommRing B]
    {f : A →+* B} (hf : f.Flat) :
    (ModuleCat.extendScalars.{u, u, u} f).Additive :=
  have := preservesFiniteLimits_extendScalars hf
  (ModuleCat.extendScalars.{u, u, u} f).additive_of_preserves_binary_products

/-- Extension of scalars along a flat ring map carries a flat representative concentrated in
`[a, b]` to a flat representative concentrated in `[a, b]`.

The terms of the base-changed complex are flat over `B` because flatness is stable under base
change, the strict bounds survive because extension of scalars is applied in each degree, and
the identification in `D(B)` comes from exactness of extension of scalars. -/
public theorem hasFlatRepresentative_extendScalars {A B : Type u} [CommRing A] [CommRing B]
    {f : A →+* B} (hf : f.Flat) (K : DerivedCategory (ModuleCat.{u} A)) (a b : ℤ)
    (hK : HasFlatRepresentative.{u, u} K a b) :
    have := preservesFiniteLimits_extendScalars hf
    have := additive_extendScalars hf
    HasFlatRepresentative.{u, u}
      ((ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategory.obj K) a b := by
  have := preservesFiniteLimits_extendScalars hf
  have := additive_extendScalars hf
  obtain ⟨E, hflat, hGE, hLE, ⟨e⟩⟩ := hK
  let F := ModuleCat.extendScalars.{u, u, u} f
  refine ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj E, ?_, ?_, ?_, ?_⟩
  · intro n
    let : Algebra A B := f.toAlgebra
    have : Module.Flat A (E.X n) := hflat n
    change Module.Flat B (B ⊗[A] (E.X n))
    infer_instance
  · have := hGE
    infer_instance
  · have := hLE
    infer_instance
  · exact ⟨F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app E⟩

/-- The general form of Stacks 066M: let `f : A →+* B` be a flat homomorphism of commutative
rings. If the `A`-module `M` has Tor dimension at most `d`, then the `B`-module `B ⊗_A M` has Tor
dimension at most `d`.

The two Tor-amplitude conditions are taken relative to arbitrary certified derived tensor
products on `D(A)` and on `D(B)`; they are related through the flat-representative
characterisation of Stacks 0654, which refers to neither. The tag sits on the specialisation to
the canonical derived tensor products of `A` and of `B`,
`StacksDraft.TorAmplitude.hasTorDimensionLECanonical_extendScalars_of_flat` in
`StacksFrontier.Homology.TorAmplitude.CanonicalCertificate`. -/
public theorem hasTorDimensionLE_extendScalars_of_flat {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat)
    {derivedTensorA : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A)}
    (comparisonA : ∀ N : ModuleCat.{u} A,
      DerivedCategory.Q ⋙ derivedTensorA.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) ⟶
        (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerivedA : ∀ N : ModuleCat.{u} A,
      (derivedTensorA.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)).IsLeftDerivedFunctor
          (comparisonA N)
          (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)))
    {derivedTensorB : DerivedCategory (ModuleCat.{u} B) ⥤
      DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B)}
    (comparisonB : ∀ N : ModuleCat.{u} B,
      DerivedCategory.Q ⋙ derivedTensorB.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj N) ⟶
        (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerivedB : ∀ N : ModuleCat.{u} B,
      (derivedTensorB.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj N)).IsLeftDerivedFunctor
          (comparisonB N)
          (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)))
    (M : ModuleCat.{u} A) (d : ℕ)
    (hM : HasTorAmplitude derivedTensorA comparisonA isLeftDerivedA
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) (-(d : ℤ)) 0) :
    HasTorAmplitude derivedTensorB comparisonB isLeftDerivedB
      ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj
        ((ModuleCat.extendScalars.{u, u, u} f).obj M)) (-(d : ℤ)) 0 := by
  have := preservesFiniteLimits_extendScalars hf
  have := additive_extendScalars hf
  let F := ModuleCat.extendScalars.{u, u, u} f
  refine (hasTorAmplitude_of_iso ((F.mapDerivedCategorySingleFunctor 0).app M)
    (-(d : ℤ)) 0).mp ?_
  refine (hasTorAmplitude_iff_hasFlatRepresentative comparisonB isLeftDerivedB _ _ _).mpr ?_
  exact hasFlatRepresentative_extendScalars hf _ _ _
    ((hasTorAmplitude_iff_hasFlatRepresentative comparisonA isLeftDerivedA _ _ _).mp hM)

end

end StacksDraft.TorAmplitude
