module

public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.InjectiveHull.FieldExtensionInjectiveDimension
public import StacksFrontier.Homology.TorAmplitude.ExtendScalars
public import StacksFrontier.RingTheory.Dualizing.Complexes.TensorInvertible
public import StacksFrontier.RingTheory.Dualizing.GorensteinRingDualizing
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Dualizing
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatBaseChange
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.PolynomialBaseChangeIso
import all StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange
import all StacksFrontier.RingTheory.Dualizing.UbiquityDualizingComplexes.FlatBaseChange
import all StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatBaseChange

/-!
# Base change of a dualizing complex along an extension of fields

Let `k ⊆ K` be an extension of fields and let `A` be a `k`-algebra of finite type.  For every
dualizing complex `ω` for `A` the derived base change `ω ⊗_A^L A_K` is a dualizing complex for
`A_K = K ⊗_k A`.

## Main results

* `Dualizing.isDualizingComplex_single_self_field` — a field in degree zero is a dualizing
  complex for itself.
* `Dualizing.isDualizingComplex_derivedExtensionScalars_fieldExtension` — [stacks 0E0P].

## Implementation notes

The three defining conditions of `Dualizing.IsDualizingComplex` are checked one at a time for the
base change along `A → A_K`, a flat map because `K` is flat over `k`.

Finiteness of the cohomology modules is `Dualizing.finiteCohomology_extendScalars` and the
homothety condition is `Dualizing.homothetyQuasiIso_extendScalars_of_flat`; both hold for an
arbitrary flat extension of scalars of Noetherian rings and so need nothing of the present
situation beyond flatness.

Finite injective dimension is `Dualizing.finiteInjectiveDimension_mapDerivedCategory`, whose
hypothesis is that extension of scalars carries an injective `A`-module to an `A_K`-module of
finite injective dimension.  That is
`Module.exists_hasInjectiveDimensionLE_tensorProduct_fieldExtension`, and it is the only place
where the field hypothesis on `k` and `K` and the finite type hypothesis on `A` are used: writing
`A` as a quotient of a polynomial algebra `P = k[x_1, …, x_n]`, an injective `A`-module is a
retract of `Hom_P(A, E)` for a suitable injective `P`-module `E`, flat base change identifies
`A_K ⊗_A Hom_P(A, E)` with `Hom_{P_K}(A_K, P_K ⊗_P E)`, and `P_K = K[x_1, …, x_n]` is regular of
global dimension `n`, which bounds the injective dimension by `n`.

Derived base change is read at
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`; for a flat map it agrees
with the derived functor of termwise extension of scalars by
`Dualizing.flatDerivedExtensionTotalIso`, both being left derived functors of termwise extension
of scalars.

The base change is written `K ⊗_k A` with structure map `Algebra.TensorProduct.includeRight`, the
orientation in which this library states flat base change; the source writes `A ⊗_k K`.

### No projection-formula hypothesis is carried

An earlier form of this result went through the flat-base-change map for `φ^!` of [stacks 0BZN]
and therefore carried the projection-formula compatibility `Dualizing.KFlatAlgebraActionEq` of
[stacks 0E2A].  Checking the three conditions directly avoids `φ^!` altogether, so no such
hypothesis appears.

## References

* [Stacks Project, Tag 0E0P](https://stacks.math.columbia.edu/tag/0E0P)
* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local implicit_reducible]
  extensionOfScalarsComplexGeneral extensionOfScalarsComplex

universe u

namespace Dualizing

/-- A field placed in degree zero is a dualizing complex for itself: every module over a field is
injective, so the field has injective dimension zero over itself. -/
theorem isDualizingComplex_single_self_field (k : Type u) [Field k] :
    IsDualizingComplex
      ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)) := by
  rw [isDualizingComplex_single_self_iff]
  refine ⟨0, ?_⟩
  rw [← CategoryTheory.injective_iff_hasInjectiveDimensionLE_zero]
  let : Module.Injective k k := Module.injective_of_isSemisimpleRing k _
  exact Module.injective_object_of_injective_module k k

/-- Derived extension of scalars along a flat homomorphism, computed degreewise, agrees with the
unbounded derived extension of scalars: both are left derived functors of termwise extension of
scalars, which determines them up to a unique isomorphism. -/
@[no_expose]
private def flatDerivedExtensionTotalIso {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) :
    flatDerivedExtension f hf ≅ (totalDerivedExtensionScalars.{u, u, u} f).functor :=
  letI := flatDerivedExtension_isLeftDerivedFunctor f hf
  letI := (totalDerivedExtensionScalars.{u, u, u} f).isLeftDerived
  Functor.leftDerivedUnique _ _ (flatDerivedExtensionComparison f hf)
    (totalDerivedExtensionScalars.{u, u, u} f).comparison
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))

section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

variable {A : Type u} [CommRing A] [Algebra k A] [Algebra.FiniteType k A]

/-- **Stacks Project, Tag 0E0P.** Let `k ⊆ K` be an extension of fields and let `A` be a
`k`-algebra of finite type.  The derived base change of a dualizing complex for `A` along
`A → A_K = K ⊗_k A` is a dualizing complex for `A_K`. -/
@[stacks 0E0P]
theorem isDualizingComplex_derivedExtensionScalars_fieldExtension
    {ω : DerivedCategory (ModuleCat.{u} A)}
    (hω : letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
      IsDualizingComplex ω) :
    letI : IsNoetherianRing (TensorProduct k K A) :=
      Algebra.FiniteType.isNoetherianRing K (TensorProduct k K A)
    IsDualizingComplex
      ((totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.includeRight :
          A →ₐ[k] TensorProduct k K A).toRingHom).functor.obj ω) := by
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  let : IsNoetherianRing (TensorProduct k K A) :=
    Algebra.FiniteType.isNoetherianRing K (TensorProduct k K A)
  set fT := (Algebra.TensorProduct.includeRight : A →ₐ[k] TensorProduct k K A).toRingHom
  have hfTflat : fT.Flat :=
    flat_includeRight (R := k) (A := A) (R' := K) (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : Module.Flat A (TensorProduct k K A) := RingHom.flat_algebraMap_iff.mp hfTflat
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} fT) :=
    StacksDraft.TorAmplitude.preservesFiniteLimits_extendScalars hfTflat
  let : (ModuleCat.extendScalars.{u, u, u} fT).Additive :=
    StacksDraft.TorAmplitude.additive_extendScalars hfTflat
  let : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} fT) := inferInstance
  have hInj : ∀ M : ModuleCat.{u} A, Injective M →
      ∃ n : ℕ, HasInjectiveDimensionLE
        ((ModuleCat.extendScalars.{u, u, u} fT).obj M) n := by
    intro M hM
    let : Injective M := hM
    exact Module.exists_hasInjectiveDimensionLE_tensorProduct_fieldExtension (k := k) (K := K) M
  -- the three conditions, checked for termwise extension of scalars along `A → A_K`
  have hmain : IsDualizingComplex
      ((ModuleCat.extendScalars.{u, u, u} fT).mapDerivedCategory.obj ω) :=
    ⟨finiteInjectiveDimension_mapDerivedCategory _ hInj ω hω.finiteInjectiveDimension,
     finiteCohomology_extendScalars (A := A) (B := TensorProduct k K A) ω hω.finiteCohomology,
     homothetyQuasiIso_extendScalars_of_flat (A := A) (B := TensorProduct k K A) ω hω⟩
  exact isDualizingComplex_of_iso ((flatDerivedExtensionTotalIso fT hfTflat).app ω) hmain

end

end Dualizing

end
