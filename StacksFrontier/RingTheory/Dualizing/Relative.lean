module

public import Mathlib.RingTheory.FinitePresentation
public import StacksCore.RingTheory.FiniteStability
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.KInjective.ChangeOfRings
public import StacksFrontier.Homology.PseudoCoherent.RelativelyPerfect
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality

/-!
# Relative dualizing complexes (Stacks chapter Dualizing Complexes)

Let `R → A` be a flat ring map of finite presentation. A *relative dualizing complex* for
`R → A` is an object `K` of `D(A)` which is perfect relative to `R` and whose derived base
change along the left coprojection `A → A ⊗[R] A` has derived Hom from the diagonal
`A ⊗[R] A → A` isomorphic to `A` placed in degree zero:
`RHom_{A ⊗[R] A}(A, K ⊗ᴸ_A (A ⊗[R] A)) ≅ A[0]`.

Relative perfectness is `PseudoCoherence.IsRelativelyPerfect`, evaluated at the canonical
derived tensor product over `R`, and derived Hom from the diagonal is the derived
coextension-of-scalars functor `Dualizing.derivedHom` along multiplication `A ⊗[R] A → A`.

Because `A` is flat over `R`, the left coprojection `A → A ⊗[R] A` is flat, so extension of
scalars along it is exact and its derived functor is computed termwise on any complex
representing `K`, with no K-flatness hypothesis.

## Main definitions

* `Dualizing.diagonalDerivedExtension` — the canonical derived extension of scalars
  `K ↦ K ⊗ᴸ_A (A ⊗[R] A)` along the left coprojection.
* `Dualizing.IsRelativeDualizingComplex` — the predicate of being a relative dualizing complex.

## Main results

* `Dualizing.includeLeftRingHom_flat` — flatness of the left coprojection `A → A ⊗[R] A`.
* `Dualizing.diagonalDerivedExtensionIso` — the canonical extension agrees with termwise
  extension of any representative.
* `Dualizing.diagonalDerivedHomIso`, `Dualizing.diagonalDerivedHom_isomorphic_iff` — the
  corresponding comparisons after applying derived Hom from the diagonal.
* `Dualizing.isRelativeDualizingComplex_iff` — the predicate unfolded into its two defining
  conditions.

## References

* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0DHS](https://stacks.math.columbia.edu/tag/0DHS)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

noncomputable section

/-- If `A` is flat over `R`, the left coprojection `A → A ⊗[R] A` is flat. -/
lemma includeLeftRingHom_flat (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] :
    (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A).Flat := by
  let f : A →+* A ⊗[R] A := Algebra.TensorProduct.includeLeftRingHom
  show f.Flat
  rw [RingHom.Flat, show f.toAlgebra = (inferInstance : Algebra A (A ⊗[R] A)) from
    Algebra.algebra_ext _ _ fun _ => rfl]
  infer_instance

/-- The canonical derived extension of scalars along the left coprojection
`A → A ⊗[R] A`. This is `K ↦ K ⊗[A]ᴸ (A ⊗[R] A)`. -/
@[implicit_reducible]
noncomputable def diagonalDerivedExtension (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] :
    DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} (A ⊗[R] A)) := by
  let F := ModuleCat.extendScalars.{u, u, u}
    (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)
  let : Limits.PreservesFiniteLimits F :=
    extendScalars_preservesFiniteLimits_of_flat' _ (includeLeftRingHom_flat R A)
  let : Limits.PreservesColimitsOfSize.{0, 0} F :=
    (ModuleCat.extendRestrictScalarsAdj
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).leftAdjoint_preservesColimits
  let : Limits.PreservesFiniteColimits F :=
    Limits.PreservesColimitsOfSize.preservesFiniteColimits F
  let : F.Additive := Functor.additive_of_preserves_binary_products F
  exact F.mapDerivedCategory

/-- The canonical derived extension agrees with termwise extension of every representative
of a derived object; no K-flatness assumption on the representative is needed. -/
noncomputable def diagonalDerivedExtensionIso (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] (K : DerivedCategory (ModuleCat.{u} A))
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (e : DerivedCategory.Q.obj P ≅ K) :
    (diagonalDerivedExtension R A).obj K ≅
      DerivedCategory.Q.obj
        ((CochainComplex.extendScalars
          (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).obj P) := by
  let F := ModuleCat.extendScalars.{u, u, u}
    (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)
  let : Limits.PreservesFiniteLimits F :=
    extendScalars_preservesFiniteLimits_of_flat' _ (includeLeftRingHom_flat R A)
  let : Limits.PreservesColimitsOfSize.{0, 0} F :=
    (ModuleCat.extendRestrictScalarsAdj
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).leftAdjoint_preservesColimits
  let : Limits.PreservesFiniteColimits F :=
    Limits.PreservesColimitsOfSize.preservesFiniteColimits F
  let : F.Additive := Functor.additive_of_preserves_binary_products F
  exact (diagonalDerivedExtension R A).mapIso e.symm ≪≫ F.mapDerivedCategoryFactors.app P

/-- Applying derived Hom from the diagonal to `diagonalDerivedExtensionIso` identifies the
canonical derived-Hom object with that computed from any representative. -/
noncomputable def diagonalDerivedHomIso (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] (K : DerivedCategory (ModuleCat.{u} A))
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (e : DerivedCategory.Q.obj P ≅ K) :
    (derivedHom.{u, u}
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
        ((diagonalDerivedExtension R A).obj K) ≅
      (derivedHom.{u, u}
        (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
          (DerivedCategory.Q.obj
            ((CochainComplex.extendScalars
              (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).obj P)) :=
  (derivedHom.{u, u}
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapIso
      (diagonalDerivedExtensionIso R A K P e)

/-- The derived-Hom object of the canonical extension is isomorphic to `L` exactly when the
derived-Hom object computed from any representative is isomorphic to `L`. -/
theorem diagonalDerivedHom_isomorphic_iff (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] (K L : DerivedCategory (ModuleCat.{u} A))
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (e : DerivedCategory.Q.obj P ≅ K) :
    Nonempty
        ((derivedHom.{u, u}
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
            ((diagonalDerivedExtension R A).obj K) ≅ L) ↔
      Nonempty
        ((derivedHom.{u, u}
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
            (DerivedCategory.Q.obj
              ((CochainComplex.extendScalars
                (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).obj P)) ≅ L) :=
  ⟨fun ⟨h⟩ => ⟨(diagonalDerivedHomIso R A K P e).symm ≪≫ h⟩,
    fun ⟨h⟩ => ⟨diagonalDerivedHomIso R A K P e ≪≫ h⟩⟩

/-- **Stacks Project, Tag 0E2C.** A relative dualizing complex for a flat, finitely
presented map `R → A` is an `R`-perfect object `K` of `D(A)` such that
`RHom_{A ⊗[R] A}(A, K ⊗[A]ᴸ (A ⊗[R] A))` is isomorphic to `A`. -/
@[stacks 0E2C]
structure IsRelativeDualizingComplex (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K : DerivedCategory (ModuleCat.{u} A)) : Prop where
  /-- The complex is perfect relative to `R`. -/
  relativelyPerfect : PseudoCoherence.IsRelativelyPerfect
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
    (StacksDraft.TorAmplitude.canonicalTensorComparison R)
    (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R) K
  /-- Derived Hom from the diagonal into the derived base change of `K` is `A[0]`. -/
  diagonalDerivedHom :
    Nonempty
      ((derivedHom.{u, u}
        (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
          ((diagonalDerivedExtension R A).obj K) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))

/-- Characterization of a relative dualizing complex by relative perfectness and the
canonical diagonal derived-Hom condition. -/
theorem isRelativeDualizingComplex_iff (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K : DerivedCategory (ModuleCat.{u} A)) :
    IsRelativeDualizingComplex R A K ↔
      (PseudoCoherence.IsRelativelyPerfect
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
        (StacksDraft.TorAmplitude.canonicalTensorComparison R)
        (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R) K ∧
        Nonempty
          ((derivedHom.{u, u}
            (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
              ((diagonalDerivedExtension R A).obj K) ≅
            (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))) :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

end

end Dualizing
