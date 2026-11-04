module

public import StacksFrontier.AlgebraicGeometry.Perfect.LocalTorDimensionCanonicalCertificate
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObject
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeDerivedSections
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkBridge
public import StacksFrontier.Homology.PseudoCoherent.Basic

/-!
# Relative perfectness on affine schemes is read on global derived sections

Let `f : X ⟶ S` be a morphism of affine schemes which is flat and locally of finite
presentation, and let `E ∈ D_QCoh(𝒪_X)`. Then `E` is `S`-perfect (Stacks 0DI0) exactly when
`RΓ(X, E)` is `Γ(S, 𝒪_S)`-perfect: pseudo-coherent over `Γ(X, 𝒪_X)` and of finite Tor dimension
over `Γ(S, 𝒪_S)`. This is the affine case of Stacks 0DI2, read off its two clauses with the
coverings by `X` and `S` themselves.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_iff_derivedSections_of_isAffine`
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace StacksDraft.TorAmplitude

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine X] [IsAffine S]

/-- **Stacks 0DI2 for affine schemes.** For `f : X ⟶ S` a flat morphism of affine schemes locally
of finite presentation and `E ∈ D_QCoh(𝒪_X)`, `E` is `S`-perfect exactly when `RΓ(X, E)` is
pseudo-coherent and has finite Tor dimension over `Γ(S, 𝒪_S)`. -/
theorem isPerfectRelativeTo_iff_derivedSections_of_isAffine [Flat f]
    [LocallyOfFinitePresentation f] (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent) :
    f.IsPerfectRelativeTo
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage S.toRingedSpace f.base)) E ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherent ((derivedSectionsUnbounded X ⊤).obj E) ∧
        HasFiniteTorDimensionCanonical Γ(S, ⊤)
          ((ModuleCat.restrictScalars f.appTop.hom).mapDerivedCategory.obj
            ((derivedSectionsUnbounded X ⊤).obj E)) := by
  have hpc := pseudoCoherent_derivedSections_tfae f E hE
  have htor :=
    torDimension_derivedSections_tfae f _ (isGenuineRelativeTensorFamily_canonical f) E hE
  have hp₁ := hpc.out 1 2
  have hp₂ := hpc.out 1 3
  have ht₁ := htor.out 1 2
  have ht₂ := htor.out 1 3
  have happ : f.appLE ⊤ ⊤ le_top = f.appTop := f.appLE_eq_app
  refine and_congr ⟨fun h => hp₁.1 h ⊤ (isAffineOpen_top X) ⊤ (isAffineOpen_top S) le_top,
    fun h => hp₂.2 ⟨PUnit, fun _ => ⟨⊤, isAffineOpen_top S⟩, iSup_const,
      fun _ => ⟨PUnit, fun _ => ⟨⊤, isAffineOpen_top X⟩, iSup_const, fun _ => h⟩⟩⟩ ?_
  refine ⟨fun h => ?_, fun h => ht₂.2 ⟨PUnit, fun _ => ⟨⊤, isAffineOpen_top S⟩,
    iSup_const, fun _ => ⟨PUnit, fun _ => ⟨⊤, isAffineOpen_top X⟩, iSup_const,
      fun _ => ⟨le_top, by rwa [happ]⟩⟩⟩⟩
  have := ht₁.1 h ⊤ (isAffineOpen_top X) ⊤ (isAffineOpen_top S) le_top
  rwa [happ] at this

end AlgebraicGeometry.Scheme.Hom

end
