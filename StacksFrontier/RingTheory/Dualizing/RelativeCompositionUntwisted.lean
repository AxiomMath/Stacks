module

public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
public import StacksFrontier.RingTheory.Dualizing.RelativeCompositionCoextension
public import StacksFrontier.RingTheory.Dualizing.RelativeCompositionDiagonalSection

/-!
# The untwisted half of the diagonal identification of [stacks 0E2H]

Let `R → A → B` be flat ring maps of finite presentation and let `K_{A/R}` be a relative
dualizing complex for `R → A` in the sense of [stacks 0E2C].  Write `D = A ⊗[R] A` for the
diagonal of `R → A`, `C = B ⊗[R] B`, `C' = B ⊗[A] B`, `Δ : D → A` for the multiplication map,
`δ : D → C` for the map of diagonals and `X_D = K_{A/R} ⊗ᴸ_A D`, `X = K_{A/R} ⊗ᴸ_A C`.

This file proves

`RHom_C(C', X) ≅ C'`

in `D(C)`, the untwisted half of the isomorphism (★) of [stacks 0E2H], and the restriction to
`A` of the isomorphism (*) of [stacks 0E2H] from the monoidality of derived base change.

## Main results

* `Dualizing.internalHomRestrictedAlgebraIso` -- for a ring map `φ : S → T` whose derived
  coextension of scalars carries `X` to the tensor unit of `D(T)`, the internal Hom of `D(S)` out
  of the algebra into `X` is the algebra.
* `Dualizing.nonempty_internalHom_diagonal_iso_diagonal` -- `RHom_D(A, X_D) ≅ A`.
* `Dualizing.nonempty_derivedExtension_restrictedAlgebra_iso_single` -- the derived base change
  along `δ` of the restricted algebra of `Δ` is `C'`.
* `Dualizing.nonempty_internalHom_diagonalQuotient_untwisted` -- **the untwisted half**,
  `RHom_C(C', X) ≅ C'`.
* `Dualizing.nonempty_restrict_diagonalQuotientDerivedHom_of_restrictDiagonalTensorIso` -- the
  restriction to `A` of the isomorphism (*) of [stacks 0E2H], from an identification
  `W|_D ≅ Y_D ⊗ᴸ_D X_D`.
* `Dualizing.restrictDiagonalTensorIso_of_derivedExtension_tensor_iso` -- an identification
  `K ⊗ᴸ_B C ≅ Y ⊗ᴸ_C X` over `C` restricts to that identification over `D`.
* `Dualizing.nonempty_restrict_diagonalQuotientDerivedHom_of_derivedExtension_tensor_iso` -- the
  restriction to `A` of the isomorphism (*) of [stacks 0E2H], from an identification
  `K ⊗ᴸ_B C ≅ Y ⊗ᴸ_C X` over `C`.

## References

* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
* [Stacks Project, Tag 0A71](https://stacks.math.columbia.edu/tag/0A71)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0E2H](https://stacks.math.columbia.edu/tag/0E2H)
-/


@[expose] public section

open CategoryTheory
open CochainComplex.DerivedExtensionScalars
open StacksDraft.DerivedHom
open scoped TensorProduct

universe u

namespace Dualizing

noncomputable section

attribute [local instance] HasDerivedCategory.standard

section Abstract

variable {S T : Type u} [CommRing S] [CommRing T]

/-- **The internal Hom out of the algebra into a coextension-of-scalars unit.**  Let
`φ : S →+* T`, let `E` be a model of derived extension of scalars along `φ` and let `X` be an
object of `D(S)` whose derived coextension of scalars along `φ` is the tensor unit of `D(T)`.
Then the internal Hom of `D(S)` out of the restricted algebra `i_*1_T` into `X` is that algebra. -/
def internalHomRestrictedAlgebraIso (φ : S →+* T)
    (E : TotalDerivedExtensionScalars φ)
    (iStar : DerivedCategory (ModuleCat.{u} T) ⥤ DerivedCategory (ModuleCat.{u} S))
    (adj : iStar ⊣ Dualizing.derivedHom φ) (adjE : E.functor ⊣ iStar)
    (X : DerivedCategory (ModuleCat.{u} S))
    (e : (Dualizing.derivedHom φ).obj X ≅ derivedTensorUnit.{u} T) :
    (derivedHomAdjunctionOverRing S).hom.obj
        (Opposite.op (ProjectionFormula.restrictedAlgebra iStar), X) ≅
      ProjectionFormula.restrictedAlgebra iStar :=
  ((ProjectionFormula.restrictCoextendInternalHomIso φ E iStar adj adjE).app X).symm ≪≫
    iStar.mapIso e

end Abstract

section Composite

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
  [Module.Flat R A] [Algebra.FinitePresentation R A]

/-- The restricted algebra of the diagonal `Δ : A ⊗[R] A → A` is the diagonal `A` in degree zero,
read through `Dualizing.derivedTensorUnitIsoSingleSelf`. -/
def restrictedAlgebraDiagonalIso :
    ProjectionFormula.restrictedAlgebra
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory ≅
      (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) :=
  (ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.lmul' R :
        A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory.mapIso
    (derivedTensorUnitIsoSingleSelf A)

/-- **`RHom_D(A, X_D) ≅ A`.**  Let `R → A` be flat of finite presentation and let
`K_{A/R}` be a relative dualizing complex for it.  Writing `D = A ⊗[R] A` and
`X_D = K_{A/R} ⊗ᴸ_A D`, the internal Hom of `D(D)` out of the diagonal `A` into `X_D` is `A`. -/
theorem nonempty_internalHom_diagonal_iso_diagonal
    (KA : DerivedCategory (ModuleCat.{u} A))
    (hKA : IsRelativeDualizingComplex R A KA) :
    Nonempty
      ((derivedHomAdjunctionOverRing (A ⊗[R] A)).hom.obj
          (Opposite.op (ProjectionFormula.restrictedAlgebra
            (ModuleCat.restrictScalars.{u}
              (Algebra.TensorProduct.lmul' R :
                A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory),
            (diagonalDerivedExtension R A).obj KA) ≅
        ProjectionFormula.restrictedAlgebra
          (ModuleCat.restrictScalars.{u}
            (Algebra.TensorProduct.lmul' R :
              A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory) := by
  have adjE : (totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).functor ⊣
      (ModuleCat.restrictScalars.{u}
        (Algebra.TensorProduct.lmul' R :
          A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory :=
    @derivedExtensionScalarsAdjunction.{u, u, u} (A ⊗[R] A) A _ _ _ _ _
      (totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).functor
      (totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).comparison
      (totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).isLeftDerived
  exact ⟨internalHomRestrictedAlgebraIso
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom
    (totalDerivedExtensionScalars.{u, u, u}
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom)
    (ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory
    (restrictScalarsDerived_adj_derivedHom.{u, u, u}
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).some adjE _
    (hKA.diagonalDerivedHom.some ≪≫ (derivedTensorUnitIsoSingleSelf A).symm)⟩

variable [Module.Flat A B]

omit [Module.Flat R A] [Algebra.FinitePresentation R A] in
/-- **The derived base change of the restricted algebra of the diagonal is `C'`.**  Writing
`C = B ⊗[R] B`, `C' = B ⊗[A] B` and `D = A ⊗[R] A`, derived extension of scalars along the map of
diagonals carries the restricted algebra of `Δ : D → A` to `C'` in degree zero. -/
theorem nonempty_derivedExtension_restrictedAlgebra_iso_single :
    letI := diagonalAlgebra R A B
    letI := diagonalAlgebraSelf R A
    letI := diagonalQuotientAlgebra R A B
    letI := diagonalAlgebraQuot R A B
    letI := diagonalIsScalarTowerSelf R A B
    Nonempty
      ((totalDerivedExtensionScalars.{u, u, u} (diagonalBaseMap R A B).toRingHom).functor.obj
          (ProjectionFormula.restrictedAlgebra
            (ModuleCat.restrictScalars.{u}
              (Algebra.TensorProduct.lmul' R :
                A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} (B ⊗[R] B)) 0).obj
          (ModuleCat.of (B ⊗[R] B) (B ⊗[A] B))) := by
  let := diagonalAlgebra R A B
  let := diagonalAlgebraSelf R A
  let := diagonalQuotientAlgebra R A B
  let := diagonalAlgebraQuot R A B
  let := diagonalIsScalarTowerSelf R A B
  obtain ⟨c⟩ := diagonalDerivedExtensionSingleIso R A B
  refine ⟨(totalDerivedExtensionScalars.{u, u, u}
      (diagonalBaseMap R A B).toRingHom).functor.mapIso
        (restrictedAlgebraDiagonalIso R A ≪≫
          ((ModuleCat.restrictScalars.{u}
            (Algebra.TensorProduct.lmul' R :
              A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategorySingleFunctor 0).app
            (ModuleCat.of A A)) ≪≫ ?_⟩
  exact c

/-- **[stacks 0A6A] (3) at the map of diagonals.**  Let `K_{A/R}` be `R`-perfect.  Writing
`D = A ⊗[R] A`, `C = B ⊗[R] B` and `X_D = K_{A/R} ⊗ᴸ_A D`, the derived-Hom base-change morphism
of [stacks 0E1X] at the pair `(A, X_D)` along `δ : D → C` is invertible. -/
theorem isIso_derivedHomBaseChange_diagonal
    (KA : DerivedCategory (ModuleCat.{u} A))
    (hKA : PseudoCoherence.IsRelativelyPerfect.{u, u, u}
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison R)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R) KA) :
    IsIso (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, u, u}
      (diagonalBaseMap R A B).toRingHom
      (totalDerivedExtensionScalars.{u, u, u} (diagonalBaseMap R A B).toRingHom).functor
      (ProjectionFormula.modelComparison.{u, u} (diagonalBaseMap R A B).toRingHom
        (totalDerivedExtensionScalars.{u, u, u} (diagonalBaseMap R A B).toRingHom))
      (ProjectionFormula.restrictedAlgebra
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory)
      ((diagonalDerivedExtension R A).obj KA)) := by
  refine Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange.{u, u, u} _ _ _ _ _
    (Or.inr (Or.inr (Or.inl ⟨flat_diagonalBaseMap R A B, ?_, ?_⟩)))
  · exact StacksDraft.PseudoCoherence.IsPseudoCoherent.ofIso (isPseudoCoherent_diagonal R A)
      (restrictedAlgebraDiagonalIso R A).symm
  · exact exists_isGE_diagonalDerivedExtension_of_relativelyPerfect R A KA hKA

/-- **The untwisted half of the isomorphism (★) of [stacks 0E2H].**  Let `R → A → B` be flat of
finite presentation and let `K_{A/R}` be a relative dualizing complex for `R → A`.  Writing
`C = B ⊗[R] B`, `C' = B ⊗[A] B` and `X = K_{A/R} ⊗ᴸ_A C`, the internal Hom of `D(C)` out of `C'`
into `X` is `C'`:

`RHom_C(C', X) ≅ C'`. -/
theorem nonempty_internalHom_diagonalQuotient_untwisted
    (KA : DerivedCategory (ModuleCat.{u} A))
    (hKA : IsRelativeDualizingComplex R A KA) :
    letI := diagonalAlgebra R A B
    letI := diagonalAlgebraSelf R A
    letI := diagonalQuotientAlgebra R A B
    letI := diagonalAlgebraQuot R A B
    letI := diagonalIsScalarTowerSelf R A B
    letI : Module.Flat R B := Module.Flat.trans R A B
    Nonempty
      ((derivedHomAdjunctionOverRing (B ⊗[R] B)).hom.obj
          (Opposite.op ((DerivedCategory.singleFunctor (ModuleCat.{u} (B ⊗[R] B)) 0).obj
              (ModuleCat.of (B ⊗[R] B) (B ⊗[A] B))),
            (diagonalDerivedExtension R B).obj
              ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A B)).functor.obj KA)) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} (B ⊗[R] B)) 0).obj
          (ModuleCat.of (B ⊗[R] B) (B ⊗[A] B))) := by
  let := diagonalAlgebra R A B
  let := diagonalAlgebraSelf R A
  let := diagonalQuotientAlgebra R A B
  let := diagonalAlgebraQuot R A B
  let := diagonalIsScalarTowerSelf R A B
  let : Module.Flat R B := Module.Flat.trans R A B
  obtain ⟨eC⟩ := nonempty_derivedExtension_restrictedAlgebra_iso_single R A B
  obtain ⟨eX⟩ := diagonalDerivedExtensionBaseChangeIso R A B KA
  obtain ⟨e1⟩ := nonempty_internalHom_diagonal_iso_diagonal R A KA hKA
  have := isIso_derivedHomBaseChange_diagonal R A B KA hKA.relativelyPerfect
  exact ⟨(derivedHomAdjunctionOverRing (B ⊗[R] B)).hom.mapIso (eC.op.prod eX.symm) ≪≫
    (asIso (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, u, u}
      (diagonalBaseMap R A B).toRingHom
      (totalDerivedExtensionScalars.{u, u, u} (diagonalBaseMap R A B).toRingHom).functor
      (ProjectionFormula.modelComparison.{u, u} (diagonalBaseMap R A B).toRingHom
        (totalDerivedExtensionScalars.{u, u, u} (diagonalBaseMap R A B).toRingHom))
      _ _)).symm ≪≫
    (totalDerivedExtensionScalars.{u, u, u}
      (diagonalBaseMap R A B).toRingHom).functor.mapIso e1 ≪≫ eC⟩

variable [Algebra.FinitePresentation A B]

/-- **The restriction to `A` of the isomorphism (*) of [stacks 0E2H], from an identification over
`D`.**  Let `R → A → B` be flat of finite presentation, let `K_{A/R}` be a relative dualizing
complex for `R → A` and let `K_{B/A}` be perfect relative to `A` in `D(B)`.  Writing
`C = B ⊗[R] B`, `C' = B ⊗[A] B`, `D = A ⊗[R] A`, `W = K ⊗ᴸ_B C`, `Y_D = (K_{B/A} ⊗ᴸ_B C)|_D` and
`X_D = K_{A/R} ⊗ᴸ_A D`, an identification `h`

`W|_D ≅ Y_D ⊗ᴸ_D X_D`

gives the restriction to `A` of (*). -/
theorem nonempty_restrict_diagonalQuotientDerivedHom_of_restrictDiagonalTensorIso
    (KA : DerivedCategory (ModuleCat.{u} A)) (KB K : DerivedCategory (ModuleCat.{u} B))
    (hKA : IsRelativeDualizingComplex R A KA)
    (hKB : PseudoCoherence.IsRelativelyPerfect.{u, u, u}
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison A)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived A) KB)
    (h : letI : Module.Flat R B := Module.Flat.trans R A B
      (ModuleCat.restrictScalars.{u}
            (diagonalBaseMap R A B).toRingHom).mapDerivedCategory.obj
          ((diagonalDerivedExtension R B).obj K) ≅
        (derivedHomAdjunctionOverRing (A ⊗[R] A)).tensor.obj
          ((ModuleCat.restrictScalars.{u}
              (diagonalBaseMap R A B).toRingHom).mapDerivedCategory.obj
            ((diagonalDerivedExtension R B).obj KB),
            (diagonalDerivedExtension R A).obj KA)) :
    letI := diagonalAlgebra R A B
    letI := diagonalAlgebraSelf R A
    letI := diagonalQuotientAlgebra R A B
    letI := diagonalAlgebraQuot R A B
    letI := diagonalIsScalarTower R A B
    letI := diagonalIsScalarTowerSelf R A B
    letI : Module.Flat R B := Module.Flat.trans R A B
    Nonempty
      ((ModuleCat.restrictScalars.{u}
            (algebraMap A (B ⊗[A] B))).mapDerivedCategory.obj
          ((derivedHom.{u, u, u} (diagonalQuotient R A B).toRingHom).obj
            ((diagonalDerivedExtension R B).obj K)) ≅
        (ModuleCat.restrictScalars.{u}
            (algebraMap A (B ⊗[A] B))).mapDerivedCategory.obj
          ((diagonalDerivedExtension A B).obj KB)) := by
  let := diagonalAlgebra R A B
  let := diagonalAlgebraSelf R A
  let := diagonalQuotientAlgebra R A B
  let := diagonalAlgebraQuot R A B
  let := diagonalIsScalarTower R A B
  let := diagonalIsScalarTowerSelf R A B
  let : Module.Flat R B := Module.Flat.trans R A B
  obtain ⟨e1⟩ := nonempty_restrictDerivedHomDiagonalQuotientObjIso R A B
    ((diagonalDerivedExtension R B).obj K)
  obtain ⟨e3⟩ := nonempty_diagonalExtension_iso_derivedHom_derivedTensor R A B KA KB hKA hKB
  obtain ⟨e4⟩ := nonempty_diagonalBaseChangeExtensionIsoFlip R A B
  obtain ⟨e5⟩ := diagonalDerivedExtensionCompIso R A B KB
  exact ⟨e1 ≪≫ (derivedHom.{u, u, u}
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapIso h ≪≫ e3.symm ≪≫
    e4.app ((diagonalDerivedExtension R B).obj KB) ≪≫
    (ModuleCat.restrictScalars.{u}
      (algebraMap A (B ⊗[A] B))).mapDerivedCategory.mapIso e5⟩

omit [Algebra.FinitePresentation R A] [Algebra.FinitePresentation A B] in
/-- **An identification over `C` restricted to `D`.**  Writing `C = B ⊗[R] B`, `D = A ⊗[R] A`,
`Y = K_{B/A} ⊗ᴸ_B C`, `X = K_{A/R} ⊗ᴸ_A C` and `X_D = K_{A/R} ⊗ᴸ_A D`, an identification
`K ⊗ᴸ_B C ≅ Y ⊗ᴸ_C X` over `C` restricts to `(K ⊗ᴸ_B C)|_D ≅ Y|_D ⊗ᴸ_D X_D` over `D`. -/
theorem restrictDiagonalTensorIso_of_derivedExtension_tensor_iso
    (KA : DerivedCategory (ModuleCat.{u} A)) (KB K : DerivedCategory (ModuleCat.{u} B))
    (h : letI : Module.Flat R B := Module.Flat.trans R A B
      (diagonalDerivedExtension R B).obj K ≅
        (derivedHomAdjunctionOverRing (B ⊗[R] B)).tensor.obj
          ((diagonalDerivedExtension R B).obj KB,
            (diagonalDerivedExtension R B).obj
              ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A B)).functor.obj KA))) :
    letI : Module.Flat R B := Module.Flat.trans R A B
    Nonempty
      ((ModuleCat.restrictScalars.{u}
              (diagonalBaseMap R A B).toRingHom).mapDerivedCategory.obj
            ((diagonalDerivedExtension R B).obj K) ≅
          (derivedHomAdjunctionOverRing (A ⊗[R] A)).tensor.obj
            ((ModuleCat.restrictScalars.{u}
                (diagonalBaseMap R A B).toRingHom).mapDerivedCategory.obj
              ((diagonalDerivedExtension R B).obj KB),
              (diagonalDerivedExtension R A).obj KA)) := by
  let : Module.Flat R B := Module.Flat.trans R A B
  obtain ⟨eBC⟩ := diagonalDerivedExtensionBaseChangeIso R A B KA
  refine ⟨(ModuleCat.restrictScalars.{u}
      (diagonalBaseMap R A B).toRingHom).mapDerivedCategory.mapIso
        (h ≪≫ (derivedHomAdjunctionOverRing (B ⊗[R] B)).tensor.mapIso
          ((Iso.refl ((diagonalDerivedExtension R B).obj KB)).prod eBC.symm)) ≪≫ ?_⟩
  exact (ProjectionFormula.derivedProjNatIso.{u, u} (diagonalBaseMap R A B).toRingHom
    (totalDerivedExtensionScalars.{u, u, u} (diagonalBaseMap R A B).toRingHom)
    (ModuleCat.restrictScalars.{u} (diagonalBaseMap R A B).toRingHom).mapDerivedCategory
    (restrictScalarsDerived_adj_derivedHom.{u, u, u}
      (diagonalBaseMap R A B).toRingHom).some
    ((diagonalDerivedExtension R A).obj KA)).app ((diagonalDerivedExtension R B).obj KB)

/-- **The restriction to `A` of the isomorphism (*) of [stacks 0E2H], from an identification over
`C`.**  Let `R → A → B` be flat of finite presentation, let `K_{A/R}` be a relative dualizing
complex for `R → A` and let `K_{B/A}` be perfect relative to `A` in `D(B)`.  Writing
`C = B ⊗[R] B`, an identification

`K ⊗ᴸ_B C ≅ (K_{B/A} ⊗ᴸ_B C) ⊗ᴸ_C (K_{A/R} ⊗ᴸ_A C)`

over `C` gives the restriction to `A` of (*). -/
theorem nonempty_restrict_diagonalQuotientDerivedHom_of_derivedExtension_tensor_iso
    (KA : DerivedCategory (ModuleCat.{u} A)) (KB K : DerivedCategory (ModuleCat.{u} B))
    (hKA : IsRelativeDualizingComplex R A KA)
    (hKB : PseudoCoherence.IsRelativelyPerfect.{u, u, u}
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison A)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived A) KB)
    (h : letI : Module.Flat R B := Module.Flat.trans R A B
      (diagonalDerivedExtension R B).obj K ≅
        (derivedHomAdjunctionOverRing (B ⊗[R] B)).tensor.obj
          ((diagonalDerivedExtension R B).obj KB,
            (diagonalDerivedExtension R B).obj
              ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A B)).functor.obj KA))) :
    letI := diagonalAlgebra R A B
    letI := diagonalAlgebraSelf R A
    letI := diagonalQuotientAlgebra R A B
    letI := diagonalAlgebraQuot R A B
    letI := diagonalIsScalarTower R A B
    letI := diagonalIsScalarTowerSelf R A B
    letI : Module.Flat R B := Module.Flat.trans R A B
    Nonempty
      ((ModuleCat.restrictScalars.{u}
            (algebraMap A (B ⊗[A] B))).mapDerivedCategory.obj
          ((derivedHom.{u, u, u} (diagonalQuotient R A B).toRingHom).obj
            ((diagonalDerivedExtension R B).obj K)) ≅
        (ModuleCat.restrictScalars.{u}
            (algebraMap A (B ⊗[A] B))).mapDerivedCategory.obj
          ((diagonalDerivedExtension A B).obj KB)) :=
  nonempty_restrict_diagonalQuotientDerivedHom_of_restrictDiagonalTensorIso R A B KA KB K hKA hKB
    (restrictDiagonalTensorIso_of_derivedExtension_tensor_iso R A B KA KB K h).some

end Composite

end

end Dualizing

end
