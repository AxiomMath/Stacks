module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.DiagonalSection
public import StacksFrontier.RingTheory.Dualizing.RelativeCompositionTorAmplitude
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Criterion
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.DerivedCoextensionIsDualizing
public import StacksFrontier.Homology.ExtendScalars.AlongARingIsomorphism

/-!
# The diagonal identification of [stacks 0E2H], unconditionally

Let `R → A → B` be flat ring maps of finite presentation, let `K_{A/R}` be a relative dualizing
complex for `R → A` and `K_{B/A}` one for `A → B`.  Write `D = A ⊗[R] A` for the diagonal of
`R → A`, `C = B ⊗[R] B`, `Δ : D → A` for the multiplication map, `X_D = K_{A/R} ⊗ᴸ_A D` and `Y_D`
for `K_{B/A} ⊗ᴸ_B C` read over `D` along `Dualizing.diagonalBaseMap`.  This file proves

`Ext_Δ(Y_D) ≅ Δ^!(Y_D ⊗ᴸ_D X_D)`

in `D(A)`, carrying nothing beyond the relative perfectness of the two complexes and the diagonal
condition of [stacks 0E2C] for `K_{A/R}`.

This is the step of the residue of [stacks 0E2H] that an earlier analysis of this library expected
to cost the compatibility of the projection formula with the counit of [stacks 0GMT],
`Dualizing.ProjectionFormula.ProjCounitCompat`.  It does not: the multiplication map of a diagonal
has a section, either coprojection, so
`Dualizing.nonempty_extendScalars_iso_derivedHom_tensor_of_section` applies and the linearity of
the projection formula over `A` is never needed.  See the module documentation of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.DiagonalSection`.

## Main results

* `Dualizing.isIso_derivedTensorHomDiagonalOverRing_diagonal_composite` -- [stacks 0ATK] (3) at
  the diagonal of `D`, in the spelling of
  `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`.
* `Dualizing.nonempty_diagonalExtension_iso_derivedHom_derivedTensor` -- the identification
  displayed above.

## Implementation notes

`Dualizing.isIso_derivedTensorHomDiagonal_diagonal_composite` already proves [stacks 0ATK] (3) at
the same three objects, but for `StacksDraft.DerivedHom.derivedTensorHomDiagonal`, the diagonal of
the canonical tensor and internal Hom over `D` itself.  The projection formula and the comparison
of restricted coextension with the internal Hom are stated for the independent-universe
bifunctors of `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`, which are the canonical ones
over `ULift D` conjugated by the scalar equivalence of [stacks 0E1W]; no identification of the two
spellings over `D` exists.  So the three hypotheses are transported to `ULift D` instead, where
`Dualizing.isIso_derivedTensorHomDiagonalModel_iff` and
`Dualizing.derivedTensorHomDiagonalModel_eq_overRing` land them.  The transport of the
Tor-amplitude hypothesis is avoided: the fourth situation of [stacks 0ATK],
`Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal_of_relativeKFlat`, asks instead
that the tensor factor be a base change of a bounded-below K-flat complex, and over `ULift D` it
is the base change along `ULift.ringEquiv` of the representative that
`Dualizing.exists_kFlat_flat_representative_restrictScalars_diagonalDerivedExtension` produces
over `D`.

No `@[stacks]` attribute is placed here: the tag of the composition theorem sits on
`Dualizing.isRelativeDualizingComplex_derivedTensorProductOver`, and [stacks 0ATK] sits on
`Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal`.

## References

* [Stacks Project, Tag 0ATK](https://stacks.math.columbia.edu/tag/0ATK)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0E2H](https://stacks.math.columbia.edu/tag/0E2H)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
open StacksDraft.DerivedHom
open scoped TensorProduct

universe u

namespace Dualizing

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- **Derived restriction of scalars preserves a lower bound.**  Restriction of scalars is exact,
so it commutes with the homology of the derived category by
`CategoryTheory.Functor.mapDerivedCategoryCompHomologyFunctorIso`, and an additive functor carries
a zero object to a zero object. -/
theorem isGE_mapDerivedCategory_restrictScalars {S T : Type u} [CommRing S] [CommRing T]
    (f : S →+* T) (K : DerivedCategory (ModuleCat.{u} T)) (b : ℤ) [K.IsGE b] :
    ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj K).IsGE b := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  have hz := (DerivedCategory.isGE_iff K b).1 inferInstance i hi
  refine IsZero.of_iso ?_
    (((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryCompHomologyFunctorIso i).app K)
  rw [IsZero.iff_id_eq_zero]
  dsimp only [Functor.comp_obj]
  rw [← (ModuleCat.restrictScalars.{u} f).map_id, hz.eq_of_src (𝟙 _) 0, Functor.map_zero]

/-- **The unit module of `D(A)` is `A`.**  The tensor unit of the independent-universe
tensor--Hom adjunction is `ULift A` read along `ULift.ringEquiv`, which at a module universe equal
to the ring universe is `A` itself. -/
def derivedTensorUnitModuleIsoSelf (A : Type u) [CommRing A] :
    derivedTensorUnitModule.{u, u} A ≅ ModuleCat.of A A :=
  (AddEquiv.toLinearEquiv (M := (derivedTensorUnitModule.{u, u} A : Type u)) (M₂ := A)
    ULift.ringEquiv.toAddEquiv (fun _ _ => rfl)).toModuleIso

/-- **The tensor unit of `D(A)` is `A` in degree zero.**
`Dualizing.derivedTensorUnitIsoSingle` with its unit module identified by
`Dualizing.derivedTensorUnitModuleIsoSelf`. -/
def derivedTensorUnitIsoSingleSelf (A : Type u) [CommRing A] :
    derivedTensorUnit.{u, u} A ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) :=
  derivedTensorUnitIsoSingle.{u, u} A ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso
      (derivedTensorUnitModuleIsoSelf A)

section Composite

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
  [Module.Flat R A] [Module.Flat A B]
  [Algebra.FinitePresentation R A] [Algebra.FinitePresentation A B]

/-- **[stacks 0ATK] (3) at the diagonal of `D = A ⊗[R] A`, in the independent-universe
spelling.**  This is `Dualizing.isIso_derivedTensorHomDiagonal_diagonal_composite` for
`Dualizing.derivedTensorHomDiagonalOverRing` instead of for the canonical diagonal over `D`; see
the module documentation for why the two have to be proved separately and how the hypotheses are
transported. -/
theorem isIso_derivedTensorHomDiagonalOverRing_diagonal_composite
    (KA : DerivedCategory (ModuleCat.{u} A)) (KB : DerivedCategory (ModuleCat.{u} B))
    (hKA : PseudoCoherence.IsRelativelyPerfect.{u, u, u}
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison R)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R) KA)
    (hKB : PseudoCoherence.IsRelativelyPerfect.{u, u, u}
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison A)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived A) KB) :
    letI : Module.Flat R B := Module.Flat.trans R A B
    IsIso (derivedTensorHomDiagonalOverRing.{u, u}
      ((ModuleCat.restrictScalars.{u}
          (diagonalBaseMap R A B).toRingHom).mapDerivedCategory.obj
        ((diagonalDerivedExtension R B).obj KB))
      ((diagonalDerivedExtension R A).obj KA)
      (ProjectionFormula.restrictedAlgebra.{u, u}
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory)) := by
  let : Module.Flat R B := Module.Flat.trans R A B
  obtain ⟨E, a, hEflat, -, hEGE, ⟨eE⟩⟩ :=
    exists_kFlat_flat_representative_restrictScalars_diagonalDerivedExtension R A B KB hKB
  obtain ⟨b, hb⟩ := exists_isGE_diagonalDerivedExtension_of_relativelyPerfect R A KA hKA
  have := hb
  rw [← derivedTensorHomDiagonalModel_eq_overRing.{u, u},
    isIso_derivedTensorHomDiagonalModel_iff.{u, u}]
  refine Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal_of_relativeKFlat
    (ULift.ringEquiv : ULift.{u} (A ⊗[R] A) ≃+* (A ⊗[R] A)).symm.toRingHom _ _ _ a
    ⟨E, hEGE, hEflat, ⟨?_⟩⟩ ?_ ⟨b, isGE_mapDerivedCategory_restrictScalars _ _ b⟩
  · let U := ModuleCat.restrictScalars.{u}
      (ULift.ringEquiv : ULift.{u} (A ⊗[R] A) ≃+* (A ⊗[R] A)).toRingHom
    exact U.mapDerivedCategory.mapIso eE ≪≫ U.mapDerivedCategoryFactors.app E ≪≫
      DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
        (ModuleCat.extendScalarsIsoRestrictScalarsSymm
          (ULift.ringEquiv : ULift.{u} (A ⊗[R] A) ≃+* (A ⊗[R] A)).symm)
        (ComplexShape.up ℤ)).symm.app E)
  · refine (StacksDraft.PseudoCoherence.pseudoCoherent_iff_of_ringEquiv
      (ULift.ringEquiv : ULift.{u} (A ⊗[R] A) ≃+* (A ⊗[R] A)) _).2.mp ?_
    exact StacksDraft.PseudoCoherence.IsPseudoCoherent.ofIso (isPseudoCoherent_diagonal R A)
      ((ModuleCat.restrictScalars.{u}
        (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory.mapIso
          (derivedTensorUnitIsoSingleSelf A).symm)

/-- **`Ext_Δ(Y_D) ≅ Δ^!(Y_D ⊗ᴸ_D X_D)`, unconditionally.**  Let `R → A → B` be flat of finite
presentation, let `K_{A/R}` be a relative dualizing complex for `R → A` and let `K_{B/A}` be
perfect relative to `A` in `D(B)`.  Writing `D = A ⊗[R] A`, `X_D = K_{A/R} ⊗ᴸ_A D` and `Y_D` for
`K_{B/A} ⊗ᴸ_B (B ⊗[R] B)` read over `D`, derived extension of scalars along the multiplication map
carries `Y_D` to derived coextension of scalars of `Y_D ⊗ᴸ_D X_D`.

Nothing is carried.  The invertibility input is [stacks 0ATK] (3) at the diagonal of the single
ring `D`, which `Dualizing.isIso_derivedTensorHomDiagonalOverRing_diagonal_composite` supplies, and
the descent from `D(D)` to `D(A)` is the section of the multiplication map, not a linearity of the
projection formula; see the module documentation. -/
theorem nonempty_diagonalExtension_iso_derivedHom_derivedTensor
    (KA : DerivedCategory (ModuleCat.{u} A)) (KB : DerivedCategory (ModuleCat.{u} B))
    (hKA : IsRelativeDualizingComplex R A KA)
    (hKB : PseudoCoherence.IsRelativelyPerfect.{u, u, u}
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison A)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived A) KB) :
    letI : Module.Flat R B := Module.Flat.trans R A B
    Nonempty ((totalDerivedExtensionScalars.{u, u, u}
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).functor.obj
        ((ModuleCat.restrictScalars.{u}
            (diagonalBaseMap R A B).toRingHom).mapDerivedCategory.obj
          ((diagonalDerivedExtension R B).obj KB)) ≅
      (derivedHom.{u, u} (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
        ((derivedHomAdjunctionOverRing.{u, u} (A ⊗[R] A)).tensor.obj
          ((ModuleCat.restrictScalars.{u}
              (diagonalBaseMap R A B).toRingHom).mapDerivedCategory.obj
            ((diagonalDerivedExtension R B).obj KB),
            (diagonalDerivedExtension R A).obj KA))) := by
  let : Module.Flat R B := Module.Flat.trans R A B
  set Δ := (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom with hΔ
  have adjE : (totalDerivedExtensionScalars.{u, u, u} Δ).functor ⊣
      (ModuleCat.restrictScalars.{u} Δ).mapDerivedCategory :=
    @derivedExtensionScalarsAdjunction.{u, u, u} (A ⊗[R] A) A _ _ Δ _ _
      (totalDerivedExtensionScalars.{u, u, u} Δ).functor
      (totalDerivedExtensionScalars.{u, u, u} Δ).comparison
      (totalDerivedExtensionScalars.{u, u, u} Δ).isLeftDerived
  refine nonempty_extendScalars_iso_derivedHom_tensor_of_section Δ
    (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)
    (lmul'_comp_includeLeftRingHom R A) _
    (restrictScalarsDerived_adj_derivedHom.{u, u, u} Δ).some adjE _ _
    (hKA.diagonalDerivedHom.some ≪≫ (derivedTensorUnitIsoSingleSelf A).symm)
    (isIso_derivedTensorHomDiagonalOverRing_diagonal_composite R A B KA KB
      hKA.relativelyPerfect hKB)

end Composite

end

end Dualizing

end
