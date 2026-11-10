module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperFlatDualizing.RelativelyPerfect
public import StacksFrontier.AlgebraicGeometry.Duality.ProperFlatDualizing.AbstractEndomorphisms
public import StacksFrontier.AlgebraicGeometry.Duality.ProperFlatDualizing.HomothetyCriterion
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedBelowCompact
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The derived endomorphisms of the relative dualizing complex

Let `Y` be quasi-compact and quasi-separated and `f : X ⟶ Y` proper, flat and of finite
presentation, with relative dualizing complex `ω = a(𝒪_Y)` ([Stacks, Remark 0B6S]). Then the
homothety `𝒪_X ⟶ R𝓗om_{𝒪_X}(ω, ω)` is an isomorphism: [Stacks, Tag 0E4L] (3).

The proof is the source's. For a perfect `E` there is a bijection
`Hom(E ⊗ ω, ω) ≃ Hom(E, 𝒪_X)`, natural in `E`
(`CategoryTheory.MonoidalCategory.RelativeDuality.endHomEquivOfEq`), so the map
`Hom(E, 𝒪_X) ⟶ Hom(E, R𝓗om(ω, ω))` given by the homothety is bijective for every perfect `E`;
`R𝓗om(ω, ω)` has quasi-coherent cohomology since `ω` is pseudo-coherent and bounded below
(clause (1) of the tag), and the perfect objects generate `D_QCoh(𝒪_X)`.

## Main results

* `Stacks.Duality.StandardModel.isIso_derivedSheafHomothety_relativeDualizingComplex`: the
  homothety `𝒪_X ⟶ R𝓗om_{𝒪_X}(ω, ω)` is an isomorphism.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace Stacks.Duality.StandardModel

attribute [local instance 10000] HasDerivedCategory.standard

/-- The bijectivity of `g ↦ g ▷ W ≫ λ_W`, read in the spelling
`DerivedCategory (StructureSheafModules X.sheaf)` of the monoidal structure of
[Stacks, Tag 0FPT]. -/
theorem bijective_spelling {X : Scheme.{u}} (W : DerivedCategory X.Modules)
    (h : letI := monoidal X
      ∀ E : DerivedCategory X.Modules,
        Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E →
          Function.Bijective fun g : E ⟶ 𝟙_ (DerivedCategory X.Modules) => g ▷ W ≫ (λ_ W).hom) :
    letI := Stacks.SheafOfModules.derivedMonoidalStructure X.sheaf
    ∀ E : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules X.sheaf),
      Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} (X := X.toRingedSpace) E →
        Function.Bijective fun g :
          E ⟶ 𝟙_ (DerivedCategory (Stacks.SheafOfModules.StructureSheafModules X.sheaf)) =>
            g ▷ (show DerivedCategory (Stacks.SheafOfModules.StructureSheafModules X.sheaf)
              from W) ≫
            (λ_ (show DerivedCategory (Stacks.SheafOfModules.StructureSheafModules X.sheaf)
              from W)).hom :=
  h

/-- The homothety criterion `Stacks.Duality.StandardModel.isIso_derivedSheafHomothety_of_bijective`
with its bijectivity hypothesis read in the spelling `DerivedCategory X.Modules` of the monoidal
structure `Stacks.Duality.StandardModel.monoidal`. -/
theorem isIso_derivedSheafHomothety_of_bijective_monoidal {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (W : DerivedCategory X.Modules)
    (hW : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) W)
    (hWb : DerivedCategoryB.IsBoundedBelow W)
    (h : letI := monoidal X
      ∀ E : DerivedCategory X.Modules,
        Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E →
          Function.Bijective fun g : E ⟶ 𝟙_ (DerivedCategory X.Modules) => g ▷ W ≫ (λ_ W).hom) :
    IsIso (Stacks.SheafOfModules.derivedSheafHomothety X.sheaf W) :=
  isIso_derivedSheafHomothety_of_bijective
    (show DerivedCategory (Stacks.SheafOfModules.StructureSheafModules X.sheaf) from W) hW hWb
    (bijective_spelling W h)

attribute [local implicit_reducible] structureSheafRing
  StrictlyPerfect.structureSheafOfRings StrictlyPerfect.structureModule
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf TopCat.Sheaf

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- The right dual of a perfect object, for the monoidal structure
`Stacks.Duality.StandardModel.monoidal`. -/
@[instance_reducible]
def hasRightDualOfIsPerfect {Z : Scheme.{u}} (K : DerivedCategory Z.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Z.toRingedSpace) K) :
    @HasRightDual (DerivedCategory Z.Modules) _ (monoidal Z) K :=
  @HasRightDual.mk _ _ (monoidal Z) K (dual K) (exactPairingDual K hK)

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace Y] [QuasiSeparatedSpace Y] [IsProper f]
  [Flat f] [LocallyOfFinitePresentation f]

omit [CompactSpace Y] [QuasiSeparatedSpace Y] in
/-- For a perfect `E` on `X`, the derived pushforward `Rf_* E^∨` of its dual is perfect on `Y`. -/
theorem isPerfect_derivedPushforward_dual (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace)
      ((derivedPushforward f).obj (dual E)) :=
  (ProperFlatBaseChange.isPerfect_derivedPushforward_and_isIso_derivedBaseChangeMap_of_flat f
    ⟨inferInstance, inferInstance, inferInstance⟩ inferInstance inferInstance _
    (Stacks.DerivedQCoh.isPerfect_derivedDual X E hE)).1

section

variable [CompactSpace X] [QuasiSeparatedSpace X]

/-- `Lf^*𝒪_Y ≅ 𝒪_X`. -/
def pullbackUnitIso :
    letI := monoidal X
    letI := monoidal Y
    (pullback f).obj (𝟙_ (DerivedCategory Y.Modules)) ≅ 𝟙_ (DerivedCategory X.Modules) :=
  Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso f.toLRSHom.toShHom

/-- **`Hom(E ⊗ ω, ω) ≃ Hom(E, 𝒪_X)`** for a perfect `E`, the chain of bijections of the third
paragraph of the proof of [Stacks, Tag 0E4L]. -/
def endHomEquiv (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) :
    letI := monoidal X
    (E ⊗ (relativeDualizingComplex f).obj ⟶ (relativeDualizingComplex f).obj) ≃
      (E ⟶ 𝟙_ (DerivedCategory X.Modules)) := by
  letI := monoidal X
  letI := monoidal Y
  letI := symmetric Y
  letI : HasRightDual E := hasRightDualOfIsPerfect E hE
  have hP := isPerfect_derivedPushforward_dual f E hE
  letI : HasRightDual ((derivedPushforward f).obj Eᘁ) := hasRightDualOfIsPerfect _ hP
  have hEω : DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) (E ⊗ (relativeDualizingComplex f).obj) :=
    AlgebraicGeometry.isQuasicoherent_homology_derivedTensor_obj_obj X _ _
      (isQuasicoherent_homology_of_isPerfect E hE) (relativeDualizingComplex f).property
  exact RelativeDuality.endHomEquivOfEq (pullbackAdjunction f)
    (isQuasicoherent_homology_derivedPushforward f)
    (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward f))
    (structureSheaf Y) (Iso.refl _) (pullbackUnitIso f) (curriedTensor_monoidal X)
    (curriedTensor_monoidal Y) E (isQuasicoherent_dual_tensor_pullback f E hE)
    (projectionFormulaDualIso f E hE) (projectionFormulaDualIso_naturality f E hE)
    (isQuasicoherent_homology_derivedPushforward f ⟨_, hEω⟩)
    (Stacks.DerivedQCoh.isQuasicoherent_homology_derivedDual Y _ hP) hEω

/-- **The bijection `Hom(E ⊗ ω, ω) ≃ Hom(E, 𝒪_X)` is natural in the perfect object `E`.** -/
theorem endHomEquiv_naturality {E E' : DerivedCategory X.Modules}
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (hE' : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E') (g : E ⟶ E')
    (y : letI := monoidal X
      E' ⊗ (relativeDualizingComplex f).obj ⟶ (relativeDualizingComplex f).obj) :
    letI := monoidal X
    endHomEquiv f E hE (g ▷ (relativeDualizingComplex f).obj ≫ y) =
      g ≫ endHomEquiv f E' hE' y := by
  let := monoidal X
  let := monoidal Y
  let := symmetric Y
  let : HasRightDual E := hasRightDualOfIsPerfect E hE
  let : HasRightDual E' := hasRightDualOfIsPerfect E' hE'
  have hP := isPerfect_derivedPushforward_dual f E hE
  have hP' := isPerfect_derivedPushforward_dual f E' hE'
  let : HasRightDual ((derivedPushforward f).obj Eᘁ) := hasRightDualOfIsPerfect _ hP
  let : HasRightDual ((derivedPushforward f).obj E'ᘁ) := hasRightDualOfIsPerfect _ hP'
  have hEω_aux : ∀ F : DerivedCategory X.Modules,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) F →
        DerivedCategoryB.derivedCategoryB (A := X.Modules)
          (SheafOfModules.isQuasicoherent X.ringCatSheaf) (F ⊗ (relativeDualizingComplex f).obj) :=
    fun F hF => AlgebraicGeometry.isQuasicoherent_homology_derivedTensor_obj_obj X _ _
      (isQuasicoherent_homology_of_isPerfect F hF) (relativeDualizingComplex f).property
  have hEω := hEω_aux E hE
  have hEω' := hEω_aux E' hE'
  exact RelativeDuality.endHomEquivOfEq_naturality (pullbackAdjunction f)
    (isQuasicoherent_homology_derivedPushforward f)
    (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward f))
    (structureSheaf Y) (Iso.refl _) (pullbackUnitIso f) (curriedTensor_monoidal X)
    (curriedTensor_monoidal Y) g (isQuasicoherent_dual_tensor_pullback f E hE)
    (isQuasicoherent_dual_tensor_pullback f E' hE')
    (projectionFormulaDualIso f E hE) (projectionFormulaDualIso f E' hE')
    (fun M hM => projectionFormulaDualIso_naturality_left f E hE E' hE' (rightAdjointMate g) M hM)
    (projectionFormulaDualIso_naturality f E hE) (projectionFormulaDualIso_naturality f E' hE')
    (isQuasicoherent_homology_derivedPushforward f ⟨_, hEω⟩)
    (isQuasicoherent_homology_derivedPushforward f ⟨_, hEω'⟩)
    (Stacks.DerivedQCoh.isQuasicoherent_homology_derivedDual Y _ hP)
    (Stacks.DerivedQCoh.isQuasicoherent_homology_derivedDual Y _ hP') hEω hEω' y

end

/-- For every perfect `E`, `g ↦ g ⊗ 1_ω` followed by the unit constraint is a bijection
`Hom(E, 𝒪_X) ≃ Hom(E ⊗^L ω, ω)`: the bijection `endHomEquiv` is natural in `E`. -/
theorem bijective_whiskerRight_relativeDualizingComplex
    [CompactSpace X] [QuasiSeparatedSpace X] :
    letI := monoidal X
    ∀ E : DerivedCategory X.Modules,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E →
        Function.Bijective fun g : E ⟶ 𝟙_ (DerivedCategory X.Modules) =>
          g ▷ (relativeDualizingComplex f).obj ≫ (λ_ (relativeDualizingComplex f).obj).hom := by
  let := monoidal X
  have h1 : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)
      (𝟙_ (DerivedCategory X.Modules)) := by
    have hp := Stacks.SheafOfModules.isPerfect_derivedStructureSheaf_space.{u} X.toRingedSpace
    rw [show 𝟙_ (DerivedCategory X.Modules) = RingedSite.derivedStructureSheaf
      (Stacks.SheafOfModules.ringedSite X.sheaf) from
        Stacks.SheafOfModules.tensorUnit_derivedMonoidalStructure X.sheaf]
    exact hp
  exact MonoidalCategory.bijective_whiskerRight_comp_leftUnitor_of_equiv
    (C := DerivedCategory X.Modules)
    (fun E => Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) h1
    (relativeDualizingComplex f).obj (fun E hE => (endHomEquiv f E hE).symm)
    (fun E hE g => by
      rw [Equiv.symm_apply_eq, endHomEquiv_naturality f hE h1, Equiv.apply_symm_apply,
        Category.comp_id])

/-- Let `Y` be a quasi-compact and quasi-separated scheme and `f : X ⟶ Y` a proper, flat
morphism of finite presentation, with relative dualizing complex `ω_{X/Y} = a(𝒪_Y)`
([Stacks, Remark 0B6S]). Then the homothety `𝒪_X ⟶ R𝓗om_{𝒪_X}(ω_{X/Y}, ω_{X/Y})` is an
isomorphism. -/
@[stacks 0E4L "(3)"]
theorem isIso_derivedSheafHomothety_relativeDualizingComplex :
    haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
    IsIso (Stacks.SheafOfModules.derivedSheafHomothety X.sheaf
      (relativeDualizingComplex f).obj) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have hRP := isRelativelyPerfect_relativeDualizingComplex f
  have hloc := AlgebraicGeometry.isLocallyBoundedBelow_of_isPerfectRelativeTo f
    (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) (fun _ => rfl) _ hRP
  obtain ⟨N, hN⟩ := RingedSpace.exists_isGE_of_isLocallyBoundedBelow X.toRingedSpace _ hloc
  have hb : DerivedCategoryB.IsBoundedBelow (relativeDualizingComplex f).obj :=
    ⟨N, fun n hn => (DerivedCategory.isGE_iff _ N).1 hN n hn⟩
  exact isIso_derivedSheafHomothety_of_bijective_monoidal _ hRP.1 hb
    (bijective_whiskerRight_relativeDualizingComplex f)

end Stacks.Duality.StandardModel

end
