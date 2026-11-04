module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexRigidity
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexChartConverse
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulRegularRightAdjoint.SheafHom
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BoundedBelow
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.StandardModelTwistedInverseImage
public import StacksFrontier.Homology.DerivedCategory.Bridge.Pullback
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.Composition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.FinitePresentation

/-!
# The map `ξ` of the relative dualizing complex of a proper flat morphism

Let `S` be a quasi-compact and quasi-separated scheme and `f : X ⟶ S` proper, flat and of finite
presentation, with relative dualizing complex `ω_{X/S}^• = a(𝒪_S)` ([Stacks, Remark 0B6S]). As `f`
is separated the diagonal `Δ : X ⟶ X ×_S X` is a closed immersion, so `W = X ×_S X` is an open as
in [Stacks, Definition 0E2T]. Let `c` be the right adjoint of `RΔ_*` of [Stacks, Tag 0A9E].
[Stacks, Tag 0E2Q] is an isomorphism `𝒪_X ≅ c(L pr₁^*ω_{X/S}^•)`, and its adjoint is the map

`ξ : Δ_*𝒪_X ⟶ L pr₁^*ω_{X/S}^•`

with which [Stacks, Tag 0E2Z] makes `ω_{X/S}^•` a relative dualizing complex. This file builds
`ξ` at the model of [Stacks, Definition 0E2T].

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.ofIsSeparated` — for `f` separated, the open
  `W = X ×_S X` with `Δ` the relative diagonal.
* `Stacks.Duality.structureSheafIsoExactSupportPullbackFst` — [Stacks, Tag 0E2Q] with `c` read
  as `R ℰom(𝒪_X, -)` ([Stacks, Tag 0A9X]): `𝒪_X ≅ R ℰom(𝒪_X, L pr₁^*ω_{X/S}^•)`.
* `Stacks.Duality.diagonalExactSupportRelativeDualizingComplexIso` — the same at the standard
  model, for `ω_{X/S}^•` the standard-model `a(𝒪_S)` of
  `Stacks.Duality.StandardModel.relativeDualizingComplex`.
* `Stacks.Duality.relativeDualizingComplexDiagonalMap` — `ξ`, the adjoint of that isomorphism
  under `Δ_* ⊣ R ℰom(𝒪_X, -)` ([Stacks, Tag 0A76]).

## Implementation notes

[Stacks, Tag 0E2Q] is proved at the locally small model, the only model at which `c` exists as
the right adjoint of `RΔ_*` on `D_QCoh`. The isomorphism is read off the bounded-below object
`L pr₁^*ω_{X/S}^•` ([Stacks, Tag 0A9I] together with flat base change [Stacks, Tag 0AAB]) through
[Stacks, Tag 0A9X], which identifies `c` with derived sheaf Hom with exact support there, the
diagonal of a flat morphism locally of finite presentation being pseudo-coherent. It is then
carried to the standard model, at which relative dualizing complexes are defined, by the model
comparison of `R ℰom(𝒪_X, -)`, of `L pr₁^*`, of `𝒪_X[0]` and of `a(𝒪_S)`.

## References

* [Stacks Project, Tag 0E2Z](https://stacks.math.columbia.edu/tag/0E2Z)
* [Stacks Project, Tag 0E2Q](https://stacks.math.columbia.edu/tag/0E2Q)
* [Stacks Project, Tag 0A9X](https://stacks.math.columbia.edu/tag/0A9X)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open Stacks.Duality.DerivedPushforward

universe u

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

/-- **The diagonal open of a separated morphism**: `W = X ×_S X`, through which the relative
diagonal factors as the closed immersion `Δ_{X/S}` itself. -/
@[simps]
def ofIsSeparated {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] : DiagonalOpen f where
  W := pullback f f
  ι := 𝟙 _
  isOpenImmersion := inferInstance
  diag := pullback.diagonal f
  isClosedImmersion := inferInstance
  fac := Category.comp_id _

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

namespace Stacks.Duality

/-- **The diagonal of a flat morphism locally of finite presentation is pseudo-coherent**:
`pr₁ ∘ Δ = id`, `pr₁` is flat and locally of finite presentation, hence pseudo-coherent, and
[Stacks, Tag 0683] cancels it. -/
theorem pseudoCoherent_pullbackDiagonal {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] : PseudoCoherent (pullback.diagonal f) := by
  have : PseudoCoherent (pullback.diagonal f ≫ pullback.fst f f) := by
    rw [pullback.diagonal_fst]; infer_instance
  exact pseudoCoherent_of_comp _ (pullback.fst f f)

section LocallySmall

variable {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S] [IsProper f]
  [Flat f] [LocallyOfFinitePresentation f] [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace (pullback f f : Scheme.{u})] [QuasiSeparatedSpace (pullback f f : Scheme.{u})]

/-- `L pr₁^*ω_{X/S}^•` in `D_QCoh(𝒪_{X ×_S X})`, at the locally small model, for
`ω_{X/S}^• = a(𝒪_S)` the relative dualizing complex of [Stacks, Remark 0B6S]. -/
abbrev pullbackFstRelativeDualizingComplex :
    quasiCoherentDerivedCategory (pullback f f : Scheme.{u}) :=
  (quasiCoherentDerivedPullback' (pullback.fst f f)).obj
    ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
      (derivedStructureSheaf S))

omit [CompactSpace (pullback f f : Scheme.{u})]
  [QuasiSeparatedSpace (pullback f f : Scheme.{u})] in
/-- **`L pr₁^*ω_{X/S}^•` is bounded below.** By flat base change ([Stacks, Tag 0AAB]) it is
`a'(𝒪_X)` for `a'` the right adjoint for `pr₂`, and `a'` preserves `D^+` ([Stacks, Tag 0A9I]). -/
theorem isBoundedBelow_pullbackFstRelativeDualizingComplex :
    DerivedCategoryB.IsBoundedBelow (pullbackFstRelativeDualizingComplex f).obj := by
  have : CompactSpace (pullback f f : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f f)
  have : QuasiSeparatedSpace (pullback f f : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f f)
  have e := twistedInverseImageStructureSheafBaseChangeIso (IsPullback.of_hasPullback f f)
  have hO : DerivedCategoryB.IsBoundedBelow (derivedStructureSheaf X).obj :=
    KoszulRegular.isBoundedBelow_singleFunctor_obj _
  obtain ⟨n, hn⟩ := isBoundedBelow_twistedInverseImage_obj (pullback.snd f f)
    (derivedStructureSheaf X) hO
  exact ⟨n, fun i hi => (hn i hi).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso ((ObjectProperty.ι _).mapIso e)).symm⟩

/-- **[Stacks, Tag 0A9X] at `L pr₁^*ω_{X/S}^•`**:
`c(L pr₁^*ω_{X/S}^•) ≅ R ℰom(𝒪_X, L pr₁^*ω_{X/S}^•)`, through the canonical comparison
`Stacks.Duality.LocallySmall.rightAdjointToDerivedSheafHom` (the mate of the counit of `c`),
invertible on the bounded-below object `L pr₁^*ω_{X/S}^•`. -/
def diagonalTwistedInverseImageIsoExactSupport :
    ((twistedInverseImage (pullback.diagonal f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f))).obj
        (pullbackFstRelativeDualizingComplex f)).obj ≅
      (LocallySmall.derivedSheafHomExactSupport (pullback.diagonal f)).obj
        (pullbackFstRelativeDualizingComplex f).obj :=
  haveI := LocallySmall.isIso_rightAdjointToDerivedSheafHom_app (pullback.diagonal f)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f)) _
    (twistedInverseImageAdjunction (pullback.diagonal f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f)))
    (pseudoCoherent_pullbackDiagonal f)
    ⟨pullbackFstRelativeDualizingComplex f, isBoundedBelow_pullbackFstRelativeDualizingComplex f⟩
  asIso ((LocallySmall.rightAdjointToDerivedSheafHom (pullback.diagonal f)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f)) _
    (twistedInverseImageAdjunction (pullback.diagonal f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (pullback.diagonal f)))).app
    (pullbackFstRelativeDualizingComplex f))

/-- **[Stacks, Tag 0E2Q] with `c = R ℰom(𝒪_X, -)`**: the isomorphism `𝒪_X ≅ c(L pr₁^*ω_{X/S}^•)` of
`Stacks.Duality.structureSheafIsoDiagonalTwistedInverseImagePullbackFst` followed by the
identification of [Stacks, Tag 0A9X], at the locally small model. -/
def structureSheafIsoExactSupportPullbackFst :
    (derivedStructureSheaf X).obj ≅
      (LocallySmall.derivedSheafHomExactSupport (pullback.diagonal f)).obj
        (pullbackFstRelativeDualizingComplex f).obj :=
  (ObjectProperty.ι _).mapIso (structureSheafIsoDiagonalTwistedInverseImagePullbackFst f) ≪≫
    diagonalTwistedInverseImageIsoExactSupport f

end LocallySmall

section Standard

variable {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S] [IsProper f]
  [Flat f] [LocallyOfFinitePresentation f] [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace (pullback f f : Scheme.{u})] [QuasiSeparatedSpace (pullback f f : Scheme.{u})]

omit [CompactSpace S] [QuasiSeparatedSpace S] [IsProper f] [Flat f]
  [LocallyOfFinitePresentation f] [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace (pullback f f : Scheme.{u})] [QuasiSeparatedSpace (pullback f f : Scheme.{u})] in
/-- **`R ℰom(𝒪_X, L pr₁^* -)` at the two models.** For `K` in `D(𝒪_X)` at the standard model,
the comparison equivalence carries `R ℰom(𝒪_X, L pr₁^*K)` (computed at the standard model) to
`R ℰom(𝒪_X, L pr₁^*K)` computed at the locally small model on the image of `K`. -/
def diagonalExactSupportModelIso [IsSeparated f]
    (K : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _)) :
    (Scheme.Modules.derivedModelEquiv X).functor.obj
        ((Scheme.Hom.DiagonalOpen.ofIsSeparated f).diagonalExactSupport K) ≅
      (LocallySmall.derivedSheafHomExactSupport (pullback.diagonal f)).obj
        ((derivedPullback (pullback.fst f f)).obj
          ((Scheme.Modules.derivedModelEquiv X).functor.obj K)) :=
  (AnyModel.derivedSheafHomExactSupportModelIso
      (Scheme.Hom.DiagonalOpen.ofIsSeparated f).diagQuotient
      (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
      (SheafOfModules.hasDerivedCategory _) (SheafOfModules.hasDerivedCategory _)).app
      ((Scheme.Hom.DiagonalOpen.ofIsSeparated f).derivedPullbackProj K) ≪≫
    (LocallySmall.derivedSheafHomExactSupport (pullback.diagonal f)).mapIso
      ((StacksDraft.DerivedModel.schemeDerivedPullbackStandardModelEquivIso
          (𝟙 _ ≫ pullback.fst f f)).app K ≪≫
        eqToIso (congrArg (fun g => (derivedPullback g).obj
          ((Scheme.Modules.derivedModelEquiv X).functor.obj K)) (Category.id_comp _)))

/-- **[Stacks, Tag 0E2Q] at the model of relative dualizing complexes**:
`R ℰom(𝒪_X, L pr₁^*ω_{X/S}^•) ≅ 𝒪_X[0]` in `D(𝒪_X)` at the standard model, for
`ω_{X/S}^• = a(𝒪_S)` (`Stacks.Duality.StandardModel.relativeDualizingComplex`). It is
`Stacks.Duality.structureSheafIsoExactSupportPullbackFst` carried across the model comparison. -/
def diagonalExactSupportRelativeDualizingComplexIso :
    (Scheme.Hom.DiagonalOpen.ofIsSeparated f).diagonalExactSupport
        (StandardModel.relativeDualizingComplex f).obj ≅
      Scheme.structureSingle X :=
  (Scheme.Modules.derivedModelEquiv X).fullyFaithfulFunctor.preimageIso
    (diagonalExactSupportModelIso f (StandardModel.relativeDualizingComplex f).obj ≪≫
      (LocallySmall.derivedSheafHomExactSupport (pullback.diagonal f)).mapIso
        ((derivedPullback (pullback.fst f f)).mapIso
          ((ObjectProperty.ι _).mapIso (StandardModel.relativeDualizingComplexModelIso f))) ≪≫
      (structureSheafIsoExactSupportPullbackFst f).symm ≪≫
      ((StacksDraft.DerivedModel.modelSingleFunctorIso (HasDerivedCategory.standard X.Modules)
        (Scheme.Modules.hasDerivedCategory X) 0).app (SheafOfModules.unit X.ringCatSheaf)).symm)

/-- **The map `ξ : Δ_*𝒪_X ⟶ L pr₁^*ω_{X/S}^•` of [Stacks, Tag 0E2Z]**, on `W = X ×_S X`: the
adjoint, under `Δ_* ⊣ R ℰom(𝒪_X, -)` ([Stacks, Tag 0A76]), of the isomorphism
`𝒪_X ≅ R ℰom(𝒪_X, L pr₁^*ω_{X/S}^•)` of [Stacks, Tag 0E2Q]
(`Stacks.Duality.diagonalExactSupportRelativeDualizingComplexIso`). -/
def relativeDualizingComplexDiagonalMap :
    (Scheme.Hom.DiagonalOpen.ofIsSeparated f).diagonalObject ⟶
      (Scheme.Hom.DiagonalOpen.ofIsSeparated f).derivedPullbackProj
        (StandardModel.relativeDualizingComplex f).obj :=
  (Scheme.Hom.DiagonalOpen.ofIsSeparated f).diagonalGenerator _
    (diagonalExactSupportRelativeDualizingComplexIso f)

end Standard

end Stacks.Duality

end
