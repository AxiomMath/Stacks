module

public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceGlobalHom
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceProperIso
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardPseudoCoherent

/-!
# Duality for the relative cup product into the relative dualizing complex

Let `Y` be a quasi-compact quasi-separated scheme and `f : X ⟶ Y` a proper, flat morphism of
finite presentation. Let `a` be the right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`
([Stacks, Tag 0A9E]), `ω^•_{X/Y} = a(𝒪_Y)` the relative dualizing complex and
`Tr_{f, 𝒪_Y} : Rf_*ω^•_{X/Y} ⟶ 𝒪_Y` the trace, the counit of `Rf_* ⊣ a` at `𝒪_Y`
([Stacks, Tag 0B6S]). Let `K, M ∈ D_QCoh(𝒪_X)` with `M` pseudo-coherent, and let
`K ⊗^L_{𝒪_X} M ⟶ ω^•_{X/Y}` be a map corresponding to an isomorphism
`K ⟶ R𝓗om_{𝒪_X}(M, ω^•_{X/Y})` under [Stacks, Tag 08DI]. Then the relative cup product of
[Stacks, Tag 0B68] followed by the trace,

`Rf_*K ⊗^L_{𝒪_Y} Rf_*M ⟶ Rf_*(K ⊗^L_{𝒪_X} M) ⟶ Rf_*ω^•_{X/Y} ⟶ 𝒪_Y`,

determines an isomorphism `Rf_*K ⟶ R𝓗om_{𝒪_Y}(Rf_*M, 𝒪_Y)` ([Stacks, Tag 0G81]).

The proof is the source's. The map determined by the composite is `Rf_*` of the given
isomorphism `K ⟶ R𝓗om_{𝒪_X}(M, ω^•_{X/Y})` followed by the canonical map

`Rf_*R𝓗om_{𝒪_X}(M, a(𝒪_Y)) ⟶ R𝓗om_{𝒪_Y}(Rf_*M, 𝒪_Y)`

of [Stacks, Tag 0B6H] — this is the commutativity of the diagram of [Stacks, Tag 0G7A], which for
`Stacks.Duality.derivedSheafHomPushforward` is its defining property
`Stacks.Duality.derivedSheafHomPushforward_homEquiv`, together with the naturality of the relative
cup product and of the tensor–internal-Hom bijection. The canonical map is an isomorphism by
[Stacks, Tag 0A9Q] and clause (2) of [Stacks, Tag 0GEV]: `𝒪_Y` is bounded below, so is `a(𝒪_Y)`
by [Stacks, Tag 0A9I], and `M` and `Rf_*M` are pseudo-coherent, the latter by
[Stacks, Tag 0CSD].

## Main results

* `Stacks.Duality.homEquiv_symm_relativeCupProduct_comp_counit` — for any morphism of schemes
  and any right adjoint `a` of `Rf_*`, the map `Rf_*K ⟶ R𝓗om_{𝒪_Y}(Rf_*M, N)` determined by
  the relative cup product, `Rf_*` of `φ : K ⊗^L M ⟶ a(N)` and the counit at `N` is `Rf_*` of
  the transpose of `φ` followed by the map of [Stacks, Tag 0B6H].
* `Stacks.Duality.isIso_homEquiv_symm_relativeCupProduct_comp_trace` — **[Stacks, Tag 0G81]**.

## Implementation notes

Standard model: uses `Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct` and
`Stacks.Duality.sheafyTrace`, which exist only there, in every statement, generic lemmas included.

*The model.* Everything is stated at the standard model of the derived categories,
`CategoryTheory.HasDerivedCategory.standard`, which is the model at which the map of
[Stacks, Tag 0B6H] (`Stacks.Duality.sheafyTrace`), the relative cup product of
[Stacks, Tag 0B68] and the inputs [Stacks, Tags 0A9Q, 0A9I, 0CSD] are proved in this
development. The relative dualizing complex and its trace are
`Stacks.Duality.relativeDualizingComplex` and `Stacks.Duality.relativeDualizingComplexTrace`
at the twisted inverse image `Stacks.Duality.twistedInverseImage` of [Stacks, Tag 0A9E] at that
model and at `ω_Y = 𝒪_Y`, the structure sheaf in degree zero
(`Stacks.Duality.derivedStructureSheafInDegree Y 0`): by definition `a(𝒪_Y)` and the counit of
`Rf_* ⊣ a` at `𝒪_Y`, which is what [Stacks, Tag 0B6S] names `ω^•_{X/Y}` and `Tr_{f, 𝒪_Y}`.

*The bijection of Tag 08DI.* The relative cup product lands in
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`, so the bijection used on both `X`
and `Y` is the tensor–internal-Hom adjunction of [Stacks, Tag 08J8] at that tensor product,
`Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.derivedTensorHomAdjunction`: the
bijection `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` of [Stacks, Tag 08DI] read across
the comparison of the two derived tensor products. This is also the bijection out of which the
map of [Stacks, Tag 0B6H] is built.

*Generality.* The object `K` is not required to have quasi-coherent cohomology: the argument does
not use it (and it follows from the hypothesis, `R𝓗om_{𝒪_X}(M, ω^•_{X/Y})` being in
`D_QCoh(𝒪_X)`).

## References

* [Stacks Project, Tag 0G81](https://stacks.math.columbia.edu/tag/0G81)
* [Stacks Project, Tag 0B6S](https://stacks.math.columbia.edu/tag/0B6S)
* [Stacks Project, Tag 0B6H](https://stacks.math.columbia.edu/tag/0B6H)
* [Stacks Project, Tag 0A9Q](https://stacks.math.columbia.edu/tag/0A9Q)
* [Stacks Project, Tag 0GEV](https://stacks.math.columbia.edu/tag/0GEV)
* [Stacks Project, Tag 0CSD](https://stacks.math.columbia.edu/tag/0CSD)
* [Stacks Project, Tag 0G7A](https://stacks.math.columbia.edu/tag/0G7A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  Opposite TopologicalSpace
open Stacks.Cohomology.DerivedRelativeCupProduct
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi
open Stacks.DerivedTensor.RingedSite

namespace Stacks.Duality

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

section General

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (DX : TensorHomAdjunction
    (derivedTensorProductFunctor (Stacks.SheafOfModules.ringedSite X.sheaf).O)
    (RingedSite.derivedSheafHomBifunctor (Stacks.SheafOfModules.ringedSite X.sheaf)))
  (DY : TensorHomAdjunction
    (derivedTensorProductFunctor (Stacks.SheafOfModules.ringedSite Y.sheaf).O)
    (RingedSite.derivedSheafHomBifunctor (Stacks.SheafOfModules.ringedSite Y.sheaf)))
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
  (adj : quasiCoherentDerivedPushforward f hpush ⊣ a)

/-- **The relative cup product into `a(N)` determines `Rf_*` of the transpose followed by the map
of [Stacks, Tag 0B6H].** Let `f : X ⟶ Y` be a morphism of schemes, `a` a right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, `K ∈ D(𝒪_X)`, `M ∈ D_QCoh(𝒪_X)`, `N ∈ D_QCoh(𝒪_Y)` and
`φ : K ⊗^L_{𝒪_X} M ⟶ a(N)`. The map `Rf_*K ⟶ R𝓗om_{𝒪_Y}(Rf_*M, N)` corresponding under the
tensor–internal-Hom bijection to

`Rf_*K ⊗^L_{𝒪_Y} Rf_*M ⟶ Rf_*(K ⊗^L_{𝒪_X} M) ⟶ Rf_*a(N) ⟶ N`

(relative cup product, `Rf_*φ`, counit) is `Rf_*` of the transpose `K ⟶ R𝓗om_{𝒪_X}(M, a(N))`
of `φ` followed by the map `Rf_*R𝓗om_{𝒪_X}(M, a(N)) ⟶ R𝓗om_{𝒪_Y}(Rf_*M, N)` of
[Stacks, Tag 0B6H]. This is the commutativity of the diagram of [Stacks, Tag 0G7A] as the
source uses it in [Stacks, Tag 0G81]. -/
theorem homEquiv_symm_relativeCupProduct_comp_counit (K : DerivedCategory X.Modules)
    (M : quasiCoherentDerivedCategory X) (N : quasiCoherentDerivedCategory Y)
    (φ : ((derivedTensorProductFunctor X.sheaf).obj K).obj M.obj ⟶ (a.obj N).obj) :
    (DY.homEquiv ((derivedPushforward f).obj K) ((derivedPushforward f).obj M.obj) N.obj).symm
        (relativeCupProduct f.toLRSHom.toShHom K M.obj ≫ (derivedPushforward f).map φ ≫
          (ι _).map (adj.counit.app N)) =
      (derivedPushforward f).map ((DX.homEquiv _ _ _).symm φ) ≫
        sheafyTrace f DX DY hpush adj M N := by
  have hφ : ((derivedTensorProductFunctor X.sheaf).map ((DX.homEquiv _ _ _).symm φ)).app M.obj ≫
      DX.evaluation M.obj (a.obj N).obj = φ :=
    (DX.homEquiv_naturality_source ((DX.homEquiv _ _ _).symm φ) (𝟙 _)).symm.trans
      ((congrArg (DX.homEquiv _ _ _) (Category.comp_id _)).trans
        ((DX.homEquiv _ _ _).apply_symm_apply φ))
  refine (Equiv.symm_apply_eq _).2 ?_
  refine Eq.trans ?_ (DY.homEquiv_naturality_source _ _).symm
  refine Eq.trans ?_ (congrArg (_ ≫ ·) ((DY.homEquiv_naturality_target
    (derivedSheafHomPushforward f DX DY M.obj (a.obj N).obj) ((ι _).map (adj.counit.app N))).trans
      (congrArg (· ≫ _) (derivedSheafHomPushforward_homEquiv f DX DY M.obj (a.obj N).obj)))).symm
  refine Eq.trans ?_ (whisker_eq _ (Category.assoc _ _ _)).symm
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (eq_whisker (relativeCupProduct_natural_left f.toLRSHom.toShHom
    ((DX.homEquiv _ _ _).symm φ) M.obj) _).symm
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine whisker_eq _ ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine eq_whisker ?_ _
  exact (congrArg (derivedPushforward f).map hφ).symm.trans (Functor.map_comp _ _ _)

/-- **The relative cup product into the relative dualizing complex.** The special case of
`Stacks.Duality.homEquiv_symm_relativeCupProduct_comp_counit` at the twisted inverse image
`a = f^×` of [Stacks, Tag 0A9E] and `ω_X^• = a(ω_Y^•)`: for `φ : K ⊗^L_{𝒪_X} M ⟶ ω_X^•` the map
`Rf_*K ⟶ R𝓗om_{𝒪_Y}(Rf_*M, ω_Y^•)` corresponding to the relative cup product followed by
`Rf_*φ` and the trace `Rf_*ω_X^• ⟶ ω_Y^•` is `Rf_*` of the transpose of `φ` followed by the map
of [Stacks, Tag 0B6H]. -/
theorem homEquiv_symm_relativeCupProduct_comp_relativeDualizingComplexTrace
    [(quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint] (K : DerivedCategory X.Modules)
    (M : quasiCoherentDerivedCategory X) (ωY : quasiCoherentDerivedCategory Y)
    (φ : ((derivedTensorProductFunctor X.sheaf).obj K).obj M.obj ⟶
      (relativeDualizingComplex f hpush ωY).obj) :
    (DY.homEquiv ((derivedPushforward f).obj K) ((derivedPushforward f).obj M.obj) ωY.obj).symm
        (relativeCupProduct f.toLRSHom.toShHom K M.obj ≫ (derivedPushforward f).map φ ≫
          (ι _).map (relativeDualizingComplexTrace f hpush ωY)) =
      (derivedPushforward f).map
          ((DX.homEquiv K M.obj (relativeDualizingComplex f hpush ωY).obj).symm φ) ≫
        sheafyTrace f DX DY hpush (twistedInverseImageAdjunction f hpush) M ωY :=
  homEquiv_symm_relativeCupProduct_comp_counit f DX DY hpush (twistedInverseImageAdjunction f hpush)
    K M ωY φ

end General

section ProperFlat

attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
  [IsProper f] [Flat f] [LocallyOfFinitePresentation f]

/-- **Stacks Project, Tag 0G81.** Let `Y` be a quasi-compact quasi-separated scheme and
`f : X ⟶ Y` a proper, flat morphism of finite presentation; let `a` be the right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of [Stacks, Tag 0A9E], `ω^•_{X/Y} = a(𝒪_Y)` the relative
dualizing complex and `Tr_{f, 𝒪_Y} : Rf_*ω^•_{X/Y} ⟶ 𝒪_Y` the trace of [Stacks, Tag 0B6S]. Let
`K ∈ D(𝒪_X)` and `M ∈ D_QCoh(𝒪_X)` with `M` pseudo-coherent, and let
`φ : K ⊗^L_{𝒪_X} M ⟶ ω^•_{X/Y}` be a map whose transpose `K ⟶ R𝓗om_{𝒪_X}(M, ω^•_{X/Y})` under
the tensor–internal-Hom bijection of [Stacks, Tag 08DI] is an isomorphism. Then the map
`Rf_*K ⟶ R𝓗om_{𝒪_Y}(Rf_*M, 𝒪_Y)` corresponding under that bijection on `Y` to

`Rf_*K ⊗^L_{𝒪_Y} Rf_*M ⟶ Rf_*(K ⊗^L_{𝒪_X} M) ⟶ Rf_*ω^•_{X/Y} ⟶ 𝒪_Y`

(the relative cup product of [Stacks, Tag 0B68], `Rf_*φ` and `Tr_{f, 𝒪_Y}`) is an isomorphism.

The source asks `K` to lie in `D_QCoh(𝒪_X)`; that is not used. The instance arguments
`CompactSpace X` and `QuasiSeparatedSpace X` restrict nothing: they hold for every proper `f` over
a quasi-compact quasi-separated `Y` (`AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace`
and `AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated`), and are arguments only because
the right adjoint `a` of [Stacks, Tag 0A9E] at this model is found by instance search from them. -/
@[stacks 0G81]
theorem isIso_homEquiv_symm_relativeCupProduct_comp_trace (K : DerivedCategory X.Modules)
    (M : quasiCoherentDerivedCategory X)
    (hM : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) M.obj)
    (φ : ((derivedTensorProductFunctor X.sheaf).obj K).obj M.obj ⟶
      (relativeDualizingComplex f (StandardModel.isQuasicoherent_homology_derivedPushforward f)
        (derivedStructureSheafInDegree Y 0)).obj)
    (hφ : IsIso (((derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite X.sheaf)).homEquiv
      K M.obj (relativeDualizingComplex f
        (StandardModel.isQuasicoherent_homology_derivedPushforward f)
        (derivedStructureSheafInDegree Y 0)).obj).symm φ)) :
    IsIso (((derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite Y.sheaf)).homEquiv
      ((derivedPushforward f).obj K) ((derivedPushforward f).obj M.obj)
      (derivedStructureSheafInDegree Y 0).obj).symm
        (relativeCupProduct f.toLRSHom.toShHom K M.obj ≫ (derivedPushforward f).map φ ≫
          (ι _).map (relativeDualizingComplexTrace f
            (StandardModel.isQuasicoherent_homology_derivedPushforward f)
            (derivedStructureSheafInDegree Y 0)))) := by
  have hRM := isPseudoCoherent_derivedPushforward_of_flat_of_isProper f M.obj hM
  have hO : DerivedCategoryB.IsBoundedBelow (derivedStructureSheafInDegree Y 0).obj :=
    ⟨0, fun n hn => DerivedCategory.isZero_of_isGE (C := Y.Modules)
      ((DerivedCategory.singleFunctor Y.Modules 0).obj (SheafOfModules.unit Y.ringCatSheaf)) 0 n hn
      (hX := DerivedCategory.instIsGEObjSingleFunctor _ _)⟩
  have hST := isIso_sheafyTrace_of_isPseudoCoherent f
    (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite X.sheaf))
    (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite Y.sheaf))
    (StandardModel.isQuasicoherent_homology_derivedPushforward f)
    (twistedInverseImageAdjunction f
      (StandardModel.isQuasicoherent_homology_derivedPushforward f))
    (Adjunction.ofIsLeftAdjoint _) M (derivedStructureSheafInDegree Y 0)
    (isBoundedBelow_rightAdjoint_obj_of_adjunction f
      (twistedInverseImageAdjunction f
        (StandardModel.isQuasicoherent_homology_derivedPushforward f)) _)
    (isIso_coherator_map_sheafyTrace_of_adjunction f
      (twistedInverseImageAdjunction f
        (StandardModel.isQuasicoherent_homology_derivedPushforward f)) M _) hO hM hRM
  have key := homEquiv_symm_relativeCupProduct_comp_relativeDualizingComplexTrace f
    (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite X.sheaf))
    (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite Y.sheaf))
    (StandardModel.isQuasicoherent_homology_derivedPushforward f)
    K M (derivedStructureSheafInDegree Y 0) φ
  exact (congrArg IsIso key).mpr (IsIso.comp_isIso'
    ((derivedPushforward f).mapIso (@asIso _ _ _ _ _ hφ)).isIso_hom hST)

end ProperFlat

end Stacks.Duality

end
