module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierNormalTensorIso
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointSheafHomLocallySmall
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierAdjunctionModule
public import StacksFrontier.AlgebraicGeometry.Duality.ExceptionalDualizingSheafIdentification
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistFlatness
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorInvertibleSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveHomologySplitting

/-!
# The twisted inverse image of an invertible module along an effective Cartier divisor

Let `W` be a locally Noetherian, quasi-compact and quasi-separated scheme, `i : D ⟶ W` the closed
immersion of an effective Cartier divisor with normal sheaf `𝒩 = i^*𝒪_W(D)`, and `G` an invertible
`𝒪_W`-module. The right adjoint `i^×` of `Ri_* : D_QCoh(𝒪_D) ⥤ D_QCoh(𝒪_W)` satisfies

`i^×(G[1]) ≅ R𝓗om(𝒪_D, G[1]) ≅ Li^*(G[1]) ⊗^L 𝒩[-1] ≅ (𝒩 ⊗ i^*G)[0]`,

an invertible `𝒪_D`-module placed in degree zero. This is the computation used in
[Stacks, Example 0AAC], from [Stacks, Tag 0A9X] and [Stacks, Tag 0AA4].

## Main results

* `Stacks.Duality.isInvertibleModule_normalTensorPullback`: `𝒩 ⊗ i^*G` is invertible.
* `Stacks.Duality.nonempty_derivedSheafHomExactSupport_single_iso_standard`:
  `R𝓗om(𝒪_D, G[0]) ≅ (𝒩 ⊗ i^*G)[-1]` at the standard model of the derived categories.
* `Stacks.Duality.nonempty_derivedSheafHomExactSupport_single_iso`: the same at the locally
  small model.
* `Stacks.Duality.exists_isInvertibleModule_twistedInverseImage_subschemeι_iso_single`:
  `i^×(G[1])` is an invertible module in degree zero.

## The proof

By [Stacks, Tag 0AA4], `Ri_* R𝓗om(𝒪_D, G[0]) ≅ G[0] ⊗^L (i_*𝒩)[-1]`, and since `G[0]` is K-flat
the right-hand side is `(G ⊗ i_*𝒩)[-1]`. As `i_*` is exact and faithful, `R𝓗om(𝒪_D, G[0])` has
cohomology only in degree `1`, where it is `𝒩 ⊗ i^*G` by the adjunction formula for modules. This
is carried from the standard model to the locally small one by the comparison equivalence, and
[Stacks, Tag 0A9X] identifies `i^×` with `R𝓗om(𝒪_D, -)` on the bounded below object `G[1]`; the
shift by one is moved through `R𝓗om(𝒪_D, -)`, a right adjoint of a functor commuting with shifts.

## References

* [Stacks Project, Example 0AAC](https://stacks.math.columbia.edu/tag/0AAC)
* [Stacks Project, Tag 0A9X](https://stacks.math.columbia.edu/tag/0A9X)
* [Stacks Project, Tag 0AA4](https://stacks.math.columbia.edu/tag/0AA4)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.Duality

variable {W : Scheme.{u}} (D : W.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]

/-- **`𝒩 ⊗ i^*G` is invertible.** For an effective Cartier divisor `i : D ⟶ W` and an invertible
`𝒪_W`-module `G`, the tensor product of the normal sheaf `𝒩 = i^*𝒪_W(D)` with `i^*G` is an
invertible `𝒪_D`-module: pullbacks and tensor products of invertible modules are invertible. -/
theorem isInvertibleModule_normalTensorPullback (G : W.Modules)
    [Stacks.Ample.IsInvertibleModule W G] :
    Stacks.Ample.IsInvertibleModule D.subscheme
      (((Stacks.SheafOfModules.Tensor.sheafTensor
            (Stacks.SheafOfModules.ringedSite D.subscheme.sheaf).O).obj
          ((Scheme.Modules.pullback D.subschemeι).obj (Stacks.Divisors.divisorSheaf D))).obj
        ((Scheme.Modules.pullback D.subschemeι).obj G)) := by
  have : Stacks.SheafOfModules.IsInvertible W.presheaf
      (structureSheafRing W.toRingedSpace).property (Stacks.Divisors.divisorSheaf D) :=
    Stacks.Divisors.isTensorInvertible_invertibleSheaf D
  have : Stacks.SheafOfModules.IsInvertible W.presheaf
      (structureSheafRing W.toRingedSpace).property G := ‹Stacks.Ample.IsInvertibleModule W G›
  have : Stacks.SheafOfModules.IsInvertible D.subscheme.presheaf
      (structureSheafRing D.subscheme.toRingedSpace).property
      ((Scheme.Modules.pullback D.subschemeι).obj (Stacks.Divisors.divisorSheaf D)) :=
    Stacks.Modules.isInvertible_pullback _ _
  have : Stacks.SheafOfModules.IsInvertible D.subscheme.presheaf
      (structureSheafRing D.subscheme.toRingedSpace).property
      ((Scheme.Modules.pullback D.subschemeι).obj G) :=
    Stacks.Modules.isInvertible_pullback _ _
  exact Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ _

/-- **`R𝓗om(𝒪_D, G[0]) ≅ (𝒩 ⊗ i^*G)[-1]` at the standard model**, for an invertible `G`. After
`Ri_*` the left-hand side is `G[0] ⊗^L (i_*𝒩)[-1]` by [Stacks, Tag 0AA4], which is concentrated in
degree `1` because `G[0]` is K-flat; `i_*` is exact and faithful, so `R𝓗om(𝒪_D, G[0])` has
cohomology in degree `1` only, where it is `𝒩 ⊗ i^*G` by the module-level adjunction formula. -/
theorem nonempty_derivedSheafHomExactSupport_single_iso_standard (G : W.Modules)
    [Stacks.Ample.IsInvertibleModule W G] :
    Nonempty ((Stacks.Divisors.closedQuotient D).derivedSheafHomExactSupport.obj
        ((@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard W.Modules) 0).obj G) ≅
      (@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard D.subscheme.Modules) 1).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor
            (Stacks.SheafOfModules.ringedSite D.subscheme.sheaf).O).obj
          ((Scheme.Modules.pullback D.subschemeι).obj (Stacks.Divisors.divisorSheaf D))).obj
        ((Scheme.Modules.pullback D.subschemeι).obj G))) := by
  let Q := Stacks.Divisors.closedQuotient D
  let : HasDerivedCategory W.Modules := HasDerivedCategory.standard W.Modules
  let : HasDerivedCategory D.subscheme.Modules := HasDerivedCategory.standard D.subscheme.Modules
  let : HasDerivedCategory (SheafOfModules.{u} (structureSheafRing Q.X)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory (SheafOfModules.{u} (structureSheafRing Q.Z)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory
      (RingedSite.Modules.{u, u, u} (Stacks.SheafOfModules.ringedSite W.sheaf)) :=
    HasDerivedCategory.standard _
  let A := Q.derivedSheafHomExactSupport.obj ((DerivedCategory.singleFunctor W.Modules 0).obj G)
  let T := Stacks.SheafOfModules.canonicalDerivedTensorProduct
    (Stacks.SheafOfModules.ringedSite W.sheaf)
  let N' := (Stacks.Divisors.normalShortComplex D).X₃
  have hflat := Stacks.SheafOfModules.isFlat_of_isInvertible (X := W.toRingedSpace) G
    ‹Stacks.Ample.IsInvertibleModule W G›
  have hG : Stacks.SheafOfModules.IsKFlat (Stacks.SheafOfModules.ringedSite W.sheaf).O
      ((CochainComplex.singleFunctor _ 0).obj G) :=
    Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat _ G hflat 0
  let := T.commShift_right ((DerivedCategory.singleFunctor _ 0).obj G)
  let e₁ : (modulePushforward Q.i).mapDerivedCategory.obj A ≅
      (DerivedCategory.singleFunctor _ 1).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          (Stacks.SheafOfModules.ringedSite W.sheaf).O).obj G).obj N') :=
    Stacks.Divisors.pushforwardDerivedSheafHomExactSupportTensorIso D _ ≪≫
      (T.tensor.obj ((DerivedCategory.singleFunctor _ 0).obj G)).mapIso
        (((DerivedCategory.singleFunctors _).shiftIso (-1) 1 0 (by ring)).app N').symm ≪≫
      ((T.tensor.obj ((DerivedCategory.singleFunctor _ 0).obj G)).commShiftIso (-1 : ℤ)).app _ ≪≫
      (shiftFunctor _ (-1 : ℤ)).mapIso (T.tensorSingleIso G N' hG) ≪≫
      ((DerivedCategory.singleFunctors _).shiftIso (-1) 1 0 (by ring)).app _
  have hA : ∀ j : ℤ, j ≠ 1 →
      IsZero ((DerivedCategory.homologyFunctor D.subscheme.Modules j).obj A) := by
    intro j hj
    have h1 : IsZero ((DerivedCategory.homologyFunctor _ j).obj
        ((modulePushforward Q.i).mapDerivedCategory.obj A)) :=
      (DerivedCategory.Plus.isZero_homologyFunctor_singleFunctor_obj _ hj).of_iso
        ((DerivedCategory.homologyFunctor _ j).mapIso e₁)
    have h2 : IsZero ((modulePushforward Q.i).obj
        ((DerivedCategory.homologyFunctor D.subscheme.Modules j).obj A)) :=
      h1.of_iso (((modulePushforward Q.i).mapDerivedCategoryHomologyFunctorIso j).app A).symm
    exact (IsZero.iff_id_eq_zero _).2 ((modulePushforward Q.i).map_injective (h2.eq_of_src _ _))
  obtain ⟨e₂⟩ := DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero A 1 hA
  obtain ⟨e₃⟩ := Stacks.Divisors.nonempty_homologyOne_derivedSheafHomExactSupport_iso D G
  exact ⟨e₂ ≪≫ (DerivedCategory.singleFunctor _ 1).mapIso e₃⟩

/-- **`R𝓗om(𝒪_D, G[0]) ≅ (𝒩 ⊗ i^*G)[-1]` at the locally small model**, for an invertible `G`:
`Stacks.Duality.nonempty_derivedSheafHomExactSupport_single_iso_standard` carried across the
comparison equivalence of the two models, which matches the two right derived functors of sheaf
Hom with exact support and the two placements of a module in a single degree. -/
theorem nonempty_derivedSheafHomExactSupport_single_iso (G : W.Modules)
    [Stacks.Ample.IsInvertibleModule W G] :
    Nonempty ((LocallySmall.derivedSheafHomExactSupport D.subschemeι).obj
        ((DerivedCategory.singleFunctor W.Modules 0).obj G) ≅
      (DerivedCategory.singleFunctor D.subscheme.Modules 1).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor
            (Stacks.SheafOfModules.ringedSite D.subscheme.sheaf).O).obj
          ((Scheme.Modules.pullback D.subschemeι).obj (Stacks.Divisors.divisorSheaf D))).obj
        ((Scheme.Modules.pullback D.subschemeι).obj G))) := by
  let Q := Stacks.Duality.closedQuotient D.subschemeι
  let hLSX : HasDerivedCategory.{u} (SheafOfModules.{u} (structureSheafRing Q.X)) :=
    inferInstance
  let hLSE : HasDerivedCategory.{u} (SheafOfModules.{u} (structureSheafRing Q.Z)) :=
    inferInstance
  let hstdX := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing Q.X))
  let hstdE := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing Q.Z))
  obtain ⟨estd⟩ := nonempty_derivedSheafHomExactSupport_single_iso_standard D G
  refine ⟨(StacksDraft.DerivedModel.modelEquiv hLSE hstdE).fullyFaithfulFunctor.preimageIso ?_⟩
  exact (Stacks.Duality.AnyModel.derivedSheafHomExactSupportModelIso Q hLSX hLSE hstdX hstdE).app
      _ ≪≫
    (@Stacks.Duality.AnyModel.derivedSheafHomExactSupport Q hstdX hstdE).mapIso
      ((StacksDraft.DerivedModel.modelSingleFunctorIso hLSX hstdX 0).app G) ≪≫ estd ≪≫
    ((StacksDraft.DerivedModel.modelSingleFunctorIso hLSE hstdE 1).app _).symm

/-- For an effective Cartier divisor `D ⊆ W` and an invertible `G`, the twisted inverse image
along the closed immersion of `D` carries `G[1]` to an invertible module in degree zero. -/
theorem exists_isInvertibleModule_twistedInverseImage_subschemeι_iso_single
    {W : Scheme.{u}} [IsLocallyNoetherian W] [CompactSpace W] [QuasiSeparatedSpace W]
    (D : W.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D] (G : W.Modules)
    [Stacks.Ample.IsInvertibleModule W G] (K : quasiCoherentDerivedCategory W)
    (eK : K.obj ≅ ((DerivedCategory.singleFunctor W.Modules 0).obj G)⟦(1 : ℤ)⟧)
    [CompactSpace D.subscheme] [QuasiSeparatedSpace D.subscheme] :
    ∃ L : D.subscheme.Modules, Stacks.Ample.IsInvertibleModule D.subscheme L ∧
      Nonempty (((twistedInverseImage D.subschemeι
        (isQuasicoherent_homology_derivedPushforward_of_qcqs D.subschemeι)).obj K).obj ≅
          (DerivedCategory.singleFunctor D.subscheme.Modules 0).obj L) := by
  have hpc : PseudoCoherent D.subschemeι :=
    (pseudoCoherent_iff_locallyOfFiniteType _).2 inferInstance
  obtain ⟨e0A9X⟩ := LocallySmall.isDerivedSheafHomRightAdjoint_of_pseudoCoherent
    D.subschemeι hpc (isQuasicoherent_homology_derivedPushforward_of_qcqs D.subschemeι) _
    (twistedInverseImageAdjunction D.subschemeι
      (isQuasicoherent_homology_derivedPushforward_of_qcqs D.subschemeι))
  obtain ⟨e⟩ := nonempty_derivedSheafHomExactSupport_single_iso D G
  refine ⟨_, isInvertibleModule_normalTensorPullback D G, ⟨?_⟩⟩
  have hK : DerivedCategoryB.IsBoundedBelow K.obj :=
    ⟨-1, fun m hm => (DerivedCategory.isZero_of_isGE _ (-1) m hm).of_iso
      ((DerivedCategory.homologyFunctor _ m).mapIso
        (eK ≪≫ ((DerivedCategory.singleFunctors W.Modules).shiftIso 1 (-1) 0 (by ring)).app G))⟩
  let := (LocallySmall.derivedModulePushforwardSheafHomExactSupportAdjunction
    D.subschemeι).rightAdjointCommShift ℤ
  exact e0A9X.app ⟨K, hK⟩ ≪≫ (LocallySmall.derivedSheafHomExactSupport D.subschemeι).mapIso eK ≪≫
    ((LocallySmall.derivedSheafHomExactSupport D.subschemeι).commShiftIso (1 : ℤ)).app _ ≪≫
    (shiftFunctor _ (1 : ℤ)).mapIso e ≪≫
    ((DerivedCategory.singleFunctors _).shiftIso 1 0 1 (by ring)).app _

end Stacks.Duality
