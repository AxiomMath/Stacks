module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperModuleSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ModuleSupportProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupportTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupportFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# Proper support descends along an fppf covering of the base

Let

```
X' ⟶ X
↓     ↓ f
Y' ⟶ Y
    g
```

be a cartesian square of algebraic spaces over a scheme `S` whose right vertical morphism `f` is
locally of finite type, and whose bottom morphism `g` is flat and forms a one-member fppf covering
of `Y` (for instance a surjective étale scheme atlas of `Y`). For a quasi-coherent `𝒪_X`-module `F`
of finite type, if the support of the pullback of `F` to `X'` is proper over `Y'`, then the support
of `F` is proper over `Y`. Together with Stacks 0CZJ, which is the converse, this says that
properness of the support of a finite type quasi-coherent module is local on the base for such
coverings.

## Main results

* `AlgebraicGeometry.Space.hasProperSupport_of_isPullback_of_mem_fppf`: proper support descends
  along a flat one-member fppf covering of the base.

## References

* [Stacks Project, Tag 0D3V](https://stacks.math.columbia.edu/tag/0D3V)
* [Stacks Project, Tag 0422](https://stacks.math.columbia.edu/tag/0422)
* [Stacks Project, Tag 089C](https://stacks.math.columbia.edu/tag/089C)
* [Stacks Project, Tag 07U0](https://stacks.math.columbia.edu/tag/07U0)
* [Stacks Project, Tag 0CZC](https://stacks.math.columbia.edu/tag/0CZC)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 0CZJ](https://stacks.math.columbia.edu/tag/0CZJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Proper support descends along a flat one-member fppf covering of the base.** In a cartesian
square of algebraic spaces over `S` whose right vertical morphism `f : X ⟶ Y` is locally of finite
type and whose bottom morphism `g : Y' ⟶ Y` is flat and alone covers `Y` in the fppf precoverage, a
quasi-coherent `𝒪_X`-module `F` of finite type has support proper over `Y` as soon as its pullback
to `X'` has support proper over `Y'`. -/
theorem hasProperSupport_of_isPullback_of_mem_fppf {X' X Y' Y : AlgebraicSpaces B S hS}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hcov : Presieve.singleton g ∈ (Topology.fppf.precoverage.{u, v} B S hS).coverings Y)
    (hg : IsFlat B S hS g.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hqc : F.IsQuasicoherentOnSite)
    (hft : SheafOfModules.IsFiniteTypeOnSite F)
    (hF' : HasProperSupport B S hS X'.2 Y'.2 f'.hom
      ((isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback sq hf)
      ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS g').obj F))) :
    HasProperSupport B S hS X.2 Y.2 f.hom hf ((SheafOfModules.toSheaf _).obj F) := by
  have hg' : IsFlat B S hS g'.hom :=
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback sq.flip hg
  have hftp := Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite F hft
  obtain ⟨hZ, -⟩ := exists_isClosedSubspace_schemeTheoreticSupport B S hS X F hqc hftp
  set Z := schemeTheoreticSupport B S hS X F
  have hsupp := supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport B S hS X F hqc hft
  have hcl : IsClosed (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F)) :=
    have := hft
    isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.2 F
  refine ⟨hcl, (isProper_reducedClosedSubspace_iff_exists B S hS X.2 Y.2 f.hom hf _ hcl).2
    ⟨Z, hZ, hsupp.symm, ?_⟩⟩
  set Z' := Z.preimage g'.hom
  have hZ' : IsClosedSubspace B S hS Z' := isClosedSubspace_preimage B S hS g'.hom Z X.2 X'.2 hZ
  have hqc' := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g' F hqc
  have hft' := isFiniteTypeOnSite_modulePullback B S hS g' F hft
  have h089C : schemeTheoreticSupport B S hS X' ((modulePullback B S hS g').obj F) = Z' :=
    schemeTheoreticSupport_modulePullback B S hS hg' F hqc hftp
  have hsupp' := supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport B S hS X'
    ((modulePullback B S hS g').obj F) hqc' hft'
  rw [h089C] at hsupp'
  have hZ'proper : IsProper B S hS (Z'.ι ≫ f'.hom) :=
    isProper_comp_of_hasProperSupport_of_range_subset B S hS X'.2 Y'.2 f'.hom _ hF' hZ'.1 Z'.ι
      hZ'.2 hsupp'.symm.subset
  let ZA : AlgebraicSpaces B S hS := ⟨Z.toFunctor, hZ.1⟩
  let ZA' : AlgebraicSpaces B S hS := ⟨Z'.toFunctor, hZ'.1⟩
  have psq : IsPullback (ObjectProperty.homMk (Z.fromPreimage g'.hom) : ZA' ⟶ ZA)
      (ObjectProperty.homMk (Z'.ι ≫ f'.hom) : ZA' ⟶ Y')
      (ObjectProperty.homMk (Z.ι ≫ f.hom) : ZA ⟶ Y) g :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _)
      ((Subfunctor.isPullback_preimage g'.hom Z).paste_vert
        (AlgebraicSpaces.isPullback_hom B S hS sq))
  change properProperty B S hS (ObjectProperty.homMk (Z.ι ≫ f.hom) : ZA ⟶ Y)
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (P := properProperty B S hS) (K := Topology.fppf.precoverage.{u, v} B S hS) hcov ?_
  rintro U _ _ ⟨⟩
  have : (properProperty B S hS).RespectsIso :=
    (proper_isLocalAtTarget_fppf.{u, v} B S hS).toRespects
  refine ((properProperty B S hS).cancel_left_of_respectsIso psq.isoPullback.hom
    (pullback.snd _ _)).1 ?_
  rwa [psq.isoPullback_hom_snd]

end AlgebraicGeometry.Space

end
