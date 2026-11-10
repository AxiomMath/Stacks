module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSubmoduleSup
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeFilteredColimitStage
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionOfColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectsAffine

/-!
# Containment of a finite type submodule over an étale space of an affine algebraic space

Let `W` be an affine algebraic space, `ℱ` a quasi-coherent `𝒪_W`-module, `g : T ⟶ W` an étale
morphism from a quasi-compact algebraic space and `𝒢 ⊆ ℱ|_T` a submodule of finite type. This file
proves that `𝒢` is contained in the restriction to `T` of a quasi-coherent submodule of `ℱ` of
finite type.

## Main results

* `AlgebraicGeometry.Space.exists_le_etaleSubmoduleRestrict_of_isAffineSpace`: the affine case.

## References

* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 01BB](https://stacks.math.columbia.edu/tag/01BB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.SheafOfModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The affine case.**  Let `W` be an affine algebraic space, `ℱ` a quasi-coherent
`𝒪_W`-module, `g : T ⟶ W` étale with `T` quasi-compact and `𝒢 ⊆ ℱ|_T` a submodule of finite
type.  Then `𝒢` is contained in the restriction to `T` of a quasi-coherent submodule of `ℱ` of
finite type. -/
theorem exists_le_etaleSubmoduleRestrict_of_isAffineSpace (W : AlgebraicSpaces B S hS)
    (hWa : IsAffineSpace B S hS W.1) (F : Modules.{u, u} B S hS W.1 W.2)
    (hF : F.IsQuasicoherentOnSite) {T : AlgebraicSpaces B S hS} (g : T ⟶ W)
    (hg : IsEtale B S hS g.hom) (hTqc : IsQuasiCompactSpace B S hS T.1)
    (G : ((etaleModulePullback.{u, u} B S hS g hg).obj F).Submodule)
    (hGf : G.toSheafOfModules.IsFiniteType) :
    ∃ K : F.Submodule, K.toSheafOfModules.IsQuasicoherentOnSite ∧
      K.toSheafOfModules.IsFiniteType ∧ G ≤ etaleSubmoduleRestrict B S hS g hg K := by
  classical
  have : F.IsQuasicoherentOnSite := hF
  have hesW : EssentiallySmall.{u} (smallEtaleRingedSite B S hS W.1 W.2).C := by
    change EssentiallySmall.{u} (SmallEtale B S hS W.1)
    infer_instance
  let habW : Abelian (Modules.{u, u} B S hS W.1 W.2) :=
    SheafOfModules.instAbelian.{u, u, u, u + 1}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O))
  have hgrW : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS W.1 W.2) :=
    SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _
  have hLlim : PreservesFiniteLimits (etaleModulePullback.{u, u} B S hS g hg) :=
    preservesFiniteLimits_etaleModulePullback B S hS g hg
  have hLcos : PreservesLimitsOfShape WalkingCospan (etaleModulePullback.{u, u} B S hS g hg) :=
    hLlim.preservesFiniteLimits WalkingCospan
  have hLcol : PreservesColimitsOfSize.{u, u} (etaleModulePullback.{u, u} B S hS g hg) :=
    preservesColimitsOfSize_etaleModulePullback B S hS g hg
  have hcol : IsColimit (finiteTypeQuasicoherentSubobjectCocone B S hS W.1 W.2 F) :=
    (nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone_of_isAffineSpace B S hS W.2
      hWa F).some
  have hfil : IsFiltered (FiniteTypeQuasicoherentSubobject B S hS W.1 W.2 F) :=
    isFiltered_finiteTypeQuasicoherentSubobject B S hS W.1 W.2 F
  have hsmall : Small.{u} (FiniteTypeQuasicoherentSubobject B S hS W.1 W.2 F) :=
    small_of_injective (f := fun T => T.obj)
      (fun a b h => by cases a; cases b; subst h; rfl)
  have hess : EssentiallySmall.{u} (FiniteTypeQuasicoherentSubobject B S hS W.1 W.2 F) :=
    inferInstance
  set eqv := (equivSmallModel.{u} (FiniteTypeQuasicoherentSubobject B S hS W.1 W.2 F)).symm
    with heqv
  have hfil' : IsFiltered (SmallModel.{u} (FiniteTypeQuasicoherentSubobject B S hS W.1 W.2 F)) :=
    IsFiltered.of_equivalence
      (equivSmallModel.{u} (FiniteTypeQuasicoherentSubobject B S hS W.1 W.2 F))
  set D' := eqv.functor ⋙ finiteTypeQuasicoherentSubobjectFunctor B S hS W.1 W.2 F with hD'
  set c' := (finiteTypeQuasicoherentSubobjectCocone B S hS W.1 W.2 F).whisker eqv.functor
    with hc'
  have hc'col : IsColimit c' := hcol.whiskerEquivalence eqv
  have hιmono : ∀ i, Mono (c'.ι.app i) := by
    intro i
    change Mono (eqv.functor.obj i).obj.arrow
    infer_instance
  have hDmono : ∀ {i i' : SmallModel.{u} (FiniteTypeQuasicoherentSubobject B S hS W.1 W.2 F)}
      (f : i ⟶ i'), Mono (D'.map f) := fun {i _} f ↦
    have := hιmono i
    mono_of_mono_fac (c'.w f)
  have hLDmono : ∀ {i i' : SmallModel.{u} (FiniteTypeQuasicoherentSubobject B S hS W.1 W.2 F)}
      (f : i ⟶ i'), Mono ((D' ⋙ etaleModulePullback.{u, u} B S hS g hg).map f) := fun f ↦
    have := hDmono f
    preserves_mono_of_preservesLimit (etaleModulePullback.{u, u} B S hS g hg) (D'.map f)
  obtain ⟨k, hk⟩ := exists_stage_of_isFiniteType_of_isQuasiCompactSpace B S hS hTqc
    (D' ⋙ etaleModulePullback.{u, u} B S hS g hg)
    ((etaleModulePullback.{u, u} B S hS g hg).mapCocone c')
    (isColimitOfPreserves (etaleModulePullback.{u, u} B S hS g hg) hc'col) hLDmono G.ι hGf
  have hm : Mono (c'.ι.app k) := hιmono k
  let K := ImageSubsheaf.monoRangeSubmodule (c'.ι.app k)
  have hKq : (D'.obj k).IsQuasicoherentOnSite := (eqv.functor.obj k).property.1
  have hKf : (D'.obj k).IsFiniteType := (eqv.functor.obj k).property.2
  obtain ⟨hKq', hKf'⟩ :=
    isQuasicoherentOnSite_isFiniteType_monoRangeSubmodule_of_mono B S hS (c'.ι.app k) hKq hKf
  refine ⟨K, hKq', hKf', fun V s hs ↦ ?_⟩
  obtain ⟨y, hy⟩ := hk V ⟨s, hs⟩
  exact ⟨y, hy⟩

end AlgebraicGeometry.Space

end
