module

public import StacksFrontier.AlgebraicGeometry.Descent.RelativeAmpleFpqcLocalOnBaseFull
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseChangeModuleInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleEtaleBaseChange

/-!
# Relative ampleness descends along a surjective étale chart of an affine base, for a scheme

Let `V ⟶ U` be a surjective étale morphism of affine schemes, let `f : X ⟶ U` be a morphism of
algebraic spaces whose source `X` is a scheme, let `L` be an invertible `𝒪_X`-module and let
`Y = V ×_U X`. If the pullback of `L` to `Y` is ample on `Y/V` then `L` is ample on `X/U`.

This is the last step of the proof of [Stacks, Tag 0D35]: once `X` is known to be a scheme, the
statement is the descent of relative ampleness for schemes along `V ⟶ U`, which is
[Stacks, Tag 0D2P] at the one-member fpqc covering `{V ⟶ U}`,
`Stacks.Descent.isRelativelyAmple_of_forall_of_fpqcCover`, at the
cartesian square of schemes `Y ⟶ X` over `V ⟶ U`, and the invertibility of the reading of `L`
on the scheme `X`, `AlgebraicGeometry.Space.isInvertibleModule_baseChangeModule`.

## Main results

* `AlgebraicGeometry.Space.isRelativelyAmple_of_baseChange_etale_of_isRepresentable`: the
  statement above.

## References

* [Stacks Project, Tag 0D35](https://stacks.math.columbia.edu/tag/0D35)
* [Stacks Project, Tag 0D2P](https://stacks.math.columbia.edu/tag/0D2P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AmpleLocallyClosed (pullbackModule)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance (priority := high) hasPullbacks_presheaf_relativeAmpleEtaleDescentRepresentable :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

/-- Discrete limits of presheaves on the big fppf site (instance search times out without this
shortcut). -/
private instance (priority := high)
    hasLimitsOfShape_discrete_presheaf_relativeAmpleEtaleDescentRepresentable (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

private instance (priority := high) hasPullback_presheaf_relativeAmpleEtaleDescentRepresentable
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Relative ampleness descends along a surjective étale morphism of affine bases, for a
representable source.** Let `g : V ⟶ U` be a morphism of algebraic spaces which are the affine
schemes `V₀` and `U₀`, induced by a surjective étale `h₀ : V₀ ⟶ U₀`, let `f : X ⟶ U` be a
morphism of algebraic spaces with `X` representable, let `L` be an invertible `𝒪_X`-module, and
let `pr : Y ⟶ X`, `f' : Y ⟶ V` present `Y` as `V ×_U X`. If the pullback of `L` to `Y` is ample
on `Y/V`, then `L` is ample on `X/U`. -/
theorem isRelativelyAmple_of_baseChange_etale_of_isRepresentable
    {U V X Y : AlgebraicSpaces B S hS} {f : X ⟶ U} {g : V ⟶ U} {f' : Y ⟶ V} {pr : Y ⟶ X}
    (hsq : IsPullback pr f' f g) (L : Modules.{u, u} B S hS X.1 X.2)
    (hLinv : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    (U₀ V₀ : BigFppfOver B S hS) (hU₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀))
    (hV₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj V₀))
    (eU : U.1 ≅ yoneda.obj U₀) (eV : V.1 ≅ yoneda.obj V₀)
    (h₀ : V₀ ⟶ U₀) (hg : g.hom ≫ eU.hom = eV.hom ≫ yoneda.map h₀)
    (hsurj : Surjective ((BigFppfOver.toScheme B S hS).map h₀))
    (hetale : Etale ((BigFppfOver.toScheme B S hS).map h₀))
    (hX : X.1.IsRepresentable)
    (hN : IsRelativelyAmple B S hS f' ((modulePullback B S hS pr).obj L)) :
    IsRelativelyAmple B S hS f L := by
  obtain ⟨Y₀, eY, hNinv, hNamp⟩ := hN.exists_scheme V₀ eV
  have := hX
  refine isRelativelyAmple_of_exists_scheme f L hLinv U₀ eU
    ⟨X.1.reprX, X.1.reprW, ?_⟩
  have hpr : yoneda.map (yoneda.preimage (eY.hom ≫ pr.hom ≫ X.1.reprW.inv)) ≫
      X.1.reprW.hom = eY.hom ≫ pr.hom := by simp
  -- the given square, read on the underlying presheaves
  have hpre : IsPullback pr.hom f'.hom f.hom g.hom := by
    have hcan := AlgebraicSpaces.isPullback_fiberProduct B S hS f g
    exact IsPullback.of_iso_pullback ⟨congrArg InducedCategory.Hom.hom hsq.w⟩
      ((ObjectProperty.ι _).mapIso (hsq.isoIsPullback _ _ hcan))
      (congrArg InducedCategory.Hom.hom (hsq.isoIsPullback_hom_fst _ _ hcan))
      (congrArg InducedCategory.Hom.hom (hsq.isoIsPullback_hom_snd _ _ hcan))
  have hsq₁ : IsPullback (yoneda.map (yoneda.preimage (eY.hom ≫ pr.hom ≫ X.1.reprW.inv)))
      (yoneda.map (yoneda.preimage (eY.hom ≫ f'.hom ≫ eV.hom)))
      (yoneda.map (yoneda.preimage (X.1.reprW.hom ≫ f.hom ≫ eU.hom))) (yoneda.map h₀) :=
    hpre.of_iso eY.symm X.1.reprW.symm eV eU
      (by simp) (by simp) (by simp) hg
  have hsq₂ := IsPullback.of_map yoneda (yoneda.map_injective (by simpa using hsq₁.w)) hsq₁
  obtain ⟨e⟩ := nonempty_baseChangeModule_baseChange_of_isInvertible L hLinv X.1.reprX Y₀
    X.1.reprW.hom (yoneda.preimage (eY.hom ≫ pr.hom ≫ X.1.reprW.inv))
  rw [hpr] at e
  have hMinv := isInvertibleModule_baseChangeModule L hLinv X.1.reprX X.1.reprW.hom
  have := hNinv
  have := hU₀
  have := hV₀
  have : Flat ((BigFppfOver.toScheme B S hS).map h₀) := inferInstance
  have hcov : Presieve.ofArrows (fun _ : PUnit.{u + 1} => (BigFppfOver.toScheme B S hS).obj V₀)
      (fun _ => (BigFppfOver.toScheme B S hS).map h₀) ∈
        Scheme.fpqcPrecoverage ((BigFppfOver.toScheme B S hS).obj U₀) := by
    rw [Presieve.ofArrows_pUnit]
    exact ((BigFppfOver.toScheme B S hS).map h₀).singleton_mem_fpqcPrecoverage
  refine ⟨hMinv, ?_⟩
  refine Stacks.Descent.isRelativelyAmple_of_forall_of_fpqcCover hcov _ _
    (fun _ => hsq₂.map (BigFppfOver.toScheme B S hS)) fun _ => ?_
  exact (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _
    ((baseChangeModuleCompIso B S hS pr L Y₀ eY.hom).symm ≪≫ e)).mp hNamp

end AlgebraicGeometry.Space

end
