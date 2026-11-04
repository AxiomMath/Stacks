module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleRelocalize
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeReflectsRepresentable

/-!
# Relative ampleness does not depend on the base

Let `h : W ⟶ S` be a morphism of a big fppf site and `Λ` the lower-shriek extension, which views
an algebraic space over `W` as one over `S`. For a morphism `f : X ⟶ Y` of algebraic spaces over
`W` and an invertible `𝒪_{Λ X}`-module `M`, the module `M` read over `W`
(`AlgebraicGeometry.Space.moduleDerelocalize`) is ample relative to `f` (Stacks 0D31) exactly
when `M` is ample relative to `Λ f`.

## Main results

* `AlgebraicGeometry.Space.relativelyRepresentable_of_relocalize`: `Λ` reflects
  representability of morphisms.
* `AlgebraicGeometry.Space.isRelativelyAmple_moduleDerelocalize_iff`: relative ampleness over
  `W` and over `S` agree, for an invertible module.

## Implementation notes

A test square of Stacks 0D31 over `W` is carried by `Λ` to one over `S` with the same schemes
(`AlgebraicGeometry.Space.isPullback_relocalizeChart_of_isPullback`), and the two pullbacks of the
module to the corner agree (`AlgebraicGeometry.Space.baseChangeModuleDerelocalizeIso`). A test
square over `S` is isomorphic to the image of one over `W`, because the test scheme factors
through `W` (`AlgebraicGeometry.exists_relocalizeChart`); the comparison is an isomorphism of
schemes, along which relative ampleness is carried by Stacks 0893.

## References

* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AmpleLocallyClosed (pullbackModule)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {W S : Scheme.{u}} {hW : B.Contains W} {hS : B.Contains S}
  (h : B.obj hW ⟶ B.obj hS)

/-- **`Λ` reflects representability of morphisms.** -/
theorem relativelyRepresentable_of_relocalize {X Y : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable ((OverShriek.relocalizePresheafFunctor h).map f)) :
    yoneda.relativelyRepresentable f := by
  have _ : PreservesLimitsOfShape WalkingCospan (OverShriek.relocalizePresheafFunctor h) :=
    relocalizePresheaf_preservesConnectedLimits h
  refine (yoneda_relativelyRepresentable_iff_pullback_representable f).2 fun T ξ => ?_
  set y := yonedaEquiv.symm ξ
  have hsq := ((IsPullback.of_hasPullback y f).map (OverShriek.relocalizePresheafFunctor h)).flip
  have hsq' : IsPullback ((OverShriek.relocalizePresheafFunctor h).map (pullback.snd y f))
      ((OverShriek.relocalizePresheafFunctor h).map (pullback.fst y f) ≫
        (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h T).hom)
      ((OverShriek.relocalizePresheafFunctor h).map f) (relocalizeChart B W S hW hS h y) := by
    refine hsq.of_iso (Iso.refl _) (Iso.refl _) (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h T)
      (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp [relocalizeChart]
  obtain ⟨T', -, ⟨e⟩⟩ := OverShriek.exists_left_eq_nonempty_iso_yoneda h
    (hsq'.isoIsPullback _ _ (hf.isPullback (relocalizeChart B W S hW hS h y)))
  exact Functor.IsRepresentable.mk' e.symm

/-- Relative ampleness over `S` of the extended morphism gives relative ampleness over `W` of the
module read over `W`. -/
theorem isRelativelyAmple_of_isRelativelyAmple_relocalize {X Y : AlgebraicSpaces B W hW}
    {f : X ⟶ Y} {M : Modules.{u, u} B S hS (relocalizeSpace B hW hS h X).1
      (relocalizeSpace B hW hS h X).2}
    (hamp : IsRelativelyAmple B S hS (relocalizeSpaceMap h f) M) :
    IsRelativelyAmple B W hW f ((moduleDerelocalize B W S hW hS h X).obj M) := by
  refine ⟨relativelyRepresentable_of_relocalize h hamp.1, fun T U g p q hsq => ?_⟩
  obtain ⟨hinv, ha⟩ := hamp.2 ((Over.map h).obj T) ((Over.map h).obj U)
    (relocalizeChart B W S hW hS h g) (relocalizeChart B W S hW hS h p) ((Over.map h).map q)
    (isPullback_relocalizeChart_of_isPullback h hsq)
  let e := baseChangeModuleDerelocalizeIso h X M U p
  have hinv' : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B W hW).obj U)
      (baseChangeModule B W hW ((moduleDerelocalize B W S hW hS h X).obj M) U p) :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e.symm
  exact ⟨hinv', (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ e.symm).mp ha⟩

/-- Relative ampleness over `W` of an invertible module read over `W` gives relative ampleness over
`S` of the extended morphism. -/
theorem isRelativelyAmple_relocalize_of_isRelativelyAmple {X Y : AlgebraicSpaces B W hW}
    {f : X ⟶ Y} {M : Modules.{u, u} B S hS (relocalizeSpace B hW hS h X).1
      (relocalizeSpace B hW hS h X).2}
    (hM : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS (relocalizeSpace B hW hS h X).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (relocalizeSpace B hW hS h X).1 (relocalizeSpace B hW hS h X).2).O)).property M)
    (hamp : IsRelativelyAmple B W hW f ((moduleDerelocalize B W S hW hS h X).obj M)) :
    IsRelativelyAmple B S hS (relocalizeSpaceMap h f) M := by
  refine ⟨relativelyRepresentable_relocalize h hamp.1, fun T' U' g' p' q' hsq => ?_⟩
  obtain ⟨ψ, hψ, g, hg⟩ := exists_relocalizeChart B W S hW hS h T' g'
  -- the test square over `W` along the descended chart
  have hsqW := hamp.1.isPullback g
  have hsqS := isPullback_relocalizeChart_of_isPullback h hsqW
  let ρ := relocalizeBaseHom B W S hW hS h hψ
  have hsq₂ : IsPullback p' (yoneda.map (q' ≫ ρ))
      ((OverShriek.relocalizePresheafFunctor h).map f.hom) (relocalizeChart B W S hW hS h g) := by
    rw [hg] at hsq
    refine hsq.of_iso (Iso.refl _) (Iso.refl _) (yoneda.mapIso (asIso ρ)) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp only [Iso.refl_hom, Category.comp_id]
      rfl
  let κ' := hsq₂.isoIsPullback _ _ hsqS
  let κ := yoneda.preimageIso κ'
  have hκp : yoneda.map κ.hom ≫ relocalizeChart B W S hW hS h (hamp.1.fst g) = p' := by
    simp only [κ, Functor.preimageIso_hom, Functor.map_preimage]
    exact IsPullback.isoIsPullback_hom_fst _ _ hsq₂ hsqS
  have hκq : κ.hom ≫ (Over.map h).map (hamp.1.snd g) = q' ≫ ρ := by
    apply yoneda.map_injective
    simp only [κ, Functor.preimageIso_hom, Functor.map_comp, Functor.map_preimage]
    exact IsPullback.isoIsPullback_hom_snd _ _ hsq₂ hsqS
  -- ampleness over `W`, read over `S`
  obtain ⟨hinv₀, ha₀⟩ := hamp.2 (Over.mk ψ) (hamp.1.pullback g) g (hamp.1.fst g) (hamp.1.snd g) hsqW
  let e₀ := baseChangeModuleDerelocalizeIso h X M (hamp.1.pullback g) (hamp.1.fst g)
  have hinvN : Stacks.Ample.IsInvertibleModule
      ((BigFppfOver.toScheme B S hS).obj ((Over.map h).obj (hamp.1.pullback g)))
      (baseChangeModule B S hS M ((Over.map h).obj (hamp.1.pullback g))
        (relocalizeChart B W S hW hS h (hamp.1.fst g))) :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e₀
  have haN : @Stacks.RelativeAmple.IsRelativelyAmple _ _
      ((BigFppfOver.toScheme B S hS).map ((Over.map h).map (hamp.1.snd g)))
      (baseChangeModule B S hS M ((Over.map h).obj (hamp.1.pullback g))
        (relocalizeChart B W S hW hS h (hamp.1.fst g))) hinvN :=
    (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ e₀).mp ha₀
  -- pulling back along the comparison of corners
  obtain ⟨e₁⟩ := nonempty_baseChangeModule_baseChange_of_isInvertible M hM
    ((Over.map h).obj (hamp.1.pullback g)) U' (relocalizeChart B W S hW hS h (hamp.1.fst g)) κ.hom
  rw [hκp] at e₁
  have hpb : IsPullback ((BigFppfOver.toScheme B S hS).map κ.hom)
      ((BigFppfOver.toScheme B S hS).map q')
      ((BigFppfOver.toScheme B S hS).map ((Over.map h).map (hamp.1.snd g)))
      ((BigFppfOver.toScheme B S hS).map ρ) :=
    IsPullback.of_horiz_isIso ⟨by rw [← Functor.map_comp, hκq, Functor.map_comp]⟩
  have ha' := Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback hpb _ haN
  have hinv' : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U')
      (baseChangeModule B S hS M U' p') :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e₁.symm
  exact ⟨hinv', (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ e₁.symm).mp ha'⟩

/-- **Relative ampleness does not depend on the base.** For an invertible `𝒪_{Λ X}`-module `M`,
the module `M` read over `W` is ample relative to `f` exactly when `M` is ample relative to
`Λ f`. -/
theorem isRelativelyAmple_moduleDerelocalize_iff {X Y : AlgebraicSpaces B W hW}
    (f : X ⟶ Y) (M : Modules.{u, u} B S hS (relocalizeSpace B hW hS h X).1
      (relocalizeSpace B hW hS h X).2)
    (hM : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS (relocalizeSpace B hW hS h X).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (relocalizeSpace B hW hS h X).1 (relocalizeSpace B hW hS h X).2).O)).property M) :
    IsRelativelyAmple B W hW f ((moduleDerelocalize B W S hW hS h X).obj M) ↔
      IsRelativelyAmple B S hS (relocalizeSpaceMap h f) M :=
  ⟨isRelativelyAmple_relocalize_of_isRelativelyAmple h hM,
    isRelativelyAmple_of_isRelativelyAmple_relocalize h⟩

end AlgebraicGeometry.Space

end
