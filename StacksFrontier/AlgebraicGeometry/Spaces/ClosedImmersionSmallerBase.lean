module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase

/-!
# Closed immersions and a change of base scheme

Let `h : W ⟶ S` be a morphism of a big fppf site and let `Λ_h` be the lower-shriek extension
`CategoryTheory.OverShriek.relocalizePresheafFunctor h` of Stacks 03I5 part (2).

`AlgebraicGeometry.presheaf_relocalizeMap_of` of
`StacksFrontier/AlgebraicGeometry/Spaces/ProperSmallerBase.lean` shows that a property of a morphism
of presheaves tested on its representable base changes is *inherited from* its extension. This
file proves the converse implication, so that such a property is *unchanged* by the extension,
and reads it at closed immersions: being a closed immersion of algebraic spaces does not depend
on the base scheme it is read over.

## Main results

* `AlgebraicGeometry.presheaf_relocalizeMap`: a property of a morphism of presheaves tested on
  representable base changes is carried to its lower-shriek extension.
* `AlgebraicGeometry.Space.isClosedImmersion_relocalizeMap_iff`: being a closed immersion is
  unchanged by the lower-shriek extension.
* `AlgebraicGeometry.Space.isClosedImmersion_relocalizeToYoneda_iff`: the structural morphism of
  a lower-shriek extension is a closed immersion exactly when the structural morphism to the
  terminal object of the big fppf site of `W` is one.
* `AlgebraicGeometry.Space.isClosedImmersion_spacesOverSmallerBaseFunctor_iff`: the structural
  morphism of the image of Stacks 04SG's forward functor is a closed immersion over `S` exactly
  when it is one over a larger base `S'`.

## Implementation notes

The argument is the one of the converse direction of
`AlgebraicGeometry.presheaf_relocalizeChart_iff`, with the chart replaced by an arbitrary
morphism: every scheme-valued point of `Λ_h Y` is the extension of a point of `Y`
(`AlgebraicGeometry.exists_relocalizeChart`), the extension preserves fibre products
(`AlgebraicGeometry.relocalizePresheaf_preservesConnectedLimits`) and carries representable
presheaves to representable presheaves (Stacks 03I4 part (2)), and corresponding base changes
have the same underlying morphism of schemes.

## References

* [Stacks Project, Tag 03I4](https://stacks.math.columbia.edu/tag/03I4)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS)

/-- **A property of a morphism of presheaves, tested on representable base changes, is carried to
its lower-shriek extension.** The converse of `AlgebraicGeometry.presheaf_relocalizeMap_of`. -/
theorem presheaf_relocalizeMap (Q : MorphismProperty Scheme.{u})
    [MorphismProperty.RespectsIso Q]
    {X Y : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u} (k : X ⟶ Y)
    (hk : (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B W hW)).presheaf k) :
    (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf
      ((OverShriek.relocalizePresheafFunctor h).map k) := by
  have _ : PreservesLimitsOfShape WalkingCospan (OverShriek.relocalizePresheafFunctor h) :=
    relocalizePresheaf_preservesConnectedLimits h
  refine MorphismProperty.relative.of_exists (F := yoneda) ?_
  intro V' e'
  obtain ⟨ψ, hψ, e₀, he⟩ := exists_relocalizeChart B W S hW hS h V' e'
  have hpull₀ := hk.1.isPullback e₀
  have hQr₀ := hk.2 e₀ (hk.1.fst e₀) (hk.1.snd e₀) hpull₀
  set T₀ := hk.1.pullback e₀
  set r₀ := hk.1.snd e₀
  set p₀ := hk.1.fst e₀
  have hpullS : IsPullback
      ((relocalizedYonedaIso B (B.obj hW) (B.obj hS) h T₀).inv ≫
        (OverShriek.relocalizePresheafFunctor h).map p₀)
      (yoneda.map ((Over.map h).map r₀))
      ((OverShriek.relocalizePresheafFunctor h).map k)
      (relocalizeChart B W S hW hS h e₀) := by
    refine (hpull₀.map (OverShriek.relocalizePresheafFunctor h)).of_iso
      (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h T₀) (Iso.refl _)
      (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · exact (relocalizedYonedaIso_naturality B (B.obj hW) (B.obj hS) h r₀).symm
    · simp
    · simp [relocalizeChart]
  set ι := relocalizeBaseHom B W S hW hS h hψ
  refine ⟨(Over.map h).obj T₀,
    (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h T₀).inv ≫
      (OverShriek.relocalizePresheafFunctor h).map p₀,
    (Over.map h).map r₀ ≫ inv ι, ?_, ?_⟩
  · refine hpullS.of_iso (Iso.refl _) (Iso.refl _)
      (yoneda.mapIso (asIso ι)).symm (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp [he]
  · exact MorphismProperty.RespectsIso.postcomp Q
      ((BigFppfOver.toScheme B S hS).map (inv ι))
      ((BigFppfOver.toScheme B S hS).map ((Over.map h).map r₀)) hQr₀

namespace Space

/-- Being a closed immersion of presheaves respects isomorphisms: it is a base-change-stable
property of morphisms of presheaves. -/
theorem isClosedImmersion_respectsIso :
    MorphismProperty.RespectsIso (@Space.IsClosedImmersion B S hS) := by
  have h₁ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact MorphismProperty.IsStableUnderBaseChange.respectsIso

/-- **Being a closed immersion is unchanged by the lower-shriek extension.** -/
theorem isClosedImmersion_relocalizeMap_iff {X Y : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    (k : X ⟶ Y) :
    IsClosedImmersion B S hS ((OverShriek.relocalizePresheafFunctor h).map k) ↔
      IsClosedImmersion B W hW k :=
  ⟨isClosedImmersion_of_relocalizeMap B W S hW hS h k,
    presheaf_relocalizeMap B W S hW hS h
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) k⟩

/-- **The structural morphism of a lower-shriek extension is a closed immersion exactly when the
structural morphism over `W` is one.** -/
theorem isClosedImmersion_relocalizeToYoneda_iff (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) :
    IsClosedImmersion B S hS (OverShriek.relocalizeToYoneda h F) ↔
      IsClosedImmersion B W hW (toYonedaId B W hW F) := by
  have _ := isIso_relocalizeToYoneda_yonedaId B W S hW hS h
  have _ := isClosedImmersion_respectsIso B S hS
  rw [← relocalizeToYoneda_eq_map_toYonedaId B W S hW hS h F,
    MorphismProperty.cancel_right_of_respectsIso (@Space.IsClosedImmersion B S hS)]
  exact isClosedImmersion_relocalizeMap_iff B W S hW hS h (toYonedaId B W hW F)

variable (S' : Scheme.{u}) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')

/-- **The structural morphism of an algebraic space over `W` is a closed immersion over `S`
exactly when it is one over a larger base `S'`.** Both sides are the condition over `W` itself. -/
theorem isClosedImmersion_relocalizeToYoneda_comp_iff (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) :
    IsClosedImmersion B S' hS' (OverShriek.relocalizeToYoneda (h ≫ g) F) ↔
      IsClosedImmersion B S hS (OverShriek.relocalizeToYoneda h F) :=
  (isClosedImmersion_relocalizeToYoneda_iff B W S' hW hS' (h ≫ g) F).trans
    (isClosedImmersion_relocalizeToYoneda_iff B W S hW hS h F).symm

/-- **Being a closed immersion, for the structural morphism of the image of Stacks 04SG's forward
functor, does not depend on the base.** An algebraic space over `W`, viewed over `S` along `h` and
over `S'` along a factorization `h ≫ g`, has closed immersion structural morphism over `S`
exactly when it has one over `S'`. The companion at closed immersions of
`AlgebraicGeometry.Space.isQuasiCompact_spacesOverSmallerBaseFunctor_iff`. -/
theorem isClosedImmersion_spacesOverSmallerBaseFunctor_iff
    (u : B.obj hW ⟶ B.obj hS') (hg : h ≫ g = u)
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B W hW F) :
    IsClosedImmersion B S' hS'
        (((spacesOverSmallerBaseFunctor B W S' hW hS' u).obj ⟨F, hF⟩).1.hom) ↔
      IsClosedImmersion B S hS
        (((spacesOverSmallerBaseFunctor B W S hW hS h).obj ⟨F, hF⟩).1.hom) := by
  subst hg
  have _ := isClosedImmersion_respectsIso B S hS
  have _ := isClosedImmersion_respectsIso B S' hS'
  rw [← MorphismProperty.cancel_left_of_respectsIso (@Space.IsClosedImmersion B S hS)
      ((spacesOverSmallerBaseFunctorForgetIso B W S hW hS h).inv.app ⟨F, hF⟩) _,
    ← MorphismProperty.cancel_left_of_respectsIso (@Space.IsClosedImmersion B S' hS')
      ((spacesOverSmallerBaseFunctorForgetIso B W S' hW hS' (h ≫ g)).inv.app ⟨F, hF⟩) _,
    relocalizeToYoneda_eq B W S hW hS h ⟨F, hF⟩,
    relocalizeToYoneda_eq B W S' hW hS' (h ≫ g) ⟨F, hF⟩]
  exact isClosedImmersion_relocalizeToYoneda_comp_iff B W S hW hS h S' hS' g F

end Space

end AlgebraicGeometry

end
