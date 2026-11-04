module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeComposite

/-!
# Quasi-compactness, quasi-separatedness and a change of base scheme (Stacks 03HE, 03HL, 04SG)

Let `h : W ⟶ S` be a morphism of a big fppf site and let `Λ_h` be the lower-shriek extension
`CategoryTheory.OverShriek.relocalizePresheafFunctor h` of Stacks 03I5 part (2), which carries an
algebraic space over `W` to an algebraic space over `S` together with a morphism to the
representable algebraic space of `W`.

This file proves that **quasi-compactness** (Stacks 03HE) and **quasi-separatedness**
(Stacks 03HL, part (3)) of the structural morphism of an algebraic space over `W` do not depend
on the base it is read over: an algebraic space over `W`, viewed over `S` and then over a larger
base `S'`, has quasi-compact structural morphism over `S` as soon as it has one over `S'`, and
likewise for quasi-separatedness.

That is the step a separation condition needs in order to be transferred along Construction A of
Stacks 04X5, in the shape the quantifier of Stacks 04XB leaves it in. The
every-étale-chart conditions of Stacks 03MJ are already base-independent for an *arbitrary*
property of morphisms of schemes, by
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_iff`; the two
conditions here are not of that shape — quasi-compactness quantifies over quasi-compact algebraic
spaces mapping to the target — so they need their own statements.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompactSpace_relocalizePresheafFunctor_obj` and
  `AlgebraicGeometry.Space.isQuasiCompactSpace_of_relocalize`: quasi-compactness of an algebraic
  space (**Stacks 03E3**) is unchanged by the lower-shriek extension.
* `AlgebraicGeometry.Space.isQuasiCompact_of_relocalizeMap` and
  `AlgebraicGeometry.Space.isQuasiSeparated_of_relocalizeMap`: a morphism of presheaves on the
  big fppf site of `W` is quasi-compact, resp. quasi-separated, as soon as its lower-shriek
  extension is.
* `AlgebraicGeometry.Space.isQuasiCompact_spacesOverSmallerBaseFunctor_of` and
  `AlgebraicGeometry.Space.isQuasiSeparated_spacesOverSmallerBaseFunctor_of`: **Stacks 03HE** and
  **Stacks 03HL** part (3) for the structural morphism of the image of Stacks 04SG's forward
  functor do not depend on the base.

## Implementation notes

The argument is the one direction of base-independence that needs no essential surjectivity, and
that is why it is stated as an implication rather than an equivalence. Reading the condition over
the *smaller* base `S` means quantifying over algebraic spaces over `S`; each of them can be
*pushed forward* to the larger base `S'` by `Λ_g`, which preserves algebraicity (Stacks 03I5
part (2)), preserves and reflects quasi-compactness (the two results above), and preserves fibre
products. The converse direction would need every algebraic space over `S'` mapping to the
representable of `W` to come from one over `S`, which is the essential surjectivity of the
equivalence of Stacks 04SG and is not needed here.

Quasi-compactness of an algebraic space is unchanged by `Λ_h` because every chart of `Λ_h F` is
the extension of a chart of `F` (`AlgebraicGeometry.exists_relocalizeChart`), corresponding
charts have the same underlying scheme, and being surjective or étale is unchanged
(`AlgebraicGeometry.presheaf_relocalizeChart_iff`, together with
`AlgebraicGeometry.Space.isEtale_iff_presheaf_of_yoneda` identifying étaleness of a chart as a
morphism of algebraic spaces with the relatively representable property).

Quasi-separatedness is quasi-compactness of the relative diagonal, so it is the quasi-compact
statement applied to the diagonal: the extension of the diagonal *is* the diagonal of the
extension, because the extension preserves fibre products and the diagonal is determined by its
two projections.

The passage from `CategoryTheory.OverShriek.relocalizeToYoneda h F` over `S` to
`CategoryTheory.OverShriek.relocalizeToYoneda (h ≫ g) F` over `S'` uses
`CategoryTheory.OverShriek.relocalizeToYoneda_comp_relocalizeYonedaComp`, and the passage to the
structural morphism that Stacks 04SG's forward functor produces uses
`AlgebraicGeometry.Space.relocalizeToYoneda_eq`; both are read through
`CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`, quasi-compactness of morphisms of
presheaves being packaged as the morphism property
`AlgebraicGeometry.Space.quasiCompactPresheafProperty`, which is stable under base change and
therefore respects isomorphisms.

## References

* [Stacks Project, Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] etale_scheme_respectsIso

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS)

/-! ### Quasi-compactness of an algebraic space and the lower-shriek extension -/

/-- **The lower-shriek extension preserves quasi-compactness of an algebraic space.** The
extension of a quasi-compact, surjective, étale chart is one: it has the same underlying scheme,
and surjectivity and étaleness are unchanged by the extension. -/
theorem Space.isQuasiCompactSpace_relocalizePresheafFunctor_obj
    (X : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) (hX : Space.IsQuasiCompactSpace B W hW X) :
    Space.IsQuasiCompactSpace B S hS ((OverShriek.relocalizePresheafFunctor h).obj X) := by
  obtain ⟨U, c, hcompact, hsurj, hetale⟩ := hX
  refine ⟨(Over.map h).obj U, relocalizeChart B W S hW hS h c, hcompact, ?_, ?_⟩
  · exact (presheaf_relocalizeChart_iff B W S hW hS h _ c).2 hsurj
  · rw [Space.isEtale_iff_presheaf_of_yoneda]
    exact (presheaf_relocalizeChart_iff B W S hW hS h _ c).2
      ((Space.isEtale_iff_presheaf_of_yoneda B W hW c).1 hetale)

/-- **The lower-shriek extension reflects quasi-compactness of an algebraic space.** Every chart
of the extension is the extension of a chart, up to an isomorphism of the site which is the
identity on underlying schemes, so a quasi-compact surjective étale chart of the extension
descends to one of the original presheaf. -/
theorem Space.isQuasiCompactSpace_of_relocalize (X : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u)
    (hX : Space.IsQuasiCompactSpace B S hS
      ((OverShriek.relocalizePresheafFunctor h).obj X)) :
    Space.IsQuasiCompactSpace B W hW X := by
  obtain ⟨U', c', hcompact, hsurj, hetale⟩ := hX
  obtain ⟨ψ, hψ, c, hce⟩ := exists_relocalizeChart B W S hW hS h U' c'
  rw [Space.isEtale_iff_presheaf_of_yoneda] at hetale
  rw [hce] at hsurj hetale
  have key (Q : MorphismProperty Scheme.{u}) [Q.RespectsIso]
      (hQ : (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf
        (yoneda.map (relocalizeBaseHom B W S hW hS h hψ) ≫
          relocalizeChart B W S hW hS h c)) :
      (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B W hW)).presheaf c :=
    (presheaf_relocalizeChart_iff B W S hW hS h Q c).1
      ((MorphismProperty.cancel_left_of_respectsIso _ _ _).1 hQ)
  refine ⟨Over.mk ψ, c, hcompact, key _ hsurj, ?_⟩
  rw [Space.isEtale_iff_presheaf_of_yoneda]
  exact key _ hetale

private instance : (Space.quasiCompactPresheafProperty B S hS).RespectsIso :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

private instance : MorphismProperty.RespectsIso (@Space.IsQuasiSeparated B S hS) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso
    (P := (Space.quasiCompactPresheafProperty B S hS).diagonal)

/-! ### Quasi-compactness and quasi-separatedness of a morphism -/

/-- **A morphism of presheaves on the big fppf site of `W` is quasi-compact as soon as its
lower-shriek extension is.** A quasi-compact algebraic space over `W` mapping to the target is
carried by the extension to a quasi-compact algebraic space over `S` mapping to the extended
target, and the extension preserves and reflects the fibre product and its quasi-compactness. -/
theorem Space.isQuasiCompact_of_relocalizeMap {X Y : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    (k : X ⟶ Y)
    (hk : Space.IsQuasiCompact B S hS ((OverShriek.relocalizePresheafFunctor h).map k)) :
    Space.IsQuasiCompact B W hW k := by
  have _ : PreservesLimitsOfShape WalkingCospan (OverShriek.relocalizePresheafFunctor h) :=
    relocalizePresheaf_preservesConnectedLimits h
  intro Z hZ hZqc γ
  refine Space.isQuasiCompactSpace_of_relocalize B W S hW hS h _ ?_
  refine Space.isQuasiCompactSpace_of_iso B S hS
    (PreservesPullback.iso (OverShriek.relocalizePresheafFunctor h) γ k).symm ?_
  exact hk _ (isAlgebraicSpace_viewOver B W S hW hS h Z hZ)
    (Space.isQuasiCompactSpace_relocalizePresheafFunctor_obj B W S hW hS h Z hZqc)
    ((OverShriek.relocalizePresheafFunctor h).map γ)

/-- **A morphism of presheaves on the big fppf site of `W` is quasi-separated as soon as its
lower-shriek extension is.** Quasi-separatedness is quasi-compactness of the relative diagonal,
and the extension of the diagonal *is* the diagonal of the extension, because the extension
preserves fibre products and the diagonal is determined by its two projections. -/
theorem Space.isQuasiSeparated_of_relocalizeMap {X Y : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    (k : X ⟶ Y)
    (hk : Space.IsQuasiSeparated B S hS ((OverShriek.relocalizePresheafFunctor h).map k)) :
    Space.IsQuasiSeparated B W hW k := by
  have : PreservesLimitsOfShape WalkingCospan (OverShriek.relocalizePresheafFunctor h) :=
    relocalizePresheaf_preservesConnectedLimits h
  have hdiag : (OverShriek.relocalizePresheafFunctor h).map (pullback.diagonal k) ≫
      (PreservesPullback.iso (OverShriek.relocalizePresheafFunctor h) k k).hom =
        pullback.diagonal ((OverShriek.relocalizePresheafFunctor h).map k) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, PreservesPullback.iso_hom_fst, ← Functor.map_comp,
        pullback.diagonal_fst, CategoryTheory.Functor.map_id]
    · simp only [Category.assoc, PreservesPullback.iso_hom_snd, ← Functor.map_comp,
        pullback.diagonal_snd, CategoryTheory.Functor.map_id]
  refine Space.isQuasiCompact_of_relocalizeMap B W S hW hS h (pullback.diagonal k) ?_
  refine (MorphismProperty.cancel_right_of_respectsIso
    (Space.quasiCompactPresheafProperty B S hS) _
    (PreservesPullback.iso (OverShriek.relocalizePresheafFunctor h) k k).hom).1 ?_
  rw [hdiag]
  exact hk

/-! ### Change of base scheme -/

section ChangeOfBase

variable (S' : Scheme.{u}) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')

/-- **Quasi-compactness of the structural morphism of a lower-shriek extension does not depend on
the base.** Both sides are read through
`CategoryTheory.OverShriek.relocalizeToYoneda_comp_relocalizeYonedaComp`, which exhibits the
structural morphism over `S'` as the image under `Λ_g` of the structural morphism over `S`. -/
theorem Space.isQuasiCompact_relocalizeToYoneda_comp_of
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u)
    (hF : Space.IsQuasiCompact B S' hS' (OverShriek.relocalizeToYoneda (h ≫ g) F)) :
    Space.IsQuasiCompact B S hS (OverShriek.relocalizeToYoneda h F) := by
  refine Space.isQuasiCompact_of_relocalizeMap B S S' hS hS' g _ ?_
  have h1 : Space.quasiCompactPresheafProperty B S' hS'
      (OverShriek.relocalizeToYoneda (h ≫ g) F ≫
        (OverShriek.relocalizeYonedaComp h g).hom) :=
    (MorphismProperty.cancel_right_of_respectsIso _ _ _).2 hF
  rw [OverShriek.relocalizeToYoneda_comp_relocalizeYonedaComp h g F] at h1
  exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).1 h1

/-- **Quasi-separatedness of the structural morphism of a lower-shriek extension does not depend
on the base.** -/
theorem Space.isQuasiSeparated_relocalizeToYoneda_comp_of
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u)
    (hF : Space.IsQuasiSeparated B S' hS' (OverShriek.relocalizeToYoneda (h ≫ g) F)) :
    Space.IsQuasiSeparated B S hS (OverShriek.relocalizeToYoneda h F) := by
  refine Space.isQuasiSeparated_of_relocalizeMap B S S' hS hS' g _ ?_
  have h1 : Space.IsQuasiSeparated B S' hS'
      (OverShriek.relocalizeToYoneda (h ≫ g) F ≫
        (OverShriek.relocalizeYonedaComp h g).hom) :=
    (MorphismProperty.cancel_right_of_respectsIso
      (@Space.IsQuasiSeparated B S' hS') _ _).2 hF
  rw [OverShriek.relocalizeToYoneda_comp_relocalizeYonedaComp h g F] at h1
  exact (MorphismProperty.cancel_left_of_respectsIso
    (@Space.IsQuasiSeparated B S' hS') _ _).1 h1

/-- **Stacks 03HE for the image of Stacks 04SG's forward functor does not depend on the base.**
An algebraic space over `W`, viewed over `S` along `h` and over `S'` along a factorization
`h ≫ g`, has quasi-compact structural morphism over `S` as soon as it has one over `S'`. -/
theorem Space.isQuasiCompact_spacesOverSmallerBaseFunctor_of
    (u : B.obj hW ⟶ B.obj hS') (hu : h ≫ g = u)
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B W hW F)
    (hqc : Space.IsQuasiCompact B S' hS'
      (((spacesOverSmallerBaseFunctor B W S' hW hS' u).obj ⟨F, hF⟩).1.hom)) :
    Space.IsQuasiCompact B S hS
      (((spacesOverSmallerBaseFunctor B W S hW hS h).obj ⟨F, hF⟩).1.hom) := by
  subst hu
  refine (MorphismProperty.cancel_left_of_respectsIso
    (Space.quasiCompactPresheafProperty B S hS)
    ((spacesOverSmallerBaseFunctorForgetIso B W S hW hS h).inv.app ⟨F, hF⟩) _).1 ?_
  rw [Space.relocalizeToYoneda_eq B W S hW hS h ⟨F, hF⟩]
  refine Space.isQuasiCompact_relocalizeToYoneda_comp_of B W S hW hS h S' hS' g F ?_
  rw [← Space.relocalizeToYoneda_eq B W S' hW hS' (h ≫ g) ⟨F, hF⟩]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (Space.quasiCompactPresheafProperty B S' hS')
    ((spacesOverSmallerBaseFunctorForgetIso B W S' hW hS' (h ≫ g)).inv.app ⟨F, hF⟩) _).2 hqc

/-- **Stacks 03HL part (3) for the image of Stacks 04SG's forward functor does not depend on the
base.** -/
theorem Space.isQuasiSeparated_spacesOverSmallerBaseFunctor_of
    (u : B.obj hW ⟶ B.obj hS') (hu : h ≫ g = u)
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B W hW F)
    (hqs : Space.IsQuasiSeparated B S' hS'
      (((spacesOverSmallerBaseFunctor B W S' hW hS' u).obj ⟨F, hF⟩).1.hom)) :
    Space.IsQuasiSeparated B S hS
      (((spacesOverSmallerBaseFunctor B W S hW hS h).obj ⟨F, hF⟩).1.hom) := by
  subst hu
  refine (MorphismProperty.cancel_left_of_respectsIso
    (@Space.IsQuasiSeparated B S hS)
    ((spacesOverSmallerBaseFunctorForgetIso B W S hW hS h).inv.app ⟨F, hF⟩) _).1 ?_
  rw [Space.relocalizeToYoneda_eq B W S hW hS h ⟨F, hF⟩]
  refine Space.isQuasiSeparated_relocalizeToYoneda_comp_of B W S hW hS h S' hS' g F ?_
  rw [← Space.relocalizeToYoneda_eq B W S' hW hS' (h ≫ g) ⟨F, hF⟩]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (@Space.IsQuasiSeparated B S' hS')
    ((spacesOverSmallerBaseFunctorForgetIso B W S' hW hS' (h ≫ g)).inv.app ⟨F, hF⟩) _).2 hqs

end ChangeOfBase

end AlgebraicGeometry

end
