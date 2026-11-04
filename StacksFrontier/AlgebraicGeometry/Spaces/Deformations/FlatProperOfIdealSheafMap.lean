module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.FlatProperOfConormal
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FlatImageSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionRealizationConormal

/-!
# Flatness of a morphism of first-order thickenings from its map of defining ideals

The last step of the proof of [Stacks Project, Tag 0D3X] reads off that `X' ⟶ Y` is flat, proper
and of finite presentation from the conormal map of the morphism of first-order thickenings
`(X₀ ⊂ X') ⟶ (Y₀ ⊂ Y)` being an isomorphism, the map `X₀ ⟶ Y₀` being flat, proper and of finite
presentation (`Space.isFlat_isProper_isFinitePresentation_of_isIso_conormalMapOfImmersions`). In
that proof the closed subspaces and the morphism between them are only known up to
isomorphism. This file records the two forms in which the step is consumed:

* the three properties survive composition with isomorphisms on both sides;
* the conclusion holds as soon as the map `g^*𝓘_{Y₀} ⟶ 𝓘_{X₀}` of defining ideals, pulled back to
  the closed subspace and read on a space isomorphic to it, is an isomorphism.

## Main results

* `Space.isFlat_isProper_isFinitePresentation_iso_comp_comp_iso`.
* `Space.isFlat_isProper_isFinitePresentation_of_isIso_modulePullback_map_idealSheafMap`.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 06BH](https://stacks.math.columbia.edu/tag/06BH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Flatness, properness and finite presentation are invariant under composition with
isomorphisms on both sides**: `e ≫ t ≫ e'` has the three properties when `t` has them, as
isomorphisms have them (and they compose, Stacks 03MN, 04XY, 03XQ). -/
theorem isFlat_isProper_isFinitePresentation_iso_comp_comp_iso {A A' C C' : AlgebraicSpaces B S hS}
    (e : A ≅ A') (t : A' ⟶ C) (e' : C ≅ C')
    (ht : IsFlat B S hS t.hom ∧ IsProper B S hS t.hom ∧ IsFinitePresentation B S hS t.hom) :
    IsFlat B S hS (e.hom ≫ t ≫ e'.hom).hom ∧ IsProper B S hS (e.hom ≫ t ≫ e'.hom).hom ∧
      IsFinitePresentation B S hS (e.hom ≫ t ≫ e'.hom).hom := by
  have : IsIso e.hom.hom := Iso.isIso_hom ((ObjectProperty.ι _).mapIso e)
  have : IsIso e'.hom.hom := Iso.isIso_hom ((ObjectProperty.ι _).mapIso e')
  have hfp : IsFinitePresentation B S hS (t.hom ≫ e'.hom.hom) :=
    isFinitePresentation_comp_iso A'.2 C.2 C'.2 t.hom ((ObjectProperty.ι _).mapIso e') ht.2.2
  refine ⟨?_, ?_, ?_⟩
  · exact isFlat_comp B S hS A.2 A'.2 C'.2 e.hom.hom (t.hom ≫ e'.hom.hom)
      (isFlat_of_isIso e.hom.hom A'.2)
      (isFlat_comp B S hS A'.2 C.2 C'.2 t.hom e'.hom.hom ht.1 (isFlat_of_isIso e'.hom.hom C'.2))
  · exact isProper_comp' B S hS e.hom.hom (t.hom ≫ e'.hom.hom) A'.2 C'.2
      (isProper_of_isIso B S hS e.hom.hom)
      (isProper_comp' B S hS t.hom e'.hom.hom C.2 C'.2 ht.2.1 (isProper_of_isIso B S hS _))
  · exact isFinitePresentation_of_isPullback B S hS A.2 A'.2 C'.2 C'.2
      (IsPullback.of_horiz_isIso (fst := e.hom.hom) (snd := e.hom.hom ≫ t.hom ≫ e'.hom.hom)
        (f := t.hom ≫ e'.hom.hom) (g := 𝟙 _) ⟨by simp⟩) hfp

/-- **The last step of the proof of Stacks 0D3X, from the map of defining ideals.** Let
`(f, g) : (X ⊆ X') → (Y ⊆ Y')` be a morphism of first-order thickenings with `f` flat, proper and
of finite presentation. If the map `g^*𝓘_Y ⟶ 𝓘_X` of defining ideals, pulled back to `X` and read
on a space `A ≅ X`, is an isomorphism, then `g` is flat, proper and of finite presentation and
`X = Y ×_{Y'} X'`. -/
theorem isFlat_isProper_isFinitePresentation_of_isIso_modulePullback_map_idealSheafMap
    {X' Y' A : AlgebraicSpaces B S hS} (X : ClosedSubspaces B S hS X'.1)
    (Y : ClosedSubspaces B S hS Y'.1) (g : X' ⟶ Y')
    (f : (⟨X.1.toFunctor, X.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X' X ≫ g = f ≫ subspaceInclusion B S hS Y' Y)
    (hX : IsFirstOrderThickening B S hS X' X.1) (hY : IsFirstOrderThickening B S hS Y' Y.1)
    (hf : IsFlat B S hS f.hom ∧ IsProper B S hS f.hom ∧ IsFinitePresentation B S hS f.hom)
    (ρ : A ≅ (⟨X.1.toFunctor, X.2.1⟩ : AlgebraicSpaces B S hS))
    (h : IsIso ((modulePullback B S hS ρ.hom).map
      ((modulePullback B S hS (subspaceInclusion B S hS X' X)).map
        (idealSheafMap B S hS X Y g f hsq)))) :
    IsFlat B S hS g.hom ∧ IsProper B S hS g.hom ∧ IsFinitePresentation B S hS g.hom ∧
      IsPullback (subspaceInclusion B S hS X' X) f g (subspaceInclusion B S hS Y' Y) :=
  isFlat_isProper_isFinitePresentation_of_isIso_conormalMapOfImmersions B S hS X Y g f hsq hX hY
    hf.1 hf.2.1 hf.2.2
    (isIso_conormalMapOfImmersions_of_isIso_modulePullback_map_idealSheafMap B S hS X Y g f hsq
      ρ h)

end AlgebraicGeometry.Space

end
