module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupRelativelyAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowNoetherianRelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveSpaceImmersionRelativeAmple

/-!
# Stacks Remark 088T: the morphism `Z' ⟶ Y` of Chow's lemma carries a relatively ample sheaf

In Lemmas 088R and 088S (Chow's lemma for algebraic spaces) the morphism `g : Z' ⟶ Y` is a
`U`-admissible blowup `b : Z' ⟶ Z` followed by a closed immersion `Z ⟶ ℙⁿ_Y` and the projection
`ℙⁿ_Y ⟶ Y`, over a quasi-compact base `Y`. Remark 088T says that `g` is a composition of
projective morphisms and that, by the analogue for algebraic spaces of Morphisms, Lemma 0C4K,
there exists a `g`-ample invertible sheaf on `Z'`.

## Main results

All names are in the namespace `AlgebraicGeometry.Space`.

* `exists_isRelativelyAmple_of_isAdmissibleBlowup_of_projectiveSpaceImmersion`: both factors of
  `g` are proper, representable and carry a relatively ample invertible module, and `Z'` carries a
  `g`-ample invertible module.

## The statement

The source has no definition of a projective morphism of algebraic spaces (Section 088P says so),
so "a composition of projective morphisms" is read as: each of the two factors `Z' ⟶ Z` and
`Z ⟶ Y` is proper and representable and carries an invertible module ample relative to it
(Stacks 0D31). For `Z ⟶ Y` that module is the twist `i^* 𝒪_{ℙⁿ_Y}(1)`, for the blowup
`Z' ⟶ Z` it is the ideal sheaf `𝓘_E` of the exceptional divisor. The `g`-ample invertible module
is `𝓘_E ⊗ b^*(i^* 𝒪(1))^{⊗ a}` for `a` large, by the analogue of Stacks 0C4K,
`AlgebraicGeometry.Space.exists_threshold_isRelativelyAmple_comp`.

Of the conditions of Lemmas 088R and 088S on the diagram, the statement keeps those the remark is
about: `Y` quasi-compact, the closed immersion `Z ⟶ ℙⁿ_Y` and the `U`-admissible blowup
`Z' ⟶ Z`. Quasi-separatedness of `Y`, properness of `g` and the remaining arrows of the diagram
are not needed. Representability of the blowup, and hence of `g`, is part of the conclusion.

## References

* [Stacks Project, Tag 088T](https://stacks.math.columbia.edu/tag/088T)
* [Stacks Project, Tag 088R](https://stacks.math.columbia.edu/tag/088R)
* [Stacks Project, Tag 088S](https://stacks.math.columbia.edu/tag/088S)
* [Stacks Project, Tag 0C4K](https://stacks.math.columbia.edu/tag/0C4K)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 088T.** Let `Y` be a quasi-compact algebraic space, `i : Z ⟶ ℙⁿ_Y` a closed
immersion, `U ⊆ Z` an open subspace and `b : Z' ⟶ Z` a `U`-admissible blowup, as in Lemmas 088R
and 088S, and let `g = b ≫ (Z ⟶ ℙⁿ_Y ⟶ Y)`. Then

1. `g` is a composition of projective morphisms: `b` is proper and representable and carries a
   `b`-ample invertible module, and `Z ⟶ Y` is proper and representable and carries an ample
   invertible module relative to it;
2. there exists a `g`-ample invertible `𝒪_{Z'}`-module. -/
@[stacks 088T]
theorem exists_isRelativelyAmple_of_isAdmissibleBlowup_of_projectiveSpaceImmersion
    {Y Z Z' : AlgebraicSpaces B S hS} (hY : IsQuasiCompactSpace B S hS Y.1) {n : ℕ}
    {hP : B.Contains (projectiveSpaceOver n S)} (D : ProjectiveSpaceImmersion B S hS n hP Z Y)
    (U : OpenSubspaces B S hS Z.1) {b : Z' ⟶ Z} (hb : IsAdmissibleBlowup B S hS U b) :
    (IsProper B S hS b.hom ∧ yoneda.relativelyRepresentable b.hom ∧
        ∃ L : Modules.{u, u} B S hS Z'.1 Z'.2,
          Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Z'.1)
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS Z'.1 Z'.2).O)).property L ∧
          IsRelativelyAmple B S hS b L) ∧
      (IsProper B S hS D.hom.hom ∧ yoneda.relativelyRepresentable D.hom.hom ∧
        ∃ M : Modules.{u, u} B S hS Z.1 Z.2,
          Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Z.1)
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS Z.1 Z.2).O)).property M ∧
          IsRelativelyAmple B S hS D.hom M) ∧
      ∃ L : Modules.{u, u} B S hS Z'.1 Z'.2,
        Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Z'.1)
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Z'.1 Z'.2).O)).property L ∧
        IsRelativelyAmple B S hS (b ≫ D.hom) L := by
  have : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    BigFppfOver.hasSheafify_type B S hS
  obtain ⟨C, hfp, -, hbl⟩ := hb
  have hLinv : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Z'.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z'.1 Z'.2).O)).property
      (idealSheafOfModules B S hS Z' (preimageClosedSubspace b C)) :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hbl.isPullbackDefined
  have hL := isRelativelyAmple_idealSheafOfModules_of_isBlowupAlong hfp hbl
  have hM := D.isRelativelyAmple_twist
  obtain ⟨m, hm⟩ := exists_threshold_isRelativelyAmple_comp b D.hom hY _ hLinv D.twist
    D.isInvertible_twist hL hM
  refine ⟨⟨isProper_of_isBlowupAlong_of_isFinitePresentation B S hS C b hfp hbl, hL.1, _, hLinv,
    hL⟩, ⟨D.isProper_hom, D.relativelyRepresentable_hom, D.twist, D.isInvertible_twist, hM⟩, _,
    @isInvertible_modulesTensorObj B S hS _ _ _ hLinv (isInvertible_modulePullback B S hS b _
      (hL := @isInvertible_tensorPow B S hS _ D.twist D.isInvertible_twist m)), hm m le_rfl⟩

end AlgebraicGeometry.Space

end
