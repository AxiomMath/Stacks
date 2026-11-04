module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectEssSurjCanonicalPullbackData
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackDataCompIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackCompositionAgree

/-!
# The two pullback-pseudofunctor data of derived pullback have the same comparisons

`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData` and
`AlgebraicGeometry.Space.canonicalPullbackData` are two `CategoryTheory.PullbackData` with the
same inverse images `Lf^*`: the first takes as composition comparison the universal comparison
of the total left derived functor along a composite, the second the composition isomorphism of
Stacks 0D6D.  This file proves that the two comparisons agree, hence that the hom-level maps of
Stacks 09RI — conjugation by the comparison of a presented factorisation — are the same maps for
the two data, and that the colimit statement
`CategoryTheory.PullbackData.LimitSystem.IsColim` for one is the colimit statement for the other.

## Main results

* `AlgebraicGeometry.Space.canonicalPullbackData_compIso_eq_smallEtale`: **the two
  composition comparisons agree.**
* `AlgebraicGeometry.Space.canonicalPullbackData_triangle_eq_smallEtale` and
  `canonicalPullbackData_factorHom_eq_smallEtale`: hence so do the comparisons of a presented
  factorisation and the maps they induce on homomorphism groups.
* `AlgebraicGeometry.Space.isColim_canonicalPullbackData_iff`: **the colimit statement of
  Stacks 09RI is the same for the two data.**

## How the identification is obtained

The identification is the comparison discussed in the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectEssSurjCanonicalPullbackData.lean`
(whether the universal comparison of the total left derived functor along a composite agrees,
across the 2-isomorphism of Stacks 03G8, with the composition comparison of Stacks 0D6D) and in
the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ExtensionByZeroBaseChangeIsoLimitSystem.lean`
(the two comparisons are not definitionally equal).  It has two
halves, both proved:
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData_compIso_eq` identifies the universal
comparison with `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso`, and
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso_eq_canonical_iso` identifies the
latter with the comparison of
`AlgebraicGeometry.Space.DerivedPullbackComposition.canonical`, which is the composition
comparison of `AlgebraicGeometry.Space.canonicalPullbackData` by definition.  This file puts
the two together.

Only the inverse images and the composition comparisons are identified below; the unit
comparisons are not, and nothing here needs them.  In particular
`CategoryTheory.PullbackData.LimitSystem.IsColim` mentions the datum only through
`CategoryTheory.PullbackData.factorHom`, so the statement transported below is the whole of the
conclusion of Stacks 09RI.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe w u

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS}

/-- **The composition comparison of
`AlgebraicGeometry.Space.canonicalPullbackData` is the composition comparison of
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`**: the composition isomorphism of
Stacks 0D6D is the universal comparison of the total left derived functor along the composite. -/
theorem canonicalPullbackData_compIso_eq_smallEtale (f : X ⟶ Y) (g : Y ⟶ Z) :
    (canonicalPullbackData B S hS).compIso f g =
      (smallEtaleDerivedPullbackData B S hS).compIso f g := by
  rw [smallEtaleDerivedPullbackData_compIso_eq,
    smallEtaleDerivedModulePullbackCompIso_eq_canonical_iso]
  rfl

/-- The comparison of a presented factorisation `f ≫ g = k` is the same for the two data. -/
theorem canonicalPullbackData_triangle_eq_smallEtale {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z}
    (h : f ≫ g = k) :
    (canonicalPullbackData B S hS).triangle h =
      (smallEtaleDerivedPullbackData B S hS).triangle h := by
  subst h
  rw [PullbackData.triangle_rfl, PullbackData.triangle_rfl,
    canonicalPullbackData_compIso_eq_smallEtale]

/-- The map on homomorphism groups attached to a presented factorisation `f ≫ g = k` — the
transition maps and the maps to the limit of Stacks 09RI — is the same for the two data. -/
theorem canonicalPullbackData_factorHom_eq_smallEtale {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z}
    (h : f ≫ g = k) {A C : derivedModules B S hS Z}
    (φ : ((canonicalPullbackData B S hS).pull g).obj A ⟶
      ((canonicalPullbackData B S hS).pull g).obj C) :
    (canonicalPullbackData B S hS).factorHom h φ =
      (smallEtaleDerivedPullbackData B S hS).factorHom h φ := by
  simp only [PullbackData.factorHom, canonicalPullbackData_triangle_eq_smallEtale]
  rfl

variable {B S hS}

/-- The transition maps of a system over a base are the same for the two data. -/
theorem trans_canonicalPullbackData_eq_smallEtale {b : AlgebraicSpaces B S hS} {J : Type w}
    [Preorder J]
    (Sys : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) b J)
    (A C : derivedModules B S hS b) :
    Sys.trans (canonicalPullbackData B S hS) A C =
      Sys.trans (smallEtaleDerivedPullbackData B S hS) A C := by
  funext i j h φ
  exact canonicalPullbackData_factorHom_eq_smallEtale B S hS (Sys.transition_toBase h) φ

/-- The maps to the vertex of a system over a base are the same for the two data. -/
theorem projHom_canonicalPullbackData_eq_smallEtale {b : AlgebraicSpaces B S hS} {J : Type w}
    [Preorder J]
    (Sys : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) b J)
    (A C : derivedModules B S hS b) :
    Sys.projHom (canonicalPullbackData B S hS) A C =
      Sys.projHom (smallEtaleDerivedPullbackData B S hS) A C := by
  funext j φ
  exact canonicalPullbackData_factorHom_eq_smallEtale B S hS (Sys.proj_toBase j) φ

/-- **The colimit statement of Stacks 09RI is the same statement for the two data.**  Its
transition maps and its maps to the vertex are conjugation by the comparison of a presented
factorisation, and those agree. -/
theorem isColim_canonicalPullbackData_iff {b : AlgebraicSpaces B S hS} {J : Type w} [Preorder J]
    (Sys : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) b J)
    (A C : derivedModules B S hS b) :
    Sys.IsColim (canonicalPullbackData B S hS) A C ↔
      Sys.IsColim (smallEtaleDerivedPullbackData B S hS) A C := by
  unfold PullbackData.LimitSystem.IsColim
  rw [trans_canonicalPullbackData_eq_smallEtale Sys A C,
    projHom_canonicalPullbackData_eq_smallEtale Sys A C]
  rfl

end AlgebraicGeometry.Space

end
