module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveGlobalSectionsPerfectShift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalVanishingFromCechVanishing
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Global sections on a small étale site as morphisms out of the constant sheaf `ℤ`

For a scheme `Y : Scheme.{u}` and any coefficient universe `w ≥ u + 1`, sections of abelian sheaves
on the small étale site of `Y` over the terminal object `Y` are corepresented by the constant
sheaf `ℤ`: `Γ(Y, F) ≅ Hom(ℤ_Y, F)`, naturally in `F`. Consequently the complex of global sections
of a complex of sheaves is the complex of morphisms out of `ℤ_Y`.

## Main definitions

* `Stacks.EtaleSections.zSheaf`: the constant sheaf `ℤ` at the coefficient universe `w`.
* `Stacks.EtaleSections.sections`: sections over the terminal object `Y`.
* `Stacks.EtaleSections.sectionsIso`: `Γ(Y, -) ≅ Hom(ℤ_Y, -)` on abelian sheaves.
* `Stacks.EtaleSections.sectionsComplexIso`: the complex of sections of a complex of abelian
  sheaves is its complex of morphisms out of `ℤ_Y`.

## References

* [Stacks Project, Tag 03TV](https://stacks.math.columbia.edu/tag/03TV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe w u

namespace Stacks.EtaleSections

variable (Y : Scheme.{u})

/-- The constant abelian sheaf `ℤ` on the small étale site of `Y`, at the coefficient universe
`max (u + 1) w`. -/
abbrev zSheaf : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) w} :=
  (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) w}).obj
    (AddCommGrpCat.of (ULift.{max (u + 1) w} ℤ))

/-- Sections over the terminal object `Y` of the small étale site of `Y`. -/
abbrev sections : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) w} ⥤
    AddCommGrpCat.{max (u + 1) w} :=
  (sheafSections Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) w}).obj
    (op (Scheme.Etale.mk (𝟙 Y)))

/-- **Sections over `Y` are corepresented by the constant sheaf `ℤ`**, through the adjunction
between constant sheaves and sections over the terminal object. -/
def sectionsIso :
    sections.{w} Y ≅ preadditiveCoyoneda.obj (op (zSheaf.{w} Y)) :=
  (NatIso.ofComponents (fun F =>
    (((constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) w}
        (Stacks.EtaleCohomology.etaleMkIdIsTerminal Y)).homAddEquiv
        (AddCommGrpCat.of (ULift.{max (u + 1) w} ℤ)) F).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)).toAddCommGrpIso) (by
    intro F G φ
    ext x
    change ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) w}).obj
      (AddCommGrpCat.of (ULift.{max (u + 1) w} ℤ)) ⟶ F) at x
    change ((constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) w}
        (Stacks.EtaleCohomology.etaleMkIdIsTerminal Y)).homEquiv _ G (x ≫ φ))
        (ULift.up (1 : ℤ)) =
      φ.hom.app (op (Scheme.Etale.mk (𝟙 Y)))
        (((constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) w}
          (Stacks.EtaleCohomology.etaleMkIdIsTerminal Y)).homEquiv _ F x) (ULift.up (1 : ℤ)))
    rw [Adjunction.homEquiv_naturality_right]
    rfl)).symm

/-- The complex of sections over `Y` of a complex of abelian sheaves is the complex of morphisms
out of the constant sheaf `ℤ`. -/
def sectionsComplexIso (T : CochainComplex (Sheaf Y.smallEtaleTopology
    AddCommGrpCat.{max (u + 1) w}) ℤ) :
    ((sections.{w} Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj T ≅
      StacksDraft.DimensionShift.homComplex (zSheaf.{w} Y) T :=
  (NatIso.mapHomologicalComplex (sectionsIso.{w} Y) (ComplexShape.up ℤ)).app T

end Stacks.EtaleSections

end
