module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally

/-!
# Global cohomology of a module sheaf from abelian sheaf cohomology

Two descriptions of the cohomology of a sheaf of modules on a scheme `X` coexist in this
library. `Hgroup X.ringCatSheaf ⊤ n F` is the `n`-th right derived functor of global sections
computed in `Mod(𝒪_X)`, and `Sheaf.H G n` is Mathlib's `Ext`-theoretic cohomology of an
abelian sheaf `G`, namely `Ext^n` out of the constant sheaf `ℤ`. The vanishing theorems of
Stacks chapter 20 that are stated for abelian sheaves — notably Stacks 0A3G, cohomology
vanishes above the dimension of a spectral space — produce the second, while the local
cohomology results of chapter 51 consume the first.

This file is the bridge in positive degree. The identification has three steps. Global
sections of abelian sheaves are corepresented by the constant sheaf on `ℤ`, and sections over
the terminal open `⊤` are corepresented by the sheafification of the free abelian presheaf on
`yoneda.obj ⊤`; since `⊤` *is* terminal, the two corepresented functors agree, so the two
corepresenting objects are isomorphic. Vanishing of `Ext` out of one therefore gives vanishing
of `Ext` out of the other. Finally `Ext` out of a corepresenting object computes the right
derived functors of the corepresented functor, and Stacks 03FD moves that computation from
abelian sheaves to module sheaves.

## Main results

* `Stacks.LocalCohomology.isZero_Hgroup_of_subsingleton_sheafCohomology` — if the abelian
  sheaf cohomology of the underlying abelian sheaf of `F` vanishes in a positive degree, then
  so does `H^n(X, F)` computed in `Mod(𝒪_X)`.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 0A3G](https://stacks.math.columbia.edu/tag/0A3G)
* [Stacks Project, Tag 0DXC](https://stacks.math.columbia.edu/tag/0DXC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.LocalCohomology

/-- Over a scheme, the corepresenting object of sections over the terminal open `⊤` is
isomorphic to the corepresenting object of global sections, the constant sheaf on `ℤ`. -/
def sheafificationFreeYonedaTopIsoConstantSheafInt (X : Scheme.{u}) :
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (yoneda.obj (⊤ : X.Opens) ⋙ AddCommGrpCat.free) ≅
      (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  (preadditiveCoyoneda.preimageIso
    ((ModuleSheafCohomology.evaluationRepresentation
          (Opens.grothendieckTopology X) (⊤ : X.Opens)).symm ≪≫
      (Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}
        (isTerminalTop (α := X.Opens))).symm ≪≫
      ModuleSheafCohomology.globalSectionsRepresentation
        (Opens.grothendieckTopology X))).unop.symm

/-- **The abelian-to-module comparison for global cohomology in positive degree.** If the
`Ext`-theoretic sheaf cohomology of the underlying abelian sheaf of a module sheaf `F` on a
scheme `X` is trivial in degree `p > 0`, then the degree-`p` cohomology of `F` computed in
`Mod(𝒪_X)` is a zero object. -/
theorem isZero_Hgroup_of_subsingleton_sheafCohomology
    {X : Scheme.{u}}
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (F : X.Modules) (p : ℕ) (hp : 0 < p)
    (hF : Subsingleton
      (Sheaf.H ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) p)) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p F) := by
  cases p with
  | zero => omega
  | succ n =>
    let R := X.ringCatSheaf
    let J := Opens.grothendieckTopology X
    let A := (presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj (⊤ : X.Opens) ⋙ AddCommGrpCat.free)
    let Z := (constantSheaf J AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))
    have hConst : IsZero ((extFunctorObj Z (n + 1)).obj ((SheafOfModules.toSheaf R).obj F)) :=
      AddCommGrpCat.isZero_iff_subsingleton.mpr hF
    have hExt : IsZero ((extFunctorObj A (n + 1)).obj ((SheafOfModules.toSheaf R).obj F)) :=
      hConst.of_iso (((extFunctor (n + 1)).mapIso
        (sheafificationFreeYonedaTopIsoConstantSheafInt X).op).app
          ((SheafOfModules.toSheaf R).obj F)).symm
    exact hExt.of_iso
      ((ModuleSheafCohomology.sectionsComparisonIso J R (⊤ : X.Opens) (n + 1)).app F ≪≫
        (Functor.isoWhiskerLeft (SheafOfModules.toSheaf R)
          (ModuleSheafCohomology.rightDerivedIso
              (ModuleSheafCohomology.evaluationRepresentation J (⊤ : X.Opens)) (n + 1) ≪≫
            ModuleSheafCohomology.rightDerivedCoyonedaSuccIso A n)).app F)

end Stacks.LocalCohomology

end
