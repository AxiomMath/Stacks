module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomFilteredColimit
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomFilteredColimitsSections
public import StacksFrontier.Topology.Sheaves.Limits.FilteredColimitGlobalSections
import StacksCore.Tactic.StacksAttribute

/-!
# Hom out of a finitely presented module and filtered colimits on a ringed space

Let `(X, O_X)` be a ringed space, let `F` be an `O_X`-module of finite presentation and let
`G = colim_λ G_λ` be a filtered colimit of `O_X`-modules.  Assume that `X` has a cofinal system of
open coverings `X = ⋃_{j ∈ J} U_j` with `J` finite and `U_j ∩ U_j'` quasi-compact for all
`j, j' ∈ J`.  Then

`colim_λ Hom_X(F, G_λ) = Hom_X(F, colim_λ G_λ)`,

the equality being that the canonical comparison map is a bijection.

The proof is the one of the source.  Write `H = Hom_O(F, colim G_λ)` and `H_λ = Hom_O(F, G_λ)` for
the *internal* Hom sheaves.  Global sections of `H` and of the `H_λ` compute `Hom_X(F, colim G_λ)`
and the `Hom_X(F, G_λ)`; one has `H = colim H_λ` by Stacks 0GMV; and global sections commute with
the filtered colimit by Stacks 009F (4), which is where the hypothesis on the coverings of `X`
enters.

## Main results

* `Stacks.SheafOfModules.preservesColimitsOfShape_sectionsFunctor`: global sections of sheaves of
  modules on such a ringed space commute with filtered colimits.
* `Stacks.SheafOfModules.preservesColimitsOfShape_coyoneda_of_isFinitePresentation`:
  **Stacks 01BS**, as preservation of filtered colimits by `Hom_X(F, -)`.
* `Stacks.SheafOfModules.isIso_colimitPost_coyoneda_of_hasFiniteCompactCofinalCovers`:
  **Stacks 01BS** as
  the source displays it, namely that the canonical map
  `colim_λ Hom_X(F, G_λ) ⟶ Hom_X(F, colim_λ G_λ)` is an isomorphism of types.

## Implementation notes

Hypothesis (3) of the source is
`DirectedColimitOfSheaves.HasFiniteCompactCofinalCovers (X := X) ⊤`, the predicate Stacks 009F is
stated with: every open covering of `X` is refined by a *finite* covering of `X` all of whose
*pairwise intersections are quasi-compact*.  It is neither weakened to quasi-compactness of `X`
nor strengthened to quasi-compactness of the members of the covering.

Hypothesis (1) of the source, that the index set is directed, is generalised to an arbitrary
filtered index category; a nonempty directed preorder is filtered by
`CategoryTheory.isFiltered_of_directed_le_nonempty`.  Hypothesis (2), finite presentation of the
module out of which one takes Hom, is `SheafOfModules.IsFinitePresentation`: local existence of a
presentation by finite free modules, which is what the source means by an `O_X`-module of finite
presentation.  All three hypotheses are used: (2) and (1) by Stacks 0GMV for the internal Hom
sheaves, (3) and (1) by Stacks 009F (4) for the global sections.

Everything is equi-universe, as in the ringed-space form of Stacks 0GMV and in the ringed-site
form of this statement (Stacks 0GN0): the space lives in `Type u`, the structure sheaf is
`CommRingCat.{u}`-valued and the index category has both objects and morphisms in `Type u`.  That
is the setting of the two inputs, and it is also what makes `Type u` have the colimits at issue.

A ringed space is read as a ringed site through `Stacks.SheafOfModules.opensRingedSite`, which is
how the two inputs are already phrased; `Stacks.SheafOfModules.Tensor.ringSheaf` and
`structureSheaf` are the same sheaf of rings.

## References

* [Stacks Project, Tag 01BS](https://stacks.math.columbia.edu/tag/01BS)
* [Stacks Project, Tag 0GMV](https://stacks.math.columbia.edu/tag/0GMV)
* [Stacks Project, Tag 009F](https://stacks.math.columbia.edu/tag/009F)
* [Stacks Project, Tag 0GN0](https://stacks.math.columbia.edu/tag/0GN0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

/-- **Global sections of sheaves of modules on a ringed space commute with filtered colimits**,
when the space has a cofinal system of finite open coverings with quasi-compact pairwise
intersections.

Stacks 009F (4) is about sheaves of *sets*, so the module statement is obtained by factoring the
sections functor as `SheafOfModules.toSheaf`, then the forgetful functor from abelian sheaves to
sheaves of sets, then global sections; the first two commute with filtered colimits on any ringed
site and the third does so by Stacks 009F (4). -/
theorem preservesColimitsOfShape_sectionsFunctor (K : Type u) [Category.{u} K] [IsFiltered K]
    (hX : DirectedColimitOfSheaves.HasFiniteCompactCofinalCovers (X := X) ⊤) :
    PreservesColimitsOfShape K (_root_.SheafOfModules.sectionsFunctor.{u} (structureSheaf Rc)) := by
  have hΓ : PreservesColimitsOfShape K (Sheaf.Γ (Opens.grothendieckTopology ↑X) (Type u)) :=
    DirectedColimitOfSheaves.preservesColimitsOfShape_globalSections K hX
  have h₁ : PreservesColimitsOfShape K
      (_root_.SheafOfModules.toSheaf.{u} (structureSheaf Rc)) :=
    InternalHom.toSheaf_preservesColimitsOfShape (opensRingedSite Rc) K
  have h₂ : PreservesColimitsOfShape K
      (sheafCompose (Opens.grothendieckTopology ↑X) (forget AddCommGrpCat.{u})) :=
    InternalHom.sheafCompose_forget_preservesColimitsOfShape (opensRingedSite Rc) K
  have hcomp : PreservesColimitsOfShape K
      ((_root_.SheafOfModules.toSheaf.{u} (structureSheaf Rc) ⋙
        sheafCompose (Opens.grothendieckTopology ↑X) (forget AddCommGrpCat.{u})) ⋙
          Sheaf.Γ (Opens.grothendieckTopology ↑X) (Type u)) := inferInstance
  exact preservesColimitsOfShape_of_natIso
    (Functor.isoWhiskerLeft
      (_root_.SheafOfModules.toSheaf.{u} (structureSheaf Rc) ⋙
        sheafCompose (Opens.grothendieckTopology ↑X) (forget AddCommGrpCat.{u}))
      (Sheaf.ΓNatIsoSectionsFunctor (Opens.grothendieckTopology ↑X)))

/-- **Stacks Project, Tag 01BS.**  Let `X` be a ringed space with a cofinal system of open
coverings `X = ⋃_{j ∈ J} U_j` with `J` finite and all `U_j ∩ U_j'` quasi-compact, let `F` be an
`O_X`-module of finite presentation and let `λ ↦ G_λ` be a filtered system of `O_X`-modules.  Then

`colim_λ Hom_X(F, G_λ) = Hom_X(F, colim_λ G_λ)`;

here in the form that `Hom_X(F, -)` preserves colimits of the given filtered shape, which says
exactly that the canonical comparison map out of any colimit of the `Hom_X(F, G_λ)` is an
isomorphism. -/
@[stacks 01BS]
theorem preservesColimitsOfShape_coyoneda_of_isFinitePresentation
    (F : _root_.SheafOfModules.{u} (structureSheaf Rc)) [F.IsFinitePresentation]
    (K : Type u) [Category.{u} K] [IsFiltered K]
    (hX : DirectedColimitOfSheaves.HasFiniteCompactCofinalCovers (X := X) ⊤) :
    PreservesColimitsOfShape K (coyoneda.obj (op F)) := by
  have h₁ : PreservesColimitsOfShape K
      (InternalHom.internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology ↑X) Rc F) :=
    preservesColimitsOfShape_ihomFunctor F
  have h₂ : PreservesColimitsOfShape K
      (_root_.SheafOfModules.sectionsFunctor.{u} (Tensor.ringSheaf Rc)) :=
    preservesColimitsOfShape_sectionsFunctor Rc K hX
  have hcomp : PreservesColimitsOfShape K
      (InternalHom.internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology ↑X) Rc F ⋙
        _root_.SheafOfModules.sectionsFunctor.{u} (Tensor.ringSheaf Rc)) :=
    comp_preservesColimitsOfShape _ _
  exact (preservesColimitsOfShape_iff_of_natIso
    (InternalHom.coyonedaIsoInternalHomSections Rc F).symm).mp hcomp

/-- **Stacks Project, Tag 01BS as the source displays it.**  The canonical comparison map

`colim_λ Hom_X(F, G_λ) ⟶ Hom_X(F, colim_λ G_λ)`

is an isomorphism of types, for `F` an `O_X`-module of finite presentation and `G` a filtered
system of `O_X`-modules on a ringed space with a cofinal system of finite open coverings having
quasi-compact pairwise intersections. -/
@[stacks 01BS]
theorem isIso_colimitPost_coyoneda_of_hasFiniteCompactCofinalCovers
    (F : _root_.SheafOfModules.{u} (structureSheaf Rc)) [F.IsFinitePresentation]
    {K : Type u} [Category.{u} K] [IsFiltered K]
    (G : K ⥤ _root_.SheafOfModules.{u} (structureSheaf Rc))
    (hX : DirectedColimitOfSheaves.HasFiniteCompactCofinalCovers (X := X) ⊤) :
    IsIso (colimit.post G (coyoneda.obj (op F))) :=
  have := preservesColimitsOfShape_coyoneda_of_isFinitePresentation Rc F K hX
  inferInstance

end Stacks.SheafOfModules

end
