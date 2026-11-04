module

public import StacksFrontier.Algebra.Homology.DerivedCategory.LerayPullbackComparison
public import StacksFrontier.Algebra.Homology.RightDerivedEdgeIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcCohomologicalDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiCohomologyComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology across the comparison morphism of the locally quasi-compact site

Let `X` be an object of `LC_qc` and let `a_X : Sh(LC_qc/X) → Sh(X)` be the comparison morphism
of topoi of Section 21.31, the composite of the change-of-topology morphism
`ε_X : Sh(LC_qc/X) → Sh(LC_Zar/X)` with the Zariski comparison `π_X : Sh(LC_Zar/X) → Sh(X)`.
For an abelian sheaf `F` on the space `X`, the cohomology of the localized quasi-compact site
with coefficients in `a_X^{-1}F` agrees with the cohomology of the space:

`H^n(X, F) = H^n_{qc}(X, a_X^{-1}F)`,

naturally in `F`. This is `qcCohomologyComparisonIso`, the abelian-sheaf assertion of
Stacks 09X4.

Cohomology is read here as the right derived functors of global sections — sections over the
terminal object `opensToSlice ⊤` of the two localized sites, and sections over `⊤ ⊆ X` on the
space — rather than as `Ext` out of the constant sheaf.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.spaceGlobalSections`,
  `zariskiGlobalSections`, `qcGlobalSections`: the three global-sections functors.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.zariskiGlobalSectionsRightDerivedIso`:
  `H^n_{Zar}(X, G) ≅ H^n(X, π_{X,*}G)`.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.qcSectionsEdge`: the edge morphism
  `H^n_{Zar}(X, ε_{X,*}M) ⟶ H^n_{qc}(X, M)`.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.zariskiToQcCohomologyMap`: the comparison
  `H^n_{Zar}(X, G) ⟶ H^n_{qc}(X, ε_X^{-1}G)`.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.constantSheafCompQcInverseImageIso` and
  `constantSheafCompQcTopologicalInverseImageIso`: `ε_X^{-1}` and `a_X^{-1}` carry the constant
  abelian sheaf to the constant abelian sheaf.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.spaceHypercohomology` and
  `qcHypercohomology`: hypercohomology `H^n(X, K)` and `H^n_{qc}(X, M)` of bounded below
  complexes, and `qcDerivedGlobalSectionsPullback`, the map `RΓ(X, K) ⟶ RΓ_{qc}(X, a_X^{-1}K)`.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.spaceRightDerivedIsoComp`: clause (1) of
  Stacks 0DCU in the right-derived model.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.qcCohomologyComparisonIso`:
  **Stacks 09X4 for abelian sheaves.**
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.constantSheafQcCohomologyComparisonIso`:
  **Stacks 09X4 for a constant abelian sheaf.**
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.qcHypercohomologyComparisonIso`:
  **Stacks 09X4 for bounded below complexes.**

## Implementation notes

The source deduces 09X4 from Stacks 0D91 — the derived unit `K ⟶ Ra_{X,*}a_X^{-1}K` is an
isomorphism on `D^+(X)` — through Remark 21.14.4 (Stacks 08J6). For a single abelian sheaf the
same argument is available without any derived category, and that is how it is run here: the
two identifications of global sections

* `π_{X,*}` followed by sections over `⊤ ⊆ X` is sections over `opensToSlice ⊤`
  (`comparisonDirectImage_comp_spaceGlobalSections`),
* `ε_{X,*}` followed by sections over `opensToSlice ⊤` on the Zariski site is sections over the
  same object on the quasi-compact site
  (`qcAbelianDirectImage_comp_zariskiGlobalSections`),

hold on the nose, neither direct image changing the underlying presheaf of a sheaf except by
remembering a weaker sheaf condition. So the two comparisons of cohomology are the two
degeneration statements for the composites `Γ(X, -) ∘ π_{X,*}` and `Γ_{Zar}(X, -) ∘ ε_{X,*}`:

* for `π_{X,*}`, which is exact and preserves injectives, the degeneration is unconditional and
  is `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`, Stacks 015Z. Together
  with invertibility of the unit of `π_X^{-1} ⊣ π_{X,*}` (Stacks 0DCU, the unit clause) this
  gives `H^n(X, F) = H^n_{Zar}(X, π_X^{-1}F)`, clause (1) of Stacks 0DCU in the right-derived
  model, as `spaceRightDerivedIsoComp`.
* for `ε_{X,*}`, which is left exact and preserves injectives but is *not* exact, the
  degeneration is the invertibility of the edge morphism
  `Stacks.Cohomology.RightDerivedEdgeIso.isIso_edge_app`, which needs
  `R^q ε_{X,*}(a_X^{-1}F) = 0` for `1 ≤ q ≤ n`. That vanishing is the second half of clause (1)
  of Stacks 0DCY.

The vanishing `R^q ε_{X,*}(a_X^{-1}F) = 0` for `q > 0`, the second half of clause (1) of
Stacks 0DCY, is `isZero_rightDerived_qcAbelianDirectImage_qcAbelianInverseImage`: the vanishing
conditions `(V_n)` of `comparisonSituation`, the instance of Situation 0EZ3 for `LC_qc` and
`LC_Zar`, which hold in every degree by Stacks 0EZF. Condition (0EZ6) of Situation 0EZ3, the other
input of clause (1) of Stacks 0DCY, is `zariskiPullbackClass_isSheaf_qc`.

The assertion for an object `K` of `D⁺(X)` is `qcHypercohomologyComparisonIso`, deduced as in
the source from Stacks 0D91 (`isIso_qcTopologicalDerivedUnit_app`) through the Leray
factorization of Remark 21.14.4 (Stacks 08J6).

## References

* [Stacks Project, Tag 09X4](https://stacks.math.columbia.edu/tag/09X4)
* [Stacks Project, Tag 0D91](https://stacks.math.columbia.edu/tag/0D91)
* [Stacks Project, Tag 0DCY](https://stacks.math.columbia.edu/tag/0DCY)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.CompositeRightDerived

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)

/-! ### The three global-sections functors -/

/-- Global sections of an abelian sheaf on the space underlying `X`: sections over `⊤ ⊆ X`. -/
abbrev spaceGlobalSections :
    Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v} ⥤
      AddCommGrpCat.{max (u + 1) v} :=
  (sheafSections (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}).obj (op ⊤)

/-- Global sections on the localized Zariski site: sections over the terminal object
`opensToSlice ⊤`. -/
abbrev zariskiGlobalSections :
    Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v} ⥤
      AddCommGrpCat.{max (u + 1) v} :=
  (sheafSections (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}).obj
    (op ((S.opensToSlice X).1.obj ⊤))

/-- Global sections on the localized quasi-compact site: sections over the same terminal object
`opensToSlice ⊤` of the slice category, which the two topologies share. -/
abbrev qcGlobalSections :
    Sheaf (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{max (u + 1) v} ⥤
      AddCommGrpCat.{max (u + 1) v} :=
  (sheafSections (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{max (u + 1) v}).obj
    (op ((S.opensToSlice X).1.obj ⊤))

/-- Global sections on the space are additive. -/
instance spaceGlobalSections_additive : (spaceGlobalSections.{u, w, v} S X).Additive := by
  change (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj _).Additive
  infer_instance

/-- Global sections on the localized Zariski site are additive. -/
instance zariskiGlobalSections_additive : (zariskiGlobalSections.{u, w, v} S X).Additive := by
  change (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj _).Additive
  infer_instance

/-- Global sections on the localized quasi-compact site are additive. -/
instance qcGlobalSections_additive : (qcGlobalSections.{u, w, v} S X).Additive := by
  change (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj _).Additive
  infer_instance

/-- Sections of `π_{X,*}G` over `⊤ ⊆ X` are sections of `G` over the terminal object
`opensToSlice ⊤` of the localized Zariski site, the two functors being equal, not merely
isomorphic. -/
theorem comparisonDirectImage_comp_spaceGlobalSections :
    S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v} ⋙ spaceGlobalSections.{u, w, v} S X =
      zariskiGlobalSections.{u, w, v} S X :=
  rfl

/-- Sections of `ε_{X,*}M` over `opensToSlice ⊤`, computed on the localized Zariski site, are
sections of `M` over the same object of the slice category computed on the localized quasi-compact
site. -/
theorem qcAbelianDirectImage_comp_zariskiGlobalSections :
    qcAbelianDirectImage.{u, w, v} S X ⋙ zariskiGlobalSections.{u, w, v} S X =
      qcGlobalSections.{u, w, v} S X :=
  rfl

/-! ### Cohomology across the Zariski comparison morphism -/

section Zariski

attribute [local instance] enoughInjectives_sheafOpens_site enoughInjectives_zariskiSliceSheaf

/-- **Cohomology of the localized Zariski site, computed on the space through `π_{X,*}`.** For
an abelian sheaf `G` on the localized Zariski site,

`H^n_{Zar}(X, G) ≅ H^n(X, π_{X,*}G)`,

naturally in `G`. -/
def zariskiGlobalSectionsRightDerivedIso (n : ℕ) :
    (zariskiGlobalSections.{u, w, v} S X).rightDerived n ≅
      S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v} ⋙
        (spaceGlobalSections.{u, w, v} S X).rightDerived n :=
  haveI : (S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v} ⋙
      spaceGlobalSections.{u, w, v} S X).Additive :=
    Functor.instAdditiveComp _ _
  rightDerivedNatIso
      (eqToIso (comparisonDirectImage_comp_spaceGlobalSections.{u, w, v} S X).symm) n ≪≫
    compRightDerivedNatIso (S.comparisonDirectImage X AddCommGrpCat.{max (u + 1) v})
      (spaceGlobalSections.{u, w, v} S X) n

/-- **Clause (1) of Stacks 0DCU in the right-derived model.** For an abelian sheaf `F` on the
space underlying `X`,

`H^n(X, F) ≅ H^n_{Zar}(X, π_X^{-1}F)`,

naturally in `F`, with cohomology read as the right derived functors of global sections. -/
def spaceRightDerivedIsoComp (n : ℕ) :
    (spaceGlobalSections.{u, w, v} S X).rightDerived n ≅
      S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X ⋙
        (zariskiGlobalSections.{u, w, v} S X).rightDerived n :=
  have _ : IsIso (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X).unit :=
    abelianComparisonAdjunction_unit_isIso.{u, w, v} S X
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight
        (asIso (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X).unit) _ ≪≫
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (zariskiGlobalSectionsRightDerivedIso.{u, w, v} S X n).symm

end Zariski

/-! ### Cohomology across the change-of-topology morphism -/

section ChangeOfTopology

attribute [local instance] enoughInjectives_sheafOpens_site enoughInjectives_zariskiSliceSheaf
  enoughInjectives_qcSliceSheaf

/-- **The edge morphism of the pair `(ε_{X,*}, Γ_{Zar}(X, -))`.** For an abelian sheaf `M` on the
localized quasi-compact site it is the edge morphism `E_2^{n,0} ⟶ H^n` of the Grothendieck spectral
sequence of that pair, a map

`H^n_{Zar}(X, ε_{X,*}M) ⟶ H^n_{qc}(X, M)`,

natural in `M`. -/
def qcSectionsEdge (n : ℕ) :
    qcAbelianDirectImage.{u, w, v} S X ⋙ (zariskiGlobalSections.{u, w, v} S X).rightDerived n ⟶
      (qcGlobalSections.{u, w, v} S X).rightDerived n :=
  Stacks.Cohomology.RightDerivedEdge.edge (qcAbelianDirectImage.{u, w, v} S X)
      (zariskiGlobalSections.{u, w, v} S X) n ≫
    (rightDerivedNatIso
      (eqToIso (qcAbelianDirectImage_comp_zariskiGlobalSections.{u, w, v} S X)) n).hom

/-- **The comparison of cohomology across the change-of-topology morphism.** For an abelian
sheaf `G` on the localized Zariski site it is a map

`H^n_{Zar}(X, G) ⟶ H^n_{qc}(X, ε_X^{-1}G)`,

natural in `G`: the unit of `ε_X^{-1} ⊣ ε_{X,*}` followed by the edge morphism `qcSectionsEdge`
at `ε_X^{-1}G`. -/
def zariskiToQcCohomologyMap (n : ℕ) :
    (zariskiGlobalSections.{u, w, v} S X).rightDerived n ⟶
      qcAbelianInverseImage.{u, w, v} S X ⋙ (qcGlobalSections.{u, w, v} S X).rightDerived n :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (qcAbelianComparisonAdjunction.{u, w, v} S X).unit _ ≫
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (qcAbelianInverseImage.{u, w, v} S X)
          (qcSectionsEdge.{u, w, v} S X n)

/-- The comparison at an abelian sheaf `G` on the localized Zariski site is the unit of the
change-of-topology adjunction, read in cohomology, followed by the edge morphism at
`ε_X^{-1}G`. -/
theorem zariskiToQcCohomologyMap_app (n : ℕ)
    (G : Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}) :
    (zariskiToQcCohomologyMap.{u, w, v} S X n).app G =
      ((zariskiGlobalSections.{u, w, v} S X).rightDerived n).map
          ((qcAbelianComparisonAdjunction.{u, w, v} S X).unit.app G) ≫
        (qcSectionsEdge.{u, w, v} S X n).app
          ((qcAbelianInverseImage.{u, w, v} S X).obj G) := by
  dsimp only [zariskiToQcCohomologyMap]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.leftUnitor_inv_app, Category.id_comp]

/-- **The comparison is an isomorphism at a sheaf pulled back from the space**, that is, at
`π_X^{-1}F` for an abelian sheaf `F` on the space underlying `X`. -/
theorem isIso_zariskiToQcCohomologyMap_app (n : ℕ)
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}) :
    IsIso ((zariskiToQcCohomologyMap.{u, w, v} S X n).app
      ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj F)) := by
  have hunit : IsIso ((qcAbelianComparisonAdjunction.{u, w, v} S X).unit.app
      ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj F)) :=
    isIso_qcAbelianComparisonAdjunction_unit_app.{u, w, v} S X _
      (zariskiPullbackClass_isSheaf_qc.{u, w, v} S X _
        (zariskiPullbackClass_abelianComparisonInverseImage.{u, w, v} S X F))
  have hedge : IsIso ((Stacks.Cohomology.RightDerivedEdge.edge
      (qcAbelianDirectImage.{u, w, v} S X) (zariskiGlobalSections.{u, w, v} S X) n).app
        ((qcAbelianInverseImage.{u, w, v} S X).obj
          ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj F))) :=
    Stacks.Cohomology.RightDerivedEdgeIso.isIso_edge_app _ _ _ n fun q hq _ =>
      isZero_rightDerived_qcAbelianDirectImage_qcAbelianInverseImage.{u, w, v} S X _
        (zariskiPullbackClass_abelianComparisonInverseImage.{u, w, v} S X F) q hq
  have hsec : IsIso ((qcSectionsEdge.{u, w, v} S X n).app
      ((qcAbelianInverseImage.{u, w, v} S X).obj
        ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj F))) := by
    dsimp only [qcSectionsEdge]
    rw [NatTrans.comp_app]
    infer_instance
  rw [zariskiToQcCohomologyMap_app]
  infer_instance

/-- **Stacks 09X4 for abelian sheaves.** For an object `X` of `LC_qc` and an abelian sheaf `F`
on the space underlying `X`, the cohomology of the localized quasi-compact site with
coefficients in `a_X^{-1}F` is the cohomology of the space with coefficients in `F`:

`H^n_{qc}(X, a_X^{-1}F) ≅ H^n(X, F)`,

naturally in `F`. -/
@[stacks 09X4 "part (1): H^n(X, F) = H^n_qc(X, a_X^{-1}F) for an abelian sheaf F on X, naturally
in F, with cohomology read as the right derived functors of global sections"]
def qcCohomologyComparisonIso (n : ℕ) :
    qcTopologicalAbelianInverseImage.{u, w, v} S X ⋙
        (qcGlobalSections.{u, w, v} S X).rightDerived n ≅
      (spaceGlobalSections.{u, w, v} S X).rightDerived n :=
  have _ : ∀ F, IsIso ((Functor.whiskerLeft
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X)
      (zariskiToQcCohomologyMap.{u, w, v} S X n)).app F) := fun F =>
    isIso_zariskiToQcCohomologyMap_app.{u, w, v} S X n F
  have _ : IsIso (Functor.whiskerLeft
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X)
      (zariskiToQcCohomologyMap.{u, w, v} S X n)) := NatIso.isIso_of_isIso_app _
  (spaceRightDerivedIsoComp.{u, w, v} S X n ≪≫
    asIso (Functor.whiskerLeft (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X)
      (zariskiToQcCohomologyMap.{u, w, v} S X n)) ≪≫
    (Functor.associator _ _ _).symm).symm

/-! ### The constant-sheaf example -/

/-- The change-of-topology inverse image carries the constant abelian sheaf on the localized
Zariski site to the constant abelian sheaf on the localized quasi-compact site, naturally in the
abelian group of values. -/
def constantSheafCompQcInverseImageIso :
    constantSheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v} ⋙
        qcAbelianInverseImage.{u, w, v} S X ≅
      constantSheaf (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{max (u + 1) v} :=
  Adjunction.leftAdjointUniq
    (show constantSheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v} ⋙
          qcAbelianInverseImage.{u, w, v} S X ⊣ qcGlobalSections.{u, w, v} S X from
      (constantSheafAdj (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}
          (opensToSlice_top_isTerminal S X)).comp
        (qcAbelianComparisonAdjunction.{u, w, v} S X))
    (constantSheafAdj (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{max (u + 1) v}
      (opensToSlice_top_isTerminal S X))

/-- **`a_X^{-1}` carries the constant abelian sheaf to the constant abelian sheaf.** The
inverse image along `a_X = π_X ∘ ε_X` of the constant sheaf on an abelian group `A` on the space
`X` is the constant sheaf on `A` of the localized quasi-compact site, naturally in `A`. -/
def constantSheafCompQcTopologicalInverseImageIso :
    constantSheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v} ⋙
        qcTopologicalAbelianInverseImage.{u, w, v} S X ≅
      constantSheaf (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{max (u + 1) v} :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (constantSheafCompComparisonInverseImageIso.{u, w, v} S X) _ ≪≫
      constantSheafCompQcInverseImageIso.{u, w, v} S X

/-- **Stacks 09X4, the constant-sheaf example.** For an abelian group `A`, the cohomology of the
space `X` with coefficients in the constant sheaf on `A` is the cohomology of the localized
quasi-compact site with coefficients in its constant sheaf on `A`:

`H^n(X, A) ≅ H^n_{qc}(X, A)`,

naturally in `A`. -/
@[stacks 09X4 "the example: H^n(X, A) = H^n_qc(X, A) for an abelian group A, naturally in A"]
def constantSheafQcCohomologyComparisonIso (n : ℕ) :
    constantSheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v} ⋙
        (spaceGlobalSections.{u, w, v} S X).rightDerived n ≅
      constantSheaf (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{max (u + 1) v} ⋙
        (qcGlobalSections.{u, w, v} S X).rightDerived n :=
  (Functor.isoWhiskerLeft _ (qcCohomologyComparisonIso.{u, w, v} S X n)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (constantSheafCompQcTopologicalInverseImageIso.{u, w, v} S X) _

end ChangeOfTopology

/-! ### Hypercohomology of a bounded below complex -/

section Hypercohomology

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

attribute [local instance] enoughInjectives_sheafOpens_site enoughInjectives_zariskiSliceSheaf
  enoughInjectives_qcSliceSheaf

/-- **Degree-`n` hypercohomology of the space**, `K ↦ H^n(X, K)` on the bounded below derived
category of abelian sheaves on the space underlying `X`: the degree-`n` cohomology of the right
derived functor of global sections. -/
abbrev spaceHypercohomology (n : ℤ) :
    DerivedCategory.Plus (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}) ⥤
      AddCommGrpCat.{max (u + 1) v} :=
  (spaceGlobalSections.{u, w, v} S X).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor _ n

/-- **Degree-`n` hypercohomology of the localized quasi-compact site**, `M ↦ H^n_{qc}(X, M)` on
the bounded below derived category of abelian sheaves on `LC_qc/X`: the degree-`n` cohomology of
the right derived functor of sections over the terminal object `opensToSlice ⊤`. -/
abbrev qcHypercohomology (n : ℤ) :
    DerivedCategory.Plus
        (Sheaf (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{max (u + 1) v}) ⥤
      AddCommGrpCat.{max (u + 1) v} :=
  (qcGlobalSections.{u, w, v} S X).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor _ n

/-- Global sections of `a_{X,*}M` on the space are global sections of `M` on the localized
quasi-compact site. -/
theorem qcTopologicalAbelianDirectImage_comp_spaceGlobalSections :
    qcTopologicalAbelianDirectImage.{u, w, v} S X ⋙ spaceGlobalSections.{u, w, v} S X =
      qcGlobalSections.{u, w, v} S X :=
  rfl

/-- **Derived global sections across `a_X`.** The pullback on derived sections
`RΓ(X, -) ⟶ ā_X^{-1} ⋙ RΓ_{qc}(X, -)` for the adjunction `a_X^{-1} ⊣ a_{X,*}`. -/
def qcDerivedGlobalSectionsPullback :
    (spaceGlobalSections.{u, w, v} S X).rightDerivedFunctorPlus ⟶
      (qcTopologicalAbelianInverseImage.{u, w, v} S X).mapDerivedCategoryPlus ⋙
        (qcGlobalSections.{u, w, v} S X).rightDerivedFunctorPlus :=
  Stacks.LerayPullbackComparison.lerayPullback
    (qcTopologicalAbelianComparisonAdjunction.{u, w, v} S X)
    (spaceGlobalSections.{u, w, v} S X) (qcGlobalSections.{u, w, v} S X)
    (eqToIso (qcTopologicalAbelianDirectImage_comp_spaceGlobalSections.{u, w, v} S X))

/-- The derived pullback `RΓ(X, K) ⟶ RΓ_{qc}(X, a_X^{-1}K)` is an isomorphism at every `K` at
which the derived unit `K ⟶ Ra_{X,*}a_X^{-1}K` of `a_X^{-1} ⊣ a_{X,*}` is one. -/
theorem isIso_qcDerivedGlobalSectionsPullback_app
    (K : DerivedCategory.Plus
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}))
    [IsIso ((qcTopologicalDerivedUnit.{u, w, v} S X).app K)] :
    IsIso ((qcDerivedGlobalSectionsPullback.{u, w, v} S X).app K) :=
  have : IsIso ((Stacks.LerayPullbackComparison.derivedUnit
      (qcTopologicalAbelianComparisonAdjunction.{u, w, v} S X)).app K) :=
    inferInstanceAs (IsIso ((qcTopologicalDerivedUnit.{u, w, v} S X).app K))
  Stacks.LerayPullbackComparison.isIso_lerayPullback_app _ _ _ _ K

/-- **Stacks 09X4 for bounded below complexes.** For an object `X` of `LC_qc` and `K` in
`D⁺(X)`, the hypercohomology of the space with coefficients in `K` is the hypercohomology of the
localized quasi-compact site with coefficients in `a_X^{-1}K`:

`H^n(X, K) ≅ H^n_{qc}(X, a_X^{-1}K)`,

naturally in `K`. -/
@[stacks 09X4 "part (2): H^n(X, K) = H^n_qc(X, a_X^{-1}K) for K in D^+(X), naturally in K, with
hypercohomology read as the cohomology of the right derived functor of global sections on D^+"]
def qcHypercohomologyComparisonIso (n : ℤ) :
    spaceHypercohomology.{u, w, v} S X n ≅
      (qcTopologicalAbelianInverseImage.{u, w, v} S X).mapDerivedCategoryPlus ⋙
        qcHypercohomology.{u, w, v} S X n :=
  have : ∀ K, IsIso ((qcDerivedGlobalSectionsPullback.{u, w, v} S X).app K) := fun K =>
    have := isIso_qcTopologicalDerivedUnit_app.{u, w, v} S X K
    isIso_qcDerivedGlobalSectionsPullback_app.{u, w, v} S X K
  have : IsIso (qcDerivedGlobalSectionsPullback.{u, w, v} S X) := NatIso.isIso_of_isIso_app _
  Functor.isoWhiskerRight (asIso (qcDerivedGlobalSectionsPullback.{u, w, v} S X))
    (DerivedCategory.Plus.homologyFunctor _ n)

end Hypercohomology

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
