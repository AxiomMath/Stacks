module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksCore.Tactic.StacksAttribute
public import
StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleAssociatedSheafRestriction
public import
StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupportComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleZariskiCohomology
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelianSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteSheafCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerived.DerivedDeltaFunctor

/-!
# Cohomology with support in a closed subscheme: the étale–Zariski comparison on Mathlib's site

Let `X` be a scheme, `Z ⊆ X` a closed subset with open complement `U`, and `F` a quasi-coherent
`𝒪_X`-module with associated sheaf `Fᵃ` on the small étale site of `X` (Stacks 03DU,
`AlgebraicGeometry.smallEtaleAssociatedSheaf`).  Cohomology with support in `Z` is the right
derived functor of the functor of global sections vanishing on `U`.  This file compares the
Zariski and small étale versions of that derived functor at the coefficients `F` and `Fᵃ`, which
is clause (1) of Stacks 0A46, with no hypothesis beyond the source's.

The comparison is the one of the source.  The small Zariski site of `X` sits inside Mathlib's
small étale site as `AlgebraicGeometry.opensToEtale`; the direct image `ε_*` along the resulting
morphism of sites is restriction of an étale abelian sheaf to the opens of `X`, and sections on
the étale site over the image of an open are *literally* the sections of the restriction over
that open.  Consequently the étale functor of sections vanishing on `U` is `ε_*` followed by its
Zariski counterpart (`Stacks.Sites.SupportedSections.sectionsVanishingOutsidePushforward`).
Since `ε_*` is left exact and carries injective abelian sheaves to injective abelian sheaves, a
coefficient whose higher direct images under `ε_*` vanish has its étale derived supported
sections computed by the Zariski ones
(`Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfObjAcyclic`).  For `Fᵃ` both inputs are
available: the higher direct images vanish by
`AlgebraicGeometry.isZero_rightDerived_pushforward_opensToEtale`, and the direct image itself is
`F` by `AlgebraicGeometry.smallEtaleSectionsUnitIso`.  Those two are the two halves of
Stacks 03P2 for `𝒞 = X_étale`.

## Main definitions

* `AlgebraicGeometry.zariskiSectionsVanishingOutside` and
  `AlgebraicGeometry.smallEtaleSectionsVanishingOutside` — for an inclusion `V' ⟶ V` of opens
  of `X`, the sections over `V` vanishing on `V'`, on the small Zariski and on Mathlib's small
  étale site.  `AlgebraicGeometry.smallEtaleSectionsWithSupport` is the case of the complement
  of a closed subset inside `⊤`, which is the functor `Γ_Z` of the source on `X_étale`; on the
  Zariski side that case is `AlgebraicGeometry.SmallEtale.zariskiSectionsWithSupport`.

## Main results

* `AlgebraicGeometry.smallEtaleZariskiPushforward_preservesInjectiveObjects` — `ε_*` carries
  injective abelian sheaves to injective abelian sheaves.
* `AlgebraicGeometry.sectionsVanishingOutsideCohomologyEtaleIso` — the comparison with the pair
  of opens left free, which is where the work is done.
* `AlgebraicGeometry.supportedCohomologyEtaleIso` — **Stacks 0A46, clause (1)**:
  `H^q_Z(X_étale, Fᵃ)` agrees with `H^q_Z(X, F)` in every degree.  It is the previous
  declaration at the inclusion of the complement of `Z` into `⊤`.

## Implementation notes

On the small étale site cut out of a big étale site, whose ingredients for this comparison are
in `StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupportComparison`, the
vanishing of the higher direct images of `Fᵃ` along the inclusion of the small Zariski site is
not available.  On Mathlib's small étale site that vanishing is proved, which is why this file
works there.

Clause (2) of the tag — that `i_*ℋ^q_Z(Fᵃ)` is a quasi-coherent `𝒪_X`-module equal to
`(i_*ℋ^q_Z(F))^a` when the complement of `Z` is retrocompact in `X` — is
`AlgebraicGeometry.supportedCohomology_isQuasicoherent_and_associatedSheaf`, and the two
declarations together state the tag.  The two clauses are stated on two models of the small
étale site of `X`.  Clause (2) uses the small étale site cut out of a big étale site containing
`X`, `AlgebraicGeometry.SmallEtale.topology`, on which the étale functor `i_*ℋ_Z` and its long
exact sequence (Stacks 0A45), the exact functor `F ↦ Fᵃ` (Stacks 08H8) and Descent, Lemma 071N
are proved.  On both sites `Fᵃ` is the sheaf of sections `(T ⟶ X) ↦ Γ(T, T^*F)`, and the two
topoi are equivalent by `AlgebraicGeometry.smallEtaleToCommonToposEquiv`.

The degrees are the natural numbers, which is the source's range `q ≥ 0`.

Two points make the two sides the groups the source names.  First, the open `⊤` of `X`, read as
an object of the small étale site, is a *final* object there — this is
`AlgebraicGeometry.isTerminal_opensToEtale_top` — so the sections over it which
`smallEtaleSectionsWithSupport` cuts down are the global sections of `X_étale`; the same holds
for `⊤` on the small Zariski site.  Second, the comparison is *constructed* and not chosen: it is
the composite of the identification of the étale supported-sections functor with the Zariski one
after direct image, the collapse of the derived functor of that composite at the
`ε_*`-acyclic coefficient `Fᵃ`, and the unit of the associated-sheaf comparison.

Coefficients are `AddCommGrpCat.{u}` on both sites, the morphism universe of the small étale
site, which is where `AlgebraicGeometry.isZero_rightDerived_pushforward_opensToEtale` and
`AlgebraicGeometry.enoughInjectives_sheaf_smallEtaleTopology` live.

`Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfObjAcyclic` is used rather than
`Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic`, which asks the left factor to
be exact, whereas `ε_*` is right exact only when every local ring of `X` is strictly henselian
(Stacks 09AX, `AlgebraicGeometry.zariskiPushforward_preservesFiniteColimits`).

## References

* [Stacks Project, Tag 0A46](https://stacks.math.columbia.edu/tag/0A46)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-! ### The direct image along the inclusion of the small Zariski site -/

variable (X : Scheme.{u})

/-- The direct image `ε_*` is additive: on sections it is the identity. -/
public instance smallEtaleZariskiPushforward_additive :
    (smallEtaleZariskiPushforward X).Additive where
  map_add := by intros; rfl

/-- **The direct image `ε_*` carries injective abelian sheaves to injective abelian sheaves.**
Its left adjoint is lower shriek along `AlgebraicGeometry.opensToEtale`, which is exact because
the opens of `X` have fibre products and equalizers and `opensToEtale` preserves them. -/
public instance smallEtaleZariskiPushforward_preservesInjectiveObjects :
    (smallEtaleZariskiPushforward X).PreservesInjectiveObjects :=
  Stacks.Cohomology.BiggerSite.preservesInjectiveObjects_sheafPushforwardContinuous
    (Opens.grothendieckTopology ↥X) (Scheme.smallEtaleTopology X) (opensToEtale X)

/-- The direct image `ε_*` is left exact, being a right adjoint. -/
public instance smallEtaleZariskiPushforward_preservesFiniteLimits :
    PreservesFiniteLimits (smallEtaleZariskiPushforward X) :=
  haveI : (smallEtaleZariskiPushforward X).IsRightAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (opensToEtale X)
      AddCommGrpCat.{u} (Opens.grothendieckTopology ↥X)
      (Scheme.smallEtaleTopology X)).isRightAdjoint
  inferInstance

/-! ### The two functors of sections vanishing on an open -/

/-- Sections over an open `V` of `X` vanishing on a smaller open `V'`, on the small Zariski
site of `X`.  At the inclusion of the complement of a closed subset `Z` into `⊤` this is the
functor `Γ_Z` of global sections supported on `Z`. -/
public abbrev zariskiSectionsVanishingOutside {V' V : X.Opens} (f : V' ⟶ V) :
    Sheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  Stacks.Sites.SupportedSections.sectionsVanishingOutside.{u}
    (Opens.grothendieckTopology ↥X) f

/-- Sections over an open `V` of `X`, read as an object of the small étale site, vanishing on a
smaller open `V'`.  At the inclusion of the complement of a closed subset `Z` into `⊤` this is
the functor `Γ_Z` on `X_étale`. -/
public abbrev smallEtaleSectionsVanishingOutside {V' V : X.Opens} (f : V' ⟶ V) :
    Sheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  Stacks.Sites.SupportedSections.sectionsVanishingOutside.{u} (Scheme.smallEtaleTopology X)
    ((opensToEtale X).map f)

/-- **The étale functor of sections vanishing on an open is the direct image followed by the
Zariski one.**  Sections on the small étale site over the image of an open of `X` are the
sections of the restriction over that open, and the two restriction maps agree. -/
public def smallEtaleSectionsVanishingOutsideIso {V' V : X.Opens} (f : V' ⟶ V) :
    smallEtaleZariskiPushforward X ⋙ zariskiSectionsVanishingOutside X f ≅
      smallEtaleSectionsVanishingOutside X f :=
  Stacks.Sites.SupportedSections.sectionsVanishingOutsidePushforward.{u}
    (Opens.grothendieckTopology ↥X) (Scheme.smallEtaleTopology X) (opensToEtale X) f

/-! ### The comparison -/

variable (F : X.Modules) [F.IsQuasicoherent]

/-- **The étale–Zariski comparison for sections vanishing on an open, in every degree.**  For a
quasi-coherent `𝒪_X`-module `F` and an inclusion `f : V' ⟶ V` of opens of a scheme `X`, the
right derived functors of "sections over `V` vanishing on `V'`" agree at the associated sheaf
`Fᵃ` on `X_étale` and at `F` on `X_Zariski`.

This is `AlgebraicGeometry.supportedCohomologyEtaleIso` with the pair of opens left free; the
closed-subset form of the source is the case `f = SmallEtale.openComplementι`.  The comparison is
*constructed*: it is the identification of the étale functor with the Zariski one after direct
image, the collapse of the derived functor of that composite at the `ε_*`-acyclic coefficient
`Fᵃ`, and the unit `ε_*(Fᵃ) ≅ F`. -/
public def sectionsVanishingOutsideCohomologyEtaleIso {V' V : X.Opens} (f : V' ⟶ V) (q : ℕ) :
    ((smallEtaleSectionsVanishingOutside X f).rightDerived q).obj
        (smallEtaleAssociatedSheaf X F) ≅
      ((zariskiSectionsVanishingOutside X f).rightDerived q).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) :=
  haveI : (smallEtaleZariskiPushforward X ⋙ zariskiSectionsVanishingOutside X f).Additive :=
    inferInstance
  (Stacks.Cohomology.CechDelta.rightDerivedIsoOfIso
      (smallEtaleSectionsVanishingOutsideIso X f).symm q).app
    (smallEtaleAssociatedSheaf X F) ≪≫
  Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfObjAcyclic
    (smallEtaleZariskiPushforward X) (zariskiSectionsVanishingOutside X f)
    (smallEtaleAssociatedSheaf X F)
    (fun n hn ↦ isZero_rightDerived_pushforward_opensToEtale X F n hn) q ≪≫
  ((zariskiSectionsVanishingOutside X f).rightDerived q).mapIso
    (smallEtaleSectionsUnitIso X F).symm

/-! ### Clause (1) of Stacks 0A46 -/

variable (Z : Set ↥X) (hZ : IsClosed Z)

/-- `Γ_Z` on the small étale site of `X`: sections of an abelian sheaf over `X` whose
restriction to the open complement of `Z`, read as an object of the small étale site,
vanishes. -/
public abbrev smallEtaleSectionsWithSupport :
    Sheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  smallEtaleSectionsVanishingOutside X (SmallEtale.openComplementι X Z hZ)

/-- **Stacks 0A46, clause (1).**  For a quasi-coherent `𝒪_X`-module `F` and a closed subset `Z`
of a scheme `X`, cohomology with support in `Z` of the associated sheaf `Fᵃ` on the small étale
site of `X` agrees, in every degree, with cohomology with support in `Z` of `F` on the small
Zariski site.

Both sides are right derived functors of the functor of global sections vanishing on the open
complement of `Z`, taken on the respective site.  There is no hypothesis beyond those of the
source: the vanishing of the higher direct images `R^nε_*(Fᵃ)` for `n > 0` is
`AlgebraicGeometry.isZero_rightDerived_pushforward_opensToEtale` and the identification of
`ε_*(Fᵃ)` with `F` is `AlgebraicGeometry.smallEtaleSectionsUnitIso`, those two being the two
halves of Stacks 03P2 for `𝒞 = X_étale`. -/
@[stacks 0A46 "clause (1): cohomology with support in a closed subset agrees between \
the small etale site and the Zariski site, for a quasi-coherent module, in every degree, with \
no hypothesis beyond the source's. Clause (2) is \
supportedCohomology_isQuasicoherent_and_associatedSheaf, on the size-bounded small etale site"]
public def supportedCohomologyEtaleIso (F : X.Modules) [F.IsQuasicoherent] (q : ℕ) :
    ((smallEtaleSectionsWithSupport X Z hZ).rightDerived q).obj
        (smallEtaleAssociatedSheaf X F) ≅
      ((SmallEtale.zariskiSectionsWithSupport X Z hZ).rightDerived q).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) :=
  sectionsVanishingOutsideCohomologyEtaleIso X F (SmallEtale.openComplementι X Z hZ) q

end AlgebraicGeometry

end
