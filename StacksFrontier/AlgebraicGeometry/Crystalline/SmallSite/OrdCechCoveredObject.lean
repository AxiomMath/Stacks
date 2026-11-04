module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LocalizedSiteCohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OrdCechRestrictCover
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.AcyclicCoveringFamilyCohomology

/-!
# [Stacks, Tag 03F7] for a restriction cover, and the route to the global `RΓ`

`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/OrdCechRestrictCover.lean` proves that the
ordered Čech complex of a restriction cover of an object `A` of `Cris(X/S)` computes the *Čech*
cohomology of that covering family, `...CrystallineThickening.restrictOrdCechCohomologyIso`, and
stops there: passing from Čech cohomology of a family to cohomology is [Stacks, Tag 03F7], which
that file does not apply.  Item 5 of the "What is and is not proved" section of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CechCoverComplex.lean` records that
[Stacks, Tag 03F7] *does* apply to these coverings — its two hypotheses being
`...CechCovering.restrictOpenCover_mem_smallTopology` and
`...CrystallineThickening.hasProduct_restrictOpenHypercover`, with the universes lining up — but
that the instantiation, with the covering family inlined, does not elaborate within the default
heartbeat budget.

This file records it.  The instantiation elaborates in well under a second once the covering
family is kept as a variable `V` and the covering statement as a hypothesis `hV`, rather than
inlined; nothing was weakened to obtain it.  The file then carries the conclusion along the two
identifications that the consumers of [Stacks, Tag 07MN] need: to the cohomology
`H^j(Cris(X/S)/A, F)` of the localized site, and from there — under the one hypothesis that the
missing terminal object costs — to the global `...SmallSite.cohomologyFunctor`.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `isIso_cechCohomologyToCohomology_restrictOpenHypercover` — **[Stacks, Tag 03F7] at a
  restriction cover of an object of `Cris(X/S)`**: for an abelian sheaf acyclic on the finite
  fibre products of the cover, the comparison of [Stacks, Tag 03AX] from the Čech cohomology of
  the cover to the cohomology of `F` over `A` is an isomorphism in every degree.
* `restrictCechCohomologyIsoOverCohomology` — the same read as an isomorphism
  `Ȟ^j(𝒰_A, F) ≅ H^j(Cris(X/S)/A, F)` of groups, through
  `...SmallSite.overCohomologyIsoRightDerivedSections`.
* **`restrictOrdCechOverCohomologyIso`** — **the ordered Čech complex of a restriction cover of
  `A` computes the cohomology of `F` over `A`**, in every degree.  This is the step
  `restrictOrdCechCohomologyIso` left open.
* `restrictOrdCechCohomologyFunctorIso` — **the same with the global `H^j(Cris(X/S), -)` on the
  right**, under the hypothesis `hΓ` that sections over `A` *are* the global sections of the
  site.  That hypothesis is the whole cost of `Cris(X/S)` having no terminal object; it is not a
  stand-in for any tag, and it is discharged whenever `A` is terminal.
* `restrictOrdCechCohomologyFunctorIso_of_isTerminal` — the previous statement with `hΓ`
  discharged at a terminal `A`, by `CategoryTheory.Sheaf.ΓNatIsoSheafSections`.

## What is and is not proved

**[Stacks, Tag 07MN] is not proved and no tag attribute for it is placed**, here or anywhere.
What is closed is one of the two things that item 5 of `CechCoverComplex.lean` says is left of
the remark's "insert future reference here" step: the Čech-to-cohomology comparison for the
restriction covers.  Three things are *not* closed.

* **The global sections of `Cris(X/S)`.**  [Stacks, Tag 03F7] computes the cohomology of the
  *covered object*, and `Cris(X/S)` has no terminal object; this is not a gap in the Čech
  argument but the difference between `H^j(Cris(X/S)/A, -)` and `H^j(Cris(X/S), -)`.  It is
  isolated here into the single datum `hΓ : globalSections S ≅ sectionsFunctorOver S A` of
  `restrictOrdCechCohomologyFunctorIso` — a natural isomorphism of functors, not a proposition
  named after a tag — and discharged at a terminal object.  The only terminal object of a small
  crystalline site this library has is
  `Crystalline.GlobalCrystallineSituation.isTerminal_closedFiberCrystallineThickening`, which is
  terminal in `Cris(S₀/S)` and says nothing about `Cris(X/S)` for a general `X`; the general
  statement needs a covering of the final sheaf by objects of the site, which is what
  [Stacks, Tag 07MM] builds out of the divided power envelopes and what item 2 of
  `CechCoverComplex.lean` still owes.
* **The index universe of the double complex of [Stacks, Tag 07MN].**  The covering families of
  `Cris(X/S)` are indexed by `Type (u + 1)` — that is the index universe of
  `...CrystallineThickening.restrictOpenCover`, of
  `...SmallSite.smallZariskiCovering_mem_smallTopology`, and of the
  `CategoryTheory.PreZeroHypercover` that [Stacks, Tag 03F7] is stated for —
  whereas `...SmallSite.CechSystem` and `...SmallSite.OrdCechTuple` fix their index type `Λ` in
  `Type u`, and `...CechCovering.restrictOpenCover_mem_smallTopology` therefore ULifts: it covers
  with `fun l : ULift.{u + 1} Λ ↦ ...`.  Everything below is stated at an index type in
  `Type (u + 1)`, which is the one the coverings have, so it applies verbatim to that ULifted
  family; what it does *not* reach is
  `...SmallSite.restrictOrdCechSystemCohomologyIso` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/OrdCechSystemIdentification.lean`, whose
  `Λ` is in `Type u`.  Composing the two asks for the reindexing isomorphism of ordered Čech
  complexes along the order isomorphism `ULift.{u + 1} Λ ≃o Λ`, which is not in the library:
  `...CechComplex.Alternating` reindexes *tuples* (`tres`) and not the index type of the family.
  The gap is a formalization artifact — the `Λ` of the remark is a finite index set — and not
  mathematics.
* **The de Rham direction** of the remark, item 4 of `CechCoverComplex.lean`, which is untouched
  here.

No tag attribute is placed in this file.  [Stacks, Tag 03F7] itself is tagged where it is proved,
`Stacks.CechSite.Acyclic.isIso_cechCohomologyToCohomology_app` and
`Stacks.CechSite.Acyclic.cechCohomologyIsoRightDerivedSections`; the declarations below are its
instantiation at one site and carry no content of the tag beyond it.

## References

* [Stacks Project, Tag 03F7](https://stacks.math.columbia.edu/tag/03F7)
* [Stacks Project, Tag 03AX](https://stacks.math.columbia.edu/tag/03AX)
* [Stacks Project, Tag 07MN](https://stacks.math.columbia.edu/tag/07MN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open _root_.Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening

attribute [local instance] HasDerivedCategory.standard

variable {S : GlobalCrystallineSituation.{u}} (A : CrystallineThickening S) {ι : Type (u + 1)}
  (V : ι → A.obj.thickening.target.scheme.Opens)

/-- **The acyclicity hypothesis of [Stacks, Tag 03F7] for a restriction cover of an object of
`Cris(X/S)`**: the higher cohomology of the abelian sheaf `F` vanishes over every nonempty finite
fibre product, taken in `Over A`, of members of the family of restrictions.

This is the hypothesis of the tag, spelled at this site; it is not discharged here.  For a
locally quasi-coherent module it is what [Stacks, Tag 07JJ] supplies, in the shape
`...SmallSite.Vanishing07JJ`, on the objects with affine ambient scheme. -/
def RestrictCoverAcyclic (A : CrystallineThickening S) {ι : Type (u + 1)}
    (V : ι → A.obj.thickening.target.scheme.Opens)
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) : Prop :=
  ∀ (r : ℕ) (s : Fin (r + 1) → (restrictOpenHypercover A V).I₀) (q : ℕ), 0 < q →
    IsZero (((Stacks.CechSite.Acyclic.tupleSections (smallTopology S)
      (restrictOpenHypercover A V) s).rightDerived q).obj F)

/-- **A family of restrictions of `A` to opens covering its ambient scheme generates a covering
sieve of the small crystalline site.**  This is
`...CrystallineThickening.isZariskiCovering_restrictOpenCover` through
`...SmallSite.smallZariskiCovering_mem_smallTopology`, in the
`...CrystallineThickening.restrictOpenHypercover` spelling that [Stacks, Tag 03F7] asks for; the
two families are the same, `...CrystallineThickening.restrictOpenHypercover_eq_restrictOpenCover`.
It is what discharges the hypothesis `hV` below. -/
theorem restrictOpenHypercover_mem_smallTopology
    (hcov : ∀ x : A.obj.thickening.target.scheme, ∃ i, x ∈ V i) :
    Sieve.generate (restrictOpenHypercover A V).presieve₀ ∈ smallTopology S A :=
  smallZariskiCovering_mem_smallTopology S _
    (CrystallineThickening.isZariskiCovering_restrictOpenCover A V hcov)

variable (hV : Sieve.generate (restrictOpenHypercover A V).presieve₀ ∈ smallTopology S A)

/-- **Stacks Project, Tag 03F7 at a restriction cover of an object of `Cris(X/S)`.**  Let `A` be
an object of the small crystalline site, let `V` be a family of opens of its ambient scheme whose
restrictions `A|_{V_i} ⟶ A` generate a covering sieve, and let `F` be an abelian sheaf whose
higher cohomology vanishes over every nonempty finite fibre product of those restrictions.  Then
the comparison of [Stacks, Tag 03AX] from the Čech cohomology of the family to the cohomology of
`F` over `A` is an isomorphism in every degree.

Both hypotheses of the general statement are available at this site: the covering statement is
`...CechCovering.restrictOpenCover_mem_smallTopology` (or
`...CrystallineThickening.isZariskiCovering_restrictOpenCover` through
`...SmallSite.smallZariskiCovering_mem_smallTopology`), and the iterated fibre products of a
restriction cover exist, `...CrystallineThickening.hasProduct_restrictOpenHypercover`.  The
coefficient universe matches: the objects of `Cris(X/S)` form a `Type (u + 1)` and its morphisms
a `Type u`, so the `max u v` of the general statement is `u + 1`. -/
theorem isIso_cechCohomologyToCohomology_restrictOpenHypercover
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (hac : RestrictCoverAcyclic A V F) (p : ℤ) :
    IsIso ((Stacks.CechSite.cechCohomologyToCohomology.{u + 1} (smallTopology S)
      (restrictOpenHypercover A V) hV p).app F) :=
  Stacks.CechSite.Acyclic.isIso_cechCohomologyToCohomology_app (smallTopology S)
    (restrictOpenHypercover A V) hV F hac p

/-- **The Čech cohomology of a restriction cover of `A` is the cohomology of `F` over `A`**, as
an isomorphism of groups, the right hand side being the `j`-th right derived functor of sections
over `A`.  This is `Stacks.CechSite.Acyclic.cechCohomologyIsoRightDerivedSections` at this
site. -/
def restrictCechCohomologyIsoRightDerivedSections
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (hac : RestrictCoverAcyclic A V F) (j : ℕ) :
    Stacks.CechSite.cechCohomology (restrictOpenHypercover A V) F.obj j ≅
      ((sectionsFunctorOver S A).rightDerived j).obj F :=
  Stacks.CechSite.Acyclic.cechCohomologyIsoRightDerivedSections (smallTopology S)
    (restrictOpenHypercover A V) hV F hac j

/-- **The Čech cohomology of a restriction cover of `A` is the cohomology of the localized site
`Cris(X/S)/A`**, `Ȟ^j(𝒰_A, F) ≅ H^j(Cris(X/S)/A, F)`.  This is
`restrictCechCohomologyIsoRightDerivedSections` read through
`...SmallSite.overCohomologyIsoRightDerivedSections`, which identifies the cohomology of the
localized site with the right derived sections over the object. -/
def restrictCechCohomologyIsoOverCohomology
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (hac : RestrictCoverAcyclic A V F) (j : ℕ) :
    Stacks.CechSite.cechCohomology (restrictOpenHypercover A V) F.obj j ≅
      (overCohomologyFunctor S A j).obj ((restrictToOver S A).obj F) :=
  restrictCechCohomologyIsoRightDerivedSections A V hV F hac j ≪≫
    (overCohomologyIsoRightDerivedSections S A F j).symm

/-- **The ordered Čech complex of a restriction cover of an object of `Cris(X/S)` computes the
cohomology of that object**, in every degree:

`H^j(C_ord(𝒰_A, F)) ≅ H^j(Cris(X/S)/A, F)`.

This is the step that `...CrystallineThickening.restrictOrdCechCohomologyIso` left open.  That
isomorphism lands the ordered complex on the Čech cohomology of the covering family —
[Stacks, Tag 01FM] and [Stacks, Tag 01FK] (2) for the family, lifted off the opens of a space —
and `restrictCechCohomologyIsoOverCohomology` carries the Čech cohomology to the cohomology of
the covered object by [Stacks, Tag 03F7]. -/
def restrictOrdCechOverCohomologyIso [LinearOrder ι]
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (hac : RestrictCoverAcyclic A V F) (j : ℕ) :
    (CrystallineThickening.restrictCechComplexOrd.{u + 1, u, u} A V F.obj).homology j ≅
      (overCohomologyFunctor S A j).obj ((restrictToOver S A).obj F) :=
  CrystallineThickening.restrictOrdCechCohomologyIso.{u + 1, u, u} A V F.obj j ≪≫
    restrictCechCohomologyIsoOverCohomology A V hV F hac j

/-! ### The global cohomology of `Cris(X/S)` -/

/-- **The ordered Čech complex of a restriction cover of `A` computes the global cohomology of
`Cris(X/S)`**, in every degree, *provided* the sections over `A` are the global sections of the
site.

`Cris(X/S)` has no terminal object, so sections over an object are not global sections, and that
is the whole distance between `restrictOrdCechOverCohomologyIso` and the `RΓ(Cris(X/S), -)` of
[Stacks, Tag 07MN].  The distance is carried here as the datum `hΓ`, a natural isomorphism
`Γ(Cris(X/S), -) ≅ Γ(A, -)` of functors on abelian sheaves; given it, the two right derived
functors agree by `CategoryTheory.Functor.rightDerivedIsoOfNatIso`, and
`...SmallSite.rightDerivedGlobalSectionsIso` turns the right derived global sections into
`...SmallSite.cohomologyFunctor`.

`hΓ` is *not* a stand-in proposition for an unproved tag: it is the statement that `A`
corepresents global sections, which is a property of `A` and of nothing else, and it is
discharged at a terminal object in
`restrictOrdCechCohomologyFunctorIso_of_isTerminal`. -/
def restrictOrdCechCohomologyFunctorIso [LinearOrder ι]
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (hac : RestrictCoverAcyclic A V F)
    (hΓ : globalSections S ≅ sectionsFunctorOver S A) (j : ℕ) :
    (CrystallineThickening.restrictCechComplexOrd.{u + 1, u, u} A V F.obj).homology j ≅
      (cohomologyFunctor S j).obj F :=
  CrystallineThickening.restrictOrdCechCohomologyIso.{u + 1, u, u} A V F.obj j ≪≫
    restrictCechCohomologyIsoRightDerivedSections A V hV F hac j ≪≫
    ((Functor.rightDerivedIsoOfNatIso hΓ j).app F).symm ≪≫
    (rightDerivedGlobalSectionsIso S j).app F

/-- **The ordered Čech complex of a restriction cover of a terminal object of `Cris(X/S)`
computes the global cohomology of `Cris(X/S)`.**  This is
`restrictOrdCechCohomologyFunctorIso` with its hypothesis `hΓ` discharged: over a terminal object
the global sections of a sheaf are its sections, `CategoryTheory.Sheaf.ΓNatIsoSheafSections`.

The hypothesis is on `A` alone and is exactly what `Cris(X/S)` does not supply in general; see
the "What is and is not proved" section of this file. -/
def restrictOrdCechCohomologyFunctorIso_of_isTerminal [LinearOrder ι]
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (hac : RestrictCoverAcyclic A V F) (hA : IsTerminal A) (j : ℕ) :
    (CrystallineThickening.restrictCechComplexOrd.{u + 1, u, u} A V F.obj).homology j ≅
      (cohomologyFunctor S j).obj F :=
  have : HasTerminal (CrystallineThickening S) := hA.hasTerminal
  restrictOrdCechCohomologyFunctorIso A V hV F hac
    (Sheaf.ΓNatIsoSheafSections (smallTopology S) AddCommGrpCat.{u + 1} hA) j

end Crystalline.GlobalCrystallineSituation.SmallSite

end
