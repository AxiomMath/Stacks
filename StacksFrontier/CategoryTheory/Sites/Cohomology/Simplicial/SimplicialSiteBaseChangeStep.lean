module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialSiteColumnStep
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialSiteMooreBicomplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialSitePulledBackCopower
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.StdCoverResolution
import StacksCore.Tactic.StacksAttribute

/-!
# The fourth step of the proof of Stacks 09D2

Let `C` be a site and let `A_• ⟶ B_•` be a homomorphism of simplicial sheaves of rings on `C`.
[Stacks, Tag 09D2] asserts that if `L π_! A_• ⟶ L π_! B_•` is an isomorphism in `D(C)` then
`L π_!(K) = L π_!(K ⊗^𝐋_{A_•} B_•)` for every `K` in `D(A_•)`. Its proof has four steps: `L π_!`
commutes with colimits, so it is enough to treat bounded above complexes; such a complex has a
flat resolution ([Stacks, Tag 03EW]), so it is enough to treat a flat `A_•`-module, for which the
derived tensor product is the ordinary one; by [Stacks, Tag 08PJ] and [Stacks, Tag 08PI] the
cohomology sheaves of both sides are computed on the fibre categories `Δ × U`, so it is enough to
treat the restriction of the module to them; and there the statement is [Stacks, Tag 08RX]. This
file proves the fourth step.

## The gap at the junction of the third and fourth steps, and what replaces it

The third step does not supply what the fourth consumes. Applied at the fibre over `U`, the
hypothesis (2) of [Stacks, Tag 08RX] is that `s(A_•(U)) ⟶ s(B_•(U))` be a quasi-isomorphism, for
each `U` separately. The hypothesis of [Stacks, Tag 09D2] is only that `L π_! A_• ⟶ L π_! B_•` be
invertible, which by [Stacks, Tag 08PJ] and [Stacks, Tag 08PI] says that the **sheafification** of
the fibrewise homology maps is invertible. That is strictly weaker, and visibly so in this
library: in the namespace `Stacks.Sites.FibredCategory.FibredCategorySituation`, the equivalence
`isIso_derivedAbelianLowerShriekHomology_map_iff` has the sheafified condition on its right-hand
side, while the fibrewise condition enters only through the one-way
`isIso_derivedAbelianLowerShriekHomology_map_of_fibrewise`.
Nor can the weaker hypothesis be upgraded on a covering: a morphism of presheaves whose
sheafification is invertible need not be invertible over any object of any covering sieve, new
sections and new relations appearing at each refinement.

The lemma is nevertheless true as stated, and the repair is not to patch the third step but to
skip it: [Stacks, Tag 08RX] is proved by resolving the coefficients by the generators
`j_{U!}O_U` and using that the standard simplices are contractible, and **that argument runs on
the simplicial site `Δ × C` itself**, where the hypothesis it needs is exactly the sheaf-level
hypothesis that [Stacks, Tag 09D2] grants. Two facts carry it, both proved on this branch:

* the projection away from the simplex factor of a representable of `Δ × C` is, at each fibre, a
  simplicial homotopy equivalence
  (`Stacks.SimplicialSite.homotopyEquivalences_copowerMap_prodProjIndex_fibre`), so multiplying by
  it changes no Moore homology — this is where the contractibility of the standard simplices
  ([Stacks, Tag 08QD]) is spent;
* an abelian presheaf which sheafifies to zero has a copower which sheafifies to zero
  (`Stacks.isZero_presheafToSheaf_copower`), so the copower by a presheaf of sets does not see
  sheafification and a sheaf-level quasi-isomorphism survives it
  (`Stacks.quasiIso_mapHomologicalComplex_presheafToSheaf_copowerFunctor`) — this is the formal
  content of the conclusion of [Stacks, Tag 09D2] being sheaf-local.

The resolution consumed is the standard-cover form of [Stacks, Tag 03EW],
`PresheafOfModules.exists_isStdCover_resolution_of_isLE`, which is the form the proof of
[Stacks, Tag 08RX] itself quotes and which refines the flat resolution of the second step
(`Stacks.SimplicialModules.exists_isFlat_resolution`): a standard cover is a direct sum of free
modules on representables, and those are flat.

## Main results

* `Stacks.SimplicialModules.quasiIso_mooreSheafBaseChange_app_of_quasiIso`: the base-change unit
  `s(F) ⟶ s(F ⊗_{A_•} B_•)` is a quasi-isomorphism at every standard cover, under the hypothesis
  of [Stacks, Tag 09D2] and nothing else.
* `Stacks.SimplicialModules.quasiIso_total_mooreSheafBicomplexBaseChangeMap_of_isStdCover`:
  **the fourth step.** The same for a bounded above complex of standard covers, which is the
  object the earlier steps hand over.

Composing those with the second step gives the statement for an arbitrary sectionwise flat
simplicial module, which is what the source's proof reduces [Stacks, Tag 09D2] to: that is
`Stacks.SimplicialModules.quasiIso_mooreSheafBaseChange_app_of_flat` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Simplicial/SimplicialSiteFlatBaseChange.lean`. It is
not the lemma either, and is likewise untagged.

## Nothing here is tagged 09D2, and what would have to be true for anything to be

[Stacks, Tag 09D2] is a single lemma. Its four "steps" are steps of its *proof*, not numbered
parts of its statement, so a declaration proving one of them is not a member of any covering set
for the tag: the tag belongs on a declaration whose statement is the lemma — a hypothesis that
`L π_! A_• ⟶ L π_! B_•` be invertible in `D(C)`, and the conclusion
`L π_!(K) = L π_!(K ⊗^𝐋_{A_•} B_•)` for **every** `K` in `D(A_•)`. Nothing in this library states
that yet, and in particular nothing below does: the declarations here mention neither `L π_!`,
nor the derived tensor product, nor an arbitrary object of `D(A_•)`, and the complex they treat is
bounded above.

Three things are owed before the tag can be registered anywhere.

1. **`L π_!` on a complex.** [Stacks, Tag 09D0] is available on this branch, as
   `Stacks.SimplicialModules.derivedProjectionLowerShriekIsoMooreComplex`, but only for a single
   abelian sheaf placed in degree `0`: `L π_!(ℱ[0]) ≅ s(ℱ_•)`. The conclusion of Tag 09D2 is about
   a complex, so what is needed is that identification for a bounded above complex, i.e. between
   `L π_!` and the total complex of the Moore double complex used here. The five Moore modules of
   this directory mention no derived category at all.
2. **The derived tensor product, in the category the Moore machinery works in.**
   `Stacks.SimplicialModules.derivedSimplicialBaseChange` is `- ⊗^𝐋_{A_•} B_•` on sheaves of
   modules, and `Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedPullbackObjIsoOfFlat`
   computes it on a bounded above complex with flat terms; the Moore machinery here works on
   *presheaves* of modules over a presheaf of rings, and the identification of
   `Stacks.PresheafOfModules.ChangeOfRings.changeOfRings` with extension of scalars on sheaves of
   modules across `Stacks.SimplicialModules.equivSheafOfModules` is not in the library.
3. **The unbounded case.** The source's reduction of an arbitrary `K` in `D(A_•)` to bounded above
   complexes is the first step together with Derived Categories, Proposition 13.29.2; only the
   first step is available here. Restricting the conclusion to bounded above `K` would be a
   special case of the lemma, not the lemma.

The other three steps are also untagged, and for the same reason: the first and third in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Simplicial/SimplicialSiteLowerShriek.lean`, the
second in `StacksFrontier/CategoryTheory/Sites/Cohomology/Simplicial/SimplicialFlatResolution.lean`.
The third is a true statement and is left standing; it is simply not a step the corrected proof
uses.

## Implementation notes

Simplicial modules are taken here as presheaves of modules on `Δ × C`, not as sheaves of modules;
since `s(-)` sheafifies in each degree this loses nothing and assumes less, a sheaf of modules
having an underlying presheaf of modules with the same `s(-)`.

## References

* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2)
* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
* [Stacks Project, Tag 08QD](https://stacks.math.columbia.edu/tag/08QD)
* [Stacks Project, Tag 08PI](https://stacks.math.columbia.edu/tag/08PI)
* [Stacks Project, Tag 08PJ](https://stacks.math.columbia.edu/tag/08PJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Stacks.PresheafOfModules.ChangeOfRings

universe u

namespace Stacks.SimplicialModules

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  {O O' : (SimplexCategory × C)ᵒᵖ ⥤ CommRingCat.{u}} (θ : O ⟶ O')

/-- **The base-change unit is a quasi-isomorphism at a standard cover, under the hypothesis of
[Stacks, Tag 09D2].** The hypothesis `hθ` is that `s(A_•) ⟶ s(B_•)` be a quasi-isomorphism of
complexes of abelian sheaves on `C`, which is the hypothesis of [Stacks, Tag 09D2] read through
the identification of `L π_!` on simplicial modules with `s(-)`; it is a sheaf-level condition,
not a fibrewise one.

The column step `Stacks.SimplicialModules.quasiIso_mooreSheafBaseChange_app_of_isStdCover` asks
for the unit to be inverted at the copower of the structure ring by a representable pulled back
from `C`, and that is what the hypothesis gives, the copower not seeing sheafification
(`Stacks.SimplicialModules.quasiIso_mooreAbSheafCochain_copowerMap_prodPullbackIndex`). -/
theorem quasiIso_mooreSheafBaseChange_app_of_quasiIso
    (hθ : QuasiIso ((mooreAbSheafCochain J).map (unitMap' θ)))
    {N : PresheafOfModules.{u} (ringPresheaf O)} (hN : PresheafOfModules.IsStdCover N) :
    QuasiIso ((mooreSheafBaseChange J θ).app N) :=
  quasiIso_mooreSheafBaseChange_app_of_isStdCover J θ
    (fun U => quasiIso_mooreAbSheafCochain_copowerMap_prodPullbackIndex J
      (uliftYoneda.{u}.obj U) (unitMap' θ) hθ) hN

/-- **The fourth step of the proof of [Stacks, Tag 09D2]: the appeal to [Stacks, Tag 08RX], run on
the simplicial site `Δ × C` instead of at the fibre categories.**

Let `θ : A_• ⟶ B_•` be a homomorphism of simplicial sheaves of commutative rings on a site `C`,
and suppose `s(A_•) ⟶ s(B_•)` is a quasi-isomorphism of complexes of abelian sheaves on `C` —
the hypothesis of [Stacks, Tag 09D2]. Then for every complex `L` of simplicial `A_•`-modules
which vanishes in positive degrees and all of whose terms are standard covers, the base-change
unit is a quasi-isomorphism on total complexes:

`s(L) ⟶ s(L ⊗_{A_•} B_•)`.

The complex `L` is what the earlier steps hand over: the first reduces to bounded above complexes
and the second resolves such a complex by standard covers
(`PresheafOfModules.exists_isStdCover_resolution_of_isLE`, the form of [Stacks, Tag 03EW] quoted
in the proof of [Stacks, Tag 08RX]), whose terms are direct sums of free modules on
representables and so are flat.

The proof is the column filtration
(`Stacks.SimplicialModules.quasiIso_total_mooreSheafBicomplexBaseChangeMap`, which is
[Stacks, Tag 0133] for a double complex bounded above) applied to
`Stacks.SimplicialModules.quasiIso_mooreSheafBaseChange_app_of_quasiIso`. No hypothesis about the
fibres is made or needed: see the module docstring for why the source's reduction to them cannot
be used, and what replaces it.

It carries no [Stacks, Tag 09D2] attribute; see the module docstring. -/
theorem quasiIso_total_mooreSheafBicomplexBaseChangeMap_of_isStdCover
    (hθ : QuasiIso ((mooreAbSheafCochain J).map (unitMap' θ)))
    (L : CochainComplex (PresheafOfModules.{u} (ringPresheaf O)) ℤ) [L.IsStrictlyLE 0]
    (hL : ∀ p, PresheafOfModules.IsStdCover (L.X p)) :
    QuasiIso (HomologicalComplex₂.total.map (mooreSheafBicomplexBaseChangeMap J θ L)
      (ComplexShape.up ℤ)) :=
  quasiIso_total_mooreSheafBicomplexBaseChangeMap J θ L
    (fun p => quasiIso_mooreSheafBaseChange_app_of_quasiIso J θ hθ (hL p))

end Stacks.SimplicialModules

end
