module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.VanishingCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFinitePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# The canonical morphism to the spectrum of global functions is separated

Let `X` be a quasi-compact, quasi-separated algebraic space all of whose quasi-coherent modules
have vanishing first cohomology, that is the data of Stacks 07UY, and write `A = Γ(X, 𝒪_X)`.
Stacks 07V5 asserts that the canonical morphism `p : X ⟶ Spec A` is separated.

The morphism itself is `AlgebraicGeometry.Space.CohomologyVanishingSituation`'s
`toSpecGlobalFunctions`, built from the universal property of Stacks 05Z1; nothing is
constructed here.  The source's proof chooses a scheme `Y` with a surjective integral morphism
`Y ⟶ X`, finds `Y` affine by Serre's criterion, and descends separatedness of `Y ⟶ Spec A`
along the surjection.

## Main definitions

* `AlgebraicGeometry.Space.ExistsIntegralSurjectiveSchemeCover` is clause (1) of Stacks 09YB.
* `AlgebraicGeometry.Space.SchemeAffineOverFirstZariskiCohomologyVanishing` is clause (1) of
  Stacks 07V0 for a scheme of the site affine over `X`, in Zariski cohomology.

## Main results

* `AlgebraicGeometry.Space.isSeparated_to_affine_of_existsIntegralSurjectiveSchemeCover`: a
  quasi-compact algebraic space covered as in Stacks 09YB, over which the vanishing above
  holds, is separated over every affine object of the site.
* `…CohomologyVanishingSituation.isSeparated_toSpecGlobalFunctions`: **Stacks 07V5**, the
  canonical morphism `X ⟶ Spec A` is separated.
* `…CohomologyVanishingSituation.isAbsolutelySeparated_of_existsIntegralSurjectiveSchemeCover`:
  the stronger conclusion the source's proof reaches, that `X` is a separated algebraic space.

## Implementation notes

*The chain of results used.*  Integrality of the cover `g : Y ⟶ X` gives affineness and
universal closedness of `g` by Stacks 0415,
`AlgebraicGeometry.Space.isIntegralHom_iff_isAffineHom_and_universallyClosed`.  Universal
closedness makes `g` quasi-compact by Stacks 04XW, so `Y` is quasi-compact because `X` is, by
`AlgebraicGeometry.Space.isQuasiCompactSpace_source_of_isQuasiCompact`, and then
`AlgebraicGeometry.Space.compactSpace_of_isQuasiCompactSpace_yoneda_obj` reads that on the scheme.
Serre's criterion, Stacks 01XF in the form
`Stacks.SerreCriterion.isAffine_of_forall_isZero_H1_ideal`, makes `Y` affine.  A morphism
between affine objects of the site is separated,
`AlgebraicGeometry.Space.isSeparated_yoneda_map_of_isAffine`, and the surjection `g` is
universally closed, so part (4) of Stacks 05Z2,
`AlgebraicGeometry.Space.isSeparated_of_isSurjective_of_universallyClosed`, descends
separatedness from `Y ⟶ Spec A` to `X ⟶ Spec A`.  The source's own last step — part (2) of
Stacks 05Z2, separatedness of `X` as an algebraic space — is reached instead from the relative
statement through `AlgebraicGeometry.Space.isAbsolutelySeparated_of_isSeparated_to_affine`,
the target being affine.

*The two carried hypotheses, and what was tried instead.*

`h09YB` is clause (1) of Stacks 09YB, the existence of a scheme with a surjective integral
morphism to `X`.  No declaration of this development carries `@[stacks 09YB]`, so there is
nothing to apply; it is the source's first step and cannot be avoided, since part (4) of
Stacks 05Z2 needs a separated algebraic space surjecting onto `X` and the vanishing hypothesis
alone produces none.

`h07V0` is clause (1) of Stacks 07V0 — `H¹(X', 𝓕') = 0` for an affine morphism `X' ⟶ X` and a
quasi-coherent `𝒪_{X'}`-module — restricted to an `X'` represented by an object of the site and
to a quasi-coherent ideal sheaf, with the first cohomology read as Zariski cohomology of that
scheme.  That clause *is* proved, as
`…CohomologyVanishingSituation.isZero_firstCohomology_of_isAffineHom`, and it is not applied
here for two independent reasons.  First, its first cohomology is the first right derived
functor of `Γ(X, f_*−)` on the small étale ringed site of the space, whereas Stacks 01XF — the
only Serre criterion available, and the one the source cites — consumes the first right derived
functor of `Γ(Y, −)` on the *Zariski* site of the scheme `Y`; the comparison of the two is
Stacks 03DW, whose single attribute site,
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModuleCohomologyDegreeZero.lean`, is
clause-qualified to the case `q = 0`, which is not the degree needed.  The scheme-level half of
that comparison does exist, as `AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso`
(Stacks 03P2 for `𝒞 = S_étale`), but it compares Zariski cohomology of a module with the
cohomology of the associated *abelian* sheaf on the small étale site of the scheme, not with
module cohomology on the small étale site of the algebraic space, and no declaration bridges
those two.  Second, clause (1) itself carries four further hypotheses — Stacks 07UY
at the module universe of the structure rings, 07U8, 03DW and 072Z — none of which the
situation discharges, so routing through it would raise the count to six rather than lower it.
Carrying the clause once, in the shape Stacks 01XF consumes, is therefore the minimum.

Neither hypothesis is a technical condition of the argument below: each is an assertion of a
named tag about `X` alone.  Quasi-separatedness of the situation is not used; quasi-compactness
is, to make the cover quasi-compact.

*Why `IsTerminal T.base` appears.*  It is not a hypothesis of the argument but part of the
signature of `…CohomologyVanishingSituation.toSpecGlobalFunctions`, the canonical
morphism, which cannot be written without it: the universal property of Stacks 05Z1 it is built
from reads a morphism of underlying schemes as a morphism over the base.  The same is true of
the presentation data `V` and `e` of `Spec Γ(X, 𝒪_X)` as an affine object of the site.  Both are
documented at the point of definition, in
`StacksFrontier/AlgebraicGeometry/Spaces/CohomologyVanishingBaseChange.lean`.  The general
statement below, from which the tagged one is a specialization, carries neither.

## References

* [Stacks Project, Tag 07V5](https://stacks.math.columbia.edu/tag/07V5)
* [Stacks Project, Tag 07UY](https://stacks.math.columbia.edu/tag/07UY)
* [Stacks Project, Tag 09YB](https://stacks.math.columbia.edu/tag/09YB)
* [Stacks Project, Tag 07V0](https://stacks.math.columbia.edu/tag/07V0)
* [Stacks Project, Tag 01XF](https://stacks.math.columbia.edu/tag/01XF)
* [Stacks Project, Tag 0415](https://stacks.math.columbia.edu/tag/0415)
* [Stacks Project, Tag 05Z2](https://stacks.math.columbia.edu/tag/05Z2)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Clause (1) of Stacks 09YB** for an algebraic space `X` over `S`: some object of the site
admits a surjective integral morphism from its representable algebraic space to `X`. -/
def ExistsIntegralSurjectiveSchemeCover (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∃ (W : BigFppfOver B S hS) (g : yoneda.obj W ⟶ X),
    IsSurjective B S hS g ∧ IsIntegralHom B S hS g

/-- **Clause (1) of Stacks 07V0** for an algebraic space `X` over `S`, restricted to a scheme
`W` of the site affine over `X` and to a quasi-coherent ideal sheaf on `W`, whose first
cohomology is read in the Zariski topology of `W`. -/
def SchemeAffineOverFirstZariskiCohomologyVanishing
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (W : BigFppfOver B S hS) (g : yoneda.obj W ⟶ X), IsAffineHom B S hS g →
    ∀ I : Subobject (SheafOfModules.unit
        ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf),
      (Subobject.underlying.obj I).IsQuasicoherent →
      IsZero (((SheafOfModules.evaluation
        ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf (op ⊤)).rightDerived 1).obj
          (Subobject.underlying.obj I))

/-- **An algebraic space as in Stacks 09YB with the vanishing of Stacks 07V0 is separated over
every affine object of the site.** This is the proof of Stacks 07V5 with the target left
general: the cover is affine, hence separated over the target, and the surjection descends. -/
theorem isSeparated_to_affine_of_existsIntegralSurjectiveSchemeCover
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXqc : IsQuasiCompactSpace B S hS X)
    (h09YB : ExistsIntegralSurjectiveSchemeCover B S hS X)
    (h07V0 : SchemeAffineOverFirstZariskiCohomologyVanishing B S hS X)
    (V : BigFppfOver B S hS) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (p : X ⟶ yoneda.obj V) :
    IsSeparated B S hS p := by
  obtain ⟨W, g, hgsurj, hgint⟩ := h09YB
  have hW : IsAlgebraicSpace B S hS (yoneda.obj W) := isAlgebraicSpace_yoneda B S hS W
  obtain ⟨hgaff, hgclosed⟩ :=
    (isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS hW hX g).1 hgint
  have hWqc : IsQuasiCompactSpace B S hS (yoneda.obj W) :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS hX hXqc
      (isQuasiCompact_of_universallyClosed B S hS hW hX g hgclosed)
  have hWcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj W) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hWqc
  have hWaff : IsAffine ((BigFppfOver.toScheme B S hS).obj W) :=
    Stacks.SerreCriterion.isAffine_of_forall_isZero_H1_ideal _ (h07V0 W g hgaff)
  have hcomp : IsSeparated B S hS (g ≫ p) := by
    have hsep := isSeparated_yoneda_map_of_isAffine B S hS (yoneda.preimage (g ≫ p)) hWaff hV
    rwa [yoneda.map_preimage] at hsep
  exact isSeparated_of_isSurjective_of_universallyClosed B S hS hW hX
    (isAlgebraicSpace_yoneda B S hS V) g p hgsurj hgclosed hcomp

namespace CohomologyVanishingSituation

variable (T : CohomologyVanishingSituation.{u, m}) (hterminal : IsTerminal T.base)
    (V : BigFppfOver T.site T.base T.containsBase)
    [IsAffine ((BigFppfOver.toScheme T.site T.base T.containsBase).obj V)]
    (e : Γ((BigFppfOver.toScheme T.site T.base T.containsBase).obj V, ⊤) ≃+*
      _root_.AlgebraicGeometry.Space.globalFunctions T.site T.base T.containsBase T.space.1)

/-- **Stacks 07V5.** In the situation of Stacks 07UY, the canonical morphism
`p : X ⟶ Spec Γ(X, 𝒪_X)` is separated, `Spec Γ(X, 𝒪_X)` being presented by an affine object `V`
of the site through a ring isomorphism `Γ(V, 𝒪_V) ≅ Γ(X, 𝒪_X)`. -/
@[stacks 07V5 "two inputs are carried as named hypotheses -- h09YB, clause (1) of Stacks 09YB,
and h07V0, clause (1) of Stacks 07V0 for a scheme of the site affine over X with its first
cohomology read in the Zariski topology of that scheme. IsTerminal T.base is inherited from the
signature of toSpecGlobalFunctions. See this file's implementation notes"]
theorem isSeparated_toSpecGlobalFunctions
    (h09YB : ExistsIntegralSurjectiveSchemeCover T.site T.base T.containsBase T.space.1)
    (h07V0 : SchemeAffineOverFirstZariskiCohomologyVanishing T.site T.base T.containsBase
      T.space.1) :
    IsSeparated T.site T.base T.containsBase
      (toSpecGlobalFunctions T hterminal V e).hom :=
  isSeparated_to_affine_of_existsIntegralSurjectiveSchemeCover T.site T.base T.containsBase
    T.space.2 T.quasiCompact h09YB h07V0 V inferInstance _

/-- **In the situation of Stacks 07UY the space `X` is a separated algebraic space.** This is
the conclusion the proof of Stacks 07V5 reaches, separatedness over the terminal scheme, which
is stronger than separatedness of the canonical morphism to `Spec Γ(X, 𝒪_X)`. -/
theorem isAbsolutelySeparated_of_existsIntegralSurjectiveSchemeCover
    (T' : CohomologyVanishingSituation.{u, m}) (hterm : IsTerminal T'.base)
    (W : BigFppfOver T'.site T'.base T'.containsBase)
    [hW : IsAffine ((BigFppfOver.toScheme T'.site T'.base T'.containsBase).obj W)]
    (ε : Γ((BigFppfOver.toScheme T'.site T'.base T'.containsBase).obj W, ⊤) ≃+*
      _root_.AlgebraicGeometry.Space.globalFunctions T'.site T'.base T'.containsBase T'.space.1)
    (h09YB : ExistsIntegralSurjectiveSchemeCover T'.site T'.base T'.containsBase T'.space.1)
    (h07V0 : SchemeAffineOverFirstZariskiCohomologyVanishing T'.site T'.base T'.containsBase
      T'.space.1) :
    IsAbsolutelySeparated T'.site T'.base T'.containsBase T'.containsTerminal T'.space.1 :=
  isAbsolutelySeparated_of_isSeparated_to_affine T'.site T'.base T'.containsBase
    T'.containsTerminal W hW (toSpecGlobalFunctions T' hterm W ε).hom
    (isSeparated_toSpecGlobalFunctions T' hterm W ε h09YB h07V0)

end CohomologyVanishingSituation

end AlgebraicGeometry.Space

end
