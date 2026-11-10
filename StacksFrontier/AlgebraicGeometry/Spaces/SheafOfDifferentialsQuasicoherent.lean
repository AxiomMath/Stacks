module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.CotangentSheafComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeTransport
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence
import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf of differentials of a morphism of algebraic spaces is quasi-coherent

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`.  Stacks 04CV asserts that
the sheaf of differentials `Ω_{X/Y}` of Stacks 04CT is a quasi-coherent `𝒪_X`-module on the
small étale site of `X`.

The proof below is the source's.  A surjective étale chart `V ⟶ Y` of the target lifts to a
commuting square

```
U --α--> V
|        |
p        q
v        v
X --f--> Y
```

whose chart `p : U ⟶ X` is again surjective and étale (Stacks 02X1); on that chart the
restriction of `Ω_{X/Y}` is the sheaf of differentials of `α` (Stacks 04CU), that sheaf is
quasi-coherent because the Zariski sheaf of relative differentials of a morphism of schemes is
(Stacks 08S2) and because the small-étale module associated to a quasi-coherent module on a
scheme is quasi-coherent (Stacks 03DV (2)), and quasi-coherence descends from a surjective
étale chart to the algebraic space (Stacks 03M0, conditions (1) and (2)).

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_representedAssociatedModule`: **the
  small-étale module on a represented algebraic space attached to a quasi-coherent module on
  its scheme is quasi-coherent.**  This is Stacks 03DV (2) for the scheme, carried along the
  equivalence of its small étale site with the small étale site of the algebraic space it
  represents.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_sheafOfDifferentials`: **Stacks 04CV**.

## Implementation notes

The proof uses four inputs, listed below under the names `hloc`, `ecomp`/`hecomp` and
`hschemeChart`, and all four are proved; none of them is quasi-coherence of a sheaf of
differentials, on a chart or anywhere else.  The
quasi-coherence in the proof is produced by the two theorems of this development named above,
`AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentials` and
`AlgebraicGeometry.Space.isQuasicoherentOnSite_representedAssociatedModule`.

* `hloc` is the étale-source localization `Ω_{X/Y}|_{U_étale} = Ω_{U/Y}` along an étale
  `a : U ⟶ X`, which is Stacks 03LP and Equation 03LQ together with Modules on Sites,
  Lemma 04BO.  The clause is proved in this development, as
  `AlgebraicGeometry.Space.sheafOfDifferentialsEtaleSourceLocalizationIso`, and
  `AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso` uses it directly.
* `ecomp` and `hecomp` are the étale-base comparison
  `(ψ ≫ b)^{-1}𝒪_Y = ψ^{-1}𝒪_V` under the structure maps, for an étale `b : V ⟶ Y`, which is
  the composition law of Stacks 03G8 together with the clause `b^{-1}𝒪_Y = 𝒪_V` of
  Stacks 03LV.  The comparison is
  `AlgebraicGeometry.Space.etaleBaseInverseImageStructureSheafIso` and its compatibility
  lemma.
* `hschemeChart` is the final sentence of Stacks 04CU, read through Stacks 04CS: for a morphism
  `α` of schemes of the big fppf site, the *spaces*-level sheaf of differentials of `α` — the
  sheafification on the small étale site of the presheaf of sectionwise Kähler differentials of
  `α^{-1}𝒪` — is the small-étale module associated to the Zariski sheaf of relative
  differentials `Ω_{U/V}` of Stacks 01US.  It is the theorem
  `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison` of
  `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeTransport.lean`.  Stacks 04CS
  itself is proved in the scheme's own spelling:
  `AlgebraicGeometry.SmallEtale.existsUnique_postcomp_associatedRelativeDifferentialsDerivation`
  gives the corepresentability, and
  `AlgebraicGeometry.SmallEtale.isIso_differentialsComparison_of_universal` the invertibility of
  `AlgebraicGeometry.SmallEtale.differentialsComparison` at a universal pair; the canonical
  isomorphism `(Ω_{U/V})^a ≅ Ω_{U_étale/V_étale}` is
  `AlgebraicGeometry.SmallEtale.differentialsIso` of
  `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDifferentialsIso.lean`, and
  the transport of that identification to the spaces-level sheaf of differentials — the
  scheme-level statement being about derivations annihilating the functions pulled back from
  *opens* of `V`, while `AlgebraicGeometry.Space.sheafOfDifferentials` is defined by its
  universal property among derivations relative to the inverse image `α⁻¹𝒪_{V}` on the small
  étale site — is carried out in
  `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeTransport.lean`.

`AlgebraicGeometry.Space.isQuasicoherentOnSite_representedAssociatedModule` is proved, and not
carried.  Its two halves are Stacks 03DV (2) on the small étale site of the scheme, which is
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent`, and
the invariance of quasi-coherence under an equivalence of ringed sites,
`Stacks.SheafOfModules.isQuasicoherentOnSite_reindex`, applied to
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`.  The instance that the latter asks
for — that the inverse of the equivalence is a dense subsite — is supplied by
`AlgebraicGeometry.Space.isDenseSubsite_representedSmallEtaleEquivalence_inverse` from the equality
of the two topologies, `AlgebraicGeometry.Space.representedSmallEtaleEquivalence_topology`.

The reindexing lemma has to be applied with its target topology given explicitly.  The
structure sheaf of the small étale site of an algebraic space arrives as
`AlgebraicGeometry.Space.RingedSite.ringSheaf` of
`AlgebraicGeometry.Space.smallEtaleRingedSite`, so its Grothendieck topology arrives as the
projection `.J`, which instance search does not unfold, and the continuity of the comparison
functor is then unreachable; naming `AlgebraicGeometry.Space.SmallEtale.topology` in the
argument `J'` fixes it, and the resulting statement is accepted at the goal because the two
spellings of the topology — and hence of the structure sheaf, by
`AlgebraicGeometry.Space.ringStructureSheaf_eq_ringSheaf` — are definitionally equal.  This is
the discipline that `AlgebraicGeometry.Space.SmallEtale.freeSliceIso` records.

The surjective étale chart is used through Stacks 03M0, conditions (1) and (2), rather than
through conditions (1) and (4): the identification of Stacks 04CU is stated for the pullback of
modules `a^*` of Stacks 03LU, and it is the pullback along an étale morphism, not the
restriction to a slice, that condition (2) tests.  The two are matched by
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, Equation 03LW.

## References

* [Stacks Project, Tag 04CV](https://stacks.math.columbia.edu/tag/04CV)
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT), the sheaf of
  differentials of a morphism of algebraic spaces.
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU), the identification
  `Ω_{X/Y}|_{U_étale} = Ω_{U/V}` on a square of étale charts.
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS), the comparison of the
  differentials of a morphism of schemes on its small Zariski and small étale sites.
* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2), quasi-coherence of the
  sheaf of relative differentials of a morphism of schemes.
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0), the characterizations
  of quasi-coherence on an algebraic space.
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV), quasi-coherence of the
  associated module on a small étale site.
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM), the local conditions of
  Stacks 03DL are intrinsic.
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1), the lift of a
  surjective étale chart along a morphism of algebraic spaces.
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW), the pullback of modules
  along an étale morphism as étale restriction.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Inducing the small étale topology of a represented algebraic space back along the inverse of
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence` returns the small étale topology of
the underlying scheme. -/
private theorem inducedTopology_representedSmallEtaleEquivalence_inverse
    (U : BigFppfOver B S hS) :
    (representedSmallEtaleEquivalence B S hS U).inverse.inducedTopology
        (SmallEtale.topology B S hS (yoneda.obj U)) =
      AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property :=
  inducedTopology_symm_of_equivalence (representedSmallEtaleEquivalence B S hS U) _ _
    (representedSmallEtaleEquivalence_topology B S hS U)

/-- The inverse of the equivalence between the small étale site of a scheme of the big fppf site
and the small étale site of the algebraic space it represents is a dense subsite: the two
topologies correspond, by
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence_topology`. -/
instance isDenseSubsite_representedSmallEtaleEquivalence_inverse (U : BigFppfOver B S hS) :
    Functor.IsDenseSubsite
      (AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
      (SmallEtale.topology B S hS (yoneda.obj U))
      (representedSmallEtaleEquivalence B S hS U).inverse := by
  rw [← inducedTopology_representedSmallEtaleEquivalence_inverse B S hS U]
  infer_instance

/-- **The small-étale module attached to a quasi-coherent module on a scheme of the big fppf site
is quasi-coherent on the small étale site of the algebraic space the scheme represents.**

The associated module of the scheme's own small étale site is quasi-coherent there by
Stacks 03DV (2), and quasi-coherence is invariant under the equivalence of that site with the
small étale site of the represented algebraic space, the two structure sheaves being equal. -/
theorem isQuasicoherentOnSite_representedAssociatedModule
    (U : BigFppfOver B S hS) (hU : IsAlgebraicSpace B S hS (yoneda.obj U))
    (M : ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (hM : SheafOfModules.IsQuasicoherent M) :
    ((representedAssociatedModule B S hS U hU).obj M).IsQuasicoherentOnSite := by
  have h : ((AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj M).IsQuasicoherentOnSite :=
    AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property M hM
  have key := Stacks.SheafOfModules.isQuasicoherentOnSite_reindex
    (J' := SmallEtale.topology B S hS (yoneda.obj U))
    (representedSmallEtaleEquivalence B S hS U)
    (AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    ((AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj M)
  exact key

/-- **Stacks 04CV.**  The sheaf of differentials `Ω_{X/Y}` of a morphism `f : X ⟶ Y` of
algebraic spaces over a scheme `S` is a quasi-coherent `𝒪_X`-module on the small étale site
of `X`.

The proof follows the source.  An atlas `q : V ⟶ Y` of the target lifts, by Stacks 02X1, to a
surjective étale chart `p : U ⟶ X` of the source together with a morphism `α : U ⟶ V` of
schemes making the square commute.  The identification of Stacks 04CU then reads the pullback
of `Ω_{X/Y}` along `p` as the sheaf of differentials of `α`, which
`AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison` identifies with the small-étale
module associated to the Zariski sheaf of
relative differentials of `α`; that module is quasi-coherent because `Ω_{U/V}` is
(Stacks 08S2) and because the associated module of a quasi-coherent module is quasi-coherent
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_representedAssociatedModule`).  Finally
Stacks 03M0, conditions (1) and (2), returns quasi-coherence on `X` from quasi-coherence of the
pullback along one surjective étale chart, the pullback of modules and étale restriction being
matched by Equation 03LW.

Nothing is carried: the two clauses of Stacks 04CU proper are used through
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso`, and the final sentence,
read through Stacks 04CS, through
`AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison`; see the implementation
notes. -/
@[stacks 04CV]
theorem isQuasicoherentOnSite_sheafOfDifferentials
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (sheafOfDifferentials B S hS f).IsQuasicoherentOnSite := by
  obtain ⟨V, q, hqS, hqE⟩ := Y.property.exists_atlas
  obtain ⟨U, p, α, hdiag, hpS, hpE⟩ :=
    exists_surjective_etale_presentation_lift B S hS X.property Y.property f.hom V q hqS hqE
  set a : schemeSpace U ⟶ X := ObjectProperty.homMk p
  set bb : schemeSpace V ⟶ Y := ObjectProperty.homMk q
  set ψ : schemeSpace U ⟶ schemeSpace V := schemeSpaceMap α
  have haE : IsEtale B S hS a.hom := isEtale_of_presheaf_etale B S hS hpE
  have hbE : IsEtale B S hS bb.hom := isEtale_of_presheaf_etale B S hS hqE
  have haS : IsSurjective B S hS a.hom := isSurjective_of_presheafSurjective B S hS p hpS
  have hcomm : a ≫ f = ψ ≫ bb := ObjectProperty.hom_ext _ hdiag
  have iso1 := sheafOfDifferentialsEtaleLocalizationIso B S hS f a ψ bb haE hbE hcomm
  obtain ⟨echart⟩ := sheafOfDifferentialsSchemeComparison B S hS U V α
  have hqc : (sheafOfDifferentials B S hS ψ).IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso echart.symm
      (isQuasicoherentOnSite_representedAssociatedModule B S hS U _ _
        (Scheme.Hom.isQuasicoherent_relativeDifferentials _))
  refine (isQuasicoherentOnSite_iff_exists_etale_surjective B S hS
    (sheafOfDifferentials B S hS f)).2 ⟨schemeSpace U, a, haE, haS, ?_⟩
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((modulePullbackIsoEtaleModulePullback B S hS a haE).app (sheafOfDifferentials B S hS f))
    (SheafOfModules.IsQuasicoherentOnSite.of_iso iso1.symm hqc)

end AlgebraicGeometry.Space

end
