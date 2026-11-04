module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.RegularEpi
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.SubgroupoidDivisionDescent
public import StacksFrontier.AlgebraicGeometry.Groupoids.FullyFaithfulRestriction
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivalenceRelationGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivalenceRelationQuasiFiniteSlice
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasiSplittingAffineLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasiSplittingEtaleScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.PreEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Presheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Restriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Sheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SplittingSituations
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValued
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafFppfOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.CoveringMap
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationsOverSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.LocallySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Stability
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalMonomorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
import all StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FlatRelationQuotient

/-!
# The final bootstrap theorem for algebraic spaces

An fppf sheaf on the big fppf site of a scheme `S` is an algebraic space over `S` as soon as it
is the quotient of a flat, locally finitely presented equivalence relation, or as soon as it
carries a surjective, flat, locally finitely presented presentation by an algebraic space.  This
is Stacks 04S6, Theorem 80.10.1 of the source's Bootstrap chapter, in all six of its forms.

## Main results

All in the namespace `AlgebraicGeometry.Bootstrap04S6`:

* `isAlgebraicSpace_quotient_groupoidInAlgebraicSpaces` is condition (1), the quotient criterion
  for a groupoid in algebraic spaces.
* Condition (2), the groupoid-scheme version, is `isAlgebraicSpace_quotientSheaf_groupoidScheme`.
* `isAlgebraicSpace_of_representable_surjective_flat_locallyOfFinitePresentation` and
  `isAlgebraicSpace_of_representable_surjective_flat_locallyOfFinitePresentation_scheme` are
  conditions (3) and (4), the criteria with a presentation representable by algebraic spaces.
* `isAlgebraicSpace_of_representableDiagonal_surjective_flat_locallyOfFinitePresentation` and
  `isAlgebraicSpace_of_representableDiagonal_surjective_flat_locallyOfFinitePresentation_scheme`
  are conditions (5) and (6), the criteria with a representable diagonal.
* `isAlgebraicSpace_quotient_preRelation` is condition (1) restated for an equivalence relation
  of algebraic spaces rather than for a groupoid.

## Implementation notes

Conditions (1) and (2) are stated for the displayed quotient sheaf itself, since that is the
object whose algebraicity is asserted.  In condition (2) the object scheme must belong to the
chosen bounded site, as every scheme does in the source's full big site; in condition (1) the
groupoid is allowed over an arbitrary algebraic space over `S`, which generalizes the source's
base `S`.  Flatness and local finite presentation in conditions (5) and (6) are tested on every
scheme-valued base change, and representability of the resulting spaces follows from
representability of the diagonal.

The reductions are the source's.  Conditions (5) and (3) reduce to (1) by replacing the
presentation `f : X ⟶ F` with its kernel pair `R = X ×_F X`, which is an equivalence relation
whose quotient sheaf is `F` because `f` is a surjection of fppf sheaves (Stacks 04S1).
Condition (1) reduces to (2) by restricting along an étale scheme atlas of the object space,
which does not change the quotient (Stacks 046P).  Condition (2) is the substance: Stacks 0489
replaces the relation by a locally quasi-finite one, Stacks 04S0 produces an affine étale
neighbourhood over which the relation is quasi-split, Stacks 04S4 divides by the quasi-splitting
to leave a groupoid whose identity is an open immersion, such a groupoid has étale source and
target, and Stacks 02WW makes its quotient an algebraic space.  The passage from the local
quotients back to `U/R` is by open immersions (Stacks 02WU, Stacks 046M) and the coproduct and
open-cover criteria Stacks 02WQ and Stacks 02WR.

## References

* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 0489](https://stacks.math.columbia.edu/tag/0489)
* [Stacks Project, Tag 04S0](https://stacks.math.columbia.edu/tag/04S0)
* [Stacks Project, Tag 04S4](https://stacks.math.columbia.edu/tag/04S4)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Bootstrap04S6

attribute [local instance] schemeBelowClosedIso

attribute [local instance] schemeBelowClosedCospan

attribute [local instance] schemeBelowPreservesCospan

attribute [local instance] bigFppfOverHasPullbacks

attribute [local instance] bigFppfOverHasBinaryProducts

private theorem isRepresentableByAlgebraicSpaces_of_relativelyRepresentable
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {X Y : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f) :
    AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces site S hS f := by
  intro U ξ
  let e := (hf.isPullback ξ).flip.isoPullback
  exact AlgebraicGeometry.isAlgebraicSpace_of_relativelyRepresentable site S hS e.inv
    (Functor.relativelyRepresentable.of_isIso yoneda e.inv)
    (AlgebraicGeometry.isAlgebraicSpace_yoneda site S hS (hf.pullback ξ))

attribute [local instance] bigFppfOverToSchemePreservesPullbacks

private theorem chartProperty_pullback_of_scheme_baseChanges
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    (P : MorphismProperty Scheme.{u})
    (hP : AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget P)
    {F X Y : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ F) (g : Y ⟶ F)
    (hY : AlgebraicGeometry.IsAlgebraicSpace site S hS Y)
    (hrep : AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces site S hS f)
    (hf : ∀ (V : AlgebraicGeometry.BigFppfOver site S hS) (b : yoneda.obj V ⟶ F),
      AlgebraicGeometry.Space.HoldsOnEveryEtaleChart site S hS P (pullback.fst b f)) :
    AlgebraicGeometry.Space.HoldsOnEveryEtaleChart site S hS P (pullback.fst g f) := by
  let R := pullback g f
  have hR := AlgebraicGeometry.Space.isAlgebraicSpace_pullback_of_isRepresentableByAlgebraicSpaces
    site S hS f g hrep hY
  obtain ⟨V, b, hbSurj, hbEtale⟩ := hY.exists_atlas
  let T := pullback (b ≫ g) f
  have hT : AlgebraicGeometry.IsAlgebraicSpace site S hS T := hrep V (b ≫ g)
  let z : T ⟶ R := pullback.lift
    (pullback.fst (b ≫ g) f ≫ b) (pullback.snd (b ≫ g) f) (by
      rw [Category.assoc, pullback.condition])
  have hz : IsPullback (pullback.fst (b ≫ g) f) z b (pullback.fst g f) := by
    refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback g f)
    · simpa only [z, pullback.lift_snd] using IsPullback.of_hasPullback (b ≫ g) f
    · simp only [z, pullback.lift_fst]
  let PE := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme site S hS)
  let PS := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme site S hS)
  have hzEtale : PE.presheaf z :=
    (MorphismProperty.relative_isStableUnderBaseChange PE).of_isPullback hz hbEtale
  have hzSurj : PS.presheaf z :=
    (MorphismProperty.relative_isStableUnderBaseChange PS).of_isPullback hz hbSurj
  obtain ⟨U, V', a, b', k, haEtale, hb'Etale, haSurj, hw, hk⟩ :=
    (AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_surjectiveChart site S hS P hP hT
      (AlgebraicGeometry.isAlgebraicSpace_yoneda site S hS V) _).mp (hf V (b ≫ g))
  apply (AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_surjectiveChart
    site S hS P hP hR hY _).mpr
  let : MorphismProperty.IsStableUnderComposition
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    ⟨fun l k _ _ => Etale.etale_comp l k⟩
  let : MorphismProperty.IsStableUnderComposition
      (@Surjective.{u} : MorphismProperty Scheme.{u}) :=
    ⟨fun _ k _ _ => inferInstance⟩
  let : PE.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  let : PS.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  refine ⟨U, V', a ≫ z, b' ≫ b, k,
    MorphismProperty.comp_mem PE.presheaf _ _ haEtale hzEtale,
    MorphismProperty.comp_mem PE.presheaf _ _ hb'Etale hbEtale,
    MorphismProperty.comp_mem PS.presheaf _ _ haSurj hzSurj, ?_, hk⟩
  calc
    yoneda.map k ≫ (b' ≫ b) = a ≫ pullback.fst (b ≫ g) f ≫ b := by
      rw [← Category.assoc, hw, Category.assoc]
    _ = (a ≫ z) ≫ pullback.fst g f := by
      dsimp [z]
      simp only [Category.assoc, pullback.lift_fst]

private theorem kernelPair_isAlgebraicSpace
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {F U : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (f : U ⟶ F) (hU : AlgebraicGeometry.IsAlgebraicSpace site S hS U)
    (hrep : AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces site S hS f) :
    AlgebraicGeometry.IsAlgebraicSpace site S hS (pullback f f) :=
  AlgebraicGeometry.Space.isAlgebraicSpace_pullback_of_isRepresentableByAlgebraicSpaces
    site S hS f f hrep hU

private def terminalSiteObject
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S) :
    AlgebraicGeometry.BigFppfOver site S hS :=
  Over.mk (𝟙 (site.obj hS))

private noncomputable def terminalSiteObject_isTerminal
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S) :
    IsTerminal (terminalSiteObject site S hS) :=
  Over.mkIdTerminal

private noncomputable def uniqueMapToTerminalYoneda
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    (P : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u) :
    P ⟶ yoneda.obj (terminalSiteObject site S hS) where
  app X := ↾ fun _ : P.obj X =>
    (terminalSiteObject_isTerminal site S hS).from X.unop
  naturality _ _ _ := ConcreteCategory.hom_ext _ _ fun _ =>
    (terminalSiteObject_isTerminal site S hS).hom_ext _ _

private theorem hom_ext_toTerminalYoneda
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {P : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (a b : P ⟶ yoneda.obj (terminalSiteObject site S hS)) : a = b := by
  ext X x
  exact (terminalSiteObject_isTerminal site S hS).hom_ext _ _

private noncomputable def kernelPairOver
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {F U : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (f : U ⟶ F) (_hU : AlgebraicGeometry.IsAlgebraicSpace site S hS U)
    (_hrep : AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces site S hS f) :
    Over (yoneda.obj (terminalSiteObject site S hS)) :=
  Over.mk (uniqueMapToTerminalYoneda site S hS (pullback f f))

private noncomputable def kernelPairUOver
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {F U : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (_f : U ⟶ F) (_hU : AlgebraicGeometry.IsAlgebraicSpace site S hS U) :
    Over (yoneda.obj (terminalSiteObject site S hS)) :=
  Over.mk (uniqueMapToTerminalYoneda site S hS U)

private noncomputable def kernelPairFirst
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {F U : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (f : U ⟶ F) (hU : AlgebraicGeometry.IsAlgebraicSpace site S hS U)
    (hrep : AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces site S hS f) :
    kernelPairOver site S hS f hU hrep ⟶ kernelPairUOver site S hS f hU :=
  Over.homMk (pullback.fst f f) (hom_ext_toTerminalYoneda site S hS _ _)

private noncomputable def kernelPairSecond
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {F U : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (f : U ⟶ F) (hU : AlgebraicGeometry.IsAlgebraicSpace site S hS U)
    (hrep : AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces site S hS f) :
    kernelPairOver site S hS f hU hrep ⟶ kernelPairUOver site S hS f hU :=
  Over.homMk (pullback.snd f f) (hom_ext_toTerminalYoneda site S hS _ _)

private noncomputable def kernelPairPreRelation
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {F U : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (f : U ⟶ F) (hU : AlgebraicGeometry.IsAlgebraicSpace site S hS U)
    (hrep : AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces site S hS f) :
    AlgebraicGeometry.Space.PreRelation (kernelPairOver site S hS f hU hrep)
      (kernelPairUOver site S hS f hU) :=
  prod.lift (kernelPairFirst site S hS f hU hrep)
    (kernelPairSecond site S hS f hU hrep)

private theorem kernelPairPreRelation_target
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {F U : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (f : U ⟶ F) (hU : AlgebraicGeometry.IsAlgebraicSpace site S hS U)
    (hrep : AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces site S hS f) :
    (kernelPairPreRelation site S hS f hU hrep).target.left = pullback.fst f f :=
  congrArg Over.Hom.left (prod.lift_fst _ _)

private theorem kernelPairPreRelation_source
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {F U : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (f : U ⟶ F) (hU : AlgebraicGeometry.IsAlgebraicSpace site S hS U)
    (hrep : AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces site S hS f) :
    (kernelPairPreRelation site S hS f hU hrep).source.left = pullback.snd f f :=
  congrArg Over.Hom.left (prod.lift_snd _ _)

private theorem kernelPairPreRelation_mono
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {F U : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (f : U ⟶ F) (hU : AlgebraicGeometry.IsAlgebraicSpace site S hS U)
    (hrep : AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces site S hS f) :
    Mono (kernelPairPreRelation site S hS f hU hrep) := by
  constructor
  intro X g h hgh
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hfst := congrArg (fun k => k ≫ prod.fst) hgh
    have hfst' := congrArg (fun k => k.left) hfst
    change g.left ≫ (kernelPairPreRelation site S hS f hU hrep).target.left =
      h.left ≫ (kernelPairPreRelation site S hS f hU hrep).target.left at hfst'
    rwa [kernelPairPreRelation_target] at hfst'
  · have hsnd := congrArg (fun k => k ≫ prod.snd) hgh
    have hsnd' := congrArg (fun k => k.left) hsnd
    change g.left ≫ (kernelPairPreRelation site S hS f hU hrep).source.left =
      h.left ≫ (kernelPairPreRelation site S hS f hU hrep).source.left at hsnd'
    rwa [kernelPairPreRelation_source] at hsnd'

private theorem kernelPairPreRelation_of_comp_eq
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {F U : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (f : U ⟶ F) (hU : AlgebraicGeometry.IsAlgebraicSpace site S hS U)
    (hrep : AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces site S hS f)
    (T : AlgebraicGeometry.BigFppfOver site S hS)
    (b : yoneda.obj T ⟶ yoneda.obj (terminalSiteObject site S hS))
    (x y : { g : yoneda.obj T ⟶ U //
      g ≫ (kernelPairUOver site S hS f hU).hom = b })
    (hxy : x.1 ≫ f = y.1 ≫ f) :
    (kernelPairPreRelation site S hS f hU hrep).Rel b x y := by
  let r := pullback.lift x.1 y.1 hxy
  let j := kernelPairPreRelation site S hS f hU hrep
  refine ⟨⟨r, ?_⟩, ?_, ?_⟩
  · exact hom_ext_toTerminalYoneda site S hS _ _
  · change r ≫ j.target.left = x.1
    rw [kernelPairPreRelation_target]
    exact pullback.lift_fst _ _ _
  · change r ≫ j.source.left = y.1
    rw [kernelPairPreRelation_source]
    exact pullback.lift_snd _ _ _

private theorem comp_eq_of_kernelPairPreRelation_rel
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {F U : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (f : U ⟶ F) (hU : AlgebraicGeometry.IsAlgebraicSpace site S hS U)
    (hrep : AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces site S hS f)
    (T : AlgebraicGeometry.BigFppfOver site S hS)
    (b : yoneda.obj T ⟶ yoneda.obj (terminalSiteObject site S hS))
    {x y : { g : yoneda.obj T ⟶ U //
      g ≫ (kernelPairUOver site S hS f hU).hom = b }}
    (hxy : (kernelPairPreRelation site S hS f hU hrep).Rel b x y) :
    x.1 ≫ f = y.1 ≫ f := by
  obtain ⟨r, hrx, hry⟩ := hxy
  have hkernel :
      (kernelPairPreRelation site S hS f hU hrep).target.left ≫ f =
        (kernelPairPreRelation site S hS f hU hrep).source.left ≫ f := by
    rw [kernelPairPreRelation_target, kernelPairPreRelation_source]
    exact pullback.condition
  calc
    _ = (r.1 ≫ (kernelPairPreRelation site S hS f hU hrep).target.left) ≫ f :=
      congrArg (fun k => k ≫ f) hrx.symm
    _ = (r.1 ≫ (kernelPairPreRelation site S hS f hU hrep).source.left) ≫ f :=
      (Category.assoc _ _ _).trans ((congrArg
        (fun k => r.1 ≫ k) hkernel).trans (Category.assoc _ _ _).symm)
    _ = _ := congrArg (fun k => k ≫ f) hry

private theorem kernelPairPreRelation_isPreEquivalenceRelation
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {F U : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (f : U ⟶ F) (hU : AlgebraicGeometry.IsAlgebraicSpace site S hS U)
    (hrep : AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces site S hS f) :
    AlgebraicGeometry.Space.IsPreEquivalenceRelation
      (kernelPairPreRelation site S hS f hU hrep) := by
  intro T b
  refine ⟨fun x => kernelPairPreRelation_of_comp_eq site S hS f hU hrep T b x x rfl,
    fun hxy => ?_, fun hxy hyz => ?_⟩
  · exact kernelPairPreRelation_of_comp_eq site S hS f hU hrep T b _ _
      (comp_eq_of_kernelPairPreRelation_rel site S hS f hU hrep T b hxy).symm
  · exact kernelPairPreRelation_of_comp_eq site S hS f hU hrep T b _ _
      ((comp_eq_of_kernelPairPreRelation_rel site S hS f hU hrep T b hxy).trans
        (comp_eq_of_kernelPairPreRelation_rel site S hS f hU hrep T b hyz))

private theorem kernelPairPreRelation_isEquivalenceRelation
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {F U : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (f : U ⟶ F) (hU : AlgebraicGeometry.IsAlgebraicSpace site S hS U)
    (hrep : AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces site S hS f) :
    IsEquivalenceRelation
      (kernelPairPreRelation site S hS f hU hrep).target
      (kernelPairPreRelation site S hS f hU hrep).source :=
  (AlgebraicGeometry.Space.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation _).2
    ⟨kernelPairPreRelation_mono site S hS f hU hrep,
      kernelPairPreRelation_isPreEquivalenceRelation site S hS f hU hrep⟩

private theorem isIso_of_mono_locallySurjective
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    {P Q : Cᵒᵖ ⥤ Type u} (m : P ⟶ Q)
    (hP : Presheaf.IsSheaf J P) (hQ : Presheaf.IsSheaf J Q)
    [Mono m] [Presheaf.IsLocallySurjective J m] : IsIso m := by
  let m' : (⟨P, hP⟩ : Sheaf J (Type u)) ⟶ ⟨Q, hQ⟩ := ⟨m⟩
  have : IsIso m' := (Sheaf.isLocallyBijective_iff_isIso m').mp
    ⟨Presheaf.isLocallyInjective_of_injective J m fun X =>
      (mono_iff_injective (m.app X)).mp inferInstance, inferInstance⟩
  exact (inferInstance : IsIso ((sheafToPresheaf J (Type u)).map m'))

private theorem quotient_kernelPair_isPullback
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)]
    {F U : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (f : U ⟶ F) (hU : AlgebraicGeometry.IsAlgebraicSpace site S hS U)
    (hrep : AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces site S hS f)
    (hQ : AlgebraicGeometry.IsAlgebraicSpace site S hS
      (AlgebraicGeometry.Space.quotientSheaf (kernelPairPreRelation site S hS f hU hrep)).obj) :
    let q := AlgebraicGeometry.Space.toQuotientSheaf (kernelPairPreRelation site S hS f hU hrep)
    IsPullback (pullback.fst f f) (pullback.snd f f) q q := by
  let j := kernelPairPreRelation site S hS f hU hrep
  let q := AlgebraicGeometry.Space.toQuotientSheaf j
  have hw : pullback.fst f f ≫ q = pullback.snd f f ≫ q := by
    have h := AlgebraicGeometry.Space.target_toQuotientSheaf_eq_source j
    rwa [kernelPairPreRelation_target, kernelPairPreRelation_source] at h
  let m : pullback f f ⟶ pullback q q :=
    pullback.lift (pullback.snd f f) (pullback.fst f f) hw.symm
  have hmfst : m ≫ pullback.fst q q = pullback.snd f f := pullback.lift_fst _ _ _
  have hmsnd : m ≫ pullback.snd q q = pullback.fst f f := pullback.lift_snd _ _ _
  have hm : Mono m := by
    constructor
    intro Z a b hab
    apply pullback.hom_ext
    · have h := congrArg (fun k => k ≫ pullback.snd q q) hab
      simp only [Category.assoc, hmsnd] at h
      exact h
    · have h := congrArg (fun k => k ≫ pullback.fst q q) hab
      simp only [Category.assoc, hmfst] at h
      exact h
  have hloc : Presheaf.IsLocallySurjective
      (AlgebraicGeometry.BigFppfOver.topology site S hS) m := by
    have h := AlgebraicGeometry.Space.isLocallySurjective_relationToQuotientPullback j
      (kernelPairPreRelation_isPreEquivalenceRelation site S hS f hU hrep)
    have hmap : m = pullback.lift j.source.left j.target.left
        (AlgebraicGeometry.Space.target_toQuotientSheaf_eq_source j).symm :=
      pullback.hom_ext
        (hmfst.trans
          (((kernelPairPreRelation_source site S hS f hU hrep).symm).trans
            (pullback.lift_fst _ _ _).symm))
        (hmsnd.trans
          (((kernelPairPreRelation_target site S hS f hU hrep).symm).trans
            (pullback.lift_snd _ _ _).symm))
    rwa [hmap]
  let q' : (⟨U, hU⟩ : AlgebraicGeometry.AlgebraicSpaces site S hS) ⟶ ⟨_, hQ⟩ :=
    ObjectProperty.homMk q
  have hQQ : AlgebraicGeometry.IsAlgebraicSpace site S hS (pullback q q) :=
    (AlgebraicGeometry.AlgebraicSpaces.fiberProduct site S hS q' q').property
  have hmi : IsIso m := isIso_of_mono_locallySurjective _ m
    (kernelPair_isAlgebraicSpace site S hS f hU hrep).isSheaf hQQ.isSheaf
  exact (IsPullback.of_iso_pullback ⟨hw.symm⟩ (@asIso _ _ _ _ m hmi)
    hmfst hmsnd).flip

open Cardinal TopologicalSpace

private theorem isAlgebraicSpace_quotient_of_siteRelation
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)]
    {base : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u} {R U : Over base}
    (jA : AlgebraicGeometry.Space.PreRelation R U)
    {Rs Us : AlgebraicGeometry.BigFppfOver site S hS} (ts ss : Rs ⟶ Us)
    (eR : R.left ≅ yoneda.obj Rs) (eU : U.left ≅ yoneda.obj Us)
    (ht : jA.target.left ≫ eU.hom = eR.hom ≫ yoneda.map ts)
    (hs : jA.source.left ≫ eU.hom = eR.hom ≫ yoneda.map ss)
    (h : AlgebraicGeometry.IsAlgebraicSpace site S hS
      (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
        (Over.post site.inclusion)
        (prod.lift ((Over.post site.inclusion).map ts)
          ((Over.post site.inclusion).map ss))).obj) :
    AlgebraicGeometry.IsAlgebraicSpace site S hS
      (AlgebraicGeometry.Space.quotientSheaf jA).obj := by
  let F := Over.post (X := site.obj hS) site.inclusion
  let jS : Stacks.Groupoids.PreRelation (F.obj Rs) (F.obj Us) :=
    prod.lift (F.map ts) (F.map ss)
  have htgt : jS.target = F.map ts := prod.lift_fst _ _
  have hsrc : jS.source = F.map ss := prod.lift_snd _ _
  have hnt : Stacks.Groupoids.targetMap F jS ≫ (postPointsIso site S hS Us).hom =
      (postPointsIso site S hS Rs).hom ≫ yoneda.map ts := by
    rw [show Stacks.Groupoids.targetMap F jS =
      F.op.whiskerLeft (yoneda.map (F.map ts)) by rw [← htgt]]
    exact postPointsIso_hom_naturality site S hS ts
  have hns : Stacks.Groupoids.sourceMap F jS ≫ (postPointsIso site S hS Us).hom =
      (postPointsIso site S hS Rs).hom ≫ yoneda.map ss := by
    rw [show Stacks.Groupoids.sourceMap F jS =
      F.op.whiskerLeft (yoneda.map (F.map ss)) by rw [← hsrc]]
    exact postPointsIso_hom_naturality site S hS ss
  let e : AlgebraicGeometry.Space.quotientPresheaf jA ≅ Stacks.Groupoids.quotientPresheaf F jS :=
    coequalizerIsoOfIso _ _ (yoneda.map ts) (yoneda.map ss) eR eU ht hs ≪≫
      coequalizerIsoOfIso (yoneda.map ts) (yoneda.map ss)
          (Stacks.Groupoids.targetMap F jS) (Stacks.Groupoids.sourceMap F jS)
          (postPointsIso site S hS Rs).symm (postPointsIso site S hS Us).symm
          (comp_inv_eq_inv_comp hnt) (comp_inv_eq_inv_comp hns) ≪≫
        coequalizerSwapIso _ _
  exact isAlgebraicSpace_of_iso site S hS
    ((sheafToPresheaf _ _).mapIso
      ((presheafToSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)).mapIso e)) h

private theorem isAlgebraicSpace_quotient_of_restrict
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)]
    {base : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u} {R U U' : Over base}
    (j : AlgebraicGeometry.Space.PreRelation R U) (g : U' ⟶ U)
    (hj : AlgebraicGeometry.Space.IsPreEquivalenceRelation j)
    (hg : Presheaf.IsLocallySurjective
      (AlgebraicGeometry.BigFppfOver.topology site S hS) g.left)
    (hU : AlgebraicGeometry.IsAlgebraicSpace site S hS U.left)
    (hU' : AlgebraicGeometry.IsAlgebraicSpace site S hS U'.left)
    (h : AlgebraicGeometry.IsAlgebraicSpace site S hS
      (AlgebraicGeometry.Space.quotientSheaf
        (AlgebraicGeometry.Space.PreRelation.restrict j g)).obj) :
    AlgebraicGeometry.IsAlgebraicSpace site S hS (AlgebraicGeometry.Space.quotientSheaf j).obj := by
  let q := AlgebraicGeometry.Space.restrictQuotientSheafMap j g
  let : IsIso q := AlgebraicGeometry.Space.restrictQuotientSheafMap_isIso j g hj hg
    hU.isSheaf hU'.isSheaf
  exact isAlgebraicSpace_of_iso site S hS
    ((sheafToPresheaf _ _).mapIso (asIso q)).symm h

/-- The underlying presheaf of a product in the slice of presheaves over an algebraic space
is an algebraic space, being the presheaf fibre product of the two factors. -/
private theorem isAlgebraicSpace_over_prod_left
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {base : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (hbase : AlgebraicGeometry.IsAlgebraicSpace site S hS base) (X Y : Over base)
    (hX : AlgebraicGeometry.IsAlgebraicSpace site S hS X.left)
    (hY : AlgebraicGeometry.IsAlgebraicSpace site S hS Y.left) :
    AlgebraicGeometry.IsAlgebraicSpace site S hS (X ⨯ Y : Over base).left :=
  isAlgebraicSpace_of_iso site S hS (isPullback_over_prod X Y).isoPullback
    (AlgebraicGeometry.isAlgebraicSpace_pullback site S hS X.hom Y.hom hX hY hbase)

/-- The underlying presheaf of a fibre product in the slice of presheaves over an algebraic
space is an algebraic space: the forgetful functor to presheaves preserves it. -/
private theorem isAlgebraicSpace_over_pullback_left
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {base : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    {X Y Z : Over base} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hX : AlgebraicGeometry.IsAlgebraicSpace site S hS X.left)
    (hY : AlgebraicGeometry.IsAlgebraicSpace site S hS Y.left)
    (hZ : AlgebraicGeometry.IsAlgebraicSpace site S hS Z.left) :
    AlgebraicGeometry.IsAlgebraicSpace site S hS (pullback f g).left :=
  isAlgebraicSpace_of_iso site S hS
    ((IsPullback.of_hasPullback f g).map (Over.forget base)).isoPullback
    (AlgebraicGeometry.isAlgebraicSpace_pullback site S hS f.left g.left hX hY hZ)

/-- **Stacks 0AMM read on presheaves.** A property of morphisms of schemes which is étale
local on the source and target and stable under base change passes along an arbitrary
cartesian square of presheaves whose four corners are algebraic spaces. -/
private theorem chartProperty_of_isPullback
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    (P : MorphismProperty Scheme.{u})
    (hP : AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget P)
    [P.IsStableUnderBaseChange]
    {W X Y Z : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (hW : AlgebraicGeometry.IsAlgebraicSpace site S hS W)
    (hX : AlgebraicGeometry.IsAlgebraicSpace site S hS X)
    (hY : AlgebraicGeometry.IsAlgebraicSpace site S hS Y)
    (hZ : AlgebraicGeometry.IsAlgebraicSpace site S hS Z)
    {a : W ⟶ X} {b : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g)
    (hf : AlgebraicGeometry.Space.HoldsOnEveryEtaleChart site S hS P f) :
    AlgebraicGeometry.Space.HoldsOnEveryEtaleChart site S hS P b := by
  let Q : ObjectProperty ((AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u) :=
    AlgebraicGeometry.IsAlgebraicSpace site S hS
  have h' : IsPullback (ObjectProperty.homMk a : (⟨W, hW⟩ : Q.FullSubcategory) ⟶ ⟨X, hX⟩)
      (ObjectProperty.homMk b : (⟨W, hW⟩ : Q.FullSubcategory) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : Q.FullSubcategory) ⟶ ⟨Z, hZ⟩)
      (ObjectProperty.homMk g : (⟨Y, hY⟩ : Q.FullSubcategory) ⟶ ⟨Z, hZ⟩) :=
    IsPullback.of_map Q.ι (ObjectProperty.hom_ext _ h.w) h
  exact (AlgebraicGeometry.Space.holdsOnEveryEtaleChart_isStableUnderBaseChange
    site S hS P hP).of_isPullback h' hf

/-- A property stable under base change and composition passes to the leg `m` of a pullback
square over `pullback a g ⟶ U` whose base is the composite of `pullback.fst a g` and `b`, when
it holds for `b` and for the restricting morphism `g`. -/
private theorem algSpace_property_of_isPullback_pullback_fst_comp
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    (P : MorphismProperty Scheme.{u})
    (hP : AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget P)
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    {base : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u} {R U U' W : Over base}
    (hR : AlgebraicGeometry.IsAlgebraicSpace site S hS R.left)
    (hU : AlgebraicGeometry.IsAlgebraicSpace site S hS U.left)
    (hU' : AlgebraicGeometry.IsAlgebraicSpace site S hS U'.left)
    (hW : AlgebraicGeometry.IsAlgebraicSpace site S hS W.left)
    (a b : R ⟶ U) (g : U' ⟶ U) {m : W ⟶ U'}
    (hk : ∃ k, IsPullback k m (pullback.fst a g ≫ b) g)
    (hb : AlgebraicGeometry.Space.HoldsOnEveryEtaleChart site S hS P b.left)
    (hg : AlgebraicGeometry.Space.HoldsOnEveryEtaleChart site S hS P g.left) :
    AlgebraicGeometry.Space.HoldsOnEveryEtaleChart site S hS P m.left := by
  obtain ⟨k, hk⟩ := hk
  have hPB : AlgebraicGeometry.IsAlgebraicSpace site S hS (pullback a g).left :=
    isAlgebraicSpace_over_pullback_left site S hS a g hR hU' hU
  have h₁ : AlgebraicGeometry.Space.HoldsOnEveryEtaleChart site S hS P
      (pullback.fst a g).left :=
    chartProperty_of_isPullback site S hS P hP hPB hU' hR hU
      ((IsPullback.of_hasPullback a g).flip.map (Over.forget base)) hg
  have h₂ : AlgebraicGeometry.Space.HoldsOnEveryEtaleChart site S hS P
      (pullback.fst a g ≫ b).left := by
    rw [Over.comp_left]
    exact AlgebraicGeometry.Space.holdsOnEveryEtaleChart_comp site S hS P hP hPB hR hU _ _ h₁ hb
  exact chartProperty_of_isPullback site S hS P hP hW hPB hU' hU (hk.map (Over.forget base)) h₂

private theorem isFlat_of_etale_presheaf
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    {V : AlgebraicGeometry.BigFppfOver site S hS} (f : yoneda.obj V ⟶ F)
    (hF : AlgebraicGeometry.IsAlgebraicSpace site S hS F)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) f) :
    AlgebraicGeometry.Space.IsFlat site S hS f := by
  let : MorphismProperty.IsLocalAtTarget (@Flat : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  exact chartProperty_of_etale_presheaf site S hS _
    AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget
    (fun _ hk => (Etale.iff_flat_and_formallyUnramified.mp hk).1) f hF he

private theorem isLocallyOfFinitePresentation_of_etale_presheaf
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    {V : AlgebraicGeometry.BigFppfOver site S hS} (f : yoneda.obj V ⟶ F)
    (hF : AlgebraicGeometry.IsAlgebraicSpace site S hS F)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme site S hS))) f) :
    AlgebraicGeometry.Space.IsLocallyOfFinitePresentation site S hS f := by
  let : MorphismProperty.IsLocalAtTarget
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  have hP : AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    AlgebraicGeometry.LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
  exact chartProperty_of_etale_presheaf site S hS _ hP
    (fun _ hk => (Etale.iff_flat_and_formallyUnramified.mp hk).2.2) f hF he

/-- Cancelling the isomorphisms `eR` and `eU` from an equation between composites of
morphisms of site objects. -/
private theorem yoneda_map_comp_eq_of_comp_eq
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {A B : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    {Rs Us T : AlgebraicGeometry.BigFppfOver site S hS}
    (eR : A ≅ yoneda.obj Rs) (eU : B ≅ yoneda.obj Us) {p q : A ⟶ B} {x y : Rs ⟶ Us}
    (hx : yoneda.map x = eR.inv ≫ p ≫ eU.hom) (hy : yoneda.map y = eR.inv ≫ q ≫ eU.hom)
    {f g : T ⟶ Rs} (h : f ≫ x = g ≫ y) :
    yoneda.map f ≫ eR.inv ≫ p = yoneda.map g ≫ eR.inv ≫ q := by
  have h := congrArg yoneda.map h
  simp only [Functor.map_comp, hx, hy] at h
  simp only [← Category.assoc] at h
  simpa only [Category.assoc] using (cancel_mono eU.hom).mp h

private theorem jointlyMono_site_of_jointlyMono
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {base : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u} {R U : Over base}
    (j : AlgebraicGeometry.Space.PreRelation R U) [JointlyMono₂ j.target j.source]
    {Rs Us : AlgebraicGeometry.BigFppfOver site S hS}
    (eR : R.left ≅ yoneda.obj Rs) (eU : U.left ≅ yoneda.obj Us)
    (ts ss : Rs ⟶ Us)
    (hts : yoneda.map ts = eR.inv ≫ j.target.left ≫ eU.hom)
    (hss : yoneda.map ss = eR.inv ≫ j.source.left ≫ eU.hom) :
    JointlyMono₂ ts ss := by
  have hwt : j.target.left ≫ U.hom = R.hom := Over.w j.target
  constructor
  intro T f g h₁ h₂
  have hA := yoneda_map_comp_eq_of_comp_eq site S hS eR eU hts hts h₁
  have hB := yoneda_map_comp_eq_of_comp_eq site S hS eR eU hss hss h₂
  let xf : yoneda.obj T ⟶ R.left := yoneda.map f ≫ eR.inv
  let xg : yoneda.obj T ⟶ R.left := yoneda.map g ≫ eR.inv
  have hw : xg ≫ R.hom = xf ≫ R.hom := by
    calc (yoneda.map g ≫ eR.inv) ≫ R.hom
        = (yoneda.map g ≫ eR.inv ≫ j.target.left) ≫ U.hom := by
          simp only [Category.assoc, hwt]
      _ = (yoneda.map f ≫ eR.inv ≫ j.target.left) ≫ U.hom := by rw [hA]
      _ = (yoneda.map f ≫ eR.inv) ≫ R.hom := by
          simp only [Category.assoc, hwt]
  have hfg : (Over.homMk xf : Over.mk (xf ≫ R.hom) ⟶ R) = Over.homMk xg hw := by
    refine JointlyMono₂.right_cancellation (p₁ := j.target) (p₂ := j.source) _ _ ?_ ?_
    · apply Over.OverMorphism.ext
      change (yoneda.map f ≫ eR.inv) ≫ j.target.left =
        (yoneda.map g ≫ eR.inv) ≫ j.target.left
      simpa only [Category.assoc] using hA
    · apply Over.OverMorphism.ext
      change (yoneda.map f ≫ eR.inv) ≫ j.source.left =
        (yoneda.map g ≫ eR.inv) ≫ j.source.left
      simpa only [Category.assoc] using hB
  have heq : yoneda.map f ≫ eR.inv = yoneda.map g ≫ eR.inv :=
    congrArg (fun k : Over.mk (xf ≫ R.hom) ⟶ R => k.left) hfg
  exact yoneda.map_injective ((cancel_mono eR.inv).mp heq)

private theorem exists_refl_site
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {base : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u} {R U : Over base}
    (j : AlgebraicGeometry.Space.PreRelation R U)
    (hjpre : AlgebraicGeometry.Space.IsPreEquivalenceRelation j)
    {Rs Us : AlgebraicGeometry.BigFppfOver site S hS}
    (eR : R.left ≅ yoneda.obj Rs) (eU : U.left ≅ yoneda.obj Us)
    (ts ss : Rs ⟶ Us)
    (hts : yoneda.map ts = eR.inv ≫ j.target.left ≫ eU.hom)
    (hss : yoneda.map ss = eR.inv ≫ j.source.left ≫ eU.hom) :
    ∃ r : Us ⟶ Rs, r ≫ ts = 𝟙 Us ∧ r ≫ ss = 𝟙 Us := by
  obtain ⟨r, hr₁, hr₂⟩ := (hjpre Us (eU.inv ≫ U.hom)).refl ⟨eU.inv, rfl⟩
  refine ⟨yoneda.preimage (r.1 ≫ eR.hom), ?_, ?_⟩
  · apply yoneda.map_injective
    simp only [Functor.map_comp, Functor.map_preimage, hts,
      Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, hr₁, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  · apply yoneda.map_injective
    simp only [Functor.map_comp, Functor.map_preimage, hss,
      Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, hr₂, Iso.inv_hom_id, CategoryTheory.Functor.map_id]

private theorem exists_symm_site
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {base : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u} {R U : Over base}
    (j : AlgebraicGeometry.Space.PreRelation R U)
    (hjpre : AlgebraicGeometry.Space.IsPreEquivalenceRelation j)
    {Rs Us : AlgebraicGeometry.BigFppfOver site S hS}
    (eR : R.left ≅ yoneda.obj Rs) (eU : U.left ≅ yoneda.obj Us)
    (ts ss : Rs ⟶ Us)
    (hts : yoneda.map ts = eR.inv ≫ j.target.left ≫ eU.hom)
    (hss : yoneda.map ss = eR.inv ≫ j.source.left ≫ eU.hom) :
    ∃ sy : Rs ⟶ Rs, sy ≫ ts = ss ∧ sy ≫ ss = ts := by
  have hwt : j.target.left ≫ U.hom = R.hom := Over.w j.target
  have hws : j.source.left ≫ U.hom = R.hom := Over.w j.source
  obtain ⟨r, hr₁, hr₂⟩ := (hjpre Rs (eR.inv ≫ R.hom)).symm
    (x := ⟨eR.inv ≫ j.target.left, by simp only [Category.assoc, hwt]⟩)
    (y := ⟨eR.inv ≫ j.source.left, by simp only [Category.assoc, hws]⟩)
    ⟨⟨eR.inv, rfl⟩, rfl, rfl⟩
  refine ⟨yoneda.preimage (r.1 ≫ eR.hom), ?_, ?_⟩
  · apply yoneda.map_injective
    simp only [Functor.map_comp, Functor.map_preimage, hts, hss, Category.assoc,
      Iso.hom_inv_id_assoc]
    rw [← Category.assoc, hr₁]
    simp only [Category.assoc]
  · apply yoneda.map_injective
    simp only [Functor.map_comp, Functor.map_preimage, hts, hss, Category.assoc,
      Iso.hom_inv_id_assoc]
    rw [← Category.assoc, hr₂]
    simp only [Category.assoc]

private theorem exists_trans_site
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {base : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u} {R U : Over base}
    (j : AlgebraicGeometry.Space.PreRelation R U)
    (hjpre : AlgebraicGeometry.Space.IsPreEquivalenceRelation j)
    {Rs Us : AlgebraicGeometry.BigFppfOver site S hS}
    (eR : R.left ≅ yoneda.obj Rs) (eU : U.left ≅ yoneda.obj Us)
    (ts ss : Rs ⟶ Us)
    (hts : yoneda.map ts = eR.inv ≫ j.target.left ≫ eU.hom)
    (hss : yoneda.map ss = eR.inv ≫ j.source.left ≫ eU.hom) :
    ∃ tr : pullback ss ts ⟶ Rs,
      tr ≫ ts = pullback.fst ss ts ≫ ts ∧ tr ≫ ss = pullback.snd ss ts ≫ ss := by
  have hwt : j.target.left ≫ U.hom = R.hom := Over.w j.target
  have hws : j.source.left ≫ U.hom = R.hom := Over.w j.source
  have hstar : yoneda.map (pullback.fst ss ts) ≫ eR.inv ≫ j.source.left =
      yoneda.map (pullback.snd ss ts) ≫ eR.inv ≫ j.target.left :=
    yoneda_map_comp_eq_of_comp_eq site S hS eR eU hss hts pullback.condition
  have hbb : yoneda.map (pullback.snd ss ts) ≫ eR.inv ≫ R.hom =
      yoneda.map (pullback.fst ss ts) ≫ eR.inv ≫ R.hom := by
    calc yoneda.map (pullback.snd ss ts) ≫ eR.inv ≫ R.hom
        = (yoneda.map (pullback.snd ss ts) ≫ eR.inv ≫ j.target.left) ≫ U.hom := by
          simp only [Category.assoc, hwt]
      _ = (yoneda.map (pullback.fst ss ts) ≫ eR.inv ≫ j.source.left) ≫ U.hom := by
          rw [hstar]
      _ = yoneda.map (pullback.fst ss ts) ≫ eR.inv ≫ R.hom := by
          simp only [Category.assoc, hws]
  obtain ⟨r, hr₁, hr₂⟩ := (hjpre (pullback ss ts)
      (yoneda.map (pullback.fst ss ts) ≫ eR.inv ≫ R.hom)).trans
    (x := ⟨yoneda.map (pullback.fst ss ts) ≫ eR.inv ≫ j.target.left, by
      simp only [Category.assoc, hwt]⟩)
    (y := ⟨yoneda.map (pullback.fst ss ts) ≫ eR.inv ≫ j.source.left, by
      simp only [Category.assoc, hws]⟩)
    (z := ⟨yoneda.map (pullback.snd ss ts) ≫ eR.inv ≫ j.source.left, by
      simp only [Category.assoc, hws]
      simpa only [Category.assoc] using hbb⟩)
    ⟨⟨yoneda.map (pullback.fst ss ts) ≫ eR.inv, by simp only [Category.assoc]⟩,
      by simp only [Category.assoc], by simp only [Category.assoc]⟩
    ⟨⟨yoneda.map (pullback.snd ss ts) ≫ eR.inv, by
        simpa only [Category.assoc] using hbb⟩,
      by simpa only [Category.assoc] using hstar.symm,
      by simp only [Category.assoc]⟩
  refine ⟨yoneda.preimage (r.1 ≫ eR.hom), ?_, ?_⟩
  · apply yoneda.map_injective
    simp only [Functor.map_comp, Functor.map_preimage, hts, Category.assoc,
      Iso.hom_inv_id_assoc]
    rw [← Category.assoc, hr₁]
    simp only [Category.assoc]
  · apply yoneda.map_injective
    simp only [Functor.map_comp, Functor.map_preimage, hss, Category.assoc,
      Iso.hom_inv_id_assoc]
    rw [← Category.assoc, hr₂]
    simp only [Category.assoc]

/-- Pushing a jointly monic pair of site objects forward to schemes over `site.obj hS`
keeps it jointly monic. -/
private theorem jointlyMono_overPost_map
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {Rs Us : AlgebraicGeometry.BigFppfOver site S hS} (ts ss : Rs ⟶ Us)
    [JointlyMono₂ ts ss] :
    JointlyMono₂ ((Over.post (X := site.obj hS) site.inclusion).map ts)
      ((Over.post (X := site.obj hS) site.inclusion).map ss) := by
  let : Mono (prod.lift ts ss) := mono_prodLift_of_jointlyMono ts ss
  have hmL : Mono ((prod.lift ts ss).left) := mono_left_of_mono_over _
  have hmS : Mono (site.inclusion.map ((prod.lift ts ss).left)) :=
    mono_map_of_preservesPullback site.inclusion _
  have hcomp : ∀ (c : (Us ⨯ Us : AlgebraicGeometry.BigFppfOver site S hS) ⟶ Us)
      (t : Rs ⟶ Us), prod.lift ts ss ≫ c = t → ∀ {Z : Scheme.{u}}
      (w : Z ⟶ site.inclusion.obj Rs.left),
      (w ≫ site.inclusion.map ((prod.lift ts ss).left)) ≫ site.inclusion.map c.left =
        w ≫ site.inclusion.map t.left := fun c t h Z w => by
    rw [Category.assoc, ← site.inclusion.map_comp]
    exact congrArg (fun k => w ≫ site.inclusion.map k) (congrArg Over.Hom.left h)
  constructor
  intro T x y h₁ h₂
  apply Over.OverMorphism.ext
  refine (cancel_mono (site.inclusion.map ((prod.lift ts ss).left))).mp ?_
  refine ((isPullback_over_prod Us Us).map site.inclusion).hom_ext ?_ ?_
  · exact (hcomp _ _ (prod.lift_fst ts ss) x.left).trans
      ((congrArg Over.Hom.left h₁).trans (hcomp _ _ (prod.lift_fst ts ss) y.left).symm)
  · exact (hcomp _ _ (prod.lift_snd ts ss) x.left).trans
      ((congrArg Over.Hom.left h₂).trans (hcomp _ _ (prod.lift_snd ts ss) y.left).symm)

/-- The quotient sheaf of a pair of site objects whose image in schemes over
`site.obj hS` is an equivalence relation with flat and locally finitely presented
projections is an algebraic space. -/
private theorem isAlgebraicSpace_quotient_of_isEquivalenceRelation_overPost
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)]
    {Rs Us : AlgebraicGeometry.BigFppfOver site S hS} (ts ss : Rs ⟶ Us)
    (hEF : CategoryTheory.IsEquivalenceRelation
      ((Over.post (X := site.obj hS) site.inclusion).map ts)
      ((Over.post (X := site.obj hS) site.inclusion).map ss))
    (hsflat : Flat ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map ss))
    (htflat : Flat ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map ts))
    (hslfp : LocallyOfFinitePresentation
      ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map ss))
    (htlfp : LocallyOfFinitePresentation
      ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map ts)) :
    AlgebraicGeometry.IsAlgebraicSpace site S hS
      (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
        (Over.post site.inclusion)
        (prod.lift ((Over.post site.inclusion).map ts)
          ((Over.post site.inclusion).map ss))).obj := by
  let F := Over.post (X := site.obj hS) site.inclusion
  let jS : Stacks.Groupoids.PreRelation (F.obj Rs) (F.obj Us) :=
    prod.lift (F.map ts) (F.map ss)
  have hjt : jS.target = F.map ts := prod.lift_fst _ _
  have hjs : jS.source = F.map ss := prod.lift_snd _ _
  let : CategoryTheory.IsEquivalenceRelation jS.target jS.source := by
    rwa [hjt, hjs]
  obtain ⟨H0, hH0, -⟩ := AlgebraicGeometry.existsUnique_groupoidScheme_of_isEquivalenceRelation jS
  rcases H0 with ⟨objects, arrows, source, target, comp, identity, inverse,
    hsid, htid, hsinv, htinv, hsc, htc, li, ri, linv, rinv, assoc'⟩
  rcases hH0 with ⟨hob, har, hsrc, htgt⟩
  dsimp only at hob har
  subst hob har
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hsrc htgt
  subst hsrc htgt
  let H : Stacks.Groupoids.GroupoidScheme S :=
    ⟨F.obj Us, F.obj Rs, jS.source, jS.target, comp, identity, inverse,
      hsid, htid, hsinv, htinv, hsc, htc, li, ri, linv, rinv, assoc'⟩
  have hj : AlgebraicGeometry.groupoidPreRelation H = jS :=
    prod.hom_ext (prod.lift_fst _ _) (prod.lift_snd _ _)
  have hU : site.Contains H.objects.left := Us.left.property
  let : Flat H.source.left := by
    change Flat (jS.source).left
    rwa [hjs]
  let : Flat H.target.left := by
    change Flat (jS.target).left
    rwa [hjt]
  let : LocallyOfFinitePresentation H.source.left := by
    change LocallyOfFinitePresentation (jS.source).left
    rwa [hjs]
  let : LocallyOfFinitePresentation H.target.left := by
    change LocallyOfFinitePresentation (jS.target).left
    rwa [hjt]
  have hrelH : CategoryTheory.IsEquivalenceRelation
      (AlgebraicGeometry.groupoidPreRelation H).target
      (AlgebraicGeometry.groupoidPreRelation H).source := by
    rw [hj]
    infer_instance
  have hres := isAlgebraicSpace_quotient_groupoidScheme_aux site S hS H hU hrelH
  rwa [hj] at hres

/-- The quotient sheaf of a relation of site objects carrying reflexivity, symmetry
and transitivity maps, jointly monic, with flat and locally finitely presented
projections, is an algebraic space. -/
private theorem isAlgebraicSpace_quotient_of_siteEquivalenceData
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)]
    {Rs Us : AlgebraicGeometry.BigFppfOver site S hS} (ts ss : Rs ⟶ Us)
    (hjm : JointlyMono₂ ts ss)
    (rr : Us ⟶ Rs) (hr₁ : rr ≫ ts = 𝟙 Us) (hr₂ : rr ≫ ss = 𝟙 Us)
    (sy : Rs ⟶ Rs) (hsy₁ : sy ≫ ts = ss) (hsy₂ : sy ≫ ss = ts)
    (tr : pullback ss ts ⟶ Rs)
    (htr₁ : tr ≫ ts = pullback.fst ss ts ≫ ts)
    (htr₂ : tr ≫ ss = pullback.snd ss ts ≫ ss)
    (hsflat : Flat ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map ss))
    (htflat : Flat ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map ts))
    (hslfp : LocallyOfFinitePresentation
      ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map ss))
    (htlfp : LocallyOfFinitePresentation
      ((AlgebraicGeometry.BigFppfOver.toScheme site S hS).map ts)) :
    AlgebraicGeometry.IsAlgebraicSpace site S hS
      (Stacks.Groupoids.quotientSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS)
        (Over.post site.inclusion)
        (prod.lift ((Over.post site.inclusion).map ts)
          ((Over.post site.inclusion).map ss))).obj := by
  let F := Over.post (X := site.obj hS) site.inclusion
  let : JointlyMono₂ ts ss := hjm
  let E : CategoryTheory.EquivalenceRelation ts ss :=
    { __ := hjm
      r := rr, reflexivity₁ := hr₁, reflexivity₂ := hr₂
      s := sy, symmetry₁ := hsy₁, symmetry₂ := hsy₂
      c := PullbackCone.mk (pullback.fst ss ts) (pullback.snd ss ts) pullback.condition
      isLimit := pullbackIsPullback ss ts
      t := tr, transitivity₁ := htr₁, transitivity₂ := htr₂ }
  let : JointlyMono₂ (F.map ts) (F.map ss) := jointlyMono_overPost_map site S hS ts ss
  let : PreservesLimitsOfShape WalkingCospan F :=
    overPost_preservesLimitsOfShape site.inclusion (site.obj hS)
  let Et := E.toTransitiveRelation.map F
  let Es := E.toSymmetricRelation.map F
  let EF : CategoryTheory.EquivalenceRelation (F.map ts) (F.map ss) :=
    { __ := E.toReflexiveRelation.map F
      s := Es.s, symmetry₁ := Es.symmetry₁, symmetry₂ := Es.symmetry₂
      c := Et.c, isLimit := Et.isLimit, t := Et.t
      transitivity₁ := Et.transitivity₁, transitivity₂ := Et.transitivity₂ }
  exact isAlgebraicSpace_quotient_of_isEquivalenceRelation_overPost site S hS ts ss
    EF.isEquivalenceRelation hsflat htflat hslfp htlfp

private theorem chartProperty_postcomp_iso
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    (P : MorphismProperty Scheme.{u})
    {X Y Y' : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (e : Y ≅ Y')
    (hf : AlgebraicGeometry.Space.HoldsOnEveryEtaleChart site S hS P f) :
    AlgebraicGeometry.Space.HoldsOnEveryEtaleChart site S hS P (f ≫ e.hom) := by
  intro U V a b k ha hb hw
  refine hf U V a (b ≫ e.inv) k ha
    (MorphismProperty.RespectsIso.postcomp _ e.inv b hb) ?_
  rw [← Category.assoc, hw]
  simp

/-- A morphism of site objects corresponding, up to isomorphisms, to a morphism of
presheaves with a chart property has that chart property. -/
private theorem chartProperty_yoneda_map_of_eq
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    (P : MorphismProperty Scheme.{u})
    {A B : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    {Rs Us : AlgebraicGeometry.BigFppfOver site S hS}
    (eR : A ≅ yoneda.obj Rs) (eU : B ≅ yoneda.obj Us) (k : A ⟶ B) {t : Rs ⟶ Us}
    (ht : yoneda.map t = eR.inv ≫ k ≫ eU.hom)
    (hk : AlgebraicGeometry.Space.HoldsOnEveryEtaleChart site S hS P k) :
    AlgebraicGeometry.Space.HoldsOnEveryEtaleChart site S hS P (yoneda.map t) := by
  rw [ht]
  exact chartProperty_precomp_iso site S hS _ eR.symm _
    (chartProperty_postcomp_iso site S hS _ k eU hk)

/-- An algebraic space over `base` carrying a jointly monic pair to an object with a
scheme chart, one leg locally of finite presentation, is representable. -/
private theorem isRepresentable_of_jointlyMono_of_iso_yoneda
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {base : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u} {R U' : Over base}
    (t s : R ⟶ U') [JointlyMono₂ t s]
    (hR : AlgebraicGeometry.IsAlgebraicSpace site S hS R.left)
    (hU' : AlgebraicGeometry.IsAlgebraicSpace site S hS U'.left)
    (Us : AlgebraicGeometry.BigFppfOver site S hS) (eU : U'.left ≅ yoneda.obj Us)
    (hsL : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation site S hS s.left) :
    R.left.IsRepresentable := by
  have hTU : AlgebraicGeometry.IsAlgebraicSpace site S hS (yoneda.obj (Us ⨯ Us)) :=
    AlgebraicGeometry.isAlgebraicSpace_yoneda site S hS (Us ⨯ Us)
  let py : yoneda.obj (Us ⨯ Us) ≅ yoneda.obj Us ⨯ yoneda.obj Us :=
    PreservesLimitPair.iso yoneda Us Us
  let q : R.left ⟶ yoneda.obj (Us ⨯ Us) :=
    prod.lift (t.left ≫ eU.hom) (s.left ≫ eU.hom) ≫ py.inv
  let q₁ : yoneda.obj (Us ⨯ Us) ⟶ U'.left :=
    yoneda.map (prod.fst : Us ⨯ Us ⟶ Us) ≫ eU.inv
  let q₂ : yoneda.obj (Us ⨯ Us) ⟶ U'.left :=
    yoneda.map (prod.snd : Us ⨯ Us ⟶ Us) ≫ eU.inv
  have hq₁ : q ≫ q₁ = t.left := by
    change (prod.lift (t.left ≫ eU.hom) (s.left ≫ eU.hom) ≫ py.inv) ≫
      (yoneda.map (prod.fst : Us ⨯ Us ⟶ Us) ≫ eU.inv) = t.left
    rw [Category.assoc, ← Category.assoc py.inv, PreservesLimitPair.iso_inv_fst,
      ← Category.assoc, prod.lift_fst, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hq₂ : q ≫ q₂ = s.left := by
    change (prod.lift (t.left ≫ eU.hom) (s.left ≫ eU.hom) ≫ py.inv) ≫
      (yoneda.map (prod.snd : Us ⨯ Us ⟶ Us) ≫ eU.inv) = s.left
    rw [Category.assoc, ← Category.assoc py.inv, PreservesLimitPair.iso_inv_snd,
      ← Category.assoc, prod.lift_snd, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hmonoq : Mono q := mono_of_jointlyMono_factor t s q q₁ q₂ hq₁ hq₂
  have hlft : AlgebraicGeometry.Space.IsLocallyOfFiniteType site S hS q := by
    refine AlgebraicGeometry.Space.isLocallyOfFiniteType_of_comp site S hS
      hR hTU hU' q q₂ ?_
    rw [hq₂]
    exact AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation
      site S hS hsL
  exact AlgebraicGeometry.Space.isRepresentable_of_locallyQuasiFinite_separated site S hS
    R.left (yoneda.obj (Us ⨯ Us)) hR hTU q inferInstance
    (AlgebraicGeometry.Space.isLocallyQuasiFinite_of_mono site S hS hR hTU q hmonoq hlft)
    (AlgebraicGeometry.Space.isSeparated_of_mono site S hS q hmonoq)

/-- The quotient of a jointly monic pre-equivalence relation with representable relation
object, an object with a scheme chart, and flat, locally finitely presented projections is
an algebraic space. -/
private theorem isAlgebraicSpace_quotient_of_isRepresentable_of_iso_yoneda
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)]
    {base : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u} {R U : Over base}
    (j : AlgebraicGeometry.Space.PreRelation R U) [JointlyMono₂ j.target j.source]
    (hjpre : AlgebraicGeometry.Space.IsPreEquivalenceRelation j) [R.left.IsRepresentable]
    (Us : AlgebraicGeometry.BigFppfOver site S hS) (eU : U.left ≅ yoneda.obj Us)
    (hsF : AlgebraicGeometry.Space.IsFlat site S hS j.source.left)
    (htF : AlgebraicGeometry.Space.IsFlat site S hS j.target.left)
    (hsL : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation site S hS j.source.left)
    (htL : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation site S hS j.target.left) :
    AlgebraicGeometry.IsAlgebraicSpace site S hS
      (AlgebraicGeometry.Space.quotientSheaf j).obj := by
  let Rs := R.left.reprX
  let eR : R.left ≅ yoneda.obj Rs := R.left.reprW.symm
  let ts : Rs ⟶ Us := yoneda.preimage (eR.inv ≫ j.target.left ≫ eU.hom)
  let ss : Rs ⟶ Us := yoneda.preimage (eR.inv ≫ j.source.left ≫ eU.hom)
  have hts : yoneda.map ts = eR.inv ≫ j.target.left ≫ eU.hom :=
    Functor.map_preimage _ _
  have hss : yoneda.map ss = eR.inv ≫ j.source.left ≫ eU.hom :=
    Functor.map_preimage _ _
  obtain ⟨rr, hr₁, hr₂⟩ := exists_refl_site site S hS j hjpre eR eU ts ss hts hss
  obtain ⟨sy, hsy₁, hsy₂⟩ := exists_symm_site site S hS j hjpre eR eU ts ss hts hss
  obtain ⟨tr, htr₁, htr₂⟩ := exists_trans_site site S hS j hjpre eR eU ts ss hts hss
  refine isAlgebraicSpace_quotient_of_siteRelation site S hS j ts ss eR eU ?_ ?_ ?_
  · rw [hts]
    simp only [Iso.hom_inv_id_assoc]
  · rw [hss]
    simp only [Iso.hom_inv_id_assoc]
  · exact isAlgebraicSpace_quotient_of_siteEquivalenceData site S hS ts ss
      (jointlyMono_site_of_jointlyMono site S hS j eR eU ts ss hts hss)
      rr hr₁ hr₂ sy hsy₁ hsy₂ tr htr₁ htr₂
      (flat_of_chartProperty_yoneda site S hS ss
        (chartProperty_yoneda_map_of_eq site S hS _ eR eU _ hss hsF))
      (flat_of_chartProperty_yoneda site S hS ts
        (chartProperty_yoneda_map_of_eq site S hS _ eR eU _ hts htF))
      (lfp_of_chartProperty_yoneda site S hS ss
        (chartProperty_yoneda_map_of_eq site S hS _ eR eU _ hss hsL))
      (lfp_of_chartProperty_yoneda site S hS ts
        (chartProperty_yoneda_map_of_eq site S hS _ eR eU _ hts htL))

/-- After restricting along a scheme atlas of the object space, the restricted relation is a
relation of schemes in the site, and its quotient sheaf is an algebraic space. -/
private theorem isAlgebraicSpace_quotient_restricted
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)]
    {base : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (hbase : AlgebraicGeometry.IsAlgebraicSpace site S hS base) {R U U' : Over base}
    (hR : AlgebraicGeometry.IsAlgebraicSpace site S hS R.left)
    (hU : AlgebraicGeometry.IsAlgebraicSpace site S hS U.left)
    (hU' : AlgebraicGeometry.IsAlgebraicSpace site S hS U'.left)
    (j : AlgebraicGeometry.Space.PreRelation R U)
    (hrel : CategoryTheory.IsEquivalenceRelation j.target j.source)
    (hjpre : AlgebraicGeometry.Space.IsPreEquivalenceRelation j) (g : U' ⟶ U)
    (Us : AlgebraicGeometry.BigFppfOver site S hS) (eU : U'.left ≅ yoneda.obj Us)
    (hsflat : AlgebraicGeometry.Space.IsFlat site S hS j.source.left)
    (htflat : AlgebraicGeometry.Space.IsFlat site S hS j.target.left)
    (hslfp : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation site S hS j.source.left)
    (htlfp : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation site S hS j.target.left)
    (hgflat : AlgebraicGeometry.Space.IsFlat site S hS g.left)
    (hglfp : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation site S hS g.left) :
    AlgebraicGeometry.IsAlgebraicSpace site S hS
      (AlgebraicGeometry.Space.quotientSheaf
        (AlgebraicGeometry.Space.PreRelation.restrict j g)).obj := by
  classical
  let j'' := AlgebraicGeometry.Space.PreRelation.restrict j g
  let : CategoryTheory.IsEquivalenceRelation j.target j.source := hrel
  let : CategoryTheory.IsEquivalenceRelation j''.target j''.source :=
    AlgebraicGeometry.Space.PreRelation.isEquivalenceRelation_restrict j g
  have hmono'' : Mono j'' :=
    ((AlgebraicGeometry.Space.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j'').mp
      inferInstance).1
  have hjm'' : JointlyMono₂ j''.target j''.source := by
    apply jointlyMono_of_mono_prodLift
    rwa [show prod.lift j''.target j''.source = j'' from
      prod.hom_ext (prod.lift_fst _ _) (prod.lift_snd _ _)]
  let : JointlyMono₂ j''.target j''.source := hjm''
  have hjpre'' : AlgebraicGeometry.Space.IsPreEquivalenceRelation j'' :=
    AlgebraicGeometry.Space.PreRelation.isPreEquivalenceRelation_restrict j g hjpre
  have hRest : AlgebraicGeometry.IsAlgebraicSpace site S hS
      (AlgebraicGeometry.Space.PreRelation.restriction j g).left :=
    isAlgebraicSpace_over_pullback_left site S hS (prod.map g g) j
      (isAlgebraicSpace_over_prod_left site S hS hbase U' U' hU' hU') hR
      (isAlgebraicSpace_over_prod_left site S hS hbase U U hU hU)
  have hs''F : AlgebraicGeometry.Space.IsFlat site S hS j''.source.left :=
    algSpace_property_of_isPullback_pullback_fst_comp site S hS _
      AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget hR hU hU' hRest
      (j ≫ prod.fst) (j ≫ prod.snd) g (isPullback_restrict_source j g) hsflat hgflat
  have ht''F : AlgebraicGeometry.Space.IsFlat site S hS j''.target.left :=
    algSpace_property_of_isPullback_pullback_fst_comp site S hS _
      AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget hR hU hU' hRest
      (j ≫ prod.snd) (j ≫ prod.fst) g (isPullback_restrict_target j g) htflat hgflat
  have hs''L : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation site S hS j''.source.left :=
    algSpace_property_of_isPullback_pullback_fst_comp site S hS _
      AlgebraicGeometry.LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget hR hU hU' hRest
      (j ≫ prod.fst) (j ≫ prod.snd) g (isPullback_restrict_source j g) hslfp hglfp
  have ht''L : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation site S hS j''.target.left :=
    algSpace_property_of_isPullback_pullback_fst_comp site S hS _
      AlgebraicGeometry.LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget hR hU hU' hRest
      (j ≫ prod.snd) (j ≫ prod.fst) g (isPullback_restrict_target j g) htlfp hglfp
  let : (AlgebraicGeometry.Space.PreRelation.restriction j g).left.IsRepresentable :=
    isRepresentable_of_jointlyMono_of_iso_yoneda site S hS j''.target j''.source hRest hU' Us eU
      hs''L
  exact isAlgebraicSpace_quotient_of_isRepresentable_of_iso_yoneda site S hS j'' hjpre''
    Us eU hs''F ht''F hs''L ht''L

/-- Condition (1): the quotient of a flat, locally finitely presented
equivalence-relation groupoid in algebraic spaces is an algebraic space. -/
@[stacks 04S6 "part (1)"]
public theorem isAlgebraicSpace_quotient_groupoidInAlgebraicSpaces
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)]
    {base : AlgebraicGeometry.AlgebraicSpaces site S hS}
    (G : AlgebraicGeometry.GroupoidInAlgebraicSpaces site S hS base)
    (hrel : CategoryTheory.IsEquivalenceRelation
      (AlgebraicGeometry.Space.groupoidPreRelation G).target
      (AlgebraicGeometry.Space.groupoidPreRelation G).source)
    (hsflat : AlgebraicGeometry.Space.IsFlat site S hS G.source.hom)
    (htflat : AlgebraicGeometry.Space.IsFlat site S hS G.target.hom)
    (hslfp : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation site S hS G.source.hom)
    (htlfp : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation site S hS G.target.hom) :
    AlgebraicGeometry.IsAlgebraicSpace site S hS
      (AlgebraicGeometry.Space.quotientSheaf
        (AlgebraicGeometry.Space.groupoidPreRelation G)).obj := by
  classical
  obtain ⟨Us, a, haS, haE⟩ := G.objects.property.exists_atlas
  let g : (Over.mk (a ≫ G.objectsToBase.hom) : Over base.obj) ⟶
      (Over.mk G.objectsToBase.hom : Over base.obj) := Over.homMk a
  have hg : Presheaf.IsLocallySurjective
      (AlgebraicGeometry.BigFppfOver.topology site S hS) g.left :=
    locallySurjective_of_surjectiveEtale site S hS a haS haE
  have hgflat : AlgebraicGeometry.Space.IsFlat site S hS g.left :=
    isFlat_of_etale_presheaf site S hS a G.objects.property haE
  have hglfp : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation site S hS g.left :=
    isLocallyOfFinitePresentation_of_etale_presheaf site S hS a G.objects.property haE
  have hjs : (AlgebraicGeometry.Space.groupoidPreRelation G).source.left = G.source.hom :=
    congrArg Over.Hom.left (prod.lift_snd _ _)
  have hjt : (AlgebraicGeometry.Space.groupoidPreRelation G).target.left = G.target.hom :=
    congrArg Over.Hom.left (prod.lift_fst _ _)
  refine isAlgebraicSpace_quotient_of_restrict site S hS
    (AlgebraicGeometry.Space.groupoidPreRelation G) g
    (AlgebraicGeometry.Space.groupoidPreRelation_isPreEquivalenceRelation G) hg
    G.objects.property (AlgebraicGeometry.isAlgebraicSpace_yoneda site S hS Us) ?_
  refine isAlgebraicSpace_quotient_restricted site S hS base.property
    G.arrows.property G.objects.property
    (AlgebraicGeometry.isAlgebraicSpace_yoneda site S hS Us)
    (AlgebraicGeometry.Space.groupoidPreRelation G) hrel
    (AlgebraicGeometry.Space.groupoidPreRelation_isPreEquivalenceRelation G) g Us (Iso.refl _)
    ?_ ?_ ?_ ?_ hgflat hglfp
  · rwa [hjs]
  · rwa [hjt]
  · rwa [hjs]
  · rwa [hjt]

/-- Condition (1) of **Stacks 04S6** for a pre-relation instead of a groupoid: the quotient
sheaf of an equivalence relation of algebraic spaces over an algebraic space, whose source and
target are flat and locally of finite presentation, is an algebraic space.

An equivalence relation determines its composition law uniquely
(`AlgebraicGeometry.Space.existsUnique_groupoid_of_isEquivalenceRelation`), so the groupoid
structure condition (1) asks for is not an extra hypothesis here. -/
public theorem isAlgebraicSpace_quotient_preRelation
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)]
    {base : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (hbase : AlgebraicGeometry.IsAlgebraicSpace site S hS base) {R U : Over base}
    (hR : AlgebraicGeometry.IsAlgebraicSpace site S hS R.left)
    (hU : AlgebraicGeometry.IsAlgebraicSpace site S hS U.left)
    (j : AlgebraicGeometry.Space.PreRelation R U)
    [IsEquivalenceRelation j.target j.source]
    (hs : AlgebraicGeometry.Space.IsFlat site S hS j.source.left)
    (ht : AlgebraicGeometry.Space.IsFlat site S hS j.target.left)
    (hsfp : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation site S hS j.source.left)
    (htfp : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation site S hS j.target.left) :
    AlgebraicGeometry.IsAlgebraicSpace site S hS (AlgebraicGeometry.Space.quotientSheaf j).obj := by
  have hjrel : IsEquivalenceRelation j.target j.source := inferInstance
  let baseA : AlgebraicGeometry.AlgebraicSpaces site S hS := ⟨base, hbase⟩
  let RA : AlgebraicGeometry.AlgebraicSpaces site S hS := ⟨R.left, hR⟩
  let UA : AlgebraicGeometry.AlgebraicSpaces site S hS := ⟨U.left, hU⟩
  let qR : RA ⟶ baseA := ObjectProperty.homMk R.hom
  let qU : UA ⟶ baseA := ObjectProperty.homMk U.hom
  let j' : AlgebraicGeometry.Space.PreRelation (Over.mk qR.hom) (Over.mk qU.hom) := j
  have hjrel' : IsEquivalenceRelation j'.target j'.source := hjrel
  obtain ⟨G, hG, _⟩ := AlgebraicGeometry.Space.existsUnique_groupoid_of_isEquivalenceRelation j'
  rcases G with ⟨objects, arrows, ob, ab, source, target, so, htOver, comp, co, pg⟩
  rcases hG with ⟨ho, ha, hob, hab, hs', ht'⟩
  dsimp at ho ha
  subst objects arrows
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hob hab hs' ht'
  subst ob ab source target
  let G : AlgebraicGeometry.GroupoidInAlgebraicSpaces site S hS baseA :=
    ⟨UA, RA, qU, qR, ObjectProperty.homMk j'.source.left,
      ObjectProperty.homMk j'.target.left, so, htOver, comp, co, pg⟩
  have hj : AlgebraicGeometry.Space.groupoidPreRelation G = j' := by
    apply prod.hom_ext <;>
      simp only [AlgebraicGeometry.Space.groupoidPreRelation, G, prod.lift_fst, prod.lift_snd] <;>
      apply Over.OverMorphism.ext <;> rfl
  have hrel : IsEquivalenceRelation
      (AlgebraicGeometry.Space.groupoidPreRelation G).target
      (AlgebraicGeometry.Space.groupoidPreRelation G).source := by
    rwa [hj]
  have hQG := isAlgebraicSpace_quotient_groupoidInAlgebraicSpaces
    site S hS G hrel hs ht hsfp htfp
  rwa [hj] at hQG

/-- A field-valued point of `F` dominating the image of a field-valued point `x` of `X`
is the image of a restriction of `x`. -/
private theorem exists_app_map_value_eq_of_dominates
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {X F : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ F)
    (x : AlgebraicGeometry.Space.FieldValuedPoint site S hS X)
    (r : AlgebraicGeometry.Space.FieldValuedPoint site S hS F)
    (h : AlgebraicGeometry.Space.FieldValuedPoint.Dominates site S hS F r
      (AlgebraicGeometry.Space.FieldValuedPoint.map site S hS X f x)) :
    ∃ e : r.siteObject site S hS F ⟶ x.siteObject site S hS X,
      (f.app (Opposite.op (r.siteObject site S hS F))).hom (X.map e.op x.value) = r.value := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, ?_⟩
  calc
    (f.app (Opposite.op (r.siteObject site S hS F))).hom (X.map e.op x.value) =
        F.map e.op ((AlgebraicGeometry.Space.FieldValuedPoint.map site S hS X f x).value) :=
      congrArg (fun g => g x.value) (f.naturality e.op)
    _ = r.value := by simpa [AlgebraicGeometry.Space.FieldValuedPoint.map] using he

private theorem isSurjective_pullback_of_isSurjective
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    {X F : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ F) (hsurj : AlgebraicGeometry.Space.IsSurjective site S hS f)
    (T : AlgebraicGeometry.BigFppfOver site S hS) (ξ : yoneda.obj T ⟶ F) :
    AlgebraicGeometry.Space.IsSurjective site S hS (pullback.fst ξ f) := by
  intro y
  obtain ⟨q, rfl⟩ := Quot.exists_rep y
  obtain ⟨xclass, hx⟩ := hsurj
    (AlgebraicGeometry.Space.pointsMap site S hS (yoneda.obj T) ξ
      (q.class site S hS (yoneda.obj T)))
  obtain ⟨x, rfl⟩ := Quot.exists_rep xclass
  have hclasses :
      (AlgebraicGeometry.Space.FieldValuedPoint.map site S hS X f x).class site S hS F =
        (AlgebraicGeometry.Space.FieldValuedPoint.map site S hS (yoneda.obj T) ξ q).class
          site S hS F := by
    simpa only [AlgebraicGeometry.Space.pointsMap_class] using hx
  obtain ⟨r, hXr, hTr⟩ :=
    (AlgebraicGeometry.Space.FieldValuedPoint.class_eq_class_iff site S hS F
      (AlgebraicGeometry.Space.FieldValuedPoint.map site S hS X f x)
      (AlgebraicGeometry.Space.FieldValuedPoint.map site S hS (yoneda.obj T) ξ q)).mp hclasses
  obtain ⟨eX, hvalueX⟩ := exists_app_map_value_eq_of_dominates site S hS f x r hXr
  obtain ⟨eT, hvalueT⟩ := exists_app_map_value_eq_of_dominates site S hS ξ q r hTr
  let R := r.siteObject site S hS F
  let xR := X.map eX.op x.value
  let tR := (yoneda.obj T).map eT.op q.value
  let α : yoneda.obj R ⟶ X := (yonedaEquiv (F := X)).symm xR
  let β : yoneda.obj R ⟶ yoneda.obj T :=
    (yonedaEquiv (F := yoneda.obj T)).symm tR
  have hcomm : α ≫ f = β ≫ ξ := by
    apply (yonedaEquiv (F := F)).injective
    simp only [yonedaEquiv_comp, α, β, Equiv.apply_symm_apply]
    exact hvalueX.trans hvalueT.symm
  let ℓ : yoneda.obj R ⟶ pullback ξ f := pullback.lift β α hcomm.symm
  let p : AlgebraicGeometry.Space.FieldValuedPoint site S hS (pullback ξ f) := {
    carrier := r.carrier
    field := r.field
    contained := r.contained
    toBase := r.toBase
    value := yonedaEquiv ℓ
  }
  refine ⟨p.class site S hS (pullback ξ f), ?_⟩
  rw [AlgebraicGeometry.Space.pointsMap_class]
  have hdom : AlgebraicGeometry.Space.FieldValuedPoint.Dominates site S hS (yoneda.obj T)
      (AlgebraicGeometry.Space.FieldValuedPoint.map site S hS (pullback ξ f)
        (pullback.fst ξ f) p) q := by
    refine ⟨eT, ?_⟩
    change (yoneda.obj T).map eT.op q.value =
      (pullback.fst ξ f).app (Opposite.op R) (yonedaEquiv ℓ)
    rw [← yonedaEquiv_comp]
    dsimp [ℓ]
    rw [pullback.lift_fst]
    exact (yonedaEquiv.apply_symm_apply tR).symm
  exact Quot.sound ⟨_, AlgebraicGeometry.Space.FieldValuedPoint.dominates_refl site S hS
    (yoneda.obj T) (AlgebraicGeometry.Space.FieldValuedPoint.map site S hS (pullback ξ f)
      (pullback.fst ξ f) p), hdom⟩

private theorem nonempty_iso_of_common_kernelPair
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    [HasSheafify J (Type u)] {R U F Q : Cᵒᵖ ⥤ Type u}
    (hR : Presheaf.IsSheaf J R) (hU : Presheaf.IsSheaf J U)
    (hF : Presheaf.IsSheaf J F) (hQ : Presheaf.IsSheaf J Q)
    (s t : R ⟶ U) (f : U ⟶ F) (q : U ⟶ Q)
    (hf : IsPullback s t f f) (hq : IsPullback s t q q)
    (hfls : Presheaf.IsLocallySurjective J f)
    (hqls : Presheaf.IsLocallySurjective J q) :
    Nonempty (F ≅ Q) := by
  have := hfls
  have := hqls
  let R' : Sheaf J (Type u) := ⟨R, hR⟩
  let U' : Sheaf J (Type u) := ⟨U, hU⟩
  let F' : Sheaf J (Type u) := ⟨F, hF⟩
  let Q' : Sheaf J (Type u) := ⟨Q, hQ⟩
  let s' : R' ⟶ U' := ⟨s⟩
  let t' : R' ⟶ U' := ⟨t⟩
  let f' : U' ⟶ F' := ⟨f⟩
  let q' : U' ⟶ Q' := ⟨q⟩
  have hf' : IsPullback s' t' f' f' :=
    IsPullback.of_map_of_faithful (sheafToPresheaf J (Type u)) hf
  have hq' : IsPullback s' t' q' q' :=
    IsPullback.of_map_of_faithful (sheafToPresheaf J (Type u)) hq
  let : Epi f' := Sheaf.epi_of_isLocallySurjective f'
  let : Epi q' := Sheaf.epi_of_isLocallySurjective q'
  let : IsRegularEpi f' := IsRegularEpiCategory.regularEpiOfEpi f'
  let : IsRegularEpi q' := IsRegularEpiCategory.regularEpiOfEpi q'
  let cf := isColimitCoforkOfEffectiveEpi f' _ hf'.isLimit
  let cq := isColimitCoforkOfEffectiveEpi q' _ hq'.isLimit
  exact ⟨(sheafToPresheaf J (Type u)).mapIso (cf.coconePointUniqueUpToIso cq)⟩

private theorem isAlgebraicSpace_quotient_kernelPairPreRelation
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u)]
    {X F : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ F) (hX : AlgebraicGeometry.IsAlgebraicSpace site S hS X)
    (hrep : AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces site S hS f)
    (hflat : AlgebraicGeometry.Space.HasProperty site S hS
      (fun ⦃_ _⦄ φ => AlgebraicGeometry.Space.IsFlat site S hS φ.hom) f hrep)
    (hlfp : AlgebraicGeometry.Space.HasProperty site S hS
      (fun ⦃_ _⦄ φ => AlgebraicGeometry.Space.IsLocallyOfFinitePresentation site S hS φ.hom)
      f hrep) :
    AlgebraicGeometry.IsAlgebraicSpace site S hS
      (AlgebraicGeometry.Space.quotientSheaf
        (kernelPairPreRelation site S hS f hX hrep)).obj := by
  let j := kernelPairPreRelation site S hS f hX hrep
  let : IsEquivalenceRelation j.target j.source :=
    kernelPairPreRelation_isEquivalenceRelation site S hS f hX hrep
  have hfstFlat : AlgebraicGeometry.Space.IsFlat site S hS (pullback.fst f f) :=
    chartProperty_pullback_of_scheme_baseChanges site S hS _
      AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget f f hX hrep hflat
  have hfstLfp :
      AlgebraicGeometry.Space.IsLocallyOfFinitePresentation site S hS (pullback.fst f f) :=
    chartProperty_pullback_of_scheme_baseChanges site S hS _
      AlgebraicGeometry.LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
      f f hX hrep hlfp
  have hsndFlat : AlgebraicGeometry.Space.IsFlat site S hS (pullback.snd f f) := by
    simpa only [pullbackSymmetry_hom_comp_fst] using
      chartProperty_precomp_iso site S hS _ (pullbackSymmetry f f) _ hfstFlat
  have hsndLfp :
      AlgebraicGeometry.Space.IsLocallyOfFinitePresentation site S hS (pullback.snd f f) := by
    simpa only [pullbackSymmetry_hom_comp_fst] using
      chartProperty_precomp_iso site S hS _ (pullbackSymmetry f f) _ hfstLfp
  apply isAlgebraicSpace_quotient_preRelation site S hS
    (AlgebraicGeometry.isAlgebraicSpace_yoneda site S hS (terminalSiteObject site S hS))
    (kernelPair_isAlgebraicSpace site S hS f hX hrep) hX j
  · change AlgebraicGeometry.Space.IsFlat site S hS
      (kernelPairPreRelation site S hS f hX hrep).source.left
    rwa [kernelPairPreRelation_source]
  · change AlgebraicGeometry.Space.IsFlat site S hS
      (kernelPairPreRelation site S hS f hX hrep).target.left
    rwa [kernelPairPreRelation_target]
  · change AlgebraicGeometry.Space.IsLocallyOfFinitePresentation site S hS
      (kernelPairPreRelation site S hS f hX hrep).source.left
    rwa [kernelPairPreRelation_source]
  · change AlgebraicGeometry.Space.IsLocallyOfFinitePresentation site S hS
      (kernelPairPreRelation site S hS f hX hrep).target.left
    rwa [kernelPairPreRelation_target]

/-- Condition (3) with surjectivity read, like flatness and local finite presentation, on
every scheme-valued base change of `f`.

It implies `isAlgebraicSpace_of_representable_surjective_flat_locallyOfFinitePresentation`,
since a surjection of presheaves representable by algebraic spaces is surjective on every base
change. -/
@[stacks 04S6 "part (3), surjectivity on base changes"]
public theorem
    isAlgebraicSpace_of_representable_hasProperty_surjective_flat_locallyOfFinitePresentation
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    (F : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS) F)
    {X : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace site S hS X)
    (f : X ⟶ F)
    (hrep : AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces site S hS f)
    (hsurj : AlgebraicGeometry.Space.HasProperty site S hS
      (fun ⦃_ _⦄ φ => AlgebraicGeometry.Space.IsSurjective site S hS φ.hom) f hrep)
    (hflat : AlgebraicGeometry.Space.HasProperty site S hS
      (fun ⦃_ _⦄ φ => AlgebraicGeometry.Space.IsFlat site S hS φ.hom) f hrep)
    (hlfp : AlgebraicGeometry.Space.HasProperty site S hS
      (fun ⦃_ _⦄ φ => AlgebraicGeometry.Space.IsLocallyOfFinitePresentation site S hS φ.hom)
      f hrep) :
    AlgebraicGeometry.IsAlgebraicSpace site S hS F := by
  let := AlgebraicGeometry.essentiallySmall_bigFppfOver site S hS
  let : HasSheafify (AlgebraicGeometry.BigFppfOver.topology site S hS) (Type u) :=
    hasSheafifyEssentiallySmallSite _ _
  let j := kernelPairPreRelation site S hS f hX hrep
  let : IsEquivalenceRelation j.target j.source :=
    kernelPairPreRelation_isEquivalenceRelation site S hS f hX hrep
  have hQ : AlgebraicGeometry.IsAlgebraicSpace site S hS
      (AlgebraicGeometry.Space.quotientSheaf j).obj :=
    isAlgebraicSpace_quotient_kernelPairPreRelation site S hS f hX hrep hflat hlfp
  let q := AlgebraicGeometry.Space.toQuotientSheaf j
  let J := AlgebraicGeometry.BigFppfOver.topology site S hS
  obtain ⟨e⟩ := nonempty_iso_of_common_kernelPair J
    (kernelPair_isAlgebraicSpace site S hS f hX hrep).isSheaf hX.isSheaf hF hQ.isSheaf
    (pullback.fst f f) (pullback.snd f f) f q (IsPullback.of_hasPullback f f)
    (quotient_kernelPair_isPullback site S hS f hX hrep hQ)
    (AlgebraicGeometry.Space.isLocallySurjective_of_isRepresentableByAlgebraicSpaces
      site S hS hX.isSheaf hF f hrep hflat hlfp hsurj)
    (AlgebraicGeometry.Space.isLocallySurjective_toQuotientSheaf j)
  exact isAlgebraicSpace_of_iso site S hS e hQ

/-- Condition (3): a representable, surjective, flat, locally finitely
presented map from an algebraic space presents an algebraic space. -/
@[stacks 04S6 "part (3)"]
public theorem isAlgebraicSpace_of_representable_surjective_flat_locallyOfFinitePresentation
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    (F : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS) F)
    {X : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace site S hS X)
    (f : X ⟶ F)
    (hrep : AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces site S hS f)
    (hsurj : AlgebraicGeometry.Space.IsSurjective site S hS f)
    (hflat : AlgebraicGeometry.Space.HasProperty site S hS
      (fun ⦃_ _⦄ φ => AlgebraicGeometry.Space.IsFlat site S hS φ.hom) f hrep)
    (hlfp : AlgebraicGeometry.Space.HasProperty site S hS
      (fun ⦃_ _⦄ φ => AlgebraicGeometry.Space.IsLocallyOfFinitePresentation site S hS φ.hom)
      f hrep) :
    AlgebraicGeometry.IsAlgebraicSpace site S hS F :=
  isAlgebraicSpace_of_representable_hasProperty_surjective_flat_locallyOfFinitePresentation
    site S hS F hF hX f hrep
    (isSurjective_pullback_of_isSurjective site S hS f hsurj) hflat hlfp

/-- Condition (4) with surjectivity read on every scheme-valued base change of `f`:
`isAlgebraicSpace_of_representable_hasProperty_surjective_flat_locallyOfFinitePresentation`
with a scheme as the source. -/
@[stacks 04S6 "part (4), surjectivity on base changes"]
public theorem
    isAlgebraicSpace_of_representable_hasProperty_surjective_flat_locallyOfFinitePresentation_scheme
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    (F : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS) F)
    (U : AlgebraicGeometry.BigFppfOver site S hS)
    (f : yoneda.obj U ⟶ F)
    (hrep : AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces site S hS f)
    (hsurj : AlgebraicGeometry.Space.HasProperty site S hS
      (fun ⦃_ _⦄ φ => AlgebraicGeometry.Space.IsSurjective site S hS φ.hom) f hrep)
    (hflat : AlgebraicGeometry.Space.HasProperty site S hS
      (fun ⦃_ _⦄ φ => AlgebraicGeometry.Space.IsFlat site S hS φ.hom) f hrep)
    (hlfp : AlgebraicGeometry.Space.HasProperty site S hS
      (fun ⦃_ _⦄ φ => AlgebraicGeometry.Space.IsLocallyOfFinitePresentation site S hS φ.hom)
      f hrep) :
    AlgebraicGeometry.IsAlgebraicSpace site S hS F :=
  isAlgebraicSpace_of_representable_hasProperty_surjective_flat_locallyOfFinitePresentation
    site S hS F hF (AlgebraicGeometry.isAlgebraicSpace_yoneda site S hS U) f hrep
    hsurj hflat hlfp

/-- Condition (4): the preceding criterion with a scheme as the source. -/
@[stacks 04S6 "part (4)"]
public theorem isAlgebraicSpace_of_representable_surjective_flat_locallyOfFinitePresentation_scheme
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    (F : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS) F)
    (U : AlgebraicGeometry.BigFppfOver site S hS)
    (f : yoneda.obj U ⟶ F)
    (hrep : AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces site S hS f)
    (hsurj : AlgebraicGeometry.Space.IsSurjective site S hS f)
    (hflat : AlgebraicGeometry.Space.HasProperty site S hS
      (fun ⦃_ _⦄ φ => AlgebraicGeometry.Space.IsFlat site S hS φ.hom) f hrep)
    (hlfp : AlgebraicGeometry.Space.HasProperty site S hS
      (fun ⦃_ _⦄ φ => AlgebraicGeometry.Space.IsLocallyOfFinitePresentation site S hS φ.hom)
      f hrep) :
    AlgebraicGeometry.IsAlgebraicSpace site S hS F :=
  isAlgebraicSpace_of_representable_surjective_flat_locallyOfFinitePresentation
    site S hS F hF (AlgebraicGeometry.isAlgebraicSpace_yoneda site S hS U)
    f hrep hsurj hflat hlfp

/-- Condition (5): a sheaf with diagonal representable by algebraic spaces
and a surjective flat locally finitely presented algebraic-space presentation
is an algebraic space. -/
@[stacks 04S6 "part (5)"]
public theorem isAlgebraicSpace_of_representableDiagonal_surjective_flat_locallyOfFinitePresentation
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    (F : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS) F)
    (hdiag : AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces site S hS (diag F))
    {X : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace site S hS X)
    (f : X ⟶ F)
    (hsurj : AlgebraicGeometry.Space.IsSurjective site S hS f)
    (hflat : ∀ (T : AlgebraicGeometry.BigFppfOver site S hS)
      (ξ : yoneda.obj T ⟶ F),
      AlgebraicGeometry.Space.IsFlat site S hS (pullback.fst ξ f))
    (hlfp : ∀ (T : AlgebraicGeometry.BigFppfOver site S hS)
      (ξ : yoneda.obj T ⟶ F),
      AlgebraicGeometry.Space.IsLocallyOfFinitePresentation site S hS
        (pullback.fst ξ f)) :
    AlgebraicGeometry.IsAlgebraicSpace site S hS F := by
  let : HasBinaryProducts (AlgebraicGeometry.BigFppfOver site S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hrep : AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces site S hS f :=
    ((AlgebraicGeometry.Space.forall_yoneda_isRepresentableByAlgebraicSpaces_iff_isAlgebraicSpace
      site S hS F).mp
      ((AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_diag_iff_forall_yoneda
        site S hS F).mp hdiag)) X hX f
  exact isAlgebraicSpace_of_representable_surjective_flat_locallyOfFinitePresentation
    site S hS F hF hX f hrep hsurj (fun T ξ => hflat T ξ) (fun T ξ => hlfp T ξ)

/-- Condition (6): a scheme presentation suffices when the diagonal is
representable by schemes. -/
@[stacks 04S6 "part (6)"]
public theorem
    isAlgebraicSpace_of_representableDiagonal_surjective_flat_locallyOfFinitePresentation_scheme
    (site : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : site.Contains S)
    (F : (AlgebraicGeometry.BigFppfOver site S hS)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology site S hS) F)
    (hdiag : yoneda.relativelyRepresentable (diag F))
    (U : AlgebraicGeometry.BigFppfOver site S hS)
    (f : yoneda.obj U ⟶ F)
    (hsurj : AlgebraicGeometry.Space.IsSurjective site S hS f)
    (hflat : ∀ (T : AlgebraicGeometry.BigFppfOver site S hS)
      (ξ : yoneda.obj T ⟶ F),
      AlgebraicGeometry.Space.IsFlat site S hS (pullback.fst ξ f))
    (hlfp : ∀ (T : AlgebraicGeometry.BigFppfOver site S hS)
      (ξ : yoneda.obj T ⟶ F),
      AlgebraicGeometry.Space.IsLocallyOfFinitePresentation site S hS
        (pullback.fst ξ f)) :
    AlgebraicGeometry.IsAlgebraicSpace site S hS F := by
  have hrep : AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces site S hS f :=
    isRepresentableByAlgebraicSpaces_of_relativelyRepresentable site S hS f
      ((Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := F)).mp
        hdiag f)
  exact isAlgebraicSpace_of_representable_surjective_flat_locallyOfFinitePresentation_scheme
    site S hS F hF U f hrep hsurj (fun T ξ => hflat T ξ) (fun T ξ => hlfp T ξ)

end AlgebraicGeometry.Bootstrap04S6

end
