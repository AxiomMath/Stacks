module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianValuativeProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalTFAE
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionUniqueness
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeUniquenessSeparated
import StacksFrontier.AlgebraicGeometry.Spaces.ProperFpqcLocalAtTarget
import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessBaseChange
import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
import StacksFrontier.AlgebraicGeometry.Stacks.GerbeRelativeDiagonalDescent
import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalFiniteType
import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalRepresentable
import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyFppfCoverGeneral
import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
import StacksFrontier.AlgebraicGeometry.Stacks.SchemePointBaseChange
import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismMonotone
import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange

/-!
# The Noetherian valuative criterion for separatedness (Stacks 0E80)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` with `𝒴` locally Noetherian and
`f` locally of finite type and quasi-separated. **Stacks 0E80** says that `f` is separated as soon
as the category of dotted arrows of every valuative diagram for `f` whose valuation ring is a
*discrete* valuation ring is either empty or a setoid with exactly one isomorphism class.

## Main results

* `AlgebraicGeometry.Stack.ValuativeCriterion.DiscreteUniqueness`: the hypothesis of
  **Stacks 0E80**, the uniqueness part of the valuative criterion (**Stacks 0CLG**) restricted to
  discrete valuation rings.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_of_discreteUniqueness`: **Stacks 0E80**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_of_discreteLift`: the assembly of
  Stacks 0E80 from the Noetherian valuative criterion for properness of a morphism of algebraic
  spaces (**Stacks 0ARK**), with the valuative input carried as the hypothesis `hlift` discussed
  below.

## Implementation notes

Separatedness of `f` is properness of `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` in the relative sense of Stacks 04XB,
so it is a condition on every algebraic space representing a base change of `Δ_f` along a
scheme-valued point of `𝒳 ×_𝒴 𝒳`; the Noetherian hypothesis survives at no such point, since the
test scheme is an arbitrary object of the site. The route is therefore the chart reduction of
**Stacks 0CPP**: `𝒳 ×_𝒴 𝒳` is locally Noetherian, being locally of finite type over `𝒳` (the
first projection is a base change of `f`) which is locally of finite type over `𝒴` by
**Stacks 06R6**; a locally Noetherian scheme chart `U` of `𝒳 ×_𝒴 𝒳` is a surjective, flat,
locally finitely presented cover, and Stacks 0CPP reduces properness of `Δ_f` to the relative
property of the projection `U ×_{𝒳 ×_𝒴 𝒳} 𝒳 ⟶ U`. Over the *represented* base `U` that relative
property is a single morphism of algebraic spaces over `S` (the bridge
`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap` of the Stacks 04XB
conventions), namely — by `AlgebraicGeometry.Stack.representingMap_relocalizeFibre` — the
structural morphism of the lower-shriek extension of the algebraic space over `U` representing the
base change of `Δ_f` along the chart. **Stacks 0ARK** applies to that morphism over the site of
`U`, where the base is the representable algebraic space of the terminal object; its three
non-valuative hypotheses are local Noetherianity of `U`, finiteness of type of `Δ_f` —
quasi-compactness being the first conjunct of quasi-separatedness of `f` and local finiteness of
type part (2) of **Stacks 04XS** — and quasi-separatedness of `Δ_f`, the second conjunct. Those
are read over `S` at the chart and carried to the site of `U` by the base-change independence
results of `StacksFrontier/AlgebraicGeometry/Spaces/ProperSmallerBase.lean`, and properness is
carried back the same way.

The chart produced by **Stacks 04YG** is a 1-morphism out of the slice of the site of `S` at `U`,
while a scheme-valued point in the sense of Stacks 04XB is a 1-morphism out of the big fppf site
of `U`; the two are exchanged by the equivalence `CategoryTheory.Over.iteratedSliceBackward`,
along which surjectivity, flatness and local finite presentation are invariant.

## How the valuative input is discharged

`AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_of_discreteLift` takes that input as the
explicit hypothesis `hlift`: for every scheme-valued point of `𝒳 ×_𝒴 𝒳` and every algebraic space
`F` representing the base change of `Δ_f` along it, every valuative square for the structural
morphism of `F` whose valuation ring is discrete has exactly one lift. That is the shape
Stacks 0ARK consumes, and
`AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_of_discreteUniqueness` supplies it from
`AlgebraicGeometry.Stack.ValuativeCriterion.DiscreteUniqueness` through the point-level transfers
of `StacksFrontier/AlgebraicGeometry/Stacks/ValuativeCriterionExistencePoints.lean` (existence of a
lift, **Stacks 0CLN**) and
`StacksFrontier/AlgebraicGeometry/Stacks/ValuativeCriterionUniquenessPoints.lean` (uniqueness of a
lift, **Stacks 0CLJ**), both of which pass a restriction on the valuation ring through unchanged,
composed with the two `Δ_f`-side results of **Stacks 0E8L**. No step extends the fraction field or
passes to a dominating valuation ring, so the restriction to *discrete* valuation rings survives
intact — which is exactly what the Noetherian form of the criterion buys.

## References

* [Stacks Project, Tag 0E80](https://stacks.math.columbia.edu/tag/0E80)
* [Stacks Project, Tag 0ARK](https://stacks.math.columbia.edu/tag/0ARK)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04YG](https://stacks.math.columbia.edu/tag/04YG)
* [Stacks Project, Tag 06R6](https://stacks.math.columbia.edu/tag/06R6)
* [Stacks Project, Tag 0CLG](https://stacks.math.columbia.edu/tag/0CLG)
* [Stacks Project, Tag 0CPP](https://stacks.math.columbia.edu/tag/0CPP)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

namespace ValuativeCriterion

/-- **The hypothesis of Stacks 0E80.** A 1-morphism of algebraic stacks over `S` satisfies the
*discrete* uniqueness part of the valuative criterion when, for every valuative diagram for it
whose valuation ring is a discrete valuation ring, the category of dotted arrows is either empty
or a setoid with exactly one isomorphism class.

This is `AlgebraicGeometry.Stack.ValuativeCriterion.Uniqueness` of **Stacks 0CLG** with the extra
clause `IsDiscreteValuationRing D.R`. The ring and domain structures of the valuation ring of a
`AlgebraicGeometry.Stack.ValuativeDiagram` are fields of the structure which are not registered as
instances — the proofs that need them write `letI := D.ring` — so they are supplied explicitly
here. -/
abbrev DiscreteUniqueness (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ D : ValuativeDiagram B S hS 𝒳 𝒴 f, @IsDiscreteValuationRing D.R D.ring D.domain →
    IsSetoidCategory (CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ) ∧
      ∀ a b : CategoryTheory.DottedArrow D.x D.j f.hom D.y D.γ, Nonempty (a ≅ b)

end ValuativeCriterion

namespace AlgebraicStacks

/-- **Being locally of finite type is unchanged, for the structural morphism of a lower-shriek
extension, by a change of the base scheme.** This is
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff` at
`AlgebraicGeometry.LocallyOfFiniteType`, local finiteness of type of a morphism of algebraic
spaces being an every-étale-chart condition. -/
private theorem isLocallyOfFiniteType_relocalizeToYoneda_iff (W : Scheme.{u})
    (hW : B.Contains W) (h : B.obj hW ⟶ B.obj hS)
    (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u) :
    Space.IsLocallyOfFiniteType B S hS (OverShriek.relocalizeToYoneda h F) ↔
      Space.IsLocallyOfFiniteType B W hW (Space.toYonedaId B W hW F) :=
  Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B W S hW hS h
    (@AlgebraicGeometry.LocallyOfFiniteType.{u}) F

/-- **The assembly of Stacks 0E80**, with the valuative input taken as the hypothesis `hlift`.

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` with `𝒴` locally Noetherian and `f`
locally of finite type and quasi-separated. Assume that for every scheme-valued point `y` of
`𝒳 ×_𝒴 𝒳` over an object `U` of the site, every algebraic space `F` over `U` representing the base
change of `Δ_f` along `y`, and every morphism `p` from `F` to the representable algebraic space of
the terminal object of the site of `U`, each valuative square for `p` whose valuation ring is a
discrete valuation ring has exactly one lift. Then `f` is separated.

The hypothesis `hlift` is the hypothesis of **Stacks 0ARK** for the base change of `Δ_f` along a
scheme-valued point; see the module documentation for how it is to be discharged from
`AlgebraicGeometry.Stack.ValuativeCriterion.DiscreteUniqueness`. -/
private theorem isSeparated_of_discreteLift (f : 𝒳 ⟶ 𝒴)
    (hY : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hqs : IsQuasiSeparated B S hS f)
    (hlift : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ (twoFibreProduct B S hS f f).val.val.obj)
      (_hy : y ⋙ (twoFibreProduct B S hS f f).val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (_e : StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p
          (twoFibreProduct B S hS f f).val.val.p y
          (CatFiberedInGroupoids.homFunctor (relativeDiagonal B S hS f).hom))
        (presheafOfCategories (F ⋙ typeToCat)).p)
      (p : F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj U.left.2))))
      (q : Space.ValuativeSquare p), IsDiscreteValuationRing q.R →
        Nonempty q.Lift ∧ Subsingleton q.Lift) :
    IsSeparated B S hS f := by
  classical
  -- the properties of morphisms of algebraic spaces the relative conditions are tested at
  have _ : (Space.properProperty B S hS).IsStableUnderBaseChange :=
    Space.isProper_isStableUnderBaseChange B S hS
  have _ : (Space.properProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.proper_isLocalAtTarget_fppf B S hS
  have _ : MorphismProperty.RespectsIso (Space.quasiCompactProperty B S hS) :=
    (Space.isQuasiCompact_isStableUnderBaseChange B S hS).respectsIso
  have _ : MorphismProperty.RespectsIso (Space.quasiSeparatedProperty B S hS) :=
    (Space.isQuasiSeparated_isStableUnderBaseChange B S hS).respectsIso
  have _ : MorphismProperty.RespectsIso (Space.locallyOfFiniteTypeProperty B S hS) :=
    (Space.isLocallyOfFiniteType_isStableUnderBaseChange B S hS).respectsIso
  -- Stacks 06R6 twice: `𝒳 ×_𝒴 𝒳` is locally Noetherian
  have hXN : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒳 :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS f hft hY
  have hfstft : IsLocallyOfFiniteType B S hS (twoFibreProductSquare B S hS f f).fst :=
    isLocallyOfFiniteType_baseChange B S hS f f (twoFibreProductSquare B S hS f f)
      (isTwoFibreProduct_twoFibreProductSquare B S hS f f) hft
  obtain ⟨U, gpres, hgsurj, hgsm, hUN⟩ :
      HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T)
        (twoFibreProduct B S hS f f) :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS _ hfstft hXN
  -- the chart, read on the big fppf site of `U` instead of the slice of the site of `S` at `U`
  have hbe : Functor.IsEquivalence (Over.iteratedSliceBackward U) :=
    (Over.iteratedSliceEquiv U).isEquivalence_inverse
  let kU : schemeSliceStack.{u, w} B S hS U ⟶ schemeStack.{u, w} B S hS U :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
      (⟨Over.iteratedSliceBackward U, Over.iteratedSliceBackward_forget U⟩ :
        (schemeSliceStack.{u, w} B S hS U).val.val ⥤ᵇ
          (schemeStack.{u, w} B S hS U).val.val))
  have hkUe : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor kU.hom) := hbe
  -- the chart as a scheme-valued point of `𝒳 ×_𝒴 𝒳`
  let y : BigFppfOver B U.left.1 U.left.2 ⥤ (twoFibreProduct B S hS f f).val.val.obj :=
    CatFiberedInGroupoids.homFunctor (kU ≫ gpres).hom
  have hy : y ⋙ (twoFibreProduct B S hS f f).val.val.p = Over.map U.hom :=
    CatFiberedInGroupoids.homFunctor_comp_p (kU ≫ gpres).hom
  let c : schemeSliceStack.{u, w} B S hS U ⟶ twoFibreProduct B S hS f f :=
    schemeSliceStackMap.{u, w} B S hS U y hy
  have hcsurj : Stack.IsSurjective B S hS c :=
    isSurjective_comp_of_isEquivalence B S hS kU gpres hkUe hgsurj
  have hcflat : IsFlat B S hS c :=
    isFlat_comp_of_isEquivalence B S hS kU gpres hkUe (isFlat_of_isSmooth B S hS gpres hgsm)
  have hclfp : IsLocallyOfFinitePresentation B S hS c :=
    isLocallyOfFinitePresentation_comp_of_isEquivalence B S hS kU gpres hkUe
      (isLocallyOfFinitePresentation_of_isSmooth B S hS gpres hgsm)
  -- the algebraic space over `U` representing the base change of `Δ_f` along the chart
  have hΔrep : Stack.IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonal B S hS f).hom.hom :=
    Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f
  obtain ⟨F, hF, ⟨e⟩⟩ := hΔrep U y hy
  -- local Noetherianity of the base over the site of `U`
  have hNoethU : Space.HasEtaleLocalProperty B U.left.1 U.left.2
      (yoneda.obj (Over.mk (𝟙 (B.obj U.left.2))))
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    (Space.exists_atlas_iff_of_representable B U.left.1 U.left.2
      (yoneda.obj (Over.mk (𝟙 (B.obj U.left.2))))
      (fun T : Scheme.{u} => IsLocallyNoetherian T) (Over.mk (𝟙 (B.obj U.left.2)))
      (Iso.refl _)).mpr hUN
  -- the three non-valuative hypotheses of Stacks 0ARK, read over `S` at the chart
  have hqcS : Space.IsQuasiCompact B S hS (OverShriek.relocalizeToYoneda U.hom F) :=
    (Stack.prop_algebraicSpaceMap_iff B S hS (Space.quasiCompactProperty B S hS) U F hF).mp
      (hqs.1 U y hy F hF ⟨e⟩)
  have hqsS : Space.IsQuasiSeparated B S hS (OverShriek.relocalizeToYoneda U.hom F) :=
    (Stack.prop_algebraicSpaceMap_iff B S hS (Space.quasiSeparatedProperty B S hS) U F hF).mp
      (hqs.2 U y hy F hF ⟨e⟩)
  have hftS : Space.IsLocallyOfFiniteType B S hS (OverShriek.relocalizeToYoneda U.hom F) :=
    (Stack.prop_algebraicSpaceMap_iff B S hS (Space.locallyOfFiniteTypeProperty B S hS)
        U F hF).mp
      ((Stack.isLocallyOfFiniteType_relativeDiagonal_of_isAlgebraicStack B S hS f).2
        U y hy F hF ⟨e⟩)
  -- Stacks 0ARK over the site of `U`
  have hproperU : Space.IsProper B U.left.1 U.left.2
      (Space.toYonedaId B U.left.1 U.left.2 F) :=
    Space.isProper_of_isQuasiSeparated_of_discreteValuativeCriterion B U.left.1 U.left.2 hF
      (isAlgebraicSpace_yoneda B U.left.1 U.left.2 _) _ hNoethU
      ⟨(isLocallyOfFiniteType_relocalizeToYoneda_iff B S hS U.left.1 U.left.2 U.hom F).mp hftS,
        (Space.isQuasiCompact_relocalizeToYoneda_iff B U.left.1 S U.left.2 hS U.hom F).mp hqcS⟩
      ((Space.isQuasiSeparated_relocalizeToYoneda_iff B U.left.1 S U.left.2 hS U.hom F).mp hqsS)
      (hlift U y hy F e _)
  -- and back over `S`
  have hproperS : Space.IsProper B S hS (OverShriek.relocalizeToYoneda U.hom F) :=
    (Space.isProper_relocalizeToYoneda_iff B U.left.1 S U.left.2 hS U.hom F hF).mpr hproperU
  -- Stacks 0CPP along the chart
  have hQ : Bicategory.IsTwoFibreProduct
      (twoFibreProductSquare B S hS c (relativeDiagonal B S hS f)) :=
    isTwoFibreProduct_twoFibreProductSquare B S hS c (relativeDiagonal B S hS f)
  have hfstrep : Stack.IsRepresentableByAlgebraicSpaces B S hS
      (twoFibreProductSquare B S hS c (relativeDiagonal B S hS f)).fst.hom.hom :=
    Stack.isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS 𝒳.val
      (twoFibreProduct B S hS f f).val (schemeSliceStack.{u, w} B S hS U).val
      (relativeDiagonal B S hS f).hom c.hom
      (toCatFiberedInGroupoids B S hS
        (twoFibreProductSquare B S hS c (relativeDiagonal B S hS f)))
      (isTwoFibreProduct_toCatFiberedInGroupoids B S hS _ hQ) hΔrep
  have hV := isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom F hF
  -- over the represented base `U` the relative property is a single morphism of algebraic spaces,
  -- which by Stacks 04SW is the structural morphism of the lower-shriek extension
  have key : Space.properProperty B S hS
      (ObjectProperty.homMk (OverShriek.relocalizeToYoneda U.hom F) :
        (⟨(OverShriek.relocalizePresheafFunctor U.hom).obj F,
            hV⟩ :
          AlgebraicSpaces B S hS) ⟶
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)) :=
    hproperS
  rw [← Stack.representingMap_relocalizeFibre B S hS U
    (relativeDiagonal B S hS f).hom y F e hy] at key
  refine (Stack.hasRelativeProperty_iff_of_fppfCoverStack B S hS
    (Space.properProperty B S hS) (relativeDiagonal B S hS f) c hΔrep hcsurj hcflat hclfp
    (twoFibreProductSquare B S hS c (relativeDiagonal B S hS f)) hQ).2 ⟨hfstrep, ?_⟩
  exact (Stack.hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
    (Space.properProperty B S hS)
    (twoFibreProductSquare B S hS c (relativeDiagonal B S hS f)).fst.hom hfstrep
    ((OverShriek.relocalizePresheafFunctor U.hom).obj F) (yoneda.obj U)
    hV
    (isAlgebraicSpace_yoneda B S hS U)
    (Stack.relocalizeFibreEquivalence B S hS U (relativeDiagonal B S hS f).hom y F e)
    (Stack.schemeSliceEquivalenceOver B S hS U)).2 key

/-- **Stacks 0E80, the Noetherian valuative criterion for separatedness.** Let `f : 𝒳 ⟶ 𝒴` be a
1-morphism of algebraic stacks over `S` with `𝒴` locally Noetherian and `f` locally of finite type
and quasi-separated. If, for every valuative diagram for `f` whose valuation ring is a *discrete*
valuation ring, the category of dotted arrows is either empty or a setoid with exactly one
isomorphism class, then `f` is separated.

Separatedness is properness of `Δ_f` in the relative sense of Stacks 04XB, and
`AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_of_discreteLift` reduces it, along a locally
Noetherian scheme chart of `𝒳 ×_𝒴 𝒳`, to the full valuative criterion at discrete valuation rings
for the algebraic spaces representing the base changes of `Δ_f`. Both halves of that criterion
come from the hypothesis through the two transfers of Stacks 0CLN and Stacks 0CLJ, each of which
carries a restriction on the valuation ring through unchanged:

* a lift exists by `AlgebraicGeometry.Stack.nonempty_lift_baseChange_point`, whose input is a
  dotted arrow for a valuative *square* for `Δ_f` over the same valuation ring; reading that
  square as a valuative diagram, Stacks 0E8L builds it from the hypothesis through
  `AlgebraicGeometry.Stack.nonempty_dottedArrow_relativeDiagonal_of_pred`;
* it is unique by `AlgebraicGeometry.Stack.subsingleton_lift_baseChange_point`, whose input is the
  isomorphism of any two dotted arrows of a valuative diagram for `Δ_f`, which is
  `AlgebraicGeometry.Stack.nonempty_iso_dottedArrow_relativeDiagonal_of_pred`.

The valuation ring never changes along the way — no extension of the fraction field and no passage
to a dominating valuation ring — so "discrete" survives every step, which is the whole point of
the Noetherian form of the criterion. -/
@[stacks 0E80 "a quasi-separated 1-morphism of algebraic stacks, locally of finite type over a
locally Noetherian target, is separated as soon as the uniqueness part of the valuative criterion
holds at every discrete valuation ring"]
theorem isSeparated_of_discreteUniqueness (f : 𝒳 ⟶ 𝒴)
    (hY : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒴)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hqs : IsQuasiSeparated B S hS f)
    (H : ValuativeCriterion.DiscreteUniqueness B S hS f) :
    IsSeparated B S hS f :=
  let P : ∀ R : Type u, [CommRing R] → [IsDomain R] → [ValuationRing R] → Prop :=
    fun R i d _ => @IsDiscreteValuationRing R i d
  isSeparated_of_discreteLift B S hS f hY hft hqs
    (fun U y hy F e p q hq =>
      ⟨nonempty_lift_baseChange_point B S hS (relativeDiagonal B S hS f)
          P
          (fun Q hQ => nonempty_dottedArrow_relativeDiagonal_of_pred B S hS f
            P (fun D hD => (H D hD).2)
            (ValuativeSquare.toValuativeDiagram B S hS Q) hQ)
          U y hy F e p q hq,
        subsingleton_lift_baseChange_point B S hS (relativeDiagonal B S hS f)
          P
          (fun D hD => nonempty_iso_dottedArrow_relativeDiagonal_of_pred B S hS f
            P (fun D' hD' => (H D' hD').1) D hD)
          U y hy F e p q hq⟩)

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
