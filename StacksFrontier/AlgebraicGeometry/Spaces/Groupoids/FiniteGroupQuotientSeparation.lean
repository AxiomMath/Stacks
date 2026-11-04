module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FiniteGroupQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import StacksFrontier.CategoryTheory.Limits.BinaryProductDiagonal

/-!
# Separation of the quotient of a scheme by a finite group action

Let a finite group `G` act on a scheme `U` over `S` so that every nonidentity element
fixing a point acts nontrivially on the residue field there. The graph relation
`j : R ⟶ U ×_S U` of the action is then the base change of the diagonal of the quotient
`U/G` along the square of the quotient map, so a property of scheme morphisms that is
stable under base change and fppf local on the target passes from `j` to the diagonal of
`U/G`. Applied to closed immersions and to quasi-compact morphisms this gives the two
separation statements of Stacks 02Z4.

## Main results

* `AlgebraicGeometry.Space.presheaf_diag_actionQuotient`: a base-change-stable,
  fppf-locally-testable property of scheme morphisms passes from the graph relation of the
  action to the diagonal of the quotient.
* `AlgebraicGeometry.Space.isSeparatedOver_actionQuotient`: the quotient of a scheme
  separated over `S` is separated over `S`.
* `AlgebraicGeometry.Space.isQuasiSeparatedOver_actionQuotient`: the quotient of a scheme
  quasi-separated over `S` is quasi-separated over `S`.

## Implementation notes

The source proof of Stacks 02Z4 reduces both statements to the corresponding property of
`j`, and those two properties of `j` are
`AlgebraicGeometry.Space.isClosedImmersion_actionRelation` and
`AlgebraicGeometry.Space.quasiCompact_actionRelation`. The reduction itself is Stacks 02WZ,
`AlgebraicGeometry.presheaf_inverseImage_iff_atlas_snd`: the square of the quotient
map is a surjective étale representable atlas of `U/G × U/G`, and the base change of the
diagonal along it is `j`. That the base change of a diagonal along a square of a map is the
map's kernel pair is `CategoryTheory.Limits.isPullback_diagonal_prod_of_kernelPair`, and the
kernel pair of the quotient map is the relation by Stacks 02WV,
`AlgebraicGeometry.Space.quotientMap_isPullback`.

The three statements below take the algebraic-space property of the quotient as an explicit
hypothesis `hQ`, and consequently do **not** carry `@[stacks 02Z4]`. In the source that
property is not a hypothesis: it is the conclusion of Stacks 02Z2, which rests on the
quotient theorem Stacks 02WW and through it on Stacks 0265, whose descent hypotheses are
undischarged in this repository — see
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf`. Discharging `hQ` for a finite
group action is exactly what Stacks 02Z2 adds, and these statements become that tag's
immediate consequences once it lands.

## References

* [Stacks Project, Tag 02Z4](https://stacks.math.columbia.edu/tag/02Z4)
* [Stacks Project, Tag 02Z2](https://stacks.math.columbia.edu/tag/02Z2)
* [Stacks Project, Tag 02WZ](https://stacks.math.columbia.edu/tag/02WZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u v

namespace AlgebraicGeometry.Space

/-- The kernel-pair square of `q` exhibits `yoneda.map (prod.lift t s)` as the base change of the
diagonal of `F` along the square of `q`, through the comparison of `yoneda` with products. -/
private theorem isPullback_yoneda_diag_of_kernelPair {C : Type*} [Category.{v} C]
    [HasBinaryProducts C] {R X : C} {F : Cᵒᵖ ⥤ Type v} (t s : R ⟶ X) (q : yoneda.obj X ⟶ F)
    (hker : IsPullback (yoneda.map t) (yoneda.map s) q q) :
    IsPullback (yoneda.map t ≫ q) (yoneda.map (prod.lift t s)) (diag F)
      (prodComparison yoneda X X ≫ prod.map q q) := by
  let c := asIso (prodComparison yoneda X X)
  have hpair : prod.lift (yoneda.map t) (yoneda.map s) ≫ c.inv = yoneda.map (prod.lift t s) :=
    c.comp_inv_eq.2 <| prod.hom_ext (by simp [c, ← Functor.map_comp])
      (by simp [c, ← Functor.map_comp])
  refine (isPullback_diagonal_prod_of_kernelPair _ _ q hker).of_iso (Iso.refl _) (Iso.refl _)
    c.symm (Iso.refl _) ?_ hpair ?_ ?_ <;> simp [c]

/-- The square of a morphism of presheaves with a property inverse-imaged along a functor has the
same property, once composed with the comparison of `yoneda` with products. -/
private theorem presheaf_inverseImage_prodComparison_comp_prodMap {C D : Type*}
    [Category.{v} C] [Category D] [HasBinaryProducts C] (P : MorphismProperty D)
    [P.IsStableUnderComposition] (G : C ⥤ D) {U : C} {F : Cᵒᵖ ⥤ Type v}
    (q : yoneda.obj U ⟶ F) (hq : (P.inverseImage G).presheaf q) :
    (P.inverseImage G).presheaf (prodComparison yoneda U U ≫ prod.map q q) := by
  have : (P.inverseImage G).IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  exact MorphismProperty.RespectsIso.precomp _ _ _
    (MorphismProperty.relative_prod_map yoneda _ q q hq hq)

/-- A property of scheme morphisms respecting isomorphisms holds for the site map
`prod.lift t s` of the graph relation of a group action once it holds for the graph relation. -/
private theorem toScheme_map_prodLift_siteActionRelation (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (V : BigFppfOver B S hS) (G : Type v) [Group G] [Small.{u} G]
    [HasBinaryProducts (BigFppfOver B S hS)] (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (a : G →* Aut (underlyingOver B hS V))
    (hR : B.Contains (actionRelationScheme (underlyingOver B hS V) G).left)
    (hj : P (actionRelation (underlyingOver B hS V) G a).left) :
    P ((BigFppfOver.toScheme B S hS).map (prod.lift (siteActionRelationTarget G B hS V hR a)
      (siteActionRelationSource G B hS V hR))) := by
  have : PreservesFiniteLimits B.inclusion :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks B.inclusion
  let post : BigFppfOver B S hS ⥤ Over S := Over.post (X := B.obj hS) B.inclusion
  have : PreservesFiniteLimits post := PreservesFiniteLimits.overPost
  let postProd : post.obj (V ⨯ V) ≅ post.obj V ⨯ post.obj V := asIso (prodComparison post V V)
  have hpost : post.map (prod.lift (siteActionRelationTarget G B hS V hR a)
      (siteActionRelationSource G B hS V hR)) ≫ postProd.hom =
      actionRelation (underlyingOver B hS V) G a := by
    apply prod.hom_ext
    · show (post.map _ ≫ prodComparison post V V) ≫ prod.fst = _
      simp only [Category.assoc, prodComparison_fst, ← Functor.map_comp, prod.lift_fst,
        actionRelation]
      exact (prod.lift_fst _ _).symm
    · show (post.map _ ≫ prodComparison post V V) ≫ prod.snd = _
      simp only [Category.assoc, prodComparison_snd, ← Functor.map_comp, prod.lift_snd,
        actionRelation]
      exact (prod.lift_snd _ _).symm
  refine (MorphismProperty.cancel_right_of_respectsIso P _
    ((Over.forget S).mapIso postProd).hom).mp ?_
  show P ((Over.forget S).map (post.map _) ≫ (Over.forget S).map postProd.hom)
  rwa [← Functor.map_comp, hpost]

/-- A property of scheme morphisms local at the target for the fpqc precoverage is local at the
target for the fppf precoverage. -/
private theorem isLocalAtTarget_fppfPrecoverage (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtTarget Scheme.fpqcPrecoverage] : P.IsLocalAtTarget Scheme.fppfPrecoverage :=
  MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (V : BigFppfOver B S hS) (G : Type v) [Group G] [Finite G]
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- A property of scheme morphisms which is stable under base change and fppf local on the
target passes from the graph relation of a finite group action to the diagonal of the
quotient of the action, when that quotient is an algebraic space over `S`.

This is the reduction step of **Stacks 02Z4**. It does not carry `@[stacks 02Z4]`: the
algebraic-space property `hQ` of the quotient is the conclusion of Stacks 02Z2 rather than a
hypothesis of the source, and is undischarged here. -/
theorem presheaf_diag_actionQuotient
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    (a : G →* Aut (underlyingOver B hS V))
    (ha : ActsNontriviallyOnFixedResidueFields (underlyingOver B hS V) G a)
    (hQ : IsAlgebraicSpace B S hS (actionQuotient G B hS V a))
    (hj : P (actionRelation (underlyingOver B hS V) G a).left) :
    (MorphismProperty.presheaf (P.inverseImage (BigFppfOver.toScheme B S hS)))
      (diag (actionQuotient G B hS V a)) := by
  have hR : B.Contains (actionRelationScheme (underlyingOver B hS V) G).left :=
    contains_actionRelationScheme G B hS V a ha
  let sA := siteActionRelationSource G B hS V hR
  let tA := siteActionRelationTarget G B hS V hR a
  have : IsEtaleEquivalenceRelation (relation B S hS sA tA) :=
    actionRelation_isEtaleEquivalenceRelation (underlyingOver B hS V) G a ha
  let Q := actionQuotient G B hS V a
  let Fsite := BigFppfOver.toScheme B S hS
  let q : yoneda.obj V ⟶ Q := quotientMap B S hS sA tA
  have hrep : yoneda.relativelyRepresentable (quotientMap B S hS sA tA) :=
    relativelyRepresentable_quotientMap_of_isAlgebraicSpace B S hS sA tA hQ
  have : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have : MorphismProperty.IsStableUnderComposition
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  let q₂ : yoneda.obj (V ⨯ V) ⟶ Q ⨯ Q := prodComparison yoneda V V ≫ prod.map q q
  have hdRep : yoneda.relativelyRepresentable (diag Q) := hQ.diagonal_representable
  have hpull : IsPullback (yoneda.map tA ≫ q) (yoneda.map (prod.lift tA sA)) (diag Q) q₂ :=
    isPullback_yoneda_diag_of_kernelPair tA sA q (quotientMap_isPullback B S hS sA tA)
  let e := yoneda.preimageIso (hpull.isoIsPullback _ _ (hdRep.isPullback q₂))
  have he : e.hom ≫ hdRep.snd q₂ = prod.lift tA sA := by
    apply yoneda.map_injective
    simp [e, hpull.isoIsPullback_hom_snd _ _ (hdRep.isPullback q₂)]
  have hchosen : P (Fsite.map (hdRep.snd q₂)) := by
    refine (MorphismProperty.cancel_left_of_respectsIso P (Fsite.map e.hom) _).mp ?_
    rw [← Fsite.map_comp, he]
    exact toScheme_map_prodLift_siteActionRelation B S hS V G P a hR hj
  exact (presheaf_inverseImage_iff_atlas_snd B S hS P (diag Q) hdRep (V ⨯ V) q₂
    (presheaf_inverseImage_prodComparison_comp_prodMap _ Fsite q
      (quotientMap_surjective B S hS sA tA hrep))
    (presheaf_inverseImage_prodComparison_comp_prodMap _ Fsite q
      (quotientMap_etale B S hS sA tA hrep))).2 hchosen

/-- **Stacks 02Z4, part (2).** The quotient of a scheme separated over `S` by a finite group
action whose nonidentity stabilizers act nontrivially on the residue fields they fix is
separated over `S`.

It does not carry `@[stacks 02Z4]`: the algebraic-space property `hQ` of the quotient is the
conclusion of Stacks 02Z2 rather than a hypothesis of the source, and is undischarged
here. -/
theorem isSeparatedOver_actionQuotient
    (a : G →* Aut (underlyingOver B hS V))
    (ha : ActsNontriviallyOnFixedResidueFields (underlyingOver B hS V) G a)
    (hQ : IsAlgebraicSpace B S hS (actionQuotient G B hS V a))
    [_root_.AlgebraicGeometry.IsSeparated (underlyingOver B hS V).hom] :
    IsSeparatedOver B S hS (actionQuotient G B hS V a) := by
  have := isLocalAtTarget_fppfPrecoverage
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
  exact presheaf_diag_actionQuotient B S hS V G
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) a ha hQ
    (isClosedImmersion_actionRelation (underlyingOver B hS V) G a ha)

/-- **Stacks 02Z4, part (1).** The quotient of a scheme quasi-separated over `S` by a finite
group action whose nonidentity stabilizers act nontrivially on the residue fields they fix is
quasi-separated over `S`.

It does not carry `@[stacks 02Z4]`: the algebraic-space property `hQ` of the quotient is the
conclusion of Stacks 02Z2 rather than a hypothesis of the source, and is undischarged
here. -/
theorem isQuasiSeparatedOver_actionQuotient
    (a : G →* Aut (underlyingOver B hS V))
    (ha : ActsNontriviallyOnFixedResidueFields (underlyingOver B hS V) G a)
    (hQ : IsAlgebraicSpace B S hS (actionQuotient G B hS V a))
    [QuasiSeparated (underlyingOver B hS V).hom] :
    IsQuasiSeparatedOver B S hS (actionQuotient G B hS V a) := by
  have := isLocalAtTarget_fppfPrecoverage (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
  exact presheaf_diag_actionQuotient B S hS V G (@QuasiCompact.{u}) a ha hQ
    (quasiCompact_actionRelation (underlyingOver B hS V) G a)

end AlgebraicGeometry.Space

end
