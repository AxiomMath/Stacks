module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.JacobsonPoints.Jacobson
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.MonomorphismFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImageSiteOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsInducingTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.ConstancyOfStackDimension
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionAtFiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfSiteFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.JacobsonAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismGenericOpenImmersionChart
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenImageSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsQuotientOfSpaceAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.PseudoCatenary
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionSmoothStacks
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothMonomorphismOpenImmersion

/-!
# The chart of Stacks 0DS2 and its transport to the stack of an algebraic space

Stacks 0DS2 proves that a locally-of-finite-type monomorphism `m : 𝒯 ⟶ 𝒳` of algebraic stacks
over `S`, with `𝒳` Jacobson, pseudo-catenary and locally Noetherian, with `|𝒯|` irreducible of
dimension `d` and with `𝒳` reduced of dimension at most `d`, is an open immersion on some
non-empty open substack of `𝒯`. Its proof runs on a smooth surjective chart `a : U ⟶ 𝒳` by an
algebraic space and on the base change `𝒯 ×_𝒳 U` of `m` along it, and the dimension hypotheses
enter only through the inequality

`dim_u(U) ≤ dim_{u'}(𝒯 ×_𝒳 U)`,   `u` the image of `u'`,

which is the displayed equation **Stacks 0DS3** of that proof.

This module proves that inequality and performs the transport that makes the chart-level
argument usable at the level of presheaves: the 2-fibre product `𝒯 ×_𝒳 U` of **Stacks 04T2** is
only *represented* by an algebraic space, while the chart-level conclusion of Stacks 0DS2 is
phrased in terms of an honest 1-morphism out of the algebraic stack of an algebraic space.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isJacobson_of_isLocallyOfFiniteType`: the source of a
  locally-of-finite-type 1-morphism with Jacobson target is Jacobson. This is the parenthetical
  "and thus also `𝒯`" in the statement of Stacks 0DS2, for the Jacobson condition; its
  pseudo-catenary half is **Stacks 0DRW** and its locally Noetherian half **Stacks 06R6**.
* `AlgebraicGeometry.Stack.exists_isSmooth_isSurjective_representingMap_eq_id`: **the comparison
  1-morphism.** An algebraic space `E` over `S` representing an algebraic stack `𝒵` over `S`
  carries a 1-morphism `E ⟶ 𝒵` whose induced morphism of representing presheaves is the identity
  of `E`, and that 1-morphism is smooth and surjective. Applied to a 2-fibre product of
  algebraic stacks and an algebraic space representing it, this is the comparison the
  chart-level argument of Stacks 0DS2 needs.
* `AlgebraicGeometry.Stack.dimensionAtPoint_le_dimensionAtPoint_representingMap`: the displayed
  inequality **Stacks 0DS3**, read on the representing algebraic spaces, together with the
  finiteness of the dimension of the chart at the point in question.
* `AlgebraicGeometry.Stack.exists_openSubspace_isEtale_of_mono_of_dimensionAtPoint_le`: the
  production of the open subspace, at the level of algebraic spaces. This is the scheme-level
  kernel `AlgebraicGeometry.exists_opens_isOpenImmersion_comp_of_mono_of_topologicalKrullDimAt_le`
  carried across the boundary between schemes and algebraic spaces.
* `AlgebraicGeometry.Stack.exists_chart_openSubspace_isSmooth`: the chart-level conclusion of
  Stacks 0DS2 — an algebraic space `U'` over `S` with a smooth 1-morphism to `𝒯`, a non-empty
  open subspace `W` of `U'`, and `W ⟶ 𝒳` smooth.

## The comparison 1-morphism

`AlgebraicGeometry.Stack.algebraicSpaceStack` turns an algebraic space over `S` into an
algebraic stack over `S`, and `AlgebraicGeometry.Stack.algebraicSpaceStackMap` turns a morphism
of algebraic spaces into a 1-morphism between those. A 2-fibre product of algebraic stacks is
not of that form: `AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks` produces the
2-fibre product of **Stacks 04T2**, whose apex is at best *representable by an algebraic space*
in the sense of **Stacks 04SV**, i.e. equivalent over the site to the category of elements of
some algebraic space.

The bridge is **Stacks 04SW**, whose surjectivity clause is
`AlgebraicGeometry.Stack.exists_oneMorphism_representingMap_eq`: every morphism of representing
presheaves is induced by a 1-morphism. Applied to the identity of the representing presheaf it
produces the comparison, and the representable case of **Stacks 06FM** reads smoothness and
surjectivity of the comparison off smoothness and surjectivity of that identity.

The same representable case of Stacks 06FM is what carries properties in the other direction.
Stacks 04SW is functorial (`AlgebraicGeometry.Stack.representingMap_comp`) and sends the
1-morphism of a morphism of algebraic spaces to that morphism
(`AlgebraicGeometry.Stack.representingMap_associatedMap`), so the morphism of representing
presheaves of `W ⟶ U' ⟶ 𝒯 ×_𝒳 U ⟶ U` is computed to be `W ⟶ U' ⟶ U`; a 1-morphism between
algebraic stacks of algebraic spaces is smooth exactly when its morphism of representing
presheaves is, which turns étaleness of `W ⟶ U` into smoothness of the 1-morphism. No comparison
of 2-isomorphism classes is needed anywhere.

## Stacks 0DS3

The inequality is the source's own computation. With `𝒰` the algebraic stack of `U`, `Q` a
2-fibre product of `m` and `a`, and `z` a point of its apex:

* **Stacks 0DRP** at the projection `Q.fst : Q.pt ⟶ 𝒯`, which is smooth because it is a base
  change of the smooth `a` (**Stacks 075W**), writes `dim_z(Q.pt)` as the dimension of `𝒯` at
  the image of `z` plus the relative dimension of `Q.fst` at `z`;
* **Stacks 0DRP** at `a` writes the dimension of `𝒰` at the image of `z` under `Q.snd` as the
  dimension of `𝒳` at its image plus the relative dimension of `a` there;
* **Stacks 0DRN** identifies those two relative dimensions, `Q.fst` being a base change of `a`;
* **Stacks 0DRX** makes the dimension of `𝒯` constant on `|𝒯|`, so the first summand of the
  first line is the dimension `d` of `𝒯`, while the first summand of the second line is at most
  the dimension of `𝒳`, hence at most `d`.

Cancelling the common relative dimension, which is an integer
(`AlgebraicGeometry.Stack.exists_relativeStackDimensionAt_eq_intCast`), gives the inequality and
at the same time bounds the dimension of `𝒰` at the image of `z` by an integer, which is the
finiteness the chart-level argument also needs. Stacks 0DRX asks `𝒯` to be Jacobson,
pseudo-catenary and locally Noetherian; those are derived from the corresponding properties of
`𝒳` by `AlgebraicGeometry.Stack.AlgebraicStacks.isJacobson_of_isLocallyOfFiniteType`,
Stacks 0DRW and Stacks 06R6, so only the source's own hypotheses on `𝒳` are made.

The dimensions of the two algebraic spaces are those of **Stacks 04N5**; they are read off the
dimensions of Stacks 0AFN of the corresponding algebraic stacks by
`AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionSubNat_zero_of_representing`, and
`AlgebraicGeometry.Stack.dimensionSubNat_zero_le_dimensionSubNat_zero_iff` turns the comparison
of extended integers back into one of the values in `WithBot ℕ∞`.

## The open subspace

The remaining step of the proof is the production of the open subspace `W`: `U' ⟶ U` is a
monomorphism locally of finite type, hence separated and locally quasi-finite (**Stacks 0463**),
so representable (**Stacks 0418**) and unramified; the étale-local structure of an unramified
morphism (**Stacks 04HI**) presents it locally as a closed immersion into an étale neighbourhood;
the dimension inequality forces that closed immersion to be an isomorphism; and the image of the
étale neighbourhood in `U'` is a non-empty open subspace with `W ⟶ U` étale (**Stacks 04N4**).

That argument is carried out for morphisms of schemes by
`AlgebraicGeometry.exists_opens_isOpenImmersion_comp_of_mono_of_topologicalKrullDimAt_le`, and
`AlgebraicGeometry.Stack.exists_openSubspace_isEtale_of_mono_of_dimensionAtPoint_le` transports
it to algebraic spaces whose target is represented by a scheme of the site, which is the shape the
chart of Stacks 0DS2 has. The source of the monomorphism is then representable too, by Stacks 0463
and Stacks 0418 again, so both ends of the morphism and the open subspace produced at the end are
represented; the dimensions of **Stacks 04N5** at the two ends are the local Krull dimensions of
the representing schemes, and étaleness of a morphism of the site is étaleness in the sense of
**Stacks 03FR** of its Yoneda image. The reducedness and local Noetherianity of the chart scheme
that the kernel asks for are read off `𝒳` by the scheme criterion of **Stacks 04YF**.

## References

* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 042M](https://stacks.math.columbia.edu/tag/042M)
* [Stacks Project, Tag 0418](https://stacks.math.columbia.edu/tag/0418)
* [Stacks Project, Tag 0463](https://stacks.math.columbia.edu/tag/0463)
* [Stacks Project, Tag 04HI](https://stacks.math.columbia.edu/tag/04HI)
* [Stacks Project, Tag 04N4](https://stacks.math.columbia.edu/tag/04N4)
* [Stacks Project, Tag 04N5](https://stacks.math.columbia.edu/tag/04N5)
* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04XX](https://stacks.math.columbia.edu/tag/04XX)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 04YG](https://stacks.math.columbia.edu/tag/04YG)
* [Stacks Project, Tag 04ZP](https://stacks.math.columbia.edu/tag/04ZP)
* [Stacks Project, Tag 04ZU](https://stacks.math.columbia.edu/tag/04ZU)
* [Stacks Project, Tag 04ZX](https://stacks.math.columbia.edu/tag/04ZX)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FU](https://stacks.math.columbia.edu/tag/06FU)
* [Stacks Project, Tag 06R6](https://stacks.math.columbia.edu/tag/06R6)
* [Stacks Project, Tag 075W](https://stacks.math.columbia.edu/tag/075W)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0AFP](https://stacks.math.columbia.edu/tag/0AFP)
* [Stacks Project, Tag 0DRN](https://stacks.math.columbia.edu/tag/0DRN)
* [Stacks Project, Tag 0DRP](https://stacks.math.columbia.edu/tag/0DRP)
* [Stacks Project, Tag 0DRW](https://stacks.math.columbia.edu/tag/0DRW)
* [Stacks Project, Tag 0DRX](https://stacks.math.columbia.edu/tag/0DRX)
* [Stacks Project, Tag 0DS2](https://stacks.math.columbia.edu/tag/0DS2)
* [Stacks Project, Tag 0DS3](https://stacks.math.columbia.edu/tag/0DS3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PresheafOfCategories

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The Jacobson condition along a locally-of-finite-type 1-morphism -/

/-- **The source of a locally-of-finite-type 1-morphism of algebraic stacks over `S` whose
target is Jacobson is Jacobson.** This is the parenthetical "and thus also `𝒯`" in the statement
of Stacks 0DS2, for the Jacobson condition.

The proof is the one of **Stacks 0DRW** for the pseudo-catenary condition. A Jacobson smooth
surjective scheme atlas `U ⟶ 𝒳` base changes to a smooth surjective `𝒴 ×_𝒳 U ⟶ 𝒴`
(**Stacks 075W** and **Stacks 04ZU**), along which a smooth surjective scheme atlas
`V ⟶ 𝒴 ×_𝒳 U` composes to a smooth surjective scheme atlas of `𝒴`; and `V ⟶ U` is locally of
finite type, being `V ⟶ 𝒴 ×_𝒳 U ⟶ U` with the second map a base change of the given 1-morphism
(**Stacks 06FU**), so `V` is Jacobson. -/
theorem AlgebraicStacks.isJacobson_of_isLocallyOfFiniteType
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒴 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (h𝒳 : AlgebraicStacks.IsJacobson B S hS 𝒳) :
    AlgebraicStacks.IsJacobson B S hS 𝒴 := by
  obtain ⟨U, a, haSurj, haSmooth, hU⟩ := h𝒳
  have hQ : Bicategory.IsTwoFibreProduct (twoFibreProductSquareAlgebraicStacks B S hS f a) :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f a
  have hfstSmooth : AlgebraicStacks.IsSmooth B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f a).fst :=
    AlgebraicStacks.isSmooth_baseChange B S hS a f
      (twoFibreProductSquareAlgebraicStacks B S hS f a) hQ haSmooth
  have hfstSurj : IsSurjective B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f a).fst :=
    isSurjective_of_isTwoFibreProduct B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f a).swap
      (Bicategory.isTwoFibreProduct_swap hQ) haSurj
  have hsndType : AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS f a).snd :=
    AlgebraicStacks.isLocallyOfFiniteType_baseChange B S hS f a
      (twoFibreProductSquareAlgebraicStacks B S hS f a).swap
      (Bicategory.isTwoFibreProduct_swap hQ) hf
  obtain ⟨V, c, hcSmooth, hcSurj⟩ := exists_smooth_surjective_schemeStack B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS f a).pt
  have hcType : AlgebraicStacks.IsLocallyOfFiniteType B S hS c :=
    AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
      (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS c hcSmooth)
  obtain ⟨g, hg⟩ := exists_schemeMap_locallyOfFiniteType_of_schemeStackHom B S hS
    (c ≫ (twoFibreProductSquareAlgebraicStacks B S hS f a).snd)
    (AlgebraicStacks.isLocallyOfFiniteType_comp B S hS c _ hcType hsndType)
  let _ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g) := hg
  let _ := hU
  exact ⟨V, c ≫ (twoFibreProductSquareAlgebraicStacks B S hS f a).fst,
    isSurjective_comp B S hS c _ hcSurj hfstSurj,
    AlgebraicStacks.isSmooth_comp B S hS c _ hcSmooth hfstSmooth,
    LocallyOfFiniteType.jacobsonSpace ((BigFppfOver.toScheme B S hS).map g)⟩

/-! ### The comparison 1-morphism of an algebraic space representing an algebraic stack -/

/-- **The comparison 1-morphism of Stacks 04SW attached to the identity of a representing
presheaf.** If the algebraic space `E` over `S` represents the algebraic stack `𝒵` over `S`,
there is a 1-morphism from the algebraic stack of `E` to `𝒵` whose induced morphism of
representing presheaves is the identity of `E`, and it is smooth and surjective.

This is the 1-morphism that lets a 2-fibre product of algebraic stacks be used where a
1-morphism out of `AlgebraicGeometry.Stack.algebraicSpaceStack` is wanted. It exists by the
surjectivity clause of **Stacks 04SW**, and it is smooth and surjective because the identity is,
by the representable case of **Stacks 06FM**. -/
theorem exists_isSmooth_isSurjective_representingMap_eq_id
    (𝒵 : AlgebraicStacks.{u, w} B S hS)
    (E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hE : IsAlgebraicSpace B S hS E)
    (eE : StacksRepresentableCFG.EquivalenceOver 𝒵.val.val.p
      (presheafOfCategories (E ⋙ typeToCat)).p) :
    ∃ c : algebraicSpaceStack.{u, w} B S hS E hE ⟶ 𝒵,
      representingMap B S hS (algebraicSpaceStack.{u, w} B S hS E hE).val 𝒵.val E E
          (StacksRepresentableCFG.EquivalenceOver.refl _) eE c.hom = 𝟙 E ∧
        AlgebraicStacks.IsSmooth B S hS c ∧ IsSurjective B S hS c := by
  obtain ⟨c, hc⟩ := exists_oneMorphism_representingMap_eq B S hS
    (𝒳 := algebraicSpaceStack.{u, w} B S hS E hE) (𝒴 := 𝒵) E E
    (StacksRepresentableCFG.EquivalenceOver.refl _) eE (𝟙 E)
  refine ⟨c, hc, ?_, ?_⟩
  · exact isSmooth_of_isSmooth_representingMap B S hS E E hE hE
      (StacksRepresentableCFG.EquivalenceOver.refl _) eE c
      (by rw [hc]; exact Space.isSmooth_id B S hS hE)
  · refine isSurjective_of_isSurjective_representingMap B S hS E E hE hE
      (StacksRepresentableCFG.EquivalenceOver.refl _) eE c ?_
    rw [hc]
    intro x
    exact ⟨x, by rw [Space.pointsMap_id]; rfl⟩

/-! ### Extended-integer arithmetic -/

/-- An inequality of extended integers is preserved by adding an integer to both sides. This is
the converse of `AlgebraicGeometry.Stack.le_of_add_intCast_le_add_intCast`. -/
theorem add_intCast_le_add_intCast_of_le {A B : EInt} (c : ℤ) (h : A ≤ B) :
    A + ((c : ℤ) : EInt) ≤ B + ((c : ℤ) : EInt) := by
  have hc : ((c : ℤ) : EInt) = ((((c : ℤ) : WithTop ℤ)) : WithBot (WithTop ℤ)) := rfl
  rw [hc]
  induction A using WithBot.recBotCoe with
  | bot =>
    rw [show (⊥ : WithBot (WithTop ℤ)) + ((((c : ℤ) : WithTop ℤ)) : WithBot (WithTop ℤ)) = ⊥
      from rfl]
    exact bot_le
  | coe A' =>
    induction B using WithBot.recBotCoe with
    | bot => exact absurd (le_bot_iff.mp h) WithBot.coe_ne_bot
    | coe B' =>
      rw [WithBot.coe_le_coe] at h
      rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_le_coe]
      induction A' using WithTop.recTopCoe with
      | top =>
        rw [top_le_iff] at h
        subst h
        exact le_rfl
      | coe x =>
        induction B' using WithTop.recTopCoe with
        | top => rw [top_add]; exact le_top
        | coe y =>
          rw [WithTop.coe_le_coe] at h
          rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
          omega

/-- **The dimension shift of Stacks 0AFN by zero reflects and preserves the order.** The
extended integer `AlgebraicGeometry.Stack.dimensionSubNat δ 0` attached to a value `δ` of the
dimension of Stacks 04N5 determines `δ` up to the order, so a comparison of dimensions of the
algebraic stacks of two algebraic spaces is a comparison of the dimensions of those spaces. -/
theorem dimensionSubNat_zero_le_dimensionSubNat_zero_iff {δ δ' : WithBot ℕ∞} :
    dimensionSubNat δ 0 ≤ dimensionSubNat δ' 0 ↔ δ ≤ δ' := by
  refine ⟨fun h => ?_, dimensionSubNat_mono 0⟩
  induction δ using WithBotTop.rec with
  | bot => exact bot_le
  | top =>
    induction δ' using WithBotTop.rec with
    | bot =>
      have h' : (⊤ : EInt) ≤ (⊥ : EInt) := h
      exact absurd (le_bot_iff.mp h') WithBotTop.top_ne_bot
    | top => exact le_rfl
    | coe k' =>
      have h' : (⊤ : EInt) ≤ ((((k' : ℤ) - ((0 : ℕ) : ℤ)) : ℤ) : EInt) := h
      exact absurd (top_le_iff.mp h') (WithBotTop.coe_ne_top _)
  | coe k =>
    induction δ' using WithBotTop.rec with
    | bot =>
      have h' : ((((k : ℤ) - ((0 : ℕ) : ℤ)) : ℤ) : EInt) ≤ (⊥ : EInt) := h
      exact absurd (le_bot_iff.mp h') (WithBotTop.coe_ne_bot _)
    | top => exact le_top
    | coe k' =>
      have h' : ((((k : ℤ) - ((0 : ℕ) : ℤ)) : ℤ) : EInt) ≤
          ((((k' : ℤ) - ((0 : ℕ) : ℤ)) : ℤ) : EInt) := h
      rw [WithBotTop.coe_le_coe] at h'
      exact WithBotTop.coe_le_coe.mpr (by omega)

/-- A value of the dimension of Stacks 04N5 whose shift by zero is bounded by an integer is
finite. -/
theorem ne_top_of_dimensionSubNat_zero_le_intCast {δ : WithBot ℕ∞} {k : ℤ}
    (h : dimensionSubNat δ 0 ≤ ((k : ℤ) : EInt)) : δ ≠ ⊤ := by
  intro hδ
  rw [hδ, dimensionSubNat_top, top_le_iff] at h
  exact absurd h (WithBotTop.coe_ne_top _)

/-! ### Stacks 0DS3 -/

section Chart

variable {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **The displayed inequality of Stacks 0DS3, at the level of algebraic stacks.** The dimension
of the algebraic stack of the chart at the image of a point of the apex of the square is at most
the dimension of the apex at that point, and is bounded by an integer.

The module's "Stacks 0DS3" sets the computation out. The two local-Noetherianity witnesses are
arguments so that the statement does not have to name the way they are derived; both are
produced at the one call site below. -/
private theorem dimensionAtPoint_chart_le_of_isTwoFibreProduct (m : 𝒯 ⟶ 𝒳)
    (hft : AlgebraicStacks.IsLocallyOfFiniteType B S hS m)
    (h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (h𝒳N : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (d : ℕ)
    (h𝒯dim : dimension B S hS 𝒯
      (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS m hft h𝒳N) =
      ((d : ℤ) : EInt))
    (h𝒳dim : dimension B S hS 𝒳 h𝒳N ≤ ((d : ℤ) : EInt))
    {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    (a : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (hasm : AlgebraicStacks.IsSmooth B S hS a)
    (Q : Bicategory.TwoCommSq m a) (hQ : Bicategory.IsTwoFibreProduct Q)
    (h𝒰N : IsLocallyNoetherianStack.{u, w} B S hS (algebraicSpaceStack.{u, w} B S hS U hU))
    (hQN : IsLocallyNoetherianStack.{u, w} B S hS Q.pt)
    (z : points B S hS Q.pt.val.val Q.pt.val.property) :
    dimensionAtPoint B S hS (algebraicSpaceStack.{u, w} B S hS U hU) h𝒰N
          (pointsMap B S hS Q.pt.val.val Q.pt.val.property
            (algebraicSpaceStack.{u, w} B S hS U hU).val.property Q.snd.hom.hom z) ≤
        dimensionAtPoint B S hS Q.pt hQN z ∧
      ∃ k : ℤ, dimensionAtPoint B S hS (algebraicSpaceStack.{u, w} B S hS U hU) h𝒰N
        (pointsMap B S hS Q.pt.val.val Q.pt.val.property
          (algebraicSpaceStack.{u, w} B S hS U hU).val.property Q.snd.hom.hom z) ≤
        ((k : ℤ) : EInt) := by
  classical
  -- the three properties of `𝒯` that Stacks 0DRX needs
  have h𝒯N : IsLocallyNoetherianStack.{u, w} B S hS 𝒯 :=
    AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS m hft h𝒳N
  have h𝒯Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒯 :=
    AlgebraicStacks.isJacobson_of_isLocallyOfFiniteType B S hS m hft h𝒳Jacobson
  have h𝒯Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒯 :=
    isPseudoCatenary_of_isLocallyOfFiniteType B S hS m hft h𝒳Catenary
  have haType := AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS a hasm
  have hfstSmooth : AlgebraicStacks.IsSmooth B S hS Q.fst :=
    AlgebraicStacks.isSmooth_baseChange B S hS a m Q hQ hasm
  have hfstType := AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS Q.fst hfstSmooth
  -- the two dimension formulas of Stacks 0DRP, and Stacks 0DRN comparing their second summands
  have hQP := dimensionAtPoint_eq_add_relativeStackDimensionAt_of_isSmooth B S hS Q.fst
    hfstSmooth hfstType hQN h𝒯N z
  have haP := dimensionAtPoint_eq_add_relativeStackDimensionAt_of_isSmooth B S hS a hasm haType
    h𝒰N h𝒳N (pointsMap B S hS Q.pt.val.val Q.pt.val.property
      (algebraicSpaceStack.{u, w} B S hS U hU).val.property Q.snd.hom.hom z)
  have hDRN := relativeStackDimensionAt_fst_eq_relativeStackDimensionAt.{u, w} B S hS m a Q hQ
    haType hfstType hQN h𝒰N h𝒯N h𝒳N z
  -- Stacks 0DRX: the dimension of `𝒯` is `d` at every point
  have hconst := isConstant_dimensionAtPoint_of_irreducibleSpace B S hS 𝒯 h𝒯N h𝒯Jacobson
    h𝒯Catenary h𝒯Irreducible
  have h𝒯val : dimensionAtPoint B S hS 𝒯 h𝒯N
      (pointsMap B S hS Q.pt.val.val Q.pt.val.property 𝒯.val.property Q.fst.hom.hom z) =
      ((d : ℤ) : EInt) :=
    (dimension_eq_dimensionAtPoint_of_isConstant B S hS 𝒯 h𝒯N hconst _).symm.trans h𝒯dim
  have h𝒳val : dimensionAtPoint B S hS 𝒳 h𝒳N
      (pointsMap B S hS (algebraicSpaceStack.{u, w} B S hS U hU).val.val
        (algebraicSpaceStack.{u, w} B S hS U hU).val.property 𝒳.val.property a.hom.hom
        (pointsMap B S hS Q.pt.val.val Q.pt.val.property
          (algebraicSpaceStack.{u, w} B S hS U hU).val.property Q.snd.hom.hom z)) ≤
      ((d : ℤ) : EInt) :=
    le_trans (le_iSup (fun x => dimensionAtPoint B S hS 𝒳 h𝒳N x) _) h𝒳dim
  obtain ⟨c, hc⟩ := exists_relativeStackDimensionAt_eq_intCast B S hS a haType h𝒰N h𝒳N
    (pointsMap B S hS Q.pt.val.val Q.pt.val.property
      (algebraicSpaceStack.{u, w} B S hS U hU).val.property Q.snd.hom.hom z)
  have key := add_intCast_le_add_intCast_of_le c h𝒳val
  refine ⟨?_, (d : ℤ) + c, ?_⟩ <;> rw [haP, hc]
  · rw [hQP, hDRN, hc, h𝒯val]
    exact key
  · exact key

/-- **The displayed inequality Stacks 0DS3.** Let `m : 𝒯 ⟶ 𝒳` be a locally-of-finite-type
1-morphism of algebraic stacks over `S`, with `𝒳` Jacobson, pseudo-catenary and locally
Noetherian, with `|𝒯|` irreducible and `𝒯` of dimension `d` in the sense of Stacks 0AFP, and
with `𝒳` of dimension at most `d`. Let `a : U ⟶ 𝒳` be a smooth 1-morphism from an algebraic
space over `S`, let `Q` be a 2-fibre product of `m` and `a` in the sense of **Stacks 04T2**, and
let the algebraic space `U'` over `S` represent its apex. Then for every point `u'` of `U'` the
dimension of Stacks 04N5 of `U` at the image of `u'` under the induced morphism `U' ⟶ U` is
finite and at most the dimension of `U'` at `u'`.

This is the displayed inequality of the proof of Stacks 0DS2, together with the finiteness of
its left-hand side. The Jacobson, pseudo-catenary and locally Noetherian conditions on `𝒯`,
which Stacks 0DRX needs, are derived from those on `𝒳` by
`AlgebraicGeometry.Stack.AlgebraicStacks.isJacobson_of_isLocallyOfFiniteType`, Stacks 0DRW and
Stacks 06R6; so are the local Noetherianity of `U` and that of the apex of the square. The
module's "Stacks 0DS3" sets the computation out; the whole displayed chain, at the level of
algebraic stacks, is
`AlgebraicGeometry.Stack.dimensionAtPoint_twoFibreProduct_eq_add_ge_add_eq`. -/
theorem dimensionAtPoint_le_dimensionAtPoint_representingMap (m : 𝒯 ⟶ 𝒳)
    (hft : AlgebraicStacks.IsLocallyOfFiniteType B S hS m)
    (h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (h𝒳N : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (d : ℕ)
    (h𝒯dim : dimension B S hS 𝒯
      (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS m hft h𝒳N) =
      ((d : ℤ) : EInt))
    (h𝒳dim : dimension B S hS 𝒳 h𝒳N ≤ ((d : ℤ) : EInt))
    {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    (a : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (hasm : AlgebraicStacks.IsSmooth B S hS a)
    (Q : Bicategory.TwoCommSq m a) (hQ : Bicategory.IsTwoFibreProduct Q)
    (U' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU' : IsAlgebraicSpace B S hS U')
    (eU' : StacksRepresentableCFG.EquivalenceOver Q.pt.val.val.p
      (presheafOfCategories (U' ⋙ typeToCat)).p)
    (u' : Space.points B S hS U') :
    Space.dimensionAtPoint B S hS U hU
          (Space.pointsMap B S hS U'
            (representingMap B S hS Q.pt.val (algebraicSpaceStack.{u, w} B S hS U hU).val U' U
              eU' (StacksRepresentableCFG.EquivalenceOver.refl _) Q.snd.hom) u') ≤
        Space.dimensionAtPoint B S hS U' hU' u' ∧
      Space.dimensionAtPoint B S hS U hU
        (Space.pointsMap B S hS U'
          (representingMap B S hS Q.pt.val (algebraicSpaceStack.{u, w} B S hS U hU).val U' U
            eU' (StacksRepresentableCFG.EquivalenceOver.refl _) Q.snd.hom) u') ≠ ⊤ := by
  classical
  have h𝒯N : IsLocallyNoetherianStack.{u, w} B S hS 𝒯 :=
    AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS m hft h𝒳N
  have haType := AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS a hasm
  have h𝒰N : IsLocallyNoetherianStack.{u, w} B S hS
      (algebraicSpaceStack.{u, w} B S hS U hU) :=
    AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS a haType h𝒳N
  have hfstSmooth : AlgebraicStacks.IsSmooth B S hS Q.fst :=
    AlgebraicStacks.isSmooth_baseChange B S hS a m Q hQ hasm
  have hQN : IsLocallyNoetherianStack.{u, w} B S hS Q.pt :=
    AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS Q.fst
      (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS Q.fst hfstSmooth) h𝒯N
  obtain ⟨hle, k, hk⟩ := dimensionAtPoint_chart_le_of_isTwoFibreProduct B S hS m hft
    h𝒳Jacobson h𝒳Catenary h𝒳N h𝒯Irreducible d h𝒯dim h𝒳dim hU a hasm Q hQ h𝒰N hQN
    (spacePointMap B S hS U' Q.pt.val
      (representingEquivalence B S hS U' Q.pt.val eU').functor u')
  have hnat := spacePointMap_representing_naturality B S hS U' U Q.pt.val
    (algebraicSpaceStack.{u, w} B S hS U hU).val eU'
    (StacksRepresentableCFG.EquivalenceOver.refl _) Q.snd.hom u'
  rw [dimensionAtPoint_eq_dimensionSubNat_zero_of_representing.{u, w} B S hS Q.pt hQN U' hU'
    eU' u' _ rfl] at hle
  rw [dimensionAtPoint_eq_dimensionSubNat_zero_of_representing.{u, w} B S hS
    (algebraicSpaceStack.{u, w} B S hS U hU) h𝒰N U hU
    (StacksRepresentableCFG.EquivalenceOver.refl _) _ _ hnat] at hle hk
  exact ⟨dimensionSubNat_zero_le_dimensionSubNat_zero_iff.mp hle,
    ne_top_of_dimensionSubNat_zero_le_intCast hk⟩

/-! ### The open subspace of the chart -/

/-- **The production of the open subspace of Stacks 0DS2, at the level of algebraic spaces.** Let
`U₀` be a scheme of the site which is reduced and locally Noetherian, let `g : U'' ⟶ U₀` be a
monomorphism of algebraic spaces over `S` which is locally of finite type, and let `x` be a point
of `U''` at which the dimension of **Stacks 04N5** of `U₀` does not exceed that of `U''` and is
finite. Then some non-empty open subspace `i : W ⟶ U''` has `W ⟶ U₀` étale.

This is the hypothesis `hopen` of
`AlgebraicGeometry.Stack.exists_chart_openSubspace_isSmooth_of_isTwoFibreProduct`, at the chart
the next theorem chooses, and it is the scheme-level kernel
`AlgebraicGeometry.exists_opens_isOpenImmersion_comp_of_mono_of_topologicalKrullDimAt_le`
transported across the boundary between schemes and algebraic spaces. The module's "The open
subspace" sets out the geometry; the transport is the following four steps.

`U''` is representable, being the source of a monomorphism locally of finite type with
representable target (**Stacks 0463** and **Stacks 0418**,
`AlgebraicGeometry.Space.isRepresentable_of_mono_of_isLocallyOfFiniteType`), so `g` composed with
the representing isomorphism is the Yoneda image of a morphism `j` of the site; `j` is a
monomorphism because `yoneda` reflects monomorphisms and
`AlgebraicGeometry.BigFppfOver.toScheme` preserves them, and it is locally of finite type because
the representing isomorphism and the identity form a square of étale charts of `g`. The
dimensions of Stacks 04N5 at the two ends are the local Krull dimensions of the representing
schemes, by `AlgebraicGeometry.Stack.dimensionAtPoint_yoneda_eq_topologicalKrullDimAt` and the
étale invariance `AlgebraicGeometry.Space.dimensionAtPoint_eq_of_isEtale` of **Stacks 04N5**
applied to the representing isomorphism. Finally the open subscheme the kernel returns is carried
back to an open immersion of presheaves by
`AlgebraicGeometry.Space.isOpenImmersion_yoneda_map_openSubobjectHom`, and étaleness of its
composite with `j`, a morphism of the site, to étaleness in the sense of **Stacks 03FR** by
`AlgebraicGeometry.Space.presheaf_yoneda_map_etale_iff` and
`AlgebraicGeometry.Space.isEtale_of_presheafEtale`. -/
theorem exists_openSubspace_isEtale_of_mono_of_dimensionAtPoint_le (U₀ : BigFppfOver B S hS)
    (hU₀red : IsReduced ((BigFppfOver.toScheme B S hS).obj U₀))
    (hU₀N : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U₀))
    (U'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU'' : IsAlgebraicSpace B S hS U'')
    (g : U'' ⟶ yoneda.obj U₀) (hgmono : Mono g)
    (hgType : Space.IsLocallyOfFiniteType B S hS g) (x : Space.points B S hS U'')
    (hdim : Space.dimensionAtPoint B S hS (yoneda.obj U₀) (isAlgebraicSpace_yoneda B S hS U₀)
          (Space.pointsMap B S hS U'' g x) ≤
        Space.dimensionAtPoint B S hS U'' hU'' x)
    (hfin : Space.dimensionAtPoint B S hS (yoneda.obj U₀) (isAlgebraicSpace_yoneda B S hS U₀)
        (Space.pointsMap B S hS U'' g x) ≠ ⊤) :
    ∃ (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i : W ⟶ U''),
      Space.IsOpenImmersion B S hS i ∧ Nonempty (Space.points B S hS W) ∧
        Space.IsEtale B S hS (i ≫ g) := by
  classical
  -- Stacks 0463 and 0418: the source of `g` is representable by a scheme of the site.
  have _hrep : U''.IsRepresentable :=
    Space.isRepresentable_of_mono_of_isLocallyOfFiniteType B S hS g hU''
      (isAlgebraicSpace_yoneda B S hS U₀) hgType hgmono inferInstance
  obtain ⟨j, hj⟩ : ∃ j : U''.reprX ⟶ U₀, yoneda.map j = U''.reprW.hom ≫ g :=
    ⟨yoneda.preimage (U''.reprW.hom ≫ g), yoneda.map_preimage _⟩
  -- `j` is a monomorphism of schemes, locally of finite type, with reduced locally Noetherian
  -- target.
  have hjmono : Mono (yoneda.map j) := by
    have := hgmono
    rw [hj]
    infer_instance
  have _ : Mono j := Functor.mono_of_mono_map yoneda hjmono
  have _ : Mono ((BigFppfOver.toScheme B S hS).map j) := Space.mono_toScheme_map B S hS j
  have _ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map j) :=
    hgType U''.reprX U₀ U''.reprW.hom (𝟙 (yoneda.obj U₀)) j
      (Space.presheaf_etale_of_iso B S hS U''.reprW)
      (Space.presheaf_etale_id B S hS U₀) (by rw [Category.comp_id, hj])
  have _ : IsReduced ((BigFppfOver.toScheme B S hS).obj U₀) := hU₀red
  have _ : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U₀) := hU₀N
  -- the point of the representing scheme above `x`
  obtain ⟨q, hq⟩ := Space.pointsMap_surjective_of_isIso B S hS U''.reprW.hom x
  -- the two dimensions, read as local Krull dimensions of the representing schemes
  have hsrc : Space.dimensionAtPoint B S hS U'' hU'' x =
      topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U''.reprX)
        (Space.pointsToScheme B S hS U''.reprX q) := by
    rw [← hq, ← Space.dimensionAtPoint_eq_of_isEtale B S hS
      (isAlgebraicSpace_yoneda B S hS U''.reprX) hU'' U''.reprW.hom
      (Space.isEtale_of_iso B S hS U''.reprW) q]
    exact dimensionAtPoint_yoneda_eq_topologicalKrullDimAt B S hS U''.reprX q
  have htgt : Space.dimensionAtPoint B S hS (yoneda.obj U₀)
        (isAlgebraicSpace_yoneda B S hS U₀) (Space.pointsMap B S hS U'' g x) =
      topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U₀)
        ((BigFppfOver.toScheme B S hS).map j (Space.pointsToScheme B S hS U''.reprX q)) := by
    have hpt : Space.pointsMap B S hS U'' g x =
        Space.pointsMap B S hS (yoneda.obj U''.reprX) (yoneda.map j) q := by
      rw [hj, Space.pointsMap_comp, ← hq]
      rfl
    rw [hpt, dimensionAtPoint_yoneda_eq_topologicalKrullDimAt B S hS U₀,
      Space.pointsToScheme_pointsMap_yoneda]
  -- the scheme-level kernel
  obtain ⟨W₀, hW₀ne, hW₀et, -⟩ :=
    exists_opens_isOpenImmersion_comp_of_mono_of_topologicalKrullDimAt_le
      ((BigFppfOver.toScheme B S hS).map j) (Space.pointsToScheme B S hS U''.reprX q)
      (by rw [← htgt, ← hsrc]; exact hdim) (by rw [← htgt]; exact hfin)
  refine ⟨yoneda.obj (Space.openSubobject B S hS U''.reprX W₀.ι inferInstance),
    yoneda.map (Space.openSubobjectHom B S hS U''.reprX W₀.ι inferInstance) ≫ U''.reprW.hom,
    Space.isOpenImmersion_comp B S hS _ _
      (Space.isOpenImmersion_yoneda_map_openSubobjectHom B S hS U''.reprX W₀.ι inferInstance)
      (Space.isOpenImmersion_of_isIso B S hS U''.reprW.hom), ?_, ?_⟩
  · obtain ⟨w, hw⟩ := hW₀ne
    exact ⟨(Space.pointsEquivScheme B S hS
      (Space.openSubobject B S hS U''.reprX W₀.ι inferInstance)).symm
        (⟨w, hw⟩ : W₀.toScheme)⟩
  · rw [Category.assoc, ← hj, ← Functor.map_comp]
    refine Space.isEtale_of_presheafEtale B S hS _
      ((Space.presheaf_yoneda_map_etale_iff B S hS _).2 ?_)
    rw [Functor.map_comp, Space.toScheme_map_openSubobjectHom]
    exact hW₀et

/-! ### The chart-level conclusion of Stacks 0DS2 -/

/-- **The chart-level conclusion of the proof of Stacks 0DS2, at a given chart and a given
2-fibre product square.**

The hypothesis `hopen` is the production of the open subspace: for a monomorphism `g : U' ⟶ U`
of algebraic spaces over `S` which is locally of finite type, with `U` the source of a smooth
surjective chart of `𝒳`, and at a point of `U'` where the dimension of `U` does not exceed that
of `U'` and is finite, some non-empty open subspace `W` of `U'` has `W ⟶ U` étale. Every other
input is supplied: `U'` is the algebraic space representing the apex of the square, which is
representable because `m` is (**Stacks 04ZP**); `g` is the morphism of representing presheaves of
the projection `Q.snd`, a monomorphism locally of finite type because that projection is a base
change of `m` (**Stacks 04ZX** and **Stacks 06FU**), read through **Stacks 04XB** at the
monomorphism property (**Stacks 042M**) and through **Stacks 06FM** for local finite type; `|U'|`
is non-empty because `|𝒯|` is and `Q.fst` is surjective (**Stacks 04ZU**); and the dimension
inequality with its finiteness is
`AlgebraicGeometry.Stack.dimensionAtPoint_le_dimensionAtPoint_representingMap`.

The smooth 1-morphism `U' ⟶ 𝒯` is the comparison 1-morphism of Stacks 04SW followed by `Q.fst`.
For smoothness of `W ⟶ 𝒳`: the morphism of representing presheaves of `W ⟶ U' ⟶ Q.pt ⟶ U` is
`i ≫ g`, which is étale, so that 1-morphism is smooth by the representable case of
**Stacks 06FM** and **Stacks 04XX**; composing with the chart `a` and transporting along the
filler of the square gives `W ⟶ U' ⟶ Q.pt ⟶ 𝒯 ⟶ 𝒳` smooth. -/
theorem exists_chart_openSubspace_isSmooth_of_isTwoFibreProduct (m : 𝒯 ⟶ 𝒳)
    (hmono : AlgebraicStacks.IsMonomorphism B S hS m)
    (hft : AlgebraicStacks.IsLocallyOfFiniteType B S hS m)
    (h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (h𝒳N : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (d : ℕ)
    (h𝒯dim : dimension B S hS 𝒯
      (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS m hft h𝒳N) =
      ((d : ℤ) : EInt))
    (h𝒳dim : dimension B S hS 𝒳 h𝒳N ≤ ((d : ℤ) : EInt))
    {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    (a : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (hasm : AlgebraicStacks.IsSmooth B S hS a) (hasurj : IsSurjective B S hS a)
    (Q : Bicategory.TwoCommSq m a) (hQ : Bicategory.IsTwoFibreProduct Q)
    (hopen : ∀ (U'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU'' : IsAlgebraicSpace B S hS U'')
      (g : U'' ⟶ U), Mono g → Space.IsLocallyOfFiniteType B S hS g →
      ∀ x : Space.points B S hS U'',
        Space.dimensionAtPoint B S hS U hU (Space.pointsMap B S hS U'' g x) ≤
          Space.dimensionAtPoint B S hS U'' hU'' x →
        Space.dimensionAtPoint B S hS U hU (Space.pointsMap B S hS U'' g x) ≠ ⊤ →
        ∃ (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i : W ⟶ U''),
          Space.IsOpenImmersion B S hS i ∧ Nonempty (Space.points B S hS W) ∧
            Space.IsEtale B S hS (i ≫ g)) :
    ∃ (U' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU' : IsAlgebraicSpace B S hS U')
      (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hW : IsAlgebraicSpace B S hS W) (i : W ⟶ U')
      (f' : algebraicSpaceStack.{u, w} B S hS U' hU' ⟶ 𝒯),
      Space.IsOpenImmersion B S hS i ∧ AlgebraicStacks.IsSmooth B S hS f' ∧
        Nonempty (AlgebraicStacks.points B S hS (algebraicSpaceStack.{u, w} B S hS W hW)) ∧
          AlgebraicStacks.IsSmooth B S hS
            (algebraicSpaceStackMap.{u, w} B S hS hW hU' i ≫ f' ≫ m) := by
  classical
  have hQc : Bicategory.IsTwoFibreProduct Q.underlying :=
    Bicategory.isTwoFibreProduct_underlying (twoFibreProductSquareAlgebraicStacks B S hS m a) hQ
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        m.hom a.hom)
  have hfstSmooth : AlgebraicStacks.IsSmooth B S hS Q.fst :=
    AlgebraicStacks.isSmooth_baseChange B S hS a m Q hQ hasm
  have hfstSurj : IsSurjective B S hS Q.fst :=
    isSurjective_of_isTwoFibreProduct B S hS Q.swap
      (Bicategory.isTwoFibreProduct_swap hQ) hasurj
  have hsndType : AlgebraicStacks.IsLocallyOfFiniteType B S hS Q.snd :=
    AlgebraicStacks.isLocallyOfFiniteType_baseChange B S hS m a Q.swap
      (Bicategory.isTwoFibreProduct_swap hQ) hft
  -- the algebraic space representing the apex, and the comparison 1-morphism
  obtain ⟨U', hU', ⟨eU'₀⟩⟩ := isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1}
    B S hS 𝒯.val 𝒳.val (algebraicSpaceStack.{u, w} B S hS U hU).val m.hom a.hom
    Q.underlying.swap (Bicategory.isTwoFibreProduct_swap hQc) hmono.1
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU)
  -- the representing equivalence, read at the apex of the square itself
  have eU' : StacksRepresentableCFG.EquivalenceOver Q.pt.val.val.p
      (presheafOfCategories (U' ⋙ typeToCat)).p := eU'₀
  obtain ⟨c, hc, hcsm, hcsurj⟩ := exists_isSmooth_isSurjective_representingMap_eq_id.{u, w}
    B S hS Q.pt U' hU' eU'
  obtain ⟨g, hg⟩ : ∃ g : U' ⟶ U, g = representingMap B S hS Q.pt.val
      (algebraicSpaceStack.{u, w} B S hS U hU).val U' U eU'
      (StacksRepresentableCFG.EquivalenceOver.refl _) Q.snd.hom := ⟨_, rfl⟩
  -- `g` is a monomorphism, locally of finite type
  have hgmono : Mono g := by
    let _ : (MorphismProperty.monomorphisms (AlgebraicSpaces B S hS)).IsLocalAtTarget
        (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
      Space.mono_isLocalAtTarget_fppf B S hS
    rw [hg]
    exact (Space.mono_hom_iff_mono B S hS
      (ObjectProperty.homMk (representingMap B S hS Q.pt.val
          (algebraicSpaceStack.{u, w} B S hS U hU).val U' U eU'
          (StacksRepresentableCFG.EquivalenceOver.refl _) Q.snd.hom) :
        (⟨U', hU'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨U, hU⟩)).mpr
      (prop_representingMap_of_hasRelativeProperty B S hS
        (MorphismProperty.monomorphisms (AlgebraicSpaces B S hS)) m.hom hmono.1 hmono.2
        (algebraicSpaceStack.{u, w} B S hS U hU).val a.hom Q.underlying.swap
        (Bicategory.isTwoFibreProduct_swap hQc) U' U hU' hU eU'
        (StacksRepresentableCFG.EquivalenceOver.refl _))
  have hgType : Space.IsLocallyOfFiniteType B S hS g := by
    rw [hg]
    refine (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      Q.pt.property (algebraicSpaceStack.{u, w} B S hS U hU).property U' U hU' hU eU'
      (StacksRepresentableCFG.EquivalenceOver.refl _) Q.snd.hom).mp ?_
    exact (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      Q.pt.property (algebraicSpaceStack.{u, w} B S hS U hU).property Q.snd.hom).mp hsndType
  -- `|U'|` is non-empty
  obtain ⟨u'⟩ : Nonempty (Space.points B S hS U') := by
    let _ := pointTopology B S hS 𝒯.val
    obtain ⟨t, -⟩ := (IrreducibleSpace.isIrreducible_univ
      (points B S hS 𝒯.val.val 𝒯.val.property)).nonempty
    obtain ⟨p, -⟩ := hfstSurj t
    exact ⟨((bijective_spacePointMap_representing B S hS U' Q.pt.val eU').surjective p).choose⟩
  -- the dimension inequality and its finiteness
  obtain ⟨hdim, hfin⟩ := dimensionAtPoint_le_dimensionAtPoint_representingMap B S hS m hft
    h𝒳Jacobson h𝒳Catenary h𝒳N h𝒯Irreducible d h𝒯dim h𝒳dim hU a hasm Q hQ U' hU' eU' u'
  obtain ⟨W, i, hi, hWne, hig⟩ := hopen U' hU' g hgmono hgType u' (hg ▸ hdim) (hg ▸ hfin)
  have hW : IsAlgebraicSpace B S hS W :=
    AlgebraicGeometry.isAlgebraicSpace_of_relativelyRepresentable B S hS i hi.1 hU'
  refine ⟨U', hU', W, hW, i, c ≫ Q.fst, hi,
    AlgebraicStacks.isSmooth_comp B S hS c Q.fst hcsm hfstSmooth,
    ⟨stackPointOfSpacePoint B S hS W hWne.some⟩, ?_⟩
  -- the morphism of representing presheaves of `W ⟶ 𝒰` is `i ≫ g`
  have h4 : _ = g :=
    (representingMap_comp B S hS U' U' U
      (StacksRepresentableCFG.EquivalenceOver.refl _) eU'
      (StacksRepresentableCFG.EquivalenceOver.refl _) c.hom Q.snd.hom).trans
      (by rw [hc, Category.id_comp, ← hg])
  have h0 : _ = i ≫ g :=
    (representingMap_comp B S hS W U' U
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (algebraicSpaceStackMap.{u, w} B S hS hW hU' i).hom (c.hom ≫ Q.snd.hom)).trans
      (by rw [representingMap_associatedMap B S hS W U' i]
          exact congrArg (fun t => i ≫ t) h4)
  -- so `W ⟶ 𝒰` is smooth, by the representable case of Stacks 06FM
  have hWU : AlgebraicStacks.IsSmooth B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hW hU' i ≫ c ≫ Q.snd) := by
    refine (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
      (algebraicSpaceStack.{u, w} B S hS W hW).property
      (algebraicSpaceStack.{u, w} B S hS U hU).property W U hW hU
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (algebraicSpaceStackMap.{u, w} B S hS hW hU' i ≫ c ≫ Q.snd).hom).mpr ?_
    rw [show (algebraicSpaceStackMap.{u, w} B S hS hW hU' i ≫ c ≫ Q.snd).hom =
        (algebraicSpaceStackMap.{u, w} B S hS hW hU' i).hom ≫ c.hom ≫ Q.snd.hom from rfl, h0]
    exact Space.isSmooth_of_isEtale B S hS hU hig
  have hWX : AlgebraicStacks.IsSmooth B S hS
      ((algebraicSpaceStackMap.{u, w} B S hS hW hU' i ≫ c) ≫ Q.snd ≫ a) := by
    rw [Category.assoc, ← Category.assoc c Q.snd a, ← Category.assoc]
    exact AlgebraicStacks.isSmooth_comp B S hS _ a hWU hasm
  -- and `W ⟶ 𝒳` through `𝒯` is 2-isomorphic to it, by the filler of the square
  rw [Category.assoc c Q.fst m,
    ← Category.assoc (algebraicSpaceStackMap.{u, w} B S hS hW hU' i) c (Q.fst ≫ m)]
  exact hasPropertyOnSomeSmoothDiagram_of_twoIso B S hS _
    (Bicategory.whiskerLeftIso
      ((algebraicSpaceStackMap.{u, w} B S hS hW hU' i).hom ≫ c.hom)
      (Bicategory.InducedBicategory.isoHom Q.iso).symm) hWX

/-- **The chart-level conclusion of the proof of Stacks 0DS2.** Let `m : 𝒯 ⟶ 𝒳` be a
monomorphism of algebraic stacks over `S`, locally of finite type, with `𝒳` Jacobson,
pseudo-catenary and locally Noetherian, with `|𝒯|` irreducible and `𝒯` of dimension `d`, and
with `𝒳` reduced of dimension at most `d`. Then there are an algebraic space `U'` over `S` with a
smooth 1-morphism `U' ⟶ 𝒯`, a non-empty open subspace `i : W ⟶ U'`, and `W ⟶ 𝒳` smooth.

The chart of `𝒳` is Stacks 03YP together with the comparison of a scheme atlas with the
algebraic space that scheme represents, and the square is the 2-fibre product of
**Stacks 04T2**; the rest is
`AlgebraicGeometry.Stack.exists_chart_openSubspace_isSmooth_of_isTwoFibreProduct`, whose `hopen`
is `AlgebraicGeometry.Stack.exists_openSubspace_isEtale_of_mono_of_dimensionAtPoint_le` at that
chart. Its two hypotheses on the chart scheme are read off `𝒳` by the scheme criterion of
**Stacks 04YF**: reducedness from `h𝒳red` and local Noetherianity from `h𝒳N`, local
Noetherianity being local in the smooth topology because it is local in the fppf topology. -/
theorem exists_chart_openSubspace_isSmooth (m : 𝒯 ⟶ 𝒳)
    (hmono : AlgebraicStacks.IsMonomorphism B S hS m)
    (hft : AlgebraicStacks.IsLocallyOfFiniteType B S hS m)
    (h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (h𝒳N : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (d : ℕ)
    (h𝒯dim : dimension B S hS 𝒯
      (AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType.{u, w} B S hS m hft h𝒳N) =
      ((d : ℤ) : EInt))
    (h𝒳red : IsReducedStack.{u, w} B S hS 𝒳)
    (h𝒳dim : dimension B S hS 𝒳 h𝒳N ≤ ((d : ℤ) : EInt)) :
    ∃ (U' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU' : IsAlgebraicSpace B S hS U')
      (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hW : IsAlgebraicSpace B S hS W) (i : W ⟶ U')
      (f' : algebraicSpaceStack.{u, w} B S hS U' hU' ⟶ 𝒯),
      Space.IsOpenImmersion B S hS i ∧ AlgebraicStacks.IsSmooth B S hS f' ∧
        Nonempty (AlgebraicStacks.points B S hS (algebraicSpaceStack.{u, w} B S hS W hW)) ∧
          AlgebraicStacks.IsSmooth B S hS
            (algebraicSpaceStackMap.{u, w} B S hS hW hU' i ≫ f' ≫ m) := by
  obtain ⟨U₀, a₀, ha₀sm, ha₀surj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  -- Stacks 04YF: the chart scheme is reduced and locally Noetherian, because `𝒳` is.
  have hU₀red : IsReduced ((BigFppfOver.toScheme B S hS).obj U₀) :=
    (exists_scheme_atlas_iff_forall_scheme B S hS (fun Y : Scheme.{u} => IsReduced Y) 𝒳).1
      h𝒳red U₀ a₀ ha₀sm
  have hU₀N : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U₀) := by
    let _ : ObjectProperty.IsLocal (fun T : Scheme.{u} => IsLocallyNoetherian T)
        (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
      ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
    exact (exists_scheme_atlas_iff_forall_scheme B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒳).1 h𝒳N U₀ a₀ ha₀sm
  obtain ⟨e, hesm, hesurj⟩ := exists_smooth_surjective_algebraicSpaceStack_hom.{u, w} B S hS U₀
  exact exists_chart_openSubspace_isSmooth_of_isTwoFibreProduct B S hS m hmono hft h𝒳Jacobson
    h𝒳Catenary h𝒳N h𝒯Irreducible d h𝒯dim h𝒳dim (isAlgebraicSpace_yoneda B S hS U₀) (e ≫ a₀)
    (AlgebraicStacks.isSmooth_comp B S hS e a₀ hesm ha₀sm)
    (isSurjective_comp B S hS e a₀ hesurj ha₀surj)
    (twoFibreProductSquareAlgebraicStacks B S hS m (e ≫ a₀))
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS m (e ≫ a₀))
    (fun U'' hU'' g hgmono hgType x hdim hfin =>
      exists_openSubspace_isEtale_of_mono_of_dimensionAtPoint_le B S hS U₀ hU₀red hU₀N U'' hU''
        g hgmono hgType x hdim hfin)

end Chart

end AlgebraicGeometry.Stack

end
