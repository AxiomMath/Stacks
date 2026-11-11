module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Points
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.Substack
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective

/-!
# Monomorphisms of algebraic stacks, and the conditions for a residual gerbe (Stacks 04ZW, 06MT)

Stacks 06MT asks, of a point `x` of an algebraic stack `𝒳`, whether `x` is cut out by a
one-point substack. It offers three conditions:

1. some algebraic stack `𝒵` admits a monomorphism to `𝒳` whose space of points is a singleton
   mapping to `x`;
2. the same with `𝒵` reduced;
3. there is a monomorphism `f : 𝒵 ⟶ 𝒳` together with a surjective flat morphism from the
   spectrum of a field to `𝒵` whose image in `𝒳` is `x`;

and asserts that when they hold there is a *unique* strictly full subcategory of `𝒳` which is a
reduced, locally Noetherian algebraic stack with one point, lying over `x`. That subcategory is
the *residual gerbe of `𝒳` at `x`* (Stacks 06MU).

This file supplies the vocabulary those statements are phrased in, including the notion of a
monomorphism of algebraic stacks (**Stacks 04ZW**), which the library did not have.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.IsMonomorphism`: **Stacks 04ZW**.
* `AlgebraicGeometry.Stack.IsReducedStack` and
  `AlgebraicGeometry.Stack.IsLocallyNoetherianStack`: reducedness and local Noetherianity of an
  algebraic stack, tested on a smooth scheme atlas.
* `AlgebraicGeometry.Stack.HasUniquePointOver`: the source of a 1-morphism has exactly one point,
  and it lies over a prescribed point of the target.
* `AlgebraicGeometry.Stack.HasSingletonPointMonomorphism`,
  `AlgebraicGeometry.Stack.HasReducedSingletonPointMonomorphism` and
  `AlgebraicGeometry.Stack.HasFlatFieldCoverMonomorphism`: conditions (1), (2) and (3) of
  Stacks 06MT.
* `AlgebraicGeometry.Stack.FieldSpectrum`: the spectrum of a field in the chosen big fppf site.
* `AlgebraicGeometry.Stack.IsResidualGerbeAt`: the property of an object property of `𝒳` which
  the residual gerbe at `x` is asserted to satisfy uniquely.
* `AlgebraicGeometry.Stack.HasReducedSingletonPointMonomorphism` carries **Stacks 06MU**, part (1)
  — the residual gerbe of
  `𝒳` at `x` exists.
* `AlgebraicGeometry.Stack.residualGerbe` and
  `AlgebraicGeometry.Stack.residualGerbeInclusion`: **Stacks 06MU**, part (2) — the residual
  gerbe itself and its inclusion into `𝒳`, as functions of an object property witnessing
  `AlgebraicGeometry.Stack.IsResidualGerbeAt`.

## Main results

* `AlgebraicGeometry.Stack.hasSingletonPointMonomorphism_of_reduced`: condition (2) of
  Stacks 06MT implies condition (1), the direction the source calls immediate.

## Implementation notes

**Stacks 04ZW** defines a monomorphism of algebraic stacks as a 1-morphism which is
representable by algebraic spaces and a monomorphism in the sense of the relative-property
machinery of Section 04XB. That machinery is this library's
`AlgebraicGeometry.Stack.HasRelativeProperty` (**Stacks 03YK**), so the intended reading is that
predicate at `CategoryTheory.MorphismProperty.monomorphisms`. It cannot be written that way here:
`HasRelativeProperty` takes the property's locality at the target for the fppf precoverage as an
instance argument, and that instance for the monomorphisms of algebraic spaces over `S` is not
available — unlike stability under base change, which is. The definition below is therefore the
body of `HasRelativeProperty` with `CategoryTheory.Mono` in place of the property, which is the
same statement with the unavailable hypothesis discharged by inspection rather than assumed.

Reducedness and local Noetherianity are asked through the existential scheme criterion
`AlgebraicGeometry.Stack.HasPropertyOnSomeSchemeAtlas` of **Stacks 04YF**; both properties of
schemes are local for the smooth precoverage, so the criterion applies to them without further
hypotheses.

The three conditions of Stacks 06MT quantify over an algebraic stack `𝒵` and a 1-morphism to
`𝒳`, rather than over a subcategory of `𝒳`, because that is how the source states them; the
passage to a strictly full subcategory is the content of the lemma's final assertion and is
expressed by `IsResidualGerbeAt` over an object property of `𝒳`. In condition (3) the point of
the field spectrum is an arbitrary point of its associated algebraic stack, which is the unique
point of that stack.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 04ZW](https://stacks.math.columbia.edu/tag/04ZW)
* [Stacks Project, Tag 06MT](https://stacks.math.columbia.edu/tag/06MT)
* [Stacks Project, Tag 06MU](https://stacks.math.columbia.edu/tag/06MU)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

/-- **Stacks 04ZW.** A 1-morphism of algebraic stacks over `S` is a *monomorphism* when it is
representable by algebraic spaces and every algebraic space representing one of its base changes
along a scheme-valued point of the target has structural morphism a monomorphism of algebraic
spaces over `S`.

This is `AlgebraicGeometry.Stack.HasRelativeProperty` (**Stacks 03YK**, the Section 04XB notion
the source refers to) at the monomorphisms, written out rather than invoked; see the
implementation notes. -/
@[stacks 04ZW]
abbrev AlgebraicStacks.IsMonomorphism
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  IsRepresentableByAlgebraicSpaces B S hS f.hom.hom ∧
    ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.val.obj)
      (_hy : y ⋙ 𝒴.val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y
          (CatFiberedInGroupoids.homFunctor f.hom))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Mono (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))

/-- An algebraic stack over `S` is *reduced* when some smooth surjective scheme atlas of it has
reduced underlying scheme. This is the existential scheme criterion of **Stacks 04YF** at
reducedness, which is local for the smooth precoverage. -/
abbrev IsReducedStack
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  HasPropertyOnSomeSchemeAtlas B S hS (fun X : Scheme.{u} => IsReduced X) 𝒳

/-- An algebraic stack over `S` is *locally Noetherian* when some smooth surjective scheme atlas
of it has locally Noetherian underlying scheme. This is the existential scheme criterion of
**Stacks 04YF** at local Noetherianity, which is local for the smooth precoverage. -/
abbrev IsLocallyNoetherianStack
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  HasPropertyOnSomeSchemeAtlas B S hS (fun X : Scheme.{u} => IsLocallyNoetherian X) 𝒳

/-- The source of a 1-morphism `f` of algebraic stacks has exactly one point, and that point maps
to `x` under `f`. -/
abbrev HasUniquePointOver
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒵 ⟶ 𝒳)
    (x : points B S hS 𝒳.val.val (Classical.choose 𝒳.property)) : Prop :=
  ∃ z : points B S hS 𝒵.val.val (Classical.choose 𝒵.property),
    (∀ z', z' = z) ∧
      pointsMap B S hS 𝒵.val.val
        (Classical.choose 𝒵.property) (Classical.choose 𝒳.property) f.hom.hom z = x

/-- **Condition (1) of Stacks 06MT.** Some algebraic stack admits a monomorphism to `𝒳` whose
space of points is a singleton mapping to `x`. -/
abbrev HasSingletonPointMonomorphism
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : points B S hS 𝒳.val.val (Classical.choose 𝒳.property)) : Prop :=
  ∃ (𝒵 : AlgebraicStacks.{u, w} B S hS) (f : 𝒵 ⟶ 𝒳),
    AlgebraicStacks.IsMonomorphism B S hS f ∧ HasUniquePointOver B S hS f x

/-- **Condition (2) of Stacks 06MT.** The one-point substack of condition (1) can be chosen
reduced. -/
@[stacks 06MU "part (1), the existence of the residual gerbe of X at x, read as condition (2) \
of the three equivalent conditions of Stacks 06MT"]
abbrev HasReducedSingletonPointMonomorphism
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : points B S hS 𝒳.val.val (Classical.choose 𝒳.property)) : Prop :=
  ∃ (𝒵 : AlgebraicStacks.{u, w} B S hS) (f : 𝒵 ⟶ 𝒳),
    IsReducedStack B S hS 𝒵 ∧
      AlgebraicStacks.IsMonomorphism B S hS f ∧ HasUniquePointOver B S hS f x

/-- The spectrum of a field, as an object of the big fppf site of `S` presented together with an
isomorphism identifying its underlying scheme. -/
structure FieldSpectrum
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) where
  /-- The field. -/
  carrier : Type u
  [field : Field carrier]
  /-- The object of the big fppf site of `S`. -/
  base : BigFppfOver B S hS
  /-- Its underlying scheme is the spectrum of the field. -/
  isSpec : (BigFppfOver.toScheme B S hS).obj base ≅ Spec (.of carrier)

attribute [instance] FieldSpectrum.field

/-- **Condition (3) of Stacks 06MT.** Some algebraic stack admits a monomorphism `f` to `𝒳` and a
surjective flat 1-morphism to it from the algebraic stack of the spectrum of a field, some point
of which maps to `x` under `f`. -/
abbrev HasFlatFieldCoverMonomorphism
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : points B S hS 𝒳.val.val (Classical.choose 𝒳.property)) : Prop :=
  ∃ (𝒵 : AlgebraicStacks.{u, w} B S hS)
    (f : 𝒵 ⟶ 𝒳) (F : FieldSpectrum B S hS)
    (z : schemeStack.{u, w} B S hS F.base ⟶ 𝒵),
    AlgebraicStacks.IsMonomorphism B S hS f ∧
      IsSurjective B S hS z ∧
        AlgebraicStacks.IsFlat B S hS z ∧
          ∃ q : points B S hS
            (schemeStack.{u, w} B S hS F.base).val.val
            (Classical.choose (schemeStack.{u, w} B S hS F.base).property),
            pointsMap B S hS 𝒵.val.val
              (Classical.choose 𝒵.property) (Classical.choose 𝒳.property) f.hom.hom
              (pointsMap B S hS
                (schemeStack.{u, w} B S hS F.base).val.val
                (Classical.choose (schemeStack.{u, w} B S hS F.base).property)
                (Classical.choose 𝒵.property) z.hom.hom q) = x

/-- **The specification of the residual gerbe of Stacks 06MT.** A property of the objects of `𝒳`
is closed under isomorphism, its full subcategory is an algebraic stack which is reduced and
locally Noetherian, and that subcategory has exactly one point, lying over `x`.

Stacks 06MT asserts that under its equivalent conditions exactly one object property of `𝒳` has
this property; it is the *residual gerbe of `𝒳` at `x`* of Stacks 06MU. -/
abbrev IsResidualGerbeAt
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : points B S hS 𝒳.val.val (Classical.choose 𝒳.property))
    (P : ObjectProperty 𝒳.val.val.obj) : Prop :=
  P.IsClosedUnderIsomorphisms ∧
    ∃ hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P),
      IsReducedStack B S hS (fullSubcategoryAlgebraicStack 𝒳 P hP) ∧
        IsLocallyNoetherianStack B S hS (fullSubcategoryAlgebraicStack 𝒳 P hP) ∧
          HasUniquePointOver B S hS (fullSubcategoryInclusion 𝒳 P hP) x

/-- Condition (2) of **Stacks 06MT** implies its condition (1): a reduced one-point substack is in
particular a one-point substack. This is the direction the source calls immediate; the converse,
which replaces the substack by its reduction, is
`AlgebraicGeometry.Stack.hasReducedSingletonPointMonomorphism_of_hasSingletonPointMonomorphism`
of `StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeEquivalentConditions`. -/
theorem hasSingletonPointMonomorphism_of_reduced
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : points B S hS 𝒳.val.val (Classical.choose 𝒳.property))
    (h : HasReducedSingletonPointMonomorphism B S hS 𝒳 x) :
    HasSingletonPointMonomorphism B S hS 𝒳 x := by
  obtain ⟨𝒵, f, _, hm, hu⟩ := h
  exact ⟨𝒵, f, hm, hu⟩

/-! ### The residual gerbe (Stacks 06MU) -/

/-- **Stacks 06MU, part (2): the residual gerbe of `𝒳` at `x`, as an algebraic stack.** The
source takes it to be the strictly full subcategory `𝒵_x ⊂ 𝒳` produced by **Stacks 06MT**, that
is, the one cut out by an object property of `𝒳` meeting the specification
`AlgebraicGeometry.Stack.IsResidualGerbeAt`: closed under isomorphism, with full subcategory a
reduced, locally Noetherian algebraic stack having exactly one point, lying over `x`.

That object property `P` and the proof `hP` that it meets the specification are the data of this
definition. They are the defining property of the object being defined — what the source supposes
when it says that, the residual gerbe existing, it *is* `𝒵_x` — and not a substitute for an
unproved result: the algebraic stack returned is
`AlgebraicGeometry.Stack.fullSubcategoryAlgebraicStack` at `P`, whose algebraicity is one of the
conjuncts of `hP`.

Nothing here picks `P` out. Uniqueness of the object property, and with it the definite article
in "*the* residual gerbe", is the final assertion of Stacks 06MT; the library proves it as
`AlgebraicGeometry.Stack.eq_of_isResidualGerbeAt_of_bootstrap`, and existence together
with uniqueness under the equivalent conditions as
`AlgebraicGeometry.Stack.existsUnique_isResidualGerbeAt` of `StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeExistsUnique`. -/
@[stacks 06MU "part (2), the residual gerbe as an algebraic stack: the strictly full subcategory \
of X cut out by an object property meeting the specification IsResidualGerbeAt of Stacks 06MT"]
abbrev residualGerbe
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : points B S hS 𝒳.val.val (Classical.choose 𝒳.property))
    (P : ObjectProperty 𝒳.val.val.obj) (hP : IsResidualGerbeAt B S hS 𝒳 x P) :
    AlgebraicStacks.{u, w} B S hS :=
  fullSubcategoryAlgebraicStack 𝒳 P hP.2.choose

/-- **Stacks 06MU, part (2): the inclusion of the residual gerbe of `𝒳` at `x`.** The residual
gerbe is a *strictly full subcategory* of `𝒳`, and this is the inclusion 1-morphism `𝒵_x ⟶ 𝒳`
that makes it one: `AlgebraicGeometry.Stack.fullSubcategoryInclusion` at the object property
witnessing the specification.

The inclusion is fully faithful, being the inclusion of a full subcategory
(`AlgebraicGeometry.Stack.full_fullSubcategoryInclusion` and
`AlgebraicGeometry.Stack.faithful_fullSubcategoryInclusion`), and it satisfies the monomorphy
clause of **Stacks 04ZW** by
`AlgebraicGeometry.Stack.AlgebraicStacks.mono_representingMaps_fullSubcategoryInclusion`. That it
is also representable by algebraic spaces, and so a monomorphism, is
`AlgebraicGeometry.Stack.AlgebraicStacks.isMonomorphism_fullSubcategoryInclusion`, the last
assertion of Stacks 06MR, in a module downstream of this one. -/
@[stacks 06MU "part (2), the inclusion of the residual gerbe into X as a strictly full \
subcategory"]
def residualGerbeInclusion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : points B S hS 𝒳.val.val (Classical.choose 𝒳.property))
    (P : ObjectProperty 𝒳.val.val.obj) (hP : IsResidualGerbeAt B S hS 𝒳 x P) :
    residualGerbe B S hS 𝒳 x P hP ⟶ 𝒳 :=
  fullSubcategoryInclusion 𝒳 P hP.2.choose

end AlgebraicGeometry.Stack

end
