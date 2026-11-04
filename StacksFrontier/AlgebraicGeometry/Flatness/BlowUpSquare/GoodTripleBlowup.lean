module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTriple

/-!
# The universal good-triple modification of a perfect complex and a divisor

Let `(X, D, M)` be a triple as in Situation 0F8S.  Stacks tag 0GTY asserts that there is a
*unique* morphism `b : X' ⟶ X` such that

1. the pullback `D' = b⁻¹D` is defined and `(X', D', Lb^*M)` is a good triple, and
2. every `h : Y ⟶ X` for which `E = h⁻¹D` is defined and `(Y, E, Lh^*M)` is a good triple
   factors uniquely through `b`.

This file names the two conditions — `IsGoodOver` for the condition appearing in (1) and in the
hypothesis of (2), and `IsGoodBlowup` for their conjunction — and proves the *uniqueness* half
of tag 0GTY: a morphism satisfying (1) and (2) is unique up to a unique isomorphism over `X`,
equivalently it is a terminal object of the category of morphisms to `X` that are good for the
triple.

## Main definitions

* `AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodOver`: `h : Y ⟶ X` has defined pullback
  of `D` and makes `(Y, h⁻¹D, Lh^*M)` a good triple.  This is condition (1) for `b`, and the
  hypothesis of condition (2) for a test morphism `h`.
* `AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowup`: the conjunction of (1) and (2),
  i.e. the property that tag 0GTY asserts of a unique `b`.
* `AlgebraicGeometry.ComplexAndDivisorSituation.GoodOver`: the objects of `Sch/X` that are good
  for the triple, as an object property; its full subcategory is the category in which a
  morphism as in tag 0GTY is terminal.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.isGoodBlowup_id`: if `𝟙 X` is good for the
  triple then it has properties (1) and (2), so the morphism of tag 0GTY exists and is the
  identity.
* `AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowup.isIso_of_isGoodOver_id`: over such
  a triple, any morphism with properties (1) and (2) is an isomorphism.
* `AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowup.eq_id_of_comp_eq`: a self-map of
  `X'` over `X` is the identity.
* `AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowup.existsUnique_iso`: any two
  morphisms with properties (1) and (2) are identified by a unique isomorphism over `X`.  This
  is the uniqueness assertion of tag 0GTY.
* `AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowup.nonempty_isTerminal`: a morphism
  with properties (1) and (2) is a terminal object of the category of good morphisms to `X`.
* `AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowup.of_isTerminal`: conversely, a good
  morphism that is terminal in that category has property (2).

## What of tag 0GTY is proved here

This file is the *formal* half of the tag: the two conditions are named, and everything that
follows from them alone is proved here.  The morphism they describe is built in
`GoodBlowupGluing.lean` and shown to have them in `GoodBlowupIsGood.lean` and
`GoodBlowupUniversal.lean`, which is where the existence assertion of the tag,
`AlgebraicGeometry.ComplexAndDivisorSituation.existsUnique_isGoodBlowup`, is registered
(`GoodBlowupTag.lean`), alongside the affine-chart description of the morphism.

Three statements here carry `@[stacks 0GTY "..."]`.  The *uniqueness* assertion is
`AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowup.existsUnique_iso`: any two morphisms
with properties (1) and (2) are identified by a unique isomorphism over `X`, which is what
uniqueness of the tag's morphism means.  The other two describe the morphism over a triple for
which `𝟙 X` is already good, where it may be taken to be the identity:
`AlgebraicGeometry.ComplexAndDivisorSituation.isGoodBlowup_id` and
`AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowup.isIso_of_isGoodOver_id`.

The centre of the blowup over an affine chart is
`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.blowupCentre` (`GoodTriple.lean`), of
finite type and supported on the divisor; the blowing up of the chart in it is a
`(U \ D)`-admissible blowing up and the pulled-back triple is good
(`AffineChart.isAdmissibleBlowup_blowUpToBase_blowupCentreIdealSheaf` and
`AffineChart.isGoodOver_chartBlowupToBase` in `ChartBlowupAdmissible.lean`), and it has the tag's
universal property over the chart (`AffineChart.existsUnique_lift_chartBlowup` in
`ChartBlowupUniversal.lean`).

## Implementation notes

`IsGoodOver` is a two-field structure rather than an `∃`-statement so that the goodness of the
pulled-back triple can refer to the proof that the pullback of the divisor is defined; by proof
irrelevance this does not depend on which proof is used.

Uniqueness is extracted from the universal property alone, with no geometry: `b₁` is good over
`X`, hence factors uniquely through `b₂` and conversely, and both composites are identities
because the identity is the unique factorization of `bᵢ` through itself.  The terminality
statement is phrased as `Nonempty (CategoryTheory.Limits.IsTerminal _)`, matching
`Stacks.Blowup.nonempty_isTerminal_of_forall_exists`, since `IsTerminal` is data and the
factorizations are only given to exist.

## References

* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

variable {S : ComplexAndDivisorSituation.{u, d}}

/-- A morphism `h : Y ⟶ X` is **good** for the triple `(X, D, M)` if the pullback `E = h⁻¹D` of
the effective Cartier divisor is defined and `(Y, E, Lh^*M)` is a good triple.  This is
condition (1) of Stacks tag 0GTY for the morphism it produces, and it is the hypothesis on a
test morphism in condition (2). -/
structure IsGoodOver (S : ComplexAndDivisorSituation.{u, d}) {Y : Scheme.{u}} (h : Y ⟶ S.X) :
    Prop where
  /-- The pullback `h⁻¹D` of the divisor is defined. -/
  pullbackDefined : Stacks.Divisors.IsPullbackDefined h S.D
  /-- The pulled-back triple `(Y, h⁻¹D, Lh^*M)` is a good triple. -/
  isGoodTriple : IsGoodTriple (S.pullback h pullbackDefined)

/-- The conjunction of conditions (1) and (2) of Stacks tag 0GTY for a morphism
`b : X' ⟶ X`: the triple pulled back along `b` is good, and every morphism to `X` that is good
for the triple factors uniquely through `b`.  Tag 0GTY asserts that exactly one morphism to `X`
has this property. -/
structure IsGoodBlowup (S : ComplexAndDivisorSituation.{u, d}) {X' : Scheme.{u}}
    (b : X' ⟶ S.X) : Prop where
  /-- Condition (1): the triple pulled back along `b` is good. -/
  isGoodOver : S.IsGoodOver b
  /-- Condition (2): a morphism that is good for the triple factors uniquely through `b`. -/
  existsUnique_lift : ∀ {Y : Scheme.{u}} (h : Y ⟶ S.X), S.IsGoodOver h →
    ∃! k : Y ⟶ X', k ≫ b = h

/-- **The existence assertion of Stacks tag 0GTY for a triple that is already good.**  If `𝟙 X`
is good for `(X, D, M)` then it has both properties (1) and (2) of the tag: property (1) is the
hypothesis, and every morphism `h : Y ⟶ X` factors through `𝟙 X` uniquely, by `h` itself. -/
@[stacks 0GTY "the morphism `b`, in the case where `𝟙 X` is good for the triple: the identity \
of `X` then has both properties of the tag, so `b` may be taken to be `𝟙 X`"]
theorem isGoodBlowup_id (h : S.IsGoodOver (𝟙 S.X)) : S.IsGoodBlowup (𝟙 S.X) :=
  ⟨h, fun g _ => ⟨g, Category.comp_id g, fun k hk => by simpa using hk⟩⟩

namespace IsGoodBlowup

variable {X' : Scheme.{u}} {b : X' ⟶ S.X}

/-- A self-map of `X'` over `X` is the identity: both it and the identity are factorizations of
`b` through `b`, which are unique. -/
theorem eq_id_of_comp_eq (hb : S.IsGoodBlowup b) {k : X' ⟶ X'} (hk : k ≫ b = b) :
    k = 𝟙 X' := by
  obtain ⟨_, _, huniq⟩ := hb.existsUnique_lift b hb.isGoodOver
  rw [huniq k hk, ← huniq (𝟙 X') (Category.id_comp b)]

/-- **The uniqueness assertion of Stacks tag 0GTY.**  Two morphisms to `X` with properties (1)
and (2) are identified by a unique isomorphism over `X`.

Each factors through the other by (2), and the two composites are identities by
`AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowup.eq_id_of_comp_eq`; an isomorphism
over `X` is determined by its underlying morphism, which (2) pins down. -/
@[stacks 0GTY "the uniqueness assertion: any two morphisms to `X` with properties (1) and (2) \
of the tag are identified by a unique isomorphism over `X`, which is what it means for the \
morphism the tag describes to be unique"]
theorem existsUnique_iso {X₁ X₂ : Scheme.{u}} {b₁ : X₁ ⟶ S.X} {b₂ : X₂ ⟶ S.X}
    (h₁ : S.IsGoodBlowup b₁) (h₂ : S.IsGoodBlowup b₂) :
    ∃! e : X₁ ≅ X₂, e.hom ≫ b₂ = b₁ := by
  obtain ⟨k, hk, hkuniq⟩ := h₂.existsUnique_lift b₁ h₁.isGoodOver
  obtain ⟨l, hl, _⟩ := h₁.existsUnique_lift b₂ h₂.isGoodOver
  exact ⟨⟨k, l, h₁.eq_id_of_comp_eq (by rw [Category.assoc, hl, hk]),
    h₂.eq_id_of_comp_eq (by rw [Category.assoc, hk, hl])⟩, hk,
    fun e he => Iso.ext (hkuniq e.hom he)⟩

/-- A morphism with properties (1) and (2) of Stacks tag 0GTY over a triple for which `𝟙 X` is
already good is an isomorphism.  By
`AlgebraicGeometry.ComplexAndDivisorSituation.isGoodBlowup_id` the identity also has those
properties, so the two are identified over `X` by
`AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodBlowup.existsUnique_iso`. -/
@[stacks 0GTY "the morphism `b` over a triple for which `𝟙 X` is good: any morphism with the \
two properties of the tag is then an isomorphism"]
theorem isIso_of_isGoodOver_id (hb : S.IsGoodBlowup b) (h : S.IsGoodOver (𝟙 S.X)) : IsIso b := by
  obtain ⟨e, he, -⟩ := hb.existsUnique_iso (isGoodBlowup_id h)
  rw [← he, Category.comp_id]
  infer_instance

end IsGoodBlowup

/-- The objects `Y ⟶ X` of `Sch/X` that are good for the triple `(X, D, M)`.  A morphism as in
Stacks tag 0GTY is exactly a terminal object of the corresponding full subcategory. -/
abbrev GoodOver (S : ComplexAndDivisorSituation.{u, d}) : ObjectProperty (Over S.X) :=
  fun Y => S.IsGoodOver Y.hom

namespace IsGoodBlowup

variable {X' : Scheme.{u}} {b : X' ⟶ S.X}

/-- A morphism with properties (1) and (2) of Stacks tag 0GTY is a terminal object of the
category of morphisms to `X` that are good for the triple. -/
theorem nonempty_isTerminal (hb : S.IsGoodBlowup b) :
    Nonempty (IsTerminal (⟨Over.mk b, hb.isGoodOver⟩ : S.GoodOver.FullSubcategory)) := by
  choose k hk huniq using fun Y : S.GoodOver.FullSubcategory =>
    hb.existsUnique_lift Y.obj.hom Y.property
  exact ⟨IsTerminal.ofUniqueHom (fun Y => ObjectProperty.homMk (Over.homMk (k Y) (hk Y)))
    fun Y m => by
      apply ObjectProperty.hom_ext
      exact Over.OverMorphism.ext (huniq Y _ (Over.w m.hom))⟩

/-- Conversely, a morphism that is good for the triple and terminal in the category of good
morphisms to `X` has property (2) of Stacks tag 0GTY, hence both properties. -/
theorem of_isTerminal (hgood : S.IsGoodOver b)
    (ht : IsTerminal (⟨Over.mk b, hgood⟩ : S.GoodOver.FullSubcategory)) :
    S.IsGoodBlowup b := by
  refine ⟨hgood, fun {Y} h hh => ?_⟩
  let Z : S.GoodOver.FullSubcategory := ⟨Over.mk h, hh⟩
  exact ⟨(ht.from Z).hom.left, Over.w (ht.from Z).hom, fun k hk =>
    congrArg (fun g => g.hom.left)
      (ht.hom_ext (ObjectProperty.homMk (Over.homMk k hk)) (ht.from Z))⟩

end IsGoodBlowup

end AlgebraicGeometry.ComplexAndDivisorSituation

end
