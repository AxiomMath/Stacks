module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSituation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmoothBaseChange

/-!
# The analytic reformulation of the compatibility condition

In the situation of Artin's theorem on contractions (Stacks 0GH8) the functor whose
algebraicity gives the contraction sends a locally Noetherian scheme `V` over `S` to the set
of triples `(Z, u' : V ∖ Z ⟶ U', x̂ : V_{/Z} ⟶ W)` subject to four conditions, of which the
fourth — that `u'` and `x̂` be *compatible* — is the existence of a commutative diagram.
**Stacks 0GID** offers a way to think about that fourth condition: were there a category
`An_S` of analytic spaces over `S` and an analytification functor `Y ↦ Y^an` on locally
Noetherian formal algebraic spaces over `S`, the condition ought to become the requirement
that a single square of analytic spaces commute.

The remark is explicitly *not* mathematically precise: `An_S` and `Y ↦ Y^an` are called
fictitious in the source, and the final sentence asserts the equivalence with condition (4)
only "under some assumptions of faithfulness of the analytification functor", which the
source does not state. What *is* precise is everything the remark asks of the fiction, once
that fiction is carried as a hypothesis rather than constructed: the properties (a)–(d)
listed below, the square itself, and the remark's own observation that the square makes
sense. That is what this module formalizes.

## What is formalized and what is not

The remark requires of `An_S` and of `Y ↦ Y^an`:

* **(a)** `An_S` has open and closed immersions, and the open complement of a closed
  immersion can be taken;
* **(b)** for every `Y` the morphism `Y_red ⟶ Y` induces a closed immersion
  `Y_red^an ⟶ Y^an`, and `Y^rig` is by definition its open complement in `Y^an`;
* **(c)** for an algebraic space `Y` and a closed `Z ⊆ Y` the morphism `Y_{/Z} ⟶ Y` induces
  an open immersion `Y_{/Z}^an ⟶ Y^an`, which in turn induces an open immersion
  `can : (Y_{/Z})^rig ⟶ (Y ∖ Z)^an`;
* **(d)** a formal modification `g : Y' ⟶ Y` of locally Noetherian formal algebraic spaces
  induces an isomorphism `g^rig : (Y')^rig ⟶ Y^rig`.

All four are fields of `AlgebraicGeometry.Artin.Analytification`. The square is
`AlgebraicGeometry.Artin.ContractionSituation.AnalyticSquareCommutes`, and the remark's
sentence "this makes sense as `g^rig : (X'_{/T'})^rig ⟶ W^rig` is an isomorphism and
`U' = X' ∖ T'`" is
`AlgebraicGeometry.Artin.ContractionSituation.isIso_rigFunctor_map_g_and_range_pointsMap_ι_U'`.

The final clause of the remark — that the requirement is *equivalent* to compatibility
condition (4) — is **deliberately not stated anywhere in this module**, not even as a
hypothesis. The source conditions it on unstated faithfulness assumptions, so there is no
precise statement to formalize; claiming the equivalence would assert something the source
does not.

## Main definitions

* `AlgebraicGeometry.Artin.Analytification`: **Stacks 0GID**, the analytification data the
  remark posits, together with the properties (a)–(d) it requires of them.
* `AlgebraicGeometry.Artin.ContractionSituation.PreCompatibilityTriple`: a triple
  `(Z, u', x̂)` satisfying conditions (1), (2) and (3) of the unlabelled prose preceding the
  remark. Those conditions carry no Stacks tag of their own, so this definition carries no
  tag. On the name, and why the existing `Triple` is not reused, see the implementation notes.
* `AlgebraicGeometry.Artin.ContractionSituation.gRigIso`: the isomorphism
  `g^rig : (X'_{/T'})^rig ≅ W^rig` supplied by property (d), whose inverse appears in the
  left-hand column of the square.
* `AlgebraicGeometry.Artin.ContractionSituation.AnalyticSquareCommutes`: **Stacks 0GID**,
  the requirement that the remark's square commute.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.isIso_rigFunctor_map_g_and_range_pointsMap_ι_U'`:
  **Stacks 0GID**, the remark's own observation that the requirement is well formed, namely
  that `g^rig` is an isomorphism — so that the composite `(g^rig)⁻¹ ∘ x̂^rig` forming the
  left-hand column exists — and that `|U'| = |X'| ∖ T'`, so that the bottom row of the
  square may be read as landing in `(X' ∖ T')^an`.
* `AlgebraicGeometry.Artin.ContractionSituation.analyticSquareCommutes_iff`: the square
  commutes exactly when there is a *unique* morphism
  `(V_{/Z})^rig ⟶ (X'_{/T'})^rig` over `x̂^rig` along `g^rig` making the resulting square
  commute. This is the inverse-free form of the requirement, and is the precise sense in
  which the invertibility of `g^rig` is what makes the requirement meaningful.

## Implementation notes

**The fiction is a hypothesis.** `An_S` and `Y ↦ Y^an` are carried as the parameters and
fields of `Analytification`: the ambient category is a parameter `An` with a `Category`
instance, and the two assignments `Y ↦ Y^an`, `Y ↦ Y^rig` are honest `CategoryTheory.Functor`s
out of `AlgebraicGeometry.FormalSpace.FppfSheaf`. Proving results about an arbitrary such
structure is a generalization of the remark, not a weakening of it: nothing is asserted to
exist.

**Totality of the two functors is an encoding choice.** The remark's functor is defined on
locally Noetherian formal algebraic spaces over `S`, whereas `anFunctor` and `rigFunctor`
below are defined on the whole ambient category `FormalSpace.FppfSheaf B S hS` of fppf
sheaves of `Type (u + 1)`. The reason is that the square's two right-hand corners are
`(V ∖ Z)^an` and `(X' ∖ T')^an`, analytifications of *algebraic* spaces; the remark reads
those through the inclusion of algebraic spaces into formal algebraic spaces, which is
Stacks 0AIL, and this library does not have 0AIL — there is no theorem here that an
algebraic space is a formal algebraic space. Restricting the two functors to the locally
Noetherian formal algebraic spaces would therefore make the square fail to typecheck, and
the only repairs would be to invent 0AIL or to carry unprovable local-Noetherianity
witnesses for four separate objects. Totality is strictly more data than the remark offers,
so it is a *stronger* hypothesis; to keep that from leaking into the requirements, every
field that imposes a condition keeps exactly the hypotheses the source states — (b) is
quantified over reductions, (c) over algebraic spaces with a closed subset, and (d) over
formal modifications. An algebraic space is read as an object of `FppfSheaf B S hS` by
`AlgebraicGeometry.Space.sheafifiedULift`, the fppf sheafification of its universe lift,
which is the same device `AlgebraicGeometry.Space.completionSheaf` already uses and which
needs nothing proved.

**Which of the immersion notions are kept.** Property (a) asks for open immersions, closed
immersions, and open complements; these are kept, as the three uninterpreted fields
`IsOpenImmersion`, `IsClosedImmersion` and `IsOpenComplement` together with
`exists_isOpenComplement` and `isOpenImmersion_of_isOpenComplement`. They are not a theory of
immersions in an arbitrary category and are not meant to be: they exist so that (b) and (c)
can be stated at all. (b) says that the analytification of a reduction is a closed immersion
and that `Y^rig ⟶ Y^an` is its open complement — without the two predicates this is not
expressible, and `rigFunctor` would be an entirely unconstrained functor. (c) likewise says
that two specific morphisms are open immersions. Nothing beyond this is assumed: in
particular no closure properties, no relation to monomorphisms, and no uniqueness of
complements. None of the three tagged results uses any of these five fields, so dropping them
would not weaken the results — it would only make the structure say less than the remark
asks, which is why they are kept.

**Why the triple here is not `ContractionSituation.Triple`.** There is a structure of that
name in `StacksFrontier/AlgebraicGeometry/Artin/ContractionFunctor.lean`, and it is *not* the
one the remark needs. That one carries a sixth field `compatible`, asserting condition (4) by
way of a `CompatibilityWitness`. Condition (4) is exactly what Stacks 0GID sets out to
explain, so a triple that already assumes it is the wrong input: the remark fixes a triple
satisfying (1), (2) and (3) and then asks what (4) ought to mean. The structure here therefore
has four fields and no compatibility condition, and is named
`PreCompatibilityTriple` — the data of a triple *before* compatibility is imposed. The two
are deliberately distinct rather than one being a specialisation of the other.

**What is dropped.** `Y ↦ Y_red` is not an operation here. Stacks 0AIN,
`AlgebraicGeometry.FormalSpace.exists_isReduction_of_isFormalAlgebraicSpace`, gives existence
rather than a canonical choice (see the documentation of
`AlgebraicGeometry.Artin.ContractionSituation`), so property (b) is quantified over an
arbitrary morphism `i : Y_red ⟶ Y` exhibiting `Y_red` as a reduction of `Y` in the sense of
`AlgebraicGeometry.FormalSpace.IsReduction`, rather than applying an operation. For the same
reason `Y^rig` is a field in its own right and not defined as a complement; the definitional
content of `Y^rig = Y^an ∖ Y_red^an` is recorded instead by the field
`isOpenComplement_rigι`. The inclusion `Y^rig ⟶ Y^an` is carried as a
plain family of morphisms rather than a natural transformation, because the remark does not
assert its naturality and no result here needs it.

**A typo in the source.** The left-hand column of the remark's displayed square is printed as
`(g^{rig})^{-1} ∘ \hat x^{an}`, but its domain is `(V_{/Z})^{rig}` and its codomain
`(X'_{/T'})^{rig}`, so the second factor must be `\hat x^{rig}`; `\hat x^{an}` would not
compose. It is read as `x̂^rig` here.

**Conditions (1), (2), (3).** These live in unlabelled prose in the source, between Situation
0GH8 and the remark, and so carry no tag; `ContractionSituation.PreCompatibilityTriple` is
therefore untagged. Condition (3), that `x̂` be adic, is read here in the chart form over
`WAdm^{Noeth}`, `AlgebraicGeometry.FormalSpace.IsAdicOnEveryAffineEtaleDiagramNoetherian`,
which is the form the rest of the contraction development uses; Definition 0AQ3 itself takes
adicness to be representability by algebraic spaces,
`AlgebraicGeometry.FormalSpace.IsAdicMorphism`. "`V` a locally Noetherian
scheme over `S`" is an object `V` of the big fppf site over `S` whose underlying scheme is
locally Noetherian, read as an algebraic space by `CategoryTheory.yoneda`; the local
Noetherianity of `V` is a hypothesis of the ambient prose and is not used by any result
below, so it is not carried.

## References

* [Stacks Project, Tag 025Z](https://stacks.math.columbia.edu/tag/025Z)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BY](https://stacks.math.columbia.edu/tag/03BY)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 0AIL](https://stacks.math.columbia.edu/tag/0AIL)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
* [Stacks Project, Tag 0AQ3](https://stacks.math.columbia.edu/tag/0AQ3)
* [Stacks Project, Tag 0GDK](https://stacks.math.columbia.edu/tag/0GDK)
* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GID](https://stacks.math.columbia.edu/tag/0GID)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry.Artin

attribute [local instance] Space.pointTopology

/-- **Stacks 0GID.** The analytification data the remark posits, over a base `S` contained in
a big fppf site `B` and with values in a category `An` standing for the fictitious category
`An_S` of analytic spaces over `S`: an analytification `Y ↦ Y^an`, its rigid part
`Y ↦ Y^rig` with the inclusion `Y^rig ⟶ Y^an`, the notions of open immersion, closed
immersion and open complement in `An`, and the comparison morphisms
`can : (Y_{/Z})^rig ⟶ (Y ∖ Z)^an`, subject to the four requirements the remark imposes.

Nothing here is asserted to exist: this is the remark's fiction carried as a hypothesis, so
that what the remark deduces from it can be stated and proved. See the module documentation
for the two places where the encoding departs from the source — the two functors are total on
the ambient category of fppf sheaves rather than defined only on locally Noetherian formal
algebraic spaces, and `Y ↦ Y_red` is not an operation, property (b) being quantified over
reductions instead. -/
@[stacks 0GID "the fictitious category of analytic spaces over S and the fictitious \
analytification functor, together with the four properties the remark requires of them: (a) \
that open immersions, closed immersions and open complements of closed immersions exist in \
An_S, (b) that the analytification of a reduction Y_red ⟶ Y is a closed immersion with \
Y^rig ⟶ Y^an as its open complement, (c) that for an algebraic space Y and a closed Z the \
analytification of Y_{/Z} ⟶ Y is an open immersion and induces an open immersion can : \
(Y_{/Z})^rig ⟶ (Y ∖ Z)^an, and (d) that the rigid part of a formal modification is an \
isomorphism. The remark's closing claim, that the resulting requirement is equivalent to \
compatibility condition (4), is not stated: the source makes it only under assumptions of \
faithfulness of the analytification functor that it does not formulate"]
structure Analytification (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (An : Type v) [Category.{w} An] where
  /-- The analytification functor `Y ↦ Y^an`. -/
  anFunctor : FormalSpace.FppfSheaf B S hS ⥤ An
  /-- The rigid part `Y ↦ Y^rig` of the analytification, which the remark defines as the open
  complement of `Y_red^an` in `Y^an`; see `isOpenComplement_rigι`. -/
  rigFunctor : FormalSpace.FppfSheaf B S hS ⥤ An
  /-- The inclusion `Y^rig ⟶ Y^an` of the rigid part into the analytification. -/
  rigι : ∀ Y : FormalSpace.FppfSheaf B S hS, rigFunctor.obj Y ⟶ anFunctor.obj Y
  /-- **Property (a).** The open immersions of `An_S`. -/
  IsOpenImmersion : MorphismProperty An
  /-- **Property (a).** The closed immersions of `An_S`. -/
  IsClosedImmersion : MorphismProperty An
  /-- **Property (a).** The relation "`j : C ⟶ D` exhibits `C` as the open complement of the
  closed immersion `i : A ⟶ D`". -/
  IsOpenComplement : ∀ {A C D : An}, (A ⟶ D) → (C ⟶ D) → Prop
  /-- **Property (a).** The open complement of a closed immersion can be taken. -/
  exists_isOpenComplement : ∀ {A D : An} (i : A ⟶ D), IsClosedImmersion i →
    ∃ (C : An) (j : C ⟶ D), IsOpenComplement i j
  /-- **Property (a).** The open complement of a closed immersion is an open immersion. -/
  isOpenImmersion_of_isOpenComplement : ∀ {A C D : An} {i : A ⟶ D} {j : C ⟶ D},
    IsClosedImmersion i → IsOpenComplement i j → IsOpenImmersion j
  /-- **Property (b).** The morphism `Y_red ⟶ Y` from a reduction induces a closed immersion
  `Y_red^an ⟶ Y^an`. -/
  isClosedImmersion_anFunctor_map_of_isReduction :
    ∀ (Y Yred : FormalSpace.FppfSheaf B S hS) (i : Yred ⟶ Y),
      FormalSpace.IsReduction B S hS Y Yred i → IsClosedImmersion (anFunctor.map i)
  /-- **Property (b).** `Y^rig` is the open complement of `Y_red^an` in `Y^an`. -/
  isOpenComplement_rigι :
    ∀ (Y Yred : FormalSpace.FppfSheaf B S hS) (i : Yred ⟶ Y),
      FormalSpace.IsReduction B S hS Y Yred i → IsOpenComplement (anFunctor.map i) (rigι Y)
  /-- **Property (c).** For an algebraic space `Y` and a closed subset `Z ⊆ |Y|`, the
  morphism `Y_{/Z} ⟶ Y` induces an open immersion `Y_{/Z}^an ⟶ Y^an`. -/
  isOpenImmersion_anFunctor_map_completionSheafInclusion :
    ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS Y →
      ∀ Z : Set (Space.points B S hS Y), IsClosed Z →
        IsOpenImmersion (anFunctor.map (Space.completionSheafInclusion B S hS Y Z))
  /-- **Property (c).** The comparison morphism `can : (Y_{/Z})^rig ⟶ (Y ∖ Z)^an`, for an
  algebraic space `Y` and a closed subset `Z ⊆ |Y|`. -/
  can : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS Y →
    ∀ Z : Set (Space.points B S hS Y), IsClosed Z →
      (rigFunctor.obj (Space.completionSheaf B S hS Y Z) ⟶
        anFunctor.obj (Space.sheafifiedULift B S hS
          (Space.openSubspaceOfPoints B S hS Y Zᶜ).toFunctor))
  /-- **Property (c).** The comparison morphism `can` is an open immersion. -/
  isOpenImmersion_can : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hY : IsAlgebraicSpace B S hS Y) (Z : Set (Space.points B S hS Y)) (hZ : IsClosed Z),
      IsOpenImmersion (can Y hY Z hZ)
  /-- **Property (d).** A formal modification `g : Y' ⟶ Y` of locally Noetherian formal
  algebraic spaces induces an isomorphism `g^rig : (Y')^rig ⟶ Y^rig`. -/
  isIso_rigFunctor_map_of_isFormalModification :
    ∀ {Y Y' : FormalSpace.FppfSheaf B S hS} (f : Y ⟶ Y'),
      FormalSpace.IsFormalModification B S hS f → IsIso (rigFunctor.map f)

namespace ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A triple `(Z, u', x̂)` over an object `V` of the big fppf site over `S`, satisfying
conditions (1), (2) and (3) of the prose following Situation 0GH8: `Z` is a closed subset of
the point space of `V`, `u'` is a morphism `V ∖ Z ⟶ U'` over `S`, and `x̂` is an adic
morphism `V_{/Z} ⟶ W` of formal algebraic spaces over `S`.

Condition (4), the compatibility of `u'` and `x̂`, is deliberately absent: Stacks 0GID is
about a way of thinking about that condition, and takes a triple satisfying only (1), (2) and
(3) as its input.

These three conditions appear in unlabelled prose in the source and carry no Stacks tag, so
this definition carries none either. -/
structure PreCompatibilityTriple (c : ContractionSituation B S hS) (V : BigFppfOver B S hS) where
  /-- **Condition (1).** The closed subset `Z ⊆ V`, as a subset of the point space of `V` in
  the sense of Stacks 03BU. -/
  Z : Set (Space.points B S hS (yoneda.obj V))
  /-- **Condition (1).** `Z` is closed in the topology of Stacks 03BY. -/
  isClosed_Z : IsClosed Z
  /-- **Condition (2).** The morphism `u' : V ∖ Z ⟶ U'` over `S`, where `V ∖ Z` is the open
  subspace of `V` with point set the complement of `Z` and `U'` is the open subspace of `X'`
  with point set the complement of `T'`. -/
  u' : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) Zᶜ).toFunctor ⟶ c.U'.toFunctor
  /-- **Condition (3).** The morphism `x̂ : V_{/Z} ⟶ W` out of the completion of `V` along
  `Z` of Stacks 0AMC. -/
  x : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ c.W
  /-- **Condition (3).** `x̂` is adic, in the chart form over `WAdm^{Noeth}`. -/
  isAdicMorphism_x :
    FormalSpace.IsAdicOnEveryAffineEtaleDiagramNoetherian B S hS x

variable {An : Type v} [Category.{w} An] (c : ContractionSituation B S hS)
    (d : Analytification B S hS An)

/-- The isomorphism `g^rig : (X'_{/T'})^rig ≅ W^rig` of the situation of Stacks 0GH8,
supplied by property (d) of the analytification data applied to the formal modification `g`.
Its inverse is the second factor of the left-hand column of the remark's square. -/
noncomputable def gRigIso :
    d.rigFunctor.obj (Space.completionSheaf B S hS c.X' c.T') ≅ d.rigFunctor.obj c.W :=
  have h : IsIso (d.rigFunctor.map c.g) :=
    d.isIso_rigFunctor_map_of_isFormalModification c.g c.isFormalModification_g
  @asIso _ _ _ _ (d.rigFunctor.map c.g) h

/-- The morphism underlying `gRigIso c d` is `d.rigFunctor.map c.g`. -/
@[simp]
theorem gRigIso_hom : (gRigIso c d).hom = d.rigFunctor.map c.g := rfl

/-- **Stacks 0GID.** The requirement of the remark: that the square

```
        (V_{/Z})^rig  --can-->  (V ∖ Z)^an
            |                        |
  (g^rig)⁻¹ ∘ x̂^rig              (u')^an
            v                        v
      (X'_{/T'})^rig  --can-->  (X' ∖ T')^an
```

commute, for a triple `(Z, u', x̂)` satisfying conditions (1), (2), (3) and for analytification
data as the remark posits. The two horizontal morphisms are the comparison morphisms of
property (c), the right-hand column is the analytification of `u'`, and the left-hand column
is `x̂^rig` followed by the inverse of the isomorphism `g^rig` of property (d).

This is a requirement on the given data, and only that. Whether it is equivalent to
compatibility condition (4) is left open: the source asserts that equivalence only under
assumptions of faithfulness of the analytification functor which it does not state. -/
@[stacks 0GID "the requirement that the displayed square of analytic spaces commute: the \
comparison morphism can : (V_{/Z})^rig ⟶ (V ∖ Z)^an followed by the analytification of u' \
agrees with x̂^rig followed by the inverse of the isomorphism g^rig and then by can : \
(X'_{/T'})^rig ⟶ (X' ∖ T')^an. It is stated as a requirement on the posited analytification \
data, exactly as the source states it, and is not asserted to be equivalent to compatibility \
condition (4)"]
def AnalyticSquareCommutes {V : BigFppfOver B S hS} (t : PreCompatibilityTriple c V) : Prop :=
  d.can (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V) t.Z t.isClosed_Z ≫
      d.anFunctor.map (Space.sheafifiedULiftMap B S hS t.u') =
    d.rigFunctor.map t.x ≫ (gRigIso c d).inv ≫
      d.can c.X' c.isAlgebraicSpace_X' c.T' c.isClosed_T'

/-- **Stacks 0GID.** The remark's own observation that its requirement is well formed: in
Situation 0GH8 the morphism `g^rig : (X'_{/T'})^rig ⟶ W^rig` is an isomorphism, by property
(d) of the analytification data applied to the formal modification `g`, so that the composite
`(g^rig)⁻¹ ∘ x̂^rig` forming the left-hand column of the square exists; and `|U'| = |X'| ∖ T'`,
so that the bottom row of the square, which lands in the analytification of the open subspace
of `X'` complementary to `T'`, may be read as landing in `(X' ∖ T')^an`. -/
@[stacks 0GID "that the requirement is well formed, which is the remark's sentence \"this \
makes sense as g^rig : (X'_{/T'})^rig ⟶ W^rig is an isomorphism and U' = X' ∖ T'\": the \
first conjunct is the invertibility of g^rig, which is what lets the left-hand column of the \
square be formed as (g^rig)⁻¹ ∘ x̂^rig, and the second is that the point set of U' is the \
complement of T'"]
theorem isIso_rigFunctor_map_g_and_range_pointsMap_ι_U' :
    IsIso (d.rigFunctor.map c.g) ∧
      Set.range (Space.pointsMap B S hS c.U'.toFunctor c.U'.ι) = c.T'ᶜ :=
  ⟨d.isIso_rigFunctor_map_of_isFormalModification c.g c.isFormalModification_g,
    c.range_pointsMap_ι_U'⟩

/-- The inverse-free form of the remark's requirement: the square commutes exactly when there
is a unique morphism `h : (V_{/Z})^rig ⟶ (X'_{/T'})^rig` with `h` followed by `g^rig` equal
to `x̂^rig` and with the square formed from `h` commutative.

This is the precise content of the remark's "this makes sense": the left-hand column of the
square is not given, it is the unique filler over `x̂^rig` along `g^rig`, and it exists
because `g^rig` is an isomorphism. -/
@[stacks 0GID "that the requirement is well formed, in the inverse-free form that carries the \
mathematical content of the remark's sentence \"this makes sense as g^rig is an \
isomorphism\": the square commutes exactly when there is a UNIQUE filler h over x̂^rig along \
g^rig making the square formed from h commute. The left-hand column of the source's square is \
not given data, it is that filler, and it exists and is unique precisely because g^rig is \
invertible by property (d). This is the substantive reading; the conjunction in \
AlgebraicGeometry.Artin.ContractionSituation.isIso_rigFunctor_map_g_and_range_pointsMap_ι_U' \
is the literal reading of the same sentence"]
theorem analyticSquareCommutes_iff {V : BigFppfOver B S hS} (t : PreCompatibilityTriple c V) :
    AnalyticSquareCommutes c d t ↔
      ∃! h : d.rigFunctor.obj (Space.completionSheaf B S hS (yoneda.obj V) t.Z) ⟶
          d.rigFunctor.obj (Space.completionSheaf B S hS c.X' c.T'),
        h ≫ d.rigFunctor.map c.g = d.rigFunctor.map t.x ∧
          d.can (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V) t.Z t.isClosed_Z ≫
              d.anFunctor.map (Space.sheafifiedULiftMap B S hS t.u') =
            h ≫ d.can c.X' c.isAlgebraicSpace_X' c.T' c.isClosed_T' := by
  have key : ∀ h : d.rigFunctor.obj (Space.completionSheaf B S hS (yoneda.obj V) t.Z) ⟶
      d.rigFunctor.obj (Space.completionSheaf B S hS c.X' c.T'),
      h ≫ d.rigFunctor.map c.g = d.rigFunctor.map t.x ↔
        h = d.rigFunctor.map t.x ≫ (gRigIso c d).inv := by
    intro h
    rw [(gRigIso c d).eq_comp_inv, gRigIso_hom]
  constructor
  · intro hsq
    exact ⟨d.rigFunctor.map t.x ≫ (gRigIso c d).inv, ⟨(key _).2 rfl, by rwa [Category.assoc]⟩,
      fun h' hh' ↦ (key h').1 hh'.1⟩
  · rintro ⟨h, ⟨hg, hsq⟩, -⟩
    rwa [(key h).1 hg, Category.assoc] at hsq

end ContractionSituation

end AlgebraicGeometry.Artin

end
