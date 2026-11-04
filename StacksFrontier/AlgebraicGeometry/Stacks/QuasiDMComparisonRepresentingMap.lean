module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.PropertySchemePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalSchemePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiDMChartDimensionComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemePointProductPasting
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFibreProductProperties

/-!
# The comparison 1-morphism of a quasi-DM 1-morphism, as a morphism of algebraic spaces

Let `h : 𝒵 ⟶ 𝒯` be a quasi-DM 1-morphism of algebraic stacks over `S` and let `x₁ : 𝒯₁ ⟶ 𝒵`,
`x₂ : 𝒯₂ ⟶ 𝒵` be 1-morphisms into `𝒵` from algebraic stacks representable by algebraic spaces.
**Stacks 0CPL**, part (1) — equivalently **Stacks 050H**, part (5) — makes the comparison
1-morphism `𝒯₁ ×_𝒵 𝒯₂ ⟶ 𝒯₁ ×_𝒯 𝒯₂` locally quasi-finite in the sense of **Stacks 04XB**, a
condition on its base changes to the schemes of the site. This file reads that condition as
local quasi-finiteness of a *morphism of algebraic spaces*: the two 2-fibre products are
representable by algebraic spaces, and the morphism of representing presheaves of **Stacks 04SW**
between them is locally quasi-finite.

## Main results

* `AlgebraicGeometry.Stack.isLocallyQuasiFinite_representingMap`: the bridge of Stacks 04XB at
  local quasi-finiteness, for a 1-morphism of represented categories fibred in groupoids.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpace_twoFibreProduct`:
  **Stacks 0300** at a 2-fibre product over an algebraic stack of two algebraic stacks
  representable by algebraic spaces. Used at both cospans of the comparison, it is the pair of
  representability witnesses the bridge needs.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyQuasiFinite_representingMap_mapBase`:
  Stacks 0CPL, part (1), the quasi-DM case, read as a statement about the induced morphism of
  representing algebraic spaces.
* `dimensionAtPoint_le_dimensionAtPoint_representingMap_mapBase`, in the same namespace: that
  comparison does not raise the dimension at a point, when the target of the comparison is
  locally of finite type over the spectrum of a field.

## Implementation notes

The forward half of the bridge of Stacks 04XB is
`AlgebraicGeometry.Stack.prop_representingMap_of_relativeProperty`, which asks that the property
may be tested on base changes along morphisms from representable presheaves. At local
quasi-finiteness that hypothesis is a theorem: local quasi-finiteness of morphisms of algebraic
spaces over `S` is local on the base for the fppf topology, **Stacks 0427**
(`AlgebraicGeometry.Space.isLocallyQuasiFinite_isLocalAtTarget_fppf`), and a property local on
the base may be tested on representable base changes by
`AlgebraicGeometry.Space.prop_homMk_of_forall_yoneda`. So the bridge below needs no hypothesis on
the property at all — only the two representing presheaves and the representability of the
1-morphism, the latter being
`AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_mapBase`, **Stacks 04XS**
part (1) at a base change of the relative diagonal.

The two representing presheaves are data, not content: nothing about local quasi-finiteness is
assumed of them, their existence is the theorem
`AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpace_twoFibreProduct` below,
and the conclusion holds for *every* pair of algebraic spaces representing the two 2-fibre
products, two such being isomorphic by `AlgebraicGeometry.Stack.representingIso`.

The cospan is taken at arbitrary algebraic stacks representable by algebraic spaces rather than
at algebraic-space-valued points as in
`AlgebraicGeometry.Stack.HigherDiagonal.isLocallyQuasiFinite_mapBase_of_isQuasiDM`. The 0CPL
statement is the same — `isLocallyQuasiFinite_mapBase_of_isQuasiDM` of
`AlgebraicGeometry.Stack.AlgebraicStacks`
is already stated at an arbitrary cospan — and the extra generality is what lets the second leg
be the 1-morphism of a field-valued point, whose source is the algebraic stack of a scheme of the
site and not the stack of an algebraic space.

Local finite type of the comparison, which the dimension bound needs beside local
quasi-finiteness, is read off the definition: local quasi-finiteness of a morphism of algebraic
spaces is the every-étale-chart condition of **Stacks 03MJ** at the infimum of local finite type
and the fibre condition (**Stacks 03XJ**, part (1)), so
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_mono` at the first projection gives it.

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
* [Stacks Project, Tag 0427](https://stacks.math.columbia.edu/tag/0427)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 0CPL](https://stacks.math.columbia.edu/tag/0CPL)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The bridge of Stacks 04XB at local quasi-finiteness.** Let `a : 𝒜 ⟶ 𝒞` be a 1-morphism
representable by algebraic spaces between two categories fibred in groupoids over the big fppf
site of `S` which are represented by algebraic spaces `F` and `G`. If `a` is locally
quasi-finite in the sense of Stacks 04XB — every algebraic space representing a base change of
`a` along a scheme-valued point of `𝒞` has locally quasi-finite structural morphism — then the
morphism `F ⟶ G` of representing presheaves of **Stacks 04SW** is locally quasi-finite.

This is `AlgebraicGeometry.Stack.prop_representingMap_of_relativeProperty` at local
quasi-finiteness, whose testability hypothesis is discharged by the fppf locality of
**Stacks 0427** through `AlgebraicGeometry.Space.prop_homMk_of_forall_yoneda`. -/
theorem isLocallyQuasiFinite_representingMap
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (a : 𝒜 ⟶ 𝒞)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a.hom)
    (hqf : IsLocallyQuasiFinite.{u, u, u + 1} B S hS a) :
    Space.IsLocallyQuasiFinite B S hS (representingMap B S hS 𝒜 𝒞 F G eF eG a) :=
  prop_representingMap_of_relativeProperty B S hS (Space.locallyQuasiFiniteProperty B S hS)
    a F G hF hG eF eG
    (fun _ _ => Space.prop_homMk_of_forall_yoneda.{u, u + 1} B S hS
      (Space.locallyQuasiFiniteProperty B S hS))
    ha hqf

namespace AlgebraicStacks

variable {𝒯₁ 𝒯₂ 𝒵 𝒯 : AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 0300 at a 2-fibre product over an algebraic stack.** For 1-morphisms
`x₁ : 𝒯₁ ⟶ 𝒵` and `x₂ : 𝒯₂ ⟶ 𝒵` of algebraic stacks over `S` with `𝒯₁` and `𝒯₂` representable
by algebraic spaces, the 2-fibre product `𝒯₁ ×_{x₁, 𝒵, x₂} 𝒯₂` is representable by an algebraic
space over `S`.

The projection to `𝒯₁` is a base change of `x₂`, which is representable by algebraic spaces
because `𝒵` is an algebraic stack — the consequence of **Stacks 045G** that Properties of Stacks,
Section 04XB uses without further mention — so Stacks 0300 applies with `𝒯₁` as the representable
base.

Applied at the cospan `(x₁, x₂)` and at the cospan `(x₁ ≫ h, x₂ ≫ h)` this supplies both
representing algebraic spaces that
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyQuasiFinite_representingMap_mapBase` reads the
comparison 1-morphism between. -/
theorem isRepresentableByAlgebraicSpace_twoFibreProduct (x₁ : 𝒯₁ ⟶ 𝒵) (x₂ : 𝒯₂ ⟶ 𝒵)
    (h𝒯₁ : IsRepresentableByAlgebraicSpace B S hS 𝒯₁.val)
    (h𝒯₂ : IsRepresentableByAlgebraicSpace B S hS 𝒯₂.val) :
    IsRepresentableByAlgebraicSpace B S hS
      (AlgebraicStacks.twoFibreProduct B S hS x₁ x₂).val :=
  isRepresentableByAlgebraicSpace_twoFibreProductSquare_pt B S hS x₂.hom x₁.hom
    (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒵.property h𝒯₂ x₂.hom)
    h𝒯₁

/-- **Stacks 0CPL, part (1), the quasi-DM case, between representing algebraic spaces.** Let
`h : 𝒵 ⟶ 𝒯` be a quasi-DM 1-morphism of algebraic stacks over `S`, let `x₁ : 𝒯₁ ⟶ 𝒵` and
`x₂ : 𝒯₂ ⟶ 𝒵` be 1-morphisms of algebraic stacks, and let `P` and `Q` be algebraic spaces over
`S` representing `𝒯₁ ×_{x₁, 𝒵, x₂} 𝒯₂` and `𝒯₁ ×_{x₁h, 𝒯, x₂h} 𝒯₂`. Then the morphism `P ⟶ Q`
of representing presheaves induced by the comparison 1-morphism is locally quasi-finite.

Stacks 0CPL part (1) gives the condition of Stacks 04XB
(`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyQuasiFinite_mapBase_of_isQuasiDM`,
**Stacks 050H** part (5)); the comparison 1-morphism is representable by algebraic spaces by
`AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_mapBase`; and
`AlgebraicGeometry.Stack.isLocallyQuasiFinite_representingMap` carries the condition over to the
morphism of representing presheaves. -/
theorem isLocallyQuasiFinite_representingMap_mapBase (x₁ : 𝒯₁ ⟶ 𝒵) (x₂ : 𝒯₂ ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯)
    (P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hP : IsAlgebraicSpace B S hS P) (hQ : IsAlgebraicSpace B S hS Q)
    (eP : StacksRepresentableCFG.EquivalenceOver
      (AlgebraicStacks.twoFibreProduct B S hS x₁ x₂).val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p)
    (eQ : StacksRepresentableCFG.EquivalenceOver
      (AlgebraicStacks.twoFibreProduct B S hS (x₁ ≫ h) (x₂ ≫ h)).val.val.p
      (presheafOfCategories (Q ⋙ typeToCat)).p)
    (hh : AlgebraicStacks.IsQuasiDM B S hS h) :
    Space.IsLocallyQuasiFinite B S hS
      (representingMap B S hS (AlgebraicStacks.twoFibreProduct B S hS x₁ x₂).val
        (AlgebraicStacks.twoFibreProduct B S hS (x₁ ≫ h) (x₂ ≫ h)).val P Q eP eQ
        (AlgebraicStacks.mapBase B S hS x₁ x₂ h).hom) :=
  isLocallyQuasiFinite_representingMap B S hS _ P Q hP hQ eP eQ
    (isRepresentableByAlgebraicSpaces_mapBase B S hS x₁ x₂ h)
    (isLocallyQuasiFinite_mapBase_of_isQuasiDM B S hS x₁ x₂ h hh)

/-- **The comparison 1-morphism of a quasi-DM 1-morphism does not raise the dimension at a point,
over the spectrum of a field.** In the situation of
`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyQuasiFinite_representingMap_mapBase`, suppose
in addition that the algebraic space `Q` representing `𝒯₁ ×_{x₁h, 𝒯, x₂h} 𝒯₂` is locally of
finite type over the field spectrum of a field-valued point of a presheaf on the site. Then at
every point of `P` the dimension of `P` is at most the dimension of `Q` at the image point.

This is the keystone
`AlgebraicGeometry.Space.dimensionAtPoint_le_dimensionAtPoint_of_isLocallyQuasiFinite_fieldTarget`
fed by the bridge: the comparison is locally quasi-finite by Stacks 0CPL part (1), and locally of
finite type because local quasi-finiteness of a morphism of algebraic spaces is the
every-étale-chart condition at a property whose first conjunct is local finite type
(**Stacks 03XJ**, part (1)). -/
theorem dimensionAtPoint_le_dimensionAtPoint_representingMap_mapBase
    (x₁ : 𝒯₁ ⟶ 𝒵) (x₂ : 𝒯₂ ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯)
    (P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hP : IsAlgebraicSpace B S hS P) (hQ : IsAlgebraicSpace B S hS Q)
    (eP : StacksRepresentableCFG.EquivalenceOver
      (AlgebraicStacks.twoFibreProduct B S hS x₁ x₂).val.val.p
      (presheafOfCategories (P ⋙ typeToCat)).p)
    (eQ : StacksRepresentableCFG.EquivalenceOver
      (AlgebraicStacks.twoFibreProduct B S hS (x₁ ≫ h) (x₂ ≫ h)).val.val.p
      (presheafOfCategories (Q ⋙ typeToCat)).p)
    (hh : AlgebraicStacks.IsQuasiDM B S hS h)
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : Space.FieldValuedPoint B S hS G)
    (g : Q ⟶ yoneda.obj (k.siteObject B S hS G))
    (hg : Space.IsLocallyOfFiniteType B S hS g) (x : Space.points B S hS P) :
    Space.dimensionAtPoint B S hS P hP x ≤
      Space.dimensionAtPoint B S hS Q hQ
        (Space.pointsMap B S hS P
          (representingMap B S hS (AlgebraicStacks.twoFibreProduct B S hS x₁ x₂).val
            (AlgebraicStacks.twoFibreProduct B S hS (x₁ ≫ h) (x₂ ≫ h)).val P Q eP eQ
            (AlgebraicStacks.mapBase B S hS x₁ x₂ h).hom) x) :=
  have hqf := isLocallyQuasiFinite_representingMap_mapBase B S hS x₁ x₂ h P Q hP hQ eP eQ hh
  Space.dimensionAtPoint_le_dimensionAtPoint_of_isLocallyQuasiFinite_fieldTarget B S hS hP hQ k
    _ g (Space.holdsOnEveryEtaleChart_mono B S hS (fun _ h' => h'.1) hqf) hqf hg x

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
