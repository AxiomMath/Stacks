module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentableUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.FullyFaithfulMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeResidualGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbeMonomorphism

/-!
# The reduced locally Noetherian one-point substack (Stacks 06MR)

Let `𝒵` be an algebraic stack over `S` satisfying the equivalent conditions of **Stacks 06MN**,
that is, reduced with a singleton space of points. **Stacks 06MR** asserts that there is a
*unique* strictly full subcategory `𝒵' ⊂ 𝒵` which is an algebraic stack satisfying the
equivalent conditions of **Stacks 06MP**, and that the inclusion `𝒵' ⟶ 𝒵` is representable by
algebraic spaces and a monomorphism.

This file proves the uniqueness assertion and the monomorphy assertion. The existence assertion
is not proved here: the source constructs `𝒵'` as the quotient stack `[U/R]` of the
self-intersection groupoid of a surjective flat locally finite type cover `U = Spec(k) ⟶ 𝒵`, using
the representability theorem **Stacks 06FI** and then replacing `[U/R]` by its essential image by
**Stacks 03YQ**; see `StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointSubstackExistence`.

Uniqueness is the source's own argument. Given two such subcategories `P` and `Q`, the first
projection of the 2-fibre product `𝒵_P ×_𝒵 𝒵_Q` is a monomorphism, being a base change of the
inclusion of `Q`; the apex has a point by **Stacks 04XH**, since both `𝒵_P` and `𝒵_Q` have one
and `|𝒵|` is a singleton; so that projection is an equivalence over the big fppf site by
**Stacks 06MQ**. Essential surjectivity of the projection then exhibits every object of `𝒵`
satisfying `P` as isomorphic to one satisfying `Q`, and strict fullness of `Q` finishes; the
roles of `P` and `Q` are symmetric.

## Main definitions

* `AlgebraicGeometry.Stack.IsReducedLocallyNoetherianUniquePointSubstack`: the property of an
  object property of `𝒵` which **Stacks 06MR** asserts holds for exactly one of them.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isMonomorphism_fullSubcategoryInclusion`: the last
  assertion of **Stacks 06MR**, that the inclusion of the substack is representable by algebraic
  spaces and a monomorphism.
* `AlgebraicGeometry.Stack.eq_of_isReducedLocallyNoetherianUniquePointSubstack`: the uniqueness
  assertion of **Stacks 06MR**.

## Implementation notes

A strictly full subcategory is a `CategoryTheory.ObjectProperty` closed under isomorphism, as in
`AlgebraicGeometry.Stack.Substack` (**Stacks 04YM**), and the inclusion is
`AlgebraicGeometry.Stack.fullSubcategoryInclusion`. "Monomorphism" is
`AlgebraicGeometry.Stack.AlgebraicStacks.IsMonomorphism` (**Stacks 04ZW**), whose two conjuncts
are representability by algebraic spaces and the monomorphy clause of Stacks 04XB.

The equivalent conditions of **Stacks 06MP** are read in the shape of its condition (2), the
existence of a surjective flat 1-morphism locally of finite presentation from the spectrum of a
field: that condition is the one **Stacks 06MQ** consumes. Since the conditions of Stacks 06MP are
equivalent,
the class of object properties quantified over is the same one the source quantifies over. The
hypothesis on `𝒵` is condition (1) of **Stacks 06MN**, the source's hypothesis; only its
singleton clause is used, through
`AlgebraicGeometry.Stack.imp_of_isReducedLocallyNoetherianUniquePointSubstack`, which asks only
that the points of the two subcategories have the same image in `|𝒵|`.

The inclusion of a strictly full algebraic subcategory is fully faithful, and the source deduces
that it is representable by algebraic spaces from the implication (2) ⟹ (3) of **Stacks 04Y5**.
The library has that implication as
`AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_faithful`,
fed with the bootstrap theorem Stacks 04S6 part (3),
`AlgebraicGeometry.Space.isBootstrapAlgebraicSpaceAlongFlatSurjection`.
The monomorphy clause itself is unconditional: it is
`AlgebraicGeometry.Stack.AlgebraicStacks.mono_representingMaps_fullSubcategoryInclusion`, the
implication (2) ⟹ (1) of **Stacks 04ZZ** for a substack inclusion.

Base change of the monomorphism is taken along the canonical 2-fibre product square of
**Stacks 04T2**, which is the only square for which
`AlgebraicGeometry.Stack.AlgebraicStacks.isMonomorphism_fst_twoFibreProductSquareAlgebraicStacks`
is available; its apex is the 2-fibre product over the base site of **Stacks 0040**, whose
objects carry the comparison isomorphism in `𝒵` that the last step of the argument uses.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 04ZW](https://stacks.math.columbia.edu/tag/04ZW)
* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
* [Stacks Project, Tag 06MN](https://stacks.math.columbia.edu/tag/06MN)
* [Stacks Project, Tag 06MP](https://stacks.math.columbia.edu/tag/06MP)
* [Stacks Project, Tag 06MQ](https://stacks.math.columbia.edu/tag/06MQ)
* [Stacks Project, Tag 06MR](https://stacks.math.columbia.edu/tag/06MR)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The substack of Stacks 06MR.** A property of the objects of an algebraic stack `𝒵` over `S`
is closed under isomorphism and its full subcategory is an algebraic stack satisfying condition
(2) of **Stacks 06MP**: it admits a surjective flat 1-morphism, locally of finite presentation,
from the algebraic stack of the spectrum of a field.

Stacks 06MR asserts that exactly one object property of `𝒵` has this property when `𝒵` satisfies
the equivalent conditions of Stacks 06MN. -/
abbrev IsReducedLocallyNoetherianUniquePointSubstack
    (𝒵 : AlgebraicStacks.{u, w} B S hS) (P : ObjectProperty 𝒵.val.val.obj) : Prop :=
  P.IsClosedUnderIsomorphisms ∧
    ∃ hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒵 P),
      HasLocallyOfFinitePresentationFlatFieldSpectrumCover B S hS
        (fullSubcategoryAlgebraicStack 𝒵 P hP)

/-- **The last assertion of Stacks 06MR.** The inclusion of a strictly full subcategory of an
algebraic stack `𝒵` over `S` which is itself an algebraic stack is representable by algebraic
spaces and a monomorphism in the sense of **Stacks 04ZW**.

The monomorphy clause is unconditional, by the implication (2) ⟹ (1) of **Stacks 04ZZ** for a
fully faithful 1-morphism. Representability by algebraic spaces is what the source takes from
**Stacks 04Y5**, the inclusion being faithful; the library has the implication (2) ⟹ (3) of
Stacks 04Y5 as
`AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_faithful`,
fed with the bootstrap theorem Stacks 04S6 part (3). -/
@[stacks 06MR "the inclusion morphism of the substack is representable by algebraic spaces and \
a monomorphism, granting the implication (2) ⟹ (3) of Stacks 04Y5 for the inclusion of a \
strictly full algebraic subcategory, which is the hypothesis hrep and which the library leaves \
open"]
theorem AlgebraicStacks.isMonomorphism_fullSubcategoryInclusion
    (𝒵 : AlgebraicStacks.{u, w} B S hS) (P : ObjectProperty 𝒵.val.val.obj)
    (hP : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒵 P)) :
    AlgebraicStacks.IsMonomorphism B S hS (fullSubcategoryInclusion 𝒵 P hP) :=
  ⟨AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_faithful B S hS
      (fullSubcategoryInclusion 𝒵 P hP) inferInstance, fun U y hy F hF he =>
    AlgebraicStacks.mono_representingMaps_fullSubcategoryInclusion B S hS 𝒵 P hP U y hy F hF he⟩

/-- **A 1-morphism carries one one-point substack into another, Stacks 0DTH's argument.** Let
`f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `P` cut out a strictly full
algebraic subcategory of `𝒳` and `Q` one of `𝒴`, both satisfying condition (2) of
**Stacks 06MP**, and let the image under `f` of every point of the first have the same image in
`|𝒴|` as every point of the second. Then `f` carries every object of `𝒳` satisfying `P` to an
object satisfying `Q`.

The first projection `𝒵_P ×_𝒴 𝒵_Q ⟶ 𝒵_P` of the canonical 2-fibre product square of
**Stacks 04T2**, formed over `𝒵_P ⟶ 𝒳 ⟶ 𝒴` and the inclusion of `𝒵_Q`, is a monomorphism, being
a base change of the inclusion of `Q`. Both `𝒵_P` and `𝒵_Q` have a point, by the implication
(2) ⟹ (1) of **Stacks 06MP**, and their images in `|𝒴|` agree by hypothesis, so
**Stacks 04XH** puts a point on the apex. Hence **Stacks 06MQ** makes that projection an
equivalence over the big fppf site. Its quasi-inverse sends an object `X` of `𝒳` satisfying `P`
to a triple consisting of an object of `𝒵_P` isomorphic to `X`, an object of `𝒵_Q`, and an
isomorphism in `𝒴` between the image under `f` of the first and the second; so `f X` is
isomorphic to an object satisfying `Q`.

The source of Stacks 0DTH obtains the point of the apex from Stacks 06MW instead; Stacks 04XH
gives it directly. -/
theorem map_mem_of_isReducedLocallyNoetherianUniquePointSubstack
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    {P : ObjectProperty 𝒳.val.val.obj} {Q : ObjectProperty 𝒴.val.val.obj}
    (hP : IsReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS 𝒳 P)
    (hQ : IsReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS 𝒴 Q)
    (hpts : ∀ (hPalg : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
      (hQalg : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴 Q))
      (zP : AlgebraicStacks.points B S hS (fullSubcategoryAlgebraicStack 𝒳 P hPalg))
      (zQ : AlgebraicStacks.points B S hS (fullSubcategoryAlgebraicStack 𝒴 Q hQalg)),
      AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒳 P hPalg ≫ f) zP =
        AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒴 Q hQalg) zQ)
    (X : 𝒳.val.val.obj) (hX : P X) : Q (f.hom.hom.toFunctor.obj X) := by
  obtain ⟨-, hPalg, hPcov⟩ := hP
  obtain ⟨hQiso, hQalg, hQcov⟩ := hQ
  set sq := twoFibreProductSquareAlgebraicStacks B S hS
    (fullSubcategoryInclusion 𝒳 P hPalg ≫ f) (fullSubcategoryInclusion 𝒴 Q hQalg)
  have hWmono : AlgebraicStacks.IsMonomorphism B S hS sq.fst :=
    AlgebraicStacks.isMonomorphism_fst_twoFibreProductSquareAlgebraicStacks B S hS _ _
      (AlgebraicStacks.isMonomorphism_fullSubcategoryInclusion B S hS 𝒴 Q hQalg)
  obtain ⟨zP⟩ := (isReducedLocallyNoetherianWithUniquePoint_of_locallyOfFinitePresentation
    B S hS (fullSubcategoryAlgebraicStack 𝒳 P hPalg) hPcov).1.2.1
  obtain ⟨zQ⟩ := (isReducedLocallyNoetherianWithUniquePoint_of_locallyOfFinitePresentation
    B S hS (fullSubcategoryAlgebraicStack 𝒴 Q hQalg) hQcov).1.2.1
  obtain ⟨w, -, -⟩ := exists_point_of_isTwoFibreProduct_algebraicStacks B S hS sq
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ _) zP zQ
    (hpts hPalg hQalg zP zQ)
  rcases isEmpty_points_or_isEquivalenceOver_of_isMonomorphism B S hS sq.pt
    (fullSubcategoryAlgebraicStack 𝒳 P hPalg) sq.fst hWmono hPcov with hempty | hne
  · exact (hempty.false w).elim
  · have e := hne.some
    exact Q.prop_of_iso
      ((e.inv.obj ⟨X, hX⟩).iso.symm.trans
        (f.hom.hom.toFunctor.mapIso (P.ι.mapIso (e.counitIso.app ⟨X, hX⟩))))
      (e.inv.obj ⟨X, hX⟩).y.property

/-- **The uniqueness argument of Stacks 06MR, in the asymmetric form.** Let `P` and `Q` both cut
out a strictly full algebraic subcategory of `𝒵` satisfying condition (2) of **Stacks 06MP**, and
let every point of the first have the same image in `|𝒵|` as every point of the second. Then
every object of `𝒵` satisfying `P` satisfies `Q`.

The hypothesis on the images holds when `|𝒵|` is a subsingleton, which is the case of
Stacks 06MR, and when both subcategories have all their points over one point of `|𝒵|`, which is
the uniqueness argument of **Stacks 06MT**.

This is `AlgebraicGeometry.Stack.map_mem_of_isReducedLocallyNoetherianUniquePointSubstack` at the
identity 1-morphism of `𝒵`. -/
theorem imp_of_isReducedLocallyNoetherianUniquePointSubstack
    (𝒵 : AlgebraicStacks.{u, w} B S hS)
    {P Q : ObjectProperty 𝒵.val.val.obj}
    (hP : IsReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS 𝒵 P)
    (hQ : IsReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS 𝒵 Q)
    (hpts : ∀ (hPalg : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒵 P))
      (hQalg : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒵 Q))
      (zP : AlgebraicStacks.points B S hS (fullSubcategoryAlgebraicStack 𝒵 P hPalg))
      (zQ : AlgebraicStacks.points B S hS (fullSubcategoryAlgebraicStack 𝒵 Q hQalg)),
      AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒵 P hPalg) zP =
        AlgebraicStacks.pointsMap B S hS (fullSubcategoryInclusion 𝒵 Q hQalg) zQ)
    (X : 𝒵.val.val.obj) (hX : P X) : Q X :=
  map_mem_of_isReducedLocallyNoetherianUniquePointSubstack B S hS (𝟙 𝒵) hP hQ
    (fun hPalg hQalg zP zQ => by
      rw [AlgebraicStacks.pointsMap_comp, AlgebraicStacks.pointsMap_id]
      exact hpts hPalg hQalg zP zQ) X hX

/-- **Stacks 06MR, the uniqueness assertion.** Let `𝒵` be an algebraic stack over `S` which is
reduced with a singleton space of points, that is, which satisfies condition (1) of
**Stacks 06MN**. Then at most one strictly full subcategory of `𝒵` is an algebraic stack
satisfying condition (2) of **Stacks 06MP**.

Existence is not proved; see the module docstring. -/
@[stacks 06MR "the uniqueness of the substack, with the equivalent conditions of Stacks 06MP \
read as its condition (2), and granting the implication (2) ⟹ (3) of Stacks 04Y5 for the \
inclusion of a strictly full algebraic subcategory, which is the hypothesis hrep and which the \
library leaves open"]
theorem eq_of_isReducedLocallyNoetherianUniquePointSubstack
    (𝒵 : AlgebraicStacks.{u, w} B S hS) (h𝒵 : IsReducedWithUniquePoint B S hS 𝒵)
    {P Q : ObjectProperty 𝒵.val.val.obj}
    (hP : IsReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS 𝒵 P)
    (hQ : IsReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS 𝒵 Q) : P = Q :=
  funext fun X => propext
    ⟨imp_of_isReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS 𝒵 hP hQ
        (fun _ _ _ _ => h𝒵.2.2.elim _ _) X,
      imp_of_isReducedLocallyNoetherianUniquePointSubstack.{u, w} B S hS 𝒵 hQ hP
        (fun _ _ _ _ => h𝒵.2.2.elim _ _) X⟩

end AlgebraicGeometry.Stack

end
