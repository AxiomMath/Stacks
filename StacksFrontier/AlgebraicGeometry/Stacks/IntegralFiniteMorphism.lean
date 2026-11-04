module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffine

/-!
# Integral and finite 1-morphisms of algebraic stacks (Stacks 0CHU, 0CHV, 0CHW)

Following Stacks 0CHU, a 1-morphism of algebraic stacks over `S` *is integral*, respectively
*is finite*, when it is representable and integral, respectively finite, in the sense of
Properties of Stacks, Section 04XB: every algebraic space representing its base change along a
scheme-valued point of the target has integral, respectively finite, structural morphism, read
as a morphism of algebraic spaces over `S`.

Both properties are stable under base change (Stacks 0CHV) and under composition
(Stacks 0CHW).

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.IsIntegralHom`: **Stacks 0CHU**, part (1).
* `AlgebraicGeometry.Stack.AlgebraicStacks.IsFinite` of
  `StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffine` is **Stacks 0CHU**, part (2); the tag is
  recorded on it here.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isIntegralHom_baseChange` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isFinite_baseChange`: **Stacks 0CHV**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isIntegralHom_comp` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isFinite_comp`: **Stacks 0CHW**.

## Implementation notes

The Stacks definition reads "representable, and integral in the sense of Section 04XB"; the
source replaces "representable" by "representable by algebraic spaces" throughout Chapter 101,
saying the two notions agree and that it will use the second without further mention, and that
is the form taken here, as it is for the affine 1-morphisms of Stacks 0CHQ
(`AlgebraicGeometry.Stack.AlgebraicStacks.IsAffineHom`) and the immersions of Stacks 04YL.

Part (2) of Stacks 0CHU is already in the library, as
`AlgebraicGeometry.Stack.AlgebraicStacks.IsFinite`, introduced for the finite 1-morphism in the
definition of a well-nigh affine algebraic stack (Stacks 0DUL); it is exactly the notion of
Stacks 0CHU, part (2), so the tag is added to it rather than a second copy being written, and
part (1) is defined here in the same shape — the Stacks 03YK quantifier written out, with the
representability datum carried as an existential so that a single witness contains everything a
consumer needs.

The quantifier is written out rather than spelled `AlgebraicGeometry.Stack.HasRelativeProperty`
because that is the shape part (2) already has; the two forms are the same proposition, as
`AlgebraicGeometry.Stack.AlgebraicStacks.isIntegralHom_iff_exists_hasRelativeProperty` and its
finite companion certify by `rfl`. That identity is what makes Stacks 0CHV and Stacks 0CHW
immediate from the general relative-property results: **Stacks 045C**
(`AlgebraicGeometry.Stack.hasRelativeProperty_baseChange`) gives the base change and
**Stacks 045B** (`AlgebraicGeometry.Stack.hasRelativeProperty_comp`) the composition, each at
the packaged property `AlgebraicGeometry.Space.integralMorphismProperty`, respectively
`AlgebraicGeometry.Space.finiteMorphismProperty`. Both of those theorems carry the three
permanence hypotheses a relative property is introduced under — stability under base change,
locality at the target for the fppf precoverage, and stability under composition — and for
integrality and finiteness of morphisms of algebraic spaces **all three are discharged by results of
the library**, collected as instances in
`StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteMorphismProperty`; so neither statement
below carries a hypothesis on the property, unlike the immersion siblings of Stacks 0502, whose
locality is a Chapter 67 result this library does not have. The representability halves are
**Stacks 0302** (`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_baseChange`) and
**Stacks 0301** (`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_comp`).

Base change is stated at an arbitrary 2-commutative square of algebraic stacks *recognised* as a
2-fibre product, as everywhere in this directory, so no comparison 1-morphism has to be built
and the statement applies to any construction of `𝒵 ×_𝒴 𝒳`; the square is carried down to the
ambient 2-category of categories fibred in groupoids, where Stacks 045C lives, by
`AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_toCatFiberedInGroupoids`. With the
cospan written `f : 𝒳 ⟶ 𝒴`, `g : 𝒵 ⟶ 𝒴` and the square taken over `(f, g)`, its first
projection is `𝒵 ×_𝒴 𝒳 ⟶ 𝒳`, which is the 1-morphism the source's conclusion is about.

## References

* [Stacks Project, Tag 0301](https://stacks.math.columbia.edu/tag/0301)
* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 0CHU](https://stacks.math.columbia.edu/tag/0CHU)
* [Stacks Project, Tag 0CHV](https://stacks.math.columbia.edu/tag/0CHV)
* [Stacks Project, Tag 0CHW](https://stacks.math.columbia.edu/tag/0CHW)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Definition

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 0CHU**, part (1). A 1-morphism of algebraic stacks over `S` *is integral* when it is
representable by algebraic spaces and is integral in the sense of Stacks 04XB: every algebraic
space representing its base change along a scheme-valued point of the target has integral
structural morphism, read as a morphism of algebraic spaces over `S`. -/
@[stacks 0CHU "part (1): integral morphisms"]
abbrev IsIntegralHom (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∃ _hf : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom,
    ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.val.obj)
      (_hy : y ⋙ 𝒴.val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y
          (CatFiberedInGroupoids.homFunctor f.hom))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsIntegralHom B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

add_to_stacks 0CHU "part (2): finite morphisms"
  AlgebraicGeometry.Stack.AlgebraicStacks.IsFinite

/-- Part (1) of Stacks 0CHU is the relative property of Stacks 03YK at
`AlgebraicGeometry.Space.integralMorphismProperty`, conjoined with representability by algebraic
spaces. -/
theorem isIntegralHom_iff_exists_hasRelativeProperty (f : 𝒳 ⟶ 𝒴) :
    IsIntegralHom B S hS f ↔
      ∃ hf : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom,
        Stack.HasRelativeProperty B S hS (Space.integralMorphismProperty B S hS) f.hom hf :=
  Iff.rfl

/-- Part (2) of Stacks 0CHU is the relative property of Stacks 03YK at
`AlgebraicGeometry.Space.finiteMorphismProperty`, conjoined with representability by algebraic
spaces. -/
theorem isFinite_iff_exists_hasRelativeProperty (f : 𝒳 ⟶ 𝒴) :
    IsFinite B S hS f ↔
      ∃ hf : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom,
        Stack.HasRelativeProperty B S hS (Space.finiteMorphismProperty B S hS) f.hom hf :=
  Iff.rfl

end Definition

section BaseChange

variable {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 0CHV**, the integral case. A base change of an integral 1-morphism of algebraic
stacks over `S` is integral: if `g : 𝒵 ⟶ 𝒴` is integral and `P` is a 2-fibre product of the
cospan `(f, g)` for a 1-morphism `f : 𝒳 ⟶ 𝒴`, then `P.fst : 𝒵 ×_𝒴 𝒳 ⟶ 𝒳` is integral.

Representability by algebraic spaces base changes by **Stacks 0302** and the relative property
of Stacks 04XB by **Stacks 045C**, which applies because integrality of morphisms of algebraic
spaces is stable under base change and local at the target for the fppf precoverage. -/
@[stacks 0CHV "integral"]
theorem isIntegralHom_baseChange (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (P : Bicategory.TwoCommSq f g) (hP : Bicategory.IsTwoFibreProduct P)
    (hg : IsIntegralHom B S hS g) :
    IsIntegralHom B S hS P.fst := by
  obtain ⟨hgr, hPg⟩ := hg
  have hD : Bicategory.IsTwoFibreProduct (toCatFiberedInGroupoids B S hS P) :=
    isTwoFibreProduct_toCatFiberedInGroupoids B S hS P hP
  exact ⟨Stack.isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS
      𝒵.val 𝒴.val 𝒳.val g.hom f.hom (toCatFiberedInGroupoids B S hS P) hD hgr,
    Stack.hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
      (Space.integralMorphismProperty B S hS) 𝒵.val 𝒴.val 𝒳.val g.hom f.hom
      (toCatFiberedInGroupoids B S hS P) hD hgr hPg⟩

/-- **Stacks 0CHV**, the finite case. A base change of a finite 1-morphism of algebraic stacks
over `S` is finite: if `g : 𝒵 ⟶ 𝒴` is finite and `P` is a 2-fibre product of the cospan
`(f, g)` for a 1-morphism `f : 𝒳 ⟶ 𝒴`, then `P.fst : 𝒵 ×_𝒴 𝒳 ⟶ 𝒳` is finite.

Representability by algebraic spaces base changes by **Stacks 0302** and the relative property
of Stacks 04XB by **Stacks 045C**, which applies because finiteness of morphisms of algebraic
spaces is stable under base change and local at the target for the fppf precoverage. -/
@[stacks 0CHV "finite"]
theorem isFinite_baseChange (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (P : Bicategory.TwoCommSq f g) (hP : Bicategory.IsTwoFibreProduct P)
    (hg : IsFinite B S hS g) :
    IsFinite B S hS P.fst := by
  obtain ⟨hgr, hPg⟩ := hg
  have hD : Bicategory.IsTwoFibreProduct (toCatFiberedInGroupoids B S hS P) :=
    isTwoFibreProduct_toCatFiberedInGroupoids B S hS P hP
  exact ⟨Stack.isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS
      𝒵.val 𝒴.val 𝒳.val g.hom f.hom (toCatFiberedInGroupoids B S hS P) hD hgr,
    Stack.hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
      (Space.finiteMorphismProperty B S hS) 𝒵.val 𝒴.val 𝒳.val g.hom f.hom
      (toCatFiberedInGroupoids B S hS P) hD hgr hPg⟩

end BaseChange

section Composition

variable {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 0CHW**, the integral case: a composite of integral 1-morphisms of algebraic stacks
over `S` is integral.

Representability by algebraic spaces composes by **Stacks 0301** and the relative property of
Stacks 04XB by **Stacks 045B**, which applies because
integrality of morphisms of algebraic spaces is stable under base change and under composition
(**Stacks 03ZR**) and local at the target for the fppf precoverage. -/
@[stacks 0CHW "integral"]
theorem isIntegralHom_comp (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsIntegralHom B S hS f) (hg : IsIntegralHom B S hS g) :
    IsIntegralHom B S hS (f ≫ g) := by
  obtain ⟨hfr, hPf⟩ := hf
  obtain ⟨hgr, hPg⟩ := hg
  have hrep := isRepresentableByAlgebraicSpaces_comp B S hS f.hom g.hom hfr hgr
  exact ⟨hrep, Stack.hasRelativeProperty_comp.{u, u, u + 1, u} B S hS
    (Space.integralMorphismProperty B S hS) f.hom g.hom hfr hgr hPf hPg⟩

/-- **Stacks 0CHW**, the finite case: a composite of finite 1-morphisms of algebraic stacks over
`S` is finite.

Representability by algebraic spaces composes by **Stacks 0301** and the relative property of
Stacks 04XB by **Stacks 045B**, which applies because finiteness of morphisms of algebraic
spaces is stable under base change and under composition (**Stacks 03ZR**) and local at the
target for the fppf precoverage. -/
@[stacks 0CHW "finite"]
theorem isFinite_comp (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsFinite B S hS f) (hg : IsFinite B S hS g) :
    IsFinite B S hS (f ≫ g) := by
  obtain ⟨hfr, hPf⟩ := hf
  obtain ⟨hgr, hPg⟩ := hg
  have hrep := isRepresentableByAlgebraicSpaces_comp B S hS f.hom g.hom hfr hgr
  exact ⟨hrep, Stack.hasRelativeProperty_comp.{u, u, u + 1, u} B S hS
    (Space.finiteMorphismProperty B S hS) f.hom g.hom hfr hgr hPf hPg⟩

end Composition

end AlgebraicGeometry.Stack.AlgebraicStacks

end
