module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMapToRepresentingSpace

/-!
# Recovering the data of Stacks 06CK from a morphism to the representing algebraic space

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of a
scheme `S`, let `y` be a scheme-valued point of `𝒴` over an object `U` of the site, and let
`X_y` be an algebraic space over `U` representing the 2-fibre product
`(Sch/U)_{fppf} ×_{y, 𝒴, F} 𝒳`. Stacks 06CK attaches to a scheme `Z` over `U`, an object `x` of
`𝒳` over `Z` and a vertical isomorphism `α : y|_Z ⟶ F(x)` a morphism `x_α : Z ⟶ X_y` of
algebraic spaces over `U`; this is `AlgebraicGeometry.Stack.relativeMap`.

This file is the **inverse** of that construction: every morphism `Z ⟶ X_y` of algebraic spaces
over `U` is `x_α` for some pair `(x, α)`, and the pair is unique up to a vertical isomorphism of
`𝒳` compatible with the two comparison isomorphisms. So Stacks 06CK is a bijection between the
isomorphism classes of pairs `(x, α)` over `Z` and the sections of `X_y` over `Z`.

Both halves come from the corresponding properties of naming a section of a representing presheaf
by an object: `CategoryTheory.PresheafOfCategories.exists_sectionOfObj` for surjectivity and
`CategoryTheory.PresheafOfCategories.fiberIsoOfSectionOfObj_eq` for injectivity. What this file
adds is the translation between an object of the 2-fibre product lying over `Z` and the pair
`(x, α)`, which is the content of the right-hand diagram of Stacks 06CK read backwards.

## Main results

* `AlgebraicGeometry.Stack.exists_relativeSection_eq`: every section of `X_y` over `Z` is named
  by a pair `(x, α)`.
* `AlgebraicGeometry.Stack.exists_relativeMap_eq`: **the inverse of Stacks 06CK**, every morphism
  `Z ⟶ X_y` of algebraic spaces over `U` is the relative map of a pair `(x, α)`.
* `AlgebraicGeometry.Stack.exists_hom_of_relativeSection_eq`: two pairs over `Z` naming the same
  section are related by a vertical morphism of `𝒳` compatible with the two comparison
  isomorphisms, the converse of
  `AlgebraicGeometry.Stack.relativeSection_eq_of_vertical`.

## Implementation notes

An object of the 2-fibre product lying over `Z` for the first projection is a quadruple
`(W, Z', x, α)` with `Z'` the first component and `Z' = Z`; its base `W` is then
`(Over.map U.hom).obj Z` because the first component lies over the base. Substituting both
equalities turns the quadruple into exactly the data `AlgebraicGeometry.Stack.relativeObj`
assembles, and the two objects are then literally equal — there is no transport to perform, which
is why the proofs below are a destructuring followed by the statement about sections.

The uniqueness statement is stated as the existence of a morphism rather than of an isomorphism.
In a category fibred in groupoids a morphism lying over an identity is an isomorphism, so nothing
is lost; stating it this way avoids assuming fibredness of `𝒳`, which none of the constructions
of Stacks 06CK use.

## References

* [Stacks Project, Tag 02XV](https://stacks.math.columbia.edu/tag/02XV)
* [Stacks Project, Tag 06CK](https://stacks.math.columbia.edu/tag/06CK)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u v₁ v₂ w₁ w₂

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : BasedCategory.{v₁, w₁} (BigFppfOver B S hS)}
  {𝒴 : BasedCategory.{v₂, w₂} (BigFppfOver B S hS)}
  {F : 𝒳 ⥤ᵇ 𝒴} {U : BigFppfOver B S hS}
  {y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.obj}
  {Xy : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u}
  {e : StacksRepresentableCFG.EquivalenceOver
    (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.p 𝒴.p y F.toFunctor)
    (presheafOfCategories (Xy ⋙ typeToCat)).p}

/-! ### Surjectivity -/

/-- **Every section of `X_y` over `Z` is named by a pair `(x, α)`.** Given a scheme `Z` over `U`
and a section of the representing algebraic space over it, there are an object `x` of `𝒳` over
`Z` and a vertical isomorphism `α : y|_Z ⟶ F(x)` whose object of the 2-fibre product names that
section.

The section is named by *some* object of the 2-fibre product lying over `Z`
(`CategoryTheory.PresheafOfCategories.exists_sectionOfObj`), and such an object is precisely a
pair `(x, α)`. -/
theorem exists_relativeSection_eq (Z : BigFppfOver B U.left.1 U.left.2) (s : Xy.obj (op Z)) :
    ∃ (x : 𝒳.obj) (hx : 𝒳.p.obj x = (Over.map U.hom).obj Z)
      (α : y.obj Z ≅ F.toFunctor.obj x)
      (hα : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z)) α.hom),
      relativeSection F y e Z x hx α hα = s := by
  obtain ⟨z, hz, hzs⟩ := PresheafOfCategories.exists_sectionOfObj e (W := Z) s
  obtain ⟨base, zx, zy, hbase, hzy, iso, vert⟩ := z
  change zx = Z at hz
  subst hz
  change (Over.map U.hom).obj zx = base at hbase
  subst hbase
  exact ⟨zy, hzy, iso, vert, hzs⟩

/-- **The inverse of Stacks 06CK.** Every morphism `Z ⟶ X_y` of algebraic spaces over `U` is the
relative map `x_α` of an object `x` of `𝒳` over `Z` together with a vertical isomorphism
`α : y|_Z ⟶ F(x)`.

Under the Yoneda lemma the morphism is a section of `X_y` over `Z`, and
`AlgebraicGeometry.Stack.exists_relativeSection_eq` names that section by a pair.

No tag attribute is placed here: Stacks 06CK is the numbered display of the two diagrams, whose
objects are `AlgebraicGeometry.Stack.relativeObj` and `AlgebraicGeometry.Stack.relativeMap` and
already carry it; that the second diagram's assignment is surjective is not part of the
display. -/
theorem exists_relativeMap_eq (hXy : IsAlgebraicSpace B U.left.1 U.left.2 Xy)
    (Z : BigFppfOver B U.left.1 U.left.2)
    (g : (⟨yoneda.obj Z, isAlgebraicSpace_yoneda B U.left.1 U.left.2 Z⟩ :
        AlgebraicSpaces B U.left.1 U.left.2) ⟶ ⟨Xy, hXy⟩) :
    ∃ (x : 𝒳.obj) (hx : 𝒳.p.obj x = (Over.map U.hom).obj Z)
      (α : y.obj Z ≅ F.toFunctor.obj x)
      (hα : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z)) α.hom),
      relativeMap F y e hXy Z x hx α hα = g := by
  obtain ⟨x, hx, α, hα, hs⟩ := exists_relativeSection_eq (e := e) Z (yonedaEquiv g.hom)
  refine ⟨x, hx, α, hα, ?_⟩
  have h : (relativeMap F y e hXy Z x hx α hα).hom = g.hom := by
    rw [← yonedaEquiv.injective.eq_iff, yonedaEquiv_relativeMap_hom, hs]
  exact ObjectProperty.hom_ext _ h

/-! ### Uniqueness -/

/-- **Two pairs over `Z` naming the same section are related by a vertical morphism of `𝒳`.**
This is the converse of `AlgebraicGeometry.Stack.relativeSection_eq_of_vertical`: the morphism
`a : x ⟶ x'` lies over the identity of `Z` and identifies the two comparison isomorphisms.

The two objects of the 2-fibre product lie in one fibre and name the same section, so they are
isomorphic in that fibre (`CategoryTheory.PresheafOfCategories.fiberIsoOfSectionOfObj_eq`); the
first component of the isomorphism is the identity of `Z` and the second is `a`. -/
theorem exists_hom_of_relativeSection_eq {Z : BigFppfOver B U.left.1 U.left.2} {x x' : 𝒳.obj}
    {hx : 𝒳.p.obj x = (Over.map U.hom).obj Z} {hx' : 𝒳.p.obj x' = (Over.map U.hom).obj Z}
    {α : y.obj Z ≅ F.toFunctor.obj x} {α' : y.obj Z ≅ F.toFunctor.obj x'}
    {hα : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z)) α.hom}
    {hα' : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z)) α'.hom}
    (hs : relativeSection F y e Z x hx α hα = relativeSection F y e Z x' hx' α' hα') :
    ∃ a : x ⟶ x', 𝒳.p.IsHomLift (𝟙 ((Over.map U.hom).obj Z)) a ∧
      α'.hom = α.hom ≫ F.toFunctor.map a := by
  have i := PresheafOfCategories.fiberIsoOfSectionOfObj_eq e
    (z := relativeObj F y Z x hx α hα) (z' := relativeObj F y Z x' hx' α' hα') rfl rfl hs
  obtain ⟨φ, hφ⟩ :
      ∃ φ : relativeObj F y Z x hx α hα ⟶ relativeObj F y Z x' hx' α' hα',
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.p 𝒴.p y F.toFunctor).IsHomLift (𝟙 Z) φ :=
    ⟨Functor.Fiber.fiberInclusion.map i.hom, i.hom.2⟩
  have := hφ
  have hφa : φ.a = 𝟙 Z := by
    have h : φ.a = eqToHom (rfl : Z = Z) ≫ 𝟙 Z ≫ eqToHom (rfl : Z = Z) :=
      CategoryTheory.IsHomLift.fac'
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.p 𝒴.p y F.toFunctor) (𝟙 Z) φ
    simpa using h
  have hbase : φ.hbase = 𝟙 ((Over.map U.hom).obj Z) := by
    have h : φ.hbase = eqToHom (rfl : (Over.map U.hom).obj Z = (Over.map U.hom).obj Z) ≫
        (Over.map U.hom).map φ.a ≫
        eqToHom (rfl : (Over.map U.hom).obj Z = (Over.map U.hom).obj Z) :=
      TwoFibreProductOver.Hom.hbase_eq φ
    rw [hφa] at h
    simpa using h
  refine ⟨φ.b, ?_, ?_⟩
  · have h := φ.hb
    rwa [hbase] at h
  · have hφaZ : (φ.a : Z ⟶ Z) = 𝟙 Z := hφa
    have h : y.map (X := Z) (Y := Z) φ.a ≫ α'.hom = α.hom ≫ F.toFunctor.map φ.b := φ.w
    have hid : y.map (X := Z) (Y := Z) φ.a = 𝟙 (y.obj Z) := by rw [hφaZ]; simp
    rw [hid, CategoryTheory.Category.id_comp] at h
    exact h

end AlgebraicGeometry.Stack

end
