module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.MorphismFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatDescentAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionSingleCover
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.PostcomposeSnd
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# The Stacks 06NR step for a base change that factors (the presheaf dictionary)

**Stacks 06NR** is proved, unconditionally, as a statement about *presheaves on the big fppf site
carrying `AlgebraicGeometry.IsAlgebraicSpace`*: flatness, local finite type and local finite
presentation descend from a composite `f ≫ g` of morphisms of algebraic spaces to the second
factor `g` as soon as `f` is surjective as a morphism of fppf sheaves
(`AlgebraicGeometry.Space.isFlat_of_comp_of_locallySurjective` and its two siblings). The use the
chapter on gerbes makes of it is at a *triangle of 2-fibre products of algebraic stacks*, so the
step needs a translation between the two languages. This file is that translation.

The situation is the one the route to the unproved half of **Stacks 06QG** part (3) arrives at.
Let `x : 𝒰 ⟶ 𝒳` and `q : 𝒱 ⟶ 𝒳` be 1-morphisms of algebraic stacks over `S` and suppose `q`
factors through `x`: there are `γ : 𝒱 ⟶ 𝒰` and a 2-isomorphism `γ ≫ x ≅ q`. Let `Q₁` exhibit
`𝒱 ×_𝒳 𝒰` and let `Q₂` be any 2-commutative square over the cospan `(q, q)` — in the application
the 2-fibre product `𝒱 ×_𝒳 𝒱`. The factorisation reads `Q₂` as a square over the cospan `(q, x)`
(`CategoryTheory.Bicategory.TwoCommSq.postcomposeSnd`), so the universal property of `Q₁` supplies
a 1-morphism

`k : Q₂.pt ⟶ Q₁.pt` with `Q₂.fst ≅ k ≫ Q₁.fst`,

and Stacks 06NR applies to that triangle once all three of `Q₂.pt`, `Q₁.pt` and `𝒱` are
representable by algebraic spaces. The step itself is stated for an arbitrary 2-commutative
triangle `p ≅ k ≫ r` of 1-morphisms of algebraic stacks, which is all it uses; the 2-fibre
products enter only in the route assembled at the end of the file.

## The dictionary

The passage from a 1-morphism of algebraic stacks to a morphism of presheaves is **Stacks 06FM
read at a represented source and target**,
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_iff_represented`: for a 1-morphism between
algebraic stacks representable by algebraic spaces `F` and `G`, the existential smooth-diagram
criterion at a property smooth local on the source-and-target holds exactly when the induced
morphism `F ⟶ G` of representing presheaves (**Stacks 04SW**,
`AlgebraicGeometry.Stack.representingMap`) has that property. Since flatness of a 1-morphism
(**Stacks 06PW**) *is* that criterion at flatness of morphisms of algebraic spaces, and local
finite presentation (**Stacks 06Q2** part (1)) is its universal form, which agrees with it by
`AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_iff_some`, both notions translate.

Note that this is *not* **Stacks 04XC**
(`AlgebraicGeometry.Stack.hasRelativeProperty_iff_forall_space_baseChange`), which translates the
relative property of **Stacks 03YK** carried by a 1-morphism *representable by algebraic spaces*.
That notion is a different proposition from Stacks 06PW, and the descent results this step feeds —
**Stacks 06PZ** and **Stacks 06Q8** — are stated at Stacks 06PW and Stacks 06Q2, so Stacks 06FM at
a represented source and target is the translation that fits on both sides.

Functoriality of `AlgebraicGeometry.Stack.representingMap` turns the 2-isomorphism
`Q₂.fst ≅ k ≫ Q₁.fst` into an equality of morphisms of presheaves, by
`AlgebraicGeometry.Stack.representingMap_comp` and
`AlgebraicGeometry.Stack.representingMap_congr_twoIso`; that equality is the whole arithmetic of
the file.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.baseChangeFactorisationMap`: the 1-morphism `k` above.
* `AlgebraicGeometry.Stack.AlgebraicStacks.baseChangeFactorisationMapFstIso`: the 2-isomorphism
  `Q₂.fst ≅ k ≫ Q₁.fst`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.factorisationMediatingMap`: the same 1-morphism for the
  two *canonical* squares, chosen by a formula rather than by the universal property, so that its
  action on objects of the fibres can be computed.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.representingMap_eq_comp_of_twoIso`: a 2-commutative
  triangle of 1-morphisms between algebraic stacks representable by algebraic spaces is a
  commuting triangle of morphisms of representing presheaves.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_comp_of_locallySurjective_representingMap`
  and `…isLocallyOfFinitePresentation_of_comp_of_locallySurjective_representingMap`: **the
  Stacks 06NR step**. For a 2-commutative triangle `p ≅ k ≫ r` of 1-morphisms of algebraic stacks
  whose three objects are representable by algebraic spaces, if `p` is flat (resp. locally of
  finite presentation) and `k` induces a surjection of fppf sheaves, then so is `r`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_fiber_iso_factorisationMediatingMap` and
  `Stack.AlgebraicStacks.isLocallySurjective_representingMap_factorisationMediatingMap`:
  **the surjectivity hypothesis, discharged** when `x` is a section of a 1-morphism `π : 𝒳 ⟶ 𝒰`.
  Every object of a fibre of `𝒱 ×_𝒳 𝒰` is isomorphic — over the same object of the site, with no
  covering — to the image of an object of the fibre of `𝒱 ×_𝒳 𝒱`, so the mediating 1-morphism
  induces a surjection of fppf sheaves.
* `Stack.AlgebraicStacks.isFlat_and_isLocallyOfFinitePresentation_of_factorisation`:
  the step composed with **Stacks 06PY**, **Stacks 06Q4**, **Stacks 06PZ** and **Stacks 06Q8**: a
  surjective, flat, locally finitely presented `q` which factors through a *section* `x` makes `x`
  itself flat and locally of finite presentation.

## Implementation notes

The surjectivity hypothesis of the Stacks 06NR step is Mathlib's
`CategoryTheory.Presheaf.IsLocallySurjective` for the topology of the big fppf site of `S`,
exactly as in the library's Stacks 06NR. For the triangle the route produces it is *proved* here,
along the following path.
`AlgebraicGeometry.Stack.isLocallySurjective_representingMap_of_isoClassMap` reduces it to local
surjectivity of the morphism of presheaves of isomorphism classes of **Stacks 04SC**, which is a
condition on *objects of fibres*. An object of the fibre of
`𝒱 ×_𝒳 𝒰` over `T` is a triple `(v, u, φ : q v ≅ x u)` (**Stacks 0040**); the factorisation makes
`x (γ v) ≅ x u`, and since `x` is a section it separates the objects of a fibre
(`AlgebraicGeometry.Stack.nonempty_iso_fiber_of_iso_section_image`), so `γ v ≅ u` vertically. The
triple `(v, v, φ ≫ x β⁻¹ ≫ δ_v)` of `𝒱 ×_𝒳 𝒱` then has image isomorphic to the given object.

Two things about that argument are worth recording. It needs no covering: the comparison
isomorphism of an object of `𝒱 ×_𝒳 𝒱` is free data, so it can be chosen to make the image match
on the nose, and the surjection is a surjection of *presheaves*, for every topology on the site.
And for the same reason it needs no discreteness of the fibres of `𝒰`: a vertical isomorphism
`γ v ≅ u` suffices and `AlgebraicGeometry.Stack.fiberArrow_eq_of_iso` is not used, so `𝒰` may be
any algebraic stack rather than a represented one.

`CategoryTheory.Bicategory.TwoCommSq.postcomposeSnd` changes neither the apex nor the first leg of
a square, so `(Q₂.postcomposeSnd γ hγ).pt` and `(Q₂.postcomposeSnd γ hγ).fst` are `Q₂.pt` and
`Q₂.fst` definitionally and the mediating pre-morphism of Stacks 003O can be read as data on `Q₂`
itself with no transport.

The universal property of a 2-fibre product supplies the mediating 1-morphism only as a *class*
in the category of 2-commutative squares of Stacks 003O, so
`AlgebraicGeometry.Stack.AlgebraicStacks.baseChangeFactorisationMap` has to choose a
representative with `CategoryTheory.Bicategory.twoFibreProductPreHom`, and the action of that
choice on objects of fibres is not computable from the data. **That is why the Stacks 06NR step
below takes an arbitrary `k` together with a 2-isomorphism `p ≅ k ≫ r`, rather than the chosen
one.** Anything that has to compute with `k` — in particular a proof of the surjectivity
hypothesis — can construct its own mediating 1-morphism explicitly and supply it here; and since
any two pre-morphisms into a 2-fibre product are 2-cell equivalent
(`CategoryTheory.Bicategory.twoFibreProductPreHom_rel`), the surjectivity hypothesis does not
depend on which one is used, by `AlgebraicGeometry.Stack.representingMap_congr_twoIso`.

Every statement takes the representing presheaves and the representing equivalences as data and
quantifies over nothing, so none of them depends on those choices. `Bicategory.IsTwoFibreProduct`
is `CategoryTheory.Limits.IsTerminal`, hence *data* rather than a proposition, so inside a proof a
witness for it must be named by `let` and not by `have`: the mediating 1-morphism
`baseChangeFactorisationMap` is computed from it, and a `have` makes the two sides of a hypothesis
about that 1-morphism two different terms.

Stacks 06Q8 asks for its hypothesis on the *second* projection of the canonical square of the
cospan `(x, q)`, while the step above concludes about the *first* projection of a square over the
cospan `(q, x)`; those are two apexes of one cospan, so the passage between them is
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_fst_of_isTwoFibreProduct` applied to the
leg exchange of Stacks 003Q, exactly as inside the proof of Stacks 06Q8 itself.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06NR](https://stacks.math.columbia.edu/tag/06NR)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 06PY](https://stacks.math.columbia.edu/tag/06PY)
* [Stacks Project, Tag 06PZ](https://stacks.math.columbia.edu/tag/06PZ)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 06Q4](https://stacks.math.columbia.edu/tag/06Q4)
* [Stacks Project, Tag 06Q8](https://stacks.math.columbia.edu/tag/06Q8)
* [Stacks Project, Tag 06QG](https://stacks.math.columbia.edu/tag/06QG)
-/


@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The Stacks 06NR step for a triangle of algebraic stacks -/

section Triangle

variable {𝒲 𝒴 𝒱 : Stack.AlgebraicStacks.{u, w} B S hS}
  (p : 𝒲 ⟶ 𝒱) (r : 𝒴 ⟶ 𝒱) (k : 𝒲 ⟶ 𝒴) (hk : p ≅ k ≫ r)
  (A Y G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eA : StacksRepresentableCFG.EquivalenceOver
    𝒲.val.val.p (presheafOfCategories (A ⋙ typeToCat)).p)
  (eY : StacksRepresentableCFG.EquivalenceOver
    𝒴.val.val.p (presheafOfCategories (Y ⋙ typeToCat)).p)
  (eG : StacksRepresentableCFG.EquivalenceOver
    𝒱.val.val.p (presheafOfCategories (G ⋙ typeToCat)).p)

include hk in
/-- **A 2-commutative triangle of 1-morphisms between algebraic stacks representable by algebraic
spaces is a commuting triangle of morphisms of representing presheaves.** If `p ≅ k ≫ r` then the
morphism of representing presheaves induced by `p` is the composite of those induced by `k` and
by `r`.

This is functoriality of the identification of **Stacks 04SW**: the composite is split by
`AlgebraicGeometry.Stack.representingMap_comp` and the 2-isomorphism is forgotten by
`AlgebraicGeometry.Stack.representingMap_congr_twoIso`. -/
theorem representingMap_eq_comp_of_twoIso :
    representingMap B S hS 𝒲.val 𝒱.val A G eA eG p.hom =
      representingMap B S hS 𝒲.val 𝒴.val A Y eA eY k.hom ≫
        representingMap B S hS 𝒴.val 𝒱.val Y G eY eG r.hom := by
  rw [← representingMap_comp B S hS A Y G eA eY eG k.hom r.hom]
  exact representingMap_congr_twoIso B S hS A G eA eG (Bicategory.InducedBicategory.isoHom hk)

variable (hA : IsAlgebraicSpace B S hS A) (hY : IsAlgebraicSpace B S hS Y)
  (hG : IsAlgebraicSpace B S hS G)

/-- The Stacks 06NR step at the existential smooth-diagram criterion of Stacks 06FM, for a
property `P` of morphisms of algebraic spaces which descends along locally surjective maps. -/
private theorem hasPropertyOnSomeSmoothDiagram_of_comp_of_locallySurjective
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hP : Space.IsSmoothLocalOnSourceAndTarget B S hS P)
    (hA : IsAlgebraicSpace B S hS A) (hY : IsAlgebraicSpace B S hS Y)
    (hG : IsAlgebraicSpace B S hS G)
    (hdescent : ∀ (f : A ⟶ Y) (g : Y ⟶ G), P (f ≫ g) →
      Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f → P g)
    (hcomp : representingMap B S hS 𝒲.val 𝒱.val A G eA eG p.hom =
      representingMap B S hS 𝒲.val 𝒴.val A Y eA eY k.hom ≫
        representingMap B S hS 𝒴.val 𝒱.val Y G eY eG r.hom)
    (hp : HasPropertyOnSomeSmoothDiagram B S hS P p.hom)
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (representingMap B S hS 𝒲.val 𝒴.val A Y eA eY k.hom)) :
    HasPropertyOnSomeSmoothDiagram B S hS P r.hom := by
  have h₂ := (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS P hP
    𝒲.property 𝒱.property A G hA hG eA eG p.hom).1 hp
  rw [hcomp] at h₂
  exact (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS P hP
    𝒴.property 𝒱.property Y G hY hG eY eG r.hom).2 (hdescent _ _ h₂ hsurj)

include hk G eG hA hY hG in
/-- **The Stacks 06NR step at flatness, for a triangle of algebraic stacks.** Let `p ≅ k ≫ r` be a
2-commutative triangle of 1-morphisms of algebraic stacks over `S` whose three objects are
representable by algebraic spaces `A`, `Y`, `G`. If `p` is flat and the morphism of representing
presheaves induced by `k` is surjective as a morphism of fppf sheaves, then `r` is flat.

Flatness of a 1-morphism of algebraic stacks is the existential smooth-diagram criterion of
**Stacks 06FM** (**Stacks 06PW**), which at a represented source and target is flatness of the
induced morphism of representing presheaves
(`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_iff_represented`); so the hypothesis and
the conclusion are the two ends of **Stacks 06NR** read along the triangle of
`AlgebraicGeometry.Stack.AlgebraicStacks.representingMap_eq_comp_of_twoIso`. -/
theorem isFlat_of_comp_of_locallySurjective_representingMap
    (hp : IsFlat B S hS p)
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (representingMap B S hS 𝒲.val 𝒴.val A Y eA eY k.hom)) :
    IsFlat B S hS r :=
  hasPropertyOnSomeSmoothDiagram_of_comp_of_locallySurjective B S hS p r k A Y G eA eY eG _
    (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) hA hY hG
    (fun _ _ => Space.isFlat_of_comp_of_locallySurjective B S hS hA hY hG _ _)
    (representingMap_eq_comp_of_twoIso B S hS p r k hk A Y G eA eY eG) hp hsurj

include hk G eG hA hY hG in
/-- **The Stacks 06NR step at local finite presentation, for a triangle of algebraic stacks.** In
the situation of
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_comp_of_locallySurjective_representingMap`, if
`p` is locally of finite presentation and the morphism of representing presheaves induced by `k`
is surjective as a morphism of fppf sheaves, then `r` is locally of finite presentation.

Local finite presentation of a 1-morphism of algebraic stacks (**Stacks 06Q2** part (1)) is the
*universal* smooth-diagram criterion of **Stacks 06FM**, which agrees with the existential one by
`AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_iff_some`; the rest is as at flatness. -/
theorem isLocallyOfFinitePresentation_of_comp_of_locallySurjective_representingMap
    (hp : IsLocallyOfFinitePresentation B S hS p)
    (hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (representingMap B S hS 𝒲.val 𝒴.val A Y eA eY k.hom)) :
    IsLocallyOfFinitePresentation B S hS r := by
  have hP := Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS
  exact (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _ hP
    𝒴.property 𝒱.property r.hom).2
    (hasPropertyOnSomeSmoothDiagram_of_comp_of_locallySurjective B S hS p r k A Y G eA eY eG _ hP
      hA hY hG
      (fun _ _ => Space.isLocallyOfFinitePresentation_of_comp_of_locallySurjective B S hS hA hY hG
        _ _)
      (representingMap_eq_comp_of_twoIso B S hS p r k hk A Y G eA eY eG)
      ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _ hP
        𝒲.property 𝒱.property p.hom).1 hp) hsurj)

end Triangle

/-! ### The triangle a factorisation of one leg of a cospan produces -/

section Factorisation

variable {𝒳 𝒰 𝒱 : Stack.AlgebraicStacks.{u, w} B S hS}
  {x : 𝒰 ⟶ 𝒳} {q : 𝒱 ⟶ 𝒳} (γ : 𝒱 ⟶ 𝒰) (hγ : γ ≫ x ≅ q)
  {Q₁ : Bicategory.TwoCommSq q x} (hQ₁ : Bicategory.IsTwoFibreProduct Q₁)
  (Q₂ : Bicategory.TwoCommSq q q)

/-- **The 1-morphism from `𝒱 ×_𝒳 𝒱` to `𝒱 ×_𝒳 𝒰` induced by a factorisation of `q` through `x`.**
A 2-isomorphism `γ ≫ x ≅ q` reads a 2-commutative square `Q₂` over the cospan `(q, q)` as one over
the cospan `(q, x)` with the same apex and the same first leg
(`CategoryTheory.Bicategory.TwoCommSq.postcomposeSnd`), and the universal property of the 2-fibre
product `Q₁` of that cospan then supplies a 1-morphism of the apexes. -/
noncomputable def baseChangeFactorisationMap : Q₂.pt ⟶ Q₁.pt :=
  (Bicategory.twoFibreProductPreHom hQ₁ (Q₂.postcomposeSnd γ hγ)).hom

/-- **The mediating 1-morphism of a factorisation is compatible with the first projections.**
The comparison 2-cell of Stacks 003O on the first leg, read through the identification of the
apex and the first leg of `CategoryTheory.Bicategory.TwoCommSq.postcomposeSnd` with those of the
given square. -/
noncomputable def baseChangeFactorisationMapFstIso :
    Q₂.fst ≅ baseChangeFactorisationMap B S hS γ hγ hQ₁ Q₂ ≫ Q₁.fst :=
  (Bicategory.twoFibreProductPreHom hQ₁ (Q₂.postcomposeSnd γ hγ)).isoFst

end Factorisation

/-! ### The explicit mediating 1-morphism of the canonical squares, and its surjectivity -/

section Mediating

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.TwoFibreProductOver.structureFunctor

variable {𝒳 𝒰 𝒱 : Stack.AlgebraicStacks.{u, w} B S hS}
  {x : 𝒰 ⟶ 𝒳} {q : 𝒱 ⟶ 𝒳} (γ : 𝒱 ⟶ 𝒰) (hγ : γ ≫ x ≅ q)

/-- The natural isomorphism of underlying functors of a factorisation `γ ≫ x ≅ q`. -/
noncomputable def factorisationUnderlyingIso :
    (γ ≫ x).hom.hom.toFunctor ≅ q.hom.hom.toFunctor :=
  CatFiberedInGroupoids.underlyingIso
    (Bicategory.InducedBicategory.isoHom (f := γ ≫ x) (g := q) hγ)

/-- **The mediating pre-morphism of Stacks 003O from `𝒱 ×_𝒳 𝒱` to `𝒱 ×_𝒳 𝒰`, chosen
explicitly.** The square of the cospan `(q, q)` is read over the cospan `(q, x)` by the
factorisation (`CategoryTheory.Bicategory.TwoCommSq.postcomposeSnd`) and then mapped to the
*canonical* square of `(q, x)` by `CategoryTheory.CatFiberedInGroupoids.liftTwoFibreProductSquare`,
read in the 2-category of algebraic stacks by
`CategoryTheory.Bicategory.TwoCommSq.PreHom.ofUnderlying`.

Unlike `AlgebraicGeometry.Stack.AlgebraicStacks.baseChangeFactorisationMap`, which takes the
representative of the universal property's mediating *class* that
`CategoryTheory.Bicategory.twoFibreProductPreHom` chooses with `Quotient.out`, this one is given
by a formula, so its action on objects of the fibres can be computed —
`AlgebraicGeometry.Stack.AlgebraicStacks.factorisationMediatingMap_obj_iso_hom`. The two are
2-cell equivalent, both being pre-morphisms into a 2-fibre product
(`CategoryTheory.Bicategory.twoFibreProductPreHom_rel`). -/
noncomputable def factorisationMediatingPreHom :
    Bicategory.TwoCommSq.PreHom
      ((Stack.twoFibreProductSquareAlgebraicStacks B S hS q q).postcomposeSnd γ hγ)
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS q x) :=
  Bicategory.TwoCommSq.PreHom.ofUnderlying
    (CatFiberedInGroupoids.preHomTwoFibreProductSquare.{u, u, u + 1, u + 1} q.hom x.hom _)

/-- **The explicit 1-morphism `𝒱 ×_𝒳 𝒱 ⟶ 𝒱 ×_𝒳 𝒰` of a factorisation of `q` through `x`**: the
1-morphism of `AlgebraicGeometry.Stack.AlgebraicStacks.factorisationMediatingPreHom`. -/
noncomputable def factorisationMediatingMap :
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS q q).pt ⟶
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS q x).pt :=
  (factorisationMediatingPreHom B S hS γ hγ).hom

/-- The explicit mediating 1-morphism is compatible with the first projections. -/
noncomputable def factorisationMediatingMapFstIso :
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS q q).fst ≅
      factorisationMediatingMap B S hS γ hγ ≫
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS q x).fst :=
  (factorisationMediatingPreHom B S hS γ hγ).isoFst

/-- **The comparison isomorphism of the image of an object under the explicit mediating
1-morphism.** An object of `𝒱 ×_𝒳 𝒱` over `U` is a triple `(v, v', ψ : q v ≅ q v')`
(**Stacks 0040**) and its image is `(v, γ v', ψ ≫ δ⁻¹_{v'})`, where `δ : γ ≫ x ≅ q` is the
factorisation; the base and the two components hold by `rfl`, and this is the remaining field.

The only arithmetic is that the 2-category of algebraic stacks is strict, so the associator
`CategoryTheory.Bicategory.TwoCommSq.postcomposeSnd` leaves in the filler is an identity. -/
theorem factorisationMediatingMap_obj_iso_hom
    (W : (Stack.twoFibreProductSquareAlgebraicStacks B S hS q q).pt.val.val.obj) :
    ((factorisationMediatingMap B S hS γ hγ).hom.hom.toFunctor.obj W).iso.hom =
      W.iso.hom ≫ (factorisationUnderlyingIso B S hS γ hγ).inv.app W.y := by
  show W.iso.hom ≫ (factorisationUnderlyingIso B S hS γ hγ).inv.app W.y ≫ 𝟙 _ = _
  simp

/-- **Every object of a fibre of `𝒱 ×_𝒳 𝒰` is isomorphic to the image of an object of the fibre
of `𝒱 ×_𝒳 𝒱` over the same object of the site**, when `x` is a section of a 1-morphism
`π : 𝒳 ⟶ 𝒰`. No covering is needed: the statement holds over each object of the site on the nose.

Let `(v, u, φ : q v ≅ x u)` be an object of the fibre of `𝒱 ×_𝒳 𝒰` over `T`. The factorisation
gives `x (γ v) ≅ q v`, so `x (γ v) ≅ x u` in the fibre of `𝒳` over `T`, and a section separates
the objects of a fibre (`AlgebraicGeometry.Stack.nonempty_iso_fiber_of_iso_section_image`), so
there is a vertical isomorphism `β : γ v ≅ u`. The object of `𝒱 ×_𝒳 𝒱` to take is then
`(v, v, ψ)` with `ψ := φ ≫ x β⁻¹ ≫ δ_v`, whose image `(v, γ v, ψ ≫ δ⁻¹_v) = (v, γ v, φ ≫ x β⁻¹)`
is carried to `(v, u, φ)` by `(𝟙 v, β)`.

Note that the comparison isomorphism `ψ` of the second component is *free* data, which is why no
covering has to be refined and why the fibres of `𝒰` need not be discrete: the isomorphism `β`
alone suffices, and `AlgebraicGeometry.Stack.fiberArrow_eq_of_iso` is not used. -/
theorem exists_fiber_iso_factorisationMediatingMap (π : 𝒳 ⟶ 𝒰) (hx : x ≫ π ≅ 𝟙 𝒰)
    (T : BigFppfOver B S hS)
    (P : (Stack.twoFibreProductSquareAlgebraicStacks B S hS q x).pt.val.val.p.Fiber T) :
    ∃ W : (Stack.twoFibreProductSquareAlgebraicStacks B S hS q q).pt.val.val.p.Fiber T,
      Nonempty ((Functor.Fiber.mapOfComp
          (Stack.twoFibreProductSquareAlgebraicStacks B S hS q q).pt.val.val.p
          (Stack.twoFibreProductSquareAlgebraicStacks B S hS q x).pt.val.val.p
          (CatFiberedInGroupoids.homFunctor (factorisationMediatingMap B S hS γ hγ).hom)
          (CatFiberedInGroupoids.homFunctor_comp_p
            (factorisationMediatingMap B S hS γ hγ).hom) T).obj W ≅ P) := by
  obtain ⟨P, rfl⟩ := P
  -- the objects of the fibres over `P.base` that the argument uses
  have hgT : 𝒰.val.val.p.obj (γ.hom.hom.toFunctor.obj P.x) = P.base :=
    (BasedFunctor.w_obj γ.hom.hom P.x).trans P.hx
  have huT : 𝒰.val.val.p.obj P.y = P.base := P.hy
  have hxg : 𝒳.val.val.p.obj (x.hom.hom.toFunctor.obj (γ.hom.hom.toFunctor.obj P.x)) = P.base :=
    (BasedFunctor.w_obj x.hom.hom _).trans hgT
  have hxq : 𝒳.val.val.p.obj (q.hom.hom.toFunctor.obj P.x) = P.base :=
    (BasedFunctor.w_obj q.hom.hom _).trans P.hx
  have hxu : 𝒳.val.val.p.obj (x.hom.hom.toFunctor.obj P.y) = P.base :=
    (BasedFunctor.w_obj x.hom.hom _).trans huT
  -- the factorisation, read as an isomorphism of the fibre of `𝒳` over `P.base`
  have h1 : 𝒳.val.val.p.IsHomLift (𝟙 P.base)
      ((factorisationUnderlyingIso B S hS γ hγ).hom.app P.x) := by
    have h := CatFiberedInGroupoids.isHomLift_app
      (Bicategory.InducedBicategory.isoHom (f := γ ≫ x) (g := q) hγ).hom P.x
    rwa [P.hx] at h
  have h1' : 𝒳.val.val.p.IsHomLift (𝟙 P.base)
      ((factorisationUnderlyingIso B S hS γ hγ).inv.app P.x) := by
    have h := CatFiberedInGroupoids.isHomLift_app
      (Bicategory.InducedBicategory.isoHom (f := γ ≫ x) (g := q) hγ).inv P.x
    rwa [P.hx] at h
  let δ : (Functor.Fiber.mk hxg : 𝒳.val.val.p.Fiber P.base) ≅ Functor.Fiber.mk hxq :=
    { hom := ⟨(factorisationUnderlyingIso B S hS γ hγ).hom.app P.x, h1⟩
      inv := ⟨(factorisationUnderlyingIso B S hS γ hγ).inv.app P.x, h1'⟩
      hom_inv_id := Functor.Fiber.hom_ext (by
        show (factorisationUnderlyingIso B S hS γ hγ).hom.app P.x ≫
          (factorisationUnderlyingIso B S hS γ hγ).inv.app P.x = 𝟙 _
        simp)
      inv_hom_id := Functor.Fiber.hom_ext (by
        show (factorisationUnderlyingIso B S hS γ hγ).inv.app P.x ≫
          (factorisationUnderlyingIso B S hS γ hγ).hom.app P.x = 𝟙 _
        simp) }
  -- the comparison isomorphism of the given object, read in the same fibre (Stacks 0040 (1))
  let φ : (Functor.Fiber.mk hxq : 𝒳.val.val.p.Fiber P.base) ≅ Functor.Fiber.mk hxu :=
    TwoFibreProductOver.fibreIso 𝒱.val.val.p 𝒰.val.val.p 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor q.hom) (CatFiberedInGroupoids.homFunctor x.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p q.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p x.hom) P
  -- the section separates the objects of the fibre of `𝒰`
  obtain ⟨β⟩ := Stack.nonempty_iso_fiber_of_iso_section_image π.hom x.hom
    (Bicategory.InducedBicategory.isoHom (f := x ≫ π) (g := 𝟙 𝒰) hx)
    (Functor.Fiber.mk hgT) (Functor.Fiber.mk huT) (δ ≪≫ φ)
  let βX : (Functor.Fiber.mk hxg : 𝒳.val.val.p.Fiber P.base) ≅ Functor.Fiber.mk hxu :=
    (Functor.Fiber.mapOfComp 𝒰.val.val.p 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor x.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p x.hom) P.base).mapIso β
  let βU : γ.hom.hom.toFunctor.obj P.x ≅ P.y := Functor.Fiber.fiberInclusion.mapIso β
  -- the object of `𝒱 ×_𝒳 𝒱` whose image is the given one
  let W : (Stack.twoFibreProductSquareAlgebraicStacks B S hS q q).pt.val.val.obj :=
    { base := P.base
      x := P.x
      y := P.x
      hx := P.hx
      hy := P.hx
      iso := Functor.Fiber.fiberInclusion.mapIso (φ ≪≫ βX.symm ≪≫ δ)
      vertical := (φ ≪≫ βX.symm ≪≫ δ).hom.2 }
  have hwf : φ.hom = ((φ ≪≫ βX.symm ≪≫ δ).hom ≫ δ.inv) ≫ βX.hom := by simp
  have hwf2 : (φ ≪≫ βX.symm ≪≫ δ).hom ≫ δ.inv = φ.hom ≫ βX.inv := by simp
  have hw : q.hom.hom.toFunctor.map (𝟙 P.x) ≫ P.iso.hom =
      ((factorisationMediatingMap B S hS γ hγ).hom.hom.toFunctor.obj W).iso.hom ≫
        x.hom.hom.toFunctor.map βU.hom := by
    rw [factorisationMediatingMap_obj_iso_hom, CategoryTheory.Functor.map_id]
    exact (Category.id_comp _).trans (congrArg Subtype.val hwf)
  have hw2 : q.hom.hom.toFunctor.map (𝟙 P.x) ≫
      ((factorisationMediatingMap B S hS γ hγ).hom.hom.toFunctor.obj W).iso.hom =
      P.iso.hom ≫ x.hom.hom.toFunctor.map βU.inv := by
    rw [factorisationMediatingMap_obj_iso_hom, CategoryTheory.Functor.map_id]
    exact (Category.id_comp _).trans (congrArg Subtype.val hwf2)
  let m : ((factorisationMediatingMap B S hS γ hγ).hom.hom.toFunctor.obj W) ⟶ P :=
    { hbase := 𝟙 P.base
      a := 𝟙 P.x
      b := βU.hom
      ha := CategoryTheory.IsHomLift.id P.hx
      hb := β.hom.2
      w := hw }
  let mi : P ⟶ ((factorisationMediatingMap B S hS γ hγ).hom.hom.toFunctor.obj W) :=
    { hbase := 𝟙 P.base
      a := 𝟙 P.x
      b := βU.inv
      ha := CategoryTheory.IsHomLift.id P.hx
      hb := β.inv.2
      w := hw2 }
  refine ⟨⟨W, rfl⟩, ⟨{
    hom := ⟨m, TwoFibreProductOver.structureFunctor_isHomLift m (𝟙 P.base)
      (CategoryTheory.IsHomLift.id P.hx)⟩
    inv := ⟨mi, TwoFibreProductOver.structureFunctor_isHomLift mi (𝟙 P.base)
      (CategoryTheory.IsHomLift.id P.hx)⟩
    hom_inv_id := ?_
    inv_hom_id := ?_ }⟩⟩
  · refine Functor.Fiber.hom_ext (TwoFibreProductOver.Hom.ext' ?_ ?_)
    · show 𝟙 P.x ≫ 𝟙 P.x = 𝟙 P.x
      simp
    · show βU.hom ≫ βU.inv = 𝟙 _
      simp
  · refine Functor.Fiber.hom_ext (TwoFibreProductOver.Hom.ext' ?_ ?_)
    · show 𝟙 P.x ≫ 𝟙 P.x = 𝟙 P.x
      simp
    · show βU.inv ≫ βU.hom = 𝟙 _
      simp

/-- **The explicit mediating 1-morphism of a factorisation through a section induces a surjection
of fppf sheaves.** This is the hypothesis the **Stacks 06NR** step above consumes, discharged: if
`x : 𝒰 ⟶ 𝒳` is a section of a 1-morphism `π : 𝒳 ⟶ 𝒰` and `γ ≫ x ≅ q`, then the morphism of
representing presheaves induced by
`AlgebraicGeometry.Stack.AlgebraicStacks.factorisationMediatingMap` is locally surjective for
*every* topology on the site — in fact its morphism of presheaves of isomorphism classes of
**Stacks 04SC** is surjective over each object, by
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_fiber_iso_factorisationMediatingMap`.

The passage from objects of fibres to the representing presheaves is
`AlgebraicGeometry.Stack.isLocallySurjective_representingMap_of_isoClassMap`. -/
theorem isLocallySurjective_representingMap_factorisationMediatingMap
    (π : 𝒳 ⟶ 𝒰) (hx : x ≫ π ≅ 𝟙 𝒰)
    (A Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eA : StacksRepresentableCFG.EquivalenceOver
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS q q).pt.val.val.p
      (presheafOfCategories (A ⋙ typeToCat)).p)
    (eY : StacksRepresentableCFG.EquivalenceOver
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS q x).pt.val.val.p
      (presheafOfCategories (Y ⋙ typeToCat)).p)
    (J : GrothendieckTopology (BigFppfOver B S hS)) :
    Presheaf.IsLocallySurjective J
      (representingMap B S hS
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS q q).pt.val
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS q x).pt.val A Y eA eY
        (factorisationMediatingMap B S hS γ hγ).hom) := by
  refine isLocallySurjective_representingMap_of_isoClassMap B S hS _ _ A Y eA eY J
    (factorisationMediatingMap B S hS γ hγ).hom ?_
  let : (Stack.twoFibreProductSquareAlgebraicStacks B S hS q q).pt.val.val.p.IsFibered :=
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS q q).pt.val.property.isFibered
  let : (Stack.twoFibreProductSquareAlgebraicStacks B S hS q x).pt.val.val.p.IsFibered :=
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS q x).pt.val.property.isFibered
  refine Presheaf.isLocallySurjective_of_surjective J _ (fun U c => ?_)
  induction c using _root_.Quotient.ind with
  | _ P =>
    obtain ⟨W, ⟨e⟩⟩ := exists_fiber_iso_factorisationMediatingMap B S hS γ hγ π hx U.unop P
    exact ⟨Functor.isoClassMk _ W, (Functor.isoClassMap_app_isoClassMk _ W).trans
      (Functor.isoClassMk_eq_of_iso e)⟩

end Mediating

/-! ### The route to flatness and local finite presentation of the factored 1-morphism -/

section Route

variable {𝒳 𝒰 𝒱 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **A surjective, flat, locally finitely presented 1-morphism which factors through a section
`x` makes `x` flat and locally of finite presentation.** Let `x : 𝒰 ⟶ 𝒳` be a section of a
1-morphism `π : 𝒳 ⟶ 𝒰` of algebraic stacks over `S`, let `q : 𝒱 ⟶ 𝒳` be surjective, flat and
locally of finite presentation, and let `γ : 𝒱 ⟶ 𝒰` with `γ ≫ x ≅ q` factor it through `x`. If
the apexes of the canonical 2-fibre products `𝒱 ×_𝒳 𝒱` and `𝒱 ×_𝒳 𝒰` and the stack `𝒱` are
representable by algebraic spaces, then `x` is flat and locally of finite presentation.

This is the whole of the route to the unproved half of **Stacks 06QG** part (3) *after* the
1-morphism `q` has been produced. The chain is: `Q₂.fst` is flat and locally of finite
presentation by base change along `q` (**Stacks 06PY**, **Stacks 06Q4**); the **Stacks 06NR** step
of `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_comp_of_locallySurjective_representingMap`
and its sibling carry both properties to `Q₁.fst` along the mediating 1-morphism
`𝒱 ×_𝒳 𝒱 ⟶ 𝒱 ×_𝒳 𝒰`, whose surjectivity as a morphism of fppf sheaves is
`isLocallySurjective_representingMap_factorisationMediatingMap`;
and **Stacks 06PZ** and **Stacks 06Q8** descend them from `Q₁.fst` to `x` along the surjective
flat locally finitely presented `q`.

The hypothesis that `x` is a *section* is what makes the surjectivity true, and it is the
situation of the application: there `π` is the structural 1-morphism of a gerbe and `x` is the
section whose flatness and local finite presentation are wanted. That application is
`isFlat_and_isLocallyOfFinitePresentation_section_of_isGerbeOver`
in `StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatLocalSection`, which supplies the three
representability data above and, with the fppf-local section of **Stacks 06QH** (1) `⟹` (2),
makes **Stacks 06QI** unconditional. -/
theorem isFlat_and_isLocallyOfFinitePresentation_of_factorisation
    (x : 𝒰 ⟶ 𝒳) (q : 𝒱 ⟶ 𝒳) (γ : 𝒱 ⟶ 𝒰) (hγ : γ ≫ x ≅ q)
    (π : 𝒳 ⟶ 𝒰) (hx : x ≫ π ≅ 𝟙 𝒰)
    (hqsurj : Stack.IsSurjective B S hS q)
    (hqflat : IsFlat B S hS q)
    (hqlfp : IsLocallyOfFinitePresentation B S hS q)
    (A Y G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hA : IsAlgebraicSpace B S hS A) (hY : IsAlgebraicSpace B S hS Y)
    (hG : IsAlgebraicSpace B S hS G)
    (eA : StacksRepresentableCFG.EquivalenceOver
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS q q).pt.val.val.p
      (presheafOfCategories (A ⋙ typeToCat)).p)
    (eY : StacksRepresentableCFG.EquivalenceOver
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS q x).pt.val.val.p
      (presheafOfCategories (Y ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒱.val.val.p (presheafOfCategories (G ⋙ typeToCat)).p) :
    IsFlat B S hS x ∧ IsLocallyOfFinitePresentation B S hS x := by
  -- the explicit mediating 1-morphism of the factorisation, and its surjectivity
  let k := factorisationMediatingMap B S hS γ hγ
  have hk : (Stack.twoFibreProductSquareAlgebraicStacks B S hS q q).fst ≅
      k ≫ (Stack.twoFibreProductSquareAlgebraicStacks B S hS q x).fst :=
    factorisationMediatingMapFstIso B S hS γ hγ
  have hsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (representingMap B S hS
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS q q).pt.val
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS q x).pt.val A Y eA eY k.hom) :=
    isLocallySurjective_representingMap_factorisationMediatingMap B S hS γ hγ π hx A Y eA eY _
  -- Stacks 06PY and Stacks 06Q4: the base change of `q` along itself
  have h₂flat : IsFlat B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS q q).fst :=
    isFlat_baseChange B S hS q q _
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS q q) hqflat
  have h₂lfp : IsLocallyOfFinitePresentation B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS q q).fst :=
    isLocallyOfFinitePresentation_baseChange B S hS q q _
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS q q) hqlfp
  -- the Stacks 06NR step along the triangle
  have h₁flat : IsFlat B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS q x).fst :=
    isFlat_of_comp_of_locallySurjective_representingMap B S hS _ _ k hk A Y G eA eY eG
      hA hY hG h₂flat hsurj
  have h₁lfp : IsLocallyOfFinitePresentation B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS q x).fst :=
    isLocallyOfFinitePresentation_of_comp_of_locallySurjective_representingMap B S hS _ _ k hk
      A Y G eA eY eG hA hY hG h₂lfp hsurj
  refine ⟨isFlat_twoFibreProduct_fst_descent B S hS x q _
    (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS q x)
    hqsurj hqflat h₁flat, ?_⟩
  -- Stacks 06Q8 asks for the second projection of the canonical square of the cospan `(x, q)`;
  -- that is the first projection of the leg exchange of the square of `(q, x)`, so Stacks 06FM
  -- moves the property between them
  refine isLocallyOfFinitePresentation_of_baseChange B S hS x q hqsurj hqflat hqlfp ?_
  refine (Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
    (fun _ _ m => Space.IsLocallyOfFinitePresentation B S hS m)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS x q).pt.property 𝒱.property
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS x q).snd.hom).2 ?_
  refine Stack.hasPropertyOnSomeSmoothDiagram_fst_of_isTwoFibreProduct B S hS
    (fun _ _ m => Space.IsLocallyOfFinitePresentation B S hS m)
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} q.hom x.hom)
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} x.hom q.hom).swap
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      q.hom x.hom)
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        x.hom q.hom)) ?_
  exact (Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
    (fun _ _ m => Space.IsLocallyOfFinitePresentation B S hS m)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS q x).pt.property 𝒱.property
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS q x).fst.hom).1 h₁lfp

end Route

end AlgebraicGeometry.Stack.AlgebraicStacks

end
